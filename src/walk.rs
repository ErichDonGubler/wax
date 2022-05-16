use itertools::Itertools as _;
use regex::Regex;
use std::borrow::Cow;
use std::fs::{FileType, Metadata};
use std::io;
use std::path::{Component, Path, PathBuf};
use thiserror::Error;
use walkdir::{self, DirEntry, WalkDir};

use crate::capture::MatchedText;
use crate::encode::CompileError;
use crate::token::{self, Boundedness, InvariantText, Token};
use crate::{CandidatePath, Glob, GlobError, PositionExt as _};

pub type WalkItem<'e> = Result<WalkEntry<'e>, WalkError>;

/// Describes errors that occur when matching a [`Glob`] against a directory
/// tree.
///
/// `WalkError` supports conversion into [`io::Error`].
///
/// [`Glob`]: crate::Glob
/// [`io::Error`]: std::io::Error
#[derive(Debug, Error)]
#[error("failed to match directory tree: {kind}")]
pub struct WalkError {
    depth: usize,
    kind: ErrorKind,
}

impl WalkError {
    /// Gets the path at which the error occurred.
    ///
    /// Returns `None` if there is no path associated with the error.
    pub fn path(&self) -> Option<&Path> {
        self.kind.path()
    }

    /// Gets the depth from the root at which the error occurred.
    pub fn depth(&self) -> usize {
        self.depth
    }
}

impl From<walkdir::Error> for WalkError {
    fn from(error: walkdir::Error) -> Self {
        let depth = error.depth();
        let path = error.path().map(From::from);
        if error.io_error().is_some() {
            WalkError {
                depth,
                kind: ErrorKind::Io {
                    path,
                    error: error.into_io_error().expect("incongruent error kind"),
                },
            }
        }
        else {
            WalkError {
                depth,
                kind: ErrorKind::LinkCycle {
                    root: error
                        .loop_ancestor()
                        .expect("incongruent error kind")
                        .into(),
                    leaf: path.expect("incongruent error kind"),
                },
            }
        }
    }
}

impl From<WalkError> for io::Error {
    fn from(error: WalkError) -> Self {
        let kind = match error.kind {
            ErrorKind::Io { ref error, .. } => error.kind(),
            _ => io::ErrorKind::Other,
        };
        io::Error::new(kind, error)
    }
}

#[derive(Debug, Error)]
#[non_exhaustive]
enum ErrorKind {
    #[error("failed to read file at `{path:?}`: {error}")]
    Io {
        path: Option<PathBuf>,
        error: io::Error,
    },
    #[error("symbolic link cycle detected from `{root}` to `{leaf}`")]
    LinkCycle { root: PathBuf, leaf: PathBuf },
}

impl ErrorKind {
    pub fn path(&self) -> Option<&Path> {
        match self {
            ErrorKind::Io { ref path, .. } => path.as_ref().map(|path| path.as_ref()),
            ErrorKind::LinkCycle { ref leaf, .. } => Some(leaf.as_ref()),
        }
    }
}

/// Traverses a directory tree via a `Walk` instance.
///
/// This macro emits an interruptable loop that executes a block of code
/// whenever a `WalkEntry` or error is encountered while traversing a directory
/// tree. The block may return from its function or otherwise interrupt and
/// subsequently resume the loop.
///
/// Note that if the block attempts to emit a `WalkEntry` across a function
/// boundary, then the entry contents must be copied via `into_owned`.
macro_rules! walk {
    ($state:expr => |$entry:ident| $f:block) => {
        use itertools::EitherOrBoth::{Both, Left, Right};
        use itertools::Position::{First, Last, Middle, Only};

        // `while-let` avoids a mutable borrow of `walk`, which would prevent a
        // subsequent call to `skip_current_dir` within the loop body.
        #[allow(clippy::while_let_on_iterator)]
        #[allow(unreachable_code)]
        'walk: while let Some(entry) = $state.walk.next() {
            let entry = match entry {
                Ok(entry) => entry,
                Err(error) => {
                    let $entry = Err(error.into());
                    $f
                    continue; // May be unreachable.
                }
            };
            let path = entry
                .path()
                .strip_prefix(&$state.prefix)
                .expect("path is not in tree");
            let depth = entry.depth().saturating_sub(1);
            for candidate in path
                .components()
                .skip(depth)
                .filter_map(|component| match component {
                    Component::Normal(component) => Some(CandidatePath::from(component)),
                    _ => None,
                })
                .zip_longest($state.components.iter().skip(depth))
                .with_position()
            {
                match candidate.as_tuple() {
                    (First(_) | Middle(_), Both(component, pattern)) => {
                        if !pattern.is_match(component.as_ref()) {
                            // Do not descend into directories that do not match
                            // the corresponding component pattern.
                            if entry.file_type().is_dir() {
                                $state.walk.skip_current_dir();
                            }
                            continue 'walk;
                        }
                    }
                    (Last(_) | Only(_), Both(component, pattern)) => {
                        if pattern.is_match(component.as_ref()) {
                            let path = CandidatePath::from(path);
                            if let Some(matched) =
                                $state.pattern.captures(path.as_ref()).map(MatchedText::from)
                            {
                                let $entry = Ok(WalkEntry {
                                    entry: Cow::Borrowed(&entry),
                                    matched,
                                });
                                $f
                            }
                        }
                        else {
                            // Do not descend into directories that do not match
                            // the corresponding component pattern.
                            if entry.file_type().is_dir() {
                                $state.walk.skip_current_dir();
                            }
                        }
                        continue 'walk;
                    }
                    (_, Left(_component)) => {
                        let path = CandidatePath::from(path);
                        if let Some(matched) =
                            $state.pattern.captures(path.as_ref()).map(MatchedText::from)
                        {
                            let $entry = Ok(WalkEntry {
                                entry: Cow::Borrowed(&entry),
                                matched,
                            });
                            $f
                        }
                        continue 'walk;
                    }
                    (_, Right(_pattern)) => {
                        continue 'walk;
                    }
                }
            }
            // If the loop is not entered, check for a match. This may indicate
            // that the `Glob` is empty and a single invariant path may be
            // matched.
            let path = CandidatePath::from(path);
            if let Some(matched) = $state.pattern.captures(path.as_ref()).map(MatchedText::from) {
                let $entry = Ok(WalkEntry {
                    entry: Cow::Borrowed(&entry),
                    matched,
                });
                $f
            }
        }
    };
}

/// Extension methods for [`Iterator`]s concerning [`Glob`]s and directory
/// traversals.
///
/// [`Glob`]: crate::Glob
/// [`Iterator`]: std::iter::Iterator
pub trait IteratorExt: Iterator + Sized {
    /// Filters items and determines the traversal of directory trees in
    /// `FileIterator`s such as [`Walk`].
    ///
    /// A `FileIterator` is an [`Iterator`] that reads the file system and
    /// traverses directory trees. [`Walk`] and [`FilterTree`] are both
    /// `FileIterator`s and they both support this function.
    ///
    /// This function creates an adaptor that filters [`WalkEntry`]s and
    /// furthermore specifies how iteration proceeds to walk directory trees.
    /// The adaptor accepts a function that, when discarding a [`WalkEntry`],
    /// yields a [`FilterTarget`]. **Importantly, if the entry refers to a
    /// directory and [`FilterTarget::Tree`] is returned by the function, then
    /// iteration will not descend into that directory and the tree will not be
    /// read from the file system.** Therefore, this adaptor should be preferred
    /// over [`Iterator::filter`] when discarded directories do not need to be
    /// read.
    ///
    /// Errors are not filtered, so if an error occurs reading a file at a path
    /// that would have been discarded, then that error is still yielded by the
    /// iterator.
    ///
    /// # Examples
    ///
    /// The [`FilterTree`] adaptor can be used to apply additional custom
    /// filtering that avoids unnecessary directory traversals. The following
    /// example filters out hidden files on Unix and Windows. On Unix, hidden
    /// files are filtered out nominally via [`not`]. On Windows, `filter_tree`
    /// is used to detect the [hidden attribute][attributes]. In both cases, the
    /// adaptor does not read hidden directory trees.
    ///
    /// ```rust,no_run
    /// #[cfg(windows)]
    /// use wax::{FilterTarget, IteratorExt as _};
    ///
    /// let walk = wax::walk("**/*.(?i){jpg,jpeg}", "./Pictures", usize::MAX).unwrap();
    /// // Filter out conventionally hidden files on Unix. Note that `not` will
    /// // not perform unnecessary reads of hidden directory trees.
    /// #[cfg(unix)]
    /// let walk = walk.not(["**/.*/**"]).unwrap();
    /// // Filter out files with the hidden attribute on Windows.
    /// #[cfg(windows)]
    /// let walk = walk.filter_tree(|entry| {
    ///     use std::os::windows::fs::MetadataExt as _;
    ///
    ///     const ATTRIBUTE_HIDDEN: u32 = 0x2;
    ///
    ///     let attributes = entry.metadata().unwrap().file_attributes();
    ///     if (attributes & ATTRIBUTE_HIDDEN) == ATTRIBUTE_HIDDEN {
    ///         // Do not read hidden directory trees.
    ///         Some(FilterTarget::Tree)
    ///     }
    ///     else {
    ///         None
    ///     }
    /// });
    /// for entry in walk {
    ///     let entry = entry.unwrap();
    ///     println!("JPEG: {:?}", entry.path());
    /// }
    /// ```
    ///
    /// [`FilterTree`]: crate::FilterTree
    /// [`Iterator`]: std::iter::Iterator
    /// [`Iterator::filter`]: std::iter::Iterator::filter
    /// [`not`]: crate::Walk::not
    /// [`Walk`]: crate::Walk
    /// [`WalkEntry`]: crate::WalkEntry
    ///
    /// [attributes]: https://docs.microsoft.com/en-us/windows/win32/fileio/file-attribute-constants
    fn filter_tree<F>(self, f: F) -> FilterTree<Self, F>
    where
        Self: FileIterator<Item = WalkItem<'static>>,
        F: FnMut(&WalkEntry<'static>) -> Option<FilterTarget>;
}

impl<I> IteratorExt for I
where
    I: Iterator,
{
    fn filter_tree<F>(self, f: F) -> FilterTree<Self, F>
    where
        Self: FileIterator<Item = WalkItem<'static>>,
        F: FnMut(&WalkEntry<'static>) -> Option<FilterTarget>,
    {
        FilterTree { input: self, f }
    }
}

pub trait FileIterator: Iterator {
    fn skip_tree(&mut self);
}

impl FileIterator for walkdir::IntoIter {
    fn skip_tree(&mut self) {
        self.skip_current_dir();
    }
}

/// Negated [`Glob`]s and their associated [`FilterTarget`]s.
///
/// Determines an appropriate [`FilterTarget`] for a [`WalkEntry`] based on
/// [`Glob`]s used as a filter. This can be used with [`FilterTree`] to
/// effeciently filter [`WalkEntry`]s without reading directory trees from the
/// file system when not necessary.
///
/// [`FilterTarget`]: crate::FilterTarget
/// [`FilterTree`]: crate::FilterTree
/// [`Pattern`]: crate::Pattern
/// [`WalkEntry`]: crate::WalkEntry
#[derive(Clone, Debug)]
pub struct Negation {
    terminal: Regex,
    nonterminal: Regex,
}

impl Negation {
    /// Constructs a `Negation` from an [`IntoIterator`] with items that can be
    /// converted into [`Glob`]s.
    ///
    /// # Errors
    ///
    /// Returns an error if any of the items cannot be successfully converted
    /// into a [`Glob`]. If the items are [`Glob`]s, then this function is
    /// infallible.
    ///
    /// [`Glob`]: crate::Glob
    /// [`IntoIterator`]: std::iter::IntoIterator
    pub fn try_from_patterns<'t, P>(
        patterns: impl IntoIterator<Item = P>,
    ) -> Result<Self, GlobError<'t>>
    where
        GlobError<'t>: From<P::Error>,
        P: TryInto<Glob<'t>>,
    {
        // TODO: Inlining the code in this function causes E0271 in the call to
        //       `crate::any` claiming that `Infallible` was expected but
        //       `<P as TryInto<Glob<'t>>>::Error` was found instead. This may
        //       be a bug in the compiler. In this case, these types are the
        //       same, but it's unclear why the compiler requires this, as
        //       `crate::any` has no such requirement.
        fn from_globs(globs: Vec<Glob>) -> Negation {
            // Partition the negation globs into terminals and nonterminals. A
            // terminal glob matches all sub-paths once it has matched and so
            // arrests the traversal into sub-directories. This is determined by
            // whether or not a glob is terminated by a component with unbounded
            // depth and unbounded variance.
            let (terminals, nonterminals) = globs.into_iter().partition::<Vec<_>, _>(is_terminal);
            Negation {
                terminal: crate::any::<Glob, _>(terminals).unwrap().regex,
                nonterminal: crate::any::<Glob, _>(nonterminals).unwrap().regex,
            }
        }

        let globs: Vec<_> = patterns
            .into_iter()
            .map(TryInto::try_into)
            .collect::<Result<_, _>>()?;
        Ok(from_globs(globs))
    }

    /// Gets the appropriate [`FilterTarget`] for the given [`WalkEntry`].
    ///
    /// This function can be used with [`IteratorExt::filter_tree`] to
    /// effeciently filter [`WalkEntry`]s without reading directory trees from
    /// the file system when not necessary.
    ///
    /// Returns [`FilterTarget::Tree`] if the [`WalkEntry`] matches a terminal
    /// glob expression, such as `secret/**`.
    ///
    /// [`FilterTarget`]: crate::FilterTarget
    /// [`FilterTarget::Tree`]: crate::FilterTarget::Tree
    /// [`IteratorExt::filter_tree`]: crate::IteratorExt::filter_tree
    /// [`WalkEntry`]: crate::WalkEntry
    pub fn target(&self, entry: &WalkEntry) -> Option<FilterTarget> {
        let path = entry.to_candidate_path();
        if self.terminal.is_match(path.as_ref()) {
            // Do not descend into directories that match the terminal negation.
            Some(FilterTarget::Tree)
        }
        else if self.nonterminal.is_match(path.as_ref()) {
            Some(FilterTarget::File)
        }
        else {
            None
        }
    }
}

/// Configuration for interpreting symbolic links.
///
/// Determines how symbolic links are interpreted when traversing directory
/// trees using functions like [`Glob::walk`]. By default, symbolic links are
/// read as regular files and their targets are ignored.
///
/// [`Glob::walk`]: crate::Glob::walk
#[derive(Clone, Copy, Debug)]
pub enum LinkBehavior {
    /// Read the symbolic link file itself.
    ///
    /// This behavior reads the symbolic link as a regular file. The
    /// corresponding [`WalkEntry`] uses the path of the link file and its
    /// metadata describes the link file itself. The target is effectively
    /// ignored and traversal will **not** follow the link.
    ///
    /// [`WalkEntry`]: crate::WalkEntry
    ReadFile,
    /// Read the target of the symbolic link.
    ///
    /// This behavior reads the target of the symbolic link. The corresponding
    /// [`WalkEntry`] uses the path of the link file and its metadata describes
    /// the target. If the target is a directory, then traversal will follow the
    /// link and descend into the target.
    ///
    /// If a link is reentrant and forms a cycle, then an error will be emitted
    /// instead of a [`WalkEntry`] and traversal will not follow the link.
    ///
    /// [`WalkEntry`]: crate::WalkEntry
    ReadTarget,
}

impl Default for LinkBehavior {
    fn default() -> Self {
        LinkBehavior::ReadFile
    }
}

/// Configuration for matching [`Glob`]s against directory trees.
///
/// Determines the behavior of the traversal within a directory tree when using
/// functions like [`Glob::walk`]. `WalkBehavior` can be constructed via
/// conversions from types representing its fields. APIs generally accept `impl
/// Into<WalkBehavior>`, so these conversion can be used implicitly. When
/// constructed using such a conversion, `WalkBehavior` will use defaults for
/// any remaining fields.
///
/// # Examples
///
/// By default, symbolic links are interpreted as regular files and targets are
/// ignored. To read linked targets, use [`LinkBehavior::ReadTarget`].
///
/// ```rust
/// use wax::LinkBehavior;
///
/// for entry in wax::walk("**", ".", LinkBehavior::ReadTarget).unwrap() {
///     let entry = entry.unwrap();
///     // ...
/// }
/// ```
///
/// [`Glob`]: crate::Glob
/// [`Glob::walk`]: crate::Glob::walk
#[derive(Clone, Copy, Debug)]
pub struct WalkBehavior {
    // TODO: Consider using a dedicated type for this field. Using primitive
    //       types does not interact well with conversions used in `walk` APIs.
    //       For example, if another `usize` field is introduced, then the
    //       conversions become ambiguous and confusing.
    /// Maximum depth.
    ///
    /// Determines the maximum depth to which a directory tree will be traversed
    /// relative to the root. A depth of zero corresponds to the root and so
    /// using such a depth will yield at most one entry for the root.
    ///
    /// The default value is [`usize::MAX`].
    ///
    /// [`usize::MAX`]: usize::MAX
    pub depth: usize,
    /// Interpretation of symbolic links.
    ///
    /// Determines how symbolic links are interpreted when traversing a
    /// directory tree. See [`LinkBehavior`].
    ///
    /// The default value is [`LinkBehavior::ReadFile`].
    ///
    /// [`LinkBehavior`]: crate::LinkBehavior
    /// [`LinkBehavior::ReadFile`]: crate::LinkBehavior::ReadFile
    pub link: LinkBehavior,
}

/// Constructs a `WalkBehavior` using the following defaults:
///
/// | Field     | Description                       | Value                      |
/// |-----------|-----------------------------------|----------------------------|
/// | [`depth`] | Maximum depth.                    | [`usize::MAX`]             |
/// | [`link`]  | Interpretation of symbolic links. | [`LinkBehavior::ReadFile`] |
///
/// [`depth`]: crate::WalkBehavior::depth
/// [`link`]: crate::WalkBehavior::link
/// [`LinkBehavior::ReadFile`]: crate::LinkBehavior::ReadFile
/// [`usize::MAX`]: usize::MAX
impl Default for WalkBehavior {
    fn default() -> Self {
        WalkBehavior {
            depth: usize::MAX,
            link: Default::default(),
        }
    }
}

impl From<()> for WalkBehavior {
    fn from(_: ()) -> Self {
        Default::default()
    }
}

impl From<LinkBehavior> for WalkBehavior {
    fn from(link: LinkBehavior) -> Self {
        WalkBehavior {
            link,
            ..Default::default()
        }
    }
}

impl From<usize> for WalkBehavior {
    fn from(depth: usize) -> Self {
        WalkBehavior {
            depth,
            ..Default::default()
        }
    }
}

/// Iterator over files matching a [`Glob`] in a directory tree.
///
/// `Walk` is a `FileIterator` and supports [`IteratorExt::filter_tree`].
///
/// [`Glob`]: crate::Glob
/// [`IteratorExt::filter_tree`]: crate::IteratorExt::filter_tree
#[derive(Debug)]
// This type is principally an iterator and is therefore lazy.
#[must_use]
pub struct Walk<'g> {
    pattern: Cow<'g, Regex>,
    components: Vec<Regex>,
    prefix: PathBuf,
    walk: walkdir::IntoIter,
}

impl<'g> Walk<'g> {
    fn compile<'t, I>(tokens: I) -> Result<Vec<Regex>, CompileError>
    where
        I: IntoIterator<Item = &'t Token<'t>>,
        I::IntoIter: Clone,
    {
        let mut regexes = Vec::new();
        for component in token::components(tokens) {
            if component
                .tokens()
                .iter()
                .any(|token| token.has_component_boundary())
            {
                // Stop at component boundaries, such as tree wildcards or any
                // boundary within a group token.
                break;
            }
            else {
                regexes.push(Glob::compile(component.tokens().iter().cloned())?);
            }
        }
        Ok(regexes)
    }

    /// Clones any borrowed data into an owning instance.
    pub fn into_owned(self) -> Walk<'static> {
        let Walk {
            pattern,
            components,
            prefix,
            walk,
        } = self;
        Walk {
            pattern: Cow::Owned(pattern.into_owned()),
            components,
            prefix,
            walk,
        }
    }

    /// Calls a closure on each matched file or error.
    ///
    /// This function does not clone the contents of paths and captures when
    /// emitting entries and so may be more efficient than external iteration
    /// via [`Iterator::for_each`], which must clone text.
    ///
    /// [`Iterator::for_each`]: std::iter::Iterator::for_each
    pub fn for_each(mut self, mut f: impl FnMut(WalkItem)) {
        walk!(self => |entry| {
            f(entry);
        });
    }

    /// Filters [`WalkEntry`]s against negated [`Glob`]s.
    ///
    /// This function creates an adaptor that discards [`WalkEntry`]s that match
    /// any of the given [`Glob`]s. This allows for broad negations while
    /// matching a [`Glob`] against a directory tree that cannot be achieved
    /// using a single glob expression.
    ///
    /// The adaptor is constructed via [`FilterTree`] and [`Negation`] and
    /// therefore **does not read directory trees from the file system when a
    /// directory matches a terminal glob expression** such as `**/private/**`
    /// or `hidden/<<?>/>*`. This function should be preferred when filtering
    /// [`WalkEntry`]s against [`Glob`]s, since this avoids potentially large
    /// and unnecessary reads.
    ///
    /// # Errors
    ///
    /// Returns an error if any of the given patterns could not be converted
    /// into a [`Glob`]. If the given patterns are [`Glob`]s, then this function
    /// is infallible.
    ///
    /// # Examples
    ///
    /// Because glob expressions do not support general negations, it is
    /// sometimes impossible to express patterns that deny particular text. In
    /// such cases, `not` can be used to apply additional patterns as a filter.
    ///
    /// ```rust,no_run
    /// use wax::Glob;
    ///
    /// // Find image files, but not if they are beneath a directory with a name that
    /// // suggests that they are private.
    /// let glob = Glob::new("**/*.(?i){jpg,jpeg,png}").unwrap();
    /// for entry in glob
    ///     .walk(".", usize::MAX)
    ///     .not(["**/(?i)<.:0,1>private/**"])
    ///     .unwrap()
    /// {
    ///     let entry = entry.unwrap();
    ///     // ...
    /// }
    /// ```
    ///
    /// [`Glob`]: crate::Glob
    /// [`Iterator::filter`]: std::iter::Iterator::filter
    /// [`IteratorExt::filter_tree`]: crate::IteratorExt::filter_tree
    /// [`Negation`]: crate::Negation
    /// [`WalkEntry`]: crate::WalkEntry
    pub fn not<'n, P>(
        self,
        patterns: impl IntoIterator<Item = P>,
    ) -> Result<impl 'g + FileIterator<Item = WalkItem<'static>>, GlobError<'n>>
    where
        P: TryInto<Glob<'n>, Error = GlobError<'n>>,
    {
        Negation::try_from_patterns(patterns)
            .map(|negation| self.filter_tree(move |entry| negation.target(entry)))
    }
}

impl Iterator for Walk<'_> {
    type Item = WalkItem<'static>;

    fn next(&mut self) -> Option<Self::Item> {
        walk!(self => |entry| {
            return Some(entry.map(|entry: WalkEntry| entry.into_owned()));
        });
        None
    }
}

impl FileIterator for Walk<'_> {
    fn skip_tree(&mut self) {
        self.walk.skip_tree();
    }
}

/// Describes how files are read and discarded by [`FilterTree`].
///
/// [`FilterTree`]: crate::FilterTree
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum FilterTarget {
    /// Discard the file.
    ///
    /// The [`WalkEntry`] for the given file is discarded by the [`FilterTree`]
    /// adaptor. Only this particular file is ignored and if the entry
    /// represents a directory, then its tree is still read from the file
    /// system.
    ///
    /// [`FilterTree`]: crate::FilterTree
    /// [`WalkEntry`]: crate::WalkEntry
    File,
    /// Discard the file and its directory tree, if any.
    ///
    /// The [`WalkEntry`] for the given file is discarded by the [`FilterTree`]
    /// adaptor. If the entry represents a directory, then its entire tree is
    /// ignored and is not read from the file system.
    ///
    /// When the [`WalkEntry`] represents a normal file (not a directory), then
    /// this is the same as [`FilterTarget::File`].
    ///
    /// [`FilterTarget::File`]: crate::FilterTarget::File
    /// [`FilterTree`]: crate::FilterTree
    /// [`WalkEntry`]: crate::WalkEntry
    Tree,
}

/// Iterator adaptor that filters [`WalkEntry`]s and determines the traversal of
/// directory trees.
///
/// This adaptor is returned by [`IteratorExt::filter_tree`] and in addition to
/// filtering [`WalkEntry`]s also determines how `FileIterator`s walk directory
/// trees. If discarded directories do not need to be read from the file system,
/// then **this adaptor should be preferred over [`Iterator::filter`], because
/// it can avoid potentially large and unnecessary reads.**
///
/// `FilterTree` is a `FileIterator` and supports [`IteratorExt::filter_tree`].
/// This means that `filter_tree` may be chained.
///
/// [`IteratorExt::filter_tree`]: crate::IteratorExt::filter_tree
/// [`WalkEntry`]: crate::WalkEntry
#[derive(Clone, Debug)]
pub struct FilterTree<I, F> {
    input: I,
    f: F,
}

impl<I, F> Iterator for FilterTree<I, F>
where
    I: FileIterator<Item = WalkItem<'static>>,
    F: FnMut(&WalkEntry<'static>) -> Option<FilterTarget>,
{
    type Item = WalkItem<'static>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(result) = self.input.next() {
                if let Ok(entry) = result.as_ref() {
                    match (self.f)(entry) {
                        None => {
                            return Some(result);
                        },
                        Some(FilterTarget::File) => {
                            continue;
                        },
                        Some(FilterTarget::Tree) => {
                            if entry.file_type().is_dir() {
                                self.input.skip_tree();
                            }
                            continue;
                        },
                    }
                }
                else {
                    return Some(result);
                }
            }
            else {
                return None;
            }
        }
    }
}

impl<I, F> FileIterator for FilterTree<I, F>
where
    Self: Iterator,
    I: FileIterator,
{
    fn skip_tree(&mut self) {
        self.input.skip_tree()
    }
}

/// Describes a file matching a [`Glob`] in a directory tree.
///
/// [`Glob`]: crate::Glob
#[derive(Debug)]
pub struct WalkEntry<'e> {
    entry: Cow<'e, DirEntry>,
    matched: MatchedText<'e>,
}

impl<'e> WalkEntry<'e> {
    /// Clones any borrowed data into an owning instance.
    pub fn into_owned(self) -> WalkEntry<'static> {
        let WalkEntry { entry, matched } = self;
        WalkEntry {
            entry: Cow::Owned(entry.into_owned()),
            matched: matched.into_owned(),
        }
    }

    pub fn into_path(self) -> PathBuf {
        match self.entry {
            Cow::Borrowed(entry) => entry.path().to_path_buf(),
            Cow::Owned(entry) => entry.into_path(),
        }
    }

    /// Gets the absolute path of the matched file.
    pub fn path(&self) -> &Path {
        self.entry.path()
    }

    /// Converts the entry to the relative [`CandidatePath`].
    ///
    /// **This differs from [`path`] and [`into_path`], which are absolute
    /// paths. The [`CandidatePath`] is relative to the root of the directory
    /// tree.**
    ///
    /// [`CandidatePath`]: crate::CandidatePath
    /// [`into_path`]: crate::WalkEntry::into_path
    /// [`matched`]: crate::WalkEntry::matched
    /// [`path`]: crate::WalkEntry::path
    pub fn to_candidate_path(&self) -> CandidatePath<'_> {
        self.matched.to_candidate_path()
    }

    pub fn file_type(&self) -> FileType {
        self.entry.file_type()
    }

    pub fn metadata(&self) -> Result<Metadata, GlobError<'static>> {
        self.entry
            .metadata()
            .map_err(WalkError::from)
            .map_err(From::from)
    }

    /// Gets the depth of the file from the root of the directory tree.
    pub fn depth(&self) -> usize {
        self.entry.depth()
    }

    /// Gets the matched text in the path of the file.
    pub fn matched(&self) -> &MatchedText<'e> {
        &self.matched
    }
}

pub fn walk<'g>(
    glob: &'g Glob<'_>,
    directory: impl AsRef<Path>,
    behavior: impl Into<WalkBehavior>,
) -> Walk<'g> {
    let directory = directory.as_ref();
    let WalkBehavior { depth, link } = behavior.into();
    // The directory tree is traversed from `root`, which may include an
    // invariant prefix from the glob pattern. `Walk` patterns are only
    // applied to path components following the `prefix` (distinct from the
    // glob pattern prefix) in `root`.
    let (root, prefix, depth) = invariant_path_prefix(glob.tokenized.tokens())
        .map(|prefix| {
            let root = directory.join(&prefix).into();
            if prefix.is_absolute() {
                // Absolute paths replace paths with which they are joined,
                // in which case there is no prefix.
                (root, PathBuf::new().into(), depth)
            }
            else {
                // TODO: If the depth is exhausted by an invariant prefix
                //       path, then `Walk` should yield no entries. This
                //       computes a depth of zero when this occurs, so
                //       entries may still be yielded.
                // `depth` is relative to the input `directory`, so count
                // any components added by an invariant prefix path from the
                // glob.
                let depth = depth.saturating_sub(prefix.components().count());
                (root, directory.into(), depth)
            }
        })
        .unwrap_or_else(|| {
            let root = Cow::from(directory);
            (root.clone(), root, depth)
        });
    let components =
        Walk::compile(glob.tokenized.tokens()).expect("failed to compile glob sub-expressions");
    Walk {
        pattern: Cow::Borrowed(&glob.regex),
        components,
        prefix: prefix.into_owned(),
        walk: WalkDir::new(root)
            .follow_links(match link {
                LinkBehavior::ReadFile => false,
                LinkBehavior::ReadTarget => true,
            })
            .max_depth(depth)
            .into_iter(),
    }
}

fn invariant_path_prefix<'t, A, I>(tokens: I) -> Option<PathBuf>
where
    A: 't,
    I: IntoIterator<Item = &'t Token<'t, A>>,
{
    let prefix = token::invariant_text_prefix(tokens);
    if prefix.is_empty() {
        None
    }
    else {
        Some(prefix.into())
    }
}

/// Returns `true` if the [`Glob`] is terminal.
///
/// A [`Glob`] is terminal if its final component has unbounded depth and
/// unbounded variance. When walking a directory tree, such an expression allows
/// a matching directory to be ignored when used as a negation, because the
/// negating expression matches any and all sub-paths.
///
/// See [`Negation`].
///
/// [`Glob`]: crate::Glob
/// [`Negation`]: crate::walk::Negation
fn is_terminal(glob: &Glob<'_>) -> bool {
    let component = token::components(glob.tokenized.tokens()).last();
    matches!(
        component.map(|component| {
            (
                component.depth(),
                component.variance::<InvariantText>().boundedness(),
            )
        }),
        Some((Boundedness::Open, Boundedness::Open)),
    )
}

#[cfg(test)]
mod tests {
    use crate::walk;
    use crate::Glob;

    #[test]
    fn query_terminal_glob() {
        assert!(walk::is_terminal(&Glob::new("**").unwrap()));
        assert!(walk::is_terminal(&Glob::new("a/**").unwrap()));
        assert!(walk::is_terminal(&Glob::new("a/<*/>*").unwrap()));
        assert!(walk::is_terminal(&Glob::new("a/<<?>/>*").unwrap()));

        assert!(!walk::is_terminal(&Glob::new("a/**/b").unwrap()));
        assert!(!walk::is_terminal(&Glob::new("a/*").unwrap()));
        assert!(!walk::is_terminal(&Glob::new("a/<?>").unwrap()));
        assert!(!walk::is_terminal(&Glob::new("a</**/b>").unwrap()));
        assert!(!walk::is_terminal(&Glob::new("**/a").unwrap()));
        assert!(!walk::is_terminal(&Glob::new("").unwrap()));
    }
}
