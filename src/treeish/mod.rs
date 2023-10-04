mod parse;

use std::borrow::Cow;
use std::ops::Deref;
use std::path::Path;

use crate::Glob;

pub use crate::treeish::parse::parse;

// TODO: It is probably possible to implement this in a separate crate!

// TODO: Syntax like this:
//
//       `C:\Users::**/*.txt`
//       `/mnt/media1::**/*.txt`
//
//       This uses `::` as the separator. Consider `>>`.

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(transparent)]
pub struct Unrooted<T>(T);

impl<T> Unrooted<T> {
    fn map<U, F>(self, f: F) -> Unrooted<U>
    where
        F: FnOnce(T) -> U,
    {
        Unrooted(f(self.0))
    }
}

impl<'t> Unrooted<TreeishGlob<'t>> {
    pub fn into_owned(self) -> Unrooted<TreeishGlob<'static>> {
        self.map(TreeishGlob::into_owned)
    }
}

impl<T> AsRef<T> for Unrooted<T> {
    fn as_ref(&self) -> &T {
        &self.0
    }
}

impl<T> Deref for Unrooted<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
#[repr(transparent)]
pub struct TreeishPath<'p>(Cow<'p, Path>);

impl<'p> TreeishPath<'p> {
    pub fn into_owned(self) -> TreeishPath<'static> {
        TreeishPath(self.0.into_owned().into())
    }

    pub fn as_ref(&'p self) -> &'p Path {
        self.0.as_ref()
    }
}

impl<'p> Deref for TreeishPath<'p> {
    type Target = Cow<'p, Path>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<'p> From<TreeishPath<'p>> for Cow<'p, Path> {
    fn from(path: TreeishPath<'p>) -> Self {
        path.0
    }
}

#[derive(Clone, Debug)]
#[repr(transparent)]
pub struct TreeishGlob<'t>(Glob<'t>);

impl<'t> TreeishGlob<'t> {
    pub fn into_owned(self) -> TreeishGlob<'static> {
        TreeishGlob(self.0.into_owned())
    }
}

impl<'t> AsRef<Glob<'t>> for TreeishGlob<'t> {
    fn as_ref(&self) -> &Glob<'t> {
        &self.0
    }
}

impl<'t> Deref for TreeishGlob<'t> {
    type Target = Glob<'t>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<'t> From<TreeishGlob<'t>> for Glob<'t> {
    fn from(glob: TreeishGlob<'t>) -> Self {
        glob.0
    }
}

// TODO: What about "empty"? Arguably, path-like structures should not provide an intrinsic
//       representation of empty, like `Path("")`. Instead, an extrinsic representation like `None`
//       should be used and types like `Path` should **never** represent "nothing". `Treeish`
//       should do the same, and APIs should probably be fallible (or if not conceptually
//       "fallible" still yield `Option<Treeish>`).
pub enum Treeish<'t> {
    Path(TreeishPath<'t>),
    Pattern(TreeishGlob<'t>),
    PatternIn {
        tree: TreeishPath<'t>,
        glob: Unrooted<TreeishGlob<'t>>,
    },
}

impl<'t> Treeish<'t> {
    pub fn into_owned(self) -> Treeish<'static> {
        use Treeish::{Path, Pattern, PatternIn};

        match self {
            Path(path) => Path(path.into_owned()),
            Pattern(glob) => Pattern(glob.into_owned()),
            PatternIn { tree, glob } => PatternIn {
                tree: tree.into_owned(),
                glob: glob.into_owned(),
            },
        }
    }

    pub fn walk(&self) -> () {
        todo!()
    }

    pub fn is_semantic_match(&self, _: ()) -> bool {
        todo!()
    }
}

impl<'t> TryFrom<Glob<'t>> for Treeish<'t> {
    type Error = ();

    fn try_from(glob: Glob<'t>) -> Result<Self, Self::Error> {
        // TODO: This conversion does not handle an "empty" glob and there is no (good) way to
        //       determine if a glob is empty or not. `Glob::partition` should probably provide a
        //       better API for this!
        let (path, glob) = glob.partition();
        if glob.has_root() {
            return Err(());
        }
        let glob = TreeishGlob(glob);
        Ok(if path.as_os_str().is_empty() {
            Treeish::Pattern(glob)
        }
        else {
            Treeish::PatternIn {
                tree: TreeishPath(path.into()),
                glob: Unrooted(glob),
            }
        })
    }
}
