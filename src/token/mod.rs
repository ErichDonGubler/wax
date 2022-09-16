mod parse;
mod variance;

use itertools::{Itertools as _, PeekingNext};
use std::borrow::Cow;
use std::cmp;
use std::collections::{HashSet, VecDeque};
use std::mem;
use std::ops::Deref;
use std::path::{PathBuf, MAIN_SEPARATOR};
use std::slice;
use std::str;

use crate::diagnostics::{Span, SpanExt as _};
use crate::token::variance::{
    Coda, CompositeBreadth, CompositeDepth, Conjunction, ConjunctiveVariance, DisjunctiveVariance,
    IntoInvariantText, Invariance, UnitBreadth, UnitDepth, UnitVariance,
};
use crate::tree::TreeIterator;
use crate::{StrExt as _, PATHS_ARE_CASE_INSENSITIVE};

pub use crate::token::parse::{parse, Annotation, ParseError, ROOT_SEPARATOR_EXPRESSION};
pub use crate::token::variance::{
    invariant_text_prefix, is_exhaustive, Boundedness, InvariantSize, InvariantText, Variance,
};

macro_rules! grouped {
    ($entries:expr => |$group:ident| $f:block) => {
        $entries
            .into_iter()
            .peekable()
            .batching(move |entries| {
                entries
                    .peek()
                    .map(|first| first.position.group)
                    .and_then(|group| {
                        #[allow(unused_mut)]
                        let mut $group =
                            entries.peeking_take_while(|entry| entry.position.group == group);
                        $f
                    })
            })
            .fuse()
    };
}

pub trait TokenTree<'t>: Sized {
    type Annotation;

    fn into_tokens(self) -> Vec<Token<'t, Self::Annotation>>;

    fn tokens(&self) -> &[Token<'t, Self::Annotation>];

    fn walk(&self) -> Walk<'_, 't, Self::Annotation> {
        Walk::new(self.tokens())
    }
}

#[derive(Clone, Debug)]
pub struct Tokenized<'t, A = Annotation> {
    expression: Cow<'t, str>,
    tokens: Vec<Token<'t, A>>,
}

impl<'t, A> Tokenized<'t, A> {
    pub fn into_owned(self) -> Tokenized<'static, A> {
        let Tokenized { expression, tokens } = self;
        Tokenized {
            expression: expression.into_owned().into(),
            tokens: tokens.into_iter().map(Token::into_owned).collect(),
        }
    }

    pub fn expression(&self) -> &Cow<'t, str> {
        &self.expression
    }

    pub fn variance<T>(&self) -> Variance<T>
    where
        T: Invariance,
        for<'i> &'i Token<'t, A>: UnitVariance<T, ()>,
    {
        self.tokens().iter().conjunctive_variance()
    }
}

impl<'t> Tokenized<'t, Annotation> {
    pub fn partition(self) -> (PathBuf, Self) {
        fn pop_expression_bytes(expression: &str, n: usize) -> &str {
            let n = cmp::min(expression.len(), n);
            str::from_utf8(&expression.as_bytes()[n..])
                .expect("span offset split UTF-8 byte sequence")
        }

        let Tokenized {
            expression,
            mut tokens,
        } = self;

        // Get the invariant prefix and its upper bound for the token sequence.
        let prefix = variance::invariant_text_prefix(tokens.iter()).into();
        let n = variance::invariant_text_prefix_upper_bound(&tokens);
        let mut offset: usize = tokens
            .iter()
            .take(n)
            .map(|token| token.annotation().1)
            .sum();

        // Drain invariant tokens from the beginning of the token sequence and
        // unroot any tokens at the beginning of the variant sequence (tree
        // wildcards). Finally, translate spans and discard the corresponding
        // invariant bytes in the expression.
        tokens.drain(0..n);
        if tokens.first_mut().map_or(false, Token::unroot) {
            // TODO: The relationship between roots, the unrooting operation,
            //       and the span in an expression that represents such a root
            //       (if any) is not captured by these APIs very well. Perhaps
            //       `unroot` should do more here?
            // Pop additional bytes for the root separator expression if the
            // initial token has lost a root.
            offset += ROOT_SEPARATOR_EXPRESSION.len();
        }
        for token in tokens.iter_mut() {
            let start = token.annotation().0.saturating_sub(offset);
            token.annotation.0 = start;
        }
        let expression = match expression {
            Cow::Borrowed(expression) => pop_expression_bytes(expression, offset).into(),
            Cow::Owned(expression) => {
                String::from(pop_expression_bytes(&expression, offset)).into()
            },
        };

        (prefix, Tokenized { expression, tokens })
    }
}

impl<'t, A> TokenTree<'t> for Tokenized<'t, A> {
    type Annotation = A;

    fn into_tokens(self) -> Vec<Token<'t, Self::Annotation>> {
        let Tokenized { tokens, .. } = self;
        tokens
    }

    fn tokens(&self) -> &[Token<'t, Self::Annotation>] {
        &self.tokens
    }
}

#[derive(Clone, Debug)]
pub struct Token<'t, A = Annotation> {
    kind: TokenKind<'t, A>,
    annotation: A,
}

impl<'t, A> Token<'t, A> {
    fn new(kind: TokenKind<'t, A>, annotation: A) -> Self {
        Token { kind, annotation }
    }

    pub fn into_owned(self) -> Token<'static, A> {
        let Token { kind, annotation } = self;
        Token {
            kind: kind.into_owned(),
            annotation,
        }
    }

    pub fn unannotate(self) -> Token<'t, ()> {
        let Token { kind, .. } = self;
        Token {
            kind: kind.unannotate(),
            annotation: (),
        }
    }

    pub fn unroot(&mut self) -> bool {
        self.kind.unroot()
    }

    pub fn kind(&self) -> &TokenKind<'t, A> {
        self.as_ref()
    }

    pub fn annotation(&self) -> &A {
        self.as_ref()
    }

    pub fn walk(&self) -> Walk<'_, 't, A> {
        Walk::new(slice::from_ref(self))
    }

    pub fn has_root(&self) -> bool {
        inclusive_starting_subtree(self.walk()).any(|entry| {
            matches!(
                entry.kind(),
                TokenKind::Separator(_) | TokenKind::Wildcard(Wildcard::Tree { has_root: true }),
            )
        })
    }

    pub fn has_component_boundary(&self) -> bool {
        self.walk().any(|token| token.is_component_boundary())
    }
}

impl<'t, A> AsRef<TokenKind<'t, A>> for Token<'t, A> {
    fn as_ref(&self) -> &TokenKind<'t, A> {
        &self.kind
    }
}

impl<'t, A> AsRef<A> for Token<'t, A> {
    fn as_ref(&self) -> &A {
        &self.annotation
    }
}

impl<'t, A> Deref for Token<'t, A> {
    type Target = TokenKind<'t, A>;

    fn deref(&self) -> &Self::Target {
        self.as_ref()
    }
}

impl<'t> From<TokenKind<'t, ()>> for Token<'t, ()> {
    fn from(kind: TokenKind<'t, ()>) -> Self {
        Token {
            kind,
            annotation: (),
        }
    }
}

impl<'t, A> TokenTree<'t> for Token<'t, A> {
    type Annotation = A;

    fn into_tokens(self) -> Vec<Token<'t, Self::Annotation>> {
        vec![self]
    }

    fn tokens(&self) -> &[Token<'t, Self::Annotation>] {
        slice::from_ref(self)
    }
}

impl<'i, 't, A> UnitBreadth for &'i Token<'t, A> {
    fn unit_breadth(self) -> Boundedness {
        self.kind.unit_breadth()
    }
}

impl<'i, 't, A> UnitDepth for &'i Token<'t, A> {
    fn unit_depth(self) -> Boundedness {
        self.kind.unit_depth()
    }
}

impl<'i, 't, A, T, C> UnitVariance<T, C> for &'i Token<'t, A>
where
    &'i TokenKind<'t, A>: UnitVariance<T, C>,
    T: Invariance,
{
    fn unit_variance(self) -> Variance<T> {
        self.kind.unit_variance()
    }
}

#[derive(Clone, Debug)]
pub enum TokenKind<'t, A = ()> {
    Alternative(Alternative<'t, A>),
    Class(Class),
    Literal(Literal<'t>),
    Repetition(Repetition<'t, A>),
    Separator(Separator),
    Wildcard(Wildcard),
}

impl<'t, A> TokenKind<'t, A> {
    pub fn into_owned(self) -> TokenKind<'static, A> {
        match self {
            TokenKind::Alternative(alternative) => alternative.into_owned().into(),
            TokenKind::Class(class) => TokenKind::Class(class),
            TokenKind::Literal(Literal {
                text,
                is_case_insensitive,
            }) => TokenKind::Literal(Literal {
                text: text.into_owned().into(),
                is_case_insensitive,
            }),
            TokenKind::Repetition(repetition) => repetition.into_owned().into(),
            TokenKind::Separator(_) => TokenKind::Separator(Separator),
            TokenKind::Wildcard(wildcard) => TokenKind::Wildcard(wildcard),
        }
    }

    pub fn unannotate(self) -> TokenKind<'t, ()> {
        match self {
            TokenKind::Alternative(alternative) => TokenKind::Alternative(alternative.unannotate()),
            TokenKind::Class(class) => TokenKind::Class(class),
            TokenKind::Literal(literal) => TokenKind::Literal(literal),
            TokenKind::Repetition(repetition) => TokenKind::Repetition(repetition.unannotate()),
            TokenKind::Separator(_) => TokenKind::Separator(Separator),
            TokenKind::Wildcard(wildcard) => TokenKind::Wildcard(wildcard),
        }
    }

    pub fn unroot(&mut self) -> bool {
        match self {
            TokenKind::Wildcard(Wildcard::Tree { ref mut has_root }) => {
                mem::replace(has_root, false)
            },
            _ => false,
        }
    }

    pub fn variance<T>(&self) -> Variance<T>
    where
        T: Invariance,
        for<'i> &'i TokenKind<'t, A>: UnitVariance<T, ()>,
    {
        self.unit_variance()
    }

    pub fn has_subtree(&self) -> bool {
        // It is not necessary to detect empty branches or sub-expressions.
        matches!(self, TokenKind::Alternative(_) | TokenKind::Repetition(_))
    }

    pub fn is_component_boundary(&self) -> bool {
        matches!(
            self,
            TokenKind::Separator(_) | TokenKind::Wildcard(Wildcard::Tree { .. })
        )
    }

    pub fn is_capturing(&self) -> bool {
        use TokenKind::{Alternative, Class, Repetition, Wildcard};

        matches!(
            self,
            Alternative(_) | Class(_) | Repetition(_) | Wildcard(_),
        )
    }
}

impl<'t, A> From<Alternative<'t, A>> for TokenKind<'t, A> {
    fn from(alternative: Alternative<'t, A>) -> Self {
        TokenKind::Alternative(alternative)
    }
}

impl<A> From<Class> for TokenKind<'_, A> {
    fn from(class: Class) -> Self {
        TokenKind::Class(class)
    }
}

impl<'t, A> From<Repetition<'t, A>> for TokenKind<'t, A> {
    fn from(repetition: Repetition<'t, A>) -> Self {
        TokenKind::Repetition(repetition)
    }
}

impl<A> From<Wildcard> for TokenKind<'static, A> {
    fn from(wildcard: Wildcard) -> Self {
        TokenKind::Wildcard(wildcard)
    }
}

impl<'i, 't, A> UnitBreadth for &'i TokenKind<'t, A> {
    fn unit_breadth(self) -> Boundedness {
        match self {
            TokenKind::Alternative(ref alternative) => alternative.unit_breadth(),
            TokenKind::Class(ref class) => class.unit_breadth(),
            TokenKind::Literal(ref literal) => literal.unit_breadth(),
            TokenKind::Repetition(ref repetition) => repetition.unit_breadth(),
            TokenKind::Separator(ref separator) => separator.unit_breadth(),
            TokenKind::Wildcard(ref wildcard) => wildcard.unit_breadth(),
        }
    }
}

impl<'i, 't, A> UnitDepth for &'i TokenKind<'t, A> {
    fn unit_depth(self) -> Boundedness {
        match self {
            TokenKind::Alternative(ref alternative) => alternative.unit_depth(),
            TokenKind::Class(ref class) => class.unit_depth(),
            TokenKind::Literal(ref literal) => literal.unit_depth(),
            TokenKind::Repetition(ref repetition) => repetition.unit_depth(),
            TokenKind::Separator(ref separator) => separator.unit_depth(),
            TokenKind::Wildcard(ref wildcard) => wildcard.unit_depth(),
        }
    }
}

impl<'i, 't, A, T, C> UnitVariance<T, C> for &'i TokenKind<'t, A>
where
    &'i Alternative<'t, A>: UnitVariance<T, C>,
    &'i Class: UnitVariance<T, C>,
    &'i Literal<'t>: UnitVariance<T, C>,
    &'i Repetition<'t, A>: UnitVariance<T, C>,
    &'i Separator: UnitVariance<T, C>,
    T: Invariance,
{
    fn unit_variance(self) -> Variance<T> {
        match self {
            TokenKind::Alternative(ref alternative) => alternative.unit_variance(),
            TokenKind::Class(ref class) => class.unit_variance(),
            TokenKind::Literal(ref literal) => literal.unit_variance(),
            TokenKind::Repetition(ref repetition) => repetition.unit_variance(),
            TokenKind::Separator(ref separator) => separator.unit_variance(),
            TokenKind::Wildcard(_) => Variance::Variant(Boundedness::Open),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Alternative<'t, A = ()>(Vec<Vec<Token<'t, A>>>);

impl<'t, A> Alternative<'t, A> {
    pub fn into_owned(self) -> Alternative<'static, A> {
        Alternative(
            self.0
                .into_iter()
                .map(|tokens| tokens.into_iter().map(Token::into_owned).collect())
                .collect(),
        )
    }

    pub fn unannotate(self) -> Alternative<'t, ()> {
        let Alternative(branches) = self;
        Alternative(
            branches
                .into_iter()
                .map(|branch| branch.into_iter().map(Token::unannotate).collect())
                .collect(),
        )
    }

    pub fn branches(&self) -> &Vec<Vec<Token<'t, A>>> {
        &self.0
    }
}

impl<'t, A> From<Vec<Vec<Token<'t, A>>>> for Alternative<'t, A> {
    fn from(alternatives: Vec<Vec<Token<'t, A>>>) -> Self {
        Alternative(alternatives)
    }
}

impl<'i, 't, A, T> Conjunction<'i, T, ()> for &'i Alternative<'t, A>
where
    't: 'i,
    A: 't,
    T: Invariance,
{
    type Item = &'i Token<'t, A>;

    fn conjunction(tokens: impl IntoIterator<Item = Self::Item>) -> Variance<T>
    where
        Self::Item: UnitVariance<T, ()>,
    {
        tokens.into_iter().conjunctive_variance()
    }
}

impl<'i, 't, A, T> Conjunction<'i, T, Coda> for &'i Alternative<'t, A>
where
    't: 'i,
    A: 't,
    T: Invariance,
{
    type Item = &'i Token<'t, A>;

    fn conjunction(tokens: impl IntoIterator<Item = Self::Item>) -> Variance<T>
    where
        Self::Item: UnitVariance<T, Coda>,
    {
        components(tokens)
            .last()
            .into_iter()
            .flat_map(|component| component.0)
            .conjunctive_variance()
    }
}

impl<'i, 't, A> UnitBreadth for &'i Alternative<'t, A> {
    fn unit_breadth(self) -> Boundedness {
        self.branches()
            .iter()
            .map(|tokens| tokens.iter().composite_breadth())
            .composite_breadth()
    }
}

impl<'i, 't, A> UnitDepth for &'i Alternative<'t, A> {
    fn unit_depth(self) -> Boundedness {
        self.branches()
            .iter()
            .map(|tokens| tokens.iter().composite_depth())
            .composite_depth()
    }
}

impl<'i, 't, A, T, C> UnitVariance<T, C> for &'i Alternative<'t, A>
where
    't: 'i,
    Self: Conjunction<'i, T, C, Item = &'i Token<'t, A>>,
    // TODO: It seems that this bound *may* trigger a compiler bug that causes
    //       an infinite loop when normalizing bounds on associated types.
    //<Self as Conjunction<'i, T, C>>::Item: UnitVariance<T, C>,
    A: 't,
    T: Invariance,
{
    fn unit_variance(self) -> Variance<T> {
        DisjunctiveVariance::<T, C>::disjunctive_variance(
            self.branches().iter().map(Self::conjunction),
        )
    }
}

#[derive(Clone, Copy, Debug)]
pub enum Archetype {
    Character(char),
    Range(char, char),
}

impl Archetype {
    fn domain_variance(&self) -> Variance<char> {
        match self {
            Archetype::Character(x) => {
                if PATHS_ARE_CASE_INSENSITIVE {
                    Variance::Variant(Boundedness::Closed)
                }
                else {
                    Variance::Invariant(*x)
                }
            },
            Archetype::Range(a, b) => {
                if (a != b) || PATHS_ARE_CASE_INSENSITIVE {
                    Variance::Variant(Boundedness::Closed)
                }
                else {
                    Variance::Invariant(*a)
                }
            },
        }
    }
}

impl From<char> for Archetype {
    fn from(literal: char) -> Self {
        Archetype::Character(literal)
    }
}

impl From<(char, char)> for Archetype {
    fn from(range: (char, char)) -> Self {
        Archetype::Range(range.0, range.1)
    }
}

impl<'i, 't, C> UnitVariance<InvariantText<'t>, C> for &'i Archetype {
    fn unit_variance(self) -> Variance<InvariantText<'t>> {
        self.domain_variance()
            .map_invariance(|invariance| invariance.to_string().into_nominal_text())
    }
}

impl<'i, C> UnitVariance<InvariantSize, C> for &'i Archetype {
    fn unit_variance(self) -> Variance<InvariantSize> {
        // This is pessimistic and assumes that the code point will require four
        // bytes when encoded as UTF-8. This is technically possible, but most
        // commonly only one or two bytes will be required.
        self.domain_variance().map_invariance(|_| 4.into())
    }
}

#[derive(Clone, Debug)]
pub struct Class {
    is_negated: bool,
    archetypes: Vec<Archetype>,
}

impl Class {
    pub fn archetypes(&self) -> &[Archetype] {
        &self.archetypes
    }

    pub fn is_negated(&self) -> bool {
        self.is_negated
    }
}

impl<'i> UnitBreadth for &'i Class {}

impl<'i> UnitDepth for &'i Class {}

impl<'i, T, C> UnitVariance<T, C> for &'i Class
where
    &'i Archetype: UnitVariance<T, C>,
    T: Invariance,
{
    fn unit_variance(self) -> Variance<T> {
        if self.is_negated {
            // It is not feasible to encode a character class that matches all
            // UTF-8 text and therefore nothing when negated, and so a character
            // class must be variant if it is negated.
            Variance::Variant(Boundedness::Closed)
        }
        else {
            // TODO: This ignores casing groups, such as in the pattern `[aA]`.
            self.archetypes().iter().disjunctive_variance()
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub enum Evaluation {
    Eager,
    Lazy,
}

#[derive(Clone, Debug)]
pub struct Literal<'t> {
    text: Cow<'t, str>,
    is_case_insensitive: bool,
}

impl<'t> Literal<'t> {
    pub fn text(&self) -> &str {
        self.text.as_ref()
    }

    fn domain_variance(&self) -> Variance<&Cow<'t, str>> {
        if self.has_variant_casing() {
            Variance::Variant(Boundedness::Closed)
        }
        else {
            Variance::Invariant(&self.text)
        }
    }

    pub fn is_case_insensitive(&self) -> bool {
        self.is_case_insensitive
    }

    pub fn has_variant_casing(&self) -> bool {
        // If path case sensitivity agrees with the literal case sensitivity,
        // then the literal is not variant. Otherwise, the literal is variant if
        // it contains characters with casing.
        (PATHS_ARE_CASE_INSENSITIVE != self.is_case_insensitive) && self.text.has_casing()
    }
}

impl<'i, 't> UnitBreadth for &'i Literal<'t> {}

impl<'i, 't> UnitDepth for &'i Literal<'t> {}

impl<'i, 't, C> UnitVariance<InvariantText<'t>, C> for &'i Literal<'t> {
    fn unit_variance(self) -> Variance<InvariantText<'t>> {
        self.domain_variance()
            .map_invariance(|invariance| invariance.clone().into_nominal_text())
    }
}

impl<'i, 't, C> UnitVariance<InvariantSize, C> for &'i Literal<'t> {
    fn unit_variance(self) -> Variance<InvariantSize> {
        self.domain_variance()
            .map_invariance(|invariance| invariance.as_bytes().len().into())
    }
}

#[derive(Clone, Debug)]
pub struct Repetition<'t, A = ()> {
    tokens: Vec<Token<'t, A>>,
    lower: usize,
    // This representation is not ideal, as it does not statically enforce the
    // invariant that the upper bound is greater than or equal to the lower
    // bound. For example, this field could instead be a summand. However,
    // tokens must closely resemble their glob expression representations so
    // that errors in expressions can be deferred and presented more clearly.
    // Failures in the parser are difficult to describe.
    upper: Option<usize>,
}

impl<'t, A> Repetition<'t, A> {
    pub fn into_owned(self) -> Repetition<'static, A> {
        let Repetition {
            tokens,
            lower,
            upper,
        } = self;
        Repetition {
            tokens: tokens.into_iter().map(Token::into_owned).collect(),
            lower,
            upper,
        }
    }

    pub fn unannotate(self) -> Repetition<'t, ()> {
        let Repetition {
            tokens,
            lower,
            upper,
        } = self;
        Repetition {
            tokens: tokens.into_iter().map(Token::unannotate).collect(),
            lower,
            upper,
        }
    }

    pub fn tokens(&self) -> &Vec<Token<'t, A>> {
        &self.tokens
    }

    pub fn bounds(&self) -> (usize, Option<usize>) {
        (self.lower, self.upper)
    }

    pub fn is_converged(&self) -> bool {
        self.upper.map_or(false, |upper| self.lower == upper)
    }

    fn walk(&self) -> Walk<'_, 't, A> {
        Walk::new(self.tokens.as_slice())
    }

    fn coalesce_boundary_variance<'i, T, C>(
        tokens: impl IntoIterator<Item = &'i Token<'t, A>>,
    ) -> impl Iterator<Item = &'i Token<'t, A>>
    where
        't: 'i,
        &'i Token<'t, A>: UnitVariance<T, C>,
        A: 't,
    {
        use TokenKind::Separator;
        use Variance::Variant;

        tokens
            .into_iter()
            // Coalesce tokens with open variance together with separators. This
            // isn't destructive and doesn't affect invariance, because this
            // only happens in the presence of open variance, which means that
            // the repetition is variant (and has no invariant size or text).
            .coalesce(|left, right| {
                match (
                    (left.kind(), left.unit_variance()),
                    (right.kind(), right.unit_variance()),
                ) {
                    ((Separator(_), _), (_, Variant(Open))) => Ok(right),
                    ((_, Variant(Open)), (Separator(_), _)) => Ok(left),
                    _ => Err((left, right)),
                }
            })
    }
}

impl<'i, 't, A, T> Conjunction<'i, T, ()> for &'i Repetition<'t, A>
where
    't: 'i,
    A: 't,
    T: Invariance,
{
    type Item = &'i Token<'t, A>;

    fn conjunction(tokens: impl IntoIterator<Item = Self::Item>) -> Variance<T>
    where
        Self::Item: UnitVariance<T, ()>,
    {
        Repetition::coalesce_boundary_variance(tokens.into_iter()).conjunctive_variance()
    }
}

impl<'i, 't, A, T> Conjunction<'i, T, Coda> for &'i Repetition<'t, A>
where
    't: 'i,
    A: 't,
    T: Invariance,
{
    type Item = &'i Token<'t, A>;

    fn conjunction(tokens: impl IntoIterator<Item = Self::Item>) -> Variance<T>
    where
        Self::Item: UnitVariance<T, Coda>,
    {
        Repetition::coalesce_boundary_variance(
            components(tokens)
                .last()
                .into_iter()
                .flat_map(|component| component.0),
        )
        .conjunctive_variance()
    }
}

impl<'i, 't, A> UnitBreadth for &'i Repetition<'t, A> {
    fn unit_breadth(self) -> Boundedness {
        self.tokens().iter().composite_breadth()
    }
}

impl<'i, 't, A> UnitDepth for &'i Repetition<'t, A> {
    fn unit_depth(self) -> Boundedness {
        if self.tokens().iter().composite_depth().is_open() {
            Boundedness::Open
        }
        else {
            let (_, upper) = self.bounds();
            if upper.is_none() && self.walk().any(|token| token.is_component_boundary()) {
                Boundedness::Open
            }
            else {
                Boundedness::Closed
            }
        }
    }
}

impl<'i, 't, A, T, C> UnitVariance<T, C> for &'i Repetition<'t, A>
where
    't: 'i,
    Self: Conjunction<'i, T, C, Item = &'i Token<'t, A>>,
    //<Self as Conjunction<'i, T, C>>::Item: UnitVariance<T, C>,
    A: 't,
    T: Invariance,
{
    fn unit_variance(self) -> Variance<T> {
        use Boundedness::Open;
        use Variance::Variant;

        let variance = Self::conjunction(self.tokens());
        match self.upper {
            // Repeating invariance can cause overflows, very large allocations,
            // and very inefficient comparisons (e.g., comparing very large
            // strings). This is detected by both `encode::compile` and
            // `rule::check` (in distinct but similar ways). Querying token
            // trees for their invariance must be done with care (after using
            // these functions) to avoid expanding pathological invariant
            // expressions like `<long:9999999999999>`.
            Some(_) if self.is_converged() => {
                variance.map_invariance(|invariance| invariance * self.lower)
            },
            _ => variance + Variant(Open),
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Separator;

impl Separator {
    pub fn invariant_text() -> String {
        MAIN_SEPARATOR.to_string()
    }
}

impl<'i> UnitBreadth for &'i Separator {}

impl<'i> UnitDepth for &'i Separator {}

impl<'i, 't, C> UnitVariance<InvariantText<'t>, C> for &'i Separator {
    fn unit_variance(self) -> Variance<InvariantText<'t>> {
        Variance::Invariant(Separator::invariant_text().into_structural_text())
    }
}

impl<'i, C> UnitVariance<InvariantSize, C> for &'i Separator {
    fn unit_variance(self) -> Variance<InvariantSize> {
        Variance::Invariant(Separator::invariant_text().as_bytes().len().into())
    }
}

#[derive(Clone, Debug)]
pub enum Wildcard {
    One,
    ZeroOrMore(Evaluation),
    Tree { has_root: bool },
}

impl<'i> UnitBreadth for &'i Wildcard {
    fn unit_breadth(self) -> Boundedness {
        match self {
            Wildcard::One => Boundedness::Closed,
            _ => Boundedness::Open,
        }
    }
}

impl<'i> UnitDepth for &'i Wildcard {
    fn unit_depth(self) -> Boundedness {
        match self {
            Wildcard::Tree { .. } => Boundedness::Open,
            _ => Boundedness::Closed,
        }
    }
}

pub type MapOutput<M, T, U> = <M as ClosedMap<T, U>>::Output;

pub trait ClosedMap<T, U> {
    type Output;

    fn map<F>(self, f: F) -> Self::Output
    where
        F: FnOnce(T) -> U;
}

impl<'i, 't, A, U> ClosedMap<&'i Token<'t, A>, U> for &'i Token<'t, A>
where
    't: 'i,
    A: 't,
{
    type Output = U;

    fn map<F>(self, f: F) -> Self::Output
    where
        F: FnOnce(&'i Token<'t, A>) -> U,
    {
        f(self)
    }
}

pub trait TokenEntry<'i, 't, A> {
    fn map_token<U, F>(self, f: F) -> MapOutput<Self, &'i Token<'t, A>, U>
    where
        Self: ClosedMap<&'i Token<'t, A>, U> + Sized,
        F: FnOnce(&'i Token<'t, A>) -> U,
    {
        self.map(f)
    }

    fn as_token(&self) -> &'i Token<'t, A>;
}

impl<'i, 't, A> TokenEntry<'i, 't, A> for &'i Token<'t, A> {
    fn as_token(&self) -> &'i Token<'t, A> {
        *self
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Position {
    pub index: usize,
    pub group: Group,
}

impl Position {
    // This may appear to operate in place.
    #[must_use]
    fn converge(self) -> Self {
        let Position { index, group } = self;
        Position {
            index: index + 1,
            group: group.converge(),
        }
    }

    // This may appear to operate in place.
    #[must_use]
    fn diverge(self, branch: usize) -> Self {
        let Position { index, group } = self;
        Position {
            index: index + 1,
            group: group.diverge(branch),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Group {
    Conjunctive { depth: usize },
    Disjunctive { depth: usize, branch: usize },
}

impl Group {
    pub fn depth(&self) -> usize {
        match self {
            Group::Conjunctive { ref depth, .. } | Group::Disjunctive { ref depth, .. } => *depth,
        }
    }

    pub fn branch(&self) -> Option<usize> {
        if let Group::Disjunctive { ref branch, .. } = self {
            Some(*branch)
        }
        else {
            None
        }
    }

    // This may appear to operate in place.
    #[must_use]
    fn converge(self) -> Self {
        match self {
            Group::Conjunctive { depth, .. } | Group::Disjunctive { depth, .. } => {
                Group::Conjunctive { depth: depth + 1 }
            },
        }
    }

    // This may appear to operate in place.
    #[must_use]
    fn diverge(self, branch: usize) -> Self {
        match self {
            Group::Conjunctive { depth, .. } | Group::Disjunctive { depth, .. } => {
                Group::Disjunctive {
                    depth: depth + 1,
                    branch,
                }
            },
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct WalkEntry<T> {
    pub parent: Option<Position>,
    pub position: Position,
    pub item: T,
}

impl<T> WalkEntry<T> {
    pub fn map_item<U, F>(self, f: F) -> WalkEntry<U>
    where
        F: FnOnce(T) -> U,
    {
        let WalkEntry {
            parent,
            position,
            item,
        } = self;
        WalkEntry {
            parent,
            position,
            item: f(item),
        }
    }

    pub fn into_item(self) -> T {
        self.item
    }
}

impl<'i, 't, A, U> ClosedMap<&'i Token<'t, A>, U> for WalkEntry<&'i Token<'t, A>>
where
    't: 'i,
    A: 't,
{
    type Output = WalkEntry<U>;

    fn map<F>(self, f: F) -> Self::Output
    where
        F: FnOnce(&'i Token<'t, A>) -> U,
    {
        self.map_item(f)
    }
}

impl<'i, 't, A> TokenEntry<'i, 't, A> for WalkEntry<&'i Token<'t, A>> {
    fn as_token(&self) -> &'i Token<'t, A> {
        self.item
    }
}

impl<T> Deref for WalkEntry<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.item
    }
}

#[derive(Clone, Debug)]
pub struct Walk<'i, 't, A> {
    is_committing: bool,
    staged: Vec<WalkEntry<&'i Token<'t, A>>>,
    committed: VecDeque<WalkEntry<&'i Token<'t, A>>>,
}

impl<'i, 't, A> Walk<'i, 't, A> {
    fn new(tokens: impl IntoIterator<Item = &'i Token<'t, A>>) -> Self {
        Walk {
            is_committing: true,
            staged: vec![],
            committed: tokens
                .into_iter()
                .enumerate()
                .map(|(index, token)| WalkEntry {
                    parent: None,
                    position: Position {
                        index,
                        group: Group::Conjunctive { depth: 0 },
                    },
                    item: token,
                })
                .collect(),
        }
    }

    pub fn components(self) -> impl 'i + Iterator<Item = WalkEntry<Component<'i, 't, A>>>
    where
        't: 'i,
        A: 't,
    {
        grouped!(self => |tokens| {
            let (_, component) = Component::take(tokens);
            component
        })
    }
}

impl<'i, 't, A> Iterator for Walk<'i, 't, A>
where
    't: 'i,
    A: 't,
{
    type Item = WalkEntry<&'i Token<'t, A>>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.is_committing {
            self.committed.extend(self.staged.drain(..));
        }
        else {
            self.staged.clear();
        }
        self.is_committing = true;
        if let Some(entry) = self.committed.pop_front() {
            match entry.kind() {
                TokenKind::Alternative(ref alternative) => {
                    self.staged
                        .extend(alternative.branches().iter().enumerate().flat_map(
                            |(branch, tokens)| {
                                tokens.iter().map(move |token| WalkEntry {
                                    parent: Some(entry.position),
                                    position: entry.position.diverge(branch),
                                    item: token,
                                })
                            },
                        ));
                },
                TokenKind::Repetition(ref repetition) => {
                    self.staged
                        .extend(repetition.tokens().iter().map(|token| WalkEntry {
                            parent: Some(entry.position),
                            position: entry.position.converge(),
                            item: token,
                        }));
                },
                _ => {},
            }
            Some(entry)
        }
        else {
            None
        }
    }
}

impl<'i, 't, A> TreeIterator for Walk<'i, 't, A>
where
    't: 'i,
    A: 't,
{
    fn skip_tree(&mut self) {
        self.is_committing = false;
    }
}

#[derive(Clone, Debug)]
pub struct LiteralSequence<'i, 't>(Vec<&'i Literal<'t>>);

impl<'i, 't> LiteralSequence<'i, 't> {
    pub fn literals(&self) -> &[&'i Literal<'t>] {
        self.0.as_ref()
    }

    pub fn text(&self) -> Cow<'t, str> {
        if self.literals().len() == 1 {
            self.literals().first().unwrap().text.clone()
        }
        else {
            self.literals()
                .iter()
                .map(|literal| &literal.text)
                .join("")
                .into()
        }
    }

    #[cfg(any(unix, windows))]
    pub fn is_semantic(&self) -> bool {
        matches!(self.text().as_ref(), "." | "..")
    }

    #[cfg(not(any(unix, windows)))]
    pub fn is_semantic(&self) -> bool {
        false
    }
}

#[derive(Debug)]
pub struct Component<'i, 't, A = Annotation>(Vec<&'i Token<'t, A>>);

impl<'i, 't, A> Component<'i, 't, A> {
    // The output type is somewhat specific here and may become less clear if
    // more type definitions are introduced.
    #[allow(clippy::type_complexity)]
    fn take<I>(mut tokens: I) -> (I, Option<MapOutput<I::Item, &'i Token<'t, A>, Self>>)
    where
        't: 'i,
        A: 't,
        I: PeekingNext,
        I::Item: ClosedMap<&'i Token<'t, A>, Self> + TokenEntry<'i, 't, A>,
    {
        let mut first = tokens.next();
        while matches!(
            first.as_ref().map(|first| first.as_token().kind()),
            Some(TokenKind::Separator(_))
        ) {
            first = tokens.next();
        }
        let component = first.map(|first| match first.as_token().kind() {
            TokenKind::Wildcard(Wildcard::Tree { .. }) => {
                first.map_token(|first| Component(vec![first]))
            },
            _ => first.map_token(|first| {
                Component(
                    Some(first)
                        .into_iter()
                        .chain(
                            tokens
                                .peeking_take_while(|token| {
                                    !token.as_token().is_component_boundary()
                                })
                                .map(|token| token.as_token()),
                        )
                        .collect(),
                )
            }),
        });
        (tokens, component)
    }

    pub fn literal(&self) -> Option<LiteralSequence<'i, 't>> {
        if self.0.is_empty() {
            None
        }
        else {
            self.tokens()
                .iter()
                .all(|token| matches!(token.kind(), TokenKind::Literal(_)))
                .then(|| {
                    LiteralSequence(
                        self.tokens()
                            .iter()
                            .map(|token| match token.kind() {
                                TokenKind::Literal(ref literal) => literal,
                                _ => unreachable!(), // See predicate above.
                            })
                            .collect(),
                    )
                })
        }
    }

    pub fn tokens(&self) -> &[&'i Token<'t, A>] {
        self.0.as_ref()
    }

    pub fn walk(&self) -> Walk<'i, 't, A> {
        Walk::new(self.tokens().iter().copied())
    }

    pub fn variance<T>(&self) -> Variance<T>
    where
        T: Invariance,
        &'i Token<'t, A>: UnitVariance<T, ()>,
    {
        self.0.iter().copied().conjunctive_variance()
    }

    pub fn depth(&self) -> Boundedness {
        self.0.iter().copied().composite_depth()
    }
}

impl<'i, 't> Component<'i, 't, Annotation> {
    pub fn span(&self) -> Option<Span> {
        self.tokens()
            .iter()
            .map(|token| *token.annotation())
            .reduce(|left, right| left.union(&right))
    }
}

impl<'i, 't, A> Clone for Component<'i, 't, A> {
    fn clone(&self) -> Self {
        Component(self.0.clone())
    }
}

pub fn any<'t, A, I>(tokens: I) -> Token<'t, ()>
where
    I: IntoIterator,
    I::Item: IntoIterator<Item = Token<'t, A>>,
{
    Token {
        kind: Alternative(
            tokens
                .into_iter()
                .map(|tokens| tokens.into_iter().map(Token::unannotate).collect())
                .collect(),
        )
        .into(),
        annotation: (),
    }
}

pub fn components<'i, 't, A, I>(tokens: I) -> impl Iterator<Item = Component<'i, 't, A>>
where
    't: 'i,
    A: 't,
    I: IntoIterator<Item = &'i Token<'t, A>>,
{
    tokens
        .into_iter()
        .peekable()
        .batching(|tokens| {
            let (_, component) = Component::take(tokens);
            component
        })
        .fuse()
}

pub fn inclusive_starting_subtree<T, I>(entries: I) -> impl Iterator<Item = WalkEntry<T>>
where
    I: IntoIterator<Item = WalkEntry<T>>,
{
    grouped!(entries => |entries| {
        let first = entries.next();
        entries.for_each(drop);
        first
    })
}

pub fn inclusive_ending_subtree<T, I>(entries: I) -> impl Iterator<Item = WalkEntry<T>>
where
    I: IntoIterator<Item = WalkEntry<T>>,
{
    grouped!(entries => |entries| { entries.last() })
}

pub fn exclusive_ending_subtree<T, I>(entries: I) -> impl Iterator<Item = WalkEntry<T>>
where
    I: IntoIterator<Item = WalkEntry<T>>,
{
    let mut parents = HashSet::new();
    entries
        .into_iter()
        .peekable()
        .batching(move |entries| loop {
            let entry = entries.next().map(|first| {
                entries
                    .peeking_take_while(|entry| first.position.group == entry.position.group)
                    .last()
                    .unwrap_or(first)
            });
            if let Some(entry) = entry {
                if let Some(parent) = entry.parent {
                    if !parents.contains(&parent) {
                        continue;
                    }
                }
                parents.insert(entry.position);
                return Some(entry);
            }
            return None;
        })
        .fuse()
}

#[cfg(test)]
mod tests {
    use crate::token::{self, TokenKind, TokenTree};

    #[test]
    fn literal_case_insensitivity() {
        let tokenized = token::parse("(?-i)../foo/(?i)**/bar/**(?-i)/baz/*(?i)qux").unwrap();
        let literals: Vec<_> = tokenized
            .tokens()
            .iter()
            .filter_map(|token| match token.kind {
                TokenKind::Literal(ref literal) => Some(literal),
                _ => None,
            })
            .collect();

        assert!(!literals[0].is_case_insensitive); // `..`
        assert!(!literals[1].is_case_insensitive); // `foo`
        assert!(literals[2].is_case_insensitive); // `bar`
        assert!(!literals[3].is_case_insensitive); // `baz`
        assert!(literals[4].is_case_insensitive); // `qux`
    }

    // TODO:
    #[test]
    fn sanity() {
        let tokenized = token::parse("{a,..}").unwrap();
        //let tokenized = token::parse("/root/**/file.ext").unwrap();
        //for entry in token::exclusive_ending_subtree(tokenized.walk().components()) {
        for entry in tokenized.walk().components() {
            eprintln!(
                "{:#?}\n{:?} => {:?}\n",
                entry.item, entry.parent, entry.position
            );
            //if let Some(literal) = entry.literal() {
            //    eprintln!(
            //        "{}   :   {:?} => {:?}",
            //        literal.text(),
            //        entry.parent,
            //        entry.position
            //    );
            //}
            //else {
            //    eprintln!("%%    :   {:?} => {:?}", entry.parent, entry.position);
            //}
        }
    }
}
