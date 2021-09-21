//! Rules and limitations for token sequences.
//!
//! This module provides the `check` function, which examines a token sequence
//! and emits an error if the sequence violates rules. Rules are invariants that
//! are difficult or impossible to enforce when parsing text and primarily
//! detect and reject token sequences that produce anomalous, meaningless, or
//! unexpected globs (regular expressions) when compiled.
//!
//! Most rules concern alternatives, which have complex interactions with
//! neighboring tokens.

use itertools::Itertools as _;
#[cfg(feature = "diagnostics")]
use miette::{Diagnostic, SourceSpan};
use std::borrow::Cow;
use thiserror::Error;

use crate::token::{Annotation, Token};
#[cfg(feature = "diagnostics")]
use crate::SourceSpanExt as _;
use crate::{IteratorExt as _, SliceExt as _, Terminals};

#[derive(Debug, Error)]
#[error("invalid glob: {kind}")]
#[cfg_attr(feature = "diagnostics", derive(Diagnostic))]
#[cfg_attr(feature = "diagnostics", diagnostic(code = "glob::rule"))]
pub struct RuleError<'t> {
    expression: Cow<'t, str>,
    kind: ErrorKind,
    #[cfg(feature = "diagnostics")]
    #[snippet(expression, message("in this expression"))]
    snippet: SourceSpan,
    #[cfg(feature = "diagnostics")]
    #[highlight(snippet, label("here"))]
    error: SourceSpan,
}

impl<'t> RuleError<'t> {
    #[cfg(feature = "diagnostics")]
    fn new(expression: &'t str, kind: ErrorKind, span: SourceSpan) -> Self {
        RuleError {
            expression: expression.into(),
            kind,
            snippet: (0, expression.len()).into(),
            error: span,
        }
    }

    #[cfg(not(feature = "diagnostics"))]
    fn new(expression: &'t str, kind: ErrorKind) -> Self {
        RuleError {
            expression: expression.into(),
            kind,
        }
    }

    pub fn into_owned(self) -> RuleError<'static> {
        let RuleError {
            expression,
            kind,
            #[cfg(feature = "diagnostics")]
            snippet,
            #[cfg(feature = "diagnostics")]
            error,
        } = self;
        RuleError {
            expression: expression.into_owned().into(),
            kind,
            #[cfg(feature = "diagnostics")]
            snippet,
            #[cfg(feature = "diagnostics")]
            error,
        }
    }
}

// TODO: This probably shouldn't implement `Error`.
#[derive(Clone, Copy, Debug, Error, Eq, Hash, PartialEq)]
#[non_exhaustive]
enum ErrorKind {
    #[error("rooted sub-glob or adjacent component boundaries `/` or `**` in alternative")]
    AlternativeBoundary,
    #[error("adjacent zero-or-more wildcards `*` or `$` in alternative")]
    AlternativeZeroOrMore,
    #[error("adjacent component boundaries `/` or `**`")]
    BoundaryAdjacent,
}

pub fn check<'t, 'i, I>(expression: &'t str, tokens: I) -> Result<(), RuleError<'t>>
where
    I: IntoIterator<Item = &'i Token<'t, Annotation>>,
    I::IntoIter: Clone,
    't: 'i,
{
    let tokens = tokens.into_iter();
    alternative(expression, tokens.clone())?;
    boundary(expression, tokens)?;
    Ok(())
}

fn alternative<'t, 'i, I>(expression: &'t str, tokens: I) -> Result<(), RuleError<'t>>
where
    I: IntoIterator<Item = &'i Token<'t, Annotation>>,
    't: 'i,
{
    use crate::token::TokenKind::{Alternative, Separator, Wildcard};
    use crate::token::Wildcard::{Tree, ZeroOrMore};
    use crate::Terminals::{Only, StartEnd};

    struct CheckError {
        kind: ErrorKind,
        #[cfg(feature = "diagnostics")]
        span: Option<SourceSpan>,
    }

    impl From<ErrorKind> for CheckError {
        fn from(kind: ErrorKind) -> CheckError {
            CheckError {
                kind,
                #[cfg(feature = "diagnostics")]
                span: None,
            }
        }
    }

    #[derive(Clone, Copy, Default)]
    struct Outer<'t, 'i> {
        left: Option<&'i Token<'t, Annotation>>,
        right: Option<&'i Token<'t, Annotation>>,
    }

    fn is_component_boundary<'t>(adjacent: Option<&'t Token<'t, Annotation>>) -> bool {
        adjacent
            .map(|token| token.is_component_boundary())
            .unwrap_or(false)
    }

    fn is_component_boundary_or_terminal<'t>(adjacent: Option<&'t Token<'t, Annotation>>) -> bool {
        adjacent
            .map(|token| token.is_component_boundary())
            .unwrap_or(true)
    }

    fn recurse<'t, 'i, I>(
        expression: &'t str,
        tokens: I,
        outer: Outer<'t, 'i>,
    ) -> Result<(), RuleError<'t>>
    where
        I: IntoIterator<Item = &'i Token<'t, Annotation>>,
        't: 'i,
    {
        #[cfg_attr(not(feature = "diagnostics"), allow(unused))]
        for (token, alternative, left, right) in
            tokens.into_iter().adjacent().filter_map(|adjacency| {
                let (left, token, right) = adjacency.into_tuple();
                match token.kind() {
                    Alternative(alternative) => Some((token, alternative, left, right)),
                    _ => None,
                }
            })
        {
            let outer = Outer {
                left: left.or(outer.left),
                right: right.or(outer.right),
            };
            for tokens in alternative.branches() {
                if let Some(terminals) = tokens.terminals() {
                    // Check branch terminals against the tokens adjacent to
                    // their corresponding alternative token.
                    check(terminals, outer).map_err(
                        |CheckError {
                             kind,
                             #[cfg(feature = "diagnostics")]
                             span,
                         }| {
                            RuleError::new(
                                expression,
                                kind,
                                // TODO: Reverse this relationship. `check`
                                //       should compose the final span, which
                                //       may be smaller than the span of the
                                //       alternative token.
                                #[cfg(feature = "diagnostics")]
                                if let Some(span) = span {
                                    span.union(token.annotation())
                                } else {
                                    token.annotation().clone()
                                },
                            )
                        },
                    )?;
                }
                recurse(expression, tokens.iter(), outer)?;
            }
        }
        Ok(())
    }

    fn check<'t, 'i>(
        terminals: Terminals<&'i Token<'t, Annotation>>,
        outer: Outer<'t, 'i>,
    ) -> Result<(), CheckError> {
        let Outer { left, right } = outer;
        match terminals.map(Token::kind) {
            Only(Separator) if is_component_boundary_or_terminal(left) => {
                // The alternative is preceded by component boundaries or
                // terminations; disallow singular separators and rooted
                // sub-globs.
                //
                // For example, `foo/{bar,/}` or `{/,foo}`.
                Err(CheckError {
                    kind: ErrorKind::AlternativeBoundary,
                    #[cfg(feature = "diagnostics")]
                    span: left.map(|left| left.annotation().clone()),
                })
            }
            Only(Separator) if is_component_boundary(right) => {
                // The alternative is followed by component boundaries; disallow
                // singular separators and rooted sub-globs.
                //
                // For example, `foo/{bar,/}` or `{/,foo}`.
                Err(CheckError {
                    kind: ErrorKind::AlternativeBoundary,
                    #[cfg(feature = "diagnostics")]
                    span: right.map(|right| right.annotation().clone()),
                })
            }
            StartEnd(Separator, _) if is_component_boundary_or_terminal(left) => {
                // The alternative is preceded by component boundaries or
                // terminations; disallow leading separators and rooted
                // sub-globs.
                //
                // For example, `foo/{bar,/baz}` or `{bar,/baz}`.
                Err(CheckError {
                    kind: ErrorKind::AlternativeBoundary,
                    #[cfg(feature = "diagnostics")]
                    span: left.map(|left| left.annotation().clone()),
                })
            }
            StartEnd(_, Separator) if is_component_boundary(right) => {
                // The alternative is followed by component boundaries; disallow
                // trailing separators.
                //
                // For example, `{foo,bar/}/baz`.
                Err(CheckError {
                    kind: ErrorKind::AlternativeBoundary,
                    #[cfg(feature = "diagnostics")]
                    span: right.map(|right| right.annotation().clone()),
                })
            }
            Only(Wildcard(Tree { .. })) => {
                // NOTE: Supporting singular tree tokens is possible, but
                //       presents subtle edge cases that may be misleading or
                //       confusing. Rather than optimize or otherwise allow
                //       singular tree tokens, they are forbidden for
                //       simplicity.
                // Disallow singular tree tokens.
                //
                // For example, `{foo,bar,**}`.
                Err(ErrorKind::AlternativeBoundary.into())
            }
            StartEnd(Wildcard(Tree { is_rooted: true }), _) if left.is_none() => {
                // NOTE: `is_rooted` is not considered when the alternative is
                //       prefixed.
                // Disallow rooted sub-globs.
                //
                // For example, `{/**/foo,bar}`.
                Err(ErrorKind::AlternativeBoundary.into())
            }
            StartEnd(Wildcard(Tree { .. }), _) if is_component_boundary(left) => {
                // The alternative is preceded by component boundaries; disallow
                // leading tree tokens.
                //
                // For example, `foo/{bar,**/baz}`.
                Err(CheckError {
                    kind: ErrorKind::AlternativeBoundary,
                    #[cfg(feature = "diagnostics")]
                    span: left.map(|left| left.annotation().clone()),
                })
            }
            StartEnd(_, Wildcard(Tree { .. })) if is_component_boundary(right) => {
                // The alternative is followed by component boundaries; disallow
                // trailing tree tokens.
                //
                // For example, `{foo,bar/**}/baz`.
                Err(CheckError {
                    kind: ErrorKind::AlternativeBoundary,
                    #[cfg(feature = "diagnostics")]
                    span: right.map(|right| right.annotation().clone()),
                })
            }
            Only(Wildcard(ZeroOrMore(_)))
                if matches!(
                    (left.map(Token::kind), right.map(Token::kind)),
                    (Some(Wildcard(ZeroOrMore(_))), _) | (_, Some(Wildcard(ZeroOrMore(_))))
                ) =>
            {
                // The alternative is adjacent to a zero-or-more token; disallow
                // singular zero-or-more tokens.
                //
                // For example, `foo*{bar,*,baz}`.
                Err(ErrorKind::AlternativeZeroOrMore.into())
            }
            StartEnd(Wildcard(ZeroOrMore(_)), _)
                if matches!(left.map(Token::kind), Some(Wildcard(ZeroOrMore(_)))) =>
            {
                // The alternative is prefixed by a zero-or-more token; disallow
                // leading zero-or-more tokens.
                //
                // For example, `foo*{bar,*baz}`.
                Err(CheckError {
                    kind: ErrorKind::AlternativeZeroOrMore,
                    #[cfg(feature = "diagnostics")]
                    span: left.map(|left| left.annotation().clone()),
                })
            }
            StartEnd(_, Wildcard(ZeroOrMore(_)))
                if matches!(right.map(Token::kind), Some(Wildcard(ZeroOrMore(_)))) =>
            {
                // The alternative is postfixed by a zero-or-more token;
                // disallow trailing zero-or-more tokens.
                //
                // For example, `{foo,bar*}*baz`.
                Err(CheckError {
                    kind: ErrorKind::AlternativeZeroOrMore,
                    #[cfg(feature = "diagnostics")]
                    span: right.map(|right| right.annotation().clone()),
                })
            }
            _ => Ok(()),
        }
    }

    recurse(expression, tokens, Default::default())
}

fn boundary<'t, 'i, I>(expression: &'t str, tokens: I) -> Result<(), RuleError<'t>>
where
    I: IntoIterator<Item = &'i Token<'t, Annotation>>,
    't: 'i,
{
    #[cfg_attr(not(feature = "diagnostics"), allow(unused))]
    if let Some((left, right)) = tokens
        .into_iter()
        .tuple_windows::<(_, _)>()
        .find(|(left, right)| left.is_component_boundary() && right.is_component_boundary())
        .map(|(left, right)| (left.annotation(), right.annotation()))
    {
        Err(RuleError::new(
            expression,
            ErrorKind::BoundaryAdjacent,
            #[cfg(feature = "diagnostics")]
            left.union(right),
        ))
    } else {
        Ok(())
    }
}
