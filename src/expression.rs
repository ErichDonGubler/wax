use itertools::Itertools as _;
#[cfg(feature = "diagnostics-report")]
use miette::Diagnostic;
use std::borrow::Cow;
#[cfg(feature = "diagnostics-report")]
use std::fmt::Display;
use std::path::{Component, Path};
use thiserror::Error;

use crate::CandidatePath;

#[derive(Clone, Debug, Error)]
#[error("incompatible path")]
pub struct PathError;

#[cfg(feature = "diagnostics-report")]
#[cfg_attr(docsrs, doc(cfg(feature = "diagnostics-report")))]
impl Diagnostic for PathError {
    fn code<'a>(&'a self) -> Option<Box<dyn 'a + Display>> {
        Some(Box::new(String::from("wax::glob::incompatible_path")))
    }
}

pub trait ToExpression {
    type Error;

    fn to_expression(&self) -> Result<Cow<str>, Self::Error>;
}

impl ToExpression for Path {
    type Error = PathError;

    fn to_expression(&self) -> Result<Cow<str>, Self::Error> {
        let (components, has_root) = self
            .components()
            .map(|component| match component {
                Component::Normal(text) => Ok(Some(text)),
                Component::RootDir => Ok(None),
                _ => Err(PathError),
            })
            .fold_ok(
                (vec![], false),
                |(mut components, has_root), component| match component {
                    Some(text) => {
                        let path = CandidatePath::from(text);
                        components.push(path.text.into_owned());
                        (components, has_root)
                    },
                    None => (components, true),
                },
            )?;
        Ok(format!(
            "{}{}",
            if has_root { "/" } else { "" },
            components.join("/"),
        )
        .into())
    }
}

pub fn components(expression: &str) -> impl Iterator<Item = &str> {
    expression
        .char_indices()
        .peekable()
        .batching(|chars| chars.next().map(|left| (left, chars.peek().cloned())))
        .peekable()
        .batching(|pairs| {
            pairs.peek().is_some().then(|| {
                let mut alternatives = 0usize;
                let mut repetitions = 0usize;
                let mut component = pairs
                    .take_while(|((_, x), _)| {
                        alternatives = match x {
                            '{' => alternatives.saturating_add(1),
                            '}' => alternatives.saturating_sub(1),
                            _ => alternatives,
                        };
                        repetitions = match x {
                            '<' => repetitions.saturating_add(1),
                            '>' => repetitions.saturating_sub(1),
                            _ => repetitions,
                        };
                        *x != '/' || alternatives != 0 || repetitions != 0
                    })
                    .map(|((start, _), right)| (start, right.map(|(end, _)| end)));
                match (component.next(), component.last()) {
                    (Some((start, _)), Some((_, Some(end)))) | (Some((start, Some(end))), None) => {
                        Some(&expression[start..end])
                    },
                    (Some((start, _)), Some((_, None))) | (Some((start, None)), None) => {
                        Some(&expression[start..])
                    },
                    _ => None,
                }
            })
        })
        .flatten()
}

#[cfg(test)]
mod tests {
    use crate::expression;

    #[test]
    fn components_valid_expression() {
        assert_eq!(expression::components("").count(), 0);
        assert_eq!(expression::components("/").count(), 0);
        assert_eq!(
            expression::components("a/b").collect::<Vec<_>>(),
            vec!["a", "b"],
        );
        assert_eq!(
            expression::components("a/**/b").collect::<Vec<_>>(),
            vec!["a", "**", "b"],
        );
        assert_eq!(
            expression::components("a/<b/c:0,>").collect::<Vec<_>>(),
            vec!["a", "<b/c:0,>"],
        );
        assert_eq!(
            expression::components("a/{b,c/d}").collect::<Vec<_>>(),
            vec!["a", "{b,c/d}"],
        );
        assert_eq!(
            expression::components("a/{<b/c:1,0>,d}/e").collect::<Vec<_>>(),
            vec!["a", "{<b/c:1,0>,d}", "e"],
        );
        assert_eq!(
            expression::components("ä/b").collect::<Vec<_>>(),
            vec!["ä", "b"],
        );
        assert_eq!(
            expression::components("öü/äb").collect::<Vec<_>>(),
            vec!["öü", "äb"],
        );
        assert_eq!(
            expression::components("面白くて/楽しくて").collect::<Vec<_>>(),
            vec!["面白くて", "楽しくて"],
        );
    }

    #[test]
    fn components_invalid_expression() {
        assert_eq!(expression::components("//").count(), 0);
        assert_eq!(expression::components("///").count(), 0);
        // This test case is very sensitive to behavior that will likely remain
        // unspecified. Its main purpose is to test that separators and groups
        // are detected, even when they are otherwise incoherent.
        assert_eq!(
            expression::components("***//{a/b").collect::<Vec<_>>(),
            vec!["***", "{a/b"],
        );
    }
}
