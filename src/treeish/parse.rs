use nom::error::{VerboseError as NomError, VerboseErrorKind as NomErrorKind};

use crate::token::{self, ParseError as GlobParseError};
use crate::treeish::Treeish;

type Input<'i> = &'i str;
type ErrorStack<'i> = NomError<Input<'i>>;
type ErrorMode<'i> = nom::Err<ErrorStack<'i>>;

pub struct ParseError<'t> {
    kind: ParseErrorKind<'t>,
}

enum ParseErrorKind<'t> {
    Glob(GlobParseError<'t>),
    Treeish,
}

pub fn parse(expression: &str) -> Result<Treeish, ParseError> {
    use nom::bytes::complete as bytes;
    use nom::character::complete as character;
    use nom::error;
    use nom::{branch, combinator, multi, sequence, IResult, Parser};

    type ParseResult<'i, O> = IResult<Input<'i>, O, ErrorStack<'i>>;

    todo!()
}
