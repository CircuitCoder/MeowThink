pub mod expr;
pub mod ind;

use std::iter::Peekable;

use thiserror::Error;

use crate::{data::Expr, lexer::{Token, TokenInner}};

use self::expr::parse_expr;


#[derive(Error, Debug)]
pub enum ParseError<'a> {
    #[error("Unexpected token: {token:?}")]
    UnexpectedToken {
        token: Token<'a>
    },

    #[error("Malformed constructor: {token:?}")]
    MalformedCtr {
        token: Token<'a>,
    },

    #[error("Malformed attribute: {token:?}")]
    MalformedAttr {
        token: Token<'a>,
    },

    #[error("Malformed attribute: {token:?}")]
    MalformedUniverse {
        token: Token<'a>,
    },

    #[error("Absolute import cannot have ..")]
    AbsPathUp,

    #[error("Unexpected EOF")]
    EOF,

    #[error("Unexpected EOF")]
    SoftEOF,
}

pub type ParseResult<'a, T> = Result<T, ParseError<'a>>;

fn parse_single<'a, I: Iterator<Item = Token<'a>>>(tokens: &mut Peekable<I>, expected: TokenInner) -> ParseResult<'a, Token<'a>> {
    let token = tokens.next().ok_or(ParseError::SoftEOF)?;
    if token.inner != expected {
        return Err(ParseError::UnexpectedToken{ token });
    }

    Ok(token)
}

fn parse_str<'a, I: Iterator<Item = Token<'a>>>(tokens: &mut Peekable<I>) -> ParseResult<'a, &'a str> {
    let token = tokens.next().ok_or(ParseError::SoftEOF)?;
    match token.inner {
        TokenInner::Symb(s) | TokenInner::Word(s) => Ok(s),
        _ => Err(ParseError::UnexpectedToken{ token }),
    }
}

fn parse_level<'a, I: Iterator<Item = Token<'a>>>(tokens: &mut Peekable<I>) -> ParseResult<'a, Option<usize>> {
    let token = tokens.next().ok_or(ParseError::SoftEOF)?;
    match token.inner {
        TokenInner::Symb("_") => Ok(None),
        TokenInner::Word(s) => s.parse::<usize>().map_err(|_| ParseError::MalformedUniverse{ token }).map(Some),
        _ => Err(ParseError::MalformedUniverse{ token }),
    }
}

pub fn parse<'a, I: Iterator<Item = Token<'a>>>(tokens: &mut Peekable<I>) -> ParseResult<'a, Expr<'a, ()>> {
    parse_expr(tokens, isize::MIN)
}