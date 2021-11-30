pub mod expr;
pub mod ind;

use std::iter::Peekable;

use thiserror::Error;

use crate::lexer::{Token, TokenInner};

use self::expr::{RawExpr, parse_expr};


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

pub fn parse<'a, I: Iterator<Item = Token<'a>>>(tokens: &mut Peekable<I>) -> ParseResult<'a, RawExpr<'a>> {
    parse_expr(tokens, isize::MIN)
}