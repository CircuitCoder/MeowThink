use std::iter::Peekable;

use crate::lexer::{Token, TokenInner};

use super::{ParseError, ParseResult, expr::{RawExpr, parse_expr}, parse_single, parse_str};

#[derive(Debug)]
pub struct RawCtor<'a> {
    pub name: &'a str,
    pub sig: RawExpr<'a>,
}

pub fn parse_ctors<'a, I: Iterator<Item = Token<'a>>>(tokens: &mut Peekable<I>) -> ParseResult<'a, Vec<RawCtor<'a>>> {
    parse_single(tokens, TokenInner::BracketLeft)?;
    let mut result = Vec::new();
    loop {
        match tokens.peek() {
            None => return Err(ParseError::EOF),
            Some(t) => {
                if t.inner == TokenInner::BracketRight {
                    tokens.next();
                    break;
                }
            },
        }
        let cur = parse_ctor(tokens)?;
        result.push(cur);
    }

    Ok(result)
}

pub fn parse_ctor<'a, I: Iterator<Item = Token<'a>>>(tokens: &mut Peekable<I>) -> ParseResult<'a, RawCtor<'a>> {
    let name = parse_str(tokens)?;
    parse_single(tokens, TokenInner::Symb(":"))?;
    let sig = parse_expr(tokens, -30)?;
    parse_single(tokens, TokenInner::SemiColon)?;
    Ok(RawCtor {
        name,
        sig,
    })
}