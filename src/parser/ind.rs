use std::iter::Peekable;

use crate::{data::Ctor, lexer::{Token, TokenInner}};

use super::{ParseError, ParseResult, expr::parse_expr, parse_single, parse_str};

pub fn parse_ctors<'a, I: Iterator<Item = Token<'a>>>(tokens: &mut Peekable<I>) -> ParseResult<'a, Vec<Ctor<'a, ()>>> {
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

pub fn parse_ctor<'a, I: Iterator<Item = Token<'a>>>(tokens: &mut Peekable<I>) -> ParseResult<'a, Ctor<'a, ()>> {
    let name = parse_str(tokens)?;
    parse_single(tokens, TokenInner::Symb(":"))?;
    let sig = parse_expr(tokens, -30)?;
    parse_single(tokens, TokenInner::SemiColon)?;
    Ok(Ctor {
        name,
        sig,
    })
}