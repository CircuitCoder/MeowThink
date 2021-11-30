use std::iter::Peekable;

use crate::lexer::{Token, TokenInner};

use super::{ParseError, ParseResult, ind::{RawCtor, parse_ctors}, parse_single, parse_str};

#[derive(Debug)]
pub enum RawExpr<'a> {
    // Type of type (sort-of?)
    IndType(Box<RawExpr<'a>>),
    PartialType(Box<RawExpr<'a>>),

    // Type
    Def {
        sig: Box<RawExpr<'a>>,
        ctors: Vec<RawCtor<'a>>,
    },
    Fn(RawFn<'a>),

    // Other "Non-types"
    Lambda {
        // Currently only with one argument
        arg: Box<RawName<'a>>,
        ret: Option<Box<RawExpr<'a>>>,
        body: Box<RawExpr<'a>>,

        rec: Option<&'a str>,
        partial: bool,
    },
    Binding {
        binding: Box<RawBinding<'a>>,
        rest: Box<RawExpr<'a>>,
    },
    Name(Box<RawName<'a>>),
    Ap(Box<(RawExpr<'a>, RawExpr<'a>)>),
    Macro(&'a str),
    Match {
        matched: Box<RawExpr<'a>>,
        arms: Vec<RawMatchArm<'a>>,
    }
}

#[derive(Debug)]
pub struct RawName<'a> {
    pub name: &'a str,
    pub sig: Option<RawExpr<'a>>,
}

#[derive(Debug)]
pub struct RawBinding<'a> {
    name: RawName<'a>,
    val: RawExpr<'a>,
}

#[derive(Debug)]
pub struct RawFn<'a> {
    input: Box<RawExpr<'a>>,
    output: Box<RawExpr<'a>>,
}

#[derive(Debug)]
pub struct RawMatchArm<'a> {
    ctor: &'a str,
    data: Vec<&'a str>,
    ev: Vec<RawName<'a>>,
    body: RawExpr<'a>,
}

fn binding_power_unary(op: &str) -> Option<isize> {
    match op {
        // ind 100
        "partial" => Some(90),
        // def 80
        // match 70
        _ => None,
    }
}

fn binding_power_bin(op: &str) -> Option<(isize, isize)> {
    match op {
        "/" => Some((-9, -10)),
        "->" => Some((-19, -20)),
        ":" => Some((-29, -30)),
        // "=>" -40
        "=" => Some((-50, -49)),
        _ => None,
    }
}

pub fn parse_expr<'a, I: Iterator<Item = Token<'a>>>(tokens: &mut Peekable<I>, power: isize) -> ParseResult<'a, RawExpr<'a>> {
    let first = tokens.next().ok_or(ParseError::SoftEOF)?;
    let mut lhs = match first.inner {
        TokenInner::SemiColon | TokenInner::ParenRight | TokenInner::BracketRight | TokenInner::BracketLeft | TokenInner::Comma => {
            return Err(ParseError::UnexpectedToken{ token: first });
        }
        TokenInner::Macro(m) => RawExpr::Macro(m),
        TokenInner::ParenLeft => {
            // Step after the paren
            let inner = parse_expr(tokens, isize::MIN)?;
            let next = tokens.next().ok_or(ParseError::EOF)?;
            if next.inner != TokenInner::ParenRight {
                return Err(ParseError::UnexpectedToken{ token: next });
            } else {
                inner
            }
        },
        TokenInner::Symb(op) | TokenInner::Word(op) => {
            if op == "let" {
                let binding = Box::new(parse_binding_tail(tokens)?);
                let rest = Box::new(parse_expr(tokens, power)?);
                RawExpr::Binding {
                    binding,
                    rest,
                }
            } else if op == "ind" {
                let inner = parse_expr(tokens, 100)?;
                RawExpr::IndType(Box::new(inner))
            } else if op == "partial" {
                let inner = parse_expr(tokens, 90)?;
                RawExpr::PartialType(Box::new(inner))
            } else if op == "def" {
                let sig = Box::new(parse_expr(tokens, 80)?);
                let ctors = parse_ctors(tokens)?;
                RawExpr::Def {
                    sig,
                    ctors,
                }
            } else if op == "\\" {
                parse_lambda_tail(tokens)?
            } else if op == "match" {
                let matched = Box::new(parse_expr(tokens, 70)?);
                let arms = parse_match_body(tokens)?;

                RawExpr::Match {
                    matched,
                    arms,
                }
            } else if let Some(bp) = binding_power_unary(op) {
                let inner = parse_expr(tokens, bp)?;
                inner
            } else {
                // Is a single word
                RawExpr::Name(Box::new(RawName {
                    name: op,
                    sig: None,
                }))
            }
        }
    };

    loop {
        let op = match tokens.peek() {
            None => break,
            Some(inner) => inner,
        };

        let mut is_binary = false;
        match op.inner {
            TokenInner::SemiColon | TokenInner::ParenRight | TokenInner::BracketRight | TokenInner::Comma | TokenInner::BracketLeft => {
                break;
            }
            TokenInner::Symb(op) | TokenInner::Word(op) => {
                if let Some((lbp, rbp)) = binding_power_bin(op) {
                    is_binary = true;
                    if lbp < power {
                        break;
                    }

                    let token = tokens.next().unwrap();
                    let rhs = parse_expr(tokens, rbp)?;

                    match op {
                        "->" => {
                            lhs = RawExpr::Fn(RawFn {
                                input: Box::new(lhs),
                                output: Box::new(rhs),
                            });
                        },
                        ":" => {
                            if let RawExpr::Name(ref mut name) = lhs {
                                if name.sig.is_some() {
                                    return Err(ParseError::UnexpectedToken{ token });
                                }

                                name.sig = Some(rhs);
                            } else {
                                return Err(ParseError::UnexpectedToken{ token });
                            }
                        },
                        _ => unreachable!(),
                    }
                }
            }
            _ => {}
        }

        if !is_binary {
            // Is function application
            if power >= 0 {
                break;
            }

            let rhs = parse_expr(tokens, 1)?;
            lhs = RawExpr::Ap(Box::new((lhs, rhs)));
        }
    }

    Ok(lhs)
}

pub fn parse_capture_group<'a, I: Iterator<Item = Token<'a>>>(tokens: &mut Peekable<I>) -> ParseResult<'a, RawName<'a>> {
    let contains_paren = match tokens.peek() {
        None => return Err(ParseError::EOF),
        Some(t) => match t.inner {
            TokenInner::ParenLeft => {
                tokens.next();
                true
            },
            TokenInner::Word(_) | TokenInner::Symb(_) => false,
            _ => return Err(ParseError::UnexpectedToken{ token: tokens.next().unwrap() }),
        }
    };

    // Parse name & sig
    let name = parse_str(tokens)?;
    let sig = if tokens.peek().map(|t| t.inner == TokenInner::Symb(":")) == Some(true) {
        tokens.next();
        Some(parse_expr(tokens, -30)?)
    } else {
        None
    };

    if contains_paren {
        parse_single(tokens, TokenInner::ParenRight)?;
    }

    Ok(RawName {
        name, sig
    })
}


pub fn parse_lambda_tail<'a, I: Iterator<Item = Token<'a>>>(tokens: &mut Peekable<I>) -> ParseResult<'a, RawExpr<'a>> {
    let arg = Box::new(parse_capture_group(tokens)?);
    // Parse result value
    let ret = if tokens.peek().map(|t| t.inner == TokenInner::Symb("->")) == Some(true) {
        tokens.next();
        Some(Box::new(parse_expr(tokens, -20)?))
    } else {
        None
    };

    let mut partial = false;
    let mut rec = None;
    while tokens.peek().map(|t| t.inner == TokenInner::Comma) == Some(true) {
        tokens.next();
        let mut attr = Vec::new();
        let mut first = None;

        loop {
            let peek = tokens.peek().map(|t| t.inner == TokenInner::Symb("=>") || t.inner == TokenInner::Symb(","));
            if peek == Some(true) || peek == None {
                break;
            }

            if first.is_none() {
                first = Some(tokens.next().unwrap());
            } else {
                attr.push(parse_str(tokens)?);
            }
        }

        let directive = match first {
            None => return Err(ParseError::EOF),
            Some(ref t) => match t.inner {
                TokenInner::Word(d) => d,
                _ => return Err(ParseError::UnexpectedToken{ token: first.unwrap() }),
            }
        };

        match directive {
            "partial" if attr.len() == 0 => {
                partial = true;
            },
            "rec" if attr.len() == 1 => {
                rec = Some(attr[0]);
            },
            _ => return Err(ParseError::MalformedAttr{ token: first.unwrap() })
        }
    }

    parse_single(tokens, TokenInner::Symb("=>"))?;
    let body = Box::new(parse_expr(tokens, -40)?);
    Ok(RawExpr::Lambda {
        arg,
        ret,
        body,

        rec,
        partial,
    })
}

pub fn parse_binding_tail<'a, I: Iterator<Item = Token<'a>>>(tokens: &mut Peekable<I>) -> ParseResult<'a, RawBinding<'a>> {
    let name = parse_str(tokens)?;
    let mut sig = None;
    if let Some(t) = tokens.next() {
        match t.inner {
            TokenInner::Symb(":") => {
                // Has signature
                sig = Some(parse_expr(tokens, -30)?);
                parse_single(tokens, TokenInner::Symb("="))?;
            }
            TokenInner::Symb("=") => {},
            _ => {
                return Err(ParseError::UnexpectedToken{ token: t });
            }
        }
    } else {
        return Err(ParseError::SoftEOF);
    }

    let val = parse_expr(tokens, -49)?;
    parse_single(tokens, TokenInner::SemiColon)?;

    Ok(RawBinding {
        name: RawName {
            name,
            sig,
        },
        val,
    })
}

pub fn parse_match_arm<'a, I: Iterator<Item = Token<'a>>>(tokens: &mut Peekable<I>) -> ParseResult<'a, RawMatchArm<'a>> {
    let ctor = parse_str(tokens)?;
    let mut data = Vec::new();
    let mut ev = Vec::new();
    loop {
        let peek = tokens.peek();
        match tokens.peek() {
            None => break,
            Some(token) => match token.inner {
                TokenInner::Symb("/") => break,
                TokenInner::Symb("=>") => break,
                _ => {}
            },
        }

        data.push(parse_str(tokens)?);
    }

    match tokens.next() {
        None => return Err(ParseError::EOF),
        Some(token) => match token.inner {
            TokenInner::Symb("/") => {
                // Parse evidences
                loop {
                    let peek = tokens.peek();
                    match tokens.peek() {
                        None => break,
                        Some(token) => match token.inner {
                            TokenInner::Symb("=>") => break,
                            _ => {}
                        },
                    }

                    ev.push(parse_capture_group(tokens)?);
                }
                parse_single(tokens, TokenInner::Symb("=>"))?;
            },
            TokenInner::Symb("=>") => {}
            _ => return Err(ParseError::UnexpectedToken{ token }),
        }
    }

    println!("Parsing match body with ctor {}", ctor);
    let body = parse_expr(tokens, -49)?;
    parse_single(tokens, TokenInner::SemiColon)?;
    Ok(RawMatchArm {
        ctor,
        data,
        ev,
        body,
    })
}

pub fn parse_match_body<'a, I: Iterator<Item = Token<'a>>>(tokens: &mut Peekable<I>) -> ParseResult<'a, Vec<RawMatchArm<'a>>> {
    parse_single(tokens, TokenInner::BracketLeft)?;

    let mut arms = Vec::new();

    // TODO: write a combinator: do_until
    loop {
        let peek = tokens.peek();
        match tokens.peek() {
            None => break,
            Some(token) => match token.inner {
                TokenInner::BracketRight => break,
                _ => {}
            },
        }

        arms.push(parse_match_arm(tokens)?);
    }
    parse_single(tokens, TokenInner::BracketRight)?;

    Ok(arms)
}