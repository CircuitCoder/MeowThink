use std::iter::Peekable;

use crate::{data::*, lexer::{Token, TokenInner, Keyword}};

use super::{ParseError, ParseResult, ind::parse_ctors, parse_single, parse_str, parse_level};

fn binding_power_bin(op: &str) -> Option<(isize, isize)> {
    match op {
        // # => 100
        // . => 10
        "^" => Some((-9, -10)),
        "/" => Some((-9, -10)),
        "==" => Some((-19, -20)),
        "->" => Some((-24, -25)),
        ":" => Some((-29, -30)),
        // "=>" -40
        "=" => Some((-50, -49)),
        _ => None,
    }
}

pub fn parse_expr<'a, I: Iterator<Item = Token<'a>>>(tokens: &mut Peekable<I>, power: isize) -> ParseResult<'a, Expr<'a, ()>> {
    let first = tokens.next().ok_or(ParseError::SoftEOF)?;
    let mut lhs = match first.inner {
        TokenInner::SemiColon | TokenInner::ParenRight | TokenInner::BracketRight | TokenInner::Comma => {
            return Err(ParseError::UnexpectedToken{ token: first });
        }
        TokenInner::ParenLeft => {
            // Step after the paren
            let inner = parse_expr(tokens, isize::MIN)?;
            parse_single(tokens, TokenInner::ParenRight)?;
            inner
        },
        TokenInner::BracketLeft => {
            let inner = ExprInner::Struct(parse_struct_body(tokens)?).with(());
            parse_single(tokens, TokenInner::BracketRight)?;
            inner
        },

        TokenInner::Keyword(kw) => match kw {
            // TODO: check for binding power for keywords, and update binding power
            Keyword::Let => {
                let binding = Box::new(parse_binding_tail(tokens)?);
                let rest = Box::new(parse_expr(tokens, power)?);
                ExprInner::Binding {
                    binding,
                    rest,
                }.with(())
            },
            Keyword::Struct => {
                parse_single(tokens, TokenInner::BracketLeft)?;
                let inner = ExprInner::StructTy(parse_struct_type_body(tokens)?).with(());
                parse_single(tokens, TokenInner::BracketRight)?;
                inner
            },
            Keyword::Partial => {
                let inner = parse_expr(tokens, 90)?;
                ExprInner::PartialType(Box::new(inner)).with(())
            },
            Keyword::Ind => {
                let peek = tokens.peek();
                let sig = if peek.is_none() || peek.unwrap().inner != TokenInner::BracketLeft {
                    Some(Box::new(parse_expr(tokens, 80)?))
                } else {
                    None
                };
                let ctors = parse_ctors(tokens)?;
                ExprInner::Ind {
                    sig,
                    ctors,
                }.with(())
            },
            Keyword::Match => {
                let matched = Box::new(parse_expr(tokens, 70)?);
                let arms = parse_match_body(tokens)?;

                ExprInner::Match {
                    matched,
                    arms,
                }.with(())
            },
            Keyword::Type => {
                let level = parse_level(tokens)?;
                ExprInner::Universe { level }.with(())
            },
            Keyword::SelfType => ExprInner::SelfInvoc.with(()),
            Keyword::Refl => ExprInner::ReflInvoc.with(()),
            Keyword::Import => ExprInner::Import(parse_import_tail(tokens)?).with(()),
        },
        TokenInner::Symb(op) | TokenInner::Word(op) => {
            if op == "\\" {
                parse_lambda_tail(tokens)?
            } else {
                // Is a single word
                ExprInner::Name(Box::new(Name {
                    name: op,
                    sig: None,
                })).with(())
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
                if op == "#" {
                    tokens.next().unwrap();
                    is_binary = true;
                    lhs = ExprInner::CtorOf {
                        parent: Box::new(lhs),
                        variant: parse_str(tokens)?,
                    }.with(());
                } else if op == "." {
                    tokens.next().unwrap();
                    is_binary = true;
                    lhs = ExprInner::Field {
                        parent: Box::new(lhs),
                        field: parse_str(tokens)?,
                    }.with(());
                } else if op == "=>" {
                    break;
                } else if let Some((lbp, rbp)) = binding_power_bin(op) {
                    is_binary = true;
                    if lbp < power {
                        break;
                    }

                    let token = tokens.next().unwrap();
                    let rhs = parse_expr(tokens, rbp)?;

                    match op {
                        "->" => {
                            lhs = ExprInner::Fun(Fun {
                                input: Box::new(lhs),
                                output: Box::new(rhs),
                            }).with(());
                        },
                        ":" => {
                            // TODO: let's do this more sophicately
                            if let ExprInner::Name(ref mut name) = lhs.inner {
                                if name.sig.is_some() {
                                    return Err(ParseError::UnexpectedToken{ token });
                                }

                                name.sig = Some(rhs);
                            } else {
                                return Err(ParseError::UnexpectedToken{ token });
                            }
                        },
                        "==" => {
                            lhs = ExprInner::Eq {
                                lhs: Box::new(lhs),
                                rhs: Box::new(rhs),
                            }.with(());
                        },
                        "/" => {
                            lhs = ExprInner::Cast{
                                orig: Box::new(lhs),
                                eq: Box::new(rhs),
                            }.with(());
                        },
                        "^" => {
                            lhs = ExprInner::EqAp {
                                eq: Box::new(lhs),
                                fun: Box::new(rhs),
                            }.with(());
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
            lhs = ExprInner::Ap(Box::new((lhs, rhs))).with(());
        }
    }

    Ok(lhs)
}

pub fn parse_capture_group<'a, I: Iterator<Item = Token<'a>>>(tokens: &mut Peekable<I>) -> ParseResult<'a, Name<'a, ()>> {
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

    Ok(Name {
        name, sig
    })
}


pub fn parse_lambda_tail<'a, I: Iterator<Item = Token<'a>>>(tokens: &mut Peekable<I>) -> ParseResult<'a, Expr<'a, ()>> {
    let arg = Box::new(parse_capture_group(tokens)?);
    // Parse result value
    let ret = if tokens.peek().map(|t| t.inner == TokenInner::Symb("->")) == Some(true) {
        tokens.next();
        Some(Box::new(parse_expr(tokens, -20)?))
    } else {
        None
    };

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
            "rec" if attr.len() == 1 => {
                rec = Some(attr[0]);
            },
            _ => return Err(ParseError::MalformedAttr{ token: first.unwrap() })
        }
    }

    parse_single(tokens, TokenInner::Symb("=>"))?;
    let body = Box::new(parse_expr(tokens, -40)?);
    Ok(ExprInner::Lambda {
        arg,
        ret,
        body,

        rec,
    }.with(()))
}

pub fn parse_binding_tail<'a, I: Iterator<Item = Token<'a>>>(tokens: &mut Peekable<I>) -> ParseResult<'a, Binding<'a, ()>> {
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

    Ok(Binding {
        name: Name {
            name,
            sig,
        },
        val,
    })
}

pub fn parse_match_arm<'a, I: Iterator<Item = Token<'a>>>(tokens: &mut Peekable<I>) -> ParseResult<'a, MatchArm<'a, ()>> {
    let ctor = parse_str(tokens)?;
    let mut data = Vec::new();
    let mut ev = Vec::new();
    let mut sig = None;

    loop {
        match tokens.peek() {
            None => break,
            Some(token) => match token.inner {
                TokenInner::Symb("/") => break,
                TokenInner::Symb("=>") => break,
                TokenInner::Symb("->") => break,
                _ => {}
            },
        }

        data.push(parse_str(tokens)?);
    }

    loop {
        match tokens.next() {
            None => return Err(ParseError::EOF),
            Some(token) => match token.inner {
                TokenInner::Symb("/") => {
                    // Parse evidences
                    loop {
                        match tokens.peek() {
                            None => break,
                            Some(token) => match token.inner {
                                TokenInner::Symb("=>") => break,
                                TokenInner::Symb("->") => break,
                                _ => {}
                            },
                        }

                        ev.push(parse_capture_group(tokens)?);
                    }
                },
                TokenInner::Symb("->") => {
                    sig = Some(parse_expr(tokens, 41)?);
                },
                TokenInner::Symb("=>") => break,
                _ => return Err(ParseError::UnexpectedToken{ token }),
            }
        }
    }

    let body = parse_expr(tokens, -49)?;
    parse_single(tokens, TokenInner::SemiColon)?;
    Ok(MatchArm {
        ctor,
        data,
        ev,
        sig,
        body,
    })
}

pub fn parse_match_body<'a, I: Iterator<Item = Token<'a>>>(tokens: &mut Peekable<I>) -> ParseResult<'a, Vec<MatchArm<'a, ()>>> {
    parse_single(tokens, TokenInner::BracketLeft)?;

    let mut arms = Vec::new();

    // TODO: write a combinator: do_until
    loop {
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

pub fn parse_struct_body<'a, I: Iterator<Item = Token<'a>>>(tokens: &mut Peekable<I>) -> ParseResult<'a, Vec<Binding<'a, ()>>> {
    let mut fields = Vec::new();

    loop {
        if let Some(&TokenInner::BracketRight) = tokens.peek().map(|t| &t.inner) {
            break;
        }
        fields.push(parse_binding_tail(tokens)?);
    }

    Ok(fields)
}

pub fn parse_struct_type_body<'a, I: Iterator<Item = Token<'a>>>(tokens: &mut Peekable<I>) -> ParseResult<'a, Vec<Name<'a, ()>>> {
    let mut fields = Vec::new();

    loop {
        if let Some(&TokenInner::BracketRight) = tokens.peek().map(|t| &t.inner) {
            break;
        }

        let name = parse_str(tokens)?;
        let mut sig = None;
        if let Some(t) = tokens.next() {
            match t.inner {
                TokenInner::Symb(":") => {
                    // Has signature
                    sig = Some(parse_expr(tokens, -30)?);
                    parse_single(tokens, TokenInner::SemiColon)?;
                }
                TokenInner::SemiColon => {},
                _ => {
                    return Err(ParseError::UnexpectedToken{ token: t });
                }
            }
        } else {
            return Err(ParseError::SoftEOF);
        }
        fields.push(Name { name, sig });
    }

    Ok(fields)
}

pub fn parse_import_tail<'a, I: Iterator<Item = Token<'a>>>(tokens: &mut Peekable<I>) -> ParseResult<'a, Path<'a>> {
    let mut segs = Vec::new();
    loop {
        let cur = match tokens.peek() {
            Some(t) => if let TokenInner::Word(w) = t.inner {
                tokens.next();
                Some(w)
            } else {
                None
            },
            _ => None,
        };

        let at_end = match tokens.peek() {
            Some(t) => match t.inner {
                TokenInner::Symb(".") => {
                    tokens.next();
                    false
                },
                _ => true,
            },
            _ => true,
        };
        if at_end && !cur.is_some() {
            if let Some(token) = tokens.next() {
                return Err(ParseError::UnexpectedToken { token })
            } else {
                return Err(ParseError::EOF)
            }
        }

        segs.push(cur);
        if at_end {
            break;
        }
    }

    let is_abs = segs.first().unwrap().is_some();
    let iter = segs.iter();
    if is_abs {
        let segs: Result<Vec<_>, _> = segs.into_iter().map(|s| s.ok_or(ParseError::AbsPathUp)).collect();
        let segs = segs?;
        Ok(Path::Absolute(segs))
    } else {
        let segs = segs.into_iter().skip(1).map(|s| match s {
            Some(s) => RelPathSeg::Down(s),
            None => RelPathSeg::Up,
        }).collect();
        Ok(Path::Relative(segs))
    }
}