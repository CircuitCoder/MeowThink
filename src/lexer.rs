#[derive(Debug, PartialEq, Eq)]
pub enum TokenInner<'a> {
    /// Paren
    ParenLeft, ParenRight,

    /// Bracket
    BracketLeft, BracketRight,

    /// Semi-colon
    SemiColon,

    // Comma
    Comma,

    /// !alphabetical
    Macro(&'a str),

    // TODO: comments

    Keyword(Keyword),

    /// Any other alphanumerical word
    Word(&'a str),

    /// Any other symbol combination
    Symb(&'a str),
}

#[derive(Debug, PartialEq, Eq)]
pub enum Keyword {
    Let,
    Ind,
    Partial,
    Type,
    Match,
    SelfType,
}

impl Keyword {
    pub fn from_str(s: &str) -> Option<Keyword> {
        match s {
            "ind" => Some(Self::Ind),
            "partial" => Some(Self::Partial),
            "let" => Some(Self::Let),
            "type" => Some(Self::Type),
            "match" => Some(Self::Match),
            "self" => Some(Self::SelfType),
            _ => None,
        }
    }
}

#[derive(Debug)]
pub struct SrcRange {
    pub from: (usize, usize),
    pub to: (usize, usize),
}

#[derive(Debug)]
pub struct Token<'a> {
    pub inner: TokenInner<'a>,
    pub loc: SrcRange,
}

pub fn map_builtin<'a>(c: char) -> Option<TokenInner<'a>> {
    match c {
        '{' => Some(TokenInner::BracketLeft),
        '}' => Some(TokenInner::BracketRight),
        '(' => Some(TokenInner::ParenLeft),
        ')' => Some(TokenInner::ParenRight),
        ';' => Some(TokenInner::SemiColon),
        ',' => Some(TokenInner::Comma),
        _ => None,
    }
}

pub fn tokenize<'a>(mut input: &'a str) -> impl Iterator<Item = Token<'a>> {
    let mut current_line = 0;
    let mut current_pos = 0;
    // TODO: handles Unicode
    std::iter::from_fn(move || -> Option<Token<'a>> {
        while let Some(first) = input.chars().next() {
            if !first.is_whitespace() {
                break;
            }

            if first == '\n' {
                current_pos = 0;
                current_line += 1;
            } else {
                current_pos += 1; // TODO: width?
            }
            input = &input[first.len_utf8()..];
        }

        if input.len() == 0 {
            return None;
        }

        let first_char = input.chars().nth(0).unwrap();
        if let Some(inner) = map_builtin(first_char) {
            let loc = SrcRange {
                from: (current_line, current_pos),
                to: (current_line, current_pos),
            };

            current_pos += 1;
            input = &input[1..];
            return Some(Token {
                inner, loc
            });
        }

        let mut token_len = first_char.len_utf8();
        let mut token_visible_len = 1;

        let is_punc  = first_char.is_ascii_punctuation() && first_char != '_';
        let is_macro = if first_char == '!' {
            let second = input.chars().nth(1);
            if let Some(inner) = second {
                if inner.is_alphanumeric() || inner == '_' {
                    true
                } else {
                    false
                }
            } else {
                false
            }
        } else {
            false
        };

        for c in input.chars().skip(1) {
            if c.is_whitespace() || (c.is_ascii_punctuation() && c != '_') != (is_punc && !is_macro) || map_builtin(c).is_some() {
                break;
            }

            token_len += c.len_utf8();
            token_visible_len += 1;
        }

        let content = &input[0..token_len];
        input = &input[token_len..];

        let inner = if is_macro {
            TokenInner::Macro(&content[1..])
        } else if let Some(kw) = Keyword::from_str(content) {
            TokenInner::Keyword(kw)
        } else if is_punc {
            TokenInner::Symb(content)
        } else {
            TokenInner::Word(content)
        };

        let loc = SrcRange {
            from: (current_line, current_pos),
            to: (current_line, current_pos + token_visible_len - 1),
        };

        current_pos += token_visible_len;

        Some(Token {
            inner,
            loc,
        })
    })
}