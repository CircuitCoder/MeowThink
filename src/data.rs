use std::fmt::Display;

#[derive(Debug)]
pub struct Expr<'a, T> {
    pub inner: ExprInner<'a, T>,
    pub data: T,
}

#[derive(Debug)]
pub enum ExprInner<'a, T> {
    // Type of types
    PartialType(Box<Expr<'a, T>>),
    Universe {
        level: Option<usize>,
    },

    // Type
    Ind {
        sig: Option<Box<Expr<'a, T>>>,
        ctors: Vec<Ctor<'a, T>>,
    },
    Fun(Fun<'a, T>),
    StructTy(Vec<Name<'a, T>>),

    // Other "Non-types"
    Lambda {
        // Currently only with one argument
        arg: Box<Name<'a, T>>,
        ret: Option<Box<Expr<'a, T>>>,
        body: Box<Expr<'a, T>>,

        rec: Option<&'a str>,
    },
    Binding {
        binding: Box<Binding<'a, T>>,
        rest: Box<Expr<'a, T>>,
    },
    Name(Box<Name<'a, T>>),
    Ap(Box<(Expr<'a, T>, Expr<'a, T>)>),
    Eq {
        lhs: Box<Expr<'a, T>>,
        rhs: Box<Expr<'a, T>>,
    },
    Cast {
        orig: Box<Expr<'a, T>>,
        eq: Box<Expr<'a, T>>,
    },
    EqAp {
        eq: Box<Expr<'a, T>>,
        fun: Box<Expr<'a, T>>,
    },
    Match {
        matched: Box<Expr<'a, T>>,
        arms: Vec<MatchArm<'a, T>>,
    },
    CtorOf {
        parent: Box<Expr<'a, T>>,
        variant: &'a str,
    },
    SelfInvoc,
    ReflInvoc,
    Struct(Vec<Binding<'a, T>>),
    Field {
        parent: Box<Expr<'a, T>>,
        field: &'a str,
    },

    Import(Path<'a>),
}

impl<'a, T> ExprInner<'a, T> {
    pub fn with(self, data: T) -> Expr<'a, T> {
        Expr {
            inner: self,
            data,
        }
    }
}

#[derive(Debug)]
pub struct Name<'a, T> {
    pub name: &'a str,
    pub sig: Option<Expr<'a, T>>,
}

#[derive(Debug)]
pub struct Binding<'a, T> {
    pub name: Name<'a, T>,
    pub val: Expr<'a, T>,
}

#[derive(Debug)]
pub struct Fun<'a, T> {
    pub input: Box<Expr<'a, T>>,
    pub output: Box<Expr<'a, T>>,
}

#[derive(Debug)]
pub struct MatchArm<'a, T> {
    pub ctor: &'a str,
    pub data: Vec<&'a str>,
    pub ev: Vec<Name<'a, T>>,
    pub sig: Option<Expr<'a, T>>,
    pub body: Expr<'a, T>,
}

#[derive(Debug)]
pub struct Ctor<'a, T> {
    pub name: &'a str,
    pub sig: Expr<'a, T>,
}

#[derive(Debug)]
pub enum RelPathSeg<'a> {
    Up,
    Down(&'a str),
}

#[derive(Debug)]
pub enum Path<'a> {
    Absolute(Vec<&'a str>),
    Relative(Vec<RelPathSeg<'a>>),
}

impl<'a> Display for Path<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Path::Absolute(segs) => write!(f, "{}", segs.join("."))?,
            Path::Relative(segs) => for seg in segs{
                match seg {
                    RelPathSeg::Up => write!(f, ".")?,
                    RelPathSeg::Down(seg) => write!(f, ".{}", seg)?,
                }
            }
        }

        Ok(())
    }
}
