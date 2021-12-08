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
    Match {
        matched: Box<Expr<'a, T>>,
        arms: Vec<MatchArm<'a, T>>,
    },
    CtorOf {
        parent: Box<Expr<'a, T>>,
        variant: &'a str,
    },
    SelfInvoc,
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