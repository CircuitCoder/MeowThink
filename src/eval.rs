use std::{rc::Rc, collections::HashMap, fmt::Display, marker::PhantomData, path::PathBuf};

use thiserror::Error;
use std::fmt::Debug;

use crate::{data::{Expr, ExprInner, Name}, exec::Runner};

#[derive(Debug, PartialEq, Eq)]
pub struct Ind {
    sig: Rc<Type>,
    // indexes: Vec<Rc<Type>>,
    variants: im::HashMap<String, Rc<Type>>,
}

impl Ind {
    pub fn substitute(&self, ident: ExtBindingIdent, with: &Value) -> Ind {
        log::debug!("Ind sub: {:?} [{}/{:?}]", self, ident, with);
        Ind {
            sig: self.sig.clone().substitute(ident, with),
            variants: self.variants.iter().map(|(name, orig)| (name.clone(), orig.clone().substitute(ident, with))).collect(),
        }
    }
}

#[derive(Debug, PartialEq, Clone, Eq)]
pub enum IndPtr {
    SelfInvoc,
    Complete(Rc<Ind>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Variant {
    captures: Vec<ExtBindingIdent>,
    value: Value,
    // TODO: allow different ret in match
    // ret: Type,
}

impl Variant {
    pub fn substitute(&self, ident: ExtBindingIdent, with: &Value) -> Variant {
        if self.captures.contains(&ident) {
            return self.clone();
        }

        Variant {
            captures: self.captures.clone(),
            value: self.value.substitute(ident, with),
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Value {
    Refl,
    TypedRefl(Rc<Type>),
    Equality(Rc<Type>),
    Type(Rc<Type>),
    Lambda {
        ident: ExtBindingIdent,
        recursor: ExtBindingIdent,
        body: Box<Evaluated>,
    },
    PartiallyIndexedInd {
        ind: IndPtr,
        // Maybe partially indexed
        indexes: im::Vector<Value>,
    },
    Inductive {
        ind: Rc<Ind>,
        ctor: String,
        // Maybe partially applied
        data: im::Vector<Value>,
    },
    Struct(im::HashMap<String, Value>),

    // Delayed evaluation
    Ap {
        fun: Box<Value>,
        arg: Box<Value>,
    },
    Match {
        matched: Box<Value>,
        variants: im::HashMap<String, Variant>,
    },
    Field {
        parent: Box<Value>,
        field: String,
    },
    Pending(ExtBindingIdent),
    Placeholder, // Hole in identity, hole in argument, etc
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub enum Type {
    Hole,
    Partial(Rc<Type>),

    Type {
        universe: Option<usize>,
    },
    Eq {
        within: Rc<Type>,
        lhs: Value,
        rhs: Value,
    },
    Fun {
        arg: Rc<Type>,
        ident: ExtBindingIdent,
        ret: Rc<Type>,
    },
    FullyIndexedInd {
        ind: IndPtr,
        indexes: im::Vector<Value>,
    },
    Struct(im::HashMap<String, Rc<Type>>),
    // Ap, Match, Pending
    Delayed(Value),
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Hole => write!(f, "_"),
            Type::Partial(t) => write!(f, "partial {}", t),
            Type::Type { universe } => write!(f, "type {}", universe.map(|i| i.to_string()).unwrap_or("_".to_owned())),
            Type::Eq { within, lhs, rhs } => write!(f, "<{} = {}>", lhs, rhs),
            Type::Fun { arg, ident, ret } => write!(f, "([{}]: {}) -> {}", ident, arg, ret),
            Type::FullyIndexedInd { ind, indexes } => {
                write!(f, "<indtype>")?;
                for index in indexes.iter() {
                    write!(f, " {}", index)?;
                }
                Ok(())
            },
            Type::Struct(fields) => {
                write!(f, "struct {{")?;
                let mut is_first = true;
                for (k, v) in fields {
                    if is_first {
                        write!(f, " ")?;
                    } else {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}: {}", k, v)?;
                    is_first = false;
                }
                if !is_first {
                    write!(f, " ")?;
                }
                write!(f, "}}")?;
                Ok(())
            }
            Type::Delayed(v) => write!(f, "<delayed, {}>", v),
        }
    }
}

impl From<Rc<Type>> for Value {
    fn from(v: Rc<Type>) -> Self {
        Value::Type(v)
    }
}

impl Value {
    pub fn substitute(&self, ident: ExtBindingIdent, with: &Value) -> Value {
        let ret = match self {
            Value::Pending(self_ident) => if *self_ident == ident {
                with.clone()
            } else {
                self.clone()
            }
            Value::Ap { fun, arg } => Value::Ap {
                fun: Box::new(fun.substitute(ident, with)),
                arg: Box::new(arg.substitute(ident, with)),
            },
            Value::Match { matched, variants } => Value::Match {
                matched: Box::new(matched.substitute(ident, with)),
                variants: variants.iter().map(|(ctor, variant)| (ctor.clone(), variant.substitute(ident, with))).collect(),
            },
            Value::Equality(t) => Value::Equality(t.clone().substitute(ident, with)),
            Value::Type(t) => Value::Type(t.clone().substitute(ident, with)),
            Value::Lambda { ident: arg, recursor, body } => {
                if *arg == ident || ident == *recursor {
                    // Overridden, skip
                    self.clone()
                } else {
                    Value::Lambda { ident: *arg, recursor: *recursor, body: Box::new(body.substitute(ident, with)) }
                }
            },
            Value::PartiallyIndexedInd { ind, indexes } => {
                let ind = match ind {
                    IndPtr::SelfInvoc => IndPtr::SelfInvoc,
                    IndPtr::Complete(i) => IndPtr::Complete(Rc::new(i.substitute(ident, with))),
                };
                Value::PartiallyIndexedInd {
                    ind,
                    indexes: indexes.iter().map(|e| e.substitute(ident, with)).collect(),
                }
            },
            Value::Inductive { ind, ctor, data } => {
                Value::Inductive {
                    ind: Rc::new(ind.substitute(ident, with)),
                    ctor: ctor.clone(),
                    data: data.iter().map(|d| d.substitute(ident, with)).collect()
                }
            },
            Value::Struct(fields) => {
                Value::Struct(
                    fields.iter().map(|(name, val)| (name.clone(), val.substitute(ident, with))).collect()
                )
            },
            Value::Field { parent, field } => {
                Value::Field { parent: Box::new(parent.substitute(ident, with)), field: field.clone() }
            },
            Value::Placeholder => Value::Placeholder,
            Value::Refl => Value::Refl,
            Value::TypedRefl(ty) => Value::TypedRefl(ty.clone().substitute(ident, with)),
        };

        ret.compact()
    }

    pub fn match_with(self, variants: im::HashMap<String, Variant>) -> Value {
        match self {
            Value::Inductive { ind, ctor, data } => {
                // TODO: sanity check ind = matched
                let variant = variants.get(&ctor).unwrap();
                assert_eq!(data.len(), variant.captures.len());
                let body = data.into_iter().zip(variant.captures.iter()).fold(variant.value.clone(), |acc, (val, ident)| acc.substitute(*ident, &val));
                body.progress()
            },
            // Halts progression in variants if match is not resolved
            _ => Value::Match {
                matched: Box::new(self),
                variants,
            },
        }
    }

    pub fn ap_with(self, arg: Value) -> Value {
        log::debug!("Ap: {:?} <- {:?}", self, arg);
        match self {
            Value::Lambda { ident, recursor, ref body } => {
                body.0.substitute(ident, &arg).substitute(recursor, &self).progress()
            }
            Value::PartiallyIndexedInd { ind, mut indexes } => {
                // TODO: sanity check: arity?
                indexes.push_back(arg);
                Value::PartiallyIndexedInd {
                    ind,
                    indexes,
                }.progress()
            },
            Value::Inductive { ind, ctor, mut data } => {
                // TODO: sanity check: arity?
                data.push_back(arg);
                Value::Inductive { ind, ctor, data }.progress()
            },
            Value::Refl => Value::TypedRefl(arg.try_unwrap_as_type::<()>().unwrap()),
            Value::TypedRefl(ty) => Value::Equality(Rc::new(Type::Eq {
                within: ty,
                lhs: arg.clone(),
                rhs: arg.clone(),
            })),
            _ => Value::Ap {
                fun: Box::new(self),
                arg: Box::new(arg.progress()),
            },
        }
    }

    pub fn field_with(self, field: String) -> Value {
        match self {
            Value::Struct(mut fields) => {
                fields.remove(&field).unwrap()
            },
            _ => Value::Field {
                parent: Box::new(self),
                field,
            },
        }
    }

    pub fn try_unwrap_as_type<PI>(self) -> EvalResult<Rc<Type>, PI> {
        match self {
            Value::Type(t) => Ok(t),
            Value::PartiallyIndexedInd{ ind, indexes } => {
                // FIXME: check arity
                Ok(Rc::new(Type::FullyIndexedInd { ind, indexes }))
            },
            Value::Placeholder => Ok(Rc::new(Type::Hole)),
            Value::Ap { .. } | Value::Match { .. } | Value::Pending(_) => Ok(Rc::new(Type::Delayed(self))),
            _ => panic!("Trying to unwrap as type: {:?}", self),
        }
    }

    pub fn progress(self) -> Value {
        match self {
            Value::Equality(ty) => Value::Equality(ty.progress()),
            Value::Type(ty) => Value::Type(ty.progress()),
            Value::Lambda { ident, recursor, mut body } => {
                body.0 = body.0.progress();
                Value::Lambda { ident, recursor, body }
            },
            Value::PartiallyIndexedInd { ind, indexes } => Value::PartiallyIndexedInd { ind, indexes: indexes.into_iter().map(Value::progress).collect() },
            Value::Inductive { ind, ctor, data } => Value::Inductive {
                ind, ctor,
                data: data.into_iter().map(Value::progress).collect(),
            },
            Value::Struct(fields) => Value::Struct(
                fields.iter().map(|(name, val)| (name.clone(), val.clone().progress())).collect()
            ),
            Value::Pending(_) => self,

            // TODO: optimize Ap and Match
            Value::Ap { fun, arg } => fun.progress().ap_with(*arg),
            Value::Match { matched, variants } => matched.progress().match_with(variants),
            Value::Field { parent, field } => parent.progress().field_with(field),
            Value::Placeholder => Value::Placeholder,
            Value::Refl => Value::Refl,
            Value::TypedRefl(ty) => Value::TypedRefl(ty.progress()),
        }
    }

    pub fn unify(&self, ano: &Value) -> Option<Value> {
        // FIXME: correctly unify match body, lambda body, recursive unify, etc
        log::debug!("Value unify: {} <-> {}", self, ano);
        if self == ano {
            return Some(self.clone());
        }
        match (self, ano) {
            (&Value::Placeholder, _) => Some(ano.clone()),
            (_, &Value::Placeholder) => Some(self.clone()),
            (Value::Type(t), Value::Type(at)) => Some(Value::Type(t.clone().unify(at.clone())?).compact()),
            (Value::Lambda { ident, recursor, body }, Value::Lambda { ident: ai, recursor: ar, body: ab }) => {
                let replaced_ab = ab.substitute(*ai, &Value::Pending(*ident)).substitute(*ar, &Value::Pending(*recursor));
                if replaced_ab == **body {
                    return Some(self.clone());
                } else {
                    return None;
                }
            }
            _ => None,
        }
    }

    pub fn promote_ind_type(self) -> Value {
        if let Value::PartiallyIndexedInd { ind, indexes } = &self {
            if let IndPtr::Complete(c) = ind {
                assert!(c.sig.arity() == indexes.len());
            }
            return Value::Type(Rc::new(Type::FullyIndexedInd { ind: ind.clone(), indexes: indexes.clone() }));
        }
        return self;
    }

    pub fn demote_ind_type(self) -> Value {
        if let Value::Type(t) = &self {
            if let Type::FullyIndexedInd { ind, indexes } = &**t {
                return Value::PartiallyIndexedInd { ind: ind.clone(), indexes: indexes.clone() };
            }
        }
        return self;
    }

    pub fn compact(self) -> Value {
        // Persumably we don't need deep compact
        match self {
            Value::Type(ref t) if let Type::Delayed(d) = &**t => d.clone(),
            _ => self,
        }
    }
}

impl Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Equality(eq) => write!(f, "<eq, {:?}>", eq),
            Value::Type(t) => write!(f, "<ty, {:?}>", t),
            Value::Lambda { .. } => write!(f, "<lambda>"),
            Value::PartiallyIndexedInd { .. } => write!(f, "<ind>"),
            Value::Inductive { ctor, data, .. } => {
                write!(f, "{}", ctor)?;
                for d in data.iter() {
                    write!(f, " ({})", d)?;
                }
                Ok(())
            }
            Value::Struct(fields) => {
                write!(f, "{{")?;
                let mut is_first = true;
                for (k, v) in fields {
                    if is_first {
                        write!(f, " ")?;
                    } else {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}: {}", k, v)?;
                    is_first = false;
                }
                if !is_first {
                    write!(f, " ")?;
                }
                write!(f, "}}")?;
                Ok(())
            }
            Value::Ap { fun, arg } => write!(f, "{} {}", fun, arg),
            Value::Match { matched, ..}  => write!(f, "match {}", matched),
            Value::Pending(p) => write!(f, "[{}]", p),
            Value::Placeholder => write!(f, "_"),
            Value::Refl => write!(f, "refl"),
            Value::TypedRefl(t) => write!(f, "refl_{:?}", t),
            Value::Field { parent, field } => write!(f, "({}).{}", parent, field),
        }
    }
}

impl Type {
    pub fn unify(self: Rc<Self>, ano: Rc<Type>) -> Option<Rc<Type>> {
        if self == ano {
            return Some(self);
        }

        // TODO: partial ord?
        match (self.as_ref(), ano.as_ref()) {
            (_, Type::Hole) => Some(self.clone()),
            (Type::Hole, _) => Some(ano.clone()),
            (Type::Partial(a), Type::Partial(b)) => if a == b {
                Some(self.clone())
            } else {
                a.clone().unify(b.clone()).map(Type::Partial).map(Rc::new)
            }
            (Type::Type{ universe }, Type::Type{ universe: anou }) => {
                if universe == anou || anou.is_none() {
                    return Some(self.clone())
                }
                if universe.is_none() {
                    return Some(ano.clone())
                }
                None
            },
            (Type::Fun{ arg, ident, ret }, Type::Fun{ arg: anoarg, ident: anoident, ret: anoret }) => {
                let unified_arg = arg.clone().unify(anoarg.clone())?;
                if ident == anoident {
                    return Some(Rc::new(Type::Fun {
                        arg: unified_arg,
                        ident: ident.clone(),
                        ret: ret.clone(),
                    }))
                }

                let unified_ret = anoret.clone().substitute(*anoident, &Value::Pending(*ident)).unify(ret.clone())?;

                Some(Rc::new(Type::Fun {
                    arg: unified_arg,
                    ident: ident.clone(),
                    ret: unified_ret,
                }))
            },
            (Type::Eq { within, lhs, rhs }, Type::Eq { within: aw, lhs: al, rhs: ar }) => Some(Rc::new(Type::Eq {
                within: within.clone().unify(aw.clone())?,
                lhs: lhs.unify(al)?.clone(),
                rhs: rhs.unify(ar)?.clone(),
            })),
            (Type::FullyIndexedInd { ind, indexes }, Type::FullyIndexedInd { ind: ai, indexes: aidx }) => {
                match (ind, ai) {
                    (IndPtr::Complete(ic), IndPtr::Complete(aic)) => {
                        if ic != aic {
                            return None;
                        }
                    },
                    (IndPtr::SelfInvoc, IndPtr::SelfInvoc) => {},
                    _ => return None,
                }
                let mut idx = im::Vector::new();
                for (ii, aii) in indexes.iter().zip(aidx) {
                    idx.push_back(ii.unify(aii)?);
                }
                Some(Rc::new(Type::FullyIndexedInd { ind: ind.clone(), indexes: idx }))
            },
            (Type::Struct(fa), Type::Struct(fb)) => {
                if fa.len() != fb.len() {
                    return None;
                }

                let mut ret = im::HashMap::new();
                for (k, va) in fa {
                    if let Some(vb) = fb.get(k) {
                        ret.insert(k.clone(), va.clone().unify(vb.clone())?);
                    } else {
                        return None;
                    }
                }

                Some(Rc::new(Type::Struct(ret)))
            },
            // _ => panic!("Type unification not impleneted: {}, {}", self, ano),
            _ => None
        }
    }

    pub fn try_unify<PI>(self: Rc<Self>, ano: Rc<Type>) -> EvalResult<Rc<Type>, PI> {
        self.clone().unify(ano.clone()).ok_or_else(|| {
            EvalError::Ununifiable{
                expected: self,
                actual: ano,
                _pi: PhantomData::default(),
            }
        })
    }

    pub fn arity(&self) -> usize {
        match self {
            Type::Fun{ ret, ..  } => ret.arity() + 1,
            _ => 0,
        }
    }

    pub fn substitute(self: Rc<Self>, ident: ExtBindingIdent, with: &Value) -> Rc<Type> {
        log::debug!("Type {:?} [{}/{:?}]", self, ident, with);
        let ret = match self.as_ref() {
            Type::Hole => self.clone(),
            Type::Partial(p) => Rc::new(Type::Partial(p.clone().substitute(ident, with))),
            Type::Type { .. } => self.clone(),
            Type::Fun { arg, ident: sident, ret } => {
                if *sident == ident {
                    // Inside ctor type instantiate
                    return self.clone();
                }
                Rc::new(Type::Fun {
                    arg: arg.clone().substitute(ident, with),
                    ident: *sident,
                    ret: ret.clone().substitute(ident, with),
                })
            },
            Type::FullyIndexedInd { ind, indexes } => {
                let ind = match ind {
                    IndPtr::SelfInvoc => IndPtr::SelfInvoc,
                    IndPtr::Complete(c) => IndPtr::Complete(Rc::new(c.substitute(ident, with))),
                };
                Rc::new(Type::FullyIndexedInd {
                    ind,
                    indexes: indexes.iter().map(|i| i.substitute(ident, with)).collect(),
                })
            },
            Type::Struct(fields) => {
                Rc::new(Type::Struct(
                    fields.iter().map(|(name, val)| (name.clone(), val.clone().substitute(ident, with))).collect()
                ))
            },
            Type::Delayed(d) => d.substitute(ident, with).try_unwrap_as_type::<()>().unwrap(),
            Type::Eq { within, lhs, rhs } => {
                Rc::new(Type::Eq {
                    within: within.clone().substitute(ident, with),
                    lhs: lhs.substitute(ident, with),
                    rhs: rhs.substitute(ident, with),
                })
            }
        };

        ret.progress().compact()
    }

    pub fn instantiate_self(self: Rc<Self>, ind: Rc<Ind>, top: bool) -> Rc<Type> {
        // Assumes strict postivity
        let ret = match self.as_ref() {
            Type::Fun { arg, ident: sident, ret } => {
                let arg = if top {
                    arg.clone().instantiate_self(ind.clone(), false)
                } else {
                    arg.clone()
                };

                let ret = ret.clone().instantiate_self(ind, top);

                Rc::new(Type::Fun { arg, ident: *sident, ret })
            },
            Type::FullyIndexedInd { ind: orig, indexes } if orig == &IndPtr::SelfInvoc => {
                Rc::new(Type::FullyIndexedInd {
                    ind: IndPtr::Complete(ind),
                    indexes: indexes.clone(),
                })
            },
            _ => self.clone(),
        };

        ret.progress().compact()
    }

    pub fn progress(self: Rc<Self>) -> Rc<Type> {
        if let Type::Delayed(v) = &*self {
            return Rc::new(Type::Delayed(v.clone().progress())).compact();
        }

        return self;
    }

    pub fn assert_concrete<PI>(&self) -> EvalResult<(), PI> {
        // FIXME: impl
        Ok(())
    }

    pub fn compact(self: Rc<Self>) -> Rc<Type> {
        // Persumably we don't need deep compact
        match &*self {
            Type::Delayed(Value::Type(t)) => t.clone(),
            _ => self,
        }
    }
}

#[derive(Error, Debug)]
pub enum EvalError<PI> {
    #[error("Ununifiable types, expected {expected}, got {actual}")]
    Ununifiable {
        expected: Rc<Type>,
        actual: Rc<Type>,

        // TODO: implement parser info
        _pi: PhantomData<PI>,
    },

    #[error("Expected type, got {actual} with type {ty}")]
    TypeOnly {
        actual: Value,
        ty: Rc<Type>,
    },

    #[error("Can only match inductive types, got {actual} with type {ty}")]
    NonIndMatch {
        actual: Value,
        ty: Rc<Type>,
    },

    #[error("Can only select ctor of non-indexed inductive types, got {actual}")]
    NonIndCtor {
        actual: Value,
    },

    #[error("Ctor `{ctor}` not present in inductive types {ind:?}")]
    UndefinedCtor {
        ctor: String,
        ind: Rc<Ind>,
    },

    #[error("Can only select field of structs, got {actual} of type {ty}")]
    NonStructField {
        actual: Value,
        ty: Rc<Type>,
    },

    #[error("Field `{field}` not present in type {ty:?}")]
    UndefinedField {
        field: String,
        ty: Rc<Type>,
    },

    #[error("Matching arm for ctor `{ctor}` of {ind:?} got wrong number of data binding: got {actual}")]
    MatchWrongArity {
        ctor: String,
        ind: Rc<Ind>,
        actual: usize,
    },

    #[error("Matching arm for ctor `{ctor}` of {ind:?} got wrong number of evidence: got {actual}")]
    MatchWrongEvidence {
        ctor: String,
        ind: Rc<Ind>,
        actual: usize,
    },

    #[error("Ctor `{ctors:?}` missing when matching inductive types {ind:?}")]
    MatchNonExhaustive {
        ctors: Vec<String>,
        ind: Rc<Ind>,
    },

    #[error("`self` used outside of inductive defination")]
    SelfOutsideInd,

    #[error("Undefined name / constructor: {name}")]
    Undefined {
        name: String,
    },

    #[error("Unexpected type signature")]
    UnexpectedSig {
        // name: &'a Name<'a, PI>,
        name: String,
    },

    #[error("Unbounded recursion")]
    UnboundedRecursion,

    #[error("Cannot cast with type: {ty}")]
    NonTyEqCast {
        ty: Rc<Type>,
    },

    #[error("Cannot transport with dependent function: {ty}")]
    DependentTransport {
        ty: Rc<Type>,
    },

    #[error("Error occured when processing import {path}: {error}")]
    Import {
        path: String,
        error: anyhow::Error,
    },
}

type EvalResult<T, PI> = Result<T, EvalError<PI>>;

/// Distinguishing different external binding
type ExtBindingIdent = usize;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Source {
    /// Functiona argument
    External {
        ident: ExtBindingIdent,
    },

    /// Destructed from an external argument
    Destructed {
        source: ExtBindingIdent,
    },

    /// Given as recursor
    Recursor {
        /// Null = partial recursor
        linked: ExtBindingIdent,
    },

    /// From arbitrary expression
    Constructed,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Evaluated(
    pub Value,
    pub Rc<Type>,
    pub Source,
);

impl Evaluated {
    pub fn create<PI>(v: Value, t: Rc<Type>, src: Source) -> EvalResult<Self, PI> {
        // TODO: check if t is concrete
        t.assert_concrete()?;
        Ok(Self(v.compact(), t.compact(), src))
    }

    pub fn try_unwrap_as_type<PI>(self) -> EvalResult<Rc<Type>, PI> {
        // TODO: return universe
        match self.1.as_ref() {
            Type::Type { .. } => {},
            _ => return Err(EvalError::TypeOnly{ actual: self.0, ty: self.1 })
        }
        self.0.try_unwrap_as_type()
    }

    pub fn substitute(&self, ident: ExtBindingIdent, with: &Value) -> Evaluated {
        Evaluated(
            self.0.substitute(ident, with),
            self.1.clone().substitute(ident, with),
            self.2.clone()
        )
    }
}

#[derive(Clone, Default)]
struct Scope<'a> {
    bindings: im::HashMap<&'a str, Evaluated>,
    ind_type: Option<Rc<Type>>,
}

impl<'a> Scope<'a> {
    pub fn bind(&self, name: &'a str, bounded: Evaluated) -> Self {
        Scope {
            bindings: self.bindings.update(name, bounded),
            ind_type: self.ind_type.clone(),
        }
    }

    pub fn inside_ind(&self, ty: Rc<Type>) -> Self {
        Scope {
            bindings: self.bindings.clone(),
            ind_type: Some(ty),
        }
    }
}

#[derive(Default)]
pub struct EvalCtx {
    ticket_gen: usize,
}

impl EvalCtx {
    // TODO: ensure hint and result type is always unifiable
    fn eval<'a, PI: Debug>(
        &mut self,
        expr: &'a Expr<'a, PI>,
        scope: &Scope<'a>,
        hint: Rc<Type>,
        at: &PathBuf,
        runner: &mut Runner,
    ) -> EvalResult<Evaluated, PI> {
        log::debug!("Eval: {:?}", expr);
        match &expr.inner {
            ExprInner::PartialType(inner) => {
                let inner_hint = hint.try_unify(Rc::new(Type::Type{ universe: None }))?;

                let inner = self.eval(inner.as_ref(), scope, inner_hint, at, runner)?;
                let Evaluated(_, t, src) = inner.clone();
                let wrapped = Type::Partial(inner.try_unwrap_as_type()?);
                Evaluated::create(Value::Type(Rc::new(wrapped)), t, src)
            },
            ExprInner::Ind { sig, ctors } => {
                let interface = if let Some(sig) = sig {
                    let sig_val = self.eval_hint(sig.as_ref(), scope, at, runner)?;
                    // TODO: check if sig is a type
                    hint.try_unify(sig_val)?
                } else {
                    hint
                };

                // TODO: ensure hint is concrete
                // TODO: check if hint is _ -> _ -> type _ ?

                let inner_scope = scope.inside_ind(interface.clone());
                let mut mapped_ctors = im::HashMap::new();
                for ctor in ctors.iter() {
                    let ctor_type_value = self.eval_hint(&ctor.sig, &inner_scope, at, runner)?;
                     
                    // TODO: check strict positivity and ctor yield type
                    // TODO: check ctor is inside the required universe
                    mapped_ctors.insert(ctor.name.to_owned(), ctor_type_value);
                }

                let ind = IndPtr::Complete(Rc::new(Ind { variants: mapped_ctors, sig: interface.clone() }));
                let mut self_val = Value::PartiallyIndexedInd { ind, indexes: im::Vector::new() };
                if let Type::Type { .. } = &*interface {
                    self_val = self_val.promote_ind_type();
                }
                Evaluated::create(self_val, interface, Source::Constructed)
            },
            ExprInner::Fun(f) => {
                let self_hint = hint.try_unify(Rc::new(Type::Type{ universe: None }))?;
                let (input_arg_name, input_type) = match &f.input.inner {
                    ExprInner::Name(name) if name.sig.is_some() => {
                        (Some(name.name), name.sig.as_ref().unwrap())
                    }
                    _ => (None, f.input.as_ref()),
                };
                let input_type_val = self.eval_hint(input_type, scope, at, runner)?;

                // Update scope before passing down for named dependent type variable
                let inner_scope_data;
                let mut inner_scope = scope;
                let arg_ident = self.count_external();
                if let Some(arg_name) = input_arg_name {
                    let bounded = Evaluated::create(Value::Pending(arg_ident), input_type_val.clone(), Source::External{ ident: arg_ident })?;
                    inner_scope_data = scope.bind(arg_name, bounded);
                    inner_scope = &inner_scope_data;
                }
                let ret_type_val = self.eval(f.output.as_ref(), inner_scope, Rc::new(Type::Type{ universe: None }), at, runner)?.try_unwrap_as_type()?;
                let self_type_val = Rc::new(Type::Fun{
                    arg: input_type_val,
                    ident: arg_ident,
                    ret: ret_type_val,
                });
                // FIXME: pin down universe
                Evaluated::create(Value::Type(self_type_val), Rc::new(Type::Type{ universe: Some(0) }), Source::Constructed)
            },
            ExprInner::Lambda { arg, ret, body, rec } => {
                let hint = hint.try_unify(Rc::new(Type::Fun {
                    arg: Rc::new(Type::Hole),
                    ident: 0,
                    ret: Rc::new(Type::Hole),
                }))?;

                let (arg_hint, mut arg_ident, ret_hint) = match hint.as_ref() {
                    Type::Fun{ arg, ident, ret } => (arg, *ident, ret),
                    _ => unreachable!()
                };

                // Evaluate arg type
                if arg_ident == 0 {
                    arg_ident = self.count_external();
                }
                let arg_type = if let Some(sig) = arg.sig.as_ref() {
                    self.eval_hint(sig, scope, at, runner)?.try_unify(arg_hint.clone())?
                } else {
                    arg_hint.clone()
                };

                // Introduce arg into scope
                let bounded = Evaluated::create(Value::Pending(arg_ident), arg_type.clone(), Source::External{ ident: arg_ident })?;
                let ret_scope = scope.bind(arg.name, bounded);

                // Evaluate ret type
                let ret_type= if let Some(sig) = ret.as_ref() {
                    self.eval_hint(sig, &ret_scope, at, runner)?.try_unify(ret_hint.clone())?
                } else {
                    ret_hint.clone()
                };

                let self_type = Rc::new(Type::Fun {
                    arg: arg_type.clone(),
                    ident: arg_ident,
                    ret: ret_type.clone(),
                });

                // Introduce rec
                let recursor_ident = self.count_external();
                let mut inner_scope = ret_scope;
                if let Some(rec) = rec {
                    let rec_bounded = Evaluated::create(Value::Pending(recursor_ident), self_type.clone(), Source::Recursor{ linked: arg_ident })?;
                    inner_scope = inner_scope.bind(rec, rec_bounded);
                }

                // Do shadowed eval / type check in body
                let body_eval = self.eval(body.as_ref(), &inner_scope, ret_type, at, runner)?;
                let body_ty = body_eval.1.clone();

                let self_val = Value::Lambda {
                    ident: arg_ident,
                    recursor: recursor_ident,
                    body: Box::new(body_eval),
                };

                let self_type = Rc::new(Type::Fun {
                    arg: arg_type,
                    ident: arg_ident,
                    ret: body_ty,
                });

                Evaluated::create(self_val, self_type, Source::Constructed)
            },
            ExprInner::Binding { binding, rest } => {
                let binding_hint = if let Some(sig) = &binding.name.sig {
                    self.eval_hint(sig, scope, at, runner)?
                } else {
                    Rc::new(Type::Hole)
                };
                let evaled = self.eval(&binding.val, scope, binding_hint, at, runner)?;
                let inner_scope = scope.bind(binding.name.name, evaled);
                self.eval(rest.as_ref(), &inner_scope, hint, at, runner)
            },
            ExprInner::Name(name) => {
                if name.sig.is_some() {
                    return Err(EvalError::UnexpectedSig{ name: name.name.to_owned() })
                }
                let value = scope.bindings.get(name.name).cloned().ok_or(EvalError::Undefined{ name: name.name.to_owned() })?;
                hint.try_unify(value.1.clone())?;
                Ok(value)
            },
            ExprInner::Ap(pair) => {
                let (f, arg) = pair.as_ref();
                // TODO: finer grind hints
                let f_eval = self.eval(f, scope, Rc::new(Type::Fun {
                    arg: Rc::new(Type::Hole),
                    ident: 0,
                    ret: Rc::new(Type::Hole),
                }), at, runner)?;

                log::debug!("Applying function {:#?}", f_eval);
                let (arg_type, arg_ident, ret_type) = match f_eval.1.as_ref() {
                    Type::Fun { arg, ident, ret } => (arg, *ident, ret),
                    _ => panic!("Why did ap get a {:?}", f_eval.1),
                };
                let arg_eval = self.eval(arg, scope, arg_type.clone(), at, runner)?;
                // TODO: assert arg type concrete
                let ret_type = ret_type.clone().substitute(arg_ident, &arg_eval.0);
                let ret_type = ret_type.try_unify(hint)?;

                if let Source::Recursor { linked } = f_eval.2 {
                    match arg_eval.2 {
                        Source::Destructed { source } if source == linked => {},
                        _ => return Err(EvalError::UnboundedRecursion),
                    }
                }

                let mut val = Value::Ap {
                    fun: Box::new(f_eval.0),
                    arg: Box::new(arg_eval.0),
                }.progress();

                if let Type::Type { .. } = &*ret_type {
                    val = val.promote_ind_type();
                }

                Evaluated::create(val, ret_type, Source::Constructed)
            },
            ExprInner::Match { matched, arms } => {
                // Build pendings
                let Evaluated(matched_val, matched_type, matched_src) = self.eval(matched.as_ref(), scope, Rc::new(Type::Hole), at, runner)?;
                let (ind, indexes) = match matched_type.as_ref() {
                    Type::FullyIndexedInd { ind, indexes } => {
                        match ind {
                            IndPtr::SelfInvoc => unreachable!(), // We should never get self out side of ind defination
                            IndPtr::Complete(ind) => (ind, indexes),
                        }
                    },
                    _ => {
                        return Err(EvalError::NonIndMatch{ actual: matched_val, ty: matched_type });
                    },
                };

                let ind_arity = ind.sig.arity();
                assert!(ind_arity == indexes.len());

                let data_src = match matched_src {
                    Source::External { ident: source } | Source::Destructed { source } => Source::Destructed { source },
                    _ => Source::Constructed,
                };

                // Check exhaustiveness
                let mut remaining = ind.variants.clone();
                let mut evaluated_arms = HashMap::new();
                let mut cur_hint = hint;
                for arm in arms {
                    if arm.sig.is_some() {
                        // TODO: impl typed match arms
                        panic!("Currently don't supports typed match");
                    }

                    let mut variant_sig = remaining.remove(arm.ctor).ok_or(EvalError::UndefinedCtor { ctor: arm.ctor.to_owned(), ind: ind.clone() })?;

                    let arity = variant_sig.arity();
                    if arity != arm.data.len() {
                        return Err(EvalError::MatchWrongArity { actual: arm.data.len(), ctor: arm.ctor.to_owned(), ind: ind.clone() })
                    }
                    if ind_arity + 1 != arm.ev.len() {
                        return Err(EvalError::MatchWrongEvidence { actual: arm.ev.len(), ctor: arm.ctor.to_owned(), ind: ind.clone() })
                    }

                    // Generate datum bindings
                    let mut arm_scope = scope.clone();
                    let mut data_idents = Vec::new();
                    let mut data_names = arm.data.iter();
                    let arm_indexes = loop {
                        match variant_sig.as_ref() {
                            Type::Fun { arg, ident: orig, ret } => {
                                let ident = self.count_external();
                                data_idents.push(ident);
                                let val = Value::Pending(ident);

                                let bounded = Evaluated(val.clone(), arg.clone().instantiate_self(ind.clone(), true), data_src.clone());
                                let name = data_names.next().unwrap();
                                arm_scope = arm_scope.bind(*name, bounded);

                                variant_sig = ret.clone().substitute(*orig, &val);
                            },
                            Type::FullyIndexedInd { ind, indexes } => {
                                assert!(*ind == IndPtr::SelfInvoc);
                                break indexes;
                            },
                            _ => unreachable!()
                        }
                    };

                    let data_arm_scope = arm_scope.clone();
                    let constructed = Value::Inductive {
                        ind: ind.clone(),
                        ctor: arm.ctor.to_owned(),
                        data: data_idents.iter().cloned().map(|ident| Value::Pending(ident)).collect()
                    };
                    let mut matched_eq = Rc::new(Type::Eq {
                        within: matched_type.clone(),
                        lhs: constructed,
                        rhs: matched_val.clone(),
                    });
                    let mut ev_names = arm.ev.iter();
                    let full_ev_name = ev_names.next().unwrap();
                    if let Some(sig) = full_ev_name.sig.as_ref(){
                        matched_eq = self.eval_hint(sig, &data_arm_scope, at, runner)?.try_unify(matched_eq)?;
                    }
                    let matched_ev = Evaluated(Value::Equality(matched_eq.clone()), matched_eq, Source::Constructed);
                    arm_scope = arm_scope.bind(full_ev_name.name, matched_ev);

                    let mut ind_sig = ind.sig.clone();
                    let mut index_pairs = ev_names.zip(arm_indexes.iter().zip(indexes.iter()));
                    loop {
                        match ind_sig.as_ref() {
                            Type::Fun { arg, ident: orig, ret } => {
                                // Base type
                                let (ev_name, (lhs, rhs)) = index_pairs.next().unwrap();
                                let mut ev_ty = Rc::new(Type::Eq {
                                    within: arg.clone(),
                                    lhs: lhs.clone(),
                                    rhs: rhs.clone(),
                                });
                                if let Some(sig) = ev_name.sig.as_ref(){
                                    ev_ty = self.eval_hint(sig, &data_arm_scope, at, runner)?.try_unify(ev_ty)?;
                                }
                                let ev = Evaluated(Value::Equality(ev_ty.clone()), ev_ty, Source::Constructed);
                                arm_scope = arm_scope.bind(ev_name.name, ev);

                                ind_sig = ret.clone().substitute(*orig, lhs);
                            },
                            Type::Type { .. } => break,
                            _ => unreachable!(),
                        }
                    }

                    let body = self.eval(&arm.body, &arm_scope, cur_hint.clone(), at, runner)?;
                    cur_hint = cur_hint.try_unify(body.1.clone())?;
                    evaluated_arms.insert(arm.ctor, (data_idents, body));
                }

                if remaining.len() != 0 {
                    return Err(EvalError::MatchNonExhaustive {
                        ctors: remaining.keys().cloned().collect(),
                        ind: ind.clone(),
                    });
                }

                // Merge source
                let mut src = evaluated_arms.values().next().map(|(_, e)| e.2.clone()).unwrap_or(Source::Constructed);
                for (_, arm) in evaluated_arms.values() {
                    match arm.2 {
                        Source::Destructed { .. } if arm.2 == src => {},
                        _ => src = Source::Constructed,
                    }
                }

                // Check if all variants have same result type
                cur_hint.assert_concrete()?;
                let variants: EvalResult<im::HashMap<_, _>, PI> = evaluated_arms.into_iter().map(|(name, (captures, eval))| {
                    cur_hint.clone().try_unify(eval.1)?;
                    Ok((name.to_owned(), Variant {
                        captures,
                        value: eval.0,
                    }))
                }).collect();
                let variants = variants?;

                // TODO: respect opaque?
                let val = Value::Match {
                    matched: Box::new(matched_val),
                    variants,
                }.progress();

                Evaluated::create(val, cur_hint, src)
            },
            ExprInner::CtorOf { parent, variant } => {
                let parent = self.eval(parent.as_ref(), scope, Rc::new(Type::Hole), at, runner)?;
                let demoted = parent.0.demote_ind_type();
                let ind = match demoted {
                    Value::PartiallyIndexedInd { ind, indexes } if indexes.len() == 0 => {
                        match ind {
                            IndPtr::SelfInvoc => unreachable!(), // We should never get self out side of ind defination
                            IndPtr::Complete(ind) => ind,
                        }
                    },
                    _ => {
                        return Err(EvalError::NonIndCtor { actual: demoted });
                    },
                };

                let ctor_type = ind.variants.get(*variant).ok_or(EvalError::UndefinedCtor { ctor: (*variant).to_owned(), ind: ind.clone() })?;
                let ctor_type = ctor_type.clone().instantiate_self(ind.clone(), true);
                let ctor_type = ctor_type.try_unify(hint)?;

                Evaluated::create(
                    Value::Inductive {
                        ind,
                        ctor: (*variant).to_owned(),
                        data: im::Vector::new(),
                    },
                    ctor_type,
                    Source::Constructed,
                )
            },
            ExprInner::Universe{ level } => {
                let level = level.expect("Currently we don't support the `type _` universe kind");
                let self_type = hint.try_unify(Rc::new(Type::Type {
                    universe: Some(level + 1),
                }))?;
                Evaluated::create(
                    Value::Type(Rc::new(Type::Type { universe: Some(level) })),
                    self_type,
                    Source::Constructed,
                )
            }
            ExprInner::SelfInvoc => {
                let val = Value::PartiallyIndexedInd{ ind: IndPtr::SelfInvoc, indexes: im::Vector::new() };
                Evaluated::create(val, scope.ind_type.clone().ok_or(EvalError::SelfOutsideInd)?, Source::Constructed)
            }
            ExprInner::ReflInvoc => {
                let ty_ident = self.count_external();
                let val_ident = self.count_external();
                let ty = Rc::new(Type::Delayed(Value::Pending(ty_ident)));
                Evaluated::create(Value::Refl, Rc::new(Type::Fun {
                    arg: Rc::new(Type::Type { universe: None }),
                    ident: ty_ident,
                    ret: Rc::new(Type::Fun {
                        arg: ty.clone(),
                        ident: val_ident,
                        ret: Rc::new(Type::Eq {
                            within: ty,
                            lhs: Value::Pending(val_ident),
                            rhs: Value::Pending(val_ident),
                        }),
                    }),
                }), Source::Constructed)
            }
            ExprInner::Cast { orig, eq } => {
                let eq = self.eval(eq, scope, Rc::new(Type::Eq {
                    within: Rc::new(Type::Type { universe: None }),
                    lhs: Value::Type(Rc::new(Type::Hole)),
                    rhs: Value::Type(hint).compact(),
                }), at, runner)?;
                let (lhs, rhs, univ) = match eq.1.as_ref() {
                    Type::Eq {
                        within,
                        lhs,
                        rhs,
                    } => {
                        let univ = if let Type::Type { universe } = within.as_ref() {
                            universe
                        } else {
                            return Err(EvalError::NonTyEqCast { ty: eq.1 });
                        };
                        (lhs.clone().try_unwrap_as_type()?, rhs.clone().try_unwrap_as_type()?, univ)
                    },
                    _ => return Err(EvalError::NonTyEqCast { ty: eq.1 }),
                };

                // TODO: check universe
                let mut val = self.eval(orig, scope, lhs.clone(), at, runner)?;
                // Fixme: check lhs and orig type is the same
                if val.1 != lhs {
                    println!("evaluated type: {}", val.1);
                    println!("expected type: {}", lhs);
                    panic!("Cast eq sanity check failed");
                }

                val.1 = rhs;
                Ok(val)
            },
            ExprInner::EqAp { eq, fun } => {
                let unified = hint.try_unify(Rc::new(Type::Eq {
                    within: Rc::new(Type::Hole),
                    lhs: Value::Placeholder,
                    rhs: Value::Placeholder,
                }))?;

                let within = match unified.as_ref() {
                    Type::Eq {
                        within,
                        ..
                    } => {
                        within
                    },
                    _ => unreachable!()
                };

                let eq = self.eval(eq, scope, Rc::new(Type::Eq {
                    within: Rc::new(Type::Hole),
                    lhs: Value::Placeholder,
                    rhs: Value::Placeholder,
                }), at, runner)?;

                let (lhs, rhs, arg_ty) = match eq.1.as_ref() {
                    Type::Eq {
                        within,
                        lhs,
                        rhs,
                    } => {
                        (lhs, rhs, within)
                    },
                    _ => unreachable!()
                };

                let fun = self.eval(fun, scope, Rc::new(Type::Fun {
                    arg: arg_ty.clone(),
                    ident: 0,
                    ret: Rc::new(Type::Hole),
                }), at, runner)?;

                // Asserts ret is non dependent on fun
                let (ident, ret) = match fun.1.as_ref() {
                    Type::Fun { ident, ret, .. } => (ident, ret),
                    _ => unreachable!()
                };
                
                let lhs_ap_ty = ret.clone().substitute(*ident, lhs);
                let rhs_ap_ty = ret.clone().substitute(*ident, rhs);
                if lhs_ap_ty != rhs_ap_ty {
                    log::info!("{:?}", lhs_ap_ty);
                    log::info!("{:?}", rhs_ap_ty);
                    return Err(EvalError::DependentTransport { ty: fun.1 })
                }

                within.clone().try_unify(lhs_ap_ty.clone())?;

                let lhs_ap = Value::Ap {
                    fun: Box::new(fun.0.clone()),
                    arg: Box::new(lhs.clone()),
                }.progress();

                let rhs_ap = Value::Ap {
                    fun: Box::new(fun.0),
                    arg: Box::new(rhs.clone()),
                }.progress();

                let ret_ty = Rc::new(Type::Eq {
                    within: lhs_ap_ty.clone(),
                    lhs: lhs_ap,
                    rhs: rhs_ap,
                });

                Evaluated::create(Value::Equality(ret_ty.clone()), ret_ty, Source::Constructed)
            },
            ExprInner::Eq { lhs, rhs } => {
                let lhs = self.eval(lhs, scope, Rc::new(Type::Hole), at, runner)?;
                let rhs = self.eval(rhs, scope, lhs.1.clone(), at, runner)?;

                let within = rhs.1.clone();
                let eq = Rc::new(Type::Eq {
                    within,
                    lhs: lhs.0,
                    rhs: rhs.0,
                });

                // FIXME: universe + 1

                Evaluated::create(
                    Value::Type(eq),
                    Rc::new(Type::Type { universe: None }),
                    Source::Constructed,
                )
            },
            ExprInner::StructTy(fields) => {
                let hint = hint.try_unify(Rc::new(Type::Type{ universe: None }))?;
                let mut ret = im::HashMap::new();
                for f in fields {
                    let v = f.sig.as_ref()
                        .map(|s| self.eval(s, scope, Rc::new(Type::Type{ universe: None }), at, runner))
                        .map(|e| e.and_then(|e| e.0.try_unwrap_as_type())).transpose()?
                        .unwrap_or_else(|| Rc::new(Type::Hole));
                    ret.insert(f.name.to_owned(), v);
                }

                // TODO: check universe
                Evaluated::create(
                    Value::Type(Rc::new(Type::Struct(ret))),
                    hint,
                    Source::Constructed,
                )
            },
            ExprInner::Struct(fields) => {
                let mut field_hints = im::HashMap::new();
                for binding in fields {
                    let sig = if let Some(sig) = &binding.name.sig {
                        self.eval_hint(sig, scope, at, runner)?
                    } else {
                        Rc::new(Type::Hole)
                    };
                    field_hints.insert(binding.name.name.to_owned(), sig);
                }
                let unified = hint.try_unify(Rc::new(Type::Struct(field_hints)))?;
                let mut field_hints = match &*unified {
                    Type::Struct(f) => f.clone(),
                    _ => unreachable!(),
                };

                let mut values = im::HashMap::new();
                for binding in fields {
                    let hint = field_hints.get(binding.name.name).unwrap();
                    let evaled = self.eval(&binding.val, scope, hint.clone(), at, runner)?;
                    values.insert(binding.name.name.to_owned(), evaled.0);
                    field_hints.insert(binding.name.name.to_owned(), evaled.1);
                }

                Evaluated::create(Value::Struct(values), Rc::new(Type::Struct(field_hints)), Source::Constructed)
            },

            ExprInner::Field { parent, field } => {
                let parent_eval = self.eval(parent.as_ref(), scope, Rc::new(Type::Hole), at, runner)?;
                let field_types = match &*parent_eval.1 {
                    &Type::Struct(ref s) => {
                        s
                    },
                    _ => return Err(EvalError::NonStructField { actual: parent_eval.0, ty: parent_eval.1 }),
                };
                let field_ty = field_types.get(*field).ok_or_else(|| EvalError::UndefinedField { field: (*field).to_owned(), ty: parent_eval.1.clone() })?;
                let field_ty = hint.try_unify(field_ty.clone())?;

                let val = parent_eval.0.field_with((*field).to_owned());

                let src = match parent_eval.2 {
                    Source::External { ident: source } | Source::Destructed { source } => Source::Destructed { source },
                    _ => Source::Constructed,
                };

                Evaluated::create(val, field_ty, src)
            },
            ExprInner::Import(path) => {
                runner.run_import(at, path).map_err(|error| EvalError::Import { path: format!("{}", path), error })
            },
        }
    }

    pub fn eval_hint<'a, PI: Debug>(&mut self, sig: &'a Expr<'a, PI>, scope: &Scope<'a>, at: &PathBuf, runner: &mut Runner) -> EvalResult<Rc<Type>, PI> {
        let evaluated = self.eval(sig, scope, Rc::new(Type::Type{ universe: None }), at, runner)?;
        // TODO: check is type
        evaluated.try_unwrap_as_type()
    }

    fn count_external(&mut self) -> ExtBindingIdent {
        self.ticket_gen += 1;
        self.ticket_gen
    }

    pub fn eval_top<'a, PI: Debug>(&mut self, expr: &'a Expr<'a, PI>, at: &PathBuf, runner: &mut Runner) -> EvalResult<Evaluated, PI> {
        let scope = Scope::default();
        let hint = Rc::new(Type::Hole);
        self.eval(expr, &scope, hint, at, runner)
    }
}