use std::{rc::Rc, collections::HashMap, fmt::Display};

use thiserror::Error;

use crate::data::{Expr, ExprInner, Name};

#[derive(Debug, PartialEq, Eq)]
pub struct Ind<'a> {
    sig: Rc<Type<'a>>,
    // indexes: Vec<Rc<Type<'a>>>,
    variants: im::HashMap<&'a str, Rc<Type<'a>>>,
}

impl<'a> Ind<'a> {
    pub fn substitute(&self, ident: ExtBindingIdent, with: &Value<'a>) -> Ind<'a> {
        log::debug!("Ind sub: {:?} [{}/{:?}]", self, ident, with);
        Ind {
            sig: self.sig.clone().substitute(ident, with),
            variants: self.variants.iter().map(|(name, orig)| (*name, orig.clone().substitute(ident, with))).collect(),
        }
    }
}

#[derive(Debug, PartialEq, Clone, Eq)]
pub enum IndPtr<'a> {
    SelfInvoc,
    Complete(Rc<Ind<'a>>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Variant<'a> {
    captures: Vec<ExtBindingIdent>,
    value: Value<'a>,
    // TODO: allow different ret in match
    // ret: Type<'a>,
}

impl<'a> Variant<'a> {
    pub fn substitute(&self, ident: ExtBindingIdent, with: &Value<'a>) -> Variant<'a> {
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
pub enum Value<'a> {
    Refl,
    TypedRefl(Rc<Type<'a>>),
    Equality(Rc<Type<'a>>),
    Type(Rc<Type<'a>>),
    Lambda {
        ident: ExtBindingIdent,
        recursor: ExtBindingIdent,
        body: Box<Evaluated<'a>>,
    },
    PartiallyIndexedInd {
        ind: IndPtr<'a>,
        // Maybe partially indexed
        indexes: im::Vector<Value<'a>>,
    },
    Inductive {
        ind: Rc<Ind<'a>>,
        ctor: &'a str,
        // Maybe partially applied
        data: im::Vector<Value<'a>>,
    },

    // Delayed evaluation
    Ap {
        fun: Box<Value<'a>>,
        arg: Box<Value<'a>>,
    },
    Match {
        matched: Box<Value<'a>>,
        variants: im::HashMap<&'a str, Variant<'a>>,
    },
    Pending(ExtBindingIdent),
    Placeholder, // Hole in identity, hole in argument, etc
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub enum Type<'a> {
    Hole,
    Partial(Rc<Type<'a>>),

    Type {
        universe: Option<usize>,
    },
    Eq {
        within: Rc<Type<'a>>,
        lhs: Value<'a>,
        rhs: Value<'a>,
    },
    Fun {
        arg: Rc<Type<'a>>,
        ident: ExtBindingIdent,
        ret: Rc<Type<'a>>,
    },
    FullyIndexedInd {
        ind: IndPtr<'a>,
        indexes: im::Vector<Value<'a>>,
    },
    // Ap, Match, Pending
    Delayed(Value<'a>),
}

impl<'a> From<Rc<Type<'a>>> for Value<'a> {
    fn from(v: Rc<Type<'a>>) -> Self {
        Value::Type(v)
    }
}

impl<'a> Value<'a> {
    pub fn substitute(&self, ident: ExtBindingIdent, with: &Value<'a>) -> Value<'a> {
        match self {
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
                variants: variants.iter().map(|(ctor, variant)| (*ctor, variant.substitute(ident, with))).collect(),
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
                    ctor: *ctor,
                    data: data.iter().map(|d| d.substitute(ident, with)).collect()
                }
            },
            Value::Placeholder => Value::Placeholder,
            Value::Refl => Value::Refl,
            Value::TypedRefl(ty) => Value::TypedRefl(ty.clone().substitute(ident, with)),
        }
    }

    pub fn match_with(self, variants: im::HashMap<&'a str, Variant<'a>>) -> Value<'a> {
        match self {
            Value::Inductive { ind, ctor, data } => {
                // TODO: sanity check ind = matched
                let variant = variants.get(ctor).unwrap();
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

    pub fn ap_with(self, arg: Value<'a>) -> Value<'a> {
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

    pub fn try_unwrap_as_type<PI>(self) -> EvalResult<'a, Rc<Type<'a>>, PI> {
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

    pub fn progress(self) -> Value<'a> {
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
            Value::Pending(_) => self,

            // TODO: optimize Ap and Match
            Value::Ap { fun, arg } => fun.progress().ap_with(*arg),
            Value::Match { matched, variants } => matched.progress().match_with(variants),
            Value::Placeholder => Value::Placeholder,
            Value::Refl => Value::Refl,
            Value::TypedRefl(ty) => Value::TypedRefl(ty.progress()),
        }
    }
}

impl<'a> Display for Value<'a> {
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
            Value::Ap { fun, arg } => write!(f, "(ap {}, {})", fun, arg),
            Value::Match { matched, ..}  => write!(f, "(match {})", matched),
            Value::Pending(p) => write!(f, "[{}]", p),
            Value::Placeholder => write!(f, "_"),
            Value::Refl => write!(f, "refl"),
            Value::TypedRefl(t) => write!(f, "refl_{:?}", t),
        }
    }
}

impl<'a> Type<'a> {
    pub fn unify(self: Rc<Self>, ano: Rc<Type<'a>>) -> Option<Rc<Type<'a>>> {
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

                return Some(Rc::new(Type::Fun {
                    arg: unified_arg,
                    ident: ident.clone(),
                    ret: unified_ret,
                }));
            },
            _ => panic!("Type unification not impleneted: {:#?}, {:#?}", self, ano),
        }
    }

    pub fn try_unify<PI>(self: Rc<Self>, ano: Rc<Type<'a>>) -> EvalResult<'a, Rc<Type<'a>>, PI> {
        self.clone().unify(ano.clone()).ok_or_else(|| {
            EvalError::Ununifiable{
                expected: self,
                actual: ano,
            }
        })
    }

    pub fn arity(&self) -> usize {
        match self {
            Type::Fun{ ret, ..  } => ret.arity() + 1,
            _ => 0,
        }
    }

    pub fn substitute(self: Rc<Self>, ident: ExtBindingIdent, with: &Value<'a>) -> Rc<Type<'a>> {
        log::debug!("Type {:?} [{}/{:?}]", self, ident, with);
        match self.as_ref() {
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
            Type::Delayed(d) => d.substitute(ident, with).try_unwrap_as_type::<()>().unwrap(),
            Type::Eq { within, lhs, rhs } => {
                Rc::new(Type::Eq {
                    within: within.clone().substitute(ident, with),
                    lhs: lhs.substitute(ident, with),
                    rhs: rhs.substitute(ident, with),
                })
            }
        }
    }

    pub fn instantiate_self(self: Rc<Self>, ind: Rc<Ind<'a>>, top: bool) -> Rc<Type<'a>> {
        // Assumes strict postivity
        match self.as_ref() {
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
        }
    }

    pub fn progress(self: Rc<Self>) -> Rc<Type<'a>> {
        // TODO: do we need to do anything here?
        self
    }

    pub fn assert_concrete<PI>(&self) -> EvalResult<'a, (), PI> {
        // FIXME: impl
        Ok(())
    }
}

#[derive(Error, Debug)]
pub enum EvalError<'a, PI> {
    #[error("Ununifiable types, expected {expected:?}, got {actual:?}")]
    Ununifiable {
        expected: Rc<Type<'a>>,
        actual: Rc<Type<'a>>,
    },

    #[error("Expected type, got {actual:?} with type {ty:?}")]
    TypeOnly {
        actual: Value<'a>,
        ty: Rc<Type<'a>>,
    },

    #[error("Can only match inductive types, got {actual:?} with type {ty:?}")]
    NonIndMatch {
        actual: Value<'a>,
        ty: Rc<Type<'a>>,
    },

    #[error("Can only select ctor of non-indexed inductive types, got {actual:?}")]
    NonIndCtor {
        actual: Value<'a>,
    },

    #[error("Ctor `{ctor}` not present in inductive types {ind:?}")]
    UndefinedCtor {
        ctor: &'a str,
        ind: Rc<Ind<'a>>,
    },

    #[error("Matching arm for ctor `{ctor}` of {ind:?} got wrong number of data binding: got {actual}")]
    MatchWrongArity {
        ctor: &'a str,
        ind: Rc<Ind<'a>>,
        actual: usize,
    },

    #[error("Matching arm for ctor `{ctor}` of {ind:?} got wrong number of evidence: got {actual}")]
    MatchWrongEvidence {
        ctor: &'a str,
        ind: Rc<Ind<'a>>,
        actual: usize,
    },

    #[error("Ctor `{ctors:?}` missing when matching inductive types {ind:?}")]
    MatchNonExhaustive {
        ctors: Vec<&'a str>,
        ind: Rc<Ind<'a>>,
    },

    #[error("`self` used outside of inductive defination")]
    SelfOutsideInd,

    #[error("Undefined name / constructor: {name:?}")]
    Undefined {
        name: &'a str,
    },

    #[error("Unexpected type signature")]
    UnexpectedSig {
        name: &'a Name<'a, PI>,
    },

    #[error("Unbounded recursion")]
    UnboundedRecursion,

    #[error("Cannot cast with type: {ty:?}")]
    NonTyEqCast {
        ty: Rc<Type<'a>>,
    },

    #[error("Cannot transport with dependent function: {ty:?}")]
    DependentTransport {
        ty: Rc<Type<'a>>,
    },
}

type EvalResult<'a, T, PI> = Result<T, EvalError<'a, PI>>;

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
pub struct Evaluated<'a>(
    pub Value<'a>,
    pub Rc<Type<'a>>,
    pub Source,
);

impl<'a> Evaluated<'a> {
    pub fn create<PI>(v: Value<'a>, t: Rc<Type<'a>>, src: Source) -> EvalResult<'a, Self, PI> {
        // TODO: check if t is concrete
        t.assert_concrete()?;
        Ok(Self(v, t, src))
    }

    pub fn try_unwrap_as_type<PI>(self) -> EvalResult<'a, Rc<Type<'a>>, PI> {
        // TODO: return universe
        match self.1.as_ref() {
            Type::Type { .. } => {},
            _ => return Err(EvalError::TypeOnly{ actual: self.0, ty: self.1 })
        }
        self.0.try_unwrap_as_type()
    }

    pub fn substitute(&self, ident: ExtBindingIdent, with: &Value<'a>) -> Evaluated<'a> {
        Evaluated(
            self.0.substitute(ident, with),
            self.1.clone().substitute(ident, with),
            self.2.clone()
        )
    }
}

#[derive(Clone, Default)]
struct Scope<'a> {
    bindings: im::HashMap<&'a str, Evaluated<'a>>,
    ind_type: Option<Rc<Type<'a>>>,
}

impl<'a> Scope<'a> {
    pub fn bind(&self, name: &'a str, bounded: Evaluated<'a>) -> Self {
        Scope {
            bindings: self.bindings.update(name, bounded),
            ind_type: self.ind_type.clone(),
        }
    }

    pub fn inside_ind(&self, ty: Rc<Type<'a>>) -> Self {
        Scope {
            bindings: self.bindings.clone(),
            ind_type: Some(ty),
        }
    }
}

#[derive(Default)]
struct EvalCtx {
    ticket_gen: usize,
}

impl EvalCtx {
    // TODO: ensure hint and result type is always unifiable
    pub fn eval<'a, PI>(
        &mut self,
        expr: &'a Expr<'a, PI>,
        scope: &Scope<'a>,
        hint: Rc<Type<'a>>,
    ) -> EvalResult<'a, Evaluated<'a>, PI> {
        match &expr.inner {
            ExprInner::PartialType(inner) => {
                let inner_hint = hint.try_unify(Rc::new(Type::Type{ universe: None }))?;

                let inner = self.eval(inner.as_ref(), scope, inner_hint)?;
                let Evaluated(_, t, src) = inner.clone();
                let wrapped = Type::Partial(inner.try_unwrap_as_type()?);
                Evaluated::create(Value::Type(Rc::new(wrapped)), t, src)
            },
            ExprInner::Ind { sig, ctors } => {
                let interface = if let Some(sig) = sig {
                    let sig_val = self.eval_hint(sig.as_ref(), scope)?;
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
                    let ctor_type_value = self.eval_hint(&ctor.sig, &inner_scope)?;
                     
                    // TODO: check strict positivity and ctor yield type
                    // TODO: check ctor is inside the required universe
                    mapped_ctors.insert(ctor.name, ctor_type_value);
                }

                let ind = IndPtr::Complete(Rc::new(Ind { variants: mapped_ctors, sig: interface.clone() }));
                let self_val = Value::PartiallyIndexedInd { ind, indexes: im::Vector::new() };
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
                let input_type_val = self.eval_hint(input_type, scope)?;

                // Update scope before passing down for named dependent type variable
                let inner_scope_data;
                let mut inner_scope = scope;
                let arg_ident = self.count_external();
                if let Some(arg_name) = input_arg_name {
                    let bounded = Evaluated::create(Value::Pending(arg_ident), input_type_val.clone(), Source::External{ ident: arg_ident })?;
                    inner_scope_data = scope.bind(arg_name, bounded);
                    inner_scope = &inner_scope_data;
                }
                let ret_type_val = self.eval(f.output.as_ref(), inner_scope, Rc::new(Type::Type{ universe: None }))?.try_unwrap_as_type()?;
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
                    self.eval_hint(sig, scope)?.try_unify(arg_hint.clone())?
                } else {
                    arg_hint.clone()
                };

                // Introduce arg into scope
                let bounded = Evaluated::create(Value::Pending(arg_ident), arg_type.clone(), Source::External{ ident: arg_ident })?;
                let ret_scope = scope.bind(arg.name, bounded);

                // Evaluate ret type
                let ret_type= if let Some(sig) = ret.as_ref() {
                    self.eval_hint(sig, &ret_scope)?.try_unify(ret_hint.clone())?
                } else {
                    ret_hint.clone()
                };

                let self_type = Rc::new(Type::Fun {
                    arg: arg_type,
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
                let body_eval = self.eval(body.as_ref(), &inner_scope, ret_type)?;

                let self_val = Value::Lambda {
                    ident: arg_ident,
                    recursor: recursor_ident,
                    body: Box::new(body_eval),
                };
                // TODO: make self_type more specific using body_eval type
                Evaluated::create(self_val, self_type, Source::Constructed)
            },
            ExprInner::Binding { binding, rest } => {
                let binding_hint = if let Some(sig) = &binding.name.sig {
                    self.eval_hint(sig, scope)?
                } else {
                    Rc::new(Type::Hole)
                };
                let evaled = self.eval(&binding.val, scope, binding_hint)?;
                let inner_scope = scope.bind(binding.name.name, evaled);
                self.eval(rest.as_ref(), &inner_scope, hint)
            },
            ExprInner::Name(name) => {
                if name.sig.is_some() {
                    return Err(EvalError::UnexpectedSig{ name: name.as_ref() })
                }
                scope.bindings.get(name.name).cloned().ok_or(EvalError::Undefined{ name: name.name })
            },
            ExprInner::Ap(pair) => {
                let (f, arg) = pair.as_ref();
                // TODO: finer grind hints
                let f_eval = self.eval(f, scope, Rc::new(Type::Fun {
                    arg: Rc::new(Type::Hole),
                    ident: 0,
                    ret: Rc::new(Type::Hole),
                }))?;

                log::debug!("Applying function {:#?}", f_eval);
                let (arg_type, arg_ident, ret_type) = match f_eval.1.as_ref() {
                    Type::Fun { arg, ident, ret } => (arg, *ident, ret),
                    _ => unreachable!(),
                };
                let arg_eval = self.eval(arg, scope, arg_type.clone())?;
                // TODO: assert arg type concrete
                let ret_type = ret_type.clone().substitute(arg_ident, &arg_eval.0);
                let ret_type = ret_type.try_unify(hint)?;

                if let Source::Recursor { linked } = f_eval.2 {
                    match arg_eval.2 {
                        Source::Destructed { source } if source == linked => {},
                        _ => return Err(EvalError::UnboundedRecursion),
                    }
                }

                let val = Value::Ap {
                    fun: Box::new(f_eval.0),
                    arg: Box::new(arg_eval.0),
                }.progress();

                Evaluated::create(val, ret_type, Source::Constructed)
            },
            ExprInner::Match { matched, arms } => {
                // Build pendings
                let Evaluated(matched_val, matched_type, matched_src) = self.eval(matched.as_ref(), scope, Rc::new(Type::Hole))?;
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

                    let mut variant_sig = remaining.remove(arm.ctor).ok_or(EvalError::UndefinedCtor { ctor: arm.ctor, ind: ind.clone() })?;

                    let arity = variant_sig.arity();
                    if arity != arm.data.len() {
                        return Err(EvalError::MatchWrongArity { actual: arm.data.len(), ctor: arm.ctor, ind: ind.clone() })
                    }
                    if ind_arity + 1 != arm.ev.len() {
                        return Err(EvalError::MatchWrongEvidence { actual: arm.ev.len(), ctor: arm.ctor, ind: ind.clone() })
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

                                let bounded = Evaluated(val.clone(), arg.clone(), data_src.clone());
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

                    let constructed = Value::Inductive {
                        ind: ind.clone(),
                        ctor: arm.ctor,
                        data: data_idents.iter().cloned().map(|ident| Value::Pending(ident)).collect()
                    };
                    let mut matched_eq = Rc::new(Type::Eq {
                        within: matched_type.clone(),
                        lhs: matched_val.clone(),
                        rhs: constructed,
                    });
                    let mut ev_names = arm.ev.iter();
                    let full_ev_name = ev_names.next().unwrap();
                    if let Some(sig) = full_ev_name.sig.as_ref(){
                        matched_eq = self.eval_hint(sig, scope)?.try_unify(matched_eq)?;
                    }
                    let matched_ev = Evaluated(Value::Equality(matched_eq.clone()), matched_eq, Source::Constructed);
                    arm_scope = arm_scope.bind(full_ev_name.name, matched_ev);

                    let mut ind_sig = ind.sig.clone();
                    let mut index_pairs = ev_names.zip(indexes.iter().zip(arm_indexes.iter()));
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
                                    ev_ty = self.eval_hint(sig, scope)?.try_unify(ev_ty)?;
                                }
                                let ev = Evaluated(Value::Equality(ev_ty.clone()), ev_ty, Source::Constructed);
                                arm_scope = arm_scope.bind(ev_name.name, ev);

                                ind_sig = ret.clone().substitute(*orig, lhs);
                            },
                            Type::Type { .. } => break,
                            _ => unreachable!(),
                        }
                    }

                    let body = self.eval(&arm.body, &arm_scope, cur_hint.clone())?;
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
                let variants: EvalResult<'a, im::HashMap<_, _>, PI> = evaluated_arms.into_iter().map(|(name, (captures, eval))| {
                    cur_hint.clone().try_unify(eval.1)?;
                    Ok((name, Variant {
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
                let parent = self.eval(parent.as_ref(), scope, Rc::new(Type::Hole))?;
                let ind = match parent.0 {
                    Value::PartiallyIndexedInd { ind, indexes } if indexes.len() == 0 => {
                        match ind {
                            IndPtr::SelfInvoc => unreachable!(), // We should never get self out side of ind defination
                            IndPtr::Complete(ind) => ind,
                        }
                    },
                    _ => {
                        return Err(EvalError::NonIndCtor { actual: parent.0 });
                    },
                };

                let ctor_type = ind.variants.get(variant).ok_or(EvalError::UndefinedCtor { ctor: *variant, ind: ind.clone() })?;
                let ctor_type = ctor_type.clone().instantiate_self(ind.clone(), true);
                let ctor_type = ctor_type.try_unify(hint)?;

                Evaluated::create(
                    Value::Inductive {
                        ind,
                        ctor: *variant,
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
                    rhs: Value::Type(hint),
                }))?;
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
                let mut val = self.eval(orig, scope, lhs.clone())?;
                // Fixme: check lhs and orig type is the same
                if val.1 != lhs {
                    panic!("Cast eq sanity check failed");
                }

                val.1 = rhs;
                Ok(val)
            },
            ExprInner::Transport { eq, fun } => {
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
                }))?;

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
                    ret: within.clone(),
                }))?;

                // Asserts ret is non dependent on fun
                let (ident, ret) = match fun.1.as_ref() {
                    Type::Fun { ident, ret, .. } => (ident, ret),
                    _ => unreachable!()
                };
                
                let lhs_ap_ty = ret.clone().substitute(*ident, lhs);
                let rhs_ap_ty = ret.clone().substitute(*ident, rhs);
                if lhs_ap_ty != rhs_ap_ty {
                    return Err(EvalError::DependentTransport { ty: fun.1 })
                }

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
        }
    }

    pub fn eval_hint<'a, PI>(&mut self, sig: &'a Expr<'a, PI>, scope: &Scope<'a>) -> EvalResult<'a, Rc<Type<'a>>, PI> {
        let evaluated = self.eval(sig, scope, Rc::new(Type::Type{ universe: None }))?;
        // TODO: check is type
        evaluated.try_unwrap_as_type()
    }

    fn count_external<'a>(&mut self) -> ExtBindingIdent {
        self.ticket_gen += 1;
        self.ticket_gen
    }
}

pub fn eval_top<'a, PI>(
    expr: &'a Expr<'a, PI>,
) -> EvalResult<'a, Evaluated<'a>, PI> {
    let mut ctx = EvalCtx::default();
    let scope = Scope::default();
    let hint = Rc::new(Type::Hole);
    ctx.eval(expr, &scope, hint)
}