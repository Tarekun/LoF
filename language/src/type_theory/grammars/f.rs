use crate::type_theory::{
    commons::evaluation::reduce_variable,
    environment::Environment,
    f::f::SystemF,
    grammars::{
        f::{
            FTerm::{
                Abstraction, Application, TypeAbstraction, TypeApplication,
                Variable,
            },
            FType::{Arrow, Atomic, Forall, MetaVariable},
        },
        traits::{NamedSubstitution, Reduction},
    },
};
use std::collections::HashSet;
use std::fmt;

#[derive(Clone, PartialEq)]
/// A term of System F: the simply typed λ-calculus extended with abstraction
/// over types (Λα:K. t) and application of terms to types (t [T])
pub enum FTerm {
    /// var_name
    Variable(String),
    /// var_name, var_type, body
    Abstraction(String, FType, Box<FTerm>),
    /// fun, arg
    Application(Box<FTerm>, Box<FTerm>),
    /// type_var_name, type_var_kind, body
    TypeAbstraction(String, Box<FType>, Box<FTerm>),
    /// term, type_arg
    TypeApplication(Box<FTerm>, FType),
}

#[derive(Clone, PartialEq)]
/// A type of System F
pub enum FType {
    /// Rigid type name: either a base type or a bound type variable,
    /// both resolved in the environment
    Atomic(String),
    /// Unification metavariable, reserved for type inference
    MetaVariable(String),
    /// domain, codomain
    Arrow(Box<FType>, Box<FType>),
    /// type_var_name, type_var_kind, body
    Forall(String, Box<FType>, Box<FType>),
}

//############################# DEBUG LOGS
impl fmt::Debug for FType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Atomic(name) => write!(f, "{}", name),
            MetaVariable(name) => write!(f, "?{}", name),
            Arrow(domain, codomain) => match **domain {
                Arrow(_, _) | Forall(_, _, _) => {
                    write!(f, "({:?}) → {:?}", domain, codomain)
                }
                _ => write!(f, "{:?} → {:?}", domain, codomain),
            },
            Forall(var_name, kind, body) => {
                write!(f, "∀{}:{:?}. {:?}", var_name, kind, body)
            }
        }
    }
}
impl fmt::Debug for FTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        /// Wraps binders and applications in parentheses
        fn atomic(term: &FTerm) -> String {
            match term {
                Variable(_) => format!("{:?}", term),
                _ => format!("({:?})", term),
            }
        }

        match self {
            Variable(name) => write!(f, "{}", name),
            Abstraction(var_name, var_type, body) => {
                write!(f, "λ{}:{:?}. {:?}", var_name, var_type, body)
            }
            Application(fun, arg) => match **fun {
                Application(_, _) | TypeApplication(_, _) => {
                    write!(f, "{:?} {}", fun, atomic(arg))
                }
                _ => write!(f, "{} {}", atomic(fun), atomic(arg)),
            },
            TypeAbstraction(var_name, kind, body) => {
                write!(f, "Λ{}:{:?}. {:?}", var_name, kind, body)
            }
            TypeApplication(fun, type_arg) => match **fun {
                Application(_, _) | TypeApplication(_, _) => {
                    write!(f, "{:?} [{:?}]", fun, type_arg)
                }
                _ => write!(f, "{} [{:?}]", atomic(fun), type_arg),
            },
        }
    }
}
//############################# DEBUG LOGS
//
//
//############################# LOOKUPS

/// Returns `name` primed enough times to be absent from `avoid`
fn fresh_name(name: &str, avoid: &HashSet<String>) -> String {
    let mut fresh = format!("{}'", name);
    while avoid.contains(&fresh) {
        fresh.push('\'');
    }
    fresh
}

impl FType {
    /// Returns the type names occurring free in `self`, base types included.
    /// Kind annotations are not inspected
    pub fn free_type_vars(&self) -> HashSet<String> {
        match self {
            Atomic(name) => HashSet::from([name.to_string()]),
            MetaVariable(_) => HashSet::new(),
            Arrow(domain, codomain) => {
                let mut free = domain.free_type_vars();
                free.extend(codomain.free_type_vars());
                free
            }
            // kinds never contain type variables
            Forall(var_name, _, body) => {
                let mut free = body.free_type_vars();
                free.remove(var_name);
                free
            }
        }
    }

    /// Returns `true` iff `self` and `other` are equal up to renaming of
    /// bound type variables
    pub fn alpha_equivalent(&self, other: &FType) -> bool {
        /// `bound` pairs the type variables bound on the left with the ones
        /// bound on the right, innermost last
        fn solver(
            left: &FType,
            right: &FType,
            bound: &mut Vec<(String, String)>,
        ) -> bool {
            match (left, right) {
                (Atomic(l), Atomic(r)) => {
                    let l_binder = bound.iter().rposition(|(bl, _)| bl == l);
                    let r_binder = bound.iter().rposition(|(_, br)| br == r);
                    match (l_binder, r_binder) {
                        (None, None) => l == r,
                        (l_binder, r_binder) => l_binder == r_binder,
                    }
                }
                (MetaVariable(l), MetaVariable(r)) => l == r,
                (Arrow(l_dom, l_cod), Arrow(r_dom, r_cod)) => {
                    solver(l_dom, r_dom, bound) && solver(l_cod, r_cod, bound)
                }
                (Forall(l, l_kind, l_body), Forall(r, r_kind, r_body)) => {
                    if !solver(l_kind, r_kind, bound) {
                        return false;
                    }
                    bound.push((l.to_string(), r.to_string()));
                    let equivalent = solver(l_body, r_body, bound);
                    bound.pop();
                    equivalent
                }
                _ => false,
            }
        }

        solver(self, other, &mut vec![])
    }
}

impl FTerm {
    /// Returns the term variables occurring free in `self`
    pub fn free_vars(&self) -> HashSet<String> {
        match self {
            Variable(name) => HashSet::from([name.to_string()]),
            Abstraction(var_name, _, body) => {
                let mut free = body.free_vars();
                free.remove(var_name);
                free
            }
            Application(fun, arg) => {
                let mut free = fun.free_vars();
                free.extend(arg.free_vars());
                free
            }
            TypeAbstraction(_, _, body) => body.free_vars(),
            TypeApplication(term, _) => term.free_vars(),
        }
    }

    /// Returns the type names occurring free in the annotations of `self`
    pub fn free_type_vars(&self) -> HashSet<String> {
        match self {
            Variable(_) => HashSet::new(),
            Abstraction(_, var_type, body) => {
                let mut free = var_type.free_type_vars();
                free.extend(body.free_type_vars());
                free
            }
            Application(fun, arg) => {
                let mut free = fun.free_type_vars();
                free.extend(arg.free_type_vars());
                free
            }
            // kinds never contain type variables
            TypeAbstraction(var_name, _, body) => {
                let mut free = body.free_type_vars();
                free.remove(var_name);
                free
            }
            TypeApplication(term, type_arg) => {
                let mut free = term.free_type_vars();
                free.extend(type_arg.free_type_vars());
                free
            }
        }
    }
}

//############################# LOOKUPS
//
//
//############################# EXPRESSIONS MANIPULATION

impl NamedSubstitution<FType> for FType {
    /// Capture avoiding substitution of the type variable `target_name`
    fn substitute_name(&self, target_name: &str, arg: &FType) -> FType {
        match self {
            Atomic(name) if name == target_name => arg.to_owned(),
            Atomic(_) | MetaVariable(_) => self.to_owned(),
            Arrow(domain, codomain) => Arrow(
                Box::new(domain.substitute_name(target_name, arg)),
                Box::new(codomain.substitute_name(target_name, arg)),
            ),
            Forall(var_name, kind, body) => {
                let kind = Box::new(kind.substitute_name(target_name, arg));
                // the name is overridden in `body`'s scope
                if var_name == target_name {
                    return Forall(var_name.to_string(), kind, body.to_owned());
                }

                let arg_free = arg.free_type_vars();
                let (var_name, body) = if arg_free.contains(var_name) {
                    let mut avoid = arg_free;
                    avoid.extend(body.free_type_vars());
                    avoid.insert(target_name.to_string());
                    let fresh = fresh_name(var_name, &avoid);
                    let body =
                        body.substitute_name(var_name, &Atomic(fresh.clone()));
                    (fresh, body)
                } else {
                    (var_name.to_string(), (**body).to_owned())
                };
                Forall(
                    var_name,
                    kind,
                    Box::new(body.substitute_name(target_name, arg)),
                )
            }
        }
    }
}

impl NamedSubstitution<FTerm> for FTerm {
    /// Capture avoiding substitution of the term variable `target_name`
    fn substitute_name(&self, target_name: &str, arg: &FTerm) -> FTerm {
        match self {
            Variable(name) if name == target_name => arg.to_owned(),
            Variable(_) => self.to_owned(),
            Abstraction(var_name, var_type, body) => {
                // the name is overridden in `body`'s scope
                if var_name == target_name {
                    return self.to_owned();
                }

                let arg_free = arg.free_vars();
                let (var_name, body) = if arg_free.contains(var_name) {
                    let mut avoid = arg_free;
                    avoid.extend(body.free_vars());
                    avoid.insert(target_name.to_string());
                    let fresh = fresh_name(var_name, &avoid);
                    let body = body
                        .substitute_name(var_name, &Variable(fresh.clone()));
                    (fresh, body)
                } else {
                    (var_name.to_string(), (**body).to_owned())
                };
                Abstraction(
                    var_name,
                    var_type.to_owned(),
                    Box::new(body.substitute_name(target_name, arg)),
                )
            }
            Application(fun, fun_arg) => Application(
                Box::new(fun.substitute_name(target_name, arg)),
                Box::new(fun_arg.substitute_name(target_name, arg)),
            ),
            TypeAbstraction(var_name, kind, body) => {
                // `arg` mustn't have its type names captured by the binder
                let arg_free = arg.free_type_vars();
                let (var_name, body) = if arg_free.contains(var_name) {
                    let mut avoid = arg_free;
                    avoid.extend(body.free_type_vars());
                    let fresh = fresh_name(var_name, &avoid);
                    let body =
                        body.substitute_name(var_name, &Atomic(fresh.clone()));
                    (fresh, body)
                } else {
                    (var_name.to_string(), (**body).to_owned())
                };
                TypeAbstraction(
                    var_name,
                    kind.to_owned(),
                    Box::new(body.substitute_name(target_name, arg)),
                )
            }
            TypeApplication(term, type_arg) => TypeApplication(
                Box::new(term.substitute_name(target_name, arg)),
                type_arg.to_owned(),
            ),
        }
    }
}

impl NamedSubstitution<FType> for FTerm {
    /// Capture avoiding substitution of the type variable `target_name`
    /// in every type annotation of `self`
    fn substitute_name(&self, target_name: &str, arg: &FType) -> FTerm {
        match self {
            Variable(_) => self.to_owned(),
            Abstraction(var_name, var_type, body) => Abstraction(
                var_name.to_string(),
                var_type.substitute_name(target_name, arg),
                Box::new(body.substitute_name(target_name, arg)),
            ),
            Application(fun, fun_arg) => Application(
                Box::new(fun.substitute_name(target_name, arg)),
                Box::new(fun_arg.substitute_name(target_name, arg)),
            ),
            TypeAbstraction(var_name, kind, body) => {
                let kind = Box::new(kind.substitute_name(target_name, arg));
                // the name is overridden in `body`'s scope
                if var_name == target_name {
                    return TypeAbstraction(
                        var_name.to_string(),
                        kind,
                        body.to_owned(),
                    );
                }

                let arg_free = arg.free_type_vars();
                let (var_name, body) = if arg_free.contains(var_name) {
                    let mut avoid = arg_free;
                    avoid.extend(body.free_type_vars());
                    avoid.insert(target_name.to_string());
                    let fresh = fresh_name(var_name, &avoid);
                    let body: FTerm =
                        body.substitute_name(var_name, &Atomic(fresh.clone()));
                    (fresh, body)
                } else {
                    (var_name.to_string(), (**body).to_owned())
                };
                TypeAbstraction(
                    var_name,
                    kind,
                    Box::new(body.substitute_name(target_name, arg)),
                )
            }
            TypeApplication(term, type_arg) => TypeApplication(
                Box::new(term.substitute_name(target_name, arg)),
                type_arg.substitute_name(target_name, arg),
            ),
        }
    }
}

//############################# EXPRESSIONS MANIPULATION
//
//
//############################# REDUCTION

impl Reduction<SystemF> for FTerm {
    /// Performs one step of normal order (leftmost outermost) βδ-reduction,
    /// also reducing under binders. Type level β-reduction contracts
    /// (Λα:K. t) [T] to t[T/α]
    fn step(&self, env: &Environment<SystemF>) -> FTerm {
        /// `bound` holds the term variables bound by the enclosing
        /// abstractions, which mustn't be δ-reduced to globals of the same name
        fn solver(
            term: &FTerm,
            env: &Environment<SystemF>,
            bound: &mut Vec<String>,
        ) -> FTerm {
            match term {
                Variable(name) if bound.contains(name) => term.to_owned(),
                Variable(name) => reduce_variable::<SystemF>(env, name, term),
                Application(fun, arg) => match &**fun {
                    // β-reduction
                    Abstraction(var_name, _, body) => {
                        body.substitute_name(var_name, &**arg)
                    }
                    _ => {
                        let fun_reduced = solver(fun, env, bound);
                        if fun_reduced != **fun {
                            Application(Box::new(fun_reduced), arg.to_owned())
                        } else {
                            Application(
                                fun.to_owned(),
                                Box::new(solver(arg, env, bound)),
                            )
                        }
                    }
                },
                TypeApplication(fun, type_arg) => match &**fun {
                    // type level β-reduction
                    TypeAbstraction(var_name, _, body) => {
                        body.substitute_name(var_name, type_arg)
                    }
                    _ => TypeApplication(
                        Box::new(solver(fun, env, bound)),
                        type_arg.to_owned(),
                    ),
                },
                Abstraction(var_name, var_type, body) => {
                    bound.push(var_name.to_string());
                    let body = solver(body, env, bound);
                    bound.pop();
                    Abstraction(
                        var_name.to_string(),
                        var_type.to_owned(),
                        Box::new(body),
                    )
                }
                TypeAbstraction(var_name, kind, body) => TypeAbstraction(
                    var_name.to_string(),
                    kind.to_owned(),
                    Box::new(solver(body, env, bound)),
                ),
            }
        }

        solver(self, env, &mut vec![])
    }
}

//############################# REDUCTION

#[cfg(test)]
#[path = "../../tests/type_theory/grammars/f.rs"]
mod tests;
