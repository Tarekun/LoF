use super::type_check::{
    type_check_abstraction, type_check_arrow, type_check_atomic,
    type_check_forall, type_check_type_abstraction,
    type_check_type_application, type_check_variable,
};
use crate::error::LofError;
use crate::misc::Union::{self, L, R};
use crate::parser::api::{Expression, Statement};
use crate::runtime::program::Schedule;
use crate::type_theory::commons::type_check::{
    type_check_application, type_check_axiom, type_check_global,
};
use crate::type_theory::environment::Environment;
use crate::type_theory::f::f::FStm::{Axiom, Global};
use crate::type_theory::grammars::f::{
    FTerm::{
        self, Abstraction, Application, TypeAbstraction, TypeApplication,
        Variable,
    },
    FType::{self, Arrow, Atomic, Forall, MetaVariable},
};
use crate::type_theory::interface::{Kernel, TypeTheory};

/// Name of the only kind of System F, the kind of proper types
pub const TYPE_KIND: &str = "*";

#[derive(Debug, PartialEq, Clone)]
pub enum FStm {
    /// name, type: postulates `name` of type `type`. When `type` is the kind
    /// `*` it declares `name` as a base type
    Axiom(String, FType),
    /// var_name, var_type, definition_body
    Global(String, Option<FType>, FTerm),
}

pub struct SystemF;

impl TypeTheory for SystemF {
    type Term = FTerm;
    type Type = FType;
    type Stm = FStm;
    type Exp = Union<FTerm, FType>;

    fn default_environment() -> Environment<SystemF> {
        Environment::with_defaults(vec![], vec![], vec![])
    }

    fn base_term_equality(
        term1: &Self::Term,
        term2: &Self::Term,
    ) -> Result<(), LofError> {
        if *term1 == *term2 {
            Ok(())
        } else {
            Err(LofError::type_mismatch("equality check", term1, term2))
        }
    }

    /// Types are equal up to renaming of bound type variables
    fn base_type_equality(
        type1: &Self::Type,
        type2: &Self::Type,
    ) -> Result<(), LofError> {
        if type1.alpha_equivalent(type2) {
            Ok(())
        } else {
            Err(LofError::type_mismatch("equality check", type1, type2))
        }
    }

    fn elaborate_expression(_exp: &Expression) -> Result<Self::Exp, LofError> {
        Err(LofError::unsupported(
            "Elaboration of expressions is not implemented for System F yet",
        ))
    }

    fn elaborate_statement(
        _stm: &Statement,
    ) -> Result<Schedule<SystemF>, LofError> {
        Err(LofError::unsupported(
            "Elaboration of statements is not implemented for System F yet",
        ))
    }
}

impl Kernel for SystemF {
    fn type_check_expression(
        exp: &Union<FTerm, FType>,
        environment: &mut Environment<SystemF>,
    ) -> Result<FType, LofError> {
        match exp {
            L(term) => SystemF::type_check_term(term, environment),
            R(typee) => SystemF::type_check_type(typee, environment),
        }
    }

    /// Type checks `term` returning its type. There is no type inference,
    /// types are only compared for (α-)equality
    fn type_check_term(
        term: &FTerm,
        environment: &mut Environment<SystemF>,
    ) -> Result<FType, LofError> {
        match term {
            Variable(var_name) => type_check_variable(environment, var_name),
            Abstraction(var_name, var_type, body) => {
                type_check_abstraction(environment, var_name, var_type, body)
            }
            Application(fun, arg) => {
                type_check_application(environment, fun, arg, |fun_type| {
                    match fun_type {
                        Arrow(domain, codomain) => Some((
                            (**domain).to_owned(),
                            (**codomain).to_owned(),
                        )),
                        _ => None,
                    }
                })
            }
            TypeAbstraction(var_name, kind, body) => {
                type_check_type_abstraction(environment, var_name, kind, body)
            }
            TypeApplication(fun, type_arg) => {
                type_check_type_application(environment, fun, type_arg)
            }
        }
    }

    /// Checks the well formedness of `typee` returning its kind
    fn type_check_type(
        typee: &FType,
        environment: &mut Environment<SystemF>,
    ) -> Result<FType, LofError> {
        match typee {
            Atomic(type_name) => type_check_atomic(environment, type_name),
            MetaVariable(name) => Err(LofError::unsupported(format!(
                "Metavariable ?{}: type inference is not supported in System F yet",
                name
            ))),
            Arrow(domain, codomain) => {
                type_check_arrow(environment, domain, codomain)
            }
            Forall(var_name, kind, body) => {
                type_check_forall(environment, var_name, kind, body)
            }
        }
    }

    fn type_check_stm(
        stm: &FStm,
        environment: &mut Environment<SystemF>,
    ) -> Result<FType, LofError> {
        match stm {
            Axiom(name, typee) => {
                type_check_axiom::<SystemF>(environment, name, typee)
            }
            Global(var_name, opt_type, body) => type_check_global::<SystemF>(
                environment,
                var_name,
                opt_type,
                body,
            ),
        }
    }
}
