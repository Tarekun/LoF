use super::{
    saturation::saturate,
    type_check::{
        type_check_application, type_check_atomic, type_check_clause,
        type_check_equality, type_check_forall, type_check_not,
    },
};
use crate::{
    misc::Union::{self, L, R},
    runtime::program::Schedule,
    type_theory::{
        commons::type_check::type_check_variable,
        environment::Environment,
        interface::{Automatic, Kernel, TypeTheory},
        sup::{
            sup::{
                SupFormula::{Atom, Clause, Equality, ForAll, Not},
                SupTerm::{Application, Variable},
            },
            sup_utils::{kbo_terms, kbo_types},
        },
    },
};
use std::cmp::Ordering;

#[derive(Debug, Clone, PartialEq)]
pub enum SupTerm {
    /// var_name
    Variable(String),
    /// fun_name, [args]
    Application(String, Vec<SupTerm>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum SupFormula {
    /// pred_name, [args]
    Atom(String, Vec<SupTerm>),
    Equality(SupTerm, SupTerm),
    Not(Box<SupFormula>),
    /// literals
    Clause(Vec<SupFormula>),
    /// var_name, var_type, formula
    ForAll(String, Box<SupFormula>, Box<SupFormula>),
    // Exists(String, Box<SupFormula>),
}

pub struct Sup;
impl TypeTheory for Sup {
    type Term = SupTerm;
    type Type = SupFormula;
    type Exp = Union<SupTerm, SupFormula>;
    type Stm = ();

    fn default_environment() -> Environment<Sup> {
        Environment::with_defaults(vec![], vec![], vec![])
    }

    fn base_term_equality(
        term1: &SupTerm,
        term2: &SupTerm,
    ) -> Result<(), String> {
        if term1 == term2 {
            Ok(())
        } else {
            Err(format!("{:?} and {:?} are not equal", term1, term2))
        }
    }
    fn base_type_equality(
        type1: &SupFormula,
        type2: &SupFormula,
    ) -> Result<(), String> {
        if type1 == type2 {
            Ok(())
        } else {
            Err(format!("{:?} and {:?} are not equal", type1, type2))
        }
    }

    fn elaborate_expression(
        _: &crate::parser::api::Expression,
    ) -> Result<Self::Exp, String> {
        Err(
            "TODO: superposition calculus doesnt support elaboration currently"
                .to_string(),
        )
    }
    fn elaborate_statement(
        _: &crate::parser::api::Statement,
    ) -> Result<Schedule<Sup>, String> {
        Err(
            "TODO: superposition calculus doesnt support elaboration currently"
                .to_string(),
        )
    }
}

impl Kernel for Sup {
    /// Terms are variables x or f(t₁,…,tₙ).  Well‐formed iff
    /// 1) each variable is well-scoped (we allow any fresh variable here),
    /// 2) each function symbol is in the signature with the correct arity,
    /// 3) recursively its arguments are well‐formed.
    fn type_check_term(
        term: &Self::Term,
        env: &mut Environment<Sup>,
    ) -> Result<Self::Type, String> {
        match term {
            Variable(var_name) => type_check_variable::<Sup>(env, var_name),
            Application(fun_name, args) => {
                type_check_application(env, fun_name, args)
            }
        }
    }

    /// Formulas are well-formed iff:
    /// - `Atom(p, ts)`: `p` in predicate signature with correct arity, each `t` is a well-formed term;
    /// - `Neg(φ)`: φ is well-formed;
    /// - `ForAll(x, φ)` / `Exists(x, φ)`: φ is well-formed under `x` added to the bound-var set;
    /// - `Clause(lits)`: each literal is either an atomic formula or a negated atomic formula.
    fn type_check_type(
        φ: &Self::Type,
        environment: &mut Environment<Sup>,
    ) -> Result<Self::Type, String> {
        match φ {
            Atom(predicate, args) => {
                type_check_atomic(environment, predicate, args)
            }
            Equality(t1, t2) => type_check_equality(environment, t1, t2),
            Not(ψ) => type_check_not(environment, ψ),
            ForAll(var_name, var_type, ψ) => {
                type_check_forall(environment, var_name, var_type, ψ)
            }
            Clause(literals) => type_check_clause(environment, literals),
        }
    }

    fn type_check_expression(
        exp: &Union<SupTerm, SupFormula>,
        environment: &mut Environment<Sup>,
    ) -> Result<Self::Type, String> {
        match exp {
            L(term) => Sup::type_check_term(term, environment),
            R(typee) => Sup::type_check_type(typee, environment),
        }
    }

    fn type_check_stm(
        _stm: &Self::Stm,
        _env: &mut Environment<Sup>,
    ) -> Result<Self::Type, String> {
        Err("Statement type checking is not supported in SUP".to_string())
    }
}

impl Automatic for Sup {
    //TODO
    fn compare_terms(term1: &Self::Term, term2: &Self::Term) -> Ordering {
        kbo_terms(term1, term2)
    }
    //TODO
    fn compare_types(type1: &Self::Type, type2: &Self::Type) -> Ordering {
        kbo_types(type1, type2)
    }

    fn select(clause: &Self::Type) -> Result<Self::Type, String> {
        match clause {
            Clause(formulas) => {
                if formulas.len() == 0 {
                    Err(format!(
                        "Empty clause does not allow for selection of literals"
                    ))
                } else {
                    // TODO implement better selection other than pick the first
                    Ok(formulas[0].to_owned())
                }
            }
            _ => Err(format!(
                "Selection is defined on clause formulas only, not {:?}",
                clause
            )),
        }
    }

    fn proove(
        premises: Vec<SupFormula>,
        goal: SupFormula,
    ) -> Result<(), String> {
        let mut copy = premises.clone();
        copy.push(Not(Box::new(goal)));
        saturate(&copy)
    }
}
