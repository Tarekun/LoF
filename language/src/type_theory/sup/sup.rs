use super::type_check::{
    type_check_application, type_check_atomic, type_check_clause,
    type_check_equality, type_check_forall, type_check_not,
};
use crate::{
    error::LofError,
    misc::Union::{self, L, R},
    runtime::program::Schedule,
    type_theory::{
        algorithms::saturation::saturate,
        commons::{type_check::type_check_variable, unification::Substitution},
        environment::Environment,
        grammars::cnf::{
            CnfFormula::{self, Atom, Clause, Equality, ForAll, Not},
            CnfTerm::{self, Application, Variable},
        },
        interface::{Automatic, Kernel, TypeTheory},
        sup::{
            freedom::{GivingClauseSignature, SelectionFunctionSignature},
            sup_utils::{kbo_terms, kbo_types},
        },
    },
};
use std::cmp::Ordering;

pub struct Sup;
impl TypeTheory for Sup {
    type Term = CnfTerm;
    type Type = CnfFormula;
    type Exp = Union<CnfTerm, CnfFormula>;
    type Stm = ();

    fn default_environment() -> Environment<Sup> {
        Environment::with_defaults(vec![], vec![], vec![])
    }

    fn base_term_equality(
        term1: &CnfTerm,
        term2: &CnfTerm,
    ) -> Result<(), LofError> {
        if term1 == term2 {
            Ok(())
        } else {
            Err(LofError::type_mismatch("equality check", term1, term2))
        }
    }
    fn base_type_equality(
        type1: &CnfFormula,
        type2: &CnfFormula,
    ) -> Result<(), LofError> {
        if type1 == type2 {
            Ok(())
        } else {
            Err(LofError::type_mismatch("equality check", type1, type2))
        }
    }

    fn elaborate_expression(
        _: &crate::parser::api::Expression,
    ) -> Result<Self::Exp, LofError> {
        Err(LofError::unsupported(
            "TODO: superposition calculus doesnt support elaboration currently",
        ))
    }
    fn elaborate_statement(
        _: &crate::parser::api::Statement,
    ) -> Result<Schedule<Sup>, LofError> {
        Err(LofError::unsupported(
            "TODO: superposition calculus doesnt support elaboration currently",
        ))
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
    ) -> Result<Self::Type, LofError> {
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
    ) -> Result<Self::Type, LofError> {
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
        exp: &Union<CnfTerm, CnfFormula>,
        environment: &mut Environment<Sup>,
    ) -> Result<Self::Type, LofError> {
        match exp {
            L(term) => Sup::type_check_term(term, environment),
            R(typee) => Sup::type_check_type(typee, environment),
        }
    }

    fn type_check_stm(
        _stm: &Self::Stm,
        _env: &mut Environment<Sup>,
    ) -> Result<Self::Type, LofError> {
        Err(LofError::unsupported(
            "Statement type checking is not supported in SUP",
        ))
    }
}

impl Automatic for Sup {
    fn compare_terms(term1: &CnfTerm, term2: &CnfTerm) -> Ordering {
        kbo_terms(term1, term2)
    }

    fn compare_types(type1: &Self::Type, type2: &Self::Type) -> Ordering {
        kbo_types(type1, type2)
    }

    fn saturate(
        saturation_set: &Vec<CnfFormula>,
        selection_fn: &SelectionFunctionSignature,
        giving_clause_fn: &GivingClauseSignature,
    ) -> Result<Substitution<CnfTerm>, LofError> {
        saturate(saturation_set, selection_fn, *giving_clause_fn)
    }
}
