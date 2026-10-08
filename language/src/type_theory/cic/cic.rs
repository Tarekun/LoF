use super::evaluation::{evaluate_statement, one_step_reduction};
use super::tactics::type_check_tactic;
use super::type_check::{cic_convertible, type_check_sort};
use crate::error::LofError;
use crate::parser::api::{Expression, LofStatement, Statement, Tactic};
use crate::runtime::program::Schedule;
use crate::type_theory::cic::cic::CicTerm::Product;
use crate::type_theory::cic::cic_utils::{
    alpha_equivalent, close_term, make_multiarg_fun_type, open_term,
    substitute_and_lift, substitute_local,
};
use crate::type_theory::cic::elaboration::{
    elaborate_expression, elaborate_statement,
};
use crate::type_theory::cic::type_check::{
    type_check_inductive, type_check_match,
};
use crate::type_theory::commons::evaluation::generic_term_normalization;
use crate::type_theory::commons::type_check::{
    ln_type_check_abstraction, ln_type_check_application,
    ln_type_check_fo_universal, ln_type_check_function, ln_type_check_let,
    type_check_axiom, type_check_global, type_check_theorem,
    type_check_variable,
};
use crate::type_theory::environment::Environment;
use crate::type_theory::grammars::traits::{
    AlphaEquiv, LocallyNameless, Reduction, ReductionEq, SyntacticalEq,
};
use crate::type_theory::interface::{
    Interactive, Kernel, Reducer, Stm, TypeTheory,
};
use tracing::debug;

pub static FIRST_INDEX: i32 = 0;
pub static GLOBAL_INDEX: i32 = -1;
pub static PLACEHOLDER_DBI: i32 = -2;

#[derive(PartialEq, Clone)]
pub enum NameKind {
    /// De Bruijn index
    Bound(i32),
    /// locally free name from a binder descended under,
    /// whose type is in the context
    // TODO: keyed by name only, not a fresh atom id. Two different binders
    // opened under the same name (e.g. a function parameter and a pattern
    // variable that happen to share a name) collapse onto the same `Local`
    // and become indistinguishable to `structurally_equal`/the context.
    // Should carry a generated atom id instead (registered in the context,
    // stripped again for display) to make each `open` truly fresh.
    Local(),
    /// global irreducable constant
    Const(),
}
#[derive(PartialEq, Clone)]
pub enum CicTerm {
    /// (sort name)
    Sort(String),
    /// (var name, name kind)
    Variable(String, NameKind),
    /// (var name, var type, body)
    Abstraction(String, Box<CicTerm>, Box<CicTerm>), //add bodytype?
    /// (var name, var type, body)
    Product(String, Box<CicTerm>, Box<CicTerm>), //add bodytype?
    /// (function, argument)
    Application(Box<CicTerm>, Box<CicTerm>),
    /// (matched_term, [ branch: (pattern, body) ])
    Match(Box<CicTerm>, Vec<(CicTerm, CicTerm)>),
    /// (var_name, var_type, body, scope)
    Let(String, Box<Option<CicTerm>>, Box<CicTerm>, Box<CicTerm>),
    /// index
    Meta(i32),
}
impl Reduction<Cic> for CicTerm {
    fn step(&self, env: &Environment<Cic>) -> CicTerm {
        one_step_reduction(env, self)
    }
}
impl SyntacticalEq for CicTerm {
    fn syntactically_equal(&self, other: &Self) -> bool {
        *self == *other
    }
}
impl AlphaEquiv for CicTerm {
    fn alpha_equivalent(&self, other: &Self) -> bool {
        alpha_equivalent(self, other, false)
    }
}
impl LocallyNameless for CicTerm {
    fn open(&self, name: &str) -> Self {
        open_term(self, name)
    }
    fn close(&self, name: &str) -> Self {
        close_term(self, name)
    }
}
impl ReductionEq<Cic> for CicTerm {
    /// Normal forms are compared up to α-equivalence
    fn equal_up_to_reduction(
        &self,
        other: &Self,
        env: &Environment<Cic>,
    ) -> bool {
        let self_reduced = self.reduce_to_normal(env);
        let other_reduced = other.reduce_to_normal(env);
        self_reduced.alpha_equivalent(&other_reduced)
    }
}

pub struct Cic;

impl TypeTheory for Cic {
    type Term = CicTerm;
    type Type = CicTerm;
    type Exp = CicTerm;

    #[allow(non_snake_case)]
    fn default_environment() -> Environment<Cic> {
        let TYPE = CicTerm::Sort("TYPE".to_string());
        let axioms: Vec<(&str, &CicTerm)> =
            vec![("TYPE", &TYPE), ("PROP", &TYPE)];

        Environment::with_defaults(axioms, Vec::default(), vec![])
    }

    fn term_judgemental_equality(
        env: &Environment<Cic>,
        term1: &CicTerm,
        term2: &CicTerm,
    ) -> Result<(), LofError> {
        if term1.equal_up_to_reduction(term2, env) {
            Ok(())
        } else {
            Err(LofError::custom(format!(
                "{:?} and {:?} are not equal",
                term1, term2
            )))
        }
    }
    fn type_judgemental_equality(
        env: &Environment<Cic>,
        type1: &CicTerm,
        type2: &CicTerm,
    ) -> Result<(), LofError> {
        cic_convertible(env, type2, type1)
    }

    fn elaborate_expression(exp: &Expression) -> Result<CicTerm, LofError> {
        Ok(elaborate_expression(exp))
    }
    fn elaborate_statement(
        stm: &LofStatement,
    ) -> Result<Schedule<Cic>, LofError> {
        elaborate_statement(stm)
    }
}

impl Kernel for Cic {
    fn type_check_expression(
        term: &CicTerm,
        environment: &mut Environment<Cic>,
    ) -> Result<CicTerm, LofError> {
        match term {
            CicTerm::Sort(sort_name) => type_check_sort(environment, sort_name),
            CicTerm::Variable(var_name, _) => {
                type_check_variable::<Cic>(environment, var_name)
            }
            CicTerm::Abstraction(var_name, var_type, body) => {
                ln_type_check_abstraction::<Cic, _>(
                    environment,
                    var_name,
                    var_type,
                    body,
                    |var_name, var_type, body_type| {
                        Product(
                            var_name,
                            Box::new(var_type),
                            Box::new(body_type),
                        )
                    },
                )
            }
            CicTerm::Product(var_name, var_type, body) => {
                ln_type_check_fo_universal::<Cic>(
                    environment,
                    var_name,
                    var_type,
                    body,
                )
            }
            CicTerm::Application(left, right) => ln_type_check_application(
                environment,
                left,
                right,
                |cic_type| match cic_type {
                    Product(var_name, domain, codomain) => Some((
                        var_name.to_string(),
                        (**domain).to_owned(),
                        (**codomain).to_owned(),
                    )),
                    _ => None,
                },
                Cic::normalize_term,
                Cic::substitute,
            ),
            CicTerm::Match(matched_term, branches) => {
                type_check_match(environment, matched_term, branches)
            }
            CicTerm::Let(var_name, var_type, body, scope) => {
                ln_type_check_let(
                    environment,
                    var_name,
                    var_type,
                    body,
                    scope,
                    substitute_local,
                )
            }
            CicTerm::Meta(index) => Err(LofError::custom(format!(
                "Unresolved metavariable ?[{}] reached the kernel: holes have to be solved by the refiner",
                index
            ))),
        }
    }

    fn type_check_term(
        term: &CicTerm,
        environment: &mut Environment<Cic>,
    ) -> Result<CicTerm, LofError> {
        debug!("Term-type checking of {:?}", term);
        Cic::type_check_expression(term, environment)
    }

    fn type_check_type(
        typee: &CicTerm,
        environment: &mut Environment<Cic>,
    ) -> Result<CicTerm, LofError> {
        debug!("Type-type checking of {:?}", typee);
        let type_sort = Cic::type_check_expression(typee, environment)?;
        match type_sort {
            CicTerm::Sort(_) => Ok(type_sort),
            _ => {
                Err(LofError::type_mismatch("type checking", &"a sort", typee))
            }
        }
    }

    fn type_check_stm(
        stm: &Stm<Cic>,
        environment: &mut Environment<Cic>,
    ) -> Result<CicTerm, LofError> {
        debug!("Type-type checking of {:?}", stm);
        match stm {
            Statement::Global(var_name, opt_type, body) => {
                type_check_global::<Cic>(environment, var_name, opt_type, body)
            }
            Statement::Axiom(axiom_name, formula) => {
                type_check_axiom::<Cic>(environment, axiom_name, formula)
            }
            Statement::Inductive(type_name, params, ariety, constructors) => {
                type_check_inductive(
                    environment,
                    type_name,
                    params,
                    ariety,
                    constructors,
                )
            }
            Statement::Fun(fun_name, args, out_type, body, is_rec) => {
                ln_type_check_function::<Cic, _, _>(
                    environment,
                    fun_name,
                    args,
                    out_type,
                    body,
                    is_rec,
                    |args, out_type| make_multiarg_fun_type(&args, &out_type),
                    |(var_name, var_type), body| {
                        CicTerm::Abstraction(
                            var_name,
                            Box::new(var_type),
                            Box::new(body),
                        )
                    },
                )
            }
            Statement::Theorem(theorem_name, formula, proof) => {
                type_check_theorem::<Cic>(
                    environment,
                    theorem_name,
                    formula,
                    proof,
                )
            }
            // Statement::Auto(formula) => {
            //     type_check_auto::<Cic>(environment, formula)
            // }
            _ => Err(LofError::unsupported_construct("CIC", stm)),
        }
    }
}

impl Reducer for Cic {
    fn substitute(term: &CicTerm, var_name: &str, body: &CicTerm) -> CicTerm {
        substitute_and_lift(term, var_name, body)
    }

    fn normalize_expression(
        environment: &Environment<Cic>,
        term: &CicTerm,
    ) -> CicTerm {
        debug!("Normalizing term: {:?}", term);
        generic_term_normalization::<Cic, _>(
            environment,
            term,
            one_step_reduction,
        )
    }

    fn normalize_term(
        environment: &Environment<Cic>,
        term: &CicTerm,
    ) -> CicTerm {
        debug!("Normalizing term: {:?}", term);
        generic_term_normalization::<Cic, _>(
            environment,
            term,
            one_step_reduction,
        )
    }

    fn evaluate_statement(
        environment: &mut Environment<Cic>,
        stm: &Stm<Cic>,
    ) -> Result<(), LofError> {
        debug!("Evaluating statement: {:?}", stm);
        evaluate_statement(environment, stm)
    }
}

impl Interactive for Cic {
    fn proof_hole() -> CicTerm {
        CicTerm::Sort("THIS_IS_A_PARTIAL_PROOF_HOLE".to_string())
    }
    fn empty_target() -> CicTerm {
        CicTerm::Sort("THIS_IS_AN_EMPTY_TERMINATION_PROOF_TARGET".to_string())
    }

    fn type_check_tactic(
        environment: &mut Environment<Cic>,
        tactic: &Tactic<CicTerm, CicTerm>,
        target: &CicTerm,
        partial_proof: &CicTerm,
    ) -> Result<(CicTerm, Vec<CicTerm>), LofError> {
        type_check_tactic(environment, tactic, target, partial_proof)
    }
}
