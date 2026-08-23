use super::evaluation::{evaluate_statement, one_step_reduction};
use super::tactics::type_check_tactic;
use super::type_check::type_check_sort;
use super::unification::{
    cic_so_unification, cic_unification, solve_unification,
};
use crate::misc::Union::{self};
use crate::parser::api::{Expression, Statement, Tactic};
use crate::runtime::program::Schedule;
use crate::type_theory::cic::cic::CicTerm::{Application, Meta, Product};
use crate::type_theory::cic::cic_utils::{
    make_multiarg_fun_type, substitute, substitute_meta,
};
use crate::type_theory::cic::elaboration::{
    elaborate_expression, elaborate_statement,
};
use crate::type_theory::cic::type_check::{
    type_check_inductive, type_check_match,
};
use crate::type_theory::cic::unification::{
    cic_apply_unifier, cic_collect_unifications, cic_solve_unifications,
};
use crate::type_theory::commons::evaluation::generic_term_normalization;
use crate::type_theory::commons::type_check::{
    i_type_check_abstraction, i_type_check_application, type_check_axiom,
    type_check_fo_universal, type_check_function, type_check_global,
    type_check_let, type_check_theorem, type_check_variable,
};
use crate::type_theory::commons::unification::Substitution;
use crate::type_theory::environment::{Constraint, Environment};
use crate::type_theory::interface::{
    Interactive, Kernel, Reducer, Refiner, TypeInference, TypeTheory,
};
use std::collections::HashMap;
use tracing::debug;

pub static FIRST_INDEX: i32 = 0;
pub static GLOBAL_INDEX: i32 = -1;
pub static PLACEHOLDER_DBI: i32 = -2;

#[derive(PartialEq, Clone)]
pub enum CicTerm {
    /// (sort name)
    Sort(String),
    /// (var name, De Bruijn index)
    Variable(String, i32),
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
#[derive(Debug, PartialEq, Clone)]
pub enum CicStm {
    /// axiom_name, formula
    Axiom(String, Box<CicTerm>),
    /// theorem_name, formula, proof
    Theorem(String, Box<CicTerm>, Union<CicTerm, Vec<Tactic<CicTerm>>>),
    /// (var_name, var_type, definition_body)
    Global(String, Option<CicTerm>, Box<CicTerm>),
    /// (fun_name, args, out_type, body, is_rec)
    Fun(
        String,
        Vec<(String, CicTerm)>,
        Box<CicTerm>,
        Box<CicTerm>,
        bool,
    ),
    /// type_name, [(param_name : param_type)], ariety, [( constr_name, constr_type )]
    InductiveDef(
        String,
        Vec<(String, CicTerm)>,
        Box<CicTerm>,
        Vec<(String, CicTerm)>,
    ),
    // Auto(CicTerm),
}

pub struct Cic;
impl TypeTheory for Cic {
    type Term = CicTerm;
    type Type = CicTerm;
    type Stm = CicStm;
    type Exp = CicTerm;

    #[allow(non_snake_case)]
    fn default_environment() -> Environment<Cic> {
        let TYPE = CicTerm::Sort("TYPE".to_string());
        let axioms: Vec<(&str, &CicTerm)> =
            vec![("TYPE", &TYPE), ("PROP", &TYPE)];

        Environment::with_defaults(axioms, Vec::default(), vec![])
    }

    // uses unification, implementing structural equality under some
    // metavariable substitution
    fn base_term_equality(
        term1: &CicTerm,
        term2: &CicTerm,
    ) -> Result<(), String> {
        // tbh im not really sure these specific functions should use unification instead of syntactic equality
        let _ = cic_so_unification(term1, term2)?;
        Ok(())
    }
    fn base_type_equality(
        type1: &CicTerm,
        type2: &CicTerm,
    ) -> Result<(), String> {
        // tbh im not really sure these specific functions should use unification instead of syntactic equality
        let _ = cic_so_unification(type1, type2)?;
        Ok(())
    }

    fn elaborate_expression(exp: &Expression) -> Result<CicTerm, String> {
        Ok(elaborate_expression(exp))
    }
    fn elaborate_statement(stm: &Statement) -> Result<Schedule<Cic>, String> {
        elaborate_statement(stm)
    }
}

impl Kernel for Cic {
    fn type_check_expression(
        term: &CicTerm,
        environment: &mut Environment<Cic>,
    ) -> Result<CicTerm, String> {
        match term {
            CicTerm::Sort(sort_name) => type_check_sort(environment, sort_name),
            CicTerm::Variable(var_name, _) => {
                type_check_variable::<Cic>(environment, var_name)
            }
            CicTerm::Abstraction(var_name, var_type, body) => {
                i_type_check_abstraction::<Cic, _>(
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
                type_check_fo_universal::<Cic>(
                    environment,
                    var_name,
                    var_type,
                    body,
                )
            }
            CicTerm::Application(left, right) => i_type_check_application(
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
                |l, r| {
                    Application(Box::new(l.to_owned()), Box::new(r.to_owned()))
                },
                Cic::substitute,
            ),
            CicTerm::Match(matched_term, branches) => {
                type_check_match(environment, matched_term, branches)
            }
            CicTerm::Let(var_name, var_type, body, scope) => {
                type_check_let(environment, var_name, var_type, body, scope)
            }
            CicTerm::Meta(index) => {
                //TODO handle this properly
                // Err(format!("MetaVariables should never appear as type checkable terms. Received ?[{}]", index))
                Ok(CicTerm::Sort("TYPE".to_string()))
            }
        }
    }

    fn type_check_term(
        term: &CicTerm,
        environment: &mut Environment<Cic>,
    ) -> Result<CicTerm, String> {
        debug!("Term-type checking of {:?}", term);
        Cic::type_check_expression(term, environment)
    }

    fn type_check_type(
        typee: &CicTerm,
        environment: &mut Environment<Cic>,
    ) -> Result<CicTerm, String> {
        debug!("Type-type checking of {:?}", typee);
        let type_sort = Cic::type_check_expression(typee, environment)?;
        match type_sort {
            CicTerm::Sort(_) => Ok(type_sort),
            _ => Err(format!("Expected a sort, found: {:?}", typee)),
        }
    }

    fn type_check_stm(
        stm: &CicStm,
        environment: &mut Environment<Cic>,
    ) -> Result<CicTerm, String> {
        debug!("Type-type checking of {:?}", stm);
        match stm {
            CicStm::Global(var_name, opt_type, body) => {
                type_check_global::<Cic>(environment, var_name, opt_type, body)
            }
            CicStm::Axiom(axiom_name, formula) => {
                type_check_axiom::<Cic>(environment, axiom_name, formula)
            }
            CicStm::InductiveDef(type_name, params, ariety, constructors) => {
                type_check_inductive(
                    environment,
                    type_name,
                    params,
                    ariety,
                    constructors,
                )
            }
            CicStm::Fun(fun_name, args, out_type, body, is_rec) => {
                type_check_function::<Cic, _, _>(
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
            CicStm::Theorem(theorem_name, formula, proof) => {
                type_check_theorem::<Cic>(
                    environment,
                    theorem_name,
                    formula,
                    proof,
                )
            } // CicStm::Auto(formula) => {
              //     type_check_auto::<Cic>(environment, formula)
              // }
        }
    }
}

impl TypeInference for Cic {
    fn type_unify(
        type1: &CicTerm,
        type2: &CicTerm,
    ) -> Result<Substitution<CicTerm>, String> {
        cic_so_unification(type1, type2)
    }
    fn apply_so_substitution(
        typ: &CicTerm,
        substitution: &Substitution<CicTerm>,
    ) -> CicTerm {
        let mut solved_exp = typ.to_owned();
        for index in substitution.names() {
            solved_exp = substitute_meta(
                &solved_exp,
                &index.parse().unwrap(),
                substitution.get(index).unwrap(),
            )
        }
        solved_exp
    }
}

impl Refiner for Cic {
    fn solve_unifications(
        constraints: Vec<(CicTerm, CicTerm)>,
        environment: &mut Environment<Cic>,
    ) -> Result<Substitution<CicTerm>, String>
    where
        Self: Sized,
    {
        cic_solve_unifications(constraints, environment)
    }
    fn term_collect_unifications(
        exp: &CicTerm,
        environment: &mut Environment<Cic>,
    ) -> Result<Vec<(CicTerm, CicTerm)>, String> {
        cic_collect_unifications(exp, environment)
    }
    fn type_collect_unifications(
        exp: &CicTerm,
        environment: &mut Environment<Cic>,
    ) -> Result<Vec<(CicTerm, CicTerm)>, String> {
        cic_collect_unifications(exp, environment)
    }
    fn term_apply_unifier(
        exp: &CicTerm,
        substitution: &Substitution<CicTerm>,
    ) -> CicTerm {
        cic_apply_unifier(exp, substitution)
    }
    fn type_apply_unifier(
        exp: &CicTerm,
        substitution: &Substitution<CicTerm>,
    ) -> CicTerm {
        cic_apply_unifier(exp, substitution)
    }
    fn needs_refinement(exp: &CicTerm) -> bool {
        true
    }

    ///////////////////////////////////////////////////////////

    ///////////////////////////////////////////////////////////
    fn solve_unification(
        constraints: Vec<Constraint<Cic>>,
    ) -> Result<HashMap<i32, CicTerm>, String> {
        solve_unification(constraints)
    }

    fn meta_index(meta: &CicTerm) -> Option<i32> {
        match meta {
            Meta(index) => Some(index.to_owned()),
            _ => None,
        }
    }

    fn term_solve_metas(
        exp: &CicTerm,
        substitution: &HashMap<i32, CicTerm>,
    ) -> CicTerm {
        let mut solved_exp = exp.to_owned();
        for index in substitution.keys() {
            solved_exp = substitute_meta(
                &solved_exp,
                index,
                substitution.get(index).unwrap(),
            )
        }
        solved_exp
    }
    fn type_solve_metas(
        exp: &CicTerm,
        substitution: &HashMap<i32, CicTerm>,
    ) -> CicTerm {
        let mut solved_exp = exp.to_owned();
        for index in substitution.keys() {
            solved_exp = substitute_meta(
                &solved_exp,
                index,
                substitution.get(index).unwrap(),
            )
        }
        solved_exp
    }

    fn terms_unify(
        environment: &mut Environment<Cic>,
        term1: &CicTerm,
        term2: &CicTerm,
    ) -> bool {
        cic_unification(environment, term1, term2).is_ok()
    }

    fn types_unify(
        environment: &mut Environment<Cic>,
        type1: &CicTerm,
        type2: &CicTerm,
    ) -> bool {
        cic_unification(environment, type1, type2).is_ok()
    }
}

impl Reducer for Cic {
    fn substitute(term: &CicTerm, var_name: &str, body: &CicTerm) -> CicTerm {
        substitute(term, var_name, body)
    }

    fn normalize_expression(
        environment: &mut Environment<Cic>,
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
        environment: &mut Environment<Cic>,
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
        stm: &Self::Stm,
    ) -> Result<(), String> {
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
        tactic: &Tactic<CicTerm>,
        target: &CicTerm,
        partial_proof: &CicTerm,
    ) -> Result<(CicTerm, Vec<CicTerm>), String> {
        type_check_tactic(environment, tactic, target, partial_proof)
    }
}
