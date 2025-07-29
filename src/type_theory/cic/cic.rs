use super::evaluation::{evaluate_statement, one_step_reduction};
use super::tactics::type_check_tactic;
use super::type_check::{
    type_check_abstraction, type_check_application, type_check_axiom,
    type_check_fun, type_check_let, type_check_product, type_check_sort,
    type_check_theorem, type_check_variable,
};
use super::unification::{cic_unification, solve_unification};
use crate::misc::Union::{self};
use crate::parser::api::{Expression, Statement, Tactic};
use crate::runtime::program::Schedule;
use crate::type_theory::cic::elaboration::{
    elaborate_expression, elaborate_statement,
};
use crate::type_theory::cic::type_check_inductive::{
    type_check_inductive, type_check_match,
};
use crate::type_theory::commons::evaluation::generic_term_normalization;
use crate::type_theory::environment::Environment;
use crate::type_theory::interface::{
    Interactive, Kernel, Reducer, Refiner, TypeTheory,
};
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
    Let(String, Option<CicTerm>, Box<CicTerm>),
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
}

pub struct Cic;
impl TypeTheory for Cic {
    type Term = CicTerm;
    type Type = CicTerm;
    type Stm = CicStm;
    type Exp = CicTerm;

    #[allow(non_snake_case)]
    fn default_environment() -> Environment<CicTerm, CicTerm> {
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
        common_unification_check(term1, term2)
    }
    fn base_type_equality(
        type1: &CicTerm,
        type2: &CicTerm,
    ) -> Result<(), String> {
        common_unification_check(type1, type2)
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
        environment: &mut Environment<CicTerm, CicTerm>,
    ) -> Result<CicTerm, String> {
        match term {
            CicTerm::Sort(sort_name) => type_check_sort(environment, sort_name),
            CicTerm::Variable(var_name, _) => {
                type_check_variable(environment, var_name)
            }
            CicTerm::Abstraction(var_name, var_type, body) => {
                type_check_abstraction(environment, var_name, var_type, body)
            }
            CicTerm::Product(var_name, var_type, body) => {
                type_check_product(environment, var_name, var_type, body)
            }
            CicTerm::Application(left, right) => {
                type_check_application(environment, left, right)
            }
            CicTerm::Match(matched_term, branches) => {
                type_check_match(environment, matched_term, branches)
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
        environment: &mut Environment<CicTerm, CicTerm>,
    ) -> Result<CicTerm, String> {
        debug!("Term-type checking of {:?}", term);
        Cic::type_check_expression(term, environment)
    }

    fn type_check_type(
        typee: &CicTerm,
        environment: &mut Environment<CicTerm, CicTerm>,
    ) -> Result<CicTerm, String> {
        debug!("Type-type checking of {:?}", typee);
        let type_sort = Cic::type_check_expression(typee, environment)?;
        match type_sort {
            CicTerm::Sort(_) => Ok(type_sort),
            _ => Err(format!("Expected sort term, found: {:?}", typee)),
        }
    }

    fn type_check_stm(
        stm: &CicStm,
        environment: &mut Environment<CicTerm, CicTerm>,
    ) -> Result<CicTerm, String> {
        debug!("Type-type checking of {:?}", stm);
        match stm {
            CicStm::Let(var_name, var_type, body) => {
                type_check_let(environment, var_name, var_type, body)
            }
            CicStm::Axiom(axiom_name, formula) => {
                type_check_axiom(environment, axiom_name, formula)
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
                type_check_fun(
                    environment,
                    fun_name,
                    args,
                    out_type,
                    body,
                    is_rec,
                )
            }
            CicStm::Theorem(theorem_name, formula, proof) => {
                type_check_theorem(environment, theorem_name, formula, proof)
            }
        }
    }
}

impl Refiner for Cic {
    fn terms_unify(
        environment: &mut Environment<CicTerm, CicTerm>,
        term1: &CicTerm,
        term2: &CicTerm,
    ) -> bool {
        match cic_unification(environment, term1, term2) {
            Ok(res) => res,
            //TODO: better handling
            Err(message) => panic!("{}", message),
        }
    }

    fn types_unify(
        environment: &mut Environment<CicTerm, CicTerm>,
        type1: &CicTerm,
        type2: &CicTerm,
    ) -> bool {
        match cic_unification(environment, type1, type2) {
            Ok(res) => res,
            //TODO: better handling
            Err(message) => panic!("{}", message),
        }
    }
}

impl Reducer for Cic {
    fn normalize_expression(
        environment: &mut Environment<CicTerm, CicTerm>,
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
        environment: &mut Environment<CicTerm, CicTerm>,
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
        environment: &mut Environment<CicTerm, CicTerm>,
        stm: &Self::Stm,
    ) -> () {
        debug!("Evaluating statement: {:?}", stm);
        evaluate_statement(environment, stm)
    }
}

impl Interactive for Cic {
    fn proof_hole() -> Self::Term {
        CicTerm::Sort("THIS_IS_A_PARTIAL_PROOF_HOLE".to_string())
    }
    fn empty_target() -> Self::Type {
        CicTerm::Sort("THIS_IS_AN_EMPTY_TERMINATION_PROOF_TARGET".to_string())
    }

    fn type_check_tactic(
        environment: &mut Environment<CicTerm, CicTerm>,
        tactic: &Tactic<Self::Exp>,
        target: &Self::Type,
        partial_proof: &Self::Term,
    ) -> Result<(Self::Type, Self::Term), String> {
        type_check_tactic(environment, tactic, target, partial_proof)
    }
}

fn common_unification_check(
    term1: &CicTerm,
    term2: &CicTerm,
) -> Result<(), String> {
    if solve_unification(vec![(term1.to_owned(), term2.to_owned())]).is_ok() {
        Ok(())
    } else {
        Err(format!("{:?} and {:?} do not unifiy", term1, term2))
    }
}
