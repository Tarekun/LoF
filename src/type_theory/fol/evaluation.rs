use super::fol::FolStm::{Axiom, Fun, Let, Theorem};
use super::fol::FolTerm::Variable;
use super::fol_utils::make_multiarg_fun_type;
use crate::type_theory::commons::evaluation::generic_evaluate_fun;
use crate::{
    misc::Union,
    parser::api::Tactic,
    type_theory::{
        commons::evaluation::{
            generic_evaluate_axiom, generic_evaluate_let,
            generic_evaluate_theorem, generic_reduce_variable,
        },
        environment::Environment,
    },
};

use super::fol::{Fol, FolFormula, FolStm, FolTerm};

//########################### TERM βδ-REDUCTION
pub fn one_step_reduction(
    environment: &mut Environment<Fol>,
    term: &FolTerm,
) -> FolTerm {
    match term {
        Variable(var_name) => reduce_variable(environment, var_name, term),
        // Application(left, right) => {
        //     reduce_application(environment, left, right)
        // }
        _ => term.clone(),
    }
}
//
//
fn reduce_variable(
    environment: &Environment<Fol>,
    var_name: &str,
    og_term: &FolTerm,
) -> FolTerm {
    generic_reduce_variable::<Fol>(environment, var_name, og_term)
}

//########################### TERM βδ-REDUCTION

//########################### STATEMENTS EXECUTION
pub fn evaluate_statement(
    environment: &mut Environment<Fol>,
    stm: &FolStm,
) -> () {
    match stm {
        Axiom(axiom_name, formula) => {
            evaluate_axiom(environment, axiom_name, formula)
        }
        Let(var_name, var_type, body) => {
            evaluate_let(environment, var_name, var_type, body)
        }
        Fun(fun_name, args, out_type, body, is_rec) => {
            evaluate_fun(environment, fun_name, args, out_type, body, is_rec)
        }
        Theorem(theorem_name, formula, proof) => {
            evaluate_theorem(environment, theorem_name, formula, proof)
        }
    }
}
//
//
pub fn evaluate_let(
    environment: &mut Environment<Fol>,
    var_name: &str,
    var_type: &Option<FolFormula>,
    body: &FolTerm,
) -> () {
    generic_evaluate_let::<Fol>(environment, var_name, var_type, body);
}
//
//
pub fn evaluate_axiom(
    environment: &mut Environment<Fol>,
    axiom_name: &str,
    formula: &FolFormula,
) -> () {
    generic_evaluate_axiom::<Fol>(environment, axiom_name, formula);
}
//
//
pub fn evaluate_theorem(
    environment: &mut Environment<Fol>,
    theorem_name: &str,
    formula: &FolFormula,
    proof: &Union<FolTerm, Vec<Tactic<Union<FolTerm, FolFormula>>>>,
) -> () {
    generic_evaluate_theorem::<Fol, Union<FolTerm, FolFormula>>(
        environment,
        theorem_name,
        formula,
        proof,
    );
}
//
//
pub fn evaluate_fun(
    environment: &mut Environment<Fol>,
    fun_name: &str,
    args: &Vec<(String, FolFormula)>,
    out_type: &FolFormula,
    body: &FolTerm,
    is_rec: &bool,
) -> () {
    generic_evaluate_fun::<Fol, _>(
        environment,
        fun_name,
        args,
        out_type,
        body,
        is_rec,
        |args, body_type| make_multiarg_fun_type(&args, &body_type),
    );
}
//########################### STATEMENTS EXECUTION
//
//########################### HELPER FUNCTIONS
//########################### HELPER FUNCTIONS

//########################### UNIT TESTS
#[cfg(test)]
mod unit_tests {}
