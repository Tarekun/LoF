use super::fol::FolStm::{Axiom, Fun, Let, Theorem};
use super::fol::{
    Fol, FolFormula, FolStm,
    FolTerm::{self, Abstraction, Application, Variable},
};
use super::fol_utils::make_multiarg_fun_type;
use crate::type_theory::commons::evaluation::{
    evaluate_fun, reduce_application,
};
use crate::{
    misc::Union,
    type_theory::{
        commons::evaluation::{
            evaluate_axiom, evaluate_let, evaluate_theorem, reduce_variable,
        },
        environment::Environment,
    },
};

//########################### TERM βδ-REDUCTION
pub fn one_step_reduction(
    environment: &mut Environment<Fol>,
    term: &FolTerm,
) -> FolTerm {
    match term {
        Variable(var_name) => {
            reduce_variable::<Fol>(environment, var_name, term)
        }
        Application(left, right) => {
            fol_reduce_application(environment, left, right)
        }
        _ => term.clone(),
    }
}
//
//
fn fol_reduce_application(
    environment: &mut Environment<Fol>,
    left: &FolTerm,
    right: &FolTerm,
) -> FolTerm {
    reduce_application::<Fol, _, _>(
        environment,
        left,
        right,
        |fun_reduced| match fun_reduced {
            Abstraction(var_name, _, body) => {
                Some((var_name.to_string(), (**body).to_owned()))
            }
            _ => None,
        },
        |left_reduced, right_reduced| {
            Application(Box::new(left_reduced), Box::new(right_reduced))
        },
    )
}
//########################### TERM βδ-REDUCTION

//########################### STATEMENTS EXECUTION
pub fn evaluate_statement(
    environment: &mut Environment<Fol>,
    stm: &FolStm,
) -> () {
    match stm {
        Axiom(axiom_name, formula) => {
            evaluate_axiom::<Fol>(environment, axiom_name, formula)
        }
        Let(var_name, var_type, body) => {
            evaluate_let::<Fol>(environment, var_name, var_type, body)
        }
        Fun(fun_name, args, out_type, body, is_rec) => {
            evaluate_fun::<Fol, _, _>(
                environment,
                fun_name,
                args,
                out_type,
                body,
                is_rec,
                |args, body_type| make_multiarg_fun_type(&args, &body_type),
                |(var_name, var_type), body| {
                    Abstraction(var_name, Box::new(var_type), Box::new(body))
                },
            )
        }
        Theorem(theorem_name, formula, proof) => {
            evaluate_theorem::<Fol, Union<FolTerm, FolFormula>>(
                environment,
                theorem_name,
                formula,
                proof,
            )
        }
    }
}
//########################### STATEMENTS EXECUTION
//
//########################### HELPER FUNCTIONS
//########################### HELPER FUNCTIONS

//########################### UNIT TESTS
#[cfg(test)]
mod unit_tests {}
