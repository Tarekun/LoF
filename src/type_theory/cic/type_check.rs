use std::collections::HashMap;
use super::cic::CicTerm::{Application, Product, Sort, Variable, Abstraction};
use super::cic::{Cic, CicTerm};
use super::cic_utils::{check_positivity};
use super::evaluation::{evaluate_inductive};
use super::unification::solve_unification;
use crate::misc::{simple_map, simple_map_indexed};
use crate::type_theory::cic::cic::{GLOBAL_INDEX, PLACEHOLDER_DBI};
use crate::type_theory::cic::cic_utils::{
    application_args, apply_arguments, clone_product_with_different_result,  get_arg_types, get_prod_innermost, get_variables_as_terms, index_variables, is_instance_of, make_multiarg_fun_type, substitute
};
use crate::type_theory::cic::unification::{equal_under_substitution, instatiate_metas};
use crate::type_theory::commons::type_check::{
    type_check_function, type_check_variable,
};
use crate::type_theory::environment::Environment;
use crate::type_theory::interface::Kernel;

//########################### EXPRESSIONS TYPE CHECKING
//
pub fn type_check_sort(
    environment: &mut Environment<Cic>,
    sort_name: &str,
) -> Result<CicTerm, String> {
    //TODO check that the type is a sort itself?
    type_check_variable::<Cic>(environment, sort_name)
}
//
//
pub fn type_check_application(
    environment: &mut Environment<Cic>,
    left: &CicTerm,
    right: &CicTerm,
) -> Result<CicTerm, String> {
    fn solve_metas(
        local_env: &mut Environment<Cic>,
        arg_type: CicTerm, 
        domain: CicTerm,
    ) -> Result<(CicTerm, CicTerm, HashMap<i32, CicTerm>), String> {
        local_env.add_constraint(&domain, &arg_type);
        let unifier = solve_unification(local_env.get_constraints())?;
        let domain = instatiate_metas(&domain, &unifier);
        let arg_type = instatiate_metas(&arg_type, &unifier);

        Ok((arg_type, domain, unifier))
    }

    fn type_check_nested_app(
        local_env: &mut Environment<Cic>,
        term: CicTerm,
    ) -> Result<CicTerm, String> {
        match term {
            Application(left, right) => {
                let function_type =
                    type_check_nested_app(local_env, *left.clone())?;
                let arg_type = 
                    Cic::type_check_term(&right, local_env)?;

                match function_type {
                    Product(var_name, domain, codomain) => {
                        // solve metavariables in domain types before checking for equality
                        let (arg_type, domain, unifier) = solve_metas(
                            local_env, 
                            arg_type, 
                            *domain
                        )?;

                        // need to support alpha equivalence here
                        if equal_under_substitution(local_env, &domain, &arg_type) {
                            local_env.add_substitution_with_type(&var_name, &right, &arg_type);
                            let var_swapped = substitute(&codomain, &var_name, &right);
                            // solve possible metavariables of `right`
                            let meta_swapped = instatiate_metas(&var_swapped, &unifier);
                            Ok(meta_swapped)
                        } else {
                            Err(format!(
                                "Function and argument have incompatible types: function expects a {:?} but the argument has type {:?}", 
                                domain,
                                arg_type
                            ))
                        }
                    }
                    _ => Err(format!(
                        "Attempted application on non functional term '{:?}' of type: {:?}",
                        left,
                        function_type
                    )),
                }
            }
            _ => {
                let term_type = Cic::type_check_term(&term, local_env)?;
                Ok(term_type)
            }
        }
    }

    environment.with_rollback_keep_meta(|local_env| {
        type_check_nested_app(
            local_env,
            Application(Box::new(left.clone()), Box::new(right.clone())),
        )
    })
}
//
//########################### EXPRESSIONS TYPE CHECKING
//
//
//########################### STATEMENTS TYPE CHECKING
pub fn cic_type_check_fun(
    environment: &mut Environment<Cic>,
    fun_name: &str,
    args: &Vec<(String, CicTerm)>,
    out_type: &CicTerm,
    body: &CicTerm,
    is_rec: &bool,
) -> Result<CicTerm, String> {
    type_check_function::<Cic, _, _>(
        environment,
        fun_name,
        args,
        out_type,
        body,
        is_rec,
        |args, out_type| make_multiarg_fun_type(&args, &out_type), 
        |(var_name, var_type), body| {
            Abstraction(var_name, Box::new(var_type), Box::new(body))
        }
    )
}
//
//
//########################### STATEMENTS TYPE CHECKING
//
//########################### HELPER FUNCTIONS
/// Returns the vector of type judgements for the variables provided if they match the constructor type
fn type_constr_vars(
    constr_type: &CicTerm,
    variables: Vec<CicTerm>,
) -> Result<Vec<(String, CicTerm)>, String> {
    match variables.len() {
        0 => Ok(vec![]),
        1.. => match &variables[0] {
            Variable(var_name, _dbi) => match constr_type {
                Product(type_var, domain, codomain) => {
                    let reduced_codomain = substitute(&codomain, type_var, &variables[0]);
                    let mut typed_vars =
                        type_constr_vars(&reduced_codomain, variables[1..].to_vec())?;
                    typed_vars.insert(0, (var_name.to_string(), *(domain.clone())));
                    Ok(typed_vars)
                }
                // i dont want to return results here
                _ => {
                    Err(format!(
                        "Mismatch in number of variables for constructor"
                    ))
                }
            },
            _ => {
                Err(format!(
                    "Found illegal term in place of variable {:?}",
                    variables[0]
                ))
            }
        },
    }
}

/// Type checks a patter of a branch of a match term against `constr_type`
fn type_check_pattern(
    constr_type: &CicTerm,
    variables: Vec<CicTerm>,
    environment: &mut Environment<Cic>,
) -> Result<CicTerm, String> {
    match variables.len() {
        0 => Ok(constr_type.clone()),
        1.. => match variables[0] {
            Variable(_, _) => match constr_type {
                Product(var_name, _, codomain) => {
                    let reduced_codomain = substitute(&codomain, var_name, &variables[0]);
                    // doesnt need to update the context, here var_name is a type variable, not a term
                    type_check_pattern(
                        &reduced_codomain,
                        variables[1..].to_vec(),
                        environment,
                    )
                }
                _ => Err("Mismatch in number of variables for constructor"
                    .to_string()),
            },
            _ => Err(format!(
                "Found illegal term in place of variable {:?}",
                variables[0],
            )),
        },
    }
}
//########################### HELPER FUNCTIONS
