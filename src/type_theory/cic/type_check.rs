use std::collections::HashMap;
use super::cic::CicTerm::{Application, Product, Sort, Meta};
use super::cic::{Cic, CicTerm};
use super::cic_utils::substitute_meta;
use super::unification::solve_unification;
use crate::misc::Union;
use crate::parser::api::Tactic;
use crate::type_theory::cic::cic_utils::{
    make_multiarg_fun_type, substitute
};
use crate::type_theory::cic::unification::{equal_under_substitution, instatiate_metas};
use crate::type_theory::commons::type_check::{
    generic_type_check_abstraction, generic_type_check_axiom, 
    generic_type_check_fun, generic_type_check_let, generic_type_check_theorem, 
    generic_type_check_universal, generic_type_check_variable
};
use crate::type_theory::environment::Environment;
use crate::type_theory::interface::Kernel;

//########################### EXPRESSIONS TYPE CHECKING
//
pub fn type_check_sort(
    environment: &mut Environment<CicTerm, CicTerm>,
    sort_name: &str,
) -> Result<CicTerm, String> {
    //TODO check that the type is a sort itself?
    generic_type_check_variable::<Cic>(environment, sort_name)
}
//
//
pub fn type_check_variable(
    environment: &mut Environment<CicTerm, CicTerm>,
    var_name: &str,
) -> Result<CicTerm, String> {
    generic_type_check_variable::<Cic>(environment, var_name)
}
//
//
pub fn type_check_abstraction(
    environment: &mut Environment<CicTerm, CicTerm>,
    var_name: &str,
    var_type: &CicTerm,
    body: &CicTerm,
) -> Result<CicTerm, String> {
    let body_type = generic_type_check_abstraction::<Cic>(environment, var_name, var_type, body)?;
    let (var_type, body_type) = if let Meta(index) = var_type {
        let substitution = solve_unification(environment.get_constraints())?;
        (&substitute_meta(var_type, index, substitution.get(index).unwrap()),
        substitute_meta(&body_type, index, substitution.get(index).unwrap()))
    } else {
        (var_type, body_type)
    };

    Ok(Product(
        var_name.to_string(),
        Box::new(var_type.clone()),
        Box::new(body_type),
    ))
}
//
//
pub fn type_check_product(
    environment: &mut Environment<CicTerm, CicTerm>,
    var_name: &str,
    var_type: &CicTerm,
    body: &CicTerm,
) -> Result<CicTerm, String> {
    // TODO: im not sure using the FO quantification is actually correct here
    let body_type = generic_type_check_universal::<Cic>(environment, var_name, var_type, body)?;
    match body_type {
        Sort(_) => Ok(body_type),
        _ => Err(format!("Body of product term must be of type sort, i.e. must be a type, not {:?}", body_type)),
    }
}
//
//
pub fn type_check_application(
    environment: &mut Environment<CicTerm, CicTerm>,
    left: &CicTerm,
    right: &CicTerm,
) -> Result<CicTerm, String> {
    fn solve_metas(
        local_env: &mut Environment<CicTerm, CicTerm>,
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
        local_env: &mut Environment<CicTerm, CicTerm>,
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
//
pub fn type_check_let(
    environment: &mut Environment<CicTerm, CicTerm>,
    var_name: &str,
    opt_type: &Option<CicTerm>,
    body: &CicTerm,
) -> Result<CicTerm, String> {
    generic_type_check_let::<Cic>(environment, var_name, opt_type, body)
}
//
//
pub fn type_check_fun(
    environment: &mut Environment<CicTerm, CicTerm>,
    fun_name: &str,
    args: &Vec<(String, CicTerm)>,
    out_type: &CicTerm,
    body: &CicTerm,
    is_rec: &bool,
) -> Result<CicTerm, String> {
    generic_type_check_fun::<Cic, _>(environment, fun_name, args, out_type, body, is_rec, make_multiarg_fun_type)
}
//
//
pub fn type_check_theorem(
    environment: &mut Environment<CicTerm, CicTerm>,
    theorem_name: &str,
    formula: &CicTerm,
    proof: &Union<CicTerm, Vec<Tactic<CicTerm>>>
) -> Result<CicTerm, String> {
    generic_type_check_theorem::<Cic, CicTerm>(environment, theorem_name, formula, proof)
}
//
//
pub fn type_check_axiom(
    environment: &mut Environment<CicTerm, CicTerm>,
    axiom_name: &str,
    formula: &CicTerm,
) -> Result<CicTerm, String> {
    generic_type_check_axiom::<Cic>(environment, axiom_name, formula)
}
//
//########################### STATEMENTS TYPE CHECKING
//
//########################### HELPER FUNCTIONS
//
//
//########################### HELPER FUNCTIONS
