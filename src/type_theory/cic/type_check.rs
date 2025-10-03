use std::collections::HashMap;
use super::cic::CicTerm::{Application, Product};
use super::cic::{Cic, CicTerm};
use super::unification::solve_unification;
use crate::type_theory::cic::cic_utils::substitute;
use crate::type_theory::cic::unification::{equal_under_substitution, instatiate_metas};
use crate::type_theory::commons::type_check::{
    type_check_variable,
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
        local_env.add_type_constraint(&domain, &arg_type);
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
