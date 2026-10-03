use crate::{
    error::LofError, misc::{simple_map, simple_map_indexed}, type_theory::{
        cic::{
            cic::{
                Cic, CicTerm::{self, Application, Product, Sort, Variable}, NameKind, PLACEHOLDER_DBI,
            }, cic_utils::{
                alpha_equivalent, application_args, apply_arguments, check_positivity, clone_product_with_different_result, free_locals, get_applied_function, get_arg_types, get_prod_innermost, get_variables_as_terms, index_variables, is_instance_of, make_multiarg_fun_type,
            }, evaluation::evaluate_inductive, patterns::{LocalEntry, open_branch, pattern_telescope, with_local_entries},
        }, commons::type_check::type_check_variable, environment::Environment, grammars::traits::LocallyNameless, interface::{Kernel, Reducer},
    },
};
use tracing::error;

//########################### JUDGEMENTAL EQUALITY
/// Judgemental equality of CIC types: `actual` and `expected` are reduced to
/// their normal forms which are then compared up to α-equivalence and sort
/// cumulativity (`PROP ≤ TYPE`). This is the only notion of type equality
/// used by the kernel, there is no unification involved
pub fn cic_convertible(
    environment: &Environment<Cic>,
    actual: &CicTerm,
    expected: &CicTerm,
) -> Result<(), LofError> {
    if alpha_equivalent(actual, expected, true) {
        return Ok(());
    }
    let actual_normal = Cic::normalize_term(environment, actual);
    let expected_normal = Cic::normalize_term(environment, expected);
    if alpha_equivalent(&actual_normal, &expected_normal, true) {
        Ok(())
    } else {
        Err(LofError::type_mismatch(
            "judgemental equality",
            &expected_normal,
            &actual_normal,
        ))
    }
}
//########################### JUDGEMENTAL EQUALITY

//########################### EXPRESSIONS TYPE CHECKING
//
pub fn type_check_sort(
    environment: &mut Environment<Cic>,
    sort_name: &str,
) -> Result<CicTerm, LofError> {
    //TODO check that the type is a sort itself?
    type_check_variable::<Cic>(environment, sort_name)
}
//
/// Kernel type checking of (non dependent) pattern matching.
/// Every branch is checked under the entries its pattern introduces (see
/// `pattern_telescope`), all branches must have convertible types, and every
/// constructor of the matched inductive type must be covered
pub fn type_check_match(
    environment: &mut Environment<Cic>,
    matched_term: &CicTerm,
    branches: &Vec<(CicTerm, CicTerm)>,
) -> Result<CicTerm, LofError> {
    let matched_type = Cic::type_check_term(matched_term, environment)?;
    let matched_type = Cic::normalize_term(environment, &matched_type);

    let matched_type_name = match get_applied_function(&matched_type) {
        Variable(name, _) => name,
        other => {
            return Err(LofError::type_check_error(&format!(
                "Unable to reconstruct which inductive type is being matched {:?}",
                other
            )))
        }
    };
    let mut expected_constrs = environment
        .get_constructors_for(&matched_type_name)
        .ok_or_else(|| {
            LofError::type_check_error(&format!(
                "Inductive type named {:?} has no constructors registered",
                matched_type_name
            ))
        })?;

    let mut return_type: Option<CicTerm> = None;
    for (pattern, body) in branches {
        let (opened_pattern, opened_body, _) =
            open_branch(pattern, body, |name| name.to_string());
        let (constr_name, entries) =
            pattern_telescope(environment, &opened_pattern, &matched_type)?;
        expected_constrs.remove(&constr_name);

        // names bound by the pattern that dont exist outside of the branch:
        // the (non dependent) branch type cannot refer to them
        let branch_only: Vec<String> = entries
            .iter()
            .filter_map(|entry| match entry {
                LocalEntry::Assume(name, _) => Some(name.to_owned()),
                LocalEntry::Define(_, _, _) => None,
            })
            .filter(|name| !environment.is_var_bound(name))
            .collect();

        let body_type =
            with_local_entries(environment, &entries, |local_env| {
                let body_type = Cic::type_check_term(&opened_body, local_env)?;
                Ok::<CicTerm, LofError>(Cic::normalize_term(local_env, &body_type))
            })?;
        let mentioned = free_locals(&body_type);
        if let Some(escaping) = branch_only.iter().find(|name| mentioned.contains(*name)) {
            return Err(LofError::type_check_error(&format!(
                "The type {:?} of the branch for {} depends on the pattern variable {}, dependent pattern matching is not supported",
                body_type, constr_name, escaping
            )));
        }

        match &return_type {
            None => return_type = Some(body_type),
            Some(expected) => {
                cic_convertible(environment, &body_type, expected).map_err(|_| {
                    LofError::type_mismatch(
                        format!("branch for constructor {}", constr_name),
                        expected,
                        &body_type,
                    )
                })?
            }
        }
    }

    if !expected_constrs.is_empty() {
        return Err(LofError::type_check_error(
            &format!(
                "Not all constructors have been covered, missing: {:?}",
                expected_constrs
            ),
        ));
    }

    return_type.ok_or_else(|| {
        LofError::type_check_error(&format!(
            "Cannot compute the type of the match on {:?} without branches",
            matched_term
        ))
    })
}
//
//########################### EXPRESSIONS TYPE CHECKING

/// Given the values of an inductive type definition, returns the corresponding eliminator
/// Reference that guided this implementation is Inductive Families by Peter Dybjer
pub fn inductive_eliminator(
    type_name: String,
    params: Vec<(String, CicTerm)>,
    ariety: CicTerm,
    constructors: Vec<(String, CicTerm)>,
) -> CicTerm {
    /// Creation of the first parameters ( A :: σ )
    fn make_left_param_vars(params: Vec<(String, CicTerm)>) -> Vec<CicTerm> {
        params
            .iter()
            .map(|(var_name, _)| Variable(var_name.to_owned(), NameKind::Bound(PLACEHOLDER_DBI)))
            .collect()
    }
    /// Creation of the first parameters ( a :: α\[A\] )
    fn make_right_param_vars(ariety: &CicTerm) -> Vec<CicTerm> {
        // anonymous binders have been named, see `name_anonymous_indices`
        let right_params: Vec<CicTerm> = get_variables_as_terms(ariety);
        right_params
    }
    /// Creation of the full inductive type (P A a) instanciated
    fn make_instance_type(
        type_name: &str,
        left_param_vars: Vec<CicTerm>,
        right_param_vars: Vec<CicTerm>,
    ) -> CicTerm {
        let instance_type =
            apply_arguments(&Variable(type_name.to_string(), NameKind::Bound(PLACEHOLDER_DBI)), left_param_vars);
        let instance_type = apply_arguments(&instance_type, right_param_vars);
        instance_type
    }
    /// Creation of the dependent result type of the eliminator
    /// ( C : (a :: α\[A\]) (c : P A a) set )
    fn make_result_type(
        type_name: &str,
        left_param_vars: Vec<CicTerm>,
        ariety: &CicTerm,
    ) -> CicTerm {
        // TODO might need to rename right_params, i think they're all anonymous
        let right_params = make_right_param_vars(ariety);
        let instance_type =
            make_instance_type(type_name, left_param_vars, right_params);

        clone_product_with_different_result(
            &ariety,
            Product(
                "instance".to_string(),
                Box::new(instance_type),
                //TODO review this sort
                Box::new(Sort("TYPE".to_string())),
            ),
        )
    }
    /// Creation of the dependent branches ( e :: ε\[A\] ) with each ε_j\[A\] is
    /// (b :: β\[A\]) (u :: γ\[A,b\]) (v :: δ\[A,b\]) C p\[A,b\] (cons_j A b u)
    /// where b are non recursive, u are recursive and v are inductive hypotesis and the output is
    /// a construction of the result for this inductive case
    fn make_inductive_cases(
        constructors: Vec<(String, CicTerm)>,
        left_param_vars: Vec<CicTerm>,
        result_var: CicTerm,
        type_name: String,
    ) -> Vec<CicTerm> {
        fn split_recursive_arguments(
            arg_types: Vec<CicTerm>,
            type_name: &str,
        ) -> (Vec<(String, CicTerm)>, Vec<(String, CicTerm)>) {
            let mut are_recursive = false;
            let mut recursive = vec![];
            let mut non_recursive = vec![];

            for (index, arg_type) in arg_types.into_iter().enumerate() {
                //TODO: switch to reference check instead of instance
                if is_instance_of(&arg_type, type_name) {
                    are_recursive = true;
                    recursive.push(((format!("r_{}", index)), arg_type));
                } else if are_recursive {
                    // TODO this could be an error case, should cover it?
                    error!("AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA");
                    error!("THE UNEXPECTED ERROR HAPPEND");
                } else {
                    non_recursive.push(((format!("nr_{}", index)), arg_type));
                }
            }

            (non_recursive, recursive)
        }
        fn make_inductive_hypotheses(
            rec_args: Vec<(String, CicTerm)>,
            result_var: CicTerm,
            left_params_len: usize,
        ) -> Vec<CicTerm> {
            let mut hypotheses = vec![];
            for (arg_name, arg_type) in rec_args {
                //assumption: arg_type is an instance (var/app) of the inductive type
                let mut right_params = application_args(&arg_type);
                // drop left params used in instantiation of inductive type
                right_params.drain(0..left_params_len); // da crab a drainer frfr
                let result_with_rights =
                    apply_arguments(&result_var, right_params);

                hypotheses.push(Application(
                    Box::new(result_with_rights.clone()),
                    Box::new(Variable(arg_name, NameKind::Bound(PLACEHOLDER_DBI))),
                ));
            }

            hypotheses
        }
        let left_params_len = left_param_vars.len();
        let mut cases: Vec<CicTerm> = vec![];

        for (constr_name, constr_type) in constructors {
            let innermost = get_prod_innermost(&constr_type);
            let mut right_params = application_args(innermost);
            // drop left params used in instantiation of inductive type
            right_params.drain(0..left_params_len); // da crab a drainer frfr
            let result_with_rights = apply_arguments(&result_var, right_params);

            // TODO might need to rename args, i think they're all anonymous
            let arg_types = get_arg_types(&constr_type);
            // in the paper non_recursive are called b and recursive u
            let (non_recursive, recursive) =
                split_recursive_arguments(arg_types, &type_name);
            let inductive_hypotheses = make_inductive_hypotheses(
                recursive.clone(),
                result_var.clone(),
                left_params_len,
            );

            let constr_instance = apply_arguments(
                &Variable(constr_name, NameKind::Bound(PLACEHOLDER_DBI)),
                left_param_vars.clone(),
            );
            let constr_instance = apply_arguments(
                &constr_instance,
                simple_map(non_recursive.clone(), |(arg_name, _)| {
                    Variable(arg_name, NameKind::Bound(PLACEHOLDER_DBI))
                }),
            );
            let constr_instance = apply_arguments(
                &constr_instance,
                simple_map(recursive.clone(), |(arg_name, _)| {
                    Variable(arg_name, NameKind::Bound(PLACEHOLDER_DBI))
                }),
            );

            let result_instance =
                apply_arguments(&result_with_rights, vec![constr_instance]);

            // parametrization of the full minor premise
            // start from the innermost (result_instance) and progressively wrap it
            let named_hypotheses: Vec<(String, CicTerm)> = simple_map_indexed(
                inductive_hypotheses,
                |(index, hypothesis)| (format!("ih_{}", index), hypothesis),
            );
            let mut branch_type =
                make_multiarg_fun_type(&named_hypotheses, &result_instance);
            branch_type = make_multiarg_fun_type(&recursive, &branch_type);
            branch_type = make_multiarg_fun_type(&non_recursive, &branch_type);

            cases.push(branch_type);
        }

        cases
    }

    fn name_anonymous_indices(ariety: &CicTerm, position: usize) -> CicTerm {
        match ariety {
            Product(name, domain, codomain) => Product(
                if name == "_" { format!("idx_{}", position) } else { name.to_owned() },
                domain.clone(),
                Box::new(name_anonymous_indices(codomain, position + 1)),
            ),
            _ => ariety.to_owned(),
        }
    }

    let ariety = name_anonymous_indices(&ariety, 0);
    let left_param_vars = make_left_param_vars(params.clone());
    // 0 is a placeholder value, the eliminator type is indexed when returned 
    let result_var = Variable(format!("er_{}", type_name), NameKind::Bound(PLACEHOLDER_DBI)); // er = eliminator result, C in the paper
    let result_type =
        make_result_type(&type_name, left_param_vars.clone(), &ariety);
    let inductive_cases = make_inductive_cases(
        constructors,
        left_param_vars.clone(),
        result_var.clone(),
        type_name.clone(),
    );
    let right_params =
        simple_map_indexed(get_arg_types(&ariety), |(index, param_type)| {
            (format!("rp_{}", index), param_type)
        });
    let right_param_vars =
        simple_map(right_params.clone(), |(param_name, _)| {
            Variable(param_name, NameKind::Bound(PLACEHOLDER_DBI))
        });
    let inductive_instace_var = Variable("t".to_string(), NameKind::Const());
    let inductive_instace = make_instance_type(
        &type_name,
        left_param_vars,
        right_param_vars.clone(),
    );
    let mut result_instance =
        apply_arguments(&result_var, right_param_vars.clone());
    result_instance =
        Application(Box::new(result_instance), Box::new(inductive_instace_var));

    let mut full_parametrization = make_multiarg_fun_type(
        &vec![("t".to_string(), inductive_instace)],
        &result_instance,
    );
    full_parametrization =
        make_multiarg_fun_type(&right_params, &full_parametrization);
    full_parametrization = make_multiarg_fun_type(
        &simple_map_indexed(inductive_cases, |(index, case_type)| {
            (format!("c_{}", index), case_type)
        }),
        &full_parametrization,
    );
    full_parametrization = make_multiarg_fun_type(
        &vec![(format!("er_{}", type_name), result_type)],
        &full_parametrization,
    );
    full_parametrization =
        make_multiarg_fun_type(&params, &full_parametrization);
    index_variables(&full_parametrization)
}

pub fn type_check_inductive(
    environment: &mut Environment<Cic>,
    type_name: &str,
    params: &Vec<(String, CicTerm)>,
    ariety: &CicTerm,
    constructors: &Vec<(String, CicTerm)>,
) -> Result<CicTerm, LofError> {
    //TODO check positivity
    let inductive_type = make_multiarg_fun_type(params, ariety);
    let _ = Cic::type_check_type(&inductive_type, environment)?;

    // Each parameter's type is stated under the parameters preceding it, and
    // every constructor under the whole parameter telescope. Those binders are
    // not present in the terms themselves, so their references are naked De
    // Bruijn indices whose meaning depends on the depth they are read at.
    // Opening the telescope turns them into `Local`s, which the context can
    // hand back at any depth without reindexing.
    let mut opened_params: Vec<(String, CicTerm)> = vec![];
    for (param_name, param_type) in params {
        let opened_type = opened_params
            .iter()
            .rev()
            .fold(param_type.clone(), |opened, (earlier_param, _)| {
                opened.open(earlier_param)
            });
        opened_params.push((param_name.to_owned(), opened_type));
    }
    let open_under_params = |typee: &CicTerm| {
        params
            .iter()
            .rev()
            .fold(typee.to_owned(), |opened, (param_name, _)| {
                opened.open(param_name)
            })
    };

    let inductive_assumptions: Vec<(String, CicTerm)> = 
        vec![
            (type_name.to_string(), inductive_type.clone())
        ]
            .into_iter()
            .chain(opened_params.into_iter())
            .collect();

    let mut constr_bindings = vec![];
    environment.with_local_assumptions(
        &inductive_assumptions,
        |local_env| {
            for (constr_name, constr_type) in constructors {
                let opened_constr = open_under_params(constr_type);
                let _ = Cic::type_check_type(&opened_constr, local_env)?;
                for arg_type in get_arg_types(&opened_constr) {
                    if !check_positivity(&arg_type, &type_name) {
                        return Err(LofError::custom(format!("Inductive constructor {} has recursive argument with negative polarity", constr_name)));
                    }
                }
                
                constr_bindings.push((constr_name.clone(), constr_type.clone()));
            }

            Ok::<(), LofError>(())
        },
    )?;

    let _ = evaluate_inductive(
        environment,
        type_name,
        params,
        ariety,
        &constr_bindings,
    );
    Ok(Variable("Unit".to_string(), NameKind::Const()))
}

#[cfg(test)]
#[path = "../../tests/type_theory/cic/type_check.rs"]
mod tests;
