use crate::{
    misc::{simple_map, simple_map_indexed},
    type_theory::{
        cic::{
            cic::{
                Cic,
                CicTerm::{
                    self, Application, Product, Sort, Variable,
                }, GLOBAL_INDEX, PLACEHOLDER_DBI,
            },
            cic_utils::{application_args, apply_arguments, check_positivity, clone_product_with_different_result, get_applied_function, get_arg_types, get_prod_innermost, get_variables_as_terms, index_variables, is_instance_of, make_multiarg_fun_type, substitute}, evaluation::evaluate_inductive,
        },
        environment::Environment,
        interface::{Kernel, Refiner},
    }
};
use tracing::error;

/// Returns the vector of type judgements for the variables provided if they match the constructor type
fn type_constr_vars(
    constr_type: &CicTerm,
    pattern: &CicTerm,
) -> Result<Vec<(String, CicTerm)>, String> {
    fn solver(
        constr_type: &CicTerm,
        variables: Vec<CicTerm>,
    ) -> Result<Vec<(String, CicTerm)>, String> {
        match variables.len() {
            0 => Ok(vec![]),
            1.. => match &variables[0] {
                Variable(var_name, _) => match constr_type {
                    Product(type_var, domain, codomain) => {
                        let reduced_codomain =
                            substitute(&codomain, type_var, &variables[0]);
                        let mut typed_vars = solver(
                            &reduced_codomain,
                            variables[1..].to_vec(),
                        )?;
                        typed_vars
                            .insert(0, (var_name.to_string(), *(domain.clone())));
                        Ok(typed_vars)
                    }
                    _ => Err(format!(
                        "Mismatch in number of variables for constructor"
                    )),
                },
                _ => Err(format!(
                    "Found illegal term in place of variable {:?}",
                    variables[0]
                )),
            },
        }
    }

    let variables = application_args(pattern);
    solver(constr_type, variables)
}

/// Type checks the provided terms with the constructor type and returns the actual instanciation
/// type provided
fn type_check_pattern(
    environment: &mut Environment<Cic>,
    pattern: &CicTerm,
    constr_type: &CicTerm,
) -> Result<CicTerm, String> {
    fn solver(
        constr_type: &CicTerm,
        variables: Vec<CicTerm>,
        environment: &mut Environment<Cic>,
    ) -> Result<CicTerm, String> {
        match variables.len() {
            0 => Ok(constr_type.clone()),
            1.. => match variables[0] {
                Variable(_, _) => match constr_type {
                    Product(var_name, _, codomain) => {
                        // TODO if the variable is an argument to the type it should be type checked
                        // (if its constructor argument its simply a new binded variable)
                        let reduced_codomain =
                            substitute(&codomain, var_name, &variables[0]);
                        // doesnt need to update the context, here var_name is a type variable, not a term
                        solver(
                            &reduced_codomain,
                            variables[1..].to_vec(),
                            environment,
                        )
                    }
                    _ => Err("Mismatch in number of variables for constructor"
                        .to_string()),
                },
                // TODO to extend functionality for constr argument expansion in the pattern
                // simply support other cases here (eg nested applications)
                _ => Err(format!(
                    "Found illegal term in place of variable {:?}",
                    variables[0],
                )),
            },
        }
    }

    let variables = application_args(pattern);
    solver(constr_type, variables, environment)
}

pub fn type_check_match(
    environment: &mut Environment<Cic>,
    matched_term: &CicTerm,
    branches: &Vec<(CicTerm, CicTerm)>,
) -> Result<CicTerm, String> {
    let matching_type = Cic::type_check_term(matched_term, environment)?;
    let mut return_type = None;

    for (pattern, body) in branches {
        //pattern type checking
        let constructor = get_applied_function(pattern);
        let constr_type = if let Variable(_, _) = constructor {
            Cic::type_check_term(&constructor, environment)
        } else {
            Err(format!(
                "Pattern should start with constructor variable application, found {:?}",
                constructor
            ))
        }?;
        let result_type = type_check_pattern(
            environment,
            pattern,
            &constr_type,
        )?;
        if !Cic::terms_unify(environment, &result_type, &matching_type) {
            return Err(
                format!(
                    "Pattern doesnt produce expected type: expected {:?} produced {:?}",
                    matching_type,
                    result_type
                )
            );
        }

        //body type checking
        let pattern_assumptions =
            type_constr_vars(&constr_type, pattern)?;
        let body_type = environment
            .with_local_assumptions(&pattern_assumptions, |local_env| {
                Cic::type_check_term(body, local_env)
            })?;
        if return_type.is_none() {
            return_type = Some(body_type);
        } else if !Cic::terms_unify(
            environment,
            &return_type.clone().unwrap(),
            &body_type,
        ) {
            return Err(
                format!(
                    "Match branches have different types: found {:?} with previous {:?}",
                    body_type,
                    return_type.unwrap()
                )
            );
        }
    }

    Ok(return_type.unwrap())
}

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
            .map(|(var_name, _)| Variable(var_name.to_owned(), PLACEHOLDER_DBI))
            .collect()
    }
    /// Creation of the first parameters ( a :: α\[A\] )
    fn make_right_param_vars(ariety: &CicTerm) -> Vec<CicTerm> {
        // TODO might need to rename right_params, i think they're all anonymous
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
            apply_arguments(&Variable(type_name.to_string(), PLACEHOLDER_DBI), left_param_vars);
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
                    Box::new(Variable(arg_name, PLACEHOLDER_DBI)),
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
                &Variable(constr_name, PLACEHOLDER_DBI),
                left_param_vars.clone(),
            );
            let constr_instance = apply_arguments(
                &constr_instance,
                simple_map(non_recursive.clone(), |(arg_name, _)| {
                    Variable(arg_name, PLACEHOLDER_DBI)
                }),
            );
            let constr_instance = apply_arguments(
                &constr_instance,
                simple_map(recursive.clone(), |(arg_name, _)| {
                    Variable(arg_name, PLACEHOLDER_DBI)
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

    let left_param_vars = make_left_param_vars(params.clone());
    // 0 is a placeholder value, the eliminator type is indexed when returned 
    let result_var = Variable(format!("er_{}", type_name), PLACEHOLDER_DBI); // er = eliminator result, C in the paper
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
            Variable(param_name, PLACEHOLDER_DBI)
        });
    let inductive_instace_var = Variable("t".to_string(), GLOBAL_INDEX);
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
) -> Result<CicTerm, String> {
    //TODO check positivity
    let inductive_type = make_multiarg_fun_type(params, ariety);
    let _ = Cic::type_check_type(&inductive_type, environment)?;

    let inductive_assumptions: Vec<(String, CicTerm)> = 
        vec![
            (type_name.to_string(), inductive_type.clone())
        ]
            .into_iter()
            .chain(params.clone().into_iter())
            .collect();

    let mut constr_bindings = vec![];
    environment.with_local_assumptions(
        &inductive_assumptions,
        |local_env| {
            for (constr_name, constr_type) in constructors {
                let _ = Cic::type_check_type(constr_type, local_env)?;
                for arg_type in get_arg_types(&constr_type) {
                    if !check_positivity(&arg_type, &type_name) {
                        return Err(format!("Inductive constructor {} has recursive argument with negative polarity", constr_name));
                    }
                }
                
                constr_bindings.push((constr_name.clone(), constr_type.clone()));
            }

            Ok::<(), String>(())
        },
    )?;

    evaluate_inductive(
        environment,
        type_name,
        params,
        ariety,
        &constr_bindings,
    );
    Ok(Variable("Unit".to_string(), GLOBAL_INDEX))
}
