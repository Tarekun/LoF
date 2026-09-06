use crate::{
    error::LofError, misc::{simple_map, simple_map_indexed}, type_theory::{
        cic::{
            cic::{
                Cic, CicTerm::{self, Application, Product, Sort, Variable}, NameKind, PLACEHOLDER_DBI,
            }, cic_utils::{
                alpha_equivalent, application_args, apply_arguments,
                check_positivity, clone_product_with_different_result,
                get_applied_function, get_arg_types, get_prod_innermost,
                get_variables_as_terms, index_variables, is_instance_of,
                make_multiarg_fun_type, pattern_binder_names, substitute,
                substitute_and_lift,
            },
            evaluation::{
                evaluate_equivalence, evaluate_inductive, evaluate_transport,
            },
        },
        commons::type_check::type_check_variable,
        environment::Environment,
        grammars::traits::LocallyNameless,
        interface::{Kernel, Reducer},
    },
};
use tracing::error;

//########################### JUDGEMENTAL EQUALITY
/// CIC convertibility with universe cumulativity
pub fn cic_convertible(
    environment: &Environment<Cic>,
    actual: &CicTerm,
    expected: &CicTerm,
) -> Result<(), LofError> {
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
/// Types a projection `target.i` out of a single-constructor inductive.
///
/// Given `target : T(p_1..p_m)` and `T`'s only constructor
/// `C : ∀p_1..p_m. ∀a_0:A_0. .. ∀a_{k-1}:A_{k-1}. T(p_1..p_m)`, the result
/// is `A_i` with the type's parameters instantiated to `target`'s actual
/// ones and every *earlier* field replaced by its own projection:
///
/// ```text
/// A_i[p_j := actual_j][a_0 := target.0, .., a_{i-1} := target.{i-1}]
/// ```
///
/// That second substitution is what makes a dependent field come out
/// right: `PackedVec`'s second field has declared type `Vec(Tp, n)`, and
/// projecting it yields `Vec(Tp, target.0)` rather than a term mentioning
/// the constructor's own unbound `n`.
pub fn type_check_proj(
    environment: &mut Environment<Cic>,
    type_name: &str,
    field_index: usize,
    target: &CicTerm,
) -> Result<CicTerm, LofError> {
    let target_type = Cic::type_check_term(target, environment)?;
    if !is_instance_of(&target_type, type_name) {
        return Err(LofError::custom(format!(
            "projection .{} expects a '{}', got a '{}'",
            field_index, type_name, target_type
        )));
    }

    let constructors = environment
        .get_inductive_constructors(type_name)
        .ok_or_else(|| {
            LofError::custom(format!("unknown inductive type '{}'", type_name))
        })?;
    if constructors.len() != 1 {
        return Err(LofError::custom(format!(
            "projection .{} needs a single-constructor type, but '{}' has {}",
            field_index,
            type_name,
            constructors.len()
        )));
    }
    let constructor_type = constructors[0].1.to_owned();
    let param_count = environment
        .get_inductive_param_count(type_name)
        .unwrap_or(0);
    let actual_params = application_args(&target_type);

    // walk the constructor's Pi-chain, substituting the type's parameters
    // and then each earlier field's projection as we pass it
    let mut remaining = constructor_type;
    for depth in 0..param_count + field_index {
        let Product(binder, _, codomain) = remaining else {
            return Err(LofError::custom(format!(
                "'{}' has no field {}",
                type_name, field_index
            )));
        };
        let value = if depth < param_count {
            actual_params.get(depth).cloned().ok_or_else(|| {
                LofError::custom(format!(
                    "'{}' applied to too few parameters",
                    type_name
                ))
            })?
        } else {
            CicTerm::Proj(
                type_name.to_string(),
                depth - param_count,
                Box::new(target.to_owned()),
            )
        };
        remaining = substitute(&codomain, &binder, &value);
    }

    match remaining {
        Product(_, domain, _) => Ok((*domain).to_owned()),
        _ => Err(LofError::custom(format!(
            "'{}' has no field {}",
            type_name, field_index
        ))),
    }
}
//
//
/// Kernel type checking of (non dependent) pattern matching: every branch is
/// checked under the entries its pattern introduces,
/// and all branches must have convertible types
pub fn type_check_match(
    environment: &mut Environment<Cic>,
    matched_term: &CicTerm,
    branches: &Vec<(CicTerm, CicTerm)>,
) -> Result<CicTerm, LofError> {
    let matching_type = Cic::type_check_term(matched_term, environment)?;
    let matching_type = Cic::normalize_term(environment, &matching_type);
    let mut return_type = None;

    let ind_type_constructor = get_applied_function(&matching_type);
    let matching_type_name = if let Variable(name, _) = ind_type_constructor {
        name
    } else {
        return Err(LofError::type_check_error(&format!(
            "Unable to reconstruct which inductive type is being matched {:?}",
            ind_type_constructor
        )));
    };
    let mut expected_constrs = if let Some(constrs) = environment.get_constructors_for(
        &matching_type_name
    ) {
        constrs
    } else {
        return Err(LofError::type_check_error(&format!(
            "Inductive type named {:?} has no constructors registered",
            matching_type_name
        )));
    };

    for (pattern, body) in branches {
        let (opened_pattern, opened_body, _) =
            open_branch(pattern, body, |name| name.to_string());
        let (constr_name, entries) =
            pattern_telescope(environment, &opened_pattern, &matching_type)?;
        expected_constrs.remove(&constr_name);

        let body_type = with_local_entries(environment, &entries, |local_env| {
            let body_type = Cic::type_check_term(&opened_body, local_env)?;
            // aliases of the parameters are only defined in here
            Ok::<_, LofError>(Cic::normalize_term(local_env, &body_type))
        })?;
        match &return_type {
            None => return_type = Some(body_type),
            Some(expected) => cic_convertible(environment, &body_type, expected)?,
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

    Ok(return_type.unwrap())
}


#[derive(Debug, Clone, PartialEq)]
pub enum LocalEntry {
    /// local assumption: (name, type)
    Assume(String, CicTerm),
    /// local definition: (name, value, type)
    Define(String, CicTerm, CicTerm),
}


pub fn with_local_entries<F: FnOnce(&mut Environment<Cic>) -> R, R>(
    environment: &mut Environment<Cic>,
    entries: &[LocalEntry],
    callable: F,
) -> R {
    match entries.split_first() {
        None => callable(environment),
        Some((LocalEntry::Assume(name, typee), rest)) => environment
            .with_local_assumption(name, typee, |local_env| {
                with_local_entries(local_env, rest, callable)
            }),
        Some((LocalEntry::Define(name, value, typee), rest)) => environment
            .with_local_substitution(
                name,
                value,
                &Some(typee.to_owned()),
                |local_env| with_local_entries(local_env, rest, callable),
            ),
    }
}

/// Opens a match branch: every binder introduced by `pattern` is turned
/// into a locally free variable named by `rename`, both in the pattern and
/// in the `body`
pub fn open_branch<F: FnMut(&str) -> String>(
    pattern: &CicTerm,
    body: &CicTerm,
    mut rename: F,
) -> (CicTerm, CicTerm, Vec<String>) {
    let locals: Vec<String> = pattern_binder_names(pattern)
        .iter()
        .map(|name| rename(name))
        .collect();
    // innermost binder (the last one) has index 0, so it's opened first
    let (pattern, body) = locals.iter().rev().fold(
        (pattern.to_owned(), body.to_owned()),
        |(pattern, body), local| (pattern.open(local), body.open(local)),
    );
    (pattern, body, locals)
}

/// Computes the local entries an opened `pattern` introduces
/// returning them in binding order along with the constructor name.
///
/// The first arguments of a constructor are the parameters of its inductive
/// type: they're fixed by `matching_type`, so a variable in those positions
/// is a definition aliasing the actual parameter (and a `?` is ignored). The
/// remaining arguments are assumptions typed by the constructor, instantiated
/// with the arguments preceding them
pub fn pattern_telescope(
    environment: &Environment<Cic>,
    pattern: &CicTerm,
    matching_type: &CicTerm,
) -> Result<(String, Vec<LocalEntry>), LofError> {
    let constr_name = match get_applied_function(pattern) {
        Variable(name, _) => name,
        other => {
            return Err(LofError::type_check_error(&format!(
                "Pattern should start with constructor variable application, found {:?}",
                other
            )))
        }
    };
    let inductive_name = environment
        .constructor_type_of(&constr_name)
        .ok_or_else(|| LofError::unbound_variable(&constr_name))?;
    let actual_left_params = application_args(matching_type);
    let left_param_count = environment
        .get_inductive_param_count(&inductive_name)
        .unwrap_or(0);
    // check that the inductive type constructed by this pattern matches matching_type
    match get_applied_function(matching_type) {
        Variable(name, _)
            if name == inductive_name && actual_left_params.len() >= left_param_count => {}
        _ => {
            return Err(LofError::type_mismatch(
                format!("pattern `{:?}`", pattern),
                matching_type,
                &inductive_name,
            ))
        }
    }

    let mut constr_type = environment
        .get_variable_type(&constr_name)
        .ok_or_else(|| LofError::unbound_variable(&constr_name))?;
    let formal_arguments = application_args(pattern);
    let mut entries = vec![];

    // TODO id like this remade into a pretty recursive function instead of stinky for loop
    for (position, argument) in formal_arguments.iter().enumerate() {
        let Product(binder, domain, codomain) = constr_type else {
            return Err(LofError::arity_mismatch(
                "constructor pattern",
                position,
                formal_arguments.len(),
            ));
        };

        let value = if position < left_param_count {
            if let Variable(name, _) = argument {
                entries.push(LocalEntry::Define(
                    name.to_owned(),
                    // left params are δ-reducable by the actual value found in matching_type
                    actual_left_params[position].to_owned(),
                    *domain,
                ));
            }
            actual_left_params[position].to_owned()
        } else {
            match argument {
                Variable(name, _) => {
                    entries.push(LocalEntry::Assume(name.to_owned(), *domain))
                }
                // subpattern
                Application(_, _) => {
                    let nested_type = Cic::normalize_term(environment, &domain);
                    let (_, nested) =
                        pattern_telescope(environment, argument, &nested_type)?;
                    entries.extend(nested);
                }
                _ => return Err(LofError::type_check_error(argument)),
            }
            argument.to_owned()
        };
        constr_type = substitute_and_lift(&codomain, &binder, &value);
    }

    if let Product(_, _, _) = constr_type {
        return Err(LofError::type_check_error(&format!(
            "Pattern {:?} doesnt fully apply constructor {}",
            pattern, constr_name
        )));
    }
    Ok((constr_name, entries))
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

/// Sanity-checks every component of an `equivalence` declaration (each
/// must type-check on its own terms - the engine does not attempt to
/// verify eg that `dep_elim` is genuinely shaped like `type_a`'s own
/// recursor, only that it is a well-typed term), then registers the
/// resulting `EquivConfig` via `evaluate_equivalence` so later statements
/// in the same file (including further `transport` invocations) can see
/// it - mirroring how `type_check_inductive` registers the inductive type
/// itself via `evaluate_inductive`, rather than deferring registration to
/// the later `execute` phase.
#[allow(clippy::too_many_arguments)]
pub fn type_check_equivalence(
    environment: &mut Environment<Cic>,
    name: &str,
    type_a: &CicTerm,
    type_b: &CicTerm,
    forward: &CicTerm,
    backward: &CicTerm,
    section: &CicTerm,
    retraction: &CicTerm,
    dep_elim: &CicTerm,
    eta: &Option<Box<CicTerm>>,
    dep_constr: &Vec<(String, CicTerm)>,
    iota: &Vec<(String, CicTerm)>,
) -> Result<CicTerm, LofError> {
    // Both sides must be well-formed, but not necessarily *types*: a
    // parameterized inductive is referred to by its bare name, so `List`
    // is a type former (`TYPE -> TYPE`) rather than a type. Require only
    // that its type ends in a sort.
    for (label, type_former) in [("type_a", type_a), ("type_b", type_b)] {
        let former_type = Cic::type_check_term(type_former, environment)?;
        if !matches!(get_prod_innermost(&former_type), Sort(_)) {
            return Err(LofError::type_mismatch(
                &format!("equivalence '{}' {}", name, label),
                &"a type or type former",
                type_former,
            ));
        }
    }
    let _ = Cic::type_check_term(forward, environment)?;
    let _ = Cic::type_check_term(backward, environment)?;
    let _ = Cic::type_check_term(section, environment)?;
    let _ = Cic::type_check_term(retraction, environment)?;
    let _ = Cic::type_check_term(dep_elim, environment)?;
    if let Some(eta_term) = eta {
        let _ = Cic::type_check_term(eta_term, environment)?;
    }
    for (_, term) in dep_constr {
        let _ = Cic::type_check_term(term, environment)?;
    }
    for (_, term) in iota {
        let _ = Cic::type_check_term(term, environment)?;
    }

    evaluate_equivalence(
        environment,
        name,
        type_a,
        type_b,
        forward,
        backward,
        section,
        retraction,
        dep_elim,
        eta,
        dep_constr,
        iota,
    )?;

    Ok(Variable("Unit".to_string(), GLOBAL_INDEX))
}

/// Type-checks the declared target type/formula, then performs the actual
/// transport (via `evaluate_transport`, which calls into
/// `cic::transport::transport_term` and validates the result) - mirroring
/// how `type_check_inductive` both checks and registers in one pass.
pub fn type_check_transport(
    environment: &mut Environment<Cic>,
    new_name: &str,
    new_type: &CicTerm,
    old_name: &str,
    equiv_name: &str,
) -> Result<CicTerm, LofError> {
    let _ = Cic::type_check_type(new_type, environment)?;

    evaluate_transport(
        environment,
        new_name,
        new_type,
        old_name,
        equiv_name,
    )?;

    Ok(new_type.to_owned())
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
