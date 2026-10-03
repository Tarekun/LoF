use super::cic::CicTerm::{Application, Meta, Product, Variable};
use super::cic::{Cic, CicTerm, HOLE_INDEX};
use super::cic_utils::{
    application_args, get_applied_function, open_term, pattern_binder_names,
    substitute_and_lift,
};
use crate::error::LofError;
use crate::type_theory::environment::Environment;
use crate::type_theory::interface::Reducer;

/// A local entry introduced by a match pattern for its branch body
#[derive(Debug, Clone, PartialEq)]
pub enum PatternEntry {
    /// constructor argument bound by the pattern: (name, type)
    Assume(String, CicTerm),
    /// pattern variable sitting in a parameter position of the inductive
    /// type: it doesnt bind anything new, it's an alias for the parameter
    /// the matched term was instantiated with: (name, value, type)
    Define(String, CicTerm, CicTerm),
}

/// Opens a match branch: every binder introduced by `pattern` is turned
/// into a locally free variable, both in the pattern and in the `body`.
/// `rename` decides the local name every binder is opened with.
/// Returns the opened (pattern, body) and the local names used, in the order
/// the pattern binds them
pub fn open_branch<F: FnMut(&str) -> String>(
    pattern: &CicTerm,
    body: &CicTerm,
    mut rename: F,
) -> (CicTerm, CicTerm, Vec<String>) {
    let local_names: Vec<String> = pattern_binder_names(pattern)
        .iter()
        .map(|name| rename(name))
        .collect();
    // innermost binder (the last one) has index 0, so it's opened first
    let (opened_pattern, opened_body) = local_names.iter().rev().fold(
        (pattern.to_owned(), body.to_owned()),
        |(pattern, body), local_name| {
            (open_term(&pattern, local_name), open_term(&body, local_name))
        },
    );

    (opened_pattern, opened_body, local_names)
}

/// Computes the local entries an (opened, see `open_branch`) `pattern`
/// introduces when matching a term of type `matched_type` (in normal form).
///
/// The first arguments of a constructor are the parameters of its inductive
/// type: those are fixed by `matched_type` and never bound by the pattern, so
/// a variable in those positions is just an alias to the actual parameter and
/// a `?`/`_` is ignored. The remaining arguments are bound with the types
/// given by the constructor, instantiated with the arguments preceding them.
/// Indices are not checked against `matched_type`: branch bodies are typed
/// without assuming any index equality (non dependent pattern matching).
///
/// Returns the name of the constructor used by the pattern and the entries
/// in binding order
pub fn pattern_telescope(
    environment: &Environment<Cic>,
    pattern: &CicTerm,
    matched_type: &CicTerm,
) -> Result<(String, Vec<PatternEntry>), LofError> {
    let mut entries = vec![];
    let constructor =
        solve_pattern(environment, pattern, matched_type, &mut entries)?;
    Ok((constructor, entries))
}

fn solve_pattern(
    environment: &Environment<Cic>,
    pattern: &CicTerm,
    matched_type: &CicTerm,
    entries: &mut Vec<PatternEntry>,
) -> Result<String, LofError> {
    let constructor_name = match get_applied_function(pattern) {
        Variable(name, _) => name,
        other => {
            return Err(LofError::type_check_error(&format!(
                "Pattern should start with a constructor, found {:?}",
                other
            )))
        }
    };
    let inductive_name = environment
        .constructor_type_of(&constructor_name)
        .ok_or_else(|| {
            LofError::type_check_error(&format!(
                "{} is not the constructor of any inductive type",
                constructor_name
            ))
        })?;
    match get_applied_function(matched_type) {
        Variable(name, _) if name == inductive_name => {}
        _ => {
            return Err(LofError::type_mismatch(
                format!("pattern `{:?}`", pattern),
                matched_type,
                &inductive_name,
            ))
        }
    }
    let param_count = environment
        .get_inductive_param_count(&inductive_name)
        .unwrap_or(0);
    let actual_params = application_args(matched_type);
    if actual_params.len() < param_count {
        return Err(LofError::type_check_error(&format!(
            "Matched type {:?} is not a fully applied instance of {}",
            matched_type, inductive_name
        )));
    }

    let mut constructor_type = environment
        .get_variable_type(&constructor_name)
        .ok_or_else(|| LofError::unbound_variable(&constructor_name))?;
    let arguments = application_args(pattern);

    for (position, argument) in arguments.iter().enumerate() {
        let (binder, domain, codomain) = match constructor_type {
            Product(binder, domain, codomain) => (binder, *domain, *codomain),
            _ => {
                return Err(LofError::arity_mismatch(
                    format!("constructor pattern {}", constructor_name),
                    position,
                    arguments.len(),
                ))
            }
        };

        let value = if position < param_count {
            let actual = actual_params[position].to_owned();
            match argument {
                // every variable is a binder, see `pattern_binder_names`
                Variable(name, _) => entries.push(
                    PatternEntry::Define(name.to_owned(), actual.clone(), domain),
                ),
                // a hole in a parameter position stands for the parameter itself
                Meta(HOLE_INDEX) => {}
                _ => {
                    return Err(LofError::type_check_error(&format!(
                        "Parameter positions of pattern {:?} can only hold a variable or `?`, found {:?}",
                        pattern, argument
                    )))
                }
            }
            actual
        } else {
            match argument {
                // every variable is a binder (`_` is an anonymous one), see
                // `pattern_binder_names`
                Variable(name, _) => {
                    entries.push(PatternEntry::Assume(name.to_owned(), domain))
                }
                Application(_, _) => {
                    let nested_type = Cic::normalize_term(environment, &domain);
                    solve_pattern(environment, argument, &nested_type, entries)?;
                }
                _ => {
                    return Err(LofError::type_check_error(&format!(
                        "Constructor argument positions of pattern {:?} can only hold a variable or a nested pattern, found {:?}",
                        pattern, argument
                    )))
                }
            }
            argument.to_owned()
        };

        constructor_type = substitute_and_lift(&codomain, &binder, &value);
    }

    if let Product(_, _, _) = constructor_type {
        return Err(LofError::type_check_error(&format!(
            "Pattern {:?} doesnt fully apply constructor {}",
            pattern, constructor_name
        )));
    }

    Ok(constructor_name)
}

/// Runs `callable` with every pattern entry in the environment
pub fn with_pattern_entries<F: FnOnce(&mut Environment<Cic>) -> R, R>(
    environment: &mut Environment<Cic>,
    entries: &[PatternEntry],
    callable: F,
) -> R {
    match entries.split_first() {
        None => callable(environment),
        Some((PatternEntry::Assume(name, typee), rest)) => environment
            .with_local_assumption(name, typee, |local_env| {
                with_pattern_entries(local_env, rest, callable)
            }),
        Some((PatternEntry::Define(name, value, typee), rest)) => environment
            .with_local_substitution(
                name,
                value,
                &Some(typee.to_owned()),
                |local_env| with_pattern_entries(local_env, rest, callable),
            ),
    }
}
