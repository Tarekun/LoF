use super::cic::CicTerm;
use super::cic::CicTerm::{
    Abstraction, Application, Let, Match, Meta, Product, Sort, Variable,
};
use crate::error::LofError;
use crate::type_theory::cic::cic::{Cic, GLOBAL_INDEX};
use crate::type_theory::cic::cic_utils::{
    application_args, get_applied_function, get_arg_types, is_constant,
    substitute, substitute_meta,
};
use crate::type_theory::commons::unification::{ucs, Substitution};
use crate::type_theory::environment::Environment;
use crate::type_theory::interface::{Kernel, Reducer};
use std::collections::VecDeque;

fn is_substitutable(term: &CicTerm) -> Option<String> {
    match term {
        Meta(idx) => Some(format!("metavariable_{}", idx)),
        Variable(var_name, _dbi) => {
            if !is_constant(term) {
                Some(format!("variable_{}", var_name))
            } else {
                None
            }
        }
        _ => None,
    }
}
fn structurally_equal(term1: &CicTerm, term2: &CicTerm) -> bool {
    match (term1, term2) {
        (Sort(_), Sort(_)) => true,
        (Meta(_), Meta(_)) => true,
        // TODO this is a bug: ? and Nat should be able to unify the same way x and 3 can at FO
        // however this needs to make sure the Variable actually is a type name and not some random term
        // idx == GLOBAL_INDEX is a current hack (global type names get assigned this value) but should be fixed
        (Meta(_), Variable(_, idx)) | (Variable(_, idx), Meta(_)) => {
            *idx == GLOBAL_INDEX
        }
        (Variable(name1, dbi1), Variable(name2, dbi2)) => {
            // same dbi1 and if they are global constants then also the constant symbols must be the same
            dbi1 == dbi2 && (!is_constant(term1) || name1 == name2)
        }
        (Abstraction(_, type1, body1), Abstraction(_, type2, body2)) => {
            structurally_equal(type1, type2) && structurally_equal(body1, body2)
        }
        (Product(_, type1, body1), Product(_, type2, body2)) => {
            structurally_equal(type1, type2) && structurally_equal(body1, body2)
        }
        (Application(_, _), Application(_, _)) => {
            // TODO: review if this is enough/too much
            structurally_equal(
                &get_applied_function(term1),
                &get_applied_function(term2),
            ) && application_args(term1).len() == application_args(term2).len()
        }
        (Let(_, _, body1, scope1), Let(_, _, body2, scope2)) => {
            structurally_equal(body1, body2)
                && structurally_equal(scope1, scope2)
        }
        // TODO this explosion is order dependent on the branches, itd be nice to
        // reorder branches in some deterministic way
        (Match(matched1, branches1), Match(matched2, branches2)) => {
            if !structurally_equal(matched1, matched2) {
                return false;
            }
            for (b1, b2) in branches1.iter().zip(branches2.iter()) {
                let (pattern1, body1) = b1;
                let (pattern2, body2) = b2;
                if !(structurally_equal(pattern1, pattern2)
                    || structurally_equal(body1, body2))
                {
                    return false;
                }
            }
            true
        }
        _ => false,
    }
}
fn explode(term: &CicTerm) -> Vec<CicTerm> {
    match term {
        Abstraction(_, var_type, body) => {
            vec![(**var_type).to_owned(), (**body).to_owned()]
        }
        Product(_, var_type, body) => {
            vec![(**var_type).to_owned(), (**body).to_owned()]
        }
        Application(left, right) => {
            vec![(**left).to_owned(), (**right).to_owned()]
        }
        // TODO this explosion is order dependent on the branches, itd be nice to
        // reorder branches in some deterministic way
        Match(matched_term, branches) => {
            let mut subexpressions = vec![(**matched_term).to_owned()];
            for (pattern, body) in branches {
                subexpressions.push(pattern.to_owned());
                subexpressions.push(body.to_owned());
            }
            subexpressions
        }
        // TODO figure out what to do with opt_type
        Let(_, opt_type, body, scope) => {
            vec![(**body).to_owned(), (**scope).to_owned()]
        }
        _ => vec![],
    }
}
fn occurs_meta_check(meta_index: i32, term: &CicTerm) -> Result<(), LofError> {
    match term {
        Meta(index) => {
            if meta_index == *index {
                Err(LofError::occurs_check_cyclic(format!(
                    "metavariable_{}",
                    meta_index
                )))
            } else {
                Ok(())
            }
        }
        Abstraction(_, arg_type, body) => {
            occurs_meta_check(meta_index, arg_type)?;
            occurs_meta_check(meta_index, body)
        }
        Product(_, arg_type, body) => {
            occurs_meta_check(meta_index, arg_type)?;
            occurs_meta_check(meta_index, body)
        }
        Application(left, right) => {
            occurs_meta_check(meta_index, &left)?;
            occurs_meta_check(meta_index, &right)
        }
        Match(matched, branches) => {
            for (pattern, body) in branches {
                occurs_meta_check(meta_index, pattern)?;
                occurs_meta_check(meta_index, body)?;
            }
            occurs_meta_check(meta_index, &matched)
        }
        Let(_, opt_type, body, scope) => {
            if let Some(typ) = &**opt_type {
                occurs_meta_check(meta_index, typ)?;
            }
            occurs_meta_check(meta_index, body)?;
            occurs_meta_check(meta_index, scope)
        }
        _ => Ok(()),
    }
}
fn occurs_var_check(term: &CicTerm, name: &str) -> bool {
    match term {
        Sort(_) => false,
        Variable(var_name, _) => var_name == name,
        Abstraction(var_name, var_type, body) => {
            (var_name != name && occurs_var_check(var_type, name))
                || (var_name != name && occurs_var_check(body, name))
        }
        Product(var_name, var_type, body) => {
            (var_name != name && occurs_var_check(var_type, name))
                || (var_name != name && occurs_var_check(body, name))
        }
        Application(func, arg) => {
            occurs_var_check(func, name) || occurs_var_check(arg, name)
        }
        Match(scrutinee, branches) => {
            occurs_var_check(scrutinee, name)
                || branches.iter().any(|(pattern, body)| {
                    occurs_var_check(pattern, name)
                        || occurs_var_check(body, name)
                })
        }
        Let(var_name, var_type, value, body) => {
            let type_occurs = if let Some(ty) = var_type.as_ref() {
                occurs_var_check(ty, name)
            } else {
                false
            };
            (var_name != name && type_occurs)
                || (var_name != name && occurs_var_check(value, name))
                || (var_name != name && occurs_var_check(body, name))
        }
        Meta(_) => false,
    }
}
fn occurs(term: &CicTerm, name: &str) -> bool {
    if name.starts_with("metavariable_") {
        occurs_meta_check(
            name.strip_prefix("metavariable_").unwrap().parse().unwrap(),
            term,
        )
        .is_err()
    } else if name.starts_with("variable_") {
        occurs_var_check(term, name.strip_prefix("variable_").unwrap())
    } else {
        panic!("CIC occurs check is being called on a name that isnt formed by any of the 2 prefixes used. this shuold NOT happen");
    }
}

/// Binary second order unification of meta-variable for type inference
/// This function does NOT support normalization of terms to be unified and hence
/// does not require an environment to be passed
pub fn cic_so_unification(
    term1: &CicTerm,
    term2: &CicTerm,
) -> Result<Substitution<CicTerm>, LofError> {
    solve_unifications_unnormalized(VecDeque::from([(
        term1.to_owned(),
        term2.to_owned(),
    )]))
}

pub fn cic_solve_unifications(
    constraints: Vec<(CicTerm, CicTerm)>,
    environment: &mut Environment<Cic>,
) -> Result<Substitution<CicTerm>, LofError> {
    let mut reduced_constraints = VecDeque::new();
    for (left, right) in constraints {
        reduced_constraints.push_back((
            Cic::normalize_term(environment, &left),
            Cic::normalize_term(environment, &right),
        ));
        // reduced_constraints.push_back((left, right));
    }

    solve_unifications_unnormalized(reduced_constraints)
}

fn solve_unifications_unnormalized(
    constraints: VecDeque<(CicTerm, CicTerm)>,
) -> Result<Substitution<CicTerm>, LofError> {
    Ok(ucs(
        &mut Substitution::empty(),
        constraints,
        is_substitutable,
        structurally_equal,
        explode,
        occurs,
    )?
    .reduce(|term, idx, arg| {
        // Same metavariable_/variable_ dispatch as `cic_apply_unifier`: a
        // substitution key from `is_substitutable` is either a `Meta`
        // (substituted by index) or an ordinary bound `Variable`
        // (substituted by name) - the two need different substitution
        // functions.
        if let Some(meta_idx) = idx.strip_prefix("metavariable_") {
            substitute_meta(term, &meta_idx.parse().unwrap(), arg)
        } else if let Some(var_name) = idx.strip_prefix("variable_") {
            substitute(term, var_name, arg)
        } else {
            term.clone()
        }
    }))
}

pub fn cic_collect_unifications(
    term: &CicTerm,
    environment: &mut Environment<Cic>,
) -> Result<Vec<(CicTerm, CicTerm)>, LofError> {
    match term {
        Abstraction(var_name, var_type, body) => {
            let type_cons = cic_collect_unifications(var_type, environment)?;
            let body_cons = environment.with_local_assumption(
                var_name,
                var_type,
                |local_env| cic_collect_unifications(body, local_env),
            )?;

            Ok([type_cons, body_cons].concat())
        }
        Application(fun, arg) => {
            let fun_cons = cic_collect_unifications(fun, environment)?;
            let arg_cons = cic_collect_unifications(arg, environment)?;

            let arg_type = Cic::type_check_term(arg, environment)?;
            let fun_type = Cic::type_check_term(fun, environment)?;
            let first_arg_type = &get_arg_types(&fun_type)[0];

            Ok([
                fun_cons,
                vec![(first_arg_type.to_owned(), arg_type)],
                arg_cons,
            ]
            .concat())
        }
        Product(var_name, domain, codomain) => {
            let domain_cons = cic_collect_unifications(domain, environment)?;
            let codomain_cons = environment.with_local_assumption(
                var_name,
                domain,
                |local_env| cic_collect_unifications(codomain, local_env),
            )?;

            Ok([domain_cons, codomain_cons].concat())
        }
        Let(_, opt_type, body, scope) => {
            let type_cons = match &**opt_type {
                Some(var_type) => {
                    cic_collect_unifications(var_type, environment)?
                }
                // TODO im pretty sure this should introduce the opt_type=body_type constraint
                None => vec![],
            };
            let body_cons = cic_collect_unifications(body, environment)?;
            let scope_cons = cic_collect_unifications(scope, environment)?;

            Ok([type_cons, body_cons, scope_cons].concat())
        }
        // TODO im pretty sure this branch should introduce constraints between the matched
        // term type and the produced pattern + all of the branches results
        Match(matched_term, branches) => {
            let matched_cons =
                cic_collect_unifications(matched_term, environment)?;
            let mut branch_cons = vec![];
            for (pattern, body) in branches {
                // NOTE: the pattern itself is a binding form (`s(nn)`
                // introduces `nn`), not an ordinary expression - it must
                // not be fed through `cic_collect_unifications` (which
                // would try to type-check `nn` as a reference before it's
                // bound). Only its bound variables (collected below) and
                // the branch body need constraints collected.

                // Bind the pattern's own variables (eg `nn` in `s(nn)`)
                // before recursing into the branch body, exactly like
                // `type_check_match` already does via `type_constr_vars` -
                // otherwise a body referencing a pattern variable (eg a
                // recursive call `plus(nn, m)`) fails with an unbound-
                // variable error the moment this collection pass is
                // triggered on a term containing the match (which ordinary
                // `fun` type-checking never does, since it checks a fun's
                // un-wrapped body with its own parameters already bound
                // manually - but validating an already-evaluated,
                // lambda-wrapped definition, as `transport` does, goes
                // through `i_type_check_abstraction` and hits this path).
                // Best-effort: if the pattern's head isn't a resolvable
                // constructor (eg a test exercising this in isolation,
                // without registering one), fall back to no assumptions
                // rather than aborting constraint collection entirely -
                // this pass collects whatever constraints it safely can,
                // it isn't the authoritative pattern type-checker (that's
                // `type_check_match`/`type_constr_vars` itself).
                let constructor = get_applied_function(pattern);
                let pattern_assumptions = match &constructor {
                    Variable(_, _) => Cic::type_check_term(
                        &constructor,
                        environment,
                    )
                    .ok()
                    .and_then(|constr_type| {
                        crate::type_theory::cic::type_check::type_constr_vars(
                            environment,
                            pattern,
                            &constr_type,
                        )
                        .ok()
                    })
                    .unwrap_or_default(),
                    _ => vec![],
                };
                let body_cons = environment.with_local_assumptions(
                    &pattern_assumptions,
                    |local_env| cic_collect_unifications(body, local_env),
                )?;
                branch_cons.extend(body_cons);
            }

            Ok([matched_cons, branch_cons].concat())
        }
        _ => Ok(vec![]),
    }
}
/// Folds a solved `substitution` back into `exp`. Substitution keys are
/// tagged by `is_substitutable` as either `metavariable_<idx>` (a `Meta`
/// placeholder, folded via `substitute_meta`) or `variable_<name>` (an
/// ordinary non-constant `Variable`, folded via the name-based `substitute`)
/// - the two kinds need different substitution functions, since a `Meta`
/// is addressed by index and an ordinary variable by name.
pub fn cic_apply_unifier(
    exp: &CicTerm,
    substitution: &Substitution<CicTerm>,
) -> CicTerm {
    let mut solved_exp = exp.to_owned();
    for index in substitution.names() {
        let value = substitution.get(index).unwrap();
        solved_exp = if let Some(meta_idx) =
            index.strip_prefix("metavariable_")
        {
            substitute_meta(&solved_exp, &meta_idx.parse().unwrap(), value)
        } else if let Some(var_name) = index.strip_prefix("variable_") {
            substitute(&solved_exp, var_name, value)
        } else {
            solved_exp
        };
    }
    solved_exp
}

#[cfg(test)]
#[path = "../../tests/type_theory/cic/unification.rs"]
mod tests;
