use super::cic::CicTerm;
use super::cic::CicTerm::{
    Abstraction, Application, Let, Match, Meta, Product, Sort, Variable,
};
use super::metavariables::{MetaContext, NameGenerator};
use crate::error::LofError;
use crate::type_theory::cic::cic::{Cic, NameKind};
use crate::type_theory::cic::cic_utils::{
    application_args, get_applied_function, is_constant, open_term,
    substitute, substitute_meta,
};
use crate::type_theory::commons::unification::{ucs, Substitution};
use crate::type_theory::environment::Environment;
use crate::type_theory::grammars::traits::AlphaEquiv;
use crate::type_theory::interface::Reducer;
use std::collections::VecDeque;

/// Outcome of a single unification step
enum Step {
    /// constraint solved
    Done,
    /// constraint reduced to simpler ones
    Split(Vec<(CicTerm, CicTerm)>),
    /// constraint cant be solved yet (flexible application head)
    Postpone,
}

fn is_flexible(term: &CicTerm) -> bool {
    matches!(term, Application(_, _))
        && matches!(get_applied_function(term), Meta(_))
}

/// One step of first order unification of `expected ≐ actual` modulo
/// βδι-reduction. Only metavariables are unification variables: every other
/// name (bound, local or constant) is rigid
fn unify_step(
    environment: &Environment<Cic>,
    expected: &CicTerm,
    actual: &CicTerm,
    metas: &mut MetaContext,
    names: &mut NameGenerator,
) -> Result<Step, LofError> {
    let expected =
        Cic::normalize_term(environment, &metas.instantiate(expected));
    let actual = Cic::normalize_term(environment, &metas.instantiate(actual));

    if expected.alpha_equivalent(&actual) {
        return Ok(Step::Done);
    }

    let mismatch = || LofError::unification_failure(&expected, &actual);
    match (&expected, &actual) {
        (Meta(index), other) | (other, Meta(index)) => {
            metas.assign(*index, other)?;
            Ok(Step::Done)
        }
        // sorts are unified leniently: the kernel decides on cumulativity
        (Sort(s1), Sort(s2)) => {
            let universes = ["PROP", "TYPE"];
            if universes.contains(&s1.as_str())
                && universes.contains(&s2.as_str())
            {
                Ok(Step::Done)
            } else {
                Err(mismatch())
            }
        }
        (Product(n1, d1, c1), Product(_, d2, c2))
        | (Abstraction(n1, d1, c1), Abstraction(_, d2, c2)) => {
            // bodies are compared opened with the same fresh local
            let local = names.fresh_local_name(n1);
            Ok(Step::Split(vec![
                ((**d1).to_owned(), (**d2).to_owned()),
                (open_term(c1, &local), open_term(c2, &local)),
            ]))
        }
        _ if is_flexible(&expected) || is_flexible(&actual) => {
            Ok(Step::Postpone)
        }
        (Application(_, _), Application(_, _)) => {
            let args1 = application_args(&expected);
            let args2 = application_args(&actual);
            if args1.len() != args2.len() {
                return Err(mismatch());
            }
            let mut subproblems = vec![(
                get_applied_function(&expected),
                get_applied_function(&actual),
            )];
            subproblems.extend(args1.into_iter().zip(args2.into_iter()));
            Ok(Step::Split(subproblems))
        }
        (Let(_, _, v1, s1), Let(_, _, v2, s2)) => Ok(Step::Split(vec![
            ((**v1).to_owned(), (**v2).to_owned()),
            ((**s1).to_owned(), (**s2).to_owned()),
        ])),
        (Match(m1, branches1), Match(m2, branches2)) => {
            if branches1.len() != branches2.len()
                || branches1
                    .iter()
                    .zip(branches2.iter())
                    .any(|((p1, _), (p2, _))| !p1.alpha_equivalent(p2))
            {
                return Err(mismatch());
            }
            let mut subproblems = vec![((**m1).to_owned(), (**m2).to_owned())];
            subproblems.extend(
                branches1
                    .iter()
                    .zip(branches2.iter())
                    .map(|((_, b1), (_, b2))| (b1.to_owned(), b2.to_owned())),
            );
            Ok(Step::Split(subproblems))
        }
        _ => Err(mismatch()),
    }
}

/// Unifies `expected ≐ actual` modulo βδι-reduction, assigning the
/// metavariables of `metas`. Constraints with a flexible head (eg `?f x`)
/// cannot be solved yet: they're postponed in `metas`, and retried every time
/// some progress is made. `names` supplies the locals binders are opened
/// with when compared
pub fn unify(
    environment: &Environment<Cic>,
    metas: &mut MetaContext,
    names: &mut NameGenerator,
    expected: &CicTerm,
    actual: &CicTerm,
) -> Result<(), LofError> {
    let mut queue = VecDeque::from([(expected.to_owned(), actual.to_owned())]);
    loop {
        let mut progress = false;
        while let Some((expected, actual)) = queue.pop_front() {
            match unify_step(environment, &expected, &actual, metas, names)? {
                Step::Done => progress = true,
                Step::Split(subproblems) => {
                    progress = true;
                    // solve the subproblems before moving on (depth first)
                    for subproblem in subproblems.into_iter().rev() {
                        queue.push_front(subproblem);
                    }
                }
                Step::Postpone => metas.postpone(expected, actual),
            }
        }

        if !progress {
            return Ok(());
        }
        queue.extend(metas.take_postponed());
        if queue.is_empty() {
            return Ok(());
        }
    }
}

//########################### TACTICS UNIFICATION
// First order unification treating metavariables and non constant variables
// alike, still used by the tactic engine
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
        (Meta(_), Variable(_, NameKind::Const()))
        | (Variable(_, NameKind::Const()), Meta(_)) => true,
        // free variables and constants must match by name
        (
            Variable(name1, NameKind::Local()),
            Variable(name2, NameKind::Local()),
        )
        | (
            Variable(name1, NameKind::Const()),
            Variable(name2, NameKind::Const()),
        ) => name1 == name2,
        // bound variables must match by index, implementing α-equivalence
        (Variable(_, dbi1), Variable(_, dbi2)) => dbi1 == dbi2,
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
    environment: &Environment<Cic>,
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
        // TODO: this now applies both first and second order substitution
        // review if its actually what i want implemented here
        if let Some(meta_idx) = idx.strip_prefix("metavariable_") {
            substitute_meta(term, &meta_idx.parse().unwrap(), arg)
        } else if let Some(var_name) = idx.strip_prefix("variable_") {
            substitute(term, var_name, arg)
        } else {
            term.clone()
        }
    }))
}

//########################### TACTICS UNIFICATION

#[cfg(test)]
#[path = "../../tests/type_theory/cic/unification.rs"]
mod tests;
