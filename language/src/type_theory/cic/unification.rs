use super::cic::CicTerm;
use super::cic::CicTerm::{
    Abstraction, Application, Let, Match, Meta, Product, Sort,
};
use super::metavariables::{MetaContext, NameGenerator};
use crate::error::LofError;
use crate::type_theory::cic::cic::Cic;
use crate::type_theory::cic::cic_utils::{
    application_args, get_applied_function, open_term,
};
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
        (Sort(s1), Sort(s2)) => match (s1.as_str(), s2.as_str()) {
            ("PROP" | "TYPE", "PROP" | "TYPE") => Ok(Step::Done),
            _ => Err(mismatch()),
        },
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
                Step::Postpone => metas.postponed.push((expected, actual)),
            }
        }

        if !progress {
            return Ok(());
        }
        queue.extend(std::mem::take(&mut metas.postponed));
        if queue.is_empty() {
            return Ok(());
        }
    }
}
#[cfg(test)]
#[path = "../../tests/type_theory/cic/unification.rs"]
mod tests;
