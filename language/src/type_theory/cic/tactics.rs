//! CIC tactic engine. Tactics are part of the untrusted refinement layer:
//! every goal is a metavariable `Γ ⊢ ?g : T` of the refinement's
//! `MetaContext`, and each tactic solves the focused goal by assigning it a
//! piece of proof, possibly mentioning new goals (ie new metavariables).
//! Once all goals are solved, the proof term is the instantiation of the
//! root goal, which is then checked by the kernel like any other proof.
use super::cic::CicTerm;
use super::cic::CicTerm::{Abstraction, Meta, Product};
use super::cic_utils::{
    apply_arguments, localize, open_term, reclose_unique_binders, strip_unique_name,
    substitute_and_lift,
};
use super::refiner::{check, infer, refine_type, RefinerState};
use crate::error::LofError;
use crate::parser::api::Tactic::{self, Apply, Begin, Exact, Intro, Qed};
use crate::type_theory::cic::cic::Cic;
use crate::type_theory::environment::Environment;
use crate::type_theory::interface::Reducer;
use std::collections::VecDeque;

/// The goal being worked on by a tactic
struct Goal {
    /// index of the goal metavariable
    id: i32,
    /// its local context (local name, type), outermost first
    context: Vec<(String, CicTerm)>,
    /// its type, in normal form
    target: CicTerm,
}

impl Goal {
    /// Pairs of (user facing, local) names of the goal assumptions, used to
    /// resolve the names of terms elaborated outside of this context
    fn names(&self) -> Vec<(String, String)> {
        self.context
            .iter()
            .map(|(local, _)| (strip_unique_name(local).to_string(), local.to_owned()))
            .collect()
    }
}

/// Pops the first goal that is still open: goals might have been solved by
/// unification while working on some other goal
fn focus(state: &RefinerState, goals: &mut VecDeque<i32>) -> Option<i32> {
    while let Some(goal) = goals.pop_front() {
        if !state.metas.is_assigned(&goal) {
            return Some(goal);
        }
    }
    None
}

/// Runs the `tactics` proving `formula`, returning the constructed proof term
pub fn run_tactics(
    environment: &mut Environment<Cic>,
    formula: &CicTerm,
    tactics: &[Tactic<CicTerm, CicTerm>],
) -> Result<CicTerm, LofError> {
    let mut state = RefinerState::new();
    let root = state.fresh_meta(formula.to_owned());
    let mut goals: VecDeque<i32> = match root {
        Meta(id) => VecDeque::from([id]),
        _ => unreachable!("fresh metavariables are metavariables"),
    };

    for tactic in tactics {
        if let Begin() | Qed() = tactic {
            continue;
        }
        let id = focus(&state, &mut goals).ok_or_else(|| {
            LofError::custom(format!("No goals left to apply tactic {:?} to", tactic))
        })?;
        let context = state.metas.decl(&id).unwrap().context.clone();

        // the goal context is only in scope while working on this goal
        state.enter_locals(&context);
        let new_goals = environment.with_local_assumptions(&context, |local_env| {
            let target = Cic::normalize_term(
                local_env,
                &state.metas.meta_type(&id).unwrap(),
            );
            let goal = Goal {
                id,
                context: context.clone(),
                target,
            };
            run_tactic(local_env, &mut state, &goal, tactic)
        });
        state.exit_locals(context.len());

        for new_goal in new_goals?.into_iter().rev() {
            goals.push_front(new_goal);
        }
    }

    if let Some(id) = focus(&state, &mut goals) {
        let remaining = 1 + goals
            .iter()
            .filter(|goal| !state.metas.is_assigned(goal))
            .count();
        return Err(LofError::custom(format!(
            "Proof is incomplete: {} unproven goal(s), the first one is {:?}",
            remaining,
            state.metas.meta_type(&id).unwrap()
        )));
    }

    // the bodies of the abstractions built by `intro` are only known now
    let proof = state.finalize(&root)?;
    Ok(reclose_unique_binders(&proof))
}

/// Runs `tactic` on the focused `goal` (whose context is already in the
/// `environment` and in the `state` scope), returning the goals it opens
fn run_tactic(
    environment: &mut Environment<Cic>,
    state: &mut RefinerState,
    goal: &Goal,
    tactic: &Tactic<CicTerm, CicTerm>,
) -> Result<Vec<i32>, LofError> {
    match tactic {
        Intro(ass_name, ass_type) => run_intro(environment, state, goal, ass_name, ass_type),
        Exact(proof_term) => run_exact(environment, state, goal, proof_term),
        Apply(lemma) => run_apply(environment, state, goal, lemma),
        _ => Err(LofError::custom(format!(
            "Tactic {:?} currently not supported in CIC",
            tactic
        ))),
    }
}

/// `intro x : A` on a goal `Γ ⊢ ?g : Πy:A'.B` checks that A ≡ A' and assigns
/// `?g := λx:A'. ?h` with the new goal `Γ, x:A' ⊢ ?h : B`
fn run_intro(
    environment: &mut Environment<Cic>,
    state: &mut RefinerState,
    goal: &Goal,
    ass_name: &str,
    ass_type: &CicTerm,
) -> Result<Vec<i32>, LofError> {
    let (domain, codomain) = match &goal.target {
        Product(_, domain, codomain) => (domain, codomain),
        target => {
            return Err(LofError::custom(format!(
                "Intro tactic not allowed: current proof target {:?} is not a dependent product",
                target
            )))
        }
    };

    let ass_type = localize(ass_type, &goal.names());
    let ass_type = refine_type(environment, state, &ass_type)?;
    state.unify(
        environment,
        domain,
        &ass_type,
        &format!("assumption `{}`", ass_name),
    )?;

    let local = state.names.fresh_local_name(ass_name);
    let assumption = [(local.clone(), (**domain).to_owned())];
    state.enter_locals(&assumption);
    let new_goal = state.fresh_meta(open_term(codomain, &local));
    state.exit_locals(1);

    // the body of the abstraction refers to the introduced variable through
    // the local `local`, turned into a De Bruijn index once the proof term
    // is finalized (see `reclose_unique_binders`)
    state.metas.assign(
        goal.id,
        &Abstraction(local, domain.clone(), Box::new(new_goal.clone())),
    )?;
    match new_goal {
        Meta(id) => Ok(vec![id]),
        _ => unreachable!("fresh metavariables are metavariables"),
    }
}

/// `exact t` assigns `?g := t`, if the type of t matches the target
fn run_exact(
    environment: &mut Environment<Cic>,
    state: &mut RefinerState,
    goal: &Goal,
    proof_term: &CicTerm,
) -> Result<Vec<i32>, LofError> {
    let proof_term = localize(proof_term, &goal.names());
    let proof_term = check(environment, state, &proof_term, &goal.target, "exact tactic")?;
    state.metas.assign(goal.id, &proof_term)?;

    Ok(vec![])
}

/// `apply l` with `l : Πx1:A1...Πxn:An. C` unifies C with the target,
/// assigning `?g := l ?x1 ... ?xn`: every premise not determined by
/// unification becomes a new goal. It uses the least number of premises
/// needed for the conclusion to match the target
fn run_apply(
    environment: &mut Environment<Cic>,
    state: &mut RefinerState,
    goal: &Goal,
    lemma: &CicTerm,
) -> Result<Vec<i32>, LofError> {
    let lemma = localize(lemma, &goal.names());
    let (lemma, lemma_type) = infer(environment, state, &lemma)?;

    let mut conclusion =
        Cic::normalize_term(environment, &state.metas.instantiate(&lemma_type));
    let mut premises: Vec<CicTerm> = vec![];
    let mut last_error: LofError;
    loop {
        // try to close the goal using the premises collected so far
        let mut attempt = state.clone();
        match attempt.unify(environment, &goal.target, &conclusion, "apply tactic") {
            Ok(()) => {
                *state = attempt;
                break;
            }
            Err(error) => last_error = error,
        }

        // otherwise take one more premise
        match conclusion {
            Product(var_name, domain, codomain) => {
                let premise = state.fresh_meta(*domain);
                conclusion = Cic::normalize_term(
                    environment,
                    &substitute_and_lift(&codomain, &var_name, &premise),
                );
                premises.push(premise);
            }
            _ => {
                return Err(LofError::custom(format!(
                    "Cannot apply {:?} of type {:?} to target {:?}: {}",
                    lemma, lemma_type, goal.target, last_error
                )))
            }
        }
    }

    state
        .metas
        .assign(goal.id, &apply_arguments(&lemma, premises.clone()))?;
    // the premises not determined by unification are the new goals
    Ok(premises
        .iter()
        .filter_map(|premise| match premise {
            Meta(id) if !state.metas.is_assigned(id) => Some(*id),
            _ => None,
        })
        .collect())
}

//########################### UNIT TESTS
#[cfg(test)]
mod unit_tests {
    use crate::{
        parser::api::Tactic::{Apply, Exact, Intro},
        type_theory::{
            cic::{
                cic::{
                    Cic,
                    CicTerm::{Abstraction, Application, Meta, Product, Sort, Variable},
                    NameKind, HOLE_INDEX,
                },
                tactics::run_tactics,
            },
            interface::{Kernel, TypeTheory},
        },
    };

    fn constant(name: &str) -> crate::type_theory::cic::cic::CicTerm {
        Variable(name.to_string(), NameKind::Const())
    }

    #[test]
    fn test_intro() {
        let nat = constant("Nat");
        let mut test_env = Cic::default_environment();
        test_env.add_to_context("Nat", &Sort("TYPE".to_string()));
        test_env.add_to_context("z", &nat);
        let nat_to_nat = Product(
            "n".to_string(),
            Box::new(nat.clone()),
            Box::new(nat.clone()),
        );

        let proof = run_tactics(
            &mut test_env,
            &nat_to_nat,
            &[Intro("n".to_string(), nat.clone()), Exact(constant("z"))],
        );
        assert_eq!(
            proof,
            Ok(Abstraction(
                "n".to_string(),
                Box::new(nat.clone()),
                Box::new(constant("z")),
            )),
            "Intro tactic doesnt build an abstraction"
        );

        assert!(
            run_tactics(
                &mut test_env,
                &nat_to_nat,
                &[Intro("ass".to_string(), Meta(HOLE_INDEX)), Exact(constant("z"))],
            )
            .is_ok(),
            "Intro tactic isnt working with unspecified assumption type"
        );

        assert!(
            run_tactics(
                &mut test_env,
                &nat_to_nat,
                &[Intro("ass".to_string(), Sort("TYPE".to_string()))],
            )
            .is_err(),
            "Intro tactic accepts an assumption of the wrong type"
        );

        assert!(
            run_tactics(
                &mut test_env,
                &nat,
                &[Intro("ass".to_string(), nat.clone())],
            )
            .is_err(),
            "Intro tactic accepts tactic with unassumable target"
        );

        assert!(
            run_tactics(
                &mut test_env,
                &nat_to_nat,
                &[Intro("n".to_string(), nat.clone())],
            )
            .is_err(),
            "Incomplete proofs are accepted"
        );
    }

    #[test]
    fn test_intro_exposes_variable_to_later_tactics() {
        let nat = constant("Nat");
        let mut test_env = Cic::default_environment();
        test_env.add_to_context("Nat", &Sort("TYPE".to_string()));

        // Πn:Nat. Nat proven by λn:Nat. n
        let target = Product(
            "n".to_string(),
            Box::new(nat.clone()),
            Box::new(nat.clone()),
        );
        let proof = run_tactics(
            &mut test_env,
            &target,
            &[Intro("n".to_string(), nat.clone()), Exact(constant("n"))],
        )
        .unwrap();

        assert_eq!(
            proof,
            Abstraction(
                "n".to_string(),
                Box::new(nat.clone()),
                Box::new(Variable("n".to_string(), NameKind::Bound(0))),
            ),
            "the introduced variable must be bound by the constructed abstraction"
        );
        assert_eq!(
            test_env.get_variable_type("n"),
            None,
            "tactics must not leak assumptions into the environment"
        );
        assert_eq!(Cic::type_check_term(&proof, &mut test_env), Ok(target));
    }

    #[test]
    fn test_exact() {
        let nat = constant("Nat");
        let mut test_env = Cic::default_environment();
        test_env.add_to_context("Nat", &Sort("TYPE".to_string()));
        test_env.add_to_context("Bool", &Sort("TYPE".to_string()));
        test_env.add_to_context("n", &nat);

        assert_eq!(
            run_tactics(&mut test_env, &nat, &[Exact(constant("n"))]),
            Ok(constant("n")),
            "Exact tactic checking doesnt accept simple type inhabiting"
        );
        assert!(
            run_tactics(&mut test_env, &constant("Bool"), &[Exact(constant("n"))])
                .is_err(),
            "Exact tactic checking accepts term with wrong type"
        );
    }

    #[test]
    fn test_apply() {
        let mut test_env = Cic::default_environment();
        let premise1 = constant("Premise1");
        let premise2 = constant("Premise2");
        let conclusion = constant("Conclusion");
        test_env.add_to_context("Premise1", &Sort("PROP".to_string()));
        test_env.add_to_context("Premise2", &Sort("PROP".to_string()));
        test_env.add_to_context("Conclusion", &Sort("PROP".to_string()));
        test_env.add_to_context("p1", &premise1);
        test_env.add_to_context("p2", &premise2);

        let simple_implication = Product(
            "_".to_string(),
            Box::new(premise1.clone()),
            Box::new(conclusion.clone()),
        );
        test_env.add_to_context("simple_lemma", &simple_implication);
        assert_eq!(
            run_tactics(
                &mut test_env,
                &conclusion,
                &[Apply(constant("simple_lemma")), Exact(constant("p1"))],
            ),
            Ok(Application(
                Box::new(constant("simple_lemma")),
                Box::new(constant("p1"))
            )),
            "The constructed proof is not the expected one"
        );

        let double_implication = Product(
            "_".to_string(),
            Box::new(premise1.clone()),
            Box::new(Product(
                "_".to_string(),
                Box::new(premise2.clone()),
                Box::new(conclusion.clone()),
            )),
        );
        test_env.add_to_context("double_lemma", &double_implication);
        let proof = run_tactics(
            &mut test_env,
            &conclusion,
            &[
                Apply(constant("double_lemma")),
                Exact(constant("p1")),
                Exact(constant("p2")),
            ],
        );
        assert_eq!(
            proof,
            Ok(Application(
                Box::new(Application(
                    Box::new(constant("double_lemma")),
                    Box::new(constant("p1"))
                )),
                Box::new(constant("p2"))
            )),
            "Apply tactic doesnt track all premises of the applied lemma, in order"
        );
        assert_eq!(
            Cic::type_check_term(&proof.unwrap(), &mut test_env),
            Ok(conclusion.clone())
        );

        assert!(
            run_tactics(
                &mut test_env,
                &conclusion,
                &[Apply(constant("double_lemma")), Exact(constant("p1"))],
            )
            .is_err(),
            "Apply tactic loses premises"
        );
        assert!(
            run_tactics(
                &mut test_env,
                &conclusion,
                &[
                    Apply(constant("double_lemma")),
                    Exact(constant("p2")),
                    Exact(constant("p1"))
                ],
            )
            .is_err(),
            "Apply tactic premises are not proven in order"
        );
    }
}
