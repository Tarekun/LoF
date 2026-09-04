use super::cic::CicTerm;
use super::cic::CicTerm::{Abstraction, Application, Product};
use super::cic_utils::swap_body;
use crate::error::LofError;
use crate::parser::api::Tactic::{self, Apply, Exact, Intro};
use crate::type_theory::cic::cic::Cic;
use crate::type_theory::cic::cic_utils::{get_arg_types, get_prod_innermost};
use crate::type_theory::environment::Environment;
use crate::type_theory::interface::{
    Interactive, Kernel, Reducer, Refiner, TypeInference, TypeTheory,
};

pub fn type_check_tactic(
    environment: &mut Environment<Cic>,
    tactic: &Tactic<CicTerm>,
    target: &CicTerm,
    partial_proof: &CicTerm,
) -> Result<(CicTerm, Vec<CicTerm>), LofError> {
    match tactic {
        Intro(ass_name, ass_type) => type_check_intro(
            environment,
            target,
            partial_proof,
            ass_name,
            ass_type,
        ),
        Exact(proof_term) => {
            type_check_exact(environment, target, partial_proof, proof_term)
        }
        Apply(lemma) => {
            type_check_apply(environment, target, partial_proof, lemma)
        }
        _ => Err(LofError::custom(format!(
            "Tactic {:?} currently not type-checkable in CIC",
            tactic
        ))),
    }
}
//
//
fn type_check_intro(
    _: &mut Environment<Cic>,
    target: &CicTerm,
    partial_proof: &CicTerm,
    ass_name: &str,
    ass_type: &CicTerm,
) -> Result<(CicTerm, Vec<CicTerm>), LofError> {
    match target {
        Product(_, domain, codomain) => {
            if Cic::base_type_equality(ass_type, domain).is_ok() {
                let partial_proof = swap_body(partial_proof, &Abstraction(
                    ass_name.to_string(),
                    Box::new(ass_type.to_owned()),
                    Box::new(Cic::proof_hole())
                ));

                Ok((partial_proof, vec![(**codomain).clone()]))
            } else {
                Err(LofError::type_mismatch(
                    format!("assumption `{}`", ass_name),
                    domain,
                    ass_type,
                ))
            }
        },
        _ => {
            Err(LofError::custom(format!(
                "Intro tactic not allowed: current proof target {:?} is not a dependent product",
                target
            )))
        }
    }
}
//
//
fn type_check_exact(
    environment: &mut Environment<Cic>,
    target: &CicTerm,
    partial_proof: &CicTerm,
    proof_term: &CicTerm,
) -> Result<(CicTerm, Vec<CicTerm>), LofError> {
    // TODO reevaluate if normalization is needed here: normal forms are already computed by CIC unification
    let proof_type = Cic::type_check_term(proof_term, environment)?;
    let proof_type_reduced = Cic::normalize_term(environment, &proof_type);
    let target_reduced = Cic::normalize_term(environment, target);

    Cic::types_unify(environment, &proof_type_reduced, &target_reduced)?;
    Ok((swap_body(partial_proof, proof_term), vec![]))
}
//
//
fn type_check_apply(
    environment: &mut Environment<Cic>,
    target: &CicTerm,
    partial_proof: &CicTerm,
    lemma: &CicTerm,
) -> Result<(CicTerm, Vec<CicTerm>), LofError> {
    let lemma_type = Cic::type_check_term(lemma, environment)?;
    // TODO see if i should be able to use a bigger term than the innermost as conclusion to unify
    let conclusion = get_prod_innermost(&lemma_type);
    if Cic::type_unify(target, conclusion).is_ok() {
        let premises = get_arg_types(&lemma_type);
        let new_proof = swap_body(
            partial_proof,
            &Application(
                Box::new(lemma.to_owned()),
                Box::new(Cic::proof_hole()),
            ),
        );

        Ok((new_proof, premises))
    } else {
        Err(LofError::unification_failure(target, &lemma_type))
    }
}

//########################### UNIT TESTS
#[cfg(test)]
mod unit_tests {
    use crate::{
        parser::api::Tactic::{Apply, Intro},
        type_theory::{
            cic::{
                cic::{
                    Cic,
                    CicTerm::{
                        Abstraction, Application, Meta, Product, Sort, Variable,
                    },
                    GLOBAL_INDEX,
                },
                tactics::{
                    type_check_exact, type_check_intro, type_check_tactic,
                },
            },
            interface::{Interactive, TypeTheory},
        },
    };

    #[test]
    fn test_intro() {
        let nat = Variable("Nat".to_string(), GLOBAL_INDEX);
        let mut test_env = Cic::default_environment();

        assert_eq!(
            type_check_intro(
                &mut test_env,
                &Product(
                    "n".to_string(),
                    Box::new(nat.clone()),
                    Box::new(nat.clone()),
                ),
                &Cic::proof_hole(),
                "n",
                &nat.clone(),
            ),
            Ok((
                Abstraction(
                    "n".to_string(),
                    Box::new(nat.clone()),
                    Box::new(Cic::proof_hole()),
                ),
                vec![nat.clone()]
            )),
            "Intro tactic checking isnt working as expected"
        );
        assert!(
            type_check_intro(
                &mut test_env,
                &Product(
                    "n".to_string(),
                    Box::new(nat.clone()),
                    Box::new(nat.clone()),
                ),
                &Cic::proof_hole(),
                "ass",
                &nat.clone(),
            ).is_ok(),
            "Intro tactic checking isnt working with missmatched variable names"
        );

        assert!(
            type_check_intro(
                &mut test_env,
                &Product(
                    "n".to_string(),
                    Box::new(nat.clone()),
                    Box::new(nat.clone()),
                ),
                &Cic::proof_hole(),
                "ass",
                &Meta(0),
            ).is_ok(),
            "Intro tactic checking isnt working with unspecified assumption type"
        );

        assert!(
            type_check_tactic(
                &mut test_env,
                &Intro("ass".to_string(), nat.clone()),
                &Product(
                    "n".to_string(),
                    Box::new(nat.clone()),
                    Box::new(nat.clone()),
                ),
                &Cic::proof_hole()
            )
            .is_ok(),
            "Top-level tactic checker doesnt support intro"
        );

        assert!(
            type_check_intro(
                &mut test_env,
                &nat,
                &Cic::proof_hole(),
                "ass",
                &nat.clone(),
            )
            .is_err(),
            "Intro tactic checking accepts tactic with unassumable target"
        );
    }

    #[test]
    fn test_exact() {
        let nat = Variable("Nat".to_string(), GLOBAL_INDEX);
        let boolean = Variable("Bool".to_string(), GLOBAL_INDEX);
        let mut test_env = Cic::default_environment();
        test_env.add_to_context("Nat", &Sort("TYPE".to_string()));
        test_env.add_to_context("Bool", &Sort("TYPE".to_string()));
        test_env.add_to_context("n", &nat);

        let proof_term = Variable("n".to_string(), GLOBAL_INDEX);
        assert_eq!(
            type_check_exact(
                &mut test_env,
                &nat,
                &Cic::proof_hole(),
                &proof_term
            ),
            Ok((proof_term.clone(), vec![])),
            "Exact tactic checking doesnt accept simple type inhabiting"
        );
        assert!(
            type_check_exact(
                &mut test_env,
                &boolean,
                &Cic::proof_hole(),
                &proof_term
            )
            .is_err(),
            "Exact tactic checking accepts term with wrong type"
        );
    }

    #[test]
    fn test_apply() {
        let mut test_env = Cic::default_environment();
        let premise1 = Variable("Premise1".to_string(), GLOBAL_INDEX);
        let premise2 = Variable("Premise2".to_string(), GLOBAL_INDEX);
        let conclusion = Variable("Conclusion".to_string(), GLOBAL_INDEX);
        test_env.add_to_context("Premise1", &Sort("PROP".to_string()));
        test_env.add_to_context("Premise2", &Sort("PROP".to_string()));
        test_env.add_to_context("Conclusion", &Sort("PROP".to_string()));

        let simple_implication = Product(
            "_".to_string(),
            Box::new(premise1.clone()),
            Box::new(conclusion.clone()),
        );
        test_env.add_to_context("simple_lemma", &simple_implication);
        let simple_lemma = Variable("simple_lemma".to_string(), GLOBAL_INDEX);
        let hole = Cic::proof_hole();

        let (proof, subgoals) = Cic::type_check_tactic(
            &mut test_env,
            &Apply(simple_lemma.clone()),
            &conclusion,
            &hole,
        )
        .unwrap();
        assert_eq!(
            proof,
            Application(Box::new(simple_lemma), Box::new(hole.clone())),
            "The constructed partial proof is not the expected one"
        );
        assert_eq!(subgoals, vec![premise1.clone()], "The returned subgoals dont match the premises of the applied implication");

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
        let double_lemma = Variable("double_lemma".to_string(), GLOBAL_INDEX);
        let (_, subgoals) = Cic::type_check_tactic(
            &mut test_env,
            &Apply(double_lemma),
            &conclusion,
            &hole,
        )
        .unwrap();
        assert_eq!(
            subgoals,
            vec![premise1, premise2],
            "Apply tactic doesnt track all premises of the applied lemma"
        );
    }
}
