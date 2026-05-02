use super::cic::CicTerm;
use super::cic::CicTerm::{Abstraction, Application, Product};
use super::cic_utils::swap_body;
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
) -> Result<(CicTerm, Vec<CicTerm>), String> {
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
        _ => Err(format!(
            "Tactic {:?} currently not type-checkable in CIC",
            tactic
        )),
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
) -> Result<(CicTerm, Vec<CicTerm>), String> {
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
                Err(format!(
                    "{} has inconsistent type: expected {:?}, found {:?}", 
                    ass_name, domain, ass_type
                ))
            }
        },
        _ => {
            Err(format!(
                "Intro tactic not allowed: current proof target {:?} is not a dependent product",
                target
            ))
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
) -> Result<(CicTerm, Vec<CicTerm>), String> {
    // TODO reevaluate if normalization is needed here: normal forms are already computed by CIC unification
    let proof_type = Cic::type_check_term(proof_term, environment)?;
    let proof_type_reduced = Cic::normalize_term(environment, &proof_type);
    let target_reduced = Cic::normalize_term(environment, target);

    if Cic::types_unify(environment, &proof_type_reduced, &target_reduced) {
        Ok((swap_body(partial_proof, proof_term), vec![]))
    } else {
        Err(format!(
            "Term type and target don't unify: target is {:?} while expression has type {:?}",
            target, proof_type
        ))
    }
}
//
//
fn type_check_apply(
    _: &mut Environment<Cic>,
    target: &CicTerm,
    partial_proof: &CicTerm,
    lemma: &CicTerm,
) -> Result<(CicTerm, Vec<CicTerm>), String> {
    // TODO see if i should be able to use a bigger term than the innermost as conclusion to unify
    let conclusion = get_prod_innermost(lemma);
    if Cic::type_unify(target, conclusion).is_ok() {
        let premises = get_arg_types(lemma);
        let new_proof = swap_body(
            partial_proof,
            &Application(
                Box::new(lemma.to_owned()),
                Box::new(Cic::proof_hole()),
            ),
        );

        Ok((new_proof, premises))
    } else {
        Err(format!(
            "Cannot unify target {:?} with conclusion of {:?}",
            target, lemma
        ))
    }
}

//########################### UNIT TESTS
#[cfg(test)]
mod unit_tests {
    use crate::{
        misc::Union::R,
        parser::api::Tactic::{Apply, Exact, Intro},
        type_theory::{
            cic::{
                cic::{
                    Cic,
                    CicStm::{Fun, InductiveDef},
                    CicTerm::{
                        Abstraction, Application, Match, Meta, Product, Sort,
                        Variable,
                    },
                    GLOBAL_INDEX,
                },
                tactics::{
                    type_check_exact, type_check_intro, type_check_tactic,
                },
            },
            commons::type_check::type_check_theorem,
            interface::{Interactive, Kernel, TypeTheory},
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
        let simple_implication = Product(
            "_".to_string(),
            Box::new(premise1.clone()),
            Box::new(conclusion.clone()),
        );
        let hole = Cic::proof_hole();

        let (proof, subgoals) = Cic::type_check_tactic(
            &mut test_env,
            &Apply(simple_implication.clone()),
            &conclusion,
            &hole,
        )
        .unwrap();
        assert_eq!(
            proof,
            Application(Box::new(simple_implication), Box::new(hole.clone())),
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
        let (_, subgoals) = Cic::type_check_tactic(
            &mut test_env,
            &Apply(double_implication.clone()),
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

    #[test]
    fn test_refl_equality() {
        let nat = Variable("Nat".to_string(), GLOBAL_INDEX);
        let mut test_env = Cic::default_environment();

        // inductive Nat {z: Nat, s: Nat -> Nat}
        Cic::type_check_stm(
            &InductiveDef(
                "Nat".to_string(),
                vec![],
                Box::new(Sort("TYPE".to_string())),
                vec![
                    ("z".to_string(), nat.clone()),
                    (
                        "s".to_string(),
                        Product(
                            "_".to_string(),
                            Box::new(nat.clone()),
                            Box::new(nat.clone()),
                        ),
                    ),
                ],
            ),
            &mut test_env,
        )
        .expect("Failed to set up Nat inductive type");

        // inductive Eq : (T:TYPE) (x:T) : T -> PROP { refl: Eq T x x }
        Cic::type_check_stm(
            &InductiveDef(
                "Eq".to_string(),
                vec![
                    ("T".to_string(), Sort("TYPE".to_string())),
                    ("x".to_string(), Variable("T".to_string(), GLOBAL_INDEX)),
                ],
                Box::new(Product(
                    "_".to_string(),
                    Box::new(Variable("T".to_string(), GLOBAL_INDEX)),
                    Box::new(Sort("PROP".to_string())),
                )),
                vec![(
                    "refl".to_string(),
                    Application(
                        Box::new(Application(
                            Box::new(Application(
                                Box::new(Variable(
                                    "Eq".to_string(),
                                    GLOBAL_INDEX,
                                )),
                                Box::new(Variable(
                                    "T".to_string(),
                                    GLOBAL_INDEX,
                                )),
                            )),
                            Box::new(Variable("x".to_string(), GLOBAL_INDEX)),
                        )),
                        Box::new(Variable("x".to_string(), GLOBAL_INDEX)),
                    ),
                )],
            ),
            &mut test_env,
        )
        .expect("Failed to set up Eq inductive type");

        // fun rec plus (n:Nat) (m:Nat) : Nat { match n with | z => m, | s nn => s (plus nn m) }
        Cic::type_check_stm(
            &Fun(
                "plus".to_string(),
                vec![
                    ("n".to_string(), nat.clone()),
                    ("m".to_string(), nat.clone()),
                ],
                Box::new(nat.clone()),
                Box::new(Match(
                    Box::new(Variable("n".to_string(), GLOBAL_INDEX)),
                    vec![
                        (
                            Variable("z".to_string(), GLOBAL_INDEX),
                            Variable("m".to_string(), GLOBAL_INDEX),
                        ),
                        (
                            Application(
                                Box::new(Variable(
                                    "s".to_string(),
                                    GLOBAL_INDEX,
                                )),
                                Box::new(Variable(
                                    "nn".to_string(),
                                    GLOBAL_INDEX,
                                )),
                            ),
                            Application(
                                Box::new(Variable(
                                    "s".to_string(),
                                    GLOBAL_INDEX,
                                )),
                                Box::new(Application(
                                    Box::new(Application(
                                        Box::new(Variable(
                                            "plus".to_string(),
                                            GLOBAL_INDEX,
                                        )),
                                        Box::new(Variable(
                                            "nn".to_string(),
                                            GLOBAL_INDEX,
                                        )),
                                    )),
                                    Box::new(Variable(
                                        "m".to_string(),
                                        GLOBAL_INDEX,
                                    )),
                                )),
                            ),
                        ),
                    ],
                )),
                true,
            ),
            &mut test_env,
        )
        .expect("Failed to set up plus function");

        let z = Variable("z".to_string(), GLOBAL_INDEX);
        let s = Variable("s".to_string(), GLOBAL_INDEX);
        let one = Application(Box::new(s.clone()), Box::new(z.clone()));

        // theorem: 0 + 1 = 1
        let theorem = Application(
            Box::new(Application(
                Box::new(Application(
                    Box::new(Variable("Eq".to_string(), GLOBAL_INDEX)),
                    Box::new(nat.clone()),
                )),
                Box::new(Application(
                    Box::new(Application(
                        Box::new(Variable("plus".to_string(), GLOBAL_INDEX)),
                        Box::new(z.clone()),
                    )),
                    Box::new(one.clone()),
                )),
            )),
            Box::new(one.clone()),
        );

        // proof: refl Nat (s z)
        let proof_term = Application(
            Box::new(Application(
                Box::new(Variable("refl".to_string(), GLOBAL_INDEX)),
                Box::new(nat.clone()),
            )),
            Box::new(one.clone()),
        );

        assert!(
            type_check_theorem::<Cic>(
                &mut test_env,
                "",
                &theorem,
                &R(vec![Exact(proof_term)]),
            )
            .is_ok(),
            "Failed to prove Eq Nat (plus z (s z)) (s z) using exact tactic on refl Nat (s z)"
        );
    }
}
