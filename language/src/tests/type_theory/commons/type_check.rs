use crate::{
    misc::Union::{L, R},
    parser::api::Tactic::{Exact, Intro},
    type_theory::{
        cic::cic::{
            Cic,
            CicTerm::{Product, Sort, Variable},
            GLOBAL_INDEX,
        },
        commons::type_check::u_type_check_theorem,
        interface::TypeTheory,
    },
};

#[test]
fn test_u_type_check_theorem_registers_name() {
    let mut env = Cic::default_environment();
    env.add_to_context("Nat", &Sort("TYPE".to_string()));
    env.add_to_context("z", &Variable("Nat".to_string(), GLOBAL_INDEX));

    let formula = Variable("Nat".to_string(), GLOBAL_INDEX);
    let proof_term = Variable("z".to_string(), GLOBAL_INDEX);

    assert!(
        u_type_check_theorem::<Cic>(
            &mut env,
            "my_thm",
            &formula,
            &L(proof_term),
        )
        .is_ok(),
        "theorem should type check"
    );
    assert_eq!(
        env.get_variable_type("my_thm"),
        Some(formula),
        "u_type_check_theorem must register the theorem's name in the real environment"
    );
}

#[test]
fn test_u_type_check_theorem_rejects_incomplete_tactic_proof() {
    // Regression test: running out of tactic steps while a subgoal is still
    // pending used to be treated as a *successful*, complete proof - the
    // unresolved `T::proof_hole()` sentinel was silently left embedded in
    // the returned term, only to surface later as a confusing "Unbound
    // variable: THIS_IS_A_PARTIAL_PROOF_HOLE" error out of type-checking the
    // assembled proof, rather than a clear "incomplete proof" error.
    let mut env = Cic::default_environment();
    env.add_to_context("Nat", &Sort("TYPE".to_string()));

    // `Nat -> Nat`, provable only by `intro`-ing the argument first
    let formula = Product(
        "n".to_string(),
        Box::new(Variable("Nat".to_string(), GLOBAL_INDEX)),
        Box::new(Variable("Nat".to_string(), GLOBAL_INDEX)),
    );

    let result = u_type_check_theorem::<Cic>(
        &mut env,
        "incomplete_thm",
        &formula,
        &R(vec![]),
    );
    assert!(
        result.is_err(),
        "an interactive proof with no tactics left to discharge a pending subgoal must be rejected, not accepted as complete"
    );
    assert!(
        format!("{}", result.unwrap_err()).contains("Incomplete proof"),
        "the error should clearly say the proof is incomplete, not leak an internal hole-sentinel/unbound-variable error"
    );

    // sanity check: the same formula is still provable once every subgoal
    // is actually discharged (`\n: Nat. n`, ie `intro` then `exact`)
    assert!(
        u_type_check_theorem::<Cic>(
            &mut env,
            "complete_thm",
            &formula,
            &R(vec![
                Intro(
                    "n".to_string(),
                    Variable("Nat".to_string(), GLOBAL_INDEX),
                ),
                Exact(Variable("n".to_string(), GLOBAL_INDEX)),
            ]),
        )
        .is_ok(),
        "the same formula must still be provable once tactics actually discharge every subgoal"
    );
}
