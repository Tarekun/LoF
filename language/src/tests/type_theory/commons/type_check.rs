use crate::{
    misc::Union::{L, R},
    type_theory::{
        cic::cic::{
            Cic,
            CicTerm::{Sort, Variable},
            NameKind,
        },
        commons::type_check::type_check_theorem,
        interface::TypeTheory,
    },
};

#[test]
fn test_type_check_theorem_registers_name() {
    let mut env = Cic::default_environment();
    env.add_to_context("Nat", &Sort("TYPE".to_string()));
    env.add_to_context("z", &Variable("Nat".to_string(), NameKind::Const()));

    let formula = Variable("Nat".to_string(), NameKind::Const());
    let proof_term = Variable("z".to_string(), NameKind::Const());

    assert!(
        type_check_theorem::<Cic>(
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
        "type_check_theorem must register the theorem's name in the real environment"
    );
}

#[test]
fn test_type_check_theorem_rejects_wrong_proofs() {
    let mut env = Cic::default_environment();
    env.add_to_context("Nat", &Sort("TYPE".to_string()));
    env.add_to_context("Bool", &Sort("TYPE".to_string()));
    env.add_to_context("z", &Variable("Nat".to_string(), NameKind::Const()));

    let formula = Variable("Bool".to_string(), NameKind::Const());
    let proof_term = Variable("z".to_string(), NameKind::Const());

    assert!(
        type_check_theorem::<Cic>(&mut env, "wrong", &formula, &L(proof_term))
            .is_err(),
        "the kernel must reject a proof whose type isnt the stated formula"
    );
    assert!(
        type_check_theorem::<Cic>(&mut env, "unrefined", &formula, &R(vec![]))
            .is_err(),
        "the kernel must reject tactic proofs that werent refined into terms"
    );
    assert_eq!(env.get_variable_type("wrong"), None);
}
