use crate::{
    misc::Union::L,
    type_theory::{
        cic::cic::{
            Cic,
            CicTerm::{Sort, Variable},
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
