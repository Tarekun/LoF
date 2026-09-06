use crate::type_theory::cic::cic::{
    Cic,
    CicTerm::{self, Abstraction, Application, Product, Sort, Variable},
    GLOBAL_INDEX,
};
use crate::type_theory::commons::transport::EquivConfig;
use crate::type_theory::interface::TypeTheory;
use std::collections::HashMap;

/// Builds a minimal environment with two unary inductive types (`Nat`-like
/// `A` with constructors `az`/`as_`, `Bin`-like `B` with constructor `bz`
/// and a non-constructor smart-successor `bs`) registered, matching the
/// shape transport actually needs to detect: `A`'s constructors registered
/// via `add_constructor_store`, so `is_constructor_of` can see them.
fn test_env() -> crate::type_theory::environment::Environment<Cic> {
    let mut env = Cic::default_environment();
    env.add_to_context("A", &Sort("TYPE".to_string()));
    env.add_to_context("B", &Sort("TYPE".to_string()));
    env.add_constructor_store(
        "A",
        vec![
            ("az".to_string(), Variable("A".to_string(), GLOBAL_INDEX)),
            (
                "as_".to_string(),
                Product(
                    "_".to_string(),
                    Box::new(Variable("A".to_string(), GLOBAL_INDEX)),
                    Box::new(Variable("A".to_string(), GLOBAL_INDEX)),
                ),
            ),
        ],
    );
    env
}

fn test_config() -> EquivConfig<Cic> {
    let mut dep_constr = HashMap::new();
    dep_constr.insert(
        "az".to_string(),
        Variable("bz".to_string(), GLOBAL_INDEX),
    );
    dep_constr.insert("as_".to_string(), Variable("bs".to_string(), GLOBAL_INDEX));

    EquivConfig {
        name: "AB".to_string(),
        type_a: "A".to_string(),
        type_b: "B".to_string(),
        forward: Variable("a_to_b".to_string(), GLOBAL_INDEX),
        backward: Variable("b_to_a".to_string(), GLOBAL_INDEX),
        section: Variable("section_ab".to_string(), GLOBAL_INDEX),
        retraction: Variable("retraction_ab".to_string(), GLOBAL_INDEX),
        dep_constr,
        dep_elim: Variable("b_induction".to_string(), GLOBAL_INDEX),
        eta: Some(Abstraction(
            "x".to_string(),
            Box::new(Variable("B".to_string(), GLOBAL_INDEX)),
            Box::new(Variable("x".to_string(), 0)),
        )),
        iota: HashMap::new(),
        lifted_names: HashMap::new(),
    }
}

#[test]
fn test_transport_type_variable() {
    let mut env = test_env();
    let config = test_config();

    assert_eq!(
        super::transport_term(
            &mut env,
            &config,
            &Variable("A".to_string(), GLOBAL_INDEX)
        )
        .unwrap(),
        Variable("B".to_string(), GLOBAL_INDEX),
        "a bare occurrence of type_a should be rewritten to type_b"
    );
}

#[test]
fn test_transport_bare_constructor_uses_dep_constr() {
    let mut env = test_env();
    let config = test_config();

    assert_eq!(
        super::transport_term(
            &mut env,
            &config,
            &Variable("az".to_string(), GLOBAL_INDEX)
        )
        .unwrap(),
        Variable("bz".to_string(), GLOBAL_INDEX),
        "a bare 0-ary constructor should be rewritten to its dep_constr image"
    );
}

#[test]
fn test_transport_application_rewrites_constructor_head_and_args() {
    let mut env = test_env();
    let config = test_config();

    // as_(az) -> should become bs(bz)
    let term = Application(
        Box::new(Variable("as_".to_string(), GLOBAL_INDEX)),
        Box::new(Variable("az".to_string(), GLOBAL_INDEX)),
    );
    let expected = Application(
        Box::new(Variable("bs".to_string(), GLOBAL_INDEX)),
        Box::new(Variable("bz".to_string(), GLOBAL_INDEX)),
    );

    assert_eq!(
        super::transport_term(&mut env, &config, &term).unwrap(),
        expected,
        "an application of a constructor should rewrite both the head (via dep_constr) and recursively transport its arguments"
    );
}

#[test]
fn test_transport_product_retypes_binder_and_recurses_into_body() {
    let mut env = test_env();
    let config = test_config();

    // forall n:A. az  ~>  forall n:B. bz
    let term = Product(
        "n".to_string(),
        Box::new(Variable("A".to_string(), GLOBAL_INDEX)),
        Box::new(Variable("az".to_string(), GLOBAL_INDEX)),
    );
    let expected = Product(
        "n".to_string(),
        Box::new(Variable("B".to_string(), GLOBAL_INDEX)),
        Box::new(Variable("bz".to_string(), GLOBAL_INDEX)),
    );

    assert_eq!(
        super::transport_term(&mut env, &config, &term).unwrap(),
        expected,
        "Product should rewrite its domain type and recursively transport its body"
    );
}

#[test]
fn test_transport_eliminator_application_uses_dep_elim() {
    let mut env = test_env();
    let config = test_config();

    // e_A(motive, c0, c1) -> b_induction(transported_motive, c0, c1)
    let motive = Variable("A".to_string(), GLOBAL_INDEX);
    let term = Application(
        Box::new(Application(
            Box::new(Variable("e_A".to_string(), GLOBAL_INDEX)),
            Box::new(motive.clone()),
        )),
        Box::new(Variable("c0".to_string(), GLOBAL_INDEX)),
    );

    let result = super::transport_term(&mut env, &config, &term).unwrap();
    let expected = Application(
        Box::new(Application(
            Box::new(Variable("b_induction".to_string(), GLOBAL_INDEX)),
            Box::new(Variable("B".to_string(), GLOBAL_INDEX)),
        )),
        Box::new(Variable("c0".to_string(), GLOBAL_INDEX)),
    );

    assert_eq!(
        result, expected,
        "an application of e_<type_a> should swap the head for dep_elim and still transport its arguments (here the motive A -> B)"
    );
}

#[test]
fn test_transport_lifted_name_is_substituted() {
    let mut env = test_env();
    let mut config = test_config();
    config
        .lifted_names
        .insert("old_fun".to_string(), "new_fun".to_string());

    let term = Application(
        Box::new(Variable("old_fun".to_string(), GLOBAL_INDEX)),
        Box::new(Variable("az".to_string(), GLOBAL_INDEX)),
    );
    let expected = Application(
        Box::new(Variable("new_fun".to_string(), GLOBAL_INDEX)),
        Box::new(Variable("bz".to_string(), GLOBAL_INDEX)),
    );

    assert_eq!(
        super::transport_term(&mut env, &config, &term).unwrap(),
        expected,
        "a call to an already-lifted auxiliary function should be rewritten to its new name"
    );

    // an unrelated, un-lifted name should pass through untouched
    let unrelated = Variable("unrelated_fun".to_string(), GLOBAL_INDEX);
    assert_eq!(
        super::transport_term(&mut env, &config, &unrelated).unwrap(),
        unrelated,
        "a name that isn't a constructor, isn't lifted, and isn't type_a should pass through unchanged"
    );
}

#[test]
fn test_transport_missing_dep_constr_entry_is_an_error() {
    let mut env = test_env();
    let mut config = test_config();
    config.dep_constr.remove("az");

    assert!(
        super::transport_term(
            &mut env,
            &config,
            &Variable("az".to_string(), GLOBAL_INDEX)
        )
        .is_err(),
        "transporting a constructor with no registered dep_constr entry must fail, not silently pass the old constructor through"
    );
}

#[test]
fn test_transport_raw_match_over_type_a_is_rejected() {
    let mut env = test_env();
    let config = test_config();

    let term = CicTerm::Match(
        Box::new(Variable("n".to_string(), 0)),
        vec![
            (
                Variable("az".to_string(), GLOBAL_INDEX),
                Variable("az".to_string(), GLOBAL_INDEX),
            ),
            (
                Application(
                    Box::new(Variable("as_".to_string(), GLOBAL_INDEX)),
                    Box::new(Variable("nn".to_string(), GLOBAL_INDEX)),
                ),
                Variable("nn".to_string(), GLOBAL_INDEX),
            ),
        ],
    );
    env.with_local_assumption(
        "n",
        &Variable("A".to_string(), GLOBAL_INDEX),
        |local_env| {
            assert!(
                super::transport_term(local_env, &config, &term).is_err(),
                "a raw `match` whose scrutinee has type_a must be rejected - this engine only rewrites explicit e_<type_a> applications, not surface `match`"
            );
        },
    );
}
