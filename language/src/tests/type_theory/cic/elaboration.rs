use crate::{
    parser::api::Expression,
    type_theory::{
        cic::{
            cic::{
                Cic, CicStm,
                CicTerm::{
                    self, Abstraction, Application, Let, Match, Product, Sort,
                    Variable,
                },
                NameKind, FIRST_INDEX,
            },
            elaboration::{
                elaborate_application, elaborate_expression,
                elaborate_inductive, elaborate_match, elaborate_type_product,
                elaborate_var_use,
            },
        },
        commons::utils::ElabStore,
        interface::TypeTheory,
    },
};

#[test]
fn test_var_elaboration() {
    let test_var_name = "test_var";
    let test_var = Variable(test_var_name.to_string(), NameKind::Const());
    let test_var_placeholder =
        Variable(test_var_name.to_string(), NameKind::Bound(FIRST_INDEX));
    let store = ElabStore::empty().push_name(test_var_name);

    assert_eq!(
        elaborate_var_use(test_var_name, &store),
        test_var_placeholder.clone(),
        "Variable term not properly constructed"
    );
    assert_eq!(
        elaborate_var_use("TYPE", &store),
        Sort("TYPE".to_string()),
        "Sort name returns a simple variable instead of a sort term"
    );
    assert_eq!(
        elaborate_expression(&Expression::VarUse(test_var_name.to_string())),
        test_var.clone(),
        "Top level elaboration doesnt work with variables as expected"
    );
}

#[test]
fn test_abs_elaboration() {
    let expected_term = Abstraction(
        "x".to_string(),
        Box::new(Sort("TYPE".to_string())),
        Box::new(Variable("x".to_string(), NameKind::Bound(FIRST_INDEX))),
    );

    assert_eq!(
        elaborate_expression(&Expression::Abstraction(
            "x".to_string(),
            Box::new(Expression::VarUse("TYPE".to_string())),
            Box::new(Expression::VarUse("x".to_string())),
        )),
        expected_term,
        "Top level elaborator isnt working with abstraction"
    );
}

#[test]
fn test_prod_elaboration() {
    let expected_term = Product(
        "x".to_string(),
        Box::new(Sort("TYPE".to_string())),
        Box::new(Sort("TYPE".to_string())),
    );

    assert_eq!(
        elaborate_type_product(
            "x",
            &Expression::VarUse("TYPE".to_string()),
            &Expression::VarUse("TYPE".to_string()),
            &ElabStore::empty(),
        ),
        expected_term.clone(),
        "Type abstraction elaboration isnt working as expected"
    );
    assert_eq!(
        elaborate_expression(&Expression::TypeProduct(
            "x".to_string(),
            Box::new(Expression::VarUse("TYPE".to_string())),
            Box::new(Expression::VarUse("TYPE".to_string())),
        )),
        expected_term,
        "Top level elaborator isnt working with type abstraction"
    );
}

#[test]
fn test_app_elaboration() {
    let expected_term = Application(
        Box::new(Variable("s".to_string(), NameKind::Const())),
        Box::new(Variable("o".to_string(), NameKind::Const())),
    );

    assert_eq!(
        elaborate_application(
            &Expression::VarUse("s".to_string()),
            &vec![Expression::VarUse("o".to_string())],
            &ElabStore::empty(),
        ),
        expected_term.clone(),
        "Application elaboration isnt working as expected"
    );
    assert_eq!(
        elaborate_application(
            &Expression::VarUse("f".to_string()),
            &vec![
                Expression::VarUse("x".to_string()),
                Expression::VarUse("y".to_string())
            ],
            &ElabStore::empty(),
        ),
        Application(
            Box::new(Application(
                Box::new(Variable("f".to_string(), NameKind::Const())),
                Box::new(Variable("x".to_string(), NameKind::Const())),
            )),
            Box::new(Variable("y".to_string(), NameKind::Const()))
        ),
        "Application elaboration isnt respecting associativity"
    );
    assert_eq!(
        elaborate_expression(&Expression::Application(
            Box::new(Expression::VarUse("s".to_string())),
            vec![Expression::VarUse("o".to_string())],
        )),
        expected_term,
        "Top level elaborator isnt working with applications"
    );
}

#[test]
fn test_let_elaboration() {
    assert_eq!(
        Cic::elaborate_expression(&Expression::Let(
            "x".to_string(),
            Box::new(Some(Expression::VarUse("Complex".to_string()))),
            Box::new(Expression::VarUse("i".to_string())),
            Box::new(Expression::VarUse("x".to_string())),
        )),
        Ok(Let(
            "x".to_string(),
            Box::new(Some(Variable("Complex".to_string(), NameKind::Const()))),
            Box::new(Variable("i".to_string(), NameKind::Const())),
            Box::new(Variable("x".to_string(), NameKind::Bound(0))),
        )),
        "Let elaboration isnt producing the proper term"
    );
    assert_eq!(
        Cic::elaborate_expression(&Expression::Let(
            "x".to_string(),
            Box::new(None),
            Box::new(Expression::VarUse("i".to_string())),
            Box::new(Expression::VarUse("x".to_string())),
        )),
        Ok(Let(
            "x".to_string(),
            Box::new(None),
            Box::new(Variable("i".to_string(), NameKind::Const())),
            Box::new(Variable("x".to_string(), NameKind::Bound(0))),
        )),
        "Let elaboration cant cope with missing type annotation"
    );
}

#[test]
fn test_match_elaboration() {
    let expected_term = Match(
        Box::new(Variable("t".to_string(), NameKind::Const())),
        vec![
            (
                Variable("o".to_string(), NameKind::Const()),
                Application(
                    Box::new(Variable("s".to_string(), NameKind::Const())),
                    Box::new(Variable("o".to_string(), NameKind::Const())),
                ),
            ),
            // `n` is the constructor's argument: it binds, so both the
            // pattern occurrence and the branch body that uses it index
            // it as the innermost binder of that branch
            (
                Application(
                    Box::new(Variable("s".to_string(), NameKind::Const())),
                    Box::new(Variable(
                        "n".to_string(),
                        NameKind::Bound(FIRST_INDEX),
                    )),
                ),
                Variable("n".to_string(), NameKind::Bound(FIRST_INDEX)),
            ),
        ],
    );
    let base_pattern = (
        Expression::VarUse("o".to_string()),
        Expression::Application(
            Box::new(Expression::VarUse("s".to_string())),
            vec![Expression::VarUse("o".to_string())],
        ),
    );
    let inductive_patter = (
        Expression::Application(
            Box::new(Expression::VarUse("s".to_string())),
            vec![Expression::VarUse("n".to_string())],
        ),
        Expression::VarUse("n".to_string()),
    );

    assert_eq!(
        elaborate_match(
            &Expression::VarUse("t".to_string()),
            &vec![base_pattern.clone(), inductive_patter.clone()],
            &ElabStore::empty(),
        ),
        expected_term,
        "Match elaboration isnt working as expected"
    );
    assert_eq!(
        elaborate_expression(&Expression::Match(
            Box::new(Expression::VarUse("t".to_string())),
            vec![base_pattern, inductive_patter]
        )),
        expected_term,
        "Top level elaboration doesnt work with match"
    );
}

#[test]
fn test_inductive_elaboration() {
    let ariety = Expression::VarUse("TYPE".to_string());

    let result = elaborate_inductive(
        &"nat".to_string(),
        &vec![],
        &ariety,
        &vec![
            ("o".to_string(), Expression::VarUse("nat".to_string())),
            (
                "s".to_string(),
                Expression::TypeProduct(
                    "_".to_string(),
                    Box::new(Expression::VarUse("nat".to_string())),
                    Box::new(Expression::VarUse("nat".to_string())),
                ),
            ),
        ],
    );
    assert_eq!(
        result,
        Ok(CicStm::InductiveDef(
            "nat".to_string(),
            vec![],
            Box::new(Sort("TYPE".to_string())),
            vec![
                (
                    "o".to_string(),
                    Variable("nat".to_string(), NameKind::Const())
                ),
                (
                    "s".to_string(),
                    Product(
                        "_".to_string(),
                        Box::new(Variable(
                            "nat".to_string(),
                            NameKind::Const()
                        )),
                        Box::new(Variable(
                            "nat".to_string(),
                            NameKind::Const()
                        )),
                    )
                )
            ]
        )),
        "Inductive elaboration isnt working with constant constructor"
    );
}

#[test]
fn test_let_does_not_bind_its_own_definition_body() {
    // `let x := x in ...` : the `x` on the right of `:=` refers to an
    // *outer* `x`, not to the binder it's defining — this is the
    // Let-shadowing fix (the old `index_variables` incorrectly put `var_name`
    // in scope for `body` too, making this term wrongly self-referential).
    let term = elaborate_expression(&Expression::Abstraction(
        "x".to_string(),
        Box::new(Expression::VarUse("TYPE".to_string())),
        Box::new(Expression::Let(
            "x".to_string(),
            Box::new(None),
            Box::new(Expression::VarUse("x".to_string())),
            Box::new(Expression::VarUse("x".to_string())),
        )),
    ));
    assert_eq!(
        term,
        Abstraction(
            "x".to_string(),
            Box::new(Sort("TYPE".to_string())),
            Box::new(Let(
                "x".to_string(),
                Box::new(None),
                // the definition's own `x` refers to the outer abstraction
                Box::new(Variable("x".to_string(), NameKind::Bound(0))),
                // the continuation's `x` refers to the let-binding itself
                Box::new(Variable("x".to_string(), NameKind::Bound(0))),
            )),
        ),
        "let definition binds the variable name in the definition body too"
    );
}

#[test]
fn test_shadowing_a_global_with_a_local_binder_of_the_same_name() {
    // The user's acceptance example: given a global type `Nat`, a lambda
    // binding a local `Nat:PROP` argument must have every reference to
    // `Nat` *inside its body* resolve to that local variable, not the
    // global — full shadowing, not a name collision.
    let bare_reference =
        elaborate_expression(&Expression::VarUse("Nat".to_string()));
    assert_eq!(
        bare_reference,
        Variable("Nat".to_string(), NameKind::Const()),
        "a top-level, unshadowed `Nat` must elaborate to the global (Free) reference"
    );

    let shadowed = elaborate_expression(&Expression::Abstraction(
        "Nat".to_string(),
        Box::new(Expression::VarUse("PROP".to_string())),
        Box::new(Expression::VarUse("Nat".to_string())),
    ));
    assert_eq!(
        shadowed,
        Abstraction(
            "Nat".to_string(),
            Box::new(Sort("PROP".to_string())),
            Box::new(Variable("Nat".to_string(), NameKind::Bound(0))),
        ),
        "inside λNat:PROP. Nat, the body's `Nat` must resolve to the local Bound variable, fully shadowing the global"
    );
}

#[test]
fn test_match_elaboration_nested_pattern_binds_two_arguments() {
    // cons(h, cons(h2, ll))  =>  ...   -- two levels of nesting, three total
    // binders (h, h2, ll), depth-first left-to-right.
    let pattern = Expression::Application(
        Box::new(Expression::VarUse("cons".to_string())),
        vec![
            Expression::VarUse("h".to_string()),
            Expression::Application(
                Box::new(Expression::VarUse("cons".to_string())),
                vec![
                    Expression::VarUse("h2".to_string()),
                    Expression::VarUse("ll".to_string()),
                ],
            ),
        ],
    );
    let body = Expression::VarUse("h".to_string());

    let term = elaborate_expression(&Expression::Match(
        Box::new(Expression::VarUse("scrutinee".to_string())),
        vec![(pattern, body)],
    ));

    // h is the leftmost/outermost binder => highest index (2 of 3);
    // h2 is next => index 1; ll is innermost => index 0.
    let expected_pattern = Application(
        Box::new(Application(
            Box::new(Variable("cons".to_string(), NameKind::Const())),
            Box::new(Variable("h".to_string(), NameKind::Bound(2))),
        )),
        Box::new(Application(
            Box::new(Application(
                Box::new(Variable("cons".to_string(), NameKind::Const())),
                Box::new(Variable("h2".to_string(), NameKind::Bound(1))),
            )),
            Box::new(Variable("ll".to_string(), NameKind::Bound(0))),
        )),
    );

    match term {
        Match(_, branches) => {
            assert_eq!(branches[0].0, expected_pattern);
            assert_eq!(
                branches[0].1,
                Variable("h".to_string(), NameKind::Bound(2)),
                "the branch body must see the same telescope as the pattern"
            );
        }
        _ => panic!("expected a Match term"),
    }
}
