use crate::type_theory::cic::cic::{Cic, FIRST_INDEX};
use crate::type_theory::cic::cic::{
    CicStm::{Fun, InductiveDef},
    CicTerm::{
        self, Abstraction, Application, Let, Match, Meta, Product, Sort,
        Variable,
    },
    GLOBAL_INDEX,
};
use crate::type_theory::cic::unification::{
    cic_apply_unifier, cic_collect_unifications, cic_so_unification,
    cic_solve_unifications, explode, is_substitutable, occurs,
    solve_unifications_unnormalized, structurally_equal,
};
use crate::type_theory::commons::unification::Substitution;
use crate::type_theory::interface::{Kernel, TypeTheory};
use std::collections::VecDeque;

mod components {
    use super::*;

    #[test]
    fn test_variable_structural_equality() {
        assert!(
            structurally_equal(
                &Variable("x".to_string(), 0),
                &Variable("y".to_string(), 0),
            ),
            "bound variables at the same de Bruijn position should be equal regardless of name (they're alpha equivalent)"
        );

        assert!(
            !structurally_equal(
                &Variable("x".to_string(), 0),
                &Variable("y".to_string(), 1),
            ),
            "bound variables at different positions with different names must not be equal"
        );

        assert!(
            !structurally_equal(
                &Variable("z".to_string(), GLOBAL_INDEX),
                &Variable("s".to_string(), GLOBAL_INDEX),
            ),
            "different global constants should not be considered structurally equal"
        );
    }

    #[test]
    fn test_structurally_equal_abstraction() {
        // (x,y) -> x
        let term = Abstraction(
            "x".to_string(),
            Box::new(Sort("TYPE".to_string())),
            Box::new(Abstraction(
                "y".to_string(),
                Box::new(Sort("TYPE".to_string())),
                Box::new(Variable("x".to_string(), 1)),
            )),
        );
        // (y,x) -> y
        let unifiable = Abstraction(
            "y".to_string(),
            Box::new(Sort("TYPE".to_string())),
            Box::new(Abstraction(
                "x".to_string(),
                Box::new(Sort("TYPE".to_string())),
                Box::new(Variable("y".to_string(), 1)),
            )),
        );
        // (y,x) -> x
        let ununifiable = Abstraction(
            "y".to_string(),
            Box::new(Sort("TYPE".to_string())),
            Box::new(Abstraction(
                "x".to_string(),
                Box::new(Sort("TYPE".to_string())),
                Box::new(Variable("x".to_string(), 2)),
            )),
        );

        assert!(
            structurally_equal(&term, &unifiable),
            "first arg projection functions are not alpha equivalent"
        );
        assert!(
            !structurally_equal(&term, &ununifiable),
            "first/second arg projection functions are unifiable"
        );
    }
}

mod constraint_collection {
    use super::*;

    #[test]
    fn test_collect_unifications_product_match_and_let() {
        let bool_type = Variable("Bool".to_string(), GLOBAL_INDEX);
        let mut env = Cic::default_environment();
        Cic::type_check_stm(
            &InductiveDef(
                "Bool".to_string(),
                vec![],
                Box::new(Sort("TYPE".to_string())),
                vec![
                    ("true".to_string(), bool_type.clone()),
                    ("false".to_string(), bool_type.clone()),
                ],
            ),
            &mut env,
        )
        .expect("Failed to set up Bool");
        env.add_to_context(
            "f",
            &Product(
                "_".to_string(),
                Box::new(bool_type),
                Box::new(Sort("TYPE".to_string())),
            ),
        );
        let f = Variable("f".to_string(), GLOBAL_INDEX);
        // applying `f` (Bool -> TYPE) to a metavariable generates a
        // constraint pairing `f`'s domain against the meta's own type
        let inner_application =
            Application(Box::new(f.clone()), Box::new(Meta(0)));

        let product = Product(
            "_".to_string(),
            Box::new(inner_application.clone()),
            Box::new(Sort("TYPE".to_string())),
        );
        assert!(
            !cic_collect_unifications(&product, &mut env).unwrap().is_empty(),
            "cic_collect_unifications must recurse into a Product's domain/codomain"
        );
        // a Let whose body contains that inner application
        let let_term = Let(
            "x".to_string(),
            Box::new(None),
            Box::new(inner_application.clone()),
            Box::new(Sort("TYPE".to_string())),
        );
        assert!(
            !cic_collect_unifications(&let_term, &mut env)
                .unwrap()
                .is_empty(),
            "cic_collect_unifications must recurse into a Let's body/scope"
        );

        let match_term = Match(
            Box::new(inner_application),
            vec![(
                Variable("true".to_string(), GLOBAL_INDEX),
                Sort("TYPE".to_string()),
            )],
        );
        assert!(
            !cic_collect_unifications(&match_term, &mut env).unwrap().is_empty(),
            "cic_collect_unifications must recurse into a Match's scrutinee/branches"
        );
    }

    #[test]
    fn test_collect_unifications_binds_match_pattern_variables() {
        let nat = Variable("Nat".to_string(), GLOBAL_INDEX);
        let s = Variable("s".to_string(), GLOBAL_INDEX);
        let nn = Variable("nn".to_string(), GLOBAL_INDEX);
        let mut env = Cic::default_environment();
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
            &mut env,
        )
        .expect("Failed to set up Nat");

        // match n { s(nn) => s(nn) }: `nn` is bound by the pattern and only
        // then used by the body
        let match_term = Match(
            Box::new(Variable("n".to_string(), FIRST_INDEX)),
            vec![(
                Application(Box::new(s.clone()), Box::new(nn.clone())),
                Application(Box::new(s), Box::new(nn)),
            )],
        );
        let constraints = cic_collect_unifications(&match_term, &mut env)
            .expect("collection must bind a pattern's variables for its branch body, not type check the pattern as a reference");

        assert_eq!(
            constraints,
            vec![(nat.clone(), nat)],
            "a match branch must contribute only its body's constraints, the pattern is a binder not an expression"
        );
    }

    #[test]
    fn test_collect_unifications_works_with_bindings() {
        let mut env = Cic::default_environment();
        env.add_to_context("Nat", &Sort("TYPE".to_string()));
        env.add_to_context(
            "s",
            &Product(
                "_".to_string(),
                Box::new(Variable("Nat".to_string(), GLOBAL_INDEX)),
                Box::new(Variable("Nat".to_string(), GLOBAL_INDEX)),
            ),
        );
        let s = Variable("s".to_string(), GLOBAL_INDEX);
        let nat = Variable("Nat".to_string(), GLOBAL_INDEX);

        // `\lambda n: Nat. s(n)`
        let abstraction = Abstraction(
            "n".to_string(),
            Box::new(nat.clone()),
            Box::new(Application(
                Box::new(s.clone()),
                Box::new(Variable("n".to_string(), 0)),
            )),
        );
        assert!(
            cic_collect_unifications(&abstraction, &mut env).is_ok(),
            "cic_collect_unifications fails when inner abstraction body needs argument in context"
        );

        // `forall n: Nat. Eq(Nat, s(n), s(n))`
        let product = Product(
            "n".to_string(),
            Box::new(nat),
            Box::new(Application(
                Box::new(s),
                Box::new(Variable("n".to_string(), 0)),
            )),
        );
        assert!(
            cic_collect_unifications(&product, &mut env).is_ok(),
            "cic_collect_unifications fails when collection needs a binded variable in context"
        );
    }
}

#[test]
fn test_variable_ground_unification() {
    fn var(name: &str) -> CicTerm {
        Variable(name.to_string(), -100)
    }
    let listbool = Application(Box::new(var("List")), Box::new(var("Bool")));
    let listt = Application(
        Box::new(var("List")),
        Box::new(Variable("T".to_string(), FIRST_INDEX)),
    );
    assert!(cic_so_unification(&listbool, &listt).is_ok(), "nook");
}

#[test]
fn test_dhm() {
    let nat = Variable("Nat".to_string(), GLOBAL_INDEX);
    assert_eq!(
        cic_so_unification(&Meta(0), &nat).unwrap(),
        Substitution::from([("metavariable_0".to_string(), nat.clone())]),
        "Unification couldnt solve one simple constraint"
    );

    let constraints = vec![
        (
            Meta(1),
            Product("_".to_string(), Box::new(nat.clone()), Box::new(Meta(0))),
        ),
        (Meta(0), nat.clone()),
    ];
    let expected = Substitution::from([
        (
            "metavariable_1".to_string(),
            Product(
                "_".to_string(),
                Box::new(nat.clone()),
                Box::new(nat.clone()),
            ),
        ),
        ("metavariable_0".to_string(), nat.clone()),
    ]);
    assert_eq!(
            cic_solve_unifications(constraints, &mut Cic::default_environment()).unwrap(),
            expected,
            "Unification couldnt solve a problem with a function over metavariables"
        );
}

#[test]
fn test_match_unification() {
    let t = Variable("true".to_string(), GLOBAL_INDEX);
    let expected =
        Substitution::from([("metavariable_1".to_string(), t.clone())]);
    let constraints = vec![(
        Match(
            Box::new(Variable("b".to_string(), 0)),
            vec![
                (t.clone(), Variable("b".to_string(), GLOBAL_INDEX)),
                (
                    Variable("false".to_string(), GLOBAL_INDEX),
                    Variable("b".to_string(), GLOBAL_INDEX),
                ),
            ],
        ),
        Match(
            Box::new(Variable("b".to_string(), 0)),
            vec![
                (Meta(1), Variable("b".to_string(), GLOBAL_INDEX)),
                (
                    Variable("false".to_string(), GLOBAL_INDEX),
                    Variable("b".to_string(), GLOBAL_INDEX),
                ),
            ],
        ),
    )];
    assert_eq!(
        solve_unifications_unnormalized(VecDeque::from(constraints)).unwrap(),
        expected,
        "Unification couldnt solve a problem of constructor recovery in pattern matching"
    );

    let body = Sort("TYPE".to_string());
    let expected =
        Substitution::from([("metavariable_2".to_string(), body.clone())]);
    let constraints = vec![(
        Match(
            Box::new(Variable("b".to_string(), 0)),
            vec![
                (Variable("true".to_string(), GLOBAL_INDEX), body.clone()),
                (Variable("false".to_string(), GLOBAL_INDEX), body.clone()),
            ],
        ),
        Match(
            Box::new(Variable("b".to_string(), 0)),
            vec![
                (Variable("true".to_string(), GLOBAL_INDEX), Meta(2)),
                (Variable("false".to_string(), GLOBAL_INDEX), body.clone()),
            ],
        ),
    )];
    assert_eq!(
        solve_unifications_unnormalized(VecDeque::from(constraints)).unwrap(),
        expected,
        "Unification couldnt solve unification of pattern match bodies"
    );
}

mod substitution_routing {
    use super::*;

    // NOTE: this test is here atm, but im not sure CIC unification should really
    // support FO variable substitution
    #[test]
    fn test_apply_unifier_routes_variable_keys_by_name() {
        let nat = Variable("Nat".to_string(), GLOBAL_INDEX);
        let vec = Variable("Vec".to_string(), GLOBAL_INDEX);
        // Θ = { variable_n -> Nat, metavariable_0 -> Vec }
        let substitution = Substitution::from([
            ("variable_n".to_string(), nat.clone()),
            ("metavariable_0".to_string(), vec.clone()),
        ]);
        // Vec(n, ?0) mentions both the named variable and the metavariable
        let exp = Application(
            Box::new(Application(
                Box::new(vec.clone()),
                Box::new(Variable("n".to_string(), FIRST_INDEX)),
            )),
            Box::new(Meta(0)),
        );

        assert_eq!(
            cic_apply_unifier(&exp, &substitution),
            Application(
                Box::new(Application(Box::new(vec.clone()), Box::new(nat))),
                Box::new(vec),
            ),
            "applying a unifier must substitute `variable_<name>` keys by name and `metavariable_<idx>` keys by index"
        );
    }

    // NOTE: imma be honest i dont think this should be a test at all even
    // assuming CIC unification should include FO substitution too `x` is
    // a FO variable and im pretty sure it should NOT be replaceable
    // with the type `Nat`
    #[test]
    fn test_solved_mgu_grounds_variable_keys_inside_meta_bodies() {
        let nat = Variable("Nat".to_string(), GLOBAL_INDEX);
        let list = Variable("List".to_string(), GLOBAL_INDEX);
        let x = Variable("x".to_string(), FIRST_INDEX);

        // ?0 ≐ List(x) and x ≐ Nat: solving the second must ground the first
        let constraints = VecDeque::from(vec![
            (
                Meta(0),
                Application(Box::new(list.clone()), Box::new(x.clone())),
            ),
            (x, nat.clone()),
        ]);

        assert_eq!(
            solve_unifications_unnormalized(constraints).unwrap(),
            Substitution::from([
                (
                    "metavariable_0".to_string(),
                    Application(Box::new(list), Box::new(nat.clone())),
                ),
                ("variable_x".to_string(), nat),
            ]),
            "reducing an mgu must fold `variable_<name>` solutions into the other bodies by name"
        );
    }

    /// The mirror of the case below, and the reason the trivial x=x guard has
    /// to run *before* the redirect as well as after it: here the vacuous pair
    /// arrives *after* `x` already has a solution. `f(x, x) ≐ f(x, y)`
    /// derives `x =~= y` and then, from the repeated occurrence, `x ≐ x` -
    /// which is vacuous and must be dropped. Redirecting it through the stored
    /// `x -> y` instead invents `y -> x` out of nothing, closing a cycle that
    /// `reduce` then collapses into the useless mgu `{x -> x, y -> y}`.
    #[test]
    fn test_trivial_constraint_after_a_solution_is_dropped_not_redirected() {
        let f = Variable("f".to_string(), GLOBAL_INDEX);
        let x = Variable("x".to_string(), FIRST_INDEX);
        let y = Variable("y".to_string(), FIRST_INDEX);

        let f_of = |arg1: &CicTerm, arg2: &CicTerm| {
            Application(
                Box::new(Application(
                    Box::new(f.clone()),
                    Box::new(arg1.clone()),
                )),
                Box::new(arg2.clone()),
            )
        };
        assert_eq!(
            cic_so_unification(&f_of(&x, &x), &f_of(&x, &y)).unwrap(),
            Substitution::from([("variable_x".to_string(), y)]),
            "a vacuous x =~= x constraint must be dropped outright, never redirected through an existing solution for x"
        );
    }

    /// Redirecting through an already present substitution can turn a pair that
    /// was not self-referential into one that is: re-deriving `r_0 ≐ r` from a
    /// second occurrence of `r_0` in the same term redirects (via the stored
    /// `r_0 -> r`) to `r ≐ r`, which is trivially true - not an occurs-check
    /// failure. The x=x guard has to be re-checked *after* the redirect.
    #[test]
    fn test_repeated_variable_constraint_is_not_an_occurs_failure() {
        let f = Variable("f".to_string(), GLOBAL_INDEX);
        let r = Variable("r".to_string(), FIRST_INDEX);
        let r_0 = Variable("r_0".to_string(), FIRST_INDEX);

        let app = |arg1: &CicTerm, arg2: &CicTerm| {
            Application(
                Box::new(Application(
                    Box::new(f.clone()),
                    Box::new(arg1.clone()),
                )),
                Box::new(arg2.clone()),
            )
        };
        // `f(r_0, r_0) ≐ f(r, r)` derives `r_0 ≐ r`
        assert_eq!(
            cic_so_unification(&app(&r_0, &r_0), &app(&r, &r)).unwrap(),
            Substitution::from([("variable_r_0".to_string(), r)]),
            "deriving the same variable constraint twice must stay trivially solvable, not trip the occurs check"
        );
    }
}

#[test]
fn test_substitutability() {
    assert_eq!(
        is_substitutable(&Meta(420)),
        Some("metavariable_420".to_string()),
        "is_substitutable check doesnt return proper naming for a metavariable"
    );
    assert_eq!(
        is_substitutable(&Variable("super_idol".to_string(), 69)),
        Some("variable_super_idol".to_string()),
        "is_substitutable check doesnt return proper naming for a variable"
    );
    assert!(
        is_substitutable(&Sort("TYPE".to_string())).is_none(),
        "is_substitutable check returns a key for a term different from [meta]variables"
    );
    assert!(
        is_substitutable(&Application(Box::new(Variable("".to_string(), 0)), Box::new(Meta(0)))).is_none(),
        "is_substitutable check returns a key for a term different from [meta]variables"
    );
    assert!(
        is_substitutable(&Product("".to_string(), Box::new(Meta(0)), Box::new(Variable("".to_string(), 0)))).is_none(),
        "is_substitutable check returns a key for a term different from [meta]variables"
    );
    assert!(
        is_substitutable(&Abstraction("".to_string(), Box::new(Meta(0)), Box::new(Variable("".to_string(), 0)))).is_none(),
        "is_substitutable check returns a key for a term different from [meta]variables"
    );
    assert!(
        is_substitutable(&Match(
            Box::new(Variable("".to_string(), 0)),
            vec![
                (Variable("".to_string(), 0), Meta(0))
            ]
        )).is_none(),
        "is_substitutable check returns a key for a term different from [meta]variables"
    );
    assert!(
        is_substitutable(&Let("".to_string(), Box::new(Some(Meta(0))), Box::new(Variable("".to_string(), 0)), Box::new(Sort("TYPE".to_string())))).is_none(),
        "is_substitutable check returns a key for a term different from [meta]variables"
    );
}

#[test]
fn test_explosion() {
    let subterm1 = Sort("dope".to_string());
    let subterm2 = Sort("dope".to_string());
    assert_eq!(
        explode(&Sort("".to_string())),
        vec![],
        "CIC explosion doesnt produce the proper subcomponents vector"
    );
    assert_eq!(
        explode(&Meta(63)),
        vec![],
        "CIC explosion doesnt produce the proper subcomponents vector"
    );
    assert_eq!(
        explode(&Variable("".to_string(), 0)),
        vec![],
        "CIC explosion doesnt produce the proper subcomponents vector"
    );
    assert_eq!(
        explode(&Abstraction(
            "".to_string(),
            Box::new(subterm1.clone()),
            Box::new(subterm2.clone())
        )),
        vec![subterm1.clone(), subterm2.clone()],
        "CIC explosion doesnt produce the proper subcomponents vector"
    );
    assert_eq!(
        explode(&Product(
            "".to_string(),
            Box::new(subterm1.clone()),
            Box::new(subterm2.clone())
        )),
        vec![subterm1.clone(), subterm2.clone()],
        "CIC explosion doesnt produce the proper subcomponents vector"
    );
    assert_eq!(
        explode(&Application(
            Box::new(subterm1.clone()),
            Box::new(subterm2.clone())
        )),
        vec![subterm1.clone(), subterm2.clone()],
        "CIC explosion doesnt produce the proper subcomponents vector"
    );
    // TODO: test these too
    // assert_eq!(
    //     explode(&Match(subterm1.clone(), vec![(subterm2.clone(), ?)])),
    //     vec![],
    //     "CIC explosion doesnt produce the proper subcomponents vector"
    // );
    // assert_eq!(
    //     explode(&Let("".to_string())),
    //     vec![],
    //     "CIC explosion doesnt produce the proper subcomponents vector"
    // );
}

#[test]
fn test_cic_occurs() {
    let variable = Variable("name".to_string(), 0);
    let name_key = "variable_name";
    let meta = Meta(16 * 29);
    let meta_key = &format!("metavariable_{}", 16 * 29);
    let random = Sort("TYPE".to_string());

    assert!(
        occurs(&variable, name_key),
        "occurs check doesnt see variable"
    );
    assert!(
        occurs(
            &Application(
                Box::new(Variable("f".to_string(), GLOBAL_INDEX)),
                Box::new(variable.clone())
            ),
            name_key
        ),
        "occurs check doesnt see variable"
    );
    assert!(
        occurs(
            &Let(
                "".to_string(),
                Box::new(None),
                Box::new(Variable("exp".to_string(), 0)),
                Box::new(variable.clone())
            ),
            name_key
        ),
        "occurs check doesnt see variable"
    );

    assert!(
        occurs(&meta, meta_key),
        "occurs check doesnt see metavariable"
    );
    assert!(
        occurs(
            &Abstraction(
                "T".to_string(),
                Box::new(meta.clone()),
                Box::new(random.clone())
            ),
            meta_key
        ),
        "occurs check doesnt see metavariable"
    );
    assert!(
        occurs(
            &Application(
                Box::new(Variable("nil".to_string(), GLOBAL_INDEX)),
                Box::new(meta.clone())
            ),
            meta_key
        ),
        "occurs check doesnt see metavariable"
    );

    assert!(
        occurs(
            &Match(
                Box::new(Variable("".to_string(), 42)),
                vec![
                    (Variable("true".to_string(), 0), variable.clone()),
                    (Variable("false".to_string(), 0), meta.clone())
                ]
            ),
            name_key
        ),
        "occurs check doesnt see variable"
    );
    assert!(
        occurs(
            &Match(
                Box::new(Variable("".to_string(), 42)),
                vec![
                    (Variable("true".to_string(), 0), variable.clone()),
                    (Variable("false".to_string(), 0), meta.clone())
                ]
            ),
            meta_key
        ),
        "occurs check doesnt see metavariable"
    );
    assert!(
        !occurs(
            &Match(
                Box::new(Variable("".to_string(), 42)),
                vec![
                    (Variable("true".to_string(), 0), variable.clone()),
                    (Variable("false".to_string(), 0), meta.clone())
                ]
            ),
            "variable_missing_key"
        ),
        "occurs passes on unreferenced variable"
    );
    assert!(
        !occurs(&Sort(name_key.to_string()), name_key),
        "occurs check passes on a sort which isnt a substitutable term"
    );
    assert!(
        !occurs(&Sort(format!("{}", meta_key)), meta_key),
        "occurs check passes on a sort which isnt a substitutable term"
    );
    assert!(
        !occurs(
            &Abstraction(
                "T".to_string(),
                Box::new(Sort("TYPE".to_string())),
                Box::new(Sort("TYPE".to_string()))
            ),
            name_key
        ),
        "occurs check passes on a term that doesnt reference the variable"
    );
}

#[test]
fn test_plus_zero_one_unification() {
    let nat = Variable("Nat".to_string(), GLOBAL_INDEX);
    let mut env = Cic::default_environment();

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
        &mut env,
    )
    .expect("Failed to set up Nat");

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
                            Box::new(Variable("s".to_string(), GLOBAL_INDEX)),
                            Box::new(Variable("nn".to_string(), GLOBAL_INDEX)),
                        ),
                        Application(
                            Box::new(Variable("s".to_string(), GLOBAL_INDEX)),
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
        &mut env,
    )
    .expect("Failed to set up plus");

    let z = Variable("z".to_string(), GLOBAL_INDEX);
    let s = Variable("s".to_string(), GLOBAL_INDEX);
    let one = Application(Box::new(s.clone()), Box::new(z.clone()));
    let plus_zero_one = Application(
        Box::new(Application(
            Box::new(Variable("plus".to_string(), GLOBAL_INDEX)),
            Box::new(z.clone()),
        )),
        Box::new(one.clone()),
    );

    assert!(
        cic_solve_unifications(vec![(plus_zero_one, one)], &mut env).is_ok(),
        // cic_unification(&mut env, &plus_zero_one, &one).is_ok(),
        "plus(z, s(z)) should unify with s(z) after normalization"
    );
}
