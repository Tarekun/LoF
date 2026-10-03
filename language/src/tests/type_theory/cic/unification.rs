use crate::parser::api::Statement::{Fun, Inductive};
use crate::type_theory::cic::cic::CicTerm::{
    self, Application, Match, Meta, Product, Sort, Variable,
};
use crate::type_theory::cic::cic::{Cic, NameKind};
use crate::type_theory::cic::metavariables::{MetaContext, NameGenerator};
use crate::type_theory::cic::unification::unify;
use crate::type_theory::environment::Environment;
use crate::type_theory::interface::{Kernel, TypeTheory};

fn constant(name: &str) -> CicTerm {
    Variable(name.to_string(), NameKind::Const())
}
fn local(name: &str) -> CicTerm {
    Variable(name.to_string(), NameKind::Local())
}
fn arrow(domain: CicTerm, codomain: CicTerm) -> CicTerm {
    Product("_".to_string(), Box::new(domain), Box::new(codomain))
}
fn app(function: CicTerm, argument: CicTerm) -> CicTerm {
    Application(Box::new(function), Box::new(argument))
}
fn typee() -> CicTerm {
    Sort("TYPE".to_string())
}
fn constraint(expected: CicTerm, actual: CicTerm) -> (CicTerm, CicTerm) {
    (expected, actual)
}
fn index(meta: &CicTerm) -> i32 {
    match meta {
        Meta(index) => *index,
        other => panic!("{:?} is not a metavariable", other),
    }
}
fn cic_unify(
    env: &Environment<Cic>,
    metas: &mut MetaContext,
    expected: &CicTerm,
    actual: &CicTerm,
) -> Result<(), crate::error::LofError> {
    unify(env, metas, &mut NameGenerator::default(), expected, actual)
}
/// Unifies all the `constraints`, failing if any of them is left postponed
fn solve(
    metas: &mut MetaContext,
    constraints: Vec<(CicTerm, CicTerm)>,
) -> Result<(), crate::error::LofError> {
    let env = Cic::default_environment();
    let mut names = NameGenerator::default();
    for (expected, actual) in constraints {
        unify(&env, metas, &mut names, &expected, &actual)?;
    }
    match metas.postponed().first() {
        None => Ok(()),
        Some(postponed) => Err(crate::error::LofError::custom(format!(
            "constraint {:?} left postponed",
            postponed
        ))),
    }
}

#[test]
fn test_dhm() {
    let nat = constant("Nat");
    let env = Cic::default_environment();
    let mut metas = MetaContext::default();
    let m0 = metas.fresh_meta(vec![], typee());
    cic_unify(&env, &mut metas, &m0, &nat).unwrap();
    assert_eq!(
        metas.instantiate(&m0),
        nat,
        "Unification couldnt solve one simple constraint"
    );

    let mut metas = MetaContext::default();
    let m0 = metas.fresh_meta(vec![], typee());
    let m1 = metas.fresh_meta(vec![], typee());
    solve(
        &mut metas,
        vec![
            constraint(m1.clone(), arrow(nat.clone(), m0.clone())),
            constraint(m0.clone(), nat.clone()),
        ],
    )
    .unwrap();
    assert_eq!(
        metas.instantiate(&m1),
        arrow(nat.clone(), nat.clone()),
        "Unification couldnt solve a problem with a function over metavariables"
    );
}

#[test]
fn test_only_metavariables_are_unification_variables() {
    let env = Cic::default_environment();
    let mut metas = MetaContext::default();
    let list_bool = app(constant("List"), constant("Bool"));

    assert!(
        cic_unify(&env, &mut metas, &list_bool, &app(constant("List"), local("T")))
            .is_err(),
        "local variables are rigid, they must not be substituted by unification"
    );
    assert!(
        cic_unify(&env, &mut metas, &constant("Nat"), &constant("Bool")).is_err(),
        "distinct constants must not unify"
    );
    assert!(
        cic_unify(&env, &mut metas, &typee(), &constant("Nat")).is_err(),
        "a sort must not unify with a constant"
    );
    let m0 = metas.fresh_meta(vec![], typee());
    cic_unify(&env, &mut metas, &list_bool, &app(constant("List"), m0.clone())).unwrap();
    assert_eq!(metas.instantiate(&m0), constant("Bool"));
}

#[test]
fn test_undeclared_metavariables_cannot_be_assigned() {
    let env = Cic::default_environment();
    let mut metas = MetaContext::default();
    assert!(
        cic_unify(&env, &mut metas, &Meta(42), &constant("Nat")).is_err(),
        "metavariables only exist in the context that declared them"
    );
}

#[test]
fn test_occurs_check() {
    let env = Cic::default_environment();
    let mut metas = MetaContext::default();
    let m0 = metas.fresh_meta(vec![], typee());
    assert!(
        cic_unify(&env, &mut metas, &m0, &app(constant("List"), m0.clone())).is_err(),
        "occurs check must prevent cyclic solutions"
    );
    assert!(
        cic_unify(&env, &mut metas, &m0, &m0).is_ok(),
        "trivial constraints are not occurs check failures"
    );
}

#[test]
fn test_scope_check() {
    let mut metas = MetaContext::default();
    let outside = metas.fresh_meta(vec![], constant("Nat"));
    let inside = metas.fresh_meta(vec![("x#0".to_string(), constant("Nat"))], constant("Nat"));

    assert!(
        solve(&mut metas, vec![constraint(outside, local("x#0"))]).is_err(),
        "a metavariable cannot be solved with a variable not in its context"
    );
    assert!(
        solve(&mut metas, vec![constraint(inside.clone(), local("x#0"))]).is_ok(),
        "a metavariable can be solved with a variable in its context"
    );
    assert_eq!(metas.decl(&index(&inside)).unwrap().assignment, Some(local("x#0")));
}

#[test]
fn test_binders_unify_under_opened_bodies() {
    let bound = |name: &str| Variable(name.to_string(), NameKind::Bound(0));
    // Πy:Nat. List y ≐ Πx:?0. List x
    let mut metas = MetaContext::default();
    let m0 = metas.fresh_meta(vec![], typee());
    solve(
        &mut metas,
        vec![constraint(
            Product("y".to_string(), Box::new(constant("Nat")), Box::new(app(constant("List"), bound("y")))),
            Product("x".to_string(), Box::new(m0.clone()), Box::new(app(constant("List"), bound("x")))),
        )],
    )
    .unwrap();
    assert_eq!(metas.instantiate(&m0), constant("Nat"));

    // Πy:Nat. List y ≐ Πx:Nat. List ?1 where ?1 lives under some other x
    let mut metas = MetaContext::default();
    let m1 = metas.fresh_meta(vec![("x#7".to_string(), constant("Nat"))], typee());
    assert!(
        solve(
            &mut metas,
            vec![constraint(
                Product("y".to_string(), Box::new(constant("Nat")), Box::new(app(constant("List"), bound("y")))),
                Product("x".to_string(), Box::new(constant("Nat")), Box::new(app(constant("List"), m1))),
            )],
        )
        .is_err(),
        "bodies are opened with a fresh local, that metavariables of other scopes cannot mention \
         (the refiner pushes expected types under binders instead, see `check`)"
    );
}

#[test]
fn test_flexible_constraints_are_postponed() {
    // (?0 Nat) ≐ (List Nat) can only be solved once ?0 is known
    let mut metas = MetaContext::default();
    let m0 = metas.fresh_meta(vec![], arrow(typee(), typee()));
    solve(
        &mut metas,
        vec![
            constraint(app(m0.clone(), constant("Nat")), app(constant("List"), constant("Nat"))),
            constraint(m0.clone(), constant("List")),
        ],
    )
    .expect("postponed constraints must be retried once progress is made");

    let mut metas = MetaContext::default();
    let m0 = metas.fresh_meta(vec![], arrow(typee(), typee()));
    assert!(
        solve(
            &mut metas,
            vec![constraint(
                app(m0, constant("Nat")),
                app(constant("List"), constant("Nat"))
            )],
        )
        .is_err(),
        "higher order constraints that cannot progress must fail"
    );
}

#[test]
fn test_match_unification() {
    let env = Cic::default_environment();
    let mut metas = MetaContext::default();
    let hole = metas.fresh_meta(vec![("b".to_string(), constant("Bool"))], typee());
    let body = typee();
    let matched = || Box::new(local("b"));
    cic_unify(
        &env,
        &mut metas,
        &Match(
            matched(),
            vec![
                (constant("true"), body.clone()),
                (constant("false"), body.clone()),
            ],
        ),
        &Match(
            matched(),
            vec![(constant("true"), hole.clone()), (constant("false"), body.clone())],
        ),
    )
    .unwrap();
    assert_eq!(
        metas.instantiate(&hole),
        body,
        "Unification couldnt solve unification of pattern match bodies"
    );
}

#[test]
fn test_plus_zero_one_unification() {
    let nat = constant("Nat");
    let mut env = Cic::default_environment();

    Cic::type_check_stm(
        &Inductive(
            "Nat".to_string(),
            vec![],
            Box::new(typee()),
            vec![
                ("z".to_string(), nat.clone()),
                ("s".to_string(), arrow(nat.clone(), nat.clone())),
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
                Box::new(Variable("n".to_string(), NameKind::Bound(1))),
                vec![
                    (
                        constant("z"),
                        Variable("m".to_string(), NameKind::Bound(0)),
                    ),
                    (
                        app(constant("s"), Variable("nn".to_string(), NameKind::Bound(0))),
                        app(
                            constant("s"),
                            app(
                                app(
                                    constant("plus"),
                                    Variable("nn".to_string(), NameKind::Bound(0)),
                                ),
                                Variable("m".to_string(), NameKind::Bound(1)),
                            ),
                        ),
                    ),
                ],
            )),
            true,
        ),
        &mut env,
    )
    .expect("Failed to set up plus");

    let one = app(constant("s"), constant("z"));
    let plus_zero_one = app(app(constant("plus"), constant("z")), one.clone());

    let mut metas = MetaContext::default();
    assert!(
        cic_unify(&env, &mut metas, &plus_zero_one, &one).is_ok(),
        "plus(z, s(z)) should unify with s(z) after normalization"
    );
    let m0 = metas.fresh_meta(vec![], nat.clone());
    cic_unify(&env, &mut metas, &app(constant("s"), m0.clone()), &plus_zero_one).unwrap();
    assert_eq!(
        metas.instantiate(&m0),
        constant("z"),
        "unification must work modulo reduction"
    );
}

/// unification used by the tactic engine
mod tactics_unification {
    use crate::parser::api::Statement::{Fun, Inductive};
    use crate::type_theory::cic::cic::CicTerm::{
        self, Abstraction, Application, Let, Match, Meta, Product, Sort, Variable,
    };
    use crate::type_theory::cic::cic::{Cic, NameKind, FIRST_INDEX};
    use crate::type_theory::cic::unification::{
        cic_so_unification,
        cic_solve_unifications, explode, is_substitutable, occurs,
        solve_unifications_unnormalized, structurally_equal,
    };
    use crate::type_theory::commons::unification::Substitution;
    use crate::type_theory::interface::{Kernel, TypeTheory};
    use std::collections::VecDeque;

    mod components {
        use crate::type_theory::cic::cic::NameKind;

        use super::*;

        #[test]
        fn test_variable_structural_equality() {
            assert!(
                structurally_equal(
                    &Variable("x".to_string(), NameKind::Bound(0)),
                    &Variable("y".to_string(), NameKind::Bound(0)),
                ),
                "bound variables at the same de Bruijn position should be equal regardless of name (they're alpha equivalent)"
            );

            assert!(
                !structurally_equal(
                    &Variable("x".to_string(), NameKind::Bound(0)),
                    &Variable("y".to_string(), NameKind::Bound(1)),
                ),
                "bound variables at different positions with different names must not be equal"
            );

            assert!(
                !structurally_equal(
                    &Variable("z".to_string(), NameKind::Const()),
                    &Variable("s".to_string(), NameKind::Const()),
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
                    Box::new(Variable("x".to_string(), NameKind::Bound(1))),
                )),
            );
            // (y,x) -> y
            let unifiable = Abstraction(
                "y".to_string(),
                Box::new(Sort("TYPE".to_string())),
                Box::new(Abstraction(
                    "x".to_string(),
                    Box::new(Sort("TYPE".to_string())),
                    Box::new(Variable("y".to_string(), NameKind::Bound(1))),
                )),
            );
            // (y,x) -> x
            let ununifiable = Abstraction(
                "y".to_string(),
                Box::new(Sort("TYPE".to_string())),
                Box::new(Abstraction(
                    "x".to_string(),
                    Box::new(Sort("TYPE".to_string())),
                    Box::new(Variable("x".to_string(), NameKind::Bound(2))),
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


    #[test]
    fn test_variable_ground_unification() {
        fn var(name: &str) -> CicTerm {
            Variable(name.to_string(), NameKind::Bound(-100))
        }
        let listbool = Application(Box::new(var("List")), Box::new(var("Bool")));
        let listt = Application(
            Box::new(var("List")),
            Box::new(Variable("T".to_string(), NameKind::Bound(FIRST_INDEX))),
        );
        assert!(cic_so_unification(&listbool, &listt).is_ok(), "nook");
    }

    #[test]
    fn test_dhm() {
        let nat = Variable("Nat".to_string(), NameKind::Const());
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
        let t = Variable("true".to_string(), NameKind::Const());
        let expected =
            Substitution::from([("metavariable_1".to_string(), t.clone())]);
        let constraints = vec![(
            Match(
                Box::new(Variable("b".to_string(), NameKind::Bound(0))),
                vec![
                    (t.clone(), Variable("b".to_string(), NameKind::Const())),
                    (
                        Variable("false".to_string(), NameKind::Const()),
                        Variable("b".to_string(), NameKind::Const()),
                    ),
                ],
            ),
            Match(
                Box::new(Variable("b".to_string(), NameKind::Bound(0))),
                vec![
                    (Meta(1), Variable("b".to_string(), NameKind::Const())),
                    (
                        Variable("false".to_string(), NameKind::Const()),
                        Variable("b".to_string(), NameKind::Const()),
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
                Box::new(Variable("b".to_string(), NameKind::Bound(0))),
                vec![
                    (
                        Variable("true".to_string(), NameKind::Const()),
                        body.clone(),
                    ),
                    (
                        Variable("false".to_string(), NameKind::Const()),
                        body.clone(),
                    ),
                ],
            ),
            Match(
                Box::new(Variable("b".to_string(), NameKind::Bound(0))),
                vec![
                    (Variable("true".to_string(), NameKind::Const()), Meta(2)),
                    (
                        Variable("false".to_string(), NameKind::Const()),
                        body.clone(),
                    ),
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
        use crate::type_theory::cic::cic::FIRST_INDEX;

        use super::*;

        // NOTE: this test is here atm, but im not sure CIC unification should really
        // support FO variable substitution

        // NOTE: imma be honest i dont think this should be a test at all even
        // assuming CIC unification should include FO substitution too `x` is
        // a FO variable and im pretty sure it should NOT be replaceable
        // with the type `Nat`
        #[test]
        fn test_solved_mgu_grounds_variable_keys_inside_meta_bodies() {
            let nat = Variable("Nat".to_string(), NameKind::Const());
            let list = Variable("List".to_string(), NameKind::Const());
            let x = Variable("x".to_string(), NameKind::Bound(FIRST_INDEX));

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
            let f = Variable("f".to_string(), NameKind::Const());
            let x = Variable("x".to_string(), NameKind::Bound(FIRST_INDEX));
            let y = Variable("y".to_string(), NameKind::Bound(FIRST_INDEX));

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
            let f = Variable("f".to_string(), NameKind::Const());
            let r = Variable("r".to_string(), NameKind::Bound(FIRST_INDEX));
            let r_0 = Variable("r_0".to_string(), NameKind::Bound(FIRST_INDEX));

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
            is_substitutable(&Variable(
                "super_idol".to_string(),
                NameKind::Bound(69)
            )),
            Some("variable_super_idol".to_string()),
            "is_substitutable check doesnt return proper naming for a variable"
        );
        assert!(
            is_substitutable(&Sort("TYPE".to_string())).is_none(),
            "is_substitutable check returns a key for a term different from [meta]variables"
        );
        assert!(
            is_substitutable(&Application(Box::new(Variable("".to_string(), NameKind::Bound(0))), Box::new(Meta(0)))).is_none(),
            "is_substitutable check returns a key for a term different from [meta]variables"
        );
        assert!(
            is_substitutable(&Product("".to_string(), Box::new(Meta(0)), Box::new(Variable("".to_string(), NameKind::Bound(0))))).is_none(),
            "is_substitutable check returns a key for a term different from [meta]variables"
        );
        assert!(
            is_substitutable(&Abstraction("".to_string(), Box::new(Meta(0)), Box::new(Variable("".to_string(), NameKind::Bound(0))))).is_none(),
            "is_substitutable check returns a key for a term different from [meta]variables"
        );
        assert!(
            is_substitutable(&Match(
                Box::new(Variable("".to_string(), NameKind::Bound(0))),
                vec![
                    (Variable("".to_string(), NameKind::Bound(0)), Meta(0))
                ]
            )).is_none(),
            "is_substitutable check returns a key for a term different from [meta]variables"
        );
        assert!(
            is_substitutable(&Let("".to_string(), Box::new(Some(Meta(0))), Box::new(Variable("".to_string(), NameKind::Bound(0))), Box::new(Sort("TYPE".to_string())))).is_none(),
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
            explode(&Variable("".to_string(), NameKind::Bound(0))),
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
        let variable = Variable("name".to_string(), NameKind::Bound(0));
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
                    Box::new(Variable("f".to_string(), NameKind::Const())),
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
                    Box::new(Variable("exp".to_string(), NameKind::Bound(0))),
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
                    Box::new(Variable("nil".to_string(), NameKind::Const())),
                    Box::new(meta.clone())
                ),
                meta_key
            ),
            "occurs check doesnt see metavariable"
        );

        assert!(
            occurs(
                &Match(
                    Box::new(Variable("".to_string(), NameKind::Bound(42))),
                    vec![
                        (
                            Variable("true".to_string(), NameKind::Bound(0)),
                            variable.clone()
                        ),
                        (
                            Variable("false".to_string(), NameKind::Bound(0)),
                            meta.clone()
                        )
                    ]
                ),
                name_key
            ),
            "occurs check doesnt see variable"
        );
        assert!(
            occurs(
                &Match(
                    Box::new(Variable("".to_string(), NameKind::Bound(42))),
                    vec![
                        (
                            Variable("true".to_string(), NameKind::Bound(0)),
                            variable.clone()
                        ),
                        (
                            Variable("false".to_string(), NameKind::Bound(0)),
                            meta.clone()
                        )
                    ]
                ),
                meta_key
            ),
            "occurs check doesnt see metavariable"
        );
        assert!(
            !occurs(
                &Match(
                    Box::new(Variable("".to_string(), NameKind::Bound(42))),
                    vec![
                        (
                            Variable("true".to_string(), NameKind::Bound(0)),
                            variable.clone()
                        ),
                        (
                            Variable("false".to_string(), NameKind::Bound(0)),
                            meta.clone()
                        )
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
        let nat = Variable("Nat".to_string(), NameKind::Const());
        let mut env = Cic::default_environment();

        Cic::type_check_stm(
            &Inductive(
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
                    Box::new(Variable("n".to_string(), NameKind::Bound(1))),
                    vec![
                        (
                            Variable("z".to_string(), NameKind::Const()),
                            Variable("m".to_string(), NameKind::Bound(0)),
                        ),
                        (
                            Application(
                                Box::new(Variable(
                                    "s".to_string(),
                                    NameKind::Const(),
                                )),
                                Box::new(Variable(
                                    "nn".to_string(),
                                    NameKind::Bound(0),
                                )),
                            ),
                            Application(
                                Box::new(Variable(
                                    "s".to_string(),
                                    NameKind::Const(),
                                )),
                                Box::new(Application(
                                    Box::new(Application(
                                        Box::new(Variable(
                                            "plus".to_string(),
                                            NameKind::Const(),
                                        )),
                                        Box::new(Variable(
                                            "nn".to_string(),
                                            NameKind::Bound(0),
                                        )),
                                    )),
                                    Box::new(Variable(
                                        "m".to_string(),
                                        NameKind::Bound(1),
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

        let z = Variable("z".to_string(), NameKind::Const());
        let s = Variable("s".to_string(), NameKind::Const());
        let one = Application(Box::new(s.clone()), Box::new(z.clone()));
        let plus_zero_one = Application(
            Box::new(Application(
                Box::new(Variable("plus".to_string(), NameKind::Const())),
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
}
