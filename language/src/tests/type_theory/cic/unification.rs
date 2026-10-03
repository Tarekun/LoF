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
