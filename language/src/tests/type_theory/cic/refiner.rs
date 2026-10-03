use crate::{
    config::Config,
    misc::Union::L,
    parser::api::{LofParser, Statement},
    runtime::program::ProgramNode,
    type_theory::{
        cic::{
            cic::{
                Cic,
                CicTerm::{self, Abstraction, Application, Match, Meta, Product, Sort, Variable},
                NameKind, HOLE_INDEX,
            },
            evaluation::evaluate_inductive,
            refiner::{refine_expression, refine_statement},
        },
        environment::Environment,
        interface::{Kernel, Stm, TypeTheory},
    },
};

fn constant(name: &str) -> CicTerm {
    Variable(name.to_string(), NameKind::Const())
}
fn bound(name: &str, dbi: i32) -> CicTerm {
    Variable(name.to_string(), NameKind::Bound(dbi))
}
fn app(function: CicTerm, args: Vec<CicTerm>) -> CicTerm {
    args.into_iter().fold(function, |acc, arg| {
        Application(Box::new(acc), Box::new(arg))
    })
}
fn arrow(domain: CicTerm, codomain: CicTerm) -> CicTerm {
    Product("_".to_string(), Box::new(domain), Box::new(codomain))
}
fn typee() -> CicTerm {
    Sort("TYPE".to_string())
}

/// Environment with Nat, Bool and List(T) inductive types
fn inductive_env() -> Environment<Cic> {
    let mut env = Cic::default_environment();
    let nat = constant("Nat");
    let _ = evaluate_inductive(
        &mut env,
        "Nat",
        &vec![],
        &typee(),
        &vec![
            ("z".to_string(), nat.clone()),
            ("s".to_string(), arrow(nat.clone(), nat.clone())),
        ],
    );
    let _ = evaluate_inductive(
        &mut env,
        "Bool",
        &vec![],
        &typee(),
        &vec![
            ("true".to_string(), constant("Bool")),
            ("false".to_string(), constant("Bool")),
        ],
    );
    let list_t = app(constant("List"), vec![bound("T", 0)]);
    let _ = evaluate_inductive(
        &mut env,
        "List",
        &vec![("T".to_string(), typee())],
        &typee(),
        &vec![
            ("nil".to_string(), list_t.clone()),
            (
                "cons".to_string(),
                arrow(
                    bound("T", 0),
                    arrow(app(constant("List"), vec![bound("T", 1)]), app(constant("List"), vec![bound("T", 2)])),
                ),
            ),
        ],
    );
    env
}

/// Refines `term` and type checks the result with the kernel
fn refine_and_check(
    env: &mut Environment<Cic>,
    term: &CicTerm,
) -> Result<(CicTerm, CicTerm), crate::error::LofError> {
    let refined = refine_expression(env, term)?;
    let refined_type = Cic::type_check_term(&refined, env)?;
    Ok((refined, refined_type))
}

fn parse_stm(code: &str) -> Stm<Cic> {
    let parser = LofParser::new(Config::default());
    let (_, stm) = parser.parse_statement(code).unwrap();
    match Cic::elaborate_statement(&stm).unwrap().peek_first().unwrap().clone() {
        ProgramNode::OfStm(stm) => stm,
        _ => unreachable!(),
    }
}

#[test]
fn test_abstraction_inference() {
    let nat = constant("Nat");
    let mut env = inductive_env();

    // λ n:?. s n
    let term = Abstraction(
        "n".to_string(),
        Box::new(Meta(HOLE_INDEX)),
        Box::new(app(constant("s"), vec![bound("n", 0)])),
    );
    assert_eq!(
        refine_and_check(&mut env, &term),
        Ok((
            Abstraction(
                "n".to_string(),
                Box::new(nat.clone()),
                Box::new(app(constant("s"), vec![bound("n", 0)])),
            ),
            Product("n".to_string(), Box::new(nat.clone()), Box::new(nat.clone())),
        )),
        "Refiner cant infer the type of an argument applied to a function Nat->Nat"
    );
}

#[test]
fn test_application_inference() {
    let mut env = inductive_env();
    let nat = constant("Nat");
    env.add_to_context("elem", &nat);
    env.add_to_context("li", &app(constant("List"), vec![nat.clone()]));
    // id : ΠT:TYPE. Πx:T. T
    env.add_to_context(
        "id",
        &Product(
            "T".to_string(),
            Box::new(typee()),
            Box::new(Product("x".to_string(), Box::new(bound("T", 0)), Box::new(bound("T", 1)))),
        ),
    );

    // cons ? elem li
    let (refined, refined_type) = refine_and_check(
        &mut env,
        &app(constant("cons"), vec![Meta(HOLE_INDEX), constant("elem"), constant("li")]),
    )
    .unwrap();
    assert_eq!(
        refined,
        app(constant("cons"), vec![nat.clone(), constant("elem"), constant("li")]),
        "Refiner doesnt fill the type argument of cons"
    );
    assert_eq!(refined_type, app(constant("List"), vec![nat.clone()]));

    // λ n:Nat. id ? n
    let (refined, refined_type) = refine_and_check(
        &mut env,
        &Abstraction(
            "n".to_string(),
            Box::new(nat.clone()),
            Box::new(app(constant("id"), vec![Meta(HOLE_INDEX), bound("n", 0)])),
        ),
    )
    .unwrap();
    assert_eq!(
        refined,
        Abstraction(
            "n".to_string(),
            Box::new(nat.clone()),
            Box::new(app(constant("id"), vec![nat.clone(), bound("n", 0)])),
        ),
    );
    assert_eq!(
        refined_type,
        Product("n".to_string(), Box::new(nat.clone()), Box::new(nat.clone())),
        "Refiner cant infer the output type of a polymorphic function"
    );

    assert!(
        refine_and_check(
            &mut env,
            &app(constant("cons"), vec![Meta(HOLE_INDEX), constant("elem"), constant("elem")]),
        )
        .is_err(),
        "Refiner accepts an ill typed application"
    );
}

#[test]
fn test_match_inference() {
    let mut env = inductive_env();
    let tt = constant("true");
    let matc = Match(
        Box::new(app(constant("nil"), vec![constant("Bool")])),
        vec![
            (app(constant("nil"), vec![Meta(HOLE_INDEX)]), tt.clone()),
            (
                app(constant("cons"), vec![Meta(HOLE_INDEX), bound("h", 1), bound("l", 0)]),
                tt.clone(),
            ),
        ],
    );

    let (refined, refined_type) = refine_and_check(&mut env, &matc)
        .expect("Match refinement fails when patterns make use of holes");
    assert_eq!(refined_type, constant("Bool"));
    assert_eq!(
        refined, matc,
        "holes in pattern parameter positions are wildcards, they are left untouched"
    );
}

#[test]
fn test_unsolved_holes_are_rejected() {
    let mut env = inductive_env();
    // λ x:?. x
    let identity = Abstraction("x".to_string(), Box::new(Meta(HOLE_INDEX)), Box::new(bound("x", 0)));
    let result = refine_expression(&mut env, &identity);
    assert!(
        result.is_err(),
        "Refiner must reject holes nothing can determine, got {:?}",
        result
    );
    assert!(
        format!("{:?}", result).contains("Could not infer hole"),
        "Unsolved holes must be reported as such, got {:?}",
        result
    );
}

#[test]
fn test_undeclared_metavariables_are_rejected() {
    let mut env = inductive_env();
    assert!(
        refine_expression(&mut env, &app(constant("s"), vec![Meta(0)])).is_err(),
        "metavariables only exist in the refinement that declared them: \
         elaborated terms can only contain holes"
    );
}

#[test]
fn test_refined_binders_get_their_names_back() {
    let mut env = inductive_env();
    // λ A:TYPE. λ x:?. x : ΠA:TYPE. Πx:?. ?   with the hole solved by `A`
    // thanks to the annotation below
    let term = CicTerm::Let(
        "f".to_string(),
        Box::new(Some(Product(
            "A".to_string(),
            Box::new(typee()),
            Box::new(Product("x".to_string(), Box::new(bound("A", 0)), Box::new(bound("A", 1)))),
        ))),
        Box::new(Abstraction(
            "A".to_string(),
            Box::new(typee()),
            Box::new(Abstraction("x".to_string(), Box::new(Meta(HOLE_INDEX)), Box::new(bound("x", 0)))),
        )),
        Box::new(constant("z")),
    );
    let (refined, refined_type) = refine_and_check(&mut env, &term).unwrap();
    assert_eq!(refined_type, constant("Nat"));
    match refined {
        CicTerm::Let(_, _, definition, _) => assert_eq!(
            *definition,
            Abstraction(
                "A".to_string(),
                Box::new(typee()),
                Box::new(Abstraction("x".to_string(), Box::new(bound("A", 0)), Box::new(bound("x", 0)))),
            ),
            "a hole solved with a local variable must become the right De Bruijn index"
        ),
        other => panic!("unexpected refined term {:?}", other),
    }
}

#[test]
fn test_refine_statements() {
    let mut env = inductive_env();

    let fun = parse_stm("fun f (l: List(?)) : List(Nat) { l }");
    let refined = refine_statement(&mut env, &fun).expect("fun refinement failed");
    match &refined {
        Statement::Fun(_, args, _, _, _) => assert_eq!(
            args,
            &vec![("l".to_string(), app(constant("List"), vec![constant("Nat")]))]
        ),
        other => panic!("unexpected refined statement {:?}", other),
    }
    assert!(Cic::type_check_stm(&refined, &mut env).is_ok());

    let unsolvable = parse_stm("fun g (l: List(?)) : Nat { z }");
    assert!(
        refine_statement(&mut env, &unsolvable).is_err(),
        "holes in signatures that nothing determines must be rejected"
    );

    let theorem = parse_stm(
        "theorem t : ∀n:Nat. Nat :=\n  begin\n  intro m : Nat\n  exact s(m)\n  qed.",
    );
    let refined = refine_statement(&mut env, &theorem).expect("theorem refinement failed");
    match &refined {
        Statement::Theorem(_, _, L(proof)) => assert_eq!(
            proof,
            &Abstraction(
                "m".to_string(),
                Box::new(constant("Nat")),
                Box::new(app(constant("s"), vec![bound("m", 0)])),
            ),
            "tactics must be run into a proof term"
        ),
        other => panic!("unexpected refined statement {:?}", other),
    }
    assert!(
        Cic::type_check_stm(&refined, &mut env).is_ok(),
        "the kernel must accept the proof built by tactics"
    );
}

