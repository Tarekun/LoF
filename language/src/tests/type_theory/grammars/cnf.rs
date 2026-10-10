use crate::type_theory::grammars::traits::SyntacticalEq;
use crate::type_theory::{
    commons::unification::Substitution,
    grammars::{
        cnf::CnfFormula::{self, Atom, Clause, Equality, ForAll, Not},
        cnf::CnfTerm::{self, Application, Variable},
        traits::Unification,
    },
};
use std::fmt::{self, Write};

#[test]
fn test_tautology_detection() {
    let variable = Variable("x".to_string());
    let p = Atom("P".to_string(), vec![variable.clone()]);
    let q = Atom("Q".to_string(), vec![variable.clone()]);
    let taut = Equality(variable.clone(), variable.clone());

    assert!(
        taut.is_tautology(),
        "Tautology detection couldnt notice simple equality of identicals"
    );
    assert!(
        !Clause(vec![]).is_tautology(),
        "Tautology detection accepts the empty clause"
    );

    assert!(
        Clause(vec![taut.clone()]).is_tautology(),
        "Tautology detection couldnt notice clause containing a tautology"
    );

    assert!(
        Clause(vec![p.clone(), q.clone(), Not(Box::new(p))]).is_tautology(),
        "Tautology detection couldnt notice clause with contradicting literals"
    );
}

#[test]
// TODO add check for unification
fn test_subsumption() {
    let variable = Variable("x".to_string());
    let p = Atom("P".to_string(), vec![variable.clone()]);
    let q = Atom("Q".to_string(), vec![variable.clone()]);

    assert!(
        Clause(vec![]).subsumes(&Clause(vec![p.clone()])),
        "subsumption check doesnt work with emtpy clause"
    );

    assert!(
        Clause(vec![p.clone()]).subsumes(&Clause(vec![p.clone()])),
        "subsumption check doesnt work with identical clauses"
    );

    assert!(
        Clause(vec![p.clone()])
            .subsumes(&Clause(vec![q.clone(), p.clone()])),
        "subsumption check doesnt work with emtpy clause that extend the first one"
    );
}

#[test]
fn test_term_unification() {
    let x = Variable("x".to_string());
    let y = Variable("y".to_string());
    let fx = Application("f".to_string(), vec![x.clone()]);
    let ffx = Application("f".to_string(), vec![fx.clone()]);

    assert!(
        x.unifies(&x).is_ok(),
        "Identical variable terms arent unified"
    );
    assert!(
        fx.unifies(&fx).is_ok(),
        "Identical application terms arent unified"
    );

    assert_eq!(
        Application("f".to_string(), vec![y.clone()]).unifies(&fx),
        Ok(Substitution::from([("y".to_string(), x.clone())])),
        "Unification didnt produce the proper MGU"
    );
    assert_eq!(
        Application("f".to_string(), vec![y.clone()]).unifies(&ffx),
        Ok(Substitution::from([("y".to_string(), fx.clone())])),
        "Unification didnt produce the proper MGU with deeper structure"
    );

    assert!(
        fx.unifies(&Application("f".to_string(), vec![x.clone(), y.clone()]))
            .is_err(),
        "Unifiable terms pass unification checks"
    );
    assert!(
        Application("f".to_string(), vec![x.clone()])
            .unifies(&ffx)
            .is_err(),
        "Unification passes on substitution that dont pass the occurs check"
    );
}

#[test]
fn test_fully_solved_mgu() {
    let x = Variable("x".to_string());
    let y = Variable("y".to_string());
    let fy = Application("f".to_string(), vec![y.clone()]);
    let k = Application("k".to_string(), vec![]);
    let s = Application("container".to_string(), vec![x.clone(), y.clone()]);
    let t = Application("container".to_string(), vec![fy.clone(), k.clone()]);

    assert_eq!(
        s.unifies(&t),
        Ok(Substitution::from([
            ("y".to_string(), k.clone()),
            (
                "x".to_string(),
                Application("f".to_string(), vec![k.clone()])
            )
        ])),
        // TODO: im not really sure this should be enforced at the terms_unify but whatever for now
        "Returned MGU didnt solve variable `y` to constant `k` in assignment for variable `x`"
    )
}

#[test]
fn test_formula_unification() {
    let x = Variable("x".to_string());
    let y = Variable("y".to_string());
    // let y = Variable("z".to_string());
    let fx = Application("f".to_string(), vec![x.clone()]);

    assert!(
        Atom("P".to_string(), vec![y.clone()])
            .unifies(&Atom("P".to_string(), vec![y.clone()]))
            .is_ok(),
        "Identical predicates dont unify"
    );
    assert!(
        Not(Box::new(Atom("P".to_string(), vec![y.clone()])))
            .unifies(&Not(Box::new(Atom("P".to_string(), vec![fx.clone()]))))
            .is_ok(),
        "Simple 1-step unification didnt pass"
    );
    assert!(
        Clause(vec![
            Atom("P".to_string(), vec![y.clone()]),
            Not(Box::new(Atom("P".to_string(), vec![y.clone()])))
        ])
        .unifies(&Clause(vec![
            Atom("P".to_string(), vec![y.clone()]),
            Not(Box::new(Atom("P".to_string(), vec![fx.clone()])))
        ]))
        .is_ok(),
        "Single formula-unification passed, but failed when inside a clause"
    );
    assert_eq!(
        Equality(Application("k".to_string(), vec![]), fx.clone()).unifies(
            &Equality(Application("k".to_string(), vec![]), y.clone())
        ),
        Ok(Substitution::from([("y".to_string(), fx.clone())])),
        "Unification didnt produce the proper MGU"
    );
}

fn var(name: &str) -> CnfTerm {
    Variable(name.to_string())
}
fn app(name: &str, args: Vec<CnfTerm>) -> CnfTerm {
    Application(name.to_string(), args)
}
fn constant(name: &str) -> CnfTerm {
    app(name, vec![])
}
fn atom(name: &str, args: Vec<CnfTerm>) -> CnfFormula {
    Atom(name.to_string(), args)
}
fn not(φ: CnfFormula) -> CnfFormula {
    Not(Box::new(φ))
}
fn forall(
    var_name: &str,
    var_type: CnfFormula,
    body: CnfFormula,
) -> CnfFormula {
    ForAll(var_name.to_string(), Box::new(var_type), Box::new(body))
}

/// Formatter sink accepting only `budget` writes, failing all the following ones
struct FailingWriter {
    budget: usize,
    written: String,
}
impl Write for FailingWriter {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        if self.budget == 0 {
            return Err(fmt::Error);
        }
        self.budget -= 1;
        self.written.push_str(s);
        Ok(())
    }
}

#[test]
fn test_debug_rendering() {
    let x = var("x");
    let k = constant("k");

    assert_eq!(format!("{:?}", x), "x", "Variable isnt rendered by name");
    assert_eq!(
        format!("{:?}", k),
        "<k>",
        "Constant isnt rendered in brackets"
    );
    assert_eq!(
        format!("{:?}", app("f", vec![x.clone(), k.clone()])),
        "f(x, <k>)",
        "Function application isnt rendered with comma separated arguments"
    );

    assert_eq!(
        format!("{:?}", atom("P", vec![])),
        "P",
        "Nullary predicate isnt rendered by name"
    );
    assert_eq!(
        format!("{:?}", atom("P", vec![x.clone(), k.clone()])),
        "P(x, <k>)",
        "Predicate isnt rendered with comma separated arguments"
    );
    assert_eq!(
        format!("{:?}", Clause(vec![])),
        "⊥",
        "Empty clause isnt rendered as bottom"
    );
    assert_eq!(
        format!(
            "{:?}",
            Clause(vec![atom("P", vec![]), not(atom("Q", vec![]))])
        ),
        "P ∨ ¬Q",
        "Clause isnt rendered as a disjunction of its literals"
    );
    assert_eq!(
        format!("{:?}", Equality(x.clone(), k.clone())),
        "x = <k>",
        "Equality isnt rendered with ="
    );
    assert_eq!(
        format!("{:?}", not(Equality(x.clone(), k.clone()))),
        "x≠<k>",
        "Negated equality isnt rendered with ≠"
    );
    assert_eq!(
        format!(
            "{:?}",
            forall("x", atom("Nat", vec![]), atom("P", vec![x.clone()]))
        ),
        "∀x:Nat. P(x)",
        "Universal quantification isnt rendered with its typed binder"
    );
}

#[test]
fn test_debug_propagates_formatter_errors() {
    fn check<T: fmt::Debug>(exp: &T) {
        let rendered = format!("{:?}", exp);
        for budget in 0.. {
            let mut writer = FailingWriter {
                budget,
                written: String::new(),
            };
            let result = write!(writer, "{:?}", exp);
            assert!(
                rendered.starts_with(&writer.written),
                "Failing formatter received {:?}, which isnt a prefix of {:?}",
                writer.written,
                rendered
            );
            if result.is_ok() {
                assert_eq!(writer.written, rendered);
                break;
            }
        }
    }

    let args = vec![app("g", vec![var("x")]), constant("k")];
    check(&app("f", args.clone()));
    check(&atom("P", args.clone()));
    check(&Clause(vec![atom("P", args.clone()), atom("Q", args)]));
}

#[test]
fn test_term_containment() {
    let x = var("x");
    let k = constant("k");
    let nested = app("f", vec![app("g", vec![x.clone()]), k.clone()]);

    assert!(x.contains(&x), "Term doesnt contain itself");
    assert!(nested.contains(&x), "Nested variable isnt found");
    assert!(nested.contains(&k), "Direct argument isnt found");
    assert!(
        !app("f", vec![var("y")]).contains(&x),
        "Application contains a variable not occurring in its arguments"
    );
    assert!(
        !x.contains(&app("f", vec![x.clone()])),
        "Variable contains a term bigger than itself"
    );
}

#[test]
fn test_syntactic_equality() {
    let fx = app("f", vec![var("x")]);

    assert!(fx.syntactically_equal(&fx.clone()));
    assert!(
        !fx.syntactically_equal(&app("f", vec![var("y")])),
        "Terms differing only by variable name are syntactically equal"
    );
    assert!(atom("P", vec![fx.clone()])
        .syntactically_equal(&atom("P", vec![fx.clone()])));
    assert!(
        !atom("P", vec![fx.clone()]).syntactically_equal(&atom("Q", vec![fx])),
        "Atoms with different predicates are syntactically equal"
    );
}

#[test]
fn test_tautology_detection_edge_cases() {
    let p = atom("P", vec![var("x")]);
    let q = atom("Q", vec![var("x")]);

    assert!(
        Clause(vec![not(p.clone()), p.clone()]).is_tautology(),
        "Tautology detection depends on the order of the complementary literals"
    );
    assert!(
        !Clause(vec![p.clone(), not(q.clone())]).is_tautology(),
        "Literals over different predicates are taken as complementary"
    );
    assert!(
        !Clause(vec![not(p.clone()), q.clone()]).is_tautology(),
        "Literals over different predicates are taken as complementary"
    );
    assert!(
        !Equality(var("x"), var("y")).is_tautology(),
        "Equality between distinct terms is a tautology"
    );
    assert!(!p.is_tautology(), "Single atom is a tautology");
}

#[test]
fn test_subsumption_edge_cases() {
    let p = atom("P", vec![var("x")]);
    let q = atom("Q", vec![var("x")]);

    assert!(
        !Clause(vec![p.clone(), q.clone()]).subsumes(&Clause(vec![p.clone()])),
        "Clause subsumes a clause missing one of its literals"
    );
    assert!(
        p.subsumes(&Clause(vec![q.clone(), p.clone()])),
        "Unit clauses given as bare literals dont subsume"
    );
    assert!(
        Clause(vec![p.clone()]).subsumes(&p),
        "Unit clauses given as bare literals arent subsumed"
    );
    assert!(
        !q.subsumes(&p),
        "Unit clause subsumes a unit clause with a different literal"
    );
    let equality = Equality(var("x"), var("y"));
    assert!(
        equality.subsumes(&Clause(vec![p.clone(), equality.clone()])),
        "Unit equalities dont subsume"
    );
}

#[test]
fn test_unpack_literals() {
    let p = atom("P", vec![]);
    let not_q = not(atom("Q", vec![]));

    assert_eq!(
        Clause(vec![p.clone(), not_q.clone()]).unpack_literals(),
        vec![p.clone(), not_q.clone()],
        "Clause isnt unpacked into its literals"
    );
    assert_eq!(
        not_q.unpack_literals(),
        vec![not_q.clone()],
        "Literal isnt unpacked as a singleton clause"
    );
}

#[test]
fn test_term_substitution() {
    let x = var("x");
    let k = constant("k");
    let gx = app("g", vec![x.clone()]);

    assert_eq!(
        app("f", vec![gx.clone(), var("y")]).substitute_term(&x, &k),
        app("f", vec![app("g", vec![k.clone()]), var("y")]),
        "Nested occurrences arent substituted, or others are touched"
    );
    assert_eq!(
        app("f", vec![gx.clone()]).substitute_term(&gx, &k),
        app("f", vec![k.clone()]),
        "Compound subterm isnt substituted as a whole"
    );
    assert_eq!(
        var("y").substitute_term(&x, &k),
        var("y"),
        "Variable different from the target is substituted"
    );
}

#[test]
fn test_formula_substitution() {
    let x = var("x");
    let k = constant("k");
    let formula = |t: &CnfTerm| {
        forall(
            "n",
            atom("Vec", vec![t.clone()]),
            Clause(vec![
                atom("P", vec![t.clone(), var("n")]),
                not(Equality(t.clone(), app("f", vec![t.clone()]))),
            ]),
        )
    };

    assert_eq!(
        formula(&x).substitute_formula(&x, &k),
        formula(&k),
        "Substitution didnt reach every term of the formula"
    );
}

#[test]
fn test_standardize_apart() {
    let x = var("x");
    let formula = forall(
        "x",
        atom("Nat", vec![]),
        Clause(vec![
            atom("P", vec![x.clone(), app("f", vec![var("y")])]),
            not(Equality(x.clone(), constant("k"))),
        ]),
    );

    let renamed = formula.standardize_apart();
    let ForAll(bound, _, _) = &renamed else {
        panic!("Standardizing apart changed the formula structure")
    };
    let suffix = bound
        .strip_prefix("x_")
        .expect("Bound variable wasnt renamed");
    let fresh = |name: &str| var(&format!("{}_{}", name, suffix));
    assert_eq!(
        renamed,
        forall(
            &format!("x_{}", suffix),
            atom("Nat", vec![]),
            Clause(vec![
                atom("P", vec![fresh("x"), app("f", vec![fresh("y")])]),
                not(Equality(fresh("x"), constant("k"))),
            ]),
        ),
        "Variables arent consistently renamed, or symbols got renamed"
    );

    let ForAll(bound_again, _, _) = formula.standardize_apart() else {
        panic!("Standardizing apart changed the formula structure")
    };
    assert_ne!(
        *bound, bound_again,
        "Two standardizations of the same clause share variables"
    );
}

#[test]
fn test_apply_substitution() {
    let substitution = Substitution::from([("x".to_string(), constant("k"))]);
    let formula = |t: CnfTerm| {
        forall(
            "n",
            atom("Vec", vec![t.clone()]),
            Clause(vec![
                atom("P", vec![app("f", vec![t.clone(), var("y")])]),
                not(Equality(t.clone(), var("y"))),
            ]),
        )
    };

    let mut unbound = var("y");
    unbound.apply_substitution(&substitution);
    assert_eq!(
        unbound,
        var("y"),
        "Unbound variable changed by the substitution"
    );
    let mut bound = formula(var("x"));
    bound.apply_substitution(&substitution);
    assert_eq!(
        bound,
        formula(constant("k")),
        "Substitution wasnt applied to every term of the formula"
    );
}

#[test]
fn test_formula_unification_solves_mgu() {
    let x = var("x");
    let y = var("y");
    let k = constant("k");

    assert_eq!(
        atom("P", vec![x.clone(), y.clone()])
            .unifies(&atom("P", vec![app("f", vec![y.clone()]), k.clone()])),
        Ok(Substitution::from([
            ("x".to_string(), app("f", vec![k.clone()])),
            ("y".to_string(), k.clone()),
        ])),
        "Formula MGU isnt fully solved"
    );
    assert_eq!(
        forall(
            "n",
            atom("Nat", vec![x.clone()]),
            atom("P", vec![y.clone()])
        )
        .unifies(&forall(
            "n",
            atom("Nat", vec![k.clone()]),
            atom("P", vec![k.clone()])
        )),
        Ok(Substitution::from([
            ("x".to_string(), k.clone()),
            ("y".to_string(), k.clone()),
        ])),
        "Quantifications with the same binder dont unify"
    );
}

#[test]
fn test_formula_unification_failures() {
    let x = var("x");
    let k = constant("k");
    let h = constant("h");
    let px = atom("P", vec![x.clone()]);
    let nat = atom("Nat", vec![]);
    let fails = |φ: CnfFormula, ψ: CnfFormula, reason: &str| {
        assert!(φ.unifies(&ψ).is_err(), "Unification passes with {}", reason);
    };

    fails(
        px.clone(),
        atom("Q", vec![x.clone()]),
        "different predicates",
    );
    fails(
        px.clone(),
        atom("P", vec![x.clone(), x.clone()]),
        "different arity",
    );
    fails(
        atom("P", vec![k.clone()]),
        atom("P", vec![h.clone()]),
        "clashing arguments",
    );
    fails(
        not(atom("P", vec![k.clone()])),
        not(atom("P", vec![h.clone()])),
        "clashing negated atoms",
    );
    fails(
        Equality(k.clone(), x.clone()),
        Equality(h.clone(), x.clone()),
        "clashing left sides",
    );
    fails(
        Equality(x.clone(), k.clone()),
        Equality(x.clone(), h.clone()),
        "clashing right sides",
    );
    fails(
        Clause(vec![px.clone()]),
        Clause(vec![px.clone(), px.clone()]),
        "clauses of different length",
    );
    fails(
        Clause(vec![atom("P", vec![k.clone()])]),
        Clause(vec![atom("P", vec![h.clone()])]),
        "clashing literals",
    );
    fails(
        forall("n", nat.clone(), px.clone()),
        forall("m", nat.clone(), px.clone()),
        "different binders",
    );
    fails(
        forall("n", atom("Vec", vec![k.clone()]), px.clone()),
        forall("n", atom("Vec", vec![h.clone()]), px.clone()),
        "clashing binder types",
    );
    fails(
        forall("n", nat.clone(), atom("P", vec![k.clone()])),
        forall("n", nat.clone(), atom("P", vec![h.clone()])),
        "clashing bodies",
    );
    fails(px.clone(), not(px.clone()), "different connectives");
}
