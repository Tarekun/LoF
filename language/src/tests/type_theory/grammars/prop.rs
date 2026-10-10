use crate::{
    config::SelectionFunction,
    type_theory::{
        algorithms::saturation::saturation,
        grammars::{
            cnf::CnfFormula,
            prop::{
                PropFormula::{
                    self, Arrow, Atom, Conjunction, Disjunction, Not,
                },
                PropTerm::{
                    self, Abstraction, Application, Let, Tuple, Variable,
                },
            },
            traits::{BottomTop, Complement, NamedSubstitution, ToCnfFormula},
        },
        sup::freedom::{get_selection_fn, pick_clause},
    },
};
use std::collections::{BTreeSet, HashMap};

fn atom(name: &str) -> PropFormula {
    Atom(name.to_string())
}
fn not(φ: PropFormula) -> PropFormula {
    Not(Box::new(φ))
}
fn arrow(φ: PropFormula, ψ: PropFormula) -> PropFormula {
    Arrow(Box::new(φ), Box::new(ψ))
}
fn iff(φ: PropFormula, ψ: PropFormula) -> PropFormula {
    // Iff(Box::new(φ), Box::new(ψ))
    Conjunction(vec![
        Arrow(Box::new(φ.clone()), Box::new(ψ.clone())),
        Arrow(Box::new(ψ), Box::new(φ)),
    ])
}
fn var(name: &str) -> PropTerm {
    Variable(name.to_string())
}

/// Every valuation over `atoms`
fn all_valuations(atoms: &BTreeSet<String>) -> Vec<HashMap<String, bool>> {
    let atoms: Vec<_> = atoms.iter().collect();
    (0..1u32 << atoms.len())
        .map(|bits| {
            atoms
                .iter()
                .enumerate()
                .map(|(i, a)| (a.to_string(), bits & (1 << i) != 0))
                .collect()
        })
        .collect()
}

/// Asserts that `φ` and `ψ` have the same truth table
fn assert_equivalent(φ: &PropFormula, ψ: &PropFormula, message: &str) {
    let mut atoms = φ.atoms();
    atoms.extend(ψ.atoms());
    for valuation in all_valuations(&atoms) {
        assert_eq!(
            φ.evaluate(&valuation).unwrap(),
            ψ.evaluate(&valuation).unwrap(),
            "{message}: {φ} and {ψ} differ on {valuation:?}"
        );
    }
}

/// A few formulas using every connective, for semantic checks
fn sample_formulas() -> Vec<PropFormula> {
    let (a, b, c) = (atom("A"), atom("B"), atom("C"));
    vec![
        iff(a.clone(), b.clone()),
        not(iff(a.clone(), arrow(b.clone(), c.clone()))),
        arrow(
            Conjunction(vec![
                a.clone(),
                Disjunction(vec![b.clone(), Conjunction(vec![])]),
            ]),
            Disjunction(vec![not(c.clone()), Disjunction(vec![])]),
        ),
        Disjunction(vec![
            Conjunction(vec![a.clone(), b.clone()]),
            Conjunction(vec![not(a.clone()), c.clone()]),
        ]),
        not(Conjunction(vec![])),
        Disjunction(vec![]),
        Disjunction(vec![a.clone(), not(a.clone())]),
        Conjunction(vec![a.clone(), not(a.clone())]),
    ]
}

#[test]
fn test_display() {
    let (a, b, c) = (atom("A"), atom("B"), atom("C"));

    assert_eq!(
        Disjunction(vec![Conjunction(vec![a.clone(), b.clone()]), c.clone()])
            .to_string(),
        "A ∧ B ∨ C",
        "Display adds parentheses that precedence makes redundant"
    );
    assert_eq!(
        Conjunction(vec![Disjunction(vec![a.clone(), b.clone()]), c.clone()])
            .to_string(),
        "(A ∨ B) ∧ C",
        "Display drops parentheses required by precedence"
    );
    assert_eq!(
        arrow(a.clone(), arrow(b.clone(), c.clone())).to_string(),
        "A → B → C",
        "Display doesnt treat implication as right associative"
    );
    assert_eq!(
        arrow(arrow(a.clone(), b.clone()), c.clone()).to_string(),
        "(A → B) → C",
        "Display drops parentheses of left nested implications"
    );
    assert_eq!(
        format!("{:?}", Conjunction(vec![a.clone(), not(b.clone())])),
        "(A ∧ ¬(B))",
        "Debug isnt fully parenthesized"
    );
}

#[test]
fn test_checks() {
    let (a, b) = (atom("A"), atom("B"));

    assert!(a.is_literal() && not(a.clone()).is_literal());
    assert!(
        !not(not(a.clone())).is_literal(),
        "Double negation is accepted as a literal"
    );
    assert!(Disjunction(vec![a.clone(), not(b.clone())]).is_clause());
    assert!(Conjunction(vec![
        a.clone(),
        Disjunction(vec![a.clone(), b.clone()])
    ])
    .is_cnf());
    assert!(
        !Disjunction(vec![Conjunction(vec![a.clone(), b.clone()])]).is_cnf(),
        "Disjunction of conjunctions is accepted as CNF"
    );
    assert!(
        !arrow(a.clone(), b.clone()).is_nnf(),
        "Implication is accepted as NNF"
    );
    for φ in sample_formulas() {
        assert!(φ.negation_normal_form().is_nnf(), "NNF of {φ} isnt in NNF");
    }
}

#[test]
fn test_evaluation() {
    let valuation =
        HashMap::from([("A".to_string(), true), ("B".to_string(), false)]);

    assert_eq!(
        arrow(atom("A"), atom("B")).evaluate(&valuation).unwrap(),
        false,
        "True cant imply false"
    );
    assert_eq!(
        iff(atom("B"), Disjunction(vec![]))
            .evaluate(&valuation)
            .unwrap(),
        true,
        "Equivalence of falsities isnt true"
    );
    assert_eq!(Conjunction(vec![]).evaluate(&valuation).unwrap(), true);
    assert_eq!(Disjunction(vec![]).evaluate(&valuation).unwrap(), false);
    assert!(
        atom("C").evaluate(&valuation).is_err(),
        "Unassigned atom evaluated"
    );
}

#[test]
fn test_lookups() {
    let φ = arrow(atom("B"), Disjunction(vec![atom("A"), not(atom("B"))]));
    assert_eq!(
        φ.atoms(),
        BTreeSet::from(["A".to_string(), "B".to_string()])
    );

    let app = PropTerm::make_multiarg_app("f", &[var("x"), var("y")]);
    assert_eq!(
        app,
        Application(
            Box::new(Application(Box::new(var("f")), Box::new(var("x")))),
            Box::new(var("y"))
        )
    );
    assert_eq!(
        app.get_application_components().unwrap(),
        ("f".to_string(), vec![var("x"), var("y")])
    );

    let term = Abstraction(
        "x".to_string(),
        Box::new(atom("A")),
        Box::new(Tuple(vec![var("x"), var("y")])),
    );
    assert_eq!(
        term.free_variables(),
        BTreeSet::from(["y".to_string()]),
        "Bound variable is considered free"
    );
}

/// Returns `term` where each instance of `target_name` is substituted with `arg`
fn substituted<A, T: NamedSubstitution<A>>(
    mut term: T,
    target_name: &str,
    arg: &A,
) -> T {
    term.substitute_name(target_name, arg);
    term
}

#[test]
fn test_substitution() {
    // uniform substitution of atoms
    assert_eq!(
        substituted(
            arrow(atom("A"), atom("B")),
            "A",
            &Conjunction(vec![atom("B"), atom("C")])
        ),
        arrow(Conjunction(vec![atom("B"), atom("C")]), atom("B"))
    );

    // terms substitution respects shadowing
    let term = Application(
        Box::new(Abstraction(
            "x".to_string(),
            Box::new(atom("A")),
            Box::new(var("x")),
        )),
        Box::new(var("x")),
    );
    assert_eq!(
        substituted(term, "x", &var("y")),
        Application(
            Box::new(Abstraction(
                "x".to_string(),
                Box::new(atom("A")),
                Box::new(var("x")),
            )),
            Box::new(var("y")),
        ),
        "Substitution goes under a binder of the same name"
    );
    let term = Let(
        "x".to_string(),
        Box::new(None),
        Box::new(var("x")),
        Box::new(var("x")),
    );
    assert_eq!(
        substituted(term, "x", &var("y")),
        Let(
            "x".to_string(),
            Box::new(None),
            Box::new(var("y")),
            Box::new(var("x")),
        ),
        "Let substitution doesnt handle body and scope separately"
    );

    // atoms substitution in terms annotations
    let term =
        Abstraction("x".to_string(), Box::new(atom("A")), Box::new(var("A")));
    assert_eq!(
        substituted(term, "A", &atom("B")),
        Abstraction("x".to_string(), Box::new(atom("B")), Box::new(var("A"))),
        "Formula substitution in terms touches term variables"
    );
}

#[test]
fn test_negation_normal_form() {
    let (a, b) = (atom("A"), atom("B"));

    assert_eq!(
        not(Conjunction(vec![a.clone(), b.clone()])).negation_normal_form(),
        Disjunction(vec![not(a.clone()), not(b.clone())]),
        "NNF algorithm doesnt apply simple De Morgan on conjunctions"
    );
    assert_eq!(
        arrow(a.clone(), b.clone()).negation_normal_form(),
        Disjunction(vec![not(a.clone()), b.clone()]),
        "NNF algorithm doesnt resolve implications"
    );
    assert_eq!(
        not(not(a.clone())).negation_normal_form(),
        a.clone(),
        "NNF algorithm doesnt resolve double negation"
    );
    assert_eq!(
        not(Conjunction(vec![])).negation_normal_form(),
        Disjunction(vec![]),
        "NNF algorithm doesnt resolve negated constants"
    );
    for φ in sample_formulas() {
        assert_equivalent(&φ, &φ.negation_normal_form(), "NNF isnt equivalent");
    }
}

#[test]
fn test_normal_forms() {
    let (a, b, c) = (atom("A"), atom("B"), atom("C"));

    assert_eq!(
        Disjunction(vec![a.clone(), Conjunction(vec![b.clone(), c.clone()])])
            .conjunction_normal_form(),
        vec![
            Disjunction(vec![a.clone(), b.clone()]),
            Disjunction(vec![a.clone(), c.clone()]),
        ],
        "CNF algorithm doesnt distribute disjunction over conjunction"
    );
    assert_eq!(
        Disjunction(vec![a.clone(), not(a.clone())]).conjunction_normal_form(),
        vec![],
        "CNF algorithm keeps tautological clauses"
    );
    assert_eq!(
        Disjunction(vec![a.clone(), a.clone(), Disjunction(vec![])])
            .conjunction_normal_form(),
        vec![a.clone()],
        "CNF algorithm keeps duplicate literals or falsities"
    );
    assert_eq!(
        Conjunction(vec![a.clone(), not(a.clone())]).disjunction_normal_form(),
        vec![],
        "DNF algorithm keeps contradictory cubes"
    );
    assert_eq!(
        Disjunction(vec![]).conjunction_normal_form(),
        vec![Disjunction(vec![])]
    );
    assert_eq!(
        Conjunction(vec![]).disjunction_normal_form(),
        vec![Conjunction(vec![])]
    );

    for φ in sample_formulas() {
        let cnf = Conjunction(φ.conjunction_normal_form());
        let dnf = Disjunction(φ.disjunction_normal_form());
        assert!(cnf.is_cnf(), "{cnf} isnt in CNF");
        assert_equivalent(&φ, &cnf, "CNF isnt equivalent");
        assert_equivalent(&φ, &dnf, "DNF isnt equivalent");
    }
}

#[test]
fn test_complement() {
    assert_eq!(atom("A").complement(), not(atom("A")));
    assert_eq!(
        not(atom("A")).complement(),
        atom("A"),
        "Complement doesnt simplify double negation"
    );
    assert!(Conjunction(vec![]).is_top() && !Conjunction(vec![]).is_bottom());
    assert!(Disjunction(vec![]).is_bottom());
}

#[test]
fn test_to_cnf() {
    assert_eq!(
        arrow(atom("A"), atom("B")).to_cnf(),
        vec![CnfFormula::Clause(vec![
            CnfFormula::Not(Box::new(CnfFormula::Atom(
                "A".to_string(),
                vec![]
            ))),
            CnfFormula::Atom("B".to_string(), vec![]),
        ])]
    );
    assert_eq!(
        Disjunction(vec![]).to_cnf(),
        vec![CnfFormula::Clause(vec![])]
    );
    assert_eq!(Conjunction(vec![]).to_cnf(), vec![]);
}

#[test]
fn test_saturation_on_prop_formulas() {
    let (a, b, c) = (atom("A"), atom("B"), atom("C"));
    let selection_fn = get_selection_fn(SelectionFunction::All);

    // A → B, B → C ⊢ A → C
    let premises =
        vec![arrow(a.clone(), b.clone()), arrow(b.clone(), c.clone())];
    assert!(
        saturation(
            &premises,
            &[arrow(a.clone(), c.clone())],
            &selection_fn,
            pick_clause,
            false
        )
        .is_ok(),
        "Saturation cant prove transitivity of implication"
    );
    assert!(
        saturation(
            &premises,
            &[arrow(c.clone(), a.clone())],
            &selection_fn,
            pick_clause,
            false
        )
        .is_err(),
        "Saturation proves the converse of a chain of implications"
    );
}
