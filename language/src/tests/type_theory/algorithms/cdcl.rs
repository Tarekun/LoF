use super::{cdcl, cdcl_prove, Model};
use crate::type_theory::algorithms::dpll::dpll;
use crate::type_theory::grammars::{
    cnf::{
        CnfFormula::{self, Clause},
        CnfTerm,
    },
    prop::PropFormula::{self, Arrow, Atom, Conjunction, Disjunction, Not},
};
use std::collections::{BTreeSet, HashMap};

//########################### TEST HELPERS
fn atom(name: &str) -> PropFormula {
    Atom(name.to_string())
}
fn not(φ: PropFormula) -> PropFormula {
    Not(Box::new(φ))
}
fn arrow(φ: PropFormula, ψ: PropFormula) -> PropFormula {
    Arrow(Box::new(φ), Box::new(ψ))
}

/// Asserts that `model` satisfies every formula in `formulas`. Atoms missing
/// from `model` are unconstrained, so they're given an arbitrary value
fn assert_model(formulas: &[PropFormula], model: &Model) {
    let mut model = model.clone();
    for a in formulas.iter().flat_map(|φ| φ.atoms()) {
        model.entry(a).or_insert(false);
    }
    for φ in formulas {
        assert!(
            φ.evaluate(&model).unwrap(),
            "model {model:?} doesnt satisfy {φ}"
        );
    }
}

/// Decides satisfiability by enumerating every valuation
fn brute_force_sat(formulas: &[PropFormula]) -> bool {
    let atoms: Vec<String> = formulas
        .iter()
        .flat_map(|φ| φ.atoms())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
    (0..1u32 << atoms.len()).any(|bits| {
        let valuation: HashMap<String, bool> = atoms
            .iter()
            .enumerate()
            .map(|(i, a)| (a.to_string(), bits & (1 << i) != 0))
            .collect();
        formulas.iter().all(|φ| φ.evaluate(&valuation).unwrap())
    })
}

/// Pigeonhole principle: `pigeons` pigeons in `holes` holes, each pigeon in
/// some hole and no hole with two pigeons. Unsatisfiable iff pigeons > holes
fn pigeonhole(pigeons: usize, holes: usize) -> Vec<PropFormula> {
    let p = |i: usize, j: usize| atom(&format!("p{i}_{j}"));
    let mut formulas = vec![];
    for i in 0..pigeons {
        formulas.push(Disjunction((0..holes).map(|j| p(i, j)).collect()));
    }
    for j in 0..holes {
        for i in 0..pigeons {
            for k in i + 1..pigeons {
                formulas.push(not(Conjunction(vec![p(i, j), p(k, j)])));
            }
        }
    }
    formulas
}
//########################### TEST HELPERS

#[test]
fn test_trivial_instances() {
    assert_eq!(
        cdcl::<PropFormula>(&[]).unwrap(),
        Some(HashMap::new()),
        "Empty set of formulas isnt satisfiable"
    );
    assert!(
        cdcl(&[Conjunction(vec![])]).unwrap().is_some(),
        "⊤ isnt satisfiable"
    );
    assert!(
        cdcl(&[Disjunction(vec![])]).unwrap().is_none(),
        "⊥ is satisfiable"
    );
    assert!(
        cdcl(&[atom("A"), not(atom("A"))]).unwrap().is_none(),
        "Contradicting literals are satisfiable"
    );
}

#[test]
fn test_satisfiable_instances_have_models() {
    let instances = vec![
        vec![atom("A")],
        vec![Disjunction(vec![atom("A"), atom("B")]), not(atom("A"))],
        vec![arrow(atom("A"), atom("B")), atom("A")],
        // excluded middle only, every atom still gets a value
        vec![Disjunction(vec![atom("A"), not(atom("A"))])],
        pigeonhole(3, 3),
    ];
    for formulas in instances {
        let model = cdcl(&formulas)
            .unwrap()
            .unwrap_or_else(|| panic!("{formulas:?} found unsatisfiable"));
        assert_model(&formulas, &model);
    }
}

#[test]
fn test_unsatisfiable_instances() {
    assert!(
        cdcl(&[
            arrow(atom("A"), atom("B")),
            arrow(atom("B"), atom("C")),
            atom("A"),
            not(atom("C")),
        ])
        .unwrap()
        .is_none(),
        "Broken chain of implications is satisfiable"
    );
    assert!(
        cdcl(&pigeonhole(4, 3)).unwrap().is_none(),
        "Pigeonhole principle with more pigeons than holes is satisfiable"
    );
    assert!(
        cdcl(&pigeonhole(6, 5)).unwrap().is_none(),
        "Pigeonhole principle with more pigeons than holes is satisfiable"
    );
}

#[test]
fn test_agrees_with_truth_tables() {
    // deterministic linear congruential generator for random 3-CNFs
    let mut seed: u64 = 42;
    let mut next = |bound: u64| {
        seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
        (seed >> 33) % bound
    };

    for _ in 0..200 {
        let clauses_count = 1 + next(20);
        let formulas: Vec<PropFormula> = (0..clauses_count)
            .map(|_| {
                Disjunction(
                    (0..3)
                        .map(|_| {
                            let a = atom(&format!("x{}", next(6)));
                            if next(2) == 0 {
                                a
                            } else {
                                not(a)
                            }
                        })
                        .collect(),
                )
            })
            .collect();

        match cdcl(&formulas).unwrap() {
            Some(model) => assert_model(&formulas, &model),
            None => assert!(
                !brute_force_sat(&formulas),
                "{formulas:?} found unsatisfiable but it has a model"
            ),
        }
    }
}

#[test]
fn test_agrees_with_dpll() {
    // instances with too many atoms for truth tables, around the 3-SAT
    // threshold of 4.26 clauses per atom, where conflicts are frequent
    let mut seed: u64 = 7;
    let mut next = |bound: u64| {
        seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
        (seed >> 33) % bound
    };

    for _ in 0..50 {
        let atoms_count = 20;
        let formulas: Vec<PropFormula> = (0..85)
            .map(|_| {
                Disjunction(
                    (0..3)
                        .map(|_| {
                            let a = atom(&format!("x{}", next(atoms_count)));
                            if next(2) == 0 {
                                a
                            } else {
                                not(a)
                            }
                        })
                        .collect(),
                )
            })
            .collect();

        match cdcl(&formulas).unwrap() {
            Some(model) => assert_model(&formulas, &model),
            None => assert!(
                dpll(&formulas).unwrap().is_none(),
                "{formulas:?} found unsatisfiable but DPLL finds a model"
            ),
        }
    }
}

#[test]
fn test_proving() {
    let (a, b, c) = (atom("A"), atom("B"), atom("C"));

    assert_eq!(
        cdcl_prove(&[arrow(a.clone(), b.clone()), a.clone()], &[b.clone()])
            .unwrap(),
        None,
        "CDCL cant prove modus ponens"
    );
    assert_eq!(
        cdcl_prove(
            &[arrow(a.clone(), b.clone()), arrow(b.clone(), c.clone())],
            &[arrow(a.clone(), c.clone())]
        )
        .unwrap(),
        None,
        "CDCL cant prove transitivity of implication"
    );
    assert_eq!(
        cdcl_prove(&[], &[Disjunction(vec![a.clone(), not(a.clone())])])
            .unwrap(),
        None,
        "CDCL cant prove excluded middle"
    );

    // the converse doesnt hold, and the countermodel shows why
    let premises = [arrow(a.clone(), b.clone())];
    let countermodel = cdcl_prove(&premises, &[arrow(b.clone(), a.clone())])
        .unwrap()
        .expect("CDCL proves the converse of an implication");
    assert_model(&premises, &countermodel);
    assert!(
        !arrow(b, a).evaluate(&countermodel).unwrap(),
        "Countermodel doesnt falsify the goal"
    );
}

#[test]
fn test_rejects_non_propositional_literals() {
    let x = CnfTerm::Variable("x".to_string());
    let y = CnfTerm::Variable("y".to_string());
    assert!(
        cdcl(&[CnfFormula::Atom("P".to_string(), vec![x.clone()])]).is_err(),
        "CDCL accepts atoms with arguments"
    );
    assert!(
        cdcl(&[Clause(vec![CnfFormula::Equality(x.clone(), y)])]).is_err(),
        "CDCL accepts equalities"
    );
}
