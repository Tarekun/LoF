#[cfg(test)]
mod unit_tests {
    use std::{fs, path::PathBuf};

    use crate::{
        config::SelectionFunction,
        tptp::problem::{load_tptp_file, parse_tptp, Role, TptpFormula},
        type_theory::{
            grammars::cnf::{
                CnfFormula::{self, Atom, Clause, Equality, Not},
                CnfTerm::{self, Application, Variable},
            },
            sup::{
                freedom::{get_selection_fn, pick_clause},
                saturation::saturate,
            },
        },
    };

    fn var(name: &str) -> CnfTerm {
        Variable(name.to_string())
    }
    fn constant(name: &str) -> CnfTerm {
        Application(name.to_string(), vec![])
    }
    fn pred(name: &str, args: Vec<CnfTerm>) -> CnfFormula {
        Atom(name.to_string(), args)
    }
    fn not(φ: CnfFormula) -> CnfFormula {
        Not(Box::new(φ))
    }

    /// Creates a fresh directory under the system temp dir with the given files
    fn temp_workspace(test_name: &str, files: &[(&str, &str)]) -> PathBuf {
        let root = std::env::temp_dir().join(format!(
            "proofr_tptp_{}_{}",
            test_name,
            std::process::id()
        ));
        let _ = fs::remove_dir_all(&root);
        for (path, content) in files {
            let path = root.join(path);
            fs::create_dir_all(path.parent().unwrap()).unwrap();
            fs::write(path, content).unwrap();
        }
        root
    }

    /// Returns true iff SUP saturation finds a refutation of `clauses`
    fn refutes(clauses: &Vec<CnfFormula>) -> bool {
        let selection_fn = get_selection_fn(SelectionFunction::Maximal);
        saturate(clauses, &selection_fn, pick_clause).is_ok()
    }

    #[test]
    fn test_annotated_formulas() {
        let problem = parse_tptp(
            "% a mixed problem
            fof(ax, axiom, ![X]: (p(X) => q(X)), file('a.p', ax), [useful(info)]).
            /* block */ cnf(12, negated_conjecture, ~q(a)).
            fof('named conj', conjecture, q(a)).",
        )
        .unwrap();

        let summary: Vec<_> = problem
            .inputs
            .iter()
            .map(|input| (input.name.as_str(), input.role.clone()))
            .collect();
        assert_eq!(
            summary,
            vec![
                ("ax", Role::Axiom),
                ("12", Role::NegatedConjecture),
                ("'named conj'", Role::Conjecture),
            ],
            "TPTP parser doesnt read names and roles of annotated formulas"
        );
        assert_eq!(
            problem.inputs[1].formula,
            TptpFormula::Cnf(not(pred("q", vec![constant("a")])))
        );
        assert!(matches!(problem.inputs[0].formula, TptpFormula::Fol(_, _)));
    }

    #[test]
    fn test_invalid_problems() {
        assert!(
            parse_tptp("thf(t, type, a: $i).").is_err(),
            "TPTP parser accepts unsupported dialects"
        );
        assert!(
            parse_tptp("include('Axioms/SET001-0.ax').").is_err(),
            "TPTP string parser accepts includes it cannot resolve"
        );
        assert!(
            parse_tptp("cnf(c, axiom, p) cnf(d, axiom, q).").is_err(),
            "TPTP parser accepts annotated formulas not terminated by a dot"
        );
        assert!(parse_tptp("").unwrap().inputs.is_empty());
    }

    #[test]
    fn test_includes() {
        let root = temp_workspace(
            "includes",
            &[
                (
                    "Axioms/base.ax",
                    "cnf(a1, axiom, p(a)).\ncnf(a2, axiom, p(b)).\ninclude('extra.ax').",
                ),
                ("Axioms/extra.ax", "cnf(a3, axiom, p(c))."),
                (
                    "Problems/prob.p",
                    "include('../Axioms/base.ax', [a1, a3]).\ncnf(g, negated_conjecture, ~p(a)).",
                ),
                ("cyclic.p", "include('cyclic.p')."),
            ],
        );

        let problem =
            load_tptp_file(root.join("Problems/prob.p").to_str().unwrap())
                .unwrap();
        let names: Vec<_> = problem
            .inputs
            .iter()
            .map(|input| input.name.as_str())
            .collect();
        assert_eq!(
            names,
            vec!["a1", "a3", "g"],
            "Includes arent resolved recursively or their selection isnt applied"
        );

        assert!(
            load_tptp_file(root.join("cyclic.p").to_str().unwrap()).is_err(),
            "Cyclic includes arent detected"
        );
        assert!(
            load_tptp_file(root.join("missing.p").to_str().unwrap()).is_err()
        );

        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn test_fof_clausification() {
        let problem = parse_tptp(
            "fof(a1, axiom, ![X]: (man(X) => mortal(X))).
            fof(a2, axiom, man(socrates)).
            fof(c, conjecture, mortal(socrates)).",
        )
        .unwrap();

        assert_eq!(
            problem.to_clauses(),
            Ok(vec![
                Clause(vec![
                    not(pred("man", vec![var("X")])),
                    pred("mortal", vec![var("X")]),
                ]),
                pred("man", vec![constant("socrates")]),
                not(pred("mortal", vec![constant("socrates")])),
            ]),
            "FOF problem isnt clausified with a negated conjecture"
        );
    }

    #[test]
    fn test_skolem_witnesses_are_renamed_apart() {
        let problem = parse_tptp(
            "fof(a1, axiom, ?[X]: p(X)).
            fof(a2, axiom, ?[X]: q(X)).",
        )
        .unwrap();

        assert_eq!(
            problem.to_clauses(),
            Ok(vec![
                pred("p", vec![constant("sk0_0")]),
                pred("q", vec![constant("sk1_0")]),
            ]),
            "Skolem constants of different formulas clash or arent constants"
        );
    }

    #[test]
    fn test_fof_equality_clausification() {
        let problem =
            parse_tptp("fof(a, axiom, ![X]: (f(X) = X | a != b)).").unwrap();
        assert_eq!(
            problem.to_clauses(),
            Ok(vec![Clause(vec![
                Equality(
                    Application("f".to_string(), vec![var("X")]),
                    var("X")
                ),
                not(Equality(constant("a"), constant("b"))),
            ])]),
            "FOF equality isnt clausified to CNF equality"
        );
    }

    #[test]
    fn test_truth_constants() {
        let problem = parse_tptp(
            "cnf(t, axiom, p | $true).
            cnf(f, axiom, p | $false).
            cnf(bottom, axiom, $false).",
        )
        .unwrap();
        assert_eq!(
            problem.to_clauses(),
            Ok(vec![pred("p", vec![]), Clause(vec![])]),
            "Truth constants arent simplified away"
        );
    }

    #[test]
    fn test_fof_refutation() {
        let problem = parse_tptp(
            "fof(exists_p, axiom, ?[X]: p(X)).
            fof(p_implies_q, axiom, ![X]: (p(X) => q(X))).
            fof(goal, conjecture, ?[Y]: q(Y)).",
        )
        .unwrap();
        assert!(
            refutes(&problem.to_clauses().unwrap()),
            "SUP cant refute a clausified FOF problem"
        );

        let satisfiable =
            parse_tptp("fof(a, axiom, p(a)). fof(goal, conjecture, p(b)).")
                .unwrap();
        assert!(
            !refutes(&satisfiable.to_clauses().unwrap()),
            "SUP refutes a satisfiable clausified FOF problem"
        );
    }

    #[test]
    fn test_cnf_refutation() {
        let problem = parse_tptp(
            "cnf(e1, axiom, f(a) = b).
            cnf(e2, axiom, p(f(a))).
            cnf(transfer, axiom, ~p(X) | q(X)).
            cnf(goal, negated_conjecture, ~q(b)).",
        )
        .unwrap();
        assert!(
            refutes(&problem.to_clauses().unwrap()),
            "SUP cant refute a CNF problem with equality"
        );
    }
}
