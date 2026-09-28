#[cfg(test)]
mod unit_tests {
    use crate::{
        config::SelectionFunction,
        tptp::problem::{load_tptp_file, Role, TptpFormula},
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

    /// Returns the path of the CNF test artifact `file_name`
    fn artifact(file_name: &str) -> String {
        format!(
            "{}/../test_artifacts/tptp/cnf/{}",
            env!("CARGO_MANIFEST_DIR"),
            file_name
        )
    }

    /// Loads the CNF test artifact `file_name` as (name, role, clause) triples
    fn load_cnf(file_name: &str) -> Vec<(String, Role, CnfFormula)> {
        load_tptp_file(&artifact(file_name))
            .unwrap_or_else(|err| panic!("Cannot load {}: {}", file_name, err))
            .inputs
            .into_iter()
            .map(|input| match input.formula {
                TptpFormula::Cnf(clause) => (input.name, input.role, clause),
                other => panic!("Expected a CNF formula, found {:?}", other),
            })
            .collect()
    }

    fn var(name: &str) -> CnfTerm {
        Variable(name.to_string())
    }
    fn constant(name: &str) -> CnfTerm {
        Application(name.to_string(), vec![])
    }
    fn fun(name: &str, args: Vec<CnfTerm>) -> CnfTerm {
        Application(name.to_string(), args)
    }
    fn pred(name: &str, args: Vec<CnfTerm>) -> CnfFormula {
        Atom(name.to_string(), args)
    }
    fn not(φ: CnfFormula) -> CnfFormula {
        Not(Box::new(φ))
    }
    fn input(
        name: &str,
        role: Role,
        clause: CnfFormula,
    ) -> (String, Role, CnfFormula) {
        (name.to_string(), role, clause)
    }

    #[test]
    fn test_horn_clauses() {
        assert_eq!(
            load_cnf("socrates.p"),
            vec![
                input(
                    "men_are_mortal",
                    Role::Axiom,
                    Clause(vec![
                        not(pred("man", vec![var("X")])),
                        pred("mortal", vec![var("X")]),
                    ])
                ),
                input(
                    "socrates_is_a_man",
                    Role::Axiom,
                    pred("man", vec![constant("socrates")])
                ),
                input(
                    "socrates_is_not_mortal",
                    Role::NegatedConjecture,
                    not(pred("mortal", vec![constant("socrates")]))
                ),
            ],
            "socrates.p isnt parsed to the expected clauses"
        );
    }

    #[test]
    fn test_equational_clauses() {
        let multiply = |l: CnfTerm, r: CnfTerm| fun("multiply", vec![l, r]);
        assert_eq!(
            load_cnf("equality.p"),
            vec![
                input(
                    "left_identity",
                    Role::Axiom,
                    Equality(
                        multiply(constant("identity"), var("X")),
                        var("X")
                    )
                ),
                input(
                    "associativity",
                    Role::Axiom,
                    Equality(
                        multiply(multiply(var("X"), var("Y")), var("Z")),
                        multiply(var("X"), multiply(var("Y"), var("Z")))
                    )
                ),
                input(
                    "distinct_elements",
                    Role::Axiom,
                    not(Equality(constant("a"), constant("b")))
                ),
                input(
                    "conditional_equality",
                    Role::Hypothesis,
                    Clause(vec![
                        Equality(var("X"), var("Y")),
                        not(pred("equivalent", vec![var("X"), var("Y")])),
                        not(Equality(
                            fun("f", vec![var("X")]),
                            fun("f", vec![var("Y")])
                        )),
                    ])
                ),
            ],
            "equality.p isnt parsed to the expected clauses"
        );
    }

    #[test]
    fn test_lexical_corner_cases() {
        assert_eq!(
            load_cnf("syntax.p"),
            vec![
                input(
                    "quoted_atoms",
                    Role::Axiom,
                    pred("abc", vec![constant("'Mixed Case'"), var("X")])
                ),
                input(
                    "literals",
                    Role::Axiom,
                    pred(
                        "value",
                        vec![
                            constant("\"forty two\""),
                            constant("42"),
                            constant("-1/2"),
                        ]
                    )
                ),
                input(
                    "7",
                    Role::Plain,
                    Clause(vec![
                        pred("p", vec![var("X")]),
                        pred("q", vec![var("X")]),
                    ])
                ),
                input(
                    "bottom",
                    Role::NegatedConjecture,
                    pred("$false", vec![])
                ),
            ],
            "syntax.p isnt parsed to the expected clauses"
        );
    }

    #[test]
    fn test_includes() {
        let multiply = |l: CnfTerm, r: CnfTerm| fun("multiply", vec![l, r]);
        assert_eq!(
            load_cnf("group_problem.p"),
            vec![
                input(
                    "left_identity",
                    Role::Axiom,
                    Equality(
                        multiply(constant("identity"), var("X")),
                        var("X")
                    )
                ),
                input(
                    "left_inverse",
                    Role::Axiom,
                    Equality(
                        multiply(fun("inverse", vec![var("X")]), var("X")),
                        constant("identity")
                    )
                ),
                input(
                    "prove_right_identity",
                    Role::NegatedConjecture,
                    not(Equality(
                        multiply(constant("a"), constant("identity")),
                        constant("a")
                    ))
                ),
            ],
            "group_problem.p doesnt resolve its selective include"
        );
    }

    #[test]
    fn test_clauses_for_saturation() {
        let clauses = load_tptp_file(&artifact("syntax.p"))
            .unwrap()
            .to_clauses()
            .unwrap();
        assert_eq!(
            clauses.last(),
            Some(&Clause(vec![])),
            "$false isnt simplified to the empty clause"
        );

        let clauses = load_tptp_file(&artifact("socrates.p"))
            .unwrap()
            .to_clauses()
            .unwrap();
        let selection_fn = get_selection_fn(SelectionFunction::Maximal);
        assert!(
            saturate(&clauses, &selection_fn, pick_clause).is_ok(),
            "SUP cant refute socrates.p"
        );
    }
}

/// End to end tests: TPTP source → CNF → SUP saturation. Every problem under
/// `test_artifacts/tptp/saturation` declares its expected outcome with the
/// TPTP `% Status` header, so new problems need no code changes
#[cfg(test)]
mod end_to_end {
    use crate::{
        config::SelectionFunction,
        tptp::problem::load_tptp_file,
        type_theory::sup::{
            freedom::{
                get_selection_fn, pick_clause, pick_clause_weighted,
                GivingClauseSignature,
            },
            saturation::saturate,
        },
    };
    use std::{fs, path::Path, sync::mpsc, thread, time::Duration};

    /// Saturation has no resource limit, a run exceeding this is reported
    /// as a failure instead of hanging the test suite
    const TIMEOUT: Duration = Duration::from_secs(10);

    #[derive(Debug, PartialEq)]
    enum Outcome {
        /// the empty clause was derived
        Refuted,
        /// the clause set saturated without contradiction
        Saturated,
        TimedOut,
    }

    /// Returns the outcome expected by the `% Status` header of `source`
    fn expected_outcome(source: &str) -> Result<Outcome, String> {
        let status = source
            .lines()
            .find_map(|line| line.strip_prefix("% Status"))
            .and_then(|rest| rest.split(':').nth(1))
            .map(str::trim)
            .ok_or("missing `% Status :` header")?;
        match status {
            "Unsatisfiable" | "Theorem" => Ok(Outcome::Refuted),
            "Satisfiable" | "CounterSatisfiable" => Ok(Outcome::Saturated),
            other => Err(format!("unknown status `{}`", other)),
        }
    }

    /// Runs saturation on a separate thread, giving up after `TIMEOUT`.
    /// Saturation fails only when it runs out of clauses, as TPTP problems
    /// carry no answer literals, so an error means the set is satisfiable
    fn saturate_with_timeout(
        path: &str,
        giving_clause_fn: GivingClauseSignature,
    ) -> Result<Outcome, String> {
        let clauses = load_tptp_file(path)
            .and_then(|problem| problem.to_clauses())
            .map_err(|err| err.to_string())?;

        let (sender, receiver) = mpsc::channel();
        thread::spawn(move || {
            let selection_fn = get_selection_fn(SelectionFunction::Maximal);
            let refuted =
                saturate(&clauses, &selection_fn, giving_clause_fn).is_ok();
            let _ = sender.send(refuted);
        });

        match receiver.recv_timeout(TIMEOUT) {
            Ok(true) => Ok(Outcome::Refuted),
            Ok(false) => Ok(Outcome::Saturated),
            Err(_) => Ok(Outcome::TimedOut),
        }
    }

    /// Runs every `.p` problem directly under `test_artifacts/tptp/<directory>`
    /// with both giving clause strategies, returning the unexpected outcomes
    fn run_artifacts(directory: &str) -> Vec<String> {
        let directory = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../test_artifacts/tptp")
            .join(directory);
        let mut problems: Vec<_> = fs::read_dir(&directory)
            .unwrap()
            .map(|entry| entry.unwrap().path())
            .filter(|path| path.extension().is_some_and(|ext| ext == "p"))
            .collect();
        problems.sort();
        assert!(
            !problems.is_empty(),
            "No artifacts found in {:?}",
            directory
        );

        let strategies: [(&str, GivingClauseSignature); 2] =
            [("FIFO", pick_clause), ("Weighted", pick_clause_weighted)];
        let mut failures = vec![];
        for problem in &problems {
            let name = problem.file_name().unwrap().to_string_lossy();
            let path = problem.to_string_lossy();
            let expected =
                match expected_outcome(&fs::read_to_string(problem).unwrap()) {
                    Ok(expected) => expected,
                    Err(err) => {
                        failures.push(format!("{}: {}", name, err));
                        continue;
                    }
                };

            for (strategy, giving_clause_fn) in strategies {
                match saturate_with_timeout(&path, giving_clause_fn) {
                    Ok(outcome) if outcome == expected => {}
                    Ok(outcome) => failures.push(format!(
                        "{} ({}): expected {:?}, got {:?}",
                        name, strategy, expected, outcome
                    )),
                    Err(err) => failures.push(format!(
                        "{} ({}): cannot be clausified: {}",
                        name, strategy, err
                    )),
                }
            }
        }
        failures
    }

    #[test]
    fn test_saturation_artifacts() {
        let failures = run_artifacts("saturation");
        assert!(
            failures.is_empty(),
            "Saturation artifacts with unexpected outcomes:\n{}",
            failures.join("\n")
        );
    }

    /// Problems SUP can't solve yet, kept as benchmarks for its improvement.
    /// Run with `cargo test -- --ignored`
    #[test]
    #[ignore]
    fn test_open_saturation_artifacts() {
        let failures = run_artifacts("saturation/open");
        assert!(
            failures.is_empty(),
            "Open saturation artifacts still unsolved:\n{}",
            failures.join("\n")
        );
    }
}
