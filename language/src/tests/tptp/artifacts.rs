/// End to end tests over the TPTP problems of `test_artifacts/tptp`: each
/// problem is parsed in the logic its header declares and solved, checking
/// the outcome against the header's `% Status`
#[cfg(test)]
mod end_to_end {
    use crate::{
        config::SelectionFunction,
        error::LofError,
        tptp::{
            header::Status,
            problem::{load_tptp_file, TptpBody, TptpProblem},
            syntax::Role,
        },
        type_theory::{
            algorithms::{
                dpll::{dpll, dpll_prove},
                saturation::saturate,
            },
            grammars::{
                cnf::CnfFormula,
                prop::PropFormula::{self, Atom, Conjunction},
            },
            sup::freedom::{get_selection_fn, pick_clause},
        },
    };
    use std::{fs, path::Path};

    /// Given clauses after which saturation gives up on a clausal problem
    const MAX_STEPS: usize = 500;

    /// Returns the paths of every `.p` problem directly under
    /// `test_artifacts/tptp/<directory>`
    fn artifacts(directory: &str) -> Vec<String> {
        let directory = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../test_artifacts/tptp")
            .join(directory);
        let mut problems: Vec<_> = fs::read_dir(&directory)
            .unwrap()
            .map(|entry| entry.unwrap().path())
            .filter(|path| path.extension().is_some_and(|ext| ext == "p"))
            .map(|path| path.to_string_lossy().to_string())
            .collect();
        problems.sort();
        assert!(
            !problems.is_empty(),
            "No artifacts found in {:?}",
            directory
        );
        problems
    }

    /// Computes the status of a propositional problem with DPLL. The
    /// conjectures are proved jointly, as TPTP requires
    fn decide_propositional(problem: &TptpProblem) -> Result<Status, LofError> {
        let TptpBody::Propositional(inputs) = &problem.body else {
            return Err(LofError::custom("Not a propositional problem"));
        };
        let (conjectures, premises): (Vec<_>, Vec<_>) = inputs
            .iter()
            .partition(|input| input.role == Role::Conjecture);
        let premises: Vec<PropFormula> = premises
            .into_iter()
            .map(|input| input.formula.clone())
            .collect();
        let mut conjectures: Vec<PropFormula> = conjectures
            .into_iter()
            .map(|input| input.formula.clone())
            .collect();

        if dpll(&premises)?.is_none() {
            return Ok(if conjectures.is_empty() {
                Status::Unsatisfiable
            } else {
                Status::ContradictoryAxioms
            });
        }
        if conjectures.is_empty() {
            return Ok(Status::Satisfiable);
        }

        let goal = if conjectures.len() == 1 {
            conjectures.pop().unwrap()
        } else {
            Conjunction(conjectures)
        };
        Ok(match dpll_prove(&premises, &[goal])? {
            None => Status::Theorem,
            Some(_) => Status::CounterSatisfiable,
        })
    }

    /// Computes the status of a clausal problem with SUP saturation
    fn decide_clausal(problem: &TptpProblem) -> Result<Status, LofError> {
        let TptpBody::Clausal(inputs) = &problem.body else {
            return Err(LofError::custom("Not a clausal problem"));
        };
        let clauses: Vec<CnfFormula> =
            inputs.iter().map(|input| input.formula.clone()).collect();
        let selection_fn = get_selection_fn(SelectionFunction::Maximal);
        // match saturate_bounded(&clauses, &selection_fn, pick_clause, MAX_STEPS)?
        match saturate(&clauses, &selection_fn, pick_clause) {
            Ok(_) => Ok(Status::Unsatisfiable),
            Err(_) => Ok(Status::Satisfiable),
            // StepLimit => Err(LofError::custom(format!(
            //     "SUP found no outcome within {} steps",
            //     MAX_STEPS
            // ))),
        }
    }

    /// Solves every problem at `paths` with `decide`, describing each one
    /// whose outcome disagrees with its header's status
    fn failures(
        paths: Vec<String>,
        decide: fn(&TptpProblem) -> Result<Status, LofError>,
    ) -> Vec<String> {
        let mut failures = vec![];
        for path in paths {
            let outcome = load_tptp_file(&path).and_then(|problem| {
                Ok((problem.header.status, decide(&problem)?))
            });
            match outcome {
                Ok((expected, found)) if expected == found => {}
                Ok((expected, found)) => failures.push(format!(
                    "{}: header says {:?}, found {:?}",
                    path, expected, found
                )),
                Err(err) => failures.push(format!("{}: {}", path, err)),
            }
        }
        failures
    }

    #[test]
    fn test_propositional_artifacts() {
        let failures = failures(artifacts("prp"), decide_propositional);
        assert!(
            failures.is_empty(),
            "Propositional artifacts with unexpected outcomes:\n{}",
            failures.join("\n")
        );
    }

    #[test]
    /// Traces every given clause, shown when the test fails
    fn test_clausal_artifacts() {
        let _ = tracing_subscriber::fmt()
            .with_max_level(tracing::Level::TRACE)
            .with_ansi(false)
            .with_test_writer()
            .try_init();
        let failures = failures(artifacts("cnf"), decide_clausal);
        assert!(
            failures.is_empty(),
            "Clausal artifacts with unexpected outcomes:\n{}",
            failures.join("\n")
        );
    }

    #[test]
    fn test_propositional_artifact_parsing() {
        let path = format!(
            "{}/../test_artifacts/tptp/prp/modus_ponens.p",
            env!("CARGO_MANIFEST_DIR")
        );
        let problem = load_tptp_file(&path).unwrap();

        assert_eq!(problem.header.field("Problem"), Some("Modus ponens"));
        let TptpBody::Propositional(inputs) = problem.body else {
            panic!("modus_ponens.p isnt parsed as a propositional problem")
        };
        let summary: Vec<_> = inputs
            .into_iter()
            .map(|input| (input.name, input.role, input.formula))
            .collect();
        let atom = |name: &str| Atom(name.to_string());
        assert_eq!(
            summary,
            vec![
                ("p".to_string(), Role::Axiom, atom("p")),
                (
                    "p_implies_q".to_string(),
                    Role::Axiom,
                    PropFormula::Arrow(
                        Box::new(atom("p")),
                        Box::new(atom("q"))
                    )
                ),
                ("q".to_string(), Role::Conjecture, atom("q")),
            ],
            "modus_ponens.p isnt parsed to the expected propositional formulas"
        );
    }
}
#[cfg(test)]
mod clausal {
    use crate::{
        tptp::{
            problem::{load_tptp_file, TptpBody},
            syntax::Role,
        },
        type_theory::grammars::cnf::{
            CnfFormula::{self, Atom, Clause, Equality, Not},
            CnfTerm::{self, Application, Variable},
        },
    };

    /// Loads the CNF test artifact `file_name` as (name, role, clause) triples
    fn load_cnf(file_name: &str) -> Vec<(String, Role, CnfFormula)> {
        let path = format!(
            "{}/../test_artifacts/tptp/cnf/{}",
            env!("CARGO_MANIFEST_DIR"),
            file_name
        );
        let problem = load_tptp_file(&path)
            .unwrap_or_else(|err| panic!("Cannot load {}: {}", file_name, err));
        let TptpBody::Clausal(inputs) = problem.body else {
            panic!("{} isnt parsed as a clausal problem", file_name)
        };
        inputs
            .into_iter()
            .map(|input| (input.name, input.role, input.formula))
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
                    pred("abc", vec![constant("Mixed Case"), var("X")])
                ),
                input(
                    "7",
                    Role::Plain,
                    Clause(vec![
                        pred("p", vec![var("X")]),
                        pred("q", vec![var("X")]),
                    ])
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
}
