/// End to end tests over the TPTP problems of `test_artifacts/tptp`: each
/// problem is parsed in the logic its header declares and solved, checking
/// the outcome against the header's `% Status`
#[cfg(test)]
mod end_to_end {
    use crate::{
        error::LofError,
        tptp::{
            header::Status,
            problem::{load_tptp_file, TptpBody, TptpProblem},
            syntax::Role,
        },
        type_theory::{
            algorithms::dpll::{dpll, dpll_prove},
            grammars::prop::PropFormula::{self, Atom, Conjunction},
        },
    };
    use std::{fs, path::Path};

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
        let inputs = match &problem.body {
            TptpBody::Propositional(inputs) => inputs,
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

    #[test]
    fn test_propositional_artifacts() {
        let mut failures = vec![];
        for path in artifacts("prp") {
            let outcome = load_tptp_file(&path).and_then(|problem| {
                let status = decide_propositional(&problem)?;
                Ok((problem.header.status, status))
            });
            match outcome {
                Ok((expected, found)) if expected == found => {}
                Ok((expected, found)) => failures.push(format!(
                    "{}: header says {:?}, DPLL found {:?}",
                    path, expected, found
                )),
                Err(err) => failures.push(format!("{}: {}", path, err)),
            }
        }

        assert!(
            failures.is_empty(),
            "Propositional artifacts with unexpected outcomes:\n{}",
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
        let inputs = match problem.body {
            TptpBody::Propositional(inputs) => inputs,
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
