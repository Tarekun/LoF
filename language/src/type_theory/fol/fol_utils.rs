use super::fol::Fol;
use crate::{
    error::LofError,
    type_theory::{
        commons::utils::generic_multiarg_fun_type,
        grammars::{
            cnf::{
                CnfFormula::{self, Clause},
                CnfTerm,
            },
            fol::{
                FolFormula::{self, Arrow, Disjunction, Not, Predicate},
                FolTerm::{self, Application, Variable},
            },
        },
    },
};
use std::collections::HashSet;

pub fn make_multiarg_fun_type(
    arg_types: &[(String, FolFormula)],
    base: &FolFormula,
) -> FolFormula {
    generic_multiarg_fun_type::<Fol, _>(
        arg_types,
        base,
        |_, arg_type, sub_type| Arrow(Box::new(arg_type), Box::new(sub_type)),
    )
}

pub fn term_to_cnf(
    term: &FolTerm,
    constants: &HashSet<String>,
) -> Result<CnfTerm, LofError> {
    match &term {
        Variable(name) => {
            if constants.contains(name) {
                Ok(CnfTerm::Application(name.to_string(), vec![]))
            } else {
                Ok(CnfTerm::Variable(name.to_string()))
            }
        }
        Application(_, _) => {
            let (fun_name, args) = term.get_application_components()?;
            let mut sup_args = vec![];
            for arg in args {
                sup_args.push(term_to_cnf(&arg, constants)?);
            }
            Ok(CnfTerm::Application(fun_name, sup_args))
        }
        _ => Err(LofError::custom(format!(
            "FOL term {:?} doesn't have a corresponding SUP term",
            term
        ))),
    }
}

#[allow(non_snake_case)]
pub fn clausify(
    φ: &FolFormula,
    constants: &HashSet<String>,
) -> Result<Vec<CnfFormula>, LofError> {
    fn clauses_to_sup(
        clauses: Vec<FolFormula>,
        constants: &HashSet<String>,
    ) -> Result<Vec<CnfFormula>, LofError> {
        // collect errors across all clauses
        let mut errors = vec![];
        let mut sup_clauses = vec![];

        for clause in clauses {
            match clause_to_cnf(clause, constants) {
                Ok(clause) => sup_clauses.push(clause),
                Err(err) => errors.push(err),
            }
        }

        if errors.is_empty() {
            Ok(sup_clauses)
        } else {
            Err(LofError::aggregate(errors))
        }
    }

    fn clause_to_cnf(
        C: FolFormula,
        constants: &HashSet<String>,
    ) -> Result<CnfFormula, LofError> {
        let C = match C {
            Predicate(name, args) => {
                let mut sup_args = vec![];
                for arg in args {
                    sup_args.push(term_to_cnf(&arg, constants)?);
                }
                CnfFormula::Atom(name, sup_args)
            }
            Disjunction(lits) => Clause(clauses_to_sup(lits, constants)?),
            Not(D) => CnfFormula::Not(Box::new(clause_to_cnf(*D, constants)?)),
            _ => {
                return Err(LofError::custom(format!("Not a Clause: {:?}", C)));
            }
        };

        Ok(C)
    }

    let cnf = φ
        .negation_normal_form()
        .prenex_normal_form()
        .skolemize()
        .conjunction_normal_form();
    clauses_to_sup(cnf, constants)
}
