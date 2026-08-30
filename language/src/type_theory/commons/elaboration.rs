use crate::{
    error::LofError,
    parser::api::{
        Expression, LofAst, Statement,
        Tactic::{self, Apply, Begin, Exact, Induction, Intro, Qed},
    },
    runtime::program::Schedule,
    type_theory::interface::TypeTheory,
};

//########################### STATEMENTS ELABORATION
pub fn elaborate_ast_vector<T: TypeTheory>(
    _root: &String,
    asts: &Vec<LofAst>,
) -> Result<Schedule<T>, LofError> {
    let mut errors: Vec<_> = vec![];
    let mut schedule = Schedule::new();

    for sub_ast in asts {
        match sub_ast {
            LofAst::Stm(stm) => match T::elaborate_statement(&stm) {
                Err(message) => errors.push(message),
                Ok(stms) => {
                    schedule.extend(&stms);
                }
            },
            LofAst::Exp(exp) => match T::elaborate_expression(&exp) {
                Err(message) => errors.push(message),
                Ok(exp) => schedule.add_expression(&exp),
            },
        }
    }

    if errors.is_empty() {
        Ok(schedule)
    } else {
        Err(LofError::aggregate(errors))
    }
}

pub fn elaborate_file_root<T: TypeTheory>(
    file_path: &String,
    asts: &Vec<LofAst>,
) -> Result<Schedule<T>, LofError> {
    elaborate_ast_vector::<T>(file_path, asts)
}

pub fn elaborate_dir_root<T: TypeTheory>(
    dir_path: &String,
    asts: &Vec<LofAst>,
) -> Result<Schedule<T>, LofError> {
    let mut schedule = Schedule::new();

    for sub_ast in asts {
        match sub_ast {
            LofAst::Stm(Statement::FileRoot(file_path, file_contet)) => {
                let file_content = elaborate_file_root(
                    &format!("{}/{}", dir_path, file_path),
                    file_contet,
                )?;
                schedule.extend(&file_content);
            }
            _ => {
                return Err(LofError::invalid_ast_node("FileRoot", sub_ast));
            }
        }
    }

    Ok(schedule)
}
//########################### STATEMENTS ELABORATION
//
//
//########################### TACTICS ELABORATION
pub fn elaborate_tactic<E, F: Fn(Expression) -> E>(
    tactic: Tactic<Expression>,
    elaborate_expression: F,
) -> Result<Tactic<E>, LofError> {
    match tactic {
        Begin() => Ok(Begin()),
        Qed() => Ok(Qed()),
        Intro(assumption_name, formula) => elaborate_intro::<E, F>(
            assumption_name,
            formula,
            elaborate_expression,
        ),
        Exact(proof_term) => elaborate_exact(proof_term, elaborate_expression),
        Apply(lemma) => elaborate_apply(lemma, elaborate_expression),
        Induction(var_name) => Ok(Induction(var_name)),
    }
}
//
//
fn elaborate_intro<E, F: Fn(Expression) -> E>(
    assumption_name: String,
    formula: Expression,
    elaborate_expression: F,
) -> Result<Tactic<E>, LofError> {
    Ok(Intro(assumption_name, elaborate_expression(formula)))
}
//
//
fn elaborate_exact<E, F: Fn(Expression) -> E>(
    proof_term: Expression,
    elaborate_expression: F,
) -> Result<Tactic<E>, LofError> {
    Ok(Exact(elaborate_expression(proof_term)))
}
//
//
fn elaborate_apply<E, F: Fn(Expression) -> E>(
    lemma: Expression,
    elaborate_expression: F,
) -> Result<Tactic<E>, LofError> {
    Ok(Apply(elaborate_expression(lemma)))
}
//########################### TACTICS ELABORATION

//########################### UNIT TESTS
#[cfg(test)]
mod unit_tests {
    use crate::{
        parser::api::{
            Expression,
            Tactic::{Exact, Intro},
        },
        type_theory::{
            cic::{
                cic::{CicTerm::Variable, GLOBAL_INDEX},
                elaboration::elaborate_expression,
            },
            commons::elaboration::{elaborate_exact, elaborate_intro},
        },
    };

    //TODO: this only checks CIC. is that enough or should i support others?
    #[test]
    fn test_intro_elaboration() {
        assert_eq!(
            elaborate_intro(
                "n".to_string(),
                Expression::VarUse("Nat".to_string()),
                |exp| elaborate_expression(&exp)
            ),
            Ok(Intro(
                "n".to_string(),
                Variable("Nat".to_string(), GLOBAL_INDEX)
            )),
            "Intro elaboration doesnt produce expected tactic"
        );
    }

    #[test]
    fn test_exact_elaboration() {
        assert_eq!(
            elaborate_exact(Expression::VarUse("p".to_string()), |exp| {
                elaborate_expression(&exp)
            }),
            Ok(Exact(Variable("p".to_string(), GLOBAL_INDEX))),
            "Exact elaboration doesnt produce expected tactic"
        );
    }
}
//########################### UNIT TESTS
