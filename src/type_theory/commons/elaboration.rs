use crate::{
    parser::api::{
        Expression, LofAst, Statement,
        Tactic::{self, Begin, By, Intro, Qed},
    },
    runtime::program::Schedule,
    type_theory::interface::TypeTheory,
};

//########################### STATEMENTS ELABORATION
pub fn elaborate_ast_vector<T: TypeTheory>(
    root: &String,
    asts: &Vec<LofAst>,
) -> Result<Schedule<T>, String> {
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
        Err(format!(
            "Elaborating the ASTs rooted at '{}' raised errors:\n{}",
            root,
            errors.join("\n")
        ))
    }
}

pub fn elaborate_file_root<T: TypeTheory>(
    file_path: &String,
    asts: &Vec<LofAst>,
) -> Result<Schedule<T>, String> {
    elaborate_ast_vector::<T>(file_path, asts)
}

pub fn elaborate_dir_root<T: TypeTheory>(
    dir_path: &String,
    asts: &Vec<LofAst>,
) -> Result<Schedule<T>, String> {
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
                return Err(format!("AST nodes of directory node can only be FileRoot, not {:?}", sub_ast));
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
) -> Result<Tactic<E>, String> {
    match tactic {
        Begin() => Ok(Begin()),
        Qed() => Ok(Qed()),
        Intro(assumption_name, formula) => elaborate_intro::<E, F>(
            assumption_name,
            formula,
            elaborate_expression,
        ),
        By(proof_term) => elaborate_by(proof_term, elaborate_expression),
        // _ => {
        //     Err("WIP: tactic {:?} is not yet supported. too bad :(".to_string())
        // }
    }
}
//
//
fn elaborate_intro<E, F: Fn(Expression) -> E>(
    assumption_name: String,
    formula: Expression,
    elaborate_expression: F,
) -> Result<Tactic<E>, String> {
    Ok(Intro(assumption_name, elaborate_expression(formula)))
}
//
//
fn elaborate_by<E, F: Fn(Expression) -> E>(
    proof_term: Expression,
    elaborate_expression: F,
) -> Result<Tactic<E>, String> {
    Ok(By(elaborate_expression(proof_term)))
}
//########################### TACTICS ELABORATION

//########################### UNIT TESTS
#[cfg(test)]
mod unit_tests {
    use crate::{
        parser::api::{
            Expression,
            Tactic::{By, Intro},
        },
        type_theory::{
            cic::{
                cic::{CicTerm::Variable, GLOBAL_INDEX},
                elaboration::elaborate_expression,
            },
            commons::elaboration::{elaborate_by, elaborate_intro},
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
    fn test_by_elaboration() {
        assert_eq!(
            elaborate_by(Expression::VarUse("p".to_string()), |exp| {
                elaborate_expression(&exp)
            }),
            Ok(By(Variable("p".to_string(), GLOBAL_INDEX))),
            "By elaboration doesnt produce expected tactic"
        );
    }
}
//########################### UNIT TESTS
