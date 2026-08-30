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
pub fn elaborate_tactic<
    Term,
    Type,
    FT: Fn(Expression) -> Result<Term, LofError>,
    FY: Fn(Expression) -> Result<Type, LofError>,
>(
    tactic: Tactic<Expression, Expression>,
    elaborate_term: FT,
    elaborate_type: FY,
) -> Result<Tactic<Term, Type>, LofError> {
    match tactic {
        Begin() => Ok(Begin()),
        Qed() => Ok(Qed()),
        Intro(assumption_name, formula) => {
            elaborate_intro(assumption_name, formula, elaborate_type)
        }
        Exact(proof_term) => elaborate_exact(proof_term, elaborate_term),
        Apply(lemma) => elaborate_apply(lemma, elaborate_term),
        Induction(var_name) => Ok(Induction(var_name)),
    }
}
//
//
fn elaborate_intro<Term, Type, F: Fn(Expression) -> Result<Type, LofError>>(
    assumption_name: String,
    formula: Expression,
    elaborate_type: F,
) -> Result<Tactic<Term, Type>, LofError> {
    Ok(Intro(assumption_name, elaborate_type(formula)?))
}
//
//
fn elaborate_exact<Term, Type, F: Fn(Expression) -> Result<Term, LofError>>(
    proof_term: Expression,
    elaborate_term: F,
) -> Result<Tactic<Term, Type>, LofError> {
    Ok(Exact(elaborate_term(proof_term)?))
}
//
//
fn elaborate_apply<Term, Type, F: Fn(Expression) -> Result<Term, LofError>>(
    lemma: Expression,
    elaborate_term: F,
) -> Result<Tactic<Term, Type>, LofError> {
    Ok(Apply(elaborate_term(lemma)?))
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
                cic::{
                    CicTerm::{self, Variable},
                    NameKind,
                },
                elaboration::elaborate_expression,
            },
            commons::elaboration::{elaborate_exact, elaborate_intro},
        },
    };

    //TODO: this only checks CIC. is that enough or should i support others?
    #[test]
    fn test_intro_elaboration() {
        assert_eq!(
            elaborate_intro::<CicTerm, _, _>(
                "n".to_string(),
                Expression::VarUse("Nat".to_string()),
                |exp| Ok(elaborate_expression(&exp))
            ),
            Ok(Intro(
                "n".to_string(),
                Variable("Nat".to_string(), NameKind::Const())
            )),
            "Intro elaboration doesnt produce expected tactic"
        );
    }

    #[test]
    fn test_exact_elaboration() {
        assert_eq!(
            elaborate_exact::<_, CicTerm, _>(
                Expression::VarUse("p".to_string()),
                |exp| Ok(elaborate_expression(&exp))
            ),
            Ok(Exact(Variable("p".to_string(), NameKind::Const()))),
            "Exact elaboration doesnt produce expected tactic"
        );
    }
}
//########################### UNIT TESTS
