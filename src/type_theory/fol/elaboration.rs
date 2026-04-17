use super::fol::FolFormula::{Arrow, Disjunction, ForAll, Predicate};
use super::fol::FolStm::{Auto, Axiom, Fun, Global, Theorem};
use super::fol::FolTerm::{Abstraction, Application, Let, Tuple, Variable};
use super::fol::{Fol, FolFormula, FolTerm};
use crate::misc::simple_map;
use crate::parser::api::{Statement, Tactic};
use crate::runtime::program::Schedule;
use crate::type_theory::commons::elaboration::{
    elaborate_ast_vector, elaborate_dir_root, elaborate_file_root,
    elaborate_tactic,
};
use crate::type_theory::commons::utils::{wrap_term, wrap_type};
use crate::type_theory::fol::fol::FolStm;
use crate::{
    misc::Union,
    misc::Union::{L, R},
    parser::api::{Expression, LofAst},
};
use regex::Regex;

fn map_typed_variables(
    variables: &Vec<(String, Expression)>,
) -> Vec<(String, FolFormula)> {
    variables
        .iter()
        .map(|(var_name, var_type_exp)| {
            match elaborate_expression(var_type_exp) {
                Ok(Union::L(term)) => panic!(
                    "TODO handle this but term is no supposed to show up {:?}",
                    term
                ),
                Ok(Union::R(var_type)) => (var_name.to_owned(), var_type),
                _ => panic!("TODO: handle"),
            }
        })
        .collect()
}

fn type_expected_error<Expected>(
    task: &str,
    term: &FolTerm,
) -> Result<Expected, String> {
    Err(format!(
        "[FOL elaboration]: in {} a type was expected, but term {:?} was received",
        task,
        term
    ))
}
fn term_expected_error<Expected>(
    task: &str,
    type_exp: &FolFormula,
) -> Result<Expected, String> {
    Err(format!(
        "[FOL elaboration]: in {} a term was expected, but type {:?} was received",
        task,
        type_exp
    ))
}

fn expect_term(arg: Union<FolTerm, FolFormula>) -> Result<FolTerm, String> {
    match arg {
        L(fol_term) => Ok(fol_term),
        R(fol_type) => {
            Err(format!("Expected term, found {:?} instead", fol_type))
        }
    }
}
fn expect_type(arg: Union<FolTerm, FolFormula>) -> Result<FolFormula, String> {
    match arg {
        L(fol_term) => {
            Err(format!("Expected type, found {:?} instead", fol_term))
        }
        R(fol_type) => Ok(fol_type),
    }
}

//########################### EXPRESSIONS ELABORATION
pub fn elaborate_expression(
    ast: &Expression,
) -> Result<Union<FolTerm, FolFormula>, String> {
    match ast {
        Expression::VarUse(var_name) => elaborate_var_use(var_name.clone()),
        Expression::Abstraction(var_name, var_type, body) => {
            wrap_term::<Fol>(elaborate_abstraction(var_name, var_type, body))
        }
        Expression::Application(left, right) => {
            elaborate_application(left, right)
        }
        Expression::Arrow(domain, codomain) => {
            wrap_type::<Fol>(elaborate_arrow(domain, codomain))
        }
        Expression::TypeProduct(var_name, var_type, body) => {
            wrap_type::<Fol>(elaborate_forall(var_name, var_type, body))
        }
        Expression::Let(var_name, var_type, definition_body, scope) => {
            wrap_term::<Fol>(elaborate_let(
                var_name,
                var_type,
                definition_body,
                scope,
            ))
        }
        Expression::Tuple(terms) => wrap_term::<Fol>(elaborate_tuple(terms)),
        Expression::Pipe(types) => wrap_type::<Fol>(elaborate_pipe(types)),
        _ => panic!("Expression {:?} is not supported in FOL", ast),
    }
}
//
//
pub fn elaborate_var_use(
    var_name: String,
) -> Result<Union<FolTerm, FolFormula>, String> {
    let pascal_case = Regex::new(r"^[A-Z][a-zA-Z]*$").unwrap();

    //TODO better evaluate how to distinguish them
    //for now the logic is if it's spelled in PascalCase, its a type (formula)
    if pascal_case.is_match(&var_name) {
        Ok(Union::R(Predicate(var_name, vec![])))
    } else {
        Ok(Union::L(Variable(var_name)))
    }
}
//
//
pub fn elaborate_abstraction(
    var_name: &String,
    var_type: &Expression,
    body: &Expression,
) -> Result<FolTerm, String> {
    let var_type = elaborate_expression(var_type)?;
    match var_type {
        Union::R(var_type) => {
            let body = elaborate_expression(body)?;
            match body {
                Union::L(body_term) => Ok(Abstraction(
                    var_name.to_string(),
                    Box::new(var_type),
                    Box::new(body_term),
                )),
                Union::R(wrong_type) => {
                    term_expected_error("abstraction", &wrong_type)
                }
            }
        }
        Union::L(term) => type_expected_error("abstraction", &term),
    }
}
//
//
pub fn elaborate_arrow(
    domain: &Expression,
    codomain: &Expression,
) -> Result<FolFormula, String> {
    let domain = elaborate_expression(domain)?;
    match domain {
        Union::R(domain_type) => {
            let codomain = elaborate_expression(codomain)?;
            match codomain {
                Union::R(codomain_type) => {
                    Ok(Arrow(Box::new(domain_type), Box::new(codomain_type)))
                }
                Union::L(term) => type_expected_error("arrow", &term),
            }
        }
        Union::L(term) => type_expected_error("arrow", &term),
    }
}
//
//
pub fn elaborate_application(
    function: &Expression,
    args: &Vec<Expression>,
) -> Result<Union<FolTerm, FolFormula>, String> {
    let fun_term: FolTerm = expect_term(elaborate_expression(function)?)?;
    let arg_terms =
        simple_map(args.to_owned(), |arg| elaborate_expression(&arg));
    let mut unwrapped: Vec<FolTerm> = vec![];
    for term in arg_terms {
        unwrapped.push(expect_term(term?)?);
    }

    if let Variable(applied_name) = &fun_term {
        let pascal_case = Regex::new(r"^[A-Z][a-zA-Z]*$").unwrap();
        if pascal_case.is_match(&applied_name) {
            return wrap_type::<Fol>(Ok(Predicate(
                applied_name.to_string(),
                unwrapped,
            )));
        }
    }

    wrap_term::<Fol>(Ok(unwrapped.into_iter().fold(fun_term, |acc, arg| {
        Application(Box::new(acc), Box::new(arg))
    })))
}
//
//
pub fn elaborate_forall(
    var_name: &String,
    var_type: &Expression,
    body: &Expression,
) -> Result<FolFormula, String> {
    let var_type = elaborate_expression(var_type)?;
    match var_type {
        Union::R(var_type) => {
            let body = elaborate_expression(body)?;
            match body {
                Union::R(body_formula) => Ok(ForAll(
                    var_name.to_string(),
                    Box::new(var_type),
                    Box::new(body_formula),
                )),
                Union::L(term) => type_expected_error("forall", &term),
            }
        }
        Union::L(term) => type_expected_error("forall", &term),
    }
}
//
//
fn elaborate_let(
    var_name: &str,
    var_type: &Option<Expression>,
    body: &Expression,
    scope: &Expression,
) -> Result<FolTerm, String> {
    let var_type = if var_type.is_some() {
        Some(expect_type(elaborate_expression(
            &var_type.as_ref().unwrap(),
        )?)?)
    } else {
        None
    };
    let body = expect_term(elaborate_expression(body)?)?;
    let scope = expect_term(elaborate_expression(scope)?)?;

    Ok(Let(
        var_name.to_string(),
        Box::new(var_type),
        Box::new(body),
        Box::new(scope),
    ))
}
//
//
pub fn elaborate_tuple(terms: &Vec<Expression>) -> Result<FolTerm, String> {
    let mut elaborated_terms = vec![];
    for term in terms {
        elaborated_terms.push(expect_term(elaborate_expression(term)?)?);
    }

    Ok(Tuple(elaborated_terms))
}
//
//
pub fn elaborate_pipe(types: &Vec<Expression>) -> Result<FolFormula, String> {
    let mut elaborated_types = vec![];
    for term in types {
        elaborated_types.push(expect_type(elaborate_expression(term)?)?);
    }

    Ok(Disjunction(elaborated_types))
}
//########################### EXPRESSIONS ELABORATION
//
//########################### STATEMENTS ELABORATION
pub fn elaborate_statement(ast: &Statement) -> Result<Schedule<Fol>, String> {
    match ast {
        Statement::Comment() => Ok(Schedule::new()),
        Statement::FileRoot(file_path, asts) => {
            elaborate_file_root::<Fol>(file_path, asts)
        }
        Statement::DirRoot(dirpath, asts) => elaborate_dir_root(dirpath, asts),
        Statement::Axiom(axiom_name, formula) => Ok(Schedule::singleton_stm(
            elaborate_axiom(axiom_name, formula)?,
        )),
        Statement::Global(var_name, var_type, body) => {
            Ok(Schedule::singleton_stm(elaborate_global(
                var_name, var_type, body,
            )?))
        }
        Statement::Fun(fun_name, args, out_type, body, is_rec) => {
            Ok(Schedule::singleton_stm(elaborate_fun(
                fun_name, args, out_type, body, is_rec,
            )?))
        }
        Statement::EmptyRoot(nodes) => elaborate_empty(nodes),
        Statement::Theorem(theorem_name, formula, proof) => {
            Ok(Schedule::singleton_stm(elaborate_theorem(
                theorem_name,
                formula,
                proof,
            )?))
        }
        Statement::Auto(formula) => {
            Ok(Schedule::singleton_stm(elaborate_auto(formula)?))
        }
        _ => Err(format!("Language construct {:?} not supported in FOL", ast)),
    }
}
//
//
pub fn elaborate_axiom(
    axiom_name: &String,
    formula: &Expression,
) -> Result<FolStm, String> {
    let formula = elaborate_expression(formula)?;
    match formula {
        Union::R(formula) => Ok(Axiom(axiom_name.to_string(), formula)),
        Union::L(term) => {
            type_expected_error(&format!("axiom {}", axiom_name), &term)
        }
    }
}
//
//
pub fn elaborate_theorem(
    theorem_name: &String,
    formula: &Expression,
    proof: &Union<Expression, Vec<Tactic<Expression>>>,
) -> Result<FolStm, String> {
    let fol_formula_union = elaborate_expression(formula)?;
    let fol_formula = expect_type(fol_formula_union)?;
    let proof: Union<FolTerm, Vec<Tactic<Union<FolTerm, FolFormula>>>> =
        match proof {
            L(proof_term) => {
                let fol_proof_term = elaborate_expression(proof_term)?;
                let fol_proof_term = expect_term(fol_proof_term)?;
                L(fol_proof_term)
            }
            R(interactive_proof) => {
                let fol_interactive_proof: Vec<
                    Tactic<Union<FolTerm, FolFormula>>,
                > = simple_map(interactive_proof.to_vec(), |tactic| {
                    elaborate_tactic::<Union<FolTerm, FolFormula>, _>(
                        tactic,
                        |exp| elaborate_expression(&exp).unwrap(),
                    )
                    //TODO this is a temporary solution, doesnt handle errors gracefully
                    .unwrap()
                });
                R(fol_interactive_proof)
            }
        };

    Ok(Theorem(
        theorem_name.to_string(),
        Box::new(fol_formula),
        proof,
    ))
}
//
//
pub fn elaborate_global(
    var_name: &String,
    opt_type: &Option<Expression>,
    body: &Expression,
) -> Result<FolStm, String> {
    let body = elaborate_expression(body)?;
    match body {
        Union::L(body_term) => {
            let var_type = match opt_type {
                Some(type_exp) => Some(elaborate_expression(type_exp)?),
                None => None,
            };
            match var_type {
                Some(Union::R(var_type)) => Ok(Global(
                    var_name.to_string(),
                    Some(var_type),
                    Box::new(body_term),
                )),
                None => {
                    Ok(Global(var_name.to_string(), None, Box::new(body_term)))
                }

                Some(Union::L(wrong_term)) => type_expected_error(
                    &format!("let definition of {}", var_name),
                    &wrong_term,
                ),
            }
        }
        Union::R(wrong_type) => term_expected_error(
            &format!("let definition of {}", var_name),
            &wrong_type,
        ),
    }
}
//
//
pub fn elaborate_fun(
    fun_name: &String,
    args: &Vec<(String, Expression)>,
    out_type: &Expression,
    body: &Expression,
    is_rec: &bool,
) -> Result<FolStm, String> {
    let out_type = elaborate_expression(out_type)?;
    match out_type {
        Union::R(out_type) => {
            let body = elaborate_expression(body)?;
            match body {
                Union::L(body) => Ok(Fun(
                    fun_name.to_string(),
                    map_typed_variables(args),
                    Box::new(out_type),
                    Box::new(body),
                    *is_rec,
                )),
                Union::R(type_exp) => term_expected_error(
                    &format!("fun definition of {}", fun_name),
                    &type_exp,
                ),
            }
        }
        Union::L(term) => type_expected_error(
            &format!("fun definition of {}", fun_name),
            &term,
        ),
    }
}
//
//
pub fn elaborate_empty(nodes: &Vec<LofAst>) -> Result<Schedule<Fol>, String> {
    elaborate_ast_vector::<Fol>(&"".to_string(), nodes)
}
//
//
fn elaborate_auto(formula: &Expression) -> Result<FolStm, String> {
    let formula = elaborate_expression(formula)?;

    Ok(Auto(expect_type(formula)?))
}
//
//########################### STATEMENTS ELABORATION

//########################### UNIT TESTS
