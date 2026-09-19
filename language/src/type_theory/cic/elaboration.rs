use super::cic::CicStm::{Axiom, Theorem};
use super::cic::{
    CicStm::{self},
    CicTerm,
    CicTerm::{
        Abstraction, Application, Let, Match, Meta, Product, Sort, Variable,
    },
};
use crate::error::LofError;
use crate::misc::simple_map;
use crate::misc::Union;
use crate::misc::Union::{L, R};
use crate::parser::api::{Expression, LofAst, Statement, Tactic};
use crate::runtime::program::Schedule;
use crate::type_theory::cic::cic::{Cic, NameKind};
use crate::type_theory::cic::cic_utils::application_args;
// use crate::type_theory::cic::cic_utils::index_variables_in_store;
use crate::type_theory::commons::elaboration::{
    elaborate_ast_vector, elaborate_tactic,
};
use crate::type_theory::commons::utils::ElabStore;

pub fn index_variables_in_store(term: &CicTerm, store: &ElabStore) -> CicTerm {
    /// Returns the list of bounded names introduced by this patter
    fn pattern_binder_names(pattern: &CicTerm) -> Vec<String> {
        match pattern {
            Application(_, _) => application_args(pattern)
                .iter()
                .flat_map(|arg| match arg {
                    Variable(name, _) => vec![name.to_string()],
                    Application(_, _) => pattern_binder_names(arg),
                    _ => vec![],
                })
                .collect(),
            _ => vec![],
        }
    }

    fn solver(term: &CicTerm, store: &ElabStore) -> CicTerm {
        match term {
            Sort(_) => term.to_owned(),
            Meta(_) => term.to_owned(),
            Variable(_, NameKind::Local()) => term.to_owned(),
            Variable(name, _) => match store.lookup_dbi(name) {
                Some(dbi) => Variable(name.to_string(), NameKind::Bound(dbi)),
                // unbound variables in the term get the global variable index
                None => Variable(name.to_string(), NameKind::Const()),
            },
            Abstraction(var_name, var_type, body) => {
                let var_type = solver(var_type, store);

                Abstraction(
                    var_name.to_string(),
                    Box::new(var_type),
                    Box::new(solver(body, &store.push_name(var_name))),
                )
            }
            Product(var_name, var_type, body) => {
                let var_type = solver(var_type, store);

                Product(
                    var_name.to_string(),
                    Box::new(var_type),
                    Box::new(solver(body, &store.push_name(var_name))),
                )
            }
            Let(var_name, var_type, body, scope) => {
                // the definition body lives in the *outer* scope: the `x`
                // on the right of `:=` must resolve against whatever `x`
                // was bound before this `let`, not against the binder this
                // `let` is itself introducing.
                let body = solver(body, store);
                let inner_scope = store.push_name(var_name);

                let var_type = if var_type.is_some() {
                    Some(solver(&(**var_type).as_ref().unwrap(), &inner_scope))
                } else {
                    None
                };

                Let(
                    var_name.to_string(),
                    Box::new(var_type),
                    Box::new(body),
                    Box::new(solver(scope, &inner_scope)),
                )
            }
            Application(left, right) => Application(
                Box::new(solver(left, store)),
                Box::new(solver(right, store)),
            ),
            Match(matched_term, branches) => {
                let matched_term = solver(matched_term, store);
                let branches = branches
                    .iter()
                    .map(|(pattern, body)| {
                        // a pattern's arguments bind over the pattern itself
                        // *and* over its branch body, so both share one
                        // telescope, exactly like an eliminator's minor premise
                        let branch_store = pattern_binder_names(pattern)
                            .iter()
                            .fold(store.to_owned(), |current, name| {
                                current.push_name(name)
                            });

                        (
                            solver(pattern, &branch_store),
                            solver(body, &branch_store),
                        )
                    })
                    .collect();

                Match(Box::new(matched_term), branches)
            }
        }
    }

    solver(term, store)
}

fn map_typed_variables(
    variables: &Vec<(String, Expression)>,
) -> (Vec<(String, CicTerm)>, ElabStore) {
    let mut store = ElabStore::empty();
    let mut elaborated_args = vec![];
    for (arg_name, arg_type_exp) in variables {
        let arg_type = elaborate_expression_rec(arg_type_exp, &store);

        store = store.push_name(arg_name);
        elaborated_args.push((arg_name.to_owned(), arg_type));
    }

    (elaborated_args, store)
}
//
//########################### EXPRESSIONS ELABORATION
pub fn elaborate_expression(ast: &Expression) -> CicTerm {
    elaborate_expression_rec(ast, &mut ElabStore::empty())
}
/// Performs elaboration of the LoF `Expression` to a `CicTerm`.
fn elaborate_expression_rec(ast: &Expression, store: &ElabStore) -> CicTerm {
    let elaborated = match ast {
        Expression::VarUse(var_name) => elaborate_var_use(var_name, store),
        Expression::Abstraction(var_name, var_type, body) => {
            elaborate_abstraction(var_name, &*var_type, &*body, store)
        }
        Expression::TypeProduct(var_name, var_type, body) => {
            elaborate_type_product(var_name, &*var_type, &*body, store)
        }
        Expression::Application(left, args) => {
            elaborate_application(left, args, store)
        }
        Expression::Let(var_name, var_type, definition_body, scope) => {
            elaborate_let(var_name, var_type, definition_body, scope, store)
        }
        Expression::Match(matched_term, branches) => {
            elaborate_match(&*matched_term, branches, store)
        }
        Expression::Arrow(domain, codomain) => {
            elaborate_arrow(domain, codomain, store)
        }
        Expression::Inferator() => elaborate_meta(),
        _ => panic!("Expression primitive {:?} is not supported in CIC", ast),
    };

    // index_variables(&elaborated)
    elaborated
}
//
//
#[allow(non_upper_case_globals)]
static mut next_index: i32 = 0;
fn elaborate_meta() -> CicTerm {
    //TODO well... this causes issues with tests
    //'twas unsafe indeed...
    //unsafe my ass stupid crab
    unsafe {
        let index = next_index;
        next_index += 1;
        return Meta(index);
    }
}
//
fn is_sort(var_name: &str) -> bool {
    //TODO this should probably be at the parser level
    var_name.len() > 1 && var_name.chars().all(|c| c.is_ascii_uppercase())
}
//
fn elaborate_var_use(var_name: &str, store: &ElabStore) -> CicTerm {
    if is_sort(var_name) {
        Sort(var_name.to_string())
    } else {
        if let Some(index) = store.lookup_dbi(var_name) {
            Variable(var_name.to_string(), NameKind::Bound(index))
        } else {
            Variable(var_name.to_string(), NameKind::Const())
        }
    }
}
//
//
fn elaborate_abstraction(
    var_name: &str,
    var_type: &Expression,
    body: &Expression,
    store: &ElabStore,
) -> CicTerm {
    let var_type_term = elaborate_expression_rec(var_type, &store);
    let body_term = elaborate_expression_rec(body, &store.push_name(var_name));

    Abstraction(
        var_name.to_string(),
        Box::new(var_type_term),
        Box::new(body_term),
    )
}
//
//
fn elaborate_type_product(
    var_name: &str,
    var_type: &Expression,
    body: &Expression,
    store: &ElabStore,
) -> CicTerm {
    let type_term = elaborate_expression_rec(var_type, &store);
    let body_term = elaborate_expression_rec(body, &store.push_name(var_name));

    Product(
        var_name.to_string(),
        Box::new(type_term),
        Box::new(body_term),
    )
}
//
//
fn elaborate_application(
    function: &Expression,
    args: &Vec<Expression>,
    store: &ElabStore,
) -> CicTerm {
    let fun_term = elaborate_expression_rec(function, store);
    let arg_terms = simple_map(args.to_owned(), |arg| {
        elaborate_expression_rec(&arg, store)
    });

    arg_terms.into_iter().fold(fun_term, |acc, arg| {
        Application(Box::new(acc), Box::new(arg))
    })
}
//
//
fn elaborate_arrow(
    domain: &Expression,
    codomain: &Expression,
    store: &ElabStore,
) -> CicTerm {
    // fully treated as a forall with an anonymous variable
    // this means A->B is still treated as a binder for _
    elaborate_type_product("_", domain, codomain, store)
}
//
//
fn elaborate_let(
    var_name: &str,
    var_type: &Option<Expression>,
    body: &Expression,
    scope: &Expression,
    store: &ElabStore,
) -> CicTerm {
    let var_type = if var_type.is_some() {
        Some(elaborate_expression(&var_type.as_ref().unwrap()))
    } else {
        None
    };

    Let(
        var_name.to_string(),
        Box::new(var_type),
        Box::new(elaborate_expression_rec(body, store)),
        Box::new(elaborate_expression_rec(scope, &store.push_name(var_name))),
    )
}
//
//

fn elaborate_match(
    matched_exp: &Expression,
    branches: &Vec<(Expression, Expression)>,
    store: &ElabStore,
) -> CicTerm {
    let matched_term = elaborate_expression_rec(matched_exp, store);
    let mut branch_terms = vec![];
    for (pattern, body_exp) in branches {
        branch_terms.push((
            elaborate_expression_rec(pattern, store),
            elaborate_expression_rec(body_exp, store),
        ));
    }

    // cant be bother to implement this here, just call index_variables
    index_variables_in_store(
        &Match(Box::new(matched_term), branch_terms),
        store,
    )
}
//
//########################### EXPRESSIONS ELABORATION
//
//########################### STATEMENTS ELABORATION
pub fn elaborate_statement(ast: &Statement) -> Result<Schedule<Cic>, LofError> {
    match ast {
        Statement::Comment() => Ok(Schedule::new()),
        Statement::FileRoot(file_path, asts) => {
            elaborate_file_root(file_path, asts)
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
        Statement::Inductive(type_name, parameters, ariety, constructors) => {
            Ok(Schedule::singleton_stm(elaborate_inductive(
                type_name,
                parameters,
                ariety,
                constructors,
            )?))
        }
        Statement::Fun(fun_name, args, out_type, body, is_rec) => {
            Ok(Schedule::singleton_stm(elaborate_fun(
                fun_name, args, out_type, body, is_rec,
            )?))
        }
        Statement::EmptyRoot(nodes) => Ok(elaborate_empty(nodes)?),
        Statement::Theorem(theorem_name, formula, proof) => {
            Ok(Schedule::singleton_stm(elaborate_theorem(
                theorem_name,
                formula,
                proof,
            )?))
        }
        // Statement::Auto(formula) => {
        //     Ok(Schedule::singleton_stm(elaborate_auto(formula)?))
        // } //
        _ => Err(LofError::unsupported_construct("CIC", ast)),
    }
}
//
//
fn elaborate_file_root(
    file_path: &String,
    asts: &Vec<LofAst>,
) -> Result<Schedule<Cic>, LofError> {
    elaborate_ast_vector::<Cic>(file_path, asts)
}
//
//
fn elaborate_dir_root(
    dir_path: &String,
    asts: &Vec<LofAst>,
) -> Result<Schedule<Cic>, LofError> {
    let mut schedule = Schedule::new();
    for sub_ast in asts {
        match sub_ast {
            LofAst::Stm(Statement::FileRoot(file_path, file_contet)) => {
                let content = elaborate_file_root(
                    &format!("{}/{}", dir_path, file_path),
                    file_contet,
                )?;
                schedule.extend(&content);
            }
            _ => {
                return Err(LofError::invalid_ast_node("FileRoot", sub_ast));
            }
        }
    }

    Ok(schedule)
}
//
//
fn elaborate_global(
    var_name: &String,
    var_type: &Option<Expression>,
    body: &Expression,
) -> Result<CicStm, LofError> {
    //TODO im pretty sure this should increase the dbi in its scope
    //but i have no reference to the scope here
    let opt_type = match var_type {
        Some(type_exp) => Some(elaborate_expression(&type_exp)),
        None => None,
    };
    let elaborated_body = elaborate_expression(&body);

    Ok(CicStm::Global(
        var_name.to_string(),
        opt_type,
        Box::new(elaborated_body),
    ))
}
//
//
fn elaborate_fun(
    fun_name: &String,
    args: &Vec<(String, Expression)>,
    out_type: &Expression,
    body: &Expression,
    is_rec: &bool,
) -> Result<CicStm, LofError> {
    // compute dbis for the arguments introduced and use them in the body
    let (elaborated_args, store) = map_typed_variables(args);
    let elaborated_out_type = elaborate_expression_rec(&out_type, &store);
    let elaborated_body = elaborate_expression_rec(&body, &store);

    Ok(CicStm::Fun(
        fun_name.to_string(),
        elaborated_args,
        Box::new(elaborated_out_type),
        Box::new(elaborated_body),
        *is_rec,
    ))
}
//
//
fn elaborate_inductive(
    type_name: &String,
    parameters: &Vec<(String, Expression)>,
    ariety: &Expression,
    constructors: &Vec<(String, Expression)>,
) -> Result<CicStm, LofError> {
    // compute dbis for the left params and use them for arity and constructor types
    let (parameter_terms, store) = map_typed_variables(&parameters);
    let ariety_term = elaborate_expression_rec(&ariety, &store);
    let constructor_terms: Vec<(String, CicTerm)> = constructors
        .iter()
        .map(|(constr_name, constr_type)| {
            (
                constr_name.to_owned(),
                elaborate_expression_rec(constr_type, &store),
            )
        })
        .collect();

    Ok(CicStm::InductiveDef(
        type_name.to_string(),
        parameter_terms,
        Box::new(ariety_term),
        constructor_terms,
    ))
}
//
//
fn elaborate_axiom(
    axiom_name: &String,
    formula: &Expression,
) -> Result<CicStm, LofError> {
    let elaborated_formula = elaborate_expression(&formula);
    Ok(Axiom(axiom_name.to_string(), Box::new(elaborated_formula)))
}
//
//
fn elaborate_theorem(
    theorem_name: &String,
    formula: &Expression,
    proof: &Union<Expression, Vec<Tactic<Expression>>>,
) -> Result<CicStm, LofError> {
    let elaborated_formula = elaborate_expression(&formula);
    let elaborated_proof = match proof {
        L(proof_term) => {
            let cic_proof_term = elaborate_expression(&proof_term);
            L(cic_proof_term)
        }
        R(interactive_proof) => {
            let cic_interactive_proof: Vec<Tactic<CicTerm>> =
                simple_map(interactive_proof.to_owned(), |tactic| {
                    elaborate_tactic::<CicTerm, _>(tactic, |exp| {
                        elaborate_expression(&exp)
                    })
                    //TODO this is a temporary solution, doesnt handle errors gracefully
                    .unwrap()
                });
            R(cic_interactive_proof)
        }
    };

    Ok(Theorem(
        theorem_name.to_string(),
        Box::new(elaborated_formula),
        elaborated_proof,
    ))
}
//
//
fn elaborate_empty(nodes: &Vec<LofAst>) -> Result<Schedule<Cic>, LofError> {
    elaborate_ast_vector::<Cic>(&"".to_string(), nodes)
}
//
//########################### STATEMENTS ELABORATION

//########################### UNIT TESTS

#[path = "../../tests/type_theory/cic/elaboration.rs"]
mod tests;
