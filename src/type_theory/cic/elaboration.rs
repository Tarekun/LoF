use super::cic::CicStm::{Auto, Axiom, Theorem};
use super::cic::PLACEHOLDER_DBI;
use super::cic::{
    CicStm::{self},
    CicTerm,
    CicTerm::{
        Abstraction, Application, Let, Match, Meta, Product, Sort, Variable,
    },
};
use super::cic_utils::index_variables;
use crate::misc::simple_map;
use crate::misc::Union;
use crate::misc::Union::{L, R};
use crate::parser::api::{Expression, LofAst, Statement, Tactic};
use crate::runtime::program::Schedule;
use crate::type_theory::cic::cic::Cic;
use crate::type_theory::commons::elaboration::{
    elaborate_ast_vector, elaborate_tactic,
};

fn map_typed_variables(
    variables: &Vec<(String, Expression)>,
) -> Vec<(String, CicTerm)> {
    variables
        .iter()
        .map(|(var_name, var_type_exp)| {
            (var_name.to_owned(), elaborate_expression(var_type_exp))
        })
        .collect()
}
//
//########################### EXPRESSIONS ELABORATION
/// Performs elaboration of the LoF `Expression` to a `CicTerm`.
pub fn elaborate_expression(ast: &Expression) -> CicTerm {
    let elaborated = match ast {
        Expression::VarUse(var_name) => elaborate_var_use(var_name),
        Expression::Abstraction(var_name, var_type, body) => {
            elaborate_abstraction(var_name, &*var_type, &*body)
        }
        Expression::TypeProduct(var_name, var_type, body) => {
            elaborate_type_product(var_name, &*var_type, &*body)
        }
        Expression::Application(left, args) => {
            elaborate_application(left, args)
        }
        Expression::Let(var_name, var_type, definition_body, scope) => {
            elaborate_let(var_name, var_type, definition_body, scope)
        }
        Expression::Match(matched_term, branches) => {
            elaborate_match(&*matched_term, branches)
        }
        Expression::Arrow(domain, codomain) => {
            elaborate_arrow(domain, codomain)
        }
        Expression::Inferator() => elaborate_meta(),
        _ => panic!("Expression primitive {:?} is not supported in CIC", ast),
    };

    index_variables(&elaborated)
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
//
fn elaborate_var_use(var_name: &str) -> CicTerm {
    //TODO this should probably be at the parser level
    if var_name.len() > 1 && var_name.chars().all(|c| c.is_ascii_uppercase()) {
        Sort(var_name.to_string())
    } else {
        Variable(var_name.to_string(), PLACEHOLDER_DBI)
    }
}
//
//
fn elaborate_abstraction(
    var_name: &str,
    var_type: &Expression,
    body: &Expression,
) -> CicTerm {
    let var_type_term = elaborate_expression(var_type);
    let body_term = elaborate_expression(body);

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
) -> CicTerm {
    let type_term = elaborate_expression(var_type);
    let body_term = elaborate_expression(body);

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
) -> CicTerm {
    let fun_term = elaborate_expression(function);
    let arg_terms =
        simple_map(args.to_owned(), |arg| elaborate_expression(&arg));

    arg_terms.into_iter().fold(fun_term, |acc, arg| {
        Application(Box::new(acc), Box::new(arg))
    })
}
//
//
fn elaborate_arrow(domain: &Expression, codomain: &Expression) -> CicTerm {
    //TODO this introduces a binder on no variable. should it increase the dbi?
    let type_term = elaborate_expression(domain);
    let body_term = elaborate_expression(codomain);

    Product("_".to_string(), Box::new(type_term), Box::new(body_term))
}
//
//
fn elaborate_let(
    var_name: &str,
    var_type: &Option<Expression>,
    body: &Expression,
    scope: &Expression,
) -> CicTerm {
    let var_type = if var_type.is_some() {
        Some(elaborate_expression(&var_type.as_ref().unwrap()))
    } else {
        None
    };

    Let(
        var_name.to_string(),
        Box::new(var_type),
        Box::new(elaborate_expression(body)),
        Box::new(elaborate_expression(scope)),
    )
}
//
//
fn elaborate_match(
    matched_exp: &Expression,
    branches: &Vec<(Expression, Expression)>,
) -> CicTerm {
    //TODO im not sure if the match is a binder
    let matched_term = elaborate_expression(matched_exp);

    let mut branch_terms = vec![];
    for (pattern, body_exp) in branches {
        let pattern = elaborate_expression(pattern);
        let body_exp = elaborate_expression(body_exp);

        // let mut pattern_terms = vec![constr_term];
        // for arg in &pattern[1..] {
        //     let arg_term = elaborate_expression(arg);

        //     match &arg_term {
        //         Variable(_, _) => {
        //             pattern_terms.push(arg_term);
        //         }
        //         _ => panic!("Argument expression should be just a variable"),
        //     }
        // }

        // let body_term = elaborate_expression(&body_exp);

        branch_terms.push((pattern, body_exp));
    }

    Match(Box::new(matched_term), branch_terms)
}
//
//########################### EXPRESSIONS ELABORATION
//
//########################### STATEMENTS ELABORATION
pub fn elaborate_statement(ast: &Statement) -> Result<Schedule<Cic>, String> {
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
        Statement::Auto(formula) => {
            Ok(Schedule::singleton_stm(elaborate_auto(formula)?))
        } //
          // _ => Err(format!("Language construct {:?} not supported in CIC", ast)),
    }
}
//
//
fn elaborate_file_root(
    file_path: &String,
    asts: &Vec<LofAst>,
) -> Result<Schedule<Cic>, String> {
    elaborate_ast_vector::<Cic>(file_path, asts)
}
//
//
fn elaborate_dir_root(
    dir_path: &String,
    asts: &Vec<LofAst>,
) -> Result<Schedule<Cic>, String> {
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
                return Err(format!("AST nodes of directory node can only be FileRoot, not {:?}", sub_ast));
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
) -> Result<CicStm, String> {
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
) -> Result<CicStm, String> {
    let elaborated_args = map_typed_variables(&args);
    let elaborated_out_type = elaborate_expression(&out_type);
    let elaborated_body = elaborate_expression(&body);

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
) -> Result<CicStm, String> {
    let parameter_terms: Vec<(String, CicTerm)> =
        //TODO i assume inductive definitions are only top-level avaible but who knows
        map_typed_variables(&parameters);
    let ariety_term = elaborate_expression(&ariety);
    let ariety_term = index_variables(&ariety_term);
    let constructor_terms: Vec<(String, CicTerm)> = constructors
        .iter()
        .map(|(constr_name, constr_type)| {
            (constr_name.to_owned(), elaborate_expression(constr_type))
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
) -> Result<CicStm, String> {
    let elaborated_formula = elaborate_expression(&formula);
    Ok(Axiom(axiom_name.to_string(), Box::new(elaborated_formula)))
}
//
//
fn elaborate_theorem(
    theorem_name: &String,
    formula: &Expression,
    proof: &Union<Expression, Vec<Tactic<Expression>>>,
) -> Result<CicStm, String> {
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
fn elaborate_empty(nodes: &Vec<LofAst>) -> Result<Schedule<Cic>, String> {
    elaborate_ast_vector::<Cic>(&"".to_string(), nodes)
}
//
//
fn elaborate_auto(formula: &Expression) -> Result<CicStm, String> {
    Ok(Auto(elaborate_expression(formula)))
}
//
//########################### STATEMENTS ELABORATION

//########################### UNIT TESTS
#[cfg(test)]
mod unit_tests {
    use crate::{
        parser::api::Expression,
        type_theory::{
            cic::{
                cic::{
                    Cic, CicStm,
                    CicTerm::{
                        Abstraction, Application, Let, Match, Product, Sort,
                        Variable,
                    },
                    GLOBAL_INDEX, PLACEHOLDER_DBI,
                },
                elaboration::{
                    elaborate_application, elaborate_expression,
                    elaborate_inductive, elaborate_match,
                    elaborate_type_product, elaborate_var_use,
                },
            },
            interface::TypeTheory,
        },
    };

    #[test]
    fn test_var_elaboration() {
        let test_var_name = "test_var";
        let test_var = Variable(test_var_name.to_string(), GLOBAL_INDEX);
        let test_var_placeholder =
            Variable(test_var_name.to_string(), PLACEHOLDER_DBI);

        assert_eq!(
            elaborate_var_use(test_var_name),
            test_var_placeholder.clone(),
            "Variable term not properly constructed"
        );
        assert_eq!(
            elaborate_var_use("TYPE"),
            Sort("TYPE".to_string()),
            "Sort name returns a simple variable instead of a sort term"
        );
        assert_eq!(
            elaborate_expression(&Expression::VarUse(
                test_var_name.to_string()
            )),
            test_var.clone(),
            "Top level elaboration doesnt work with variables as expected"
        );
    }

    #[test]
    fn test_abs_elaboration() {
        let expected_term = Abstraction(
            "x".to_string(),
            Box::new(Sort("TYPE".to_string())),
            Box::new(Variable("x".to_string(), 0)),
        );

        assert_eq!(
            elaborate_expression(&Expression::Abstraction(
                "x".to_string(),
                Box::new(Expression::VarUse("TYPE".to_string())),
                Box::new(Expression::VarUse("x".to_string())),
            )),
            expected_term,
            "Top level elaborator isnt working with abstraction"
        );
    }

    #[test]
    fn test_prod_elaboration() {
        let expected_term = Product(
            "x".to_string(),
            Box::new(Sort("TYPE".to_string())),
            Box::new(Sort("TYPE".to_string())),
        );

        assert_eq!(
            elaborate_type_product(
                "x",
                &Expression::VarUse("TYPE".to_string()),
                &Expression::VarUse("TYPE".to_string())
            ),
            expected_term.clone(),
            "Type abstraction elaboration isnt working as expected"
        );
        assert_eq!(
            elaborate_expression(&Expression::TypeProduct(
                "x".to_string(),
                Box::new(Expression::VarUse("TYPE".to_string())),
                Box::new(Expression::VarUse("TYPE".to_string())),
            )),
            expected_term,
            "Top level elaborator isnt working with type abstraction"
        );
    }

    #[test]
    fn test_app_elaboration() {
        let expected_term = Application(
            Box::new(Variable("s".to_string(), GLOBAL_INDEX)),
            Box::new(Variable("o".to_string(), GLOBAL_INDEX)),
        );

        assert_eq!(
            elaborate_application(
                &Expression::VarUse("s".to_string()),
                &vec![Expression::VarUse("o".to_string())]
            ),
            expected_term.clone(),
            "Application elaboration isnt working as expected"
        );
        assert_eq!(
            elaborate_application(
                &Expression::VarUse("f".to_string()),
                &vec![
                    Expression::VarUse("x".to_string()),
                    Expression::VarUse("y".to_string())
                ]
            ),
            Application(
                Box::new(Application(
                    Box::new(Variable("f".to_string(), GLOBAL_INDEX)),
                    Box::new(Variable("x".to_string(), GLOBAL_INDEX)),
                )),
                Box::new(Variable("y".to_string(), GLOBAL_INDEX))
            ),
            "Application elaboration isnt respecting associativity"
        );
        assert_eq!(
            elaborate_expression(&Expression::Application(
                Box::new(Expression::VarUse("s".to_string())),
                vec![Expression::VarUse("o".to_string())],
            )),
            expected_term,
            "Top level elaborator isnt working with applications"
        );
    }

    #[test]
    fn test_let_elaboration() {
        assert_eq!(
            Cic::elaborate_expression(&Expression::Let(
                "x".to_string(),
                Box::new(Some(Expression::VarUse("Complex".to_string()))),
                Box::new(Expression::VarUse("i".to_string())),
                Box::new(Expression::VarUse("x".to_string())),
            )),
            Ok(Let(
                "x".to_string(),
                Box::new(Some(Variable("Complex".to_string(), GLOBAL_INDEX))),
                Box::new(Variable("i".to_string(), GLOBAL_INDEX)),
                Box::new(Variable("x".to_string(), 0)),
            )),
            "Let elaboration isnt producing the proper term"
        );
        assert_eq!(
            Cic::elaborate_expression(&Expression::Let(
                "x".to_string(),
                Box::new(None),
                Box::new(Expression::VarUse("i".to_string())),
                Box::new(Expression::VarUse("x".to_string())),
            )),
            Ok(Let(
                "x".to_string(),
                Box::new(None),
                Box::new(Variable("i".to_string(), GLOBAL_INDEX)),
                Box::new(Variable("x".to_string(), 0)),
            )),
            "Let elaboration cant cope with missing type annotation"
        );
    }

    #[test]
    fn test_match_elaboration() {
        let expected_term = Match(
            Box::new(Variable("t".to_string(), GLOBAL_INDEX)),
            vec![
                (
                    Variable("o".to_string(), GLOBAL_INDEX),
                    Application(
                        Box::new(Variable("s".to_string(), GLOBAL_INDEX)),
                        Box::new(Variable("o".to_string(), GLOBAL_INDEX)),
                    ),
                ),
                (
                    Application(
                        Box::new(Variable("s".to_string(), GLOBAL_INDEX)),
                        Box::new(Variable("n".to_string(), GLOBAL_INDEX)),
                    ),
                    Variable("n".to_string(), GLOBAL_INDEX),
                ),
            ],
        );
        let base_pattern = (
            Expression::VarUse("o".to_string()),
            Expression::Application(
                Box::new(Expression::VarUse("s".to_string())),
                vec![Expression::VarUse("o".to_string())],
            ),
        );
        let inductive_patter = (
            Expression::Application(
                Box::new(Expression::VarUse("s".to_string())),
                vec![Expression::VarUse("n".to_string())],
            ),
            Expression::VarUse("n".to_string()),
        );

        assert_eq!(
            elaborate_match(
                &Expression::VarUse("t".to_string()),
                &vec![base_pattern.clone(), inductive_patter.clone()]
            ),
            expected_term,
            "Match elaboration isnt working as expected"
        );
        assert_eq!(
            elaborate_expression(&Expression::Match(
                Box::new(Expression::VarUse("t".to_string())),
                vec![base_pattern, inductive_patter]
            )),
            expected_term,
            "Top level elaboration doesnt work with match"
        );
    }

    #[test]
    fn test_inductive_elaboration() {
        let ariety = Expression::VarUse("TYPE".to_string());

        let result = elaborate_inductive(
            &"nat".to_string(),
            &vec![],
            &ariety,
            &vec![
                ("o".to_string(), Expression::VarUse("nat".to_string())),
                (
                    "s".to_string(),
                    Expression::TypeProduct(
                        "_".to_string(),
                        Box::new(Expression::VarUse("nat".to_string())),
                        Box::new(Expression::VarUse("nat".to_string())),
                    ),
                ),
            ],
        );
        assert_eq!(
            result,
            Ok(CicStm::InductiveDef(
                "nat".to_string(),
                vec![],
                Box::new(Sort("TYPE".to_string())),
                vec![
                    (
                        "o".to_string(),
                        Variable("nat".to_string(), GLOBAL_INDEX)
                    ),
                    (
                        "s".to_string(),
                        Product(
                            "_".to_string(),
                            Box::new(Variable("nat".to_string(), GLOBAL_INDEX)),
                            Box::new(Variable("nat".to_string(), GLOBAL_INDEX)),
                        )
                    )
                ]
            )),
            "Inductive elaboration isnt working with constant constructor"
        );
    }
}
