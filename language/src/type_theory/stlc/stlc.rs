use super::elaboration::{
    elaborate_abstraction, elaborate_application, elaborate_arrow,
    elaborate_file_root, elaborate_var_use,
};
use crate::parser::api::{Expression, NsAst, Statement};
use crate::runtime::program::Program;
use crate::type_theory::environment::Environment;
use crate::type_theory::interface::TypeTheory;

#[derive(Debug, Clone, PartialEq)] //support toString printing and equality check
pub enum StlcTerm {
    Variable(String),
    Abstraction(String, Box<StlcType>, Box<StlcTerm>),
    Application(Box<StlcTerm>, Box<StlcTerm>),
    //
    ArrowTmpTerm(Box<StlcTerm>, Box<StlcTerm>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum StlcType {
    Atomic(String),
    Arrow(Box<StlcType>, Box<StlcType>),
}

pub struct Stlc;
impl TypeTheory for Stlc {
    type Term = StlcTerm;
    type Type = StlcType;

    fn elaborate_expression(ast: Expression) -> StlcTerm {
        match ast {
            Expression::VarUse(var_name) => elaborate_var_use(var_name),
            Expression::Abstraction(var_name, var_type, body) => {
                elaborate_abstraction(var_name, *var_type, *body)
            }
            Expression::Application(left, right) => {
                elaborate_application(*left, *right)
            }
            Expression::Arrow(domain, codomain) => {
                elaborate_arrow(*domain, *codomain)
            }
            _ => panic!("non implemented"),
        }
    }

    fn elaborate_statement(
        ast: Statement,
        program: &mut Program<StlcTerm>,
    ) -> Result<(), String> {
        match ast {
            Statement::Comment() => Ok(()),
            Statement::FileRoot(file_path, asts) => {
                elaborate_file_root(program, file_path, asts);
                Ok(())
            }
            Statement::Let(_, _, _) => {
                program.push_statement(&ast);
                Ok(())
            }
            _ => panic!("not implemented"),
        }
    }

    fn elaborate_ast(ast: NsAst) -> Program<StlcTerm> {
        let nat = StlcType::Atomic("nat".to_string());
        let mut program = Program::new();

        match ast {
            NsAst::Stm(stm) => {
                let _ = Stlc::elaborate_statement(stm, &mut program);
            }
            NsAst::Exp(exp) => {
                let _ = Stlc::elaborate_expression(exp);
            }
        }

        program
    }

    fn type_check(
        term: StlcTerm,
        environment: &mut Environment<StlcTerm, StlcType>,
    ) -> Result<StlcType, String> {
        return Ok(StlcType::Atomic("TODO".to_string()));
    }

    fn terms_unify(term1: &StlcTerm, term2: &StlcTerm) -> bool {
        term1 == term2
    }

    fn types_unify(type1: &StlcType, type2: &StlcType) -> bool {
        type1 == type2
    }
}
