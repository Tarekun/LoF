use super::elaboration::{elaborate_expression, elaborate_statement};
use super::evaluation::{evaluate_statement, one_step_reduction};
use super::type_check::{
    type_check_application, type_check_arrow, type_check_forall,
};
use crate::misc::Union::{self, L, R};
use crate::parser::api::{Expression, Statement, Tactic};
use crate::runtime::program::Schedule;
use crate::type_theory::commons::evaluation::generic_term_normalization;
use crate::type_theory::commons::type_check::{
    type_check_abstraction, type_check_axiom, type_check_let,
    type_check_theorem, type_check_variable,
};
use crate::type_theory::environment::Environment;
use crate::type_theory::fol::fol::FolFormula::{
    Arrow, Conjunction, Disjunction, ForAll, Not, Predicate,
};
use crate::type_theory::fol::fol::FolStm::{Axiom, Fun, Let, Theorem};
use crate::type_theory::fol::fol::FolTerm::{
    Abstraction, Application, Tuple, Variable,
};
use crate::type_theory::fol::type_check::{
    fol_type_check_fun, type_check_conjunction, type_check_disjunction,
    type_check_not, type_check_predicate, type_check_tuple,
};
use crate::type_theory::interface::{Interactive, Kernel, Reducer, TypeTheory};

#[derive(Debug, Clone, PartialEq)]
pub enum FolTerm {
    Variable(String),
    Abstraction(String, Box<FolFormula>, Box<FolTerm>),
    Application(Box<FolTerm>, Box<FolTerm>),
    Tuple(Vec<FolTerm>),
}
#[derive(Clone, PartialEq)]
pub enum FolFormula {
    //TODO add predicate application
    Predicate(String, Vec<FolTerm>),
    Arrow(Box<FolFormula>, Box<FolFormula>),
    Not(Box<FolFormula>),
    Conjunction(Vec<FolFormula>),
    Disjunction(Vec<FolFormula>),
    ForAll(String, Box<FolFormula>, Box<FolFormula>),
    Exist(String, Box<FolFormula>, Box<FolFormula>),
}
#[derive(Debug, PartialEq, Clone)]
pub enum FolStm {
    /// axiom_name, formula
    Axiom(String, FolFormula),
    /// theorem_name, formula, proof
    Theorem(
        String,
        Box<FolFormula>,
        Union<FolTerm, Vec<Tactic<Union<FolTerm, FolFormula>>>>,
    ),
    /// (var_name, var_type, definition_body)
    Let(String, Option<FolFormula>, Box<FolTerm>),
    /// (fun_name, args, out_type, body, is_rec)
    Fun(
        String,
        Vec<(String, FolFormula)>,
        Box<FolFormula>,
        Box<FolTerm>,
        bool,
    ),
}

pub struct Fol;

impl TypeTheory for Fol {
    type Term = FolTerm;
    type Type = FolFormula;
    type Stm = FolStm;
    type Exp = Union<FolTerm, FolFormula>;

    fn default_environment() -> Environment<Fol> {
        Environment::with_defaults(
            vec![],
            vec![],
            vec![("Unit", &vec![]), ("Top", &vec![])],
        )
    }

    // TODO only supports identical expressions
    fn base_term_equality(
        term1: &Self::Term,
        term2: &Self::Term,
    ) -> Result<(), String> {
        if *term1 == *term2 {
            Ok(())
        } else {
            Err(format!("{:?} and {:?} are not equal", term1, term2))
        }
    }
    fn base_type_equality(
        type1: &Self::Type,
        type2: &Self::Type,
    ) -> Result<(), String> {
        if *type1 == *type2 {
            Ok(())
        } else {
            Err(format!("{:?} and {:?} are not equal", type1, type2))
        }
    }

    fn elaborate_expression(exp: &Expression) -> Result<Self::Exp, String> {
        elaborate_expression(exp)
    }
    fn elaborate_statement(stm: &Statement) -> Result<Schedule<Fol>, String> {
        elaborate_statement(stm)
    }
}

impl Kernel for Fol {
    fn type_check_expression(
        exp: &Union<FolTerm, FolFormula>,
        environment: &mut Environment<Fol>,
    ) -> Result<Self::Type, String> {
        match exp {
            L(term) => Fol::type_check_term(term, environment),
            R(typee) => Fol::type_check_type(typee, environment),
        }
    }

    fn type_check_term(
        term: &FolTerm,
        environment: &mut Environment<Fol>,
    ) -> Result<FolFormula, String> {
        match term {
            Variable(var_name) => {
                type_check_variable::<Fol>(environment, var_name)
            }
            Abstraction(var_name, var_type, body) => {
                type_check_abstraction::<Fol, _>(
                    environment,
                    var_name,
                    var_type,
                    body,
                    |_, var_type, body_type| {
                        Arrow(Box::new(var_type), Box::new(body_type))
                    },
                )
            }
            Application(left, right) => {
                type_check_application(environment, left, right)
            }
            Tuple(terms) => type_check_tuple(environment, terms),
        }
    }

    // TODO i need to decide what exact type to return here
    fn type_check_type(
        typee: &FolFormula,
        environment: &mut Environment<Fol>,
    ) -> Result<FolFormula, String> {
        match typee {
            Predicate(type_name, args) => {
                type_check_predicate(environment, type_name, args)
            }
            Arrow(domain, codomain) => {
                type_check_arrow(environment, domain, codomain)
            }
            ForAll(var_name, var_type, predicate) => {
                type_check_forall(environment, var_name, var_type, predicate)
            }
            Not(ψ) => type_check_not(environment, ψ),
            Conjunction(sub_formulas) => {
                type_check_conjunction(environment, sub_formulas)
            }
            Disjunction(sub_formulas) => {
                type_check_disjunction(environment, sub_formulas)
            }
            _ => {
                Err("TODO: Existential type checking not yet supported"
                    .to_string())
            }
        }
    }

    // TODO i need to decide what exact type to return here
    fn type_check_stm(
        stm: &Self::Stm,
        environment: &mut Environment<Fol>,
    ) -> Result<Self::Type, String> {
        match stm {
            Axiom(axiom_name, predicate) => {
                type_check_axiom::<Fol>(environment, axiom_name, predicate)
            }
            Let(var_name, opt_type, body) => {
                type_check_let::<Fol>(environment, var_name, opt_type, body)
            }
            Fun(fun_name, args, out_type, body, is_rec) => fol_type_check_fun(
                environment,
                fun_name,
                args,
                out_type,
                body,
                is_rec,
            ),
            Theorem(theorem_name, formula, proof) => type_check_theorem::<Fol>(
                environment,
                theorem_name,
                formula,
                proof,
            ),
        }
    }
}

impl Reducer for Fol {
    fn normalize_expression(
        environment: &mut Environment<Fol>,
        exp: &Union<FolTerm, FolFormula>,
    ) -> Union<FolTerm, FolFormula> {
        match exp {
            L(term) => L(Fol::normalize_term(environment, term)),
            R(typee) => {
                panic!("TODO still need to implement type normalization in FOL")
            }
        }
    }

    fn normalize_term(
        environment: &mut Environment<Fol>,
        term: &FolTerm,
    ) -> FolTerm {
        generic_term_normalization::<Fol, _>(
            environment,
            term,
            one_step_reduction,
        )
    }

    fn evaluate_statement(
        environment: &mut Environment<Fol>,
        stm: &FolStm,
    ) -> () {
        evaluate_statement(environment, stm)
    }
}

impl Interactive for Fol {
    fn proof_hole() -> Self::Term {
        Variable("THIS_IS_A_PARTIAL_PROOF_HOLE".to_string())
    }
    fn empty_target() -> Self::Type {
        Predicate(
            "THIS_IS_AN_EMPTY_TERMINATION_PROOF_TARGET".to_string(),
            vec![],
        )
    }

    fn type_check_tactic(
        environment: &mut Environment<Fol>,
        tactic: &Tactic<Self::Exp>,
        target: &Self::Type,
        partial_proof: &Self::Term,
    ) -> Result<(Self::Type, Self::Term), String> {
        Err("not implemented".to_string())
    }
}
