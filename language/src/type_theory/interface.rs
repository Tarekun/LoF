use crate::error::LofError;
use crate::misc::Union::{self, L, R};
use crate::parser::api::{Expression, LofAst, LofStatement, Statement, Tactic};
use crate::runtime::program::{
    ProgramNode::{OfExp, OfStm},
    Schedule,
};
use crate::type_theory::commons::unification::Substitution;
use crate::type_theory::environment::Environment;
use crate::type_theory::sup::freedom::{
    GivingClauseSignature, SelectionFunctionSignature,
};
use std::cmp::Ordering;
use std::fmt::Debug;

/// Statements elaborated in the grammars of the type system `T`
pub type Stm<T> = Statement<<T as TypeTheory>::Term, <T as TypeTheory>::Type>;

/// Base trait for type systems. Requires a grammar for terms
/// and one for types, plus a function that returns the default
/// environment for this system. Statements are shared by all systems
/// and instantiated over these grammars (see `Stm`).
/// Higher order systems can set Self::Term = Self::Type
pub trait TypeTheory {
    /// Enum listing all the term constructors.
    type Term: Debug + Clone + PartialEq;
    /// Enum listing all the type constructors.
    type Type: Debug + Clone + PartialEq;
    /// Type for the system's expressions, usually Term or Union<Term, Type>
    type Exp: Debug + Clone;

    /// Create the default environment
    fn default_environment() -> Environment<Self>
    where
        Self: Sized;

    /// Computes default system equality. Returns Ok(()) if the check is
    /// successfull, an error message otherwise.
    /// This is the equality checked used by the commons library for consistency
    fn term_judgemental_equality(
        env: &Environment<Self>,
        term1: &Self::Term,
        term2: &Self::Term,
    ) -> Result<(), LofError>
    where
        Self: Sized;

    /// Computes default system equality. Returns Ok(()) if the check is
    /// successfull, an error message otherwise.
    /// This is the equality checked used by the commons library for consistency
    fn type_judgemental_equality(
        env: &Environment<Self>,
        type1: &Self::Type,
        type2: &Self::Type,
    ) -> Result<(), LofError>
    where
        Self: Sized;

    fn elaborate_expression(exp: &Expression) -> Result<Self::Exp, LofError>;
    fn elaborate_statement(
        stm: &LofStatement,
    ) -> Result<Schedule<Self>, LofError>
    where
        Self: Sized;

    fn elaborate_node(
        node: &LofAst,
    ) -> Result<Union<Self::Exp, Stm<Self>>, LofError>
    where
        Self: Sized,
    {
        match node {
            LofAst::Exp(exp) => Ok(L(Self::elaborate_expression(exp)?)),
            LofAst::Stm(stm) => {
                //TODO in case of nested staments this has no concept of schedule and picks the first element at random
                let first_stm = Self::elaborate_statement(stm)?
                    .peek_first()
                    .unwrap()
                    .to_owned();
                match first_stm {
                    OfStm(stm) => Ok(R(stm)),
                    OfExp(_) => Err(LofError::custom(
                        "elaborate_node: TODO nested statements have no schedule concept yet",
                    )),
                }
            }
        }
    }

    /// Elaborate a full AST into a program.
    fn elaborate_ast(ast: &LofAst) -> Result<Schedule<Self>, LofError>
    where
        Self: Sized,
    {
        let mut schedule = Schedule::new();

        match ast {
            LofAst::Exp(exp) => {
                let exp = Self::elaborate_expression(exp)?;
                schedule.add_expression(&exp);
            }
            LofAst::Stm(stm) => {
                let subschedule = Self::elaborate_statement(stm)?;
                schedule.extend(&subschedule);
            }
        }

        Ok(schedule)
    }
}

/// Kernel module, implements the type checking algorithms
pub trait Kernel: TypeTheory {
    /// Type checks the term and returns its type.
    fn type_check_term(
        term: &Self::Term,
        environment: &mut Environment<Self>,
    ) -> Result<Self::Type, LofError>
    where
        Self: Sized;

    /// Type checks the type and returns its type.
    fn type_check_type(
        typee: &Self::Type,
        environment: &mut Environment<Self>,
    ) -> Result<Self::Type, LofError>
    where
        Self: Sized;

    // Type checks the expression and returns its type
    fn type_check_expression(
        exp: &Self::Exp,
        environment: &mut Environment<Self>,
    ) -> Result<Self::Type, LofError>
    where
        Self: Sized;

    /// Type checks the statement components
    fn type_check_stm(
        term: &Stm<Self>,
        environment: &mut Environment<Self>,
    ) -> Result<Self::Type, LofError>
    where
        Self: Sized;
}

/// Reducer module, implements the execution of programs
pub trait Reducer: TypeTheory {
    /// Given a `term`, a `var_name`, and a substitution `body`,
    /// returns the term where occurences of `var_name` have been swapped with `body`
    // TODO this doesnt feel right. what about dependent types? what about second order formulas?
    fn substitute(
        term: &Self::Term,
        var_name: &str,
        body: &Self::Term,
    ) -> Self::Term;

    /// Reduces the given term to its normal form
    fn normalize_term(
        environment: &Environment<Self>,
        term: &Self::Term,
    ) -> Self::Term
    where
        Self: Sized;

    fn normalize_expression(
        environment: &Environment<Self>,
        exp: &Self::Exp,
    ) -> Self::Exp
    where
        Self: Sized;

    /// Evaluates the statement, updating the context accordingly
    fn evaluate_statement(
        environment: &mut Environment<Self>,
        stm: &Stm<Self>,
    ) -> Result<(), LofError>
    where
        Self: Sized;
}

/// Interactive module, implements tactic checking for interactive theorem proving
pub trait Interactive: TypeTheory {
    /// Canonical proof hole term for partial proofs
    fn proof_hole() -> Self::Term;
    /// Canonical empty  target signaling the completeness of the proof
    fn empty_target() -> Self::Type;

    /// Proof checking for the current `tactic` given a `target` and a `partial_proof`.
    /// Returns an updated (proof_term, subgoals) pair
    fn type_check_tactic(
        environment: &mut Environment<Self>,
        tactic: &Tactic<Self::Term, Self::Type>,
        target: &Self::Type,
        partial_proof: &Self::Term,
    ) -> Result<(Self::Term, Vec<Self::Type>), LofError>
    where
        Self: Sized;
}

/// Automatic module, implements automatic theorem proving via satisfaction
/// of a set of formulas. Inspired by saturation algorithms on Sup
pub trait Automatic: TypeTheory {
    /// Simplification ordering over terms. Returns < 0 if t1 < t2,
    /// returns > 0 if t2 < t1, 0 otherwise
    fn compare_terms(term1: &Self::Term, term2: &Self::Term) -> Ordering;
    #[allow(non_snake_case)]
    /// Simplification ordering over types. Returns < 0 if T1 < T2,
    /// returns > 0 if T2 < T1, 0 otherwise
    fn compare_types(type1: &Self::Type, type2: &Self::Type) -> Ordering;

    /// Runs the saturation algorithm on the given set, closing the set under
    /// derivation. Terminates when bottom is derived or nothing new can be derived
    fn saturate(
        saturation_set: &Vec<Self::Type>,
        selection_fn: &SelectionFunctionSignature,
        giving_clause_fn: &GivingClauseSignature,
    ) -> Result<Substitution<Self::Term>, LofError>;
}
