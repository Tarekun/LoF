use crate::error::LofError;
use crate::misc::Union::{self, L, R};
use crate::parser::api::{Expression, LofAst, Statement, Tactic};
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

/// Base trait for type systems. Requires a grammar for terms,
/// one for type and one for statements, plus a function that
/// returns the default environment for this system.
/// Higher order systems can set Self::Term = Self::Type
pub trait TypeTheory {
    /// Enum listing all the term constructors.
    type Term: Debug + Clone + PartialEq;
    /// Enum listing all the type constructors.
    type Type: Debug + Clone + PartialEq;
    /// Enum listing all the statements elaborated with proper types
    type Stm: Debug + Clone;
    /// Type for the system's expressions, usually Term or Union<Term, Type>
    type Exp: Debug + Clone;

    /// Create the default environment
    fn default_environment() -> Environment<Self>
    where
        Self: Sized;

    /// Computes default system equality. Returns Ok(()) if the check is
    /// successfull, an error message otherwise.
    /// This is the equality checked used by the commons library for consistency
    fn base_term_equality(
        term1: &Self::Term,
        term2: &Self::Term,
    ) -> Result<(), LofError>;

    /// Computes default system equality. Returns Ok(()) if the check is
    /// successfull, an error message otherwise.
    /// This is the equality checked used by the commons library for consistency
    fn base_type_equality(
        type1: &Self::Type,
        type2: &Self::Type,
    ) -> Result<(), LofError>;

    fn elaborate_expression(exp: &Expression) -> Result<Self::Exp, LofError>;
    fn elaborate_statement(stm: &Statement) -> Result<Schedule<Self>, LofError>
    where
        Self: Sized;

    fn elaborate_node(
        node: &LofAst,
    ) -> Result<Union<Self::Exp, Self::Stm>, LofError>
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
        term: &Self::Stm,
        environment: &mut Environment<Self>,
    ) -> Result<Self::Type, LofError>
    where
        Self: Sized;
}

pub trait TypeInference: TypeTheory {
    fn type_unify(
        type1: &Self::Type,
        type2: &Self::Type,
    ) -> Result<Substitution<Self::Type>, LofError>;

    fn apply_so_substitution(
        typ: &Self::Type,
        mgu: &Substitution<Self::Type>,
    ) -> Self::Type;
}

/// Refiner module, implements unification
pub trait Refiner: TypeTheory {
    /// Collects unification constraints necessary for `term`
    fn term_collect_unifications(
        term: &Self::Term,
        environment: &mut Environment<Self>,
    ) -> Result<Vec<(Self::Exp, Self::Exp)>, LofError>
    where
        Self: Sized;

    /// Collects unification constraints necessary for `typee`
    fn type_collect_unifications(
        typee: &Self::Type,
        environment: &mut Environment<Self>,
    ) -> Result<Vec<(Self::Exp, Self::Exp)>, LofError>
    where
        Self: Sized;

    /// Algorithm to compute the MCU given a set of constraints.
    /// Returns a substitution for all solvable meta variables or an error
    fn solve_unifications(
        constraints: Vec<(Self::Exp, Self::Exp)>,
        environment: &mut Environment<Self>,
    ) -> Result<Substitution<Self::Exp>, LofError>
    where
        Self: Sized;

    /// Applies a given Substitution to `term`
    fn term_apply_unifier(
        term: &Self::Term,
        substitution: &Substitution<Self::Exp>,
    ) -> Self::Term;

    /// Applies a given Substitution to `typee`
    fn type_apply_unifier(
        typee: &Self::Type,
        substitution: &Substitution<Self::Exp>,
    ) -> Self::Type;

    /// Check if the two terms provided unify with one another
    /// ie they are structurally equal, given a unifier for metavariables
    fn terms_unify(
        environment: &mut Environment<Self>,
        term1: &Self::Term,
        term2: &Self::Term,
    ) -> Result<(), LofError>
    where
        Self: Sized;

    /// Check if the two types provided unify with one another
    /// ie they are structurally equal, given a unifier for metavariables
    fn types_unify(
        environment: &mut Environment<Self>,
        type1: &Self::Type,
        type2: &Self::Type,
    ) -> Result<(), LofError>
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
        stm: &Self::Stm,
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

    /// Recomputes variable binding metadata (eg. de Bruijn indices) over a
    /// fully assembled interactive proof term. Tactic steps are checked and
    /// composed one subgoal at a time, each in its own, independently
    /// elaborated fragment (eg. `intro`'s introduced assumption, or an
    /// `exact`/`apply` term), so identically-named variables may end up
    /// tagged inconsistently across fragments (eg. as a free/global
    /// reference in one place, but a binder-relative index in another) even
    /// though they refer to the same bound variable once the fragments are
    /// glued together. Implementors should normalize the finished term so it
    /// matches what ordinary, single-pass elaboration would have produced,
    /// before it is type-checked against the theorem's stated formula.
    fn reindex_proof(term: &Self::Term) -> Self::Term;

    /// Proof checking for the current `tactic` given a `target` and a `partial_proof`.
    /// Returns an updated (proof_term, subgoals) pair
    fn type_check_tactic(
        environment: &mut Environment<Self>,
        tactic: &Tactic<Self::Exp>,
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
