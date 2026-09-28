use crate::{
    error::LofError,
    type_theory::{
        commons::unification::Substitution,
        environment::Environment,
        grammars::cnf::{CnfFormula, CnfTerm},
        interface::{Kernel, TypeTheory},
    },
};

/// Trait for type checking/well formedness quick access.
/// This trait must be parametric on a TypeTheory, because typing rules
/// are of a type system, not a grammar
pub trait Check<T: Kernel> {
    fn check(&self, env: Environment<T>) -> Result<T::Type, LofError>;
}

/// Trait for complementation of formulas
pub trait Complement {
    fn complement(&self) -> Self;
}

/// Substitution by explicitly provided variable name
pub trait NamedSubstitution<T> {
    /// Returns a copy of `self` where every occurance of `target_name`
    /// is replaced by `arg`
    fn substitute_name(&self, target_name: &str, arg: &T) -> Self;
}

/// Trait for expression reduction. Requires the implementation of
/// one step reduction (`step`) and using it implements right away
/// a transitive closure of it
// TODO: this should really depend on any given TypeTheory, currently
// this is needed only because Environment depends on T, but it would
// only need the type for terms and types
pub trait Reduction<T: TypeTheory> {
    /// Performs one step of expression reduction
    fn step(&self, env: &Environment<T>) -> Self;

    /// Reduces an expression to its normal form by iterating `step`
    /// until it reaches a fixpoint
    fn reduce_to_normal(&self, env: &Environment<T>) -> Self
    where
        Self: Clone + PartialEq,
    {
        let mut reduced = self.to_owned();
        loop {
            let next = reduced.step(env);
            if next == reduced {
                return reduced;
            }
            reduced = next
        }
    }
}

pub trait ToCnfTerm {
    fn to_cnf(&self) -> CnfTerm;
}
pub trait ToCnfFormula {
    fn to_cnf(&self) -> Vec<CnfFormula>;
}

/// Unification utilities for expressions.
/// Requires implementation of a unification algorithm (`unifies`) that
/// computes the MGU and a transformation function to apply such MGU
pub trait Unification<T> {
    /// Returns the MGU that unifies `self` and `other` if any, otherwise
    /// returns an error with a message on why terms don't unify
    fn unifies(&self, other: &Self) -> Result<Substitution<T>, LofError>;

    /// Returns a copy of `self` with the `substitution` applied
    fn apply_substitution(&self, substitution: &Substitution<T>) -> Self;
}
