use crate::{
    error::LofError,
    type_theory::{
        commons::unification::Substitution,
        environment::Environment,
        grammars::cnf::{CnfFormula, CnfTerm},
        interface::{Kernel, TypeTheory},
    },
};

pub trait BottomTop {
    /// Returns `true` iff `self` represents bottom (or false)
    fn is_bottom(&self) -> bool;

    /// Returns `true` iff `self` represents top (or true)
    fn is_top(&self) -> bool;
}

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
// TODO: this shouldnt really depend on any given TypeTheory, currently
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

pub trait SyntacticalEq {
    /// Returns `true` iff `self` and `other` are exactly the same expression
    fn syntactically_equal(&self, other: &Self) -> bool;
}
pub trait AlphaEquiv {
    /// Returns `true` iff `self` and `other` are the same expression up to
    /// the renaming of bound variables (α-conversion)
    fn alpha_equivalent(&self, other: &Self) -> bool;
}
pub trait ReductionEq<T: TypeTheory>: Reduction<T> + SyntacticalEq {
    /// Returns `true` iff `self` and `other` are exactly the same expression when reduced to their normal form
    fn equal_up_to_reduction(&self, other: &Self, env: &Environment<T>) -> bool
    where
        Self: Clone + PartialEq,
    {
        let self_reduced = self.reduce_to_normal(env);
        let other_reduced = other.reduce_to_normal(env);
        self_reduced.syntactically_equal(&other_reduced)
    }
}

/// Locally nameless representation of binders: bound variables are De
/// Bruijn indices while free ones are names
pub trait LocallyNameless {
    /// Opens instances of `name` within `self`, marking them as (locally)
    /// free variables instead of bounded with a De Bruijn index
    fn open(&self, name: &str) -> Self;

    /// Rebuilds a binder around `self`, turning the locally free `name` back
    /// into a bound variant and updating De Bruijn indeces. Inverse of `open`
    fn close(&self, name: &str) -> Self;
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
