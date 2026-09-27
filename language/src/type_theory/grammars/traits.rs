use crate::{error::LofError, type_theory::commons::unification::Substitution};

pub trait Unification<T> {
    /// Returns the MGU that unifies `self` and `other` if any, otherwise
    /// returns an error with a message on why terms don't unify
    fn unifies(&self, other: &Self) -> Result<Substitution<T>, LofError>;

    /// Returns a copy of `self` with the `substitution` applied
    fn apply_substitution(&self, substitution: &Substitution<T>) -> Self;
}

pub trait NamedSubstitution<T> {
    fn substitute(&self, target_name: &str, arg: &T) -> Self;
}
