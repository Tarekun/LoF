use crate::{
    misc::Union::{self, L, R},
    type_theory::interface::TypeTheory,
};

pub fn generic_multiarg_fun_type<T, F>(
    arg_types: &[(String, T::Type)],
    base: &T::Type,
    aggregator: F,
) -> T::Type
where
    T: TypeTheory,
    F: Fn(String, T::Type, T::Type) -> T::Type + Copy,
{
    if arg_types.is_empty() {
        return base.to_owned();
    }

    let ((arg_name, arg_type), rest) = arg_types.split_first().unwrap();
    let sub_type = generic_multiarg_fun_type::<T, F>(rest, base, aggregator);

    aggregator(arg_name.to_owned(), arg_type.to_owned(), sub_type)
}

/// Wraps a term in the expressions union
pub fn wrap_term<T: TypeTheory>(
    term_exp: Result<T::Term, String>,
) -> Result<Union<T::Term, T::Type>, String> {
    let term_exp = term_exp?;
    Ok(L(term_exp))
}
/// Wraps a type in the expressions union
pub fn wrap_type<T: TypeTheory>(
    type_exp: Result<T::Type, String>,
) -> Result<Union<T::Term, T::Type>, String> {
    let type_exp = type_exp?;
    Ok(R(type_exp))
}

/// η-expands `body` by wrapping it in a function with arguments `args`.
/// First element of the slice will be the first argument to apply
pub fn eta_expand<
    T: TypeTheory,
    F: Fn((String, T::Type), T::Term) -> T::Term,
>(
    args: &[(String, T::Type)],
    body: &T::Term,
    single_wrap: F,
) -> T::Term {
    args.iter()
        .rev()
        .cloned()
        .fold(body.clone(), |acc, arg| single_wrap(arg, acc))
}

pub enum UnifiedExpression<T: TypeTheory> {
    L(T::Term),
    R(T::Type),
}
impl<T: TypeTheory> UnifiedExpression<T> {
    pub fn of_term(term: T::Term) -> UnifiedExpression<T> {
        UnifiedExpression::L(term)
    }

    pub fn of_type(typee: T::Type) -> UnifiedExpression<T> {
        UnifiedExpression::R(typee)
    }

    pub fn as_union(self) -> Union<T::Term, T::Type> {
        match self {
            UnifiedExpression::L(term) => Union::L(term),
            UnifiedExpression::R(typee) => Union::R(typee),
        }
    }
}
