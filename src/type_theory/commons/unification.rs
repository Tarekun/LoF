use std::{
    collections::{HashMap, VecDeque},
    fmt::Debug,
};

#[derive(Clone, PartialEq, Debug)]
pub struct Substitution<T> {
    mappings: HashMap<String, T>,
}
impl<T: Debug + Clone + PartialEq> Substitution<T> {
    /// Creates an empty substitution of variables
    pub fn empty() -> Self {
        Substitution {
            mappings: HashMap::new(),
        }
    }
    // look wtf i have to do for a fucking wrapper to that pos from
    // i hate ferris fr sometimes
    pub fn from<I>(pairs: I) -> Self
    where
        I: IntoIterator<Item = (String, T)>,
    {
        Substitution {
            mappings: pairs.into_iter().collect(),
        }
    }

    pub fn get(&self, var_name: &str) -> Option<&T> {
        self.mappings.get(var_name)
    }

    fn add_substitution<O, Iv>(
        &mut self,
        var_name: &str,
        body: &T,
        occurs: &O,
        is_variable: &Iv,
    ) -> Result<(), String>
    where
        O: Fn(&T, &str) -> bool,
        Iv: Fn(&T) -> Option<String>,
    {
        // avoid failing on x=x but do not generate useless assignment
        if let Some(other_variable) = is_variable(body) {
            if var_name == other_variable {
                return Ok(());
            }
        }

        let (var_name, body) =
            // if a substitution for var_name is already present  find another variable to add as a key
            if let Some(previous_subst) = self.mappings.get(var_name) {
                if let Some(other_variable) = is_variable(previous_subst)
                {
                    (other_variable, body.to_owned())
                } else if let Some(other_variable) = is_variable(body) {
                    (other_variable, previous_subst.to_owned())
                }
                else if *previous_subst != *body {
                    return Err(format!(
                        "Unification failed: found conflicting substitution for variable {}: term {:?} and term {:?}",
                        var_name, previous_subst, body
                    ));
                } else {
                    return Ok(())
                }
            } else {
                (var_name.to_string(), body.to_owned())
            };

        if occurs(&body, &var_name) {
            // occurs check
            return Err(format!(
                "Substitution body {:?} contains a reference to variable {:?}",
                body, var_name
            ));
        }

        self.mappings.insert(var_name, body);
        return Ok(());
    }

    pub fn reduce<S>(self, reduce_var: S) -> Substitution<T>
    where
        S: Fn(&T, &str, &T) -> T,
    {
        let mut reduced_mappings = HashMap::new();
        for (var, term) in &self.mappings {
            let mut reduced_term = term.clone();
            // apply every other substitution to term and append it in the new one
            for (other_var, other_term) in &self.mappings {
                if var == other_var {
                    continue;
                }
                reduced_term = reduce_var(&reduced_term, other_var, other_term);
            }

            reduced_mappings.insert(var.clone(), reduced_term);
        }

        Substitution {
            mappings: reduced_mappings,
        }
    }

    pub fn merge(&mut self, other: Substitution<T>) {
        self.mappings.extend(other.mappings);
    }

    pub fn names(&self) -> Vec<&String> {
        self.mappings.keys().collect()
    }
}

/// Expression-agnostic Hindley-Milner style unification algorithm.
/// Takes 2 expressions in the grammar `T` and checks if `exp1` ≐ `exp2`
/// returning the mgu satisfying unification. It also takes 4 functional arguments
/// needed to implement the recursive algorithm. Implementation is tail-recursive
///
/// # Function arguments requirements
///
/// * `is_variable` - Checks if an expression is a variable returning `Some` of the name, `None` otherwise
/// * `structurally_equal` - Returns `true` if two expressions are structurally equal, `false` otherwise
/// * `explode` - Returns a vector of the subcomponents of the expression to recur on in the unification algorithm (e.g., for a function application, it would return the arguments)
/// * `occurs` - Returns `true` if a variable occurs in an expression, `false` otherwise
///
/// # Returns
///
/// * `Result<Substitution<T>, String>` - The MGU if unification succeeds or an error message if unification fails.
pub fn unify<T: PartialEq, Iv, Se, E, O>(
    exp1: &T,
    exp2: &T,
    is_variable: Iv,
    structurally_equal: Se,
    explode: E,
    occurs: O,
) -> Result<Substitution<T>, String>
where
    T: Debug + Clone,
    Iv: Fn(&T) -> Option<String>,
    Se: Fn(&T, &T) -> bool,
    E: Fn(&T) -> Vec<T>,
    O: Fn(&T, &str) -> bool,
{
    return unify_with_base(
        exp1,
        exp2,
        &mut Substitution::empty(),
        is_variable,
        structurally_equal,
        explode,
        occurs,
    );
}

/// Expression-agnostic Hindley-Milner style unification algorithm.
/// Takes 2 expressions in the grammar `T` and checks if `exp1` ≐ `exp2`
/// returning the mgu satisfying unification. It also takes 4 functional arguments
/// needed to implement the recursive algorithm. Implementation is tail-recursive.
///
/// This is a variant of `unify` that takes a base substitution to include and start
/// building the MGU from.
///
/// # Function arguments requirements
///
/// * `is_variable` - Checks if an expression is a variable returning `Some` of the name, `None` otherwise
/// * `structurally_equal` - Returns `true` if two expressions are structurally equal, `false` otherwise
/// * `explode` - Returns a vector of the subcomponents of the expression to recur on in the unification algorithm (e.g., for a function application, it would return the arguments)
/// * `occurs` - Returns `true` if a variable occurs in an expression, `false` otherwise
///
/// # Returns
///
/// * `Result<Substitution<T>, String>` - The MGU if unification succeeds or an error message if unification fails.
pub fn unify_with_base<T: PartialEq, Iv, Se, E, O>(
    exp1: &T,
    exp2: &T,
    mgu: &mut Substitution<T>,
    is_variable: Iv,
    structurally_equal: Se,
    explode: E,
    occurs: O,
) -> Result<Substitution<T>, String>
where
    T: Debug + Clone,
    Iv: Fn(&T) -> Option<String>,
    Se: Fn(&T, &T) -> bool,
    E: Fn(&T) -> Vec<T>,
    O: Fn(&T, &str) -> bool,
{
    return solver(
        mgu,
        VecDeque::from(vec![(exp1.clone(), exp2.clone())]),
        is_variable,
        structurally_equal,
        explode,
        occurs,
    );
}

fn solver<T: PartialEq, Iv, Se, E, O>(
    mgu: &mut Substitution<T>,
    mut constraints: VecDeque<(T, T)>,
    is_variable: Iv,
    structurally_equal: Se,
    explode: E,
    occurs: O,
) -> Result<Substitution<T>, String>
where
    T: Debug + Clone,
    Iv: Fn(&T) -> Option<String>,
    Se: Fn(&T, &T) -> bool,
    E: Fn(&T) -> Vec<T>,
    O: Fn(&T, &str) -> bool,
{
    if let Some((exp1, exp2)) = constraints.pop_front() {
        // produce substitution v1 -> e2
        if let Some(var_name) = is_variable(&exp1) {
            mgu.add_substitution(&var_name, &exp2, &occurs, &is_variable)?;
            solver(
                mgu,
                constraints,
                is_variable,
                structurally_equal,
                explode,
                occurs,
            )
        }
        // produce substitution v2 -> e1
        else if let Some(var_name) = is_variable(&exp2) {
            mgu.add_substitution(&var_name, &exp1, &occurs, &is_variable)?;
            solver(
                mgu,
                constraints,
                is_variable,
                structurally_equal,
                explode,
                occurs,
            )
        }
        // recur if structurally equal or fail
        else if structurally_equal(&exp1, &exp2) {
            let sub1 = explode(&exp1);
            let sub2 = explode(&exp2);
            if sub1.len() != sub2.len() {
                return Err(format!(
                    "Unification failed on unexpected behaviour: expressions {:?} and {:?} seemingly structurally equal, but exploded in vectors of different lengths {:?} and {:?}",
                    exp1, exp2, sub1, sub2
                ));
            }

            for (s, t) in sub1.into_iter().zip(sub2.into_iter()) {
                constraints.push_back((s, t));
            }
            solver(
                mgu,
                constraints,
                is_variable,
                structurally_equal,
                explode,
                occurs,
            )
        } else {
            Err(format!(
                "Unification failed: {:?} and {:?} do not unify",
                exp1, exp2
            ))
        }
    }
    // no more constraints to solve, return the mgu built
    else {
        Ok(mgu.to_owned())
    }
}
