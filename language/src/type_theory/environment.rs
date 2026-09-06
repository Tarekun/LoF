use crate::type_theory::commons::transport::EquivConfig;
use crate::type_theory::interface::TypeTheory;
use std::collections::{HashMap, HashSet};
use std::fmt::Debug;

#[derive(Debug)]
pub struct Environment<T: TypeTheory> {
    /// var_name, variable type
    pub context: HashMap<String, Vec<T::Type>>,
    /// var_name, definition term, type
    pub deltas: HashMap<String, Vec<T::Term>>,
    /// pred_name, arg_types
    pub predicates: HashMap<String, Vec<T::Type>>,
    /// type_name, constructors_vec
    pub constructor_store: HashMap<String, Vec<(String, T::Type)>>,
    /// theorem_name, proof term. Unlike `deltas`, this is never consulted
    /// by δ-reduction or unification - theorems stay opaque for reduction,
    /// exactly like an axiom. It exists purely so a tool (eg `transport`)
    /// can retrieve an already-checked theorem's witness term by name.
    pub theorem_proofs: HashMap<String, Vec<T::Term>>,
    /// equivalence_name, registered configuration. Populated by the
    /// `equivalence` statement, consulted by `transport`.
    pub equivalences: HashMap<String, EquivConfig<T>>,
    /// type_name, number of left parameters (the inductive's own params,
    /// excluding right/index parameters) - needed to locate the motive
    /// and per-constructor cases inside an `e_<type_name>` application by
    /// position, so that application can be ι-reduced when its final
    /// (instance) argument is a concrete constructor.
    pub inductive_param_counts: HashMap<String, usize>,
}
impl<T: TypeTheory> Clone for Environment<T>
where
    T::Term: Clone,
    T::Type: Clone,
{
    fn clone(&self) -> Self {
        Environment {
            context: self.context.clone(),
            deltas: self.deltas.clone(),
            predicates: self.predicates.clone(),
            constructor_store: self.constructor_store.clone(),
            theorem_proofs: self.theorem_proofs.clone(),
            equivalences: self.equivalences.clone(),
            inductive_param_counts: self.inductive_param_counts.clone(),
        }
    }
}

// context handling
impl<T: TypeTheory> Environment<T> {
    fn context_stack(&mut self, name: &str) -> &mut Vec<T::Type> {
        self.context
            .entry(name.to_string())
            .or_insert_with(Vec::new)
    }

    /// Insert a new typed variable into the context
    pub fn add_to_context(&mut self, name: &str, typee: &T::Type) {
        let context_stack = self.context_stack(name);
        context_stack.push(typee.to_owned());
    }

    /// Read the type of a variable. Returns the `Some(type)` if the name is found,
    /// `None` otherwise
    pub fn get_from_context(&self, name: &str) -> Option<(String, T::Type)> {
        self.context.get(name).and_then(|context_stack| {
            context_stack
                .last()
                .map(|type_| (name.to_string(), type_.clone()))
        })
    }

    /// Returns all var_name : VarType bindings in the context
    pub fn get_context(&self) -> HashMap<String, T::Type> {
        self.context
            .iter()
            .filter_map(|(name, stack)| {
                stack.last().map(|ty| (name.to_string(), ty.to_owned()))
            })
            .collect()
    }

    /// Remove a variable from the context
    fn remove_from_context(&mut self, name: &str) {
        let context_stack = self.context_stack(name);
        context_stack.pop();
        if context_stack.len() == 0 {
            self.context.remove(name);
        }
    }

    /// Add a local variable to the context, execute a closure, and then remove the variable
    pub fn with_local_assumption<F: FnOnce(&mut Self) -> R, R>(
        &mut self,
        name: &str,
        typee: &T::Type,
        callable: F,
    ) -> R {
        self.add_to_context(name, typee);
        let result = callable(self);
        self.remove_from_context(name);

        result
    }

    /// Add a list of local variables to the context, execute a closure, and then remove the variables
    pub fn with_local_assumptions<F: FnOnce(&mut Self) -> R, R>(
        &mut self,
        assumptions: &[(String, T::Type)],
        callable: F,
    ) -> R {
        if assumptions.is_empty() {
            callable(self)
        } else {
            let ((name, typee), rest) = assumptions.split_first().unwrap();
            self.add_to_context(name, typee);
            let result = self.with_local_assumptions(rest, callable);
            self.remove_from_context(name);

            result
        }
    }
}

// variables with reducable bodies
impl<T: TypeTheory> Environment<T> {
    fn substitution_stack(&mut self, name: &str) -> &mut Vec<T::Term> {
        self.deltas.entry(name.to_string()).or_insert_with(Vec::new)
    }

    pub fn add_substitution(&mut self, name: &str, term: &T::Term) {
        let definition_stack = self.substitution_stack(name);
        definition_stack.push(term.clone());
    }

    pub fn add_substitution_with_type(
        &mut self,
        name: &str,
        term: &T::Term,
        typee: &T::Type,
    ) {
        let definition_stack = self.substitution_stack(name);
        definition_stack.push(term.clone());
        self.add_to_context(name, typee);
    }

    pub fn get_from_deltas(&self, name: &str) -> Option<(String, T::Term)> {
        self.deltas.get(name).and_then(|definition_stack| {
            definition_stack
                .last()
                .map(|type_| (name.to_string(), type_.clone()))
        })
    }

    /// Returns all var_name := body subsitution in the environment
    pub fn get_deltas(&self) -> HashMap<String, T::Term> {
        self.deltas
            .iter()
            .filter_map(|(name, stack)| {
                stack.last().map(|term| (name.to_string(), term.to_owned()))
            })
            .collect()
    }

    /// Add a local variable substitution (ie definition) to the deltas, execute a closure,
    /// and then remove the variable
    pub fn with_local_substitution<F: FnOnce(&mut Self) -> R, R>(
        &mut self,
        name: &str,
        term: &T::Term,
        typee: &Option<T::Type>,
        callable: F,
    ) -> R {
        self.add_substitution(name, term);
        if typee.is_some() {
            let typee = typee.as_ref().unwrap();
            self.add_to_context(name, typee);
        }

        let result = callable(self);

        self.remove_substitution(name);
        if typee.is_some() {
            self.remove_from_context(name);
        }

        result
    }

    /// Add a list of local variables to the context, execute a closure, and then remove the variables
    pub fn with_local_substitutions<F: FnOnce(&mut Self) -> R, R>(
        &mut self,
        substitutions: &[(String, T::Term, Option<T::Type>)],
        callable: F,
    ) -> R {
        if substitutions.is_empty() {
            callable(self)
        } else {
            let ((name, term, typee), rest) =
                substitutions.split_first().unwrap();
            self.add_substitution(name, term);
            if typee.is_some() {
                let typee = typee.as_ref().unwrap();
                self.add_to_context(name, typee);
            }

            let result = self.with_local_substitutions(rest, callable);

            self.remove_substitution(name);
            if typee.is_some() {
                self.remove_from_context(name);
            }

            result
        }
    }

    fn remove_substitution(&mut self, name: &str) {
        let definition_stack = self.substitution_stack(name);
        definition_stack.pop();
        if definition_stack.len() == 0 {
            self.deltas.remove(name);
        }
    }
}

// predicates
impl<T: TypeTheory> Environment<T> {
    pub fn add_predicate(&mut self, name: &str, arg_types: &Vec<T::Type>) {
        self.predicates
            .insert(name.to_string(), arg_types.to_owned());
    }

    pub fn get_predicate(&self, type_name: &str) -> Option<Vec<T::Type>> {
        self.predicates
            .get(type_name)
            .map(|arg_types| arg_types.to_owned())
    }
}

// constructor store
impl<T: TypeTheory> Environment<T> {
    pub fn add_constructor_store(
        &mut self,
        name: &str,
        typee: Vec<(String, T::Type)>,
    ) {
        self.constructor_store
            .insert(name.to_string(), typee.clone());
    }

    /// Reverse of `get_constructors_for`: which inductive type declares
    /// `constructor_name`. Used where a term's type has to be recovered
    /// from a constructor occurrence rather than inferred - notably by the
    /// reducer, which only holds `&Environment` and so cannot type check.
    pub fn constructor_type_of(&self, constructor_name: &str) -> Option<String> {
        self.constructor_store.iter().find_map(|(type_name, constructors)| {
            constructors
                .iter()
                .any(|(name, _)| name == constructor_name)
                .then(|| type_name.to_owned())
        })
    }

    pub fn get_constructors_for(&self, name: &str) -> Option<HashSet<String>> {
        match self.constructor_store.get(name) {
            None => None,
            Some(list) => {
                let res: HashSet<String> = list
                    .into_iter()
                    .map(|(constr_name, _)| constr_name.to_owned())
                    .collect();

                Some(res)
            }
        }
    }
}

// theorem proofs
impl<T: TypeTheory> Environment<T> {
    /// Records `theorem_name`'s proof term for later introspection (eg by
    /// `transport`). Does not affect δ-reduction/unification - a
    /// theorem's name still only carries its formula in `context`, exactly
    /// as before; this is a separate, read-only channel.
    pub fn add_theorem_proof(&mut self, theorem_name: &str, proof: &T::Term) {
        self.theorem_proofs
            .entry(theorem_name.to_string())
            .or_insert_with(Vec::new)
            .push(proof.to_owned());
    }

    pub fn get_theorem_proof(&self, theorem_name: &str) -> Option<T::Term> {
        self.theorem_proofs
            .get(theorem_name)
            .and_then(|stack| stack.last())
            .map(|proof| proof.to_owned())
    }
}

// type equivalences
impl<T: TypeTheory> Environment<T> {
    pub fn add_equivalence(&mut self, name: &str, config: EquivConfig<T>) {
        self.equivalences.insert(name.to_string(), config);
    }

    pub fn get_equivalence(&self, name: &str) -> Option<&EquivConfig<T>> {
        self.equivalences.get(name)
    }

    /// Mutable access to a registered equivalence, needed to grow
    /// `EquivConfig::lifted_names` as `transport` lifts more auxiliary
    /// `fun`/`global` definitions under it.
    pub fn get_equivalence_mut(
        &mut self,
        name: &str,
    ) -> Option<&mut EquivConfig<T>> {
        self.equivalences.get_mut(name)
    }
}

// inductive parameter counts (for eliminator ι-reduction)
impl<T: TypeTheory> Environment<T> {
    pub fn add_inductive_param_count(&mut self, type_name: &str, count: usize) {
        self.inductive_param_counts
            .insert(type_name.to_string(), count);
    }

    pub fn get_inductive_param_count(&self, type_name: &str) -> Option<usize> {
        self.inductive_param_counts.get(type_name).copied()
    }
}

// other utilities
impl<T: TypeTheory> Environment<T> {
    pub fn with_defaults(
        axioms: Vec<(&str, &T::Type)>,
        deltas: Vec<(&str, &T::Term, &Option<T::Type>)>,
        predicates: Vec<(&str, &Vec<T::Type>)>,
    ) -> Self {
        let mut context_map = HashMap::new();
        let mut deltas_map = HashMap::new();
        let mut predicates_map = HashMap::new();

        for (name, term) in axioms {
            context_map.insert(name.to_string(), vec![term.clone()]);
        }
        for (name, term, typee) in deltas {
            deltas_map.insert(name.to_string(), vec![term.clone()]);
            if let Some(typee) = typee.as_ref() {
                context_map.insert(name.to_string(), vec![typee.clone()]);
            }
        }
        for (name, arg_types) in predicates {
            predicates_map.insert(name.to_string(), arg_types.clone());
        }

        Self {
            context: context_map,
            deltas: deltas_map,
            predicates: predicates_map,
            constructor_store: HashMap::new(),
            theorem_proofs: HashMap::new(),
            equivalences: HashMap::new(),
            inductive_param_counts: HashMap::new(),
        }
    }

    /// Returns true if `var_name` is present in the context (bound)
    /// false otherwise (fresh)
    pub fn is_var_bound(&self, var_name: &str) -> bool {
        match self.get_from_context(var_name) {
            Some(_) => true,
            None => match self.get_from_deltas(var_name) {
                Some(_) => true,
                None => false,
            },
        }
    }

    /// Lookup the type of a variable. If x:T is present in the context or was
    /// registered as a typed substitution x:T=t it returns `Some(T)`,
    /// None otherwise
    pub fn get_variable_type(&self, var_name: &str) -> Option<T::Type> {
        match self.get_from_context(var_name) {
            Some((_, var_type)) => Some(var_type.clone()),
            None => None,
        }
    }

    // TODO this needs to be checked, its used only in the saturation algorithm
    // and i think it needs something like get_predicates instead
    /// Returns the set of constant symbols contained in the context
    pub fn get_constants(&self) -> HashSet<String> {
        self.get_context().into_keys().collect()
    }

    /// Runs a callable under a local environment which is a rollbackable copy
    /// of `self` that can be mutated without staining the original environment
    pub fn with_rollback<F: FnOnce(&mut Self) -> R, R>(
        &self,
        callable: F,
    ) -> R {
        let mut cloned = self.clone();
        let result = callable(&mut cloned);

        result
    }
}

#[cfg(test)]
mod unit_tests {
    use std::collections::HashMap;

    use crate::type_theory::{
        cic::cic::{
            Cic,
            CicTerm::{self, Sort, Variable},
            GLOBAL_INDEX,
        },
        environment::Environment,
        interface::TypeTheory,
    };

    #[test]
    fn test_context_manipulation() {
        let mut test_env = Cic::default_environment();
        let test_var_name = "test";
        let first_type = Sort("TYPE".to_string());
        let second_type = Sort("PROP".to_string());

        test_env.add_to_context(test_var_name, &first_type);
        assert_eq!(
            Some((test_var_name.to_string(), first_type.clone())),
            test_env.get_from_context(test_var_name),
            "Environment didnt store context assumption correctly"
        );

        test_env.add_to_context(test_var_name, &second_type);
        assert_eq!(
            Some((test_var_name.to_string(), second_type)),
            test_env.get_from_context(test_var_name),
            "Environment didnt override the same variable name"
        );

        test_env.remove_from_context(test_var_name);
        assert_eq!(
            Some((test_var_name.to_string(), first_type)),
            test_env.get_from_context(test_var_name),
            "Environment didnt restore previous variable type after second name was freed"
        );
    }

    #[test]
    fn test_delta_manipulation() {
        let mut test_env = Cic::default_environment();
        let test_var_name = "test";
        let first_body = Sort("TYPE".to_string());
        let second_body = Sort("PROP".to_string());

        test_env.add_substitution(test_var_name, &first_body);
        assert_eq!(
            Some((test_var_name.to_string(), first_body.clone())),
            test_env.get_from_deltas(test_var_name),
            "Environment didnt store variable substitution correctly"
        );

        test_env.add_substitution(test_var_name, &second_body);
        assert_eq!(
            Some((test_var_name.to_string(), second_body)),
            test_env.get_from_deltas(test_var_name),
            "Environment didnt override the same variable name"
        );

        test_env.remove_substitution(test_var_name);
        assert_eq!(
            Some((test_var_name.to_string(), first_body)),
            test_env.get_from_deltas(test_var_name),
            "Environment didnt restore previous variable type after second name was freed"
        );
    }

    #[test]
    fn test_boundness() {
        let mut test_env = Cic::default_environment();

        assert!(
            !test_env.is_var_bound("unbound_var_name"),
            "Environment signals unbound variable as bound"
        );

        test_env.add_to_context("a", &Variable("a".to_string(), GLOBAL_INDEX));
        assert!(
            test_env.is_var_bound("a"),
            "Environment signals bound variable as unbound"
        );

        test_env
            .add_substitution("b", &Variable("a".to_string(), GLOBAL_INDEX));
        assert!(
            test_env.is_var_bound("b"),
            "Environment signals bound variable as unbound if it was introduced as a substitution"
        );
    }

    #[test]
    fn test_with_local_assumption() {
        let mut test_env = Cic::default_environment();
        let var_name = "local_var";
        let var_type = Sort("TYPE".to_string());

        test_env.with_local_assumption(var_name, &var_type, |env| {
            assert_eq!(
                Some((var_name.to_string(), var_type.clone())),
                env.get_from_context(var_name),
                "Local assumption was not added to the context"
            );
        });
        assert_eq!(
            None,
            test_env.get_from_context(var_name),
            "Local assumption was not removed from the context after closure execution"
        );
    }

    #[test]
    fn test_with_local_assumptions() {
        let mut test_env = Cic::default_environment();
        let typed_variables = vec![
            ("var1".to_string(), Sort("TYPE".to_string())),
            ("var2".to_string(), Sort("PROP".to_string())),
        ];

        test_env.with_local_assumptions(&typed_variables, |env| {
            for (name, typee) in typed_variables.iter() {
                assert_eq!(
                    Some((name.to_string(), typee.clone())),
                    env.get_from_context(name),
                    "Local assumption was not added to the context"
                );
            }
        });
        for (name, _) in typed_variables.iter() {
            assert_eq!(
                None,
                test_env.get_from_context(name),
                "Local assumption was not removed from the context after closure execution"
            );
        }
    }

    #[test]
    fn test_with_local_substitution() {
        let mut test_env = Cic::default_environment();
        let var_name = "local_var";
        let substitution_term = Variable(var_name.to_string(), GLOBAL_INDEX);

        test_env.with_local_substitution(
            var_name,
            &substitution_term,
            &None,
            |env| {
                assert_eq!(
                    Some((var_name.to_string(), substitution_term.clone())),
                    env.get_from_deltas(var_name),
                    "Local substitution was not added to the deltas"
                );
            },
        );
        assert_eq!(
            None,
            test_env.get_from_deltas(var_name),
            "Local substitution was not removed from the deltas after closure execution"
        );
    }

    #[test]
    fn test_with_local_substitutions() {
        let mut test_env = Cic::default_environment();
        let var_names_and_terms = vec![
            (
                "var1".to_string(),
                Variable("term1".to_string(), GLOBAL_INDEX),
                None,
            ),
            (
                "var2".to_string(),
                Variable("term2".to_string(), GLOBAL_INDEX),
                None,
            ),
        ];

        test_env.with_local_substitutions(&var_names_and_terms, |env| {
            for (name, term, _) in var_names_and_terms.iter() {
                assert_eq!(
                    Some((name.to_string(), term.clone())),
                    env.get_from_deltas(name),
                    "Local substitution was not added to the deltas"
                );
            }
        });
        for (name, _, _) in var_names_and_terms.iter() {
            assert_eq!(
                None,
                test_env.get_from_deltas(name),
                "Local substitution was not removed from the deltas after closure execution"
            );
        }
    }

    #[test]
    fn test_active_context_reading() {
        let mut test_env: Environment<Cic> =
            Environment::with_defaults(vec![], vec![], vec![]);
        let nat = CicTerm::Variable("Nat".to_string(), GLOBAL_INDEX);
        let boolean = CicTerm::Variable("Bool".to_string(), GLOBAL_INDEX);

        test_env.add_to_context("x", &nat);
        test_env.add_to_context("y", &boolean);
        assert_eq!(
            test_env.get_context(),
            HashMap::from([
                ("x".to_string(), nat.clone()),
                ("y".to_string(), boolean.clone())
            ]),
            "Environment::get_context is returning the proper context"
        );

        test_env.add_to_context("x", &boolean);
        assert_eq!(
            test_env.get_context(),
            HashMap::from([
                ("x".to_string(), boolean.clone()),
                ("y".to_string(), boolean.clone())
            ]),
            "Environment::get_context is returning the latest typing assinged to name 'x'"
        );

        test_env.add_to_context("z", &boolean);
        assert_eq!(
            test_env.get_context(),
            HashMap::from([
                ("x".to_string(), boolean.clone()),
                ("y".to_string(), boolean.clone()),
                ("z".to_string(), boolean.clone()),
            ]),
            "Environment::get_context doesnt behave properly after inclusion of new names"
        );
    }
}
