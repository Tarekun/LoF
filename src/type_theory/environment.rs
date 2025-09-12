use crate::type_theory::interface::TypeTheory;
use std::collections::HashMap;

#[derive(Debug)]
pub struct Environment<T: TypeTheory> {
    /// var_name, variable type
    pub context: HashMap<String, Vec<T::Type>>,
    /// var_name, definition term, type
    pub deltas: HashMap<String, Vec<T::Term>>,
    /// pred_name, arg_types
    pub predicates: HashMap<String, Vec<T::Type>>,
    /// [exp1 = exp2]
    constraints: Vec<(T::Exp, T::Exp)>,
    next_index: i32,
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
            constraints: self.constraints.clone(),
            next_index: self.next_index,
        }
    }
}

//TODO check if this cloning is really necessary or there's better ways
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
            constraints: vec![],
            next_index: 0,
        }
    }

    fn context_stack(&mut self, name: &str) -> &mut Vec<T::Type> {
        self.context
            .entry(name.to_string())
            .or_insert_with(Vec::new)
    }
    fn substitution_stack(&mut self, name: &str) -> &mut Vec<T::Term> {
        self.deltas.entry(name.to_string()).or_insert_with(Vec::new)
    }

    //######################### ENV MANIPULATION
    //
    /// Insert a new typed variable into the context
    pub fn add_to_context(&mut self, name: &str, typee: &T::Type) {
        let context_stack = self.context_stack(name);
        context_stack.push(typee.to_owned());
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

    pub fn add_constraint(&mut self, left: &T::Exp, right: &T::Exp) {
        self.constraints.push((left.clone(), right.clone()));
    }

    pub fn add_predicate(&mut self, name: &str, arg_types: &Vec<T::Type>) {
        self.predicates
            .insert(name.to_string(), arg_types.to_owned());
    }

    fn remove_substitution(&mut self, name: &str) {
        let definition_stack = self.substitution_stack(name);
        definition_stack.pop();
        if definition_stack.len() == 0 {
            self.deltas.remove(name);
        }
    }

    /// Remove a variable from the context
    fn remove_from_context(&mut self, name: &str) {
        let context_stack = self.context_stack(name);
        context_stack.pop();
        if context_stack.len() == 0 {
            self.context.remove(name);
        }
    }

    /// Returns a fresh meta variable index
    pub fn fresh_meta(&mut self) -> i32 {
        self.next_index += 1;
        return self.next_index - 1;
    }
    //
    //######################### ENV MANIPULATION

    //######################### LOCAL ENV UTILS
    //
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

    /// Runs a callable under a local environment which is a rollbackable copy
    /// of `self` that can be mutated without staining the original environment
    pub fn with_rollback<F: FnOnce(&mut Self) -> R, R>(
        &mut self,
        callable: F,
    ) -> R {
        let mut cloned = self.clone();
        let result = callable(&mut cloned);

        result
    }

    /// Runs a callable under a local environment which is a rollbackable copy
    /// of `self` that can be mutated without staining the original environment.
    /// Keeps meta variable constraints produced
    pub fn with_rollback_keep_meta<F: FnOnce(&mut Self) -> R, R>(
        &mut self,
        callable: F,
    ) -> R {
        let mut cloned = self.clone();
        let result = callable(&mut cloned);
        self.constraints = cloned.constraints;

        result
    }
    //
    //######################### LOCAL ENV UTILS

    //######################### VARIABLE LOOKUPS
    //
    pub fn get_from_context(&self, name: &str) -> Option<(String, T::Type)> {
        self.context.get(name).and_then(|context_stack| {
            context_stack
                .last()
                .map(|type_| (name.to_string(), type_.clone()))
        })
    }

    pub fn get_from_deltas(&self, name: &str) -> Option<(String, T::Term)> {
        self.deltas.get(name).and_then(|definition_stack| {
            definition_stack
                .last()
                .map(|type_| (name.to_string(), type_.clone()))
        })
    }

    pub fn get_predicate(&self, type_name: &str) -> Option<Vec<T::Type>> {
        self.predicates
            .get(type_name)
            .map(|arg_types| arg_types.to_owned())
    }

    pub fn get_constraints(&self) -> Vec<(T::Exp, T::Exp)> {
        self.constraints.clone()
    }

    pub fn is_var_bound(&self, var_name: &str) -> bool {
        match self.get_from_context(var_name) {
            Some(_) => true,
            None => match self.get_from_deltas(var_name) {
                Some(_) => true,
                None => false,
            },
        }
    }

    pub fn get_variable_type(&self, var_name: &str) -> Option<T::Type> {
        match self.get_from_context(var_name) {
            Some((_, var_type)) => Some(var_type.clone()),
            None => None,
        }
    }
    //
    //######################### VARIABLE LOOKUPS
}

#[cfg(test)]
mod unit_tests {
    use crate::type_theory::{
        cic::cic::{
            Cic,
            CicTerm::{Sort, Variable},
            GLOBAL_INDEX,
        },
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
}
