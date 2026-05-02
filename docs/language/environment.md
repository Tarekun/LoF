# Environment

`language/src/type_theory/environment.rs`

The `Environment<T>` struct is the shared mutable state threaded through elaboration, type checking, and execution. It is generic over a type theory `T: TypeTheory`.

## Fields

```rust
pub struct Environment<T: TypeTheory> {
    pub context:           HashMap<String, Vec<T::Type>>,
    pub deltas:            HashMap<String, Vec<T::Term>>,
    pub predicates:        HashMap<String, Vec<T::Type>>,
    pub constructor_store: HashMap<String, Vec<(String, T::Type)>>,
}
```

### `context`

Maps variable names to their types (`Γ` in type theory notation). Each entry is a stack (`Vec`) rather than a single value, which enables lexical scoping: pushing a new type for a name shadows the previous one, and popping restores it. This is what makes `with_local_assumption` safe — it pushes on entry and pops on exit.

### `deltas`

Maps variable names to their definitions (`Δ` in reduction rules). Also stack-based for the same reason. Used for δ-reduction: when a variable's name appears during normalization, the engine looks it up here to get the substitutable body.

A variable can have both a context entry (its type) and a delta entry (its definition). Globally defined functions and `let` bindings appear in both; axioms appear only in context.

### `predicates`

Maps predicate symbol names to their argument type lists. Used by SUP and FOL to validate predicate applications.

### `constructor_store`

Maps an inductive type name to its list of `(constructor_name, constructor_type)` pairs. Populated when an inductive type is checked, and used to look up the constructors available for a given type (e.g. for exhaustiveness/pattern checks in `match`).

Note: metavariable unification constraints are no longer accumulated on the environment. The `Refiner` trait now threads them explicitly as a `Vec<(Exp, Exp)>` collected by `term_collect_unifications`/`type_collect_unifications` and consumed directly by `solve_unifications` — see [systems/type-theory-interface.md](systems/type-theory-interface.md).

## Core Operations

### Adding bindings

```rust
env.add_to_context(name, &typee);          // adds to context only
env.add_substitution(name, &term);          // adds to deltas only
env.add_substitution_with_type(name, &term, &typee); // adds to both
env.add_constructor_store(name, constructors); // registers an inductive type's constructors
```

### Looking up bindings

```rust
env.get_from_context(name)        // -> Option<(String, T::Type)>
env.get_from_deltas(name)         // -> Option<(String, T::Term)>
env.get_variable_type(name)       // -> Option<T::Type>
env.is_var_bound(name)            // true if in context OR deltas
env.get_context()                 // flattened snapshot: HashMap<String, T::Type>
env.get_deltas()                  // flattened snapshot: HashMap<String, T::Term>
env.get_constants()               // set of all bound names
env.get_constructors_for(name)    // -> Option<HashSet<String>>, constructor names for an inductive type
```

## Scoped Operations

These are the preferred way to introduce local variables during type checking because they guarantee cleanup even if the closure panics.

### `with_local_assumption`

Temporarily adds a variable to the context for the duration of a closure:

```rust
env.with_local_assumption("x", &x_type, |env| {
    // x:T is in scope here
    T::type_check_term(body, env)
})
// x is removed here
```

Used when type checking lambda abstractions and universal quantifiers.

### `with_local_substitution`

Temporarily adds a variable to both context and deltas (for `let` bindings):

```rust
env.with_local_substitution("x", &term, &Some(x_type), |env| {
    T::type_check_term(scope, env)
})
```

### Plural variants

`with_local_assumptions` and `with_local_substitutions` accept `&[(name, type)]` and `&[(name, term, Option<type>)]` slices, adding and removing them all atomically via recursion.

### `with_rollback`

Runs a closure on a cloned copy of the environment. Any mutations made inside are discarded when the closure returns — the original environment is unchanged. Takes `&self` (not `&mut self`): it only needs to clone, never to mutate the caller's environment.

```rust
env.with_rollback(|sandbox| {
    // mutations here don't affect env
    T::terms_unify(sandbox, t1, t2)
})
```
