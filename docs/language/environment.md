# Environment

`language/src/type_theory/environment.rs`

The `Environment<T>` struct is the shared mutable state threaded through elaboration, type checking, and execution. It is generic over a type theory `T: TypeTheory`.

## Fields

```rust
pub struct Environment<T: TypeTheory> {
    context:          HashMap<String, Vec<T::Type>>,
    deltas:           HashMap<String, Vec<T::Term>>,
    predicates:       HashMap<String, Vec<T::Type>>,
    inductive_store:  HashMap<String, (Vec<(String, T::Type)>, usize)>,
    equivalences:      HashMap<String, EquivConfig<T>>,
    theorem_proofs:    HashMap<String, Vec<T::Term>>,
}
```

All fields are private. Nothing outside this module reaches into them directly - every read or write goes through one of the methods below, which is what keeps the invariants each map relies on (stack discipline on `context`/`deltas`, constructor order in `inductive_store`) from being violated by a call site that only meant to read one field.

### `context`

Maps variable names to their types (`Γ` in type theory notation). Each entry is a stack (`Vec`) rather than a single value, which enables lexical scoping: pushing a new type for a name shadows the previous one, and popping restores it. This is what makes `with_local_assumption` safe — it pushes on entry and pops on exit.

### `deltas`

Maps variable names to their definitions (`Δ` in reduction rules). Also stack-based for the same reason. Used for δ-reduction: when a variable's name appears during normalization, the engine looks it up here to get the substitutable body.

A variable can have both a context entry (its type) and a delta entry (its definition). Globally defined functions and `let` bindings appear in both; axioms *and checked theorems* appear in context alone - a theorem's proof term is deliberately **not** a delta (see `theorem_proofs` below).

### `predicates`

Maps predicate symbol names to their argument type lists. Used by SUP and FOL to validate predicate applications.

### `inductive_store`

Maps an inductive type name to its `(constructor_name, constructor_type)` list **in declaration order**, paired with the type's left-parameter count. Populated once, when the inductive is checked. The order matters beyond `get_constructors_for`'s exhaustiveness use: it's what lets an eliminator application line its per-constructor cases up positionally against the inductive's own constructors (see `get_inductive_constructors`, and [systems/transport.md](systems/transport.md), which relies on that alignment to repair a `dep_elim` application case by case). The param count is what lets a generated eliminator's motive/cases/instance be located by position inside an `e_<Type>` application.

### `equivalences`

Maps an equivalence name to its registered `EquivConfig` (`commons/transport.rs`): the forward/backward functions, section/retraction proofs, and the DepConstr/DepElim/Eta/Iota data. Populated by the `equivalence` statement, consulted by `transport` — see [systems/transport.md](systems/transport.md).

### `theorem_proofs`

Maps a theorem name to its proof term. Unlike `deltas` this is **never consulted by δ-reduction or unification** - a theorem stays opaque for reduction, exactly like an axiom, whether or not it happens to have a term-mode proof on file here. It exists purely so a tool can retrieve an already-checked theorem's witness by name, which is what [`transport`](systems/transport.md) needs in order to rewrite an existing proof.

This is a deliberate divergence from treating a theorem like an ordinary definition: a hand-derived `dep_elim` (see [systems/transport.md](systems/transport.md)) is typically itself a *theorem*, and the entire Iota mechanism exists because such a `dep_elim` has no computational behaviour of its own. Making theorem bodies δ-reduce would silently give some of them behaviour again - inconsistently, since it would only "work" where the theorem's own proof happens to bottom out in something reducible - which undermines the very distinction Iota is there to bridge. So the proof is kept retrievable by name without being substitutable.

Note: metavariable unification constraints are no longer accumulated on the environment. The `Refiner` trait now threads them explicitly as a `Vec<(Exp, Exp)>` collected by `term_collect_unifications`/`type_collect_unifications` and consumed directly by `solve_unifications` — see [systems/type-theory-interface.md](systems/type-theory-interface.md).

## Core Operations

### Adding bindings

```rust
env.add_to_context(name, &typee);          // adds to context only
env.add_substitution(name, &term);          // adds to deltas only
env.add_substitution_with_type(name, &term, &typee); // adds to both
env.add_to_inductive_store(name, constructors, left_param_count); // registers an inductive type
env.add_equivalence(name, config);         // registers an `equivalence` statement's configuration
env.add_theorem_proof(name, &proof);       // records a checked theorem's witness (not a delta)
```

### Looking up bindings

```rust
env.get_from_context(name)         // -> Option<(String, T::Type)>
env.get_from_deltas(name)          // -> Option<(String, T::Term)>
env.get_variable_type(name)        // -> Option<T::Type>
env.is_var_bound(name)             // true if in context OR deltas
env.get_context()                  // flattened snapshot: HashMap<String, T::Type>
env.get_deltas()                   // flattened snapshot: HashMap<String, T::Term>
env.get_constants()                // set of all bound names
env.get_constructors_for(name)     // -> Option<HashSet<String>>, constructor names for an inductive type
env.get_inductive_constructors(name) // -> Option<&Vec<(String, T::Type)>>, in declaration order
env.get_inductive_param_count(name)  // -> Option<usize>, the type's left-parameter count
env.get_equivalence(name)          // -> Option<&EquivConfig<T>>
env.get_equivalence_mut(name)      // -> Option<&mut EquivConfig<T>>, for growing `lifted_names`
env.get_theorem_proof(name)        // -> Option<T::Term>, a checked theorem's proof term
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
