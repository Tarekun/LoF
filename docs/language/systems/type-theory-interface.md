# Type Theory Interface

`language/src/type_theory/interface.rs` defines the trait hierarchy that all type systems must implement. Adding a new type system means implementing these traits on a new unit struct.

All fallible methods across these traits return `Result<_, LofError>` — `LofError` (`language/src/error.rs`) is a `thiserror`-based enum shared by the whole pipeline (parsing, elaboration, type checking, unification, evaluation), replacing what used to be plain `Result<_, String>`.

## `TypeTheory` (base trait)

Every type system begins here. Defines four associated types and the elaboration entry points.

```rust
pub trait TypeTheory {
    type Term: Debug + Clone + PartialEq;  // constructors for terms (computations)
    type Type: Debug + Clone + PartialEq;  // constructors for types/propositions
    type Stm: Debug + Clone;               // elaborated statements
    type Exp: Debug + Clone;               // expression — usually Term or Union<Term, Type>
}
```

Higher-order systems (like CIC) set `Term = Type = Exp` because types are first-class terms in dependent type theory. FOL keeps them separate.

**Required methods:**

| Method | Description |
|--------|-------------|
| `default_environment()` | Returns the initial `Environment<Self>` with built-in axioms |
| `base_term_equality(t1, t2) -> Result<(), LofError>` | Definitional equality check used by the commons library. `Ok(())` if equal, `Err` describing the mismatch otherwise |
| `base_type_equality(T1, T2) -> Result<(), LofError>` | Same, for types |
| `elaborate_expression(exp)` | Converts a generic `Expression` AST node to `Self::Exp` |
| `elaborate_statement(stm)` | Converts a generic `Statement` to a `Schedule<Self>` (may produce multiple nodes, e.g. an inductive type produces the type and all its constructors) |

**Provided methods** (have default implementations):

- `elaborate_node` — dispatches between expression and statement
- `elaborate_ast` — drives elaboration of a full `LofAst` into a `Schedule<Self>`

## `Kernel` (type checking)

```rust
pub trait Kernel: TypeTheory {
    fn type_check_term(term, env: &mut Environment<Self>) -> Result<Self::Type, LofError>;
    fn type_check_type(typee, env: &mut Environment<Self>) -> Result<Self::Type, LofError>;
    fn type_check_expression(exp, env: &mut Environment<Self>) -> Result<Self::Type, LofError>;
    fn type_check_stm(stm, env: &mut Environment<Self>) -> Result<Self::Type, LofError>;
}
```

`type_check_term` and `type_check_type` are conceptually separate in systems like FOL where terms and types live in different syntactic categories. In CIC they delegate to a shared `type_check_expression` since everything is a term.

## `Refiner` (metavariable unification)

Used by systems that support implicit arguments and metavariables (currently only CIC).

```rust
pub trait Refiner: TypeTheory {
    fn term_collect_unifications(term, env) -> Result<Vec<(Self::Exp, Self::Exp)>, LofError>;
    fn type_collect_unifications(typee, env) -> Result<Vec<(Self::Exp, Self::Exp)>, LofError>;
    fn solve_unifications(constraints: Vec<(Self::Exp, Self::Exp)>, env)
        -> Result<Substitution<Self::Exp>, LofError>;
    fn term_apply_unifier(term, substitution: &Substitution<Self::Exp>) -> Self::Term;
    fn type_apply_unifier(typee, substitution: &Substitution<Self::Exp>) -> Self::Type;
    fn terms_unify(env, t1, t2) -> Result<(), LofError>;
    fn types_unify(env, T1, T2) -> Result<(), LofError>;
}
```

Metavariables are represented as `Meta(i32)` in CIC terms. The flow is now explicit rather than environment-accumulated: `*_collect_unifications` walks a term/type and returns the `(Self::Exp, Self::Exp)` pairs that must unify (recursing into binders like `Abstraction`/`Product`/`Let`/`Match`), `solve_unifications` runs the constraint solver (`commons/unification.rs`'s `ucs`) over that list to produce a single `Substitution<Self::Exp>`, and `*_apply_unifier` substitutes the solution back into a term or type. `terms_unify`/`types_unify` return `Result<(), LofError>` (not `bool`) — the error variant carries the mismatch.

This replaced an earlier design where constraints accumulated as a side effect on the `Environment` (via a `constraints` field and `add_type_constraint`) and were resolved with a single `solve_unification` called with no explicit constraint argument; `Environment<T>` no longer carries any constraint state.

## `TypeInference`

A lighter variant of `Refiner` used for second-order unification of type schemas.

```rust
pub trait TypeInference: TypeTheory {
    fn type_unify(T1, T2) -> Result<Substitution<Self::Type>, LofError>;
    fn apply_so_substitution(typ, mgu) -> Self::Type;
}
```

## `Reducer` (evaluation)

```rust
pub trait Reducer: TypeTheory {
    fn substitute(term, var_name, body) -> Self::Term;
    fn normalize_term(env: &Environment<Self>, term) -> Self::Term;
    fn normalize_expression(env: &Environment<Self>, exp) -> Self::Exp;
    fn evaluate_statement(env: &mut Environment<Self>, stm) -> Result<(), LofError>;
}
```

`normalize_term`/`normalize_expression` take a shared `&Environment<Self>` — normalization only reads bindings (for δ-reduction), it never needs to mutate the environment. `normalize_term` reduces a term to its normal form (β/δ-normal in CIC). `evaluate_statement` does mutate the environment — adding definitions, verifying theorems, running automation — hence `&mut`.

## `Interactive` (tactic-based proving)

```rust
pub trait Interactive: TypeTheory {
    fn proof_hole() -> Self::Term;
    fn empty_target() -> Self::Type;
    fn type_check_tactic(env, tactic, target, partial_proof)
        -> Result<(Self::Term, Vec<Self::Type>), LofError>;
}
```

`type_check_tactic` takes the current proof goal (`target`) and the partial proof built so far, applies one tactic step, and returns the updated partial proof and the list of remaining subgoals.

## `Automatic` (saturation-based ATP)

```rust
pub trait Automatic: TypeTheory {
    fn compare_terms(t1, t2) -> Ordering;
    fn compare_types(T1, T2) -> Ordering;
    fn saturate(
        saturation_set: &Vec<Self::Type>,
        selection_fn: &SelectionFunctionSignature,
        giving_clause_fn: &GivingClauseSignature,
    ) -> Result<Substitution<Self::Term>, LofError>;
}
```

The ordering functions implement a simplification order (KBO in SUP's case). `saturate` runs the given-clause algorithm on a set of clauses, driven by the caller-supplied selection and giving-clause strategies (built from `config.selection_fn`/`config.giving_clause_fn`, see [configuration.md](../configuration.md)); `SelectionFunctionSignature`/`GivingClauseSignature` are function-pointer type aliases defined in `type_theory/sup/freedom.rs` but reused here since they're system-agnostic. On success it returns the accumulated MGU as a `Substitution<Self::Term>` (see [sup.md](sup.md) for how `solve`/`auto` use it to extract query-variable bindings).

## Trait Bounds Summary

| Entry point | Required bounds |
|-------------|-----------------|
| `parse_and_elaborate` | `TypeTheory + Kernel` |
| `type_check` | `TypeTheory + Kernel + Reducer` |
| `execute` | `TypeTheory + Kernel + Reducer` |
| `interactive` | `TypeTheory + Kernel + Reducer` |
| Theorem type checking | `+ Interactive` |
| Implicit argument resolution | `+ Refiner` |
| Automatic proving | `+ Automatic` |
