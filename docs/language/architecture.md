# Architecture and Data Flow

## Pipeline

```
Source files (.lof)
      │
      ▼
  LofParser::parse_workspace()
      │  nom-based parser
      ▼
  LofAst  (system-agnostic)
      │  Statement | Expression | Tactic
      ▼
  T::elaborate_ast()
      │  maps generic AST nodes to T::Stm / T::Exp
      ▼
  Schedule<T>  (queue of ProgramNode<T::Exp, T::Stm>)
      │
      ├──▶ T::type_check_expression() / T::type_check_stm()
      │        updates Environment<T>
      │
      └──▶ T::evaluate_statement() / T::normalize_expression()
               final execution
```

## Key Types

### `LofAst`

The output of parsing. Contains only generic, system-neutral nodes:

```
LofAst
  ├── Stm(Statement)   — declarations and commands
  └── Exp(Expression)  — expressions and types
```

The `Statement` and `Expression` enums are defined in `parser/api.rs` and carry no type-theory-specific information.

### `Schedule<T>`

A `VecDeque`-backed queue of `ProgramNode<T::Exp, T::Stm>`. Produced by elaboration and consumed by type checking and execution sequentially. The queue preserves source order, which matters because statements can depend on earlier ones.

### `Program<T>`

Wraps a `Schedule<T>` and an `Environment<T>`. The `execute()` method drains the schedule, calling `evaluate_statement` or `normalize_expression` on each node.

### `Environment<T>`

The shared mutable state threaded through all phases. See [environment.md](environment.md).

## Generic Dispatch

The entire pipeline is generic over a type `T` that implements the relevant traits from `type_theory/interface.rs`. The entry points in `runtime/entrypoints.rs` are monomorphized at the call site, after the config has determined which type system to use:

```rust
// from main.rs (simplified)
match config.system {
    TypeSystem::Cic => run_with_theory::<Cic>(config, &filepath, entrypoint),
    TypeSystem::Fol => run_with_theory::<Fol>(config, &filepath, entrypoint),
}
```

`cli.rs` itself only contains `get_flag_value`, a small helper for reading `--flag <value>` pairs from `argv`; argument-to-entrypoint dispatch (`determine_entrypoint`, `run_with_theory`, the match above) lives in `main.rs`.

This means no dynamic dispatch is needed inside the pipeline. Each type system compiles to its own specialised code path.

## Entry Points

All entry points are in `runtime/entrypoints.rs`. Each builds on the previous one:

| Function | Does |
|----------|------|
| `parse_only` | Parses files, returns `LofAst` |
| `parse_and_elaborate` | Parse + elaborate to `Schedule<T>` |
| `type_check` | Parse + elaborate + type check |
| `execute` | Parse + elaborate + type check + run |
| `interactive` | REPL loop — parses and executes one node at a time |

## Commons Layer

`type_theory/commons/` contains algorithms that are genuinely shared across type systems. These are generic functions parameterized by the `TypeTheory` trait bounds, not duplicated per-system:

- `type_check.rs` — `type_check_variable`, `type_check_abstraction` (plus the inference-aware variant `i_type_check_abstraction`), `type_check_application` (plus `i_type_check_application`), `type_check_fo_universal`, `type_check_let`, `type_check_global`, `type_check_function`, `type_check_axiom`, `type_check_auto`, `type_check_interactive_proof`, and theorem checking split into `eq_type_check_theorem` (equality-based, no `Refiner` needed) and `u_type_check_theorem` (unification-based, requires `Refiner`), sharing a private `type_check_theorem_base`
- `evaluation.rs` — `generic_term_normalization`, reduction helpers `reduce_variable`/`reduce_application`/`reduce_let`, plus `evaluate_global`, `evaluate_fun`, `evaluate_axiom`, `evaluate_theorem`, `evaluate_auto`, `evaluate_solve`
- `unification.rs` — Hindley-Milner unification over `Substitution<T>`: `unify`, `unify_with_base` (unifies against a base substitution), and `ucs` (the recursive unification constraint solver both build on)
- `elaboration.rs` — helpers for elaborating file roots, directory roots, and tactic lists
- `utils.rs` — `generic_multiarg_fun_type`, `wrap_term`, `wrap_type`, `eta_expand`

See [systems/commons.md](systems/commons.md) for the full breakdown of each function.
