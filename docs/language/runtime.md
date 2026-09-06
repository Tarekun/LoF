# Runtime

`language/src/runtime/`

The runtime module contains the execution engine and all entry points into the system.

## `program.rs`

### `ProgramNode<Exp, Stm>`

A tagged union representing one item in the execution queue:

```rust
pub enum ProgramNode<Exp, Stm> {
    OfExp(Exp),
    OfStm(Stm),
}
```

### `Schedule<T>`

An ordered queue of `ProgramNode`s backed by a `VecDeque`. Produced by elaboration and consumed sequentially by type checking and execution.

Key methods:

| Method | Description |
|--------|-------------|
| `new()` | Empty schedule |
| `singleton_stm(stm)` | Schedule with one statement |
| `add_statement(stm)` | Append a statement node |
| `add_expression(exp)` | Append an expression node |
| `extend(other)` | Append all nodes from another schedule |
| `iter()` | Iterate over all nodes in order |
| `peek_first()` / `peek_latest()` | Inspect without consuming |

Order is significant: a statement that defines a function must precede statements that use it, because type checking updates the environment as it goes.

### `Program<T>`

Wraps a `Schedule<T>` and an `Environment<T>`. After type checking, a `Program` is created and `execute()` is called to drain the schedule:

```rust
impl Program<T> where T: TypeTheory + Reducer {
    pub fn execute_expression(&mut self, exp: &T::Exp) -> Result<T::Exp, LofError> {
        Ok(T::normalize_expression(&self.environment, exp))
    }

    pub fn execute_statement(&mut self, stm: &T::Stm) -> Result<(), LofError> {
        T::evaluate_statement(&mut self.environment, stm)
    }

    pub fn execute(&mut self) -> Result<(), LofError> {
        for node in nodes {
            match node {
                OfExp(term) => { self.execute_expression(&term)?; }
                OfStm(stm) => { self.execute_statement(&stm)?; }
            }
        }
        Ok(())
    }
}
```

Note `normalize_expression` takes `&self.environment` (a shared reference), not `&mut` — normalization no longer needs to mutate the environment.

The `interactive` mode creates a `Program` without a pre-built schedule and processes nodes one at a time as they arrive from stdin.

## `entrypoints.rs`

All fallible entry points return `Result<_, LofError>` (see `language/src/error.rs` for the shared error type used across parsing, elaboration, type checking, and evaluation).

### `parse_only`

```rust
pub fn parse_only(config: &Config, workspace: &str) -> Result<LofAst, LofError>
```

Constructs a `LofParser` and calls `parse_workspace`. Returns the `LofAst` root node.

### `parse_and_elaborate<T>`

```rust
pub fn parse_and_elaborate<T: TypeTheory + Kernel>(
    config: &Config, workspace: &str
) -> Result<Schedule<T>, LofError>
```

Calls `parse_only` then `T::elaborate_ast`. Returns the elaborated `Schedule<T>`.

### `type_check<T>`

```rust
pub fn type_check<T: TypeTheory + Kernel + Reducer>(
    config: &Config, workspace: &str
) -> Result<Schedule<T>, LofError>
```

Calls `parse_and_elaborate`, then iterates the schedule in order. For each node:
- `OfExp` → `T::type_check_expression`
- `OfStm` → `T::type_check_stm`

Collects all errors before returning (bundled into a single `LofError::Aggregate`), so the user sees all type errors at once. Returns the schedule unchanged if successful (ready to pass to `execute`).

### `execute<T>`

```rust
pub fn execute<T: TypeTheory + Kernel + Reducer>(
    config: &Config, workspace: &str
) -> Result<(), LofError>
```

Calls `type_check`, wraps the result in a `Program`, and calls `program.execute()`.

### `interactive<T>`

```rust
pub fn interactive<T: TypeTheory + Kernel + Reducer>(
    config: &Config, workspace: &str
) -> Result<(), LofError>
```

REPL loop:
1. Print `> ` prompt
2. Read a line (with `\` line continuation support)
3. Parse one node
4. Elaborate the node
5. Type check it against the current environment
6. If expression: normalize and print the result
7. If statement: evaluate and update the environment
8. Loop

Errors are printed and the loop continues rather than aborting.

## `EntryPoint` Enum

```rust
pub enum EntryPoint {
    Execute,
    TypeCheck,
    Elaborate,
    ParseOnly,
    Help(Vec<String>),
    Interactive,
}
```

`Help` now carries the subcommand path (e.g. `["tactics", "intro"]` for `lof help tactics intro`), forwarded to `help()`. Used in `main.rs` to dispatch to the correct function.

## CLI

Command-line dispatch is split across two files:

- `language/src/cli.rs` contains only `get_flag_value`, a small helper for reading `--flag <value>` pairs out of `argv`.
- `language/src/main.rs` does the actual work: `determine_entrypoint` maps `argv[1]` to an `EntryPoint`, then `run_with_theory::<T>` matches on it and calls the corresponding function in `entrypoints.rs`. The type parameter `T` (`Cic` or `Fol`) is selected by matching on `config.system` once, at the top of `main()`.

Usage:

```
lof <operation> <workspace> [--config <path>]
```

| Operation | Entry point |
|-----------|-------------|
| `run` | `execute` |
| `check` | `type_check` |
| `parse` | `parse_only` |
| `elaborate` | `parse_and_elaborate` |
| `interactive` | `interactive` |
| `help [subcommand...]` | `help(args)` |
| *(no operation given)* | `interactive` |
| *(unrecognized operation)* | `help([])` |

`--config <path>` overrides the default `./config.yml`.

### `help`

`help(args: Vec<String>)` in `entrypoints.rs` is a small documentation browser, not just a usage banner. With no subcommand it prints the generic usage message; with a subcommand it dispatches to a dedicated section:

| Subcommand | Shows |
|------------|-------|
| `help` | This help message itself |
| `systems` | The type systems supported (`cic`, `fol`, and the `sup` backend) and how to select one via `config.yml` |
| `tactics [name]` | The list of tactics, or a detailed explanation of one tactic (`intro`, `exact`, `apply`) |
| `run` | Details on how the `run` operation resolves a workspace path |

Unrecognized subcommands print a pointer to `lof help help`.
