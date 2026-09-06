# Configuration

`language/src/config.rs`

LoF is configured via a YAML file, by default `./config.yml` relative to the working directory. A custom path can be specified with `--config <path>`.

## Config Struct

```rust
pub struct Config {
    pub system:           TypeSystem,
    pub log_level:        tracing::Level,
    pub selection_fn:     SelectionFunction,
    pub giving_clause_fn: GivingClause,
}
```

The active `Config` is also available anywhere in the program as a global singleton: `main.rs` calls `init_global_config(config.clone())` once at startup, and `config::global_config()` reads it back (initializing to `Config::default()` if it was never set, e.g. in unit tests).

## Options

### `system`

Which type system to use. Affects elaboration, type checking, and execution.

| Value | Type system |
|-------|-------------|
| `cic` | Calculus of Inductive Constructions (default) |
| `fol` | First-Order Logic |

```yaml
system: cic
```

### `log_level`

Controls tracing output verbosity.

| Value | Meaning |
|-------|---------|
| `info` | General progress messages (default) |
| `error` | Errors only |
| `debug` | Detailed per-node tracing |
| `trace` | Very verbose |
| `warn` | Warnings |

```yaml
log_level: debug
```

### `selection_fn`

Literal selection strategy within a clause, for the SUP saturation algorithm. Only relevant when using FOL's `auto`/`solve` commands.

| Value | Strategy |
|-------|----------|
| `maximal` | Select the KBO-maximal literal in each clause (default) |
| `all` | Select all literals |

```yaml
selection_fn: maximal
```

### `giving_clause_fn`

Giving-clause heuristic for the SUP saturation algorithm — which clause is picked next from the unprocessed set. Only relevant when using FOL's `auto`/`solve` commands. See [systems/sup.md](systems/sup.md) for what each strategy does.

| Value | Strategy |
|-------|----------|
| `fifo` | Take the first unprocessed clause |
| `weighted` | Take the clause with the fewest symbols (default) |

```yaml
giving_clause_fn: weighted
```

## Defaults

If no config file is present or a field is omitted, defaults are:
- `system: cic`
- `log_level: INFO`
- `selection_fn: maximal`
- `giving_clause_fn: weighted`

## Example Config

```yaml
system: fol
log_level: debug
selection_fn: all
giving_clause_fn: fifo
```
