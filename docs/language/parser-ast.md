# Parser and AST

`language/src/parser/`

The parser is built with [nom](https://docs.rs/nom) and produces a system-agnostic AST. It knows nothing about which type theory will be used — that is the elaboration phase's job.

Parser functions return `PResult<'a, T>`, a type alias defined in `api.rs`:

```rust
pub type PResult<'a, T> = nom::IResult<&'a str, T, LofError>;
```

`LofError` (`language/src/error.rs`) is a single `thiserror`-based enum shared by the whole pipeline — parsing, elaboration, type checking, unification, evaluation — not just the parser. Besides parse-specific variants (`Nom`, `IncompleteInput`, `ReservedKeyword`, `LeftoverInput`), it covers unbound names, type/arity mismatches, unification failures, occurs-check failures, I/O and config errors, and a couple of generic catch-alls (`Unsupported`, `Other`). Every `Result<_, String>` that used to appear across the codebase is now `Result<_, LofError>`. Notably, `parse_source_file` and `parse_workspace` used to panic on file-read or parse failure; they now return `Result<_, LofError>` like everything else.

## AST Nodes

### `Expression`

Expressions are terms or types that evaluate to something. They are used both as proof terms and as type annotations.

```rust
pub enum Expression {
    VarUse(String),
    /// \lambda var_name: var_type. body
    Abstraction(String, Box<Expression>, Box<Expression>),
    /// \Pi var_name: var_type. dependent_type
    TypeProduct(String, Box<Expression>, Box<Expression>),
    /// domain -> codomain  (non-dependent arrow)
    Arrow(Box<Expression>, Box<Expression>),
    /// f(arg1, arg2, …)  (multi-argument application, parenthesized & comma-separated)
    Application(Box<Expression>, Vec<Expression>),
    /// match term with | pat => body, …
    Match(Box<Expression>, Vec<(Expression, Expression)>),
    /// ?  (hole to be filled by type inference)
    Inferator(),
    /// (e1, e2, …)  conjunctive tuple
    Tuple(Vec<Expression>),
    /// e1 | e2 | …  disjunctive union
    Pipe(Vec<Expression>),
    /// let var_name : opt_type := body in scope
    Let(String, Box<Option<Expression>>, Box<Expression>, Box<Expression>),
}
```

`Arrow` is syntactic sugar for `TypeProduct` where the variable name is unused. During elaboration, CIC maps both to its `Product` constructor.

`Inferator` corresponds to the `?` wildcard, which the engine elaborates to a fresh metavariable. (`_` is not this wildcard — it is an ordinary identifier, commonly used as a bound variable name for a pattern component the branch ignores.)

`Application` is built by `parse_app` (`expressions.rs`) from a parenthesized, comma-separated argument list — `f(a, b, c)`. The old space-juxtaposition syntax (`f a b c` parsed as `((f a) b) c`) no longer parses at all. The argument list requires at least one argument (`separated_list1`); a trailing comma is allowed. This is uniform across the language: ordinary function calls, predicate/type applications (`le(z, n)`, `Eq(T, x, x)`, `And(P, Q)`), and constructor patterns inside `match` (`s(nn)`, `cons(h, l)`) all produce the same `Application` node. Arguments may themselves be nested applications or custom notations without extra parenthesization, since `argument_expression` now tries `parse_custom`/`parse_app` before falling back to a bare variable.

### `Statement`

Statements interact with the engine and modify the context.

```rust
pub enum Statement {
    Comment(),
    FileRoot(String, Vec<LofAst>),      // wraps all nodes from one file
    DirRoot(String, Vec<LofAst>),       // wraps all FileRoots from a directory
    EmptyRoot(Vec<LofAst>),
    Axiom(String, Box<Expression>),
    /// theorem_name, formula, proof (term or tactic list)
    Theorem(String, Expression, Union<Expression, Vec<Tactic<Expression>>>),
    /// var_name, opt_type, body
    Global(String, Option<Expression>, Expression),
    /// fun_name, args, return_type, body, is_recursive
    Fun(String, Vec<(String, Expression)>, Box<Expression>, Box<Expression>, bool),
    /// type_name, params, arity, constructors
    Inductive(String, Vec<(String, Expression)>, Box<Expression>, Vec<(String, Expression)>),
    Auto(Expression),
    Solve(Vec<Expression>),
    HClause(Expression, Vec<Expression>),
}
```

`FileRoot` and `DirRoot` are structural wrappers created by the parser to represent the file system hierarchy. They carry no semantic content beyond grouping.

`Fun` has an `is_rec` flag that is set when the `rec` keyword appears. Recursive functions receive themselves as an additional local assumption during type checking.

Both `Fun`'s and `Inductive`'s parameter list (`Vec<(String, Expression)>`) come from `typed_parameter_list` (`commons.rs`): a single optional parenthesized, comma-separated group, e.g. `(n: Nat, m: Nat)`. Omitting the parenthesized group entirely yields an empty parameter list. This replaced an older grammar where each parameter had its own parenthesized group (`(arg1: T1) (arg2: T2)`).

`Inductive` encodes both the type name with parameters and the list of constructors. For example (`library/lists.lof`):
```
inductive List (T:TYPE) : TYPE {
  | nil : List(T)
  | cons : T -> List(T) -> List(T)
}
```
becomes `Inductive("List", [("T", TYPE)], TYPE, [("nil", List(T)), ("cons", T -> List(T) -> List(T))])`.

### `Tactic`

Tactics appear only inside `Theorem` proofs written in interactive style.

```rust
pub enum Tactic<E> {
    Begin(),
    Qed(),
    Intro(String, E),   // introduce a variable with a given type
    Exact(E),           // close the goal with this term
    Apply(E),           // apply a function, generating subgoals for arguments
}
```

The `E` type parameter is `Expression` at the parse level, and gets specialized to `T::Exp` during elaboration.

### `LofAst`

Top-level wrapper distinguishing expressions from statements:

```rust
pub enum LofAst {
    Stm(Statement),
    Exp(Expression),
}
```

## `LofParser`

The parser struct holds a `Config` (for system-specific settings) and a `BTreeMap` of custom notations (registered via `sugar` declarations). It is stateful: notation registrations accumulate during a parse run.

Key methods:

| Method | Description |
|--------|-------------|
| `parse_node(input)` | Parse one top-level AST node |
| `parse_source_file(filepath) -> Result<(String, LofAst), LofError>` | Parse a full `.lof` file into a `FileRoot`, returning the remaining unparsed input alongside it |
| `parse_workspace(config, path) -> Result<LofAst, LofError>` | Parse a file or directory into a `FileRoot`/`DirRoot` |

## Parser Modules

| File | Contents |
|------|----------|
| `api.rs` | AST types, `LofParser`, public interface |
| `commons.rs` | Whitespace/comment handling, identifier parser, utility combinators |
| `expressions.rs` | Expression parsers (abstractions, applications, let, match, products) |
| `statements.rs` | Statement parsers (axiom, theorem, fun, inductive, sugar, theory blocks) |
| `tactics.rs` | Tactic parsers (begin/qed/intro/exact/apply) |

## Custom Notations

`sugar "pattern" := "expansion"` registers an infix/prefix/postfix notation. Patterns use `_0`, `_1`, … as positional holes, split on whitespace into `Notation::pattern_tokens: Vec<String>`; `Notation::body` holds the pre-parsed expansion `Expression`. A `precedence` field exists on `Notation` in source but is commented out and unused.

`custom_notations` is `RefCell<BTreeMap<i32, Notation>>`. Each `sugar` declaration is inserted under `next_key = custom_notations.borrow().len() as i32`, i.e. a monotonically increasing index assigned at registration time — not a precedence value. Since `BTreeMap` iterates keys in ascending order, `parse_custom` tries notations in the order they were declared in the source (first-declared, first-tried). This replaces an earlier bug where every notation was inserted under the same fixed key (`0`), so registering a second `sugar` silently clobbered the first and only the most-recently-declared notation ever matched.

A related fix changed where `parse_custom` sits inside the `alt(...)` chains in `expressions.rs` (`parse_expression`, `argument_expression`, `parse_pattern`): it is now tried *before* `parse_app`, `parse_var`, etc. Previously, if a notation's left operand looked like a complete application, `parse_app` would greedily match just that operand first and leave the rest of the notation unparsed, so most custom notations failed to parse in practice.

Example from the standard library (`library/nat.lof`):
```
sugar "_0 + _1" := "plus(_0, _1)"
sugar "_0 * _1" := "times(_0, _1)"
```

## Theory Blocks

The `!theory_block cic … !end_block` syntax lets you lock specific constructs to a particular type system within a mixed file. This is used in the standard library to define inductive types (which only make sense in CIC) while keeping function definitions in the outer scope.
