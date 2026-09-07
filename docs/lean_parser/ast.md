# lean_parser AST Reference

All types live under `lean_parser/src/ast/` (`term.rs`, `decl.rs`,
`tactic.rs`) and are `serde`-derived. This page documents the JSON shape
they produce and the design decisions behind it.

## Node shape

Every AST node is a struct pairing a `#[serde(flatten)]`-ed,
internally-tagged `*Kind` enum with a `span: Span`:

```rust
pub struct Term {
    #[serde(flatten)]
    pub kind: TermKind,
    pub span: Span,
}

#[serde(tag = "kind", rename_all = "camelCase")]
pub enum TermKind {
    Var { name: String },
    App { func: Box<Term>, args: Vec<Term> },
    // ...
}
```

which serializes to `{"kind": "app", "func": {...}, "args": [...], "span": {...}}`.

**Hard constraint this imposes**: every `*Kind` variant must be a
*struct* variant (`Foo { a, b }`), never a newtype variant (`Foo(T)`).
With `#[serde(tag = "kind")]`, a newtype variant wrapping a non-map
value serializes to a bare scalar, and `#[serde(flatten)]` panics at
runtime trying to flatten a scalar into a struct. This is exercised by
a JSON round-trip test for every single variant, in each of
`ast/{term,decl,tactic}.rs`'s `unit_tests` module — if you add a
variant, add its round-trip test alongside it.

## Spans

```rust
pub struct Span {
    pub start: u32,    // byte offset, inclusive
    pub end: u32,      // byte offset, exclusive
    pub line: u32,     // 1-based
    pub col: u32,      // 0-based, Unicode scalar values
    pub end_line: u32,
    pub end_col: u32,
}
```

The filename appears once, on `Module::path` — not repeated on every
node. `Span::merge(a, b)` (start of `a` through end of `b`) is how
composite nodes compute their own span from their parts; `Span::DUMMY`
is reserved for synthesized nodes with no real source position (none
exist in normal output today).

## Terms (`ast/term.rs`)

`TermKind` covers: `Var`/`DotIdent` (purely syntactic — no name
resolution, so `Nat.succ` is one string, not a resolved constant),
`Hole` (`_`), `SyntheticHole` (`?m`), `Sort` (`Type`/`Prop`/`Sort u`),
`Nat`/`Str`/`Char` literals, `App` (n-ary, flattened juxtaposition
application), `Fun`, `Forall` (covers *both* `∀ x : T, P` and
`(x : T) → B` — the two Lean spellings of the same dependent product),
`Exists`, `Arrow` (the *non-dependent* arrow, kept as its own variant
rather than folded into `Forall`/`BinOp` — this mirrors the
`language` crate's own `Arrow`/`TypeProduct` split, so a future LoF ↔
Lean bridge is a direct structural map), `BinOp`/`UnOp` (every other
table-driven operator; see `parser/precedence.rs`), `Let` (covers both
`let` and `have` via `is_have`), `Match`, `By` (a `by` block's tactics),
`Tuple`, `Anonymous` (`⟨⟩`), `Ite`, and `Error` (a term-level parse
failure, propagated up rather than recovered from locally).

`Binder` records a `Vec<String>` of names sharing one optional type and
a `BinderInfo` (`Explicit`/`Implicit`/`StrictImplicit`/`InstImplicit`)
recording which bracket shape was used — purely syntactic, with no
typeclass-resolution semantics attached to `InstImplicit`.

## Patterns (`ast/term.rs`)

Patterns are **not** a separate grammar. A `match` alternative's pattern
is parsed with the ordinary term grammar and then reinterpreted
structurally (`parser::patterns::term_to_pattern`) — far less code than
a second grammar, and it can't drift out of sync with what the term
parser actually accepts. `PatternKind::Ctor` is only produced when the
head carries arguments or is itself a `.dotted` name; a bare,
argument-less identifier stays `PatternKind::Var` — this parser never
guesses whether an identifier is a constructor or a bound variable by
capitalization or any other heuristic, since that's name resolution
and out of scope.

## Declarations (`ast/decl.rs`)

`Module { path, doc, decls, span }` at the root. `Decl` carries an
optional leading doc comment, a list of raw `@[...]` attribute texts
(un-parsed beyond balancing brackets), a `Modifiers` struct
(`is_partial`/`is_private`/`is_protected`/`is_unsafe`/
`is_noncomputable`), and a `DeclKind`.

`DeclKind::Def` covers both `def` and `abbrev` (`is_abbrev`
distinguishes them) and has **no** `is_rec` flag — unlike the
`language` crate's `Statement::Fun`, Lean doesn't mark recursion
syntactically; a `def` referencing its own name in its body simply is
recursive. `DeclKind::Theorem` likewise covers both `theorem` and
`lemma` (`keyword` records which spelling was used).

`DeclKind::Error { message, text }` is a recovery node: when a chunk of
source doesn't parse as any known declaration, `parser::api::recover`
skips forward (guaranteeing progress) to the next plausible declaration
start and records what it skipped, rather than aborting the whole
file's parse. `parser::api::has_errors` checks a `Module` for any such
node; the CLI uses it to pick an exit code.

## Tactics (`ast/tactic.rs`)

A deliberately small, closed vocabulary — `Intro`/`Exact`/`Apply`,
matching the `language` crate's own interactive-tactic set — plus
`SeqFocus` (`<;>`) and an `Unknown { name, text }` catch-all holding the
verbatim source text of any other tactic (`simp`, `rfl`, `induction`,
`constructor`, ...). This is what lets real-world Lean files with a
richer tactic vocabulary parse without hard-failing: only the
five/six-construct core is structured, everything else is preserved as
text for a future revision (or another tool) to interpret.

## Root output

A single file parses to a bare `Module` object. A directory parses to:

```json
{"kind": "workspace", "root": "<path>", "modules": [Module, ...], "errors": ["<message>", ...]}
```

where `errors` collects file-level failures (e.g. a lex error) that
kept a whole file from producing a `Module` at all — as opposed to a
`DeclKind::Error` node, which represents one declaration's worth of
unparsed source inside an otherwise-successful `Module`.
