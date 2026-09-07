# lean_parser

A standalone Rust crate that parses a subset of Lean 4 source into a
serde-serializable AST, emitted as JSON. It is a nom-7-based, hand-lexed
parser, built as a first step toward eventual Lean ↔ [LoF](../language/)
interoperability — for now it has no dependency on and no integration
with the `language` crate; it just produces a standardized, easily
parsable representation of Lean 4 source.

See `docs/lean_parser/` (at the repo root) for the full design writeup:
overview, AST reference, and lexer/indentation notes.

## Scope

This crate targets roughly the surface features the `language` crate's
own `.lof` language supports, translated into their Lean 4 equivalents,
rather than the whole of Lean 4.

**In scope**

| Layer | Constructs |
|---|---|
| Declarations | `import`, `def`/`abbrev`, `theorem`/`lemma`, `example`, `axiom`, `inductive ... where \| c : T`, `@[attr]` (recorded as raw text), `deriving`, modifiers (`partial`/`private`/`protected`/`unsafe`/`noncomputable`) |
| Binders | `(x y : T)`, `{x : T}`, `⦃x⦄`, `[Inst]`, bare `x`, and the shared-type form `∀ x y : T, ...` — parsed as syntax only, no typeclass resolution |
| Terms | `fun`/`λ`, `∀`/`\forall`, `∃`/`\exists`, `(x : T) → B`, `A → B`/`A -> B`, juxtaposition application `f a b`, `match ... with \| p => b`, `let`/`have` (`;`-separated or newline-separated), `_` and `?m` holes, `.ctor` dotted names, `Type`/`Prop`/`Sort u`, tuples, `⟨⟩` anonymous constructors, `if/then/else`, nat/string/char literals, a fixed operator-precedence table (Pratt parser) |
| Tactics | `by` blocks, `intro`/`exact`/`apply`, `<;>`/`;` sequencing, an `Unknown{name, text}` catch-all for every other tactic (`simp`, `rfl`, `induction`, `constructor`, ...) so real files don't hard-fail |
| Comments | `--` line, `/- -/` nested block, `/-- -/` doc comments (attached to the following declaration), `/-! -/` module doc (skipped) |

**Explicit non-goals**: `macro`/`macro_rules`/`syntax`/`notation`/`infix`
and any user-extensible syntax; `do`-notation; `structure`/`class`/
`instance`; typeclass resolution; `namespace`/`section`/`open`/
`variable`/`universe`; `mutual`; universe polymorphism beyond parsing
`Sort u`; anonymous-constructor elaboration; **any elaboration, name
resolution, or type checking whatsoever**. The parser is purely
syntactic — `Nat.succ` is one identifier string, not a resolved
constant. Anything unrecognized at declaration level becomes a
`DeclKind::Error` node rather than a hard parse failure.

## Usage

```
lean_parser [OPTIONS] <PATH>

  <PATH>              a .lean file, or a directory of .lean files

  -o, --output FILE   write JSON to FILE (default: stdout)
  -p, --pretty        pretty-print the JSON
      --tokens        emit the token stream instead of the AST (debugging)
      --no-spans      strip all "span" objects from the output
      --lenient       exit 0 even when the AST contains error nodes
      --recursive     recurse into subdirectories (default: top level only)
  -h, --help          print this message
```

Exit code is `0` when the parse produced no `Error` nodes (or when
`--lenient` was given), `1` otherwise. The JSON is always well-formed
either way.

## Building and testing

```
cd lean_parser
cargo build
cargo test
```

`tests/corpus/` holds the test fixtures: `lof/` and `lof/proofs/` are
hand-translated from `../library/*.lof` and
`../library/tests/proofs/*.lof` to demonstrate feature parity with LoF;
`lean/` exercises general Lean features (comments, literals, binders,
operators, indentation, nested `match`, tactics, `let`/`have`); `bad/`
holds deliberately malformed files with a `-- EXPECT: <line>:<col>`
annotation checked by `tests/errors.rs`. `tests/corpus/expected/*.json`
are golden files; regenerate them with `UPDATE_EXPECT=1 cargo test`.
