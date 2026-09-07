# lean_parser Overview

`lean_parser` is a standalone Rust crate at [`lean_parser/`](../../lean_parser/)
that parses a subset of Lean 4 source into a JSON AST. It is entirely
separate from the [`language`](../language/overview.md) crate — no
shared dependency, no shared code, no integration — built as a first
step toward eventual Lean ↔ LoF interoperability. For now the goal is
narrower: produce a standardized, easily parsable representation
(JSON) of Lean 4 source that a downstream tool (this project or
otherwise) can consume.

## Why this scope

Lean 4's full grammar is large: user-extensible notation, `do`-notation,
typeclasses, structures, namespaces, universe polymorphism, and a
macro system that can add arbitrary new syntax. Modelling all of it
would be a project in its own right. Instead, this crate targets
roughly the surface features [LoF's own `.lof` language](../language/syntax.md)
supports, translated into their Lean 4 equivalents — inductive types,
definitions (including recursion, which Lean doesn't mark
syntactically), theorems with term-mode or tactic-mode proofs, `match`,
`let`, arrows and dependent products, holes, imports, comments — so the
two languages' feature sets line up directly. See
[`lean_parser/README.md`](../../lean_parser/README.md) for the exact
in-scope/non-goal table.

Everything unmodelled degrades gracefully rather than failing outright:
an unrecognized declaration becomes a `DeclKind::Error` node, an
unrecognized tactic becomes a `TacticKind::Unknown{name, text}` node
carrying its raw source text. The JSON output is therefore always
well-formed, even for a file this crate only partially understands.

## Pipeline

```
&str source
  │  lexer::lex (src/lexer/scanner.rs)
  ▼
Vec<Token>                        -- see lexer.md
  │  Tokens<'a> (src/tokens.rs): nom-7 input traits over &[Token]
  ▼
nom combinators (src/parser/*.rs)
  │  LeanParser::term / LeanParser::decl / parser::api::parse_module
  ▼
Module (src/ast/*.rs)              -- see ast.md
  │  serde_json
  ▼
JSON
```

Nothing is a lexer-then-parser-then-lexer-again round trip: the lexer
runs once, up front, producing a flat `Vec<Token>` with byte offsets
and line/column positions; every later stage works over that token
slice via a custom nom input type (`Tokens<'a>` in `src/tokens.rs`),
never re-touching the original `&str` except to recover verbatim text
for `Unknown` tactics and `Error` nodes (`LeanParser::text_between`).

## Module layout

| Path | Responsibility |
|---|---|
| `src/lexer/token.rs` | `Token`/`TokenKind`/`Keyword`/`Sym`, the symbol table |
| `src/lexer/scanner.rs` | The hand-written scanner |
| `src/tokens.rs` | `Tokens<'a>`, the nom-7 input trait impls, `sym`/`kw`/`ident`/... helpers |
| `src/ast/{term,decl,tactic}.rs` | The AST, all serde-derived |
| `src/parser/mod.rs` | `Ctx` (the indentation/layout context), `LeanParser` |
| `src/parser/commons.rs` | `col_gt`/`col_ge`/`col_eq`, `spanned` |
| `src/parser/precedence.rs` | The infix/prefix operator table |
| `src/parser/terms.rs` | The Pratt loop, atoms, binders, `fun`/`∀`/`∃`/`let`/`match`/`if` |
| `src/parser/patterns.rs` | Reinterpreting a parsed `Term` as a `Pattern` |
| `src/parser/decls.rs` | Declarations |
| `src/parser/tactics.rs` | `by` blocks and tactics |
| `src/parser/api.rs` | `parse_module`: the top-level loop, with error recovery |
| `src/cli.rs`, `src/main.rs` | The `lean_parser` binary |
| `src/emit.rs` | JSON serialization, `--no-spans` stripping |
| `src/file_manager.rs` | Reading a file / discovering `.lean` files under a directory |

## Worked example

Given `tests/corpus/lof/proofs/basic_tactics.lean`:

```lean
inductive Eq' (T : Type) (x : T) : T -> Prop where
  | refl : Eq' T x x

inductive Nat' : Type where
  | z : Nat'
  | s : Nat' -> Nat'
```

`cargo run -- --pretty tests/corpus/lof/proofs/basic_tactics.lean` produces
(elided for brevity — spans included in the real output):

```json
{
  "path": "tests/corpus/lof/proofs/basic_tactics.lean",
  "decls": [
    {
      "kind": "inductive",
      "name": "Eq'",
      "binders": [
        {"names": ["T"], "ty": {"kind": "sort", "sort": {"kind": "type"}, "level": null}, "info": "explicit"},
        {"names": ["x"], "ty": {"kind": "var", "name": "T"}, "info": "explicit"}
      ],
      "ty": {"kind": "arrow", "domain": {"kind": "var", "name": "T"}, "codomain": {"kind": "sort", "sort": {"kind": "prop"}}},
      "ctors": [
        {"name": "refl", "ty": {"kind": "app", "func": {"kind": "var", "name": "Eq'"}, "args": ["T", "x", "x"]}}
      ]
    }
  ]
}
```

(Real spans are omitted from this excerpt for readability — every node
in the actual output carries one; see `ast.md`.)
