# lean_parser Lexer and Indentation

## Why a separate token layer, not `nom` straight over `&str`

The `language` crate's own parser (`language/src/parser/`) runs nom
combinators directly over `&str`. `lean_parser` instead lexes up front
into a flat `Vec<Token>` and runs the parser over that token slice via
a custom nom input type (`Tokens<'a>` in `src/tokens.rs`). Two things
about Lean 4 specifically motivate this:

- **Indentation sensitivity.** Lean's tactic blocks and `match`
  alternatives are column-based (`withPosition`/`colGt` in Lean's own
  grammar). Getting at "what column is the next token at" from inside
  an `&str`-based combinator is awkward; from a token stream where
  every `Token` already carries its `line`/`col`, it's a field read.
- **Unicode-heavy, multi-spelling operators.** `→`/`->`, `λ`/`fun`,
  `∀`/`\forall`, `¬`, `⟨⟩`, `⦃⦄`, nested `/- -/` comments — normalizing
  all of this once, in the lexer, means the parser proper never
  branches on spelling; it only ever sees a `Sym::Arrow` or
  `Keyword::Forall`, regardless of how it was written.

## Token model (`src/lexer/token.rs`)

`Token { kind, start, end, line, col, newline_before }`. `start`/`end`
are byte offsets; `line` is 1-based; `col` is 0-based and counts
**Unicode scalar values**, not bytes or grapheme clusters — this
matches Lean's own convention and is what makes the indentation rules
below correct for multi-byte source (e.g. `∀` is one column, not the
three bytes it takes in UTF-8).

`newline_before` is the *only* extra layout information the lexer
records beyond raw column: whether the whitespace/comments immediately
preceding this token contained a newline. No newline tokens are ever
emitted — every place a newline genuinely matters (a same-line `by
exact foo` vs. a multi-line tactic block; a `;`-free `let` body)
reduces to a column comparison plus this one flag, at zero grammar
cost.

Key normalizations performed by the scanner: `->`/`→` → `Sym::Arrow`,
`λ`/`fun`/`∀`/`\forall`/`∃`/`\exists` → the corresponding `Keyword`,
ASCII (`/\`, `\/`) and Unicode (`∧`, `∨`) operator spellings unified to
the same `Sym`. Dot-separated identifier components collapse into a
single `Ident` token (`Nat.succ` is one token), but `.` before a digit
does not (`x.1` lexes as `Ident("x")`, `Sym::Dot`, `Nat(1)`, since
numeric projections are out of scope and must not corrupt ordinary
dotted-identifier lexing). A bare `?` is a lex error — every synthetic
hole needs a name (`?m`, or `?_` for the anonymous form).

## `Tokens<'a>` (`src/tokens.rs`)

A newtype over `&[Token]` implementing just enough of nom 7's input
traits (`InputLength`, `InputTake`, `InputIter`, `Offset`, the `Slice`
family) to run `alt`/`many0`/`separated_list1`/etc. over it — but
deliberately *not* `Compare` or `InputTakeAtPosition`, which are the
wrong shape for matching "any identifier" or "the symbol `→`" by kind
rather than by payload. Small factory functions (`sym(Sym::Arrow)`,
`kw(Keyword::Fun)`, `ident`, `nat_lit`, ...) stand in for
`nom::bytes::tag`, which only works over character streams.

`impl ParseError<Tokens> for LeanError` overrides `or()` to keep
whichever of two competing errors is *farther* into the token stream,
rather than nom's default of keeping whichever `alt` branch was tried
last. Without this, a deeply nested `alt` (the term-atom dispatch is
one) always reports the shallowest, least specific failure ("expected
application") no matter what actually went wrong several tokens in.

## The indentation rule

Everything indentation-sensitive in this grammar reduces to one rule,
threaded through parsing as an explicit `Ctx { min_col, alt_col, depth }`
(`src/parser/mod.rs`), passed by value (it's `Copy`) rather than stored
as mutable state:

> A construct anchored at column `c` may be continued only by tokens at
> column **strictly greater than `c`**. The construct's own leading
> token is exempt.

- **Top-level declarations**: `Ctx::top()` has `min_col = 0`, so a new
  declaration at column 0 naturally ends whatever term/tactic parsing
  came before it — no lookahead heuristics needed.
- **`by` blocks** (`parser::tactics::by_block`): the anchor is the
  *first* tactic's column; later tactics need `col >= anchor` (or an
  explicit `;`). A term parsed *inside* a tactic (e.g. `exact`'s
  argument) is re-anchored at that same column so its own application
  chain can't swallow the next tactic.
- **`match` alternatives** (`parser::terms::match_alts`): the anchor is
  the first `|`'s column; a nested `match`'s own alternatives are only
  accepted if their `|` sits at a column *strictly greater* than the
  enclosing match's — two `match`es whose alternatives share a column
  is a rejected, tested case (`tests/corpus/bad/bad_match_alt.lean`).
- **`let`/`have`** (`parser::terms::let_term`): re-anchored at the
  `let`/`have` keyword's own column, not the enclosing construct's —
  otherwise a `let` nested a few lines into a `def` body could parse
  its value's application chain right through the next top-level
  declaration (this was a real bug caught by the corpus tests; see the
  comment at the top of `let_term`).

One nom-7 subtlety this design leans on: a zero-width verifier
(`col_gt`/`col_ge`) must never be the *entire* body of `many0`/`many1` —
nom's no-progress guard would treat that as a hard error. It's always
paired, via `preceded`, with something that actually consumes a token.
A related, sharper version of the same trap bit the first version of
`parser::terms::match_alt_committed`: `many1` silently *stops* (rather
than propagating an error) the moment its inner parser fails once,
which is correct when there's simply no more `|`, but wrong when a `|`
*is* present and something after it is malformed — that failure needs
promoting to `nom::Err::Failure` (via `match_alt_committed`) so it
doesn't get silently swallowed as "end of alternatives".
