# SUP — Superposition Calculus

`language/src/type_theory/sup/`

SUP is the automation backend. It implements the superposition calculus for first-order logic with equality, capable of automatically proving theorems by refutation: to prove `φ`, add `¬φ` to the clause set and saturate; if the empty clause is derived, `φ` is proved.

SUP is not directly exposed in the source language — users interact through FOL's `auto` and `solve` commands. SUP does not support elaboration from the generic AST.

## Grammars

### `SupTerm`

```rust
pub enum SupTerm {
    Variable(String),
    Application(String, Vec<SupTerm>),  // f(t1, …, tn)
}
```

Terms are either variables or ground/non-ground function applications. There are no abstractions or dependent types.

### `SupFormula`

```rust
pub enum SupFormula {
    Atom(String, Vec<SupTerm>),          // P(t1, …, tn)
    Equality(SupTerm, SupTerm),          // t1 = t2
    Not(Box<SupFormula>),                // ¬φ
    Clause(Vec<SupFormula>),             // l1 ∨ l2 ∨ … (disjunction of literals)
    ForAll(String, Box<SupFormula>, Box<SupFormula>),
}
```

A `Clause` is a disjunction of literals, where each literal is an `Atom`, `Equality`, or their negation via `Not`. The empty `Clause([])` is falsum (⊥).

## Saturation Algorithm

`sup/saturation.rs` implements the given-clause loop:

```
unprocessed = initial clause set
kept = {}

loop:
    if unprocessed is empty: return Err (satisfiable)
    C = giving_clause_fn(unprocessed)
    
    if C is empty clause: return Ok(mgu)    # proof found
    if C is redundant: skip
    
    C = forward_simplification(kept, C)     # simplify C using kept
    if C is empty clause: return Ok(mgu)
    if C is redundant: skip
    
    simplified = backward_simplification(kept, C)  # simplify kept using C
    unprocessed += simplified               # re-process simplified clauses
    
    new_clauses = generating_inferences(C, kept)
    kept += C
    unprocessed += new_clauses
```

### Inference Rules

`sup/inferences.rs` implements:

| Rule | Description |
|------|-------------|
| **Resolution** | From `C ∨ L` and `D ∨ ¬L'`, derive `(C ∨ D)σ` where `σ = mgu(L, L')` |
| **Factoring** | From `C ∨ L ∨ L'`, derive `(C ∨ L)σ` where `σ = mgu(L, L')` |
| **Superposition** | Equality reasoning: replace a subterm using an equation `l=r` |
| **Equality Resolution** | From `¬(l=r)`, derive `Cσ` where `σ = mgu(l,r)` |
| **Equality Factoring** | Merge two equalities in a clause via unification |

### Simplification Rules

| Rule | Description |
|------|-------------|
| **Demodulation** (forward) | Rewrite a subterm of the given clause using an equation in `kept` |
| **Subsumption Resolution** | Remove a literal from the given clause subsumed by `kept` |
| **Demodulation** (backward) | Rewrite kept clauses using the given clause as a rewrite rule |
| **Tautology deletion** | Discard clauses that are trivially true |
| **Subsumption deletion** | Discard clauses subsumed by smaller kept clauses |

### Clause Selection

Two independent choices are each configured via `config.yml` (enums defined in `config.rs`, functions implemented in `sup/freedom.rs`):

**Literal selection** (`selection_fn: SelectionFunction`) picks which literals of a clause are eligible for the inference rules above:

| Strategy | Description |
|----------|-------------|
| `Maximal` (default) | Select only the maximally ordered literal(s) in a clause (KBO ordering) |
| `All` | Select all literals |

**Giving-clause selection** (`giving_clause_fn: GivingClause`) picks which clause is taken next from `unprocessed`:

| Strategy | Description |
|----------|-------------|
| `Fifo` | Take the first unprocessed clause (`pick_clause`) |
| `Weighted` (default) | Take the clause with the fewest symbols (`pick_clause_weighted`) |

Both `pick_clause` and `pick_clause_weighted` have signature `fn(&mut Vec<SupFormula>) -> Result<SupFormula, LofError>` (`GivingClauseSignature`); they only error on an empty input, a case `saturate`'s loop already guards against before calling them.

## Simplification Ordering (KBO)

`sup/sup_utils.rs` implements a Knuth-Bendix-style ordering over terms (`kbo_terms`) and formulas (`kbo_types`). It is used by literal selection (`drop_maximal_literals`) to pick the maximal literal(s) in a clause, and by demodulation/superposition/equality-factoring to orient equations (via `min`/`max` on this order).

`kbo_terms` compares two terms as follows:

1. **Weight**: a `Variable` always weighs `1`; an `Application(_, args)` weighs `1 + args.len()` — only the immediate arity counts, argument weight is not summed recursively.
2. If weights are equal: two `Variable`s are always `Equal`, a `Variable` is always `Less` than an `Application`, and two `Application`s are compared by argument count first, then lexicographically by recursively comparing corresponding arguments (the first non-equal comparison decides).

The function/predicate **symbol name is never compared** — there is no name-based precedence. Per the function's own doc comment ("Ordering ties are not broken using the internal names, so ex. `Variable`s are all isomorphic"), two applications of the same arity with pairwise-equal arguments compare `Equal` even when their symbols differ (e.g. `f(x)` and `g(x)`).

`kbo_types` extends the same scheme to formulas: `Atom`s compare by argument count then lexicographically by argument via `kbo_terms` (again ignoring the predicate name); `Equality` compares left-hand side then right-hand side; `Not` recurses on the inner formula; `Clause` compares by literal count, then lexicographically over both sides' literals sorted by this same order. Formulas of different constructors are ordered `Atom < Not < Equality < Clause`.

## Return Value

On success (empty clause derived), `saturate` returns `Ok(Substitution<SupTerm>)` — the most general unifier accumulated during resolution. The `Substitution::resolvent(var_name)` method extracts the computed value for a query variable. This is how `solve` returns answers.

On failure (set is satisfiable), returns `Err(LofError)` (see `error.rs`).

## Source Files

| File | Contents |
|------|----------|
| `sup.rs` | `SupTerm`, `SupFormula`, trait implementations |
| `saturation.rs` | Main given-clause loop |
| `inferences.rs` | Inference rules (resolution, superposition, factoring, equality rules) |
| `freedom.rs` | Clause selection functions and giving-clause strategies |
| `sup_utils.rs` | KBO ordering, subsumption check, tautology check, term substitution |
| `type_check.rs` | Well-formedness checks for SUP terms and formulas |
| `unification.rs` | `SupTerm`/`SupFormula` unification (`terms_unify`, `formulas_unify`) and substitution application |

Note: `language/benches/sld_vs_saturation_problems.txt` is a (currently untracked) problem-set fixture for a planned benchmark comparing SLD resolution against saturation; its header comments reference `sld_bench.rs`/`sld.rs`, but no such SLD engine exists in the codebase yet — it is fixture data only.
