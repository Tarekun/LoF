# FOL — First-Order Logic

`language/src/type_theory/fol/`

FOL is the user-facing type system for proof automation. It provides a richer and more natural syntax for expressing logical domains than working directly with clauses. The engine compiles FOL statements to SUP and lets the saturation algorithm find proofs automatically.

## Grammars

### `FolTerm` — computational terms

```rust
pub enum FolTerm {
    Variable(String),
    /// \lambda var_name: formula. body
    Abstraction(String, Box<FolFormula>, Box<FolTerm>),
    Application(Box<FolTerm>, Box<FolTerm>),
    Tuple(Vec<FolTerm>),
    /// let var_name : opt_formula := body in scope
    Let(String, Box<Option<FolFormula>>, Box<FolTerm>, Box<FolTerm>),
}
```

### `FolFormula` — types and propositions

```rust
pub enum FolFormula {
    Predicate(String, Vec<FolTerm>),
    Arrow(Box<FolFormula>, Box<FolFormula>),  // implication / function type
    Not(Box<FolFormula>),
    Conjunction(Vec<FolFormula>),
    Disjunction(Vec<FolFormula>),
    ForAll(String, Box<FolFormula>, Box<FolFormula>),
    Exist(String, Box<FolFormula>, Box<FolFormula>),
}
```

`Term ≠ Type` in FOL: terms and formulas are syntactically distinct. `Exp = Union<FolTerm, FolFormula>`.

### `FolStm` — statements

```rust
pub enum FolStm {
    Axiom(String, FolFormula),
    Theorem(String, Box<FolFormula>, Union<FolTerm, Vec<Tactic<Union<FolTerm, FolFormula>>>>),
    Global(String, Option<FolFormula>, Box<FolTerm>),
    Fun(String, Vec<(String, FolFormula)>, Box<FolFormula>, Box<FolTerm>, bool),
    Auto(FolFormula),    // prove formula automatically
    Solve(Vec<FolFormula>), // logic programming query
}
```

## Default Environment

The initial environment seeds a set of primitive predicates:
```
Unit : []    (nullary)
Top  : []
TYPE : []
PROP : []
```

These cover the built-in sort names used as type-level constants.

## Type Checking

FOL type checking is more permissive than CIC — equality is purely structural (`term1 == term2`), with no unification for metavariables.

| Expression | Rule |
|------------|------|
| `Variable(x)` | Look up `x` in context |
| `Abstraction(x, A, b)` | Check `A` is a formula, extend context with `x:A`, return `A → type_of(b)` |
| `Application(f, a)` | Check `f : A → B`, check `a : A`, return `B` |
| `Tuple(ts)` | Check each term, return `Conjunction` of their types |
| `Let(x, T, b, s)` | Check `b:T`, extend environment, return type of `s` |
| `Predicate(p, args)` | Look up `p` in predicates, check argument count and types |
| `Arrow(A, B)` | Check both formulas, return a formula type |
| `ForAll(x, A, P)` | Check `A`, extend context, check `P` |
| `Not(φ)` | Check `φ` is a formula |
| `Conjunction/Disjunction` | Check all sub-formulas |

## `Auto` and `Solve`

These are the automation entry points:

- `auto formula` — instructs the engine to automatically prove `formula`. During type checking, only validates the formula is well-formed; the actual proof search happens in evaluation via the FOL→SUP compilation path.
- `solve formula1 formula2 …` — logic programming query. Checks each formula is well-formed.

Function/predicate application uses parenthesized, comma-separated syntax (`f(a, b, c)`), not space-juxtaposition. For example, from `library/tests/loprog/nat.lof`:

```
axiom ax1 : \forall n : Nat. NatEq(plus(z, n), n);
axiom ax2 : \forall n:Nat. \forall m:Nat. \forall p:Nat. NatEq(plus(n, m), p) -> NatEq(plus(s(n), m), s(p));

# solve the equation 1+r = 3
solve NatEq(plus(s(z), r), s(s(s(z))))
```

Both `auto` and `solve` bottom out in `Sup::saturate`, whose search strategy is additionally configured by the global `selection_fn` and `giving_clause_fn` config options (see `sup.md` for saturation details).

## Evaluation

`fol/evaluation.rs` handles statement evaluation:

- `Axiom`, `Global`, `Fun`, `Theorem` — same as CIC: add name and definition to environment
- `Auto(target)` and `Solve(goals)` — delegate to the generic `evaluate_auto`/`evaluate_solve` (`commons/evaluation.rs`), passing FOL's `clausify` and `term_to_sup` (both from `fol_utils.rs`) plus a `complement` closure `|φ| Not(φ)` that negates the goal(s) for refutation-based search. `Auto` reports success/failure of proving a single `target`; `Solve` reports the answer `Substitution` recovered for its (possibly multiple) `goals`.

The shared `saturation_interface` (in `commons/evaluation.rs`) assembles the saturation set from: each context axiom/theorem's clausified formula, each `global`/`fun` definition's clausified type plus an equality axiom `name = term_to_sup(body)`, and the clausified negation of the goal(s). It then calls `Sup::saturate(&saturation_set, &selection_fn, &giving_clause_fn)`.

### FOL→SUP compilation (`fol_utils.rs`)

`clausify(φ, constants)` turns a `FolFormula` into a `Vec<SupFormula>` (clauses) via a four-stage pipeline:

1. **Negation normal form** (`negation_normal_form`) — removes implications (`Arrow(A, B)` → `Disjunction([Not(A), B])`) and pushes negations inward via De Morgan's laws, flipping `ForAll`↔`Exist` under negation and collapsing double negation.
2. **Prenex normal form** (`prenex_normal_form`) — pulls all quantifiers to the front, producing a quantifier prefix over a quantifier-free matrix (assumes the input is already in NNF).
3. **Skolemization** (`skolemize`) — eliminates `Exist` by substituting each existentially bound variable with a fresh Skolem application `sw_N(args)`, where `args` are the enclosing `ForAll`-bound variables and `N` is a per-formula witness counter.
4. **Conjunctive normal form** (`conjunction_normal_form`) — distributes `Disjunction` over `Conjunction`, flattens nested disjunctions, drops the (redundant, since all variables are now either universal or skolemized) `ForAll` prefix, and returns the resulting clause list.

Each resulting clause is then mapped to `SupFormula`:

| `FolFormula` | `SupFormula` |
|---|---|
| `Predicate(p, args)` | `Atom(p, args.map(term_to_sup))` |
| `Disjunction(lits)` | `Clause(lits.map(clause_to_sup))` |
| `Not(φ)` | `Not(clause_to_sup(φ))` |
| anything else | error (not a valid clause literal; shouldn't occur past NNF/PNF/skolemization/CNF) |

Terms are compiled separately by `term_to_sup(term, constants)`:

| `FolTerm` | `SupTerm` |
|---|---|
| `Variable(name)`, `name ∈ constants` | `Application(name, [])` |
| `Variable(name)`, otherwise | `Variable(name)` |
| `Application(_, _)` (curried spine, via `get_application_components`) | `Application(fun_name, args.map(term_to_sup))` |
| `Abstraction`/`Tuple`/`Let` | error (no SUP counterpart) |

## Reduction

`one_step_reduction(environment: &Environment<Fol>, term: &FolTerm) -> FolTerm` handles β, δ, and let reductions on `FolTerm`, analogous to CIC. It takes the environment by shared reference — term normalization no longer needs `&mut`. Type (`FolFormula`) normalization is not yet implemented (`normalize_expression` panics on the `R(_)`/formula case).

## Source Files

| File | Contents |
|------|----------|
| `fol.rs` | `FolTerm`, `FolFormula`, `FolStm`, trait implementations |
| `elaboration.rs` | Expression/statement → FOL conversion |
| `type_check.rs` | FOL-specific type checking rules |
| `evaluation.rs` | `one_step_reduction` and statement evaluation; wires `clausify`/`term_to_sup` into the generic `evaluate_auto`/`evaluate_solve` |
| `fol_utils.rs` | `substitute_term`/`substitute_formula`, `FolFormula` display, and the FOL→SUP compilation pipeline (`negation_normal_form`, `prenex_normal_form`, `skolemize`, `conjunction_normal_form`, `clausify`, `term_to_sup`) |
