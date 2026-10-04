# TPTP — Problem Input

`language/src/tptp/`

LoF can read problems written in the [TPTP](https://tptp.org) language, the standard input format of automated theorem provers. A TPTP problem file is made of a header and a list of annotated formulas. The header declares the logic of the problem, and the formulas are parsed into the grammar of that logic.

## Problems

```rust
pub struct TptpProblem { pub header: TptpHeader, pub body: TptpBody }
```

`parse_tptp` parses a problem from a string, and `load_tptp_file` reads one from a file.

### Header

The header is the comment block at the top of the file, made of `% Field : value` lines. Lines indented further continue the value of the previous field:

```
%------------------------------------------------------------------------------
% File     : modus_ponens.p
% Problem  : Modus ponens
% Status   : Theorem
% SPC      : FOF_THM_PRP
%------------------------------------------------------------------------------
```

`TptpHeader` keeps every field (`field(name)`) and decodes the two that define the problem. Both are required:
- **`Status`** → `status`: what is known about the problem. The values are `Theorem`, `ContradictoryAxioms`, `CounterSatisfiable`, `Unsatisfiable`, `Satisfiable`, `Unknown` and `Open`.
- **`SPC`** (Specialist Problem Class): underscore-separated components, e.g. `FOF_THM_PRP`. Two of them are decoded:
  - the first, the language form → `form`: `CNF`, `FOF`, `TF0`, `TF1`, `TX0`, `TX1`, `TH0` or `TH1`;
  - the third, for FOF and CNF only, the order of the logic → `order`: `PRP` (propositional), `EPR` (effectively propositional) or `RFO` (really first order).

  The second component repeats the status, and the remaining ones list features such as equality or Horness. Neither is decoded.

### Body

The form and the order alone decide how the formulas are parsed. Each variant of `TptpBody` is a logic, holding its annotated formulas (`TptpInput { name, role, formula }`) in that logic's grammar.

| SPC | Logic | Keyword | `TptpBody` variant |
|---|---|---|---|
| `FOF_*_PRP` | Propositional | `fof` | `Propositional(Vec<TptpInput<PropFormula>>)` |
| `CNF_*_PRP`, `CNF_*_EPR`, `CNF_*_RFO` | Clauses | `cnf` | `Clausal(Vec<TptpInput<CnfFormula>>)` |
| `TH0_*`, `TH1_*` | Higher order | `thf` | `HigherOrder(Vec<TptpInput<ThfInput>>)` |

Any other class is rejected with an `Unsupported` error. Propositional CNF problems are parsed as clauses over atoms without arguments (a TODO tracks parsing them to `PropFormula` instead).

`include('file', [names])` directives are replaced by the formulas of the included file, parsed in the logic of the including problem. The included file's own header is ignored, as axiom files don't declare a Status or SPC. The optional list selects formulas by name. `file` is looked up in the including file's directory, then in the `$TPTP` library root. `parse_tptp` uses the working directory as the including directory.

## Propositional problems

Propositional formulas use the full FOF connective syntax and map onto `PropFormula`:

| TPTP | PropFormula |
|---|---|
| `p`, `'It rains'` | `Atom(name)` |
| `$true` / `$false` | `Conjunction([])` (⊤) / `Disjunction([])` (⊥) |
| `~ A` | `Not(A)` |
| `A \| B \| C`, `A & B & C` | flat `Disjunction(vec)` / `Conjunction(vec)` |
| `A => B` / `A <= B` | `Arrow(A, B)` / `Arrow(B, A)` |
| `A <=> B` | `Conjunction([Arrow(A, B), Arrow(B, A)])` |
| `A <~> B`, `A ~\| B`, `A ~& B` | `Not(iff)`, `Not(Disjunction)`, `Not(Conjunction)` |

Quoted atoms lose their quotes, so `'p'` and `p` are the same atom. First-order constructs (quantifiers, variables, atoms with arguments, equality) are not part of the grammar, so they fail to parse.

The problems in `test_artifacts/tptp/prp/` are decided end to end with DPLL (`algorithms::dpll`), and the result is checked against each header's `Status`.

## Clausal problems

Each `cnf` formula is a disjunction of literals, optionally wrapped in parentheses, and maps onto `CnfFormula`:

| TPTP | CnfFormula |
|---|---|
| `X` (upper word) | `CnfTerm::Variable`, implicitly universally quantified |
| `f(t1, …, tn)`, `a` | `CnfTerm::Application`, constants with no arguments |
| `p(t1, …, tn)`, `p` | `Atom(p, args)` |
| `s = t` / `s != t` | `Equality(s, t)` / `Not(Equality(s, t))` |
| `~ L` | `Not(L)` |
| `L1 \| … \| Ln` | `Clause([L1, …, Ln])`. A unit clause is the bare literal, as SUP expects |

Defined words (`$true`, `$false`), numbers and distinct objects (`"…"`) aren't supported yet.

The problems in `test_artifacts/tptp/cnf/` are compared clause by clause, `group_problem.p` with a selective include of `Axioms/groups.ax`, and `socrates.p` is refuted with SUP saturation.

## Higher order problems

THF formulas and types share one grammar, as types and terms do in CIC, and map onto `CicTerm`. A `thf` input is either a declaration `symbol: type` or a formula (`ThfInput::Declaration` / `ThfInput::Formula`), kept in file order.

Formulas are terms of type `$o`, the standard encoding of higher order logic. `$o` is an opaque type rather than CIC's `PROP`, so CIC's own logic doesn't mix with HOL's classical, extensional one. Logical symbols are constants (`Variable(name, Const())`) that a prelude environment will have to declare:

| Constant | Type |
|---|---|
| `~` | `$o → $o` |
| `&`, `\|`, `=>`, `<=>` | `$o → $o → $o` |
| `=` | `Π A:TYPE. A → A → $o` |
| `!!`, `??` | `Π A:TYPE. (A → $o) → $o` |

| TPTP | CicTerm |
|---|---|
| `$tType` | `Sort("TYPE")` |
| `$i`, `$o`, `$true`, `c` | `Variable(name, Const())` |
| `X` bound by a binder | `Variable(X, Bound(i))`, the binders are closed (locally nameless) |
| `f @ a @ b` | `Application(Application(f, a), b)` |
| `A > B > C` | `Product(_, A, Product(_, B, C))` |
| `A & B & C`, `A \| B \| C` | left nested `& (& A B) C` |
| `A => B` / `A <= B` | `=> A B` / `=> B A` |
| `A <~> B`, `A ~\| B`, `A ~& B` | `~` of `<=>`, `\|`, `&` |
| `s = t` / `s != t` | `= ? s t` / `~ (= ? s t)`, the type argument is a hole (`Meta(HOLE_INDEX)`) for the refiner |
| `!!`, `??` as terms | `!! ?`, `?? ?` |
| `![X: τ]: φ` / `?[X: τ]: φ` | `!! τ (λX:τ. φ)` / `?? τ (λX:τ. φ)` |
| `^[X: τ]: t` | `λX:τ. t` |
| TH1 `!>[A: $tType]: φ` | `ΠA:TYPE. φ` |

TH1 type constructors (`list: $tType > $tType`) are terms of type `TYPE → TYPE`, and polymorphic symbols take their type arguments explicitly with `@`. A formula quantified over types with `!>` becomes a product, which a TODO notes is only a term of type `$o` if `$o` were read as `PROP`.

Not supported: choice and description (`@+`, `@-`), `?*`, connectives used as terms (`(&)`), and product and sum types (`*`, `+`).

There is no automated reasoning over `CicTerm` yet, so the problems in `test_artifacts/tptp/thf/` are only checked to parse into closed terms, and `leibniz.p` term by term.
