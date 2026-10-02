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

Any other class is rejected with an `Unsupported` error. `include` directives aren't supported yet and fail to parse.

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
