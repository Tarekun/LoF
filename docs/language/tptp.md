# TPTP — Problem Input

`language/src/tptp/`

LoF can read problems written in the [TPTP](https://tptp.org) language, the standard input format of automated theorem provers. Each TPTP dialect is parsed straight into the grammar of the LoF type system that matches it, so a problem can be type checked by that system's kernel or handed to SUP saturation.

## Dialects

TPTP groups its languages into families, most of them split into levels. The keyword that opens an annotated formula (`cnf(...)`, `fof(...)`, …) picks the family.

| Keyword | Language | What it adds | Support | Parsed into |
|---|---|---|---|---|
| `cnf` | CNF | Untyped clauses | ✅ | `CnfFormula` |
| `fof` | FOF | Untyped first-order formulas | ✅ | `FolFormula` |
| `tff` | TF0 | Monomorphic types: sorts, typed symbols, typed binders | ✅ | `FolFormula` + FOL `Environment` |
| `tff` | TF1 | Polymorphism: `!>[A: $tType]: (A > A)` and type constructors `list: $tType > $tType` | ❌ rejected | — |
| `tff` | TXF | Booleans as terms (`X: $o`, formulas as arguments), `$ite`, `$let`, tuples | ❌ rejected | — |
| `tff` | Arithmetic | `$int`/`$rat`/`$real` with interpreted symbols (`$sum`, `$less`, …) | ⚠️ partial: literals are typed, interpreted symbols are rejected | — |
| `tcf` | TCF | Typed clauses, e.g. `![X: nat]: (p(X) \| q(X))` | ❌ | — |
| `thf` | TH0 | Higher-order logic over simply typed λ-calculus: `^[X: $i]: t`, `@`, `$i > $o` types, quantification over functions and predicates | ✅ | `FTerm` + System F `Environment` |
| `thf` | TH1 | Rank-1 polymorphism: polymorphic symbols `!>[A: $tType]: (A > A)`, type arguments `f @ $i`, polymorphic formulas | ⚠️ partial: no type constructors (they need System Fω) | `FTerm` + System F `Environment` |
| non-classical | NTF/NHF | Modal and other non-classical connectives (`{$box}`, …) on top of TFF/THF | ❌ | — |
| `tpi` | Process instructions | Commands for the prover rather than logic (`input`, `output`, `set_role`, …) | ❌ | — |

Rejected dialects fail parsing with an `Unsupported` error naming the missing feature.

`include('file', [names])` directives are resolved by `load_tptp_file`. It tries the including file's directory first, then the `$TPTP` library root, then the working directory. Inclusion cycles are reported as errors.

## How each dialect maps

### CNF → SUP clauses

Variables become `CnfTerm::Variable`, and constants become nullary `CnfTerm::Application`s. `=`/`!=` become `CnfFormula::Equality` and its negation. Unit clauses are bare literals, following SUP's convention.

### FOF / TF0 → FOL

- Formulas map onto `FolFormula`. Untyped variables get the sort `$i`.
- Equality is encoded as the `=` predicate (`Predicate("=", [l, r])`), which the FOL kernel type checks polymorphically and `clausify` maps back to CNF equality. A TODO tracks replacing this with a dedicated `FolFormula::Equality`.
- TF0 declarations build the FOL `Environment`:
  - sorts become nullary predicates;
  - predicates go into the predicate store;
  - functions and constants go into the context with curried `Arrow` types.
- Undeclared symbols get the TPTP defaults: every argument and function result is `$i`.

`TptpProblem::to_clauses` clausifies FOF/TF0 input for SUP. Axioms are clausified as they are, and conjectures are negated jointly. TF0 sorts are erased on the way. That is only sound for monotonic problems, and a TODO tracks it.

### TH0 / TH1 → System F

THF formulas are terms of type `$o`, the standard encoding of higher-order logic. Logical symbols are constants of the environment returned by `thf::hol_environment`:

| Constant | Type |
|---|---|
| `$true`, `$false` | `$o` |
| `~` | `$o → $o` |
| `&`, `\|`, `=>`, `<=>` | `$o → $o → $o` |
| `=` | `∀A:*. A → A → $o` |
| `!!`, `??` | `∀A:*. (A → $o) → $o` |

Quantifiers become polymorphic constants applied to a λ. For example, `![X: nat]: φ` becomes `!! [nat] (λX:nat. φ)`. TH1's `!>[A: $tType]: φ` becomes a type abstraction `ΛA:*. φ`. `$tType` is System F's kind `*`.

Before type checking, `thf::elaborate` completes a parsed term against the environment. There is no unification involved:
- an application `f @ nat` to a name that denotes a type becomes the type application `f [nat]`;
- the implicit type argument of `=`, `!!` and `??` is taken from the type of the first term they are applied to.

`TptpProblem::type_check_thf` then checks every declaration and every formula, and requires the formulas to have type `$o`, or `∀A:*. … $o` for polymorphic ones. THF input can't be clausified for SUP.
