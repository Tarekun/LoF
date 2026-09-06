# Transport across type equivalences

`language/src/type_theory/cic/transport.rs`,
`language/src/type_theory/commons/transport.rs`

Transport takes a proof or definition stated in terms of one type and
mechanically rewrites it into the corresponding proof or definition about an
equivalent type. It is aimed at *proof repair*: when a datatype's
representation changes, the developments built on it don't have to be
rewritten by hand.

## Theoretical basis

The implementation follows Ringer, Porter, Yazdani, Leo & Grossman,
[*Proof Repair across Type Equivalences*](https://arxiv.org/abs/2010.00774)
(the PUMPKIN Pi tool for Coq). That approach transforms proof **terms**
directly, guided by a per-equivalence *configuration* with four components:

| Component | Meaning | Here |
|---|---|---|
| **DepConstr** | how each constructor of the source type is built on the target side | `dep_constr` table |
| **DepElim** | the eliminator to use over the target type in place of the source type's own | `dep_elim` field |
| **Eta** | repackaging needed when the target type bundles extra data | `eta` field (recorded, not consumed - see Limitations) |
| **Iota** | proofs bridging steps that reduce definitionally on the source side but only propositionally on the target | `iota` table (recorded, not consumed - see Limitations) |

Crucially the approach needs **no new axioms**: the output is an ordinary
term checked by the ordinary kernel. That is what makes it implementable
here as a language feature rather than a kernel redesign.

### Why this approach and not another

Two other families were considered and rejected for this codebase:

- **Statement-level transfer** (Isabelle/HOL's Transfer package;
  [Coq's `transfer` plugin](https://arxiv.org/pdf/1505.05028)) rewrites a
  *goal* along a registered isomorphism and discharges a fresh obligation by
  composing with it. It never inspects proof terms, so it cannot carry over
  computational content - only opaque propositions.
- **Univalent parametricity** and its generalization *Trocq* translate the
  whole type theory through a parametricity/logical-relations construction,
  needing either the univalence axiom or a bespoke hierarchy of relations
  inside the kernel. Far more general, but a kernel redesign: this CIC has
  no universe hierarchy and no relational infrastructure to build on.

The 2023 follow-up on *quotient* type equivalences needs setoid rewriting as
an oracle and loses the axiom-free property outside Cubical Agda; quotients
are out of scope here.

## Surface syntax

### Declaring an equivalence

```
equivalence <Name> : <TypeA> <-> <TypeB> {
  forward    := <expr>;      # f : A -> B
  backward   := <expr>;      # g : B -> A
  section    := <expr>;      # forall a:A. g(f(a)) = a
  retraction := <expr>;      # forall b:B. f(g(b)) = b
  dep_elim   := <expr>;      # eliminator over B, shaped like A's own
  eta        := <expr>;      # optional
  dep_constr {
    | <A_constructor> => <expr>
    ...
  }
  iota {
    | <A_constructor> => <expr>
    ...
  }
}
```

`<TypeA>`/`<TypeB>` are bare type names; a parameterized type is named
without its parameters (`List`, not `List(T)`). Fields are parsed in the
order shown. A value may be any expression - typically a name defined
earlier, or a parenthesized `\lambda`.

`dep_elim` must accept the same argument shape as the *source* type's
generated eliminator `e_<TypeA>`: parameters, motive, one case per
constructor of A, then the target. That is what lets the engine drop it in
wherever the source proof eliminated an A.

### Invoking transport

```
transport <new_name> : <new_type_or_formula> from <old_name> using <equiv_name>;
```

`<old_name>` may be a checked `theorem`, or a `fun`/`global`. Whether the
result is registered as a new theorem or as a new definition is decided by
the sort of `<new_type_or_formula>` (`PROP` ⇒ theorem-shaped). The target
type is mandatory: there is deliberately no "translate the statement
automatically" pass, that being the statement-level approach this design
does not adopt.

Transporting a `fun`/`global` also records `old_name -> new_name` in the
equivalence, so later transports of proofs that *call* it pick up the new
name automatically. Auxiliary functions must therefore be transported
before the proofs that use them.

## How the engine works

`transport_term` walks the source term structurally:

| Node | Action |
|---|---|
| a constructor of `type_a` (bare or applied) | replaced by its `dep_constr` image, arguments transported |
| an application of `e_<type_a>` | head replaced by `dep_elim`, arguments (motive, cases, target) transported |
| a name already lifted under this equivalence | replaced by its lifted counterpart |
| an occurrence of `type_a` itself | replaced by `type_b` |
| `Abstraction`/`Product` | binder type and body transported - this is what turns `forall x:A. …` into `forall x:B. …`, with no separate statement-translation pass |
| a raw `match` over `type_a` | rejected (see Limitations) |

`transport_definition` handles the one shape the structural walk cannot: a
`fun rec`-style body whose top level is a `match` on a `type_a`-typed
parameter. That `match` is converted into a `dep_elim` application - a
constant motive built from the declared target type, one minor premise per
constructor built from the corresponding branch, and each self-recursive
call replaced by the induction hypothesis.

The result is re-indexed, type checked with the ordinary kernel, and unified
against the declared target type before being registered. A failed
transport therefore surfaces as an ordinary type error - the kernel remains
the only thing that decides what is a proof.

## Worked examples

Both live in `library/tests/proofs/` and run as part of `cargo test`.

### Unary ≃ binary naturals (`transport_nat_bin.lof`)

`Nat` (`z`/`s`) against a binary representation mirroring Coq's own
`N`/`positive` split. `s`'s DepConstr image is `bin_succ`, an ordinary
function rather than a constructor of `Bin` - exactly the mismatch that
motivates DepConstr. `dep_elim` is `bin_succ_induction`, which has to be
*derived*: `e_Bin`'s own `bp` case takes a `Pos`, not a recursive `Bin`, so
it cannot express "prove `C(bin_succ(b))` from `C(b)`". It is bootstrapped
by induction on `Nat` (where `nat_to_bin(s(n)) = bin_succ(nat_to_bin(n))`
holds definitionally) and then transferred to `Bin` via the retraction.

`transport plus_bin … from plus` succeeds. Transporting a theorem on top of
it does not - see Limitations.

### Lists ≃ length-indexed vectors (`transport_list_vec.lof`)

`List(T)` against `PackedVec(T)`, a `Vec(T,n)` bundled with its length
(the paper's `Σ n. vector n`, spelled as a one-constructor inductive since
this language has no dependent pair). `dep_elim` is an ordinary `global`
composing the two generated eliminators `e_PackedVec` and `e_Vec`, so unlike
the Nat/Bin case it computes. Both `len` and `app` transport into functions
over `PackedVec`.

## Kernel changes this required

Transport is a language feature, but making it work exposed gaps in the
kernel that had never been exercised - nothing in the codebase had used a
generated eliminator before, so no proof by induction had ever been checked.
The following were fixed along the way:

- **ι-reduction for generated eliminators.** `e_<Type>` applications had a
  type but no computation rule, so anything defined through an eliminator
  never reduced, even on a concrete constructor.
  `try_reduce_eliminator_application` supplies it, including for indexed
  families.
- **Reduction under binders.** Normalization never descended into a
  `Product`/`Abstraction`, so two Pi-types differing only by an
  under-binder redex - the routine case when comparing an eliminator's
  generated types - were never recognized as equal.
- **A stuck `match` is a normal form**, not a panic: a scrutinee that is an
  open variable is exactly what an inductive proof's step case produces.
- **Substitution round-trips through unification.** Solved substitutions
  keyed by an ordinary variable (rather than a metavariable) were fed to a
  metavariable-only substitution function, panicking on the key.
- **Pattern variables are binding occurrences.** Constraint collection
  type-checked them as if they were references, so any term containing a
  `match` failed the moment its enclosing abstraction was checked.
- **Identity bindings.** `x ≐ x` where only one side is flagged global (an
  artifact of indexing each elaborated fragment separately) was reported as
  an occurs-check cycle.
- **Theorem proof terms are retained.** `evaluate_theorem` discarded them,
  so an already-proved theorem's witness could not be retrieved by name -
  which transport fundamentally needs.

## Limitations

These are the boundaries of the MVP. Each is pinned by a fixture under
`library/tests/transport_failures/`, asserted to fail by
`test_transport_expected_failures`.

**Iota is recorded but not inserted.** The `iota` table is part of the
configuration but the engine never consumes it. Where a step is definitional
on the source side and only propositional on the target, the transported
proof has a hole the engine cannot fill. Concretely
(`nat_bin_theorem.lof`): `plus_z_r`'s base case is `refl`, valid only
because `plus(z,z)` *computes* to `z`. Its transported counterpart needs
`plus_bin(bz,bz)` to compute to `bz`, but `plus_bin` is built from
`bin_succ_induction` - a derived *theorem*, and theorems are opaque to
reduction here exactly like axioms - so it has no computational behaviour at
all. Note the ι-reduction rule above does not help: it fires for an
inductive's own `e_<Type>`, and `Bin`'s own eliminator cannot serve as
`dep_elim` in the first place.

**Eta is recorded but not inserted, and the kernel has no eta rule.**
(`list_vec_theorem.lof`.) `len(cons(h,ll))` reduces definitionally, but the
target-side step `len_pv(pv_cons(h,pv))` does not: `pv_cons` is a function
that must destructure its argument, and for a universally quantified `pv`
that `match` is stuck. What would fix it is precisely Eta - `PackedVec` has
a single constructor, so every `pv` *is* `pack(n,v)` - but making that a
definitional equality needs an eta rule for single-constructor inductives
(Coq gets this from primitive projections), which this kernel lacks.

**Raw `match` over the source type.** (`raw_match.lof`.) Only a top-level
recursion split is converted to `dep_elim`. A `match` elsewhere is rejected
rather than rewritten, because the source type's constructors need not
correspond to constructors of the target type at all - rewriting the
patterns through DepConstr would produce a `match` whose patterns aren't
constructors. Source proofs should eliminate via `e_<Type>` explicitly.

**No automatic configuration discovery.** Every `dep_constr`, `dep_elim` and
`iota` entry is written by hand. The paper's own search heuristics are
limited to four built-in procedures and frequently need manual override; not
attempting them keeps the engine's behaviour predictable.

**Recursion shape.** `transport_definition` handles structural recursion on
one parameter where each self-recursive call passes the recursive sub-term
(in any argument position) with the other arguments unchanged. Mutual
recursion, recursion nested under a second `match`, and calls whose other
arguments are themselves transformed are out of scope.

**Auxiliary lifting is not transitive.** The engine does not walk a
function's call graph and lift dependencies on demand; each must be
transported first, bottom-up. Doing it automatically risks non-termination
when the target refines the source, a hazard the paper also flags.

**No mutual or nested inductive types**, and **no quotient types** - both
are pre-existing gaps in this kernel rather than transport-specific ones.

**No decompiler.** PUMPKIN Pi can render a transported term back into a
tactic script (explicitly forfeiting soundness to do so); this produces only
kernel-checked terms.

### Two practical gotchas

- **Bound-variable names must be distinct across nested scopes.** The
  unifier keys variables by name, so reusing a name that a motive or an
  inductive's parameter already binds produces spurious failures. The
  fixtures rename accordingly (`bx`, `Tp`).
- **Deeply nested proof terms are expensive.** Normalization recurses
  through a term's structure, so a large proof is cheaper split into named
  lemmas than written as one deep term - `transport_nat_bin.lof` extracts
  `double_s` and `pos_succ_correct_xI` for exactly this reason.
