# The theory behind transport

Background reading for [transport.md](transport.md), which describes *what*
the feature does. This document is about *why* it is built the way it is:
which pieces of type theory the design leans on, which choices were forced by
theory rather than convenience, and where to read further.

It assumes comfort with dependent types - Π/Σ, inductive families,
eliminators, the difference between definitional and propositional equality -
but **no** familiarity with homotopy type theory, and none with the proof
repair literature. Where HoTT is unavoidable (it is the origin of several
ideas here) it is introduced in the small, and the document is explicit about
which of its results are *not* being assumed.

Links: nLab entries are given as page names under `ncatlab.org/nlab/show/`.
A few papers are cited by title and venue rather than URL, deliberately -
their canonical locations move, and the title is the stable identifier.

---

## 1. The problem: two equalities, and only one of them computes

Every dependent type theory of this family has two notions of sameness.

**Definitional (judgemental) equality**, `a ≡ b`, is a *judgement of the
kernel*. It is decided by normalizing both sides and comparing, and it is
silent: if `a ≡ b` then anything that type checks with `a` type checks with
`b`, with nothing recorded in the term. This is the conversion rule, and it is
what makes `refl` a proof of `plus(z, z) = z`: the two sides are literally the
same normal form, so the reflexivity proof of the trivial equation is already
a proof of the interesting-looking one.

**Propositional equality**, `Eq(T, a, b)`, is an *inductive type inside the
theory*. Its inhabitants are terms you must build and then explicitly use.
Using one means eliminating it - in this kernel, `e_Eq`, which is Martin-Löf's
`J`. Every use leaves a mark in the proof term, and changes the term's type
only where you aimed it.

Definitional equality implies propositional (`refl` witnesses it). The
converse fails, and that asymmetry is the entire subject of this document.

A proof written against a datatype is, in practice, saturated with appeals to
the *definitional* behaviour of that datatype's functions. `plus_z_r`'s base
case is `refl` and nothing else, because `plus(z, z) ≡ z` holds by ι-reduction
of `Nat`'s eliminator. Nothing in the proof term names that fact; it is
invisible, discharged by the conversion rule.

Now change the representation. `Bin`'s corresponding step is *true* but only
*propositionally* so: `plus_bin(bz, bz) = bz` needs a proof, and there is no
`refl` to be had. The proof term that worked has no place to put that proof,
because it never mentioned the step in the first place.

That is the shape of every difficulty in this feature. **Transport across a
change of representation fails exactly where the source proof was relying on
computation that the target does not reproduce.** Everything below is either
a way to restore the computation (η, §5) or a way to hand the proof term the
missing propositional bridge and splice it in at the right place (ι, §4).

Further reading: nLab *definitional equality*, *propositional equality*,
*identity type*. For the rules themselves, Paulin-Mohring, *Inductive
Definitions in the System Coq: Rules and Properties* (TLCA 1993) is the
primary source for CIC's ι-rules; the Coq reference manual's *Typing rules*
chapter is the readable modern statement.

---

## 2. Equivalence, and the univalence-shaped hole

Two types `A` and `B` are **equivalent** when there are `f : A → B` and
`g : B → A` with `g ∘ f ∼ id` (the *section*) and `f ∘ g ∼ id` (the
*retraction*). That is the data an `equivalence` declaration carries in its
first four fields, and it is the classical notion of isomorphism up to
propositional equality.

(A caveat worth knowing, though nothing here depends on it: in HoTT
"equivalence" is defined more carefully than "isomorphism", because the naive
four-field record is not a proposition - a given `f` can carry
non-equal isomorphism structures. The standard fixes are the *half-adjoint
equivalence* (add a coherence law relating section and retraction) or a
*contractible-fibres* definition. This kernel has no universe hierarchy and no
h-level infrastructure, so it uses the naive form and never quantifies over
equivalences; that is sound here precisely because equivalences are only ever
*consumed*, at elaboration time, and never reasoned about. nLab:
*equivalence in type theory*, *half adjoint equivalence*.)

The obvious thing to want is the **univalence axiom**: equivalent types are
themselves equal, `(A ≃ B) → (A = B)`. With it, transport is not a feature at
all - it is `e_Eq` applied to the path you get from the equivalence.
Everything transports, uniformly, with no configuration.

Two reasons this design does not go there.

**It is an axiom, and axioms do not compute.** Adding univalence to a
conventional type theory breaks canonicity: `transport` along a univalence
path is stuck, so the transported function is a term that type checks and
never reduces. You would move `plus` to `Bin` and get something that cannot
evaluate `plus_bin(bz, bz)` to anything. Cubical type theory exists to fix
exactly this - it gives univalence computational content - but that is a
different theory with a different kernel (interval, Kan operations, a
composition structure on every type), not an addition to this one.

**The scale is wrong.** Univalence is a statement about a universe, and this
kernel does not have a universe hierarchy to state it in.

What replaces it here: the source proof is not transported along a *path*
between types. It is **re-elaborated against a second presentation of the
target type**, which is the subject of §3. The output is an ordinary term in
the ordinary theory, checked by the ordinary kernel, using no axiom the
library did not already assume. That axiom-freedom is the property the whole
design is organized around, and it is what makes the feature implementable in
a kernel this small.

Further reading: the HoTT book (homotopytypetheory.org/book), chapters 2 and
4, for equivalence and univalence - chapter 2 alone is enough for this
document. nLab: *univalence axiom*, *structure identity principle*. For why
univalence does not compute and what it costs to make it, Cohen, Coquand,
Huber & Mörtberg, *Cubical Type Theory: a constructive interpretation of the
univalence axiom* (TYPES 2015).

---

## 3. The central idea: a configuration is a second presentation of a type

This is the load-bearing concept, and it is the one that makes the four
configuration fields feel inevitable rather than ad hoc.

An inductive type in CIC is not given by its set of values. It is given by an
*interface*:

| | for `Nat` |
|---|---|
| **introduction rules** - how to build one | `z`, `s` |
| **elimination rule** - how to consume one | `e_Nat` (dependent induction) |
| **ι (iota) rules** - what elimination does to each introduction | `e_Nat(C, b, f, z) ≡ b`, `e_Nat(C, b, f, s n) ≡ f n (e_Nat(C, b, f, n))` |
| **η rule** - that every value is built by some introduction | for `Nat`, only derivable propositionally |

A proof about `Nat` uses *nothing else*. It mentions `z`, `s` and `e_Nat`, and
it silently relies on the ι-rules holding definitionally. It cannot mention
anything about `Nat` that isn't in this table, because that is all `Nat` is.

So: **if you can equip `Bin` with a table of the same shape, every proof about
`Nat` can be replayed against it.** That is exactly what a configuration is:

- **DepConstr** - introduction rules for `B`, one per constructor *of `A`*.
  They need not be constructors of `B`. `Nat`'s `s` maps to `bin_succ`, an
  ordinary recursive function. This is the whole point of the abstraction: `B`
  is being presented *as if* it were `A`, and its real constructors are
  irrelevant to that presentation.
- **DepElim** - the elimination rule for that presentation: an eliminator over
  `B` with the argument shape of `A`'s. Often it must be *derived*, because
  `B`'s own eliminator eliminates along `B`'s real recursion structure, which
  is the wrong shape. `bin_succ_induction` is derived exactly so.
- **Iota** - the computation rules of the presentation, one per DepConstr.
  When `dep_elim` is a real eliminator applied to a real constructor these
  hold definitionally and the table is empty. When it is a derived function
  applied to a DepConstr image that is not a constructor, they hold only
  propositionally - and then they must be supplied as equalities.
- **Eta** - the uniqueness rule, needed when the target bundles extra data
  (`PackedVec` = a vector plus its length) and something must repackage a
  value into the canonical form the presentation expects.

Read this way the four fields are not a heuristic toolkit; they are the
introduction, elimination, computation and uniqueness rules of a type, and
transport is *change of presentation*, not translation. This also explains the
division of labour in the implementation: ι and η are the two rules that can
degrade from definitional to propositional, and so they are the two that need
machinery.

It also explains a design decision that otherwise looks like an omission.
Transport requires you to *state* the target type; it does not derive it. A
presentation is a thing you choose - which `A`-shaped interface you want `B`
to wear is not determined by `B` - so the statement is input, not output.

Further reading: Ringer, Porter, Yazdani, Leo & Grossman, *Proof Repair across
Type Equivalences* (PLDI 2021), [arXiv:2010.00774](https://arxiv.org/abs/2010.00774)
- §2-4 are the source of this framing, and are the single most useful thing to
read alongside this codebase. Talia Ringer's PhD thesis, *Proof Repair* (2021),
covers the same ground at more length with the design history. For the general
"a type is its rules" stance, Martin-Löf, *Intuitionistic Type Theory* (1984),
and nLab *natural deduction*, *inductive type*.

---

## 4. Iota: when a computation rule is only a proposition

Take the two rules for `Nat` above. On the `Bin` side, the corresponding
statement is:

```
iota[z] : ∀C base step. Eq( C(bz),
                            bin_succ_induction(C, base, step, bz),
                            base )
```

which is `e_Nat(C, b, f, z) ≡ b`, demoted from a judgement to a proposition.

**Why it is demoted here.** `bin_succ_induction` is not a primitive
eliminator. It is derived: prove the statement by induction on `Nat`, where
`nat_to_bin(s n) ≡ bin_succ(nat_to_bin n)` does hold definitionally, then
transfer along the retraction. The transfer goes through `e_Eq` applied to
`retraction_nat_bin`, and that retraction is an *axiom* in this library. An
`e_Eq` stuck on an opaque proof never reduces, so `bin_succ_induction` has no
computational behaviour whatsoever - not weak, not partial, none. Nothing
about `plus_bin` reduces.

This is not an artefact of the axiom. Even with a derived retraction the same
thing happens for a different reason: `bin_succ(b)` for opaque `b` is a
`match` on a variable, irreducibly stuck. Binary successor genuinely does not
compute on an unknown argument, and no amount of transparency changes that.
The demotion from `≡` to `=` is real, and it is the price of the
representation change.

**How a proposition substitutes for a conversion rule.** It cannot, in
general - that is why this is a limitation and not a solved problem. What it
*can* do is patch a specific spot. Given `p : Eq(T, lhs, rhs)` and a goal
mentioning `lhs`, eliminating `p` with `J` transports a proof of the
`rhs`-flavoured statement into a proof of the `lhs`-flavoured one, provided
you tell `J` a *motive*: which occurrences of `lhs` to generalize. Choosing
the motive is choosing where to rewrite, and it is the only real content of a
rewrite step.

The engine therefore does, for each minor premise that fails to type check:

1. Take the expected type (what `dep_elim` demands) and the actual type (what
   the transported case has). If they unify, do nothing - which is why an
   empty `iota` table costs nothing and every previously-working configuration
   is unaffected.
2. Instantiate the relevant `iota` entry by **first-order matching** its
   left-hand side against subterms of the goal. First-order, not higher-order:
   the rules are equations between applications with the quantified variables
   in argument position, so pattern variables are always applied to nothing
   and a positional match suffices. Full higher-order unification is
   undecidable, and even the decidable Miller-pattern fragment is more
   machinery than these rules need.
3. Abstract the matched occurrence to build the motive.
4. Eliminate.

Two facts about step 4 are worth stating because they are theory, not tuning.

**Direction.** You have a term of the actual type and need one of the expected
type; `J` runs one way, so which endpoint you eliminate at is determined, and
getting it backwards produces a well-typed rewrite of the wrong statement. The
engine eliminates *into a function type* - it builds `abstracted[to] → goal`
and applies it - rather than composing `sym` with a rewrite. That is one `J`
instead of two, and it halves the nesting.

**Two vocabularies.** The ι-rule speaks of `dep_elim` applied at a DepConstr
image. The goal says the same thing by naming the lifted function that was
*built* from those. They are convertible but not syntactically equal, so
matching must happen against a δ-unfolded scratch copy while the rewrite is
emitted in the goal's own folded vocabulary. Emitting normal forms instead
would be correct and unusable: it inlines every definition the goal mentions,
which measured two orders of magnitude more type-checking work.

The remaining limitation is honest and precise: **one rewrite, along one rule,
per premise.** A premise needing two independent bridging steps, or whose
redex is not an instance of any declared rule, falls through to an ordinary
type error. Closing that gap is proof *search*, which is a different project
with different failure modes - see the note on PUMPKIN PATCH in §8.

Further reading: on `J` and why the motive is the whole story, the HoTT book
§1.12 (path induction) is the clearest short account, and needs no homotopy.
On rewriting in a dependent setting, Sozeau, *A New Look at Generalized
Rewriting in Type Theory* (JFR 2009). On why higher-order matching was
avoided, Miller, *A logic programming language with lambda-abstraction,
function variables, and simple unification* (1991) for the pattern fragment,
and Huet's classic undecidability result for the general case.

---

## 5. Eta, and why it had to be definitional

η-rules are *uniqueness* rules: they say a value of a type is determined by
what you can observe of it. For functions, `f ≡ λx. f x`. For a
single-constructor ("record") type with fields, `t ≡ C(t.0, …, t.k-1)` -
classically, *surjective pairing*.

The lists ≃ vectors example needs this. `PackedVec(T)` has one constructor
`pack(n, v)`. `cons`'s DepConstr image, `pv_cons`, must destructure its
argument to get at `n` and `v`. In an inductive proof's step case the argument
is a universally quantified variable, so that `match` is stuck - even though
*every* `PackedVec` is a `pack`, and the type theory ought to know it.

**Propositional η is not enough, and this is the non-obvious part.** Supplying
`∀pv. pv = pack(π₁ pv, π₂ pv)` as a rewrite unsticks one layer: `pv_cons`
fires. But its output feeds `app_pv`, which is stuck on the *next* opaque
value one layer down, and `pv_cons` applied to *that* re-sticks. Closing the
example propositionally would need unbounded nested rewriting, driven by a
search that knows when to stop.

Definitional η closes it in one shot, and - the actual payoff - closes it with
**zero changes to the transport engine and no new axioms**. The existing
configuration was already sufficient; it was the kernel that was missing a
rule. This is worth dwelling on, because it is the general lesson: when a
transport fails, the question to ask first is whether the *theory* is missing
a rule, not whether the *tool* is missing a feature.

### The three eligibility conditions

The kernel's rule fires only for types that are: **single-constructor**, with
**no indices**, and with **no recursive occurrence** among the constructor's
argument types.

The first is definitional. The third is termination: η-expanding a recursive
type would produce a value whose fields are of the same type, expandable
again, forever.

**The middle one is soundness, and it is the interesting one.** `Eq(T,x,y)` is
a single-constructor type - `refl` is its only constructor. η for it would
say: every `p : Eq(T,x,y)` is *definitionally* `refl`. That is **UIP** (all
proofs of an equality are equal) - equivalently, in eliminator form, **Streicher's
axiom K**.

Why that is a real cost, stated without HoTT: K is *not derivable* from `J`.
Hofmann and Streicher's groupoid model is a model of the theory in which K is
false, which settles independence. Adding it is therefore a genuine extension
of the theory's strength, taken silently, as a side effect of a rule that
looks like it is about records. It is also known to be incompatible with the
univalent direction (in a univalent setting a type can have distinguishable
identity proofs, so UIP is outright false), which forecloses ever relating
this kernel to one. Handing that out for free, from an optimization, is not a
trade anyone chose - hence the condition, and hence the unit test that pins
`Eq` as ineligible.

Note that Coq, Agda and Lean all have definitional η for records, and all of
them have exactly this restriction in some form. Agda's `--without-K` and
Coq's `Prop`-vs-`SProp` story are both, in part, about drawing this line
carefully.

### Why `Proj` is a primitive term former

The expansion is `t ↦ C(params, Proj(T,0,t), …, Proj(T,k-1,t))`, where `Proj`
is a new term former in the grammar rather than sugar for an eliminator
application.

If projections were encoded as `e_T` applications, each one would itself be a
stuck eliminator application on an opaque target - so the η rule would fire on
its own output, produce more stuck eliminator applications, and expand
forever. Normalization here terminates by reaching a syntactic fixpoint and
has no fuel, so this is a hang, not an error. `Proj` is inert: no reduction
site looks through it, which is what breaks the cycle.

This is not a local hack. It is why Coq has **primitive projections** as a
kernel notion rather than deriving them from `match`, and the reasons are the
same ones: η needs a normal form for "the observation of an unknown value",
and building that out of the eliminator makes conversion undecidable or
non-terminating. In general, adding η to a conversion algorithm is delicate
precisely because it is a rule that fires on *non*-canonical terms; the
type-directed conversion algorithms in the literature exist for this reason.

Further reading: nLab *eta-conversion*, *axiom K (type theory)*, *uniqueness
of identity proofs*. Hofmann & Streicher, *The Groupoid Interpretation of Type
Theory* (1998) - the independence result, readable without homotopy. Cockx,
Devriese & Piessens, *Pattern Matching Without K* (ICFP 2014) - what it takes
to keep K out of a real elaborator. Gilbert, Cockx, Sozeau & Tabareau,
*Definitional Proof-Irrelevance without K* (POPL 2019) - how to get some of
what K offers while staying compatible. Abel, Öhman & Vezzosi, *Decidability
of Conversion for Type Theory in Type Theory* (POPL 2018) - η in the
conversion algorithm, done properly. Coq reference manual, *Primitive
projections*. Carneiro, *The Type Theory of Lean* (2019) - a compact account
of definitional η for structures in a working kernel.

---

## 6. A theory-adjacent aside: why type checking was exponential

Making ι work meant emitting terms with substantially more nesting, and that
turned a latent quadratic-looking cost into an observed 143-second fixture and
a stack overflow. The cause is worth recording because it is a *typing
discipline* mistake, not a performance one.

Checking `f x` collected unification constraints over the whole application,
and constraint collection on an application in turn type-checked that
application's function. The two were mutually recursive, so cost doubled per
argument: a six-argument curried application nested three deep cost 27 million
type-check calls.

The principle violated is compositionality of typing, the same principle
**bidirectional type checking** is built on: each node's rule should consume
its subterms' types as *results*, and contribute only *its own* constraint. A
node that re-derives what its children already established is not a slow
implementation of the rule - it is a different, wrong rule. Collecting only
the node's own constraint (argument type against domain, both sides already
checked in their own right) brought it to a few hundred calls, and the whole
test suite from 20s to 15s while doing strictly more work.

Further reading: Dunfield & Krishnaswami, *Bidirectional Typing* (ACM Computing
Surveys, 2021) - the survey, and directly applicable. Coquand, *An Algorithm
for Type-Checking Dependent Types* (1996) for the classical presentation of a
dependent checker with conversion.

---

## 7. What the alternatives are, and what they would have cost

Understanding why the configuration approach was chosen means knowing what it
was chosen *over*. All four families below are live research directions; none
is wrong, they buy different things.

**Statement-level transfer.** Isabelle/HOL's `Transfer` package (Huffman &
Kunčar, *Lifting and Transfer*, CPP 2013) and Coq's `transfer` plugin
([arXiv:1505.05028](https://arxiv.org/pdf/1505.05028)) register *relations*
between types and rewrite a **goal** along them, leaving a residual obligation
discharged by composing transfer rules. Mature, extremely effective in
practice, and the right tool in a classical setting. It never inspects proof
terms, so it can carry propositions but not computational content: it will not
give you a `plus_bin` that runs. In a theory where definitions and proofs are
the same syntactic category, that is a serious restriction.

**Univalent parametricity.** Tabareau, Tanter & Sozeau, *Equivalences for
Free!* (ICFP 2018) and its journal version. A parametricity translation is
defined for the whole type theory, and one shows that equivalent types are
related, giving transport uniformly for free. Beautiful and general, but it
needs the univalence axiom for the interesting cases, and inherits the
computation problem of §2 - plus a whole relational infrastructure defined
over the type theory.

**Trocq** (Cohen, Crance & Mahboubi, ESOP 2024) refines this with a
*hierarchy* of relation strengths, so each transport pays only for the
structure it actually uses, and many go through without univalence. This is
the closest thing to a general solution, and if this kernel had a universe
hierarchy it would be the obvious thing to build on. It does not, which is
the whole reason.

**Ornaments.** McBride's *Ornamental algebras, algebraic ornaments* (2010) and
Dagand & McBride, *Transporting functions across ornaments* (ICFP 2012): a
principled account of the specific case where the new type is the old one plus
extra indices or fields - exactly `List` vs `Vec`. Ringer et al.'s earlier
DEVOID (*Ornaments for Proof Reuse in Coq*, ITP 2019) automates this case
fully, and the PLDI 2021 configuration approach generalizes it to equivalences
that are not ornaments at all (`Nat`/`Bin` is not). Reading DEVOID first makes
the configuration abstraction feel much less arbitrary.

**Cubical representation independence.** Angiuli, Cavallo, Mörtberg & Zeuner,
*Internalizing Representation Independence with Univalence* (POPL 2021) - in a
theory where univalence computes, this problem simply does not exist in the
form described here. Instructive for seeing which of the difficulties above
are essential and which are artefacts of working in a conventional CIC. (Most
are artefacts. That does not make them avoidable in this kernel.)

The 2023 follow-up extending the configuration approach to **quotient** type
equivalences needs setoid rewriting as an oracle and loses the axiom-free
property outside Cubical Agda; quotients are out of scope here for both
reasons.

---

## 8. Proof repair as a field, briefly

Transport-across-equivalences is one point in a larger design space, and the
neighbouring points explain the shape of the limitations.

The earlier tool in the same line, **PUMPKIN PATCH** (Ringer, Yazdani, Leo &
Grossman, *Adapting Proof Automation to Adapt Proofs*, CPP 2018), works by
*diffing* two versions of a proof and generalizing the difference into a
patch. That is proof **search**, with search's characteristic failure modes:
it finds things you did not anticipate, and fails unpredictably. The
configuration approach deliberately gives that up in exchange for
predictability - if the configuration is right, transport works; if it is not,
you get a type error naming the premise. The "one rewrite per premise" limit
(§4) is exactly the boundary where this design stops and search would begin,
and moving that boundary is a decision about which failure mode you want.

The other structural choice inherited from the same work: PUMPKIN Pi can
*decompile* a transported term back into a tactic script, explicitly forfeiting
soundness to do so (the script is a suggestion; only the term is checked).
This produces terms only. Every transported result goes through the ordinary
kernel, and the kernel remains the sole authority on what counts as a proof -
which is also why a failed transport surfaces as an ordinary type error rather
than a bespoke diagnostic.

For the wider context of why any of this matters at scale, Ringer, Palmskog,
Sergey, Gligoric & Tatlock, *QED at Large: A Survey of Engineering of Formally
Verified Software* (Foundations and Trends in PL, 2019) is the standard
reference on proof engineering as a discipline; the chapter on proof
maintenance is directly on point.

---

## 9. Reading list, ordered

**Start here (the one paper this feature implements)**

1. Ringer, Porter, Yazdani, Leo & Grossman, *Proof Repair across Type
   Equivalences*, PLDI 2021 -
   [arXiv:2010.00774](https://arxiv.org/abs/2010.00774). §2 (motivating
   examples), §3 (configurations), §4 (the lifting algorithm). The `Nat`/`Bin`
   and `List`/`Vec` examples in this repo are its examples.
2. Ringer, *Proof Repair*, PhD thesis, University of Washington, 2021. Longer,
   with the design history and the failed attempts, which are the useful part.

**Type theory background, if the CIC rules are not fresh**

3. Paulin-Mohring, *Inductive Definitions in the System Coq: Rules and
   Properties*, TLCA 1993 - where ι-reduction is specified.
4. The Coq reference manual, *Core language → Typing rules* and *Primitive
   projections*.
5. Coquand, *An Algorithm for Type-Checking Dependent Types*, 1996.
6. Dunfield & Krishnaswami, *Bidirectional Typing*, ACM CSUR 2021 - for §6.

**Eta, K, and why the eligibility conditions exist**

7. nLab: *eta-conversion*, *axiom K (type theory)*, *uniqueness of identity
   proofs*.
8. Hofmann & Streicher, *The Groupoid Interpretation of Type Theory*, 1998 -
   the independence of K. Readable with no homotopy background.
9. Cockx, Devriese & Piessens, *Pattern Matching Without K*, ICFP 2014.
10. Abel, Öhman & Vezzosi, *Decidability of Conversion for Type Theory in Type
    Theory*, POPL 2018 - η handled inside conversion, which is what §5 is
    about.
11. Gilbert, Cockx, Sozeau & Tabareau, *Definitional Proof-Irrelevance without
    K*, POPL 2019.
12. Carneiro, *The Type Theory of Lean*, 2019 - definitional η for structures
    in a kernel, compactly described.

**Equivalence and univalence, in the small**

13. The HoTT book, homotopytypetheory.org/book - chapter 1 §1.12 (path
    induction) and chapter 2 §2.4 and §4.2-4.4 (equivalence). Stop there;
    nothing later is needed for this codebase.
14. nLab: *equivalence in type theory*, *half adjoint equivalence*,
    *univalence axiom*, *structure identity principle*, *transport*.
15. Cohen, Coquand, Huber & Mörtberg, *Cubical Type Theory*, TYPES 2015 - for
    what it costs to make univalence compute.

**Alternative approaches (§7)**

16. Huffman & Kunčar, *Lifting and Transfer: A Modular Design for Quotients in
    Isabelle/HOL*, CPP 2013.
17. Zimmermann & Herbelin, *Automatic and Transparent Transfer of Theorems
    along Isomorphisms in the Coq Proof Assistant*,
    [arXiv:1505.05028](https://arxiv.org/pdf/1505.05028).
18. Tabareau, Tanter & Sozeau, *Equivalences for Free! Univalent Parametricity
    for Effective Transport*, ICFP 2018.
19. Cohen, Crance & Mahboubi, *Trocq: Proof Transfer for Free, With or Without
    Univalence*, ESOP 2024.
20. Dagand & McBride, *Transporting Functions Across Ornaments*, ICFP 2012;
    and McBride, *Ornamental Algebras, Algebraic Ornaments*, 2010.
21. Ringer, Yazdani, Leo & Grossman, *Ornaments for Proof Reuse in Coq*, ITP
    2019 (DEVOID) - the specialization of this feature to ornaments, worth
    reading before the PLDI paper.
22. Angiuli, Cavallo, Mörtberg & Zeuner, *Internalizing Representation
    Independence with Univalence*, POPL 2021.
23. Sozeau, *A New Look at Generalized Rewriting in Type Theory*, JFR 2009 -
    the rewriting machinery the quotient follow-up needs as an oracle.

**Proof engineering context**

24. Ringer, Yazdani, Leo & Grossman, *Adapting Proof Automation to Adapt
    Proofs*, CPP 2018 (PUMPKIN PATCH) - the search-based sibling.
25. Ringer, Palmskog, Sergey, Gligoric & Tatlock, *QED at Large: A Survey of
    Engineering of Formally Verified Software*, FnTPL 2019.
26. Talia Ringer's blog and talks (dependenttyp.es) - the accessible entry
    point to the whole line of work, and the best place to start if the papers
    feel dense.

---

## 10. Summary of what theory forced what

| Implementation fact | Forced by |
|---|---|
| Four configuration fields, not three or five | An inductive type *is* intro/elim/ι/η rules (§3) |
| `iota` entries have exactly the shape of `dep_elim`'s computation rule | They are that rule, demoted from `≡` to `=` (§4) |
| The `iota` table may be empty | ι holds definitionally when `dep_elim` is a real eliminator (§3, §4) |
| Rewriting via `e_Eq` with an abstracted motive | `J` is the only way to use a propositional equality (§4) |
| First-order matching, not higher-order | Rule variables occur applied to nothing; HOU is undecidable (§4) |
| η is definitional, not a propositional rewrite | Propositional η re-sticks one layer down, unboundedly (§5) |
| η requires **no indices** | Otherwise `Eq` becomes eligible and UIP/K falls out (§5) |
| η requires non-recursive fields | Otherwise expansion does not terminate (§5) |
| `Proj` is a primitive term former | An eliminator-encoded projection makes η fire on its own output (§5) |
| The target type must be written out by the user | Which presentation you want is a choice, not a consequence (§3) |
| No axioms are introduced by the engine | The whole point of not using univalence (§2) |
| The kernel decides; failures are ordinary type errors | No decompiler, no soundness forfeited for ergonomics (§8) |
