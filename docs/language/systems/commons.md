# Commons — Shared Type Theory Algorithms

`language/src/type_theory/commons/`

The commons module contains implementations of type-theoretic algorithms that are genuinely system-independent. These are generic Rust functions parameterized over `T: TypeTheory + …` bounds, not duplicated code.

Every fallible function in this module returns `Result<_, LofError>` (`language/src/error.rs`), a `thiserror`-based enum of structured variants (`UnboundName`, `TypeMismatch`, `ArityMismatch`, `UnificationFailure`, `OccursCheckCyclic`, `OccursCheckInTerm`, `ConflictingSubstitution`, `UnsupportedConstruct`, `InvalidAstNode`, …) built through matching constructors (e.g. `LofError::unbound_variable(name)`, `LofError::type_mismatch(context, expected, found)`) rather than ad-hoc `format!`ed `String`s.

## `type_check.rs`

### Expression checkers

**`type_check_variable<T>`**

The standard VAR rule: `Γ ∋ x:A ⊢ x:A`. Looks up `var_name` in the context and returns its type, or errors with `LofError::unbound_variable(var_name)` (renders as `"Unbound variable: {name}"`).

**`type_check_abstraction<T, C>`**

```
Γ ⊢ A : s    Γ, x:A ⊢ b : B
─────────────────────────────
     Γ ⊢ λx:A.b : A→B
```

Type checks the domain `A`, then checks the body `b` under `x:A`. The constructor `C` builds the return type from `(var_name, A, B)` — FOL builds `Arrow(A, B)`, CIC builds `Product(x, A, B)`.

Does not support metavariable resolution. See `i_type_check_abstraction` for that.

**`i_type_check_abstraction<T, C>`** (requires `Refiner`, renamed from `u_type_check_abstraction`)

Same rule but supports inference: after type checking the domain `A` and the body `b`, it collects unification constraints from both — `T::type_collect_unifications(A, env)` and `T::term_collect_unifications(b, env)` — concatenates them, solves the combined list with `T::solve_unifications`, and applies the resulting `Substitution` to both `A` and the body's type via `T::type_apply_unifier` before constructing the return type. Constraint collection is stateless (no constraints are accumulated on the `Environment` itself); they're threaded explicitly through these calls as `Vec<(Exp, Exp)>`.

**`type_check_application<T, F>`**

```
Γ ⊢ f : A→B    Γ ⊢ a : A
──────────────────────────
     Γ ⊢ f a : B
```

The `unpack_fun_type: F` closure extracts `(domain, codomain)` from a function type. Returns the codomain if `domain = arg_type`, otherwise errors with `LofError::type_mismatch("function application", …)`; applying to a non-function errors via `LofError::custom`. Does not handle dependent types.

**`i_type_check_application<T, F, R, S>`** (requires `Refiner`, renamed from `u_type_check_application`)

Same rule, but supports both inference of implicit types and term-dependent codomains:
1. `unpack_fun_type: F` now also extracts the bound variable name from the function type: `(var_name, domain, codomain)`.
2. Rather than checking `domain = arg_type` directly, it rebuilds the whole application term via the new `repack_application: R` closure (`f a` from `left`/`right`) and calls `T::term_collect_unifications` on it — the domain/argument compatibility check is implicit in these constraints, collected as a side effect of walking the rebuilt application (see the comment in `i_type_check_application` noting this).
3. Solves the constraints with `T::solve_unifications`, substitutes the argument into the codomain via `substitute_type: S` for the dependent case (`B[arg/x]`), then applies the solved substitution to the result via `T::type_apply_unifier`.

**`type_check_fo_universal<T>`**

```
Γ ⊢ A : s    Γ, x:A ⊢ P : s'
──────────────────────────────
     Γ ⊢ ∀x:A.P : s'
```

Type checks `A`, extends context, type checks `P`. Used for CIC's `Product` (dependent type / Π-type) and FOL's `ForAll`.

**`type_check_let<T>`**

Type checks the body, verifies the declared type matches (if given), extends the environment via `with_local_substitution`, and returns the type of the scope expression.

### Statement checkers

**`type_check_global<T>`**

Checks the body term, verifies the declared type unifies with it, then calls `evaluate_global` to add the name and definition to the environment.

**`type_check_function<T, C, E>`**

Builds the function type from arguments and return type via the `constructor` closure. Under the assumption of all arguments (plus the function itself for recursive cases), type checks the body and verifies it matches the declared return type. Then calls `evaluate_fun` to add the curried function to the environment.

**`type_check_axiom<T>`**

Checks the formula is a well-formed type, then calls `evaluate_axiom` to add the name to the context.

**`eq_type_check_theorem<T>`** (requires `Interactive`) / **`u_type_check_theorem<T>`** (requires `Interactive + Refiner`)

Replace the old single `type_check_theorem<T>`. Both take the same shape (`theorem_name`, `formula`, `proof: Union<Term, Vec<Tactic<Exp>>>`) and delegate to a shared private `type_check_theorem_base<T, P>`, parametric over a compatibility closure `P: FnMut(&Type, &Type, &mut Environment<T>) -> bool`:
- `eq_type_check_theorem` passes `T::base_type_equality` as the compatibility check.
- `u_type_check_theorem` passes `T::types_unify` (unification-based comparison against the target formula) as the compatibility check.

`type_check_theorem_base` handles both proof styles:
- **Term proof**: type checks the proof term, verifies it's compatible with `formula` via the closure.
- **Tactic proof**: delegates to `type_check_interactive_proof`, then verifies the resulting proof term's type against `formula` (currently not enforced as a hard failure for tactic proofs — see the `TODO` in the source).

In both cases, on success it now unconditionally calls `evaluate_theorem` to register `theorem_name` in the environment — previously this only happened for term-mode proofs, and `u_type_check_theorem` used to run against a cloned environment so the registration never reached the caller's real environment; both were fixed so `theorem_name` is always registered in the environment the caller passed in.

**`type_check_auto<T>`**

Only validates the formula is well-formed. Actual automation runs in the evaluation phase.

**`type_check_interactive_proof<T>`** (internal)

Drives the tactic loop: starts with `[target]` as the goal stack and `proof_hole()` as the partial proof. Each step calls `type_check_tactic`, appends new subgoals to the stack, and updates the partial proof. Terminates when the tactic list is exhausted or no subgoals remain.

## `evaluation.rs`

Generic statement evaluation functions that add definitions to the environment. Each returns `()` — side effects only.

**`generic_term_normalization<T, F>`**

Fixed-point normalization: calls `one_step_reduction: F` repeatedly until the term is unchanged. The reduction function is system-specific and passed as a parameter. Takes the `Environment<T>` by shared reference (`&Environment<T>`, not `&mut`) — normalization no longer needs to mutate the environment now that constraint solving is stateless, so `one_step_reduction: F` is `Fn(&Environment<T>, &T::Term) -> T::Term`.

**`evaluate_global<T>`**

Adds a global definition: `name ↦ body` in deltas, `name: type` in context (if a type is given).

**`evaluate_fun<T, C, E>`**

Wraps the function body in `Abstraction`s for each argument (via `eta_wrap`), then adds the result as a substitution. Builds the curried function type via `constructor`.

**`evaluate_axiom<T>`**

Adds the axiom name to the context with the given formula as its type.

**`evaluate_theorem<T>`**

Adds the theorem name to the context with `formula` as its type. The `proof` argument is currently unused (`_proof`) — it is not stored in deltas.

**`evaluate_auto<T, C, S, G>`** / **`evaluate_solve<T, C, S, G>`** (require `Kernel`)

Both delegate to the private `saturation_interface<T, C, S, G>`, which builds a SUP clause set and runs `Sup::saturate`:
- `clausify: C` — `Fn(&Type, &HashSet<String>) -> Result<Vec<SupFormula>, LofError>`, clausifies a formula given the set of constant names.
- `term_to_sup: S` — `Fn(&Term, &HashSet<String>) -> Result<SupTerm, LofError>`, converts a term into its SUP-term representation (new parameter; previously these functions took only `clausify` and `complement`).
- `complement: G` — `Fn(&Type) -> Type`, negates a goal formula so it can be refuted by saturation.

`saturation_interface` clausifies every type in `environment.get_context()`, and — new — for every `(var_name, body)` in `environment.get_deltas()` it also type checks `body`, clausifies its type, and pushes an explicit equality clause `var_name = term_to_sup(body)`, so delta-bound (`let`/`def`) definitions participate in resolution both through their type and through their value. It then clausifies `complement(goal)` for each goal and saturates. Selection and clause-giving functions now come from `global_config()` rather than being hardcoded.

`evaluate_auto` calls this with a single-element goal vector (`target`) and only reports success/failure; `evaluate_solve` calls it with the full `goals` vector and prints the resulting `Substitution<SupTerm>` of variable bindings. FOL's call sites changed accordingly, e.g. `evaluate_solve::<Fol, _, _, _>(env, goals, clausify, term_to_sup, negate_fn)`.

## `unification.rs`

**`Substitution<T>`**

A `HashMap<String, T>` wrapper with extra operations:
- `Substitution::empty()` — empty substitution
- `merge(other)` — union of two substitutions (last write wins on conflict)
- `reduce(f)` — applies a substitution function to all values in place
- `resolvent(var_name)` — looks up the computed value for a query variable
- `names()` — iterator over bound variable names

**`unify<T>`**

Hindley-Milner unification algorithm:
1. Check structural equality
2. If one side is a variable (meta), bind it (occurs check)
3. Recurse on children

Returns `Result<Substitution<T>, LofError>`. Delegates to `unify_with_base` starting from `Substitution::empty()`.

**`unify_with_base<T>`**

Same as `unify`, but takes an existing `mgu: &mut Substitution<T>` to build the unification on top of instead of starting from an empty one — lets callers accumulate a substitution across a sequence of unification calls. Wraps the single `(exp1, exp2)` pair into a one-element constraint queue and calls `ucs`.

**`ucs<T>`** (Unification Constraint Solver)

The recursive core both `unify` and `unify_with_base` bottom out in (renamed and made `pub`, from a private `solver` function, specifically to expose this entrypoint). Takes the base `mgu` plus a `VecDeque<(T, T)>` queue of constraints directly, so callers that already have a batch of pairwise constraints to solve — e.g. a system's `Refiner::solve_unifications` implementation — can hand them to `ucs` in one go instead of unifying pairs one at a time. Per constraint it pops the front pair and: binds it if either side is a variable (occurs-checked), recurses on exploded children if structurally equal, or fails with `LofError::unification_failure`.

## `elaboration.rs`

**`elaborate_ast_vector<T>`**

Elaborates a `Vec<LofAst>` into a `Schedule<T>` by mapping each node.

**`elaborate_file_root<T>`** / **`elaborate_dir_root<T>`**

Handles the `FileRoot`/`DirRoot` wrappers produced by the parser.

**`elaborate_tactic<T>`**

Converts a `Tactic<Expression>` to `Tactic<T::Exp>` by elaborating the embedded expressions.

## `utils.rs`

**`generic_multiarg_fun_type<T>`**

Given `[(x1:A1), (x2:A2), …]` and return type `B`, builds the curried function type `A1 → A2 → … → B` using the type theory's `Arrow` or `Product` constructor.

**`wrap_term<T>`** / **`wrap_type<T>`**

Lift a `T::Term` / `T::Type` into `T::Exp` using `Union::L` / `Union::R`.

**`eta_expand<T>`**

Given a term and a list of argument names, wraps the term in `Abstraction`s for each argument.
