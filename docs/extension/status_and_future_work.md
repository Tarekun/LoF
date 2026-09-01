# Extension Status and Future Work

## Current State

The `lof-core` extension is at version 0.0.1 — a skeleton created from the standard VSCode extension generator. What exists and works:

- **Syntax highlighting** for `.lof` files via a TextMate grammar covering keywords (`axiom`, `lemma`, `theorem`, `inductive`, `fun`, `lambda`, `exact`, `intro`, `apply`, `import`, `match`, …), operators (`=>`, `->`, `|`), strings, hash comments, and basic identifier classes (lowercase variables, PascalCase types).
- **Language configuration**: comment toggling with `#`, bracket matching for `()` and `{}`.
- **A placeholder command** `lof-core.helloWorld` that displays an information message. This exists only as scaffolding.

There is currently no connection between the extension and the `proofr` language backend. All editor intelligence (diagnostics, hover, completion, proof state) is absent.

---

## Immediate Next Steps

These are concrete actions that can be taken now, each independently deliverable and directly useful to a developer working with `.lof` files.

### 1. Fix activation events

`package.json` has an empty `activationEvents` array. The extension should activate when a `.lof` file is opened:

```json
"activationEvents": ["onLanguage:lof"]
```

Without this, none of the programmatic features added in subsequent steps will fire.

### 2. Inline diagnostics via subprocess

The most impactful near-term feature: run `proofr check` on the current file on save and surface errors as red squiggles.

- Spawn `proofr check <file>` as a child process from `activate()`.
- Parse stdout/stderr for error locations (file, line, column, message).
- Push results to a `vscode.DiagnosticCollection`.

This requires defining a stable machine-readable output format for `proofr check` (JSON is the natural choice). That work belongs in the `language/` project. Even a simple line-based format (`file:line:col: message`) would be enough to start.

The subprocess approach avoids all LSP complexity while delivering the most visible user-facing value immediately.

### 3. Configurable path to `proofr`

Add a contribution to `package.json`:

```json
"configuration": {
  "lof.proofrPath": {
    "type": "string",
    "default": "proofr",
    "description": "Path to the proofr executable"
  }
}
```

This lets users point to a debug or release build without modifying extension code.

### 4. Remove the hello world command

Replace `lof-core.helloWorld` with a useful command such as `lof-core.checkFile` (run `proofr check` on the active document on demand) or `lof-core.openInteractive` (open a terminal running `proofr interactive`).

### 5. Improve the TextMate grammar

The grammar was written by hand for an early language snapshot. As the language stabilises, ensure:
- All tactic keywords are covered.
- Type universes and universe levels are highlighted distinctly.
- Proof blocks (`begin … qed`) are scoped so themes can style them differently from term definitions.

---

## Long-Term Goals

These require more design work and represent the full vision for the extension.

### LSP server in the language backend

A proper Language Server Protocol implementation inside `proofr` would enable everything below. Rust has mature LSP libraries (`tower-lsp`, `lsp-server`). The extension would then use `vscode-languageclient` to speak JSON-RPC to the server over stdio, gaining:

- **Live diagnostics** (incremental, not re-run on every save)
- **Hover** showing the inferred type of any expression
- **Go-to-definition** for lemmas, axioms, inductive types
- **Find all references**
- **Rename symbol**
- **Completion** for identifiers in scope

### Proof state panel

Interactive theorem proving produces an intermediate goal state (open hypotheses, current goal) that changes as tactics are applied. A dedicated webview panel showing the current proof state — updated as the cursor moves through a proof block — is the signature feature of proof assistant editors (cf. Lean's Infoview, Coq's Goals panel). This is a significant but high-value piece of work that depends on the LSP server.

### Workspace-aware checking

`proofr` operates on workspaces (directories of `.lof` files). The extension should understand workspace roots, re-check dependent files when an imported file changes, and respect the `config.yml` that controls which type system is active.

### Snippet and template support

Common proof patterns (`by induction`, `intro x; exact …`, inductive type skeletons) as VSCode snippets reduce boilerplate for new users.

### Semantic token highlighting

TextMate grammars are purely syntactic. An LSP server can provide semantic tokens that let the editor colour e.g. bound variables differently from free ones, or highlight unsolved goals visually.

### Testing infrastructure for the extension

The current test file is a placeholder. As features are added, integration tests should cover:
- Diagnostics appearing and clearing correctly.
- Commands executing without error.
- Grammar producing expected scopes for representative `.lof` snippets (snapshot tests using `vscode-tmgrammar-test`).
