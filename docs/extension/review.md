# Extension Review

This document examines the extension project critically — what is worth keeping, what should be reconsidered, and what pitfalls to anticipate. The project is early enough that architectural pivots cost very little.

---

## What the project is now

A scaffold. The extension registers a language ID (`lof`), associates it with `.lof` files, applies a hand-written TextMate grammar, and contributes a hello-world command. There is no connection to the language backend and no programmatic editor behaviour at all. The TypeScript source is essentially the generator output, untouched.

This is not a criticism — it is the correct state for an extension at the start of language development, where the language itself is still in flux. The risk is letting the scaffold sit for too long and adding features piecemeal without a clear model of what the extension should ultimately be.

---

## Things to reevaluate

### The subprocess approach vs. LSP from the start

The most tempting first step is to spawn `proofr check` on save and pipe errors into a diagnostic collection. It is fast to implement and immediately useful. However:

- It requires `proofr` to produce stable, machine-readable output. That output format becomes an implicit API between two projects in the same repo, and changing it later means coordinating two sides.
- Subprocess-based diagnostics are inherently file-level and stateless. The language is workspace-aware; the extension eventually needs to understand dependency graphs between files.
- You will likely implement a proper LSP server at some point. At that point the subprocess code becomes dead weight that has to be carefully removed.

The alternative is to skip the subprocess step entirely and build toward an LSP server in `proofr` from the start, even if the server initially does nothing more than publish diagnostics. This is more upfront work but avoids a design dead end. Given the language is in Rust and has mature LSP crates available (`tower-lsp`, `lsp-server`), this is worth serious consideration.

If you do take the subprocess route, treat it explicitly as a temporary measure: keep it behind a feature flag or a clearly marked "legacy" code path so it can be removed cleanly.

### The extension name and identifier

The extension is named `lof-core` with publisher `undefined-publisher`. Before any real distribution, these need to be settled. More importantly, the language is called "LoF" in the grammar and documentation but the `proofr` binary uses a different name. The relationship between the language name and the tool name should be made consistent across the repo, because the extension manifest, grammar scope names (`source.lof`), file associations (`.lof`), and CLI name all encode this identity and are painful to rename later.

### The TextMate grammar maintenance burden

TextMate grammars are fragile. They are regex-based, have no knowledge of language semantics, and must be updated by hand whenever syntax changes. Consider two mitigations:

1. Write a test suite for the grammar now, before it grows. [`vscode-tmgrammar-test`](https://github.com/PanAeon/vscode-tmgrammar-test) lets you write snapshot tests asserting which scopes are applied to which tokens. Without tests, every grammar change is a manual visual check.
2. Decide how much effort to invest in the TextMate grammar vs. moving to semantic tokens (which come from an LSP server and are more accurate). The TextMate grammar will always be needed as a fallback for files opened before the LSP starts, but it does not need to be exhaustive.

### The activation model

The current `activationEvents: []` means the extension does nothing until a command is manually run. For a language extension this is wrong — it should activate on `onLanguage:lof`. This is a trivial fix but it signals that the activation model has never been thought through. When the extension starts doing real work (running `proofr`, starting an LSP server), activation latency and ordering will matter. Think about this early: should the LSP server start eagerly on activation, or lazily on first document open?

### Testing

The test file is a placeholder with trivial assertions. This is fine for now, but there is a subtle trap: the VSCode test harness (`@vscode/test-electron`) is slow and environment-dependent. It is worth deciding what belongs in extension integration tests vs. what should be tested in the language backend directly. Diagnostics accuracy, for example, is better tested by testing `proofr`'s output format directly rather than standing up a full VSCode instance.

---

## Structural decisions to make before committing

**1. Who owns the protocol?**  
If you go the subprocess route, `proofr`'s output format is the protocol. If you go LSP, the language client/server split is the protocol. Either way, document the protocol contract explicitly before building both sides.

**2. Where does proof state live?**  
The interactive prover maintains a goal stack that changes as tactics are applied. When an LSP server exists, this state should live in the server (it has the full elaborated term). The extension is then purely a display layer. Avoid putting any proof logic in the TypeScript side — it will diverge from the Rust implementation.

**3. Webview vs. panel API for proof state display**  
When you build the goal panel, you will choose between a `WebviewPanel` (full HTML/CSS/JS, maximum flexibility) and native VSCode panel contributions. Webviews are more powerful but introduce a separate mini-frontend with its own state synchronisation complexity. For a proof state display that is essentially a structured text view, native panels or even `OutputChannel` may be sufficient initially and are much simpler to implement and reason about.

**4. Multi-root workspace support**  
VSCode supports workspaces with multiple root folders. The `proofr` workspace concept maps to a single directory. Decide early whether the extension will support multi-root workspaces or explicitly scope itself to a single root, because this affects how you resolve file paths and how you configure the LSP server.

---

## Pitfalls to keep in mind

**Path resolution across platforms.** The extension runs on Windows, macOS, and Linux. Any code that constructs a path to `proofr`, to a workspace root, or to a `.lof` file must use `vscode.Uri` and `path.join` — never string concatenation. The current codebase has no path code at all, so this is clean, but it is easy to introduce bugs here on the first pass.

**Long-running processes and disposal.** If the extension spawns `proofr` as a child process or starts an LSP server, those processes must be killed in `deactivate()`. Leaked processes are invisible to the user and accumulate across Extension Development Host reload cycles, causing confusing behaviour during development. VSCode's `ExtensionContext.subscriptions` array handles disposal automatically for disposables — use it.

**Error handling in async extension code.** VSCode extension APIs are heavily Promise-based. Unhandled rejections in extension code produce cryptic "extension host terminated unexpectedly" errors. All async paths should have explicit error handling and surface failures to the user via `vscode.window.showErrorMessage` or a status bar item, not silently.

**Grammar scope naming.** The TextMate scope `source.lof` is correct. Take care that sub-scopes follow the TextMate convention (`keyword.control.lof`, `entity.name.function.lof`, etc.) rather than inventing a flat scheme. Themes apply colour rules by matching scope name prefixes — a non-standard scheme means `.lof` files will be unstyled in most themes.

**The `undefined-publisher` placeholder.** The `publisher` field in `package.json` is `undefined-publisher`. If this extension is ever packaged or published before being changed, the identifier `undefined-publisher.lof-core` becomes the stable extension ID that users will have installed — it cannot be changed without a breaking migration. Fix this before any distribution.
