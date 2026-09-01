# VSCode Extension Developer Guide

This document covers how to set up, run, and test the `lof-core` VSCode extension locally.

## Prerequisites

- [Node.js](https://nodejs.org/) 18 or later (includes npm)
- [Visual Studio Code](https://code.visualstudio.com/) 1.97 or later
- A working build of the `proofr` CLI (see the `language/` project)

## Project Structure

```
vscode_extension/
├── src/
│   ├── extension.ts          # Entry point — activate() and deactivate()
│   └── test/
│       └── extension.test.ts # Mocha test suite
├── syntaxes/
│   └── lof.tmLanguage.json   # TextMate grammar for .lof syntax highlighting
├── language-configuration.json  # Comment/bracket config for the lof language
├── package.json              # Extension manifest, contributes, scripts
├── tsconfig.json             # TypeScript compiler config (out → out/)
├── .vscode/
│   ├── launch.json           # Debug launch configuration
│   └── tasks.json            # Build tasks wired to npm scripts
└── .vscode-test.mjs          # Test runner configuration
```

## Setup

From the `vscode_extension/` directory:

```sh
npm install
```

This installs all dev dependencies (TypeScript, ESLint, the VSCode test harness).

## Running the Extension

The recommended workflow is to open `vscode_extension/` as the workspace in VSCode and press **F5**. This:

1. Runs the `npm: watch` pre-launch task, which compiles TypeScript incrementally to `out/`.
2. Opens a new **Extension Development Host** window — a fresh VSCode instance with your extension loaded.
3. Any `.lof` file opened in the host window will receive syntax highlighting from the TextMate grammar.

Alternatively, compile once and launch manually:

```sh
npm run compile       # one-shot compile
code --extensionDevelopmentPath=$PWD  # open VSCode with extension loaded
```

### Triggering the extension

Currently the extension only activates when the `lof-core.helloWorld` command is run (open the Command Palette with Ctrl+Shift+P and search "Hello World"). Syntax highlighting for `.lof` files is always active via the grammar contribution regardless of activation state.

## Compiling

```sh
npm run compile   # compile once
npm run watch     # recompile on every change (recommended during development)
```

Output goes to `out/` (TypeScript target ES2022, module system Node16).

## Linting

```sh
npm run lint
```

Uses ESLint with `@typescript-eslint` rules. The project enforces strict equality, curly braces, and semicolons. Fix lint errors before committing; the `pretest` script runs lint automatically before any test run.

## Running Tests

```sh
npm test
```

This runs `pretest` (compile + lint) then invokes `@vscode/test-cli` / `@vscode/test-electron`, which launches a headless VSCode instance and executes the Mocha suite in `src/test/extension.test.ts`. Test output appears in the terminal.

You can also run tests from within VSCode using the **Testing** sidebar panel (populated by the `@vscode/test-cli` configuration in `.vscode-test.mjs`).

## Packaging

To produce a `.vsix` file for local installation:

```sh
npm install -g @vscode/vsce
vsce package
```

Install the resulting `.vsix` directly in VSCode via **Extensions → Install from VSIX**.

The `.vscodeignore` file excludes source files, tests, and maps from the package — only the compiled `out/` directory and static assets are bundled.

## Connecting to the Language Backend

The `proofr` binary (built from `language/`) is the proof checker. To build it:

```sh
cd ../language
cargo build           # debug build → language/target/debug/proofr
cargo build --release # release build → language/target/release/proofr
```

The key CLI entry points relevant to editor integration are:

| Command | What it does |
|---|---|
| `proofr check <file-or-dir>` | Parse + type-check; exits non-zero on error |
| `proofr parse <file-or-dir>` | Parse only |
| `proofr run <file-or-dir>` | Full execution |
| `proofr interactive` | REPL |

The extension does not yet invoke `proofr` — wiring this up is the most impactful next step (see `status_and_future_work.md`).

## Useful References

- [VSCode Extension API](https://code.visualstudio.com/api)
- [Language Server Protocol specification](https://microsoft.github.io/language-server-protocol/)
- [TextMate grammar reference](https://macromates.com/manual/en/language_grammars)
- [`vscode-languageclient` npm package](https://www.npmjs.com/package/vscode-languageclient)
