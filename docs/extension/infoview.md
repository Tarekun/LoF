# LoF Infoview Panel

A side panel that displays language output alongside the active `.lof` editor, modelled after the Lean 4 Infoview.

## Current state

The panel is scaffolded and functional as a VSCode WebviewPanel. It opens automatically whenever a `.lof` file becomes the active editor and currently renders a static placeholder string:

```
Hello from LoF
```

No live language data is wired up yet — the content is hardcoded in `infoview.ts`.

## Behaviour

| Scenario | Result |
|---|---|
| Open a `.lof` file | Panel opens beside the editor |
| Switch to a `.lof` file from another tab | Panel opens (or re-reveals) beside the editor |
| Switch away from a `.lof` file | Panel stays open |
| Close the panel manually | Panel is destroyed; reopens next time a `.lof` file is focused |
| Open a second `.lof` file | Existing panel is reused, not duplicated |

The panel opens with `preserveFocus: true` so the cursor stays in the source editor.

## Implementation

| File | Role |
|---|---|
| `vscode_extension/src/infoview.ts` | Panel lifecycle and HTML content |
| `vscode_extension/src/extension.ts` | Calls `registerInfoview(context)` at activation |

`registerInfoview` listens to `vscode.window.onDidChangeActiveTextEditor` and calls `getOrCreatePanel()` whenever the new active document has `languageId === 'lof'`. It also checks the active editor at startup so the panel appears immediately if a `.lof` file is already open.

The panel is identified by the view type `lofInfoview` and titled **LoF Infoview**.

## What is not implemented yet

- **Live output**: the panel content is static. It needs to be connected to the LSP server (or a separate protocol) to receive and display real language output such as goal states, type information, and proof progress.
- **Cursor tracking**: in a full infoview the displayed content updates as the cursor moves through the file. This requires the extension to send the current cursor position to the server and receive a response.
- **Rich formatting**: the current HTML is plain text. Goal states and type expressions will need syntax highlighting and structured layout.
