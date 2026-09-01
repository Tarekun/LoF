// manages the LoF Infoview panel — a side panel that shows language output,
// modelled after Lean's infoview. currently displays a static placeholder.

import * as vscode from 'vscode';

let panel: vscode.WebviewPanel | undefined;

function getOrCreatePanel(): vscode.WebviewPanel {
  if (panel) {
    panel.reveal(vscode.ViewColumn.Beside, /* preserveFocus */ true);
    return panel;
  }

  panel = vscode.window.createWebviewPanel(
    'lofInfoview',
    'LoF Infoview',
    { viewColumn: vscode.ViewColumn.Beside, preserveFocus: true },
    { enableScripts: true },
  );

  panel.webview.html = buildHtml();

  // clear the reference when the user closes the panel so it can be recreated next time
  panel.onDidDispose(() => { panel = undefined; });

  return panel;
}

function buildHtml(): string {
  return /* html */`<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8">
  <style>
    body {
      font-family: var(--vscode-font-family);
      font-size: var(--vscode-font-size);
      color: var(--vscode-foreground);
      background: var(--vscode-editor-background);
      padding: 1rem;
      margin: 0;
    }
  </style>
</head>
<body>
  <!-- TODO: replace static string with real language output once the infoview protocol is wired up -->
  <p>Hello from LoF</p>
  <pre id="content" style="white-space: pre-wrap; margin: 0;"></pre>
  <script>
    window.addEventListener('message', (event) => {
      document.getElementById('content').textContent = event.data.content;
    });
  </script>
</body>
</html>`;
}

function postCursor(document: vscode.TextDocument, position: vscode.Position): void {
  // collect everything from the start of the file up to (but not including) the cursor.
  // this mirrors Lean's infoview model: only the content before the cursor is relevant for
  // computing the current goal state — future work will send this slice to the language server.
  const content = document.getText(new vscode.Range(new vscode.Position(0, 0), position));
  panel?.webview.postMessage({ content });
}

export function registerInfoview(context: vscode.ExtensionContext): void {
  // open the panel whenever the user switches to a .lof file
  context.subscriptions.push(
    vscode.window.onDidChangeActiveTextEditor((editor) => {
      if (editor?.document.languageId === 'lof') {
        getOrCreatePanel();
        postCursor(editor.document, editor.selection.active);
      }
    }),
  );

  // update the cursor line on every selection/cursor change inside a .lof file
  context.subscriptions.push(
    vscode.window.onDidChangeTextEditorSelection((e) => {
      if (e.textEditor.document.languageId === 'lof') {
        postCursor(e.textEditor.document, e.selections[0].active);
      }
    }),
  );

  // also open immediately if a .lof file is already active at extension startup
  const active = vscode.window.activeTextEditor;
  if (active?.document.languageId === 'lof') {
    getOrCreatePanel();
    postCursor(active.document, active.selection.active);
  }
}
