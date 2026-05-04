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
    { enableScripts: false },
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
</body>
</html>`;
}

export function registerInfoview(context: vscode.ExtensionContext): void {
  // open the panel whenever the user switches to a .lof file
  context.subscriptions.push(
    vscode.window.onDidChangeActiveTextEditor((editor) => {
      if (editor?.document.languageId === 'lof') {
        getOrCreatePanel();
      }
    }),
  );

  // also open immediately if a .lof file is already active at extension startup
  if (vscode.window.activeTextEditor?.document.languageId === 'lof') {
    getOrCreatePanel();
  }
}
