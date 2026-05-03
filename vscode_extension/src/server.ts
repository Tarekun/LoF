// the language server runs as a separate node process and communicates with the
// extension host over ipc using the language server protocol (LSP).
// vscode spawns this file via the serverOptions defined in extension.ts.

import * as path from 'path';
import { existsSync } from 'fs';
import { spawnSync } from 'child_process';
import {
  createConnection,
  TextDocuments,
  ProposedFeatures,
  InitializeParams,
  TextDocumentSyncKind,
  Diagnostic,
  DiagnosticSeverity,
  Range,
} from 'vscode-languageserver/node';
import { TextDocument } from 'vscode-languageserver-textdocument';
import { URI } from 'vscode-uri';

// the connection object is the two-way channel to the vscode extension host.
// ProposedFeatures.all enables workspace config, file watching, etc. on top of the base LSP spec.
const connection = createConnection(ProposedFeatures.all);

// TextDocuments manages open document state so we get notified on open/save/close
const documents: TextDocuments<TextDocument> = new TextDocuments(TextDocument);

// tell the client what this server can do — for MVP, we only need full-sync text documents
connection.onInitialize((_params: InitializeParams) => ({
  capabilities: {
    // full sync means the server receives the complete file content on every open/save.
    // incremental sync (sending only diffs) can be added later if performance becomes a concern.
    textDocumentSync: TextDocumentSyncKind.Full,
  },
}));

// TODO: replace these hardcoded paths with configurable lof.proofrPath / lof.configPath settings.
// for now we point directly at the debug build and the config next to it.
const exeName = process.platform === 'win32' ? 'proofr.exe' : 'proofr';
// __dirname is vscode_extension/out/ after compilation, so ../../language/target/debug/ is correct
const proofrBin = path.join(__dirname, '..', '..', 'language', 'target', 'debug', exeName);
const proofrConfig = path.join(__dirname, '..', '..', 'language', 'config.yml');

// strip ANSI color/style escape sequences so the message reads cleanly in the Problems panel
function stripAnsi(text: string): string {
  // matches escape sequences like \x1b[31m, \x1b[0m, \x1b[2m, etc.
  return text.replace(/\x1b\[[0-9;]*m/g, '');
}

// extract just the meaningful part of a proofr error message.
// proofr logs "[timestamp] ERROR Program failed: <reason>" — we only want <reason>.
function extractMessage(raw: string): string {
  const cleaned = stripAnsi(raw).trim();

  // look for the "Program failed:" marker that proofr always emits on errors
  const marker = 'Program failed: ';
  const idx = cleaned.indexOf(marker);
  if (idx !== -1) {
    return cleaned.slice(idx + marker.length).trim();
  }

  // fall back to the full cleaned output if the marker isn't there
  return cleaned || 'type checking failed (no output from proofr).';
}

// run `proofr check <file>` and turn the result into a vscode diagnostic.
// the diagnostic is published back to the client, which shows it in the Problems panel.
function check(uri: string, fsPath: string): void {
  // guard against a missing binary — gives a clearer error than a cryptic spawn failure
  if (!existsSync(proofrBin)) {
    connection.sendDiagnostics({
      uri,
      diagnostics: [{
        severity: DiagnosticSeverity.Error,
        range: Range.create(0, 0, 0, 0),
        message: `proofr binary not found at ${proofrBin} — run \`cargo build\` inside language/`,
        source: 'proofr',
      }],
    });
    return;
  }

  // set cwd to the file's parent directory so that relative `import` statements in .lof files
  // resolve correctly (e.g. `import "unit"` in bool.lof looks for unit.lof next to bool.lof)
  const cwd = path.dirname(fsPath);

  const result = spawnSync(
    proofrBin,
    ['check', fsPath, '--config', proofrConfig],
    { encoding: 'utf8', cwd },
  );

  // proofr may write errors to stdout or stderr — collect both
  const output = (result.stdout ?? '') + (result.stderr ?? '');

  const diagnostics: Diagnostic[] = [];

  // proofr exits with code 0 even on type errors — detect failures by output content instead.
  // the error logger always writes a line containing "Program failed:" when checking fails.
  const hasError = output.includes('Program failed:');

  if (hasError) {
    // anchor at (0,0) — this is the whole-file position vscode uses when no line info is available.
    // it shows up in the Problems panel and as a red dot in the Explorer, which is our MVP target.
    // precise line/column positioning can be added once proofr emits structured location data.
    diagnostics.push({
      severity: DiagnosticSeverity.Error,
      range: Range.create(0, 0, 0, 0),
      message: extractMessage(output),
      source: 'proofr',
    });
  }

  // sending an empty array here clears any previously published errors for this file
  connection.sendDiagnostics({ uri, diagnostics });
}

// fire the checker whenever the user opens a .lof file or saves it
documents.onDidOpen((e) => {
  // URI.parse().fsPath gives a safe cross-platform path — on windows, new URL().pathname
  // produces /C:/... which confuses win32 APIs, but vscode-uri handles it correctly
  check(e.document.uri, URI.parse(e.document.uri).fsPath);
});

documents.onDidSave((e) => {
  check(e.document.uri, URI.parse(e.document.uri).fsPath);
});

// connect the document manager and start listening for LSP messages
documents.listen(connection);
connection.listen();
