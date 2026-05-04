// this file is the extension entry point — it runs inside the vscode extension host process.
// its only job is to start the language server and hand vscode a LanguageClient to talk to it.

import * as path from 'path';
import * as vscode from 'vscode';
import {
  LanguageClient,
  LanguageClientOptions,
  ServerOptions,
  TransportKind,
} from 'vscode-languageclient/node';
import { registerInfoview } from './infoview';

let client: LanguageClient;

export function activate(context: vscode.ExtensionContext) {
  // server.ts is compiled to out/server.js — that's the module vscode will spawn as a child process
  const serverModule = context.asAbsolutePath(path.join('out', 'server.js'));

  const serverOptions: ServerOptions = {
    // in normal use: launch server.js as a node module, talking to us over IPC
    run: { module: serverModule, transport: TransportKind.ipc },
    // in debug mode: same, but also open the node inspector on port 6009 so you can
    // attach the VS Code debugger to the server process via the "Attach to Server" launch config
    debug: {
      module: serverModule,
      transport: TransportKind.ipc,
      options: { execArgv: ['--nolazy', '--inspect=6009'] },
    },
  };

  const clientOptions: LanguageClientOptions = {
    // only activate the LSP for .lof files — other file types are untouched
    documentSelector: [{ scheme: 'file', language: 'lof' }],
  };

  // create the client — this does NOT start it yet, just configures it
  client = new LanguageClient('lof-core', 'LoF Core', serverOptions, clientOptions);

  // start() spawns server.js as a child process and begins the LSP handshake
  client.start();

  // ensure the server process is killed when the extension is deactivated or the window closes
  context.subscriptions.push({ dispose: () => client.stop() });

  registerInfoview(context);
}

export function deactivate(): Thenable<void> | undefined {
  // stop() sends a shutdown request to the server and then kills the process
  return client?.stop();
}
