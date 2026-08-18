'use strict';

// Paper citations in Lean docstrings, made clickable.
//
// A citation names a `\label`; `.citation-links.json` says which `.tex` holds that label
// and on which line; this turns the label into a DocumentLink that opens the paper there.
// The map is written by `tools/citation_links.py` (`make citation-links`), is gitignored,
// and names files by repository-relative path -- the absolute part is the workspace
// folder, joined here at click time, so nothing machine-specific is ever committed.
//
// `tools/check_citations.py` owns the citation grammar. Every form it recognises --
// prose, in-parenthesis, statement header, elided, and MAPPING.md rows -- carries the
// label in backticks, so matching the backticked label alone covers all five without
// restating them; that is also why no link can land in code, where a backticked
// `kind:label` is not syntax.

const vscode = require('vscode');
const fs = require('fs');
const path = require('path');

const MAP_NAME = '.citation-links.json';

// The label, as `check_citations.py` spells it (its `LABEL`), inside its backticks.
const LABEL = /`((?:hft:)?(?:def|ass|lem|cor|rem|alg|thm|prop):[a-z0-9-]+)`/g;

// The line span a citation may state after the label, on the same line: `, lines 522-530`
// or `, 1092-1101`. The dash class is the checker's `DASH`: en dash, em dash, hyphen.
const SPAN = /^,?\s*(?:lines?\s+)?(\d+)\s*[–—-]\s*(\d+)/;

/** The label map, and the workspace folder its relative paths are relative to. */
class LabelMap {
  constructor(log) {
    this.log = log;
    this.labels = {};
    this.root = null;
    this.warned = false;
  }

  /** Read the map from whichever workspace folder holds one. Never throws, never
      toasts: with no map there are simply no links, and the reason is logged once. */
  load() {
    this.labels = {};
    this.root = null;
    for (const folder of vscode.workspace.workspaceFolders || []) {
      const file = path.join(folder.uri.fsPath, MAP_NAME);
      if (!fs.existsSync(file)) continue;
      try {
        const parsed = JSON.parse(fs.readFileSync(file, 'utf8'));
        this.labels = parsed.labels || {};
        this.root = folder.uri.fsPath;
        this.warned = false;
        this.log.appendLine(
          `loaded ${Object.keys(this.labels).length} labels from ${file}`);
        return;
      } catch (err) {
        this.log.appendLine(`could not read ${file}: ${err}`);
      }
    }
    if (!this.warned) {
      this.warned = true;
      this.log.appendLine(
        `no ${MAP_NAME} in any workspace folder; run "make citation-links" to arm the ` +
        'citation links');
    }
  }

  /** Where a label is defined: absolute path and 1-based line, or null. */
  lookup(label) {
    const where = this.labels[label];
    if (!where || !this.root) return null;
    return {
      file: path.join(this.root, where.file),
      shown: where.file,
      line: where.line,
      span: where.span || null,
    };
  }
}

/** A link target that opens `file` at `line`.
    A `command:` URI rather than a `file:` URI with an `L<n>` fragment: the fragment form
    could not be verified headlessly, and the plan this was built from says not to ship it
    unverified. The command below reveals the line explicitly, which needs no such check. */
function openAt(file, line) {
  const args = encodeURIComponent(JSON.stringify([file, line]));
  return vscode.Uri.parse(`command:decoupledCitations.open?${args}`);
}

/** The links in one document: one per backticked label, plus one per stated line span. */
function linksIn(document, map) {
  const links = [];
  for (let lineNo = 0; lineNo < document.lineCount; lineNo++) {
    const text = document.lineAt(lineNo).text;
    LABEL.lastIndex = 0;
    let match;
    while ((match = LABEL.exec(text)) !== null) {
      const where = map.lookup(match[1]);
      if (!where) continue;

      // The label itself, backticks excluded so the link reads as the label.
      const from = match.index + 1;
      const label = new vscode.DocumentLink(
        new vscode.Range(lineNo, from, lineNo, from + match[1].length),
        openAt(where.file, where.line));
      label.tooltip = `${where.shown}:${where.line}`;
      links.push(label);

      // A line span stated right after it points at the same place; linking it too means
      // the numbers a reader actually looks at are the ones that are clickable.
      const after = match.index + match[0].length;
      const span = SPAN.exec(text.slice(after));
      if (span) {
        const start = after + span[0].indexOf(span[1]);
        const stop = after + span[0].length;
        const range = new vscode.DocumentLink(
          new vscode.Range(lineNo, start, lineNo, stop),
          openAt(where.file, Number(span[1])));
        range.tooltip = `${where.shown}:${span[1]}`;
        links.push(range);
      }
    }
  }
  return links;
}

function activate(context) {
  const log = vscode.window.createOutputChannel('Paper citations');
  const map = new LabelMap(log);
  map.load();

  context.subscriptions.push(log);

  context.subscriptions.push(vscode.commands.registerCommand(
    'decoupledCitations.open', async (file, line) => {
      const doc = await vscode.workspace.openTextDocument(vscode.Uri.file(file));
      const editor = await vscode.window.showTextDocument(doc, { preview: false });
      const at = new vscode.Position(Math.max(0, line - 1), 0);
      editor.selection = new vscode.Selection(at, at);
      editor.revealRange(new vscode.Range(at, at), vscode.TextEditorRevealType.InCenter);
    }));

  context.subscriptions.push(vscode.commands.registerCommand(
    'decoupledCitations.reload', () => map.load()));

  // `make citation-links` rewrites the map; pick the new one up without a reload.
  const watcher = vscode.workspace.createFileSystemWatcher(`**/${MAP_NAME}`);
  watcher.onDidCreate(() => map.load());
  watcher.onDidChange(() => map.load());
  watcher.onDidDelete(() => map.load());
  context.subscriptions.push(watcher);

  context.subscriptions.push(vscode.workspace.onDidChangeWorkspaceFolders(
    () => map.load()));

  context.subscriptions.push(vscode.languages.registerDocumentLinkProvider(
    [{ language: 'lean4' }, { language: 'lean' }, { pattern: '**/*.lean' }],
    { provideDocumentLinks: (document) => linksIn(document, map) }));
}

function deactivate() {}

module.exports = { activate, deactivate, linksIn, LABEL, SPAN };
