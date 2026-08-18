# Paper citations, made clickable

A local VS Code extension: in a `.lean` file, ctrl+click a citation's label — or the line
span beside it — and the cited `.tex` opens at the cited line.

```
/-- Definition 48 (`def:height-vote-rule`, lines 1952–1981): the current-height signing
                    ^^^^^^^^^^^^^^^^^^^^         ^^^^^^^^^
                    both of these are links, both open recovery_core.tex at line 1952
```

Nothing in the Lean files changes: the citations were already there, and `make cites`
already checks them. This only makes them navigable.

## Arm it

```sh
make citation-links      # writes .citation-links.json, which the extension reads
```

That file is gitignored and derived from the `latex-specs` submodule. Regenerate it after
the submodule moves; the extension notices the rewrite and reloads without a restart.

## Install it

No marketplace publishing. Either:

* **symlink or copy this folder** into `~/.vscode/extensions/` and restart VS Code — a
  folder with a valid `package.json` is loaded from there, no packaging step; or
* `npx vsce package` here and install the resulting `.vsix` through
  *Extensions → … → Install from VSIX*.

There is no build step and no dependency: `extension.js` is the whole extension.

## How it works, and the two things worth knowing

`tools/citation_links.py` writes `.citation-links.json`: for every `\label` in either
paper, the repository-relative `.tex` path and the line the label sits on. The extension
joins the workspace folder to that relative path at click time, which is why no absolute
path is ever committed — the same device `mapping.html` uses for its jump links.

**The grammar has one owner.** `tools/check_citations.py` defines and checks the citation
forms; the extension does not restate them. Every form that file recognises carries the
label in backticks, so matching the backticked label alone covers all of them — and no
link can land in code, where a backticked `kind:label` is not Lean syntax (measured: 318
occurrences across `lean/`, every one in a docstring or comment).

**Links go through a command, not a URI fragment.** `DocumentLink` targets support a
`file:` URI with an `L<n>` fragment, which would be shorter, but that behaviour could not
be verified without a running editor, so the extension registers
`decoupledCitations.open` and reveals the line explicitly instead. If you confirm the
fragment form works in your VS Code, `openAt` is the one function to change.

## What is linked

The label, and a line span stated immediately after it on the same line. A citation
without a label is not linked — the label is what resolves the file — which is why the
convention is that any citation stating line numbers carries its label beside them. Two
things stay plain text by design: a label-less re-mention next to a fully cited one
("Definition 12 makes the write part of the rule"), and the per-line figure comments
(`-- line 531`), which the enclosing docstring's own labelled citation anchors.

## Commands

| Command | What it does |
| --- | --- |
| `Paper citations: Open the cited paper line` | what a link invokes; not useful by hand |
| `Paper citations: Reload the citation label map` | re-read the JSON, if the watcher missed a rewrite |

With no `.citation-links.json` present there are simply no links, and the reason is
logged once to the *Paper citations* output channel. Nothing pops up.
