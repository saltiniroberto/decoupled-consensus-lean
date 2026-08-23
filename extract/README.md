# `extract/` — the document-extraction workstream

The goal (Roberto, 2026-08-23): a script that extracts, out of the `Spec/Consensus1/`
Lean files, a document similar to the source `consensus-1.pdf`.

## Prose is opt-in: the `## Extract` marker

Roberto, 2026-08-24. A module header or docstring section headed `## Extract` is document
prose; everything unmarked is Lean-side commentary and stays out of the PDF. The default
was chosen deliberately: marked text is written *for* the document, so it can read like
the draft, and new commentary stays out without anyone remembering to fence it.

- In a module header: the section becomes the file's section prose. `## Extract — X`
  gives it subsection title `X`.
- In a figured routine's docstring: the section leads that routine's figure in, the way
  the draft's prose introduces each figure.
- In any other declaration's docstring: the section follows the figure.

Marked prose renders in the draft's typography: backticked spans go through the same
rewriter as the figures, and fall back to mono exactly when they quote Lean.

**The durable home for these sections is the live spec's headers** — a refresh of the
frozen copy wipes anything written only here. The `## Extract` sections currently in
`Consensus1-frozen/Fig2GoldfishDuties.lean` are demos, marked as such in their text.

## `Consensus1-frozen/`

A plain copy of `lean/Spec/Consensus1/` (the `.lean` files, without `doc/`), frozen at
commit `909b4f6` on 2026-08-23. It exists so the extraction script has a stable input
while the live spec keeps changing in parallel.

Rules:

- **The live spec is `lean/Spec/Consensus1/`.** Nothing imports the frozen copy, no build
  target reads it (`lake`'s globs claim only `lean/`, and `make orphans` scans only
  `lean/`), and no spec change is made here.
- The copy is refreshed deliberately, on instruction — re-copy and update the commit hash
  above — never as a side effect of editing the live spec.
