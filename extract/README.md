# `extract/` — the document-extraction workstream

The goal (Roberto, 2026-08-23): a script that extracts, out of the `Spec/Consensus1/`
Lean files, a document similar to the source `consensus-1.pdf`.

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
