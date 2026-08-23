# Documentation for `Spec/Consensus1/`

`Spec/Consensus1/` renders the draft `consensus-1.pdf` (committed at the repository root).
These pages document the design a reader meets on every page of the Lean:

- [nondeterminism.md](nondeterminism.md) — how the pseudocode's arbitrary choices are
  rendered: the `NDR`/`NDRE` monads, the pick arrow `←ᵖ`, and how a result is consumed.
- [naming.md](naming.md) — how definitions are named: `Store.…`, `Fig<n>.…`, bare names,
  and why the files have no `namespace` blocks.
- [style.md](style.md) — the remaining style rulings, one line each, with pointers to
  where the mechanics live.

The running record behind these pages is `CONTEXT.md` at the repository root — the dated
2026-08-22/23 entries and the section "The `Consensus1` style sheet". Where a page here and
`CONTEXT.md` disagree, `CONTEXT.md` is the record: fix the page.

All decisions documented here are Roberto's. The pages state the decisions and how to read
the code under them; the decision trails — what was tried and declined — stay in
`CONTEXT.md`.
