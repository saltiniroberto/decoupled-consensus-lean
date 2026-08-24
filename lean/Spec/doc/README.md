# Documentation for `Spec/`

`lean/Spec/` is the specification of Ethereum decoupled consensus, rendered from the
protocol's working draft (`consensus-1.pdf`, kept locally at the repository root; no PDF
spec is committed). These pages document the design a reader meets on every page of the
Lean:

- [guide.md](guide.md) — **start here if you don't know Lean**: how to read this spec
  knowing only how to code and how to read paper pseudocode.
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
