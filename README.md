# decoupled-consensus-lean

A Lean 4 formalization of `consensus-1.pdf` — a human-controlled draft of a Simplex-style
finality protocol — together with an extractor that renders the Lean back into a document
shaped like the draft.

The draft itself is a local file at the repository root and is **not committed**: no PDF
spec is. A fresh clone builds and reads the Lean on its own; the Lean's docstrings are
self-contained.

## The specification

Everything is under `lean/`. The Lake library is `Spec`, `srcDir` is `lean`, and the module
root is `Spec`, so `Spec.Consensus1.Model` is `lean/Spec/Consensus1/Model.lean`. The one
subtree is `lean/Spec/Consensus1/`, namespace `Consensus1`:

- `Fig<n><Subject>.lean` — one file per figure of the draft, `<n>` the draft's own figure
  number, the `-- line n` comments its own line numbering. The draft defines some routines
  incrementally; the last reading of each bears the plain `Store` name and the superseded
  readings are figure-named (`Fig1.getHead`, …).
- `Model.lean`, `Store.lean`, `SigningHistory.lean`, `FinalityVote.lean` — the substrate,
  the store, and the imported finality-vote strategy (the draft never defines how the
  attestation pairs are filled; `FinalityVote.lean` says where its logic comes from).
- `Notation.lean`, `Raise.lean`, `FinsetM.lean`, `Nondet.lean`, `Duty.lean`,
  `OldDefs.lean` — the vocabulary layers: the draft's spellings, the failure monad `DRE`,
  monadic set operations, the nondeterminism monads `NDR`/`NDRE` and the pick `←ᵖ`, the
  duty monad `NDREB` with `broadcast`, and parked definitions.
- `doc/` — reader-facing pages on the design: nondeterminism, naming, the style rulings.

## The extractor

`extract/` renders the frozen copy of the spec (`extract/Consensus1-frozen/`) into a PDF
shaped like the draft: `python3 extract/extract.py` writes and compiles
`extract/out/consensus1.pdf` (LuaLaTeX). `extract/README.md` carries the conventions the
script harvests from the Lean and the rewrite rules, and the rule for refreshing the
frozen copy.

## Commands

    make            # list the available targets
    make cache      # fetch prebuilt Mathlib artifacts -- do this before a first build
    make dev        # working target: allows sorry, counts what is outstanding
    make check      # strict target: any sorry/admit fails it
    make build      # build the library

The toolchain is pinned in `lean-toolchain` (Lean 4.32.2); Mathlib's rev in
`lakefile.toml` and the rev `deps/lean-sts` requires must match it. `deps/lean-sts` is a
git submodule (the state-transition-system framework the eventual wiring will target).

## History

Two older renderings — the `latex-specs` papers (with a proved `Analysis/` layer and a
citation apparatus) and `consensus.pdf` — lived in this repository until 2026-08-24, when
it narrowed to the scope above. The branch `pre-consensus1-purge` holds the last commit
carrying them, full history included. `CONTEXT.md` is the running record of decisions
since; the `latex-specs` checkout survives locally, untracked.
