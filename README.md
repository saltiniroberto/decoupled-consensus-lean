# decoupled-consensus-lean

## The spec

It lives in [`lean/Spec/`](lean/Spec/) — one algorithm file per part of the protocol, and
the routines read the way they would in a paper:

```lean
def Store.decideHeightVote (S : Store Validator) :
    DRE (Store Validator) := do
  let mut S := S
  let hp ← S.computeHeightVote
  -- a named target is recorded as the height's first target
  if hp.T ≠ ⊥ then
    S.history ← S.history.saveTarget (← hp.h) (← hp.T)
  -- an empty target sets the height's flag
  if hp.T = ⊥ ∧ hp.h ≠ ⊥ then
    S.history ← S.history.saveEmptyTarget (← hp.h)
  S.heightPair ← hp
  return S
```

Every definition carries a docstring saying what it means, so the files can be read top
to bottom, in the order [`lean/Spec.lean`](lean/Spec.lean) lists them. A few notations
are not standard pseudocode — the failure-propagating `←`, the nondeterministic pick
`←ᵖ`, the bracketed store reads — and the guide covers all of them in a few minutes:

- **[How to read the spec](lean/Spec/doc/guide.md)** — for readers who know code and
  pseudocode, no Lean assumed. Start here.
- **[The file map](lean/Spec/doc/README.md)** — what each file specifies, and the design
  pages: [nondeterminism](lean/Spec/doc/nondeterminism.md),
  [naming](lean/Spec/doc/naming.md), [style](lean/Spec/doc/style.md),
  [sts](lean/Spec/doc/sts.md).
- [`lean/Sts.lean`](lean/Sts.lean) — the spec placed under the transition-system
  framework: which routine runs on a tick, and which handler runs on each kind of message
  received.
- [`lean/Analysis/`](lean/Analysis/) — results stated against the spec (accountable
  safety, so far as a statement).

Also here:

- [`extract/`](extract/README.md) — `make extract` renders the spec into a paper-shaped
  PDF, `extract/out/dc.pdf`.
- [`deps/lean-sts`](https://github.com/saltiniroberto/lean-sts) — the transition-system
  framework, a submodule. The spec says what one validator does; the framework supplies
  everything around it — signed messages and a message log, the views it maintains so a
  protocol can neither forget nor fabricate a delivery, a schedule of who is corrupt and who
  is awake at each time, executions, and the network and fairness assumptions as predicates
  over them. Its invariants come with it, so this project neither restates nor re-proves
  them: that every message in a view really was signed and sent, that the log only grows,
  and what a reaction may and may not touch. Because the assumptions are predicates, the
  model is a choice a protocol makes rather than something the framework commits to.
  [`lean/Sts.lean`](lean/Sts.lean) places this spec under the `StsMultisetLog` flavour; no
  model is instantiated yet.

## Building

    make            # list the available targets
    make cache      # fetch prebuilt Mathlib artifacts -- do this before a first build
    make dev        # working target: allows sorry, counts what is outstanding
    make check      # strict target: any sorry/admit fails it
    make extract    # render the spec into a paper-shaped PDF (extract/out/dc.pdf)

Toolchain pinned in [`lean-toolchain`](lean-toolchain) (Lean 4.32.2); Mathlib's rev in
`lakefile.toml` and the rev the `deps/lean-sts` submodule requires must match it.
`CONTEXT.md` is the running record of design decisions.
