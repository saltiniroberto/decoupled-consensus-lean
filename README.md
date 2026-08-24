# decoupled-consensus-lean

The Lean 4 specification of **Ethereum decoupled consensus** — a protocol design that
separates the chain that stays *available* from the mechanism that makes it *final*, so
that each can be simple where the other cannot afford to be.

Three layers, each building on the one below:

- **The available chain.** Time runs in slots; each slot has an assigned proposer and a
  committee. The proposer builds on the current fork-choice head; committee members vote
  for the head with one-slot Goldfish votes, carried by blocks — blocks are the only
  relay channel — and at each slot's end the node evaluates what that slot *confirmed*.
- **Slot-group (SG) votes.** Slots group into rounds. Once per round every validator
  votes its confirmed block, and a relative-majority fork choice over the latest SG
  votes anchors the walk, so the available chain grows from what a majority recently
  confirmed.
- **Finality (FG).** Every block replays to a chain state; attestations, carried in
  blocks, justify and then finalize heights of that state on chain — a Simplex-style
  finality mechanism with accountable safety: conflicting finalizations expose a third
  of the validator weight as provably slashable. The finalized state filters the block
  tree the other layers walk.

A validator's node is one **store** — messages and their arrival times — plus **duties**
driven by a clock: propose, vote, confirm, attest. The specification is precise about
what the paper leaves open: unspecified orders and tie-breaks are genuine nondeterminism
(every resolution is an outcome, none privileged), impossible reads fail loudly, and
"the failure never happens" is a theorem to prove, not an assumption.

## Where everything is

The spec is `lean/Spec/`, one file per algorithm figure of the protocol's working draft
(the draft, `consensus-1.pdf`, is not distributed with this repository; the Lean stands
alone, every definition documented in place):

| File | What it specifies |
| --- | --- |
| `Fig1GoldfishWalk.lean` | the walk: `best_child`, `ghost`, the Goldfish fork choice |
| `Fig2GoldfishDuties.lean` | the slot duties: `on_tick`, `propose_block`, `goldfish_vote`, the block and vote handlers |
| `Fig3AvailableConfirmation.lean` | `update_confirmation`: what a slot confirms |
| `Fig4SGForkChoice.lean` | `latest`, `sg_support`, the majority fork choice |
| `Fig5SGDuty.lean` | `sg_vote`, its handler, and the protocol's `on_tick` |
| `Fig6StateTransition.lean` | the chain state: how processed attestations justify and finalize heights |
| `Fig7FGStore.lean` | the finality store: viability, `update_finality`, the filtered tree, the protocol's `get_head` |

`lean/Spec/Defs/` holds what the figures are written in terms of: the model and wire
objects (`Model.lean`), the store (`Store.lean`), the rule determining a validator's
attestation (`FinalityVote.lean`, with `SigningHistory.lean`), and the vocabulary layers
that make the Lean read like the draft's pseudocode. `lean/Analysis/` holds results
stated against the spec — accountable safety, so far as a statement.

**To read the spec without knowing Lean, start at
[`lean/Spec/doc/guide.md`](lean/Spec/doc/guide.md)** — it covers exactly the notation a
reader of paper pseudocode won't already have. The pages beside it document the design:
the nondeterminism machinery, the naming scheme, the style rules.

## The extractor

`extract/` renders the spec back into a paper-shaped PDF: `python3 extract/extract.py`
compiles `extract/out/consensus1.pdf` from a frozen copy of the Lean.
`extract/README.md` has the conventions it harvests and the rewrite rules.

## Building

    make            # list the available targets
    make cache      # fetch prebuilt Mathlib artifacts -- do this before a first build
    make dev        # working target: allows sorry, counts what is outstanding
    make check      # strict target: any sorry/admit fails it

Toolchain pinned in `lean-toolchain` (Lean 4.32.2); Mathlib's rev in `lakefile.toml` and
the rev the `deps/lean-sts` submodule requires must match it.

## History

Two earlier renderings — the `latex-specs` papers, with a proved analysis layer, and an
earlier draft — lived here until 2026-08-24; the branch `pre-consensus1-purge` holds the
last commit carrying them. `CONTEXT.md` is the running record of decisions since.
