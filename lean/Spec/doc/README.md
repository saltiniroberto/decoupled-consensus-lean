# The spec, file by file

`lean/Spec/` is the specification of Ethereum decoupled consensus. One algorithm file per
part of the protocol; read them in this order, which is dependency order:

| File | What it specifies |
| --- | --- |
| [`01_GoldfishWalk.lean`](../01_GoldfishWalk.lean) | the fork-choice walk: `best_child`, `ghost`, the Goldfish fork choice |
| [`06_StateTransition.lean`](../06_StateTransition.lean) | the chain state: how processed attestations justify and finalize heights |
| [`03_AvailableConfirmation.lean`](../03_AvailableConfirmation.lean) | `update_confirmation`: what a slot confirms |
| [`02_GoldfishDuties.lean`](../02_GoldfishDuties.lean) | the slot duties: `on_tick`, `propose_block`, `goldfish_vote`, the block and vote handlers |
| [`04_SGForkChoice.lean`](../04_SGForkChoice.lean) | `latest`, `sg_support`, the majority fork choice |
| [`05_SGDuty.lean`](../05_SGDuty.lean) | `sg_vote`, its handler, and the protocol's `on_tick` |
| [`07_FGStore.lean`](../07_FGStore.lean) | the finality store: viability, `update_finality`, the filtered tree, the protocol's `get_head` |
| [`08_FinalityVote.lean`](../08_FinalityVote.lean) | how a validator fills the attestation it signs |

What the algorithms are written in terms of sits in [`Defs/`](../Defs):

| File | What it holds |
| --- | --- |
| [`Model.lean`](../Defs/Model.lean) | the substrate: validators and weights, committees, blocks and ancestry, the wire objects |
| [`Store.lean`](../Defs/Store.lean) | the store — what a node keeps — and the duty boundary object |
| [`SigningHistory.lean`](../Defs/SigningHistory.lean) | the durable signing record behind the attestation rules |
| [`Notation.lean`](../Defs/Notation.lean), [`Raise.lean`](../Defs/Raise.lean), [`FinsetM.lean`](../Defs/FinsetM.lean), [`Nondet.lean`](../Defs/Nondet.lean) | the vocabulary: pseudocode spellings, the failure monad `DRE`, monadic set operations, the nondeterminism monads `NDR`/`NDRE`, the duty monad `NDREB` with `broadcast` |
| [`OldDefs.lean`](../Defs/OldDefs.lean) | parked definitions, kept compiling; nothing imports it |

## The design pages

- [guide.md](guide.md) — **start here if you don't know Lean**: how to read this spec
  knowing only how to code and how to read paper pseudocode.
- [nondeterminism.md](nondeterminism.md) — how unspecified choices are rendered: the
  `NDR`/`NDRE` monads, the pick arrow `←ᵖ`, and how a result is consumed.
- [naming.md](naming.md) — how definitions are named: `Store.…`, `Fig<n>.…`, bare names,
  and why the files have no `namespace` blocks.
- [style.md](style.md) — the style rulings, one line each, with pointers to where the
  mechanics live.

The running record behind these pages is `CONTEXT.md` at the repository root — the dated
entries and the section "The `DC` style sheet". Where a page here and
`CONTEXT.md` disagree, `CONTEXT.md` is the record: fix the page.
