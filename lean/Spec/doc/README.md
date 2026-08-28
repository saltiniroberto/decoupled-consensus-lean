# The spec, file by file

`lean/Spec/` is the specification of Ethereum decoupled consensus. One algorithm file per
part of the protocol; read them in this order, which is dependency order:

| File | What it specifies |
| --- | --- |
| [`01_GoldfishWalk.lean`](../01_GoldfishWalk.lean) | the fork-choice walk: `best_child`, `ghost`, the Goldfish fork choice, and `get_head`, written once over what each layer supplies |
| [`06_StateTransition.lean`](../06_StateTransition.lean) | the chain state: how processed attestations justify and finalize heights |
| [`03_AvailableConfirmation.lean`](../03_AvailableConfirmation.lean) | what a slot confirms: the confirmation walk, and the two routines that run it and record its answer |
| [`02_GoldfishDuties.lean`](../02_GoldfishDuties.lean) | the slot duties: `on_tick`, `propose_block`, `goldfish_vote`, the block and vote handlers |
| [`04_SGForkChoice.lean`](../04_SGForkChoice.lean) | `latest`, `sg_support`, the majority fork choice |
| [`05_SGDuty.lean`](../05_SGDuty.lean) | `sg_vote`, the head a validator votes for its round, and the handler that stores one |
| [`07_FGStore.lean`](../07_FGStore.lean) | the finality store: viability, `update_finality`, the filtered tree, and this layer's fork choice |
| [`08_FinalityVote.lean`](../08_FinalityVote.lean) | how a validator fills the attestation it signs |
| [`09_Healing.lean`](../09_Healing.lean) | healing: the support scores and grades, the round-root functions, and the layer as assembled — the tree every walk descends, and `on_tick` |

What the algorithms are written in terms of sits in [`Defs/`](../Defs):

| File | What it holds |
| --- | --- |
| [`Model.lean`](../Defs/Model.lean) | the substrate: validators and weights, committees, blocks and ancestry, the wire objects |
| [`Store.lean`](../Defs/Store.lean) | the store — what a node keeps — and the duty boundary object |
| [`SigningHistory.lean`](../Defs/SigningHistory.lean) | the durable signing record behind the attestation rules |
| [`Notation.lean`](../Defs/Notation.lean), [`Raise.lean`](../Defs/Raise.lean), [`FinsetM.lean`](../Defs/FinsetM.lean), [`Nondet.lean`](../Defs/Nondet.lean) | the vocabulary: pseudocode spellings, the failure monad `DRE`, monadic set operations, the nondeterminism monads `NDR`/`NDRE`, the duty monad `NDREB` with `broadcast` |
| [`GoldfishWalk.lean`](../Defs/GoldfishWalk.lean) | what `get_head` takes from the layer — the tree it descends, root and blocks together, and the eligibility condition; one instance, supplied by the layer whose readings are the protocol's |
| [`Tick.lean`](../Defs/Tick.lean) | `on_tick`, the protocol's one entry point from the clock; one instance, supplied by the layer whose reading is the protocol's |
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
- [sts.md](sts.md) — the duty boundary: the spec is shaped to be consumed as a state
  transition system, and this page says by what and how.

Outside `lean/Spec/`: [`lean/Sts.lean`](../../Sts.lean) places the spec under the
transition-system framework — which routine runs on a tick, and which handler runs on each
kind of message received. [sts.md](sts.md) is its design page.

The running record behind these pages is `CONTEXT.md` at the repository root — the dated
entries and the section "The `DC` style sheet". Where a page here and
`CONTEXT.md` disagree, `CONTEXT.md` is the record: fix the page.
