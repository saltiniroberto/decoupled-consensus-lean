# The spec, file by file

`lean/Spec/` is the specification of Ethereum decoupled consensus. One algorithm file per
part of the protocol; read them in this order, which is dependency order:

| File | What it specifies |
| --- | --- |
| [`01_GoldfishWalk.lean`](../01_GoldfishWalk.lean) | the fork-choice walk: `best_child`, `ghost`, and the Goldfish score |
| [`02_GoldfishStore.lean`](../02_GoldfishStore.lean) | `process_goldfish_vote`, the Goldfish vote handler |
| [`04_SGForkChoice.lean`](../04_SGForkChoice.lean) | `latest`, `sg_support`, the majority fork choice, over the attestation pool |
| [`05_SGDuty.lean`](../05_SGDuty.lean) | `process_sg_vote`, the handler that admits a combined attestation into the round pool |
| [`06_StateTransition.lean`](../06_StateTransition.lean) | the chain state: how processed attestations justify and finalize heights |
| [`07_FGStore.lean`](../07_FGStore.lean) | the finality store: `process_block`'s admission, viability, `update_finality`, the FG root and the filtered tree, the eligibility condition |
| [`08_FinalityVote.lean`](../08_FinalityVote.lean) | the validator client: the store-blind rules that fill the two pairs, and `record_attestation`, the record's one writer |
| [`09_Healing.lean`](../09_Healing.lean) | the graded layer: the grades, the grade-0 veto, the SG root, the tree every walk descends, `get_head`, and the two vote rules `get_sg_vote`/`get_fg_vote` |
| [`10_AvailableConfirmation.lean`](../10_AvailableConfirmation.lean) | `update_confirmation`, the slot's confirmation evaluation |
| [`11_Duties.lean`](../11_Duties.lean) | `propose_block`, `goldfish_vote`, and `on_tick`, the tick that runs everything |

What the algorithms are written in terms of sits in [`Defs/`](../Defs):

| File | What it holds |
| --- | --- |
| [`Model.lean`](../Defs/Model.lean) | the substrate: validators and weights, committees, proposers, blocks and the wire objects |
| [`Store.lean`](../Defs/Store.lean) | the store — what a node keeps — ancestry, resolution times, and the duty boundary object |
| [`SigningHistory.lean`](../Defs/SigningHistory.lean) | the anti-slashing record `Λ` behind the attestation rules |
| [`Notation.lean`](../Defs/Notation.lean), [`Raise.lean`](../Defs/Raise.lean), [`FinsetM.lean`](../Defs/FinsetM.lean), [`Nondet.lean`](../Defs/Nondet.lean) | the vocabulary: pseudocode spellings, the failure monad `DRE`, monadic set operations, the nondeterminism monads `NDR`/`NDRE`, the duty monad `NDREB` with `broadcast` |
| [`OldDefs.lean`](../Defs/OldDefs.lean) | parked definitions, kept compiling; nothing imports it |

## The design pages

- [guide.md](guide.md) — **start here if you don't know Lean**: how to read this spec
  knowing only how to code and how to read paper pseudocode.
- [nondeterminism.md](nondeterminism.md) — how unspecified choices are rendered: the
  `NDR`/`NDRE` monads, the pick arrow `←ᵖ`, and how a result is consumed.
- [naming.md](naming.md) — how definitions are named: `Store.…` and bare names,
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
