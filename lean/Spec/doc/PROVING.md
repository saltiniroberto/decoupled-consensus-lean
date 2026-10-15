# How the library `Spec` is proved

The proofs are stated once over a record of operations, `Record.Model V`, and over the facts a
model must prove about those operations, `Record.Facts M`. The spec is one model of the record, `Model.specDraft`, and
`Model.specDraft_facts` proves the facts for it. The end results for the spec are the record's
nine top-level theorems applied to `Model.specDraft_facts` (`lean/EndResults.lean` and
`lean/EndResults/ExistentialForms.lean`). All
nine assume nothing beyond their own statement's premises.

## Terms used on this page

- **The vocabulary model**: a second model of the protocol, under `lean/Model/Vocabulary/`, with
  its proofs under `lean/Proofs/Vocabulary/`; its Lean namespace is `DecoupledConsensusModel`. The
  claims were first proved over it.
- **Named form** and **plain form**: the vocabulary model has every block, attestation and height pair twice.
  In the named form (`NamedBlock`, `NamedAttestation`, `NamedHeightPair`,
  `lean/Model/Vocabulary/Objects/NamedBlocks.lean`) a timeout vote names the block it was cast on.
  In the plain form (`Block`, `CombinedAttestation`, `HeightPair`,
  `lean/Model/Vocabulary/Objects/Blocks.lean`) a timeout vote holds its height only. The spec has
  one form, with the content of the named form.
- **`erase`**: the vocabulary model's map from the named form to the plain form, which drops the block of every
  timeout vote (`lean/Model/Vocabulary/Objects/NamedBlocks.lean:94` for blocks).
- **The record**: the structure `Record.Model V` (`lean/Model/Record/Model.lean:35`, namespace
  `DecoupledConsensusModel.Sts.Record`). Its members are the types, readers and operations the
  proofs use, typed over the vocabulary model's object types.
- **The facts**: the structure `Record.Facts M` (`lean/Model/Record/Facts.lean:29`). Each field of
  each of its parts is one property of the members of a model `M` that a proof calls.
- **A level-1 fact**: what one operation guarantees on an arbitrary input. **A fact about runs**:
  what holds along every run of the model's node.

## The record

A member of the record is one of three kinds:

- a type member, which stands for one of the thirteen structures of the vocabulary model that
  statements read as a store: the stores, the signing records, a round's grades, the grade cache
  and contract, the node state; and the chain state's type;
- a reader, one field of such a structure, read off the record's type;
- an operation, one of the vocabulary model's routines that a statement names, typed as that model
  types it with the thirteen structures replaced by the record's types.

`Record.protocolOf M S` (`lean/Model/Record/Wiring.lean:232`) places a model's node under the sts
framework: its initial node states are the model's, and a step is one of the model's reactions to
the event, or, when the model has none, the node state kept with nothing sent.

## The facts

`Record.Facts M` has one field for the level-1 facts and one for the facts about runs of each
family of operations: the chain state (with a second pair of fields for its added facts), the
schedule, the store, the fork choice, the validator client, the grades, the handlers, the duties
and the tick, the node, and the evidence. That is twenty-two fields. A proof over the record takes
one hypothesis `facts : Record.Facts M` and calls a fact as a field of a field.

## The spec as a model of the record

`Model.specDraft` (`lean/Proofs/Instance/Model.lean:471`) fills every member of the record with the
spec's behaviour.

**The maps.** `lean/Proofs/Instance/Objects.lean` declares, for every object type, maps between
the spec's type and the vocabulary model's. `x.toProofNamed` maps a block, an attestation or a
height pair to the named form; it drops nothing and is injective. `x.toProof` maps them to the plain
form; it drops the root of every timeout vote, so two different values can have the same image.
`toSpecNamed` and `toSpec` map back.

**The types.** The chain state is the spec's `Spec.Protocol.ChainState V`, the grades are the
spec's `RoundGrades V` and `SavedGrades V`, and the signing records are the spec's
`SigningHistory`. The seven store types are `OkStore V` (`lean/Proofs/Instance/StoreOk.lean:25`),
the spec's stores that meet `StoreOk` (`lean/Proofs/Instance/NoRaise/Predicates.lean:37`): every
object they hold is stamped, no two blocks of the tree share a root, the tree holds the parent of
each of its blocks, and the tree holds the finalized block. The node type is the spec's node
states whose store meets `StoreOk`.

**The members.** Each other member is a spec routine read through the maps. The members of the
namespace `SpecDraftRecord.OkMember` (`lean/Proofs/Instance/Model.lean:18`) differ from the spec
where a store would leave its type. Among them, the five that admit a block refuse it, and return the store unchanged, when another
block of the tree has that block's root (`RootHeldByOther`,
`lean/Proofs/Instance/StoreOk.lean:40`): the store type holds no two blocks of one root, and the
spec's admission would add the second. The header of `lean/Proofs/Instance/Model.lean` names every
member whose value is not the spec's routine as it is.

**The facts at the spec.** `Model.specDraft_facts : Record.Facts Model.specDraft`
(`lean/Proofs/Instance/Facts/Assembly.lean:1241`) proves every fact. Many fields are read from the
same fact at the vocabulary model's instance of the record, `Model.vocabulary`
(`lean/Proofs/Vocabulary/ModelVocabulary.lean:28`),
whose level-1 facts are proved family by family (`Model.vocabulary_facts_<family>`,
`lean/Proofs/Vocabulary/ModelVocabularyFacts.lean`). The bridge is a set of theorems that a spec
routine, read through the maps, equals the vocabulary model's routine
(`lean/Proofs/Instance/Equalities/`). This is why the proofs about the vocabulary model are still
part of `Proofs`.

**The wiring.** The record's wiring at the spec's model is the spec's own protocol
`Spec.Sts.protocol` of `lean/Sts.lean`, read through the maps:

- `protocolOf_specDraft_init` (`lean/Proofs/Instance/ModelWiring.lean:230`): the two protocols
  start every validator from the same node state;
- `protocolOf_specDraft_step_iff` (`lean/Proofs/Instance/ModelWiring.lean:238`): a step of the
  record's wiring holds exactly when the spec's protocol takes the corresponding step, provided
  every step the spec's node takes there keeps its store in `StoreOk`.

Read aloud: where the spec's node keeps its store stamped, with distinct roots, parent-closed and
holding its finalized block, the executions the end results talk about take the same steps as the
spec's own protocol. Where a step of the spec would leave the store outside `StoreOk`, for
example by admitting a second block with the root of a block already in the tree, the record's
step keeps the node state and sends nothing, a step the spec does not take.

## The restated claims

`lean/Proofs/Claims/Restated/` states every theorem the end results need over an arbitrary model
`M : Record.Model V`, with `facts : Record.Facts M` as a hypothesis. Its nine top-level theorems are:

| theorem | file |
| --- | --- |
| `constants_holds` | `lean/Proofs/Claims/Restated/Constants.lean:30` |
| `claimConfirmedAfterHealing_holds` | `lean/Proofs/Claims/Restated/ClaimConfirmedAfterHealingHolds.lean:261` |
| `claimStableLiveAfterHealing_holds` | `lean/Proofs/Claims/Restated/ClaimStableLiveAfterHealingHolds.lean:296` |
| `claimConfirmedIncludedAfterHealing_holds` | `lean/Proofs/Claims/Restated/ClaimConfirmedIncludedAfterHealingHolds.lean:322` |
| `claimStableThroughOneAsyncPeriod_holds` | `lean/Proofs/Claims/Restated/ClaimStableThroughOneAsyncPeriodHolds.lean:209` |
| `claim13bf_holds` | `lean/Proofs/Claims/Restated/Claim13bfKitTop.lean:104` |
| `claimConfirmedGrowsAfterHealing_holds` | `lean/Proofs/Claims/Restated/ClaimConfirmedGrowsAfterHealingHolds.lean:285` |
| `claimFinalityLiveAfterHealing_holds` | `lean/Proofs/Claims/Restated/ClaimFinalityLiveAfterHealingKit.lean:80` |
| `claimStableThroughOneAsyncPeriodCommonViewAgain_holds` | `lean/Proofs/Claims/Restated/ClaimStableThroughAsyncPeriodCommonViewAgainHolds.lean:157` |

Each concludes a statement defined under `lean/Model/Conditions/`, for example
`claim13bfStatement` (`lean/Model/Conditions/Sts_Spec2Claims_Claim13bf.lean:56`). Except for
`constants_holds`, which is about the timing constants, each statement is about the executions of
`Record.protocolOf M S`.

## The end results

The library `EndResults` applies each of the nine to `Model.specDraft_facts`. The theorem
`EndResults.<name>` is `<name>` at `M := Model.specDraft`: `EndResults.constants_holds`,
`EndResults.claimConfirmedAfterHealing_holds`, `EndResults.claimStableLiveAfterHealing_holds`,
`EndResults.claimConfirmedIncludedAfterHealing_holds`,
`EndResults.claimStableThroughOneAsyncPeriod_holds`, `EndResults.claim13bf_holds`,
`EndResults.claimConfirmedGrowsAfterHealing_holds`, `EndResults.claimFinalityLiveAfterHealing_holds`
and `EndResults.claimStableThroughOneAsyncPeriodCommonViewAgain_holds`
(`lean/EndResults.lean:62` for the first, `lean/EndResults/ExistentialForms.lean:42` to
`lean/EndResults/ExistentialForms.lean:1291` for the other eight). Their Lean namespace is
`EndResults`. Each of the eight with an `∃ tHeal` is followed by its per-execution form
`EndResults.<name>_perExecution`, the same statement with the execution `x`, and each hypothesis
naming only `x` and the binders before it, before the colon, so that `tHeal` is chosen for each
execution. Each of the eight also has an explicit form, `EndResults.<name>_explicit`, which states
the claim over every phase `[tGAT, tAwakeEnd]` at least as long as the value of `tHeal` that the
proof of `<name>` picks, with every hypothesis before the colon. That value is
`healingLengthη M S gap + (constants M S).period` for `claim13bf_holds` and
`claimFinalityLiveAfterHealing_holds`, and
`healingLengthη M S gap + (gap + 2) * (constants M S).period` for the other six. They are
`EndResults.claimConfirmedAfterHealing_holds_explicit` (`lean/EndResults.lean:101`),
`EndResults.claimStableLiveAfterHealing_holds_explicit` (`lean/EndResults.lean:177`),
`EndResults.claimConfirmedIncludedAfterHealing_holds_explicit` (`lean/EndResults.lean:256`),
`EndResults.claimStableThroughOneAsyncPeriod_holds_explicit` (`lean/EndResults.lean:332`),
`EndResults.claim13bf_holds_explicit` (`lean/EndResults.lean:441`),
`EndResults.claimConfirmedGrowsAfterHealing_holds_explicit` (`lean/EndResults.lean:525`),
`EndResults.claimFinalityLiveAfterHealing_holds_explicit` (`lean/EndResults.lean:603`) and
`EndResults.claimStableThroughOneAsyncPeriodCommonViewAgain_holds_explicit`
(`lean/EndResults.lean:684`).

## How `claim13bf_holds` is proved

`EndResults.claim13bf_holds` (`lean/EndResults/ExistentialForms.lean:773`) concludes
`claim13bfStatement` at the spec's model. That statement says: for every gap `gap` with
`gap + 2 ≤ K` there is a healing length such that, in every execution that meets the statement's
premises over a phase at least that long, any two validators, each outside the adversary's set at
every time up to the step at which its store is read, hold finalized blocks that are compatible
(one is an ancestor of the other, or they are equal).

`claim13bf_holds` (`lean/Proofs/Claims/Restated/Claim13bfKitTop.lean:104`) proves it from the
statement's premises alone. Its proof calls `claim13bf_conclusion_of_joint`
(`lean/Proofs/Claims/Restated/Claim13bfJoint.lean:338`), which carries the invariant
`AfterPhaseInvariantOverActiveSetsJoint` (`lean/Model/Conditions/Claim13bInvariantActiveJoint.lean:35`)
from the switch round to every later round. The switch round is the last round whose third slot
is confirmed at or before the end of the phase (`switchRound`,
`lean/Model/Conditions/Claim13bSGCompatible.lean:30`). The one further input of
`claim13bf_conclusion_of_joint`, a lower bound on the justified height of every honest store up to
the switch round's tick, is proved by `hlow_of_premises_l85f`
(`lean/Proofs/Claims/Restated/Claim13beRoute3_85f.lean:1261`).

Until 2026-10-15 the end result kept a premise that asked for five facts about the rounds up to
the switch round. The proof of `claim13bf_holds` now derives what it needs of them, and the
premise is gone. The definitions of the five facts stay under `lean/Model/Conditions/`, where
intermediate theorems use them.

## Building it

`lake build Proofs` builds every proof but the end results, and `lake build EndResults` builds the
end results, the library `EndResults` (`lean/EndResults.lean` and
`lean/EndResults/ExistentialForms.lean`); none of `Model`, `Proofs` and
`EndResults` is a default target of `lakefile.toml`.
