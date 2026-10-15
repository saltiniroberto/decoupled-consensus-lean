# The library `Spec`

`Spec` is one node of the decoupled consensus protocol, written in Lean as definitions only. It
holds no theorem: every fact proved about it is under `lean/Proofs/` (see `PROVING.md`).

## What it is

The library declares its own types, its own parameters and its own routines. Its Lean namespace
is `Spec`; the protocol's routines and a few types sit in `Spec.Protocol`.

**The objects.** A block `Block V` is the genesis block, or a block that holds its parent, its
slot, its root, the Goldfish votes and the attestations it includes, and its proposer
(`lean/Spec/Objects.lean:233`). An attestation `Attestation V` holds its validator, its round, the
root of the block it confirms, a height pair and a finality pair (`lean/Spec/Objects.lean:218`).
A height pair is empty, or a vote at a height for the block with a given root; a flag says whether
the vote is a timeout vote, and a timeout vote names the block it was cast on
(`lean/Spec/Objects.lean:188`). The objects a node sends and receives are one type, `NamedObject V`: a block, a Goldfish vote or an attestation
(`lean/Spec/Objects.lean:316`).

**The parameters.** A routine reads at most three records (`lean/Spec/Config.lean`):

- `Config`, every parameter a node knows: the schedule unit `Δ`, the round length `R`, the lookback
  `η_SG`, the finality constants `K`, `D` and `timeoutDelay`, and the conditions on them
  (`lean/Spec/Config.lean:44`);
- `Provisional V`, values given to the node for now: the proposer of each slot, the committees
  and the weights (`lean/Spec/Config.lean:86`);
- `External V`, values another piece of software supplies: the root of the block a validator
  proposes in a slot (`lean/Spec/Config.lean:100`).

A routine takes `C : Config`, and takes `P : Provisional V` or `X : External V` only when it
reads one of their values, directly or through a routine it calls. No record holds the instant
after which delivery is bounded: that is a property of an execution, not something a node knows.

**The state.** The store `Store V` is one record that holds everything a node keeps about the
protocol, apart from the validator's signing history (`lean/Spec/Store.lean:198`): the clock and
the slot, the block tree `T`, the stamps (the time at which each block, each Goldfish vote and
the strong-gadget vote of each attestation was processed), the chain state of each block, the Goldfish votes and the attestations
it has processed, the finalized and justified blocks, the three confirmation records, and the
saved grades (the grade results of one round and of the next). The signing history `SigningHistory` holds what the validator has
signed, height by height (`lean/Spec/Protocol/ValidatorClient.lean:55`). The node state
`NodeState V` holds the validator `v`, the store `st`, the signing history, and `awakeSince`, the
instant since which the node has been awake without interruption, or `none` between a wake and
the next tick (`lean/Spec/NodeState.lean:48`).

**What a node does.** Six routines are the whole node:

- `initial C v`, the node state a validator starts from (`lean/Spec/Node.lean:87`);
- `tick C P X n t`, what the node does when its clock reaches time `t`
  (`lean/Spec/Node.lean:130`);
- `wake n`, what a wake does: `awakeSince` becomes `none`, and nothing else changes
  (`lean/Spec/NodeState.lean:60`);
- `receive_block`, `receive_goldfish_vote`, `receive_attestation`, what the node does on
  receiving each kind of object: admit it into the store, then replace every block of the saved
  grades by its deepest ancestor compatible with the finalized block
  (`lean/Spec/Node.lean:157`, `lean/Spec/Node.lean:167`, `lean/Spec/Node.lean:177`).

The tick, in order: it records the wake's instant in `awakeSince` when that is `none`; it updates
the saved grades whose instant is `t`; it sets the store's clock and slot; it runs the proposal
(for the slot's proposer only), the Goldfish vote, the confirmation and the attestation, each when
`t` is that duty's instant and the node has been awake since one delay before the first cutoff of
the grades the duty reads; and it replaces every block of the saved grades by its deepest ancestor
compatible with the finalized block. The first three duties run only in a slot after slot `0`.
The duties send what they send with `broadcast` (`lean/Spec/Broadcast.lean:51`), inside the result
type `DREB V`, which keeps the list of the objects sent.

**Failure.** A routine that can fail has the result type `DRE α`, an answer of type `α` or the one
failure value (`lean/Spec/Defs/Raise.lean:65`). A routine fails only where a read finds something
the protocol says cannot happen: a grade result that is still pending, two blocks of the tree with
the same root, an object of the store with no stamp. Each such routine's docstring says when it
fails.

## The files

The root module `lean/Spec.lean` imports the fifteen files outside `lean/Spec/Defs/`.

| file | what it holds |
| --- | --- |
| `lean/Spec/Objects.lean` | the types (slots, heights, rounds, roots, instants, stamps, height pairs, finality pairs, Goldfish votes, attestations, blocks, weights, committees, `NamedObject`, grade results, a round's grades, the saved grades, the chain state, the strong-gadget vote, the duties' inputs); the functions on blocks (ancestry, the deeper order, the lookups by root, the deepest block), on instants, and the resolution of a Goldfish vote; three notations of the library |
| `lean/Spec/Config.lean` | `Config`, `Provisional V`, `External V`; the schedule's instants and the weights read from them |
| `lean/Spec/Protocol/ChainState.lean` | the chain-state transition: one attestation, the height events, the chain state of a block |
| `lean/Spec/Store.lean` | the store `Store V`, its initial value, its readers (vote sets, the resolution time of a vote, the saved grade of a phase), the routines on the saved grades, and the stable and confirmed blocks the node exposes |
| `lean/Spec/Protocol/ValidatorClient.lean` | the signing history and the routines that read and write it: the finality pair, the height pair, the attestation |
| `lean/Spec/NodeState.lean` | the node state, `wake`, and the wake test the duties read |
| `lean/Spec/Broadcast.lean` | the result type `DREB V` of a duty, and `broadcast` |
| `lean/Spec/Protocol/ForkChoice/Goldfish.lean` | the Goldfish vote sets and score, the walk `ghost`, the viability test, the fork-choice root `get_fg_root`, the filtered block tree |
| `lean/Spec/Protocol/ForkChoice/Views.lean` | the votes and blocks the voter and the proposer of a slot count |
| `lean/Spec/Protocol/ForkChoice/Head.lean` | the active prefix of a block, the strong-gadget root, the composed head |
| `lean/Spec/Protocol/Grades.lean` | the grade test, `update_grades`, and the reads of a round's grades that the duties use |
| `lean/Spec/Protocol/GoldfishVotes.lean` | the admission of a Goldfish vote, the Goldfish vote duty, the confirmation duty |
| `lean/Spec/Protocol/Attestations.lean` | the admission of an attestation, the attestation's reads, the attestation duty |
| `lean/Spec/Protocol/Blocks.lean` | the finality update, the admission of a block, the proposal's routines and duty |
| `lean/Spec/Node.lean` | `initial`, `tick`, and the three receiving routines |
| `lean/Spec/Defs/Raise.lean` | the failure value, `DRE`, the read `Option.value`, and the lift that reads an optional value in a routine that can fail |
| `lean/Spec/Defs/FinsetM.lean` | `Finset.filterM`, `Finset.unionM` and `Finset.map'` |
| `lean/Spec/Defs/Notation.lean` | the assignment arrows, the raising set-builder, the image comprehension and `\|s\|` |
| `lean/Spec/Defs/Model.lean` | the `⊥` spelling of an absent optional value |
| `lean/Spec/Defs/Nondet.lean` | the result types of a routine that picks; no file of the library imports it |

`DEPENDENCIES.md` says what each file imports and what each file of `lean/Spec/Defs/` provides.

## The node under the sts framework

`lean/Sts.lean` places the node under the framework of `deps/lean-sts` (its `StsMultisetLog`
flavour). It is its own library, `Sts`; no file of `Spec` imports it. Its namespace is `Spec.Sts`:

- `Setup V`, the three records `C`, `P` and `X` the node reads (`lean/Sts.lean:108`);
- `receive`, which hands each delivered object to the routine of its kind
  (`lean/Sts.lean:122`);
- `relayedObjects`, the objects a validator sends again when one is delivered: the object, and
  for a block every Goldfish vote and attestation it includes (`lean/Sts.lean:135`);
- `reaction`, a validator's reaction to an event (`lean/Sts.lean:166`). A tick at a reading that
  is a whole multiple of `Δ` runs `tick`; when the tick fails, the state is kept and nothing is
  sent. A tick at any other reading keeps the state. A delivery runs `receive` and sends
  `relayedObjects`. A wake runs `wake`;
- `protocol`, the framework's `Protocol` value: `init` is `initial`, and a step is the reaction
  (`lean/Sts.lean:197`).

A validator asleep in the framework's schedule takes no tick and receives nothing. The node's
own wake rule reads `awakeSince`, which the wake event sets to `none`.

## What it imports

Mathlib, and its own files: no file of `Spec` imports `Model` or `Proofs`.
`lean/Sts.lean` imports `Spec` and the framework's module `StsMultisetLog`. `DEPENDENCIES.md` has
the list, file by file.

## Building it

`lake build Spec Sts` builds the library and its placement under the framework; they are the
default targets of `lakefile.toml`, so `lake build` alone does the same. `make spec` builds `Spec`
alone, after checking that no file of the project uses `native_decide` and that no file under
`lean/Spec/` holds `sorry` or `admit`. Run `make cache` before a first build, to fetch Mathlib's
built files.

## The other pages

- `DEPENDENCIES.md`: what every file imports, what `lean/Spec/Defs/` provides, and where the
  definitions came from.
- `PROVING.md`: how the library is proved: the record, its facts, the instance at the spec, the
  restated claims and the end results.
- `STYLE.md`: the style the library is written in, rule by rule, with the places that do not
  follow a rule.
