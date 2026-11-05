module
public import GoldilocksCorrectness.Record.ModelSpellings

@[expose] public section

/-!
# The facts of the initial node state

`InitialFacts M` holds, for a model `M`, what each reader of a node state answers on the node
state `M.initial C v` a node of the validator `v` starts from, one field per reader or per group of
readers: the tree holds the genesis block alone; the finalized and the justified blocks are the
genesis block, justified at the height `0`; no attestation and no Goldfish vote is held; the
genesis block alone is stamped, with the stamp `⊥`, earlier than every time; no confirmation is
saved, no lock entry and no fast block is held, and the record of the confirmed tip is the genesis
block; nothing is signed; the clock is `0` and the validator is `v`; and the node counts as awake
since `C.t_ 0 + C.Δ − 4 * C.Δ * (C.k + 1)`, the start of slot `0`'s proposal window. The initial
state satisfies the model's node invariant: that is the field `initial_nodeInv` of
`NodeInvFacts`. This file holds the structure only.
-/

set_option autoImplicit false

open scoped DC

namespace GoldilocksCorrectness.Record

open Goldilocks (Config Block Slot Time Stamp)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The facts of `M` about the initial node state `M.initial C v`.

Read aloud: a node starts with the genesis block alone, nothing held, nothing signed, its clock at
zero and its wake time the first proposal window's start. -/
structure InitialFacts (M : GoldilocksModel V) : Prop where
  /-- The tree of the initial state is the genesis block alone.

      Read aloud: a node starts holding the genesis block and no other block. -/
  initial_tree : ∀ (C : Config) (v : V), (M.initial C v).tree = {Block.genesis}
  /-- The finalized block of the initial state is the genesis block.

      Read aloud: a node starts with the genesis block finalized. -/
  initial_finalized : ∀ (C : Config) (v : V), (M.initial C v).finalized = Block.genesis
  /-- The justified block of the initial state is the genesis block.

      Read aloud: a node starts with the genesis block justified. -/
  initial_justified : ∀ (C : Config) (v : V), (M.initial C v).justified = Block.genesis
  /-- The justification height of the initial state is `0`.

      Read aloud: a node starts with the justification height zero. -/
  initial_justifiedHeight : ∀ (C : Config) (v : V), (M.initial C v).justifiedHeight = 0
  /-- The initial state holds no attestation.

      Read aloud: a node starts with no attestation. -/
  initial_attestationsHeld : ∀ (C : Config) (v : V), (M.initial C v).attestationsHeld = []
  /-- The initial state holds no Goldfish vote of any slot.

      Read aloud: a node starts with no Goldfish vote. -/
  initial_votesHeld : ∀ (C : Config) (v : V) (s : Slot), (M.initial C v).votesHeld s = []
  /-- In the initial state no Goldfish vote is stamped, and the genesis block alone is stamped,
      with the stamp `⊥`.

      Read aloud: a node starts with no vote stamped and with the genesis block stamped earlier than
      every time, and no other block stamped. -/
  initial_stamps : ∀ (C : Config) (v : V),
    (∀ vote, (M.initial C v).voteStamp vote = none) ∧
      ∀ B : Block V, (M.initial C v).blockStamp B =
        if B = Block.genesis then some (⊥ : Stamp) else none
  /-- The initial state has no saved confirmation of any slot.

      Read aloud: a node starts with no saved confirmation. -/
  initial_savedConfirmation : ∀ (C : Config) (v : V) (s : Slot),
    (M.initial C v).savedConfirmation s = none
  /-- The initial state holds no lock entry.

      Read aloud: a node starts with no lock. -/
  initial_lockEntries : ∀ (C : Config) (v : V), (M.initial C v).lockEntries = ∅
  /-- The initial state holds no fast block.

      Read aloud: a node starts with no fast block. -/
  initial_fastBlocks : ∀ (C : Config) (v : V), (M.initial C v).fastBlocks = ∅
  /-- The record of the confirmed tip of the initial state is the genesis block.

      Read aloud: a node starts with the genesis block as its confirmed tip's record. -/
  initial_latestConfirmed : ∀ (C : Config) (v : V),
    (M.initial C v).latestConfirmed = Block.genesis
  /-- The initial state's anti-slashing record holds, at every height, no target, no timeout and no
      lock, and the initial state has sent no attestation.

      Read aloud: a node starts having signed nothing. -/
  initial_sent : ∀ (C : Config) (v : V),
    (∀ h, (M.initial C v).sentTarget h = none ∧ (M.initial C v).sentTimeout h = false ∧
      (M.initial C v).sentLock h = none) ∧
    (M.initial C v).sentAttestations = ∅
  /-- The clock of the initial state is `0`, and its validator is `v`.

      Read aloud: a node of `v` starts as `v`, with its clock at zero. -/
  initial_clock : ∀ (C : Config) (v : V), (M.initial C v).t = 0 ∧ (M.initial C v).v = v
  /-- The initial state counts as awake since `C.t_ 0 + C.Δ − 4 * C.Δ * (C.k + 1)`, the start of
      slot `0`'s proposal window computed as a time (the spec's `proposal_window_start C 0`).

      Read aloud: a node starts awake since the first proposal window's start, so a node awake from
      the start passes every duty's test. -/
  initial_awakeSince : ∀ (C : Config) (v : V),
    (M.initial C v).awakeSince = some (C.t_ 0 + C.Δ - 4 * C.Δ * ((C.k : Time) + 1))

end GoldilocksCorrectness.Record
