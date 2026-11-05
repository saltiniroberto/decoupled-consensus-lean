module
public import GoldilocksCorrectness.Record.Facts
public import GoldilocksCorrectness.Proofs.Routines.Wiring

@[expose] public section

/-!
# Wiring, over a model

The theorems of `GoldilocksCorrectness/Proofs/Routines/Wiring.lean` that are not receipt facts,
over a model `M` whose facts `F` hold, each proved from the receipt facts `F.rcv`: a delivery keeps
the votes filed by slot and grows the node state (`receive_grows`, from `receive_step`), keeps the
wake time (`receive_awakeSince`, from `receive_keeps_confirmation`), and re-sends the delivered
object and the Goldfish votes it carries (`mem_relayedObjects_self`,
`gfVote_mem_relayedObjects_block`, `gfVote_mem_relayedObjects`, from `mem_relayedObjects_iff`).


The recovery section at the end of the page states each landed theorem again, as the landed
statement (`type_of%`), and proves it from its record form at the spec's model `Model.goldilocks`
and its facts `goldilocksFacts`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section

variable (M : GoldilocksModel V) (F : Facts M)
include M F

/-- A delivery to a node state whose votes are filed by slot keeps them filed by slot, and grows
the node state: the tree, the finalized block's chain, the votes of each slot, and the stamps of
the blocks and the votes held.

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `o`: the object;
- `hk`: `n`'s votes are filed by slot.

Read aloud: a delivery keeps the votes filed by slot and grows the node state. -/
theorem receive_grows [RootOrder] (C : Config) (P : Provisional V) (X : External V) (n : M.N)
    (o : NamedObject V) (hk : SlotKeyed M n) :
    SlotKeyed M (M.receive C P X n o) ∧
      (n.tree ⊆ (M.receive C P X n o).tree ∧
        n.finalized.AncestorEq (M.receive C P X n o).finalized ∧
        (∀ s : Slot, n.votesHeld s <+: (M.receive C P X n o).votesHeld s) ∧
        (∀ B ∈ n.tree, (M.receive C P X n o).blockStamp B = n.blockStamp B) ∧
        ∀ s : Slot, ∀ vote ∈ n.votesHeld s,
          (M.receive C P X n o).voteStamp vote = n.voteStamp vote) :=
  ⟨(F.rcv.receive_step C P X n o hk).1, (F.rcv.receive_step C P X n o hk).2.1⟩

/-- A delivery keeps the time since which the node has been awake.

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `o`: the object.

Read aloud: a delivery does not change the time since which the node has been awake. -/
theorem receive_awakeSince [RootOrder] (C : Config) (P : Provisional V) (X : External V)
    (n : M.N) (o : NamedObject V) :
    (M.receive C P X n o).awakeSince = n.awakeSince :=
  (F.rcv.receive_keeps_confirmation C P X n o).2.2.2.2.1

/-- The objects re-sent on a delivery include the delivered object.

The variables:
- `M`: the model; `F`: its facts;
- `o`: the object.

Read aloud: a node re-sends the object delivered to it. -/
theorem mem_relayedObjects_self (o : NamedObject V) : o ∈ M.relayedObjects o :=
  (F.rcv.mem_relayedObjects_iff o o).2 (Or.inl rfl)

/-- The objects re-sent for a block include, as Goldfish-vote objects, the votes the block
includes.

The variables:
- `M`: the model; `F`: its facts;
- `B`: the block; `vote`: a vote of `B.votes`.

Read aloud: a node re-sends each vote of a block delivered to it. -/
theorem gfVote_mem_relayedObjects_block {B : Block V} {vote : GoldfishVote V}
    (h : vote ∈ B.votes) : NamedObject.gfVote vote ∈ M.relayedObjects (NamedObject.block B) :=
  (F.rcv.mem_relayedObjects_iff _ _).2 (Or.inr ⟨B, rfl, Or.inl ⟨vote, h, rfl⟩⟩)

/-- An object that carries a Goldfish vote (the vote itself, or a block whose `votes` holds it)
has that vote among the objects re-sent for it.

The variables:
- `M`: the model; `F`: its facts;
- `o`: the object; `vote`: the vote it carries.

Read aloud: a node re-sends every vote the delivered object carries. -/
theorem gfVote_mem_relayedObjects {o : NamedObject V} {vote : GoldfishVote V}
    (h : o = NamedObject.gfVote vote ∨ ∃ B : Block V, o = NamedObject.block B ∧ vote ∈ B.votes) :
    NamedObject.gfVote vote ∈ M.relayedObjects o := by
  rcases h with rfl | ⟨B, rfl, hB⟩
  · exact mem_relayedObjects_self M F _
  · exact gfVote_mem_relayedObjects_block M F hB

end

/-! ## At the spec's model -/

/-- The landed `GoldilocksCorrectness.Proofs.Routines.receive_grows`, recovered from its record
form at the spec's model.

Read aloud: the landed `receive_grows` holds, as the record's theorem at the spec's model. -/
theorem receive_grows_recovered {V : Type} [DecidableEq V] [Fintype V] [RootOrder] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.receive_grows V _ _ _) := by
  exact fun C P X n o hk => receive_grows Model.goldilocks goldilocksFacts C P X n o hk

/-- The landed `GoldilocksCorrectness.Proofs.Routines.receive_awakeSince`, recovered from its
record form at the spec's model.

Read aloud: the landed `receive_awakeSince` holds, as the record's theorem at the spec's model. -/
theorem receive_awakeSince_recovered {V : Type} [DecidableEq V] [Fintype V] [RootOrder] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.receive_awakeSince V _ _ _) := by
  exact fun C P X n o => receive_awakeSince Model.goldilocks goldilocksFacts C P X n o

/-- The landed `GoldilocksCorrectness.Proofs.Routines.mem_relayedObjects_self`, recovered from its
record form at the spec's model.

Read aloud: the landed `mem_relayedObjects_self` holds, as the record's theorem at the spec's
model. -/
theorem mem_relayedObjects_self_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.mem_relayedObjects_self V) := by
  exact fun o => mem_relayedObjects_self Model.goldilocks goldilocksFacts o

/-- The landed `GoldilocksCorrectness.Proofs.Routines.gfVote_mem_relayedObjects_block`, recovered
from its record form at the spec's model.

Read aloud: the landed `gfVote_mem_relayedObjects_block` holds, as the record's theorem at the
spec's model. -/
theorem gfVote_mem_relayedObjects_block_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.gfVote_mem_relayedObjects_block V) := by
  exact fun h => gfVote_mem_relayedObjects_block Model.goldilocks goldilocksFacts h

/-- The landed `GoldilocksCorrectness.Proofs.Routines.gfVote_mem_relayedObjects`, recovered from
its record form at the spec's model.

Read aloud: the landed `gfVote_mem_relayedObjects` holds, as the record's theorem at the spec's
model. -/
theorem gfVote_mem_relayedObjects_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.gfVote_mem_relayedObjects V) := by
  exact fun h => gfVote_mem_relayedObjects Model.goldilocks goldilocksFacts h

end GoldilocksCorrectness.Record.Proofs.Routines
