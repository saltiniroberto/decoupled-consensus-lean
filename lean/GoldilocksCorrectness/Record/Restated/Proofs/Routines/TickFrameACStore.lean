module
public import GoldilocksCorrectness.Record.Facts
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ACStoreDefs
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.TickFrameDefs

@[expose] public section

/-!
# TickFrameACStore, over a model

The theorems of `GoldilocksCorrectness/Proofs/Routines/TickFrame.lean` on the node's saved
confirmations, lock entries and votes, over a model `M` whose facts `F` hold:
`KeepsConfirmation` (on `TickFrameDefs.lean`) is reflexive, symmetric and transitive, the
valid payload's conditions, and two node states with the same votes have the same votes of
each slot. (The page's theorems on the resolution time `tau` and on the admission of a
Goldfish vote are restated with the receipt's and the tick's families.)

The recovery section at the end of the page states each landed theorem again, as the
landed statement (`type_of%`), and proves it from its record form at the spec's model
`Model.goldilocks` and its facts `goldilocksFacts`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Record
open GoldilocksCorrectness.Record.Proofs.Routines (KeepsVotes KeepsConfirmation)

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded in the goal and in every
hypothesis: `omega` does not see a fact stated at either. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

variable {V : Type} [DecidableEq V] [Fintype V]

section

variable (M : GoldilocksModel V) (F : Facts M)
include M F

/-- Every AC state keeps its own confirmation fields.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: every AC state keeps its own confirmation fields. -/
theorem KeepsConfirmation.refl (n : M.N) :
    KeepsConfirmation M n n :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- `KeepsConfirmation` composes.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: `KeepsConfirmation` composes. -/
theorem KeepsConfirmation.trans {n n' n'' : M.N} (h : KeepsConfirmation M n n')
    (h' : KeepsConfirmation M n' n'') :
    KeepsConfirmation M n n'' :=
  ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1, h'.2.2.2.trans h.2.2.2⟩

/-- Two AC states with the same confirmation fields keep each other's.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: two AC states with the same confirmation fields keep each other's. -/
theorem KeepsConfirmation.symm {n n' : M.N} (h : KeepsConfirmation M n n') :
    KeepsConfirmation M n' n :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.symm⟩

/-- What a valid payload says of a block's votes: every Goldfish vote of `B.votes` has the slot
`B.slot − 1` and a validator of the committee of that slot, and every vote of `B.support_votes` is
one of `B.votes`.

The variables:
- `M`: the model; `F`: its facts;
- `P`: the values, with the committees; `B`: the block.

Read aloud: a valid payload holds votes of the previous slot's committee, for that slot. -/
theorem ac_valid_payload_facts (P : Provisional V) (B : Block V)
    (h : M.ac_valid_payload P B = true) :
    (∀ vote ∈ B.votes, vote.slot = B.slot - 1) ∧ (∀ vote ∈ B.support_votes, vote ∈ B.votes) ∧
      ∀ vote ∈ B.votes, vote.val_index ∈ P.committee (B.slot - 1) := by
  simp only [F.rd.ac_valid_payload_eq, decide_eq_true_eq] at h
  exact h

/-- An AC state with the pool of `n` has `n`'s pool of every slot.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: an AC state with `n`'s pool has `n`'s pool of every slot. -/
theorem pool_of_keepsVotes {n n' : M.N} (h : KeepsVotes M n n') (s : Slot) :
    M.votesHeldSet n' s = M.votesHeldSet n s := by
  rw [F.rd.votesHeldSet_eq, F.rd.votesHeldSet_eq, h.1]

end

/-! ## At the spec's model -/

/-- The landed `GoldilocksCorrectness.Proofs.Routines.KeepsConfirmation.refl`,
recovered from its record form at the spec's model, at
the AC state `n.A` of every node state `n`.

Read aloud: the landed `KeepsConfirmation.refl` holds at the AC state `n.A` of every node state `n`, as the record's theorem at the
spec's model. -/
theorem KeepsConfirmation.refl_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (n : NodeState V), type_of% (@GoldilocksCorrectness.Proofs.Routines.KeepsConfirmation.refl V n.A) := by
  intro n
  simp only [record_goldilocks]
  exact KeepsConfirmation.refl Model.goldilocks goldilocksFacts n

/-- The landed `GoldilocksCorrectness.Proofs.Routines.KeepsConfirmation.trans`,
recovered from its record form at the spec's model, at
the AC states `n.A`, `n'.A`, `n''.A` of every three node states.

Read aloud: the landed `KeepsConfirmation.trans` holds at the AC states `n.A`, `n'.A`, `n''.A` of every three node states, as the record's theorem at the
spec's model. -/
theorem KeepsConfirmation.trans_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (n n' n'' : NodeState V), type_of% (@GoldilocksCorrectness.Proofs.Routines.KeepsConfirmation.trans V n.A n'.A n''.A) := by
  intro n n' n''
  simp only [record_goldilocks]
  exact KeepsConfirmation.trans Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.KeepsConfirmation.symm`,
recovered from its record form at the spec's model, at
the AC states `n.A`, `n'.A` of every two node states.

Read aloud: the landed `KeepsConfirmation.symm` holds at the AC states `n.A`, `n'.A` of every two node states, as the record's theorem at the
spec's model. -/
theorem KeepsConfirmation.symm_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (n n' : NodeState V), type_of% (@GoldilocksCorrectness.Proofs.Routines.KeepsConfirmation.symm V n.A n'.A) := by
  intro n n'
  simp only [record_goldilocks]
  exact KeepsConfirmation.symm Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.ac_valid_payload_facts`,
recovered from its record form at the spec's model.

Read aloud: the landed `ac_valid_payload_facts` holds, as the record's theorem at the spec's
model. -/
theorem ac_valid_payload_facts_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.ac_valid_payload_facts V _) := by
  exact ac_valid_payload_facts Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.pool_of_keepsVotes`,
recovered from its record form at the spec's model, at
the AC states `n.A`, `n'.A` of every two node states.

Read aloud: the landed `pool_of_keepsVotes` holds at the AC states `n.A`, `n'.A` of every two node states, as the record's theorem at the
spec's model. -/
theorem pool_of_keepsVotes_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (n n' : NodeState V), type_of% (@GoldilocksCorrectness.Proofs.Routines.pool_of_keepsVotes V _ n.A n'.A) := by
  intro n n'
  simp only [record_goldilocks]
  exact pool_of_keepsVotes Model.goldilocks goldilocksFacts

end GoldilocksCorrectness.Record.Proofs.Routines
