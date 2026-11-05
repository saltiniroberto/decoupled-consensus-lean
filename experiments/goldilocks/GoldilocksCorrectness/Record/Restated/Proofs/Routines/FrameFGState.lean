module
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.FGStateReaders

@[expose] public section

/-!
# FrameFGState, over a model: Lemma 56 and its three cases

The FG-state theorems of `GoldilocksCorrectness/Proofs/Routines/Frame.lean` over a model `M` whose
facts `F` hold: Lemma 56, the frame of a node state of a given shape, and its three cases. Each is
stated for a node state `n` satisfying the model's node invariant `M.nodeInv C P X n` (the readers'
facts `F.ndAdded` hold under it), with `hMax M C n` for the stored greatest height and
`M.chainStateOf C B` for the stored chain state of a block. Lemma 56's statement about viability
reads the blocks of `n`'s tree: the record reads the chain state of a block of the tree only.

The recovery section at the end of the page states each landed theorem again, as the landed
statement (`type_of%`) at the FG state `n.S` of a node state `n` satisfying the spec's model's node
invariant, and proves it from its record form at the spec's model `Model.goldilocks` and its facts
`goldilocksFacts`, reading `hMax` as the stored `n.S.h_max` (`hMax_goldilocks`) and the chain state
of a block of the tree as the stored one (the invariant's clause `ChainStatesComputed`). The landed
Lemma 56 states the viability of every block, read off its stored chain state, of the tree or not:
its record form takes the block in the tree, and it has no recovery here (as the landed
`is_viable_iff` on `FGStateReaders.lean`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Record
open GoldilocksCorrectness.Record.Statements.Routines (hMax FrameShape BoxOne BoxTwo BoxThree
  goldilocks_BoxOne goldilocks_BoxTwo)

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded in the goal and in every
hypothesis: `omega` does not see a fact stated at either. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

variable {V : Type} [DecidableEq V] [Fintype V]

section

variable (M : GoldilocksModel V) (F : Facts M)
include M F

/-- **`lem56_frame_of_shape` under the clock-free part of the node invariant.** Its hypothesis `hI` is
`M.nodeInvCore C P X n`, the clauses of the node invariant that compare no stamp with the clock, which
hold for every validator, one in the adversary set included; `lem56_frame_of_shape` is this theorem at
`F.nd.nodeInv_core hI`.

**Lemma 56, the frame of a shape.**

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `hI`: `n` satisfies the clock-free part of the model's node invariant,
  `M.nodeInvCore C P X n`; `ρ`: the root; `φ`: the least height of a viable
  block.

Read aloud: the frame of a shape is rooted at `ρ`, a block of the tree is viable when its height is
at least `φ`, and its viable heads are the accepted blocks on `ρ`'s chain, from `ρ` on, that reach
the height `φ`. -/
theorem lem56_frame_of_shape_of_core (C : Config) (P : Provisional V) (X : External V) (n : M.N)
    (hI : M.nodeInvCore C P X n) (ρ : Block V) (φ : Height)
    (hShape : FrameShape M n ρ φ) :
    (M.fg_to_ac n).fc_root = ρ ∧
    (∀ B ∈ n.tree, M.is_viable n B = true ↔ φ ≤ (M.chainStateOf C B).h) ∧
    (∀ B : Block V, B ∈ (M.fg_to_ac n).viable_heads ↔
      B ∈ n.tree ∧ n.finalized.AncestorEq B ∧ ρ.AncestorEq B ∧ φ ≤ (M.chainStateOf C B).h) := by
  obtain ⟨hρ, hφ⟩ := hShape
  have hroot : (M.fg_to_ac n).fc_root = ρ := by rw [F.rd.fg_to_ac_eq]; exact hρ
  have hviable : ∀ B ∈ n.tree, M.is_viable n B = true ↔ φ ≤ (M.chainStateOf C B).h := by
    intro B hB
    rw [F.ndAdded.is_viable_eq_of_core hI hB, hφ, decide_eq_true_eq]
  refine ⟨hroot, hviable, fun B => ?_⟩
  rw [← hρ, F.rd.fg_to_ac_eq]
  simp only [Finset.mem_filter, Bool.and_eq_true]
  constructor
  · rintro ⟨⟨hB, hF⟩, hr, hv⟩
    exact ⟨hB, hF, hr, (hviable B hB).1 hv⟩
  · rintro ⟨hB, hF, hr, hv⟩
    exact ⟨⟨hB, hF⟩, hr, (hviable B hB).2 hv⟩

/-- **Lemma 56, the frame of a shape.** The proof; the audited statement is in
`Record/Restated/Statements/Routines/FrameStatementsFGState.lean`.

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `hI`: `n` satisfies the model's node invariant; `ρ`: the root; `φ`: the least height of a viable
  block.

Read aloud: the frame of a shape is rooted at `ρ`, a block of the tree is viable when its height is
at least `φ`, and its viable heads are the accepted blocks on `ρ`'s chain, from `ρ` on, that reach
the height `φ`. -/
theorem lem56_frame_of_shape (C : Config) (P : Provisional V) (X : External V) (n : M.N)
    (hI : M.nodeInv C P X n) (ρ : Block V) (φ : Height)
    (hShape : FrameShape M n ρ φ) :
    (M.fg_to_ac n).fc_root = ρ ∧
    (∀ B ∈ n.tree, M.is_viable n B = true ↔ φ ≤ (M.chainStateOf C B).h) ∧
    (∀ B : Block V, B ∈ (M.fg_to_ac n).viable_heads ↔
      B ∈ n.tree ∧ n.finalized.AncestorEq B ∧ ρ.AncestorEq B ∧ φ ≤ (M.chainStateOf C B).h) :=
  lem56_frame_of_shape_of_core M F C P X n (F.nd.nodeInv_core hI) ρ φ hShape

/-- **`frameShape_of_boxOne` under the clock-free part of the node invariant.** Its hypothesis `hI` is
`M.nodeInvCore C P X n`, the clauses of the node invariant that compare no stamp with the clock, which
hold for every validator, one in the adversary set included; `frameShape_of_boxOne` is this theorem at
`F.nd.nodeInv_core hI`.

**Lemma 56, box 1: not contested; root the finalized block, least viable height
`hMax M C n − 1`.**

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `hI`: `n` satisfies the clock-free part of the model's node invariant,
  `M.nodeInvCore C P X n`.

Read aloud: in box 1 the fork choice is rooted at the finalized block and a block is viable from
height `hMax M C n − 1` on. -/
theorem frameShape_of_boxOne_of_core (C : Config) (P : Provisional V) (X : External V) (n : M.N)
    (hI : M.nodeInvCore C P X n) (h : BoxOne M C n) :
    M.fg_contest n = false ∧ FrameShape M n n.finalized (hMax M C n - 1) := by
  unfold BoxOne at h
  have hne : hMax M C n ≠ n.justifiedHeight + 1 := by
    intro he
    omega_nat
  have hc : M.fg_contest n = false := by
    rw [F.ndAdded.fg_contest_eq_of_core hI, if_pos hne]
  refine ⟨hc, ?_, ?_⟩
  · rw [F.ndAdded.get_fc_root_eq_of_core hI, if_neg (by simp [hne])]
  · rw [F.ndAdded.head_height_floor_eq_of_core hI, hc]
    rfl

/-- **Lemma 56, box 1: not contested; root the finalized block, least viable height
`hMax M C n − 1`.** The proof; the audited statement is in
`Record/Restated/Statements/Routines/FrameStatementsFGState.lean`.

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `hI`: `n` satisfies the model's node invariant.

Read aloud: in box 1 the fork choice is rooted at the finalized block and a block is viable from
height `hMax M C n − 1` on. -/
theorem frameShape_of_boxOne (C : Config) (P : Provisional V) (X : External V) (n : M.N)
    (hI : M.nodeInv C P X n) (h : BoxOne M C n) :
    M.fg_contest n = false ∧ FrameShape M n n.finalized (hMax M C n - 1) :=
  frameShape_of_boxOne_of_core M F C P X n (F.nd.nodeInv_core hI) h

/-- **`frameShape_of_boxTwo` under the clock-free part of the node invariant.** Its hypothesis `hI` is
`M.nodeInvCore C P X n`, the clauses of the node invariant that compare no stamp with the clock, which
hold for every validator, one in the adversary set included; `frameShape_of_boxTwo` is this theorem at
`F.nd.nodeInv_core hI`.

**Lemma 56, box 2: root `J₀`, least viable height `hMax M C n − 1`.**

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `hI`: `n` satisfies the clock-free part of the model's node invariant,
  `M.nodeInvCore C P X n`; `J₀`: the justified block.

Read aloud: in box 2 the fork choice is rooted at the justified block `J₀` and a block is viable
from height `hMax M C n − 1` on. -/
theorem frameShape_of_boxTwo_of_core (C : Config) (P : Provisional V) (X : External V) (n : M.N)
    (hI : M.nodeInvCore C P X n) (J₀ : Block V) (h : BoxTwo M C n J₀) :
    FrameShape M n J₀ (hMax M C n - 1) := by
  obtain ⟨he, hc, hJ⟩ := h
  refine ⟨?_, ?_⟩
  · rw [F.ndAdded.get_fc_root_eq_of_core hI, if_pos (by simp [he, hc])]
    exact hJ
  · rw [F.ndAdded.head_height_floor_eq_of_core hI, hc]
    rfl

/-- **Lemma 56, box 2: root `J₀`, least viable height `hMax M C n − 1`.** The proof; the audited
statement is in `Record/Restated/Statements/Routines/FrameStatementsFGState.lean`.

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `hI`: `n` satisfies the model's node invariant; `J₀`: the justified block.

Read aloud: in box 2 the fork choice is rooted at the justified block `J₀` and a block is viable
from height `hMax M C n − 1` on. -/
theorem frameShape_of_boxTwo (C : Config) (P : Provisional V) (X : External V) (n : M.N)
    (hI : M.nodeInv C P X n) (J₀ : Block V) (h : BoxTwo M C n J₀) :
    FrameShape M n J₀ (hMax M C n - 1) :=
  frameShape_of_boxTwo_of_core M F C P X n (F.nd.nodeInv_core hI) J₀ h

/-- **`frameShape_of_boxThree` under the clock-free part of the node invariant.** Its hypothesis `hI` is
`M.nodeInvCore C P X n`, the clauses of the node invariant that compare no stamp with the clock, which
hold for every validator, one in the adversary set included; `frameShape_of_boxThree` is this theorem at
`F.nd.nodeInv_core hI`.

**Lemma 56, box 3: `hMax M C n = n.justifiedHeight + 1`; root the finalized block, least
viable height `hMax M C n`.**

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `hI`: `n` satisfies the clock-free part of the model's node invariant,
  `M.nodeInvCore C P X n`.

Read aloud: in box 3 the fork choice is rooted at the finalized block and a block is viable from
height `hMax M C n` on. -/
theorem frameShape_of_boxThree_of_core (C : Config) (P : Provisional V) (X : External V) (n : M.N)
    (hI : M.nodeInvCore C P X n) (h : BoxThree M n) :
    hMax M C n = n.justifiedHeight + 1 ∧ FrameShape M n n.finalized (hMax M C n) := by
  unfold BoxThree at h
  have he : hMax M C n = n.justifiedHeight + 1 := h_max_of_contested_of_core M F C P X n hI h
  refine ⟨he, ?_, ?_⟩
  · rw [F.ndAdded.get_fc_root_eq_of_core hI, if_neg (by simp [h])]
  · rw [F.ndAdded.head_height_floor_eq_of_core hI, if_pos h]

/-- **Lemma 56, box 3: `hMax M C n = n.justifiedHeight + 1`; root the finalized block, least
viable height `hMax M C n`.** The proof; the audited statement is in
`Record/Restated/Statements/Routines/FrameStatementsFGState.lean`.

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `hI`: `n` satisfies the model's node invariant.

Read aloud: in box 3 the fork choice is rooted at the finalized block and a block is viable from
height `hMax M C n` on. -/
theorem frameShape_of_boxThree (C : Config) (P : Provisional V) (X : External V) (n : M.N)
    (hI : M.nodeInv C P X n) (h : BoxThree M n) :
    hMax M C n = n.justifiedHeight + 1 ∧ FrameShape M n n.finalized (hMax M C n) :=
  frameShape_of_boxThree_of_core M F C P X n (F.nd.nodeInv_core hI) h

end

/-! ## At the spec's model -/

/-- The landed `GoldilocksCorrectness.Proofs.Routines.frameShape_of_boxOne`, recovered from its
record form at the spec's model, at the FG state `n.S` of every node state `n` satisfying the spec's
model's node invariant.

Read aloud: the landed `frameShape_of_boxOne` holds at the FG state of every node state satisfying
the invariant. -/
theorem frameShape_of_boxOne_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (C : Config) (P : Provisional V) (X : External V) (n : NodeState V),
      (Model.goldilocks (V := V)).nodeInv C P X n →
      type_of% (@GoldilocksCorrectness.Proofs.Routines.frameShape_of_boxOne V _ n.S) := by
  intro C P X n hI h
  have h' := frameShape_of_boxOne Model.goldilocks goldilocksFacts C P X n hI
    ((goldilocks_BoxOne C n (hMax_goldilocks hI).symm).1 h)
  rw [hMax_goldilocks hI] at h'
  exact h'

/-- The landed `GoldilocksCorrectness.Proofs.Routines.frameShape_of_boxTwo`, recovered from its
record form at the spec's model, at the FG state `n.S` of every node state `n` satisfying the spec's
model's node invariant.

Read aloud: the landed `frameShape_of_boxTwo` holds at the FG state of every node state satisfying
the invariant. -/
theorem frameShape_of_boxTwo_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (C : Config) (P : Provisional V) (X : External V) (n : NodeState V),
      (Model.goldilocks (V := V)).nodeInv C P X n →
      type_of% (@GoldilocksCorrectness.Proofs.Routines.frameShape_of_boxTwo V _ n.S) := by
  intro C P X n hI J₀ h
  have h' := frameShape_of_boxTwo Model.goldilocks goldilocksFacts C P X n hI J₀
    ((goldilocks_BoxTwo C n J₀ (hMax_goldilocks hI).symm).1 h)
  rw [hMax_goldilocks hI] at h'
  exact h'

/-- The landed `GoldilocksCorrectness.Proofs.Routines.frameShape_of_boxThree`, recovered from its
record form at the spec's model, at the FG state `n.S` of every node state `n` satisfying the spec's
model's node invariant.

Read aloud: the landed `frameShape_of_boxThree` holds at the FG state of every node state
satisfying the invariant. -/
theorem frameShape_of_boxThree_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (C : Config) (P : Provisional V) (X : External V) (n : NodeState V),
      (Model.goldilocks (V := V)).nodeInv C P X n →
      type_of% (@GoldilocksCorrectness.Proofs.Routines.frameShape_of_boxThree V _ n.S) := by
  intro C P X n hI h
  have h' := frameShape_of_boxThree Model.goldilocks goldilocksFacts C P X n hI h
  rw [hMax_goldilocks hI] at h'
  exact h'

end GoldilocksCorrectness.Record.Proofs.Routines
