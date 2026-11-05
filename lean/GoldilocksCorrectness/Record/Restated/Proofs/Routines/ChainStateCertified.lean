module
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ChainStateOf

@[expose] public section

/-!
# ChainStateCertified, over a model

The theorems of `GoldilocksCorrectness/Proofs/Routines/ChainStateCertified.lean` over a model `M`
whose facts `F` hold: one state transition keeps a pending justification, and the first advance past
a height.

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
open GoldilocksCorrectness.Record.Statements.Routines (IsEntry JustificationCertOn ProgressCertOn FinalityCertOn)
open GoldilocksCorrectness.Record.Proofs.Routines (JustifiedOnChainWith)
open GoldilocksCorrectness.Statements.Routines (chainStateOf)

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded in the goal and in every
hypothesis: `omega` does not see a fact stated at either. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

variable {V : Type} [DecidableEq V] [Fintype V]

section

variable (M : GoldilocksModel V) (F : Facts M)
include M F

/-- **Kit theorem, one state transition keeps a pending justification.** Take a pending
justification `e₀` of `σ` with at most one pending justification after it, and none unless
`σ.h ≥ h + 1`; `e₀.j < h ≤ σ.h`; and the state transition on the block `B` leaving a justification
height at most `h`. Then the transition finalizes at a height at least `e₀.j`, or it keeps `e₀`
pending in the same position, keeps every validator counted for `e₀.j`, and counts at `e₀.j` every
attestation of `B` with the finality pair `(e₀.j, e₀.T)`.

Why: counting the attestations keeps the pending list and adds to the participation at `e₀.j`
(`foldl_finality_participation`); the loop leaves `h_F'`, and when `h_F' < e₀.j` the filter keeps
`e₀` and its tail. A justification in this transition is at `σ.h`, at most `h`, so `σ.h = h` and the
tail is empty; then `newest` keeps `e₀` and the new pair (`K_W ≥ 2`), and the height becomes
`h + 1`. The participation at `e₀.j` is reset only by a justification at `e₀.j < σ.h`, which is not
this one.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `σ`: the parent's chain state; `B`: the block; `e₀`: the pending
  justification; `h`: the bound on the justification height.

In this text, `σ` is `M.chainStateOf C B.parent`, the chain state of `B`'s
parent; `hB`: `B` is not the genesis block.

Read aloud: one block either finalizes at least the pending pair's height, or keeps the pair pending, keeps its counted validators, and counts the block's finality pairs for it. -/
theorem pending_pair_step (C : Config) (B : Block V) (hB : B ≠ Block.genesis) (e₀ : M.PP)
    (h : Height)
    (hshape : ∃ l₁ l₂ : List (M.PP), (M.chainStateOf C B.parent).pending_finality = l₁ ++ e₀ :: l₂ ∧
      (l₂ = [] ∨ (l₂.length = 1 ∧ h + 1 ≤ (M.chainStateOf C B.parent).h)))
    (hj₀ : e₀.j < h) (hh : h ≤ (M.chainStateOf C B.parent).h)
    (hJ : (M.chainStateOf C B).h_j ≤ h) :
    e₀.j ≤ (M.chainStateOf C B).h_F ∨
      ((∃ l₁ l₂ : List (M.PP), (M.chainStateOf C B).pending_finality = l₁ ++ e₀ :: l₂ ∧
        (l₂ = [] ∨ (l₂.length = 1 ∧ h + 1 ≤ (M.chainStateOf C B).h))) ∧
      (∀ v ∈ (M.chainStateOf C B.parent).finality_participation e₀.j,
        v ∈ (M.chainStateOf C B).finality_participation e₀.j) ∧
      (∀ a ∈ B.attestations, a.finality_pair = some (FinalityPair.mk e₀.j e₀.T.root) →
        a.val_index ∈ (M.chainStateOf C B).finality_participation e₀.j)) :=
  F.cs.pending_pair_step C B hB e₀ h hshape hj₀ hh hJ

/-- **The first advance past a height, with the justification height.** When `1 ≤ h` and the chain
state of `B` has a height greater than `h`, some block `Y`, `B` or an ancestor of `B` and not the
genesis block, has a parent at the height `h` and is itself at the height `h + 1`; and `Y`'s
justification height is `h`, or the slot of the parent's `T_h`, plus `δt`, is at most `Y`'s slot.

Why: as Lemma 67 (b) (`lem67b_first_advance_cases`), reading the branch of the state transition
that raised the height: the justification branch sets the justification height to the parent's
height, the timeout branch passed the slot test.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `B`: the block; `h`: the height.

Read aloud: the first block past the height `h` on a chain was raised by a justification at `h`, or by a timeout. -/
theorem first_advance_justified_or_timeout (C : Config) (B : Block V) (h : Height)
    (h1 : 1 ≤ h) (hlt : h < (M.chainStateOf C B).h) :
    ∃ Y : Block V, Y.AncestorEq B ∧ Y ≠ Block.genesis ∧
      (M.chainStateOf C Y.parent).h = h ∧ (M.chainStateOf C Y).h = h + 1 ∧
      ((M.chainStateOf C Y).h_j = h ∨ (M.chainStateOf C Y.parent).T_h.slot + C.δt ≤ Y.slot) :=
  F.cs.first_advance_justified_or_timeout C B h h1 hlt

end

/-! ## At the spec's model -/

/-- The landed `GoldilocksCorrectness.Proofs.Routines.pending_pair_step`
at the chain state of `B`'s parent,
`chainStateOf C B.parent`, for every block `B` that is not the genesis block,
recovered from its record form at the spec's model.

Read aloud: the landed `pending_pair_step` holds at the parent's chain state of every
non-genesis block, as the record's theorem at the spec's model. -/
theorem pending_pair_step_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (C : Config) (B : Block V), B ≠ Block.genesis →
      type_of% (@GoldilocksCorrectness.Proofs.Routines.pending_pair_step V _ _ C
        (GoldilocksCorrectness.Statements.Routines.chainStateOf C B.parent) B) := by
  intro C B hB
  cases B with
  | genesis => exact absurd rfl hB
  | node p s r votes support ats v =>
      exact pending_pair_step Model.goldilocks goldilocksFacts C _ hB

/-- The landed `GoldilocksCorrectness.Proofs.Routines.first_advance_justified_or_timeout`,
recovered from its record form at the spec's model.

Read aloud: the landed `first_advance_justified_or_timeout` holds, as the record's theorem at the spec's
model. -/
theorem first_advance_justified_or_timeout_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.first_advance_justified_or_timeout V _ _) := by
  exact first_advance_justified_or_timeout Model.goldilocks goldilocksFacts

end GoldilocksCorrectness.Record.Proofs.Routines
