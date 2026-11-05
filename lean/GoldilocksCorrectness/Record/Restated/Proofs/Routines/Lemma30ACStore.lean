module
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ScoreACStore

@[expose] public section

/-!
# Lemma30ACStore, over a model

The theorems of `GoldilocksCorrectness/Proofs/Routines/Lemma30.lean` on the readers of a
set of votes, over a model `M` whose facts `F` hold: no equivocator among the early votes
with no second late vote, and the supporters from a set of support votes are among the
participants. (The page's theorems on the resolution time `tau` are restated with the
tick's family.)
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Record
open GoldilocksCorrectness.Record.Proofs.Routines.ScoreDefs (supportersOf)

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded in the goal and in every
hypothesis: `omega` does not see a fact stated at either. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

variable {V : Type} [DecidableEq V] [Fintype V]

section

variable (M : GoldilocksModel V) (F : Facts M)
include M F

/-- When the early votes are among the late votes, no validator has two support votes.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: when the early votes are among the late votes, no validator has two support votes. -/
theorem equivocators_support_eq_empty (early late : Finset (GoldfishVote V))
    (h : early ⊆ late) :
    M.equivocators {vote ∈ early | M.no_second_vote_in late vote = true} = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun v hv => ?_
  rw [(mem_equivocators_iff M F)] at hv
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by omega :
    1 < (M.votes_by {vote ∈ early | M.no_second_vote_in late vote = true} v).card)
  simp only [F.rd.votes_by_eq, Finset.mem_filter] at ha hb
  have hN := ha.1.2
  simp only [F.rd.no_second_vote_in_eq, decide_eq_true_eq] at hN
  rcases hN b (h hb.1.1) with h' | h'
  · exact hab h'.symm
  · exact h' (hb.2.trans ha.2.symm)

/-- When the support votes are among `late`, every supporter of a block has a vote in `late`.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: when the support votes are among `late`, every supporter of a block has a vote in `late`. -/
theorem supportersOf_support_subset_participants (Φ : Frame V) (s' : Slot) (B : Block V)
    (support late : Finset (GoldfishVote V)) (h : support ⊆ late) :
    supportersOf M Φ support support s' B ⊆ M.participants late := by
  intro v hv
  obtain ⟨vote, hvote, hval, -⟩ := ((mem_supportersOf_iff M F) _ _ _ _ _ _).1 hv
  exact ((mem_participants_iff M F) _ _).2 ⟨vote, h hvote, hval⟩

end

end GoldilocksCorrectness.Record.Proofs.Routines
