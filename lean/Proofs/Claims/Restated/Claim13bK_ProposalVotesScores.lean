import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Record.Wiring

/-!
# Equivocators and participants of the proposer's and the voter's votes

The proposer's and the voter's raw Goldfish vote sets have the same equivocators and the same
participants, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
set_option autoImplicit false

/-- If every vote in `votesV` is in `votesP` or is signed by a validator that equivocates in
    `votesP`, and `votesP ⊆ votesV`, then every validator equivocates in `votesV` exactly when it
    equivocates in `votesP`. -/
theorem equivocates_eq_of_proposalViews (facts : Record.Facts M) {votesP votesV : Finset (GoldfishVote V)}
    (hraw : ∀ u ∈ votesV, u ∈ votesP ∨ M.equivocates votesP u.val_index = true)
    (hsub : votesP ⊆ votesV) (w : V) :
    M.equivocates votesV w = M.equivocates votesP w := by
  cases hP : M.equivocates votesP w with
  | true => exact facts.sch.equivocates_mono_of_subset hsub hP
  | false =>
    cases hV : M.equivocates votesV w with
    | false => rfl
    | true =>
      exfalso
      obtain ⟨u, hu, u', hu', hne, huw, hu'w⟩ := (facts.sch.equivocates_eq_true_iff votesV w).1 hV
      have hin : ∀ z ∈ votesV, z.val_index = w → z ∈ votesP := by
        intro z hz hzw
        rcases hraw z hz with hzP | hzE
        · exact hzP
        · rw [hzw, hP] at hzE
          exact absurd hzE (by decide)
      have hP' : M.equivocates votesP w = true :=
        (facts.sch.equivocates_eq_true_iff votesP w).2
          ⟨u, hin u hu huw, u', hin u' hu' hu'w, hne, huw, hu'w⟩
      rw [hP] at hP'
      exact absurd hP' (by decide)

end

section
set_option autoImplicit false

/-- If every vote in `votesV` is in `votesP` or is signed by a validator that equivocates in
    `votesP`, and `votesP ⊆ votesV`, then every validator participates in `votesV` exactly when it
    participates in `votesP`. -/
theorem participates_eq_of_proposalViews (facts : Record.Facts M) {votesP votesV : Finset (GoldfishVote V)}
    (hraw : ∀ u ∈ votesV, u ∈ votesP ∨ M.equivocates votesP u.val_index = true)
    (hsub : votesP ⊆ votesV) (w : V) :
    M.participates votesV w = M.participates votesP w := by
  apply Bool.eq_iff_iff.2
  rw [facts.sch.participates_eq_true_iff, facts.sch.participates_eq_true_iff]
  constructor
  · rintro ⟨u, hu, huw⟩
    rcases hraw u hu with huP | huE
    · exact ⟨u, huP, huw⟩
    · rw [huw] at huE
      exact (facts.sch.participates_eq_true_iff votesP w).1 (facts.sch.participates_of_equivocates huE)
  · rintro ⟨u, hu, huw⟩
    exact ⟨u, hsub hu, huw⟩

end

end DecoupledConsensusModel.Sts.Restated
