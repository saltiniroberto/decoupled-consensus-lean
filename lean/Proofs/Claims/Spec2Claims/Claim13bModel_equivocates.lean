module
public import Model.Vocabulary.Protocol.Schedule
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# Facts about `Protocol.equivocates` and `Protocol.participates`

The two per-signer tests over a set of Goldfish votes: `Protocol.equivocates` (the set holds two
distinct votes of the signer) and `Protocol.participates` (the set holds a vote of the signer).
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.equivocates
  DecoupledConsensusModel.Protocol.votes_by

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- `w` equivocates in `votes` exactly when `votes` holds two different votes both signed by `w`. -/
theorem equivocates_eq_true_iff (votes : Finset (GoldfishVote V)) (w : V) :
    Protocol.equivocates votes w = true ↔
      ∃ u ∈ votes, ∃ u' ∈ votes, u ≠ u' ∧ u.val_index = w ∧ u'.val_index = w := by
  have h21 : ∀ n : Nat, 2 ≤ n ↔ 1 < n := fun _ => Iff.rfl
  rw [Protocol.equivocates, decide_eq_true_eq, h21, Finset.one_lt_card]
  simp only [Protocol.votes_by, Finset.mem_filter]
  constructor
  · rintro ⟨u, ⟨hu, huw⟩, u', ⟨hu', hu'w⟩, hne⟩
    exact ⟨u, hu, u', hu', hne, huw, hu'w⟩
  · rintro ⟨u, hu, u', hu', hne, huw, hu'w⟩
    exact ⟨u, ⟨hu, huw⟩, u', ⟨hu', hu'w⟩, hne⟩

/-- `w` participates in `votes` exactly when `votes` holds a vote signed by `w`. -/
theorem participates_eq_true_iff (votes : Finset (GoldfishVote V)) (w : V) :
    Protocol.participates votes w = true ↔ ∃ u ∈ votes, u.val_index = w := by
  rw [Protocol.participates, decide_eq_true_eq, Finset.card_pos]
  simp only [Finset.Nonempty, Protocol.votes_by, Finset.mem_filter]

/-- If `votes ⊆ votes'` and `w` equivocates in `votes`, then `w` equivocates in `votes'`. -/
theorem equivocates_mono_of_subset {votes votes' : Finset (GoldfishVote V)}
    (hsub : votes ⊆ votes') {w : V} (h : Protocol.equivocates votes w = true) :
    Protocol.equivocates votes' w = true := by
  rw [equivocates_eq_true_iff] at h ⊢
  obtain ⟨u, hu, u', hu', hne, huw, hu'w⟩ := h
  exact ⟨u, hsub hu, u', hsub hu', hne, huw, hu'w⟩

/-- If `w` equivocates in `votes`, then `w` participates in `votes`. -/
theorem participates_of_equivocates {votes : Finset (GoldfishVote V)} {w : V}
    (h : Protocol.equivocates votes w = true) : Protocol.participates votes w = true := by
  rw [equivocates_eq_true_iff] at h
  obtain ⟨u, hu, _, _, _, huw, _⟩ := h
  exact (participates_eq_true_iff votes w).2 ⟨u, hu, huw⟩

/-- If `votes` holds at most one vote of `w`, then `w` does not equivocate in `votes`. -/
theorem equivocates_eq_false_of_card_le_one {votes : Finset (GoldfishVote V)} {w : V}
    (h : (Protocol.votes_by votes w).card ≤ 1) : Protocol.equivocates votes w = false := by
  simp only [Protocol.equivocates, decide_eq_false_iff_not]
  omega

end DecoupledConsensusModel.Sts
