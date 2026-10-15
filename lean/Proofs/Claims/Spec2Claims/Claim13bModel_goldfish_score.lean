import Model.Vocabulary.Protocol.ForkChoice.Goldfish
import Proofs.Claims.ModelIrreducible
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.Confirmation
import Proofs.Vocabulary.ModelProperties.Block_Preceq

/-!
# Facts about `Protocol.goldfish_score`

Lemmas that unfold the Goldfish score and the definitions it is written over:
`Protocol.raw_goldfish_score`, `Protocol.raw_equivocators`, `Protocol.raw_supporters` and
`Protocol.votes_by`.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.equivocates
  DecoupledConsensusModel.Protocol.goldfish_score DecoupledConsensusModel.Protocol.raw_equivocators
  DecoupledConsensusModel.Protocol.raw_goldfish_score
  DecoupledConsensusModel.Protocol.raw_supporters DecoupledConsensusModel.Protocol.votes_by

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- If two vote-set pairs have the same equivocators and the same non-equivocating supporters of
    `C`, the Goldfish score of `C` is the same over both. -/
theorem goldfish_score_eq_of_iff (E : Env V) {T T' : Finset (Block V)}
    {votes support votes' support' : Finset (GoldfishVote V)} (s : Slot) (C : Block V)
    (heq : ∀ w : V, Protocol.equivocates votes w = Protocol.equivocates votes' w)
    (hsup : ∀ w : V, Protocol.equivocates votes w = false →
      ((∃ u ∈ support, u.val_index = w ∧ u.slot = s ∧ Protocol.targets_under T C u = true) ↔
        (∃ u ∈ support', u.val_index = w ∧ u.slot = s ∧
          Protocol.targets_under T' C u = true))) :
    Protocol.goldfish_score E T votes support s C =
      Protocol.goldfish_score E T' votes' support' s C := by
  have hequiv : Protocol.raw_equivocators votes = Protocol.raw_equivocators votes' := by
    ext w
    simp only [Protocol.raw_equivocators, Finset.mem_filter, Finset.mem_univ, true_and, heq w]
  have hsupp : Protocol.raw_supporters T votes support s C =
      Protocol.raw_supporters T' votes' support' s C := by
    ext w
    simp only [Protocol.raw_supporters, Finset.mem_filter, Finset.mem_univ, true_and,
      Protocol.votes_by]
    rw [← heq w]
    constructor
    · rintro ⟨hw, u, ⟨hu, huw⟩, hus, ht⟩
      obtain ⟨u', hu', hu'w, hu's, ht'⟩ := (hsup w hw).1 ⟨u, hu, huw, hus, ht⟩
      exact ⟨hw, u', ⟨hu', hu'w⟩, hu's, ht'⟩
    · rintro ⟨hw, u, ⟨hu, huw⟩, hus, ht⟩
      obtain ⟨u', hu', hu'w, hu's, ht'⟩ := (hsup w hw).2 ⟨u, hu, huw, hus, ht⟩
      exact ⟨hw, u', ⟨hu', hu'w⟩, hu's, ht'⟩
  simp only [Protocol.goldfish_score, Protocol.raw_goldfish_score, hequiv, hsupp]

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- If `D ⪯ C`, the Goldfish score of `C` is at most that of `D`, over the same tree, votes, support
    votes and slot. -/
theorem goldfish_score_le_of_Preceq (E : Env V) (T : Finset (Block V))
    (votes support : Finset (GoldfishVote V)) (s : Slot) {C D : Block V}
    (hDC : Block.Preceq D C) :
    Protocol.goldfish_score E T votes support s C ≤ Protocol.goldfish_score E T votes support s D := by
  have h := Finset.card_le_card (Protocol.supporters_mono E T votes support s (C := D) (B := C)
    (Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mpr hDC))
  simp only [Protocol.goldfishSupporters] at h
  simp only [Protocol.goldfish_score, Protocol.raw_goldfish_score]
  omega

end DecoupledConsensusModel.Sts

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

end DecoupledConsensusModel.Sts
