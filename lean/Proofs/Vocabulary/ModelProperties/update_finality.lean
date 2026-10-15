module
public import Model.Vocabulary.Protocol.Handlers

@[expose] public section

/-!
# Facts about the finality update

Facts about `Protocol.update_finality`, the update of a store's finalized block from a chain state.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

variable {V : Type} [DecidableEq V]

/-- The finality update writes `σ`'s finalized block when the store's finalized block is a strict
    ancestor of it, it is an ancestor of the justified block the justification step leaves, and it
    is in the store's viable tree with the maximum height raised to `σ.h`. -/
theorem update_finality_F_of_conditions (st : Protocol.Store V) (σ : Protocol.ChainState V)
    (hprec : Block.prec st.F σ.F = true)
    (hJ : Block.preceq σ.F
      (if Block.preceq st.F σ.J && decide (Protocol.HeightId.mk st.h_j st.J.root <
          Protocol.HeightId.mk σ.h_j σ.J.root) then σ.J else st.J) = true)
    (hviable : σ.F ∈ Protocol.viable_tree st.σ st.F (max st.h_max σ.h) st.T) :
    (Protocol.update_finality st σ).F = σ.F := by
  unfold Protocol.update_finality
  by_cases hm : (Block.preceq st.F σ.J && decide (Protocol.HeightId.mk st.h_j st.J.root <
      Protocol.HeightId.mk σ.h_j σ.J.root)) = true
  · rw [if_pos hm] at hJ
    simp only [if_pos hm]
    split_ifs with hc
    · rfl
    · exact absurd (by
        rw [Bool.and_eq_true, Bool.and_eq_true]
        exact ⟨⟨hprec, hJ⟩, decide_eq_true hviable⟩) hc
  · rw [if_neg hm] at hJ
    simp only [if_neg hm]
    split_ifs with hc
    · rfl
    · exact absurd (by
        rw [Bool.and_eq_true, Bool.and_eq_true]
        exact ⟨⟨hprec, hJ⟩, decide_eq_true hviable⟩) hc

end DecoupledConsensusModel.Proofs.ModelProperties

end
