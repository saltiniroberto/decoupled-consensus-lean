module
public import Proofs.Vocabulary.Protocol.ChainState.Chain
import Proofs.Vocabulary.Objects.Weights

@[expose] public section


namespace DecoupledConsensusModel
namespace Protocol

open Protocol (ChainState HeightConfig)
open Internal

/-! ## Quorum weakening -/

section Weakening

variable {V : Type} [Fintype V]

/-- A superset of a quorum is a quorum. -/
theorem isQuorum_of_subset {E : Electorate V} {S T : Finset V} (h : E.IsQuorum S)
    (hst : S ⊆ T) : E.IsQuorum T :=
  Nat.le_trans h (E.weightOf_mono hst)

end Weakening


/-! ## The height crossing -/

section Crossing

variable {V : Type} [DecidableEq V] [Fintype V]


/-- When `target_participation ⊆ progress`, `process_height_events` either keeps the height or
    raises it by one, and it raises it only when `progress` is a quorum. -/
theorem height_advance_step (E : Env V) (cfg : HeightConfig) {σ : ChainState V}
    (hsub : σ.target_participation ⊆ σ.progress) :
    (Protocol.process_height_events E cfg σ).h = σ.h ∨
      ((Protocol.process_height_events E cfg σ).h = σ.h + 1 ∧
        E.electorate.IsQuorum σ.progress) := by
  rw [process_height_events_eq]
  split_ifs with h1 h2
  · refine Or.inr ⟨by rw [advance_height_h, afterFin_h], ?_⟩
    have hq := isQuorum_of_targetReady E h1
    rw [afterFin_target_participation] at hq
    exact isQuorum_of_subset hq hsub
  · refine Or.inr ⟨by rw [advance_height_h, afterFin_h], ?_⟩
    rcases quorum_of_progReady E cfg h2 with hq | ⟨-, hq⟩
    · rw [afterFin_target_participation] at hq
      exact isQuorum_of_subset hq hsub
    · rwa [afterFin_progress] at hq
  · exact Or.inl (afterFin_h E)


variable (E : Env V) (cfg : HeightConfig)


end Crossing

end Protocol
end DecoupledConsensusModel

end
