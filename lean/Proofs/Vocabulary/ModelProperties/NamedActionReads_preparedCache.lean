module
public import Model.Vocabulary.Execution.Run
public import Proofs.Vocabulary.ModelProperties.onPhaseTick
public import Proofs.Vocabulary.ModelProperties.Store_toHealing

@[expose] public section

/-!
# Facts about `Execution.NamedActionReads.preparedCache`

The grade cache a node prepares at a time from its node state.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

open DecoupledConsensusModel.Execution DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A phase result already present in the cache aligned to the round of `t` survives the
    preparation, clipped to the finalized block of `before`'s core store. -/
theorem preparedCache_phase_of_align (S : Setup V) (before : NamedNodeState V) (t : Time)
    (r : Round) (p : Phase)
    (h : phaseResult (cacheAtRound (alignRound before.cache (S.hc.round_of (S.E.slotOf t))) r)
      p ≠ none) :
    phaseResult (cacheAtRound (NamedActionReads.preparedCache S before t) r) p =
      clipResult before.st.core.F
        (phaseResult (cacheAtRound (alignRound before.cache (S.hc.round_of (S.E.slotOf t))) r)
          p) := by
  unfold NamedActionReads.preparedCache
  rw [onPhaseTick_phase_of_align _ _ _ _ _ _ _ h, toHealing_F]

end DecoupledConsensusModel.Proofs.ModelProperties

end
