module
public import Model.Vocabulary.Protocol.Grades

@[expose] public section

/-!
# Facts about the round's frame

Facts about `Protocol.readFrame`, the frame of a round read from a grade cache at a store, which
reads only the store's finalized block.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

variable {V : Type} [DecidableEq V]

/-- The grade-2 result of the round-`r` frame read from the cache `c` at `st` is the grade-2 result
    of `c`'s round-`r` frame, clipped to `st`'s finalized block. -/
theorem readFrame_g2 (c : DecoupledConsensusModel.Protocol.Cache V)
    (st : Protocol.HealingStore V) (r : Round) :
    (DecoupledConsensusModel.Protocol.readFrame c st r).g2 =
      DecoupledConsensusModel.Protocol.clipResult st.F
        (DecoupledConsensusModel.Protocol.cacheAtRound c r).g2 := rfl

/-- For every phase `p`, the result for `p` of the round-`r` frame read from the cache `c` at `st`
    is the result for `p` of `c`'s round-`r` frame, clipped to `st`'s finalized block. -/
theorem readFrame_phase (c : DecoupledConsensusModel.Protocol.Cache V)
    (st : Protocol.HealingStore V) (r : Round) (p : DecoupledConsensusModel.Protocol.Phase) :
    DecoupledConsensusModel.Protocol.phaseResult
        (DecoupledConsensusModel.Protocol.readFrame c st r) p =
      DecoupledConsensusModel.Protocol.clipResult st.F
        (DecoupledConsensusModel.Protocol.phaseResult
          (DecoupledConsensusModel.Protocol.cacheAtRound c r) p) := by
  cases p <;> rfl

end DecoupledConsensusModel.Proofs.ModelProperties

end
