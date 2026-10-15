import Proofs.Claims.Spec2Claims.Claim13bModel_frameStableRoot

/-!
# Facts about `Protocol.frameSGCandidate`

The frame contract's select candidate for the confirmation record, as the stable root at the store's
own round.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.HealConfig.round_of
  DecoupledConsensusModel.Protocol.Store.toHealing DecoupledConsensusModel.Protocol.frameSGCandidate
  DecoupledConsensusModel.Protocol.readFrame

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- If the frame contract's select candidate of `c` at `st` and any slot is `G`, then the stable
    root of `c` at `st` for the round of `st`'s slot is `G`. -/
theorem frameSGCandidate_stableRoot (c : Protocol.Cache V) (E : Env V)
    (hc : Protocol.HealConfig) (st : Protocol.Store V) (slot : Slot) {G : Block V}
    (h : Protocol.frameSGCandidate c E hc st.toHealing slot = some G) :
    Protocol.frameStableRoot c E hc st.toHealing (hc.round_of st.s) = some G := by
  have h' : ((Protocol.readFrame c st.toHealing (hc.round_of st.s)).g2.bind id).bind
      (Protocol.activePrefix (Protocol.get_filtered_block_tree st.toHealing.toFG)) = some G := by
    unfold Protocol.frameSGCandidate at h
    exact h
  exact frameStableRoot_of_projection c E hc st.toHealing _ h'

end DecoupledConsensusModel.Sts
