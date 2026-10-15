module
public import Model.Vocabulary.Protocol.Store
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# Facts about `Protocol.HealingStore.gradeView`

Equations for the fields of the grade view a grade reads from a healing store, taken at the healing
store `Protocol.Store.toHealing` builds from a store.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.HealingStore.gradeView
  DecoupledConsensusModel.Protocol.Store.sg_pool DecoupledConsensusModel.Protocol.Store.toHealing

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- The tree of the grade view read from a store's healing view is that store's tree. -/
theorem gradeView_T (st : Protocol.Store V) : st.toHealing.gradeView.T = st.T := by
  unfold Protocol.HealingStore.gradeView
  rfl

omit [Fintype V] in
/-- The block timestamp map of the grade view read from a store's healing view is that store's block
    timestamp map. -/
theorem gradeView_timestamp_block (st : Protocol.Store V) :
    st.toHealing.gradeView.timestamp_block = st.timestamp_block := by
  unfold Protocol.HealingStore.gradeView
  rfl

omit [Fintype V] in
/-- The SG votes of round `r` in the grade view read from a store's healing view are the SG votes of
    the attestations in that store's SG pool of round `r`. -/
theorem gradeView_sg_votes (st : Protocol.Store V) (r : Round) :
    st.toHealing.gradeView.sg_votes r = (st.sg_pool r).image Protocol.sgVote := by
  unfold Protocol.HealingStore.gradeView
  rfl

omit [Fintype V] in
/-- The filtered tree of the grade view read from the healing store `hs` is
    `Protocol.get_filtered_block_tree hs.toFG`. -/
theorem gradeView_tree (hs : Protocol.HealingStore V) :
    hs.gradeView.tree = Protocol.get_filtered_block_tree hs.toFG := by
  unfold Protocol.HealingStore.gradeView
  rfl

omit [Fintype V] in
/-- The SG vote timestamp map of the grade view read from a store's healing view is that store's SG
    vote timestamp map. -/
theorem gradeView_timestamp_sg_vote (st : Protocol.Store V) :
    st.toHealing.gradeView.timestamp_sg_vote = st.timestamp_sg_vote := by
  unfold Protocol.HealingStore.gradeView
  rfl

end DecoupledConsensusModel.Sts
