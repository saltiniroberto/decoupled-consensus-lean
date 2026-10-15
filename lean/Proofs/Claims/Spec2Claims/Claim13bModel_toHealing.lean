module
public import Model.Vocabulary.Protocol.Store
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# Facts about `Protocol.Store.toHealing`

The adapter `Protocol.Store.toHealing` copies a store's fields into the healing store the fork
choice reads; these lemmas state each copied field.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.GoldfishStore.pool
  DecoupledConsensusModel.Protocol.Store.pool DecoupledConsensusModel.Protocol.Store.sg_pool
  DecoupledConsensusModel.Protocol.Store.toHealing

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- The Goldfish store a store's healing view projects to has the store's tree. -/
theorem toHealing_gs_T (st : Protocol.Store V) :
    st.toHealing.toFG.toSG.toGoldfishStore.T = st.T := rfl

omit [Fintype V] in
/-- The Goldfish store a store's healing view projects to has the store's slot. -/
theorem toHealing_gs_s (st : Protocol.Store V) :
    st.toHealing.toFG.toSG.toGoldfishStore.s = st.s := rfl

omit [Fintype V] in
/-- The Goldfish store a store's healing view projects to has the store's Goldfish vote buckets. -/
theorem toHealing_gs_gf_votes (st : Protocol.Store V) (s : Slot) :
    st.toHealing.toFG.toSG.toGoldfishStore.gf_votes s = st.gf_votes s := rfl

omit [Fintype V] in
/-- The Goldfish store a store's healing view projects to pools the store's votes. -/
theorem toHealing_gs_pool (st : Protocol.Store V) (s : Slot) :
    st.toHealing.toFG.toSG.toGoldfishStore.pool s = st.pool s := rfl

omit [Fintype V] in
/-- The Goldfish store a store's healing view projects to has the store's vote stamps. -/
theorem toHealing_gs_timestamp_vote (st : Protocol.Store V) :
    st.toHealing.toFG.toSG.toGoldfishStore.timestamp_vote = st.timestamp_vote := rfl

omit [Fintype V] in
/-- The Goldfish store a store's healing view projects to has the store's block stamps. -/
theorem toHealing_gs_timestamp_block (st : Protocol.Store V) :
    st.toHealing.toFG.toSG.toGoldfishStore.timestamp_block = st.timestamp_block := rfl

omit [Fintype V] in
/-- The finalized block of `st.toHealing` is the finalized block of `st`. -/
theorem toHealing_F (st : Protocol.Store V) : st.toHealing.F = st.F := rfl

omit [Fintype V] in
/-- The justified block of `st.toHealing` is the justified block of `st`. -/
theorem toHealing_J (st : Protocol.Store V) : st.toHealing.J = st.J := rfl

omit [Fintype V] in
/-- The highest height `h_max` of `st.toHealing` is that of `st`. -/
theorem toHealing_h_max (st : Protocol.Store V) : st.toHealing.h_max = st.h_max := rfl

omit [Fintype V] in
/-- The chain-state map `σ` of `st.toHealing` is that of `st`. -/
theorem toHealing_σ (st : Protocol.Store V) : st.toHealing.σ = st.σ := rfl

omit [Fintype V] in
/-- The justified height `h_j` of `st.toHealing` is that of `st`. -/
theorem toHealing_h_j (st : Protocol.Store V) : st.toHealing.h_j = st.h_j := rfl

omit [Fintype V] in
/-- The SG votes of round `r` in `st.toHealing` are the SG votes `Protocol.sgVote` of the
    attestations in `st`'s SG pool of round `r`. -/
theorem toHealing_sg_votes (st : Protocol.Store V) (r : Round) :
    st.toHealing.sg_votes r = (st.sg_pool r).image Protocol.sgVote := rfl

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

end DecoupledConsensusModel.Sts
