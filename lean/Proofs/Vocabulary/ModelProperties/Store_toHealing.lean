module
public import Model.Vocabulary.Protocol.Store

@[expose] public section

/-!
# Facts about `Protocol.Store.toHealing`

The healing view of a store, read field by field.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

variable {V : Type} [DecidableEq V]

/-- The healing view of a store has the store's finalized block. -/
theorem toHealing_F (st : Protocol.Store V) : st.toHealing.F = st.F := rfl

/-- The healing view of a store has the store's slot. -/
theorem toHealing_s (st : Protocol.Store V) : st.toHealing.s = st.s := rfl

/-- The healing view of a store has the store's block tree. -/
theorem toHealing_T (st : Protocol.Store V) : st.toHealing.T = st.T := rfl

/-- The healing view of a store has the store's live confirmed block. -/
theorem toHealing_live_confirmed (st : Protocol.Store V) :
    st.toHealing.live_confirmed = st.live_confirmed := rfl

/-- The healing view of a store has the store's justified block. -/
theorem toHealing_J (st : Protocol.Store V) : st.toHealing.J = st.J := rfl

/-- The healing view of a store has the store's chain-state map. -/
theorem toHealing_σ (st : Protocol.Store V) : st.toHealing.σ = st.σ := rfl

/-- The healing view of a store has the store's `h_max`. -/
theorem toHealing_h_max (st : Protocol.Store V) : st.toHealing.h_max = st.h_max := rfl

/-- The SG votes of round `r` in the healing view of `st` are the images under `Protocol.sgVote` of
    `st`'s SG pool of round `r`. -/
theorem toHealing_sg_votes (st : Protocol.Store V) (r : Round) :
    st.toHealing.sg_votes r = (st.sg_pool r).image Protocol.sgVote := rfl

end DecoupledConsensusModel.Proofs.ModelProperties

end
