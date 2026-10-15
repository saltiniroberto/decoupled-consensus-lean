module
public import Model.Vocabulary.Protocol.Handlers
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# Facts about `Protocol.on_goldfish_vote`: the rejecting branches

The two branches of the Goldfish-vote receipt that return the store unchanged.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.on_goldfish_vote

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- If `u`'s slot is less than the store's slot minus one or greater than the store's slot, or the
    store already holds `u` in the bucket of its slot, the Goldfish receipt of `u` returns the store
    it was given. -/
theorem on_goldfish_vote_of_rejected (st : Protocol.Store V) (u : GoldfishVote V)
    (h : u.slot < st.s - 1 ∨ st.s < u.slot ∨ u ∈ st.gf_votes u.slot) :
    Protocol.on_goldfish_vote st u = st := by
  unfold Protocol.on_goldfish_vote
  rw [if_pos h]

/-- If `u` passes the first test of the Goldfish receipt and the store already sees `u`'s signer
    equivocating in the pool of `u`'s slot, the receipt of `u` returns the store it was given. -/
theorem on_goldfish_vote_of_equivocates (st : Protocol.Store V) (u : GoldfishVote V)
    (h1 : ¬ (u.slot < st.s - 1 ∨ st.s < u.slot ∨ u ∈ st.gf_votes u.slot))
    (h2 : Protocol.equivocates (st.pool u.slot) u.val_index = true) :
    Protocol.on_goldfish_vote st u = st := by
  unfold Protocol.on_goldfish_vote
  rw [if_neg h1, if_pos h2]

end DecoupledConsensusModel.Sts
