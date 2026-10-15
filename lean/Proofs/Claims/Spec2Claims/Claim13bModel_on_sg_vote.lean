module

public import Model.Vocabulary.Protocol.Handlers
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# Facts about `Protocol.on_sg_vote`

Lemmas that unfold the store update an SG vote makes. It writes only the SG-vote pool `sg_votes` and
its stamps `timestamp_sg_vote`.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.Store.sg_pool
  DecoupledConsensusModel.Protocol.on_sg_vote

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- The store `on_sg_vote` returns has the finalized block, the justified block, the justified
    height, the largest height and the block tree of the store it was given. -/
theorem on_sg_vote_tree_fields (hc : Protocol.HealConfig) (st : Protocol.Store V)
    (a : CombinedAttestation V) :
    (Protocol.on_sg_vote hc st a).F = st.F ∧ (Protocol.on_sg_vote hc st a).J = st.J ∧
      (Protocol.on_sg_vote hc st a).h_j = st.h_j ∧
      (Protocol.on_sg_vote hc st a).h_max = st.h_max ∧
      (Protocol.on_sg_vote hc st a).T = st.T := by
  unfold Protocol.on_sg_vote
  split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]


end DecoupledConsensusModel.Sts

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- If the attestation `a` is of a round at least the store's round minus `η_SG` and at most the
    store's round, its confirmed root is not yet among the roots the store holds for `a`'s validator
    and round, and the store does not already hold two such roots, then after `on_sg_vote` the
    store's pool of `a`'s round holds `a`. -/
theorem mem_on_sg_vote_sg_pool_of_not (hc : Protocol.HealConfig) (st : Protocol.Store V)
    (a : CombinedAttestation V)
    (h : ¬ (a.round < hc.round_of st.s - hc.η_SG ∨ hc.round_of st.s < a.round ∨
      a.confirmed ∈ Protocol.round_votes st a ∨ (Protocol.round_votes st a).card = 2)) :
    a ∈ (Protocol.on_sg_vote hc st a).sg_pool a.round := by
  unfold Protocol.on_sg_vote
  rw [if_neg h]
  simp [Protocol.Store.sg_pool]

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- If the combined attestation `a` is of a round at least the store's round minus `η_SG` and at
    most the store's round, its head is not already among the store's heads for its sender and
    round, and the store does not already hold two heads for them, then the store `on_sg_vote`
    returns stamps `a`'s SG vote with the clock `st.t`. -/
theorem on_sg_vote_timestamp_of_admitted (hc : Protocol.HealConfig) (st : Protocol.Store V)
    (a : CombinedAttestation V)
    (h : ¬ (a.round < hc.round_of st.s - hc.η_SG ∨ hc.round_of st.s < a.round ∨
      a.confirmed ∈ Protocol.round_votes st a ∨ (Protocol.round_votes st a).card = 2)) :
    (Protocol.on_sg_vote hc st a).timestamp_sg_vote (Protocol.sgVote a) =
      some (st.t : Stamp) := by
  unfold Protocol.on_sg_vote
  rw [if_neg h]
  simp

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]


end DecoupledConsensusModel.Sts

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- `Protocol.on_sg_vote` leaves the store's `latest_stable` and `latest_confirmed` unchanged. -/
theorem on_sg_vote_latest_records (hc : Protocol.HealConfig) (st : Protocol.Store V)
    (a : CombinedAttestation V) :
    (Protocol.on_sg_vote hc st a).latest_stable = st.latest_stable ∧
      (Protocol.on_sg_vote hc st a).latest_confirmed = st.latest_confirmed := by
  simp only [Protocol.on_sg_vote]
  split_ifs <;> exact ⟨rfl, rfl⟩

end DecoupledConsensusModel.Sts

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V]

/-- When `on_sg_vote`'s admission test rejects `a`, the store it returns is the store it was given. -/
theorem on_sg_vote_of_rejected (hc : Protocol.HealConfig) (st : Protocol.Store V)
    (a : CombinedAttestation V)
    (h : a.round < hc.round_of st.s - hc.η_SG ∨ hc.round_of st.s < a.round ∨
      a.confirmed ∈ Protocol.round_votes st a ∨ (Protocol.round_votes st a).card = 2) :
    Protocol.on_sg_vote hc st a = st := by
  unfold Protocol.on_sg_vote
  exact if_pos h

/-- When the admission test accepts `a`, the SG-vote lists of the store `on_sg_vote` returns are
    those of `st` with `a` appended to the list of `a`'s round. -/
theorem on_sg_vote_sg_votes_of_admitted (hc : Protocol.HealConfig) (st : Protocol.Store V)
    (a : CombinedAttestation V)
    (h : ¬ (a.round < hc.round_of st.s - hc.η_SG ∨ hc.round_of st.s < a.round ∨
      a.confirmed ∈ Protocol.round_votes st a ∨ (Protocol.round_votes st a).card = 2)) :
    (Protocol.on_sg_vote hc st a).sg_votes =
      fun r => if r = a.round then st.sg_votes r ++ [a] else st.sg_votes r := by
  unfold Protocol.on_sg_vote
  rw [if_neg h]

/-- The attestation handler keeps the store's slot. -/
theorem on_sg_vote_s' (hc : HealConfig) (c : Store V) (b : CombinedAttestation V) :
    (on_sg_vote hc c b).s = c.s := by
  unfold on_sg_vote
  split <;> rfl

end DecoupledConsensusModel.Sts

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- The SG-vote receipt leaves the store's `live_confirmed` unchanged. -/
theorem on_sg_vote_live_confirmed (hc : Protocol.HealConfig) (st : Protocol.Store V)
    (a : CombinedAttestation V) :
    (Protocol.on_sg_vote hc st a).live_confirmed = st.live_confirmed := by
  simp only [Protocol.on_sg_vote]
  split_ifs <;> rfl

end DecoupledConsensusModel.Sts
