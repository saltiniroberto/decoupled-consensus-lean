module
public import Proofs.Claims.ModelIrreducible
public import Proofs.Claims.Spec2Claims.Claim13bModel_on_sg_vote
public import Proofs.Claims.Spec2Claims.Claim13bModel_round_votes

@[expose] public section

/-!
# Facts about `Protocol.on_sg_vote`, read with `Protocol.round_votes`

Lemmas that unfold the SG-vote handler: when it returns the store unchanged, and that otherwise the
attestation ends up in its round's pool.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.on_sg_vote

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- An attestation already in its round's pool leaves the store unchanged. -/
theorem on_sg_vote_eq_of_mem (hc : Protocol.HealConfig) (st : Store V)
    (a : CombinedAttestation V) (ha : a ∈ st.sg_pool a.round) :
    on_sg_vote hc st a = st := by
  have hrv : a.confirmed ∈ round_votes st a := by
    simp only [round_votes, Finset.mem_image, Finset.mem_filter]
    exact ⟨a, ⟨ha, rfl⟩, rfl⟩
  rw [on_sg_vote, if_pos (Or.inr (Or.inr (Or.inl hrv)))]

omit [Fintype V] in
/-- The SG handler either returns the store, or the attestation ends up in its round's pool. -/
theorem on_sg_vote_noop_or_mem (hc : Protocol.HealConfig) (st : Store V)
    (a : CombinedAttestation V) :
    on_sg_vote hc st a = st ∨ a ∈ (on_sg_vote hc st a).sg_pool a.round := by
  simp only [on_sg_vote]
  split
  · exact Or.inl rfl
  · refine Or.inr ?_
    simp only [Store.sg_pool, List.mem_toFinset]
    exact List.mem_append_right _ (List.mem_singleton_self _)

omit [Fintype V] in
/-- The SG handler leaves the slot vote lists alone. -/
theorem on_sg_vote_gf_votes (hc : Protocol.HealConfig) (st : Store V)
    (a : CombinedAttestation V) : (on_sg_vote hc st a).gf_votes = st.gf_votes := by
  simp only [on_sg_vote]; split <;> rfl

omit [Fintype V] in
/-- If the combined attestation's confirmed head is already one of its validator's confirmed heads
    for its round, the SG-vote handler returns the store unchanged. -/
theorem on_sg_vote_of_mem_round_votes (hc : Protocol.HealConfig) (st : Protocol.Store V)
    (a : CombinedAttestation V) (h : a.confirmed ∈ Protocol.round_votes st a) :
    Protocol.on_sg_vote hc st a = st := by
  unfold Protocol.on_sg_vote
  exact if_pos (Or.inr (Or.inr (Or.inl h)))

end DecoupledConsensusModel.Sts
