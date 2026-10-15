module
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# Facts about `Protocol.on_goldfish_vote`

Lemmas that unfold the Goldfish-vote handler on the core store.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.on_goldfish_vote DecoupledConsensusModel.Protocol.Store.pool

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- The Goldfish handler leaves the erased tree alone. -/
theorem on_goldfish_vote_T (st : Store V) (u : GoldfishVote V) :
    (on_goldfish_vote st u).T = st.T := by
  simp only [on_goldfish_vote]; split; · rfl
  split <;> rfl

omit [Fintype V] in
/-- The Goldfish handler leaves the attestation lists alone. -/
theorem on_goldfish_vote_sg_votes (st : Store V) (u : GoldfishVote V) :
    (on_goldfish_vote st u).sg_votes = st.sg_votes := by
  simp only [on_goldfish_vote]; split; · rfl
  split <;> rfl

omit [Fintype V] in
/-- The Goldfish handler only adds to the slot vote lists. -/
theorem on_goldfish_vote_gf_votes_subset (st : Store V) (u : GoldfishVote V) (k : Slot) :
    st.gf_votes k ⊆ (on_goldfish_vote st u).gf_votes k := by
  simp only [on_goldfish_vote]
  split
  · exact fun _ h => h
  split
  · exact fun _ h => h
  · intro y hy
    by_cases hk : k = u.slot
    · simp only [hk]
      exact List.mem_append_left _ (by rw [← hk]; exact hy)
    · simpa [hk] using hy

omit [Fintype V] in
/-- The Goldfish handler either returns the store, or the vote ends up in its slot's pool. -/
theorem on_goldfish_vote_noop_or_mem (st : Store V) (u : GoldfishVote V) :
    on_goldfish_vote st u = st ∨ u ∈ (on_goldfish_vote st u).pool u.slot := by
  simp only [on_goldfish_vote]
  split
  · exact Or.inl rfl
  split
  · exact Or.inl rfl
  · refine Or.inr ?_
    simp only [Store.pool, List.mem_toFinset]
    exact List.mem_append_right _ (List.mem_singleton_self _)

omit [Fintype V] in
/-- The Goldfish handler adds only the vote it is handed. -/
theorem mem_gf_votes_on_goldfish_vote (st : Store V) (u : GoldfishVote V) (k : Slot)
    {y : GoldfishVote V} (h : y ∈ (on_goldfish_vote st u).gf_votes k) :
    y ∈ st.gf_votes k ∨ y = u := by
  simp only [on_goldfish_vote] at h
  split at h
  · exact Or.inl h
  · split at h
    · exact Or.inl h
    · have h' : y ∈ (if k = u.slot then st.gf_votes k ++ [u] else st.gf_votes k) := h
      by_cases hk : k = u.slot
      · rw [if_pos hk] at h'
        rcases List.mem_append.1 h' with hy | hy
        · exact Or.inl hy
        · exact Or.inr (List.mem_singleton.1 hy)
      · rw [if_neg hk] at h'
        exact Or.inl h'

end DecoupledConsensusModel.Sts
