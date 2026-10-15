module
public import Proofs.Claims.ModelIrreducible
public import Proofs.Claims.Spec2Claims.Claim13bModel_on_goldfish_vote

@[expose] public section

/-!
# Facts about `Protocol.on_goldfish_vote_checked`

Lemmas that unfold the committee-checked Goldfish-vote handler and its fold over the Goldfish votes
a block includes.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.on_goldfish_vote_checked DecoupledConsensusModel.Protocol.on_goldfish_vote

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The committee-checked Goldfish handler leaves the erased tree alone. -/
theorem on_goldfish_vote_checked_T (E : Env V) (st : Store V) (u : GoldfishVote V) :
    (on_goldfish_vote_checked E st u).T = st.T := by
  simp only [on_goldfish_vote_checked]; split
  · rfl
  · exact on_goldfish_vote_T st u

/-- The committee-checked Goldfish handler leaves the attestation lists alone. -/
theorem on_goldfish_vote_checked_sg_votes (E : Env V) (st : Store V) (u : GoldfishVote V) :
    (on_goldfish_vote_checked E st u).sg_votes = st.sg_votes := by
  simp only [on_goldfish_vote_checked]; split
  · rfl
  · exact on_goldfish_vote_sg_votes st u

/-- The committee-checked Goldfish handler only adds to the slot vote lists. -/
theorem on_goldfish_vote_checked_gf_votes_subset (E : Env V) (st : Store V)
    (u : GoldfishVote V) (k : Slot) :
    st.gf_votes k ⊆ (on_goldfish_vote_checked E st u).gf_votes k := by
  simp only [on_goldfish_vote_checked]; split
  · exact fun _ h => h
  · exact on_goldfish_vote_gf_votes_subset st u k

/-- The committee-checked Goldfish handler either returns the store, or the vote ends up in its
    slot's pool. -/
theorem on_goldfish_vote_checked_noop_or_mem (E : Env V) (st : Store V)
    (u : GoldfishVote V) :
    on_goldfish_vote_checked E st u = st ∨
      u ∈ (on_goldfish_vote_checked E st u).pool u.slot := by
  simp only [on_goldfish_vote_checked]; split
  · exact Or.inl rfl
  · exact on_goldfish_vote_noop_or_mem st u

/-- Folding the committee-checked Goldfish handler over a list of votes leaves the erased tree
    alone. -/
theorem foldl_on_goldfish_vote_checked_T (E : Env V) :
    ∀ (us : List (GoldfishVote V)) (st : Store V),
      (us.foldl (on_goldfish_vote_checked E) st).T = st.T
  | [], _ => rfl
  | u :: us, st => by
      rw [List.foldl_cons, foldl_on_goldfish_vote_checked_T E us,
        on_goldfish_vote_checked_T]

/-- Folding the committee-checked Goldfish handler over a list of votes leaves the attestation lists
    alone. -/
theorem foldl_on_goldfish_vote_checked_sg_votes (E : Env V) :
    ∀ (us : List (GoldfishVote V)) (st : Store V),
      (us.foldl (on_goldfish_vote_checked E) st).sg_votes = st.sg_votes
  | [], _ => rfl
  | u :: us, st => by
      rw [List.foldl_cons, foldl_on_goldfish_vote_checked_sg_votes E us,
        on_goldfish_vote_checked_sg_votes]

/-- Folding the committee-checked Goldfish handler over a list of votes only adds to the slot vote
    lists. -/
theorem foldl_on_goldfish_vote_checked_gf_votes_subset (E : Env V) (k : Slot) :
    ∀ (us : List (GoldfishVote V)) (st : Store V),
      st.gf_votes k ⊆ (us.foldl (on_goldfish_vote_checked E) st).gf_votes k
  | [], _ => fun _ h => h
  | u :: us, st => by
      rw [List.foldl_cons]
      exact fun y hy =>
        foldl_on_goldfish_vote_checked_gf_votes_subset E k us _
          (on_goldfish_vote_checked_gf_votes_subset E st u k hy)

/-- The committee-checked Goldfish handler adds only the vote it is handed. -/
theorem mem_gf_votes_on_goldfish_vote_checked (E : Env V) (st : Store V) (u : GoldfishVote V)
    (k : Slot) {y : GoldfishVote V} (h : y ∈ (on_goldfish_vote_checked E st u).gf_votes k) :
    y ∈ st.gf_votes k ∨ y = u := by
  simp only [on_goldfish_vote_checked] at h
  split at h
  · exact Or.inl h
  · exact mem_gf_votes_on_goldfish_vote st u k h

/-- Folding the committee-checked Goldfish handler over a list of votes adds only votes of that
    list. -/
theorem mem_gf_votes_foldl_on_goldfish_vote_checked (E : Env V) (k : Slot) :
    ∀ (us : List (GoldfishVote V)) (st : Store V) {y : GoldfishVote V},
      y ∈ (us.foldl (on_goldfish_vote_checked E) st).gf_votes k →
        y ∈ st.gf_votes k ∨ y ∈ us
  | [], _, _, h => Or.inl h
  | u :: us, st, y, h => by
      rw [List.foldl_cons] at h
      rcases mem_gf_votes_foldl_on_goldfish_vote_checked E k us _ h with h' | h'
      · rcases mem_gf_votes_on_goldfish_vote_checked E st u k h' with h'' | h''
        · exact Or.inl h''
        · exact Or.inr (by rw [h'']; exact List.mem_cons_self)
      · exact Or.inr (List.mem_cons_of_mem _ h')

/-- Processing a Goldfish vote the store already holds for its slot returns the core store
    unchanged. -/
theorem on_goldfish_vote_checked_of_mem (E : Env V) (st : Protocol.Store V)
    (u : GoldfishVote V) (h : u ∈ st.gf_votes u.slot) :
    Protocol.on_goldfish_vote_checked E st u = st := by
  unfold Protocol.on_goldfish_vote_checked
  split_ifs with hcm
  · unfold Protocol.on_goldfish_vote
    exact if_pos (Or.inr (Or.inr h))
  · rfl

end DecoupledConsensusModel.Sts
