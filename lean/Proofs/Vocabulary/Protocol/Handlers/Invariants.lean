module
public import Proofs.Vocabulary.Objects.Ancestry
public import Proofs.Vocabulary.Internal.Invariants

@[expose] public section

/-!
# Single-handler store invariants

The vote handlers and `update_finality` leave `Σ.F` unchanged or advance it and write no block, and
`update_finality` keeps `Σ.F` in the tree.
-/

namespace DecoupledConsensusModel
namespace Proofs

open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Internal

variable {V : Type} [DecidableEq V] [Fintype V]


/-! ## Monotonicity of `Σ.F` -/

omit [Fintype V] in
/-- `on_goldfish_vote` leaves `Σ.F` unchanged. -/
theorem on_goldfish_vote_F (st : Protocol.Store V) (vote : GoldfishVote V) :
    (Protocol.on_goldfish_vote st vote).F = st.F := by
  unfold Protocol.on_goldfish_vote
  split_ifs <;> rfl

/-- `on_goldfish_vote_checked` leaves `Σ.F` unchanged. -/
theorem on_goldfish_vote_checked_F (E : Env V) (st : Protocol.Store V)
    (vote : GoldfishVote V) :
    (Protocol.on_goldfish_vote_checked E st vote).F = st.F := by
  simp only [Protocol.on_goldfish_vote_checked]
  split_ifs
  · exact on_goldfish_vote_F st vote
  · rfl


/-- A fold of `on_goldfish_vote_checked` leaves `Σ.F` unchanged. -/
theorem foldl_on_goldfish_vote_checked_F (E : Env V)
    (l : List (GoldfishVote V)) (st : Protocol.Store V) :
    (l.foldl (Protocol.on_goldfish_vote_checked E) st).F = st.F := by
  induction l generalizing st with
  | nil => rfl
  | cons v vs ih =>
      rw [List.foldl_cons, ih, on_goldfish_vote_checked_F]

omit [Fintype V] in
/-- `on_sg_vote` leaves `Σ.F` unchanged. -/
theorem on_sg_vote_F (hc : HealConfig) (st : Protocol.Store V)
    (a : CombinedAttestation V) : (Protocol.on_sg_vote hc st a).F = st.F := by
  simp only [Protocol.on_sg_vote]
  split_ifs <;> rfl


omit [Fintype V] in
/-- `update_finality` only advances `Σ.F`. -/
theorem update_finality_F (st : Protocol.Store V) (σ : ChainState V) :
    Block.preceq st.F (Protocol.update_finality st σ).F = true := by
  simp only [Protocol.update_finality]
  split_ifs <;> rename_i h <;>
    first
      | exact Block.preceq_self _
      | exact Block.preceq_of_prec (by
          rw [Bool.and_eq_true, Bool.and_eq_true] at h
          exact h.1.1)

omit [Fintype V] in
/-- `update_finality` leaves the tree unchanged. -/
theorem update_finality_T (st : Protocol.Store V) (σ : ChainState V) :
    (Protocol.update_finality st σ).T = st.T := by
  simp only [Protocol.update_finality]
  split_ifs <;> rfl

omit [Fintype V] in
/-- `on_goldfish_vote` leaves the tree unchanged. -/
theorem on_goldfish_vote_T (st : Protocol.Store V) (vote : GoldfishVote V) :
    (Protocol.on_goldfish_vote st vote).T = st.T := by
  unfold Protocol.on_goldfish_vote
  split_ifs <;> rfl

/-- `on_goldfish_vote_checked` leaves the tree unchanged. -/
theorem on_goldfish_vote_checked_T (E : Env V) (st : Protocol.Store V)
    (vote : GoldfishVote V) :
    (Protocol.on_goldfish_vote_checked E st vote).T = st.T := by
  simp only [Protocol.on_goldfish_vote_checked]
  split_ifs
  · exact on_goldfish_vote_T st vote
  · rfl


/-- A fold of `on_goldfish_vote_checked` leaves the tree unchanged. -/
theorem foldl_on_goldfish_vote_checked_T (E : Env V)
    (l : List (GoldfishVote V)) (st : Protocol.Store V) :
    (l.foldl (Protocol.on_goldfish_vote_checked E) st).T = st.T := by
  induction l generalizing st with
  | nil => rfl
  | cons v vs ih =>
      rw [List.foldl_cons, ih, on_goldfish_vote_checked_T]

omit [Fintype V] in
/-- `ParentClosed st` holds when genesis is in `st.T` and every block of `st.T` other than genesis
    has its parent in `st.T`. -/
theorem parentClosed_iff (st : Protocol.Store V) :
    ParentClosed st ↔
      (Block.genesis ∈ st.T ∧ ∀ B ∈ st.T, B.parent? = none ∨ B.parent ∈ st.T) :=
  Iff.rfl


/-! ## The finalized block is in the tree -/

omit [Fintype V] in
/-- `on_sg_vote` leaves the tree unchanged. -/
theorem on_sg_vote_T (hc : HealConfig) (st : Protocol.Store V)
    (a : CombinedAttestation V) : (Protocol.on_sg_vote hc st a).T = st.T := by
  simp only [Protocol.on_sg_vote]
  split_ifs <;> rfl


omit [Fintype V] in
/-- `update_finality` keeps `Σ.F` in the tree. -/
theorem finalizedInTree_update_finality (st : Protocol.Store V) (σ : ChainState V)
    (h : st.F ∈ st.T) :
    (Protocol.update_finality st σ).F ∈ (Protocol.update_finality st σ).T := by
  rw [Proofs.update_finality_T]
  simp only [Protocol.update_finality]
  split_ifs <;> rename_i hg <;>
    first
      | exact h
      | (simp only [Bool.and_eq_true, decide_eq_true_eq, Protocol.viable_tree,
            Protocol.finalized_descendants, Finset.mem_filter] at hg
         exact hg.2.1.1)

end Proofs
end DecoupledConsensusModel

end
