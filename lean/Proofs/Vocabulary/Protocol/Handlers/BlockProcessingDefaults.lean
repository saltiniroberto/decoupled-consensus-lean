module
public import Proofs.Vocabulary.Protocol.Handlers.TickBridges
import Proofs.Vocabulary.Protocol.Handlers.Invariants2

@[expose] public section

/-!
# The checked block handler

Reductions of the checked block handler and of the named block derivation.
-/
namespace DecoupledConsensusModel.Proofs.BlockProcessingDefaults
open Protocol
variable {V : Type} [DecidableEq V] [Fintype V]


theorem derive_named_node (E : Env V) (cfg : HeightConfig) (p : NamedBlock V)
    (s : Slot) (root : BlockId) (votes support : List (GoldfishVote V))
    (rows : List (NamedAttestation V)) (proposer : V) :
    derive_named E cfg (.node p s root votes support rows proposer) =
      named_transition E cfg (derive_named E cfg p)
        (.node p s root votes support rows proposer) := rfl

private theorem raw_tree_cases (E : Env V) (st : Protocol.Store V) (B : Block V)
    (buildState : ChainState V → ChainState V) :
    (Protocol.on_block_using E st B buildState).T = st.T ∨
      (Protocol.on_block_using E st B buildState).T = insert B st.T := by
  simp only [Protocol.on_block_using]
  split_ifs <;> first
    | exact Or.inl rfl
    | exact Or.inr (by rw [Proofs.update_finality_T, Proofs.foldl_on_goldfish_vote_checked_T E])

theorem checked_tree_cases (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.Store V)
    (B : Block V) (buildState : ChainState V → ChainState V) :
    let out := Protocol.on_block_checked_using
      (fun current => Protocol.on_block_using E current B buildState) hc st B
    out.T = st.T ∨ out.T = insert B st.T := by
  dsimp only [Protocol.on_block_checked_using]
  split_ifs
  · exact raw_tree_cases E st B buildState
  · exact Or.inl rfl

private theorem raw_sg_votes (E : Env V) (st : Protocol.Store V) (B : Block V)
    (buildState : ChainState V → ChainState V) :
    (Protocol.on_block_using E st B buildState).sg_votes = st.sg_votes := by
  simp only [Protocol.on_block_using]
  split_ifs <;> first
    | rfl
    | (rw [Proofs.Optimistic.update_finality_sg_votes,
        Proofs.Optimistic.foldl_on_goldfish_vote_checked_sg_votes])

/-- The checked block handler leaves the SG votes unchanged. -/
theorem checked_sg_votes (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.Store V)
    (B : Block V) (buildState : ChainState V → ChainState V) :
    (Protocol.on_block_checked_using
      (fun current => Protocol.on_block_using E current B buildState) hc st B).sg_votes =
        st.sg_votes := by
  dsimp only [Protocol.on_block_checked_using]
  split_ifs
  · exact raw_sg_votes E st B buildState
  · rfl

/-- A block freshly inserted by the checked block handler gets the chain state that `buildState`
    builds from its parent's. -/
theorem checked_fresh_state (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.Store V)
    (B : Block V) (buildState : ChainState V → ChainState V)
    (hfresh : B ∉ st.T)
    (hmem : B ∈ (Protocol.on_block_checked_using
      (fun current => Protocol.on_block_using E current B buildState) hc st B).T) :
    (Protocol.on_block_checked_using
      (fun current => Protocol.on_block_using E current B buildState) hc st B).σ B =
        buildState (st.σ B.parent) := by
  dsimp only [Protocol.on_block_checked_using] at hmem ⊢
  split_ifs at hmem ⊢ with hvalid
  · simp only [Protocol.on_block_using] at hmem ⊢
    split_ifs at hmem ⊢ <;> first
      | exact False.elim (hfresh hmem)
      | (rw [update_finality_σ,
          (coreEq_foldl_on_goldfish_vote_checked E B.gf_votes _).σ_eq]
         simp)
  · exact False.elim (hfresh hmem)

/-- A named block other than genesis is derived by `named_transition` from its named parent. -/
theorem derive_named_of_not_genesis (E : Env V) (cfg : HeightConfig) (B : NamedBlock V)
    (hB : B ≠ .genesis) :
    derive_named E cfg B = named_transition E cfg (derive_named E cfg B.parent) B := by
  cases B with
  | genesis => exact False.elim (hB rfl)
  | node p s root votes support rows proposer => rfl

/-- The checked block handler leaves the store unchanged on a block it already holds. -/
theorem checked_existing (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.Store V)
    (B : Block V) (buildState : ChainState V → ChainState V) (hB : B ∈ st.T) :
    Protocol.on_block_checked_using
      (fun current => Protocol.on_block_using E current B buildState) hc st B = st := by
  simp [Protocol.on_block_checked_using, Protocol.on_block_using, hB]

private theorem checked_other_state (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.Store V) (B C : Block V) (buildState : ChainState V → ChainState V)
    (hne : C ≠ B) :
    (Protocol.on_block_checked_using
      (fun current => Protocol.on_block_using E current B buildState) hc st B).σ C = st.σ C := by
  dsimp only [Protocol.on_block_checked_using]
  split_ifs
  · simp only [Protocol.on_block_using]
    split_ifs <;> first
      | rfl
      | (rw [update_finality_σ,
          (coreEq_foldl_on_goldfish_vote_checked E B.gf_votes _).σ_eq]
         simp [hne])
  · rfl

/-- The checked block handler keeps the chain state of every block already held. -/
theorem checked_old_state (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.Store V)
    (B C : Block V) (buildState : ChainState V → ChainState V) (hC : C ∈ st.T) :
    (Protocol.on_block_checked_using
      (fun current => Protocol.on_block_using E current B buildState) hc st B).σ C = st.σ C := by
  by_cases hCB : C = B
  · subst C
    rw [checked_existing E hc st B buildState hC]
  · exact checked_other_state E hc st B C buildState hCB

#print axioms derive_named_node
#print axioms checked_tree_cases
#print axioms checked_sg_votes
#print axioms checked_fresh_state
#print axioms derive_named_of_not_genesis
#print axioms checked_existing
#print axioms checked_old_state
end DecoupledConsensusModel.Proofs.BlockProcessingDefaults

end
