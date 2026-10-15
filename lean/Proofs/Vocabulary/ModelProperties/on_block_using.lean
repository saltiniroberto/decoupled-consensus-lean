module
public import Model.Vocabulary.Protocol.Handlers

@[expose] public section

/-!
# Facts about `Protocol.on_block_using`

The shared block-processing body: one fact for its rejecting cases and one for the case that writes
the block.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

variable {V : Type} [DecidableEq V] [Fintype V]

/-- If `B` is rejected (its slot is after the store's, it is already in the tree, its parent is not
    in the tree, the finalized block is not its ancestor, its proposer is wrong, or its parent's
    slot is not before its own), the store is unchanged. -/
theorem on_block_using_of_rejected (E : Env V) (st : Protocol.Store V) (B : Block V)
    (buildState : Protocol.ChainState V → Protocol.ChainState V)
    (h : (st.s < B.slot ∨ B ∈ st.T ∨ B.parent ∉ st.T) ∨ (!Block.preceq st.F B) = true ∨
      B.proposer? ≠ some (E.proposer B.slot) ∨ ¬ (B.parent.slot < B.slot)) :
    Protocol.on_block_using E st B buildState = st := by
  unfold Protocol.on_block_using
  rcases h with h1 | h2 | h3 | h4
  · rw [if_pos h1]
  · by_cases h1 : st.s < B.slot ∨ B ∈ st.T ∨ B.parent ∉ st.T
    · rw [if_pos h1]
    · rw [if_neg h1, if_pos h2]
  · by_cases h1 : st.s < B.slot ∨ B ∈ st.T ∨ B.parent ∉ st.T
    · rw [if_pos h1]
    · by_cases h2 : (!Block.preceq st.F B) = true
      · rw [if_neg h1, if_pos h2]
      · rw [if_neg h1, if_neg h2, if_pos h3]
  · by_cases h1 : st.s < B.slot ∨ B ∈ st.T ∨ B.parent ∉ st.T
    · rw [if_pos h1]
    · by_cases h2 : (!Block.preceq st.F B) = true
      · rw [if_neg h1, if_pos h2]
      · by_cases h3 : B.proposer? ≠ some (E.proposer B.slot)
        · rw [if_neg h1, if_neg h2, if_pos h3]
        · rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4]

/-- If `B` is not rejected, the body stores `B` with the chain state `buildState` builds from its
    parent's, processes its carried Goldfish votes, and applies the finality update. -/
theorem on_block_using_of_accepted (E : Env V) (st : Protocol.Store V) (B : Block V)
    (buildState : Protocol.ChainState V → Protocol.ChainState V)
    (h1 : ¬ (st.s < B.slot ∨ B ∈ st.T ∨ B.parent ∉ st.T))
    (h2 : ¬ (!Block.preceq st.F B) = true)
    (h3 : ¬ B.proposer? ≠ some (E.proposer B.slot))
    (h4 : ¬ ¬ (B.parent.slot < B.slot)) :
    Protocol.on_block_using E st B buildState =
      Protocol.update_finality
        (B.gf_votes.foldl (Protocol.on_goldfish_vote_checked E)
          { st with
            σ := fun C => if C = B then buildState (st.σ B.parent) else st.σ C
            T := insert B st.T
            timestamp_block := fun C =>
              if C = B then some (st.t : Stamp) else st.timestamp_block C })
        ((B.gf_votes.foldl (Protocol.on_goldfish_vote_checked E)
          { st with
            σ := fun C => if C = B then buildState (st.σ B.parent) else st.σ C
            T := insert B st.T
            timestamp_block := fun C =>
              if C = B then some (st.t : Stamp) else st.timestamp_block C }).σ B) := by
  unfold Protocol.on_block_using
  rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4]

end DecoupledConsensusModel.Proofs.ModelProperties

end
