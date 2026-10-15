import Proofs.Vocabulary.Protocol.Grades.ProposalParent
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.Records
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Records
import Model.Record.Wiring

/-!
# The head walk and the anchor stay in the tree

The head the grade contract walks to, and the anchor, are blocks of the store's tree, stated over a
model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedProposalParent

/-- For every outcome `G` of the contract's grade read at the round of `st`'s slot, if `G`'s anchor
    is in `st`'s tree, then every outcome `X` of the head
    `M.get_head_with gc E hc st votes support k` is in `st`'s tree. -/
theorem Vocabulary.Proofs.NamedProposalParent.get_head_with_mem (facts : Record.Facts M) (gc : M.Contract) (E : Env V)
    (hc : Protocol.HealConfig) (st : M.HS)
    (votes support : Finset (GoldfishVote V)) (k : Slot) :
    ∀ G, gc.read E hc st ((M.round_of hc st.s)) ⇢ G → G.anchor ∈ st.T →
    ∀ X, M.get_head_with gc E hc st votes support k ⇢ X → X ∈ st.T :=
  facts.fc.NamedProposalParent_get_head_with_mem gc E hc st votes support k

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedProposalParent

/-- If the FG root of `st` is in `st`'s tree, then every outcome `a` of the anchor
    `M.anchor E hc st r g1` is in `st`'s tree. -/
theorem Vocabulary.Proofs.NamedProposalParent.frame_anchor_mem (facts : Record.Facts M) (E : Env V) (hc : Protocol.HealConfig)
    (st : M.HS) (r : Round) (g1 : Option (Option (Block V)))
    (hroot : M.get_fg_root st.toFG ∈ st.T) :
    ∀ a : Block V, M.anchor E hc st r g1 ⇢ a → a ∈ st.T := by
  intro a ha
  rcases facts.gr.anchor_cases E hc st r g1 a ha with h | ⟨root, B, -, hp, h⟩
  · rw [h]
    exact hroot
  · rw [h]
    exact facts.fc.get_filtered_block_tree_subset st.toFG
      (facts.gr.activePrefix_mem _ root B hp)

end

end DecoupledConsensusModel.Sts.Restated
