module
public import Proofs.Vocabulary.Internal.Definitions.NamedLifecycle
public import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.Admissible
import Proofs.Vocabulary.Execution.Acceptance
import Proofs.Vocabulary.Protocol.ChainState.ProposalBridge
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.ProposalSnapshotBridge
import Proofs.Vocabulary.Protocol.Grades.Grades
import Proofs.Vocabulary.Protocol.Grades.HealthyHeadReady
import Proofs.Vocabulary.Protocol.Handlers.AcceptanceTiming
import Proofs.Vocabulary.Protocol.Handlers.AdoptionConstructor
import Proofs.Vocabulary.Protocol.Handlers.HMaxCore
import Proofs.Vocabulary.Protocol.Handlers.Proposer
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.Data.Rat.Floor
public import Proofs.Vocabulary.Internal.Internal.GradeReads

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Voter-filtered tree inclusion

The voter-filtered block tree of a store is contained in its filtered block tree.
-/


namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Internal.PhaseGrades
open Internal.NamedOutageEntry
open Internal.NamedRecoveryRead
open Protocol
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]


private theorem pinScoreEq_voterCandidateTree_subset_filtered
    (E : Env V) (st : Protocol.Store V) :
    Protocol.voter_filtered_block_tree E st st.s ⊆
      Protocol.get_filtered_block_tree st.toHealing.toFG := by
  intro B hB
  have hB' : B ∈ Proofs.Optimistic.voter_candidate_tree E st.toHealing := by
    simpa only [Proofs.Optimistic.voter_candidate_tree_eq_protocol_voter_filtered_block_tree]
      using hB
  simp only [Proofs.Optimistic.voter_candidate_tree,
    Protocol.get_filtered_block_tree,
    Protocol.get_filtered_block_tree_from, Protocol.viable_tree,
    Protocol.finalized_descendants, Protocol.viable,
    Finset.mem_filter, decide_eq_true_eq] at hB' ⊢
  obtain ⟨⟨⟨hBprocessed, hFB⟩, W, hWprocessed, hBW, hheight⟩,
    hroot⟩ := hB'
  have hBT : B ∈ st.T := by
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
      at hBprocessed
    exact hBprocessed.1
  have hWT : W ∈ st.T := by
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
      at hWprocessed
    exact hWprocessed.1
  exact ⟨⟨⟨hBT, hFB⟩, W, hWT, hBW, hheight⟩, hroot⟩


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
