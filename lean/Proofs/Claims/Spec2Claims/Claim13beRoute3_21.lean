import Proofs.Claims.RunAll
import Proofs.Vocabulary.Protocol.ChainState.FinalityComparison
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Tactic.Bound
import Proofs.Vocabulary.Protocol.ValidatorClient.Bridge
import Proofs.Claims.Spec2Claims.Claim13bModel_Slashable
import Proofs.Claims.Spec2Claims.Claim13bModel_conflictsWithFinality
import Proofs.Claims.Spec2Claims.Claim13bModel_e1Fields
import Proofs.Claims.Spec2Claims.Claim13bModel_e2Fields
import Proofs.Claims.Spec2Claims.Claim13bModel_author
import Proofs.Vocabulary.Protocol.ChainState.SlashableBoundBridge
import Proofs.Vocabulary.Protocol.ChainState.Main
import Mathlib.Tactic.Monotonicity.Lemmas
import Proofs.Claims.Spec2Claims.Claim13bModel_HasIntersectionWeight
import Proofs.Claims.Spec2Claims.Claim13bModel_compatible
import Proofs.Vocabulary.Execution.IdxDriverHelpers
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedBlock_attestations
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedAttestation_erase
import Proofs.Vocabulary.Protocol.Duties.Proposals.ProposalRows
import Proofs.Vocabulary.Protocol.Handlers.Pool
import Proofs.Vocabulary.Protocol.Duties.Proposals.Actions
import Proofs.Vocabulary.Protocol.ValidatorClient.BlockEmission
import Mathlib.Data.Rat.Floor
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedBlock_gf_votes
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedBlock_slot
import Proofs.Claims.Spec2Claims.Claim13bModel_Env_committee
import Proofs.Claims.Spec2Claims.Claim13bModel_propose_block_with_snd
import Proofs.Claims.Spec2Claims.Claim13bModel_Env_W
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedBlock_Preceq
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedBlock_parent
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedBlock_erase
import Proofs.Claims.Spec2Claims.Claim13bModel_chain_attestations

/-!
# Ancestors of named blocks and the attestations of their chains

A named ancestor of a block is the block itself or an ancestor of its parent, and every attestation
of a named block's erased chain comes from an attestation of one of its named ancestors.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- A named ancestor `X` of `B` is `B` itself or an ancestor of `B.parent`. -/
theorem namedPreceq_eq_or_parent {X B : NamedBlock V} (h : NamedBlock.Preceq X B) :
    X = B ∨ NamedBlock.Preceq X B.parent := by
  cases B with
  | genesis =>
    left
    exact namedPreceq_genesis_iff_l85.mp h
  | node p s root gf support rows proposer =>
    rw [namedBlock_parent_node]
    exact namedPreceq_node_iff_l85.mp h

omit [Fintype V] in
/-- Every attestation `a` of `chain_attestations B.erase` is the erasure of an attestation included
    in some named ancestor of `B`. -/
theorem named_mem_chain_attestations_of_erase {a : CombinedAttestation V} :
    ∀ B : NamedBlock V, a ∈ chain_attestations B.erase →
      ∃ X : NamedBlock V, NamedBlock.Preceq X B ∧
        ∃ row ∈ X.attestations, row.erase = a := by
  intro B
  induction B with
  | genesis =>
    intro h
    rw [erase_named_genesis, chain_attestations_genesis] at h
    simp at h
  | node p s root gf support rows proposer ih =>
    intro h
    rw [erase_named_node, chain_attestations_node] at h
    simp only [Finset.mem_union, List.mem_toFinset, List.mem_map] at h
    rcases h with ⟨row, hrow, hrowa⟩ | h
    · refine ⟨.node p s root gf support rows proposer, namedBlock_Preceq_self _, row, ?_, hrowa⟩
      rw [named_node_attestations]
      exact hrow
    · obtain ⟨X, hXp, row, hrow, hrowa⟩ := ih h
      exact ⟨X, namedPreceq_node_iff_l85.mpr (Or.inr hXp), row, hrow, hrowa⟩

end DecoupledConsensusModel.Sts
