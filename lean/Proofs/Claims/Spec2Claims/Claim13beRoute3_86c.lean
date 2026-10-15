import Proofs.Claims.Spec2Claims.Claim13beRoute3_71
import Proofs.Claims.Spec2Claims.Claim13bModel_confirmationReadFrom
import Proofs.Claims.Spec2Claims.Claim13bSGCompatible
import Proofs.Claims.Spec2Claims.Claim13bModel_setClock_inclG2b
import Proofs.Claims.Spec2Claims.Claim13bModel_voter_processed_block_tree
import Proofs.Claims.Spec2Claims.Claim13bModel_voter_filtered_block_tree
import Proofs.Claims.Spec2Claims.Claim13bModel_setClock
import Proofs.Claims.Spec2Claims.Claim13bModel_setClock_incl
import Proofs.Claims.Spec2Claims.Claim13bModel_setClock_inclG2
import Proofs.Claims.Spec2Claims.Claim13bModel_toHealing
import Proofs.Claims.Spec2Claims.Claim13bModel_actionStoreAt
import Proofs.Claims.Spec2Claims.Claim13bModel_get_filtered_block_tree_inclG5
import Proofs.Claims.Spec2Claims.Claim13bModel_compatible
import Proofs.Claims.Spec2Claims.Claim13bModel_Preceq
import Proofs.Vocabulary.ModelProperties.Block_Preceq
import Proofs.Claims.Spec2Claims.Claim13bModel_opening_slot

/-!
# Height pairs and chain attestations

A height pair matching an entry at height `H` has height `H`, and a row of a block is among the
chain attestations of each of its descendants.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

variable {V : Type} [DecidableEq V] [Fintype V]

section FGSafetySourceNamed

omit [DecidableEq V] [Fintype V] in
/-- If `a`'s height pair matches the entry at height `H`, its height is `H`. -/
theorem named_height_of_matches_source_l86c
    {a : NamedAttestation V} {H : Height} {root : BlockId}
    (hmatch : NamedHeightPair.matchesEntry H root a.height_pair = true) :
    a.height_pair.erase.height? = some H := by
  obtain ⟨tmo, htmo⟩ := vote_of_matchesEntry hmatch
  rw [htmo]
  exact namedHeightPair_erase_vote_height? H root tmo

omit [Fintype V] in
/-- If `A ⪯ B` and `a` is a row of `A`, then `a` is among `B`'s chain attestations. -/
theorem named_row_mem_chain_of_ancestor_source_l86c
    {A B : NamedBlock V} {a : NamedAttestation V}
    (hAB : NamedBlock.Preceq A B) (ha : a ∈ A.attestations) :
    a ∈ Protocol.named_chain_attestations B := by
  induction B generalizing A with
  | genesis =>
      rw [namedPreceq_genesis_iff_l85] at hAB
      subst A
      simp [named_genesis_attestations] at ha
  | node parent slot root votes support rows proposer ih =>
      rw [namedPreceq_node_iff_l85] at hAB
      simp only [Protocol.named_chain_attestations, Finset.mem_union, List.mem_toFinset]
      rcases hAB with rfl | hparent
      · exact Or.inr (by simpa only [named_node_attestations] using ha)
      · exact Or.inl (ih hparent ha)

end FGSafetySourceNamed

end DecoupledConsensusModel.Sts
