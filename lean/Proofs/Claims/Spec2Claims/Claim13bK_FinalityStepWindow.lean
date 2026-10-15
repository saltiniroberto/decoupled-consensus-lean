import Proofs.Claims.Spec2Claims.Claim13bK_ProposalAdoption
import Proofs.Claims.Spec2Claims.Claim13bModel_actionStoreAt
import Proofs.Claims.Spec2Claims.Claim13bModel_inWindow
import Proofs.Claims.Spec2Claims.Claim13bModel_select
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedStore_initial
import Proofs.Claims.Spec2Claims.Claim13bModel_derive_named
import Proofs.Vocabulary.Protocol.ValidatorClient.W4FKChainFinalityRows
import Proofs.Vocabulary.Protocol.ChainState.W4FKChainFinalityWrite
import Proofs.Vocabulary.Execution.W4FKChainAdvanceFold
import Proofs.Claims.Spec2Claims.Claim13bModel_setClock_inclG2b
import Proofs.Claims.Spec2Claims.Claim13bModel_setClock_incl
import Proofs.Claims.Spec2Claims.Claim13bModel_opening_slot
import Proofs.Claims.Spec2Claims.Claim13bModel_Preceq
import Proofs.Vocabulary.ModelProperties.Block_Preceq
import Proofs.Vocabulary.ModelProperties.NamedBlock_erase

/-!
# Justified and finalized blocks of a chain state

When a chain state's justified height is at most its finalized height, its justified block is an
ancestor of its finalized block.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation

variable {V : Type} [DecidableEq V] [Fintype V]

section ChainState

/-- If the justified height of `B`'s chain state is at most its finalized height, then its justified
    block is an ancestor of its finalized block. -/
theorem justified_preceq_finalized_of_le_f1b1 (E : Env V) (cfg : HeightConfig) (B : NamedBlock V)
    (hle : (Protocol.derive_named E cfg B).h_j ≤ (Protocol.derive_named E cfg B).h_F) :
    Block.Preceq (Protocol.derive_named E cfg B).J (Protocol.derive_named E cfg B).F := by
  obtain ⟨⟨J, hJB, hJerase, hJself, hJh⟩, ⟨F, hFB, hFerase, hFself, hFh⟩⟩ :=
    derive_named_checkpoint_entries E cfg B
  rcases hJh with ⟨-, rfl⟩ | hJh
  · rw [← hJerase, Proofs.ModelProperties.erase_genesis]
    exact preceq_eq_true_iff_Preceq.mp (Protocol.preceq_genesis _)
  have hone : ∀ X : NamedBlock V, 1 ≤ (Protocol.derive_named E cfg X).h := fun X =>
    derive_named_genesis_h E cfg ▸
      Proofs.NamedEntryHeight.derive_height_mono E cfg (genesis_namedPreceq_l85 X)
  rcases hFh with ⟨hF0, -⟩ | hFh
  · exfalso
    have h1 := hone J
    rw [hJh] at h1
    rw [hF0] at hle
    exact absurd (h1.trans hle) (by decide)
  rcases namedPreceq_total_l85 hJB hFB with hJF | hFJ
  · rw [← hJerase, ← hFerase]
    exact Proofs.NamedWire.erase_preceq hJF
  · have hFJh := Proofs.NamedEntryHeight.derive_height_mono E cfg hFJ
    have heq : (Protocol.derive_named E cfg F).h = (Protocol.derive_named E cfg J).h := by
      refine Nat.le_antisymm hFJh ?_
      rw [hJh, hFh]
      exact hle
    have hT := Proofs.NamedEntryHeight.entry_eq_on_plateau E cfg hFJ heq
    rw [hFself, hJself] at hT
    rw [← hJerase, ← hFerase, hT]
    exact Proofs.ModelProperties.Preceq_self _

end ChainState

end DecoupledConsensusModel.Sts
