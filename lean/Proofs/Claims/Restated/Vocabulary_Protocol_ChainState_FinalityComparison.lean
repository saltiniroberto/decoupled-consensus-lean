import Proofs.Vocabulary.Protocol.ChainState.FinalityComparison
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_FinalityCertificates
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedOutageEntry
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Record.Wiring

/-!
# Finalized blocks of run blocks

A theorem over a model `M : Record.Model V` and its facts `facts : Record.Facts M`: along a path `W`
of a run with the slashable bound and no root collision, the finalized block of a run block `D` is
an ancestor of every run block whose height is greater than `D`'s finalized height.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedFinalizationBridge
open Execution Protocol

/-- For every path `W` of `rho`, if the run blocks read along `W` satisfy the slashable bound and
    have no root collision, `C` and `D` are run blocks read along `W`, and `D`'s finalized height is
    less than `C`'s height, then `D`'s finalized block is an ancestor of `C`'s erasure. -/
theorem Vocabulary.Proofs.NamedFinalizationBridge.finalized_preceq_of_height_lt (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N)
    (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (C D : NamedBlock V)
    (hsb : Restated.Vocabulary.Internal.NamedOutageEntry.SlashableBound M S rho W)
    (hroot : Restated.Vocabulary.Execution.NamedRootCollisionFree M S rho W)
    (hC : Restated.Vocabulary.Execution.NamedRun.blockInRun M S rho W C) (hD : Restated.Vocabulary.Execution.NamedRun.blockInRun M S rho W D)
    (hlt : (M.derive_named S.E S.cfg D).h_F < (M.derive_named S.E S.cfg C).h) :
    Block.Preceq (M.derive_named S.E S.cfg D).F C.erase := by
  by_cases hz : (M.derive_named S.E S.cfg D).h_F = 0
  · rw [facts.cs.finalized_zero_is_genesis S.E S.cfg D hz]
    exact Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mp (Protocol.preceq_genesis C.erase)
  · obtain ⟨F, hFD, hFE, Qf, hQf, hwf⟩ :=
      Restated.Vocabulary.Proofs.NamedFinalityCertificates.finality_certificate facts S.E S.cfg D hz
    obtain ⟨X, hXC, _hXheight, Qc, hQc, hwc⟩ :=
      facts.cs.height_crossing S.E S.cfg C
        (M.derive_named S.E S.cfg D).h_F (Nat.one_le_iff_ne_zero.mpr hz) hlt
    by_cases hroots : X.root = F.root
    · have hXF : X = F :=
        hroot.root_injective C D hC hD X F (Or.inl hXC) (Or.inr hFD) hroots
      rw [← hFE, ← hXF]
      exact Proofs.NamedWire.erase_preceq hXC
    · exfalso
      apply hsb C D hC hD
      refine facts.ev.ModelProperties_hasSlashableWeightBetween_intro (Qc ∩ Qf)
        (facts.ev.quorum_intersection S.E hQc hQf) ?_
      intro signer hsigner
      obtain ⟨hc, hf⟩ := Finset.mem_inter.mp hsigner
      obtain ⟨carrierA, a, hcarrierA, ha, hav, hamatch⟩ := hwc signer hc
      obtain ⟨carrierB, b, hcarrierB, hb, hbv, hbfinal⟩ := hwf signer hf
      refine facts.ev.ModelProperties_slashableBetween_intro a.erase
        (facts.ev.named_row_erase_mem hcarrierA ha)
        b.erase (facts.ev.named_row_erase_mem hcarrierB hb)
        ?_ ?_ ?_
      · exact (Proofs.ModelProperties.erase_val_index a).trans hav
      · exact (Proofs.ModelProperties.erase_val_index b).trans hbv
      · exact facts.csAdded.matching_finality_e1 a b
          (M.derive_named S.E S.cfg D).h_F X.root F.root
          (hav.trans hbv.symm) hamatch hbfinal hroots

end

end DecoupledConsensusModel.Sts.Restated
