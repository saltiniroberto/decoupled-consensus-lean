import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.StoreFinalityUpgrade
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_FinalityCertificates
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_FinalityComparison
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_JustificationCertificates
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_FinalizationBridge
import Model.Conditions.Vocabulary_Internal_Legacy_Assumptions_Weight
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Admissible
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Run
import Proofs.Vocabulary.Protocol.ChainState.Chain
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Protocol_Evidence_ProvenanceBridge
import Model.Conditions.Vocabulary_Statements_Instantiation_Certificates
import Model.Record.Wiring

/-!
# A store justification descends from the finalized block

A store's justification at least as high as a finalized block's height descends from that block,
stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.StoreFinality
open DecoupledConsensusModel.Statements.Instantiation
open Protocol (HeightConfig derive_named)
open Internal
open Execution

/-- For every path `W` of `ρ`, if the run blocks read along `W` expose no slashable weight and are
    free of root collisions, `BF` and every body of `st` are run blocks read along `W`, `st` carries
    named provenance, `BF` finalizes `F` at height `h_f`, and `h_f ≤ st.core.h_j`, then `F` is an
    ancestor of `st.core.J`. -/
theorem Vocabulary.Proofs.StoreFinality.upgrade_of_height_le (facts : Record.Facts M) {S : Setup V} {ρ : Record.Run V}
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S ρ W)
    {st : M.NS} {BF : NamedBlock V} {F : Block V} {h_f : Height}
    (hsb : Restated.Vocabulary.Execution.SlashableBound M S ρ W)
    (hcf : Restated.Vocabulary.Execution.RootCollisionFree M S ρ W)
    (hBF : Restated.Vocabulary.Execution.RunBlock M S ρ W BF)
    (hRun : ∀ D ∈ st.bodies, Restated.Vocabulary.Execution.RunBlock M S ρ W D)
    (hprov : Restated.Vocabulary.Proofs.Bridges.NamedProvenance M S st)
    (hfin : Restated.Vocabulary.Statements.Instantiation.NamedFinalizedAt M S.E S.cfg BF F h_f)
    (hle : h_f ≤ st.core.h_j) :
    Block.preceq F st.core.J = true := by
  obtain ⟨C, hC, hCJ, hCh⟩ := hprov.2
  have hCrun : Restated.Vocabulary.Execution.RunBlock M S ρ W C := hRun C hC
  by_cases hz : h_f = 0
  · have hFg : F = Block.genesis := by
      rw [← hfin.1]
      exact facts.cs.finalized_zero_is_genesis S.E S.cfg BF
        (by rw [hfin.2]; exact hz)
    rw [hFg]
    exact Protocol.preceq_genesis st.core.J
  have hFnz : (M.derive_named S.E S.cfg BF).h_F ≠ 0 := by
    rw [hfin.2]
    exact hz
  have hjnz : (M.derive_named S.E S.cfg C).h_j ≠ 0 := by
    rw [hCh]
    intro h0
    rw [h0] at hle
    exact hz (Nat.le_zero.mp hle)
  rcases lt_or_eq_of_le hle with hlt | heq
  · have hCbelow : h_f < (M.derive_named S.E S.cfg C).h := by
      have hjh :=
        (facts.cs.chainOrder_derive_named S.E S.cfg C).justified_below_height
      rw [hCh] at hjh
      exact lt_trans hlt hjh
    have hFC : Block.Preceq F C.erase := by
      have h := Restated.Vocabulary.Proofs.NamedFinalizationBridge.finalized_preceq_of_height_lt facts S ρ W hW C BF hsb hcf
        hCrun hBF (by rw [hfin.2]; exact hCbelow)
      rwa [hfin.1] at h
    have hJC : Block.Preceq st.core.J C.erase := by
      rw [← hCJ]
      exact ((facts.cs.derive_named_anchors_preceq S.E S.cfg C)).2
    rcases Proofs.ModelProperties.Preceq_linear hFC hJC with hFJ | hJF
    · exact Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mpr hFJ
    · exfalso
      obtain ⟨Jn, hJnC, hJnE, hJnh⟩ :=
        (facts.cs.justified_ancestor_height S.E S.cfg C).resolve_left hjnz
      obtain ⟨Fn, hFnBF, hFnE, hFnh⟩ :=
        (facts.csAdded.finalized_ancestor_height S.E S.cfg BF).resolve_left hFnz
      have hlift : Block.Preceq Jn.erase Fn.erase := by
        rw [hJnE, hCJ, hFnE, hfin.1]
        exact hJF
      obtain ⟨J', hJ'Fn, hJ'E⟩ := Proofs.NamedAncestry.erased_ancestor_lift Fn hlift
      have hroots : Jn.root = J'.root := by
        rw [← Proofs.NamedWire.erase_root Jn, ← Proofs.NamedWire.erase_root J', hJ'E]
      have hEq : Jn = J' :=
        Restated.Vocabulary.Execution.NamedRootCollisionFree.root_injective hcf C BF hCrun hBF Jn J' (Or.inl hJnC)
          (Or.inr (Proofs.NamedOutageHistory.IdxDriverHelpers.named_preceq_trans hJ'Fn hFnBF)) hroots
      have hmono : (M.derive_named S.E S.cfg Jn).h ≤ (M.derive_named S.E S.cfg Fn).h := by
        rw [hEq]
        exact facts.cs.derive_height_mono S.E S.cfg hJ'Fn
      rw [hJnh, hCh, hFnh, hfin.2] at hmono
      exact absurd hmono (Nat.not_le_of_gt hlt)
  · obtain ⟨Jn, hJnC, hJnE, Qj, hQj, hwj⟩ :=
      Restated.Vocabulary.Proofs.NamedJustificationCertificates.justification_certificate facts S.E S.cfg C hjnz
    obtain ⟨Fn, hFnBF, hFnE, Qf, hQf, hwf⟩ :=
      Restated.Vocabulary.Proofs.NamedFinalityCertificates.finality_certificate facts S.E S.cfg BF hFnz
    have hJnroot : Jn.root = st.core.J.root := by
      rw [← Proofs.NamedWire.erase_root Jn, hJnE, hCJ]
    have hFnroot : Fn.root = F.root := by
      rw [← Proofs.NamedWire.erase_root Fn, hFnE, hfin.1]
    by_cases hr : st.core.J.root = F.root
    · have hinj : Execution.RootInjectiveOnAncestors C.erase BF.erase :=
        Restated.Vocabulary.Proofs.NamedFinalizationBridge.rootInjectiveOnAncestors_of_collisionFree facts S ρ W hW hcf C BF
          hCrun hBF
      have hJF : st.core.J = F :=
        Proofs.ModelProperties.RootInjectiveOnAncestors.eq_of_root_eq hinj
          (by
            rw [← hCJ]
            exact ((facts.cs.derive_named_anchors_preceq S.E S.cfg C)).2)
          (by
            rw [← hfin.1]
            exact ((facts.cs.derive_named_anchors_preceq S.E S.cfg BF)).1)
          hr
      rw [hJF]
      exact Block.preceq_self _
    · exfalso
      apply hsb C BF hCrun hBF
      refine facts.ev.ModelProperties_hasSlashableWeightBetween_intro (Qj ∩ Qf)
        (facts.ev.quorum_intersection S.E hQj hQf) (fun i hi => ?_)
      obtain ⟨hij, hif⟩ := Finset.mem_inter.mp hi
      obtain ⟨ca, a, hca, ha, hav, hap⟩ := hwj i hij
      obtain ⟨cb, b, hcb, hb, hbv, hbp⟩ := hwf i hif
      refine facts.ev.ModelProperties_slashableBetween_intro
        a.erase (facts.ev.erase_mem_chain_attestations C ca hca a ha)
        b.erase (facts.ev.erase_mem_chain_attestations BF cb hcb b hb)
        (by rw [Proofs.ModelProperties.erase_val_index]; exact hav)
        (by rw [Proofs.ModelProperties.erase_val_index]; exact hbv) ?_
      refine facts.csAdded.matching_finality_e1 a b h_f Jn.root Fn.root (hav.trans hbv.symm) ?_ ?_ ?_
      · rw [hap, Proofs.ModelProperties.matchesEntry_vote_iff]
        refine ⟨?_, rfl⟩
        rw [hCh, ← heq]
      · rw [hbp, hfin.2]
      · rw [hJnroot, hFnroot]
        exact hr

end

end DecoupledConsensusModel.Sts.Restated
