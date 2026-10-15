module
public import Proofs.Vocabulary.Protocol.ChainState.FinalityComparison
public import Proofs.Vocabulary.ModelProperties.NamedAttestation_erase
public import Proofs.Vocabulary.ModelProperties.Block_Preceq
public import Proofs.Vocabulary.ModelProperties.RootInjectiveOnAncestors
public import Proofs.Vocabulary.ModelProperties.HasSlashableWeightBetween
public import Proofs.Vocabulary.ModelProperties.SlashableBetween
public import Proofs.Vocabulary.ModelProperties.NamedHeightPair_matchesEntry
public import Proofs.Vocabulary.Protocol.ChainState.CheckpointHeights
public import Proofs.Vocabulary.Protocol.ChainState.JustificationCertificates
public import Proofs.Vocabulary.Internal.Definitions.NamedDerived
public import Proofs.Vocabulary.Internal.StoreFinality
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.GradeBootstrapCore
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Logic.Equiv.PartialEquiv
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Justification upgrade

If a run block `BF` finalizes `F` at height `h_f` and a store's justification height is at least
`h_f`, the store's justified block `Σ.J` is a descendant of `F`.
-/


namespace DecoupledConsensusModel
namespace Proofs
namespace StoreFinality

open Protocol (HeightConfig derive_named)
open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]


omit [Fintype V] in
private theorem named_trans {A B C : NamedBlock V}
    (hAB : NamedBlock.Preceq A B) (hBC : NamedBlock.Preceq B C) : NamedBlock.Preceq A C := by
  induction C with
  | genesis =>
    simp only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] at hBC
    subst B
    exact hAB
  | node parent s root votes support rows proposer ih =>
    simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true, decide_eq_true_eq] at hBC
    rcases hBC with rfl | hparent
    · exact hAB
    · exact Proofs.NamedAncestry.named_extend s root votes support rows proposer (ih hparent)

omit [Fintype V] in
/-- A height-pair vote and a finality pair by the same validator, at the same height and on
    different targets, are slashable. -/
private theorem matching_finality_e1 (a b : NamedAttestation V)
    (h : Height) (entry finalized : BlockId)
    (hv : a.val_index = b.val_index)
    (hm : a.height_pair.matchesEntry h entry = true)
    (hf : b.finality_pair = some ⟨h, finalized⟩) (hne : entry ≠ finalized) :
    Protocol.Slashable a.erase b.erase := by
  cases hp : a.height_pair with
  | empty => simp [hp, NamedHeightPair.matchesEntry] at hm
  | vote height root timeout =>
    have heq : height = h ∧ root = entry := by
      simpa only [hp, NamedHeightPair.matchesEntry, decide_eq_true_eq] using hm
    rcases heq with ⟨rfl, rfl⟩
    cases timeout <;>
      simp [Protocol.Slashable, Protocol.slashable,
        Protocol.e1Slashable, Protocol.e1Fields,
        Protocol.conflictsWithFinality, Protocol.sameValidator,
        NamedAttestation.erase, NamedHeightPair.erase, hp, hf, hv, hne]


/-- If the run block `BF` finalizes `F` at height `h_f` and `h_f ≤ Σ.h_j`, then `F ⪯ Σ.J`. -/
theorem upgrade_of_height_le {S : Setup V} {ρ : Run V}
    {st : Protocol.NamedStore V} {BF : NamedBlock V} {F : Block V} {h_f : Height}
    (hsb : SlashableBound S ρ)
    (hcf : RootCollisionFree S ρ)
    (hBF : RunBlock S ρ BF)
    (hRun : ∀ D ∈ st.bodies, RunBlock S ρ D)
    (hprov : Proofs.Bridges.NamedProvenance S st)
    (hfin : Statements.Instantiation.NamedFinalizedAt S.E S.cfg BF F h_f)
    (hle : h_f ≤ st.core.h_j) :
    Block.preceq F st.core.J = true := by
  obtain ⟨C, hC, hCJ, hCh⟩ := hprov.2
  have hCrun : RunBlock S ρ C := hRun C hC
  by_cases hz : h_f = 0
  · have hFg : F = Block.genesis := by
      rw [← hfin.1]
      exact NamedFinalityCertificates.finalized_zero_is_genesis S.E S.cfg BF
        (by rw [hfin.2]; exact hz)
    rw [hFg]
    exact Protocol.preceq_genesis st.core.J
  have hFnz : (derive_named S.E S.cfg BF).h_F ≠ 0 := by
    rw [hfin.2]
    exact hz
  have hjnz : (derive_named S.E S.cfg C).h_j ≠ 0 := by
    rw [hCh]
    intro h0
    rw [h0] at hle
    exact hz (Nat.le_zero.mp hle)
  rcases lt_or_eq_of_le hle with hlt | heq
  · have hCbelow : h_f < (derive_named S.E S.cfg C).h := by
      have hjh :=
        (NamedDerivationGeometry.chainOrder_derive_named S.E S.cfg C).justified_below_height
      rw [hCh] at hjh
      exact lt_trans hlt hjh
    have hFC : Block.Preceq F C.erase := by
      have h := NamedFinalizationBridge.finalized_preceq_of_height_lt S ρ C BF hsb hcf
        hCrun hBF (by rw [hfin.2]; exact hCbelow)
      rwa [hfin.1] at h
    have hJC : Block.Preceq st.core.J C.erase := by
      rw [← hCJ]
      exact (Proofs.NamedStoreRoots.derive_named_anchors_preceq S.E S.cfg C).2
    rcases Proofs.ModelProperties.Preceq_linear hFC hJC with hFJ | hJF
    · exact Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mpr hFJ
    · exfalso
      obtain ⟨Jn, hJnC, hJnE, hJnh⟩ :=
        (NamedCheckpointHeights.justified_ancestor_height S.E S.cfg C).resolve_left hjnz
      obtain ⟨Fn, hFnBF, hFnE, hFnh⟩ :=
        (NamedCheckpointHeights.finalized_ancestor_height S.E S.cfg BF).resolve_left hFnz
      have hlift : Block.Preceq Jn.erase Fn.erase := by
        rw [hJnE, hCJ, hFnE, hfin.1]
        exact hJF
      obtain ⟨J', hJ'Fn, hJ'E⟩ := Proofs.NamedAncestry.erased_ancestor_lift Fn hlift
      have hroots : Jn.root = J'.root := by
        rw [← Proofs.NamedWire.erase_root Jn, ← Proofs.NamedWire.erase_root J', hJ'E]
      have hEq : Jn = J' :=
        NamedRootCollisionFree.root_injective hcf C BF hCrun hBF Jn J' (Or.inl hJnC)
          (Or.inr (named_trans hJ'Fn hFnBF)) hroots
      have hmono : (derive_named S.E S.cfg Jn).h ≤ (derive_named S.E S.cfg Fn).h := by
        rw [hEq]
        exact Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hJ'Fn
      rw [hJnh, hCh, hFnh, hfin.2] at hmono
      exact absurd hmono (Nat.not_le_of_gt hlt)
  · obtain ⟨Jn, hJnC, hJnE, Qj, hQj, hwj⟩ :=
      NamedJustificationCertificates.justification_certificate S.E S.cfg C hjnz
    obtain ⟨Fn, hFnBF, hFnE, Qf, hQf, hwf⟩ :=
      NamedFinalityCertificates.finality_certificate S.E S.cfg BF hFnz
    have hJnroot : Jn.root = st.core.J.root := by
      rw [← Proofs.NamedWire.erase_root Jn, hJnE, hCJ]
    have hFnroot : Fn.root = F.root := by
      rw [← Proofs.NamedWire.erase_root Fn, hFnE, hfin.1]
    by_cases hr : st.core.J.root = F.root
    · have hinj : Execution.RootInjectiveOnAncestors C.erase BF.erase :=
        NamedFinalizationBridge.rootInjectiveOnAncestors_of_collisionFree S ρ hcf C BF
          hCrun hBF
      have hJF : st.core.J = F :=
        Proofs.ModelProperties.RootInjectiveOnAncestors.eq_of_root_eq hinj
          (by
            rw [← hCJ]
            exact (Proofs.NamedStoreRoots.derive_named_anchors_preceq S.E S.cfg C).2)
          (by
            rw [← hfin.1]
            exact (Proofs.NamedStoreRoots.derive_named_anchors_preceq S.E S.cfg BF).1)
          hr
      rw [hJF]
      exact Block.preceq_self _
    · exfalso
      apply hsb C BF hCrun hBF
      refine Proofs.ModelProperties.hasSlashableWeightBetween_intro (Qj ∩ Qf)
        (quorum_intersection S.E hQj hQf) (fun i hi => ?_)
      obtain ⟨hij, hif⟩ := Finset.mem_inter.mp hi
      obtain ⟨ca, a, hca, ha, hav, hap⟩ := hwj i hij
      obtain ⟨cb, b, hcb, hb, hbv, hbp⟩ := hwf i hif
      refine Proofs.ModelProperties.slashableBetween_intro
        a.erase (Proofs.Bridges.erase_mem_chain_attestations C ca hca a ha)
        b.erase (Proofs.Bridges.erase_mem_chain_attestations BF cb hcb b hb)
        (by rw [Proofs.ModelProperties.erase_val_index]; exact hav)
        (by rw [Proofs.ModelProperties.erase_val_index]; exact hbv) ?_
      refine matching_finality_e1 a b h_f Jn.root Fn.root (hav.trans hbv.symm) ?_ ?_ ?_
      · rw [hap, Proofs.ModelProperties.matchesEntry_vote_iff]
        refine ⟨?_, rfl⟩
        rw [hCh, ← heq]
      · rw [hbp, hfin.2]
      · rw [hJnroot, hFnroot]
        exact hr


/-- If a body of the store justifies `F` at the height `h_f` at which the run block `BF` finalizes
    it, then `F ⪯ Σ.J`. -/
theorem upgrade {S : Setup V} {ρ : Run V} {st : Protocol.NamedStore V}
    {BF B : NamedBlock V} {F : Block V} {h_f : Height}
    (hnhj : Internal.NamedNoHighJustifications S.E S.cfg st)
    (hprov : Proofs.Bridges.NamedProvenance S st)
    (hB : B ∈ st.bodies)
    (hjust : Internal.NamedJustifiedAt S.E S.cfg B F h_f)
    (hsb : SlashableBound S ρ)
    (hcf : RootCollisionFree S ρ)
    (hBF : RunBlock S ρ BF)
    (hRun : ∀ D ∈ st.bodies, RunBlock S ρ D)
    (hfin : Statements.Instantiation.NamedFinalizedAt S.E S.cfg BF F h_f) :
    Block.preceq F st.core.J = true := by
  have hfloor : h_f ≤ st.core.h_j := by
    rw [← hjust.2]
    exact hnhj B hB
  exact upgrade_of_height_le hsb hcf hBF hRun hprov hfin hfloor


end StoreFinality
end Proofs
end DecoupledConsensusModel

end
