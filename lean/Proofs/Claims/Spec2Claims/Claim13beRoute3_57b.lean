import Proofs.Vocabulary.Protocol.Grades.GSTZeroSelectionSafety
import Proofs.Vocabulary.Objects.HeightRegimeStep
import Proofs.Claims.Spec2Claims.Claim13beRoute3_56
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedAttestation_erase
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedHeightPair_erase
import Proofs.Claims.Spec2Claims.Claim13bModel_opening_slot
import Proofs.Claims.Spec2Claims.Claim13bModel_actionStoreAt
import Proofs.Claims.Spec2Claims.Claim13bModel_Preceq
import Proofs.Vocabulary.ModelProperties.get_fg_root
import Proofs.Claims.Spec2Claims.Claim13bModel_domain_attest
import Proofs.Claims.Spec2Claims.Claim13bModel_opening
import Proofs.Claims.Spec2Claims.Claim13bModel_a

/-!
# Action stores and the height regime

The action store's agreement with the named derivation, its bodies as run blocks, and the justified
and finalized blocks of a store at a checkpoint height, over a run whose premises are given by the
bundle `AdmissibleFieldsOn`.
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

section RecoverySourceProgress

/-- For every validator `v` and round `r`, every body `D` of `v`'s round-`r` action store has, in
    that store, the stored view of its named derivation. -/
theorem derivedStateAgrees_actionStoreAtOn
    (S : Setup V) {rho : Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    (_hf : AdmissibleFieldsOn S rho Hs Xb lo)
    (v : V) (r : Round) :
    Internal.NamedDerivedStateAgrees S.E S.cfg (actionStoreAt S rho v r).st := by
  intro D hD
  have hDpre : D ∈ (rho.stateBeforeTime S (S.a r) v).st.bodies := by
    rw [actionStoreAt_st_bodies] at hD
    exact hD
  have hview := Proofs.NamedStoreBridge.derivedView_stateBeforeTime
    S rho (S.a r) v D hDpre
  rw [actionStoreAt_st_core_σ]
  exact hview

end RecoverySourceProgress

section HeightRegimeStep

open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas

/-- If `v ∈ Xb` and `D` is a body of `v`'s round-`r` action store, `D` is a run block read through
    `Xb`. -/
theorem actionBody_runBlock_heightRegimeOn
    (S : Setup V) {rho : Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    (hf : AdmissibleFieldsOn S rho Hs Xb lo)
    {v : V} (hv : v ∈ Xb) {r : Round} {D : NamedBlock V}
    (hD : D ∈ (actionStoreAt S rho v r).st.bodies) :
    RunBlockOn S rho Xb D :=
  actionBody_runBlockOn S Hs Xb hf hv hD

/-- Under `BelowOneThird S (Hs rho.horizon)`, if `v ∈ Xb`, `T` is a run block read through `Xb`,
    `k ≠ 0`, every height-`k` row emitted by a signer in `Hs rho.horizon` has `T` as its action's
    confirmation witness, and `v`'s justified height after `n` events is `k`, then `v`'s justified
    block there is `T.erase`. -/
theorem storeJustified_eq_of_honestWitnessesOn
    (S : Setup V) {rho : Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    (hf : AdmissibleFieldsOn S rho Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hbelow : Execution.BelowOneThird S (Hs rho.horizon))
    {v : V} (hv : v ∈ Xb) {n : Nat} {k : Height} {T : NamedBlock V}
    (hTrun : RunBlockOn S rho Xb T) (hk : k ≠ 0)
    (hwit : ∀ (b : NamedAttestation V) (tb : Time), b.val_index ∈ Hs rho.horizon →
      NamedRun.emits S rho b.val_index (Object.attest b) tb →
      b.height_pair.erase.height? = some k →
      fgConfirmationWitness S (actionStoreAt S rho b.val_index b.round) = some T.erase)
    (hhj : (rho.stateBefore S n v).st.core.h_j = k) :
    (rho.stateBefore S n v).st.core.J = T.erase := by
  have hmajority := AlignedRoundLemmas.honestWeightMajority_of_belowOneThird hbelow
  obtain ⟨C, hC, hCJ, hhjC⟩ :=
    Proofs.Bridges.storeJustificationOnChain_stateBefore S rho n v
  have hCrun : RunBlockOn S rho Xb C :=
    runBlock_of_stateBefore_memOn S Xb hv hC
  have hhjC' : (Protocol.derive_named S.E S.cfg C).h_j = k := hhjC.trans hhj
  obtain ⟨J, hJC, hJerase, Q, hQ, hwitQ⟩ :=
    NamedJustificationCertificates.justification_certificate S.E S.cfg C
      (by rw [hhjC']; exact hk)
  obtain ⟨i, hiQ, hiHon⟩ :=
    Protocol.HonestWeightMajority.exists_honest_member_of_quorum hmajority hQ
  obtain ⟨carrier, a, hcarrier, ha, hai, hap⟩ := hwitQ i hiQ
  have haHon : a.val_index ∈ Hs rho.horizon := by rw [hai]; exact hiHon
  have haChain : a.erase ∈ chain_attestations C.erase :=
    Proofs.Bridges.erase_mem_chain_attestations C carrier hcarrier a ha
  obtain ⟨b, tb, hba, hemit⟩ :=
    carriedByHonest_of_runBlockOn S Hs Xb hf hHs hCrun a.erase haChain
      (by rw [namedAttestation_erase_val_index]; exact haHon)
  have hbHon : b.val_index ∈ Hs rho.horizon := by
    have hvb : b.val_index = a.val_index := by
      have h := congrArg CombinedAttestation.val_index hba
      rwa [namedAttestation_erase_val_index, namedAttestation_erase_val_index] at h
    rw [hvb]
    exact haHon
  have hpairEq : b.height_pair.erase = a.height_pair.erase := by
    have h := congrArg CombinedAttestation.height_pair hba
    rwa [namedAttestation_erase_height_pair, namedAttestation_erase_height_pair] at h
  have hbrow : b.height_pair.erase.height? = some k := by
    rw [hpairEq, hap, hhjC']
    exact namedHeightPair_erase_vote_height? k J.root false
  have hva : a.erase.val_index = b.val_index :=
    (congrArg CombinedAttestation.val_index hba.symm).trans (namedAttestation_erase_val_index b)
  rw [hva] at hemit
  have hW := hwit b tb hbHon hemit hbrow
  obtain ⟨D, K, hK, hD, hsource, hDheight, hKmem, hKentry, hKheight,
      hKD, hshape⟩ := honestHeightRow_confirmationWitnessOn S Hs Xb hf (hHsXb _ hbHon) hemit hbrow
  have hKT : (Protocol.derive_named S.E S.cfg K).T_h = T.erase :=
    Option.some.inj (hK.symm.trans hW)
  have hJroot : J.root = K.erase.root := by
    have hpair : a.height_pair.erase = HeightPair.target k J.erase.root := by
      rw [hap, hhjC', namedHeightPair_erase_vote_false, Proofs.NamedWire.erase_root]
    rcases hshape with htarget | htimeout
    · have htarget' : HeightPair.target k J.erase.root =
          HeightPair.target k K.erase.root := by
        calc
          HeightPair.target k J.erase.root = a.height_pair.erase := hpair.symm
          _ = b.height_pair.erase := hpairEq.symm
          _ = HeightPair.target k K.erase.root := htarget
      exact (Proofs.NamedWire.erase_root J).symm.trans (HeightPair.target.inj htarget').2
    · rw [hpairEq, hpair] at htimeout
      cases htimeout
  have hDrun : RunBlockOn S rho Xb D :=
    actionBody_runBlock_heightRegimeOn S Hs Xb hf (hHsXb _ hbHon) hD
  have hKrun : RunBlockOn S rho Xb K :=
    actionBody_runBlock_heightRegimeOn S Hs Xb hf (hHsXb _ hbHon) hKmem
  obtain ⟨K', hK'D, hK'entry⟩ :=
    Proofs.NamedAncestry.erased_ancestor_lift D hKD
  have hK'run : RunBlockOn S rho Xb K' :=
    blockInRun_of_ancestorOn S rho Xb hDrun hK'D
  have hK'eq : K' = K := by
    apply hf.rootCollisionFree.root_injective K' K hK'run hKrun K' K
      (Or.inl (Proofs.NamedAncestry.named_self K'))
      (Or.inr (Proofs.NamedAncestry.named_self K))
    rw [← Proofs.NamedWire.erase_root K', hK'entry, Proofs.NamedWire.erase_root]
  have hKtarget : (Protocol.derive_named S.E S.cfg K).T_h = K.erase := by
    have hplateau : (Protocol.derive_named S.E S.cfg K).T_h =
        (Protocol.derive_named S.E S.cfg D).T_h := by
      rw [← hK'eq]
      exact Proofs.NamedEntryHeight.entry_eq_on_plateau S.E S.cfg hK'D
        ((hK'eq ▸ hKheight).trans hDheight.symm)
    exact hplateau.trans hKentry.symm
  have hTroot : T.root = K.root := by
    calc
      T.root = T.erase.root := (Proofs.NamedWire.erase_root T).symm
      _ = (Protocol.derive_named S.E S.cfg K).T_h.root :=
        (congrArg Block.root hKT).symm
      _ = K.erase.root := congrArg Block.root hKtarget
      _ = K.root := Proofs.NamedWire.erase_root K
  have hJroot' : J.root = K.root := hJroot.trans (Proofs.NamedWire.erase_root K)
  have hJrun : RunBlockOn S rho Xb J :=
    blockInRun_of_ancestorOn S rho Xb hCrun hJC
  have hJK : J = T := by
    apply hf.rootCollisionFree.root_injective J T hJrun hTrun J T
      (Or.inl (Proofs.NamedAncestry.named_self J))
      (Or.inr (Proofs.NamedAncestry.named_self T))
    exact hJroot'.trans hTroot.symm
  rw [← hCJ, ← hJerase, hJK]

/-- Under `BelowOneThird S (Hs rho.horizon)`, if `v ∈ Xb`, `T` is a run block read through `Xb` of
    height `k ≥ 2`, every height-`k` row emitted by a signer in `Hs rho.horizon` has `T` as its
    action's confirmation witness, and `v`'s `h_max` after `n` events is at most `k + 1`, then `v`'s
    finalized block there is an ancestor of `T.erase`. -/
theorem storeF_preceq_checkpoint_of_windowOn
    (S : Setup V) {rho : Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    (hf : AdmissibleFieldsOn S rho Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hbelow : Execution.BelowOneThird S (Hs rho.horizon))
    {v : V} (hv : v ∈ Xb) {n : Nat} {k : Height} {T : NamedBlock V}
    (hTrun : RunBlockOn S rho Xb T)
    (hTh : (Protocol.derive_named S.E S.cfg T).h = k) (hk : 2 ≤ k)
    (hwit : ∀ (b : NamedAttestation V) (tb : Time), b.val_index ∈ Hs rho.horizon →
      NamedRun.emits S rho b.val_index (Object.attest b) tb →
      b.height_pair.erase.height? = some k →
      fgConfirmationWitness S (actionStoreAt S rho b.val_index b.round) = some T.erase)
    (hwin : (rho.stateBefore S n v).st.core.h_max ≤ k + 1) :
    Block.Preceq (rho.stateBefore S n v).st.core.F T.erase := by
  have hsb : SlashableBoundOn S rho Xb := hf.slashableBound
  obtain ⟨C, hC, hF, hFheight⟩ :=
    Proofs.Bridges.storeFinalizationOnChain_stateBefore S rho n v
  have hCrun : RunBlockOn S rho Xb C :=
    runBlock_of_stateBefore_memOn S Xb hv hC
  have hFle : (Protocol.derive_named S.E S.cfg C).h_F ≤ k :=
    Nat.le_of_lt_succ (hFheight.trans_le hwin)
  rcases lt_or_eq_of_le hFle with hFlt | hFeq
  · have hpre : Block.Preceq (Protocol.derive_named S.E S.cfg C).F T.erase :=
      finalized_preceq_of_height_ltOn S rho Xb T C hsb
        hf.rootCollisionFree hTrun hCrun
        (by rw [hTh]; exact hFlt)
    simpa only [hF] using hpre
  · have hFJ : Block.Preceq (rho.stateBefore S n v).st.core.F
        (rho.stateBefore S n v).st.core.J :=
      Proofs.NamedStoreBridge.finalized_preceq_justified_stateBefore S rho n v
    obtain ⟨C', hC', hJ, hhj'⟩ :=
      NamedJustificationCarrier.justification_carrier_stateBefore S rho n v
    have hC'run : RunBlockOn S rho Xb C' :=
      runBlock_of_stateBefore_memOn S Xb hv hC'
    have hFnonzero : (Protocol.derive_named S.E S.cfg C).h_F ≠ 0 := by
      intro hzero
      exact (Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hk))
        (hFeq.symm.trans hzero)
    obtain ⟨Fn, hFnC, hFnErase, hFnHeight⟩ :=
      (NamedCheckpointHeights.finalized_ancestor_height S.E S.cfg C).resolve_left hFnonzero
    have hFnState : Fn.erase = (rho.stateBefore S n v).st.core.F :=
      hFnErase.trans hF
    have hFnrun : RunBlockOn S rho Xb Fn :=
      blockInRun_of_ancestorOn S rho Xb hCrun hFnC
    rcases NamedCheckpointHeights.justified_ancestor_height S.E S.cfg C' with
      hJzero | ⟨Jn, hJnC', hJnErase, hJnHeight⟩
    · exfalso
      have hJgen : (rho.stateBefore S n v).st.core.J = Block.genesis := by
        rw [← hJ]
        exact NamedJustificationCertificates.justified_zero_is_genesis S.E S.cfg C' hJzero
      have hFgen : (rho.stateBefore S n v).st.core.F = Block.genesis :=
        Block.preceq_antisymm (by rw [hJgen] at hFJ; exact preceq_eq_true_iff_Preceq.mpr hFJ)
          (Protocol.preceq_genesis _)
      have hFnGen : Fn = NamedBlock.genesis :=
        (priv% Proofs.Vocabulary.Objects.HeightRegimeStep
          DecoupledConsensusModel.Proofs.HealingSurface.namedGenesis_of_erase_genesis)
          (hFnState.trans hFgen)
      have hFnHeight' : (Protocol.derive_named S.E S.cfg Fn).h = k :=
        hFnHeight.trans hFeq
      rw [hFnGen, derive_named_genesis_h] at hFnHeight'
      exact absurd hFnHeight'
        (Nat.ne_of_lt (lt_of_lt_of_le (by decide : 1 < 2) hk))
    have hJnState : Jn.erase =
        (rho.stateBefore S n v).st.core.J := hJnErase.trans hJ
    have hJnrun : RunBlockOn S rho Xb Jn :=
      blockInRun_of_ancestorOn S rho Xb hC'run hJnC'
    have hFJ' : Block.Preceq (rho.stateBefore S n v).st.core.F Jn.erase := by
      rw [hJnState]
      exact hFJ
    obtain ⟨F'n, hF'nJn, hF'nErase⟩ :=
      Proofs.NamedAncestry.erased_ancestor_lift Jn hFJ'
    have hF'nrun : RunBlockOn S rho Xb F'n :=
      blockInRun_of_ancestorOn S rho Xb hJnrun hF'nJn
    have hF'nFn : F'n = Fn := by
      apply hf.rootCollisionFree.root_injective F'n Fn hF'nrun hFnrun F'n Fn
        (Or.inl (Proofs.NamedAncestry.named_self F'n))
        (Or.inr (Proofs.NamedAncestry.named_self Fn))
      rw [← Proofs.NamedWire.erase_root F'n, hF'nErase, hFnState.symm,
        Proofs.NamedWire.erase_root]
    have hFnHeight' : (Protocol.derive_named S.E S.cfg Fn).h = k := by
      exact hFnHeight.trans hFeq
    have hJnHeight' : (Protocol.derive_named S.E S.cfg Jn).h =
        (rho.stateBefore S n v).st.core.h_j := hJnHeight.trans hhj'
    have hjge : k ≤ (rho.stateBefore S n v).st.core.h_j := by
      rw [← hFnHeight', ← hJnHeight']
      rw [← hF'nFn]
      exact Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hF'nJn
    have hjlt : (rho.stateBefore S n v).st.core.h_j <
        (rho.stateBefore S n v).st.core.h_max := by
      exact NamedJustificationBound.justificationBelowMax_stateBefore S rho n v
    have hjeq : (rho.stateBefore S n v).st.core.h_j = k :=
      Nat.le_antisymm (Nat.le_of_lt_succ (hjlt.trans_le hwin)) hjge
    have hJT := storeJustified_eq_of_honestWitnessesOn S Hs Xb hf hHs hHsXb hbelow hv
      hTrun (Nat.ne_of_gt (lt_of_lt_of_le (by decide) hk)) hwit hjeq
    rw [hJT] at hFJ
    exact hFJ

end HeightRegimeStep

end DecoupledConsensusModel.Sts
