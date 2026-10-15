import Proofs.Claims.Spec2Claims.Claim13beRoute3_48b
import Proofs.Vocabulary.Objects.EmittedHeightBound
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.ProposalVoteDuty
import Proofs.Claims.Spec2Claims.Claim13bModel_GoldfishStore_tau
import Proofs.Claims.Spec2Claims.Claim13bModel_GoldfishStore_pool
import Proofs.Claims.Spec2Claims.Claim13bModel_no_second_vote_in
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedDuties_goldfish_vote_with_some
import Proofs.Claims.Spec2Claims.Claim13bModel_ChainState_initial
import Proofs.Claims.Spec2Claims.Claim13bModel_Slashable
import Proofs.Claims.Spec2Claims.Claim13bModel_derive_named
import Proofs.Claims.Spec2Claims.Claim13bModel_e1Fields
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedHeightPair_erase
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedBlock_attestations
import Proofs.Claims.Spec2Claims.Claim13bModel_initial
import Proofs.Claims.Spec2Claims.Claim13bModel_actionStoreAt
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedAttestation_erase
import Proofs.Claims.Spec2Claims.Claim13bModel_setClock_inclG2b
import Proofs.Claims.Spec2Claims.Claim13bModel_weightOf
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedStore_initial
import Proofs.Claims.Spec2Claims.Claim13bModel_actionReadFrom
import Proofs.Claims.Spec2Claims.Claim13bModel_toHealing
import Proofs.Vocabulary.ModelProperties.Block_Preceq
import Proofs.Vocabulary.ModelProperties.viable_tree
import Proofs.Vocabulary.ModelProperties.Store_toHealing
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedBlock_gf_votes
import Proofs.Claims.Spec2Claims.Claim13bModel_propose_block_with_snd
import Proofs.Claims.Spec2Claims.Claim13bModel_setClock
import Proofs.Claims.Spec2Claims.Claim13bModel_setClock_inclG2
import Proofs.Vocabulary.ModelProperties.NamedDuties_attest_with
import Proofs.Vocabulary.ModelProperties.get_fg_root
import Proofs.Claims.Spec2Claims.Claim13bModel_get_filtered_block_tree_from
import Proofs.Claims.Spec2Claims.Claim13bModel_get_filtered_block_tree_inclG5
import Proofs.Claims.Spec2Claims.Claim13bModel_get_filtered_block_tree
import Proofs.Claims.Spec2Claims.Claim13bModel_voter_filtered_block_tree
import Proofs.Claims.Spec2Claims.Claim13bModel_voter_processed_block_tree
import Proofs.Claims.Spec2Claims.Claim13bModel_confirmationReadFrom
import Proofs.Claims.Spec2Claims.Claim13bModel_get_fg_root
import Proofs.Claims.Spec2Claims.Claim13bModel_get_head_in_tree_with_layer
import Proofs.Vocabulary.ModelProperties.get_head_in_tree_with_layer
import Proofs.Vocabulary.ModelProperties.NamedProfile_gradeContract
import Proofs.Vocabulary.Protocol.Grades.ProposalParent

/-!
# Per-instant forms of the FG witness lemmas

The FG selector body and the confirmation witness of an emitted height row, and the action store's
bodies, over a run whose premises are given by the bundle `AdmissibleFieldsOn` and whose run blocks
are read through `Xb`.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

section FGSelectorWitness

/-- If `a`'s signer, a member of `X`, emits `a` at `ta` with a height pair naming `h`, then `ta` is
    `a`'s round's action instant, `a` is the signer's action attestation of that round, the action's
    FG source is the erasure of a body `D` of the action store, both the store's cached height at it
    and `D`'s named height are `h`, and `a`'s height pair targets `D`'s entry root at `h` or is the
    timeout at `h`. -/
theorem honestEmittedHeightRow_exactFGSelectorWitnessOn
    (S : Setup V) {rho : Run V} (Hs : Int → Finset V) (Xb X : Finset V) {lo : Int}
    (hf : AdmissibleFieldsOn S rho Hs Xb lo)
    {a : NamedAttestation V} {ta : Time} {h : Height}
    (_haHon : a.val_index ∈ X)
    (hemit : rho.emits S a.val_index (Object.attest a) ta)
    (hh : a.height_pair.erase.height? = some h) :
    ∃ D : NamedBlock V, ∃ J : Block V,
      ta = S.a a.round ∧
        a = actionAttestationAt S rho a.val_index a.round ∧
        actionFGSource S (actionStoreAt S rho a.val_index a.round) =
          some D.erase ∧
        D ∈ (actionStoreAt S rho a.val_index a.round).st.bodies ∧
        ((actionStoreAt S rho a.val_index a.round).st.core.σ D.erase).h = h ∧
        (Protocol.derive_named S.E S.cfg D).h = h ∧
        J = (Protocol.derive_named S.E S.cfg D).T_h ∧
        (a.height_pair.erase = HeightPair.target h J.root ∨
          a.height_pair.erase = HeightPair.timeout h) := by
  have hshape := Proofs.Optimistic.emits_attest_shape S hemit
  have htime : ta = S.a a.round := hshape.2
  have haEq : a = actionAttestationAt S rho a.val_index a.round := by
    exact ((action_run_emissionOn S rho Hs Xb hf
      a.val_index a.round a).mp (by simpa only [htime] using hemit)).2.2
  rw [haEq] at hh
  generalize hp : (actionAttestationAt S rho a.val_index a.round).height_pair = q at hh
  cases q with
  | empty =>
      rw [namedHeightPair_erase_empty] at hh
      cases hh
  | vote h' entry timeout =>
      have hh' : h' = h := by
        rw [namedHeightPair_erase_vote_height?] at hh
        exact Option.some.inj hh
      subst h'
      obtain ⟨Cfg, hCfg, hCfgHeight, hCfgRoot⟩ :=
        NamedActionSources.action_source S rho a.val_index a.round h entry timeout
          hp
      obtain ⟨D, hD, hDerase, hDderive, -⟩ :=
        NamedActionSources.action_witness S rho a.val_index a.round Cfg hCfg
      let J := (Protocol.derive_named S.E S.cfg D).T_h
      have hsource : actionFGSource S
          (actionStoreAt S rho a.val_index a.round) = some D.erase := by
        simpa only [actionStoreAt, hDerase] using hCfg
      have hheight :
          ((actionStoreAt S rho a.val_index a.round).st.core.σ D.erase).h = h := by
        simpa only [actionStoreAt, hDerase] using hCfgHeight
      have hnamedHeight :
          (Protocol.derive_named S.E S.cfg D).h = h := by
        simpa only [hDderive, actionStoreAt, hDerase] using hheight
      have hJroot : J.root = entry := by
        dsimp only [J]
        simpa only [hDderive] using hCfgRoot
      refine ⟨D, J, htime, haEq, hsource, hD, hheight,
        hnamedHeight, rfl, ?_⟩
      cases timeout with
      | false =>
          left
          rw [haEq, hp, namedHeightPair_erase_vote_false, hJroot]
      | true =>
          right
          rw [haEq, hp, namedHeightPair_erase_vote_true]

end FGSelectorWitness

section FGConfirmationHistory

/-- `v`'s round-`r` action store is coherent. -/
theorem actionStore_coherentOn
    (S : Setup V) {rho : Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    (_hf : AdmissibleFieldsOn S rho Hs Xb lo)
    (v : V) (r : Round) :
    Proofs.NamedStore.Coherent S.E S.cfg (actionStoreAt S rho v r).st := by
  apply Proofs.NamedDuties.coherent_confirmation
  show Proofs.NamedStore.Coherent S.E S.cfg (NamedActionReads.confirmationReadFrom S
    (NamedRun.stateBeforeTime S rho (S.a r) v) (S.a r)).st
  rw [confirmationReadFrom_st]
  exact Proofs.NamedStore.coherent_clock S.E S.cfg _ (S.a r)
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho (S.a r) v).1.1.1

/-- If `v ∈ Xb` and `D` is a body of `v`'s round-`r` action store, `D` is a run block read through
    `Xb`. -/
theorem actionBody_runBlockOn
    (S : Setup V) {rho : Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    (hf : AdmissibleFieldsOn S rho Hs Xb lo)
    {v : V} (hv : v ∈ Xb) {r : Round} {D : NamedBlock V}
    (hD : D ∈ (actionStoreAt S rho v r).st.bodies) :
    RunBlockOn S rho Xb D := by
  have hDpre : D ∈ (rho.stateBeforeTime S (S.a r) v).st.bodies := by
    have h := hD
    simp only [actionStoreAt, actionReadAt, NamedActionReads.actionReadAt] at h
    rw [actionReadFrom_st_bodies] at h
    exact h
  obtain ⟨i, hi, -⟩ := stateBeforeTime_eq_stateBeforeOn S Hs Xb hf (S.a r)
  have hDi : D ∈ (rho.stateBefore S i v).st.bodies := by
    have h2 : D ∈ (rho.stateBeforeTime S (S.a r) v).st.bodies := hDpre
    rw [hi] at h2
    exact h2
  exact runBlock_of_stateBefore_memOn S Xb hv hDi

/-- If `v ∈ Xb` and `D` is a body of `v`'s round-`r` action store, some body `K` of that store
    erases to `D`'s entry, has `D`'s named height, is an ancestor of `D`, and is a run block read
    through `Xb`. -/
theorem action_named_checkpointOn
    (S : Setup V) {rho : Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    (hf : AdmissibleFieldsOn S rho Hs Xb lo)
    {v : V} (hv : v ∈ Xb) {r : Round} {D : NamedBlock V}
    (hD : D ∈ (actionStoreAt S rho v r).st.bodies) :
    ∃ K : NamedBlock V,
      K ∈ (actionStoreAt S rho v r).st.bodies ∧
      K.erase = (derive_named S.E S.cfg D).T_h ∧
      (derive_named S.E S.cfg K).h = (derive_named S.E S.cfg D).h ∧
      NamedBlock.Preceq K D ∧
      RunBlockOn S rho Xb K := by
  obtain ⟨K, hKD, hKentry, hKh⟩ :=
    Proofs.NamedEntryHeight.entry_ancestor_same_height S.E S.cfg D
  have hcoh := actionStore_coherentOn S Hs Xb hf v r
  have hK : K ∈ (actionStoreAt S rho v r).st.bodies :=
    (priv% Proofs.Vocabulary.Objects.FGConfirmationHistory
      DecoupledConsensusModel.Proofs.HealingSurface.namedAncestorBodyMem) hcoh.2.2.1 hD hKD
  exact ⟨K, hK, hKentry, hKh, hKD, actionBody_runBlockOn S Hs Xb hf hv hK⟩

/-- If `a`'s signer, a member of `Xb`, emits `a` at `ta` with a height pair naming `h`, the signer's
    round action has FG source `D` at named height `h` and confirmation witness the entry of a
    same-height checkpoint body `K ⪯ D`, and `a`'s height pair targets `K`'s root at `h` or is the
    timeout at `h`. -/
theorem honestHeightRow_confirmationWitnessOn
    (S : Setup V) {rho : Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    (hf : AdmissibleFieldsOn S rho Hs Xb lo)
    {a : NamedAttestation V} {ta : Time} {h : Height}
    (haHon : a.val_index ∈ Xb)
    (hemit : rho.emits S a.val_index (Object.attest a) ta)
    (hh : a.height_pair.erase.height? = some h) :
    ∃ D K : NamedBlock V,
      fgConfirmationWitness S
          (actionStoreAt S rho a.val_index a.round) =
        some (derive_named S.E S.cfg K).T_h ∧
      D ∈ (actionStoreAt S rho a.val_index a.round).st.bodies ∧
      actionFGSource S (actionStoreAt S rho a.val_index a.round) = some D.erase ∧
      (derive_named S.E S.cfg D).h = h ∧
      K ∈ (actionStoreAt S rho a.val_index a.round).st.bodies ∧
      K.erase = (derive_named S.E S.cfg D).T_h ∧
      (derive_named S.E S.cfg K).h = h ∧
      Block.Preceq K.erase D.erase ∧
      (a.height_pair.erase = HeightPair.target h K.erase.root ∨
        a.height_pair.erase = HeightPair.timeout h) := by
  obtain ⟨D, J, htime, ha, hsource, hD, hheight, hnamedHeight, hJ, hrow⟩ :=
    honestEmittedHeightRow_exactFGSelectorWitnessOn S Hs Xb Xb hf haHon hemit hh
  obtain ⟨K, hK, hKentry, hKheight, hKpre, hKrun⟩ :=
    action_named_checkpointOn S Hs Xb hf haHon hD
  have hKheight' : (derive_named S.E S.cfg K).h = h :=
    hKheight.trans hnamedHeight
  have hDderive :
      (actionStoreAt S rho a.val_index a.round).st.core.σ D.erase =
        derive_named S.E S.cfg D :=
    (actionStore_coherentOn S Hs Xb hf a.val_index a.round).2.2.2.2 D hD
  have hfg' : fgConfirmationWitness S
      (actionStoreAt S rho a.val_index a.round) =
      some (derive_named S.E S.cfg D).T_h := by
    unfold fgConfirmationWitness
    rw [hsource, Option.map_some, hDderive]
  have hKtarget : (derive_named S.E S.cfg K).T_h = K.erase := by
    exact (Proofs.NamedEntryHeight.entry_eq_on_plateau S.E S.cfg hKpre hKheight).trans
      hKentry.symm
  have hfgK : fgConfirmationWitness S
      (actionStoreAt S rho a.val_index a.round) =
      some (derive_named S.E S.cfg K).T_h := by
    rw [hfg']
    congr 1
    exact (hKtarget.trans hKentry).symm
  have hJroot : J.root = K.erase.root := by
    rw [hJ, ← hKentry]
  refine ⟨D, K, hfgK, hD, hsource, hnamedHeight, hK, hKentry,
    hKheight', ?_, ?_⟩
  · exact Proofs.NamedWire.erase_preceq hKpre
  · simpa only [hJroot] using hrow

end FGConfirmationHistory

end DecoupledConsensusModel.Sts
