import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bK_ConeChain
import Proofs.Claims.Restated.Claim13bK_ConfirmedOld
import Proofs.Claims.Restated.Claim13bK_FgJustified
import Proofs.Claims.Restated.Claim13bK_FinBeforeTick
import Proofs.Claims.Restated.Claim13bK_GradeDescendant
import Proofs.Claims.Restated.Claim13bK_GradeOld
import Proofs.Claims.Restated.Claim13bK_GradeOldHeads
import Proofs.Claims.Restated.Claim13bK_HeadsNewAnchor
import Proofs.Claims.Restated.Claim13bStepActionF
import Proofs.Claims.Restated.Claim13bStepAssembly
import Proofs.Claims.Restated.Claim13bStepConeIter
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bStepSGMove
import Proofs.Claims.Restated.Claim13beRoute3_5
import Proofs.Claims.Restated.CommonViewOfFinalizedDescendantsFacts
import Proofs.Claims.Restated.ProcessIdempotent
import Proofs.Claims.Restated.Projection
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bInvariantActiveTop
import Model.Conditions.Claim13bK_FgJustified
import Model.Conditions.Claim13bK_FinBeforeTick
import Model.Conditions.Claim13bK_GradePairwise
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13bStepAssembly
import Model.Conditions.Claim13bStepCone
import Model.Conditions.Claim13bStepConeIter
import Model.Conditions.Claim13bStepSG
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring

/-!
# Confirmed blocks on one chain with the attested confirmed blocks

After the phase, the block each member of `HonRound S Sched r` names as confirmed in its round-`r`
attestation lies on one chain with the confirmed block of every member of
`HonRound S Sched (r + 1)`, given the honest heads of round `r + 1`'s opening slot; with the anchor
chain and compatibility facts at the confirmation read this uses. Stated over a model
`M : Record.Model V` and its facts.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
set_option autoImplicit false

omit [Fintype V] in
/-- If `A` and `B` lie on one chain, so do `B` and `A`. -/
private theorem compatible_symm_l3 {A B : Block V} (h : Block.compatible A B = true) :
    Block.compatible B A = true :=
  Protocol.compatible_comm h

/-- If `a + 3 ≤ b` then `a + 2 ≤ b`. -/
private theorem two_le_of_three_le_l3 (a b : Nat) (h : a + 3 ≤ b) : a + 2 ≤ b := by omega

/-- If `a + 2 ≤ s` then `0 < s`. -/
private theorem pos_of_add_two_le_l3 (a s : Nat) (h : a + 2 ≤ s) : 0 < s := by omega

/-- For a positive slot `s`, `support_cutoff s = slotStart s + 2Δ`. -/
private theorem support_cutoff_eq_of_pos (facts : Record.Facts M) (E : Env V) {s : Slot}
    (hs : 0 < s) : M.support_cutoff E s = slotStart E.Δ s + 2 * E.Δ := by
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, (Nat.succ_pred_eq_of_pos hs).symm⟩
  rw [← facts.sch.confirmation_time_eq_support_cutoff_succ,
    ← facts.sch.slotStart_add_six_delta_eq_confirmation_time, slotStart_succ]
  ring

/-- If `C` is in the store's tree, the store's finalized block and fork-choice root are ancestors of
    `C`, and some descendant `W` of `C` in the tree has chain-state height at least the store's
    `h_max` minus one, then `C` is in the tree the store's confirmation walk descends. -/
private theorem confTree_mem_of_parts (facts : Record.Facts M) (st : M.S) {C W : Block V}
    (hC : C ∈ st.T) (hF : Block.Preceq st.F C)
    (hW : W ∈ st.T) (hCW : Block.Preceq C W) (hh : st.h_max - 1 ≤ (st.σ W).h)
    (hroot : Block.Preceq (M.get_fg_root (M.toHealing st).toFG) C) :
    C ∈ Restated.Vocabulary.Protocol.confTree M st := by
  unfold Restated.Vocabulary.Protocol.confTree
  refine facts.fc.mem_get_filtered_block_tree_of_parts (M.toHealing st) ?_ ?_ ?_ hCW ?_ hroot
  · rw [facts.sto.toHealing_T]; exact hC
  · rw [facts.sto.ModelProperties_toHealing_F]; exact hF
  · rw [facts.sto.toHealing_T]; exact hW
  · rw [facts.sto.ModelProperties_toHealing_h_max, facts.sto.ModelProperties_toHealing_σ]
    exact hh

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Under its premises on the execution and the phase ending at `tE`, with the invariant `hinv` at a
    round `r` at or after the switch round with anchor `T` and the condition `hcross`: if `v_1`
    holds `B` among its bodies after `m` steps and is honest through step `m`, `x[m].time` is at or
    after `tGAT` and `x[m].time + Δ < S.a (r + 1) − 1`, `T` is an ancestor of `B`, `n'` is the tick
    step at `S.a (r + 1)`, `v` is in `HonRound S Sched (r + 1)`, and the ticks named by `hneTick`
    have an outcome, then for every outcome `c` of `v`'s phase tick at the opening slot's
    confirmation instant and every SG root `A` the confirmation read can start from under `c`'s
    grade contract, every descendant of `A` other than `A` that is an ancestor of `B`'s erasure is
    in the tree the confirmation walk descends. -/
theorem confAnchorChainInTree_at_honRound_ofHolder (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE) (hcs : Restated.committeeSleepinessW M S Sched tE)
    {r : Round} {n : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r) (hinv : Restated.AfterPhaseInvariantOverActiveSetsTop M S Sched x r n T)
    (hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x r n'' T)
    {B : NamedBlock V} {v_1 : V} {m : Nat} (hBv_1 : B ∈ (x[m][v_1].st).st.bodies)
    (hv_1 : Restated.HonestThrough M Sched x m v_1) (hm : tGAT ≤ (x[m].time : Int))
    (hdeadline : (x[m].time : Int) + S.E.Δ < (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) - 1)
    (hTB : Block.Preceq T.erase B.erase)
    {n' : Nat} (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    {v : V} (hv : v ∈ Restated.HonRound M S Sched (r + 1))
    (hneTick : ∀ (n'' : Nat) (t' : Int),
      Restated.tickStepAt M x n'' t' → t' % S.E.Δ = 0 → v ∈ Sched.awake t' \ Sched.adv t' → t' ≤ Restated.Vocabulary.Execution.Setup.a M S (r + 1) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched t' x[n''] v) t' ⇢ out) :
    ∀ c : M.Cache, M.onPhaseTick S.E S.hc (M.toHealing (x[n'][v].st).st.core)
        (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1)))) (x[n'][v].st).cache ⇢ c →
    ∀ A : Block V, Restated.Vocabulary.Protocol.confAnchorWith M (M.gradeContract c) S.E S.hc
        (Restated.confStoreAt M S (x[n'][v].st) ((M.opening_slot S.hc (r + 1)))) ⇢ A →
    ∀ C : Block V, Block.Preceq A C → C ≠ A → Block.Preceq C B.erase →
      C ∈ Restated.Vocabulary.Protocol.confTree M (Restated.confStoreAt M S (x[n'][v].st) ((M.opening_slot S.hc (r + 1)))) := by
  intro c hc A hA C hAC _ hCB
  have hd := S.E.Δ_pos
  have hd1 : (1 : Int) ≤ S.E.Δ := hd
  have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  have hRd : 12 * S.E.Δ ≤ 4 * (S.hc.R : Int) * S.E.Δ := by nlinarith
  have hsucc := facts.gr.action_succ_eq_add_rounds S r
  have hfin := Restated.fin_old_anchor_before_succ_tick_of_hypotheses facts (hcross := hcross) S Sched x tE
    hexec hmono tGAT gap hgst hlen hthird hphase hrsW hr hinv hn'
  have hhm := Restated.hMax_le_anchor_succ_before_succ_tick_of_hypotheses facts S Sched x tE hexec hmono
    tGAT gap hgst hlen hthird hphase hrsW hr hinv hn'
  obtain ⟨hn'1, hn'0⟩ := Restated.tickStepAt_time facts x hn'
  have htn : (x[n'].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) := by
    rw [← hn'1]; exact Restated.time_mono_int facts S Sched x (Nat.le_succ n')
  have hvadv : v ∉ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) := (Finset.mem_sdiff.1 hv).2
  have hvn : Restated.HonestThrough M Sched x n' v := fun t ht hin =>
    hvadv (hmono t _ (le_trans ht htn) hin)
  have hwaw : v ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)) - 1 - 2 * S.E.Δ) ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)) - 1) :=
    Restated.awakeThroughout_sub_of_mem_honRound facts hv (by linarith) (by linarith)
  have hchain := fun (X : Block V) (hX : Block.Preceq X B.erase) =>
    Restated.chain_in_reader_tree_of_holder facts S Sched x hexec hsync hmult htd hmono (tR := (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) - 1)
      hgst hcv hphase hthird hcs (Restated.delta_le_of_healingLengthη facts S hlen) hBv_1 hv_1 hm
      (fun v_2 d hd' hv_2d => preceq_trans_Preceq
        (hfin v_2 d (Restated.le_tick_of_time_lt_action facts S Sched x hn' hd') hv_2d) hTB)
      hdeadline le_rfl (by linarith) hvn hwaw hX
      (fun n'' t' hn'' hΔ hq _ ht' => hneTick n'' t' hn'' hΔ hq (le_trans ht' htn))
  obtain ⟨hCmem, -⟩ := hchain C hCB
  obtain ⟨hBT, -⟩ := hchain B.erase (Proofs.ModelProperties.Preceq_self _)
  have hBlog : Restated.blockInLog M S Sched x B := Restated.blockInLog_of_mem_bodies facts S Sched hv_1 hBv_1
  have hBb : B ∈ (x[n'][v].st).st.bodies :=
    Restated.mem_bodies_of_mem_T_honest facts S Sched x hexec hvn hBlog hBT
  have hco : Restated.Vocabulary.Proofs.NamedStore.Coherent M (Setup.alwaysAwake S).E (Setup.alwaysAwake S).cfg
      (x[n'][v].st).st := (Restated.nodeInvariant_sts facts S Sched x n' v).1.1.1
  have hσ : (x[n'][v].st).st.core.σ B.erase = M.derive_named S.E S.cfg B :=
    hco.2.2.2.2 B hBb
  have hTBh : (M.derive_named S.E S.cfg T).h ≤ (M.derive_named S.E S.cfg B).h :=
    facts.cs.derive_height_mono S.E S.cfg
      (Restated.namedPreceq_of_blockInLog facts S Sched x hexec.idealization hinv.inPlay hBlog hTB)
  have hh : (x[n'][v].st).st.core.h_max - 1 ≤ ((x[n'][v].st).st.core.σ B.erase).h := by
    rw [hσ]
    exact Nat.sub_le_iff_le_add.mpr (le_trans (hhm v n' le_rfl) (Nat.succ_le_succ hTBh))
  have hF : Block.Preceq (x[n'][v].st).st.core.F C :=
    preceq_trans_Preceq (Restated.confAnchor_F_preceq facts S Sched x n' v _ c hc A hA) hAC
  have hroot := preceq_trans_Preceq
    (Restated.confAnchor_fgRoot_preceq facts S (x[n'][v].st) _ c hc A hA) hAC
  have hcs : Restated.confStoreAt M S (x[n'][v].st) ((M.opening_slot S.hc (r + 1))) =
      (M.ns_setClock S.E (x[n'][v].st).st
        (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1))))).core := rfl
  refine confTree_mem_of_parts facts _ ?_ ?_ (W := B.erase) ?_ hCB ?_ hroot
  · rw [hcs, facts.hd.Sts_setClock_core_T]; exact hCmem
  · rw [hcs, facts.hd.setClock_core_F]; exact hF
  · rw [hcs, facts.hd.Sts_setClock_core_T]; exact hBT
  · rw [hcs, facts.hd.setClock_core_h_max, facts.hd.Sts_setClock_core_σ]; exact hh

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Under its premises on the execution and the phase ending at `tE`, with the invariant `hinv` at a
    round `r` at or after the switch round with anchor `T` and the conditions `hcross` and `hjust`:
    if `v_1` is in `HonRound S Sched r`, its round-`r` attestation `a` is in the sent log
    `x[n + 1].sent` and names as confirmed the block `C` among `v_1`'s bodies after `n + 1` steps,
    `T` is an ancestor of `C`, `n'` is the tick step at `S.a (r + 1)`, `v` is in
    `HonRound S Sched (r + 1)`, the ticks named by `hneTick` and `hneAtt` have an outcome, and `c`
    is an outcome of `v`'s phase tick at the opening slot's confirmation instant, then every SG root
    the confirmation read can start from under `c`'s grade contract lies on one chain with `C`. -/
theorem confAnchor_compatible_at_honRound_ofFreshSG (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE) (hcs : Restated.committeeSleepinessW M S Sched tE)
    {r : Round} {n : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r) (hinv : Restated.AfterPhaseInvariantOverActiveSetsTop M S Sched x r n T)
    (hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x r n'' T)
    (hjust : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepJustifiedRootUnderAnchor M S Sched x r n n'' T)
    {v_1 : V} (hv_1 : v_1 ∈ Restated.HonRound M S Sched r) {a : NamedAttestation V}
    (ha : a.round = r) (hav : a.val_index = v_1)
    (hsent : (⟨v_1, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n + 1].sent)
    {C : NamedBlock V} (hC : C ∈ (x[n + 1][v_1].st).st.bodies) (hconf : a.confirmed = some C.root)
    (hTC : Block.Preceq T.erase C.erase)
    {n' : Nat} (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    {v : V} (hv : v ∈ Restated.HonRound M S Sched (r + 1))
    (hneTick : ∀ w ∈ Restated.HonRound M S Sched (r + 1), ∀ (n'' : Nat) (t' : Int),
      Restated.tickStepAt M x n'' t' → t' % S.E.Δ = 0 → w ∈ Sched.awake t' \ Sched.adv t' → t' ≤ Restated.Vocabulary.Execution.Setup.a M S (r + 1) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched t' x[n''] w) t' ⇢ out)
    (hneAtt : ∀ v_2 ∈ Restated.HonRound M S Sched r, ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v_2 (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S r) x[n] v_2) (Restated.Vocabulary.Execution.Setup.a M S r) ⇢ out)
    (c : M.Cache) (hc : M.onPhaseTick S.E S.hc (M.toHealing (x[n'][v].st).st.core)
      (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1)))) (x[n'][v].st).cache ⇢ c)
    (hrecvR : Restated.NextRoundReceipts M S Sched x r) :
    ∀ A, Restated.Vocabulary.Protocol.confAnchorWith M (M.gradeContract c) S.E S.hc
        (Restated.confStoreAt M S (x[n'][v].st) ((M.opening_slot S.hc (r + 1)))) ⇢ A →
      Block.compatible A C.erase = true := by
  have hround := Restated.round_of_confStoreAt_opening_slot facts S (x[n'][v].st) (r + 1)
  have hct := Restated.confirmation_time_opening_slot facts S (r + 1)
  have hn'' : Restated.tickStepAt M x n' (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1)))) := by
    rw [hct]; exact hn'
  have htn : (x[n'].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) := by
    rw [← (Restated.tickStepAt_time facts x hn').1]
    exact Restated.time_mono_int facts S Sched x (Nat.le_succ n')
  have hvadv : v ∉ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) := (Finset.mem_sdiff.1 hv).2
  have hvn : Restated.HonestThrough M Sched x n' v := fun t ht hin =>
    hvadv (hmono t _ (le_trans ht htn) hin)
  refine Restated.confAnchor_compatible_of_parts facts S (x[n'][v].st) _ c hc ?_ ?_ ?_
  · intro root hroot
    obtain ⟨m, B, hm, hB, hpre⟩ :=
      Restated.confFrame_g1_provenance facts S Sched x hn'' v root c hc hroot
    rw [hround] at hm hB
    obtain ⟨b, hb⟩ := facts.gr.gradeBool_nonempty S.E (M.gradeView (M.toHealing (x[m][v].st).st.core))
      (x[m][v].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) .g1)
      (M.late S.E S.hc (r + 1) .g1) B
    have hbt := hB b hb
    subst hbt
    obtain ⟨v_2, hv_2, a', ha', hav', hsent', G, hG, hconf', hBG⟩ :=
      Restated.graded_preceq_freshSG_of_premises (hrecvR := hrecvR) facts S Sched x tE hexec hmono htd hsync hmult tGAT
        gap hgst hlen hcv hthird hphase hrsW hcs hr hinv hcross hv (facts.gr.domain_le_action S (r + 1) .g1)
        hm B hb hneTick hneAtt
    have hGC : Block.compatible G.erase C.erase = true :=
      hinv.sgPairwise v_2 hv_2 v_1 hv_1 a' a ha' hav' hsent' ha hav hsent G C hG hconf' hC hconf
    exact Protocol.compatible_of_preceq_of_compatible (preceq_trans_Preceq hpre hBG) hGC
  · exact compatible_of_preceq_common_Preceq
      (preceq_trans_Preceq
        (Restated.fin_old_anchor_before_succ_tick_of_hypotheses facts (hcross := hcross) S Sched x tE
          hexec hmono tGAT gap hgst hlen hthird hphase hrsW hr hinv hn' v n' le_rfl hvn) hTC)
      (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _))
  · exact fun hroot => compatible_of_preceq_common_Preceq
      (preceq_trans_Preceq
        (Restated.justified_old_anchor_before_succ_tick_of_hypotheses facts (hjust := hjust) S Sched x tE
          hexec hmono tGAT gap hgst hlen hthird hphase hrsW hr hinv hn' v n'
          (Restated.tick_succ_le_tick_succ_round facts S Sched x hinv.tick hn') le_rfl hvn hroot) hTC)
      (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _))

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Under its premises on the execution and the phase ending at `tE`, with the invariant `hinv` at a
    round `r` at or after the switch round with anchor `T`, and the conditions `hcross` and `hjust`: if `n'` is the tick step at `S.a (r + 1)`, `v_1` is in
    `HonRound S Sched r`, its round-`r` attestation `a` is in the sent log `x[n + 1].sent` and names
    as confirmed the block `C` among `v_1`'s bodies after `n + 1` steps, every honest active member
    of the committee of round `r + 1`'s opening slot votes for a descendant of `C` when `C` is a
    strict descendant of `T`, `v` is in `HonRound S Sched (r + 1)`, and the ticks named by
    `hneTickVote`, `hneTick`, `hneTickW` and `hneAtt` have an outcome, then `C` lies on one chain
    with the confirmed block of every store `v`'s round-`(r + 1)` action read can give. -/
theorem freshSG_compatible_live_confirmed_of_openingHeads (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE) (hcs : Restated.committeeSleepinessW M S Sched tE)
    {r : Round} {n : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r) (hinv : Restated.AfterPhaseInvariantOverActiveSetsTop M S Sched x r n T)
    (hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x r n'' T)
    (hjust : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepJustifiedRootUnderAnchor M S Sched x r n n'' T)
    {n' : Nat} (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    {v_1 : V} (hv_1 : v_1 ∈ Restated.HonRound M S Sched r) {a : NamedAttestation V}
    (ha : a.round = r) (hav : a.val_index = v_1)
    (hsent : (⟨v_1, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n + 1].sent)
    {C : NamedBlock V} (hC : C ∈ (x[n + 1][v_1].st).st.bodies) (hconf : a.confirmed = some C.root)
    (hheads : Block.Preceq T.erase C.erase → C.erase ≠ T.erase →
      Restated.HeadsBelow M S Sched x C.erase ((M.opening_slot S.hc (r + 1))))
    {v : V} (hv : v ∈ Restated.HonRound M S Sched (r + 1))
    (hneTickVote : ∀ s : Slot, (M.opening_slot S.hc r) + 2 ≤ s → s ≤ (M.opening_slot S.hc (r + 1)) →
      ∀ m : Nat, Restated.tickStepAt M x m (M.vote_time S.E s) →
      ∀ q ∈ Restated.HonSlot M S Sched s, ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) q (Record.wakeStage M Sched (M.vote_time S.E s) x[m] q) (M.vote_time S.E s) ⇢ out)
    (hneTick : ∀ s : Slot, (M.opening_slot S.hc r) + 2 ≤ s → s ≤ (M.opening_slot S.hc (r + 1)) →
      ∀ w ∈ Restated.HonSlot M S Sched (s + 1), ∀ (n'' : Nat) (t' : Int),
      Restated.tickStepAt M x n'' t' → t' % S.E.Δ = 0 → w ∈ Sched.awake t' \ Sched.adv t' → t' ≤ Restated.Vocabulary.Execution.Setup.a M S (r + 1) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched t' x[n''] w) t' ⇢ out)
    (hneTickW : ∀ w ∈ Restated.HonRound M S Sched (r + 1), ∀ (n'' : Nat) (t' : Int),
      Restated.tickStepAt M x n'' t' → t' % S.E.Δ = 0 → w ∈ Sched.awake t' \ Sched.adv t' → t' ≤ Restated.Vocabulary.Execution.Setup.a M S (r + 1) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched t' x[n''] w) t' ⇢ out)
    (hneAtt : ∀ v_2 ∈ Restated.HonRound M S Sched r, ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v_2 (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S r) x[n] v_2) (Restated.Vocabulary.Execution.Setup.a M S r) ⇢ out)
    (hrecvR : Restated.NextRoundReceipts M S Sched x r) :
    ∀ hs ∈ Restated.actionHealingStore M S (x[n'][v].st) (r + 1),
      Block.compatible C.erase hs.live_confirmed = true := by
  intro hs hhs
  have hd := S.E.Δ_pos
  have hd1 : (1 : Int) ≤ S.E.Δ := hd
  have hold := Restated.confirmedOld_at_honRound (hrecvR := hrecvR) facts (hcross := hcross) (hjust := hjust) S Sched x tE
    hexec hmono htd hsync hmult hcom tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hinv hn' hv
    hneTickVote hneTick (hneTickW v hv) hneAtt hs hhs
  have hsg := hinv.sg v_1 hv_1 a ha hav hsent C hC hconf
  rcases compatible_cases hsg with hCT | hTC
  · -- `C` is an ancestor of `T`
    have hold' := hold
    rcases compatible_cases hold' with hLT | hTL
    · exact compatible_of_preceq_common_Preceq hCT hLT
    · exact compatible_of_preceq_common_Preceq (preceq_trans_Preceq hCT hTL) (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _))
  · by_cases hCeq : C.erase = T.erase
    · rw [hCeq]; exact compatible_symm_l3 hold
    · -- `C` is a strict descendant of `T`
      obtain ⟨t', ht'E, ht's, ht'len, hcs'⟩ :=
        Restated.exists_cone_cutoff facts S Sched tE hmono hcom tGAT gap hgst hlen hphase hcs hr
      have hRs : (M.opening_slot S.hc r) + 2 ≤ (M.opening_slot S.hc (r + 1)) := by
        refine two_le_of_three_le_l3 _ _ ?_
        rw [facts.gr.opening_slot_succ]; exact Nat.add_le_add_left S.hc.R_ge_three _
      have hsE : t' ≤ slotStart S.E.Δ ((M.opening_slot S.hc (r + 1))) :=
        le_trans ht's (slotStart_mono S hRs)
      have hfin := Restated.fin_old_anchor_before_succ_tick_of_hypotheses facts (hcross := hcross) S Sched x
        tE hexec hmono tGAT gap hgst hlen hthird hphase hrsW hr hinv hn'
      have htn : (x[n'].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) := by
        rw [← (Restated.tickStepAt_time facts x hn').1]; exact Restated.time_mono_int facts S Sched x (Nat.le_succ n')
      have hvadv : v ∉ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) := (Finset.mem_sdiff.1 hv).2
      have hvn : Restated.HonestThrough M Sched x n' v := fun t ht hin =>
        hvadv (hmono t _ (le_trans ht htn) hin)
      have hsR : M.support_cutoff S.E ((M.opening_slot S.hc (r + 1))) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) - 1 := by
        have e1 : M.support_cutoff S.E ((M.opening_slot S.hc (r + 1)))
            = slotStart S.E.Δ ((M.opening_slot S.hc (r + 1))) + 2 * S.E.Δ :=
          support_cutoff_eq_of_pos facts S.E (pos_of_add_two_le_l3 _ _ hRs)
        have e2 : M.confirmation_time S.E ((M.opening_slot S.hc (r + 1)))
            = slotStart S.E.Δ ((M.opening_slot S.hc (r + 1))) + 6 * S.E.Δ := (facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E _).symm
        rw [Restated.confirmation_time_opening_slot facts S (r + 1)] at e2
        linarith
      obtain ⟨hn1, -⟩ := Restated.tickStepAt_time facts x hinv.tick
      have hv_1adv : v_1 ∉ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S r)) := (Finset.mem_sdiff.1 hv_1).2
      have hv_1h : Restated.HonestThrough M Sched x (n + 1) v_1 := fun t ht hin =>
        hv_1adv (hmono t _ (by rw [← hn1]; exact ht) hin)
      have hopen : M.opening S.E S.hc r ≤ Restated.Vocabulary.Execution.Setup.a M S r := by
        show _ ≤ M.a S.hc S.E.Δ r
        rw [facts.gr.opening_eq_proposal_time, facts.sch.a_eq_confirmation_time]
        exact facts.sch.proposal_time_le_confirmation_time _ _
      have htGAT : tGAT ≤ (Restated.Vocabulary.Execution.Setup.a M S r) :=
        le_trans (Restated.tGAT_le_switchOpening facts S tGAT tE gap hgst hlen)
          (le_trans (Restated.switchOpening_le_opening facts S hr) hopen)
      have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
      have hRd : 12 * S.E.Δ ≤ 4 * (S.hc.R : Int) * S.E.Δ := by nlinarith
      have hsucc := facts.gr.action_succ_eq_add_rounds S r
      obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc (M.toHealing (x[n'][v].st).st.core)
        (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1)))) (x[n'][v].st).cache
      obtain ⟨A, hA0⟩ := facts.fc.get_sg_root_with_nonempty (M.gradeContract c) S.E S.hc
        (M.toHealing (Restated.confStoreAt M S (x[n'][v].st) ((M.opening_slot S.hc (r + 1)))))
        (M.round_of S.hc (Restated.confStoreAt M S (x[n'][v].st) ((M.opening_slot S.hc (r + 1)))).s)
      have hA : Restated.Vocabulary.Protocol.confAnchorWith M (M.gradeContract c) S.E S.hc
          (Restated.confStoreAt M S (x[n'][v].st) ((M.opening_slot S.hc (r + 1)))) ⇢ A := by
        unfold Restated.Vocabulary.Protocol.confAnchorWith; exact hA0
      have hpath := Restated.confAnchorChainInTree_at_honRound_ofHolder facts S Sched x tE hexec hmono
        htd hsync hmult tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hinv hcross hC hv_1h
        (by rw [hn1]; exact htGAT) (by rw [hn1]; linarith) hTC hn' hv (hneTickW v hv) c hc A hA
      have hAB := Restated.confAnchor_compatible_at_honRound_ofFreshSG (hrecvR := hrecvR) facts S Sched x tE hexec hmono
        htd hsync hmult tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hinv hcross hjust hv_1 ha hav
        hsent hC hconf hTC hn' hv hneTickW hneAtt c hc A hA
      have hF : Block.Preceq hs.F C.erase := by
        rw [Restated.actionHealingStore_F facts S _ _ hs hhs]
        exact preceq_trans_Preceq (hfin v n' le_rfl hvn) hTC
      have hJ : hs.h_max = hs.h_j + 1 → Block.compatible hs.J C.erase = true := by
        intro hroot
        rw [Restated.actionHealingStore_h_max facts S _ _ hs hhs,
          Restated.actionHealingStore_h_j facts S _ _ hs hhs] at hroot
        rw [Restated.actionHealingStore_J facts S _ _ hs hhs]
        exact compatible_of_preceq_common_Preceq
          (preceq_trans_Preceq
            (Restated.justified_old_anchor_before_succ_tick_of_hypotheses facts (hjust := hjust) S Sched x
              tE hexec hmono tGAT gap hgst hlen hthird hphase hrsW hr hinv hn' v n'
              (Restated.tick_succ_le_tick_succ_round facts S Sched x hinv.tick hn') le_rfl hvn hroot) hTC)
          (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _))
      have hL := Restated.live_confirmed_compatible_at_action_afterPhase_ofCompatible facts S Sched x
        hexec hsync hmult htd hmono hgst hcv (fun t h1 h2 => hphase t h1 (le_trans h2 ht'E))
        (fun t h => hthird t (le_trans h ht'E)) hcs' ht'len (T := C)
        (Restated.deliveredDescendant_mono facts S Sched x
          (Restated.deliveredDescendantUnderFinalized_anchor facts S Sched x hn' hfin tGAT) hTC)
          (Restated.finalizedPreceqAtSteps_mono facts S Sched x
          (Restated.finalizedPreceqAtSteps_anchor facts S Sched x hn' hfin tGAT) hTC)
        hsE hsR hn' hv (hheads hTC hCeq) c hc A hA hAB hpath hs hhs hF hJ
        (hneTickVote _ hRs le_rfl)
        (fun n'' t' hn'' hΔ hq ht' =>
          hneTickW v hv n'' t' hn'' hΔ hq (le_of_le_of_eq ht' (Restated.confirmation_time_opening_slot facts S (r + 1))))
      exact compatible_symm_l3 hL

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Under its premises on the execution and the phase ending at `tE`, with the invariant `hinv` at a
    round `r` at or after the switch round with anchor `T`, and the conditions `hcross` and `hjust`: if `n'` is the tick step at `S.a (r + 1)`, every block `C` that a
    member of `HonRound S Sched r` names as confirmed in its round-`r` attestation and that is a
    strict descendant of `T` has every honest active member of the committee of round `r + 1`'s
    opening slot voting for a descendant of it, and the ticks named by `hneTickVote`, `hneTick`,
    `hneTickW` and `hneAtt` have an outcome, then
    `ConfirmedCompatibleFreshSGOverHonRound S Sched x r n n'` holds. -/
theorem confirmedCompatibleFreshSG_of_openingHeads (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE) (hcs : Restated.committeeSleepinessW M S Sched tE)
    {r : Round} {n : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r) (hinv : Restated.AfterPhaseInvariantOverActiveSetsTop M S Sched x r n T)
    (hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x r n'' T)
    (hjust : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepJustifiedRootUnderAnchor M S Sched x r n n'' T)
    {n' : Nat} (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (hheads : ∀ v_1 ∈ Restated.HonRound M S Sched r, ∀ a : NamedAttestation V,
      a.round = r → a.val_index = v_1 →
      (⟨v_1, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n + 1].sent →
      ∀ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies → a.confirmed = some C.root →
      Block.Preceq T.erase C.erase → C.erase ≠ T.erase →
      Restated.HeadsBelow M S Sched x C.erase ((M.opening_slot S.hc (r + 1))))
    (hneTickVote : ∀ s : Slot, (M.opening_slot S.hc r) + 2 ≤ s → s ≤ (M.opening_slot S.hc (r + 1)) →
      ∀ m : Nat, Restated.tickStepAt M x m (M.vote_time S.E s) →
      ∀ q ∈ Restated.HonSlot M S Sched s, ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) q (Record.wakeStage M Sched (M.vote_time S.E s) x[m] q) (M.vote_time S.E s) ⇢ out)
    (hneTick : ∀ s : Slot, (M.opening_slot S.hc r) + 2 ≤ s → s ≤ (M.opening_slot S.hc (r + 1)) →
      ∀ w ∈ Restated.HonSlot M S Sched (s + 1), ∀ (n'' : Nat) (t' : Int),
      Restated.tickStepAt M x n'' t' → t' % S.E.Δ = 0 → w ∈ Sched.awake t' \ Sched.adv t' → t' ≤ Restated.Vocabulary.Execution.Setup.a M S (r + 1) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched t' x[n''] w) t' ⇢ out)
    (hneTickW : ∀ w ∈ Restated.HonRound M S Sched (r + 1), ∀ (n'' : Nat) (t' : Int),
      Restated.tickStepAt M x n'' t' → t' % S.E.Δ = 0 → w ∈ Sched.awake t' \ Sched.adv t' → t' ≤ Restated.Vocabulary.Execution.Setup.a M S (r + 1) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched t' x[n''] w) t' ⇢ out)
    (hneAtt : ∀ v_2 ∈ Restated.HonRound M S Sched r, ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v_2 (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S r) x[n] v_2) (Restated.Vocabulary.Execution.Setup.a M S r) ⇢ out)
    (hrecvR : Restated.NextRoundReceipts M S Sched x r) :
    Restated.ConfirmedCompatibleFreshSGOverHonRound M S Sched x r n n' :=
  fun _ hv v_1 hv_1 a ha hav hsent C hC hconf =>
    Restated.freshSG_compatible_live_confirmed_of_openingHeads (hrecvR := hrecvR) facts S Sched x tE hexec hmono htd hsync hmult
      hcom tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hinv hcross hjust hn' hv_1 ha hav
      hsent hC hconf (hheads v_1 hv_1 a ha hav hsent C hC hconf) hv hneTickVote hneTick hneTickW hneAtt

end

end DecoupledConsensusModel.Sts.Restated
