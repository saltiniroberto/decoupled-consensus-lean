import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bK_ConeAnchor
import Proofs.Claims.Restated.Claim13bK_ConeAnchorUpTo
import Proofs.Claims.Restated.Claim13bK_ConeChain
import Proofs.Claims.Restated.Claim13bK_ConeChainUpTo
import Proofs.Claims.Restated.Claim13bK_ConeSlotsUpTo
import Proofs.Claims.Restated.Claim13bK_ConfirmedOld
import Proofs.Claims.Restated.Claim13bK_FgJustified
import Proofs.Claims.Restated.Claim13bK_FinBeforeTick
import Proofs.Claims.Restated.Claim13bK_GradeOld
import Proofs.Claims.Restated.Claim13bK_GradeOldHeads
import Proofs.Claims.Restated.Claim13bStepActionF
import Proofs.Claims.Restated.Claim13bStepConeIter
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13beRoute3_5
import Proofs.Claims.Restated.ProcessIdempotent
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bInvariantActiveTop
import Model.Conditions.Claim13bK_FgJustified
import Model.Conditions.Claim13bK_FinBeforeTick
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13bStepCone
import Model.Conditions.Claim13bStepConeIter
import Model.Conditions.Claim13bStepSG
import Model.Conditions.Claim13beRoute3_7
import Model.Conditions.ClaimAsyncK_DeliveryUpTo
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
import Proofs.Claims.Restated.Claim13bW_ReceiptBefore

/-!
# Confirmed blocks on one chain with the anchor, with synchrony up to the action instant

The anchor chains in the voter and confirmation trees, the honest heads of the next round's opening
slot, and an honest attester's confirmed block at the next round's action read, from the switch
round on, with synchrony assumed only up to round `r + 1`'s action instant. Stated over a model
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
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If `a + 3 ≤ b` then `b − 1 + 1 = b`. -/
private theorem pred_succ_of_three_le_nat (a b : Nat) (h : a + 3 ≤ b) : b - 1 + 1 = b := by
  omega

/-- If `a + 3 ≤ b` then `a + 2 ≤ b`. -/
private theorem two_le_of_three_le_nat (a b : Nat) (h : a + 3 ≤ b) : a + 2 ≤ b := by omega

/-- If `s ≤ b − 1` then `s ≤ b`. -/
private theorem le_of_le_pred_nat (s b : Nat) (h : s ≤ b - 1) : s ≤ b := by omega

/-- If `a + 2 ≤ s` then `0 < s`. -/
private theorem pos_of_add_two_le_nat (a s : Nat) (h : a + 2 ≤ s) : 0 < s := by omega

/-- If `a + 3 ≤ b` then `0 < b − 1`. -/
private theorem pred_pos_of_add_three_le_nat (a b : Nat) (h : a + 3 ≤ b) : 0 < b - 1 := by omega

/-- Synchrony from wake up to `b'` gives synchrony from wake up to every `b ≤ b'`. -/
private theorem synchronyFromWakeBefore_mono {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (Record.protocolOf M S) Sched} {b b' : Int} (hb : b ≤ b')
    (hs : Restated.SynchronyFromWakeBefore M S x b') : Restated.SynchronyFromWakeBefore M S x b :=
  fun k w sm hsend hle haw => hs k w sm hsend (le_trans hle hb) haw

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

/-- For a positive slot `s`, `support_cutoff s = slotStart s + 2Δ`. -/
private theorem support_cutoff_eq_of_pos (facts : Record.Facts M) (E : Env V) {s : Slot}
    (hs : 0 < s) : M.support_cutoff E s = slotStart E.Δ s + 2 * E.Δ := by
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, (Nat.succ_pred_eq_of_pos hs).symm⟩
  rw [← facts.sch.confirmation_time_eq_support_cutoff_succ,
    ← facts.sch.slotStart_add_six_delta_eq_confirmation_time, slotStart_succ]
  ring

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- With synchrony up to `S.a (r + 1)`, under its premises on the execution and the phase ending at
    `tE`, with the invariant `hinv` at a round `r` at or after the switch round with anchor `T`, the
    condition `hcross`, `committeeSleepinessW` from the start of the slot two after round `r`'s
    opening slot, and the ticks named by `hneTickW` having an outcome: `ConeAnchorChainInTree` holds
    for `T`'s erasure at every slot from two after round `r`'s opening slot to round `r + 1`'s
    opening slot. -/
theorem coneAnchorChainInTree_at_anchor_of_committee_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    {r : Round} (hsync : Restated.SynchronyFromWakeBefore M S x ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (hmult : AwakeAtMultiples S Sched)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE) (hcs : Restated.committeeSleepinessW M S Sched tE)
    {n : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r) (hinv : Restated.AfterPhaseInvariantOverActiveSetsTop M S Sched x r n T)
    (hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x r n'' T)
    (hcs2 : Restated.committeeSleepinessW M S Sched (slotStart S.E.Δ ((M.opening_slot S.hc r) + 2)))
    (hneTickW : ∀ s : Slot, (M.opening_slot S.hc r) + 2 ≤ s → s ≤ (M.opening_slot S.hc (r + 1)) →
      ∀ w ∈ Restated.HonSlot M S Sched (s + 1), ∀ (n' : Nat) (t' : Int),
      Restated.tickStepAt M x n' t' → t' % S.E.Δ = 0 → w ∈ Sched.awake t' \ Sched.adv t' → t' < M.vote_time S.E (s + 1) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched t' x[n'] w) t' ⇢ out) :
    ∀ s : Slot, (M.opening_slot S.hc r) + 2 ≤ s → s ≤ (M.opening_slot S.hc (r + 1)) →
      Restated.ConeAnchorChainInTree M S x T.erase s := by
  intro s hs0 hs1
  have hd := S.E.Δ_pos
  obtain ⟨v₀, m₀, hTbody, hv₀h, hm₀, hm₀t⟩ :=
    Restated.exists_anchor_holder_of_committee facts S Sched x tE hexec hmono htd tGAT gap hgst hlen hr hinv
      hcs2
  have hmo := slotStart_mono S hs0
  have hss : slotStart S.E.Δ ((M.opening_slot S.hc r) + 2) = (Restated.Vocabulary.Execution.Setup.a M S r) + 2 * S.E.Δ := by
    have e := Restated.vote_time_opening_slot_add facts S r 2
    have e2 : M.vote_time S.E ((M.opening_slot S.hc r) + 2) = slotStart S.E.Δ ((M.opening_slot S.hc r) + 2) + S.E.Δ :=
      (facts.sch.slotStart_add_delta_eq_vote_time S.E ((M.opening_slot S.hc r) + 2)).symm
    push_cast at e
    linarith
  have hvf : slotStart S.E.Δ s + 2 * S.E.Δ < M.view_freeze S.E s := by
    rw [← support_cutoff_eq_of_pos facts S.E (pos_of_add_two_le_nat _ _ hs0)]
    exact facts.sch.Sts_support_cutoff_lt_view_freeze S.E s
  exact Restated.coneAnchorChainInTree_of_holder_upTo facts (hcross := hcross) S Sched x tE hexec hmono htd hsync hmult tGAT gap hgst
    hlen hcv hthird hphase hrsW hcs hr hinv hTbody hv₀h hm₀ (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _))
    le_rfl (by linarith) (Nat.succ_le_succ hs1) (hneTickW s hs0 hs1)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- With synchrony up to `S.a (r + 1)`, under its premises on the execution and the phase ending at
    `tE`, with the invariant `hinv` at a round `r` at or after the switch round with anchor `T`, the
    condition `hcross` and `committeeSleepinessW` from the start of the slot two after round `r`'s
    opening slot: if `n'` is the tick step at `S.a (r + 1)`, `v` is in `HonRound S Sched (r + 1)`
    and the ticks named by `hneTick` have an outcome, then for every outcome `c` of `v`'s phase tick
    at the opening slot's confirmation instant and every SG root `A` the confirmation read can start
    from under `c`'s grade contract, every descendant of `A` other than `A` that is an ancestor of
    `T`'s erasure is in the tree the confirmation walk descends. -/
theorem confAnchorChainInTree_at_honRound_of_committee_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    {r : Round} (hsync : Restated.SynchronyFromWakeBefore M S x ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (hmult : AwakeAtMultiples S Sched)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE) (hcs : Restated.committeeSleepinessW M S Sched tE)
    {n : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r) (hinv : Restated.AfterPhaseInvariantOverActiveSetsTop M S Sched x r n T)
    (hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x r n'' T)
    (hcs2 : Restated.committeeSleepinessW M S Sched (slotStart S.E.Δ ((M.opening_slot S.hc r) + 2)))
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
    ∀ C : Block V, Block.Preceq A C → C ≠ A → Block.Preceq C T.erase →
      C ∈ Restated.Vocabulary.Protocol.confTree M (Restated.confStoreAt M S (x[n'][v].st) ((M.opening_slot S.hc (r + 1)))) := by
  intro c hc A hA C hAC _ hCT
  have hd := S.E.Δ_pos
  have hd1 : (1 : Int) ≤ S.E.Δ := hd
  have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  have hRd : 12 * S.E.Δ ≤ 4 * (S.hc.R : Int) * S.E.Δ := by nlinarith
  have hsucc := facts.gr.action_succ_eq_add_rounds S r
  obtain ⟨v₀, m₀, hTbody, hv₀h, hm₀, hm₀t⟩ :=
    Restated.exists_anchor_holder_of_committee facts S Sched x tE hexec hmono htd tGAT gap hgst hlen hr hinv
      hcs2
  have hfin := Restated.fin_old_anchor_before_succ_tick_of_hypotheses facts (hcross := hcross) S Sched x tE hexec hmono tGAT gap
    hgst hlen hthird hphase hrsW hr hinv hn'
  have hhm := Restated.hMax_le_anchor_succ_before_succ_tick_of_hypotheses facts S Sched x tE hexec hmono tGAT
    gap hgst hlen hthird hphase hrsW hr hinv hn'
  obtain ⟨hn'1, hn'0⟩ := Restated.tickStepAt_time facts x hn'
  have htn : (x[n'].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) := by
    rw [← hn'1]; exact Restated.time_mono_int facts S Sched x (Nat.le_succ n')
  have hvadv : v ∉ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) := (Finset.mem_sdiff.1 hv).2
  have hvn : Restated.HonestThrough M Sched x n' v := fun t ht hin =>
    hvadv (hmono t _ (le_trans ht htn) hin)
  have hwaw : v ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)) - 1 - 2 * S.E.Δ) ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)) - 1) :=
    Restated.awakeThroughout_sub_of_mem_honRound facts hv (by linarith) (by linarith)
  have hchain := fun (X : Block V) (hX : Block.Preceq X T.erase) =>
    Restated.chain_in_reader_tree_of_holder_upTo facts S Sched x hexec
      (synchronyFromWakeBefore_mono (b := (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) - 1) (by linarith) hsync)
      hmult htd hmono (tR := (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) - 1)
      hgst hcv hphase hthird hcs (Restated.delta_le_of_healingLengthη facts S hlen) hTbody hv₀h hm₀
      (fun v_1 d hd' hv_1d => hfin v_1 d (Restated.le_tick_of_time_lt_action facts S Sched x hn' hd') hv_1d)
      (by linarith) le_rfl (by linarith) hvn hwaw hX
      (fun n'' t' hn'' hΔ hq _ ht' => hneTick n'' t' hn'' hΔ hq (le_trans ht' htn))
  obtain ⟨hCmem, -⟩ := hchain C hCT
  obtain ⟨hTT, -⟩ := hchain T.erase (Proofs.ModelProperties.Preceq_self _)
  have hTb : T ∈ (x[n'][v].st).st.bodies :=
    Restated.mem_bodies_of_mem_T_honest facts S Sched x hexec hvn hinv.inPlay hTT
  have hco : Restated.Vocabulary.Proofs.NamedStore.Coherent M (Setup.alwaysAwake S).E (Setup.alwaysAwake S).cfg
      (x[n'][v].st).st := (Restated.nodeInvariant_sts facts S Sched x n' v).1.1.1
  have hσ : (x[n'][v].st).st.core.σ T.erase = M.derive_named S.E S.cfg T :=
    hco.2.2.2.2 T hTb
  have hh : (x[n'][v].st).st.core.h_max - 1 ≤ ((x[n'][v].st).st.core.σ T.erase).h := by
    rw [hσ]; exact Nat.sub_le_iff_le_add.mpr (hhm v n' le_rfl)
  have hF : Block.Preceq (x[n'][v].st).st.core.F C :=
    preceq_trans_Preceq (Restated.confAnchor_F_preceq facts S Sched x n' v _ c hc A hA) hAC
  have hroot := preceq_trans_Preceq
    (Restated.confAnchor_fgRoot_preceq facts S (x[n'][v].st) _ c hc A hA) hAC
  have hcs : Restated.confStoreAt M S (x[n'][v].st) ((M.opening_slot S.hc (r + 1))) =
      (M.ns_setClock S.E (x[n'][v].st).st
        (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1))))).core := rfl
  refine confTree_mem_of_parts facts _ ?_ ?_ (W := T.erase) ?_ hCT ?_ hroot
  · rw [hcs, facts.hd.ModelProperties_setClock_core_T]; exact hCmem
  · rw [hcs, facts.hd.setClock_core_F]; exact hF
  · rw [hcs, facts.hd.ModelProperties_setClock_core_T]; exact hTT
  · rw [hcs, facts.hd.setClock_core_h_max, facts.hd.ModelProperties_setClock_core_σ]; exact hh

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- With synchrony up to `S.a (r + 1)`, under its premises on the execution and the phase ending at
    `tE`, with the invariant `hinv` at a round `r` at or after the switch round with anchor `T`, the conditions `hcross` and `hjust`, and the ticks named by `hneTickVote`,
    `hneTick` and `hneAtt` having an outcome: every honest active member of the committee of round
    `r + 1`'s opening slot votes for a descendant of `T`'s erasure. -/
theorem headsBelow_succ_opening_slot_at_anchor_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    {r : Round} (hsync : Restated.SynchronyFromWakeBefore M S x ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (hmult : AwakeAtMultiples S Sched)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE) (hcs : Restated.committeeSleepinessW M S Sched tE)
    {n : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r) (hinv : Restated.AfterPhaseInvariantOverActiveSetsTop M S Sched x r n T)
    (hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x r n'' T)
    (hjust : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepJustifiedRootUnderAnchor M S Sched x r n n'' T)
    {n' : Nat} (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (hneTickVote : ∀ s : Slot, (M.opening_slot S.hc r) + 2 ≤ s → s ≤ (M.opening_slot S.hc (r + 1)) →
      ∀ m : Nat, Restated.tickStepAt M x m (M.vote_time S.E s) →
      ∀ q ∈ Restated.HonSlot M S Sched s, ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) q (Record.wakeStage M Sched (M.vote_time S.E s) x[m] q) (M.vote_time S.E s) ⇢ out)
    (hneTick : ∀ s : Slot, (M.opening_slot S.hc r) + 2 ≤ s → s ≤ (M.opening_slot S.hc (r + 1)) →
      ∀ v ∈ Restated.HonSlot M S Sched (s + 1), ∀ (n'' : Nat) (t' : Int),
      Restated.tickStepAt M x n'' t' → t' % S.E.Δ = 0 → v ∈ Sched.awake t' \ Sched.adv t' → t' ≤ Restated.Vocabulary.Execution.Setup.a M S (r + 1) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched t' x[n''] v) t' ⇢ out)
    (hneAtt : ∀ v_1 ∈ Restated.HonRound M S Sched r, ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v_1 (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S r) x[n] v_1) (Restated.Vocabulary.Execution.Setup.a M S r) ⇢ out) :
    Restated.HeadsBelow M S Sched x T.erase ((M.opening_slot S.hc (r + 1))) := by
  have hd := S.E.Δ_pos
  have hd1 : (1 : Int) ≤ S.E.Δ := hd
  have hvtle : ∀ s : Slot, s ≤ (M.opening_slot S.hc (r + 1)) →
      M.vote_time S.E (s + 1) ≤ Restated.Vocabulary.Execution.Setup.a M S (r + 1) := by
    intro s hs
    have h1 := facts.sch.vote_time_mono S.E (Nat.succ_le_succ hs)
    have h2 := facts.sch.slotStart_add_delta_eq_vote_time S.E ((M.opening_slot S.hc (r + 1)) + 1)
    have h3 := slotStart_succ S.E.Δ (M.opening_slot S.hc (r + 1))
    have h4 := facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E (M.opening_slot S.hc (r + 1))
    rw [Restated.confirmation_time_opening_slot facts S (r + 1)] at h4
    linarith
  obtain ⟨t', ht'E, ht's, ht'len, hcs'⟩ :=
    Restated.exists_cone_cutoff facts S Sched tE hmono hcom tGAT gap hgst hlen hphase hcs hr
  have hcs2 := Restated.committeeSleepinessW_at_heads_slot facts S Sched tE hmono hcom tGAT gap hgst hlen hphase
    hcs hr
  have hfin := Restated.fin_old_anchor_before_succ_tick_of_hypotheses facts (hcross := hcross) S Sched x tE hexec hmono tGAT gap
    hgst hlen hthird hphase hrsW hr hinv hn'
  have hRs : (M.opening_slot S.hc r) + 3 ≤ (M.opening_slot S.hc (r + 1)) := by
    rw [facts.gr.opening_slot_succ]; exact Nat.add_le_add_left S.hc.R_ge_three _
  have hs1 : (M.opening_slot S.hc (r + 1)) - 1 + 1 = (M.opening_slot S.hc (r + 1)) :=
    pred_succ_of_three_le_nat _ _ hRs
  have hsR : M.support_cutoff S.E ((M.opening_slot S.hc (r + 1)) - 1) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) - 1 := by
    have e1 : M.support_cutoff S.E ((M.opening_slot S.hc (r + 1)) - 1) = slotStart S.E.Δ ((M.opening_slot S.hc (r + 1)) - 1) + 2 * S.E.Δ :=
      support_cutoff_eq_of_pos facts S.E (pred_pos_of_add_three_le_nat _ _ hRs)
    have e2 : slotStart S.E.Δ ((M.opening_slot S.hc (r + 1)))
        = slotStart S.E.Δ ((M.opening_slot S.hc (r + 1)) - 1) + 4 * S.E.Δ := by
      conv_lhs => rw [← hs1]
      exact slotStart_succ S.E.Δ _
    have e3 : M.confirmation_time S.E ((M.opening_slot S.hc (r + 1))) = slotStart S.E.Δ ((M.opening_slot S.hc (r + 1))) + 6 * S.E.Δ :=
      (facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E ((M.opening_slot S.hc (r + 1)))).symm
    rw [Restated.confirmation_time_opening_slot facts S (r + 1)] at e3
    rw [e1]
    linarith
  have hrange := Restated.headsBelow_range_afterPhase_upTo (hr1 := Restated.one_le_round_of_of_opening_slot_le facts S (r := r)
      (le_trans (Restated.one_le_switchRound facts S tGAT tE gap hgst hlen) hr) (Nat.le_add_right _ 2)) facts S Sched x hexec
    (s₀ := (M.opening_slot S.hc r) + 2) (s₁ := (M.opening_slot S.hc (r + 1)) - 1)
    (synchronyFromWakeBefore_mono (by linarith) hsync) hmult htd hmono hgst hcv
    (fun t h1 h2 => hphase t h1 (le_trans h2 ht'E))
    (fun t h => hthird t (le_trans h ht'E)) hcs' ht'len
    (Restated.deliveredDescendantUnderFinalized_anchor facts S Sched x hn' hfin tGAT)
    (Restated.finalizedPreceqAtSteps_anchor facts S Sched x hn' hfin tGAT)
    (Nat.succ_pos _) ht's hsR
    (fun s h0 h1 => Restated.coneAnchorCompatible_range_at_anchor_upTo facts (hcross := hcross) (hjust := hjust) S Sched x tE hexec hmono htd hsync hmult
      tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hinv hneTick hneAtt s h0 (le_of_le_pred_nat _ _ h1))
    (fun s h0 h1 => Restated.coneAnchorChainInTree_at_anchor_of_committee_upTo facts (hcross := hcross) S Sched x tE hexec hmono htd
      hsync hmult tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hinv hcs2
      (fun s' h0' h1' w hw' n'' t' hn'' hΔ hq ht' =>
        hneTick s' h0' h1' w hw' n'' t' hn'' hΔ hq (le_trans (le_of_lt ht') (hvtle s' h1')))
      s h0 (le_of_le_pred_nat _ _ h1))
    hinv.heads
    (fun s h0 h1 => hneTickVote s h0 (le_of_le_pred_nat _ _ h1))
    (fun s h0 h1 w hw' n'' t' hn'' hΔ hq ht' =>
      hneTick s h0 (le_of_le_pred_nat _ _ h1) w hw' n'' t' hn'' hΔ hq
        (le_trans (le_of_lt ht') (hvtle s (le_of_le_pred_nat _ _ h1))))
  exact hrange _ (two_le_of_three_le_nat _ _ hRs) (le_of_eq hs1.symm)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- With synchrony up to `S.a (r + 1)`, under its premises on the execution and the phase ending at
    `tE`, with the invariant `hinv` at a round `r` at or after the switch round with anchor `T`, and the conditions `hcross` and `hjust`: if `n'` is the tick step at
    `S.a (r + 1)`, `v` is in `HonRound S Sched (r + 1)`, and the ticks named by `hneTickVote`,
    `hneTick`, `hneTickv` and `hneAtt` have an outcome, then the confirmed block of every store
    `v`'s round-`(r + 1)` action read can give lies on one chain with `T`'s erasure. -/
theorem confirmedOld_at_honRound_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    {r : Round} (hsync : Restated.SynchronyFromWakeBefore M S x ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)))) (hcatchB : Restated.CatchUpOnWakeBefore M S x ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (hmult : AwakeAtMultiples S Sched)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE) (hcs : Restated.committeeSleepinessW M S Sched tE)
    {n : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r) (hinv : Restated.AfterPhaseInvariantOverActiveSetsTop M S Sched x r n T)
    (hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x r n'' T)
    (hjust : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepJustifiedRootUnderAnchor M S Sched x r n n'' T)
    {n' : Nat} (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    {v : V} (hv : v ∈ Restated.HonRound M S Sched (r + 1))
    (hneTickVote : ∀ s : Slot, (M.opening_slot S.hc r) + 2 ≤ s → s ≤ (M.opening_slot S.hc (r + 1)) →
      ∀ m : Nat, Restated.tickStepAt M x m (M.vote_time S.E s) →
      ∀ q ∈ Restated.HonSlot M S Sched s, ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) q (Record.wakeStage M Sched (M.vote_time S.E s) x[m] q) (M.vote_time S.E s) ⇢ out)
    (hneTick : ∀ s : Slot, (M.opening_slot S.hc r) + 2 ≤ s → s ≤ (M.opening_slot S.hc (r + 1)) →
      ∀ v ∈ Restated.HonSlot M S Sched (s + 1), ∀ (n'' : Nat) (t' : Int),
      Restated.tickStepAt M x n'' t' → t' % S.E.Δ = 0 → v ∈ Sched.awake t' \ Sched.adv t' → t' ≤ Restated.Vocabulary.Execution.Setup.a M S (r + 1) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched t' x[n''] v) t' ⇢ out)
    (hneTickv : ∀ (n'' : Nat) (t' : Int),
      Restated.tickStepAt M x n'' t' → t' % S.E.Δ = 0 → v ∈ Sched.awake t' \ Sched.adv t' → t' ≤ Restated.Vocabulary.Execution.Setup.a M S (r + 1) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched t' x[n''] v) t' ⇢ out)
    (hneAtt : ∀ v_1 ∈ Restated.HonRound M S Sched r, ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v_1 (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S r) x[n] v_1) (Restated.Vocabulary.Execution.Setup.a M S r) ⇢ out) :
    ∀ hs ∈ Restated.actionHealingStore M S (x[n'][v].st) (r + 1),
      Block.compatible hs.live_confirmed T.erase = true := by
  have hrecvR : Restated.NextRoundReceipts M S Sched x r :=
    Restated.nextRoundReceipts_of_before facts S Sched x hsync hcatchB
      (Restated.gst_le_action_of_switchRound_le facts S tGAT tE gap hgst hlen hr)
      (by have := Restated.early_g1_le_action_rb facts S (r + 1); have := S.E.Δ_pos; linarith)
  intro hs hhs
  have hd := S.E.Δ_pos
  have hd1 : (1 : Int) ≤ S.E.Δ := hd
  obtain ⟨t', ht'E, ht's, ht'len, hcs'⟩ :=
    Restated.exists_cone_cutoff facts S Sched tE hmono hcom tGAT gap hgst hlen hphase hcs hr
  have hcs2 := Restated.committeeSleepinessW_at_heads_slot facts S Sched tE hmono hcom tGAT gap hgst hlen hphase
    hcs hr
  have hRs : (M.opening_slot S.hc r) + 2 ≤ (M.opening_slot S.hc (r + 1)) := by
    refine two_le_of_three_le_nat _ _ ?_
    rw [facts.gr.opening_slot_succ]; exact Nat.add_le_add_left S.hc.R_ge_three _
  have hsE : t' ≤ slotStart S.E.Δ ((M.opening_slot S.hc (r + 1))) :=
    le_trans ht's (slotStart_mono S hRs)
  have hfin := Restated.fin_old_anchor_before_succ_tick_of_hypotheses facts (hcross := hcross) S Sched x tE hexec hmono tGAT gap
    hgst hlen hthird hphase hrsW hr hinv hn'
  have htn : (x[n'].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) := by
    rw [← (Restated.tickStepAt_time facts x hn').1]; exact Restated.time_mono_int facts S Sched x (Nat.le_succ n')
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc (M.toHealing (x[n'][v].st).st.core)
    (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1)))) (x[n'][v].st).cache
  obtain ⟨A, hA0⟩ := facts.fc.get_sg_root_with_nonempty (M.gradeContract c) S.E S.hc
    (M.toHealing (Restated.confStoreAt M S (x[n'][v].st) ((M.opening_slot S.hc (r + 1)))))
    (M.round_of S.hc (Restated.confStoreAt M S (x[n'][v].st) ((M.opening_slot S.hc (r + 1)))).s)
  have hA : Restated.Vocabulary.Protocol.confAnchorWith M (M.gradeContract c) S.E S.hc
      (Restated.confStoreAt M S (x[n'][v].st) ((M.opening_slot S.hc (r + 1)))) ⇢ A := by
    unfold Restated.Vocabulary.Protocol.confAnchorWith; exact hA0
  have hvadv : v ∉ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) := (Finset.mem_sdiff.1 hv).2
  have hvn : Restated.HonestThrough M Sched x n' v := fun t ht hin =>
    hvadv (hmono t _ (le_trans ht htn) hin)
  have hsR : M.support_cutoff S.E ((M.opening_slot S.hc (r + 1))) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) - 1 := by
    have e1 : M.support_cutoff S.E ((M.opening_slot S.hc (r + 1))) = slotStart S.E.Δ ((M.opening_slot S.hc (r + 1))) + 2 * S.E.Δ :=
      support_cutoff_eq_of_pos facts S.E (pos_of_add_two_le_nat _ _ hRs)
    have e2 : M.confirmation_time S.E ((M.opening_slot S.hc (r + 1))) = slotStart S.E.Δ ((M.opening_slot S.hc (r + 1))) + 6 * S.E.Δ :=
      (facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E ((M.opening_slot S.hc (r + 1)))).symm
    rw [Restated.confirmation_time_opening_slot facts S (r + 1)] at e2
    linarith
  have hF : Block.Preceq hs.F T.erase := by
    rw [Restated.actionHealingStore_F facts S _ _ hs hhs]; exact hfin v n' le_rfl hvn
  have hJ : hs.h_max = hs.h_j + 1 → Block.compatible hs.J T.erase = true := by
    intro hroot
    rw [Restated.actionHealingStore_h_max facts S _ _ hs hhs,
      Restated.actionHealingStore_h_j facts S _ _ hs hhs] at hroot
    rw [Restated.actionHealingStore_J facts S _ _ hs hhs]
    exact Block.compatible_of_preceq_common
      (preceq_eq_true_iff_Preceq.mpr <| Restated.justified_old_anchor_before_succ_tick_of_hypotheses facts (hjust := hjust) S Sched x tE hexec
        hmono tGAT gap hgst hlen hthird hphase hrsW hr hinv hn' v n'
        (Restated.tick_succ_le_tick_succ_round facts S Sched x hinv.tick hn') le_rfl hvn hroot)
      (Block.preceq_self _)
  exact Restated.live_confirmed_compatible_at_action_afterPhase_ofCompatible_upTo facts S Sched x hexec
    (synchronyFromWakeBefore_mono (by linarith) hsync) hmult
    htd hmono hgst hcv (fun t h1 h2 => hphase t h1 (le_trans h2 ht'E))
    (fun t h => hthird t (le_trans h ht'E)) hcs' ht'len
    (Restated.deliveredDescendantUnderFinalized_anchor facts S Sched x hn' hfin tGAT)
    (Restated.finalizedPreceqAtSteps_anchor facts S Sched x hn' hfin tGAT) hsE hsR hn' hv
    (Restated.headsBelow_succ_opening_slot_at_anchor_upTo facts (hcross := hcross) (hjust := hjust) S Sched x tE hexec hmono htd hsync hmult hcom tGAT gap
      hgst hlen hcv hthird hphase hrsW hcs hr hinv hn' hneTickVote hneTick hneAtt)
    c hc A hA
    (Restated.confAnchor_compatible_at_honRound_upTo (hrecvR := hrecvR) facts (hcross := hcross) (hjust := hjust) S Sched x tE hexec hmono htd hsync hmult tGAT gap hgst hlen
      hcv hthird hphase hrsW hcs hr hinv hn' hv hneTickv hneAtt c hc A hA)
    (Restated.confAnchorChainInTree_at_honRound_of_committee_upTo facts (hcross := hcross) S Sched x tE hexec hmono htd hsync hmult tGAT
      gap hgst hlen hcv hthird hphase hrsW hcs hr hinv hcs2 hn' hv hneTickv c hc A hA)
    hs hhs hF hJ
    (hneTickVote _ hRs le_rfl)
    (fun n'' t' hn'' hΔ hq ht' =>
      hneTickv n'' t' hn'' hΔ hq (le_of_le_of_eq ht' (Restated.confirmation_time_opening_slot facts S (r + 1))))

end

end DecoupledConsensusModel.Sts.Restated
