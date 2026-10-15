import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bK_ConeAnchor
import Proofs.Claims.Restated.Claim13bK_FinBeforeTick
import Proofs.Claims.Restated.Claim13bK_FreshAttestersW
import Proofs.Claims.Restated.Claim13bK_GradeLateUpTo
import Proofs.Claims.Restated.Claim13bK_GradeOld
import Proofs.Claims.Restated.Claim13bK_GradeOldHeads
import Proofs.Claims.Restated.Claim13bK_GradeOldHeadsUpTo
import Proofs.Claims.Restated.Claim13bPhaseSleepiness
import Proofs.Claims.Restated.Claim13bStepAssembly
import Proofs.Claims.Restated.Claim13bStepCone
import Proofs.Claims.Restated.Claim13bStepConeIter
import Proofs.Claims.Restated.Claim13bStepGrade
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13beRoute3_3
import Proofs.Claims.Restated.CommonViewOfFinalizedDescendantsFacts
import Proofs.Claims.Restated.Projection
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bInvariantActiveTop
import Model.Conditions.Claim13bK_ConeSlots
import Model.Conditions.Claim13bK_FgJustified
import Model.Conditions.Claim13bK_FinBeforeTick
import Model.Conditions.Claim13bK_FreshAttestersW
import Model.Conditions.Claim13bK_GradeOldHeads
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13bStepAssembly
import Model.Conditions.Claim13bStepCone
import Model.Conditions.Claim13bStepKitTick
import Model.Conditions.ClaimAsyncK_DeliveryUpTo
import Model.Conditions.CommonViewOfFinalizedDescendantsFacts
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring
import Proofs.Claims.Restated.WakeWindow
import Proofs.Claims.Restated.Claim13bK_ConeAnchorUpToRecv
import Proofs.Claims.Restated.Claim13bK_GradeLateRecv

/-!
# The SG root of a vote walk lies on one chain with the anchor, synchrony up to a bound

Over a model `M : Record.Model V`, with synchrony assumed only up to a bound: `ConeAnchorCompatible`
at the round-`r` anchor for the honest active committee members of round `r`'s later slots and of
round `r + 1`'s opening slot and the slot after it.
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

/-- If synchrony from wake holds for every send whose deadline is at or before `b'`, and `b ≤ b'`,
    then it holds for every send whose deadline is at or before `b`. -/
private theorem synchronyFromWakeBefore_mono {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (Record.protocolOf M S) Sched} {b b' : Int} (hb : b ≤ b')
    (hs : Restated.SynchronyFromWakeBefore M S x b') : Restated.SynchronyFromWakeBefore M S x b :=
  fun k w sm hsend hle haw => hs k w sm hsend (le_trans hle hb) haw

/-- Synchrony before `b` alone: with GST at or before `S.a r` and `S.a r + Δ ≤ b`, a validator `v`
    awake from `S.a r` to a time `t₁` at or after `S.a r + Δ` receives round `r`'s honest attestations
    strictly before round `r + 1`'s first cutoff of phase `p`. -/
theorem receives_of_awake_from_action_before (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {b : Int}
    (hsync : Restated.SynchronyFromWakeBefore M S x b) {r : Round} {v : V} {t₁ : Int}
    (p : Protocol.Phase) (hgst : S.E.t_GST ≤ Restated.Vocabulary.Execution.Setup.a M S r)
    (hb : Restated.Vocabulary.Execution.Setup.a M S r + S.E.Δ ≤ b)
    (haw : v ∈ Sched.awakeThroughout (Restated.Vocabulary.Execution.Setup.a M S r) t₁)
    (ht₁ : Restated.Vocabulary.Execution.Setup.a M S r + S.E.Δ ≤ t₁) :
    Restated.ReceivesRoundAttestationsBefore M S Sched x r v (M.early S.E S.hc (r + 1) p) := by
  intro k w a hk hsend _ _
  obtain ⟨h1, h0⟩ := Restated.tickStepAt_time facts x hk
  have hk0 : (x[k].time : Int) = Restated.Vocabulary.Execution.Setup.a M S r - 1 := by linarith
  have hmax : max (x[k].time : Int) S.E.t_GST + S.E.Δ ≤
      Restated.Vocabulary.Execution.Setup.a M S r + S.E.Δ := by
    have : max (x[k].time : Int) S.E.t_GST ≤ Restated.Vocabulary.Execution.Setup.a M S r :=
      max_le (by rw [hk0]; linarith) hgst
    linarith
  have haw' : v ∈ Sched.awakeThroughout (x[k + 1].time : Int)
      (max (x[k].time : Int) S.E.t_GST + S.E.Δ) := by
    rw [h1]; exact awakeThroughout_mono Sched haw le_rfl (le_trans hmax ht₁)
  obtain ⟨d, hkd, hl, -, hlt⟩ := hsync k v _ hsend (le_trans hmax hb) haw'
  exact ⟨d, hkd, hl, lt_of_lt_of_le hlt (le_trans hmax (le_trans (Restated.action_delta_le_early_succ facts S r)
    (Restated.early_g2_le_early facts S (r + 1) p)))⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- With synchrony only up to `S.a (r + 1)`: if round `r` is at or after the switch round, the
    invariant holds at round `r` with anchor `T`, and slot `s + 1` is round `r + 1`'s opening slot
    or the slot after it, then the SG root every honest active member of slot `(s + 1)`'s committee
    starts its vote walk from lies on one chain with `T`. The hypotheses `hneTick` and `hneAtt` ask
    for tick outcomes as in `grade1_compatible_at_awakeReader_upTo`, `hneTick` at every such member. -/
theorem coneAnchorCompatible_at_opening_slots_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
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
    (hjust : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepJustifiedRootUnderAnchor M S Sched x r n n'' T)
    {s : Slot} {j : Nat} (hj : j ≤ 1) (hs : s + 1 = (M.opening_slot S.hc (r + 1)) + j)
    (hneTick : ∀ v ∈ Restated.HonSlot M S Sched (s + 1), ∀ (n' : Nat) (t' : Int),
      Restated.tickStepAt M x n' t' → t' % S.E.Δ = 0 → v ∈ Sched.awake t' \ Sched.adv t' → t' ≤ Restated.Vocabulary.Execution.Setup.a M S (r + 1) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched t' x[n'] v) t' ⇢ out)
    (hneAtt : ∀ v_1 ∈ Restated.HonRound M S Sched r, ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v_1 (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S r) x[n] v_1) (Restated.Vocabulary.Execution.Setup.a M S r) ⇢ out) :
    Restated.ConeAnchorCompatible M S x T.erase s := by
  have hd := S.E.Δ_pos
  have hd1 : (1 : Int) ≤ S.E.Δ := hd
  have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  have hRd : 12 * S.E.Δ ≤ 4 * (S.hc.R : Int) * S.E.Δ := by nlinarith
  have hsucc := facts.gr.action_succ_eq_add_rounds S r
  have hj' : (j : Int) ≤ 1 := by exact_mod_cast hj
  have hj0 : (0 : Int) ≤ (j : Int) := by exact_mod_cast Nat.zero_le j
  have hvt : M.vote_time S.E (s + 1) = (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) - 5 * S.E.Δ + 4 * S.E.Δ * (j : Int) := by
    rw [hs]; exact Restated.vote_time_opening_slot_add facts S (r + 1) j
  have hjd : 4 * S.E.Δ * (j : Int) ≤ 4 * S.E.Δ := by nlinarith
  have hjd0 : 0 ≤ 4 * S.E.Δ * (j : Int) := by positivity
  have hround : (M.round_of S.hc (s + 1)) = r + 1 := by
    rw [hs]; exact facts.gr.round_of_opening_slot_add S.hc (r + 1) (by have := S.hc.R_ge_three; omega)
  have hdomEq : M.domain S.E S.hc (r + 1) .g1 + 5 * S.E.Δ
      ≤ Restated.Vocabulary.Execution.Setup.a M S (r + 1) :=
    facts.gr.domain_add_five_delta_le_action S (r + 1) .g1
  have hdom : M.domain S.E S.hc (r + 1) .g1 ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) := facts.gr.domain_le_action S (r + 1) .g1
  refine Restated.coneAnchorCompatible_of_voteReads facts S x ?_
    (Restated.voteFinJustCompatible_of_before_succ_tick facts (hcross := hcross) (hjust := hjust) S Sched x tE hexec hmono htd tGAT gap hgst hlen
      hthird hphase hrsW hr hinv (by rw [hvt]; linarith) (by rw [hvt]; linarith))
  intro v mr hv hmr nr hnr root hroot
  obtain ⟨m, B, hm, hB, hpre⟩ := Restated.voteFrame_g1_provenance facts S Sched x hmr v root hnr hroot
  rw [hround] at hm hB
  -- the voter's awake window
  have hact := ((Restated.mem_HonSlot facts).mp hv).1
  have hwin : v ∈ Sched.awakeThroughout (M.vote_time S.E (s + 1) - wVote S)
      (M.vote_time S.E (s + 1)) := by
    rw [← facts.sch.slotStart_add_delta_eq_vote_time S.E (s + 1)]; exact hact
  have hwv : wVote S = 4 * (S.hc.R : Int) * S.E.Δ + 2 * S.E.Δ := by
    unfold wVote; ring
  have hawT : v ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S r)) (M.domain S.E S.hc (r + 1) .g1) :=
    awakeThroughout_mono Sched hwin (by rw [hvt, hwv]; linarith)
      (by rw [hvt]; linarith)
  have hvS : v ∉ Sched.adv (M.domain S.E S.hc (r + 1) .g1) := by
    intro hin
    refine ((Restated.mem_HonSlot facts).mp hv).2.2 (hmono _ _ ?_ hin)
    have e : M.confirmation_time S.E (s + 1)
        = M.vote_time S.E (s + 1) + 5 * S.E.Δ := by
      have h1 := facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E (s + 1)
      have h2 := facts.sch.slotStart_add_delta_eq_vote_time S.E (s + 1)
      linarith
    rw [e, hvt]; linarith
  obtain ⟨b, hb⟩ := facts.gr.gradeBool_nonempty S.E (M.gradeView (M.toHealing (x[m][v].st).st.core))
    (x[m][v].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) .g1) (M.late S.E S.hc (r + 1) .g1) B
  have hbt := hB b hb
  subst hbt
  have hlo := facts.gr.action_delta_le_early S S.hc.R_ge_three (Nat.lt_succ_self r)
  have h21 := facts.gr.early_g2_add_delta_le_early_g1 S (r + 1)
  have he0 := facts.gr.early_g1_add_delta_le_early_g0 S (r + 1)
  have hl0 := facts.gr.early_le_late S.E S.hc (r + 1) .g0
  have hl1 := facts.gr.late_g0_add_delta_le_late_g1 S (r + 1)
  have ht₀ : Restated.Vocabulary.Execution.Setup.a M S r ≤ M.late S.E S.hc (r + 1) .g1 - 1 - 2 * S.E.Δ := by
    show M.a S.hc S.E.Δ r ≤ _
    linarith
  have hgstr : S.E.t_GST ≤ Restated.Vocabulary.Execution.Setup.a M S r :=
    Restated.gst_le_action_of_switchRound_le facts S tGAT tE gap hgst hlen hr
  have hadom := Restated.action_delta_lt_domain_succ facts S r .g1
  have hrecv := receives_of_awake_from_action_before facts S Sched x hsync .g1 hgstr
    (le_of_lt (lt_of_lt_of_le hadom hdom)) hawT (le_of_lt hadom)
  have hBT := Restated.grade1_compatible_at_awakeReader_upTo_recv facts (hcross := hcross) S Sched x tE hexec hmono htd
    (synchronyFromWakeBefore_mono (le_trans (facts.gr.late_le_domain S (r + 1) .g1) hdom) hsync)
    hmult tGAT gap
    hgst hlen hcv hthird hphase hrsW hcs hr hinv hdom _ ht₀ hawT hrecv hvS hm B hb (hneTick v hv) hneAtt
  exact Protocol.compatible_of_preceq_of_compatible hpre hBT

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- With synchrony only up to `S.a (r + 1)`: if round `r` is at or after the switch round, the
    invariant holds at round `r` with anchor `T`, then
    `ConeAnchorCompatible` holds at `T` for every slot `s` from round `r`'s third slot to round
    `r + 1`'s opening slot. The hypotheses `hneTick` and `hneAtt` ask for tick outcomes as in
    `coneAnchorCompatible_at_opening_slots_upTo`, `hneTick` at the committee members of every slot
    of the range. -/
theorem coneAnchorCompatible_range_at_anchor_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
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
    (hjust : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepJustifiedRootUnderAnchor M S Sched x r n n'' T)
    (hneTick : ∀ s : Slot, (M.opening_slot S.hc r) + 2 ≤ s → s ≤ (M.opening_slot S.hc (r + 1)) →
      ∀ v ∈ Restated.HonSlot M S Sched (s + 1), ∀ (n' : Nat) (t' : Int),
      Restated.tickStepAt M x n' t' → t' % S.E.Δ = 0 → v ∈ Sched.awake t' \ Sched.adv t' → t' ≤ Restated.Vocabulary.Execution.Setup.a M S (r + 1) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched t' x[n'] v) t' ⇢ out)
    (hneAtt : ∀ v_1 ∈ Restated.HonRound M S Sched r, ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v_1 (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S r) x[n] v_1) (Restated.Vocabulary.Execution.Setup.a M S r) ⇢ out) :
    ∀ s : Slot, (M.opening_slot S.hc r) + 2 ≤ s → s ≤ (M.opening_slot S.hc (r + 1)) →
      Restated.ConeAnchorCompatible M S x T.erase s := by
  intro s hs0 hs1
  have hneS := hneTick s hs0 hs1
  rw [facts.gr.opening_slot_succ] at hs1
  rcases slot_cases_aux _ _ _ hs0 hs1 with ⟨j, hj, hj3, hjR, hlo3, hlast⟩ | ⟨j, hj, hsj⟩
  · -- round `r`'s slots: `s + 1 = opening_slot r + j` with `3 ≤ j ≤ R - 1`
    have hd := S.E.Δ_pos
    have hj3' : (3 : Int) ≤ (j : Int) := by exact_mod_cast hj3
    have hjR' : (j : Int) + 1 ≤ (S.hc.R : Int) := by exact_mod_cast hjR
    have hvt : M.vote_time S.E (s + 1) = (Restated.Vocabulary.Execution.Setup.a M S r) - 5 * S.E.Δ + 4 * S.E.Δ * (j : Int) := by
      rw [hj]; exact Restated.vote_time_opening_slot_add facts S r j
    have hsucc := facts.gr.action_succ_eq_add_rounds S r
    have h1 : 12 * S.E.Δ ≤ 4 * S.E.Δ * (j : Int) := by nlinarith
    have h2 : 4 * S.E.Δ * (j : Int) + 4 * S.E.Δ ≤ 4 * (S.hc.R : Int) * S.E.Δ := by nlinarith
    have hgr1 : Restated.VoteGradeOneCompatible M S x T.erase s := by
      intro v mr hv hmr nr hnr root hroot
      obtain ⟨m, B, hm, hBall, hpre⟩ := Restated.voteFrame_g1_provenance facts S Sched x hmr v root hnr hroot
      have hround : (M.round_of S.hc (s + 1)) = r := by
        rw [hj]; exact facts.gr.round_of_opening_slot_add S.hc r hjR
      rw [hround] at hm hBall
      have hv' : v ∈ Restated.HonSlot M S Sched ((M.opening_slot S.hc r) + j) := by rw [← hj]; exact hv
      have hvP : v ∈ Restated.grade1PerformersW M S Sched r :=
        Finset.mem_sdiff.2 (Restated.awakeThroughout_grade1_window_of_mem_honSlot facts S Sched hmono hjR hv')
      obtain ⟨b, hb⟩ := facts.gr.gradeBool_nonempty S.E (M.gradeView (M.toHealing (x[m][v].st).st.core))
        (x[m][v].st).st.core.F S.hc.η_SG r (M.early S.E S.hc r .g1) (M.late S.E S.hc r .g1) B
      exact Protocol.compatible_of_preceq_of_compatible hpre
        (hinv.grade1Performers v hvP m hm B b hb (hBall b hb))
    exact Restated.coneAnchorCompatible_of_voteReads facts S x hgr1
      (Restated.voteFinJustCompatible_of_before_succ_tick facts (hcross := hcross) (hjust := hjust) S Sched x tE hexec hmono htd tGAT gap hgst hlen
        hthird hphase hrsW hr hinv (by rw [hvt]; linarith) (by rw [hvt]; linarith))
  · exact Restated.coneAnchorCompatible_at_opening_slots_upTo facts (hcross := hcross) (hjust := hjust) S Sched x tE hexec hmono htd hsync hmult tGAT gap
      hgst hlen hcv hthird hphase hrsW hcs hr hinv hj (by rw [facts.gr.opening_slot_succ]; exact hsj)
      hneS hneAtt

end

end DecoupledConsensusModel.Sts.Restated
