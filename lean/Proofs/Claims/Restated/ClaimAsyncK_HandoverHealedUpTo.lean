import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bK_ConfirmedSettleEarlier
import Proofs.Claims.Restated.Claim13bK_ConfirmedStrongRoundSettle
import Proofs.Claims.Restated.Claim13bK_ConfirmedStrongRoundSettleUpTo
import Proofs.Claims.Restated.Claim13bW_Schedule
import Proofs.Claims.Restated.Claim13beRoute3_85d
import Proofs.Claims.Restated.ClaimAsyncK_AfterFacts
import Proofs.Claims.Restated.ClaimAsyncK_DeliveryUpTo
import Proofs.Claims.Restated.ClaimAsyncK_HandoverCoversUpTo
import Proofs.Claims.Restated.ClaimAsyncK_HandoverRootsUpTo
import Proofs.Claims.Restated.ClaimConfirmedAfterHealingHolds
import Model.Conditions.Claim13bK_ConfirmedWakeUpTo
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.ClaimAsyncK_DeliveryUpTo
import Model.Conditions.ClaimAsyncK_Handover
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Sts_Spec2Claims_ClaimConfirmedAfterHealing
import Model.Conditions.Sts_Spec2Claims_ClaimStableThroughAsyncPeriod
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bK_ConfirmedStrongRoundSettle
import Proofs.Claims.Spec2Claims.Claim13bModel_Preceq
import Proofs.Claims.Spec2Claims.Claim13bK_ConfirmedRecordUpTo
import Proofs.Claims.Spec2Claims.ClaimAsyncK_HandoverCoversUpTo

/-!
# The hand-over from a healed execution

Theorems over a model `M : Record.Model V` with facts `facts : Record.Facts M`: an earlier phase end
at which the healing premises hold and the records are settled
(`settledPremisesAtEarlierEnd_of_healed_upTo`), and the hand-over facts at round `r + 1` with
synchrony suspended on `[b₀, b₁)` (`stableHandover_of_healed_upTo`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

/-- Refers by name to the private closed forms of the module
    `Proofs.Claims.Restated.Claim13bK_ConfirmedStrongRoundSettle`. -/
local macro "pS% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13bK_ConfirmedStrongRoundSettle)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog

/-- On the healing premises with a phase `[tGAT, tE]` of at least `healingLengthη S gap + (gap + 2)`
    periods, and synchrony only up to `max tE (S.a (S.hc.round_of (sEnd - 2) + 1))`, there is a
    phase end `tE' ≤ tE` with `tGAT + healingLengthη S gap + period ≤ tE'` at which the third bound,
    the awake premise, the recurrence of strong openings, the three sleepiness premises and the
    records settled up to `sEnd` all hold. -/
theorem settledPremisesAtEarlierEnd_of_healed_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (gap : Nat)
    (hgap : gap + 2 ≤ S.cfg.K)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tGAT tE : Int)
    (hlen : tGAT + (Restated.healingLengthη M S gap + ((gap : Int) + 2) * (Restated.constants M S).period) ≤ tE)
    (hgst : S.E.t_GST ≤ tGAT) (hmono : Sched.MonotoneCorruption)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {sEnd : Slot}
    (hsync : Restated.SynchronyFromWakeBefore M S x (max tE ((Restated.Vocabulary.Execution.Setup.a M S ((M.round_of S.hc (sEnd - 2)) + 1)))))
    (hmult : AwakeAtMultiples S Sched)
    (hwakes : Restated.WakesAtActionInstants M S Sched) (hsleeps : Restated.SleepsAfterActionInstants M S Sched)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (htd : Restated.TimeDiverges M x) (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    (hsl : sleepinessW S Sched tE) (hrs : Restated.roundSleepinessW M S Sched tE)
    (hcs : Restated.committeeSleepinessW M S Sched tE) :
    ∃ tE' : Int, tE' ≤ tE ∧
      tGAT + (Restated.healingLengthη M S gap + (Restated.constants M S).period) ≤ tE' ∧
      (∀ t : Int, t ≤ tE' →
        3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight) ∧
      (∀ t : Int, tGAT ≤ t → t ≤ tE' → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t) ∧
      Restated.strongOpeningsRecurFrom M S Sched tGAT tE' gap ∧
      sleepinessW S Sched tE' ∧ Restated.roundSleepinessW M S Sched tE' ∧
      Restated.committeeSleepinessW M S Sched tE' ∧
      Restated.RecordsSettledAtSettleTickTo M S Sched x tE' sEnd := by
  have hd : (1 : Int) ≤ S.E.Δ := S.E.Δ_pos
  have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  have hper := Restated.period_eq facts S
  have hηp := Restated.period_le_healingLengthη facts S gap
  have hgst0 : (0 : Int) ≤ tGAT := le_trans S.E.t_GST_nonneg hgst
  set T0 : Int := tGAT + (Restated.healingLengthη M S gap + (Restated.constants M S).period) with hT0
  have hT0Δ : 14 * S.E.Δ ≤ T0 := by
    rw [hper] at hηp
    rw [hT0, hper]
    nlinarith
  set r : Round := Restated.switchRound M S T0 + 1 with hr
  obtain ⟨hTr, hopr⟩ := Restated.round_after_switch_bounds facts S hT0Δ
  rw [← hr] at hTr hopr
  have hstart : tGAT ≤ M.proposal_time S.E ((M.opening_slot S.hc r)) := by
    rw [← facts.gr.opening_eq_proposal_time]
    have h1 := hTr
    rw [(pS% confirmation_time_closed_srs) facts S.E] at h1
    rw [(pS% opening_closed_srs) facts S]
    push_cast at h1 ⊢
    rw [hper] at hηp
    nlinarith
  have hgapper : (gap : Int) * ((Restated.Vocabulary.Execution.Setup.a M S 1) - (Restated.Vocabulary.Execution.Setup.a M S 0)) = (gap : Int) * (Restated.constants M S).period := rfl
  have hwinr : M.proposal_time S.E ((M.opening_slot S.hc r)) + (gap : Int) * ((Restated.Vocabulary.Execution.Setup.a M S 1) - (Restated.Vocabulary.Execution.Setup.a M S 0))
      ≤ tE := by
    rw [← facts.gr.opening_eq_proposal_time, hgapper]
    have : T0 + ((gap : Int) + 1) * (Restated.constants M S).period ≤ tE := by
      rw [hT0]; nlinarith
    nlinarith
  obtain ⟨c, hrc, hcg, hprops, hprev1, -⟩ := Restated.strongWindow_of_recurrence_l85d facts S Sched hrec hstart
    hwinr
  have hc2 : 2 ≤ c := le_trans (Nat.le_add_left 2 r) hrc
  have hopening : S.E.proposer ((M.opening_slot S.hc c)) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c))) :=
    hprops 0 (by decide)
  obtain ⟨h12, h2a, -, -, hwin⟩ := Restated.settle_instants facts S hc2 tGAT gap
  have hlen₁ : T0 ≤ M.confirmation_time S.E ((M.opening_slot S.hc (c - 2)) + 2) := by
    have hrc2 : r ≤ c - 2 := Nat.le_sub_of_add_le hrc
    have hmono' := facts.sch.confirmation_time_mono S
      (Nat.add_le_add_right (facts.gr.opening_slot_mono S hrc2) 2)
    linarith
  have hcE : (Restated.Vocabulary.Execution.Setup.a M S c) ≤ tE := by
    have hca : (Restated.Vocabulary.Execution.Setup.a M S c) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + gap)) := Restated.action_mono facts S hcg
    have hrg : (Restated.Vocabulary.Execution.Setup.a M S (r + gap)) = M.opening S.E S.hc r + (gap : Int) * (Restated.constants M S).period
        + 6 * S.E.Δ := by
      rw [(pS% action_closed_srs) facts S, (pS% opening_closed_srs) facts S, (pS% opening_slot_closed_srs) facts S.hc, hper]
      push_cast
      ring
    have : T0 + ((gap : Int) + 1) * (Restated.constants M S).period ≤ tE := by
      rw [hT0]; nlinarith
    nlinarith
  obtain ⟨-, -, hwin8⟩ := hwin hlen₁
  set tE' : Int := M.confirmation_time S.E ((M.opening_slot S.hc (c - 1)) + 2) with htE'
  have htE' : tE' ≤ tE := le_trans h2a hcE
  have hlen' : tGAT + (Restated.healingLengthη M S gap + (Restated.constants M S).period) ≤ tE' :=
    le_trans hlen₁ (le_of_lt h12)
  have hwin' : tGAT + 8 * (S.hc.R : Int) * S.E.Δ ≤ tE' := le_trans hwin8 (le_of_lt h12)
  have hsettle : Restated.RecordsSettledAtSettleTickTo M S Sched x tE' sEnd :=
    Restated.recordsSettledAtSettleTick_atStrongRound_upTo facts S Sched x tGAT tE gap hgap hgst hmono hexec hsync
      hmult hwakes hsleeps hcv htd hcom hthird hawake hrec hsl hrs hcs hc2 hlen₁ hcE
      hopening hprev1
  exact ⟨tE', htE', hlen', third_of_later S Sched tE tE' htE' hthird,
    awake_of_later Sched tGAT tE tE' htE' hawake,
    Restated.strongOpeningsRecurFrom_of_later facts S Sched tGAT tE tE' gap htE' hrec,
    sleepinessW_of_later S Sched tGAT tE tE' hmono hawake hwin' hsl,
    Restated.roundSleepinessW_of_later facts S Sched tGAT tE tE' hmono hawake hwin' hrs,
    Restated.committeeSleepinessW_of_later facts S Sched tGAT tE tE' hmono hawake hcom hwin' hcs, hsettle⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog

/-- On the healing premises, with the healing phase at least `healingLengthη S gap + (gap + 2)`
    periods long, synchrony and catch-up on wake suspended on `[b₀, b₁)`, and
    `Restated.periodAfterRound M S (r + 1) b₀`: every block that is an ancestor of the stable output
    of an honest validator active at a step between the settle instant and round `r`'s action
    instant satisfies the hand-over facts at round `r + 1`. -/
theorem stableHandover_of_healed_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (gap : Nat)
    (hgap : gap + 2 ≤ S.cfg.K)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tGAT tAwakeEnd b₀ b₁ : Int)
    (hlen : tGAT + (Restated.healingLengthη M S gap + ((gap : Int) + 2) * (Restated.constants M S).period)
      ≤ tAwakeEnd)
    (hgst : S.E.t_GST ≤ tGAT) (hmono : Sched.MonotoneCorruption)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWakeOutside M S x b₀ b₁) (hmult : AwakeAtMultiples S Sched)
    (hwakes : Restated.WakesAtActionInstants M S Sched) (hsleeps : Restated.SleepsAfterActionInstants M S Sched)
    (hcatch : Restated.CatchUpOnWakeOutside M S x b₀ b₁) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (htd : Restated.TimeDiverges M x) (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hthird : ∀ t : Int, t ≤ tAwakeEnd →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tAwakeEnd gap)
    (hsl : sleepinessW S Sched tAwakeEnd) (hrs : Restated.roundSleepinessW M S Sched tAwakeEnd)
    (hcs : Restated.committeeSleepinessW M S Sched tAwakeEnd)
    (r : Nat) (hb₀ : Restated.periodAfterRound M S (r + 1) b₀)
    (v : V) (T : Nat) (P : Block V)
    (hvT : Restated.HonestThrough M Sched x T v)
    (hT : Restated.confirmedSettleTime M S tAwakeEnd ≤ (x[T].time : Int))
    (hTr : (x[T].time : Int) ≤ (M.a S.hc S.E.Δ r))
    (hva : v ∈ activeAtW S Sched (S.E.slotOf (x[T].time : Int)))
    (hP : Block.Preceq P (M.get_stable (x[T][v].st).st.core)) :
    Restated.StableHandover M S Sched x (r + 1) P := by
  have hs0 : Restated.SynchronyFromWakeBefore M S x b₀ := Restated.synchronyFromWakeBefore_of_outside facts hsync
  have hd := S.E.Δ_pos
  have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  have hb : (Restated.Vocabulary.Execution.Setup.a M S (r + 2)) + S.E.Δ ≤ b₀ := hb₀
  have h8 := Restated.tAwakeEnd_lt_confirmedSettleTime_add facts S tAwakeEnd
  have hTr₀ : (x[T].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S r) := hTr
  have ha1 := facts.gr.action_succ_eq_add_rounds S r
  have ha2 := facts.gr.action_succ_eq_add_rounds S (r + 1)
  have ha2' : (Restated.Vocabulary.Execution.Setup.a M S (r + 2)) = (Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1)) := rfl
  have hRΔ : 3 * S.E.Δ ≤ (S.hc.R : Int) * S.E.Δ := by nlinarith
  have hEnd : tAwakeEnd ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 2)) := by linarith
  have hRs : (M.round_of S.hc ((M.opening_slot S.hc (r + 2)) + 1 - 2)) = r + 1 :=
    Restated.round_of_opening_succ_add_one_sub_two facts S.hc (r + 1)
  obtain ⟨tE', htE', hlen', hthird', hawake', hrec', hsl', hrs', hcs', hsettle⟩ :=
    Restated.settledPremisesAtEarlierEnd_of_healed_upTo facts S Sched gap hgap x tGAT tAwakeEnd hlen hgst hmono
      hexec (sEnd := (M.opening_slot S.hc (r + 2)) + 1)
      (Restated.SynchronyFromWakeBefore.mono (by rw [hRs]; exact max_le (by linarith) (by linarith)) hs0)
      hmult hwakes hsleeps hcv htd hcom hthird hawake hrec hsl hrs hcs
  have hT' : Restated.confirmedSettleTime M S tE' ≤ (x[T].time : Int) :=
    le_trans (Restated.confirmedSettleTime_mono facts S htE') hT
  have hTr' : (x[T].time : Int) ≤ (M.a S.hc S.E.Δ (r + 1)) :=
    le_trans hTr (Restated.action_mono facts S (Nat.le_succ r))
  have hE' : tE' ≤ b₀ := by linarith
  exact
    { covers := Restated.stableHandover_covers_of_settleTick_upTo facts S Sched x tGAT tE' gap hgap hlen' hgst
        hmono hexec hs0 hmult hwakes hsleeps hcv htd hcom hthird' hawake' hrec' hsl' hrs' hcs'
        hsettle r T hT' hTr v hvT hva P hP (Nat.le_succ _) (max_le hE' hb)
      entries := Restated.stableHandover_entries_of_settleTick_upTo facts S Sched x tGAT tE' gap hgap hlen' hgst
        hmono hexec hs0 hmult hwakes hsleeps hcv htd hcom hthird' hawake' hrec' hsl' hrs' hcs'
        hsettle (r + 1) T hT' hTr' v hvT hva P hP le_rfl (max_le hE' hb)
      roots := Restated.stableHandover_roots_of_settleTick_upTo facts S Sched x tGAT tE' gap hgap hlen' hgst
        hmono hexec hs0 hmult hwakes hsleeps hcv htd hcom hthird' hawake' hrec' hsl' hrs' hcs'
        hsettle (r + 1) T hT' hTr' v hvT hva P hP le_rfl (max_le hE' (by linarith)) }

end

end DecoupledConsensusModel.Sts.Restated
