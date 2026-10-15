import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bK_ConfirmedSettleEarlier
import Proofs.Claims.Restated.Claim13bK_ConfirmedStrongRoundSettle
import Proofs.Claims.Restated.Claim13bKit
import Proofs.Claims.Restated.Claim13bW_Schedule
import Proofs.Claims.Restated.ClaimAsyncK_AfterFacts
import Proofs.Claims.Restated.ClaimAsyncK_HandoverHealedUpTo
import Proofs.Claims.Restated.ClaimAsyncK_Kit
import Proofs.Claims.Restated.CommonViewOfFinalizedDescendantsDerived
import Proofs.Claims.Restated.Constants
import Model.Conditions.Claim13bKit
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
import Proofs.Claims.Spec2Claims.ClaimAsyncK_SecondHealing
import Proofs.Claims.Spec2Claims.Claim13bModel_Preceq
import Proofs.Claims.Spec2Claims.Claim13bModel_compatible
import Proofs.Claims.Spec2Claims.Claim13bModel_slotStart
import Proofs.Claims.Spec2Claims.Claim13bModel_confirmation_time
import Proofs.Claims.Spec2Claims.Claim13bModel_proposal_time_inclG1
import Proofs.Claims.Spec2Claims.ClaimAsyncK_AfterPeriod
import Proofs.Claims.Spec2Claims.Claim13bK_ConfirmedStrongRoundSettle
import Proofs.Claims.Spec2Claims.Claim13bK_ConfirmedRecordUpTo
import Proofs.Claims.Spec2Claims.ClaimAsyncK_HandoverCoversUpTo

/-!
# The stable output through one asynchronous period

Theorems over a model `M : Record.Model V` with facts `facts : Record.Facts M`: the asynchronous
period starts at least one delay after `tGAT` (`tGAT_add_delta_le_periodStart`), and
`claimStableThroughOneAsyncPeriod_holds`, which proves
`Restated.claimStableThroughOneAsyncPeriodStatement M S Sched`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog

/-- If the phase `[tGAT, tAwakeEnd]` is at least `healingLengthη S gap + (gap + 2) · period` long,
    `confirmedSettleTime S tAwakeEnd` is at or before round `r`'s action instant, and
    `periodAfterRound S (r + 1) b₀` holds, then `tGAT + Δ ≤ b₀`. -/
theorem tGAT_add_delta_le_periodStart (facts : Record.Facts M) (S : Setup V) (gap : Nat) {tGAT tAwakeEnd b₀ : Int}
    {r : Nat}
    (hlen : tGAT + (Restated.healingLengthη M S gap + ((gap : Int) + 2) * (Restated.constants M S).period) ≤ tAwakeEnd)
    (hset : Restated.confirmedSettleTime M S tAwakeEnd ≤ (M.a S.hc S.E.Δ r))
    (hb₀ : Restated.periodAfterRound M S (r + 1) b₀) :
    tGAT + S.E.Δ ≤ b₀ := by
  have hd : (1 : Int) ≤ S.E.Δ := S.E.Δ_pos
  have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  have hη := Restated.healingLengthη_nonneg facts S gap
  have hg : (0 : Int) ≤ (gap : Int) := Int.natCast_nonneg gap
  have hpe := Restated.period_eq facts S
  have hlt := Restated.tAwakeEnd_lt_confirmedSettleTime_add facts S tAwakeEnd
  have har := Restated.action_eq_l85d facts S r
  have har2 := Restated.action_eq_l85d facts S (r + 1 + 1)
  have hSar : (Restated.Vocabulary.Execution.Setup.a M S r) = (M.a S.hc S.E.Δ r) := rfl
  have hSa2 : (Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1)) = (M.a S.hc S.E.Δ (r + 1 + 1)) := rfl
  have hb₀' : (M.a S.hc S.E.Δ (r + 1 + 1)) + S.E.Δ ≤ b₀ := hb₀
  rw [← hSar, har] at hset
  rw [← hSa2, har2] at hb₀'
  rw [hpe] at hlen
  push_cast at hset hb₀'
  have hRΔ : 3 * S.E.Δ ≤ S.E.Δ * (S.hc.R : Int) := by nlinarith
  have hgR : 0 ≤ (gap : Int) * (S.E.Δ * (S.hc.R : Int)) := by positivity
  nlinarith

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog

/-- `claimStableThroughOneAsyncPeriod_holds` at the healing length
    `healingLengthη M S gap + (gap + 2) · period`. -/
theorem claimStableThroughOneAsyncPeriod_holds_at (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V)
    (gap : Nat) (hgap : gap + 2 ≤ S.cfg.K)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (tGAT tAwakeEnd b₀ b₁ tAgain tSafe : Int) (r : Nat)
    (hlen : tGAT + (Restated.healingLengthη M S gap
      + ((gap : Int) + 2) * (Restated.constants M S).period) ≤ tAwakeEnd)
    (hgst : S.E.t_GST ≤ tGAT)
    (hmono : Sched.MonotoneCorruption)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWakeOutside M S x b₀ b₁)
    (hmult : AwakeAtMultiples S Sched)
    (hwakes : Restated.WakesAtActionInstants M S Sched)
    (hsleeps : Restated.SleepsAfterActionInstants M S Sched)
    (hcatch : Restated.CatchUpOnWakeOutside M S x b₀ b₁)
    (htd : Restated.TimeDiverges M x)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hthird : ∀ t : Int, t ≤ tAwakeEnd →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tAwakeEnd gap)
    (hsl : sleepinessW S Sched tAwakeEnd)
    (hrs : Restated.roundSleepinessW M S Sched tAwakeEnd)
    (hcs : Restated.committeeSleepinessW M S Sched tAwakeEnd)
    (hset : Restated.confirmedSettleTime M S tAwakeEnd ≤ (M.a S.hc S.E.Δ r))
    (hb₀ : Restated.periodAfterRound M S (r + 1) b₀)
    (hb : b₀ ≤ b₁)
    (hb₁ : Restated.periodBeforeExpiry M S (r + 1) b₁)
    (hfix : Restated.fixedRoundSleepinessCountedW M S Sched (r + 1))
    (hout : Restated.outsideAttestersUnderThird M S Sched (r + 1))
    (hAgain : b₁ + S.E.Δ ≤ tAgain)
    (hSafe : tAgain + (Restated.healingLengthη M S gap
      + ((gap : Int) + 2) * (Restated.constants M S).period
      + Restated.liveAgainAfterHealing M S gap) ≤ tSafe)
    (hthird' : ∀ t : Int, t ≤ tSafe →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hawake' : ∀ t : Int, tAgain ≤ t → t ≤ tSafe →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrec' : Restated.strongOpeningsRecurFrom M S Sched tAgain tSafe gap) :
    Restated.StablePersistsFromRound M S Sched x tAwakeEnd r b₀ := by
  have hper : (0 : Int) < (Restated.constants M S).period := (Restated.constants_holds facts S).period_pos
  have hgapI : (0 : Int) ≤ (gap : Int) := Int.natCast_nonneg gap
  have hη := Restated.healingLengthη_nonneg facts S gap
  have hd : (1 : Int) ≤ S.E.Δ := S.E.Δ_pos
  have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  have hpe := Restated.period_eq facts S
  have hηp := Restated.period_le_healingLengthη facts S gap
  have hlt := Restated.tAwakeEnd_lt_confirmedSettleTime_add facts S tAwakeEnd
  have hSar : (Restated.Vocabulary.Execution.Setup.a M S r) = (M.a S.hc S.E.Δ r) := rfl
  have hSa1 : (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) = (M.a S.hc S.E.Δ (r + 1)) := rfl
  have har1 := Restated.actionInstant_succ_eq facts S r
  have hop1 : (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) = M.opening S.E S.hc (r + 1) + 6 * S.E.Δ := by
    have h1 : Restated.Vocabulary.Execution.Setup.a M S (r + 1)
        = M.confirmation_time S.E (M.opening_slot S.hc (r + 1)) :=
      facts.sch.a_eq_confirmation_time S.hc S.E (r + 1)
    rw [h1, facts.gr.opening_eq_proposal_time]
    exact (facts.sch.slot_instants_l55 S.E (M.opening_slot S.hc (r + 1))).2.2.2.2.2
  have hRΔ : (0 : Int) ≤ (S.hc.R : Int) * S.E.Δ := by nlinarith
  set tE' : Int := min tAwakeEnd (M.opening S.E S.hc (r + 1)) with htE'def
  have htE'le : tE' ≤ tAwakeEnd := min_le_left _ _
  have htE'op : tE' ≤ M.opening S.E S.hc (r + 1) := min_le_right _ _
  have hwin : tGAT + 8 * (S.hc.R : Int) * S.E.Δ ≤ tE' := by
    refine le_min ?_ ?_
    · rw [hpe] at hηp hlen
      nlinarith
    · rw [hpe] at hηp hlen
      nlinarith
  have hsl' := sleepinessW_of_later S Sched tGAT tAwakeEnd tE' hmono hawake hwin hsl
  have hrs' := Restated.roundSleepinessW_of_later facts S Sched tGAT tAwakeEnd tE' hmono hawake hwin hrs
  have hcs' := Restated.committeeSleepinessW_of_later facts S Sched tGAT tAwakeEnd tE' hmono hawake hcom hwin hcs
  have hgst' : S.E.t_GST ≤ (M.a S.hc S.E.Δ (r + 1)) := by
    rw [← hSa1, har1]
    rw [← hSar] at hset
    nlinarith
  have hgstb₁ : S.E.t_GST ≤ b₁ := by
    have hSa2 : (Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1)) = (M.a S.hc S.E.Δ (r + 1 + 1)) := rfl
    have h12 : (M.a S.hc S.E.Δ (r + 1)) ≤ (M.a S.hc S.E.Δ (r + 1 + 1)) := by
      rw [← hSa1, ← hSa2]
      exact Restated.action_mono facts S (Nat.le_succ _)
    have hb₀' : (M.a S.hc S.E.Δ (r + 1 + 1)) + S.E.Δ ≤ b₀ := hb₀
    linarith
  have hSafeΔ : tAgain + S.E.Δ ≤ tSafe := by
    have hlive := Restated.liveAgainAfterHealing_nonneg facts S gap
    rw [hpe] at hper
    have : S.E.Δ ≤ Restated.healingLengthη M S gap + ((gap : Int) + 2) * (Restated.constants M S).period := by
      rw [hpe]
      nlinarith
    linarith
  have htb := Restated.tGAT_add_delta_le_periodStart facts S gap hlen hset hb₀
  have hcv := Restated.commonViewOfFinalizedDescendantsAt_beforePeriod facts S Sched x hexec hsync hcatch hgst
    htb hmult htd (tE := tAwakeEnd)
    (by have := Restated.delta_le_healingLengthη_add_gap_period facts S gap; linarith) hawake
  have hcvAgain := Restated.commonViewOfFinalizedDescendantsAt_afterPeriod facts S Sched x hexec hsync hcatch
    hb hgstb₁ hAgain hmult htd hSafeΔ hawake'
  intro v T P hvT hT hTr hva hPv
  have hH := Restated.stableHandover_of_healed_upTo facts S Sched gap hgap x tGAT tAwakeEnd b₀ b₁ hlen hgst
    hmono hexec hsync hmult hwakes hsleeps hcatch hcv htd hcom hthird hawake hrec hsl hrs hcs
    r hb₀ v T P hvT hT hTr hva hPv
  exact Restated.stablePersists_forEver_ofHandover facts S Sched x gap hgap tE' b₀ b₁ tAgain tSafe
    (Restated.healingLengthη M S gap + ((gap : Int) + 2) * (Restated.constants M S).period) r P le_rfl hmono hexec
    hsync hmult hwakes hsleeps hcatch htd hcom hcvAgain hsl' hrs' hcs' htE'op hgst' hb₀ hb hb₁
    hfix hout hAgain hSafe hthird' hawake' hrec' v T hvT hTr hPv hH

/-- `Restated.claimStableThroughOneAsyncPeriodStatement M S Sched` holds: with the healing length
    `healingLengthη S gap + (gap + 2) · period`, on every execution satisfying the healing and
    asynchronous-period premises, if `v` is honest through a step `T` between
    `confirmedSettleTime S tAwakeEnd` and round `r`'s action instant and awake throughout the vote
    window of that step's slot, then every ancestor `P` of `v`'s stable output at step `T` is an
    ancestor of the stable output of every validator `w` at every step `j` whose time is at or after
    `b₀`, when `w` is honest through step `j` and awake at every time from the start of round
    `r + 1`'s attester window to step `j`'s time. -/
theorem claimStableThroughOneAsyncPeriod_holds (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) :
    Restated.claimStableThroughOneAsyncPeriodStatement M S Sched := by
  intro gap hgap
  have hper : (0 : Int) < (Restated.constants M S).period := (Restated.constants_holds facts S).period_pos
  have hgapI : (0 : Int) ≤ (gap : Int) := Int.natCast_nonneg gap
  have hη := Restated.healingLengthη_nonneg facts S gap
  refine ⟨Restated.healingLengthη M S gap + ((gap : Int) + 2) * (Restated.constants M S).period,
    by nlinarith, ?_⟩
  exact fun x tGAT tAwakeEnd b₀ b₁ tAgain tSafe r hlen hgst hmono hexec hsync hmult hwakes hsleeps
    hcatch htd hcom hthird hawake hrec hsl hrs hcs hset hb₀ hb hb₁ hfix hout hAgain hSafe hthird'
    hawake' hrec' =>
    Restated.claimStableThroughOneAsyncPeriod_holds_at facts S Sched gap hgap x tGAT tAwakeEnd b₀ b₁
      tAgain tSafe r hlen hgst hmono hexec hsync hmult hwakes hsleeps hcatch htd hcom hthird hawake
      hrec hsl hrs hcs hset hb₀ hb hb₁ hfix hout hAgain hSafe hthird' hawake' hrec'

end

end DecoupledConsensusModel.Sts.Restated
