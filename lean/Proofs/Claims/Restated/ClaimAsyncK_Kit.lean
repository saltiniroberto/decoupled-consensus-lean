import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bKit
import Proofs.Claims.Restated.ClaimAsyncK_AfterFacts
import Proofs.Claims.Restated.ClaimAsyncK_AfterPeriod
import Proofs.Claims.Restated.ClaimAsyncK_AfterSafe
import Proofs.Claims.Restated.ClaimAsyncK_Defs
import Proofs.Claims.Restated.ClaimAsyncK_PeriodInduction
import Proofs.Claims.Restated.Constants
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bKit
import Model.Conditions.ClaimAsyncK_Handover
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
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

/-!
# The stable output keeps `P` after the asynchronous period

A theorem over a model `M : Record.Model V` with facts `facts : Record.Facts M`: from the hand-over
facts for `P`, `P` stays an ancestor of every honest stable output from `b₀` on
(`stablePersists_forEver_ofHandover`).
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
open DecoupledConsensusModel.Protocol
open Framework.StsMultisetLog

/-- With delivery suspended on `[b₀, b₁)`, the sleepiness premises from a time `tE` at or before
    round `r + 1`'s opening, the GST at or before round `r + 1`'s action instant, the period placed
    after rounds `r + 1` and `r + 2` and ending before round `r + 1`'s attestations expire, the
    participation premise and the bound on the period's outside attesters, the healing premises
    again from `tAgain ≥ b₁ + Δ` to `tSafe ≥ tAgain + tHeal + liveAgainAfterHealing S gap`,
    `CommonViewOfFinalizedDescendantsAt S Sched x tAgain`, a validator `v` honest through a step at
    or before round `r`'s action instant whose stable output has `P` as an ancestor, and the
    hand-over facts for `P` at round `r + 1`: every validator honest through a step at or after
    `b₀`, and awake from the start of round `r + 1`'s attester window to that step, has `P` as an
    ancestor of its stable output there, or as that output itself. -/
theorem stablePersists_forEver_ofHandover (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (gap : Nat) (hgap : gap + 2 ≤ S.cfg.K)
    (tE b₀ b₁ tAgain tSafe tHeal : Int) (r : Nat) (P : Block V)
    (hheal : Restated.healingLengthη M S gap + ((gap : Int) + 2) * (Restated.constants M S).period ≤ tHeal)
    (hmono : Sched.MonotoneCorruption)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWakeOutside M S x b₀ b₁)
    (hmult : AwakeAtMultiples S Sched)
    (hwakes : Restated.WakesAtActionInstants M S Sched) (hsleeps : Restated.SleepsAfterActionInstants M S Sched)
    (hcatch : Restated.CatchUpOnWakeOutside M S x b₀ b₁)
    (htd : Restated.TimeDiverges M x) (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hcvAgain : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tAgain)
    (hsl : sleepinessW S Sched tE) (hrs : Restated.roundSleepinessW M S Sched tE)
    (hcs : Restated.committeeSleepinessW M S Sched tE)
    (htE : tE ≤ M.opening S.E S.hc (r + 1))
    (hgst : S.E.t_GST ≤ (M.a S.hc S.E.Δ (r + 1)))
    (hb₀ : Restated.periodAfterRound M S (r + 1) b₀) (hb : b₀ ≤ b₁)
    (hb₁ : Restated.periodBeforeExpiry M S (r + 1) b₁)
    (hfix : Restated.fixedRoundSleepinessCountedW M S Sched (r + 1))
    (hout : Restated.outsideAttestersUnderThird M S Sched (r + 1))
    (hAgain : b₁ + S.E.Δ ≤ tAgain)
    (hSafe : tAgain + (tHeal + Restated.liveAgainAfterHealing M S gap) ≤ tSafe)
    (hthird : ∀ t : Int, t ≤ tSafe →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hawake : ∀ t : Int, tAgain ≤ t → t ≤ tSafe →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tAgain tSafe gap)
    (v : V) (T : Nat) (hvT : Restated.HonestThrough M Sched x T v)
    (hTr : (x[T].time : Int) ≤ (M.a S.hc S.E.Δ r))
    (hPv : Block.Preceq P (M.get_stable (x[T][v].st).st.core))
    (hP : Restated.StableHandover M S Sched x (r + 1) P) :
    ∀ (w : V) (j : Nat), Restated.HonestThrough M Sched x j w →
      b₀ ≤ (x[j].time : Int) →
      w ∈ Sched.awakeThroughout ((M.a S.hc S.E.Δ (r + 1)) - wAttest S) (x[j].time : Int) →
      Block.Preceq P (M.get_stable (x[j][w].st).st.core) := by
  have hd : (0 : Int) < S.E.Δ := S.E.Δ_pos
  have hper : (0 : Int) < (Restated.constants M S).period := (Restated.constants_holds facts S).period_pos
  have hgapI : (0 : Int) ≤ (gap : Int) := Int.natCast_nonneg gap
  have hgp : (0 : Int) ≤ ((gap : Int) + 2) * (Restated.constants M S).period :=
    mul_nonneg (by linarith) hper.le
  have hη := Restated.healingLengthη_nonneg facts S gap
  have hlive := Restated.liveAgainAfterHealing_nonneg facts S gap
  have hb₀' : (M.a S.hc S.E.Δ (r + 2)) + S.E.Δ ≤ b₀ := hb₀
  have hr01 : (M.a S.hc S.E.Δ r) ≤ (M.a S.hc S.E.Δ (r + 1)) := Restated.healA_mono facts S (Nat.le_succ r)
  have hr12 : (M.a S.hc S.E.Δ (r + 1)) ≤ (M.a S.hc S.E.Δ (r + 2)) := Restated.healA_mono facts S (Nat.le_succ (r + 1))
  have hr2η : (M.a S.hc S.E.Δ (r + 2)) ≤ (M.a S.hc S.E.Δ (r + S.hc.η_SG + 2)) :=
    Restated.healA_mono facts S (by omega)
  have hop : M.opening S.E S.hc (r + 1) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) := by
    show _ ≤ M.a S.hc S.E.Δ (r + 1)
    rw [facts.gr.opening_eq_proposal_time, facts.sch.a_eq_confirmation_time]
    exact facts.sch.proposal_time_le_confirmation_time _ _
  have hSa1 : (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) = (M.a S.hc S.E.Δ (r + 1)) := rfl
  have hSa2 : (Restated.Vocabulary.Execution.Setup.a M S (r + 2)) = (M.a S.hc S.E.Δ (r + 2)) := rfl
  have hg : S.E.t_GST ≤ b₁ := by linarith
  have htE' : tE ≤ tAgain + tHeal := by linarith
  have hhealη : Restated.healingLengthη M S gap ≤ tHeal := by linarith
  have hsafe : (M.a S.hc S.E.Δ (r + S.hc.η_SG + 2)) ≤ tSafe :=
    Restated.action_le_tSafe_ofPage facts S hb₀ hb hAgain hSafe hhealη
  have htSafe0 : (0 : Int) ≤ tSafe := by linarith [S.E.t_GST_nonneg]
  obtain ⟨B, t, ht, hseenB, hfin, hBlog⟩ := Restated.finalizedAboveSeen_afterPeriod_inLog facts S Sched x gap
    hgap hheal hb hg hAgain hSafe htE' hmono hexec hsync hmult hwakes hsleeps htd hcom hcvAgain
    hsl hrs hcs hthird hawake hrec
  obtain ⟨n₁, hn₁⟩ := Restated.exists_tickStepAt facts x htd (Restated.action_pos facts S (r + 2))
  have hn₁t := (Restated.tickStepAt_time facts x hn₁).2
  have hroots := Restated.honestRoots_upToSafe_atPage facts S Sched x tE b₀ b₁ tSafe r P hmono hexec hsync hmult
    hwakes hsleeps hcatch htd hrs htE hgst hb₀ hb hb₁ hfix hout hthird hsafe hP hn₁
  let t' : Int := max t ((M.a S.hc S.E.Δ (r + S.hc.η_SG + 2)))
  have ht't : t ≤ t' := le_max_left _ _
  have ht'a : (M.a S.hc S.E.Δ (r + S.hc.η_SG + 2)) ≤ t' := le_max_right _ _
  have ht'S : t' ≤ tSafe := max_le ht hsafe
  obtain ⟨C, hC, hPC⟩ := Restated.exists_body_preceq_of_read facts S Sched x T v P hPv
  have hTA : (x[T].time : Int) ≤ tAgain := by linarith
  have hafter := Restated.stablePersists_afterSafe facts S Sched x tSafe t' P B ht'S htSafe0 hexec hBlog
    (fun w j hw hj => hfin w j hw (ht't.trans hj))
    (fun k hk hkS w hw => (hroots k
      (Restated.lt_of_time_lt facts S Sched x (by linarith)) hkS w hw).1)
    ⟨v, T, C, hvT, hC, hPC, hseenB v T hTA⟩
  intro w j hw hjb hwr
  by_cases h1 : (x[j].time : Int) < (M.a S.hc S.E.Δ (r + S.hc.η_SG + 2))
  · exact Restated.stablePersists_throughPeriod_atPage facts S Sched x tE b₀ b₁ tSafe r P hmono hexec hsync
      hmult hwakes hsleeps hcatch htd hrs htE hgst hb₀ hfix hout hthird hsafe hP w j hw hjb h1 hwr
  by_cases h2 : (x[j].time : Int) < t'
  · exact Restated.stablePersists_untilSafe_atPage facts S Sched x tE b₀ b₁ tSafe r P hmono hexec hsync hmult
      hwakes hsleeps hcatch htd hrs htE hgst hb₀ hb hb₁ hfix hout hthird hP w j hw
      (not_lt.mp h1) (by linarith) hwr
  · exact hafter w j hw (not_lt.mp h2)

end

end DecoupledConsensusModel.Sts.Restated
