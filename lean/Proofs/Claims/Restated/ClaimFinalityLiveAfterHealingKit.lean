import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bK_FinalityGrowth
import Proofs.Claims.Restated.Claim13bK_FinalityInclusion
import Proofs.Claims.Restated.Claim13bKit
import Proofs.Claims.Restated.Constants
import Model.Conditions.Claim13bKit
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Sts_Spec2Claims_ClaimFinalityLiveAfterHealing
import Model.Record.Wiring

/-!
# Finality liveness after healing

A theorem over a model `M : Record.Model V` with facts `facts : Record.Facts M`:
`claimFinalityLiveAfterHealing_holds`, which proves
`Restated.claimFinalityLiveAfterHealingStatement M S Sched`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section

open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog

/-- `claimFinalityLiveAfterHealing_holds` at the healing length
    `healingLengthη M S gap + period`. -/
theorem claimFinalityLiveAfterHealing_holds_at (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V)
    (gap : Nat) (hgap : gap + 2 ≤ S.cfg.K)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tGAT tE tL : Int)
    (hlen : tGAT + (Restated.healingLengthη M S gap + (Restated.constants M S).period) ≤ tE)
    (hEL : tE ≤ tL)
    (hgst : S.E.t_GST ≤ tGAT)
    (hmono : Sched.MonotoneCorruption)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWake M S x)
    (hmult : AwakeAtMultiples S Sched)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (htd : Restated.TimeDiverges M x)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hthird : ∀ t : Int, t ≤ tL →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tL →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tL gap)
    (hsl : sleepinessW S Sched tE)
    (hrs : Restated.roundSleepinessW M S Sched tE)
    (hcs : Restated.committeeSleepinessW M S Sched tE) :
    Restated.FinalityIncludedAfterHealing M S Sched x tE tL gap ∧
      Restated.FinalityGrowsAfterHealing M S Sched x tE tL gap := by
  exact ⟨Restated.finalityIncluded_of_premises_f3 facts S Sched x tGAT tE tL gap hgap hlen hEL
      hgst hmono hexec hsync hmult hcv htd hcom hthird hawake hrec hsl hrs hcs,
    Restated.finalityGrows_of_premises_f5 facts S Sched x tGAT tE tL gap hgap hlen hEL hgst
      hmono hexec hsync hmult hcv htd hcom hthird hawake hrec hsl hrs hcs⟩

/-- For every `gap` with `gap + 2 ≤ K` there is a phase length `tHeal ≥ 0` such that, in every
    execution satisfying the healing premises with a phase of at least `tHeal` ending at
    `tAwakeEnd ≤ tLive`, every honest proposal made at or after `finalityLiveStart S tAwakeEnd gap`
    and at least `finalityPremisesContinueDirect S gap` before `tLive` is an ancestor of the
    finalized block of every validator honest through any step at or after its proposal instant plus
    `finalityDeadlineDirect S gap`; and from every such time `t` some later honest proposal strictly
    extends every honest finalized block at `t` and is an ancestor of every honest finalized block
    from `t + finalityGrowthDelay S gap` on. -/
theorem claimFinalityLiveAfterHealing_holds (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) :
    Restated.claimFinalityLiveAfterHealingStatement M S Sched := by
  intro gap hgap
  refine ⟨Restated.healingLengthη M S gap + (Restated.constants M S).period, ?_, ?_⟩
  · have h0 := Restated.healingLengthη_nonneg facts S gap
    have h1 : (0 : Int) < (Restated.constants M S).period := (Restated.constants_holds facts S).period_pos
    linarith
  · exact fun x tGAT tE tL hlen hEL hgst hmono hexec hsync hmult hcv htd hcom hthird
      hawake hrec hsl hrs hcs =>
      Restated.claimFinalityLiveAfterHealing_holds_at facts S Sched gap hgap x tGAT tE tL hlen hEL
        hgst hmono hexec hsync hmult hcv htd hcom hthird hawake hrec hsl hrs hcs

end

end DecoupledConsensusModel.Sts.Restated
