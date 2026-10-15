import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13beRoute3_44
import Proofs.Claims.Restated.Claim13beRoute3_44UpTo
import Proofs.Claims.Restated.Claim13beRoute3_70b
import Proofs.Claims.Restated.Claim13beRoute3_71
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.ClaimAsyncK_DeliveryUpTo
import Model.Conditions.RunAll
import Model.Conditions.RunVocabulary
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# The progress deadline on the full run, with synchrony up to a step

The progress deadline for a run-scoped named base on the run `runAll`, with synchrony only up to
`x[n].time`, stated over a model `M : Record.Model V` and concluded along `Restated.runAllPath`.
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
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- With synchrony only up to `x[n].time`, if the action instant of the progress deadline from
    `roundAt S tGAT + η_SG` is in the horizon of `runAll M S Sched x v n` with the validators not
    held as its honest set, then some run-scoped named base at round `roundAt S tGAT + η_SG + 2`,
    read along `Restated.runAllPath M S Sched x v n` over the validators not held, has its first
    crossing no later than the deadline's inclusive index. -/
theorem exists_namedHeightRegimeBaseRun_before_fgSafetyProgressDeadline_runAll_notHeld_upTo (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V) (n : Nat)
    {tGAT tAwakeEnd : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWakeBefore M S x (x[n].time : Int)) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tAwakeEnd →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hn : (x[n].time : Int) ≤ tAwakeEnd)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tAwakeEnd gap)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S))
        (fgSafetyProgressDeadline (Setup.alwaysAwake S)
          ({ Restated.runAll M S Sched x v n with honest := notHeldAt Sched (x[n].time : Int) } : Record.Run V)
          (Restated.roundAt M S tGAT + S.hc.η_SG) gap (Setup.alwaysAwake S).extraRounds) ≤
      ({ Restated.runAll M S Sched x v n with honest := notHeldAt Sched (x[n].time : Int) } :
        Record.Run V).horizon) :
    ∃ (blocked : Height) (first : Nat) (Tprev : NamedBlock V),
      first ≤ inclusiveEventIndex
        ({ Restated.runAll M S Sched x v n with honest := notHeldAt Sched (x[n].time : Int) } : Record.Run V)
        ((Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S))
          (fgSafetyProgressDeadline (Setup.alwaysAwake S)
            ({ Restated.runAll M S Sched x v n with honest := notHeldAt Sched (x[n].time : Int) } : Record.Run V)
            (Restated.roundAt M S tGAT + S.hc.η_SG) gap (Setup.alwaysAwake S).extraRounds)) ∧
      Restated.NamedHeightRegimeBaseRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v n with honest := notHeldAt Sched (x[n].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v n)
        (fun t => Restated.runAllPath M S Sched x v n
          (strictEventIndex
            ({ Restated.runAll M S Sched x v n with honest := notHeldAt Sched (x[n].time : Int) } :
              Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ (Restated.roundAt M S tGAT + S.hc.η_SG + 2)
        blocked first Tprev := by
  obtain ⟨hpost, hlo, hloOpen, ht₀⟩ := Restated.roundAt_bounds_l71 facts S hgst
  exact Restated.exists_namedHeightRegimeBaseRun_before_fgSafetyProgressDeadlineOn facts
    (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ Finset.univ
    (Restated.admissibleFieldsOn_runAll_notHeld_upTo facts S Sched x v n hsync hmono hawake hgst hcv
      hvalid hawm hthird hn)
    (fun _ _ h => notHeldAt_anti hmono h) (fun _ => Finset.subset_univ _)
    (fun _ _ => Finset.subset_univ _) (Finset.subset_univ _)
    (Restated.honestCommitteesOn_notHeld facts S Sched hcom)
    (Restated.belowOneThirdOn_runAll_notHeld facts S Sched x v n hthird hn)
    (Restated.multiProposerRecurrenceOn_runAll_notHeld facts S Sched x v n hrec hn)
    (Setup.timeoutDelayBound _) hpost hhor hlo hloOpen ht₀
    (fun k hk u _ j hj => Restated.awake_g2_action_runAllPath facts S Sched x v n hmono hawake hn
      k hk u j hj)

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

local macro "p68% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Claims.Restated.Claim13beRoute3_68)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

end

end DecoupledConsensusModel.Sts.Restated
