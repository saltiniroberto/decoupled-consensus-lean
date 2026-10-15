import Model.Sts.Spec2Claims.Claim13bf
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Record.Wiring

/-!
# Catch-up on wake and compatible finality

The catch-up premise, and the statement that the finalized blocks of honest validators are
compatible after a long enough phase of awake honest validators, stated over a model
`M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- A message an honest validator sent or forwarded before `w`'s wake instant `t_w` is delivered to
    `w` at or after the wake and within `Δ` of it, after `t_GST`, provided `w` stays awake for that
    `Δ`. -/
def CatchUpOnWake (M : Record.Model V) (S : Setup V) {Sched : Schedule V}
    (x : AtomicExec (Record.protocolOf M S) Sched) : Prop :=
  ∀ (k : Nat) (w : V) (sm : SignedMsg V (NamedObject V)) (t_w : Int),
    Restated.HonestSendAt M S x k sm →
    (x[k].time : Int) < t_w →
    w ∈ Sched.awake t_w → w ∉ Sched.awake (t_w - 1) →
    w ∈ Sched.awakeThroughout t_w (max t_w S.E.t_GST + S.E.Δ) →
    ∃ d : Nat, k < d ∧ x.lbl d = AtomicAction.deliver w sm ∧
      t_w ≤ (x[d].time : Int) ∧ (x[d].time : Int) < max t_w S.E.t_GST + S.E.Δ

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For every `gap` with `gap + 2 ≤ S.cfg.K` there is a `tHeal ≥ 0` such that, in every execution
    with a phase `[tGAT, tAwakeEnd]` of length at least `tHeal`, starting at or after `S.E.t_GST`
    and meeting the premises listed, any two validators honest through any two steps have compatible
    finalized blocks. -/
def claim13bfStatement (M : Record.Model V) (S : Setup V) (Sched : Schedule V) : Prop :=
  ∀ gap : Nat, gap + 2 ≤ S.cfg.K →
  ∃ tHeal : Int, 0 ≤ tHeal ∧
  ∀ (x : AtomicExec (Record.protocolOf M S) Sched) (tGAT tAwakeEnd : Int),
    tGAT + tHeal ≤ tAwakeEnd →
    S.E.t_GST ≤ tGAT →
    Sched.MonotoneCorruption →
    Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x →
    Restated.SynchronyFromWake M S x →
    AwakeAtMultiples S Sched →
    Restated.WakesAtActionInstants M S Sched →
    Restated.SleepsAfterActionInstants M S Sched →
    Restated.CatchUpOnWake M S x →
    Restated.TimeDiverges M x →
    Restated.HonestCommittees M S Sched (Restated.interface M S Sched) →
    (∀ t : Int, t ≤ tAwakeEnd →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight) →
    (∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t) →
    Restated.strongOpeningsRecurFrom M S Sched tGAT tAwakeEnd gap →
    sleepinessW S Sched tAwakeEnd →
    Restated.roundSleepinessW M S Sched tAwakeEnd →
    Restated.committeeSleepinessW M S Sched tAwakeEnd →
    ∀ (v₁ v₂ : V) (i j : Nat),
      Restated.HonestThrough M Sched x i v₁ → Restated.HonestThrough M Sched x j v₂ →
      Block.Compatible (Restated.Read.finalized M x[i][v₁].st) (Restated.Read.finalized M x[j][v₂].st)

end

end DecoupledConsensusModel.Sts.Restated
