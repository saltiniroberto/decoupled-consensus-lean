import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Record.Wiring

/-!
# Adversary weight inside the phase

The validators the adversary holds at a configuration at or before `tAwakeEnd` weigh less than a
third of the total, stated over a model `M : Record.Model V` and its facts `facts : Record.Facts M`.
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
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- If the adversary holds less than a third of the weight at every instant up to `tAwakeEnd` and
    `x[n].time ≤ tAwakeEnd`, then `Execution.BelowOneThird` holds of the validators not held by the
    adversary at `x[n].time`: the validators outside that set weigh less than a third of the total. -/
theorem belowOneThird_runAll_notHeld_inPhase (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (n : Nat) (tAwakeEnd : Int)
    (hthird : ∀ t : Int, t ≤ tAwakeEnd →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hn : (x[n].time : Int) ≤ tAwakeEnd) :
    Execution.BelowOneThird (Setup.alwaysAwake S)
      (Finset.univ \ Sched.adv (x[n].time : Int)) := by
  show 3 * S.E.electorate.weightOf
      (Finset.univ \ (Finset.univ \ Sched.adv (x[n].time : Int))) < S.E.W
  rw [sdiff_sdiff_right_self, inf_eq_right.2 (Finset.subset_univ _)]
  have h1 := hthird _ hn
  have h2 := weightOf_add_weightOf_sdiff_eq_W S.E (Sched.adv (x[n].time : Int))
  have h3 := S.E.electorate.weightOf_add_weightOf_sdiff (Sched.adv (x[n].time : Int))
  omega

end

end DecoupledConsensusModel.Sts.Restated
