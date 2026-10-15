import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Generic
import Proofs.Claims.Restated.RunAll
import Proofs.Claims.Restated.VocabularyAssumptionsLemmas
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Generic
import Model.Conditions.Sts_Conditions
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bInvariant

/-!
# Tick steps and the sent log

Over a model `M : Record.Model V`: the instants around a tick step, a tick step as the last step
strictly before its instant, a tick step at every positive instant, and the growth of the sent log.
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

/-- If step `n` is the tick at `t`, then the configuration before it is at `t − 1` and the one after
    it is at `t`. -/
theorem tickStepAt_time (facts : Record.Facts M) {S : Setup V} {Sched : Schedule V}
    (x : AtomicExec (Record.protocolOf M S) Sched) {n : Nat} {t : Int} (h : Restated.tickStepAt M x n t) :
    (x[n + 1].time : Int) = t ∧ (x[n].time : Int) + 1 = t := by
  obtain ⟨t', hlbl, ht'⟩ := h
  obtain ⟨h1, h2⟩ := Restated.tickAllAwake_time facts S Sched x hlbl
  refine ⟨?_, ?_⟩
  · rw [← ht']
    exact_mod_cast h2
  · rw [← ht']
    exact_mod_cast h1

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If step `n` is the tick at `t`, then the configurations strictly before `t` are exactly those up
    to step `n`. -/
theorem stepBeforeInstant_of_tickStepAt (facts : Record.Facts M) {S : Setup V} {Sched : Schedule V}
    (x : AtomicExec (Record.protocolOf M S) Sched) {n : Nat} {t : Int} (h : Restated.tickStepAt M x n t) :
    Restated.stepBeforeInstant M x n t := by
  obtain ⟨h1, h0⟩ := Restated.tickStepAt_time facts x h
  refine ⟨?_, ?_⟩
  · intro k hk
    have hle : (x[k + 1].time : Int) ≤ (x[n].time : Int) := by
      exact_mod_cast Restated.time_mono facts S Sched x (Nat.succ_le_of_lt hk)
    linarith
  · intro k hk
    have hle : (x[n + 1].time : Int) ≤ (x[k + 1].time : Int) := by
      exact_mod_cast Restated.time_mono facts S Sched x (Nat.succ_le_succ hk)
    linarith

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- On an execution whose clock diverges, every instant `t` with `0 < t` is entered by a tick step. -/
theorem exists_tickStepAt (facts : Record.Facts M) {S : Setup V} {Sched : Schedule V}
    (x : AtomicExec (Record.protocolOf M S) Sched) (htd : Restated.TimeDiverges M x) {t : Int} (ht : 0 < t) :
    ∃ n : Nat, Restated.tickStepAt M x n t := by
  have hreach : Restated.ReachesEveryInstant M x := Restated.reachesEveryInstant_of_timeDiverges facts S x htd
  obtain ⟨i, hi⟩ := Restated.exists_step_at_instant facts hreach t.toNat
  have htn : ((t.toNat : Nat) : Int) = t := Int.toNat_of_nonneg (le_of_lt ht)
  have h0 : t.toNat ≠ 0 := by omega
  obtain ⟨j, -, hlbl, -, -⟩ := tickAllAwake_of_time x i hi h0
  exact ⟨j, t.toNat, hlbl, htn⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- A message in the sent log after `i` steps is in the sent log after `j` steps, for every `j ≥ i`. -/
theorem mem_sent_of_le (facts : Record.Facts M) {S : Setup V} {Sched : Schedule V}
    (x : AtomicExec (Record.protocolOf M S) Sched) {i j : Nat} (hij : i ≤ j)
    {sm : SignedMsg V (NamedObject V)} (h : sm ∈ x[i].sent) : sm ∈ x[j].sent := by
  have hle : x[i].sent ≤ x[j].sent := by
    induction j, hij using Nat.le_induction with
    | base => exact le_rfl
    | succ j hij ih => exact le_trans ih (atomic_sent_mono (x.step j))
  exact Multiset.mem_of_le hle h

end

end DecoupledConsensusModel.Sts.Restated
