import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Conditions.Generic
import Model.Conditions.Sts_Conditions
import Model.Record.Wiring

/-!
# Diverging time reaches every instant

A theorem over a model `M : Record.Model V` with facts `facts : Record.Facts M`: `TimeDiverges`
gives `ReachesEveryInstant`.
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

/-- If the execution's time diverges (`TimeDiverges M x`), every integer time is at or before the
    time of some step (`ReachesEveryInstant M x`). -/
theorem reachesEveryInstant_of_timeDiverges (facts : Record.Facts M) (S : Setup V) {Sched : Schedule V}
    (x : AtomicExec (Record.protocolOf M S) Sched) (h : Restated.TimeDiverges M x) :
    Restated.ReachesEveryInstant M x := by
  intro t
  obtain ⟨i, hi⟩ := h (max t 0).toNat
  refine ⟨i, ?_⟩
  have hkval : (((max t 0).toNat : Nat) : Int) = max t 0 :=
    Int.toNat_of_nonneg (le_max_right t 0)
  have hkt : t ≤ (((max t 0).toNat : Nat) : Int) := by
    rw [hkval]; exact le_max_left t 0
  have hi' : (((max t 0).toNat : Nat) : Int) ≤ (x[i].time : Int) := by exact_mod_cast hi
  exact le_trans hkt hi'

end

end DecoupledConsensusModel.Sts.Restated
