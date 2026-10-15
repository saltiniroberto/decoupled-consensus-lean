import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Conditions.ClaimAsyncK_DeliveryUpTo
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Sts_Spec2Claims_ClaimStableThroughAsyncPeriod
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.ClaimAsyncK_DeliveryUpTo

/-!
# Synchrony up to a bound

Theorems over a model `M : Record.Model V` with facts `facts : Record.Facts M` about synchrony from
wake for the sends whose deadline is at or before a bound.
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
theorem SynchronyFromWakeBefore.mono {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (Record.protocolOf M S) Sched} {b b' : Int} (hb : b ≤ b')
    (hs : Restated.SynchronyFromWakeBefore M S x b') : Restated.SynchronyFromWakeBefore M S x b :=
  fun k w sm hsend hle haw => hs k w sm hsend (le_trans hle hb) haw

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If synchrony is suspended only on the period `[b₀, b₁)`, then every honest send whose deadline
    is at or before `b₀` is delivered by that deadline. -/
theorem synchronyFromWakeBefore_of_outside (facts : Record.Facts M) {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (Record.protocolOf M S) Sched} {b₀ b₁ : Int}
    (hs : Restated.SynchronyFromWakeOutside M S x b₀ b₁) : Restated.SynchronyFromWakeBefore M S x b₀ := by
  intro k w sm hsend hle haw
  have hd : deadlineOutside S b₀ b₁ (x[k].time : Int) =
      max (x[k].time : Int) S.E.t_GST + S.E.Δ := if_pos hle
  obtain ⟨d, h1, h2, h3, h4⟩ := hs k w sm hsend (by rw [hd]; exact haw)
  exact ⟨d, h1, h2, h3, by rw [hd] at h4; exact h4⟩

end

end DecoupledConsensusModel.Sts.Restated
