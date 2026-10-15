import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Record.Wiring

/-!
# The common view among finalized descendants

A theorem over a model `M : Record.Model V` with facts `facts : Record.Facts M`: `CommonViewAtGAT`
gives `CommonViewOfFinalizedDescendantsAt`.
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

/-- `CommonViewAtGAT` at `t₀` gives `CommonViewOfFinalizedDescendantsAt` at `t₀`: a validator that
    holds, from `t₀ + Δ` on, every block an honest validator held by `t₀` holds in particular those
    of which its finalized block is an ancestor. -/
theorem commonViewOfFinalizedDescendantsAt_of_commonViewAtGAT (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (t₀ : Int) (h : Restated.CommonViewAtGAT M S Sched x t₀) :
    Restated.CommonViewOfFinalizedDescendantsAt M S Sched x t₀ :=
  fun i j v w B hi hv hB hj hw haw _ => h i j v w B hi hv hB hj hw haw

end

end DecoupledConsensusModel.Sts.Restated
