import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Record.Wiring

/-!
# The honest active attesters of a round, on the awake rule's grade-2 window

The set `freshAttestersW`, stated over a model `M : Record.Model V`.
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

/-- The members of `attestersAt` for round `r` (the validators awake throughout the awake rule's
    grade-2 window of round `r`) that are honest through step `m`. -/
noncomputable def freshAttestersW (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (r : Round) (m : Nat) : Finset V := by
  classical
  exact (Restated.attestersAt M S Sched r).filter (fun v => Restated.HonestThrough M Sched x m v)

end

end DecoupledConsensusModel.Sts.Restated
