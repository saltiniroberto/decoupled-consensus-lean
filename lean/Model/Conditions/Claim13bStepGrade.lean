import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13b
import Model.Record.Wiring

/-!
# The fresh attesters of a round

The set `freshAttesters`, stated over a model `M : Record.Model V`.
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

/-- The members of `activeRound` for round `r` (the validators awake throughout the `4Δ` before
    round `r`'s action time) that are honest through step `m`. -/
noncomputable def freshAttesters (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (r : Round) (m : Nat) : Finset V := by
  classical
  exact (Restated.activeRound M S Sched r).filter (fun q => Restated.HonestThrough M Sched x m q)

end

end DecoupledConsensusModel.Sts.Restated
