import Model.Sts.Spec2Claims.Claim13bd
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Record.Wiring

/-!
# Recurring strong openings

The recurrence of rounds with honest proposers over a time window, stated over a model
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

/-- From `tGAT` to `tAwakeEnd`, within every `gap` rounds a round opens, at least two rounds later,
    whose first three slots have honest proposers, and every round opening in the two rounds before
    it has an honest proposer; each proposer's honesty is read through its own slot's confirmation
    instant. -/
def strongOpeningsRecurFrom (M : Record.Model V) (S : Setup V) (Sched : Schedule V) (tGAT tAwakeEnd : Int)
    (gap : Nat) : Prop :=
  ∀ t : Int, tGAT ≤ t → t + (gap : Int) * (Restated.constants M S).period ≤ tAwakeEnd →
    ∃ s : Slot, t + 2 * (Restated.constants M S).period ≤ (Restated.interface M S Sched).proposalTime s ∧
      (Restated.interface M S Sched).proposalTime s ≤ t + (gap : Int) * (Restated.constants M S).period ∧
      Restated.MultiProposerAt M S Sched (Restated.interface M S Sched) (Restated.constants M S) s ∧
      ∀ s' : Slot, (Restated.interface M S Sched).opening s' →
        (Restated.interface M S Sched).proposalTime s - 2 * (Restated.constants M S).period ≤
          (Restated.interface M S Sched).proposalTime s' →
        (Restated.interface M S Sched).proposalTime s' < (Restated.interface M S Sched).proposalTime s →
        HonestThroughTime Sched (M.confirmation_time S.E s')
          ((Restated.interface M S Sched).proposer s')

end

end DecoupledConsensusModel.Sts.Restated
