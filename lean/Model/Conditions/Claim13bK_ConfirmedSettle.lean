import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Claim13bStepConeIter
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bK_ConfirmedSettle

/-!
# A block that is an ancestor of every honest head from a slot on

The condition `AncestorOfHonestHeadsFrom`, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Every honest active member of the committee of every slot from `s` on votes there for a
    descendant of `B`. -/
def AncestorOfHonestHeadsFrom (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (B : Block V) (s : Slot) : Prop :=
  ∀ s' : Slot, s ≤ s' → Restated.HeadsBelow M S Sched x B s'

end

end DecoupledConsensusModel.Sts.Restated
