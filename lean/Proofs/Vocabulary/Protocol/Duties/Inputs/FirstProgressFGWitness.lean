module
public import Proofs.Vocabulary.Objects.FGConfirmationHistory
public import Proofs.Vocabulary.Protocol.Grades.VoteBelowSource
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.ActionSourceCore
public import Proofs.Vocabulary.Internal.Definitions.NamedJointOutage
import Proofs.Vocabulary.Protocol.Grades.Q10Frame
import Proofs.Vocabulary.Protocol.Handlers.HMaxCore
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section

/-!
# Height windows

`HeightWindowAt`: before an event index, every honest maximum height is at most `H`.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Before the event index `first`, which is positive, every honest maximum height is at most `H`. -/
structure HeightWindowAt
    (S : Setup V) (rho : Run V) (H : Height) (first : Nat) : Prop where
  positive : 0 < first
  before : ∀ i : Nat, i < first → honestHMaxBeforeIndex S rho i ≤ H


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
