module
public import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.Run
public import Proofs.Vocabulary.Internal.ModelVocabulary.Protocol.NamedStoreReads
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
public import Proofs.Vocabulary.Internal.Internal.GradeReads
public import Mathlib.Data.DFinsupp.Notation

@[expose] public section

/-!
# Height-filter progress

The predicate `HonestHeightFilterProgressAboveThrough`.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Some honest validator's store at some time `u ≤ t` has `h_max` at least `H + 2`. -/
def HonestHeightFilterProgressAboveThrough
    (S : Setup V) (rho : Run V) (H : Height) (t : Time) : Prop :=
  ∃ v, v ∈ rho.honest ∧ ∃ u, u <= t ∧
    H + 2 <= (rho.storeAt S v u).h_max


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
