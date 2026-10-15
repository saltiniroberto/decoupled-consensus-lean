module
public import Proofs.Vocabulary.Internal.StoreFinality
public import Proofs.Vocabulary.Protocol.Handlers.Bridges
public import Model.Vocabulary.Protocol.Evidence
public import Proofs.Vocabulary.Internal.Invariants
import Proofs.Vocabulary.Protocol.ChainState.AlignedRoundLemmas
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.Records
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section

/-!
# The justification height is less than the maximum height

`update_finality` preserves `JustificationBelowMax`, the store's justification height being less
than its maximum height.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace StoreFinality

open Protocol (ChainState HeightConfig)
open Protocol (Record HeightId)
open Protocol (HealConfig)
open Internal

variable {V : Type} [DecidableEq V] [Fintype V]


omit [Fintype V] in
/-- `update_finality` preserves `h_j < h_max` when the offered chain state satisfies `σ.h_j < σ.h`. -/
theorem justificationBelowMax_update_finality (st : Protocol.Store V)
    (σ : ChainState V) (hst : JustificationBelowMax st)
    (hσ : σ.h_j < σ.h) :
    JustificationBelowMax (Protocol.update_finality st σ) := by
  simp only [JustificationBelowMax, Protocol.update_finality]
  split_ifs <;>
    first
      | exact lt_of_lt_of_le hσ (Nat.le_max_right _ _)
      | exact lt_of_lt_of_le hst (Nat.le_max_left _ _)

end StoreFinality
end Proofs
end DecoupledConsensusModel

end
