module
public import Model.Vocabulary.Protocol.Handlers
public import Proofs.Vocabulary.Objects.Ancestry

@[expose] public section

/-!
# The confirmation record update

Algebraic facts about `advance_confirmed`: when it moves to the candidate, and what it keeps.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace ConfirmationPolicy

variable {V : Type} [DecidableEq V]


/-- `advance_confirmed old candidate` is `candidate` when `candidate`'s slot is at least `old`'s and
    every strict ancestor of a block has a smaller slot than the block. -/
theorem advance_eq_candidate_of_slot (old candidate : Block V)
    (hslot : old.slot ≤ candidate.slot)
    (hstrict : Block.Preceq candidate old → candidate ≠ old → candidate.slot < old.slot) :
    Protocol.advance_confirmed old candidate = candidate := by
  unfold Protocol.advance_confirmed
  split
  · rename_i hpre
    by_cases heq : candidate = old
    · exact heq.symm
    · exact False.elim ((Nat.not_lt_of_ge hslot) (hstrict hpre heq))
  · rfl


end ConfirmationPolicy
end Proofs
end DecoupledConsensusModel

end
