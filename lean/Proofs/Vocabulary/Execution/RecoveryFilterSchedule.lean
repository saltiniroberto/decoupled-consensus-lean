module
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.ProposalVoteDuty
import Proofs.Vocabulary.Generic.EvaluationStore
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section

/-!
# Settlement of recovery-filter sources

An attestation is emitted at a round action `a_r`, and any later read of the four relevant kinds is
at least one network delay after it.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Schedule arithmetic -/

/-- An action earlier than the vote time of slot `s` is at least one network delay before it. -/
theorem action_add_delta_le_vote_of_lt
    (S : Setup V) {r : Round} {s : Slot}
    (hlt : S.a r < Protocol.vote_time S.E s) :
    S.a r + S.E.Δ ≤ Protocol.vote_time S.E s := by
  have hproposal : S.a r < Protocol.proposal_time S.E s :=
    Protocol.action_time_lt_proposal_of_lt_vote S hlt
  exact le_trans
    (Protocol.action_add_delta_le_proposal_of_lt S hproposal)
    (le_of_lt (Protocol.proposal_time_lt_vote_time S.E s))


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
