module
public import Model.Vocabulary.Execution.Setup
import Proofs.Vocabulary.Execution.HealthyLocalFacts
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.ProposalVoteDuty
import Mathlib.Data.Rat.Floor

@[expose] public section

/-!
# Actions before a later vote

The action of a round is before the vote of every slot of a later round.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Protocol
open Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]


/-- The action of round `r` is before the vote time of every slot `d` of a later round. -/
theorem action_before_vote_of_round_lt
    (S : Setup V) {r : Round} {d : Slot} (hr : r < S.hc.round_of d) :
    S.a r < Protocol.vote_time S.E d := by
  have hfirst := Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt S hr
  have hslots : S.hc.opening_slot (S.hc.round_of d) ≤ d :=
    Nat.div_mul_le_self d S.hc.R
  have hproposal := hfirst.trans (proposal_time_mono S.E hslots)
  exact (Int.lt_add_of_pos_right _ S.E.Δ_pos).trans_le
    (hproposal.trans (le_of_lt (proposal_time_lt_vote_time S.E d)))

#print axioms action_before_vote_of_round_lt

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
