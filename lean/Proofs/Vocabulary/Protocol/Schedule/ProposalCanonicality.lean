module
public import Proofs.Vocabulary.ModelVocabulary.Goldfish.ForkChoice
public import Proofs.Vocabulary.Objects.AdmissibleCore
public import Proofs.Vocabulary.Protocol.ForkChoice.Views.ProposalCore
import Proofs.Vocabulary.Protocol.ForkChoice.Views.VoteSetValidityCore
import Proofs.Vocabulary.Protocol.Handlers.TickBridges
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# A slot-time inequality for proposals

A slot's support cutoff is at most the next slot's proposal time.
-/


namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The slot-`s` support cutoff is at most the slot-`(s + 1)` proposal time. -/
theorem support_cutoff_le_proposal_time_succ (E : Env V) (s : Slot) :
    Protocol.support_cutoff E s ≤ Protocol.proposal_time E (s + 1) := by
  have hstep : Protocol.proposal_time E (s + 1) =
      Protocol.support_cutoff E s + 2 * E.Δ := by
    unfold Protocol.support_cutoff Protocol.proposal_time Env.t slotStart
    push_cast
    ring
  rw [hstep]
  exact le_add_of_nonneg_right
    (Int.mul_nonneg (by norm_num) (le_of_lt E.Δ_pos))


end Protocol
end DecoupledConsensusModel

end
