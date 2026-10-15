module
public import Model.Vocabulary.Execution.Setup
import Proofs.Vocabulary.ModelVocabulary.Healing.Schedule
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.Walk
import Proofs.Vocabulary.Protocol.Schedule.ConfirmationHistoryProducer
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Data.DFinsupp.Notation
public import Mathlib.Data.Finsupp.Notation
public import Proofs.Vocabulary.Internal.Legacy.Definitions.LeakLedger

@[expose] public section


namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## No honest round action between proposal and vote -/

/-- A round action before slot `s`'s vote time is before slot `s`'s proposal time. -/
theorem action_time_lt_proposal_of_lt_vote
    (S : Setup V) {r : Round} {s : Slot}
    (h : S.a r < Protocol.vote_time S.E s) :
    S.a r < Protocol.proposal_time S.E s := by
  change S.hc.a S.E.Δ r < Protocol.vote_time S.E s at h
  change S.hc.a S.E.Δ r < Protocol.proposal_time S.E s
  rw [Protocol.a_eq_support_cutoff_succ S.hc S.E r] at h ⊢
  exact support_cutoff_lt_vote_time_imp_lt_proposal_time S.E h

/-- Proposal time precedes the same slot's vote time. -/
theorem proposal_time_lt_vote_time (E : Env V) (s : Slot) :
    Protocol.proposal_time E s < Protocol.vote_time E s := by
  unfold Protocol.vote_time
  exact Int.lt_add_of_pos_right _ E.Δ_pos


#print axioms action_time_lt_proposal_of_lt_vote

end Protocol
end DecoupledConsensusModel

end
