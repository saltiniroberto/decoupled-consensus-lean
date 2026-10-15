module
public import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.Admissible
public import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.Run
import Proofs.Vocabulary.Execution.HealthyLocalFacts
import Proofs.Vocabulary.Objects.Ancestry
import Proofs.Vocabulary.Protocol.Schedule.SlotInduction
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section

/-!
# A slot-time inequality

A support cutoff before slot `s`'s vote time is also before slot `s`'s proposal time.
-/

namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]


/-- A support cutoff before slot `s`'s vote time is before slot `s`'s proposal time. -/
theorem support_cutoff_lt_vote_time_imp_lt_proposal_time
    (E : Env V) {k s : Slot}
    (h : Protocol.support_cutoff E k < Protocol.vote_time E s) :
    Protocol.support_cutoff E k < Protocol.proposal_time E s := by
  have hvoteCut : Protocol.vote_time E s < Protocol.support_cutoff E s := by
    rw [← Proofs.Optimistic.vote_time_add_delta]
    exact Int.lt_add_of_pos_right _ E.Δ_pos
  have hks : k < s := by
    by_contra hnot
    have hsk : s ≤ k := Nat.le_of_not_gt hnot
    have hmono := Proofs.Optimistic.support_cutoff_mono E hsk
    have hbad : Protocol.vote_time E s < Protocol.support_cutoff E k :=
      lt_of_lt_of_le hvoteCut hmono
    exact (not_lt_of_ge (le_of_lt h)) hbad
  have hnext : Protocol.support_cutoff E k <
      Protocol.proposal_time E (k + 1) := by
    unfold Protocol.support_cutoff Protocol.proposal_time Env.t slotStart
    push_cast
    have h24 : 2 * E.Δ < 4 * E.Δ :=
      Int.mul_lt_mul_of_pos_right (by decide : (2 : Int) < 4) E.Δ_pos
    calc
      4 * E.Δ * (k : Int) + 2 * E.Δ <
          4 * E.Δ * (k : Int) + 4 * E.Δ :=
        Int.add_lt_add_left h24 _
      _ = 4 * E.Δ * ((k : Int) + 1) := by ring
  have hmono : Protocol.proposal_time E (k + 1) ≤
      Protocol.proposal_time E s :=
    proposal_time_mono E (Nat.succ_le_iff.mpr hks)
  exact lt_of_lt_of_le hnext hmono


end Protocol
end DecoupledConsensusModel

end
