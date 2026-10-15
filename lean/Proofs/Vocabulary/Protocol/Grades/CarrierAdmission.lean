module
public import Proofs.Vocabulary.Internal.Definitions.TickReads
public import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.Admissible
import Proofs.Vocabulary.Execution.Acceptance
import Proofs.Vocabulary.Protocol.Handlers.BlockAdmission
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Acceptance of blocks in a vote-duty tree

A positive-slot block in a validator's vote-duty tree was accepted before that vote duty.
-/


namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]


/-- A positive-slot block `B` in `w`'s slot-`k` vote-duty tree is the erasure of a named block that
    `w` accepted at a time `t` with the proposal time of `B.slot` at most `t` and `t` before slot
    `k`'s vote time. -/
theorem acceptsAt_carrier_before_vote_of_mem_voteDutyStore
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} {k : Slot} {B : Block V} (hBpos : 0 < B.slot)
    (hB : B ∈ (Proofs.Optimistic.voteDutyStore S rho w k).T) :
    ∃ (C : NamedBlock V) (i : Nat) (t : Time), C.erase = B ∧
      NamedRun.acceptsAt S rho i w (.block C) t ∧
      Protocol.proposal_time S.E B.slot ≤ t ∧
      t < Protocol.vote_time S.E k := by
  obtain ⟨n, hn, hbefore⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
    adm.toNamedScheduleWellFormed (Protocol.vote_time S.E k)
  have hBn : B ∈ (rho.stateBefore S n w).st.core.T := by
    simpa [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore,
      Run.storeBeforeTime, hn] using hB
  obtain ⟨C, hCmem, hCerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore S rho n w hBn
  have hprocessed : NamedReceipt.processed (rho.stateBefore S n w).st (.block C) = true := by
    simpa only [Object.processed, NamedReceipt.processed, decide_eq_true_eq] using hCmem
  rcases acceptsAt_block_of_processed S rho w n C hprocessed with
    hgen | ⟨i, hin, t, hacc⟩
  · exfalso
    apply Nat.ne_of_gt hBpos
    rw [← hCerase, hgen]
    rfl
  · obtain ⟨-, e, he, -, het⟩ := hacc.1
    refine ⟨C, i, t, hCerase, hacc, ?_, ?_⟩
    · rw [← hCerase]
      exact proposal_time_le_of_acceptsAt_block S adm hacc
    · rw [← het]
      exact hbefore i e hin he


end Protocol
end DecoupledConsensusModel

end
