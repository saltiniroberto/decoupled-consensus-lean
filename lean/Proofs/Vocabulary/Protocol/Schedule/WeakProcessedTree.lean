module
public import Proofs.Vocabulary.Protocol.Grades.Q10Frame
public import Proofs.Vocabulary.Protocol.Handlers.AdoptionConstructor
import Proofs.Vocabulary.Protocol.Handlers.AcceptanceTiming
import Proofs.Vocabulary.Protocol.Handlers.GoldfishVotePool
import Proofs.Vocabulary.Protocol.Schedule.SlotInduction
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.HonestMajorityCore

@[expose] public section

/-!
# Processed-tree ancestor closure

Every ancestor of a block in an honest validator's frozen processed block tree at its vote duty is
in that tree too.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace WeakGoldfish

open Internal Execution
open Proofs.Optimistic Protocol
open Protocol.HonestWeightMajority
  (on_block_new_timestamp on_tick_emit_proposal_timestamp_block)

variable {V : Type} [DecidableEq V] [Fintype V]


/-! ## Named processed-tree ancestor closure -/

theorem ancestorProcessed_of_voterProcessed
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {w : V} (hw : w ∈ rho.honest) {s : Slot} {B : Block V}
    (hBmem : B ∈ Protocol.voter_processed_block_tree S.E
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.s) :
    ∀ C : Block V, Block.Preceq C B →
      C ∈ Protocol.voter_processed_block_tree S.E
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.s := by
  let duty := Proofs.Optimistic.voteDutyStore S rho w (s + 1)
  have sch : ScheduleWellFormed S rho := AdmissibleCore.toScheduleWellFormed adm
  have hprocessed : B ∈ Protocol.voter_processed_block_tree S.E
      duty.toHealing.toFG.toSG.toGoldfishStore duty.toHealing.s := hBmem
  have hslot : duty.toHealing.s = s + 1 := by
    simpa only [duty, Proofs.Optimistic.toHealing_slot] using
      Proofs.Optimistic.voteDutyStore_slot S rho w (s + 1)
  intro C hCB
  simp only [Protocol.voter_processed_block_tree, Finset.mem_filter] at hprocessed ⊢
  rw [hslot, Nat.add_sub_cancel] at hprocessed ⊢
  rcases hprocessed with ⟨hBT, hstamp | ⟨P, hP, hBP⟩⟩
  · have hBTtime : B ∈
        (rho.stateBeforeTime S (Protocol.vote_time S.E (s + 1)) w).st.core.T := by
      simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, Run.storeBeforeTime,
        Protocol.Store.toHealing] using hBT
    have hstampTime : stampedBefore
        (rho.stateBeforeTime S (Protocol.vote_time S.E (s + 1)) w).st.core.timestamp_block
        (Protocol.view_freeze S.E s) B = true := by
      simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, Run.storeBeforeTime,
        Protocol.Store.toHealing] using hstamp
    obtain ⟨Bn, hBn, hBnErase⟩ :=
      Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
        (Protocol.vote_time S.E (s + 1)) w hBTtime
    have hstampBn : stampedBefore
        (rho.stateBeforeTime S (Protocol.vote_time S.E (s + 1)) w).st.core.timestamp_block
        (Protocol.view_freeze S.E s) Bn.erase = true := by
      simpa only [hBnErase] using hstampTime
    have hBnFreeze :=
      NamedPublicCutBody.body_mem_stateBeforeTime_of_public_stampedBefore S rho
        sch (publicTime_view_freeze S s) hBn hstampBn
    have hcohFreeze := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
      (Protocol.view_freeze S.E s) w).1.1.1
    have hBfreeze : B ∈
        (rho.stateBeforeTime S (Protocol.view_freeze S.E s) w).st.core.T := by
      rw [hcohFreeze.1]
      exact Finset.mem_image.mpr ⟨Bn, hBnFreeze, hBnErase⟩
    have hCfreeze : C ∈
        (rho.stateBeforeTime S (Protocol.view_freeze S.E s) w).st.core.T := by
      exact Proofs.Records.mem_of_preceq
        ((parentClosed_iff _).mp
          (Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho
            (Protocol.view_freeze S.E s) w)).2 C B hBfreeze hCB
    obtain ⟨Cn, hCn, hCnErase⟩ :=
      Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
        (Protocol.view_freeze S.E s) w hCfreeze
    have hCnStamp := NamedBlockStamp.held_body_stampedBefore_stateBeforeTime
      S rho sch w (Protocol.view_freeze S.E s) Cn hCn
    have hcarry := NamedOutageClosure.q10_strict_body_carry S rho
      sch w (le_of_lt (view_freeze_lt_vote_time_succ S.E s)) hCn
    have hCtreeTime : C ∈
        (rho.stateBeforeTime S (Protocol.vote_time S.E (s + 1)) w).st.core.T := by
      have hcohDuty := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
        (Protocol.vote_time S.E (s + 1)) w).1.1.1
      rw [hcohDuty.1]
      exact Finset.mem_image.mpr ⟨Cn, hcarry.1, hCnErase⟩
    have hCtree : C ∈ duty.T := by
      simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, Run.storeBeforeTime] using hCtreeTime
    have hCstampTime : stampedBefore
        (NamedRun.stateBeforeTime S rho
          (Protocol.vote_time S.E (s + 1)) w).st.core.timestamp_block
        (Protocol.view_freeze S.E s) C = true := by
      rw [stampedBefore_eq_occurrenceBefore] at hCnStamp ⊢
      rw [← hCnErase, hcarry.2]
      exact hCnStamp
    have hCstamp : stampedBefore duty.toHealing.toFG.toSG.toGoldfishStore.timestamp_block
        (Protocol.view_freeze S.E s) C = true := by
      simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, Run.storeBeforeTime,
        Protocol.Store.toHealing] using hCstampTime
    exact ⟨by simpa only [Protocol.Store.toHealing] using hCtree,
      Or.inl hCstamp⟩
  · have hPT : P ∈ duty.T := by
      simpa only [Protocol.Store.toHealing] using hP.1
    have hpc := Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho
      (Protocol.vote_time S.E (s + 1)) w
    have hCP : Block.Preceq C P := Block.preceq_trans hCB hBP
    have hCT : C ∈ duty.T :=
      Proofs.Records.mem_of_preceq ((parentClosed_iff _).mp hpc).2 C P hPT hCP
    exact ⟨by simpa only [Protocol.Store.toHealing] using hCT,
      Or.inr ⟨P, hP, hCP⟩⟩


#print axioms ancestorProcessed_of_voterProcessed

end WeakGoldfish
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
