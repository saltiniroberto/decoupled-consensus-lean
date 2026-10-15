module
public import Proofs.Vocabulary.Protocol.Handlers.CommitteePools
public import Proofs.Vocabulary.Protocol.Grades.Main
public import Proofs.Vocabulary.Protocol.Handlers.Pool
import Proofs.Vocabulary.Protocol.Handlers.Bridges

@[expose] public section

/-!
# Vote-set validity

The pool, the cutoff views, the confirmation late view and the voter view of a store are valid vote
sets for their slot.
-/
namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

theorem voteSetValid_pool {E : Env V} {st : Protocol.Store V}
    (hslots : PoolStamps st) (hcommittee : CommitteePools E st) (k : Slot) :
    Protocol.VoteSetValid E k (st.pool k) := by
  intro u hu
  refine ⟨?_, ?_⟩
  · apply hslots.slot k u
    simpa only [Protocol.Store.pool, List.mem_toFinset] using hu
  · exact hcommittee.mem_committee hu

theorem voteSetValid_beforeCutoff {E : Env V} {st : Protocol.Store V}
    (hslots : PoolStamps st) (hcommittee : CommitteePools E st)
    (k : Slot) (ts : TimestampMap (GoldfishVote V)) (Gamma : Time) :
    Protocol.VoteSetValid E k (beforeCutoff ts Gamma (st.pool k)) := by
  apply (voteSetValid_pool hslots hcommittee k).mono
  intro u hu
  rw [beforeCutoff, Finset.mem_filter] at hu
  exact hu.1


theorem voteSetValid_confLate {E : Env V} {st : Protocol.Store V}
    (hslots : PoolStamps st) (hcommittee : CommitteePools E st) (s : Slot) :
    Protocol.VoteSetValid E s (confLate E st s) := by
  exact voteSetValid_beforeCutoff hslots hcommittee s st.timestamp_vote
    (Protocol.confirmation_time E s)


theorem voteSetValid_pool_stateBefore (S : Setup V) {rho : Run V}
    (sch : ScheduleWellFormed S rho) (v : V) (n : Nat) (k : Slot) :
    Protocol.VoteSetValid S.E k ((rho.stateBefore S n v).st.pool k) := by
  exact voteSetValid_pool
    (poolStamps_stateBefore S sch v n)
    (CommitteePools.stateBefore S rho v n) k


theorem voteSetValid_confLate_stateBefore (S : Setup V) {rho : Run V}
    (sch : ScheduleWellFormed S rho) (v : V) (n : Nat) (s : Slot) :
    Protocol.VoteSetValid S.E s (confLate S.E (rho.stateBefore S n v).st.core s) := by
  exact voteSetValid_confLate
    (poolStamps_stateBefore S sch v n)
    (CommitteePools.stateBefore S rho v n) s


theorem voteSetValid_confLate_stateBeforeTime (S : Setup V) {rho : Run V}
    (sch : ScheduleWellFormed S rho) (v : V) (t : Time) (s : Slot) :
    Protocol.VoteSetValid S.E s
      (confLate S.E (rho.stateBeforeTime S t v).st.core s) := by
  obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S sch t
  rw [hn]
  exact voteSetValid_confLate_stateBefore S sch v n s


theorem voteSetValid_voter_view_of_carried {E : Env V} {st : Protocol.Store V}
    (s : Slot)
    (hpool : Protocol.VoteSetValid E (s - 1) (st.pool (s - 1)))
    (hcarried : ∀ B ∈ st.T, ∀ u ∈ B.gf_votes,
      u.val_index ∈ E.committee u.slot) :
    Protocol.VoteSetValid E (s - 1)
      (Protocol.voter_view E st.toHealing.toFG.toSG.toGoldfishStore s) := by
  intro u hu
  rw [Protocol.voter_view, Finset.mem_union] at hu
  rcases hu with hpoolArm | hcarriedArm
  · apply hpool
    rw [beforeCutoff, Finset.mem_filter] at hpoolArm
    exact hpoolArm.1
  · rw [Finset.mem_biUnion] at hcarriedArm
    obtain ⟨B, hBT, huB⟩ := hcarriedArm
    rw [Finset.mem_filter] at hBT huB
    refine ⟨huB.2, ?_⟩
    have hcommittee := hcarried B hBT.1 u (List.mem_toFinset.mp huB.1)
    simpa only [huB.2] using hcommittee

#print axioms voteSetValid_pool
#print axioms voteSetValid_beforeCutoff
#print axioms voteSetValid_confLate
#print axioms voteSetValid_pool_stateBefore
#print axioms voteSetValid_confLate_stateBefore
#print axioms voteSetValid_confLate_stateBeforeTime
#print axioms voteSetValid_voter_view_of_carried

end Protocol
end DecoupledConsensusModel

end
