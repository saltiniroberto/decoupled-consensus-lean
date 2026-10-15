module
public import Proofs.Vocabulary.Protocol.Schedule.AdoptionTransport
import Proofs.Vocabulary.Execution.Acceptance
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section

/-!
# Votes at the confirmation read

The votes frozen in a validator's slot-`(s + 1)` vote view are in its slot-`s` confirmation view,
and `ConfirmationAcceptanceTiming` gives the acceptance windows of the votes a confirmation counts.
-/

namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Cutoff transport -/

/-- The slot-`s` view freeze is before the slot-`s` confirmation time. -/
theorem view_freeze_lt_confirmation_time (E : Env V) (s : Slot) :
    Protocol.view_freeze E s < Protocol.confirmation_time E s := by
  have key : ∀ a d : Int, 0 < d → a + 3 * d < a + 6 * d := by
    intro a d hd
    omega
  exact key (E.t s) E.Δ E.Δ_pos

omit [DecidableEq V] [Fintype V] in
private theorem filter_lt_length_mono (rho : Run V) {t t' : Time}
    (h : t ≤ t') :
    (rho.events.filter (fun e => decide (e.time < t))).length ≤
      (rho.events.filter (fun e => decide (e.time < t'))).length :=
  (List.monotone_filter_right rho.events
    (fun e he => by
      simp only [decide_eq_true_eq] at he ⊢
      exact lt_of_lt_of_le he h)).length_le

/-- Every vote in the slot-`s` pool of `w`'s slot-`(s + 1)` vote store, stamped before the slot-`s`
    view freeze, is in the late view of `w`'s slot-`s` confirmation store. -/
theorem voteDutyFrozen_subset_confLate
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    (w : V) (s : Slot) :
    beforeCutoff
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).timestamp_vote
        (Protocol.view_freeze S.E s)
        ((Proofs.Optimistic.voteDutyStore S rho w (s + 1)).pool s) ⊆
      confLate S.E (Proofs.Optimistic.confStore S rho w s) s := by
  let Γ1 := Protocol.vote_time S.E (s + 1)
  let Γ2 := Protocol.confirmation_time S.E s
  let N1 := (rho.events.filter (fun e => decide (e.time < Γ1))).length
  let N2 := (rho.events.filter (fun e => decide (e.time < Γ2))).length
  have h12 : Γ1 ≤ Γ2 := by
    dsimp only [Γ1, Γ2]
    rw [← vote_time_succ_add_delta_eq_confirmation_time S.E s]
    exact Int.le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)
  have hN : N1 ≤ N2 := by
    exact filter_lt_length_mono rho h12
  have hcarry : PoolCarry (rho.stateBefore S N1 w).st.core
      (rho.stateBefore S N2 w).st.core :=
    pool_carry S sch w N2 hN
  intro u hu
  have hstore1 : Proofs.Optimistic.voteDutyStore S rho w (s + 1) =
      Proofs.Optimistic.voteStore S (rho.stateBefore S N1 w).st.core (s + 1) := by
    unfold Proofs.Optimistic.voteDutyStore Run.storeBeforeTime
    rw [congrArg NamedNodeState.st
      (congrFun (Proofs.Optimistic.stateBeforeTime_eq_take S sch Γ1) w)]
  have hu1 : u ∈ beforeCutoff
      (rho.stateBefore S N1 w).st.core.timestamp_vote
      (Protocol.view_freeze S.E s)
      ((rho.stateBefore S N1 w).st.core.pool s) := by
    rw [hstore1] at hu
    simpa only [Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore,
      Protocol.Store.pool] using hu
  have hu2 : u ∈ beforeCutoff
      (rho.stateBefore S N2 w).st.core.timestamp_vote
      (Protocol.view_freeze S.E s)
      ((rho.stateBefore S N2 w).st.core.pool s) :=
    beforeCutoff_subset_of_poolCarry hcarry s (Protocol.view_freeze S.E s) hu1
  have hu3 : u ∈ beforeCutoff
      (rho.stateBefore S N2 w).st.core.timestamp_vote
      (Protocol.confirmation_time S.E s)
      ((rho.stateBefore S N2 w).st.core.pool s) :=
    beforeCutoff_mono _ (le_of_lt (view_freeze_lt_confirmation_time S.E s)) _ hu2
  have hstore2 : Proofs.Optimistic.confStore S rho w s =
      Proofs.Optimistic.tickStore S (rho.stateBefore S N2 w).st.core
        (Protocol.confirmation_time S.E s) := by
    unfold Proofs.Optimistic.confStore Run.storeBeforeTime
    rw [congrArg NamedNodeState.st
      (congrFun (Proofs.Optimistic.stateBeforeTime_eq_take S sch Γ2) w)]
  rw [confLate, hstore2]
  simpa only [Proofs.Optimistic.tickStore, Protocol.Store.pool] using hu3

/-! ## Acceptance windows -/

/-- Every acceptance by `v` of a vote counted in `v`'s slot-`s` confirmation happens at or after the
    slot-`s` proposal time and before the slot-`s` support cutoff. -/
def ConfirmationAcceptanceTiming (S : Setup V) (rho : Run V) (v : V)
    (s : Slot) : Prop :=
  ∀ u ∈ confVotes S.E (Proofs.Optimistic.confStore S rho v s) s,
    ∀ i t, Run.acceptsAt S rho i v (Object.gfVote u) t →
      Protocol.proposal_time S.E s ≤ t ∧
        t < Protocol.support_cutoff S.E s

/-- `ConfirmationAcceptanceTiming` gives `ConfirmationVotesAcceptedInWindow` for `v`'s slot-`s`
    confirmation store. -/
theorem confirmationVotesAcceptedInWindow_of_timing
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} {s : Slot} (htiming : ConfirmationAcceptanceTiming S rho v s) :
    ConfirmationVotesAcceptedInWindow S rho v
      (Proofs.Optimistic.confStore S rho v s) s := by
  intro u hu
  have hupool : u ∈ (Proofs.Optimistic.confStore S rho v s).pool s := by
    rw [confVotes, Finset.mem_filter, confEarly, beforeCutoff,
      Finset.mem_filter] at hu
    exact hu.1.1
  obtain ⟨n, hn, -⟩ :=
    Proofs.Bridges.stateBeforeTime_eq_stateBefore S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
      (Protocol.confirmation_time S.E s)
  have hstoreEq : Proofs.Optimistic.confStore S rho v s =
      Proofs.Optimistic.tickStore S (rho.stateBefore S n v).st.core
        (Protocol.confirmation_time S.E s) := by
    unfold Proofs.Optimistic.confStore Run.storeBeforeTime
    rw [congrArg NamedNodeState.st (congrFun hn v)]
  have huprefix : u ∈ (rho.stateBefore S n v).st.core.pool s := by
    rw [hstoreEq] at hupool
    simpa only [Proofs.Optimistic.tickStore, Protocol.Store.pool] using hupool
  have hulist : u ∈ (rho.stateBefore S n v).st.core.gf_votes s := by
    simpa only [Protocol.Store.pool, List.mem_toFinset] using huprefix
  have hus : u.slot = s :=
    (poolStamps_stateBefore S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed v n).slot
      s u hulist
  have hprocessed : Object.processed
      (rho.stateBefore S n v).st (Object.gfVote u) = true := by
    simp only [Object.processed, NamedReceipt.processed, decide_eq_true_eq]
    rw [hus]
    exact huprefix
  obtain ⟨i, -, t, hacc⟩ :=
    acceptsAt_gfVote_of_processed S rho v n u hprocessed
  obtain ⟨hlo, hhi⟩ := htiming u hu i t hacc
  exact ⟨i, t, hacc, hus, hlo, hhi⟩


end Protocol
end DecoupledConsensusModel

end
