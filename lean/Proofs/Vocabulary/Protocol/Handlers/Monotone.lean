module
public import Proofs.Vocabulary.Protocol.Handlers.Bridges
public import Proofs.Vocabulary.Protocol.Handlers.ConfirmationPolicy
public import Proofs.Vocabulary.Internal.Legacy.Definitions.Confirmation
import Mathlib.Data.Int.ConditionallyCompleteOrder

@[expose] public section

/-!
# Persistence of the confirmation record

Every handler and duty other than the confirmation update leaves `Σ.latest_confirmed` unchanged, and
a later read is an earlier read continued by the events in between.
-/

namespace DecoupledConsensusModel
namespace Protocol

open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Internal
open Execution
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## `Σ.latest_confirmed` is written by the confirmation update alone -/

omit [Fintype V] in
/-- `update_finality` leaves `Σ.latest_confirmed` unchanged. -/
theorem update_finality_latest (st : Protocol.Store V) (σ : ChainState V) :
    (Protocol.update_finality st σ).latest_confirmed = st.latest_confirmed := by
  simp only [Protocol.update_finality]
  split_ifs <;> rfl

omit [Fintype V] in
/-- `on_goldfish_vote` leaves `Σ.latest_confirmed` unchanged. -/
theorem on_goldfish_vote_latest (st : Protocol.Store V) (u : GoldfishVote V) :
    (Protocol.on_goldfish_vote st u).latest_confirmed = st.latest_confirmed := by
  simp only [Protocol.on_goldfish_vote]
  split_ifs <;> rfl

/-- `on_goldfish_vote_checked` leaves `Σ.latest_confirmed` unchanged. -/
theorem on_goldfish_vote_checked_latest (E : Env V) (st : Protocol.Store V)
    (u : GoldfishVote V) :
    (Protocol.on_goldfish_vote_checked E st u).latest_confirmed = st.latest_confirmed := by
  simp only [Protocol.on_goldfish_vote_checked]
  split_ifs
  · exact on_goldfish_vote_latest st u
  · rfl


/-- A fold of `on_goldfish_vote_checked` leaves `Σ.latest_confirmed` unchanged. -/
theorem foldl_on_goldfish_vote_checked_latest (E : Env V)
    (l : List (GoldfishVote V)) (st : Protocol.Store V) :
    (l.foldl (Protocol.on_goldfish_vote_checked E) st).latest_confirmed =
      st.latest_confirmed := by
  induction l generalizing st with
  | nil => rfl
  | cons u l ih =>
      rw [List.foldl_cons, ih, on_goldfish_vote_checked_latest]

omit [Fintype V] in
/-- `on_sg_vote` leaves `Σ.latest_confirmed` unchanged. -/
theorem on_sg_vote_latest (hc : HealConfig) (st : Protocol.Store V)
    (a : CombinedAttestation V) :
    (Protocol.on_sg_vote hc st a).latest_confirmed = st.latest_confirmed := by
  simp only [Protocol.on_sg_vote]
  split_ifs <;> rfl


theorem on_block_using_latest (E : Env V) (st : Protocol.Store V) (B : Block V)
    (buildState : ChainState V → ChainState V) :
    (Protocol.on_block_using E st B buildState).latest_confirmed = st.latest_confirmed := by
  simp only [Protocol.on_block_using]
  split_ifs <;>
    first
      | rfl
      | rw [update_finality_latest, foldl_on_goldfish_vote_checked_latest]

theorem on_block_checked_using_latest (handle : Protocol.Store V → Protocol.Store V)
    (hc : HealConfig) (st : Protocol.Store V) (B : Block V)
    (hhandle : (handle st).latest_confirmed = st.latest_confirmed) :
    (Protocol.on_block_checked_using handle hc st B).latest_confirmed = st.latest_confirmed := by
  simp only [Protocol.on_block_checked_using]
  split_ifs
  · exact hhandle
  · rfl

private theorem commitBlock_latest (before : Protocol.NamedStore V) (after : Protocol.Store V)
    (B : NamedBlock V) :
    (Protocol.NamedStore.commitBlock before after B).latest_confirmed = after.latest_confirmed := by
  simp only [Protocol.NamedStore.commitBlock]
  split_ifs <;> rfl

theorem process_block_core_latest (E : Env V) (hc : HealConfig) (cfg : HeightConfig)
    (st : Protocol.NamedStore V) (B : NamedBlock V) :
    (Protocol.NamedStore.process_block_core E hc cfg st B).latest_confirmed =
      st.latest_confirmed := by
  simp only [Protocol.NamedStore.process_block_core]
  split_ifs with hp
  all_goals first
    | rfl
    | (rw [commitBlock_latest]
       exact on_block_checked_using_latest _ hc st.core B.erase
         (on_block_using_latest E st.core B.erase _))

theorem admit_row_latest (hc : HealConfig) (st : Protocol.NamedStore V)
    (row : NamedAttestation V) :
    (Protocol.NamedAdmission.admit_row hc st row).latest_confirmed = st.latest_confirmed := by
  simp only [Protocol.NamedAdmission.admit_row]
  split_ifs <;> exact on_sg_vote_latest hc st.core row.erase

private theorem foldl_admit_row_latest (hc : HealConfig)
    (l : List (NamedAttestation V)) (st : Protocol.NamedStore V) :
    (l.foldl (Protocol.NamedAdmission.admit_row hc) st).latest_confirmed =
      st.latest_confirmed := by
  induction l generalizing st with
  | nil => rfl
  | cons row l ih => rw [List.foldl_cons, ih, admit_row_latest]

theorem admit_rows_latest (hc : HealConfig) (st : Protocol.NamedStore V)
    (rows : List (NamedAttestation V)) :
    (Protocol.NamedAdmission.admit_rows hc st rows).latest_confirmed = st.latest_confirmed :=
  foldl_admit_row_latest hc rows st

theorem admit_carried_latest (admission : Protocol.CarriedAdmission) (hc : HealConfig)
    (before after : Protocol.NamedStore V) (B : NamedBlock V) :
    (Protocol.NamedAdmission.admit_carried admission hc before after B).latest_confirmed =
      after.latest_confirmed := by
  cases admission with
  | alsoCarried =>
      simp only [Protocol.NamedAdmission.admit_carried]
      split_ifs
      · exact admit_rows_latest hc after B.attestations
      · rfl

theorem on_block_with_latest (admission : Protocol.CarriedAdmission) (E : Env V)
    (hc : HealConfig) (cfg : HeightConfig) (st : Protocol.NamedStore V) (B : NamedBlock V) :
    (Protocol.NamedAdmission.on_block_with admission E hc cfg st B).latest_confirmed =
      st.latest_confirmed := by
  simp only [Protocol.NamedAdmission.on_block_with]
  rw [admit_carried_latest]
  exact process_block_core_latest E hc cfg st B

theorem propose_block_with_latest (contract : Protocol.GradeContract V) (E : Env V)
    (hc : HealConfig) (cfg : HeightConfig) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) :
    (Protocol.NamedDuties.propose_block_with contract E hc cfg nd st).1.latest_confirmed =
      st.latest_confirmed := by
  simp only [Protocol.NamedDuties.propose_block_with]
  cases Protocol.NamedActions.proposal_with contract .poolAndCarried E hc nd st with
  | none => rfl
  | some B => exact on_block_with_latest .alsoCarried E hc cfg st B

theorem goldfish_vote_with_latest (contract : Protocol.GradeContract V) (E : Env V)
    (hc : HealConfig) (nd : Protocol.Node V) (st : Protocol.Store V) :
    (Protocol.goldfish_vote_with contract E hc nd st).1.latest_confirmed = st.latest_confirmed := by
  simp only [Protocol.goldfish_vote_with]
  split_ifs
  · exact on_goldfish_vote_checked_latest E st _
  · rfl

theorem named_goldfish_vote_with_latest (contract : Protocol.GradeContract V) (E : Env V)
    (hc : HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V) :
    (Protocol.NamedDuties.goldfish_vote_with contract E hc nd st).1.latest_confirmed =
      st.latest_confirmed := by
  simp only [Protocol.NamedDuties.goldfish_vote_with]
  exact goldfish_vote_with_latest contract E hc nd st.core

theorem attest_with_latest (contract : Protocol.GradeContract V) (E : Env V)
    (hc : HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) :
    (Protocol.NamedDuties.attest_with contract E hc nd st record).1.latest_confirmed =
      st.latest_confirmed := by
  simp only [Protocol.NamedDuties.attest_with]
  exact admit_row_latest hc st _

/-! ## The schedule: `[0, t]` is a prefix of `[0, t']` -/

/-- In a well-formed schedule, the events are sorted by time. -/
theorem pairwise_time_le (S : Setup V) {ρ : Run V} (sch : ScheduleWellFormed S ρ) :
    ρ.events.Pairwise (fun e f => e.time ≤ f.time) := by
  refine sch.sorted.imp ?_
  intro e f h
  rcases Prod.Lex.le_iff.mp h with h | ⟨h, _⟩
  · exact le_of_lt h
  · exact le_of_eq h

omit [DecidableEq V] [Fintype V] in

/-- In a time-sorted list, the events at or before `t` are a prefix of the events at or before `t'`,
    for `t ≤ t'`. -/
theorem filter_time_prefix {t t' : Time} (h : t ≤ t') :
    ∀ (l : List (Event V)), l.Pairwise (fun e f => e.time ≤ f.time) →
      l.filter (fun e => decide (e.time ≤ t)) <+:
        l.filter (fun e => decide (e.time ≤ t'))
  | [], _ => by simp
  | a :: l, hs => by
      rw [List.pairwise_cons] at hs
      by_cases ha : a.time ≤ t
      · have ha' : a.time ≤ t' := le_trans ha h
        rw [List.filter_cons_of_pos (by simpa using ha),
          List.filter_cons_of_pos (by simpa using ha')]
        obtain ⟨m, hm⟩ := filter_time_prefix h l hs.2
        exact ⟨m, by rw [List.cons_append, hm]⟩
      · have hnil : l.filter (fun e => decide (e.time ≤ t)) = [] := by
          refine List.filter_eq_nil_iff.mpr ?_
          intro f hf hcon
          exact ha (le_trans (hs.1 f hf) (by simpa using hcon))
        rw [List.filter_cons_of_neg (by simpa using ha), hnil]
        exact List.nil_prefix

/-- For `t ≤ t'`, the read at `t'` is the read at `t` continued by a list of events. -/
theorem stateAt_eq_foldl (S : Setup V) {ρ : Run V} (sch : ScheduleWellFormed S ρ)
    {t t' : Time} (h : t ≤ t') :
    ∃ m : List (Event V),
      NamedRun.readAt S ρ t' = m.foldl (NamedWorld.step S) (NamedRun.readAt S ρ t) := by
  obtain ⟨m, hm⟩ := filter_time_prefix h ρ.events (pairwise_time_le S sch)
  refine ⟨m, ?_⟩
  simp only [NamedRun.readAt]
  rw [← hm, List.foldl_append]


end Protocol
end DecoupledConsensusModel

end
