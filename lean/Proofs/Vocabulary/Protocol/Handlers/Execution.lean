module
public import Proofs.Vocabulary.Internal.Definitions.NamedExecutionQueries
public import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.Admissible
public import Mathlib.CategoryTheory.Category.Basic
public import Proofs.Vocabulary.ModelProperties.NamedNode_initial
public import Proofs.Vocabulary.ModelProperties.NamedStore_initial
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Order.ConditionallyCompleteLattice.Basic

@[expose] public section

/-!
# The execution layer and the store clock

The public times are the four per-slot times, and a store's clock and slot are written by ticks
alone: every handler and duty leaves them unchanged, so a node's clock at any state of a run is the
time of its last tick.
-/

namespace DecoupledConsensusModel
namespace Execution

open Protocol (ChainState HeightConfig)

variable {V : Type} [DecidableEq V] [Fintype V]


/-! ## The tick schedule -/

/-- The public times are exactly the proposal, vote, support-cutoff and view-freeze times of the
    slots. -/
theorem publicTime_iff (S : Setup V) (t : Time) :
    PublicTime S t ↔
      ∃ s : Slot, t = Protocol.proposal_time S.E s ∨ t = Protocol.vote_time S.E s ∨
        t = Protocol.support_cutoff S.E s ∨ t = Protocol.view_freeze S.E s := by
  unfold PublicTime Protocol.proposal_time Protocol.vote_time Protocol.support_cutoff
    Protocol.view_freeze Env.t slotStart
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨k / 4, ?_⟩
    have hk : (k : Time) = 4 * ((k / 4 : Nat) : Time) + ((k % 4 : Nat) : Time) := by
      have h : 4 * (k / 4) + k % 4 = k := Nat.div_add_mod k 4
      exact_mod_cast h.symm
    have h4 : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
    rcases h4 with h | h | h | h
    · exact Or.inl (by rw [hk, h]; push_cast; ring)
    · exact Or.inr (Or.inl (by rw [hk, h]; push_cast; ring))
    · exact Or.inr (Or.inr (Or.inl (by rw [hk, h]; push_cast; ring)))
    · exact Or.inr (Or.inr (Or.inr (by rw [hk, h]; push_cast; ring)))
  · rintro ⟨s, h | h | h | h⟩
    · exact ⟨4 * s, by rw [h]; push_cast; ring⟩
    · exact ⟨4 * s + 1, by rw [h]; push_cast; ring⟩
    · exact ⟨4 * s + 2, by rw [h]; push_cast; ring⟩
    · exact ⟨4 * s + 3, by rw [h]; push_cast; ring⟩

/-! ## The store clock is written by ticks alone -/

omit [Fintype V] in
/-- `update_finality` leaves `Σ.t` unchanged. -/
theorem update_finality_time (st : Protocol.Store V) (σ : ChainState V) :
    (Protocol.update_finality st σ).t = st.t := by
  simp only [Protocol.update_finality]
  split_ifs <;> rfl

omit [Fintype V] in
/-- `on_goldfish_vote` leaves `Σ.t` unchanged. -/
theorem on_goldfish_vote_time (st : Protocol.Store V) (u : GoldfishVote V) :
    (Protocol.on_goldfish_vote st u).t = st.t := by
  simp only [Protocol.on_goldfish_vote]
  split_ifs <;> rfl

/-- `on_goldfish_vote_checked` leaves `Σ.t` unchanged. -/
theorem on_goldfish_vote_checked_time (E : Env V) (st : Protocol.Store V)
    (u : GoldfishVote V) :
    (Protocol.on_goldfish_vote_checked E st u).t = st.t := by
  simp only [Protocol.on_goldfish_vote_checked]
  split_ifs
  · exact on_goldfish_vote_time st u
  · rfl


/-- A fold of `on_goldfish_vote_checked` leaves `Σ.t` unchanged. -/
theorem foldl_on_goldfish_vote_checked_time (E : Env V)
    (l : List (GoldfishVote V)) (st : Protocol.Store V) :
    (l.foldl (Protocol.on_goldfish_vote_checked E) st).t = st.t := by
  induction l generalizing st with
  | nil => rfl
  | cons u l ih =>
      rw [List.foldl_cons, ih, on_goldfish_vote_checked_time]


omit [Fintype V] in
/-- `on_sg_vote` leaves `Σ.t` unchanged. -/
theorem on_sg_vote_time (hc : Protocol.HealConfig) (st : Protocol.Store V)
    (a : CombinedAttestation V) : (Protocol.on_sg_vote hc st a).t = st.t := by
  simp only [Protocol.on_sg_vote]
  split_ifs <;> rfl

omit [Fintype V] in
/-- `update_finality` leaves `Σ.s` unchanged. -/
theorem update_finality_slot (st : Protocol.Store V) (σ : ChainState V) :
    (Protocol.update_finality st σ).s = st.s := by
  simp only [Protocol.update_finality]
  split_ifs <;> rfl

omit [Fintype V] in
/-- `on_goldfish_vote` leaves `Σ.s` unchanged. -/
theorem on_goldfish_vote_slot (st : Protocol.Store V) (u : GoldfishVote V) :
    (Protocol.on_goldfish_vote st u).s = st.s := by
  simp only [Protocol.on_goldfish_vote]
  split_ifs <;> rfl

/-- `on_goldfish_vote_checked` leaves `Σ.s` unchanged. -/
theorem on_goldfish_vote_checked_slot (E : Env V) (st : Protocol.Store V)
    (u : GoldfishVote V) :
    (Protocol.on_goldfish_vote_checked E st u).s = st.s := by
  simp only [Protocol.on_goldfish_vote_checked]
  split_ifs
  · exact on_goldfish_vote_slot st u
  · rfl

/-- A fold of `on_goldfish_vote_checked` leaves `Σ.s` unchanged. -/
theorem foldl_on_goldfish_vote_checked_slot (E : Env V)
    (l : List (GoldfishVote V)) (st : Protocol.Store V) :
    (l.foldl (Protocol.on_goldfish_vote_checked E) st).s = st.s := by
  induction l generalizing st with
  | nil => rfl
  | cons u l ih =>
      rw [List.foldl_cons, ih, on_goldfish_vote_checked_slot]

omit [Fintype V] in
/-- `on_sg_vote` leaves `Σ.s` unchanged. -/
theorem on_sg_vote_slot (hc : Protocol.HealConfig) (st : Protocol.Store V)
    (a : CombinedAttestation V) : (Protocol.on_sg_vote hc st a).s = st.s := by
  simp only [Protocol.on_sg_vote]
  split_ifs <;> rfl

/-! ### The shared block body -/

/-- `on_block_using` leaves `Σ.t` unchanged, whatever state it builds. -/
theorem on_block_using_time (E : Env V) (st : Protocol.Store V) (B : Block V)
    (build : ChainState V → ChainState V) :
    (Protocol.on_block_using E st B build).t = st.t := by
  simp only [Protocol.on_block_using]
  split_ifs <;>
    first
      | rfl
      | rw [update_finality_time, foldl_on_goldfish_vote_checked_time E]

/-- `on_block_using` leaves `Σ.s` unchanged, whatever state it builds. -/
theorem on_block_using_slot (E : Env V) (st : Protocol.Store V) (B : Block V)
    (build : ChainState V → ChainState V) :
    (Protocol.on_block_using E st B build).s = st.s := by
  simp only [Protocol.on_block_using]
  split_ifs <;>
    first
      | rfl
      | rw [update_finality_slot, foldl_on_goldfish_vote_checked_slot E]

/-! ### The named store steps -/

omit [Fintype V] in
/-- The core after `commitBlock` is the store it is given. -/
theorem commitBlock_core (before : Protocol.NamedStore V) (after : Protocol.Store V)
    (B : NamedBlock V) : (Protocol.NamedStore.commitBlock before after B).core = after := by
  unfold Protocol.NamedStore.commitBlock
  split_ifs <;> rfl

omit [Fintype V] in
/-- The core of `admit_row` is `on_sg_vote` applied to the row's erasure. -/
theorem admit_row_core (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (a : NamedAttestation V) :
    (Protocol.NamedAdmission.admit_row hc st a).core =
      Protocol.on_sg_vote hc st.core a.erase := by
  dsimp only [Protocol.NamedAdmission.admit_row]
  split_ifs <;> rfl

omit [Fintype V] in
/-- `admit_row` leaves the core's clock and slot unchanged. -/
theorem admit_row_clock (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (a : NamedAttestation V) :
    (Protocol.NamedAdmission.admit_row hc st a).core.t = st.core.t ∧
      (Protocol.NamedAdmission.admit_row hc st a).core.s = st.core.s := by
  rw [admit_row_core]
  exact ⟨on_sg_vote_time hc st.core a.erase, on_sg_vote_slot hc st.core a.erase⟩

omit [Fintype V] in
/-- `admit_rows` leaves the core's clock and slot unchanged. -/
theorem admit_rows_clock (hc : Protocol.HealConfig) :
    ∀ (rows : List (NamedAttestation V)) (st : Protocol.NamedStore V),
      (Protocol.NamedAdmission.admit_rows hc st rows).core.t = st.core.t ∧
        (Protocol.NamedAdmission.admit_rows hc st rows).core.s = st.core.s
  | [], _ => ⟨rfl, rfl⟩
  | a :: rows, st => by
      have h1 := admit_row_clock hc st a
      have h2 := admit_rows_clock hc rows (Protocol.NamedAdmission.admit_row hc st a)
      exact ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

/-- `process_block_core` leaves the core's clock and slot unchanged. -/
theorem process_block_core_clock (E : Env V) (hc : Protocol.HealConfig)
    (cfg : HeightConfig) (st : Protocol.NamedStore V) (B : NamedBlock V) :
    (Protocol.NamedStore.process_block_core E hc cfg st B).core.t = st.core.t ∧
      (Protocol.NamedStore.process_block_core E hc cfg st B).core.s = st.core.s := by
  dsimp only [Protocol.NamedStore.process_block_core]
  split_ifs with hp
  · rw [commitBlock_core]
    dsimp only [Protocol.on_block_checked_using]
    split_ifs
    · exact ⟨on_block_using_time E st.core B.erase _, on_block_using_slot E st.core B.erase _⟩
    · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

/-- `on_block_with` leaves the core's clock and slot unchanged. -/
theorem on_block_with_clock (adm : Protocol.CarriedAdmission) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : HeightConfig) (st : Protocol.NamedStore V)
    (B : NamedBlock V) :
    (Protocol.NamedAdmission.on_block_with adm E hc cfg st B).core.t = st.core.t ∧
      (Protocol.NamedAdmission.on_block_with adm E hc cfg st B).core.s = st.core.s := by
  have hb := process_block_core_clock E hc cfg st B
  cases adm with
  | alsoCarried =>
      dsimp only [Protocol.NamedAdmission.on_block_with, Protocol.NamedAdmission.admit_carried]
      split_ifs
      · have h := admit_rows_clock hc B.attestations
          (Protocol.NamedStore.process_block_core E hc cfg st B)
        exact ⟨h.1.trans hb.1, h.2.trans hb.2⟩
      · exact hb

/-! ### The four named duties -/

/-- The named proposal duty leaves the core's clock and slot unchanged. -/
theorem named_propose_clock (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : HeightConfig) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) :
    (Protocol.NamedDuties.propose_block_with gc E hc cfg nd st).1.core.t = st.core.t ∧
      (Protocol.NamedDuties.propose_block_with gc E hc cfg nd st).1.core.s = st.core.s := by
  unfold Protocol.NamedDuties.propose_block_with
  split
  · exact ⟨rfl, rfl⟩
  · exact on_block_with_clock .alsoCarried E hc cfg st _

/-- The named Goldfish vote duty leaves the core's clock and slot unchanged. -/
theorem named_vote_clock (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V) :
    (Protocol.NamedDuties.goldfish_vote_with gc E hc nd st).1.core.t = st.core.t ∧
      (Protocol.NamedDuties.goldfish_vote_with gc E hc nd st).1.core.s = st.core.s := by
  dsimp only [Protocol.NamedDuties.goldfish_vote_with, Protocol.goldfish_vote_with]
  split_ifs
  · exact ⟨on_goldfish_vote_checked_time E st.core _, on_goldfish_vote_checked_slot E st.core _⟩
  · exact ⟨rfl, rfl⟩

/-- The named confirmation duty leaves the core's clock and slot unchanged. -/
theorem named_confirmation_clock (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (st : Protocol.NamedStore V) (s : Slot) :
    (Protocol.NamedDuties.update_confirmation_with gc E hc st s).core.t = st.core.t ∧
      (Protocol.NamedDuties.update_confirmation_with gc E hc st s).core.s = st.core.s :=
  ⟨rfl, rfl⟩

/-- The named attestation duty leaves the core's clock and slot unchanged. -/
theorem named_attest_clock (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) :
    (Protocol.NamedDuties.attest_with gc E hc nd st record).1.core.t = st.core.t ∧
      (Protocol.NamedDuties.attest_with gc E hc nd st record).1.core.s = st.core.s :=
  admit_row_clock hc st _

/-- A store property preserved by setting the clock and by each of the four named duties holds of
    the store a named tick returns. -/
theorem named_tick_preserves (P : Protocol.NamedStore V → Prop)
    (gc : Protocol.GradeContract V) (E : Env V) (hc : Protocol.HealConfig)
    (cfg : HeightConfig) (nd : Protocol.Node V)
    (hp : ∀ st, P st → P (Protocol.NamedDuties.propose_block_with gc E hc cfg nd st).1)
    (hv : ∀ st, P st → P (Protocol.NamedDuties.goldfish_vote_with gc E hc nd st).1)
    (hcf : ∀ st s, P st → P (Protocol.NamedDuties.update_confirmation_with gc E hc st s))
    (ha : ∀ st record, P st → P (Protocol.NamedDuties.attest_with gc E hc nd st record).1)
    (st : Protocol.NamedStore V) (record : Protocol.NamedRecord) (t : Time)
    (h : P (Protocol.NamedStore.setClock E st t)) :
    P (Protocol.NamedTick.tick gc E hc cfg nd st record t).1 := by
  dsimp only [Protocol.NamedTick.tick, Protocol.TickScheduler.runWith,
    Protocol.NamedTick.namedOps]
  split_ifs <;> solve_by_elim (maxDepth := 8) [hp, hv, hcf, ha, h]

/-- A named tick to time `t` sets the core's clock to `t` and its slot to the slot of `t`. -/
theorem named_tick_clock (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : HeightConfig) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) (record : Protocol.NamedRecord) (t : Time) :
    (Protocol.NamedTick.tick gc E hc cfg nd st record t).1.core.t = t ∧
      (Protocol.NamedTick.tick gc E hc cfg nd st record t).1.core.s = E.slotOf t := by
  refine named_tick_preserves
    (fun st' => st'.core.t = t ∧ st'.core.s = E.slotOf t) gc E hc cfg nd ?_ ?_ ?_ ?_ st record t
    ⟨rfl, rfl⟩
  · intro st' h
    exact ⟨(named_propose_clock gc E hc cfg nd st').1.trans h.1,
      (named_propose_clock gc E hc cfg nd st').2.trans h.2⟩
  · intro st' h
    exact ⟨(named_vote_clock gc E hc nd st').1.trans h.1,
      (named_vote_clock gc E hc nd st').2.trans h.2⟩
  · intro st' s h
    exact ⟨(named_confirmation_clock gc E hc st' s).1.trans h.1,
      (named_confirmation_clock gc E hc st' s).2.trans h.2⟩
  · intro st' record' h
    exact ⟨(named_attest_clock gc E hc nd st' record').1.trans h.1,
      (named_attest_clock gc E hc nd st' record').2.trans h.2⟩

/-! ### The named execution steps -/

/-- The named tick sets the store's clock and slot from the tick's time. -/
theorem on_tick_emit_time (S : Setup V) : Execution.NamedTickTimeQuery S := by
  intro v before t
  exact named_tick_clock _ S.E S.hc S.cfg (S.node v) before.st before.record t

/-- Processing a delivered object leaves the store's clock and slot unchanged. -/
theorem process_time (S : Setup V) : Execution.NamedProcessTimeQuery S := by
  intro n o
  cases o with
  | block B => exact on_block_with_clock .alsoCarried S.E S.hc S.cfg n.st B
  | gfVote u =>
      exact ⟨on_goldfish_vote_checked_time S.E n.st.core u,
        on_goldfish_vote_checked_slot S.E n.st.core u⟩
  | attest a => exact admit_row_clock S.hc n.st a

/-- After an event list, a node's `Σ.t` is the time of its last tick in the list, or its starting
    clock if it has none. -/
theorem foldl_step_time (S : Setup V) : Execution.NamedFoldStepTimeQuery S := by
  intro w l v
  induction l generalizing w with
  | nil => rfl
  | cons e l ih =>
      rw [List.foldl_cons, ih]
      cases hl : Run.lastTickIn v l with
      | some t' => simp [Run.lastTickIn, hl]
      | none =>
          simp only [Run.lastTickIn, hl, Option.getD]
          cases e with
          | tick u t' =>
              by_cases hu : u = v
              · subst hu
                simp only [Execution.NamedWorld.step, Function.update_self]
                exact (on_tick_emit_time S u (w u) t').1
              · simp only [Execution.NamedWorld.step,
                  Function.update_of_ne (Ne.symm hu), if_neg hu]
          | deliver u o t' =>
              by_cases hu : u = v
              · subst hu
                simp only [Execution.NamedWorld.step, Function.update_self]
                exact (process_time S (w u) o).1
              · simp only [Execution.NamedWorld.step, Function.update_of_ne (Ne.symm hu)]

/-- The clock of `v`'s store after `i` events is the time of `v`'s last tick among them, or zero if
    there is none. -/
theorem store_time_eq_lastTick (S : Setup V) (rho : Execution.NamedRun V) :
    Execution.NamedStoreTimeEqLastTickQuery S rho := by
  intro v i
  have h := foldl_step_time S (Execution.NamedWorld.init : Execution.NamedWorld V)
    (rho.events.take i) v
  rw [show ((Execution.NamedWorld.init : Execution.NamedWorld V) v).st.core.t
      = (0 : Time) by
        show (Execution.NamedNode.initial : Execution.NamedNodeState V).st.core.t = 0
        rw [Proofs.ModelProperties.initial_st, Proofs.ModelProperties.initial_core_t]] at h
  exact h

omit [Fintype V] in
/-- A last tick recorded by `Run.lastTickIn` is an event of the list. -/
theorem tick_mem_of_lastTickIn (v : V) :
    ∀ (l : List (Event V)) {t : Time}, Run.lastTickIn v l = some t → Event.tick v t ∈ l
  | [], _, h => by simp [Run.lastTickIn] at h
  | e :: l, t, h => by
      simp only [Run.lastTickIn] at h
      cases hl : Run.lastTickIn v l with
      | some t' =>
          rw [hl] at h
          have ht : t' = t := by simpa using h
          subst ht
          exact List.mem_cons_of_mem _ (tick_mem_of_lastTickIn v l hl)
      | none =>
          rw [hl] at h
          cases e with
          | tick u t'' =>
              by_cases hu : u = v
              · subst hu
                have ht : t'' = t := by simpa using h
                subst ht
                exact List.mem_cons_self ..
              · simp [hu] at h
          | deliver u o t'' => simp at h

/-- In a well-formed schedule, every event of the first `i` events is at most as late as event `i`. -/
theorem time_le_of_mem_take (S : Setup V) {ρ : Run V} (sch : ScheduleWellFormed S ρ)
    {i : Nat} {f : Event V} (hf : ρ.events[i]? = some f) :
    ∀ e ∈ ρ.events.take i, e.time ≤ f.time := by
  intro e he
  obtain ⟨hi, hget⟩ := List.getElem?_eq_some_iff.mp hf
  have hsplit : ρ.events = ρ.events.take i ++ f :: ρ.events.drop (i + 1) := by
    conv_lhs => rw [← List.take_append_drop i ρ.events]
    rw [List.drop_eq_getElem_cons hi, hget]
  have hpair := sch.sorted
  change List.Pairwise (fun e f : Event V => Event.key e ≤ Event.key f) ρ.events at hpair
  rw [hsplit] at hpair
  have hkey : Event.key e ≤ Event.key f :=
    (List.pairwise_append.mp hpair).2.2 e he f (List.mem_cons_self ..)
  rcases Prod.Lex.le_iff.mp hkey with h | ⟨h, _⟩
  · exact le_of_lt h
  · exact le_of_eq h


end Execution
end DecoupledConsensusModel

end
