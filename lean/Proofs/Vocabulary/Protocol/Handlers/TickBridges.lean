module
public import Proofs.Vocabulary.Internal.Definitions.TickReads
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.Agreement
public import Proofs.Vocabulary.Protocol.Handlers.Bridges
public import Mathlib.Algebra.Group.End
public import Proofs.Vocabulary.ModelProperties.confirmationReadFrom
public import Proofs.Vocabulary.ModelProperties.NamedActions_proposal_with_slot
public import Proofs.Vocabulary.ModelProperties.NamedNode_initial
public import Proofs.Vocabulary.ModelProperties.NamedStore_initial
public import Proofs.Vocabulary.ModelProperties.Store_sg_pool
import Proofs.Vocabulary.Protocol.Handlers.Execution
import Mathlib.Logic.Equiv.PartialEquiv
import Mathlib.Order.Interval.Finset.Box
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation


namespace DecoupledConsensusModel
namespace Proofs
namespace Optimistic

open Protocol (ChainState HeightConfig)
open Protocol (HealConfig)
open Internal
open Execution
open Internal.NamedRecoveryRead
open Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The slot of each tick time -/

theorem slotOfTime_add (Δ : Time) (hΔ : 0 < Δ) (s : Slot) (r : Time)
    (hr0 : 0 ≤ r) (hr : r < 4 * Δ) : slotOfTime Δ (4 * Δ * (s : Time) + r) = s := by
  have hne : (4 : Time) * Δ ≠ 0 := by
    have h : ∀ d : Int, 0 < d → (4 : Int) * d ≠ 0 := by intro d hd; omega
    exact h Δ hΔ
  unfold slotOfTime
  have hrw : 4 * Δ * (s : Time) + r = r + (s : Time) * (4 * Δ) := by ring
  rw [hrw, Int.add_mul_fdiv_right _ _ hne, Int.fdiv_eq_zero_of_lt hr0 hr, zero_add]
  simp

/-- The proposal time of slot `s` lies in slot `s`. -/
theorem slotOf_proposal_time (E : Env V) (s : Slot) :
    E.slotOf (Protocol.proposal_time E s) = s := by
  have h : ∀ d : Int, 0 < d → (0 : Int) ≤ 0 ∧ (0 : Int) < 4 * d := by intro d hd; omega
  obtain ⟨h0, h1⟩ := h E.Δ E.Δ_pos
  have hrw : Protocol.proposal_time E s = 4 * E.Δ * (s : Time) + 0 := by
    unfold Protocol.proposal_time Env.t slotStart; ring
  rw [Env.slotOf, hrw]
  exact slotOfTime_add E.Δ E.Δ_pos s 0 h0 h1

/-- The vote time of slot `s` lies in slot `s`. -/
theorem slotOf_vote_time (E : Env V) (s : Slot) :
    E.slotOf (Protocol.vote_time E s) = s := by
  have h : ∀ d : Int, 0 < d → (0 : Int) ≤ d ∧ d < 4 * d := by intro d hd; omega
  obtain ⟨h0, h1⟩ := h E.Δ E.Δ_pos
  exact slotOfTime_add E.Δ E.Δ_pos s E.Δ h0 h1

/-- The support cutoff of slot `s` lies in slot `s`. -/
theorem slotOf_support_cutoff (E : Env V) (s : Slot) :
    E.slotOf (Protocol.support_cutoff E s) = s := by
  have h : ∀ d : Int, 0 < d → (0 : Int) ≤ 2 * d ∧ 2 * d < 4 * d := by intro d hd; omega
  obtain ⟨h0, h1⟩ := h E.Δ E.Δ_pos
  exact slotOfTime_add E.Δ E.Δ_pos s (2 * E.Δ) h0 h1

/-- The confirmation time of slot `s` lies in slot `s + 1`. -/
theorem slotOf_confirmation_time (E : Env V) (s : Slot) :
    E.slotOf (Protocol.confirmation_time E s) = s + 1 := by
  have h : ∀ d : Int, 0 < d → (0 : Int) ≤ 2 * d ∧ 2 * d < 4 * d := by intro d hd; omega
  obtain ⟨h0, h1⟩ := h E.Δ E.Δ_pos
  have hrw : Protocol.confirmation_time E s
      = 4 * E.Δ * ((s + 1 : Slot) : Time) + 2 * E.Δ := by
    unfold Protocol.confirmation_time Env.t slotStart
    push_cast
    ring
  rw [Env.slotOf, hrw]
  exact slotOfTime_add E.Δ E.Δ_pos (s + 1) (2 * E.Δ) h0 h1

/-- The support cutoff of a slot differs from its proposal time. -/
theorem support_cutoff_ne_proposal_time (E : Env V) (s : Slot) :
    Protocol.support_cutoff E s ≠ Protocol.proposal_time E s := by
  have h : ∀ a d : Int, 0 < d → a + 2 * d ≠ a := by intro a d hd; omega
  exact h (E.t s) E.Δ E.Δ_pos

theorem support_cutoff_ne_vote_time (E : Env V) (s : Slot) :
    Protocol.support_cutoff E s ≠ Protocol.vote_time E s := by
  have h : ∀ a d : Int, 0 < d → a + 2 * d ≠ a + d := by intro a d hd; omega
  exact h (E.t s) E.Δ E.Δ_pos

theorem vote_time_ne_proposal_time (E : Env V) (s : Slot) :
    Protocol.vote_time E s ≠ Protocol.proposal_time E s := by
  have h : ∀ a d : Int, 0 < d → a + d ≠ a := by intro a d hd; omega
  exact h (E.t s) E.Δ E.Δ_pos

theorem vote_time_ne_support_cutoff (E : Env V) (s : Slot) :
    Protocol.vote_time E s ≠ Protocol.support_cutoff E s :=
  fun h => support_cutoff_ne_vote_time E s h.symm

/-! ## `Σ.live_confirmed` has one writer -/


omit [Fintype V] in
/-- `on_sg_vote` leaves `live_confirmed` unchanged. -/
theorem on_sg_vote_live_confirmed (hc : HealConfig) (st : Protocol.Store V)
    (a : CombinedAttestation V) :
    (Protocol.on_sg_vote hc st a).live_confirmed = st.live_confirmed := by
  simp only [Protocol.on_sg_vote]
  split_ifs <;> rfl

/-! ### The named store's writers -/

/-- The named row admission `admit_row` leaves `live_confirmed` unchanged. -/
theorem admit_row_live_confirmed (hc : HealConfig) (st : Protocol.NamedStore V)
    (row : NamedAttestation V) :
    (Protocol.NamedAdmission.admit_row hc st row).live_confirmed =
      st.live_confirmed := by
  simp only [Protocol.NamedAdmission.admit_row]
  split <;> exact on_sg_vote_live_confirmed _ _ _


/-- The named round action `attest_with` leaves `live_confirmed` unchanged. -/
theorem attest_with_live_confirmed (contract : Protocol.GradeContract V) (E : Env V)
    (hc : HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) :
    (Protocol.NamedDuties.attest_with contract E hc nd st record).1.live_confirmed =
      st.live_confirmed :=
  admit_row_live_confirmed hc st _

/-! ## The reads the duties perform -/

/-- At the support cutoff of a slot `s > 0`, the tick's `live_confirmed` is the output of the
    confirmation duty `update_confirmation_with`. -/
theorem on_tick_emit_confirmation (S : Setup V) (v : V) (n : NodeState V)
    (s : Slot) (hs : 0 < s) :
    (on_tick_emit S v n (Protocol.support_cutoff S.E s)).1.st.live_confirmed =
      (Protocol.NamedDuties.update_confirmation_with
        (NamedProfile.gradeContract
          (NamedActionReads.confirmationReadFrom S n
            (Protocol.support_cutoff S.E s)).cache)
        S.E S.hc
        (NamedActionReads.confirmationReadFrom S n
          (Protocol.support_cutoff S.E s)).st (s - 1)).live_confirmed := by
  have hslot : S.E.slotOf (Protocol.support_cutoff S.E s) = s := slotOf_support_cutoff S.E s
  simp only [NamedNode.tick, NamedProfile.tick, Protocol.NamedTick.tick,
    Protocol.TickScheduler.runWith, Protocol.NamedTick.namedOps, hslot,
    support_cutoff_ne_proposal_time S.E s, support_cutoff_ne_vote_time S.E s, hs,
    and_true, and_false, false_and, if_true, if_false,
    NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
    Protocol.NamedStore.setClock]
  split
  · exact attest_with_live_confirmed _ S.E S.hc _ _ _
  · rfl


/-! ## The prefix a tick reads -/


/-- A stretch of the event list that never touches `v` does not move `v`'s
state. -/
theorem stateBefore_eq_of_ne (S : Setup V) (ρ : Run V) (v : V) {m : Nat} :
    ∀ n : Nat, m ≤ n →
      (∀ (j : Nat) (e : Event V), m ≤ j → j < n →
        ρ.events[j]? = some e → e.node ≠ v) →
      (ρ.stateBefore S n v) = (ρ.stateBefore S m v) := by
  intro n
  induction n with
  | zero => intro hm _; rw [Nat.le_zero.mp hm]
  | succ n ih =>
      intro hm h
      rcases Nat.lt_or_ge m (n + 1) with hlt | hge
      · have hmn : m ≤ n := Nat.lt_succ_iff.mp hlt
        rw [← ih hmn (fun j e h1 h2 h3 => h j e h1 (Nat.lt_succ_of_lt h2) h3)]
        unfold Run.stateBefore NamedRun.stateBefore
        rw [List.take_add_one, List.foldl_append]
        cases hn : ρ.events[n]? with
        | none => simp
        | some e =>
            have hne : e.node ≠ v := h n e hmn (Nat.lt_succ_self n) hn
            simp only [Option.toList, List.foldl_cons, List.foldl_nil]
            cases e with
            | tick u t' =>
                simp only [NamedWorld.step]
                exact Function.update_of_ne (Ne.symm hne) _ _
            | deliver u o t' =>
                simp only [NamedWorld.step]
                exact Function.update_of_ne (Ne.symm hne) _ _
      · rw [Nat.le_antisymm hm hge]

/-- A filter of the event list that is downward closed along the key order is a prefix of the list. -/
theorem filter_eq_take (S : Setup V) {ρ : Run V} (sch : ScheduleWellFormed S ρ)
    (p : Event V → Bool)
    (hdc : ∀ e f : Event V, NamedEvent.key e ≤ NamedEvent.key f → p f = true → p e = true) :
    ρ.events.filter p = ρ.events.take (ρ.events.filter p).length := by
  refine List.prefix_iff_eq_take.mp ?_
  rw [Proofs.Bridges.filter_eq_takeWhile_of_pairwise hdc _ sch.sorted]
  exact List.takeWhile_prefix _

/-- Nothing at or beyond that prefix satisfies the filter. -/
theorem filter_false_of_index_ge (S : Setup V) {ρ : Run V} (sch : ScheduleWellFormed S ρ)
    (p : Event V → Bool)
    (hdc : ∀ e f : Event V, NamedEvent.key e ≤ NamedEvent.key f → p f = true → p e = true)
    {j : Nat} {e : Event V} (hj : (ρ.events.filter p).length ≤ j)
    (hget : ρ.events[j]? = some e) : p e = false := by
  set n := (ρ.events.filter p).length with hn
  have hfilt : ρ.events.filter p = ρ.events.take n := filter_eq_take S sch p hdc
  have hdropnil : (ρ.events.drop n).filter p = [] := by
    have h1 : ρ.events.filter p
        = (ρ.events.take n).filter p ++ (ρ.events.drop n).filter p := by
      conv_lhs => rw [← List.take_append_drop n ρ.events]
      rw [List.filter_append]
    have h2 : (ρ.events.take n).filter p = ρ.events.take n := by
      conv_lhs => rw [← hfilt]
      rw [List.filter_filter]
      simp only [Bool.and_self]
      exact hfilt
    rw [h2, ← hfilt] at h1
    exact List.self_eq_append_right.mp h1
  have hmem : e ∈ ρ.events.drop n := by
    refine List.mem_of_getElem? (i := j - n) ?_
    rw [List.getElem?_drop]
    have hjn : n + (j - n) = j := by omega
    rw [hjn]
    exact hget
  by_contra hcon
  have hin : e ∈ (ρ.events.drop n).filter p :=
    List.mem_filter.mpr ⟨hmem, by simpa using hcon⟩
  rw [hdropnil] at hin
  simp at hin

omit [DecidableEq V] [Fintype V] in
/-- The `< t` filter is downward closed along the key order. -/
theorem downward_lt (t : Time) :
    ∀ e f : Event V, NamedEvent.key e ≤ NamedEvent.key f → decide (f.time < t) = true →
      decide (e.time < t) = true := by
  intro e f hk hf
  simp only [decide_eq_true_eq] at hf ⊢
  exact lt_of_le_of_lt (Proofs.Bridges.time_le_of_key_le hk) hf

omit [DecidableEq V] [Fintype V] in
/-- The `≤ t` filter is downward closed along the key order. -/
theorem downward_le (t : Time) :
    ∀ e f : Event V, NamedEvent.key e ≤ NamedEvent.key f → decide (f.time ≤ t) = true →
      decide (e.time ≤ t) = true := by
  intro e f hk hf
  simp only [decide_eq_true_eq] at hf ⊢
  exact le_trans (Proofs.Bridges.time_le_of_key_le hk) hf

/-- `stateBeforeTime` at `t` is the prefix state whose length is that of the `< t` filter. -/
theorem stateBeforeTime_eq_take (S : Setup V) {ρ : Run V}
    (sch : ScheduleWellFormed S ρ) (t : Time) :
    ρ.stateBeforeTime S t =
      ρ.stateBefore S (ρ.events.filter (fun e => decide (e.time < t))).length := by
  unfold Run.stateBeforeTime Run.stateBefore NamedRun.stateBeforeTime NamedRun.stateBefore
  rw [← filter_eq_take S sch _ (downward_lt t)]

/-- `readAt` at `t` is the prefix state whose length is that of the `≤ t` filter. -/
theorem stateAt_eq_take (S : Setup V) {ρ : Run V}
    (sch : ScheduleWellFormed S ρ) (t : Time) :
    NamedRun.readAt S ρ t =
      ρ.stateBefore S (ρ.events.filter (fun e => decide (e.time ≤ t))).length := by
  unfold Run.stateBefore NamedRun.readAt NamedRun.stateBefore
  rw [← filter_eq_take S sch _ (downward_le t)]

/-- Nothing at or beyond the `< t` prefix happens before `t`. -/
theorem le_time_of_index_ge (S : Setup V) {ρ : Run V} (sch : ScheduleWellFormed S ρ)
    {t : Time} {j : Nat} {e : Event V}
    (hj : (ρ.events.filter (fun e => decide (e.time < t))).length ≤ j)
    (hget : ρ.events[j]? = some e) : t ≤ e.time := by
  have h := filter_false_of_index_ge S sch _ (downward_lt t) hj hget
  simpa using h

/-- The state a tick of `v` at time `t` reads is `v`'s node state made of every event strictly
    before `t`. -/
theorem stateBefore_tick_eq_stateBeforeTime (S : Setup V) {ρ : Run V}
    (sch : ScheduleWellFormed S ρ) {i : Nat} {v : V} {t : Time}
    (hi : ρ.events[i]? = some (Event.tick v t)) :
    ρ.stateBefore S i v = ρ.stateBeforeTime S t v := by
  have hni : (ρ.events.filter (fun e => decide (e.time < t))).length ≤ i := by
    by_contra hcon
    have hlt : i < (ρ.events.filter (fun e => decide (e.time < t))).length :=
      Nat.lt_of_not_ge hcon
    have hmem : Event.tick v t ∈ ρ.events.filter (fun e => decide (e.time < t)) := by
      rw [filter_eq_take S sch _ (downward_lt t)]
      exact List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hlt]; exact hi)
    have hp := (List.mem_filter.mp hmem).2
    simp only [decide_eq_true_eq, NamedEvent.time] at hp
    exact lt_irrefl _ hp
  rw [stateBeforeTime_eq_take S sch t]
  refine stateBefore_eq_of_ne S ρ v i hni ?_
  intro j e hj hji hget
  have hlow : t ≤ e.time := le_time_of_index_ge S sch hj hget
  obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hget
  obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
  have hkey : NamedEvent.key e ≤ NamedEvent.key (Event.tick v t) := by
    have hp := (List.pairwise_iff_getElem.mp sch.sorted) j i hjl hil hji
    rw [hje, hie] at hp
    exact hp
  have hteq : e.time = t := le_antisymm (Proofs.Bridges.time_le_of_key_le hkey) hlow
  intro hnode
  have heq : e = Event.tick v t := by
    cases e with
    | tick u t' =>
        simp only [NamedEvent.node] at hnode
        simp only [NamedEvent.time] at hteq
        rw [hnode, hteq]
    | deliver u o t' =>
        exfalso
        simp only [NamedEvent.time] at hteq
        subst hteq
        simp [NamedEvent.key, NamedEvent.time, NamedEvent.phase, Prod.Lex.toLex_le_toLex] at hkey
  have hev : ρ.events[j] = ρ.events[i] := by rw [hje, hie, heq]
  have hij : j = i := (List.Nodup.getElem_inj_iff (NamedScheduleWellFormed.nodup sch)).mp hev
  omega

/-! ## The emission bridge -/

/-- Slot proposal times are nonnegative. -/
theorem proposal_time_nonneg (E : Env V) (s : Slot) : 0 ≤ Protocol.proposal_time E s := by
  have h4 : (0 : Time) ≤ 4 * E.Δ := by
    have h : ∀ d : Int, 0 < d → (0 : Int) ≤ 4 * d := by intro d hd; omega
    exact h E.Δ E.Δ_pos
  unfold Protocol.proposal_time Env.t slotStart
  exact Int.mul_nonneg h4 (Int.natCast_nonneg s)

theorem vote_time_nonneg (E : Env V) (s : Slot) : 0 ≤ Protocol.vote_time E s := by
  have h := proposal_time_nonneg E s
  have key : ∀ a d : Int, 0 ≤ a → 0 < d → 0 ≤ a + d := by intro a d h1 h2; omega
  exact key _ E.Δ h E.Δ_pos

theorem publicTime_vote_time (S : Setup V) (s : Slot) :
    PublicTime S (Protocol.vote_time S.E s) :=
  (publicTime_iff S _).mpr ⟨s, Or.inr (Or.inl rfl)⟩

/-- Everything an honest node's tick at a public time `t` emits is a `Run.emits` of that node at
    `t`. -/
theorem emits_of_on_tick_emit (S : Setup V) {ρ : Run V} (sch : ScheduleWellFormed S ρ)
    {v : V} (hv : v ∈ ρ.honest) {t : Time} (hpub : PublicTime S t) (ht0 : 0 ≤ t)
    (hthor : t ≤ ρ.horizon) {o : Object V}
    (ho : o ∈ (on_tick_emit S v (ρ.stateBeforeTime S t v) t).2) :
    ρ.emits S v o t := by
  have hmem : Event.tick v t ∈ ρ.events :=
    NamedScheduleWellFormed.tick_total sch v hv t hpub ht0 hthor
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hmem
  refine ⟨i, hi, ?_⟩
  show o ∈ (on_tick_emit S v (ρ.stateBefore S i v) t).2
  rw [stateBefore_tick_eq_stateBeforeTime S sch hi]
  exact ho

/-- The vote duty reads a store whose slot is the vote time's own slot. -/
theorem voteStore_slot (S : Setup V) (st : Protocol.Store V) (s : Slot) :
    (voteStore S st s).s = s := by
  simp only [voteStore, tickStore, slotOf_vote_time]

/-- The prepared vote read has slot `s`. -/
theorem voteDutyRead_slot (S : Setup V) (ρ : Run V) (v : V) (s : Slot) :
    (voteDutyRead S ρ v s).st.core.s = s := by
  show (NamedActionReads.confirmationReadFrom S
      (NamedRun.stateBeforeTime S ρ (Protocol.vote_time S.E s) v)
      (Protocol.vote_time S.E s)).st.core.s = s
  rw [ModelProperties.confirmationReadFrom_st_core_s]
  exact slotOf_vote_time S.E s

/-- At the vote time of a slot `s > 0`, the Goldfish vote the named duty computes on the tick's
    prepared read is among the tick's emissions. -/
theorem on_tick_emit_vote_mem (S : Setup V) (v : V) (n : NodeState V) (s : Slot)
    (hs : 0 < s) {u : GoldfishVote V}
    (hu : (Protocol.NamedDuties.goldfish_vote_with
        (NamedProfile.gradeContract
          (NamedActionReads.confirmationReadFrom S n (Protocol.vote_time S.E s)).cache)
        S.E S.hc (S.node v)
        (NamedActionReads.confirmationReadFrom S n
          (Protocol.vote_time S.E s)).st).2 = some u) :
    Object.gfVote u ∈ (on_tick_emit S v n (Protocol.vote_time S.E s)).2 := by
  have hslot : S.E.slotOf (Protocol.vote_time S.E s) = s := slotOf_vote_time S.E s
  simp only [NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
    Protocol.NamedStore.setClock, hslot] at hu
  simp only [NamedNode.tick, NamedProfile.tick, Protocol.NamedTick.tick,
    Protocol.TickScheduler.runWith, Protocol.NamedTick.namedOps, hslot,
    NamedActionReads.preparedCache, Protocol.NamedStore.setClock,
    vote_time_ne_proposal_time S.E s, vote_time_ne_support_cutoff S.E s, hs,
    and_false, false_and, if_false, and_true, if_true]
  rw [hu]
  split <;> simp


/-! ## The confirmation time -/

/-- Sortedness at two indices. -/
theorem key_le_of_index_lt (S : Setup V) {ρ : Run V} (sch : ScheduleWellFormed S ρ)
    {j i : Nat} {e f : Event V} (hji : j < i)
    (hj : ρ.events[j]? = some e) (hi : ρ.events[i]? = some f) :
    NamedEvent.key e ≤ NamedEvent.key f := by
  obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hj
  obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
  have hp := (List.pairwise_iff_getElem.mp sch.sorted) j i hjl hil hji
  rw [hje, hie] at hp
  exact hp

/-- The store the slot-`s` confirmation reads: the tick store at the slot-`s` confirmation time. -/
def confStore (S : Setup V) (ρ : Run V) (v : V) (s : Slot) : Protocol.Store V :=
  tickStore S (ρ.storeBeforeTime S v (Protocol.confirmation_time S.E s)).core
    (Protocol.confirmation_time S.E s)

/-- `confStore` is the core store of the prepared confirmation read. -/
theorem confStore_eq_confirmationInputRead (S : Setup V) (ρ : Run V) (v : V) (s : Slot) :
    confStore S ρ v s = (confirmationInputRead S ρ v s).st.core := by
  show confStore S ρ v s = (NamedActionReads.confirmationReadFrom S
      (NamedRun.stateBeforeTime S ρ (Protocol.confirmation_time S.E s) v)
      (Protocol.confirmation_time S.E s)).st.core
  rw [ModelProperties.confirmationReadFrom_st_core]
  rfl


/-! ## The proposal time -/

theorem proposal_time_ne_vote_time (E : Env V) (s : Slot) :
    Protocol.proposal_time E s ≠ Protocol.vote_time E s :=
  fun h => vote_time_ne_proposal_time E s h.symm

theorem proposal_time_ne_support_cutoff (E : Env V) (s : Slot) :
    Protocol.proposal_time E s ≠ Protocol.support_cutoff E s :=
  fun h => support_cutoff_ne_proposal_time E s h.symm

theorem publicTime_proposal_time (S : Setup V) (s : Slot) :
    PublicTime S (Protocol.proposal_time S.E s) :=
  (publicTime_iff S _).mpr ⟨s, Or.inl rfl⟩

/-- At the proposal time of a slot `s > 0` whose proposer is `v`, the block the named proposal duty
    computes on the tick's prepared read is among the tick's emissions. -/
theorem on_tick_emit_proposal_mem (S : Setup V) (v : V) (n : NodeState V) (s : Slot)
    (hs : 0 < s) (hpr : S.E.proposer s = (S.node v).val_index) {B : NamedBlock V}
    (hB : (Protocol.NamedDuties.propose_block_with
        (NamedProfile.gradeContract
          (NamedActionReads.confirmationReadFrom S n
            (Protocol.proposal_time S.E s)).cache)
        S.E S.hc S.cfg (S.node v)
        (NamedActionReads.confirmationReadFrom S n
          (Protocol.proposal_time S.E s)).st).2 = some B) :
    Object.block B ∈ (on_tick_emit S v n (Protocol.proposal_time S.E s)).2 := by
  have hslot : S.E.slotOf (Protocol.proposal_time S.E s) = s := slotOf_proposal_time S.E s
  simp only [NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
    Protocol.NamedStore.setClock, hslot] at hB
  simp only [NamedNode.tick, NamedProfile.tick, Protocol.NamedTick.tick,
    Protocol.TickScheduler.runWith, Protocol.NamedTick.namedOps, hslot,
    NamedActionReads.preparedCache, Protocol.NamedStore.setClock,
    proposal_time_ne_vote_time S.E s, proposal_time_ne_support_cutoff S.E s, hpr, hs,
    and_false, if_false, and_true, if_true]
  rw [hB]
  split <;> simp

/-- The block computed for slot `s` has slot `s`. -/
theorem proposedBlockAt_slot (S : Setup V) (ρ : Run V) (s : Slot) {B : NamedBlock V}
    (hB : Statements.Instantiation.proposedBlockAt S ρ s = some B) : B.slot = s := by
  have hst : (Statements.Instantiation.proposerReadAt S ρ s).st.core.s = s := by
    show (NamedActionReads.confirmationReadFrom S
        (NamedRun.stateBeforeTime S ρ (Protocol.proposal_time S.E s) (S.E.proposer s))
        (Protocol.proposal_time S.E s)).st.core.s = s
    rw [ModelProperties.confirmationReadFrom_st_core_s]
    exact slotOf_proposal_time S.E s
  exact (ModelProperties.proposal_with_slot _ _ _ _ _ _ B hB).trans hst

/-- An honest slot-`s` proposer emits, at the slot-`s` proposal time, the block `B` its duty
    computed, and `B` has slot `s`. -/
theorem proposalTick (S : Setup V) {ρ : Run V} (sch : ScheduleWellFormed S ρ)
    (s : Slot) (hs : 0 < s) (hprop : S.E.proposer s ∈ ρ.honest)
    (hhor : Protocol.proposal_time S.E s ≤ ρ.horizon)
    {B : NamedBlock V} (hB : Statements.Instantiation.proposedBlockAt S ρ s = some B) :
    B.slot = s ∧
      NamedRun.emits S ρ (S.E.proposer s) (.block B)
        (Protocol.proposal_time S.E s) := by
  refine ⟨proposedBlockAt_slot S ρ s hB, ?_⟩
  refine emits_of_on_tick_emit S sch hprop (publicTime_proposal_time S s)
    (proposal_time_nonneg S.E s) hhor ?_
  refine on_tick_emit_proposal_mem S (S.E.proposer s)
    (ρ.stateBeforeTime S (Protocol.proposal_time S.E s) (S.E.proposer s)) s hs
    (S.node_val_index (S.E.proposer s)).symm ?_
  have hB' : Protocol.NamedActions.proposal_with
      (NamedProfile.gradeContract
        (NamedActionReads.confirmationReadFrom S
          (ρ.stateBeforeTime S (Protocol.proposal_time S.E s) (S.E.proposer s))
          (Protocol.proposal_time S.E s)).cache)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc (S.node (S.E.proposer s))
      (NamedActionReads.confirmationReadFrom S
        (ρ.stateBeforeTime S (Protocol.proposal_time S.E s) (S.E.proposer s))
        (Protocol.proposal_time S.E s)).st = some B := hB
  simp only [Protocol.NamedDuties.propose_block_with, hB']

/-! ## Origin of the SG pool's attestations -/

omit [Fintype V] in
/-- `update_finality` leaves `sg_votes` unchanged. -/
theorem update_finality_sg_votes (st : Protocol.Store V) (σ : ChainState V) :
    (Protocol.update_finality st σ).sg_votes = st.sg_votes := by
  simp only [Protocol.update_finality]
  split_ifs <;> rfl

omit [Fintype V] in
/-- `on_goldfish_vote` leaves `sg_votes` unchanged. -/
theorem on_goldfish_vote_sg_votes (st : Protocol.Store V) (u : GoldfishVote V) :
    (Protocol.on_goldfish_vote st u).sg_votes = st.sg_votes := by
  simp only [Protocol.on_goldfish_vote]
  split_ifs <;> rfl

/-- `on_goldfish_vote_checked` leaves `sg_votes` unchanged. -/
theorem on_goldfish_vote_checked_sg_votes (E : Env V)
    (st : Protocol.Store V) (u : GoldfishVote V) :
    (Protocol.on_goldfish_vote_checked E st u).sg_votes = st.sg_votes := by
  simp only [Protocol.on_goldfish_vote_checked]
  split_ifs
  · exact on_goldfish_vote_sg_votes st u
  · rfl


/-- Folding `on_goldfish_vote_checked` leaves `sg_votes` unchanged. -/
theorem foldl_on_goldfish_vote_checked_sg_votes (E : Env V)
    (l : List (GoldfishVote V)) (st : Protocol.Store V) :
    (l.foldl (Protocol.on_goldfish_vote_checked E) st).sg_votes = st.sg_votes := by
  induction l generalizing st with
  | nil => rfl
  | cons u l ih =>
      rw [List.foldl_cons, ih, on_goldfish_vote_checked_sg_votes]


omit [Fintype V] in
/-- An attestation in the SG pool after `on_sg_vote` was already there or is the attestation `a`
    handled. -/
theorem on_sg_vote_sg_pool_mem (hc : HealConfig) (st : Protocol.Store V)
    (a : CombinedAttestation V) (r : Round) {b : CombinedAttestation V}
    (hb : b ∈ (Protocol.on_sg_vote hc st a).sg_pool r) :
    b ∈ st.sg_pool r ∨ b = a := by
  simp only [Protocol.on_sg_vote] at hb
  split_ifs at hb
  · exact Or.inl hb
  · simp only [Protocol.Store.sg_pool] at hb ⊢
    split_ifs at hb with hr
    · rw [List.toFinset_append] at hb
      rcases Finset.mem_union.mp hb with h | h
      · exact Or.inl h
      · exact Or.inr (by simpa using h)
    · exact Or.inl hb

/-- `b` is a row the object `o` can add to the SG pool: an attestation itself, or the erasure of a
    row a block includes. -/
def CarriesRow (o : Object V) (b : CombinedAttestation V) : Prop :=
  match o with
  | .block B => ∃ row ∈ B.attestations, b = row.erase
  | .gfVote _ => False
  | .attest row => b = row.erase

/-- `on_block_using` leaves `sg_votes` unchanged, whatever chain state it builds. -/
theorem on_block_using_sg_votes (E : Env V) (st : Protocol.Store V) (B : Block V)
    (buildState : ChainState V → ChainState V) :
    (Protocol.on_block_using E st B buildState).sg_votes = st.sg_votes := by
  simp only [Protocol.on_block_using]
  split_ifs <;>
    simp only [update_finality_sg_votes, foldl_on_goldfish_vote_checked_sg_votes]

/-- `on_block_checked_using` leaves `sg_votes` unchanged when its handler does. -/
theorem on_block_checked_using_sg_votes
    (handle : Protocol.Store V → Protocol.Store V) (hc : HealConfig)
    (st : Protocol.Store V) (B : Block V)
    (hh : ∀ st' : Protocol.Store V, (handle st').sg_votes = st'.sg_votes) :
    (Protocol.on_block_checked_using handle hc st B).sg_votes = st.sg_votes := by
  simp only [Protocol.on_block_checked_using]
  split_ifs
  · exact hh st
  · rfl

/-- The named block core leaves `sg_votes` unchanged. -/
theorem process_block_core_sg_votes (E : Env V) (hc : HealConfig)
    (cfg : HeightConfig) (st : Protocol.NamedStore V) (B : NamedBlock V) :
    (Protocol.NamedStore.process_block_core E hc cfg st B).core.sg_votes =
      st.core.sg_votes := by
  simp only [Protocol.NamedStore.process_block_core]
  split
  · rfl
  · simp only [Protocol.NamedStore.commitBlock]
    split <;>
      exact on_block_checked_using_sg_votes _ hc st.core B.erase
        (fun st' => on_block_using_sg_votes E st' B.erase _)

omit [Fintype V] in
/-- An attestation in the SG pool after `admit_row` was already there or is the erasure of the row
    handled. -/
theorem admit_row_sg_pool_mem (hc : HealConfig) (st : Protocol.NamedStore V)
    (row : NamedAttestation V) (r : Round) {b : CombinedAttestation V}
    (hb : b ∈ (Protocol.NamedAdmission.admit_row hc st row).core.sg_pool r) :
    b ∈ st.core.sg_pool r ∨ b = row.erase := by
  simp only [Protocol.NamedAdmission.admit_row] at hb
  split at hb <;> exact on_sg_vote_sg_pool_mem hc st.core row.erase r hb

omit [Fintype V] in

/-- An attestation in the SG pool after `admit_rows` was already there or is the erasure of one of
    the rows handled. -/
theorem admit_rows_sg_pool_mem (hc : HealConfig) :
    ∀ (rows : List (NamedAttestation V)) (st : Protocol.NamedStore V) (r : Round)
      (b : CombinedAttestation V),
      b ∈ (Protocol.NamedAdmission.admit_rows hc st rows).core.sg_pool r →
        b ∈ st.core.sg_pool r ∨ ∃ row ∈ rows, b = row.erase := by
  intro rows
  induction rows with
  | nil => intro st r b hb; exact Or.inl hb
  | cons a l ih =>
      intro st r b hb
      have h : Protocol.NamedAdmission.admit_rows hc st (a :: l) =
          Protocol.NamedAdmission.admit_rows hc
            (Protocol.NamedAdmission.admit_row hc st a) l := rfl
      rw [h] at hb
      rcases ih _ r b hb with h1 | ⟨row, hrow, hbe⟩
      · rcases admit_row_sg_pool_mem hc st a r h1 with h2 | h2
        · exact Or.inl h2
        · exact Or.inr ⟨a, List.mem_cons_self .., h2⟩
      · exact Or.inr ⟨row, List.mem_cons_of_mem _ hrow, hbe⟩

/-- An attestation in the SG pool after the named block handler was already there or is the erasure
    of a row the block includes. -/
theorem on_block_with_sg_pool_mem (adm : Protocol.CarriedAdmission) (E : Env V)
    (hc : HealConfig) (cfg : HeightConfig) (st : Protocol.NamedStore V)
    (B : NamedBlock V) (r : Round) {b : CombinedAttestation V}
    (hb : b ∈ (Protocol.NamedAdmission.on_block_with adm E hc cfg st B).core.sg_pool r) :
    b ∈ st.core.sg_pool r ∨ ∃ row ∈ B.attestations, b = row.erase := by
  have hcore : ∀ k : Round,
      (Protocol.NamedStore.process_block_core E hc cfg st B).core.sg_pool k =
        st.core.sg_pool k := by
    intro k
    simp only [Protocol.Store.sg_pool, process_block_core_sg_votes]
  cases adm with
  | alsoCarried =>
      rw [show Protocol.NamedAdmission.on_block_with .alsoCarried E hc cfg st B =
          (if B ∉ st.bodies ∧
              B ∈ (Protocol.NamedStore.process_block_core E hc cfg st B).bodies then
            Protocol.NamedAdmission.admit_rows hc
              (Protocol.NamedStore.process_block_core E hc cfg st B) B.attestations
          else Protocol.NamedStore.process_block_core E hc cfg st B) from rfl] at hb
      split_ifs at hb
      · rcases admit_rows_sg_pool_mem hc B.attestations _ r b hb with h | h
        · exact Or.inl ((hcore r) ▸ h)
        · exact Or.inr h
      · exact Or.inl ((hcore r) ▸ hb)

/-- The named Goldfish vote duty leaves `sg_votes` unchanged. -/
theorem goldfish_vote_with_sg_votes (contract : Protocol.GradeContract V) (E : Env V)
    (hc : HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V) :
    (Protocol.NamedDuties.goldfish_vote_with contract E hc nd st).1.core.sg_votes =
      st.core.sg_votes := by
  simp only [Protocol.NamedDuties.goldfish_vote_with, Protocol.goldfish_vote_with]
  split
  · exact on_goldfish_vote_checked_sg_votes E _ _
  · rfl

/-- The named confirmation duty leaves `sg_votes` unchanged. -/
theorem update_confirmation_with_sg_votes (contract : Protocol.GradeContract V)
    (E : Env V) (hc : HealConfig) (st : Protocol.NamedStore V) (s : Slot) :
    (Protocol.NamedDuties.update_confirmation_with contract E hc st s).core.sg_votes =
      st.core.sg_votes := rfl

/-- An attestation in the SG pool after the named proposal duty was already there or is the erasure
    of a row the emitted block includes. -/
theorem propose_block_with_sg_pool_mem (contract : Protocol.GradeContract V) (E : Env V)
    (hc : HealConfig) (cfg : HeightConfig) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) (r : Round) {b : CombinedAttestation V}
    (hb : b ∈
      (Protocol.NamedDuties.propose_block_with contract E hc cfg nd st).1.core.sg_pool r) :
    b ∈ st.core.sg_pool r ∨
      ∃ B : NamedBlock V,
        (Protocol.NamedDuties.propose_block_with contract E hc cfg nd st).2 = some B ∧
          ∃ row ∈ B.attestations, b = row.erase := by
  simp only [Protocol.NamedDuties.propose_block_with] at hb ⊢
  split at hb
  · exact Or.inl hb
  · rename_i B hBeq
    rcases on_block_with_sg_pool_mem .alsoCarried E hc cfg st B r hb with h | h
    · exact Or.inl h
    · refine Or.inr ⟨B, ?_, h⟩
      simp only [hBeq]

/-- An attestation in the SG pool after the named round action was already there or is the erasure
    of the row it emits. -/
theorem attest_with_sg_pool_mem (contract : Protocol.GradeContract V) (E : Env V)
    (hc : HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) (r : Round) {b : CombinedAttestation V}
    (hb : b ∈ (Protocol.NamedDuties.attest_with contract E hc nd st record).1.core.sg_pool r) :
    b ∈ st.core.sg_pool r ∨
      b = (Protocol.NamedDuties.attest_with contract E hc nd st record).2.2.erase :=
  admit_row_sg_pool_mem hc st _ r hb

/-- An attestation in the SG pool after processing an object was already there or is a row that
    object carries. -/
theorem process_sg_pool_mem (S : Setup V) (n : NodeState V) (o : Object V)
    (r : Round) {b : CombinedAttestation V}
    (hb : b ∈ (n.process S o).st.core.sg_pool r) :
    b ∈ n.st.core.sg_pool r ∨ CarriesRow o b := by
  cases o with
  | block B =>
      rcases on_block_with_sg_pool_mem .alsoCarried S.E S.hc S.cfg n.st B r hb with h | h
      · exact Or.inl h
      · exact Or.inr h
  | gfVote u =>
      refine Or.inl ?_
      simp only [Protocol.Store.sg_pool, NodeState.process, NamedNode.process,
        NamedReceipt.process, on_goldfish_vote_checked_sg_votes] at hb ⊢
      exact hb
  | attest a =>
      rcases admit_row_sg_pool_mem S.hc n.st a r hb with h | h
      · exact Or.inl h
      · exact Or.inr h

/-! ## Origin of the SG pool's attestations at a tick and along the run -/

/-- An attestation in the SG pool after the tick scheduler was already there or is carried by an
    object the tick emits. -/
private theorem runWith_sg_pool_mem
    (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V)
    (ops : Protocol.TickScheduler.TickOps (Protocol.NamedStore V) Protocol.NamedRecord
      (NamedBlock V) (GoldfishVote V) (NamedAttestation V))
    (hclock : ∀ (st0 : Protocol.NamedStore V) (t' : Time) (s' : Slot) (r : Round),
      (ops.clock st0 t' s').core.sg_pool r = st0.core.sg_pool r)
    (hprop : ∀ (st0 : Protocol.NamedStore V) (r : Round) {b : CombinedAttestation V},
      b ∈ (ops.proposal st0).1.core.sg_pool r →
        b ∈ st0.core.sg_pool r ∨
          ∃ B : NamedBlock V, (ops.proposal st0).2 = some B ∧
            ∃ row ∈ B.attestations, b = row.erase)
    (hvote : ∀ (st0 : Protocol.NamedStore V) (r : Round),
      (ops.vote st0).1.core.sg_pool r = st0.core.sg_pool r)
    (hconf : ∀ (st0 : Protocol.NamedStore V) (s' : Slot) (r : Round),
      (ops.confirmation st0 s').core.sg_pool r = st0.core.sg_pool r)
    (hatt : ∀ (st0 : Protocol.NamedStore V) (record0 : Protocol.NamedRecord) (r : Round)
      {b : CombinedAttestation V},
      b ∈ (ops.attestation st0 record0).1.core.sg_pool r →
        b ∈ st0.core.sg_pool r ∨ b = (ops.attestation st0 record0).2.2.erase)
    (st : Protocol.NamedStore V) (record : Protocol.NamedRecord) (t : Time) (r : Round)
    {b : CombinedAttestation V}
    (hb : b ∈ (Protocol.TickScheduler.runWith E hc nd ops
        NamedObject.block NamedObject.gfVote NamedObject.attest
        (fun st record emitted => (st, record, emitted)) st record t).1.core.sg_pool r) :
    b ∈ st.core.sg_pool r ∨
      ∃ o ∈ (Protocol.TickScheduler.runWith E hc nd ops
        NamedObject.block NamedObject.gfVote NamedObject.attest
        (fun st record emitted => (st, record, emitted)) st record t).2.2,
        CarriesRow o b := by
  simp only [Protocol.TickScheduler.runWith,
    apply_ite (fun p : Protocol.NamedStore V × Protocol.NamedRecord × List (NamedObject V) =>
      p.1.core.sg_pool r),
    apply_ite (fun p : Protocol.NamedStore V × Protocol.NamedRecord × List (NamedObject V) =>
      p.2.2)] at hb ⊢
  set st1 := (if 0 < E.slotOf t ∧ t = Protocol.proposal_time E (E.slotOf t) ∧
      E.proposer (E.slotOf t) = nd.val_index then
        (ops.proposal (ops.clock st t (E.slotOf t))).1
      else ops.clock st t (E.slotOf t)) with hst1
  set st2 := (if 0 < E.slotOf t ∧ t = Protocol.vote_time E (E.slotOf t) then
      (ops.vote st1).1 else st1) with hst2
  set emitted2 : List (NamedObject V) :=
    (if 0 < E.slotOf t ∧ t = Protocol.vote_time E (E.slotOf t) then
      List.map NamedObject.gfVote (ops.vote st1).2.toList else []) with hemitted2
  set st3 := (if 0 < E.slotOf t ∧ t = Protocol.support_cutoff E (E.slotOf t) then
      ops.confirmation st2 (E.slotOf t - 1) else st2) with hst3
  have hpeel23 : st3.core.sg_pool r = st1.core.sg_pool r := by
    by_cases hP3 : 0 < E.slotOf t ∧ t = Protocol.support_cutoff E (E.slotOf t)
    · rw [hst3, if_pos hP3, hconf st2 (E.slotOf t - 1) r]
      by_cases hP2 : 0 < E.slotOf t ∧ t = Protocol.vote_time E (E.slotOf t)
      · rw [hst2, if_pos hP2, hvote st1 r]
      · rw [hst2, if_neg hP2]
    · rw [hst3, if_neg hP3]
      by_cases hP2 : 0 < E.slotOf t ∧ t = Protocol.vote_time E (E.slotOf t)
      · rw [hst2, if_pos hP2, hvote st1 r]
      · rw [hst2, if_neg hP2]
  have hstep1 : b ∈ st1.core.sg_pool r →
      b ∈ st.core.sg_pool r ∨
        ∃ B : NamedBlock V, (ops.proposal (ops.clock st t (E.slotOf t))).2 = some B ∧
          (0 < E.slotOf t ∧ t = Protocol.proposal_time E (E.slotOf t) ∧
            E.proposer (E.slotOf t) = nd.val_index) ∧
          ∃ row ∈ B.attestations, b = row.erase := by
    intro hb1
    by_cases hP1 : 0 < E.slotOf t ∧ t = Protocol.proposal_time E (E.slotOf t) ∧
        E.proposer (E.slotOf t) = nd.val_index
    · rw [hst1, if_pos hP1] at hb1
      rcases hprop (ops.clock st t (E.slotOf t)) r hb1 with h0 | ⟨B, hBeq, hrow⟩
      · left; rw [hclock st t (E.slotOf t) r] at h0; exact h0
      · right; exact ⟨B, hBeq, hP1, hrow⟩
    · rw [hst1, if_neg hP1, hclock st t (E.slotOf t) r] at hb1
      left; exact hb1
  by_cases hP4 : t = hc.a E.Δ (hc.round_of (ops.slot st3)) ∧
      nd.awake (hc.round_of (ops.slot st3)) = true
  · rw [if_pos hP4] at hb ⊢
    rcases hatt st3 record r hb with h3 | heq
    · rw [hpeel23] at h3
      rcases hstep1 h3 with h | ⟨B, hBeq, hP1, hrow⟩
      · exact Or.inl h
      · refine Or.inr ⟨NamedObject.block B, ?_, hrow⟩
        apply List.mem_append_left
        apply List.mem_append_left
        rw [if_pos hP1, hBeq]
        exact List.mem_cons_self ..
    · exact Or.inr ⟨NamedObject.attest (ops.attestation st3 record).2.2,
        List.mem_append_right _ (List.mem_cons_self ..), heq⟩
  · rw [if_neg hP4] at hb ⊢
    rw [hpeel23] at hb
    rcases hstep1 hb with h | ⟨B, hBeq, hP1, hrow⟩
    · exact Or.inl h
    · refine Or.inr ⟨NamedObject.block B, ?_, hrow⟩
      apply List.mem_append_left
      rw [if_pos hP1, hBeq]
      exact List.mem_cons_self ..

/-- An attestation in the SG pool after a tick was already there or is carried by an object the tick
    emitted. -/
theorem on_tick_emit_sg_mem (S : Setup V) (v : V) (n : NodeState V) (t : Time)
    (r : Round) {b : CombinedAttestation V}
    (hb : b ∈ (on_tick_emit S v n t).1.st.core.sg_pool r) :
    b ∈ n.st.core.sg_pool r ∨ ∃ o ∈ (on_tick_emit S v n t).2, CarriesRow o b := by
  simp only [NamedNode.tick, NamedProfile.tick, Protocol.NamedTick.tick] at hb ⊢
  set gc := NamedProfile.gradeContract
    (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache) with hgc
  exact runWith_sg_pool_mem S.E S.hc (S.node v)
    (Protocol.NamedTick.namedOps gc S.E S.hc S.cfg (S.node v))
    (fun st0 t' s' _r => rfl)
    (by intro st0 r b hb
        exact propose_block_with_sg_pool_mem gc S.E S.hc S.cfg (S.node v) st0 r hb)
    (fun st0 r => by
      simp only [Protocol.NamedTick.namedOps, Protocol.Store.sg_pool, goldfish_vote_with_sg_votes])
    (fun st0 s' r => by
      simp only [Protocol.NamedTick.namedOps, Protocol.Store.sg_pool,
        update_confirmation_with_sg_votes])
    (by intro st0 record0 r b hb
        exact attest_with_sg_pool_mem gc S.E S.hc (S.node v) st0 record0 r hb)
    n.st n.record t r hb

/-- An attestation in a node's SG pool in a prefix state was carried, in the sense of `CarriesRow`,
    by an object the node processed strictly earlier. -/
theorem processes_attest_of_mem_sg_pool (S : Setup V) (ρ : Run V) (v : V) :
    ∀ (i : Nat) (r : Round) (a : CombinedAttestation V),
      a ∈ (ρ.stateBefore S i v).st.core.sg_pool r →
        ∃ (j : Nat) (e : Event V) (o : Object V), j < i ∧ ρ.events[j]? = some e ∧
          NamedRun.processes S ρ v o e.time ∧ CarriesRow o a := by
  intro i
  induction i with
  | zero =>
      intro r a ha
      exfalso
      have hinit : (ρ.stateBefore S 0 v) = NamedNode.initial := rfl
      rw [hinit, ModelProperties.initial_st] at ha
      exact ModelProperties.initial_core_not_mem_sg_pool r a ha
  | succ n ih =>
      intro r a ha
      cases hn : ρ.events[n]? with
      | none =>
          have heq : ρ.stateBefore S (n + 1) v = ρ.stateBefore S n v := by
            unfold Run.stateBefore NamedRun.stateBefore
            rw [List.take_add_one, hn, List.foldl_append]
            simp
          rw [heq] at ha
          obtain ⟨j, e, o, hji, hje, hpr, hcarry⟩ := ih r a ha
          exact ⟨j, e, o, Nat.lt_succ_of_lt hji, hje, hpr, hcarry⟩
      | some e =>
          cases e with
          | tick u t' =>
              by_cases hu : v = u
              · subst hu
                have heq : ρ.stateBefore S (n + 1) v =
                    (on_tick_emit S v (ρ.stateBefore S n v) t').1 := by
                  unfold Run.stateBefore NamedRun.stateBefore
                  rw [List.take_add_one, hn, List.foldl_append]
                  simp only [Option.toList, List.foldl_cons, List.foldl_nil, NamedWorld.step,
                    Function.update_self]
                rw [heq] at ha
                rcases on_tick_emit_sg_mem S v (ρ.stateBefore S n v) t' r ha with
                  h | ⟨o, ho, hcarry⟩
                · obtain ⟨j, e', o', hji, hje, hpr, hcarry⟩ := ih r a h
                  exact ⟨j, e', o', Nat.lt_succ_of_lt hji, hje, hpr, hcarry⟩
                · refine ⟨n, Event.tick v t', o, Nat.lt_succ_self n, hn, ?_, hcarry⟩
                  exact Or.inl ⟨n, hn, ho⟩
              · have heq : ρ.stateBefore S (n + 1) v = ρ.stateBefore S n v := by
                  unfold Run.stateBefore NamedRun.stateBefore
                  rw [List.take_add_one, hn, List.foldl_append]
                  simp only [Option.toList, List.foldl_cons, List.foldl_nil, NamedWorld.step]
                  exact Function.update_of_ne hu _ _
                rw [heq] at ha
                obtain ⟨j, e', o, hji, hje, hpr, hcarry⟩ := ih r a ha
                exact ⟨j, e', o, Nat.lt_succ_of_lt hji, hje, hpr, hcarry⟩
          | deliver u o' t' =>
              by_cases hu : v = u
              · subst hu
                have heq : ρ.stateBefore S (n + 1) v =
                    NodeState.process S (ρ.stateBefore S n v) o' := by
                  unfold Run.stateBefore NamedRun.stateBefore
                  rw [List.take_add_one, hn, List.foldl_append]
                  simp only [Option.toList, List.foldl_cons, List.foldl_nil, NamedWorld.step,
                    Function.update_self]
                rw [heq] at ha
                rcases process_sg_pool_mem S (ρ.stateBefore S n v) o' r ha with h | hcarry
                · obtain ⟨j, e', o'', hji, hje, hpr, hcarry⟩ := ih r a h
                  exact ⟨j, e', o'', Nat.lt_succ_of_lt hji, hje, hpr, hcarry⟩
                · refine ⟨n, Event.deliver v o' t', o', Nat.lt_succ_self n, hn, ?_, hcarry⟩
                  exact Or.inr ⟨n, hn⟩
              · have heq : ρ.stateBefore S (n + 1) v = ρ.stateBefore S n v := by
                  unfold Run.stateBefore NamedRun.stateBefore
                  rw [List.take_add_one, hn, List.foldl_append]
                  simp only [Option.toList, List.foldl_cons, List.foldl_nil, NamedWorld.step]
                  exact Function.update_of_ne hu _ _
                rw [heq] at ha
                obtain ⟨j, e', o, hji, hje, hpr, hcarry⟩ := ih r a ha
                exact ⟨j, e', o, Nat.lt_succ_of_lt hji, hje, hpr, hcarry⟩

end Optimistic
end Proofs
end DecoupledConsensusModel

end
