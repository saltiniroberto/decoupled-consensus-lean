module
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.HonestProposalExtensionDefs
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89Handover
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma95
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma91
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma81
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Provenance
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Clock
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.FGStateReadersOnChain
public import GoldilocksCorrectness.Proofs.Executions.Lemma89
public import GoldilocksCorrectness.Proofs.Routines.Schedule

@[expose] public section

/-!
# HonestProposalExtension, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/HonestProposalExtension.lean`, over a
model `M` whose facts `F` hold, for a trace `x` whose node states are the model's: the new
conclusions of Lemma 90 and Lemma 98, each
derived from the conclusions those lemmas already had.

- `ac_confirmed_mem_tree`: a node state's confirmed tip is in its tree when its finalized block
  is;
- `proposalAt_of_proposalAtV`: a proposal on the view of `x` is a proposal of `x`;
- `slot_lt_of_ancestorEq_held_clock`: a block that is a block held after a step at which the
  holder's clock value is before the start of slot `s`, or an ancestor of one, has a slot less than
  `s`;
- `exists_step_near_clock`, `st_eq_of_no_own_step`, `awake_of_no_restart`,
  `time_le_of_active_no_tick`, `exists_state_kept_from_time_le`,
  `slotStart_add_le_supportCutoff_succ`, `exists_state_kept_le_of_clockValue_lt`: a node state read at
  a clock value before slot `s` was held, unchanged, from a step at a real time at most the support
  cutoff of slot `s + 1`;
- `exists_step_leaving_state_or_first`: a node state read at a clock before slot `s` is the one a
  step at a time from `tE` to `t` leaves, unless it was set before `tE` and changes at the first step
  from `tE` on;
- `honestThroughTime_tick_or_corrupted_after`: a validator honest at `c` is honest through its tick
  to `c`, unless that tick is late and the validator is corrupted right after it;
- `confirmed_strict_ancestor_of_agree`: a confirmed tip read at a clock before slot `s` is a strict
  ancestor of a slot-`s` block an honest validator confirms at a step the agreement reads;
- `two_le_of_after_phase`: every slot starting after the end of the healing phase is at least `2`;
- `confirmedExtendedBetween_of_agree_included`, `confirmedExtended_of_agree_included`: Lemma 90's
  fourth conclusion from its agreement and its inclusion, read up to a time and with no upper end;
- `finalizedExtendedBetween_of_compatible_included`: Lemma 98's second conclusion from Lemma 86's
  compatibility of the finalized blocks and Lemma 98's first conclusion.

The argument, both times: the proposal `B` of slot `s` has the slot `s`; every block a validator
holds while its clock is before the start of slot `s`, and every ancestor of one, has a slot less
than `s`; so such an output is never `B` or a descendant of `B`, and the compatibility each lemma
gives, read at a step at a time at most `t` at which the validator already held that output, leaves
only the other order. The derivations read the conclusions on the view
`x.map (nodeView M)` directly, so they call none of the view bridges.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (Δ Δ_F slotStart voteTime supportCutoff
  proposalWindowStart)
open GoldilocksCorrectness.Proofs.Routines (slot_mono_int ancestorEq_refl ancestorEq_trans
  compatible_iff)

namespace GoldilocksCorrectness.Record.Proofs.Executions

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject Vocab.goldilocks blockOf
  healFrontSlots)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Record.Statements.View

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded in the goal and in every
hypothesis: `omega` does not see a fact stated at either. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

/-! ## Kit facts -/

omit [RootOrder] in
/-- **Kit fact, the confirmed tip is held.** A node state's confirmed tip (`M.ac_confirmed`) is in
its tree when its finalized block is.

Why: the confirmed tip is the record `n.latestConfirmed` when the record is in the tree of the
frame `M.fg_to_ac n`, whose blocks are blocks of `n.tree`; and it is the frame's finalized block,
`n.finalized`, otherwise (the reader fact `ac_confirmed_eq`).

The variables:
- `M`: the model; `F`: its facts;
- `n`: the node state.

Read aloud: a node state's confirmed tip is a block it holds, when its finalized block is. -/
theorem ac_confirmed_mem_tree (n : M.N)
    -- the finalized block is in the tree
    (hFT : n.finalized ∈ n.tree) :
    M.ac_confirmed n ∈ n.tree := by
  rw [F.rd.ac_confirmed_eq]
  split
  · rename_i hin
    exact (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hin).1
  · rw [(GoldilocksCorrectness.Record.Proofs.Routines.fg_to_ac_F M F)]
    exact hFT

omit F in
/-- **Kit fact, a proposal on the view.** A proposal of slot `s` on the view `x.map (nodeView M)`
of `x` is a proposal of `x`: the proposer's tick at the start of slot `s` puts the block on the
wire under the proposer's signature.

Why: the view keeps the labels and the sent log; the only object Goldilocks's vocabulary reads as
the block `b` is the block `b` itself (`blockOf`).

The variables:
- `M`: the model;
- `S`: the setup; `x`: the trace; `s`: the slot; `b`: the block.

Read aloud: a proposal on the view is a proposal of the trace. -/
theorem proposalAt_of_proposalAtV {S : Setup V} {x : Trace V (NamedObject V) M.N} {s : ℕ}
    {b : Block V}
    (hb : ProposalAtV M Vocab.goldilocks S (x.map (nodeView M)) s b) :
    ProposalAt M S x s b := by
  obtain ⟨i, hl, ⟨v', o⟩, hm, hv, hbo⟩ := hb
  refine ⟨i, hl, ?_⟩
  cases o with
  | block b' =>
    simp only [Vocab.goldilocks, blockOf, Option.some.injEq] at hbo
    simp only at hv
    subst hv hbo
    exact hm
  | gfVote _ => simp [Vocab.goldilocks, blockOf] at hbo
  | attest _ => simp [Vocab.goldilocks, blockOf] at hbo

/-- **Kit fact, what is held while the clock is before a slot has an earlier slot.** A block `B`
that is a block `D` of `u`'s tree after a step `i`, with `u` outside the adversary set after `i`
steps and `u`'s clock value after `i` steps less than the start of slot `s`, or an ancestor of `D`,
has a slot less than `s`.

Why: `D` has a slot at most the slot of `u`'s clock value (`slot_le_clockValue_of_mem_tree`), less
than `s`; a strict ancestor of `D` in the tree has a smaller slot
(`slot_lt_of_ancestorEq_of_treeClosed_node`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `x`: the trace; `R`: the run's facts; `E`: the environment's facts; `i`: the step; `u`: the
  validator; `s`: the slot; `B`, `D`: the blocks.

Read aloud: a block held while the holder's clock is before slot `s`, and each of its ancestors,
is from a slot before `s`. -/
theorem slot_lt_of_ancestorEq_held_clock (U : UniformSchedule M.toSlotLayout) {S : Setup V}
    {A : Activity V} (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject Vocab.goldilocks)
    {i : ℕ} {u : V} {s : ℕ} {B D : Block V}
    -- `u` is outside the adversary set after `i` steps
    (hu : u ∉ A.corrupted i)
    -- `u` holds `D` after step `i`
    (hD : D ∈ (x.st i u).tree)
    -- `B` is `D` or an ancestor of it
    (hBD : B.AncestorEq D)
    -- `u`'s clock value after `i` steps is before the start of slot `s`
    (hc : x.clockValue i u < M.slotStart S.C s) :
    B.slot < s := by
  have hInv := (lem11_node_invariant M F S A x R E i u hu).1
  have hDs : D.slot < s := by
    have h1 := (slot_le_clockValue_of_mem_tree M F) R E hu hD
    have h3 := (GoldilocksCorrectness.Record.Proofs.Routines.slot_lt_of_lt_slotStart M.toSlotLayout
      F.sched) S hc
    have h4 : S.C.slot ((x.clockValue i u : ℕ) : Int) = M.toSlotLayout.slot S.C (x.clockValue i u) := by
      rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast,
        (GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U)]
    rw [h4] at h1
    omega_nat
  by_cases hBD' : B = D
  · rw [hBD']
    exact hDs
  · exact lt_trans ((slot_lt_of_ancestorEq_of_treeClosed_node M F) (F.nd.nodeInv_treeClosed hInv)
      hD hBD hBD') hDs

omit F in
/-- **Kit fact, a step near every clock value.** For every clock value `t ≥ 1`, some step has a
real time in `[t − ΔClockAhead, t + ΔClockBehind]`.

Why: otherwise every validator `v` is active at every step whose real time is in that window (there
is none), so `v` ticks to `t` at a step whose real time is in it (`tick_of_active`).

The variables:
- `x`: the trace; `E`: the environment's facts; `v`: a validator; `t`: the clock value.

Read aloud: the run has a step within the clock bounds of every clock value. -/
theorem exists_step_near_clock {A : Activity V} {x : Trace V (NamedObject V) M.N}
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject Vocab.goldilocks)
    (v : V) {t : ℕ} (ht : 1 ≤ t) :
    ∃ i : ℕ, (t : ℝ) - ΔClockAhead ≤ x.time i ∧ x.time i ≤ t + ΔClockBehind := by
  by_contra h
  push_neg at h
  obtain ⟨i, -, h1, h2⟩ := E.tick_of_active t ht v (fun i h1 h2 => absurd h2 (not_le.2 (h i h1)))
  exact absurd h2 (not_le.2 (h i h1))

omit F in
/-- **Kit fact, a node state is kept between the node's own steps.** When no step from `a` to
before `b` is a tick, a restart or a delivery of `v`, `v`'s node state after every step from `a` to
`b` is its state after `b` steps (`untouched`).

The variables:
- `M`: the model; `S`: the setup; `x`: the trace; `R`: the run's facts; `v`: the validator; `a`,
  `b`: the steps.

Read aloud: only `v`'s own steps change `v`'s node state. -/
theorem st_eq_of_no_own_step {S : Setup V} {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x)
    {v : V} {a b : ℕ}
    -- no step from `a` to before `b` is `v`'s tick, restart or delivery
    (h : ∀ l : ℕ, a ≤ l → l < b → (∀ t : ℕ, x.lbl l ≠ Event.tick v t) ∧
      (∀ (t : ℕ) (keep : Bool), x.lbl l ≠ Event.restart v t keep) ∧
      ∀ sm : SignedMsg V (NamedObject V), x.lbl l ≠ Event.deliver v sm) :
    ∀ l : ℕ, a ≤ l → l ≤ b → x.st l v = x.st b v := by
  intro l hal hlb
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hlb
  clear hlb
  induction d generalizing l with
  | zero => rfl
  | succ d ih =>
    obtain ⟨h1, h2, h3⟩ := h l hal (by omega)
    rw [← R.untouched l v h1 h2 h3]
    have := ih (l + 1) (by omega) (fun l' h1' h2' => h l' h1' (by omega))
    rw [show l + 1 + d = l + (d + 1) by omega] at this
    exact this

omit F in
/-- **Kit fact, awake back to the last restart.** A validator awake after `j` steps, with no
restart of it at a step from `a` to before `j`, is awake after every step from `a` to `j`
(`restart_of_awake`).

The variables:
- `x`: the trace; `E`: the environment's facts; `v`: the validator; `a`, `j`: the steps.

Read aloud: a validator awake now was awake since its last restart. -/
theorem awake_of_no_restart {A : Activity V} {x : Trace V (NamedObject V) M.N}
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject Vocab.goldilocks)
    {v : V} {a j : ℕ} (hj : v ∈ A.awake j)
    -- no step from `a` to before `j` is a restart of `v`
    (hnr : ∀ l : ℕ, a ≤ l → l < j → ∀ (t : ℕ) (keep : Bool), x.lbl l ≠ Event.restart v t keep) :
    ∀ l : ℕ, a ≤ l → l ≤ j → v ∈ A.awake l := by
  intro l hal hlj
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hlj
  clear hlj
  induction d generalizing l with
  | zero => simpa using hj
  | succ d ih =>
    have h1 : v ∈ A.awake (l + 1) :=
      ih (l + 1) (by omega) (by rw [show l + 1 + d = l + (d + 1) by omega]; exact hj)
        (fun l' h1 h2 => hnr l' h1 (by omega))
    by_contra h0
    obtain ⟨t, keep, hr⟩ := E.restart_of_awake l v h0 h1
    exact hnr l hal (by omega) t keep hr

omit F in
/-- **Kit fact, an active validator's real time is near its clock.** When `v` is active after every
step at a real time after `τ₀ ≥ 0` up to step `j`, and no step at a real time after `τ₀` before `j`
is a tick of `v`, the real time of `j` is at most `τ₀ + ΔClockAhead + ΔClockBehind + 2`.

Why: otherwise, for the clock value `t' := ⌈τ₀ + ΔClockAhead⌉₊ + 1`, every step whose real time is
in `[t' − ΔClockAhead, t' + ΔClockBehind]` is after `τ₀` and before `j`, so `v` is active there and
ticks to `t'` at one of them (`tick_of_active`).

The variables:
- `M`: the model; `S`: the setup; `x`: the trace; `R`: the run's facts; `E`: the environment's
  facts; `v`: the validator; `j`: the step; `τ₀`: the real time.

Read aloud: a validator active since `τ₀` that has not ticked since is still within a few time
units of `τ₀`. -/
theorem time_le_of_active_no_tick {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N}
    (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject Vocab.goldilocks)
    {v : V} {j : ℕ} {τ₀ : ℝ} (hτ₀ : 0 ≤ τ₀)
    -- `v` is active after every step at a real time after `τ₀` up to `j`
    (hact : ∀ l : ℕ, τ₀ < x.time l → l ≤ j → v ∈ A.active l)
    -- no step at a real time after `τ₀` before `j` is a tick of `v`
    (hnt : ∀ l : ℕ, τ₀ < x.time l → l < j → ∀ t : ℕ, x.lbl l ≠ Event.tick v t) :
    x.time j ≤ τ₀ + ΔClockAhead + ΔClockBehind + 2 := by
  by_contra hlt
  push_neg at hlt
  have hA := E.ahead_nonneg
  set t' : ℕ := ⌈τ₀ + ΔClockAhead⌉₊ + 1 with ht'
  have hc1 : τ₀ + ΔClockAhead ≤ (⌈τ₀ + ΔClockAhead⌉₊ : ℝ) := Nat.le_ceil _
  have hc2 : (⌈τ₀ + ΔClockAhead⌉₊ : ℝ) < τ₀ + ΔClockAhead + 1 := Nat.ceil_lt_add_one (by linarith)
  have ht'R : (t' : ℝ) = (⌈τ₀ + ΔClockAhead⌉₊ : ℝ) + 1 := by rw [ht']; push_cast; ring
  -- a step in the window is after `τ₀` and before `j`
  have hin : ∀ l : ℕ, (t' : ℝ) - ΔClockAhead ≤ x.time l → x.time l ≤ t' + ΔClockBehind →
      τ₀ < x.time l ∧ l < j := by
    intro l h1 h2
    refine ⟨by linarith, ?_⟩
    by_contra hjl
    have := (time_mono M) x R (show j ≤ l by omega)
    linarith
  obtain ⟨l, hl, h1, h2⟩ := E.tick_of_active t' (by omega) v
    (fun l h1 h2 => hact l (hin l h1 h2).1 (hin l h1 h2).2.le)
  exact hnt l (hin l h1 h2).1 (hin l h1 h2).2 t' hl

omit F in
/-- **Kit fact, every node state was taken near its clock value.** For every step `i` and
validator `v`, some step `k ≤ i` has a real time at most `v`'s clock value after `i` steps plus
`ΔClockAhead + 2 ΔClockBehind + 2`, and `v`'s node state after every step from `k` to `i` is its
state after `i` steps.

Why: `k` is the step after `v`'s last tick, restart or delivery before `i` (`0` when there is none):
nothing between changes `v`'s state (`st_eq_of_no_own_step`), and that step keeps the time
(`time_keep`). A tick or a restart is at a real time at most its clock value plus `ΔClockBehind`
(`tick_active`, `restart_time`), and its clock value is `v`'s clock value after `i` steps
(`clockValue_cases`). A delivery is to an active validator (`deliver_active`), awake since its last
restart (`awake_of_no_restart`) and with no tick since its last tick or restart, so its real time is
at most that one's plus `ΔClockAhead + ΔClockBehind + 2` (`time_le_of_active_no_tick`).

The variables:
- `M`: the model; `S`: the setup; `x`: the trace; `R`: the run's facts; `E`: the environment's
  facts; `i`: the step; `v`: the validator.

Read aloud: whatever `v` holds now, it already held at a step not long after its clock's last
setting, and has held unchanged since. -/
theorem exists_state_kept_from_time_le {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N}
    (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject Vocab.goldilocks)
    (i : ℕ) (v : V) :
    ∃ k : ℕ, k ≤ i ∧ x.time k ≤ (x.clockValue i v : ℝ) + ΔClockAhead + 2 * ΔClockBehind + 2 ∧
      ∀ l : ℕ, k ≤ l → l ≤ i → x.st l v = x.st i v := by
  classical
  have hA := E.ahead_nonneg
  have hB := E.behind_nonneg
  have hc0 : (0 : ℝ) ≤ (x.clockValue i v : ℝ) := Nat.cast_nonneg _
  -- `v`'s own steps
  let Q : ℕ → Prop := fun l => (∃ t : ℕ, x.lbl l = Event.tick v t) ∨
    (∃ (t : ℕ) (keep : Bool), x.lbl l = Event.restart v t keep) ∨
    ∃ sm : SignedMsg V (NamedObject V), x.lbl l = Event.deliver v sm
  have hnotQ : ∀ l : ℕ, ¬ Q l → (∀ t : ℕ, x.lbl l ≠ Event.tick v t) ∧
      (∀ (t : ℕ) (keep : Bool), x.lbl l ≠ Event.restart v t keep) ∧
      ∀ sm : SignedMsg V (NamedObject V), x.lbl l ≠ Event.deliver v sm := by
    intro l hq
    exact ⟨fun t h => hq (Or.inl ⟨t, h⟩), fun t keep h => hq (Or.inr (Or.inl ⟨t, keep, h⟩)),
      fun sm h => hq (Or.inr (Or.inr ⟨sm, h⟩))⟩
  by_cases hQ : ∃ l, l < i ∧ Q l
  swap
  · -- no own step before `i`: the state is the initial one, at the time `0`
    push_neg at hQ
    refine ⟨0, Nat.zero_le _, ?_, st_eq_of_no_own_step M R (fun l _ hl => hnotQ l (hQ l hl))⟩
    rw [R.time_zero]
    linarith
  -- the last own step `j` before `i`
  obtain ⟨l₀, hl₀, hQl₀⟩ := hQ
  set j := Nat.findGreatest Q (i - 1) with hjdef
  have hQj : Q j := Nat.findGreatest_spec (P := Q) (show l₀ ≤ i - 1 by omega) hQl₀
  have hji : j < i := by
    have := Nat.findGreatest_le (P := Q) (i - 1)
    omega
  have hafter : ∀ l : ℕ, j < l → l < i → ¬ Q l := fun l h1 h2 =>
    Nat.findGreatest_is_greatest (P := Q) h1 (by omega)
  refine ⟨j + 1, by omega, ?_, st_eq_of_no_own_step M R
    (fun l h1 h2 => hnotQ l (hafter l (by omega) h2))⟩
  have hother : x.lbl j ≠ Event.other := by
    rcases hQj with ⟨t, h⟩ | ⟨t, keep, h⟩ | ⟨sm, h⟩ <;> rw [h] <;> exact nofun
  rw [R.time_keep j hother]
  -- `v`'s clock value after `i` steps: set by its last tick or restart before `i`, or `0`
  rcases x.clockValue_cases i v with ⟨hc, hnone⟩ | ⟨j₀, hj₀i, hj₀, hnone⟩
  · -- no tick or restart before `i`: `j` is a delivery, `v` active since step `0`
    have hdel : ∃ sm : SignedMsg V (NamedObject V), x.lbl j = Event.deliver v sm := by
      rcases hQj with ⟨t, h⟩ | ⟨t, keep, h⟩ | h
      · exact absurd h ((hnone j hji).1 t)
      · exact absurd h ((hnone j hji).2 t keep)
      · exact h
    obtain ⟨sm, hsm⟩ := hdel
    have hactj := E.deliver_active j v sm hsm
    have haw := awake_of_no_restart M E (Finset.mem_sdiff.1 hactj).1 (a := 0)
      (fun l _ hl => (hnone l (by omega)).2)
    have := time_le_of_active_no_tick M R E (τ₀ := 0) le_rfl
      (fun l _ hl => Finset.mem_sdiff.2 ⟨haw l (Nat.zero_le _) hl,
        fun hc' => (Finset.mem_sdiff.1 hactj).2 (E.corrupted_mono l j hl hc')⟩)
      (fun l _ hl => (hnone l (by omega)).1)
    rw [hc]
    push_cast
    linarith
  · -- the last tick or restart `j₀ ≤ j`, at a real time at most the clock value plus `ΔClockBehind`
    have hj₀j : j₀ ≤ j := Nat.le_findGreatest (P := Q) (by omega) (by
      rcases hj₀ with h | ⟨keep, h⟩
      · exact Or.inl ⟨_, h⟩
      · exact Or.inr (Or.inl ⟨_, keep, h⟩))
    have hτ₀ : x.time j₀ ≤ (x.clockValue i v : ℝ) + ΔClockBehind := by
      rcases hj₀ with h | ⟨keep, h⟩
      · exact (E.tick_active j₀ v _ h).2.2
      · exact (E.restart_time j₀ v _ keep h).2
    rcases Nat.eq_or_lt_of_le hj₀j with hjj | hjj
    · rw [← hjj]
      linarith
    -- `j` after `j₀` is a delivery
    have hdel : ∃ sm : SignedMsg V (NamedObject V), x.lbl j = Event.deliver v sm := by
      rcases hQj with ⟨t, h⟩ | ⟨t, keep, h⟩ | h
      · exact absurd h ((hnone j hjj hji).1 t)
      · exact absurd h ((hnone j hjj hji).2 t keep)
      · exact h
    obtain ⟨sm, hsm⟩ := hdel
    have hactj := E.deliver_active j v sm hsm
    have haw := awake_of_no_restart M E (Finset.mem_sdiff.1 hactj).1 (a := j₀ + 1)
      (fun l h1 h2 => (hnone l (by omega) (by omega)).2)
    -- a step at a real time after the time of `j₀` is after `j₀`
    have hlt : ∀ l : ℕ, x.time j₀ < x.time l → j₀ + 1 ≤ l := by
      intro l hl
      by_contra h
      have := (time_mono M) x R (show l ≤ j₀ by omega)
      linarith
    have := time_le_of_active_no_tick M R E (τ₀ := x.time j₀) ((time_nonneg M) x R j₀)
      (fun l h1 hl => Finset.mem_sdiff.2 ⟨haw l (hlt l h1) hl,
        fun hc' => (Finset.mem_sdiff.1 hactj).2 (E.corrupted_mono l j hl hc')⟩)
      (fun l h1 hl => (hnone l (hlt l h1) (by omega)).1)
    linarith

omit [RootOrder] in
/-- **Kit fact, the support cutoff of the next slot is six delays after a slot's start.**

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `S`: the setup; `s`: the slot.

Read aloud: the support cutoff of slot `s + 1` is at least `6Δ` after the start of slot `s`. -/
theorem slotStart_add_le_supportCutoff_succ (U : UniformSchedule M.toSlotLayout) (S : Setup V)
    (s : ℕ) : M.slotStart S.C s + 6 * Δ S ≤ M.supportCutoff S.C (s + 1) := by
  have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S
    (s + 1)
  have h2 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s
  have h3 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S
    (s + 1)
  have h4 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U)
    S (s + 1)
  rw [Nat.mul_succ] at h1
  omega

/-- **Kit fact, a node state read at a clock value before slot `s` is read at a time at most `t`.**
When `ΔClockAhead + ΔClockBehind < Δ`, `v`'s clock value after `i` steps is less than the start of
slot `s`, and the support cutoff of slot `s + 1` is at most `t`, some step `k ≤ i` at a real time at
most `t` has `v`'s node state after every step from `k` to `i` equal to its state after `i` steps
(`exists_state_kept_from_time_le`: the real time of `k` is at most the clock value plus
`ΔClockAhead + 2 ΔClockBehind + 2`, at most the start of slot `s` plus `2Δ`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`: the setup, the activity, the trace; `R`: the run's facts; `E`: the environment's
  facts; `i`: the step; `v`: the validator; `s`: the slot; `t`: the time.

Read aloud: a state an honest clock reads before slot `s` was already held by the next slot's
support cutoff. -/
theorem exists_state_kept_le_of_clockValue_lt (U : UniformSchedule M.toSlotLayout) {S : Setup V}
    {A : Activity V} {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject Vocab.goldilocks)
    (hSkew : ΔClockAhead + ΔClockBehind < (Δ S : ℝ))
    {i : ℕ} {v : V} {s t : ℕ}
    (hc : x.clockValue i v < M.slotStart S.C s) (hst : M.supportCutoff S.C (s + 1) ≤ t) :
    ∃ k : ℕ, k ≤ i ∧ x.time k ≤ t ∧ ∀ l : ℕ, k ≤ l → l ≤ i → x.st l v = x.st i v := by
  obtain ⟨k, hki, hkT, hkst⟩ := (exists_state_kept_from_time_le M) R E i v
  refine ⟨k, hki, ?_, hkst⟩
  have hA := E.ahead_nonneg
  have hB := E.behind_nonneg
  have hgap := (slotStart_add_le_supportCutoff_succ M F U) S s
  have h1 : ((x.clockValue i v : ℕ) : ℝ) + 1 ≤ (M.slotStart S.C s : ℝ) := by exact_mod_cast hc
  have h2 : ((M.slotStart S.C s + 6 * Δ S : ℕ) : ℝ) ≤ (t : ℝ) := by exact_mod_cast hgap.trans hst
  have hΔ : (1 : ℝ) ≤ (Δ S : ℝ) := by exact_mod_cast GoldilocksCorrectness.Proofs.Routines.one_le_Δ S
  push_cast at h2
  linarith

/-- **Kit fact, the step that leaves a node state read at a clock before slot `s`.** For a
validator `v` honest through a step `i` at a time from `tE` on, with `v`'s clock value after `i`
steps less than the start of slot `s`, slot `s` starting at or after `tE`, and `t` at least the
earliest real time of a tick to the support cutoff of slot `s + 1`: either some step `l` at a time
from `tE` to `t`, through whose time `v` is honest, leaves `v`'s state after `i` steps
(`x.st (l + 1) v = x.st i v`); or every step before `i` is at a time less than `tE` and step `i`
changes `v`'s state.

Why: when the time of `i` is at most `t`, `l` is `i` (if step `i` keeps `v`'s state) or `i − 1` (if
its time is at least `tE`). Otherwise `v`'s state after `i` steps was held unchanged from a step `k`
at a time at most `t` (`exists_state_kept_from_time_le`, the clock value being before slot `s`):
`l` is `k − 1` when its time is at least `tE`, and otherwise a step at a time from `tE` to `t`
(`exists_step_near_clock`), which lies from `k − 1` to before `i`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`: the setup, the activity, the trace; `R`: the run's facts; `E`: the environment's
  facts; `tE`, `t`: the times; `s`: the slot; `v`, `i`: the validator and its step.

Read aloud: a state an honest validator holds while its clock is before slot `s` is left by a step
the agreement from `tE` up to `t` reads, unless it was set before `tE` and changes at the first
step from `tE` on. -/
theorem exists_step_leaving_state_or_first (U : UniformSchedule M.toSlotLayout) {S : Setup V}
    {A : Activity V} {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject Vocab.goldilocks)
    (hSkew : ΔClockAhead + ΔClockBehind < (Δ S : ℝ))
    {tE t s : ℕ} (hsE : tE ≤ M.slotStart S.C s)
    (ht : (M.supportCutoff S.C (s + 1) : ℝ) - ΔClockAhead ≤ t)
    {v : V} {i : ℕ} (hv : A.HonestThroughTime x (x.time i) v) (hi : (tE : ℝ) ≤ x.time i)
    (hc : x.clockValue i v < M.slotStart S.C s) :
    (∃ l : ℕ, (tE : ℝ) ≤ x.time l ∧ x.time l ≤ t ∧ A.HonestThroughTime x (x.time l) v ∧
        x.st (l + 1) v = x.st i v) ∨
      ((∀ l : ℕ, l < i → x.time l < tE) ∧ x.st (i + 1) v ≠ x.st i v) := by
  have hA := E.ahead_nonneg
  have hB := E.behind_nonneg
  have hΔ : (1 : ℝ) ≤ (Δ S : ℝ) := by
    exact_mod_cast GoldilocksCorrectness.Proofs.Routines.one_le_Δ S
  have hgap := (slotStart_add_le_supportCutoff_succ M F U) S s
  have h6 : ((M.slotStart S.C s + 6 * Δ S : ℕ) : ℝ) ≤ (M.supportCutoff S.C (s + 1) : ℝ) := by
    exact_mod_cast hgap
  push_cast at h6
  have hsE' : (tE : ℝ) ≤ (M.slotStart S.C s : ℝ) := by exact_mod_cast hsE
  have hhon : ∀ l : ℕ, l ≤ i → A.HonestThroughTime x (x.time l) v := fun l hl j hj =>
    hv j (hj.trans ((time_mono M) x R hl))
  by_cases hti : x.time i ≤ t
  · by_cases hst1 : x.st (i + 1) v = x.st i v
    · exact Or.inl ⟨i, hi, hti, hv, hst1⟩
    by_cases hpre : ∃ l : ℕ, l < i ∧ (tE : ℝ) ≤ x.time l
    · obtain ⟨l, hli, hlE⟩ := hpre
      obtain ⟨m, rfl⟩ : ∃ m : ℕ, i = m + 1 := ⟨i - 1, by omega⟩
      exact Or.inl ⟨m, hlE.trans ((time_mono M) x R (by omega)),
        ((time_mono M) x R (Nat.le_succ m)).trans hti, hhon m (Nat.le_succ m), rfl⟩
    · push_neg at hpre
      exact Or.inr ⟨hpre, hst1⟩
  push_neg at hti
  left
  obtain ⟨k, hki, hkT, hkst⟩ := (exists_state_kept_from_time_le M) R E i v
  have h1 : ((x.clockValue i v : ℕ) : ℝ) + 1 ≤ (M.slotStart S.C s : ℝ) := by exact_mod_cast hc
  have hkt : x.time k ≤ t := by linarith
  by_cases hk1 : ∃ l : ℕ, l + 1 = k ∧ (tE : ℝ) ≤ x.time l
  · obtain ⟨l, rfl, hlE⟩ := hk1
    exact ⟨l, hlE, ((time_mono M) x R (Nat.le_succ l)).trans hkt, hhon l (by omega),
      hkst (l + 1) le_rfl hki⟩
  push_neg at hk1
  -- a step at a real time from `tE` to `t`, from `k − 1` to before `i`
  set t' : ℕ := tE + ⌈ΔClockAhead⌉₊ + 1 with ht'
  obtain ⟨l, hl1, hl2⟩ := (exists_step_near_clock M) E v (t := t') (by omega)
  have hc1 : ΔClockAhead ≤ (⌈ΔClockAhead⌉₊ : ℝ) := Nat.le_ceil _
  have hc2 : (⌈ΔClockAhead⌉₊ : ℝ) < ΔClockAhead + 1 := Nat.ceil_lt_add_one hA
  have ht'R : (t' : ℝ) = (tE : ℝ) + ⌈ΔClockAhead⌉₊ + 1 := by rw [ht']; push_cast; ring
  have hlE : (tE : ℝ) + 1 ≤ x.time l := by linarith
  have hlt : x.time l ≤ t := by linarith
  have hli : l < i := by
    by_contra h
    have := (time_mono M) x R (show i ≤ l by omega)
    linarith
  have hkl : k ≤ l + 1 := by
    by_contra h
    obtain ⟨m, hm⟩ : ∃ m : ℕ, k = m + 1 := ⟨k - 1, by omega⟩
    have hm' := hk1 m hm.symm
    have := (time_mono M) x R (show l ≤ m by omega)
    linarith
  exact ⟨l, by linarith, hlt, hhon l hli.le, hkst (l + 1) hkl (by omega)⟩

omit F in
/-- **Kit fact, a validator's honesty through its own tick.** A validator `p` ticking to the clock
value `c` at step `k'`, outside the adversary set at `c`, is honest through the time of `k'`, or
that tick is at a real time after `c` and `p` is in the adversary set after a step `j > k' + 1` at a
real time at most that tick's.

Why: when the tick is at a time at most `c`, the honesty at `c` covers it. Otherwise a step `j` at
a time at most the tick's is at or before the tick (`p` is outside the adversary set at its tick,
`tick_active`, so at every step before it, `corrupted_mono`), the step right after the tick (a
tick keeps the adversary set, `corrupted_keep`), or a later step.

The variables:
- `M`: the model;
- `S`, `A`, `x`: the setup, the activity, the trace; `R`: the run's facts; `E`: the environment's
  facts; `p`: the validator; `k'`: its tick; `c`: the clock value.

Read aloud: a validator honest at `c` stays honest through its tick to `c`, unless it is corrupted
right after a late tick, at the tick's real time. -/
theorem honestThroughTime_tick_or_corrupted_after {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject Vocab.goldilocks)
    {p : V} {k' c : ℕ} (hk' : x.lbl k' = Event.tick p c) (hpc : p ∉ A.corruptedAtTime x c) :
    A.HonestThroughTime x (x.time k') p ∨
      ((c : ℝ) < x.time k' ∧ ∃ j : ℕ, k' + 1 < j ∧ x.time j ≤ x.time k' ∧ p ∈ A.corrupted j) := by
  by_cases hct : x.time k' ≤ c
  · exact Or.inl fun j hj => (not_mem_corrupted_of_le_time M) x R E hpc (hj.trans hct)
  push_neg at hct
  by_cases hex : ∃ j : ℕ, k' + 1 < j ∧ x.time j ≤ x.time k' ∧ p ∈ A.corrupted j
  · exact Or.inr ⟨hct, hex⟩
  push_neg at hex
  left
  have hpk : p ∉ A.corrupted k' :=
    Activity.not_mem_corrupted_of_mem_active (E.tick_active k' p c hk').1
  intro j hj hpj
  rcases Nat.lt_or_ge (k' + 1) j with h | h
  · exact hex j h hj hpj
  rcases Nat.lt_or_ge j (k' + 1) with h' | h'
  · exact hpk (E.corrupted_mono j k' (by omega) hpj)
  · have hj' : j = k' + 1 := by omega
    subst hj'
    rw [E.corrupted_keep k' (by rw [hk']; exact nofun)] at hpj
    exact hpk hpj

/-- **Kit fact, a confirmed tip read at a clock before slot `s` is a strict ancestor of a slot-`s`
block another honest validator confirms.** From the agreement from `tE` up to `t`, a validator `p`
honest through a step `j₁` at a time from `tE` to `t` whose confirmed tip in the state `j₁` leaves is
`b`, of slot `s`, and a validator `v` outside the adversary set after `i` steps, with `v`'s clock
value after `i` steps less than the start of slot `s`, whose state after `i` steps is the one a step
`l` at a time from `tE` to `t`, through whose time `v` is honest, leaves: `v`'s confirmed tip after
`i` steps is an ancestor of `b` other than `b`.

Why: `v`'s confirmed tip is held (`ac_confirmed_mem_tree`), so `b`, of slot `s`, is not it or an
ancestor of it (`slot_lt_of_ancestorEq_held_clock`). The agreement at `l` and `j₁` leaves only the other order.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`: the setup, the activity, the trace; `R`: the run's facts; `E`: the environment's
  facts; `tE`, `t`: the times of the agreement; `s`: the slot; `b`: the block; `p`, `j₁`: the
  validator confirming `b` and its step; `v`, `i`: the reader and its step; `l`: the step leaving the
  reader's state.

Read aloud: what an honest validator confirmed while its clock was before slot `s` is a strict
ancestor of a slot-`s` block an honest validator confirms. -/
theorem confirmed_strict_ancestor_of_agree (U : UniformSchedule M.toSlotLayout) {S : Setup V}
    {A : Activity V} (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject Vocab.goldilocks)
    {tE t s : ℕ} (hAgree : ConfirmedAgreeBetween M S A x tE t)
    {b : Block V} (hbs : b.slot = s)
    -- `p` is honest through `j₁`, at a time from `tE` to `t`, and has `b` as its confirmed tip in
    -- the state `j₁` leaves
    {p : V} {j₁ : ℕ} (hpC : M.ac_confirmed (x.st (j₁ + 1) p) = b)
    (hpH : A.HonestThroughTime x (x.time j₁) p) (hj₁E : (tE : ℝ) ≤ x.time j₁)
    (hj₁t : x.time j₁ ≤ t)
    -- `v` is outside the adversary set after `i` steps, with its clock before slot `s`
    {v : V} {i : ℕ} (hvi : v ∉ A.corrupted i) (hc : x.clockValue i v < M.slotStart S.C s)
    -- the step `l`, at a time from `tE` to `t`, leaves `v`'s state after `i` steps
    {l : ℕ} (hvl : A.HonestThroughTime x (x.time l) v) (hlE : (tE : ℝ) ≤ x.time l)
    (hlt : x.time l ≤ t) (hlst : x.st (l + 1) v = x.st i v) :
    (M.ac_confirmed (x.st i v)).AncestorEq b ∧ M.ac_confirmed (x.st i v) ≠ b := by
  have hCT : M.ac_confirmed (x.st i v) ∈ (x.st i v).tree :=
    (ac_confirmed_mem_tree M F) _
      (F.nd.nodeInv_finalized_mem_tree (lem11_node_invariant M F S A x R E i v hvi).1)
  have hnot : ¬ b.AncestorEq (M.ac_confirmed (x.st i v)) := fun h => by
    have := (slot_lt_of_ancestorEq_held_clock M F U) x R E hvi hCT h hc
    omega_nat
  have hcomp := hAgree v p l j₁ hvl hpH hlE hj₁E hlt hj₁t
  rw [show (x.map (nodeView M)).st (l + 1) v = (x.map (nodeView M)).st i v by
    simp only [Trace.map_st, hlst]] at hcomp
  rcases hcomp with h | h
  · have h' : (M.ac_confirmed (x.st i v)).AncestorEq b := by
      rw [← hpC]
      exact h
    refine ⟨h', fun heq => hnot ?_⟩
    rw [← heq]
    exact ancestorEq_refl _
  · have h' : b.AncestorEq (M.ac_confirmed (x.st i v)) := by
      rw [← hpC]
      exact h
    exact absurd h' hnot

omit [RootOrder] in
/-- **Kit fact, the slots after the healing phase.** Every slot starting after the end `tAwakeEnd`
of a healing phase whose honest round opening slots start at or after
`tGAT + 4Δ · healFrontSlots S` is at least `2`.

Why: the last honest round opening slot's support cutoff is at most `tAwakeEnd`, and that slot
starts at or after the first one, which starts at or after `4Δ · healFrontSlots S ≥ 4Δ`, the start
of slot `1`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `A`: the activity; `r`: the rounds of the honest round opening slots; `m`: the
  index of the last one; `tGAT`, `tAwakeEnd`: the start and end of the healing phase.

Read aloud: a slot starting at or after the end of the healing phase is at least slot `2`. -/
theorem two_le_of_after_phase (U : UniformSchedule M.toSlotLayout) {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N}
    {r : ℕ → ℕ} {m tGAT tAwakeEnd : ℕ}
    (hSeq : HonestOpeningSeq M S A x r m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd) :
    ∀ s : ℕ, tAwakeEnd ≤ M.slotStart S.C s → 2 ≤ s := by
  intro s hs
  have h0 : r 0 ≤ r m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h]
    · exact le_of_lt (GoldilocksCorrectness.Proofs.Executions.r_lt_of_lt_of_mono r m hSeq.mono 0 m
        h le_rfl)
  have hmono := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched)
    S (Nat.mul_le_mul_right S.C.R h0)
  have hc := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U)
    S (r m * S.C.R)
  have hv := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U)
    S (r m * S.C.R)
  have hf := hSeq.first
  have hl := hSeq.last
  have hfs : 1 ≤ healFrontSlots S := by
    unfold healFrontSlots
    omega
  have h4 : 4 * Δ S * 1 ≤ 4 * Δ S * healFrontSlots S := Nat.mul_le_mul_left _ hfs
  have hΔ := GoldilocksCorrectness.Proofs.Routines.one_le_Δ S
  rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U)] at hs
  by_contra hlt
  have h5 : 4 * Δ S * s ≤ 4 * Δ S * 1 := Nat.mul_le_mul_left _ (by omega)
  omega

/-! ## Lemma 90's fourth conclusion -/

/-- **Lemma 90's fourth conclusion, read up to `t`, from its agreement and its inclusion.** When
every slot starting at or after `tE` is at least `2`, the agreement of the confirmed tips from `tE`
up to `t` (`ConfirmedAgreeBetween`) and the inclusion of the honest proposals
(`ConfirmedIncludedBetween`) give `ConfirmedExtendedByHonestProposalsBetween M S A x tE t`.

Why: for an honest proposal `B` of slot `s` without a root collision, the proposer, an honest
active validator of slot `s`, has `B` as its confirmed tip in the state its own tick `k'` to the
support cutoff of slot `s + 1` leaves (the inclusion), and that tick is at a time from `tE` to `t`
, with the proposer honest through it. A confirmed tip `C` of a validator honest through a step `i` at a time from `tE` on,
in the state step `i` leaves and read while its clock there is before the start of slot `s`
, is the one a step `l` at a time from `tE` to `t` leaves: `i` itself when its time is
at most `t`, otherwise a step from which the state was kept (`exists_state_kept_from_time_le`,
`exists_step_near_clock`). So the agreement at `l` and `k'` makes it compatible with `B`; `C` is
held, so `B`, of slot `s` (`proposal_slot_parent`), is not `C` or an ancestor of `C`: `C` is an
ancestor of `B` other than `B` (`confirmed_strict_ancestor_of_agree`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `A`: the activity; `x`: the trace; `R`: the run's facts; `E`: the environment's
  facts; `hSkew`: the clock bounds are less than `Δ`; `tE`: the time from which the slots are read; `t`: the
  time up to which the updates are read. -/
theorem confirmedExtendedBetween_of_agree_included (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject Vocab.goldilocks)
    (hSkew : ΔClockAhead + ΔClockBehind < (Δ S : ℝ))
    (tE t : ℕ)
    -- every slot starting at or after `tE` is at least `2`
    (h2 : ∀ s : ℕ, tE ≤ M.slotStart S.C s → 2 ≤ s)
    -- Lemma 90's agreement and inclusion from `tE` up to `t`
    (hAgree : ConfirmedAgreeBetween M S A x tE t)
    (hIncl : ConfirmedIncludedBetween M S A x tE t) :
    ConfirmedExtendedByHonestProposalsBetween M S A x tE t := by
  intro s hs hct hst hop b hb
  -- the proposer is outside the adversary set at every step at a time at most its own tick to the
  -- cutoff (`HonestOpenerAt`'s second member,)
  have hpT := fun h => hop.2 (Finset.mem_union_left _ (Finset.mem_union_right _ h))
  obtain ⟨q, rfl⟩ : ∃ q, s = q + 2 := ⟨s - 2, by have := h2 s hs; omega⟩
  have hBslot : b.slot = q + 2 :=
    ((proposal_slot_parent M F U) S A x R E (by omega) (proposalAt_of_proposalAtV M hb)).1
  have hp := (opener_mem_honestActiveAt M F U) S A R E q hop
  have hpU := (honestActiveAt_subset_updaterAt M F) S A x R E (q + 2) hp
  obtain ⟨k', hk', -⟩ := Activity.mem_activeThroughoutToTick.1 hpU
  have hks : x.tickStep (S.P.proposer (q + 2)) (M.supportCutoff S.C (q + 2 + 1)) = k' :=
    (tickStep_eq_of_lbl M) x E hk'
  have hkt := (time_of_lbl_tick M) x R E hk'
  have hk't : x.time k' ≤ t := by
    have h := hst
    simp only [Trace.map_time, Trace.map_tickStep] at h
    rwa [hks] at h
  -- case (2): the proposer's honesty through its tick, from the new clause
  have hpH : A.HonestThroughTime x (x.time k') (S.P.proposer (q + 2)) := by
    have h := hpT
    simp only [Trace.map_time, Trace.map_tickStep, hks] at h
    exact Activity.not_mem_corruptedAtTime_iff_honestThroughTime.1 h
  -- case (1): the inclusion, under the cutoff antecedent
  rcases (hIncl (q + 2) hs hct hop).2 b hb with hcol | ⟨hfirst, -⟩
  · exact Or.inl hcol
  right
  intro v i hv hi hlt
  change (tE : ℝ) ≤ x.time i at hi
  have hlt' : x.clockValue (i + 1) v < M.slotStart S.C (q + 2) := by
    simpa only [Trace.map_clockValue] using hlt
  have hconf := hfirst _ hp hst
  have hconf₀ : M.ac_confirmed (x.tickOutput (S.P.proposer (q + 2)) (M.supportCutoff S.C (q + 2 + 1))) = b :=
    hconf
  have hconf' : M.ac_confirmed (x.st (k' + 1) (S.P.proposer (q + 2))) = b := by
    unfold Trace.tickOutput at hconf₀
    rw [hks] at hconf₀
    exact hconf₀
  have hgap := (slotStart_add_le_supportCutoff_succ M F U) S (q + 2)
  have h6 : ((tE + 6 * Δ S : ℕ) : ℝ) ≤ ((M.supportCutoff S.C (q + 2 + 1) : ℕ) : ℝ) := by
    exact_mod_cast (Nat.add_le_add_right hs _).trans hgap
  push_cast at h6
  have hΔ : (1 : ℝ) ≤ (Δ S : ℝ) := by
    exact_mod_cast GoldilocksCorrectness.Proofs.Routines.one_le_Δ S
  have hA := E.ahead_nonneg
  have hB := E.behind_nonneg
  have hk'E : (tE : ℝ) ≤ x.time k' := by linarith [hkt.1.1]
  have ht : ((M.supportCutoff S.C (q + 2 + 1) : ℕ) : ℝ) - ΔClockAhead ≤ t := hkt.1.1.trans hk't
  have hhon : ∀ l : ℕ, l ≤ i → A.HonestThroughTime x (x.time l) v := fun l hl j hj =>
    hv j (hj.trans ((time_mono M) x R hl))
  -- case (3) is gone: the step leaving the reader's state is `i` itself when its time is at most
  -- `t`, and otherwise a step at a time from `tE` to `t` from which the state was kept
  have hstep : ∃ l : ℕ, (tE : ℝ) ≤ x.time l ∧ x.time l ≤ t ∧ A.HonestThroughTime x (x.time l) v ∧
      x.st (l + 1) v = x.st (i + 1) v := by
    by_cases hti : x.time i ≤ t
    · exact ⟨i, hi, hti, hv, rfl⟩
    push_neg at hti
    obtain ⟨k, hki, hkT, hkst⟩ := (exists_state_kept_from_time_le M) R E (i + 1) v
    have h1 : ((x.clockValue (i + 1) v : ℕ) : ℝ) + 1 ≤ (M.slotStart S.C (q + 2) : ℝ) := by
      exact_mod_cast hlt'
    have h6' : ((M.slotStart S.C (q + 2) + 6 * Δ S : ℕ) : ℝ) ≤
        ((M.supportCutoff S.C (q + 2 + 1) : ℕ) : ℝ) := by exact_mod_cast hgap
    push_cast at h6'
    have hkt : x.time k ≤ t := by linarith
    by_cases hk1 : ∃ l : ℕ, l + 1 = k ∧ (tE : ℝ) ≤ x.time l
    · obtain ⟨l, rfl, hlE⟩ := hk1
      exact ⟨l, hlE, ((time_mono M) x R (Nat.le_succ l)).trans hkt, hhon l (by omega),
        hkst (l + 1) le_rfl hki⟩
    push_neg at hk1
    set t' : ℕ := tE + ⌈ΔClockAhead⌉₊ + 1 with ht'
    obtain ⟨l, hl1, hl2⟩ := (exists_step_near_clock M) E v (t := t') (by omega)
    have hc1 : ΔClockAhead ≤ (⌈ΔClockAhead⌉₊ : ℝ) := Nat.le_ceil _
    have hc2 : (⌈ΔClockAhead⌉₊ : ℝ) < ΔClockAhead + 1 := Nat.ceil_lt_add_one hA
    have ht'R : (t' : ℝ) = (tE : ℝ) + ⌈ΔClockAhead⌉₊ + 1 := by rw [ht']; push_cast; ring
    have hlE : (tE : ℝ) + 1 ≤ x.time l := by linarith
    have hlt : x.time l ≤ t := by linarith
    have hli : l ≤ i := by
      by_contra h
      have := (time_mono M) x R (show i ≤ l by omega)
      linarith
    have hkl : k ≤ l + 1 := by
      by_contra h
      obtain ⟨m, hm⟩ : ∃ m : ℕ, k = m + 1 := ⟨k - 1, by omega⟩
      have hm' := hk1 m hm.symm
      have := (time_mono M) x R (show l ≤ m by omega)
      linarith
    exact ⟨l, by linarith, hlt, hhon l hli, hkst (l + 1) hkl (by omega)⟩
  obtain ⟨l, hlE, hlt2, hvl, hlst⟩ := hstep
  -- the reader's honesty after step `i`: a tick, restart or delivery keeps the adversary set; a
  -- step of the kind `other` keeps the reader's state and clock, so the helper is read at `i`
  by_cases hoth : x.lbl i = Event.other
  · have hst1 : x.st (i + 1) v = x.st i v :=
      R.untouched i v (fun t h => by rw [hoth] at h; cases h)
        (fun t keep h => by rw [hoth] at h; cases h)
        (fun sm h => by rw [hoth] at h; cases h)
    have hcv : x.clockValue (i + 1) v = x.clockValue i v :=
      x.clockValue_succ_of_not (fun t h => by rw [hoth] at h; cases h)
        (fun t keep h => by rw [hoth] at h; cases h)
    rw [hst1] at hlst
    rw [hcv] at hlt'
    have hres := (confirmed_strict_ancestor_of_agree M F U) x R E hAgree hBslot hconf' hpH hk'E hk't
      (hv i le_rfl) hlt' hvl hlE hlt2 hlst
    rw [← hst1] at hres
    exact hres
  · have hvi : v ∉ A.corrupted (i + 1) := by
      rw [E.corrupted_keep i hoth]
      exact hv i le_rfl
    exact (confirmed_strict_ancestor_of_agree M F U) x R E hAgree hBslot hconf' hpH hk'E hk't
      hvi hlt' hvl hlE hlt2 hlst

/-- **Lemma 90's fourth conclusion, with no upper end, from its agreement and its inclusion.** When
every slot starting at or after `tE` is at least `2`, `ConfirmedAgreeAfterHealing` and
`ConfirmedIncludedAfterHealing` give `ConfirmedExtendedByHonestProposals M S A x tE`.

Why: at a slot `s`, both read up to the time `t`, the larger of the support cutoff of slot `s + 1`
and the least whole number at least the time of the proposer's tick to that cutoff
(`confirmedAgreeAfterHealing_iff`, `confirmedIncludedAfterHealing_iff`), and
`confirmedExtendedBetween_of_agree_included` at that time.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `A`: the activity; `x`: the trace; `R`: the run's facts; `E`: the environment's
  facts; `hSkew`: the clock bounds are less than `Δ`; `tE`: the time from which the slots are read. -/
theorem confirmedExtended_of_agree_included (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject Vocab.goldilocks)
    (hSkew : ΔClockAhead + ΔClockBehind < (Δ S : ℝ))
    (tE : ℕ)
    -- every slot starting at or after `tE` is at least `2`
    (h2 : ∀ s : ℕ, tE ≤ M.slotStart S.C s → 2 ≤ s)
    -- Lemma 90's agreement and inclusion from `tE` on
    (hAgree : ConfirmedAgreeAfterHealing M S A x tE)
    (hIncl : ConfirmedIncludedAfterHealing M S A x tE) :
    ConfirmedExtendedByHonestProposals M S A x tE := by
  intro s hs hop b hb
  refine (confirmedExtendedBetween_of_agree_included M F U) S A x R E hSkew tE
    (max (M.supportCutoff S.C (s + 1))
      ⌈x.time (x.tickStep (S.P.proposer s) (M.supportCutoff S.C (s + 1)))⌉₊) h2
    (((confirmedAgreeAfterHealing_iff M) S A x tE).1 hAgree _)
    (((confirmedIncludedAfterHealing_iff M) S A x tE).1 hIncl _) s hs (le_max_left _ _) ?_ hop b hb
  simp only [Trace.map_time, Trace.map_tickStep]
  exact (Nat.le_ceil _).trans (by exact_mod_cast le_max_right _ _)

/-! ## Lemma 98's second conclusion -/

/-- **Lemma 98's second conclusion from Lemma 86's compatibility and Lemma 98's first.** When the
finalized blocks of validators honest through steps at times at most `t` are pairwise compatible
(Lemma 86 read up to `t`), `FinalityIncludedBetween M S A x Δs tE t` gives
`FinalizedExtendedByHonestProposalsBetween M S A x Δs tE t`.

Why: for a proposal `B` of slot `s` without a root collision, and a reader `v` after step `j`
(at or before some support cutoff at most `t`, so at a time at most `t`), `FinalityIncludedBetween`
makes `B` an ancestor of, or equal to, `v`'s finalized block, and that finalized block one no
validator had after a step at a time before the start of slot `s`. A
finalized block `F'` of a validator honest through a step at a time from `tE` to before the start
of slot `s` is so not `v`'s, and is compatible with it (Lemma 86, both steps at times at most `t`).
If `v`'s were an ancestor of `F'`, then `B` would be an ancestor of a block held before slot `s`
starts, while `B` has the slot `s` (`proposal_slot_parent`, `slot_lt_of_ancestorEq_held_clock`);
and `F'` is not `v`'s, for `B` is an ancestor of `v`'s. Lemma 86 is read at a step at a time at most
`t` at which `w` already held `F'`.
So `F'` is an ancestor of `v`'s other than it.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `A`: the activity; `x`: the trace; `R`: the run's facts; `E`: the environment's
  facts; `hSkew`: the clock bounds are less than `Δ`; `Δs`: the sync delay; `tE`: the time from which the
  slots are read; `t`: the time that decides the readers (a reader's step is at or before some
  support cutoff at most `t`). -/
theorem finalizedExtendedBetween_of_compatible_included (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject Vocab.goldilocks)
    (hSkew : ΔClockAhead + ΔClockBehind < (Δ S : ℝ))
    (Δs tE t : ℕ)
    -- Lemma 86 read up to `t`: the finalized blocks of honest validators are compatible
    (hCompat : ∀ (v₁ v₂ : V) (i j : ℕ), x.HonestThrough A i v₁ → x.HonestThrough A j v₂ →
      x.time i ≤ t → x.time j ≤ t →
      (x.st i v₁).finalized.compatible (x.st j v₂).finalized = true)
    -- Lemma 98's first conclusion from `tE` up to `t`
    (hIncl : FinalityIncludedBetween M S A x Δs tE t) :
    FinalizedExtendedByHonestProposalsBetween M S A x Δs tE t := by
  intro s r hs hop hsr hwin hcut b hb
  -- a proposal of slot `0`: no clock value is before the start of slot `0`
  rcases Nat.eq_zero_or_pos s with h0 | hs1
  · subst h0
    refine Or.inr (Or.inr fun v j _ _ _ w i _ _ hlt => ?_)
    have hlt' : x.clockValue i w < M.slotStart S.C 0 := by
      simpa only [Trace.map_clockValue] using hlt
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U),
      Nat.mul_zero] at hlt'
    exact absurd hlt' (Nat.not_lt_zero _)
  have hBslot : b.slot = s :=
    ((proposal_slot_parent M F U) S A x R E hs1 (proposalAt_of_proposalAtV M hb)).1
  rcases (hIncl s r hs hop hsr hwin hcut).2 b hb with hc | hc | hmain
  · exact Or.inl hc
  · exact Or.inr (Or.inl hc)
  right; right
  intro v j hv hjc hAw w i hw _ hlt
  have hlt' : x.clockValue i w < M.slotStart S.C s := by
    simpa only [Trace.map_clockValue] using hlt
  -- the reader's step is at or before a support cutoff at most `t`, so at a time at most `t`
  have hjt : x.time j ≤ t := by
    obtain ⟨s', h₁, h₂⟩ := hjc
    exact le_trans h₁ (by exact_mod_cast h₂)
  obtain ⟨hBF, -⟩ := hmain v j hv hjc hAw
  -- the support cutoff of slot `s + 1` is at most `t`
  have hst : M.supportCutoff S.C (s + 1) ≤ t := by
    have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout
      F.sched) S (show s + 1 ≤ (r + 3) * S.C.R + 1 from
        Nat.succ_le_succ (le_trans hsr (Nat.mul_le_mul_right _ (by omega))))
    omega
  have hwi : w ∉ A.corrupted i := hw i le_rfl
  have hFT : (x.st i w).finalized ∈ (x.st i w).tree :=
    F.nd.nodeInv_finalized_mem_tree (lem11_node_invariant M F S A x R E i w hwi).1
  have hnot : ¬ b.AncestorEq (x.st i w).finalized := fun h => by
    have := (slot_lt_of_ancestorEq_held_clock M F U) x R E hwi hFT h hlt'
    omega_nat
  -- `w`'s state after `i` steps is its state at a step at a time at most `t`
  obtain ⟨k, hki, hkt, hkst⟩ := (exists_state_kept_le_of_clockValue_lt M F U) R E hSkew hlt' hst
  have hwk : x.HonestThrough A k w := R.honestThrough_of_le hki hw
  have hcomp := hCompat w v k j hwk ((honestThrough_of_honestThroughTime M) x R hv) hkt hjt
  rw [hkst k le_rfl hki] at hcomp
  rcases (compatible_iff _ _).1 hcomp with h | h
  · refine ⟨h, fun heq => hnot ?_⟩
    have heq' : (x.st i w).finalized = (x.st j v).finalized := heq
    rw [heq']
    exact hBF
  · exact absurd (ancestorEq_trans hBF h) hnot

end GoldilocksCorrectness.Record.Proofs.Executions
