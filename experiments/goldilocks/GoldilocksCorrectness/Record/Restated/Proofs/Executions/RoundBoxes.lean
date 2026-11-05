module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma80
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Boxes
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.HeightInvariantStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.FGStateReaders
public import GoldilocksCorrectness.Proofs.Executions.Lemma80
public import GoldilocksCorrectness.Proofs.Executions.Boxes
public import GoldilocksCorrectness.Statements.Executions.HeightInvariantStatements
public import GoldilocksCorrectness.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Proofs.Routines.FGStateReaders
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# RoundBoxes, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/RoundBoxes.lean`, over a model `M` whose
facts `F` hold, for an execution `x` of `protocolOf M S`: Lemma 80 in the three boxes, the box
instances of its hypotheses and its corollaries, and the box corollaries of the round's height
advance read at the first slot's reading points, read with the greatest chain-state height `hMax M
S.C n` of the node's tree in place of the cache `h_max`. The page's routine-level theorems are the
facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ Δ_F slotStart voteTime supportCutoff
  dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_eq slot_eq_of_mem supportCutoff_eq
  voteTime_eq)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor ConfirmationUpdated LocksRevoked
  VoterTreeAt hMax)

open GoldilocksCorrectness.Record.Statements.Routines (BoxOne BoxThree BoxTwo CountedVotes
  FrameShape ProposalCountedVotes)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (Vocab.goldilocks acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (expireLocks)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  ancestorEq_of_parent?)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- An honest proposal of slot `s` is at a slot `s ≥ 1`, its parent is an ancestor of it, and
`head_height_floor` at the proposer before the start of slot `s` is at most its chain-state height,
when its parent is in the proposer's viable tree: a tick proposes only at a slot after the first
(Lemma 19), and then `proposal_parent_walk_end` and `proposal_viable` apply.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot; `B`: the proposal;
  `p`: its proposer.

Read aloud: an honest proposal of slot `s` is at a slot `s ≥ 1`, its parent is `B`'s ancestor, and
`head_height_floor` at its proposer before slot `s` is at most its chain-state height. -/
theorem proposal_facts_at (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (s : ℕ) (B : Block V) (p : V)
    -- `p` put `B` on the wire at its tick at the start of slot `s`
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    -- `B`'s parent is in `p`'s viable tree
    (hParentIn : B.parent ∈ M.viable_tree (M.fg_to_ac (x.tickInput p (M.slotStart S.C s)))
      (M.fg_to_ac (x.tickInput p (M.slotStart S.C s))).tree) :
    1 ≤ s ∧ B.parent.AncestorEq B ∧
      M.head_height_floor (x.tickInput p (M.slotStart S.C s)) ≤ (M.chainStateOf S.C B).h := by
  obtain ⟨i, hl, hsent⟩ := hPropose
  have h1 : 1 ≤ s := by
    obtain ⟨-, n', sent, hrun, hB⟩ := (tick_send_of_honestSendAt M F R E) hl hsent
    -- the tick's input state satisfies the node invariant (a wake keeps it)
    have hInvT : M.nodeInv S.C S.P S.X (x.tickInput p (M.slotStart S.C s)) := by
      rw [show x.tickInput p (M.slotStart S.C s) = x.st i p by
        unfold Trace.tickInput
        rw [(tickStep_eq_of_lbl M) x E (i := i) (v := p) (by assumption)]]
      exact (lem11_node_invariant M F S A x R E i p (E.not_mem_corrupted_of_tick hl)).1
    have hpos := ((GoldilocksCorrectness.Record.Statements.Routines.lem19_tick_proposes F) S.C S.P S.X _ n' _
      sent B hrun hInvT hB).1
    have hΔ := one_le_Δ S
    have hss : M.slotStart S.C (s + 1) = M.slotStart S.C s + 4 * Δ S := by
      rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add, Nat.mul_one]
    -- the record's Lemma 19 reads the spec's slot of the time
    rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast,
      ← (GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U),
      (GoldilocksCorrectness.Record.Proofs.Routines.slot_eq_of_mem M.toSlotLayout F.sched) S (le_refl _)
        (by omega)] at hpos
    exact hpos
  have hsm : s - 1 + 1 = s := by omega
  have hl' : x.lbl i = Event.tick p (M.slotStart S.C (s - 1 + 1)) := by rw [hsm]; exact hl
  obtain ⟨-, -, hpar, -⟩ := (proposal_parent_walk_end M F U) S A x R E (s - 1) i B p hl' hsent
  have hv := (proposal_viable M F U) S A x R E (s - 1) B p ⟨i, hl', hsent⟩ (by rw [hsm]; exact hParentIn)
  rw [hsm] at hv
  exact ⟨h1, ancestorEq_of_parent? hpar, hv⟩

/-- **Kit fact, a reader is active from any of its own ticks inside its window.** When `v` ticks to
`b`, active at every step up to that tick from the trace's start or from its own tick to a clock value
at most `a`, and step `kc` is `v`'s tick to a clock value `c` greater than `a`, then `v` is active at
every step from `kc` to its tick to `b`.

Why: in the reader's first case `v` is active at every step up to its tick to `b`; in the second, its
tick to a value at most `a` comes before its tick to `c` (`tick_lt_of_clock_lt`).

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `v`: the validator; `a`,
  `b`: the reader's window; `c`, `kc`: the clock value and the step of `v`'s tick inside it.

Read aloud: a reader is active from each of its own ticks after the window's start up to its tick to
the window's end. -/
theorem active_from_tick_of_reader {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N}
    (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {v : V} {a : ℤ} {b c kc : ℕ} (hv : v ∈ A.activeThroughoutToTick x a b)
    (hkc : x.lbl kc = Event.tick v c) (hac : a < (c : ℤ)) :
    ∀ j : ℕ, kc ≤ j → j ≤ x.tickStep v b → v ∈ A.active j := by
  obtain ⟨k', hk', hcase⟩ := Activity.mem_activeThroughoutToTick.1 hv
  rw [(tickStep_eq_of_lbl M) x E hk']
  intro j hj1 hj2
  rcases hcase with hall | ⟨k₀, -, c₀, hc₀, hk₀, hwin⟩
  · exact hall j hj2
  · have : k₀ < kc := (tick_lt_of_clock_lt M) x E hk₀ hkc (by omega)
    exact hwin j (by omega) hj2

/-- **Kit fact, a member's ticks over a round's window.** When `v` ticks to the start of slot `s''`,
active up to that tick from the trace's start or from its own tick to a clock value at most
`duty_window_start S.C s`, with `1 ≤ s`, the support cutoff of slot `s + 1` at most the start of slot
`s''`, and the clock bounds less than one delay together: `v` ticks to the start of slot `s` and to the
support cutoff of slot `s + 1`, these two ticks and its tick to the start of slot `s''` are in that order,
and `v` is active at every step from its tick to the start of slot `s` to its tick to the start of slot
`s''`.

Why: both clock values lie inside the reader's window by more than both clock bounds
(`mem_activeThroughoutToTick_of_inside`: the window opens `4 Δ k − Δ ≥ 7 Δ` before the start of slot `s`,
and the start of slot `s''` is at least the start of slot `s + 2`); the order is the clock values' order
(`tick_lt_of_clock_lt`); the activity is `active_from_tick_of_reader`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`, `R`, `E`: the setup, the activity, the execution, the run's facts, the environment's
  facts; `s`, `s''`: the window's slots; `v`: the member.

Read aloud: a member of a round's window ticks to the round's first slot start and to its support
cutoff in order before the window's end, and is active between its first and last ticks. -/
theorem member_box_window (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (s s'' : ℕ) (v : V) (hs1 : 1 ≤ s)
    (hs'' : M.supportCutoff S.C (s + 1) ≤ M.slotStart S.C s'')
    (hv : v ∈ A.activeThroughoutToTick x (duty_window_start S.C s) (M.slotStart S.C s'')) :
    x.lbl (x.tickStep v (M.slotStart S.C s)) = Event.tick v (M.slotStart S.C s) ∧
    x.lbl (x.tickStep v (M.supportCutoff S.C (s + 1))) =
      Event.tick v (M.supportCutoff S.C (s + 1)) ∧
    x.tickStep v (M.slotStart S.C s) < x.tickStep v (M.supportCutoff S.C (s + 1)) ∧
    x.tickStep v (M.supportCutoff S.C (s + 1)) < x.tickStep v (M.slotStart S.C s'') ∧
    (∀ j : ℕ, x.tickStep v (M.slotStart S.C s) ≤ j → j ≤ x.tickStep v (M.slotStart S.C s'') →
      v ∈ A.active j) := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  obtain ⟨-, -, -, hs1', -, hk8, hΔ⟩ := (slot_times M F U) S s
  obtain ⟨-, hc1, -, hs2, -, -, -⟩ := (slot_times M F U) S (s + 1)
  rw [show s + 1 + 1 = s + 2 from rfl] at hs2
  have hss := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s
  have hs2' : s + 2 ≤ s'' := by
    by_contra h
    push_neg at h
    have := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_le_of_le M.toSlotLayout F.sched) S
      (show s'' ≤ s + 1 by omega)
    omega
  have hm2 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_le_of_le M.toSlotLayout F.sched) S hs2'
  have hdw := duty_window_start_real S s
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hk8R : (8 : ℝ) * Δ S ≤ 4 * Δ S * S.C.k := by exact_mod_cast hk8
  have hssR : ((M.slotStart S.C s : ℕ) : ℝ) = 4 * Δ S * s := by rw [hss]; push_cast; ring
  have hn1 : M.slotStart S.C s + 6 * Δ S = M.supportCutoff S.C (s + 1) := by omega
  have hn2 : M.supportCutoff S.C (s + 1) + 2 * Δ S ≤ M.slotStart S.C s'' := by omega
  have hr1 : ((M.slotStart S.C s : ℕ) : ℝ) + 6 * Δ S = M.supportCutoff S.C (s + 1) := by
    exact_mod_cast hn1
  have hr2 : ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + 2 * Δ S ≤ M.slotStart S.C s'' := by
    exact_mod_cast hn2
  have hdwR : ((duty_window_start S.C s : ℤ) : ℝ) + ΔClockBehind <
      ((M.slotStart S.C s : ℕ) : ℝ) - ΔClockAhead := by
    rw [hdw, hssR]; linarith
  have hst1 : 1 ≤ M.slotStart S.C s := by
    rw [hss]; exact Nat.mul_pos (Nat.mul_pos (by norm_num) hΔ) hs1
  have hvs := (mem_activeThroughoutToTick_of_inside M F) R E hv hst1 hdwR (by linarith)
  have hvc := (mem_activeThroughoutToTick_of_inside M F) R E hv (c := M.supportCutoff S.C (s + 1))
    (by omega) (by linarith) (by linarith)
  obtain ⟨k1, hk1, -⟩ := Activity.mem_activeThroughoutToTick.1 hvs
  obtain ⟨k2, hk2, -⟩ := Activity.mem_activeThroughoutToTick.1 hvc
  obtain ⟨k3, hk3, -⟩ := Activity.mem_activeThroughoutToTick.1 hv
  have h12 := (tick_lt_of_clock_lt M) x E hk1 hk2 (by omega)
  have h23 := (tick_lt_of_clock_lt M) x E hk2 hk3 (by omega)
  have hlt : duty_window_start S.C s < ((M.slotStart S.C s : ℕ) : ℤ) := by
    have : ((duty_window_start S.C s : ℤ) : ℝ) < ((M.slotStart S.C s : ℕ) : ℝ) := by linarith
    exact_mod_cast this
  have hact := (active_from_tick_of_reader M F) R E hv hk1 hlt
  rw [(tickStep_eq_of_lbl M) x E hk1, (tickStep_eq_of_lbl M) x E hk2, (tickStep_eq_of_lbl M) x E hk3]
  rw [(tickStep_eq_of_lbl M) x E hk3] at hact
  exact ⟨hk1, hk2, h12, h23, hact⟩

/-- `h_j_eq_of_boxTwo` at a step: in box 2 with the justified block `J₀ ≠ genesis`, `v`'s state at
step `i` has `J₀`'s height as its justification height.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `A`, `x`, `R`, `E`: the setup, the activity, the execution, the run's facts, the environment's
  facts; `i`: the step; `v`: the validator; `J₀`: the justified block.

Read aloud: in box 2 the justification height is the justified block's height. -/
theorem h_j_eq_of_boxTwo_st (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (i : ℕ) (v : V) (J₀ : Block V)
    (hBox : BoxTwo M S.C (x.st i v) J₀)
    (hJ₀ : J₀ ≠ Block.genesis) :
    (x.st i v).justifiedHeight = (M.chainStateOf S.C J₀).h := by
  obtain ⟨-, hJH, -, -, -⟩ := (GoldilocksCorrectness.Record.Statements.Executions.lem57_justification_cache_and_record M F) S A x R E i v
  have hJ : (x.st i v).justified = J₀ := hBox.2.2
  have hJH' : GoldilocksCorrectness.Record.Statements.Routines.JustifiedHeight M S.C (x.st i v) := hJH
  rcases hJH' with hg | hh
  · exact absurd (hJ.symm.trans hg) hJ₀
  · rw [hJ] at hh
    exact hh.symm

/-- `entry_block_of_boxTwo` at a step: in box 2 with the justified block `J₀ ≠ genesis` at `v`'s state
at step `i`, a block `B` on `J₀`'s chain at that state's greatest chain-state height minus one has
`J₀` as its `T_h`.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `A`, `x`, `R`, `E`: the setup, the activity, the execution, the run's facts, the environment's
  facts; `i`: the step; `v`: the validator; `B`: the block; `J₀`: the justified block.

Read aloud: in box 2 a block on the justified block's chain at the justification height has that
block as its `T_h`. -/
theorem entry_block_of_boxTwo_st (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (i : ℕ) (v : V) (B J₀ : Block V)
    (hBox : BoxTwo M S.C (x.st i v) J₀)
    (hJ₀ : J₀ ≠ Block.genesis)
    (hJB : J₀.AncestorEq B)
    (hH : (M.chainStateOf S.C B).h = hMax M S.C (x.st i v) - 1) :
    (M.chainStateOf S.C B).T_h = J₀ := by
  obtain ⟨hmax, -, hJ⟩ := hBox
  obtain ⟨-, hJH, -, -⟩ := (GoldilocksCorrectness.Record.Statements.Executions.lem57_justification_cache_and_record M F) S A x R E i v
  have hJh : (M.chainStateOf S.C J₀).h = (M.chainStateOf S.C B).h := by
    rcases hJH with hg | hh
    · exact absurd (hJ.symm.trans hg) hJ₀
    · have hh' : (M.chainStateOf S.C J₀).h = (x.st i v).justifiedHeight := by
        rw [← hJ]
        exact hh
      rw [hh', hH, hmax, Nat.add_sub_cancel]
  have hT := ((GoldilocksCorrectness.Record.Statements.Routines.lem47_chain_state_heights M F) S.C J₀
    B).2.2.2.2 hJB hJh
  rcases (lem57b_justified_is_entry M F) S A x R E i v with hg | he
  · exact absurd (hJ.symm.trans hg) hJ₀
  · have he' : (M.chainStateOf S.C (x.st i v).justified).T_h = (x.st i v).justified := he
    rw [hJ] at he'
    rw [← hT, he']

/-- Lemma 80 in box 1, its hypotheses. The proof; the audited statement is in
`Statements/Executions/RoundStatements.lean`.

The variables:
- `M`: the model; `F`: its facts.

Every member is read at its own steps: the window is the steps
from its tick to the start of slot `s` to its tick to the start of slot `s''`, its single reads
are at the states its ticks to the vote time of slot `s` and to the support cutoff of slot
`s + 1` start from, and each member ticks to the start of slot `s''`, active up to that tick
from the trace's start or from its own tick to a clock value at most `duty_window_start S.C s`.

Read aloud: in box 1 with one greatest chain-state height the round theorem's frame conditions
reduce to the box over the window and the finalized blocks' positions on the proposal's chain, and
the record hypothesis is free. -/
theorem lem80_boxOne_hypotheses (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (s s'' : ℕ) (Hon : Finset V) (X B : Block V) (p : V)
    (h₀ : Height)
    -- each member ticks to the start of slot `s''`, active up to that tick from the trace's start or
    -- from its own tick to a clock value at most `duty_window_start S.C s`
    (hHon : ∀ v ∈ Hon, v ∈ A.activeThroughoutToTick x (duty_window_start S.C s) (M.slotStart S.C s''))
    (hBox : ∀ v ∈ Hon, ∀ j : ℕ, x.tickStep v (M.slotStart S.C s) ≤ j →
      j ≤ x.tickStep v (M.slotStart S.C s'') →
      BoxOne M S.C (x.st j v) ∧ hMax M S.C (x.st j v) = h₀)
    (hFw : ∀ w ∈ Hon, (x.tickInput w (M.voteTime S.C s)).finalized.AncestorEq B.parent)
    (hFar : ∀ v ∈ Hon, (x.tickInput v (M.supportCutoff S.C (s + 1))).finalized.AncestorEq B)
    (hFafter : ∀ v ∈ Hon, ∀ j : ℕ, x.tickStep v (M.voteTime S.C s) < j →
      j ≤ x.tickStep v (M.slotStart S.C s'') →
      (x.st j v).finalized.compatible B = true)
    (hp : p ∈ Hon)
    (hs'' : M.supportCutoff S.C (s + 1) ≤ M.slotStart S.C s'')
    (hHeadP : ∃ W ∈ (x.tickInput p (M.slotStart S.C s)).tree,
      X.AncestorEq W ∧ (x.tickInput p (M.slotStart S.C s)).finalized.AncestorEq W ∧
        h₀ - 1 ≤ (M.chainStateOf S.C W).h)
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    (hParentIn : B.parent ∈ M.viable_tree (M.fg_to_ac (x.tickInput p (M.slotStart S.C s)))
      (M.fg_to_ac (x.tickInput p (M.slotStart S.C s))).tree) :
    (∀ v ∈ Hon, ∀ j : ℕ, x.tickStep v (M.slotStart S.C s) ≤ j →
      j ≤ x.tickStep v (M.slotStart S.C s'') →
      FrameShape M (x.st j v) (x.st j v).finalized (h₀ - 1)) ∧
    (∀ w ∈ Hon, (x.tickInput w (M.voteTime S.C s)).finalized.AncestorEq B.parent) ∧
    (∀ v ∈ Hon, (x.tickInput v (M.supportCutoff S.C (s + 1))).finalized.AncestorEq B) ∧
    (∀ v ∈ Hon, ∀ j : ℕ, x.tickStep v (M.voteTime S.C s) < j →
      j ≤ x.tickStep v (M.slotStart S.C s'') →
      (x.st j v).finalized.compatible B = true) ∧
    (∃ W ∈ (x.tickInput p (M.slotStart S.C s)).tree,
      X.AncestorEq W ∧ (x.tickInput p (M.slotStart S.C s)).finalized.AncestorEq W ∧
        h₀ - 1 ≤ (M.chainStateOf S.C W).h) ∧
    (∀ v ∈ Hon, (x.tickInput v (M.supportCutoff S.C (s + 1))).justifiedHeight <
        (M.chainStateOf S.C B).h) := by
  obtain ⟨hs1, hPB, hfl0⟩ := (proposal_facts_at M F U) S A x R E s B p hPropose hParentIn
  have hW := fun v (hv : v ∈ Hon) => (member_box_window M F U) S A x R E hSkew s s'' v hs1 hs'' (hHon v hv)
  have hI : ∀ v ∈ Hon, ∀ j : ℕ, x.tickStep v (M.slotStart S.C s) ≤ j →
      j ≤ x.tickStep v (M.slotStart S.C s'') → M.nodeInv S.C S.P S.X (x.st j v) := fun v hv j h1 h2 =>
    (lem11_node_invariant M F S A x R E j v
      (Activity.not_mem_corrupted_of_mem_active ((hW v hv).2.2.2.2 j h1 h2))).1
  obtain ⟨-, -, hp12, hp23, -⟩ := hW p hp
  have hShape : ∀ v ∈ Hon, ∀ j : ℕ, x.tickStep v (M.slotStart S.C s) ≤ j →
      j ≤ x.tickStep v (M.slotStart S.C s'') →
      FrameShape M (x.st j v) (x.st j v).finalized (h₀ - 1) := by
    intro v hv' j h1 h2
    have h := ((GoldilocksCorrectness.Record.Statements.Routines.frameShape_of_boxOne M F) S.C S.P S.X _
      (hI v hv' j h1 h2) (hBox v hv' j h1 h2).1).2
    rw [(hBox v hv' j h1 h2).2] at h
    exact h
  -- `head_height_floor` at `p`'s tick to the start of slot `s`, `h₀ − 1`, is at most `H`
  have hfl : h₀ - 1 ≤ (M.chainStateOf S.C B).h := by
    have h : M.head_height_floor (x.tickInput p (M.slotStart S.C s)) = h₀ - 1 :=
      (hShape p hp (x.tickStep p (M.slotStart S.C s)) le_rfl (by omega)).2
    rw [h] at hfl0
    exact hfl0
  refine ⟨hShape, hFw, hFar, hFafter, hHeadP, fun v hv' => ?_⟩
  obtain ⟨-, -, h12, h23, -⟩ := hW v hv'
  have hb : BoxOne M S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) ∧
      hMax M S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) = h₀ :=
    hBox v hv' _ h12.le h23.le
  have hb' : (x.tickInput v (M.supportCutoff S.C (s + 1))).justifiedHeight + 1 <
      hMax M S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) := hb.1
  rw [hb.2] at hb'
  unfold Height at *
  omega

/-- Lemma 80 in box 2, its hypotheses. The proof; the audited statement is in
`Statements/Executions/RoundStatements.lean`.

The variables:
- `M`: the model; `F`: its facts.

Every member is read at its own steps: the window is the steps
from its tick to the start of slot `s` to its tick to the start of slot `s''`, its single reads
are at the states its ticks to the vote time of slot `s` and to the support cutoff of slot
`s + 1` start from, and each member ticks to the start of slot `s''`, active up to that tick
from the trace's start or from its own tick to a clock value at most `duty_window_start S.C s`.

Read aloud: in box 2 the root condition is free, the values of `head_height_floor` agree because
every member's greatest chain-state height is one more than `J₀`'s height, and the lock, when set at
the greatest chain-state height minus one, is on `J₀`, which is `B`'s `T_h` when `B` is at that
height. -/
theorem lem80_boxTwo_hypotheses (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (s s'' : ℕ) (Hon Q : Finset V) (X B J₀ : Block V)
      (p : V)
    -- each member ticks to the start of slot `s''`, active up to that tick from the trace's start or
    -- from its own tick to a clock value at most `duty_window_start S.C s`
    (hHon : ∀ v ∈ Hon, v ∈ A.activeThroughoutToTick x (duty_window_start S.C s) (M.slotStart S.C s''))
    (hBox : ∀ v ∈ Hon, ∀ j : ℕ, x.tickStep v (M.slotStart S.C s) ≤ j →
      j ≤ x.tickStep v (M.slotStart S.C s'') →
      BoxTwo M S.C (x.st j v) J₀)
    (hJ₀ : J₀ ≠ Block.genesis)
    (hp : p ∈ Hon)
    (hs'' : M.supportCutoff S.C (s + 1) ≤ M.slotStart S.C s'')
    (hHeadP : ∃ W ∈ (x.tickInput p (M.slotStart S.C s)).tree,
      X.AncestorEq W ∧ J₀.AncestorEq W ∧
        hMax M S.C (x.tickInput p (M.slotStart S.C s)) - 1 ≤ (M.chainStateOf S.C W).h)
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    (hParentIn : B.parent ∈ M.viable_tree (M.fg_to_ac (x.tickInput p (M.slotStart S.C s)))
      (M.fg_to_ac (x.tickInput p (M.slotStart S.C s))).tree)
    (hQ : Q ⊆ Hon)
    (hLockJ₀ : ∀ v ∈ Q, ∀ T' : BlockId,
      (x.tickInput v (M.supportCutoff S.C (s + 1))).sentLock
        (hMax M S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) - 1) = some T' → T' = J₀.root)
            :
    (∀ v ∈ Hon, ∀ j : ℕ, x.tickStep v (M.slotStart S.C s) ≤ j →
      j ≤ x.tickStep v (M.slotStart S.C s'') →
      FrameShape M (x.st j v) J₀
        (hMax M S.C (x.tickInput p (M.slotStart S.C s)) - 1)) ∧
    J₀.AncestorEq B.parent ∧ J₀.AncestorEq B ∧ J₀.compatible B = true ∧
    (∃ W ∈ (x.tickInput p (M.slotStart S.C s)).tree,
      X.AncestorEq W ∧ J₀.AncestorEq W ∧
        hMax M S.C (x.tickInput p (M.slotStart S.C s)) - 1 ≤ (M.chainStateOf S.C W).h) ∧
    (∀ v ∈ Q,
      (x.tickInput v (M.supportCutoff S.C (s + 1))).justifiedHeight < (M.chainStateOf S.C B).h ∨
      (x.tickInput v (M.supportCutoff S.C (s + 1))).sentLock (M.chainStateOf S.C B).h = none ∨
      (x.tickInput v (M.supportCutoff S.C (s + 1))).sentLock (M.chainStateOf S.C B).h =
        some (M.chainStateOf S.C B).T_h.root) := by
  obtain ⟨hs1, hPB, hfl0⟩ := (proposal_facts_at M F U) S A x R E s B p hPropose hParentIn
  have hW := fun v (hv : v ∈ Hon) => (member_box_window M F U) S A x R E hSkew s s'' v hs1 hs'' (hHon v hv)
  have hI : ∀ v ∈ Hon, ∀ j : ℕ, x.tickStep v (M.slotStart S.C s) ≤ j →
      j ≤ x.tickStep v (M.slotStart S.C s'') → M.nodeInv S.C S.P S.X (x.st j v) := fun v hv j h1 h2 =>
    (lem11_node_invariant M F S A x R E j v
      (Activity.not_mem_corrupted_of_mem_active ((hW v hv).2.2.2.2 j h1 h2))).1
  obtain ⟨-, -, hp12, hp23, -⟩ := hW p hp
  have hBoxP : BoxTwo M S.C (x.tickInput p (M.slotStart S.C s)) J₀ :=
    hBox p hp (x.tickStep p (M.slotStart S.C s)) le_rfl (by omega)
  -- every greatest chain-state height of the window is `J₀`'s height plus one, `p`'s at the start
  -- of slot `s`
  have hmax : ∀ v ∈ Hon, ∀ j : ℕ, x.tickStep v (M.slotStart S.C s) ≤ j →
      j ≤ x.tickStep v (M.slotStart S.C s'') →
      hMax M S.C (x.st j v) = hMax M S.C (x.tickInput p (M.slotStart S.C s)) := by
    intro v hv' j h1 h2
    have hB := hBox v hv' j h1 h2
    have hjp : (x.tickInput p (M.slotStart S.C s)).justifiedHeight = (M.chainStateOf S.C J₀).h :=
      (h_j_eq_of_boxTwo_st M F) S A x R E _ p J₀ hBoxP hJ₀
    rw [hB.1, hBoxP.1, (h_j_eq_of_boxTwo_st M F) S A x R E j v J₀ hB hJ₀, hjp]
  have hShape : ∀ v ∈ Hon, ∀ j : ℕ, x.tickStep v (M.slotStart S.C s) ≤ j →
      j ≤ x.tickStep v (M.slotStart S.C s'') →
      FrameShape M (x.st j v) J₀ (hMax M S.C (x.tickInput p (M.slotStart S.C s)) - 1) := by
    intro v hv' j h1 h2
    have h := (GoldilocksCorrectness.Record.Statements.Routines.frameShape_of_boxTwo M F) S.C S.P S.X _
      (hI v hv' j h1 h2) _ (hBox v hv' j h1 h2)
    rw [hmax v hv' j h1 h2] at h
    exact h
  -- the root `J₀` is an ancestor of `B`'s parent, which is in `p`'s viable tree
  have hShapeP : FrameShape M (x.tickInput p (M.slotStart S.C s)) J₀
      (hMax M S.C (x.tickInput p (M.slotStart S.C s)) - 1) :=
    hShape p hp (x.tickStep p (M.slotStart S.C s)) le_rfl (by omega)
  have hJP : J₀.AncestorEq B.parent := by
    have hR : (M.fg_to_ac (x.tickInput p (M.slotStart S.C s))).fc_root = J₀ :=
      ((GoldilocksCorrectness.Record.Statements.Routines.lem56_frame_of_shape M F) S.C S.P S.X _
      (hI p hp (x.tickStep p (M.slotStart S.C s)) le_rfl (by omega)) _ _ hShapeP).1
    have hP := hParentIn
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_tree_iff M F)] at hP
    obtain ⟨-, hRB, -⟩ := hP
    rw [hR] at hRB
    exact hRB
  have hJB := ancestorEq_trans hJP hPB
  have hfl : hMax M S.C (x.tickInput p (M.slotStart S.C s)) - 1 ≤ (M.chainStateOf S.C B).h := by
    rw [hShapeP.2] at hfl0
    exact hfl0
  refine ⟨hShape, hJP, hJB, (compatible_iff _ _).2 (Or.inl hJB), hHeadP, fun v hvQ => ?_⟩
  -- the record: the justification height is the greatest chain-state height minus one, at most `H`;
  -- at `H` that height minus one, the lock is `T`
  have hvH := hQ hvQ
  obtain ⟨-, -, h12, h23, -⟩ := hW v hvH
  have hBv : BoxTwo M S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) J₀ := hBox v hvH _ h12.le h23.le
  have hmv : hMax M S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) =
      hMax M S.C (x.tickInput p (M.slotStart S.C s)) := hmax v hvH _ h12.le h23.le
  have hjv : hMax M S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) =
      (x.tickInput v (M.supportCutoff S.C (s + 1))).justifiedHeight + 1 := hBv.1
  by_cases hlt : (x.tickInput v (M.supportCutoff S.C (s + 1))).justifiedHeight < (M.chainStateOf S.C B).h
  · exact Or.inl hlt
  · have hH : (M.chainStateOf S.C B).h =
        hMax M S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) - 1 := by
      unfold Height at *
      omega
    right
    cases hl : (x.tickInput v (M.supportCutoff S.C (s + 1))).sentLock (M.chainStateOf S.C B).h with
    | none => exact Or.inl rfl
    | some T' =>
        right
        have hTT : T' = J₀.root := hLockJ₀ v hvQ T' (by rw [← hH]; exact hl)
        have hE := (entry_block_of_boxTwo_st M F) S A x R E _ v B J₀ hBv hJ₀ hJB hH
        rw [hTT, hE]

/-- Lemma 80 in box 3, its hypotheses. The proof; the audited statement is in
`Statements/Executions/RoundStatements.lean`.

The variables:
- `M`: the model; `F`: its facts.

Every member is read at its own steps: the window is the steps
from its tick to the start of slot `s` to its tick to the start of slot `s''`, its single reads
are at the states its ticks to the vote time of slot `s` and to the support cutoff of slot
`s + 1` start from, and each member ticks to the start of slot `s''`, active up to that tick
from the trace's start or from its own tick to a clock value at most `duty_window_start S.C s`.

Read aloud: box 3 is box 1 with `head_height_floor` the greatest chain-state height. -/
theorem lem80_boxThree_hypotheses (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (s s'' : ℕ) (Hon : Finset V) (X B : Block V) (p : V)
    (h₀ : Height)
    -- each member ticks to the start of slot `s''`, active up to that tick from the trace's start or
    -- from its own tick to a clock value at most `duty_window_start S.C s`
    (hHon : ∀ v ∈ Hon, v ∈ A.activeThroughoutToTick x (duty_window_start S.C s) (M.slotStart S.C s''))
    (hBox : ∀ v ∈ Hon, ∀ j : ℕ, x.tickStep v (M.slotStart S.C s) ≤ j →
      j ≤ x.tickStep v (M.slotStart S.C s'') →
      BoxThree M (x.st j v) ∧ hMax M S.C (x.st j v) = h₀)
    (hFw : ∀ w ∈ Hon, (x.tickInput w (M.voteTime S.C s)).finalized.AncestorEq B.parent)
    (hFar : ∀ v ∈ Hon, (x.tickInput v (M.supportCutoff S.C (s + 1))).finalized.AncestorEq B)
    (hFafter : ∀ v ∈ Hon, ∀ j : ℕ, x.tickStep v (M.voteTime S.C s) < j →
      j ≤ x.tickStep v (M.slotStart S.C s'') →
      (x.st j v).finalized.compatible B = true)
    (hp : p ∈ Hon)
    (hs'' : M.supportCutoff S.C (s + 1) ≤ M.slotStart S.C s'')
    (hHeadP : ∃ W ∈ (x.tickInput p (M.slotStart S.C s)).tree,
      X.AncestorEq W ∧ (x.tickInput p (M.slotStart S.C s)).finalized.AncestorEq W ∧
        h₀ ≤ (M.chainStateOf S.C W).h)
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    (hParentIn : B.parent ∈ M.viable_tree (M.fg_to_ac (x.tickInput p (M.slotStart S.C s)))
      (M.fg_to_ac (x.tickInput p (M.slotStart S.C s))).tree) :
    (∀ v ∈ Hon, ∀ j : ℕ, x.tickStep v (M.slotStart S.C s) ≤ j →
      j ≤ x.tickStep v (M.slotStart S.C s'') →
      FrameShape M (x.st j v) (x.st j v).finalized h₀) ∧
    (∀ w ∈ Hon, (x.tickInput w (M.voteTime S.C s)).finalized.AncestorEq B.parent) ∧
    (∀ v ∈ Hon, (x.tickInput v (M.supportCutoff S.C (s + 1))).finalized.AncestorEq B) ∧
    (∀ v ∈ Hon, ∀ j : ℕ, x.tickStep v (M.voteTime S.C s) < j →
      j ≤ x.tickStep v (M.slotStart S.C s'') →
      (x.st j v).finalized.compatible B = true) ∧
    (∃ W ∈ (x.tickInput p (M.slotStart S.C s)).tree,
      X.AncestorEq W ∧ (x.tickInput p (M.slotStart S.C s)).finalized.AncestorEq W ∧
        h₀ ≤ (M.chainStateOf S.C W).h) ∧
    (∀ v ∈ Hon, (x.tickInput v (M.supportCutoff S.C (s + 1))).justifiedHeight <
        (M.chainStateOf S.C B).h) := by
  obtain ⟨hs1, hPB, hfl0⟩ := (proposal_facts_at M F U) S A x R E s B p hPropose hParentIn
  have hW := fun v (hv : v ∈ Hon) => (member_box_window M F U) S A x R E hSkew s s'' v hs1 hs'' (hHon v hv)
  have hI : ∀ v ∈ Hon, ∀ j : ℕ, x.tickStep v (M.slotStart S.C s) ≤ j →
      j ≤ x.tickStep v (M.slotStart S.C s'') → M.nodeInv S.C S.P S.X (x.st j v) := fun v hv j h1 h2 =>
    (lem11_node_invariant M F S A x R E j v
      (Activity.not_mem_corrupted_of_mem_active ((hW v hv).2.2.2.2 j h1 h2))).1
  obtain ⟨-, -, hp12, hp23, -⟩ := hW p hp
  have hShape : ∀ v ∈ Hon, ∀ j : ℕ, x.tickStep v (M.slotStart S.C s) ≤ j →
      j ≤ x.tickStep v (M.slotStart S.C s'') →
      FrameShape M (x.st j v) (x.st j v).finalized h₀ := by
    intro v hv' j h1 h2
    have h := ((GoldilocksCorrectness.Record.Statements.Routines.frameShape_of_boxThree M F) S.C S.P S.X _
      (hI v hv' j h1 h2) (hBox v hv' j h1 h2).1).2
    rw [(hBox v hv' j h1 h2).2] at h
    exact h
  -- `head_height_floor` at `p`'s tick to the start of slot `s`, `h₀`, is at most `H`
  have hfl : h₀ ≤ (M.chainStateOf S.C B).h := by
    have h : M.head_height_floor (x.tickInput p (M.slotStart S.C s)) = h₀ :=
      (hShape p hp (x.tickStep p (M.slotStart S.C s)) le_rfl (by omega)).2
    rw [h] at hfl0
    exact hfl0
  refine ⟨hShape, hFw, hFar, hFafter, hHeadP, fun v hv' => ?_⟩
  obtain ⟨-, -, h12, h23, -⟩ := hW v hv'
  have hb : BoxThree M (x.tickInput v (M.supportCutoff S.C (s + 1))) ∧
      hMax M S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) = h₀ :=
    hBox v hv' _ h12.le h23.le
  have hj : hMax M S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) =
      (x.tickInput v (M.supportCutoff S.C (s + 1))).justifiedHeight + 1 :=
    ((GoldilocksCorrectness.Record.Statements.Routines.frameShape_of_boxThree M F) S.C S.P S.X _
      (hI v hv' _ h12.le h23.le) hb.1).1
  rw [hb.2] at hj
  unfold Height at *
  omega

/-- The members' holder row at Lemma 42's sync read time, from their readers to the start of slot `s''`.
The real-time window from `M.supportCutoff S.C (s + 1) - max (Δ S) Δs` through the sync delay `Δs` starts more than
`ΔClockBehind` after `duty_window_start S.C s` (by `hΔs`) and ends at most at the support cutoff of slot `s + 1`, more
than `ΔClockAhead` before the start of slot `s''` (by `hs''` and `hSkew_F`), so the reader covers it
(`mem_activeThroughout_of_mem_activeThroughoutToTick`).

The variables:
- `M`: the model; `F`: its facts; `w`: the member; `Δs`: the sync delay.

Read aloud: a member active up to its tick to the start of slot `s''`, from its own tick to a clock value at most
`duty_window_start S.C s`, is active through Lemma 42's sync delay for the round's first slot. -/
theorem hold42_of_reader (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (GST s s'' Δs : ℕ) (w : V)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C (s - 1))
    (hs'' : M.supportCutoff S.C (s + 1) + Δ_F S ≤ M.slotStart S.C s'')
    (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    (hw : w ∈ A.activeThroughoutToTick x (duty_window_start S.C s) (M.slotStart S.C s'')) :
    w ∈ A.activeThroughout x ((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs) := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hD0 : (0 : ℝ) ≤ Δ S := by positivity
  have hsE := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S
  have hvT := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S
  have hc := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S
  have hdwR := duty_window_start_real S s
  have hmono : M.supportCutoff S.C (s - 1) ≤ M.supportCutoff S.C (s + 1) :=
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)
  have hle : max (Δ S) Δs ≤ M.supportCutoff S.C (s + 1) := by omega
  have hcR : ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) = 4 * (Δ S : ℝ) * (s : ℝ) + 6 * Δ S := by
    rw [hc, hvT, hsE]; push_cast; ring
  have hmR : ((max (Δ S) Δs : ℕ) : ℝ) = max (Δ S : ℝ) (Δs : ℝ) := by push_cast; rfl
  have hmx : (Δs : ℝ) ≤ max (Δ S : ℝ) (Δs : ℝ) := le_max_right _ _
  have hendR : ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + Δ_F S ≤ ((M.slotStart S.C s'' : ℕ) : ℝ) := by
    exact_mod_cast hs''
  have h := (mem_activeThroughout_of_mem_activeThroughoutToTick M F) R E hw
    (a' := M.supportCutoff S.C (s + 1) - max (Δ S) Δs) (e := M.supportCutoff S.C (s + 1) - max (Δ S) Δs + Δs)
    (by rw [Nat.cast_sub hle, hdwR, hcR, hmR]; linarith)
    (by rw [Nat.cast_add, Nat.cast_sub hle, hmR]; linarith)
  rw [Nat.cast_add] at h
  exact h

/-- Lemma 80 in box 1. The proof; the audited statement is in
`Statements/Executions/RoundStatements.lean`.

Roots name blocks at every tick to a clock value at most `M.supportCutoff S.C (s'' - 1)`: the proof reads
Lemma 80 (`lem80_round_height_advances_frame`) at the same slots, which reads them per tick.

Two lines the attestations' sync route reads:
`hGSTF`, the attestations' sync delay has elapsed after `GST` by the start of slot `s''`; and `hselq`, no member
of `Q` has justified past the height of `B`'s chain state before the later of the duty window's start of slot `s`
and `GST`.

The variables:
- `M`: the model; `F`: its facts.

Every member is read at its own steps: the box and the finalized
blocks over the steps from its tick to the start of slot `s` to its tick to the start of slot `s''`, its single
reads at the states its ticks to the vote time of slot `s` and to the support cutoff of slot `s + 1` start from;
each member ticks to the start of slot `s''`, active up to that tick from the trace's start or from its own tick
to a clock value at most `duty_window_start S.C s`; the proposer from its own tick to a clock value at most
`tStart`.

Read aloud: in box 1 the round raises the height or puts the progress quorum on chain. -/
theorem lem80_boxOne (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (GST r s s'' : ℕ) (Hon Q : Finset V) (Hs : ℕ → Finset V) (H : V → Block V)
    (X B B' : Block V) (p q : V) (h₀ : Height)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    -- roots name blocks at every tick, by any validator, to a clock value at most the support cutoff of slot `s'' − 1`
    --
    (hRoots : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (s'' - 1) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    {ΔNet_F : ℕ} (E_F : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {Δs_F : ℕ} (Sy_F : SyncedWithin A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST)
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    (hs : s = r * S.C.R)
    (hs1 : 1 ≤ s)
    (hs'' : M.supportCutoff S.C (s + 1) + Δ_F S ≤ M.slotStart S.C s'')
    (hGSTF : GST + max (Δ_F S) Δs_F ≤ M.slotStart S.C s'')
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C (s - 1))
    -- each member ticks to the start of slot `s''`, active up to that tick from the trace's start or
    -- from its own tick to a clock value at most `duty_window_start S.C s`
    (hHon : ∀ v ∈ Hon, v ∈ A.activeThroughoutToTick x (duty_window_start S.C s) (M.slotStart S.C s''))
    -- the members are active through the attestations' sync delay after the later of the duty window's start
    -- of slot `s` and `GST`, where the attestations' sync fact is read
    (hHoldF : ∀ w ∈ Hon, w ∈ A.activeThroughout x ((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ)
      (((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ) + Δs_F))
    (hp : p ∈ Hon)
    -- `tStart`: a clock value more than both clock bounds before Lemma 12's read time of slot `s − 1`, the proposer's
    -- reader start (: the amended rows of the `_frame` theorems;)
    (tStart : ℤ) (htStart : (tStart : ℝ) + ΔClockAhead + ΔClockBehind <
      ((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ))
    -- the proposer ticks to the start of slot `s`, active up to that tick from the trace's start or from its own
    -- tick to a clock value at most `tStart`
    (hpR : p ∈ A.activeThroughoutToTick x tStart (M.slotStart S.C s))
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    (hHsPrev : ∀ u ∈ Hs (s - 1), u ∈ S.P.committee (s - 1) ∧
      (∀ w ∈ Hon, u ∉ A.corrupted (x.tickStep w (M.voteTime S.C s))) ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s - 1)) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u (s - 1) (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H u ∈ (x.tickInput u (M.voteTime S.C (s - 1))).tree ∧ X.AncestorEq (H u))
    -- the previous slot's voters are active through the sync delay after Lemma 12's read time of slot `s − 1`
    -- ( under)
    (hHold : ∀ u ∈ Hs (s - 1), u ∈ A.activeThroughout x ((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hVotersPrev : ∀ w ∈ Hon, ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes M S.C (x.tickInput w (M.voteTime S.C s)) s votes support_votes →
      M.voters_count votes < 2 * (Hs (s - 1)).card)
    (hApX :
        (M.get_anchor (x.tickInput p (M.slotStart S.C s))
            ((M.slotStart S.C s : ℕ) : Int)).AncestorEq X)
    (hLocksW : ∀ w ∈ Hon, ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C s))
        ((M.voteTime S.C s : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C s)) s →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.tickInput w (M.voteTime S.C s)) ((M.voteTime S.C s : ℕ) : Int) e =
          true → e.B.AncestorEq B.parent)
    (hOnly : ∀ w ∈ Hon, ∀ B₁ ∈ (x.tickInput w (M.voteTime S.C s)).tree, B₁.slot = s → B₁ = B)
    (hRootNew : ∀ B₁ ∈ (x.tickInput p (M.slotStart S.C s)).tree, B₁.root ≠ B.root)
    (hHs : ∀ s', s ≤ s' → s' < s'' → ∀ u ∈ Hs s', u ∈ Hon ∧ u ∈ S.P.committee s' ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s' ∧
        ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s') ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x.sent (i + 1) - x.sent i)
    (hVoters : ∀ s', s ≤ s' → s' < s'' → ∀ v ∈ Hon,
      (∀ votes support_votes : Finset (GoldfishVote V),
        CountedVotes M S.C (x.tickInput v (M.voteTime S.C (s' + 1)))
          (s' + 1) votes support_votes →
        M.voters_count votes < 2 * (Hs s').card) ∧
      M.voters_count (M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s' + 1))) s') < 2 *
        (Hs s').card)
    (hVotersQ : ∀ votes support_votes : Finset (GoldfishVote V),
      ProposalCountedVotes M (x.tickInput q (M.slotStart S.C s''))
        (s'' - 1) votes support_votes →
      M.voters_count votes < 2 * (Hs (s'' - 1)).card)
    (hHalf : (S.P.committee s).card ≤ 2 * (Hs s).card)
    (hBox : ∀ v ∈ Hon, ∀ j : ℕ, x.tickStep v (M.slotStart S.C s) ≤ j →
      j ≤ x.tickStep v (M.slotStart S.C s'') →
      BoxOne M S.C (x.st j v) ∧ hMax M S.C (x.st j v) = h₀)
    (hFw : ∀ w ∈ Hon, (x.tickInput w (M.voteTime S.C s)).finalized.AncestorEq B.parent)
    (hFar : ∀ v ∈ Hon, (x.tickInput v (M.supportCutoff S.C (s + 1))).finalized.AncestorEq B)
    (hFafter : ∀ v ∈ Hon, ∀ j : ℕ, x.tickStep v (M.voteTime S.C s) < j →
      j ≤ x.tickStep v (M.slotStart S.C s'') →
      (x.st j v).finalized.compatible B = true)
    (hHeadP : ∃ W ∈ (x.tickInput p (M.slotStart S.C s)).tree,
      X.AncestorEq W ∧ (x.tickInput p (M.slotStart S.C s)).finalized.AncestorEq W ∧
        h₀ - 1 ≤ (M.chainStateOf S.C W).h)
    (hParentIn : B.parent ∈ M.viable_tree (M.fg_to_ac (x.tickInput p (M.slotStart S.C s)))
      (M.fg_to_ac (x.tickInput p (M.slotStart S.C s))).tree)
    (hQ : Q ⊆ Hon)
    (hQuorum : quorum V ≤ Q.card)
    (hselq : ∀ v ∈ Q, M.justifiedHeight (x.stateBefore (max (M.dutyWindowStart S.C s) GST) v) ≤
      (M.chainStateOf S.C B).h)
    (hq : q ∈ Hon)
    -- `q` is active at every step from the real time at which the attestations' sync fact is read up to its own tick
    -- to the start of slot `s''` (the sync fact's receiver row,)
    (hqWin : ∀ i : ℕ, ((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ) ≤ x.time i →
      i ≤ x.tickStep q (M.slotStart S.C s'') → q ∈ A.active i)
    -- the voters of the last slot `s'' − 1` are outside the adversary set at `q`'s tick to the start of slot `s''`,
    -- where `q`'s proposal counts their votes
    (hHonestQ : ∀ u ∈ Hs (s'' - 1), u ∉ A.corrupted (x.tickStep q (M.slotStart S.C s'')))
    (hPropose' : ∃ i : ℕ, x.lbl i = Event.tick q (M.slotStart S.C s'') ∧
      (⟨q, NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) :
    B.AncestorEq B' ∧
    ((M.chainStateOf S.C B).h + 1 ≤ (M.chainStateOf S.C B').h ∨
      ((M.chainStateOf S.C B').h = (M.chainStateOf S.C B).h ∧
        Q ⊆ (M.chainStateOf S.C B').progress ∧
        B'.slot < (M.chainStateOf S.C B).T_h.slot + S.C.δt)) ∧
    ((∀ u ∈ Q, ∀ b ∈ (x.tickInput u (M.supportCutoff S.C (s + 1))).sentAttestations,
        b.h ≠ (M.chainStateOf S.C B).h) →
      (M.chainStateOf S.C B).h + 1 ≤ (M.chainStateOf S.C B').h ∧
        ((M.chainStateOf S.C B'.parent).h = (M.chainStateOf S.C B).h →
          (M.chainStateOf S.C B').J = (M.chainStateOf S.C B).T_h)) := by
  obtain ⟨hShape, hRootW, hRootAr, hRootAfter, hHeadP', hjlt⟩ :=
    (lem80_boxOne_hypotheses M F U) S A x R E hSkew s s'' Hon X B p h₀ hHon hBox hFw hFar hFafter hp
      (le_trans (Nat.le_add_right _ _) hs'') hHeadP hPropose hParentIn
  have hHold42 := fun w (hw : w ∈ Hon) => (hold42_of_reader M F U) S A x R E GST s s'' Δs w hΔs hGST hs'' hSkew_F (hHon w hw)
  exact (lem80_round_height_advances_frame M F U Fx) S A x R GST r s s'' Hon Q Hs H X B B' p q (h₀ - 1)
    (fun v j => (x.st j v).finalized) E hNet hSkew hRedeliver hRoots hParent hOwner E_F hNet_F hSkew_F Sy hΔs Sy_F hΔs_F
    hs hs1 hs'' hGSTF hGST hHon hHold42 hHoldF hp tStart htStart hpR hPropose hHsPrev hHold hVotersPrev hApX hLocksW
    hOnly hRootNew hHs hVoters hVotersQ hHalf hShape hRootW hRootAr hRootAfter hHeadP' hParentIn hQ hQuorum
    (fun v hv => Or.inl (hjlt v (hQ hv))) hselq hq hqWin hHonestQ hPropose'

/-- Lemma 80 in box 2. The proof; the audited statement is in
`Statements/Executions/RoundStatements.lean`.

Roots name blocks at every tick to a clock value at most `M.supportCutoff S.C (s'' - 1)`: the proof reads
Lemma 80 (`lem80_round_height_advances_frame`) at the same slots, which reads them per tick.

Two lines the attestations' sync route reads:
`hGSTF`, the attestations' sync delay has elapsed after `GST` by the start of slot `s''`; and `hselq`, no member
of `Q` has justified past the height of `B`'s chain state before the later of the duty window's start of slot `s`
and `GST`.

The variables:
- `M`: the model; `F`: its facts.

Every member is read at its own steps: the box and the finalized
blocks over the steps from its tick to the start of slot `s` to its tick to the start of slot `s''`, its single
reads at the states its ticks to the vote time of slot `s` and to the support cutoff of slot `s + 1` start from;
each member ticks to the start of slot `s''`, active up to that tick from the trace's start or from its own tick
to a clock value at most `duty_window_start S.C s`; the proposer from its own tick to a clock value at most
`tStart`.

Read aloud: in box 2 the round raises the height or puts the progress quorum on chain. -/
theorem lem80_boxTwo (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (GST r s s'' : ℕ) (Hon Q : Finset V) (Hs : ℕ → Finset V) (H : V → Block V)
    (X B B' J₀ : Block V) (p q : V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    -- roots name blocks at every tick, by any validator, to a clock value at most the support cutoff of slot `s'' − 1`
    --
    (hRoots : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (s'' - 1) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    {ΔNet_F : ℕ} (E_F : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {Δs_F : ℕ} (Sy_F : SyncedWithin A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST)
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    (hs : s = r * S.C.R)
    (hs1 : 1 ≤ s)
    (hs'' : M.supportCutoff S.C (s + 1) + Δ_F S ≤ M.slotStart S.C s'')
    (hGSTF : GST + max (Δ_F S) Δs_F ≤ M.slotStart S.C s'')
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C (s - 1))
    -- each member ticks to the start of slot `s''`, active up to that tick from the trace's start or
    -- from its own tick to a clock value at most `duty_window_start S.C s`
    (hHon : ∀ v ∈ Hon, v ∈ A.activeThroughoutToTick x (duty_window_start S.C s) (M.slotStart S.C s''))
    -- the members are active through the attestations' sync delay after the later of the duty window's start
    -- of slot `s` and `GST`, where the attestations' sync fact is read
    (hHoldF : ∀ w ∈ Hon, w ∈ A.activeThroughout x ((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ)
      (((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ) + Δs_F))
    (hp : p ∈ Hon)
    -- `tStart`: a clock value more than both clock bounds before Lemma 12's read time of slot `s − 1`, the proposer's
    -- reader start (: the amended rows of the `_frame` theorems;)
    (tStart : ℤ) (htStart : (tStart : ℝ) + ΔClockAhead + ΔClockBehind <
      ((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ))
    -- the proposer ticks to the start of slot `s`, active up to that tick from the trace's start or from its own
    -- tick to a clock value at most `tStart`
    (hpR : p ∈ A.activeThroughoutToTick x tStart (M.slotStart S.C s))
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    (hHsPrev : ∀ u ∈ Hs (s - 1), u ∈ S.P.committee (s - 1) ∧
      (∀ w ∈ Hon, u ∉ A.corrupted (x.tickStep w (M.voteTime S.C s))) ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s - 1)) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u (s - 1) (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H u ∈ (x.tickInput u (M.voteTime S.C (s - 1))).tree ∧ X.AncestorEq (H u))
    -- the previous slot's voters are active through the sync delay after Lemma 12's read time of slot `s − 1`
    -- ( under)
    (hHold : ∀ u ∈ Hs (s - 1), u ∈ A.activeThroughout x ((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hVotersPrev : ∀ w ∈ Hon, ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes M S.C (x.tickInput w (M.voteTime S.C s)) s votes support_votes →
      M.voters_count votes < 2 * (Hs (s - 1)).card)
    (hApX :
        (M.get_anchor (x.tickInput p (M.slotStart S.C s))
            ((M.slotStart S.C s : ℕ) : Int)).AncestorEq X)
    (hLocksW : ∀ w ∈ Hon, ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C s))
        ((M.voteTime S.C s : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C s)) s →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.tickInput w (M.voteTime S.C s)) ((M.voteTime S.C s : ℕ) : Int) e =
          true → e.B.AncestorEq B.parent)
    (hOnly : ∀ w ∈ Hon, ∀ B₁ ∈ (x.tickInput w (M.voteTime S.C s)).tree, B₁.slot = s → B₁ = B)
    (hRootNew : ∀ B₁ ∈ (x.tickInput p (M.slotStart S.C s)).tree, B₁.root ≠ B.root)
    (hHs : ∀ s', s ≤ s' → s' < s'' → ∀ u ∈ Hs s', u ∈ Hon ∧ u ∈ S.P.committee s' ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s' ∧
        ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s') ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x.sent (i + 1) - x.sent i)
    (hVoters : ∀ s', s ≤ s' → s' < s'' → ∀ v ∈ Hon,
      (∀ votes support_votes : Finset (GoldfishVote V),
        CountedVotes M S.C (x.tickInput v (M.voteTime S.C (s' + 1)))
          (s' + 1) votes support_votes →
        M.voters_count votes < 2 * (Hs s').card) ∧
      M.voters_count (M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s' + 1))) s') < 2 *
        (Hs s').card)
    (hVotersQ : ∀ votes support_votes : Finset (GoldfishVote V),
      ProposalCountedVotes M (x.tickInput q (M.slotStart S.C s''))
        (s'' - 1) votes support_votes →
      M.voters_count votes < 2 * (Hs (s'' - 1)).card)
    (hHalf : (S.P.committee s).card ≤ 2 * (Hs s).card)
    (hBox : ∀ v ∈ Hon, ∀ j : ℕ, x.tickStep v (M.slotStart S.C s) ≤ j →
      j ≤ x.tickStep v (M.slotStart S.C s'') →
      BoxTwo M S.C (x.st j v) J₀)
    (hJ₀ : J₀ ≠ Block.genesis)
    (hHeadP : ∃ W ∈ (x.tickInput p (M.slotStart S.C s)).tree,
      X.AncestorEq W ∧ J₀.AncestorEq W ∧
        hMax M S.C (x.tickInput p (M.slotStart S.C s)) - 1 ≤ (M.chainStateOf S.C W).h)
    (hParentIn : B.parent ∈ M.viable_tree (M.fg_to_ac (x.tickInput p (M.slotStart S.C s)))
      (M.fg_to_ac (x.tickInput p (M.slotStart S.C s))).tree)
    (hQ : Q ⊆ Hon)
    (hQuorum : quorum V ≤ Q.card)
    (hLockJ₀ : ∀ v ∈ Q, ∀ T' : BlockId,
      (x.tickInput v (M.supportCutoff S.C (s + 1))).sentLock
        (hMax M S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) - 1) = some T' → T' = J₀.root)
    (hselq : ∀ v ∈ Q, M.justifiedHeight (x.stateBefore (max (M.dutyWindowStart S.C s) GST) v) ≤
      (M.chainStateOf S.C B).h)
    (hq : q ∈ Hon)
    -- `q` is active at every step from the real time at which the attestations' sync fact is read up to its own tick
    -- to the start of slot `s''` (the sync fact's receiver row,)
    (hqWin : ∀ i : ℕ, ((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ) ≤ x.time i →
      i ≤ x.tickStep q (M.slotStart S.C s'') → q ∈ A.active i)
    -- the voters of the last slot `s'' − 1` are outside the adversary set at `q`'s tick to the start of slot `s''`,
    -- where `q`'s proposal counts their votes
    (hHonestQ : ∀ u ∈ Hs (s'' - 1), u ∉ A.corrupted (x.tickStep q (M.slotStart S.C s'')))
    (hPropose' : ∃ i : ℕ, x.lbl i = Event.tick q (M.slotStart S.C s'') ∧
      (⟨q, NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) :
    B.AncestorEq B' ∧
    ((M.chainStateOf S.C B).h + 1 ≤ (M.chainStateOf S.C B').h ∨
      ((M.chainStateOf S.C B').h = (M.chainStateOf S.C B).h ∧
        Q ⊆ (M.chainStateOf S.C B').progress ∧
        B'.slot < (M.chainStateOf S.C B).T_h.slot + S.C.δt)) ∧
    ((∀ u ∈ Q, ∀ b ∈ (x.tickInput u (M.supportCutoff S.C (s + 1))).sentAttestations,
        b.h ≠ (M.chainStateOf S.C B).h) →
      (M.chainStateOf S.C B).h + 1 ≤ (M.chainStateOf S.C B').h ∧
        ((M.chainStateOf S.C B'.parent).h = (M.chainStateOf S.C B).h →
          (M.chainStateOf S.C B').J = (M.chainStateOf S.C B).T_h)) := by
  obtain ⟨hShape, hRootW, hRootAr, hRootAfter, hHeadP', hLockBox⟩ :=
    (lem80_boxTwo_hypotheses M F U) S A x R E hSkew s s'' Hon Q X B J₀ p hHon hBox hJ₀ hp
      (le_trans (Nat.le_add_right _ _) hs'') hHeadP hPropose hParentIn hQ hLockJ₀
  have hHold42 := fun w (hw : w ∈ Hon) => (hold42_of_reader M F U) S A x R E GST s s'' Δs w hΔs hGST hs'' hSkew_F (hHon w hw)
  exact (lem80_round_height_advances_frame M F U Fx) S A x R GST r s s'' Hon Q Hs H X B B' p q
    (hMax M S.C (x.tickInput p (M.slotStart S.C s)) - 1) (fun _ _ => J₀) E hNet hSkew hRedeliver hRoots hParent hOwner
    E_F hNet_F hSkew_F Sy hΔs Sy_F hΔs_F hs hs1 hs'' hGSTF hGST hHon hHold42 hHoldF hp tStart htStart hpR hPropose
    hHsPrev hHold hVotersPrev hApX hLocksW hOnly hRootNew hHs hVoters hVotersQ hHalf hShape (fun _ _ => hRootW)
    (fun _ _ => hRootAr) (fun _ _ _ _ _ => hRootAfter) hHeadP' hParentIn hQ hQuorum hLockBox hselq hq hqWin hHonestQ
    hPropose'

/-- Lemma 80 in box 3. The proof; the audited statement is in
`Statements/Executions/RoundStatements.lean`.

Roots name blocks at every tick to a clock value at most `M.supportCutoff S.C (s'' - 1)`: the proof reads
Lemma 80 (`lem80_round_height_advances_frame`) at the same slots, which reads them per tick.

Two lines the attestations' sync route reads:
`hGSTF`, the attestations' sync delay has elapsed after `GST` by the start of slot `s''`; and `hselq`, no member
of `Q` has justified past the height of `B`'s chain state before the later of the duty window's start of slot `s`
and `GST`.

The variables:
- `M`: the model; `F`: its facts.

Every member is read at its own steps: the box and the finalized
blocks over the steps from its tick to the start of slot `s` to its tick to the start of slot `s''`, its single
reads at the states its ticks to the vote time of slot `s` and to the support cutoff of slot `s + 1` start from;
each member ticks to the start of slot `s''`, active up to that tick from the trace's start or from its own tick
to a clock value at most `duty_window_start S.C s`; the proposer from its own tick to a clock value at most
`tStart`.

Read aloud: in box 3 the round raises the height or puts the progress quorum on chain. -/
theorem lem80_boxThree (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (GST r s s'' : ℕ) (Hon Q : Finset V) (Hs : ℕ → Finset V) (H : V → Block V)
    (X B B' : Block V) (p q : V) (h₀ : Height)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    -- roots name blocks at every tick, by any validator, to a clock value at most the support cutoff of slot `s'' − 1`
    --
    (hRoots : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (s'' - 1) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    {ΔNet_F : ℕ} (E_F : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {Δs_F : ℕ} (Sy_F : SyncedWithin A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST)
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    (hs : s = r * S.C.R)
    (hs1 : 1 ≤ s)
    (hs'' : M.supportCutoff S.C (s + 1) + Δ_F S ≤ M.slotStart S.C s'')
    (hGSTF : GST + max (Δ_F S) Δs_F ≤ M.slotStart S.C s'')
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C (s - 1))
    -- each member ticks to the start of slot `s''`, active up to that tick from the trace's start or
    -- from its own tick to a clock value at most `duty_window_start S.C s`
    (hHon : ∀ v ∈ Hon, v ∈ A.activeThroughoutToTick x (duty_window_start S.C s) (M.slotStart S.C s''))
    -- the members are active through the attestations' sync delay after the later of the duty window's start
    -- of slot `s` and `GST`, where the attestations' sync fact is read
    (hHoldF : ∀ w ∈ Hon, w ∈ A.activeThroughout x ((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ)
      (((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ) + Δs_F))
    (hp : p ∈ Hon)
    -- `tStart`: a clock value more than both clock bounds before Lemma 12's read time of slot `s − 1`, the proposer's
    -- reader start (: the amended rows of the `_frame` theorems;)
    (tStart : ℤ) (htStart : (tStart : ℝ) + ΔClockAhead + ΔClockBehind <
      ((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ))
    -- the proposer ticks to the start of slot `s`, active up to that tick from the trace's start or from its own
    -- tick to a clock value at most `tStart`
    (hpR : p ∈ A.activeThroughoutToTick x tStart (M.slotStart S.C s))
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    (hHsPrev : ∀ u ∈ Hs (s - 1), u ∈ S.P.committee (s - 1) ∧
      (∀ w ∈ Hon, u ∉ A.corrupted (x.tickStep w (M.voteTime S.C s))) ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s - 1)) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u (s - 1) (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H u ∈ (x.tickInput u (M.voteTime S.C (s - 1))).tree ∧ X.AncestorEq (H u))
    -- the previous slot's voters are active through the sync delay after Lemma 12's read time of slot `s − 1`
    -- ( under)
    (hHold : ∀ u ∈ Hs (s - 1), u ∈ A.activeThroughout x ((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hVotersPrev : ∀ w ∈ Hon, ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes M S.C (x.tickInput w (M.voteTime S.C s)) s votes support_votes →
      M.voters_count votes < 2 * (Hs (s - 1)).card)
    (hApX :
        (M.get_anchor (x.tickInput p (M.slotStart S.C s))
            ((M.slotStart S.C s : ℕ) : Int)).AncestorEq X)
    (hLocksW : ∀ w ∈ Hon, ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C s))
        ((M.voteTime S.C s : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C s)) s →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.tickInput w (M.voteTime S.C s)) ((M.voteTime S.C s : ℕ) : Int) e =
          true → e.B.AncestorEq B.parent)
    (hOnly : ∀ w ∈ Hon, ∀ B₁ ∈ (x.tickInput w (M.voteTime S.C s)).tree, B₁.slot = s → B₁ = B)
    (hRootNew : ∀ B₁ ∈ (x.tickInput p (M.slotStart S.C s)).tree, B₁.root ≠ B.root)
    (hHs : ∀ s', s ≤ s' → s' < s'' → ∀ u ∈ Hs s', u ∈ Hon ∧ u ∈ S.P.committee s' ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s' ∧
        ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s') ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x.sent (i + 1) - x.sent i)
    (hVoters : ∀ s', s ≤ s' → s' < s'' → ∀ v ∈ Hon,
      (∀ votes support_votes : Finset (GoldfishVote V),
        CountedVotes M S.C (x.tickInput v (M.voteTime S.C (s' + 1)))
          (s' + 1) votes support_votes →
        M.voters_count votes < 2 * (Hs s').card) ∧
      M.voters_count (M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s' + 1))) s') < 2 *
        (Hs s').card)
    (hVotersQ : ∀ votes support_votes : Finset (GoldfishVote V),
      ProposalCountedVotes M (x.tickInput q (M.slotStart S.C s''))
        (s'' - 1) votes support_votes →
      M.voters_count votes < 2 * (Hs (s'' - 1)).card)
    (hHalf : (S.P.committee s).card ≤ 2 * (Hs s).card)
    (hBox : ∀ v ∈ Hon, ∀ j : ℕ, x.tickStep v (M.slotStart S.C s) ≤ j →
      j ≤ x.tickStep v (M.slotStart S.C s'') →
      BoxThree M (x.st j v) ∧ hMax M S.C (x.st j v) = h₀)
    (hFw : ∀ w ∈ Hon, (x.tickInput w (M.voteTime S.C s)).finalized.AncestorEq B.parent)
    (hFar : ∀ v ∈ Hon, (x.tickInput v (M.supportCutoff S.C (s + 1))).finalized.AncestorEq B)
    (hFafter : ∀ v ∈ Hon, ∀ j : ℕ, x.tickStep v (M.voteTime S.C s) < j →
      j ≤ x.tickStep v (M.slotStart S.C s'') →
      (x.st j v).finalized.compatible B = true)
    (hHeadP : ∃ W ∈ (x.tickInput p (M.slotStart S.C s)).tree,
      X.AncestorEq W ∧ (x.tickInput p (M.slotStart S.C s)).finalized.AncestorEq W ∧
        h₀ ≤ (M.chainStateOf S.C W).h)
    (hParentIn : B.parent ∈ M.viable_tree (M.fg_to_ac (x.tickInput p (M.slotStart S.C s)))
      (M.fg_to_ac (x.tickInput p (M.slotStart S.C s))).tree)
    (hQ : Q ⊆ Hon)
    (hQuorum : quorum V ≤ Q.card)
    (hselq : ∀ v ∈ Q, M.justifiedHeight (x.stateBefore (max (M.dutyWindowStart S.C s) GST) v) ≤
      (M.chainStateOf S.C B).h)
    (hq : q ∈ Hon)
    -- `q` is active at every step from the real time at which the attestations' sync fact is read up to its own tick
    -- to the start of slot `s''` (the sync fact's receiver row,)
    (hqWin : ∀ i : ℕ, ((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ) ≤ x.time i →
      i ≤ x.tickStep q (M.slotStart S.C s'') → q ∈ A.active i)
    -- the voters of the last slot `s'' − 1` are outside the adversary set at `q`'s tick to the start of slot `s''`,
    -- where `q`'s proposal counts their votes
    (hHonestQ : ∀ u ∈ Hs (s'' - 1), u ∉ A.corrupted (x.tickStep q (M.slotStart S.C s'')))
    (hPropose' : ∃ i : ℕ, x.lbl i = Event.tick q (M.slotStart S.C s'') ∧
      (⟨q, NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) :
    B.AncestorEq B' ∧
    ((M.chainStateOf S.C B).h + 1 ≤ (M.chainStateOf S.C B').h ∨
      ((M.chainStateOf S.C B').h = (M.chainStateOf S.C B).h ∧
        Q ⊆ (M.chainStateOf S.C B').progress ∧
        B'.slot < (M.chainStateOf S.C B).T_h.slot + S.C.δt)) ∧
    ((∀ u ∈ Q, ∀ b ∈ (x.tickInput u (M.supportCutoff S.C (s + 1))).sentAttestations,
        b.h ≠ (M.chainStateOf S.C B).h) →
      (M.chainStateOf S.C B).h + 1 ≤ (M.chainStateOf S.C B').h ∧
        ((M.chainStateOf S.C B'.parent).h = (M.chainStateOf S.C B).h →
          (M.chainStateOf S.C B').J = (M.chainStateOf S.C B).T_h)) := by
  obtain ⟨hShape, hRootW, hRootAr, hRootAfter, hHeadP', hjlt⟩ :=
    (lem80_boxThree_hypotheses M F U) S A x R E hSkew s s'' Hon X B p h₀ hHon hBox hFw hFar hFafter hp
      (le_trans (Nat.le_add_right _ _) hs'') hHeadP hPropose hParentIn
  have hHold42 := fun w (hw : w ∈ Hon) => (hold42_of_reader M F U) S A x R E GST s s'' Δs w hΔs hGST hs'' hSkew_F (hHon w hw)
  exact (lem80_round_height_advances_frame M F U Fx) S A x R GST r s s'' Hon Q Hs H X B B' p q h₀
    (fun v j => (x.st j v).finalized) E hNet hSkew hRedeliver hRoots hParent hOwner E_F hNet_F hSkew_F Sy hΔs Sy_F hΔs_F
    hs hs1 hs'' hGSTF hGST hHon hHold42 hHoldF hp tStart htStart hpR hPropose hHsPrev hHold hVotersPrev hApX hLocksW
    hOnly hRootNew hHs hVoters hVotersQ hHalf hShape hRootW hRootAr hRootAfter hHeadP' hParentIn hQ hQuorum
    (fun v hv => Or.inl (hjlt v (hQ hv))) hselq hq hqWin hHonestQ hPropose'

/-! ## `lem80wq_round_height_advances_steps` in the three boxes -/

open Classical in
/-- `lem80wq_round_height_advances_steps` in box 1. The proof; the audited statement is in
`Statements/Executions/RoundStatements.lean`.

Roots name blocks until `M.supportCutoff S.C (s'' - 1)`: the proof reads
`lem80wq_round_height_advances_steps` at the same slots, whose bound is that time.

Two lines the attestations' sync route reads:
`hGSTF`, the attestations' sync delay has elapsed after `GST` by the start of slot `s''`; and `hselq`, no member
of `Q` has justified past the height of `B`'s chain state before the later of the duty window's start of slot `s`
and `GST`.

The proposer's window `hp` starts `max (Δ S) Δs` before the support cutoff of slot `s − 1` and ends at the start
of slot `s`.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: when the proposer is in box 1 and each member in box 1 or box 3 with its greatest
chain-state height between the proposer's and the parent's height plus one, the round raises the
height or puts the progress quorum on chain. -/
theorem lem80wq_boxOne (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (GST r s s'' : ℕ) (Hon : ℕ → Finset V) (Q : Finset V) (Hs : ℕ → Finset V)
    (H : V → Block V) (X B B' : Block V) (p q : V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (hRoots : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (s'' - 1) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    -- attestations are delivered within `Δ_F S` after `GST`
    {ΔNet_F : ℕ} (E_F : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {Δs_F : ℕ} (Sy_F : SyncedWithin A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST)
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    -- `s` is the first slot of round `r`, not the first slot of all; an attestation sent at
    -- the action time of slot `s` is delivered, within `Δ_F S`, before slot `s''` starts
    (hs : s = r * S.C.R) (hs1 : 1 ≤ s)
      (hs'' : M.supportCutoff S.C (s + 1) + Δ_F S ≤ M.slotStart S.C s'')
    -- the network is synchronous from the vote time of slot `s − 1`
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C (s - 1))
    (hGSTF : GST + max (Δ_F S) Δs_F ≤ M.slotStart S.C s'')
    -- the member sets shrink from one slot to the next
    (hHonMono : ∀ s', s ≤ s' → s' + 1 < s'' → Hon (s' + 1) ⊆ Hon s')
    -- for every slot `s'` before the last: the members of slot `s'` tick to its vote time, active up to that tick from
    -- the trace's start or from their own tick to a clock value at most the duty window's start of slot `s'`
    --, each runs the update of slot `s'`, and none is in the adversary set at a step where a
    -- validator outside it ticks to the support cutoff of slot `s' + 1`
    (hHon : ∀ s', s ≤ s' → s' + 1 < s'' → ∀ v ∈ Hon s',
      v ∈ A.activeThroughoutToTick x (duty_window_start S.C s') (M.voteTime S.C s'))
    (hHonUpd : ∀ s', s ≤ s' → s' + 1 < s'' → ∀ v ∈ Hon s', v ∈ updaterAt M S A x s')
    (hHonTick : ∀ s', s ≤ s' → s' + 1 < s'' → ∀ u ∈ Hon s', u ∉ Finset.univ.filter (fun u => ∃ (k : ℕ) (w : V),
      x.lbl k = Event.tick w (M.supportCutoff S.C (s' + 1)) ∧ w ∉ A.corrupted k ∧ u ∈ A.corrupted k))
    -- the members of the last slot `s'' − 1` tick to the start of slot `s''`, active up to that tick from the trace's start
    -- or from their own tick to a clock value at most the duty window's start of that slot
    (hHonLast : ∀ v ∈ Hon (s'' - 1),
      v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s'' - 1)) (M.slotStart S.C s''))
    -- the voters of the last slot `s'' − 1` are outside the adversary set at `q`'s tick to the start of slot `s''`,
    -- where `q`'s proposal counts their votes
    (hHonestQ : ∀ u ∈ Hs (s'' - 1), u ∉ A.corrupted (x.tickStep q (M.slotStart S.C s'')))
    -- the members of the round's first slot `s` are active in every configuration in force at a real time of the sync
    -- delay after `M.supportCutoff S.C (s + 1) - max (Δ S) Δs`, where Lemma 42 reads the sync fact for their blocks
    --
    (hHold42 : ∀ w ∈ Hon s, w ∈ A.activeThroughout x ((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- the members are active through the sync delay after `M.viewFreeze S.C s - max (Δ S) Δs` (Lemma 42's holder
    -- row `hv₀`;)
    (hHoldV : ∀ w ∈ Hon s, w ∈ A.activeThroughout x ((M.viewFreeze S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.viewFreeze S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- the members of the round's first slot are active through the attestations' sync delay after the later of
    -- the duty window's start of slot `s` and `GST`, where the attestations' sync fact is read
    --
    (hHoldF : ∀ w ∈ Hon s, w ∈ A.activeThroughout x ((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ)
      (((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ) + Δs_F))
    -- the proposer is active from the recovery delay before the support cutoff of slot `s − 1`
    -- through the start of slot `s`
    -- `tStart`: a clock value more than both clock bounds before Lemma 12's read time of slot `s − 1`; the proposer
    -- ticks to the start of slot `s`, active up to that tick from the trace's start or from its own tick to a clock value
    -- at most `tStart`, and is active through the sync delay after `M.slotStart S.C s - max (Δ S) Δs` (: the
    -- amended rows of the `_frame` theorems, under)
    (tStart : ℤ) (htStart : (tStart : ℝ) + ΔClockAhead + ΔClockBehind <
      ((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ))
    (hp : p ∈ A.activeThroughoutToTick x tStart (M.slotStart S.C s))
    (hHoldP : p ∈ A.activeThroughout x ((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- `p` put `B` on the wire at its tick at the start of slot `s`
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    -- the honest voters of slot `s − 1` vote for blocks on `X`'s chain, honest at the vote time
    -- of slot `s`
    (hHsPrev : ∀ u ∈ Hs (s - 1), u ∈ S.P.committee (s - 1) ∧
      (∀ w ∈ Hon s, u ∉ A.corrupted (x.tickStep w (M.voteTime S.C s))) ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s - 1)) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u (s - 1) (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H u ∈ (x.tickInput u (M.voteTime S.C (s - 1))).tree ∧ X.AncestorEq (H u))
    -- the previous slot's voters are active through the sync delay after Lemma 12's read time of slot `s − 1`
    -- ( under)
    (hHold : ∀ u ∈ Hs (s - 1), u ∈ A.activeThroughout x ((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- at every member of `Hon s`, the voters its vote of slot `s` counts are fewer than twice
    -- `Hs (s − 1)`
    (hVotersPrev : ∀ w ∈ Hon s, ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes M S.C (x.tickInput w (M.voteTime S.C s)) s votes support_votes →
      M.voters_count votes < 2 * (Hs (s - 1)).card)
    -- `p`'s anchor is `X` or an ancestor of `X`
    (hApX :
        (M.get_anchor (x.tickInput p (M.slotStart S.C s))
            ((M.slotStart S.C s : ℕ) : Int)).AncestorEq X)
    -- every live lock a member's revocation of slot `s` leaves is on `B`'s parent's chain
    (hLocksW : ∀ w ∈ Hon s, ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C s))
        ((M.voteTime S.C s : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C s)) s →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.tickInput w (M.voteTime S.C s)) ((M.voteTime S.C s : ℕ) : Int) e =
          true → e.B.AncestorEq B.parent)
    -- `B` is the only slot-`s` block a member holds at the vote time; its root is new to `p`
    (hOnly : ∀ w ∈ Hon s, ∀ B₁ ∈ (x.tickInput w (M.voteTime S.C s)).tree, B₁.slot = s → B₁ = B)
    (hRootNew : ∀ B₁ ∈ (x.tickInput p (M.slotStart S.C s)).tree, B₁.root ≠ B.root)
    -- the honest voters of slot `s'` are members of `Hon s'` and of the slot's committee
    (hHs : ∀ s', s ≤ s' → s' < s'' → ∀ u ∈ Hs s', u ∈ Hon s' ∧ u ∈ S.P.committee s' ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s' ∧
        ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s') ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x.sent (i + 1) - x.sent i)
    -- the counts of slot `s'`, read at the members of `Hon s'`: the voters counted by a vote of
    -- slot `s' + 1` and the slot-`s'` voters of the pool at its tick to the support cutoff of slot
    -- `s' + 1` are fewer than twice `Hs s'`
    (hVoters : ∀ s', s ≤ s' → s' < s'' → ∀ v ∈ Hon s',
      (∀ votes support_votes : Finset (GoldfishVote V),
        CountedVotes M S.C (x.tickInput v (M.voteTime S.C (s' + 1)))
          (s' + 1) votes support_votes →
        M.voters_count votes < 2 * (Hs s').card) ∧
      M.voters_count (M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s' + 1))) s') < 2 *
        (Hs s').card)
    -- the slot-`(s'' − 1)` voters `q`'s proposal counts are fewer than twice `Hs (s'' − 1)`
    (hVotersQ : ∀ votes support_votes : Finset (GoldfishVote V),
      ProposalCountedVotes M (x.tickInput q (M.slotStart S.C s''))
        (s'' - 1) votes support_votes →
      M.voters_count votes < 2 * (Hs (s'' - 1)).card)
    -- the slot-`s` committee is at most twice `Hs s`
    (hHalf : (S.P.committee s).card ≤ 2 * (Hs s).card)
    -- `p` is in box 1 before the start of slot `s`
    (hBoxP : BoxOne M S.C (x.tickInput p (M.slotStart S.C s)))
    -- before the vote time of slot `s`, every member of `Hon s` is in box 1 with greatest
    -- chain-state height at least `p`'s and at most `h(B.parent) + 1`, or in box 3 with greatest
    -- chain-state height at least `p`'s minus one and at most `h(B.parent)`
    (hBoxW : ∀ w ∈ Hon s,
      (BoxOne M S.C (x.tickInput w (M.voteTime S.C s)) ∧ hMax M S.C
          (x.tickInput p (M.slotStart S.C s)) ≤ hMax M S.C
            (x.tickInput w (M.voteTime S.C s)) ∧
        hMax M S.C (x.tickInput w (M.voteTime S.C s)) ≤ (M.chainStateOf S.C B.parent).h + 1) ∨
      (BoxThree M (x.tickInput w (M.voteTime S.C s)) ∧ hMax M S.C
          (x.tickInput p (M.slotStart S.C s)) ≤ hMax M S.C
            (x.tickInput w (M.voteTime S.C s)) + 1 ∧
        hMax M S.C (x.tickInput w (M.voteTime S.C s)) ≤ (M.chainStateOf S.C B.parent).h))
    -- before the action time, every member of `Hon s` is in box 1 with greatest chain-state height
    -- at most `h(B) + 1`, or in box 3 with greatest chain-state height at most `h(B)`
    (hBoxV : ∀ v ∈ Hon s,
      (BoxOne M S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) ∧ hMax M S.C
          (x.tickInput v (M.supportCutoff S.C (s + 1))) ≤ (M.chainStateOf S.C B).h + 1) ∨
      (BoxThree M (x.tickInput v (M.supportCutoff S.C (s + 1))) ∧ hMax M S.C
          (x.tickInput v (M.supportCutoff S.C (s + 1))) ≤ (M.chainStateOf S.C B).h))
    -- the finalized blocks: on `B`'s parent's chain at the vote time of slot `s`, on `B`'s chain
    -- at the action time
    (hFw : ∀ w ∈ Hon s, (x.tickInput w (M.voteTime S.C s)).finalized.AncestorEq B.parent)
    (hFar : ∀ v ∈ Hon s, (x.tickInput v (M.supportCutoff S.C (s + 1))).finalized.AncestorEq B)
    -- some block of `p`'s tree, on `X`'s and `p`'s finalized block's chains, reaches `p`'s
    -- greatest chain-state height minus one
    (hHeadP : ∃ W ∈ (x.tickInput p (M.slotStart S.C s)).tree,
      X.AncestorEq W ∧ (x.tickInput p (M.slotStart S.C s)).finalized.AncestorEq W ∧ hMax M S.C
        (x.tickInput p (M.slotStart S.C s)) - 1 ≤ (M.chainStateOf S.C W).h)
    -- after the action time, at the members of the next slot: `StepFrameAt` relative to `B` for
    -- every slot `s'` with `s' + 3 ≤ s''`; for the last slot `s'' − 1`, the voter's fork choice
    -- before its vote time (the first two conjuncts of `StepFrameAt S Sched x B (s'' − 2) w`)
    (hStep : ∀ s', s ≤ s' → s' + 3 ≤ s'' → ∀ w ∈ Hon (s' + 1), StepFrameAt M S A x B s' w)
    (hStepLast : ∀ w ∈ Hon (s'' - 1),
      (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s'' - 1)))).fc_root.compatible B = true ∧
      ((M.fg_to_ac (x.tickInput w (M.voteTime S.C (s'' - 1)))).fc_root.AncestorEq B →
        ∃ W, VoterTreeAt M (x.tickInput w (M.voteTime S.C (s'' - 1)))
          (S.C.t_ ((s'' - 1) - 1) + 3 * S.C.Δ) (s'' - 1) W ∧ W ∈
            (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s'' - 1)))).viable_heads ∧
            B.AncestorEq W))
    -- the quorum attests at `a`, inside slot `s`'s active window
    (hQ : Q ⊆ Hon s) (hQuorum : quorum V ≤ Q.card)
    (hselq : ∀ v ∈ Q, M.justifiedHeight (x.stateBefore (max (M.dutyWindowStart S.C s) GST) v) ≤
      (M.chainStateOf S.C B).h)
    -- the next proposer is a member of the last slot's set
    (hq : q ∈ Hon (s'' - 1))
    -- `q` is active at every step from the real time at which the attestations' sync fact is read up to its own tick
    -- to the start of slot `s''` (the sync fact's receiver row,)
    (hqWin : ∀ i : ℕ, ((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ) ≤ x.time i →
      i ≤ x.tickStep q (M.slotStart S.C s'') → q ∈ A.active i)
    -- `q`'s fork-choice root before the start of slot `s''` is compatible with `B`, and when it
    -- is `B` or an ancestor of `B`, a block of `q`'s frame tree that is `B` or a descendant of `B`
    -- is a viable head
    (hFrameQ : (M.fg_to_ac (x.tickInput q (M.slotStart S.C s''))).fc_root.compatible B = true ∧
      ((M.fg_to_ac (x.tickInput q (M.slotStart S.C s''))).fc_root.AncestorEq B →
        ∃ W ∈ (M.fg_to_ac (x.tickInput q (M.slotStart S.C s''))).tree,
          W ∈ (M.fg_to_ac (x.tickInput q (M.slotStart S.C s''))).viable_heads ∧ B.AncestorEq W))
    -- `q` put `B'` on the wire at its tick at the start of slot `s''`
    (hPropose' : ∃ i : ℕ, x.lbl i = Event.tick q (M.slotStart S.C s'') ∧
      (⟨q, NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) :
    B.AncestorEq B' ∧
    ((M.chainStateOf S.C B).h + 1 ≤ (M.chainStateOf S.C B').h ∨
      ((M.chainStateOf S.C B').h = (M.chainStateOf S.C B).h ∧
        Q ⊆ (M.chainStateOf S.C B').progress ∧
        B'.slot < (M.chainStateOf S.C B).T_h.slot + S.C.δt)) ∧
    ((∀ u ∈ Q, ∀ b ∈ (x.tickInput u (M.supportCutoff S.C (s + 1))).sentAttestations,
        b.h ≠ (M.chainStateOf S.C B).h) →
      (M.chainStateOf S.C B).h + 1 ≤ (M.chainStateOf S.C B').h ∧
        ((M.chainStateOf S.C B'.parent).h = (M.chainStateOf S.C B).h →
          (M.chainStateOf S.C B').J = (M.chainStateOf S.C B).T_h)) := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hs2 := (GoldilocksCorrectness.Record.Proofs.Routines.slot_add_two_le_of_delivery M.toSlotLayout F.sched) S hs''
  obtain ⟨hvA, -, -, hsA, -, hk8, hΔ⟩ := (slot_times M F U) S s
  obtain ⟨-, hcB, -, -, -, -, -⟩ := (slot_times M F U) S (s + 1)
  have hss := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s
  have hdw := duty_window_start_real S (s + 1)
  push_cast at hdw
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hk8R : (8 : ℝ) * Δ S ≤ 4 * Δ S * S.C.k := by exact_mod_cast hk8
  have hvR : ((M.voteTime S.C s : ℕ) : ℝ) = 4 * Δ S * s + Δ S := by rw [hvA, hss]; push_cast; ring
  have hcR : ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) = 4 * Δ S * s + 6 * Δ S := by
    rw [hcB, hsA, hss]; push_cast; ring
  -- the states the ticks read satisfy the node invariant (Lemma 11 at the tick's step, whose validator is
  -- outside the adversary set)
  have hInvAt : ∀ (v : V) (t i : ℕ), x.lbl i = Event.tick v t → M.nodeInv S.C S.P S.X (x.tickInput v t) :=
    fun v t i hl => by
      rw [show x.tickInput v t = x.st i v by
        unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hl]]
      exact (lem11_node_invariant M F S A x R E i v (E.not_mem_corrupted_of_tick hl)).1
  have hInvP : M.nodeInv S.C S.P S.X (x.tickInput p (M.slotStart S.C s)) := by
    obtain ⟨i, hl, -⟩ := hPropose
    exact hInvAt p _ i hl
  -- each member ticks to the vote time of slot `s` inside its reader of slot `s`'s update
  have hInvW : ∀ w ∈ Hon s, M.nodeInv S.C S.P S.X (x.tickInput w (M.voteTime S.C s)) := by
    intro w hw
    have hr := (mem_activeThroughoutToTick_of_inside M F) R E (hHonUpd s le_rfl (by omega) w hw)
      (c := M.voteTime S.C s) (by omega) (by rw [hdw, hvR]; linarith) (by rw [hvR, hcR]; linarith)
    obtain ⟨k, hk, -⟩ := Activity.mem_activeThroughoutToTick.1 hr
    exact hInvAt w _ k hk
  have hInvV : ∀ v ∈ Hon s, M.nodeInv S.C S.P S.X (x.tickInput v (M.supportCutoff S.C (s + 1))) := by
    intro v hv
    obtain ⟨k, hk, -⟩ := Activity.mem_activeThroughoutToTick.1 (hHonUpd s le_rfl (by omega) v hv)
    exact hInvAt v _ k hk
  have hpS := (GoldilocksCorrectness.Record.Proofs.Routines.frameShape_of_boxOne M F) S.C S.P S.X _ hInvP hBoxP
  -- the members' frames: the root is the finalized block, the `head_height_floor` is between the proposer's and
  -- the parent's height at the tick to the vote time, at most `h(B)` at the tick to the support cutoff
  have hW : ∀ w ∈ Hon s, M.get_fc_root (x.tickInput w (M.voteTime S.C s)) =
        (x.tickInput w (M.voteTime S.C s)).finalized ∧
      M.head_height_floor (x.tickInput p (M.slotStart S.C s)) ≤
        M.head_height_floor (x.tickInput w (M.voteTime S.C s)) ∧
      M.head_height_floor (x.tickInput w (M.voteTime S.C s)) ≤ (M.chainStateOf S.C B.parent).h ∧
      (x.tickInput w (M.voteTime S.C s)).justifiedHeight < (M.chainStateOf S.C B.parent).h := by
    intro w hw
    rw [hpS.2.2]
    refine (GoldilocksCorrectness.Record.Proofs.Routines.floor_of_boxOne_or_boxThree M F) S.C S.P S.X _
      (hInvW w hw) _ _ ?_
    rcases hBoxW w hw with ⟨hb, h1, h2⟩ | ⟨hb, h1, h2⟩
    · exact Or.inl ⟨hb, by unfold Height at *; omega, h2⟩
    · exact Or.inr ⟨hb, by unfold Height at *; omega, h2⟩
  have hV : ∀ v ∈ Hon s, M.get_fc_root (x.tickInput v (M.supportCutoff S.C (s + 1))) =
        (x.tickInput v (M.supportCutoff S.C (s + 1))).finalized ∧
      0 ≤ M.head_height_floor (x.tickInput v (M.supportCutoff S.C (s + 1))) ∧
      M.head_height_floor (x.tickInput v (M.supportCutoff S.C (s + 1))) ≤ (M.chainStateOf S.C B).h ∧
      (x.tickInput v (M.supportCutoff S.C (s + 1))).justifiedHeight < (M.chainStateOf S.C B).h := by
    intro v hv
    refine (GoldilocksCorrectness.Record.Proofs.Routines.floor_of_boxOne_or_boxThree M F) S.C S.P S.X _
      (hInvV v hv) _ _ ?_
    rcases hBoxV v hv with ⟨hb, h2⟩ | ⟨hb, h2⟩
    · exact Or.inl ⟨hb, Nat.zero_le _, h2⟩
    · exact Or.inr ⟨hb, Nat.zero_le _, h2⟩
  exact (lem80wq_round_height_advances_steps M F U Fx) S A x R GST r s s'' Hon Q Hs H X B B' p q
    (M.head_height_floor (x.tickInput p (M.slotStart S.C s)))
    (fun w => M.head_height_floor (x.tickInput w (M.voteTime S.C s)))
    (fun v => M.head_height_floor (x.tickInput v (M.supportCutoff S.C (s + 1))))
    (M.get_fc_root (x.tickInput p (M.slotStart S.C s)))
    (fun w => M.get_fc_root (x.tickInput w (M.voteTime S.C s)))
    (fun v => M.get_fc_root (x.tickInput v (M.supportCutoff S.C (s + 1))))
    E hNet hSkew hRedeliver hRoots hParent hOwner E_F hNet_F hSkew_F Sy hΔs Sy_F hΔs_F hs hs1 hs'' hGST hGSTF
    hHonMono hHon hHonUpd hHonTick hHonLast hHonestQ hHold42 hHoldV hHoldF tStart htStart hp hHoldP hPropose hHsPrev hHold
    hVotersPrev hApX hLocksW hOnly hRootNew hHs hVoters hVotersQ hHalf
    ⟨rfl, rfl⟩ (fun _ _ => ⟨rfl, rfl⟩) (fun _ _ => ⟨rfl, rfl⟩)
    (fun w hw => ⟨(hW w hw).2.1, (hW w hw).2.2.1⟩) (fun v hv => (hV v hv).2.2.1)
    (fun w hw => by rw [(hW w hw).1]; exact hFw w hw)
    (fun v hv => by rw [(hV v hv).1]; exact hFar v hv)
    (by rw [hpS.2.1, hpS.2.2]; exact hHeadP) hStep hStepLast hQ hQuorum
    (fun v hv => Or.inl (hV v (hQ hv)).2.2.2) hselq hq hqWin hFrameQ hPropose'

open Classical in
/-- `lem80wq_round_height_advances_steps` in box 2. The proof; the audited statement is in
`Statements/Executions/RoundStatements.lean`.

Roots name blocks until `M.supportCutoff S.C (s'' - 1)`: the proof reads
`lem80wq_round_height_advances_steps` at the same slots, whose bound is that time.

Two lines the attestations' sync route reads:
`hGSTF`, the attestations' sync delay has elapsed after `GST` by the start of slot `s''`; and `hselq`, no member
of `Q` has justified past the height of `B`'s chain state before the later of the duty window's start of slot `s`
and `GST`.

The proposer's window `hp` starts `max (Δ S) Δs` before the support cutoff of slot `s − 1` and ends at the start
of slot `s`.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: when the proposer and every member are in box 2 with one justified block, the round
raises the height or puts the progress quorum on chain. -/
theorem lem80wq_boxTwo (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (GST r s s'' : ℕ) (Hon : ℕ → Finset V) (Q : Finset V) (Hs : ℕ → Finset V)
    (H : V → Block V) (X B B' J₀ : Block V) (p q : V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (hRoots : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (s'' - 1) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    -- attestations are delivered within `Δ_F S` after `GST`
    {ΔNet_F : ℕ} (E_F : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {Δs_F : ℕ} (Sy_F : SyncedWithin A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST)
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    -- `s` is the first slot of round `r`, not the first slot of all; an attestation sent at
    -- the action time of slot `s` is delivered, within `Δ_F S`, before slot `s''` starts
    (hs : s = r * S.C.R) (hs1 : 1 ≤ s)
      (hs'' : M.supportCutoff S.C (s + 1) + Δ_F S ≤ M.slotStart S.C s'')
    -- the network is synchronous from the vote time of slot `s − 1`
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C (s - 1))
    (hGSTF : GST + max (Δ_F S) Δs_F ≤ M.slotStart S.C s'')
    -- the member sets shrink from one slot to the next
    (hHonMono : ∀ s', s ≤ s' → s' + 1 < s'' → Hon (s' + 1) ⊆ Hon s')
    -- for every slot `s'` before the last: the members of slot `s'` tick to its vote time, active up to that tick from
    -- the trace's start or from their own tick to a clock value at most the duty window's start of slot `s'`
    --, each runs the update of slot `s'`, and none is in the adversary set at a step where a
    -- validator outside it ticks to the support cutoff of slot `s' + 1`
    (hHon : ∀ s', s ≤ s' → s' + 1 < s'' → ∀ v ∈ Hon s',
      v ∈ A.activeThroughoutToTick x (duty_window_start S.C s') (M.voteTime S.C s'))
    (hHonUpd : ∀ s', s ≤ s' → s' + 1 < s'' → ∀ v ∈ Hon s', v ∈ updaterAt M S A x s')
    (hHonTick : ∀ s', s ≤ s' → s' + 1 < s'' → ∀ u ∈ Hon s', u ∉ Finset.univ.filter (fun u => ∃ (k : ℕ) (w : V),
      x.lbl k = Event.tick w (M.supportCutoff S.C (s' + 1)) ∧ w ∉ A.corrupted k ∧ u ∈ A.corrupted k))
    -- the members of the last slot `s'' − 1` tick to the start of slot `s''`, active up to that tick from the trace's start
    -- or from their own tick to a clock value at most the duty window's start of that slot
    (hHonLast : ∀ v ∈ Hon (s'' - 1),
      v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s'' - 1)) (M.slotStart S.C s''))
    -- the voters of the last slot `s'' − 1` are outside the adversary set at `q`'s tick to the start of slot `s''`,
    -- where `q`'s proposal counts their votes
    (hHonestQ : ∀ u ∈ Hs (s'' - 1), u ∉ A.corrupted (x.tickStep q (M.slotStart S.C s'')))
    -- the members of the round's first slot `s` are active in every configuration in force at a real time of the sync
    -- delay after `M.supportCutoff S.C (s + 1) - max (Δ S) Δs`, where Lemma 42 reads the sync fact for their blocks
    --
    (hHold42 : ∀ w ∈ Hon s, w ∈ A.activeThroughout x ((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- the members are active through the sync delay after `M.viewFreeze S.C s - max (Δ S) Δs` (Lemma 42's holder
    -- row `hv₀`;)
    (hHoldV : ∀ w ∈ Hon s, w ∈ A.activeThroughout x ((M.viewFreeze S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.viewFreeze S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- the members of the round's first slot are active through the attestations' sync delay after the later of
    -- the duty window's start of slot `s` and `GST`, where the attestations' sync fact is read
    --
    (hHoldF : ∀ w ∈ Hon s, w ∈ A.activeThroughout x ((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ)
      (((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ) + Δs_F))
    -- the proposer is active from the recovery delay before the support cutoff of slot `s − 1`
    -- through the start of slot `s`
    -- `tStart`: a clock value more than both clock bounds before Lemma 12's read time of slot `s − 1`; the proposer
    -- ticks to the start of slot `s`, active up to that tick from the trace's start or from its own tick to a clock value
    -- at most `tStart`, and is active through the sync delay after `M.slotStart S.C s - max (Δ S) Δs` (: the
    -- amended rows of the `_frame` theorems, under)
    (tStart : ℤ) (htStart : (tStart : ℝ) + ΔClockAhead + ΔClockBehind <
      ((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ))
    (hp : p ∈ A.activeThroughoutToTick x tStart (M.slotStart S.C s))
    (hHoldP : p ∈ A.activeThroughout x ((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- `p` put `B` on the wire at its tick at the start of slot `s`
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    -- the honest voters of slot `s − 1` vote for blocks on `X`'s chain, honest at the vote time
    -- of slot `s`
    (hHsPrev : ∀ u ∈ Hs (s - 1), u ∈ S.P.committee (s - 1) ∧
      (∀ w ∈ Hon s, u ∉ A.corrupted (x.tickStep w (M.voteTime S.C s))) ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s - 1)) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u (s - 1) (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H u ∈ (x.tickInput u (M.voteTime S.C (s - 1))).tree ∧ X.AncestorEq (H u))
    -- the previous slot's voters are active through the sync delay after Lemma 12's read time of slot `s − 1`
    -- ( under)
    (hHold : ∀ u ∈ Hs (s - 1), u ∈ A.activeThroughout x ((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- at every member of `Hon s`, the voters its vote of slot `s` counts are fewer than twice
    -- `Hs (s − 1)`
    (hVotersPrev : ∀ w ∈ Hon s, ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes M S.C (x.tickInput w (M.voteTime S.C s)) s votes support_votes →
      M.voters_count votes < 2 * (Hs (s - 1)).card)
    -- `p`'s anchor is `X` or an ancestor of `X`
    (hApX :
        (M.get_anchor (x.tickInput p (M.slotStart S.C s))
            ((M.slotStart S.C s : ℕ) : Int)).AncestorEq X)
    -- every live lock a member's revocation of slot `s` leaves is on `B`'s parent's chain
    (hLocksW : ∀ w ∈ Hon s, ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C s))
        ((M.voteTime S.C s : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C s)) s →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.tickInput w (M.voteTime S.C s)) ((M.voteTime S.C s : ℕ) : Int) e =
          true → e.B.AncestorEq B.parent)
    -- `B` is the only slot-`s` block a member holds at the vote time; its root is new to `p`
    (hOnly : ∀ w ∈ Hon s, ∀ B₁ ∈ (x.tickInput w (M.voteTime S.C s)).tree, B₁.slot = s → B₁ = B)
    (hRootNew : ∀ B₁ ∈ (x.tickInput p (M.slotStart S.C s)).tree, B₁.root ≠ B.root)
    -- the honest voters of slot `s'` are members of `Hon s'` and of the slot's committee
    (hHs : ∀ s', s ≤ s' → s' < s'' → ∀ u ∈ Hs s', u ∈ Hon s' ∧ u ∈ S.P.committee s' ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s' ∧
        ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s') ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x.sent (i + 1) - x.sent i)
    -- the counts of slot `s'`, read at the members of `Hon s'`: the voters counted by a vote of
    -- slot `s' + 1` and the slot-`s'` voters of the pool at its tick to the support cutoff of slot
    -- `s' + 1` are fewer than twice `Hs s'`
    (hVoters : ∀ s', s ≤ s' → s' < s'' → ∀ v ∈ Hon s',
      (∀ votes support_votes : Finset (GoldfishVote V),
        CountedVotes M S.C (x.tickInput v (M.voteTime S.C (s' + 1)))
          (s' + 1) votes support_votes →
        M.voters_count votes < 2 * (Hs s').card) ∧
      M.voters_count (M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s' + 1))) s') < 2 *
        (Hs s').card)
    -- the slot-`(s'' − 1)` voters `q`'s proposal counts are fewer than twice `Hs (s'' − 1)`
    (hVotersQ : ∀ votes support_votes : Finset (GoldfishVote V),
      ProposalCountedVotes M (x.tickInput q (M.slotStart S.C s''))
        (s'' - 1) votes support_votes →
      M.voters_count votes < 2 * (Hs (s'' - 1)).card)
    -- the slot-`s` committee is at most twice `Hs s`
    (hHalf : (S.P.committee s).card ≤ 2 * (Hs s).card)
    -- `J₀` is not the genesis block; `p` is in box 2 with `J₀` before the start of slot `s`, and
    -- every member of `Hon s` is too before the vote time of slot `s` and before the action time
    (hJ₀ : J₀ ≠ Block.genesis)
    (hBoxP : BoxTwo M S.C (x.tickInput p (M.slotStart S.C s)) J₀)
    (hBoxW : ∀ w ∈ Hon s, BoxTwo M S.C (x.tickInput w (M.voteTime S.C s)) J₀)
    (hBoxV : ∀ v ∈ Hon s, BoxTwo M S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) J₀)
    -- some block of `p`'s tree, on `X`'s and `J₀`'s chains, reaches `p`'s greatest chain-state
    -- height minus one; and `B`'s parent is in `p`'s viable tree
    (hHeadP : ∃ W ∈ (x.tickInput p (M.slotStart S.C s)).tree,
      X.AncestorEq W ∧ J₀.AncestorEq W ∧ hMax M S.C (x.tickInput p (M.slotStart S.C s)) - 1 ≤
        (M.chainStateOf S.C W).h)
    (hParentIn : B.parent ∈ M.viable_tree (M.fg_to_ac (x.tickInput p (M.slotStart S.C s)))
      (M.fg_to_ac (x.tickInput p (M.slotStart S.C s))).tree)
    -- unforgeability, and fewer than a third of the validators corrupted up to the real time of each member's own tick
    -- to the support cutoff of slot `s + 1` (rule R3;)
    (hAdv : ∀ v ∈ Hon s, A.AdversaryFewerThanThirdUntil x (validator_count V)
        (x.time (x.tickStep v (M.supportCutoff S.C (s + 1)))))
    -- after the action time, at the members of the next slot: `StepFrameAt` relative to `B` for
    -- every slot `s'` with `s' + 3 ≤ s''`; for the last slot `s'' − 1`, the voter's fork choice
    -- before its vote time (the first two conjuncts of `StepFrameAt S Sched x B (s'' − 2) w`)
    (hStep : ∀ s', s ≤ s' → s' + 3 ≤ s'' → ∀ w ∈ Hon (s' + 1), StepFrameAt M S A x B s' w)
    (hStepLast : ∀ w ∈ Hon (s'' - 1),
      (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s'' - 1)))).fc_root.compatible B = true ∧
      ((M.fg_to_ac (x.tickInput w (M.voteTime S.C (s'' - 1)))).fc_root.AncestorEq B →
        ∃ W, VoterTreeAt M (x.tickInput w (M.voteTime S.C (s'' - 1)))
          (S.C.t_ ((s'' - 1) - 1) + 3 * S.C.Δ) (s'' - 1) W ∧ W ∈
            (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s'' - 1)))).viable_heads ∧
            B.AncestorEq W))
    -- the quorum attests at `a`, inside slot `s`'s active window
    (hQ : Q ⊆ Hon s) (hQuorum : quorum V ≤ Q.card)
    (hselq : ∀ v ∈ Q, M.justifiedHeight (x.stateBefore (max (M.dutyWindowStart S.C s) GST) v) ≤
      (M.chainStateOf S.C B).h)
    -- the next proposer is a member of the last slot's set
    (hq : q ∈ Hon (s'' - 1))
    -- `q` is active at every step from the real time at which the attestations' sync fact is read up to its own tick
    -- to the start of slot `s''` (the sync fact's receiver row,)
    (hqWin : ∀ i : ℕ, ((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ) ≤ x.time i →
      i ≤ x.tickStep q (M.slotStart S.C s'') → q ∈ A.active i)
    -- `q`'s fork-choice root before the start of slot `s''` is compatible with `B`, and when it
    -- is `B` or an ancestor of `B`, a block of `q`'s frame tree that is `B` or a descendant of `B`
    -- is a viable head
    (hFrameQ : (M.fg_to_ac (x.tickInput q (M.slotStart S.C s''))).fc_root.compatible B = true ∧
      ((M.fg_to_ac (x.tickInput q (M.slotStart S.C s''))).fc_root.AncestorEq B →
        ∃ W ∈ (M.fg_to_ac (x.tickInput q (M.slotStart S.C s''))).tree,
          W ∈ (M.fg_to_ac (x.tickInput q (M.slotStart S.C s''))).viable_heads ∧ B.AncestorEq W))
    -- `q` put `B'` on the wire at its tick at the start of slot `s''`
    (hPropose' : ∃ i : ℕ, x.lbl i = Event.tick q (M.slotStart S.C s'') ∧
      (⟨q, NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) :
    B.AncestorEq B' ∧
    ((M.chainStateOf S.C B).h + 1 ≤ (M.chainStateOf S.C B').h ∨
      ((M.chainStateOf S.C B').h = (M.chainStateOf S.C B).h ∧
        Q ⊆ (M.chainStateOf S.C B').progress ∧
        B'.slot < (M.chainStateOf S.C B).T_h.slot + S.C.δt)) ∧
    ((∀ u ∈ Q, ∀ b ∈ (x.tickInput u (M.supportCutoff S.C (s + 1))).sentAttestations,
        b.h ≠ (M.chainStateOf S.C B).h) →
      (M.chainStateOf S.C B).h + 1 ≤ (M.chainStateOf S.C B').h ∧
        ((M.chainStateOf S.C B'.parent).h = (M.chainStateOf S.C B).h →
          (M.chainStateOf S.C B').J = (M.chainStateOf S.C B).T_h)) := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hs2 := (GoldilocksCorrectness.Record.Proofs.Routines.slot_add_two_le_of_delivery M.toSlotLayout F.sched) S hs''
  obtain ⟨hvA, -, -, hsA, -, hk8, hΔ⟩ := (slot_times M F U) S s
  obtain ⟨-, hcB, -, -, -, -, -⟩ := (slot_times M F U) S (s + 1)
  have hss := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s
  have hdw := duty_window_start_real S (s + 1)
  push_cast at hdw
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hk8R : (8 : ℝ) * Δ S ≤ 4 * Δ S * S.C.k := by exact_mod_cast hk8
  have hvR : ((M.voteTime S.C s : ℕ) : ℝ) = 4 * Δ S * s + Δ S := by rw [hvA, hss]; push_cast; ring
  have hcR : ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) = 4 * Δ S * s + 6 * Δ S := by
    rw [hcB, hsA, hss]; push_cast; ring
  -- the states the ticks read satisfy the node invariant (Lemma 11 at the tick's step, whose validator is
  -- outside the adversary set)
  have hInvAt : ∀ (v : V) (t i : ℕ), x.lbl i = Event.tick v t → M.nodeInv S.C S.P S.X (x.tickInput v t) :=
    fun v t i hl => by
      rw [show x.tickInput v t = x.st i v by
        unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hl]]
      exact (lem11_node_invariant M F S A x R E i v (E.not_mem_corrupted_of_tick hl)).1
  have hInvP : M.nodeInv S.C S.P S.X (x.tickInput p (M.slotStart S.C s)) := by
    obtain ⟨i, hl, -⟩ := hPropose
    exact hInvAt p _ i hl
  -- each member ticks to the vote time of slot `s` inside its reader of slot `s`'s update
  have hInvW : ∀ w ∈ Hon s, M.nodeInv S.C S.P S.X (x.tickInput w (M.voteTime S.C s)) := by
    intro w hw
    have hr := (mem_activeThroughoutToTick_of_inside M F) R E (hHonUpd s le_rfl (by omega) w hw)
      (c := M.voteTime S.C s) (by omega) (by rw [hdw, hvR]; linarith) (by rw [hvR, hcR]; linarith)
    obtain ⟨k, hk, -⟩ := Activity.mem_activeThroughoutToTick.1 hr
    exact hInvAt w _ k hk
  have hInvV : ∀ v ∈ Hon s, M.nodeInv S.C S.P S.X (x.tickInput v (M.supportCutoff S.C (s + 1))) := by
    intro v hv
    obtain ⟨k, hk, -⟩ := Activity.mem_activeThroughoutToTick.1 (hHonUpd s le_rfl (by omega) v hv)
    exact hInvAt v _ k hk
  -- in box 2 the root is `J₀` and `head_height_floor` is `J₀`'s height: `h_max − 1 = h_j` (Lemma 57)
  have hfl : ∀ (v : V) (t : ℕ), M.nodeInv S.C S.P S.X (x.tickInput v t) → BoxTwo M S.C (x.tickInput v t) J₀ →
      M.get_fc_root (x.tickInput v t) = J₀ ∧
      M.head_height_floor (x.tickInput v t) = (M.chainStateOf S.C J₀).h := by
    intro v t hI hb
    have h := (GoldilocksCorrectness.Record.Statements.Routines.frameShape_of_boxTwo M F) S.C S.P S.X _ hI _ hb
    refine ⟨h.1, ?_⟩
    rw [h.2, hb.1, Nat.add_sub_cancel]
    exact (h_j_eq_of_boxTwo_st M F) S A x R E _ v J₀ hb hJ₀
  have hP := (GoldilocksCorrectness.Record.Statements.Routines.frameShape_of_boxTwo M F) S.C S.P S.X _ hInvP _ hBoxP
  have hfP := (hfl p _ hInvP hBoxP).2
  -- `J₀` is an ancestor of `B`'s parent, which is in `p`'s viable tree; `head_height_floor` is at most the
  -- parent's height
  obtain ⟨-, hPB, -⟩ := (proposal_facts_at M F U) S A x R E s B p hPropose hParentIn
  have hJP : J₀.AncestorEq B.parent := by
    have hR : (M.fg_to_ac (x.tickInput p (M.slotStart S.C s))).fc_root = J₀ :=
      ((GoldilocksCorrectness.Record.Statements.Routines.lem56_frame_of_shape M F) S.C S.P S.X _ hInvP _ _ hP).1
    have hPin := hParentIn
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_tree_iff M F)] at hPin
    obtain ⟨-, hRB, -⟩ := hPin
    rw [hR] at hRB
    exact hRB
  have hJB := ancestorEq_trans hJP hPB
  have hφ : (M.chainStateOf S.C J₀).h ≤ (M.chainStateOf S.C B.parent).h :=
    (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_height_mono M F) S.C hJP
  have hPBh := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C B.parent B).2.2.2.1 hPB
  refine (lem80wq_round_height_advances_steps M F U Fx) S A x R GST r s s'' Hon Q Hs H X B B' p q
    (M.head_height_floor (x.tickInput p (M.slotStart S.C s)))
    (fun w => M.head_height_floor (x.tickInput w (M.voteTime S.C s)))
    (fun v => M.head_height_floor (x.tickInput v (M.supportCutoff S.C (s + 1))))
    (M.get_fc_root (x.tickInput p (M.slotStart S.C s)))
    (fun w => M.get_fc_root (x.tickInput w (M.voteTime S.C s)))
    (fun v => M.get_fc_root (x.tickInput v (M.supportCutoff S.C (s + 1))))
    E hNet hSkew hRedeliver hRoots hParent ((votesCastByOwner_of_unforgeability M F) S A x R E) E_F hNet_F hSkew_F
    Sy hΔs Sy_F hΔs_F hs hs1 hs'' hGST hGSTF
    hHonMono hHon hHonUpd hHonTick hHonLast hHonestQ hHold42 hHoldV hHoldF tStart htStart hp hHoldP hPropose hHsPrev hHold
    hVotersPrev hApX hLocksW hOnly hRootNew hHs hVoters hVotersQ hHalf
    ⟨rfl, rfl⟩ (fun _ _ => ⟨rfl, rfl⟩) (fun _ _ => ⟨rfl, rfl⟩)
    (fun w hw => by rw [(hfl w _ (hInvW w hw) (hBoxW w hw)).2, hfP]; exact ⟨le_rfl, hφ⟩)
    (fun v hv => by rw [(hfl v _ (hInvV v hv) (hBoxV v hv)).2]; exact le_trans hφ hPBh)
    (fun w hw => by rw [(hfl w _ (hInvW w hw) (hBoxW w hw)).1]; exact hJP)
    (fun v hv => by rw [(hfl v _ (hInvV v hv) (hBoxV v hv)).1]; exact hJB)
    (by rw [hP.1, hP.2]; exact hHeadP) hStep hStepLast hQ hQuorum (fun v hvQ => ?_) hselq hq hqWin hFrameQ hPropose'
  -- the record: `h_j = h(J₀)`; at `H` the greatest chain-state height minus one the lock, when set, is on `J₀` (one
  -- justification per height, read at `v`'s tick to the support cutoff of slot `s + 1` under the adversary bound up to
  -- that tick,), which is `B`'s `T_h`
  have hvs := hQ hvQ
  have hBv := hBoxV v hvs
  have hjv : (x.tickInput v (M.supportCutoff S.C (s + 1))).justifiedHeight = (M.chainStateOf S.C J₀).h :=
    (h_j_eq_of_boxTwo_st M F) S A x R E _ v J₀ hBv hJ₀
  by_cases hlt : (x.tickInput v (M.supportCutoff S.C (s + 1))).justifiedHeight < (M.chainStateOf S.C B).h
  · exact Or.inl hlt
  · have hH : (M.chainStateOf S.C B).h = hMax M S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) - 1 := by
      rw [hBv.1, Nat.add_sub_cancel]
      have := le_trans hφ hPBh
      unfold Height at *
      omega
    right
    cases hl : (x.tickInput v (M.supportCutoff S.C (s + 1))).sentLock (M.chainStateOf S.C B).h with
    | none => exact Or.inl rfl
    | some T' =>
        right
        have hTT : T' = J₀.root := (lockBox_of_one_justification_tick M F Fx) S A x R E _ v v J₀ T'
          (by rw [max_self]; exact hAdv v hvs) hBv (by rw [← hH]; exact hl)
        have hE := (entry_block_of_boxTwo_st M F) S A x R E _ v B J₀ hBv hJ₀ hJB hH
        rw [hTT, hE]

open Classical in
/-- `lem80wq_round_height_advances_steps` in box 3. The proof; the audited statement is in
`Statements/Executions/RoundStatements.lean`.

Roots name blocks until `M.supportCutoff S.C (s'' - 1)`: the proof reads
`lem80wq_round_height_advances_steps` at the same slots, whose bound is that time.

Two lines the attestations' sync route reads:
`hGSTF`, the attestations' sync delay has elapsed after `GST` by the start of slot `s''`; and `hselq`, no member
of `Q` has justified past the height of `B`'s chain state before the later of the duty window's start of slot `s`
and `GST`.

The proposer's window `hp` starts `max (Δ S) Δs` before the support cutoff of slot `s − 1` and ends at the start
of slot `s`.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: when the proposer is in box 3 and each member in box 3 or box 1 with its
`head_height_floor` between the proposer's and the parent's height, the round raises the height or
puts the progress quorum on chain. -/
theorem lem80wq_boxThree (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (GST r s s'' : ℕ) (Hon : ℕ → Finset V) (Q : Finset V) (Hs : ℕ → Finset V)
    (H : V → Block V) (X B B' : Block V) (p q : V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (hRoots : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (s'' - 1) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    -- attestations are delivered within `Δ_F S` after `GST`
    {ΔNet_F : ℕ} (E_F : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {Δs_F : ℕ} (Sy_F : SyncedWithin A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST)
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    -- `s` is the first slot of round `r`, not the first slot of all; an attestation sent at
    -- the action time of slot `s` is delivered, within `Δ_F S`, before slot `s''` starts
    (hs : s = r * S.C.R) (hs1 : 1 ≤ s)
      (hs'' : M.supportCutoff S.C (s + 1) + Δ_F S ≤ M.slotStart S.C s'')
    -- the network is synchronous from the vote time of slot `s − 1`
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C (s - 1))
    (hGSTF : GST + max (Δ_F S) Δs_F ≤ M.slotStart S.C s'')
    -- the member sets shrink from one slot to the next
    (hHonMono : ∀ s', s ≤ s' → s' + 1 < s'' → Hon (s' + 1) ⊆ Hon s')
    -- for every slot `s'` before the last: the members of slot `s'` tick to its vote time, active up to that tick from
    -- the trace's start or from their own tick to a clock value at most the duty window's start of slot `s'`
    --, each runs the update of slot `s'`, and none is in the adversary set at a step where a
    -- validator outside it ticks to the support cutoff of slot `s' + 1`
    (hHon : ∀ s', s ≤ s' → s' + 1 < s'' → ∀ v ∈ Hon s',
      v ∈ A.activeThroughoutToTick x (duty_window_start S.C s') (M.voteTime S.C s'))
    (hHonUpd : ∀ s', s ≤ s' → s' + 1 < s'' → ∀ v ∈ Hon s', v ∈ updaterAt M S A x s')
    (hHonTick : ∀ s', s ≤ s' → s' + 1 < s'' → ∀ u ∈ Hon s', u ∉ Finset.univ.filter (fun u => ∃ (k : ℕ) (w : V),
      x.lbl k = Event.tick w (M.supportCutoff S.C (s' + 1)) ∧ w ∉ A.corrupted k ∧ u ∈ A.corrupted k))
    -- the members of the last slot `s'' − 1` tick to the start of slot `s''`, active up to that tick from the trace's start
    -- or from their own tick to a clock value at most the duty window's start of that slot
    (hHonLast : ∀ v ∈ Hon (s'' - 1),
      v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s'' - 1)) (M.slotStart S.C s''))
    -- the voters of the last slot `s'' − 1` are outside the adversary set at `q`'s tick to the start of slot `s''`,
    -- where `q`'s proposal counts their votes
    (hHonestQ : ∀ u ∈ Hs (s'' - 1), u ∉ A.corrupted (x.tickStep q (M.slotStart S.C s'')))
    -- the members of the round's first slot `s` are active in every configuration in force at a real time of the sync
    -- delay after `M.supportCutoff S.C (s + 1) - max (Δ S) Δs`, where Lemma 42 reads the sync fact for their blocks
    --
    (hHold42 : ∀ w ∈ Hon s, w ∈ A.activeThroughout x ((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- the members are active through the sync delay after `M.viewFreeze S.C s - max (Δ S) Δs` (Lemma 42's holder
    -- row `hv₀`;)
    (hHoldV : ∀ w ∈ Hon s, w ∈ A.activeThroughout x ((M.viewFreeze S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.viewFreeze S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- the members of the round's first slot are active through the attestations' sync delay after the later of
    -- the duty window's start of slot `s` and `GST`, where the attestations' sync fact is read
    --
    (hHoldF : ∀ w ∈ Hon s, w ∈ A.activeThroughout x ((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ)
      (((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ) + Δs_F))
    -- the proposer is active from the recovery delay before the support cutoff of slot `s − 1`
    -- through the start of slot `s`
    -- `tStart`: a clock value more than both clock bounds before Lemma 12's read time of slot `s − 1`; the proposer
    -- ticks to the start of slot `s`, active up to that tick from the trace's start or from its own tick to a clock value
    -- at most `tStart`, and is active through the sync delay after `M.slotStart S.C s - max (Δ S) Δs` (: the
    -- amended rows of the `_frame` theorems, under)
    (tStart : ℤ) (htStart : (tStart : ℝ) + ΔClockAhead + ΔClockBehind <
      ((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ))
    (hp : p ∈ A.activeThroughoutToTick x tStart (M.slotStart S.C s))
    (hHoldP : p ∈ A.activeThroughout x ((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- `p` put `B` on the wire at its tick at the start of slot `s`
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    -- the honest voters of slot `s − 1` vote for blocks on `X`'s chain, honest at the vote time
    -- of slot `s`
    (hHsPrev : ∀ u ∈ Hs (s - 1), u ∈ S.P.committee (s - 1) ∧
      (∀ w ∈ Hon s, u ∉ A.corrupted (x.tickStep w (M.voteTime S.C s))) ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s - 1)) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u (s - 1) (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H u ∈ (x.tickInput u (M.voteTime S.C (s - 1))).tree ∧ X.AncestorEq (H u))
    -- the previous slot's voters are active through the sync delay after Lemma 12's read time of slot `s − 1`
    -- ( under)
    (hHold : ∀ u ∈ Hs (s - 1), u ∈ A.activeThroughout x ((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s - 1) - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- at every member of `Hon s`, the voters its vote of slot `s` counts are fewer than twice
    -- `Hs (s − 1)`
    (hVotersPrev : ∀ w ∈ Hon s, ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes M S.C (x.tickInput w (M.voteTime S.C s)) s votes support_votes →
      M.voters_count votes < 2 * (Hs (s - 1)).card)
    -- `p`'s anchor is `X` or an ancestor of `X`
    (hApX :
        (M.get_anchor (x.tickInput p (M.slotStart S.C s))
            ((M.slotStart S.C s : ℕ) : Int)).AncestorEq X)
    -- every live lock a member's revocation of slot `s` leaves is on `B`'s parent's chain
    (hLocksW : ∀ w ∈ Hon s, ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C s))
        ((M.voteTime S.C s : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C s)) s →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.tickInput w (M.voteTime S.C s)) ((M.voteTime S.C s : ℕ) : Int) e =
          true → e.B.AncestorEq B.parent)
    -- `B` is the only slot-`s` block a member holds at the vote time; its root is new to `p`
    (hOnly : ∀ w ∈ Hon s, ∀ B₁ ∈ (x.tickInput w (M.voteTime S.C s)).tree, B₁.slot = s → B₁ = B)
    (hRootNew : ∀ B₁ ∈ (x.tickInput p (M.slotStart S.C s)).tree, B₁.root ≠ B.root)
    -- the honest voters of slot `s'` are members of `Hon s'` and of the slot's committee
    (hHs : ∀ s', s ≤ s' → s' < s'' → ∀ u ∈ Hs s', u ∈ Hon s' ∧ u ∈ S.P.committee s' ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s' ∧
        ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s') ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x.sent (i + 1) - x.sent i)
    -- the counts of slot `s'`, read at the members of `Hon s'`: the voters counted by a vote of
    -- slot `s' + 1` and the slot-`s'` voters of the pool at its tick to the support cutoff of slot
    -- `s' + 1` are fewer than twice `Hs s'`
    (hVoters : ∀ s', s ≤ s' → s' < s'' → ∀ v ∈ Hon s',
      (∀ votes support_votes : Finset (GoldfishVote V),
        CountedVotes M S.C (x.tickInput v (M.voteTime S.C (s' + 1)))
          (s' + 1) votes support_votes →
        M.voters_count votes < 2 * (Hs s').card) ∧
      M.voters_count (M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s' + 1))) s') < 2 *
        (Hs s').card)
    -- the slot-`(s'' − 1)` voters `q`'s proposal counts are fewer than twice `Hs (s'' − 1)`
    (hVotersQ : ∀ votes support_votes : Finset (GoldfishVote V),
      ProposalCountedVotes M (x.tickInput q (M.slotStart S.C s''))
        (s'' - 1) votes support_votes →
      M.voters_count votes < 2 * (Hs (s'' - 1)).card)
    -- the slot-`s` committee is at most twice `Hs s`
    (hHalf : (S.P.committee s).card ≤ 2 * (Hs s).card)
    -- `p` is in box 3 before the start of slot `s`
    (hBoxP : BoxThree M (x.tickInput p (M.slotStart S.C s)))
    -- before the vote time of slot `s`, every member of `Hon s` is in box 3 with greatest
    -- chain-state height at least `p`'s and at most `h(B.parent)`, or in box 1 with greatest
    -- chain-state height at least `p`'s plus one and at most `h(B.parent) + 1`
    (hBoxW : ∀ w ∈ Hon s,
      (BoxThree M (x.tickInput w (M.voteTime S.C s)) ∧ hMax M S.C
          (x.tickInput p (M.slotStart S.C s)) ≤ hMax M S.C
            (x.tickInput w (M.voteTime S.C s)) ∧
        hMax M S.C (x.tickInput w (M.voteTime S.C s)) ≤ (M.chainStateOf S.C B.parent).h) ∨
      (BoxOne M S.C (x.tickInput w (M.voteTime S.C s)) ∧ hMax M S.C
          (x.tickInput p (M.slotStart S.C s)) + 1 ≤ hMax M S.C
            (x.tickInput w (M.voteTime S.C s)) ∧
        hMax M S.C (x.tickInput w (M.voteTime S.C s)) ≤ (M.chainStateOf S.C B.parent).h + 1))
    -- before the action time, every member of `Hon s` is in box 3 with greatest chain-state height
    -- at most `h(B)`, or in box 1 with greatest chain-state height at most `h(B) + 1`
    (hBoxV : ∀ v ∈ Hon s,
      (BoxThree M (x.tickInput v (M.supportCutoff S.C (s + 1))) ∧ hMax M S.C
          (x.tickInput v (M.supportCutoff S.C (s + 1))) ≤ (M.chainStateOf S.C B).h) ∨
      (BoxOne M S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) ∧ hMax M S.C
          (x.tickInput v (M.supportCutoff S.C (s + 1))) ≤ (M.chainStateOf S.C B).h + 1))
    -- the finalized blocks: on `B`'s parent's chain at the vote time of slot `s`, on `B`'s chain
    -- at the action time
    (hFw : ∀ w ∈ Hon s, (x.tickInput w (M.voteTime S.C s)).finalized.AncestorEq B.parent)
    (hFar : ∀ v ∈ Hon s, (x.tickInput v (M.supportCutoff S.C (s + 1))).finalized.AncestorEq B)
    -- some block of `p`'s tree, on `X`'s and `p`'s finalized block's chains, reaches `p`'s
    -- greatest chain-state height
    (hHeadP : ∃ W ∈ (x.tickInput p (M.slotStart S.C s)).tree,
      X.AncestorEq W ∧ (x.tickInput p (M.slotStart S.C s)).finalized.AncestorEq W ∧ hMax M S.C
        (x.tickInput p (M.slotStart S.C s)) ≤ (M.chainStateOf S.C W).h)
    -- after the action time, at the members of the next slot: `StepFrameAt` relative to `B` for
    -- every slot `s'` with `s' + 3 ≤ s''`; for the last slot `s'' − 1`, the voter's fork choice
    -- before its vote time (the first two conjuncts of `StepFrameAt S Sched x B (s'' − 2) w`)
    (hStep : ∀ s', s ≤ s' → s' + 3 ≤ s'' → ∀ w ∈ Hon (s' + 1), StepFrameAt M S A x B s' w)
    (hStepLast : ∀ w ∈ Hon (s'' - 1),
      (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s'' - 1)))).fc_root.compatible B = true ∧
      ((M.fg_to_ac (x.tickInput w (M.voteTime S.C (s'' - 1)))).fc_root.AncestorEq B →
        ∃ W, VoterTreeAt M (x.tickInput w (M.voteTime S.C (s'' - 1)))
          (S.C.t_ ((s'' - 1) - 1) + 3 * S.C.Δ) (s'' - 1) W ∧ W ∈
            (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s'' - 1)))).viable_heads ∧
            B.AncestorEq W))
    -- the quorum attests at `a`, inside slot `s`'s active window
    (hQ : Q ⊆ Hon s) (hQuorum : quorum V ≤ Q.card)
    (hselq : ∀ v ∈ Q, M.justifiedHeight (x.stateBefore (max (M.dutyWindowStart S.C s) GST) v) ≤
      (M.chainStateOf S.C B).h)
    -- the next proposer is a member of the last slot's set
    (hq : q ∈ Hon (s'' - 1))
    -- `q` is active at every step from the real time at which the attestations' sync fact is read up to its own tick
    -- to the start of slot `s''` (the sync fact's receiver row,)
    (hqWin : ∀ i : ℕ, ((max (M.dutyWindowStart S.C s) GST : ℕ) : ℝ) ≤ x.time i →
      i ≤ x.tickStep q (M.slotStart S.C s'') → q ∈ A.active i)
    -- `q`'s fork-choice root before the start of slot `s''` is compatible with `B`, and when it
    -- is `B` or an ancestor of `B`, a block of `q`'s frame tree that is `B` or a descendant of `B`
    -- is a viable head
    (hFrameQ : (M.fg_to_ac (x.tickInput q (M.slotStart S.C s''))).fc_root.compatible B = true ∧
      ((M.fg_to_ac (x.tickInput q (M.slotStart S.C s''))).fc_root.AncestorEq B →
        ∃ W ∈ (M.fg_to_ac (x.tickInput q (M.slotStart S.C s''))).tree,
          W ∈ (M.fg_to_ac (x.tickInput q (M.slotStart S.C s''))).viable_heads ∧ B.AncestorEq W))
    -- `q` put `B'` on the wire at its tick at the start of slot `s''`
    (hPropose' : ∃ i : ℕ, x.lbl i = Event.tick q (M.slotStart S.C s'') ∧
      (⟨q, NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) :
    B.AncestorEq B' ∧
    ((M.chainStateOf S.C B).h + 1 ≤ (M.chainStateOf S.C B').h ∨
      ((M.chainStateOf S.C B').h = (M.chainStateOf S.C B).h ∧
        Q ⊆ (M.chainStateOf S.C B').progress ∧
        B'.slot < (M.chainStateOf S.C B).T_h.slot + S.C.δt)) ∧
    ((∀ u ∈ Q, ∀ b ∈ (x.tickInput u (M.supportCutoff S.C (s + 1))).sentAttestations,
        b.h ≠ (M.chainStateOf S.C B).h) →
      (M.chainStateOf S.C B).h + 1 ≤ (M.chainStateOf S.C B').h ∧
        ((M.chainStateOf S.C B'.parent).h = (M.chainStateOf S.C B).h →
          (M.chainStateOf S.C B').J = (M.chainStateOf S.C B).T_h)) := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hs2 := (GoldilocksCorrectness.Record.Proofs.Routines.slot_add_two_le_of_delivery M.toSlotLayout F.sched) S hs''
  obtain ⟨hvA, -, -, hsA, -, hk8, hΔ⟩ := (slot_times M F U) S s
  obtain ⟨-, hcB, -, -, -, -, -⟩ := (slot_times M F U) S (s + 1)
  have hss := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s
  have hdw := duty_window_start_real S (s + 1)
  push_cast at hdw
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hk8R : (8 : ℝ) * Δ S ≤ 4 * Δ S * S.C.k := by exact_mod_cast hk8
  have hvR : ((M.voteTime S.C s : ℕ) : ℝ) = 4 * Δ S * s + Δ S := by rw [hvA, hss]; push_cast; ring
  have hcR : ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) = 4 * Δ S * s + 6 * Δ S := by
    rw [hcB, hsA, hss]; push_cast; ring
  -- the states the ticks read satisfy the node invariant (Lemma 11 at the tick's step, whose validator is
  -- outside the adversary set)
  have hInvAt : ∀ (v : V) (t i : ℕ), x.lbl i = Event.tick v t → M.nodeInv S.C S.P S.X (x.tickInput v t) :=
    fun v t i hl => by
      rw [show x.tickInput v t = x.st i v by
        unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hl]]
      exact (lem11_node_invariant M F S A x R E i v (E.not_mem_corrupted_of_tick hl)).1
  have hInvP : M.nodeInv S.C S.P S.X (x.tickInput p (M.slotStart S.C s)) := by
    obtain ⟨i, hl, -⟩ := hPropose
    exact hInvAt p _ i hl
  -- each member ticks to the vote time of slot `s` inside its reader of slot `s`'s update
  have hInvW : ∀ w ∈ Hon s, M.nodeInv S.C S.P S.X (x.tickInput w (M.voteTime S.C s)) := by
    intro w hw
    have hr := (mem_activeThroughoutToTick_of_inside M F) R E (hHonUpd s le_rfl (by omega) w hw)
      (c := M.voteTime S.C s) (by omega) (by rw [hdw, hvR]; linarith) (by rw [hvR, hcR]; linarith)
    obtain ⟨k, hk, -⟩ := Activity.mem_activeThroughoutToTick.1 hr
    exact hInvAt w _ k hk
  have hInvV : ∀ v ∈ Hon s, M.nodeInv S.C S.P S.X (x.tickInput v (M.supportCutoff S.C (s + 1))) := by
    intro v hv
    obtain ⟨k, hk, -⟩ := Activity.mem_activeThroughoutToTick.1 (hHonUpd s le_rfl (by omega) v hv)
    exact hInvAt v _ k hk
  have hpS := (GoldilocksCorrectness.Record.Proofs.Routines.frameShape_of_boxThree M F) S.C S.P S.X _ hInvP hBoxP
  -- the members' frames: the root is the finalized block, the `head_height_floor` is between the proposer's and
  -- the parent's height at the tick to the vote time, at most `h(B)` at the tick to the support cutoff
  have hW : ∀ w ∈ Hon s, M.get_fc_root (x.tickInput w (M.voteTime S.C s)) =
        (x.tickInput w (M.voteTime S.C s)).finalized ∧
      M.head_height_floor (x.tickInput p (M.slotStart S.C s)) ≤
        M.head_height_floor (x.tickInput w (M.voteTime S.C s)) ∧
      M.head_height_floor (x.tickInput w (M.voteTime S.C s)) ≤ (M.chainStateOf S.C B.parent).h ∧
      (x.tickInput w (M.voteTime S.C s)).justifiedHeight < (M.chainStateOf S.C B.parent).h := by
    intro w hw
    rw [hpS.2.2]
    refine (GoldilocksCorrectness.Record.Proofs.Routines.floor_of_boxOne_or_boxThree M F) S.C S.P S.X _
      (hInvW w hw) _ _ ?_
    rcases hBoxW w hw with ⟨hb, h1, h2⟩ | ⟨hb, h1, h2⟩
    · exact Or.inr ⟨hb, h1, h2⟩
    · exact Or.inl ⟨hb, by unfold Height at *; omega, h2⟩
  have hV : ∀ v ∈ Hon s, M.get_fc_root (x.tickInput v (M.supportCutoff S.C (s + 1))) =
        (x.tickInput v (M.supportCutoff S.C (s + 1))).finalized ∧
      0 ≤ M.head_height_floor (x.tickInput v (M.supportCutoff S.C (s + 1))) ∧
      M.head_height_floor (x.tickInput v (M.supportCutoff S.C (s + 1))) ≤ (M.chainStateOf S.C B).h ∧
      (x.tickInput v (M.supportCutoff S.C (s + 1))).justifiedHeight < (M.chainStateOf S.C B).h := by
    intro v hv
    refine (GoldilocksCorrectness.Record.Proofs.Routines.floor_of_boxOne_or_boxThree M F) S.C S.P S.X _
      (hInvV v hv) _ _ ?_
    rcases hBoxV v hv with ⟨hb, h2⟩ | ⟨hb, h2⟩
    · exact Or.inr ⟨hb, Nat.zero_le _, h2⟩
    · exact Or.inl ⟨hb, Nat.zero_le _, h2⟩
  exact (lem80wq_round_height_advances_steps M F U Fx) S A x R GST r s s'' Hon Q Hs H X B B' p q
    (M.head_height_floor (x.tickInput p (M.slotStart S.C s)))
    (fun w => M.head_height_floor (x.tickInput w (M.voteTime S.C s)))
    (fun v => M.head_height_floor (x.tickInput v (M.supportCutoff S.C (s + 1))))
    (M.get_fc_root (x.tickInput p (M.slotStart S.C s)))
    (fun w => M.get_fc_root (x.tickInput w (M.voteTime S.C s)))
    (fun v => M.get_fc_root (x.tickInput v (M.supportCutoff S.C (s + 1))))
    E hNet hSkew hRedeliver hRoots hParent hOwner E_F hNet_F hSkew_F Sy hΔs Sy_F hΔs_F hs hs1 hs'' hGST hGSTF
    hHonMono hHon hHonUpd hHonTick hHonLast hHonestQ hHold42 hHoldV hHoldF tStart htStart hp hHoldP hPropose hHsPrev hHold
    hVotersPrev hApX hLocksW hOnly hRootNew hHs hVoters hVotersQ hHalf
    ⟨rfl, rfl⟩ (fun _ _ => ⟨rfl, rfl⟩) (fun _ _ => ⟨rfl, rfl⟩)
    (fun w hw => ⟨(hW w hw).2.1, (hW w hw).2.2.1⟩) (fun v hv => (hV v hv).2.2.1)
    (fun w hw => by rw [(hW w hw).1]; exact hFw w hw)
    (fun v hv => by rw [(hV v hv).1]; exact hFar v hv)
    (by rw [hpS.2.1, hpS.2.2]; exact hHeadP) hStep hStepLast hQ hQuorum
    (fun v hv => Or.inl (hV v (hQ hv)).2.2.2) hselq hq hqWin hFrameQ hPropose'

end GoldilocksCorrectness.Record.Proofs.Executions

