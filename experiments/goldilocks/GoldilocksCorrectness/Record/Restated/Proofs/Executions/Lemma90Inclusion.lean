module
public import GoldilocksCorrectness.Record.Restated.Proofs.View.Bridges
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma91
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.HealedChainBefore
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma78
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma90
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma81
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Sleepy
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.ProposalWalk
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.OrderedFloorStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.PhaseKitStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.FrameShapeStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.FastConfirmationStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.ProposalPropagationStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.SleepyStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.HealedFrameStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ConfirmationSupporters
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ForkChoiceFacts
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Node
public import GoldilocksCorrectness.Proofs.Executions.Lemma90Inclusion
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
import Mathlib.Tactic.Rify
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.AsyncDeliveryBoundary

@[expose] public section

/-!
# Lemma90Inclusion, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma90Inclusion.lean`, over a model `M`
whose facts `F` hold, for an execution `x` of `protocolOf M S`: the honest proposal of the slot two
after the healed slot, its parent on the honest chain, its votes, its saving by every updater, and
Lemma 90's inclusion, the honest proposal confirmed after healing. The page's routine-level theorems
are the facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff dutyWindowStart
  proposalWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_le_supportCutoff dutyWindowStart_mono
  dutyWindowStart_succ_le_slotStart one_le_Δ proposalWindowStart_eq proposal_window_start_eq
  slotStart_cast slotStart_eq slotStart_mono slot_after_healed_round slot_eq_of_mem
  slot_le_of_supportCutoff_lt supportCutoff_cast supportCutoff_eq supportCutoff_lt_of_lt
  voteTime_cast voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (earlySupporterOf_of_keepsVotes expireLocks_keepsVotes)

open GoldilocksCorrectness.Proofs.Routines (wake_eq)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)



open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax JustifiedInTree)


open GoldilocksCorrectness.Proofs.Routines (tick_emits_proposal)
open GoldilocksCorrectness.Statements.Routines (confirmedOf)

open GoldilocksCorrectness.Proofs.Routines (ac_on_tick_emits_vote)

open GoldilocksCorrectness.Proofs.Routines (DREBEmits DREBEmits.bind DREBEmits.ite DREBEmits.pure)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (Vocab.goldilocks acObject)
open GoldilocksCorrectness.Statements.Routines (expireLocks)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  ancestorEq_of_parent? awake_since_record_awake deepest?_mem ac_confirmed_cases)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded in the goal and in every
hypothesis: `omega` does not see a fact stated at either. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

omit [RootOrder] in
/-- The support cutoff grows with the slot: `supportCutoff_mono` of `Lemma89f.lean`, which this file
does not import (the forms on the chain before a slot read it).

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `a ≤ b`: the two slots.

Read aloud: the support cutoff of a slot is at most that of every later slot. -/
private theorem supportCutoff_le_of_le (S : Setup V) {a b : ℕ} (h : a ≤ b) :
    M.supportCutoff S.C a ≤ M.supportCutoff S.C b := by
  rcases Nat.lt_or_eq_of_le h with h | h
  · exact le_of_lt ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_lt_of_lt M.toSlotLayout F.sched) S h)
  · rw [h]

/-! ## Step 1: the proposal -/

/-- **Kit fact, an honest proposer proposes.** When the proposer of slot `q + 2` ticks to the start of slot
`q + 2`, active since the trace's start or since a tick, after its last restart, to a clock value at most the
protocol's proposal window start of slot `q + 2`, that tick puts a block on the wire.

Why: the tick answers (`RunFacts.tick`), the proposer's stored wake time at that tick is at most the proposal
window's start (`awakeSince_le_of_mem_activeThroughoutToTick`), so the proposal test passes, and the proposal
sends its block (`tick_emits_proposal`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `q`: the slot is `q + 2`.

Read aloud: an honest proposer of slot `q + 2`, active up to its tick to the slot's start from its proposal
window, puts a block on the wire at that tick. -/
theorem honest_proposer_proposes (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (q : ℕ)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hp : S.P.proposer (q + 2) ∈ A.activeThroughoutToTick x (proposal_window_start S.C (q + 2)) (M.slotStart S.C (q + 2))) :
    ∃ (i : ℕ) (B : Block V), x.lbl i = Event.tick (S.P.proposer (q + 2)) (M.slotStart S.C (q + 2)) ∧
      (⟨S.P.proposer (q + 2), NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i := by
  have hΔ := one_le_Δ S
  set p := S.P.proposer (q + 2) with hpdef
  -- the proposer's tick to the slot's start, and the outcome the step took
  obtain ⟨k', hk', -⟩ := Activity.mem_activeThroughoutToTick.1 hp
  obtain ⟨n', sent, hok, -, hsent⟩ := R.tick k' p (M.slotStart S.C (q + 2)) hk'
  have hin : x.tickInput p (M.slotStart S.C (q + 2)) = x.st k' p := by
    unfold Trace.tickInput
    rw [(tickStep_eq_of_lbl M) x E hk']
  -- the slot's start, read as the spec's time, and its slot
  have hcast := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_cast M.toSlotLayout F.sched U) S (q + 2)
  have hss := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (q + 2)
  have hslot : S.C.slot ((M.slotStart S.C (q + 2) : ℕ) : Int) = q + 2 := by
    rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast, hss]
    have h4 : 0 < 4 * Δ S := by omega
    exact Nat.mul_div_cancel_left (q + 2) h4
  have htime : ((M.slotStart S.C (q + 2) : ℕ) : Int) =
      S.C.t_ (S.C.slot ((M.slotStart S.C (q + 2) : ℕ) : Int)) := by
    rw [hslot]; exact hcast
  -- the wake test: awake since a time at most the proposal window's start
  have hab : proposal_window_start S.C (q + 2) < ((M.slotStart S.C (q + 2) : ℕ) : Int) := by
    have h := GoldilocksCorrectness.Record.proposal_window_start_lt_slotStart S.C _ htime
    rwa [hslot] at h
  obtain ⟨τ, hτ, hτle⟩ := (awakeSince_le_of_mem_activeThroughoutToTick M F) x R E hab hp
  rw [hin] at hτ
  have hτ' : τ ≤ proposal_window_start S.C (q + 2) := by
    rcases hτle with h | h
    · rw [h, GoldilocksCorrectness.Proofs.Routines.proposal_window_start_eqJ S q]
      exact GoldilocksCorrectness.Proofs.Routines.proposal_window_start_zero_le_duty S.C (q + 1)
    · exact h
  obtain ⟨-, -, haw⟩ := F.tk.tick_clock_validator_awakeSince S.C S.P S.X _ _ n' sent hok
  rw [hτ] at haw
  have hawake : M.awake_since n' (proposal_window_start S.C (S.C.slot ((M.slotStart S.C (q + 2) : ℕ) : Int))) =
      true := by
    rw [F.rd.awake_since_eq, haw, hslot]
    exact decide_eq_true hτ'
  -- the node's validator is the proposer
  have hvi : p ∉ A.corrupted k' := E.not_mem_corrupted_of_tick hk'
  have hnv : (x.st k' p).v = S.P.proposer (S.C.slot ((M.slotStart S.C (q + 2) : ℕ) : Int)) := by
    rw [hslot, (lem11_node_invariant M F S A x R E k' p hvi).2.1]
  have hpos : 0 < S.C.slot ((M.slotStart S.C (q + 2) : ℕ) : Int) := by
    rw [hslot]; exact Nat.succ_pos _
  obtain ⟨B, hB⟩ := F.tk.tick_emits_proposal S.C S.P S.X (x.st k' p) _ n' sent hok hpos htime hnv hawake
  refine ⟨k', B, hk', ?_⟩
  rw [hsent, add_tsub_cancel_left]
  exact Multiset.mem_map.2 ⟨_, Multiset.mem_coe.2 hB, rfl⟩

/-! ## The proposer's frame on the chain -/

/-- A tick to the support cutoff of slot `s_a + 1` at a step `k` whose time is more than `ΔClockAhead`
before the support cutoff of slot `q + 1` is for a slot `s_a < q`: a tick to a clock value `c` is at a real
time at least `c − ΔClockAhead` (`tick_active`).

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `E`: the environment's facts; `k`: the tick's step; `u`: its validator; `s_a`, `q`: the
  slots.

Read aloud: a tick to a slot's support cutoff, more than `ΔClockAhead` before the support cutoff of slot
`q + 1`, is for a slot before `q`. -/
theorem slot_lt_of_tick_time (S : Setup V) {A : Activity V} {x : Trace V (NamedObject V) M.N}
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {k s_a q : ℕ} {u : V} (hk : x.lbl k = Event.tick u (M.supportCutoff S.C (s_a + 1)))
    (htk : x.time k + ΔClockAhead < M.supportCutoff S.C (q + 1)) : s_a < q := by
  have h1 := (E.tick_active k u _ hk).2.1
  have h2 : (M.supportCutoff S.C (s_a + 1) : ℝ) < M.supportCutoff S.C (q + 1) := by linarith
  exact ((GoldilocksCorrectness.Record.Proofs.Routines.slot_le_of_supportCutoff_lt M.toSlotLayout F.sched) S s_a q).2.1
    (by exact_mod_cast h2)

/-- **Kit fact, the proposer's anchor is on the chain.** The anchor of the proposer `p` of slot
`q + 2`, read at its tick to the start of that slot (the tick's step `ip`), is on the honest chain before
slot `q + 1`, when `p` is an honest active validator of slot `q + 1`, its caches at the tick are on the chain,
and the lock invariant holds at slot `q` for the chain before `q + 1` (`hLk`).

Why: the anchor is the root of the fork choice (Lemma 91 (f) at `ip`: every tick to a support cutoff before
`ip` is for a slot before `q + 1`, since `ip` is at a real time at most `ΔClockBehind` after the slot's start)
or an ancestor of the block of a live lock entry. Such an entry is on `p`'s confirmation of slot `q` or an
ancestor of it, or on an ancestor of an entry `p`'s revocation of slot `q + 1` left live
(`live_lock_entry_source`, with `p` counted up to its tick to the slot's start); the latter is on the chain
by `hLk` when `p` is an honest active validator of slot `q`, and there is none when `p` slept before.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `q`: the slot
  of the proposal is `q + 2`; `H`: the threshold; `ip`: the step of
  the proposer's tick; `p`: the proposer.

Roots name blocks until `x[ip].time`: the root of the proposer's fork choice at its tick (Lemma 91 (f)).

Caches at `ip`: the one caches fact the proof reads, the proposer's at its tick.

Read aloud: the anchor of the honest proposer of slot `q + 2`, read at its tick to that slot's start, is on
the honest chain before slot `q + 1`. -/
theorem proposer_anchor_on_chain_until (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ q H ip : ℕ) (p : V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    (hRoots : RootsNameBlocksUntil M A x (x.time ip))
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (x.time ip))
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hCaches : CachesOnChain M S A x s₀ H (x.st ip p))
    (hs₀q : s₀ ≤ q)
    (hl : x.lbl ip = Event.tick p (M.slotStart S.C (q + 2)))
    (hpA : p ∈ honestActiveAt M S A x (q + 1))
    (hLk : ∀ u ∈ honestActiveAt M S A x q,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (q + 1)) q u) :
    OnHonestChainBefore M S A x s₀ (q + 1)
      (M.get_anchor (x.tickInput p (M.slotStart S.C (q + 2)))
          ((M.slotStart S.C (q + 2) : ℕ) : Int)) := by
  have hΔ := one_le_Δ S
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hss : M.slotStart S.C (q + 2) = M.slotStart S.C (q + 1) + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (q + 1), show q + 2 = (q + 1) + 1 from rfl, Nat.mul_add,
      Nat.mul_one]
  have hv2 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (q + 2)
  have hv1 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (q + 1)
  have hc1 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (q + 1)
  have hc2b := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (q + 1 + 1)
  have hv2b := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (q + 1 + 1)
  have hss2 : M.slotStart S.C (q + 1 + 1) = M.slotStart S.C (q + 2) := rfl
  have hdw := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_succ_le_slotStart M.toSlotLayout F.sched) S q
  have hsq : M.slotStart S.C q ≤ M.slotStart S.C (q + 1) := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (Nat.le_succ q)
  have hR1 : ((M.slotStart S.C q : ℕ) : ℝ) + 4 * (Δ S : ℝ) ≤ ((M.slotStart S.C (q + 2) : ℕ) : ℝ) := by
    exact_mod_cast (show M.slotStart S.C q + 4 * Δ S ≤ M.slotStart S.C (q + 2) by omega)
  have hR2 : ((M.slotStart S.C (q + 2) : ℕ) : ℝ) + 2 * (Δ S : ℝ) ≤ ((M.supportCutoff S.C (q + 1 + 1) : ℕ) : ℝ) := by
    exact_mod_cast (show M.slotStart S.C (q + 2) + 2 * Δ S ≤ M.supportCutoff S.C (q + 1 + 1) by omega)
  have hR3 : ((M.supportCutoff S.C (s₀ + 1) : ℕ) : ℝ) + 2 * (Δ S : ℝ) ≤ ((M.slotStart S.C (q + 2) : ℕ) : ℝ) := by
    have h := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
      (show s₀ + 1 ≤ q + 1 by omega)
    exact_mod_cast (show M.supportCutoff S.C (s₀ + 1) + 2 * Δ S ≤ M.slotStart S.C (q + 2) by omega)
  -- the tick's step: its state is the tick input, `p` is honest there, at a real time within the clock bounds
  have hin : x.tickInput p (M.slotStart S.C (q + 2)) = x.st ip p := by
    unfold Trace.tickInput
    rw [(tickStep_eq_of_lbl M) x E hl]
  have hpi : p ∉ A.corrupted ip := E.not_mem_corrupted_of_tick hl
  obtain ⟨-, hip1, hip2⟩ := E.tick_active ip p _ hl
  have hroot : OnHonestChainBefore M S A x s₀ (q + 1)
      (M.fg_to_ac (x.tickInput p (M.slotStart S.C (q + 2)))).fc_root := by
    rw [hin]
    refine (lem91f_voter_root_on_chain_before_until M F U Fx) S A x R s₀ ip (q + 1) H p E hRoots
      (hAdvQ.mono (max_le le_rfl (by linarith))) hOld hCaches hpi ?_
    rintro s_a ⟨k, w, hk, hkl⟩
    exact (slot_lt_of_tick_time M F) S E hkl (by
      have := (time_mono M) x R hk.le
      linarith)
  rcases (GoldilocksCorrectness.Record.Proofs.Routines.get_anchor_cases_live_lock M F)
      (x.tickInput p (M.slotStart S.C (q + 2))) ((M.slotStart S.C (q + 2) : ℕ) : Int) with
    h | ⟨e, he, hlive, hae⟩
  · rw [h]; exact hroot
  · have hdl : ((M.slotStart S.C (q + 2) : ℕ) : Int) < e.d := by
      rw [(GoldilocksCorrectness.Record.Proofs.Routines.is_live_iff M F)] at hlive
      exact hlive.1
    -- `p` is counted up to its tick to the slot's start, from the duty window's start of slot `q + 2`
    have hdwI := (GoldilocksCorrectness.Record.Proofs.Routines.duty_window_start_le_dutyWindowStart M.toSlotLayout
      F.sched U) S (q + 1)
    have hdwI2 : duty_window_start S.C (q + 1) ≤ ((M.dutyWindowStart S.C (q + 2) : ℕ) : ℤ) :=
      le_trans hdwI (by exact_mod_cast (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_mono
        M.toSlotLayout F.sched) S (show q + 1 ≤ q + 2 by omega))
    have hdwR : ((duty_window_start S.C (q + 1) : ℤ) : ℝ) ≤ ((M.slotStart S.C q : ℕ) : ℝ) := by
      have : duty_window_start S.C (q + 1) ≤ ((M.slotStart S.C q : ℕ) : ℤ) :=
        le_trans hdwI (by exact_mod_cast hdw)
      exact_mod_cast this
    have hHon : p ∈ A.activeThroughoutToTick x ((M.dutyWindowStart S.C (q + 2) : ℕ) : ℤ) (M.slotStart S.C (q + 2)) :=
      Activity.mem_activeThroughoutToTick_of_le hdwI2
        ((mem_activeThroughoutToTick_of_inside M F) R E ((honestActiveAt_window M F) S A (q + 1) p E hpA)
          (by omega) (by linarith) (by linarith))
    rcases (live_lock_entry_source M F U) S A x R q (M.slotStart S.C (q + 2)) p E hSkew hHon
        (by omega) (by omega) e he hdl with
      ⟨C', hC', heC⟩ | ⟨n₃, sent₃, hrun₃, hA₃, e', he', hlive', hee'⟩
    · exact (onHonestChainBefore_of_ancestorEq M F) S A x s₀ (q + 1)
        ⟨q, Nat.lt_succ_self q, hs₀q, p, (honestActiveAt_succ_subset_updaterAt M F U) S A q R E hSkew hpA,
          C', hC', ancestorEq_refl C'⟩ (ancestorEq_trans hae heC)
    · rcases (mem_honestActiveAt_or_lockFree M F U) S A q p R E hSkew hpA with hpq | hslept
      · -- the outcome `n₃` of `p`'s tick at the vote time of slot `q + 1`, read by the lock invariant
        obtain ⟨D, hD, he'D⟩ := hLk p hpq n₃ sent₃ hrun₃ hA₃ e' he' hlive'
        exact (onHonestChainBefore_of_ancestorEq M F) S A x s₀ (q + 1) hD
          (ancestorEq_trans hae (ancestorEq_trans hee' he'D))
      · -- that tick revoked the locks there, and `p` held no live entry before it
        exact ((revoke_locks_empty_of_lockFree M F) S A x (M.voteTime S.C (q + 1)) (q + 1) _ n₃
          (Nat.le_add_left 1 q) hslept
          ((locksRevoked_of_voteTime_outcome M F U) S A x R E (q + 1) p n₃ sent₃ hrun₃ hA₃) e'
          he').elim

/-- **Kit fact, the proposer's anchor is on the chain.** `proposer_anchor_on_chain_until` with the caches
restricted to the steps it reads.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `q`: the slot
  of the proposal is `q + 2`; `i₁`: the step at the phase's end; `H`: the threshold; `ip`: the step of
  the proposer's tick; `p`: the proposer.

Roots name blocks until `x[ip].time`: the root of the proposer's fork choice at its tick.

Read aloud: the anchor of the honest proposer of slot `q + 2`, read at its tick to that slot's start, is on
the honest chain before slot `q + 1`. -/
theorem proposer_anchor_on_chain (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ q i₁ H ip : ℕ) (p : V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    (hRoots : RootsNameBlocksUntil M A x (x.time ip))
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (x.time ip))
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x.time i₁ ≤ x.time j → u ∉ A.corrupted j →
      CachesOnChain M S A x s₀ H (x.st j u))
    (hs₀q : s₀ ≤ q)
    (hl : x.lbl ip = Event.tick p (M.slotStart S.C (q + 2))) (hi₁ : x.time i₁ ≤ x.time ip)
    (hpA : p ∈ honestActiveAt M S A x (q + 1))
    (hLk : ∀ u ∈ honestActiveAt M S A x q,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (q + 1)) q u) :
    OnHonestChainBefore M S A x s₀ (q + 1)
      (M.get_anchor (x.tickInput p (M.slotStart S.C (q + 2)))
          ((M.slotStart S.C (q + 2) : ℕ) : Int)) :=
  (proposer_anchor_on_chain_until M F U Fx) S A x R s₀ q H ip p E hSkew hRoots hAdvQ hOld
    (hCaches ip p hi₁ (E.not_mem_corrupted_of_tick hl)) hs₀q hl hpA hLk

/-- The first clause of the chain invariant at slot `r`, as a function: some `H` names, for every
honest active committee member `u` of slot `r`, the block of `u`'s slot-`r` vote, held by `u`, of
which every block of the chain before `r` is an ancestor or which it is.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `r`: the slot;
  `C₀`: a block of the chain before `r`.

Read aloud: some function names, for every honest active committee member of slot `r`, the block of
its slot-`r` vote, which it holds and which every block of the chain before `r` is an ancestor of or
equal to. -/
theorem chain_votes_of_inv (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ r : ℕ) (C₀ : Block V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    (hInv : ChainInvFor M S A x (honestActiveAt M S A x r)
        (OnHonestChainBefore M S A x s₀ r) r)
    (hC₀ : OnHonestChainBefore M S A x s₀ r C₀) :
    ∃ H : V → Block V, ∀ u ∈ honestActiveAt M S A x r ∩ S.P.committee r,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C r) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u r (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H u ∈ (x.tickInput u (M.voteTime S.C r)).tree ∧
      ∀ C : Block V, OnHonestChainBefore M S A x s₀ r C → C.AncestorEq (H u) := by
  obtain ⟨H, hH⟩ := (voters_of_votes_clause M F U) S A x R r (honestActiveAt M S A x r ∩ S.P.committee r)
    C₀ E hSkew (fun u hu => Finset.mem_inter.1 hu)
    (fun u hu => (hInv C₀ hC₀).1 u (Finset.mem_inter.1 hu).1)
  refine ⟨H, fun u hu => ⟨(hH u hu).1, (hH u hu).2.1, fun C hC => ?_⟩⟩
  obtain ⟨H', hH'T, heq, hCH'⟩ := (hInv C hC).1 u (Finset.mem_inter.1 hu).1 _ (hH u hu).1
  have hroot : (H u).root = H'.root := by
    have := congrArg GoldfishVote.head heq
    exact this
  obtain ⟨iu, hiu, -⟩ := (hH u hu).1
  have hti : x.tickInput u (M.voteTime S.C r) = x.st iu u := by
    unfold Trace.tickInput
    rw [(tickStep_eq_of_lbl M) x E hiu]
  have hInvU : M.nodeInv S.C S.P S.X (x.tickInput u (M.voteTime S.C r)) := by
    rw [hti]
    exact (lem11_node_invariant M F S A x R E iu u (E.not_mem_corrupted_of_tick hiu)).1
  have hHH : H u = H' := (F.nd.nodeInv_rootsNameBlocksIn hInvU) _ (hH u hu).2.1 _ hH'T hroot
  rw [hHH]
  exact hCH'

/-- After the phase's end, an honest validator's greatest chain-state height is at least `H + 2`:
its justification height is more than `H` (`CachesOnChain`) and less than that greatest height.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `H`: the threshold; `j`: the step; `u`: the validator.

Caches at step `j`: the one caches fact the proof reads, `u`'s at step `j`.

Read aloud: after the phase's end, an honest validator's greatest chain-state height is at least
`H + 2`. -/
theorem h_max_ge_of_caches_until
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (s₀ H j : ℕ) (u : V)
    (hCaches : CachesOnChain M S A x s₀ H (x.st j u)) :
    H + 2 ≤ hMax M S.C (x.st j u) := by
  obtain ⟨hHp, -, -, -, -⟩ := hCaches
  obtain ⟨⟨Dp, hDp, -, hhjDp⟩, -, -⟩ := (cachesWitnessed_of_exec M F) S A x R E j u
  -- the chain-state height of an accepted block is at most the greatest one (the record's chain
  -- states are computed, so no equation on the stored chain state is read)
  have hDpm : (M.chainStateOf S.C Dp).h ≤ hMax M S.C (x.st j u) := le_hMax M hDp
  have hjh := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C Dp Dp).1.2.1
  rw [hhjDp] at hHp
  omega_nat

/-- After the phase's end, an honest validator's greatest chain-state height is at least `H + 2`:
its justification height is more than `H` (`CachesOnChain`) and less than that greatest height.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `i₁`: the step
  at the phase's end; `H`: the threshold; `j`: the step; `u`: the validator.

It is `h_max_ge_of_caches_until` with the caches restricted to the steps it reads.

Read aloud: after the phase's end, an honest validator's greatest chain-state height is at least
`H + 2`. -/
theorem h_max_ge_of_caches (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (s₀ i₁ H j : ℕ) (u : V)
    (hCaches : ∀ (j : ℕ) (u : V), x.time i₁ ≤ x.time j → u ∉ A.corrupted j →
      CachesOnChain M S A x s₀ H (x.st j u))
    (hj : x.time i₁ ≤ x.time j) (hu : u ∉ A.corrupted j) :
    H + 2 ≤ hMax M S.C (x.st j u) :=
  (h_max_ge_of_caches_until M F) S A x R E s₀ H j u (hCaches j u hj hu)

/-- The honest chain before slot `q + 1` has a block at the chain-state height `m − 1`, with `m`
the greatest chain-state height of the proposer's tree read at its tick to the start of slot `q + 2` (the
tick's step `ip`).

Why: the proposer holds a block at `m`; the block that raised its chain past `m − 1` carries a
certificate at `m − 1 > H`, and the certificate route names an entry of the chain at `m − 1`
confirmed at a slot `s_a` whose support cutoff some validator ticked to before `ip`, so `s_a < q + 1`
(`ip` is at a real time at most `ΔClockBehind` after the slot's start).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `q`: the slot
  of the proposal is `q + 2`; `H`: the threshold; `ip`: the step of
  the proposer's tick; `p`: the proposer.

Caches at `ip`: the one caches fact the proof reads, `p`'s at its tick.

Read aloud: the honest chain before slot `q + 1` has a block at the chain-state height one less than
the greatest chain-state height of the proposer's tree at its tick to the start of slot `q + 2`. -/
theorem proposer_entry_on_chain_until (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ q H ip : ℕ) (p : V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    -- fewer than a quorum of validators have been in the adversary set up to the later of the tick's time and the hand-over cutoff
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max (x.time ip) (M.supportCutoff S.C (s₀ + 1))))
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hCaches : CachesOnChain M S A x s₀ H (x.st ip p))
    (hl : x.lbl ip = Event.tick p (M.slotStart S.C (q + 2))) :
    ∃ E : Block V, OnHonestChainBefore M S A x s₀ (q + 1) E ∧
      (M.chainStateOf S.C E).h = hMax M S.C (x.tickInput p (M.slotStart S.C (q + 2))) - 1 := by
  have hΔ := one_le_Δ S
  have hB0 := E.behind_nonneg
  have hc2b := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (q + 1 + 1)
  have hv2b := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (q + 1 + 1)
  have hss2 : M.slotStart S.C (q + 1 + 1) = M.slotStart S.C (q + 2) := rfl
  have hR2 : ((M.slotStart S.C (q + 2) : ℕ) : ℝ) + 2 * (Δ S : ℝ) ≤ ((M.supportCutoff S.C (q + 1 + 1) : ℕ) : ℝ) := by
    exact_mod_cast (show M.slotStart S.C (q + 2) + 2 * Δ S ≤ M.supportCutoff S.C (q + 1 + 1) by omega)
  have hin : x.tickInput p (M.slotStart S.C (q + 2)) = x.st ip p := by
    unfold Trace.tickInput
    rw [(tickStep_eq_of_lbl M) x E hl]
  obtain ⟨-, -, hip2⟩ := E.tick_active ip p _ hl
  have hm2 := (h_max_ge_of_caches_until M F) S A x R E s₀ H ip p hCaches
  obtain ⟨-, ⟨Y, hY, hYh⟩, -⟩ := (cachesWitnessed_of_exec M F) S A x R E ip p
  rw [hin]
  obtain ⟨Y₁, hY₁Y, -, -, -, -, hPC⟩ := (GoldilocksCorrectness.Record.Statements.Routines.lem67_first_advance M F) S.C Y
    (hMax M S.C (x.st ip p) - 1) (by omega_nat) (by rw [hYh]; omega_nat)
  have hY₁T : Y₁ ∈ (x.st ip p).tree := (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E ip p Y Y₁ hY hY₁Y
  obtain ⟨s_a, uₐ, Eb, hlt, hlbl, -, -, -, hAt, -, hEh, -⟩ := (cert_entry_at_slot M F U Fx) S A x R s₀ H ip p Y₁ _ _ E
     hAdvQ hOld hY₁T hPC (by omega_nat)
  have hsa : s_a < q + 1 := (slot_lt_of_tick_time M F) S E hlbl (by
    have := (time_mono M) x R hlt.le
    linarith)
  exact ⟨Eb, ⟨s_a, hsa, hAt⟩, hEh⟩

/-- `proposer_entry_on_chain_until` with the caches restricted to the steps it reads.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `q`: the slot
  of the proposal is `q + 2`; `i₁`: the step at the phase's end; `H`: the threshold; `ip`: the step of
  the proposer's tick; `p`: the proposer.

Read aloud: the honest chain before slot `q + 1` has a block at the chain-state height one less than
the greatest chain-state height of the proposer's tree at its tick to the start of slot `q + 2`. -/
theorem proposer_entry_on_chain (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ q i₁ H ip : ℕ) (p : V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    (hAdvQ : ∀ t : ℝ, A.AdversaryFewerThanQuorumUntil x (quorum V) t)
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x.time i₁ ≤ x.time j → u ∉ A.corrupted j →
      CachesOnChain M S A x s₀ H (x.st j u))
    (hl : x.lbl ip = Event.tick p (M.slotStart S.C (q + 2))) (hi₁ : x.time i₁ ≤ x.time ip) :
    ∃ E : Block V, OnHonestChainBefore M S A x s₀ (q + 1) E ∧
      (M.chainStateOf S.C E).h = hMax M S.C (x.tickInput p (M.slotStart S.C (q + 2))) - 1 :=
  (proposer_entry_on_chain_until M F U Fx) S A x R s₀ q H ip p E hSkew (hAdvQ _) hOld
    (hCaches ip p hi₁ (E.not_mem_corrupted_of_tick hl)) hl

/-! ## Steps 2 and 3: the parent and the votes -/

/-- The proposer's real-time windows from its activity up to its tick: from `p` active up to
its tick to the support cutoff of slot `q + 3`, from the trace's start or from its own tick to a clock value at most
the spec's integer start of its proposal window `Goldilocks.proposal_window_start S.C (q + 2)` (never truncated: for
a small `q` it is negative, and then only "active since the trace's start" remains), the constraint `htStart` of
`lem59le_goldfish_vote_names_honest_proposal_frame` at slot `q + 1` with that start, and three real-time windows of
`p`: from `max (Δ S) Δs` before the vote time of `q + 2` through the start of `q + 2`; from `max (Δ S) Δs` before
the support cutoff of `q + 1` through it; from `M.voteTime S.C (q + 1) + Δ S - max (Δ S) Δs` through
`M.voteTime S.C (q + 1) + Δ S`. Each window starts more than `ΔClockBehind` after the proposal window's start, by
`hΔs`, and ends more than `ΔClockAhead` before the support cutoff of `q + 3`, by `hSkew`
(`mem_activeThroughout_of_mem_activeThroughoutToTick_real`). No case on the value of the window's start.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `S`: the setup; `A`: the activity;
- `x`, `R`, `E`: the execution, its facts, its environment facts; `ΔClockAhead`, `ΔClockBehind`: the clock bounds;
- `q`: the slot before the proposal's; `Δs`: the sync delay; `p`: the proposer.

Read aloud: a proposer active up to its tick to the support cutoff of slot `q + 3` from the start of its proposal
window is active throughout the three real-time windows the inclusion step reads. -/
theorem proposer_windows_of_activeThroughoutToTick (U : UniformSchedule M.toSlotLayout) (S : Setup V)
    (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release
      ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    {q Δs : ℕ} {p : V}
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hp : p ∈ A.activeThroughoutToTick x (Goldilocks.proposal_window_start S.C (q + 2))
      (M.supportCutoff S.C (q + 3))) :
    ((Goldilocks.proposal_window_start S.C (q + 2) : ℤ) : ℝ) + ΔClockAhead + ΔClockBehind <
      ((M.supportCutoff S.C (q + 1) - max (2 * Δ S) Δs : ℕ) : ℝ) ∧
    p ∈ A.activeThroughout x ((M.voteTime S.C (q + 2)) - (max (Δ S) Δs)) (M.slotStart S.C (q + 2)) ∧
    p ∈ A.activeThroughout x ((M.supportCutoff S.C (q + 1)) - (max (Δ S) Δs)) (M.supportCutoff S.C (q + 1)) ∧
    p ∈ A.activeThroughout x (M.voteTime S.C (q + 1) + Δ S - max (Δ S) Δs) (M.voteTime S.C (q + 1) + Δ S) := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ := GoldilocksCorrectness.Proofs.Routines.one_le_Δ S
  have hΔR : (1 : ℝ) ≤ (Δ S : ℝ) := by exact_mod_cast hΔ
  have hd : ((Goldilocks.proposal_window_start S.C (q + 2) : ℤ) : ℝ) =
      4 * ((Δ S : ℝ) * (q : ℝ)) + 5 * (Δ S : ℝ) - 4 * ((Δ S : ℝ) * (S.C.k : ℝ)) := by
    rw [GoldilocksCorrectness.Proofs.Routines.proposal_window_start_eq S q, duty_window_start_real S (q + 1)]
    push_cast; ring
  have hs1 : ((M.slotStart S.C (q + 1) : ℕ) : ℝ) = 4 * ((Δ S : ℝ) * (q : ℝ)) + 4 * (Δ S : ℝ) := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (q + 1)]; push_cast; ring
  have hv1 : ((M.voteTime S.C (q + 1) : ℕ) : ℝ) = 4 * ((Δ S : ℝ) * (q : ℝ)) + 5 * (Δ S : ℝ) := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (q + 1),
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (q + 1)]
    push_cast; ring
  have hc1 : ((M.supportCutoff S.C (q + 1) : ℕ) : ℝ) = 4 * ((Δ S : ℝ) * (q : ℝ)) + 6 * (Δ S : ℝ) := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (q + 1),
      (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (q + 1),
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (q + 1)]
    push_cast; ring
  have hs2 : ((M.slotStart S.C (q + 2) : ℕ) : ℝ) = 4 * ((Δ S : ℝ) * (q : ℝ)) + 8 * (Δ S : ℝ) := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (q + 2)]; push_cast; ring
  have hv2 : ((M.voteTime S.C (q + 2) : ℕ) : ℝ) = 4 * ((Δ S : ℝ) * (q : ℝ)) + 9 * (Δ S : ℝ) := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (q + 2),
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (q + 2)]
    push_cast; ring
  have hc3 : ((M.supportCutoff S.C (q + 3) : ℕ) : ℝ) = 4 * ((Δ S : ℝ) * (q : ℝ)) + 14 * (Δ S : ℝ) := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (q + 3),
      (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (q + 3),
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (q + 3)]
    push_cast; ring
  have hmx1 : (Δ S : ℝ) ≤ (max (Δ S) Δs : ℕ) := by exact_mod_cast le_max_left (Δ S) Δs
  have hmx0 : (0 : ℝ) ≤ (max (Δ S) Δs : ℕ) := by positivity
  have hq0 : (0 : ℝ) ≤ (Δ S : ℝ) * (q : ℝ) := by positivity
  have hm2 : (max (2 * Δ S) Δs : ℕ) ≤ max (Δ S) Δs + Δ S := by
    rcases le_total (2 * Δ S) Δs with h | h
    · rw [max_eq_right h]; omega
    · rw [max_eq_left h]; omega
  have hm2R : ((max (2 * Δ S) Δs : ℕ) : ℝ) ≤ (max (Δ S) Δs : ℕ) + (Δ S : ℝ) := by exact_mod_cast hm2
  push_cast at hΔs hmx1 hmx0 hm2R
  refine ⟨?_, ?_, ?_, ?_⟩
  · rcases le_or_gt (max (2 * Δ S) Δs) (M.supportCutoff S.C (q + 1)) with hle | hlt
    · rw [Nat.cast_sub hle, hd, hc1]; push_cast; linarith
    · rw [Nat.sub_eq_zero_of_le hlt.le, hd]; push_cast
      have : ((M.supportCutoff S.C (q + 1) : ℕ) : ℝ) < ((max (2 * Δ S) Δs : ℕ) : ℝ) := by exact_mod_cast hlt
      push_cast at this
      rw [hc1] at this
      linarith
  · exact (mem_activeThroughout_of_mem_activeThroughoutToTick_real M F) R E hp (by rw [hd, hv2]; push_cast; linarith)
      (by rw [hs2, hc3]; linarith)
  · exact (mem_activeThroughout_of_mem_activeThroughoutToTick_real M F) R E hp (by rw [hd, hc1]; push_cast; linarith)
      (by rw [hc1, hc3]; linarith)
  · exact (mem_activeThroughout_of_mem_activeThroughoutToTick_real M F) R E hp (by rw [hd, hv1]; push_cast; linarith)
      (by rw [hv1, hc3]; linarith)

/-- The `GST` lines and the windows `honest_proposal_extends_chain_until` passes to its callees
, built from its `GST` line at the healed slot `s₀ ≤ q` and from the
proposer's activity up to its tick to the support cutoff of slot `q + 3` from the spec's start of its proposal
window, under `hΔs`. Write `t₀` for `M.voteTime S.C (q + 1) + Δ S - max (Δ S) Δs`, the
start of the window of the voters' blocks reaching the proposer:
1. `GST ≤ t₀`; 2. `t₀ + max (Δ S) Δs` is the
support cutoff of `q + 1`'s time `M.voteTime S.C (q + 1) + Δ S`; 3. `GST + max (Δ S) Δs ≤
M.supportCutoff S.C (q + 1)`; 4. `GST ≤ M.voteTime S.C (q + 1)`; 5. `GST + max (Δ S) Δs ≤
M.voteTime S.C (q + 2)`; 6. the vote time of `q + 1` is at most the support cutoff of `q + 2`, and the vote time of
`q + 2` at most the support cutoff of `q + 3`;
7. `p` is active from `max (Δ S) Δs` before the vote time of `q + 2` through the start of `q + 2`;
8. `p` is active from `max (Δ S) Δs` before the support cutoff of `q + 1` through it; 9. `p` is
active from `t₀` through `M.voteTime S.C (q + 1) + Δ S`.

Kept out of the proof that reads them so that its elaboration stays within its budget.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `S`: the setup; `A`: the
  activity; `x`, `R`, `E`: the execution, its facts, its environment facts; `GST`, `s₀`, `q`: the time from which
  the network is synchronous, the healed slot, the slot before the proposal's; `Δs`: the sync delay; `p`: the
  proposer.

Read aloud: the proposer's activity up to its tick from the start of its proposal window and the healed slot's
`GST` line give every window and `GST` line the proof of the inclusion step reads. -/
theorem chain_until_windows (U : UniformSchedule M.toSlotLayout) (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver}
    {GST s₀ q Δs : ℕ} {p : V} {ΔClockAhead ΔClockBehind : ℝ}
    (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release
      ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀) (hs₀q : s₀ ≤ q)
    (hp : p ∈ A.activeThroughoutToTick x (Goldilocks.proposal_window_start S.C (q + 2))
      (M.supportCutoff S.C (q + 3))) :
    GST ≤ M.voteTime S.C (q + 1) + Δ S - max (Δ S) Δs ∧
    M.voteTime S.C (q + 1) + Δ S - max (Δ S) Δs + max (Δ S) Δs ≤ M.voteTime S.C (q + 1) + Δ S ∧
    GST + max (Δ S) Δs ≤ M.supportCutoff S.C (q + 1) ∧
    GST ≤ M.voteTime S.C (q + 1) ∧
    GST + max (Δ S) Δs ≤ M.voteTime S.C (q + 2) ∧
    M.voteTime S.C (q + 1) ≤ M.supportCutoff S.C (q + 2) ∧
    M.voteTime S.C (q + 2) ≤ M.supportCutoff S.C (q + 2 + 1) ∧
    p ∈ A.activeThroughout x ((M.voteTime S.C (q + 2)) - (max (Δ S) Δs))
      (M.slotStart S.C (q + 2)) ∧
    p ∈ A.activeThroughout x ((M.supportCutoff S.C (q + 1)) - (max (Δ S) Δs))
      (M.supportCutoff S.C (q + 1)) ∧
    p ∈ A.activeThroughout x (M.voteTime S.C (q + 1) + Δ S - max (Δ S) Δs)
      (M.voteTime S.C (q + 1) + Δ S) := by
  obtain ⟨-, hw8, hw9, hw10⟩ :=
    (proposer_windows_of_activeThroughoutToTick M F) U S A x R E hSkew hΔs hp
  obtain ⟨hv1, hc1, -, hs1, -, hk1, hΔ⟩ := (slot_times M F U) S (q + 1)
  obtain ⟨hv2, hc2, -, hs2, -, -, -⟩ := (slot_times M F U) S (q + 2)
  obtain ⟨-, hc3', -, -, -, -, -⟩ := (slot_times M F U) S (q + 2 + 1)
  have hc3 : M.supportCutoff S.C (q + 3) = M.slotStart S.C (q + 3) + 2 * Δ S := hc3'
  have hs2' : M.slotStart S.C (q + 2) = M.slotStart S.C (q + 1) + 4 * Δ S := hs1
  have hs3 : M.slotStart S.C (q + 3) = M.slotStart S.C (q + 2) + 4 * Δ S := hs2
  have h0 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
    (show s₀ ≤ q + 1 by omega)
  have hmx1 := le_max_left (Δ S) Δs
  have hmx2 := le_max_right (Δ S) Δs
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hkN : max (Δ S) Δs + 3 * Δ S < 4 * Δ S * S.C.k := by
    have : ((max (Δ S) Δs + 3 * Δ S : ℕ) : ℝ) < ((4 * Δ S * S.C.k : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have hcb2 : max (Δ S) Δs ≤ M.voteTime S.C (q + 2) := by omega
  have hcb1 : max (Δ S) Δs ≤ M.supportCutoff S.C (q + 1) := by omega
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, hw8, hw9, hw10⟩

/-- The real-time inequalities `honest_proposal_extends_chain_until` reads between the slot times of `q + 1`,
`q + 2` and `q + 3`, the proposer's window opening `Goldilocks.proposal_window_start S.C (q + 2)` and the voters'
`Goldilocks.duty_window_start S.C (q + 2)`, under `hSkew` and `hΔs`: each window opening is more than both clock
bounds before the times its readers shorten it to, and the opening of the voters' window is more than both clock
bounds before the sync fact's read time `supportCutoff (q + 1) − max (2 Δ) Δs` (that ℕ subtraction read in its two
cases). Kept out of the proof that reads them so that its elaboration stays within its budget.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `S`: the setup;
- `ΔClockAhead`, `ΔClockBehind`: the clock bounds; `q`: the slot before the proposal's; `Δs`: the sync delay.

Read aloud: the slot times around slot `q + 2` and the two window openings are far enough apart for every window the
inclusion step shortens. -/
theorem extends_chain_until_reals (U : UniformSchedule M.toSlotLayout) (S : Setup V) {ΔClockAhead ΔClockBehind : ℝ}
    (hA0 : 0 ≤ ΔClockAhead) (hB0 : 0 ≤ ΔClockBehind) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) {q Δs : ℕ}
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) :
    ((Goldilocks.proposal_window_start S.C (q + 2) : ℤ) : ℝ) + ΔClockBehind <
      ((M.supportCutoff S.C (q + 1) : ℕ) : ℝ) - ΔClockAhead ∧
    ((M.supportCutoff S.C (q + 1) : ℕ) : ℝ) + ΔClockBehind < ((M.supportCutoff S.C (q + 3) : ℕ) : ℝ) - ΔClockAhead ∧
    ((Goldilocks.proposal_window_start S.C (q + 2) : ℤ) : ℝ) + ΔClockBehind <
      ((M.supportCutoff S.C (q + 2) : ℕ) : ℝ) - ΔClockAhead ∧
    ((M.supportCutoff S.C (q + 2) : ℕ) : ℝ) + ΔClockBehind < ((M.supportCutoff S.C (q + 3) : ℕ) : ℝ) - ΔClockAhead ∧
    ((Goldilocks.proposal_window_start S.C (q + 2) : ℤ) : ℝ) + ΔClockBehind <
      ((M.slotStart S.C (q + 2) : ℕ) : ℝ) - ΔClockAhead ∧
    ((M.slotStart S.C (q + 2) : ℕ) : ℝ) + ΔClockBehind < ((M.supportCutoff S.C (q + 3) : ℕ) : ℝ) - ΔClockAhead ∧
    ((Goldilocks.duty_window_start S.C (q + 2) : ℤ) : ℝ) + ΔClockBehind <
      ((M.voteTime S.C (q + 2) : ℕ) : ℝ) - ΔClockAhead ∧
    ((M.voteTime S.C (q + 2) : ℕ) : ℝ) + ΔClockBehind < ((M.supportCutoff S.C (q + 3) : ℕ) : ℝ) - ΔClockAhead ∧
    ((Goldilocks.duty_window_start S.C (q + 2) : ℤ) : ℝ) + ΔClockAhead + ΔClockBehind <
      ((M.slotStart S.C (q + 2) : ℕ) : ℝ) ∧
    ((Goldilocks.duty_window_start S.C (q + 2) : ℤ) : ℝ) + ΔClockAhead + ΔClockBehind <
      ((M.supportCutoff S.C (q + 1) - max (2 * Δ S) Δs : ℕ) : ℝ) ∧
    ((Goldilocks.proposal_window_start S.C (q + 2) : ℤ) : ℝ) + ΔClockBehind <
      ((M.supportCutoff S.C (q + 1) - max (2 * Δ S) Δs : ℕ) : ℝ) ∧
    Goldilocks.proposal_window_start S.C (q + 2) ≤ Goldilocks.duty_window_start S.C (q + 2) ∧
    ((M.voteTime S.C (q + 2) : ℕ) : ℝ) = ((M.slotStart S.C (q + 2) : ℕ) : ℝ) + Δ S ∧
    ((M.supportCutoff S.C (q + 2) : ℕ) : ℝ) = ((M.slotStart S.C (q + 2) : ℕ) : ℝ) + 2 * Δ S ∧
    ((M.supportCutoff S.C (q + 1) : ℕ) : ℝ) + 2 * Δ S = ((M.slotStart S.C (q + 2) : ℕ) : ℝ) ∧
    ((M.supportCutoff S.C (q + 3) : ℕ) : ℝ) = ((M.slotStart S.C (q + 2) : ℕ) : ℝ) + 6 * Δ S := by
  obtain ⟨hv1, hc1, -, hs1, -, hk8, hΔ⟩ := (slot_times M F U) S (q + 1)
  obtain ⟨hv2, hc2, -, hs2, -, -, -⟩ := (slot_times M F U) S (q + 2)
  obtain ⟨-, hc3', -, -, -, -, -⟩ := (slot_times M F U) S (q + 2 + 1)
  have hs12 : M.slotStart S.C (q + 2) = M.slotStart S.C (q + 1) + 4 * Δ S := hs1
  have hs23 : M.slotStart S.C (q + 3) = M.slotStart S.C (q + 2) + 4 * Δ S := hs2
  have hc3 : M.supportCutoff S.C (q + 3) = M.slotStart S.C (q + 3) + 2 * Δ S := hc3'
  have hΔR : (1 : ℝ) ≤ (Δ S : ℝ) := by exact_mod_cast hΔ
  have hk8R : (8 : ℝ) * Δ S ≤ 4 * Δ S * S.C.k := by exact_mod_cast hk8
  have hs1R : ((M.slotStart S.C (q + 1) : ℕ) : ℝ) = 4 * (Δ S : ℝ) * (q : ℝ) + 4 * (Δ S : ℝ) := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (q + 1)]; push_cast; ring
  have hs2R : ((M.slotStart S.C (q + 2) : ℕ) : ℝ) = 4 * (Δ S : ℝ) * (q : ℝ) + 8 * (Δ S : ℝ) := by
    rw [hs12]; push_cast; rw [hs1R]; ring
  have hv2R : ((M.voteTime S.C (q + 2) : ℕ) : ℝ) = 4 * (Δ S : ℝ) * (q : ℝ) + 9 * (Δ S : ℝ) := by
    rw [hv2]; push_cast; rw [hs2R]; ring
  have hc1R : ((M.supportCutoff S.C (q + 1) : ℕ) : ℝ) = 4 * (Δ S : ℝ) * (q : ℝ) + 6 * (Δ S : ℝ) := by
    rw [hc1]; push_cast; rw [hs1R]; ring
  have hc2R : ((M.supportCutoff S.C (q + 2) : ℕ) : ℝ) = 4 * (Δ S : ℝ) * (q : ℝ) + 10 * (Δ S : ℝ) := by
    rw [hc2]; push_cast; rw [hs2R]; ring
  have hc3R : ((M.supportCutoff S.C (q + 3) : ℕ) : ℝ) = 4 * (Δ S : ℝ) * (q : ℝ) + 14 * (Δ S : ℝ) := by
    rw [hc3, hs23]; push_cast; rw [hs2R]; ring
  have hpwR : ((Goldilocks.proposal_window_start S.C (q + 2) : ℤ) : ℝ) =
      4 * (Δ S : ℝ) * (q : ℝ) + 5 * (Δ S : ℝ) - 4 * (Δ S : ℝ) * (S.C.k : ℝ) := by
    rw [GoldilocksCorrectness.Proofs.Routines.proposal_window_start_eq S q, duty_window_start_real S (q + 1)]
    push_cast; ring
  have hdw2R : ((Goldilocks.duty_window_start S.C (q + 2) : ℤ) : ℝ) =
      4 * (Δ S : ℝ) * (q : ℝ) + 9 * (Δ S : ℝ) - 4 * (Δ S : ℝ) * (S.C.k : ℝ) := by
    rw [duty_window_start_real S (q + 2)]; push_cast; ring
  have hq0 : (0 : ℝ) ≤ 4 * (Δ S : ℝ) * (q : ℝ) := by positivity
  have hmx1 : (Δ S : ℝ) ≤ ((max (Δ S) Δs : ℕ) : ℝ) := by exact_mod_cast le_max_left (Δ S) Δs
  have hmx2 : (Δs : ℝ) ≤ ((max (Δ S) Δs : ℕ) : ℝ) := by exact_mod_cast le_max_right (Δ S) Δs
  push_cast at hΔs hmx1 hmx2
  have htS : ((Goldilocks.duty_window_start S.C (q + 2) : ℤ) : ℝ) + ΔClockAhead + ΔClockBehind <
      ((M.supportCutoff S.C (q + 1) - max (2 * Δ S) Δs : ℕ) : ℝ) := by
    rcases le_total (2 * Δ S) Δs with h2 | h2
    · have hm : max (2 * Δ S) Δs = Δs := max_eq_right h2
      have h2R : 2 * (Δ S : ℝ) ≤ Δs := by exact_mod_cast h2
      have hmΔ : (max (Δ S : ℝ) (Δs : ℝ)) = Δs := max_eq_right (by linarith)
      rw [hmΔ] at hΔs
      rw [hm]
      rcases le_or_gt Δs (M.supportCutoff S.C (q + 1)) with hle | hlt
      · rw [Nat.cast_sub hle, hdw2R, hc1R]; linarith
      · rw [Nat.sub_eq_zero_of_le hlt.le, hdw2R]
        have hltR : ((M.supportCutoff S.C (q + 1) : ℕ) : ℝ) < Δs := by exact_mod_cast hlt
        rw [hc1R] at hltR; push_cast; linarith
    · have hm : max (2 * Δ S) Δs = 2 * Δ S := max_eq_left h2
      rw [hm]
      have hle : 2 * Δ S ≤ M.supportCutoff S.C (q + 1) := by omega
      rw [Nat.cast_sub hle, hdw2R, hc1R]; push_cast; linarith
  have hpwdw : ((Goldilocks.proposal_window_start S.C (q + 2) : ℤ) : ℝ) ≤
      ((Goldilocks.duty_window_start S.C (q + 2) : ℤ) : ℝ) := by rw [hpwR, hdw2R]; linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, htS, by linarith, by exact_mod_cast hpwdw, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (rw [hpwR, hc1R]; linarith) | (rw [hc1R, hc3R]; linarith) | (rw [hpwR, hc2R]; linarith)
    | (rw [hc2R, hc3R]; linarith) | (rw [hpwR, hs2R]; linarith) | (rw [hs2R, hc3R]; linarith)
    | (rw [hdw2R, hv2R]; linarith) | (rw [hv2R, hc3R]; linarith) | (rw [hdw2R, hs2R]; linarith)
    | (rw [hv2R, hs2R]; ring) | (rw [hc2R, hs2R]; ring) | (rw [hc1R, hs2R]; ring)

/-- **Steps 2 and 3 of the inclusion: the proposal's parent extends the chain, and every honest
vote names the proposal.** Under the hypotheses of the inclusion at slot `q + 2`, with the lock
invariant at slot `q` (`hLk`) and `B` the proposal of slot `q + 2` with a root new to its proposer:
every block of the chain before `q + 1` is `B`'s parent or an ancestor of it; `B` is a non-genesis
block of slot `q + 2`; every vote an honest active validator `w` of slot `q + 2` sends at the vote
time of slot `q + 2` names `B`; and every such `w` holds `B` before that vote time.

Why: the proposer's root and anchor are on the chain (Lemma 91 (f), `proposer_anchor_on_chain`);
every honest committee member of slot `q + 1` voted for a block extending the chain, which reaches
the proposer as a viable head; so the proposal's parent extends every block of the chain
(`proposal_parent_extends_majority_block`, `get_anchor_ancestorEq_proposal_parent`). Lemma 59 with
ordered `head_height_floor` values (the least chain-state height a viable block may have) (`lem59le_goldfish_vote_names_honest_proposal_frame`) then names `B` in every
honest vote: the forms with `head_height_floor` at the proposer at most `head_height_floor` at the
voter hold by Lemma 91 (c) and (d), and `head_height_floor` at the voter is at most the
parent's height by Lemma 91 (b). Lemmas 22a and 22 deliver `B`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold;
- `q`: the slot of the proposal is `q + 2`; `ip`: the step of the proposer's tick; `B`: the
  proposal.

Roots name blocks until `M.voteTime S.C (q + 2)`: the proof reads the proposer's root and anchor
before the start of slot `q + 2`, the voters' roots and Lemmas 22, 59 (ordered `head_height_floor` values) and 91
(c) up to the vote time of slot `q + 2`.

Caches, and the count of the adversary, up to the real time of each validator's tick to a clock value at most
`M.voteTime S.C (q + 2)`: the proof reads the proposer's at its tick to the start of
slot `q + 2` and each voter's at its tick to the vote time of slot `q + 2` (Lemmas 91 (b), (d) and (f)). Two named
gaps remain in the proof: the proposer's tick at or after `x[i₁].time` (F-75-3 (3)) and Lemma 91 (c) at the two
tick inputs (F-76-1).

Read aloud: the honest proposal of slot `q + 2` has a parent that every block of the chain before
`q + 1` is an ancestor of or equal to, and every honest vote of slot `q + 2` names it. -/
theorem honest_proposal_extends_chain_until (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ anchor i₁ H q ip : ℕ) (B : Block V)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks up to the real time of each validator's tick to a clock value at most the vote time of slot
    -- `q + 2`
    (hRoots : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.voteTime S.C (q + 2) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    -- fewer than a quorum in the adversary set up to the real time of each validator's tick to a clock value at most
    -- the vote time of slot `q + 2` (, read as `hRoots`)
    (hAdvQ : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.voteTime S.C (q + 2) →
      A.AdversaryFewerThanQuorumUntil x (quorum V) (x.time k))
    (hSleepK : CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C (q + 2))) (hAnchor : anchor ≤ x.time i₁)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀)
    (hChain : ConfirmationsChainBefore M S A x s₀ (q + 1))
    (hInv : ∀ s : ℕ, s₀ < s → s ≤ q + 1 →
      ChainInvFor M S A x (honestActiveAt M S A x s) (OnHonestChainBefore M S A x s₀ s) s)
    (hLocks : ∀ s : ℕ, s₀ < s → s ≤ q + 1 → ∀ u ∈ honestActiveAt M S A x s,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ s) s u)
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    -- caches on the chain at the steps from the phase's end up to the real time of each validator's tick to a clock
    -- value at most the vote time of slot `q + 2` (, read as `hRoots`)
    (hCaches : ∀ (k : ℕ) (w : V) (c : ℕ), x.lbl k = Event.tick w c → c ≤ M.voteTime S.C (q + 2) →
      ∀ (j : ℕ) (u : V), i₁ < j → x.time j ≤ x.time k →
      u ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j u))
    (ht₀ : M.supportCutoff S.C (s₀ + 1) ≤ x.time i₁)
    (hs₀q : s₀ ≤ q) (hs : x.time i₁ < M.slotStart S.C (q + 2))
    -- the proposer's tick to the start of slot `q + 2` is after the phase's end (, strict by)
    (hip : x.time i₁ < x.time ip)
    (hLk : ∀ u ∈ honestActiveAt M S A x q,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (q + 1)) q u)
    -- the honest voters of slot `q + 1` are active through the sync delay after Lemma 12's read time of slot `q + 1`
    -- ( under)
    (hHold : ∀ u ∈ honestActiveAt M S A x (q + 1), u ∈ S.P.committee (q + 1) →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C (q + 1) - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C (q + 1) - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hp : S.P.proposer (q + 2) ∈ A.activeThroughoutToTick x (Goldilocks.proposal_window_start S.C (q + 2))
        (M.supportCutoff S.C (q + 3)) ∧
      S.P.proposer (q + 2) ∉ A.corruptedAtTime x (M.supportCutoff S.C (q + 3)))
    -- the proposer is active through the sync delay after `M.slotStart S.C (q + 2) - max (Δ S) Δs`
    -- the amended row `hHoldP`,)
    (hHoldP : S.P.proposer (q + 2) ∈ A.activeThroughout x ((M.slotStart S.C (q + 2) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C (q + 2) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hl : x.lbl ip = Event.tick (S.P.proposer (q + 2)) (M.slotStart S.C (q + 2)))
    (hsent : (⟨S.P.proposer (q + 2), NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
      x.sent (ip + 1) - x.sent ip)
    (hRootNew : ∀ B' ∈ (x.tickInput (S.P.proposer (q + 2)) (M.slotStart S.C (q + 2))).tree,
      B'.root ≠ B.root) :
    (∀ C : Block V, OnHonestChainBefore M S A x s₀ (q + 1) C → C.AncestorEq B.parent) ∧
    B.slot = q + 2 ∧ B ≠ Block.genesis ∧ B.parent.AncestorEq B ∧
    (∀ w ∈ honestActiveAt M S A x (q + 2), ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick w (M.voteTime S.C (q + 2)) ∧
        (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x.sent (i + 1) - x.sent i) → vote.head = B.root) ∧
    (∀ w ∈ honestActiveAt M S A x (q + 2), B ∈ (x.tickInput w (M.voteTime S.C (q + 2))).tree)
      := by
  -- the times (`extends_chain_until_reals`), the GST lines (`chain_until_windows`)
  set p := S.P.proposer (q + 2) with hpdef
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, htS, htSp, hpwdw, ev2, ec2, ec1, ec3⟩ :=
    (extends_chain_until_reals M F U) S hA0 hB0 hSkew (q := q) hΔs
  obtain ⟨hW1, hW2, hW3, hW4, hW5, hW6, hW7, -, -, -⟩ :=
    (chain_until_windows M F U) S A x R E hSkew hΔs hGST hs₀q hp.1
  have hc0R : ((M.supportCutoff S.C (s₀ + 1) : ℕ) : ℝ) ≤ ((M.supportCutoff S.C (q + 1) : ℕ) : ℝ) := by
    exact_mod_cast (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
      (show s₀ + 1 ≤ q + 1 by omega)
  have hΔ := one_le_Δ S
  have hc1N : 1 ≤ M.supportCutoff S.C (q + 1) :=
    ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_slot M.toSlotLayout F.sched) S q).2
  have hs2c1 : M.supportCutoff S.C (q + 1) ≤ M.slotStart S.C (q + 2) := by
    have h : ((M.supportCutoff S.C (q + 1) : ℕ) : ℝ) ≤ ((M.slotStart S.C (q + 2) : ℕ) : ℝ) := by
      have : (0 : ℝ) ≤ (Δ S : ℝ) := Nat.cast_nonneg _
      linarith only [ec1, this]
    exact_mod_cast h
  have hss2N : M.slotStart S.C (q + 2) ≤ M.voteTime S.C (q + 2) := by
    have h := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (q + 2); omega
  have hc1vN : M.supportCutoff S.C (q + 1) ≤ M.voteTime S.C (q + 2) := le_trans hs2c1 hss2N
  have hv2N := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (q + 2)
  -- the proposer's tick `ip` to the start of slot `q + 2`, its state, its real time
  obtain ⟨-, hip1, hip2⟩ := E.tick_active ip p _ hl
  have hpi : p ∉ A.corrupted ip := E.not_mem_corrupted_of_tick hl
  have hin : x.tickInput p (M.slotStart S.C (q + 2)) = x.st ip p := by
    unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hl]
  have hipv : x.time ip ≤ ((M.voteTime S.C (q + 2) : ℕ) : ℝ) := by linarith only [hip2, ev2, hSkew, hA0]
  have hc0ip : ((M.supportCutoff S.C (s₀ + 1) : ℕ) : ℝ) ≤ x.time ip := by
    linarith only [hip1, hc0R, ec1, hSkew, hB0]
  have hRootsP : RootsNameBlocksUntil M A x (x.time ip) := hRoots ip p _ hl hss2N
  have hAdvP : A.AdversaryFewerThanQuorumUntil x (quorum V) (x.time ip) := hAdvQ ip p _ hl hss2N
  have hAdvPm : A.AdversaryFewerThanQuorumUntil x (quorum V)
      (max (x.time ip) (M.supportCutoff S.C (s₀ + 1))) := hAdvP.mono (max_le le_rfl hc0ip)
  have hCachesP : ∀ (j : ℕ) (u : V), i₁ < j → x.time j ≤ x.time ip →
      u ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j u) :=
    hCaches ip p _ hl hss2N
  -- the one caches fact the Lemma 91 kit reads at the proposer's tick
  have hCp : CachesOnChain M S A x s₀ H (x.st ip p) := hCachesP ip p ((lt_of_time_lt M) x R hip) le_rfl hpi
  -- every tick to a support cutoff before a step of real time at most `t` with `t + ΔClockAhead` before the support
  -- cutoff of slot `q + 2` is for a slot before `q + 1`
  have hsBefore : ∀ (j : ℕ), x.time j + ΔClockAhead < ((M.supportCutoff S.C (q + 1 + 1) : ℕ) : ℝ) →
      ∀ s_a : ℕ, (∃ (k : ℕ) (u : V), k < j ∧ x.lbl k = Event.tick u (M.supportCutoff S.C (s_a + 1))) →
      s_a < q + 1 := by
    rintro j hj s_a ⟨k, u, hk, hkl⟩
    exact (slot_lt_of_tick_time M F) S E hkl (by
      have := (time_mono M) x R hk.le
      linarith only [this, hj])
  have hipc2 : x.time ip ≤ ((M.supportCutoff S.C (q + 1 + 1) : ℕ) : ℝ) := by
    show _ ≤ ((M.supportCutoff S.C (q + 2) : ℕ) : ℝ)
    linarith only [hip2, ec2, hSkew, hA0]
  have hipc : x.time ip + ΔClockAhead < ((M.supportCutoff S.C (q + 1 + 1) : ℕ) : ℝ) := by
    show x.time ip + ΔClockAhead < ((M.supportCutoff S.C (q + 2) : ℕ) : ℝ)
    linarith only [hip2, ec2, hSkew]
  -- the proposer is an honest active validator of slot `q + 1`
  have hpAct : p ∈ A.activeThroughoutToTick x (Goldilocks.proposal_window_start S.C (q + 2))
      (M.supportCutoff S.C (q + 1 + 1)) :=
    (mem_activeThroughoutToTick_of_inside M F) R E hp.1
      (show 1 ≤ M.supportCutoff S.C (q + 2) from
        ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_slot M.toSlotLayout F.sched) S (q + 1)).2) r3 r4
  have hpA : p ∈ honestActiveAt M S A x (q + 1) := by
    unfold honestActiveAt activeAt
    refine Finset.mem_sdiff.2 ⟨?_, fun h => ?_⟩
    · rw [← GoldilocksCorrectness.Proofs.Routines.proposal_window_start_eq S q]
      exact Activity.mem_awakeThroughoutToTick_of_mem_activeThroughoutToTick hpAct
    · rcases Finset.mem_union.1 h with h1 | h2
      · exact (not_mem_corruptedAtTime_of_mem_activeThroughoutToTick M F) x R E hp.1
          (show ((M.supportCutoff S.C (q + 2) : ℕ) : ℝ) + ΔClockAhead < _ by linarith only [r4, hB0]) h1
      · exact (outside_at_honest_ticks_of_mem_activeThroughoutToTick M F) x R E hp.1
          (show ((M.supportCutoff S.C (q + 2) : ℕ) : ℝ) + ΔClockBehind + ΔClockAhead < _ by linarith only [r4]) h2
  -- the chain before `q + 1`: the proposer's root and anchor, its entry at `hMax − 1` (Lemma 91 (f), step form)
  have hρp : OnHonestChainBefore M S A x s₀ (q + 1) (M.get_fc_root (x.tickInput p (M.slotStart S.C (q + 2)))) := by
    rw [hin, ← (GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F)]
    exact (lem91f_voter_root_on_chain_before_until M F U Fx) S A x R s₀ ip (q + 1) H p E hRootsP hAdvPm hOld
      hCp hpi (hsBefore ip hipc)
  have hap := (proposer_anchor_on_chain_until M F U Fx) S A x R s₀ q H ip p E hSkew hRootsP hAdvP hOld
    hCp hs₀q hl hpA hLk
  obtain ⟨Hf, hHf⟩ := (chain_votes_of_inv M F) U S A x R s₀ (q + 1) _ E hSkew
    (hInv (q + 1) (by omega) le_rfl) hρp
  obtain ⟨Eb, hE, hEh⟩ := (proposer_entry_on_chain_until M F U Fx) S A x R s₀ q H ip p E hSkew hAdvPm hOld
    hCp hl
  -- committee sleepiness: the honest active members of slot `q + 1` are more than half of its committee
  have hK := hSleepK (q + 1 + 1) (by omega)
    (by have h := lt_of_le_of_lt hAnchor hs
        have h' : anchor < M.slotStart S.C (q + 2) := by exact_mod_cast h
        exact h'.le) le_rfl
  rw [Nat.add_sub_cancel] at hK
  have hsub : S.P.committee (q + 1) \ (honestActiveAt M S A x (q + 1) ∩ S.P.committee (q + 1)) ⊆
      S.P.committee (q + 1) \ honestActiveAt M S A x (q + 1) := by
    intro w hw
    simp only [Finset.mem_sdiff, Finset.mem_inter] at hw ⊢
    tauto
  have hMaj : |S.P.committee (q + 1) \ (honestActiveAt M S A x (q + 1) ∩ S.P.committee (q + 1))| <
      |honestActiveAt M S A x (q + 1) ∩ S.P.committee (q + 1)| :=
    lt_of_le_of_lt (Finset.card_le_card hsub) hK
  have hcard : 0 < (honestActiveAt M S A x (q + 1) ∩ S.P.committee (q + 1)).card := by
    have := Finset.card_le_card_sdiff_add_card (s := S.P.committee (q + 1))
      (t := honestActiveAt M S A x (q + 1) ∩ S.P.committee (q + 1))
    omega
  obtain ⟨u₀, hu₀⟩ : (honestActiveAt M S A x (q + 1) ∩ S.P.committee (q + 1)).Nonempty :=
    Finset.card_pos.1 hcard
  -- the honest members of slot `q + 1` are honest at every step up to the support cutoff of slot `q + 2`
  have hHonU : ∀ u ∈ honestActiveAt M S A x (q + 1) ∩ S.P.committee (q + 1), ∀ j : ℕ,
      x.time j ≤ ((M.supportCutoff S.C (q + 1 + 1) : ℕ) : ℝ) → u ∉ A.corrupted j := fun u hu j hj =>
    (not_mem_corrupted_of_le_time M) x R E
      (fun h => (Finset.mem_sdiff.1 (Finset.mem_inter.1 hu).1).2 (Finset.mem_union_left _ h)) hj
  -- the proposer's tick to the support cutoff of slot `q + 1` and its activity from the sync fact's read time (the
  -- core's form)
  have hpCore : ∃ kR : ℕ, x.lbl kR = Event.tick p (M.supportCutoff S.C (q + 1)) ∧
      ∀ j : ℕ, ((M.supportCutoff S.C (q + 1) - max (2 * Δ S) Δs : ℕ) : ℝ) ≤ x.time j → j ≤ kR → p ∈ A.active j := by
    exact (tick_window_of_activeThroughoutToTick_int M) x R E
      ((mem_activeThroughoutToTick_of_inside M F) R E hp.1 hc1N r1 r2) htSp
  obtain ⟨kR, hkR, -⟩ := id hpCore
  have hRootsR : RootsNameBlocksUntil M A x (x.time (x.tickStep p (M.supportCutoff S.C (q + 1)))) := by
    rw [(tickStep_eq_of_lbl M) x E hkR]
    exact hRoots kR p _ hkR hc1vN
  have hOwner := (GoldilocksCorrectness.Record.Statements.Executions.votesCastByOwner_of_unforgeability M F) S A x R E
  have hFp : ∀ u ∈ honestActiveAt M S A x (q + 1) ∩ S.P.committee (q + 1),
      (x.tickInput p (M.slotStart S.C (q + 2))).finalized.AncestorEq (Hf u) := by
    intro u hu
    refine ancestorEq_trans ?_ ((hHf u hu).2.2 _ hρp)
    rw [hin]
    exact (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F) S A x R E ip p
  -- every voter's block of slot `q + 1` reaches the proposer by its tick (Lemma 12, step form)
  have hHeldP := (lem12_honest_vote_delivered_until_of_steps M F U) S A x R GST (q + 1) (M.slotStart S.C (q + 2))
    (honestActiveAt M S A x (q + 1) ∩ S.P.committee (q + 1)) Hf p E hNet hSkew hRedeliver Sy hΔs hRootsR hParent
    hOwner hW3 hs2c1 ip hl
    (fun u hu => ⟨(Finset.mem_inter.1 hu).2, hHonU u hu ip hipc2, (hHf u hu).1,
      (hHf u hu).2.1⟩)
    (fun u hu => hHold u (Finset.mem_inter.1 hu).1 (Finset.mem_inter.1 hu).2)
    hpCore
    hFp
  have hFρp : (x.tickInput p (M.slotStart S.C (q + 2))).finalized.AncestorEq
      (M.get_fc_root (x.tickInput p (M.slotStart S.C (q + 2)))) := by
    rw [hin]
    exact (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F) S A x R E ip p
  have hInvP : M.nodeInv S.C S.P S.X (x.tickInput p (M.slotStart S.C (q + 2))) := by
    rw [hin]; exact (lem11_node_invariant M F S A x R E ip p hpi).1
  have hφp : M.head_height_floor (x.tickInput p (M.slotStart S.C (q + 2))) =
      hMax M S.C (x.tickInput p (M.slotStart S.C (q + 2))) - 1 := by
    rw [hin]
    exact ((lem91d_not_contested_until M F U Fx) S A x R s₀ ip (q + 1) H p E hAdvPm hChain hOld hCp hpi
      (hsBefore ip hipc)).2
  have hHp : ∀ u ∈ honestActiveAt M S A x (q + 1) ∩ S.P.committee (q + 1),
      Hf u ∈ (x.tickInput p (M.slotStart S.C (q + 2))).tree := fun u hu =>
    (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 (hHeldP u hu).2.2.1).1
  have hHv : ∀ u ∈ honestActiveAt M S A x (q + 1) ∩ S.P.committee (q + 1),
      Hf u ∈ (M.fg_to_ac (x.tickInput p (M.slotStart S.C (q + 2)))).tree ∧
      Hf u ∈ (M.fg_to_ac (x.tickInput p (M.slotStart S.C (q + 2)))).viable_heads ∧
      M.head_height_floor (x.tickInput p (M.slotStart S.C (q + 2))) ≤ (M.chainStateOf S.C (Hf u)).h := by
    intro u hu
    have hT := hHp u hu
    have hCH := (hHf u hu).2.2
    have hFH := ancestorEq_trans hFρp (hCH _ hρp)
    have hφ : M.head_height_floor (x.tickInput p (M.slotStart S.C (q + 2))) ≤
        (M.chainStateOf S.C (Hf u)).h := by
      rw [hφp, ← hEh]
      exact ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C Eb (Hf u)).2.2.2.1 (hCH Eb hE)
    refine ⟨((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).2 ⟨hT, hFH⟩,
      (((GoldilocksCorrectness.Record.Statements.Routines.lem56_frame_of_shape M F) S.C S.P S.X _ hInvP _ _
        ⟨rfl, rfl⟩).2.2 (Hf u)).2 ⟨hT, hFH, hCH _ hρp, ?_⟩, hφ⟩
    exact hφ
  -- the proposal's parent extends every block of the chain before `q + 1`
  have hPE : ∀ X : Block V, OnHonestChainBefore M S A x s₀ (q + 1) X →
      (M.get_anchor (x.tickInput p (M.slotStart S.C (q + 1 + 1)))
        ((M.slotStart S.C (q + 1 + 1) : ℕ) : Int)).AncestorEq X →
      X.AncestorEq B.parent ∧ B.slot = q + 1 + 1 ∧ B ≠ Block.genesis ∧
      B.parent? = some B.parent ∧
      (B.parent ∈ M.viable_tree (M.fg_to_ac (x.tickInput p (M.slotStart S.C (q + 1 + 1))))
          (M.fg_to_ac (x.tickInput p (M.slotStart S.C (q + 1 + 1)))).tree ∨
        B.parent = M.get_anchor (x.tickInput p (M.slotStart S.C (q + 1 + 1)))
          ((M.slotStart S.C (q + 1 + 1) : ℕ) : Int)) := by
    intro X hX haX
    exact (proposal_parent_extends_majority_block M F U) S A x R GST (q + 1) ip
      (honestActiveAt M S A x (q + 1) ∩ S.P.committee (q + 1)) Hf X B p E hNet hSkew hRedeliver Sy hΔs
      hRootsR hParent hOwner hW3
      (fun u hu => ⟨(Finset.mem_inter.1 hu).2,
        by rw [(tickStep_eq_of_lbl M) x E hl]; exact hHonU u hu ip hipc2,
        (hHf u hu).1, (hHf u hu).2.1, (hHf u hu).2.2 X hX⟩)
      (fun votes_p support_p hPCV => by
        rw [hPCV.1]
        exact (GoldilocksCorrectness.Record.Proofs.Routines.voters_count_lt_of_committee_majority M F)
          (by rw [hin]; exact (GoldilocksCorrectness.Record.Statements.Executions.pool_committee_of_exec M F) S A x R E ip p (q + 1))
          hMaj)
      (fun u hu => hHold u (Finset.mem_inter.1 hu).1 (Finset.mem_inter.1 hu).2)
      hpCore
      hl hsent
      ⟨Hf u₀, (hHv u₀ hu₀).1, (hHv u₀ hu₀).2.1, (hHf u₀ hu₀).2.2 X hX⟩ haX
  obtain ⟨-, hBslot, hBne, hBpar?, hBparT⟩ := hPE _ hap (ancestorEq_refl _)
  have hPB : B.parent.AncestorEq B := ancestorEq_of_parent? hBpar?
  have hParentChain : ∀ C : Block V, OnHonestChainBefore M S A x s₀ (q + 1) C →
      C.AncestorEq B.parent := by
    intro C hC
    rcases (compatible_iff _ _).1 ((onHonestChainBefore_compatible M F) S A x s₀ (q + 1) C _ hChain
      hC hap) with h | h
    · exact ancestorEq_trans h ((get_anchor_ancestorEq_proposal_parent M F) S A x R E (q + 2) ip B p hl
        hsent)
    · exact (hPE C hC h).1
  -- the proposer holds its proposal
  have hJIT : JustifiedInTree M (x.tickInput p (M.slotStart S.C (q + 2))) :=
    F.nd.nodeInv_justifiedInTree hInvP
  have hBparT' : B.parent ∈ (x.tickInput p (M.slotStart S.C (q + 2))).tree := by
    rcases hBparT with h | h
    · exact (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 (((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_tree_iff M F) _ _ _).1 h).1).1
    · rw [h]; exact (GoldilocksCorrectness.Record.Proofs.Routines.get_anchor_mem_T M F) S.C S.P S.X _ hInvP _
        (F.nd.nodeInv_finalized_mem_tree hInvP) hJIT
  have hFB : (x.tickInput p (M.slotStart S.C (q + 2))).finalized.AncestorEq B :=
    ancestorEq_trans hFρp (ancestorEq_trans (hParentChain _ hρp) hPB)
  have hBp : B ∈ (x.st (ip + 1) p).tree :=
    (GoldilocksCorrectness.Record.Statements.Executions.lem22a_proposer_holds_own_proposal M F U) S A x R
      (q + 1) ip B p E hl hsent hRootNew hBparT' ((compatible_iff _ _).2 (Or.inl hFB))
  have hm1 : hMax M S.C (x.tickInput p (M.slotStart S.C (q + 2))) - 1 ≤
      (M.chainStateOf S.C B.parent).h := by
    rw [← hEh]; exact ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C Eb B.parent).2.2.2.1 (hParentChain Eb hE)
  -- at every honest active validator `w` of slot `q + 2`: its tick `iw` to the vote time of slot `q + 2`
  have hwTick : ∀ w ∈ honestActiveAt M S A x (q + 2),
      w ∈ A.activeThroughoutToTick x (Goldilocks.duty_window_start S.C (q + 2)) (M.voteTime S.C (q + 2)) := by
    intro w hwA
    exact (mem_activeThroughoutToTick_of_inside M F) R E ((honestActiveAt_window M F) S A (q + 2) w E hwA)
      (show 1 ≤ M.voteTime S.C (q + 2) by omega) r7 r8
  have hwFacts : ∀ w ∈ honestActiveAt M S A x (q + 2), ∀ iw : ℕ,
      x.lbl iw = Event.tick w (M.voteTime S.C (q + 2)) →
      x.tickInput w (M.voteTime S.C (q + 2)) = x.st iw w ∧ w ∉ A.corrupted iw ∧
      x.time i₁ < x.time iw ∧ x.time iw + ΔClockAhead < ((M.supportCutoff S.C (q + 1 + 1) : ℕ) : ℝ) ∧
      x.time iw ≤ ((M.voteTime S.C (q + 2) : ℕ) : ℝ) + ΔClockBehind ∧
      ((M.supportCutoff S.C (s₀ + 1) : ℕ) : ℝ) ≤ x.time iw := by
    intro w hwA iw hiw
    obtain ⟨-, hw1, hw2⟩ := E.tick_active iw w _ hiw
    refine ⟨by unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hiw], E.not_mem_corrupted_of_tick hiw,
      by linarith only [hs, hw1, ev2, hSkew, hB0],
      by show _ < ((M.supportCutoff S.C (q + 2) : ℕ) : ℝ); linarith only [hw2, ev2, ec2, hSkew],
      hw2, by linarith only [hw1, ev2, ec1, hc0R, hSkew, hB0]⟩
  have hW : ∀ w ∈ honestActiveAt M S A x (q + 2),
      (M.get_fc_root (x.tickInput w (M.voteTime S.C (q + 2)))).AncestorEq B ∧
      B ∈ (x.tickInput w (M.voteTime S.C (q + 2))).tree := by
    intro w hwA
    obtain ⟨iw, hiw, -⟩ := Activity.mem_activeThroughoutToTick.1 (hwTick w hwA)
    obtain ⟨hinw, hwi, hiwt, hiwc, -, hiw0⟩ := hwFacts w hwA iw hiw
    have hρw : OnHonestChainBefore M S A x s₀ (q + 1) (M.get_fc_root (x.tickInput w (M.voteTime S.C (q + 2)))) := by
      rw [hinw, ← (GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F)]
      exact (lem91f_voter_root_on_chain_before_until M F U Fx) S A x R s₀ iw (q + 1) H w E
        (hRoots iw w _ hiw le_rfl)
        ((hAdvQ iw w _ hiw le_rfl).mono (max_le le_rfl hiw0)) hOld
        (hCaches iw w _ hiw le_rfl iw w ((lt_of_time_lt M) x R hiwt) le_rfl hwi) hwi (hsBefore iw hiwc)
    have hρwB := ancestorEq_trans (hParentChain _ hρw) hPB
    refine ⟨hρwB, ?_⟩
    exact (GoldilocksCorrectness.Record.Statements.Executions.lem22_proposal_held_by_voter M F U) S A x R GST
      (q + 1) ip B p w E hNet hSkew hRedeliver
      (by rw [(tickStep_eq_of_lbl M) x E hiw]; exact hRoots iw w _ hiw le_rfl) hParent hW4
      (Goldilocks.duty_window_start S.C (q + 2)) r9 (hwTick w hwA) hl hsent hBp
      ((compatible_iff _ _).2 (Or.inl (ancestorEq_trans (by
        rw [hinw]
        exact (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F) S A x R E iw w)
        hρwB)))
  refine ⟨hParentChain, hBslot, hBne, hPB, fun w hwA vote hSend => ?_, fun w hwA => (hW w hwA).2⟩
  -- the vote names `B` (Lemma 59 with ordered `head_height_floor` values, per tick)
  obtain ⟨iw, hiw, hsw⟩ := hSend
  obtain ⟨hinw, hwi, hiwt, hiwc, hiwv, hiw0⟩ := hwFacts w hwA iw hiw
  have hφw : M.head_height_floor (x.tickInput w (M.voteTime S.C (q + 2))) =
      hMax M S.C (x.tickInput w (M.voteTime S.C (q + 2))) - 1 := by
    rw [hinw]
    exact ((lem91d_not_contested_until M F U Fx) S A x R s₀ iw (q + 1) H w E
      ((hAdvQ iw w _ hiw le_rfl).mono (max_le le_rfl hiw0)) hChain hOld
      (hCaches iw w _ hiw le_rfl iw w ((lt_of_time_lt M) x R hiwt) le_rfl hwi) hwi (hsBefore iw hiwc)).2
  -- Lemma 91 (e) at the proposer's tick, and `B` in the voter's tree at its tick (F-77-3's route)
  have hHmax : hMax M S.C (x.tickInput p (M.slotStart S.C (q + 2))) ≤
      hMax M S.C (x.tickInput w (M.voteTime S.C (q + 2))) := by
    have he := (lem91e_proposal_height_ge_h_max_at_tick M F U Fx) S A x R s₀ (q + 2) i₁ H ip p B E hRootsP hAdvPm
      hs hChain hOld hCp (hsBefore ip hipc) hl hsent (by rw [hφp]; exact hm1) hParentChain
    exact le_trans he (GoldilocksCorrectness.Record.Statements.Routines.le_hMax M (C := S.C) (hW w hwA).2)
  have hb := (lem91b_voter_head_height_floor_le_parent_until M F U Fx) S A x R s₀ (q + 2) H iw w B.parent E
    ((hAdvQ iw w _ hiw le_rfl).mono (max_le le_rfl hiw0)) hiw
    (fun s_a h => by have := hsBefore iw hiwc s_a h; omega) hChain hOld (hCaches iw w _ hiw le_rfl iw w ((lt_of_time_lt M) x R hiwt) le_rfl hwi)
    (fun C hC => hParentChain C hC)
  exact (GoldilocksCorrectness.Record.Statements.Executions.lem59le_goldfish_vote_names_honest_proposal_frame M F U)
    S A x R GST (q + 1) (honestActiveAt M S A x (q + 1) ∩ S.P.committee (q + 1)) Hf _ B p w vote
    _ _ _ _ E hNet hSkew hRedeliver Sy hΔs
    (by rw [(tickStep_eq_of_lbl M) x E hiw]; exact hRoots iw w _ hiw le_rfl) hParent hOwner hW3
    (fun u hu => ⟨(Finset.mem_inter.1 hu).2,
      by rw [(tickStep_eq_of_lbl M) x E hiw]; exact hHonU u hu iw (by linarith only [hiwc, hA0]),
      (hHf u hu).1, (hHf u hu).2.1, (hHf u hu).2.2 _ hap⟩)
    (fun votes_w support_w hCV => (GoldilocksCorrectness.Record.Proofs.Routines.voters_count_lt_of_committee_majority M F)
      (by rw [hinw] at hCV; exact (countedVotes_committee_st M F) S A x R E iw (q + 1) w votes_w support_w hCV) hMaj)
    (fun u hu => hHold u (Finset.mem_inter.1 hu).1 (Finset.mem_inter.1 hu).2)
    (Goldilocks.duty_window_start S.C (q + 2)) htS
    (Activity.mem_activeThroughoutToTick_of_le hpwdw
      ((mem_activeThroughoutToTick_of_inside M F) R E hp.1 (show 1 ≤ M.slotStart S.C (q + 2) by omega) r5 r6))
    hHoldP (hwTick w hwA) ⟨ip, hl, hsent⟩ ⟨iw, hiw, hsw⟩
    (fun B' hB' hsl => (only_block_of_unforgeability_st M F U) S A x R E (q + 1 + 1) iw B B' p w
      ((not_mem_corrupted_of_le_time M) x R E hp.2 (by linarith only [hiwv, r8, hA0])) rfl ⟨ip, hl, hsent⟩
      (by rw [hinw] at hB'; exact hB') hsl)
    hRootNew ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
    (show M.head_height_floor (x.tickInput p (M.slotStart S.C (q + 2))) ≤
        M.head_height_floor (x.tickInput w (M.voteTime S.C (q + 2))) by rw [hφp, hφw]; exact Nat.sub_le_sub_right hHmax 1)
    ⟨Hf u₀, hHp u₀ hu₀, (hHf u₀ hu₀).2.2 _ hap, (hHf u₀ hu₀).2.2 _ hρp, (hHv u₀ hu₀).2.2⟩
    (ancestorEq_refl _) (hW w hwA).1
    (fun n' sent hrun hA e he hlive => by
      rcases (mem_honestActiveAt_or_lockFree M F U) S A (q + 1) w R E hSkew hwA with h | hsl
      · obtain ⟨D, hD, heD⟩ := hLocks (q + 1) (by omega) le_rfl w h n' sent hrun hA e he hlive
        exact ancestorEq_trans heD (ancestorEq_trans (hParentChain D hD) hPB)
      · exact ((revoke_locks_empty_of_lockFree M F) S A x (M.voteTime S.C (q + 1 + 1)) (q + 1 + 1) _ n'
          (Nat.le_add_left 1 _) hsl
          ((locksRevoked_of_voteTime_outcome M F U) S A x R E (q + 1 + 1) w n' sent hrun hA) e
          he).elim)
    hb

/-- **Steps 2 and 3 of the inclusion: the proposal's parent extends the chain, and every honest
vote names the proposal.** Under the hypotheses of the inclusion at slot `q + 2`, with the lock
invariant at slot `q` (`hLk`) and `B` the proposal of slot `q + 2` with a root new to its proposer:
every block of the chain before `q + 1` is `B`'s parent or an ancestor of it; `B` is a non-genesis
block of slot `q + 2`; every vote an honest active validator `w` of slot `q + 2` sends at the vote
time of slot `q + 2` names `B`; and every such `w` holds `B` before that vote time.

Why: the proposer's root and anchor are on the chain (Lemma 91 (f), `proposer_anchor_on_chain`);
every honest committee member of slot `q + 1` voted for a block extending the chain, which reaches
the proposer as a viable head; so the proposal's parent extends every block of the chain
(`proposal_parent_extends_majority_block`, `get_anchor_ancestorEq_proposal_parent`). Lemma 59 with
ordered `head_height_floor` values (`lem59le_goldfish_vote_names_honest_proposal_frame`) then names `B` in every
honest vote: the forms with `head_height_floor` at the proposer at most `head_height_floor` at the
voter hold by Lemma 91 (c) and (d), and `head_height_floor` at the voter is at most the
parent's height by Lemma 91 (b). Lemmas 22a and 22 deliver `B`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold;
- `q`: the slot of the proposal is `q + 2`; `ip`: the step of the proposer's tick; `B`: the
  proposal.

Roots name blocks up to the real time of each validator's tick to a clock value at most
`M.voteTime S.C (q + 2)`, as in `honest_proposal_extends_chain_until`.

It is `honest_proposal_extends_chain_until` with the caches restricted to the steps it reads.

Read aloud: the honest proposal of slot `q + 2` has a parent that every block of the chain before
`q + 1` is an ancestor of or equal to, and every honest vote of slot `q + 2` names it. -/
theorem honest_proposal_extends_chain (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ anchor i₁ H q ip : ℕ) (B : Block V)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks up to the real time of each validator's tick to a clock value at most the vote time of slot
    -- `q + 2` (the until form's text,)
    (hRoots : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.voteTime S.C (q + 2) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    -- fewer than a quorum in the adversary set up to the real time of each validator's tick to a clock value at most
    -- the vote time of slot `q + 2` (, read as `hRoots`)
    (hAdvQ : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.voteTime S.C (q + 2) →
      A.AdversaryFewerThanQuorumUntil x (quorum V) (x.time k))
    (hSleepK : CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C (q + 2))) (hAnchor : anchor ≤ x.time i₁)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀)
    (hChain : ConfirmationsChain M S A x s₀)
    (hInv : ∀ s : ℕ, s₀ < s →
      ChainInvFor M S A x (honestActiveAt M S A x s) (OnHonestChainBefore M S A x s₀ s) s)
    (hLocks : ∀ s : ℕ, s₀ < s → ∀ u ∈ honestActiveAt M S A x s,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ s) s u)
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x.time i₁ ≤ x.time j → u ∉ A.corrupted j →
      CachesOnChain M S A x s₀ H (x.st j u))
    (ht₀ : M.supportCutoff S.C (s₀ + 1) ≤ x.time i₁)
    (hs₀q : s₀ ≤ q) (hs : x.time i₁ < M.slotStart S.C (q + 2) ∧
      ∀ k : ℕ, x.lbl k = Event.tick (S.P.proposer (q + 2)) (M.slotStart S.C (q + 2)) → x.time i₁ < x.time k)
    (hLk : ∀ u ∈ honestActiveAt M S A x q,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (q + 1)) q u)
    -- the honest voters of slot `q + 1` are active through the sync delay after Lemma 12's read time of slot `q + 1`
    -- ( under)
    (hHold : ∀ u ∈ honestActiveAt M S A x (q + 1), u ∈ S.P.committee (q + 1) →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C (q + 1) - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C (q + 1) - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hp : S.P.proposer (q + 2) ∈ A.activeThroughoutToTick x (Goldilocks.proposal_window_start S.C (q + 2))
        (M.supportCutoff S.C (q + 3)) ∧
      S.P.proposer (q + 2) ∉ A.corruptedAtTime x (M.supportCutoff S.C (q + 3)))
    -- the proposer is active through the sync delay after `M.slotStart S.C (q + 2) - max (Δ S) Δs`
    -- the amended row `hHoldP`,)
    (hHoldP : S.P.proposer (q + 2) ∈ A.activeThroughout x ((M.slotStart S.C (q + 2) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C (q + 2) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hl : x.lbl ip = Event.tick (S.P.proposer (q + 2)) (M.slotStart S.C (q + 2)))
    (hsent : (⟨S.P.proposer (q + 2), NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
      x.sent (ip + 1) - x.sent ip)
    (hRootNew : ∀ B' ∈ (x.tickInput (S.P.proposer (q + 2)) (M.slotStart S.C (q + 2))).tree,
      B'.root ≠ B.root) :
    (∀ C : Block V, OnHonestChainBefore M S A x s₀ (q + 1) C → C.AncestorEq B.parent) ∧
    B.slot = q + 2 ∧ B ≠ Block.genesis ∧ B.parent.AncestorEq B ∧
    (∀ w ∈ honestActiveAt M S A x (q + 2), ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick w (M.voteTime S.C (q + 2)) ∧
        (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x.sent (i + 1) - x.sent i) → vote.head = B.root) ∧
    (∀ w ∈ honestActiveAt M S A x (q + 2), B ∈ (x.tickInput w (M.voteTime S.C (q + 2))).tree)
      := by
  exact (honest_proposal_extends_chain_until M F U Fx) S A x R GST s₀ anchor i₁ H q ip B E hNet hSkew hRedeliver Sy hΔs
    hRoots hParent hAdvQ hSleepK hAnchor hGST (confirmationsChainBefore_of_chain M S A x s₀ (q + 1) hChain)
    (fun s h1 _ => hInv s h1) (fun s h1 _ => hLocks s h1) hOld
    (fun _ _ _ _ _ j u h₁ _ h₂ => hCaches j u ((time_mono M) x R h₁.le) h₂) ht₀ hs₀q hs.1
    (hs.2 ip hl) hLk hHold hp hHoldP hl hsent hRootNew

/-! ## Steps 4 and 5: the update of the proposal's slot -/

/-- **Kit fact, an updater's fork-choice root at its update.** At `v`'s tick to the support cutoff of
slot `s + 1`, the root of `v`'s fork choice is on the honest chain before `s`, or it is an ancestor
of, or equal to, the confirmation of slot `s` that an updater `u` of slot `s` saved at its own tick to
that cutoff, a step before `v`'s (F-78-1, route (a)).

Why: the root is `v`'s justified block `J` or its finalized block, an ancestor of `J` (the caches).
`J`'s certificate names an entry that an honest attester `uₐ` held at its tick to the support cutoff
of a slot `sₐ`, a step before `v`'s tick, and that entry is `uₐ`'s own saved confirmation of `sₐ` or
an ancestor of it (`cert_entry_at_slot_saved`); roots name blocks, so the entry is `J`. When
`sₐ < s` the root is on the chain before `s`; when `sₐ = s`, `uₐ` is the updater `u`; `sₐ > s` is
impossible, since a tick to a later support cutoff is at a real time after `v`'s tick (`hSkew`). It is
the route of `updaterFrame_after_handover_until` (`HealedChainBefore.lean`), read on the root.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `A`, `x`, `R`, `E`: the setup, the activity, the execution, its run facts, its environment
  facts; `s₀`: the healed slot; `i₂`: the step from which the caches are on the chain; `H`: the
  threshold; `s`: the slot; `v`: the updater.

Read aloud: an updater's fork-choice root at its update of slot `s` is on the honest chain before
`s`, or on the confirmation of slot `s` that another updater saved at an earlier tick. -/
theorem updater_root_on_chain_or_earlier (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ H s : ℕ) (v : V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C (s + 1)))))
    -- fewer than a quorum of validators have been in the adversary set up to the later of the real time of `v`'s
    -- tick to `M.supportCutoff S.C (s + 1)` and the hand-over cutoff
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max (x.time (x.tickStep v (M.supportCutoff S.C (s + 1)))) (M.supportCutoff S.C (s₀ + 1))))
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    -- `v`'s caches at its tick to the support cutoff of slot `s + 1` are on the chain (, the one step read)
    (hCaches : CachesOnChain M S A x s₀ H (x.tickInput v (M.supportCutoff S.C (s + 1))))
    (hv : v ∈ updaterAt M S A x s) :
    OnHonestChainBefore M S A x s₀ s (M.get_fc_root (x.tickInput v (M.supportCutoff S.C (s + 1)))) ∨
      ∃ u ∈ updaterAt M S A x s,
        x.tickStep u (M.supportCutoff S.C (s + 1)) < x.tickStep v (M.supportCutoff S.C (s + 1)) ∧
        ∃ C : Block V, (x.tickOutput u (M.supportCutoff S.C (s + 1))).savedConfirmation s = some C ∧
          (M.get_fc_root (x.tickInput v (M.supportCutoff S.C (s + 1)))).AncestorEq C := by
  -- `v`'s tick to the support cutoff of slot `s + 1`
  have hv' := hv
  unfold updaterAt at hv'
  obtain ⟨k', hk', -⟩ := (Activity.mem_activeThroughoutToTick).1 hv'
  have hts : x.tickStep v (M.supportCutoff S.C (s + 1)) = k' := (tickStep_eq_of_lbl M) x E hk'
  have hin : x.tickInput v (M.supportCutoff S.C (s + 1)) = x.st k' v := by
    unfold Trace.tickInput; rw [hts]
  rw [hin, hts]
  rw [hin] at hCaches
  rw [hts] at hRoots hAdvQ
  have hvk : v ∉ A.corrupted k' := E.not_mem_corrupted_of_tick hk'
  -- the certificate of `v`'s justified block names an entry an honest attester held at its tick
  obtain ⟨⟨D, hD, hJD, hhjD⟩, -, -⟩ := (cachesWitnessed_of_exec M F) S A x R E k' v
  obtain ⟨hH, -, -, -, hFJ⟩ := hCaches
  have h1 : 1 ≤ (M.chainStateOf S.C D).h_j := by
    rw [← hhjD]; exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le H) hH)
  obtain ⟨hJC, -, -⟩ := ((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) S.C D).1 h1
  rw [← hJD, ← hhjD] at hJC
  obtain ⟨s_a, uₐ, Eb, hk, hl, hua, -, hEb, hs₀a, -, -, hEr, C_a, hSa, hEbC⟩ :=
    (cert_entry_at_slot_saved M F U Fx) S A x R s₀ H k' v D _ _ E
      (hAdvQ.mono le_rfl) hOld hD ((progressCertOn_of_justificationCertOn M F) hJC) hH
  -- the entry and `J` have one root, and honest validators hold both
  have hJmem : (x.st k' v).justified ∈ (x.st k' v).tree :=
    (F.nd.nodeInv_justifiedInTree (lem11_node_invariant M F S A x R E k' v hvk).1)
  have hEJ : Eb = (x.st k' v).justified :=
    hRoots Eb _ ((onHonestChainAt_inHonestTreeBy M F U) S A x R E _ uₐ (M.supportCutoff S.C (s_a + 1)) _ Eb hl
      ((time_mono M) x R hk.le) hEb)
      ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := k') (v := v) hvk le_rfl hJmem) hEr.symm
  -- the root is the justified block or the finalized block, an ancestor of the attester's confirmation
  have hRC : (M.get_fc_root (x.st k' v)).AncestorEq C_a := by
    rcases (GoldilocksCorrectness.Record.Proofs.Routines.get_fc_root_cases M F) S.C S.P S.X _
        (lem11_node_invariant M F S A x R E k' v hvk).1 with h | h
    · rw [h, ← hEJ]; exact hEbC
    · rw [h]; rw [← hEJ] at hFJ; exact ancestorEq_trans hFJ hEbC
  rcases Nat.lt_trichotomy s_a s with hlt | heq | hgt
  · -- the entry's slot is before `s`: the root is on the chain before `s`
    exact Or.inl ⟨s_a, hlt, hs₀a, uₐ, hua, C_a, hSa, hRC⟩
  · -- the entry's slot is `s`: the attester is an updater of slot `s` that ticked before `v`
    subst heq
    exact Or.inr ⟨uₐ, hua, hk, C_a, hSa, hRC⟩
  · -- a tick to a later support cutoff is at a real time after `v`'s tick
    exfalso
    have h₁ := (E.tick_active _ _ _ hl).2.1
    have h₂ := (E.tick_active _ _ _ hk').2.2
    have h₃ := (time_mono M) x R hk.le
    have hA := E.ahead_nonneg
    have hmono := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
      (show s + 1 + 1 ≤ s_a + 1 by omega)
    have hc := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_succ_eq M.toSlotLayout F.sched U) S (s + 1)
    have hcR : ((M.supportCutoff S.C (s + 1 + 1) : ℕ) : ℝ) = (M.supportCutoff S.C (s + 1) : ℕ) + 4 * Δ S := by
      rw [hc]; push_cast; ring
    have hmR : ((M.supportCutoff S.C (s + 1 + 1) : ℕ) : ℝ) ≤ (M.supportCutoff S.C (s_a + 1) : ℕ) := by
      exact_mod_cast hmono
    have hΔ : (1 : ℝ) ≤ Δ S := by exact_mod_cast GoldilocksCorrectness.Proofs.Routines.one_le_Δ S
    linarith

open Classical in
/-- An updater of slot `s` outside the adversary set after every step whose time is at most the support
cutoff of slot `s + 1`, and at every step at which a validator outside it ticks to that cutoff, is an
honest active validator of slot `s`, or holds, before the vote time of slot `s + 1`, no lock entry live
there.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `A`: the activity; `x`, `R`, `E`, `hWS`: the execution, its facts, its wake shape;
  `s`: the slot; `v`: the validator.

Read aloud: an updater of slot `s` honest at its support cutoff is an honest active validator of slot
`s` or holds no live lock at the vote time of slot `s + 1`. -/
theorem updater_active_or_lockFree (U : UniformSchedule M.toSlotLayout) (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
 (s : ℕ) (v : V) (hv : v ∈ updaterAt M S A x s)
    (hc : v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) ∪ Finset.univ.filter (fun u => ∃ (k : ℕ) (w : V),
      x.lbl k = Event.tick w (M.supportCutoff S.C (s + 1)) ∧ w ∉ A.corrupted k ∧ u ∈ A.corrupted k)) :
    v ∈ honestActiveAt M S A x s ∨
      ∀ e ∈ (x.tickInput v (M.voteTime S.C (s + 1))).lockEntries,
        M.is_live (x.tickInput v (M.voteTime S.C (s + 1))) ((M.voteTime S.C (s + 1) : ℕ) : Int) e = false :=
  ((mem_activeAt_or_lockFree M F U) S A x R s v E hv).imp
    (fun h => Finset.mem_sdiff.2 ⟨h, hc⟩) id

open Classical in
/-- **Step 4 of the inclusion, at the updaters ticking no later than one updater `v₀`.** The facts of
`honest_proposal_saved_of_locks_until` that do not read the live locks, from its hypotheses with the rows
(roots, the adversary bound, the caches) read up to the real time of `v₀`'s tick to the support cutoff of slot
`q + 3` only: every block of the chain before `q + 2` is `B` or an ancestor of `B`; `B` is a non-genesis block of
slot `q + 2`; some block is on the chain before `q + 2`; every honest vote of slot `q + 2` names `B` and every
honest active validator of slot `q + 2` holds `B` at its vote; and every updater of slot `q + 2` whose tick to the
support cutoff of slot `q + 3` is no later than `v₀`'s has its root on `B`'s chain, saves `B`, makes it fast,
locks it, and has its finalized block on its root's chain.

Why: as `honest_proposal_saved_of_locks_until`. The rows the proposal's step reads are read at ticks to a clock
value at most the support cutoff of slot `q + 2`, before `v₀`'s tick; the strong induction on the updaters' tick
steps reads, at each updater, the rows up to its own tick, no later than `v₀`'s, and calls the induction
hypothesis only at earlier ticks.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `A`, `x`, `R`, `E`: the setup, the activity, the execution, its run facts, its environment facts;
  `GST`: the time from which the network is synchronous; `s₀`: the healed slot; `anchor`: the time from
  which committee sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold;
- `q`: the slot of the proposal is `q + 2`; `ip`: the step of the proposer's tick; `B`: the proposal;
  `v₀`: the updater whose tick bounds the rows.

Read aloud: with the rows read up to the tick of one updater `v₀` of slot `q + 2`, every updater of slot `q + 2`
that ticks to the support cutoff of slot `q + 3` no later than `v₀` saves the honest proposal of slot `q + 2`, fast
and locked. -/
theorem honest_proposal_saved_at_until (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ anchor i₁ H q ip : ℕ) (B : Block V) (v₀ : V)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- `v₀` is an updater of slot `q + 2`; the rows are read up to the real time of its tick to the support cutoff of slot `q + 3`
    (hv₀ : v₀ ∈ updaterAt M S A x (q + 2))
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep v₀ (M.supportCutoff S.C (q + 2 + 1)))))
    (hParent : ParentHeldAtDelivery M x)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (x.time (x.tickStep v₀ (M.supportCutoff S.C (q + 2 + 1)))))
    (hSleepK : CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C (q + 2 + 1))) (hAnchor : anchor ≤ x.time i₁)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀)
    (hChain : ConfirmationsChainBefore M S A x s₀ (q + 1))
    (hInv : ∀ s : ℕ, s₀ < s → s ≤ q + 2 →
      ChainInvFor M S A x (honestActiveAt M S A x s) (OnHonestChainBefore M S A x s₀ s) s)
    (hLocks : ∀ s : ℕ, s₀ < s → s ≤ q + 2 → ∀ u ∈ honestActiveAt M S A x s,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ s) s u)
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), i₁ < j → x.time j ≤ x.time (x.tickStep v₀ (M.supportCutoff S.C (q + 2 + 1))) →
      u ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j u))
    (ht₀ : M.supportCutoff S.C (s₀ + 1) ≤ x.time i₁)
    (hs₀q : s₀ ≤ q) (hs : x.time i₁ < M.slotStart S.C (q + 2) ∧
      ∀ k : ℕ, x.lbl k = Event.tick (S.P.proposer (q + 2)) (M.slotStart S.C (q + 2)) → x.time i₁ < x.time k)
    (hLk : ∀ u ∈ honestActiveAt M S A x q,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (q + 1)) q u)
    -- the honest voters of slots `q + 1` and `q + 2` are active through the sync delay after Lemma 12's read time of
    -- their slot ( under: Lemma 59 at slot `q + 1`, Lemma 27 at slot `q + 2`)
    (hHold : ∀ s' : ℕ, q + 1 ≤ s' → s' ≤ q + 2 → ∀ u ∈ honestActiveAt M S A x s', u ∈ S.P.committee s' →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hp : S.P.proposer (q + 2) ∈ A.activeThroughoutToTick x (Goldilocks.proposal_window_start S.C (q + 2))
        (M.supportCutoff S.C (q + 3)) ∧
      S.P.proposer (q + 2) ∉ A.corruptedAtTime x (M.supportCutoff S.C (q + 3)))
    -- the proposer is active through the sync delay after `M.slotStart S.C (q + 2) - max (Δ S) Δs`
    -- the amended row `hHoldP`,)
    (hHoldP : S.P.proposer (q + 2) ∈ A.activeThroughout x ((M.slotStart S.C (q + 2) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C (q + 2) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hl : x.lbl ip = Event.tick (S.P.proposer (q + 2)) (M.slotStart S.C (q + 2)))
    (hsent : (⟨S.P.proposer (q + 2), NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
      x.sent (ip + 1) - x.sent ip)
    (hRootNew : ∀ B' ∈ (x.tickInput (S.P.proposer (q + 2)) (M.slotStart S.C (q + 2))).tree,
      B'.root ≠ B.root) :
    (∀ C : Block V, OnHonestChainBefore M S A x s₀ (q + 2) C → C.AncestorEq B) ∧
    B.slot = q + 2 ∧ B ≠ Block.genesis ∧
    (∃ C₀ : Block V, OnHonestChainBefore M S A x s₀ (q + 2) C₀) ∧
    (∀ w ∈ honestActiveAt M S A x (q + 2), ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick w (M.voteTime S.C (q + 2)) ∧
        (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x.sent (i + 1) - x.sent i) → vote.head = B.root) ∧
    (∀ w ∈ honestActiveAt M S A x (q + 2), B ∈ (x.tickInput w (M.voteTime S.C (q + 2))).tree) ∧
    (∀ v ∈ updaterAt M S A x (q + 2),
      x.tickStep v (M.supportCutoff S.C (q + 2 + 1)) ≤ x.tickStep v₀ (M.supportCutoff S.C (q + 2 + 1)) →
      ((M.get_fc_root (x.tickInput v (M.supportCutoff S.C (q + 2 + 1)))).AncestorEq B ∧
        (x.tickOutput v (M.supportCutoff S.C (q + 2 + 1))).savedConfirmation (q + 2) = some B ∧
        B ∈ (x.tickOutput v (M.supportCutoff S.C (q + 2 + 1))).fastBlocks ∧
        (∃ e ∈ (x.tickOutput v (M.supportCutoff S.C (q + 2 + 1))).lockEntries, M.le_B e = B ∧
          M.le_d e = (S.C.t_ (q + 2 + S.C.k) + 5 * S.C.Δ))) ∧
      (x.tickInput v (M.supportCutoff S.C (q + 2 + 1))).finalized.AncestorEq
        (M.get_fc_root (x.tickInput v (M.supportCutoff S.C (q + 2 + 1))))) := by
  have hΔ := one_le_Δ S
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔR : (1 : ℝ) ≤ (Δ S : ℝ) := by exact_mod_cast hΔ
  have hsR : ∀ s' : ℕ, ((M.slotStart S.C s' : ℕ) : ℝ) = 4 * (Δ S : ℝ) * (s' : ℝ) := fun s' => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s']; push_cast; ring
  have hvR : ∀ s' : ℕ, ((M.voteTime S.C s' : ℕ) : ℝ) = 4 * (Δ S : ℝ) * (s' : ℝ) + Δ S := fun s' => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s',
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s']; push_cast; ring
  have hcR : ∀ s' : ℕ, ((M.supportCutoff S.C s' : ℕ) : ℝ) = 4 * (Δ S : ℝ) * (s' : ℝ) + 2 * Δ S := fun s' => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s',
      (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s',
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s']; push_cast; ring
  have hvc : M.voteTime S.C (q + 2) ≤ M.supportCutoff S.C (q + 2) := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (q + 2)]; omega
  have hcc : M.supportCutoff S.C (q + 2) ≤ M.supportCutoff S.C (q + 2 + 1) :=
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)
  -- the times: every tick to the support cutoff of slot `q + 3` is after the phase's end, and after every tick to a
  -- clock value at most the support cutoff of slot `q + 2` (the cutoffs are `4 Δ S` apart, `hSkew`)
  have hearly : ∀ (k : ℕ) (u : V), x.lbl k = Event.tick u (M.supportCutoff S.C (q + 2 + 1)) →
      x.time i₁ < x.time k := by
    intro k u hk
    have h1 := (E.tick_active _ _ _ hk).2.1
    have h0 := hs.1
    rw [hcR] at h1
    rw [hsR] at h0
    push_cast at h1 h0
    linarith
  have hlate : ∀ (k j : ℕ) (u w : V) (c : ℕ), x.lbl k = Event.tick u (M.supportCutoff S.C (q + 2 + 1)) →
      x.lbl j = Event.tick w c → c ≤ M.supportCutoff S.C (q + 2) → x.time j ≤ x.time k := by
    intro k j u w c hk hj hc
    have h1 := (E.tick_active _ _ _ hk).2.1
    have h2 := (E.tick_active _ _ _ hj).2.2
    have hc' : (c : ℝ) ≤ ((M.supportCutoff S.C (q + 2) : ℕ) : ℝ) := by exact_mod_cast hc
    rw [hcR] at h1 hc'
    push_cast at h1 hc'
    linarith
  -- an honest active member `w₀` of the slot-`q + 2` committee (Lemma 88)
  have hanc0 : anchor < M.slotStart S.C (q + 2) := by exact_mod_cast lt_of_le_of_lt hAnchor hs.1
  have hanc : anchor ≤ M.slotStart S.C (q + 2 + 1) :=
    le_trans hanc0.le ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (by omega))
  have h88 := (lem88_counting_of_committeeSleepiness M F) S A x R E anchor (q + 2) (S.P.proposer (q + 2)) 0
    hSleepK hanc le_rfl
  have h88c := h88.1
  set Hs := honestActiveAt M S A x (q + 2) ∩ S.P.committee (q + 2) with hHsdef
  obtain ⟨w₀, hw₀⟩ : Hs.Nonempty := Finset.card_pos.1 (show 0 < Hs.card by omega)
  have hw₀A := (Finset.mem_inter.1 hw₀).1
  have hw₀C := (Finset.mem_inter.1 hw₀).2
  -- the rows at `v₀`'s tick `k₀` to the support cutoff of slot `q + 3`, after every tick to a clock value at most
  -- the support cutoff of slot `q + 2` (`hlate`)
  obtain ⟨k₀, hk₀, -⟩ := Activity.mem_activeThroughoutToTick.1 hv₀
  have hk₀s : x.tickStep v₀ (M.supportCutoff S.C (q + 2 + 1)) = k₀ := (tickStep_eq_of_lbl M) x E hk₀
  have hR₀ := hRoots
  have hAdv₀ := hAdvQ
  have hCa₀ := hCaches
  rw [hk₀s] at hR₀ hAdv₀ hCa₀
  have hi₁k₀ := (hearly k₀ v₀ hk₀).le
  -- step 1: the proposal (`honest_proposal_extends_chain_until`), its rows read up to `v₀`'s tick
  obtain ⟨-, hBslot, hBne, -, hVote, hBw⟩ := (honest_proposal_extends_chain_until M F U Fx) S A x R GST s₀ anchor
    i₁ H q ip B E hNet hSkew hRedeliver Sy hΔs
    (fun k u c hk hc => (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M)
      (hlate k₀ k v₀ u c hk₀ hk (le_trans hc hvc)) hR₀)
    hParent (fun k u c hk hc => hAdv₀.mono (hlate k₀ k v₀ u c hk₀ hk (le_trans hc hvc)))
    ((GoldilocksCorrectness.Record.Statements.Executions.CommitteeSleepinessUntil.mono M) hSleepK hcc) hAnchor hGST
    hChain (fun s h₁ _ => hInv s h₁ (by omega)) (fun s h₁ _ => hLocks s h₁ (by omega)) hOld
    (fun k w c hk hc j u h₁ h₂ h₃ => hCa₀ j u h₁ (le_trans h₂ (hlate k₀ k v₀ w c hk₀ hk (le_trans hc hvc))) h₃)
    ht₀ hs₀q hs.1 (hs.2 ip hl) hLk (fun u hu hc => hHold (q + 1) le_rfl (by omega) u hu hc) hp hHoldP hl hsent
    hRootNew
  -- `w₀`'s vote of slot `q + 2`, at its tick `kV`
  obtain ⟨kV, vote₀, hlV, -, -, hsV⟩ := (honest_active_votes M F U) S A x R (q + 2) w₀ E hSkew hw₀A hw₀C
  have hw₀kV : w₀ ∉ A.corrupted kV := E.not_mem_corrupted_of_tick hlV
  have hVk₀ : x.time kV ≤ x.time k₀ := hlate k₀ kV v₀ w₀ _ hk₀ hlV hvc
  have hi₁kV : x.time i₁ < x.time kV := by
    have h1 := (E.tick_active _ _ _ hlV).2.1
    have h0 := hs.1
    rw [hvR] at h1
    rw [hsR] at h0
    linarith
  -- a block of the chain before `q + 2`: the root at `w₀`'s vote tick (Lemma 91 (f))
  have hC₀ := (lem91f_voter_root_on_chain_before_until M F U Fx) S A x R s₀ kV (q + 2) H w₀ E
    ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) hVk₀ hR₀)
    (hAdv₀.mono (max_le hVk₀ (le_trans ht₀ hi₁k₀))) hOld
    (hCa₀ kV w₀ ((lt_of_time_lt M) x R hi₁kV) hVk₀ hw₀kV) hw₀kV (by
      rintro s_a ⟨k, u, hk, hlk⟩
      by_contra hge
      have h1 := (E.tick_active _ _ _ hlk).2.1
      have h2 := (time_mono M) x R hk.le
      have h3 := (E.tick_active _ _ _ hlV).2.2
      have hmono := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
        (show q + 2 + 1 ≤ s_a + 1 by omega)
      have hmR : ((M.supportCutoff S.C (q + 2 + 1) : ℕ) : ℝ) ≤ (M.supportCutoff S.C (s_a + 1) : ℕ) := by
        exact_mod_cast hmono
      rw [hcR] at hmR
      rw [hvR] at h3
      push_cast at hmR h3
      linarith)
  -- the honest votes of slot `q + 2` are for `B`, and every block of the chain before `q + 2` is an ancestor of `B`
  have hRootH : ∀ u ∈ honestActiveAt M S A x (q + 2), ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (q + 2)) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) →
      ∀ H' : Block V, vote = GoldfishVote.mk u (q + 2) H'.root → H'.root = B.root := by
    intro u hu vote hsend H' heq
    have h1 := hVote u hu vote hsend
    rw [heq] at h1
    exact h1
  have hChainLeB : ∀ C : Block V, OnHonestChainBefore M S A x s₀ (q + 2) C → C.AncestorEq B := by
    intro C hC
    obtain ⟨H', hH'T, heq, hCH'⟩ := (hInv (q + 2) (by omega) le_rfl C hC).1 w₀ hw₀A vote₀ ⟨kV, hlV, hsV⟩
    have hroot := hRootH w₀ hw₀A vote₀ ⟨kV, hlV, hsV⟩ H' heq
    have hkVs : x.tickInput w₀ (M.voteTime S.C (q + 2)) = x.st kV w₀ := by
      unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hlV]
    have hT := hH'T
    have hBT := hBw w₀ hw₀A
    rw [hkVs] at hT hBT
    have hHB : H' = B :=
      F.nd.nodeInv_rootsNameBlocksIn (lem11_node_invariant M F S A x R E kV w₀ hw₀kV).1 _ hT _ hBT hroot
    rw [← hHB]
    exact hCH'
  -- the voters' facts Lemma 18 reads, at every updater's tick
  have hHsv : ∀ v ∈ updaterAt M S A x (q + 2), ∀ u ∈ Hs, u ∈ S.P.committee (q + 2) ∧
      u ∉ A.corrupted (x.tickStep v (M.supportCutoff S.C (q + 2 + 1))) ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (q + 2)) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u (q + 2) B.root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      B ∈ (x.tickInput u (M.voteTime S.C (q + 2))).tree := by
    intro v hv u hu
    have huA := (Finset.mem_inter.1 hu).1
    have huC := (Finset.mem_inter.1 hu).2
    obtain ⟨kv, hkv, -⟩ := Activity.mem_activeThroughoutToTick.1 hv
    refine ⟨huC, ?_, ?_, hBw u huA⟩
    · intro h
      rw [(tickStep_eq_of_lbl M) x E hkv] at h
      exact (Finset.mem_sdiff.1 huA).2 (Finset.mem_union_right _
        (Finset.mem_filter.2 ⟨Finset.mem_univ _, kv, v, hkv, E.not_mem_corrupted_of_tick hkv, h⟩))
    · obtain ⟨i, vote, hli, hvi, hvs, hsi⟩ := (honest_active_votes M F U) S A x R (q + 2) u E hSkew huA huC
      have hh := hVote u huA vote ⟨i, hli, hsi⟩
      have hvote : vote = GoldfishVote.mk u (q + 2) B.root := by
        obtain ⟨a, b, c⟩ := vote
        dsimp only at hvi hvs hh
        rw [hvi, hvs, hh]
      rw [hvote] at hsi
      exact ⟨i, hli, hsi⟩
  have hHoldHs : ∀ u ∈ Hs, u ∈ A.activeThroughout x ((M.supportCutoff S.C (q + 2) - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (q + 2) - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs) := fun u hu =>
    hHold (q + 2) (by omega) le_rfl u (Finset.mem_inter.1 hu).1 (Finset.mem_inter.1 hu).2
  have hMaj : (S.P.committee (q + 2) \ Hs).card < Hs.card := by
    have hcd := Finset.card_sdiff_add_card_eq_card (show Hs ⊆ S.P.committee (q + 2) from Finset.inter_subset_right)
    omega
  have hGST2 : GST + max (Δ S) Δs ≤ M.supportCutoff S.C (q + 2) :=
    le_trans hGST ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
      (show s₀ ≤ q + 2 by omega))
  -- the finalized block at an updater's tick is the root or an ancestor of it (the caches)
  have hFin : ∀ v ∈ updaterAt M S A x (q + 2), x.tickStep v (M.supportCutoff S.C (q + 2 + 1)) ≤ k₀ →
      (x.tickInput v (M.supportCutoff S.C (q + 2 + 1))).finalized.AncestorEq
        (M.get_fc_root (x.tickInput v (M.supportCutoff S.C (q + 2 + 1)))) := by
    intro v hv hle
    obtain ⟨kv, hkv, -⟩ := Activity.mem_activeThroughoutToTick.1 hv
    have hkvs : x.tickStep v (M.supportCutoff S.C (q + 2 + 1)) = kv := (tickStep_eq_of_lbl M) x E hkv
    have hvk : v ∉ A.corrupted kv := E.not_mem_corrupted_of_tick hkv
    obtain ⟨-, -, -, -, hFJ⟩ := hCa₀ kv v ((lt_of_time_lt M) x R (hearly kv v hkv)) ((time_mono M) x R (hkvs ▸ hle)) hvk
    have hin : x.tickInput v (M.supportCutoff S.C (q + 2 + 1)) = x.st kv v := by
      unfold Trace.tickInput; rw [hkvs]
    rw [hin]
    rcases (GoldilocksCorrectness.Record.Proofs.Routines.get_fc_root_cases M F) S.C S.P S.X _
        (lem11_node_invariant M F S A x R E kv v hvk).1 with h | h
    · rw [h]; exact hFJ
    · rw [h]; exact ancestorEq_refl _
  -- step 2, by strong induction on the updaters' tick steps to the support cutoff of slot `q + 3`: each updater's
  -- root is on `B`'s chain (`updater_root_on_chain_or_earlier`: on the chain before `q + 2`, or on an earlier
  -- updater's confirmation, which is `B`), so its finalized block is too, and its update saves `B`, makes it fast
  -- and locks it (Lemma 18, the honest committee members of slot `q + 2` a majority of it, Lemma 88)
  have hMain : ∀ n : ℕ, ∀ v ∈ updaterAt M S A x (q + 2), x.tickStep v (M.supportCutoff S.C (q + 2 + 1)) = n → n ≤ k₀ →
      (M.get_fc_root (x.tickInput v (M.supportCutoff S.C (q + 2 + 1)))).AncestorEq B ∧
      (x.tickOutput v (M.supportCutoff S.C (q + 2 + 1))).savedConfirmation (q + 2) = some B ∧
      B ∈ (x.tickOutput v (M.supportCutoff S.C (q + 2 + 1))).fastBlocks ∧
      (∃ e ∈ (x.tickOutput v (M.supportCutoff S.C (q + 2 + 1))).lockEntries, M.le_B e = B ∧
        M.le_d e = (S.C.t_ (q + 2 + S.C.k) + 5 * S.C.Δ)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro v hv hn hnk
    have htm : x.time (x.tickStep v (M.supportCutoff S.C (q + 2 + 1))) ≤ x.time k₀ :=
      (time_mono M) x R (hn ▸ hnk)
    obtain ⟨kv, hkv, -⟩ := Activity.mem_activeThroughoutToTick.1 hv
    have hkvs : x.tickStep v (M.supportCutoff S.C (q + 2 + 1)) = kv := (tickStep_eq_of_lbl M) x E hkv
    have hvkv : v ∉ A.corrupted kv := E.not_mem_corrupted_of_tick hkv
    have hRootB : (M.get_fc_root (x.tickInput v (M.supportCutoff S.C (q + 2 + 1)))).AncestorEq B := by
      rcases (updater_root_on_chain_or_earlier M F U Fx) S A x R s₀ H (q + 2) v E hSkew
          ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) htm hR₀)
          (hAdv₀.mono (max_le htm (le_trans ht₀ hi₁k₀))) hOld
          (by unfold Trace.tickInput; rw [hkvs]
              exact hCa₀ kv v ((lt_of_time_lt M) x R (hearly kv v hkv)) (hkvs ▸ htm) hvkv) hv with
        h | ⟨u, hu, hlt, C, hC, hrC⟩
      · exact hChainLeB _ h
      · rw [hn] at hlt
        rw [(ih _ hlt u hu rfl (by omega)).2.1] at hC
        cases hC
        exact hrC
    have hR18 : RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C (q + 2)))) := by
      refine (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) ?_
        ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) htm hR₀)
      have h1 := (time_tickStep_le_add_behind M F) x R E v (M.supportCutoff S.C (q + 2))
      have h2 := (E.time_tickStep ⟨kv, hkv⟩).1
      rw [hcR] at h1 h2
      push_cast at h1 h2
      linarith
    have h18 := (GoldilocksCorrectness.Record.Statements.Executions.lem18_update_confirmation_confirms_majority_block
      M F U) S A x R GST (q + 2) Hs B v E hNet hSkew hRedeliver Sy hΔs hR18 hParent
      ((votesCastByOwner_of_unforgeability M F) S A x R E) hGST2 (hHsv v hv) hHoldHs hMaj hBne hv
      (ancestorEq_trans (hFin v hv (hn ▸ hnk)) hRootB)
    exact ⟨hRootB, h18.1, h18.2.1, h18.2.2.1⟩
  refine ⟨hChainLeB, hBslot, hBne, ⟨_, hC₀⟩, hVote, hBw, fun v hv hle => ?_⟩
  rw [hk₀s] at hle
  exact ⟨hMain _ v hv rfl hle, hFin v hv hle⟩

open Classical in
/-- **Step 4 of the inclusion, with the live locks of every updater.** The conclusion of
`honest_proposal_saved_until`, from its hypotheses with `hLocksU`: every
updater of slot `q + 2` outside `honestActiveAt M S A x (q + 2)` keeps its live locks, after its revocation
of slot `q + 3`, on the chain before `q + 2` (`hLocks` gives it at the honest active validators).

Why: `honest_proposal_extends_chain_until` names `B` in every honest vote of slot `q + 2`, its rows read up to
the tick of an honest active committee member `w₀` (Lemma 88) to the support cutoff of slot `q + 3`, which is
after every tick to a clock value at most the support cutoff of slot `q + 2`. The chain before `q + 2` is on
`B`'s chain (`hInv` at `w₀`'s vote, whose block is `B`, roots naming blocks in `w₀`'s tree). By strong
induction on the updaters' tick steps to the support cutoff of slot `q + 3`: an updater's fork-choice root is on
the chain before `q + 2` or on the confirmation of slot `q + 2` an earlier updater saved
(`updater_root_on_chain_or_earlier`), which is `B` by induction; its finalized block is an ancestor of the root
(the caches); so Lemma 18, the honest active committee members of slot `q + 2` a majority of the committee,
saves `B`, makes it fast and locks it. The live locks are on the chain before `q + 2`, so on `B`'s chain.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `A`, `x`, `R`, `E`: the setup, the activity, the execution, its run facts, its environment facts;
  `GST`: the time from which the network is synchronous; `s₀`: the healed slot; `anchor`: the time from
  which committee sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold;
- `q`: the slot of the proposal is `q + 2`; `ip`: the step of the proposer's tick; `B`: the proposal.

Read aloud: when the updaters of slot `q + 2` that are not honest active validators keep their live locks on
the chain before `q + 2`, every updater of slot `q + 2` saves the honest proposal of slot `q + 2`, fast and
locked. -/
theorem honest_proposal_saved_of_locks_until (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ anchor i₁ H q ip : ℕ) (B : Block V)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : ∀ v ∈ updaterAt M S A x (q + 2), RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C (q + 2 + 1)))))
    (hParent : ParentHeldAtDelivery M x)
    (hAdvQ : ∀ v ∈ updaterAt M S A x (q + 2), A.AdversaryFewerThanQuorumUntil x (quorum V) (x.time (x.tickStep v (M.supportCutoff S.C (q + 2 + 1)))))
    (hSleepK : CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C (q + 2 + 1))) (hAnchor : anchor ≤ x.time i₁)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀)
    (hChain : ConfirmationsChainBefore M S A x s₀ (q + 1))
    (hInv : ∀ s : ℕ, s₀ < s → s ≤ q + 2 →
      ChainInvFor M S A x (honestActiveAt M S A x s) (OnHonestChainBefore M S A x s₀ s) s)
    (hLocks : ∀ s : ℕ, s₀ < s → s ≤ q + 2 → ∀ u ∈ honestActiveAt M S A x s,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ s) s u)
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hCaches : ∀ v ∈ updaterAt M S A x (q + 2), ∀ (j : ℕ) (u : V), x.time i₁ ≤ x.time j → x.time j ≤ x.time (x.tickStep v (M.supportCutoff S.C (q + 2 + 1))) →
      u ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j u))
    (ht₀ : M.supportCutoff S.C (s₀ + 1) ≤ x.time i₁)
    (hs₀q : s₀ ≤ q) (hs : x.time i₁ < M.slotStart S.C (q + 2) ∧
      ∀ k : ℕ, x.lbl k = Event.tick (S.P.proposer (q + 2)) (M.slotStart S.C (q + 2)) → x.time i₁ < x.time k)
    (hLk : ∀ u ∈ honestActiveAt M S A x q,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (q + 1)) q u)
    -- every updater of slot `q + 2` outside `honestActiveAt` keeps its live locks, after its revocation of slot `q + 3`,
    -- on the chain before `q + 2` (`hLocks` gives it at the honest active validators)
    (hLocksU : ∀ v ∈ updaterAt M S A x (q + 2), v ∉ honestActiveAt M S A x (q + 2) →
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (q + 2)) (q + 2) v)
    -- the honest voters of slots `q + 1` and `q + 2` are active through the sync delay after Lemma 12's read time of
    -- their slot ( under: Lemma 59 at slot `q + 1`, Lemma 27 at slot `q + 2`)
    (hHold : ∀ s' : ℕ, q + 1 ≤ s' → s' ≤ q + 2 → ∀ u ∈ honestActiveAt M S A x s', u ∈ S.P.committee s' →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hp : S.P.proposer (q + 2) ∈ A.activeThroughoutToTick x (Goldilocks.proposal_window_start S.C (q + 2))
        (M.supportCutoff S.C (q + 3)) ∧
      S.P.proposer (q + 2) ∉ A.corruptedAtTime x (M.supportCutoff S.C (q + 3)))
    -- the proposer is active through the sync delay after `M.slotStart S.C (q + 2) - max (Δ S) Δs`
    -- the amended row `hHoldP`,)
    (hHoldP : S.P.proposer (q + 2) ∈ A.activeThroughout x ((M.slotStart S.C (q + 2) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C (q + 2) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hl : x.lbl ip = Event.tick (S.P.proposer (q + 2)) (M.slotStart S.C (q + 2)))
    (hsent : (⟨S.P.proposer (q + 2), NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
      x.sent (ip + 1) - x.sent ip)
    (hRootNew : ∀ B' ∈ (x.tickInput (S.P.proposer (q + 2)) (M.slotStart S.C (q + 2))).tree,
      B'.root ≠ B.root) :
    (∀ C : Block V, OnHonestChainBefore M S A x s₀ (q + 2) C → C.AncestorEq B) ∧
    B.slot = q + 2 ∧ B ≠ Block.genesis ∧
    HonestChainExtends M S A x (honestActiveAt M S A x (q + 2)) B (q + 2) ∧
    (∀ v ∈ updaterAt M S A x (q + 2),
      (x.tickOutput v (M.supportCutoff S.C (q + 2 + 1))).savedConfirmation (q + 2) = some B)
          ∧
    (∀ v ∈ updaterAt M S A x (q + 2),
      (x.tickInput v (M.supportCutoff S.C (q + 2 + 1))).finalized.AncestorEq B ∧
      (M.get_fc_root (x.tickInput v (M.supportCutoff S.C (q + 2 + 1)))).AncestorEq B ∧
      ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (M.voteTime S.C (q + 2 + 1)))
        ((M.voteTime S.C (q + 2 + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput v (M.voteTime S.C (q + 2 + 1))) (q + 2 + 1) →
        ∀ e ∈ M.lockEntries n',
          M.is_live (x.tickInput v (M.voteTime S.C (q + 2 + 1)))
            ((M.voteTime S.C (q + 2 + 1) : ℕ) : Int) e = true → e.B.AncestorEq B) ∧
    (∀ v ∈ updaterAt M S A x (q + 2),
      B ∈ (x.tickOutput v (M.supportCutoff S.C (q + 2 + 1))).fastBlocks ∧
      (∃ e ∈ (x.tickOutput v (M.supportCutoff S.C (q + 2 + 1))).lockEntries, M.le_B e = B ∧
          M.le_d e = (S.C.t_ (q + 2 + S.C.k) + 5 * S.C.Δ))) := by
  -- an honest active member `w₀` of the slot-`q + 2` committee (Lemma 88), an updater of slot `q + 2`
  have hanc0 : anchor < M.slotStart S.C (q + 2) := by exact_mod_cast lt_of_le_of_lt hAnchor hs.1
  have hanc : anchor ≤ M.slotStart S.C (q + 2 + 1) :=
    le_trans hanc0.le ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (by omega))
  have h88 := (lem88_counting_of_committeeSleepiness M F) S A x R E anchor (q + 2) (S.P.proposer (q + 2)) 0
    hSleepK hanc le_rfl
  have h88c := h88.1
  set Hs := honestActiveAt M S A x (q + 2) ∩ S.P.committee (q + 2) with hHsdef
  obtain ⟨w₀, hw₀⟩ : Hs.Nonempty := Finset.card_pos.1 (show 0 < Hs.card by omega)
  have hw₀U := (honestActiveAt_subset_updaterAt M F) S A x R E (q + 2) (Finset.mem_inter.1 hw₀).1
  -- the step's facts at each updater, with the rows read up to its own tick (`honest_proposal_saved_at_until`)
  have hAt := fun (v₀ : V) (hv₀ : v₀ ∈ updaterAt M S A x (q + 2)) =>
    (honest_proposal_saved_at_until M F U Fx) S A x R GST s₀ anchor i₁ H q ip B v₀ E hNet hSkew hRedeliver Sy hΔs
      hv₀ (hRoots v₀ hv₀) hParent (hAdvQ v₀ hv₀) hSleepK hAnchor hGST hChain hInv hLocks hOld
      (fun j u h₁ h₂ h₃ => hCaches v₀ hv₀ j u ((time_mono M) x R h₁.le) h₂ h₃) ht₀
      hs₀q hs hLk hHold hp hHoldP hl hsent hRootNew
  obtain ⟨hChainLeB, hBslot, hBne, ⟨C₀, hC₀⟩, hVote, hBw, -⟩ := hAt w₀ hw₀U
  have hAll := fun v (hv : v ∈ updaterAt M S A x (q + 2)) => ((hAt v hv).2.2.2.2.2.2 v hv le_rfl).1
  have hFin := fun v (hv : v ∈ updaterAt M S A x (q + 2)) => ((hAt v hv).2.2.2.2.2.2 v hv le_rfl).2
  have hRootH : ∀ u ∈ honestActiveAt M S A x (q + 2), ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (q + 2)) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) →
      ∀ H' : Block V, vote = GoldfishVote.mk u (q + 2) H'.root → H'.root = B.root := by
    intro u hu vote hsend H' heq
    have h1 := hVote u hu vote hsend
    rw [heq] at h1
    exact h1
  -- the live locks after the revocation of slot `q + 3`: `hLocks` at the honest active validators, `hLocksU` at the others
  have hLF : ∀ v ∈ updaterAt M S A x (q + 2),
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (q + 2)) (q + 2) v := fun v hv =>
    if h : v ∈ honestActiveAt M S A x (q + 2) then hLocks (q + 2) (by omega) le_rfl v h else hLocksU v hv h
  have hsub := (honestActiveAt_subset_updaterAt M F) S A x R E (q + 2)
  refine ⟨hChainLeB, hBslot, hBne, ⟨fun u hu vote hsend => ?_, fun w hw n' sent hrun hA e he hlive => ?_,
    fun v hv C' hC' => ?_⟩, fun v hv => (hAll v hv).2.1,
    fun v hv => ⟨ancestorEq_trans (hFin v hv) (hAll v hv).1, (hAll v hv).1, fun n' sent hrun hA e he hlive => ?_⟩,
    fun v hv => ⟨(hAll v hv).2.2.1, (hAll v hv).2.2.2⟩⟩
  · obtain ⟨H', -, heq, -⟩ := (hInv (q + 2) (by omega) le_rfl _ hC₀).1 u hu vote hsend
    have hroot := hRootH u hu vote hsend H' heq
    refine ⟨B, hBw u hu, ?_, ancestorEq_refl B⟩
    rw [heq, hroot]
  · obtain ⟨D, hD, heD⟩ := hLF w (hsub hw) n' sent hrun hA e he hlive
    exact (compatible_iff _ _).2 (Or.inl (ancestorEq_trans heD (hChainLeB D hD)))
  · rw [(hAll v (hsub hv)).2.1] at hC'
    cases hC'
    exact ancestorEq_refl B
  · obtain ⟨D, hD, heD⟩ := hLF v hv n' sent hrun hA e he hlive
    exact ancestorEq_trans heD (hChainLeB D hD)

/-- **An updater of slot `q + 2` keeps its live locks on the chain before `q + 2`.** Every validator of
`updaterAt M S A x (q + 2)` satisfies, after its revocation of slot `q + 3`, the lock invariant for the chain before
`q + 2`, when every honest active validator of slot `q + 1` satisfies it, after its revocation of slot `q + 2`, for
the chain before `q + 1`.

Why: either `v` holds no live lock at its tick to the vote time of slot `q + 3` (`mem_activeAt_or_lockFree`), and
the invariant holds for every family; or `v` is in `activeAt M S A x (q + 2)`, so active from the duty window's
start of slot `q + 2` up to its tick to the support cutoff of slot `q + 3`, so an updater of slot `q + 1`
(`mem_activeThroughoutToTick_of_inside`, the two clock bounds less than one delay). Then the lock step from slot
`q + 1` (`liveLocksOnFamilyAt_step`), which reads only `v`'s own ticks: its window from `v`'s membership of
`updaterAt M S A x (q + 2)`; `v`'s own confirmation of slot `q + 1` is on the chain before `q + 2`; and the
invariant at slot `q + 1`, by the same case split at slot `q + 1`: no live lock, or `v ∈ activeAt M S A x (q + 1)`,
and then `v ∈ honestActiveAt M S A x (q + 1)`, since `v` is outside the adversary set at every step up to its tick to
the support cutoff of slot `q + 3`, which comes after every step at a real time at most the support cutoff of slot
`q + 2` plus `ΔClockBehind`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`, `R`, `E`: the setup, the activity, the execution, its run facts, its environment facts;
- `s₀`: the healed slot; `q`: the slot of the proposal is `q + 2`; `v`: the updater.

Read aloud: an updater of slot `q + 2` keeps every live lock, after its revocation of slot `q + 3`, on the chain of
a block of the honest chain before slot `q + 2`, when the honest active validators of slot `q + 1` keep theirs on
the chain before slot `q + 1`. -/
theorem updater_locks_on_chain_of_updaterAt (U : UniformSchedule M.toSlotLayout) (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (s₀ q : ℕ) (hs₀q : s₀ ≤ q)
    (hLocks1 : ∀ u ∈ honestActiveAt M S A x (q + 1),
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (q + 1)) (q + 1) u)
    (v : V) (hv : v ∈ updaterAt M S A x (q + 2)) :
    LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (q + 2)) (q + 2) v := by
  have hΔ := one_le_Δ S
  have hk := S.C.k_ge_two
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔR : (1 : ℝ) ≤ (Δ S : ℝ) := by exact_mod_cast hΔ
  have hkR : (2 : ℝ) ≤ (S.C.k : ℝ) := by exact_mod_cast hk
  have hΔk : (Δ S : ℝ) ≤ 4 * (Δ S : ℝ) * (S.C.k : ℝ) := by nlinarith
  have hcR : ∀ s' : ℕ, ((M.supportCutoff S.C (s' + 1) : ℕ) : ℝ) = 4 * (Δ S : ℝ) * ((s' : ℕ) : ℝ) + 6 * (Δ S : ℝ) := fun s' => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s' + 1),
      (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s' + 1),
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s' + 1)]
    push_cast
    ring
  have hvR : ∀ s' : ℕ, ((M.voteTime S.C (s' + 1) : ℕ) : ℝ) = 4 * (Δ S : ℝ) * ((s' : ℕ) : ℝ) + 5 * (Δ S : ℝ) := fun s' => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s' + 1),
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s' + 1)]
    push_cast
    ring
  -- no live lock at the vote time: the invariant holds for every family
  have hfree : ∀ (s : ℕ) (𝓒 : Block V → Prop),
      (∀ e ∈ (x.tickInput v (M.voteTime S.C (s + 1))).lockEntries,
        M.is_live (x.tickInput v (M.voteTime S.C (s + 1))) ((M.voteTime S.C (s + 1) : ℕ) : Int) e = false) →
      LiveLocksOnFamilyAt M S A x 𝓒 s v := fun s 𝓒 h =>
    (liveLocksOnFamilyAt_of_locksRevoked M F U) S A x R E 𝓒 s v
      ((liveLocksOnFamilyAt_of_lockFree M F) S A x 𝓒 s v h)
  rcases (mem_activeAt_or_lockFree M F U) S A x R (q + 2) v E hv with hact | hlf
  swap
  · exact hfree (q + 2) _ hlf
  -- `v` is active from the duty window's start of slot `q + 2` up to its tick to the support cutoff of slot `q + 3`,
  -- so an updater of slot `q + 1`
  have hwa : v ∈ A.activeThroughoutToTick x (duty_window_start S.C (q + 2)) (M.supportCutoff S.C (q + 2 + 1)) :=
    E.mem_activeThroughoutToTick_of_awakeThroughoutToTick hact
  have hdR := duty_window_start_real S (q + 2)
  have hc1 := ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_slot M.toSlotLayout F.sched) S (q + 1)).2
  have hvU1 : v ∈ updaterAt M S A x (q + 1) :=
    (mem_activeThroughoutToTick_of_inside M F) R E (c := M.supportCutoff S.C (q + 1 + 1)) hwa hc1
      (by rw [hdR, hcR (q + 1)]; push_cast; linarith) (by rw [hcR (q + 1), hcR (q + 2)]; push_cast; linarith)
  -- the lock step's window, from `v`'s membership of `updaterAt M S A x (q + 2)`
  have hvt1 : 1 ≤ M.voteTime S.C (q + 2 + 1) := by
    have := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (q + 2 + 1)
    omega
  have hHon0 : v ∈ A.activeThroughoutToTick x (duty_window_start S.C (q + 2 + 1)) (M.voteTime S.C (q + 2 + 1)) := by
    refine (mem_activeThroughoutToTick_of_le_end_int M) x R E hvt1 ?_ ?_ hv
    · rw [duty_window_start_real S (q + 2 + 1), hvR (q + 2)]
      push_cast
      linarith
    · rw [hvR (q + 2), hcR (q + 2)]
      linarith
  have hds : duty_window_start S.C (q + 2 + 1) ≤ ((M.dutyWindowStart S.C (q + 1 + 2) : ℕ) : ℤ) :=
    (GoldilocksCorrectness.Record.Proofs.Routines.duty_window_start_le_dutyWindowStart M.toSlotLayout F.sched U) S
      (q + 2 + 1)
  have hHon : v ∈ A.activeThroughoutToTick x ((M.dutyWindowStart S.C (q + 1 + 2) : ℕ) : ℤ)
      (M.voteTime S.C (q + 1 + 2)) :=
    Activity.mem_activeThroughoutToTick_of_le hds hHon0
  -- `v`'s own confirmation of slot `q + 1` is on the chain before `q + 2`
  have hOwn : ∀ C : Block V,
      (x.tickOutput v (M.supportCutoff S.C (q + 1 + 1))).savedConfirmation (q + 1) = some C →
      OnHonestChainBefore M S A x s₀ (q + 2) C := fun C hC =>
    ⟨q + 1, by omega, by omega, v, hvU1, C, hC, ancestorEq_refl C⟩
  have hSub : ∀ C : Block V, OnHonestChainBefore M S A x s₀ (q + 1) C →
      OnHonestChainBefore M S A x s₀ (q + 2) C := fun C ⟨s', hs', h⟩ => ⟨s', by omega, h⟩
  -- the invariant at slot `q + 1`
  have hPrev : LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (q + 1)) (q + 1) v := by
    rcases (mem_activeAt_or_lockFree M F U) S A x R (q + 1) v E hvU1 with hact1 | hlf1
    swap
    · exact hfree (q + 1) _ hlf1
    -- honest through the real time of the support cutoff of slot `q + 2` plus `ΔClockBehind`: before `v`'s tick to the
    -- support cutoff of slot `q + 3`
    have hu : v ∉ A.corruptedAtTime x (((M.supportCutoff S.C (q + 1 + 1) : ℕ) : ℝ) + ΔClockBehind) :=
      (not_mem_corruptedAtTime_of_mem_activeThroughoutToTick M F) x R E hv
        (by rw [hcR (q + 1), hcR (q + 2)]; push_cast; linarith)
    have hc := not_mem_corruptedAtTime_union_ticks_of_le E (c := M.supportCutoff S.C (q + 1 + 1)) le_rfl hu
    exact hLocks1 v (Finset.mem_sdiff.2 ⟨hact1, hc⟩)
  exact (liveLocksOnFamilyAt_of_locksRevoked M F U) S A x R E _ (q + 2) v
    ((liveLocksOnFamilyAt_step M F U) S A x R _ _ (q + 1) v E hSkew hHon hSub hOwn hPrev)

/-- **Step 4 of the inclusion: every updater saves the proposal, fast and locked.** Under the
hypotheses of `honest_proposal_extends_chain`: every block of the chain before `q + 2` is `B` or an
ancestor of `B`; `B` is a non-genesis block of slot `q + 2`; `HonestChainExtends` holds for `B` at
slot `q + 2` at its honest active validators; every updater of slot `q + 2` saves `B` (Lemma 27),
has its finalized block and its fork-choice root on `B`'s chain, keeps no live lock off `B`'s
chain after its revocation of slot `q + 3`, and has `B` fast and locked (Lemma 60).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold;
- `q`: the slot of the proposal is `q + 2`; `ip`: the step of the proposer's tick; `B`: the
  proposal.

Roots name blocks until `M.supportCutoff S.C (q + 2 + 1)`: Lemmas 27 and 60 at slot `q + 2`.

Caches up to `M.supportCutoff S.C (q + 2 + 1)`: `honest_proposal_extends_chain_until`.

Read aloud: with the honest voters of slots `q + 1` and `q + 2` and the proposer active for the sync delay
after the times the synchrony condition reads them, every updater of slot `q + 2` saves the honest proposal
of slot `q + 2`, fast and locked. -/
theorem honest_proposal_saved_until (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ anchor i₁ H q ip : ℕ) (B : Block V)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : ∀ v ∈ updaterAt M S A x (q + 2), RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C (q + 2 + 1)))))
    (hParent : ParentHeldAtDelivery M x)
    (hAdvQ : ∀ v ∈ updaterAt M S A x (q + 2), A.AdversaryFewerThanQuorumUntil x (quorum V) (x.time (x.tickStep v (M.supportCutoff S.C (q + 2 + 1)))))
    (hSleepK : CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C (q + 2 + 1))) (hAnchor : anchor ≤ x.time i₁)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀)
    (hChain : ConfirmationsChainBefore M S A x s₀ (q + 1))
    (hInv : ∀ s : ℕ, s₀ < s → s ≤ q + 2 →
      ChainInvFor M S A x (honestActiveAt M S A x s) (OnHonestChainBefore M S A x s₀ s) s)
    (hLocks : ∀ s : ℕ, s₀ < s → s ≤ q + 2 → ∀ u ∈ honestActiveAt M S A x s,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ s) s u)
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hCaches : ∀ v ∈ updaterAt M S A x (q + 2), ∀ (j : ℕ) (u : V), x.time i₁ ≤ x.time j → x.time j ≤ x.time (x.tickStep v (M.supportCutoff S.C (q + 2 + 1))) →
      u ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j u))
    (ht₀ : M.supportCutoff S.C (s₀ + 1) ≤ x.time i₁)
    (hs₀q : s₀ ≤ q) (hs : x.time i₁ < M.slotStart S.C (q + 2) ∧
      ∀ k : ℕ, x.lbl k = Event.tick (S.P.proposer (q + 2)) (M.slotStart S.C (q + 2)) → x.time i₁ < x.time k)
    (hLk : ∀ u ∈ honestActiveAt M S A x q,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (q + 1)) q u)
    -- the honest voters of slots `q + 1` and `q + 2` are active through the sync delay after Lemma 12's read time of
    -- their slot ( under: Lemma 59 at slot `q + 1`, Lemma 27 at slot `q + 2`)
    (hHold : ∀ s' : ℕ, q + 1 ≤ s' → s' ≤ q + 2 → ∀ u ∈ honestActiveAt M S A x s', u ∈ S.P.committee s' →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hp : S.P.proposer (q + 2) ∈ A.activeThroughoutToTick x (Goldilocks.proposal_window_start S.C (q + 2))
        (M.supportCutoff S.C (q + 3)) ∧
      S.P.proposer (q + 2) ∉ A.corruptedAtTime x (M.supportCutoff S.C (q + 3)))
    -- the proposer is active through the sync delay after `M.slotStart S.C (q + 2) - max (Δ S) Δs`
    -- the amended row `hHoldP`,)
    (hHoldP : S.P.proposer (q + 2) ∈ A.activeThroughout x ((M.slotStart S.C (q + 2) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C (q + 2) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hl : x.lbl ip = Event.tick (S.P.proposer (q + 2)) (M.slotStart S.C (q + 2)))
    (hsent : (⟨S.P.proposer (q + 2), NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
      x.sent (ip + 1) - x.sent ip)
    (hRootNew : ∀ B' ∈ (x.tickInput (S.P.proposer (q + 2)) (M.slotStart S.C (q + 2))).tree,
      B'.root ≠ B.root) :
    (∀ C : Block V, OnHonestChainBefore M S A x s₀ (q + 2) C → C.AncestorEq B) ∧
    B.slot = q + 2 ∧ B ≠ Block.genesis ∧
    HonestChainExtends M S A x (honestActiveAt M S A x (q + 2)) B (q + 2) ∧
    (∀ v ∈ updaterAt M S A x (q + 2),
      (x.tickOutput v (M.supportCutoff S.C (q + 2 + 1))).savedConfirmation (q + 2) = some B)
          ∧
    (∀ v ∈ updaterAt M S A x (q + 2),
      (x.tickInput v (M.supportCutoff S.C (q + 2 + 1))).finalized.AncestorEq B ∧
      (M.get_fc_root (x.tickInput v (M.supportCutoff S.C (q + 2 + 1)))).AncestorEq B ∧
      ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (M.voteTime S.C (q + 2 + 1)))
        ((M.voteTime S.C (q + 2 + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput v (M.voteTime S.C (q + 2 + 1))) (q + 2 + 1) →
        ∀ e ∈ M.lockEntries n',
          M.is_live (x.tickInput v (M.voteTime S.C (q + 2 + 1)))
            ((M.voteTime S.C (q + 2 + 1) : ℕ) : Int) e = true → e.B.AncestorEq B) ∧
    (∀ v ∈ updaterAt M S A x (q + 2),
      B ∈ (x.tickOutput v (M.supportCutoff S.C (q + 2 + 1))).fastBlocks ∧
      (∃ e ∈ (x.tickOutput v (M.supportCutoff S.C (q + 2 + 1))).lockEntries, M.le_B e = B ∧
          M.le_d e = (S.C.t_ (q + 2 + S.C.k) + 5 * S.C.Δ))) := by
  refine (honest_proposal_saved_of_locks_until M F U Fx) S A x R GST s₀ anchor i₁ H q ip B E hNet hSkew hRedeliver Sy
    hΔs hRoots hParent hAdvQ hSleepK hAnchor hGST hChain hInv hLocks hOld hCaches ht₀ hs₀q hs hLk ?_ hHold hp hHoldP hl
    hsent hRootNew
  -- the updaters outside `honestActiveAt`: the lock step from slot `q + 1` at each
  exact fun v hv _ => (updater_locks_on_chain_of_updaterAt M F U) S A x R E hSkew s₀ q hs₀q
    (hLocks (q + 1) (by omega) (by omega)) v hv

/-- **Step 4 of the inclusion: every updater saves the proposal, fast and locked.** Under the
hypotheses of `honest_proposal_extends_chain`: every block of the chain before `q + 2` is `B` or an
ancestor of `B`; `B` is a non-genesis block of slot `q + 2`; `HonestChainExtends` holds for `B` at
slot `q + 2` at its honest active validators; every updater of slot `q + 2` saves `B` (Lemma 27),
has its finalized block and its fork-choice root on `B`'s chain, keeps no live lock off `B`'s
chain after its revocation of slot `q + 3`, and has `B` fast and locked (Lemma 60).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold;
- `q`: the slot of the proposal is `q + 2`; `ip`: the step of the proposer's tick; `B`: the
  proposal.

Roots name blocks until `M.supportCutoff S.C (q + 2 + 1)`: Lemmas 27 and 60 at slot `q + 2`.

It is `honest_proposal_saved_until` with the caches restricted to the steps it reads.

Read aloud: with the honest voters of slots `q + 1` and `q + 2` and the proposer active for the sync delay
after the times the synchrony condition reads them, every updater of slot `q + 2` saves the honest proposal
of slot `q + 2`, fast and locked. -/
theorem honest_proposal_saved (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ anchor i₁ H q ip : ℕ) (B : Block V)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : ∀ v ∈ updaterAt M S A x (q + 2), RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C (q + 2 + 1)))))
    (hParent : ParentHeldAtDelivery M x)
    (hAdvQ : ∀ v ∈ updaterAt M S A x (q + 2), A.AdversaryFewerThanQuorumUntil x (quorum V) (x.time (x.tickStep v (M.supportCutoff S.C (q + 2 + 1)))))
    (hSleepK : CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C (q + 2 + 1))) (hAnchor : anchor ≤ x.time i₁)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀)
    (hChain : ConfirmationsChain M S A x s₀)
    (hInv : ∀ s : ℕ, s₀ < s →
      ChainInvFor M S A x (honestActiveAt M S A x s) (OnHonestChainBefore M S A x s₀ s) s)
    (hLocks : ∀ s : ℕ, s₀ < s → ∀ u ∈ honestActiveAt M S A x s,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ s) s u)
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x.time i₁ ≤ x.time j → u ∉ A.corrupted j →
      CachesOnChain M S A x s₀ H (x.st j u))
    (ht₀ : M.supportCutoff S.C (s₀ + 1) ≤ x.time i₁)
    (hs₀q : s₀ ≤ q) (hs : x.time i₁ < M.slotStart S.C (q + 2) ∧
      ∀ k : ℕ, x.lbl k = Event.tick (S.P.proposer (q + 2)) (M.slotStart S.C (q + 2)) → x.time i₁ < x.time k)
    (hLk : ∀ u ∈ honestActiveAt M S A x q,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (q + 1)) q u)
    -- the honest voters of slots `q + 1` and `q + 2` are active through the sync delay after Lemma 12's read time of
    -- their slot ( under: Lemma 59 at slot `q + 1`, Lemma 27 at slot `q + 2`)
    (hHold : ∀ s' : ℕ, q + 1 ≤ s' → s' ≤ q + 2 → ∀ u ∈ honestActiveAt M S A x s', u ∈ S.P.committee s' →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hp : S.P.proposer (q + 2) ∈ A.activeThroughoutToTick x (Goldilocks.proposal_window_start S.C (q + 2))
        (M.supportCutoff S.C (q + 3)) ∧
      S.P.proposer (q + 2) ∉ A.corruptedAtTime x (M.supportCutoff S.C (q + 3)))
    -- the proposer is active through the sync delay after `M.slotStart S.C (q + 2) - max (Δ S) Δs`
    -- the amended row `hHoldP`,)
    (hHoldP : S.P.proposer (q + 2) ∈ A.activeThroughout x ((M.slotStart S.C (q + 2) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C (q + 2) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hl : x.lbl ip = Event.tick (S.P.proposer (q + 2)) (M.slotStart S.C (q + 2)))
    (hsent : (⟨S.P.proposer (q + 2), NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
      x.sent (ip + 1) - x.sent ip)
    (hRootNew : ∀ B' ∈ (x.tickInput (S.P.proposer (q + 2)) (M.slotStart S.C (q + 2))).tree,
      B'.root ≠ B.root) :
    (∀ C : Block V, OnHonestChainBefore M S A x s₀ (q + 2) C → C.AncestorEq B) ∧
    B.slot = q + 2 ∧ B ≠ Block.genesis ∧
    HonestChainExtends M S A x (honestActiveAt M S A x (q + 2)) B (q + 2) ∧
    (∀ v ∈ updaterAt M S A x (q + 2),
      (x.tickOutput v (M.supportCutoff S.C (q + 2 + 1))).savedConfirmation (q + 2) = some B)
          ∧
    (∀ v ∈ updaterAt M S A x (q + 2),
      (x.tickInput v (M.supportCutoff S.C (q + 2 + 1))).finalized.AncestorEq B ∧
      (M.get_fc_root (x.tickInput v (M.supportCutoff S.C (q + 2 + 1)))).AncestorEq B ∧
      ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (M.voteTime S.C (q + 2 + 1)))
        ((M.voteTime S.C (q + 2 + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput v (M.voteTime S.C (q + 2 + 1))) (q + 2 + 1) →
        ∀ e ∈ M.lockEntries n',
          M.is_live (x.tickInput v (M.voteTime S.C (q + 2 + 1)))
            ((M.voteTime S.C (q + 2 + 1) : ℕ) : Int) e = true → e.B.AncestorEq B) ∧
    (∀ v ∈ updaterAt M S A x (q + 2),
      B ∈ (x.tickOutput v (M.supportCutoff S.C (q + 2 + 1))).fastBlocks ∧
      (∃ e ∈ (x.tickOutput v (M.supportCutoff S.C (q + 2 + 1))).lockEntries, M.le_B e = B ∧
          M.le_d e = (S.C.t_ (q + 2 + S.C.k) + 5 * S.C.Δ))) := by
  exact (honest_proposal_saved_until M F U Fx) S A x R GST s₀ anchor i₁ H q ip B E hNet hSkew hRedeliver Sy hΔs
    hRoots hParent hAdvQ hSleepK hAnchor hGST (confirmationsChainBefore_of_chain M S A x s₀ (q + 1) hChain)
    (fun s h1 _ => hInv s h1) (fun s h1 _ => hLocks s h1) hOld (fun _ _ j u h₁ _ h₂ => hCaches j u h₁ h₂) ht₀ hs₀q hs
    hLk hHold hp hHoldP hl hsent hRootNew

/-! ## Step 6: the growth -/

/-- Two support cutoffs read with the clock bounds: when a tick to the support cutoff of slot `σ`
can be no later than a tick to the support cutoff of slot `s` (the first's real time is at least
its clock value minus `ΔClockAhead`, the second's at most its clock value plus `ΔClockBehind`), and
the two bounds sum to less than one delay, then `σ ≤ s`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `σ`, `s`: the two slots.

Read aloud: support cutoffs at most the clock bounds apart in real time belong to slots in
order. -/
theorem slot_le_of_supportCutoff_sub_le (U : UniformSchedule M.toSlotLayout) (S : Setup V)
    {ΔClockAhead ΔClockBehind : ℝ} (hA : 0 ≤ ΔClockAhead) (hB : 0 ≤ ΔClockBehind)
    (hSkew : ΔClockAhead + ΔClockBehind < Δ S) {σ s : ℕ}
    (h : (M.supportCutoff S.C σ : ℝ) - ΔClockAhead ≤ (M.supportCutoff S.C s : ℝ) + ΔClockBehind) :
    σ ≤ s := by
  by_contra hn
  push Not at hn
  have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S σ
  have h2 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S σ
  have h3 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S σ
  have h4 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s
  have h5 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s
  have h6 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s
  have hm := Nat.mul_le_mul_left (4 * Δ S) (show s + 1 ≤ σ by omega)
  rw [Nat.mul_add, Nat.mul_one] at hm
  have hle : M.supportCutoff S.C s + 4 * Δ S ≤ M.supportCutoff S.C σ := by omega
  have hleR : (M.supportCutoff S.C s : ℝ) + 4 * (Δ S : ℝ) ≤ (M.supportCutoff S.C σ : ℝ) := by
    exact_mod_cast hle
  have hΔ : (1 : ℝ) ≤ Δ S := by exact_mod_cast one_le_Δ S
  linarith

/-- **Kit fact, the finality pair of an honest attestation is at a height less than the
attestation's.** At a tick that sends an attestation `a` carrying a finality pair `p`, the pair's
height is less than `a`'s height.

Why: the tick's attestation is the one the validator client builds (Lemma 49 over the record), which
keeps a finality pair only when its height is less than the source's height, the attestation's
height.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `A`, `x`: the setup, the activity, the execution; `R`: the run's facts; `E`: the
  environment's facts; `i`: the step of the tick; `t`: its clock value; `v`: the attester; `a`: the
  attestation; `p`: its finality pair.

Read aloud: an honest attestation's finality pair is at a height less than the attestation's. -/
theorem attest_tick_finality_pair_lt (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (i t : ℕ) (v : V) (a : Attestation V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hl : x.lbl i = Event.tick v t)
    (hSent : (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈
      x.sent (i + 1) - x.sent i)
    {p : FinalityPair} (hp : a.finality_pair = some p) :
    p.hf < a.h := by
  obtain ⟨-, n', sent, hrun, ha, -, -⟩ := (tick_send_step_outcome_per_step M F R E) hl hSent
  have hts := (tickStep_eq_of_lbl M) x E hl
  have hInvT : M.nodeInv S.C S.P S.X (x.tickInput v t) := by
    unfold Trace.tickInput
    rw [hts]
    exact (lem11_node_invariant M F S A x R E i v (E.not_mem_corrupted_of_tick hl)).1
  obtain ⟨-, -, source, head, -, -, hAtt, -⟩ :=
    (GoldilocksCorrectness.Record.Statements.Routines.lem49_tick_attests F) S.C S.P S.X _ n' _ sent a
      hrun hInvT ha
  obtain ⟨τ, -, -, rfl⟩ := hAtt
  dsimp only at hp ⊢
  rcases hq : M.finality_pair (x.tickInput v t) (M.chainStateOf S.C head).h_j
      (M.chainStateOf S.C head).J.root (M.chainStateOf S.C head).h_F with _ | q
  · rw [hq] at hp
    exact absurd hp (by simp)
  · rw [hq] at hp
    dsimp only at hp
    split_ifs at hp with hle
    have hqp : q = p := Option.some.inj hp
    subst hqp
    exact Nat.lt_of_not_le hle

/-- **Kit fact, a finalized block is an entry block.** A block's finalized block, at a
finalization height at least `1`, is an entry block: its chain state's `T_h` is itself.

Why: the finalized block is the justified block of a block of the chain
(`justification_witness_of_finalized`), and a justified block at a height at least `1` is the `T_h`
of some block (Lemma 47 (f)), which is an entry block.

The variables:
- `M`: the model; `F`: its facts; `C`: the parameters; `D`: the block.

Read aloud: a finalized block at a height at least `1` is an entry block. -/
theorem chainStateOf_F_isEntry (C : Config) (D : Block V)
    (h1 : 1 ≤ (M.chainStateOf C D).h_F) :
    GoldilocksCorrectness.Record.Statements.Routines.IsEntry M C (M.chainStateOf C D).F := by
  obtain ⟨Y, -, hYj, hYJ⟩ :=
    (GoldilocksCorrectness.Record.Proofs.Routines.justification_witness_of_finalized M F) C D h1
  obtain ⟨Z, -, -, hZ⟩ :=
    (GoldilocksCorrectness.Record.Statements.Routines.lem47f_justified_is_entry M F) C Y _ rfl
      (hYj ▸ h1)
  rw [← hYJ, ← hZ]
  exact ((GoldilocksCorrectness.Record.Proofs.Routines.isEntry_T_h M F) C Z).1

/-- **Kit fact, a saved confirmation is an ancestor of a block stamped before the support
cutoff.** A confirmation `X` that the update of slot `s' + 1` saves for slot `s'` is a block of the
frame's tree whose stamp in `n` is less than `C.t_ s' + 2 · C.Δ`, or an ancestor of one.

Why: the update saves the end of its walk only when the test `voters_count late < 2 · score`
passes; the score counts no equivocator of the support votes (each support vote has no second vote
among the late votes), so some support vote supports `X`; it is an early vote, which resolves before
`C.t_ s' + 2 · C.Δ` at its head block, stamped by then; roots name blocks of the frame's tree, so
that head block is the supported block, `X` or a descendant of `X`.

The variables:
- `M`: the model; `F`: its facts; `C`, `P`: the parameters; `n`, `n'`: the node states before and
  after; `t`: the time; `s'`: the slot of the votes; `X`: the confirmation.

Read aloud: a saved confirmation is an ancestor of, or is, a block stamped before the slot's support
cutoff. -/
theorem update_confirmation_early_supporter {C : Config} {P : Provisional V} {n n' : M.N}
    {t : Time} {s' : Slot}
    (hRoots : GoldilocksCorrectness.Statements.Routines.RootsNameBlocksIn (M.fg_to_ac n).tree)
    (hUpdate : GoldilocksCorrectness.Record.Statements.Routines.ConfirmationUpdated M C P n t (s' + 1) n')
    (X : Block V) (hX : n'.savedConfirmation s' = some X) :
    ∃ H ∈ (M.fg_to_ac n).tree, X.AncestorEq H ∧ ∃ τ : Stamp, n.blockStamp H = some τ ∧
      τ < ((C.t_ s' + 2 * C.Δ : Time) : Stamp) := by
  obtain ⟨H, b, -, hb, hsaved⟩ :=
    GoldilocksCorrectness.Record.Proofs.Routines.confirmationUpdated_walk F (Nat.le_add_left 1 s')
      hRoots hUpdate
  simp only [Nat.add_sub_cancel] at hb hsaved
  rw [hX] at hsaved
  cases b with
  | false => simp at hsaved
  | true =>
  simp only [if_true, Option.some.injEq] at hsaved
  subst hsaved
  set sv := {vt ∈ GoldilocksCorrectness.Record.Statements.Routines.EarlyVotes M C n s' |
    no_second_vote_in (GoldilocksCorrectness.Record.Statements.Routines.LateVotes M C n s') vt = true}
    with hsv
  rw [GoldilocksCorrectness.Proofs.Routines.goldfish_score_eq_ok hRoots] at hb
  simp only [GoldilocksCorrectness.Proofs.Routines.dre_bind_ok] at hb
  have hb' : (Except.ok (decide (voters_count
      (GoldilocksCorrectness.Record.Statements.Routines.LateVotes M C n s') <
      2 * ((equivocators sv).card +
      (GoldilocksCorrectness.Proofs.Routines.supportersOf (M.fg_to_ac n) sv sv s' X).card))) :
      DC.DRE Bool) = Except.ok true := hb
  injection hb' with hb''
  have htest := of_decide_eq_true hb''
  have hEq : equivocators sv = ∅ :=
    GoldilocksCorrectness.Proofs.Routines.equivocators_support_eq_empty _ _
      GoldilocksCorrectness.Record.Proofs.Routines.earlyVotes_subset_lateVotes
  rw [hEq, Finset.card_empty, Nat.zero_add] at htest
  obtain ⟨u, hu⟩ :
      (GoldilocksCorrectness.Proofs.Routines.supportersOf (M.fg_to_ac n) sv sv s' X).Nonempty :=
    Finset.card_pos.1 (by omega)
  obtain ⟨vt, hvt, -, -, -, H', hH', hr, hXH⟩ :=
    (GoldilocksCorrectness.Proofs.Routines.mem_supportersOf_iff _ _ _ _ _ _).1 hu
  obtain ⟨-, y, hy, hylt⟩ :=
    GoldilocksCorrectness.Record.Proofs.Routines.mem_earlyVotes.1 (Finset.mem_filter.1 hvt).1
  obtain ⟨τv, τH, H'', hτv, hH'', hr'', -, hτH, rfl⟩ := hy
  have hHH : H'' = H' := hRoots H'' hH'' H' hH' (hr''.trans hr.symm)
  subst hHH
  exact ⟨H'', hH'', hXH, τH, hτH, lt_of_le_of_lt (le_max_right _ _) hylt⟩

/-- **Kit fact, the progress-certificate route with a general `t₀`.** Under unforgeability, take a
block `Y` that `w` holds after `j` steps and a progress certificate on the chain of `Y` at a height
`h` greater than `H` for `T`'s root; when fewer than a quorum of validators have been in the
adversary set up to the later of the time after `j` steps and `t₀`, every honest attestation sent at
or after `t₀` names the honest chain's entry at its height (`hAgree`), and every honest attestation
sent before `t₀` has height at most `H`: some honest attester `uₐ` ran the update of a slot `sₐ` at
its own tick to `M.supportCutoff S.C (sₐ + 1)`, a step before `j`; it is an updater of slot `sₐ`,
outside the adversary set after every step whose time is at most the time after `j` steps; and the
entry block `E` of the height `h` it held in the state its tick started from is on the honest chain
at slot `sₐ`, with `T`'s root.

Why: `cert_entry_held_of_agree`'s proof, which reads of each vote of the certificate only its
validator, its height and its root, so a timeout serves as a target vote does.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `A`, `x`: the setup, the activity, the execution; `s₀`: the healed slot; `t₀`: the time
  from which the honest attestations name the honest chain; `H`: the threshold; `j`: the step; `w`:
  the holder; `Y`: the held block; `T`: the block named; `h`: its height.

Read aloud: a progress certificate above the threshold on a held chain names, by root, an entry of
the honest chain at a slot whose update an honest attester ran at a tick before `j`, holding the
entry when it ticked. -/
theorem progress_cert_entry_held_of_agree (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ t₀ H j : ℕ) (w : V) (Y T : Block V) (h : Height)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max (x.time j) t₀))
    (hAgree : HonestAttestationsOnChain M S A x s₀ t₀)
    (hOld : OldAttestationsAtMostHonestAt M S A x t₀ t₀ H)
    (hY : Y ∈ (x.st j w).tree)
    (hP : GoldilocksCorrectness.Record.Statements.Routines.ProgressCertOn M Y h T) (hH : H < h) :
    ∃ (s_a : ℕ) (uₐ : V) (E : Block V), x.tickStep uₐ (M.supportCutoff S.C (s_a + 1)) < j ∧
      x.lbl (x.tickStep uₐ (M.supportCutoff S.C (s_a + 1))) = Event.tick uₐ (M.supportCutoff S.C (s_a + 1)) ∧
      uₐ ∈ updaterAt M S A x s_a ∧ uₐ ∉ A.corruptedAtTime x (x.time j) ∧
      E ∈ (x.tickInput uₐ (M.supportCutoff S.C (s_a + 1))).tree ∧
      OnHonestChainAt M S A x s₀ s_a E ∧ GoldilocksCorrectness.Record.Statements.Routines.IsEntry M S.C E ∧
      (M.chainStateOf S.C E).h = h ∧ T.root = E.root := by
  obtain ⟨X₁, hX₁Y, Q, hqA, hQ⟩ := hP
  rw [GoldilocksCorrectness.Record.quorumAt_eq_quorum Fx F.sched X₁] at hqA
  -- a member of the quorum outside the adversary set after every step whose time is at most the later
  -- of `x.time j` and `t₀`
  obtain ⟨u, hu, hhonM⟩ : ∃ u ∈ Q, A.HonestThroughTime x (max (x.time j) t₀) u := by
    by_contra hno
    have hall : ∀ v ∈ Q, ∃ i : ℕ, x.time i ≤ max (x.time j) t₀ ∧ v ∈ A.corrupted i := by
      intro v hv
      by_contra hn
      exact hno ⟨v, hv, fun i hi ha => hn ⟨i, hi, ha⟩⟩
    have h3 := hAdvQ Q hall
    omega
  have hhon : x.HonestThrough A j u :=
    fun i' hi' => hhonM i' (le_trans ((time_mono M) x R hi') (le_max_left _ _))
  -- its vote of the certificate is in its record, and its tick sent it
  obtain ⟨a, hau, hah, haT, hon⟩ := hQ u hu
  have hrec : a.content ∈ (x.st j a.val_index).sentAttestations :=
    (GoldilocksCorrectness.Record.Statements.Executions.lem74_honest_attestations_recorded M F) S A x R E j w Y a hY
      ((GoldilocksCorrectness.Record.Proofs.Routines.on_chain_mono M F) a hX₁Y hon)
      (by rw [hau]; exact hhon)
  rw [hau] at hrec
  obtain ⟨j', t', a', hj', hl, -, hsent, -, hcont, -⟩ :=
    (record_content_sent_step M F) S A x R E u j _ hrec
  have hh' : a'.h = h := by
    rw [← hah]
    exact congrArg AttestationContent.h hcont
  have hT' : a'.T = T.root := by
    rw [← haT]
    exact congrArg AttestationContent.T hcont
  -- the tick ran the update of a slot `sₐ`; the attestation's source is a fast block of it, held at the tick
  obtain ⟨sₐ, source, C, ht, hv, -, hsT, hSaved, hsrcC, hh, hT⟩ :=
    (attest_tick_update_source M F U) S A x R j' t' u a' E hl hsent
  -- the tick is not before `t₀`: its height is greater than `H`
  have hge : t₀ ≤ t' := by
    by_contra hlt
    have hle := hOld j' t' u a' hl (by exact_mod_cast (Nat.lt_of_not_le hlt))
      (Activity.not_mem_corruptedAtTime.2 fun k hk => hhonM k (le_trans hk (le_max_right _ _))) hsent
    rw [hh'] at hle
    exact absurd hle (Nat.not_le.mpr hH)
  -- the slot is at least `s₀`: `hAgree` at the send
  have hs₀ : s₀ ≤ sₐ := by
    obtain ⟨s, -, hs, ht'', -⟩ := hAgree j' t' u a' hl hge
      (Activity.not_mem_corruptedAtTime.2 fun k hk =>
        hhonM k (le_trans hk (le_trans ((time_mono M) x R (Nat.le_of_lt hj')) (le_max_left _ _)))) hsent
    rw [ht] at ht''
    have h2 := (GoldilocksCorrectness.Record.Proofs.Routines.slot_lt_of_supportCutoff_le M.toSlotLayout F.sched) S (le_of_eq ht''.symm)
    omega
  subst ht
  -- the entry block of the source's height on its chain, held at the tick
  obtain ⟨hE1, hE2, hE3⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.isEntry_T_h M F) S.C source
  have hET : (M.chainStateOf S.C source).T_h ∈ (x.st j' u).tree :=
    (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E j' u
      source _ hsT hE3
  have hts := (tickStep_eq_of_lbl M) x E hl
  have hTI : (M.chainStateOf S.C source).T_h ∈
      (x.tickInput u (M.supportCutoff S.C (sₐ + 1))).tree := by
    unfold Trace.tickInput
    rw [hts]
    exact hET
  exact ⟨sₐ, u, (M.chainStateOf S.C source).T_h, by rw [hts]; exact hj', by rw [hts]; exact hl, hv,
    Activity.not_mem_corruptedAtTime.2 fun k hk => hhonM k (le_trans hk (le_max_left _ _)), hTI,
    ⟨hs₀, u, hv, C, hSaved, ancestorEq_trans hE3 hsrcC⟩, hE1, hE2.trans (hh.trans hh'),
    hT'.symm.trans hT⟩

/-- **Kit fact, an honest member of a finality certificate sent its pair after `t₀`.** Under
unforgeability, take a block `Y` that `w` holds after `j` steps and a finality certificate on the
chain of `Y` for `(h, T)` with `h` greater than `H`; when fewer than a quorum of validators have been
in the adversary set up to the later of the time after `j` steps and `t₀`, and every honest
attestation sent before `t₀` has height at most `H`: some validator `u`, outside the adversary set
after every step whose time is at most that later time, ticked to a clock value `t ≥ t₀` at a step
`k < j`, and that tick put on the wire an attestation `a` of `u` carrying the finality pair
`(h, T.root)`.

Why: a member of the certificate's quorum is outside the adversary set (`hAdvQ`); its attestation on
`Y`'s chain is in its own record (Lemma 74), which a tick of its own sent; the attestation's height
is greater than its pair's height `h` (`attest_tick_finality_pair_lt`), so greater than `H`, and
`hOld` puts that tick at or after `t₀`.

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed;
- `S`, `A`, `x`: the setup, the activity, the execution; `t₀`: the time from which honest
  attestations may be greater than `H`; `H`: the threshold; `j`: the step; `w`: the holder; `Y`: the
  held block; `T`: the block finalized; `h`: its height.

Read aloud: a finality certificate above the threshold on a held chain has an honest member whose
tick at or after `t₀`, before `j`, sent the finality pair. -/
theorem finality_cert_member_sent (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (t₀ H j : ℕ) (w : V) (Y T : Block V) (h : Height)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max (x.time j) t₀))
    (hOld : OldAttestationsAtMostHonestAt M S A x t₀ t₀ H)
    (hY : Y ∈ (x.st j w).tree)
    (hFC : GoldilocksCorrectness.Record.Statements.Routines.FinalityCertOn M Y h T) (hH : H < h) :
    ∃ (k : ℕ) (u : V) (t : ℕ) (a : Attestation V), k < j ∧ x.lbl k = Event.tick u t ∧ t₀ ≤ t ∧
      A.HonestThroughTime x (max (x.time j) t₀) u ∧
      (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (k + 1) - x.sent k ∧
      a.finality_pair = some ⟨h, T.root⟩ := by
  obtain ⟨X₁, hX₁Y, Q, hqA, hQ⟩ := hFC
  rw [GoldilocksCorrectness.Record.quorumAt_eq_quorum Fx F.sched X₁] at hqA
  obtain ⟨u, hu, hhonM⟩ : ∃ u ∈ Q, A.HonestThroughTime x (max (x.time j) t₀) u := by
    by_contra hno
    have hall : ∀ v ∈ Q, ∃ i : ℕ, x.time i ≤ max (x.time j) t₀ ∧ v ∈ A.corrupted i := by
      intro v hv
      by_contra hn
      exact hno ⟨v, hv, fun i hi ha => hn ⟨i, hi, ha⟩⟩
    have h3 := hAdvQ Q hall
    omega
  have hhon : x.HonestThrough A j u :=
    fun i' hi' => hhonM i' (le_trans ((time_mono M) x R hi') (le_max_left _ _))
  obtain ⟨a, hau, hafp, hon⟩ := hQ u hu
  have hrec : a.content ∈ (x.st j a.val_index).sentAttestations :=
    (GoldilocksCorrectness.Record.Statements.Executions.lem74_honest_attestations_recorded M F) S A x R E j w Y a hY
      ((GoldilocksCorrectness.Record.Proofs.Routines.on_chain_mono M F) a hX₁Y hon)
      (by rw [hau]; exact hhon)
  rw [hau] at hrec
  obtain ⟨k, t, a', hk, hl, -, hsent, -, hcont, -⟩ :=
    (record_content_sent_step M F) S A x R E u j _ hrec
  have hfp' : a'.finality_pair = some ⟨h, T.root⟩ := by
    rw [← hafp]
    exact congrArg AttestationContent.finality_pair hcont
  have hlt := (attest_tick_finality_pair_lt M F) S A x R k t u a' E hl hsent hfp'
  have hge : t₀ ≤ t := by
    by_contra hlt'
    have hle := hOld k t u a' hl (by exact_mod_cast (Nat.lt_of_not_le hlt'))
      (Activity.not_mem_corruptedAtTime.2 fun k' hk' => hhonM k' (le_trans hk' (le_max_right _ _))) hsent
    have hlt2 : h < a'.h := hlt
    exact absurd (lt_of_lt_of_le (lt_trans hH hlt2) hle) (lt_irrefl _)
  exact ⟨k, u, t, a', hk, hl, hge, hhonM, hsent, hfp'⟩

/-- **Kit fact, an honest finalized block by an updater's cutoff tick is on the honest chain before
the slot.** Take an updater `v` of slot `s' > s₀` whose slot starts after the phase's end, roots
naming blocks and fewer than a quorum in the adversary set up to the real time of `v`'s tick to the
support cutoff of slot `s' + 1`, every honest attestation sent before the healed cutoff at a height
at most `H`, the honest confirmations of the slots from `s₀` up to `s'` forming one chain, and every
honest validator's caches on the chain between the phase's end and that tick. Then the finalized
block of a validator `u` honest at a step `j` of that window is on the honest chain at a slot less
than `s'`.

Why: let `D` be the block whose chain state finalized `u`'s block `F`, at the height `h_F`, and `J'`
the justified block `u` held at the phase's end, on the chain at a slot less than `s'` (its caches,
`justified_onHonestChainAt_of_caches`), an entry at a height `h'`. `F` is on the chain at a slot at
most `s'` (`finalized_onHonestChainAt_of_caches`), so `F` and `J'` are compatible (`hChain`). When
`h_F ≤ h'`, `F` is `J'` or an ancestor of it (two entries of one height on compatible chains are
one block). When `h' < h_F`, `F`'s finality certificate (Lemma 66) has an honest member `w` whose
attestation, sent at its tick to the support cutoff of a slot `sₐ + 1` with `sₐ ≤ s'`, carries the
pair `(h_F, F)` at a height less than its source's (`attest_tick_finality_pair_lt`); the source's
chain passed `h_F` at a block `Y` holding a progress certificate at `h_F` for an entry `Z'` (Lemma
67). `Y` is an ancestor of the confirmation `w`'s update saved, which is an ancestor of a block
stamped before the support cutoff of slot `sₐ` (`update_confirmation_early_supporter`), so `w` held
`Y` when it ticked to that cutoff; the certificate's honest voter ticked earlier, to the support
cutoff of a slot `s_c + 1` with `s_c < sₐ`, holding an entry at `h_F` on the chain at slot `s_c`,
which is `Z'` (`progress_cert_entry_held_of_agree`, roots naming blocks); and `F = Z'`, two entries of
one height on compatible chains.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `A`, `x`: the setup, the activity, the execution; `R`: the run's facts; `E`: the
  environment's facts; `s₀`: the healed slot; `i₁`: the step at the phase's end; `H`: the
  threshold; `s'`: the slot; `j`: the step; `u`: the validator whose finalized block is read; `v`:
  the updater.

Read aloud: a block an honest validator holds as finalized, at a step no later than an updater's
tick to the support cutoff of slot `s' + 1`, is on the honest chain before slot `s'`. -/
theorem finalized_onHonestChainBefore_of_caches_until (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout) (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ i₁ H s' j : ℕ) (u v : V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C (s' + 1)))))
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V)
      (x.time (x.tickStep v (M.supportCutoff S.C (s' + 1)))))
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1))
      (M.supportCutoff S.C (s₀ + 1)) H)
    (hChain : ConfirmationsChainBefore M S A x s₀ (s' + 1))
    (hCaches : ∀ (j : ℕ) (u : V), i₁ < j →
      x.time j ≤ x.time (x.tickStep v (M.supportCutoff S.C (s' + 1))) →
      u ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j u))
    (hs₀ : s₀ < s') (hs : x.time i₁ < M.slotStart S.C s')
    (hv : v ∈ updaterAt M S A x s')
    (hj : i₁ < j)
    (hjk : x.time j ≤ x.time (x.tickStep v (M.supportCutoff S.C (s' + 1))))
    (hu : u ∉ A.corrupted j) :
    OnHonestChainBefore M S A x s₀ s' (x.st j u).finalized := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hSl : ∀ {σ s : ℕ}, (M.supportCutoff S.C σ : ℝ) - ΔClockAhead ≤
      (M.supportCutoff S.C s : ℝ) + ΔClockBehind → σ ≤ s :=
    fun h => (slot_le_of_supportCutoff_sub_le M F U) S hA0 hB0 hSkew h
  set kc := x.tickStep v (M.supportCutoff S.C (s' + 1)) with hkcdef
  obtain ⟨k0, hk0, -⟩ := Activity.mem_activeThroughoutToTick.1 hv
  have hkc : x.lbl kc = Event.tick v (M.supportCutoff S.C (s' + 1)) := by
    rw [hkcdef, (tickStep_eq_of_lbl M) x E hk0]; exact hk0
  have hkcT := (E.tick_active kc v _ hkc).2
  set t₀ := M.supportCutoff S.C (s₀ + 1) with ht₀def
  -- the healed cutoff is no later than `kc`
  have ht₀kc : (t₀ : ℝ) ≤ x.time kc := by
    by_contra hlt
    push Not at hlt
    have := hSl (σ := s' + 1) (s := s₀ + 1) (by linarith)
    omega
  have hAdv : ∀ i : ℕ, x.time i ≤ x.time kc →
      A.AdversaryFewerThanQuorumUntil x (quorum V) (max (x.time i) t₀) :=
    fun i hi => hAdvQ.mono (max_le hi ht₀kc)
  have hRo : ∀ i : ℕ, x.time i ≤ x.time kc → RootsNameBlocksUntil M A x (x.time i) :=
    fun i hi => (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) hi hRoots
  have hAgree := (GoldilocksCorrectness.Record.Proofs.Executions.lem82_honest_attestations_on_chain M F U)
    S A x R s₀ E
  -- step 1: `u`'s finalized block is on the chain at a slot `σ ≤ s'`
  obtain ⟨σ, ⟨k, w₁, hkj, hkl⟩, hσ⟩ := (finalized_onHonestChainAt_of_caches M F U Fx) S A x R s₀ H j u E
    (hRo j hjk) (hAdv j hjk) hOld hu (hCaches j u hj hjk hu)
  have hσs : σ ≤ s' := by
    have h1 := (E.tick_active k w₁ _ hkl).2.1
    have h2 := (time_mono M) x R hkj.le
    have := hSl (σ := σ + 1) (s := s' + 1) (by linarith)
    omega
  set Fb := (x.st j u).finalized with hFbdef
  have hFb : OnHonestChainBefore M S A x s₀ (s' + 1) Fb := ⟨σ, by omega, hσ⟩
  -- step 2: the block `D` whose chain state finalized `Fb`
  obtain ⟨D, hD, hDF⟩ :=
    (GoldilocksCorrectness.Record.Statements.Executions.finalizedFromChain_of_exec M F) S A x R E j u
  rw [← hFbdef] at hDF
  -- step 3: `u`'s justified block at the phase's end, on the chain before `s'`
  -- the state the hand-over step leaves, `j' := i₁ + 1`: every step before it is at a real time at most
  -- `x[i₁].time`, before the start of slot `s'`
  obtain ⟨j', hj'1, hj'2, hj'3, hj'4⟩ : ∃ j' : ℕ, j' ≤ j ∧ i₁ < j' ∧
      x.time j' ≤ x.time j ∧ ∀ k : ℕ, k < j' → x.time k < M.slotStart S.C s' :=
    ⟨i₁ + 1, hj, Nat.lt_succ_self _, (time_mono M) x R hj,
      fun k hk => lt_of_le_of_lt ((time_mono M) x R (Nat.lt_succ_iff.1 hk)) hs⟩
  have hu' : u ∉ A.corrupted j' := fun h => hu (E.corrupted_mono j' j hj'1 h)
  obtain ⟨hH', -, hE', hh', -⟩ := hCaches j' u hj'2 (hj'3.trans hjk) hu'
  obtain ⟨σ', ⟨k', w₂, hk'j, hk'l⟩, hσ'⟩ := (justified_onHonestChainAt_of_caches M F U Fx) S A x R s₀
    t₀ H j' u E (hRo j' (hj'3.trans hjk)) (hAdv j' (hj'3.trans hjk)) hAgree hOld hu' hH'
  have hσ's : σ' < s' := by
    have h1 := (E.tick_active k' w₂ _ hk'l).2.1
    have h2 := hj'4 k' hk'j
    have hss : M.slotStart S.C s' ≤ M.supportCutoff S.C s' := by
      have := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s'
      have := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s'
      omega
    have hssR : (M.slotStart S.C s' : ℝ) ≤ M.supportCutoff S.C s' := by exact_mod_cast hss
    have := hSl (σ := σ' + 1) (s := s') (by linarith)
    omega
  set J' := (x.st j' u).justified with hJ'def
  have hJ'b : OnHonestChainBefore M S A x s₀ (s' + 1) J' := ⟨σ', by omega, hσ'⟩
  have hcompat : Fb.compatible J' = true :=
    (onHonestChainBefore_compatible M F) S A x s₀ (s' + 1) Fb J' hChain hFb hJ'b
  rcases le_or_gt (M.chainStateOf S.C D).h_F (x.st j' u).justifiedHeight with hle | hlt
  · -- step 4: `h_F ≤ h'`, so `Fb` is `J'` or an ancestor of it
    have hFJ : Fb.AncestorEq J' := by
      rcases Nat.eq_zero_or_pos (M.chainStateOf S.C D).h_F with h0 | hpos
      · rw [hDF, (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_F_genesis M F) S.C D h0]
        exact GoldilocksCorrectness.Proofs.Routines.genesis_ancestorEq _
      · obtain ⟨-, -, -, hFh⟩ :=
          ((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) S.C D).2.2 hpos
        have hFE := (chainStateOf_F_isEntry M F) S.C D hpos
        rcases (GoldilocksCorrectness.Proofs.Routines.compatible_iff _ _).1 hcompat with h | h
        · exact h
        · have h47 := ((GoldilocksCorrectness.Record.Statements.Routines.lem47_chain_state_heights M F)
            S.C J' Fb).2.2.2.1 h
          rw [hDF] at h47 hcompat ⊢
          have e1 : (M.chainStateOf S.C (M.chainStateOf S.C D).F).h ≤ (M.chainStateOf S.C J').h := by
            rw [hFh, hh']; exact hle
          have heq := (GoldilocksCorrectness.Record.Proofs.Routines.entry_eq_of_compatible M F) S.C hFE hE'
            (le_antisymm e1 h47) hcompat
          rw [heq]
          exact GoldilocksCorrectness.Proofs.Routines.ancestorEq_refl _
    exact ⟨σ', hσ's, (onHonestChainAt_of_ancestorEq M F) hσ' hFJ⟩
  · -- step 5: `h' < h_F`: the finality certificate's honest member `w`
    set hF := (M.chainStateOf S.C D).h_F with hFdef
    have hHF : H < hF := lt_trans hH' hlt
    have hpos : 1 ≤ hF := lt_of_le_of_lt (Nat.zero_le H) hHF
    obtain ⟨-, hFC, -, hFh⟩ :=
      ((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) S.C D).2.2 hpos
    obtain ⟨kw, w, tw, a, hkwj, hkwl, -, -, hsent, hfp⟩ :=
      (finality_cert_member_sent M F Fx) S A x R t₀ H j u D (M.chainStateOf S.C D).F hF E
        (hAdv j hjk) hOld hD hFC hHF
    -- step 6: `w`'s source, at a height greater than `h_F`
    have hlt' := (attest_tick_finality_pair_lt M F) S A x R kw tw w a E hkwl hsent hfp
    have hlt'' : hF < a.h := hlt'
    obtain ⟨sa, source, Cw, htw, hwact, -, hsT, hsaved, hsC, hsh, -⟩ :=
      (attest_tick_update_source M F U) S A x R kw tw w a E hkwl hsent
    subst htw
    have hkwT := (E.tick_active kw w _ hkwl).2
    have hkwkc : x.time kw ≤ x.time kc := ((time_mono M) x R hkwj.le).trans hjk
    have hsas : sa ≤ s' := by
      have := hSl (σ := sa + 1) (s := s' + 1) (by linarith)
      omega
    -- step 7: the source's chain passed `h_F` at `Y`, with a progress certificate for `Z'`
    obtain ⟨Y, hYs, -, hYp, -, hZY, hPC⟩ :=
      (GoldilocksCorrectness.Record.Statements.Routines.lem67_first_advance M F) S.C source hF hpos
        (hsh ▸ hlt'')
    obtain ⟨hZE, hZh, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.isEntry_T_h M F) S.C Y.parent
    -- step 9's timing: `w`'s saved confirmation is an ancestor of a block stamped before the support
    -- cutoff of slot `sa`, so `w` held `Y` at its tick to that cutoff
    have hwk : w ∉ A.corrupted kw := E.not_mem_corrupted_of_tick hkwl
    have hti : x.tickInput w (M.supportCutoff S.C (sa + 1)) = x.st kw w := by
      unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hkwl]
    have hAw := (tickInput_awakeSince_of_mem_activeThroughoutToTick M F U) x R E hwact
      (lt_of_le_of_lt ((GoldilocksCorrectness.Record.Proofs.Routines.duty_window_start_le_dutyWindowStart
        M.toSlotLayout F.sched U) S (sa + 1))
        (by exact_mod_cast (dutyWindowStart_succ_lt_supportCutoff M F U) S sa))
    obtain ⟨n'', sent, hrun, hAwake, hsave, -, -, -⟩ := (update_state_of_tick M F U) S A x R sa w E hkwl hAw
    obtain ⟨τ, hτ, hτle⟩ := hAw
    obtain ⟨-, hInvX, -, hcut, hsl⟩ := (cutoff_state_facts_of_tick M F U) x R E sa w τ hkwl hτ hτle
    have hUpdate := F.tk2.tick_supportCutoff_confirmation S.C S.P S.X _ _ n'' sent hrun hInvX hcut
      (by rw [hsl]; exact hAwake)
    rw [hsl] at hUpdate
    rw [hsave] at hsaved
    have hRoots₂ : GoldilocksCorrectness.Statements.Routines.RootsNameBlocksIn
        (M.fg_to_ac (x.tickInput w (M.supportCutoff S.C (sa + 1)))).tree := by
      rw [hti]
      exact (GoldilocksCorrectness.Record.Statements.Executions.rootsNameBlocksIn_frame_of_exec_node M F)
        S A x R E kw w
    obtain ⟨Hb, hHb, hCHb, τb, hτb, hτblt⟩ :=
      (update_confirmation_early_supporter M F) hRoots₂ hUpdate Cw hsaved
    rw [hti] at hHb hτb
    have hHbT : Hb ∈ (x.st kw w).tree :=
      (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hHb).1
    have hYHb : Y.AncestorEq Hb := ancestorEq_trans hYs (ancestorEq_trans hsC hCHb)
    obtain ⟨τY, τH', hτY, hτH', hτle'⟩ :=
      (ancestor_blockStamp_le M F) S A x R E kw w Hb Y hHbT hYHb
    rw [hτb] at hτH'
    cases hτH'
    have hYT : Y ∈ (x.st kw w).tree :=
      (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E kw w
        Hb Y hHbT hYHb
    -- `w`'s tick `m'` to the support cutoff of slot `sa`
    have hcc := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_succ_eq M.toSlotLayout F.sched U) S sa
    have hccR : (M.supportCutoff S.C (sa + 1) : ℝ) = (M.supportCutoff S.C sa : ℝ) + 4 * (Δ S : ℝ) := by
      rw [hcc]; push_cast; ring
    have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast one_le_Δ S
    have hdwR : ((duty_window_start S.C (sa + 1) : ℤ) : ℝ) + ΔClockBehind <
        (M.supportCutoff S.C sa : ℝ) - ΔClockAhead := by
      have h1 := (duty_window_start_le_real M F U) S (sa + 1)
      have h2 : M.dutyWindowStart S.C (sa + 1) + Δ S ≤ M.supportCutoff S.C sa := by
        have := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_succ_le_slotStart
          M.toSlotLayout F.sched) S sa
        have := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S sa
        have := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S sa
        omega
      have h2R : ((M.dutyWindowStart S.C (sa + 1) : ℕ) : ℝ) + Δ S ≤ (M.supportCutoff S.C sa : ℝ) := by
        exact_mod_cast h2
      linarith
    have hc1 : 1 ≤ M.supportCutoff S.C sa := by
      have := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S sa
      have := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S sa
      have := one_le_Δ S
      omega
    have hin := (mem_activeThroughoutToTick_of_inside M F) R E hwact hc1 hdwR (by linarith)
    obtain ⟨m', hm'l, -⟩ := Activity.mem_activeThroughoutToTick.1 hin
    have hm'T := (E.tick_active m' w _ hm'l).2
    have hm'kc : x.time m' ≤ x.time kc := by linarith
    have hstamp : τY < (((M.supportCutoff S.C sa : ℕ) : Int) : Stamp) := by
      rw [(GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_cast M.toSlotLayout F.sched U) S sa]
      exact lt_of_le_of_lt hτle' hτblt
    have hYm : Y ∈ (x.st m' w).tree :=
      (mem_T_tick_of_blockStamp_lt M F) x R E hm'l hwk hYT hτY hstamp
    -- step 8: the progress certificate's honest voter, at a slot `sc < sa`
    obtain ⟨sc, u'', E'', hk''m, hk''l, -, -, hE''T, hE''c, hE''e, hE''h, hroot⟩ :=
      (progress_cert_entry_held_of_agree M F U Fx) S A x R s₀ t₀ H m' w Y _ hF E (hAdv m' hm'kc)
        hAgree hOld hYm hPC hHF
    have hscsa : sc < sa := by
      have h1 := (E.tick_active _ u'' _ hk''l).2.1
      have h2 := (time_mono M) x R hk''m.le
      have := hSl (σ := sc + 1) (s := sa) (by linarith)
      omega
    have hZeq : (M.chainStateOf S.C Y.parent).T_h = E'' := by
      refine hRoots _ _ ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := m') (v := w) (E.not_mem_corrupted_of_tick hm'l) hm'kc ((GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E m' w
          Y _ hYm hZY)) ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (v := u'') (E.not_mem_corrupted_of_tick hk''l) ((((time_mono M) x R hk''m.le).trans hm'kc)) hE''T) hroot
    -- step 10: `Fb` is `E''`
    have hE''b : OnHonestChainBefore M S A x s₀ (s' + 1) E'' := ⟨sc, by omega, hE''c⟩
    have hc2 : Fb.compatible E'' = true :=
      (onHonestChainBefore_compatible M F) S A x s₀ (s' + 1) Fb E'' hChain hFb hE''b
    have hFE := (chainStateOf_F_isEntry M F) S.C D hpos
    rw [hDF] at hc2
    have heq := (GoldilocksCorrectness.Record.Proofs.Routines.entry_eq_of_compatible M F) S.C hFE hE''e (by rw [hFh, hE''h]) hc2
    rw [hDF, heq]
    exact ⟨sc, by omega, hE''c⟩

open Classical in
/-- **Kit fact, an updater after healing saves a confirmation.** Every updater `v` of a slot
`s' > s₀` starting after the phase's end saves some confirmation of slot `s'`.

Why: `v`'s finalized block at its tick to the support cutoff of slot `s' + 1` is on the honest chain
before `s'` (`finalized_onHonestChainBefore_of_caches_until`: its finality certificate has an honest
attester whose attestation comes from an earlier action time); the honest committee members
of slot `s'` voted for blocks extending every block of that chain, so extending `v`'s finalized block;
their votes reach `v` early (Lemma 12) and are more than half of its pool's voters (Lemma 88), so the
update saves the end of its walk (`update_confirmation_saves_of_supporters`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold;
- `s'`: the slot; `v`: the updater.

Roots name blocks, and the adversary is counted, up to the real time of `v`'s tick to the support
cutoff of slot `s' + 1` (at most `ΔClockBehind` after the cutoff): Lemma 12 at slot `s'`, read at that
tick.

Caches up to the real time of `v`'s tick to the support cutoff of slot `s' + 1`: the finality route
reads them at that tick step.

Read aloud: every updater of a slot after the healed slot and after the phase's end saves some
confirmation of that slot. -/
theorem updater_saves_after_healing_until (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ anchor i₁ H s' : ℕ) (v : V)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C (s' + 1)))))
    (hParent : ParentHeldAtDelivery M x)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (x.time (x.tickStep v (M.supportCutoff S.C (s' + 1)))))
    (hSleepK : CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C (s' + 1))) (hAnchor : anchor ≤ x.time i₁)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀)
    (hInv : ∀ s : ℕ, s₀ < s → s ≤ s' →
      ChainInvFor M S A x (honestActiveAt M S A x s) (OnHonestChainBefore M S A x s₀ s) s)
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hChain : ConfirmationsChainBefore M S A x s₀ (s' + 1))
    (hCaches : ∀ (j : ℕ) (u : V), i₁ < j → x.time j ≤ x.time (x.tickStep v (M.supportCutoff S.C (s' + 1))) →
      u ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j u))
    (hs₀ : s₀ < s') (hs : x.time i₁ < M.slotStart S.C s')
    (hv : v ∈ updaterAt M S A x s') :
    ∃ C' : Block V,
      (x.tickOutput v (M.supportCutoff S.C (s' + 1))).savedConfirmation s' = some C' := by
  -- fact 1: the honest active committee members of slot `s'` are outside the adversary set at `v`'s tick
  -- to the support cutoff of slot `s' + 1`, where Lemma 12 reads them
  have hHon : ∀ u ∈ honestActiveAt M S A x s' ∩ S.P.committee s',
      u ∉ A.corrupted (x.tickStep v (M.supportCutoff S.C (s' + 1))) := by
    -- `v`'s tick to that cutoff is by a validator outside the adversary set, and `honestActiveAt` reads
    -- each member outside the adversary set at every such tick
    intro u hu h
    obtain ⟨k0, hk0, -⟩ := Activity.mem_activeThroughoutToTick.1 hv
    rw [(tickStep_eq_of_lbl M) x E hk0] at h
    exact (Finset.mem_sdiff.1 (Finset.mem_inter.1 hu).1).2 (Finset.mem_union_right _
      (Finset.mem_filter.2 ⟨Finset.mem_univ _, k0, v, hk0, E.not_mem_corrupted_of_tick hk0, h⟩))
  -- fact 2: `v`'s finalized block at that tick is on the honest chain before `s'`
  have hFin : OnHonestChainBefore M S A x s₀ s'
      (x.tickInput v (M.supportCutoff S.C (s' + 1))).finalized := by
    obtain ⟨k0, hk0, -⟩ := Activity.mem_activeThroughoutToTick.1 hv
    have hk0s := (tickStep_eq_of_lbl M) x E hk0
    have hT := (E.tick_active k0 v _ hk0).2.1
    have hi₁ : x.time i₁ < x.time (x.tickStep v (M.supportCutoff S.C (s' + 1))) := by
      rw [hk0s]
      have hss := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s'
      have hss₂ := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s' + 1)
      have hc₂ := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s' + 1)
      have hv₂ := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s' + 1)
      have hle : M.slotStart S.C s' + Δ S ≤ M.supportCutoff S.C (s' + 1) := by
        rw [Nat.mul_add, Nat.mul_one] at hss₂; omega
      have hleR : (M.slotStart S.C s' : ℝ) + Δ S ≤ (M.supportCutoff S.C (s' + 1) : ℝ) := by
        exact_mod_cast hle
      have hB0 := E.behind_nonneg
      linarith
    unfold Trace.tickInput
    exact (finalized_onHonestChainBefore_of_caches_until M F U Fx) S A x R s₀ i₁ H s' _ v v E hSkew
      hRoots hAdvQ hOld hChain hCaches hs₀ hs hv ((lt_of_time_lt M) x R hi₁) le_rfl
      (by rw [hk0s]; exact E.not_mem_corrupted_of_tick hk0)
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ := one_le_Δ S
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hk2 := S.C.k_ge_two
  have hc₂ := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s' + 1)
  have hv₂ := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s' + 1)
  have hc₁ := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s'
  have hv₁ := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s'
  have hss := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s'
  have hss₂ := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s' + 1)
  have hdw₂ := U.dutyWindowStart_eq S (s' + 1)
  have hcs₀ : M.supportCutoff S.C s₀ ≤ M.supportCutoff S.C s' :=
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S hs₀.le
  have hcs₀' : M.supportCutoff S.C s₀ + 4 * Δ S ≤ M.supportCutoff S.C s' := by
    have := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
      (show s₀ + 1 ≤ s' by omega)
    have h' := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s₀ + 1)
    have h'' := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s₀ + 1)
    have h''' := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s₀ + 1)
    have h4 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s₀
    have h5 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s₀
    have h6 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s₀
    rw [Nat.mul_add, Nat.mul_one] at h'''
    omega
  have hm := le_max_left (Δ S) Δs
  have hm' := le_max_right (Δ S) Δs
  have hm2 := le_max_left (2 * Δ S) Δs
  have hm2' := le_max_right (2 * Δ S) Δs
  have hcc : M.supportCutoff S.C (s' + 1) = M.supportCutoff S.C s' + 4 * Δ S := by
    rw [Nat.mul_add, Nat.mul_one] at hss₂; omega
  -- `v`'s tick `kc` to the support cutoff `c` of slot `s' + 1`, and the update it runs
  obtain ⟨kc, hkc, -⟩ := Activity.mem_activeThroughoutToTick.1 hv
  have hkcs : x.tickStep v (M.supportCutoff S.C (s' + 1)) = kc := (tickStep_eq_of_lbl M) x E hkc
  rw [hkcs] at hHon hRoots
  have hti : x.tickInput v (M.supportCutoff S.C (s' + 1)) = x.st kc v := by unfold Trace.tickInput; rw [hkcs]
  have hAw := (tickInput_awakeSince_of_mem_activeThroughoutToTick M F U) x R E hv
    (lt_of_le_of_lt ((GoldilocksCorrectness.Record.Proofs.Routines.duty_window_start_le_dutyWindowStart M.toSlotLayout F.sched U) S (s' + 1)) (by exact_mod_cast (dutyWindowStart_succ_lt_supportCutoff M F U) S s'))
  obtain ⟨n'', sent, hrun, hAwake, hsave, -, -, -⟩ := (update_state_of_tick M F U) S A x R s' v E hkc hAw
  obtain ⟨τ, hτ, hτle⟩ := hAw
  obtain ⟨-, hInvX, -, hcut, hsl⟩ := (cutoff_state_facts_of_tick M F U) x R E s' v τ hkc hτ hτle
  have hUpdate := F.tk2.tick_supportCutoff_confirmation S.C S.P S.X _ _ n'' sent hrun hInvX hcut
    (by rw [hsl]; exact hAwake)
  rw [hsl] at hUpdate
  rw [hsave]
  -- the honest committee members' votes extend every block of the chain before `s'`
  obtain ⟨Hf, hHf⟩ := (chain_votes_of_inv M F U) S A x R s₀ s' _ E hSkew (hInv s' hs₀ le_rfl) hFin
  -- `v` is active from `ΔClockAhead` before the support cutoff of slot `s'` up to `kc`
  have hdwR : ((duty_window_start S.C (s' + 1) : ℤ) : ℝ) + ΔClockBehind <
      (M.supportCutoff S.C s' : ℝ) - ΔClockAhead := by
    have h1 := (duty_window_start_le_real M F U) S (s' + 1)
    have h2 : M.dutyWindowStart S.C (s' + 1) + Δ S ≤ M.supportCutoff S.C s' := by
      have := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_succ_le_slotStart M.toSlotLayout F.sched) S s'
      omega
    have h2R : ((M.dutyWindowStart S.C (s' + 1) : ℕ) : ℝ) + Δ S ≤ (M.supportCutoff S.C s' : ℝ) := by
      exact_mod_cast h2
    linarith
  obtain ⟨kc', hkc', hwin⟩ := (tick_window_of_activeThroughoutToTick_int M) x R E hv hdwR
  have hkk : kc' = kc := (E.tick_unique kc' kc v _ hkc' hkc)
  subst hkk
  -- `v`'s tick `kR` to the support cutoff of slot `s'`, before `kc`
  obtain ⟨kR, hkR, hkR1, -⟩ := E.tick_of_active (M.supportCutoff S.C s') (by omega) v fun j h1 h2 => by
    refine hwin j h1 ?_
    by_contra hcon
    have hle := (time_mono M) x R (show kc' ≤ j by omega)
    have := (E.tick_active kc' v _ hkc').2.1
    have hcR : ((M.supportCutoff S.C (s' + 1)) : ℝ) = (M.supportCutoff S.C s' : ℝ) + 4 * Δ S := by rw [hcc]; push_cast; ring
    linarith
  have hkRc : kR ≤ kc' := by
    by_contra hcon
    have hvR : v ∉ A.corrupted kR := E.not_mem_corrupted_of_tick hkR
    have := E.clock_mono kc' kR v (M.supportCutoff S.C (s' + 1)) (M.supportCutoff S.C s') (by omega) hvR (Or.inl hkc') (Or.inl hkR)
    omega
  have hkRs : x.tickStep v (M.supportCutoff S.C s') = kR := (tickStep_eq_of_lbl M) x E hkR
  have hkRT : x.time kR ≥ (M.supportCutoff S.C s' : ℝ) - ΔClockAhead := (E.tick_active kR v _ hkR).2.1
  -- the voters, honest active committee members of slot `s'`
  set Hs := honestActiveAt M S A x s' ∩ S.P.committee s' with hHsdef
  have hHeld : ∀ u ∈ Hs, HeldEarlyVoteFor M S.C (x.tickInput v (M.supportCutoff S.C (s' + 1))) s' (Hf u) u := by
    refine (GoldilocksCorrectness.Record.Statements.Executions.lem12_honest_vote_delivered_until M F U) S A x R GST s'
      (M.supportCutoff S.C (s' + 1)) Hs Hf v E hNet hSkew hRedeliver Sy hΔs ?_ hParent ((votesCastByOwner_of_unforgeability M F) S A x R E)
      (le_trans hGST hcs₀) (by rw [hcc]; omega) kc' hkc' ?_ ?_ ?_ (M.dutyWindowStart S.C (s' + 1)) ?_ ?_ ?_
    · -- roots up to `v`'s tick to the support cutoff of slot `s'`, at most `kc`
      rw [hkRs]
      exact (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) ((time_mono M) x R hkRc) hRoots
    · -- no memory-losing restart of `v` after its tick to the support cutoff of slot `s'`: it is awake there
      intro l t' h1 h2 hl
      rw [hkRs] at h1
      have hact := hwin l (le_trans hkRT ((time_mono M) x R h1.le)) h2.le
      exact (E.restart_crashed l v t' false hl).1 (Activity.mem_active.1 hact).1
    · intro u hu
      exact ⟨(Finset.mem_inter.1 hu).2, hHon u hu, (hHf u hu).1, (hHf u hu).2.1⟩
    · -- the holders' window, inside each member's duty window
      intro u hu
      have hw := (honestActiveAt_window M F) S A s' u E (Finset.mem_inter.1 hu).1
      have hmc : max (2 * Δ S) Δs ≤ M.supportCutoff S.C s' := by omega
      have h := (mem_activeThroughout_of_mem_activeThroughoutToTick M F) R E hw
        (a' := M.supportCutoff S.C s' - max (2 * Δ S) Δs) (e := M.supportCutoff S.C s' - max (2 * Δ S) Δs + Δs)
        (by
          have h1 := (duty_window_start_le_real M F U) S s'
          have hdw₁ := U.dutyWindowStart_eq S s'
          have h2 : M.dutyWindowStart S.C s' + Δ S ≤ M.supportCutoff S.C s' - max (2 * Δ S) Δs := by
            rw [Nat.mul_add, Nat.mul_one] at hss₂
            have hkm : max (Δ S) Δs + 3 * Δ S < 4 * Δ S * S.C.k := by
              have h' : ((max (Δ S) Δs + 3 * Δ S : ℕ) : ℝ) < ((4 * Δ S * S.C.k : ℕ) : ℝ) := by
                push_cast; linarith
              exact_mod_cast h'
            omega
          have h2R : ((M.dutyWindowStart S.C s' : ℕ) : ℝ) + Δ S ≤
              ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) := by exact_mod_cast h2
          linarith)
        (by
          have h2 : M.supportCutoff S.C s' - max (2 * Δ S) Δs + Δs + Δ S ≤ M.supportCutoff S.C (s' + 1) := by
            omega
          have h2R : ((M.supportCutoff S.C s' - max (2 * Δ S) Δs + Δs : ℕ) : ℝ) + Δ S ≤
              (M.supportCutoff S.C (s' + 1) : ℝ) := by exact_mod_cast h2
          linarith)
      convert h using 2
      push_cast; ring
    · -- `v`'s window start, more than both clock bounds before the holders' read time
      have hk8 : 8 * Δ S ≤ 4 * Δ S * S.C.k := by
        have := Nat.mul_le_mul_left (4 * Δ S) hk2; omega
      have hs1 : 4 * Δ S ≤ 4 * Δ S * s' := by
        have := Nat.mul_le_mul_left (4 * Δ S) (show 1 ≤ s' by omega); omega
      have hmle : max (2 * Δ S) Δs ≤ M.supportCutoff S.C s' := by omega
      have hcR : ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) =
          (M.supportCutoff S.C s' : ℝ) - max ((2 * Δ S : ℕ) : ℝ) (Δs : ℝ) := by
        rw [Nat.cast_sub hmle, Nat.cast_max]
      rw [hcR]
      have hk8R : (8 : ℝ) * Δ S ≤ 4 * Δ S * S.C.k := by exact_mod_cast hk8
      have hΔsR : (Δs : ℝ) ≤ max (Δ S : ℝ) Δs := le_max_right _ _
      rcases Nat.eq_zero_or_pos (M.dutyWindowStart S.C (s' + 1)) with h0 | hpos
      · -- the window start is `0`: the read time is at least four delays
        rw [h0]
        have h4 : max (2 * Δ S) Δs + 4 * Δ S ≤ M.supportCutoff S.C s' := by omega
        have h4R : ((max (2 * Δ S) Δs : ℕ) : ℝ) + 4 * Δ S ≤ (M.supportCutoff S.C s' : ℝ) := by exact_mod_cast h4
        rw [Nat.cast_max] at h4R
        push_cast at h4R ⊢
        linarith
      · have hD : M.dutyWindowStart S.C (s' + 1) + 4 * Δ S * S.C.k = 4 * Δ S * s' + 5 * Δ S := by
          rw [Nat.mul_add, Nat.mul_one] at hss₂; omega
        have hDR : ((M.dutyWindowStart S.C (s' + 1) : ℕ) : ℝ) + 4 * Δ S * S.C.k = 4 * Δ S * s' + 5 * Δ S := by
          exact_mod_cast hD
        have hcsR : (M.supportCutoff S.C s' : ℝ) = 4 * Δ S * s' + 2 * Δ S := by
          have : M.supportCutoff S.C s' = 4 * Δ S * s' + 2 * Δ S := by omega
          rw [this]; push_cast; ring
        have hmx : max ((2 * Δ S : ℕ) : ℝ) (Δs : ℝ) < 4 * Δ S * S.C.k - 3 * Δ S - ΔClockAhead - ΔClockBehind := by
          refine max_lt ?_ ?_
          · push_cast; linarith
          · linarith
        push_cast at hmx ⊢; linarith
    · -- `v` is active from the duty window's start of slot `s' + 1` up to its tick to the support cutoff of slot `s'`
      have h1 := Activity.mem_activeThroughoutToTick_of_le
        ((GoldilocksCorrectness.Record.Proofs.Routines.duty_window_start_le_dutyWindowStart M.toSlotLayout F.sched U) S (s' + 1)) hv
      exact (mem_activeThroughoutToTick_of_tick_le M F) R E h1 hkR (by rw [hcc]; omega)
    · intro u hu
      exact (hHf u hu).2.2 _ hFin
  -- the update saves: the voters are early supporters of the frame's finalized block, and more than half of the pool's
  -- voters
  have hRoots₂ : GoldilocksCorrectness.Statements.Routines.RootsNameBlocksIn (M.fg_to_ac (x.tickInput v (M.supportCutoff S.C (s' + 1)))).tree := by
    rw [hti]; exact (GoldilocksCorrectness.Record.Statements.Executions.rootsNameBlocksIn_frame_of_exec_node M F) S A x R E kc' v
  have hSup : ∀ u ∈ Hs, GoldilocksCorrectness.Record.Statements.Routines.EarlySupporterOf M S.C
      (x.tickInput v (M.supportCutoff S.C (s' + 1))) (s' + 1 - 1) (M.fg_to_ac (x.tickInput v (M.supportCutoff S.C (s' + 1)))).F u :=
    fun u hu => (heldEarlyVoteFor_earlySupporterOf M F) S.C _ s' _ (Hf u) u (hHeld u hu)
      (by rw [(GoldilocksCorrectness.Record.Proofs.Routines.fg_to_ac_F M F)]; exact (hHf u hu).2.2 _ hFin)
  have hSlot : ∀ vote ∈ M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s' + 1))) (s' + 1 - 1), vote.slot = s' + 1 - 1 := by
    rw [hti, Nat.add_sub_cancel]
    exact (GoldilocksCorrectness.Record.Statements.Executions.pool_slot_of_exec M F) S A x R E kc' v s'
  have hK := hSleepK (s' + 1) (by omega)
    (by
      have : (anchor : ℝ) < M.slotStart S.C s' := lt_of_le_of_lt hAnchor hs
      have : anchor < M.slotStart S.C s' := by exact_mod_cast this
      rw [Nat.mul_add, Nat.mul_one] at hss₂; omega) le_rfl
  rw [Nat.add_sub_cancel] at hK
  have hsub : S.P.committee s' \ Hs ⊆ S.P.committee s' \ honestActiveAt M S A x s' := by
    intro w hw
    simp only [hHsdef, Finset.mem_sdiff, Finset.mem_inter] at hw ⊢
    tauto
  have hVoters : M.voters_count (M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s' + 1))) (s' + 1 - 1)) < 2 * Hs.card := by
    rw [hti, Nat.add_sub_cancel]
    exact (GoldilocksCorrectness.Record.Proofs.Routines.voters_count_lt_of_committee_majority M F)
      ((GoldilocksCorrectness.Record.Statements.Executions.pool_committee_of_exec M F) S A x R E kc' v s')
      (lt_of_le_of_lt (Finset.card_le_card hsub) hK)
  have h := (GoldilocksCorrectness.Record.Proofs.Routines.update_confirmation_saves_of_supporters F) _ Hs
    (Nat.le_add_left 1 s') hRoots₂ (ancestorEq_refl _) hSup hSlot hVoters hUpdate
  rw [Nat.add_sub_cancel] at h
  exact h

/-- **Kit fact, an updater after healing saves a confirmation.** Every updater `v` of a slot
`s' > s₀` starting after the phase's end saves some confirmation of slot `s'`.

Why: `v`'s finalized block at its tick to the support cutoff of slot `s' + 1` is on the honest chain
before `s'` (`finalized_onHonestChainBefore_of_caches_until`: its finality certificate has an honest
attester whose attestation comes from an earlier action time); the honest committee members
of slot `s'` voted for blocks extending every block of that chain, so extending `v`'s finalized block;
their votes reach `v` early (Lemma 12) and are more than half of its pool's voters (Lemma 88), so the
update saves the end of its walk (`update_confirmation_saves_of_supporters`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold;
- `s'`: the slot; `v`: the updater.

Roots name blocks, and the adversary is counted, up to the real time of `v`'s tick to the support
cutoff of slot `s' + 1` (at most `ΔClockBehind` after the cutoff): Lemma 12 at slot `s'`, read at that
tick.

It is `updater_saves_after_healing_until` with the caches and the chain invariant read at
every step after `i₁` and every slot after `s₀`; the confirmations' chain `hChain` is the `_until`
form's.

Read aloud: every updater of a slot after the healed slot and after the phase's end saves some
confirmation of that slot. -/
theorem updater_saves_after_healing (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ anchor i₁ H s' : ℕ) (v : V)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C (s' + 1)))))
    (hParent : ParentHeldAtDelivery M x)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (x.time (x.tickStep v (M.supportCutoff S.C (s' + 1)))))
    (hSleepK : CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C (s' + 1))) (hAnchor : anchor ≤ x.time i₁)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀)
    (hInv : ∀ s : ℕ, s₀ < s →
      ChainInvFor M S A x (honestActiveAt M S A x s) (OnHonestChainBefore M S A x s₀ s) s)
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    -- the confirmations of the updaters of the slots from `s₀` to `s'` form a chain
    (hChain : ConfirmationsChainBefore M S A x s₀ (s' + 1))
    (hCaches : ∀ (j : ℕ) (u : V), x.time i₁ ≤ x.time j → u ∉ A.corrupted j →
      CachesOnChain M S A x s₀ H (x.st j u))
    (hs₀ : s₀ < s') (hs : x.time i₁ < M.slotStart S.C s')
    (hv : v ∈ updaterAt M S A x s') :
    ∃ C' : Block V,
      (x.tickOutput v (M.supportCutoff S.C (s' + 1))).savedConfirmation s' = some C' := by
  exact (updater_saves_after_healing_until M F U) Fx S A x R GST s₀ anchor i₁ H s' v E hNet hSkew hRedeliver Sy hΔs
    hRoots hParent hAdvQ hSleepK hAnchor hGST (fun s h1 _ => hInv s h1) hOld hChain
    (fun j u h1 _ h3 => hCaches j u ((time_mono M) x R h1.le) h3) hs₀ hs hv

/-- An honest confirmation is on the honest chain.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `L`: the
  block.

Read aloud: an honest confirmation is on the honest chain. -/
theorem isHonestConfirmation_onHonestChain {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} {s₀ : ℕ} {L : Block V}
    (h : IsHonestConfirmation M S A x s₀ L) : OnHonestChain M S A x s₀ L := by
  obtain ⟨s, hs, v, hv, hL⟩ := h
  exact ⟨s, hs, v, hv, L, hL, ancestorEq_refl L⟩

/-- **Step 6 of the inclusion, on the chain before `s' + 1`: the proposal stays an ancestor of
the confirmed tip.** For an honest
active validator `v` of a slot `s' ≥ q + 2`, with `c` the support cutoff of slot `s' + 1`,
`B` is `v`'s confirmed tip in the state `v`'s tick to `c` leaves (`x.tickOutput v c`) or an ancestor
of it.

Why: `v`'s update of slot `s' + 1` saved a confirmation `C'` (`updater_saves_after_healing`), a
descendant of `B` or `B` (Lemma 81's chain), which no live lock vetoes (the lock invariant); so
the record is `C'` or a descendant; the confirmed tip is the record or the finalized block, which
then descends from the record.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold;
- `q`: the slot of the proposal is `q + 2`; `s'`: the slot; `B`: the proposal; `u₀`: an updater
  of slot `q + 2` whose saved confirmation of slot `q + 2` is `B`; `v`: the validator, whose saved
  confirmation of slot `q + 2` is `B` when it is an honest active validator of slot `q + 2`.

Roots name blocks, fewer than a quorum of validators have been in the adversary set, and the caches
and the record are on the honest chain, up to the time of the step after `v`'s tick to the support
cutoff of slot `s' + 1`: the conclusion reads the state that tick leaves, at that step, whose time can
be later than the cutoff (the tick's own real time can be up to `ΔClockBehind` after it); the caches
and the record there place `v`'s finalized block and its record on the chain
(`finalized_onHonestChainAt_of_caches`), and `updater_saves_after_healing_until` reads them up to the
tick.

On the chain before `s' + 1`, the invariant and the locks up to slot `s'`, the record on the chain
at a slot whose update ran by then: the proof compares confirmations of slots from `q + 2` to `s'`,
`v`'s record and its finalized block in the state its tick to the support cutoff of slot `s' + 1`
leaves, both then on
the chain before `s' + 1`.

Read aloud: for an honest active validator of a slot `s' ≥ q + 2`, `B` is its confirmed tip in the
state its own tick to the support cutoff of slot `s' + 1` leaves, or an ancestor of it, on the chain
before `s' + 1`. -/
theorem proposal_ancestor_of_tip_after_update_before (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ anchor i₁ H q s' : ℕ) (B : Block V) (u₀ v : V)

    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C (s' + 1)) + 1)))
    (hParent : ParentHeldAtDelivery M x)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (x.time (x.tickStep v (M.supportCutoff S.C (s' + 1)) + 1)))
    (hSleepK : CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C (s' + 1))) (hAnchor : anchor ≤ x.time i₁)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀)
    (hChain : ConfirmationsChainBefore M S A x s₀ (s' + 1))
    (hInv : ∀ s : ℕ, s₀ < s → s ≤ s' →
      ChainInvFor M S A x (honestActiveAt M S A x s) (OnHonestChainBefore M S A x s₀ s) s)
    (hLocks : ∀ s : ℕ, s₀ < s → s ≤ s' → ∀ u ∈ honestActiveAt M S A x s,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ s) s u)
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), i₁ < j →
      x.time j ≤ x.time (x.tickStep v (M.supportCutoff S.C (s' + 1)) + 1) → u ∉ A.corrupted j →
      CachesOnChain M S A x s₀ H (x.st j u))
    (hLatest : ∀ (j : ℕ) (u : V), i₁ < j → x.time j ≤ x.time (x.tickStep v (M.supportCutoff S.C (s' + 1)) + 1) →
      u ∉ A.corrupted j → (∃ σ : ℕ, x.lbl (x.tickStep u (M.supportCutoff S.C (σ + 1))) = Event.tick u (M.supportCutoff S.C (σ + 1)) ∧ x.tickStep u (M.supportCutoff S.C (σ + 1)) < j ∧
        OnHonestChainAt M S A x s₀ σ (x.st j u).latestConfirmed) ∧
        (x.st j u).latestConfirmed ∈ (x.st j u).tree)
    (hs₀q : s₀ ≤ q) (hs : x.time i₁ < M.slotStart S.C (q + 2)) (hqs : q + 2 ≤ s')
    (hu₀ : u₀ ∈ updaterAt M S A x (q + 2))
    (hSaved₀ : (x.tickOutput u₀ (M.supportCutoff S.C (q + 2 + 1))).savedConfirmation (q + 2) = some B)
    (hSavedv : v ∈ honestActiveAt M S A x (q + 2) →
      (x.tickOutput v (M.supportCutoff S.C (q + 2 + 1))).savedConfirmation (q + 2) = some B)
    (hv : v ∈ honestActiveAt M S A x s') :
    B.AncestorEq (M.ac_confirmed (x.tickOutput v (M.supportCutoff S.C (s' + 1)))) := by
  have hΔ := one_le_Δ S
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  have hvU : v ∈ updaterAt M S A x s' := (honestActiveAt_subset_updaterAt M F) S A x R E s' hv
  have hvw : v ∈ A.activeThroughoutToTick x (Goldilocks.duty_window_start S.C (s' + 1))
      (M.supportCutoff S.C (s' + 1)) := hvU
  -- `v`'s tick `K` to the support cutoff of slot `s' + 1`, honest there and at the step after it
  obtain ⟨K, hlK, -⟩ := Activity.mem_activeThroughoutToTick.1 hvw
  have hKs : x.tickStep v (M.supportCutoff S.C (s' + 1)) = K := (tickStep_eq_of_lbl M) x E hlK
  have huK1 : v ∉ A.corrupted (K + 1) := E.not_mem_corrupted_succ_of_tick hlK
  have hTO : x.tickOutput v (M.supportCutoff S.C (s' + 1)) = x.st (K + 1) v := by
    unfold Trace.tickOutput; rw [hKs]
  rw [hKs] at hRoots hAdvQ hCaches hLatest
  have hKK : x.time K ≤ x.time (K + 1) := htime (Nat.le_succ K)
  have hKt := E.tick_active K v _ hlK
  obtain ⟨-, hc1, -, hs1, -⟩ :=
    (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (s' + 1)
  obtain ⟨-, -, -, hs0, -⟩ :=
    (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S s'
  have hsq := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S hqs
  have hskew := hSkew
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  -- the phase's end is before `K`
  have hi₁K : x.time i₁ < x.time K := by
    have h1 : ((M.slotStart S.C (q + 2) : ℕ) : ℝ) + 4 * Δ S + 2 * Δ S ≤
        ((M.supportCutoff S.C (s' + 1) : ℕ) : ℝ) := by
      exact_mod_cast (show M.slotStart S.C (q + 2) + 4 * Δ S + 2 * Δ S ≤ M.supportCutoff S.C (s' + 1) by omega)
    linarith [hKt.2.1]
  -- `v`'s update of slot `s' + 1` saved a confirmation `C'`
  obtain ⟨C', hC'⟩ := (updater_saves_after_healing_until M F U) Fx S A x R GST s₀ anchor i₁ H s' v E
    hNet hSkew hRedeliver Sy hΔs
    (by rw [hKs]; exact (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) hKK hRoots)
    hParent
    (by
      rw [hKs]
      intro X hX
      exact hAdvQ X fun u hu => by
        obtain ⟨i, hi, hc⟩ := hX u hu
        exact ⟨i, le_trans hi hKK, hc⟩)
    hSleepK hAnchor hGST hInv hOld hChain
    (fun j u h1 h2 h3 => hCaches j u h1 (by rw [hKs] at h2; exact le_trans h2 hKK) h3) (by omega)
    (by
      have h1 : ((M.slotStart S.C (q + 2) : ℕ) : ℝ) ≤ ((M.slotStart S.C s' : ℕ) : ℝ) := by
        exact_mod_cast hsq
      linarith)
    hvU
  have hBC' : B.AncestorEq C' := by
    rcases Nat.lt_or_eq_of_le hqs with hlt | heq
    · exact (hChain (q + 2) s' u₀ v B C' (by omega) hqs (by omega) hu₀ hvU hSaved₀ hC').1 hlt
    · subst heq
      rw [hSavedv hv] at hC'
      cases hC'
      exact ancestorEq_refl B
  -- every block of the chain before `s'` is `C'` or an ancestor of it
  have hBeforeLe : ∀ D : Block V, OnHonestChainBefore M S A x s₀ s' D → D.AncestorEq C' := by
    intro D hD
    obtain ⟨s'', hs'', hs₀'', u, hu, C'', hC'', hDC''⟩ := hD
    exact ancestorEq_trans hDC''
      ((hChain s'' s' u v C'' C' hs₀'' hs''.le (by omega) hu hvU hC'' hC').1 hs'')
  -- the update, its record, and no veto
  obtain ⟨τ, hτ, hτle⟩ := (tickInput_awakeSince_of_mem_activeThroughoutToTick M F U) x R E hvw
    (by
      have hdwz : (Goldilocks.duty_window_start S.C (s' + 1) : ℤ) ≤
          ((M.dutyWindowStart S.C (s' + 1) : ℕ) : ℤ) := by
        rw [(GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_eq_toNat M.toSlotLayout F.sched U)]
        exact Int.self_le_toNat _
      have h := (dutyWindowStart_succ_lt_supportCutoff M F U) S s'
      have h' : ((M.dutyWindowStart S.C (s' + 1) : ℕ) : ℤ) < ((M.supportCutoff S.C (s' + 1) : ℕ) : ℤ) := by
        exact_mod_cast h
      exact lt_of_le_of_lt hdwz h')
  obtain ⟨n'', sent, hrun, hAwF, hSv, -, -, hLc⟩ :=
    (update_state_of_tick M F U) S A x R s' v E hlK ⟨τ, hτ, hτle⟩
  have hUpd := (confirmationUpdated_of_cutoff_tickInput M F U) x R s' v n'' sent hrun hAwF
  have hA''C : n''.savedConfirmation s' = some C' := by
    have h := hC'
    rw [hSv] at h
    exact h
  have hNoVeto : M.live_lock_vetoes (x.tickInput v (M.supportCutoff S.C (s' + 1)))
      ((M.supportCutoff S.C (s' + 1) : ℕ) : Int) C' = false :=
    (GoldilocksCorrectness.Record.Proofs.Routines.live_lock_vetoes_eq_false M F)
      ((live_locks_compatible_of_revocation M F U) S A x R s' C' v E hSkew hvU (Finset.mem_sdiff.1 hv).2
        (fun hH n' sent' hrun' hAw' e he hl => by
          obtain ⟨D, hD, heD⟩ := hLocks s' (by omega) le_rfl v hH n' sent' hrun' hAw' e he hl
          exact (compatible_iff _ _).2 (Or.inl (ancestorEq_trans heD (hBeforeLe D hD)))))
  have hBL : B.AncestorEq (x.tickOutput v (M.supportCutoff S.C (s' + 1))).latestConfirmed := by
    rw [hLc]
    rcases GoldilocksCorrectness.Record.Proofs.Routines.update_confirmation_latest_cases
        (Nat.add_one_ne_zero s') hUpd with
      ⟨hn, -⟩ | ⟨C₁, hC₁, ⟨hv', -⟩ | ⟨-, hadv⟩⟩
    · rw [Nat.add_sub_cancel, hA''C] at hn
      cases hn
    · rw [Nat.add_sub_cancel, hA''C] at hC₁
      cases hC₁
      rw [hNoVeto] at hv'
      cases hv'
    · rw [Nat.add_sub_cancel, hA''C] at hC₁
      cases hC₁
      have hadv' : M.latestConfirmed n'' = _ := hadv
      rw [hadv']
      rcases (GoldilocksCorrectness.Record.Proofs.Routines.advance_some F)
          (M.fg_to_ac (x.tickInput v (M.supportCutoff S.C (s' + 1))))
          (x.tickInput v (M.supportCutoff S.C (s' + 1))).latestConfirmed C' with
        ⟨-, hanc, ha⟩ | ⟨-, ha⟩
      · rw [ha]; exact ancestorEq_trans hBC' hanc
      · rw [ha]; exact hBC'
  rw [hTO] at hBL ⊢
  -- a slot whose update some validator ran at a step at most `K` is at most `s'`
  have hslot_le : ∀ (σ k : ℕ) (u : V), x.lbl k = Event.tick u (M.supportCutoff S.C (σ + 1)) →
      k ≤ K → σ ≤ s' := by
    intro σ k u hl hk
    by_contra hlt
    obtain ⟨-, hcσ, -, -, -⟩ :=
      (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 1)
    have hsσ := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
      (show s' + 1 + 1 ≤ σ + 1 by omega)
    have hmR : ((M.supportCutoff S.C (s' + 1) : ℕ) : ℝ) + 4 * Δ S ≤
        ((M.supportCutoff S.C (σ + 1) : ℕ) : ℝ) := by
      exact_mod_cast (show M.supportCutoff S.C (s' + 1) + 4 * Δ S ≤ M.supportCutoff S.C (σ + 1) by omega)
    have h1 := (E.tick_active k u _ hl).2.1
    have h2 := htime hk
    linarith [hKt.2.2]
  -- the record and the finalized block after the tick are on the chain before `s' + 1`
  obtain ⟨⟨σL, hσl, hσlt, hLh⟩, hLT⟩ := hLatest (K + 1) v (Nat.lt_succ_of_lt ((lt_of_time_lt M) x R hi₁K)) le_rfl huK1
  have hcut : ((M.supportCutoff S.C (s₀ + 1) : ℕ) : ℝ) ≤ x.time (K + 1) := by
    have hsm := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
      (show s₀ + 1 ≤ s' by omega)
    obtain ⟨-, hc₀, -, -, -⟩ :=
      (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (s₀ + 1)
    have h1 : ((M.supportCutoff S.C (s₀ + 1) : ℕ) : ℝ) + 4 * Δ S ≤ ((M.supportCutoff S.C (s' + 1) : ℕ) : ℝ) := by
      exact_mod_cast (show M.supportCutoff S.C (s₀ + 1) + 4 * Δ S ≤ M.supportCutoff S.C (s' + 1) by omega)
    linarith [hKt.2.1]
  obtain ⟨σF, ⟨kF, uF, hkF, hlF⟩, hFh⟩ := (finalized_onHonestChainAt_of_caches M F U Fx) S A x R s₀ H (K + 1)
    v E hRoots (by rw [max_eq_left hcut]; exact hAdvQ) hOld huK1
    (hCaches (K + 1) v (Nat.lt_succ_of_lt ((lt_of_time_lt M) x R hi₁K)) le_rfl huK1)
  have hLb : OnHonestChainBefore M S A x s₀ (s' + 1) (x.st (K + 1) v).latestConfirmed :=
    ⟨σL, Nat.lt_succ_of_le (hslot_le σL _ v hσl (Nat.lt_succ_iff.1 hσlt)), hLh⟩
  have hFb : OnHonestChainBefore M S A x s₀ (s' + 1) (x.st (K + 1) v).finalized :=
    ⟨σF, Nat.lt_succ_of_le (hslot_le σF kF uF hlF (Nat.lt_succ_iff.1 hkF)), hFh⟩
  have hcomp := (onHonestChainBefore_compatible M F) S A x s₀ (s' + 1) _ _ hChain hLb hFb
  -- the confirmed tip is the record, or the finalized block, a descendant of the record
  rw [F.rd.ac_confirmed_eq]
  split
  · exact hBL
  · rename_i hnot
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.fg_to_ac_F M F)]
    rcases (compatible_iff _ _).1 hcomp with h1 | h1
    · exact ancestorEq_trans hBL h1
    · exact absurd (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).2 ⟨hLT, h1⟩) hnot

/-- **Step 6 of the inclusion: the proposal stays an ancestor of the confirmed tip.** For an honest
active validator `v` of a slot `s' ≥ q + 2`, with `c` the support cutoff of slot `s' + 1`,
`B` is `v`'s confirmed tip in the state `v`'s tick to `c` leaves (`x.tickOutput v c`) or an ancestor
of it.

Why: `v`'s update of slot `s' + 1` saved a confirmation `C'` (`updater_saves_after_healing`), a
descendant of `B` or `B` (Lemma 81's chain), which no live lock vetoes (the lock invariant); so
the record is `C'` or a descendant; the confirmed tip is the record or the finalized block, which
then descends from the record.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold;
- `q`: the slot of the proposal is `q + 2`; `s'`: the slot; `B`: the proposal; `u₀`: an updater
  of slot `q + 2` whose saved confirmation of slot `q + 2` is `B`; `v`: the validator, whose saved
  confirmation of slot `q + 2` is `B` when it is an honest active validator of slot `q + 2`.

Roots name blocks, fewer than a quorum of validators have been in the adversary set, and the caches
and the record are on the honest chain, up to the time of the step after `v`'s tick to the support
cutoff of slot `s' + 1`: the conclusion reads the state that tick leaves, at that step, whose time can
be later than the cutoff (the tick's own real time can be up to `ΔClockBehind` after it); the caches
and the record there place `v`'s finalized block and its record on the chain
(`finalized_onHonestChainAt_of_caches`), and `updater_saves_after_healing_until` reads them up to the
tick.

Read aloud: for an honest active validator of a slot `s' ≥ q + 2`, `B` is its confirmed tip in the
state its own tick to the support cutoff of slot `s' + 1` leaves, or an ancestor of it. -/
theorem proposal_ancestor_of_tip_after_update_until (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ anchor i₁ H q s' : ℕ) (B : Block V) (u₀ v : V)

    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C (s' + 1)) + 1)))
    (hParent : ParentHeldAtDelivery M x)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (x.time (x.tickStep v (M.supportCutoff S.C (s' + 1)) + 1)))
    (hSleepK : CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C (s' + 1))) (hAnchor : anchor ≤ x.time i₁)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀)
    (hChain : ConfirmationsChain M S A x s₀)
    (hInv : ∀ s : ℕ, s₀ < s →
      ChainInvFor M S A x (honestActiveAt M S A x s) (OnHonestChainBefore M S A x s₀ s) s)
    (hLocks : ∀ s : ℕ, s₀ < s → ∀ u ∈ honestActiveAt M S A x s,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ s) s u)
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), i₁ < j →
      x.time j ≤ x.time (x.tickStep v (M.supportCutoff S.C (s' + 1)) + 1) → u ∉ A.corrupted j →
      CachesOnChain M S A x s₀ H (x.st j u))
    (hLatest : ∀ (j : ℕ) (u : V), i₁ < j → x.time j ≤ x.time (x.tickStep v (M.supportCutoff S.C (s' + 1)) + 1) →
      u ∉ A.corrupted j → (∃ σ : ℕ, x.lbl (x.tickStep u (M.supportCutoff S.C (σ + 1))) = Event.tick u (M.supportCutoff S.C (σ + 1)) ∧ x.tickStep u (M.supportCutoff S.C (σ + 1)) < j ∧
        OnHonestChainAt M S A x s₀ σ (x.st j u).latestConfirmed) ∧
        (x.st j u).latestConfirmed ∈ (x.st j u).tree)
    (hs₀q : s₀ ≤ q) (hs : x.time i₁ < M.slotStart S.C (q + 2)) (hqs : q + 2 ≤ s')
    (hu₀ : u₀ ∈ updaterAt M S A x (q + 2))
    (hSaved₀ : (x.tickOutput u₀ (M.supportCutoff S.C (q + 2 + 1))).savedConfirmation (q + 2) = some B)
    (hSavedv : v ∈ honestActiveAt M S A x (q + 2) →
      (x.tickOutput v (M.supportCutoff S.C (q + 2 + 1))).savedConfirmation (q + 2) = some B)
    (hv : v ∈ honestActiveAt M S A x s') :
    B.AncestorEq (M.ac_confirmed (x.tickOutput v (M.supportCutoff S.C (s' + 1)))) := by
  exact (proposal_ancestor_of_tip_after_update_before M F U) Fx S A x R GST s₀ anchor i₁ H q s' B u₀ v E hNet
    hSkew hRedeliver Sy hΔs hRoots hParent hAdvQ hSleepK hAnchor hGST
    ((confirmationsChainBefore_of_chain M) S A x s₀ (s' + 1) hChain) (fun s h1 _ => hInv s h1)
    (fun s h1 _ => hLocks s h1) hOld hCaches hLatest hs₀q hs hqs hu₀ hSaved₀ hSavedv hv

/-- **Step 6 of the inclusion: the proposal stays an ancestor of the confirmed tip.** For an honest
active validator `v` of a slot `s' ≥ q + 2`, with `c` the support cutoff of slot `s' + 1`,
`B` is `v`'s confirmed tip in the state `v`'s tick to `c` leaves (`x.tickOutput v c`) or an ancestor
of it.

Why: `v`'s update of slot `s' + 1` saved a confirmation `C'` (`updater_saves_after_healing`), a
descendant of `B` or `B` (Lemma 81's chain), which no live lock vetoes (the lock invariant); so
the record is `C'` or a descendant; the confirmed tip is the record or the finalized block, which
then descends from the record.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold;
- `q`: the slot of the proposal is `q + 2`; `s'`: the slot; `B`: the proposal; `u₀`: an updater
  of slot `q + 2` whose saved confirmation of slot `q + 2` is `B`; `v`: the validator, whose saved
  confirmation of slot `q + 2` is `B` when it is an honest active validator of slot `q + 2`.

Roots name blocks, and fewer than a quorum of validators have been in the adversary set, up to the
time of the step after `v`'s tick to the support cutoff of slot `s' + 1`, the step whose state the
conclusion reads (`proposal_ancestor_of_tip_after_update_until`).

It is `proposal_ancestor_of_tip_after_update_until`
with the caches restricted to the steps it reads.

Read aloud: for an honest active validator of a slot `s' ≥ q + 2`, `B` is its confirmed tip in the
state its own tick to the support cutoff of slot `s' + 1` leaves, or an ancestor of it. -/
theorem proposal_ancestor_of_tip_after_update (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ anchor i₁ H q s' : ℕ) (B : Block V) (u₀ v : V)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C (s' + 1)) + 1)))
    (hParent : ParentHeldAtDelivery M x)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (x.time (x.tickStep v (M.supportCutoff S.C (s' + 1)) + 1)))
    (hSleepK : CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C (s' + 1))) (hAnchor : anchor ≤ x.time i₁)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀)
    (hChain : ConfirmationsChain M S A x s₀)
    (hInv : ∀ s : ℕ, s₀ < s →
      ChainInvFor M S A x (honestActiveAt M S A x s) (OnHonestChainBefore M S A x s₀ s) s)
    (hLocks : ∀ s : ℕ, s₀ < s → ∀ u ∈ honestActiveAt M S A x s,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ s) s u)
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x.time i₁ ≤ x.time j → u ∉ A.corrupted j →
      CachesOnChain M S A x s₀ H (x.st j u))
    (hLatest : ∀ (j : ℕ) (u : V), x.time i₁ ≤ x.time j → u ∉ A.corrupted j → (∃ σ : ℕ, x.lbl (x.tickStep u (M.supportCutoff S.C (σ + 1))) = Event.tick u (M.supportCutoff S.C (σ + 1)) ∧ x.tickStep u (M.supportCutoff S.C (σ + 1)) < j ∧
        OnHonestChainAt M S A x s₀ σ (x.st j u).latestConfirmed) ∧
        (x.st j u).latestConfirmed ∈ (x.st j u).tree)
    (hs₀q : s₀ ≤ q) (hs : x.time i₁ < M.slotStart S.C (q + 2)) (hqs : q + 2 ≤ s')
    (hu₀ : u₀ ∈ updaterAt M S A x (q + 2))
    (hSaved₀ : (x.tickOutput u₀ (M.supportCutoff S.C (q + 2 + 1))).savedConfirmation (q + 2) = some B)
    (hSavedv : v ∈ honestActiveAt M S A x (q + 2) →
      (x.tickOutput v (M.supportCutoff S.C (q + 2 + 1))).savedConfirmation (q + 2) = some B)
    (hv : v ∈ honestActiveAt M S A x s') :
    B.AncestorEq (M.ac_confirmed (x.tickOutput v (M.supportCutoff S.C (s' + 1)))) := by
  exact (proposal_ancestor_of_tip_after_update_until M F U) Fx S A x R GST s₀ anchor i₁ H q s' B u₀ v E hNet
    hSkew hRedeliver Sy hΔs hRoots hParent hAdvQ hSleepK hAnchor hGST hChain hInv hLocks hOld
    (fun j u h1 _ h3 => hCaches j u ((time_mono M) x R h1.le) h3)
    (fun j u h1 _ h3 => hLatest j u ((time_mono M) x R h1.le) h3) hs₀q hs hqs hu₀ hSaved₀ hSavedv
    hv

/-! ## The export and the inclusion -/

/-- `lem90_included_update_facts` at the slot `q + 2`, with the lock invariant at slot `q` (`hLk`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold;
- `q`: the slot of the proposal is `q + 2`; `ip`: the step of the proposer's tick; `B`: the
  proposal; `v`: the updater.

Roots name blocks until `M.supportCutoff S.C (q + 2 + 1)`: `honest_proposal_saved`.

Caches up to `M.supportCutoff S.C (q + 2 + 1)`: `honest_proposal_saved_until`.

Read aloud: the per-validator facts of the inclusion at the slot `q + 2`, with the lock invariant at
slot `q` and the honest voters of slots `q + 1` and `q + 2` and the proposer active for the sync delay after
the times the synchrony condition reads them. -/
theorem included_update_facts_q_until (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ anchor i₁ H q ip : ℕ) (B : Block V) (v : V)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C (q + 2 + 1)))))
    (hParent : ParentHeldAtDelivery M x)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (x.time (x.tickStep v (M.supportCutoff S.C (q + 2 + 1)))))
    (hSleepK : CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C (q + 2 + 1))) (hAnchor : anchor ≤ x.time i₁)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀)
    (hChain : ConfirmationsChainBefore M S A x s₀ (q + 1))
    (hInv : ∀ s : ℕ, s₀ < s → s ≤ q + 2 →
      ChainInvFor M S A x (honestActiveAt M S A x s) (OnHonestChainBefore M S A x s₀ s) s)
    (hLocks : ∀ s : ℕ, s₀ < s → s ≤ q + 2 → ∀ u ∈ honestActiveAt M S A x s,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ s) s u)
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), i₁ < j → x.time j ≤ x.time (x.tickStep v (M.supportCutoff S.C (q + 2 + 1))) →
      u ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j u))
    (ht₀ : M.supportCutoff S.C (s₀ + 1) ≤ x.time i₁)
    (hs₀q : s₀ ≤ q) (hs : x.time i₁ < M.slotStart S.C (q + 2) ∧
      ∀ k : ℕ, x.lbl k = Event.tick (S.P.proposer (q + 2)) (M.slotStart S.C (q + 2)) → x.time i₁ < x.time k)
    (hLk : ∀ u ∈ honestActiveAt M S A x q,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (q + 1)) q u)
    -- the honest voters of slots `q + 1` and `q + 2` are active through the sync delay after Lemma 12's read time of
    -- their slot ( under: Lemma 59 at slot `q + 1`, Lemma 27 at slot `q + 2`)
    (hHold : ∀ s' : ℕ, q + 1 ≤ s' → s' ≤ q + 2 → ∀ u ∈ honestActiveAt M S A x s', u ∈ S.P.committee s' →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hp : S.P.proposer (q + 2) ∈ A.activeThroughoutToTick x (Goldilocks.proposal_window_start S.C (q + 2))
        (M.supportCutoff S.C (q + 2 + 1)) ∧
      S.P.proposer (q + 2) ∉ A.corruptedAtTime x (M.supportCutoff S.C (q + 2 + 1)))
    -- the proposer is active through the sync delay after `M.slotStart S.C (q + 2) - max (Δ S) Δs`
    -- the amended row `hHoldP`,)
    (hHoldP : S.P.proposer (q + 2) ∈ A.activeThroughout x ((M.slotStart S.C (q + 2) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C (q + 2) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hl : x.lbl ip = Event.tick (S.P.proposer (q + 2)) (M.slotStart S.C (q + 2)))
    (hsent : (⟨S.P.proposer (q + 2), NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
      x.sent (ip + 1) - x.sent ip)
    (hRootNew : ∀ B' ∈ (x.tickInput (S.P.proposer (q + 2)) (M.slotStart S.C (q + 2))).tree,
      B'.root ≠ B.root)
    (hv : v ∈ updaterAt M S A x (q + 2)) :
    (x.tickOutput v (M.supportCutoff S.C (q + 2 + 1))).savedConfirmation (q + 2) = some B ∧
      B ∈ (x.tickOutput v (M.supportCutoff S.C (q + 2 + 1))).fastBlocks ∧
      (∃ e ∈ (x.tickOutput v (M.supportCutoff S.C (q + 2 + 1))).lockEntries,
        M.le_B e = B ∧ M.le_d e = S.C.t_ (q + 2 + S.C.k) + 5 * S.C.Δ) ∧
      (∀ e ∈ (x.tickOutput v (M.supportCutoff S.C (q + 2 + 1))).lockEntries,
        M.is_live (x.stateBefore (M.supportCutoff S.C (q + 2 + 1)) v)
          ((M.supportCutoff S.C (q + 2 + 1) : ℕ) : Int) e = true → e.B.AncestorEq B) ∧
      (x.tickOutput v (M.supportCutoff S.C (q + 2 + 1))).latestConfirmed = B := by
  -- step 4 at `v`, with the rows at `v`'s own tick (`honest_proposal_saved_at_until`)
  obtain ⟨hChainLeB, hBslot, -, -, -, -, hUp⟩ := (honest_proposal_saved_at_until M F U Fx) S A x R GST s₀ anchor i₁
    H q ip B v E hNet hSkew hRedeliver Sy hΔs hv hRoots hParent hAdvQ hSleepK hAnchor hGST hChain hInv hLocks hOld
    hCaches ht₀ hs₀q hs hLk hHold hp hHoldP hl hsent hRootNew
  obtain ⟨⟨-, hSavedv, hFastv, hLockv⟩, -⟩ := hUp v hv le_rfl
  -- the live locks after `v`'s revocation of slot `q + 3` are on `B`'s chain
  have hLF := (updater_locks_on_chain_of_updaterAt M F U) S A x R E hSkew s₀ q hs₀q
    (hLocks (q + 1) (by omega) (by omega)) v hv
  have hRevC : ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (M.voteTime S.C (q + 2 + 1)))
        ((M.voteTime S.C (q + 2 + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput v (M.voteTime S.C (q + 2 + 1))) (q + 2 + 1) →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.tickInput v (M.voteTime S.C (q + 2 + 1)))
          ((M.voteTime S.C (q + 2 + 1) : ℕ) : Int) e = true → e.B.compatible B = true := by
    intro n' sent hrun hA e he hlive
    obtain ⟨D, hD, heD⟩ := hLF n' sent hrun hA e he hlive
    exact (compatible_iff _ _).2 (Or.inl (ancestorEq_trans heD (hChainLeB D hD)))
  -- the outcome of `v`'s tick to the support cutoff of slot `q + 3`, from a state awake since the duty window's start
  obtain ⟨K, hlK, -⟩ := Activity.mem_activeThroughoutToTick.1 hv
  obtain ⟨τ, hτ, hτle⟩ := (tickInput_awakeSince_of_mem_activeThroughoutToTick M F U) x R E hv
    (by
      have hdwz : (Goldilocks.duty_window_start S.C (q + 2 + 1) : ℤ) ≤
          ((M.dutyWindowStart S.C (q + 2 + 1) : ℕ) : ℤ) := by
        rw [(GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_eq_toNat M.toSlotLayout F.sched U)]
        exact Int.self_le_toNat _
      have h := (dutyWindowStart_succ_lt_supportCutoff M F U) S (q + 2)
      have h' : ((M.dutyWindowStart S.C (q + 2 + 1) : ℕ) : ℤ) < ((M.supportCutoff S.C (q + 2 + 1) : ℕ) : ℤ) := by
        exact_mod_cast h
      exact lt_of_le_of_lt hdwz h')
  obtain ⟨n'', sent, hrun, hAwF, hSv, -, hLe, -⟩ :=
    (update_state_of_tick M F U) S A x R (q + 2) v E hlK ⟨τ, hτ, hτle⟩
  have hSaved'' : M.savedConfirmation n'' (q + 2) = some B := by rw [← hSv]; exact hSavedv
  refine ⟨hSavedv, hFastv, hLockv, fun e he hlive => ?_, ?_⟩
  · -- the entries after the update: on `B`'s chain, the liveness read only for its deadline
    have he' : e ∈ M.lockEntries n'' := by rw [← hLe]; exact he
    exact (update_lock_entries_ancestorEq_at M F U) S A x R (q + 2) B v E hSkew hv n'' sent hrun hAwF hSaved''
      hBslot hRevC e he' _ hlive
  · -- the record of the confirmed tip: no live lock of the update's input conflicts with `B`
    exact (latest_confirmed_after_update_of_compatible M F U) S A x R (q + 2) B v E hSkew (by rw [hBslot]) hv
      hSavedv ((live_locks_compatible_of_revocation_of_active M F U) S A x R (q + 2) B v E hSkew hv
        (fun _ => hRevC))

/-- `lem90_included_update_facts` at the slot `q + 2`, with the lock invariant at slot `q` (`hLk`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold;
- `q`: the slot of the proposal is `q + 2`; `ip`: the step of the proposer's tick; `B`: the
  proposal; `v`: the updater.

Roots name blocks until `M.supportCutoff S.C (q + 2 + 1)`: `honest_proposal_saved`.

It is `included_update_facts_q_until` with the caches restricted to the steps it reads.

Read aloud: the per-validator facts of the inclusion at the slot `q + 2`, with the lock invariant at
slot `q` and the honest voters of slots `q + 1` and `q + 2` and the proposer active for the sync delay after
the times the synchrony condition reads them. -/
theorem included_update_facts_q (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ anchor i₁ H q ip : ℕ) (B : Block V) (v : V)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C (q + 2 + 1)))))
    (hParent : ParentHeldAtDelivery M x)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (x.time (x.tickStep v (M.supportCutoff S.C (q + 2 + 1)))))
    (hSleepK : CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C (q + 2 + 1))) (hAnchor : anchor ≤ x.time i₁)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀)
    (hChain : ConfirmationsChain M S A x s₀)
    (hInv : ∀ s : ℕ, s₀ < s →
      ChainInvFor M S A x (honestActiveAt M S A x s) (OnHonestChainBefore M S A x s₀ s) s)
    (hLocks : ∀ s : ℕ, s₀ < s → ∀ u ∈ honestActiveAt M S A x s,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ s) s u)
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x.time i₁ ≤ x.time j → u ∉ A.corrupted j →
      CachesOnChain M S A x s₀ H (x.st j u))
    (ht₀ : M.supportCutoff S.C (s₀ + 1) ≤ x.time i₁)
    (hs₀q : s₀ ≤ q) (hs : x.time i₁ < M.slotStart S.C (q + 2) ∧
      ∀ k : ℕ, x.lbl k = Event.tick (S.P.proposer (q + 2)) (M.slotStart S.C (q + 2)) → x.time i₁ < x.time k)
    (hLk : ∀ u ∈ honestActiveAt M S A x q,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (q + 1)) q u)
    -- the honest voters of slots `q + 1` and `q + 2` are active through the sync delay after Lemma 12's read time of
    -- their slot ( under: Lemma 59 at slot `q + 1`, Lemma 27 at slot `q + 2`)
    (hHold : ∀ s' : ℕ, q + 1 ≤ s' → s' ≤ q + 2 → ∀ u ∈ honestActiveAt M S A x s', u ∈ S.P.committee s' →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hp : S.P.proposer (q + 2) ∈ A.activeThroughoutToTick x (Goldilocks.proposal_window_start S.C (q + 2))
        (M.supportCutoff S.C (q + 2 + 1)) ∧
      S.P.proposer (q + 2) ∉ A.corruptedAtTime x (M.supportCutoff S.C (q + 2 + 1)))
    -- the proposer is active through the sync delay after `M.slotStart S.C (q + 2) - max (Δ S) Δs`
    -- the amended row `hHoldP`,)
    (hHoldP : S.P.proposer (q + 2) ∈ A.activeThroughout x ((M.slotStart S.C (q + 2) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C (q + 2) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hl : x.lbl ip = Event.tick (S.P.proposer (q + 2)) (M.slotStart S.C (q + 2)))
    (hsent : (⟨S.P.proposer (q + 2), NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
      x.sent (ip + 1) - x.sent ip)
    (hRootNew : ∀ B' ∈ (x.tickInput (S.P.proposer (q + 2)) (M.slotStart S.C (q + 2))).tree,
      B'.root ≠ B.root)
    (hv : v ∈ updaterAt M S A x (q + 2)) :
    (x.tickOutput v (M.supportCutoff S.C (q + 2 + 1))).savedConfirmation (q + 2) = some B ∧
      B ∈ (x.tickOutput v (M.supportCutoff S.C (q + 2 + 1))).fastBlocks ∧
      (∃ e ∈ (x.tickOutput v (M.supportCutoff S.C (q + 2 + 1))).lockEntries,
        M.le_B e = B ∧ M.le_d e = S.C.t_ (q + 2 + S.C.k) + 5 * S.C.Δ) ∧
      (∀ e ∈ (x.tickOutput v (M.supportCutoff S.C (q + 2 + 1))).lockEntries,
        M.is_live (x.stateBefore (M.supportCutoff S.C (q + 2 + 1)) v)
          ((M.supportCutoff S.C (q + 2 + 1) : ℕ) : Int) e = true → e.B.AncestorEq B) ∧
      (x.tickOutput v (M.supportCutoff S.C (q + 2 + 1))).latestConfirmed = B := by
  exact (included_update_facts_q_until M F U Fx) S A x R GST s₀ anchor i₁ H q ip B v E hNet hSkew hRedeliver Sy hΔs
    hRoots hParent hAdvQ hSleepK hAnchor hGST (confirmationsChainBefore_of_chain M S A x s₀ (q + 1) hChain)
    (fun s h1 _ => hInv s h1) (fun s h1 _ => hLocks s h1) hOld
    (fun j u h₁ _ h₂ => hCaches j u ((time_mono M) x R h₁.le) h₂) ht₀ hs₀q hs
    hLk hHold hp hHoldP hl hsent hRootNew hv

/-- **A row on the state each step leaves gives the row on the state before each later step.** For any
predicate `P` of a step and a validator: when `P (j + 1) u` holds for every step `j` at a real time from
`x[i₁].time` to `t` and every validator `u` outside the adversary set at `j`, then `P j u` holds for every step
`j` after `i₁` at a real time at most `t` and every `u` outside the adversary set at `j`. It is the index twin of
`cachesOnChain_st_of_succ`, for the
caches and the record rows alike.

Why: `j = j' + 1` with `i₁ ≤ j'`; the step `j'` is at a real time from `x[i₁].time` to `x.time j` (`time_mono`),
and a validator outside the adversary set at `j` is outside it at `j'`.

The variables:
- `M`: the model; `S`, `A`, `x`, `R`: the setup, the activity, the execution, its run facts; `E`: the
  environment's facts; `i₁`: the hand-over step; `t`: the bound on the real times; `P`: the row's predicate.

Read aloud: what holds after each step from the hand-over time holds before each step after the hand-over
step. -/
theorem row_of_succ_index (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (i₁ : ℕ) (t : ℝ) (P : ℕ → V → Prop)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (h : ∀ (j : ℕ) (u : V), x.time i₁ ≤ x.time j → x.time j ≤ t → u ∉ A.corrupted j → P (j + 1) u) :
    ∀ (j : ℕ) (u : V), i₁ < j → x.time j ≤ t → u ∉ A.corrupted j → P j u := by
  intro j u hj hjt hu
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  exact h j' u ((time_mono M) x R (by omega)) (le_trans ((time_mono M) x R (Nat.le_succ j')) hjt)
    (E.not_mem_corrupted_of_le (Nat.le_succ j') hu)

/-- **The first part of the inclusion's claim at the slot `q + 2`, read up to `t`.** Under
`included_q_upTo`'s hypotheses, the proposer of slot `q + 2` puts a block on the wire at its tick to
the slot's start, and for every such block `B` either some block the proposer held then carries
`B`'s root, or every honest active validator of slot `q + 2` whose tick to the support cutoff of
slot `q + 3` is at a real time at most `t` saved `B` for slot `q + 2` and has `B` as its confirmed
tip right after that tick.

Why: the proposer is active at its tick to the slot's start (`mem_activeThroughoutToTick_of_inside`,
the margins from `hSkew`), so it proposes (`honest_proposer_proposes`). For `v` as stated, write
`K` for its tick: the rows read up to `x.time K`, at most `t`, give the saved confirmation and the
record `B` after the update (`included_update_facts_q_until` at `v`). A tick keeps the time
(`RunFacts.time_keep`), so the state after `K` is read at a time at most `t` too: `B` is in its tree
(`hLatest`), and its finalized block is on the chain before slot `q + 2`
(`finalized_onHonestChainBefore_of_caches_until`), so it is `B` or an ancestor of `B`
(`honest_proposal_saved_at_until`). Then `B` is in the tree of `M.fg_to_ac`, and the confirmed tip
is the record, `B`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `A`, `x`: the setup, the activity, the execution; `R`: its run facts; `E`: the condition on
  executions; `GST`: the time from which the network is synchronous; `s₀`: the healed slot;
  `anchor`: the time from which committee sleepiness holds; `i₁`: the step at the phase's end;
  `H`: the threshold;
- `q`: the slot of the proposal is `q + 2`; `t`: the time up to which the states are read.

Read aloud: the proposer of slot `q + 2` proposes, and each block it proposes collides with a root
it held or is saved and confirmed by every honest active validator of the slot whose update tick is
by `t`. -/
theorem included_q_first_upTo (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ anchor i₁ H q t : ℕ)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x t)
    (hParent : ParentHeldAtDelivery M x)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) t)
    (hSleepK : CommitteeSleepinessUntil M S A x anchor t) (hAnchor : anchor ≤ x.time i₁)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀)
    -- the updaters' confirmations of the slots whose update some validator ran at a step by `t` form one chain
    (hChain : ∀ (σ k : ℕ) (u : V), x.lbl k = Event.tick u (M.supportCutoff S.C (σ + 1)) →
        x.time k ≤ t → ConfirmationsChainBefore M S A x s₀ (σ + 1))
    (hInv : ∀ s : ℕ, s₀ < s → M.supportCutoff S.C (s + 1) ≤ t →
      ChainInvFor M S A x (honestActiveAt M S A x s) (OnHonestChainBefore M S A x s₀ s) s)
    (hLocks : ∀ s : ℕ, s₀ < s → M.supportCutoff S.C (s + 1) ≤ t → ∀ u ∈ honestActiveAt M S A x s,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ s) s u)
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    -- the honest voters of slots `q + 1` and `q + 2` are active through the sync delay after Lemma 12's read time of
    -- their slot, and the proposer of slot `q + 2` through the sync delay after one delay or one sync delay before its
    -- start (: `honest_proposal_saved_until`'s two clauses)
    (hHold : ∀ s' : ℕ, q + 1 ≤ s' → s' ≤ q + 2 → ∀ u ∈ honestActiveAt M S A x s', u ∈ S.P.committee s' →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hHoldP : S.P.proposer (q + 2) ∈ A.activeThroughout x ((M.slotStart S.C (q + 2) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C (q + 2) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hCaches : ∀ (j : ℕ) (u : V), i₁ < j → x.time j ≤ t →
      u ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j u))
    (ht₀ : M.supportCutoff S.C (s₀ + 1) ≤ x.time i₁)
    (hs₀q : s₀ ≤ q) (hs : x.time i₁ < M.slotStart S.C (q + 2) ∧
      ∀ k : ℕ, x.lbl k = Event.tick (S.P.proposer (q + 2)) (M.slotStart S.C (q + 2)) → x.time i₁ < x.time k)
    -- the update of slot `q + 2` is at most `t`
    (hqt : M.supportCutoff S.C (q + 2 + 1) ≤ t)
    (hLk : ∀ u ∈ honestActiveAt M S A x q,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (q + 1)) q u)
    (hp : S.P.proposer (q + 2) ∈ A.activeThroughoutToTick x (Goldilocks.proposal_window_start S.C (q + 2))
        (M.supportCutoff S.C (q + 2 + 1)) ∧
      S.P.proposer (q + 2) ∉ A.corruptedAtTime x (M.supportCutoff S.C (q + 2 + 1)))
    (hLatest : ∀ (j : ℕ) (u : V), i₁ < j → x.time j ≤ t →
      u ∉ A.corrupted j → (∃ σ : ℕ, x.lbl (x.tickStep u (M.supportCutoff S.C (σ + 1))) = Event.tick u (M.supportCutoff S.C (σ + 1)) ∧ x.tickStep u (M.supportCutoff S.C (σ + 1)) < j ∧
        OnHonestChainAt M S A x s₀ σ (x.st j u).latestConfirmed) ∧
        (x.st j u).latestConfirmed ∈ (x.st j u).tree) :
    (∃ (i : ℕ) (B : Block V), x.lbl i = Event.tick (S.P.proposer (q + 2)) (M.slotStart S.C (q + 2)) ∧
      (⟨S.P.proposer (q + 2), NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i) ∧
    ∀ (i : ℕ) (B : Block V), x.lbl i = Event.tick (S.P.proposer (q + 2)) (M.slotStart S.C (q + 2)) →
      (⟨S.P.proposer (q + 2), NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i →
      RootCollisionAtProposal M S A x (q + 2) B ∨
      (∀ v ∈ updaterAt M S A x (q + 2),
        (x.time (x.tickStep v (M.supportCutoff S.C (q + 2 + 1))) : ℝ) ≤ t →
        (x.tickOutput v (M.supportCutoff S.C (q + 2 + 1))).savedConfirmation (q + 2) =
          some B ∧
        M.ac_confirmed (x.tickOutput v (M.supportCutoff S.C (q + 2 + 1))) = B) := by
  have hΔ := one_le_Δ S
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔR : (1 : ℝ) ≤ (Δ S : ℝ) := by exact_mod_cast hΔ
  have hd : ((proposal_window_start S.C (q + 2) : ℤ) : ℝ) =
      4 * ((Δ S : ℝ) * (q : ℝ)) + 5 * (Δ S : ℝ) - 4 * ((Δ S : ℝ) * (S.C.k : ℝ)) := by
    rw [GoldilocksCorrectness.Proofs.Routines.proposal_window_start_eq S q, duty_window_start_real S (q + 1)]
    push_cast; ring
  have hss : ((M.slotStart S.C (q + 2) : ℕ) : ℝ) = 4 * ((Δ S : ℝ) * (q : ℝ)) + 8 * (Δ S : ℝ) := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (q + 2)]
    push_cast; ring
  have hsc : ((M.supportCutoff S.C (q + 2 + 1) : ℕ) : ℝ) = 4 * ((Δ S : ℝ) * (q : ℝ)) + 14 * (Δ S : ℝ) := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (q + 2 + 1),
      (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (q + 2 + 1),
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (q + 2 + 1)]
    push_cast; ring
  have hk0 : (0 : ℝ) ≤ (Δ S : ℝ) * (S.C.k : ℝ) := by positivity
  have hq0 : (0 : ℝ) ≤ (Δ S : ℝ) * (q : ℝ) := by positivity
  have hc1 : 1 ≤ M.slotStart S.C (q + 2) := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (q + 2)]
    have := Nat.mul_le_mul (show 4 ≤ 4 * Δ S by omega) (show 1 ≤ q + 2 by omega)
    omega
  -- the proposer is active at its tick to the slot's start, so it proposes
  have hm := (mem_activeThroughoutToTick_of_inside M F) R E hp.1 hc1 (by rw [hd, hss]; linarith)
    (by rw [hss, hsc]; linarith)
  refine ⟨(honest_proposer_proposes M F U) S A x R q E hm, fun ip B hl hsent => ?_⟩
  by_cases hcol : RootCollisionAtProposal M S A x (q + 2) B
  · exact Or.inl hcol
  right
  have hRootNew : ∀ B' ∈ (x.tickInput (S.P.proposer (q + 2)) (M.slotStart S.C (q + 2))).tree,
      B'.root ≠ B.root := fun B' hB' h => hcol ⟨B', hB', h⟩
  intro v hvU hvt
  have hvw : v ∈ A.activeThroughoutToTick x (Goldilocks.duty_window_start S.C (q + 2 + 1))
      (M.supportCutoff S.C (q + 2 + 1)) := hvU
  -- `v`'s tick `K` to the support cutoff of slot `q + 3`; a tick keeps the time
  obtain ⟨K, hlK, -⟩ := Activity.mem_activeThroughoutToTick.1 hvw
  have hKs : x.tickStep v (M.supportCutoff S.C (q + 2 + 1)) = K := (tickStep_eq_of_lbl M) x E hlK
  have hK1 : x.time (K + 1) = x.time K := R.time_keep K (by rw [hlK]; intro h; cases h)
  have huK1 : v ∉ A.corrupted (K + 1) := E.not_mem_corrupted_succ_of_tick hlK
  have hTO : x.tickOutput v (M.supportCutoff S.C (q + 2 + 1)) = x.st (K + 1) v := by
    unfold Trace.tickOutput; rw [hKs]
  have hKt := E.tick_active K v _ hlK
  have hvtK : x.time K ≤ (t : ℝ) := by rw [← hKs]; exact hvt
  -- the chain before slot `q + 3`, from `v`'s own update at a step by `t`, and its prefix before `q + 1`
  have hChain3 : ConfirmationsChainBefore M S A x s₀ (q + 2 + 1) := hChain (q + 2) K v hlK hvtK
  have hChainq : ConfirmationsChainBefore M S A x s₀ (q + 1) :=
    fun a b c d e f g h i => hChain3 a b c d e f g h (by omega)
  -- the invariant and the locks at the slots up to `q + 2`, whose updates are by `t`
  have hcq : ∀ s : ℕ, s ≤ q + 2 → M.supportCutoff S.C (s + 1) ≤ t := fun s hs =>
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
      (show s + 1 ≤ q + 2 + 1 by omega)) hqt
  have hi₁K : x.time i₁ < x.time K := by
    have h0 := hs.1
    have h1 := hKt.2.1
    rw [hss] at h0
    rw [hsc] at h1
    linarith
  -- the rows up to `v`'s tick
  have hRootsv : RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C (q + 2 + 1)))) :=
    (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) hvt hRoots
  have hAdvv : A.AdversaryFewerThanQuorumUntil x (quorum V)
      (x.time (x.tickStep v (M.supportCutoff S.C (q + 2 + 1)))) := hAdvQ.mono hvt
  have hSleepv : CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C (q + 2 + 1)) :=
    (GoldilocksCorrectness.Record.Statements.Executions.CommitteeSleepinessUntil.mono M) hSleepK hqt
  have hCachesv : ∀ (j : ℕ) (u : V), i₁ < j →
      x.time j ≤ x.time (x.tickStep v (M.supportCutoff S.C (q + 2 + 1))) →
      u ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j u) :=
    fun j u h₁ h₂ h₃ => hCaches j u h₁ (le_trans h₂ hvt) h₃
  -- the saved confirmation and the record after the update (`included_update_facts_q_until` at `v`)
  obtain ⟨hSaved, -, -, -, hLc⟩ := (included_update_facts_q_until M F U Fx) S A x R GST s₀ anchor i₁ H q ip B v
    E hNet hSkew hRedeliver Sy hΔs hRootsv hParent hAdvv hSleepv hAnchor hGST hChainq
    (fun s h1 h2 => hInv s h1 (hcq s h2)) (fun s h1 h2 => hLocks s h1 (hcq s h2)) hOld hCachesv ht₀ hs₀q hs hLk hHold hp
    hHoldP hl hsent
    hRootNew hvU
  -- every block of the chain before `q + 2` is `B` or an ancestor of it
  obtain ⟨hChainLeB, -⟩ := (honest_proposal_saved_at_until M F U Fx) S A x R GST s₀ anchor i₁ H q ip B v E hNet
    hSkew hRedeliver Sy hΔs hvU hRootsv hParent hAdvv hSleepv hAnchor hGST hChainq (fun s h1 h2 => hInv s h1 (hcq s h2))
    (fun s h1 h2 => hLocks s h1 (hcq s h2)) hOld hCachesv ht₀ hs₀q hs hLk hHold hp hHoldP hl hsent hRootNew
  -- the finalized block after the tick is on the chain before `q + 2`
  have hFb := (finalized_onHonestChainBefore_of_caches_until M F U Fx) S A x R s₀ i₁ H (q + 2) (K + 1) v v E
    hSkew hRootsv hAdvv hOld hChain3 hCachesv
    (by omega) hs.1 hvU (Nat.lt_succ_of_lt ((lt_of_time_lt M) x R hi₁K)) (by rw [hK1, hKs]) huK1
  -- the record after the tick is in its tree
  have hLT := (hLatest (K + 1) v (Nat.lt_succ_of_lt ((lt_of_time_lt M) x R hi₁K)) (by rw [hK1]; exact hvtK) huK1).2
  refine ⟨hSaved, ?_⟩
  rw [hTO] at hLc ⊢
  have hmem : B ∈ (M.fg_to_ac (x.st (K + 1) v)).tree :=
    ((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).2
      ⟨by rw [← hLc]; exact hLT, hChainLeB _ hFb⟩
  rw [F.rd.ac_confirmed_eq, hLc, if_pos hmem]

/-- `ConfirmedIncludedBetween`'s claim at the slot `q + 2`, with the lock invariant at slot `q`
(`hLk`): `included_q` with the support cutoff of slot `q + 3` at most `t` and the confirmed tips
read at steps at times at most `t`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold;
- `q`: the slot of the proposal is `q + 2`; `t`: the time up to which the confirmed tips are read.

Roots name blocks until `t`: the update of slot `q + 2` at the support cutoff of slot `q + 3`, at
most `t`, and, at a later slot `s'`, blocks held up to `M.supportCutoff S.C (s' + 1)`, at most
the time of the step read, at most `t` (`proposal_ancestor_of_tip_after_update`).

Caches up to `t`, with the roots: the caches are read at the steps the proof reads, at times at
most `t`. Named `_upTo`, since `included_q_until` is the landed form bounded in its roots only.

Read aloud: the inclusion's claim at the slot `q + 2`, with the confirmed tips read up to `t`. -/
theorem included_q_upTo (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ anchor i₁ H q t : ℕ)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x t)
    (hParent : ParentHeldAtDelivery M x)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) t)
    (hSleepK : CommitteeSleepinessUntil M S A x anchor t) (hAnchor : anchor ≤ x.time i₁)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀)
    (hChain : ConfirmationsChain M S A x s₀)
    (hInv : ∀ s : ℕ, s₀ < s →
      ChainInvFor M S A x (honestActiveAt M S A x s) (OnHonestChainBefore M S A x s₀ s) s)
    (hLocks : ∀ s : ℕ, s₀ < s → ∀ u ∈ honestActiveAt M S A x s,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ s) s u)
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    -- the honest voters of slots `q + 1` and `q + 2` are active through the sync delay after Lemma 12's read time of
    -- their slot, and the proposer of slot `q + 2` through the sync delay after one delay or one sync delay before its
    -- start (: `honest_proposal_saved_until`'s two clauses)
    (hHold : ∀ s' : ℕ, q + 1 ≤ s' → s' ≤ q + 2 → ∀ u ∈ honestActiveAt M S A x s', u ∈ S.P.committee s' →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hHoldP : S.P.proposer (q + 2) ∈ A.activeThroughout x ((M.slotStart S.C (q + 2) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C (q + 2) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hCaches : ∀ (j : ℕ) (u : V), x.time i₁ ≤ x.time j → x.time j ≤ t →
      u ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st (j + 1) u))
    (ht₀ : M.supportCutoff S.C (s₀ + 1) ≤ x.time i₁)
    (hs₀q : s₀ ≤ q) (hs : x.time i₁ < M.slotStart S.C (q + 2) ∧
      ∀ k : ℕ, x.lbl k = Event.tick (S.P.proposer (q + 2)) (M.slotStart S.C (q + 2)) → x.time i₁ < x.time k)
    -- the update of slot `q + 2` is at most `t`
    (hqt : M.supportCutoff S.C (q + 2 + 1) ≤ t)
    (hLk : ∀ u ∈ honestActiveAt M S A x q,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (q + 1)) q u)
    (hp : S.P.proposer (q + 2) ∈ A.activeThroughoutToTick x (Goldilocks.proposal_window_start S.C (q + 2))
        (M.supportCutoff S.C (q + 2 + 1)) ∧
      S.P.proposer (q + 2) ∉ A.corruptedAtTime x (M.supportCutoff S.C (q + 2 + 1)))
    (hLatest : ∀ (j : ℕ) (u : V), x.time i₁ ≤ x.time j → x.time j ≤ t →
      u ∉ A.corrupted j → (∃ σ : ℕ, x.lbl (x.tickStep u (M.supportCutoff S.C (σ + 1))) = Event.tick u (M.supportCutoff S.C (σ + 1)) ∧ x.tickStep u (M.supportCutoff S.C (σ + 1)) < j + 1 ∧
        OnHonestChainAt M S A x s₀ σ (x.st (j + 1) u).latestConfirmed) ∧
        (x.st (j + 1) u).latestConfirmed ∈ (x.st (j + 1) u).tree) :
    (∃ (i : ℕ) (B : Block V), x.lbl i = Event.tick (S.P.proposer (q + 2)) (M.slotStart S.C (q + 2)) ∧
      (⟨S.P.proposer (q + 2), NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i) ∧
    ∀ (i : ℕ) (B : Block V), x.lbl i = Event.tick (S.P.proposer (q + 2)) (M.slotStart S.C (q + 2)) →
      (⟨S.P.proposer (q + 2), NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i →
      RootCollisionAtProposal M S A x (q + 2) B ∨
      ((∀ v ∈ honestActiveAt M S A x (q + 2),
        (x.time (x.tickStep v (M.supportCutoff S.C (q + 2 + 1))) : ℝ) ≤ t →
        (x.tickOutput v (M.supportCutoff S.C (q + 2 + 1))).savedConfirmation (q + 2) =
          some B ∧
        M.ac_confirmed (x.tickOutput v (M.supportCutoff S.C (q + 2 + 1))) = B) ∧
      (∀ (v : V) (j s' : ℕ), A.HonestThroughTime x (x.time j) v → q + 2 ≤ s' → v ∈ honestActiveAt M S A x s' →
        x.tickStep v (M.supportCutoff S.C (s' + 1)) ≤ j → M.supportCutoff S.C (s' + 1) ≤ t → x.time j ≤ t →
        B.AncestorEq (M.ac_confirmed (x.st (j + 1) v)))) := by
  obtain ⟨h1, h2⟩ := (included_q_first_upTo M F U Fx) S A x R GST s₀ anchor i₁ H q t E hNet hSkew hRedeliver
    Sy hΔs hRoots hParent hAdvQ hSleepK hAnchor hGST
    (fun σ _ _ _ _ => confirmationsChainBefore_of_chain M S A x s₀ (σ + 1) hChain) (fun s h1 _ => hInv s h1)
    (fun s h1 _ => hLocks s h1) hOld hHold hHoldP ((row_of_succ_index M F) S A x R i₁ t (fun j u => CachesOnChain M S A x s₀ H (x.st j u)) E hCaches)
    ht₀ hs₀q hs hqt hLk hp
    ((row_of_succ_index M F) S A x R i₁ t (fun j u => (∃ σ : ℕ, x.lbl (x.tickStep u (M.supportCutoff S.C (σ + 1))) =
        Event.tick u (M.supportCutoff S.C (σ + 1)) ∧ x.tickStep u (M.supportCutoff S.C (σ + 1)) < j ∧
        OnHonestChainAt M S A x s₀ σ (x.st j u).latestConfirmed) ∧ (x.st j u).latestConfirmed ∈ (x.st j u).tree) E hLatest)
  refine ⟨h1, fun ip B hl hsent => (h2 ip B hl hsent).imp_right fun hfirst =>
    ⟨fun v hv => hfirst v ((honestActiveAt_subset_updaterAt M F) S A x R E (q + 2) hv), ?_⟩⟩
  -- the second conjunct: `B` is an ancestor of `v`'s confirmed tip after its update `K` of slot `s' + 1`
  -- (`proposal_ancestor_of_tip_after_update_before`), and that tip grows from `K` to `j`
  -- (`lem90_confirmed_monotone_before`, read through `confirmedMonotoneBetween_unfold`)
  intro v j s' hHon hqs hvA hkj hct hjt
  have hΔ := one_le_Δ S
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hvU : v ∈ updaterAt M S A x s' := (honestActiveAt_subset_updaterAt M F) S A x R E s' hvA
  have hvw : v ∈ A.activeThroughoutToTick x (Goldilocks.duty_window_start S.C (s' + 1))
      (M.supportCutoff S.C (s' + 1)) := hvU
  obtain ⟨K, hlK, -⟩ := Activity.mem_activeThroughoutToTick.1 hvw
  have hKs : x.tickStep v (M.supportCutoff S.C (s' + 1)) = K := (tickStep_eq_of_lbl M) x E hlK
  have hK1 : x.time (K + 1) = x.time K := R.time_keep K (by rw [hlK]; intro h; cases h)
  have hKj : K ≤ j := hKs ▸ hkj
  have hKt : x.time K ≤ (t : ℝ) := le_trans ((time_mono M) x R hKj) hjt
  have hK1t : x.time (x.tickStep v (M.supportCutoff S.C (s' + 1)) + 1) ≤ (t : ℝ) := by rw [hKs, hK1]; exact hKt
  have hKa := (E.tick_active K v _ hlK).2.1
  -- the phase's end is before `K`
  obtain ⟨-, hc1, -, hs1, -⟩ :=
    (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (s' + 1)
  obtain ⟨-, -, -, hs0, -⟩ :=
    (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S s'
  have hsq := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S hqs
  have hi₁K : x.time i₁ ≤ x.time K := by
    have h1 : ((M.slotStart S.C (q + 2) : ℕ) : ℝ) + 4 * Δ S + 2 * Δ S ≤
        ((M.supportCutoff S.C (s' + 1) : ℕ) : ℝ) := by
      exact_mod_cast (show M.slotStart S.C (q + 2) + 4 * Δ S + 2 * Δ S ≤ M.supportCutoff S.C (s' + 1) by omega)
    linarith [hs.1]
  -- an updater `u₀` of slot `q + 2` whose saved confirmation is `B`, and `v`'s own when it is an honest active
  -- validator of slot `q + 2`: at the slot `q + 2` itself, `v`'s update is `K`, by `t`; at a later slot, every tick to
  -- the support cutoff of slot `q + 3` is at a real time before `K` (`hSkew`), and the proposer is an updater
  have hsv : ∀ u ∈ updaterAt M S A x (q + 2), (x.time (x.tickStep u (M.supportCutoff S.C (q + 2 + 1))) : ℝ) ≤ t →
      (x.tickOutput u (M.supportCutoff S.C (q + 2 + 1))).savedConfirmation (q + 2) = some B :=
    fun u hu h => (hfirst u hu h).1
  obtain ⟨u₀, hu₀, hSaved₀, hSavedv⟩ : ∃ u₀ ∈ updaterAt M S A x (q + 2),
      (x.tickOutput u₀ (M.supportCutoff S.C (q + 2 + 1))).savedConfirmation (q + 2) = some B ∧
      (v ∈ honestActiveAt M S A x (q + 2) →
        (x.tickOutput v (M.supportCutoff S.C (q + 2 + 1))).savedConfirmation (q + 2) = some B) := by
    rcases Nat.eq_or_lt_of_le hqs with heq | hlt
    · subst heq
      exact ⟨v, hvU, hsv v hvU (by rw [hKs]; exact hKt), fun _ => hsv v hvU (by rw [hKs]; exact hKt)⟩
    · have hlate : ∀ u ∈ updaterAt M S A x (q + 2),
          (x.time (x.tickStep u (M.supportCutoff S.C (q + 2 + 1))) : ℝ) ≤ t := by
        intro u hu
        have huw : u ∈ A.activeThroughoutToTick x (Goldilocks.duty_window_start S.C (q + 2 + 1))
            (M.supportCutoff S.C (q + 2 + 1)) := hu
        obtain ⟨k, hk, -⟩ := Activity.mem_activeThroughoutToTick.1 huw
        rw [(tickStep_eq_of_lbl M) x E hk]
        have h1 := (E.tick_active k u _ hk).2.2
        have hmono := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
          (show q + 2 + 1 + 1 ≤ s' + 1 by omega)
        have hc := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_succ_eq M.toSlotLayout F.sched U) S
          (q + 2 + 1)
        have hcR : ((M.supportCutoff S.C (q + 2 + 1 + 1) : ℕ) : ℝ) = (M.supportCutoff S.C (q + 2 + 1) : ℕ) + 4 * Δ S := by
          rw [hc]; push_cast; ring
        have hmR : ((M.supportCutoff S.C (q + 2 + 1 + 1) : ℕ) : ℝ) ≤ (M.supportCutoff S.C (s' + 1) : ℕ) := by
          exact_mod_cast hmono
        linarith
      have hpU : S.P.proposer (q + 2) ∈ updaterAt M S A x (q + 2) :=
        Activity.mem_activeThroughoutToTick_of_le
          (by rw [GoldilocksCorrectness.Proofs.Routines.proposal_window_start_eq S q]
              exact GoldilocksCorrectness.Proofs.Routines.duty_window_start_mono S (by omega)) hp.1
      have hvq : v ∈ honestActiveAt M S A x (q + 2) → v ∈ updaterAt M S A x (q + 2) :=
        fun h => (honestActiveAt_subset_updaterAt M F) S A x R E (q + 2) h
      exact ⟨_, hpU, hsv _ hpU (hlate _ hpU), fun h => hsv v (hvq h) (hlate v (hvq h))⟩
  have hB := (proposal_ancestor_of_tip_after_update_before M F U Fx) S A x R GST s₀ anchor i₁ H q s' B u₀ v E hNet
    hSkew hRedeliver Sy hΔs ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) hK1t hRoots)
    hParent (hAdvQ.mono hK1t)
    ((GoldilocksCorrectness.Record.Statements.Executions.CommitteeSleepinessUntil.mono M) hSleepK hct) hAnchor hGST
    (confirmationsChainBefore_of_chain M S A x s₀ (s' + 1) hChain) (fun s h1 _ => hInv s h1) (fun s h1 _ => hLocks s h1)
    hOld (fun j' u h₁ h₂ h₃ => ((row_of_succ_index M F) S A x R i₁ t (fun j u => CachesOnChain M S A x s₀ H (x.st j u)) E hCaches) j' u h₁ (le_trans h₂ hK1t) h₃)
    (fun j' u h₁ h₂ h₃ => ((row_of_succ_index M F) S A x R i₁ t (fun j u => (∃ σ : ℕ, x.lbl (x.tickStep u (M.supportCutoff S.C (σ + 1))) =
        Event.tick u (M.supportCutoff S.C (σ + 1)) ∧ x.tickStep u (M.supportCutoff S.C (σ + 1)) < j ∧
        OnHonestChainAt M S A x s₀ σ (x.st j u).latestConfirmed) ∧ (x.st j u).latestConfirmed ∈ (x.st j u).tree) E hLatest) j' u h₁ (le_trans h₂ hK1t) h₃)
    hs₀q hs.1 hqs hu₀ hSaved₀ hSavedv hvA
  have hTO : x.tickOutput v (M.supportCutoff S.C (s' + 1)) = x.st (K + 1) v := by
    unfold Trace.tickOutput; rw [hKs]
  rw [hTO] at hB
  have hc0t : M.supportCutoff S.C (s₀ + 1) ≤ t :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
      (show s₀ + 1 ≤ q + 2 + 1 by omega)) hqt
  have hmono := (lem90_confirmed_monotone_before M F U Fx) S A x R s₀ H i₁ t E hRoots
    (hAdvQ.mono (max_le le_rfl (by exact_mod_cast hc0t))) hOld
    (fun σ _ _ _ _ => confirmationsChainBefore_of_chain M S A x s₀ (σ + 1) hChain) hLatest hCaches
  exact ancestorEq_trans hB (hmono v K j hKj hHon hi₁K hjt)

/-- `ConfirmedIncludedBetween`'s claim at the slot `q + 2`, with the lock invariant at slot `q`
(`hLk`), on the chain before the slots whose update is at most `t`: `included_q` with the support
cutoff of slot `q + 3` at most `t` and the confirmed tips read at steps at times at most `t`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold;
- `q`: the slot of the proposal is `q + 2`; `t`: the time up to which the confirmed tips are read.

Roots name blocks until `t`: the update of slot `q + 2` at the support cutoff of slot `q + 3`, at
most `t`, and, at a later slot `s'`, blocks held up to `M.supportCutoff S.C (s' + 1)`, at most
the time of the step read, at most `t` (`proposal_ancestor_of_tip_after_update`).

Caches up to `t`, with the roots: the caches are read at the steps the proof reads, at times at
most `t`. Named `_upTo`, since `included_q_until` is the landed form bounded in its roots only.

Read aloud: the inclusion's claim at the slot `q + 2`, with the confirmed tips read up to `t`, on
the chain before the slots updated by `t`. -/
theorem included_q_before (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ anchor i₁ H q t : ℕ)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x t)
    (hParent : ParentHeldAtDelivery M x)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) t)
    (hSleepK : CommitteeSleepinessUntil M S A x anchor t) (hAnchor : anchor ≤ x.time i₁)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀)
    -- the updaters' confirmations of the slots whose update some validator ran at a step by `t` form one chain
    (hChain : ∀ (σ k : ℕ) (u : V), x.lbl k = Event.tick u (M.supportCutoff S.C (σ + 1)) →
        x.time k ≤ t → ConfirmationsChainBefore M S A x s₀ (σ + 1))
    (hInv : ∀ s : ℕ, s₀ < s → M.supportCutoff S.C (s + 1) ≤ t →
      ChainInvFor M S A x (honestActiveAt M S A x s) (OnHonestChainBefore M S A x s₀ s) s)
    (hLocks : ∀ s : ℕ, s₀ < s → M.supportCutoff S.C (s + 1) ≤ t → ∀ u ∈ honestActiveAt M S A x s,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ s) s u)
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    -- the honest voters of slots `q + 1` and `q + 2` are active through the sync delay after Lemma 12's read time of
    -- their slot, and the proposer of slot `q + 2` through the sync delay after one delay or one sync delay before its
    -- start (: `honest_proposal_saved_until`'s two clauses)
    (hHold : ∀ s' : ℕ, q + 1 ≤ s' → s' ≤ q + 2 → ∀ u ∈ honestActiveAt M S A x s', u ∈ S.P.committee s' →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hHoldP : S.P.proposer (q + 2) ∈ A.activeThroughout x ((M.slotStart S.C (q + 2) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C (q + 2) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hCaches : ∀ (j : ℕ) (u : V), x.time i₁ ≤ x.time j → x.time j ≤ t →
      u ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st (j + 1) u))
    (ht₀ : M.supportCutoff S.C (s₀ + 1) ≤ x.time i₁)
    (hs₀q : s₀ ≤ q) (hs : x.time i₁ < M.slotStart S.C (q + 2) ∧
      ∀ k : ℕ, x.lbl k = Event.tick (S.P.proposer (q + 2)) (M.slotStart S.C (q + 2)) → x.time i₁ < x.time k)
    -- the update of slot `q + 2` is at most `t`
    (hqt : M.supportCutoff S.C (q + 2 + 1) ≤ t)
    (hLk : ∀ u ∈ honestActiveAt M S A x q,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (q + 1)) q u)
    (hp : HonestOpenerAt M S A x (q + 2))
    (hLatest : ∀ (j : ℕ) (u : V), x.time i₁ ≤ x.time j → x.time j ≤ t →
      u ∉ A.corrupted j → (∃ σ : ℕ, x.lbl (x.tickStep u (M.supportCutoff S.C (σ + 1))) = Event.tick u (M.supportCutoff S.C (σ + 1)) ∧ x.tickStep u (M.supportCutoff S.C (σ + 1)) < j + 1 ∧
        OnHonestChainAt M S A x s₀ σ (x.st (j + 1) u).latestConfirmed) ∧
        (x.st (j + 1) u).latestConfirmed ∈ (x.st (j + 1) u).tree) :
    (∃ (i : ℕ) (B : Block V), x.lbl i = Event.tick (S.P.proposer (q + 2)) (M.slotStart S.C (q + 2)) ∧
      (⟨S.P.proposer (q + 2), NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i) ∧
    ∀ (i : ℕ) (B : Block V), x.lbl i = Event.tick (S.P.proposer (q + 2)) (M.slotStart S.C (q + 2)) →
      (⟨S.P.proposer (q + 2), NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i →
      RootCollisionAtProposal M S A x (q + 2) B ∨
      ((∀ v ∈ honestActiveAt M S A x (q + 2),
        (x.time (x.tickStep v (M.supportCutoff S.C (q + 2 + 1))) : ℝ) ≤ t →
        (x.tickOutput v (M.supportCutoff S.C (q + 2 + 1))).savedConfirmation (q + 2) =
          some B ∧
        M.ac_confirmed (x.tickOutput v (M.supportCutoff S.C (q + 2 + 1))) = B) ∧
      (∀ (v : V) (j s' : ℕ), A.HonestThroughTime x (x.time j) v → q + 2 ≤ s' → v ∈ honestActiveAt M S A x s' →
        x.tickStep v (M.supportCutoff S.C (s' + 1)) ≤ j → M.supportCutoff S.C (s' + 1) ≤ t → x.time j ≤ t →
        B.AncestorEq (M.ac_confirmed (x.st (j + 1) v)))) := by
  -- the first conjunct: `included_q_first_upTo`, its rows from the state-after rows
  obtain ⟨h1, h2⟩ := (included_q_first_upTo M F U Fx) S A x R GST s₀ anchor i₁ H q t E hNet hSkew hRedeliver
    Sy hΔs hRoots hParent hAdvQ hSleepK hAnchor hGST hChain hInv hLocks hOld hHold hHoldP
    ((row_of_succ_index M F) S A x R i₁ t (fun j u => CachesOnChain M S A x s₀ H (x.st j u)) E hCaches)
    ht₀ hs₀q hs hqt hLk ⟨hp.1, fun h => hp.2 (Finset.mem_union_left _ (Finset.mem_union_left _ h))⟩
    ((row_of_succ_index M F) S A x R i₁ t (fun j u => (∃ σ : ℕ, x.lbl (x.tickStep u (M.supportCutoff S.C (σ + 1))) =
        Event.tick u (M.supportCutoff S.C (σ + 1)) ∧ x.tickStep u (M.supportCutoff S.C (σ + 1)) < j ∧
        OnHonestChainAt M S A x s₀ σ (x.st j u).latestConfirmed) ∧ (x.st j u).latestConfirmed ∈ (x.st j u).tree) E hLatest)
  refine ⟨h1, fun ip B hl hsent => (h2 ip B hl hsent).imp_right fun hfirst =>
    ⟨fun v hv => hfirst v ((honestActiveAt_subset_updaterAt M F) S A x R E (q + 2) hv), ?_⟩⟩
  -- the second conjunct: `B` is an ancestor of `v`'s confirmed tip after its update `K` of slot `s' + 1`
  -- (`proposal_ancestor_of_tip_after_update_before`), and that tip grows from `K` to `j`
  -- (`lem90_confirmed_monotone_before`, read through `confirmedMonotoneBetween_unfold`)
  intro v j s' hHon hqs hvA hkj hct hjt
  have hcm : ∀ a b : ℕ, a ≤ b → M.supportCutoff S.C a ≤ M.supportCutoff S.C b := fun a b h =>
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S h
  have hp' : S.P.proposer (q + 2) ∈ A.activeThroughoutToTick x (Goldilocks.proposal_window_start S.C (q + 2))
        (M.supportCutoff S.C (q + 2 + 1)) ∧
      S.P.proposer (q + 2) ∉ A.corruptedAtTime x (M.supportCutoff S.C (q + 2 + 1)) :=
    ⟨hp.1, fun h => hp.2 (Finset.mem_union_left _ (Finset.mem_union_left _ h))⟩
  have hΔ := one_le_Δ S
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hvU : v ∈ updaterAt M S A x s' := (honestActiveAt_subset_updaterAt M F) S A x R E s' hvA
  have hvw : v ∈ A.activeThroughoutToTick x (Goldilocks.duty_window_start S.C (s' + 1))
      (M.supportCutoff S.C (s' + 1)) := hvU
  obtain ⟨K, hlK, -⟩ := Activity.mem_activeThroughoutToTick.1 hvw
  have hKs : x.tickStep v (M.supportCutoff S.C (s' + 1)) = K := (tickStep_eq_of_lbl M) x E hlK
  have hK1 : x.time (K + 1) = x.time K := R.time_keep K (by rw [hlK]; intro h; cases h)
  have hKj : K ≤ j := hKs ▸ hkj
  have hKt : x.time K ≤ (t : ℝ) := le_trans ((time_mono M) x R hKj) hjt
  have hK1t : x.time (x.tickStep v (M.supportCutoff S.C (s' + 1)) + 1) ≤ (t : ℝ) := by rw [hKs, hK1]; exact hKt
  have hKa := (E.tick_active K v _ hlK).2.1
  -- the phase's end is before `K`
  obtain ⟨-, hc1, -, hs1, -⟩ :=
    (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (s' + 1)
  obtain ⟨-, -, -, hs0, -⟩ :=
    (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S s'
  have hsq := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S hqs
  have hi₁K : x.time i₁ ≤ x.time K := by
    have h1 : ((M.slotStart S.C (q + 2) : ℕ) : ℝ) + 4 * Δ S + 2 * Δ S ≤
        ((M.supportCutoff S.C (s' + 1) : ℕ) : ℝ) := by
      exact_mod_cast (show M.slotStart S.C (q + 2) + 4 * Δ S + 2 * Δ S ≤ M.supportCutoff S.C (s' + 1) by omega)
    linarith [hs.1]
  -- an updater `u₀` of slot `q + 2` whose saved confirmation is `B`, and `v`'s own when it is an honest active
  -- validator of slot `q + 2`: at the slot `q + 2` itself, `v`'s update is `K`, by `t`; at a later slot, every tick to
  -- the support cutoff of slot `q + 3` is at a real time before `K` (`hSkew`), and the proposer is an updater
  have hsv : ∀ u ∈ updaterAt M S A x (q + 2), (x.time (x.tickStep u (M.supportCutoff S.C (q + 2 + 1))) : ℝ) ≤ t →
      (x.tickOutput u (M.supportCutoff S.C (q + 2 + 1))).savedConfirmation (q + 2) = some B :=
    fun u hu h => (hfirst u hu h).1
  obtain ⟨u₀, hu₀, hSaved₀, hSavedv⟩ : ∃ u₀ ∈ updaterAt M S A x (q + 2),
      (x.tickOutput u₀ (M.supportCutoff S.C (q + 2 + 1))).savedConfirmation (q + 2) = some B ∧
      (v ∈ honestActiveAt M S A x (q + 2) →
        (x.tickOutput v (M.supportCutoff S.C (q + 2 + 1))).savedConfirmation (q + 2) = some B) := by
    rcases Nat.eq_or_lt_of_le hqs with heq | hlt
    · subst heq
      exact ⟨v, hvU, hsv v hvU (by rw [hKs]; exact hKt), fun _ => hsv v hvU (by rw [hKs]; exact hKt)⟩
    · have hlate : ∀ u ∈ updaterAt M S A x (q + 2),
          (x.time (x.tickStep u (M.supportCutoff S.C (q + 2 + 1))) : ℝ) ≤ t := by
        intro u hu
        have huw : u ∈ A.activeThroughoutToTick x (Goldilocks.duty_window_start S.C (q + 2 + 1))
            (M.supportCutoff S.C (q + 2 + 1)) := hu
        obtain ⟨k, hk, -⟩ := Activity.mem_activeThroughoutToTick.1 huw
        rw [(tickStep_eq_of_lbl M) x E hk]
        have h1 := (E.tick_active k u _ hk).2.2
        have hmono := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
          (show q + 2 + 1 + 1 ≤ s' + 1 by omega)
        have hc := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_succ_eq M.toSlotLayout F.sched U) S
          (q + 2 + 1)
        have hcR : ((M.supportCutoff S.C (q + 2 + 1 + 1) : ℕ) : ℝ) = (M.supportCutoff S.C (q + 2 + 1) : ℕ) + 4 * Δ S := by
          rw [hc]; push_cast; ring
        have hmR : ((M.supportCutoff S.C (q + 2 + 1 + 1) : ℕ) : ℝ) ≤ (M.supportCutoff S.C (s' + 1) : ℕ) := by
          exact_mod_cast hmono
        linarith
      have hpU : S.P.proposer (q + 2) ∈ updaterAt M S A x (q + 2) :=
        Activity.mem_activeThroughoutToTick_of_le
          (by rw [GoldilocksCorrectness.Proofs.Routines.proposal_window_start_eq S q]
              exact GoldilocksCorrectness.Proofs.Routines.duty_window_start_mono S (by omega)) hp'.1
      have hvq : v ∈ honestActiveAt M S A x (q + 2) → v ∈ updaterAt M S A x (q + 2) :=
        fun h => (honestActiveAt_subset_updaterAt M F) S A x R E (q + 2) h
      exact ⟨_, hpU, hsv _ hpU (hlate _ hpU), fun h => hsv v (hvq h) (hlate v (hvq h))⟩
  have hB := (proposal_ancestor_of_tip_after_update_before M F U Fx) S A x R GST s₀ anchor i₁ H q s' B u₀ v E hNet
    hSkew hRedeliver Sy hΔs ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) hK1t hRoots)
    hParent (hAdvQ.mono hK1t)
    ((GoldilocksCorrectness.Record.Statements.Executions.CommitteeSleepinessUntil.mono M) hSleepK hct) hAnchor hGST
    (hChain s' K v hlK hKt)
    (fun s h1 h2 => hInv s h1 (le_trans (hcm _ _ (by omega)) hct))
    (fun s h1 h2 => hLocks s h1 (le_trans (hcm _ _ (by omega)) hct))
    hOld (fun j' u h₁ h₂ h₃ => ((row_of_succ_index M F) S A x R i₁ t (fun j u => CachesOnChain M S A x s₀ H (x.st j u)) E hCaches) j' u h₁ (le_trans h₂ hK1t) h₃)
    (fun j' u h₁ h₂ h₃ => ((row_of_succ_index M F) S A x R i₁ t (fun j u => (∃ σ : ℕ, x.lbl (x.tickStep u (M.supportCutoff S.C (σ + 1))) =
        Event.tick u (M.supportCutoff S.C (σ + 1)) ∧ x.tickStep u (M.supportCutoff S.C (σ + 1)) < j ∧
        OnHonestChainAt M S A x s₀ σ (x.st j u).latestConfirmed) ∧ (x.st j u).latestConfirmed ∈ (x.st j u).tree) E hLatest) j' u h₁ (le_trans h₂ hK1t) h₃)
    hs₀q hs.1 hqs hu₀ hSaved₀ hSavedv hvA
  have hTO : x.tickOutput v (M.supportCutoff S.C (s' + 1)) = x.st (K + 1) v := by
    unfold Trace.tickOutput; rw [hKs]
  rw [hTO] at hB
  have hc0t : M.supportCutoff S.C (s₀ + 1) ≤ t :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
      (show s₀ + 1 ≤ q + 2 + 1 by omega)) hqt
  have hmono := (lem90_confirmed_monotone_before M F U Fx) S A x R s₀ H i₁ t E hRoots
    (hAdvQ.mono (max_le le_rfl (by exact_mod_cast hc0t))) hOld
    hChain hLatest hCaches
  exact ancestorEq_trans hB (hmono v K j hKj hHon hi₁K hjt)

/-- `ConfirmedIncludedBetween`'s claim at the slot `q + 2`, with the lock invariant at slot `q`
(`hLk`): `included_q` with the support cutoff of slot `q + 3` at most `t` and the confirmed tips
read at steps at times at most `t`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold;
- `q`: the slot of the proposal is `q + 2`; `t`: the time up to which the confirmed tips are read.

Roots name blocks until `t`: the update of slot `q + 2` at the support cutoff of slot `q + 3`, at
most `t`, and, at a later slot `s'`, blocks held up to `M.supportCutoff S.C (s' + 1)`, at most
the time of the step read, at most `t` (`proposal_ancestor_of_tip_after_update`).

It is `included_q_upTo` with the caches restricted to the steps it reads.

Read aloud: the inclusion's claim at the slot `q + 2`, with the confirmed tips read up to `t`. -/
theorem included_q_until (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ anchor i₁ H q t : ℕ)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x t)
    (hParent : ParentHeldAtDelivery M x)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) t)
    (hSleepK : CommitteeSleepinessUntil M S A x anchor t) (hAnchor : anchor ≤ x.time i₁)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀)
    (hChain : ConfirmationsChain M S A x s₀)
    (hInv : ∀ s : ℕ, s₀ < s →
      ChainInvFor M S A x (honestActiveAt M S A x s) (OnHonestChainBefore M S A x s₀ s) s)
    (hLocks : ∀ s : ℕ, s₀ < s → ∀ u ∈ honestActiveAt M S A x s,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ s) s u)
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    -- the honest voters of slots `q + 1` and `q + 2` are active through the sync delay after Lemma 12's read time of
    -- their slot, and the proposer of slot `q + 2` through the sync delay after one delay or one sync delay before its
    -- start (: `honest_proposal_saved_until`'s two clauses)
    (hHold : ∀ s' : ℕ, q + 1 ≤ s' → s' ≤ q + 2 → ∀ u ∈ honestActiveAt M S A x s', u ∈ S.P.committee s' →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hHoldP : S.P.proposer (q + 2) ∈ A.activeThroughout x ((M.slotStart S.C (q + 2) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C (q + 2) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hCaches : ∀ (j : ℕ) (u : V), x.time i₁ ≤ x.time j → u ∉ A.corrupted j →
      CachesOnChain M S A x s₀ H (x.st (j + 1) u))
    (ht₀ : M.supportCutoff S.C (s₀ + 1) ≤ x.time i₁)
    -- the phase's end is at or before every tick of the proposer of slot `q + 2` to the slot's start (T-R86-1, the
    -- form `included_q_upTo` takes: with `ΔClockAhead > 0` that tick can be before the slot's start)
    (hs₀q : s₀ ≤ q) (hs : x.time i₁ < M.slotStart S.C (q + 2) ∧
      ∀ k : ℕ, x.lbl k = Event.tick (S.P.proposer (q + 2)) (M.slotStart S.C (q + 2)) → x.time i₁ < x.time k)
    -- the update of slot `q + 2` is at most `t`
    (hqt : M.supportCutoff S.C (q + 2 + 1) ≤ t)
    (hLk : ∀ u ∈ honestActiveAt M S A x q,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (q + 1)) q u)
    (hp : S.P.proposer (q + 2) ∈ A.activeThroughoutToTick x (Goldilocks.proposal_window_start S.C (q + 2))
        (M.supportCutoff S.C (q + 2 + 1)) ∧
      S.P.proposer (q + 2) ∉ A.corruptedAtTime x (M.supportCutoff S.C (q + 2 + 1)))
    (hLatest : ∀ (j : ℕ) (u : V), x.time i₁ ≤ x.time j → u ∉ A.corrupted j → (∃ σ : ℕ, x.lbl (x.tickStep u (M.supportCutoff S.C (σ + 1))) = Event.tick u (M.supportCutoff S.C (σ + 1)) ∧ x.tickStep u (M.supportCutoff S.C (σ + 1)) < j + 1 ∧
        OnHonestChainAt M S A x s₀ σ (x.st (j + 1) u).latestConfirmed) ∧
        (x.st (j + 1) u).latestConfirmed ∈ (x.st (j + 1) u).tree) :
    (∃ (i : ℕ) (B : Block V), x.lbl i = Event.tick (S.P.proposer (q + 2)) (M.slotStart S.C (q + 2)) ∧
      (⟨S.P.proposer (q + 2), NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i) ∧
    ∀ (i : ℕ) (B : Block V), x.lbl i = Event.tick (S.P.proposer (q + 2)) (M.slotStart S.C (q + 2)) →
      (⟨S.P.proposer (q + 2), NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i →
      RootCollisionAtProposal M S A x (q + 2) B ∨
      ((∀ v ∈ honestActiveAt M S A x (q + 2),
        (x.time (x.tickStep v (M.supportCutoff S.C (q + 2 + 1))) : ℝ) ≤ t →
        (x.tickOutput v (M.supportCutoff S.C (q + 2 + 1))).savedConfirmation (q + 2) =
          some B ∧
        M.ac_confirmed (x.tickOutput v (M.supportCutoff S.C (q + 2 + 1))) = B) ∧
      (∀ (v : V) (j s' : ℕ), A.HonestThroughTime x (x.time j) v → q + 2 ≤ s' → v ∈ honestActiveAt M S A x s' →
        x.tickStep v (M.supportCutoff S.C (s' + 1)) ≤ j → M.supportCutoff S.C (s' + 1) ≤ t → x.time j ≤ t →
        B.AncestorEq (M.ac_confirmed (x.st (j + 1) v)))) := by
  -- `included_q_upTo` with its rows restricted to `t`
  exact (included_q_upTo M F U Fx) S A x R GST s₀ anchor i₁ H q t E hNet hSkew hRedeliver Sy hΔs hRoots hParent
    hAdvQ hSleepK hAnchor hGST hChain hInv hLocks hOld hHold hHoldP (fun j u h₁ _ h₃ => hCaches j u h₁ h₃) ht₀ hs₀q
    hs hqt hLk hp (fun j u h₁ _ h₃ => hLatest j u h₁ h₃)

/-- `ConfirmedIncludedAfterHealing`'s claim at the slot `q + 2`, with the lock invariant at slot `q`
(`hLk`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold;
- `q`: the slot of the proposal is `q + 2`.

Roots name blocks among everything honest validators hold (`RootsNameBlocks`, not bounded): the
conclusion's last clause is for every slot `s' ≥ q + 2` and every later step, and at slot `s'` the
proof reads blocks held up to `M.supportCutoff S.C (s' + 1)`
(`proposal_ancestor_of_tip_after_update`), so no time in the theorem's own parameters bounds the
reading. It is `included_q_until` read at every time `t`: the support cutoff of slot
`q + 3` for the first parts, and the later of that and the time of the step read for the last.

Read aloud: the inclusion's claim at the slot `q + 2`, with the lock invariant at slot `q`. -/
theorem included_q (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ anchor i₁ H q : ℕ)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocks M A x)
    (hParent : ParentHeldAtDelivery M x)
    (hAdvQ : ∀ t : ℕ, A.AdversaryFewerThanQuorumUntil x (quorum V) t)
    (hSleepK : CommitteeSleepiness M S A x anchor) (hAnchor : anchor ≤ x.time i₁)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀)
    (hChain : ConfirmationsChain M S A x s₀)
    (hInv : ∀ s : ℕ, s₀ < s →
      ChainInvFor M S A x (honestActiveAt M S A x s) (OnHonestChainBefore M S A x s₀ s) s)
    (hLocks : ∀ s : ℕ, s₀ < s → ∀ u ∈ honestActiveAt M S A x s,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ s) s u)
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    -- the honest voters of slots `q + 1` and `q + 2` are active through the sync delay after Lemma 12's read time of
    -- their slot, and the proposer of slot `q + 2` through the sync delay after one delay or one sync delay before its
    -- start (: `honest_proposal_saved_until`'s two clauses)
    (hHold : ∀ s' : ℕ, q + 1 ≤ s' → s' ≤ q + 2 → ∀ u ∈ honestActiveAt M S A x s', u ∈ S.P.committee s' →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hHoldP : S.P.proposer (q + 2) ∈ A.activeThroughout x ((M.slotStart S.C (q + 2) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C (q + 2) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hCaches : ∀ (j : ℕ) (u : V), x.time i₁ ≤ x.time j → u ∉ A.corrupted j →
      CachesOnChain M S A x s₀ H (x.st (j + 1) u))
    (ht₀ : M.supportCutoff S.C (s₀ + 1) ≤ x.time i₁)
    -- the phase's end is at or before every tick of the proposer of slot `q + 2` to the slot's start (T-R86-1, the
    -- form `included_q_upTo` takes: with `ΔClockAhead > 0` that tick can be before the slot's start)
    (hs₀q : s₀ ≤ q) (hs : x.time i₁ < M.slotStart S.C (q + 2) ∧
      ∀ k : ℕ, x.lbl k = Event.tick (S.P.proposer (q + 2)) (M.slotStart S.C (q + 2)) → x.time i₁ < x.time k)
    (hLk : ∀ u ∈ honestActiveAt M S A x q,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (q + 1)) q u)
    (hp : S.P.proposer (q + 2) ∈ A.activeThroughoutToTick x (Goldilocks.proposal_window_start S.C (q + 2))
        (M.supportCutoff S.C (q + 2 + 1)) ∧
      S.P.proposer (q + 2) ∉ A.corruptedAtTime x (M.supportCutoff S.C (q + 2 + 1)))
    (hLatest : ∀ (j : ℕ) (u : V), x.time i₁ ≤ x.time j → u ∉ A.corrupted j → (∃ σ : ℕ, x.lbl (x.tickStep u (M.supportCutoff S.C (σ + 1))) = Event.tick u (M.supportCutoff S.C (σ + 1)) ∧ x.tickStep u (M.supportCutoff S.C (σ + 1)) < j + 1 ∧
        OnHonestChainAt M S A x s₀ σ (x.st (j + 1) u).latestConfirmed) ∧
        (x.st (j + 1) u).latestConfirmed ∈ (x.st (j + 1) u).tree) :
    (∃ (i : ℕ) (B : Block V), x.lbl i = Event.tick (S.P.proposer (q + 2)) (M.slotStart S.C (q + 2)) ∧
      (⟨S.P.proposer (q + 2), NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i) ∧
    ∀ (i : ℕ) (B : Block V), x.lbl i = Event.tick (S.P.proposer (q + 2)) (M.slotStart S.C (q + 2)) →
      (⟨S.P.proposer (q + 2), NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i →
      RootCollisionAtProposal M S A x (q + 2) B ∨
      ((∀ v ∈ honestActiveAt M S A x (q + 2),
        (x.tickOutput v (M.supportCutoff S.C (q + 2 + 1))).savedConfirmation (q + 2) =
          some B ∧
        M.ac_confirmed (x.tickOutput v (M.supportCutoff S.C (q + 2 + 1))) = B) ∧
      (∀ (v : V) (j s' : ℕ), A.HonestThroughTime x (x.time j) v → q + 2 ≤ s' → v ∈ honestActiveAt M S A x s' →
        x.tickStep v (M.supportCutoff S.C (s' + 1)) ≤ j →
        B.AncestorEq (M.ac_confirmed (x.st (j + 1) v)))) := by
  have key := fun (t : ℕ) (ht : M.supportCutoff S.C (q + 2 + 1) ≤ t) =>
    (included_q_until M F U Fx) S A x R GST s₀ anchor i₁ H q t E hNet hSkew hRedeliver Sy hΔs
      ((rootsNameBlocksUntil_of_rootsNameBlocks M) x F R E t hRoots) hParent (hAdvQ _) (committeeSleepinessUntil_of_committeeSleepiness M S A x _ _ hSleepK) hAnchor
      hGST hChain hInv hLocks hOld hHold hHoldP hCaches ht₀ hs₀q hs ht hLk hp hLatest
  obtain ⟨h1, h2⟩ := key (M.supportCutoff S.C (q + 2 + 1)) le_rfl
  refine ⟨h1, fun ip B hl hsent => ?_⟩
  by_cases hcol : RootCollisionAtProposal M S A x (q + 2) B
  · exact Or.inl hcol
  right
  refine ⟨fun v hv => ?_, fun v j s' hHon hqs hvA hlt => ?_⟩
  · -- a natural number at least the time of `v`'s tick to the cutoff bounds the read
    obtain ⟨T, hT⟩ := exists_nat_ge (x.time (x.tickStep v (M.supportCutoff S.C (q + 2 + 1))))
    rcases (key (max (M.supportCutoff S.C (q + 2 + 1)) T) (le_max_left _ _)).2 ip B hl hsent
      with h | ⟨h, -⟩
    · exact absurd h hcol
    · exact h v hv (le_trans hT (by exact_mod_cast le_max_right _ _))
  · -- a natural number at least the time of `j` and the support cutoff of slot `s' + 1` bounds the read (no floor
    -- or ceiling of a time)
    obtain ⟨T, hT⟩ := exists_nat_ge (x.time j)
    rcases (key (max (max (M.supportCutoff S.C (q + 2 + 1)) T) (M.supportCutoff S.C (s' + 1)))
        (le_trans (le_max_left _ _) (le_max_left _ _))).2 ip B hl hsent with h | ⟨-, h⟩
    · exact absurd h hcol
    · exact h v j s' hHon hqs hvA hlt (le_max_right _ _)
        (le_trans hT (by exact_mod_cast le_trans (le_max_right _ _) (le_max_left _ _)))

/-- **Kit fact, the lock invariant at the healed slot.** The discharge of `hLocks₀` from the
premises of Lemma 81: when committee sleepiness holds from `anchor` at or before the start of slot
`s₀ + 1`, `B₀`'s slot is at least `s₀`, `HonestChainExtends` holds for `B₀` at slot `s₀` at the
honest active validators of slot `s₀`, and every updater of slot `s₀` saves `B₀`, then every honest
active validator of slot `s₀` satisfies the lock invariant at slot `s₀` for the chain before
`s₀ + 1`.

Why: `liveLocksOnFamilyAt_base` puts every live entry on `B₀` or an ancestor of it, and `B₀` is on
the chain at slot `s₀` (some honest committee member of slot `s₀` is an updater that saved it).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `anchor`: the
  time from which committee sleepiness holds; `B₀`: the healed block; `u`: the validator.

Read aloud: at the healed slot, every honest active validator's live locks are on the chain. -/
theorem base_locks_on_chain (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ anchor : ℕ) (B₀ : Block V) (u : V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSleepK : CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C (s₀ + 1))) (hAnchor : anchor ≤ M.slotStart S.C (s₀ + 1))
    (hB₀slot : s₀ ≤ B₀.slot)
    (hBase : HonestChainExtends M S A x (honestActiveAt M S A x s₀) B₀ s₀)
    (hBaseSaved : ∀ v ∈ updaterAt M S A x s₀,
      (x.tickOutput v (M.supportCutoff S.C (s₀ + 1))).savedConfirmation s₀ = some B₀)
    (hu : u ∈ honestActiveAt M S A x s₀) :
    LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (s₀ + 1)) s₀ u := by
  have hCom := (committee_majority_of_sleepiness M F) S A x anchor s₀ hSleepK hAnchor (by omega)
  obtain ⟨u₀, hu₀⟩ : (S.P.committee s₀ ∩ honestActiveAt M S A x s₀).Nonempty :=
    Finset.card_pos.1 (by omega)
  have hv₀ := (honestActiveAt_subset_updaterAt M F) S A x R E s₀ (Finset.mem_inter.1 hu₀).2
  -- an outcome of `u`'s tick at the vote time of slot `s₀ + 1`, from an awake state: it revoked the
  -- locks there
  intro n₃ sent₃ hrun₃ hA₃ e he hl
  obtain ⟨D, hD, heD⟩ := (liveLocksOnFamilyAt_base M F U) S A x R s₀ B₀ u n₃ E hB₀slot
    ((locksRevoked_of_voteTime_outcome M F U) S A x R E (s₀ + 1) u n₃ sent₃ hrun₃ hA₃)
    (hBase.2.1 u hu n₃ sent₃ hrun₃ hA₃) e he hl
  exact ⟨D, ⟨s₀, Nat.lt_succ_self s₀, le_rfl, u₀, hv₀, B₀, hBaseSaved u₀ hv₀, hD⟩, heD⟩

/-- The lock invariant at a slot `q ≥ s₀` for the chain before `q + 1`: from `hLocks` when
`q > s₀`, from `hLocks₀` when `q = s₀`; `hLocks` read up to slot `q`.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `q`: the
  slot.

Read aloud: the lock invariant at a slot `q ≥ s₀` for the chain before `q + 1`, from the lock
invariants read up to slot `q`. -/
theorem locks_before_of_locks_le (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (s₀ q : ℕ)
    (hLocks : ∀ s : ℕ, s₀ < s → s ≤ q → ∀ u ∈ honestActiveAt M S A x s,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ s) s u)
    (hLocks₀ : ∀ u ∈ honestActiveAt M S A x s₀,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (s₀ + 1)) s₀ u)
    (hs₀q : s₀ ≤ q) :
    ∀ u ∈ honestActiveAt M S A x q,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (q + 1)) q u := by
  intro u hu
  rcases Nat.lt_or_eq_of_le hs₀q with hlt | heq
  · intro n' sent hrun hA e he hl
    obtain ⟨D, ⟨s'', hs'', hAt⟩, heD⟩ := hLocks q hlt le_rfl u hu n' sent hrun hA e he hl
    exact ⟨D, ⟨s'', Nat.lt_succ_of_lt hs'', hAt⟩, heD⟩
  · subst heq
    exact hLocks₀ u hu

/-- **The per-validator export of the inclusion.** The proof; the audited
statement is in `Statements/Executions/ConfirmedTipStatements.lean`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold;
- `s`: the slot; `B`: the proposal; `v`: the updater.

Roots name blocks until `M.supportCutoff S.C (s + 1)`: `included_update_facts_q` at `q := s − 2`.

Caches up to `M.supportCutoff S.C (s + 1)`: `included_update_facts_q_until` at `q := s − 2`.

Read aloud: with the lock invariant also at the healed slot, and the honest voters of slots `s - 1` and `s`
and the proposer active for the sync delay after the times the synchrony condition reads them, every updater of the slot confirms the
honest proposal fast, locks it, records it, and keeps no live lock off its chain, reading nothing
after the slot's update. -/
theorem lem90_included_update_facts_until (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ anchor i₁ H s : ℕ) (B : Block V) (v : V)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C (s + 1)))))
    (hParent : ParentHeldAtDelivery M x)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (x.time (x.tickStep v (M.supportCutoff S.C (s + 1)))))
    (hSleepK : CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C (s + 1))) (hAnchor : anchor ≤ x.time i₁)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀) (ht₀ : M.supportCutoff S.C (s₀ + 1) ≤ x.time i₁)
    (hChain : ConfirmationsChainBefore M S A x s₀ (s - 1))
    (hInv : ∀ s' : ℕ, s₀ < s' → s' ≤ s →
      ChainInvFor M S A x (honestActiveAt M S A x s')
        (OnHonestChainBefore M S A x s₀ s') s')
    (hLocks : ∀ s' : ℕ, s₀ < s' → s' ≤ s → ∀ u ∈ honestActiveAt M S A x s',
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ s') s' u)
    (hLocks₀ : ∀ u ∈ honestActiveAt M S A x s₀,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (s₀ + 1)) s₀ u)
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x.time i₁ ≤ x.time j → x.time j ≤ x.time (x.tickStep v (M.supportCutoff S.C (s + 1))) →
      u ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j u))
    (hs : x.time i₁ < M.slotStart S.C s ∧
      ∀ k : ℕ, x.lbl k = Event.tick (S.P.proposer s) (M.slotStart S.C s) → x.time i₁ < x.time k)
    (hp : S.P.proposer s ∈ A.activeThroughoutToTick x (Goldilocks.proposal_window_start S.C s)
        (M.supportCutoff S.C (s + 1)) ∧
      S.P.proposer s ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)))
    -- the honest voters of slots `s - 1` and `s` are active through the sync delay after Lemma 12's read time of
    -- their slot, and the proposer through the sync delay after `M.slotStart S.C s - max (Δ S) Δs`
    --, the amended row `hHoldP`, under)
    (hHold : ∀ s' : ℕ, s ≤ s' + 1 → s' ≤ s → ∀ u ∈ honestActiveAt M S A x s', u ∈ S.P.committee s' →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hHoldP : S.P.proposer s ∈ A.activeThroughout x ((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick (S.P.proposer s) (M.slotStart S.C s) ∧
      (⟨S.P.proposer s, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i)
    (hNoCollision : ¬ RootCollisionAtProposal M S A x s B)
    (hv : v ∈ updaterAt M S A x s) :
    (x.tickOutput v (M.supportCutoff S.C (s + 1))).savedConfirmation s = some B ∧
      B ∈ (x.tickOutput v (M.supportCutoff S.C (s + 1))).fastBlocks ∧
      (∃ e ∈ (x.tickOutput v (M.supportCutoff S.C (s + 1))).lockEntries,
        M.le_B e = B ∧ M.le_d e = S.C.t_ (s + S.C.k) + 5 * S.C.Δ) ∧
      (∀ e ∈ (x.tickOutput v (M.supportCutoff S.C (s + 1))).lockEntries,
        M.is_live (x.stateBefore (M.supportCutoff S.C (s + 1)) v)
          ((M.supportCutoff S.C (s + 1) : ℕ) : Int) e = true → e.B.AncestorEq B) ∧
      (x.tickOutput v (M.supportCutoff S.C (s + 1))).latestConfirmed = B := by
  obtain ⟨hs2, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.slot_after_healed_round M.toSlotLayout F.sched) S
    s₀ s (by exact_mod_cast lt_of_le_of_lt ht₀ hs.1)
  obtain ⟨q, rfl⟩ : ∃ q, s = q + 2 := ⟨s - 2, by omega⟩
  obtain ⟨ip, hl, hsent⟩ := hPropose
  exact (included_update_facts_q_until M F U Fx) S A x R GST s₀ anchor i₁ H q ip B v E hNet hSkew hRedeliver Sy hΔs
    hRoots hParent hAdvQ hSleepK hAnchor hGST (by rwa [show q + 2 - 1 = q + 1 by omega] at hChain) hInv hLocks hOld
    (fun j u h₁ h₂ h₃ => hCaches j u ((time_mono M) x R h₁.le) h₂ h₃) ht₀ (by omega) hs
    ((locks_before_of_locks_le M F) S A x s₀ q (fun s' h₁ h₂ => hLocks s' h₁ (by omega)) hLocks₀ (by omega))
    (fun s' h1 h2 => hHold s' (by omega) h2) hp hHoldP hl hsent (fun B' hB' hr => hNoCollision ⟨B', hB', hr⟩) hv

/-- **The per-validator export of the inclusion.** The proof; the audited
statement is in `Statements/Executions/ConfirmedTipStatements.lean`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold;
- `s`: the slot; `B`: the proposal; `v`: the updater.

Roots name blocks until `M.supportCutoff S.C (s + 1)`: `included_update_facts_q` at `q := s − 2`.

It is `lem90_included_update_facts_until` with the caches restricted to the steps it reads.

Read aloud: with the lock invariant also at the healed slot, and the honest voters of slots `s - 1` and `s`
and the proposer active for the sync delay after the times the synchrony condition reads them, every updater of the slot confirms the
honest proposal fast, locks it, records it, and keeps no live lock off its chain. -/
theorem lem90_included_update_facts (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ anchor i₁ H s : ℕ) (B : Block V) (v : V)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C (s + 1)))))
    (hParent : ParentHeldAtDelivery M x)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (x.time (x.tickStep v (M.supportCutoff S.C (s + 1)))))
    (hSleepK : CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C (s + 1))) (hAnchor : anchor ≤ x.time i₁)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀) (ht₀ : M.supportCutoff S.C (s₀ + 1) ≤ x.time i₁)
    (hChain : ConfirmationsChain M S A x s₀)
    (hInv : ∀ s : ℕ, s₀ < s →
      ChainInvFor M S A x (honestActiveAt M S A x s) (OnHonestChainBefore M S A x s₀ s) s)
    (hLocks : ∀ s : ℕ, s₀ < s → ∀ u ∈ honestActiveAt M S A x s,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ s) s u)
    (hLocks₀ : ∀ u ∈ honestActiveAt M S A x s₀,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (s₀ + 1)) s₀ u)
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x.time i₁ ≤ x.time j → u ∉ A.corrupted j →
      CachesOnChain M S A x s₀ H (x.st j u))
    (hs : x.time i₁ < M.slotStart S.C s ∧
      ∀ k : ℕ, x.lbl k = Event.tick (S.P.proposer s) (M.slotStart S.C s) → x.time i₁ < x.time k)
    (hp : S.P.proposer s ∈ A.activeThroughoutToTick x (Goldilocks.proposal_window_start S.C s)
        (M.supportCutoff S.C (s + 1)) ∧
      S.P.proposer s ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)))
    -- the honest voters of slots `s - 1` and `s` are active through the sync delay after Lemma 12's read time of
    -- their slot, and the proposer through the sync delay after `M.slotStart S.C s - max (Δ S) Δs`
    --, the amended row `hHoldP`, under)
    (hHold : ∀ s' : ℕ, s ≤ s' + 1 → s' ≤ s → ∀ u ∈ honestActiveAt M S A x s', u ∈ S.P.committee s' →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hHoldP : S.P.proposer s ∈ A.activeThroughout x ((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick (S.P.proposer s) (M.slotStart S.C s) ∧
      (⟨S.P.proposer s, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i)
    (hNoCollision : ¬ RootCollisionAtProposal M S A x s B)
    (hv : v ∈ updaterAt M S A x s) :
    (x.tickOutput v (M.supportCutoff S.C (s + 1))).savedConfirmation s = some B ∧
      B ∈ (x.tickOutput v (M.supportCutoff S.C (s + 1))).fastBlocks ∧
      (∃ e ∈ (x.tickOutput v (M.supportCutoff S.C (s + 1))).lockEntries,
        M.le_B e = B ∧ M.le_d e = S.C.t_ (s + S.C.k) + 5 * S.C.Δ) ∧
      (∀ e ∈ (x.tickOutput v (M.supportCutoff S.C (s + 1))).lockEntries,
        M.is_live (x.stateBefore (M.supportCutoff S.C (s + 1)) v)
          ((M.supportCutoff S.C (s + 1) : ℕ) : Int) e = true → e.B.AncestorEq B) ∧
      (x.tickOutput v (M.supportCutoff S.C (s + 1))).latestConfirmed = B := by
  obtain ⟨hs2, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.slot_after_healed_round M.toSlotLayout F.sched) S
    s₀ s (by exact_mod_cast lt_of_le_of_lt ht₀ hs.1)
  obtain ⟨q, rfl⟩ : ∃ q, s = q + 2 := ⟨s - 2, by omega⟩
  obtain ⟨ip, hl, hsent⟩ := hPropose
  exact (included_update_facts_q M F U Fx) S A x R GST s₀ anchor i₁ H q ip B v E hNet hSkew hRedeliver Sy hΔs
    hRoots hParent hAdvQ hSleepK hAnchor hGST hChain hInv hLocks hOld hCaches ht₀ (by omega) hs
    ((locks_before_of_locks_le M F) S A x s₀ q (fun s' h₁ _ => hLocks s' h₁) hLocks₀ (by omega))
    (fun s' h1 h2 => hHold s' (by omega) h2) hp hHoldP hl hsent (fun B' hB' hr => hNoCollision ⟨B', hB', hr⟩) hv

/-- **Lemma 90, inclusion, read up to a time `t`**. The proof; the audited statement is
in `Statements/Executions/ConfirmedTipStatements.lean`.

Why `htE`: at a slot `s`, the proof reads the proposer's caches and record at its tick to the start
of slot `s`, and `hCaches` and `hLatest` speak only of steps at times at least `x[i₁].time`; so the
slots read are those starting at or after `tE`, each of them starts after `x[i₁].time`, and the
proposer's tick to its start is at a step whose time is at least `x[i₁].time`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₁`: the step at the phase's end; `H`: the threshold; `t`: the time up to
  which the inclusion is read.
- `tE`: the time from which the slots are read.

Roots name blocks until `t`: `included_q_until` at every slot whose update, the support cutoff of
the next slot, is at most `t`, reading the confirmed tips at steps at times at most `t`.

On the chain before the slots whose update some validator ran at a step by `t`, the invariant and
the locks at the slots whose update is at most `t`, the records on the chain at slots whose update
the validator ran at an earlier step: `included_q_before`.

Caches up to `t`, with the roots: `included_q_upTo` at every slot whose update is at most `t`.
Named `_upTo`, since `lem90_confirmed_included_until` is the landed form bounded in its roots
only.

Read aloud: for the slots starting at or after `tE`, each of which starts after `x[i₁].time` and
whose proposer ticks to its start at a step whose time is at least `x[i₁].time`, when
the confirmations of the slots updated by `t` form one chain, up to `t` the honest proposer's block
is what every honest active validator of its slot confirms, and stays confirmed, unless the proposer
already held a block with its root. -/
theorem lem90_confirmed_included_before (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ anchor i₁ H t tE : ℕ)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x t)
    (hParent : ParentHeldAtDelivery M x)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) t)
    (hSleepK : CommitteeSleepinessUntil M S A x anchor t) (hAnchor : anchor ≤ x.time i₁)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀) (ht₀ : M.supportCutoff S.C (s₀ + 1) ≤ x.time i₁)
    (htE : ∀ s : ℕ, tE ≤ M.slotStart S.C s → x.time i₁ < M.slotStart S.C s ∧
      ∀ k : ℕ, x.lbl k = Event.tick (S.P.proposer s) (M.slotStart S.C s) → x.time i₁ < x.time k)
    -- the updaters' confirmations of the slots whose update some validator ran at a step by `t` form one chain
    (hChain : ∀ (σ k : ℕ) (u : V), x.lbl k = Event.tick u (M.supportCutoff S.C (σ + 1)) →
        x.time k ≤ t → ConfirmationsChainBefore M S A x s₀ (σ + 1))
    (hInv : ∀ s : ℕ, s₀ < s → M.supportCutoff S.C (s + 1) ≤ t →
      ChainInvFor M S A x (honestActiveAt M S A x s) (OnHonestChainBefore M S A x s₀ s) s)
    (hLocks : ∀ s : ℕ, s₀ < s → M.supportCutoff S.C (s + 1) ≤ t → ∀ u ∈ honestActiveAt M S A x s,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ s) s u)
    (hLocks₀ : ∀ u ∈ honestActiveAt M S A x s₀,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (s₀ + 1)) s₀ u)
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    -- at every slot whose next slot starts at or after `tE` and whose update is at most `t`, the honest active
    -- committee members are active through the sync delay after Lemma 12's read time of the slot; at every slot of
    -- the window with an honest opener, its proposer through the sync delay after one delay or one sync delay before
    -- its start
    (hHold : ∀ s' : ℕ, tE ≤ M.slotStart S.C (s' + 1) → M.supportCutoff S.C (s' + 1) ≤ t →
      ∀ u ∈ honestActiveAt M S A x s', u ∈ S.P.committee s' →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hHoldP : ∀ s : ℕ, tE ≤ M.slotStart S.C s → M.supportCutoff S.C (s + 1) ≤ t → HonestOpenerAt M S A x s →
      S.P.proposer s ∈ A.activeThroughout x ((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ)
        (((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hCaches : ∀ (j : ℕ) (u : V), x.time i₁ ≤ x.time j → x.time j ≤ t →
      u ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st (j + 1) u))
    (hLatest : ∀ (j : ℕ) (u : V), x.time i₁ ≤ x.time j → x.time j ≤ t →
      u ∉ A.corrupted j → (∃ σ : ℕ, x.lbl (x.tickStep u (M.supportCutoff S.C (σ + 1))) = Event.tick u (M.supportCutoff S.C (σ + 1)) ∧ x.tickStep u (M.supportCutoff S.C (σ + 1)) < j + 1 ∧
        OnHonestChainAt M S A x s₀ σ (x.st (j + 1) u).latestConfirmed) ∧
        (x.st (j + 1) u).latestConfirmed ∈ (x.st (j + 1) u).tree)
    : ConfirmedIncludedBetween M S A x tE t := by
  rw [(GoldilocksCorrectness.Record.Proofs.View.confirmedIncludedBetween_unfold M x)]
  intro s hsE hst hp
  have hs := htE s hsE
  obtain ⟨hs2, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.slot_after_healed_round M.toSlotLayout F.sched) S s₀ s (by exact_mod_cast lt_of_le_of_lt ht₀ hs.1)
  obtain ⟨q, rfl⟩ : ∃ q, s = q + 2 := ⟨s - 2, by omega⟩
  -- the slot lemma also concludes the saved confirmation, which the conclusion no longer reads
  -- (b (a))
  exact ((included_q_before M F U Fx) S A x R GST s₀ anchor i₁ H q t E hNet hSkew hRedeliver Sy hΔs hRoots
    hParent hAdvQ hSleepK hAnchor hGST hChain hInv hLocks hOld
    (fun s' h1 h2 => hHold s' (le_trans hsE ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout
        F.sched) S (by omega))) (le_trans ((supportCutoff_le_of_le M F) S (by omega)) hst))
    (hHoldP (q + 2) hsE hst hp) hCaches ht₀ (by omega) hs
    hst ((locks_before_of_locks_le M F) S A x s₀ q
      (fun s h₁ h₂ => hLocks s h₁ (le_trans ((supportCutoff_le_of_le M F) S (by omega)) hst)) hLocks₀
      (by omega)) hp hLatest).imp_right
    fun h i B hl hsent => (h i B hl hsent).imp_right fun h' => ⟨fun v hv ht => (h'.1 v hv ht).2, h'.2⟩

end GoldilocksCorrectness.Record.Proofs.Executions

