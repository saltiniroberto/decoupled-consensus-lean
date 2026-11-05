module
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.EligibleBlockVoteStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.ConfirmationCompatibilityStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.LockProvenanceStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.WakeStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.ConfirmationStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma33
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma42
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.TickUpdateState
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ACStore
public import GoldilocksCorrectness.Statements.Executions.EligibleBlockVoteStatements
public import GoldilocksCorrectness.Statements.Executions.ConfirmationCompatibilityStatements
public import GoldilocksCorrectness.Statements.Executions.LockProvenanceStatements
public import GoldilocksCorrectness.Proofs.Executions.Lemma33
public import GoldilocksCorrectness.Proofs.Executions.Lemma42
public import GoldilocksCorrectness.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma45, over a model

The theorem of `GoldilocksCorrectness/Proofs/Executions/Lemma45.lean` over a model `M` whose facts
`F` hold, for an execution `x` of `protocolOf M S`: Lemma 45, a lock whose window is after `GST` is
extended by the next slot's honest votes. The page's routine-level theorems are the facts' fields or
have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff viewFreeze
  dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_succ_le_slotStart
  dutyWindowStart_succ_le_supportCutoff lockDeadline_injective one_le_Δ slotStart_eq
  slotStart_mono supportCutoff_eq supportCutoff_lt_of_lt viewFreeze_eq voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (compatible_of_ancestorEq_both)

open GoldilocksCorrectness.Proofs.Routines (earlySupporterOf_of_keepsVotes expireLocks_keepsVotes)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor ConfirmationUpdated EarlySupporterOf
  VoterTreeAt)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (acObject)
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn expireLocks)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_trans compatible_of_ancestorEq_compatible)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

-- An index `x[i]` into an execution, and `x[i][v]` into a configuration, has the valid-index
-- predicate `fun _ _ => True`; this rule, local to the file, proves it at once, as in
-- `Lemma21.lean`.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- The spec's duty window of slot `s` starts before `0` when the model's slot start plus one delay
is less than `4 · Δ S · k`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `S`: the setup; `s`: the slot.

Read aloud: in the first slots the duty window starts before time `0`. -/
theorem duty_window_start_neg_of_lt (U : UniformSchedule M.toSlotLayout) (S : Setup V) {s : ℕ}
    (h : M.slotStart S.C s + Δ S < 4 * Δ S * S.C.k) : duty_window_start S.C s < 0 := by
  have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_cast M.toSlotLayout F.sched U) S s
  have h2 := GoldilocksCorrectness.Proofs.Routines.Δ_cast S
  have h' : S.C.t_ s + S.C.Δ < 4 * S.C.Δ * (S.C.k : Int) := by
    rw [← h1, ← h2]
    exact_mod_cast h
  rw [GoldilocksCorrectness.Proofs.Routines.duty_window_start_eq]
  exact Int.sub_neg_of_lt h'

/-- A window ending at `b`, `b` at least the view freeze of slot `s₀`, and starting `max (Δ S) Δs`
before it starts strictly after the duty window's start of slot `s₀ + 1`, or the spec's duty window
of slot `s₀ + 1` starts before `0`. The clock bounds are nonnegative (`hA`, `hB`, as `EnvFactsBy` has them): without them `hΔs` bounds
nothing.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `S`: the setup; `hΔs`: the sync
  delay's bound; `s₀`: the slot; `b`: the window's end.

Read aloud: every one-delay window ending at or after a slot's view freeze starts after the next
slot's duty window starts, or that duty window starts before time `0`. -/
theorem dutyWindowStart_succ_lt_window_or_neg (U : UniformSchedule M.toSlotLayout) (S : Setup V)
    {Δs : ℕ} {ΔClockAhead ΔClockBehind : ℝ} (hA : 0 ≤ ΔClockAhead) (hB : 0 ≤ ΔClockBehind)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) {s₀ b : ℕ} (hb : M.viewFreeze S.C s₀ ≤ b) :
    M.dutyWindowStart S.C (s₀ + 1) < b - max (Δ S) Δs ∨ duty_window_start S.C (s₀ + 1) < 0 := by
  have hkm : max (Δ S) Δs + 3 * Δ S < 4 * Δ S * S.C.k := by
    have h' : ((max (Δ S) Δs + 3 * Δ S : ℕ) : ℝ) < ((4 * Δ S * S.C.k : ℕ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast h'
  obtain ⟨-, -, hvf, hs1, hΔ⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S s₀
  have hdwe := U.dutyWindowStart_eq S (s₀ + 1)
  have hm1 := le_max_left (Δ S) Δs
  by_cases hlt : M.slotStart S.C (s₀ + 1) + Δ S < 4 * Δ S * S.C.k
  · -- the duty window of slot `s₀ + 1` starts before `0`
    exact Or.inr ((duty_window_start_neg_of_lt M F U) S hlt)
  · -- it starts at `slotStart (s₀ + 1) + Δ S − 4 Δ S k`, more than one delay before `b − max (Δ S) Δs` by `hΔs`
    left
    omega

/-- The deleted `cutoff_update_of_tick` (false over the trace) with the hypothesis that `v` is active at the support cutoff `c` of slot
`s + 1` added: over the trace a validator not active at `c` has no tick to `c`, and the node state
its tick would start from is its initial state, while its state before `c` need not be awake for
slot `s + 1`. When `v` is active at `c` and the node state its tick at `c` starts from has a wake
time `τ` at most the duty window's start of slot `s + 1`, some node state `n'` is what the
confirmation update of slot `s + 1` from `v`'s node state before the cutoff leaves
(`ConfirmationUpdated`), and satisfies every property `Q` that every outcome of the tick, under
`AwakeFor`, satisfies.

Why: the tick has an outcome (`cutoff_tick_outcome_of_active`), under `AwakeFor`; at the node
invariant and the cutoff's time (`cutoff_state_facts_of_active`), that outcome is what the update
leaves (the field `tick_supportCutoff_confirmation` of `F.tk2`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `hWS`: the trace is
  wake-shaped; `s`: the slot before the update's; `v`: the validator; `τ`: the time since which
  the tick's input state is awake; `Q`: the property of the outcome.

Read aloud: the confirmation update that the tick, at the support cutoff of slot `s + 1`, of a
validator active there runs leaves a node state with every property every outcome of that tick
has. -/
theorem cutoff_update_of_tick_of_active (U : UniformSchedule M.toSlotLayout) {S : Setup V}
    {A : Activity V}
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
 (s : ℕ) (v : V) (τ : Time)
    -- `v` is active at the support cutoff of slot `s + 1`
    (hv : v ∈ A.activeAtTime x (M.supportCutoff S.C (s + 1)))
    -- the tick at the support cutoff starts from a node state awake since `τ`
    (hτ : (x.tickInput v (M.supportCutoff S.C (s + 1))).awakeSince = some τ)
    -- `τ` is at most the duty window's start of slot `s + 1`
    (hτle : τ ≤ duty_window_start S.C (s + 1)) (Q : M.N → Prop)
    -- every outcome of the tick, from a node state awake for slot `s + 1`, has `Q`
    (hQ : ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (M.supportCutoff S.C (s + 1)))
        ((M.supportCutoff S.C (s + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) (s + 1) → Q n') :
    ∃ n' : M.N, ConfirmationUpdated M S.C S.P (x.tickInput v (M.supportCutoff S.C (s + 1)))
      ((M.supportCutoff S.C (s + 1) : ℕ) : Int) (s + 1) n' ∧ Q n' := by
  obtain ⟨n', sent, hrun, hA⟩ :=
    (cutoff_tick_outcome_of_active M F U) x R E s v τ hv hτ hτle
  obtain ⟨-, hInv, -, hcut, hsl⟩ :=
    (cutoff_state_facts_of_active M F U) x R E s v τ hv hτ hτle
  have hCU := F.tk2.tick_supportCutoff_confirmation S.C S.P S.X _ _ n' sent hrun hInv hcut
    (by rw [hsl]; exact hA)
  rw [hsl] at hCU
  exact ⟨n', hCU, hQ n' sent hrun hA⟩

/-- **The revocation an outcome of the tick at a vote time ran.** An outcome `(n', sent)` of `u`'s
tick at the vote time of slot `s`, from the state that tick starts from (`x.tickInput u (M.voteTime
S.C s)`), awake for slot `s`, leaves
what the revocation of the locks of slot `s` at that time leaves (`LocksRevoked`).

Why: the field `tick_voteTime_locks` of `F.tk2`, at the node invariant of that state (Lemma 11), the spec's slot of the vote time being `s` (`U`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot; `u`: the validator;
  `n'`, `sent`: the outcome.

Read aloud: an outcome of the tick at the vote time of slot `s`, from a state awake for the slot,
ran the revocation of the locks of slot `s`. (Moved from `RoundKit.lean`, F-78-3.) -/
theorem locksRevoked_of_voteTime_outcome (U : UniformSchedule M.toSlotLayout) (S : Setup V)
    (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (s : ℕ) (u : V) (n' : M.N)
    (sent : List (NamedObject V))
    (hrun : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput u (M.voteTime S.C s))
      ((M.voteTime S.C s : ℕ) : Int))
    (hA : AwakeFor M S.C (x.tickInput u (M.voteTime S.C s)) s) :
    GoldilocksCorrectness.Record.Statements.Routines.LocksRevoked M S.P (x.tickInput u (M.voteTime S.C s)) ((M.voteTime S.C s : ℕ) : Int) s
      n' := by
  have hΔ := one_le_Δ S
  have hss : M.slotStart S.C (s + 1) = M.slotStart S.C s + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U),
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s,
      Nat.mul_add, Nat.mul_one]
  have hv := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s
  have hsl : S.C.slot ((M.voteTime S.C s : ℕ) : Int) = s := by
    rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast,
      ← (GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U)]
    exact (GoldilocksCorrectness.Record.Proofs.Routines.slot_eq_of_mem M.toSlotLayout F.sched) S
      (by omega) (by omega)
  have hInv := (lem11_node_invariantCore_of_run M F S x R (x.tickStep u (M.voteTime S.C s)) u).1
  have hR := F.tk2.tick_voteTime_locks_of_core S.C S.P S.X _ _ n' sent hrun hInv
    (by rw [hsl]; exact (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_cast M.toSlotLayout
      F.sched U) S s)
    (by rw [hsl]; exact hA)
  rw [hsl] at hR
  exact hR

section WindowsKit

open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_le_supportCutoff
  dutyWindowStart_succ_le_supportCutoff duty_window_start_mono one_le_Δ slotStart_cast
  slotStart_eq slotStart_mono slot_le_of_t_lt supportCutoff_cast supportCutoff_eq
  supportCutoff_lt_of_lt t_lt_of_lt viewFreeze_eq voteTime_eq)
open GoldilocksCorrectness.Proofs.Routines (duty_window_start_le_dutyWindowStart)

variable {S : Setup V} {A : Activity V}

/-! ## The kit: windows read off a duty test (moved from `Lemma43.lean`, F-78-3) -/

/-- **A window read off a duty test.** When `v` ticks to `c₁` at the step `k` from a node state awake
since `τ ≤ a`, ticks to `b` at a step `kb` no earlier than `k`, and is active after every step from
`k + 1` to `kb`, then `v` is active from its tick to a clock value at most `a` up to its tick to `b`
(`A.activeThroughoutToTick x a b`).

Why: the node state `v`'s tick to `c₁` starts from is awake since the initial time and `v` has been
awake after every step up to that tick, or `v` ticked to the clock value `τ` after its last restart
and has been awake since (`awake_of_tickInput_awakeSince_of_tick`); `v` is outside the adversary set
at its tick to `c₁` (`not_mem_corrupted_of_tick`), so at every step before it (`corrupted_mono`).

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `v`: the validator; `a`:
  the clock value the window opens at; `c₁`, `k`: the duty test's tick and its step; `τ`: the time
  since which the state that tick starts from is awake; `b`, `kb`: the window's last tick and its step.

Read aloud: a validator that passed a duty test opening at `a` at one tick, and stayed active from
that tick to a later one, is active from `a` up to the later tick. -/
theorem mem_activeThroughoutToTick_of_awakeSince_steps
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {v : V} {a : ℤ} {c₁ b k kb : ℕ} {τ : Time}
    -- `v` ticks to `c₁` at `k`, from a node state awake since `τ`, at most `a`
    (hk : x.lbl k = Event.tick v c₁)
    (hτ : (x.tickInput v c₁).awakeSince = some τ) (hτa : τ ≤ a)
    -- `v` ticks to `b` at `kb`, no earlier than `k`, and is active after every step between
    (hkb : x.lbl kb = Event.tick v b) (hkkb : k ≤ kb)
    (hact : ∀ j : ℕ, k < j → j ≤ kb → v ∈ A.active j) :
    v ∈ A.activeThroughoutToTick x a b := by
  have hkS : x.tickStep v c₁ = k := (tickStep_eq_of_lbl M) x E hk
  have hvk : v ∉ A.corrupted k := E.not_mem_corrupted_of_tick hk
  rcases (awake_of_tickInput_awakeSince_of_tick M F) x R E ⟨k, hk⟩ hτ with
    ⟨-, hall⟩ | ⟨k₁, τ', hk₁, hl₁, hτ', hawk⟩
  · refine Activity.mem_activeThroughoutToTick.2 ⟨kb, hkb, Or.inl fun i hi => ?_⟩
    rcases Nat.lt_or_ge k i with hki | hik
    · exact hact i hki hi
    · rw [hkS] at hall
      exact Activity.mem_active.2 ⟨hall i hik, fun hc => hvk (E.corrupted_mono i k hik hc)⟩
  · rw [hkS] at hk₁ hawk
    refine Activity.mem_activeThroughoutToTick.2
      ⟨kb, hkb, Or.inr ⟨k₁, by omega, τ', by rw [hτ']; exact hτa, hl₁, fun i h1 h2 => ?_⟩⟩
    rcases Nat.lt_or_ge k i with hki | hik
    · exact hact i hki h2
    · exact Activity.mem_active.2 ⟨hawk i h1 hik, fun hc => hvk (E.corrupted_mono i k hik hc)⟩

/-- **A window read off a duty test, extended by a reader.** When `v` is active from its tick to a
clock value at most `tStart` up to its tick to `c` (`A.activeThroughoutToTick x tStart c`), and ticks
to a value `c₁` with `tStart < c₁ ≤ c` from a node state awake since `τ ≤ a`, then `v` is active from
its tick to a clock value at most `a` up to its tick to `c`.

Why: the tick to `c₁` is no later than the tick to `c` (`clock_mono`, `tick_unique`), and the reader's
own opening tick, to a value at most `tStart < c₁`, is before it (`clock_mono` at that opening tick, where
`v` is active), so the reader covers every step after the tick to `c₁`
(`mem_activeThroughoutToTick_of_awakeSince_steps`).

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `v`: the validator; `a`:
  the clock value the new window opens at; `tStart`, `c`: the reader's window; `c₁`, `k`: the duty
  test's tick and its step; `τ`: the time since which the state that tick starts from is awake.

Read aloud: a validator active up to its tick to `c` from an earlier opening, which passed a duty test
opening at `a` at a tick in between, is active from `a` up to its tick to `c`. -/
theorem mem_activeThroughoutToTick_of_awakeSince_of_window
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {v : V} {a : ℤ} {tStart c₁ c k : ℕ} {τ : Time}
    -- `v` is active from its tick to a value at most `tStart` up to its tick to `c`
    (hv : v ∈ A.activeThroughoutToTick x (tStart : ℤ) c)
    -- `v` ticks to `c₁` at `k`, with `tStart < c₁ ≤ c`, from a node state awake since `τ`, at most `a`
    (hk : x.lbl k = Event.tick v c₁) (htc : tStart < c₁) (hc₁c : c₁ ≤ c)
    (hτ : (x.tickInput v c₁).awakeSince = some τ) (hτa : τ ≤ a) :
    v ∈ A.activeThroughoutToTick x a c := by
  obtain ⟨k', hk', hcase⟩ := Activity.mem_activeThroughoutToTick.1 hv
  -- the tick to `c₁` is no later than the tick to `c`
  have hkk' : k ≤ k' := by
    by_contra h
    have hb := E.clock_mono k' k v c c₁ (by omega) (E.not_mem_corrupted_of_tick hk) (Or.inl hk')
      (Or.inl hk)
    have hcc : c₁ = c := le_antisymm hc₁c hb
    rw [hcc] at hk
    exact absurd (E.tick_unique k' k v c hk' hk) (by omega)
  refine (mem_activeThroughoutToTick_of_awakeSince_steps M F) x R E hk hτ hτa hk' hkk'
    fun j hj1 hj2 => ?_
  rcases hcase with h | ⟨k₀, hk₀k', c₀, hc₀, hk₀, h⟩
  · exact h j hj2
  · refine h j ?_ hj2
    -- the reader's opening tick, to `c₀ ≤ tStart < c₁`, comes before the tick to `c₁`
    by_contra hlt
    have hvk₀ : v ∉ A.corrupted k₀ := (Activity.mem_active.1 (h k₀ le_rfl hk₀k')).2
    have hcc := E.clock_mono k k₀ v c₁ c₀ (by omega) hvk₀ (Or.inl hk) (Or.inl hk₀)
    have : (c₁ : ℤ) ≤ tStart := le_trans (by exact_mod_cast hcc) hc₀
    omega

/-- **Lemma 31's windows, read off the duty test of an update.** When `u` ticks to the support cutoff
of slot `s' + 1` from a node state awake since a time at most the duty window's start of slot `s' + 1`,
then `u` ticks to the view freeze of slot `s'` at a step `kF`, is active after every step up to `kF`
whose real time is at least `ΔClockAhead` before `M.viewFreeze S.C s' − max (3 * Δ S) Δs`, and is
active for the sync delay after the view freeze of slot `s'` less one delay or one sync delay
(Lemma 31's `hwin₁` and `hv₁₀`).

Why: the duty test gives `u` active from its tick to a clock value at most that start up to the tick
(`mem_activeThroughoutToTick_of_awakeSince_steps`); that start is `4 * Δ S * S.C.k − 2 * Δ S` before the
view freeze of slot `s'`, more than `max (3 * Δ S) Δs` and both clock bounds by `hΔs`; the view freeze
is one delay before the cutoff, more than both clock bounds (`mem_activeThroughoutToTick_of_inside`,
`mem_activeThroughout_of_mem_activeThroughoutToTick`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `s'`: the slot; `k₁`: the
  step of `u`'s tick to the support cutoff of slot `s' + 1`; `u`: the validator; `τ`: the time since
  which the state that tick starts from is awake.

Read aloud: a validator that passed the duty test of slot `s' + 1` at its update is active through
the windows Lemma 31 reads at slot `s'`. -/
theorem lem31_windows_of_duty_test (U : UniformSchedule M.toSlotLayout)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    {Δs : ℕ} (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {s' k₁ : ℕ} {u : V} {τ : Time}
    -- the sync delay is at most the view freeze of slot `s'`
    (hcb : Δs ≤ M.viewFreeze S.C s')
    -- `u` ticks to the support cutoff of slot `s' + 1` at `k₁`, from a node state awake since `τ`,
    -- at most the duty window's start of slot `s' + 1`
    (hk₁ : x.lbl k₁ = Event.tick u (M.supportCutoff S.C (s' + 1)))
    (hτ : (x.tickInput u (M.supportCutoff S.C (s' + 1))).awakeSince = some τ)
    (hτle : τ ≤ duty_window_start S.C (s' + 1)) :
    ∃ kF : ℕ, x.lbl kF = Event.tick u (M.viewFreeze S.C s') ∧ kF ≤ k₁ ∧
      (∀ i : ℕ, (M.viewFreeze S.C s' : ℝ) - max (3 * Δ S) Δs - ΔClockAhead ≤ x.time i → i ≤ kF →
        u ∈ A.active i) ∧
      u ∈ A.activeThroughout x ((M.viewFreeze S.C s') - (max (Δ S) Δs))
        (((M.viewFreeze S.C s') - (max (Δ S) Δs)) + Δs) := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hk2 := S.C.k_ge_two
  obtain ⟨-, hc0, hf0, hs0, hΔ⟩ :=
    (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S s'
  obtain ⟨-, hc1, -, -, -⟩ :=
    (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (s' + 1)
  -- the duty window's start of slot `s' + 1`, an integer, is `4 * Δ S * S.C.k − 2 * Δ S` before the
  -- view freeze of slot `s'`
  have hDZ : duty_window_start S.C (s' + 1) + 4 * (Δ S : ℤ) * (S.C.k : ℤ) =
      ((M.viewFreeze S.C s' : ℕ) : ℤ) + 2 * (Δ S : ℤ) := by
    have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_cast M.toSlotLayout F.sched U)
      S (s' + 1)
    have h2 := GoldilocksCorrectness.Proofs.Routines.Δ_cast S
    rw [GoldilocksCorrectness.Proofs.Routines.duty_window_start_eq, ← h1, ← h2]
    rw [hs0, hf0]
    push_cast
    ring
  have hDR : ((duty_window_start S.C (s' + 1) : ℤ) : ℝ) + 4 * (Δ S : ℝ) * (S.C.k : ℝ) =
      (M.viewFreeze S.C s' : ℝ) + 2 * (Δ S : ℝ) := by exact_mod_cast hDZ
  -- the sync bound over the natural numbers
  have h8 : max (Δ S) Δs + 3 * Δ S < 4 * Δ S * S.C.k := by
    have hR : ((max (Δ S) Δs + 3 * Δ S : ℕ) : ℝ) < ((4 * Δ S * S.C.k : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast hR
  have h9 := Nat.mul_le_mul_left (4 * Δ S) hk2
  have hmax1 : max (Δ S) Δs = Δ S ∨ max (Δ S) Δs = Δs := max_choice _ _
  have hmax3 : max (3 * Δ S) Δs = 3 * Δ S ∨ max (3 * Δ S) Δs = Δs := max_choice _ _
  have hm1 := le_max_left (Δ S) Δs
  have hm1' := le_max_right (Δ S) Δs
  have hm3 := le_max_left (3 * Δ S) Δs
  have hm3' := le_max_right (3 * Δ S) Δs
  have hN3 : max (3 * Δ S) Δs + 3 * Δ S ≤ 4 * Δ S * S.C.k := by
    rcases hmax3 with h | h <;> rw [h] <;> omega
  have hR3 : ((max (3 * Δ S) Δs : ℕ) : ℝ) + 3 * (Δ S : ℝ) ≤ 4 * (Δ S : ℝ) * (S.C.k : ℝ) := by
    exact_mod_cast hN3
  have hR4 : ((4 * Δ S * S.C.k : ℕ) : ℝ) = 4 * (Δ S : ℝ) * (S.C.k : ℝ) := by push_cast; ring
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hfR : ((M.supportCutoff S.C (s' + 1) : ℕ) : ℝ) = (M.viewFreeze S.C s' : ℝ) + 3 * Δ S := by
    exact_mod_cast (show M.supportCutoff S.C (s' + 1) = M.viewFreeze S.C s' + 3 * Δ S by omega)
  -- `u` is active from its tick to a value at most the duty window's start up to its tick to the cutoff
  have hu := (mem_activeThroughoutToTick_of_awakeSince_steps M F) x R E hk₁ hτ hτle hk₁ le_rfl
    (fun j h1 h2 => absurd h2 (by omega))
  -- and up to its tick to the view freeze of slot `s'`
  have hm3R : (3 * (Δ S : ℝ)) ≤ ((max (3 * Δ S) Δs : ℕ) : ℝ) := by exact_mod_cast hm3
  have huF := (mem_activeThroughoutToTick_of_inside M F) R E hu (c := M.viewFreeze S.C s') (by omega)
    (by linarith) (by linarith)
  obtain ⟨kF, hkF, hcase⟩ := Activity.mem_activeThroughoutToTick.1 huF
  have hkFk₁ : kF ≤ k₁ := by
    by_contra h
    have hb := E.clock_mono k₁ kF u _ _ (by omega) (E.not_mem_corrupted_of_tick hkF) (Or.inl hk₁)
      (Or.inl hkF)
    omega
  refine ⟨kF, hkF, hkFk₁, fun i h1 h2 => ?_, ?_⟩
  · rcases hcase with h | ⟨k₀, -, c₀, hc₀, hk₀, h⟩
    · exact h i h2
    · refine h i ?_ h2
      by_contra hlt
      have hk₀a := (E.tick_active k₀ u c₀ hk₀).2.2
      have hc₀' : ((c₀ : ℤ) : ℝ) ≤ ((duty_window_start S.C (s' + 1) : ℤ) : ℝ) := by exact_mod_cast hc₀
      have := R.time_mono (show i ≤ k₀ by omega)
      have hm3R : (3 * (Δ S : ℝ)) ≤ ((max (3 * Δ S) Δs : ℕ) : ℝ) := by exact_mod_cast hm3
      have hR3' := hR3
      push_cast at hc₀' hR3'
      linarith
  · have hle : max (Δ S) Δs ≤ M.viewFreeze S.C s' := by omega
    have hw := (mem_activeThroughout_of_mem_activeThroughoutToTick M F) R E hu
      (a' := M.viewFreeze S.C s' - max (Δ S) Δs) (e := M.viewFreeze S.C s' - max (Δ S) Δs + Δs)
      (by
        have hc : ((M.viewFreeze S.C s' - max (Δ S) Δs : ℕ) : ℝ) =
            (M.viewFreeze S.C s' : ℝ) - ((max (Δ S) Δs : ℕ) : ℝ) := Nat.cast_sub hle
        have h8R : ((max (Δ S) Δs : ℕ) : ℝ) + 3 * (Δ S : ℝ) < 4 * (Δ S : ℝ) * (S.C.k : ℝ) := by
          exact_mod_cast h8
        rw [hc]
        linarith)
      (by
        have hN : M.viewFreeze S.C s' - max (Δ S) Δs + Δs ≤ M.viewFreeze S.C s' := by omega
        have hR : ((M.viewFreeze S.C s' - max (Δ S) Δs + Δs : ℕ) : ℝ) ≤ (M.viewFreeze S.C s' : ℝ) := by
          exact_mod_cast hN
        rw [hfR]
        linarith)
    refine Activity.mem_activeThroughout_of_le ?_ ?_ hw
    · push_cast [Nat.cast_sub hle]
      exact le_rfl
    · push_cast [Nat.cast_sub hle]
      exact le_rfl

end WindowsKit

/-- **Lemma 45, a lock whose window is after `GST` is extended by the next slot's honest votes.**
The proof; the audited statement is in `Statements/Executions/HealingStatements.lean`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s`: the slot of the lock;
- `v`: the validator whose update of slot `s + 1` adds the lock entry `e`; `n'`, `sent`: an outcome
of `v`'s tick at the support cutoff of slot `s + 1`, which runs that update; `w`: the voter of slot
`s + 1`; `vote`: its Goldfish vote.

Roots name blocks until `M.supportCutoff S.C (s + 1)`: Lemma 21 and Lemma 42, which the proof calls
at slot `s`, take blocks as held up to the support cutoff of slot `s + 1`; Lemma 31 reads at an
earlier slot.

Read aloud: once the recovery delay `max (Δ S) Δs` after `GST` has elapsed by the view freeze of slot `s + 1 − S.C.k`,
the lock `v` makes at slot `s` is extended by the Goldfish vote every honest `w` sends at the vote
time of slot `s + 1`, when `v` is awake and honest from the duty window's start of slot `s + 1` to
its support cutoff, `w` from that start to its vote time, the root of `w`'s fork choice is
compatible with the lock block, and, when the root is the lock block or an ancestor of it, some
block of `w`'s voter tree that is the lock block or a descendant of it is a viable head. -/
theorem lem45_honest_vote_extends_lock_of_post_GST_window (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (GST s : ℕ) (v w : V) (e : M.LE) (vote : GoldfishVote V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (s + 1)))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST + max (Δ S) Δs ≤ M.viewFreeze S.C (s + 1 - S.C.k))
    (hv : v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1)))
    -- `w` ticks to the vote time of slot `s + 1`, active up to that tick from the trace's start or from its own tick
    -- to a clock value at most `tStartW`, more than both clock bounds before the window start Lemma 42 reads; `v` and
    -- `w` are active through the sync delay after the two read times of Lemma 42's sync facts
    (tStartW : ℤ) (htStartW : (tStartW : ℝ) + ΔClockAhead + ΔClockBehind <
      ((M.viewFreeze S.C s - max (3 * Δ S) Δs : ℕ) : ℝ))
    (hw : w ∈ A.activeThroughoutToTick x tStartW (M.voteTime S.C (s + 1)))
    (hv₀ : v ∈ A.activeThroughout x ((M.viewFreeze S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.viewFreeze S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hw₀ : w ∈ A.activeThroughout x ((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (n' : M.N) (sent : List (NamedObject V))
    (hUpdate : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (M.supportCutoff S.C (s + 1)))
      ((M.supportCutoff S.C (s + 1) : ℕ) : Int))
    (hAwake : AwakeFor M S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) (s + 1))
    (he : e ∈ M.lockEntries n')
    (hd : e.d = S.C.t_ (s + S.C.k) + 5 * S.C.Δ)
    (hF2 : (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.compatible e.B = true)
    (hF3 : (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.AncestorEq e.B →
      ∃ W, VoterTreeAt M (x.tickInput w (M.voteTime S.C (s + 1)))
          (S.C.t_ ((s + 1) - 1) + 3 * S.C.Δ) (s + 1) W ∧
        W ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).viable_heads ∧
          e.B.AncestorEq W)
    (hSend : ∃ i : ℕ, x.lbl i = Event.tick w (M.voteTime S.C (s + 1)) ∧
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i) :
    ∃ H_w : Block V, vote.head = H_w.root ∧ e.B.AncestorEq H_w := by
  -- Lemma 45b's body (`lem45b_honest_vote_extends_lock_held`, `PhaseChain.lean`), whose conclusion keeps the
  -- vote's block in `w`'s tree; this page cannot import `PhaseChain.lean`, which imports it (F-78-3)
  suffices key : ∃ H_w ∈ (x.tickInput w (M.voteTime S.C (s + 1))).tree,
      vote = GoldfishVote.mk w (s + 1) H_w.root ∧ e.B.AncestorEq H_w by
    obtain ⟨H_w, -, hvote, hB⟩ := key
    exact ⟨H_w, by rw [hvote], hB⟩
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ := one_le_Δ S
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hs1 : 1 ≤ s + 1 := Nat.le_add_left 1 s
  have htime : Monotone x.time := fun _ _ h => (time_mono M) x R h
  -- the slot times
  have hss1 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s + 1)
  have hss0 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s
  have hvt := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s + 1)
  have hsc := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s + 1)
  have hfr := (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_eq M.toSlotLayout F.sched U) S s
  have hfrk := (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_eq M.toSlotLayout F.sched U) S (s + 1 - S.C.k)
  have hk2 := S.C.k_ge_two
  have hsk := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
    (show s + 1 - S.C.k ≤ s by omega)
  have hGSTv : GST + max (Δ S) Δs ≤ M.viewFreeze S.C s := by omega
  -- the reads of Lemmas 21b and 42 at `v` (`lem21b_reads_of_dutyWindow`)
  obtain ⟨htStart, -⟩ := (lem21b_reads_of_dutyWindow M F U) S R E hSkew hΔs (le_of_add_le_right hGSTv) htStartW hv
  -- `v`'s tick `k_v` to the support cutoff of slot `s + 1`, active from that cutoff less `ΔClockAhead`
  have hslR : ((M.supportCutoff S.C (s + 1) - max (6 * Δ S) Δs : ℕ) : ℝ) ≤ (M.supportCutoff S.C (s + 1) : ℝ) := by
    exact_mod_cast Nat.sub_le _ _
  have hdle := (duty_window_start_le_real M F U) S (s + 1)
  obtain ⟨k_v, hk_v, hwinv⟩ := (tick_window_of_activeThroughoutToTick_int M) x R E hv
    (t₀ := (M.supportCutoff S.C (s + 1) : ℝ) - ΔClockAhead) (by linarith)
  have hti_v : x.tickInput v (M.supportCutoff S.C (s + 1)) = x.st k_v v := by
    unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hk_v]
  have hRootsΦv : GoldilocksCorrectness.Statements.Routines.RootsNameBlocksIn
      (M.fg_to_ac (x.tickInput v (M.supportCutoff S.C (s + 1)))).tree := by
    rw [hti_v]
    exact (GoldilocksCorrectness.Record.Statements.Executions.rootsNameBlocksIn_frame_of_exec_node M F) S A x R E _ v
  -- the confirmation update `v`'s tick ran
  have hCU := (confirmationUpdated_of_cutoff_tickInput M F U) x R s v n' sent hUpdate hAwake
  -- step 1: Lemma 35 on `v`'s update; `e` is an entry it adds
  obtain ⟨-, h35⟩ := GoldilocksCorrectness.Record.Statements.Routines.lem35_update_confirmation_lock_entries hCU
  rcases h35 e he with hin | ⟨-, -, -, ⟨C', hSaved, hLC'⟩, hFS⟩
  · -- an entry of the input was added by the update of its own slot `s`, before `v`'s tick
    exfalso
    rw [hti_v] at hin
    obtain ⟨s', hd', hlt, -⟩ := (lem39_lock_entry_provenance M F U) S A x R k_v v e E hin
    have hbb : s' = s :=
      GoldilocksCorrectness.Proofs.Routines.lockDeadline_injective S (hd'.symm.trans hd)
    rw [hbb, (tickStep_eq_of_lbl M) x E hk_v] at hlt
    exact lt_irrefl _ hlt
  -- step 2: Lemma 36 gives the early supporters of `e`'s block at `v`
  obtain ⟨Sup, hSup, hElig, -⟩ :=
    (GoldilocksCorrectness.Record.Statements.Routines.lem36_confirmed_ancestor_early_supporters F)
      C' e.B hs1 hRootsΦv
      (by
        rw [Nat.add_sub_cancel, hti_v]
        exact (pool_vote_late_of_tick M F U) S A x R s v E k_v hk_v hwinv)
      hCU hSaved hLC'
  simp only [Nat.add_sub_cancel] at hSup hElig hFS
  -- the roots until the latest real time of `w`'s tick to the view freeze of slot `s`
  have hcf : (M.supportCutoff S.C (s + 1) : ℝ) = (M.viewFreeze S.C s : ℝ) + 3 * Δ S := by
    have h : M.supportCutoff S.C (s + 1) = M.viewFreeze S.C s + 3 * Δ S := by
      rw [hsc, hvt, hfr, hss1, hss0]; ring
    rw [h]; push_cast; ring
  have hRoots' : RootsNameBlocksUntil M A x ((M.viewFreeze S.C s : ℝ) + ΔClockBehind) := by
    refine (RootsNameBlocksUntil.mono M) ?_ hRoots
    rw [hcf]
    linarith
  -- `w`, active up to its tick to the view freeze of slot `s`
  have hvfv : (M.viewFreeze S.C s : ℝ) + ΔClockBehind < (M.voteTime S.C (s + 1) : ℝ) - ΔClockAhead := by
    have h : M.voteTime S.C (s + 1) = M.viewFreeze S.C s + 2 * Δ S := by
      rw [hvt, hfr, hss1, hss0]; ring
    rw [h]; push_cast; linarith
  have hfr1 : 1 ≤ M.viewFreeze S.C s := by rw [hfr]; omega
  have hwF : w ∈ A.activeThroughoutToTick x tStartW (M.viewFreeze S.C s) :=
    (mem_activeThroughoutToTick_of_le_end_int M) x R E hfr1
      (by
        have h3 : ((M.viewFreeze S.C s - max (3 * Δ S) Δs : ℕ) : ℝ) ≤ (M.viewFreeze S.C s : ℝ) := by
          exact_mod_cast Nat.sub_le _ _
        linarith)
      hvfv hw
  -- `w`'s tick `kV` to the vote time of slot `s + 1`, and its finalized block there
  obtain ⟨kV, hkV, hsV⟩ := hSend
  have hti_w : x.tickInput w (M.voteTime S.C (s + 1)) = x.st kV w := by
    unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hkV]
  have hFroot : (x.tickInput w (M.voteTime S.C (s + 1))).finalized.AncestorEq
      (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F), hti_w]
    exact (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F) S A x R E kV w
  have hFw : (x.tickInput w (M.voteTime S.C (s + 1))).finalized.compatible e.B = true :=
    GoldilocksCorrectness.Proofs.Routines.compatible_of_ancestorEq_compatible hFroot hF2
  -- step 3: the lock condition at `w`, on the revocation every outcome of `w`'s tick ran
  have hLocks : ∀ (n'' : M.N) (sent'' : List (NamedObject V)),
      .ok (n'', sent'') ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C (s + 1)))
        ((M.voteTime S.C (s + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) →
      ∀ e' ∈ M.lockEntries n'',
        M.is_live (x.tickInput w (M.voteTime S.C (s + 1)))
          ((M.voteTime S.C (s + 1) : ℕ) : Int) e' = true → e'.B.compatible e.B = true := by
    intro n'' sent'' hrun hAwakeW e' he' _
    have hRevoke := (locksRevoked_of_voteTime_outcome M F U) S A x R E (s + 1) w n'' sent'' hrun hAwakeW
    rcases hFS with hFast | hSlow
    · -- fast: Lemma 42
      exact (lem42_fast_lock_clears_conflicting_locks M F U) S A x R GST s e.B v w n' E hNet hSkew hRedeliver
        Sy hΔs hRoots' hParent hGSTv (duty_window_start S.C (s + 1)) htStart hv tStartW htStartW hwF hv₀ hw₀
        hCU hFast kV hkV hFw n'' hRevoke e' he'
    · -- slow: through the slot of each entry `w`'s revocation reads
      obtain ⟨e_w, he_w, hlive_w, -, he'w, -⟩ :=
        GoldilocksCorrectness.Record.Statements.Routines.lem38_revoke_locks_entries_moved hs1 hRevoke e' he'
      have hlt_w : ((M.voteTime S.C (s + 1) : ℕ) : Int) < e_w.d :=
        ((GoldilocksCorrectness.Record.Proofs.Routines.is_live_iff M F) _ _ _).1 hlive_w |>.1
      rw [hti_w] at he_w
      obtain ⟨s', hd_w, hc_w, hlw', ⟨τw, hτw, hτwle⟩, h39w⟩ :=
        (lem39_lock_entry_provenance M F U) S A x R kV w e_w E he_w
      rw [(tickStep_eq_of_lbl M) x E hlw'] at hc_w
      -- `s' < s`: `w`'s tick to the support cutoff of slot `s' + 1` is before its tick to the vote time of slot
      -- `s + 1`, so to a smaller clock value (`clock_mono`, `tick_unique`)
      have hcv : M.supportCutoff S.C (s' + 1) < M.voteTime S.C (s + 1) := by
        generalize x.tickStep w (M.supportCutoff S.C (s' + 1)) = kc at hc_w hlw'
        have hbc := E.clock_mono _ kV w _ _ hc_w (E.not_mem_corrupted_of_tick hkV) (Or.inl hlw') (Or.inl hkV)
        rcases Nat.lt_or_ge (M.supportCutoff S.C (s' + 1)) (M.voteTime S.C (s + 1)) with h | h
        · exact h
        · have hbb : M.supportCutoff S.C (s' + 1) = M.voteTime S.C (s + 1) := le_antisymm hbc h
          rw [hbb] at hlw'
          exact absurd (E.tick_unique _ kV w _ hlw' hkV) (by omega)
      have hlt : s' < s := by
        by_contra h
        have h' : M.supportCutoff S.C (s + 1) ≤ M.supportCutoff S.C (s' + 1) := by
          rcases Nat.lt_or_eq_of_le (show s + 1 ≤ s' + 1 by omega) with h'' | h''
          · exact le_of_lt ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_lt_of_lt M.toSlotLayout F.sched) S h'')
          · rw [h'']
        omega
      -- `s + 1 − k ≤ s'`: `e_w` is live at the vote time of slot `s + 1`
      have hlow : s + 1 - S.C.k ≤ s' := by
        by_cases hkb : S.C.k ≤ s + 1
        · refine (lem41_slot_of_live_entry M F U) S (s + 1 - S.C.k) s' (M.voteTime S.C (s + 1)) e_w hd_w hlt_w ?_
          rw [Nat.sub_add_cancel hkb]
        · omega
      -- `e`'s block is `v`'s saved confirmation of slot `s'` or an ancestor of it
      obtain ⟨-, hj⟩ :=
        (GoldilocksCorrectness.Record.Statements.Routines.lem37_slow_test_saved_confirmations F) S.C _ s e.B hSlow
      obtain ⟨Cj, hCj, -, hBj⟩ := hj s' hlow hlt
      rw [hti_v] at hCj
      obtain ⟨hlt40, hl40, ⟨τ₁, hτ₁, hτ₁le⟩, hS40, -⟩ :=
        (lem40_saved_confirmation_provenance M F U) S A x R k_v v s' Cj E hCj
      obtain ⟨n₁, sent₁, hrun₁, hAw₁, -⟩ :=
        (update_state_of_tick M F U) S A x R s' v E hl40 ⟨τ₁, hτ₁, hτ₁le⟩
      have hU₁ := (confirmationUpdated_of_cutoff_tickInput M F U) x R s' v n₁ sent₁ hrun₁ hAw₁
      -- `w`'s update of slot `s' + 1` and the confirmation `e_w` traces to
      obtain ⟨nw, sentw, hrunw, hAww, -⟩ :=
        (update_state_of_tick M F U) S A x R s' w E hlw' ⟨τw, hτw, hτwle⟩
      have hU_w := (confirmationUpdated_of_cutoff_tickInput M F U) x R s' w nw sentw hrunw hAww
      obtain ⟨e₀w, -, -, -, -, ⟨C₀w, hC₀w, hB₀w⟩, -, hBw₀, -⟩ := h39w nw sentw hrunw hAww
      -- Lemma 31 at slot `s'`, its windows read off the two duty tests
      have hfrw := (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_eq M.toSlotLayout F.sched U) S s'
      have hsw := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S hlow
      have hGSTw : GST + max (Δ S) Δs ≤ M.viewFreeze S.C s' := by omega
      have hcb : Δs ≤ M.viewFreeze S.C s' := by
        have := le_max_right (Δ S) Δs
        omega
      obtain ⟨kF₁, hkF₁, -, hwin₁, hv₁₀⟩ :=
        (lem31_windows_of_duty_test M F U) x R E hSkew hΔs hcb hl40 hτ₁ hτ₁le
      obtain ⟨kF₂, hkF₂, -, hwin₂, hv₂₀⟩ :=
        (lem31_windows_of_duty_test M F U) x R E hSkew hΔs hcb hlw' hτw hτwle
      -- the two ticks to the support cutoff of slot `s' + 1` are before the support cutoff of slot `s + 1`
      have hcc : M.supportCutoff S.C (s' + 1) + 4 * Δ S ≤ M.supportCutoff S.C (s + 1) := by
        have hsc' := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s' + 1)
        have hvt' := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s' + 1)
        have hss' := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
          (show s' + 1 ≤ s by omega)
        have hsS : M.slotStart S.C (s + 1) = M.slotStart S.C s + 4 * Δ S := by
          rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U),
            (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s, Nat.mul_add,
            Nat.mul_one]
        omega
      have hccR : ((M.supportCutoff S.C (s' + 1) : ℕ) : ℝ) + 4 * Δ S ≤ ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) := by
        exact_mod_cast hcc
      have hR31 : RootsNameBlocksUntil M A x
          (max (x.time (x.tickStep v (M.supportCutoff S.C (s' + 1))))
            (x.time (x.tickStep w (M.supportCutoff S.C (s' + 1))))) := by
        refine (RootsNameBlocksUntil.mono M) ?_ hRoots
        have h1 := (E.tick_active _ v _ hl40).2.2
        have h2 := (E.tick_active _ w _ hlw').2.2
        exact max_le (by linarith) (by linarith)
      have hcomp := (lem31_saved_confirmations_compatible M F U) S A x R GST s' v w n₁ nw Cj C₀w E
        hNet hSkew hRedeliver Sy hGSTw kF₁ hkF₁ hwin₁ hv₁₀ kF₂ hkF₂ hwin₂ hv₂₀ _ hl40 _ hlw' hR31
        hU₁ (hS40 n₁ sent₁ hrun₁ hAw₁) hU_w hC₀w
      exact GoldilocksCorrectness.Proofs.Routines.compatible_symm'
        (GoldilocksCorrectness.Proofs.Routines.compatible_of_ancestorEq_both hBj
        (ancestorEq_trans he'w (ancestorEq_trans hBw₀ hB₀w)) hcomp)
  -- step 4: Lemma 21b, which keeps the block the vote names
  exact (lem21b_goldfish_vote_extends_eligible_block_held M F U) S A x R GST s Sup e.B v w vote E hNet hSkew hRedeliver
    Sy hΔs hRoots' hParent hGSTv (duty_window_start S.C (s + 1)) htStart hv tStartW htStartW hwF hv₀ hw₀ hSup hElig
    hF2 hF3 hLocks ⟨kV, hkV, hsV⟩

end GoldilocksCorrectness.Record.Proofs.Executions

