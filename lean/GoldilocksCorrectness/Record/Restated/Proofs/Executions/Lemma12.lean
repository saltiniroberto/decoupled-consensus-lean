module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.VoteDelivery
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.VoteHeadKit
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.DeliveryDefs
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.WalkDefs
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Confirmation
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ScoreACStore
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.FGStateReadersOnChain
public import GoldilocksCorrectness.Proofs.Executions.Lemma12
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma12, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma12.lean`, over a model `M` whose facts
`F` hold, for an execution `x` of `protocolOf M S`: Lemma 12, an honest early vote is held, resolved
and unique by the support cutoff in the node state of every validator awake and honest from the vote
time to the support cutoff, and its two corollaries, `HeldEarlyVoteFor` read as `EarlyVoteOnceFor`
and as `VotesOnceInPoolFor`. The page's routine-level theorems are the facts' fields or have their
twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_eq slot_eq_of_mem
  supportCutoff_cast supportCutoff_eq voteTime_eq voteTime_succ)

open GoldilocksCorrectness.Proofs.Routines (tau_eq_ok_some)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (ResolvesAt EarlyVoteOnceFor VotesOnceInPoolFor)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (acObject)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  blockWithRoot_eq_ok find?_eq_some dre_bind_ok liftM_some occurrenceBefore_eq_true_iff)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-! ## The voter's window, read up to its vote tick

A vote tick gives its validator's activity up to that tick only: the validator may sleep at a later
step read as the vote time. These lemmas read the voter's window up to its tick
(`activeThroughoutToTick_of_vote_tick`), a window strictly inside it
(`mem_activeThroughout_of_mem_activeThroughoutToTick`), and the block and vote delivery kit with the
holder read at the window's first time and its honesty at the read time in place of a window through
the read time. -/

section VoterWindow

variable {S : Setup V} {A : Activity V}

/-- A validator in `A.activeThroughoutToTick x a b` is active through every window `[a', e]` with
`a + ΔClockBehind < a'` and `e + ΔClockAhead < b`: the tick to `b` is at a real time at least
`b − ΔClockAhead` (`tick_active`), so every configuration in force at a time at most `e` is at a step
before it; in the reader's first case every step up to that tick is counted; in its second case the
tick to a value `c ≤ a` is at a real time at most `c + ΔClockBehind ≤ a + ΔClockBehind`, so every
configuration in force at a time at least `a'` is at a step from that tick on (T-RC8-1).

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `v`: the validator;
  `a`, `b`: the reader's window (`a` an integer clock value); `a'`, `e`: the inner window.

Read aloud: a validator active up to its tick to `b`, from a window opening at `a`, is active through
every window that starts more than `ΔClockBehind` after `a` and ends more than `ΔClockAhead` before
`b`. -/
theorem mem_activeThroughout_of_mem_activeThroughoutToTick {x : Trace V (NamedObject V) M.N}
    (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {v : V} {a : ℤ} {b a' e : ℕ} (hv : v ∈ A.activeThroughoutToTick x a b)
    (ha : (a : ℝ) + ΔClockBehind < a') (he : (e : ℝ) + ΔClockAhead < b) :
    v ∈ A.activeThroughout x a' e := by
  obtain ⟨k', hk', hcase⟩ := Activity.mem_activeThroughoutToTick.1 hv
  have hk'b := (E.tick_active k' v b hk').2.1
  refine Activity.mem_activeThroughout_of_forall fun i h1 h2 => ?_
  -- the step is before the tick to `b`
  have hik' : i < k' := (lt_of_time_lt M) x R (by linarith)
  rcases hcase with h | ⟨k, -, c, hca, hk, h⟩
  · exact h i hik'.le
  · -- the step is from the tick to `c` on
    have hka := (E.tick_active k v c hk).2.2
    have hca' : (c : ℝ) ≤ (a : ℝ) := by exact_mod_cast hca
    refine h i ?_ hik'.le
    by_contra hc
    have := R.time_mono (show i + 1 ≤ k by omega)
    linarith

/-- A validator in `A.activeThroughoutToTick x a b`, `a < b`, starts its tick to `b` with `awakeSince`
the initial time `proposal_window_start S.C 0`, or some time at most `a`. In the reader's first case
it was never restarted up to that tick, and every step keeps the initial value
(`tickInput_awakeSince_of_awake_up_to_tick`). In its second case it ticks to a value `c ≤ a` at a step
`k` before its tick to `b` (`c ≠ b`): that tick leaves a present value at most `c` (it writes `c` when
none is stored; a stored value is the initial one, at most `0`, or the value of an earlier tick after
the last restart, at most `c` by `clock_mono`), and `v` stays awake from `k` to its tick to `b`, which
keeps the value (`awakeSince_kept_of_awake_steps`).

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `v`: the validator;
  `a`, `b`: the reader's window (`a` an integer clock value).

Read aloud: a validator active up to its tick to `b`, from a window opening at `a`, has been awake
since the start, or since a time at most `a`, at that tick. -/
theorem awakeSince_le_of_mem_activeThroughoutToTick
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {v : V} {a : ℤ} {b : ℕ} (hab : a < b) (hv : v ∈ A.activeThroughoutToTick x a b) :
    ∃ τ : Time, (x.tickInput v b).awakeSince = some τ ∧
      (τ = proposal_window_start S.C 0 ∨ τ ≤ a) := by
  obtain ⟨k', hk', h | ⟨k, hkk, c, hca, hk, h⟩⟩ := Activity.mem_activeThroughoutToTick.1 hv
  · exact ⟨_, (tickInput_awakeSince_of_awake_up_to_tick M F) x R E hk'
      (fun i hi => Activity.mem_awake_of_mem_active (h i hi)), Or.inl rfl⟩
  · -- the tick to `c` comes strictly before the tick to `b`
    have hkk' : k < k' := by
      rcases Nat.lt_or_ge k k' with hlt | hge
      · exact hlt
      · have hkeq : k = k' := le_antisymm hkk hge
        rw [hkeq, hk'] at hk
        have hcb := (Event.tick.inj hk).2
        omega
    -- the value the tick to `c` leaves
    have hin : x.tickInput v c = x.st k v := by
      unfold Trace.tickInput
      rw [(tickStep_eq_of_lbl M) x E hk]
    obtain ⟨n', sent, hok, hst, -⟩ := R.tick k v c hk
    have haw := (F.tk.tick_clock_validator_awakeSince S.C S.P S.X _ (c : Int) n' sent hok).2.2
    have hleft : ∃ τ : Time, (x.st (k + 1) v).awakeSince = some τ ∧ τ ≤ (c : Int) := by
      rw [hst, haw]
      rcases hsome : (x.st k v).awakeSince with _ | τ
      · exact ⟨c, rfl, le_rfl⟩
      · refine ⟨τ, rfl, ?_⟩
        have hτ : (x.tickInput v c).awakeSince = some τ := by rw [hin]; exact hsome
        rcases (awake_of_tickInput_awakeSince_of_tick M F) x R E ⟨k, hk⟩ hτ with
          ⟨h0, -⟩ | ⟨k₁, τ', hk₁, hl₁, hτ', -⟩
        · rw [h0]
          exact le_trans (GoldilocksCorrectness.Proofs.Routines.proposal_window_start_zero_le S.C) (by exact_mod_cast Nat.zero_le c)
        · rw [(tickStep_eq_of_lbl M) x E hk] at hk₁
          have hτc := E.clock_mono k₁ k v τ' c hk₁ (E.not_mem_corrupted_of_tick hk) (Or.inl hl₁)
            (Or.inl hk)
          rw [← hτ']
          exact_mod_cast hτc
    obtain ⟨τ, hτ, hτc⟩ := hleft
    refine ⟨τ, ?_, Or.inr (le_trans hτc hca)⟩
    have hkept := (awakeSince_kept_of_awake_steps M F) x R E (show k + 1 ≤ k' by omega)
      (fun i hi1 hi2 => Activity.mem_awake_of_mem_active (h i (by omega) hi2.le)) hτ
    unfold Trace.tickInput
    rw [(tickStep_eq_of_lbl M) x E hk']
    exact hkept

/-- A validator in `A.activeThroughoutToTick x a b` that ticks to `b' ≤ b` at the step `k''` is in
`A.activeThroughoutToTick x a b'`: its tick to `b'` comes no later than its tick to `b`; in the
reader's second case, when the tick to `b'` comes before the tick to the value `c ≤ a`, it is itself
a tick to a value at most `a` (`clock_mono`).

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `v`: the validator;
  `a`, `b`: the reader's window; `b'`: the earlier value; `k''`: the step of the tick to it.

Read aloud: a validator active from `a` up to its tick to `b` is active from `a` up to its tick to
any earlier value. -/
theorem mem_activeThroughoutToTick_of_tick_le {x : Trace V (NamedObject V) M.N}
    (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {v : V} {a : ℤ} {b b' k'' : ℕ} (hv : v ∈ A.activeThroughoutToTick x a b)
    (hk'' : x.lbl k'' = Event.tick v b') (hbb : b' ≤ b) :
    v ∈ A.activeThroughoutToTick x a b' := by
  -- the tick to `b'` is `k''`, no later than the tick `k'` to `b`: a later one would set an honest clock back
  -- (`clock_mono`) or tick to `b` twice (`tick_unique`)
  obtain ⟨k', hk', hcase⟩ := Activity.mem_activeThroughoutToTick.1 hv
  have hle : k'' ≤ k' := by
    by_contra h
    have hb := E.clock_mono k' k'' v b b' (by omega) (E.not_mem_corrupted_of_tick hk'') (Or.inl hk')
      (Or.inl hk'')
    have hbb' : b' = b := le_antisymm hbb hb
    rw [hbb'] at hk''
    exact absurd (E.tick_unique k' k'' v b hk' hk'') (by omega)
  refine Activity.mem_activeThroughoutToTick.2 ⟨k'', hk'', ?_⟩
  rcases hcase with h1 | ⟨k, hkk, c, hca, hk, h2⟩
  · exact Or.inl fun i hi => h1 i (le_trans hi hle)
  · rcases le_or_gt k k'' with hkk'' | hk''k
    · exact Or.inr ⟨k, hkk'', c, hca, hk, fun i h1' h2' => h2 i h1' (le_trans h2' hle)⟩
    · -- the tick to `b'` comes before the tick to `c`, so `b' ≤ c ≤ a` (`clock_mono`): the tick to `b'`
      -- itself opens the second case
      have hbc := E.clock_mono k'' k v b' c hk''k (E.not_mem_corrupted_of_tick hk) (Or.inl hk'')
        (Or.inl hk)
      refine Or.inr ⟨k'', le_rfl, b', le_trans (by exact_mod_cast hbc) hca, hk'', fun i h1' h2' => ?_⟩
      have hi : i = k'' := le_antisymm h2' h1'
      rw [hi]
      exact (E.tick_active k'' v b' hk'').1

/-- The protocol's duty window start of slot `s`, an integer, read as a real number, is at most the
model's natural-number start `M.dutyWindowStart S.C s` read as a real number (the latter is the former
raised to `0` when negative).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `S`: the setup; `s`: the slot.

Read aloud: the protocol's duty window start is at most the model's. -/
theorem duty_window_start_le_real (U : UniformSchedule M.toSlotLayout) (S : Setup V) (s : ℕ) :
    ((duty_window_start S.C s : ℤ) : ℝ) ≤ ((M.dutyWindowStart S.C s : ℕ) : ℝ) := by
  have h := (GoldilocksCorrectness.Record.Proofs.Routines.duty_window_start_le_dutyWindowStart
    M.toSlotLayout F.sched U) S s
  exact_mod_cast h

omit F in
/-- The protocol's duty window start of slot `s`, `duty_window_start S.C s = S.C.t_ s + S.C.Δ − 4 S.C.Δ S.C.k`,
read as a real number: `4 Δ s + Δ − 4 Δ k`, with `Δ = Δ S`.

The variables:
- `S`: the setup; `s`: the slot.

Read aloud: slot `s`'s duty window starts `4 Δ k − Δ` before slot `s`'s start. -/
theorem duty_window_start_real (S : Setup V) (s : ℕ) :
    ((duty_window_start S.C s : ℤ) : ℝ) =
      4 * (Δ S : ℝ) * (s : ℝ) + (Δ S : ℝ) - 4 * (Δ S : ℝ) * (S.C.k : ℝ) := by
  have h := GoldilocksCorrectness.Proofs.Routines.Δ_cast S
  rw [GoldilocksCorrectness.Proofs.Routines.duty_window_start_eq,
    GoldilocksCorrectness.Proofs.Routines.t_eq_mul, ← h]
  push_cast
  ring

/-- The spec's duty window start of slot `s` is the model's when the model's is at least `1`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `S`: the setup; `s`: the slot.

Read aloud: a duty window that starts at a positive time starts there in both readings. -/
theorem dutyWindowStart_le_duty_window_start (U : UniformSchedule M.toSlotLayout) (S : Setup V)
    {s : ℕ} (h1 : 1 ≤ M.dutyWindowStart S.C s) :
    ((M.dutyWindowStart S.C s : ℕ) : Int) ≤ duty_window_start S.C s := by
  have h := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_eq_toNat
    M.toSlotLayout F.sched U) S s
  rw [h] at h1 ⊢
  have h0 : 0 ≤ duty_window_start S.C s := by
    by_contra hc
    rw [Int.toNat_eq_zero.2 (le_of_lt (not_le.1 hc))] at h1
    omega
  rw [Int.toNat_of_nonneg h0]

end VoterWindow

/-! ## Lemma 12 at the receiver's own ticks (B3-R1's eighth launch)

The kit of the proof of Lemma 12 read at `w`'s own ticks (T-RC6-1): the clock value a validator's tick
starts from, one vote per slot of an honest validator at a step, and the delivery core. -/

section TickCore

variable {S : Setup V} {A : Activity V}

/-- A validator outside the adversary set at its tick `kR` to a positive clock value `c`, active at every
step up to `kR` whose real time is at least `c − ΔClockAhead`, has a clock value less than `c` at `kR`: the
clock value was set by an earlier tick or restart of `w` (`clockValue_cases`), to a value at most `c`
(`clock_mono`); an earlier tick to `c` would be a second tick to `c` (`tick_unique`), and a restart at `c`
is at a real time at least `c − ΔClockAhead` (`restart_time`) and finds `w` not awake (`restart_crashed`),
against the window.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `E`: the environment's facts; `kR`: the step of the tick; `w`: the validator; `c`:
  the tick's clock value.

Read aloud: a validator active from `ΔClockAhead` before `c` up to its tick to `c` reaches `c` at that tick
from a smaller clock value. -/
theorem clockValue_lt_of_tick_of_active {x : Trace V (NamedObject V) M.N}
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {kR c : ℕ} {w : V} (hl : x.lbl kR = Event.tick w c) (hc : 0 < c)
    (hwin : ∀ j : ℕ, (c : ℝ) - ΔClockAhead ≤ x.time j → j ≤ kR → w ∈ A.active j) :
    x.clockValue kR w < c := by
  have hw : w ∉ A.corrupted kR := E.not_mem_corrupted_of_tick hl
  rcases x.clockValue_cases kR w with ⟨h0, -⟩ | ⟨j, hj, hset, -⟩
  · rw [h0]; exact hc
  · have hle := E.clock_mono j kR w _ c hj hw hset (Or.inl hl)
    refine lt_of_le_of_ne hle fun heq => ?_
    rw [heq] at hset
    rcases hset with hset | ⟨keep, hset⟩
    · exact absurd (E.tick_unique j kR w c hset hl) (by omega)
    · have hT := (E.restart_time j w c keep hset).1
      exact (E.restart_crashed j w c keep hset).1
        (Activity.mem_awake_of_mem_active (hwin j hT hj.le))

/-- One vote per slot of an honest validator, at a step: two votes of the validator `u`, outside the
adversary set after `k` steps, that a validator's pool of slot `s` holds at `k` are the same vote. Each was
put on the wire before `k` (`pool_vote_sent`), so by `u`'s own tick (`hOwner`, `u` honest then by the
permanence of corruption), and an honest validator sends one vote per slot (`honest_vote_sent_once`).

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `k`: the step; `w`: the validator
  whose pool it is; `u`: the voter; `s`: the slot; `v₁`, `v₂`: the two votes.

Read aloud: a validator holds at most one vote per slot of each validator honest at that step. -/
theorem unique_vote_of_owner_at {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hOwner : VotesCastByOwner M A x)
    {k : ℕ} {w u : V} {s : Slot} {v₁ v₂ : GoldfishVote V}
    (hu : u ∉ A.corrupted k)
    (h₁ : v₁ ∈ M.votesHeldSet (x.st k w) s) (h₂ : v₂ ∈ M.votesHeldSet (x.st k w) s)
    (hi₁ : v₁.val_index = u) (hi₂ : v₂.val_index = u) :
    v₁ = v₂ := by
  have hhon : ∀ i, i < k → u ∉ A.corrupted i := fun i hi h => hu (E.corrupted_mono i k hi.le h)
  obtain ⟨i₁, hik₁, sm₁, hsm₁, hc₁⟩ := (pool_vote_sent M F) x R E h₁
  obtain ⟨i₂, hik₂, sm₂, hsm₂, hc₂⟩ := (pool_vote_sent M F) x R E h₂
  obtain ⟨k₁, t₁, -, hl₁, hs₁⟩ := hOwner i₁ sm₁ v₁ hsm₁ hc₁ (hi₁ ▸ hhon i₁ hik₁)
  obtain ⟨k₂, t₂, -, hl₂, hs₂⟩ := hOwner i₂ sm₂ v₂ hsm₂ hc₂ (hi₂ ▸ hhon i₂ hik₂)
  rw [hi₁] at hl₁ hs₁
  rw [hi₂] at hl₂ hs₂
  refine (honest_vote_sent_once M F R E) hl₁ hl₂ hs₁ hs₂ ?_
  rw [(GoldilocksCorrectness.Record.Statements.Executions.pool_slot_of_exec M F) S A x R E k w s v₁ h₁,
    (GoldilocksCorrectness.Record.Statements.Executions.pool_slot_of_exec M F) S A x R E k w s v₂ h₂]

/-- **Kit theorem, Lemma 12's core with `w`'s finalized block compatible with the vote's block** (re-check 79 (a),
STOP P2-39; the core `lem12_vote_held_at_tick_core` is derived from it). The hypotheses of
`lem12_vote_held_at_tick_core`, with `hF` read as compatibility: `w`'s finalized block at its tick `kc` to `c` is
compatible with `Hu`, in place of being `Hu` or an ancestor of `Hu`. The conclusion is the core's without the two
clauses that read `w`'s frame tree (`Hu` in the frame's tree, the vote resolved there): `w`'s state at `kc` holds `u`'s
vote of slot `s` for the root of `Hu`, stamped before the support cutoff `C.t_ s + 2 · C.Δ`; `Hu` is in `w`'s node
tree, its slot is at most `s`, its block stamp is before the cutoff; and the vote is `u`'s only vote of slot `s` there.

Why: the core's proof, which reads `hF` at two places only: the admission of a delivery of `Hu` before `w`'s tick `kR`
to the cutoff (compatibility at `kR`, from compatibility at `kc` since `w`'s finalized block at `kR` is an ancestor of
or equal to the one at `kc`), and the frame-tree clause, which this form does not conclude.

The variables: as `lem12_vote_held_at_tick_core`'s.

Read aloud: an honest early vote of slot `s`, whose block its voter keeps serving for `ΔHolderOnline` from `t₀`, is
held and stamped before the support cutoff, for a block `w` holds whose slot is at most `s` and whose stamp is before
the cutoff, as the voter's only vote of the slot, in the state of every later tick of a validator active from `t₀` up to
its tick to that cutoff whose finalized block is compatible with the vote's block. -/
theorem lem12_vote_held_at_tick_core_compat (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (s c : ℕ) (u w : V) (Hu : Block V)
    {deadline} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline (releaseOf M S.C) ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    -- a message on the wire at a real time at most `ΔClockBehind` after the vote time of slot `s` is due
    -- `ΔClockAhead` before the support cutoff of slot `s` or earlier
    (hdl : ∀ (sm : SignedMsg V (NamedObject V)) (a : ℝ), a ≤ (M.voteTime S.C s : ℝ) + ΔClockBehind →
      ∃ d : ℝ, deadline sm a = some d ∧ d + ΔClockAhead ≤ (M.supportCutoff S.C s : ℝ))
    {sync : V → SignedMsg V (NamedObject V) → ℕ → Option ℕ} {ΔHolderOnline : ℝ}
    (Sy : GoldilocksCorrectness.Statements.AbstractTrace.SyncedWithinBy A x (servesMin M S.C) acObject
      (releaseOf M S.C) ΔRedeliver sync ΔHolderOnline)
    (hHO : 0 ≤ ΔHolderOnline)
    -- the sync fact is read at `t₀`, at least one delay before the vote time of slot `s`, with a deadline for
    -- `w` at most the support cutoff of slot `s`
    (t₀ : ℕ) (ht₀ : t₀ + Δ S ≤ M.voteTime S.C s)
    (hsync : ∀ sm, ∃ d : ℕ, sync w sm t₀ = some d ∧ d ≤ M.supportCutoff S.C s)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep w (M.supportCutoff S.C s))))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hc : M.supportCutoff S.C s ≤ c) (kc : ℕ) (hkc : x.lbl kc = Event.tick w c)
    (hcomm : u ∈ S.P.committee s) (hu : u ∉ A.corrupted kc)
    (hsend : ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s) ∧
      (⟨u, NamedObject.gfVote (GoldfishVote.mk u s Hu.root)⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i)
    (hHT : Hu ∈ (x.tickInput u (M.voteTime S.C s)).tree)
    -- the voter is active in every configuration in force at a real time of `[t₀, t₀ + ΔHolderOnline]`
    (hHold : u ∈ A.activeThroughout x (t₀ : ℝ) ((t₀ : ℝ) + ΔHolderOnline))
    -- `w` ticks to the support cutoff of slot `s` at `kR`, active at every step from the real time `t₀` up
    -- to `kR`
    (hw : ∃ kR : ℕ, x.lbl kR = Event.tick w (M.supportCutoff S.C s) ∧
      ∀ j : ℕ, (t₀ : ℝ) ≤ x.time j → j ≤ kR → w ∈ A.active j)
    -- `w`'s finalized block at `kc` is compatible with `Hu` (an ancestor of `Hu`, `Hu` itself or a descendant)
    (hF : (x.tickInput w c).finalized.compatible Hu = true) :
    GoldfishVote.mk u s Hu.root ∈ M.votesHeldSet (x.tickInput w c) s ∧
      (∃ τ : Stamp, (x.tickInput w c).voteStamp (GoldfishVote.mk u s Hu.root) = some τ ∧
        τ < ((S.C.t_ s + 2 * S.C.Δ : Time) : Stamp)) ∧
      Hu ∈ (x.tickInput w c).tree ∧ Hu.slot ≤ s ∧
      (∃ τH : Stamp, (x.tickInput w c).blockStamp Hu = some τH ∧
        τH < ((S.C.t_ s + 2 * S.C.Δ : Time) : Stamp)) ∧
      ∀ vote' ∈ M.votesHeldSet (x.tickInput w c) s, vote'.val_index = u → vote' = GoldfishVote.mk u s Hu.root := by
  classical
  obtain ⟨i, hl, hsent⟩ := hsend
  obtain ⟨kR, hkR, hwin⟩ := hw
  rw [(tickStep_eq_of_lbl M) x E hkR] at hRoots
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ := one_le_Δ S
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  -- the slot layout
  have ht₂ : M.voteTime S.C s + Δ S = M.supportCutoff S.C s :=
    ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s).symm
  have hv₁ : M.voteTime S.C s = M.slotStart S.C s + Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s
  have hssn : ∀ n : ℕ, M.slotStart S.C n = 4 * Δ S * n := fun n =>
    (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S n
  have hss : M.slotStart S.C (s + 1) = M.slotStart S.C s + 4 * Δ S := by
    rw [hssn, hssn, Nat.mul_add, Nat.mul_one]
  have hsl : ∀ t : ℕ, M.slot S.C t = S.C.slot (t : Int) := fun t => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U),
      GoldilocksCorrectness.Proofs.Routines.slot_natCast]
  have hslot₀ : S.C.slot ((M.slotStart S.C s : ℕ) : Int) = s :=
    hsl _ ▸ (GoldilocksCorrectness.Record.Proofs.Routines.slot_eq_of_mem M.toSlotLayout F.sched) S le_rfl
      (by omega)
  have hslotv : S.C.slot ((M.voteTime S.C s : ℕ) : Int) = s :=
    hsl _ ▸ (GoldilocksCorrectness.Record.Proofs.Routines.slot_eq_of_mem M.toSlotLayout F.sched) S
      (by omega) (by omega)
  have hslotc : S.C.slot ((M.supportCutoff S.C s : ℕ) : Int) = s :=
    hsl _ ▸ (GoldilocksCorrectness.Record.Proofs.Routines.slot_eq_of_mem M.toSlotLayout F.sched) S
      (by omega) (by omega)
  have hcR : ((M.supportCutoff S.C s : ℕ) : ℝ) = (M.voteTime S.C s : ℝ) + Δ S := by
    rw [← ht₂]; push_cast; ring
  have ht₀R : (t₀ : ℝ) + Δ S ≤ M.voteTime S.C s := by exact_mod_cast ht₀
  -- the real times of `u`'s tick `i` and of `w`'s tick `kR`
  obtain ⟨⟨hTi0, hTi⟩, hTi10, hTi1⟩ := (time_of_lbl_tick M) x R E hl
  have hkRt := (E.tick_active kR w _ hkR).2
  rw [hcR] at hkRt
  have hik : i < kR := by
    by_contra hcon
    have := htime (show kR ≤ i by omega)
    linarith [hkRt.1]
  have hui : u ∉ A.corrupted i := E.not_mem_corrupted_of_tick hl
  have hwkR : w ∉ A.corrupted kR := E.not_mem_corrupted_of_tick hkR
  -- `kR` comes no later than `kc`
  have hRc : kR ≤ kc := by
    by_contra hcon
    have hle := E.clock_mono kc kR w c (M.supportCutoff S.C s) (by omega) hwkR (Or.inl hkc) (Or.inl hkR)
    have hcc : c = M.supportCutoff S.C s := le_antisymm hle hc
    rw [hcc] at hkc
    exact absurd (E.tick_unique kc kR w _ hkc hkR) (by omega)
  have huj : ∀ j, j ≤ kc → u ∉ A.corrupted j := fun j hj h => hu (E.corrupted_mono j kc hj h)
  have hti_w : x.tickInput w c = x.st kc w := by
    unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hkc]
  have hti_u : x.tickInput u (M.voteTime S.C s) = x.st i u := by
    unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hl]
  rw [hti_w] at hF ⊢
  rw [hti_u] at hHT
  -- `w`'s tick `k₂` to the vote time of slot `s`, before `kR`
  obtain ⟨k₂, hk₂, -, hk₂1⟩ := E.tick_of_active (M.voteTime S.C s) (by omega) w fun j h1 h2 => by
    refine hwin j (by linarith) ?_
    by_contra hcon
    have := htime (show kR ≤ j by omega)
    linarith [hkRt.1]
  -- the re-delivery premise, for every release clock value at most the vote time
  have hprem : ∀ (r j₀ k₁ t₁ : ℕ), r ≤ M.voteTime S.C s → ¬ x.ReactedAtLeast j₀ w r → j₀ < k₁ →
      x.lbl k₁ = Event.tick w t₁ →
      (∀ (l t' : ℕ), j₀ < l → l < k₁ → x.lbl l = Event.tick w t' → t' < r) →
      x.time (k₁ + 1) + ΔRedeliver ≤ x.time kR := by
    intro r j₀ k₁ t₁ hr hnr hjk₁ hlk₁ hfirst
    have hj₀k₂ : j₀ < k₂ := by
      by_contra hcon
      exact hnr ⟨k₂, by omega, _, hr, Or.inl hk₂⟩
    have hk₁k₂ : k₁ ≤ k₂ := by
      by_contra hcon
      have := hfirst k₂ _ hj₀k₂ (by omega) hk₂
      omega
    have h1 := htime hk₁k₂
    rw [R.time_keep k₁ (by rw [hlk₁]; exact nofun)]
    linarith [hkRt.1]
  -- `w`'s clock value at `kR` is less than the support cutoff
  have hcvR : x.clockValue kR w < M.supportCutoff S.C s :=
    clockValue_lt_of_tick_of_active M F E hkR (by omega) fun j hj hjk => hwin j (by linarith) hjk
  have hcvle : ∀ j, j ≤ kR → x.clockValue j w < M.supportCutoff S.C s := fun j hj =>
    lt_of_le_of_lt (E.clockValue_mono hj hwkR) hcvR
  -- the vote: delivered before `kR`, admitted
  obtain ⟨dv, hdv, hdvle⟩ := hdl ⟨u, NamedObject.gfVote (GoldfishVote.mk u s Hu.root)⟩ (x.time (i + 1)) hTi1
  obtain ⟨j, -, hjk, hlj, hadm, -⟩ := E.delivered i kR w
    ⟨u, NamedObject.gfVote (GoldfishVote.mk u s Hu.root)⟩ _ dv ⟨hsent, hui⟩
    (show acObject (NamedObject.gfVote (GoldfishVote.mk u s Hu.root)) from trivial) hkR hik
    (fun j h1 h2 => hwin j (by linarith [htime h1]) h2) hdv (by linarith [hkRt.1])
    (fun r j₀ k₁ t₁ hrel _ _ hnr hjk₁ _ hlk₁ _ hfirst => hprem r j₀ k₁ t₁
      (by rw [← Option.some.inj hrel]; show M.slotStart S.C s ≤ _; omega) hnr hjk₁ hlk₁ hfirst)
  have hreact : x.ReactedAtLeast j w (M.slotStart S.C s) := hadm _ rfl (by omega)
  obtain ⟨hwj, hstep⟩ := (deliver_step_state M F) x R E hlj
  have hwjc : w ∉ A.corrupted j := Activity.not_mem_corrupted_of_mem_active hwj
  have hge := (le_clockValue_of_reactedAtLeast M F) E hlj hwjc hreact
  have hlt := hcvle j hjk.le
  have hclock := (clock_eq_clockValue M F) x R j w
  have hs2 : (GoldfishVote.mk u s Hu.root).slot ≤ S.C.slot (x.st j w).t := by
    rw [hclock]
    show s ≤ _
    rw [← hslot₀]
    exact GoldilocksCorrectness.Proofs.Routines.slot_mono_int S (by exact_mod_cast hge)
  have hs1 : S.C.slot (x.st j w).t ≤ (GoldfishVote.mk u s Hu.root).slot + 1 := by
    have : S.C.slot (x.st j w).t ≤ s := by
      rw [hclock, ← hslotc]
      exact GoldilocksCorrectness.Proofs.Routines.slot_mono_int S (by exact_mod_cast hlt.le)
    exact Nat.le_succ_of_le this
  have hvoteR : GoldfishVote.mk u s Hu.root ∈ M.votesHeldSet (x.st kR w) s := by
    rcases F.rcv.receive_gfVote_cases S.C S.P S.X (x.st j w) (GoldfishVote.mk u s Hu.root) hs1 hs2 hcomm
      with hin | heqv
    · rw [← hstep] at hin
      exact (pool_mono M F) x R E w (show j + 1 ≤ kR by omega) s hin
    · obtain ⟨v₁, h₁, v₂, h₂, hne, hi₁, hi₂⟩ :=
        (GoldilocksCorrectness.Record.Proofs.Routines.two_votes_of_equivocates M F) heqv
      exact absurd ((unique_vote_of_owner_at M F R) E hOwner (huj j (by omega)) h₁ h₂ hi₁ hi₂) hne
  have hvote₃ : GoldfishVote.mk u s Hu.root ∈ M.votesHeldSet (x.st kc w) s :=
    (pool_mono M F) x R E w hRc s hvoteR
  -- `Hu` is in `w`'s tree at `kR`
  have hcompatR : (x.st kR w).finalized.compatible Hu = true :=
    GoldilocksCorrectness.Proofs.Routines.compatible_of_ancestorEq_compatible
      ((F_ancestorEq_of_le M F) x R E w hRc) hF
  have hcvi : x.clockValue i u ≤ M.voteTime S.C s := E.clockValue_le_of_set hui (Or.inl hl)
  have hHslot : Hu.slot ≤ s := by
    have h := (slot_le_clockValue_of_mem_tree M F) R E hui hHT
    rw [← hslotv]
    exact h.trans (GoldilocksCorrectness.Proofs.Routines.slot_mono_int S (by exact_mod_cast hcvi))
  have hrb : M.slotStart S.C Hu.slot ≤ M.slotStart S.C s := by
    rw [hssn, hssn]; exact Nat.mul_le_mul_left _ hHslot
  have hTR : ∀ j', j' < kR → x.time j' ≤ x.time kR := fun j' hj' => htime hj'.le
  have hTi' : x.time i ≤ x.time kR := hTR i hik
  have hblock : Hu ∈ (x.st kR w).tree := by
    by_cases hg : Hu = Block.genesis
    · rw [hg]
      exact (GoldilocksCorrectness.Record.Statements.Executions.genesis_mem_T_of_exec M F) S A x R E _ w
    obtain ⟨ie, hie, hsende, hhone, -, hie1⟩ := (tree_block_relayed_entry M F) x R E hHT hg
    by_cases hlate : (t₀ : ℝ) ≤ x.time (ie + 1)
    · -- `u` relayed `Hu` from `t₀` on: the relay is delivered before `kR`
      obtain ⟨d, hd, hdle⟩ := hdl ⟨u, NamedObject.block Hu⟩ (x.time (ie + 1))
        (le_trans (htime (show ie + 1 ≤ i by omega)) hTi)
      obtain ⟨j', -, hjk', hlj', hadm', -⟩ := E.delivered ie kR w ⟨u, NamedObject.block Hu⟩ _ d
        ⟨hsende, hhone⟩ (show acObject (NamedObject.block Hu) from trivial) hkR (by omega)
        (fun j h1 h2 => hwin j (le_trans hlate (htime h1)) h2) hd (by linarith [hkRt.1])
        (fun r j₀ k₁ t₁ hrel _ _ hnr hjk₁ _ hlk₁ _ hfirst => hprem r j₀ k₁ t₁
          (by rw [← Option.some.inj hrel]; show M.slotStart S.C Hu.slot ≤ _; omega) hnr hjk₁ hlk₁ hfirst)
      exact (mem_tree_of_admitted_delivery M F U) R E hRoots hParent hui hTi' hHT hlj' (hTR j' hjk')
        (hadm' _ rfl (by omega)) hjk' hwkR hcompatR
    · -- `u` held `Hu` before `t₀`: the sync fact at `t₀`
      push_neg at hlate
      have h1t : 1 ≤ t₀ := by
        have h0 : (0 : ℝ) ≤ x.time (ie + 1) := by rw [← R.time_zero]; exact htime (Nat.zero_le _)
        have : (0 : ℝ) < t₀ := lt_of_le_of_lt h0 hlate
        exact_mod_cast this
      have hiek : ie < x.stepBefore t₀ := ((lt_stepBefore_iff M) x R E).2 hlate
      obtain ⟨hk1, hk2⟩ := (stepBefore_time M) x R E h1t
      have hki : x.stepBefore t₀ < i := (lt_of_time_lt M) x R (by linarith)
      have huk : u ∈ A.active (x.stepBefore t₀) :=
        Activity.mem_activeThroughout.1 hHold _ (by linarith) hk2
      have hcomp_i : (x.st i u).finalized.compatible Hu = true := by
        have h := (vote_head_compatible_of_held M F U) x R E s u Hu ⟨i, hl, hsent⟩
          (by rw [hti_u]; exact hHT)
        rw [hti_u] at h
        exact h
      have hserve : servesMin M S.C (x.st (x.stepBefore t₀) u) (x.clockValue (x.stepBefore t₀) u)
          (NamedObject.block Hu) :=
        ⟨(mem_T_mono M F) x R E u (show ie + 1 ≤ x.stepBefore t₀ by omega) hie1,
          GoldilocksCorrectness.Proofs.Routines.compatible_of_ancestorEq_compatible
            ((F_ancestorEq_of_le M F) x R E u hki.le) hcomp_i, hg⟩
      obtain ⟨d, hd, hdle⟩ := hsync ⟨u, NamedObject.block Hu⟩
      rcases Sy (t₀ : ℝ) (x.stepBefore t₀) u w (NamedObject.block Hu) d (M.supportCutoff S.C s) kR hk1 hk2 huk
          hserve trivial
          (by
            rw [Nat.ceil_natCast]
            exact fun j h1 h2 => Activity.mem_activeThroughout.1 hHold j h2 (le_trans h1 (htime (Nat.le_succ j))))
          (by rw [Nat.ceil_natCast]; exact hd) hkR hdle (fun j h1 h2 => hwin j h1 h2)
          (fun r j₀ k₁ t₁ hrel _ hnr hjk₁ _ hlk₁ _ hfirst => hprem r j₀ k₁ t₁
            (by rw [← Option.some.inj hrel]; show M.slotStart S.C Hu.slot ≤ _; omega) hnr hjk₁ hlk₁ hfirst)
        with hwB | ⟨j', k'', hk''j, hk''t, hk''o, hlj', hjk', hadm', -⟩
      · exact (mem_T_mono M F) x R E w (show x.stepBefore t₀ ≤ kR by omega) hwB.1
      · have hk''T : x.time k'' ≤ x.time kR := htime (show k'' ≤ kR by omega)
        exact (mem_tree_of_admitted_delivery M F U) R E hRoots hParent (huj k'' (by omega)) hk''T hk''o.1
          hlj' (hTR j' hjk') (hadm' _ rfl (by omega)) hjk' hwkR hcompatR
  have hblock₃ : Hu ∈ (x.st kc w).tree := (mem_T_mono M F) x R E w hRc hblock
  -- the two stamps, clock values of `w` before `kR`
  have hcut : ((((M.supportCutoff S.C s : ℕ) : Int)) : Stamp) =
      ((S.C.t_ s + 2 * S.C.Δ : Time) : Stamp) := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_cast M.toSlotLayout F.sched U)]
  obtain ⟨e, he, -, -, hτv⟩ := (voteStamp_entry_clock M F) R E hvoteR
  have hτvlt : ((x.st (e + 1) w).t : Stamp) < ((((M.supportCutoff S.C s : ℕ) : Int)) : Stamp) := by
    rw [(clock_eq_clockValue M F) x R (e + 1) w]
    exact_mod_cast hcvle (e + 1) (by omega)
  have hτv₃ : (x.st kc w).voteStamp (GoldfishVote.mk u s Hu.root) = some ((x.st (e + 1) w).t : Stamp) := by
    rw [(voteStamp_kept M F) x R E w hRc hvoteR, hτv]
  obtain ⟨τH, hτH, hτHlt⟩ : ∃ τH : Stamp, (x.st kc w).blockStamp Hu = some τH ∧
      τH < ((((M.supportCutoff S.C s : ℕ) : Int)) : Stamp) := by
    by_cases hg : Hu = Block.genesis
    · rw [hg]
      exact ⟨⊥, (genesis_stamp M F) x R E kc w, WithBot.bot_lt_coe _⟩
    obtain ⟨e', he', -, -, hτ⟩ := (blockStamp_entry_clock M F) R E hblock hg
    refine ⟨_, by rw [(blockStamp_kept M F) x R E w hRc hblock, hτ], ?_⟩
    rw [(clock_eq_clockValue M F) x R (e' + 1) w]
    exact_mod_cast hcvle (e' + 1) (by omega)
  rw [hcut] at hτvlt hτHlt
  refine ⟨hvote₃, ⟨_, hτv₃, hτvlt⟩, hblock₃, hHslot, ⟨τH, hτH, hτHlt⟩, ?_⟩
  intro vote' hv' hi'
  exact (unique_vote_of_owner_at M F R) E hOwner (huj kc le_rfl) hv' hvote₃ hi' rfl

/-- **Kit theorem, Lemma 12's core at the receiver's own ticks** (T-RC6-1, B3-R1's eighth launch). The
voter `u`, a member of slot `s`'s committee outside the adversary set at `kc`, puts its vote for the root
of `Hu` on the wire at its tick `i` to the vote time of slot `s`, holding `Hu` there; `w` ticks at `kR` to
the support cutoff of slot `s`, active at every step from the real time `t₀` up to `kR`, and later at `kc`
to a clock value `c`. Then `w`'s state at `kc` holds `u`'s vote, stamped and resolved before the support
cutoff, the only vote of `u` of slot `s` there.

Why: the vote is delivered before `kR` (`delivered`, its deadline `hdl`), found `w`'s clock at the start of
slot `s` (`releaseOf`, its re-delivery premise from `w`'s tick to the vote time and `hRedeliver`) and at most
the support cutoff, so `w` admits it or holds two votes of `u` (`receive_gfVote_cases`), which one vote per
slot excludes (`unique_vote_of_owner_at`). `Hu` entered `u`'s tree at a step `ie` at which `u` relayed it
(`tree_block_relayed_entry`): from the real time `t₀` on, the relay is delivered before `kR` (`delivered`);
before `t₀`, `u` holds and serves `Hu` at the last step before `t₀` and stays online for `ΔHolderOnline`
after it (`hHold`), so the sync fact `Sy` delivers it before `kR` or `w` holds it already; an admitted
delivery is held (`mem_tree_of_admitted_delivery`, roots naming blocks until the real time of `w`'s own
tick to the cutoff). The stamps are clock values of `w` before `kR`, less than the cutoff
(`clockValue_lt_of_tick_of_active`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`, `R`, `E`: the setup, the activity, the execution, its facts and the environment's facts
  with the deadline `deadline`; `Sy`: the sync fact with the sync deadline `sync` and the holder's online
  time `ΔHolderOnline`; `s`: the slot; `c`: the later clock value; `u`: the voter; `w`: the receiver;
  `Hu`: the vote's block; `t₀`: the real time the sync fact is read at; `kR`, `kc`: `w`'s ticks.

Read aloud: an honest early vote of slot `s`, whose block its voter keeps serving for `ΔHolderOnline` from
`t₀`, is held, stamped and resolved before the support cutoff, and unique, in the state of every later tick
of a validator active from `t₀` up to its tick to that cutoff. -/
theorem lem12_vote_held_at_tick_core (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (s c : ℕ) (u w : V) (Hu : Block V)
    {deadline} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline (releaseOf M S.C) ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    -- a message on the wire at a real time at most `ΔClockBehind` after the vote time of slot `s` is due
    -- `ΔClockAhead` before the support cutoff of slot `s` or earlier
    (hdl : ∀ (sm : SignedMsg V (NamedObject V)) (a : ℝ), a ≤ (M.voteTime S.C s : ℝ) + ΔClockBehind →
      ∃ d : ℝ, deadline sm a = some d ∧ d + ΔClockAhead ≤ (M.supportCutoff S.C s : ℝ))
    {sync : V → SignedMsg V (NamedObject V) → ℕ → Option ℕ} {ΔHolderOnline : ℝ}
    (Sy : GoldilocksCorrectness.Statements.AbstractTrace.SyncedWithinBy A x (servesMin M S.C) acObject
      (releaseOf M S.C) ΔRedeliver sync ΔHolderOnline)
    (hHO : 0 ≤ ΔHolderOnline)
    -- the sync fact is read at `t₀`, at least one delay before the vote time of slot `s`, with a deadline for
    -- `w` at most the support cutoff of slot `s`
    (t₀ : ℕ) (ht₀ : t₀ + Δ S ≤ M.voteTime S.C s)
    (hsync : ∀ sm, ∃ d : ℕ, sync w sm t₀ = some d ∧ d ≤ M.supportCutoff S.C s)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep w (M.supportCutoff S.C s))))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hc : M.supportCutoff S.C s ≤ c) (kc : ℕ) (hkc : x.lbl kc = Event.tick w c)
    (hcomm : u ∈ S.P.committee s) (hu : u ∉ A.corrupted kc)
    (hsend : ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s) ∧
      (⟨u, NamedObject.gfVote (GoldfishVote.mk u s Hu.root)⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i)
    (hHT : Hu ∈ (x.tickInput u (M.voteTime S.C s)).tree)
    -- the voter is active in every configuration in force at a real time of `[t₀, t₀ + ΔHolderOnline]`
    (hHold : u ∈ A.activeThroughout x (t₀ : ℝ) ((t₀ : ℝ) + ΔHolderOnline))
    -- `w` ticks to the support cutoff of slot `s` at `kR`, active at every step from the real time `t₀` up
    -- to `kR`
    (hw : ∃ kR : ℕ, x.lbl kR = Event.tick w (M.supportCutoff S.C s) ∧
      ∀ j : ℕ, (t₀ : ℝ) ≤ x.time j → j ≤ kR → w ∈ A.active j)
    (hF : (x.tickInput w c).finalized.AncestorEq Hu) :
    HeldEarlyVoteFor M S.C (x.tickInput w c) s Hu u := by
  obtain ⟨hvote, ⟨τv, hτv, hτvlt⟩, htree, hslot, ⟨τH, hτH, hτHlt⟩, huniq⟩ :=
    (lem12_vote_held_at_tick_core_compat M F U) S A x R s c u w Hu E hSkew hRedeliver hdl Sy hHO t₀ ht₀ hsync hRoots
      hParent hOwner hc kc hkc hcomm hu hsend hHT hHold hw ((compatible_iff _ _).2 (Or.inl hF))
  have hHΦ : Hu ∈ (M.fg_to_ac (x.tickInput w c)).tree :=
    ((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).2 ⟨htree, hF⟩
  have htau : ResolvesAt M (x.tickInput w c) (GoldfishVote.mk u s Hu.root) (max τv τH) :=
    ⟨_, τH, Hu, hτv, hHΦ, rfl, hslot, hτH, rfl⟩
  refine ⟨hvote, ⟨_, hτv, hτvlt⟩, hHΦ, ⟨_, htau, ?_⟩, huniq⟩
  exact (occurrenceBefore_eq_true_iff _ _).2 ⟨_, rfl, max_lt hτvlt hτHlt⟩

end TickCore


/-- The read time of the sync fact in Lemma 12's four forms, `supportCutoff s − max (2 · Δ S) Δs`, is at least one
delay before the vote time of slot `s`, and one sync delay after it is at most the support cutoff.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `S`: the setup; `s`: the slot; `Δs`: the
  sync delay; `GST`: the time from which the network is synchronous.

Read aloud: the sync fact's read time leaves a delay before the vote and a sync delay before the cutoff. -/
theorem lem12_holder_read_time (U : UniformSchedule M.toSlotLayout) (S : Setup V) (s Δs GST : ℕ)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s) :
    M.supportCutoff S.C s - max (2 * Δ S) Δs + Δ S ≤ M.voteTime S.C s ∧
      M.supportCutoff S.C s - max (2 * Δ S) Δs + Δs ≤ M.supportCutoff S.C s ∧
      GST + Δs ≤ M.supportCutoff S.C s ∧ GST ≤ M.voteTime S.C s ∧
      M.supportCutoff S.C s = M.voteTime S.C s + Δ S := by
  have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s
  have h2 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s
  have hΔ := one_le_Δ S
  have hm1 := le_max_left (Δ S) Δs
  have hm2 := le_max_right (Δ S) Δs
  have hm3 := le_max_left (2 * Δ S) Δs
  have hm4 := le_max_right (2 * Δ S) Δs
  rcases max_cases (2 * Δ S) Δs with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;>
    refine ⟨by omega, by omega, by omega, by omega, by omega⟩

/-- **Lemma 12 at any later time, `w` active at steps from the sync fact's read time.**
`lem12_honest_vote_delivered_until` with `w`'s activity given as `w`'s tick `kR` to the support cutoff of slot `s` and
`w` active at every step from the real time `supportCutoff s − max (2 · Δ S) Δs` up to `kR`, the form
`lem12_vote_held_at_tick_core` reads, in place of `w`'s tick-window reader from a start `tStartW` more than both clock
bounds before that read time. A caller holding `w` active at every real time from before the read time to after
the tick (a real-time window) supplies it at every slot, also when no natural `tStartW` exists (the read time at most
both clock bounds).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform.

Read aloud: an honest early vote of slot `s` is held, resolved and unique at every later tick of a validator active
at every step from the sync fact's read time up to its tick to the support cutoff. -/
theorem lem12_honest_vote_delivered_until_of_steps (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s c : ℕ) (Hs : Finset V) (H : V → Block V) (w : V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks until the real time of `w`'s own tick to the support cutoff of slot `s`
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep w (M.supportCutoff S.C s))))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s)
    -- `w` ticks at `kc` to a clock value `c` at least the support cutoff of slot `s`
    (hc : M.supportCutoff S.C s ≤ c) (kc : ℕ) (hkc : x.lbl kc = Event.tick w c)
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ A.corrupted kc ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H u ∈ (x.tickInput u (M.voteTime S.C s)).tree)
    -- every voter is active in every configuration in force at a real time of `[t₀, t₀ + Δs]`, `t₀` the sync
    -- fact's read time `supportCutoff s − max (2 * Δ S) Δs` (:'s holder clause)
    (hHold : ∀ u ∈ Hs, u ∈ A.activeThroughout x ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- `w` ticks to the support cutoff of slot `s` at `kR` and is active at every step from the sync fact's read
    -- time `supportCutoff s − max (2 * Δ S) Δs` up to `kR` (the core's form)
    (hw : ∃ kR : ℕ, x.lbl kR = Event.tick w (M.supportCutoff S.C s) ∧
      ∀ j : ℕ, ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) ≤ x.time j → j ≤ kR → w ∈ A.active j)
    (hF : ∀ u ∈ Hs, (x.tickInput w c).finalized.AncestorEq (H u)) :
    ∀ u ∈ Hs, HeldEarlyVoteFor M S.C (x.tickInput w c) s (H u) u := by
  intro u hu
  obtain ⟨hcomm, hhon, hsend, hHT⟩ := hHs u hu
  obtain ⟨ht₀, ht₀s, hGs, hGv, hcv⟩ := lem12_holder_read_time M F U S s Δs GST hGST
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hcR : ((M.supportCutoff S.C s : ℕ) : ℝ) = (M.voteTime S.C s : ℝ) + Δ S := by
    rw [hcv]; push_cast; ring
  have hGvR : (GST : ℝ) ≤ M.voteTime S.C s := by exact_mod_cast hGv
  refine (lem12_vote_held_at_tick_core M F U) S A x R s c u w (H u) E hSkew hRedeliver ?_ Sy
    (Nat.cast_nonneg _) _ ht₀ ?_ hRoots hParent hOwner hc kc hkc hcomm hhon hsend hHT (hHold u hu) ?_ (hF u hu)
  · intro sm a ha
    refine ⟨_, rfl, ?_⟩
    have : max a (GST : ℝ) ≤ (M.voteTime S.C s : ℝ) + ΔClockBehind := max_le ha (by linarith)
    rw [hcR]; linarith
  · intro sm
    refine ⟨_, rfl, ?_⟩
    rcases max_cases (M.supportCutoff S.C s - max (2 * Δ S) Δs) GST with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> omega
  · exact hw

/-- **`lem12_honest_vote_delivered_until_of_steps` with `w`'s finalized block compatible with every voter's block** (re-check 79 (a),
STOP P2-39). The hypotheses of `lem12_honest_vote_delivered_until_of_steps`, with `hF` read as compatibility of `w`'s finalized block at
its tick to `c` with each voter's block; the conclusion, for every voter `u` of `Hs`, the clauses of
`lem12_vote_held_at_tick_core_compat`: `w`'s state holds `u`'s vote of slot `s` for the root of `H u`, stamped before the
support cutoff `C.t_ s + 2 · C.Δ`; `H u` is in `w`'s node tree with its slot at most `s` and its block stamp before the
cutoff; and the vote is `u`'s only vote of slot `s` there. The proof is `lem12_honest_vote_delivered_until_of_steps`'s, over the compat core.

The variables: as `lem12_honest_vote_delivered_until_of_steps`'s.

Read aloud: every voter's honest early vote of slot `s` is held and stamped before the support cutoff, for a block `w`
holds, as the voter's only vote of the slot, at every later tick of `w` whose finalized block is compatible with that
voter's block. -/
theorem lem12_honest_vote_delivered_until_of_steps_compat (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s c : ℕ) (Hs : Finset V) (H : V → Block V) (w : V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks until the real time of `w`'s own tick to the support cutoff of slot `s`
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep w (M.supportCutoff S.C s))))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s)
    -- `w` ticks at `kc` to a clock value `c` at least the support cutoff of slot `s`
    (hc : M.supportCutoff S.C s ≤ c) (kc : ℕ) (hkc : x.lbl kc = Event.tick w c)
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ A.corrupted kc ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H u ∈ (x.tickInput u (M.voteTime S.C s)).tree)
    -- every voter is active in every configuration in force at a real time of `[t₀, t₀ + Δs]`, `t₀` the sync
    -- fact's read time `supportCutoff s − max (2 * Δ S) Δs` (:'s holder clause)
    (hHold : ∀ u ∈ Hs, u ∈ A.activeThroughout x ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- `w` ticks to the support cutoff of slot `s` at `kR` and is active at every step from the sync fact's read
    -- time `supportCutoff s − max (2 * Δ S) Δs` up to `kR` (the core's form)
    (hw : ∃ kR : ℕ, x.lbl kR = Event.tick w (M.supportCutoff S.C s) ∧
      ∀ j : ℕ, ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) ≤ x.time j → j ≤ kR → w ∈ A.active j)
    -- `w`'s finalized block at its tick to `c` is compatible with every voter's block
    (hF : ∀ u ∈ Hs, (x.tickInput w c).finalized.compatible (H u) = true) :
    ∀ u ∈ Hs, GoldfishVote.mk u s (H u).root ∈ M.votesHeldSet (x.tickInput w c) s ∧
      (∃ τ : Stamp, (x.tickInput w c).voteStamp (GoldfishVote.mk u s (H u).root) = some τ ∧
        τ < ((S.C.t_ s + 2 * S.C.Δ : Time) : Stamp)) ∧
      H u ∈ (x.tickInput w c).tree ∧ (H u).slot ≤ s ∧
      (∃ τH : Stamp, (x.tickInput w c).blockStamp (H u) = some τH ∧
        τH < ((S.C.t_ s + 2 * S.C.Δ : Time) : Stamp)) ∧
      ∀ vote' ∈ M.votesHeldSet (x.tickInput w c) s, vote'.val_index = u →
        vote' = GoldfishVote.mk u s (H u).root := by
  intro u hu
  obtain ⟨hcomm, hhon, hsend, hHT⟩ := hHs u hu
  obtain ⟨ht₀, ht₀s, hGs, hGv, hcv⟩ := lem12_holder_read_time M F U S s Δs GST hGST
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hcR : ((M.supportCutoff S.C s : ℕ) : ℝ) = (M.voteTime S.C s : ℝ) + Δ S := by
    rw [hcv]; push_cast; ring
  have hGvR : (GST : ℝ) ≤ M.voteTime S.C s := by exact_mod_cast hGv
  refine (lem12_vote_held_at_tick_core_compat M F U) S A x R s c u w (H u) E hSkew hRedeliver ?_ Sy
    (Nat.cast_nonneg _) _ ht₀ ?_ hRoots hParent hOwner hc kc hkc hcomm hhon hsend hHT (hHold u hu) ?_ (hF u hu)
  · intro sm a ha
    refine ⟨_, rfl, ?_⟩
    have : max a (GST : ℝ) ≤ (M.voteTime S.C s : ℝ) + ΔClockBehind := max_le ha (by linarith)
    rw [hcR]; linarith
  · intro sm
    refine ⟨_, rfl, ?_⟩
    rcases max_cases (M.supportCutoff S.C s - max (2 * Δ S) Δs) GST with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> omega
  · exact hw


/-- The delivery lemma at any time `t₃` from the support cutoff of slot `s` on: `lem12`'s proof with
`t₃` in place of the vote time of slot `s + 1`, which it reads only through
`M.supportCutoff S.C s ≤ t₃` and `u`'s honesty up to it. `hw` covers only slot `s`'s vote time to
its support cutoff, the window the proof uses. Its
reading is on the statement page,
`GoldilocksCorrectness/Statements/Executions/DeliveryStatements.lean`. Roots name blocks until
the real time of `w`'s own tick to `M.supportCutoff S.C s`: the proof takes `H u` as held by `w` at a delivery before the support
cutoff (`lem12_vote_held_at_tick_core`).

The variables:
- `M`: the model; `F`: its facts.

Read aloud: an honest early vote of slot `s` reaches, by the support cutoff, every validator awake
and honest from the vote time to the support cutoff, and is held, resolved and unique in its node
state before any later `t₃` up to which the voter stays honest.

Every voter is active in every configuration in force at a real time of `[t₀, t₀ + Δs]`,
`t₀ := supportCutoff s − max (2 · Δ S) Δs`, the time the sync fact is read at: a block `H u` the voter held before `t₀` reaches `w` through the sync fact
read at `t₀` (`lem12_vote_held_at_tick_core`). -/
theorem lem12_honest_vote_delivered_until (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s c : ℕ) (Hs : Finset V) (H : V → Block V) (w : V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks until the real time of `w`'s own tick to the support cutoff of slot `s`
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep w (M.supportCutoff S.C s))))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s)
    -- `w` ticks at `kc` to a clock value `c` at least the support cutoff of slot `s`, with no restart of `w`
    -- that loses its memory between its tick to the cutoff and `kc`
    (hc : M.supportCutoff S.C s ≤ c) (kc : ℕ) (hkc : x.lbl kc = Event.tick w c)
    (hkeep : ∀ (l t' : ℕ), x.tickStep w (M.supportCutoff S.C s) < l → l < kc →
      x.lbl l ≠ Event.restart w t' false)
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ A.corrupted kc ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H u ∈ (x.tickInput u (M.voteTime S.C s)).tree)
    -- every voter is active in every configuration in force at a real time of `[t₀, t₀ + Δs]`, `t₀` the sync
    -- fact's read time `supportCutoff s − max (2 * Δ S) Δs` (:'s holder clause)
    (hHold : ∀ u ∈ Hs, u ∈ A.activeThroughout x ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- `w` is active from `tStartW`, more than both clock bounds before the earlier of the start of slot `s` and
    -- one delay or one sync delay before the support cutoff, up to its own tick to the support cutoff of slot `s`
    -- (T-RC6-1:'s reader,'s bound)
    (tStartW : ℤ)
    (htStartW : (tStartW : ℝ) + ΔClockAhead + ΔClockBehind < ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ))
    (hw : w ∈ A.activeThroughoutToTick x tStartW (M.supportCutoff S.C s))
    (hF : ∀ u ∈ Hs, (x.tickInput w c).finalized.AncestorEq (H u)) :
    ∀ u ∈ Hs, HeldEarlyVoteFor M S.C (x.tickInput w c) s (H u) u := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  exact (lem12_honest_vote_delivered_until_of_steps M F U) S A x R GST s c Hs H w E hNet hSkew hRedeliver Sy hΔs
    hRoots hParent hOwner hGST hc kc hkc hHs hHold
    ((tick_window_of_activeThroughoutToTick_int M) x R E hw (by push_cast at htStartW ⊢; linarith)) hF

/-- The delivery lemma. `hw` covers only slot `s`'s vote time to its support cutoff, the window
the proof uses. Its reading is on the statement page,
`GoldilocksCorrectness/Statements/Executions/DeliveryStatements.lean`. Roots name blocks until
the real time of `w`'s own tick to `M.supportCutoff S.C s`: `lem12_honest_vote_delivered_until`'s bound.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: an honest early vote of slot `s` is held, resolved and unique in the node state before
the next vote time of every validator awake and honest from the vote time to the support cutoff.

Every voter is active in every configuration in force at a real time of `[t₀, t₀ + Δs]`,
`t₀ := supportCutoff s − max (2 · Δ S) Δs`, the time the sync fact is read at: a block `H u` the voter held before `t₀` reaches `w` through the sync fact
read at `t₀` (`lem12_vote_held_at_tick_core`). -/
theorem lem12_honest_vote_delivered (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s : ℕ) (Hs : Finset V) (H : V → Block V) (w : V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks until the real time of `w`'s own tick to the support cutoff of slot `s`
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep w (M.supportCutoff S.C s))))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s)
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ A.corrupted (x.tickStep w (M.supportCutoff S.C s)) ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H u ∈ (x.tickInput u (M.voteTime S.C s)).tree)
    -- every voter is active in every configuration in force at a real time of `[t₀, t₀ + Δs]`, `t₀` the sync
    -- fact's read time `supportCutoff s − max (2 * Δ S) Δs` (:'s holder clause)
    (hHold : ∀ u ∈ Hs, u ∈ A.activeThroughout x ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- `w` is active from `tStartW`, more than both clock bounds before the earlier of the start of slot `s` and
    -- one delay or one sync delay before the support cutoff, up to its own tick to the support cutoff of slot `s`
    -- (T-RC6-1:'s reader,'s bound)
    (tStartW : ℤ)
    (htStartW : (tStartW : ℝ) + ΔClockAhead + ΔClockBehind < ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ))
    (hw : w ∈ A.activeThroughoutToTick x tStartW (M.supportCutoff S.C s))
    (hF : ∀ u ∈ Hs, (x.tickInput w (M.supportCutoff S.C s)).finalized.AncestorEq (H u)) :
    ∀ u ∈ Hs, HeldEarlyVoteFor M S.C (x.tickInput w (M.supportCutoff S.C s)) s (H u) u := by
  -- `w`'s tick `kc` to the support cutoff of slot `s`, at a real time at most the vote time of slot `s + 1`
  obtain ⟨kc, hkc, -⟩ := (tick_window_of_activeThroughoutToTick_int M) x R E hw
    (behind_lt_of_ahead_behind_lt_int M x E htStartW)
  have hts : x.tickStep w (M.supportCutoff S.C s) = kc := (tickStep_eq_of_lbl M) x E hkc
  exact (lem12_honest_vote_delivered_until M F U) S A x R GST s (M.supportCutoff S.C s) Hs H w E hNet hSkew hRedeliver Sy hΔs
    hRoots hParent hOwner hGST le_rfl kc hkc (fun l t' h3 h4 => absurd h4 (by omega))
    (fun u hu => ⟨(hHs u hu).1, hts ▸ (hHs u hu).2.1, (hHs u hu).2.2⟩)
    hHold tStartW htStartW hw hF

omit [RootOrder] in
/-- The delivery lemma's conclusion is what `lem8b` reads for a voter. Its reading is on the
statement page.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: a held early vote is an early vote, the voter's only one of the slot. -/
theorem heldEarlyVoteFor_earlyVoteOnceFor (C : Config) (n : M.N) (s : Slot)
    (H_u : Block V) (u : V) (h : HeldEarlyVoteFor M C n s H_u u) :
    EarlyVoteOnceFor M C n s H_u u := by
  obtain ⟨hmem, -, -, hres, huniq⟩ := h
  exact ⟨_, hmem, rfl, rfl, hres, huniq⟩

omit [RootOrder] in
/-- The delivery lemma's conclusion is what `lem5` reads for a voter. Its reading is on the
statement page.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: a held early vote is the voter's only vote of the slot in the pool, for a block of the
frame's tree. -/
theorem heldEarlyVoteFor_votesOnceInPoolFor (C : Config) (n : M.N)
    (s : Slot) (H_u : Block V) (u : V) (h : HeldEarlyVoteFor M C n s H_u u) :
    VotesOnceInPoolFor M n s H_u u := by
  obtain ⟨hmem, -, htree, ⟨y, hy, -⟩, huniq⟩ := h
  exact ⟨_, hmem, rfl, ⟨y, hy⟩, ⟨H_u, htree, rfl, ancestorEq_refl H_u⟩, huniq⟩

end GoldilocksCorrectness.Record.Proofs.Executions

