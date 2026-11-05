module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.LockSteps
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Wake
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Confirmation
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.InvariantStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.TickDefs
public import GoldilocksCorrectness.Proofs.Executions.Lemma40

@[expose] public section

/-!
# Lemma40, over a model

The definition and the theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma40.lean`, over a
model `M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: the invariant
`SavedTraced` of a validator's saved confirmations, kept by every step (the theorem
`step_saved_changed` of the record's `LockSteps` page), and Lemma 40, where a saved confirmation
comes from. The update's clause states every outcome of the tick at the support cutoff under the
wake condition (template A3): every outcome saves the same confirmation
(`confirmationUpdated_saved_eq`), and the tick starts from the state before the cutoff
(`cutoff_state_facts_of_active`). The page's routine-level theorems are the facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (supportCutoff)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ supportCutoff_eq)

open GoldilocksCorrectness.Proofs.Routines (acState_initial_eq initial_eq)

namespace GoldilocksCorrectness.Record.Proofs.Executions

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor ConfirmationUpdated)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (expireLocks)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- `SavedTraced M x v s' C' i`: if the validator `v`'s saved confirmation of slot `s'` at the step
`i` of `x` is `some C'`, then, writing `c` for the support cutoff of slot `s' + 1` and `X` for `v`'s
node state before `c`: the step `stepBefore M x c` comes before `i`; `v`'s tick at `c` starts from a
state whose `awakeSince` is some time at most the duty window's start of slot `s' + 1`; every
outcome `(n', sent)` of the tick at `c` from `X`, when `X` is awake for slot `s' + 1` (`AwakeFor`),
saves `C'` as the confirmation of slot `s'`; and at every step after `stepBefore M x c` up to `i`,
`v`'s saved confirmation of slot `s'` is `some C'`.

The landed definition names the answer of the confirmation update; the record's states every
outcome of the tick under the wake condition. At the spec's model the
two agree (`goldilocks_SavedTraced`).

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `v`: the validator; `s'`: the slot of the confirmation; `C'`: the block;
  `i`: the step.

Read aloud: a saved confirmation of slot `s'` at the step `i` was saved by `v`'s update of slot
`s' + 1` and has been kept since. -/
def SavedTraced (S : Setup V) (x : Trace V (NamedObject V) M.N) (v : V)
    (s' : ℕ) (C' : Block V) (i : ℕ) : Prop :=
  (x.st i v).savedConfirmation s' = some C' →
    x.stepBefore (M.supportCutoff S.C (s' + 1)) < i ∧
    (∃ τ : Time, (x.tickInput v (M.supportCutoff S.C (s' + 1))).awakeSince = some τ ∧ τ ≤ duty_window_start S.C (s' + 1)) ∧
    (∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.stateBefore (M.supportCutoff S.C (s' + 1)) v)
        ((M.supportCutoff S.C (s' + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.stateBefore (M.supportCutoff S.C (s' + 1)) v) (s' + 1) →
      M.savedConfirmation n' s' = some C') ∧
    ∀ i' : ℕ, x.stepBefore (M.supportCutoff S.C (s' + 1)) < i' → i' ≤ i →
      (x.st i' v).savedConfirmation s' = some C'

/-- The deleted `cutoff_state_facts` (false over the trace) with the hypothesis that `v` is active at the support cutoff `c` of slot
`s + 1` added: over the trace a validator not active at `c` has no tick to `c`, and the node state
`x.tickInput v c` is then its initial state, whose `awakeSince` is present and early, while `v`'s
state before `c` need not be awake for slot `s + 1`. When `v` is active at `c`, the node state its
tick at `c` starts from, having a wake time `τ` at most the duty window's start of slot `s + 1`, is
`v`'s state before `c` (`tickInput_eq_stateBefore_of_awakeSince_some`), and that state is awake for
slot `s + 1`, satisfies the model's node invariant (Lemma 11), has a clock at most `c`
(`stateBefore_clock_le`); and `c`, read as a time, is the support cutoff of its slot, which is
`s + 1` (`U`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `hWS`: the trace is
  wake-shaped; `s`: the slot before the cutoff's; `v`: the validator; `τ`: the wake time.

Read aloud: a validator active at the support cutoff of slot `s + 1`, awake for its duty, ticks
there from its state before the cutoff, which the tick's facts can be applied to. -/
theorem cutoff_state_facts_of_active (U : UniformSchedule M.toSlotLayout) {S : Setup V}
    {A : Activity V} (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
 (s : ℕ) (v : V) (τ : Time)
    -- `v` is active at the support cutoff of slot `s + 1`
    (hv : v ∈ A.activeAtTime x (M.supportCutoff S.C (s + 1)))
    -- the tick at the support cutoff starts from a node state awake since `τ`
    (hτ : (x.tickInput v (M.supportCutoff S.C (s + 1))).awakeSince = some τ)
    -- `τ` is at most the duty window's start of slot `s + 1`
    (hτle : τ ≤ duty_window_start S.C (s + 1)) :
    AwakeFor M S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) (s + 1) ∧
      M.nodeInv S.C S.P S.X (x.tickInput v (M.supportCutoff S.C (s + 1))) ∧
      (x.tickInput v (M.supportCutoff S.C (s + 1))).t ≤
        ((M.supportCutoff S.C (s + 1) : ℕ) : Int) ∧
      ((M.supportCutoff S.C (s + 1) : ℕ) : Int) =
        S.C.t_ (S.C.slot ((M.supportCutoff S.C (s + 1) : ℕ) : Int)) + 2 * S.C.Δ ∧
      S.C.slot ((M.supportCutoff S.C (s + 1) : ℕ) : Int) = s + 1 := by
  have hsl : S.C.slot ((M.supportCutoff S.C (s + 1) : ℕ) : Int) = s + 1 := by
    rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast,
      ← (GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U)]
    exact ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_slot M.toSlotLayout F.sched) S s).1
  -- the tick's step: `v` is honest there and its clock value there is at most the cutoff
  have hk : v ∉ A.corrupted (x.tickStep v (M.supportCutoff S.C (s + 1))) ∧
      x.clockValue (x.tickStep v (M.supportCutoff S.C (s + 1))) v ≤ M.supportCutoff S.C (s + 1) := by
    by_cases hex : ∃ i : ℕ, x.lbl i = Event.tick v (M.supportCutoff S.C (s + 1))
    · obtain ⟨i, hi⟩ := hex
      rw [(tickStep_eq_of_lbl M) x E hi]
      have hvi := Activity.not_mem_corrupted_of_mem_active (E.tick_active i v _ hi).1
      exact ⟨hvi, E.clockValue_le_of_set hvi (Or.inl hi)⟩
    · have h0 : x.tickStep v (M.supportCutoff S.C (s + 1)) = 0 := by
        unfold Trace.tickStep
        rw [dif_neg hex]
      rw [h0]
      refine ⟨?_, by simp [Trace.clockValue]⟩
      obtain ⟨k, hk1, hk2⟩ := E.exists_inForce R.time_zero (fun _ _ h => R.time_mono h)
        (Nat.cast_nonneg (M.supportCutoff S.C (s + 1)))
      have hvk := Activity.not_mem_corrupted_of_mem_active (Activity.mem_activeAtTime.1 hv k hk1 hk2)
      exact fun h => hvk (E.corrupted_mono 0 k (Nat.zero_le k) h)
  refine ⟨⟨τ, hτ, hτle⟩, ((lem11_node_invariant M F S A x R E _ v) hk.1).1, ?_, ?_, hsl⟩
  · unfold Trace.tickInput
    rw [(clock_eq_clockValue M F) x R _ v]
    exact_mod_cast hk.2
  · rw [hsl]
    exact (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_cast M.toSlotLayout F.sched U) S (s + 1)

/-- Two outcomes of the confirmation update of slot `s ≥ 1` from one node state `n` save the same
confirmation of slot `s − 1`: each saves the block where the update's walk ends when that block
passes the test, and the walk ends at one block (`walkEnd_eq_of_walkSteps`).

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`: the parameters; `n`: the node state before the update; `n₁`, `n₂`: two node states
  after it; `t`: the time; `s`: the slot; `H`: the block saved.

Read aloud: the update saves the same confirmation in every outcome. -/
theorem confirmationUpdated_saved_eq {C : Config} {P : Provisional V} {n n₁ n₂ : M.N} {t : Time}
    {s : Slot} {H : Block V}
    -- the slot is not the first
    (hs : 1 ≤ s)
    -- `n₁` and `n₂` are what the update of slot `s` leaves from `n`
    (h₁ : ConfirmationUpdated M C P n t s n₁) (h₂ : ConfirmationUpdated M C P n t s n₂)
    -- `n₁` saves `H` as the confirmation of slot `s − 1`
    (hS : n₁.savedConfirmation (s - 1) = some H) :
    n₂.savedConfirmation (s - 1) = some H := by
  obtain ⟨hW, hE, -, -⟩ :=
    GoldilocksCorrectness.Record.Proofs.Routines.confirmationUpdated_saved_some hs h₁ hS
  obtain ⟨-, H', hW', hS', -⟩ := h₂.resolve_left fun h0 => Nat.one_le_iff_ne_zero.1 hs h0.1
  letI : GoldilocksCorrectness.Statements.Routines.TieBreak V := M.tieBreak
  have hH : H' = H := GoldilocksCorrectness.Proofs.Routines.walkEnd_eq_of_walkSteps hW.1 hW.2 hW'
  rw [hS', hH, if_pos hE]

/-- `SavedTracedAfterTick M S x v s' C' i`: if the validator `v`'s saved confirmation of slot `s'`
at the step `i` of `x` is `some C'`, then, writing `c` for the support cutoff of slot `s' + 1` and
`X` for the node state `v`'s tick to `c` reads (`x.tickInput v c`): the step `x.tickStep v c` comes before `i` and is `v`'s tick to
`c`; that tick starts from a state whose `awakeSince` is some time at most the duty window's start
of slot `s' + 1`; every outcome `(n', sent)` of the tick at `c` from `X`, when `X` is awake for slot
`s' + 1` (`AwakeFor`), saves `C'` as the confirmation of slot `s'`; and at every step after `v`'s
tick to `c` up to `i`, `v`'s saved confirmation of slot `s'` is `some C'`.

It is `SavedTraced` with `v`'s own tick to `c` in place of `x.stepBefore c`: over the trace the
steps from `x.stepBefore c` to `v`'s tick come before the update, so `SavedTraced`'s last clause
fails at them.

The variables:
- `M`: the model; `S`: the setup;
- `x`: the execution; `v`: the validator; `s'`: the slot of the confirmation; `C'`: the block;
  `i`: the step.

Read aloud: a saved confirmation of slot `s'` at the step `i` was saved by `v`'s update of slot
`s' + 1`, at `v`'s own tick, and has been kept since. -/
def SavedTracedAfterTick (S : Setup V) (x : Trace V (NamedObject V) M.N) (v : V)
    (s' : ℕ) (C' : Block V) (i : ℕ) : Prop :=
  (x.st i v).savedConfirmation s' = some C' →
    x.tickStep v (M.supportCutoff S.C (s' + 1)) < i ∧
    x.lbl (x.tickStep v (M.supportCutoff S.C (s' + 1))) =
      Event.tick v (M.supportCutoff S.C (s' + 1)) ∧
    (∃ τ : Time, (x.tickInput v (M.supportCutoff S.C (s' + 1))).awakeSince = some τ ∧
      τ ≤ duty_window_start S.C (s' + 1)) ∧
    (∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (M.supportCutoff S.C (s' + 1)))
        ((M.supportCutoff S.C (s' + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput v (M.supportCutoff S.C (s' + 1))) (s' + 1) →
      M.savedConfirmation n' s' = some C') ∧
    ∀ i' : ℕ, x.tickStep v (M.supportCutoff S.C (s' + 1)) < i' → i' ≤ i →
      (x.st i' v).savedConfirmation s' = some C'

/-- `SavedTracedAfterTick` holds at every step: by induction on the step, from the initial AC
state, which saves no confirmation, through `step_saved_changed`. It is the copy of the deleted `savedTraced`
for `SavedTracedAfterTick`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`: the setup, the activity, the execution; `R`: the run's facts; `E`: the
  environment's facts; `v`: the validator; `s'`: the slot of the
  confirmation; `C'`: the block; `i`: the step.

Read aloud: a saved confirmation at a step was saved by the validator's update of the next slot,
at its own tick, and kept since. -/
theorem savedTracedAfterTick (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
        {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
 (v : V)
    (s' : ℕ) (C' : Block V) (i : ℕ) : SavedTracedAfterTick M S x v s' C' i := by
  induction i with
  | zero =>
      intro h
      rw [(getElem_zero_st M F) x R, F.init.initial_savedConfirmation] at h
      cases h
  | succ i ih =>
      intro h
      by_cases hc : (x.st (i + 1) v).savedConfirmation s' = (x.st i v).savedConfirmation s'
      · -- the step keeps the field
        obtain ⟨h1, hlab, h2, h3, h4⟩ := ih (hc ▸ h)
        refine ⟨by omega, hlab, h2, h3, fun i' hi₁ hi₂ => ?_⟩
        rcases Nat.lt_or_eq_of_le hi₂ with hlt | heq
        · exact h4 i' hi₁ (by omega)
        · rw [heq]
          exact h
      · -- the step is `v`'s tick to the support cutoff `c` of slot `s' + 1`; its input has a wake
        -- time, so it is `v`'s state before `c`, and the step leaves what the confirmation update
        -- of slot `s' + 1` leaves from that state
        obtain ⟨hl, hvA, hτ, hCU⟩ := (step_saved_changed M F U) x R E i v s' hc
        have hts : x.tickStep v (M.supportCutoff S.C (s' + 1)) = i := (tickStep_eq_of_lbl M) x E hl
        have hΔ := one_le_Δ S
        have hc1 : 1 ≤ M.supportCutoff S.C (s' + 1) := by
          rw [(GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U)]
          omega
        obtain ⟨τ, hτs, hτle⟩ := hτ
        have hti : x.tickInput v (M.supportCutoff S.C (s' + 1)) = x.st i v := by
          unfold Trace.tickInput
          rw [hts]
        refine ⟨by omega, by rw [hts]; exact hl, ⟨τ, hτs, hτle⟩, ?_, fun i' hi₁ hi₂ => ?_⟩
        · -- every outcome of that tick, from that state awake for the slot, saves `C'` too: the
          -- update's walk ends at one block (`confirmationUpdated_saved_eq`)
          intro n' sent hrun hA
          have hsl : S.C.slot ((M.supportCutoff S.C (s' + 1) : ℕ) : Int) = s' + 1 := by
            rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast,
              ← (GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U)]
            exact ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_slot M.toSlotLayout F.sched) S s').1
          have hcut : ((M.supportCutoff S.C (s' + 1) : ℕ) : Int) =
              S.C.t_ (S.C.slot ((M.supportCutoff S.C (s' + 1) : ℕ) : Int)) + 2 * S.C.Δ := by
            rw [hsl]
            exact (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_cast M.toSlotLayout F.sched U) S (s' + 1)
          have hCU' := F.tk2.tick_supportCutoff_confirmation S.C S.P S.X _ _ n' sent hrun
            (by rw [hti]; exact ((lem11_node_invariant M F S A x R E i v)
              (Activity.not_mem_corrupted_of_mem_active hvA)).1)
            hcut (by rw [hsl]; exact hA)
          rw [hsl] at hCU'
          exact confirmationUpdated_saved_eq M F (Nat.le_add_left 1 s') hCU hCU' h
        · have : i' = i + 1 := by omega
          rw [this]
          exact h

/-- **Lemma 40, where a saved confirmation comes from.** The proof; the audited statement is in
`Statements/Executions/LockProvenanceStatements.lean`. Write `c` for the support cutoff of slot
`s' + 1` and `X` for `v`'s node state before `c`: when `v`'s node state before `t` saves `C'` as the
confirmation of slot `s'`, `c` is before `t`, `v`'s tick at `c` starts from a state awake since the
duty window's start of slot `s' + 1`, every outcome `(n', sent)` of the tick at `c` from `X`, when
`X` is awake for slot `s' + 1`, saves `C'` as the confirmation of slot `s'`, and at every time `t'`
after `c` up to `t`, `v`'s node state before `t'` saves `C'` as the confirmation of slot `s'`.

The landed statement names the answer of the confirmation update; the twin states every outcome of
the tick under the wake condition. Its recovery is exact: at the spec's
model the tick at `c` has an outcome, which holds the update's answer.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `i`: the step; `v`: the validator;
- `s'`: the slot of the confirmation; `C'`: the block saved.

Read aloud: a saved confirmation of slot `s'` on `v`'s state at the step `i` was saved by `v`'s update
of slot `s' + 1`, at its own tick at a step before `i`, and has been kept since. -/
theorem lem40_saved_confirmation_provenance (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (i : ℕ) (v : V) (s' : ℕ) (C' : Block V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSaved : (x.st i v).savedConfirmation s' = some C') :
    x.tickStep v (M.supportCutoff S.C (s' + 1)) < i ∧
      x.lbl (x.tickStep v (M.supportCutoff S.C (s' + 1))) = Event.tick v (M.supportCutoff S.C (s' + 1)) ∧
      (∃ τ : Time, (x.tickInput v (M.supportCutoff S.C (s' + 1))).awakeSince = some τ ∧ τ ≤ duty_window_start S.C (s' + 1)) ∧
      (∀ (n' : M.N) (sent : List (NamedObject V)),
        .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (M.supportCutoff S.C (s' + 1)))
          ((M.supportCutoff S.C (s' + 1) : ℕ) : Int) →
        AwakeFor M S.C (x.tickInput v (M.supportCutoff S.C (s' + 1))) (s' + 1) →
        M.savedConfirmation n' s' = some C') ∧
      ∀ i' : ℕ, x.tickStep v (M.supportCutoff S.C (s' + 1)) < i' → i' ≤ i →
        (x.st i' v).savedConfirmation s' = some C' := by
  exact (savedTracedAfterTick M F U) S A x R E v s' C' i hSaved

/-- A validator whose node state before `t` saves a confirmation of slot `s'` is active at the
support cutoff of slot `s' + 1`: the confirmation was saved at `v`'s own tick to that cutoff
(`savedTracedAfterTick`), and a tick is by a validator active at its time (`E.tick_active`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`: the setup, the activity, the execution; `R`: the run's facts; `E`: the
  environment's facts; `t`: the time; `v`: the validator;
  `s'`: the slot of the confirmation; `C'`: the block saved.

Read aloud: if `v`'s node state before `t` saves `C'` as the confirmation of slot `s'`, then `v` is
active at the support cutoff of slot `s' + 1`. -/
theorem active_of_saved_confirmation (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (t : ℕ) (v : V) (s' : ℕ) (C' : Block V)
        {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)

    (hSaved : (x.stateBefore t v).savedConfirmation s' = some C') :
    v ∈ A.active (x.tickStep v (M.supportCutoff S.C (s' + 1))) := by
  obtain ⟨-, hlab, -⟩ :=
    (savedTracedAfterTick M F U) S A x R E v s' C' (x.stepBefore t) hSaved
  exact (E.tick_active _ _ _ hlab).1

end GoldilocksCorrectness.Record.Proofs.Executions

