module
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.RunFactsDefs
public import GoldilocksCorrectness.Statements.AbstractTrace.DeliveryDefs
public import GoldilocksCorrectness.Statements.Executions.UnforgeabilityDefs

@[expose] public section

/-!
# Permanent corruption

The two ways the proofs read permanent corruption (the field `corrupted_mono` of `EnvFacts`): the
adversary set at a time is contained in the one at every later time, and a validator outside the
adversary set at a time is outside it at every earlier time. They read the environment's facts only.
-/

set_option autoImplicit false

namespace GoldilocksCorrectness.Record.Proofs.Executions

open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Statements.Network (ViewVocab)

variable {V Msg N : Type} [DecidableEq V] [DecidableEq Msg] {A : Activity V} {x : Trace V Msg N}
  {Δ GST : ℕ} {ok : (m : Msg) → Prop} {B : Type} {W : ViewVocab V B Msg}

/-- Under permanent corruption, the adversary set after a step is contained in the adversary set after
every later step.

The variables:
- `A`: the activity; `E`: the environment's facts on the trace `x`;
- `i ≤ i'`: the two steps.

Read aloud: a validator in the adversary set after step `i` is in it after every step `i' ≥ i`. -/
theorem adv_subset_of_le {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver ok W) {i i' : ℕ} (hle : i ≤ i') :
    A.corrupted i ⊆ A.corrupted i' :=
  E.corrupted_mono i i' hle

/-- Under permanent corruption, a validator outside the adversary set after a step is outside it after
every earlier step.

The variables:
- `A`: the activity; `E`: the environment's facts on the trace `x`;
- `i ≤ i'`: the two steps; `v`: the validator.

Read aloud: a validator honest after step `i'` was honest after every step `i ≤ i'`. -/
theorem not_mem_adv_of_le {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver ok W) {i i' : ℕ} {v : V} (hle : i ≤ i')
    -- `v` is outside the adversary set after the later step `i'`
    (h : v ∉ A.corrupted i') : v ∉ A.corrupted i :=
  fun ha => h (adv_subset_of_le E hle ha)

open Classical in
/-- The honesty read of `honestActiveAt` at the clock value `c` (outside the adversary set after every
step at a real time at most `c`, and at every step at which a validator outside the adversary set
ticks to `c`) follows from honesty after every step at a real time at most `t`, when
`c + ΔClockBehind ≤ t`: a tick to `c` runs at a real time at most `c + ΔClockBehind`.

The variables:
- `A`: the activity; `E`: the environment's facts on the trace `x`;
- `c`: the clock value; `t`: the real time; `u`: the validator.

Read aloud: a validator honest through the real time `t` is honest through the real time `c` and at
every honest tick to `c`, when `c + ΔClockBehind ≤ t`. -/
theorem not_mem_corruptedAtTime_union_ticks_of_le [Fintype V] {deadline} {release ΔRedeliver}
    {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver ok W)
    {c : ℕ} {t : ℝ} {u : V} (hc : (c : ℝ) + ΔClockBehind ≤ t) (hu : u ∉ A.corruptedAtTime x t) :
    u ∉ A.corruptedAtTime x (c : ℝ) ∪ Finset.univ.filter (fun u => ∃ (k : ℕ) (w : V),
      x.lbl k = Event.tick w c ∧ w ∉ A.corrupted k ∧ u ∈ A.corrupted k) := by
  have hB := E.behind_nonneg
  intro h
  apply hu
  rcases Finset.mem_union.1 h with h1 | h2
  · obtain ⟨i, hi, hui⟩ := (Activity.mem_corruptedAtTime (A := A) (x := x)).1 h1
    exact (Activity.mem_corruptedAtTime (A := A) (x := x)).2 ⟨i, by linarith, hui⟩
  · obtain ⟨k, w, hk, -, huk⟩ := (Finset.mem_filter.1 h2).2
    have := (E.tick_active k w c hk).2.2
    exact (Activity.mem_corruptedAtTime (A := A) (x := x)).2 ⟨k, by linarith, huk⟩

end GoldilocksCorrectness.Record.Proofs.Executions
