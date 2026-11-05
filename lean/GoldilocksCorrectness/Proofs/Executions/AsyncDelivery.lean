module
public import GoldilocksCorrectness.Statements.Executions.AsyncResilienceDefs
public import GoldilocksCorrectness.Proofs.Executions.Network

@[expose] public section

/-!
# The delivery premises around one asynchronous period, and up to a bound

The facts relating the delivery premises suspended on one asynchronous period `[b₀, b₁)`
(`SynchronyFromWakeOutside`, `CatchUpOnWakeOutside`) to `SynchronyFromWake` and `CatchUpOnWake`:

- `synchronyFromWake_iff_by`, `catchUpOnWake_iff_by`: the premises are the deadline forms at the
  ordinary deadline `max t GST + Δ`;
- `SynchronyFromWakeUpTo.mono`, `CatchUpOnWakeUpTo.mono`: a bound on the deadlines can be lowered;
- `synchronyFromWakeUpTo_of_synchronyFromWake`, `catchUpOnWakeUpTo_of_catchUpOnWake`: the
  premises give every bounded one;
- `synchronyFromWakeUpTo_of_outside`, `catchUpOnWakeUpTo_of_outside`: before the period, the
  suspended premise is the premise restricted to the sends due by `b₀`;
- `deadlineOutside_le`, `synchronyFromWake_of_outside_after`, `catchUpOnWake_of_outside_after`:
  from the period's end, the suspended premise is the premise with `GST` moved to `max b₁ GST`.




-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (Δ)

namespace GoldilocksCorrectness.Proofs.Executions

open GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

section Delivery

variable (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)

/-- `SynchronyFromWake` is `SynchronyFromWakeBy` at the deadline `max t GST + Δ`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `Δ`: the delay; `GST`: the time
  from which the network is synchronous; `ok`: the object class.

Read aloud: synchrony is the deadline form at the ordinary deadline. -/
theorem synchronyFromWake_iff_by (Δ GST : ℕ) (ok : NamedObject V → Prop) :
    SynchronyFromWake Sched x.toTrace Δ GST ok ↔
      SynchronyFromWakeBy Sched x.toTrace (fun t => max t GST + Δ) ok :=
  Iff.rfl

/-- `CatchUpOnWake` is `CatchUpOnWakeBy` at the deadline `max t GST + Δ`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `Δ`: the delay; `GST`: the time
  from which the network is synchronous; `ok`: the object class.

Read aloud: catch-up on wake is the deadline form at the ordinary deadline. -/
theorem catchUpOnWake_iff_by (Δ GST : ℕ) (ok : NamedObject V → Prop) :
    CatchUpOnWake Sched x.toTrace Δ GST ok ↔
      CatchUpOnWakeBy Sched x.toTrace (fun t => max t GST + Δ) ok :=
  Iff.rfl

end Delivery

section DeliveryFacts

variable {S : Setup V} {Sched : Schedule V} {x : AtomicExec (protocol S) Sched} {Δ GST : ℕ}
  {ok : NamedObject V → Prop}

/-- Synchrony up to `b'` gives synchrony up to every `b ≤ b'`.

The variables:
- `b`, `b'`: the two bounds; `hle`: `b ≤ b'`; `h`: synchrony up to `b'`.

Read aloud: a bound on the deadlines can be lowered. -/
theorem SynchronyFromWakeUpTo.mono {b b' : ℕ} (hle : b ≤ b')
    (h : SynchronyFromWakeUpTo S Sched x Δ GST ok b') : SynchronyFromWakeUpTo S Sched x Δ GST ok b :=
  fun i v sm hsend hok hb hawake hhon => h i v sm hsend hok (le_trans hb hle) hawake hhon

/-- Catch-up on wake up to `b'` gives catch-up on wake up to every `b ≤ b'`.

The variables:
- `b`, `b'`: the two bounds; `hle`: `b ≤ b'`; `h`: catch-up on wake up to `b'`.

Read aloud: a bound on the deadlines can be lowered. -/
theorem CatchUpOnWakeUpTo.mono {b b' : ℕ} (hle : b ≤ b')
    (h : CatchUpOnWakeUpTo S Sched x Δ GST ok b') : CatchUpOnWakeUpTo S Sched x Δ GST ok b :=
  fun i v sm t hsend hok hit hb hw hw' hawake hhon =>
    h i v sm t hsend hok hit (le_trans hb hle) hw hw' hawake hhon

/-- `SynchronyFromWake` gives `SynchronyFromWakeUpTo` at every bound.

The variables:
- `b`: the bound; `h`: synchrony.

Read aloud: the premise gives every bounded one. -/
theorem synchronyFromWakeUpTo_of_synchronyFromWake (b : ℕ)
    (h : SynchronyFromWake Sched x.toTrace Δ GST ok) : SynchronyFromWakeUpTo S Sched x Δ GST ok b :=
  fun i v sm hsend hok _ hawake hhon => h i v sm hsend hok hawake hhon

/-- `CatchUpOnWake` gives `CatchUpOnWakeUpTo` at every bound.

The variables:
- `b`: the bound; `h`: catch-up on wake.

Read aloud: the premise gives every bounded one. -/
theorem catchUpOnWakeUpTo_of_catchUpOnWake (b : ℕ)
    (h : CatchUpOnWake Sched x.toTrace Δ GST ok) : CatchUpOnWakeUpTo S Sched x Δ GST ok b :=
  fun i v sm t hsend hok hit _ hw hw' hawake hhon => h i v sm t hsend hok hit hw hw' hawake hhon

/-- Synchrony suspended on `[b₀, b₁)` gives synchrony up to `b₀`.

Why: a send due by `b₀` has `deadlineOutside Δ GST b₀ b₁` equal to its ordinary deadline.

The variables:
- `b₀`, `b₁`: the start and the end of the period; `h`: synchrony suspended on `[b₀, b₁)`.

Read aloud: before the period, the suspended premise is the premise restricted to the sends due
by `b₀`. -/
theorem synchronyFromWakeUpTo_of_outside {b₀ b₁ : ℕ}
    (h : SynchronyFromWakeOutside Sched x.toTrace Δ GST ok b₀ b₁) :
    SynchronyFromWakeUpTo S Sched x Δ GST ok b₀ := by
  intro i v sm hsend hok hb hawake hhon
  have hd : deadlineOutside Δ GST b₀ b₁ x[i + 1].time = max x[i + 1].time GST + Δ := by
    simp only [deadlineOutside, if_pos hb]
  unfold SynchronyFromWakeOutside SynchronyFromWakeBy at h
  simp only [AtomicExec.toTrace_getElem, AtomicExec.toTrace_lbl] at h
  obtain ⟨j, hij, hl, h1, h2⟩ := h i v sm hsend hok (by rw [hd]; exact hawake)
    (fun t ht1 ht2 => hhon t ht1 (by rwa [hd] at ht2))
  exact ⟨j, hij, hl, h1, by rwa [hd] at h2⟩

/-- Catch-up on wake suspended on `[b₀, b₁)` gives catch-up on wake up to `b₀`.

Why: a wake whose ordinary deadline is at most `b₀` has `deadlineOutside Δ GST b₀ b₁` equal to
that deadline.

The variables:
- `b₀`, `b₁`: the start and the end of the period; `h`: catch-up on wake suspended on `[b₀, b₁)`.

Read aloud: before the period, the suspended catch-up is the catch-up restricted to the wakes due
by `b₀`. -/
theorem catchUpOnWakeUpTo_of_outside {b₀ b₁ : ℕ}
    (h : CatchUpOnWakeOutside Sched x.toTrace Δ GST ok b₀ b₁) :
    CatchUpOnWakeUpTo S Sched x Δ GST ok b₀ := by
  intro i v sm t hsend hok hit hb hw hw' hawake hhon
  have hd : deadlineOutside Δ GST b₀ b₁ t = max t GST + Δ := by
    simp only [deadlineOutside, if_pos hb]
  unfold CatchUpOnWakeOutside CatchUpOnWakeBy at h
  obtain ⟨j, hij, hl, h1, h2⟩ := h i v sm t hsend hok hit hw hw' (by rw [hd]; exact hawake)
    (fun t' ht1 ht2 => hhon t' ht1 (by rwa [hd] at ht2))
  exact ⟨j, hij, hl, h1, by rwa [hd] at h2⟩

omit [RootOrder] in
/-- The deadline around the period is at most the ordinary deadline with `GST` moved to
`max b₁ GST`.

The variables:
- `b₀`, `b₁`: the start and the end of the period; `t`: the time of the send.

Read aloud: `deadlineOutside Δ GST b₀ b₁ t ≤ max t (max b₁ GST) + Δ`. -/
theorem deadlineOutside_le {b₀ b₁ t : ℕ} :
    deadlineOutside Δ GST b₀ b₁ t ≤ max t (max b₁ GST) + Δ := by
  unfold deadlineOutside
  split_ifs with hc
  · exact Nat.add_le_add_right (max_le_max le_rfl (le_max_right b₁ GST)) Δ
  · exact le_rfl

/-- Synchrony suspended on `[b₀, b₁)` gives `SynchronyFromWake` at `GST' := max b₁ GST`: every
send is delivered within `Δ` of the latest of its time, `b₁` and `GST`. No hypothesis `b₀ ≤ b₁`
is needed.

Why: `deadlineOutside Δ GST b₀ b₁ t ≤ max t (max b₁ GST) + Δ` (`deadlineOutside_le`), so a
receiver awake and honest through the later deadline is so through the earlier one.

The variables:
- `b₀`, `b₁`: the start and the end of the period; `h`: synchrony suspended on `[b₀, b₁)`.

Read aloud: once the period is over, the network is the ordinary synchronous network whose `GST`
is `b₁`. -/
theorem synchronyFromWake_of_outside_after {b₀ b₁ : ℕ}
    (h : SynchronyFromWakeOutside Sched x.toTrace Δ GST ok b₀ b₁) :
    SynchronyFromWake Sched x.toTrace Δ (max b₁ GST) ok := by
  intro i v sm hsend hok hawake hhon
  have hle := deadlineOutside_le (Δ := Δ) (GST := GST) (t := x[i + 1].time) (b₀ := b₀) (b₁ := b₁)
  unfold SynchronyFromWakeOutside SynchronyFromWakeBy at h
  have hawake' : v ∈ Sched.awakeThroughout (x[i + 1].time : Int)
      ((deadlineOutside Δ GST b₀ b₁ x[i + 1].time : ℕ) : Int) := by
    rw [mem_awakeThroughout_iff] at hawake ⊢
    intro t'' h1 h2
    exact hawake t'' h1 (le_trans h2 (by exact_mod_cast hle))
  obtain ⟨j, hij, hl, h1, h2⟩ := h i v sm hsend hok hawake'
    (fun t ht1 ht2 => hhon t ht1 (le_trans ht2 hle))
  exact ⟨j, hij, hl, h1, lt_of_lt_of_le h2 hle⟩

/-- Catch-up on wake suspended on `[b₀, b₁)` gives `CatchUpOnWake` at `GST' := max b₁ GST`.

Why: as for synchrony, from `deadlineOutside_le`.

The variables:
- `b₀`, `b₁`: the start and the end of the period; `h`: catch-up on wake suspended on `[b₀, b₁)`.

Read aloud: once the period is over, a waking validator catches up as in the ordinary synchronous
network whose `GST` is `b₁`. -/
theorem catchUpOnWake_of_outside_after {b₀ b₁ : ℕ}
    (h : CatchUpOnWakeOutside Sched x.toTrace Δ GST ok b₀ b₁) :
    CatchUpOnWake Sched x.toTrace Δ (max b₁ GST) ok := by
  intro i v sm t hsend hok hit hw hw' hawake hhon
  have hle := deadlineOutside_le (Δ := Δ) (GST := GST) (t := t) (b₀ := b₀) (b₁ := b₁)
  unfold CatchUpOnWakeOutside CatchUpOnWakeBy at h
  have hawake' : v ∈ Sched.awakeThroughout (t : Int)
      ((deadlineOutside Δ GST b₀ b₁ t : ℕ) : Int) := by
    rw [mem_awakeThroughout_iff] at hawake ⊢
    intro t'' h1 h2
    exact hawake t'' h1 (le_trans h2 (by exact_mod_cast hle))
  obtain ⟨j, hij, hl, h1, h2⟩ := h i v sm t hsend hok hit hw hw' hawake'
    (fun t' ht1 ht2 => hhon t' ht1 (le_trans ht2 hle))
  exact ⟨j, hij, hl, h1, lt_of_lt_of_le h2 hle⟩

end DeliveryFacts

section Kit

variable (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)

end Kit

end GoldilocksCorrectness.Proofs.Executions
