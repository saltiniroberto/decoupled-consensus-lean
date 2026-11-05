module
public import GoldilocksCorrectness.Proofs.Executions.Steps
public import GoldilocksCorrectness.Statements.Executions.AsyncResilienceDefs

@[expose] public section

/-! The consequence of the network
model that the proofs of vote and block propagation use: a message of the object class `ok` an
honest validator put on the wire at a time at most `t ≥ GST` is delivered, before `t + Δ`,
to every validator awake and outside the adversary set throughout `[t, t + Δ]`. The network
assumptions `SynchronyFromWake` and `CatchUpOnWake` are taken at the class `ok`, so the lemma is
used with `acObject` and the delay `Δ S` for blocks and Goldfish votes.

The proof is the case analysis on the receiver's last wake before `t`. If the receiver was awake
at every time from the time the message is on the wire, `x[i + 1].time`, through `t`,
`SynchronyFromWake` delivers it before the deadline
`max x[i + 1].time GST + Δ ≤ t + Δ`, counted from the time the message is on the wire.
Otherwise, the receiver was asleep at some time from `x[i + 1].time` on; at the latest such time
`t'`, it wakes at `t' + 1 ≤ t` and stays awake through `t + Δ`, and `CatchUpOnWake` delivers the
message before `max (t' + 1) GST + Δ ≤ t + Δ`. Both need the receiver outside the adversary set
from `x[i + 1].time` on, which corruption being permanent gives from its being outside it at `t`.

- `mem_awakeThroughout_iff`, `mem_awakeThroughout_of_forall`: the schedule's `awakeThroughout`
  read time by time;
- `delivered_before_of_honest_send_upTo`: the delivery, at a step after the send and at a time
  before `t + Δ`, from the two premises restricted to the deadlines up to `t + Δ`
  (`SynchronyFromWakeUpTo`, `CatchUpOnWakeUpTo`);
- `delivered_before_of_honest_send`: its instance on the two premises;
- `delivered_before_stepBefore_of_honest_send`: the same delivery, at a step before
  `stepBefore x (t + Δ)`, so its effect is in the receiver's node state before `t + Δ`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open GoldilocksCorrectness.Statements.Routines (Δ)

namespace GoldilocksCorrectness.Proofs.Executions

open GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks (NamedObject RootOrder)
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A validator is in the schedule's `awakeThroughout t t'` exactly when it is in the awake set at
every time from `t` to `t'`.

The variables:
- `Sched`: the schedule; `t`, `t'`: the ends of the interval; `v`: the validator.

Read aloud: awake throughout `[t, t']` means awake at each time of it. -/
theorem mem_awakeThroughout_iff {Sched : Schedule V} {t t' : Int} {v : V} :
    v ∈ Sched.awakeThroughout t t' ↔ ∀ t'' : Int, t ≤ t'' → t'' ≤ t' → v ∈ Sched.awake t'' := by
  unfold Schedule.awakeThroughout
  constructor
  · intro h t'' h1 h2
    exact Finset.mem_of_subset (Finset.inf_le (Finset.mem_Icc.2 ⟨h1, h2⟩)) h
  · intro h
    refine Finset.singleton_subset_iff.1 (Finset.le_inf ?_)
    intro t'' ht''
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 ht''
    exact Finset.singleton_subset_iff.2 (h t'' h1 h2)

/-- A validator in the awake set at every natural-number time from `t` to `t'` is in the
schedule's `awakeThroughout` over the same interval, cast to `Int`.

The variables:
- `Sched`: the schedule; `t`, `t'`: the ends of the interval; `v`: the validator.

Read aloud: awake at each time of `[t, t']` means awake throughout it. -/
theorem mem_awakeThroughout_of_forall {Sched : Schedule V} {t t' : ℕ} {v : V}
    -- `v` is awake at every time from `t` to `t'`
    (h : ∀ t'' : ℕ, t ≤ t'' → t'' ≤ t' → v ∈ Sched.awake (t'' : Int)) :
    v ∈ Sched.awakeThroughout (t : Int) (t' : Int) := by
  rw [mem_awakeThroughout_iff]
  intro t'' h1 h2
  have := h t''.toNat (by omega) (by omega)
  rwa [Int.toNat_of_nonneg (by omega)] at this

variable [RootOrder] {S : Setup V} {Sched : Schedule V} (x : AtomicExec (protocol S) Sched)

/-- A message of the object class `ok` an honest validator put on the wire at the step `i`, at a
time at most `t ≥ GST`, is delivered to every validator that is awake and outside the adversary
set at every time from `t` to `t + Δ`, at a step after `i` and at a time before `t + Δ`.

The variables:
- `x`: the execution; `Δ`: the delay bound; `GST`: the time from which the network is
  synchronous; `ok`: the class of objects the network assumptions promise about;
- `i`: the step of the send; `t`: the time; `v`: the receiver; `sm`: the signed message;
- `j`: the step of the delivery.

Read aloud: a message of the class `ok` an honest validator put on the wire at a time at most
`t ≥ GST` is delivered, before `t + Δ`, to every validator awake and honest throughout
`[t, t + Δ]`.

Restated with the delivery premises up to `t + Δ`, the latest deadline its proof reads
(`max x[i + 1].time GST + Δ` in the synchrony case, `max (a + 1) GST + Δ` in the catch-up case, both
at most `t + Δ`); `delivered_before_of_honest_send` is its instance. -/
theorem delivered_before_of_honest_send_upTo {Δ GST : ℕ} {ok : NamedObject V → Prop} {t : ℕ}
    (hsync : SynchronyFromWakeUpTo S Sched x Δ GST ok (t + Δ))
    (hcatch : CatchUpOnWakeUpTo S Sched x Δ GST ok (t + Δ))
    (hmono : Sched.MonotoneCorruption)
    {i : ℕ} {v : V} {sm : SignedMsg V (NamedObject V)}
    (hsend : HonestSendAt Sched x.toTrace i sm)
    -- the object of `sm` is in the class `ok`
    (hok : ok sm.msg)
    -- the message is on the wire at or before `t`
    (hit : x[i + 1].time ≤ t)
    -- the network is synchronous from `t` on
    (hGST : GST ≤ t)
    -- `v` is awake and outside the adversary set at every time from `t` to `t + Δ`
    (hwin : ∀ t', t ≤ t' → t' ≤ t + Δ → v ∈ Sched.awake (t' : Int) ∧ v ∉ Sched.adv (t' : Int)) :
    ∃ j, i < j ∧ x.lbl j = AtomicAction.deliver v sm ∧ x[j].time < t + Δ := by
  classical
  have hsucc := time_succ_le x i
  have hle := time_le_succ x i
  -- `v` is outside the adversary set at every time up to `t + Δ`
  have hhon : ∀ t' : ℕ, t' ≤ t + Δ → v ∉ Sched.adv (t' : Int) := fun t' ht' hadv =>
    (hwin (t + Δ) (by omega) le_rfl).2 (hmono _ _ (by exact_mod_cast ht') hadv)
  by_cases hsleep : ∃ t', x[i + 1].time ≤ t' ∧ t' ≤ t ∧ v ∉ Sched.awake (t' : Int)
  · -- `v` was asleep at some time from `x[i + 1].time` on; `a` is the latest one up to `t`
    let P : ℕ → Prop := fun t' => x[i + 1].time ≤ t' ∧ v ∉ Sched.awake (t' : Int)
    obtain ⟨t₀, ht₀s, ht₀t, ht₀⟩ := hsleep
    have hPa : P (Nat.findGreatest P t) := Nat.findGreatest_spec (P := P) ht₀t ⟨ht₀s, ht₀⟩
    set a := Nat.findGreatest P t with ha
    have hat : a ≤ t := Nat.findGreatest_le t
    have hat' : a < t := by
      rcases Nat.lt_or_eq_of_le hat with h | h
      · exact h
      · exact absurd (h ▸ (hwin t le_rfl (by omega)).1) hPa.2
    -- `v` is awake at every time after `a` up to `t`
    have hafter : ∀ t', a < t' → t' ≤ t → v ∈ Sched.awake (t' : Int) := fun t' h1 h2 => by
      by_contra hn
      exact Nat.findGreatest_is_greatest h1 h2 ⟨by omega, hn⟩
    -- `v` wakes at `a + 1`; catch-up on wake delivers the message
    have hwake : v ∉ Sched.awake (((a + 1 : ℕ) : Int) - 1) := by
      have : ((a + 1 : ℕ) : Int) - 1 = (a : Int) := by push_cast; omega
      rw [this]
      exact hPa.2
    have hmax : max (a + 1) GST ≤ t := max_le (by omega) hGST
    obtain ⟨j, hij, hl, -, hj⟩ := hcatch i v sm (a + 1) hsend hok (by omega) (by omega)
      (hafter (a + 1) (by omega) (by omega)) hwake
      (mem_awakeThroughout_of_forall fun t' h1 h2 => by
        by_cases h : t' ≤ t
        · exact hafter t' (by omega) h
        · exact (hwin t' (by omega) (by omega)).1)
      (fun t' _ h2 => hhon t' (by omega))
    exact ⟨j, hij, hl, by omega⟩
  · -- `v` was awake at every time from `x[i + 1].time` through `t`; synchrony delivers it
    simp only [not_exists, not_and, not_not] at hsleep
    have hmax : max x[i + 1].time GST ≤ t := max_le hit hGST
    obtain ⟨j, hij, hl, -, hj⟩ := hsync i v sm hsend hok (by omega)
      (mem_awakeThroughout_of_forall fun t' h1 h2 => by
        by_cases h : t' ≤ t
        · exact hsleep t' h1 h
        · exact (hwin t' (by omega) (by omega)).1)
      (fun t' _ h2 => hhon t' (by omega))
    exact ⟨j, hij, hl, by omega⟩

/-- A message of the object class `ok` an honest validator put on the wire at the step `i`, at a
time at most `t ≥ GST`, is delivered to every validator that is awake and outside the adversary
set at every time from `t` to `t + Δ`, at a step after `i` and at a time before `t + Δ`.

The variables:
- `x`: the execution; `Δ`: the delay bound; `GST`: the time from which the network is
  synchronous; `ok`: the class of objects the network assumptions promise about;
- `i`: the step of the send; `t`: the time; `v`: the receiver; `sm`: the signed message;
- `j`: the step of the delivery.

Read aloud: a message of the class `ok` an honest validator put on the wire at a time at most
`t ≥ GST` is delivered, before `t + Δ`, to every validator awake and honest throughout
`[t, t + Δ]`. -/
theorem delivered_before_of_honest_send {Δ GST : ℕ}
    {ok : NamedObject V → Prop}
    (hsync : SynchronyFromWake Sched x.toTrace Δ GST ok) (hcatch : CatchUpOnWake Sched x.toTrace Δ GST ok)
    (hmono : Sched.MonotoneCorruption)
    {i t : ℕ} {v : V} {sm : SignedMsg V (NamedObject V)}
    (hsend : HonestSendAt Sched x.toTrace i sm)
    -- the object of `sm` is in the class `ok`
    (hok : ok sm.msg)
    -- the message is on the wire at or before `t`
    (hit : x[i + 1].time ≤ t)
    -- the network is synchronous from `t` on
    (hGST : GST ≤ t)
    -- `v` is awake and outside the adversary set at every time from `t` to `t + Δ`
    (hwin : ∀ t', t ≤ t' → t' ≤ t + Δ → v ∈ Sched.awake (t' : Int) ∧ v ∉ Sched.adv (t' : Int)) :
    ∃ j, i < j ∧ x.lbl j = AtomicAction.deliver v sm ∧ x[j].time < t + Δ :=
  -- the two premises restricted to the deadlines up to `t + Δ` (as
  -- `synchronyFromWakeUpTo_of_synchronyFromWake`, which `AsyncDelivery.lean` proves from this file)
  delivered_before_of_honest_send_upTo x (fun i' v' sm' hs hok' _ => hsync i' v' sm' hs hok')
    (fun i' v' sm' t' hs hok' hit' _ => hcatch i' v' sm' t' hs hok' hit') hmono hsend hok hit
    hGST hwin

/-- The delivery of `delivered_before_of_honest_send` comes strictly before
`stepBefore x (t + Δ)`, so the node state it produces is at or before the one
`stateBefore x (t + Δ) v` reads.

The variables:
- `x`: the execution; `Δ`: the delay bound; `GST`: the time from which the network is
  synchronous; `ok`: the class of objects the network assumptions promise about;
- `i`: the step of the send; `t`: the time; `v`: the receiver; `sm`: the signed message;
- `j`: the step of the delivery.

Read aloud: after `GST`, a validator awake and honest for a delay from `t` has, in its node state
before `t + Δ`, the delivery of every message of the class `ok` an honest validator put on the
wire by `t`. -/
theorem delivered_before_stepBefore_of_honest_send (hdiv : TimeDiverges x.toTrace) {Δ GST : ℕ}
    {ok : NamedObject V → Prop}
    (hsync : SynchronyFromWake Sched x.toTrace Δ GST ok) (hcatch : CatchUpOnWake Sched x.toTrace Δ GST ok)
    (hmono : Sched.MonotoneCorruption)
    {i t : ℕ} {v : V} {sm : SignedMsg V (NamedObject V)}
    (hsend : HonestSendAt Sched x.toTrace i sm)
    -- the object of `sm` is in the class `ok`
    (hok : ok sm.msg)
    -- the message is on the wire at or before `t`
    (hit : x[i + 1].time ≤ t)
    -- the network is synchronous from `t` on
    (hGST : GST ≤ t)
    -- `v` is awake and outside the adversary set at every time from `t` to `t + Δ`
    (hwin : ∀ t', t ≤ t' → t' ≤ t + Δ → v ∈ Sched.awake (t' : Int) ∧ v ∉ Sched.adv (t' : Int)) :
    ∃ j, i < j ∧ x.lbl j = AtomicAction.deliver v sm ∧ j < stepBefore x (t + Δ) := by
  obtain ⟨j, hij, hl, hj⟩ :=
    delivered_before_of_honest_send x hsync hcatch hmono hsend hok hit hGST hwin
  exact ⟨j, hij, hl, deliver_before_of_time x hdiv hl hj⟩

end GoldilocksCorrectness.Proofs.Executions
