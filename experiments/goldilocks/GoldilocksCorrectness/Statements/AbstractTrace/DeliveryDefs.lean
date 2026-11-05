module
public import GoldilocksCorrectness.Statements.AbstractTrace.TraceDefs
public import GoldilocksCorrectness.Statements.Network.NetworkDefs

@[expose] public section

/-!
# Delivery with a deadline, over a trace

Two instances of the environment's promises `EnvFactsBy`, and the delivery promises read alone.

- `EnvFactsOutside`: the promises suspended on one asynchronous period `[b₀, b₁)` (the deadline
  `deadlineOutsideR Δ GST b₀ b₁` of a real time, defined on this page; the sync fact keeps the
  natural-number deadline `deadlineOutside` of
  `GoldilocksCorrectness/Statements/Network/NetworkDefs.lean`);
- `EnvFactsUpTo`: the promises for the sends and the restarts due by a bound `b` only (the deadlines
  `deadlineUpTo` and `catchUpUpTo`);
- how the instances give one another: `EnvFactsSync.upTo`, `EnvFactsUpTo.mono`,
  `EnvFactsOutside.upTo`, `EnvFactsOutside.after`;
- the same two instances of the delivery promise alone, nothing promised to a validator that restarts
  (`EnvFactsDeliveryUpTo`, `EnvFactsDeliveryOutside`), and of the sync fact `SyncedWithinBy`
  (`SyncedWithinUpTo`, `SyncedWithinOutside`), with the sync fact's derivations
  `SyncedWithin.upTo`, `SyncedWithinUpTo.mono`, `SyncedWithinOutside.upTo`;
- the delivery promises read alone, with the deadline a function of the time of the send or of the
  restart (`SynchronyFromWakeBy`, `CatchUpOnWakeBy`), and their instances at the ordinary deadline and
  around one asynchronous period (`SynchronyFromWake`, `CatchUpOnWake`, `SynchronyFromWakeOutside`,
  `CatchUpOnWakeOutside`).

This page reads no protocol.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace GoldilocksCorrectness.Statements.AbstractTrace

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.Network (deadlineOutside ViewVocab)

/-- `deadlineOutsideR Δ GST b₀ b₁ t`: the delivery deadline, a real time, of a send at the real time
`t` around one asynchronous period `[b₀, b₁)`: the real-valued form of `deadlineOutside` of
`GoldilocksCorrectness/Statements/Network/NetworkDefs.lean`, which the sync fact keeps.

The variables:
- `Δ`: the delay; `GST`: the time from which the network is synchronous before `b₀`; `b₀`, `b₁`:
  the start and the end of the period; `t`: the real time of the send.

Read aloud: a send at time `t` whose ordinary deadline `max t GST + Δ` is at or before `b₀` keeps
that deadline; any other send is delivered within `Δ` of the latest of its own time, `b₁` and
`GST`. -/
noncomputable def deadlineOutsideR (Δ GST b₀ b₁ : ℕ) (t : ℝ) : ℝ :=
  if max t GST + Δ ≤ b₀ then max t GST + Δ else max t (max b₁ GST) + Δ

namespace Trace

variable {V Msg N : Type} [DecidableEq V] [DecidableEq Msg] (x : Trace V Msg N) (A : Activity V)

/-- `x.SynchronyFromWakeBy A deadline release ΔRedeliver ok`: the delivery promise `delivered` of
`EnvFactsBy` read alone, at the deadline `deadline (x.time (i + 1))` of a message on the wire after
step `i`: at `v`'s tick `k` to the reading `t`, every message of the class `ok` that an honest
validator put on the wire at a step `i` before `k`, with `v` active after every step from `i + 1` to
`k`, whose deadline is at most the time of step `k`, and, when its object has a release reading `r`
and a delivery of it to `v` after the sending found `v` not yet reacted to `r`, whose re-delivery
deadline (`ΔRedeliver` after the time of `v`'s first tick at a reading at least `r` after that
delivery) is also at most the time of step `k`, was delivered to `v` at a step `j` between `i` and
`k`; when `r` is at most `t`, that delivery found `v` already reacted to `r`; and no step between `j`
and `k` is a restart of `v` that loses its memory.

The variables:
- `x`: the trace; `A`: the activity; `deadline t`: the delivery deadline, a real time, of a message
  on the wire at the real time `t`; `release m`: the release clock value of the object of the message
  `m`; `ΔRedeliver`: the re-delivery delay; `ok`: the class of messages.

Read aloud: what an honest validator puts on the wire reaches, before every tick of the receiver at
a time at least its deadline, every validator that stays active until that tick. -/
def SynchronyFromWakeBy (deadline : ℝ → ℝ) (release : (m : Msg) → Option ℕ) (ΔRedeliver : ℕ)
    (ok : (m : Msg) → Prop) : Prop :=
  ∀ (i k : ℕ) (v : V) (sm : SignedMsg V Msg) (t : ℕ),
    x.HonestSendAt A i sm → ok sm.msg → x.lbl k = Event.tick v t → i < k →
    (∀ j : ℕ, i + 1 ≤ j → j ≤ k → v ∈ A.active j) →
    deadline (x.time (i + 1)) ≤ x.time k →
    -- after a delivery `j₀` that found `v` not yet reacted to `r`, the re-delivery deadline
    -- (`ΔRedeliver` after `v`'s first tick `k₁` at a reading at least `r`) is at most the time of `k`
    (∀ (r j₀ k₁ t₁ : ℕ), release sm.msg = some r →
      i < j₀ → x.lbl j₀ = Event.deliver v sm → ¬ x.ReactedAtLeast j₀ v r →
      j₀ < k₁ → k₁ ≤ k → x.lbl k₁ = Event.tick v t₁ → r ≤ t₁ →
      (∀ (l t' : ℕ), j₀ < l → l < k₁ → x.lbl l = Event.tick v t' → t' < r) →
      x.time (k₁ + 1) + ΔRedeliver ≤ x.time k) →
    ∃ j : ℕ, i < j ∧ j < k ∧ x.lbl j = Event.deliver v sm ∧
      (∀ r : ℕ, release sm.msg = some r → r ≤ t → x.ReactedAtLeast j v r) ∧
      ∀ (l t' : ℕ), j < l → l < k → x.lbl l ≠ Event.restart v t' false

/-- `x.CatchUpOnWakeBy A deadline release ΔRedeliver ok`: a validator `v` restarted at a step `k`
after the step `i` at which an honest validator put a message `sm` of the class `ok` on the wire
(`i < k`, so a restart at the time of the sending, after it, is covered), that ticks at a step
`k' > k` to a clock value `c'` at least `deadline (x.time k)`, active after every step `j` with
`k < j ≤ k'`: when the object of `sm` has a release clock value `r` and a delivery of `sm` to `v`
after the restart found `v` not yet reacted to `r`, provided that the re-delivery deadline
(`ΔRedeliver` after the time of `v`'s first tick after that delivery at a clock value at least `r`) is
at most the time of `k'`, `v` is delivered `sm` at a step `j` with `k < j < k'`; when `r` is at most
`c'`, that delivery found `v` already reacted to `r`; and no step between `j` and `k'` is a restart of
`v` that loses its memory.

The receiver's window ends at that tick: nothing is asked of the steps after it, and nothing is
promised about them. This is the reading of the catch-up promise `CatchUpAfterRestartBy`, in the shape
of the delivery promise `delivered`: any tick after the restart at a clock value at least
the deadline, not only the first.

The variables:
- `x`: the trace; `A`: the activity; `deadline t`: the delivery deadline, a real time, of a restart
  at the real time `t`; `release m`: the release clock value of the object of the message `m`;
  `ΔRedeliver`: the re-delivery delay; `ok`: the class of messages.

Read aloud: a validator that restarts and stays active from its restart to any of its ticks after the
restart at a clock value at least the deadline catches up, before that tick, on every earlier honest
message, with no memory-losing restart in between; and, when the object's release clock value is at
most that tick's, the delivery found the validator's clock already there, provided a re-delivery after
its clock reached that value would come before the tick. -/
def CatchUpOnWakeBy (deadline : ℝ → ℝ) (release : (m : Msg) → Option ℕ) (ΔRedeliver : ℕ)
    (ok : (m : Msg) → Prop) : Prop :=
  ∀ (i k : ℕ) (v : V) (sm : SignedMsg V Msg) (t : ℕ) (keep : Bool) (k' c' : ℕ),
    x.HonestSendAt A i sm → ok sm.msg → x.lbl k = Event.restart v t keep → i < k →
    k < k' → x.lbl k' = Event.tick v c' → deadline (x.time k) ≤ (c' : ℝ) →
    (∀ j : ℕ, k < j → j ≤ k' → v ∈ A.active j) →
    -- after a delivery `j₀` after the restart that found `v` not yet reacted to `r`, the re-delivery
    -- deadline (`ΔRedeliver` after `v`'s first tick `k₁` at a clock value at least `r`) is at most the
    -- time of `k'`
    (∀ (r j₀ k₁ t₁ : ℕ), release sm.msg = some r →
      k < j₀ → x.lbl j₀ = Event.deliver v sm → ¬ x.ReactedAtLeast j₀ v r →
      j₀ < k₁ → k₁ ≤ k' → x.lbl k₁ = Event.tick v t₁ → r ≤ t₁ →
      (∀ (l t' : ℕ), j₀ < l → l < k₁ → x.lbl l = Event.tick v t' → t' < r) →
      x.time (k₁ + 1) + ΔRedeliver ≤ x.time k') →
    ∃ j : ℕ, k < j ∧ j < k' ∧ x.lbl j = Event.deliver v sm ∧
      (∀ r : ℕ, release sm.msg = some r → r ≤ c' → x.ReactedAtLeast j v r) ∧
      ∀ (l t' : ℕ), j < l → l < k' → x.lbl l ≠ Event.restart v t' false

/-- `x.SynchronyFromWake A Δ ΔRedeliver GST release ok`: `x.SynchronyFromWakeBy A` at the deadline
`max t GST + Δ` of a message on the wire at time `t`, the delivery promise of `EnvFacts`
(`delivered`) read alone.

The variables:
- `x`: the trace; `A`: the activity; `Δ`: the delay; `ΔRedeliver`: the re-delivery delay; `GST`:
  the time from which the network is synchronous; `release`: the release reading of a message's
  object; `ok`: the class of messages.

Read aloud: what an honest validator puts on the wire reaches, by the later of the time it is on the
wire and `GST`, plus `Δ`, every validator active until then. -/
def SynchronyFromWake (Δ ΔRedeliver GST : ℕ) (release : (m : Msg) → Option ℕ)
    (ok : (m : Msg) → Prop) : Prop :=
  x.SynchronyFromWakeBy A (fun t => max t GST + Δ) release ΔRedeliver ok

/-- `x.CatchUpOnWake A Δ ΔRedeliver GST release ok`: `x.CatchUpOnWakeBy A` at the deadline
`max t GST + Δ` of a restart at time `t`, the catch-up promise of `EnvFacts` (`caught_up`) read alone.

The variables:
- `x`: the trace; `A`: the activity; `Δ`: the delay; `ΔRedeliver`: the re-delivery delay; `GST`: the
  time from which the network is synchronous; `release`: the release clock value of a message's
  object; `ok`: the class of messages.

Read aloud: a validator that restarts at `t` and stays active until a tick at a clock value at least
the later of `t` and `GST`, plus `Δ`, catches up on every earlier honest message before that tick. -/
def CatchUpOnWake (Δ ΔRedeliver GST : ℕ) (release : (m : Msg) → Option ℕ) (ok : (m : Msg) → Prop) :
    Prop :=
  x.CatchUpOnWakeBy A (fun t => max t GST + Δ) release ΔRedeliver ok

/-- `x.SynchronyFromWakeOutside A Δ ΔRedeliver GST release ok b₀ b₁`: synchrony suspended on the
asynchronous period `[b₀, b₁)`, that is `x.SynchronyFromWakeBy A` at the deadline
`deadlineOutsideR Δ GST b₀ b₁`.

The variables:
- `x`: the trace; `A`: the activity; `Δ`: the delay; `ΔRedeliver`: the re-delivery delay; `GST`:
  the time from which the network is synchronous before `b₀`; `release`: the release reading of a
  message's object; `ok`: the class of messages; `b₀`, `b₁`: the start and the end of the period.

Read aloud: a send due by `b₀` is delivered as in the synchronous network; any other send is
delivered within `Δ` of the latest of the time it is on the wire, `b₁` and `GST`. -/
def SynchronyFromWakeOutside (Δ ΔRedeliver GST : ℕ) (release : (m : Msg) → Option ℕ)
    (ok : (m : Msg) → Prop) (b₀ b₁ : ℕ) : Prop :=
  x.SynchronyFromWakeBy A (deadlineOutsideR Δ GST b₀ b₁) release ΔRedeliver ok

/-- `x.CatchUpOnWakeOutside A Δ ΔRedeliver GST release ok b₀ b₁`: catch-up after a restart suspended on
the asynchronous period `[b₀, b₁)`, that is `x.CatchUpOnWakeBy A` at the deadline
`deadlineOutsideR Δ GST b₀ b₁`.

The variables:
- `x`: the trace; `A`: the activity; `Δ`: the delay; `ΔRedeliver`: the re-delivery delay; `GST`: the
  time from which the network is synchronous before `b₀`; `release`: the release clock value of a
  message's object; `ok`: the class of messages; `b₀`, `b₁`: the start and the end of the period.

Read aloud: a restart whose ordinary deadline is at or before `b₀` catches up as in the synchronous
network; any other catches up within `Δ` of the latest of its own time, `b₁` and `GST`. -/
def CatchUpOnWakeOutside (Δ ΔRedeliver GST : ℕ) (release : (m : Msg) → Option ℕ)
    (ok : (m : Msg) → Prop) (b₀ b₁ : ℕ) : Prop :=
  x.CatchUpOnWakeBy A (deadlineOutsideR Δ GST b₀ b₁) release ΔRedeliver ok

end Trace

namespace Trace.CatchUpOnWakeBy

variable {V Msg N : Type} [DecidableEq V] [DecidableEq Msg] {x : Trace V Msg N} {A : Activity V}
  {ok : (m : Msg) → Prop} {release : (m : Msg) → Option ℕ} {ΔRedeliver : ℕ}

/-- The trace's catch-up premise read at a tick after the restart: a validator `v` restarted at the
step `k`, after an honest send of the class `ok` at the step `i < k`, that ticks at a step `k' > k` to
a clock value `c'` at least `deadline (x.time k)` and is active after every step `j` with
`k < j ≤ k'`, is delivered the message at a step `j` with `k < j < k'`, under the re-delivery premise
at `k'`, with the admission clause at `c'` and no memory-losing restart between `j` and `k'`.

The variables:
- `C`: the catch-up premise at `deadline`; `i`, `k`, `v`, `sm`, `t`, `keep`: the send, the restart
  and its validator, message, clock value and kind; `k'`, `c'`: the step of the tick and its clock
  value; `hrel`: the re-delivery premise at `k'`.

Read aloud: a restarted validator that stays up to any of its ticks, after the restart, at a clock
value at least the deadline is delivered the message before that tick. -/
theorem apply_tick {deadline : ℝ → ℝ} (C : x.CatchUpOnWakeBy A deadline release ΔRedeliver ok)
    {i k : ℕ} {v : V} {sm : SignedMsg V Msg} {t : ℕ} {keep : Bool} {k' c' : ℕ}
    (hs : x.HonestSendAt A i sm) (hok : ok sm.msg) (hk : x.lbl k = Event.restart v t keep)
    (hlt : i < k) (hkk' : k < k') (hk' : x.lbl k' = Event.tick v c')
    (hcc' : deadline (x.time k) ≤ (c' : ℝ)) (hwin : ∀ j : ℕ, k < j → j ≤ k' → v ∈ A.active j)
    (hrel : ∀ (r j₀ k₁ t₁ : ℕ), release sm.msg = some r →
      k < j₀ → x.lbl j₀ = Event.deliver v sm → ¬ x.ReactedAtLeast j₀ v r →
      j₀ < k₁ → k₁ ≤ k' → x.lbl k₁ = Event.tick v t₁ → r ≤ t₁ →
      (∀ (l t' : ℕ), j₀ < l → l < k₁ → x.lbl l = Event.tick v t' → t' < r) →
      x.time (k₁ + 1) + ΔRedeliver ≤ x.time k') :
    ∃ j : ℕ, k < j ∧ j < k' ∧ x.lbl j = Event.deliver v sm ∧
      (∀ r : ℕ, release sm.msg = some r → r ≤ c' → x.ReactedAtLeast j v r) ∧
      ∀ (l t' : ℕ), j < l → l < k' → x.lbl l ≠ Event.restart v t' false :=
  C i k v sm t keep k' c' hs hok hk hlt hkk' hk' hcc' hwin hrel

end Trace.CatchUpOnWakeBy

/-! ## The deadlines around one asynchronous period and up to a bound -/

/-- A message on the wire at the real time `t` is due at least `Δ` after `t`, around the period
`[b₀, b₁)`.

The variables:
- `Δ`: the delay; `GST`: the time from which the network is synchronous before `b₀`; `b₀`, `b₁`:
  the start and the end of the period; `t`: the time the message is on the wire.

Read aloud: no deadline is earlier than `Δ` after the message. -/
theorem add_le_deadlineOutsideR (Δ GST b₀ b₁ : ℕ) (t : ℝ) :
    t + Δ ≤ deadlineOutsideR Δ GST b₀ b₁ t := by
  unfold deadlineOutsideR
  have h1 := le_max_left t (GST : ℝ)
  have h2 := le_max_left t (max (b₁ : ℝ) GST)
  split_ifs <;> linarith

/-- A message due at or before `b₀` keeps its ordinary deadline around the period `[b₀, b₁)`.

The variables:
- `Δ`: the delay; `GST`: the time from which the network is synchronous before `b₀`; `b₀`, `b₁`:
  the start and the end of the period; `t`: the real time the message is on the wire; `h`: its
  ordinary deadline is at most `b₀`.

Read aloud: before the period, the deadline is the ordinary one. -/
theorem deadlineOutsideR_of_le {Δ GST b₀ b₁ : ℕ} {t : ℝ} (h : max t GST + Δ ≤ (b₀ : ℝ)) :
    deadlineOutsideR Δ GST b₀ b₁ t = max t GST + Δ := by
  unfold deadlineOutsideR
  rw [if_pos h]

/-- Every deadline around the period `[b₀, b₁)` is at most `Δ` after the latest of the message's
real time, `b₁` and `GST`.

The variables:
- `Δ`: the delay; `GST`: the time from which the network is synchronous before `b₀`; `b₀`, `b₁`:
  the start and the end of the period; `t`: the real time the message is on the wire.

Read aloud: after the period, the deadlines are those of the network synchronous from `b₁`. -/
theorem deadlineOutsideR_le_after (Δ GST b₀ b₁ : ℕ) (t : ℝ) :
    deadlineOutsideR Δ GST b₀ b₁ t ≤ max t (max (b₁ : ℝ) GST) + Δ := by
  unfold deadlineOutsideR
  have h := max_le_max (le_refl t) (le_max_right (b₁ : ℝ) GST)
  split_ifs <;> linarith

/-- The deadline around the period `[b₀, b₁)` is monotone in the message's real time.

The variables:
- `Δ`: the delay; `GST`: the time from which the network is synchronous before `b₀`; `b₀`, `b₁`:
  the start and the end of the period; `t`, `t'`: the two real times; `h`: `t ≤ t'`.

Read aloud: a later message is not due earlier. -/
theorem deadlineOutsideR_mono_time {Δ GST b₀ b₁ : ℕ} {t t' : ℝ} (h : t ≤ t') :
    deadlineOutsideR Δ GST b₀ b₁ t ≤ deadlineOutsideR Δ GST b₀ b₁ t' := by
  unfold deadlineOutsideR
  have h1 := max_le_max h (le_refl (GST : ℝ))
  have h2 := max_le_max h (le_refl (max (b₁ : ℝ) GST))
  have h3 := max_le_max (le_refl t) (le_max_right (b₁ : ℝ) GST)
  split_ifs <;> linarith

/-- The deadline around the period `[b₀, b₁)` is monotone in the delay.

The variables:
- `Δ`, `Δ'`: the two delays; `GST`: the time from which the network is synchronous before `b₀`;
  `b₀`, `b₁`: the start and the end of the period; `t`: the real time; `h`: `Δ ≤ Δ'`.

Read aloud: a longer delay does not make a message due earlier. -/
theorem deadlineOutsideR_mono_delay {Δ Δ' GST b₀ b₁ : ℕ} {t : ℝ} (h : Δ ≤ Δ') :
    deadlineOutsideR Δ GST b₀ b₁ t ≤ deadlineOutsideR Δ' GST b₀ b₁ t := by
  unfold deadlineOutsideR
  have h' : (Δ : ℝ) ≤ Δ' := by exact_mod_cast h
  have h3 := max_le_max (le_refl t) (le_max_right (b₁ : ℝ) GST)
  split_ifs <;> linarith

/-- A message on the wire at `t` is due at least `Δ` after `t`, around the period `[b₀, b₁)`.

The variables:
- `Δ`: the delay; `GST`: the time from which the network is synchronous before `b₀`; `b₀`, `b₁`:
  the start and the end of the period; `t`: the time the message is on the wire.

Read aloud: no deadline is earlier than `Δ` after the message. -/
theorem add_le_deadlineOutside (Δ GST b₀ b₁ t : ℕ) : t + Δ ≤ deadlineOutside Δ GST b₀ b₁ t := by
  unfold deadlineOutside
  split_ifs <;> omega

/-- A message due at or before `b₀` keeps its ordinary deadline around the period `[b₀, b₁)`.

The variables:
- `Δ`: the delay; `GST`: the time from which the network is synchronous before `b₀`; `b₀`, `b₁`:
  the start and the end of the period; `t`: the time the message is on the wire; `h`: its ordinary
  deadline is at most `b₀`.

Read aloud: before the period, the deadline is the ordinary one. -/
theorem deadlineOutside_of_le {Δ GST b₀ b₁ t : ℕ} (h : max t GST + Δ ≤ b₀) :
    deadlineOutside Δ GST b₀ b₁ t = max t GST + Δ := by
  unfold deadlineOutside
  rw [if_pos h]

/-- Every deadline around the period `[b₀, b₁)` is at most `Δ` after the latest of the message's
time, `b₁` and `GST`.

The variables:
- `Δ`: the delay; `GST`: the time from which the network is synchronous before `b₀`; `b₀`, `b₁`:
  the start and the end of the period; `t`: the time the message is on the wire.

Read aloud: after the period, the deadlines are those of the network synchronous from `b₁`. -/
theorem deadlineOutside_le_after (Δ GST b₀ b₁ t : ℕ) :
    deadlineOutside Δ GST b₀ b₁ t ≤ max t (max b₁ GST) + Δ := by
  unfold deadlineOutside
  split_ifs <;> omega

/-- The deadline around the period `[b₀, b₁)` is monotone in the message's time.

The variables:
- `Δ`: the delay; `GST`: the time from which the network is synchronous before `b₀`; `b₀`, `b₁`:
  the start and the end of the period; `t`, `t'`: the two times; `h`: `t ≤ t'`.

Read aloud: a later message is not due earlier. -/
theorem deadlineOutside_mono_time {Δ GST b₀ b₁ t t' : ℕ} (h : t ≤ t') :
    deadlineOutside Δ GST b₀ b₁ t ≤ deadlineOutside Δ GST b₀ b₁ t' := by
  unfold deadlineOutside
  split_ifs <;> omega

/-- The deadline around the period `[b₀, b₁)` is monotone in the delay.

The variables:
- `Δ`, `Δ'`: the two delays; `GST`: the time from which the network is synchronous before `b₀`;
  `b₀`, `b₁`: the start and the end of the period; `t`: the time; `h`: `Δ ≤ Δ'`.

Read aloud: a longer delay does not make a message due earlier. -/
theorem deadlineOutside_mono_delay {Δ Δ' GST b₀ b₁ t : ℕ} (h : Δ ≤ Δ') :
    deadlineOutside Δ GST b₀ b₁ t ≤ deadlineOutside Δ' GST b₀ b₁ t := by
  unfold deadlineOutside
  split_ifs <;> omega

/-- `deadlineUpTo Δ GST b a`: the ordinary deadline `max a GST + Δ` of a message on the wire at `a`
when it is at most `b`, no promise otherwise.

The variables:
- `α`: the type of the times (the real numbers for the delivery promises, the natural numbers for
  the sync fact); `Δ`: the delay; `GST`: the time from which the network is synchronous; `b`: the
  bound; `a`: the time the message is on the wire.

Read aloud: the ordinary deadline, promised only when it falls by `b`. -/
def deadlineUpTo {α : Type} [LinearOrder α] [Add α] (Δ GST b : α) (a : α) : Option α :=
  if max a GST + Δ ≤ b then some (max a GST + Δ) else none

/-- `catchUpUpTo Δ Δw GST b a t`: the catch-up deadline of a message on the wire at `a` for a
validator restarted at `t`, the later of the message's ordinary deadline and `max t GST + Δw`,
when both are at most `b`; no promise otherwise.

The variables:
- `α`: the type of the times; `Δ`: the delay; `Δw`: the catch-up delay; `GST`: the time from which
  the network is synchronous; `b`: the bound; `a`: the time the message is on the wire; `t`: the
  time of the restart.

Read aloud: a restarted validator is promised its backlog only when both its own deadline and the
message's fall by `b`. -/
def catchUpUpTo {α : Type} [LinearOrder α] [Add α] (Δ Δw GST b : α) (a t : α) : Option α :=
  match deadlineUpTo Δ GST b a, deadlineUpTo Δw GST b t with
  | some d, some c => some (max d c)
  | _, _ => none

/-- When the bounded deadline is defined, and what it is.

The variables:
- `Δ`: the delay; `GST`: the time from which the network is synchronous; `b`: the bound; `a`: the
  time the message is on the wire; `d`: the deadline.

Read aloud: the bounded deadline is `d` exactly when the ordinary one is `d` and at most `b`. -/
theorem deadlineUpTo_eq_some {α : Type} [LinearOrder α] [Add α] {Δ GST b a d : α} :
    deadlineUpTo Δ GST b a = some d ↔ max a GST + Δ ≤ b ∧ d = max a GST + Δ := by
  unfold deadlineUpTo
  split_ifs with h
  · simp only [Option.some.injEq]
    exact ⟨fun h' => ⟨h, h'.symm⟩, fun h' => h'.2.symm⟩
  · simp only [false_iff, not_and]
    exact fun h' => absurd h' h

/-- When the bounded catch-up deadline is defined, and what it is.

The variables:
- `Δ`: the delay; `Δw`: the catch-up delay; `GST`: the time from which the network is synchronous;
  `b`: the bound; `a`: the time the message is on the wire; `t`: the time of the restart; `c`: the
  deadline.

Read aloud: the bounded catch-up deadline is `c` exactly when the message's ordinary deadline and
the restart's are both at most `b`, and `c` is the later of the two. -/
theorem catchUpUpTo_eq_some {α : Type} [LinearOrder α] [Add α] {Δ Δw GST b a t c : α} :
    catchUpUpTo Δ Δw GST b a t = some c ↔
      max a GST + Δ ≤ b ∧ max t GST + Δw ≤ b ∧ c = max (max a GST + Δ) (max t GST + Δw) := by
  unfold catchUpUpTo
  by_cases h1 : max a GST + Δ ≤ b <;> by_cases h2 : max t GST + Δw ≤ b <;>
    simp [deadlineUpTo, h1, h2, eq_comm]

/-- `EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind Δ ΔRedeliver GST release ok W b`: the delivery promise for the sends
due by `b` only.

The variables:
- `A`: the activity; `x`: the trace; `ΔClockAhead`, `ΔClockBehind`: the two bounds of the clocks;
  `Δ`: the delay; `ΔRedeliver`: the re-delivery delay; `GST`: the
  time from which the network is synchronous; `release`: the release reading of a message's object;
  `ok`: the class of messages; `W`: the vocabulary; `b`: the bound on the deadlines.

Read aloud: a message is promised only when its ordinary deadline is at most `b`. -/
abbrev EnvFactsDeliveryUpTo {V Msg N : Type} [DecidableEq V] [DecidableEq Msg] (A : Activity V)
    (x : Trace V Msg N) (ΔClockAhead ΔClockBehind : ℝ) (Δ ΔRedeliver GST : ℕ) (release : (m : Msg) → Option ℕ)
    (ok : (m : Msg) → Prop) {B : Type} (W : ViewVocab V B Msg) (b : ℕ) : Prop :=
  EnvFactsBy A x ΔClockAhead ΔClockBehind (fun _ a => deadlineUpTo (α := ℝ) Δ GST b a) release ΔRedeliver ok W

/-- `EnvFactsDeliveryOutside A x ΔClockAhead ΔClockBehind Δ ΔRedeliver GST release ok W b₀ b₁`: the delivery promise
suspended on the asynchronous period `[b₀, b₁)`.

The variables:
- `A`: the activity; `x`: the trace; `ΔClockAhead`, `ΔClockBehind`: the two bounds of the clocks;
  `Δ`: the delay; `ΔRedeliver`: the re-delivery delay; `GST`: the
  time from which the network is synchronous before `b₀`; `release`: the release reading of a
  message's object; `ok`: the class of messages; `W`: the vocabulary; `b₀`, `b₁`: the start and the
  end of the period.

Read aloud: a message due at or before `b₀` keeps its ordinary deadline, any other is served
within `Δ` of the latest of its time, `b₁` and `GST`. -/
abbrev EnvFactsDeliveryOutside {V Msg N : Type} [DecidableEq V] [DecidableEq Msg]
    (A : Activity V) (x : Trace V Msg N) (ΔClockAhead ΔClockBehind : ℝ) (Δ ΔRedeliver GST : ℕ) (release : (m : Msg) → Option ℕ)
    (ok : (m : Msg) → Prop) {B : Type} (W : ViewVocab V B Msg) (b₀ b₁ : ℕ) : Prop :=
  EnvFactsBy A x ΔClockAhead ΔClockBehind (fun _ a => some (deadlineOutsideR Δ GST b₀ b₁ a)) release ΔRedeliver ok W

/-- `EnvFactsOutside A x ΔClockAhead ΔClockBehind Δ Δw ΔRedeliver GST release ok W b₀ b₁`: the promises suspended on the asynchronous period
`[b₀, b₁)`: the delivery promise `EnvFactsDeliveryOutside`, and the catch-up after a restart with
the deadline the later of the message's and the restart's, each `Δw` after the latest of its time,
`b₁` and `GST` when it falls after `b₀`. -/
structure EnvFactsOutside {V Msg N : Type} [DecidableEq V] [DecidableEq Msg] (A : Activity V)
    (x : Trace V Msg N) (ΔClockAhead ΔClockBehind : ℝ) (Δ Δw ΔRedeliver GST : ℕ) (release : (m : Msg) → Option ℕ)
    (ok : (m : Msg) → Prop) {B : Type} (W : ViewVocab V B Msg) (b₀ b₁ : ℕ) : Prop
    extends EnvFactsBy A x ΔClockAhead ΔClockBehind (fun _ a => some (deadlineOutsideR Δ GST b₀ b₁ a)) release ΔRedeliver ok W
    where
  /-- A restarted validator that stays up is delivered every earlier honest message of the class
  `ok` by the later of the message's suspended deadline and the restart's. -/
  caught_up : CatchUpAfterRestartBy A x
    (fun _ a t => some (max (deadlineOutsideR Δ GST b₀ b₁ a) (deadlineOutsideR Δw GST b₀ b₁ t)))
    release ΔRedeliver ok

/-- `EnvFactsUpTo A x ΔClockAhead ΔClockBehind Δ Δw ΔRedeliver GST release ok W b`: the promises for the sends and the restarts due by `b`
only: the delivery promise `EnvFactsDeliveryUpTo`, and the catch-up after a restart promised only
when both the restart's deadline and the message's are at most `b`. -/
structure EnvFactsUpTo {V Msg N : Type} [DecidableEq V] [DecidableEq Msg] (A : Activity V)
    (x : Trace V Msg N) (ΔClockAhead ΔClockBehind : ℝ) (Δ Δw ΔRedeliver GST : ℕ) (release : (m : Msg) → Option ℕ)
    (ok : (m : Msg) → Prop) {B : Type} (W : ViewVocab V B Msg) (b : ℕ) : Prop
    extends EnvFactsBy A x ΔClockAhead ΔClockBehind (fun _ a => deadlineUpTo (α := ℝ) Δ GST b a) release ΔRedeliver ok W where
  /-- A restarted validator that stays up is delivered every earlier honest message of the class
  `ok` whose catch-up deadline is at most `b`, by that deadline. -/
  caught_up : CatchUpAfterRestartBy A x (fun _ a t => catchUpUpTo (α := ℝ) Δ Δw GST b a t) release
    ΔRedeliver ok

/-- `SyncedWithinUpTo A x serves ok release ΔRedeliver Δs GST b`: the sync fact for the times `t` whose sync deadline
`max t GST + Δs` is at most `b` only.

The variables:
- `A`: the activity; `x`: the trace; `serves`: what a node state serves at a time; `ok`: the class
  of objects; `Δs`: the sync delay; `GST`: the time from which the network is synchronous; `b`:
  the bound on the deadlines.

Read aloud: what an honest active validator would serve at `t` is promised to reach the others
only when `Δs` after the later of `t` and `GST` is at most `b`. -/
abbrev SyncedWithinUpTo {V Msg N : Type} [DecidableEq V] (A : Activity V) (x : Trace V Msg N)
    (serves : N → ℕ → Msg → Prop) (ok : Msg → Prop) (release : Msg → Option ℕ) (ΔRedeliver : ℕ)
    (Δs GST b : ℕ) : Prop :=
  SyncedWithinBy A x serves ok release ΔRedeliver (fun _ _ t => deadlineUpTo (α := ℕ) Δs GST b t) Δs

/-- `SyncedWithinOutside A x serves ok release ΔRedeliver Δs GST b₀ b₁`: the sync fact suspended on the asynchronous
period `[b₀, b₁)`: what is served at a time `t` whose ordinary sync deadline is at or before `b₀`
keeps it, anything else is due `Δs` after the latest of `t`, `b₁` and `GST`.

The variables:
- `A`: the activity; `x`: the trace; `serves`: what a node state serves at a time; `ok`: the class
  of objects; `Δs`: the sync delay; `GST`: the time from which the network is synchronous before
  `b₀`; `b₀`, `b₁`: the start and the end of the period.

Read aloud: nothing served is promised to arrive inside the period, and what is due then is
promised `Δs` after its end. -/
abbrev SyncedWithinOutside {V Msg N : Type} [DecidableEq V] (A : Activity V) (x : Trace V Msg N)
    (serves : N → ℕ → Msg → Prop) (ok : Msg → Prop) (release : Msg → Option ℕ) (ΔRedeliver : ℕ)
    (Δs GST b₀ b₁ : ℕ) : Prop :=
  SyncedWithinBy A x serves ok release ΔRedeliver (fun _ _ t => some (deadlineOutside Δs GST b₀ b₁ t)) Δs

/-! ## How the instances give one another -/

section Instances

variable {V Msg N : Type} [DecidableEq V] [DecidableEq Msg] {A : Activity V} {x : Trace V Msg N}
  {ΔClockAhead ΔClockBehind : ℝ} {Δ Δw ΔRedeliver GST : ℕ} {release : (m : Msg) → Option ℕ} {ok : (m : Msg) → Prop} {B : Type}
  {W : ViewVocab V B Msg}

/-- The synchronous promises give the promises up to every bound `b`.

The variables:
- `E`: the synchronous promises; `b`: the bound.

Read aloud: the synchronous promises give every bounded one. -/
theorem EnvFactsSync.upTo (E : EnvFactsSync A x ΔClockAhead ΔClockBehind Δ Δw ΔRedeliver GST release ok W) (b : ℕ) :
    EnvFactsUpTo A x ΔClockAhead ΔClockBehind Δ Δw ΔRedeliver GST release ok W b where
  toEnvFactsBy := E.toEnvFactsBy.restrict fun _ _ _ h => by
    obtain ⟨-, rfl⟩ := deadlineUpTo_eq_some.1 h
    rfl
  caught_up := E.caught_up.restrict fun _ _ _ _ h => by
    obtain ⟨-, -, rfl⟩ := catchUpUpTo_eq_some.1 h
    rfl

/-- The promises up to `b'` give the promises up to every `b ≤ b'`.

The variables:
- `b`, `b'`: the two bounds; `hle`: `b ≤ b'`; `E`: the promises up to `b'`.

Read aloud: a bound on the deadlines can be lowered. -/
theorem EnvFactsUpTo.mono {b b' : ℕ} (hle : b ≤ b') (E : EnvFactsUpTo A x ΔClockAhead ΔClockBehind Δ Δw ΔRedeliver GST release ok W b') :
    EnvFactsUpTo A x ΔClockAhead ΔClockBehind Δ Δw ΔRedeliver GST release ok W b where
  toEnvFactsBy := E.toEnvFactsBy.restrict fun _ _ _ h => by
    obtain ⟨h1, rfl⟩ := deadlineUpTo_eq_some.1 h
    exact deadlineUpTo_eq_some.2 ⟨le_trans h1 (by exact_mod_cast hle), rfl⟩
  caught_up := E.caught_up.restrict fun _ _ _ _ h => by
    obtain ⟨h1, h2, rfl⟩ := catchUpUpTo_eq_some.1 h
    exact catchUpUpTo_eq_some.2
      ⟨le_trans h1 (by exact_mod_cast hle), le_trans h2 (by exact_mod_cast hle), rfl⟩

/-- Before the period `[b₀, b₁)`, the suspended promises are the promises up to `b₀`.

The variables:
- `b₀`, `b₁`: the start and the end of the period; `E`: the promises suspended on it.

Read aloud: a send or a restart due by `b₀` is served as in the synchronous network. -/
theorem EnvFactsOutside.upTo {b₀ b₁ : ℕ} (E : EnvFactsOutside A x ΔClockAhead ΔClockBehind Δ Δw ΔRedeliver GST release ok W b₀ b₁) :
    EnvFactsUpTo A x ΔClockAhead ΔClockBehind Δ Δw ΔRedeliver GST release ok W b₀ where
  toEnvFactsBy := E.toEnvFactsBy.restrict fun _ _ _ h => by
    obtain ⟨h1, rfl⟩ := deadlineUpTo_eq_some.1 h
    rw [deadlineOutsideR_of_le h1]
  caught_up := E.caught_up.restrict fun _ _ _ _ h => by
    obtain ⟨h1, h2, rfl⟩ := catchUpUpTo_eq_some.1 h
    rw [deadlineOutsideR_of_le h1, deadlineOutsideR_of_le h2]

/-- After the period `[b₀, b₁)`, the suspended promises are the synchronous ones from
`max b₁ GST` on: every send is served within `Δ`, and every restart within `Δw`, of the latest of
its time, `b₁` and `GST`. No hypothesis `b₀ ≤ b₁` is needed.

The variables:
- `b₀`, `b₁`: the start and the end of the period; `E`: the promises suspended on it; `htime`: the
  time is monotone in the step.

Read aloud: once the period is over, the network is the synchronous one whose `GST` is `b₁`. -/
theorem EnvFactsOutside.after {b₀ b₁ : ℕ} (E : EnvFactsOutside A x ΔClockAhead ΔClockBehind Δ Δw ΔRedeliver GST release ok W b₀ b₁)
    (htime : Monotone x.time) : EnvFactsSync A x ΔClockAhead ΔClockBehind Δ Δw ΔRedeliver (max b₁ GST) release ok W where
  toEnvFactsBy := E.toEnvFactsBy.of_le fun _ a d' h => ⟨_, rfl, by
      have h' : max a (((max b₁ GST : ℕ)) : ℝ) + Δ = d' := Option.some.inj h
      rw [← h', Nat.cast_max]
      exact deadlineOutsideR_le_after Δ GST b₀ b₁ a⟩
  caught_up := E.caught_up.of_le E.toEnvFactsBy htime fun _ a t c' h => ⟨_, rfl, by
      have h' : max (max a (((max b₁ GST : ℕ)) : ℝ) + Δ) (max t (((max b₁ GST : ℕ)) : ℝ) + Δw) = c' :=
        Option.some.inj h
      rw [← h', Nat.cast_max]
      exact max_le_max (deadlineOutsideR_le_after Δ GST b₀ b₁ a)
        (deadlineOutsideR_le_after Δw GST b₀ b₁ t)⟩

/-- The promises up to `b` give the delivery promise up to `b` alone.

The variables:
- `E`: the promises up to `b`.

Read aloud: the bounded promises keep their delivery promise without the catch-up. -/
theorem EnvFactsUpTo.delivery {b : ℕ} (E : EnvFactsUpTo A x ΔClockAhead ΔClockBehind Δ Δw ΔRedeliver GST release ok W b) :
    EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind Δ ΔRedeliver GST release ok W b :=
  E.toEnvFactsBy

/-- The promises suspended on `[b₀, b₁)` give the delivery promise suspended on it alone.

The variables:
- `E`: the promises suspended on `[b₀, b₁)`.

Read aloud: the suspended promises keep their delivery promise without the catch-up. -/
theorem EnvFactsOutside.delivery {b₀ b₁ : ℕ} (E : EnvFactsOutside A x ΔClockAhead ΔClockBehind Δ Δw ΔRedeliver GST release ok W b₀ b₁) :
    EnvFactsDeliveryOutside A x ΔClockAhead ΔClockBehind Δ ΔRedeliver GST release ok W b₀ b₁ :=
  E.toEnvFactsBy

/-- The synchronous delivery promise gives the delivery promise up to every bound `b`.

The variables:
- `E`: the synchronous delivery promise; `b`: the bound.

Read aloud: the synchronous delivery promise gives every bounded one. -/
theorem EnvFactsDelivery.upTo (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind Δ ΔRedeliver GST release ok W) (b : ℕ) :
    EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind Δ ΔRedeliver GST release ok W b :=
  EnvFactsBy.restrict E fun _ _ _ h => by
    obtain ⟨-, rfl⟩ := deadlineUpTo_eq_some.1 h
    rfl

end Instances

section SyncInstances

variable {V Msg N : Type} [DecidableEq V] {A : Activity V} {x : Trace V Msg N}
  {serves : N → ℕ → Msg → Prop} {ok : Msg → Prop} {release : Msg → Option ℕ} {ΔRedeliver : ℕ} {Δs GST : ℕ}

/-- The sync fact gives the bounded sync fact up to every bound `b`.

The variables:
- `Sy`: the sync fact; `b`: the bound.

Read aloud: the sync fact gives every bounded one. -/
theorem SyncedWithin.upTo (Sy : SyncedWithin A x serves ok release ΔRedeliver Δs GST) (b : ℕ) :
    SyncedWithinUpTo A x serves ok release ΔRedeliver Δs GST b :=
  Sy.restrict (fun _ _ _ _ h => by
    obtain ⟨-, rfl⟩ := deadlineUpTo_eq_some.1 h
    rfl)

/-- The bounded sync fact up to `b'` gives the one up to every `b ≤ b'`.

The variables:
- `b`, `b'`: the two bounds; `hle`: `b ≤ b'`; `Sy`: the sync fact up to `b'`.

Read aloud: a bound on the sync deadlines can be lowered. -/
theorem SyncedWithinUpTo.mono {b b' : ℕ} (hle : b ≤ b')
    (Sy : SyncedWithinUpTo A x serves ok release ΔRedeliver Δs GST b') : SyncedWithinUpTo A x serves ok release ΔRedeliver Δs GST b :=
  Sy.restrict (fun _ _ _ _ h => by
    obtain ⟨h1, rfl⟩ := deadlineUpTo_eq_some.1 h
    exact deadlineUpTo_eq_some.2 ⟨le_trans h1 hle, rfl⟩)

/-- Before the period `[b₀, b₁)`, the suspended sync fact is the sync fact up to `b₀`.

The variables:
- `b₀`, `b₁`: the start and the end of the period; `Sy`: the sync fact suspended on it.

Read aloud: what is due by `b₀` is served as in the synchronous network. -/
theorem SyncedWithinOutside.upTo {b₀ b₁ : ℕ} (Sy : SyncedWithinOutside A x serves ok release ΔRedeliver Δs GST b₀ b₁) :
    SyncedWithinUpTo A x serves ok release ΔRedeliver Δs GST b₀ :=
  Sy.restrict (fun _ _ _ _ h => by
    obtain ⟨h1, rfl⟩ := deadlineUpTo_eq_some.1 h
    rw [deadlineOutside_of_le h1])

end SyncInstances

end GoldilocksCorrectness.Statements.AbstractTrace
