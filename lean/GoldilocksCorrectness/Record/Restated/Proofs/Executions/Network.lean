module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Steps
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.AsyncResilienceDefs
public import GoldilocksCorrectness.Proofs.Executions.Network
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Network, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Network.lean` over a model `M`, for an
execution `x` of `protocolOf M S`: a message an honest validator put on the wire is delivered within
a delay to every validator awake and honest from a time `t₀` through it, when `t₀` is at or before
the send or early enough for the catch-up, under the environment's promises up to a bound
(`EnvFactsUpTo`) or the synchronous ones (`EnvFactsSync`), on a wake-shaped trace. The same from
the synchronous delivery promise alone (`EnvFactsDelivery`, `EnvFactsDeliveryUpTo`) for a validator
active since the message was on the wire (`delivered_before_of_honest_send_sync` and its forms);
and from the sync fact (`SyncedWithin`, `SyncedWithinUpTo`), what an honest active validator serves
at `t₀`, from its last state before `t₀`, reaches every validator active from `t₀` through
`t₀ + Δs` before `t₀ + Δs`, by a delivery at or after a step after which the holder already serves
it (`delivered_before_of_held` and its forms, from the step bound the sync fact promises). None
reads a fact of the model.
`mem_awakeThroughout_iff` and `mem_awakeThroughout_of_forall` name no member and read
no execution; the twins read the landed ones.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open GoldilocksCorrectness.Statements.Routines (Δ)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery EnvFactsDeliveryUpTo SyncedWithin SyncedWithinUpTo)

open GoldilocksCorrectness.Proofs.Executions (mem_awakeThroughout_of_forall)

open GoldilocksCorrectness.Record.Statements.Executions

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks (NamedObject RootOrder)
open Goldilocks.Sts (Setup)

variable {V : Type} [DecidableEq V] [Fintype V]
variable (M : GoldilocksModel V)

variable [RootOrder] {S : Setup V} {A : Activity V} (x : Trace V (NamedObject V) M.N)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy EnvFactsSync EnvFactsUpTo deadlineUpTo
  deadlineUpTo_eq_some catchUpUpTo_eq_some EnvFactsDelivery EnvFactsDeliveryUpTo SyncedWithin
  SyncedWithinUpTo)

/-- A delivery at a time less than `T` comes before `x.stepBefore T`, the step after every step at
a time less than `T`.

The variables:
- `M`: the model;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts, for any deadlines;
- `j`: the step of the delivery; `T`: the time; `v`: the receiver; `sm`: the signed message.

Read aloud: a delivery before time `T` is in every node state read before `T`. -/
theorem deliver_lt_stepBefore_of_time_lt (R : RunFacts M S x)
    {deadline : SignedMsg V (NamedObject V) → ℝ → Option ℝ}
    {ok : NamedObject V → Prop}
    {B : Type} {W : ViewVocab V B (NamedObject V)} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver ok W)
    {j T : ℕ} {v : V} {sm : SignedMsg V (NamedObject V)} (hl : x.lbl j = Event.deliver v sm)
    (hj : x.time j < T) : j < x.stepBefore T := by
  classical
  have hk := R.time_keep j (by rw [hl]; exact nofun)
  have hex := E.time_div T
  have hfa : x.firstAt T = Nat.find hex := by
    unfold Trace.firstAt
    rw [dif_pos hex]
  have hspec := Nat.find_spec hex
  unfold Trace.stepBefore
  rw [hfa]
  by_contra hcon
  have h1 : Nat.find hex ≤ j + 1 := by omega
  have := R.time_mono h1
  linarith

/-! ## The delivery kit: the trace premise as a promise, the bridge, the window from the send -/

/-- The trace premise `SynchronyFromWakeBy`, beside the facts of any instance `E` other than
delivery, is the environment's promises with the deadline the premise reads.

The variables:
- `M`: the model;
- `x`: the execution; `E`: the environment's facts, for their non-delivery fields; `hs`: the trace
  premise at the deadline `deadline`.

Read aloud: the delivery premise read alone, put back beside the other facts, is the
environment's promise. -/
theorem envFactsBy_of_synchronyFromWakeBy {deadline₀ : SignedMsg V (NamedObject V) → ℝ → Option ℝ}
    {ok₀ : NamedObject V → Prop} {B : Type} {W : ViewVocab V B (NamedObject V)}
    {release₀ : NamedObject V → Option ℕ} {ΔRedeliver₀ : ℕ}
    {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline₀ release₀ ΔRedeliver₀ ok₀ W) {deadline : ℝ → ℝ}
    {release : NamedObject V → Option ℕ} {ΔRedeliver : ℕ} {ok : NamedObject V → Prop}
    (hs : x.SynchronyFromWakeBy A deadline release ΔRedeliver ok) :
    EnvFactsBy A x ΔClockAhead ΔClockBehind (fun _ a => some (deadline a)) release ΔRedeliver ok W where
  time_div := E.time_div
  corrupted_mono := E.corrupted_mono
  corrupted_keep := E.corrupted_keep
  ahead_nonneg := E.ahead_nonneg
  behind_nonneg := E.behind_nonneg
  tick_of_active := E.tick_of_active
  tick_active := E.tick_active
  tick_unique := E.tick_unique
  restart_crashed := E.restart_crashed
  restart_time := E.restart_time
  clock_mono := E.clock_mono
  restart_of_awake := E.restart_of_awake
  deliver_active := E.deliver_active
  other_sent := E.other_sent
  delivered := fun i k v sm t d hsend hok hk hik hwin hd hdk hrel => by
    have hd' : deadline (x.time (i + 1)) = d := Option.some.inj hd
    exact hs i k v sm t hsend hok hk hik hwin (by rw [hd']; exact hdk) hrel

/-- The trace premise `SynchronyFromWakeUpTo` up to `b`, beside the facts of any instance `E`
other than delivery, is the environment's promises at the deadlines up to `b`.

The variables:
- `M`: the model;
- `x`: the execution; `E`: the environment's facts, for their non-delivery fields; `hs`: the trace
  premise up to `b`.

Read aloud: the bounded delivery premise, put back beside the other facts, is the bounded
promise. -/
theorem envFactsBy_of_synchronyFromWakeUpTo {deadline₀ : SignedMsg V (NamedObject V) → ℝ → Option ℝ}
    {ok₀ : NamedObject V → Prop} {B : Type} {W : ViewVocab V B (NamedObject V)}
    {release₀ : NamedObject V → Option ℕ} {ΔRedeliver₀ : ℕ}
    {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline₀ release₀ ΔRedeliver₀ ok₀ W) {Δ GST b : ℕ}
    {release : NamedObject V → Option ℕ} {ΔRedeliver : ℕ} {ok : NamedObject V → Prop}
    (hs : SynchronyFromWakeUpTo M A x Δ ΔRedeliver GST release ok b) :
    EnvFactsBy A x ΔClockAhead ΔClockBehind (fun _ a => deadlineUpTo Δ GST b a) release ΔRedeliver ok W where
  time_div := E.time_div
  corrupted_mono := E.corrupted_mono
  corrupted_keep := E.corrupted_keep
  ahead_nonneg := E.ahead_nonneg
  behind_nonneg := E.behind_nonneg
  tick_of_active := E.tick_of_active
  tick_active := E.tick_active
  tick_unique := E.tick_unique
  restart_crashed := E.restart_crashed
  restart_time := E.restart_time
  clock_mono := E.clock_mono
  restart_of_awake := E.restart_of_awake
  deliver_active := E.deliver_active
  other_sent := E.other_sent
  delivered := fun i k v sm t d hsend hok hk hik hwin hd hdk hrel => by
    obtain ⟨hb, rfl⟩ := deadlineUpTo_eq_some.1 hd
    exact hs i k v sm t hsend hok hb hk hik hwin hdk hrel

/-- A validator counted active throughout `[t₀, b]`, with `t₀` at most the time after a send at
step `i`, is active after every step from `i + 1` on whose time is at most `b`.

The variables:
- `M`: the model;
- `x`: the execution; `R`: the run's facts; `i`: the step of the send; `t₀`, `b`: the ends of the
  window; `v`: the validator.

Read aloud: active throughout a window that starts by the send is active from the send on. -/
theorem window_from_send (R : RunFacts M S x) {i t₀ b : ℕ} {v : V}
    (hwin : v ∈ A.activeThroughout x t₀ b) (ht₀ : t₀ ≤ x.time (i + 1)) :
    ∀ j : ℕ, i + 1 ≤ j → x.time j ≤ b → v ∈ A.active j := fun j hj hjb =>
  Activity.mem_active_of_mem_activeThroughout_of_time (fun _ _ h => R.time_mono h) hwin
    (le_trans ht₀ (R.time_mono hj)) hjb

/-! ## From the bounded delivery premises -/

/-- The delay `Δ_F S` is at least `1`.

The variables:
- `S`: the setup.

Read aloud: the attestations' delay is positive. -/
theorem one_le_Δ_F (S : Setup V) : 1 ≤ Δ_F S := by
  have h1 : ((Δ_F S : ℕ) : Int) = S.C.Δ_F := GoldilocksCorrectness.Proofs.Routines.Δ_F_cast S
  have h2 : ((Δ S : ℕ) : Int) = S.C.Δ := GoldilocksCorrectness.Proofs.Routines.Δ_cast S
  have h3 : ((Δ S : ℕ) : Int) ≤ ((Δ_F S : ℕ) : Int) := by
    rw [h1, h2]
    exact S.C.Δ_F_ge
  exact le_trans (GoldilocksCorrectness.Proofs.Routines.one_le_Δ S) (by exact_mod_cast h3)

/-! ## From the synchronous delivery promise alone, and from the sync fact -/

/-- A validator active after the step `k + 1` is active after the step `k` when the step from
the one configuration to the other moves the time: that step is of the kind `other` (a tick, a
restart and a delivery keep the time, `R.time_keep`), so it restarts no one (`E.restart_of_awake`),
and the adversary set only grows (`E.corrupted_mono`).

The variables:
- `M`: the model;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts, for any deadlines;
- `k`: the step; `u`: the validator.

Read aloud: a validator active right after the time moves was already active right before. -/
theorem mem_active_of_mem_active_succ_of_time_lt (R : RunFacts M S x)
    {deadline : SignedMsg V (NamedObject V) → ℝ → Option ℝ} {okE : NamedObject V → Prop}
    {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver okE
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {k : ℕ} {u : V}
    -- the step after `k` moves the time
    (hk : x.time k < x.time (k + 1))
    -- `u` is active after the step `k + 1`
    (hu : u ∈ A.active (k + 1)) :
    u ∈ A.active k := by
  have hother : x.lbl k = Event.other := by
    by_contra h
    have := R.time_keep k h
    linarith
  refine Activity.mem_active.2 ⟨?_, fun hc => Activity.not_mem_corrupted_of_mem_active hu
    (E.corrupted_mono k (k + 1) (Nat.le_succ k) hc)⟩
  by_contra hna
  obtain ⟨t, keep, hl⟩ := E.restart_of_awake k u hna (Activity.mem_awake_of_mem_active hu)
  rw [hother] at hl
  cases hl

/-- A validator active after every step read as `t₀` is active after the last step `k` before
`t₀` (`x.time k < t₀ ≤ x.time (k + 1)`): the step after `k` is read as `t₀`, and it moves the time
(`mem_active_of_mem_active_succ_of_time_lt`). The holder clause of the sync fact
from an activity at the time.

The variables:
- `M`: the model;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts, for any deadlines;
- `t₀`: the time; `k`: the last step before `t₀`; `u`: the validator.

Read aloud: a validator active at `t₀` was active just before `t₀`. -/
theorem mem_active_of_mem_activeAtTime_of_last (R : RunFacts M S x)
    {deadline : SignedMsg V (NamedObject V) → ℝ → Option ℝ} {okE : NamedObject V → Prop}
    {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver okE
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {t₀ k : ℕ} {u : V}
    -- `u` is active after every step read as `t₀`
    (hu : u ∈ A.activeAtTime x t₀)
    -- `k` is the last step before `t₀`
    (hkt : x.time k < t₀) (hkt1 : t₀ ≤ x.time (k + 1)) :
    u ∈ A.active k :=
  Activity.mem_activeAtTime.1 hu k hkt.le hkt1

/-! ## The receiver read up to its own tick (B19-1 (a))

The kit theorems with `hwin : v ∈ A.activeThroughout x t₀ e` read the receiver after every step whose
time is in `[t₀, e]`, also the steps read as `e` after its tick to `e`. The forms below read it after
every step from the first one whose time is `t₀` up to its tick `kR` to `e` only, which is what the
sync fact and the delivery promise ask; a validator of `A.activeThroughoutToTick x a e` with `a < t₀`
is so (`EnvFactsBy.active_of_mem_activeThroughoutToTick`). -/

/-- The sync fact up to a bound `b ≥ t₀ + Δs`, read up to the receiver's own tick `kR` to a clock value
`D ≥ t₀ + Δs`: what `u`,
active after its last step `k` before `t₀ ≥ GST` and at every step whose real time is in
`[t₀, t₀ + Δs]`, serves at its own clock value from its state after `k` is delivered to `w` at a step
before `kR`, at or after a step at a time less than `t₀` after which `u` already serves it at its
clock value then, with `w` active from the delivery up to `kR`; or `w` already serves it after `k`, at
its own clock value.

The variables:
- `M`: the model;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts, for any deadlines; `Δs`: the
  sync delay; `GST`: the time from which the network is synchronous; `ok`: the class of objects the
  sync fact is about; `serves`: the selection; `b`: the bound; `Sy`: the sync fact up to `b`;
- `t₀`: the time; `k`: the last step at a time less than `t₀`; `u`: the holder; `w`: the receiver;
  `o`: the object; `D`: the clock value of `w`'s tick `kR`.

Read aloud: a receiver active from `t₀` up to its tick to a clock value at least the sync deadline
gets, before that tick, what an honest holder online for `Δs` after `t₀` serves at `t₀`, or already
has it; when a re-delivery after its clock reaches the object's release clock value would come before
that tick, the delivery found its clock there. -/
theorem delivered_before_of_held_upTo_tick (R : RunFacts M S x)
    {deadline : SignedMsg V (NamedObject V) → ℝ → Option ℝ}
    {okE : NamedObject V → Prop}
    {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver okE
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {Δs GST : ℕ} {ok : NamedObject V → Prop}
    {serves : M.N → ℕ → NamedObject V → Prop} {t₀ b : ℕ}
    (Sy : SyncedWithinUpTo A x serves ok release ΔRedeliver Δs GST b) (hb : t₀ + Δs ≤ b)
    {k : ℕ} {u w : V} {o : NamedObject V}
    -- `u` is awake and outside the adversary set in the configuration after `k`
    (hu : u ∈ A.active k)
    -- `k` is `u`'s last step before `t₀`
    (hkt : x.time k < t₀) (hkt1 : t₀ ≤ x.time (k + 1))
    -- `u` serves `o` from that state, at its own clock value there
    (ho : serves (x.st k u) (x.clockValue k u) o) (hok : ok o)
    -- `u` is active at every step whose real time is in `[t₀, t₀ + Δs]`
    (hhold : ∀ i : ℕ, (t₀ : ℝ) ≤ x.time i → x.time i ≤ t₀ + Δs → u ∈ A.active i)
    -- the network is synchronous from `t₀` on
    (hGST : GST ≤ t₀)
    -- `w` ticks to `D ≥ t₀ + Δs` at `kR`, and is active from the first step read as `t₀` up to `kR`
    {D kR : ℕ} (hD : t₀ + Δs ≤ D) (hkR : x.lbl kR = Event.tick w D)
    (hwR : ∀ i : ℕ, t₀ ≤ x.time i → i ≤ kR → w ∈ A.active i)
    -- the re-delivery premise of the sync fact at `kR`
    (hprem : ∀ (r j₀ k₁ t₁ : ℕ), release o = some r →
      x.lbl j₀ = Event.deliver w ⟨u, o⟩ → ¬ x.ReactedAtLeast j₀ w r →
      j₀ < k₁ → k₁ ≤ kR → x.lbl k₁ = Event.tick w t₁ → r ≤ t₁ →
      (∀ (l t' : ℕ), j₀ < l → l < k₁ → x.lbl l = Event.tick w t' → t' < r) →
      x.time (k₁ + 1) + ΔRedeliver ≤ x.time kR) :
    serves (x.st k w) (x.clockValue k w) o ∨
    ∃ j k', k' ≤ j ∧ x.time k' < t₀ ∧ serves (x.st k' u) (x.clockValue k' u) o ∧
      x.lbl j = Event.deliver w ⟨u, o⟩ ∧ j < kR ∧
      (∀ r : ℕ, release o = some r → r ≤ D → x.ReactedAtLeast j w r) ∧
      (∀ l : ℕ, j ≤ l → l ≤ kR → w ∈ A.active l) := by
  have hd : deadlineUpTo Δs GST b t₀ = some (t₀ + Δs) :=
    deadlineUpTo_eq_some.2 ⟨by omega, by omega⟩
  exact Sy (t₀ : ℝ) k u w o (t₀ + Δs) D kR hkt hkt1 hu ho hok
    (by rw [Nat.ceil_natCast]; exact_mod_cast hhold) (by rw [Nat.ceil_natCast]; exact hd) hkR hD hwR hprem

/-- The delivery promise up to `t + Δ`, read up to the receiver's own tick `kR` to a clock value `D`
with `t + Δ + ΔClockAhead ≤ D`: a message of the class `ok` an honest validator put on the wire at
the step `i`, at a time at most `t ≥ GST`, is delivered to `v` at a step after `i` and before `kR`,
when `v` is active after every step from the first one whose time is `t₀ ≤ x.time (i + 1)` up to
`kR`. The tick `kR` is at a real time at least `D − ΔClockAhead ≥ t + Δ` (`tick_active`), at least the
message's deadline.

The variables:
- `M`: the model;
- `x`: the execution; `R`: the run's facts; `Δ`: the delay, at least `1`; `GST`: the time from which the network is
  synchronous; `ok`: the class of messages; `E`: the delivery promise up to `t + Δ`;
- `i`: the step of the send; `t₀`: the receiver's window start; `v`: the receiver; `sm`: the signed
  message; `D`: the clock value of `v`'s tick `kR`.

Read aloud: a receiver active from the send up to its tick to a clock value at least
`t + Δ + ΔClockAhead` is delivered the message before that tick. -/
theorem delivered_before_of_honest_send_sync_upTo_tick (R : RunFacts M S x) {Δ GST : ℕ}
    {ok : NamedObject V → Prop} (hΔ : 1 ≤ Δ) {t : ℕ}
    {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind Δ ΔRedeliver GST release ok
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (t + Δ))
    {i t₀ : ℕ} {v : V} {sm : SignedMsg V (NamedObject V)}
    (hsend : x.HonestSendAt A i sm)
    -- the object of `sm` is in the class `ok`
    (hok : ok sm.msg)
    -- the message is on the wire at or before `t`
    (hit : x.time (i + 1) ≤ t)
    -- the network is synchronous from `t` on
    (hGST : GST ≤ t)
    -- `v` ticks to `D` at `kR`, with `t + Δ + ΔClockAhead ≤ D`, and is active from the first step read
    -- as `t₀` up to `kR`
    {D kR : ℕ} (hD : (t : ℝ) + Δ + ΔClockAhead ≤ D) (hkR : x.lbl kR = Event.tick v D)
    (hwR : ∀ l : ℕ, t₀ ≤ x.time l → l ≤ kR → v ∈ A.active l)
    -- `v` has been active since the message was on the wire
    (ht₀ : t₀ ≤ x.time (i + 1)) :
    ∃ j, i < j ∧ x.lbl j = Event.deliver v sm ∧ j < kR := by
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  have hitr : x.time (i + 1) ≤ (t : ℝ) := hit
  have hGSTr : (GST : ℝ) ≤ t := by exact_mod_cast hGST
  have hdD : max (x.time (i + 1)) (GST : ℝ) + Δ ≤ ((t + Δ : ℕ) : ℝ) := by
    have := max_le hitr hGSTr
    push_cast
    linarith
  -- the tick `kR` is at a real time at least `D − ΔClockAhead ≥ t + Δ`
  have hkRt := (E.tick_active kR v D hkR).2.1
  have hdk : max (x.time (i + 1)) (GST : ℝ) + Δ ≤ x.time kR := by
    push_cast at hdD
    linarith
  have hikR : i < kR := by
    by_contra hc
    have h1 := htime (show kR ≤ i + 1 by omega)
    have hΔr : (1 : ℝ) ≤ Δ := by exact_mod_cast hΔ
    have := le_max_left (x.time (i + 1)) (GST : ℝ)
    linarith
  have hwin : ∀ l : ℕ, i + 1 ≤ l → l ≤ kR → v ∈ A.active l := fun l h1 h2 =>
    hwR l (le_trans ht₀ (htime h1)) h2
  by_cases hdel : ∃ j₀ : ℕ, i < j₀ ∧ j₀ < kR ∧ x.lbl j₀ = Event.deliver v sm
  · obtain ⟨j₀, h1, h2, h3⟩ := hdel
    exact ⟨j₀, h1, h3, h2⟩
  · obtain ⟨j, hij, hjk, hl, -, -⟩ := E.delivered i kR v sm D
      (max (x.time (i + 1)) GST + Δ) hsend hok hkR hikR hwin
      (deadlineUpTo_eq_some.2 ⟨hdD, rfl⟩) hdk
      (fun _ j₀ _ _ _ hij₀ hl₀ _ hj₀k₁ hk₁k _ _ _ => absurd ⟨j₀, hij₀, by omega, hl₀⟩ hdel)
    exact ⟨j, hij, hl, hjk⟩

/-- A validator of `A.activeThroughoutToTick x a e`, with `a + ΔClockBehind < t₀` for a real time
`t₀` and an integer opening value `a`, ticks to `e` at a step `kR` and is active after every step from
the first one whose time is `t₀` up to `kR`: in the reader's first case it is active after every step
up to `kR`; in the second, its tick to a value `c ≤ a` is at a real time at most
`c + ΔClockBehind ≤ a + ΔClockBehind < t₀` (`tick_active`), before every step whose time is `t₀`.

The variables:
- `M`: the model;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `v`: the validator; `a`:
  the clock value that opens its window; `t₀`: the later start, a real time; `e`: the window's end.

Read aloud: a validator active from a window opening more than `ΔClockBehind` before `t₀` up to its
tick to `e` is active from `t₀` up to that tick. -/
theorem tick_window_of_activeThroughoutToTick_int (R : RunFacts M S x)
    {deadline : SignedMsg V (NamedObject V) → ℝ → Option ℝ} {ok : NamedObject V → Prop}
    {B : Type} {W : ViewVocab V B (NamedObject V)} {release ΔRedeliver}
    {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver ok W)
    {v : V} {a : ℤ} {e : ℕ} {t₀ : ℝ} (hv : v ∈ A.activeThroughoutToTick x a e)
    (haB : (a : ℝ) + ΔClockBehind < t₀) :
    ∃ kR : ℕ, x.lbl kR = Event.tick v e ∧ ∀ i : ℕ, t₀ ≤ x.time i → i ≤ kR → v ∈ A.active i := by
  obtain ⟨kR, hkR, h1 | ⟨k, -, c, hca, hk, h2⟩⟩ := Activity.mem_activeThroughoutToTick.1 hv
  · -- active after every step up to its tick to `e`
    exact ⟨kR, hkR, fun i _ hik => h1 i hik⟩
  · -- the window from the tick to `c ≤ a`, at a real time at most `c + ΔClockBehind < t₀`
    refine ⟨kR, hkR, fun i hi hik => h2 i ?_ hik⟩
    by_contra hki
    have hle : x.time i ≤ x.time k := R.time_mono (by omega)
    have hkb := (E.tick_active k v c hk).2.2
    have hca' : (c : ℝ) ≤ (a : ℝ) := by exact_mod_cast hca
    linarith

/-- `tick_window_of_activeThroughoutToTick_int` at a natural opening value `a`.

The variables:
- `M`: the model;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `v`: the validator; `a`:
  the clock value that opens its window; `t₀`: the later start, a real time; `e`: the window's end.

Read aloud: a validator active from a window opening more than `ΔClockBehind` before `t₀` up to its
tick to `e` is active from `t₀` up to that tick. -/
theorem tick_window_of_activeThroughoutToTick (R : RunFacts M S x)
    {deadline : SignedMsg V (NamedObject V) → ℝ → Option ℝ} {ok : NamedObject V → Prop}
    {B : Type} {W : ViewVocab V B (NamedObject V)} {release ΔRedeliver}
    {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver ok W)
    {v : V} {a e : ℕ} {t₀ : ℝ} (hv : v ∈ A.activeThroughoutToTick x (a : ℤ) e)
    (haB : (a : ℝ) + ΔClockBehind < t₀) :
    ∃ kR : ℕ, x.lbl kR = Event.tick v e ∧ ∀ i : ℕ, t₀ ≤ x.time i → i ≤ kR → v ∈ A.active i :=
  tick_window_of_activeThroughoutToTick_int M x R E hv (by push_cast; exact haB)

/--

The variables:
- `a`: the real number bounded; `c`: the time; `m ≤ n`: the two multiples; `d`: the sync delay.

Read aloud: a start earlier than `c − max n d` is earlier than `c − max m d`. -/
theorem lt_natSub_max_of_le {a : ℝ} {c m n d : ℕ} (hmn : m ≤ n) (h : a < ((c - max n d : ℕ) : ℝ)) :
    a < ((c - max m d : ℕ) : ℝ) :=
  lt_of_lt_of_le h (by exact_mod_cast Nat.sub_le_sub_left (max_le_max hmn le_rfl) c)

/--

The variables:
- `E`: the environment's facts; `a`: the window's start; `t₀`: a real time.

Read aloud: a start more than both clock bounds before `t₀` is more than the clock-behind bound
before it. -/
theorem behind_lt_of_ahead_behind_lt
    {deadline : SignedMsg V (NamedObject V) → ℝ → Option ℝ} {ok : NamedObject V → Prop}
    {B : Type} {W : ViewVocab V B (NamedObject V)} {release ΔRedeliver}
    {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver ok W)
    {a : ℕ} {t₀ : ℝ} (h : (a : ℝ) + ΔClockAhead + ΔClockBehind < t₀) :
    (a : ℝ) + ΔClockBehind < t₀ := by
  linarith [E.ahead_nonneg]

/-- `behind_lt_of_ahead_behind_lt` at an integer start `a`.

The variables:
- `E`: the environment's facts; `a`: the window's start; `t₀`: a real time.

Read aloud: a start more than both clock bounds before `t₀` is more than the clock-behind bound
before it. -/
theorem behind_lt_of_ahead_behind_lt_int
    {deadline : SignedMsg V (NamedObject V) → ℝ → Option ℝ} {ok : NamedObject V → Prop}
    {B : Type} {W : ViewVocab V B (NamedObject V)} {release ΔRedeliver}
    {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver ok W)
    {a : ℤ} {t₀ : ℝ} (h : (a : ℝ) + ΔClockAhead + ΔClockBehind < t₀) :
    (a : ℝ) + ΔClockBehind < t₀ := by
  linarith [E.ahead_nonneg]

/--

The variables:
- `M`: the model;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `v`: the validator; `a`:
  the start of its window; `e`: the window's end; `c`, `m`: the two clock values whose difference is
  the later start.

Read aloud: a validator active from a start more than both clock bounds before `c − m` up to its tick
to `e` is active from `c − m` up to that tick. -/
theorem tick_window_sub_of_activeThroughoutToTick (R : RunFacts M S x)
    {deadline : SignedMsg V (NamedObject V) → ℝ → Option ℝ} {ok : NamedObject V → Prop}
    {B : Type} {W : ViewVocab V B (NamedObject V)} {release ΔRedeliver}
    {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver ok W)
    {v : V} {a e c m : ℕ} (hmc : m ≤ c) (hv : v ∈ A.activeThroughoutToTick x (a : ℤ) e)
    (h : (a : ℝ) + ΔClockAhead + ΔClockBehind < ((c - m : ℕ) : ℝ)) :
    ∃ kR : ℕ, x.lbl kR = Event.tick v e ∧
      ∀ i : ℕ, (c : ℝ) - (m : ℝ) ≤ x.time i → i ≤ kR → v ∈ A.active i := by
  have hc : ((c - m : ℕ) : ℝ) = (c : ℝ) - (m : ℝ) := Nat.cast_sub hmc
  exact tick_window_of_activeThroughoutToTick M x R E hv (by
    rw [← hc]; exact behind_lt_of_ahead_behind_lt M x E h)

/-- `tick_window_sub_of_activeThroughoutToTick` at an integer start `a`.

The variables:
- `M`: the model;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `v`: the validator; `a`:
  the start of its window; `e`: the window's end; `c`, `m`: the two clock values whose difference is
  the later start.

Read aloud: a validator active from a start more than both clock bounds before `c − m` up to its tick
to `e` is active from `c − m` up to that tick. -/
theorem tick_window_sub_of_activeThroughoutToTick_int (R : RunFacts M S x)
    {deadline : SignedMsg V (NamedObject V) → ℝ → Option ℝ} {ok : NamedObject V → Prop}
    {B : Type} {W : ViewVocab V B (NamedObject V)} {release ΔRedeliver}
    {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver ok W)
    {v : V} {a : ℤ} {e c m : ℕ} (hmc : m ≤ c) (hv : v ∈ A.activeThroughoutToTick x a e)
    (h : (a : ℝ) + ΔClockAhead + ΔClockBehind < ((c - m : ℕ) : ℝ)) :
    ∃ kR : ℕ, x.lbl kR = Event.tick v e ∧
      ∀ i : ℕ, (c : ℝ) - (m : ℝ) ≤ x.time i → i ≤ kR → v ∈ A.active i := by
  have hc : ((c - m : ℕ) : ℝ) = (c : ℝ) - (m : ℝ) := Nat.cast_sub hmc
  exact tick_window_of_activeThroughoutToTick_int M x R E hv (by
    rw [← hc]; exact behind_lt_of_ahead_behind_lt_int M x E h)

/-- `tick_window_of_activeThroughoutToTick` on the send-at-a-tick route: a
validator of `A.activeThroughoutToTick x a e`, with `a + ΔClockAhead + ΔClockBehind < c` for the clock
value `c` of the sender's tick, ticks to `e` at a step `kR` and is active after every step from the
first one whose time is `c − ΔClockAhead`, the earliest real time of a tick to `c`, up to `kR`.

The variables:
- `M`: the model;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `v`: the validator; `a`:
  the start of its window; `e`: the window's end; `c`: the clock value of the sender's tick.

Read aloud: a validator active from a start more than both clock bounds before `c` up to its tick
to `e` is active from the earliest real time of a tick to `c` up to that tick. -/
theorem tick_window_ahead_of_activeThroughoutToTick (R : RunFacts M S x)
    {deadline : SignedMsg V (NamedObject V) → ℝ → Option ℝ} {ok : NamedObject V → Prop}
    {B : Type} {W : ViewVocab V B (NamedObject V)} {release ΔRedeliver}
    {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver ok W)
    {v : V} {a e c : ℕ} (hv : v ∈ A.activeThroughoutToTick x (a : ℤ) e)
    (h : (a : ℝ) + ΔClockAhead + ΔClockBehind < c) :
    ∃ kR : ℕ, x.lbl kR = Event.tick v e ∧
      ∀ i : ℕ, (c : ℝ) - ΔClockAhead ≤ x.time i → i ≤ kR → v ∈ A.active i :=
  tick_window_of_activeThroughoutToTick M x R E hv (by linarith)

/-- `tick_window_ahead_of_activeThroughoutToTick` at an integer start `a`.

The variables:
- `M`: the model;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `v`: the validator; `a`:
  the start of its window; `e`: the window's end; `c`: the clock value of the sender's tick.

Read aloud: a validator active from a start more than both clock bounds before `c` up to its tick
to `e` is active from the earliest real time of a tick to `c` up to that tick. -/
theorem tick_window_ahead_of_activeThroughoutToTick_int (R : RunFacts M S x)
    {deadline : SignedMsg V (NamedObject V) → ℝ → Option ℝ} {ok : NamedObject V → Prop}
    {B : Type} {W : ViewVocab V B (NamedObject V)} {release ΔRedeliver}
    {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver ok W)
    {v : V} {a : ℤ} {e c : ℕ} (hv : v ∈ A.activeThroughoutToTick x a e)
    (h : (a : ℝ) + ΔClockAhead + ΔClockBehind < c) :
    ∃ kR : ℕ, x.lbl kR = Event.tick v e ∧
      ∀ i : ℕ, (c : ℝ) - ΔClockAhead ≤ x.time i → i ≤ kR → v ∈ A.active i :=
  tick_window_of_activeThroughoutToTick_int M x R E hv (by linarith)

/-- **Kit lemma, the end of a window moved to an earlier tick (T-K4).** A validator of
`A.activeThroughoutToTick x a b` is in `A.activeThroughoutToTick x a b'` for every clock value
`b' ≥ 1` whose tick window `[b' − ΔClockAhead, b' + ΔClockBehind]` lies after the window's start by
more than both clock bounds (`a + ΔClockAhead + ΔClockBehind < b'`) and wholly before the earliest
real time of a tick to `b` (`b' + ΔClockBehind < b − ΔClockAhead`): the validator is active at every
step of that tick window, so it ticks to `b'` there (`tick_of_active`), before its tick to `b`.

The variables:
- `M`: the model;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `v`: the validator; `a`:
  the window's start; `b`: its end; `b'`: the earlier end.

Read aloud: a validator active from `a` up to its tick to `b` is active from `a` up to its tick to
any clock value `b'` whose tick window is between the two. -/
theorem mem_activeThroughoutToTick_of_le_end (R : RunFacts M S x)
    {deadline : SignedMsg V (NamedObject V) → ℝ → Option ℝ} {ok : NamedObject V → Prop}
    {B : Type} {W : ViewVocab V B (NamedObject V)} {release ΔRedeliver}
    {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver ok W)
    {v : V} {a b b' : ℕ} (hb' : 1 ≤ b')
    (hab : (a : ℝ) + ΔClockAhead + ΔClockBehind < b')
    (hbb : (b' : ℝ) + ΔClockBehind < (b : ℝ) - ΔClockAhead)
    (hv : v ∈ A.activeThroughoutToTick x (a : ℤ) b) :
    v ∈ A.activeThroughoutToTick x (a : ℤ) b' := by
  have hA := E.ahead_nonneg
  have hB := E.behind_nonneg
  obtain ⟨k', hk', hcase⟩ := Activity.mem_activeThroughoutToTick.1 hv
  have htk' := (E.tick_active k' v b hk').2.1
  -- every step at a time at most `b' + ΔClockBehind` is before `k'`
  have hlt : ∀ i : ℕ, x.time i ≤ b' + ΔClockBehind → i < k' := by
    intro i hi
    by_contra h
    have := R.time_mono (not_lt.mp h)
    linarith
  -- `v` is active at every step of the tick window of `b'`
  have hact : ∀ i : ℕ, (b' : ℝ) - ΔClockAhead ≤ x.time i → x.time i ≤ b' + ΔClockBehind →
      v ∈ A.active i := by
    intro i h1 h2
    have hik := hlt i h2
    rcases hcase with h | ⟨k, -, c, hca, hk, h⟩
    · exact h i hik.le
    · refine h i ?_ hik.le
      by_contra hc
      have h3 := R.time_mono (not_le.mp hc).le
      have h4 := (E.tick_active k v c hk).2.2
      have hca' : (c : ℝ) ≤ (a : ℝ) := by exact_mod_cast hca
      linarith
  obtain ⟨k'', hk'', -, h2⟩ := E.tick_of_active b' hb' v hact
  have hk''k' := hlt k'' h2
  refine Activity.mem_activeThroughoutToTick.2 ⟨k'', hk'', ?_⟩
  rcases hcase with h | ⟨k, hkk, c, hca, hk, h⟩
  · exact Or.inl fun i hi => h i (le_trans hi hk''k'.le)
  · -- the tick to `c ≤ a` is at a real time at most `a + ΔClockBehind`, before the tick to `b'`
    have hkk'' : k ≤ k'' := by
      by_contra hc
      have h3 := R.time_mono (not_le.mp hc).le
      have h4 := (E.tick_active k v c hk).2.2
      have hca' : (c : ℝ) ≤ (a : ℝ) := by exact_mod_cast hca
      have h5 := (E.tick_active k'' v b' hk'').2.1
      linarith
    exact Or.inr ⟨k, hkk'', c, hca, hk, fun i hki hik => h i hki (le_trans hik hk''k'.le)⟩

/-- **Kit lemma, the end of a window moved to an earlier tick, from an integer start.** As
`mem_activeThroughoutToTick_of_le_end`, for a window start `a` that is an integer (a protocol time such as
`duty_window_start S.C s`, which may be negative): a validator of `A.activeThroughoutToTick x a b` is in
`A.activeThroughoutToTick x a b'` for every clock value `b' ≥ 1` whose tick window lies after `a` by more than both
clock bounds and wholly before the earliest real time of a tick to `b`.

The variables:
- `M`: the model;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `v`: the validator; `a`: the window's
  start; `b`: its end; `b'`: the earlier end.

Read aloud: a validator active from `a` up to its tick to `b` is active from `a` up to its tick to any clock value
`b'` whose tick window is between the two. -/
theorem mem_activeThroughoutToTick_of_le_end_int (R : RunFacts M S x)
    {deadline : SignedMsg V (NamedObject V) → ℝ → Option ℝ} {ok : NamedObject V → Prop}
    {B : Type} {W : ViewVocab V B (NamedObject V)} {release ΔRedeliver}
    {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver ok W)
    {v : V} {a : ℤ} {b b' : ℕ} (hb' : 1 ≤ b')
    (hab : (a : ℝ) + ΔClockAhead + ΔClockBehind < b')
    (hbb : (b' : ℝ) + ΔClockBehind < (b : ℝ) - ΔClockAhead)
    (hv : v ∈ A.activeThroughoutToTick x a b) :
    v ∈ A.activeThroughoutToTick x a b' := by
  have hA := E.ahead_nonneg
  have hB := E.behind_nonneg
  obtain ⟨k', hk', hcase⟩ := Activity.mem_activeThroughoutToTick.1 hv
  have htk' := (E.tick_active k' v b hk').2.1
  have hlt : ∀ i : ℕ, x.time i ≤ b' + ΔClockBehind → i < k' := by
    intro i hi
    by_contra h
    have := R.time_mono (not_lt.mp h)
    linarith
  have hact : ∀ i : ℕ, (b' : ℝ) - ΔClockAhead ≤ x.time i → x.time i ≤ b' + ΔClockBehind →
      v ∈ A.active i := by
    intro i h1 h2
    have hik := hlt i h2
    rcases hcase with h | ⟨k, -, c, hca, hk, h⟩
    · exact h i hik.le
    · refine h i ?_ hik.le
      by_contra hc
      have h3 := R.time_mono (not_le.mp hc).le
      have h4 := (E.tick_active k v c hk).2.2
      have hca' : ((c : ℤ) : ℝ) ≤ (a : ℝ) := by exact_mod_cast hca
      push_cast at hca'
      linarith
  obtain ⟨k'', hk'', -, h2⟩ := E.tick_of_active b' hb' v hact
  have hk''k' := hlt k'' h2
  refine Activity.mem_activeThroughoutToTick.2 ⟨k'', hk'', ?_⟩
  rcases hcase with h | ⟨k, hkk, c, hca, hk, h⟩
  · exact Or.inl fun i hi => h i (le_trans hi hk''k'.le)
  · have hkk'' : k ≤ k'' := by
      by_contra hc
      have h3 := R.time_mono (not_le.mp hc).le
      have h4 := (E.tick_active k v c hk).2.2
      have hca' : ((c : ℤ) : ℝ) ≤ (a : ℝ) := by exact_mod_cast hca
      push_cast at hca'
      have h5 := (E.tick_active k'' v b' hk'').2.1
      linarith
    exact Or.inr ⟨k, hkk'', c, hca, hk, fun i hki hik => h i hki (le_trans hik hk''k'.le)⟩

end GoldilocksCorrectness.Record.Proofs.Executions
