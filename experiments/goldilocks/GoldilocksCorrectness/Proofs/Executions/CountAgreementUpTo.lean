module
public import GoldilocksCorrectness.Proofs.Executions.CountAgreement
public import GoldilocksCorrectness.Proofs.Executions.AsyncDelivery

@[expose] public section

/-!
# `CountAgreement.lean` with the delivery premises up to a bound

The theorems of `GoldilocksCorrectness/Proofs/Executions/CountAgreement.lean` that name a delivery
premise, restated with `SynchronyFromWakeUpTo` and `CatchUpOnWakeUpTo` at a bound on the deadlines
. The bound of each twin
is the latest ordinary deadline `max t GST + Δ` of a send its proof reads, written in the twin's
own parameters.

* `pool_vote_reaches_proposer`

No `axiom`, no `native_decide`, no `sorry`. The landed page is imported, never edited.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime viewFreeze)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_eq viewFreeze_eq voteTime_eq)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicAction AtomicExec Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- A Goldfish vote of slot `s` that a validator `w` holds before the view freeze of slot `s` is in
the pool of slot `s` of every validator `p` awake and honest from the view freeze of slot `s` to the
start of slot `s + 1`, before that start; or `p` then holds two distinct votes of the vote's validator
for slot `s`. The network is synchronous from the vote time of slot `s` on.

Why: the pool-to-pool relay at the view freeze (`pool_vote_reaches_before_add_delay`): `w`
re-sent the vote at a time less than the view freeze, and that re-send reaches `p` before the view
freeze plus one delay, the start of slot `s + 1`.



The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s`: the slot of the vote; `p`: the receiver; `w`: the holder;
  `vote`: the vote.

Read aloud: a vote the next slot's voter holds before the view freeze reached the next slot's
proposer before its proposal, unless the proposer already holds two votes of its validator.

Restated with the delivery premises up to `b`, at least `slotStart S (s + 1)`: the relayed vote's delivery to `p` is due by then. -/
theorem pool_vote_reaches_proposer_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption) (GST : ℕ) {b : ℕ}
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject b)
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject b)
    (s : ℕ) (p w : V) (vote : GoldfishVote V)
    -- the network is synchronous from the vote time of slot `s` on
    (hGST : GST ≤ voteTime S s)
    -- `p` is awake and honest from the view freeze of slot `s` to the start of slot `s + 1`
    (hp : ∀ t : ℕ, viewFreeze S s ≤ t → t ≤ slotStart S (s + 1) →
      p ∈ Sched.awake (t : Int) ∧ p ∉ Sched.adv (t : Int))
    -- `w` holds `vote` in its pool of slot `s` before the view freeze of slot `s`
    (hvote : vote ∈ (stateBefore x (viewFreeze S s) w).A.pool s)
    -- the latest deadline the proof reads is at most the bound
    (hb : slotStart S (s + 1) ≤ b) :
    vote ∈ (stateBefore x (slotStart S (s + 1)) p).A.pool s ∨
      ∃ v₁ ∈ (stateBefore x (slotStart S (s + 1)) p).A.pool s,
        ∃ v₂ ∈ (stateBefore x (slotStart S (s + 1)) p).A.pool s,
          v₁ ≠ v₂ ∧ v₁.val_index = vote.val_index ∧ v₂.val_index = vote.val_index := by
  -- the times
  have hΔ := one_le_Δ S
  have hfz : viewFreeze S s = slotStart S s + 3 * Δ S := viewFreeze_eq S s
  have hss : slotStart S (s + 1) = slotStart S s + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hss2 : slotStart S (s + 2) = slotStart S s + 8 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add]
    omega
  have hv₀ : voteTime S s = slotStart S s + Δ S := voteTime_eq S s
  -- the relay at the view freeze, whose delay ends at the start of slot `s + 1`
  have hres := pool_vote_reaches_before_add_delay_upTo S Sched x hDiv hMono GST hSync hCatch
    (viewFreeze S s) s w p vote (by omega) (by omega) (fun t' h1 h2 => hp t' h1 (by omega)) hvote (by omega)
  have hfzΔ : viewFreeze S s + Δ S = slotStart S (s + 1) := by omega
  rw [hfzΔ] at hres
  exact hres

end GoldilocksCorrectness.Proofs.Executions

