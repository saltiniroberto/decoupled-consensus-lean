module
public import GoldilocksCorrectness.Proofs.Executions.Lemma32
public import GoldilocksCorrectness.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Proofs.Executions.Lemma31UpTo

@[expose] public section

/-!
# `Lemma32.lean` with the delivery premises up to a bound

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma32.lean` that name a delivery
premise, restated with `SynchronyFromWakeUpTo` and `CatchUpOnWakeUpTo` at a bound on the deadlines
. The bound of each twin
is the latest ordinary deadline `max t GST + Δ` of a send its proof reads, written in the twin's
own parameters.

* `lem32_saved_confirmations_compatible_state`

No `axiom`, no `native_decide`, no `sorry`. The landed page is imported, never edited.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff viewFreeze
  dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_succ_le_slotStart one_le_Δ slotStart_eq
  supportCutoff_eq viewFreeze_eq voteTime_eq)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction AtomicHonest Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (expireLocks)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **Lemma 32, the saved confirmations of two honest validators are compatible.** In an
execution synchronous from the support cutoff of slot `s`, the blocks `C₁` and `C₂` that `v₁` and
`v₂` have saved as the confirmation of slot `s` on their states before `t₂ + 1`, `t₂` the support
cutoff of slot `s + 1`, are compatible, when each validator is awake and honest from the duty
window's start of slot `s + 1` to `t₂`.

Why: the wake window makes the tick at `t₂` run the confirmation update of slot `s + 1` (Lemma
15), whose saved confirmation the state before `t₂ + 1` keeps; the window contains Lemma 31's,
since the duty window of slot `s + 1` starts no later than slot `s`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s`: the slot confirmed;
- `v₁`, `v₂`: the two validators; `C₁`, `C₂`: the blocks saved.

Read aloud: if two validators, each awake and honest from the duty window's start of slot `s + 1`
to its support cutoff, have `C₁` and `C₂` saved as their confirmation of slot `s` right after that
cutoff, then `C₁` and `C₂` are on one chain.

Roots name blocks until `supportCutoff S (s + 1)`: Lemma 31, which the proof calls, compares the
frame trees on the states before the support cutoff of slot `s + 1`.

Restated with the delivery premises up to `supportCutoff S s + Δ S`: Lemma 31 reads the re-sends at the support cutoff of slot `s`, due one delay after it (`lem31_saved_confirmations_compatible_upTo`). -/
theorem lem32_saved_confirmations_compatible_state_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s : ℕ) (v₁ v₂ : V) (C₁ C₂ : Block V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S s + Δ S))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S s + Δ S))
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s + 1)))
    -- the network is synchronous from the support cutoff of slot `s` on
    (hGST : GST ≤ supportCutoff S s)
    -- `v₁` is awake and honest from the duty window's start of slot `s + 1` to its support cutoff
    (hw₁ : ∀ t : ℕ, dutyWindowStart S (s + 1) ≤ t → t ≤ supportCutoff S (s + 1) →
      v₁ ∈ Sched.awake (t : Int) ∧ v₁ ∉ Sched.adv (t : Int))
    -- `v₂` likewise
    (hw₂ : ∀ t : ℕ, dutyWindowStart S (s + 1) ≤ t → t ≤ supportCutoff S (s + 1) →
      v₂ ∈ Sched.awake (t : Int) ∧ v₂ ∉ Sched.adv (t : Int))
    -- `v₁`'s state before `t₂ + 1` has `C₁` saved as the confirmation of slot `s`
    (hSaved₁ : (stateBefore x (supportCutoff S (s + 1) + 1) v₁).A.saved_confirmation s = some C₁)
    -- `v₂`'s state before `t₂ + 1` has `C₂` saved as the confirmation of slot `s`
    (hSaved₂ : (stateBefore x (supportCutoff S (s + 1) + 1) v₂).A.saved_confirmation s =
      some C₂) :
    -- then `C₁` and `C₂` are compatible
    C₁.compatible C₂ = true := by
  have hΔ := one_le_Δ S
  have hss : slotStart S (s + 1) = slotStart S s + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hv₁t : voteTime S s = slotStart S s + Δ S := voteTime_eq S s
  have hc : supportCutoff S s = voteTime S s + Δ S := supportCutoff_eq S s
  have hv₃ : voteTime S (s + 1) = slotStart S (s + 1) + Δ S := voteTime_eq S (s + 1)
  have hv₂ : supportCutoff S (s + 1) = voteTime S (s + 1) + Δ S := supportCutoff_eq S (s + 1)
  have hfr : viewFreeze S s = slotStart S s + 3 * Δ S := viewFreeze_eq S s
  have hdw : dutyWindowStart S (s + 1) ≤ slotStart S s := dutyWindowStart_succ_le_slotStart S s
  obtain ⟨A₁', hUpdate₁, hSaved₁'⟩ :=
    update_of_saved_confirmation S Sched x s v₁ C₁ hDiv hMono hw₁ hSaved₁
  obtain ⟨A₂', hUpdate₂, hSaved₂'⟩ :=
    update_of_saved_confirmation S Sched x s v₂ C₂ hDiv hMono hw₂ hSaved₂
  exact lem31_saved_confirmations_compatible_upTo S Sched x
    GST s v₁ v₂ A₁' A₂' C₁ C₂ hDiv hMono hSync hCatch hRoots hGST
    (fun t h1 h2 => hw₁ t (by omega) (by omega)) (fun t h1 h2 => hw₂ t (by omega) (by omega))
    (hw₁ _ (by omega) le_rfl).2 (hw₂ _ (by omega) le_rfl).2 hUpdate₁ hSaved₁' hUpdate₂ hSaved₂'

end GoldilocksCorrectness.Proofs.Executions

