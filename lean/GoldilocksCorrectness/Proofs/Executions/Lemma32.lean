module
public import GoldilocksCorrectness.Statements.Routines.TickStatements
public import GoldilocksCorrectness.Statements.Executions.WakeStatements
public import GoldilocksCorrectness.Proofs.Executions.Lemma31
public import GoldilocksCorrectness.Proofs.Executions.ConfirmationSteps

@[expose] public section

/-!
# Lemma 32: the saved confirmations of two honest validators are compatible

The proof of `lem32_saved_confirmations_compatible_state`, stated in
`GoldilocksCorrectness/Statements/Executions/ConfirmationCompatibilityStatements.lean`: for each
validator, the tick at the support cutoff `t₂` of slot `s + 1` runs the confirmation update
(Lemma 15), whose saved confirmation the state before `t₂ + 1` keeps; then Lemma 31.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff viewFreeze
  dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_succ_le_slotStart one_le_Δ slotStart_eq
  slot_eq_of_mem supportCutoff_cast supportCutoff_eq viewFreeze_eq voteTime_eq)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction AtomicHonest Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (expireLocks)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- A block saved as the confirmation of slot `s` on a validator's state before `t₂ + 1`, `t₂` the
support cutoff of slot `s + 1`, is saved by the confirmation update of slot `s + 1` on its state
before `t₂`, its expired lock entries removed, when the validator is awake and honest from the
duty window's start of slot `s + 1` to `t₂`. -/
theorem update_of_saved_confirmation (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s : ℕ) (v : V) (C : Block V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hw : ∀ t : ℕ, dutyWindowStart S (s + 1) ≤ t → t ≤ supportCutoff S (s + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    (hSaved : (stateBefore x (supportCutoff S (s + 1) + 1) v).A.saved_confirmation s = some C) :
    ∃ A' : ACState V, update_confirmation S.C S.P
        (expireLocks (stateBefore x (supportCutoff S (s + 1)) v).A
          ((supportCutoff S (s + 1) : ℕ) : Int))
        (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S)
        ((supportCutoff S (s + 1) : ℕ) : Int) (s + 1) = .ok A' ∧
      A'.saved_confirmation s = some C := by
  -- the times
  have hΔ := one_le_Δ S
  have hss : slotStart S (s + 1) = slotStart S s + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hss' : slotStart S (s + 1 + 1) = slotStart S (s + 1) + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq S (s + 1), Nat.mul_add, Nat.mul_one]
  have hv₃ : voteTime S (s + 1) = slotStart S (s + 1) + Δ S := voteTime_eq S (s + 1)
  have hv₂ : supportCutoff S (s + 1) = voteTime S (s + 1) + Δ S := supportCutoff_eq S (s + 1)
  have hdw : dutyWindowStart S (s + 1) ≤ slotStart S s := dutyWindowStart_succ_le_slotStart S s
  have hslot₂ : S.C.slot ((supportCutoff S (s + 1) : ℕ) : Int) = s + 1 :=
    slot_eq_of_mem S (by omega) (by omega)
  -- the tick at `t₂` runs the confirmation update
  obtain ⟨hl₂, -, hti₂'⟩ := stepBefore_spec x hDiv (by omega : 1 ≤ supportCutoff S (s + 1))
  have hv₂a := hw (supportCutoff S (s + 1)) (by omega) le_rfl
  obtain ⟨n₂, sent₂, hrun₂, hst₂⟩ := tick_step_outcome x hl₂ hv₂a.1 hv₂a.2
  have hAw₂ := awakeSince_le_dutyWindowStart_b S Sched x (s + 1) (supportCutoff S (s + 1)) v hDiv
    hMono (by omega) (fun t h1 h2 => (hw t h1 h2).1) hv₂a.2
  have hA₂ : (tickInputState x (stepBefore x (supportCutoff S (s + 1))) (supportCutoff S (s + 1))
      v).A = (stateBefore x (supportCutoff S (s + 1)) v).A := (tickInputState_frame x _ _ v).2.1
  have hS₂ : (tickInputState x (stepBefore x (supportCutoff S (s + 1))) (supportCutoff S (s + 1))
      v).S = (stateBefore x (supportCutoff S (s + 1)) v).S := (tickInputState_frame x _ _ v).1
  obtain ⟨A'', hUpdate, hsave, -, -, -⟩ :=
    GoldilocksCorrectness.Statements.Routines.lem15_tick_updates_confirmation S.C S.P S.X _ n₂ _
      sent₂ hrun₂ (by rw [hslot₂, supportCutoff_cast]) (by rw [hslot₂]; exact hAw₂)
  rw [hslot₂, hA₂, hS₂] at hUpdate
  -- from the tick at `t₂` to `t₂ + 1` the saved confirmations are kept
  have hkeep := stateBefore_succ_keepsConfirmation x hDiv v hti₂'
  rw [hst₂] at hkeep
  obtain ⟨-, k2, -, -⟩ := hkeep
  refine ⟨A'', hUpdate, ?_⟩
  rw [← hsave, ← k2]
  exact hSaved

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
frame trees on the states before the support cutoff of slot `s + 1`. -/
theorem lem32_saved_confirmations_compatible_state (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s : ℕ) (v₁ v₂ : V) (C₁ C₂ : Block V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
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
  exact lem31_saved_confirmations_compatible S Sched x
    GST s v₁ v₂ A₁' A₂' C₁ C₂ hDiv hMono hSync hCatch hRoots hGST
    (fun t h1 h2 => hw₁ t (by omega) (by omega)) (fun t h1 h2 => hw₂ t (by omega) (by omega))
    (hw₁ _ (by omega) le_rfl).2 (hw₂ _ (by omega) le_rfl).2 hUpdate₁ hSaved₁' hUpdate₂ hSaved₂'

end GoldilocksCorrectness.Proofs.Executions
