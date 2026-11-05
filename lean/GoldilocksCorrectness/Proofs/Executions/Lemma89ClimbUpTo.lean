module
public import GoldilocksCorrectness.Proofs.Executions.Lemma89Climb
public import GoldilocksCorrectness.Proofs.Executions.AsyncDelivery

@[expose] public section

/-!
# `Lemma89Climb.lean` with the delivery premises up to a bound

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma89Climb.lean` that name a delivery
premise, restated with `SynchronyFromWakeUpTo` and `CatchUpOnWakeUpTo` at a bound on the deadlines
. The bound of each twin
is the latest ordinary deadline `max t GST + Δ` of a send its proof reads, written in the twin's
own parameters.

* `honest_h_max_bounds`

No `axiom`, no `native_decide`, no `sorry`. The landed page is imported, never edited.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (lem49_tick_attests expireLocks)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- **B2, the honest `h_max` from `T₁ + Δ` to `a_r`.** The proof; the audited statement is in
`Statements/Executions/Lemma89Statements.lean`.

The route: at least `H₂` by `lem89b_at` (Lemma 89b on the four facts its proof reads) at the
honest attestation of height `H₂` sent before `T₁`, when `H₂ ≠ 0`; at most `H₂ + 1` because
`h_max` is the chain-state height of a block `w` holds (`cachesWitnessed_of_stateBefore`) and A2
bounds every such block.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `tGAT`, `tAwakeEnd`: the ends of the phase; `T₁`: the time of the
  threshold; `r`: the round; `H₂`: the threshold; `t`: the time; `w`: the validator.

Roots name blocks until `t`: the proof reads `lem89b_at` at `b := t`, `w`'s reading time.

Restated with the delivery premises up to `t`: the bound of its roots, `lem89b_at` read at `b := t`. -/
theorem honest_h_max_bounds_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd T₁ r H₂ t : ℕ) (w : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject t)
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject t)
    (hRoots : RootsNameBlocksUntil S Sched x t)
    (hParent : ParentHeldAtDelivery S Sched x) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hGST : GST ≤ tGAT) (hT₁ : tGAT ≤ T₁)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t' : ℕ, tGAT ≤ t' → t' ≤ tAwakeEnd →
      ∀ u : V, u ∉ Sched.adv (t' : Int) → u ∈ Sched.awake (t' : Int))
    (hH₂ : OldHeightAttained S Sched x T₁ H₂)
    (hOld : OldAttestationsAtMost S Sched x (aR S r) H₂)
    (hEnd : aR S r ≤ tAwakeEnd)
    (ht₁ : T₁ + Δ S ≤ t) (htr : t ≤ aR S r) (hw : w ∉ Sched.adv (t : Int)) :
    H₂ ≤ (stateBefore x t w).S.h_max ∧ (stateBefore x t w).S.h_max ≤ H₂ + 1 := by
  refine ⟨?_, ?_⟩
  · rcases hH₂.2 with h0 | ⟨t', u, a, ht', ⟨i, hl, -, -, hm⟩, hah⟩
    · rw [h0]
      exact Nat.zero_le _
    · rw [← hah]
      have hΔ := one_le_Δ S
      refine lem89b_at S Sched x GST t t' i t u w a hDiv hMono
        hSync hCatch hRoots hParent hU (by omega)
        (adversaryFewerThanThirdUntil_of_le (by exact_mod_cast (show t ≤ tAwakeEnd by omega))
          hThird) (by omega) ?_ ⟨hl, hm⟩ le_rfl
      intro t'' h1 h2
      have hwt : w ∉ Sched.adv (t'' : Int) := fun h => hw (hMono _ _ (by omega) h)
      exact ⟨hAwake t'' (by omega) (by omega) w hwt, hwt⟩
  · obtain ⟨-, ⟨X, hX, hXh⟩, -⟩ := cachesWitnessed_of_stateBefore S Sched x t w
    rw [← hXh]
    exact held_height_le_before_action S Sched x tAwakeEnd r H₂ t w X hU hThird hOld htr hEnd hX

end GoldilocksCorrectness.Proofs.Executions

