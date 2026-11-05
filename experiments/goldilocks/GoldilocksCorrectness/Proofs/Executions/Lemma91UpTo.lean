module
public import GoldilocksCorrectness.Proofs.Executions.Lemma91
public import GoldilocksCorrectness.Proofs.Executions.AsyncDelivery

@[expose] public section

/-!
# `Lemma91.lean` with the delivery premises up to a bound

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma91.lean` that name a delivery
premise, restated with `SynchronyFromWakeUpTo` and `CatchUpOnWakeUpTo` at a bound on the deadlines
. The bound of each twin
is the latest ordinary deadline `max t GST + Δ` of a send its proof reads, written in the twin's
own parameters.

* `lem91c_proposer_h_max_le_voter_h_max_until`

No `axiom`, no `native_decide`, no `sorry`. The landed page is imported, never edited.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff)
open GoldilocksCorrectness.Proofs.Routines (slot_after_healed_round slot_le_of_supportCutoff_lt
  voteTime_eq)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (JustificationCertOn ProgressCertOn
  lem66_chain_state_certified lem67_first_advance lem67b_first_advance_cases)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  ancestorEq_antisymm ancestorEq_of_parent?)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

/-- **Lemma 91 (c), the voter is at least as far as the proposer.** The proof; the audited
statement is in `Statements/Executions/HealedFrameStatements.lean`. It is the instance of
`lem91c_at` at `t := slotStart S s`, `b := voteTime S s`: the slot comes after the healed slot's
support cutoff, so `GST ≤ slotStart S s` and `1 ≤ slotStart S s` (`slot_after_healed_round`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `s`: the slot; `i₁`: the step at the phase's end;
  `H`: the threshold; `p`: the proposer; `w`: the voter.

Roots name blocks until `voteTime S s`: `lem91c_at`, which the proof calls with
`b := voteTime S s`, takes blocks as held up to that time (`p`'s block reaching `w` by the vote
time; the entry `cert_entry_at_slot` returns, held by the support cutoff of its slot, a time
before `slotStart S s`).

Caches up to `voteTime S s`: `lem91c_at_until` at `t := slotStart S s`, whose `t + Δ S` is the vote
time of slot `s`.

On the chain before `s − 1`: the blocks `lem91c_at_until` compares are on the chain at slots whose
next slot's support cutoff is before the vote time of slot `s`, so less than `s − 1`.

Restated with the delivery premises up to `voteTime S s`: `lem91c_at_until` reads the deliveries due by then. -/
theorem lem91c_proposer_h_max_le_voter_h_max_until_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ s i₁ H : ℕ) (p w : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (voteTime S s))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (voteTime S s))
    (hRoots : RootsNameBlocksUntil S Sched x (voteTime S s))
    (hParent : ParentHeldAtDelivery S Sched x) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hGST : GST ≤ voteTime S s₀) (ht₀ : supportCutoff S (s₀ + 1) ≤ x[i₁].time)
    (hs : x[i₁].time < slotStart S s)
    (hChain : ConfirmationsChainBefore S Sched x s₀ (s - 1))
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → x[j].time ≤ voteTime S s →
      u ∉ Sched.adv (x[j].time : Int) → CachesOnChain S Sched x s₀ H (x[j][u].st))
    (hp : p ∉ Sched.adv ((slotStart S s : ℕ) : Int))
    (hw : ∀ t' : ℕ, slotStart S s ≤ t' → t' ≤ voteTime S s →
      w ∈ Sched.awake (t' : Int) ∧ w ∉ Sched.adv (t' : Int)) :
    (stateBefore x (slotStart S s) p).S.h_max ≤ (stateBefore x (voteTime S s) w).S.h_max := by
  obtain ⟨-, hvs, h1s⟩ := slot_after_healed_round S s₀ s (lt_of_le_of_lt ht₀ hs)
  rw [voteTime_eq S s] at hw hRoots hCaches hSync hCatch ⊢
  exact lem91c_at_until S Sched x GST s₀ (slotStart S s) i₁ H (slotStart S s + Δ S) (s - 1) p w
    hDiv hMono hSync hCatch hRoots hParent hU hAdvQ (by omega) h1s
    hs hChain (fun s_a h => by
      have := (slot_le_of_supportCutoff_lt S s_a s).1 (by rw [voteTime_eq]; exact h)
      omega) hOld hCaches hp hw le_rfl

end GoldilocksCorrectness.Proofs.Executions

