module
public import GoldilocksCorrectness.Proofs.Executions.Relay
public import GoldilocksCorrectness.Proofs.Executions.BlockPropagation
public import GoldilocksCorrectness.Proofs.Routines.BlockLookup
public import GoldilocksCorrectness.Proofs.Routines.ACStore

@[expose] public section

/-!  The unnumbered facts the
proof of Lemma 23 (`Lemma23.lean`) reads:

- the resolution of a vote, at the routine level: `resolved_eq_ok_true` (the head block in the
  tree, of a slot at most the vote's), `tau_eq_ok_some` (the same, with the two stamps),
  `tau_head_of_eq_some` (a vote that resolves has its head block in the tree, of a slot at most the
  vote's);
- the equivocators, as two distinct votes: `mem_equivocators_iff_two`;
- along an execution: `pool_vote_reaches_proposer`, a vote the voter of slot `s + 1` holds before
  the view freeze of slot `s` reached the proposer of slot `s + 1` before its proposal, or the
  proposer holds two votes of its validator then (the inline `hToV` of `Lemma21.lean`, with the
  proposer for the receiver).
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

/-! ## The resolution of a vote -/

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime viewFreeze)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_eq viewFreeze_eq voteTime_eq)

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Statements.Routines

variable {V : Type} [DecidableEq V]

variable [Fintype V]

end GoldilocksCorrectness.Proofs.Routines

/-! ## A vote the voter holds before the view freeze reaches the proposer -/

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
proposer before its proposal, unless the proposer already holds two votes of its validator. -/
theorem pool_vote_reaches_proposer (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption) (GST : ℕ)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (s : ℕ) (p w : V) (vote : GoldfishVote V)
    -- the network is synchronous from the vote time of slot `s` on
    (hGST : GST ≤ voteTime S s)
    -- `p` is awake and honest from the view freeze of slot `s` to the start of slot `s + 1`
    (hp : ∀ t : ℕ, viewFreeze S s ≤ t → t ≤ slotStart S (s + 1) →
      p ∈ Sched.awake (t : Int) ∧ p ∉ Sched.adv (t : Int))
    -- `w` holds `vote` in its pool of slot `s` before the view freeze of slot `s`
    (hvote : vote ∈ (stateBefore x (viewFreeze S s) w).A.pool s) :
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
  have hres := pool_vote_reaches_before_add_delay S Sched x hDiv hMono GST hSync hCatch
    (viewFreeze S s) s w p vote (by omega) (by omega) (fun t' h1 h2 => hp t' h1 (by omega)) hvote
  have hfzΔ : viewFreeze S s + Δ S = slotStart S (s + 1) := by omega
  rw [hfzΔ] at hres
  exact hres

end GoldilocksCorrectness.Proofs.Executions
