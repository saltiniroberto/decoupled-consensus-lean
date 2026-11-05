module
public import GoldilocksCorrectness.Proofs.Executions.Lemma22
public import GoldilocksCorrectness.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Proofs.Executions.ProposalPropagationUpTo

@[expose] public section

/-!
# `Lemma22.lean` with the delivery premises up to a bound

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma22.lean` that name a delivery
premise, restated with `SynchronyFromWakeUpTo` and `CatchUpOnWakeUpTo` at a bound on the deadlines
. The bound of each twin
is the latest ordinary deadline `max t GST + Δ` of a send its proof reads, written in the twin's
own parameters.

* `lem22_proposal_held_by_voter`

No `axiom`, no `native_decide`, no `sorry`. The landed page is imported, never edited.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_eq voteTime_eq)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicAction AtomicExec Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Proofs.Routines (compatible_of_ancestorEq_compatible compatible_iff)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **Lemma 22, an honest proposal reaches the next slot's voter.** The proof; the audited
statement is in `Statements/Executions/ProposalPropagationStatements.lean`.

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution; `GST`: the time from which the
  network is synchronous; `s`: the slot before the proposal's;
- `i`: the step of `p`'s tick at the start of slot `s + 1`; `B`: the block; `p`: the proposer;
  `w`: the voter of slot `s + 1`.

Roots name blocks until `voteTime S (s + 1)`: `mem_T_before_of_send`'s bound at the start of
slot `s + 1`, one delay after it.

Restated with the delivery premises up to `voteTime S (s + 1)`: the proposal of slot `s + 1` reaches `w` by then (`mem_T_before_of_send_upTo`). -/
theorem lem22_proposal_held_by_voter_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s i : ℕ) (B : Block V) (p w : V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (voteTime S (s + 1)))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (voteTime S (s + 1)))
    (hRoots : RootsNameBlocksUntil S Sched x (voteTime S (s + 1)))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hGST : GST ≤ voteTime S s)
    (hp : p ∉ Sched.adv (slotStart S (s + 1) : Int))
    (hw : ∀ t : ℕ, slotStart S (s + 1) ≤ t → t ≤ voteTime S (s + 1) →
      w ∈ Sched.awake (t : Int) ∧ w ∉ Sched.adv (t : Int))
    -- `p`'s tick at the start of slot `s + 1` is the step `i`, put `B` on the wire, and left
    -- `p` holding `B`
    (hl : x.lbl i = AtomicAction.tickAllAwake (slotStart S (s + 1)))
    (hsent : (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
      x[i + 1].sent - x[i].sent)
    (hBp : B ∈ (x[i + 1][p].st).S.T)
    -- `w`'s finalized block before its vote is compatible with `B`
    (hF : (stateBefore x (voteTime S (s + 1)) w).S.F.compatible B = true) :
    B ∈ (stateBefore x (voteTime S (s + 1)) w).S.T := by
  -- step 0: the times
  have hv₃ : voteTime S (s + 1) = slotStart S (s + 1) + Δ S := voteTime_eq S (s + 1)
  have hv₁ : voteTime S s ≤ slotStart S (s + 1) := by
    rw [voteTime_eq, slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
    have := one_le_Δ S
    omega
  obtain ⟨hti, hti'⟩ := time_of_lbl_tickAllAwake x hl
  -- step 1: `p` is honest at the end of its tick
  have huh : p ∉ Sched.adv (x[i + 1].time : Int) := by
    rw [hti']
    exact hp
  -- step 2: the propagation from `p`'s send, at `t := t₁`
  rw [hv₃] at hF hw ⊢
  exact mem_T_before_of_send_upTo S Sched x hDiv hMono GST hSync hCatch hRoots hParent i
    (slotStart S (s + 1)) p w B hsent hBp huh (by omega) (by omega) hw hF (by omega) (by omega)

end GoldilocksCorrectness.Proofs.Executions

