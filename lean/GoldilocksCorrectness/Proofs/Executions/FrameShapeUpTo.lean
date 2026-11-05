module
public import GoldilocksCorrectness.Proofs.Executions.FrameShape
public import GoldilocksCorrectness.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Statements.Executions.FastConfirmationStatementsUpTo

@[expose] public section

/-!
# `FrameShape.lean` with the delivery premises up to a bound

The theorems of `GoldilocksCorrectness/Proofs/Executions/FrameShape.lean` that name a delivery
premise, restated with `SynchronyFromWakeUpTo` and `CatchUpOnWakeUpTo` at a bound on the deadlines
. The bound of each twin
is the latest ordinary deadline `max t GST + Δ` of a send its proof reads, written in the twin's
own parameters.

* `lem60_update_confirmation_fast_locks_frame`

No `axiom`, no `native_decide`, no `sorry`. The landed page is imported, never edited.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ voteTime supportCutoff dutyWindowStart)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (expireLocks CountedVotes FrameShape)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_trans ancestorEq_refl compatible_iff
  ancestorEq_of_parent?)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- Lemma 60, the confirmation update makes a voter-majority block fast and locks it, over a root.
The proof; the audited statement is in `Statements/Executions/FrameShapeStatements.lean`.

Roots name blocks until `supportCutoff S s`: Lemma 29, which the proof calls, takes blocks as
held up to the support cutoff of slot `s`.

Restated with the delivery premises up to `supportCutoff S s`: the slot-`s` votes reach `v` by then (`lem12_honest_vote_delivered_until_upTo`). -/
theorem lem60_update_confirmation_fast_locks_frame_upTo (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (protocol S) Sched) (GST s : ℕ) (Hs : Finset V)
    (B : Block V) (v : V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S s))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S s))
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S s))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S s)
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ Sched.adv (supportCutoff S (s + 1) : Int) ∧
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s B.root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      B ∈ (stateBefore x (voteTime S s) u).S.T)
    (hVoters : voters_count ((stateBefore x (supportCutoff S (s + 1)) v).A.pool s) <
      2 * Hs.card)
    (hHalf : (S.P.committee s).card ≤ 2 * Hs.card)
    (hBne : B ≠ Block.genesis)
    (hv : ∀ t : ℕ, dutyWindowStart S (s + 1) ≤ t → t ≤ supportCutoff S (s + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    (hRootV : (get_fc_root (stateBefore x (supportCutoff S (s + 1)) v).S).AncestorEq B) :
    B ∈ (stateBefore x (supportCutoff S (s + 1) + 1) v).A.fast_blocks ∧
      LockEntry.mk B (S.C.t_ (s + S.C.k) + 5 * S.C.Δ) ∈
        (stateBefore x (supportCutoff S (s + 1) + 1) v).A.lock_entries :=
  GoldilocksCorrectness.Statements.Executions.lem29_update_confirmation_fast_locks_voter_majority_block_upTo
    S Sched x GST s Hs B v hDiv hMono hSync hCatch hRoots hParent hOwner hGST hHs hVoters
    hHalf hBne hv (ancestorEq_trans (F_ancestorEq_fc_root_of_stateBefore S Sched x _ v) hRootV)

end GoldilocksCorrectness.Proofs.Executions

