module
public import GoldilocksCorrectness.Statements.Executions.FrameShapeStatements
public import GoldilocksCorrectness.Statements.Executions.AsyncDeliveryStatements
public import GoldilocksCorrectness.Proofs.Executions.FrameShapeUpTo

@[expose] public section

/-!
# `FrameShapeStatements.lean` with the delivery premises up to a bound

The theorems of `GoldilocksCorrectness/Statements/Executions/FrameShapeStatements.lean` that name
a delivery premise, restated with `SynchronyFromWakeUpTo` and `CatchUpOnWakeUpTo` at a bound on
the deadlines. The bound
of each twin is the latest ordinary deadline `max t GST + Δ` of a send its proof reads, written in
the twin's own parameters.

* `lem60_update_confirmation_fast_locks_frame`

No `axiom`, no `native_decide`, no `sorry`. The landed page is imported, never edited.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ voteTime supportCutoff dutyWindowStart)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Routines (expireLocks CountedVotes FrameShape)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **Lemma 60, the confirmation update makes a voter-majority block fast and locks it, over a
root.** Under the hypotheses of Lemma 29
(`lem29_update_confirmation_fast_locks_voter_majority_block`) with "`v`'s finalized block before
the support cutoff `t₂` of slot `s + 1` is `B` or an ancestor of `B`" replaced by "the root of
`v`'s fork choice before `t₂` is `B` or an ancestor of `B`", `v`'s node state before `t₂ + 1` has
`B` among its fast blocks and the lock entry on `B` with the deadline
`S.C.t_ (s + S.C.k) + 5 · S.C.Δ`.

Why: the finalized block is the root of the fork choice or an ancestor of it (Lemma 46); Lemma 29
concludes.

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s`: the slot of the votes;
- `Hs`: the honest voters of slot `s`; `B`: the block their votes are for;
- `v`: the validator running the confirmation update of slot `s`.

Read aloud: when the root of `v`'s fork choice is `B` or an ancestor of `B`, Lemma 29's conclusion
holds.



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
    -- the validators with a slot-`s` vote in `v`'s pool before `t₂` are fewer than twice `Hs`
    (hVoters : voters_count ((stateBefore x (supportCutoff S (s + 1)) v).A.pool s) <
      2 * Hs.card)
    -- the slot-`s` committee is at most twice `Hs`
    (hHalf : (S.P.committee s).card ≤ 2 * Hs.card)
    (hBne : B ≠ Block.genesis)
    (hv : ∀ t : ℕ, dutyWindowStart S (s + 1) ≤ t → t ≤ supportCutoff S (s + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    -- the root of `v`'s fork choice before `t₂` is `B` or an ancestor of `B`
    (hRootV : (get_fc_root (stateBefore x (supportCutoff S (s + 1)) v).S).AncestorEq B) :
    B ∈ (stateBefore x (supportCutoff S (s + 1) + 1) v).A.fast_blocks ∧
      LockEntry.mk B (S.C.t_ (s + S.C.k) + 5 * S.C.Δ) ∈
        (stateBefore x (supportCutoff S (s + 1) + 1) v).A.lock_entries :=
  GoldilocksCorrectness.Proofs.Executions.lem60_update_confirmation_fast_locks_frame_upTo S Sched x GST
    s Hs B v hDiv hMono hSync hCatch hRoots hParent hOwner hGST hHs hVoters hHalf hBne hv
    hRootV

end GoldilocksCorrectness.Statements.Executions

