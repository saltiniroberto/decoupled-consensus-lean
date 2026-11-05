module
public import GoldilocksCorrectness.Proofs.Executions.Lemma27
public import GoldilocksCorrectness.Proofs.Executions.Lemma29

@[expose] public section

/-!  The proof:

1. the voter bound: every vote of `v`'s slot-`s` pool is from the slot-`s` committee
   (`pool_committee_of_stateBefore`), so the committee majority makes the validators with a vote
   in it fewer than twice `Hs` (`voters_count_lt_of_committee_majority`);
2. the half condition from the committee majority (`committee_card_le_of_majority`);
3. the lock condition of Lemma 27 from the half condition (`lock_entries_compatible_of_half`:
   Lemma 12 at the vote time of slot `s + 1`, then Lemma 5);
4. Lemma 27 gives `B` saved and the confirmed tip advanced, Lemma 29 `B` fast and locked.
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
open GoldilocksCorrectness.Proofs.Routines (committee_card_le_of_majority
  voters_count_lt_of_committee_majority)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- Lemma 18, an honest validator's confirmation update confirms a block a committee majority
voted for early. Its reading is on the statement page,
`GoldilocksCorrectness/Statements/Executions/FastConfirmationStatements.lean`. It is Lemmas 27
and 29 with the committee majority, which gives their voter bound because every vote of `v`'s
pool is from the slot-`s` committee, their half condition, and Lemma 27's lock condition through
Lemma 5.

Roots name blocks until `supportCutoff S s`: the bound of Lemma 27,
`lock_entries_compatible_of_half` and Lemma 29, which it calls. -/
theorem lem18_update_confirmation_confirms_majority_block (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s : ℕ) (Hs : Finset V) (B : Block V) (v : V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S s))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S s)
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ Sched.adv (supportCutoff S (s + 1) : Int) ∧
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s B.root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      B ∈ (stateBefore x (voteTime S s) u).S.T)
    (hMajority : (S.P.committee s \ Hs).card < Hs.card)
    (hBne : B ≠ Block.genesis)
    (hv : ∀ t : ℕ, dutyWindowStart S (s + 1) ≤ t → t ≤ supportCutoff S (s + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    (hF1 : (stateBefore x (supportCutoff S (s + 1)) v).S.F.AncestorEq B) :
    (stateBefore x (supportCutoff S (s + 1) + 1) v).A.saved_confirmation s = some B ∧
      B ∈ (stateBefore x (supportCutoff S (s + 1) + 1) v).A.fast_blocks ∧
      LockEntry.mk B (S.C.t_ (s + S.C.k) + 5 * S.C.Δ) ∈
        (stateBefore x (supportCutoff S (s + 1) + 1) v).A.lock_entries ∧
      (stateBefore x (supportCutoff S (s + 1) + 1) v).A.latest_confirmed =
        advance (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S)
          (stateBefore x (supportCutoff S (s + 1)) v).A.latest_confirmed (some B) := by
  have hVoters : voters_count ((stateBefore x (supportCutoff S (s + 1)) v).A.pool s) <
      2 * Hs.card :=
    voters_count_lt_of_committee_majority (pool_committee_of_stateBefore S Sched x _ v s) hMajority
  have hHalf : (S.P.committee s).card ≤ 2 * Hs.card := committee_card_le_of_majority hMajority
  obtain ⟨hsave, hlatest⟩ := lem27_update_confirmation_confirms_voter_majority_block S Sched x GST
    s Hs B v hDiv hMono hSync hCatch hRoots hParent hOwner hGST hHs hVoters hBne hv hF1
    (lock_entries_compatible_of_half S Sched x GST s Hs B v hDiv hMono hSync hCatch hRoots
      hParent hOwner hGST hHs hHalf hv hF1)
  obtain ⟨hfast, hlock⟩ := lem29_update_confirmation_fast_locks_voter_majority_block S Sched x GST
    s Hs B v hDiv hMono hSync hCatch hRoots hParent hOwner hGST hHs hVoters hHalf hBne hv hF1
  exact ⟨hsave, hfast, hlock, hlatest⟩

end GoldilocksCorrectness.Proofs.Executions
