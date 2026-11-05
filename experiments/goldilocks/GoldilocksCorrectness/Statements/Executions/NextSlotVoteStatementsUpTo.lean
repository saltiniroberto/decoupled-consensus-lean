module
public import GoldilocksCorrectness.Statements.Executions.NextSlotVoteStatements
public import GoldilocksCorrectness.Statements.Executions.AsyncDeliveryStatements
public import GoldilocksCorrectness.Proofs.Executions.Lemma26UpTo

@[expose] public section

/-!
# `NextSlotVoteStatements.lean` with the delivery premises up to a bound

The theorems of `GoldilocksCorrectness/Statements/Executions/NextSlotVoteStatements.lean` that
name a delivery premise, restated with `SynchronyFromWakeUpTo` and `CatchUpOnWakeUpTo` at a bound
on the deadlines. The
bound of each twin is the latest ordinary deadline `max t GST + Δ` of a send its proof reads,
written in the twin's own parameters.

* `lem26b_goldfish_vote_extends_voter_majority_block_held`

No `axiom`, no `native_decide`, no `sorry`. The landed page is imported, never edited.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ voteTime supportCutoff)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Routines (CountedVotes expireLocks)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **Lemma 26b, the next slot's honest vote names a block the voter holds.** Under the hypotheses
of Lemma 26, `w`'s vote `vote` is its slot-`(s + 1)` vote for a block `H_w` of `w`'s tree before the
vote time `t₃` of slot `s + 1`, and `H_w` is `R` or a descendant of `R`. The hypotheses, in words:
every time is reached, corruption is permanent, blocks and Goldfish votes are delivered within `Δ`
after `GST`, a root names one block among what honest validators hold,
a block reaches a validator only once it holds the parent, and nobody votes in an honest
validator's name; `GST` is at most the vote time of slot `s`; every `u ∈ Hs` is in the slot-`s`
committee, honest through `t₃`, put its slot-`s` vote for `H u` on the wire at its tick at the vote
time of slot `s`, and holds `H u`, `R` or a descendant of `R`, then; the validators with a vote
among those `w` counts at its slot-`(s + 1)` vote are fewer than twice `Hs`; `w` is awake and
honest from the vote time of slot `s` to the support cutoff of slot `s`; on `w`'s state before
`t₃`, the root of the fork choice is compatible with `R`, and, when that root is `R` or an ancestor
of `R`, some block of `w`'s voter tree for slot `s + 1` on `R`'s chain is a viable head; every lock
entry live at `t₃` that `w`'s revocation of slot `s + 1` leaves is compatible with `R`; and `w` put
`vote` on the wire at its tick at `t₃`.

Why: Lemma 26's proof, which reaches the block `H_w` the Goldfish fork choice of `w`'s tick ends
at. Lemma 14 makes `vote` the vote of the tick's validator, `w` by Lemma 11, for the slot of `t₃`,
with head `H_w`'s root; and the fork choice ends at a block of the viable tree of `w`'s voter tree,
a block of `w`'s frame tree, or at the anchor, a locked block of that tree or the root of the fork
choice, which is `w`'s justified or finalized block; all are in `w`'s tree (Lemmas 11 and 57).




The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s`: the slot of the votes;
- `Hs`: the honest voters of slot `s`; `H`: the block each voter's vote is for;
- `R`: the block every vote of `Hs` extends; `w`: the voter of slot `s + 1`;
- `vote`: the Goldfish vote `w` sent at the vote time of slot `s + 1`.

Read aloud: under Lemma 26's hypotheses, `w`'s vote is its slot-`(s + 1)` vote for a block of its
own tree before the vote time of slot `s + 1` that is `R` or a descendant of `R`.

Roots name blocks until `supportCutoff S s`: the proof takes as held by `w` only blocks
delivered before the support cutoff of slot `s` (Lemma 12 at slot `s`).

Restated with the delivery premises up to `supportCutoff S s`: the slot-`s` votes reach `w` by then (`lem12_honest_vote_delivered_upTo`). -/
theorem lem26b_goldfish_vote_extends_voter_majority_block_held_upTo (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (protocol S) Sched) (GST s : ℕ) (Hs : Finset V)
    (H : V → Block V) (R : Block V) (w : V) (vote : GoldfishVote V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S s))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S s))
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S s))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S s)
    -- every member of `Hs` is an honest member of the slot-`s` committee that sent its slot-`s`
    -- vote for `H u`, a block it holds that is `R` or a descendant of `R`
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ Sched.adv (voteTime S (s + 1) : Int) ∧
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      H u ∈ (stateBefore x (voteTime S s) u).S.T ∧ R.AncestorEq (H u))
    -- the validators with a vote among those `w`'s slot-`(s + 1)` vote counts are fewer than
    -- twice `Hs`
    (hVoters : ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes S.C (stateBefore x (voteTime S (s + 1)) w).A
        (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) (s + 1) votes support_votes →
      voters_count votes < 2 * Hs.card)
    -- `w` is awake and honest from slot `s`'s vote time to its support cutoff
    (hw : ∀ t : ℕ, voteTime S s ≤ t → t ≤ supportCutoff S s →
      w ∈ Sched.awake (t : Int) ∧ w ∉ Sched.adv (t : Int))
    -- on `w`'s state before `t₃`, the root of its fork choice is compatible with `R`
    (hF2 : (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).fc_root.compatible R = true)
    -- when that root is `R` or an ancestor of `R`, a block of `w`'s voter tree on `R`'s chain is
    -- a viable head
    (hF3 : (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).fc_root.AncestorEq R →
      ∀ tree : Finset (Block V),
        voter_block_tree S.C (stateBefore x (voteTime S (s + 1)) w).A
          (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) (s + 1) = .ok tree →
        ∃ W ∈ tree, W ∈ (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).viable_heads ∧
          R.AncestorEq W)
    -- the block of every lock entry live at `t₃` that `w`'s revocation leaves is compatible
    -- with `R`
    (hLocks : ∀ A' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S (s + 1)) w).A
        ((voteTime S (s + 1) : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
        ((voteTime S (s + 1) : ℕ) : Int) (s + 1) = .ok A' →
      ∀ e ∈ A'.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
          ((voteTime S (s + 1) : ℕ) : Int) e = true → e.B.compatible R = true)
    -- `w` put `vote` on the wire at its tick at `t₃`
    (hSend : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s + 1)) ∧
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent) :
    -- then `vote` is `w`'s slot-`(s + 1)` vote for a block it holds on `R`'s chain
    ∃ H_w ∈ (stateBefore x (voteTime S (s + 1)) w).S.T,
      vote = GoldfishVote.mk w (s + 1) H_w.root ∧ R.AncestorEq H_w :=
  GoldilocksCorrectness.Proofs.Executions.lem26b_goldfish_vote_extends_voter_majority_block_held_upTo S
    Sched x GST s Hs H R w vote hDiv hMono hSync hCatch hRoots hParent hOwner hGST hHs
    hVoters hw hF2 hF3 hLocks hSend

end GoldilocksCorrectness.Statements.Executions

