module
public import GoldilocksCorrectness.Proofs.Executions.Lemma26Held

@[expose] public section

/-! a kit statement, new, no landed statement changes. Proved in
`GoldilocksCorrectness/Proofs/Executions/Lemma26Held.lean`.

- `lem26b_goldfish_vote_extends_voter_majority_block_of_held`: Lemma 26b with the delivery of the
  slot-`s` votes replaced by the votes held, stamped and resolved strictly before a time at most
  the view freeze of `s`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (voteTime viewFreeze)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Routines (CountedVotes expireLocks)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **Lemma 26b from held votes, the next slot's honest vote names a block the voter holds.** In an
execution that reaches every time, with permanent corruption, where nobody votes in an honest
validator's name: if `tb` is at most the view freeze of slot `s`; every `u ∈ Hs` is honest at the
vote time `t₃` of slot `s + 1`, put its slot-`s` vote for `H u` on the wire at its tick at the vote
time of slot `s`, and `H u` is `R` or a descendant of `R`; in the case `w`'s finalized block before
`t₃` is `R` or an ancestor of `R`, `w`'s AC state before `t₃` holds every such vote as its voter's
only slot-`s` vote, stamped and resolved strictly before `tb`, with `H u` in `w`'s frame tree; the
validators with a vote among those `w` counts at its slot-`(s + 1)` vote are fewer than twice `Hs`;
on `w`'s state before `t₃`, the root of the fork choice is compatible with `R`, and, when that root
is `R` or an ancestor of `R`, some block of `w`'s voter tree for slot `s + 1` on `R`'s chain is a
viable head; in the same case as the votes held, every lock entry live at `t₃` that `w`'s revocation
of slot `s + 1` leaves is compatible with `R`; and `w` put `vote` on the wire at its tick at `t₃` —
then `vote` is `w`'s slot-`(s + 1)` vote for a block `H_w` of `w`'s tree before `t₃`, and `H_w` is
`R` or a descendant of `R`.

Why: Lemma 26b's proof. In the case `R` is an ancestor of `w`'s finalized block, the walk's end
descends from the root of the fork choice, which descends from the finalized block. Otherwise the
votes are held (`hHeld`), and the proof reads their stamps only against the view freeze of `s`,
which `tb` is at most; the locks are `hLocks` in the same case.


Against Lemma 26b (`Statements/Executions/NextSlotVoteStatements.lean`): `hSync`, `hCatch`,
`hRoots`, `hParent`, `hGST`, `hw` are not taken, the delivery of Lemma 12 being replaced by `hHeld`;
`htb` is added; `hLocks` is read under the case `w`'s finalized block is `R` or an ancestor of `R`.
Two conjuncts of Lemma 26b's `hHs` are not read by the proof and are deleted:
`u ∈ S.P.committee s` and `H u ∈ (stateBefore x (voteTime S s) u).S.T`, both read by Lemma 26b only
through its Lemma 12 call.

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `s`: the slot of the votes; `tb`: the bound on their stamps and resolutions;
- `Hs`: the honest voters of slot `s`; `H`: the block each voter's vote is for;
- `R`: the block every vote of `Hs` extends; `w`: the voter of slot `s + 1`;
- `vote`: the Goldfish vote `w` sent at the vote time of slot `s + 1`.

Read aloud: Lemma 26b with the delivery of the slot-`s` votes replaced by the votes held, stamped
and resolved strictly before a time at most the view freeze of `s`: whoever holds a majority's votes
on `R`'s chain votes on `R`'s chain. -/
theorem lem26b_goldfish_vote_extends_voter_majority_block_of_held (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (protocol S) Sched) (s tb : ℕ) (Hs : Finset V)
    (H : V → Block V) (R : Block V) (w : V) (vote : GoldfishVote V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hOwner : VotesCastByOwner S Sched x)
    -- `tb` is at most the view freeze of slot `s`
    (htb : tb ≤ viewFreeze S s)
    -- every member of `Hs` is honest at `t₃` and sent its slot-`s` vote for `H u`, which is `R` or
    -- a descendant of `R`
    (hHs : ∀ u ∈ Hs, u ∉ Sched.adv (voteTime S (s + 1) : Int) ∧
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      R.AncestorEq (H u))
    -- in the case `w`'s finalized block is `R` or an ancestor of `R`: the slot-`s` votes held
    (hHeld : (stateBefore x (voteTime S (s + 1)) w).S.F.AncestorEq R →
      ∀ u ∈ Hs, HeldEarlyVoteAt (stateBefore x (voteTime S (s + 1)) w).A
        (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) ((tb : ℕ) : Int) s (H u) u)
    -- the validators with a vote among those `w`'s slot-`(s + 1)` vote counts are fewer than
    -- twice `Hs`
    (hVoters : ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes S.C (stateBefore x (voteTime S (s + 1)) w).A
        (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) (s + 1) votes support_votes →
      voters_count votes < 2 * Hs.card)
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
    -- in the same case: the block of every lock entry live at `t₃` that `w`'s revocation leaves
    -- is compatible with `R`
    (hLocks : (stateBefore x (voteTime S (s + 1)) w).S.F.AncestorEq R → ∀ A' : ACState V,
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
  GoldilocksCorrectness.Proofs.Executions.lem26b_goldfish_vote_extends_voter_majority_block_of_held
    S Sched x s tb Hs H R w vote hDiv hMono hOwner htb hHs hHeld hVoters hF2 hF3 hLocks hSend

end GoldilocksCorrectness.Statements.Executions
