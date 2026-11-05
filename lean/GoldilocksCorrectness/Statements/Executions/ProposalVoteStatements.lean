module
public import GoldilocksCorrectness.Proofs.Executions.Lemma20

@[expose] public section

/-!
# The next slot's honest Goldfish vote names the honest proposal

The audited statement of G0 over executions, `lem20_goldfish_vote_names_honest_proposal`, proved
in `GoldilocksCorrectness/Proofs/Executions/Lemma20.lean`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Routines (expireLocks CountedVotes ProposalCountedVotes)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **Lemma 20, the next slot's honest vote names the honest proposal.** In an execution where
every time is reached, corruption is permanent, blocks and Goldfish votes are delivered within `Δ`
after `GST` (synchrony from the receiver's wake, and catch-up on wake),
a root names one block among what honest validators hold, a block reaches a validator only once it
holds the parent, and nobody votes in an honest validator's name: if `GST` is at most the vote time
of slot `s`; every `u ∈ Hs` is in the slot-`s` committee, honest through the vote time `t₃` of slot
`s + 1`, put its slot-`s` vote for `H u` on the wire at its tick at the vote time of slot `s`, and
holds `H u`, a block that is `X` or a descendant of `X`, in its tree then; the validators with a
vote among those `w`'s slot-`(s + 1)` vote counts are fewer than twice `Hs`; `p` and `w` are awake and honest at every time from the vote time of
slot `s` to its support cutoff; `p` put the block `B` on the wire at its tick at the start `t₁` of
slot `s + 1`, and `w` put the Goldfish vote `vote` on the wire at its tick at `t₃`; `w`'s tree
before `t₃` holds `B`; on `p`'s node state before `t₁`, some block of its frame's tree that is `X`
or a descendant of `X` is a viable head, and its anchor at `t₁` is `X` or an ancestor of `X`; on
`w`'s node state before `t₃`, the block of every lock entry live at `t₃` that `w`'s revocation of
slot `s + 1` leaves is `B` or an ancestor of `B`, and `B` is a viable head; and, writing a path
block for a block from `X` to `B`'s parent that has the root of `w`'s fork choice as an ancestor or
is that root: every path block is a viable head at `p` exactly when it is one at `w`; for the sets
`p`'s proposal counts (`ProposalCountedVotes`) and the sets `w`'s vote counts (`CountedVotes`), the
two scores answer the same number on every child of a path block and the two sets of votes have the
same number of voters; and every child in `w`'s viable tree of a path block, other than `B`, that
`w`'s eligibility test accepts (counting those sets), is in `p`'s viable tree — then `vote`'s head
is the root of `B`.




- the hypothesis that `w`'s finalized block is each `H u` or an ancestor of it was deleted: where
  the proof needs it, `w`'s anchor is `X` or an ancestor of `X`, and it follows the same way;
- the hypothesis that `B` is the only slot-`(s + 1)` block `w` holds was deleted: the proof did not
  use it;
- the block of every live lock entry `w`'s revocation leaves is now `B`'s parent or an ancestor
  of it, where it was `X` or an ancestor of `X`;
- the scores are assumed to agree only on the children of the path blocks, where they were
  assumed on every block;
- the viable heads, the scores and the children are assumed only along the path blocks, the blocks
  from `X` to `B`'s parent that have the root of `w`'s fork choice as an ancestor (or are that
  root), where they were assumed from `X` on: that root may be a descendant of `X`, a block
  strictly between `X` and it is not a viable head at `w` while it may be one at `p`, and the proof
  reads only blocks that have `w`'s anchor as an ancestor (or are it), and the anchor has that root
  as an ancestor (or is it);
- the children assumed in `p`'s viable tree are only those `w`'s eligibility test accepts;
- `p`'s and `w`'s awake windows were narrowed from "from the start of slot `s` to `t₁`" and "from
  the start of slot `s` to `t₃`" to "from the vote time of slot `s` to its support cutoff", the
  window Lemma 12 reads;



 the committee majority gives it through the admission invariant.

Why: `p`'s tick at `t₁` sent `B`, so `B` is `p`'s proposal: its parent is the end of the Goldfish
fork choice from `p`'s anchor through `p`'s viable tree, counting `p`'s slot-`s` pool (Lemma 19).
`w`'s tick at `t₃` sent `vote`, so its head is the root of the end `H_w` of the Goldfish fork choice
from the anchor of `w`'s revoked AC state (Lemma 14). By Lemma 12 at `t₁`, every `u ∈ Hs` has its
vote for `H u` as its only slot-`s` vote in `p`'s pool, resolved. At `p` the anchor starts towards
`X` (Lemma 7, with F3), and `p` counts as many voters as `w`, fewer than twice `Hs`, so `p`'s walk
passes `X` (Lemma 2). At `w` the anchor is `B` or an ancestor of `B`
(`get_anchor_ancestorEq_of_entries`: the live lock entries are on `B` or ancestors of `B`, and the
root of `w`'s fork choice is `B` or an ancestor of it, `B` being a viable head), and so is `X`: the
anchor is an ancestor of `X`, `X`, or a descendant of `X`. When the anchor is `B`, `B` has no child
in `w`'s tree and `w`'s walk ends at `B`. Every block of `w`'s frame tree on `B`'s chain is in `w`'s
viable tree (`B` is a slot-`(s + 1)` viable head). When the anchor is `X` or an ancestor of `X`,
Lemma 12 at `t₃` gives the votes of `Hs` in `w`'s pool, the anchor starts towards `X` (Lemma 7),
`w`'s walk passes `X` (Lemma 2), and `X` is the shared block. When the anchor is a descendant of `X`
other than `B`, it is a block of `p`'s walk from `X` to `B`'s parent, `w`'s walk starts there, and
the anchor is the shared block. From the shared block on, the two walks see the same scores and the
same eligibility answers on the children of the path, `B` is eligible at `w` as a block of the
current slot and has no child in `w`'s tree, so `w`'s walk ends at `B` (Lemma 9).



The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s`: the slot of the votes;
- `Hs`: the honest voters of slot `s`; `H`: the block each voter's vote is for;
- `X`: the block every vote of `Hs` extends; `B`: the block `p` proposed at the start of slot
  `s + 1`;
- `p`: the proposer of slot `s + 1`; `w`: the voter of slot `s + 1`;
- `vote`: the Goldfish vote `w` sent at the vote time of slot `s + 1`.

Read aloud: if the honest members `Hs` of the slot-`s` committee sent at the vote time of slot `s` a
vote for a block they hold that is `X` or a descendant of `X`, and are more than half of the
validators whose votes `w` counts for its vote of slot `s + 1`; the honest proposer `p` of slot
`s + 1` put `B` on the wire at the start of slot `s + 1`, with its anchor `X` or an ancestor of `X`;
the honest voter `w` holds `B`, has every live lock on `B` or an ancestor of `B` after its
revocation, and sees `B` as a viable head; and, along the path from `X` to `B`'s parent past the
root of `w`'s fork choice, the two validators count alike on the children, agree on the viable
heads, and `p` holds every child that `w` finds eligible — then `w`'s vote of slot `s + 1` names
`B`.

Roots name blocks until `supportCutoff S s`: the proof takes as held only blocks delivered
before the support cutoff of slot `s` (Lemma 12 at slot `s`, at `p` and at `w`). -/
theorem lem20_goldfish_vote_names_honest_proposal (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s : ℕ) (Hs : Finset V) (H : V → Block V)
    (X B : Block V) (p w : V) (vote : GoldfishVote V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S s))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S s)
    -- the slot-`s` votes of `Hs` for `X`
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ Sched.adv (voteTime S (s + 1) : Int) ∧
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      H u ∈ (stateBefore x (voteTime S s) u).S.T ∧ X.AncestorEq (H u))
    -- the validators with a vote among those `w`'s slot-`(s + 1)` vote counts are fewer than
    -- twice `Hs`
    (hVoters : ∀ votes_w support_w : Finset (GoldfishVote V),
      CountedVotes S.C (stateBefore x (voteTime S (s + 1)) w).A
        (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) (s + 1) votes_w support_w →
      voters_count votes_w < 2 * Hs.card)
    -- the proposer `p` and the voter `w`
    (hp : ∀ t : ℕ, voteTime S s ≤ t → t ≤ supportCutoff S s →
      p ∈ Sched.awake (t : Int) ∧ p ∉ Sched.adv (t : Int))
    (hw : ∀ t : ℕ, voteTime S s ≤ t → t ≤ supportCutoff S s →
      w ∈ Sched.awake (t : Int) ∧ w ∉ Sched.adv (t : Int))
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    (hSend : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s + 1)) ∧
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent)
    -- `w` holds `B` before its vote
    (hBw : B ∈ (stateBefore x (voteTime S (s + 1)) w).S.T)
    -- the finality-gadget condition at `p`, on its state before `slotStart S (s + 1)`
    (hF3p : ∃ W ∈ (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).tree,
      W ∈ (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).viable_heads ∧ X.AncestorEq W)
    -- `p`'s anchor is `X` or an ancestor of `X`
    (hApX : (get_anchor (stateBefore x (slotStart S (s + 1)) p).A
      (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S)
      ((slotStart S (s + 1) : ℕ) : Int)).AncestorEq X)
    -- every live lock entry `w`'s revocation leaves is on `B` or an ancestor of `B`
    (hLocksW : ∀ A' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S (s + 1)) w).A
        ((voteTime S (s + 1) : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
        ((voteTime S (s + 1) : ℕ) : Int) (s + 1) = .ok A' →
      ∀ e ∈ A'.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
          ((voteTime S (s + 1) : ℕ) : Int) e = true → e.B.AncestorEq B)
    -- `B` is a viable head at `w`
    (hBViable : B ∈ (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).viable_heads)
    -- the two validators agree on the viable heads along the path from `X` to `B`'s parent, on
    -- the blocks of it that have the root of `w`'s fork choice as an ancestor (or are that root)
    (hViableAgree : ∀ Y : Block V, X.AncestorEq Y →
      (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).fc_root.AncestorEq Y →
      Y.AncestorEq B.parent →
      (Y ∈ (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).viable_heads ↔
        Y ∈ (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).viable_heads))
    -- the two validators count alike: the same score on every child of a block from `X` to
    -- `B`'s parent that has the root of `w`'s fork choice as an ancestor (or is that root), the
    -- same number of voters
    (hCount : ∀ votes_p support_p votes_w support_w : Finset (GoldfishVote V),
      ProposalCountedVotes (stateBefore x (slotStart S (s + 1)) p).A
        (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S) s votes_p support_p →
      CountedVotes S.C (stateBefore x (voteTime S (s + 1)) w).A
        (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) (s + 1) votes_w support_w →
      (∀ Y : Block V, X.AncestorEq Y →
        (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).fc_root.AncestorEq Y →
        Y.AncestorEq B.parent →
        ∀ D : Block V, D.parent? = some Y → ∃ n : ℕ,
          goldfish_score (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S) votes_p support_p s
            D = .ok n ∧
          goldfish_score (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) votes_w support_w s
            D = .ok n) ∧
      voters_count votes_p = voters_count votes_w)
    -- every child in `w`'s viable tree of a block from `X` to `B`'s parent that has the root of
    -- `w`'s fork choice as an ancestor (or is that root), other than `B`, that `w`'s eligibility
    -- test accepts, is in `p`'s viable tree
    (hChild : ∀ (vbt : Finset (Block V)) (votes_w support_w : Finset (GoldfishVote V)),
      voter_block_tree S.C (stateBefore x (voteTime S (s + 1)) w).A
        (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) (s + 1) = .ok vbt →
      CountedVotes S.C (stateBefore x (voteTime S (s + 1)) w).A
        (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) (s + 1) votes_w support_w →
      ∀ Y : Block V, X.AncestorEq Y →
        (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).fc_root.AncestorEq Y →
        Y.AncestorEq B.parent →
        ∀ D ∈ viable_tree (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) vbt,
          D.parent? = some Y → D ≠ B →
          goldfish_eligible S.C (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
            ((voteTime S (s + 1) : ℕ) : Int) votes_w support_w s D = .ok true →
          D ∈ viable_tree (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S)
            (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).tree) :
    vote.head = B.root :=
  GoldilocksCorrectness.Proofs.Executions.lem20_goldfish_vote_names_honest_proposal S Sched x GST
    s Hs H X B p w vote hDiv hMono hSync hCatch hRoots hParent hOwner hGST hHs hVoters hp
    hw hPropose hSend hBw hF3p hApX hLocksW hBViable hViableAgree hCount hChild

end GoldilocksCorrectness.Statements.Executions
