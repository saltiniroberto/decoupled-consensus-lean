module
public import GoldilocksCorrectness.Statements.Executions.CountAgreementStatements
public import GoldilocksCorrectness.Statements.Executions.AsyncDeliveryStatements
public import GoldilocksCorrectness.Proofs.Executions.Lemma23UpTo

@[expose] public section

/-!
# `CountAgreementStatements.lean` with the delivery premises up to a bound

The theorems of `GoldilocksCorrectness/Statements/Executions/CountAgreementStatements.lean` that
name a delivery premise, restated with `SynchronyFromWakeUpTo` and `CatchUpOnWakeUpTo` at a bound
on the deadlines. The
bound of each twin is the latest ordinary deadline `max t GST + Δ` of a send its proof reads,
written in the twin's own parameters.

* `lem23_proposer_and_voter_count_alike`

No `axiom`, no `native_decide`, no `sorry`. The landed page is imported, never edited.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime viewFreeze)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Routines (CountedVotes ProposalCountedVotes)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **Lemma 23, an honest proposer and the next slot's honest voter count alike.** In an execution
where every time is reached, corruption is permanent, blocks and Goldfish votes are delivered
within `Δ` after `GST` (synchrony from the receiver's wake, and catch-up on wake),
a root names one block among what honest validators hold, and a block reaches a
validator only once it holds the parent: if `GST` is at most the vote time of slot `s`; `p` is awake
and honest at every time from the view freeze of slot `s` to the start `t₁` of slot `s + 1`, and
`w` at every time from `t₁` to the vote time `t₃` of slot `s + 1`; `p` put its block `B` on the
wire at its tick at `t₁`; and on `w`'s node state before `t₃`, `B` is in the frame tree and is the
only slot-`(s + 1)` block of the FG tree — then, for the sets `votes_p`, `support_p` `p`'s proposal
counts (`ProposalCountedVotes`) and the sets `votes_w`, `support_w` `w`'s vote counts
(`CountedVotes`), the Goldfish scores of every block `D` that has `p`'s finalized block before `t₁`
and `w`'s finalized block before `t₃` as ancestors (or is one of them) answer one number at both,
and the two voter counts are equal.

 `hOnly` is judgement J38's hypothesis, the
unforgeability of blocks.

 `p`'s awake window was narrowed from "from the start of slot `s`" to "from the view
freeze of slot `s`", and `w`'s from "from the start of slot `s`" to "from `t₁`", the windows the
proof uses (`w`'s honesty at the view freeze follows from its honesty at `t₁`, corruption being
permanent).

Why: by Lemma 19, `B`'s votes are `p`'s pool of slot `s` and its support votes those that resolve
at `p`; by `hOnly` the votes `w` counts as included in a slot-`(s + 1)` block are exactly those. A
vote `w` holds stamped before the view freeze was re-sent by `w` and reached `p` before `t₁`, so
it is in `p`'s pool, or `p` holds two votes of its validator. Hence the equivocators agree, the
participants agree, and the one counted vote of a validator that does not equivocate is the same
at both. A vote supports a block `D` only through a head block that is `D` or a descendant of
`D`; when `D` has both finalized blocks as ancestors, so does that head block, which, when one
validator resolves it, reaches the other within a delay and is in the other's frame tree, so the
vote resolves at both; roots name one block across the two honest trees, so the vote supports `D`
at both. The score of a block is the number of equivocators plus the number of its supporters, so
the scores of such a `D` agree.

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution; `GST`: the time from which the
  network is synchronous; `s`: the slot of the votes;
- `B`: the proposal of slot `s + 1`; `p`: its proposer; `w`: the voter of slot `s + 1`;
- `votes_p`, `support_p`: the sets `p`'s proposal counts; `votes_w`, `support_w`: the sets `w`'s
  vote counts.

Read aloud: after `GST`, an honest proposer and an honest voter of the next slot give every block
that descends from both their finalized blocks the same Goldfish score, and count the same voters,
when the voter holds the proposal and no other block of its slot.

Roots name blocks until `voteTime S (s + 1)`: the proof compares the blocks `w` holds before the
vote time of slot `s + 1` with those `p` holds before the start of slot `s + 1`, and takes
blocks as held by `w` one delay after the start of slot `s + 1`.

Restated with the delivery premises up to `voteTime S (s + 1)`: the votes and blocks `p` and `w` exchange around slot `s + 1` reach them by then. -/
theorem lem23_proposer_and_voter_count_alike_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s : ℕ) (B : Block V) (p w : V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (voteTime S (s + 1)))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (voteTime S (s + 1)))
    (hRoots : RootsNameBlocksUntil S Sched x (voteTime S (s + 1)))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hGST : GST ≤ voteTime S s)
    (hp : ∀ t : ℕ, viewFreeze S s ≤ t → t ≤ slotStart S (s + 1) →
      p ∈ Sched.awake (t : Int) ∧ p ∉ Sched.adv (t : Int))
    (hw : ∀ t : ℕ, slotStart S (s + 1) ≤ t → t ≤ voteTime S (s + 1) →
      w ∈ Sched.awake (t : Int) ∧ w ∉ Sched.adv (t : Int))
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    (hBw : B ∈ (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).tree)
    (hOnly : ∀ B' ∈ (stateBefore x (voteTime S (s + 1)) w).S.T, B'.slot = s + 1 → B' = B) :
    ∀ votes_p support_p votes_w support_w : Finset (GoldfishVote V),
      ProposalCountedVotes (stateBefore x (slotStart S (s + 1)) p).A
        (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S) s votes_p support_p →
      CountedVotes S.C (stateBefore x (voteTime S (s + 1)) w).A
        (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) (s + 1) votes_w support_w →
      (∀ D : Block V, (stateBefore x (slotStart S (s + 1)) p).S.F.AncestorEq D →
        (stateBefore x (voteTime S (s + 1)) w).S.F.AncestorEq D → ∃ n : ℕ,
          goldfish_score (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S) votes_p support_p s
            D = .ok n ∧
          goldfish_score (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) votes_w support_w s
            D = .ok n) ∧
      voters_count votes_p = voters_count votes_w :=
  GoldilocksCorrectness.Proofs.Executions.lem23_proposer_and_voter_count_alike_upTo S Sched x GST s B p
    w hDiv hMono hSync hCatch hRoots hParent hGST hp hw hPropose hBw hOnly

end GoldilocksCorrectness.Statements.Executions

