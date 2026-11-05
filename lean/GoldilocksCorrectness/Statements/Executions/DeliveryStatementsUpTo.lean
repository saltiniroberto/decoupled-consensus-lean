module
public import GoldilocksCorrectness.Statements.Executions.DeliveryStatements
public import GoldilocksCorrectness.Statements.Executions.AsyncDeliveryStatements
public import GoldilocksCorrectness.Proofs.Executions.Lemma12UpTo

@[expose] public section

/-!
# `DeliveryStatements.lean` with the delivery premises up to a bound

The theorems of `GoldilocksCorrectness/Statements/Executions/DeliveryStatements.lean` that name a
delivery premise, restated with `SynchronyFromWakeUpTo` and `CatchUpOnWakeUpTo` at a bound on the
deadlines. The bound of
each twin is the latest ordinary deadline `max t GST + Δ` of a send its proof reads, written in
the twin's own parameters.

* `lem12_honest_vote_delivered`, `lem12_honest_vote_delivered_until`

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
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **Lemma 12, an honest early Goldfish vote reaches every awake honest validator.** In an
execution where every time is reached, corruption is permanent, blocks and Goldfish votes are
delivered within `Δ` after `GST` (synchrony from the receiver's wake, and catch-up on wake),
a root names one block among what honest validators hold, a block reaches a
validator only once it holds the parent, and nobody votes in an honest validator's name: if `GST`
is at most the vote time of slot `s`; every `u ∈ Hs` is in the slot-`s` committee, honest through
the vote time of slot `s + 1`, put its slot-`s` vote for `H u` on the wire at the tick of the vote
time of slot `s`, and holds `H u` in its tree then; `w` is awake and honest at every time from
slot `s`'s vote time to its support cutoff; and `w`'s finalized block before the vote time of
slot `s + 1` is `H u` or an ancestor of it — then `w`'s AC state before the vote time of slot
`s + 1` holds `u`'s vote for `H u` as `u`'s only slot-`s` vote, stamped and resolved strictly
before `C.t_ s + 2 · C.Δ`, with `H u` in `w`'s frame tree.





Why: the vote is on the wire at the vote time `t₁` of slot `s`, so synchrony, or catch-up on `w`'s
last wake, delivers it to `w` strictly before `t₁ + Δ`, the support cutoff; at the delivery `w`'s
clock is the delivery's time, in slot `s`, and `on_goldfish_vote` admits the vote unless `w`
already holds two slot-`s` votes of `u`, which cannot be, since every copy of a vote of `u` on the
wire descends from `u`'s own tick and a tick sends one vote. `H u` was put on the wire by `u`
before `t₁` and reaches `w` before the support cutoff too; `w` admits it, each test of
`block_admissible` passing from what `u`'s tree satisfies, from `hRoots` and `hParent`, and from
`w`'s finalized block being an ancestor of `H u`. Both stamps are the delivery times, strictly
before the support cutoff, and `H u`'s slot is at most `s`, so the vote resolves at the later of
the two.

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s`: the slot of the votes;
- `Hs`: the honest voters of slot `s`; `H`: the block each voter's vote is for; `w`: the
  validator the votes reach.

Roots name blocks until `supportCutoff S s`: the proof takes `H u` as held by `w` at its
delivery, before the support cutoff of slot `s`.

Restated with the delivery premises up to `supportCutoff S s`: the votes and blocks of slot `s` reach `w` by then. -/
theorem lem12_honest_vote_delivered_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s : ℕ) (Hs : Finset V) (H : V → Block V) (w : V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S s))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S s))
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S s))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S s)
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ Sched.adv (voteTime S (s + 1) : Int) ∧
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      H u ∈ (stateBefore x (voteTime S s) u).S.T)
    -- `w` is awake and honest from slot `s`'s vote time to its support cutoff
    (hw : ∀ t : ℕ, voteTime S s ≤ t → t ≤ supportCutoff S s →
      w ∈ Sched.awake (t : Int) ∧ w ∉ Sched.adv (t : Int))
    (hF : ∀ u ∈ Hs, (stateBefore x (voteTime S (s + 1)) w).S.F.AncestorEq (H u)) :
    ∀ u ∈ Hs, HeldEarlyVoteFor S.C (stateBefore x (voteTime S (s + 1)) w).A
      (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) s (H u) u :=
  GoldilocksCorrectness.Proofs.Executions.lem12_honest_vote_delivered_upTo S Sched x GST s Hs H w hDiv
    hMono hSync hCatch hRoots hParent hOwner hGST hHs hw hF

/-- **Lemma 12 at any later time, an honest early Goldfish vote stays with every awake honest
validator.** Lemma 12 with the vote time of slot `s + 1` replaced by any time `t₃` from the support
cutoff of slot `s` on. Under the assumptions of Lemma 12 (every time is reached, corruption is
permanent, blocks and Goldfish votes are delivered within `Δ` after `GST`,
a root names one block among what honest validators hold, a block reaches a validator only
once it holds the parent, nobody votes in an honest validator's name): if `GST` is at most the vote
time of slot `s`; `t₃` is the support cutoff of slot `s` or later; every `u ∈ Hs` is in the
slot-`s` committee, honest through `t₃`, put its slot-`s` vote for `H u` on the wire at the tick of
the vote time of slot `s`, and holds `H u` in its tree then; `w` is awake and honest at every time
from slot `s`'s vote time to its support cutoff; and `w`'s finalized block before `t₃` is `H u` or
an ancestor of it — then `w`'s AC state before `t₃` holds `u`'s vote for `H u` as `u`'s only
slot-`s` vote, stamped and resolved strictly before `C.t_ s + 2 · C.Δ`, with `H u` in `w`'s frame
tree.

 Lemma 12 is its instance at `t₃ := voteTime S (s + 1)`.

Why: as for Lemma 12. The vote and `H u` reach `w` strictly before the support cutoff of slot `s`,
and `w` keeps them from then to `t₃`; the vote time of slot `s + 1` entered Lemma 12's proof only as
a time at least that cutoff, up to which `u` is honest.

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s`: the slot of the votes;
- `t₃`: the time `w`'s state is read before;
- `Hs`: the honest voters of slot `s`; `H`: the block each voter's vote is for; `w`: the
  validator the votes reach.

Roots name blocks until `supportCutoff S s`: the proof takes `H u` as held by `w` at its
delivery, before the support cutoff of slot `s`, whatever `t₃` is.

Restated with the delivery premises up to `supportCutoff S s`: the votes and blocks of slot `s` reach `w` by then. -/
theorem lem12_honest_vote_delivered_until_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s t₃ : ℕ) (Hs : Finset V) (H : V → Block V) (w : V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S s))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S s))
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S s))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S s)
    (ht₃ : supportCutoff S s ≤ t₃)
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ Sched.adv (t₃ : Int) ∧
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      H u ∈ (stateBefore x (voteTime S s) u).S.T)
    -- `w` is awake and honest from slot `s`'s vote time to its support cutoff
    (hw : ∀ t : ℕ, voteTime S s ≤ t → t ≤ supportCutoff S s →
      w ∈ Sched.awake (t : Int) ∧ w ∉ Sched.adv (t : Int))
    (hF : ∀ u ∈ Hs, (stateBefore x t₃ w).S.F.AncestorEq (H u)) :
    ∀ u ∈ Hs, HeldEarlyVoteFor S.C (stateBefore x t₃ w).A (fg_to_ac (stateBefore x t₃ w).S) s
      (H u) u :=
  GoldilocksCorrectness.Proofs.Executions.lem12_honest_vote_delivered_until_upTo S Sched x GST s t₃ Hs
    H w hDiv hMono hSync hCatch hRoots hParent hOwner hGST ht₃ hHs hw hF

end GoldilocksCorrectness.Statements.Executions

