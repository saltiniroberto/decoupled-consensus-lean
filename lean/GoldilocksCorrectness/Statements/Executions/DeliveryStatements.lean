module
public import GoldilocksCorrectness.Proofs.Executions.Lemma12

@[expose] public section

/-!
# The delivery lemma

The audited statement of the delivery lemma, `lem12_honest_vote_delivered`, and its two
corollaries, each proved in `GoldilocksCorrectness/Proofs/Executions/Lemma12.lean`
. The conclusion is the definition `HeldEarlyVoteFor` of
`GoldilocksCorrectness/Statements/Executions/DeliveryDefs.lean`; the two corollaries make it the
input of `lem8b` (`EarlyVoteOnceFor`) and of `lem5` (`VotesOnceInPoolFor`). Last,
`delivered_before_of_honest_send_upTo`, the network's delivery within a delay on the delivery
premises restricted to the deadlines up to `t + Δ`, proved in
`GoldilocksCorrectness/Proofs/Executions/Network.lean`.
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
delivery, before the support cutoff of slot `s`. -/
theorem lem12_honest_vote_delivered (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s : ℕ) (Hs : Finset V) (H : V → Block V) (w : V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
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
  GoldilocksCorrectness.Proofs.Executions.lem12_honest_vote_delivered S Sched x GST s Hs H w hDiv
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
delivery, before the support cutoff of slot `s`, whatever `t₃` is. -/
theorem lem12_honest_vote_delivered_until (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s t₃ : ℕ) (Hs : Finset V) (H : V → Block V) (w : V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
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
  GoldilocksCorrectness.Proofs.Executions.lem12_honest_vote_delivered_until S Sched x GST s t₃ Hs
    H w hDiv hMono hSync hCatch hRoots hParent hOwner hGST ht₃ hHs hw hF

omit [Fintype V] [RootOrder] in
/-- **The delivery lemma's conclusion is what `lem8b` reads for a voter.** When `A` holds `u`'s
slot-`s` vote for `H_u` as `HeldEarlyVoteFor` says, `u` has exactly one slot-`s` vote in `A`'s
pool, its head is `H_u`'s root, and it resolves strictly before `C.t_ s + 2 · C.Δ`
(`EarlyVoteOnceFor`).

Why: the vote of `HeldEarlyVoteFor` is that vote; the stamp bound and `H_u ∈ Φ.tree` are not
needed.

The variables:
- `C`: the parameters; `A`: the AC state; `Φ`: the frame;
- `s`: the slot of the vote; `H_u`: the block the vote is for; `u`: the voter. -/
theorem heldEarlyVoteFor_earlyVoteOnceFor (C : Config) (A : ACState V) (Φ : Frame V) (s : Slot)
    (H_u : Block V) (u : V) (h : HeldEarlyVoteFor C A Φ s H_u u) :
    GoldilocksCorrectness.Statements.Routines.EarlyVoteOnceFor C A Φ s H_u u :=
  GoldilocksCorrectness.Proofs.Executions.heldEarlyVoteFor_earlyVoteOnceFor C A Φ s H_u u h

omit [Fintype V] [RootOrder] in
/-- **The delivery lemma's conclusion is what `lem5` reads for a voter.** When `A` holds `u`'s
slot-`s` vote for `H_u` as `HeldEarlyVoteFor` says, `u` has exactly one slot-`s` vote in `A`'s
pool, it resolves, and its head is the root of a block of `Φ.tree` that is `H_u` or a descendant of
`H_u` (`VotesOnceInPoolFor`, with `H_u` itself as that block).

Why: the vote of `HeldEarlyVoteFor` is that vote, its head is `H_u`'s root, and `H_u ∈ Φ.tree`.

The variables:
- `C`: the parameters; `A`: the AC state; `Φ`: the frame;
- `s`: the slot of the vote; `H_u`: the block the vote is for; `u`: the voter. -/
theorem heldEarlyVoteFor_votesOnceInPoolFor (C : Config) (A : ACState V) (Φ : Frame V)
    (s : Slot) (H_u : Block V) (u : V) (h : HeldEarlyVoteFor C A Φ s H_u u) :
    GoldilocksCorrectness.Statements.Routines.VotesOnceInPoolFor A Φ s H_u u :=
  GoldilocksCorrectness.Proofs.Executions.heldEarlyVoteFor_votesOnceInPoolFor C A Φ s H_u u h

/-- **Delivery within a delay, on the delivery premises up to the deadline.** A message of the
object class `ok` an honest validator put on the wire at the step `i`, at a time at most
`t ≥ GST`, is delivered to every validator `v` that is awake and outside the adversary set at
every time from `t` to `t + Δ`, at a step after `i` and at a time before `t + Δ`, when synchrony
and catch-up on wake hold for the sends and wakes whose ordinary deadline is at most `t + Δ`.

Why: if `v` was awake at every time from the time the message is on the wire through `t`,
synchrony delivers it before the deadline `max x[i + 1].time GST + Δ ≤ t + Δ`, counted from the
time the message is on the wire; otherwise `v` wakes, at the latest time `a` it was asleep plus
one, at most `t`, and catch-up on wake delivers it before `max (a + 1) GST + Δ ≤ t + Δ`. Both
deadlines are at most `t + Δ`, so the bounded premises suffice.

The variables:
- `x`: the execution; `Δ`: the delay bound; `GST`: the time from which the network is
  synchronous; `ok`: the class of objects the network assumptions promise about;
- `t`: the time; `i`: the step of the send; `v`: the receiver; `sm`: the signed message;
- `j`: the step of the delivery.

Read aloud: a message of the class `ok` an honest validator put on the wire at a time at most
`t ≥ GST` is delivered, before `t + Δ`, to every validator awake and honest throughout
`[t, t + Δ]`, when the network keeps its promises for the deadlines up to `t + Δ`. -/
theorem delivered_before_of_honest_send_upTo {S : Setup V} {Sched : Schedule V}
    (x : AtomicExec (protocol S) Sched) {Δ GST : ℕ} {ok : NamedObject V → Prop} {t : ℕ}
    (hsync : SynchronyFromWakeUpTo S Sched x Δ GST ok (t + Δ))
    (hcatch : CatchUpOnWakeUpTo S Sched x Δ GST ok (t + Δ))
    (hmono : Sched.MonotoneCorruption)
    {i : ℕ} {v : V} {sm : SignedMsg V (NamedObject V)}
    (hsend : HonestSendAt Sched x.toTrace i sm) (hok : ok sm.msg)
    (hit : x[i + 1].time ≤ t) (hGST : GST ≤ t)
    (hwin : ∀ t', t ≤ t' → t' ≤ t + Δ → v ∈ Sched.awake (t' : Int) ∧ v ∉ Sched.adv (t' : Int)) :
    ∃ j, i < j ∧ x.lbl j = AtomicAction.deliver v sm ∧ x[j].time < t + Δ :=
  GoldilocksCorrectness.Proofs.Executions.delivered_before_of_honest_send_upTo x hsync hcatch hmono
    hsend hok hit hGST hwin

end GoldilocksCorrectness.Statements.Executions
