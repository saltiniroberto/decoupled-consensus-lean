module
public import GoldilocksCorrectness.Proofs.Executions.AsyncDeliveryBoundary

@[expose] public section

/-! a kit statement, new, no landed statement changes. Proved in
`GoldilocksCorrectness/Proofs/Executions/AsyncDeliveryBoundary.lean`.

- `lem12_honest_vote_delivered_by_until`: the honest votes of slot `s` reach a validator awake and
  honest for one delay from any time `t` at or after the vote time and `GST`, strictly before
  `t + Δ`, while `t + Δ` is at most the view freeze of `s`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ voteTime viewFreeze)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **Lemma 12 by a later delay, the honest votes of a slot reach a validator one delay after any
time.** Under the assumptions of Lemma 12 (every time is reached, corruption is permanent, blocks
and Goldfish votes are delivered within `Δ` after `GST`, a root names one block among what honest
validators hold by `t + Δ`, a block reaches a validator only once it holds the parent, nobody votes
in an honest validator's name): if `GST` is at most `t`; `t` is at or after the vote time of slot
`s`, and `t + Δ` is at most the view freeze of slot `s` and at most `t₃`; every `u ∈ Hs` is in the
slot-`s` committee, honest through `t₃`, put its slot-`s` vote for `H u` on the wire at the tick
of the vote time of slot `s`, and holds `H u` in its tree then; `w` is awake and honest at every
time from `t` to `t + Δ`; and `w`'s finalized block before `t₃` is `H u` or an ancestor of it —
then `w`'s AC state before `t₃` holds `u`'s vote for `H u` as `u`'s only slot-`s` vote, stamped and
resolved strictly before `t + Δ`, with `H u` in `w`'s frame tree.

Why: Lemma 12's proof with the delivery window `[t, t + Δ]`. The vote reaches `w` strictly before
`t + Δ`, so in slot `s` (`t + Δ` is at most the view freeze of `s`), and is admitted
(`vote_in_pool_before_add_delay_at`); `H u`, held by `u` before `t`, reaches `w` by then
(`mem_T_before_add_delay` at `t`); the stamps are before `t + Δ`, and `H u`'s slot is at most `s`,
so the vote resolves at the later of the two; `u` votes once (`unique_vote_of_owner`).

Lemma 12 (`lem12_honest_vote_delivered_until`, `Statements/Executions/DeliveryStatements.lean`) is
the instance `t := voteTime S s` (its conclusion `HeldEarlyVoteFor` is `HeldEarlyVoteAt` at the
support cutoff of `s`, `heldEarlyVoteFor_iff`); it is not re-derived.



The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s`: the slot of the votes; `t`: the
  start of the delivery window; `t₃`: the time `w`'s state is read before;
- `Hs`: the honest voters of slot `s`; `H`: the block each voter's vote is for; `w`: the
  validator the votes reach.

Roots name blocks until `t + Δ`: the proof takes `H u` as held by `w` at its delivery, before
`t + Δ`.

Read aloud: the honest votes of slot `s`, with their blocks, reach a validator awake and honest for
one delay from a time `t` at or after the vote time and at or after `GST`, strictly before `t + Δ`,
and it keeps them until `t₃`; each vote is its voter's only vote of the slot. -/
theorem lem12_honest_vote_delivered_by_until (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s t t₃ : ℕ) (Hs : Finset V) (H : V → Block V) (w : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (t + Δ S))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ t) (htv : voteTime S s ≤ t) (htf : t + Δ S ≤ viewFreeze S s) (ht₃ : t + Δ S ≤ t₃)
    -- every member of `Hs` is a member of the slot-`s` committee honest through `t₃` that put its
    -- slot-`s` vote for `H u` on the wire at the tick of the vote time of `s`, holding `H u` then
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ Sched.adv (t₃ : Int) ∧
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      H u ∈ (stateBefore x (voteTime S s) u).S.T)
    -- `w` is awake and honest from `t` to `t + Δ S`
    (hw : ∀ t' : ℕ, t ≤ t' → t' ≤ t + Δ S → w ∈ Sched.awake (t' : Int) ∧ w ∉ Sched.adv (t' : Int))
    -- `w`'s finalized block before `t₃` is `H u` or an ancestor of `H u`
    (hF : ∀ u ∈ Hs, (stateBefore x t₃ w).S.F.AncestorEq (H u)) :
    ∀ u ∈ Hs, HeldEarlyVoteAt (stateBefore x t₃ w).A (fg_to_ac (stateBefore x t₃ w).S)
      (((t + Δ S : ℕ) : Int)) s (H u) u :=
  GoldilocksCorrectness.Proofs.Executions.lem12_honest_vote_delivered_by_until S Sched x GST s t t₃
    Hs H w hDiv hMono hSync hCatch hRoots hParent hOwner hGST htv htf ht₃ hHs hw hF

end GoldilocksCorrectness.Statements.Executions
