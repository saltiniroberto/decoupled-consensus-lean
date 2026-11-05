module
public import GoldilocksCorrectness.Proofs.Executions.PhaseKit

@[expose] public section

/-!
# The kit of the phase

The audited statements the round lemmas of the phase read, each proved in
`GoldilocksCorrectness/Proofs/Executions/PhaseKit.lean`:

- `vote_extends_own_root`: an honest Goldfish vote names a block its voter holds, on the chain of
  the voter's own fork-choice root;
- `only_block_of_unforgeability`: the only slot-`s` block a validator holds is the honest
  proposer's;
- `frame_has_viable_head`: every frame of a node state has a viable head;
- `lockBox_of_one_justification`: in box 2, every lock at `h_max − 1` is on the justified block;
- `counting_of_committee_majority`: the counting hypotheses of a round from a committee majority
  in a set of validators;
- `floor_le_of_delivery`: a validator awake and honest for one delay after another's reading has a
  `head_height_floor` value (the least chain-state height a viable block may have) at least the other's;
- `roundMembers_mono`, `chainInvFor_mono`, `honestChainExtends_mono`: the restrictions of the
  round's members and of the chain invariant;
- `committee_majority_of_committeeSleepiness`: the committee majority of a slot inside the slot's
  members, from committee sleepiness;
- `roundMembers_subset_honestActiveAt`: in the phase, the members of a slot are honest active at
  it, and the next slot's members are among them.


-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff dutyWindowStart)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Routines (CountedVotes BoxTwo)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **An honest vote extends its voter's root.** A Goldfish vote that `u`'s tick put on the wire
at the vote time of slot `s'` names the root of a block `H_u` that `u` holds before that time, and
`u`'s fork-choice root then is `H_u` or an ancestor of it.

Why: the vote names the end of the Goldfish fork choice from the anchor (Lemma 14); the end is the
anchor or a block of the viable tree of the voter's tree, and the anchor is the fork-choice root
or a descendant of it.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s'`: the slot; `u`: the voter;
  `vote`: the vote.



Read aloud: an honest Goldfish vote names a block its voter holds, on the chain of the voter's own
fork-choice root. -/
theorem vote_extends_own_root (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s' : ℕ) (u : V) (vote : GoldfishVote V)
    -- `u` put `vote` on the wire at its tick at the vote time of slot `s'`
    (hSend : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s') ∧
      (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) :
    ∃ H_u ∈ (stateBefore x (voteTime S s') u).S.T, vote.head = H_u.root ∧
      (get_fc_root (stateBefore x (voteTime S s') u).S).AncestorEq H_u :=
  GoldilocksCorrectness.Proofs.Executions.vote_extends_own_root S Sched x s' u vote hSend

/-- **The only block of a slot.** Under unforgeability, when `p` is the proposer of slot `s`,
honest at every time up to `t`, and its tick at the start of slot `s` put `B` on the wire, every
block of slot `s` that a validator `w` holds before `t` is `B`.

Why: `w` relayed the block, which names `p` as its proposer; unforgeability puts it on the wire
under `p`'s own signature, sent by `p`'s own tick, which sends a block only at the start of the
block's slot (Lemma 19); one tick runs at that time, and it sends one block.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `hU`: unforgeability; `s`: the slot;
  `t`: the time; `B`: the proposal; `B₁`: the held block; `p`: the proposer; `w`: the holder.



Read aloud: the only slot-`s` block a validator holds before `t` is the honest proposer's. -/
theorem only_block_of_unforgeability (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace) (s t : ℕ) (B B₁ : Block V)
    (p w : V)
    -- `p` is outside the adversary set at every time up to `t`
    (hp : HonestThroughTime Sched (t : Int) p)
    -- `p` is the proposer of slot `s`
    (hps : S.P.proposer s = p)
    -- `p`'s tick at the start of slot `s` put `B` on the wire
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    -- `w` holds `B₁` before `t`, and `B₁` is of slot `s`
    (hB₁ : B₁ ∈ (stateBefore x t w).S.T) (hslot : B₁.slot = s) :
    B₁ = B :=
  GoldilocksCorrectness.Proofs.Executions.only_block_of_unforgeability S Sched x hU s t B B₁ p w
    hp hps hPropose hB₁ hslot

/-- **Every frame has a viable head.** The frame `v`'s FG state before `t` gives the available
chain has a viable head.

Why: in box 3 the block that makes the state contested is one; in box 2 the justified block is one;
otherwise a block on the finalized block's chain at a chain-state height at least `h_max − 1` is
one, and the finality update keeps such a block at every step.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `v`: the validator.



Read aloud: every frame of a node state has a viable head. -/
theorem frame_has_viable_head (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (t : ℕ) (v : V) :
    ∃ W : Block V, W ∈ (fg_to_ac (stateBefore x t v).S).viable_heads :=
  GoldilocksCorrectness.Proofs.Executions.frame_has_viable_head S Sched x t v

/-- **The locks in box 2.** Under unforgeability, and when fewer than a third of the validators
have been in the adversary set up to `t`: when `p`'s FG state before `t` is in box 2 with the
justified block `J₀`, every lock `T'` that `v`'s record holds before `t` at `p`'s `h_max − 1` is
`J₀`'s root.

Why: the lock was written by an attestation of `v`'s tick whose finality pair is the justification
of a block `v` held, at that height; `p`'s justified block is the justification of a block `p`
holds, at the same height; two justification certificates at one height name one root (Lemma 76).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `hU`: unforgeability; `t`: the time;
  `v`: the validator whose record is read; `p`: the validator in box 2; `J₀`: its justified block;
  `T'`: the lock.



Read aloud: in box 2 at the justified height, every lock is on the justified block. -/
theorem lockBox_of_one_justification (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace) (t : ℕ) (v p : V)
    (J₀ : Block V) (T' : BlockId)
    -- fewer than a third of the validators have been in the adversary set up to `t`
    (hAdv : AdversaryFewerThanThirdUntil Sched (validator_count V) (t : Int))
    (hBox : BoxTwo (stateBefore x t p).S J₀)
    -- `v`'s record before `t` holds the lock `T'` at `p`'s `h_max − 1`
    (hLock : (stateBefore x t v).Λ.lock ((stateBefore x t p).S.h_max - 1) = some T') :
    T' = J₀.root :=
  GoldilocksCorrectness.Proofs.Executions.lockBox_of_one_justification S Sched x hU t v p J₀ T'
    hAdv hBox hLock

/-- **The counting hypotheses from a committee majority in `Hon`.** When more than half of the
committee of slot `s` is in `Hon`, the committee has at most twice its members in `Hon`, the
validators with a slot-`s` vote in any node state's pool are fewer than twice them, and so are the
validators of any set of slot-`s` votes a slot-`(s + 1)` vote counts. Lemma 88
(`lem88_counting_of_committeeSleepiness`, `Statements/Executions/SleepyStatements.lean`) is this
fact with the honest active validators of slot `s` for `Hon` and the majority from committee
sleepiness; its page is not edited.

Why: the pool's votes and the counted votes are from the committee of slot `s`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot; `t`: the time;
  `Hon`: the validators; `v`: the validator whose state is read.



Read aloud: a committee majority in `Hon` bounds the committee, the pool and the counted votes of
the slot by twice the committee's members in `Hon`. -/
theorem counting_of_committee_majority (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s t : ℕ) (Hon : Finset V) (v : V)
    -- more than half of the committee of slot `s` is in `Hon`
    (hMaj : (S.P.committee s).card < 2 * (S.P.committee s ∩ Hon).card) :
    (S.P.committee s).card ≤ 2 * (S.P.committee s ∩ Hon).card ∧
    voters_count ((stateBefore x t v).A.pool s) < 2 * (S.P.committee s ∩ Hon).card ∧
    (∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes S.C (stateBefore x t v).A (fg_to_ac (stateBefore x t v).S) (s + 1)
        votes support_votes →
      voters_count votes < 2 * (S.P.committee s ∩ Hon).card) :=
  GoldilocksCorrectness.Proofs.Executions.counting_of_committee_majority S Sched x s t Hon v hMaj

/-- **The `head_height_floor` values ordered by delivery.** Under unforgeability, roots naming blocks among what honest
validators hold, and fewer than a third of the validators in the adversary set up to `t + Δ`:
when `p` is honest at `t ≥ GST`, `w` is awake and honest at every time from `t` to `t + Δ`, and
`w`'s finalized block before `t + Δ` is an ancestor of `p`'s fork-choice root before `t`, then
`head_height_floor` at `w` before `t + Δ` is at least `head_height_floor` at `p` before `t`.

Why: a block at `p`'s `h_max` reaches `w`, or is at most the height of `w`'s finalized block
(Lemma 89a), so `p`'s `h_max` is at most `w`'s; when `p` is contested, the block that makes it so
reaches `w`, and either `w`'s `h_max` is greater, or `w` has the same justified block at the same
height (Lemma 76) and is contested by that block.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `t`: the time `p`'s state is read before; `p`, `w`: the two
  validators.



Read aloud: a validator awake and honest for one delay after another's reading, whose finalized
block is an ancestor of the other's fork-choice root, has a `head_height_floor` value at least the other's.

Roots name blocks until `t + Δ S`: the proof compares blocks `w` holds before `t + Δ S` with
blocks `p` holds before `t`. -/
theorem floor_le_of_delivery (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST t : ℕ) (p w : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (t + Δ S))
    (hParent : ParentHeldAtDelivery S Sched x) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    -- fewer than a third of the validators have been in the adversary set up to `t + Δ`
    (hAdv : AdversaryFewerThanThirdUntil Sched (validator_count V) ((t + Δ S : ℕ) : Int))
    -- `t` is from `GST` on
    (hGST : GST ≤ t)
    -- `p` is honest at `t`
    (hp : p ∉ Sched.adv (t : Int))
    -- `w` is awake and honest at every time from `t` to `t + Δ`
    (hw : ∀ t' : ℕ, t ≤ t' → t' ≤ t + Δ S → w ∈ Sched.awake (t' : Int) ∧ w ∉ Sched.adv (t' : Int))
    -- `w`'s finalized block before `t + Δ` is `p`'s fork-choice root before `t` or an ancestor of
    -- it
    (hF : (stateBefore x (t + Δ S) w).S.F.AncestorEq (get_fc_root (stateBefore x t p).S)) :
    head_height_floor (stateBefore x t p).S ≤ head_height_floor (stateBefore x (t + Δ S) w).S :=
  GoldilocksCorrectness.Proofs.Executions.floor_le_of_delivery S Sched x GST t p w hDiv hMono hSync
    hCatch hRoots hParent hU hAdv hGST hp hw hF

omit [RootOrder] in
/-- **The round's members shrink.** With permanent corruption, a later round's members are among
an earlier round's, and the validators honest at `tAwakeEnd` are among the members of a round
whose next honest round opening slot's support cutoff is at most `tAwakeEnd`.

Why: the members are read at the support cutoff of the next opening's slot, and a validator in the
adversary set stays in it.

The variables:
- `S`: the setup; `Sched`: the schedule; `s'' ≤ s'''`: the two slots; `tAwakeEnd`: the time.



Read aloud: a later round's members are among an earlier round's, and the phase set is among every
round's. -/
theorem roundMembers_mono (S : Setup V) (Sched : Schedule V) (s'' s''' tAwakeEnd : ℕ)
    (hMono : Sched.MonotoneCorruption)
    -- the earlier slot is at most the later one
    (h : s'' ≤ s''')
    -- the support cutoff of the later slot is at most `tAwakeEnd`
    (hEnd : supportCutoff S s''' ≤ tAwakeEnd) :
    roundMembers S Sched s''' ⊆ roundMembers S Sched s'' ∧
      Finset.univ \ Sched.adv (tAwakeEnd : Int) ⊆ roundMembers S Sched s''' :=
  GoldilocksCorrectness.Proofs.Executions.roundMembers_mono S Sched s'' s''' tAwakeEnd hMono h hEnd

/-- **The chain invariant restricts.** `ChainInvFor` at a set of members holds at every subset of
it.

Why: each clause is a statement about each member.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `Hon' ⊆ Hon`: the two sets;
  `𝓒`: the family; `s'`: the slot.



Read aloud: the chain invariant restricts to a subset of the members. -/
theorem chainInvFor_mono (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (Hon Hon' : Finset V) (𝓒 : Block V → Prop) (s' : ℕ)
    -- `Hon'` is a subset of `Hon`
    (hSub : Hon' ⊆ Hon) (hInv : ChainInvFor S Sched x Hon 𝓒 s') :
    ChainInvFor S Sched x Hon' 𝓒 s' :=
  GoldilocksCorrectness.Proofs.Executions.chainInvFor_mono S Sched x Hon Hon' 𝓒 s' hSub hInv

/-- **`HonestChainExtends` restricts.** `HonestChainExtends` at a set of members holds at every
subset of it.

Why: each clause is a statement about each member.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `Hon' ⊆ Hon`: the two sets;
  `B`: the block; `s'`: the slot.



Read aloud: `HonestChainExtends` restricts to a subset of the members. -/
theorem honestChainExtends_mono (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (Hon Hon' : Finset V) (B : Block V) (s' : ℕ)
    -- `Hon'` is a subset of `Hon`
    (hSub : Hon' ⊆ Hon) (hInv : HonestChainExtends S Sched x Hon B s') :
    HonestChainExtends S Sched x Hon' B s' :=
  GoldilocksCorrectness.Proofs.Executions.honestChainExtends_mono S Sched x Hon Hon' B s' hSub
    hInv

omit [RootOrder] in
/-- **The committee majority from committee sleepiness.** When committee sleepiness holds from
`anchor` and slot `s + 1` starts at or after `anchor`, more than half of the committee of slot `s`
is among the validators honest at the support cutoff of slot `s + 1`, the members
`roundMembers S Sched (s + 1)`. This is the hypothesis `hMaj` of `counting_of_committee_majority`
with `Hon := roundMembers S Sched (s + 1)`: the one committee premise gives, at every slot it
constrains, the counting of that slot inside the slot's member set.

Why: committee sleepiness at slot `s + 1` makes the members of the committee of slot `s` in
`honestActiveAt S Sched s` more than the rest of that committee, so more than half of it; and
`honestActiveAt S Sched s` is inside `roundMembers S Sched (s + 1)`, both being outside the
adversary set at the support cutoff of slot `s + 1`.

The variables:
- `S`: the setup; `Sched`: the schedule; `anchor`: the time from which committee sleepiness
  holds; `s`: the slot.



Read aloud: from committee sleepiness, the committee of slot `s` has a majority among the
validators honest at the update of slot `s`. -/
theorem committee_majority_of_committeeSleepiness (S : Setup V) (Sched : Schedule V)
    (anchor s : ℕ)
    (hSleepK : CommitteeSleepiness S Sched anchor)
    -- slot `s + 1` starts at or after `anchor`
    (hs : anchor ≤ slotStart S (s + 1)) :
    (S.P.committee s).card < 2 * (S.P.committee s ∩ roundMembers S Sched (s + 1)).card :=
  GoldilocksCorrectness.Proofs.Executions.committee_majority_of_committeeSleepiness S Sched anchor
    s hSleepK hs

omit [RootOrder] in
/-- **The members of a slot are honest active.** In the phase, at a slot `s` whose duty window
starts at or after `tGAT` and whose update runs by `tAwakeEnd`, every validator honest at the
support cutoff of slot `s + 1` is in `honestActiveAt S Sched s`, and every validator honest at the
support cutoff of slot `s + 2` is honest at the support cutoff of slot `s + 1`.

Why: a validator honest at the support cutoff of slot `s + 1` is honest at every earlier time
(permanent corruption), so awake at every time from `dutyWindowStart S s` to that cutoff, all in
the interval from `tGAT` to `tAwakeEnd`; and a validator in the adversary set at the support
cutoff of slot `s + 1` stays in it at the later support cutoff of slot `s + 2`.

The variables:
- `S`: the setup; `Sched`: the schedule; `tGAT`, `tAwakeEnd`: the ends of the interval in which
  every honest validator is awake; `s`: the slot.



Read aloud: in the phase, every validator honest at the slot's update is awake through the slot's
duties and honest at its update, and the next slot's members are among this slot's. -/
theorem roundMembers_subset_honestActiveAt (S : Setup V) (Sched : Schedule V)
    (tGAT tAwakeEnd s : ℕ)
    (hMono : Sched.MonotoneCorruption)
    -- every validator honest at a time from `tGAT` to `tAwakeEnd` is awake then
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ v : V, v ∉ Sched.adv (t : Int) → v ∈ Sched.awake (t : Int))
    -- the duty window of slot `s` starts at or after `tGAT`
    (hsw : tGAT ≤ dutyWindowStart S s)
    -- the support cutoff of slot `s + 1` is at most `tAwakeEnd`
    (hEnd : supportCutoff S (s + 1) ≤ tAwakeEnd) :
    roundMembers S Sched (s + 1) ⊆ honestActiveAt S Sched s ∧
    roundMembers S Sched (s + 2) ⊆ roundMembers S Sched (s + 1) :=
  GoldilocksCorrectness.Proofs.Executions.roundMembers_subset_honestActiveAt S Sched tGAT tAwakeEnd
    s hMono hAwake hsw hEnd

end GoldilocksCorrectness.Statements.Executions
