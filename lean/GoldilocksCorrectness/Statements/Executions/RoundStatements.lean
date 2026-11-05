module
public import GoldilocksCorrectness.Proofs.Executions.RoundBoxes
public import GoldilocksCorrectness.Statements.Executions.BoxStatements

@[expose] public section

/-!
# The height advances in a round

The audited statements of Lemma 80, `lem80_round_height_advances_frame`: in a round whose first
slot has an honest proposal, the next honest proposal at a slot `s''` before whose start the
round's attestations are delivered is on that proposal's chain and raises the height or carries the progress quorum, over frame shapes (proved in
`GoldilocksCorrectness/Proofs/Executions/Lemma80.lean`); of its form over per-slot member sets
with the frames read at the first slot's three reading points,
`lem80wq_round_height_advances_steps` (Lemma 80 is its instance); of what each box supplies to Lemma 80,
`lem80_boxOne_hypotheses`, `lem80_boxTwo_hypotheses`, `lem80_boxThree_hypotheses`; of its three
corollaries `lem80_boxOne`, `lem80_boxTwo`, `lem80_boxThree`; and of the three box corollaries
of `lem80wq_round_height_advances_steps`, `lem80wq_boxOne`, `lem80wq_boxTwo`, `lem80wq_boxThree` (proved in
`GoldilocksCorrectness/Proofs/Executions/RoundBoxes.lean`).


-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ Δ_F slotStart voteTime supportCutoff
  dutyWindowStart)

open GoldilocksCorrectness.Statements.Routines (chainStateOf)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Routines (expireLocks CountedVotes ProposalCountedVotes
  FrameShape BoxOne BoxTwo BoxThree)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-! ## Lemma 80 over per-slot member sets -/

/-- **Lemma 80 over per-slot member sets, with `q`'s fork choice before its proposal.** Write
`s = r · R` for the first slot of round `r`, `B` for the honest proposal of slot `s` by `p`, `H`
for the height of `B`'s chain state and `T` for the root of its `T_h`, `a` for the action time (the
support cutoff of slot `s + 1`), and `s''` for a slot whose start is at least `Δ_F` after `a`
(`hs''`: an attestation sent at `a` is delivered before slot `s''` starts) and whose proposer `q`
puts `B'` on the wire at its start. In an execution with the eight execution assumptions and attestations
delivered within `Δ_F` after `GST`: if the member sets `Hon s'` shrink from slot to slot and each
member of `Hon s'` is awake and honest from the duty window's start of slot `s'` to the support
cutoff of slot `s' + 1` (not past the start of slot `s''`); `p` is awake and honest from the vote
time of slot `s − 1` to the start of slot `s`; the slot `s − 1` is as Lemma 59 reads it; the honest
voters `Hs s'` of every slot of the round are in `Hon s'` and outnumber half the voters its members
count; the frames are read at three points — `p`'s before the start of slot `s` (root `ρp`,
`head_height_floor` `φ`), each member's before the vote time of slot `s` (root on `B`'s parent's
chain, `head_height_floor` between `φ` and the height of `B`'s parent) and before `a` (root on
`B`'s chain, `head_height_floor` at most `H`); after `a`, `StepFrameAt` relative to `B` holds at the
members of `Hon (s' + 1)` for every slot `s'` with `s' + 3 ≤ s''`, and the voter's fork choice of
slot `s'' − 1` at the members of `Hon (s'' − 1)`; `Q ⊆ Hon s` is a quorum whose every member, before
`a`, has its cache `h_j` less than `H`, or no lock at `H`, or its lock at `H` on `T`; `q` is a
member of `Hon (s'' − 1)` whose fork-choice root before the start of slot `s''` is compatible with
`B` and, when it is `B` or an ancestor of `B`, has a viable head on `B`'s chain — then `B'` is on
`B`'s chain, and `B'`'s chain state has a height greater than `H`, or the height `H` with `Q` in
its progress set and `B'`'s slot less than `δt` after `T_h`'s; and when no member of `Q` had sent
anything at `H` before `a`, `B'`'s height is greater than `H`, and its justified block is `B`'s
`T_h` when `B'`'s parent is still at `H`.

Why: the first slot as in Lemma 80, with Lemma 59 for a proposer's `head_height_floor` at most the
voter's and every member's own update making `B` fast; the slot invariant restricted to `B` carried
from each slot's set to the next (Lemma 79 over two sets); the quorum's attestations reach `q`,
awake and honest from the duty window's start of slot `s` as a member of every set; `q`'s walk
passes `B`; Lemma 53 concludes.

This is Lemma 80's form of record over per-slot member sets. It takes `q`'s fork choice before the
start of slot `s''` as the hypothesis `hFrameQ`, since no other hypothesis reads `q`'s fork choice
at that time; at the last slot it takes the voter's fork choice of slot `s'' − 1` (`hStepLast`) and
not the whole of `StepFrameAt`, whose third conjunct (`q`'s finalized block before the support
cutoff of slot `s''`) the proof does not read.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the network
  is synchronous; `r`: the round; `s`: its first slot; `s''`: the slot of `q`'s proposal;
- `Hon s'`: the member set of slot `s'`; `Q`: the quorum; `Hs s'`: the honest voters of slot `s'`;
  `H`: the block each voter of slot `s − 1` votes for; `X`: the block those votes extend;
- `B`: the round's proposal; `B'`: `q`'s proposal; `p`, `q`: their proposers;
- `φ`, `ρp`: the `head_height_floor` and the root of `p`'s frame before the start of slot `s`;
  `φw w`, `ρw w`: those of member `w`'s frame before the vote time of slot `s`; `φv v`, `ρv v`:
  those of member `v`'s frame before `a`.

Read aloud: the round theorem asks of each slot's committee majority honesty through its own
slot's update only, reads the frames of the first slot at its three reading points, the chain's
step conditions after the action time, and the next proposer's fork choice at its proposal; then
the next honest proposal is on the round's proposal's chain with the height risen or the progress
quorum on chain.




Roots name blocks until `supportCutoff S (s'' - 1)`: `round_proposal_extends`, which the proof
calls at the slot `s'' - 2`, takes blocks as held up to the support cutoff of slot `s'' - 1`;
the base and the invariant through the round read earlier. -/
theorem lem80wq_round_height_advances_steps (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched)
    (GST r s s'' : ℕ) (Hon : ℕ → Finset V) (Q : Finset V) (Hs : ℕ → Finset V)
    (H : V → Block V) (X B B' : Block V) (p q : V) (φ : Height) (φw φv : V → Height)
    (ρp : Block V) (ρw ρv : V → Block V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s'' - 1)))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    -- attestations are delivered within `Δ_F S` after `GST`
    (hSyncF : SynchronyFromWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hCatchF : CatchUpOnWake Sched x.toTrace (Δ_F S) GST fgObject)
    -- `s` is the first slot of round `r`, not the first slot of all; an attestation sent at
    -- the action time of slot `s` is delivered, within `Δ_F S`, before slot `s''` starts
    (hs : s = r * S.C.R) (hs1 : 1 ≤ s) (hs'' : supportCutoff S (s + 1) + Δ_F S ≤ slotStart S s'')
    -- the network is synchronous from the vote time of slot `s − 1`
    (hGST : GST ≤ voteTime S (s - 1))
    -- the member sets shrink from one slot to the next
    (hHonMono : ∀ s', s ≤ s' → s' + 1 < s'' → Hon (s' + 1) ⊆ Hon s')
    -- the members of slot `s'` are awake and honest from the duty window's start of slot `s'` to
    -- the support cutoff of slot `s' + 1`, and not past the start of slot `s''`
    (hHon : ∀ s', s ≤ s' → s' < s'' → ∀ v ∈ Hon s', ∀ t : ℕ,
      dutyWindowStart S s' ≤ t → t ≤ supportCutoff S (s' + 1) → t ≤ slotStart S s'' →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    -- the proposer: awake and honest from the vote time of slot `s − 1` to the start of slot `s`
    (hp : ∀ t : ℕ, voteTime S (s - 1) ≤ t → t ≤ slotStart S s →
      p ∈ Sched.awake (t : Int) ∧ p ∉ Sched.adv (t : Int))
    -- `p` put `B` on the wire at its tick at the start of slot `s`
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    -- the honest voters of slot `s − 1` vote for blocks on `X`'s chain, honest at the vote time
    -- of slot `s`
    (hHsPrev : ∀ u ∈ Hs (s - 1), u ∈ S.P.committee (s - 1) ∧
      u ∉ Sched.adv (voteTime S s : Int) ∧
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s - 1)) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u (s - 1) (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      H u ∈ (stateBefore x (voteTime S (s - 1)) u).S.T ∧ X.AncestorEq (H u))
    -- at every member of `Hon s`, the voters its vote of slot `s` counts are fewer than twice
    -- `Hs (s − 1)`
    (hVotersPrev : ∀ w ∈ Hon s, ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes S.C (stateBefore x (voteTime S s) w).A
        (fg_to_ac (stateBefore x (voteTime S s) w).S) s votes support_votes →
      voters_count votes < 2 * (Hs (s - 1)).card)
    -- `p`'s anchor is `X` or an ancestor of `X`
    (hApX : (get_anchor (stateBefore x (slotStart S s) p).A
      (fg_to_ac (stateBefore x (slotStart S s) p).S) ((slotStart S s : ℕ) : Int)).AncestorEq X)
    -- every live lock a member's revocation of slot `s` leaves is on `B`'s parent's chain
    (hLocksW : ∀ w ∈ Hon s, ∀ A' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S s) w).A
        ((voteTime S s : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S s) w).S)
        ((voteTime S s : ℕ) : Int) s = .ok A' →
      ∀ e ∈ A'.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S s) w).S) ((voteTime S s : ℕ) : Int) e =
          true → e.B.AncestorEq B.parent)
    -- `B` is the only slot-`s` block a member holds at the vote time; its root is new to `p`
    (hOnly : ∀ w ∈ Hon s, ∀ B₁ ∈ (stateBefore x (voteTime S s) w).S.T, B₁.slot = s → B₁ = B)
    (hRootNew : ∀ B₁ ∈ (stateBefore x (slotStart S s) p).S.T, B₁.root ≠ B.root)
    -- the honest voters of slot `s'` are members of `Hon s'` and of the slot's committee
    (hHs : ∀ s', s ≤ s' → s' < s'' → ∀ u ∈ Hs s', u ∈ Hon s' ∧ u ∈ S.P.committee s' ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s' ∧
        ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s') ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x[i + 1].sent - x[i].sent)
    -- the counts of slot `s'`, read at the members of `Hon s'`: the voters counted by a vote of
    -- slot `s' + 1` and the slot-`s'` voters of the pool before the support cutoff of slot
    -- `s' + 1` are fewer than twice `Hs s'`
    (hVoters : ∀ s', s ≤ s' → s' < s'' → ∀ v ∈ Hon s',
      (∀ votes support_votes : Finset (GoldfishVote V),
        CountedVotes S.C (stateBefore x (voteTime S (s' + 1)) v).A
          (fg_to_ac (stateBefore x (voteTime S (s' + 1)) v).S) (s' + 1) votes support_votes →
        voters_count votes < 2 * (Hs s').card) ∧
      voters_count ((stateBefore x (supportCutoff S (s' + 1)) v).A.pool s') < 2 * (Hs s').card)
    -- the slot-`(s'' − 1)` voters `q`'s proposal counts are fewer than twice `Hs (s'' − 1)`
    (hVotersQ : ∀ votes support_votes : Finset (GoldfishVote V),
      ProposalCountedVotes (stateBefore x (slotStart S s'') q).A
        (fg_to_ac (stateBefore x (slotStart S s'') q).S) (s'' - 1) votes support_votes →
      voters_count votes < 2 * (Hs (s'' - 1)).card)
    -- the slot-`s` committee is at most twice `Hs s`
    (hHalf : (S.P.committee s).card ≤ 2 * (Hs s).card)
    -- the frames at the three reading points of slot `s`: `p`'s before the start of slot `s`,
    -- each member's before the vote time of slot `s` and before the action time `a`, with their
    -- roots and `head_height_floor` values
    (hShapeP : FrameShape (stateBefore x (slotStart S s) p).S ρp φ)
    (hShapeW : ∀ w ∈ Hon s, FrameShape (stateBefore x (voteTime S s) w).S (ρw w) (φw w))
    (hShapeV : ∀ v ∈ Hon s,
      FrameShape (stateBefore x (supportCutoff S (s + 1)) v).S (ρv v) (φv v))
    -- each member's `head_height_floor` before the vote time is at least the proposer's and at
    -- most the chain-state height of `B`'s parent; before `a`, at most that of `B`
    (hFloorW : ∀ w ∈ Hon s, φ ≤ φw w ∧ φw w ≤ (chainStateOf S.C B.parent).h)
    (hFloorV : ∀ v ∈ Hon s, φv v ≤ (chainStateOf S.C B).h)
    -- the roots: before the vote time on `B`'s parent's chain, before `a` on `B`'s chain
    (hRootW : ∀ w ∈ Hon s, (ρw w).AncestorEq B.parent)
    (hRootAr : ∀ v ∈ Hon s, (ρv v).AncestorEq B)
    -- some block of `p`'s tree, on `X`'s and `ρp`'s chains, reaches `φ`
    (hHeadP : ∃ W ∈ (stateBefore x (slotStart S s) p).S.T,
      X.AncestorEq W ∧ ρp.AncestorEq W ∧ φ ≤ (chainStateOf S.C W).h)
    -- after the action time, at the members of the next slot: `StepFrameAt` relative to `B` for
    -- every slot `s'` with `s' + 3 ≤ s''`; for the last slot `s'' − 1`, the voter's fork choice
    -- before its vote time (the first two conjuncts of `StepFrameAt S Sched x B (s'' − 2) w`)
    (hStep : ∀ s', s ≤ s' → s' + 3 ≤ s'' → ∀ w ∈ Hon (s' + 1), StepFrameAt S Sched x B s' w)
    (hStepLast : ∀ w ∈ Hon (s'' - 1),
      (fg_to_ac (stateBefore x (voteTime S (s'' - 1)) w).S).fc_root.compatible B = true ∧
      ((fg_to_ac (stateBefore x (voteTime S (s'' - 1)) w).S).fc_root.AncestorEq B →
        ∀ tree : Finset (Block V),
          voter_block_tree S.C (stateBefore x (voteTime S (s'' - 1)) w).A
            (fg_to_ac (stateBefore x (voteTime S (s'' - 1)) w).S) (s'' - 1) = .ok tree →
          ∃ W ∈ tree, W ∈ (fg_to_ac (stateBefore x (voteTime S (s'' - 1)) w).S).viable_heads ∧
            B.AncestorEq W))
    -- the quorum attests at `a`, inside slot `s`'s active window
    (hQ : Q ⊆ Hon s) (hQuorum : quorum V ≤ Q.card)
    -- the record of every member of `Q` before `a`: the cache `h_j` is less than `H`, or no lock
    -- at `H`, or the lock at `H` is `T`
    (hLockBox : ∀ v ∈ Q,
      (stateBefore x (supportCutoff S (s + 1)) v).S.h_j < (chainStateOf S.C B).h ∨
      (stateBefore x (supportCutoff S (s + 1)) v).Λ.lock (chainStateOf S.C B).h = none ∨
      (stateBefore x (supportCutoff S (s + 1)) v).Λ.lock (chainStateOf S.C B).h =
        some (chainStateOf S.C B).T_h.root)
    -- the next proposer is a member of the last slot's set
    (hq : q ∈ Hon (s'' - 1))
    -- `q`'s fork-choice root before the start of slot `s''` is compatible with `B`, and when it
    -- is `B` or an ancestor of `B`, a block of `q`'s frame tree that is `B` or a descendant of `B`
    -- is a viable head
    (hFrameQ : (fg_to_ac (stateBefore x (slotStart S s'') q).S).fc_root.compatible B = true ∧
      ((fg_to_ac (stateBefore x (slotStart S s'') q).S).fc_root.AncestorEq B →
        ∃ W ∈ (fg_to_ac (stateBefore x (slotStart S s'') q).S).tree,
          W ∈ (fg_to_ac (stateBefore x (slotStart S s'') q).S).viable_heads ∧ B.AncestorEq W))
    -- `q` put `B'` on the wire at its tick at the start of slot `s''`
    (hPropose' : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s'') ∧
      (⟨q, NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) :
    B.AncestorEq B' ∧
    ((chainStateOf S.C B).h + 1 ≤ (chainStateOf S.C B').h ∨
      ((chainStateOf S.C B').h = (chainStateOf S.C B).h ∧
        Q ⊆ (chainStateOf S.C B').progress ∧
        B'.slot < (chainStateOf S.C B).T_h.slot + S.C.δt)) ∧
    ((∀ u ∈ Q, ∀ b ∈ (stateBefore x (supportCutoff S (s + 1)) u).Λ.sent,
        b.h ≠ (chainStateOf S.C B).h) →
      (chainStateOf S.C B).h + 1 ≤ (chainStateOf S.C B').h ∧
        ((chainStateOf S.C B'.parent).h = (chainStateOf S.C B).h →
          (chainStateOf S.C B').J = (chainStateOf S.C B).T_h)) :=
  GoldilocksCorrectness.Proofs.Executions.lem80wq_round_height_advances_steps S Sched x GST r s s''
    Hon Q Hs H X B B' p q φ φw φv ρp ρw ρv hDiv hMono hSync hCatch hRoots hParent hOwner
    hSyncF hCatchF hs hs1 hs'' hGST hHonMono hHon hp hPropose hHsPrev hVotersPrev hApX hLocksW
    hOnly hRootNew hHs hVoters hVotersQ hHalf hShapeP hShapeW hShapeV hFloorW hFloorV hRootW
    hRootAr hHeadP hStep hStepLast hQ hQuorum hLockBox hq hFrameQ hPropose'

/-! ## Lemma 80 -/

/-- **Lemma 80, the height advances in a round, over frame shapes.** Write `s = r · R` for the
first slot of round `r`, `B` for the honest proposal of slot `s`, `H` for the height of `B`'s chain
state and `T` for the root of its `T_h`, `a` for the action time of the round (the support cutoff
of slot `s + 1`), and `s''` for a slot whose start is at least `Δ_F` after `a` (`hs''`: an
attestation sent at `a` is delivered before slot `s''` starts) and whose honest proposer `q` puts
`B'` on the wire at its start. In an execution with the eight execution assumptions and attestations delivered
within `Δ_F` after `GST`: if the members of `Hon` are awake and honest from the duty window's start
of slot `s` to the start of slot `s''`; the slot `s − 1` is as Lemma 24 reads it; the honest voters
`Hs s'` of every slot from `s` to `s'' − 1` are members, each voting at its slot, and outnumber
half the voters every member counts; every member's frame over the window has the root `ρ v t`
and `head_height_floor` (the least chain-state height a viable block may have) equal to `φ`, the root being `B`'s parent or an ancestor of it at the vote time of slot `s`,
`B` or an ancestor of `B` at `a`, and compatible with `B` afterwards; some block of `p`'s tree on
`X`'s and its root's chains reaches `head_height_floor`, and `B`'s parent is in `p`'s viable tree; `Q ⊆ Hon`
is a quorum whose every member, before `a`, has its cache `h_j` less than `H`, or no lock at `H`, or
its lock at `H` on `T` — then `B'` is on `B`'s chain, and `B'`'s chain state has a height greater
than `H`, or the height `H` with `Q` in its progress set and `B'`'s slot less than `δt` after
`T_h`'s; and when no member of `Q` had sent anything at `H` before `a`, `B'`'s height is greater
than `H`, and its justified block is `B`'s `T_h` when `B'`'s parent is still at `H`.

`Hon` is not an arbitrary set: the hypotheses pin it down. Every member is awake and honest from
the duty window of slot `s` to the start of slot `s''`; it contains the honest voters `Hs s'` of
every slot of the round, the quorum `Q`, and the proposers `p` and `q`; the counting, frame and
root conditions hold at every member. The natural choice is the honest validators awake throughout
that window, for which the first, second and fourth requirements hold by construction and the third
becomes "at least two thirds of the validators are honest and awake throughout the window".

Why: every member votes `B` at slot `s` (Lemma 59), confirms it, makes it fast and keeps no lock off
its chain (Lemmas 60, 27, 42); the slot invariant restricted to `B` carries to slot `s'' − 1`
(Lemma 79); every member of `Q` attests for `(H, T)` at `a` or had (Lemma 61), and the attestation
reaches `q`, a member and so awake and honest from the duty window's start of slot `s`, by the
start of slot `s''`: by synchrony when `q` was awake since the send, by the catch-up on `q`'s last
wake otherwise; `q`'s walk passes `B`; Lemma 53 concludes.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the network
  is synchronous; `r`: the round; `s`: its first slot; `s''`: the slot of `q`'s proposal;
- `Hon`: the members; `Q`: the quorum; `Hs`: the honest voters of each slot; `H`: the block each
  voter of slot `s − 1` votes for; `X`: the block those votes extend;
- `B`: the round's proposal; `B'`: `q`'s proposal; `p`, `q`: their proposers;
- `φ`: the value of `head_height_floor` at the members' frames; `ρ v t`: the root of `v`'s frame before `t`.

Read aloud: inside a window where every member's frame has one `head_height_floor` value and a root on `B`'s chain, the
round's honest proposal is voted, confirmed and attested by every member, and the next honest
proposal, at a slot the round's attestations reach in time, is on its chain with the height risen or the progress quorum on chain.




Roots name blocks until `supportCutoff S (s'' - 1)`: `lem80wq_round_height_advances_steps`,
which the proof calls, takes blocks as held up to the support cutoff of slot `s'' - 1`. -/
theorem lem80_round_height_advances_frame (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched)
    (GST r s s'' : ℕ) (Hon Q : Finset V) (Hs : ℕ → Finset V) (H : V → Block V)
    (X B B' : Block V) (p q : V) (φ : Height) (ρ : V → ℕ → Block V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s'' - 1)))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    -- attestations are delivered within `Δ_F S` after `GST`
    (hSyncF : SynchronyFromWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hCatchF : CatchUpOnWake Sched x.toTrace (Δ_F S) GST fgObject)
    -- `s` is the first slot of round `r`, not the first slot of all; an attestation sent at
    -- the action time of slot `s` is delivered, within `Δ_F S`, before slot `s''` starts
    (hs : s = r * S.C.R)
    (hs1 : 1 ≤ s)
    (hs'' : supportCutoff S (s + 1) + Δ_F S ≤ slotStart S s'')
    -- the network is synchronous from the vote time of slot `s − 1`
    (hGST : GST ≤ voteTime S (s - 1))
    -- the members are awake and honest from the duty window's start of slot `s` to the start of
    -- slot `s''`
    (hHon : ∀ v ∈ Hon, ∀ t : ℕ, dutyWindowStart S s ≤ t → t ≤ slotStart S s'' →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    -- `p`, a member, put `B` on the wire at its tick at the start of slot `s`
    (hp : p ∈ Hon)
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    -- the honest voters of slot `s − 1` vote for blocks on `X`'s chain, honest at the vote time
    -- of slot `s`
    (hHsPrev : ∀ u ∈ Hs (s - 1), u ∈ S.P.committee (s - 1) ∧
      u ∉ Sched.adv (voteTime S s : Int) ∧
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s - 1)) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u (s - 1) (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      H u ∈ (stateBefore x (voteTime S (s - 1)) u).S.T ∧ X.AncestorEq (H u))
    -- at every member, the voters its vote of slot `s` counts are fewer than twice `Hs (s − 1)`
    (hVotersPrev : ∀ w ∈ Hon, ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes S.C (stateBefore x (voteTime S s) w).A
        (fg_to_ac (stateBefore x (voteTime S s) w).S) s votes support_votes →
      voters_count votes < 2 * (Hs (s - 1)).card)
    -- `p`'s anchor is `X` or an ancestor of `X`
    (hApX : (get_anchor (stateBefore x (slotStart S s) p).A
      (fg_to_ac (stateBefore x (slotStart S s) p).S) ((slotStart S s : ℕ) : Int)).AncestorEq X)
    -- every live lock a member's revocation of slot `s` leaves is on `B`'s parent's chain
    (hLocksW : ∀ w ∈ Hon, ∀ A' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S s) w).A
        ((voteTime S s : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S s) w).S)
        ((voteTime S s : ℕ) : Int) s = .ok A' →
      ∀ e ∈ A'.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S s) w).S) ((voteTime S s : ℕ) : Int) e =
          true → e.B.AncestorEq B.parent)
    -- `B` is the only slot-`s` block a member holds at the vote time; its root is new to `p`
    (hOnly : ∀ w ∈ Hon, ∀ B₁ ∈ (stateBefore x (voteTime S s) w).S.T, B₁.slot = s → B₁ = B)
    (hRootNew : ∀ B₁ ∈ (stateBefore x (slotStart S s) p).S.T, B₁.root ≠ B.root)
    -- the honest voters of every slot from `s` to `s'' − 1` are members voting at their slot
    (hHs : ∀ s', s ≤ s' → s' < s'' → ∀ u ∈ Hs s', u ∈ Hon ∧ u ∈ S.P.committee s' ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s' ∧
        ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s') ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x[i + 1].sent - x[i].sent)
    -- at every member, for every such slot `s'`, the voters counted by its vote of slot `s' + 1`
    -- and the slot-`s'` voters of its pool before the support cutoff of slot `s' + 1` are fewer
    -- than twice `Hs s'`
    (hVoters : ∀ s', s ≤ s' → s' < s'' → ∀ v ∈ Hon,
      (∀ votes support_votes : Finset (GoldfishVote V),
        CountedVotes S.C (stateBefore x (voteTime S (s' + 1)) v).A
          (fg_to_ac (stateBefore x (voteTime S (s' + 1)) v).S) (s' + 1) votes support_votes →
        voters_count votes < 2 * (Hs s').card) ∧
      voters_count ((stateBefore x (supportCutoff S (s' + 1)) v).A.pool s') < 2 * (Hs s').card)
    -- the slot-`(s'' − 1)` voters `q`'s proposal counts are fewer than twice `Hs (s'' − 1)`
    (hVotersQ : ∀ votes support_votes : Finset (GoldfishVote V),
      ProposalCountedVotes (stateBefore x (slotStart S s'') q).A
        (fg_to_ac (stateBefore x (slotStart S s'') q).S) (s'' - 1) votes support_votes →
      voters_count votes < 2 * (Hs (s'' - 1)).card)
    -- the slot-`s` committee is at most twice `Hs s`
    (hHalf : (S.P.committee s).card ≤ 2 * (Hs s).card)
    -- at every member and every time from the start of slot `s` to the start of slot `s''`, the
    -- frame has the root `ρ v t` and `head_height_floor` equal to `φ`
    (hShape : ∀ v ∈ Hon, ∀ t : ℕ, slotStart S s ≤ t → t ≤ slotStart S s'' →
      FrameShape (stateBefore x t v).S (ρ v t) φ)
    -- the roots: at the vote time of slot `s` on `B`'s parent's chain, at `a` on `B`'s chain, and
    -- after the vote time of slot `s` compatible with `B`
    (hRootW : ∀ w ∈ Hon, (ρ w (voteTime S s)).AncestorEq B.parent)
    (hRootAr : ∀ v ∈ Hon, (ρ v (supportCutoff S (s + 1))).AncestorEq B)
    (hRootAfter : ∀ v ∈ Hon, ∀ t : ℕ, voteTime S s < t → t ≤ slotStart S s'' →
      (ρ v t).compatible B = true)
    -- some block of `p`'s tree, on `X`'s and `p`'s root's chains, reaches `head_height_floor`; and `B`'s
    -- parent is in `p`'s viable tree
    (hHeadP : ∃ W ∈ (stateBefore x (slotStart S s) p).S.T,
      X.AncestorEq W ∧ (ρ p (slotStart S s)).AncestorEq W ∧ φ ≤ (chainStateOf S.C W).h)
    (hParentIn : B.parent ∈ viable_tree (fg_to_ac (stateBefore x (slotStart S s) p).S)
      (fg_to_ac (stateBefore x (slotStart S s) p).S).tree)
    -- `Q` is a quorum of members
    (hQ : Q ⊆ Hon)
    (hQuorum : quorum V ≤ Q.card)
    -- the record of every member of `Q` before `a`: the cache `h_j` is less than `H`, or no lock
    -- at `H`, or the lock at `H` is `T`
    (hLockBox : ∀ v ∈ Q,
      (stateBefore x (supportCutoff S (s + 1)) v).S.h_j < (chainStateOf S.C B).h ∨
      (stateBefore x (supportCutoff S (s + 1)) v).Λ.lock (chainStateOf S.C B).h = none ∨
      (stateBefore x (supportCutoff S (s + 1)) v).Λ.lock (chainStateOf S.C B).h =
        some (chainStateOf S.C B).T_h.root)
    -- `q`, a member, put `B'` on the wire at its tick at the start of slot `s''`
    (hq : q ∈ Hon)
    (hPropose' : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s'') ∧
      (⟨q, NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) :
    B.AncestorEq B' ∧
    ((chainStateOf S.C B).h + 1 ≤ (chainStateOf S.C B').h ∨
      ((chainStateOf S.C B').h = (chainStateOf S.C B).h ∧
        Q ⊆ (chainStateOf S.C B').progress ∧
        B'.slot < (chainStateOf S.C B).T_h.slot + S.C.δt)) ∧
    ((∀ u ∈ Q, ∀ b ∈ (stateBefore x (supportCutoff S (s + 1)) u).Λ.sent,
        b.h ≠ (chainStateOf S.C B).h) →
      (chainStateOf S.C B).h + 1 ≤ (chainStateOf S.C B').h ∧
        ((chainStateOf S.C B'.parent).h = (chainStateOf S.C B).h →
          (chainStateOf S.C B').J = (chainStateOf S.C B).T_h)) :=
  GoldilocksCorrectness.Proofs.Executions.lem80_round_height_advances_frame S Sched x GST r s s''
    Hon Q Hs H X B B' p q φ ρ hDiv hMono hSync hCatch hRoots hParent hOwner hSyncF hCatchF
    hs hs1 hs'' hGST hHon hp hPropose hHsPrev hVotersPrev hApX hLocksW hOnly hRootNew hHs hVoters
    hVotersQ hHalf hShape hRootW hRootAr hRootAfter hHeadP hParentIn hQ hQuorum hLockBox hq
    hPropose'

/-! ## What each box supplies to Lemma 80 -/

/-- **Lemma 80's frame, root and record hypotheses in box 1.** When every member of `Hon` is in box
1 with `h_max = h₀` at every time from the start of slot `s` to the start of slot `s''`, `p` is a
member, the support cutoff `a` of slot `s + 1` is in that window, and `p`'s proposal `B` has its
parent in `p`'s viable tree: every member's frame over the window has the root `F` and `head_height_floor` equal to
`h₀ − 1`, the finalized-block conditions and `p`'s block reaching `head_height_floor` are passed on as Lemma
80's root conditions and `hHeadP`, and every member's cache `h_j` before `a` is less than `B`'s
height.

Why: box 1 has the root `F` and `head_height_floor` equal to `h_max − 1` (Lemma 56); `B`'s height is at least
`head_height_floor` at `p`, equal to `h₀ − 1` (`proposal_viable`), and `h_j + 1 < h_max = h₀`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the round's first slot; `s''`:
  the end of the window; `Hon`: the members; `X`: the block `p`'s block extends; `B`: the
  proposal; `p`: its proposer; `h₀`: the common `h_max`.

Read aloud: in box 1 with one `h_max` the round theorem's frame conditions reduce to the box over
the window and the finalized blocks' positions on the proposal's chain, and the record hypothesis
is free.

 -/
theorem lem80_boxOne_hypotheses (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s s'' : ℕ) (Hon : Finset V) (X B : Block V) (p : V)
    (h₀ : Height)
    -- every member is in box 1 with `h_max = h₀` over the window
    (hBox : ∀ v ∈ Hon, ∀ t : ℕ, slotStart S s ≤ t → t ≤ slotStart S s'' →
      BoxOne (stateBefore x t v).S ∧ (stateBefore x t v).S.h_max = h₀)
    -- the finalized blocks: on `B`'s parent's chain at the vote time of slot `s`, on `B`'s chain
    -- at `a`, compatible with `B` afterwards
    (hFw : ∀ w ∈ Hon, (stateBefore x (voteTime S s) w).S.F.AncestorEq B.parent)
    (hFar : ∀ v ∈ Hon, (stateBefore x (supportCutoff S (s + 1)) v).S.F.AncestorEq B)
    (hFafter : ∀ v ∈ Hon, ∀ t : ℕ, voteTime S s < t → t ≤ slotStart S s'' →
      (stateBefore x t v).S.F.compatible B = true)
    (hp : p ∈ Hon)
    -- `a` is in the window
    (hs'' : supportCutoff S (s + 1) ≤ slotStart S s'')
    -- some block of `p`'s tree, on `X`'s and `p`'s finalized block's chains, reaches `h₀ − 1`
    (hHeadP : ∃ W ∈ (stateBefore x (slotStart S s) p).S.T,
      X.AncestorEq W ∧ (stateBefore x (slotStart S s) p).S.F.AncestorEq W ∧
        h₀ - 1 ≤ (chainStateOf S.C W).h)
    -- `p` put `B` on the wire at its tick at the start of slot `s`, `B`'s parent in its viable tree
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    (hParentIn : B.parent ∈ viable_tree (fg_to_ac (stateBefore x (slotStart S s) p).S)
      (fg_to_ac (stateBefore x (slotStart S s) p).S).tree) :
    (∀ v ∈ Hon, ∀ t : ℕ, slotStart S s ≤ t → t ≤ slotStart S s'' →
      FrameShape (stateBefore x t v).S (stateBefore x t v).S.F (h₀ - 1)) ∧
    (∀ w ∈ Hon, (stateBefore x (voteTime S s) w).S.F.AncestorEq B.parent) ∧
    (∀ v ∈ Hon, (stateBefore x (supportCutoff S (s + 1)) v).S.F.AncestorEq B) ∧
    (∀ v ∈ Hon, ∀ t : ℕ, voteTime S s < t → t ≤ slotStart S s'' →
      (stateBefore x t v).S.F.compatible B = true) ∧
    (∃ W ∈ (stateBefore x (slotStart S s) p).S.T,
      X.AncestorEq W ∧ (stateBefore x (slotStart S s) p).S.F.AncestorEq W ∧
        h₀ - 1 ≤ (chainStateOf S.C W).h) ∧
    (∀ v ∈ Hon, (stateBefore x (supportCutoff S (s + 1)) v).S.h_j < (chainStateOf S.C B).h) :=
  GoldilocksCorrectness.Proofs.Executions.lem80_boxOne_hypotheses S Sched x s s'' Hon X B p h₀
    hBox hFw hFar hFafter hp hs'' hHeadP hPropose hParentIn

/-- **Lemma 80's frame, root and record hypotheses in box 2.** When every member of `Hon` is in box
2 with the justified block `J₀ ≠ genesis` at every time from the start of slot `s` to the start of
slot `s''`, `p` is a member, the support cutoff `a` of slot `s + 1` is in that window, `p`'s
proposal `B` has its parent in `p`'s viable tree, and every member of `Q ⊆ Hon` has its lock at
`h_max − 1` before `a`, when set, on `J₀`: write `h₀` for `p`'s `h_max` before the start of slot
`s`; then every member's frame over the window has the root `J₀` and `head_height_floor` equal to `h₀ − 1`; `J₀` is an
ancestor of `B`'s parent, of `B`, and compatible with `B`; `p`'s block reaching `head_height_floor` is passed
on; and every member of `Q` before `a` has its cache `h_j` less than `B`'s height `H`, or no lock
at `H`, or its lock at `H` on the root of `B`'s `T_h`.

Why: box 2 has the root `J₀` and `head_height_floor` equal to `h_max − 1 = h_j`, and every `h_j` is `J₀`'s height
(Lemma 57), so every `head_height_floor` value is `h₀ − 1`; `B`'s parent is in the viable tree, whose blocks descend
from the root `J₀`; when `H = h_j = h_max − 1`, a lock at `H` is on `J₀`, which is `B`'s `T_h`
(`entry_block_of_boxTwo`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the round's first slot; `s''`:
  the end of the window; `Hon`: the members; `Q`: the quorum; `X`: the block `p`'s block extends;
  `B`: the proposal; `J₀`: the justified block; `p`: the proposer.

Read aloud: in box 2 the root condition is free, the `head_height_floor` values agree because every member's `h_max`
is one more than `J₀`'s height, and the lock, when set at `h_max − 1`, is on `J₀`, which is `B`'s
`T_h` when `B` is at `h_max − 1`.

 -/
theorem lem80_boxTwo_hypotheses (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s s'' : ℕ) (Hon Q : Finset V) (X B J₀ : Block V) (p : V)
    -- every member is in box 2 with the justified block `J₀` over the window
    (hBox : ∀ v ∈ Hon, ∀ t : ℕ, slotStart S s ≤ t → t ≤ slotStart S s'' →
      BoxTwo (stateBefore x t v).S J₀)
    -- `J₀` is not the genesis block
    (hJ₀ : J₀ ≠ Block.genesis)
    (hp : p ∈ Hon)
    -- `a` is in the window
    (hs'' : supportCutoff S (s + 1) ≤ slotStart S s'')
    -- some block of `p`'s tree, on `X`'s and `J₀`'s chains, reaches `p`'s `h_max − 1`
    (hHeadP : ∃ W ∈ (stateBefore x (slotStart S s) p).S.T,
      X.AncestorEq W ∧ J₀.AncestorEq W ∧
        (stateBefore x (slotStart S s) p).S.h_max - 1 ≤ (chainStateOf S.C W).h)
    -- `p` put `B` on the wire at its tick at the start of slot `s`, `B`'s parent in its viable tree
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    (hParentIn : B.parent ∈ viable_tree (fg_to_ac (stateBefore x (slotStart S s) p).S)
      (fg_to_ac (stateBefore x (slotStart S s) p).S).tree)
    (hQ : Q ⊆ Hon)
    -- every member of `Q` has its lock at `h_max − 1` before `a`, when set, on `J₀`
    (hLockJ₀ : ∀ v ∈ Q, ∀ T' : BlockId,
      (stateBefore x (supportCutoff S (s + 1)) v).Λ.lock
        ((stateBefore x (supportCutoff S (s + 1)) v).S.h_max - 1) = some T' → T' = J₀.root) :
    (∀ v ∈ Hon, ∀ t : ℕ, slotStart S s ≤ t → t ≤ slotStart S s'' →
      FrameShape (stateBefore x t v).S J₀ ((stateBefore x (slotStart S s) p).S.h_max - 1)) ∧
    J₀.AncestorEq B.parent ∧ J₀.AncestorEq B ∧ J₀.compatible B = true ∧
    (∃ W ∈ (stateBefore x (slotStart S s) p).S.T,
      X.AncestorEq W ∧ J₀.AncestorEq W ∧
        (stateBefore x (slotStart S s) p).S.h_max - 1 ≤ (chainStateOf S.C W).h) ∧
    (∀ v ∈ Q,
      (stateBefore x (supportCutoff S (s + 1)) v).S.h_j < (chainStateOf S.C B).h ∨
      (stateBefore x (supportCutoff S (s + 1)) v).Λ.lock (chainStateOf S.C B).h = none ∨
      (stateBefore x (supportCutoff S (s + 1)) v).Λ.lock (chainStateOf S.C B).h =
        some (chainStateOf S.C B).T_h.root) :=
  GoldilocksCorrectness.Proofs.Executions.lem80_boxTwo_hypotheses S Sched x s s'' Hon Q X B J₀ p
    hBox hJ₀ hp hs'' hHeadP hPropose hParentIn hQ hLockJ₀

/-- **Lemma 80's frame, root and record hypotheses in box 3.** When every member of `Hon` is in box
3 with `h_max = h₀` at every time from the start of slot `s` to the start of slot `s''`, `p` is a
member, the support cutoff `a` of slot `s + 1` is in that window, and `p`'s proposal `B` has its
parent in `p`'s viable tree: every member's frame over the window has the root `F` and `head_height_floor` equal to
`h₀`, the finalized-block conditions and `p`'s block reaching `head_height_floor` are passed on as Lemma 80's
root conditions and `hHeadP`, and every member's cache `h_j` before `a` is less than `B`'s height.

Why: box 3 has `h_max = h_j + 1`, the root `F` and `head_height_floor` equal to `h_max` (Lemma 56); `B`'s height is at
least `head_height_floor` at `p`, equal to `h₀` (`proposal_viable`), so `h_j = h₀ − 1` is less than it.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the round's first slot; `s''`:
  the end of the window; `Hon`: the members; `X`: the block `p`'s block extends; `B`: the
  proposal; `p`: its proposer; `h₀`: the common `h_max`.

Read aloud: box 3 is box 1 with `head_height_floor` equal to `h_max`.

 -/
theorem lem80_boxThree_hypotheses (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s s'' : ℕ) (Hon : Finset V) (X B : Block V) (p : V)
    (h₀ : Height)
    -- every member is in box 3 with `h_max = h₀` over the window
    (hBox : ∀ v ∈ Hon, ∀ t : ℕ, slotStart S s ≤ t → t ≤ slotStart S s'' →
      BoxThree (stateBefore x t v).S ∧ (stateBefore x t v).S.h_max = h₀)
    -- the finalized blocks: on `B`'s parent's chain at the vote time of slot `s`, on `B`'s chain
    -- at `a`, compatible with `B` afterwards
    (hFw : ∀ w ∈ Hon, (stateBefore x (voteTime S s) w).S.F.AncestorEq B.parent)
    (hFar : ∀ v ∈ Hon, (stateBefore x (supportCutoff S (s + 1)) v).S.F.AncestorEq B)
    (hFafter : ∀ v ∈ Hon, ∀ t : ℕ, voteTime S s < t → t ≤ slotStart S s'' →
      (stateBefore x t v).S.F.compatible B = true)
    (hp : p ∈ Hon)
    -- `a` is in the window
    (hs'' : supportCutoff S (s + 1) ≤ slotStart S s'')
    -- some block of `p`'s tree, on `X`'s and `p`'s finalized block's chains, reaches `h₀`
    (hHeadP : ∃ W ∈ (stateBefore x (slotStart S s) p).S.T,
      X.AncestorEq W ∧ (stateBefore x (slotStart S s) p).S.F.AncestorEq W ∧
        h₀ ≤ (chainStateOf S.C W).h)
    -- `p` put `B` on the wire at its tick at the start of slot `s`, `B`'s parent in its viable tree
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    (hParentIn : B.parent ∈ viable_tree (fg_to_ac (stateBefore x (slotStart S s) p).S)
      (fg_to_ac (stateBefore x (slotStart S s) p).S).tree) :
    (∀ v ∈ Hon, ∀ t : ℕ, slotStart S s ≤ t → t ≤ slotStart S s'' →
      FrameShape (stateBefore x t v).S (stateBefore x t v).S.F h₀) ∧
    (∀ w ∈ Hon, (stateBefore x (voteTime S s) w).S.F.AncestorEq B.parent) ∧
    (∀ v ∈ Hon, (stateBefore x (supportCutoff S (s + 1)) v).S.F.AncestorEq B) ∧
    (∀ v ∈ Hon, ∀ t : ℕ, voteTime S s < t → t ≤ slotStart S s'' →
      (stateBefore x t v).S.F.compatible B = true) ∧
    (∃ W ∈ (stateBefore x (slotStart S s) p).S.T,
      X.AncestorEq W ∧ (stateBefore x (slotStart S s) p).S.F.AncestorEq W ∧
        h₀ ≤ (chainStateOf S.C W).h) ∧
    (∀ v ∈ Hon, (stateBefore x (supportCutoff S (s + 1)) v).S.h_j < (chainStateOf S.C B).h) :=
  GoldilocksCorrectness.Proofs.Executions.lem80_boxThree_hypotheses S Sched x s s'' Hon X B p h₀
    hBox hFw hFar hFafter hp hs'' hHeadP hPropose hParentIn

/-! ## Lemma 80 in the three boxes -/

/-- **Lemma 80 in box 1.** Lemma 80's conclusion under Lemma 80's hypotheses with its frame, root
and record hypotheses replaced by box 1's: every member in box 1 with `h_max = h₀` over the window,
the finalized blocks on `B`'s parent's chain at the vote time of slot `s`, on `B`'s chain at the
action time, compatible with `B` afterwards, and some block of `p`'s tree on `X`'s and `p`'s
finalized block's chains reaching `h₀ − 1`.

Why: `lem80_boxOne_hypotheses` gives Lemma 80's frame, root and record hypotheses with the roots
`F` and `head_height_floor` equal to `h₀ − 1`; Lemma 80 concludes.

The variables: those of Lemma 80, with `h₀` the common `h_max` in place of the roots and `head_height_floor`.

Read aloud: in box 1 the round raises the height or puts the progress quorum on chain.




Roots name blocks until `supportCutoff S (s'' - 1)`: the proof reads Lemma 80
(`lem80_round_height_advances_frame`) at the same slots, whose bound is that time. -/
theorem lem80_boxOne (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (GST r s s'' : ℕ) (Hon Q : Finset V) (Hs : ℕ → Finset V) (H : V → Block V)
    (X B B' : Block V) (p q : V) (h₀ : Height)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s'' - 1)))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    -- attestations are delivered within `Δ_F S` after `GST`
    (hSyncF : SynchronyFromWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hCatchF : CatchUpOnWake Sched x.toTrace (Δ_F S) GST fgObject)
    -- `s` is the first slot of round `r`, not the first slot of all; an attestation sent at
    -- the action time of slot `s` is delivered, within `Δ_F S`, before slot `s''` starts
    (hs : s = r * S.C.R)
    (hs1 : 1 ≤ s)
    (hs'' : supportCutoff S (s + 1) + Δ_F S ≤ slotStart S s'')
    -- the network is synchronous from the vote time of slot `s − 1`
    (hGST : GST ≤ voteTime S (s - 1))
    -- the members are awake and honest from the duty window's start of slot `s` to the start of
    -- slot `s''`
    (hHon : ∀ v ∈ Hon, ∀ t : ℕ, dutyWindowStart S s ≤ t → t ≤ slotStart S s'' →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    -- `p`, a member, put `B` on the wire at its tick at the start of slot `s`
    (hp : p ∈ Hon)
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    -- the honest voters of slot `s − 1` vote for blocks on `X`'s chain, honest at the vote time
    -- of slot `s`
    (hHsPrev : ∀ u ∈ Hs (s - 1), u ∈ S.P.committee (s - 1) ∧
      u ∉ Sched.adv (voteTime S s : Int) ∧
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s - 1)) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u (s - 1) (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      H u ∈ (stateBefore x (voteTime S (s - 1)) u).S.T ∧ X.AncestorEq (H u))
    -- at every member, the voters its vote of slot `s` counts are fewer than twice `Hs (s − 1)`
    (hVotersPrev : ∀ w ∈ Hon, ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes S.C (stateBefore x (voteTime S s) w).A
        (fg_to_ac (stateBefore x (voteTime S s) w).S) s votes support_votes →
      voters_count votes < 2 * (Hs (s - 1)).card)
    -- `p`'s anchor is `X` or an ancestor of `X`
    (hApX : (get_anchor (stateBefore x (slotStart S s) p).A
      (fg_to_ac (stateBefore x (slotStart S s) p).S) ((slotStart S s : ℕ) : Int)).AncestorEq X)
    -- every live lock a member's revocation of slot `s` leaves is on `B`'s parent's chain
    (hLocksW : ∀ w ∈ Hon, ∀ A' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S s) w).A
        ((voteTime S s : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S s) w).S)
        ((voteTime S s : ℕ) : Int) s = .ok A' →
      ∀ e ∈ A'.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S s) w).S) ((voteTime S s : ℕ) : Int) e =
          true → e.B.AncestorEq B.parent)
    -- `B` is the only slot-`s` block a member holds at the vote time; its root is new to `p`
    (hOnly : ∀ w ∈ Hon, ∀ B₁ ∈ (stateBefore x (voteTime S s) w).S.T, B₁.slot = s → B₁ = B)
    (hRootNew : ∀ B₁ ∈ (stateBefore x (slotStart S s) p).S.T, B₁.root ≠ B.root)
    -- the honest voters of every slot from `s` to `s'' − 1` are members voting at their slot
    (hHs : ∀ s', s ≤ s' → s' < s'' → ∀ u ∈ Hs s', u ∈ Hon ∧ u ∈ S.P.committee s' ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s' ∧
        ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s') ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x[i + 1].sent - x[i].sent)
    -- at every member, for every such slot `s'`, the voters counted by its vote of slot `s' + 1`
    -- and the slot-`s'` voters of its pool before the support cutoff of slot `s' + 1` are fewer
    -- than twice `Hs s'`
    (hVoters : ∀ s', s ≤ s' → s' < s'' → ∀ v ∈ Hon,
      (∀ votes support_votes : Finset (GoldfishVote V),
        CountedVotes S.C (stateBefore x (voteTime S (s' + 1)) v).A
          (fg_to_ac (stateBefore x (voteTime S (s' + 1)) v).S) (s' + 1) votes support_votes →
        voters_count votes < 2 * (Hs s').card) ∧
      voters_count ((stateBefore x (supportCutoff S (s' + 1)) v).A.pool s') < 2 * (Hs s').card)
    -- the slot-`(s'' − 1)` voters `q`'s proposal counts are fewer than twice `Hs (s'' − 1)`
    (hVotersQ : ∀ votes support_votes : Finset (GoldfishVote V),
      ProposalCountedVotes (stateBefore x (slotStart S s'') q).A
        (fg_to_ac (stateBefore x (slotStart S s'') q).S) (s'' - 1) votes support_votes →
      voters_count votes < 2 * (Hs (s'' - 1)).card)
    -- the slot-`s` committee is at most twice `Hs s`
    (hHalf : (S.P.committee s).card ≤ 2 * (Hs s).card)
    -- every member is in box 1 with `h_max = h₀` over the window
    (hBox : ∀ v ∈ Hon, ∀ t : ℕ, slotStart S s ≤ t → t ≤ slotStart S s'' →
      BoxOne (stateBefore x t v).S ∧ (stateBefore x t v).S.h_max = h₀)
    -- the finalized blocks: on `B`'s parent's chain at the vote time of slot `s`, on `B`'s chain
    -- at the action time, compatible with `B` afterwards
    (hFw : ∀ w ∈ Hon, (stateBefore x (voteTime S s) w).S.F.AncestorEq B.parent)
    (hFar : ∀ v ∈ Hon, (stateBefore x (supportCutoff S (s + 1)) v).S.F.AncestorEq B)
    (hFafter : ∀ v ∈ Hon, ∀ t : ℕ, voteTime S s < t → t ≤ slotStart S s'' →
      (stateBefore x t v).S.F.compatible B = true)
    -- some block of `p`'s tree, on `X`'s and `p`'s finalized block's chains, reaches `h₀ − 1`; and
    -- `B`'s parent is in `p`'s viable tree
    (hHeadP : ∃ W ∈ (stateBefore x (slotStart S s) p).S.T,
      X.AncestorEq W ∧ (stateBefore x (slotStart S s) p).S.F.AncestorEq W ∧
        h₀ - 1 ≤ (chainStateOf S.C W).h)
    (hParentIn : B.parent ∈ viable_tree (fg_to_ac (stateBefore x (slotStart S s) p).S)
      (fg_to_ac (stateBefore x (slotStart S s) p).S).tree)
    -- `Q` is a quorum of members
    (hQ : Q ⊆ Hon)
    (hQuorum : quorum V ≤ Q.card)
    -- `q`, a member, put `B'` on the wire at its tick at the start of slot `s''`
    (hq : q ∈ Hon)
    (hPropose' : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s'') ∧
      (⟨q, NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) :
    B.AncestorEq B' ∧
    ((chainStateOf S.C B).h + 1 ≤ (chainStateOf S.C B').h ∨
      ((chainStateOf S.C B').h = (chainStateOf S.C B).h ∧
        Q ⊆ (chainStateOf S.C B').progress ∧
        B'.slot < (chainStateOf S.C B).T_h.slot + S.C.δt)) ∧
    ((∀ u ∈ Q, ∀ b ∈ (stateBefore x (supportCutoff S (s + 1)) u).Λ.sent,
        b.h ≠ (chainStateOf S.C B).h) →
      (chainStateOf S.C B).h + 1 ≤ (chainStateOf S.C B').h ∧
        ((chainStateOf S.C B'.parent).h = (chainStateOf S.C B).h →
          (chainStateOf S.C B').J = (chainStateOf S.C B).T_h)) :=
  GoldilocksCorrectness.Proofs.Executions.lem80_boxOne S Sched x GST r s s'' Hon Q Hs H X B B' p q
    h₀ hDiv hMono hSync hCatch hRoots hParent hOwner hSyncF hCatchF hs hs1 hs'' hGST hHon hp
    hPropose hHsPrev hVotersPrev hApX hLocksW hOnly hRootNew hHs hVoters hVotersQ hHalf hBox hFw
    hFar hFafter hHeadP hParentIn hQ hQuorum hq hPropose'

/-- **Lemma 80 in box 2.** Lemma 80's conclusion under Lemma 80's hypotheses with its frame, root
and record hypotheses replaced by box 2's: every member in box 2 with the justified block
`J₀ ≠ genesis` over the window, some block of `p`'s tree on `X`'s and `J₀`'s chains reaching `p`'s
`h_max − 1`, and every member of `Q` with its lock at `h_max − 1` before the action time, when
set, on `J₀`.

Why: `lem80_boxTwo_hypotheses` gives Lemma 80's frame, root and record hypotheses with the root
`J₀` and `head_height_floor` equal to `h_max − 1` of `p`'s state before the start of slot `s`; Lemma 80 concludes.

The variables: those of Lemma 80, with `J₀` the justified block in place of the roots and `head_height_floor`.

Read aloud: in box 2 the round raises the height or puts the progress quorum on chain.




Roots name blocks until `supportCutoff S (s'' - 1)`: the proof reads Lemma 80
(`lem80_round_height_advances_frame`) at the same slots, whose bound is that time. -/
theorem lem80_boxTwo (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (GST r s s'' : ℕ) (Hon Q : Finset V) (Hs : ℕ → Finset V) (H : V → Block V)
    (X B B' J₀ : Block V) (p q : V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s'' - 1)))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    -- attestations are delivered within `Δ_F S` after `GST`
    (hSyncF : SynchronyFromWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hCatchF : CatchUpOnWake Sched x.toTrace (Δ_F S) GST fgObject)
    -- `s` is the first slot of round `r`, not the first slot of all; an attestation sent at
    -- the action time of slot `s` is delivered, within `Δ_F S`, before slot `s''` starts
    (hs : s = r * S.C.R)
    (hs1 : 1 ≤ s)
    (hs'' : supportCutoff S (s + 1) + Δ_F S ≤ slotStart S s'')
    -- the network is synchronous from the vote time of slot `s − 1`
    (hGST : GST ≤ voteTime S (s - 1))
    -- the members are awake and honest from the duty window's start of slot `s` to the start of
    -- slot `s''`
    (hHon : ∀ v ∈ Hon, ∀ t : ℕ, dutyWindowStart S s ≤ t → t ≤ slotStart S s'' →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    -- `p`, a member, put `B` on the wire at its tick at the start of slot `s`
    (hp : p ∈ Hon)
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    -- the honest voters of slot `s − 1` vote for blocks on `X`'s chain, honest at the vote time
    -- of slot `s`
    (hHsPrev : ∀ u ∈ Hs (s - 1), u ∈ S.P.committee (s - 1) ∧
      u ∉ Sched.adv (voteTime S s : Int) ∧
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s - 1)) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u (s - 1) (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      H u ∈ (stateBefore x (voteTime S (s - 1)) u).S.T ∧ X.AncestorEq (H u))
    -- at every member, the voters its vote of slot `s` counts are fewer than twice `Hs (s − 1)`
    (hVotersPrev : ∀ w ∈ Hon, ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes S.C (stateBefore x (voteTime S s) w).A
        (fg_to_ac (stateBefore x (voteTime S s) w).S) s votes support_votes →
      voters_count votes < 2 * (Hs (s - 1)).card)
    -- `p`'s anchor is `X` or an ancestor of `X`
    (hApX : (get_anchor (stateBefore x (slotStart S s) p).A
      (fg_to_ac (stateBefore x (slotStart S s) p).S) ((slotStart S s : ℕ) : Int)).AncestorEq X)
    -- every live lock a member's revocation of slot `s` leaves is on `B`'s parent's chain
    (hLocksW : ∀ w ∈ Hon, ∀ A' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S s) w).A
        ((voteTime S s : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S s) w).S)
        ((voteTime S s : ℕ) : Int) s = .ok A' →
      ∀ e ∈ A'.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S s) w).S) ((voteTime S s : ℕ) : Int) e =
          true → e.B.AncestorEq B.parent)
    -- `B` is the only slot-`s` block a member holds at the vote time; its root is new to `p`
    (hOnly : ∀ w ∈ Hon, ∀ B₁ ∈ (stateBefore x (voteTime S s) w).S.T, B₁.slot = s → B₁ = B)
    (hRootNew : ∀ B₁ ∈ (stateBefore x (slotStart S s) p).S.T, B₁.root ≠ B.root)
    -- the honest voters of every slot from `s` to `s'' − 1` are members voting at their slot
    (hHs : ∀ s', s ≤ s' → s' < s'' → ∀ u ∈ Hs s', u ∈ Hon ∧ u ∈ S.P.committee s' ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s' ∧
        ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s') ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x[i + 1].sent - x[i].sent)
    -- at every member, for every such slot `s'`, the voters counted by its vote of slot `s' + 1`
    -- and the slot-`s'` voters of its pool before the support cutoff of slot `s' + 1` are fewer
    -- than twice `Hs s'`
    (hVoters : ∀ s', s ≤ s' → s' < s'' → ∀ v ∈ Hon,
      (∀ votes support_votes : Finset (GoldfishVote V),
        CountedVotes S.C (stateBefore x (voteTime S (s' + 1)) v).A
          (fg_to_ac (stateBefore x (voteTime S (s' + 1)) v).S) (s' + 1) votes support_votes →
        voters_count votes < 2 * (Hs s').card) ∧
      voters_count ((stateBefore x (supportCutoff S (s' + 1)) v).A.pool s') < 2 * (Hs s').card)
    -- the slot-`(s'' − 1)` voters `q`'s proposal counts are fewer than twice `Hs (s'' − 1)`
    (hVotersQ : ∀ votes support_votes : Finset (GoldfishVote V),
      ProposalCountedVotes (stateBefore x (slotStart S s'') q).A
        (fg_to_ac (stateBefore x (slotStart S s'') q).S) (s'' - 1) votes support_votes →
      voters_count votes < 2 * (Hs (s'' - 1)).card)
    -- the slot-`s` committee is at most twice `Hs s`
    (hHalf : (S.P.committee s).card ≤ 2 * (Hs s).card)
    -- every member is in box 2 with the justified block `J₀`, not the genesis block, over the
    -- window
    (hBox : ∀ v ∈ Hon, ∀ t : ℕ, slotStart S s ≤ t → t ≤ slotStart S s'' →
      BoxTwo (stateBefore x t v).S J₀)
    (hJ₀ : J₀ ≠ Block.genesis)
    -- some block of `p`'s tree, on `X`'s and `J₀`'s chains, reaches `p`'s `h_max − 1`; and `B`'s
    -- parent is in `p`'s viable tree
    (hHeadP : ∃ W ∈ (stateBefore x (slotStart S s) p).S.T,
      X.AncestorEq W ∧ J₀.AncestorEq W ∧
        (stateBefore x (slotStart S s) p).S.h_max - 1 ≤ (chainStateOf S.C W).h)
    (hParentIn : B.parent ∈ viable_tree (fg_to_ac (stateBefore x (slotStart S s) p).S)
      (fg_to_ac (stateBefore x (slotStart S s) p).S).tree)
    -- `Q` is a quorum of members
    (hQ : Q ⊆ Hon)
    (hQuorum : quorum V ≤ Q.card)
    -- every member of `Q` has its lock at `h_max − 1` before the action time, when set, on `J₀`
    (hLockJ₀ : ∀ v ∈ Q, ∀ T' : BlockId,
      (stateBefore x (supportCutoff S (s + 1)) v).Λ.lock
        ((stateBefore x (supportCutoff S (s + 1)) v).S.h_max - 1) = some T' → T' = J₀.root)
    -- `q`, a member, put `B'` on the wire at its tick at the start of slot `s''`
    (hq : q ∈ Hon)
    (hPropose' : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s'') ∧
      (⟨q, NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) :
    B.AncestorEq B' ∧
    ((chainStateOf S.C B).h + 1 ≤ (chainStateOf S.C B').h ∨
      ((chainStateOf S.C B').h = (chainStateOf S.C B).h ∧
        Q ⊆ (chainStateOf S.C B').progress ∧
        B'.slot < (chainStateOf S.C B).T_h.slot + S.C.δt)) ∧
    ((∀ u ∈ Q, ∀ b ∈ (stateBefore x (supportCutoff S (s + 1)) u).Λ.sent,
        b.h ≠ (chainStateOf S.C B).h) →
      (chainStateOf S.C B).h + 1 ≤ (chainStateOf S.C B').h ∧
        ((chainStateOf S.C B'.parent).h = (chainStateOf S.C B).h →
          (chainStateOf S.C B').J = (chainStateOf S.C B).T_h)) :=
  GoldilocksCorrectness.Proofs.Executions.lem80_boxTwo S Sched x GST r s s'' Hon Q Hs H X B B' J₀
    p q hDiv hMono hSync hCatch hRoots hParent hOwner hSyncF hCatchF hs hs1 hs'' hGST hHon
    hp hPropose hHsPrev hVotersPrev hApX hLocksW hOnly hRootNew hHs hVoters hVotersQ hHalf hBox
    hJ₀ hHeadP hParentIn hQ hQuorum hLockJ₀ hq hPropose'

/-- **Lemma 80 in box 3.** Lemma 80's conclusion under Lemma 80's hypotheses with its frame, root
and record hypotheses replaced by box 3's: every member in box 3 with `h_max = h₀` over the window,
the finalized blocks on `B`'s parent's chain at the vote time of slot `s`, on `B`'s chain at the
action time, compatible with `B` afterwards, and some block of `p`'s tree on `X`'s and `p`'s
finalized block's chains reaching `h₀`.

Why: `lem80_boxThree_hypotheses` gives Lemma 80's frame, root and record hypotheses with the roots
`F` and `head_height_floor` equal to `h₀`; Lemma 80 concludes.

The variables: those of Lemma 80, with `h₀` the common `h_max` in place of the roots and `head_height_floor`.

Read aloud: in box 3 the round raises the height or puts the progress quorum on chain.




Roots name blocks until `supportCutoff S (s'' - 1)`: the proof reads Lemma 80
(`lem80_round_height_advances_frame`) at the same slots, whose bound is that time. -/
theorem lem80_boxThree (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (GST r s s'' : ℕ) (Hon Q : Finset V) (Hs : ℕ → Finset V) (H : V → Block V)
    (X B B' : Block V) (p q : V) (h₀ : Height)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s'' - 1)))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    -- attestations are delivered within `Δ_F S` after `GST`
    (hSyncF : SynchronyFromWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hCatchF : CatchUpOnWake Sched x.toTrace (Δ_F S) GST fgObject)
    -- `s` is the first slot of round `r`, not the first slot of all; an attestation sent at
    -- the action time of slot `s` is delivered, within `Δ_F S`, before slot `s''` starts
    (hs : s = r * S.C.R)
    (hs1 : 1 ≤ s)
    (hs'' : supportCutoff S (s + 1) + Δ_F S ≤ slotStart S s'')
    -- the network is synchronous from the vote time of slot `s − 1`
    (hGST : GST ≤ voteTime S (s - 1))
    -- the members are awake and honest from the duty window's start of slot `s` to the start of
    -- slot `s''`
    (hHon : ∀ v ∈ Hon, ∀ t : ℕ, dutyWindowStart S s ≤ t → t ≤ slotStart S s'' →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    -- `p`, a member, put `B` on the wire at its tick at the start of slot `s`
    (hp : p ∈ Hon)
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    -- the honest voters of slot `s − 1` vote for blocks on `X`'s chain, honest at the vote time
    -- of slot `s`
    (hHsPrev : ∀ u ∈ Hs (s - 1), u ∈ S.P.committee (s - 1) ∧
      u ∉ Sched.adv (voteTime S s : Int) ∧
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s - 1)) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u (s - 1) (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      H u ∈ (stateBefore x (voteTime S (s - 1)) u).S.T ∧ X.AncestorEq (H u))
    -- at every member, the voters its vote of slot `s` counts are fewer than twice `Hs (s − 1)`
    (hVotersPrev : ∀ w ∈ Hon, ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes S.C (stateBefore x (voteTime S s) w).A
        (fg_to_ac (stateBefore x (voteTime S s) w).S) s votes support_votes →
      voters_count votes < 2 * (Hs (s - 1)).card)
    -- `p`'s anchor is `X` or an ancestor of `X`
    (hApX : (get_anchor (stateBefore x (slotStart S s) p).A
      (fg_to_ac (stateBefore x (slotStart S s) p).S) ((slotStart S s : ℕ) : Int)).AncestorEq X)
    -- every live lock a member's revocation of slot `s` leaves is on `B`'s parent's chain
    (hLocksW : ∀ w ∈ Hon, ∀ A' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S s) w).A
        ((voteTime S s : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S s) w).S)
        ((voteTime S s : ℕ) : Int) s = .ok A' →
      ∀ e ∈ A'.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S s) w).S) ((voteTime S s : ℕ) : Int) e =
          true → e.B.AncestorEq B.parent)
    -- `B` is the only slot-`s` block a member holds at the vote time; its root is new to `p`
    (hOnly : ∀ w ∈ Hon, ∀ B₁ ∈ (stateBefore x (voteTime S s) w).S.T, B₁.slot = s → B₁ = B)
    (hRootNew : ∀ B₁ ∈ (stateBefore x (slotStart S s) p).S.T, B₁.root ≠ B.root)
    -- the honest voters of every slot from `s` to `s'' − 1` are members voting at their slot
    (hHs : ∀ s', s ≤ s' → s' < s'' → ∀ u ∈ Hs s', u ∈ Hon ∧ u ∈ S.P.committee s' ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s' ∧
        ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s') ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x[i + 1].sent - x[i].sent)
    -- at every member, for every such slot `s'`, the voters counted by its vote of slot `s' + 1`
    -- and the slot-`s'` voters of its pool before the support cutoff of slot `s' + 1` are fewer
    -- than twice `Hs s'`
    (hVoters : ∀ s', s ≤ s' → s' < s'' → ∀ v ∈ Hon,
      (∀ votes support_votes : Finset (GoldfishVote V),
        CountedVotes S.C (stateBefore x (voteTime S (s' + 1)) v).A
          (fg_to_ac (stateBefore x (voteTime S (s' + 1)) v).S) (s' + 1) votes support_votes →
        voters_count votes < 2 * (Hs s').card) ∧
      voters_count ((stateBefore x (supportCutoff S (s' + 1)) v).A.pool s') < 2 * (Hs s').card)
    -- the slot-`(s'' − 1)` voters `q`'s proposal counts are fewer than twice `Hs (s'' − 1)`
    (hVotersQ : ∀ votes support_votes : Finset (GoldfishVote V),
      ProposalCountedVotes (stateBefore x (slotStart S s'') q).A
        (fg_to_ac (stateBefore x (slotStart S s'') q).S) (s'' - 1) votes support_votes →
      voters_count votes < 2 * (Hs (s'' - 1)).card)
    -- the slot-`s` committee is at most twice `Hs s`
    (hHalf : (S.P.committee s).card ≤ 2 * (Hs s).card)
    -- every member is in box 3 with `h_max = h₀` over the window
    (hBox : ∀ v ∈ Hon, ∀ t : ℕ, slotStart S s ≤ t → t ≤ slotStart S s'' →
      BoxThree (stateBefore x t v).S ∧ (stateBefore x t v).S.h_max = h₀)
    -- the finalized blocks: on `B`'s parent's chain at the vote time of slot `s`, on `B`'s chain
    -- at the action time, compatible with `B` afterwards
    (hFw : ∀ w ∈ Hon, (stateBefore x (voteTime S s) w).S.F.AncestorEq B.parent)
    (hFar : ∀ v ∈ Hon, (stateBefore x (supportCutoff S (s + 1)) v).S.F.AncestorEq B)
    (hFafter : ∀ v ∈ Hon, ∀ t : ℕ, voteTime S s < t → t ≤ slotStart S s'' →
      (stateBefore x t v).S.F.compatible B = true)
    -- some block of `p`'s tree, on `X`'s and `p`'s finalized block's chains, reaches `h₀`; and
    -- `B`'s parent is in `p`'s viable tree
    (hHeadP : ∃ W ∈ (stateBefore x (slotStart S s) p).S.T,
      X.AncestorEq W ∧ (stateBefore x (slotStart S s) p).S.F.AncestorEq W ∧
        h₀ ≤ (chainStateOf S.C W).h)
    (hParentIn : B.parent ∈ viable_tree (fg_to_ac (stateBefore x (slotStart S s) p).S)
      (fg_to_ac (stateBefore x (slotStart S s) p).S).tree)
    -- `Q` is a quorum of members
    (hQ : Q ⊆ Hon)
    (hQuorum : quorum V ≤ Q.card)
    -- `q`, a member, put `B'` on the wire at its tick at the start of slot `s''`
    (hq : q ∈ Hon)
    (hPropose' : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s'') ∧
      (⟨q, NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) :
    B.AncestorEq B' ∧
    ((chainStateOf S.C B).h + 1 ≤ (chainStateOf S.C B').h ∨
      ((chainStateOf S.C B').h = (chainStateOf S.C B).h ∧
        Q ⊆ (chainStateOf S.C B').progress ∧
        B'.slot < (chainStateOf S.C B).T_h.slot + S.C.δt)) ∧
    ((∀ u ∈ Q, ∀ b ∈ (stateBefore x (supportCutoff S (s + 1)) u).Λ.sent,
        b.h ≠ (chainStateOf S.C B).h) →
      (chainStateOf S.C B).h + 1 ≤ (chainStateOf S.C B').h ∧
        ((chainStateOf S.C B'.parent).h = (chainStateOf S.C B).h →
          (chainStateOf S.C B').J = (chainStateOf S.C B).T_h)) :=
  GoldilocksCorrectness.Proofs.Executions.lem80_boxThree S Sched x GST r s s'' Hon Q Hs H X B B' p
    q h₀ hDiv hMono hSync hCatch hRoots hParent hOwner hSyncF hCatchF hs hs1 hs'' hGST hHon
    hp hPropose hHsPrev hVotersPrev hApX hLocksW hOnly hRootNew hHs hVoters hVotersQ hHalf hBox hFw
    hFar hFafter hHeadP hParentIn hQ hQuorum hq hPropose'

/-! ## `lem80wq_round_height_advances_steps` in the three boxes -/

/-- **`lem80wq_round_height_advances_steps` in box 1.** Its conclusion under its hypotheses with
the frame, root and record hypotheses replaced by box facts at the three reading points of slot
`s`: `p` in box 1 before the start of slot `s`; each member of `Hon s` before the vote time of slot
`s` in box 1 with `h_max` at least `p`'s and at most `h(B.parent) + 1`, or in box 3 with `h_max` at
least `p`'s minus one and at most `h(B.parent)`; each member before the action time `a` in box 1
with `h_max` at most `h(B) + 1`, or in box 3 with `h_max` at most `h(B)`; the members' finalized
blocks on `B`'s parent's chain before the vote time and on `B`'s chain before `a`; and some block of
`p`'s tree on `X`'s and `p`'s finalized block's chains reaching `p`'s `h_max − 1`.

Why: in boxes 1 and 3 the root is the finalized block and the `head_height_floor` is `h_max − 1`
and `h_max` (Lemma 56), so the bounds on `h_max` place each member's `head_height_floor` between
`p`'s and the parent's height; every member's cache `h_j` before `a` is less than `B`'s height,
which gives the record hypothesis.

The variables: those of `lem80wq_round_height_advances_steps`, without the roots and the
`head_height_floor` values.

Read aloud: when the proposer is in box 1 and each member in box 1 or box 3 with its `h_max`
between the proposer's and the parent's height plus one, the round raises the height or puts the
progress quorum on chain.




Roots name blocks until `supportCutoff S (s'' - 1)`: the proof reads
`lem80wq_round_height_advances_steps` at the same slots, whose bound is that time. -/
theorem lem80wq_boxOne (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched)
    (GST r s s'' : ℕ) (Hon : ℕ → Finset V) (Q : Finset V) (Hs : ℕ → Finset V)
    (H : V → Block V) (X B B' : Block V) (p q : V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s'' - 1)))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    -- attestations are delivered within `Δ_F S` after `GST`
    (hSyncF : SynchronyFromWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hCatchF : CatchUpOnWake Sched x.toTrace (Δ_F S) GST fgObject)
    -- `s` is the first slot of round `r`, not the first slot of all; an attestation sent at
    -- the action time of slot `s` is delivered, within `Δ_F S`, before slot `s''` starts
    (hs : s = r * S.C.R) (hs1 : 1 ≤ s) (hs'' : supportCutoff S (s + 1) + Δ_F S ≤ slotStart S s'')
    -- the network is synchronous from the vote time of slot `s − 1`
    (hGST : GST ≤ voteTime S (s - 1))
    -- the member sets shrink from one slot to the next
    (hHonMono : ∀ s', s ≤ s' → s' + 1 < s'' → Hon (s' + 1) ⊆ Hon s')
    -- the members of slot `s'` are awake and honest from the duty window's start of slot `s'` to
    -- the support cutoff of slot `s' + 1`, and not past the start of slot `s''`
    (hHon : ∀ s', s ≤ s' → s' < s'' → ∀ v ∈ Hon s', ∀ t : ℕ,
      dutyWindowStart S s' ≤ t → t ≤ supportCutoff S (s' + 1) → t ≤ slotStart S s'' →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    -- the proposer: awake and honest from the vote time of slot `s − 1` to the start of slot `s`
    (hp : ∀ t : ℕ, voteTime S (s - 1) ≤ t → t ≤ slotStart S s →
      p ∈ Sched.awake (t : Int) ∧ p ∉ Sched.adv (t : Int))
    -- `p` put `B` on the wire at its tick at the start of slot `s`
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    -- the honest voters of slot `s − 1` vote for blocks on `X`'s chain, honest at the vote time
    -- of slot `s`
    (hHsPrev : ∀ u ∈ Hs (s - 1), u ∈ S.P.committee (s - 1) ∧
      u ∉ Sched.adv (voteTime S s : Int) ∧
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s - 1)) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u (s - 1) (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      H u ∈ (stateBefore x (voteTime S (s - 1)) u).S.T ∧ X.AncestorEq (H u))
    -- at every member of `Hon s`, the voters its vote of slot `s` counts are fewer than twice
    -- `Hs (s − 1)`
    (hVotersPrev : ∀ w ∈ Hon s, ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes S.C (stateBefore x (voteTime S s) w).A
        (fg_to_ac (stateBefore x (voteTime S s) w).S) s votes support_votes →
      voters_count votes < 2 * (Hs (s - 1)).card)
    -- `p`'s anchor is `X` or an ancestor of `X`
    (hApX : (get_anchor (stateBefore x (slotStart S s) p).A
      (fg_to_ac (stateBefore x (slotStart S s) p).S) ((slotStart S s : ℕ) : Int)).AncestorEq X)
    -- every live lock a member's revocation of slot `s` leaves is on `B`'s parent's chain
    (hLocksW : ∀ w ∈ Hon s, ∀ A' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S s) w).A
        ((voteTime S s : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S s) w).S)
        ((voteTime S s : ℕ) : Int) s = .ok A' →
      ∀ e ∈ A'.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S s) w).S) ((voteTime S s : ℕ) : Int) e =
          true → e.B.AncestorEq B.parent)
    -- `B` is the only slot-`s` block a member holds at the vote time; its root is new to `p`
    (hOnly : ∀ w ∈ Hon s, ∀ B₁ ∈ (stateBefore x (voteTime S s) w).S.T, B₁.slot = s → B₁ = B)
    (hRootNew : ∀ B₁ ∈ (stateBefore x (slotStart S s) p).S.T, B₁.root ≠ B.root)
    -- the honest voters of slot `s'` are members of `Hon s'` and of the slot's committee
    (hHs : ∀ s', s ≤ s' → s' < s'' → ∀ u ∈ Hs s', u ∈ Hon s' ∧ u ∈ S.P.committee s' ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s' ∧
        ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s') ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x[i + 1].sent - x[i].sent)
    -- the counts of slot `s'`, read at the members of `Hon s'`: the voters counted by a vote of
    -- slot `s' + 1` and the slot-`s'` voters of the pool before the support cutoff of slot
    -- `s' + 1` are fewer than twice `Hs s'`
    (hVoters : ∀ s', s ≤ s' → s' < s'' → ∀ v ∈ Hon s',
      (∀ votes support_votes : Finset (GoldfishVote V),
        CountedVotes S.C (stateBefore x (voteTime S (s' + 1)) v).A
          (fg_to_ac (stateBefore x (voteTime S (s' + 1)) v).S) (s' + 1) votes support_votes →
        voters_count votes < 2 * (Hs s').card) ∧
      voters_count ((stateBefore x (supportCutoff S (s' + 1)) v).A.pool s') < 2 * (Hs s').card)
    -- the slot-`(s'' − 1)` voters `q`'s proposal counts are fewer than twice `Hs (s'' − 1)`
    (hVotersQ : ∀ votes support_votes : Finset (GoldfishVote V),
      ProposalCountedVotes (stateBefore x (slotStart S s'') q).A
        (fg_to_ac (stateBefore x (slotStart S s'') q).S) (s'' - 1) votes support_votes →
      voters_count votes < 2 * (Hs (s'' - 1)).card)
    -- the slot-`s` committee is at most twice `Hs s`
    (hHalf : (S.P.committee s).card ≤ 2 * (Hs s).card)
    -- `p` is in box 1 before the start of slot `s`
    (hBoxP : BoxOne (stateBefore x (slotStart S s) p).S)
    -- before the vote time of slot `s`, every member of `Hon s` is in box 1 with `h_max` at least
    -- `p`'s and at most `h(B.parent) + 1`, or in box 3 with `h_max` at least `p`'s minus one and at
    -- most `h(B.parent)`
    (hBoxW : ∀ w ∈ Hon s,
      (BoxOne (stateBefore x (voteTime S s) w).S ∧ (stateBefore x (slotStart S s) p).S.h_max ≤ (stateBefore x (voteTime S s) w).S.h_max ∧
        (stateBefore x (voteTime S s) w).S.h_max ≤ (chainStateOf S.C B.parent).h + 1) ∨
      (BoxThree (stateBefore x (voteTime S s) w).S ∧ (stateBefore x (slotStart S s) p).S.h_max ≤ (stateBefore x (voteTime S s) w).S.h_max + 1 ∧
        (stateBefore x (voteTime S s) w).S.h_max ≤ (chainStateOf S.C B.parent).h))
    -- before the action time, every member of `Hon s` is in box 1 with `h_max` at most `h(B) + 1`,
    -- or in box 3 with `h_max` at most `h(B)`
    (hBoxV : ∀ v ∈ Hon s,
      (BoxOne (stateBefore x (supportCutoff S (s + 1)) v).S ∧ (stateBefore x (supportCutoff S (s + 1)) v).S.h_max ≤ (chainStateOf S.C B).h + 1) ∨
      (BoxThree (stateBefore x (supportCutoff S (s + 1)) v).S ∧ (stateBefore x (supportCutoff S (s + 1)) v).S.h_max ≤ (chainStateOf S.C B).h))
    -- the finalized blocks: on `B`'s parent's chain at the vote time of slot `s`, on `B`'s chain
    -- at the action time
    (hFw : ∀ w ∈ Hon s, (stateBefore x (voteTime S s) w).S.F.AncestorEq B.parent)
    (hFar : ∀ v ∈ Hon s, (stateBefore x (supportCutoff S (s + 1)) v).S.F.AncestorEq B)
    -- some block of `p`'s tree, on `X`'s and `p`'s finalized block's chains, reaches `p`'s
    -- `h_max − 1`
    (hHeadP : ∃ W ∈ (stateBefore x (slotStart S s) p).S.T,
      X.AncestorEq W ∧ (stateBefore x (slotStart S s) p).S.F.AncestorEq W ∧ (stateBefore x (slotStart S s) p).S.h_max - 1 ≤ (chainStateOf S.C W).h)
    -- after the action time, at the members of the next slot: `StepFrameAt` relative to `B` for
    -- every slot `s'` with `s' + 3 ≤ s''`; for the last slot `s'' − 1`, the voter's fork choice
    -- before its vote time (the first two conjuncts of `StepFrameAt S Sched x B (s'' − 2) w`)
    (hStep : ∀ s', s ≤ s' → s' + 3 ≤ s'' → ∀ w ∈ Hon (s' + 1), StepFrameAt S Sched x B s' w)
    (hStepLast : ∀ w ∈ Hon (s'' - 1),
      (fg_to_ac (stateBefore x (voteTime S (s'' - 1)) w).S).fc_root.compatible B = true ∧
      ((fg_to_ac (stateBefore x (voteTime S (s'' - 1)) w).S).fc_root.AncestorEq B →
        ∀ tree : Finset (Block V),
          voter_block_tree S.C (stateBefore x (voteTime S (s'' - 1)) w).A
            (fg_to_ac (stateBefore x (voteTime S (s'' - 1)) w).S) (s'' - 1) = .ok tree →
          ∃ W ∈ tree, W ∈ (fg_to_ac (stateBefore x (voteTime S (s'' - 1)) w).S).viable_heads ∧
            B.AncestorEq W))
    -- the quorum attests at `a`, inside slot `s`'s active window
    (hQ : Q ⊆ Hon s) (hQuorum : quorum V ≤ Q.card)
    -- the next proposer is a member of the last slot's set
    (hq : q ∈ Hon (s'' - 1))
    -- `q`'s fork-choice root before the start of slot `s''` is compatible with `B`, and when it
    -- is `B` or an ancestor of `B`, a block of `q`'s frame tree that is `B` or a descendant of `B`
    -- is a viable head
    (hFrameQ : (fg_to_ac (stateBefore x (slotStart S s'') q).S).fc_root.compatible B = true ∧
      ((fg_to_ac (stateBefore x (slotStart S s'') q).S).fc_root.AncestorEq B →
        ∃ W ∈ (fg_to_ac (stateBefore x (slotStart S s'') q).S).tree,
          W ∈ (fg_to_ac (stateBefore x (slotStart S s'') q).S).viable_heads ∧ B.AncestorEq W))
    -- `q` put `B'` on the wire at its tick at the start of slot `s''`
    (hPropose' : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s'') ∧
      (⟨q, NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) :
    B.AncestorEq B' ∧
    ((chainStateOf S.C B).h + 1 ≤ (chainStateOf S.C B').h ∨
      ((chainStateOf S.C B').h = (chainStateOf S.C B).h ∧
        Q ⊆ (chainStateOf S.C B').progress ∧
        B'.slot < (chainStateOf S.C B).T_h.slot + S.C.δt)) ∧
    ((∀ u ∈ Q, ∀ b ∈ (stateBefore x (supportCutoff S (s + 1)) u).Λ.sent,
        b.h ≠ (chainStateOf S.C B).h) →
      (chainStateOf S.C B).h + 1 ≤ (chainStateOf S.C B').h ∧
        ((chainStateOf S.C B'.parent).h = (chainStateOf S.C B).h →
          (chainStateOf S.C B').J = (chainStateOf S.C B).T_h)) :=
  GoldilocksCorrectness.Proofs.Executions.lem80wq_boxOne S Sched x GST r s s'' Hon Q Hs H X B B' p
    q hDiv hMono hSync hCatch hRoots hParent hOwner hSyncF hCatchF hs hs1 hs'' hGST hHonMono
    hHon hp hPropose hHsPrev hVotersPrev hApX hLocksW hOnly hRootNew hHs hVoters hVotersQ hHalf
    hBoxP hBoxW hBoxV hFw hFar hHeadP hStep hStepLast hQ hQuorum hq hFrameQ hPropose'

/-- **`lem80wq_round_height_advances_steps` in box 2.** Its conclusion under its hypotheses with
the frame, root and record hypotheses replaced by box facts at the three reading points of slot
`s`: `J₀ ≠ genesis`; `p` before the start of slot `s`, and each member of `Hon s` before the vote
time of slot `s` and before the action time `a`, in box 2 with the justified block `J₀`; some block
of `p`'s tree on `X`'s and `J₀`'s chains reaching `p`'s `h_max − 1`; `B`'s parent in `p`'s viable
tree; unforgeability; and fewer than a third of the validators corrupted up to `a`.

Why: in box 2 the root is `J₀` and the `head_height_floor` is `h_max − 1 = h_j`, `J₀`'s height
(Lemma 57), the same at every state read; it is at most the parent's height (the parent is a viable
head at `p`), and `J₀` is an ancestor of the parent (the root of `p`'s viable tree); when `B`'s
height is `h_max − 1`, a lock at it is on `J₀` (one justification per height,
`lockBox_of_one_justification`), which is `B`'s `T_h`.

The variables: those of `lem80wq_round_height_advances_steps`, without the roots and the
`head_height_floor` values; `J₀`: the justified block.

Read aloud: when the proposer and every member are in box 2 with one justified block, the round
raises the height or puts the progress quorum on chain.




Roots name blocks until `supportCutoff S (s'' - 1)`: the proof reads
`lem80wq_round_height_advances_steps` at the same slots, whose bound is that time. -/
theorem lem80wq_boxTwo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched)
    (GST r s s'' : ℕ) (Hon : ℕ → Finset V) (Q : Finset V) (Hs : ℕ → Finset V)
    (H : V → Block V) (X B B' J₀ : Block V) (p q : V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s'' - 1)))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    -- attestations are delivered within `Δ_F S` after `GST`
    (hSyncF : SynchronyFromWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hCatchF : CatchUpOnWake Sched x.toTrace (Δ_F S) GST fgObject)
    -- `s` is the first slot of round `r`, not the first slot of all; an attestation sent at
    -- the action time of slot `s` is delivered, within `Δ_F S`, before slot `s''` starts
    (hs : s = r * S.C.R) (hs1 : 1 ≤ s) (hs'' : supportCutoff S (s + 1) + Δ_F S ≤ slotStart S s'')
    -- the network is synchronous from the vote time of slot `s − 1`
    (hGST : GST ≤ voteTime S (s - 1))
    -- the member sets shrink from one slot to the next
    (hHonMono : ∀ s', s ≤ s' → s' + 1 < s'' → Hon (s' + 1) ⊆ Hon s')
    -- the members of slot `s'` are awake and honest from the duty window's start of slot `s'` to
    -- the support cutoff of slot `s' + 1`, and not past the start of slot `s''`
    (hHon : ∀ s', s ≤ s' → s' < s'' → ∀ v ∈ Hon s', ∀ t : ℕ,
      dutyWindowStart S s' ≤ t → t ≤ supportCutoff S (s' + 1) → t ≤ slotStart S s'' →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    -- the proposer: awake and honest from the vote time of slot `s − 1` to the start of slot `s`
    (hp : ∀ t : ℕ, voteTime S (s - 1) ≤ t → t ≤ slotStart S s →
      p ∈ Sched.awake (t : Int) ∧ p ∉ Sched.adv (t : Int))
    -- `p` put `B` on the wire at its tick at the start of slot `s`
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    -- the honest voters of slot `s − 1` vote for blocks on `X`'s chain, honest at the vote time
    -- of slot `s`
    (hHsPrev : ∀ u ∈ Hs (s - 1), u ∈ S.P.committee (s - 1) ∧
      u ∉ Sched.adv (voteTime S s : Int) ∧
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s - 1)) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u (s - 1) (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      H u ∈ (stateBefore x (voteTime S (s - 1)) u).S.T ∧ X.AncestorEq (H u))
    -- at every member of `Hon s`, the voters its vote of slot `s` counts are fewer than twice
    -- `Hs (s − 1)`
    (hVotersPrev : ∀ w ∈ Hon s, ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes S.C (stateBefore x (voteTime S s) w).A
        (fg_to_ac (stateBefore x (voteTime S s) w).S) s votes support_votes →
      voters_count votes < 2 * (Hs (s - 1)).card)
    -- `p`'s anchor is `X` or an ancestor of `X`
    (hApX : (get_anchor (stateBefore x (slotStart S s) p).A
      (fg_to_ac (stateBefore x (slotStart S s) p).S) ((slotStart S s : ℕ) : Int)).AncestorEq X)
    -- every live lock a member's revocation of slot `s` leaves is on `B`'s parent's chain
    (hLocksW : ∀ w ∈ Hon s, ∀ A' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S s) w).A
        ((voteTime S s : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S s) w).S)
        ((voteTime S s : ℕ) : Int) s = .ok A' →
      ∀ e ∈ A'.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S s) w).S) ((voteTime S s : ℕ) : Int) e =
          true → e.B.AncestorEq B.parent)
    -- `B` is the only slot-`s` block a member holds at the vote time; its root is new to `p`
    (hOnly : ∀ w ∈ Hon s, ∀ B₁ ∈ (stateBefore x (voteTime S s) w).S.T, B₁.slot = s → B₁ = B)
    (hRootNew : ∀ B₁ ∈ (stateBefore x (slotStart S s) p).S.T, B₁.root ≠ B.root)
    -- the honest voters of slot `s'` are members of `Hon s'` and of the slot's committee
    (hHs : ∀ s', s ≤ s' → s' < s'' → ∀ u ∈ Hs s', u ∈ Hon s' ∧ u ∈ S.P.committee s' ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s' ∧
        ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s') ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x[i + 1].sent - x[i].sent)
    -- the counts of slot `s'`, read at the members of `Hon s'`: the voters counted by a vote of
    -- slot `s' + 1` and the slot-`s'` voters of the pool before the support cutoff of slot
    -- `s' + 1` are fewer than twice `Hs s'`
    (hVoters : ∀ s', s ≤ s' → s' < s'' → ∀ v ∈ Hon s',
      (∀ votes support_votes : Finset (GoldfishVote V),
        CountedVotes S.C (stateBefore x (voteTime S (s' + 1)) v).A
          (fg_to_ac (stateBefore x (voteTime S (s' + 1)) v).S) (s' + 1) votes support_votes →
        voters_count votes < 2 * (Hs s').card) ∧
      voters_count ((stateBefore x (supportCutoff S (s' + 1)) v).A.pool s') < 2 * (Hs s').card)
    -- the slot-`(s'' − 1)` voters `q`'s proposal counts are fewer than twice `Hs (s'' − 1)`
    (hVotersQ : ∀ votes support_votes : Finset (GoldfishVote V),
      ProposalCountedVotes (stateBefore x (slotStart S s'') q).A
        (fg_to_ac (stateBefore x (slotStart S s'') q).S) (s'' - 1) votes support_votes →
      voters_count votes < 2 * (Hs (s'' - 1)).card)
    -- the slot-`s` committee is at most twice `Hs s`
    (hHalf : (S.P.committee s).card ≤ 2 * (Hs s).card)
    -- `J₀` is not the genesis block; `p` is in box 2 with `J₀` before the start of slot `s`, and
    -- every member of `Hon s` is too before the vote time of slot `s` and before the action time
    (hJ₀ : J₀ ≠ Block.genesis)
    (hBoxP : BoxTwo (stateBefore x (slotStart S s) p).S J₀)
    (hBoxW : ∀ w ∈ Hon s, BoxTwo (stateBefore x (voteTime S s) w).S J₀)
    (hBoxV : ∀ v ∈ Hon s, BoxTwo (stateBefore x (supportCutoff S (s + 1)) v).S J₀)
    -- some block of `p`'s tree, on `X`'s and `J₀`'s chains, reaches `p`'s `h_max − 1`; and `B`'s
    -- parent is in `p`'s viable tree
    (hHeadP : ∃ W ∈ (stateBefore x (slotStart S s) p).S.T,
      X.AncestorEq W ∧ J₀.AncestorEq W ∧ (stateBefore x (slotStart S s) p).S.h_max - 1 ≤ (chainStateOf S.C W).h)
    (hParentIn : B.parent ∈ viable_tree (fg_to_ac (stateBefore x (slotStart S s) p).S)
      (fg_to_ac (stateBefore x (slotStart S s) p).S).tree)
    -- unforgeability, and fewer than a third of the validators corrupted up to the action time
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdv : AdversaryFewerThanThirdUntil Sched (validator_count V) ((supportCutoff S (s + 1) : ℕ) : Int))
    -- after the action time, at the members of the next slot: `StepFrameAt` relative to `B` for
    -- every slot `s'` with `s' + 3 ≤ s''`; for the last slot `s'' − 1`, the voter's fork choice
    -- before its vote time (the first two conjuncts of `StepFrameAt S Sched x B (s'' − 2) w`)
    (hStep : ∀ s', s ≤ s' → s' + 3 ≤ s'' → ∀ w ∈ Hon (s' + 1), StepFrameAt S Sched x B s' w)
    (hStepLast : ∀ w ∈ Hon (s'' - 1),
      (fg_to_ac (stateBefore x (voteTime S (s'' - 1)) w).S).fc_root.compatible B = true ∧
      ((fg_to_ac (stateBefore x (voteTime S (s'' - 1)) w).S).fc_root.AncestorEq B →
        ∀ tree : Finset (Block V),
          voter_block_tree S.C (stateBefore x (voteTime S (s'' - 1)) w).A
            (fg_to_ac (stateBefore x (voteTime S (s'' - 1)) w).S) (s'' - 1) = .ok tree →
          ∃ W ∈ tree, W ∈ (fg_to_ac (stateBefore x (voteTime S (s'' - 1)) w).S).viable_heads ∧
            B.AncestorEq W))
    -- the quorum attests at `a`, inside slot `s`'s active window
    (hQ : Q ⊆ Hon s) (hQuorum : quorum V ≤ Q.card)
    -- the next proposer is a member of the last slot's set
    (hq : q ∈ Hon (s'' - 1))
    -- `q`'s fork-choice root before the start of slot `s''` is compatible with `B`, and when it
    -- is `B` or an ancestor of `B`, a block of `q`'s frame tree that is `B` or a descendant of `B`
    -- is a viable head
    (hFrameQ : (fg_to_ac (stateBefore x (slotStart S s'') q).S).fc_root.compatible B = true ∧
      ((fg_to_ac (stateBefore x (slotStart S s'') q).S).fc_root.AncestorEq B →
        ∃ W ∈ (fg_to_ac (stateBefore x (slotStart S s'') q).S).tree,
          W ∈ (fg_to_ac (stateBefore x (slotStart S s'') q).S).viable_heads ∧ B.AncestorEq W))
    -- `q` put `B'` on the wire at its tick at the start of slot `s''`
    (hPropose' : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s'') ∧
      (⟨q, NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) :
    B.AncestorEq B' ∧
    ((chainStateOf S.C B).h + 1 ≤ (chainStateOf S.C B').h ∨
      ((chainStateOf S.C B').h = (chainStateOf S.C B).h ∧
        Q ⊆ (chainStateOf S.C B').progress ∧
        B'.slot < (chainStateOf S.C B).T_h.slot + S.C.δt)) ∧
    ((∀ u ∈ Q, ∀ b ∈ (stateBefore x (supportCutoff S (s + 1)) u).Λ.sent,
        b.h ≠ (chainStateOf S.C B).h) →
      (chainStateOf S.C B).h + 1 ≤ (chainStateOf S.C B').h ∧
        ((chainStateOf S.C B'.parent).h = (chainStateOf S.C B).h →
          (chainStateOf S.C B').J = (chainStateOf S.C B).T_h)) :=
  GoldilocksCorrectness.Proofs.Executions.lem80wq_boxTwo S Sched x GST r s s'' Hon Q Hs H X B B' J₀
    p q hDiv hMono hSync hCatch hRoots hParent hOwner hSyncF hCatchF hs hs1 hs'' hGST
    hHonMono hHon hp hPropose hHsPrev hVotersPrev hApX hLocksW hOnly hRootNew hHs hVoters hVotersQ
    hHalf hJ₀ hBoxP hBoxW hBoxV hHeadP hParentIn hU hAdv hStep hStepLast hQ hQuorum hq hFrameQ
    hPropose'

/-- **`lem80wq_round_height_advances_steps` in box 3.** Its conclusion under its hypotheses with
the frame, root and record hypotheses replaced by box facts at the three reading points of slot
`s`: `p` in box 3 before the start of slot `s`; each member of `Hon s` before the vote time of slot
`s` in box 3 with `h_max` at least `p`'s and at most `h(B.parent)`, or in box 1 with `h_max` at
least `p`'s plus one and at most `h(B.parent) + 1`; each member before the action time `a` in box 3
with `h_max` at most `h(B)`, or in box 1 with `h_max` at most `h(B) + 1`; the members' finalized
blocks on `B`'s parent's chain before the vote time and on `B`'s chain before `a`; and some block of
`p`'s tree on `X`'s and `p`'s finalized block's chains reaching `p`'s `h_max`.

Why: as in box 1, with `p`'s `head_height_floor` `h_max`.

The variables: those of `lem80wq_round_height_advances_steps`, without the roots and the
`head_height_floor` values.

Read aloud: when the proposer is in box 3 and each member in box 3 or box 1 with its
`head_height_floor` between the proposer's and the parent's height, the round raises the height or
puts the progress quorum on chain.




Roots name blocks until `supportCutoff S (s'' - 1)`: the proof reads
`lem80wq_round_height_advances_steps` at the same slots, whose bound is that time. -/
theorem lem80wq_boxThree (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched)
    (GST r s s'' : ℕ) (Hon : ℕ → Finset V) (Q : Finset V) (Hs : ℕ → Finset V)
    (H : V → Block V) (X B B' : Block V) (p q : V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s'' - 1)))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    -- attestations are delivered within `Δ_F S` after `GST`
    (hSyncF : SynchronyFromWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hCatchF : CatchUpOnWake Sched x.toTrace (Δ_F S) GST fgObject)
    -- `s` is the first slot of round `r`, not the first slot of all; an attestation sent at
    -- the action time of slot `s` is delivered, within `Δ_F S`, before slot `s''` starts
    (hs : s = r * S.C.R) (hs1 : 1 ≤ s) (hs'' : supportCutoff S (s + 1) + Δ_F S ≤ slotStart S s'')
    -- the network is synchronous from the vote time of slot `s − 1`
    (hGST : GST ≤ voteTime S (s - 1))
    -- the member sets shrink from one slot to the next
    (hHonMono : ∀ s', s ≤ s' → s' + 1 < s'' → Hon (s' + 1) ⊆ Hon s')
    -- the members of slot `s'` are awake and honest from the duty window's start of slot `s'` to
    -- the support cutoff of slot `s' + 1`, and not past the start of slot `s''`
    (hHon : ∀ s', s ≤ s' → s' < s'' → ∀ v ∈ Hon s', ∀ t : ℕ,
      dutyWindowStart S s' ≤ t → t ≤ supportCutoff S (s' + 1) → t ≤ slotStart S s'' →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    -- the proposer: awake and honest from the vote time of slot `s − 1` to the start of slot `s`
    (hp : ∀ t : ℕ, voteTime S (s - 1) ≤ t → t ≤ slotStart S s →
      p ∈ Sched.awake (t : Int) ∧ p ∉ Sched.adv (t : Int))
    -- `p` put `B` on the wire at its tick at the start of slot `s`
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    -- the honest voters of slot `s − 1` vote for blocks on `X`'s chain, honest at the vote time
    -- of slot `s`
    (hHsPrev : ∀ u ∈ Hs (s - 1), u ∈ S.P.committee (s - 1) ∧
      u ∉ Sched.adv (voteTime S s : Int) ∧
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s - 1)) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u (s - 1) (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      H u ∈ (stateBefore x (voteTime S (s - 1)) u).S.T ∧ X.AncestorEq (H u))
    -- at every member of `Hon s`, the voters its vote of slot `s` counts are fewer than twice
    -- `Hs (s − 1)`
    (hVotersPrev : ∀ w ∈ Hon s, ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes S.C (stateBefore x (voteTime S s) w).A
        (fg_to_ac (stateBefore x (voteTime S s) w).S) s votes support_votes →
      voters_count votes < 2 * (Hs (s - 1)).card)
    -- `p`'s anchor is `X` or an ancestor of `X`
    (hApX : (get_anchor (stateBefore x (slotStart S s) p).A
      (fg_to_ac (stateBefore x (slotStart S s) p).S) ((slotStart S s : ℕ) : Int)).AncestorEq X)
    -- every live lock a member's revocation of slot `s` leaves is on `B`'s parent's chain
    (hLocksW : ∀ w ∈ Hon s, ∀ A' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S s) w).A
        ((voteTime S s : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S s) w).S)
        ((voteTime S s : ℕ) : Int) s = .ok A' →
      ∀ e ∈ A'.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S s) w).S) ((voteTime S s : ℕ) : Int) e =
          true → e.B.AncestorEq B.parent)
    -- `B` is the only slot-`s` block a member holds at the vote time; its root is new to `p`
    (hOnly : ∀ w ∈ Hon s, ∀ B₁ ∈ (stateBefore x (voteTime S s) w).S.T, B₁.slot = s → B₁ = B)
    (hRootNew : ∀ B₁ ∈ (stateBefore x (slotStart S s) p).S.T, B₁.root ≠ B.root)
    -- the honest voters of slot `s'` are members of `Hon s'` and of the slot's committee
    (hHs : ∀ s', s ≤ s' → s' < s'' → ∀ u ∈ Hs s', u ∈ Hon s' ∧ u ∈ S.P.committee s' ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s' ∧
        ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s') ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x[i + 1].sent - x[i].sent)
    -- the counts of slot `s'`, read at the members of `Hon s'`: the voters counted by a vote of
    -- slot `s' + 1` and the slot-`s'` voters of the pool before the support cutoff of slot
    -- `s' + 1` are fewer than twice `Hs s'`
    (hVoters : ∀ s', s ≤ s' → s' < s'' → ∀ v ∈ Hon s',
      (∀ votes support_votes : Finset (GoldfishVote V),
        CountedVotes S.C (stateBefore x (voteTime S (s' + 1)) v).A
          (fg_to_ac (stateBefore x (voteTime S (s' + 1)) v).S) (s' + 1) votes support_votes →
        voters_count votes < 2 * (Hs s').card) ∧
      voters_count ((stateBefore x (supportCutoff S (s' + 1)) v).A.pool s') < 2 * (Hs s').card)
    -- the slot-`(s'' − 1)` voters `q`'s proposal counts are fewer than twice `Hs (s'' − 1)`
    (hVotersQ : ∀ votes support_votes : Finset (GoldfishVote V),
      ProposalCountedVotes (stateBefore x (slotStart S s'') q).A
        (fg_to_ac (stateBefore x (slotStart S s'') q).S) (s'' - 1) votes support_votes →
      voters_count votes < 2 * (Hs (s'' - 1)).card)
    -- the slot-`s` committee is at most twice `Hs s`
    (hHalf : (S.P.committee s).card ≤ 2 * (Hs s).card)
    -- `p` is in box 3 before the start of slot `s`
    (hBoxP : BoxThree (stateBefore x (slotStart S s) p).S)
    -- before the vote time of slot `s`, every member of `Hon s` is in box 3 with `h_max` at least
    -- `p`'s and at most `h(B.parent)`, or in box 1 with `h_max` at least `p`'s plus one and at most
    -- `h(B.parent) + 1`
    (hBoxW : ∀ w ∈ Hon s,
      (BoxThree (stateBefore x (voteTime S s) w).S ∧ (stateBefore x (slotStart S s) p).S.h_max ≤ (stateBefore x (voteTime S s) w).S.h_max ∧
        (stateBefore x (voteTime S s) w).S.h_max ≤ (chainStateOf S.C B.parent).h) ∨
      (BoxOne (stateBefore x (voteTime S s) w).S ∧ (stateBefore x (slotStart S s) p).S.h_max + 1 ≤ (stateBefore x (voteTime S s) w).S.h_max ∧
        (stateBefore x (voteTime S s) w).S.h_max ≤ (chainStateOf S.C B.parent).h + 1))
    -- before the action time, every member of `Hon s` is in box 3 with `h_max` at most `h(B)`, or
    -- in box 1 with `h_max` at most `h(B) + 1`
    (hBoxV : ∀ v ∈ Hon s,
      (BoxThree (stateBefore x (supportCutoff S (s + 1)) v).S ∧ (stateBefore x (supportCutoff S (s + 1)) v).S.h_max ≤ (chainStateOf S.C B).h) ∨
      (BoxOne (stateBefore x (supportCutoff S (s + 1)) v).S ∧ (stateBefore x (supportCutoff S (s + 1)) v).S.h_max ≤ (chainStateOf S.C B).h + 1))
    -- the finalized blocks: on `B`'s parent's chain at the vote time of slot `s`, on `B`'s chain
    -- at the action time
    (hFw : ∀ w ∈ Hon s, (stateBefore x (voteTime S s) w).S.F.AncestorEq B.parent)
    (hFar : ∀ v ∈ Hon s, (stateBefore x (supportCutoff S (s + 1)) v).S.F.AncestorEq B)
    -- some block of `p`'s tree, on `X`'s and `p`'s finalized block's chains, reaches `p`'s
    -- `h_max`
    (hHeadP : ∃ W ∈ (stateBefore x (slotStart S s) p).S.T,
      X.AncestorEq W ∧ (stateBefore x (slotStart S s) p).S.F.AncestorEq W ∧ (stateBefore x (slotStart S s) p).S.h_max ≤ (chainStateOf S.C W).h)
    -- after the action time, at the members of the next slot: `StepFrameAt` relative to `B` for
    -- every slot `s'` with `s' + 3 ≤ s''`; for the last slot `s'' − 1`, the voter's fork choice
    -- before its vote time (the first two conjuncts of `StepFrameAt S Sched x B (s'' − 2) w`)
    (hStep : ∀ s', s ≤ s' → s' + 3 ≤ s'' → ∀ w ∈ Hon (s' + 1), StepFrameAt S Sched x B s' w)
    (hStepLast : ∀ w ∈ Hon (s'' - 1),
      (fg_to_ac (stateBefore x (voteTime S (s'' - 1)) w).S).fc_root.compatible B = true ∧
      ((fg_to_ac (stateBefore x (voteTime S (s'' - 1)) w).S).fc_root.AncestorEq B →
        ∀ tree : Finset (Block V),
          voter_block_tree S.C (stateBefore x (voteTime S (s'' - 1)) w).A
            (fg_to_ac (stateBefore x (voteTime S (s'' - 1)) w).S) (s'' - 1) = .ok tree →
          ∃ W ∈ tree, W ∈ (fg_to_ac (stateBefore x (voteTime S (s'' - 1)) w).S).viable_heads ∧
            B.AncestorEq W))
    -- the quorum attests at `a`, inside slot `s`'s active window
    (hQ : Q ⊆ Hon s) (hQuorum : quorum V ≤ Q.card)
    -- the next proposer is a member of the last slot's set
    (hq : q ∈ Hon (s'' - 1))
    -- `q`'s fork-choice root before the start of slot `s''` is compatible with `B`, and when it
    -- is `B` or an ancestor of `B`, a block of `q`'s frame tree that is `B` or a descendant of `B`
    -- is a viable head
    (hFrameQ : (fg_to_ac (stateBefore x (slotStart S s'') q).S).fc_root.compatible B = true ∧
      ((fg_to_ac (stateBefore x (slotStart S s'') q).S).fc_root.AncestorEq B →
        ∃ W ∈ (fg_to_ac (stateBefore x (slotStart S s'') q).S).tree,
          W ∈ (fg_to_ac (stateBefore x (slotStart S s'') q).S).viable_heads ∧ B.AncestorEq W))
    -- `q` put `B'` on the wire at its tick at the start of slot `s''`
    (hPropose' : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s'') ∧
      (⟨q, NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) :
    B.AncestorEq B' ∧
    ((chainStateOf S.C B).h + 1 ≤ (chainStateOf S.C B').h ∨
      ((chainStateOf S.C B').h = (chainStateOf S.C B).h ∧
        Q ⊆ (chainStateOf S.C B').progress ∧
        B'.slot < (chainStateOf S.C B).T_h.slot + S.C.δt)) ∧
    ((∀ u ∈ Q, ∀ b ∈ (stateBefore x (supportCutoff S (s + 1)) u).Λ.sent,
        b.h ≠ (chainStateOf S.C B).h) →
      (chainStateOf S.C B).h + 1 ≤ (chainStateOf S.C B').h ∧
        ((chainStateOf S.C B'.parent).h = (chainStateOf S.C B).h →
          (chainStateOf S.C B').J = (chainStateOf S.C B).T_h)) :=
  GoldilocksCorrectness.Proofs.Executions.lem80wq_boxThree S Sched x GST r s s'' Hon Q Hs H X B B'
    p q hDiv hMono hSync hCatch hRoots hParent hOwner hSyncF hCatchF hs hs1 hs'' hGST
    hHonMono hHon hp hPropose hHsPrev hVotersPrev hApX hLocksW hOnly hRootNew hHs hVoters hVotersQ
    hHalf hBoxP hBoxW hBoxV hFw hFar hHeadP hStep hStepLast hQ hQuorum hq hFrameQ hPropose'

end GoldilocksCorrectness.Statements.Executions
