module
public import GoldilocksCorrectness.Proofs.Executions.Lemma24

@[expose] public section

/-!
# The next slot's honest Goldfish vote names the honest proposal — composed

The audited statement `lem24_goldfish_vote_names_honest_proposal_composed`, proved in
`GoldilocksCorrectness/Proofs/Executions/Lemma24.lean`. It is
`lem20_goldfish_vote_names_honest_proposal` with five of its hypotheses discharged by Lemmas 22a,
22 and 23 and by the two theorems of `GoldilocksCorrectness/Proofs/Executions/ViableAgreement.lean`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Routines (expireLocks CountedVotes)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **Lemma 24, the next slot's honest vote names the honest proposal — composed.** In an
execution where every time is reached, corruption is permanent, blocks and Goldfish votes are
delivered within `Δ` after `GST` (synchrony from the receiver's wake, and catch-up on wake),
a root names one block among what honest validators hold, a block reaches a
validator only once it holds the parent, and nobody votes in an honest validator's name: if `GST`
is at most the vote time of slot `s`; every `u ∈ Hs` is in the slot-`s` committee, honest through
the vote time `t₃` of slot `s + 1`, put its slot-`s` vote for `H u` on the wire at its tick at the
vote time of slot `s`, and holds `H u`, a block that is `X` or a descendant of `X`, in its tree
then; the validators with a vote among those `w`'s slot-`(s + 1)` vote counts are fewer than twice
`Hs`; `p` is awake and honest at every time from
the vote time of slot `s` to the start `t₁` of slot `s + 1`, and put the block `B` on the wire at its
tick at `t₁`; `w` is awake and honest at every time from the vote time of slot `s` to `t₃`, and put
the Goldfish vote `vote` on the wire at its tick at `t₃`; `w`'s tree before `t₃` holds no
slot-`(s + 1)` block other than `B`; no block of `p`'s tree before `t₁` has `B`'s root; on `p`'s
node state before `t₁`, some block of its frame's tree that is `X` or a descendant of `X` is a
viable head, and its anchor at `t₁` is `X` or an ancestor of `X`; on `w`'s node state before `t₃`,
the root of its fork choice is `B` or an ancestor of `B`, and the block of every lock entry live at
`t₃` that `w`'s revocation of slot `s + 1` leaves is `B` or an ancestor of `B`; `B` passes `w`'s
viability test (`is_viable`: its chain-state height is at least `head_height_floor` of `w`'s FG
state); and the two node states have the same least viable height (`head_height_floor`) — then
`vote`'s head is the root of `B`.

 G0F-2 (a) ("goldilocks: G0 B viable by test"), `hBViable` as `is_viable`, with `w`
holding `B` derived from Lemmas 22a and 22 under `hRootNew`; G0F-3 (a) ("goldilocks: G0
walk duplicated"), `p`'s walk re-derived by `proposal_parent_extends_majority_block`. used here, by
`child_mem_proposer_viable_tree`) and J46 (the proposer admits its own block under the named
hypothesis `hRootNew`), and the findings of the plan's section 1: F8 (`lem20`'s `hBw` follows from its `hBViable`,
so `hBViable` is split), F9 (the composition needs `p`'s walk, which `lem20` does not export), F10
(`hOnly` is needed, through `hChild`) and F11 (a block both validators hold has the same chain state
at both, `ChainStatesComputed`, so viability differs only through the two least viable heights).


- deleted the hypotheses that `p`'s and `w`'s finalized blocks are each `H u` or an ancestor of it:
  Lemma 20 and `proposal_parent_extends_majority_block` no longer take them;
- deleted the two hypotheses that each validator's finalized block is an ancestor of, or equal to,
  every block of the other's frame tree whose root is the head of a slot-`s` vote the other holds:
  Lemma 23 no longer takes them, and the blocks whose scores Lemma 20 reads (children of the
  blocks from `X` to `B`'s parent past the root of `w`'s fork choice) descend from both finalized
  blocks, through `X` at `p` and through that root at `w`;
- the root of `w`'s fork choice, and the block of every live lock entry `w`'s revocation leaves,
  are now `B`'s parent or an ancestor of it, where they were `X` or an ancestor of `X`;
- the root of `w`'s fork choice, and the block
  of every live lock entry `w`'s revocation leaves, are now `B` or an ancestor of `B`, where they
  were `B`'s parent or an ancestor of it: the proof reads the root only as an ancestor of `B`, and
  Lemma 20 takes the live locks in that form;
- `p`'s window was narrowed from "from the start of slot `s`" to "from the vote time of slot `s`",
  and `w`'s from "from the start of slot `s`" to "from the vote time of slot `s`": the windows the
  callees read are from the vote time of slot `s` to its support cutoff (Lemma 20, through
  Lemma 12, at both), from the view freeze of slot `s` to `t₁` for `p` and from `t₁` to `t₃` for
  `w` (Lemmas 22 and 23, `child_mem_proposer_viable_tree`); each window stated is the least
  interval holding both.

 the committee majority gives it through the admission invariant. `p`'s walk is now
read off `proposal_parent_walk_end`, the conclusions of `proposal_parent_extends_majority_block`
that do not read the votes; Lemma 20 derives the rest.

Why: `p`'s tick at `t₁` sent `B`, so `B`'s parent is in `p`'s viable tree or is `p`'s anchor
(`proposal_parent_walk_end`); either way `p`'s tree holds it, and `p`'s finalized block is an
ancestor of `B`. So `p` admits `B` at its tick
(Lemma 22a), and `B` reaches `w` before `t₃` (Lemma 22), where it is a viable head
(`mem_viable_heads_iff`). The two validators count alike on every block that descends from both
finalized blocks (Lemma 23). Along the path from `X` to `B`'s parent both trees hold every block
with the same chain state, so equal least viable heights give the same viable heads on the blocks
of it that descend from the root of `w`'s fork choice (`viable_heads_agree_of_floor_eq`). A child, in `w`'s viable tree, of a
block of that path, other than `B`, is on the path, or was stamped at `w` before the view freeze of
slot `s` and reached `p` by `t₁` together with a viable head descending from it
(`child_mem_proposer_viable_tree`). Lemma 20 concludes.



The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s`: the slot of the votes;
- `Hs`: the honest voters of slot `s`; `H`: the block each voter's vote is for;
- `X`: the block every vote of `Hs` extends; `B`: the block `p` proposed at the start of slot
  `s + 1`;
- `p`: the proposer of slot `s + 1`; `w`: the voter of slot `s + 1`;
- `vote`: the Goldfish vote `w` sent at the vote time of slot `s + 1`.

Read aloud: after `GST`, if the honest members `Hs` of the slot-`s` committee voted once each for
`X` or a descendant of `X`, and are more than half of the validators whose votes `w` counts for its
vote of slot `s + 1`; the honest proposer `p` of slot `s + 1` put `B` on the wire with its
anchor `X` or an ancestor of `X` and `B`'s root new to it; the honest voter `w` has, after its
revocation, every live lock on `B` or an ancestor of `B`, its fork choice rooted at `B` or an
ancestor of `B`, and no slot-`(s + 1)` block but `B`; `B` passes `w`'s viability test;
and the two validators have the same least viable height — then `w`'s vote names `B`.

Roots name blocks until `voteTime S (s + 1)`: Lemma 22 and Lemma 23, which the proof calls, take
blocks as held up to `w`'s vote time of slot `s + 1`; Lemma 20 and
`child_mem_proposer_viable_tree` read earlier. -/
theorem lem24_goldfish_vote_names_honest_proposal_composed (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s : ℕ) (Hs : Finset V) (H : V → Block V)
    (X B : Block V) (p w : V) (vote : GoldfishVote V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (voteTime S (s + 1)))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S s)
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
    (hp : ∀ t : ℕ, voteTime S s ≤ t → t ≤ slotStart S (s + 1) →
      p ∈ Sched.awake (t : Int) ∧ p ∉ Sched.adv (t : Int))
    (hw : ∀ t : ℕ, voteTime S s ≤ t → t ≤ voteTime S (s + 1) →
      w ∈ Sched.awake (t : Int) ∧ w ∉ Sched.adv (t : Int))
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    (hSend : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s + 1)) ∧
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent)
    (hOnly : ∀ B' ∈ (stateBefore x (voteTime S (s + 1)) w).S.T, B'.slot = s + 1 → B' = B)
    (hRootNew : ∀ B' ∈ (stateBefore x (slotStart S (s + 1)) p).S.T, B'.root ≠ B.root)
    (hF3p : ∃ W ∈ (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).tree,
      W ∈ (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).viable_heads ∧ X.AncestorEq W)
    (hApX : (get_anchor (stateBefore x (slotStart S (s + 1)) p).A
      (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S)
      ((slotStart S (s + 1) : ℕ) : Int)).AncestorEq X)
    (hF2w : (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).fc_root.AncestorEq B)
    (hLocksW : ∀ A' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S (s + 1)) w).A
        ((voteTime S (s + 1) : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
        ((voteTime S (s + 1) : ℕ) : Int) (s + 1) = .ok A' →
      ∀ e ∈ A'.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
          ((voteTime S (s + 1) : ℕ) : Int) e = true → e.B.AncestorEq B)
    -- `B` passes `w`'s viability test
    (hBViable : is_viable (stateBefore x (voteTime S (s + 1)) w).S B = true)
    -- the two validators have the same least viable height
    (hFloor : head_height_floor (stateBefore x (slotStart S (s + 1)) p).S =
      head_height_floor (stateBefore x (voteTime S (s + 1)) w).S) :
    vote.head = B.root :=
  GoldilocksCorrectness.Proofs.Executions.lem24_goldfish_vote_names_honest_proposal_composed S
    Sched x GST s Hs H X B p w vote hDiv hMono hSync hCatch hRoots hParent hOwner hGST hHs
    hVoters hp hw hPropose hSend hOnly hRootNew hF3p hApX hF2w hLocksW hBViable hFloor

end GoldilocksCorrectness.Statements.Executions
