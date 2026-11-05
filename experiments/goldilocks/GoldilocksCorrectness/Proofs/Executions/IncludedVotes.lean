module
public import GoldilocksCorrectness.Proofs.Executions.VoteDelivery
public import GoldilocksCorrectness.Proofs.Routines.Blocks

@[expose] public section

/-!
- `ancestor_blockStamp_le`: in a node state of an execution, an ancestor of a tree block is
  stamped no later than the block, by Lemma 11's `StampOrder` along the chain.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (StampOrder TreeStamped)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicAction AtomicExec Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_genesis_iff ancestorEq_node_iff)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- A Goldfish vote of an honest validator `u` that a non-genesis block of `w`'s tree before `t`
includes, for the slot of a vote `u`'s tick at `t₁ ≤ t` put on the wire, is that vote: the block
was put on the wire by `w` before `t` (`tree_block_relayed_before`), carrying the vote, so `u`'s
own tick put the vote on the wire (`VotesCastByOwner`, `u` honest then), and an honest validator's
ticks put at most one Goldfish vote per slot on the wire (`honest_vote_sent_once`).

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `t`: the time `w`'s tree is read before; `i`, `t₁`: the step and the time of `u`'s tick;
- `w`: the validator holding the block; `u`: the voter; `B`: the block;
- `vote`: the vote `u`'s tick sent; `vote'`: the vote `B` includes.

Read aloud: a vote of `u` with slot `vote.slot` found in a block `w` holds before `t`, `u` honest
at `t`, is the vote `u`'s tick at `t₁ ≤ t` put on the wire for that slot. -/
theorem included_vote_eq_of_owner (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (t i t₁ : ℕ) (w u : V) (B : Block V)
    (vote vote' : GoldfishVote V)
    -- every time is reached
    (hDiv : TimeDiverges x.toTrace)
    -- corruption is permanent
    (hMono : Sched.MonotoneCorruption)
    -- nobody votes in an honest validator's name
    (hOwner : VotesCastByOwner S Sched x)
    -- `u` is honest at `t`
    (hu : u ∉ Sched.adv (t : Int))
    -- `B` is a non-genesis block of `w`'s tree before `t`
    (hB : B ∈ (stateBefore x t w).S.T) (hBne : B ≠ Block.genesis)
    -- `B` includes `vote'`, a vote of `u`
    (hvote' : vote' ∈ B.votes) (hi' : vote'.val_index = u)
    -- the step `i` is the tick of every awake validator at `t₁ ≤ t`
    (hl : x.lbl i = AtomicAction.tickAllAwake t₁) (ht₁ : t₁ ≤ t)
    -- `u` put `vote` on the wire at the step `i`
    (hsent : (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
      x[i + 1].sent - x[i].sent)
    -- the two votes are for the same slot
    (hslot : vote'.slot = vote.slot) :
    -- then they are the same vote
    vote' = vote := by
  -- `ht₁` is not needed: a tick sends only its own slot's vote, at that slot's vote time, so a
  -- vote's slot fixes the step of the tick that sent it (`honest_vote_sent_once`)
  have _ := ht₁
  obtain ⟨j, hj, hsm, -, -⟩ := tree_block_relayed_before hMono hB hBne
  have hjt : x[j].time ≤ t :=
    le_of_lt (lt_of_le_of_lt (time_le_succ x j) ((lt_stepBefore_iff x hDiv).1 hj))
  have hhon : vote'.val_index ∉ Sched.adv (x[j].time : Int) := fun h =>
    hu (hMono _ _ (by exact_mod_cast hjt) (hi' ▸ h))
  obtain ⟨k, t', -, hlk, hsk⟩ := hOwner j _ vote' hsm (Or.inr ⟨B, rfl, hvote'⟩) hhon
  rw [hi'] at hsk
  exact honest_vote_sent_once hlk hl hsk hsent hslot

/-- In every validator's node state of an execution, an ancestor `P'` of a block `B` of the tree,
or `B` itself, is stamped no later than `B`: every block of the tree is stamped
(`TreeStamped`), and every non-genesis block of the tree is stamped no earlier than its parent,
which is in the tree (`StampOrder`, `TreeClosed`, Lemma 11).

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution; `i`: the step; `v`: the validator;
- `B`: the block of the tree; `P'`: its ancestor.

Read aloud: in a node state, an ancestor of a tree block is stamped no later than the block. -/
theorem ancestor_blockStamp_le (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (i : ℕ) (v : V) (B P' : Block V)
    -- `B` is in `v`'s tree at the step `i`
    (hB : B ∈ (x[i][v].st).S.T)
    -- `P'` is an ancestor of `B`, or `B`
    (hP : P'.AncestorEq B) :
    -- then both are stamped, `P'` no later than `B`
    ∃ τ τ' : Stamp, (x[i][v].st).A.timestamp_block P' = some τ ∧
      (x[i][v].st).A.timestamp_block B = some τ' ∧ τ ≤ τ' := by
  have hinv := (lem11_node_invariant S Sched x i v).1
  have hTS : TreeStamped (x[i][v].st) := hinv.2.2.2.2.1
  have hSO : StampOrder (x[i][v].st) := hinv.2.2.2.2.2.2.2.2.1
  revert hB hP
  induction B with
  | genesis =>
      intro _ hP
      rw [(ancestorEq_genesis_iff P').1 hP, genesis_stamp]
      exact ⟨⊥, ⊥, rfl, rfl, le_rfl⟩
  | node p s r votes support ats pr ih =>
      intro hB hP
      obtain ⟨τB, hτB⟩ := Option.ne_none_iff_exists'.1 (hTS _ hB)
      rcases (ancestorEq_node_iff P' p s r votes support ats pr).1 hP with hEq | hp
      · rw [hEq]
        exact ⟨τB, τB, hτB, hτB, le_rfl⟩
      · have hne : (Block.node p s r votes support ats pr) ≠ Block.genesis := by
          intro h
          cases h
        have hpT : p ∈ (x[i][v].st).S.T :=
          parent_mem_T_of_exec S Sched x i v _ hB hne
        obtain ⟨τ, τ₁, h1, h2, h3⟩ := ih hpT hp
        obtain ⟨τp, τB', hp1, hB1, hle⟩ := hSO _ hB hne
        have hp1' : (x[i][v].st).A.timestamp_block p = some τp := hp1
        rw [h2] at hp1'
        injection hp1' with hp1'
        rw [← hp1'] at hle
        exact ⟨τ, τB', h1, hB1, le_trans h3 hle⟩

end GoldilocksCorrectness.Proofs.Executions
