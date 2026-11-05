module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.VoteDelivery
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.InvariantStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Node
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Wiring
public import GoldilocksCorrectness.Proofs.Executions.VoteDelivery
public import GoldilocksCorrectness.Proofs.Routines.Blocks
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption

@[expose] public section

/-!
# IncludedVotes, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/IncludedVotes.lean`, over a model `M` whose
facts `F` hold, for an execution `x` of `protocolOf M S`: a vote of an honest validator that a block
of a validator's tree includes is the vote its own tick put on the wire for that slot, and an
ancestor of a tree block is stamped no later than the block (the fields of the model's node
invariant, Lemma 11). The page's routine-level theorems are the facts' fields or have their twins in
phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

namespace GoldilocksCorrectness.Record.Proofs.Executions

open GoldilocksCorrectness.Record.Statements.Routines (StampOrder TreeStamped)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_genesis_iff ancestorEq_node_iff)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- A Goldfish vote of an honest validator `u` that a non-genesis block of `w`'s tree before `t`
includes, for the slot of a vote `u`'s tick at `t₁ ≤ t` put on the wire, is that vote: the block
was put on the wire by `w` before `t` (`tree_block_relayed_before`), carrying the vote, so `u`'s
own tick put the vote on the wire (`VotesCastByOwner`, `u` honest then), and an honest validator's
ticks put at most one Goldfish vote per slot on the wire (`honest_vote_sent_once`).

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `t`: the time `w`'s tree is read before; `i`, `t₁`: the step and the time of `u`'s tick;
- `w`: the validator holding the block; `u`: the voter; `B`: the block;
- `vote`: the vote `u`'s tick sent; `vote'`: the vote `B` includes.

Read aloud: a vote of `u` with slot `vote.slot` found in a block `w` holds before `t`, `u` honest
at `t`, is the vote `u`'s tick at `t₁ ≤ t` put on the wire for that slot. -/
theorem included_vote_eq_of_owner (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (t i t₁ : ℕ) (w u : V) (B : Block V)
    (vote vote' : GoldfishVote V)
    -- every time is reached
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    -- corruption is permanent
    -- nobody votes in an honest validator's name
    (hOwner : VotesCastByOwner M A x)
    -- `u` is honest at `t`
    (hu : u ∉ A.corruptedAtTime x t)
    -- `B` is a non-genesis block of `w`'s tree before `t`
    (hB : B ∈ (x.stateBefore t w).tree) (hBne : B ≠ Block.genesis)
    -- `B` includes `vote'`, a vote of `u`
    (hvote' : vote' ∈ B.votes) (hi' : vote'.val_index = u)
    -- the step `i` is the tick of every awake validator at `t₁ ≤ t`
    (hl : x.lbl i = Event.tick u t₁) (ht₁ : t₁ ≤ t)
    -- `u` put `vote` on the wire at the step `i`
    (hsent : (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
      x.sent (i + 1) - x.sent i)
    -- the two votes are for the same slot
    (hslot : vote'.slot = vote.slot) :
    -- then they are the same vote
    vote' = vote := by
  -- `ht₁` is not needed: a tick sends only its own slot's vote, at that slot's vote time, so a
  -- vote's slot fixes the step of the tick that sent it (`honest_vote_sent_once`)
  have _ := ht₁
  obtain ⟨j, hj, hsm, -, -⟩ := (tree_block_relayed_before M F R) E hB hBne
  have hjt : x.time j ≤ t :=
    le_of_lt (lt_of_le_of_lt ((time_le_succ M) x R j) (((lt_stepBefore_iff M) x R E).1 hj))
  have hhon : vote'.val_index ∉ A.corrupted j := by
    rw [hi']
    exact (not_mem_corrupted_of_le_time M) x R E hu hjt
  obtain ⟨k, t', -, hlk, hsk⟩ := hOwner j _ vote' hsm (Or.inr ⟨B, rfl, hvote'⟩) hhon
  rw [hi'] at hsk hlk
  exact (honest_vote_sent_once M F R E) hlk hl hsk hsent hslot

/-- **The included-vote uniqueness at a step.** `included_vote_eq_of_owner` with `w`'s tree read at the step `m` (a tick
input, rule R3) in place of a real time, and `u` outside the adversary set at `m`: a Goldfish vote of `u` that a
non-genesis block of `w`'s tree at `m` includes, for the slot of a vote `u`'s tick put on the wire, is that vote.

Why: the block was put on the wire by `w` at a step before `m` (`tree_block_relayed`), carrying the vote; `u` was
outside the adversary set there (the adversary set only grows, `corrupted_mono`), so `u`'s own tick put the vote on
the wire (`VotesCastByOwner`), and an honest validator's ticks put at most one Goldfish vote per slot on the wire
(`honest_vote_sent_once`).

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `x`: the execution; `R`: the run's facts; `E`: the environment's facts;
- `m`: the step `w`'s tree is read at; `i`, `t₁`: the step and the clock value of `u`'s tick;
- `w`: the validator holding the block; `u`: the voter; `B`: the block;
- `vote`: the vote `u`'s tick sent; `vote'`: the vote `B` includes.

Read aloud: a vote of `u` with slot `vote.slot` found in a block `w` holds at the step `m`, `u` honest at `m`, is the
vote `u`'s tick put on the wire for that slot. -/
theorem included_vote_eq_of_owner_st (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (m i t₁ : ℕ) (w u : V) (B : Block V)
    (vote vote' : GoldfishVote V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    -- nobody votes in an honest validator's name
    (hOwner : VotesCastByOwner M A x)
    -- `u` is outside the adversary set at `m`
    (hu : u ∉ A.corrupted m)
    -- `B` is a non-genesis block of `w`'s tree at `m`
    (hB : B ∈ (x.st m w).tree) (hBne : B ≠ Block.genesis)
    -- `B` includes `vote'`, a vote of `u`
    (hvote' : vote' ∈ B.votes) (hi' : vote'.val_index = u)
    -- `u` ticks to `t₁` at the step `i` and puts `vote` on the wire there
    (hl : x.lbl i = Event.tick u t₁)
    (hsent : (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
      x.sent (i + 1) - x.sent i)
    -- the two votes are for the same slot
    (hslot : vote'.slot = vote.slot) :
    vote' = vote := by
  obtain ⟨j, hj, hsm, -, -⟩ := (tree_block_relayed M F) x R E hB hBne
  have hhon : vote'.val_index ∉ A.corrupted j := by
    rw [hi']
    exact fun h => hu (E.corrupted_mono j m hj.le h)
  obtain ⟨k, t', -, hlk, hsk⟩ := hOwner j _ vote' hsm (Or.inr ⟨B, rfl, hvote'⟩) hhon
  rw [hi'] at hsk hlk
  exact (honest_vote_sent_once M F R E) hlk hl hsk hsent hslot

/-- In every validator's node state of an execution, an ancestor `P'` of a block `B` of the tree,
or `B` itself, is stamped no later than `B`: every block of the tree is stamped
(`TreeStamped`), and every non-genesis block of the tree is stamped no earlier than its parent,
which is in the tree (`StampOrder` by `stampOrder_of_exec`, `TreeClosed`, the clock-free part of
Lemma 11): no clock is read, so this holds for every validator.

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `Sched`: the schedule; `x`: the execution; `i`: the step; `v`: the validator;
- `B`: the block of the tree; `P'`: its ancestor.

Read aloud: in a node state, an ancestor of a tree block is stamped no later than the block. -/
theorem ancestor_blockStamp_le (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (i : ℕ) (v : V) (B P' : Block V)
    -- `B` is in `v`'s tree at the step `i`
    (hB : B ∈ (x.st i v).tree)
    -- `P'` is an ancestor of `B`, or `B`
    (hP : P'.AncestorEq B) :
    -- then both are stamped, `P'` no later than `B`
    ∃ τ τ' : Stamp, (x.st i v).blockStamp P' = some τ ∧
      (x.st i v).blockStamp B = some τ' ∧ τ ≤ τ' := by
  have hTS : TreeStamped M (x.st i v) :=
    F.nd.nodeInvCore_treeStamped ((lem11_node_invariantCore_of_run M F) S x R i v).1
  have hSO : StampOrder M (x.st i v) := (stampOrder_of_exec M F) S A x R E i v
  revert hB hP
  induction B with
  | genesis =>
      intro _ hP
      rw [(ancestorEq_genesis_iff P').1 hP, (genesis_stamp M F) x R E]
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
        have hpT : p ∈ (x.st i v).tree :=
          (GoldilocksCorrectness.Record.Statements.Executions.parent_mem_T_of_exec M F) S A x R E i v _
            hB hne
        obtain ⟨τ, τ₁, h1, h2, h3⟩ := ih hpT hp
        obtain ⟨τp, τB', hp1, hB1, hle⟩ := hSO _ hB hne
        have hp1' : (x.st i v).blockStamp p = some τp := hp1
        rw [h2] at hp1'
        injection hp1' with hp1'
        rw [← hp1'] at hle
        exact ⟨τ, τB', h1, hB1, le_trans h3 hle⟩

end GoldilocksCorrectness.Record.Proofs.Executions

