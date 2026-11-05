module
public import GoldilocksCorrectness.Proofs.Executions.Invariants

@[expose] public section

/-!
# The statements about the node invariant

Lemma 11, the node invariant `NodeInv` at every step of every execution, proved in
`GoldilocksCorrectness/Proofs/Executions/Invariants.lean`, and its corollaries, each a one-line
consequence: the pool is filed by slot and committee, the tree holds the genesis block, the
parents and the ancestors of its blocks, the frame's tree holds every block from its finalized
block to one of its blocks, no two blocks of a validator's frame's tree share a root, and the
roots of the frame's tree of an honest validator name its blocks when the roots of the honest trees
do. Lemma 46, two clauses of the node invariant on the finality caches (`lem46_finality_caches`),
and its corollaries: the finalized block is the justified block or an ancestor of it, and the root
of the fork choice or an ancestor of it. Lemma 57, the justification cache and the record
(`lem57_justification_cache_and_record`), and its corollaries: no lock at a height greater than the
cache `h_j`, the cache `h_j` bounds the justification height of every accepted block on the
finalized block's chain, every attestation sent at a locked height names the locked block, a
recorded target was sent, a sent target is recorded, and a sent timeout is recorded.
-/

set_option autoImplicit false

open scoped DC

open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (FinalizedAncestorJustified HeightCacheBounds
  JustificationCacheBounds JustifiedHeight JustifiedInTree)

open GoldilocksCorrectness.Statements.Routines (LockBelowJustified NodeInv)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec AtomicHonest Schedule)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn RecordConsistent)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **Lemma 11, the node invariant.** At every step of every execution, every validator's node
state satisfies `NodeInv`: every Goldfish vote filed under a slot has that slot and a validator of
that slot's committee, and is stamped; the genesis block is in the tree, and every other block of
the tree has its parent in the tree, is well formed, has its slot's proposer and a parent of an
earlier slot; the finalized block is in the tree; every block of the tree is stamped, at most the
node's clock and no earlier than its parent; every pool vote's stamp is at most the clock; the
chain states of the tree are computed from the blocks alone, and the included attestations are
valid against the parent's chain state; no two blocks of the tree share a root; every attestation
of the pool of attestations `n.S.attestations` is well formed (`attestation_well_formed`). The
node's validator field is the validator, and its clock is at most the framework's clock for it.

Why: the initial node state satisfies it, and every routine that writes a node state keeps it.
The pool of attestations starts empty, and its writers add only well-formed attestations:
`on_attestation` tests `attestation_well_formed` first, and `fg_on_block` adds the attestations of
a block that passed `block_well_formed`, which tests each of them.



The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution; `i`: the step; `v`: the
  validator. -/
theorem lem11_node_invariant (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (i : ℕ) (v : V) :
    NodeInv S.C S.P S.X (x[i][v].st) ∧ (x[i][v].st).v = v ∧
      ((x[i][v].st).t : Int) ≤ (x[i][v].clock : Int) :=
  GoldilocksCorrectness.Proofs.Executions.lem11_node_invariant S Sched x i v

/-- Every vote of a validator's pool of slot `s` has the slot `s`, at every step.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `i`: the step; `v`: the validator;
  `s`: the slot. -/
theorem pool_slot_of_exec (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (i : ℕ) (v : V) (s : Slot) : ∀ vote ∈ (x[i][v].st).A.pool s, vote.slot = s :=
  fun vote hv => ((lem11_node_invariant S Sched x i v).1.1 s vote
    ((GoldilocksCorrectness.Proofs.Routines.mem_pool_iff _ _ _).1 hv)).1

/-- Every vote of a validator's pool of slot `s` is from a member of the slot-`s` committee, at
every step.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `i`: the step; `v`: the validator;
  `s`: the slot. -/
theorem pool_committee_of_exec (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (i : ℕ) (v : V) (s : Slot) :
    ∀ vote ∈ (x[i][v].st).A.pool s, vote.val_index ∈ S.P.committee s :=
  fun vote hv => ((lem11_node_invariant S Sched x i v).1.1 s vote
    ((GoldilocksCorrectness.Proofs.Routines.mem_pool_iff _ _ _).1 hv)).2

/-- Every vote of a validator's pool of slot `s` before the time `t` has the slot `s`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `v`: the validator;
  `s`: the slot. -/
theorem pool_slot_of_stateBefore (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (t : ℕ) (v : V) (s : Slot) :
    ∀ vote ∈ (stateBefore x t v).A.pool s, vote.slot = s :=
  pool_slot_of_exec S Sched x (stepBefore x t) v s

/-- Every vote of a validator's pool of slot `s` before the time `t` is from a member of the
slot-`s` committee.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `v`: the validator;
  `s`: the slot. -/
theorem pool_committee_of_stateBefore (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (t : ℕ) (v : V) (s : Slot) :
    ∀ vote ∈ (stateBefore x t v).A.pool s, vote.val_index ∈ S.P.committee s :=
  pool_committee_of_exec S Sched x (stepBefore x t) v s

/-- The genesis block is in every validator's tree, at every step.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `i`: the step; `v`: the
  validator. -/
theorem genesis_mem_T_of_exec (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (i : ℕ) (v : V) :
    Block.genesis ∈ (x[i][v].st).S.T :=
  (lem11_node_invariant S Sched x i v).1.2.2.1.1

/-- The parent of a non-genesis block of a validator's tree is in the tree, at every step.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `i`: the step; `v`: the validator;
  `B`: the block. -/
theorem parent_mem_T_of_exec (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (i : ℕ) (v : V) (B : Block V)
    -- `B` is in the tree
    (hB : B ∈ (x[i][v].st).S.T)
    -- `B` is not the genesis block
    (hne : B ≠ Block.genesis) :
    B.parent ∈ (x[i][v].st).S.T :=
  ((lem11_node_invariant S Sched x i v).1.2.2.1.2 B hB hne).1

/-- Every ancestor of a block of a validator's tree is in the tree, at every step.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `i`: the step; `v`: the validator;
  `B`: the block of the tree; `P'`: an ancestor of `B`, or `B`. -/
theorem ancestors_mem_T_of_exec (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (i : ℕ) (v : V) (B P' : Block V)
    -- `B` is in the tree
    (hB : B ∈ (x[i][v].st).S.T)
    -- `P'` is an ancestor of `B`, or `B`
    (hP' : P'.AncestorEq B) :
    P' ∈ (x[i][v].st).S.T :=
  GoldilocksCorrectness.Proofs.Routines.ancestors_mem
    (fun B' h1 h2 => ((lem11_node_invariant S Sched x i v).1.2.2.1.2 B' h1 h2).1) hB hP'

/-- Every block from the finalized block to a block of the frame's tree is in the frame's tree,
for the frame `fg_to_ac (x[i][v].st).S` a validator's FG state gives at every step.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `i`: the step; `v`: the validator;
  `B`: the block of the frame's tree; `P'`: a block between the finalized block and `B`. -/
theorem frame_path_of_exec (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (i : ℕ) (v : V) (B P' : Block V)
    -- `B` is in the frame's tree
    (hB : B ∈ (fg_to_ac (x[i][v].st).S).tree)
    -- the finalized block is an ancestor of `P'`, or `P'`
    (hFP : (fg_to_ac (x[i][v].st).S).F.AncestorEq P')
    -- `P'` is an ancestor of `B`, or `B`
    (hPB : P'.AncestorEq B) :
    P' ∈ (fg_to_ac (x[i][v].st).S).tree :=
  (GoldilocksCorrectness.Proofs.Routines.mem_fg_to_ac_tree _ _).2
    ⟨ancestors_mem_T_of_exec S Sched x i v B P'
      ((GoldilocksCorrectness.Proofs.Routines.mem_fg_to_ac_tree _ _).1 hB).1 hPB,
      by rwa [GoldilocksCorrectness.Proofs.Routines.fg_to_ac_F] at hFP⟩

/-- No two blocks of the frame's tree of a validator share a root, at every step, for every
validator: the node invariant's "no two blocks of the tree share a root", read on the frame's tree,
whose blocks are blocks of the tree.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `i`: the step; `v`: the
  validator. -/
theorem rootsNameBlocksIn_frame_of_exec_node (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (i : ℕ) (v : V) :
    RootsNameBlocksIn (fg_to_ac (x[i][v].st).S).tree :=
  fun B hB B' hB' hroot => (lem11_node_invariant S Sched x i v).1.2.2.2.2.2.2.2.2.2.1.1 B
    ((GoldilocksCorrectness.Proofs.Routines.mem_fg_to_ac_tree _ _).1 hB).1 B'
    ((GoldilocksCorrectness.Proofs.Routines.mem_fg_to_ac_tree _ _).1 hB').1 hroot

/-- **Lemma 46, the finality caches.** At every step of every execution, every validator's
finalized block is its justified block or an ancestor of it (`FinalizedAncestorJustified`), and no
block of its tree has a chain-state height greater than its cache `h_max` (`HeightCacheBounds`).

Why: two clauses of the node invariant (Lemma 11, `lem11_node_invariant`). The initial state has
the genesis block as both, and the height `1` as the cache and as every chain state's height. The
finality update writes a new justified block only when the finalized block is it or an ancestor
of it, and a new finalized block only when it is the justified block or an ancestor of it; it
raises `h_max` to at least the height of the chain state it reads, which `fg_on_block` gives as
the new block's. No other routine writes the finalized block, the justified block, the tree, the
chain states or `h_max`.



The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution; `i`: the step; `v`: the
  validator.

Read aloud: the finalized block is on the justified block's chain, and the cache `h_max` bounds
the chain-state height of every accepted block. -/
theorem lem46_finality_caches (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (i : ℕ) (v : V) :
    FinalizedAncestorJustified (x[i][v].st).S ∧ HeightCacheBounds (x[i][v].st).S :=
  (lem11_node_invariant S Sched x i v).1.2.2.2.2.2.2.2.2.2.1.2.1

/-- A validator's finalized block is its justified block or an ancestor of it, at every step:
Lemma 46, first clause.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `i`: the step; `v`: the validator.



Read aloud: the finalized block is on the justified block's chain. -/
theorem F_ancestorEq_J_of_exec (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (i : ℕ) (v : V) :
    (x[i][v].st).S.F.AncestorEq (x[i][v].st).S.J :=
  (lem46_finality_caches S Sched x i v).1

/-- A validator's finalized block before the time `t` is its justified block or an ancestor of
it.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `v`: the validator.



Read aloud: before `t`, the finalized block is on the justified block's chain. -/
theorem F_ancestorEq_J_of_stateBefore (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (t : ℕ) (v : V) :
    (stateBefore x t v).S.F.AncestorEq (stateBefore x t v).S.J :=
  F_ancestorEq_J_of_exec S Sched x (stepBefore x t) v

/-- A validator's finalized block is the root of its fork choice, `get_fc_root`, or an ancestor
of it, at every step: the root is the justified block or the finalized block, and Lemma 46's first
clause.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `i`: the step; `v`: the validator.



Read aloud: the finalized block is on the chain of the fork choice's root. -/
theorem F_ancestorEq_fc_root_of_exec (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (i : ℕ) (v : V) :
    (x[i][v].st).S.F.AncestorEq (get_fc_root (x[i][v].st).S) :=
  GoldilocksCorrectness.Proofs.Routines.F_ancestorEq_get_fc_root _
    (lem46_finality_caches S Sched x i v).1

/-- A validator's finalized block before the time `t` is the root of its fork choice,
`get_fc_root`, or an ancestor of it.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `v`: the validator.



Read aloud: before `t`, the finalized block is on the chain of the fork choice's root. -/
theorem F_ancestorEq_fc_root_of_stateBefore (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (t : ℕ) (v : V) :
    (stateBefore x t v).S.F.AncestorEq (get_fc_root (stateBefore x t v).S) :=
  F_ancestorEq_fc_root_of_exec S Sched x (stepBefore x t) v

/-- **Lemma 57, the justification cache and the record.** At every step of every execution, every
validator's node state satisfies: no block of its tree on its finalized block's chain has a
justification height greater than its cache `h_j` (`JustificationCacheBounds`); its justified
block is the genesis block or has the chain-state height `h_j` (`JustifiedHeight`); its justified
block is in its tree (`JustifiedInTree`); every lock of its anti-slashing record is at a height at
most `h_j` (`LockBelowJustified`); and at a height where its record holds a lock, every attestation
the record sent names the locked block (`LockNamesSent`).

Why: the first four are clauses of the node invariant (Lemma 11, `lem11_node_invariant`). The
finality update writes the accepted block's justified block and justification height, or keeps
the cache when that justification is not greater, or when its justified block is not on the
finalized block's chain, and then it is an ancestor of the finalized block, of height at most
`h_j`. The attestation duty writes a lock only at the justification height of a head of the tree on
the finalized block's chain. The fifth follows from the record's consistency (Lemma 72): a lock is
the block of a finality pair the record sent, and every attestation sent at its height names it.



The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution; `i`: the step; `v`: the
  validator.

Read aloud: the cache `h_j` is the greatest justification height on the finalized block's chain;
the justified block is accepted and sits at its justification height; a validator locks at a
height only once its own cache has a justification there; and once locked at a height, it has
never named another block there. -/
theorem lem57_justification_cache_and_record (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (i : ℕ) (v : V) :
    JustificationCacheBounds (x[i][v].st).S ∧ JustifiedHeight (x[i][v].st).S ∧
      JustifiedInTree (x[i][v].st).S ∧ LockBelowJustified (x[i][v].st) ∧
      LockNamesSent (x[i][v].st).Λ :=
  have h := (lem11_node_invariant S Sched x i v).1.2.2.2.2.2.2.2.2.2.1.2.2
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1,
    GoldilocksCorrectness.Proofs.Executions.lockNamesSent_of_consistent h.2.2.2.2⟩

/-- A validator's anti-slashing record is consistent (`RecordConsistent`), at every step: a clause
of the node invariant (Lemma 11).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `i`: the step; `v`: the validator.



Read aloud: every validator's record is consistent. -/
theorem recordConsistent_of_exec (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (i : ℕ) (v : V) :
    RecordConsistent (x[i][v].st).Λ :=
  (lem11_node_invariant S Sched x i v).1.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2

omit [DecidableEq V] [Fintype V] [RootOrder] in
/-- **Corollary of Lemma 57, no lock beyond the cache.** At a height `H` greater than the cache
`n.S.h_j`, the record of a node state satisfying `LockBelowJustified` holds no lock.

The variables:
- `n`: the node state; `H`: the height.



Read aloud: a validator holds no lock at a height greater than its cache `h_j`. -/
theorem lock_none_of_h_j_lt (n : NodeState V) (h : LockBelowJustified n) (H : Height)
    -- the cache `h_j` is less than `H`
    (hH : n.S.h_j < H) : n.Λ.lock H = none :=
  GoldilocksCorrectness.Proofs.Executions.lock_none_of_lockBelowJustified n h H hH

/-- A validator's record holds no lock at a height `H` greater than its cache `h_j`, at every
step: Lemma 57 and its corollary `lock_none_of_h_j_lt`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `i`: the step; `v`: the validator;
  `H`: the height.



Read aloud: no validator holds a lock at a height greater than its cache `h_j`. -/
theorem lock_none_of_h_j_lt_of_exec (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (i : ℕ) (v : V) (H : Height)
    -- the cache `h_j` is less than `H`
    (hH : (x[i][v].st).S.h_j < H) : (x[i][v].st).Λ.lock H = none :=
  lock_none_of_h_j_lt _ (lem57_justification_cache_and_record S Sched x i v).2.2.2.1 H hH

/-- A validator's record before the time `t` holds no lock at a height `H` greater than its cache
`h_j`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `v`: the validator;
  `H`: the height.



Read aloud: before `t`, no validator holds a lock at a height greater than its cache `h_j`. -/
theorem lock_none_of_h_j_lt_of_stateBefore (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (t : ℕ) (v : V) (H : Height)
    -- the cache `h_j` is less than `H`
    (hH : (stateBefore x t v).S.h_j < H) : (stateBefore x t v).Λ.lock H = none :=
  lock_none_of_h_j_lt_of_exec S Sched x (stepBefore x t) v H hH

/-- The justification height of a block of a validator's tree on its finalized block's chain is at
most its cache `h_j`, at every step: Lemma 57, first clause.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `i`: the step; `v`: the validator;
  `B`: the block.



Read aloud: the cache `h_j` bounds the justification height of every accepted block on the
finalized block's chain. -/
theorem h_j_of_mem_T_of_exec (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (i : ℕ) (v : V) (B : Block V)
    -- `B` is in the tree
    (hB : B ∈ (x[i][v].st).S.T)
    -- the finalized block is an ancestor of `B`, or `B`
    (hFB : (x[i][v].st).S.F.AncestorEq B) :
    ((x[i][v].st).S.σ B).h_j ≤ (x[i][v].st).S.h_j :=
  (lem57_justification_cache_and_record S Sched x i v).1 B hB hFB

/-- The justification height of a block of a validator's tree before the time `t`, on its
finalized block's chain, is at most its cache `h_j`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `v`: the validator;
  `B`: the block.



Read aloud: before `t`, the cache `h_j` bounds the justification height of every accepted block on
the finalized block's chain. -/
theorem h_j_of_mem_T_of_stateBefore (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (t : ℕ) (v : V) (B : Block V)
    -- `B` is in the tree
    (hB : B ∈ (stateBefore x t v).S.T)
    -- the finalized block is an ancestor of `B`, or `B`
    (hFB : (stateBefore x t v).S.F.AncestorEq B) :
    ((stateBefore x t v).S.σ B).h_j ≤ (stateBefore x t v).S.h_j :=
  h_j_of_mem_T_of_exec S Sched x (stepBefore x t) v B hB hFB

/-- At a height where a validator's record holds a lock, every attestation the record sent names
the locked block, at every step: Lemma 57, fifth clause.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `i`: the step; `v`: the validator.



Read aloud: once locked at a height, a validator has named no other block there. -/
theorem lockNamesSent_of_exec (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (i : ℕ) (v : V) : LockNamesSent (x[i][v].st).Λ :=
  (lem57_justification_cache_and_record S Sched x i v).2.2.2.2

/-- At a height where a validator's record before the time `t` holds a lock, every attestation the
record sent names the locked block.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `v`: the validator.



Read aloud: before `t`, once locked at a height, a validator has named no other block there. -/
theorem lockNamesSent_of_stateBefore (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (t : ℕ) (v : V) : LockNamesSent (stateBefore x t v).Λ :=
  lockNamesSent_of_exec S Sched x (stepBefore x t) v

/-- A target a validator's record holds at a height was sent at that height for that block, at
every step: the record's consistency (`targetRec`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `i`: the step; `v`: the validator.



Read aloud: a recorded target was sent. -/
theorem target_sent_of_exec (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (i : ℕ) (v : V) :
    ∀ (h : Height) (T : BlockId), (x[i][v].st).Λ.target h = some T →
      ∃ b ∈ (x[i][v].st).Λ.sent, b.h = h ∧ b.T = T :=
  GoldilocksCorrectness.Proofs.Executions.target_sent_of_consistent
    (recordConsistent_of_exec S Sched x i v)

/-- A target a validator's record before the time `t` holds at a height was sent at that height
for that block.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `v`: the validator.



Read aloud: before `t`, a recorded target was sent. -/
theorem target_sent_of_stateBefore (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (t : ℕ) (v : V) :
    ∀ (h : Height) (T : BlockId), (stateBefore x t v).Λ.target h = some T →
      ∃ b ∈ (stateBefore x t v).Λ.sent, b.h = h ∧ b.T = T :=
  target_sent_of_exec S Sched x (stepBefore x t) v

/-- A target a validator's record sent at a height is recorded there, at every step: the record's
consistency (`targetRec`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `i`: the step; `v`: the validator.



Read aloud: a sent target is recorded. -/
theorem sent_target_recorded_of_exec (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (i : ℕ) (v : V) :
    ∀ b ∈ (x[i][v].st).Λ.sent, b.τ = false → (x[i][v].st).Λ.target b.h ≠ none :=
  GoldilocksCorrectness.Proofs.Executions.sent_target_recorded_of_consistent
    (recordConsistent_of_exec S Sched x i v)

/-- A target a validator's record before the time `t` sent at a height is recorded there.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `v`: the validator.



Read aloud: before `t`, a sent target is recorded. -/
theorem sent_target_recorded_of_stateBefore (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (t : ℕ) (v : V) :
    ∀ b ∈ (stateBefore x t v).Λ.sent, b.τ = false → (stateBefore x t v).Λ.target b.h ≠ none :=
  sent_target_recorded_of_exec S Sched x (stepBefore x t) v

/-- A timeout a validator's record sent at a height is recorded there, at every step: the record's
consistency (`timeoutRec`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `i`: the step; `v`: the validator.



Read aloud: a sent timeout is recorded. -/
theorem timeout_recorded_of_exec (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (i : ℕ) (v : V) :
    ∀ b ∈ (x[i][v].st).Λ.sent, b.τ = true → (x[i][v].st).Λ.timeout b.h = true :=
  GoldilocksCorrectness.Proofs.Executions.timeout_recorded_of_consistent
    (recordConsistent_of_exec S Sched x i v)

/-- A timeout a validator's record before the time `t` sent at a height is recorded there.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `v`: the validator.



Read aloud: before `t`, a sent timeout is recorded. -/
theorem timeout_recorded_of_stateBefore (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (t : ℕ) (v : V) :
    ∀ b ∈ (stateBefore x t v).Λ.sent, b.τ = true → (stateBefore x t v).Λ.timeout b.h = true :=
  timeout_recorded_of_exec S Sched x (stepBefore x t) v

end GoldilocksCorrectness.Statements.Executions
