module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Invariants
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Steps
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.FGStateDefs
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.FGStateReadersOnChain
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.FGStateReaders
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ACStore
public import GoldilocksCorrectness.Statements.Executions.InvariantStatements

@[expose] public section

/-!
# InvariantStatements, over a model

The statements of `GoldilocksCorrectness/Statements/Executions/InvariantStatements.lean` over a
model `M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: Lemma 11, the model's node
invariant `M.nodeInv` at every step, and its corollaries, each read through a consequence field of
`F.nd` (`nodeInv_poolKeyed`, `nodeInv_treeClosed`, `nodeInv_rootsNameBlocksIn`, …); Lemma 46, whose
second clause reads the greatest chain-state height `hMax M S.C n` of the node's tree and holds by
the definition of `hMax`; Lemma 57 and its corollaries, read through the record's readers.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (NodeInv)

namespace GoldilocksCorrectness.Record.Statements.Executions

open GoldilocksCorrectness.Record.Statements.Routines (FinalizedAncestorJustified
  HeightCacheBounds JustificationCacheBounds JustifiedHeight JustifiedInTree LockBelowJustified
  RecordConsistent)

open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy EnvFactsNoDelivery)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- **Lemma 11, the node invariant.** At every step of every execution, the node state of every
validator outside the adversary set after that step satisfies `NodeInv`: every Goldfish vote filed
under a slot has that slot and a validator of
that slot's committee, and is stamped; the genesis block is in the tree, and every other block of
the tree has its parent in the tree, is well formed, has its slot's proposer and a parent of an
earlier slot; the finalized block is in the tree; every block of the tree is stamped, at most the
node's clock and no earlier than its parent; every pool vote's stamp is at most the clock; the
chain states of the tree are computed from the blocks alone, and the included attestations are
valid against the parent's chain state; no two blocks of the tree share a root; every attestation
of the pool of attestations `n.attestationsHeld` is well formed (`attestation_well_formed`). The
node's validator field is the validator, and its clock is its clock value after the step.

Why: the initial node state satisfies it, and every routine that writes a node state keeps it.
The pool of attestations starts empty, and its writers add only well-formed attestations:
`on_attestation` tests `attestation_well_formed` first, and `fg_on_block` adds the attestations of
a block that passed `block_well_formed`, which tests each of them.



The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `Sched`: the schedule; `x`: the execution; `i`: the step; `v`: the
  validator; `hv`: `v` is outside the adversary set after `i` steps.


The clock-free part holds for every validator (`lem11_node_invariantCore_of_run`).

Read aloud: at every step of every execution of the model, every validator outside the adversary set
has a node state that satisfies the model's invariant, has its validator, and has as its clock its
clock value `x.clockValue i v`. -/
theorem lem11_node_invariant (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsNoDelivery A x ΔClockAhead ΔClockBehind GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (i : ℕ) (v : V)
    -- `v` is outside the adversary set after `i` steps
    (hv : v ∉ A.corrupted i) :
    M.nodeInv S.C S.P S.X (x.st i v) ∧ (x.st i v).v = v ∧
      (x.st i v).t = (x.clockValue i v : Int) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem11_node_invariant M F) S A x R (E.withClass _) i v hv

/-- Every vote of a validator's pool of slot `s` has the slot `s`, at every step.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `i`: the step; `v`: the validator;
  `s`: the slot.

Read aloud: every vote a validator holds under a slot has that slot, at every step. -/
theorem pool_slot_of_exec (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (i : ℕ) (v : V) (s : Slot) : ∀ vote ∈ M.votesHeldSet (x.st i v) s, vote.slot = s :=
  fun vote hv => ((F.nd.nodeInvCore_poolKeyed ((GoldilocksCorrectness.Record.Proofs.Executions.lem11_node_invariantCore_of_run M F) S x R i v).1) s vote
    (((GoldilocksCorrectness.Record.Proofs.Routines.mem_pool_iff M F) _ _ _).1 hv)).1

/-- Every vote of a validator's pool of slot `s` is from a member of the slot-`s` committee, at
every step.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `i`: the step; `v`: the validator;
  `s`: the slot.

Read aloud: every vote a validator holds under a slot is from that slot's committee, at every step.
-/
theorem pool_committee_of_exec (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (i : ℕ) (v : V) (s : Slot) :
    ∀ vote ∈ M.votesHeldSet (x.st i v) s, vote.val_index ∈ S.P.committee s :=
  fun vote hv => ((F.nd.nodeInvCore_poolKeyed ((GoldilocksCorrectness.Record.Proofs.Executions.lem11_node_invariantCore_of_run M F) S x R i v).1) s vote
    (((GoldilocksCorrectness.Record.Proofs.Routines.mem_pool_iff M F) _ _ _).1 hv)).2

/-- Every vote of a validator's pool of slot `s` before the time `t` has the slot `s`.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `v`: the validator;
  `s`: the slot.

Read aloud: before `t`, every vote a validator holds under a slot has that slot. -/
theorem pool_slot_of_stateBefore (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (t : ℕ) (v : V) (s : Slot) :
    ∀ vote ∈ M.votesHeldSet (x.stateBefore t v) s, vote.slot = s :=
  (pool_slot_of_exec M F) S A x R E (x.stepBefore t) v s

/-- Every vote of a validator's pool of slot `s` before the time `t` is from a member of the
slot-`s` committee.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `v`: the validator;
  `s`: the slot.

Read aloud: before `t`, every vote a validator holds under a slot is from that slot's committee. -/
theorem pool_committee_of_stateBefore (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (t : ℕ) (v : V) (s : Slot) :
    ∀ vote ∈ M.votesHeldSet (x.stateBefore t v) s, vote.val_index ∈ S.P.committee s :=
  (pool_committee_of_exec M F) S A x R E (x.stepBefore t) v s

/-- The genesis block is in every validator's tree, at every step.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `i`: the step; `v`: the
  validator.

Read aloud: every validator's tree holds the genesis block, at every step. -/
theorem genesis_mem_T_of_exec (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (i : ℕ) (v : V) :
    Block.genesis ∈ (x.st i v).tree :=
  (F.nd.nodeInvCore_treeClosed ((GoldilocksCorrectness.Record.Proofs.Executions.lem11_node_invariantCore_of_run M F) S x R i v).1).1

/-- The parent of a non-genesis block of a validator's tree is in the tree, at every step.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `i`: the step; `v`: the validator;
  `B`: the block.

Read aloud: every validator's tree holds the parent of each of its non-genesis blocks, at every
step. -/
theorem parent_mem_T_of_exec (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (i : ℕ) (v : V) (B : Block V)
    -- `B` is in the tree
    (hB : B ∈ (x.st i v).tree)
    -- `B` is not the genesis block
    (hne : B ≠ Block.genesis) :
    B.parent ∈ (x.st i v).tree :=
  ((F.nd.nodeInvCore_treeClosed ((GoldilocksCorrectness.Record.Proofs.Executions.lem11_node_invariantCore_of_run M F) S x R i v).1).2 B hB hne).1

/-- Every ancestor of a block of a validator's tree is in the tree, at every step.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `i`: the step; `v`: the validator;
  `B`: the block of the tree; `P'`: an ancestor of `B`, or `B`.

Read aloud: every validator's tree holds every ancestor of each of its blocks, at every step. -/
theorem ancestors_mem_T_of_exec (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (i : ℕ) (v : V) (B P' : Block V)
    -- `B` is in the tree
    (hB : B ∈ (x.st i v).tree)
    -- `P'` is an ancestor of `B`, or `B`
    (hP' : P'.AncestorEq B) :
    P' ∈ (x.st i v).tree :=
  GoldilocksCorrectness.Proofs.Routines.ancestors_mem
    (fun B' h1 h2 => ((F.nd.nodeInvCore_treeClosed ((GoldilocksCorrectness.Record.Proofs.Executions.lem11_node_invariantCore_of_run M F) S x R i v).1).2 B' h1 h2).1) hB hP'

/-- Every block from the finalized block to a block of the frame's tree is in the frame's tree,
for the frame `M.fg_to_ac (x[i][v].st)` a validator's FG state gives at every step.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `i`: the step; `v`: the validator;
  `B`: the block of the frame's tree; `P'`: a block between the finalized block and `B`.

Read aloud: the frame's tree holds every block between the finalized block and one of its blocks, at
every step. -/
theorem frame_path_of_exec (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (i : ℕ) (v : V) (B P' : Block V)
    -- `B` is in the frame's tree
    (hB : B ∈ (M.fg_to_ac (x.st i v)).tree)
    -- the finalized block is an ancestor of `P'`, or `P'`
    (hFP : (M.fg_to_ac (x.st i v)).F.AncestorEq P')
    -- `P'` is an ancestor of `B`, or `B`
    (hPB : P'.AncestorEq B) :
    P' ∈ (M.fg_to_ac (x.st i v)).tree :=
  ((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).2
    ⟨(ancestors_mem_T_of_exec M F) S A x R E i v B P'
      (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hB).1 hPB,
      by rwa [(GoldilocksCorrectness.Record.Proofs.Routines.fg_to_ac_F M F)] at hFP⟩

/-- No two blocks of the frame's tree of a validator share a root, at every step, for every
validator: the node invariant's "no two blocks of the tree share a root", read on the frame's tree,
whose blocks are blocks of the tree.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `i`: the step; `v`: the
  validator.

Read aloud: no two blocks of a validator's frame's tree share a root, at every step. -/
theorem rootsNameBlocksIn_frame_of_exec_node (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (i : ℕ) (v : V) :
    RootsNameBlocksIn (M.fg_to_ac (x.st i v)).tree :=
  fun B hB B' hB' hroot => (F.nd.nodeInvCore_rootsNameBlocksIn ((GoldilocksCorrectness.Record.Proofs.Executions.lem11_node_invariantCore_of_run M F) S x R i v).1) B
    (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hB).1 B'
    (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hB').1 hroot

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
- `M`: the model; `F`: its facts;
- `S`: the setup; `Sched`: the schedule; `x`: the execution; `i`: the step; `v`: the
  validator.

Read aloud: the finalized block is on the justified block's chain, and the cache `h_max` bounds
the chain-state height of every accepted block. -/
theorem lem46_finality_caches (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (i : ℕ) (v : V) :
    FinalizedAncestorJustified M (x.st i v) ∧ HeightCacheBounds M S.C (x.st i v) :=
  ⟨F.nd.nodeInvCore_finalizedAncestorJustified ((GoldilocksCorrectness.Record.Proofs.Executions.lem11_node_invariantCore_of_run M F) S x R i v).1,
    GoldilocksCorrectness.Record.Statements.Routines.heightCacheBounds M S.C _⟩

/-- A validator's finalized block is its justified block or an ancestor of it, at every step:
Lemma 46, first clause.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `i`: the step; `v`: the validator.



Read aloud: the finalized block is on the justified block's chain. -/
theorem F_ancestorEq_J_of_exec (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (i : ℕ) (v : V) :
    (x.st i v).finalized.AncestorEq (x.st i v).justified :=
  (lem46_finality_caches M F S A x R E i v).1

/-- A validator's finalized block before the time `t` is its justified block or an ancestor of
it.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `v`: the validator.



Read aloud: before `t`, the finalized block is on the justified block's chain. -/
theorem F_ancestorEq_J_of_stateBefore (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (t : ℕ) (v : V) :
    (x.stateBefore t v).finalized.AncestorEq (x.stateBefore t v).justified :=
  (F_ancestorEq_J_of_exec M F) S A x R E (x.stepBefore t) v

/-- A validator's finalized block is the root of its fork choice, `get_fc_root`, or an ancestor
of it, at every step: the root is the justified block or the finalized block, and Lemma 46's first
clause.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `i`: the step; `v`: the validator.



Read aloud: the finalized block is on the chain of the fork choice's root. -/
theorem F_ancestorEq_fc_root_of_exec (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (i : ℕ) (v : V) :
    (x.st i v).finalized.AncestorEq (M.get_fc_root (x.st i v)) :=
  (GoldilocksCorrectness.Record.Proofs.Routines.F_ancestorEq_get_fc_root_of_core M F) S.C S.P S.X _
    ((GoldilocksCorrectness.Record.Proofs.Executions.lem11_node_invariantCore_of_run M F) S x R i v).1 (lem46_finality_caches M F S A x R E i v).1

/-- A validator's finalized block before the time `t` is the root of its fork choice,
`get_fc_root`, or an ancestor of it.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `v`: the validator.



Read aloud: before `t`, the finalized block is on the chain of the fork choice's root. -/
theorem F_ancestorEq_fc_root_of_stateBefore (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (t : ℕ) (v : V) :
    (x.stateBefore t v).finalized.AncestorEq (M.get_fc_root (x.stateBefore t v)) :=
  (F_ancestorEq_fc_root_of_exec M F) S A x R E (x.stepBefore t) v

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
- `M`: the model; `F`: its facts;
- `S`: the setup; `Sched`: the schedule; `x`: the execution; `i`: the step; `v`: the
  validator.

Read aloud: the cache `h_j` is the greatest justification height on the finalized block's chain;
the justified block is accepted and sits at its justification height; a validator locks at a
height only once its own cache has a justification there; and once locked at a height, it has
never named another block there. -/
theorem lem57_justification_cache_and_record (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (i : ℕ) (v : V) :
    JustificationCacheBounds M S.C (x.st i v) ∧ JustifiedHeight M S.C (x.st i v) ∧
      JustifiedInTree M (x.st i v) ∧ LockBelowJustified M (x.st i v) ∧
      LockNamesSent M (x.st i v) :=
  have h := ((GoldilocksCorrectness.Record.Proofs.Executions.lem11_node_invariantCore_of_run M F) S x R i v).1
  ⟨F.nd.nodeInvCore_justificationCacheBounds h, F.nd.nodeInvCore_justifiedHeight h,
    F.nd.nodeInvCore_justifiedInTree h, F.nd.nodeInvCore_lockBelowJustified h,
    (GoldilocksCorrectness.Record.Proofs.Executions.lockNamesSent_of_consistent M F)
      (F.nd.nodeInvCore_recordConsistent h)⟩

/-- A validator's anti-slashing record is consistent (`RecordConsistent`), at every step: a clause
of the node invariant (Lemma 11).

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `i`: the step; `v`: the validator.



Read aloud: every validator's record is consistent. -/
theorem recordConsistent_of_exec (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (i : ℕ) (v : V) :
    RecordConsistent M (x.st i v) :=
  (F.nd.nodeInvCore_recordConsistent ((GoldilocksCorrectness.Record.Proofs.Executions.lem11_node_invariantCore_of_run M F) S x R i v).1)

omit [RootOrder] in
/-- **Corollary of Lemma 57, no lock beyond the cache.** At a height `H` greater than the cache
`n.justifiedHeight`, the record of a node state satisfying `LockBelowJustified` holds no lock.

The variables:
- `M`: the model; `F`: its facts;
- `n`: the node state; `H`: the height.



Read aloud: a validator holds no lock at a height greater than its cache `h_j`. -/
theorem lock_none_of_h_j_lt (n : M.N) (h : LockBelowJustified M n) (H : Height)
    -- the cache `h_j` is less than `H`
    (hH : n.justifiedHeight < H) : n.sentLock H = none :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lock_none_of_lockBelowJustified M F) n h H hH

/-- A validator's record holds no lock at a height `H` greater than its cache `h_j`, at every
step: Lemma 57 and its corollary `lock_none_of_h_j_lt`.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `i`: the step; `v`: the validator;
  `H`: the height.



Read aloud: no validator holds a lock at a height greater than its cache `h_j`. -/
theorem lock_none_of_h_j_lt_of_exec (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (i : ℕ) (v : V) (H : Height)
    -- the cache `h_j` is less than `H`
    (hH : (x.st i v).justifiedHeight < H) : (x.st i v).sentLock H = none :=
  (lock_none_of_h_j_lt M F) _ ((lem57_justification_cache_and_record M F) S A x R E i v).2.2.2.1 H hH

/-- A validator's record before the time `t` holds no lock at a height `H` greater than its cache
`h_j`.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `v`: the validator;
  `H`: the height.



Read aloud: before `t`, no validator holds a lock at a height greater than its cache `h_j`. -/
theorem lock_none_of_h_j_lt_of_stateBefore (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (t : ℕ) (v : V) (H : Height)
    -- the cache `h_j` is less than `H`
    (hH : (x.stateBefore t v).justifiedHeight < H) : (x.stateBefore t v).sentLock H = none :=
  (lock_none_of_h_j_lt_of_exec M F) S A x R E (x.stepBefore t) v H hH

/-- The justification height of a block of a validator's tree on its finalized block's chain is at
most its cache `h_j`, at every step: Lemma 57, first clause.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `i`: the step; `v`: the validator;
  `B`: the block.



Read aloud: the cache `h_j` bounds the justification height of every accepted block on the
finalized block's chain. -/
theorem h_j_of_mem_T_of_exec (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (i : ℕ) (v : V) (B : Block V)
    -- `B` is in the tree
    (hB : B ∈ (x.st i v).tree)
    -- the finalized block is an ancestor of `B`, or `B`
    (hFB : (x.st i v).finalized.AncestorEq B) :
    (M.chainStateOf S.C B).h_j ≤ (x.st i v).justifiedHeight :=
  ((lem57_justification_cache_and_record M F) S A x R E i v).1 B hB hFB

/-- The justification height of a block of a validator's tree before the time `t`, on its
finalized block's chain, is at most its cache `h_j`.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `v`: the validator;
  `B`: the block.



Read aloud: before `t`, the cache `h_j` bounds the justification height of every accepted block on
the finalized block's chain. -/
theorem h_j_of_mem_T_of_stateBefore (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (t : ℕ) (v : V) (B : Block V)
    -- `B` is in the tree
    (hB : B ∈ (x.stateBefore t v).tree)
    -- the finalized block is an ancestor of `B`, or `B`
    (hFB : (x.stateBefore t v).finalized.AncestorEq B) :
    (M.chainStateOf S.C B).h_j ≤ (x.stateBefore t v).justifiedHeight :=
  (h_j_of_mem_T_of_exec M F) S A x R E (x.stepBefore t) v B hB hFB

/-- At a height where a validator's record holds a lock, every attestation the record sent names
the locked block, at every step: Lemma 57, fifth clause.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `i`: the step; `v`: the validator.



Read aloud: once locked at a height, a validator has named no other block there. -/
theorem lockNamesSent_of_exec (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (i : ℕ) (v : V) : LockNamesSent M (x.st i v) :=
  ((lem57_justification_cache_and_record M F) S A x R E i v).2.2.2.2

/-- At a height where a validator's record before the time `t` holds a lock, every attestation the
record sent names the locked block.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `v`: the validator.



Read aloud: before `t`, once locked at a height, a validator has named no other block there. -/
theorem lockNamesSent_of_stateBefore (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (t : ℕ) (v : V) : LockNamesSent M (x.stateBefore t v) :=
  (lockNamesSent_of_exec M F) S A x R E (x.stepBefore t) v

/-- A target a validator's record holds at a height was sent at that height for that block, at
every step: the record's consistency (`targetRec`).

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `i`: the step; `v`: the validator.



Read aloud: a recorded target was sent. -/
theorem target_sent_of_exec (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (i : ℕ) (v : V) :
    ∀ (h : Height) (T : BlockId), (x.st i v).sentTarget h = some T →
      ∃ b ∈ (x.st i v).sentAttestations, b.h = h ∧ b.T = T :=
  (GoldilocksCorrectness.Record.Proofs.Executions.target_sent_of_consistent M F)
    ((recordConsistent_of_exec M F) S A x R E i v)

/-- A target a validator's record before the time `t` holds at a height was sent at that height
for that block.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `v`: the validator.



Read aloud: before `t`, a recorded target was sent. -/
theorem target_sent_of_stateBefore (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (t : ℕ) (v : V) :
    ∀ (h : Height) (T : BlockId), (x.stateBefore t v).sentTarget h = some T →
      ∃ b ∈ (x.stateBefore t v).sentAttestations, b.h = h ∧ b.T = T :=
  (target_sent_of_exec M F) S A x R E (x.stepBefore t) v

/-- A target a validator's record sent at a height is recorded there, at every step: the record's
consistency (`targetRec`).

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `i`: the step; `v`: the validator.



Read aloud: a sent target is recorded. -/
theorem sent_target_recorded_of_exec (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (i : ℕ) (v : V) :
    ∀ b ∈ (x.st i v).sentAttestations, b.τ = false → (x.st i v).sentTarget b.h ≠ none :=
  (GoldilocksCorrectness.Record.Proofs.Executions.sent_target_recorded_of_consistent M F)
    ((recordConsistent_of_exec M F) S A x R E i v)

/-- A target a validator's record before the time `t` sent at a height is recorded there.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `v`: the validator.



Read aloud: before `t`, a sent target is recorded. -/
theorem sent_target_recorded_of_stateBefore (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (t : ℕ) (v : V) :
    ∀ b ∈ (x.stateBefore t v).sentAttestations, b.τ = false → (x.stateBefore t v).sentTarget b.h ≠ none :=
  (sent_target_recorded_of_exec M F) S A x R E (x.stepBefore t) v

/-- A timeout a validator's record sent at a height is recorded there, at every step: the record's
consistency (`timeoutRec`).

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `i`: the step; `v`: the validator.



Read aloud: a sent timeout is recorded. -/
theorem timeout_recorded_of_exec (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (i : ℕ) (v : V) :
    ∀ b ∈ (x.st i v).sentAttestations, b.τ = true → (x.st i v).sentTimeout b.h = true :=
  (GoldilocksCorrectness.Record.Proofs.Executions.timeout_recorded_of_consistent M F)
    ((recordConsistent_of_exec M F) S A x R E i v)

/-- A timeout a validator's record before the time `t` sent at a height is recorded there.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `v`: the validator.



Read aloud: before `t`, a sent timeout is recorded. -/
theorem timeout_recorded_of_stateBefore (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (t : ℕ) (v : V) :
    ∀ b ∈ (x.stateBefore t v).sentAttestations, b.τ = true → (x.stateBefore t v).sentTimeout b.h = true :=
  (timeout_recorded_of_exec M F) S A x R E (x.stepBefore t) v

end GoldilocksCorrectness.Record.Statements.Executions

