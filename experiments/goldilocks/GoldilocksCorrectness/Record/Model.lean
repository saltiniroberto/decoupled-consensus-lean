module
public import GoldilocksCorrectness.Record.SlotLayout
public import GoldilocksCorrectness.Statements.Routines.WalkEndDefs

@[expose] public section

/-!
# The record of Goldilocks's routines

`GoldilocksModel V` is a model of Goldilocks, read through its interface: the slot layout; a type
for each of four kinds of value (chain state, pending pair, lock entry, node state); the five
interface routines (`initial`, `wake`, `tick`, `receive`, `relayedObjects`); the readers of a
node state, each a function of the node state alone; the model's node invariant `nodeInv`; the
chain state of a block, `chainStateOf`, with the readers of a chain state and of a pending pair;
the readers of a lock entry; the readers derived from a node state; the tie-break `tieBreak` of
the model's walk; and the readers over the objects. No member decomposes `tick` or `receive` into the routines that compute them: a
statement over the record depends on what the interface routines do, and on nothing of how they
are built. A statement written over an arbitrary model holds for every model whose facts hold;
the spec is one model, `Model.goldilocks`.

The objects (blocks, attestations, Goldfish votes, the value `fg_to_ac` returns, the times) and
the parameters (`Config`, `Provisional V`, `External V`, the root order `RootOrder`) are the
spec's own, shared by every model. A duty that broadcasts has as its value the set of its
outcomes; a routine that may raise keeps the spec's result type `DRE`. A member whose spec routine
takes the root order takes it as an instance argument.

The simp set `record_goldilocks` is declared here and filled where the spec's model is defined
(`ModelGoldilocks.lean`): a simp set is usable only in the files that import its declaration.
This file holds definitions only.
-/

set_option autoImplicit false

/-- The equations `X … = Y Model.goldilocks …` between a definition of the library or the spec and
its form over the record at the spec's model, the landed form on the left. -/
register_simp_attr record_goldilocks

namespace GoldilocksCorrectness.Record

open DC (DRE)
open GoldilocksCorrectness.Statements.Routines (TieBreak)
open Goldilocks (Config Provisional External RootOrder Block Attestation AttestationContent
  GoldfishVote NamedObject Frame FinalityPair HeightPair BlockId Height Slot Time Stamp Occurrence)

/-- A model of Goldilocks: its slot layout, its value types, its interface routines and the
readers of what they build.

Read aloud: a model of Goldilocks. -/
structure GoldilocksModel (V : Type) [DecidableEq V] [Fintype V] extends SlotLayout V where
-- BEGIN GENERATED members
  -- The type members.
  /-- Type member: the chain state of a block (the spec's `ChainState`).
      Read aloud: the type of chain states. -/
  CS : Type
  /-- Type member: a justification waiting to be finalized, a height and a block (the spec's
      `PendingPair`).
      Read aloud: the type of pending pairs. -/
  PP : Type
  /-- Type member: a lock entry, a block and a deadline (the spec's `LockEntry`).
      Read aloud: the type of lock entries. -/
  LE : Type
  /-- Type member: the state of a validator's node (the spec's `NodeState`).
      Read aloud: the type of node states. -/
  N : Type
  -- The interface family: 5 members.
  /-- Operation: `initial C v`, the node state a node of the validator `v` starts from (the spec's
      `Goldilocks.initial`).
      Read aloud: `v`'s initial state. -/
  initial : (C : Config) → (v : V) → N
  /-- Operation: `wake n t`, the node state `n` when the node wakes at the time `t`: `awakeSince`
      set to none and the clock set to `t` (the spec's `Goldilocks.wake`).
      Read aloud: `n` after a wake at `t`. -/
  wake : (n : N) → (t : Time) → N
  /-- Operation: `tick C P X n t`, the outcomes of what the node does when its clock reaches `t`:
      the node state after it and the objects broadcast, or the failure (the spec's
      `Goldilocks.tick`).
      Read aloud: the outcomes of `n`'s tick at `t`. -/
  tick : [RootOrder] → (C : Config) → (P : Provisional V) → (X : External V) → (n : N) →
      (t : Time) → Set (DRE (N × List (NamedObject V)))
  /-- Operation: `receive C P X n o`, the node state `n` when the object `o` is delivered to it,
      each kind of object to its handler (the spec's `Goldilocks.Sts.receive`).
      Read aloud: `n` after the delivery of `o`. -/
  receive : [RootOrder] → (C : Config) → (P : Provisional V) → (X : External V) → (n : N) →
      (o : NamedObject V) → N
  /-- Reader: `relayedObjects o`, the objects a validator re-sends when `o` is delivered to it: `o`,
      and a block's Goldfish votes and attestations (the spec's `Goldilocks.Sts.relayedObjects`).
      Read aloud: the objects re-sent on delivery of `o`. -/
  relayedObjects : (o : NamedObject V) → Multiset (NamedObject V)
  -- The node family: 20 members.
  /-- Reader (a field of the state): `validator n`, the validator the node runs as (the spec's
      `Goldilocks.NodeState.v`).
      Read aloud: the validator of `n`. -/
  validator : (n : N) → V
  /-- Reader (a field of the state): `clock n`, the node's clock (the spec's
      `Goldilocks.NodeState.t`).
      Read aloud: the clock of `n`. -/
  clock : (n : N) → Time
  /-- Reader (a field of the state): `awakeSince n`, the time since which the node has been awake
      without interruption, or none between a wake and the first tick after it (the spec's
      `Goldilocks.NodeState.awakeSince`).
      Read aloud: the time `n` has been awake since. -/
  awakeSince : (n : N) → Option Time
  /-- Reader (a field of the state): `tree n`, the blocks the node has accepted (the spec's
      `Goldilocks.FGState.T`).
      Read aloud: the accepted blocks of `n`. -/
  tree : (n : N) → Finset (Block V)
  /-- Reader (a field of the state): `finalized n`, the block the node has finalized (the spec's
      `Goldilocks.FGState.F`).
      Read aloud: the finalized block of `n`. -/
  finalized : (n : N) → Block V
  /-- Reader (a field of the state): `justified n`, the justified block the node holds (the spec's
      `Goldilocks.FGState.J`).
      Read aloud: the justified block of `n`. -/
  justified : (n : N) → Block V
  /-- Reader (a field of the state): `justifiedHeight n`, the height at which `justified n` was
      justified (the spec's `Goldilocks.FGState.h_j`).
      Read aloud: the justification height of `n`. -/
  justifiedHeight : (n : N) → Height
  /-- Reader (a field of the state): `attestationsHeld n`, every attestation the node has received,
      one copy of each, in the order of first acceptance (the spec's
      `Goldilocks.FGState.attestations`).
      Read aloud: the attestations `n` has received. -/
  attestationsHeld : (n : N) → List (Attestation V)
  /-- Reader (a field of the state): `votesHeld n s`, the Goldfish votes of slot `s` the node has
      admitted, in the order of admission (the spec's `Goldilocks.ACState.gf_votes`).
      Read aloud: `n`'s votes of slot `s`. -/
  votesHeld : (n : N) → (s : Slot) → List (GoldfishVote V)
  /-- Reader (a field of the state): `voteStamp n vote`, the time the node admitted the Goldfish
      vote `vote`, or none (the spec's `Goldilocks.ACState.timestamp_vote`).
      Read aloud: the time `n` admitted `vote`. -/
  voteStamp : (n : N) → (vote : GoldfishVote V) → Option Stamp
  /-- Reader (a field of the state): `blockStamp n B`, the time the node admitted the block `B`, or
      none (the spec's `Goldilocks.ACState.timestamp_block`).
      Read aloud: the time `n` admitted `B`. -/
  blockStamp : (n : N) → (B : Block V) → Option Stamp
  /-- Reader (a field of the state): `savedConfirmation n s`, the confirmation the node's update of
      slot `s` computed, or none (the spec's `Goldilocks.ACState.saved_confirmation`).
      Read aloud: `n`'s saved confirmation of slot `s`. -/
  savedConfirmation : (n : N) → (s : Slot) → Option (Block V)
  /-- Reader (a field of the state): `lockEntries n`, the lock entries the node holds (the spec's
      `Goldilocks.ACState.lock_entries`).
      Read aloud: the lock entries of `n`. -/
  lockEntries : (n : N) → Finset LE
  /-- Reader (a field of the state): `fastBlocks n`, the blocks the node's latest confirmation
      update locked by its fast test (the spec's `Goldilocks.ACState.fast_blocks`).
      Read aloud: the fast blocks of `n`. -/
  fastBlocks : (n : N) → Finset (Block V)
  /-- Reader (a field of the state): `latestConfirmed n`, the node's record of the confirmed tip
      (the spec's `Goldilocks.ACState.latest_confirmed`).
      Read aloud: the record of `n`'s confirmed tip. -/
  latestConfirmed : (n : N) → Block V
  /-- Reader (a field of the state): `sentTarget n h`, the first target the node sent at the height
      `h`, or none (the spec's `Goldilocks.SigningHistory.target`).
      Read aloud: `n`'s target at `h`. -/
  sentTarget : (n : N) → (h : Height) → Option BlockId
  /-- Reader (a field of the state): `sentTimeout n h`, whether the node sent a timeout at the
      height `h` (the spec's `Goldilocks.SigningHistory.timeout`).
      Read aloud: `n` sent a timeout at `h`. -/
  sentTimeout : (n : N) → (h : Height) → Bool
  /-- Reader (a field of the state): `sentLock n h`, the target of the node's first finality pair at
      the height `h`, or none (the spec's `Goldilocks.SigningHistory.lock`).
      Read aloud: `n`'s lock at `h`. -/
  sentLock : (n : N) → (h : Height) → Option BlockId
  /-- Reader (a field of the state): `sentAttestations n`, the contents of the attestations the node
      has sent (the spec's `Goldilocks.SigningHistory.sent`).
      Read aloud: the attestations `n` has sent. -/
  sentAttestations : (n : N) → Finset AttestationContent
  /-- Reader: `nodeInv C P X n`, the model's node invariant: what the model keeps true of every node
      state its operations reach (at the spec's model, the library's
      `GoldilocksCorrectness.Statements.Routines.NodeInv` together with the library's
      `GoldilocksCorrectness.Statements.Routines.HeightCacheAttained` of the node's FG state).
      Read aloud: the model's node invariant holds of `n`. -/
  nodeInv : (C : Config) → (P : Provisional V) → (X : External V) → (n : N) → Prop
  /-- Reader: `nodeInvCore C P X n`, the clock-free part of the model's node invariant: what the
      model keeps true of every node state its operations reach whatever the clock they run at (at
      the spec's model, the library's `NodeInvCore` together with `HeightCacheAttained` of the node's
      FG state). Read aloud: the clock-free part of the model's node invariant holds of `n`. -/
  nodeInvCore : (C : Config) → (P : Provisional V) → (X : External V) → (n : N) → Prop
  -- The chain state family: 18 members.
  /-- Operation: `chainStateOf C B`, the chain state of the block `B` (the library's
      `GoldilocksCorrectness.Statements.Routines.chainStateOf`).
      Read aloud: the chain state of `B`. -/
  chainStateOf : (C : Config) → (B : Block V) → CS
  /-- Reader (a field of the state): `cs_L σ`, the latest block of the chain state `σ` (the spec's
      `Goldilocks.ChainState.L`).
      Read aloud: the latest block of `σ`. -/
  cs_L : (σ : CS) → Block V
  /-- Reader (a field of the state): `cs_s σ`, the slot of the latest block of `σ` (the spec's
      `Goldilocks.ChainState.s`).
      Read aloud: the slot of `σ`. -/
  cs_s : (σ : CS) → Slot
  /-- Reader (a field of the state): `cs_h σ`, the current height of `σ` (the spec's
      `Goldilocks.ChainState.h`).
      Read aloud: the height of `σ`. -/
  cs_h : (σ : CS) → Height
  /-- Reader (a field of the state): `cs_T_h σ`, the block that took the chain into the height `cs_h
      σ` (the spec's `Goldilocks.ChainState.T_h`).
      Read aloud: the block that took `σ` into its height. -/
  cs_T_h : (σ : CS) → Block V
  /-- Reader (a field of the state): `cs_target_participation σ`, the validators whose target vote
      at the current height for `cs_T_h σ` has been counted (the spec's
      `Goldilocks.ChainState.target_participation`).
      Read aloud: the validators counted for the target at `σ`'s height. -/
  cs_target_participation : (σ : CS) → Finset V
  /-- Reader (a field of the state): `cs_progress σ`, the validators whose target vote or timeout at
      the current height for `cs_T_h σ` has been counted (the spec's
      `Goldilocks.ChainState.progress`).
      Read aloud: the validators counted for a target or a timeout at `σ`'s height. -/
  cs_progress : (σ : CS) → Finset V
  /-- Reader (a field of the state): `cs_pending_finality σ`, the justifications of `σ` not yet
      finalized, in increasing order of height (the spec's
      `Goldilocks.ChainState.pending_finality`).
      Read aloud: the pending justifications of `σ`. -/
  cs_pending_finality : (σ : CS) → List PP
  /-- Reader (a field of the state): `cs_finality_participation σ j`, the validators counted for the
      pending justification of height `j` (the spec's
      `Goldilocks.ChainState.finality_participation`).
      Read aloud: the validators counted for finalizing the justification of height `j`. -/
  cs_finality_participation : (σ : CS) → (j : Height) → Finset V
  /-- Reader (a field of the state): `cs_J σ`, the latest justified block of `σ` (the spec's
      `Goldilocks.ChainState.J`).
      Read aloud: the justified block of `σ`. -/
  cs_J : (σ : CS) → Block V
  /-- Reader (a field of the state): `cs_h_j σ`, the height at which `cs_J σ` was justified (the
      spec's `Goldilocks.ChainState.h_j`).
      Read aloud: the justification height of `σ`. -/
  cs_h_j : (σ : CS) → Height
  /-- Reader (a field of the state): `cs_F σ`, the latest finalized block of `σ` (the spec's
      `Goldilocks.ChainState.F`).
      Read aloud: the finalized block of `σ`. -/
  cs_F : (σ : CS) → Block V
  /-- Reader (a field of the state): `cs_h_F σ`, the height at which `cs_F σ` was justified (the
      spec's `Goldilocks.ChainState.h_F`).
      Read aloud: the finalization height of `σ`. -/
  cs_h_F : (σ : CS) → Height
  /-- Reader (a field of the state): `pp_j e`, the height at which the chain justified the block of
      `e` (the spec's `Goldilocks.PendingPair.j`).
      Read aloud: the height of the pending pair `e`. -/
  pp_j : (e : PP) → Height
  /-- Reader (a field of the state): `pp_T e`, the justified block of `e` (the spec's
      `Goldilocks.PendingPair.T`).
      Read aloud: the block of the pending pair `e`. -/
  pp_T : (e : PP) → Block V
  /-- Reader: `is_pending σ p`, whether the finality pair `p` names a pending justification of `σ`
      (the spec's `Goldilocks.is_pending`).
      Read aloud: `p` names a pending justification of `σ`. -/
  is_pending : (σ : CS) → (p : FinalityPair) → Bool
  /-- Reader: `valid_attestation σ a`, whether the attestation `a` may be included in a block whose
      parent has the chain state `σ` (the spec's `Goldilocks.valid_attestation`).
      Read aloud: `a` may be included in a child of a block with chain state `σ`. -/
  valid_attestation : (σ : CS) → (a : Attestation V) → Bool
  /-- Reader: `newest K_W l`, the last `K_W` elements of the list `l` (the spec's
      `Goldilocks.newest`).
      Read aloud: the newest `K_W` pending pairs of `l`. -/
  newest : (K_W : ℕ) → (l : List PP) → List PP
  -- The locks family: 2 members.
  /-- Reader (a field of the state): `le_B e`, the locked block of the lock entry `e` (the spec's
      `Goldilocks.LockEntry.B`).
      Read aloud: the block of `e`. -/
  le_B : (e : LE) → Block V
  /-- Reader (a field of the state): `le_d e`, the deadline of `e`: the entry is live strictly
      before it (the spec's `Goldilocks.LockEntry.d`).
      Read aloud: the deadline of `e`. -/
  le_d : (e : LE) → Time
  -- The derived (FG) family: 7 members.
  /-- Reader: `fg_contest n`, whether the node's FG state is contested (the spec's
      `Goldilocks.fg_contest`).
      Read aloud: `n`'s FG state is contested. -/
  fg_contest : (n : N) → Bool
  /-- Reader: `head_height_floor n`, the least chain-state height a viable block of the node may
      have: the greatest chain-state height of `tree n`, or one less when the node's FG state is not
      contested (the spec's `Goldilocks.head_height_floor`).
      Read aloud: the least chain-state height of a viable block of `n`. -/
  head_height_floor : (n : N) → Height
  /-- Reader: `get_fc_root n`, the node's fgroot: `justified n` when the FG state is not contested
      and the greatest chain-state height of `tree n` is one more than `justifiedHeight n`,
      `finalized n` otherwise (the spec's `Goldilocks.get_fc_root`).
      Read aloud: the fgroot of `n`. -/
  get_fc_root : (n : N) → Block V
  /-- Reader: `is_viable n B`, whether the chain-state height of `B` is at least `head_height_floor
      n` (the spec's `Goldilocks.is_viable`).
      Read aloud: `B` is viable in `n`. -/
  is_viable : (n : N) → (B : Block V) → Bool
  /-- Reader: `has_viable_descendant n B`, whether some block of `tree n` that is `B` or a
      descendant of `B` is viable in `n` (the spec's `Goldilocks.has_viable_descendant`).
      Read aloud: `B` or a descendant of `B` is viable in `n`. -/
  has_viable_descendant : (n : N) → (B : Block V) → Bool
  /-- Reader: `fg_to_ac n`, what the node's finality gadget gives its available chain: the blocks of
      `tree n` that are `finalized n` or its descendants, the fgroot, the viable heads and the
      finalized block (the spec's `Goldilocks.fg_to_ac`).
      Read aloud: what `n`'s finality gadget gives the available chain. -/
  fg_to_ac : (n : N) → Frame V
  /-- Reader: `proposal_attestations n H`, the attestations of `attestationsHeld n` that a block
      whose parent is `H` includes: valid against `H`'s chain state and not on `H`'s chain (the
      spec's `Goldilocks.proposal_attestations`).
      Read aloud: the attestations a child of `H` includes. -/
  proposal_attestations : (n : N) → (H : Block V) → List (Attestation V)
  -- The derived (client) family: 4 members.
  /-- Reader: `finality_pair n h_j J h_F`, the finality pair the node's anti-slashing record allows
      for the justification `(h_j, J)` of a source finalized at `h_F`, or none (the spec's
      `Goldilocks.finality_pair`).
      Read aloud: the finality pair `n` allows. -/
  finality_pair : (n : N) → (h_j : Height) → (J : BlockId) → (h_F : Height) → Option FinalityPair
  /-- Reader: `own_lock n h_c fp`, the lock at the height `h_c` the node's anti-slashing record
      holds, with the finality pair `fp` standing in when it is at `h_c` (the spec's
      `Goldilocks.own_lock`).
      Read aloud: the lock at `h_c` the height pair reads. -/
  own_lock : (n : N) → (h_c : Height) → (fp : Option FinalityPair) → Option BlockId
  /-- Reader: `height_pair n fields fp`, the height pair the node's anti-slashing record allows for
      the source height and block `fields`, given the finality pair `fp` (the spec's
      `Goldilocks.height_pair`).
      Read aloud: the height pair `n` allows. -/
  height_pair : (n : N) → (fields : Option (Height × BlockId)) → (fp : Option FinalityPair) →
      HeightPair
  /-- Reader: `already_sent n h T τ`, whether an attestation the node has sent at the height `h`
      forbids the vote at `h` for `T` (a timeout when `τ`) (the spec's `Goldilocks.already_sent`).
      Read aloud: `n` is forbidden the vote at `h` for `T`. -/
  already_sent : (n : N) → (h : Height) → (T : BlockId) → (τ : Bool) → Bool
  -- The derived (AC) family: 4 members.
  /-- Reader: `votesHeldSet n s`, the Goldfish votes of slot `s` the node has admitted, as a set
      (the spec's `Goldilocks.ACState.pool`).
      Read aloud: `n`'s votes of slot `s`, as a set. -/
  votesHeldSet : (n : N) → (s : Slot) → Finset (GoldfishVote V)
  /-- Reader: `is_live n t e`, whether `t` is strictly before the deadline of `e` and its block is
      in the tree of `fg_to_ac n` (the spec's `Goldilocks.is_live`).
      Read aloud: `e` is live at `t` in `n`. -/
  is_live : (n : N) → (t : Time) → (e : LE) → Bool
  /-- Reader: `is_locked n t B'`, whether some lock entry of `lockEntries n` live at `t` has a block
      that is `B'` or a descendant of `B'` (the spec's `Goldilocks.is_locked`).
      Read aloud: `B'` is locked at `t` in `n`. -/
  is_locked : (n : N) → (t : Time) → (B' : Block V) → Bool
  /-- Reader: `live_lock_vetoes n t C`, whether some lock entry of `lockEntries n` live at `t` has a
      block that conflicts with `C` (the spec's `Goldilocks.live_lock_vetoes`).
      Read aloud: a live lock of `n` at `t` conflicts with `C`. -/
  live_lock_vetoes : (n : N) → (t : Time) → (C : Block V) → Bool
  -- The derived (fork choice) family: 1 members.
  /-- Reader: `get_anchor n t`, the deepest block of the viable tree of `fg_to_ac n` that a lock
      entry of `lockEntries n` live at `t` locks, or the fgroot of `fg_to_ac n` when there is none
      (the spec's `Goldilocks.get_anchor`).
      Read aloud: the anchor of `n` at `t`. -/
  get_anchor : [RootOrder] → (n : N) → (t : Time) → Block V
  -- The tie-break family: 1 members.
  /-- Parameter: `tieBreak`, the tie-break of the model's walk: a function picking one block of each
      finite set of blocks, a member of the set when it is nonempty, and the same pick from a subset
      that still holds it (the library's
      `GoldilocksCorrectness.Proofs.Routines.goldilocksTieBreak`).
      Read aloud: the model's tie-break. -/
  tieBreak : [RootOrder] → TieBreak V
  -- The derived (confirmation) family: 3 members.
  /-- Reader: `live_entries n t`, the lock entries of `lockEntries n` live at `t` (the spec's
      `Goldilocks.live_entries`).
      Read aloud: the live lock entries of `n` at `t`. -/
  live_entries : (n : N) → (t : Time) → Finset LE
  /-- Reader: `saved_extends n s'' B`, whether `savedConfirmation n s''` is a block of the tree of
      `fg_to_ac n` that is `B` or a descendant of `B` (the spec's `Goldilocks.saved_extends`).
      Read aloud: slot `s''`'s saved confirmation in `n` extends `B`. -/
  saved_extends : (n : N) → (s'' : Slot) → (B : Block V) → Bool
  /-- Reader: `slow_test C n s' B`, whether the node's saved confirmations of the `C.k − 1` slots
      before `s'` all extend `B` (the spec's `Goldilocks.slow_test`).
      Read aloud: `B` passes `n`'s slow test of slot `s'`. -/
  slow_test : (C : Config) → (n : N) → (s' : Slot) → (B : Block V) → Bool
  -- The derived (AC interface) family: 1 members.
  /-- Reader: `ac_confirmed n`, the node's confirmed tip: `latestConfirmed n` when it is in the tree
      of `fg_to_ac n`, and the finalized block of `fg_to_ac n` otherwise (the spec's
      `Goldilocks.ac_confirmed`).
      Read aloud: the confirmed tip of `n`. -/
  ac_confirmed : (n : N) → Block V
  -- The derived (node) family: 2 members.
  /-- Reader: `awake_since n t₀`, whether the node has been awake without interruption since `t₀` or
      earlier (the spec's `Goldilocks.NodeState.awake_since`).
      Read aloud: `n` has been awake since `t₀`. -/
  awake_since : (n : N) → (t₀ : Time) → Bool
  /-- Reader: `block_admissible C P X n B`, whether the node whose state is `n` accepts the block
      `B` (the spec's `Goldilocks.block_admissible`).
      Read aloud: `n` accepts `B`. -/
  block_admissible : (C : Config) → (P : Provisional V) → (X : External V) → (n : N) →
      (B : Block V) → Bool
  -- The objects family: 20 members.
  /-- Reader: `attestations_on_chain B`, the attestations included in `B` and in each of its
      ancestors (the spec's `Goldilocks.attestations_on_chain`).
      Read aloud: the attestations of `B`'s chain. -/
  attestations_on_chain : (B : Block V) → List (Attestation V)
  /-- Reader: `on_chain a H`, whether the attestation `a` is included in `H` or in one of its
      ancestors (the spec's `Goldilocks.on_chain`).
      Read aloud: `a` is on `H`'s chain. -/
  on_chain : (a : Attestation V) → (H : Block V) → Bool
  /-- Reader: `hp_height? p`, the height of the height pair `p`, none for the empty pair (the spec's
      `Goldilocks.HeightPair.height?`).
      Read aloud: the height of `p`. -/
  hp_height? : (p : HeightPair) → Option Height
  /-- Reader: `hp_target? p`, the target the height pair `p` names, none for the empty pair and a
      timeout (the spec's `Goldilocks.HeightPair.target?`).
      Read aloud: the target of `p`. -/
  hp_target? : (p : HeightPair) → Option BlockId
  /-- Reader: `ac_valid_payload P B`, whether the Goldfish votes `B` includes are of the slot before
      `B`'s, by members of that slot's committee, and its support votes are among them (the spec's
      `Goldilocks.ac_valid_payload`).
      Read aloud: `B`'s Goldfish votes are well placed. -/
  ac_valid_payload : (P : Provisional V) → (B : Block V) → Bool
  /-- Reader: `included_votes Φ s`, the slot-`(s − 1)` Goldfish votes included in the slot-`s`
      blocks of `Φ.tree` (the spec's `Goldilocks.included_votes`).
      Read aloud: the votes the slot-`s` blocks of `Φ.tree` include. -/
  included_votes : (Φ : Frame V) → (s : Slot) → Finset (GoldfishVote V)
  /-- Reader: `included_support_votes Φ s`, the slot-`(s − 1)` support votes included in the
      slot-`s` blocks of `Φ.tree` (the spec's `Goldilocks.included_support_votes`).
      Read aloud: the support votes the slot-`s` blocks of `Φ.tree` include. -/
  included_support_votes : (Φ : Frame V) → (s : Slot) → Finset (GoldfishVote V)
  /-- Reader: `votes_by votes v`, the votes of `votes` whose validator is `v` (the spec's
      `Goldilocks.votes_by`).
      Read aloud: `v`'s votes in `votes`. -/
  votes_by : (votes : Finset (GoldfishVote V)) → (v : V) → Finset (GoldfishVote V)
  /-- Reader: `equivocates votes v`, whether `votes` holds two distinct votes of `v` (the spec's
      `Goldilocks.equivocates`).
      Read aloud: `v` equivocates in `votes`. -/
  equivocates : (votes : Finset (GoldfishVote V)) → (v : V) → Bool
  /-- Reader: `participates votes v`, whether `votes` holds a vote of `v` (the spec's
      `Goldilocks.participates`).
      Read aloud: `v` has a vote in `votes`. -/
  participates : (votes : Finset (GoldfishVote V)) → (v : V) → Bool
  /-- Reader: `no_second_vote_in late vote`, whether every vote of `late` is `vote` or a vote of
      another validator (the spec's `Goldilocks.no_second_vote_in`).
      Read aloud: `late` holds no second vote of `vote`'s validator. -/
  no_second_vote_in : (late : Finset (GoldfishVote V)) → (vote : GoldfishVote V) → Bool
  /-- Reader: `equivocators votes`, the validators with two distinct votes in `votes` (the spec's
      `Goldilocks.equivocators`).
      Read aloud: the equivocators of `votes`. -/
  equivocators : (votes : Finset (GoldfishVote V)) → Finset V
  /-- Reader: `participants votes`, the validators with a vote in `votes` (the spec's
      `Goldilocks.participants`).
      Read aloud: the participants of `votes`. -/
  participants : (votes : Finset (GoldfishVote V)) → Finset V
  /-- Reader: `voters_count votes`, the number of validators with a vote in `votes` (the spec's
      `Goldilocks.voters_count`).
      Read aloud: the number of voters in `votes`. -/
  voters_count : (votes : Finset (GoldfishVote V)) → ℕ
  /-- Reader: `viable_tree Φ tree`, the blocks of `tree` that are `Φ.fc_root` or its descendants and
      are a viable head of `Φ` in `tree` or an ancestor of one (the spec's
      `Goldilocks.viable_tree`).
      Read aloud: the viable part of `tree`. -/
  viable_tree : (Φ : Frame V) → (tree : Finset (Block V)) → Finset (Block V)
  /-- Reader: `present S`, the values held by the members of `S` that are not none (the spec's
      `Goldilocks.present`).
      Read aloud: the values present in `S`. -/
  present : {α : Type} → [DecidableEq α] → (S : Finset (Option α)) → Finset α
  /-- Reader: `advance Φ old C?`, the record of the confirmed tip `old` after the confirmation `C?`
      (the spec's `Goldilocks.advance`).
      Read aloud: `old` advanced by `C?`. -/
  advance : (Φ : Frame V) → (old : Block V) → (C? : Option (Block V)) → Block V
  /-- Reader: `slots_before s' k`, the `k − 1` slots before the slot `s'` (the spec's
      `Goldilocks.slots_before`).
      Read aloud: the `k − 1` slots before `s'`. -/
  slots_before : (s' : Slot) → (k : ℕ) → Finset Slot
  /-- Reader: `attestation_well_formed a`, whether `a`'s height is at least `1` and its finality
      pair, if any, is at a smaller height (the spec's `Goldilocks.attestation_well_formed`).
      Read aloud: `a` is well formed. -/
  attestation_well_formed : (a : Attestation V) → Bool
  /-- Reader: `block_well_formed P X B`, whether `B`'s attestations are well formed, its Goldfish
      votes well placed and its root the digest of its content (the spec's
      `Goldilocks.block_well_formed`).
      Read aloud: `B` is well formed. -/
  block_well_formed : (P : Provisional V) → (X : External V) → (B : Block V) → Bool
-- END GENERATED members

end GoldilocksCorrectness.Record
