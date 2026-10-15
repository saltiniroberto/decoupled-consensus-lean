module
public import Model.Sts
public import Model.Vocabulary.Protocol.Evidence
public import StsMultisetLog.Spec.AtomicExecution

@[expose] public section

/-!
# The interface over the execution

The readers of a validator's node state, honesty through an instant, the execution-indexed
definitions of proposed blocks, blocks in play, root collision-freedom and slashing evidence, and
the structure `Interface` with its binding `interface S Sched`. `S : Setup V` is the fixed protocol
data, `Sched : Schedule V` the sts framework's schedule, and `x : AtomicExec (protocol S) Sched` its
execution of the wired protocol.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol (get_confirmed get_stable proposal_time derive_named
  HeightConfig)

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Readers of the node state -/

namespace Read

/-- The finalized block of the node state `n`: the block its store records as finalized. -/
def finalized (n : NamedNodeState V) : Block V := n.st.core.F

/-- The confirmed block of the node state `n`, the output a client reads as confirmed: the
    store's confirmation record when the stable block of `n` is an ancestor of it or equal to
    it, and that stable block otherwise. -/
def confirmed (n : NamedNodeState V) : Block V := Protocol.get_confirmed n.st.core

/-- The stable block of the node state `n`, the output a client reads as stable: the store's
    stable record when the finalized block of `n` is an ancestor of it or equal to it, and
    that finalized block otherwise. -/
def stable (n : NamedNodeState V) : Block V := Protocol.get_stable n.st.core

/-- The named blocks the node state `n` holds: the blocks, with their payloads, whose bodies
    its store keeps. -/
def blocks (n : NamedNodeState V) : Finset (NamedBlock V) := n.st.bodies

end Read

/-! ## Honesty through an instant -/

/-- `v` is honest through the instant `t`: no instant at or before `t` has `v` in the schedule's
    adversary set. -/
def HonestThroughTime (Sched : Schedule V) (t : Int) (v : V) : Prop :=
  ∀ t' ≤ t, v ∉ Sched.adv t'

/-- `v` is honest through the time of the configuration after `i` steps: no instant at or before
    `x[i].time` has `v` in the schedule's adversary set. -/
def HonestThrough {S : Setup V} (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (i : Nat) (v : V) : Prop :=
  ∀ t' ≤ (x[i].time : Int), v ∉ Sched.adv t'

/-! ## Execution-indexed definitions -/

/-- After `i` steps the sent log `x[i].sent` holds a message signed by `S.E.proposer s` whose
    payload is a named block of slot `s`, authored by that proposer, whose erasure is `B`. -/
def proposedBlockAtStep (S : Setup V) {Sched : Schedule V}
    (x : AtomicExec (protocol S) Sched) (i : Nat) (s : Slot) (B : Block V) : Prop :=
  ∃ B' : NamedBlock V,
    (⟨S.E.proposer s, .block B'⟩ : SignedMsg V (NamedObject V)) ∈ x[i].sent ∧
      B'.erase = B ∧ B'.slot = s ∧ B'.proposer? = some (S.E.proposer s)

/-- The named block `B` is in play: some configuration's sent log holds a message whose payload is
    `B`, or some validator honest through some configuration's time holds `B` among the bodies of
    its store there. -/
def directBlockInLog (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (B : NamedBlock V) : Prop :=
  (∃ (i : Nat) (sm : SignedMsg V (NamedObject V)), sm ∈ x[i].sent ∧ sm.msg = .block B) ∨
    (∃ (i : Nat) (v : V), HonestThrough Sched x i v ∧ B ∈ Read.blocks x[i][v].st)

/-- The named block `A` is an ancestor of, or equal to, a block in play (`directBlockInLog`). -/
def blockInLog (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (A : NamedBlock V) : Prop :=
  ∃ B : NamedBlock V, directBlockInLog S Sched x B ∧ NamedBlock.Preceq A B

/-- Roots identify blocks among the ancestors of the blocks in play: equal roots force equal blocks. -/
structure RootCollisionFreeInLog (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) : Prop where
  /-- Equal roots among the ancestors of two blocks in play force equality. -/
  root_injective : ∀ B C : NamedBlock V,
    blockInLog S Sched x B → blockInLog S Sched x C →
    ∀ A D : NamedBlock V,
      (NamedBlock.Preceq A B ∨ NamedBlock.Preceq A C) →
      (NamedBlock.Preceq D B ∨ NamedBlock.Preceq D C) → A.root = D.root → A = D

/-- Two validators' stores, at two steps of the execution, hold between their attestations a pair
    that slashes `v`. -/
def slashesInLog (S : Setup V) {Sched : Schedule V} (x : AtomicExec (protocol S) Sched)
    (v : V) : Prop :=
  ∃ (u u' : V) (i j : Nat),
    SlashableBetween (store_attestations (x[i][u].st).st.core)
      (store_attestations (x[j][u'].st).st.core) v

/-! ## Certificate finalization -/

/-- Replaying the chain of the named block `C` leaves the finalized block `T` at height `h`. -/
def NamedFinalizedAt (E : Env V) (cfg : HeightConfig) (C : NamedBlock V) (T : Block V)
    (h : Height) : Prop :=
  (derive_named E cfg C).F = T ∧ (derive_named E cfg C).h_F = h

/-! ## The interface -/

/-- The interface the statements read: the outputs of a node state, the proposal schedule, the
    committees, the certificates, and the execution-indexed facts about blocks and evidence. -/
structure Interface (S : Setup V) (Sched : Schedule V) where
  /-- The confirmed output of a node state. -/
  confirmed : NamedNodeState V → Block V
  /-- The stable output of a node state. -/
  stable : NamedNodeState V → Block V
  /-- The finalized output of a node state. -/
  finalized : NamedNodeState V → Block V
  /-- The proposer of slot `s`. -/
  proposer : Slot → V
  /-- The proposal instant of slot `s`. -/
  proposalTime : Slot → Int
  /-- `proposedBlock x i s B`: after `i` steps the sent log holds slot `s`'s proposer's own signed
      block for slot `s`, erasing to `B`. -/
  proposedBlock : AtomicExec (protocol S) Sched → Nat → Slot → Block V → Prop
  /-- Slots at which a period opens. -/
  opening : Slot → Prop
  /-- The committee of a proposal slot. -/
  committee : Slot → Finset V
  /-- A finality certificate. -/
  Certificate : Type
  /-- Certificate `c` finalizes target `T`. -/
  finalizes : Certificate → Block V → Prop
  /-- The certificate roots satisfy the model's collision-free idealization. -/
  collisionFree : Certificate → Certificate → Prop
  /-- Two certificates contain slashable evidence. -/
  evidence : Certificate → Certificate → Prop
  /-- Two node states hold slashable evidence against each other. -/
  slashable : NamedNodeState V → NamedNodeState V → Prop
  /-- Certificate `c` is attributable to blocks the execution put in play. -/
  inRun : AtomicExec (protocol S) Sched → Certificate → Prop
  /-- The hash idealization the protocol assumes on the blocks of an execution. -/
  idealization : AtomicExec (protocol S) Sched → Prop
  /-- Two states of the execution, at any validators and any steps, hold evidence
      attributable to `v`. -/
  slashes : AtomicExec (protocol S) Sched → V → Prop

/-- The binding of every interface field for the wired protocol. -/
def interface (S : Setup V) (Sched : Schedule V) : Interface S Sched where
  confirmed := fun n => Read.confirmed n
  stable := fun n => Read.stable n
  finalized := fun n => Read.finalized n
  proposer := S.E.proposer
  proposalTime := proposal_time S.E
  proposedBlock := fun x i s B => proposedBlockAtStep S x i s B
  opening := fun s => ∃ r : Round, s = S.hc.opening_slot r
  committee := fun s => S.E.committee s
  Certificate := NamedBlock V
  finalizes := fun c T => ∃ h, NamedFinalizedAt S.E S.cfg c T h
  collisionFree := fun c c' => RootInjectiveOnAncestors c.erase c'.erase
  evidence := fun c c' =>
    HasSlashableWeightBetween S.E (chain_attestations c.erase)
      (chain_attestations c'.erase)
  slashable := fun n n' =>
    HasSlashableWeightBetween S.E (store_attestations n.st.core)
      (store_attestations n'.st.core)
  inRun := fun x c => blockInLog S Sched x c
  idealization := fun x => RootCollisionFreeInLog S Sched x
  slashes := fun x v => slashesInLog S x v

end DecoupledConsensusModel.Sts
