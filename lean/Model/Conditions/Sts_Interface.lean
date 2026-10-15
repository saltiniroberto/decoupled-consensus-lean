import Model.Sts.Interface
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Record.Wiring
import Proofs.Vocabulary.ModelVocabularyFacts

/-!
# The interface over a model

The readers of a node state, honesty through a step, the blocks an execution puts in play, and the
interface record with its binding, stated over a model `M : Record.Model V`. The last section
equates each with the definition of the same name in `DecoupledConsensusModel.Sts` at
`Record.Model.vocabulary`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Sts.Read
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol (get_confirmed get_stable proposal_time derive_named
  HeightConfig)

/-- The finalized block of the node state `n`: the block its store records as finalized. -/
def Read.finalized (M : Record.Model V) (n : M.N) : Block V := n.st.core.F

end

section
open DecoupledConsensusModel.Sts.Read
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol (get_confirmed get_stable proposal_time derive_named
  HeightConfig)

/-- The confirmed block of the node state `n`, `M.get_confirmed` of its store. -/
def Read.confirmed (M : Record.Model V) (n : M.N) : Block V := M.get_confirmed n.st.core

end

section
open DecoupledConsensusModel.Sts.Read
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol (get_confirmed get_stable proposal_time derive_named
  HeightConfig)

/-- The stable block of the node state `n`, `M.get_stable` of its store. -/
def Read.stable (M : Record.Model V) (n : M.N) : Block V := M.get_stable n.st.core

end

section
open DecoupledConsensusModel.Sts.Read
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol (get_confirmed get_stable proposal_time derive_named
  HeightConfig)

/-- The named blocks whose bodies the store of the node state `n` keeps. -/
def Read.blocks (M : Record.Model V) (n : M.N) : Finset (NamedBlock V) := n.st.bodies

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol (get_confirmed get_stable proposal_time derive_named
  HeightConfig)

/-- `v` is honest through step `i`: no instant at or before `x[i].time` has `v` in the adversary
    set. -/
def HonestThrough (M : Record.Model V) {S : Setup V} (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (i : Nat) (v : V) : Prop :=
  ∀ t' ≤ (x[i].time : Int), v ∉ Sched.adv t'

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol (get_confirmed get_stable proposal_time derive_named
  HeightConfig)

/-- After `i` steps the sent log `x[i].sent` holds a message signed by `S.E.proposer s` whose
    payload is a named block of slot `s`, authored by that proposer, whose erasure is `B`. -/
def proposedBlockAtStep (M : Record.Model V) (S : Setup V) {Sched : Schedule V}
    (x : AtomicExec (Record.protocolOf M S) Sched) (i : Nat) (s : Slot) (B : Block V) : Prop :=
  ∃ B' : NamedBlock V,
    (⟨S.E.proposer s, .block B'⟩ : SignedMsg V (NamedObject V)) ∈ x[i].sent ∧
      B'.erase = B ∧ B'.slot = s ∧ B'.proposer? = some (S.E.proposer s)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol (get_confirmed get_stable proposal_time derive_named
  HeightConfig)

/-- The named block `B` is on the wire, or held: some configuration's sent log holds a message whose
    payload is `B`, or some validator honest through some configuration's instant holds `B` among
    the bodies of its store there. -/
def directBlockInLog (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (B : NamedBlock V) : Prop :=
  (∃ (i : Nat) (sm : SignedMsg V (NamedObject V)), sm ∈ x[i].sent ∧ sm.msg = .block B) ∨
    (∃ (i : Nat) (v : V), Restated.HonestThrough M Sched x i v ∧ B ∈ Restated.Read.blocks M x[i][v].st)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol (get_confirmed get_stable proposal_time derive_named
  HeightConfig)

/-- The named block `A` is an ancestor of a block that is on the wire or held by an honest validator
    (`directBlockInLog`). -/
def blockInLog (M : Record.Model V) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (A : NamedBlock V) : Prop :=
  ∃ B : NamedBlock V, Restated.directBlockInLog M S Sched x B ∧ NamedBlock.Preceq A B

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol (get_confirmed get_stable proposal_time derive_named
  HeightConfig)

/-- Roots identify blocks among the ancestors of the blocks of `x` in play: equal roots force equal
    blocks. -/
structure RootCollisionFreeInLog (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) : Prop where
  /-- Equal roots among the ancestors of two blocks in play force equality. -/
  root_injective : ∀ B C : NamedBlock V,
    Restated.blockInLog M S Sched x B → Restated.blockInLog M S Sched x C →
    ∀ A D : NamedBlock V,
      (NamedBlock.Preceq A B ∨ NamedBlock.Preceq A C) →
      (NamedBlock.Preceq D B ∨ NamedBlock.Preceq D C) → A.root = D.root → A = D

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol (get_confirmed get_stable proposal_time derive_named
  HeightConfig)

/-- There are two validators and two steps such that the attestations their stores carry hold,
    between them, an occurrence pair that slashes `v`. -/
def slashesInLog (M : Record.Model V) (S : Setup V) {Sched : Schedule V} (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V) : Prop :=
  ∃ (u u' : V) (i j : Nat),
    M.SlashableBetween (M.store_attestations (x[i][u].st).st.core)
      (M.store_attestations (x[j][u'].st).st.core) v

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol (get_confirmed get_stable proposal_time derive_named
  HeightConfig)

/-- Replaying the chain of the named block `C` leaves the finalized block `T` at height `h`. -/
def NamedFinalizedAt (M : Record.Model V) (E : Env V) (cfg : HeightConfig) (C : NamedBlock V) (T : Block V)
    (h : Height) : Prop :=
  (M.derive_named E cfg C).F = T ∧ (M.derive_named E cfg C).h_F = h

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol (get_confirmed get_stable proposal_time derive_named
  HeightConfig)

/-- The interface of the protocol over the model `M`: the readers of a node state, the proposal
    schedule, the committees, the certificates and the conditions on an execution's blocks. -/
structure Interface (M : Record.Model V) (S : Setup V) (Sched : Schedule V) where
  /-- The confirmed block of a node state. -/
  confirmed : M.N → Block V
  /-- The stable block of a node state. -/
  stable : M.N → Block V
  /-- The finalized block of a node state. -/
  finalized : M.N → Block V
  /-- The proposer of slot `s`. -/
  proposer : Slot → V
  /-- The proposal instant of slot `s`. -/
  proposalTime : Slot → Int
  /-- `proposedBlock x i s B`: the sent log after `i` steps holds slot `s`'s proposer's own signed
      block for slot `s`, erasing to `B`. -/
  proposedBlock : AtomicExec (Record.protocolOf M S) Sched → Nat → Slot → Block V → Prop
  /-- The slots at which a period opens. -/
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
  slashable : M.N → M.N → Prop
  /-- Certificate `c` is attributable to blocks the execution put in play. -/
  inRun : AtomicExec (Record.protocolOf M S) Sched → Certificate → Prop
  /-- The hash idealization assumed of the blocks of an execution. -/
  idealization : AtomicExec (Record.protocolOf M S) Sched → Prop
  /-- Two states of the execution, at any validators and any steps, hold evidence
      attributable to `v`. -/
  slashes : AtomicExec (Record.protocolOf M S) Sched → V → Prop

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol (get_confirmed get_stable proposal_time derive_named
  HeightConfig)

/-- The interface bound to the readers and the conditions of this file. -/
def interface (M : Record.Model V) (S : Setup V) (Sched : Schedule V) : Restated.Interface M S Sched where
  confirmed := fun n => Restated.Read.confirmed M n
  stable := fun n => Restated.Read.stable M n
  finalized := fun n => Restated.Read.finalized M n
  proposer := S.E.proposer
  proposalTime := M.proposal_time S.E
  proposedBlock := fun x i s B => Restated.proposedBlockAtStep M S x i s B
  opening := fun s => ∃ r : Round, s = (M.opening_slot S.hc r)
  committee := fun s => S.E.committee s
  Certificate := NamedBlock V
  finalizes := fun c T => ∃ h, Restated.NamedFinalizedAt M S.E S.cfg c T h
  collisionFree := fun c c' => RootInjectiveOnAncestors c.erase c'.erase
  evidence := fun c c' =>
    M.HasSlashableWeightBetween S.E (M.chain_attestations c.erase)
      (M.chain_attestations c'.erase)
  slashable := fun n n' =>
    M.HasSlashableWeightBetween S.E (M.store_attestations n.st.core)
      (M.store_attestations n'.st.core)
  inRun := fun x c => Restated.blockInLog M S Sched x c
  idealization := fun x => Restated.RootCollisionFreeInLog M S Sched x
  slashes := fun x v => Restated.slashesInLog M S x v

end

/-! ## Agreement at `Record.Model.vocabulary` -/

section
open DecoupledConsensusModel.Sts.Read
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol (get_confirmed get_stable proposal_time derive_named
  HeightConfig)

end

end DecoupledConsensusModel.Sts.Restated
