module
public import Model.Vocabulary.Execution.Setup
public import Model.Vocabulary.Protocol.Grades
public import Model.Vocabulary.Protocol.Tick
public import Model.Vocabulary.Execution.Objects
public import Model.Vocabulary.Protocol.Handlers

@[expose] public section

/-!
# Node state and transitions

The node state of an execution, how a node processes a received object, and the node's clock tick.
-/

section
/-! ## The protocol tick -/
namespace DecoupledConsensusModel.Execution.NamedProfile
variable {V : Type} [DecidableEq V] [Fintype V]

/-- The grade behavior a node uses: the frame contract over the prepared cache. -/
def gradeContract (cache : DecoupledConsensusModel.Protocol.Cache V) : Protocol.GradeContract V :=
  DecoupledConsensusModel.Protocol.frameContract cache

/-- One call of the protocol's named tick with the setup's environment, healing configuration,
    height configuration and node identity, returning the new store, the new signing record and the
    emitted objects. -/
def tick (S : Setup V) (cache : DecoupledConsensusModel.Protocol.Cache V) (v : V)
    (st : Protocol.NamedStore V) (record : Protocol.NamedRecord) (t : Time) :
    Protocol.NamedStore V × Protocol.NamedRecord × List (NamedObject V) :=
  Protocol.NamedTick.tick (gradeContract cache) S.E S.hc S.cfg (S.node v) st record t

end DecoupledConsensusModel.Execution.NamedProfile
end

section
/-! ## Receiving an object -/
namespace DecoupledConsensusModel.Execution.NamedReceipt
variable {V : Type} [DecidableEq V]

/-- Whether a named object passes the wire-shape checks. -/
def wellFormed [Fintype V] (S : Setup V) : NamedObject V → Bool
  | .block B => Protocol.carried_votes_well_formed B.erase &&
      Protocol.carried_support_well_formed B.erase &&
      B.erase.gf_votes.all (fun u => decide (u.val_index ∈ S.E.committee u.slot))
  | .gfVote u => Protocol.vote_well_formed S.E u
  | .attest _ => true

/-- Whether the store holds what the object depends on: a block needs its parent; votes and
    attestations need nothing. -/
def depsPresent (st : Protocol.NamedStore V) : NamedObject V → Bool
  | .block B => decide (B.parent ∈ st.bodies)
  | .gfVote _ => true
  | .attest _ => true

/-- Whether the store already holds the object. -/
def processed (st : Protocol.NamedStore V) : NamedObject V → Bool
  | .block B => decide (B ∈ st.bodies)
  | .gfVote u => decide (u ∈ st.core.pool u.slot)
  | .attest a => decide (a ∈ st.sg_rows a.round)

/-- A block that conflicts with the node's finalized block (neither is an
ancestor of the other) is excluded for good, since finality only extends;
votes and attestations are never excluded. -/
def excludes (st : Protocol.NamedStore V) : NamedObject V → Bool
  | .block B => !Block.compatible st.core.F B.erase
  | .gfVote _ => false
  | .attest _ => false

/-- The store after processing a received object; a block is admitted together with the objects it
    carries. -/
def process [Fintype V] (S : Setup V) (st : Protocol.NamedStore V) :
    NamedObject V → Protocol.NamedStore V
  | .block B => Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg st B
  | .gfVote u => { st with core := Protocol.on_goldfish_vote_checked S.E st.core u }
  | .attest a => Protocol.NamedAdmission.admit_row S.hc st a

end DecoupledConsensusModel.Execution.NamedReceipt
end

section
/-! ## The node state -/
namespace DecoupledConsensusModel.Execution

structure NamedNodeState (V : Type) where
  st : Protocol.NamedStore V
  record : Protocol.NamedRecord
  cache : DecoupledConsensusModel.Protocol.Cache V

namespace NamedNode
variable {V : Type} [DecidableEq V]

def initial : NamedNodeState V :=
  ⟨Protocol.NamedStore.initial, Protocol.NamedRecord.initial, DecoupledConsensusModel.Protocol.initialCache⟩

/-- The node's tick at time `t`: prepare the phase cache from the incoming store, run the protocol
    tick once, and clip the cache to the new finalized block; returns the new node state and the
    emitted objects. -/
def tick [Fintype V] (S : Setup V) (v : V) (n : NamedNodeState V) (t : Time) :
    NamedNodeState V × List (NamedObject V) :=
  let c := DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache
  let out := NamedProfile.tick S c v n.st n.record t
  (⟨out.1, out.2.1, DecoupledConsensusModel.Protocol.clipCache out.1.core.F c⟩, out.2.2)

/-- The node state after processing a received object: the store is updated, the signing record
    kept, and the cache clipped to the finalized block. -/
def process [Fintype V] (S : Setup V) (n : NamedNodeState V) (o : NamedObject V) :
    NamedNodeState V :=
  let st := NamedReceipt.process S n.st o
  ⟨st, n.record, DecoupledConsensusModel.Protocol.clipCache st.core.F n.cache⟩

end NamedNode
end DecoupledConsensusModel.Execution
end

end
