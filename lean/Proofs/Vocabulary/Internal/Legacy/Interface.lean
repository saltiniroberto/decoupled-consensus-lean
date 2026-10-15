module
public import Model.Vocabulary.Execution.Run

@[expose] public section

/-!
# The public interface

The protocol reads the public statements use.
-/

namespace DecoupledConsensusModel
namespace Statements

open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The protocol reads used by the public statements. -/
structure Interface (V : Type) [DecidableEq V] where
  /-- The three user-facing outputs, as getters on the node store. -/
  confirmed : Protocol.Store V → Block V
  stable : Protocol.Store V → Block V
  finalized : Protocol.Store V → Block V
  /-- The proposal schedule and the block emitted by a slot. -/
  proposer : Slot → V
  proposalTime : Slot → Time
  proposedBlock : Run V → Slot → Option (NamedBlock V)
  /-- The committee of a slot. -/
  committee : Slot → Finset V
  /-- A finality certificate. -/
  Certificate : Type
  /-- Certificate `c` finalizes target `T`. -/
  finalizes : Certificate → Block V → Prop
  /-- The model's collision-free condition on the roots of two certificates. -/
  collisionFree : Certificate → Certificate → Prop
  /-- Two certificates contain slashable evidence. -/
  evidence : Certificate → Certificate → Prop
  /-- Two stores hold slashable evidence against each other. -/
  slashable : Protocol.Store V → Protocol.Store V → Prop
  /-- Certificate `c` is assembled from blocks of the run. -/
  inRun : Run V → Certificate → Prop

end Statements
end DecoupledConsensusModel

end
