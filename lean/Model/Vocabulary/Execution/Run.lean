module
public import Model.Vocabulary.Execution.Node
public import Model.Vocabulary.Execution.Objects

@[expose] public section

/-!
# Worlds and runs

The world of an execution (a node state per validator), its step on one event, runs and the node
states they reach, the blocks in a run, the reads a confirmation makes, and the environmental
conditions on a run.
-/

section
namespace DecoupledConsensusModel.Execution

abbrev NamedWorld (V : Type) := V → NamedNodeState V

namespace NamedWorld
variable {V : Type} [DecidableEq V]

def init : NamedWorld V := fun _ => NamedNode.initial

def step [Fintype V] (S : Setup V) (w : NamedWorld V) : NamedEvent V → NamedWorld V
  | .tick v t => Function.update w v (NamedNode.tick S v (w v) t).1
  | .deliver v o _ => Function.update w v (NamedNode.process S (w v) o)

end NamedWorld

abbrev NamedRun (V : Type) := Generic.Run V (NamedObject V)

namespace NamedRun
variable {V : Type}

abbrev honest (rho : NamedRun V) : Finset V := Generic.Run.honest rho
abbrev events (rho : NamedRun V) : List (NamedEvent V) := Generic.Run.events rho

end NamedRun

namespace NamedRun
variable {V : Type} [DecidableEq V] [Fintype V]

def stateBefore (S : Setup V) (rho : NamedRun V) (i : Nat) : NamedWorld V :=
  (rho.events.take i).foldl (NamedWorld.step S) NamedWorld.init

def stateBeforeTime (S : Setup V) (rho : NamedRun V) (t : Time) : NamedWorld V :=
  (rho.events.filter (fun e => decide (e.time < t))).foldl (NamedWorld.step S) NamedWorld.init

def readAt (S : Setup V) (rho : NamedRun V) (t : Time) : NamedWorld V :=
  (rho.events.filter (fun e => decide (e.time ≤ t))).foldl (NamedWorld.step S) NamedWorld.init

def objects (rho : NamedRun V) : List (NamedObject V) :=
  rho.events.filterMap NamedEvent.object?

/-- The block `B` is among the objects of the run `rho`, or some honest validator's store holds it
    before some step `i`. -/
def directBlockInRun (S : Setup V) (rho : NamedRun V) (B : NamedBlock V) : Prop :=
  NamedObject.block B ∈ objects rho ∨
    ∃ v ∈ rho.honest, ∃ i : Nat, B ∈ (stateBefore S rho i v).st.bodies

/-- `A` is an ancestor of, or equal to, a block directly in the run `rho`. -/
def blockInRun (S : Setup V) (rho : NamedRun V) (A : NamedBlock V) : Prop :=
  ∃ B : NamedBlock V, directBlockInRun S rho B ∧ NamedBlock.Preceq A B

end NamedRun
end DecoupledConsensusModel.Execution
end

section
namespace DecoupledConsensusModel.Execution

namespace NamedReceiptCalls
variable {V : Type} [DecidableEq V] [Fintype V]

/-- The store after the core block handler processes `B`. -/
def postCore (S : Setup V) (before : Protocol.NamedStore V) (B : NamedBlock V) :
    Protocol.NamedStore V :=
  Protocol.NamedStore.process_block_core S.E S.hc S.cfg before B

end NamedReceiptCalls

namespace NamedRun
variable {V : Type} [DecidableEq V] [Fintype V]

end NamedRun
end DecoupledConsensusModel.Execution
end

section
/-! ## Confirmation reads -/
namespace DecoupledConsensusModel.Execution.NamedActionReads
open DecoupledConsensusModel.Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

/-- The phase cache prepared at the start of the node's tick at time `t`. -/
def preparedCache (S : Setup V) (before : NamedNodeState V) (t : Time) : Cache V :=
  onPhaseTick S.E S.hc before.st.core.toHealing t before.cache

/-- The node state a confirmation uses at time `t`: the incoming store with its clock set to `t`,
    the incoming signing record, and the prepared cache. -/
def confirmationReadFrom (S : Setup V) (before : NamedNodeState V) (t : Time) :
    NamedNodeState V :=
  ⟨Protocol.NamedStore.setClock S.E before.st t, before.record, preparedCache S before t⟩

/-- `confirmationReadFrom` applied to `v`'s node state made of every event of the run strictly
    before time `t`. -/
def confirmationReadAt (S : Setup V) (rho : NamedRun V) (v : V) (t : Time) :
    NamedNodeState V :=
  confirmationReadFrom S (NamedRun.stateBeforeTime S rho t v) t

end DecoupledConsensusModel.Execution.NamedActionReads
end

section
namespace DecoupledConsensusModel.Execution

abbrev Run := NamedRun
namespace Run
variable {V : Type} [DecidableEq V] [Fintype V]

def storeAt (S : Setup V) (rho : Run V) (v : V) (t : Time) : Protocol.NamedStore V :=
  (NamedRun.readAt S rho t v).st

end Run

namespace Run
variable {V : Type} [DecidableEq V] [Fintype V]

end Run

end DecoupledConsensusModel.Execution
end

section
/-! ## Environmental conditions on a run -/
namespace DecoupledConsensusModel.Execution
variable {V : Type} [DecidableEq V] [Fintype V]

structure NamedRootCollisionFree (S : Setup V) (rho : NamedRun V) : Prop where
  root_injective : ∀ B C : NamedBlock V,
    NamedRun.blockInRun S rho B → NamedRun.blockInRun S rho C →
    ∀ A D : NamedBlock V,
      (NamedBlock.Preceq A B ∨ NamedBlock.Preceq A C) →
      (NamedBlock.Preceq D B ∨ NamedBlock.Preceq D C) → A.root = D.root → A = D

end DecoupledConsensusModel.Execution
end

end
