module
public import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.Objects
public import Model.Vocabulary.Execution.Run

@[expose] public section

/-!
# Node states and the tick

Abbreviations for node states, worlds and the tick, over the named node state with its record and
cache.
-/
namespace DecoupledConsensusModel.Execution

abbrev NodeState := NamedNodeState
abbrev World := NamedWorld

namespace NodeState
abbrev st {V : Type} (n : NodeState V) : Protocol.NamedStore V := NamedNodeState.st n
abbrev record {V : Type} (n : NodeState V) : Protocol.NamedRecord := NamedNodeState.record n
abbrev cache {V : Type} (n : NodeState V) : DecoupledConsensusModel.Protocol.Cache V := NamedNodeState.cache n
/-- The record of a node state. -/
abbrev Λ {V : Type} (n : NodeState V) : Protocol.NamedRecord := NamedNodeState.record n
abbrev process {V : Type} [DecidableEq V] [Fintype V]
    (S : Setup V) (n : NodeState V) (o : Object V) : NodeState V :=
  NamedNode.process S n o
end NodeState

namespace NamedNodeState
/-- The record of a named node state. -/
abbrev Λ {V : Type} (n : NamedNodeState V) : Protocol.NamedRecord := n.record
end NamedNodeState

namespace World
abbrev init := @NamedWorld.init
end World

/-- The emitting tick, `NamedNode.tick`. -/
abbrev on_tick_emit := @NamedNode.tick

end DecoupledConsensusModel.Execution

end
