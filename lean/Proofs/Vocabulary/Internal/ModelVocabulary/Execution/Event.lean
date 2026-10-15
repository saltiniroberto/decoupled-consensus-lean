module
public import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.NamedEvent
public import Model.Vocabulary.Execution.Run

@[expose] public section

/-!
# Events

The event type of a run and its world transition.
-/
namespace DecoupledConsensusModel.Execution

abbrev Event := NamedEvent
namespace Event
abbrev tick := @NamedEvent.tick
abbrev deliver := @NamedEvent.deliver
abbrev time {V : Type} (e : Event V) : Time := NamedEvent.time e
abbrev node {V : Type} (e : Event V) : V := NamedEvent.node e
abbrev key := @NamedEvent.key
end Event

namespace World
abbrev step := @NamedWorld.step
end World

end DecoupledConsensusModel.Execution

end
