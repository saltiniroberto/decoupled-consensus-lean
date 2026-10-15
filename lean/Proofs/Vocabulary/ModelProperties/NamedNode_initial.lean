module
public import Model.Vocabulary.Execution.Node

@[expose] public section

/-!
# Facts about `Execution.NamedNode.initial`

The initial node state.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V]

/-- The store of the initial node state is the initial named store. -/
theorem initial_st :
    (NamedNode.initial : NamedNodeState V).st = Protocol.NamedStore.initial := rfl

/-- At every height, the signing record of the initial node state holds no lock. -/
theorem initial_record_legacy_lock (H : Height) :
    (NamedNode.initial : NamedNodeState V).record.legacy.lock H = none := rfl

/-- At every height, the signing record of the initial node state records no target. -/
theorem initial_record_legacy_target (h : Height) :
    (NamedNode.initial : NamedNodeState V).record.legacy.target h = none := rfl

/-- At every height, the signing record of the initial node state records no timeout. -/
theorem initial_record_legacy_timeout (h : Height) :
    (NamedNode.initial : NamedNodeState V).record.legacy.timeout h = false := rfl

/-- The round of the grade cache of the initial node state is `0`. -/
theorem initial_cache_round :
    (NamedNode.initial : NamedNodeState V).cache.round = 0 := rfl

/-- For every phase, the result of the current frame of the initial node state's grade cache is
    present and holds no block. -/
theorem initial_cache_current_phase (p : DecoupledConsensusModel.Protocol.Phase) :
    DecoupledConsensusModel.Protocol.phaseResult
      (NamedNode.initial : NamedNodeState V).cache.current p = some none := by
  cases p <;> rfl

/-- The next-round frame of the initial node state's grade cache is `pendingFrame`. -/
theorem initial_cache_next :
    (NamedNode.initial : NamedNodeState V).cache.next =
      DecoupledConsensusModel.Protocol.pendingFrame := rfl

end DecoupledConsensusModel.Proofs.ModelProperties

end
