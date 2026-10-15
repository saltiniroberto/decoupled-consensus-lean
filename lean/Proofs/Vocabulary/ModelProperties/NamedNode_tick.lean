module
public import Model.Vocabulary.Execution.Node

@[expose] public section

/-!
# Facts about `Execution.NamedNode.tick`

The node state and the emitted objects after a tick.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The store after `v`'s node `n` ticks at `t` is the store the named tick returns on `n`'s store
    and record, under the grade contract of the cache `onPhaseTick` completes. -/
theorem tick_fst_st (S : Setup V) (v : V) (n : NamedNodeState V) (t : Time) :
    (NamedNode.tick S v n t).1.st =
      (Protocol.NamedTick.tick
        (NamedProfile.gradeContract
          (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache))
        S.E S.hc S.cfg (S.node v) n.st n.record t).1 := rfl

/-- The store after `v`'s node `n` ticks at `t` is the store the named tick returns on `n`'s store
    and record, under the frame contract of the cache `onPhaseTick` completes. -/
theorem tick_fst_st_frameContract (S : Setup V) (v : V) (n : NamedNodeState V) (t : Time) :
    (NamedNode.tick S v n t).1.st =
      (Protocol.NamedTick.tick
        (DecoupledConsensusModel.Protocol.frameContract
          (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache))
        S.E S.hc S.cfg (S.node v) n.st n.record t).1 := rfl

/-- The objects emitted when `v`'s node `n` ticks at `t` are those the named tick emits on `n`'s
    store and record, under the frame contract of the cache `onPhaseTick` completes. -/
theorem tick_snd_frameContract (S : Setup V) (v : V) (n : NamedNodeState V) (t : Time) :
    (NamedNode.tick S v n t).2 =
      (Protocol.NamedTick.tick
        (DecoupledConsensusModel.Protocol.frameContract
          (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache))
        S.E S.hc S.cfg (S.node v) n.st n.record t).2.2 := rfl

end DecoupledConsensusModel.Proofs.ModelProperties

end
