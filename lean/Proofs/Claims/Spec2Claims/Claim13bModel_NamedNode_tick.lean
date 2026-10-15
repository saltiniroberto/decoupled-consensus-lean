module

public import Model.Vocabulary.Execution.Node
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# Facts about `NamedNode.tick`

The store and the emitted objects of the node tick, which runs the phase tick of the grade cache and
then the profile tick `NamedProfile.tick`.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Execution.NamedNode.tick
  DecoupledConsensusModel.Execution.NamedProfile.tick
  DecoupledConsensusModel.Protocol.NamedTick.tick

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The store validator `v`'s node tick at `t` leaves is the store `Protocol.NamedTick.tick` returns
    at `t`, given `v`'s store and signing record before the tick and the grade contract of the
    phase-ticked cache. -/
theorem namedNode_tick_st (S : Setup V) (v : V) (n : NamedNodeState V) (t : Int) :
    (NamedNode.tick S v n t).1.st
      = (Protocol.NamedTick.tick
          (NamedProfile.gradeContract (Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache))
          S.E S.hc S.cfg (S.node v) n.st n.record t).1 := rfl

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The objects validator `v`'s node tick at `t` emits are the objects `Protocol.NamedTick.tick`
    emits at `t`, given `v`'s store and signing record before the tick and the grade contract of the
    phase-ticked cache. -/
theorem namedNode_tick_snd (S : Setup V) (v : V) (n : NamedNodeState V) (t : Int) :
    (NamedNode.tick S v n t).2
      = (Protocol.NamedTick.tick
          (NamedProfile.gradeContract (Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache))
          S.E S.hc S.cfg (S.node v) n.st n.record t).2.2 := rfl

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]


end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]


end DecoupledConsensusModel.Sts
