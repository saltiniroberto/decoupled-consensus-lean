module

public import Model.Vocabulary.Execution.Run
public import Proofs.Claims.ModelIrreducible
public import Proofs.Vocabulary.Internal.Definitions.TickReads
public import Proofs.Vocabulary.Internal.Legacy.Definitions.NamedDutyReads

@[expose] public section

/-!
# Facts about `NamedActionReads.confirmationReadFrom`

The confirmation read of a node state at a time: the clock-stamped store with the phase-prepared
cache.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible]
  DecoupledConsensusModel.Execution.NamedActionReads.confirmationReadFrom
  DecoupledConsensusModel.Execution.NamedActionReads.preparedCache
  DecoupledConsensusModel.Execution.NamedProfile.gradeContract
  DecoupledConsensusModel.Protocol.NamedStore.setClock
  DecoupledConsensusModel.Protocol.Store.toHealing DecoupledConsensusModel.Protocol.frameContract
  DecoupledConsensusModel.Protocol.get_fg_root
  DecoupledConsensusModel.Protocol.get_filtered_block_tree
  DecoupledConsensusModel.Protocol.get_filtered_block_tree_from
  DecoupledConsensusModel.Protocol.onPhaseTick

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The store of the confirmation read of `before` at `t` is `before`'s store with its clock set to
    `t`. -/
theorem confirmationReadFrom_st (S : Setup V) (before : NamedNodeState V) (t : Int) :
    (NamedActionReads.confirmationReadFrom S before t).st
      = Protocol.NamedStore.setClock S.E before.st t := rfl

/-- The cache of the confirmation read of `before` at `t` is the phase tick `Protocol.onPhaseTick`
    at `t` over `before`'s store and cache. -/
theorem confirmationReadFrom_cache (S : Setup V) (before : NamedNodeState V) (t : Int) :
    (NamedActionReads.confirmationReadFrom S before t).cache
      = Protocol.onPhaseTick S.E S.hc before.st.core.toHealing t before.cache := rfl

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]


/-- The grade contract of the cache of the confirmation read of `before` at `t` is
    `Protocol.frameContract` of the cache the phase tick at `t` prepares from `before`'s store and
    cache. -/
theorem confirmationReadFrom_gradeContract (S : Setup V) (before : NamedNodeState V) (t : Int) :
    NamedProfile.gradeContract (NamedActionReads.confirmationReadFrom S before t).cache
      = Protocol.frameContract
          (Protocol.onPhaseTick S.E S.hc before.st.core.toHealing t before.cache) := rfl

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

end DecoupledConsensusModel.Sts
