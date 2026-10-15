module
public import Model.Vocabulary.Execution.Run
public import Proofs.Vocabulary.Internal.Definitions.TickReads

@[expose] public section

/-!
# Facts about `Execution.NamedActionReads.confirmationReadFrom`

The confirmation read staged from a node state at a time, read field by field.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The slot of the confirmation read staged from `before` at `t` is the slot of `t`. -/
theorem confirmationReadFrom_st_core_s (S : Setup V) (before : NamedNodeState V) (t : Time) :
    (NamedActionReads.confirmationReadFrom S before t).st.core.s = S.E.slotOf t := rfl

/-- The store of the confirmation read staged from `before` at `t` is `before`'s store with its
    clock staged to `t`. -/
theorem confirmationReadFrom_st (S : Setup V) (before : NamedNodeState V) (t : Time) :
    (NamedActionReads.confirmationReadFrom S before t).st =
      Protocol.NamedStore.setClock S.E before.st t := rfl

/-- The core store of the confirmation read staged from `before` at `t` is
    `Proofs.Optimistic.tickStore` of `before`'s core store at `t`. -/
theorem confirmationReadFrom_st_core (S : Setup V) (before : NamedNodeState V) (t : Time) :
    (NamedActionReads.confirmationReadFrom S before t).st.core =
      Proofs.Optimistic.tickStore S before.st.core t := rfl

/-- The grade cache of the confirmation read staged from `before` at `t` is the cache prepared from
    `before` at `t`. -/
theorem confirmationReadFrom_cache (S : Setup V) (before : NamedNodeState V) (t : Time) :
    (NamedActionReads.confirmationReadFrom S before t).cache =
      NamedActionReads.preparedCache S before t := rfl

end DecoupledConsensusModel.Proofs.ModelProperties

end
