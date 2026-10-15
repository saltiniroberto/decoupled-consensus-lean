module

public import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.NamedActionReads
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# Facts about `NamedActionReads.actionReadFrom`

The round action read: the node state with its clock stamped at the action time `S.a r`, its phase
cache prepared, and the confirmation duty applied to its store.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Block.deepest?
  DecoupledConsensusModel.Block.preceq DecoupledConsensusModel.Env.slotOf
  DecoupledConsensusModel.Execution.NamedActionReads.confirmationReadFrom
  DecoupledConsensusModel.Protocol.HealConfig.a
  DecoupledConsensusModel.Protocol.NamedDuties.update_confirmation_with
  DecoupledConsensusModel.Protocol.NamedStore.setClock
  DecoupledConsensusModel.Protocol.Store.toHealing DecoupledConsensusModel.Protocol.activePrefix
  DecoupledConsensusModel.Protocol.allClosed DecoupledConsensusModel.Protocol.anchor
  DecoupledConsensusModel.Protocol.get_fg_root
  DecoupledConsensusModel.Protocol.get_filtered_block_tree
  DecoupledConsensusModel.Protocol.get_filtered_block_tree_from
  DecoupledConsensusModel.Protocol.goldfish_score DecoupledConsensusModel.Protocol.grade2Block
  DecoupledConsensusModel.Protocol.update_confirmation_with
  DecoupledConsensusModel.Protocol.viable_tree DecoupledConsensusModel.slotOfTime

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The store the round-`r` action reads from the node state `before` has the bodies of `before`'s
    store. -/
theorem actionReadFrom_st_bodies (S : Setup V) (before : NamedNodeState V) (r : Round) :
    (NamedActionReads.actionReadFrom S before r).st.bodies = before.st.bodies := rfl

end DecoupledConsensusModel.Sts
