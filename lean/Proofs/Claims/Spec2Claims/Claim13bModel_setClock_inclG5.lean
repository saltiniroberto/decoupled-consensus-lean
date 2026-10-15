import Model.Vocabulary.Protocol.Handlers
import Proofs.Claims.ModelIrreducible

/-!
# Facts about `Protocol.NamedStore.setClock`: the healing view

The clock stamp keeps the chain-state map, the tree and the grade view read through the healing
store.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Block.preceq
  DecoupledConsensusModel.Protocol.HealingStore.gradeView
  DecoupledConsensusModel.Protocol.NamedStore.setClock
  DecoupledConsensusModel.Protocol.Store.sg_pool DecoupledConsensusModel.Protocol.Store.toHealing
  DecoupledConsensusModel.Protocol.get_fg_root
  DecoupledConsensusModel.Protocol.get_filtered_block_tree
  DecoupledConsensusModel.Protocol.get_filtered_block_tree_from
  DecoupledConsensusModel.Protocol.viable_tree

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Stamping a named store with the time `t` leaves the chain state its healing store records for
    every block unchanged. -/
theorem setClock_toHealing_σ (E : Env V) (st : Protocol.NamedStore V) (t : Int) :
    (Protocol.NamedStore.setClock E st t).core.toHealing.σ = st.core.σ := rfl

/-- Stamping a named store with the time `t` leaves the tree its healing store holds unchanged. -/
theorem setClock_toHealing_T (E : Env V) (st : Protocol.NamedStore V) (t : Int) :
    (Protocol.NamedStore.setClock E st t).core.toHealing.T = st.core.T := rfl

/-- The grade view read from the healing view of the named store `st` with its clock set to `t` is
    the grade view read from the healing view of `st`. -/
theorem setClock_gradeView (E : Env V) (st : Protocol.NamedStore V) (t : Int) :
    (Protocol.NamedStore.setClock E st t).core.toHealing.gradeView
      = st.core.toHealing.gradeView := rfl

end DecoupledConsensusModel.Sts
