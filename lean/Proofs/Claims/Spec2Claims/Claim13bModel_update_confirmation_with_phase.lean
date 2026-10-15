import Model.Vocabulary.Protocol.Duties.Proposals
import Proofs.Claims.ModelIrreducible
import Proofs.Claims.Spec2Claims.Claim13bModel_update_confirmation_with

/-!
# Facts about `Protocol.update_confirmation_with`: what it leaves unchanged

The confirmation update and its named-store wrapper write only the confirmation fields, so the
finalized block, the filtered tree and the other fork-choice fields are those of the store it was
given.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Block.preceq
  DecoupledConsensusModel.Protocol.NamedDuties.update_confirmation_with
  DecoupledConsensusModel.Protocol.Store.toHealing DecoupledConsensusModel.Protocol.get_fg_root
  DecoupledConsensusModel.Protocol.get_filtered_block_tree
  DecoupledConsensusModel.Protocol.get_filtered_block_tree_from
  DecoupledConsensusModel.Protocol.goldfish_score
  DecoupledConsensusModel.Protocol.raw_goldfish_score
  DecoupledConsensusModel.Protocol.raw_supporters
  DecoupledConsensusModel.Protocol.update_confirmation_with
  DecoupledConsensusModel.Protocol.viable_tree

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The core of the named confirmation update is the confirmation update of the core. -/
theorem namedDuties_update_confirmation_with_core (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.NamedStore V) (s : Slot) :
    (Protocol.NamedDuties.update_confirmation_with contract E hc st s).core
      = Protocol.update_confirmation_with contract E hc st.core s := rfl

/-- The confirmation update leaves the finalized block unchanged. -/
theorem update_confirmation_with_toHealing_F (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.Store V) (s : Slot) :
    (Protocol.update_confirmation_with contract E hc st s).toHealing.F = st.toHealing.F := rfl

/-- The confirmation update leaves the justified block `J` unchanged. -/
theorem update_confirmation_with_toHealing_J (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.Store V) (s : Slot) :
    (Protocol.update_confirmation_with contract E hc st s).toHealing.J = st.toHealing.J := rfl

/-- The confirmation update leaves the slot unchanged. -/
theorem update_confirmation_with_toHealing_s (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.Store V) (s : Slot) :
    (Protocol.update_confirmation_with contract E hc st s).toHealing.s = st.toHealing.s := rfl

/-- The confirmation update leaves the filtered block tree unchanged. -/
theorem update_confirmation_with_filtered (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.Store V) (s : Slot) :
    Protocol.get_filtered_block_tree
        (Protocol.update_confirmation_with contract E hc st s).toHealing.toFG
      = Protocol.get_filtered_block_tree st.toHealing.toFG := rfl

/-- The confirmation update leaves the running height maximum `h_max` unchanged. -/
theorem update_confirmation_with_toHealing_h_max (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.Store V) (s : Slot) :
    (Protocol.update_confirmation_with contract E hc st s).toHealing.h_max
      = st.toHealing.h_max := rfl

/-- The confirmation update leaves the justified height `h_j` unchanged. -/
theorem update_confirmation_with_toHealing_h_j (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.Store V) (s : Slot) :
    (Protocol.update_confirmation_with contract E hc st s).toHealing.h_j
      = st.toHealing.h_j := rfl

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]


end DecoupledConsensusModel.Sts
