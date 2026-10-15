module
public import Model.Vocabulary.Protocol.Handlers

@[expose] public section

/-!
# Facts about the confirmation update

Facts about `Protocol.update_confirmation_with`, which writes only the fields `live_confirmed`,
`latest_stable` and `latest_confirmed`: one fact for each other field it keeps.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The confirmation update keeps the Goldfish pool. -/
theorem update_confirmation_with_pool (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (st : Protocol.Store V) (s : Slot) :
    (Protocol.update_confirmation_with contract E hc st s).pool = st.pool := rfl

/-- The confirmation update keeps the block tree. -/
theorem update_confirmation_with_T (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (st : Protocol.Store V) (s : Slot) :
    (Protocol.update_confirmation_with contract E hc st s).T = st.T := rfl

/-- The confirmation update keeps the slot. -/
theorem update_confirmation_with_s (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (st : Protocol.Store V) (s : Slot) :
    (Protocol.update_confirmation_with contract E hc st s).s = st.s := rfl

/-- The confirmation update keeps the chain-state map. -/
theorem update_confirmation_with_σ (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (st : Protocol.Store V) (s : Slot) :
    (Protocol.update_confirmation_with contract E hc st s).σ = st.σ := rfl

/-- The confirmation update keeps the grade view of the healing view. -/
theorem update_confirmation_with_toHealing_gradeView (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.Store V) (s : Slot) :
    (Protocol.update_confirmation_with contract E hc st s).toHealing.gradeView =
      st.toHealing.gradeView := rfl

/-- The confirmation update keeps the filtered tree of the healing view. -/
theorem update_confirmation_with_toHealing_filtered (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.Store V) (s : Slot) :
    Protocol.get_filtered_block_tree
        (Protocol.update_confirmation_with contract E hc st s).toHealing.toFG =
      Protocol.get_filtered_block_tree st.toHealing.toFG := rfl

/-- The confirmation update keeps the finalized block. -/
theorem update_confirmation_with_F (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (st : Protocol.Store V) (s : Slot) :
    (Protocol.update_confirmation_with contract E hc st s).F = st.F := rfl

/-- The confirmation update keeps the FG root of the healing view. -/
theorem update_confirmation_with_toHealing_fg_root (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.Store V) (s : Slot) :
    Protocol.get_fg_root (Protocol.update_confirmation_with contract E hc st s).toHealing.toFG =
      Protocol.get_fg_root st.toHealing.toFG := rfl

end DecoupledConsensusModel.Proofs.ModelProperties

end
