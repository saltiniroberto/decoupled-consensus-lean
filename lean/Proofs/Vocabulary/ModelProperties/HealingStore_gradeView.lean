module
public import Model.Vocabulary.Protocol.Store

@[expose] public section

/-!
# Facts about `Protocol.HealingStore.gradeView`

The store projected to the fields the grade readers use.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

variable {V : Type} [DecidableEq V]

/-- The block tree of the grade view of `st` is the block tree of `st`. -/
theorem gradeView_T (st : Protocol.HealingStore V) : st.gradeView.T = st.T := rfl

/-- The grade view does not read the clock or the slot. -/
theorem gradeView_toHealing_clock (st : Protocol.Store V) (t : Time) (s : Slot) :
    ({ st with t := t, s := s } : Protocol.Store V).toHealing.gradeView =
      st.toHealing.gradeView := rfl

end DecoupledConsensusModel.Proofs.ModelProperties

end
