module
public import Model.Vocabulary.Protocol.Store

@[expose] public section

/-!
# Facts about `Protocol.get_fg_root`

The FG root, which reads only the finalized block, the justified block, the justified height and
`h_max`.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

variable {V : Type} [DecidableEq V]

/-- Two stores with the same finalized block, justified block, justified height and `h_max` have the
    same FG root. -/
theorem get_fg_root_toHealing_eq_of_fields {st st' : Protocol.Store V}
    (hF : st.F = st'.F) (hJ : st.J = st'.J) (hhj : st.h_j = st'.h_j)
    (hmax : st.h_max = st'.h_max) :
    Protocol.get_fg_root st.toHealing.toFG = Protocol.get_fg_root st'.toHealing.toFG := by
  unfold Protocol.get_fg_root Protocol.Store.toHealing
  simp only [hF, hJ, hhj, hmax]

/-- When `h_max = h_j + 1`, the FG root is the justified block. -/
theorem get_fg_root_toHealing_of_eq (st : Protocol.Store V) (h : st.h_max = st.h_j + 1) :
    Protocol.get_fg_root st.toHealing.toFG = st.J := by
  unfold Protocol.get_fg_root Protocol.Store.toHealing
  exact if_pos h

/-- When `h_max ≠ h_j + 1`, the FG root is the finalized block. -/
theorem get_fg_root_toHealing_of_ne (st : Protocol.Store V) (h : ¬ st.h_max = st.h_j + 1) :
    Protocol.get_fg_root st.toHealing.toFG = st.F := by
  unfold Protocol.get_fg_root Protocol.Store.toHealing
  exact if_neg h

/-- The FG root does not read the clock or the slot. -/
theorem get_fg_root_toHealing_clock (st : Protocol.Store V) (t : Time) (s : Slot) :
    Protocol.get_fg_root ({ st with t := t, s := s } : Protocol.Store V).toHealing.toFG =
      Protocol.get_fg_root st.toHealing.toFG :=
  get_fg_root_toHealing_eq_of_fields rfl rfl rfl rfl

end DecoupledConsensusModel.Proofs.ModelProperties

end
