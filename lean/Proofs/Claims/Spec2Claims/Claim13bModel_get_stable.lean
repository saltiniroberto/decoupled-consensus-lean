import Proofs.Claims.Spec2Claims.Claim13bModel_compatible
import Model.Vocabulary.Protocol.Handlers
import Proofs.Vocabulary.Objects.Ancestry

/-!
# Facts about `Protocol.get_stable`

The client's stable output: the stable record floored on `F`.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Block.Preceq
  DecoupledConsensusModel.Protocol.get_stable

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- `get_stable st` is `st.latest_stable` or `st.F`. -/
theorem get_stable_eq_or (st : Protocol.Store V) :
    Protocol.get_stable st = st.latest_stable ∨ Protocol.get_stable st = st.F := by
  unfold Protocol.get_stable
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- If `st.F` and `st.latest_stable` are compatible, then both are ancestors of `get_stable st`. -/
theorem get_stable_upper (st : Protocol.Store V)
    (h : Block.compatible st.F st.latest_stable = true) :
    Block.Preceq st.F (Protocol.get_stable st) ∧
      Block.Preceq st.latest_stable (Protocol.get_stable st) := by
  unfold Protocol.get_stable
  split_ifs with hFL
  · exact ⟨hFL, Block.preceq_self _⟩
  · rcases compatible_cases h with h1 | h1
    · exact absurd h1 hFL
    · exact ⟨Block.preceq_self _, h1⟩

end DecoupledConsensusModel.Sts
