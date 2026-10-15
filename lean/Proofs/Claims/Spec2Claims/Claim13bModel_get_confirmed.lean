import Proofs.Claims.Spec2Claims.Claim13bModel_compatible
import Model.Vocabulary.Protocol.Handlers
import Proofs.Vocabulary.Objects.Ancestry

/-!
# Facts about `Protocol.get_confirmed`

The client's confirmed output: the confirmation record floored on the stable output.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Block.Preceq
  DecoupledConsensusModel.Protocol.get_confirmed

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- `get_confirmed st` is `st.latest_confirmed` or `get_stable st`. -/
theorem get_confirmed_eq_or (st : Protocol.Store V) :
    Protocol.get_confirmed st = st.latest_confirmed ∨
      Protocol.get_confirmed st = Protocol.get_stable st := by
  unfold Protocol.get_confirmed
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- If `get_stable st` and `st.latest_confirmed` are compatible, then both are ancestors of
    `get_confirmed st`. -/
theorem get_confirmed_upper (st : Protocol.Store V)
    (h : Block.compatible (Protocol.get_stable st) st.latest_confirmed = true) :
    Block.Preceq (Protocol.get_stable st) (Protocol.get_confirmed st) ∧
      Block.Preceq st.latest_confirmed (Protocol.get_confirmed st) := by
  unfold Protocol.get_confirmed
  split_ifs with hSC
  · exact ⟨hSC, Block.preceq_self _⟩
  · rcases compatible_cases h with h1 | h1
    · exact absurd h1 hSC
    · exact ⟨Block.preceq_self _, h1⟩

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- Either `get_stable st ⪯ st.latest_confirmed` and `get_confirmed st` is `st.latest_confirmed`, or
    `get_confirmed st` is `get_stable st`. -/
theorem get_confirmed_values (st : Protocol.Store V) :
    (Block.Preceq (Protocol.get_stable st) st.latest_confirmed ∧
        Protocol.get_confirmed st = st.latest_confirmed) ∨
      Protocol.get_confirmed st = Protocol.get_stable st := by
  unfold Protocol.get_confirmed
  split_ifs with h
  · exact Or.inl ⟨h, rfl⟩
  · exact Or.inr rfl

end DecoupledConsensusModel.Sts
