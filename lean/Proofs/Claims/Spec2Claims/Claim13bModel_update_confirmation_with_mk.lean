module
public import Model.Vocabulary.Protocol.Handlers
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# Facts about `Protocol.update_confirmation_with`, as a module file

The Goldfish vote fields and the clock the confirmation update leaves unchanged.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.update_confirmation_with

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The store the confirmation update returns has the Goldfish votes, the Goldfish vote stamps and
    the clock of `st`. -/
theorem update_confirmation_with_vote_fields (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (st : Protocol.Store V) (s : Slot) :
    (Protocol.update_confirmation_with contract E hc st s).gf_votes = st.gf_votes ∧
      (Protocol.update_confirmation_with contract E hc st s).timestamp_vote = st.timestamp_vote ∧
      (Protocol.update_confirmation_with contract E hc st s).t = st.t :=
  ⟨rfl, rfl, rfl⟩

end DecoupledConsensusModel.Sts
