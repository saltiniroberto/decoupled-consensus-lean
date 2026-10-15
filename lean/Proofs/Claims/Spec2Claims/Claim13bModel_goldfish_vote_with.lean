module
public import Model.Vocabulary.Protocol.Handlers
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# Facts about `Protocol.goldfish_vote_with`

Lemmas that unfold the Goldfish vote duty on a core store.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.goldfish_vote_with

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The store the Goldfish vote duty returns is either the store it was given or the store the
    checked Goldfish receipt of some vote returns from it. -/
theorem goldfish_vote_with_fst_cases' (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.Store V) :
    (Protocol.goldfish_vote_with contract E hc nd st).1 = st ∨
      ∃ u : GoldfishVote V,
        (Protocol.goldfish_vote_with contract E hc nd st).1
          = Protocol.on_goldfish_vote_checked E st u := by
  simp only [Protocol.goldfish_vote_with]
  split_ifs
  · exact Or.inr ⟨_, rfl⟩
  · exact Or.inl rfl

end DecoupledConsensusModel.Sts
