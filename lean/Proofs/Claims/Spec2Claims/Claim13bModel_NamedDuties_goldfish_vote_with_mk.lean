module
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# More facts about `NamedDuties.goldfish_vote_with`

The named Goldfish vote duty, related to the receipt of the vote it emits.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.NamedDuties.goldfish_vote_with DecoupledConsensusModel.Protocol.goldfish_vote_with DecoupledConsensusModel.Execution.NamedReceipt.process

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The named Goldfish vote duty either changes nothing and emits nothing, or runs the vote receipt
    on the vote it emits. -/
theorem named_vote_cases (S : Setup V) (gc : GradeContract V) (nd : Node V)
    (st : NamedStore V) :
    NamedDuties.goldfish_vote_with gc S.E S.hc nd st = (st, none) ∨
      ∃ u : GoldfishVote V, NamedDuties.goldfish_vote_with gc S.E S.hc nd st
        = (NamedReceipt.process S st (.gfVote u), some u) := by
  have hd : NamedDuties.goldfish_vote_with gc S.E S.hc nd st
      = (({ st with core := (Protocol.goldfish_vote_with gc S.E S.hc nd st.core).1 } :
            NamedStore V),
         (Protocol.goldfish_vote_with gc S.E S.hc nd st.core).2) := rfl
  rw [hd]
  simp only [Protocol.goldfish_vote_with]
  split
  · exact Or.inr ⟨_, rfl⟩
  · exact Or.inl rfl

end DecoupledConsensusModel.Sts
