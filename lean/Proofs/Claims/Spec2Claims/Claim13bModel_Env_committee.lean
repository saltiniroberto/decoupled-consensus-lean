module
public import Model.Vocabulary.Objects.Parameters
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# A slot's committee

A slot's committee depends on the environment only through its fixed committees `Env.committees`.
-/

-- The definitions this file unfolds, made locally semireducible.
set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Env.committee

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- If the environments `E` and `E'` have the same fixed committees, then slot `s`'s committee is
    the same in both. -/
theorem committee_eq_of_committees_eq {E E' : Env V} (h : E.committees = E'.committees)
    (s : Slot) : E.committee s = E'.committee s := by
  unfold Env.committee
  rw [h]

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

end DecoupledConsensusModel.Sts
