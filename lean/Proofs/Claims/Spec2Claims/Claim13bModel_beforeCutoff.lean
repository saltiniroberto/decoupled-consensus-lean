module
public import Model.Vocabulary.Objects.Time
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# Facts about `beforeCutoff`

The members of a set stamped strictly before a cutoff.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.beforeCutoff

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {α : Type} [DecidableEq α]

/-- `x` is in `beforeCutoff ts Γ S` exactly when `x ∈ S` and `x` is stamped before `Γ` under `ts`. -/
theorem mem_beforeCutoff_iff (ts : TimestampMap α) (Γ : Time) (S : Finset α) (x : α) :
    x ∈ beforeCutoff ts Γ S ↔ x ∈ S ∧ stampedBefore ts Γ x = true := by
  unfold beforeCutoff
  exact Finset.mem_filter

end DecoupledConsensusModel.Sts
