module
public import Model.Vocabulary.Protocol.Handlers
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# Facts about `Protocol.update_finality`: the slot

The finality update keeps the store's slot.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.update_finality

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V]

/-- The finality update keeps the store's slot. -/
theorem update_finality_s' (c : Store V) (σ : ChainState V) : (update_finality c σ).s = c.s := by
  simp only [update_finality]
  split <;> split <;> rfl

end DecoupledConsensusModel.Sts
