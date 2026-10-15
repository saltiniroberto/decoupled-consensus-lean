module
public import Model.Vocabulary.Execution.Setup
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# The setup with its GST replaced

`setupWithGST S g` is `S` with its environment's GST replaced by `g`.
-/

-- The definitions this file unfolds, made locally semireducible.
set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Env.committee

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

noncomputable section

/-- The setup equal to `S` except that its environment's GST is `g`. -/
def setupWithGST (S : Setup V) (g : Int) (hg : 0 ≤ g) : Setup V :=
  { S with E := { S.E with t_GST := g, t_GST_nonneg := hg } }

end

end DecoupledConsensusModel.Sts
