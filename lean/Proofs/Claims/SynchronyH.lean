module
public import Proofs.Claims.ProcessedFlip
public import Proofs.Claims.VocabularyAssumptionsLemmas
public import Proofs.Claims.Spec2Claims.Claim13bModel_Env_committee
public import Proofs.Claims.Spec2Claims.Claim13bModel_NamedBlock_slot
public import Proofs.Vocabulary.ModelProperties.NamedReceipt_excludes
public import Proofs.Vocabulary.ModelProperties.NamedNode_initial
public import Proofs.Claims.Spec2Claims.Claim13bModel_compatible

@[expose] public section

/-!
# Compatibility under ancestry

An ancestor of a block compatible with `B` is compatible with `B`.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- If `A` is an ancestor of `C` and `C` is compatible with `B`, then `A` is compatible with `B`. -/
theorem compatible_of_preceq_left {A C B : Block V} (hAC : Block.Preceq A C)
    (hCB : Block.compatible C B = true) : Block.compatible A B = true := by
  rcases compatible_cases hCB with hCB | hBC
  · exact compatible_of_cases (Or.inl (preceq_trans_Preceq hAC hCB))
  · exact compatible_of_preceq_common_Preceq hAC hBC

end DecoupledConsensusModel.Sts
