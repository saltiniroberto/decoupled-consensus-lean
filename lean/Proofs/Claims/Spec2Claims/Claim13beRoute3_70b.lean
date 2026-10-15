import Proofs.Claims.Spec2Claims.Claim13beRoute3_67b
import Proofs.Claims.Spec2Claims.Claim13bK_ConeAnchor
import Proofs.Vocabulary.ModelProperties.own_lock
import Proofs.Claims.Spec2Claims.Claim13beRoute3_57b
import Proofs.Claims.Spec2Claims.Claim13bModel_opening_slot
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedBlock_parent
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedBlock_erase
import Proofs.Claims.Spec2Claims.Claim13bModel_Preceq
import Proofs.Claims.Spec2Claims.Claim13bModel_actionStoreAt
import Proofs.Claims.Spec2Claims.Claim13bModel_get_filtered_block_tree
import Proofs.Claims.Spec2Claims.Claim13bModel_confirmationReadFrom
import Proofs.Claims.Spec2Claims.Claim13bModel_setClock
import Proofs.Claims.Spec2Claims.Claim13bModel_opening
import Proofs.Claims.Spec2Claims.Claim13bModel_compatible
import Proofs.Claims.Spec2Claims.Claim13bModel_freezeRoot
import Proofs.Claims.Spec2Claims.Claim13bModel_weightOf

/-!
# Two round and weight helpers

A round inequality over `Nat`, and the monotonicity of `BelowOneThird` in its set.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

section SeedSourceCapClosure

open DecoupledConsensusModel.Statements.Instantiation

open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.Optimistic

local macro "ssc% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Execution.SeedSourceCapClosure)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- If `r0 + 2 ≤ q'`, then `r0 + 1 ≤ q' − 1`. -/
theorem seedPromotionBase_nat_l70 (r0 q' : Nat) (h : r0 + 2 ≤ q') : r0 + 1 ≤ q' - 1 := by
  omega

end SeedSourceCapClosure

section HeightRegimeNamedBaseDeadline

open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel.Proofs.Optimistic

local macro "hnd% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ChainState.HeightRegimeNamedBaseDeadline)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- If `BelowOneThird S Y` and `Y ⊆ X`, then `BelowOneThird S X`. -/
theorem belowOneThird_mono_l70 (S : Setup V) {X Y : Finset V} (hYX : Y ⊆ X)
    (h : Execution.BelowOneThird S Y) : Execution.BelowOneThird S X := by
  have hsub : Finset.univ \ X ⊆ Finset.univ \ Y :=
    Finset.sdiff_subset_sdiff (subset_refl _) hYX
  have hle := DecoupledConsensusModel.Electorate.weightOf_mono S.E.electorate hsub
  unfold Execution.BelowOneThird at h ⊢
  omega

end HeightRegimeNamedBaseDeadline

end DecoupledConsensusModel.Sts
