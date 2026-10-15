module
public import Proofs.Vocabulary.Protocol.Handlers.NumericStore
public import Proofs.Claims.Projection
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Data.Rat.Floor
public import Proofs.Claims.Spec2Claims.Claim13bModel_latest_window_mk
public import Proofs.Claims.Spec2Claims.Claim13bModel_rawInputs
public import Proofs.Claims.Spec2Claims.Claim13bModel_rawView_mk
public import Proofs.Claims.Spec2Claims.Claim13bModel_bodyReady_mk
public import Proofs.Claims.Spec2Claims.Claim13bModel_interpretedInputs
public import Proofs.Claims.Spec2Claims.Claim13bModel_readyView
public import Proofs.Claims.Spec2Claims.Claim13bModel_localCovers
public import Proofs.Claims.Spec2Claims.Claim13bModel_token
public import Proofs.Claims.Spec2Claims.Claim13bModel_gradeBool

@[expose] public section

/-!
# Imports for the store-level facts

This file declares nothing; it gathers the imports that the height and grade-window facts on stores
rely on.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

variable {gv₁ gv₂ : Protocol.GradeView V} {eta r : Round}

end DecoupledConsensusModel.Sts
