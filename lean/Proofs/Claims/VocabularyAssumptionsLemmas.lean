module
public import Proofs.Claims.RunAll
public import Model.Vocabulary.Statements.Generic.Constants
public import Proofs.Vocabulary.Internal.Legacy.Instance
public import Proofs.Vocabulary.Protocol.Handlers.StableOutputSeed
public import Mathlib.Tactic.Bound
public import Mathlib.Topology.Sheaves.Presheaf
public import Proofs.Claims.Spec2Claims.Claim13bModel_Prec_mk
public import Proofs.Claims.Spec2Claims.Claim13bModel_proposal_time
public import Proofs.Claims.Spec2Claims.Claim13bModel_confirmation_time
public import Mathlib.Tactic.Monotonicity.Lemmas

@[expose] public section

/-!
# Membership in the honest set

Membership in `honestThroughSet Sched t` unfolded to `HonestThroughTime Sched t`.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

omit [DecidableEq V] in
/-- A validator `v` is in `honestThroughSet Sched t` exactly when `HonestThroughTime Sched t v`
    holds. -/
theorem mem_honestThroughSet {Sched : Schedule V} {t : Int} {v : V} :
    v ∈ honestThroughSet Sched t ↔ HonestThroughTime Sched t v := by
  classical
  simp [honestThroughSet, HonestThroughTime]

end DecoupledConsensusModel.Sts
