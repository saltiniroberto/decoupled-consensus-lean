import Proofs.Claims.Spec2Claims.Claim13beRoute3_29
import Mathlib.Tactic.Polynomial.Basic
import Proofs.Claims.Spec2Claims.Claim13bModel_readFrame_attest
import Proofs.Claims.Spec2Claims.Claim13bModel_actionStoreAt
import Proofs.Claims.Spec2Claims.Claim13bModel_toHealing
import Proofs.Claims.Spec2Claims.Claim13bModel_Preceq
import Proofs.Claims.Spec2Claims.Claim13bModel_localCovers
import Proofs.Claims.Spec2Claims.Claim13bModel_compatible
import Proofs.Claims.Spec2Claims.Claim13bModel_get_filtered_block_tree
import Proofs.Claims.Spec2Claims.Claim13bModel_opening
import Proofs.Claims.Spec2Claims.Claim13bModel_confirmationReadFrom
import Proofs.Claims.Spec2Claims.Claim13bModel_setClock_incl
import Proofs.Claims.Spec2Claims.Claim13bModel_activePrefix
import Proofs.Claims.Spec2Claims.Claim13bModel_freezeRoot
import Proofs.Claims.Spec2Claims.Claim13bModel_gradeView
import Proofs.Claims.Spec2Claims.Claim13bModel_gradeContract
import Proofs.Claims.Spec2Claims.Claim13bModel_frameGradeRead_attest
import Proofs.Claims.Spec2Claims.Claim13bModel_clear
import Proofs.Claims.Spec2Claims.Claim13bModel_domain_attest
import Proofs.Claims.Spec2Claims.Claim13bModel_early
import Proofs.Claims.Spec2Claims.Claim13bModel_anchor
import Proofs.Claims.Spec2Claims.Claim13bModel_gradeContract_inclG1
import Proofs.Vocabulary.ModelProperties.Block_Preceq
import Proofs.Vocabulary.ModelProperties.get_filtered_block_tree
import Proofs.Vocabulary.Protocol.Grades.ProposalParent
import Proofs.Vocabulary.ModelProperties.readFrame

/-!
# Grade cutoffs of a positive round against a lower instant

The cutoffs and domain instants of a positive round are at or after a lower instant `lo` whenever
the first round of its window opens at or after `lo`.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Proofs.NamedRawRelay
open Execution Internal.NamedOutageEntry Internal.NamedStableChainOutage DecoupledConsensusModel.Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

/-- For `0 < r`, the first round of `r`'s window opens at least `8 * Δ` before round `r`:
    `opening (r - η_SG) + 8 * Δ ≤ opening r`. -/
theorem opening_window_start_add_le (S : Setup V) {r : Round} (hr : 0 < r) :
    opening S.E S.hc (r - S.hc.η_SG) + 8 * S.E.Δ ≤ opening S.E S.hc r :=
  opening_add_le_of_lt S (Nat.sub_lt hr S.hc.η_SG_ge_one)

/-- For `0 < r` and `lo ≤ opening (r - η_SG)`, `lo ≤ early r g2`. -/
theorem lo_le_early_g2_of_window_start (S : Setup V) {r : Round} (hr : 0 < r) {lo : Time}
    (hlo : lo ≤ opening S.E S.hc (r - S.hc.η_SG)) : lo ≤ early S.E S.hc r .g2 := by
  have h := opening_window_start_add_le S hr
  have hΔ := S.E.Δ_pos
  rw [Sts.early_g2_eq_opening]
  linarith

end DecoupledConsensusModel.Proofs.NamedRawRelay

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Internal.PhaseGrades
open Internal.NamedRecoveryRead
open DecoupledConsensusModel.Protocol
open Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

end HealingSurface
end Proofs
end DecoupledConsensusModel

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Internal.PhaseGrades
open Protocol Proofs.HealingLemmas Proofs.Optimistic DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

local macro "rsk% " n:ident : term =>
  `(priv% $(Lean.mkIdent `DecoupledConsensusProofs.Protocol.Grades.RelativeSeedK3)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

end HealingSurface
end Proofs
end DecoupledConsensusModel

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

end HealingSurface
end Proofs
end DecoupledConsensusModel

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface
open Protocol Proofs.HealingLemmas Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]

end HealingSurface
end Proofs
end DecoupledConsensusModel

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Internal.PhaseGrades
open Internal.NamedRecoveryRead Protocol
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

local macro "sq2% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Vocabulary.Protocol.Grades.SameRoundQ2Retained)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

end HealingSurface
end Proofs
end DecoupledConsensusModel

namespace DecoupledConsensusModel.Proofs.NamedRawRelay
open Execution Internal.NamedOutageEntry Internal.NamedStableChainOutage DecoupledConsensusModel.Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

/-- For `0 < r`, `lo ≤ opening (r - η_SG)` and `opening r - 5 * Δ ≤ c`, `lo ≤ c`. -/
theorem lo_le_of_window_start (S : Setup V) {r : Round} (hr : 0 < r) {lo c : Time}
    (hlo : lo ≤ opening S.E S.hc (r - S.hc.η_SG))
    (hc : opening S.E S.hc r - 5 * S.E.Δ ≤ c) : lo ≤ c := by
  have h := opening_window_start_add_le S hr
  have hΔ := S.E.Δ_pos
  linarith

/-- For `0 < r` and `lo ≤ opening (r - η_SG)`, `lo ≤ domain r p` for every phase `p`. -/
theorem lo_le_domain_of_window_start (S : Setup V) {r : Round} (hr : 0 < r) {lo : Time}
    (hlo : lo ≤ opening S.E S.hc (r - S.hc.η_SG)) (p : Phase) : lo ≤ domain S.E S.hc r p := by
  apply lo_le_of_window_start S hr hlo
  have hΔ := S.E.Δ_pos
  cases p
  · rw [Sts.domain_g0_eq_opening]; linarith
  · rw [Sts.domain_g1_eq_opening]; linarith
  · rw [Sts.domain_g2_eq_opening]; linarith

end DecoupledConsensusModel.Proofs.NamedRawRelay

namespace DecoupledConsensusModel.Proofs.FrameCompleted
open Execution Protocol DecoupledConsensusModel.Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

end DecoupledConsensusModel.Proofs.FrameCompleted

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

end HealingSurface
end Proofs
end DecoupledConsensusModel

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

local macro "sgt% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SGTargetCanonicalityFixedRoot)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))


end HealingSurface
end Proofs
end DecoupledConsensusModel

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]


end HealingSurface
end Proofs
end DecoupledConsensusModel

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Internal.PhaseGrades
open Internal.NamedRecoveryRead
open DecoupledConsensusModel.Protocol
open Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

local macro "rgc% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.Grades.RecoveryGenuineClearNextVote)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))


end HealingSurface
end Proofs
end DecoupledConsensusModel

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Internal.PhaseGrades
open Protocol
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]


end HealingSurface
end Proofs
end DecoupledConsensusModel
