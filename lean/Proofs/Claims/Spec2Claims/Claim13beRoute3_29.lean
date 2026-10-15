import Proofs.Claims.Spec2Claims.Claim13beRoute3_26
import Proofs.Claims.Spec2Claims.Claim13bModel_initial
import Proofs.Claims.Spec2Claims.Claim13bModel_opening
import Proofs.Claims.Spec2Claims.Claim13bModel_gradeView
import Proofs.Claims.Spec2Claims.Claim13bModel_rawInputs
import Proofs.Claims.Spec2Claims.Claim13bModel_postCore
import Proofs.Claims.Spec2Claims.Claim13bModel_gradeBool
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedAttestation_erase
import Proofs.Claims.Spec2Claims.Claim13bModel_readyView
import Proofs.Claims.Spec2Claims.Claim13bModel_interpretedInputs
import Proofs.Claims.Spec2Claims.Claim13bModel_rawView
import Proofs.Claims.Spec2Claims.Claim13bModel_token
import Proofs.Claims.Spec2Claims.Claim13bModel_localCovers
import Proofs.Claims.Spec2Claims.Claim13bModel_bodyReady
import Proofs.Claims.Spec2Claims.Claim13bModel_sgVote
import Proofs.Claims.Spec2Claims.Claim13bModel_domain_attest
import Proofs.Claims.Spec2Claims.Claim13bModel_early
import Proofs.Claims.Spec2Claims.Claim13bModel_late
import Proofs.Claims.Spec2Claims.Claim13bModel_on_sg_vote
import Proofs.Claims.Spec2Claims.Claim13bModel_Store_sg_pool
import Proofs.Claims.Spec2Claims.Claim13bModel_gradeBool_against
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedDuties_attest_with
import Proofs.Claims.Spec2Claims.Claim13bModel_update_confirmation_with
import Proofs.Claims.Spec2Claims.Claim13bModel_positive
import Proofs.Claims.Spec2Claims.Claim13bModel_opposing

/-!
# Round openings against the round window

Round openings are at least `8 * Δ` apart, and the bounds on the openings and cutoffs of the rounds
in round `r`'s window of the latest `η_SG` rounds.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

end DecoupledConsensusModel.Sts

namespace DecoupledConsensusModel.Proofs.NamedRawRelay
open Execution Internal.NamedOutageEntry Internal.NamedStableChainOutage DecoupledConsensusModel.Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

local macro "rr% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Vocabulary.Protocol.Handlers.RawRelay)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.NamedRawRelay ++ n.getId)))

/-- If `q < r`, round `q` opens at least `8 * Δ` before round `r`. -/
theorem opening_add_le_of_lt (S : Setup V) {q r : Round} (h : q < r) :
    opening S.E S.hc q + 8 * S.E.Δ ≤ opening S.E S.hc r := by
  have hR := S.hc.R_ge_two
  have hΔ := S.E.Δ_pos
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt h
  rw [Nat.add_assoc, Sts.opening_add]
  have hR' : (2 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast hR
  have hk : (1 : Int) ≤ ((k + 1 : Nat) : Int) := by push_cast; omega
  have h1 : (2 : Int) ≤ ((k + 1 : Nat) : Int) * (S.hc.R : Int) := by nlinarith
  have h2 : 8 * S.E.Δ ≤ ((k + 1 : Nat) : Int) * (4 * S.E.Δ * (S.hc.R : Int)) := by nlinarith
  linarith

/-- For `q` in the window of the latest `η_SG` rounds before `r`, `opening (r - η_SG) ≤ opening q`
    and `opening q + 8 * Δ ≤ opening r`. -/
theorem opening_bounds_of_window (S : Setup V) {r q : Round}
    (hq : q ∈ Protocol.latest_window S.hc.η_SG r) :
    opening S.E S.hc (r - S.hc.η_SG) ≤ opening S.E S.hc q ∧
      opening S.E S.hc q + 8 * S.E.Δ ≤ opening S.E S.hc r := by
  have hw := (rr% window_bounds) hq
  exact ⟨NamedOutageClosure.opening_mono S hw.1, opening_add_le_of_lt S hw.2⟩

/-- If `lo ≤ opening (r - η_SG)`, some `q` is in `r`'s window, and `opening r - 5 * Δ ≤ c`, then
    `lo ≤ c`. -/
theorem lo_le_cut_of_window (S : Setup V) {r q : Round} {lo c : Int}
    (hlo : lo ≤ opening S.E S.hc (r - S.hc.η_SG))
    (hq : q ∈ Protocol.latest_window S.hc.η_SG r)
    (hc : opening S.E S.hc r - 5 * S.E.Δ ≤ c) : lo ≤ c := by
  obtain ⟨h1, h2⟩ := opening_bounds_of_window S hq
  have hΔ := S.E.Δ_pos
  linarith


end DecoupledConsensusModel.Proofs.NamedRawRelay

namespace DecoupledConsensusModel.Proofs.NamedRawSource
open Execution DecoupledConsensusModel.Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

end DecoupledConsensusModel.Proofs.NamedRawSource

namespace DecoupledConsensusModel.Proofs.NamedOutageHistory.GuardedHelpers
open Internal Execution Internal.PhaseGrades DecoupledConsensusModel.Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

end DecoupledConsensusModel.Proofs.NamedOutageHistory.GuardedHelpers

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Internal.PhaseGrades
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol (Token EquivocationAt Supports Opposes CleanFrom)

variable {V : Type} [DecidableEq V] [Fintype V]

local macro "rcr% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Vocabulary.Protocol.Grades.RelativeCrossReader)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

local macro "rsrc% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Vocabulary.Protocol.Store.RawSource)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.NamedRawSource ++ n.getId)))

end HealingSurface
end Proofs
end DecoupledConsensusModel
