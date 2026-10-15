import Proofs.Claims.Spec2Claims.Claim13beRoute3_25
import Proofs.Claims.Spec2Claims.Claim13bModel_onPhaseTick
import Proofs.Claims.Spec2Claims.Claim13bModel_occurrenceBefore
import Proofs.Claims.Spec2Claims.Claim13bModel_domain_attest
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedBlock_slot
import Proofs.Claims.Spec2Claims.Claim13bModel_initial
import Proofs.Claims.Spec2Claims.Claim13bModel_setClock
import Proofs.Claims.Spec2Claims.Claim13bModel_stampedBefore
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedStore_initial
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedBlock_erase
import Proofs.Claims.Spec2Claims.Claim13bModel_setClock_inclG2b
import Proofs.Claims.Spec2Claims.Claim13bModel_compatible
import Proofs.Claims.Spec2Claims.Claim13bModel_proposal_time_inclG1
import Proofs.Vocabulary.Protocol.Handlers.TickBridges

/-!
# Proposal instants of positive slots

The proposal instant of every slot after slot `0` is after time `0`.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

/-- The proposal instant of every slot `s > 0` is after time `0`. -/
theorem proposal_time_pos_of_slot_pos (E : Env V) {s : Slot} (hs : 0 < s) :
    0 < Protocol.proposal_time E s := by
  have hΔ := E.Δ_pos
  have hs' : (0 : Int) < (s : Int) := by exact_mod_cast hs
  have h0 := Proofs.Optimistic.proposal_time_nonneg E 0
  have hadd := Sts.proposal_time_add E 0 s
  rw [Nat.zero_add] at hadd
  have hpos : (0 : Int) < 4 * E.Δ * (s : Int) := Int.mul_pos (Int.mul_pos (by norm_num) hΔ) hs'
  rw [hadd]
  linarith

end DecoupledConsensusModel.Protocol

namespace DecoupledConsensusModel.Proofs.NamedRelayGuards
open Execution
variable {V : Type} [DecidableEq V] [Fintype V]

end DecoupledConsensusModel.Proofs.NamedRelayGuards

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
open Internal
open Execution
variable {V : Type} [DecidableEq V] [Fintype V]

end HealingSurface
end Proofs
end DecoupledConsensusModel

namespace DecoupledConsensusModel
namespace Protocol
open Internal
open Execution
variable {V : Type} [DecidableEq V] [Fintype V]

end Protocol
end DecoupledConsensusModel

namespace DecoupledConsensusModel.Proofs.NamedHealthyHeadReady
open Execution
variable {V : Type} [DecidableEq V] [Fintype V]

end DecoupledConsensusModel.Proofs.NamedHealthyHeadReady

namespace DecoupledConsensusModel.Proofs.NamedBlockStamp
open Execution
variable {V : Type} [DecidableEq V] [Fintype V]

end DecoupledConsensusModel.Proofs.NamedBlockStamp


namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
open Internal Execution Internal.HealingSurface Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

end HealingSurface
end Proofs
end DecoupledConsensusModel

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

section FromTGAT

variable (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched) (v : V)
  (H : Finset V) (n : Nat) {tGAT tAwakeEnd : Int}
  (hsync : SynchronyFromWake S x) (hmono : Sched.MonotoneCorruption)
  (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
  (hgst : S.E.t_GST ≤ tGAT) (hcv : CommonViewAtGAT S Sched x tGAT)
  (hvalid : ExecutionValid S Sched (interface S Sched) x)
  (hH : ∀ v₀ ∈ H, v₀ ∉ Sched.adv (x[n].time : Int))
  (hn : (x[n].time : Int) ≤ tAwakeEnd)

include hsync hmono hawake hgst hcv hvalid hH hn

end FromTGAT

end DecoupledConsensusModel.Sts
