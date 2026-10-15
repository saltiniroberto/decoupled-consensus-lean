import Proofs.Claims.Spec2Claims.Claim13beRoute3_26
import Proofs.Claims.Spec2Claims.Claim13bModel_bodyReady
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedReceiptCalls_postCore
import Proofs.Claims.Spec2Claims.Claim13beRoute3_21
import Proofs.Claims.Spec2Claims.Claim13bModel_Block_slot
import Proofs.Claims.Spec2Claims.Claim13bModel_Env_q
import Proofs.Claims.Spec2Claims.Claim13beRoute3_42b

/-!
# Per-instant forms of the fields

The section variables under which the fields of the run `runAll S Sched x v n` are read at an
instant `tCut` with `0 ≤ tCut ≤ x[n].time`.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]


open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Statements.Instantiation

section PerInstant

variable (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched) (v : V)
  (n : Nat) {tGAT tAwakeEnd : Int}
  (hsync : SynchronyFromWake S x) (hmono : Sched.MonotoneCorruption)
  (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
  (hgst : S.E.t_GST ≤ tGAT) (hcv : CommonViewAtGAT S Sched x tGAT)
  (hvalid : ExecutionValid S Sched (interface S Sched) x)
  (hawm : AwakeAtMultiples S Sched)
  (hthird : ∀ t : Int, t ≤ tAwakeEnd →
    3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
  (hn : (x[n].time : Int) ≤ tAwakeEnd)
  {tCut : Int} (htCut0 : 0 ≤ tCut) (htCutn : tCut ≤ (x[n].time : Int))

end PerInstant

end DecoupledConsensusModel.Sts
