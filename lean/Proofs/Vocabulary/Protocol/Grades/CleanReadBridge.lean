module
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.FinalityFilterRetention
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.GradeBootstrapCore
import Proofs.Vocabulary.Generic.PostGSTCarrierAdmissionCore
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.GradeDelivery
import Proofs.Vocabulary.Protocol.ValidatorClient.RecoveryTimeout
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar

@[expose] public section

/-!
# The G2 early cutoff

The phase-based G2 early cutoff of a round is strictly before the round's `Γ_0`.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Internal.NamedRecoveryRead
open Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open Protocol
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]


/-- The G2 early cutoff of round `r` is strictly before the round's `Γ_0`. -/
theorem early_g2_lt_Γ_0 (S : Setup V) (r : Round) :
    early S.E S.hc r .g2 < S.hc.Γ_0 S.E.Δ r := by
  have hopen : opening S.E S.hc r = S.hc.Γ_0 S.E.Δ r :=
    (Protocol.Γ_0_eq_proposal_time S.hc S.E r).symm
  unfold early Phase.earlyOffset
  rw [hopen]
  have hpos : (0 : Int) < S.E.Δ := S.E.Δ_pos
  have hdelta : (-5 : Int) * S.E.Δ < 0 := by omega
  simpa only [zero_mul, add_zero] using
    (Int.add_lt_add_left hdelta (S.hc.Γ_0 S.E.Δ r))

end HealingSurface
end Proofs
end DecoupledConsensusModel

namespace DecoupledConsensusModel.Proofs.HealingSurface
#print axioms early_g2_lt_Γ_0
end DecoupledConsensusModel.Proofs.HealingSurface

end
