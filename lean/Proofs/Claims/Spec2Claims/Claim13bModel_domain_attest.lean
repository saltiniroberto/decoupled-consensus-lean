import Model.Vocabulary.Execution.Setup
import Proofs.Claims.ModelIrreducible

/-!
# `Protocol.domain` and `Protocol.early` against the round's opening

The three phase-domain times of a round and its grade-2 early cutoff, written against the round's
opening time `Protocol.opening S.E S.hc r`.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.Phase.domainOffset
  DecoupledConsensusModel.Protocol.Phase.earlyOffset DecoupledConsensusModel.Protocol.domain
  DecoupledConsensusModel.Protocol.early DecoupledConsensusModel.Protocol.opening
  DecoupledConsensusModel.Protocol.proposal_time

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Round `r`'s grade-2 domain time is its opening minus `Δ`. -/
theorem domain_g2_eq_opening (S : Setup V) (r : Round) :
    Protocol.domain S.E S.hc r .g2 = Protocol.opening S.E S.hc r - S.E.Δ := by
  unfold Protocol.domain
  simp only [Protocol.Phase.domainOffset]
  ring

/-- Round `r`'s grade-1 domain time is its opening. -/
theorem domain_g1_eq_opening (S : Setup V) (r : Round) :
    Protocol.domain S.E S.hc r .g1 = Protocol.opening S.E S.hc r := by
  unfold Protocol.domain
  simp only [Protocol.Phase.domainOffset]
  ring

/-- Round `r`'s grade-0 domain time is its opening plus `Δ`. -/
theorem domain_g0_eq_opening (S : Setup V) (r : Round) :
    Protocol.domain S.E S.hc r .g0 = Protocol.opening S.E S.hc r + S.E.Δ := by
  unfold Protocol.domain
  simp only [Protocol.Phase.domainOffset]
  ring

/-- Round `r`'s grade-2 early cutoff is its opening minus `5Δ`. -/
theorem early_g2_eq_opening (S : Setup V) (r : Round) :
    Protocol.early S.E S.hc r .g2 = Protocol.opening S.E S.hc r - 5 * S.E.Δ := by
  unfold Protocol.early
  simp only [Protocol.Phase.earlyOffset]
  ring

end DecoupledConsensusModel.Sts
