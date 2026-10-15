module
public import Model.Vocabulary.Execution.Setup
public import Proofs.Claims.ModelIrreducible
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# The grade-2 early cutoff against the domain times

A round's grade-2 early cutoff `Protocol.early`, against its phase-domain times `Protocol.domain`
and its opening.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.early
  DecoupledConsensusModel.Protocol.domain DecoupledConsensusModel.Protocol.Phase.earlyOffset
  DecoupledConsensusModel.Protocol.Phase.domainOffset

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A round's grade-2 early cutoff is strictly before each of its phase-domain times. -/
theorem early_g2_lt_domain (S : Setup V) (r : Round) (p : Protocol.Phase) :
    Protocol.early S.E S.hc r .g2 < Protocol.domain S.E S.hc r p := by
  cases p <;>
    simp only [Protocol.early, Protocol.domain, Protocol.Phase.earlyOffset,
      Protocol.Phase.domainOffset] <;>
    linarith [S.E.Δ_pos]

/-- A round's grade-2 early cutoff is at most the round's opening time. -/
theorem early_g2_le_opening (S : Setup V) (r : Round) :
    Protocol.early S.E S.hc r .g2 ≤ Protocol.opening S.E S.hc r := by
  simp only [Protocol.early, Protocol.Phase.earlyOffset]
  linarith [S.E.Δ_pos]

end DecoupledConsensusModel.Sts
