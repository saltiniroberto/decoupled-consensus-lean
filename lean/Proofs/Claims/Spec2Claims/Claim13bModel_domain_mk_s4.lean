module
public import Model.Vocabulary.Execution.Setup
public import Proofs.Claims.ModelIrreducible
public import Proofs.Claims.Spec2Claims.Claim13bModel_a_mk_s4
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# A round's phase domain and its action time

The phase-domain time `Protocol.domain` of a round, against the round's action time.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.Phase.domainOffset
  DecoupledConsensusModel.Protocol.domain

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A round's phase-domain time is at most that round's action time `S.a r`. -/
theorem domain_le_action (S : Setup V) (r : Round) (p : Protocol.Phase) :
    Protocol.domain S.E S.hc r p ≤ S.a r := by
  have hΔ : (0 : Int) < S.E.Δ := S.E.Δ_pos
  show _ ≤ S.hc.a S.E.Δ r
  rw [healA_eq_opening_add_six_delta]
  unfold Protocol.domain
  cases p <;> simp only [Protocol.Phase.domainOffset] <;> linarith

end DecoupledConsensusModel.Sts
