import Proofs.Claims.Spec2Claims.Claim13bK_GradeOld
import Proofs.Claims.Spec2Claims.Claim13bK_ConeCover
import Proofs.Claims.Spec2Claims.Claim13beRoute3_6
import Proofs.Claims.Spec2Claims.Claim13bModel_stampedBefore
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedStore_initial_stamp
import Proofs.Claims.Spec2Claims.Claim13bModel_a
import Proofs.Claims.Spec2Claims.Claim13bModel_late
import Proofs.Claims.Spec2Claims.Claim13bModel_domain_attest

/-!
# Late cutoffs and domain instants

A round-`(r + 1)` phase's late cutoff is at least three delays after `S.a r`, and a phase's late
cutoff is at or before its domain instant.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

section

variable (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)

end

/-- For every phase `p`, `S.a r + 3Δ ≤ late (r + 1) p`. -/
theorem action_add_three_delta_le_late_succ (S : Setup V) (r : Round) (p : Protocol.Phase) :
    S.a r + 3 * S.E.Δ ≤ Protocol.late S.E S.hc (r + 1) p := by
  have hd := S.E.Δ_pos
  have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  have h1 : S.a (r + 1) = Protocol.opening S.E S.hc (r + 1) + 6 * S.E.Δ :=
    (opening_add_six_delta_eq_a S.E S.hc _).symm
  have h2 := action_succ_eq_add_rounds S r
  have hRd : 12 * S.E.Δ ≤ 4 * (S.hc.R : Int) * S.E.Δ := by nlinarith
  have h3 : Protocol.opening S.E S.hc (r + 1) - 3 * S.E.Δ ≤ Protocol.late S.E S.hc (r + 1) p := by
    cases p <;>
      simp only [late_g0_eq_opening, late_g1_eq_opening, late_g2_eq_opening] <;> linarith
  linarith

/-- For every phase `p`, the late cutoff `late r p` is at or before the domain instant `domain r p`. -/
theorem late_le_domain (S : Setup V) (r : Round) (p : Protocol.Phase) :
    Protocol.late S.E S.hc r p ≤ Protocol.domain S.E S.hc r p := by
  have hd := S.E.Δ_pos
  cases p <;>
    simp only [late_g0_eq_opening, late_g1_eq_opening, late_g2_eq_opening, domain_g0_eq_opening,
      domain_g1_eq_opening, domain_g2_eq_opening] <;> linarith

end DecoupledConsensusModel.Sts
