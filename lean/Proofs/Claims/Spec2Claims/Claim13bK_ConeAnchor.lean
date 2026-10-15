import Proofs.Claims.Spec2Claims.Claim13beRoute3_7
import Proofs.Claims.Spec2Claims.Claim13bModel_GoldfishStore_pool
import Proofs.Claims.Spec2Claims.Claim13bK_GradeOldHeads
import Proofs.Claims.Spec2Claims.Claim13bModel_confirmationReadFrom
import Proofs.Claims.Spec2Claims.Claim13bModel_setClock_inclG1
import Proofs.Claims.Spec2Claims.Claim13bModel_gradeContract_inclG1
import Proofs.Claims.Spec2Claims.Claim13bModel_readFrame_incl
import Proofs.Claims.Spec2Claims.Claim13bModel_get_fg_root
import Proofs.Claims.Spec2Claims.Claim13bModel_round_of
import Proofs.Claims.Spec2Claims.Claim13bModel_a
import Proofs.Claims.Spec2Claims.Claim13bModel_vote_time
import Proofs.Claims.Spec2Claims.Claim13bModel_proposal_time
import Proofs.Claims.Spec2Claims.Claim13bModel_opening
import Proofs.Claims.Spec2Claims.Claim13bModel_domain_attest

/-!
# Slot arithmetic for the readers of a round

Two facts over `Nat` about where the successor of a slot falls relative to a round's opening slot
`a` and the round length `R`.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Slot arithmetic -/

/-- Over `Nat`: if `a + 2 ≤ s ≤ a + R`, then `s + 1` is either `a + j` with `3 ≤ j` and `j + 1 ≤ R`,
    or `a + R + j` with `j ≤ 1`. -/
theorem slot_cases_aux (a R s : Nat) (h0 : a + 2 ≤ s) (h1 : s ≤ a + R) :
    (∃ j : Nat, s + 1 = a + j ∧ 3 ≤ j ∧ j + 1 ≤ R ∧ a + 3 ≤ s + 1 ∧ s + 1 < a + R) ∨
      (∃ j : Nat, j ≤ 1 ∧ s + 1 = a + R + j) := by
  by_cases h : s + 1 < a + R
  · exact Or.inl ⟨s + 1 - a, by omega, by omega, by omega, by omega, h⟩
  · exact Or.inr ⟨s + 1 - (a + R), by omega, by omega⟩

/-- Over `Nat`: if `a + 3 ≤ s + 1 < a + R`, then `s + 1 = a + j` for some `j` with `3 ≤ j < R`. -/
theorem slot_offset_aux (a R s : Nat) (h1 : a + 3 ≤ s + 1) (h2 : s + 1 < a + R) :
    ∃ j : Nat, s + 1 = a + j ∧ 3 ≤ j ∧ j < R :=
  ⟨s + 1 - a, by omega, by omega, by omega⟩

end DecoupledConsensusModel.Sts
