import Model.Conditions.Claim13bInvariantGrade1Rule
import Proofs.Claims.Spec2Claims.Claim13bStepKitConfirm

/-!
# An honest active attester of a round is one of its grade-1 performers

Under monotone corruption, every member of `HonRound M S Sched r` is in
`grade1PerformersW M S Sched r`: the awake rule's grade-2 window of round `r` contains its grade-1
window, and a validator not held at round `r`'s action instant is not held at the earlier grade-1
domain instant. Stated over a model `M : Record.Model V` and its facts `facts : Record.Facts M`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Under monotone corruption, a member of `HonRound S Sched r` is a grade-1 performer of round `r`.

    Variables: `r` the round, `v` the validator. -/
theorem mem_grade1PerformersW_of_honRound (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (hmono : Sched.MonotoneCorruption) {r : Round} {v : V}
    (hv : v ∈ Restated.HonRound M S Sched r) :
    v ∈ Restated.grade1PerformersW M S Sched r := by
  obtain ⟨hw, hadv⟩ := Finset.mem_sdiff.1 hv
  have hw' : v ∈ Sched.awakeThroughout (M.early S.E S.hc r .g2 - S.E.Δ) (M.a S.hc S.E.Δ r) := hw
  have hdom := facts.gr.domain_le_action S r .g1
  have he := facts.gr.early_g2_add_delta_le_early_g1 S r
  have hd := S.E.Δ_pos
  refine Finset.mem_sdiff.2 ⟨awakeThroughout_mono Sched hw' (by linarith) hdom, fun hmem => hadv ?_⟩
  exact hmono _ _ hdom hmem

end

end DecoupledConsensusModel.Sts.Restated
