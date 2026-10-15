import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bStepGrade
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bK_FreshAttestersW
import Model.Conditions.Claim13bStepGrade
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13b
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# Fresh attesters over the attestation window

How `freshAttestersW` relates to `activeRoundW`, `freshAttesters` and `HonRound`, stated over a
model `M : Record.Model V`.
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

/-- `v` is in `freshAttestersW S Sched x r m` exactly when it is in `attestersAt S Sched r` and
    honest through step `m`. -/
theorem mem_freshAttestersW (facts : Record.Facts M) {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (Record.protocolOf M S) Sched} {r : Round} {m : Nat} {v : V} :
    v ∈ Restated.freshAttestersW M S Sched x r m ↔
      v ∈ Restated.attestersAt M S Sched r ∧ Restated.HonestThrough M Sched x m v := by
  classical
  simp [Restated.freshAttestersW]

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- `activeRoundW S Sched r ⊆ activeRound S Sched r`: a validator awake at every time of
    `[S.a r - wAttest S, S.a r]` is awake at every time of `[S.a r - 4Δ, S.a r]`. -/
theorem activeRoundW_subset_activeRound (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (r : Round) :
    Restated.activeRoundW M S Sched r ⊆ Restated.activeRound M S Sched r := by
  intro v hv
  have hact : v ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S r) - wAttest S) ((Restated.Vocabulary.Execution.Setup.a M S r)) := hv
  have hd : (0 : Int) < S.E.Δ := S.E.Δ_pos
  have hw : 12 * S.E.Δ ≤ wAttest S := twelve_delta_le_wAttest S
  show v ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S r) - 4 * S.E.Δ) ((Restated.Vocabulary.Execution.Setup.a M S r))
  exact awakeThroughout_mono Sched hact (by linarith) le_rfl

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- `v ∈ attestersAt S Sched r` exactly when `v` is awake at every time of `[S.a r − 12Δ, S.a r]`:
    the awake rule's grade-2 window of round `r` starts one delay before the grade-2 first cutoff,
    which is `11Δ` before the action instant. -/
theorem mem_attestersAt_iff (facts : Record.Facts M) {S : Setup V} {Sched : Schedule V} {r : Round}
    {v : V} :
    v ∈ Restated.attestersAt M S Sched r ↔
      v ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S r) - 12 * S.E.Δ)
        ((Restated.Vocabulary.Execution.Setup.a M S r)) := by
  have h := facts.gr.early_g2_eq S r
  have he : M.early S.E S.hc r .g2 - S.E.Δ =
      (Restated.Vocabulary.Execution.Setup.a M S r) - 12 * S.E.Δ := by
    show _ = M.a S.hc S.E.Δ r - 12 * S.E.Δ
    rw [h]; ring
  show v ∈ Sched.awakeThroughout (M.early S.E S.hc r .g2 - S.E.Δ) (M.a S.hc S.E.Δ r) ↔ _
  rw [he]

/-- `activeRoundW S Sched r ⊆ attestersAt S Sched r`: a validator awake at every time of
    `[S.a r − wAttest S, S.a r]` is awake at every time of `[S.a r − 12Δ, S.a r]`. -/
theorem activeRoundW_subset_attestersAt (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (r : Round) :
    Restated.activeRoundW M S Sched r ⊆ Restated.attestersAt M S Sched r := by
  intro v hv
  have hact : v ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S r) - wAttest S) ((Restated.Vocabulary.Execution.Setup.a M S r)) := hv
  have hw : 12 * S.E.Δ ≤ wAttest S := twelve_delta_le_wAttest S
  exact (Restated.mem_attestersAt_iff facts).2 (awakeThroughout_mono Sched hact (by linarith) le_rfl)

/-- `attestersAt S Sched r ⊆ activeRound S Sched r`: a validator awake at every time of
    `[S.a r − 12Δ, S.a r]` is awake at every time of `[S.a r − 4Δ, S.a r]`. -/
theorem attestersAt_subset_activeRound (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (r : Round) :
    Restated.attestersAt M S Sched r ⊆ Restated.activeRound M S Sched r := by
  intro v hv
  have hact := (Restated.mem_attestersAt_iff facts).1 hv
  have hd : (0 : Int) < S.E.Δ := S.E.Δ_pos
  show v ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S r) - 4 * S.E.Δ) ((Restated.Vocabulary.Execution.Setup.a M S r))
  exact awakeThroughout_mono Sched hact (by linarith) le_rfl

/-- A member of `attestersAt S Sched r` is awake at every time of `[t, t']` for
    `S.a r − 12Δ ≤ t` and `t' ≤ S.a r`. -/
theorem awakeThroughout_of_mem_attestersAt (facts : Record.Facts M) {S : Setup V}
    {Sched : Schedule V} {r : Round} {v : V} (hv : v ∈ Restated.attestersAt M S Sched r)
    {t t' : Int} (ht : (Restated.Vocabulary.Execution.Setup.a M S r) - 12 * S.E.Δ ≤ t)
    (ht' : t' ≤ (Restated.Vocabulary.Execution.Setup.a M S r)) :
    v ∈ Sched.awakeThroughout t t' :=
  awakeThroughout_mono Sched ((Restated.mem_attestersAt_iff facts).1 hv) ht ht'

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- `freshAttestersW S Sched x r m ⊆ freshAttesters S Sched x r m`. -/
theorem freshAttestersW_subset_freshAttesters (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (r : Round) (m : Nat) :
    Restated.freshAttestersW M S Sched x r m ⊆ Restated.freshAttesters M S Sched x r m := by
  intro v hv
  obtain ⟨hact, hh⟩ := (Restated.mem_freshAttestersW facts).mp hv
  exact (Restated.mem_freshAttesters facts).mpr ⟨Restated.attestersAt_subset_activeRound facts S Sched r hact, hh⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The adversary holds a member of `freshAttestersW S Sched x r m` at no time at or before the time
    of the configuration after `m` steps. -/
theorem honestThrough_of_mem_freshAttestersW (facts : Record.Facts M) {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (Record.protocolOf M S) Sched} {r : Round} {m : Nat} {v : V}
    (hv : v ∈ Restated.freshAttestersW M S Sched x r m) : Restated.HonestThrough M Sched x m v :=
  ((Restated.mem_freshAttestersW facts).mp hv).2

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If the configuration after `m` steps stands at or after round `r`'s action time, then
    `freshAttestersW S Sched x r m ⊆ HonRound S Sched r`. -/
theorem freshAttestersW_subset_honRound (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {r : Round} {m : Nat}
    (hm : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[m].time : Int)) :
    Restated.freshAttestersW M S Sched x r m ⊆ Restated.HonRound M S Sched r := by
  intro v hv
  obtain ⟨hact, hh⟩ := (Restated.mem_freshAttestersW facts).mp hv
  exact Finset.mem_sdiff.mpr ⟨hact, hh ((Restated.Vocabulary.Execution.Setup.a M S r)) hm⟩

end

end DecoupledConsensusModel.Sts.Restated
