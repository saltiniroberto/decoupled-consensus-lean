import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bStepAnchor
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# The grade-1 clause at the new anchor

The `grade1` clause of the invariant at round `r + 1`, at the round-`(r + 1)` anchor, over the
honest active attesters; stated over a model `M : Record.Model V`.
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

/-- For a choice `att` of attestations, every block an honest active attester of round `r + 1` can
    grade at least 1 for that round, at any phase of it whose domain instant is at or before the
    round's action instant, lies on one chain with the round-`(r + 1)` anchor read along `att`. -/
theorem grade1_field_at_new_anchor_overActiveSets (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {r : Round} {n' : Nat}
    {att : V → NamedAttestation V} {T : NamedBlock V}
    (hold : Block.Preceq T.erase (Restated.newAnchor M S Sched x r n' att T).erase)
    (hgrade1 : ∀ v ∈ Restated.HonRound M S Sched (r + 1),
      ∀ p : Protocol.Phase, M.domain S.E S.hc (r + 1) p ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) →
      ∀ m : Nat, Restated.stepBeforeInstant M x m (M.domain S.E S.hc (r + 1) p) →
      ∀ B : Block V,
      M.gradeBool S.E (M.gradeView (M.toHealing (x[m][v].st).st.core))
          (x[m][v].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) p)
          (M.late S.E S.hc (r + 1) p) B ⇢ true →
      Block.compatible B T.erase = true)
    (hdesc : ∀ v ∈ Restated.HonRound M S Sched (r + 1),
      ∀ p : Protocol.Phase, M.domain S.E S.hc (r + 1) p ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) →
      ∀ m : Nat, Restated.stepBeforeInstant M x m (M.domain S.E S.hc (r + 1) p) →
      ∀ B : Block V,
      M.gradeBool S.E (M.gradeView (M.toHealing (x[m][v].st).st.core))
          (x[m][v].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) p)
          (M.late S.E S.hc (r + 1) p) B ⇢ true →
      Block.Preceq T.erase B → B ≠ T.erase →
      Block.compatible B (Restated.newAnchor M S Sched x r n' att T).erase = true) :
    ∀ v ∈ Restated.HonRound M S Sched (r + 1),
      ∀ p : Protocol.Phase, M.domain S.E S.hc (r + 1) p ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) →
      ∀ m : Nat, Restated.stepBeforeInstant M x m (M.domain S.E S.hc (r + 1) p) →
      ∀ B : Block V,
      M.gradeBool S.E (M.gradeView (M.toHealing (x[m][v].st).st.core))
          (x[m][v].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) p)
          (M.late S.E S.hc (r + 1) p) B ⇢ true →
      Block.compatible B (Restated.newAnchor M S Sched x r n' att T).erase = true := by
  classical
  intro v hv p hp m hm B hB
  rcases compatible_cases (hgrade1 v hv p hp m hm B hB) with hle | hge
  · exact compatible_of_preceq_common_Preceq (preceq_trans_Preceq hle hold)
      (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _))
  · by_cases heq : B = T.erase
    · rw [heq]
      exact compatible_of_preceq_common_Preceq hold
        (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _))
    · exact hdesc v hv p hp m hm B hB hge heq

end

end DecoupledConsensusModel.Sts.Restated
