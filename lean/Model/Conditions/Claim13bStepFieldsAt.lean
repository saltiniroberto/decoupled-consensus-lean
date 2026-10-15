import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bStepAnchor
import Model.Conditions.Claim13bStepConeIter
import Model.Conditions.Claim13bStepPairwise
import Model.Conditions.Claim13bStepSG
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# The step's four facts at one round

The structure `StepFieldsAt` of the four facts the step from round `r` to round `r + 1` reads, at
one round, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The four facts the step from round `r` to round `r + 1` reads, at round `r` with the tick steps
    `n` and `n'` and the round-`r` anchor `T`. -/
structure StepFieldsAt (M : Record.Model V) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (tE : Int) (r : Round) (n n' : Nat) (T : NamedBlock V) : Prop where
  /-- For every choice `att` of the round-`(r + 1)` action attestations, every store an honest
      active attester of round `r + 1` can read at its round-`(r + 1)` action has its confirmed
      block on one chain with the round-`(r + 1)` anchor read along `att`. -/
  confirmedNew : ∀ att : V → NamedAttestation V, Restated.ActionAttestationsOf M S Sched x r n' att →
    ∀ v ∈ Restated.HonRound M S Sched (r + 1),
    ∀ hs ∈ Restated.actionHealingStore M S (x[n'][v].st) (r + 1),
      Block.compatible hs.live_confirmed (Restated.newAnchor M S Sched x r n' att T).erase = true
  /-- For any two honest active attesters of round `r + 1`, any node state of each one's action read
      and any grade frame each of those node states can read, any two blocks the two reads could
      return other than their fgroots, at least one of them a graded block of its own read, lie on
      one chain. -/
  gradePairwise : ∀ v₁ ∈ Restated.HonRound M S Sched (r + 1), ∀ v₂ ∈ Restated.HonRound M S Sched (r + 1),
    ∀ m₁ ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (x[n'][v₁].st) (r + 1),
    ∀ m₂ ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (x[n'][v₂].st) (r + 1),
    ∀ g₁, M.frameGradeRead m₁.cache S.E S.hc (M.toHealing m₁.st.core) (r + 1) ⇢ g₁ →
    ∀ g₂, M.frameGradeRead m₂.cache S.E S.hc (M.toHealing m₂.st.core) (r + 1) ⇢ g₂ →
      Restated.GradePairwise M (M.toHealing m₁.st.core) (M.toHealing m₂.st.core) g₁ g₂
  /-- For every choice `att` of the round-`(r + 1)` action attestations, every block an honest
      active attester of round `r + 1` grades at least 1 for round `r + 1` (in some outcome of the
      grade test) that has the round-`r` anchor as a strict ancestor lies on one chain with the
      round-`(r + 1)` anchor read along `att`. -/
  gradeDescendant : ∀ att : V → NamedAttestation V, Restated.ActionAttestationsOf M S Sched x r n' att →
    ∀ v ∈ Restated.HonRound M S Sched (r + 1),
    ∀ p : Protocol.Phase, M.domain S.E S.hc (r + 1) p ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) →
    ∀ m : Nat, Restated.stepBeforeInstant M x m (M.domain S.E S.hc (r + 1) p) →
    ∀ B : Block V,
      M.gradeBool S.E (M.gradeView (M.toHealing (x[m][v].st).st.core))
          (x[m][v].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) p)
          (M.late S.E S.hc (r + 1) p) B ⇢ true →
      Block.Preceq T.erase B → B ≠ T.erase →
      Block.compatible B (Restated.newAnchor M S Sched x r n' att T).erase = true
  /-- For every choice `att` of the round-`(r + 1)` action attestations, every honest active member
      of the committee of round `(r + 1)`'s third slot votes there for a descendant of the
      round-`(r + 1)` anchor read along `att`. -/
  headsAtNewAnchor : ∀ att : V → NamedAttestation V, Restated.ActionAttestationsOf M S Sched x r n' att →
    Restated.HeadsBelow M S Sched x (Restated.newAnchor M S Sched x r n' att T).erase
      ((M.opening_slot S.hc (r + 1)) + 2)

end

end DecoupledConsensusModel.Sts.Restated
