import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bInvariantActiveSince
import Model.Conditions.Claim13bK_GradePairwise
import Model.Conditions.Claim13bStepConeIter
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# The round invariant with facts about the previous round

The round invariant `AfterPhaseInvariantOverActiveSetsSince`, extended by three facts about the
round before, stated over a model `M : Record.Model V`.
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

/-- The invariant `AfterPhaseInvariantOverActiveSetsSince` at round `r`, tick step `n`, switch-round
    tick step `n_W` and anchor `T`, extended by a tick step at round `r − 1`'s action time and three
    facts about round `r − 1` at every such step. -/
structure AfterPhaseInvariantOverActiveSetsJoint (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (r : Round) (n : Nat) (n_W : Nat)
    (T : NamedBlock V) : Prop extends Restated.AfterPhaseInvariantOverActiveSetsSince M S Sched x r n n_W T where
  /-- Some step is the framework's tick at round `r − 1`'s action time. -/
  prevTick : ∃ n_prev : Nat, Restated.tickStepAt M x n_prev ((Restated.Vocabulary.Execution.Setup.a M S (r - 1)))
  /-- At every round-`(r − 1)` tick step, every block named as confirmed by the round-`(r − 1)`
      attestation of an honest active attester of round `r − 1` is an ancestor of the block every
      honest active member of the committee of round `r`'s opening slot votes for there. -/
  prevHeads : ∀ n_prev : Nat, Restated.tickStepAt M x n_prev ((Restated.Vocabulary.Execution.Setup.a M S (r - 1))) →
    ∀ v_1 ∈ Restated.HonRound M S Sched (r - 1), ∀ a : NamedAttestation V,
      a.round = r - 1 → a.val_index = v_1 →
      (⟨v_1, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n_prev + 1].sent →
      ∀ C : NamedBlock V, C ∈ (x[n_prev + 1][v_1].st).st.bodies → a.confirmed = some C.root →
      Restated.HeadsBelow M S Sched x C.erase ((M.opening_slot S.hc r))
  /-- At every round-`(r − 1)` tick step, `ConfirmedCompatibleFreshSGOverHonRound` holds at round
      `r − 1` up to step `n`: every round-`(r − 1)` SG block of an honest active attester of round
      `r − 1` lies on one chain with the confirmed block of every honest active attester of round
      `r`. -/
  prevConfirmed : ∀ n_prev : Nat, Restated.tickStepAt M x n_prev ((Restated.Vocabulary.Execution.Setup.a M S (r - 1))) →
    Restated.ConfirmedCompatibleFreshSGOverHonRound M S Sched x (r - 1) n_prev n
  /-- At every round-`(r − 1)` tick step, every block an honest active attester of round `r` grades
      at least 1 for round `r` (in some outcome of the grade test), at any phase whose domain time
      is no later than round `r`'s action time, is an ancestor of the round-`(r − 1)` SG block of
      some honest active attester of round `r − 1`. -/
  gradedUnderPrevSG : ∀ n_prev : Nat, Restated.tickStepAt M x n_prev ((Restated.Vocabulary.Execution.Setup.a M S (r - 1))) →
    ∀ v ∈ Restated.HonRound M S Sched r, ∀ p : Protocol.Phase,
      M.domain S.E S.hc r p ≤ (Restated.Vocabulary.Execution.Setup.a M S r) →
      ∀ m : Nat, Restated.stepBeforeInstant M x m (M.domain S.E S.hc r p) →
      ∀ B : Block V, ∀ b : Bool,
      M.gradeBool S.E (M.gradeView (M.toHealing (x[m][v].st).st.core))
          (x[m][v].st).st.core.F S.hc.η_SG r (M.early S.E S.hc r p)
          (M.late S.E S.hc r p) B ⇢ b → b = true →
      ∃ v_1 ∈ Restated.HonRound M S Sched (r - 1), ∃ a : NamedAttestation V,
        a.round = r - 1 ∧ a.val_index = v_1 ∧
        (⟨v_1, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n_prev + 1].sent ∧
        ∃ C : NamedBlock V, C ∈ (x[n_prev + 1][v_1].st).st.bodies ∧ a.confirmed = some C.root ∧
          Block.Preceq B C.erase

end

end DecoupledConsensusModel.Sts.Restated
