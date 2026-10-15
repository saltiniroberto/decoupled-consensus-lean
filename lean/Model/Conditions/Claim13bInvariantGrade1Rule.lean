import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bInvariant

/-!
# The round invariant's grade-1 clauses over the grade-1 performers of a round

The validators whose grade-1 computation of round `r` runs under the awake rule, `grade1PerformersW`,
and the two clauses of the round invariant about grade-1 results, `grade1` and `gradedUnderPrevSG`,
stated for the grade-1 phase over that set, over a model `M : Record.Model V`.
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

/-- The grade-1 performers of round `r`: the validators awake at every time from one delay before
    round `r`'s grade-1 first cutoff to round `r`'s grade-1 domain instant, and not held by the
    adversary at that instant. -/
def grade1PerformersW (M : Record.Model V) (S : Setup V) (Sched : Schedule V) (r : Round) : Finset V :=
  Sched.awakeThroughout (M.early S.E S.hc r .g1 - S.E.Δ) (M.domain S.E S.hc r .g1) \
    Sched.adv (M.domain S.E S.hc r .g1)

/-- The `grade1` clause of the round invariant at round `r` for the grade-1 phase, over the grade-1
    performers of round `r`: every block a grade-1 performer of round `r` grades at least 1 for round
    `r` at the grade-1 phase, in some outcome of the grade test read at the last step before the
    grade-1 domain instant, lies on one chain with the anchor `T`. -/
def Grade1ClauseOverPerformers (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (r : Round) (T : NamedBlock V) : Prop :=
  ∀ v ∈ grade1PerformersW M S Sched r,
    ∀ m : Nat, Restated.stepBeforeInstant M x m (M.domain S.E S.hc r .g1) →
    ∀ B : Block V, ∀ b : Bool,
    M.gradeBool S.E (M.gradeView (M.toHealing (x[m][v].st).st.core))
        (x[m][v].st).st.core.F S.hc.η_SG r (M.early S.E S.hc r .g1)
        (M.late S.E S.hc r .g1) B ⇢ b → b = true →
    Block.compatible B T.erase = true

/-- The `gradedUnderPrevSG` clause of the round invariant at round `r` for the grade-1 phase, over
    the grade-1 performers of round `r`: at the tick step `n_prev` of round `r − 1`'s action instant,
    every block a grade-1 performer of round `r` grades at least 1 for round `r` at the grade-1 phase
    is an ancestor of the round-`(r − 1)` SG block of some honest active attester of round `r − 1`,
    named by the attestation it sent at that tick. -/
def GradedUnderPrevSGOverPerformers (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (r : Round) (n_prev : Nat) : Prop :=
  ∀ v ∈ grade1PerformersW M S Sched r,
    ∀ m : Nat, Restated.stepBeforeInstant M x m (M.domain S.E S.hc r .g1) →
    ∀ B : Block V, ∀ b : Bool,
    M.gradeBool S.E (M.gradeView (M.toHealing (x[m][v].st).st.core))
        (x[m][v].st).st.core.F S.hc.η_SG r (M.early S.E S.hc r .g1)
        (M.late S.E S.hc r .g1) B ⇢ b → b = true →
    ∃ v_1 ∈ Restated.HonRound M S Sched (r - 1), ∃ a : NamedAttestation V,
      a.round = r - 1 ∧ a.val_index = v_1 ∧
      (⟨v_1, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n_prev + 1].sent ∧
      ∃ C : NamedBlock V, C ∈ (x[n_prev + 1][v_1].st).st.bodies ∧ a.confirmed = some C.root ∧
        Block.Preceq B C.erase

end

end DecoupledConsensusModel.Sts.Restated
