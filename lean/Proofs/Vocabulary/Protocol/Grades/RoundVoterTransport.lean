module
public import Proofs.Vocabulary.Protocol.Grades.PostOutage
public import Proofs.Vocabulary.Protocol.Handlers.SGArrivalStampCarrier
public import Proofs.Vocabulary.Protocol.Grades.HealthyHeadReady
public import Mathlib.Algebra.Order.Archimedean.Basic
import Proofs.Vocabulary.Execution.EmissionShape
import Proofs.Vocabulary.Protocol.Grades.GradeFormsBridge
import Proofs.Vocabulary.Protocol.Grades.Persistence
import Proofs.Vocabulary.Protocol.Schedule.Action
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar

@[expose] public section

/-!
# Honest round voters after GST

An honest round-`r` action attestation, the block it confirms, and its place in the raw inputs of
round `r + 1`.
-/


namespace DecoupledConsensusModel.Proofs.NamedOutageClosure

open Internal Execution Internal.NamedOutageEntry Internal.NamedStableChainOutage
open Internal.NamedJointOutage
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Membership in `honestRoundVoters` has an exact named emission witness. -/
theorem honestRoundVoter_emits
    (S : Setup V) (rho : NamedRun V) {u : V} {r : Round}
    (hu : u ∈ honestRoundVoters S rho r) :
    ∃ a : NamedAttestation V, a.round = r ∧ a.val_index = u ∧
      NamedRun.emits S rho u (.attest a) (S.a r) := by
  obtain ⟨_, a, hval, hround, hemit⟩ :=
    (Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u r).mp hu
  exact ⟨a, hround, hval, hemit⟩

/-- An honest round-`r` action attestation confirms the root of `actionSGBlockAt` for that action. -/
theorem honest_emitted_round_confirmed
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (u : V) (hu : u ∈ rho.honest) (r : Round) (hhor : S.a r ≤ rho.horizon)
    {a : NamedAttestation V} (haround : a.round = r)
    (hemit : NamedRun.emits S rho u (.attest a) (S.a r)) :
    a.confirmed = some (Proofs.HealingSurface.actionSGBlockAt S rho u r).root := by
  have hawake : (S.node u).awake r = true := by
    simpa only [haround] using Proofs.Optimistic.emits_attest_awake S hemit
  have hcanonical := Proofs.HealingSurface.honest_emits_exact_actionAttestationAt_of_awake
    S core.toNamedScheduleWellFormed hu r hawake hhor
  have ha : a = Proofs.HealingSurface.actionAttestationAt S rho u r := by
    apply Proofs.Optimistic.emits_attest_unique S core.toNamedScheduleWellFormed
      hemit hcanonical
    simpa only [haround] using
      (Proofs.HealingSurface.actionAttestationAt_shape S rho u r).2.1.symm
  rw [ha]
  exact (Proofs.HealingSurface.actionAttestationAt_shape S rho u r).2.2


/-- An honest raw input of a round-`(r + 1)` read is the projection of the sender's own attestation
    for that input's round, emitted at that round's action time. -/
theorem honest_rawInput_is_own_round_vote
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (cut cutoff : Time) (w : V) (_hw : w ∈ rho.honest)
    {u : V} (hu : u ∈ rho.honest) {r : Round} {y : Protocol.SGVote V}
    (hy : y ∈ rawInputs
      (NamedRun.stateBeforeTime S rho cut w).st.core.toHealing.gradeView
      S.hc.η_SG (r + 1) cutoff u) :
    ∃ a : NamedAttestation V,
      a.round = y.round ∧ a.val_index = u ∧
      NamedRun.emits S rho u (.attest a) (S.a y.round) ∧
      y.val_index = a.val_index ∧ y.confirmed = a.confirmed ∧
      emittedInRound S rho u y.round = true ∧
      r + 1 - S.hc.η_SG ≤ y.round ∧ y.round ≤ r := by
  obtain ⟨a, hval, hround, hproj, hwindow, _, hemit⟩ :=
    rawInputs_trace S rho core.toNamedScheduleWellFormed
      core.toNamedUnforgeable cut cutoff w S.hc.η_SG (r + 1) u hu hy
  obtain ⟨hlower, hupper⟩ := window_bounds hwindow
  refine ⟨a, hround, hval, ?_, ?_, ?_, ?_, hlower, ?_⟩
  · simpa only [hround] using hemit
  · rw [← hproj, sgVote_val]
  · rw [← hproj, sgVote_confirmed]
  · apply (Proofs.NamedOutageInputs.emittedInRound_iff S rho u y.round).mpr
    exact ⟨a, hval, hround, by simpa only [hround] using hemit⟩
  · exact Nat.le_of_lt_succ (by simpa only [Nat.add_comm] using hupper)


#print axioms honestRoundVoter_emits
#print axioms honest_emitted_round_confirmed
#print axioms honest_rawInput_is_own_round_vote


end DecoupledConsensusModel.Proofs.NamedOutageClosure

end
