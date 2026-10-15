module
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedEntryCanonical
public import Proofs.Vocabulary.Protocol.Duties.Inputs.FirstProgressFGWitness
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SGCompatibleHistory
public import Proofs.Vocabulary.Protocol.ChainState.FGRootWitness
public import Proofs.Vocabulary.Protocol.ForkChoice.Views.WeakConfirmationSupport
public import Proofs.Vocabulary.Protocol.Grades.RecoveryFGSelectorPrefixSeed
import Proofs.Vocabulary.Protocol.ChainState.Emission
import Proofs.Vocabulary.Protocol.Grades.VoterAnchorSourceInputs
import Proofs.Vocabulary.Protocol.ForkChoice.Views.WeakBootstrapJoin
import Proofs.Vocabulary.Protocol.Grades.CleanReadBridge
import Proofs.Vocabulary.Protocol.Grades.GSTZeroSelectionSafety
import Proofs.Vocabulary.Protocol.Schedule.GSTZeroReorgResilience
import Proofs.Vocabulary.Protocol.Schedule.WeakGoldfishCone

@[expose] public section

/-!
# The prepared vote anchor and a protected block

A prepared vote anchor in round `q + 1` is compatible with a block `T` with which the honest
round-`q` SG emissions are compatible.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Proofs.HealingLemmas
open Internal.PhaseGrades
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
private theorem delayedSource_compatible_ancestor_left
    {A B C : Block V} (hAB : Block.Preceq A B)
    (hBC : Block.compatible B C = true) : Block.compatible A C = true := by
  rcases (show Block.Preceq B C ∨ Block.Preceq C B by
    simpa only [Block.compatible, Bool.or_eq_true, Block.Preceq] using hBC) with hBC | hCB
  · simp only [Block.compatible, Bool.or_eq_true]
    exact Or.inl (Block.preceq_trans hAB hBC)
  · exact Block.compatible_of_preceq_common hAB hCB


private theorem delayedSource_honestRoundVoter_emits_exactAction
    (S : Setup V) {rho : Run V} (core : NamedAdmissibleCore S rho)
    {u : V} {k : Round}
    (hu : u ∈ Internal.NamedOutageEntry.honestRoundVoters S rho k) :
    u ∈ rho.honest ∧
      NamedRun.emits S rho u
        (Object.attest (actionAttestationAt S rho u k)) (S.a k) := by
  obtain ⟨huHon, a, _, haround, hemit⟩ :=
    (Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u k).mp hu
  have hawake : (S.node u).awake k = true := by
    simpa only [haround] using Proofs.Optimistic.emits_attest_awake S hemit
  obtain ⟨i, hi, _⟩ := hemit
  have hhor : S.a k ≤ rho.horizon := by
    have h := core.toNamedScheduleWellFormed.in_horizon
      (Event.tick u (S.a k)) (List.mem_of_getElem? hi)
    simpa only [NamedEvent.time] using h.2
  exact ⟨huHon, honest_emits_exact_actionAttestationAt_of_awake
    S core.toNamedScheduleWellFormed huHon k hawake hhor⟩


/-- An honest validator's prepared vote anchor at a slot of round `q + 1` is compatible with `T`,
    when the honest round-`q` SG emissions are compatible with `T` and the FG root of the
    validator's vote-duty read precedes `T`. -/
theorem voterAnchorAt_compatible_of_previousRelativeCarrier
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q : Round} {d : Slot} (hround : S.hc.round_of d = q + 1)
    (hvoteHor : Protocol.vote_time S.E d ≤ rho.horizon)
    (hwindow : RelativeCarrierWindowAt S rho q .g1)
    (hmajority : Internal.NamedOutageEntry.GradeFormingMajority S rho (q + 1))
    {T : Block V}
    (hprev : HonestSGEmissionsCompatibleAtRound S rho q T)
    {w : V} (hw : w ∈ rho.honest)
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.toHealing.toFG) T) :
    Block.compatible (voterAnchorAt S rho w d) T = true := by
  rcases voterAnchorAt_cases S rho w d with hfg | hactive
  · rw [hfg]
    simpa only [Block.compatible, Bool.or_eq_true, Block.Preceq] using Or.inl hroot
  · obtain ⟨root, A, hframe, hactive, hanchor⟩ := hactive
    rw [hanchor]
    have hslo : S.hc.opening_slot (q + 1) ≤ d := by
      rw [← hround]
      exact Nat.div_mul_le_self d S.hc.R
    have hshi : d < S.hc.opening_slot ((q + 1) + 1) := by
      rw [← hround]
      apply (Nat.div_lt_iff_lt_mul
        (Nat.zero_lt_of_lt S.hc.R_ge_two)).mp
      exact Nat.lt_succ_self (d / S.hc.R)
    have hnext : Protocol.vote_time S.E d ≤
        DecoupledConsensusModel.Protocol.opening S.E S.hc ((q + 1) + 1) := by
      have hvoteNext : Protocol.vote_time S.E d <
          Protocol.proposal_time S.E (d + 1) := by
        apply lt_trans ?_ (support_cutoff_lt_proposal_time_succ S.E d)
        rw [← Proofs.Optimistic.vote_time_add_delta]
        exact Int.lt_add_of_pos_right _ S.E.Δ_pos
      exact hvoteNext.le.trans (by
        simpa only [DecoupledConsensusModel.Protocol.opening] using
          proposal_time_mono S.E (Nat.succ_le_iff.mpr hshi))
    have hframe' : (DecoupledConsensusModel.Protocol.readFrame
        (Internal.NamedRecoveryRead.voteDutyRead S rho w d).cache
        (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.toHealing
        (q + 1)).g1 = some (some root) := by
      have hslot :
          (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.s = d :=
        Proofs.Optimistic.voteDutyRead_slot S rho w d
      simpa only [hslot, hround] using hframe
    obtain ⟨_, hAGrade⟩ := fixedRoot_activeVoterAnchor_g1_data
      S adm (Nat.succ_pos q) hslo hround hnext hvoteHor hw hframe' hactive
    have hgrade : DecoupledConsensusModel.Protocol.gradeBool S.E
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc (q + 1) .g1) w).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc (q + 1) .g1) w).st.core.F
        S.hc.η_SG (q + 1) (early S.E S.hc (q + 1) .g1)
        (late S.E S.hc (q + 1) .g1) A = true := by
      simpa only [PhaseGrades.storeGrade, PhaseGrades.phaseGrade,
        PhaseGrades.readAt] using hAGrade
    obtain ⟨u, hu, hAu⟩ := relativeGrade_has_roundCarrier
      S adm.toNamedAdmissibleCore hwindow hmajority hw hgrade
    obtain ⟨huHon, hemit⟩ := delayedSource_honestRoundVoter_emits_exactAction
      S adm.toNamedAdmissibleCore hu
    exact delayedSource_compatible_ancestor_left hAu (hprev u huHon hemit)

#print axioms voterAnchorAt_compatible_of_previousRelativeCarrier


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
