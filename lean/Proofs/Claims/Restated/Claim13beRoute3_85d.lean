import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bInvariantActiveSinceW
import Proofs.Claims.Restated.Claim13bKit
import Proofs.Claims.Restated.Claim13beRoute3_15
import Proofs.Claims.Restated.Claim13beRoute3_44
import Proofs.Claims.Restated.Claim13beRoute3_45
import Proofs.Claims.Restated.Claim13beRoute3_45b
import Proofs.Claims.Restated.Claim13beRoute3_46
import Proofs.Claims.Restated.Claim13beRoute3_47b
import Proofs.Claims.Restated.Claim13beRoute3_48
import Proofs.Claims.Restated.Claim13beRoute3_49
import Proofs.Claims.Restated.Claim13beRoute3_51
import Proofs.Claims.Restated.Claim13beRoute3_52
import Proofs.Claims.Restated.Claim13beRoute3_58
import Proofs.Claims.Restated.Claim13beRoute3_65b
import Proofs.Claims.Restated.Claim13beRoute3_67b
import Proofs.Claims.Restated.Claim13beRoute3_71
import Proofs.Claims.Restated.Claim13beRoute3_72
import Proofs.Claims.Restated.Claim13beRoute3_78
import Proofs.Claims.Restated.Claim13beRoute3_83
import Proofs.Claims.Restated.Claim13beRoute3_85b
import Proofs.Claims.Restated.Claim13beRoute3_86e
import Proofs.Claims.Restated.Claim13beRoute3_86f
import Proofs.Claims.Restated.Claim13beRoute3_86g
import Proofs.Claims.Restated.Claim13beRoute3_87b
import Proofs.Claims.Restated.Vocabulary_Execution_ExcludesRefute
import Proofs.Claims.Restated.Vocabulary_Execution_OutageInputs
import Proofs.Claims.Restated.Vocabulary_ModelVocabulary_Healing_Schedule
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_ProposalBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_ReaderLocalCone
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_RecoveryProposalConfirmationRead
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_SGRepresentation
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Head_PreparedProposalReadBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_Grades
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_Interpolation
import Proofs.Vocabulary.Protocol.Grades.RelativeSupporter
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_JustificationBound
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_TickBridges
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_PostHealingContinuation
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bInvariantActiveSinceW
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.Claim13beRoute3_72
import Model.Conditions.Claim13beRoute3_83
import Model.Conditions.RunAll
import Model.Conditions.RunVocabulary
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Internal_Definitions_NamedDerived
import Model.Conditions.Vocabulary_Internal_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Definitions_NamedOutageEntry
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGradeQueries
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Internal_Invariants
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedHeadReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ProposalSourcesInternal
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedActionReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_MajoritySG_ForkChoice
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_ModelVocabulary_Healing_Schedule
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Vocabulary.Protocol.Grades
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Proofs.Vocabulary.Protocol.ForkChoice.Views.ProposalCore
import Model.Conditions.Vocabulary_Protocol_Handlers_Blocks
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Conditions.Vocabulary_Statements_Instantiation_RoundTimes
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_25
import Proofs.Claims.Spec2Claims.Claim13beRoute3_85d

/-!
# Strong windows after the re-based deadline round

The instants of a round and its opening slot, two strong windows given by the recurrence of strong
openings, and the facts about the proposals of a window's slots: the opening proposal is at least as
high as the re-based round's anchor, the proposal of the window's third slot has the opening
proposal as an ancestor of its parent, and it is held by every honest store from its vote instant
on. Stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

/-- A private theorem of the page `lean/Proofs/Claims/Restated/Claim13beRoute3_86g.lean`, by name. -/
local macro "p86g% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_86g)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- A private theorem of the page `lean/Proofs/Claims/Restated/Claim13beRoute3_86f.lean`, by name. -/
local macro "p86f% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_86f)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- A private theorem of the page `lean/Proofs/Claims/Restated/Claim13beRoute3_58.lean`, by name. -/
local macro "p58% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_58)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- A private theorem of the page `lean/Proofs/Claims/Restated/Claim13beRoute3_60.lean`, by name. -/
local macro "p60% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_60)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- A private theorem of the page `lean/Proofs/Claims/Restated/Claim13beRoute3_56.lean`, by name. -/
local macro "p56% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_56)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- A private theorem of the page `lean/Proofs/Claims/Restated/Claim13beRoute3_55.lean`, by name. -/
local macro "p55% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_55)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- A private theorem of the page `lean/Proofs/Claims/Restated/Claim13beRoute3_64b.lean`, by name. -/
local macro "p64b% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_64b)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- A private theorem of the page `lean/Proofs/Claims/Restated/Claim13beRoute3_71.lean`, by name. -/
local macro "p71% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_71)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- A private theorem of the page `lean/Proofs/Claims/Restated/Claim13beRoute3_86c.lean`, by name. -/
local macro "p86c% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_86c)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog

/-- The action instant of round `r`: `S.a r = 4Δ · R · r + 6Δ`. -/
theorem action_eq_l85d (facts : Record.Facts M) (S : Setup V) (r : Round) :
    Restated.Vocabulary.Execution.Setup.a M S r
      = 4 * S.E.Δ * (S.hc.R : Int) * (r : Int) + 6 * S.E.Δ := by
  have h := Restated.action_add_eq_add_period_mul facts S 0 r
  rw [Nat.zero_add, Restated.period_eq facts S] at h
  have h0 : Restated.Vocabulary.Execution.Setup.a M S 0 = 6 * S.E.Δ := by
    show M.a S.hc S.E.Δ 0 = _
    rw [facts.sch.a_eq_confirmation_time S.hc S.E 0,
      ← facts.sch.slotStart_add_six_delta_eq_confirmation_time, facts.gr.opening_slot_zero_mk]
    simp [slotStart]
  rw [h, h0]
  ring

/-- The proposal instant of round `r`'s opening slot is `4Δ · R · r`. -/
theorem proposal_time_opening_eq_l85d (facts : Record.Facts M) (S : Setup V) (r : Round) :
    M.proposal_time S.E ((M.opening_slot S.hc r)) = 4 * S.E.Δ * (S.hc.R : Int) * (r : Int) := by
  have h1 : Restated.Vocabulary.Execution.Setup.a M S r
      = M.confirmation_time S.E (M.opening_slot S.hc r) :=
    facts.sch.a_eq_confirmation_time S.hc S.E r
  have h2 := (facts.sch.slot_instants_l55 S.E (M.opening_slot S.hc r)).2.2.2.2.2
  have h3 := Restated.action_eq_l85d facts S r
  linarith

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog

/-- If the recurrence of strong openings holds from `tGAT` to `tAwakeEnd`, round `r`'s opening is
    proposed at or after `tGAT`, and its window of `gap` periods ends by `tAwakeEnd`, then some
    round `c` with `r + 2 ≤ c ≤ r + gap` has the proposers of `o_c`, `o_c + 1`, `o_c + 2`,
    `o_{c − 1}` and `o_{c − 2}` each not held at its own slot's confirmation instant. -/
theorem strongWindow_of_recurrence_l85d (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    {tGAT tAwakeEnd : Int} {gap : Nat}
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tAwakeEnd gap) {r : Round}
    (hstart : tGAT ≤ M.proposal_time S.E ((M.opening_slot S.hc r)))
    (hwin : M.proposal_time S.E ((M.opening_slot S.hc r)) + (gap : Int) * ((Restated.Vocabulary.Execution.Setup.a M S 1) - (Restated.Vocabulary.Execution.Setup.a M S 0))
      ≤ tAwakeEnd) :
    ∃ c : Round, r + 2 ≤ c ∧ c ≤ r + gap ∧
      (∀ k < 3, S.E.proposer ((M.opening_slot S.hc c) + k) ∈
        notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c) + k))) ∧
      S.E.proposer ((M.opening_slot S.hc (c - 1))) ∈
        notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc (c - 1)))) ∧
      S.E.proposer ((M.opening_slot S.hc (c - 2))) ∈
        notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc (c - 2)))) := by
  obtain ⟨s, hlo, hhi, hmp, hprevs⟩ := hrec _ hstart hwin
  obtain ⟨c, rfl⟩ := hmp.1
  have hΔ := S.E.Δ_pos
  have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  have hP : (0 : Int) < 4 * S.E.Δ * (S.hc.R : Int) := by positivity
  have hper : (Restated.constants M S).period = 4 * S.E.Δ * (S.hc.R : Int) :=
    Restated.period_eq facts S
  have hlo' : M.proposal_time S.E ((M.opening_slot S.hc r)) + 2 * (Restated.constants M S).period ≤
      M.proposal_time S.E ((M.opening_slot S.hc c)) := hlo
  have hhi' : M.proposal_time S.E ((M.opening_slot S.hc c)) ≤
      M.proposal_time S.E ((M.opening_slot S.hc r)) + (gap : Int) * (Restated.constants M S).period := hhi
  rw [Restated.proposal_time_opening_eq_l85d facts, Restated.proposal_time_opening_eq_l85d facts,
    hper] at hlo' hhi'
  have hc2 : r + 2 ≤ c := by
    have h2 : 4 * S.E.Δ * (S.hc.R : Int) * ((r : Int) + 2) ≤
        4 * S.E.Δ * (S.hc.R : Int) * (c : Int) := by nlinarith
    have := le_of_mul_le_mul_left h2 hP
    exact_mod_cast this
  have hcg : c ≤ r + gap := by
    have h2 : 4 * S.E.Δ * (S.hc.R : Int) * (c : Int) ≤
        4 * S.E.Δ * (S.hc.R : Int) * ((r : Int) + (gap : Int)) := by nlinarith
    have := le_of_mul_le_mul_left h2 hP
    exact_mod_cast this
  have hprevAt : ∀ j : Nat, 1 ≤ j → j ≤ 2 →
      S.E.proposer ((M.opening_slot S.hc (c - j))) ∈
        notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc (c - j)))) := by
    intro j hj1 hj2
    have hjc : j ≤ c := le_trans hj2 (le_trans (Nat.le_add_left 2 r) hc2)
    have hcast : ((c - j : Nat) : Int) = (c : Int) - (j : Int) := by push_cast [Nat.cast_sub hjc]; ring
    have hj1' : (1 : Int) ≤ (j : Int) := by exact_mod_cast hj1
    have hj2' : (j : Int) ≤ 2 := by exact_mod_cast hj2
    have h1 : (Restated.interface M S Sched).proposalTime ((M.opening_slot S.hc c)) - 2 * (Restated.constants M S).period ≤
        (Restated.interface M S Sched).proposalTime ((M.opening_slot S.hc (c - j))) := by
      change M.proposal_time S.E ((M.opening_slot S.hc c)) - 2 * (Restated.constants M S).period ≤
        M.proposal_time S.E ((M.opening_slot S.hc (c - j)))
      rw [Restated.proposal_time_opening_eq_l85d facts, Restated.proposal_time_opening_eq_l85d facts,
        hper, hcast]
      nlinarith
    have h2 : (Restated.interface M S Sched).proposalTime ((M.opening_slot S.hc (c - j))) <
        (Restated.interface M S Sched).proposalTime ((M.opening_slot S.hc c)) := by
      change M.proposal_time S.E ((M.opening_slot S.hc (c - j))) <
        M.proposal_time S.E ((M.opening_slot S.hc c))
      rw [Restated.proposal_time_opening_eq_l85d facts, Restated.proposal_time_opening_eq_l85d facts,
        hcast]
      nlinarith
    have hh := hprevs ((M.opening_slot S.hc (c - j))) ⟨c - j, rfl⟩ h1 h2
    exact mem_notHeldAt.mpr (hh _ le_rfl)
  refine ⟨c, hc2, hcg, ?_, hprevAt 1 le_rfl (by decide), hprevAt 2 (by decide) le_rfl⟩
  intro k hk
  exact mem_notHeldAt.mpr (hmp.2 k hk _ le_rfl)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog

/-- If `t_GST ≤ tGAT`, `tGAT + healingLengthη S gap ≤ tE` and the recurrence of strong openings
    holds from `tGAT` to `tE`, then there are rounds `c₁ < c₂` with `rD' + 3 ≤ c₁`,
    `c₁ + tD / R ≤ c₂ ≤ c₁ + tD / R + gap` and `c₂ + 1` at most the switch round, and for each of
    them the proposers of its opening slot, of the next two slots and of the two previous openings
    are not held at their own confirmation instants. -/
theorem twoStrongWindows_l85d (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) {tGAT tE : Int} {gap : Nat}
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap) :
    ∃ c₁ c₂ : Round, Restated.rebasedDeadlineRoundW M S tGAT gap + 3 ≤ c₁ ∧
      c₁ + S.cfg.timeoutDelay / S.hc.R ≤ c₂ ∧
      c₂ ≤ c₁ + S.cfg.timeoutDelay / S.hc.R + gap ∧ c₂ + 1 ≤ Restated.switchRound M S tE ∧
      ∀ c : Round, (c = c₁ ∨ c = c₂) →
        (∀ k < 3, S.E.proposer ((M.opening_slot S.hc c) + k) ∈
          notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c) + k))) ∧
        S.E.proposer ((M.opening_slot S.hc (c - 1))) ∈
          notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc (c - 1)))) ∧
        S.E.proposer ((M.opening_slot S.hc (c - 2))) ∈
          notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc (c - 2)))) := by
  have hΔ := S.E.Δ_pos
  have hR3 : 3 ≤ S.hc.R := S.hc.R_ge_three
  have hRpos : 0 < S.hc.R := lt_of_lt_of_le (by decide) hR3
  have hm : 2 ≤ S.cfg.timeoutDelay / S.hc.R :=
    (Nat.le_div_iff_mul_le hRpos).mpr (by simpa only [Nat.mul_comm] using S.timeout_rounds.2)
  have hη : Restated.cutBoundW M S tGAT gap + gap ≤ Restated.switchRound M S tE :=
    Restated.hη_of_healingLengthη' facts S tGAT tE gap hgst hlen
  have hs : Restated.deadlineRoundW M S tGAT gap + 2 * (7 * gap + 22 + 4 * S.extraRounds) + 2
      = Restated.cutBoundW M S tGAT gap := by
    have h := progressLag_alwaysAwake_eq_l72 S gap
    unfold Restated.deadlineRoundW Restated.cutBoundW
    rw [show Proofs.HealingSurface.progressLag' gap S.extraRounds
      = 7 * gap + 22 + 4 * S.extraRounds from h]
    exact deadline_slack_nat_l72 _ _ _ _
  obtain ⟨hrDW, hr₁, hr₁g⟩ := windows_pre_nat_l85d (Restated.deadlineRoundW M S tGAT gap)
    (7 * gap + 22 + 4 * S.extraRounds) (Restated.cutBoundW M S tGAT gap) gap (Restated.switchRound M S tE)
    S.extraRounds hs hη rfl
  obtain ⟨hlo0, -⟩ := Restated.window_in_phase_atRound facts S tGAT tE gap hgst hlen le_rfl hrDW
  obtain ⟨-, hWE⟩ := Restated.switchRound_window_in_phase facts S tGAT tE gap hgst hlen
  have hwa : wAttest S = 4 * (S.hc.R : Int) * S.E.Δ := rfl
  have hper1 : (Restated.Vocabulary.Execution.Setup.a M S 1) - (Restated.Vocabulary.Execution.Setup.a M S 0) = 4 * S.E.Δ * (S.hc.R : Int) := by
    rw [Restated.action_eq_l85d facts, Restated.action_eq_l85d facts]; push_cast; ring
  have hwin_of : ∀ r : Round, Restated.deadlineRoundW M S tGAT gap ≤ r → r + gap ≤ Restated.switchRound M S tE →
      tGAT ≤ M.proposal_time S.E ((M.opening_slot S.hc r)) ∧
      M.proposal_time S.E ((M.opening_slot S.hc r)) + (gap : Int) * ((Restated.Vocabulary.Execution.Setup.a M S 1) - (Restated.Vocabulary.Execution.Setup.a M S 0)) ≤ tE := by
    intro r hr hrg
    rw [Restated.proposal_time_opening_eq_l85d facts, hper1]
    rw [Restated.action_eq_l85d facts, hwa] at hlo0
    rw [Restated.action_eq_l85d facts] at hWE
    have hr' : ((Restated.deadlineRoundW M S tGAT gap : Nat) : Int) ≤ (r : Int) := by exact_mod_cast hr
    have hrg' : (r : Int) + (gap : Int) ≤ ((Restated.switchRound M S tE : Nat) : Int) := by
      exact_mod_cast hrg
    have hR3' : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast hR3
    have hP : (0 : Int) ≤ 4 * S.E.Δ * (S.hc.R : Int) := by positivity
    constructor
    · nlinarith
    · nlinarith
  obtain ⟨hst₁, hwi₁⟩ := hwin_of _ hr₁ hr₁g
  obtain ⟨c₁, hc₁lo, hc₁hi, hw₁, hw₁p, hw₁pp⟩ :=
    Restated.strongWindow_of_recurrence_l85d facts S Sched hrec hst₁ hwi₁
  obtain ⟨hr₂, hr₂g⟩ := windows_mid_nat_l85d (Restated.deadlineRoundW M S tGAT gap)
    (7 * gap + 22 + 4 * S.extraRounds) (Restated.cutBoundW M S tGAT gap) gap (Restated.switchRound M S tE)
    S.extraRounds (S.cfg.timeoutDelay / S.hc.R) c₁ hs hη rfl rfl hm hc₁lo hc₁hi
  obtain ⟨hst₂, hwi₂⟩ := hwin_of _ hr₂ hr₂g
  obtain ⟨c₂, hc₂lo, hc₂hi, hw₂, hw₂p, hw₂pp⟩ :=
    Restated.strongWindow_of_recurrence_l85d facts S Sched hrec hst₂ hwi₂
  obtain ⟨h1, h2, h3, h4⟩ := windows_all_nat_l85d (Restated.deadlineRoundW M S tGAT gap)
    (7 * gap + 22 + 4 * S.extraRounds) (Restated.cutBoundW M S tGAT gap) gap (Restated.switchRound M S tE)
    S.extraRounds (S.cfg.timeoutDelay / S.hc.R) c₁ c₂ hs hη rfl rfl hm hc₁lo hc₁hi hc₂lo hc₂hi
  refine ⟨c₁, c₂, h1, h2, h3, h4, ?_⟩
  rintro c (rfl | rfl)
  · exact ⟨hw₁, hw₁p, hw₁pp⟩
  · exact ⟨hw₂, hw₂p, hw₂pp⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog

/-- If `q` is at least two rounds after `deadlineRoundW S tGAT gap`, then `0 < o_q` and
    `tGAT + 1 ≤ proposal_time o_q`. -/
theorem openingBounds_afterDeadline_l85d (facts : Record.Facts M) (S : Setup V) {tGAT : Int} {gap : Nat} {q : Round}
    (hq : Restated.deadlineRoundW M S tGAT gap + 2 ≤ q) :
    0 < (M.opening_slot S.hc q) ∧
      tGAT + 1 ≤ M.proposal_time S.E ((M.opening_slot S.hc q)) := by
  obtain ⟨-, hdeadlineTwo, -, hdPos, hdSucc, -⟩ := facts.gr.openingSlots_l86f S hq
  refine ⟨by rw [← hdSucc]; exact Nat.succ_pos _, ?_⟩
  have hbase : Restated.roundAt M S tGAT + S.hc.η_SG ≤ Restated.deadlineRoundW M S tGAT gap := by
    unfold Restated.deadlineRoundW
    exact (Nat.le_succ _).trans (Nat.le_add_right _ _)
  exact (Restated.roundAt_lo_le_rGST_l71 facts S tGAT).trans
    (((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone hbase).trans
      ((Restated.Vocabulary.Protocol.action_lt_proposal_time_two_after facts S _).le.trans (facts.sch.proposal_time_mono S.E hdeadlineTwo)))

/-- `roundAt S tGAT + η_SG < deadlineRoundW S tGAT gap`. -/
private theorem rGST_lt_deadline₈₅dw (S : Setup V) (tGAT : Int) (gap : Nat) :
    Restated.roundAt M S tGAT + S.hc.η_SG < Restated.deadlineRoundW M S tGAT gap := by
  unfold Restated.deadlineRoundW
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_add_right _ _)

/-- If `roundAt S tGAT + η_SG < k`, then `tGAT + 1` is at most one delay before round `k`'s grade-2
    window start and one delay before its grade-1 window start. -/
private theorem lo_le_windows₈₅dw (facts : Record.Facts M) (S : Setup V) {tGAT : Int} {k : Round}
    (h : Restated.roundAt M S tGAT + S.hc.η_SG < k) :
    tGAT + 1 ≤ M.early S.E S.hc k .g2 - S.E.Δ ∧ tGAT + 1 ≤ M.early S.E S.hc k .g1 - S.E.Δ := by
  have h0 := Restated.lo_le_early_g2_sub_delta_of_action_lt facts S
    (Restated.roundAt_lo_le_rGST_l71 facts S tGAT) h
  have h1 := facts.gr.early_g2_add_delta_le_early_g1 S k
  have hΔ := S.E.Δ_pos
  exact ⟨h0, by linarith⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog

/-- In the run of the execution `x` up to step `n`, along its path `W`: if `T_D'` is an anchor at
    the re-based deadline round `rD'`, `rD' + 1 ≤ q`, `S.a q ≤ x[n].time ≤ tE`, and the proposer of
    `o_q` is not held at `o_q`'s confirmation instant and `P` is a proposal of its read on `W`, then
    `h(T_D') ≤ h(P)`. -/
theorem openingProposal_height_ge_rebasedAnchor_l85d (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v₀ : V) (n : Nat)
    {tGAT tE : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hn : (x[n].time : Int) ≤ tE)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    {T_D' : NamedBlock V}
    (hA' : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.rebasedDeadlineRoundW M S tGAT gap) T_D')
    {q : Round} (hq : Restated.rebasedDeadlineRoundW M S tGAT gap + 1 ≤ q)
    (hqhor : (Restated.Vocabulary.Execution.Setup.a M S q) ≤ (x[n].time : Int))
    (hopening : S.E.proposer ((M.opening_slot S.hc q)) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc q))))
    {P : NamedBlock V} :
    let R : Record.Run V :=
      { Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) }
    let W := Restated.runAllPath M S Sched x v₀ n
    let wp := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc q)))
      (S.E.proposer (M.opening_slot S.hc q))
    ∀ cp : M.Cache,
      M.onPhaseTick S.E S.hc wp.st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc q)) wp.cache ⇢ cp →
      let pn := M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E (M.opening_slot S.hc q)))
        wp.record cp
      M.proposal_with (M.gradeContract cp) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc q))) pn.st ⇢ some P →
    (M.derive_named S.E S.cfg T_D').h ≤ (M.derive_named S.E S.cfg P).h := by
  intro R W wp cp hcp pn hP
  have hA'c := hA'
  obtain ⟨-, -, n₀, -, -, -, -, -, -, -, -, hn₀, -⟩ := hA'
  have hrD'q : Restated.rebasedDeadlineRoundW M S tGAT gap ≤ q := (Nat.le_succ _).trans hq
  have hrDq : Restated.deadlineRoundW M S tGAT gap + 2 ≤ q := by
    refine le_trans ?_ hq
    show Restated.deadlineRoundW M S tGAT gap + 2 ≤ Restated.deadlineRoundW M S tGAT gap + gap + 1 + 1
    exact Nat.add_le_add_right (Nat.succ_le_succ (Nat.le_add_right _ _)) 1
  have hSa : (Restated.Vocabulary.Execution.Setup.a M S (Restated.rebasedDeadlineRoundW M S tGAT gap)) ≤ (x[n].time : Int) :=
    ((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone hrD'q).trans hqhor
  obtain ⟨blocked, first, i, a, ta, Cfg, T, Tprev, c0, hreg, hround, -, htop, -⟩ :=
    Restated.switchRoundRegime_runAll_notHeld_atRound facts S Sched x v₀ hsync hmono hawake hgst
      hcv hvalid hawm hthird hcom hrec (Restated.deadlineRoundW_le_rebased facts S tGAT gap) hn₀ hSa
      hn
  have hheight := Restated.anchorAtRound_height facts S Sched x hsync hmono hawake hgst hcv hvalid
    hawm hthird hA'c hn₀
  have hf := Restated.admissibleFieldsOn_runAll_notHeld facts S Sched x v₀ n hsync hmono hawake
    hgst hcv hvalid hawm hthird hn
  have hHs : ∀ t t' : Int, t ≤ t' → notHeldAt Sched t' ⊆ notHeldAt Sched t :=
    fun _ _ h => notHeldAt_anti hmono h
  have hHsXb : ∀ t : Int, notHeldAt Sched t ⊆ (Finset.univ : Finset V) :=
    fun _ => Finset.subset_univ _
  have hX : ∀ t : Int, 0 ≤ t → notHeldAt Sched t ⊆ (Finset.univ : Finset V) :=
    fun _ _ => Finset.subset_univ _
  have hXXb : (Finset.univ : Finset V) ⊆ Finset.univ := Finset.Subset.refl _
  have hcomOn := Restated.honestCommitteesOn_notHeld facts S Sched hcom
  have hbelow := Restated.belowOneThirdOn_runAll_notHeld facts S Sched x v₀ n hthird hn
  obtain ⟨-, -, hloOpen, -⟩ := Restated.roundAt_bounds_l71 facts S hgst
  have hlo := hreg.lo_le_opening_l71 facts hf hloOpen
  have hdlo : (M.opening_slot S.hc a.round) + 1 ≤ (M.opening_slot S.hc q) :=
    (facts.gr.opening_slot_succ_le_l78 S a.round).trans
      (facts.gr.opening_slot_mono S ((Nat.succ_le_succ hround).trans hq))
  have hconfA : M.confirmation_time S.E ((M.opening_slot S.hc q)) = (Restated.Vocabulary.Execution.Setup.a M S q) :=
    Restated.Vocabulary.Proofs.HealingSurface.opening_confirmation_time_eq_action facts S q
  have hhor : M.vote_time S.E ((M.opening_slot S.hc q)) + S.E.Δ ≤
      ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } :
        Record.Run V).horizon := by
    show _ ≤ (x[n].time : Int)
    refine (Restated.vote_time_add_delta_le_confirmation_l78 facts S le_rfl).trans ?_
    rw [hconfA]
    exact hqhor
  have hheads := hreg.heads_from_firstInterior facts hf hHs hHsXb hX hXXb hcomOn hbelow hdlo
    hhor hlo (fun k hk u _ j hj => Restated.awake_g2_action_runAllPath facts S Sched x v₀ n hmono
      hawake hn k hk u j hj)
  have hadopt := (Restated.openingAdoption_at_strongWindow_afterDeadline facts S Sched x v₀ n
    hsync hmono hawake hgst hcv hvalid hawm hthird hn hcom hrec hrDq hqhor hopening cp hcp
    hP).1
  have hw : S.E.proposer ((M.opening_slot S.hc q)) ∈
      notHeldAt Sched (M.vote_time S.E ((M.opening_slot S.hc q))) :=
    hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E _) hopening
  have hTP : Block.Preceq T.erase P.erase := by
    obtain ⟨H, cw, hcw, Tr, hTr, L, hL, L', hL', hH⟩ :=
      (p86g% exists_headOutcome₈₆g) facts (Setup.alwaysAwake S)
        (W (strictEventIndex R (M.vote_time S.E (M.opening_slot S.hc q)))
          (S.E.proposer (M.opening_slot S.hc q)))
        (M.vote_time S.E (M.opening_slot S.hc q))
    have h := hheads _ hw cw hcw Tr hTr L hL L' hL' H hH
    rwa [hadopt _ hw cw hcw Tr hTr L hL L' hL' H hH] at h
  obtain ⟨hTrun, -⟩ := hreg.checkpoint_runBlock facts hf hHsXb
  obtain ⟨hpos, hgat⟩ := Restated.openingBounds_afterDeadline_l85d facts S hrDq
  have hpropHor : M.proposal_time S.E ((M.opening_slot S.hc q)) ≤
      ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } :
        Record.Run V).horizon := by
    show _ ≤ (x[n].time : Int)
    refine (facts.sch.proposal_time_le_confirmation_time S.E _).trans ?_
    rw [hconfA]
    exact hqhor
  have hPclock : M.proposal_with (M.gradeContract cp)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc
      ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc q)))
      (M.ns_setClock S.E wp.st (M.proposal_time S.E (M.opening_slot S.hc q))) ⇢ some P := by
    have h := hP
    rewrite [show pn.st = M.store_with_cache
        (M.ns_setClock S.E wp.st (M.proposal_time S.E (M.opening_slot S.hc q))) cp from
      facts.nd.mkNode_st _ _ _, facts.dt.proposal_with_store_with_cache] at h
    exact h
  have hwinQ : tGAT + 1 ≤ M.early S.E S.hc (M.round_of S.hc (M.opening_slot S.hc q)) .g1 - S.E.Δ := by
    rw [facts.gr.round_of_opening_slot_eq S.hc]
    exact (lo_le_windows₈₅dw facts S (lt_of_lt_of_le (rGST_lt_deadline₈₅dw S tGAT gap)
      ((Nat.le_add_right _ 2).trans hrDq))).2
  have hPrun := Restated.proposedBlock_runBlockOn facts (Setup.alwaysAwake S) (notHeldAt Sched)
    Finset.univ hf hHs hHsXb hpos hopening hpropHor hgat (fun j hj => hf.tick_outcome j _ _ hj)
    (fun j hj => hf.awake_g1 _ _ j _ (Or.inl rfl) hj
      (hHs _ _ (facts.sch.proposal_time_le_confirmation_time S.E _) hopening) hwinQ)
    cp hcp hPclock
  have hTPn : NamedBlock.Preceq T P :=
    Restated.namedPreceq_of_runBlock_erase_preceqOn facts (notHeldAt Sched) Finset.univ hf hTrun hPrun hTP
  rw [hheight]
  exact htop.trans (facts.cs.derive_height_mono S.E S.cfg hTPn)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation

/-- The instants of the slots `o_c + 1` and `o_c + 2` against `S.a c` and `S.a (c + 1)`:
    `S.a c ≤ proposal_time (o_c + 2)`, `vote_time (o_c + 2) ≤ S.a (c + 1)`,
    `proposal_time (o_c + 2) ≤ confirmation_time (o_c + 1)`,
    `support_cutoff (o_c + 1) ≤ proposal_time (o_c + 2)`, `S.a c + Δ ≤ proposal_time (o_c + 2)`, and
    `proposal_time (o_c + 2) ≤ vote_time (o_c + 2)`. -/
theorem interiorInstants_l85d (facts : Record.Facts M) (S : Setup V) (c : Round) :
    (Restated.Vocabulary.Execution.Setup.a M S c) ≤ M.proposal_time S.E ((M.opening_slot S.hc c) + 2) ∧
    M.vote_time S.E ((M.opening_slot S.hc c) + 2) ≤ (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) ∧
    M.proposal_time S.E ((M.opening_slot S.hc c) + 2) ≤
      M.confirmation_time S.E ((M.opening_slot S.hc c) + 1) ∧
    M.support_cutoff S.E ((M.opening_slot S.hc c) + 1) ≤
      M.proposal_time S.E ((M.opening_slot S.hc c) + 2) ∧
    (Restated.Vocabulary.Execution.Setup.a M S c) + S.E.Δ ≤ M.proposal_time S.E ((M.opening_slot S.hc c) + 2) ∧
    M.proposal_time S.E ((M.opening_slot S.hc c) + 2) ≤
      M.vote_time S.E ((M.opening_slot S.hc c) + 2) := by
  have hΔ := S.E.Δ_pos
  have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  obtain ⟨-, -, -, hp1, -, hc0⟩ := facts.sch.slot_instants_l55 S.E (M.opening_slot S.hc c)
  obtain ⟨-, hs1, -, hp2, -, hc1⟩ := facts.sch.slot_instants_l55 S.E (M.opening_slot S.hc c + 1)
  obtain ⟨hv2, -, -, -, -, -⟩ := facts.sch.slot_instants_l55 S.E (M.opening_slot S.hc c + 2)
  have hp2' : M.proposal_time S.E (M.opening_slot S.hc c + 2)
      = M.proposal_time S.E (M.opening_slot S.hc c + 1) + 4 * S.E.Δ := hp2
  have ha : Restated.Vocabulary.Execution.Setup.a M S c
      = M.confirmation_time S.E (M.opening_slot S.hc c) :=
    facts.sch.a_eq_confirmation_time S.hc S.E c
  have ha1 := facts.gr.action_succ_eq_add_rounds S c
  have hRΔ : 12 * S.E.Δ ≤ 4 * (S.hc.R : Int) * S.E.Δ := by nlinarith
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog

/-- In the run of the execution `x` up to step `m + 1`, along its path `W`: if `c` is at least two
    rounds after the deadline round, step `m` is the tick at a time `t` with
    `vote_time (o_c + 2) ≤ t ≤ tE`, the proposers of `o_c` and `o_c + 2` are not held at their
    confirmation instants, `P` and `P₂` are proposals of their reads on `W` with `P ⪯ P₂`, and `w`
    is not held at `t`, then `P₂` is among `w`'s bodies after `m` steps and `h_j(P₂)` is at most
    `w`'s justified height there. -/
theorem windowProposal_held_atTick_l85d (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v₀ : V)
    {tGAT tE : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    {c : Round} (hc : Restated.deadlineRoundW M S tGAT gap + 2 ≤ c)
    {m : Nat} {t : Int} (hm : Restated.tickStepAt M x m t)
    (hvt : M.vote_time S.E ((M.opening_slot S.hc c) + 2) ≤ t) (htE : t ≤ tE)
    (hopening : S.E.proposer ((M.opening_slot S.hc c)) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c))))
    (hprop2 : S.E.proposer ((M.opening_slot S.hc c) + 2) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c) + 2)))
    {P P₂ : NamedBlock V}
    (hPP₂ : NamedBlock.Preceq P P₂)
    {w : V} (hw : w ∈ notHeldAt Sched t) :
    let R : Record.Run V :=
      { Restated.runAll M S Sched x v₀ (m + 1) with
          honest := notHeldAt Sched (x[m + 1].time : Int) }
    let W := Restated.runAllPath M S Sched x v₀ (m + 1)
    let wp := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c)))
      (S.E.proposer (M.opening_slot S.hc c))
    ∀ cp : M.Cache,
      M.onPhaseTick S.E S.hc wp.st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc c)) wp.cache ⇢ cp →
      let pn := M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E (M.opening_slot S.hc c)))
        wp.record cp
      M.proposal_with (M.gradeContract cp) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc c))) pn.st ⇢ some P →
    let wp₂ := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c + 2)))
      (S.E.proposer (M.opening_slot S.hc c + 2))
    ∀ cp₂ : M.Cache,
      M.onPhaseTick S.E S.hc wp₂.st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc c + 2)) wp₂.cache ⇢ cp₂ →
      let pn₂ := M.mkNode
        (M.ns_setClock S.E wp₂.st (M.proposal_time S.E (M.opening_slot S.hc c + 2))) wp₂.record cp₂
      M.proposal_with (M.gradeContract cp₂) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc c + 2))) pn₂.st ⇢ some P₂ →
    P₂ ∈ (x[m][w].st).st.bodies ∧
      (M.derive_named S.E S.cfg P₂).h_j ≤ (x[m][w].st).st.core.h_j := by
  intro R W wp cp hcp pn hP wp₂ cp₂ hcp₂ pn₂ hP₂
  obtain ⟨htime, -⟩ := Restated.tickStepAt_time facts x hm
  have hn : (x[m + 1].time : Int) ≤ tE := by rw [htime]; exact htE
  obtain ⟨hAc, hvoteNext, -, -, -, hpv⟩ := Restated.interiorInstants_l85d facts S c
  have hvoteHor : M.vote_time S.E ((M.opening_slot S.hc c) + 2) ≤ (x[m + 1].time : Int) := by
    rw [htime]; exact hvt
  have hAcHor : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c) ≤ (x[m + 1].time : Int) :=
    hAc.trans (hpv.trans hvoteHor)
  have hf := Restated.admissibleFieldsOn_runAll_notHeld facts S Sched x v₀ (m + 1) hsync hmono
    hawake hgst hcv hvalid hawm hthird hn
  have hHs : ∀ t t' : Int, t ≤ t' → notHeldAt Sched t' ⊆ notHeldAt Sched t :=
    fun _ _ h => notHeldAt_anti hmono h
  have hHsXb : ∀ t : Int, notHeldAt Sched t ⊆ (Finset.univ : Finset V) :=
    fun _ => Finset.subset_univ _
  have hcomOn := Restated.honestCommitteesOn_notHeld facts S Sched hcom
  have hbelow := Restated.belowOneThirdOn_runAll_notHeld facts S Sched x v₀ (m + 1) hthird hn
  have hrecOn := Restated.multiProposerRecurrenceOn_runAll_notHeld facts S Sched x v₀ (m + 1) hrec hn
  obtain ⟨hpost, -, hloOpen, ht₀⟩ := Restated.roundAt_bounds_l71 facts S hgst
  have hheads := (Restated.openingAdoption_at_strongWindow_afterDeadline facts S Sched x v₀
    (m + 1) hsync hmono hawake hgst hcv hvalid hawm hthird hn hcom hrec hc hAcHor hopening cp
    hcp hP).1
  have hsource := Restated.fgSource_eq_openingProposal_of_some_runAll_notHeld facts S Sched x v₀
    (m + 1) hsync hmono hawake hgst hcv hvalid hawm hthird hn hcom hrec hc hAcHor hopening cp
    hcp hP
  have hrootAt : ∀ u ∈ notHeldAt Sched (M.vote_time S.E ((M.opening_slot S.hc c) + 2)),
      Block.Preceq
        (M.get_fg_root (M.toHealing
          (W (strictEventIndex R (M.vote_time S.E ((M.opening_slot S.hc c) + 2))) u).st.core).toFG)
        P.erase :=
    fun u hu => Restated.fgRoot_preceq_openingProposal_at_read_afterDeadlineOn facts
      (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ hf hHs hHsXb hcomOn hbelow hrecOn
      (Setup.timeoutDelayBound _) hpost
      (by rw [Restated.fgSafetyProgressDeadline_eq_deadlineRoundW facts]; exact hc) hheads hsource
      (hAc.trans hpv) hvoteNext hvoteHor hu (Restated.roundAt_lo_le_rGST_l71 facts S tGAT) hloOpen ht₀
      (fun k hk u _ j hj => Restated.awake_g2_action_runAllPath facts S Sched x v₀ (m + 1) hmono
        hawake hn k hk u j hj)
  have hPP₂e : Block.Preceq P.erase P₂.erase :=
    Proofs.NamedWire.erase_preceq hPP₂
  obtain ⟨hpos2, hgat2⟩ : 0 < (M.opening_slot S.hc c) + 2 ∧
      tGAT + 1 ≤ M.proposal_time S.E ((M.opening_slot S.hc c) + 2) := by
    obtain ⟨-, hg⟩ := Restated.openingBounds_afterDeadline_l85d facts S hc
    exact ⟨Nat.succ_pos _, hg.trans (facts.sch.proposal_time_mono S.E (Nat.le_add_right _ 2))⟩
  have hP₂clock : M.proposal_with (M.gradeContract cp₂)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc
      ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc c + 2)))
      (M.ns_setClock S.E wp₂.st (M.proposal_time S.E (M.opening_slot S.hc c + 2))) ⇢ some P₂ := by
    have h := hP₂
    rewrite [show pn₂.st = M.store_with_cache
        (M.ns_setClock S.E wp₂.st (M.proposal_time S.E (M.opening_slot S.hc c + 2))) cp₂
      from facts.nd.mkNode_st _ _ _, facts.dt.proposal_with_store_with_cache] at h
    exact h
  have hrun₂ : ∀ j : Nat, R.events[j]? = some (Record.Event.tick
        (S.E.proposer (M.opening_slot S.hc c + 2)) (M.proposal_time S.E (M.opening_slot S.hc c + 2))) →
      M.awake_for_grade1 (Setup.alwaysAwake S) (S.E.proposer (M.opening_slot S.hc c + 2))
        (W j (S.E.proposer (M.opening_slot S.hc c + 2))) (M.round_of S.hc (M.opening_slot S.hc c + 2)) := by
    intro j hj
    have hwin : tGAT + 1 ≤ M.early S.E S.hc (M.round_of S.hc (M.opening_slot S.hc c + 2)) .g1 -
        S.E.Δ := by
      rw [facts.gr.round_of_opening_slot_add S.hc c
        (Nat.lt_of_lt_of_le (by decide : 2 < 3) S.hc.R_ge_three)]
      exact (lo_le_windows₈₅dw facts S (lt_of_lt_of_le (rGST_lt_deadline₈₅dw S tGAT gap)
        ((Nat.le_add_right _ 2).trans hc))).2
    exact hf.awake_g1 _ _ j _ (Or.inl rfl) hj
      (hHs _ _ (facts.sch.proposal_time_le_confirmation_time S.E _) hprop2) hwin
  have hadmit := Restated.proposedBlock_admittedBefore_vote_after_gstOn facts (Setup.alwaysAwake S)
    (notHeldAt Sched) Finset.univ hf hHs hHsXb hpos2 hprop2 hgat2 hvoteHor cp₂ hcp₂ hP₂clock
    (by
      intro u hu i hi
      exact Restated.Vocabulary.Proofs.finalized_preceq_at_prefix_of_storeBeforeRoot_preceq facts
        (Setup.alwaysAwake S) R hf.sorted (w := u) hi (W i) (hf.onePath i).1 _
        ((p55% onePath_slice₅₅b) W hf.onePath hi)
        (preceq_trans_Preceq (hrootAt u hu) hPP₂e))
    hrun₂
  have hwVote : w ∈ notHeldAt Sched (M.vote_time S.E ((M.opening_slot S.hc c) + 2)) :=
    hHs _ _ hvt hw
  have hmem := (Restated.admittedBefore_mem_and_stamp_atOn facts (Setup.alwaysAwake S) (notHeldAt Sched)
    Finset.univ hf (hadmit w hwVote) hvt).1
  have hP₂run := Restated.proposedBlock_runBlockOn facts (Setup.alwaysAwake S) (notHeldAt Sched)
    Finset.univ hf hHs hHsXb hpos2 hprop2 (hpv.trans hvoteHor) hgat2
    (fun j hj => hf.tick_outcome j _ _ hj) hrun₂ cp₂ hcp₂ hP₂clock
  have hbody := Restated.namedBody_of_mem_storeBeforeTime_l86f facts (Setup.alwaysAwake S) (notHeldAt Sched)
    Finset.univ hf (Finset.mem_univ w) hmem hP₂run
  have hstep := Restated.stateBeforeTime_runAll_tick facts S Sched x v₀ hm (le_refl (m + 1)) w
  have hbody' : P₂ ∈ (x[m][w].st).st.bodies := by
    rw [← hstep]; exact hbody
  refine ⟨hbody', ?_⟩
  have hnh := Restated.Vocabulary.Proofs.NamedJustificationBound.noHighJustifications_stateBeforeTime
    facts (Setup.alwaysAwake S) R t w _ ((p64b% mem_stateBeforeTime_along₆₄b) hf.sorted hf.onePath t)
  exact (hnh P₂ hbody).trans (le_of_eq (congrArg (fun z => z.st.core.h_j) hstep))

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas

/-- Under the bundle with path `W` and the weight bound: if `lo ≤ S.a q`, round `q + 1`'s earliest
    grade cutoff and the proposal instant of an interior slot `s` of round `q + 1` are in the
    horizon, every round-`q` action block along `W` of every member of the set for `S.a q` is an
    ancestor of `C`, the slot-`s` proposer is in the set for its proposal instant, `c` is an outcome
    of its cache update there, the FG root of the node state staged with `c` is an ancestor of `C`,
    every member of the set for `S.a q + Δ` is awake at `q`, and `lo ≤ domain (q + 1) g1`, then
    every round-`(q + 1)` anchor of that node state is an ancestor of `C`. -/
theorem interiorProposalAnchor_preceq_of_previousCarriersOn_l85d (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hfb : BelowOneThirdOn S rho Hs)
    {q : Round}
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S q))
    (hcut : Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (q + 1) ≤ rho.horizon)
    {s : Slot} (hslo : (M.opening_slot S.hc (q + 1)) + 1 ≤ s)
    (hshi : s < (M.opening_slot S.hc (q + 1 + 1)))
    (hproposalHor : M.proposal_time S.E s ≤ rho.horizon)
    {C : Block V}
    (hupper : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v) q,
      ∀ g, M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ g →
      ∀ B, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) g ⇢ B →
        Block.Preceq B C)
    (hprop : S.E.proposer s ∈ Hs (M.proposal_time S.E s))
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core.toHealing
      (M.proposal_time S.E s)
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).cache ⇢ c)
    (hroot : Block.Preceq
      (M.get_fg_root (M.toHealing (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
        (M.proposal_time S.E s))
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record c).st.core).toFG)
      C)
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S q)) → M.awake_for_grade2 S u (W j u) q)
    (hgat : lo ≤ M.domain S.E S.hc (q + 1) .g1) :
    ∀ A : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S
      (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
        (M.proposal_time S.E s))
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record c) (q + 1) ⇢ A →
      Block.Preceq A C := by
  intro A0 hA0
  have hW := hf.onePath
  have hround : M.round_of S.hc s = q + 1 :=
    facts.gr.round_of_eq_of_opening_succ_le_of_lt_next_opening S.hc hslo hshi
  have hopenLt : M.domain S.E S.hc (q + 1) .g1 < M.proposal_time S.E s := by
    rw [facts.gr.Sts_domain_g1_eq_opening, facts.gr.opening_eq_proposal_time]
    have hΔ := S.E.Δ_pos
    have h1 := (facts.sch.slot_instants_l55 S.E (M.opening_slot S.hc (q + 1))).2.2.2.1
    have h2 := facts.sch.proposal_time_mono S.E hslo
    linarith
  have hroundTime : M.round_of S.hc (S.E.slotOf (M.proposal_time S.E s)) = q + 1 := by
    rw [facts.sch.slotOf_proposal_time]
    exact hround
  have hdomainHor : M.domain S.E S.hc (q + 1) .g1 ≤ rho.horizon :=
    hopenLt.le.trans hproposalHor
  have hnextOpen : M.proposal_time S.E s ≤ M.opening S.E S.hc (q + 1 + 1) := by
    rw [facts.gr.opening_eq_proposal_time]
    exact facts.sch.proposal_time_mono S.E hshi.le
  set tp := M.proposal_time S.E s with htp
  set p := S.E.proposer s with hp
  set n := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho tp) p).st tp)
    (W (strictEventIndex rho tp) p).record c with hn
  have hnst : n.st = M.store_with_cache (M.ns_setClock S.E (W (strictEventIndex rho tp) p).st tp) _ := facts.nd.mkNode_st _ _ _
  have hncache : n.cache = c := facts.nd.mkNode_cache _ _ _
  have hcore : n.st = M.store_with_cache _ _ := facts.nd.mkNode_st _ _ _
  have hroundSt : M.round_of S.hc n.st.core.s = q + 1 := by
    rw [hcore]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    rw [facts.hd.Sts_setClock_core_s, htp, facts.sch.slotOf_proposal_time]
    exact hround
  have hnmem : n ∈ Restated.Vocabulary.Internal.NamedRecoveryRead.proposalDutyRead M S rho s :=
    ⟨W (strictEventIndex rho tp), (p56% mem_stateBeforeTime_along₅₆) hf.sorted hW tp, c, hc, rfl⟩
  have hA0' : Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n
      (M.round_of S.hc n.st.core.s) ⇢ A0 := by
    rw [hroundSt]
    exact hA0
  rcases Restated.Vocabulary.Proofs.HealingSurface.proposalAnchor_cases facts S rho s n hnmem A0 hA0'
    with hfg | ⟨root, A, hframe, hactive, hAA0⟩
  · rw [hfg]
    exact hroot
  rw [hAA0]
  rw [hroundSt] at hframe
  have hw : p ∈ Hs (M.domain S.E S.hc (q + 1) .g1) := hHs _ _ hopenLt.le hprop
  obtain ⟨fr, hfr⟩ := facts.gr.freezeRoot_nonempty S.E
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g1)) p).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g1)) p).st.core.F
    S.hc.η_SG (q + 1) (M.early S.E S.hc (q + 1) .g1) (M.late S.E S.hc (q + 1) .g1)
  have hbase := Restated.frame_phase_completed_in_roundOn facts S rho Hs Xb hf p (q + 1)
    (Nat.succ_pos q) .g1 hw tp hopenLt hnextOpen hdomainHor hgat
    (fun j hj => hf.tick_outcome j _ _ hj) fr hfr
  have hprepared := Restated.Vocabulary.Proofs.NamedOutageClosure.frame_phase_prepared_eq facts
    S rho p (q + 1) .g1 tp hroundTime _ (W (strictEventIndex rho tp))
    ((p56% mem_stateBeforeTime_along₅₆) hf.sorted hW tp) hbase c hc
  have hframeStore : (M.readFrame n.cache (M.toHealing n.st.core) (q + 1)).g1 =
      some (fr.map (fun X => M.clipGrade X (W (strictEventIndex rho tp) p).st.core.F)) := by
    rw [← facts.gr.phaseResult_g1, hncache, hnst]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    exact hprepared
  have hfs := hframe.symm.trans hframeStore
  rcases fr with _ | raw
  · cases hfs
  have hrootEq : root = M.clipGrade raw (W (strictEventIndex rho tp) p).st.core.F :=
    Option.some.inj (Option.some.inj hfs)
  have hLraw : Block.Preceq A raw := by
    have hLroot := facts.gr.preceq_of_activePrefix_eq_some hactive
    rw [hrootEq] at hLroot
    exact preceq_trans_Preceq hLroot (facts.gr.q10_clip_preceq raw _)
  have hrdmem := (p56% mem_stateBeforeTime_along₅₆) hf.sorted hW (M.domain S.E S.hc (q + 1) .g1)
  have hrawTree : raw ∈ (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g1)) p).st.core.T := by
    have h := facts.gr.mem_T_of_freezeRoot_eq_some (some raw) hfr rfl
    rw [facts.gr.Sts_gradeView_T] at h
    exact h
  have hAtree : A ∈ (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g1)) p).st.core.T := by
    have hpc := Restated.Vocabulary.Proofs.NamedStoreBridge.parentClosed_stateBeforeTime facts S rho
      (M.domain S.E S.hc (q + 1) .g1) p _ hrdmem
    unfold Restated.Vocabulary.Internal.ParentClosed Record.Model.GS.parent_closed at hpc
    rw [facts.sto.toHealing_T] at hpc
    exact Proofs.Records.mem_of_preceq hpc.2 A raw hrawTree (preceq_eq_true_iff_Preceq.mpr hLraw)
  obtain ⟨braw, hbraw⟩ := facts.gr.gradeBool_nonempty S.E
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g1)) p).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g1)) p).st.core.F
    S.hc.η_SG (q + 1) (M.early S.E S.hc (q + 1) .g1) (M.late S.E S.hc (q + 1) .g1) raw
  have hrawTrue := facts.gr.gradeBool_of_freezeRoot_eq_some (some raw) hfr rfl braw hbraw
  obtain ⟨gA, hgA⟩ := facts.gr.gradeBool_nonempty S.E
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g1)) p).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g1)) p).st.core.F
    S.hc.η_SG (q + 1) (M.early S.E S.hc (q + 1) .g1) (M.late S.E S.hc (q + 1) .g1) A
  have hgAtrue : gA = true :=
    facts.csAdded.confirmation_phaseGrade_mono S.E S.hc _ _ (q + 1) .g1 hLraw braw hbraw hrawTrue gA hgA
  have hFroot : Block.Preceq
      (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g1)) p).st.core.F
      (M.get_fg_root (M.toHealing n.st.core).toFG) := by
    have hFJ := Restated.Vocabulary.Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
      facts S rho tp p _ ((p56% mem_stateBeforeTime_along₅₆) hf.sorted hW tp)
    have h := facts.fc.preceq_get_fg_root_of_F (st := (M.toHealing n.st.core).toFG)
      (by
        rw [facts.sto.Sts_toHealing_F, facts.sto.Sts_toHealing_J, hcore]
        try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
        rw [facts.hd.setClock_core_F, facts.hd.setClock_core_J]
        exact preceq_eq_true_iff_Preceq.mpr hFJ)
    have hFn : n.st.core.F = (W (strictEventIndex rho tp) p).st.core.F := by
      rw [hcore]
      try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
      rw [facts.hd.setClock_core_F]
    rw [facts.sto.Sts_toHealing_F, hFn] at h
    exact preceq_trans_Preceq
      ((p56% F_mono_along₅₆) facts S hW p ((p56% strict_mono₅₆) rho hopenLt.le))
      (preceq_eq_true_iff_Preceq.mp h)
  have hFC : Block.Preceq
      (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g1)) p).st.core.F C :=
    preceq_trans_Preceq hFroot hroot
  have hlatest : q ∈ M.latest_window S.hc.η_SG (q + 1) := by
    simpa only [Nat.add_sub_cancel] using
      facts.fc.pred_mem_latest_window S.hc.η_SG (q + 1) S.hc.η_SG_ge_one (Nat.succ_pos q)
  have hactionDeadline : (Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ ≤
      M.early S.E S.hc (q + 1) .g1 :=
    (facts.gr.action_delta_le_early S S.hc.R_ge_three (Nat.lt_succ_self q)).trans
      (facts.gr.q10_early_g2_le_early_g1 S (q + 1))
  have hactionHor : (Restated.Vocabulary.Execution.Setup.a M S q) ≤ rho.horizon :=
    (le_add_of_nonneg_right S.E.Δ_pos.le).trans
      ((facts.gr.action_add_delta_le_next_Γ_neg1 S q).trans hcut)
  have hearlyHor : M.early S.E S.hc (q + 1) .g1 ≤ rho.horizon :=
    (facts.gr.q10_early_g1_le_domain_g2 S (q + 1)).trans
      (by rw [← facts.gr.gammaNeg1_eq_domain_g2_succ S q]; exact hcut)
  have hearlyDomain : M.early S.E S.hc (q + 1) .g1 ≤ M.domain S.E S.hc (q + 1) .g1 :=
    (facts.gr.q10_early_g1_le_domain_g2 S (q + 1)).trans
      (facts.gr.q10_domain_g2_lt_domain_g1 S (q + 1)).le
  have hwE : p ∈ Hs (M.early S.E S.hc (q + 1) .g1) := hHs _ _ hearlyDomain hw
  have hmemE : ∀ v ∈ Hs (M.domain S.E S.hc (q + 1) .g1), v ∈ Hs (M.early S.E S.hc (q + 1) .g1) :=
    fun v hv => hHs _ _ hearlyDomain hv
  have hmemAD : ∀ v ∈ Hs (M.domain S.E S.hc (q + 1) .g1),
      v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ) :=
    fun v hv => hHs _ _ (hactionDeadline.trans hearlyDomain) hv
  have hmemA : ∀ v ∈ Hs (M.domain S.E S.hc (q + 1) .g1),
      v ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S q) :=
    fun v hv => hHs _ _ (le_add_of_nonneg_right S.E.Δ_pos.le) (hmemAD v hv)
  have hvoteIn : ∀ v ∈ Hs (M.domain S.E S.hc (q + 1) .g1),
      ∃ (a : NamedAttestation V) (B : Block V) (Bn : NamedBlock V),
        a.val_index = v ∧ a.round = q ∧
        Restated.Vocabulary.Execution.NamedRun.emits M S rho W v (Object.attest a)
          (Restated.Vocabulary.Execution.Setup.a M S q) ∧
        a.confirmed = some B.root ∧ Bn.erase = B ∧ Restated.RunBlockOn M S rho W Xb Bn ∧
        Block.Preceq B C ∧
        ∀ Y, M.interpretedInputs
          (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g1)) p).st.core))
          (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g1)) p).st.core.F
          S.hc.η_SG (q + 1) (M.early S.E S.hc (q + 1) .g1) v ⇢ Y → M.sgVote a.erase ∈ Y := by
    intro v hv
    have hvA := hmemA v hv
    obtain ⟨nv, hnv, g, hg, B, hB⟩ := (p56% exists_actionSG₅₆) facts S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v) q
    obtain ⟨D, hD⟩ := facts.dt.attest_with_nonempty (M.gradeContract nv.cache) S.E S.hc (S.node v)
      nv.st nv.record
    have hem := Restated.honest_emits_actionAttestationAtOn facts S Hs Xb hf q hvA hactionHor hpost
      (hA v (hmemAD v hv)) (fun j hj => hf.tick_outcome j _ _ hj) nv hnv D hD
    have hsg := hem.2 g hg B hB
    have haval : D.2.2.val_index = v := by
      have h := congrArg Protocol.SGVote.val_index hsg
      rw [facts.sto.sgVote_val_index_eq_val_index, namedAttestation_erase_val_index] at h
      exact h
    have haround : D.2.2.round = q := by
      have h := congrArg Protocol.SGVote.round hsg
      rw [facts.sto.sgVote_round_eq_round, namedAttestation_erase_round] at h
      exact h
    have haconf : D.2.2.confirmed = some B.root := by
      have h := congrArg Protocol.SGVote.confirmed hsg
      rw [facts.sto.sgVote_confirmed_eq, namedAttestation_erase_confirmed] at h
      exact h
    obtain ⟨i, hi, -, -, -, -, hall⟩ :=
      Restated.Vocabulary.Proofs.NamedOutageInputs.emitted_attestation_head facts S rho W hW hem.1
    obtain ⟨ni, hni, -⟩ := (p56% exists_actionSG₅₆) facts S (W i v) D.2.2.round
    obtain ⟨H, hH, hHconf⟩ := hall ni hni
    have hHbody : H ∈ (W i v).st.bodies := by
      rw [← (p56% actionReadFrom_bodies₅₆) facts S _ _ ni hni]
      exact hH
    have hHrun : Restated.RunBlockOn M S rho W Xb H :=
      Restated.runBlock_of_stateBefore_memOn facts S W Xb (hHsXb _ hv) hHbody
    have hBmem : B ∈ (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v).st.core.T :=
      Restated.Vocabulary.Proofs.HealingSurface.actionSGBlockAt_mem_storeBeforeTime facts S rho v q _
        ((p56% mem_stateBeforeTime_along₅₆) hf.sorted hW _) nv hnv g hg B hB
    obtain ⟨Bn, hBnerase, hBnrun⟩ := Restated.runBlock_of_mem_core_T_stateBeforeTimeOn facts S Hs Xb
      hf (hHsXb _ hv) (Restated.Vocabulary.Execution.Setup.a M S q) hBmem
    have hrootEq : H.erase.root = Bn.erase.root := by
      rw [Proofs.NamedWire.erase_root, hBnerase]
      exact Option.some.inj (hHconf.symm.trans haconf)
    have hHB : H.erase = Bn.erase :=
      Restated.runBlock_eq_of_root_eqOn facts W Xb hf.rootCollisionFree hHrun hBnrun hrootEq
    have hBC : Block.Preceq B C := hupper v hvA nv hnv g hg B hB
    have hHC : Block.Preceq H.erase C := by
      rw [hHB, hBnerase]
      exact hBC
    have hmem := Restated.action_vote_mem_interpretedInputs_after_gst_common_upperOn facts
      S Hs Xb hf hHs hHsXb .g1 hlatest (hmemE v hv) hwE
      ⟨haval, haround, hem.1⟩ ⟨i, hi, ⟨ni, hni, hH⟩, hHconf⟩ hHC hFC
      (by rw [haround]; exact hpost)
      (by rw [haround, max_eq_left hpost]; exact hactionDeadline)
      hearlyDomain hearlyHor
    exact ⟨D.2.2, B, Bn, haval, haround, hem.1, haconf, hBnerase, hBnrun, hBC, hmem⟩
  have hwin : ∀ ins : V → Finset (Protocol.SGVote V),
      (∀ v, M.interpretedInputs
        (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g1)) p).st.core))
        (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g1)) p).st.core.F
        S.hc.η_SG (q + 1) (M.early S.E S.hc (q + 1) .g1) v ⇢ ins v) →
      S.E.electorate.weightOf (Finset.univ \ Hs (M.domain S.E S.hc (q + 1) .g1)) <
        S.E.electorate.weightOf ((Hs (M.domain S.E S.hc (q + 1) .g1)).filter
          fun v => (ins v).Nonempty) := by
    intro ins hins
    have hsubset : Hs (M.domain S.E S.hc (q + 1) .g1) ⊆
        (Hs (M.domain S.E S.hc (q + 1) .g1)).filter fun v => (ins v).Nonempty := by
      intro v hv
      obtain ⟨a, -, -, -, -, -, -, -, -, -, hmem⟩ := hvoteIn v hv
      exact Finset.mem_filter.2 ⟨hv, ⟨_, hmem _ (hins v)⟩⟩
    exact lt_of_lt_of_le
      (by simpa only [HonestWeightMajority] using
        honestWeightMajorityOn_of_belowOneThirdOn hfb _ hdomainHor)
      (S.E.electorate.weightOf_mono hsubset)
  obtain ⟨v, hv, I, hI, u, hu, head, hconf, hfind, -, hAhead, -, hmax⟩ :=
    facts.gr.exists_honest_max_positive_supporter_of_relativeGrade S.E S.hc hwin gA hgA hgAtrue
  obtain ⟨a, B, Bn, haval, haround, hemit, haconf, hBnerase, hBnrun, hBC, hmem⟩ := hvoteIn v hv
  have hqle : q ≤ u.round := by
    have h := hmax (M.sgVote a.erase) (hmem I hI)
    rw [facts.sto.sgVote_round_eq_round, namedAttestation_erase_round, haround] at h
    exact h
  obtain ⟨R, hR⟩ := facts.gr.rawInputs_nonempty
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g1)) p).st.core))
    S.hc.η_SG (q + 1) (M.early S.E S.hc (q + 1) .g1) v
  obtain ⟨bu, hbu⟩ := facts.gr.bodyReady_nonempty
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g1)) p).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g1)) p).st.core.F
    (M.early S.E S.hc (q + 1) .g1) u
  have huraw := ((facts.gr.mem_interpretedInputs_iff I hI R hR bu hbu).mp hu).1
  obtain ⟨b, -, hbround, hbproj, huwindow, -, hbemit⟩ :=
    Restated.rawInputs_traceOn facts S rho Hs Xb hf hHs (M.domain S.E S.hc (q + 1) .g1)
      (M.early S.E S.hc (q + 1) .g1) p S.hc.η_SG (q + 1) v hv R hR huraw
  have hule : u.round ≤ q := Nat.le_of_lt_succ (facts.fc.window_bounds huwindow).2
  have huroundEq : u.round = q := Nat.le_antisymm hule hqle
  have hba : b = a := Restated.emits_attest_uniqueOn facts S Hs Xb hf hbemit hemit
    ((hbround.trans huroundEq).trans haround.symm)
  have huEq : u = M.sgVote a.erase := by
    rw [← hbproj, hba]
  have hheadRoot : head.root = B.root := by
    have huconf := congrArg Protocol.SGVote.confirmed huEq
    rw [facts.sto.sgVote_confirmed_eq, namedAttestation_erase_confirmed, hconf, haconf] at huconf
    exact Option.some.inj huconf
  have hheadMem : head ∈ (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g1)) p).st.core.T := by
    have h := Proofs.HealingLemmas.find?_mem hfind
    rw [facts.gr.Sts_gradeView_T] at h
    exact h
  obtain ⟨Headn, hHeaderase, hHeadrun⟩ := Restated.runBlock_of_mem_core_T_stateBeforeTimeOn facts
    S Hs Xb hf (hHsXb _ hw) (M.domain S.E S.hc (q + 1) .g1) hheadMem
  have hheadBnRoot : Headn.erase.root = Bn.erase.root := by
    rw [hHeaderase, hBnerase]
    exact hheadRoot
  have hheadB : head = B := by
    rw [← hHeaderase, ← hBnerase]
    exact Restated.runBlock_eq_of_root_eqOn facts W Xb hf.rootCollisionFree hHeadrun hBnrun hheadBnRoot
  rw [hheadB] at hAhead
  exact preceq_trans_Preceq hAhead hBC

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog
open DecoupledConsensusModel.Internal.PhaseGrades

/-- In the run of the execution `x` up to step `n`, along its path `W`: if `c` is at least two
    rounds after the deadline round, `vote_time (o_c + 2) ≤ x[n].time ≤ tE`, the proposers of `o_c`
    and `o_c + 2` are not held at their confirmation instants, and `P` and `P₂` are proposals of
    their reads on `W`, then `P₂` is not genesis, `P ⪯ parent(P₂)`, `parent(P₂).slot + 1 ≤ o_c + 2`,
    and every non-genesis ancestor of `P₂` has its parent at a lower slot. -/
theorem windowParent_l85d (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v₀ : V) (n : Nat)
    {tGAT tE : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hn : (x[n].time : Int) ≤ tE)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    {c : Round} (hc : Restated.deadlineRoundW M S tGAT gap + 2 ≤ c)
    (hvoteHor : M.vote_time S.E ((M.opening_slot S.hc c) + 2) ≤ (x[n].time : Int))
    (hopening : S.E.proposer ((M.opening_slot S.hc c)) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c))))
    (hprop2 : S.E.proposer ((M.opening_slot S.hc c) + 2) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c) + 2)))
    {P P₂ : NamedBlock V} :
    let R : Record.Run V :=
      { Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) }
    let W := Restated.runAllPath M S Sched x v₀ n
    let wp := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c)))
      (S.E.proposer (M.opening_slot S.hc c))
    ∀ cp : M.Cache,
      M.onPhaseTick S.E S.hc wp.st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc c)) wp.cache ⇢ cp →
      let pn := M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E (M.opening_slot S.hc c)))
        wp.record cp
      M.proposal_with (M.gradeContract cp) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc c))) pn.st ⇢ some P →
    let wp₂ := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c + 2)))
      (S.E.proposer (M.opening_slot S.hc c + 2))
    ∀ cp₂ : M.Cache,
      M.onPhaseTick S.E S.hc wp₂.st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc c + 2)) wp₂.cache ⇢ cp₂ →
      let pn₂ := M.mkNode
        (M.ns_setClock S.E wp₂.st (M.proposal_time S.E (M.opening_slot S.hc c + 2))) wp₂.record cp₂
      M.proposal_with (M.gradeContract cp₂) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc c + 2))) pn₂.st ⇢ some P₂ →
    P₂ ≠ .genesis ∧ NamedBlock.Preceq P P₂.parent ∧
      P₂.parent.slot + 1 ≤ (M.opening_slot S.hc c) + 2 ∧
      ∀ X : NamedBlock V, NamedBlock.Preceq X P₂ → X ≠ .genesis → X.parent.slot < X.slot := by
  intro R W wp cp hcp pn hP wp₂ cp₂ hcp₂ pn₂ hP₂
  classical
  obtain ⟨q, rfl⟩ : ∃ q : Round, c = q + 1 :=
    Nat.exists_eq_succ_of_ne_zero (by
      intro h0; rw [h0] at hc; exact absurd hc (Nat.not_succ_le_zero _ ∘ fun h =>
        (Nat.le_add_left 1 _).trans ((Nat.le_succ _).trans h)))
  set o := (M.opening_slot S.hc (q + 1)) with ho
  obtain ⟨hAc, hvoteNext, hpconf, hsupp, hAcDelta, hpv⟩ :=
    Restated.interiorInstants_l85d facts S (q + 1)
  have hΔ := S.E.Δ_pos
  have hpropHor : M.proposal_time S.E (o + 2) ≤ R.horizon := hpv.trans hvoteHor
  obtain ⟨hv1, hs1, -, -, -, -⟩ := facts.sch.slot_instants_l55 S.E (o + 1)
  have hvs : M.vote_time S.E (o + 1) ≤ M.support_cutoff S.E (o + 1) := by linarith
  have hAcHor : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (q + 1)) ≤
      (x[n].time : Int) := hAc.trans hpropHor
  have hf := Restated.admissibleFieldsOn_runAll_notHeld facts S Sched x v₀ n hsync hmono hawake
    hgst hcv hvalid hawm hthird hn
  have hHs : ∀ t t' : Int, t ≤ t' → notHeldAt Sched t' ⊆ notHeldAt Sched t :=
    fun _ _ h => notHeldAt_anti hmono h
  have hHsXb : ∀ t : Int, notHeldAt Sched t ⊆ (Finset.univ : Finset V) :=
    fun _ => Finset.subset_univ _
  have hcomOn := Restated.honestCommitteesOn_notHeld facts S Sched hcom
  have hbelow := Restated.belowOneThirdOn_runAll_notHeld facts S Sched x v₀ n hthird hn
  have hrecOn := Restated.multiProposerRecurrenceOn_runAll_notHeld facts S Sched x v₀ n hrec hn
  obtain ⟨hpost, -, hloOpen, ht₀⟩ := Restated.roundAt_bounds_l71 facts S hgst
  have hloPost := Restated.roundAt_lo_le_rGST_l71 facts S tGAT
  have hA : ∀ k : Round, tGAT + 1 ≤ M.early S.E S.hc k .g2 - S.E.Δ →
      ∀ u ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat,
        R.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) →
        M.awake_for_grade2 (Setup.alwaysAwake S) u (W j u) k :=
    fun k hk u _ j hj => Restated.awake_g2_action_runAllPath facts S Sched x v₀ n hmono hawake hn
      k hk u j hj
  have hDq : Restated.deadlineRoundW M S tGAT gap ≤ q :=
    Nat.le_of_succ_le_succ ((Nat.le_succ _).trans hc)
  have hwinQ1 := lo_le_windows₈₅dw facts S
    (lt_of_lt_of_le (rGST_lt_deadline₈₅dw S tGAT gap) (hDq.trans (Nat.le_succ q)))
  have hD : Restated.fgSafetyProgressDeadline (Setup.alwaysAwake S) R
      (Restated.roundAt M S tGAT + S.hc.η_SG) gap (Setup.alwaysAwake S).extraRounds =
      Restated.deadlineRoundW M S tGAT gap :=
    Restated.fgSafetyProgressDeadline_eq_deadlineRoundW facts S R tGAT gap
  obtain ⟨hopos, hgatO⟩ := Restated.openingBounds_afterDeadline_l85d facts S hc
  have hconfA : M.confirmation_time S.E o = (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) :=
    Restated.Vocabulary.Proofs.HealingSurface.opening_confirmation_time_eq_action facts S (q + 1)
  have hp0 : S.E.proposer o ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M S (q + 1))) := by
    rw [← hconfA]; exact hopening
  have hpnst : pn.st = M.store_with_cache (M.ns_setClock S.E wp.st (M.proposal_time S.E o)) cp :=
    facts.nd.mkNode_st _ _ _
  have hpncache : pn.cache = cp := facts.nd.mkNode_cache _ _ _
  have hpread : pn ∈ Restated.Vocabulary.Statements.Instantiation.proposerReadAt M
      (Setup.alwaysAwake S) R o :=
    (p58% mkNode_mem_confirmationReadAt₅₈) hf.sorted hf.onePath _ _ cp hcp
  have hPn : M.proposal_with (M.gradeContract pn.cache) .poolAndCarried S.E S.hc
      ((Setup.alwaysAwake S).node (S.E.proposer o)) pn.st ⇢ some P := by
    rw [hpncache]
    exact hP
  have hPclock : M.proposal_with (M.gradeContract cp)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc
      ((Setup.alwaysAwake S).node (S.E.proposer o))
      (M.ns_setClock S.E wp.st (M.proposal_time S.E o)) ⇢ some P := by
    have h := hP
    rw [hpnst, facts.dt.proposal_with_store_with_cache] at h
    exact h
  have hpn₂st : pn₂.st = M.store_with_cache (M.ns_setClock S.E wp₂.st (M.proposal_time S.E (o + 2))) cp₂ :=
    facts.nd.mkNode_st _ _ _
  have hpn₂cache : pn₂.cache = cp₂ := facts.nd.mkNode_cache _ _ _
  have hp₂read : pn₂ ∈ Restated.Vocabulary.Statements.Instantiation.proposerReadAt M
      (Setup.alwaysAwake S) R (o + 2) :=
    (p58% mkNode_mem_confirmationReadAt₅₈) hf.sorted hf.onePath _ _ cp₂ hcp₂
  have hP₂n : M.proposal_with (M.gradeContract pn₂.cache) .poolAndCarried S.E S.hc
      ((Setup.alwaysAwake S).node (S.E.proposer (o + 2))) pn₂.st ⇢ some P₂ := by
    rw [hpn₂cache]
    exact hP₂
  have hP₂clock : M.proposal_with (M.gradeContract cp₂)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc
      ((Setup.alwaysAwake S).node (S.E.proposer (o + 2)))
      (M.ns_setClock S.E wp₂.st (M.proposal_time S.E (o + 2))) ⇢ some P₂ := by
    have h := hP₂
    rw [hpn₂st, facts.dt.proposal_with_store_with_cache] at h
    exact h
  have hsg := Restated.sgBlock_eq_openingProposal_runAll_notHeld facts S Sched x v₀ n hsync hmono
    hawake hgst hcv hvalid hawm hthird hn hcom hrec hc hAcHor hopening cp hcp hP
  obtain ⟨nv0, hnv0, g0, hg0, G0, hG0⟩ := (p56% exists_actionSG₅₆) facts (Setup.alwaysAwake S)
    (W (strictEventIndex R (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (q + 1)))
      (S.E.proposer o)) (q + 1)
  have hG0P : G0 = P.erase := hsg _ hp0 nv0 hnv0 g0 hg0 G0 hG0
  have hfirst := fun (w : V) (hw : w ∈ notHeldAt Sched (M.vote_time S.E (o + 1))) =>
    Restated.actionSGBlock_preceq_firstInteriorHead_after_GST_namedOn facts (Setup.alwaysAwake S)
      (notHeldAt Sched) Finset.univ hf hHs hHsXb hcomOn hbelow hrecOn
      (Setup.timeoutDelayBound _) hpost (by rw [hD]; exact hDq) hAcHor hp0
      (fun j hj => Restated.awake_g2_action_runAllPath facts S Sched x v₀ n hmono hawake hn
        (q + 1) hwinQ1.1 _ j hj) hw hloPost
      hloOpen ht₀ hA
  have hvote1Hor : M.vote_time S.E (o + 1) ≤ R.horizon :=
    (hvs.trans hsupp).trans hpropHor
  have hlo1 : tGAT + 1 ≤ M.vote_time S.E (o + 1) :=
    hgatO.trans ((facts.sch.proposal_time_mono S.E (Nat.le_succ o)).trans
      (facts.sch.proposal_time_lt_vote_time S.E (o + 1)).le)
  have hcone : Restated.NamedHonestVotesConeOn M (Setup.alwaysAwake S) R W (notHeldAt Sched)
      Finset.univ (o + 1) (fun X => Block.Preceq P.erase X) := by
    intro w hw hcomm
    obtain ⟨H, cw, hcw, Tr, hTr, L, hL, L', hL', hH⟩ :=
      (p86g% exists_headOutcome₈₆g) facts (Setup.alwaysAwake S)
        (W (strictEventIndex R (M.vote_time S.E (o + 1))) w) (M.vote_time S.E (o + 1))
    obtain ⟨X, hXerase, hXrun, hXemit⟩ := Restated.named_voter_head_emitsOn facts
      (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ hf hHsXb hw (Nat.succ_pos o) hcomm
      hvote1Hor hlo1 cw hcw
      (fun j hj => hf.awake_g1 _ _ j _ (Or.inr rfl) hj hw (by
        show tGAT + 1 ≤ M.early S.E S.hc (M.round_of S.hc (o + 1)) .g1 - S.E.Δ
        rw [ho, facts.gr.HealingLemmas_round_of_opening_succ S.hc]
        exact hwinQ1.2))
      Tr hTr L hL L' hL' H hH
    have hGH := hfirst w hw cw hcw Tr hTr L hL L' hL' H hH nv0 hnv0 g0 hg0 G0 hG0
    rw [hG0P] at hGH
    exact ⟨X, by rw [hXerase]; exact hGH, hXrun, hXemit⟩
  have huRead : S.E.proposer (o + 2) ∈ notHeldAt Sched (M.proposal_time S.E (o + 2)) :=
    hHs _ _ (facts.sch.proposal_time_le_confirmation_time S.E _) hprop2
  have huVote1 : S.E.proposer (o + 2) ∈ notHeldAt Sched (M.vote_time S.E (o + 1)) :=
    hHs _ _ (hvs.trans hsupp) huRead
  have hheads := (Restated.openingAdoption_at_strongWindow_afterDeadline facts S Sched x v₀ n
    hsync hmono hawake hgst hcv hvalid hawm hthird hn hcom hrec hc hAcHor hopening cp hcp
    hP).1
  have hsource := Restated.fgSource_eq_openingProposal_of_some_runAll_notHeld facts S Sched x v₀
    n hsync hmono hawake hgst hcv hvalid hawm hthird hn hcom hrec hc hAcHor hopening cp hcp hP
  have hroot : Block.Preceq
      (M.get_fg_root (M.toHealing
        (W (strictEventIndex R (M.proposal_time S.E (o + 2))) (S.E.proposer (o + 2))).st.core).toFG)
      P.erase :=
    Restated.fgRoot_preceq_openingProposal_at_read_afterDeadlineOn facts (Setup.alwaysAwake S)
      (notHeldAt Sched) Finset.univ hf hHs hHsXb hcomOn hbelow hrecOn
      (Setup.timeoutDelayBound _) hpost (by rw [hD]; exact hc) hheads hsource
      hAc (hpv.trans hvoteNext) hpropHor huRead hloPost hloOpen ht₀ hA
  have hPrun := Restated.proposedBlock_runBlockOn facts (Setup.alwaysAwake S) (notHeldAt Sched)
    Finset.univ hf hHs hHsXb hopos hopening
    ((facts.sch.proposal_time_le_confirmation_time S.E o).trans (by rw [hconfA]; exact hAcHor))
    hgatO (fun j hj => hf.tick_outcome j _ _ hj)
    (fun j hj => hf.awake_g1 _ _ j _ (Or.inl rfl) hj
      (hHs _ _ (facts.sch.proposal_time_le_confirmation_time S.E _) hopening) (by
        show tGAT + 1 ≤ M.early S.E S.hc (M.round_of S.hc o) .g1 - S.E.Δ
        rw [ho, facts.gr.round_of_opening_slot_eq S.hc]
        exact hwinQ1.2))
    cp hcp hPclock
  have hactiveStore : P.erase ∈ M.get_filtered_block_tree
      (M.toHealing
        (W (strictEventIndex R (M.proposal_time S.E (o + 2))) (S.E.proposer (o + 2))).st.core).toFG := by
    have hDread : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S))
        (Restated.fgSafetyProgressDeadline (Setup.alwaysAwake S) R
        (Restated.roundAt M S tGAT + S.hc.η_SG) gap (Setup.alwaysAwake S).extraRounds) ≤
        M.proposal_time S.E (o + 2) := by
      rw [hD]
      exact ((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone
        (hDq.trans (Nat.le_succ q))).trans hAc
    have hslotD : (M.opening_slot S.hc) (Restated.fgSafetyProgressDeadline
        (Setup.alwaysAwake S) R (Restated.roundAt M S tGAT + S.hc.η_SG) gap
        (Setup.alwaysAwake S).extraRounds) + 1 ≤ o + 1 := by
      rw [hD]
      exact Nat.succ_le_succ (facts.gr.opening_slot_mono S (hDq.trans (Nat.le_succ q)))
    have hshor1 : M.vote_time S.E (o + 1) + S.E.Δ ≤ R.horizon := by
      refine le_trans ?_ hpropHor
      linarith
    obtain ⟨T, hTrun, hTband, hTheads⟩ :=
      (p86f% exists_namedCommonPreviousHeadAncestor_in_frontierBand_after_GSTOn₈₆f) facts
        (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ hf hHs hHsXb hcomOn hbelow hrecOn
        (Setup.timeoutDelayBound _) hpost hDread hpropHor hslotD hpconf hshor1 huRead hloPost
        hloOpen ht₀ hA
    obtain ⟨H, cw, hcw, Tr, hTr, L, hL, L', hL', hH⟩ :=
      (p86g% exists_headOutcome₈₆g) facts (Setup.alwaysAwake S)
        (W (strictEventIndex R (M.vote_time S.E (o + 1))) (S.E.proposer (o + 2)))
        (M.vote_time S.E (o + 1))
    have hTH : Block.Preceq T.erase H :=
      hTheads _ huVote1 cw hcw Tr hTr L hL L' hL' H hH
    have hPH : Block.Preceq P.erase H := by
      have h := hfirst _ huVote1 cw hcw Tr hTr L hL L' hL' H hH nv0 hnv0 g0 hg0 G0 hG0
      rw [hG0P] at h
      exact h
    have hheadVote := Restated.voteDutyHead_mem_voteDutyStoreOn facts (Setup.alwaysAwake S)
      (notHeldAt Sched) Finset.univ hf (S.E.proposer (o + 2)) (o + 1) cw hcw Tr hTr L hL L' hL' H hH
    have hHvoteT : H ∈ (W (strictEventIndex R (M.vote_time S.E (o + 1)))
        (S.E.proposer (o + 2))).st.core.T := by
      have h := hheadVote
      rw [(p60% voteStore_eq₆₀s) facts, facts.hd.Sts_setClock_core_T] at h
      exact h
    have hheadRead : H ∈ (W (strictEventIndex R (M.proposal_time S.E (o + 2)))
        (S.E.proposer (o + 2))).st.core.T :=
      Restated.seedStore_T_subsetOn facts (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ hf
        (S.E.proposer (o + 2)) (hvs.trans hsupp) hHvoteT
    have hmemRead := (p64b% mem_stateBeforeTime_along₆₄b) hf.sorted hf.onePath
      (M.proposal_time S.E (o + 2))
    have hpc := Restated.Vocabulary.Proofs.NamedStoreBridge.parentClosed_stateBeforeTime facts
      (Setup.alwaysAwake S) R (M.proposal_time S.E (o + 2)) (S.E.proposer (o + 2)) _ hmemRead
    have hFJ := Restated.Vocabulary.Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
      facts (Setup.alwaysAwake S) R (M.proposal_time S.E (o + 2)) (S.E.proposer (o + 2)) _ hmemRead
    have hpcT := hpc
    unfold Restated.Vocabulary.Internal.ParentClosed Record.Model.GS.parent_closed at hpcT
    rw [facts.sto.toHealing_T] at hpcT
    have hmemOf : ∀ Y : Block V, Block.Preceq Y H →
        Y ∈ (W (strictEventIndex R (M.proposal_time S.E (o + 2)))
          (S.E.proposer (o + 2))).st.core.T :=
      fun Y hY => Proofs.Records.mem_of_preceq hpcT.2 Y H hheadRead
        (preceq_eq_true_iff_Preceq.mpr hY)
    have hbandOf : ∀ Y : NamedBlock V,
        Restated.RunBlockOn M (Setup.alwaysAwake S) R W Finset.univ Y →
        Block.Preceq Y.erase H →
        (M.derive_named S.E S.cfg T).h ≤ (M.derive_named S.E S.cfg Y).h →
        (W (strictEventIndex R (M.proposal_time S.E (o + 2)))
          (S.E.proposer (o + 2))).st.core.h_max - 1 ≤
          ((W (strictEventIndex R (M.proposal_time S.E (o + 2)))
            (S.E.proposer (o + 2))).st.core.σ Y.erase).h := by
      intro Y hYrun hY hTY
      have hYbody := Restated.namedBody_of_mem_storeBeforeTime_l86f facts (Setup.alwaysAwake S)
        (notHeldAt Sched) Finset.univ hf (Finset.mem_univ (S.E.proposer (o + 2)))
        (hmemOf Y.erase hY) hYrun
      have hYview := Restated.Vocabulary.Proofs.NamedStoreBridge.derivedView_stateBeforeTime facts
        (Setup.alwaysAwake S) R (M.proposal_time S.E (o + 2)) (S.E.proposer (o + 2)) _ hmemRead
        Y hYbody
      rw [hYview]
      exact hTband.trans hTY
    rcases preceq_linear_Preceq hTH hPH with hTP | hPT
    · have hTPn := Restated.namedPreceq_of_runBlock_erase_preceqOn facts (notHeldAt Sched)
        Finset.univ hf hTrun hPrun hTP
      exact Restated.Vocabulary.Proofs.HealingSurface.canonicalConeSegment_mem_filtered_of_root_preceq
        facts hpc hFJ hroot (hmemOf P.erase hPH)
        (hbandOf P hPrun hPH (facts.cs.derive_height_mono S.E S.cfg hTPn))
        (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _))
        (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _))
    · exact Restated.Vocabulary.Proofs.HealingSurface.canonicalConeSegment_mem_filtered_of_root_preceq
        facts hpc hFJ hroot (hmemOf T.erase hTH) (hbandOf T hTrun hTH le_rfl)
        (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _)) hPT
  have hactive : P.erase ∈ M.get_filtered_block_tree
      (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M (Setup.alwaysAwake S)
        (W (strictEventIndex R (M.proposal_time S.E (o + 1 + 1)))
          (S.E.proposer (o + 1 + 1))).st.core
        (M.proposal_time S.E (o + 1 + 1)))).toFG := by
    rw [(p86f% tickStore_eq₈₆f) facts, (p60% setClock_filtered₆₀) facts]
    exact hactiveStore
  have hupper := Restated.actionSGBlock_preceq_proposedParent_runAll_notHeld_afterDeadline facts S
    Sched x v₀ n hsync hmono hawake hgst hcv hvalid hawm hthird hn hcom hrec hc
    ((facts.sch.Protocol_vote_time_le_confirmation_time S.E o).trans (by rw [hconfA]; exact hAcHor))
    hopening cp hcp hP
  simp only [Nat.add_sub_cancel] at hupper
  obtain ⟨I, hI⟩ := facts.dt.with_proposal_input_nonempty (M.gradeContract cp) S.E S.hc
    ((Setup.alwaysAwake S).node (S.E.proposer o)) (M.toHealing pn.st.core)
  have hI' : Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract pn.cache) S.E S.hc
      ((Setup.alwaysAwake S).node (S.E.proposer o)) (M.toHealing pn.st.core) ⇢ I := by
    rw [hpncache]
    exact hI
  obtain ⟨-, hIP⟩ := (p58% parent_preceq_of_proposal₅₈s) facts (Setup.alwaysAwake S) R o pn hpread
    hPn I hI'
  have hupperP : ∀ v ∈ notHeldAt Sched
        ((Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) q)),
      ∀ nq ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (W (strictEventIndex R (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) q)) v) q,
      ∀ g, M.grade2_block_with (M.gradeContract nq.cache) S.E S.hc (M.toHealing nq.st.core)
          (M.round_of S.hc (M.toHealing nq.st.core).s) ⇢ g →
      ∀ B, M.get_sg_vote_with (M.gradeContract nq.cache) S.E S.hc (M.toHealing nq.st.core)
          (M.round_of S.hc (M.toHealing nq.st.core).s) g ⇢ B →
        Block.Preceq B P.erase := by
    intro v hv nq hnq g hg B hB
    exact preceq_trans_Preceq (hupper v hv nq hnq g hg B hB I hI) hIP
  have hrootProp : Block.Preceq
      (M.get_fg_root (M.toHealing (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex R (M.proposal_time S.E (o + 2))) (S.E.proposer (o + 2))).st
        (M.proposal_time S.E (o + 2)))
        (W (strictEventIndex R (M.proposal_time S.E (o + 2))) (S.E.proposer (o + 2))).record
        cp₂).st.core).toFG) P.erase := by
    rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [(p60% setClock_fgRoot₆₀) facts]
    exact hroot
  have hcut : Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (q + 1) ≤ R.horizon := by
    have h1 := facts.sch.proposal_time_mono S.E (Nat.le_add_right o 2)
    unfold Restated.Vocabulary.Protocol.HealConfig.Γ_neg1
    rw [facts.sch.Γ_0_eq_proposal_time S.hc S.E (q + 1)]
    linarith
  have hpostQ : tGAT + 1 ≤ (Restated.Vocabulary.Execution.Setup.a M S q) :=
    hloPost.trans ((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone (by
      unfold Restated.deadlineRoundW at hDq
      exact (Nat.le_succ _).trans ((Nat.le_add_right _ _).trans hDq)))
  have hgatG1 : tGAT + 1 ≤ M.domain S.E S.hc (q + 1) .g1 := by
    rw [facts.gr.Sts_domain_g1_eq_opening, facts.gr.opening_eq_proposal_time]
    exact hgatO
  have hslo : (M.opening_slot S.hc (q + 1)) + 1 ≤ o + 2 := Nat.succ_le_succ (Nat.le_succ o)
  have hshi : o + 2 < (M.opening_slot S.hc (q + 1 + 1)) := by
    have hR := S.hc.R_ge_three
    rw [ho, facts.gr.opening_slot_succ S.hc (q + 1)]
    exact Nat.add_lt_add_left (lt_of_lt_of_le (by decide) hR) _
  have hanchor := Restated.interiorProposalAnchor_preceq_of_previousCarriersOn_l85d facts
    (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ hf hHs hHsXb hbelow hpostQ hcut hslo
    hshi hpropHor hupperP huRead cp₂ hcp₂ hrootProp
    (fun u _ j hj => Restated.awake_g2_action_runAllPath facts S Sched x v₀ n hmono hawake hn q
      (lo_le_windows₈₅dw facts S (lt_of_lt_of_le (rGST_lt_deadline₈₅dw S tGAT gap) hDq)).1 u j hj)
    hgatG1
  have hround2 : M.round_of S.hc pn₂.st.core.s = q + 1 := by
    rw [hpn₂st, facts.nd.store_with_cache_core_s, facts.hd.Sts_setClock_core_s,
      facts.sch.slotOf_proposal_time]
    exact facts.gr.round_of_eq_of_opening_succ_le_of_lt_next_opening S.hc hslo hshi
  obtain ⟨A0, hA0⟩ := (p58% nodeAnchor_outcome₅₈) facts (Setup.alwaysAwake S) pn₂
    (M.round_of S.hc pn₂.st.core.s)
  have hA0' : Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M (Setup.alwaysAwake S) pn₂
      (q + 1) ⇢ A0 := by
    have h := hA0
    rw [hround2] at h
    exact h
  have hcompat : Block.compatible A0 P.erase = true :=
    compatible_of_preceq_common_Preceq (hanchor A0 hA0')
      (Proofs.ModelProperties.Preceq_self P.erase)
  have hconeT := Restated.coneTarget_preceq_nextProposedParent_namedOn facts (Setup.alwaysAwake S)
    (notHeldAt Sched) Finset.univ hf hHs hHsXb hcomOn (Nat.succ_pos o) hlo1
    (hsupp.trans hpropHor) (hHs _ _ (hsupp.trans (facts.sch.proposal_time_le_confirmation_time
      S.E _)) hprop2) hcone hactive cp₂ hcp₂ A0 hA0 hcompat
  obtain ⟨I₂, hI₂⟩ := facts.dt.with_proposal_input_nonempty (M.gradeContract cp₂) S.E S.hc
    ((Setup.alwaysAwake S).node (S.E.proposer (o + 2))) (M.toHealing pn₂.st.core)
  have hI₂' : Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract pn₂.cache) S.E S.hc
      ((Setup.alwaysAwake S).node (S.E.proposer (o + 2))) (M.toHealing pn₂.st.core) ⇢ I₂ := by
    rw [hpn₂cache]
    exact hI₂
  obtain ⟨Q, hQ, hQerase⟩ := Restated.Vocabulary.Proofs.HealingSurface.proposedBlockAt_parent facts
    (Setup.alwaysAwake S) R (o + 2) pn₂ hp₂read hP₂n I₂ hI₂'
  have hP₂ne : P₂ ≠ .genesis := by
    intro h; rw [h] at hQ; cases hQ
  have hP₂par : P₂.parent = Q := by
    cases P₂ with
    | genesis => cases hQ
    | node p sl rt vs sp rows proposer =>
        simp only [NamedBlock.parent?] at hQ
        rw [namedBlock_parent_node]
        exact Option.some.inj hQ
  have hP₂run := Restated.proposedBlock_runBlockOn facts (Setup.alwaysAwake S) (notHeldAt Sched)
    Finset.univ hf hHs hHsXb (Nat.succ_pos _) hprop2 hpropHor
    (hgatO.trans (facts.sch.proposal_time_mono S.E (Nat.le_add_right o 2)))
    (fun j hj => hf.tick_outcome j _ _ hj)
    (fun j hj => hf.awake_g1 _ _ j _ (Or.inl rfl) hj huRead (by
      show tGAT + 1 ≤ M.early S.E S.hc (M.round_of S.hc (o + 2)) .g1 - S.E.Δ
      rw [ho, facts.gr.round_of_opening_slot_add S.hc (q + 1)
        (Nat.lt_of_lt_of_le (by decide : 2 < 3) S.hc.R_ge_three)]
      exact hwinQ1.2))
    cp₂ hcp₂ hP₂clock
  have hQrun : Restated.RunBlockOn M (Setup.alwaysAwake S) R W Finset.univ Q :=
    Restated.blockInRun_of_ancestorOn facts (Setup.alwaysAwake S) R W Finset.univ hP₂run
      (by rw [← hP₂par]; exact parent_namedPreceq_l85 P₂)
  have hPQ : NamedBlock.Preceq P Q :=
    Restated.namedPreceq_of_runBlock_erase_preceqOn facts (notHeldAt Sched) Finset.univ hf hPrun hQrun
      (by rw [hQerase]; exact hconeT I₂ hI₂')
  have hQstore : Q.erase ∈ (W (strictEventIndex R (M.proposal_time S.E (o + 2)))
      (S.E.proposer (o + 2))).st.core.T := by
    rw [hQerase]
    have h := Restated.Vocabulary.Proofs.HealingSurface.proposedParent_mem facts (Setup.alwaysAwake S)
      R (o + 2) pn₂ hp₂read I₂ hI₂'
    rw [hpn₂st, facts.nd.store_with_cache_core_T, facts.hd.Sts_setClock_core_T] at h
    exact h
  have hP₂lt : P₂.parent.slot < P₂.slot :=
    named_parent_slot_lt_of_erase_l85d (Restated.proposedBlock_parent_slot_ltOn facts
      (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ hf (Nat.succ_pos _) cp₂ hcp₂ hP₂clock)
  have hP₂slot : P₂.slot = o + 2 :=
    Restated.Vocabulary.Proofs.Optimistic.proposedBlockAt_slot facts (Setup.alwaysAwake S) R (o + 2)
      (some P₂) ((p56% proposedBlockAt_mem₅₆h) facts (Setup.alwaysAwake S) hf (o + 2) cp₂ hcp₂
        hP₂clock) rfl
  refine ⟨hP₂ne, by rw [hP₂par]; exact hPQ, by rw [← hP₂slot]; exact hP₂lt, ?_⟩
  intro X hX hXne
  rcases hXeq : P₂ with _ | ⟨p, sl, rt, vs, sp, rows, proposer⟩
  · exact absurd hXeq hP₂ne
  · rw [hXeq] at hX
    rcases namedPreceq_node_iff_l85.mp hX with heq | hXp
    · rw [heq, ← hXeq]; exact hP₂lt
    · have hpQ : p = Q := by
        rw [hXeq, namedBlock_parent_node] at hP₂par
        exact hP₂par
      rw [hpQ] at hXp
      have hXmem := Restated.ancestor_mem_storeBeforeTimeOn facts (Setup.alwaysAwake S)
        (notHeldAt Sched) Finset.univ hf hQstore (Proofs.NamedWire.erase_preceq hXp)
      have hXne' : X.erase ≠ Block.genesis := fun h =>
        hXne (eq_named_genesis_of_erase_eq_genesis h)
      exact named_parent_slot_lt_of_erase_l85d (Restated.parent_slot_lt_of_mem_storeBeforeTimeOn
        facts (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ hf hXmem hXne')

end

end DecoupledConsensusModel.Sts.Restated
