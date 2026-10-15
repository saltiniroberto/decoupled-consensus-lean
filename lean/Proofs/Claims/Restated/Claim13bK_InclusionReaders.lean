import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bK_ConfirmedInclusion
import Proofs.Claims.Restated.Claim13bK_ConfirmedOld
import Proofs.Claims.Restated.Claim13bK_ConfirmedSettle
import Proofs.Claims.Restated.Claim13bK_FinBeforeTick
import Proofs.Claims.Restated.Claim13bK_GradeOldHeads
import Proofs.Claims.Restated.Claim13bK_InclusionAnchorTree
import Proofs.Claims.Restated.Claim13bK_InclusionExtends
import Proofs.Claims.Restated.Claim13bK_InclusionTick
import Proofs.Claims.Restated.Claim13bK_LiveConfirmedSlots
import Proofs.Claims.Restated.Claim13bK_PrevHeadsStep
import Proofs.Claims.Restated.Claim13bStepCone
import Proofs.Claims.Restated.Claim13bStepConeIter
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13beRoute3_82
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActiveJoint
import Model.Conditions.Claim13bInvariantActiveSinceW
import Model.Conditions.Claim13bInvariantActiveTop
import Model.Conditions.Claim13bK_ConfirmedInclusion
import Model.Conditions.Claim13bK_ConfirmedSettle
import Model.Conditions.Claim13bK_ConfirmedWake
import Model.Conditions.Claim13bK_FinBeforeTick
import Model.Conditions.Claim13bK_InclusionReaders
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13bStepCone
import Model.Conditions.Claim13bStepConeIter
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_5
import Model.Conditions.Claim13beRoute3_74
import Model.Conditions.Claim13beRoute3_83
import Model.Conditions.CommonViewOfFinalizedDescendantsFacts
import Model.Conditions.RunAll
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Sts_Spec2Claims_Claim13bf
import Model.Conditions.Sts_Spec2Claims_ClaimConfirmedAfterHealing
import Model.Conditions.Sts_Spec2Claims_ClaimConfirmedIncludedAfterHealing
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Record.Wiring

/-!
# Confirmed outputs include the honest proposals

After the phase, every block an honest proposer sends is an ancestor of the confirmed output of
every honest reader awake through its vote window, from six delays after the proposal on, stated
over a model `M : Record.Model V` and its facts `facts : Record.Facts M`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

local macro "p83% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_83)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "pHP% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13bK_HeadsPersist)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "pCW% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13bK_ConfirmedWake)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "pW% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13bK_ConfirmedStrongRoundWindow)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "pCR% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13bK_ConfirmedRecord)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "pIT% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13bK_InclusionTick)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "pCS% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13bK_ConeSlots)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

private theorem nat_pred_bounds_e (o s o' : Nat) (hs : 1 ≤ s) (h0 : o ≤ s - 1) (h1 : s - 1 < o') :
    o + 1 ≤ s ∧ s ≤ o' := by
  omega

private theorem nat_sub_two_e (s s' R : Nat) (hlt : s + 1 < s') (h3 : 3 ≤ R) :
    s' - 2 + 2 = s' ∧ s ≤ s' - 2 ∧ s' ≤ s' - 2 + R := by
  omega

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Under `SleepsAfterActionInstants`, if `1 ≤ s` and `v` is in `activeAtW S Sched (s + 1)`, then
    `v` is awake at every instant from `slotStart s − Δ` to slot `s`'s confirmation instant. -/
theorem awakeThroughout_confirmation_of_activeAtW_next (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (hs : Restated.SleepsAfterActionInstants M S Sched) {s : Slot} (hs1 : 1 ≤ s) {v : V}
    (hv : v ∈ activeAtW S Sched (s + 1)) :
    v ∈ Sched.awakeThroughout (slotStart S.E.Δ s - S.E.Δ) (M.confirmation_time S.E s) := by
  have hd := S.E.Δ_pos
  have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  have hwv : wVote S = (4 * (S.hc.R : Int) + 2) * S.E.Δ := rfl
  have hss : slotStart S.E.Δ s = 4 * S.E.Δ * (s : Int) := slotStart_closed S.E.Δ s
  have hss1 : slotStart S.E.Δ (s + 1) = 4 * S.E.Δ * (s : Int) + 4 * S.E.Δ := by
    rw [slotStart_closed]; push_cast; ring
  have hct : M.confirmation_time S.E s = 4 * S.E.Δ * (s : Int) + 6 * S.E.Δ :=
    (pCR% confirmation_time_closed_cr) facts S.E s
  have hv' : v ∈ Sched.awakeThroughout (slotStart S.E.Δ (s + 1) + S.E.Δ - wVote S)
      (slotStart S.E.Δ (s + 1) + S.E.Δ) := hv
  have hlow : v ∈ Sched.awakeThroughout (slotStart S.E.Δ s - S.E.Δ)
      (slotStart S.E.Δ s + 5 * S.E.Δ) := by
    refine awakeThroughout_mono Sched hv' ?_ ?_
    · rw [hwv, hss1, hss]; nlinarith
    · rw [hss1, hss]; linarith
  have h0 := facts.gr.opening_slot_round_of_le_slot S.hc (s - 1)
  have h1 := facts.gr.lt_opening_slot_round_of_succ S.hc (s - 1)
  obtain ⟨hn0, hn1⟩ := nat_pred_bounds_e _ _ _ hs1 h0 h1
  have hi0 : (((M.opening_slot S.hc ((M.round_of S.hc (s - 1)))) : Nat) : Int) + 1 ≤ (s : Int) := by
    exact_mod_cast hn0
  have hi1 : (s : Int) ≤ (((M.opening_slot S.hc ((M.round_of S.hc (s - 1)) + 1)) : Nat) : Int) := by
    exact_mod_cast hn1
  have ha0 : (Restated.Vocabulary.Execution.Setup.a M S ((M.round_of S.hc (s - 1))))
      = 4 * S.E.Δ * (((M.opening_slot S.hc ((M.round_of S.hc (s - 1)))) : Nat) : Int) + 6 * S.E.Δ := by
    rw [← Restated.confirmation_time_opening_slot facts S ((M.round_of S.hc (s - 1))),
      (pCR% confirmation_time_closed_cr) facts]
  have ha1 : (Restated.Vocabulary.Execution.Setup.a M S ((M.round_of S.hc (s - 1)) + 1))
      = 4 * S.E.Δ * (((M.opening_slot S.hc ((M.round_of S.hc (s - 1)) + 1)) : Nat) : Int)
        + 6 * S.E.Δ := by
    rw [← Restated.confirmation_time_opening_slot facts S ((M.round_of S.hc (s - 1)) + 1),
      (pCR% confirmation_time_closed_cr) facts]
  have h4 : (0 : Int) ≤ 4 * S.E.Δ := by linarith
  have hm0 := mul_le_mul_of_nonneg_left hi0 h4
  have hm1 := mul_le_mul_of_nonneg_left hi1 h4
  refine mem_awakeThroughout_of_forall Sched (fun t ht0 ht1 => ?_)
  by_cases ht : t ≤ slotStart S.E.Δ s + 5 * S.E.Δ
  · exact mem_awake_of_awakeThroughout Sched hlow ht0 ht
  · have haw5 : v ∈ Sched.awake (slotStart S.E.Δ s + 5 * S.E.Δ) :=
      mem_awake_of_awakeThroughout Sched hlow (by linarith) le_rfl
    refine Restated.awake_forward_to_action facts S Sched hs (r := (M.round_of S.hc (s - 1))) ?_ haw5 t
      (by linarith) ?_
    · rw [ha0, hss]; nlinarith
    · rw [ha1]; rw [hct] at ht1; nlinarith

/-- If validators wake only at action instants, `s_w + 1 ≤ s' ≤ s_w + 2`, the round of `s_w + 1` is
    not round `0`, and `v` is awake throughout the vote window of slot `s'` and from one delay
    before slot `s_w`'s start to its confirmation instant, then `v` is awake from one delay before
    the grade-2 early cutoff of the round of `s_w + 1` to slot `s_w`'s confirmation instant. -/
theorem awakeThroughout_grade2_window_of_activeAtW (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (hw : Restated.WakesAtActionInstants M S Sched) {s_w s' : Slot}
    (h1 : s_w + 1 ≤ s') (h2 : s' ≤ s_w + 2) (hr1 : 1 ≤ M.round_of S.hc (s_w + 1)) {v : V}
    (hva : v ∈ activeAtW S Sched s')
    (hwaw : v ∈ Sched.awakeThroughout (slotStart S.E.Δ s_w - S.E.Δ) (M.confirmation_time S.E s_w)) :
    v ∈ Sched.awakeThroughout (M.early S.E S.hc (M.round_of S.hc (s_w + 1)) .g2 - S.E.Δ)
      (M.confirmation_time S.E s_w) := by
  have hd : (1 : Int) ≤ S.E.Δ := S.E.Δ_pos
  have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  have hwv : wVote S = (4 * (S.hc.R : Int) + 2) * S.E.Δ := rfl
  have hv' : v ∈ Sched.awakeThroughout (slotStart S.E.Δ s' + S.E.Δ - wVote S)
      (slotStart S.E.Δ s' + S.E.Δ) := hva
  have hss': slotStart S.E.Δ s' = 4 * S.E.Δ * (s' : Int) := slotStart_closed S.E.Δ s'
  have hssw : slotStart S.E.Δ s_w = 4 * S.E.Δ * (s_w : Int) := slotStart_closed S.E.Δ s_w
  have hct : M.confirmation_time S.E s_w = 4 * S.E.Δ * (s_w : Int) + 6 * S.E.Δ :=
    (pCR% confirmation_time_closed_cr) facts S.E s_w
  have ho0 := facts.gr.opening_slot_round_of_le_slot S.hc (s_w + 1)
  have ho1 := facts.gr.lt_opening_slot_round_of_succ S.hc (s_w + 1)
  rw [facts.gr.opening_slot_succ] at ho1
  have hA : (Restated.Vocabulary.Execution.Setup.a M S (M.round_of S.hc (s_w + 1))) =
      4 * S.E.Δ * ((M.opening_slot S.hc (M.round_of S.hc (s_w + 1)) : Nat) : Int) + 6 * S.E.Δ := by
    rw [← Restated.confirmation_time_opening_slot facts S (M.round_of S.hc (s_w + 1)),
      (pCR% confirmation_time_closed_cr) facts]
  have he := facts.gr.early_g2_eq S (M.round_of S.hc (s_w + 1))
  have hprev : M.a S.hc S.E.Δ (M.round_of S.hc (s_w + 1) - 1) + S.E.Δ ≤
      M.early S.E S.hc (M.round_of S.hc (s_w + 1)) .g2 :=
    facts.gr.action_delta_le_early S S.hc.R_ge_three (Nat.sub_lt hr1 Nat.one_pos)
  have hsucc : M.round_of S.hc (s_w + 1) - 1 + 1 = M.round_of S.hc (s_w + 1) :=
    Nat.sub_add_cancel hr1
  generalize M.round_of S.hc (s_w + 1) = r_w at *
  generalize M.opening_slot S.hc r_w = o at *
  have hA' : M.a S.hc S.E.Δ r_w = 4 * S.E.Δ * (o : Int) + 6 * S.E.Δ := hA
  have h4 : (0 : Int) ≤ 4 * S.E.Δ := by linarith
  have hRΔ : 3 * S.E.Δ ≤ (S.hc.R : Int) * S.E.Δ := by nlinarith
  refine mem_awakeThroughout_of_forall Sched (fun t ht0 ht1 => ?_)
  by_cases hta : slotStart S.E.Δ s_w - S.E.Δ ≤ t
  · exact mem_awake_of_awakeThroughout Sched hwaw hta ht1
  by_cases htb : slotStart S.E.Δ s' + S.E.Δ - wVote S ≤ t
  · refine mem_awake_of_awakeThroughout Sched hv' htb ?_
    have hI : ((s_w : Nat) : Int) + 1 ≤ ((s' : Nat) : Int) := by exact_mod_cast h1
    have hm := mul_le_mul_of_nonneg_left hI h4
    rw [hss']; rw [hssw] at hta; linarith
  have hlate : o + S.hc.R ≤ s' + 1 := by
    by_contra hcon
    have hI : ((s' : Nat) : Int) + 2 ≤ ((o : Nat) : Int) + (S.hc.R : Int) := by
      have : s' + 2 ≤ o + S.hc.R := Nat.succ_le_of_lt (Nat.lt_of_not_le hcon)
      exact_mod_cast this
    have hm := mul_le_mul_of_nonneg_left hI h4
    rw [hss', hwv] at htb
    rw [he, hA'] at ht0
    nlinarith
  have hI : ((o : Nat) : Int) + (S.hc.R : Int) ≤ ((s' : Nat) : Int) + 1 := by exact_mod_cast hlate
  have hm := mul_le_mul_of_nonneg_left hI h4
  have hI2 : ((s' : Nat) : Int) ≤ ((o : Nat) : Int) + (S.hc.R : Int) := by
    have : s' ≤ o + S.hc.R := le_trans h2 (Nat.succ_le_of_lt ho1)
    exact_mod_cast this
  have hm2 := mul_le_mul_of_nonneg_left hI2 h4
  have hawk : v ∈ Sched.awake (M.a S.hc S.E.Δ r_w - 1) := by
    refine mem_awake_of_awakeThroughout Sched hv' ?_ ?_
    · rw [hss', hwv, hA']; nlinarith
    · rw [hss', hA']; nlinarith
  have hback := Restated.awake_since_action facts S Sched hw (r := r_w - 1)
    (t := M.a S.hc S.E.Δ r_w - 1)
    (show (Restated.Vocabulary.Execution.Setup.a M S (r_w - 1)) ≤ M.a S.hc S.E.Δ r_w - 1 by
      show M.a S.hc S.E.Δ (r_w - 1) ≤ _; rw [he] at hprev; linarith)
    (show M.a S.hc S.E.Δ r_w - 1 < (Restated.Vocabulary.Execution.Setup.a M S (r_w - 1 + 1)) by
      rw [hsucc]; show _ < M.a S.hc S.E.Δ r_w; linarith) hawk
  refine hback t ?_ ?_
  · show M.a S.hc S.E.Δ (r_w - 1) ≤ t
    linarith
  · rw [hss', hwv] at htb
    nlinarith

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- On the premises of `afterPhaseJointRound_of_premises` and `RecordsSettledAtSettleTick`, if slot
    `s` is at or after round `(rW + 1)`'s third slot, every honest active committee member of every
    slot from `s` on votes for a descendant of `B`, `v` is awake from one delay before slot `s`'s
    start to its confirmation instant and honest through the step after the tick there, and the node
    state that tick reads passes the grade-2 awake test of the round of `s + 1` (`hrun`), then right
    after that tick `v`'s confirmed output is a descendant of `B`. -/
theorem preceq_get_confirmed_at_write (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (hcatch : Restated.CatchUpOnWake M S x) (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (hsync : Restated.SynchronyFromWake M S x) (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight) (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t) (hrsW : Restated.roundSleepinessW M S Sched tE) (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT) (hcs : Restated.committeeSleepinessW M S Sched tE) (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched)) (hw : Restated.WakesAtActionInstants M S Sched) (hs : Restated.SleepsAfterActionInstants M S Sched) (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap) (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.BasePreviousRoundSGCompatibleWithAnchorAtRound M S Sched x v r N
        (Restated.runAllPath M S Sched x v N) T) (hclear : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round) (n₀ : Nat),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S r)) →
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T) (hB' : Restated.BaseJustifiedHighAtSwitchRoundW M S Sched x tGAT tE gap) {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)))) {T_W : NamedBlock V} (hAW : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W) (hJswitch : ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) - 1
        ≤ (x[n₁].time : Int) →
      n₁ ≤ n_W → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T_W.erase)
    {n₀ : Nat} {T₀ : NamedBlock V} (hTW₀ : Block.Preceq T_W.erase T₀.erase)
    (hJ₀ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x (Restated.switchRound M S tE) n₀ n_W T₀)
    (hsettle : Restated.RecordsSettledAtSettleTick M S Sched x tE)
    {s : Slot} (hsl : (M.opening_slot S.hc (Restated.switchRound M S tE + 1)) + 2 ≤ s)
    {B : Block V} (hBh : Restated.AncestorOfHonestHeadsFrom M S Sched x B s)
    {m : Nat} (hm : Restated.tickStepAt M x m (M.confirmation_time S.E s))
    {v : V} (hvaw : v ∈ Sched.awakeThroughout (slotStart S.E.Δ s - S.E.Δ)
      (M.confirmation_time S.E s))
    (hvh : Restated.HonestThrough M Sched x (m + 1) v)
    -- `hrun`: the node state `v`'s tick reads passes the grade-2 awake test of the round of
    -- `s + 1`.
    (hrun : M.awake_for_grade2 (Setup.alwaysAwake S) v
      (Record.wakeStage M Sched (M.confirmation_time S.E s) x[m] v) (M.round_of S.hc (s + 1))) :
    Block.Preceq B (M.get_confirmed (x[m + 1][v].st).st.core) := by
  have hd := S.E.Δ_pos
  obtain ⟨hm1, -⟩ := Restated.tickStepAt_time facts x hm
  have hvh' : HonestThroughTime Sched (M.confirmation_time S.E s) v :=
    fun t ht => hvh t (by rw [hm1]; exact ht)
  have hspos : 0 < s := lt_of_lt_of_le Nat.zero_lt_two (le_trans (Nat.le_add_left 2 _) hsl)
  obtain ⟨r, n, T, hr, hTW, hJ, -, hs1, hT⟩ := Restated.exists_joint_anchor_headsBelow_atSlot facts S Sched x
    tE hexec hmono htd hcatch tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw
    hs hrec hprev hclear hB' hnW hAW hJswitch hTW₀ hJ₀ (le_trans (Nat.le_add_right _ 2) hsl)
  have hinv := (pHP% joint_toTop_hp) hJ
  have hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x r n'' T :=
    fun n'' h => Restated.stepFinalizedCrossingUnderAnchor_of_afterSwitch facts S Sched x hr hnW
      hJ.toAfterPhaseInvariantOverActiveSetsSince
      (Restated.justified_preceq_anchor_ofJoint facts S Sched x tE hexec hmono htd tGAT gap hgst hlen hsync
        hthird hphase hrsW hmult hcv hcom hrec hprev hclear hB' hnW hAW hr hTW hJ h)
  obtain ⟨n', hn'⟩ := Restated.tick_field_at_succ facts S Sched x htd r
  have hfin := Restated.fin_old_anchor_before_succ_tick_of_hypotheses facts S Sched x tE
    hexec hmono tGAT gap hgst hlen hthird hphase hrsW hr hinv hcross hn'
  have hunderT := Restated.deliveredDescendantUnderFinalized_anchor facts S Sched x hn' hfin tGAT
  have hunderTS := Restated.finalizedPreceqAtSteps_anchor facts S Sched x hn' hfin tGAT
  have hs1I : ((s : Nat) : Int) ≤ (((M.opening_slot S.hc (r + 1)) : Nat) : Int) := by
    exact_mod_cast hs1
  have hSa1 : (Restated.Vocabulary.Execution.Setup.a M S (r + 1))
      = 4 * S.E.Δ * (((M.opening_slot S.hc (r + 1)) : Nat) : Int) + 6 * S.E.Δ := by
    rw [← Restated.confirmation_time_opening_slot facts S (r + 1), (pCR% confirmation_time_closed_cr) facts]
  have hmul1 := mul_le_mul_of_nonneg_left hs1I (le_of_lt (by linarith : (0 : Int) < 4 * S.E.Δ))
  have hcut : M.support_cutoff S.E s ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) - 1 := by
    have hd1 : (1 : Int) ≤ S.E.Δ := hd
    rw [(pIT% support_cutoff_eq_of_pos) facts S.E hspos, slotStart_closed, hSa1]; linarith
  have hcsW := Restated.committeeSleepinessW_at_heads_slot facts S Sched tE hmono hcom tGAT gap hgst hlen hphase
    hcs (r := Restated.switchRound M S tE + 1) (Nat.le_succ _)
  have hmaj := Restated.majority_of_committeeSleepinessW facts S Sched hcsW (s := s)
    (slotStart_mono S (Nat.le_succ_of_le hsl))
  obtain ⟨w, hwmem⟩ : ((S.E.committee s) ∩ Restated.HonSlot M S Sched s).Nonempty := by
    rw [← Finset.card_pos]; omega
  have hwH := (Finset.mem_inter.mp hwmem).2
  obtain ⟨mw, hmw⟩ := Restated.exists_tickStepAt facts x htd (facts.sch.vote_time_pos S hspos)
  obtain ⟨G, hG⟩ := (pCS% gfHeadFrom_nonempty_cs) facts S (x[mw][w].st) s
  have hBw := hBh s le_rfl w mw hwH hmw G hG
  have hTw := hT w mw hwH hmw G hG
  have hop : (M.opening_slot S.hc (Restated.switchRound M S tE)) ≤ (M.opening_slot S.hc (Restated.switchRound M S tE + 1)) :=
    facts.gr.opening_slot_mono S (Nat.le_succ _)
  have hs0 : (M.opening_slot S.hc (Restated.switchRound M S tE)) + 2 ≤ s :=
    le_trans (Nat.add_le_add_right hop 2) hsl
  obtain ⟨X, hBX, hTX, hX⟩ : ∃ X : Block V, Block.Preceq B X ∧ Block.Preceq T.erase X ∧
      Restated.AncestorOfHonestHeadsFrom M S Sched x X s := by
    rcases preceq_linear_Preceq hBw hTw with h | h
    · exact ⟨T.erase, h, preceq_eq_true_iff_Preceq.mp (Block.preceq_self _),
        Restated.ancestorOfHonestHeadsFrom_of_headsBelow_i1 facts S Sched x tE hexec hmono htd tGAT gap hgst
          hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear hB' hnW hAW
          hJswitch (r₀ := Restated.switchRound M S tE) le_rfl hTW₀ hJ₀ hs0 hT⟩
    · exact ⟨B, preceq_eq_true_iff_Preceq.mp (Block.preceq_self _), h, hBh⟩
  have hunder : Restated.DeliveredDescendantUnderFinalizedInPhase M S x tGAT
      (M.support_cutoff S.E s) X := by
    intro d u u' C hlbl huh h0 h1 hXC
    exact hunderT d u u' C hlbl huh h0 (le_trans h1 hcut) (preceq_trans_Preceq hTX hXC)
  have hunderS : Restated.FinalizedPreceqAtStepsInPhase M S x tGAT
      (M.support_cutoff S.E s) X :=
    fun d u huh h0 h1 => preceq_trans_Preceq (hunderTS d u huh h0 (le_trans h1 hcut)) hTX
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc (M.toHealing (x[m][v].st).st.core)
    (M.confirmation_time S.E s) (x[m][v].st).cache
  obtain ⟨A, hAo'⟩ := facts.fc.get_sg_root_with_nonempty (M.gradeContract c) S.E S.hc
    (M.toHealing (Restated.confStoreAt M S (x[m][v].st) s))
    (M.round_of S.hc (Restated.confStoreAt M S (x[m][v].st) s).s)
  have hAo : Restated.Vocabulary.Protocol.confAnchorWith M (M.gradeContract c) S.E S.hc
      (Restated.confStoreAt M S (x[m][v].st) s) ⇢ A := hAo'
  have hA := Restated.confAnchor_headsBelow_atSlot facts S Sched x tE hexec hmono htd hcatch tGAT gap hgst hlen
    hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear hB' hnW hAW hJswitch
    hTW₀ hJ₀ hsl hm hvaw hvh' c hc A hAo
  have hpath := Restated.confAnchorChainInTree_atSlot facts S Sched x tE hexec hmono htd hcatch tGAT gap hgst
    hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear hB' hnW hAW hJswitch
    hTW₀ hJ₀ hsl hm hvaw hvh' (hX s le_rfl) c hc A hAo
  exact preceq_trans_Preceq hBX (Restated.get_confirmed_descendant_after_confirmation_tick facts S Sched x tE
    hexec hmono htd hcatch tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs
    hrec hprev hclear hB' hnW hAW hJswitch hTW₀ hJ₀ hsettle hsl hX hunder
    hunderS hm hvaw hvh hrun c hc A hAo hA hpath)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- On the premises of `afterPhaseJointRound_of_premises` and `RecordsSettledAtSettleTick`, if
    `HonestProposalHeadsAtOwnSlot` holds up to `tHi`, then for every slot `s` from round
    `(rW + 1)`'s third slot on whose confirmation instant is at or before `tHi`, every block `s`'s
    honest proposer sent by `s`'s vote instant is an ancestor of the confirmed output of every
    validator honest through its read and awake throughout the vote window of its read's slot, at
    every read from six delays after `s`'s proposal instant on. -/
theorem confirmedIncluded_of_ownSlotVotes_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (hcatch : Restated.CatchUpOnWake M S x) (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (hsync : Restated.SynchronyFromWake M S x) (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight) (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t) (hrsW : Restated.roundSleepinessW M S Sched tE) (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT) (hcs : Restated.committeeSleepinessW M S Sched tE) (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched)) (hw : Restated.WakesAtActionInstants M S Sched) (hs : Restated.SleepsAfterActionInstants M S Sched) (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap) (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.BasePreviousRoundSGCompatibleWithAnchorAtRound M S Sched x v r N
        (Restated.runAllPath M S Sched x v N) T) (hclear : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round) (n₀ : Nat),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S r)) →
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T) (hB' : Restated.BaseJustifiedHighAtSwitchRoundW M S Sched x tGAT tE gap) {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)))) {T_W : NamedBlock V} (hAW : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W) (hJswitch : ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) - 1
        ≤ (x[n₁].time : Int) →
      n₁ ≤ n_W → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T_W.erase)
    {n₀ : Nat} {T₀ : NamedBlock V} (hTW₀ : Block.Preceq T_W.erase T₀.erase)
    (hJ₀ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x (Restated.switchRound M S tE) n₀ n_W T₀)
    (hsettle : Restated.RecordsSettledAtSettleTick M S Sched x tE)
    {tHi : Int}
    (hadopt : Restated.HonestProposalHeadsAtOwnSlot M S Sched x
      ((M.opening_slot S.hc (Restated.switchRound M S tE + 1))) tHi) :
    ∀ s : Slot, (M.opening_slot S.hc (Restated.switchRound M S tE + 1)) + 2 ≤ s →
      M.confirmation_time S.E s ≤ tHi → Restated.ConfirmedIncludedAtSlot M S Sched x s := by
  intro s hsl hct hprop i B hB hi v j hvj htj hva
  have hd := S.E.Δ_pos
  have hR3 := S.hc.R_ge_three
  -- step 1: the honest heads from `s` on descend from `B`
  have hop : (M.opening_slot S.hc (Restated.switchRound M S tE)) ≤ (M.opening_slot S.hc (Restated.switchRound M S tE + 1)) :=
    facts.gr.opening_slot_mono S (Nat.le_succ _)
  have hs0 : (M.opening_slot S.hc (Restated.switchRound M S tE)) + 2 ≤ s :=
    le_trans (Nat.add_le_add_right hop 2) hsl
  have hBh : Restated.AncestorOfHonestHeadsFrom M S Sched x B s :=
    Restated.honestProposal_ancestorOfHonestHeadsFrom_i1 facts S Sched x tE hexec hmono htd tGAT gap hgst hlen
      hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear hB' hnW hAW hJswitch
      (r₀ := Restated.switchRound M S tE) le_rfl hTW₀ hJ₀ hadopt hs0
      (le_trans (Nat.le_add_right _ 2) hsl) hct hprop hB hi
  have hdelay : confirmedInclusionDelay S = 6 * S.E.Δ := rfl
  have hctc := (pCR% confirmation_time_closed_cr) facts S.E s
  have hctj : M.confirmation_time S.E s ≤ (x[j].time : Int) := by
    have hps : slotStart S.E.Δ s ≤ M.proposal_time S.E s :=
      slotStart_le_of_le_slotOf S (facts.sch.Sts_proposal_time_nonneg S s)
        (le_of_eq (facts.sch.slotOf_proposal_time S.E s).symm)
    have h6 := facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E s
    rw [hdelay] at htj
    linarith
  have hj0 : (0 : Int) ≤ (x[j].time : Int) := Int.natCast_nonneg _
  -- step 2: the write's slot `s_w`
  have hss1 : slotStart S.E.Δ (s + 1) ≤ (x[j].time : Int) := by
    have e : slotStart S.E.Δ (s + 1) = 4 * S.E.Δ * (s : Int) + 4 * S.E.Δ := by
      rw [slotStart_closed]; push_cast; ring
    rw [e]; linarith
  have hs'1 : s + 1 ≤ S.E.slotOf (x[j].time : Int) := by
    have h := slotOf_mono_sts S hss1
    rwa [slotOf_slotStart] at h
  obtain ⟨s_w, hsw, hsw1, hsw2, hwaw, hwct⟩ : ∃ s_w : Slot, s ≤ s_w ∧
      s_w + 1 ≤ S.E.slotOf (x[j].time : Int) ∧ S.E.slotOf (x[j].time : Int) ≤ s_w + 2 ∧
      v ∈ Sched.awakeThroughout (slotStart S.E.Δ s_w - S.E.Δ)
        (M.confirmation_time S.E s_w) ∧
      M.confirmation_time S.E s_w ≤ (x[j].time : Int) := by
    rcases Nat.eq_or_lt_of_le hs'1 with heq | hlt
    · have hs1 : 1 ≤ s := le_trans (Nat.le_add_left 1 _) (le_trans (Nat.le_succ _) hsl)
      have hle1 : s + 1 ≤ S.E.slotOf (x[j].time : Int) := le_of_eq heq
      have hle2 : S.E.slotOf (x[j].time : Int) ≤ s + 2 := by rw [← heq]; exact Nat.le_succ _
      rw [← heq] at hva
      exact ⟨s, le_rfl, hle1, hle2,
        Restated.awakeThroughout_confirmation_of_activeAtW_next facts S Sched hs hs1 hva, hctj⟩
    · obtain ⟨h2, hsw2, hR2⟩ := nat_sub_two_e _ _ _ hlt hR3
      refine ⟨S.E.slotOf (x[j].time : Int) - 2, hsw2, le_trans (Nat.le_succ _) (le_of_eq h2),
        le_of_eq h2.symm,
        Restated.awakeThroughout_confirmation_of_activeAtW facts S Sched hva (le_of_eq h2) hR2, ?_⟩
      have hst := slotStart_le_of_le_slotOf S hj0 (le_refl (S.E.slotOf (x[j].time : Int)))
      rw [slotStart_closed] at hst
      rw [(pCR% confirmation_time_closed_cr) facts]
      have hcI : ((S.E.slotOf (x[j].time : Int) - 2 : Nat) : Int) + 2
          = ((S.E.slotOf (x[j].time : Int) : Nat) : Int) := by exact_mod_cast h2
      have e : 4 * S.E.Δ * ((S.E.slotOf (x[j].time : Int) - 2 : Nat) : Int) + 6 * S.E.Δ
          = 4 * S.E.Δ * ((S.E.slotOf (x[j].time : Int) : Nat) : Int) - 2 * S.E.Δ := by
        rw [← hcI]; ring
      rw [e]; linarith
  -- step 3: the write at the tick at slot `s_w`'s confirmation instant
  have hcpos : 0 < M.confirmation_time S.E s_w := by
    rw [(pCR% confirmation_time_closed_cr) facts]
    have : (0 : Int) ≤ (s_w : Int) := Int.natCast_nonneg _
    nlinarith
  obtain ⟨m, hm⟩ := Restated.exists_tickStepAt facts x htd hcpos
  obtain ⟨hm1, hm0⟩ := Restated.tickStepAt_time facts x hm
  have hmj : m + 1 ≤ j := by
    by_contra hcon
    have := Restated.time_mono_int facts S Sched x (Nat.le_of_lt_succ (Nat.lt_of_not_le hcon))
    linarith
  have hvh : Restated.HonestThrough M Sched x (m + 1) v :=
    fun t ht => hvj t (le_trans ht (by rw [hm1]; exact hwct))
  have hr1 : 1 ≤ M.round_of S.hc (s_w + 1) := by
    by_contra hcon
    have h0 : M.round_of S.hc (s_w + 1) = 0 := Nat.lt_one_iff.mp (Nat.lt_of_not_le hcon)
    have h1 := facts.gr.lt_opening_slot_round_of_succ S.hc (s_w + 1)
    rw [h0, Nat.zero_add] at h1
    have h2 := facts.gr.opening_slot_mono S (Nat.le_add_left 1 (Restated.switchRound M S tE))
    have hle : M.opening_slot S.hc (Restated.switchRound M S tE + 1) ≤ s_w :=
      le_trans (Nat.le_add_right _ 2) (le_trans hsl hsw)
    exact Nat.lt_irrefl _ (lt_trans (Nat.lt_succ_self s_w)
      (lt_of_lt_of_le (lt_of_lt_of_le h1 h2) hle))
  have hrun : M.awake_for_grade2 (Setup.alwaysAwake S) v
      (Record.wakeStage M Sched (M.confirmation_time S.E s_w) x[m] v)
      (M.round_of S.hc (s_w + 1)) := by
    obtain ⟨τ, hl, hτ⟩ := id hm
    rw [← hτ]
    refine facts.ndRun.run_fact_g2_at S Sched x m τ (M.round_of S.hc (s_w + 1)) v hl ?_ ?_ ?_
    · have h1 := facts.gr.early_g2_le_opening S (M.round_of S.hc (s_w + 1))
      have h3 := facts.gr.opening_eq_proposal_time S.E S.hc (M.round_of S.hc (s_w + 1))
      have h4 := facts.sch.proposal_time_mono S.E
        (facts.gr.opening_slot_round_of_le_slot S.hc (s_w + 1))
      have h5 := facts.sch.proposal_time_succ_lt_confirmation_time S.E s_w
      rw [hτ]
      linarith
    · rw [hτ]
      exact Restated.awakeThroughout_grade2_window_of_activeAtW facts S Sched hw hsw1 hsw2 hr1 hva
        hwaw
    · rw [hτ]
      exact fun t ht => hvh t (by rw [hm1]; exact ht)
  have hwrite := Restated.preceq_get_confirmed_at_write facts S Sched x tE hexec hmono htd hcatch tGAT gap hgst
    hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear hB' hnW hAW hJswitch
    hTW₀ hJ₀ hsettle (le_trans hsl hsw) (Restated.ancestorOfHonestHeadsFrom_mono facts S Sched x hsw hBh) hm
    hwaw hvh hrun
  -- step 4: the output only extends from the write to the read
  have hext := Restated.confirmedOnlyExtendsAfterHealing_of_settle facts S Sched x tE hexec hmono htd hcatch tGAT
    gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear hB' hnW hAW
    hJswitch hTW₀ hJ₀ hsettle
  have hsettleT : Restated.confirmedSettleTime M S tE ≤ (x[m + 1].time : Int) := by
    have e : Restated.confirmedSettleTime M S tE = (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE + 1)) := rfl
    have hoI : (((M.opening_slot S.hc (Restated.switchRound M S tE + 1)) : Nat) : Int) ≤ ((s_w : Nat) : Int) := by
      exact_mod_cast (le_trans (Nat.le_add_right _ 2) (le_trans hsl hsw))
    have hmul := mul_le_mul_of_nonneg_left hoI (le_of_lt (by linarith : (0 : Int) < 4 * S.E.Δ))
    rw [e, hm1, ← Restated.confirmation_time_opening_slot facts S (Restated.switchRound M S tE + 1),
      (pCR% confirmation_time_closed_cr) facts, (pCR% confirmation_time_closed_cr) facts]
    linarith
  exact preceq_trans_Preceq hwrite (hext v (m + 1) j hmj hvj hsettleT)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- On the premises of `afterPhaseJointRound_of_premises` and `RecordsSettledAtSettleTick`, if
    `HonestProposalHeadsAtOwnSlot` holds at every `tHi`, then for every slot from round `(rW + 1)`'s
    third slot on, every block the slot's honest proposer sent by the slot's vote instant is an
    ancestor of the confirmed output of every validator honest through its read and awake throughout
    the vote window of its read's slot, at every read from six delays after the slot's proposal
    instant on. -/
theorem confirmedIncluded_of_ownSlotVotes (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (hcatch : Restated.CatchUpOnWake M S x) (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (hsync : Restated.SynchronyFromWake M S x) (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight) (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t) (hrsW : Restated.roundSleepinessW M S Sched tE) (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT) (hcs : Restated.committeeSleepinessW M S Sched tE) (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched)) (hw : Restated.WakesAtActionInstants M S Sched) (hs : Restated.SleepsAfterActionInstants M S Sched) (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap) (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.BasePreviousRoundSGCompatibleWithAnchorAtRound M S Sched x v r N
        (Restated.runAllPath M S Sched x v N) T) (hclear : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round) (n₀ : Nat),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S r)) →
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T) (hB' : Restated.BaseJustifiedHighAtSwitchRoundW M S Sched x tGAT tE gap) {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)))) {T_W : NamedBlock V} (hAW : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W) (hJswitch : ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) - 1
        ≤ (x[n₁].time : Int) →
      n₁ ≤ n_W → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T_W.erase)
    {n₀ : Nat} {T₀ : NamedBlock V} (hTW₀ : Block.Preceq T_W.erase T₀.erase)
    (hJ₀ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x (Restated.switchRound M S tE) n₀ n_W T₀)
    (hsettle : Restated.RecordsSettledAtSettleTick M S Sched x tE)
    (hadopt : ∀ tHi : Int, Restated.HonestProposalHeadsAtOwnSlot M S Sched x
      ((M.opening_slot S.hc (Restated.switchRound M S tE + 1))) tHi) :
    Restated.ConfirmedIncludedFromSlot M S Sched x ((M.opening_slot S.hc (Restated.switchRound M S tE + 1)) + 2) :=
  fun s hsl => Restated.confirmedIncluded_of_ownSlotVotes_upTo facts S Sched x tE hexec hmono htd hcatch tGAT gap
    hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear hB' hnW hAW
    hJswitch hTW₀ hJ₀ hsettle (hadopt (M.confirmation_time S.E s)) s hsl le_rfl

end

end DecoupledConsensusModel.Sts.Restated
