import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bK_ConeChain
import Proofs.Claims.Restated.Claim13bK_ConfirmedOld
import Proofs.Claims.Restated.Claim13bK_ConfirmedRecord
import Proofs.Claims.Restated.Claim13bK_ConfirmedRecordReaders
import Proofs.Claims.Restated.Claim13bK_ConfirmedWake
import Proofs.Claims.Restated.Claim13bK_FinBeforeTick
import Proofs.Claims.Restated.Claim13bK_GradeOld
import Proofs.Claims.Restated.Claim13bK_GradeOldHeads
import Proofs.Claims.Restated.Claim13bK_HeadsPersist
import Proofs.Claims.Restated.Claim13bK_LiveConfirmedSlots
import Proofs.Claims.Restated.Claim13bK_PrevHeadsStep
import Proofs.Claims.Restated.Claim13bStepAssembly
import Proofs.Claims.Restated.Claim13bStepCone
import Proofs.Claims.Restated.Claim13bStepConeIter
import Proofs.Claims.Restated.Claim13bStepGrade
import Proofs.Claims.Restated.Claim13bStepSGMove
import Proofs.Claims.Restated.Claim13bW_Schedule
import Proofs.Claims.Restated.Claim13beRoute3_3
import Proofs.Claims.Restated.Claim13beRoute3_5
import Proofs.Claims.Restated.Claim13beRoute3_82
import Proofs.Claims.Restated.ProcessIdempotent
import Proofs.Claims.Restated.Projection
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bInvariantActiveJoint
import Model.Conditions.Claim13bInvariantActiveSinceW
import Model.Conditions.Claim13bInvariantActiveTop
import Model.Conditions.Claim13bK_ConfirmedSettle
import Model.Conditions.Claim13bK_FinBeforeTick
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13bStepAssembly
import Model.Conditions.Claim13bStepCone
import Model.Conditions.Claim13bStepConeIter
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_74
import Model.Conditions.Claim13beRoute3_83
import Model.Conditions.RunAll
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Sts_Spec2Claims_Claim13bf
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring
import Proofs.Claims.Restated.Claim13bK_ConfirmedRecordReadersRecv
import Proofs.Claims.Restated.Claim13bK_PrevHeadsStepRecv

/-!
# The confirmation walk's start and the honest heads

After the phase, at every slot, a round whose joint invariant holds with an anchor the honest heads
descend from; the block an honest reader's confirmation walk starts from is an ancestor of those
heads, and the blocks between it and a common ancestor of the heads are in the walk's tree. Stated
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
local macro "pCS% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13bK_ConeSlots)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "pCO% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13bK_ConfirmedOld)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "pCR% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13bK_ConfirmedRecord)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

private theorem nat_cases_three_c (a s : Nat) (h : a ≤ s) : s = a ∨ s = a + 1 ∨ a + 2 ≤ s := by
  omega

private theorem nat_succ_le_of_not_c (a b : Nat) (h : ¬ a + 1 ≤ b) : b + 1 ≤ a + 1 := by
  omega

private theorem nat_exists_pred_c (a b : Nat) (h : a + 1 ≤ b) : ∃ r : Nat, b = r + 1 ∧ a ≤ r :=
  ⟨b - 1, by omega, by omega⟩

private theorem nat_add_two_le_c (a R : Nat) (h : 3 ≤ R) : a + 2 ≤ a + R := by
  omega

private theorem nat_add_one_le_c (a R : Nat) (h : 3 ≤ R) : a + 1 ≤ a + R := by
  omega

private theorem nat_le_succ_of_add_two_le_c (a s : Nat) (h : a + 2 ≤ s) : a ≤ s + 1 := by
  omega

private theorem nat_last_slot_c (a R s : Nat) (h3 : 3 ≤ R) (h0 : a + R ≤ s + 1)
    (h1 : ¬ a + R ≤ s) : a + 2 ≤ s ∧ a + 1 ≤ s ∧ s ≤ a + R + 1 := by
  omega

private theorem nat_add_sub_succ_c (a b : Nat) (h : a ≤ b) :
    a + (b + 1 - a) = b + 1 ∧ 0 < b + 1 - a := by
  omega

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- On the premises of `afterPhaseJointRound_of_premises`, for every slot `s` from round
    `(rW + 1)`'s opening slot on there are a round `r ≥ rW`, a tick step `n` and an anchor `T` (a
    descendant of `T_W` or `T_W` itself) such that the joint invariant holds at round `r` with them,
    `o_r ≤ s ≤ o_{r+1}`, and every honest active member of slot `s`'s committee votes there for a
    descendant of `T`. -/
theorem exists_joint_anchor_headsBelow_atSlot (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (hcatch : Restated.CatchUpOnWake M S x) (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (hsync : Restated.SynchronyFromWake M S x) (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight) (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t) (hrsW : Restated.roundSleepinessW M S Sched tE) (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT) (hcs : Restated.committeeSleepinessW M S Sched tE) (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched)) (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap) (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
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
    {s : Slot} (hs1 : (M.opening_slot S.hc (Restated.switchRound M S tE + 1)) ≤ s) :
    ∃ (r : Round) (n : Nat) (T : NamedBlock V), Restated.switchRound M S tE ≤ r ∧
      Block.Preceq T_W.erase T.erase ∧
      Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r n n_W T ∧
      (M.opening_slot S.hc r) ≤ s ∧ s ≤ (M.opening_slot S.hc (r + 1)) ∧
      Restated.HeadsBelow M S Sched x T.erase s := by
  have hρ0 := facts.gr.opening_slot_round_of_le_slot S.hc s
  have hρ1 := facts.gr.lt_opening_slot_round_of_succ S.hc s
  have hR3 := S.hc.R_ge_three
  have hρW : Restated.switchRound M S tE + 1 ≤ (M.round_of S.hc s) := by
    by_contra hcon
    have h := facts.gr.opening_slot_mono S (nat_succ_le_of_not_c _ _ hcon)
    exact absurd (lt_of_lt_of_le hρ1 h) (not_lt.mpr hs1)
  obtain ⟨r₁, hr₁, hrW1⟩ := nat_exists_pred_c _ _ hρW
  have hsucc₁ := facts.gr.opening_slot_succ S.hc r₁
  have hsucc := facts.gr.opening_slot_succ S.hc (r₁ + 1)
  rw [hr₁] at hρ0 hρ1
  rcases nat_cases_three_c _ _ hρ0 with h0 | h1 | h2
  · -- `s = o_ρ`: the round before
    obtain ⟨n, T, hJ, -, hTW⟩ := Restated.anchor_at_later_round facts S Sched x tE hexec hmono htd hcatch
      tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hrec hprev hclear hB'
      hnW hAW hJswitch le_rfl hTW₀ hJ₀ hrW1
    have hanc := Restated.anchor_ancestorOfHonestHeadsFrom facts S Sched x tE hexec hmono htd hcatch tGAT gap
      hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hrec hprev hclear hB' hnW hAW
      hJswitch hrW1 hTW hJ
    refine ⟨r₁, n, T, hrW1, hTW, hJ, ?_, ?_, hanc s ?_⟩
    · rw [h0, hsucc₁]; exact Nat.le_add_right _ _
    · rw [h0]
    · rw [h0, hsucc₁]; exact nat_add_two_le_c _ _ hR3
  · -- `s = o_ρ + 1`
    obtain ⟨e, hk0⟩ := nat_add_sub_succ_c _ _ hrW1
    obtain ⟨n_k, T_k, hJk, hWk, hk⟩ := Restated.exists_anchor_chain_secondSlot facts S Sched x tE hexec hmono
      htd hcatch tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hrec hprev
      hclear hB' hnW hAW hJswitch le_rfl hTW₀ hJ₀ (r₁ + 1 - Restated.switchRound M S tE)
    rw [e] at hJk hk
    refine ⟨r₁ + 1, n_k, T_k, Nat.le_succ_of_le hrW1, hWk, hJk, ?_, ?_, ?_⟩
    · rw [h1]; exact Nat.le_succ _
    · rw [h1, hsucc]; exact nat_add_one_le_c _ _ hR3
    · rw [h1]; exact hk hk0
  · -- `s ≥ o_ρ + 2`: the round of `s`
    obtain ⟨n, T, hJ, -, hTW⟩ := Restated.anchor_at_later_round facts S Sched x tE hexec hmono htd hcatch
      tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hrec hprev hclear hB'
      hnW hAW hJswitch le_rfl hTW₀ hJ₀ (r := r₁ + 1) (Nat.le_succ_of_le hrW1)
    have hanc := Restated.anchor_ancestorOfHonestHeadsFrom facts S Sched x tE hexec hmono htd hcatch tGAT gap
      hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hrec hprev hclear hB' hnW hAW
      hJswitch (Nat.le_succ_of_le hrW1) hTW hJ
    exact ⟨r₁ + 1, n, T, Nat.le_succ_of_le hrW1, hTW, hJ, hρ0, le_of_lt hρ1, hanc s h2⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- A member of `HonRound r` is awake from one delay before the grade-2 first cutoff of the round of
    slot `opening_slot r + 1`, which is `r`, to the confirmation instant of round `r`'s opening slot,
    which is `S.a r`. -/
theorem honRound_grade2Window_confirmation (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (r : Round) {v : V} (hv : v ∈ Restated.HonRound M S Sched r) :
    v ∈ Sched.awakeThroughout
      (M.early S.E S.hc (M.round_of S.hc (M.opening_slot S.hc r + 1)) .g2 - S.E.Δ)
      (M.confirmation_time S.E (M.opening_slot S.hc r)) := by
  have hsr : M.round_of S.hc (M.opening_slot S.hc r + 1) = r := by
    rw [← Restated.slotOf_action facts S r]; exact Restated.round_of_slotOf_action facts S r
  rw [hsr, Restated.confirmation_time_opening_slot facts S r]
  exact Restated.awakeThroughout_of_mem_honRound facts hv

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- On the premises of `afterPhaseJointRound_of_premises`, if slot `s` is at or after round
    `(rW + 1)`'s third slot and `v` is awake from one delay before the grade-2 first cutoff of the
    round of slot `s + 1` to slot `s`'s confirmation instant and honest through it, then for an
    outcome `c` of `v`'s cache update at that instant and every block `A` that `v`'s confirmation
    walk under `c`'s grade contract can start from, every honest active member of slot `s`'s
    committee votes at slot `s` for a descendant of `A`. -/
theorem confAnchor_headsBelow_atSlot (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (hcatch : Restated.CatchUpOnWake M S x) (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (hsync : Restated.SynchronyFromWake M S x) (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight) (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t) (hrsW : Restated.roundSleepinessW M S Sched tE) (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT) (hcs : Restated.committeeSleepinessW M S Sched tE) (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched)) (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap) (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
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
    {s : Slot} (hsl : (M.opening_slot S.hc (Restated.switchRound M S tE + 1)) + 2 ≤ s)
    {m : Nat} (hm : Restated.tickStepAt M x m (M.confirmation_time S.E s))
    {v : V} (hvaw2 : v ∈ Sched.awakeThroughout
      (M.early S.E S.hc (M.round_of S.hc (s + 1)) .g2 - S.E.Δ) (M.confirmation_time S.E s))
    (hvh : HonestThroughTime Sched (M.confirmation_time S.E s) v)
    (c : M.Cache) (hc : M.onPhaseTick S.E S.hc (M.toHealing (x[m][v].st).st.core)
      (M.confirmation_time S.E s) (x[m][v].st).cache ⇢ c) :
    ∀ A, Restated.Vocabulary.Protocol.confAnchorWith M (M.gradeContract c) S.E S.hc
        (Restated.confStoreAt M S (x[m][v].st) s) ⇢ A →
      Restated.HeadsBelow M S Sched x A s := by
  intro A hA
  have hvaw := Restated.slotWindow_of_grade2Window facts S Sched hvaw2
  have hd := S.E.Δ_pos
  have hd1 : (1 : Int) ≤ S.E.Δ := hd
  obtain ⟨hm1, hm0⟩ := Restated.tickStepAt_time facts x hm
  have hctc := (pCR% confirmation_time_closed_cr) facts S.E s
  have hss := slotStart_closed S.E.Δ s
  have hvm : Restated.HonestThrough M Sched x m v := fun t ht => hvh t (by linarith)
  have haw : v ∈ Sched.awake (M.confirmation_time S.E s) :=
    mem_awake_of_awakeThroughout Sched hvaw (by rw [hctc, hss]; linarith) le_rfl
  have hA' := (facts.nd.gradeContract_sgRoot_eq_frameAnchor c S.E S.hc
    (M.toHealing (Restated.confStoreAt M S (x[m][v].st) s))
    (M.round_of S.hc (Restated.confStoreAt M S (x[m][v].st) s).s) A).1 hA
  rcases facts.gr.Sts_anchor_cases S _ _ _ A hA' with hfg | ⟨root, hg1, hAroot⟩
  ·
    obtain ⟨r, n, T, hr, hTW, hJ, hs0, hs1, hT⟩ := Restated.exists_joint_anchor_headsBelow_atSlot facts S Sched x
      tE hexec hmono htd hcatch tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom
      hrec hprev hclear hB' hnW hAW hJswitch hTW₀ hJ₀ (le_trans (Nat.le_add_right _ 2) hsl)
    have hroot := Restated.confRoot_preceq_anchor_atSlot facts S Sched x tE hexec hmono htd tGAT gap hgst hlen
      hsync hthird hphase hrsW hmult hcv hcom hrec hprev hclear hB' hnW hAW hr hTW hJ hs0 hs1 hm
      hvm
    rw [hfg]
    exact Restated.headsBelow_mono facts S Sched x hroot hT
  ·
    have hslot : (Restated.confStoreAt M S (x[m][v].st) s).s = s + 1 := by
      have e : (Restated.confStoreAt M S (x[m][v].st) s).s = S.E.slotOf (M.confirmation_time S.E s) :=
        facts.hd.Sts_setClock_core_s _ _ _
      rw [e]; exact facts.sch.Optimistic_slotOf_confirmation_time S.E s
    obtain ⟨root₀, hc0, -⟩ := facts.gr.readFrame_g1_provenance _ _ _ hg1
    have hdomaw := Restated.framePhaseAwakeProvenance_onPhaseTick facts S Sched
      (M.toHealing (x[m][v].st).st.core) (x[m][v].st).cache haw
      (Restated.framePhaseAwakeProvenance_sts facts S Sched x v m) c hc _ .g1 root₀ hc0
    obtain ⟨m₁, B, hm₁, hB, hrootB⟩ := Restated.confFrame_g1_provenance facts S Sched x hm v root
      c hc hg1
    rw [hslot] at hdomaw hm₁ hB
    have hρ0 := facts.gr.opening_slot_round_of_le_slot S.hc (s + 1)
    have hρ1 := facts.gr.lt_opening_slot_round_of_succ S.hc (s + 1)
    have hρW : Restated.switchRound M S tE + 1 ≤ (M.round_of S.hc (s + 1)) := by
      by_contra hcon
      have h := facts.gr.opening_slot_mono S (nat_succ_le_of_not_c _ _ hcon)
      exact absurd (lt_of_lt_of_le hρ1 h) (not_lt.mpr (nat_le_succ_of_add_two_le_c _ _ hsl))
    obtain ⟨r₁, hr₁, hrW1⟩ := nat_exists_pred_c _ _ hρW
    rw [hr₁] at hdomaw hm₁ hB hρ0
    obtain ⟨b0, hBt⟩ := facts.gr.gradeBool_nonempty S.E (M.gradeView (M.toHealing (x[m₁][v].st).st.core))
      (x[m₁][v].st).st.core.F S.hc.η_SG (r₁ + 1) (M.early S.E S.hc (r₁ + 1) .g1)
      (M.late S.E S.hc (r₁ + 1) .g1) B
    obtain rfl := hB b0 hBt
    have hA1 := Restated.action_le_time_of_stepBefore facts S Sched x htd hm₁
    have hA2 := Restated.time_lt_domain_of_stepBefore facts S Sched x htd hm₁
    have hdom5 := facts.gr.domain_add_five_delta_le_action S (r₁ + 1) .g1
    have hρ0I : (((M.opening_slot S.hc (r₁ + 1)) : Nat) : Int) ≤ ((s : Nat) : Int) + 1 := by
      exact_mod_cast hρ0
    have hSa1 : (Restated.Vocabulary.Execution.Setup.a M S (r₁ + 1))
        = 4 * S.E.Δ * (((M.opening_slot S.hc (r₁ + 1)) : Nat) : Int) + 6 * S.E.Δ := by
      rw [← Restated.confirmation_time_opening_slot facts S (r₁ + 1), (pCR% confirmation_time_closed_cr) facts]
    have hmul := mul_le_mul_of_nonneg_left hρ0I (le_of_lt (by linarith : (0 : Int) < 4 * S.E.Δ))
    have hdomtc : M.domain S.E S.hc (r₁ + 1) .g1 ≤ M.confirmation_time S.E s := by
      rw [hctc]; linarith
    have hl0 := facts.gr.early_le_late S.E S.hc (r₁ + 1) .g0
    have hl1 := facts.gr.late_g0_add_delta_le_late_g1 S (r₁ + 1)
    have he0 := facts.gr.early_g1_add_delta_le_early_g0 S (r₁ + 1)
    have hed := facts.gr.early_g1_le_domain_g1 S (r₁ + 1)
    have hlo := facts.gr.action_delta_le_early S S.hc.R_ge_three (Nat.lt_succ_self r₁)
    have h21 := facts.gr.early_g2_add_delta_le_early_g1 S (r₁ + 1)
    have hvaw2' := hvaw2
    rw [hr₁] at hvaw2'
    have hawT : v ∈ Sched.awakeThroughout (M.early S.E S.hc (r₁ + 1) .g1 - S.E.Δ)
        (M.domain S.E S.hc (r₁ + 1) .g1) :=
      awakeThroughout_mono Sched hvaw2' (by linarith) hdomtc
    have ht₀ : M.early S.E S.hc (r₁ + 1) .g1 - S.E.Δ ≤ M.late S.E S.hc (r₁ + 1) .g1 - 1 - 2 * S.E.Δ := by
      linarith
    have haρ : Restated.Vocabulary.Execution.Setup.a M S r₁ ≤ M.early S.E S.hc (r₁ + 1) .g1 - S.E.Δ := by
      show M.a S.hc S.E.Δ r₁ ≤ _
      linarith
    have hgstρ := Restated.gst_le_action_of_switchRound_le facts S tGAT tE gap hgst hlen
      hrW1
    have hrecv : Restated.ReceivesRoundAttestationsBefore M S Sched x r₁ v
        (M.early S.E S.hc (r₁ + 1) .g1) := by
      have h := Restated.receivesRoundAttestationsBefore_of_awakeFrom facts S Sched x hsync hcatch
        (r := r₁) (t₀ := M.early S.E S.hc (r₁ + 1) .g1 - S.E.Δ) haρ (le_trans hgstρ haρ)
        (awakeThroughout_mono Sched hawT le_rfl (by linarith))
      have e : M.early S.E S.hc (r₁ + 1) .g1 - S.E.Δ + S.E.Δ = M.early S.E S.hc (r₁ + 1) .g1 := by ring
      rw [e] at h
      exact h
    have hvS : v ∉ Sched.adv (M.domain S.E S.hc (r₁ + 1) .g1) := hvh _ hdomtc
    obtain ⟨n, T, hJ, -, hTW⟩ := Restated.anchor_at_later_round facts S Sched x tE hexec hmono htd hcatch
      tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hrec hprev hclear hB'
      hnW hAW hJswitch le_rfl hTW₀ hJ₀ hrW1
    refine Restated.headsBelow_mono facts S Sched x (preceq_trans_Preceq hAroot hrootB) ?_
    by_cases hlast : (M.opening_slot S.hc (r₁ + 1)) ≤ s
    · -- `s` is in round `r₁ + 1`
      obtain ⟨n₁, T₁, hJ₁, -, -⟩ := Restated.anchor_at_later_round facts S Sched x tE hexec hmono htd hcatch
        tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hrec hprev hclear
        hB' hnW hAW hJswitch le_rfl hTW₀ hJ₀ (r := r₁ + 1) (Nat.le_succ_of_le hrW1)
      exact Restated.graded_ancestorOfHonestHeadsFrom_at_awakeReader_recv facts S Sched x tE hexec hmono htd hcatch
        tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hrec hprev hclear
        hB' hnW hAW hJswitch hrW1 hTW hJ hJ₁ _ ht₀ hawT hrecv hvS hm₁ hBt s hlast
    · -- `s` is the last slot of round `r₁`
      have hr₁pos : 0 < r₁ := Restated.round_pos_of_switch facts S tGAT tE gap hgst hlen hrW1
      obtain ⟨r₀, hr₀⟩ : ∃ r₀ : Round, r₁ = r₀ + 1 :=
        ⟨r₁ - 1, (Nat.succ_pred_eq_of_pos hr₁pos).symm⟩
      subst hr₀
      have hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r₀ + 1 + 1))) →
          Restated.StepFinalizedCrossingUnderAnchor M S Sched x (r₀ + 1) n'' T :=
        fun n'' h => Restated.stepFinalizedCrossingUnderAnchor_of_afterSwitch facts S Sched x hrW1 hnW
          hJ.toAfterPhaseInvariantOverActiveSetsSince
          (Restated.justified_preceq_anchor_ofJoint facts S Sched x tE hexec hmono htd tGAT gap hgst hlen hsync
            hthird hphase hrsW hmult hcv hcom hrec hprev hclear hB' hnW hAW hrW1 hTW hJ h)
      obtain ⟨v_1, hv_1, a, har, hai, has, C, hC, hac, hBC⟩ :=
        Restated.graded_preceq_freshSG_at_awakeReader_recv facts S Sched x tE hexec hmono htd
          hsync hmult tGAT gap hgst hlen hcv hthird hphase hrsW hcs hrW1 ((pHP% joint_toTop_hp) hJ) hcross
          (facts.gr.domain_le_action S (r₀ + 1 + 1) .g1) _ ht₀ hawT hrecv hvS hm₁ B hBt
      obtain ⟨n', hn'⟩ := Restated.tick_field_at_succ facts S Sched x htd (r₀ + 1)
      have hJT := Restated.justified_fromSecondSlot_ofJoint facts S Sched x tE hexec hmono htd tGAT gap hgst hlen
        hsync hthird hphase hrsW hmult hcv hcom hrec hprev hclear hB' hnW hAW hJswitch hrW1 hTW hJ
        hn'
      obtain ⟨n_prev, hnp0⟩ := hJ.prevTick
      have hnp : Restated.tickStepAt M x n_prev ((Restated.Vocabulary.Execution.Setup.a M S r₀)) := hnp0
      have hsucc := facts.gr.opening_slot_succ S.hc (r₀ + 1)
      rw [hsucc] at hρ0 hlast
      obtain ⟨h2, h1, h3⟩ := nat_last_slot_c _ _ _ S.hc.R_ge_three hρ0 hlast
      rcases Restated.roundSG_preceq_anchor_or_headsBelow (hrecvR := Restated.nextRoundReceipts_of_catchUp facts S Sched x hsync hcatch
        (Restated.gst_le_action_of_switchRound_le facts S tGAT tE gap hgst hlen
          (by first | assumption | exact le_trans hr (Nat.le_succ _) | exact le_trans hr (Nat.le_add_right _ _) | exact Nat.le_succ_of_le hr | omega))) facts S Sched x tE hexec hmono htd hsync hmult hcom tGAT
          gap hgst hlen hcv hthird hphase hrsW hcs hrW1 hJ hn' hcross hJT hnp v_1 hv_1 a har
          hai has C hC hac with hCT | hCh
      · have hanc := Restated.anchor_ancestorOfHonestHeadsFrom facts S Sched x tE hexec hmono htd hcatch tGAT gap
          hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hrec hprev hclear hB' hnW
          hAW hJswitch hrW1 hTW hJ
        exact Restated.headsBelow_mono facts S Sched x (preceq_trans_Preceq hBC hCT) (hanc s h2)
      · exact Restated.headsBelow_mono facts S Sched x hBC (hCh s h1 (by rw [hsucc]; exact h3))

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- On the premises of `confAnchor_headsBelow_atSlot`, if every honest active member of slot `s`'s
    committee votes at slot `s` for a descendant of `X`, then for every block `A` that `v`'s
    confirmation walk can start from, every block that is a descendant of `A`, is not `A`, and is an
    ancestor of `X` is in the tree that walk descends. -/
theorem confAnchorChainInTree_atSlot (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (hcatch : Restated.CatchUpOnWake M S x) (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (hsync : Restated.SynchronyFromWake M S x) (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight) (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t) (hrsW : Restated.roundSleepinessW M S Sched tE) (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT) (hcs : Restated.committeeSleepinessW M S Sched tE) (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched)) (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap) (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
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
    {s : Slot} (hsl : (M.opening_slot S.hc (Restated.switchRound M S tE + 1)) + 2 ≤ s)
    {m : Nat} (hm : Restated.tickStepAt M x m (M.confirmation_time S.E s))
    {v : V} (hvaw : v ∈ Sched.awakeThroughout (slotStart S.E.Δ s - S.E.Δ)
      (M.confirmation_time S.E s))
    (hvh : HonestThroughTime Sched (M.confirmation_time S.E s) v)
    {X : Block V} (hX : Restated.HeadsBelow M S Sched x X s)
    (c : M.Cache) (hc : M.onPhaseTick S.E S.hc (M.toHealing (x[m][v].st).st.core)
      (M.confirmation_time S.E s) (x[m][v].st).cache ⇢ c) :
    ∀ A, Restated.Vocabulary.Protocol.confAnchorWith M (M.gradeContract c) S.E S.hc
        (Restated.confStoreAt M S (x[m][v].st) s) ⇢ A →
    ∀ C : Block V,
      Block.Preceq A C →
      C ≠ A →
      Block.Preceq C X →
      C ∈ Restated.Vocabulary.Protocol.confTree M (Restated.confStoreAt M S (x[m][v].st) s) := by
  intro A hA C hAC _ hCX
  have hd := S.E.Δ_pos
  have hd1 : (1 : Int) ≤ S.E.Δ := hd
  obtain ⟨hm1, hm0⟩ := Restated.tickStepAt_time facts x hm
  have hctc := (pCR% confirmation_time_closed_cr) facts S.E s
  have hss := slotStart_closed S.E.Δ s
  have hspos : 0 < s := lt_of_lt_of_le Nat.zero_lt_two (le_trans (Nat.le_add_left 2 _) hsl)
  have hsc : M.support_cutoff S.E s = 4 * S.E.Δ * ((s : Nat) : Int) + 2 * S.E.Δ := by
    obtain ⟨s', hs'⟩ : ∃ s' : Slot, s = s' + 1 := ⟨s - 1, (Nat.succ_pred_eq_of_pos hspos).symm⟩
    rw [hs']
    exact ((pCW% support_cutoff_closed_cw) facts S.E).2 s'
  have hvtc : M.vote_time S.E s = 4 * S.E.Δ * ((s : Nat) : Int) + S.E.Δ := by
    have h := facts.sch.slotStart_add_delta_eq_vote_time S.E s
    rw [hss] at h
    linarith
  have hvm : Restated.HonestThrough M Sched x m v := fun t ht => hvh t (by linarith)
  obtain ⟨r, n, T, hr, hTW, hJ, hs0, hs1, hT⟩ := Restated.exists_joint_anchor_headsBelow_atSlot facts S Sched x
    tE hexec hmono htd hcatch tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom
    hrec hprev hclear hB' hnW hAW hJswitch hTW₀ hJ₀ (le_trans (Nat.le_add_right _ 2) hsl)
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
  have hhm := Restated.hMax_le_anchor_succ_before_succ_tick_of_hypotheses facts S Sched x tE hexec hmono tGAT
    gap hgst hlen hthird hphase hrsW hr hinv hn'
  have hs1I : ((s : Nat) : Int) ≤ (((M.opening_slot S.hc (r + 1)) : Nat) : Int) := by
    exact_mod_cast hs1
  have hSa1 : (Restated.Vocabulary.Execution.Setup.a M S (r + 1))
      = 4 * S.E.Δ * (((M.opening_slot S.hc (r + 1)) : Nat) : Int) + 6 * S.E.Δ := by
    rw [← Restated.confirmation_time_opening_slot facts S (r + 1), (pCR% confirmation_time_closed_cr) facts]
  have hmul1 := mul_le_mul_of_nonneg_left hs1I (le_of_lt (by linarith : (0 : Int) < 4 * S.E.Δ))
  have hmn' : m ≤ n' := Restated.le_tick_of_time_lt_action facts S Sched x hn' (by rw [hSa1]; linarith)
  have hcsW := Restated.committeeSleepinessW_at_heads_slot facts S Sched tE hmono hcom tGAT gap hgst hlen hphase
    hcs (r := Restated.switchRound M S tE + 1) (Nat.le_succ _)
  have hmaj := Restated.majority_of_committeeSleepinessW facts S Sched hcsW (s := s)
    (slotStart_mono S (Nat.le_succ_of_le hsl))
  obtain ⟨w, hwmem⟩ : ((S.E.committee s) ∩ Restated.HonSlot M S Sched s).Nonempty := by
    rw [Finset.inter_eq_right.2 (Restated.HonSlot_subset_committee facts S Sched _), ← Finset.card_pos]; omega
  have hwH := (Finset.mem_inter.mp hwmem).2
  have hspos : 0 < s := lt_of_lt_of_le Nat.zero_lt_two (le_trans (Nat.le_add_left 2 _) hsl)
  obtain ⟨mw, hmw⟩ := Restated.exists_tickStepAt facts x htd (facts.sch.vote_time_pos S hspos)
  obtain ⟨-, hmw0⟩ := Restated.tickStepAt_time facts x hmw
  rw [hvtc] at hmw0
  have hwh : Restated.HonestThrough M Sched x mw w :=
    Restated.honestThrough_of_mem_HonSlot facts S Sched x hmono hwH (by rw [hctc]; linarith)
  obtain ⟨G, hG⟩ := (pCS% gfHeadFrom_nonempty_cs) facts S (x[mw][w].st) s
  obtain ⟨D, hD, hDe⟩ := Restated.exists_named_of_mem_tree facts S Sched x mw w
    (Restated.gfHeadFrom_mem_tree facts S Sched x mw w s G hG)
  have hTD : Block.Preceq T.erase D.erase := by rw [hDe]; exact hT w mw hwH hmw G hG
  have hXD : Block.Preceq X D.erase := by rw [hDe]; exact hX w mw hwH hmw G hG
  have htGATo : tGAT ≤ M.opening S.E S.hc r :=
    le_trans (Restated.tGAT_le_switchOpening facts S tGAT tE gap hgst hlen) (Restated.switchOpening_le_opening facts S hr)
  have hs0I : (((M.opening_slot S.hc r) : Nat) : Int) ≤ ((s : Nat) : Int) := by exact_mod_cast hs0
  have hmul0 := mul_le_mul_of_nonneg_left hs0I (le_of_lt (by linarith : (0 : Int) < 4 * S.E.Δ))
  rw [(pHP% opening_eq_slotStart_hp) facts, slotStart_closed] at htGATo
  have hmwG : tGAT ≤ (x[mw].time : Int) := by linarith
  have hwaw : v ∈ Sched.awakeThroughout (M.support_cutoff S.E s - 2 * S.E.Δ)
      (M.support_cutoff S.E s) :=
    awakeThroughout_mono Sched hvaw (by rw [hsc, hss]; linarith) (by rw [hsc, hctc]; linarith)
  have hchain := fun (Y : Block V) (hY : Block.Preceq Y D.erase) =>
    Restated.chain_in_reader_tree_of_holder facts S Sched x hexec hsync hmult htd hmono (tR := (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) - 1)
      hgst hcv hphase hthird hcs (Restated.delta_le_of_healingLengthη facts S hlen) hD hwh hmwG
      (fun v_2 d hd' hv_2d => preceq_trans_Preceq
        (hfin v_2 d (Restated.le_tick_of_time_lt_action facts S Sched x hn' hd') hv_2d) hTD)
      (t := M.support_cutoff S.E s) (by rw [hsc]; linarith)
      (by rw [hsc, hSa1]; linarith) (by rw [hsc]; rw [hctc] at hm0; linarith) hvm hwaw hY
      (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›)
  obtain ⟨hCT, -⟩ := hchain C (preceq_trans_Preceq hCX hXD)
  obtain ⟨hDT, -⟩ := hchain D.erase (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _))
  have hDlog : Restated.blockInLog M S Sched x D := Restated.blockInLog_of_mem_bodies facts S Sched hwh hD
  have hDb : D ∈ (x[m][v].st).st.bodies :=
    Restated.mem_bodies_of_mem_T_honest facts S Sched x hexec hvm hDlog hDT
  have hco : Restated.Vocabulary.Proofs.NamedStore.Coherent M (Setup.alwaysAwake S).E (Setup.alwaysAwake S).cfg
      (x[m][v].st).st := (Restated.nodeInvariant_sts facts S Sched x m v).1.1.1
  have hσ : (x[m][v].st).st.core.σ D.erase = M.derive_named S.E S.cfg D :=
    hco.2.2.2.2 D hDb
  have hTDh : (M.derive_named S.E S.cfg T).h ≤ (M.derive_named S.E S.cfg D).h :=
    facts.cs.derive_height_mono S.E S.cfg
      (Restated.namedPreceq_of_blockInLog facts S Sched x hexec.idealization hinv.inPlay hDlog hTD)
  have hh : (x[m][v].st).st.core.h_max - 1 ≤ ((x[m][v].st).st.core.σ D.erase).h := by
    rw [hσ]
    exact Nat.sub_le_iff_le_add.mpr (le_trans (hhm v m hmn') (Nat.succ_le_succ hTDh))
  have hF : Block.Preceq (x[m][v].st).st.core.F C :=
    preceq_trans_Preceq (Restated.confAnchor_F_preceq facts S Sched x m v s c hc A hA) hAC
  have hroot := preceq_trans_Preceq (Restated.confAnchor_fgRoot_preceq facts S (x[m][v].st) s c hc A hA) hAC
  have eT : (Restated.confStoreAt M S (x[m][v].st) s).T = (x[m][v].st).st.core.T := facts.hd.Sts_setClock_core_T _ _ _
  have eF : (Restated.confStoreAt M S (x[m][v].st) s).F = (x[m][v].st).st.core.F := facts.hd.setClock_core_F _ _ _
  have eh : (Restated.confStoreAt M S (x[m][v].st) s).h_max = (x[m][v].st).st.core.h_max :=
    facts.hd.setClock_core_h_max _ _ _
  have eσ : (Restated.confStoreAt M S (x[m][v].st) s).σ = (x[m][v].st).st.core.σ := facts.hd.Sts_setClock_core_σ _ _ _
  refine (pCO% confTree_mem_of_parts) facts (Restated.confStoreAt M S (x[m][v].st) s) (W := D.erase) ?_ ?_ ?_
    (preceq_trans_Preceq hCX hXD) ?_ hroot
  · rw [eT]; exact hCT
  · rw [eF]; exact hF
  · rw [eT]; exact hDT
  · rw [eh, eσ]; exact hh

end

end DecoupledConsensusModel.Sts.Restated
