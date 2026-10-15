import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bInvariantActiveSince
import Proofs.Claims.Restated.Claim13bK_ConfirmedSettle
import Proofs.Claims.Restated.Claim13bK_Frame
import Proofs.Claims.Restated.Claim13bK_HeadsPersist
import Proofs.Claims.Restated.Claim13bK_LiveConfirmedSlots
import Proofs.Claims.Restated.Claim13bK_PrevHeadsStep
import Proofs.Claims.Restated.Claim13bStepConeIter
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bStepKitTick
import Proofs.Claims.Restated.Claim13bW_Schedule
import Proofs.Claims.Restated.ProcessedFlip
import Proofs.Claims.Restated.Redelivery
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bInvariantActiveJoint
import Model.Conditions.Claim13bInvariantActiveSinceW
import Model.Conditions.Claim13bK_ConfirmedRecord
import Model.Conditions.Claim13bK_ConfirmedSettle
import Model.Conditions.Claim13bK_Frame
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13bStepCone
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
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bK_ConfirmedRecord

/-!
# The confirmation records after the phase

The arithmetic of action and confirmation instants, the cases of one step on a validator's two
records, and, after the phase, the stable root, the finalized block and the two outputs as ancestors
of every honest head from some slot on. Stated over a model `M : Record.Model V` and its facts.
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

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution

/-- The opening slot of round `r` is `r * R`. -/
private theorem opening_slot_closed_cr (facts : Record.Facts M) (hc : Protocol.HealConfig)
    (r : Round) : M.opening_slot hc r = r * hc.R := by
  have h := facts.gr.opening_slot_add_mk hc 0 r
  rw [Nat.zero_add, facts.gr.opening_slot_zero_mk, Nat.zero_add] at h
  exact h

/-- The confirmation instant of slot `s` is `4 * Δ * s + 6 * Δ`. -/
private theorem confirmation_time_closed_cr (facts : Record.Facts M) (E : Env V) (s : Slot) :
    M.confirmation_time E s = 4 * E.Δ * (s : Int) + 6 * E.Δ := by
  rw [← facts.sch.slotStart_add_six_delta_eq_confirmation_time E s, slotStart_closed]

/-- The action instant of round `r` is `4 * Δ * R * r + 6 * Δ`. -/
private theorem action_closed_cr (facts : Record.Facts M) (S : Setup V) (r : Round) :
    (Restated.Vocabulary.Execution.Setup.a M S r) =
      4 * S.E.Δ * (S.hc.R : Int) * (r : Int) + 6 * S.E.Δ := by
  show M.a S.hc S.E.Δ r = _
  rw [facts.sch.a_eq_confirmation_time S.hc S.E r, confirmation_time_closed_cr facts,
    opening_slot_closed_cr facts]
  push_cast
  ring

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- If `S.a 0 ≤ t`, some round `r` has `S.a r ≤ t < S.a (r + 1)`. -/
theorem exists_action_round (facts : Record.Facts M) (S : Setup V) {t : Int} (ht : (Restated.Vocabulary.Execution.Setup.a M S 0) ≤ t) :
    ∃ r : Round, (Restated.Vocabulary.Execution.Setup.a M S r) ≤ t ∧ t < (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) := by
  have key : ∀ j : Nat, ∀ r : Round, (Restated.Vocabulary.Execution.Setup.a M S r) ≤ t → t < (Restated.Vocabulary.Execution.Setup.a M S (r + j)) →
      ∃ r' : Round, (Restated.Vocabulary.Execution.Setup.a M S r') ≤ t ∧ t < (Restated.Vocabulary.Execution.Setup.a M S (r' + 1)) := by
    intro j
    induction j with
    | zero => intro r h0 h1; simp only [Nat.add_zero] at h1; linarith
    | succ j ih =>
      intro r h0 h1
      by_cases h : t < (Restated.Vocabulary.Execution.Setup.a M S (r + 1))
      · exact ⟨r, h0, h⟩
      · exact ih (r + 1) (not_lt.mp h) (by rw [show r + 1 + j = r + (j + 1) by ring]; exact h1)
  have hd := S.E.Δ_pos
  have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  refine key t.toNat 0 ht ?_
  rw [action_closed_cr facts]
  have hnn : (0 : Int) ≤ t := le_trans (le_of_lt (Restated.action_pos facts S 0)) ht
  have e : ((0 + t.toNat : Nat) : Int) = t := by simp [Int.toNat_of_nonneg hnn]
  rw [e]
  have h1 : (1 : Int) ≤ 4 * S.E.Δ * (S.hc.R : Int) := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right h1 hnn]

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- If `0 < r_b` and slot `s`'s confirmation instant is after `S.a r_b`, then, with `r'` the round
    of `s + 1`: `s` is after round `r_b`'s opening slot, `r_b ≤ r'`, `S.a (r_b − 1)` is at or before
    one delay before slot `s`'s start, `S.a (r' − 1)` is before the confirmation instant, and
    `S.a r'` is at most four delays after it. -/
theorem confirmation_tick_arith (facts : Record.Facts M) (S : Setup V) {r_b : Round} (hrb0 : 0 < r_b) {s : Slot}
    (h : (Restated.Vocabulary.Execution.Setup.a M S r_b) < M.confirmation_time S.E s) :
    (M.opening_slot S.hc r_b) + 1 ≤ s ∧ r_b ≤ (M.round_of S.hc (s + 1)) ∧
      (Restated.Vocabulary.Execution.Setup.a M S (r_b - 1)) ≤ slotStart S.E.Δ s - S.E.Δ ∧
      (Restated.Vocabulary.Execution.Setup.a M S ((M.round_of S.hc (s + 1)) - 1)) < M.confirmation_time S.E s ∧
      (Restated.Vocabulary.Execution.Setup.a M S ((M.round_of S.hc (s + 1)))) ≤ M.confirmation_time S.E s + 4 * S.E.Δ := by
  have hd := S.E.Δ_pos
  have hR3 : 3 ≤ S.hc.R := S.hc.R_ge_three
  have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast hR3
  rw [confirmation_time_closed_cr facts, action_closed_cr facts] at h
  have hI : (r_b : Int) * (S.hc.R : Int) < (s : Int) := by
    have h' : 4 * S.E.Δ * ((r_b : Int) * (S.hc.R : Int)) < 4 * S.E.Δ * (s : Int) := by
      nlinarith
    exact lt_of_mul_lt_mul_left h' (by linarith)
  have h1 : r_b * S.hc.R < s := by exact_mod_cast hI
  have hlo := facts.gr.opening_slot_round_of_le_slot S.hc (s + 1)
  have hhi := facts.gr.lt_opening_slot_round_of_succ S.hc (s + 1)
  rw [opening_slot_closed_cr facts] at hlo hhi
  have hrb : r_b ≤ (M.round_of S.hc (s + 1)) := nat_round_arith_c3 h1 hhi
  have hr'0 : 0 < (M.round_of S.hc (s + 1)) := lt_of_lt_of_le hrb0 hrb
  have hloI : (((M.round_of S.hc (s + 1)) : Nat) : Int) * (S.hc.R : Int) ≤ (s : Int) + 1 := by
    exact_mod_cast hlo
  have hsub : ∀ n : Nat, 0 < n → ((n - 1 : Nat) : Int) = (n : Int) - 1 := fun n hn => by
    push_cast [Nat.cast_sub hn]; ring
  refine ⟨by rw [opening_slot_closed_cr facts]; exact h1, hrb, ?_, ?_, ?_⟩
  · rw [action_closed_cr facts, slotStart_closed, hsub r_b hrb0]
    have hp1 : 0 ≤ S.E.Δ * ((s : Int) - 1 - (r_b : Int) * (S.hc.R : Int)) :=
      mul_nonneg (le_of_lt hd) (by linarith)
    have hp2 : 0 ≤ S.E.Δ * ((S.hc.R : Int) - 3) := mul_nonneg (le_of_lt hd) (by linarith)
    nlinarith
  · rw [action_closed_cr facts, confirmation_time_closed_cr facts, hsub _ hr'0]
    have hp1 : 0 ≤ S.E.Δ * ((s : Int) + 1 -
        (((M.round_of S.hc (s + 1)) : Nat) : Int) * (S.hc.R : Int)) :=
      mul_nonneg (le_of_lt hd) (by linarith)
    have hp2 : 0 ≤ S.E.Δ * ((S.hc.R : Int) - 3) := mul_nonneg (le_of_lt hd) (by linarith)
    nlinarith
  · rw [action_closed_cr facts, confirmation_time_closed_cr facts]
    have hp1 : 0 ≤ S.E.Δ * ((s : Int) + 1 -
        (((M.round_of S.hc (s + 1)) : Nat) : Int) * (S.hc.R : Int)) :=
      mul_nonneg (le_of_lt hd) (by linarith)
    nlinarith

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- After step `k`, validator `v` holds the `latest_stable` and `latest_confirmed` it held before,
    or step `k` is the tick at some slot's confirmation instant and `v` is awake and not held by the
    adversary there. -/
theorem records_succ_cases (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) (k : Nat) :
    ((x[k + 1][v].st).st.core.latest_stable = (x[k][v].st).st.core.latest_stable ∧
      (x[k + 1][v].st).st.core.latest_confirmed = (x[k][v].st).st.core.latest_confirmed) ∨
    ∃ s : Slot, Restated.tickStepAt M x k (M.confirmation_time S.E s) ∧
      v ∈ Sched.awake (M.confirmation_time S.E s) \
        Sched.adv (M.confirmation_time S.E s) := by
  cases hl : x.lbl k with
  | tickAllAwake τ =>
      rcases Restated.st_succ_of_tick facts S Sched x v hl with ⟨hvaw, -, out, hout, hst⟩ | hst
      · by_cases hb : 0 < S.E.slotOf (τ : Int) ∧
            (τ : Int) = M.support_cutoff S.E (S.E.slotOf (τ : Int))
        · right
          obtain ⟨hpos, hτ⟩ := hb
          refine ⟨S.E.slotOf (τ : Int) - 1, ?_, ?_⟩
          · refine ⟨τ, hl, ?_⟩
            rw [facts.sch.confirmation_time_eq_support_cutoff_succ, Nat.sub_add_cancel hpos]
            exact hτ
          · rw [facts.sch.confirmation_time_eq_support_cutoff_succ, Nat.sub_add_cancel hpos, ← hτ]
            exact hvaw
        · left
          rw [hst, ← Record.wakeStage_st facts Sched (τ : Int) x[k] v]
          exact ⟨facts.nd.on_tick_emit_stable_of_ne (Setup.alwaysAwake S) v _ _ hb out hout,
            facts.nd.on_tick_emit_latest_of_ne (Setup.alwaysAwake S) v _ _ hb out hout⟩
      · left; rw [hst, Record.wakeStage_st facts]; exact ⟨rfl, rfl⟩
  | deliver p m =>
      left
      by_cases hp : p = v
      · subst hp
        rcases Restated.st_succ_of_deliver facts S Sched x hl with hpr | ⟨-, heq⟩
        · exact ⟨facts.nd.node_process_stable _ _ _ _ hpr,
            facts.nd.node_process_latest _ _ _ _ hpr⟩
        · rw [heq]; exact ⟨rfl, rfl⟩
      · rw [Restated.getElem_succ_of_deliver_ne facts S Sched x hl hp]; exact ⟨rfl, rfl⟩
  | custom _ ev => exact ev.elim
  | adversarial p m =>
      left; rw [Restated.getElem_succ_of_adversarial facts S Sched x hl]; exact ⟨rfl, rfl⟩
  | forward p m =>
      left; rw [Restated.getElem_succ_of_forward facts S Sched x hl]; exact ⟨rfl, rfl⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- Under `WakesAtActionInstants`, if `v` is awake from `S.a r` to `e`, then for some round
    `r_w ≤ r`, `v` is awake from `S.a r_w` to `e`, and either `r_w ≤ r_cap` or `v` is asleep at the
    instant before `S.a r_w`. -/
theorem awake_stretch_start (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (hw : Restated.WakesAtActionInstants M S Sched) {v : V} {e : Int} (r_cap : Round) :
    ∀ r : Round, v ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S r)) e →
      ∃ r_w : Round, r_w ≤ r ∧ v ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S r_w)) e ∧
        (r_w ≤ r_cap ∨ v ∉ Sched.awake ((Restated.Vocabulary.Execution.Setup.a M S r_w) - 1)) := by
  intro r
  induction r with
  | zero => intro h; exact ⟨0, le_rfl, h, Or.inl (Nat.zero_le _)⟩
  | succ r ih =>
    intro h
    by_cases h1 : r + 1 ≤ r_cap
    · exact ⟨r + 1, le_rfl, h, Or.inl h1⟩
    by_cases h2 : v ∈ Sched.awake ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)) - 1)
    · have hstep : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) - 1 := by
        have hd := S.E.Δ_pos
        have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
        rw [facts.gr.action_succ_eq_add_rounds]
        have h4 : (1 : Int) ≤ 4 * (S.hc.R : Int) * S.E.Δ := by nlinarith
        linarith
      have hback : v ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S r)) e := by
        refine mem_awakeThroughout_of_forall Sched ?_
        intro t h0 h1'
        by_cases ht : (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) ≤ t
        · exact mem_awake_of_awakeThroughout Sched h ht h1'
        · exact Restated.awake_since_action facts S Sched hw hstep (by linarith) h2 t h0 (by linarith)
      obtain ⟨r_w, hle, hW, hd⟩ := ih hback
      exact ⟨r_w, Nat.le_succ_of_le hle, hW, hd⟩
    · exact ⟨r + 1, le_rfl, h, Or.inr h2⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- An action instant `S.a r` is never a slot's Goldfish vote instant `slotStart s + Δ`. -/
theorem action_ne_vote_instant (facts : Record.Facts M) (S : Setup V) (r : Round) (s : Slot) :
    (Restated.Vocabulary.Execution.Setup.a M S r) ≠ slotStart S.E.Δ s + S.E.Δ := by
  intro heq
  have hd := S.E.Δ_pos
  rw [action_closed_cr facts, slotStart_closed] at heq
  have h0 : S.E.Δ * (4 * ((S.hc.R : Int) * (r : Int) - (s : Int)) + 5) = 0 := by
    linear_combination heq
  rcases mul_eq_zero.1 h0 with h | h
  · linarith
  · obtain ⟨A, hA⟩ : ∃ A : Int, 4 * A + 5 = 0 := ⟨_, h⟩
    omega

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- Under its premises on the execution and the phase ending at `tE`, if the joint invariant holds
    at a round `r₀` at or after the switch round with an anchor `T₀` that is `T_W` or a descendant
    of it, then at every round `r ≥ r₀` it holds with some tick step and some anchor that is a
    descendant of both `T₀` and `T_W`. -/
theorem anchor_at_later_round (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (hcatch : Restated.CatchUpOnWake M S x) (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (hsync : Restated.SynchronyFromWake M S x) (hthird : ∀ t : Int, t ≤ tE →
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
    {r₀ : Round} {n₀ : Nat} {T₀ : NamedBlock V}
    (hr₀ : Restated.switchRound M S tE ≤ r₀) (hTW₀ : Block.Preceq T_W.erase T₀.erase)
    (hJ₀ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r₀ n₀ n_W T₀)
    {r : Round} (hr : r₀ ≤ r) :
    ∃ (n : Nat) (T : NamedBlock V),
      Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r n n_W T ∧
        Block.Preceq T₀.erase T.erase ∧ Block.Preceq T_W.erase T.erase := by
  obtain ⟨n, T, hJ, h1, h2⟩ := Restated.exists_anchor_chain facts S Sched x tE hexec hmono htd hcatch
    tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear hB'
    hnW hAW hJswitch hr₀ hTW₀ hJ₀ (r - r₀)
  rw [Nat.add_sub_cancel' hr] at hJ
  exact ⟨n, T, hJ, h1, h2⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- Under its premises on the execution and the phase ending at `tE`, with the joint invariant at a
    round `r₀` at or after the switch round for an anchor that is `T_W` or a descendant of it: if
    slot `s` is at least two after round `r₀`'s opening slot, `m` is the tick step at slot `s`'s
    confirmation instant, `v` is in `HonRound` of the round of `s + 1` and honest through that
    instant, `c` is an outcome of `v`'s phase tick there, and `some G` is an outcome of the stable
    root of `c`'s grade contract at the clock-stamped store's round, then `G` is an ancestor of
    every honest head from slot `s + 3` on. -/
theorem stableRoot_ancestorOfHonestHeadsFrom (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (hcatch : Restated.CatchUpOnWake M S x) (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (hsync : Restated.SynchronyFromWake M S x) (hthird : ∀ t : Int, t ≤ tE →
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
    {r₀ : Round} {n₀ : Nat} {T₀ : NamedBlock V}
    (hr₀ : Restated.switchRound M S tE ≤ r₀) (hTW₀ : Block.Preceq T_W.erase T₀.erase)
    (hJ₀ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r₀ n₀ n_W T₀)
    {s : Slot} (hs0 : (M.opening_slot S.hc r₀) + 2 ≤ s)
    {m : Nat} (hm : Restated.tickStepAt M x m (M.confirmation_time S.E s)) {v : V}
    (hvR : v ∈ Restated.HonRound M S Sched ((M.round_of S.hc (s + 1))))
    (hvh : HonestThroughTime Sched (M.confirmation_time S.E s) v)
    {G : Block V} {c : M.Cache}
    (hc : M.onPhaseTick S.E S.hc (M.toHealing (x[m][v].st).st.core)
        (M.confirmation_time S.E s) (x[m][v].st).cache ⇢ c)
    (hG : (M.gradeContract c).stableRoot S.E S.hc
          (M.toHealing (M.ns_setClock S.E (x[m][v].st).st
            (M.confirmation_time S.E s)).core)
          ((M.round_of S.hc) (M.ns_setClock S.E (x[m][v].st).st
            (M.confirmation_time S.E s)).core.s) ⇢ some G) :
    Restated.AncestorOfHonestHeadsFrom M S Sched x G (s + 3) := by
  have hslot : (M.ns_setClock S.E (x[m][v].st).st
      (M.confirmation_time S.E s)).core.s = s + 1 := by
    rw [facts.hd.Sts_setClock_core_s]; exact facts.sch.Optimistic_slotOf_confirmation_time S.E s
  have hG := (facts.nd.gradeContract_stableRoot _ _ _ _ _ _).1 hG
  rw [hslot] at hG
  rcases facts.gr.frameStableRoot_cases _ _ _ _ _ _ hG rfl with hroot | ⟨root, hg2, hGroot⟩
  · -- the fork-choice root
    obtain ⟨hm1, hm0⟩ := Restated.tickStepAt_time facts x hm
    have hvm : Restated.HonestThrough M Sched x m v := fun t ht => hvh t (by linarith)
    have hrs0 := facts.gr.opening_slot_round_of_le_slot S.hc s
    have hrs1 := facts.gr.lt_opening_slot_round_of_succ S.hc s
    have hrr : r₀ ≤ (M.round_of S.hc s) := by
      by_contra hcon
      exact nat_lt_absurd_c3 hs0 hrs1
        (facts.gr.opening_slot_mono S (Nat.succ_le_of_lt (Nat.lt_of_not_le hcon)))
    obtain ⟨n, T, hJ, -, hTW⟩ := Restated.anchor_at_later_round facts S Sched x tE hexec hmono htd hcatch
      tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear hB'
      hnW hAW hJswitch hr₀ hTW₀ hJ₀ hrr
    have hr : Restated.switchRound M S tE ≤ (M.round_of S.hc s) := le_trans hr₀ hrr
    have hroot' : Block.Preceq (Restated.Vocabulary.Protocol.confRoot M (Restated.confStoreAt M S (x[m][v].st) s)) T.erase :=
      Restated.confRoot_preceq_anchor_atSlot facts S Sched x tE hexec hmono htd tGAT gap hgst hlen hsync hthird
        hphase hrsW hmult hcv hcom hrec hprev hclear hB' hnW hAW hr hTW hJ hrs0
        (Nat.le_of_lt hrs1) hm hvm
    have hGT : Block.Preceq G T.erase := by rw [hroot]; exact hroot'
    have hanc := Restated.anchor_ancestorOfHonestHeadsFrom facts S Sched x tE hexec hmono htd hcatch tGAT gap
      hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear hB' hnW hAW
      hJswitch hr hTW hJ
    exact Restated.ancestorOfHonestHeadsFrom_mono facts S Sched x (nat_le_add3_c3 hrs0)
      (Restated.ancestorOfHonestHeadsFrom_of_preceq facts S Sched x hGT hanc)
  · -- an ancestor of the grade-2 entry of the round's frame
    obtain ⟨root₀, hc0, hroot0⟩ := facts.gr.readFrame_g2_provenance _ _ _ hg2
    have hprov := Restated.framePhaseProvenance_onPhaseTick facts S hm
      (Restated.framePhaseProvenance_sts facts S Sched x v m) c hc
    obtain ⟨m', B, hm', hB, hroot0B⟩ := hprov _ .g2 root₀ hc0
    have hrs0 := facts.gr.opening_slot_round_of_le_slot S.hc (s + 1)
    have hrs1 := facts.gr.lt_opening_slot_round_of_succ S.hc (s + 1)
    have hrr : r₀ ≤ (M.round_of S.hc (s + 1)) := by
      by_contra hcon
      exact nat_lt_absurd_c3 (Nat.le_succ_of_le hs0) hrs1
        (facts.gr.opening_slot_mono S (Nat.succ_le_of_lt (Nat.lt_of_not_le hcon)))
    have hpos : 0 < (M.round_of S.hc (s + 1)) :=
      lt_of_lt_of_le (Restated.round_pos_of_switch facts S tGAT tE gap hgst hlen hr₀) hrr
    obtain ⟨r₁, hr₁⟩ : ∃ r₁ : Round, (M.round_of S.hc (s + 1)) = r₁ + 1 :=
      ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
    rw [hr₁] at hvR hB hm' hrr hrs0
    obtain ⟨n, T, hJ, -, hTW⟩ := Restated.anchor_at_later_round facts S Sched x tE hexec hmono htd hcatch
      tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear hB'
      hnW hAW hJswitch hr₀ hTW₀ hJ₀ hrr
    obtain ⟨b, hb⟩ := facts.gr.gradeBool_nonempty S.E
      (M.gradeView (M.toHealing (x[m'][v].st).st.core)) (x[m'][v].st).st.core.F S.hc.η_SG
      (r₁ + 1) (M.early S.E S.hc (r₁ + 1) .g2) (M.late S.E S.hc (r₁ + 1) .g2) B
    have hBt : M.gradeBool S.E (M.gradeView (M.toHealing (x[m'][v].st).st.core))
        (x[m'][v].st).st.core.F S.hc.η_SG (r₁ + 1) (M.early S.E S.hc (r₁ + 1) .g2)
        (M.late S.E S.hc (r₁ + 1) .g2) B ⇢ true := hB b hb ▸ hb
    have hBP := Restated.graded_ancestorOfHonestHeadsFrom facts S Sched x tE hexec hmono htd hcatch tGAT gap
      hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear hB' hnW hAW
      hJswitch (le_trans hr₀ hrr) hTW hJ hvR .g2 (facts.gr.domain_le_action S _ _) hm' hBt
    exact Restated.ancestorOfHonestHeadsFrom_mono facts S Sched x (Nat.add_le_add_right hrs0 2)
      (Restated.ancestorOfHonestHeadsFrom_of_preceq facts S Sched x
        (preceq_trans_Preceq hGroot (preceq_trans_Preceq hroot0 hroot0B)) hBP)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- Under its premises on the execution and the phase ending at `tE`, with the joint invariant at a
    round `r₀` at or after the switch round for an anchor that is `T_W` or a descendant of it: if
    step `k`'s time is at or after `S.a r₀` and `v` is honest through step `k`, then `v`'s finalized
    block after `k` steps is an ancestor of every honest head from slot `slot(x[k].time) + 2` on. -/
theorem finalized_ancestorOfHonestHeadsFrom (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (hcatch : Restated.CatchUpOnWake M S x) (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (hsync : Restated.SynchronyFromWake M S x) (hthird : ∀ t : Int, t ≤ tE →
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
    {r₀ : Round} {n₀ : Nat} {T₀ : NamedBlock V}
    (hr₀ : Restated.switchRound M S tE ≤ r₀) (hTW₀ : Block.Preceq T_W.erase T₀.erase)
    (hJ₀ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r₀ n₀ n_W T₀)
    {k : Nat} (hk : (Restated.Vocabulary.Execution.Setup.a M S r₀) ≤ (x[k].time : Int)) {v : V} (hvk : Restated.HonestThrough M Sched x k v) :
    Restated.AncestorOfHonestHeadsFrom M S Sched x (x[k][v].st).st.core.F
      (S.E.slotOf (x[k].time : Int) + 2) := by
  obtain ⟨r, har, hra⟩ := Restated.exists_action_round facts S (le_trans (Restated.action_mono facts S (Nat.zero_le r₀)) hk)
  have hrr : r₀ ≤ r := Nat.le_of_lt_succ (Restated.round_lt_of_action_lt facts S (lt_of_le_of_lt hk hra))
  obtain ⟨n, T, hJ, -, hTW⟩ := Restated.anchor_at_later_round facts S Sched x tE hexec hmono htd hcatch
    tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear hB'
    hnW hAW hJswitch hr₀ hTW₀ hJ₀ hrr
  have hr : Restated.switchRound M S tE ≤ r := le_trans hr₀ hrr
  obtain ⟨n', hn'⟩ := Restated.tick_field_at_succ facts S Sched x htd r
  have hkn' : k ≤ n' + 1 := by
    by_contra hcon
    have h1 := Restated.time_mono_int facts S Sched x (Nat.le_of_lt (Nat.lt_of_not_le hcon))
    rw [(Restated.tickStepAt_time facts x hn').1] at h1
    linarith
  have hWk : n_W ≤ k := by
    by_contra hcon
    have h1 := Restated.time_mono_int facts S Sched x (Nat.le_of_lt (Nat.lt_of_not_le hcon))
    have h2 := (Restated.tickStepAt_time facts x hnW).2
    have h3 := Restated.action_mono facts S hr₀
    linarith
  have hJT := Restated.justified_preceq_anchor_ofJoint facts S Sched x tE hexec hmono htd tGAT gap hgst hlen
    hsync hthird hphase hrsW hmult hcv hcom hrec hprev hclear hB' hnW hAW hr hTW hJ hn' v k hWk
    hkn' hvk
  have hanc := Restated.anchor_ancestorOfHonestHeadsFrom facts S Sched x tE hexec hmono htd hcatch tGAT gap
    hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear hB' hnW hAW
    hJswitch hr hTW hJ
  have hsl : (M.opening_slot S.hc r) + 1 ≤ S.E.slotOf (x[k].time : Int) := by
    rw [← Restated.slotOf_action facts S r]; exact slotOf_mono_sts S har
  exact Restated.ancestorOfHonestHeadsFrom_mono facts S Sched x (Nat.le_succ_of_le (Nat.add_le_add_right hsl 1))
    (Restated.ancestorOfHonestHeadsFrom_of_preceq facts S Sched x
      (preceq_trans_Preceq (Restated.finalized_preceq_justified_sts facts S Sched x k v) hJT) hanc)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- Under its premises on the execution and the phase ending at `tE`, with the joint invariant at a
    round `r₀` at or after the switch round for an anchor that is `T_W` or a descendant of it: if
    step `k`'s time is at or after `S.a r₀`, `v` is honest through step `k`, and `v`'s two records
    after `k` steps satisfy `RecordsAncestorOfHonestHeads`, then `v`'s `get_stable` and
    `get_confirmed` after `k` steps are ancestors of every honest head from slot
    `slot(x[k].time) + 2` on. -/
theorem outputs_ancestorOfHonestHeads_of_records (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (hcatch : Restated.CatchUpOnWake M S x) (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (hsync : Restated.SynchronyFromWake M S x) (hthird : ∀ t : Int, t ≤ tE →
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
    {r₀ : Round} {n₀ : Nat} {T₀ : NamedBlock V}
    (hr₀ : Restated.switchRound M S tE ≤ r₀) (hTW₀ : Block.Preceq T_W.erase T₀.erase)
    (hJ₀ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r₀ n₀ n_W T₀)
    {k : Nat} (hk : (Restated.Vocabulary.Execution.Setup.a M S r₀) ≤ (x[k].time : Int)) {v : V} (hvk : Restated.HonestThrough M Sched x k v)
    (hrecs : Restated.RecordsAncestorOfHonestHeads M S Sched x v k) :
    Restated.AncestorOfHonestHeadsFrom M S Sched x (M.get_stable (x[k][v].st).st.core)
        (S.E.slotOf (x[k].time : Int) + 2) ∧
      Restated.AncestorOfHonestHeadsFrom M S Sched x (M.get_confirmed (x[k][v].st).st.core)
        (S.E.slotOf (x[k].time : Int) + 2) := by
  have hF := Restated.finalized_ancestorOfHonestHeadsFrom facts S Sched x tE hexec hmono htd hcatch tGAT gap
    hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear hB' hnW hAW
    hJswitch hr₀ hTW₀ hJ₀ hk hvk
  have hS := Restated.ancestorOfHonestHeadsFrom_get_stable facts S Sched x _ hrecs.1 hF
  exact ⟨hS, Restated.ancestorOfHonestHeadsFrom_get_confirmed facts S Sched x _ hS (fun _ => hrecs.2)⟩

end

end DecoupledConsensusModel.Sts.Restated
