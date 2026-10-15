import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bKit
import Proofs.Claims.Restated.Vocabulary_Internal_Legacy_Instance
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13bStepAssembly
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Statements_Instantiation_RoundTimes
import Model.Record.Wiring

/-!
# Round sleepiness from the switch round on

Action instants and the switch round's place after `tGAT`, and the theorem that the round-level
sleepiness premise holds from the switch round's opening on; stated over a model
`M : Record.Model V`.
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

/-- Round `r + 1`'s action instant is round `r`'s plus `4 * S.hc.R * S.E.Δ`. -/
theorem actionInstant_succ_eq (facts : Record.Facts M) (S : Setup V) (r : Round) :
    Restated.Vocabulary.Execution.Setup.a M S (r + 1)
      = Restated.Vocabulary.Execution.Setup.a M S r + 4 * (S.hc.R : Int) * S.E.Δ :=
  facts.gr.action_succ_eq_add_rounds S r

/-- If `r ≤ r'`, round `r`'s action instant is at or before round `r'`'s. -/
theorem actionInstant_mono (facts : Record.Facts M) (S : Setup V) {r r' : Round} (h : r ≤ r') : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (Restated.Vocabulary.Execution.Setup.a M S r') := by
  induction h with
  | refl => exact le_refl _
  | step _ ih =>
    rw [Restated.actionInstant_succ_eq facts]
    have hd := S.E.Δ_pos
    have hR : (0 : Int) ≤ (S.hc.R : Int) := Int.natCast_nonneg _
    have : (0 : Int) ≤ 4 * (S.hc.R : Int) * S.E.Δ := by positivity
    linarith

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

private theorem one_le_startup_nat (a b gap : Nat) : 1 ≤ 1 + a * b + 3 * b + gap + 5 := by
  omega

private theorem add_three_le_of_target_nat (r Fs Fd gap η sw : Nat) (hFs : 1 ≤ Fs)
    (h : r + Fs + Fd + gap + 2 + η ≤ sw) : r + 3 ≤ sw := by
  omega

private theorem window_indices_nat (r r₀ sw : Nat) (h3 : r + 3 ≤ sw) (hr₀ : sw ≤ r₀) :
    r + 1 ≤ r₀ - 2 ∧ r₀ - 2 + 1 = r₀ - 1 := by
  omega

/-- If `t_GST ≤ tGAT` and `tGAT + healingLengthη M S gap ≤ tE`, the round at `tGAT` plus three is at
    or before the switch round. -/
theorem roundAt_add_three_le_switchRound (facts : Record.Facts M) (S : Setup V) (tGAT tE : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) :
    Restated.Vocabulary.Statements.Instantiation.roundAt M S tGAT + 3 ≤ Restated.switchRound M S tE := by
  have hsw := Restated.switchRound_ge_of_healingLengthη facts S tGAT tE gap hgst hlen
  have hFs : 1 ≤ Statements.Instantiation.finalityStartup S gap S.extraRounds := by
    unfold Statements.Instantiation.finalityStartup
    exact one_le_startup_nat _ _ _
  exact add_three_le_of_target_nat _ _ _ _ _ _ hFs hsw

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If `t_GST ≤ tGAT`, `tGAT + healingLengthη M S gap ≤ tE` and round `r₀` is at or after the switch
    round, then `tGAT` is at or before the left end of the window of
    `activeRoundW S Sched (r₀ - 1)`. -/
theorem tGAT_le_attesterWindow_left (facts : Record.Facts M) (S : Setup V) (tGAT tE : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) {r₀ : Round}
    (hr₀ : Restated.switchRound M S tE ≤ r₀) :
    tGAT ≤ (Restated.Vocabulary.Execution.Setup.a M S (r₀ - 1)) - wAttest S := by
  have h3 := Restated.roundAt_add_three_le_switchRound facts S tGAT tE gap hgst hlen
  have hspec := Restated.Vocabulary.Statements.roundAt_spec facts S tGAT
  obtain ⟨hle, hidx⟩ := window_indices_nat _ _ _ h3 hr₀
  have hmono : (Restated.Vocabulary.Execution.Setup.a M S (Restated.Vocabulary.Statements.Instantiation.roundAt M S tGAT + 1)) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r₀ - 2)) :=
    Restated.actionInstant_mono facts S hle
  have hstep1 := Restated.actionInstant_succ_eq facts S (Restated.Vocabulary.Statements.Instantiation.roundAt M S tGAT)
  have hstep2 := Restated.actionInstant_succ_eq facts S (r₀ - 2)
  rw [hidx] at hstep2
  have hw := twelve_delta_le_wAttest S
  have hd := S.E.Δ_pos
  simp only [wAttest] at hw ⊢
  have hd1 : (1 : Int) ≤ S.E.Δ := by simpa using Int.add_one_le_of_lt hd
  have hX : 1 ≤ 4 * (S.hc.R : Int) * S.E.Δ := by linarith
  calc tGAT ≤ (Restated.Vocabulary.Execution.Setup.a M S (Restated.Vocabulary.Statements.Instantiation.roundAt M S tGAT)) := hspec
    _ ≤ (Restated.Vocabulary.Execution.Setup.a M S (r₀ - 2)) - 4 * (S.hc.R : Int) * S.E.Δ := by linarith
    _ ≤ (Restated.Vocabulary.Execution.Setup.a M S (r₀ - 1)) - 4 * (S.hc.R : Int) * S.E.Δ := by rw [hstep2]; linarith

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- `roundSleepinessW` holds at every round from the switch round's opening on, given
    `t_GST ≤ tGAT`, the healing length, monotone corruption, the adversary under a third of the
    weight up to `tE`, every validator not held by the adversary awake in `[tGAT, tE]`, and
    `roundSleepinessW S Sched tE`. -/
theorem roundSleepinessW_switchOpening_of_phase (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (tGAT tE : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hmono : Sched.MonotoneCorruption)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE) :
    Restated.roundSleepinessW M S Sched (Restated.switchOpening M S tE) := by
  classical
  intro r₀ hr₀ hanchor
  by_cases hlate : tE ≤ M.opening S.E S.hc r₀
  · exact hrsW r₀ hr₀ hlate
  rw [not_le] at hlate
  have hd := S.E.Δ_pos
  -- the round `r₀` is at or after the switch round
  have hsw : Restated.switchRound M S tE ≤ r₀ := by
    by_contra hlt
    rw [not_le] at hlt
    have h1 : M.opening S.E S.hc (r₀ + 1) ≤ Restated.switchOpening M S tE :=
      facts.gr.Sts_opening_mono S hlt
    -- round `r₀`'s opening is `8Δ` or more before round `r₀ + 1`'s
    have h2 := facts.gr.opening_add_le_of_lt S (Nat.lt_succ_self r₀)
    have h3 : Restated.switchOpening M S tE ≤ M.opening S.E S.hc r₀ := hanchor
    linarith
  set Adv := Sched.adv (M.opening S.E S.hc (r₀ + 1)) with hAdv
  -- every validator outside `Adv` is active at round `r₀ - 1`
  have hleft := Restated.tGAT_le_attesterWindow_left facts S tGAT tE gap hgst hlen hsw
  have hright : (Restated.Vocabulary.Execution.Setup.a M S (r₀ - 1)) ≤ M.opening S.E S.hc r₀ := by
    -- one delay after round `r₀ - 1`'s action is at or before round `r₀`'s G2 early cutoff, which
    -- is at or before its opening
    have h1 := facts.gr.action_delta_le_early S S.hc.R_ge_three (show r₀ - 1 < r₀ by omega)
    have h2 := facts.gr.early_g2_le_opening S r₀
    show M.a S.hc S.E.Δ (r₀ - 1) ≤ _
    linarith
  have hopen : M.opening S.E S.hc r₀ ≤ M.opening S.E S.hc (r₀ + 1) :=
    facts.gr.Sts_opening_mono S (Nat.le_succ r₀)
  have hactive : ∀ v : V, v ∉ Adv → v ∈ Restated.activeRoundW M S Sched (r₀ - 1) := by
    intro v hv
    simp only [Restated.activeRoundW]
    refine mem_awakeThroughout_of_forall Sched ?_
    intro t ht0 ht1
    have ht1' : t ≤ (Restated.Vocabulary.Execution.Setup.a M S (r₀ - 1)) := ht1
    refine hphase t (by linarith) (by linarith) v ?_
    intro hvt
    exact hv (hmono t _ (by linarith) hvt)
  -- the bounded side is inside `Adv`
  have hbounded :
      Adv ∪ (Restated.attestersIn M S Sched (r₀ - S.hc.η_SG) (r₀ - 1) \
        (Restated.activeRoundW M S Sched (r₀ - 1) \ Adv)) ⊆ Adv := by
    intro v hv
    rcases Finset.mem_union.1 hv with hv | hv
    · exact hv
    · by_contra hvA
      exact (Finset.mem_sdiff.1 hv).2 (Finset.mem_sdiff.2 ⟨hactive v hvA, hvA⟩)
  -- the bounding side contains `Finset.univ \ Adv`
  have hbounding : Finset.univ \ Adv ⊆ Restated.activeRoundW M S Sched (r₀ - 1) \ Adv := by
    intro v hv
    have hvA := (Finset.mem_sdiff.1 hv).2
    exact Finset.mem_sdiff.2 ⟨hactive v hvA, hvA⟩
  have hwB := S.E.electorate.weightOf_mono hbounded
  have hwF := S.E.electorate.weightOf_mono hbounding
  have hcompl := S.E.electorate.weightOf_add_weightOf_sdiff Adv
  -- `2 * w(Adv) < W`, in two cases on round `(r₀ + 1)`'s opening
  have htwo : 2 * S.E.electorate.weightOf Adv < S.E.electorate.totalWeight := by
    by_cases hin : M.opening S.E S.hc (r₀ + 1) ≤ tE
    · have h : 3 * S.E.electorate.weightOf Adv < S.E.electorate.totalWeight := hthird _ hin
      omega
    · rw [not_le] at hin
      have h := hrsW (r₀ + 1) (Nat.le_add_left 1 r₀) (le_of_lt hin)
      set Adv2 := Sched.adv (M.opening S.E S.hc (r₀ + 1 + 1)) with hAdv2
      have hsub : Adv ⊆ Adv2 :=
        hmono _ _ (facts.gr.Sts_opening_mono S (Nat.le_succ (r₀ + 1)))
      have hl := S.E.electorate.weightOf_mono
        (Finset.subset_union_left (s₁ := Adv2)
          (s₂ := Restated.attestersIn M S Sched (r₀ + 1 - S.hc.η_SG) (r₀ + 1 - 1) \
            (Restated.activeRoundW M S Sched (r₀ + 1 - 1) \ Adv2)))
      have hr : Restated.activeRoundW M S Sched (r₀ + 1 - 1) \ Adv2 ⊆ Finset.univ \ Adv := by
        intro v hv
        refine Finset.mem_sdiff.2 ⟨Finset.mem_univ v, fun hvA => ?_⟩
        exact (Finset.mem_sdiff.1 hv).2 (hsub hvA)
      have hr' := S.E.electorate.weightOf_mono hr
      have hA := S.E.electorate.weightOf_mono hsub
      omega
  omega

end

end DecoupledConsensusModel.Sts.Restated
