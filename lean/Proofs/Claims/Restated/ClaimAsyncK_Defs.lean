import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Conditions.Claim13bInvariant
import Model.Conditions.ClaimAsyncK_Defs
import Model.Conditions.ClaimAsyncK_Handover
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Sts_Spec2Claims_ClaimStableThroughAsyncPeriod
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.ClaimAsyncK_Defs

/-!
# Facts about rounds, attester sets and delivery

Theorems over a model `M : Record.Model V` with facts `facts : Record.Facts M`: the long-term
condition and its quorums, closed forms of action instants and cutoffs, delivery before the
asynchronous period, the classification of height votes at the hand-over tick, and inclusions
between attester sets.
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

/-- If the adversary weighs less than a third at every time up to `tSafe` and
    `outsideAttestersUnderThird S Sched r` holds, then `longTermConditionUpToW S Sched r tEnd` holds
    for every `tEnd ≤ tSafe`. -/
theorem longTermConditionUpToW_of_thirds (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (r : Nat)
    (tSafe tEnd : Int) (hle : tEnd ≤ tSafe)
    (hadv : ∀ t : Int, t ≤ tSafe →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hout : Restated.outsideAttestersUnderThird M S Sched r) :
    Restated.longTermConditionUpToW M S Sched r tEnd := by
  unfold Restated.longTermConditionUpToW
  unfold Restated.outsideAttestersUnderThird at hout
  have h1 := hadv tEnd hle
  have := S.E.electorate.weightOf_union_le (Restated.activeOutsideFixedIn M S Sched r) (Sched.adv tEnd)
  omega

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Under monotone corruption, `longTermConditionUpToW S Sched r tEnd` implies
    `longTermConditionUpToW S Sched r t` for every `t ≤ tEnd`. -/
theorem longTermConditionUpToW_mono (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (r : Nat)
    (hmono : Sched.MonotoneCorruption) {t tEnd : Int} (ht : t ≤ tEnd)
    (h : Restated.longTermConditionUpToW M S Sched r tEnd) : Restated.longTermConditionUpToW M S Sched r t := by
  unfold Restated.longTermConditionUpToW at h ⊢
  have hsub : Restated.activeOutsideFixedIn M S Sched r ∪ Sched.adv t ⊆
      Restated.activeOutsideFixedIn M S Sched r ∪ Sched.adv tEnd :=
    Finset.union_subset_union (Finset.Subset.refl _) (hmono t tEnd ht)
  have := S.E.electorate.weightOf_mono hsub
  omega

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Under `longTermConditionUpToW S Sched r t`, every set `A` weighing at least the quorum `S.E.q`
    has a member that is not in `activeOutsideFixedIn S Sched r` and that the adversary does not
    hold at `t`. -/
theorem exists_good_of_quorum (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (r : Nat) (t : Int)
    (h : Restated.longTermConditionUpToW M S Sched r t)
    {A : Finset V} (hq : S.E.q ≤ S.E.electorate.weightOf A) :
    ∃ v ∈ A, v ∉ Restated.activeOutsideFixedIn M S Sched r ∧ v ∉ Sched.adv t := by
  classical
  by_contra hex
  have hsub : A ⊆ Restated.activeOutsideFixedIn M S Sched r ∪ Sched.adv t := by
    intro v hv
    by_contra hnot
    exact hex ⟨v, hv, fun h1 => hnot (Finset.mem_union_left _ h1),
      fun h2 => hnot (Finset.mem_union_right _ h2)⟩
  have hA := S.E.electorate.weightOf_mono hsub
  have hqW : 2 * S.E.electorate.totalWeight ≤ 3 * S.E.q :=
    two_mul_totalWeight_le_three_mul_q S.E
  unfold Restated.longTermConditionUpToW at h
  omega

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Round `ρ`'s action instant in closed form: `S.hc.a S.E.Δ ρ = 4Δ · R · ρ + 6Δ`. -/
theorem healA_eq_closed (facts : Record.Facts M) (S : Setup V) (ρ : Nat) :
    (M.a S.hc S.E.Δ ρ) = 4 * S.E.Δ * (S.hc.R : Int) * (ρ : Int) + 6 * S.E.Δ := by
  have h := facts.gr.a_add_rounds S 0 ρ
  have h0 := facts.sch.a_eq_confirmation_time S.hc S.E 0
  have h6 := facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E 0
  rw [facts.gr.opening_slot_zero_mk] at h0
  rw [Nat.zero_add] at h
  rw [h, h0, ← h6]
  simp only [slotStart]
  push_cast
  ring

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Round `ρ`'s G2 early cutoff is eleven delays before its action instant. -/
theorem early_g2_eq_healA (facts : Record.Facts M) (S : Setup V) (ρ : Nat) :
    M.early S.E S.hc ρ .g2 = (M.a S.hc S.E.Δ ρ) - 11 * S.E.Δ :=
  facts.gr.early_g2_eq S ρ

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Action instants are monotone in the round: `ρ ≤ ρ'` gives `S.hc.a S.E.Δ ρ ≤ S.hc.a S.E.Δ ρ'`. -/
theorem healA_mono (facts : Record.Facts M) (S : Setup V) {ρ ρ' : Nat} (h : ρ ≤ ρ') :
    (M.a S.hc S.E.Δ ρ) ≤ (M.a S.hc S.E.Δ ρ') := by
  rw [Restated.healA_eq_closed facts, Restated.healA_eq_closed facts]
  have hΔ : (0 : Int) < S.E.Δ := S.E.Δ_pos
  have hpos : (0 : Int) ≤ 4 * S.E.Δ * (S.hc.R : Int) := by positivity
  have : (ρ : Int) ≤ (ρ' : Int) := by exact_mod_cast h
  have := mul_le_mul_of_nonneg_left this hpos
  linarith

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The next round's action instant is one attester window later:
    `S.hc.a S.E.Δ (ρ + 1) = S.hc.a S.E.Δ ρ + wAttest S`. -/
theorem healA_succ (facts : Record.Facts M) (S : Setup V) (ρ : Nat) :
    (M.a S.hc S.E.Δ (ρ + 1)) = (M.a S.hc S.E.Δ ρ) + wAttest S := by
  rw [Restated.healA_eq_closed facts, Restated.healA_eq_closed facts]
  unfold wAttest
  push_cast
  ring

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Under `SynchronyFromWakeOutside S x b₀ b₁`, if an honest validator sends `sm` at step `k`, the
    deadline `max (x[k].time) S.E.t_GST + Δ` is at or before `b₀`, and `w` is awake from the send
    through that deadline, then `sm` is delivered to `w` at a step `d` after `k`, at a time at or
    after the send's and strictly before the deadline. -/
theorem deliver_before_period (facts : Record.Facts M) (S : Setup V) {Sched : Schedule V}
    (x : AtomicExec (Record.protocolOf M S) Sched) {b₀ b₁ : Int}
    (hsync : Restated.SynchronyFromWakeOutside M S x b₀ b₁)
    {k : Nat} {w : V} {sm : SignedMsg V (NamedObject V)}
    (hs : Restated.HonestSendAt M S x k sm)
    (hdl : max (x[k].time : Int) S.E.t_GST + S.E.Δ ≤ b₀)
    (hw : w ∈ Sched.awakeThroughout (x[k + 1].time : Int)
      (max (x[k].time : Int) S.E.t_GST + S.E.Δ)) :
    ∃ d : Nat, k < d ∧ x.lbl d = AtomicAction.deliver w sm ∧
      (x[k].time : Int) ≤ (x[d].time : Int) ∧
      (x[d].time : Int) < max (x[k].time : Int) S.E.t_GST + S.E.Δ := by
  have hd := deadlineOutside_of_le S (b₁ := b₁) hdl
  have := hsync k w sm hs (by rw [hd]; exact hw)
  rw [hd] at this
  exact this

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- From `StableHandover S Sched x r P` and the tick at step `n₁` at round `r + 1`'s action instant,
    every height vote in the sent log right after that tick whose signer is honest through that step
    is bound to a root every block on the wire with which is an ancestor or a descendant of `P`, or
    is for a height less than every honest justified height right after the tick. -/
theorem votesClassified_of_handover (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (r : Nat) (P : Block V)
    (hH : Restated.StableHandover M S Sched x r P) {n₁ : Nat} (hn₁ : Restated.tickStepAt M x n₁ ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)))) :
    Restated.VotesClassified M S Sched x r P n₁ (n₁ + 1) := by
  intro u a h root tmo hu ha hsent hpair
  by_cases hall : ∀ w : V, Restated.HonestThrough M Sched x (n₁ + 1) w → h < (x[n₁ + 1][w].st).st.core.h_j
  · exact Or.inr (Or.inl hall)
  · refine Or.inl fun C hC hroot => ?_
    rcases hH.entries n₁ hn₁ u a h root tmo hu ha hsent hpair C hC hroot with hc | hc
    · exact hc
    · exact absurd hc hall

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- One delay after round `r`'s action instant is at or before round `r + 1`'s G2 early cutoff. -/
theorem action_delta_le_early_succ_kit (facts : Record.Facts M) (S : Setup V) (r : Nat) :
    (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ ≤ M.early S.E S.hc (r + 1) .g2 := by
  have h1 := Restated.early_g2_eq_healA facts S (r + 1)
  have h2 := Restated.healA_succ facts S r
  have h3 := twelve_delta_le_wAttest_kit S
  show (M.a S.hc S.E.Δ r) + S.E.Δ ≤ _
  linarith

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Under `periodBeforeExpiry S r b₁`, the period ends before round `r + η_SG + 1`'s action instant:
    `b₁ < S.a (r + η_SG + 1)`. -/
theorem lt_action_of_periodBeforeExpiry (facts : Record.Facts M) (S : Setup V) {r : Nat} {b₁ : Int}
    (h : Restated.periodBeforeExpiry M S r b₁) : b₁ < (M.a S.hc S.E.Δ (r + S.hc.η_SG + 1)) := by
  unfold Restated.periodBeforeExpiry at h
  have h1 := Restated.early_g2_eq_healA facts S (r + S.hc.η_SG + 1)
  have hΔ : (0 : Int) < S.E.Δ := S.E.Δ_pos
  linarith

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- `activeRoundWThroughNext S Sched r ⊆ activeRoundW S Sched (r + 1)`: the validators awake through
    rounds `r` and `r + 1` are awake throughout round `r + 1`'s attester window. -/
theorem activeRoundWThroughNext_subset_activeRoundW_succ (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (r : Nat) : Restated.activeRoundWThroughNext M S Sched r ⊆ Restated.activeRoundW M S Sched (r + 1) := by
  intro w hw
  unfold Restated.activeRoundWThroughNext at hw
  unfold Restated.activeRoundW
  have h1 := Restated.healA_succ facts S r
  have h2 := twelve_delta_le_wAttest_kit S
  have hΔ : (0 : Int) < S.E.Δ := S.E.Δ_pos
  exact awakeThroughout_sub Sched (by linarith) (by linarith) hw

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- `activeRoundWThroughNextCountedAt S Sched r r₀ ⊆ activeRoundWThroughNext S Sched r`. -/
theorem activeRoundWThroughNextCountedAt_subset (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (r r₀ : Nat) :
    Restated.activeRoundWThroughNextCountedAt M S Sched r r₀ ⊆ Restated.activeRoundWThroughNext M S Sched r := by
  unfold Restated.activeRoundWThroughNextCountedAt
  exact Finset.sdiff_subset

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If `w` is awake at every time from `S.a r − wAttest S` to `t`, and `S.a (r + 1) + Δ ≤ t`, then
    `w ∈ activeRoundWThroughNext S Sched r`. -/
theorem mem_activeRoundWThroughNext_of_reader (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) {r : Nat}
    {t : Int} {w : V} (hw : w ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S r) - wAttest S) t)
    (ht : (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) + S.E.Δ ≤ t) : w ∈ Restated.activeRoundWThroughNext M S Sched r := by
  unfold Restated.activeRoundWThroughNext
  exact awakeThroughout_sub Sched le_rfl ht hw

end

end DecoupledConsensusModel.Sts.Restated
