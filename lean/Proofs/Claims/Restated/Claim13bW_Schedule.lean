import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# Action instants and wake schedules

Arithmetic on the rounds' action instants and the attester window `wAttest S`, and what
`WakesAtActionInstants` and `SleepsAfterActionInstants` say about when a validator was awake or
asleep. Stated over a model `M : Record.Model V`.
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

/-- Round `(r + 1)`'s action instant minus `wAttest S` is round `r`'s action instant. -/
theorem wAttest_eq_action_succ_sub (facts : Record.Facts M) (S : Setup V) (r : Round) :
    (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) - wAttest S = (Restated.Vocabulary.Execution.Setup.a M S r) := by
  show M.a S.hc S.E.Δ (r + 1) - wAttest S = M.a S.hc S.E.Δ r
  rw [facts.gr.a_add_rounds S r 1]
  simp only [wAttest]
  push_cast
  ring

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- An action instant strictly before another belongs to an earlier round. -/
theorem round_lt_of_action_lt (facts : Record.Facts M) (S : Setup V) {r ρ : Round} (h : (Restated.Vocabulary.Execution.Setup.a M S r) < (Restated.Vocabulary.Execution.Setup.a M S ρ)) : r < ρ := by
  by_contra hcon
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt hcon)
  change M.a S.hc S.E.Δ (ρ + k) < M.a S.hc S.E.Δ ρ at h
  rw [facts.gr.a_add_rounds S ρ k] at h
  have hd := S.E.Δ_pos
  have hk : (0 : Int) ≤ ((S.hc.R * k : Nat) : Int) := Int.natCast_nonneg _
  nlinarith

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- A later round's action instant is not earlier. -/
theorem action_mono (facts : Record.Facts M) (S : Setup V) {r ρ : Round} (h : r ≤ ρ) : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (Restated.Vocabulary.Execution.Setup.a M S ρ) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  show M.a S.hc S.E.Δ r ≤ M.a S.hc S.E.Δ (r + k)
  rw [facts.gr.a_add_rounds S r k]
  have hd := S.E.Δ_pos
  have hk : (0 : Int) ≤ ((S.hc.R * k : Nat) : Int) := Int.natCast_nonneg _
  nlinarith

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- No action instant lies strictly between two consecutive action instants. -/
theorem no_action_between (facts : Record.Facts M) (S : Setup V) (r ρ : Round)
    (h1 : (Restated.Vocabulary.Execution.Setup.a M S r) < (Restated.Vocabulary.Execution.Setup.a M S ρ)) (h2 : (Restated.Vocabulary.Execution.Setup.a M S ρ) < (Restated.Vocabulary.Execution.Setup.a M S (r + 1))) : False := by
  have hlt := Restated.round_lt_of_action_lt facts S h1
  have hlt' := Restated.round_lt_of_action_lt facts S h2
  exact absurd (Nat.le_of_lt_succ hlt') (Nat.not_le.mpr hlt)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If round `ρ`'s action instant is strictly before round `r`'s, it is at or before
    `S.a r − wAttest S`, the start of round `r`'s attester window. -/
theorem action_le_sub_wAttest_of_lt (facts : Record.Facts M) (S : Setup V) {r ρ : Round} (h : (Restated.Vocabulary.Execution.Setup.a M S ρ) < (Restated.Vocabulary.Execution.Setup.a M S r)) :
    (Restated.Vocabulary.Execution.Setup.a M S ρ) ≤ (Restated.Vocabulary.Execution.Setup.a M S r) - wAttest S := by
  have hρr := Restated.round_lt_of_action_lt facts S h
  have hle : (Restated.Vocabulary.Execution.Setup.a M S ρ) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r - 1)) := Restated.action_mono facts S (Nat.le_sub_one_of_lt hρr)
  have hpred := Restated.wAttest_eq_action_succ_sub facts S (r - 1)
  rw [Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le ρ) hρr))] at hpred
  linarith

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Under `WakesAtActionInstants`, a validator awake at `S.a r` and at `S.a r − 1` is awake at every
    time of the `wAttest S` before `S.a r`. -/
theorem awake_back (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (hw : Restated.WakesAtActionInstants M S Sched)
    (r : Round) (v : V) (h0 : v ∈ Sched.awake ((Restated.Vocabulary.Execution.Setup.a M S r))) (h1 : v ∈ Sched.awake ((Restated.Vocabulary.Execution.Setup.a M S r) - 1)) :
    ∀ k : Nat, (k : Int) ≤ wAttest S → v ∈ Sched.awake ((Restated.Vocabulary.Execution.Setup.a M S r) - k) := by
  intro k
  induction k with
  | zero => intro _; simpa using h0
  | succ k ih =>
    intro hk
    have hk1 : (k : Int) + 1 ≤ wAttest S := by push_cast at hk; linarith
    have hprev := ih (by linarith)
    by_contra hcon
    have hcon' : v ∉ Sched.awake ((Restated.Vocabulary.Execution.Setup.a M S r) - (k : Int) - 1) := by
      intro h
      apply hcon
      have e : (Restated.Vocabulary.Execution.Setup.a M S r) - ((k + 1 : Nat) : Int) = (Restated.Vocabulary.Execution.Setup.a M S r) - (k : Int) - 1 := by push_cast; ring
      rw [e]; exact h
    obtain ⟨ρ, hρ⟩ := hw ((Restated.Vocabulary.Execution.Setup.a M S r) - k) v hprev hcon'
    have hρ' : (Restated.Vocabulary.Execution.Setup.a M S r) - (k : Int) = (Restated.Vocabulary.Execution.Setup.a M S ρ) := hρ
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      apply hcon'
      simpa using h1
    · have hk1' : (1 : Int) ≤ (k : Int) := by exact_mod_cast hkpos
      have hle := Restated.action_le_sub_wAttest_of_lt facts S (r := r) (ρ := ρ) (by linarith)
      linarith

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Under `WakesAtActionInstants`, a validator awake at round `r`'s action instant and at the time
    before it was awake throughout the attester window before that instant. -/
theorem active_of_awake_prev (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (hw : Restated.WakesAtActionInstants M S Sched) {r : Round} {v : V}
    (h0 : v ∈ Sched.awake ((Restated.Vocabulary.Execution.Setup.a M S r))) (h1 : v ∈ Sched.awake ((Restated.Vocabulary.Execution.Setup.a M S r) - 1)) :
    v ∈ Restated.activeRoundW M S Sched r := by
  refine mem_awakeThroughout_of_forall Sched ?_
  intro t hlo hhi
  have hlo' : (Restated.Vocabulary.Execution.Setup.a M S r) - wAttest S ≤ t := hlo
  have hhi' : t ≤ (Restated.Vocabulary.Execution.Setup.a M S r) := hhi
  obtain ⟨k, hk⟩ : ∃ k : Nat, t = (Restated.Vocabulary.Execution.Setup.a M S r) - k :=
    ⟨((Restated.Vocabulary.Execution.Setup.a M S r) - t).toNat, by rw [Int.toNat_of_nonneg (by linarith)]; ring⟩
  subst hk
  exact Restated.awake_back facts S Sched hw r v h0 h1 k (by linarith)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Under `WakesAtActionInstants`, a validator awake at a time `t` of `[S.a r, S.a (r + 1))` has
    been awake at every time from `S.a r` to `t`. -/
theorem awake_since_action (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (hw : Restated.WakesAtActionInstants M S Sched) {r : Round} {t : Int}
    (_ht0 : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ t) (ht1 : t < (Restated.Vocabulary.Execution.Setup.a M S (r + 1))) {v : V} (hv : v ∈ Sched.awake t) :
    ∀ t' : Int, (Restated.Vocabulary.Execution.Setup.a M S r) ≤ t' → t' ≤ t → v ∈ Sched.awake t' := by
  have hback : ∀ k : Nat, (k : Int) ≤ t - (Restated.Vocabulary.Execution.Setup.a M S r) → v ∈ Sched.awake (t - k) := by
    intro k
    induction k with
    | zero => intro _; simpa using hv
    | succ k ih =>
      intro hk
      have hk1 : (k : Int) + 1 ≤ t - (Restated.Vocabulary.Execution.Setup.a M S r) := by push_cast at hk; linarith
      have hprev := ih (by linarith)
      by_contra hcon
      have hcon' : v ∉ Sched.awake (t - (k : Int) - 1) := by
        intro h
        apply hcon
        have e : t - ((k + 1 : Nat) : Int) = t - (k : Int) - 1 := by push_cast; ring
        rw [e]; exact h
      obtain ⟨ρ, hρ⟩ := hw (t - k) v hprev hcon'
      have hρ' : t - (k : Int) = (Restated.Vocabulary.Execution.Setup.a M S ρ) := hρ
      exact Restated.no_action_between facts S r ρ (by linarith) (by linarith)
  intro t' hu0 hu1
  obtain ⟨k, hk⟩ : ∃ k : Nat, t' = t - k :=
    ⟨(t - t').toNat, by rw [Int.toNat_of_nonneg (by linarith)]; ring⟩
  subst hk
  exact hback k (by linarith)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Under `WakesAtActionInstants`, a validator awake at every time of `[t_0, t_1]` with
    `S.a r ≤ t_0 < S.a (r + 1)` is awake at every time of `[S.a r, t_1]`. -/
theorem awakeThroughout_from_action (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (hw : Restated.WakesAtActionInstants M S Sched) {r : Round} {t_0 t_1 : Int}
    (ha0 : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ t_0) (ha1 : t_0 < (Restated.Vocabulary.Execution.Setup.a M S (r + 1))) (hab : t_0 ≤ t_1) {v : V}
    (hv : v ∈ Sched.awakeThroughout t_0 t_1) : v ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S r)) t_1 := by
  refine mem_awakeThroughout_of_forall Sched ?_
  intro t hu0 hu1
  rcases le_or_gt t_0 t with hau | hua
  · exact mem_awake_of_awakeThroughout Sched hv hau hu1
  · have hva : v ∈ Sched.awake t_0 := mem_awake_of_awakeThroughout Sched hv le_rfl hab
    exact Restated.awake_since_action facts S Sched hw ha0 ha1 hva t hu0 (le_of_lt hua)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Under `SleepsAfterActionInstants`, a validator awake at `S.a r` and asleep at `S.a r − 1` was
    asleep at every time of `[S.a r − wAttest S + 2, S.a r − 1]`. -/
theorem asleep_back (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (hs : Restated.SleepsAfterActionInstants M S Sched)
    {r : Round} {v : V} (h1 : v ∉ Sched.awake ((Restated.Vocabulary.Execution.Setup.a M S r) - 1)) :
    ∀ k : Nat, (k : Int) + 3 ≤ wAttest S → v ∉ Sched.awake ((Restated.Vocabulary.Execution.Setup.a M S r) - 1 - k) := by
  intro k
  induction k with
  | zero => intro _; simpa using h1
  | succ k ih =>
    intro hk
    have hk1 : (k : Int) + 4 ≤ wAttest S := by push_cast at hk; linarith
    have hprev := ih (by linarith)
    intro hcon
    have hcon' : v ∈ Sched.awake ((Restated.Vocabulary.Execution.Setup.a M S r) - 1 - (k : Int) - 1) := by
      have e : (Restated.Vocabulary.Execution.Setup.a M S r) - 1 - ((k + 1 : Nat) : Int) = (Restated.Vocabulary.Execution.Setup.a M S r) - 1 - (k : Int) - 1 := by
        push_cast; ring
      rw [e] at hcon; exact hcon
    obtain ⟨ρ, hρ⟩ := hs ((Restated.Vocabulary.Execution.Setup.a M S r) - 1 - k) v hcon' hprev
    have hρ' : (Restated.Vocabulary.Execution.Setup.a M S r) - 1 - (k : Int) = (Restated.Vocabulary.Execution.Setup.a M S ρ) + 1 := hρ
    have hle := Restated.action_le_sub_wAttest_of_lt facts S (r := r) (ρ := ρ) (by linarith)
    linarith

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Under `SleepsAfterActionInstants`, a validator asleep at `S.a r − 1` was asleep at each of round
    `r`'s three phase-domain instants. -/
theorem asleep_at_domain (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (hs : Restated.SleepsAfterActionInstants M S Sched)
    {r : Round} {v : V} (h1 : v ∉ Sched.awake ((Restated.Vocabulary.Execution.Setup.a M S r) - 1))
    (p : Protocol.Phase) : v ∉ Sched.awake (M.domain S.E S.hc r p) := by
  have hd := S.E.Δ_pos
  have hd1 : (1 : Int) ≤ S.E.Δ := by simpa using Int.add_one_le_of_lt hd
  have hw12 := twelve_delta_le_wAttest S
  have hearly := facts.gr.early_g2_eq S r
  have hearly2 := facts.gr.early_add_two_delta_le_domain S r .g2
  have hg2 := facts.gr.domain_g2_le_domain_l67 S r p
  have hup := facts.gr.domain_add_five_delta_le_action S r p
  have hbounds : (Restated.Vocabulary.Execution.Setup.a M S r) - 1 - (9 * S.E.Δ - 1) ≤ M.domain S.E S.hc r p
      ∧ M.domain S.E S.hc r p ≤ (Restated.Vocabulary.Execution.Setup.a M S r) - 1 - (5 * S.E.Δ - 1) := by
    constructor <;> linarith
  obtain ⟨k, hk⟩ : ∃ k : Nat,
      M.domain S.E S.hc r p = (Restated.Vocabulary.Execution.Setup.a M S r) - 1 - k :=
    ⟨((Restated.Vocabulary.Execution.Setup.a M S r) - 1 - M.domain S.E S.hc r p).toNat, by
      rw [Int.toNat_of_nonneg (by linarith [hbounds.2])]; ring⟩
  rw [hk]
  apply Restated.asleep_back facts S Sched hs h1 k
  linarith [hbounds.1]

end

end DecoupledConsensusModel.Sts.Restated
