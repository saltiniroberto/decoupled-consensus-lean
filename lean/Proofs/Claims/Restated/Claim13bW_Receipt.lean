import Proofs.Claims.Restated.Claim13bW_Schedule
import Model.Conditions.Sts_Spec2Claims_Claim13bf
import Model.Conditions.Sts_Spec2Claims_ClaimStableThroughAsyncPeriod

/-!
# Delivery before a deadline through synchrony and catch-up

An honest message sent at or before `t₀` reaches every validator awake from `t₀` through the
deadline of `t₀`, before that deadline: by synchrony when the receiver was awake from the send on,
by catch-up from its last entrance into the awake set otherwise. Stated for a monotone deadline,
then for the healing deadline `max t S.E.t_GST + S.E.Δ` and for `deadlineOutside`, over a model
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

/-- A validator asleep at `u` and awake at every instant of `[t₀, t₁]`, with `u < t₀ ≤ t₁`, entered
    the awake set for the last time before `t₀` at some `t_w` of `(u, t₀]`, and is awake throughout
    `[t_w, t₁]`. -/
theorem exists_last_entrance (Sched : Schedule V) {v : V} {u t₀ t₁ : Int} (hu : u < t₀)
    (ht : t₀ ≤ t₁) (hasleep : v ∉ Sched.awake u) (hawake : v ∈ Sched.awakeThroughout t₀ t₁) :
    ∃ t_w : Int, u < t_w ∧ t_w ≤ t₀ ∧ v ∈ Sched.awake t_w ∧ v ∉ Sched.awake (t_w - 1) ∧
      v ∈ Sched.awakeThroughout t_w t₁ := by
  have key : ∀ n : Nat, ∀ s : Int, u < s → s - u ≤ n → s ≤ t₁ → v ∈ Sched.awakeThroughout s t₁ →
      ∃ t_w : Int, u < t_w ∧ t_w ≤ s ∧ v ∈ Sched.awake t_w ∧ v ∉ Sched.awake (t_w - 1) ∧
        v ∈ Sched.awakeThroughout t_w t₁ := by
    intro n
    induction n with
    | zero => intro s hs hn; omega
    | succ n ih =>
      intro s hs hn hst hthr
      by_cases hprev : v ∈ Sched.awake (s - 1)
      · have hne : u ≠ s - 1 := by
          intro he; rw [← he] at hprev; exact hasleep hprev
        have hthr' : v ∈ Sched.awakeThroughout (s - 1) t₁ := by
          refine mem_awakeThroughout_of_forall Sched ?_
          intro t h0 h1
          rcases eq_or_lt_of_le h0 with he | hlt
          · rw [← he]; exact hprev
          · exact mem_awake_of_awakeThroughout Sched hthr (by omega) h1
        obtain ⟨t_w, h1, h2, h3, h4, h5⟩ := ih (s - 1) (by omega) (by omega) (by omega) hthr'
        exact ⟨t_w, h1, by omega, h3, h4, h5⟩
      · exact ⟨s, hs, le_rfl, mem_awake_of_awakeThroughout Sched hthr le_rfl hst, hprev, hthr⟩
  exact key (t₀ - u).toNat t₀ hu (by omega) ht hawake

/-- An honest message sent at step `k` at or before `t₀` is delivered to `w`, strictly before
    `deadline t₀`, when `t₀ ≤ deadline t₀`, `w` is awake at every instant of `[t₀, deadline t₀]`,
    and `deadline` is monotone. -/
theorem delivered_before_of_honestSend_awakeFrom (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (deadline : Int → Int)
    (hsync : Restated.SynchronyFromWakeBy M S x deadline)
    (hcatch : Restated.CatchUpOnWakeBy M S x deadline)
    (hmono : ∀ t t', t ≤ t' → deadline t ≤ deadline t')
    {k : Nat} {w : V} {sm : SignedMsg V (NamedObject V)} {t₀ : Int}
    (hsend : Restated.HonestSendAt M S x k sm) (hk : (x[k].time : Int) ≤ t₀)
    (hdl : t₀ ≤ deadline t₀)
    (haw : w ∈ Sched.awakeThroughout t₀ (deadline t₀)) :
    ∃ d : Nat, k < d ∧ x.lbl d = AtomicAction.deliver w sm ∧ (x[d].time : Int) < deadline t₀ := by
  by_cases hA : w ∈ Sched.awakeThroughout (x[k + 1].time : Int) (deadline (x[k].time : Int))
  · obtain ⟨d, hkd, hl, -, hlt⟩ := hsync k w sm hsend hA
    exact ⟨d, hkd, hl, lt_of_lt_of_le hlt (hmono _ _ hk)⟩
  · have hu : ∃ u : Int, (x[k + 1].time : Int) ≤ u ∧ u ≤ deadline (x[k].time : Int) ∧
        w ∉ Sched.awake u := by
      by_contra hno
      push Not at hno
      exact hA (mem_awakeThroughout_of_forall Sched fun t h0 h1 => hno t h0 h1)
    obtain ⟨u, hu0, hu1, hu⟩ := hu
    have hut : u < t₀ := by
      by_contra hge
      push Not at hge
      exact hu (mem_awake_of_awakeThroughout Sched haw hge (le_trans hu1 (hmono _ _ hk)))
    obtain ⟨t_w, hutw, htw, hwa, hws, hthr⟩ := exists_last_entrance Sched hut hdl hu haw
    have hstep : (x[k].time : Int) ≤ (x[k + 1].time : Int) := by
      exact_mod_cast Record.time_mono M S Sched x (Nat.le_succ k)
    have hkt : (x[k].time : Int) < t_w := by omega
    have hthr' : w ∈ Sched.awakeThroughout t_w (deadline t_w) := by
      refine mem_awakeThroughout_of_forall Sched ?_
      intro t h0 h1
      exact mem_awake_of_awakeThroughout Sched hthr h0 (le_trans h1 (hmono _ _ htw))
    obtain ⟨d, hkd, hl, -, hlt⟩ := hcatch k w sm t_w hsend hkt hwa hws hthr'
    exact ⟨d, hkd, hl, lt_of_lt_of_le hlt (hmono _ _ htw)⟩

/-- The healing form: `deadline t = max t S.E.t_GST + S.E.Δ`, so with `S.E.t_GST ≤ t₀` the bound is
    `t₀ + S.E.Δ`. -/
theorem delivered_before_of_honestSend_awakeFrom_healing (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hsync : Restated.SynchronyFromWake M S x) (hcatch : Restated.CatchUpOnWake M S x)
    {k : Nat} {w : V} {sm : SignedMsg V (NamedObject V)} {t₀ : Int}
    (hsend : Restated.HonestSendAt M S x k sm) (hk : (x[k].time : Int) ≤ t₀) (hgst : S.E.t_GST ≤ t₀)
    (haw : w ∈ Sched.awakeThroughout t₀ (t₀ + S.E.Δ)) :
    ∃ d : Nat, k < d ∧ x.lbl d = AtomicAction.deliver w sm ∧ (x[d].time : Int) < t₀ + S.E.Δ := by
  have hmax : max t₀ S.E.t_GST = t₀ := max_eq_left hgst
  have hΔ : (0 : Int) < S.E.Δ := S.E.Δ_pos
  have hdl : t₀ ≤ max t₀ S.E.t_GST + S.E.Δ := by rw [hmax]; omega
  have haw' : w ∈ Sched.awakeThroughout t₀ (max t₀ S.E.t_GST + S.E.Δ) := by rw [hmax]; exact haw
  have h := delivered_before_of_honestSend_awakeFrom facts S Sched x
    (fun t => max t S.E.t_GST + S.E.Δ) hsync hcatch
    (fun t t' htt => by
      show max t S.E.t_GST + S.E.Δ ≤ max t' S.E.t_GST + S.E.Δ
      have := max_le_max htt (le_refl S.E.t_GST); omega)
    hsend hk hdl haw'
  rw [hmax] at h
  exact h

/-- `deadlineOutside S b₀ b₁` is monotone. -/
theorem deadlineOutside_monotone (S : Setup V) (b₀ b₁ : Int) {t t' : Int} (h : t ≤ t') :
    deadlineOutside S b₀ b₁ t ≤ deadlineOutside S b₀ b₁ t' := by
  unfold deadlineOutside
  have h1 : max t S.E.t_GST ≤ max t' S.E.t_GST := max_le_max h le_rfl
  have h2 : max t (max b₁ S.E.t_GST) ≤ max t' (max b₁ S.E.t_GST) := max_le_max h le_rfl
  have h3 : max t S.E.t_GST ≤ max t' (max b₁ S.E.t_GST) :=
    max_le_max h (le_max_right _ _)
  split_ifs <;> omega

/-- Every time `t` is at most `deadlineOutside S b₀ b₁ t`. -/
theorem self_le_deadlineOutside (S : Setup V) (b₀ b₁ t : Int) : t ≤ deadlineOutside S b₀ b₁ t := by
  unfold deadlineOutside
  have hΔ : (0 : Int) < S.E.Δ := S.E.Δ_pos
  have h1 : t ≤ max t S.E.t_GST := le_max_left _ _
  have h2 : t ≤ max t (max b₁ S.E.t_GST) := le_max_left _ _
  split_ifs <;> omega

/-- The form of the asynchrony pages: with synchrony and catch-up suspended on `[b₀, b₁)`, an honest
    message sent at or before `t₀` is delivered to `w` strictly before `deadlineOutside S b₀ b₁ t₀`
    when `w` is awake at every instant of `[t₀, deadlineOutside S b₀ b₁ t₀]`. -/
theorem delivered_before_of_honestSend_awakeFrom_outside (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) {b₀ b₁ : Int}
    (hsync : Restated.SynchronyFromWakeOutside M S x b₀ b₁)
    (hcatch : Restated.CatchUpOnWakeOutside M S x b₀ b₁)
    {k : Nat} {w : V} {sm : SignedMsg V (NamedObject V)} {t₀ : Int}
    (hsend : Restated.HonestSendAt M S x k sm) (hk : (x[k].time : Int) ≤ t₀)
    (haw : w ∈ Sched.awakeThroughout t₀ (deadlineOutside S b₀ b₁ t₀)) :
    ∃ d : Nat, k < d ∧ x.lbl d = AtomicAction.deliver w sm ∧
      (x[d].time : Int) < deadlineOutside S b₀ b₁ t₀ :=
  delivered_before_of_honestSend_awakeFrom facts S Sched x (deadlineOutside S b₀ b₁) hsync hcatch
    (fun _ _ h => deadlineOutside_monotone S b₀ b₁ h) hsend hk (self_le_deadlineOutside S b₀ b₁ t₀) haw

end

end DecoupledConsensusModel.Sts.Restated
