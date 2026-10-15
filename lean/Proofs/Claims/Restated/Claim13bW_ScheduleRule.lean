import Proofs.Claims.Restated.Claim13bW_Schedule
import Model.Record.NodeFactsWake
import Proofs.Claims.Restated.Claim13bStepGrade
import Proofs.Claims.Restated.Claim13bK_FreshAttestersW
import Proofs.Claims.Restated.Claim13bStepKitTick
import Proofs.Claims.Restated.RunAll

/-!
# Awake windows read off the awake tests a tick passed

An honest validator's tick runs round `r`'s attestation duty only when its node state passes round
`r`'s grade-2 awake test, and its confirmation duty only when the state passes the grade-2 test of
the round of the next slot. `NodeWakeFacts` reads a passed test back as a fact about the schedule:
the validator was awake at every time of the test's window. This file states what that gives for a
sent attestation, over a model `M : Record.Model V`; `Claim13bW_RecordsSuccRule.lean` states it for
a change of the confirmed records.
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

/-- The opening slot of round `r` is `r * R`. -/
private theorem opening_slot_closed_sr (facts : Record.Facts M) (hc : Protocol.HealConfig)
    (r : Round) : M.opening_slot hc r = r * hc.R := by
  have h := facts.gr.opening_slot_add_mk hc 0 r
  rw [Nat.zero_add, facts.gr.opening_slot_zero_mk, Nat.zero_add] at h
  exact h

/-- The action instant of round `r` is `4 * Δ * R * r + 6 * Δ`. -/
private theorem action_closed_sr (facts : Record.Facts M) (S : Setup V) (r : Round) :
    (Restated.Vocabulary.Execution.Setup.a M S r) =
      4 * S.E.Δ * (S.hc.R : Int) * (r : Int) + 6 * S.E.Δ := by
  show M.a S.hc S.E.Δ r = _
  rw [facts.sch.a_eq_confirmation_time S.hc S.E r,
    ← facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E _, slotStart_closed,
    opening_slot_closed_sr facts]
  push_cast
  ring

/-- From round `1` on, round `r`'s grade-2 window start, `S.a r − 12Δ`, is at or after time `0`. -/
theorem early_g2_sub_delta_nonneg (facts : Record.Facts M) (S : Setup V) {r : Round}
    (hr : 1 ≤ r) : 0 ≤ M.early S.E S.hc r .g2 - S.E.Δ := by
  have he := facts.gr.early_g2_eq S r
  have ha := action_closed_sr facts S r
  change M.a S.hc S.E.Δ r = _ at ha
  have hd := S.E.Δ_pos
  have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  have hr' : (1 : Int) ≤ (r : Int) := by exact_mod_cast hr
  have h12 : 12 * S.E.Δ ≤ 4 * S.E.Δ * (S.hc.R : Int) * (r : Int) := by
    have h1 : 0 ≤ S.E.Δ * ((S.hc.R : Int) - 3) := mul_nonneg (le_of_lt hd) (by linarith)
    have h2 : 0 ≤ S.E.Δ * (S.hc.R : Int) * ((r : Int) - 1) :=
      mul_nonneg (mul_nonneg (le_of_lt hd) (by linarith)) (by linarith)
    nlinarith
  rw [he, ha]
  linarith

/-- From round `1` on, round `r`'s grade-1 window start is at or after time `0`. -/
theorem early_g1_sub_delta_nonneg (facts : Record.Facts M) (S : Setup V) {r : Round}
    (hr : 1 ≤ r) : 0 ≤ M.early S.E S.hc r .g1 - S.E.Δ := by
  have h := early_g2_sub_delta_nonneg facts S hr
  have h1 := facts.gr.early_g2_add_delta_le_early_g1 S r
  have hd := S.E.Δ_pos
  linarith

/-- If `⟨v, o⟩` is in the multiset difference `x[k + 1].sent - x[k].sent` after the tick step `k` at
    time `t`, then `v` is awake and not held by the adversary at `t`, and some outcome of `v`'s tick
    at `t`, from the node state its wake stage leaves, has `o` in its list. -/
theorem tick_outcome_of_mem_sent_diff (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    {k t : Nat} {v : V} {o : NamedObject V} (hl : x.lbl k = AtomicAction.tickAllAwake t)
    (hnew : (⟨v, o⟩ : SignedMsg V (NamedObject V)) ∈ x[k + 1].sent - x[k].sent) :
    v ∈ Sched.awake (t : Int) \ Sched.adv (t : Int) ∧
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched (t : Int) x[k] v) (t : Int) ⇢ out ∧
          o ∈ out.2 := by
  have hs : AtomicStep (Record.protocolOf M S) Sched (x.lbl k) x[k] x[k + 1] := x.step k
  rw [hl] at hs
  obtain ⟨-, w, tk, hwake, htick, hc⟩ := hs
  have hsent : x[k + 1].sent = x[k].sent
      + (Sched.awake (t : Int) \ Sched.adv (t : Int)).sum
          (fun q => ((w q).send + (tk q).send).map (SignedMsg.mk q)) := by
    rw [hc]; rfl
  rw [hsent, add_tsub_cancel_left] at hnew
  obtain ⟨q, hq, hmem⟩ := Multiset.mem_sum.1 hnew
  obtain ⟨o', ho', heq⟩ := Multiset.mem_map.1 hmem
  have hqv : q = v := congrArg SignedMsg.sender heq
  have hoo : o' = o := congrArg SignedMsg.msg heq
  subst hqv; subst hoo
  have hwst : (w q).state = Record.wakeStage M Sched (t : Int) x[k] q ∧ (w q).send = 0 := by
    refine ⟨Record.wakeStage_of_TickAllAwakeWake M S Sched (hwake q), ?_⟩
    have hww := hwake q
    unfold TickAllAwakeWake at hww
    by_cases he : q ∈ entrants Sched t
    · rw [if_pos he] at hww
      rw [Record.protocolOf_step_wake M S hww]
    · rw [if_neg he] at hww
      rw [hww]
  rw [hwst.2, zero_add] at ho'
  have htk : tk q ∈ Record.reactionsOf M S q ((w q).state) (t : Int) .tick ∨
      (Record.reactionsOf M S q ((w q).state) (t : Int) .tick = ∅ ∧
        tk q = { state := (w q).state, send := 0 }) := htick q hq
  rcases htk with htk | ⟨-, htk⟩
  · simp only [Record.reactionsOf, Set.mem_setOf_eq] at htk
    obtain ⟨out, hout, htkv⟩ := htk
    rw [htkv] at ho'
    rw [hwst.1] at hout
    exact ⟨hq, out, hout, Multiset.mem_coe.1 ho'⟩
  · rw [htk] at ho'
    exact absurd ho' (by simp)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If an outcome of the tick of a validator `v` at the tick step `k`, at time `τ`, sends the
    attestation `a`, and `v` is awake at `τ` and not held by the adversary at any time up to `τ`,
    then `τ` is the action instant of `a`'s round, `a` is signed by `v`, and `v` was awake at every
    time from the grade-2 window start of `a`'s round to `τ`.

    Variables: `k` the tick step, `τ` its time, `v` the sender, `out` the tick's outcome, `a` the
    attestation. -/
theorem awakeThroughout_window_of_tick_emit (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    {k τ : Nat} {v : V} (hl : x.lbl k = AtomicAction.tickAllAwake τ)
    -- `v` is not held by the adversary at any time up to `τ`
    (hhon : ∀ t ≤ (τ : Int), v ∉ Sched.adv t)
    (haw : v ∈ Sched.awake (τ : Int))
    {out : M.N × List (NamedObject V)}
    (hout : M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched (τ : Int) x[k] v) (τ : Int) ⇢ out)
    {a : NamedAttestation V} (hemit : NamedObject.attest a ∈ out.2)
    -- the grade-2 window start of `a`'s round is at or after time `0`
    (hr : 0 ≤ M.early S.E S.hc a.round .g2 - S.E.Δ) :
    (τ : Int) = Restated.Vocabulary.Execution.Setup.a M S a.round ∧ a.val_index = v ∧
      v ∈ Sched.awakeThroughout (M.early S.E S.hc a.round .g2 - S.E.Δ) (τ : Int) := by
  have hf := facts.nd.tick_attestation_fields (Setup.alwaysAwake S) v _ _
    (Record.runs_as_wakeStage facts S Sched x k v (τ : Int)) out hout a hemit
  exact ⟨hf.1, hf.2.2, facts.ndWake.run_fact_g2_sound_at S Sched x k τ a.round v hl hr hhon haw hf.2.1⟩

/-- An attestation of round `r` that an honest validator `v` sent at round `r`'s action tick, step
    `n`, shows that `v` was awake at every time from round `r`'s grade-2 window start to round
    `r`'s action instant.

    Variables: `r` the round, `n` its action tick step, `v` the sender, `a` the attestation. -/
theorem awakeThroughout_window_of_attested (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    {r : Round} {n : Nat} (hn : Restated.tickStepAt M x n (Restated.Vocabulary.Execution.Setup.a M S r))
    -- the grade-2 window start of round `r` is at or after time `0`
    (hr : 0 ≤ M.early S.E S.hc r .g2 - S.E.Δ)
    {v : V}
    -- `v` is not held by the adversary at any time up to round `r`'s action instant
    (hhon : ∀ t ≤ Restated.Vocabulary.Execution.Setup.a M S r, v ∉ Sched.adv t)
    {a : NamedAttestation V}
    -- `v`'s attestation `a` is new in the sent log at step `n`
    (hsent : (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n + 1].sent - x[n].sent)
    (ha : a.round = r) (hai : a.val_index = v) :
    v ∈ Sched.awakeThroughout (M.early S.E S.hc r .g2 - S.E.Δ)
      (Restated.Vocabulary.Execution.Setup.a M S r) := by
  obtain ⟨τ, hl, hτ⟩ := hn
  obtain ⟨hvaw, out, hout, hemit⟩ := Restated.tick_outcome_of_mem_sent_diff facts S Sched x hl hsent
  subst ha
  have h := (Restated.awakeThroughout_window_of_tick_emit facts S Sched x hl
    (fun t ht => hhon t (by rw [← hτ]; exact ht)) (Finset.mem_sdiff.1 hvaw).1 hout hemit hr).2.2
  rw [hτ] at h
  exact h

/-- A validator awake from round `r`'s grade-2 window start to round `r`'s action instant, and not
    held by the adversary at that instant, is in `HonRound S Sched r`. -/
theorem mem_honRound_of_window (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    {r : Round} {v : V}
    (hwin : v ∈ Sched.awakeThroughout (M.early S.E S.hc r .g2 - S.E.Δ)
      (Restated.Vocabulary.Execution.Setup.a M S r))
    (hadv : v ∉ Sched.adv (Restated.Vocabulary.Execution.Setup.a M S r)) :
    v ∈ Restated.HonRound M S Sched r :=
  Finset.mem_sdiff.2 ⟨hwin, hadv⟩

/-- If, at round `r`'s action tick, step `k`, an outcome of the tick of a validator `v` awake and not
    held by the adversary there sends an attestation `a` of round `r`, `v` is honest up to round
    `r`'s action instant, then `v` is in `HonRound S Sched r`.

    Variables: `r` the round, `k` its action tick step, `v` the sender, `out` the tick's outcome,
    `a` the attestation. -/
theorem honRound_of_attestation_sent (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    {r : Round} {k : Nat} (htick : Restated.tickStepAt M x k (Restated.Vocabulary.Execution.Setup.a M S r))
    -- the grade-2 window start of round `r` is at or after time `0`
    (hr : 0 ≤ M.early S.E S.hc r .g2 - S.E.Δ)
    {v : V}
    (hawk : v ∈ Sched.awake (Restated.Vocabulary.Execution.Setup.a M S r) \
      Sched.adv (Restated.Vocabulary.Execution.Setup.a M S r))
    -- `v` is not held by the adversary at any time up to round `r`'s action instant
    (hhon : ∀ t ≤ Restated.Vocabulary.Execution.Setup.a M S r, v ∉ Sched.adv t)
    {out : M.N × List (NamedObject V)}
    (hout : M.tick (Setup.alwaysAwake S) v
      (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S r) x[k] v)
      (Restated.Vocabulary.Execution.Setup.a M S r) ⇢ out)
    {a : NamedAttestation V} (hemit : NamedObject.attest a ∈ out.2) (ha : a.round = r) :
    v ∈ Restated.HonRound M S Sched r := by
  obtain ⟨τ, hl, hτ⟩ := htick
  subst ha
  rw [← hτ] at hout hawk
  have h := (Restated.awakeThroughout_window_of_tick_emit facts S Sched x hl
    (fun t ht => hhon t (by rw [← hτ]; exact ht)) (Finset.mem_sdiff.1 hawk).1 hout hemit hr).2.2
  rw [hτ] at h
  exact Restated.mem_honRound_of_window facts S Sched h (hhon _ le_rfl)

/-- If the attestation `a` signed by an honest validator `v` is in the sent log `x[i].sent`, `v` is
    not held by the adversary at any time up to `tB ≥ x[i].time`, then `v` is in
    `HonRound S Sched a.round`.

    Variables: `i` the step, `tB` the honesty bound, `v` the signer, `a` the attestation. -/
theorem honRound_of_attestation_in_log (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hunf : Restated.Unforgeability M S x)
    {v : V} {a : NamedAttestation V} {tB : Int}
    (hv : HonestThroughTime Sched tB v) (hauth : a.val_index = v)
    {i : Nat} (hi : (x[i].time : Int) ≤ tB)
    (ho : (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[i].sent)
    -- the grade-2 window start of `a`'s round is at or after time `0`
    (hr : 0 ≤ M.early S.E S.hc a.round .g2 - S.E.Δ) :
    v ∈ Restated.HonRound M S Sched a.round := by
  obtain ⟨-, k, hki, htick, hawk, out, hout, hemit⟩ :=
    Restated.attest_round_of_sent facts S Sched x hv hunf hauth hi ho
  have hktime : (x[k + 1].time : Int) = Restated.Vocabulary.Execution.Setup.a M S a.round :=
    (Restated.tickStepAt_time facts x htick).1
  have hle : Restated.Vocabulary.Execution.Setup.a M S a.round ≤ tB := by
    rw [← hktime]
    exact le_trans (Restated.time_mono_int facts S Sched x (Nat.succ_le_of_lt hki)) hi
  exact Restated.honRound_of_attestation_sent facts S Sched x htick hr hawk
    (fun t ht => hv t (le_trans ht hle)) hout hemit rfl

/-- An attestation of round `r` that an honest validator `v` sent at round `r`'s action tick, step
    `n`, puts `v` in `HonRound S Sched r`.

    Variables: `r` the round, `n` its action tick step, `v` the sender, `a` the attestation. -/
theorem mem_honRound_of_attested (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    {r : Round} {n : Nat} (hn : Restated.tickStepAt M x n (Restated.Vocabulary.Execution.Setup.a M S r))
    -- the grade-2 window start of round `r` is at or after time `0`
    (hr : 0 ≤ M.early S.E S.hc r .g2 - S.E.Δ)
    {v : V}
    -- `v` is not held by the adversary at any time up to round `r`'s action instant
    (hhon : ∀ t ≤ Restated.Vocabulary.Execution.Setup.a M S r, v ∉ Sched.adv t)
    {a : NamedAttestation V}
    -- `v`'s attestation `a` is new in the sent log at step `n`
    (hsent : (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n + 1].sent - x[n].sent)
    (ha : a.round = r) (hai : a.val_index = v) :
    v ∈ Restated.HonRound M S Sched r :=
  Restated.mem_honRound_of_window facts S Sched
    (Restated.awakeThroughout_window_of_attested facts S Sched x hn hr hhon hsent ha hai)
    (hhon _ le_rfl)

end

end DecoupledConsensusModel.Sts.Restated
