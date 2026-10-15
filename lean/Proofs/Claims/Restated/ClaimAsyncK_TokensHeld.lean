import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bK_GradeForCatchUp
import Proofs.Claims.Restated.Claim13bK_GradeOld
import Proofs.Claims.Restated.Claim13bK_GradeOldHeads
import Proofs.Claims.Restated.Claim13bStepGrade
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bStepKitRecord
import Proofs.Claims.Restated.Claim13bStepKitTick
import Proofs.Claims.Restated.Claim13bSyncView
import Proofs.Claims.Restated.Claim13beRoute3_3
import Proofs.Claims.Restated.ClaimAsyncK_Defs
import Proofs.Claims.Restated.ProcessIdempotent
import Proofs.Claims.Restated.ProcessedFlip
import Proofs.Claims.Restated.Projection
import Proofs.Claims.Restated.RunAll
import Proofs.Claims.Restated.VocabularyAssumptionsLemmas
import Proofs.Claims.Restated.TickOutcomeHonest
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_Alignment
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bK_GradeOldHeads
import Model.Conditions.Claim13bStepKitTick
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Sts_Spec2Claims_ClaimStableThroughAsyncPeriod
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring

/-!
# Tokens held by a reader after a round's action instant

Theorems over a model `M : Record.Model V` with facts `facts : Record.Facts M`: an honest attester's
round-`ρ` attestation is sent at its tick, delivered to an awake reader before `S.a ρ + Δ`, held in
its pool, raw and ready in the grades of the following rounds, and the block it names resolves in
the reader's tree.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

local macro "pGF% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13bK_GradeFor)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If `ρ + 1 ≤ q`, then `S.a ρ + Δ ≤ Protocol.early S.E S.hc q p` for every phase `p`. -/
theorem action_delta_le_early_of_lt (facts : Record.Facts M) (S : Setup V) {ρ q : Nat} (hq : ρ + 1 ≤ q)
    (p : Protocol.Phase) :
    (Restated.Vocabulary.Execution.Setup.a M S ρ) + S.E.Δ ≤ M.early S.E S.hc q p := by
  have h1 := Restated.action_delta_le_early_succ_kit facts S ρ
  have h2 : M.early S.E S.hc (ρ + 1) .g2 ≤ M.early S.E S.hc q .g2 := by
    rw [Restated.early_g2_eq_healA facts, Restated.early_g2_eq_healA facts]
    linarith [Restated.healA_mono facts S hq]
  exact le_trans h1 (le_trans h2 (Restated.early_g2_le_early facts S q p))

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If `ρ + 1 ≤ q` and `m` is the last step before round `q`'s phase-`p` instant, then
    `S.a ρ + Δ ≤ x[m].time`. -/
theorem action_delta_le_time_of_stepBefore (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (htd : Restated.TimeDiverges M x) {ρ q : Nat} (hq : ρ + 1 ≤ q)
    {m : Nat} {p : Protocol.Phase}
    (hm : Restated.stepBeforeInstant M x m (M.domain S.E S.hc q p)) :
    (Restated.Vocabulary.Execution.Setup.a M S ρ) + S.E.Δ ≤ (x[m].time : Int) := by
  have hpos : 0 < (Restated.Vocabulary.Execution.Setup.a M S ρ) + S.E.Δ := by linarith only [Restated.action_pos facts S ρ, S.E.Δ_pos]
  obtain ⟨k_1, hk_1⟩ := Restated.exists_tickStepAt facts x htd hpos
  have hk_1succ := (Restated.tickStepAt_time facts x hk_1).1
  have hlt : (Restated.Vocabulary.Execution.Setup.a M S ρ) + S.E.Δ < M.domain S.E S.hc q p :=
    lt_of_le_of_lt (le_trans (Restated.action_delta_le_early_of_lt facts S hq .g2) le_rfl)
      (facts.gr.early_g2_lt_domain S q p)
  have hk_1m : k_1 < m := by
    by_contra hcon
    have h := hm.2 k_1 (Nat.le_of_not_lt hcon)
    rw [hk_1succ] at h
    exact absurd h (not_le_of_gt hlt)
  rw [← hk_1succ]
  exact Restated.time_mono_int facts S Sched x (Nat.succ_le_of_lt hk_1m)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- A member of `attestersAt S Sched ρ` is a member of `attestersAt S Sched ρ`: the window
    `wAttest S ≥ 12Δ` before `S.a ρ` contains the rule's grade-2 window of round `ρ`. -/
theorem attestersAt_of_activeRoundW (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    {ρ : Nat} {v : V} (hv : v ∈ Restated.activeRoundW M S Sched ρ) :
    v ∈ Restated.attestersAt M S Sched ρ := by
  have h1 := Restated.early_g2_eq_healA facts S ρ
  have h2 := twelve_delta_le_wAttest_kit S
  have hle : (M.a S.hc S.E.Δ ρ) - wAttest S ≤ M.early S.E S.hc ρ .g2 - S.E.Δ := by
    rw [h1]; linarith
  exact awakeThroughout_sub Sched hle le_rfl hv

/-- If every tick at a multiple of `Δ` of a validator awake there and not held up to it has an
    outcome, step `n` is the tick step at `S.a ρ`, `v_1` is awake at every time of round `ρ`'s
    attester window, and the adversary holds `v_1` at no time up to a step `m` whose time is at or
    after `S.a ρ`, then every attestation `v_1`'s round-`ρ` action read can compute from its node
    state at step `n` is among the messages step `n` added to the sent log `x[n + 1].sent`, and the
    adversary does not hold `v_1` at the time step `n` starts from. -/
theorem attest_honestSend_of_attestersAt (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    {ρ n m : Nat} (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S ρ)))
    {v_1 : V} (hv_1 : v_1 ∈ Restated.attestersAt M S Sched ρ) (hv_1m : Restated.HonestThrough M Sched x m v_1)
    (hm : (Restated.Vocabulary.Execution.Setup.a M S ρ) ≤ (x[m].time : Int))
    (hnr : ∀ (k τ : Nat) (u : V), x.lbl k = AtomicAction.tickAllAwake τ →
      (τ : Int) % S.E.Δ = 0 → u ∈ Sched.awake (τ : Int) \ Sched.adv (τ : Int) →
      (∀ t' ≤ (τ : Int), u ∉ Sched.adv t') →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) u (Record.wakeStage M Sched (τ : Int) x[k] u) (τ : Int) ⇢ out) :
    ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v_1].st) v_1 ρ,
    Restated.HonestSendAt M S x n (⟨v_1, NamedObject.attest a⟩
      : SignedMsg V (NamedObject V)) := by
  have _hr_0 : M.reachedNode (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S ρ) x[n] v_1) := Record.reachedNode_wakeStage facts S Sched x n v_1 (Restated.Vocabulary.Execution.Setup.a M S ρ)
  intro a ha
  obtain ⟨t', hlbl, ht'⟩ := id hn
  have hn0 := (Restated.tickStepAt_time facts x hn).2
  have hW : 0 ≤ wAttest S := by
    have := twelve_delta_le_wAttest_kit S
    linarith [S.E.Δ_pos]
  have hawT : v_1 ∈ Sched.awakeThroughout (M.early S.E S.hc ρ .g2 - S.E.Δ)
      ((Restated.Vocabulary.Execution.Setup.a M S ρ)) := hv_1
  have hawake : v_1 ∈ Sched.awake ((Restated.Vocabulary.Execution.Setup.a M S ρ)) := by
    have h1 := Restated.early_g2_eq_healA facts S ρ
    have hd := S.E.Δ_pos
    exact mem_awake_of_mem_awakeThroughout Sched hawT (by show _ ≤ M.a S.hc S.E.Δ ρ; rw [h1]; linarith) le_rfl
  have hhon : v_1 ∉ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S ρ)) := hv_1m _ hm
  have hq : v_1 ∈ Sched.awake (t' : Int) \ Sched.adv (t' : Int) := by
    rw [ht']; exact Finset.mem_sdiff.2 ⟨hawake, hhon⟩
  have hdvd : (t' : Int) % S.E.Δ = 0 := by rw [ht']; exact Restated.action_emod_delta facts S ρ
  have hhonUp : ∀ t'' ≤ (t' : Int), v_1 ∉ Sched.adv t'' := fun t'' h =>
    hv_1m t'' (by rw [ht'] at h; linarith)
  have hrun : M.awake_for_grade2 (Setup.alwaysAwake S) v_1
      (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S ρ) x[n] v_1) ρ :=
    Restated.run_fact_g2 facts S Sched x n t' ρ v_1 hlbl ht' hawT hhonUp
  refine ⟨?_, hv_1m _ (by linarith)⟩
  refine Restated.mem_sent_diff_of_tick facts S Sched x hlbl hq ?_
    (hnr n t' v_1 hlbl hdvd hq hhonUp)
  rw [ht']
  intro out hout
  have _hv_s1 := Record.runs_as_wakeStage facts S Sched x (n) v_1 (Restated.Vocabulary.Execution.Setup.a M S ρ)
  exact Restated.namedTick_emits_attest facts S v_1 _ ρ hrun out hout a (by have h := ha; simp only [Restated.actionAttestationFrom_wakeStage facts] at h ⊢; exact h)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Under `SynchronyFromWakeOutside S x b₀ b₁`, with `S.a ρ + Δ ≤ b₀`, GST at or before `S.a ρ`, and
    every tick at a multiple of `Δ` of a validator awake there and not held up to it having an
    outcome: if step `n` is the tick step at `S.a ρ`, `v_1` is an honest member of
    `attestersAt S Sched ρ` through a step `m` with `S.a ρ + Δ ≤ x[m].time`, and `w` is awake at
    every time from `S.a ρ` to `x[m].time`, then every attestation `v_1`'s round-`ρ` action read can
    compute from its node state at step `n` is delivered to `w` at a step `d` after `n`, at a time
    of `[S.a ρ, S.a ρ + Δ)`. -/
theorem token_delivered_before_period (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {b₀ b₁ : Int}
    (hsync : Restated.SynchronyFromWakeOutside M S x b₀ b₁) {ρ n m : Nat} (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S ρ)))
    (hgst : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S ρ)) (hb₀ : (Restated.Vocabulary.Execution.Setup.a M S ρ) + S.E.Δ ≤ b₀)
    {v_1 w : V} (hv_1 : v_1 ∈ Restated.attestersAt M S Sched ρ) (hv_1m : Restated.HonestThrough M Sched x m v_1)
    (hm : (Restated.Vocabulary.Execution.Setup.a M S ρ) + S.E.Δ ≤ (x[m].time : Int))
    (hw : w ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S ρ)) (x[m].time : Int))
    (hnr : ∀ (k τ : Nat) (u : V), x.lbl k = AtomicAction.tickAllAwake τ →
      (τ : Int) % S.E.Δ = 0 → u ∈ Sched.awake (τ : Int) \ Sched.adv (τ : Int) →
      (∀ t' ≤ (τ : Int), u ∉ Sched.adv t') →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) u (Record.wakeStage M Sched (τ : Int) x[k] u) (τ : Int) ⇢ out) :
    ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v_1].st) v_1 ρ,
    ∃ d : Nat, n < d ∧
      x.lbl d = AtomicAction.deliver w ⟨v_1, NamedObject.attest a⟩ ∧
      (Restated.Vocabulary.Execution.Setup.a M S ρ) ≤ (x[d].time : Int) ∧ (x[d].time : Int) < (Restated.Vocabulary.Execution.Setup.a M S ρ) + S.E.Δ := by
  intro a ha
  have hd := S.E.Δ_pos
  obtain ⟨hn1, hn0⟩ := Restated.tickStepAt_time facts x hn
  have hsend := Restated.attest_honestSend_of_attestersAt facts S Sched x hn hv_1 hv_1m
    (show (Restated.Vocabulary.Execution.Setup.a M S ρ) ≤ (x[m].time : Int) by linarith) hnr a ha
  have hmax : max (x[n].time : Int) S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S ρ) := max_le (by linarith) hgst
  have hwin := Restated.receiverWindowA_of_tick facts S x hn hgst hm hw
  obtain ⟨d, hnd, hlbl, -, hlt⟩ :=
    Restated.deliver_before_period facts S x hsync hsend (by linarith) hwin
  refine ⟨d, hnd, hlbl, ?_, by linarith⟩
  rw [← hn1]
  exact Restated.time_mono_int facts S Sched x hnd

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If at the delivery step `k` the validator `w` already held that sender's head for the
    attestation's round, or the attestation's row was written into `w`'s bucket at `k + 1` with the
    stamp `w`'s clock had at `k`, then at every step `m` at or after `k + 1` the SG-vote projection
    of the attestation is in `w`'s grade-view pool of its round and carries a stamp at or before
    `x[k].time`. -/
theorem token_pooled_stamped_of_record (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    {k m : Nat} {w : V} {a : NamedAttestation V}
    (hk1m : k + 1 ≤ m)
    (hcase : a.erase.confirmed ∈ M.round_votes (x[k][w].st).st.core a.erase ∨
      (a ∈ (x[k + 1][w].st).st.sg_rows a.round ∧
        (x[k + 1][w].st).st.core.timestamp_sg_vote (M.sgVote a.erase)
          = some (((x[k][w].st).st.core.t : Stamp)))) :
    M.sgVote a.erase ∈ (M.gradeView (M.toHealing (x[m][w].st).st.core)).sg_votes a.round ∧
      ∃ stamp : Int, stamp ≤ (x[k].time : Int) ∧
        (x[m][w].st).st.core.timestamp_sg_vote (M.sgVote a.erase)
          = some ((stamp : Stamp)) := by
  have hkm : k ≤ m := le_trans (Nat.le_succ k) hk1m
  have ha_eround : a.erase.round = a.round := namedAttestation_erase_round a
  rcases hcase with hheld | ⟨h1, hstamp⟩
  · obtain ⟨c, hcpool, hcidx, hcconf⟩ := (Restated.Vocabulary.Proofs.Optimistic.mem_round_votes facts).mp hheld
    have hpv := Restated.poolView_sts facts S Sched x k w a.erase.round
    have hclist := (facts.sto.Sts_mem_sg_pool_iff _ _ c).mp hcpool
    rw [hpv] at hclist
    obtain ⟨B, hB, hBc⟩ := List.mem_map.mp hclist
    obtain ⟨hBround, stamp, hstampLe, hts⟩ :=
      (Restated.sgRowData_sts facts S Sched x k w).2 a.erase.round B hB
    have hBmem : B ∈ (x[k][w].st).st.sg_rows B.round := by rw [hBround]; exact hB
    have hsg : M.sgVote B.erase = M.sgVote a.erase := by
      rw [hBc]
      have hcround : c.round = a.erase.round := by
        rw [← hBc]; exact (namedAttestation_erase_round B).trans hBround
      exact facts.sto.sgVote_eq_of_fields hcidx hcround hcconf
    obtain ⟨hmem_m, hts_m⟩ := Restated.sgRow_stamp_mono_sts facts S Sched x w hkm hBmem
    refine ⟨?_, stamp, hstampLe, ?_⟩
    · have hpool := Restated.sgRow_erase_mem_pool_sts facts S Sched x m w B hmem_m
      rw [hBround, ha_eround] at hpool
      rw [← hsg, facts.gr.gradeView_sg_votes]
      exact Finset.mem_image_of_mem M.sgVote hpool
    · rw [← hsg, hts_m, hts]
  · obtain ⟨hmem_m, hts_m⟩ := Restated.sgRow_stamp_mono_sts facts S Sched x w hk1m h1
    refine ⟨?_, (x[k][w].st).st.core.t, Restated.clock_le_time_sts facts S Sched x k w, ?_⟩
    · have hpool := Restated.sgRow_erase_mem_pool_sts facts S Sched x m w a hmem_m
      rw [facts.gr.gradeView_sg_votes]
      exact Finset.mem_image_of_mem M.sgVote hpool
    · rw [hts_m, hstamp]

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Under `SynchronyFromWakeOutside S x b₀ b₁`, with `S.a ρ + Δ ≤ b₀` and GST at or before `S.a ρ`:
    if step `n` is the tick step at `S.a ρ`, `v_1` is an honest member of `attestersAt S Sched ρ`
    through a step `m` with `S.a ρ + Δ ≤ x[m].time`, and `w` is honest through `m` and awake at
    every time from `S.a ρ` to `x[m].time`, then for every attestation `a` that `v_1`'s round-`ρ`
    action read can compute from its node state at step `n`, `w`'s grade view after `m` steps holds
    the SG-vote projection of `a` in its pool of round `ρ`, with a stamp strictly before
    `S.a ρ + Δ`. -/
theorem token_held_before_period (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {b₀ b₁ : Int} (hsync : Restated.SynchronyFromWakeOutside M S x b₀ b₁) {ρ n m : Nat}
    (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S ρ))) (hgst : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S ρ)) (hb₀ : (Restated.Vocabulary.Execution.Setup.a M S ρ) + S.E.Δ ≤ b₀)
    {v_1 w : V} (hv_1 : v_1 ∈ Restated.attestersAt M S Sched ρ) (hv_1m : Restated.HonestThrough M Sched x m v_1)
    (hm : (Restated.Vocabulary.Execution.Setup.a M S ρ) + S.E.Δ ≤ (x[m].time : Int))
    (hw : w ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S ρ)) (x[m].time : Int))
    (hwm : Restated.HonestThrough M Sched x m w) :
    ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v_1].st) v_1 ρ,
    M.sgVote a.erase ∈ (M.gradeView (M.toHealing (x[m][w].st).st.core)).sg_votes ρ ∧
      ∃ stamp : Int, stamp < (Restated.Vocabulary.Execution.Setup.a M S ρ) + S.E.Δ ∧
        (M.gradeView (M.toHealing (x[m][w].st).st.core)).timestamp_sg_vote (M.sgVote a.erase)
          = some ((stamp : Stamp)) := by
  intro a ha
  have ha_round : a.round = ρ :=
    Restated.actionAttestationFrom_round facts (Setup.alwaysAwake S) _ v_1 ρ a ha
  have ha_idx : a.val_index = v_1 :=
    Restated.actionAttestationFrom_val_index facts (Setup.alwaysAwake S) _ v_1 ρ a ha
  have hd := S.E.Δ_pos
  obtain ⟨d, hnd, hlbl, hdlo, hdlt⟩ :=
    Restated.token_delivered_before_period facts S Sched x hsync hn hgst hb₀ hv_1 hv_1m hm hw
      (fun k τ u hl _ => facts.ndRun.tick_outcome_sts S Sched x hexec.idealization.root_injective hexec.honestRootsNew k τ u hl) a ha
  have hdm : d < m := by
    by_contra hcon
    have h := Restated.time_mono_int facts S Sched x (Nat.le_of_not_lt hcon)
    linarith
  have hd1m : d + 1 ≤ m := Nat.succ_le_of_lt hdm
  have hdtime : (x[d + 1].time : Int) = (x[d].time : Int) := by
    exact_mod_cast congrArg (fun j : Nat => (j : Int)) (Restated.deliver_time facts S Sched x hlbl)
  have hd1le : (x[d + 1].time : Int) ≤ (x[m].time : Int) := Restated.time_mono_int facts S Sched x hd1m
  have hview : (⟨v_1, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[d + 1][w].view :=
    Restated.mem_view_succ_of_deliver facts S Sched x hlbl
  have haw : AtomicAwake x (d + 1) w :=
    mem_awake_of_awakeThroughout Sched hw (by rw [hdtime]; exact hdlo) hd1le
  have hv : HonestThroughTime Sched (x[d + 1].time : Int) v_1 := fun t ht =>
    hv_1m t (le_trans ht hd1le)
  have hawT : w ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S a.round)) (x[d + 1].time : Int) := by
    rw [ha_round]
    exact awakeThroughout_mono Sched hw le_rfl hd1le
  have hwh : w ∉ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S a.round)) := by
    rw [ha_round]; exact hwm _ (by linarith)
  have hexp : (M.round_of S.hc (S.E.slotOf (x[d + 1].time : Int))) ≤ a.round + S.hc.η_SG := by
    rw [ha_round]
    refine Restated.hexp_of_domain facts S ?_
    rw [hdtime]
    have h1 := Restated.healA_succ facts S ρ
    have h2 := twelve_delta_le_wAttest_kit S
    have h3 : (x[d].time : Int) < (M.a S.hc S.E.Δ ρ) + S.E.Δ := hdlt
    show (x[d].time : Int) ≤ (M.a S.hc S.E.Δ (ρ + 1))
    linarith
  have hroom : ∀ k : Nat, k < d + 1 →
      x.lbl k = AtomicAction.deliver w ⟨v_1, NamedObject.attest a⟩ →
      (M.round_votes (x[k][w].st).st.core a.erase).card ≠ 2 := by
    intro k hk _
    have hkm : k ≤ m := le_trans (Nat.le_of_lt_succ hk) (le_of_lt hdm)
    exact Restated.hroom_of_fresh facts S Sched x hexec hn
      (fun t ht => hv_1m t (le_trans ht (Restated.time_mono_int facts S Sched x hkm))) a ha
  obtain ⟨k, hkj, -, hcase⟩ :=
    Restated.attest_recorded_of_mem_view_recv facts S Sched x hview haw hv
      (fun t ht => hwm t (le_trans ht (Restated.time_mono_int facts S Sched x hd1m)))
      hexec.toUnforgeability ha_idx hexp hroom
      (fun k τ u hl hmem hhon => facts.ndRun.tick_outcome_sts S Sched x hexec.idealization.root_injective
        hexec.honestRootsNew k τ u hl hmem hhon)
      (fun k _ _ => facts.nd.process_nonempty _ _ _ (fun _ h => by cases h))
  have hk1m : k + 1 ≤ m := le_trans (Nat.succ_le_of_lt hkj) hd1m
  have hkt : (x[k].time : Int) ≤ (x[d].time : Int) :=
    Restated.time_mono_int facts S Sched x (Nat.le_of_lt_succ hkj)
  have hkey := Restated.token_pooled_stamped_of_record facts S Sched x hk1m
    (hcase.imp id (fun h => ⟨h.1, h.2.2⟩))
  rw [ha_round] at hkey
  obtain ⟨hmem, stamp, hstampLe, hts⟩ := hkey
  exact ⟨hmem, stamp, by linarith, by rw [facts.gr.gradeView_timestamp_sg_vote]; exact hts⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- On the premises of `token_held_before_period`, for every round `q` with `ρ + 1 ≤ q ≤ ρ + η_SG`,
    every cutoff `c ≥ S.a ρ + Δ` and every attestation `a` that `v_1`'s round-`ρ` action read can
    compute, the SG-vote projection of `a` is in every outcome of `v_1`'s raw inputs to `w`'s
    round-`q` grade at `c`, and its token is in every outcome of `v_1`'s raw view there. -/
theorem token_raw_in_view (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {b₀ b₁ : Int} (hsync : Restated.SynchronyFromWakeOutside M S x b₀ b₁) {ρ n m : Nat}
    (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S ρ))) (hgst : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S ρ)) (hb₀ : (Restated.Vocabulary.Execution.Setup.a M S ρ) + S.E.Δ ≤ b₀)
    {v_1 w : V} (hv_1 : v_1 ∈ Restated.attestersAt M S Sched ρ) (hv_1m : Restated.HonestThrough M Sched x m v_1)
    (hm : (Restated.Vocabulary.Execution.Setup.a M S ρ) + S.E.Δ ≤ (x[m].time : Int))
    (hw : w ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S ρ)) (x[m].time : Int))
    (hwm : Restated.HonestThrough M Sched x m w)
    {q : Nat} (hq₁ : ρ + 1 ≤ q) (hq₂ : q ≤ ρ + S.hc.η_SG) {c : Int}
    (hc : (Restated.Vocabulary.Execution.Setup.a M S ρ) + S.E.Δ ≤ c) :
    ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v_1].st) v_1 ρ,
    (∀ X, M.rawInputs (M.gradeView (M.toHealing (x[m][w].st).st.core)) S.hc.η_SG q c v_1 ⇢ X →
        M.sgVote a.erase ∈ X) ∧
      (∀ W, M.rawView (M.gradeView (M.toHealing (x[m][w].st).st.core)) S.hc.η_SG q c v_1 ⇢ W →
        M.token (M.sgVote a.erase) ∈ W) := by
  intro a ha
  obtain ⟨hmem, stamp, hlt, hts⟩ :=
    Restated.token_held_before_period facts S Sched x hexec hsync hn hgst hb₀ hv_1 hv_1m hm hw hwm
      a ha
  have hlo : q - S.hc.η_SG ≤ ρ := by omega
  have hhi : ρ < q := by omega
  have hwin : ρ ∈ M.latest_window S.hc.η_SG q :=
    facts.fc.mem_latest_window hlo hhi
  have hraw : ∀ X, M.rawInputs (M.gradeView (M.toHealing (x[m][w].st).st.core)) S.hc.η_SG q c v_1 ⇢ X →
      M.sgVote a.erase ∈ X :=
    facts.gr.mem_rawInputs_of_stamp _ S.hc.η_SG q ρ c v_1 hwin hmem
      ((facts.sto.sgVote_val _).trans
        (Restated.actionAttestationFrom_val_index facts (Setup.alwaysAwake S) (x[n][v_1].st) v_1 ρ a ha))
      hts (lt_of_lt_of_le hlt hc)
  refine ⟨hraw, fun W hW => ?_⟩
  obtain ⟨X, hX⟩ := facts.gr.rawInputs_nonempty (M.gradeView (M.toHealing (x[m][w].st).st.core))
    S.hc.η_SG q c v_1
  exact (facts.gr.mem_rawView_iff _ _ _ _ _ _ W hW X hX).mpr ⟨_, hraw X hX, rfl⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Under `SynchronyFromWakeOutside S x b₀ b₁` and `CatchUpOnWakeOutside S x b₀ b₁`, with
    `S.a ρ + Δ ≤ b₀` and GST at or before `S.a ρ`: if `n` is the tick step at `S.a ρ`, `v_1` is
    honest through `n + 1` and holds the named block `C` among its bodies there, `w` is honest
    through a step `m` with `S.a ρ + Δ ≤ x[m].time` and awake at every time from `S.a ρ` to
    `x[m].time`, and at every delivery of `C` to `w` at a time at or before `S.a ρ + Δ` `w`'s
    finalized block is an ancestor of `C` or `w` already holds `C`, then `C`'s erasure is in `w`'s
    tree after `m` steps, stamped strictly before `S.a ρ + Δ`. -/
theorem block_held_before_period (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {b₀ b₁ : Int} (hsync : Restated.SynchronyFromWakeOutside M S x b₀ b₁)
    (hcatch : Restated.CatchUpOnWakeOutside M S x b₀ b₁) (hmult : AwakeAtMultiples S Sched)
    (htd : Restated.TimeDiverges M x) {ρ n m : Nat} (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S ρ)))
    (hgst : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S ρ)) (hb₀ : (Restated.Vocabulary.Execution.Setup.a M S ρ) + S.E.Δ ≤ b₀)
    {v_1 : V} (hv_1 : Restated.HonestThrough M Sched x (n + 1) v_1) {C : NamedBlock V}
    (hC : C ∈ (x[n + 1][v_1].st).st.bodies) {w : V}
    (hm : (Restated.Vocabulary.Execution.Setup.a M S ρ) + S.E.Δ ≤ (x[m].time : Int))
    (hw : w ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S ρ)) (x[m].time : Int))
    (hwm : Restated.HonestThrough M Sched x m w)
    (hadm : Restated.ReaderAdmitsInPhase M S Sched x 0 ((Restated.Vocabulary.Execution.Setup.a M S ρ) + S.E.Δ) w C) :
    C.erase ∈ (x[m][w].st).st.core.T ∧
      ∃ σ : Stamp, (x[m][w].st).st.core.timestamp_block C.erase = some σ ∧
        σ < (((Restated.Vocabulary.Execution.Setup.a M S ρ) + S.E.Δ : Int) : Stamp) := by
  classical
  have hd := S.E.Δ_pos
  obtain ⟨hn1, hn0⟩ := Restated.tickStepAt_time facts x hn
  by_cases hgen : C = NamedBlock.genesis
  · subst hgen
    have hgb : (NamedBlock.genesis : NamedBlock V) ∈ (x[m][w].st).st.bodies :=
      ((Restated.nodeInvariant_sts facts S Sched x m w).1.1.1.2.2.1).1
    refine ⟨?_, ⊥, ?_, WithBot.bot_lt_coe _⟩
    · rw [Restated.bodies_image_eq_T facts S Sched x m w]
      exact Finset.mem_image_of_mem NamedBlock.erase hgb
    · refine Restated.block_stamp_carry facts S Sched x (Nat.zero_le m) w ?_
      have hge : (NamedBlock.genesis : NamedBlock V).erase = Block.genesis := erase_named_genesis
      rw [Record.st_zero M S Sched x w, hge]
      exact facts.nd.initial_timestamp_genesis _ _
  obtain ⟨i, k, v_0, him, hmemi, -, hkt, hnk, hnk1, hsend⟩ :=
    Restated.honestSend_of_holder facts S Sched x hC hv_1 hgen
  have hin : (x[i].time : Int) ≤ (x[n].time : Int) :=
    Restated.time_mono_int facts S Sched x (Nat.le_of_lt_succ him)
  have hki : (x[k].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S ρ) - 1 := by linarith
  have hdel : ∃ d : Nat, x.lbl d = AtomicAction.deliver w
        (⟨v_0, NamedObject.block C⟩ : SignedMsg V (NamedObject V)) ∧
      (x[i + 1].time : Int) ≤ (x[d].time : Int) ∧ (x[d].time : Int) < (Restated.Vocabulary.Execution.Setup.a M S ρ) + S.E.Δ := by
    by_cases hA : w ∈ Sched.awakeThroughout (x[k + 1].time : Int) ((Restated.Vocabulary.Execution.Setup.a M S ρ))
    · have hmax : max (x[k].time : Int) S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S ρ) := max_le (by linarith) hgst
      have hwin : w ∈ Sched.awakeThroughout (x[k + 1].time : Int)
          (max (x[k].time : Int) S.E.t_GST + S.E.Δ) := by
        refine mem_awakeThroughout_of_forall Sched (fun t h0 h1 => ?_)
        by_cases ht : t ≤ (Restated.Vocabulary.Execution.Setup.a M S ρ)
        · exact mem_awake_of_mem_awakeThroughout Sched hA h0 ht
        · exact mem_awake_of_mem_awakeThroughout Sched hw (by linarith) (by linarith)
      obtain ⟨d, hkd, hlbl, -, hlt⟩ := Restated.deliver_before_period facts S x hsync hsend (by linarith) hwin
      refine ⟨d, hlbl, ?_, by linarith⟩
      exact le_trans hnk (Restated.time_mono_int facts S Sched x hkd)
    ·
      let A : Finset Int := (Finset.Icc (x[k + 1].time : Int) ((Restated.Vocabulary.Execution.Setup.a M S ρ))).filter
        (fun t => w ∉ Sched.awake t)
      have hne : A.Nonempty := by
        by_contra hempty
        apply hA
        refine mem_awakeThroughout_of_forall Sched (fun t h0 h1 => ?_)
        by_contra hnot
        exact hempty ⟨t, Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨h0, h1⟩, hnot⟩⟩
      set t' := A.max' hne with ht'
      have ht'mem : t' ∈ A := Finset.max'_mem A hne
      obtain ⟨ht'Icc, ht'asleep⟩ := Finset.mem_filter.1 ht'mem
      obtain ⟨ht'lo, ht'hi⟩ := Finset.mem_Icc.1 ht'Icc
      have hwρ : w ∈ Sched.awake ((Restated.Vocabulary.Execution.Setup.a M S ρ)) :=
        mem_awake_of_mem_awakeThroughout Sched hw le_rfl (by linarith)
      have ht'lt : t' < (Restated.Vocabulary.Execution.Setup.a M S ρ) := by
        rcases lt_or_eq_of_le ht'hi with h | h
        · exact h
        · exact absurd (h ▸ hwρ) ht'asleep
      have hawake_after : ∀ t : Int, t' + 1 ≤ t → t ≤ (x[m].time : Int) → w ∈ Sched.awake t := by
        intro t h0 h1
        by_cases htρ : t ≤ (Restated.Vocabulary.Execution.Setup.a M S ρ)
        · by_contra hnot
          have htA : t ∈ A :=
            Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨by linarith, htρ⟩, hnot⟩
          have := Finset.le_max' A t htA
          rw [← ht'] at this
          linarith
        · exact mem_awake_of_mem_awakeThroughout Sched hw (by linarith) h1
      have hmaxw : max (t' + 1) S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S ρ) := max_le (by linarith) hgst
      have hdl : deadlineOutside S b₀ b₁ (t' + 1) = max (t' + 1) S.E.t_GST + S.E.Δ :=
        deadlineOutside_of_le S (by linarith)
      have hwthr : w ∈ Sched.awakeThroughout (t' + 1) (deadlineOutside S b₀ b₁ (t' + 1)) := by
        rw [hdl]
        exact mem_awakeThroughout_of_forall Sched (fun t h0 h1 =>
          hawake_after t h0 (by linarith))
      have hkt' : (x[k].time : Int) < t' + 1 := by
        have := Restated.time_mono_int facts S Sched x (Nat.le_succ k)
        linarith
      have hprev : w ∉ Sched.awake (t' + 1 - 1) := by
        rw [add_sub_cancel_right]; exact ht'asleep
      obtain ⟨d, -, hlbl, hdlo, hdhi⟩ :=
        hcatch k w _ (t' + 1) hsend hkt'
          (hawake_after (t' + 1) le_rfl (by linarith)) hprev hwthr
      rw [hdl] at hdhi
      exact ⟨d, hlbl, by linarith, by linarith⟩
  obtain ⟨d, hdlbl, hdlo, hdlt⟩ := hdel
  have hdm : d < m := by
    by_contra hcon
    have h := Restated.time_mono_int facts S Sched x (Nat.le_of_not_lt hcon)
    linarith
  have hwh : Restated.HonestThrough M Sched x d w := fun t ht =>
    hwm t (le_trans ht (Restated.time_mono_int facts S Sched x (le_of_lt hdm)))
  have hbody : C ∈ (x[d + 1][w].st).st.bodies :=
    Restated.block_admitted_of_deliver_ofAdmits facts S Sched x hexec hmult htd hadm hdlbl hwh hmemi hgen
      hdlo (Int.natCast_nonneg _) (le_of_lt hdlt)
      (fun n' t' hn' hΔ hq _ hhi' => Restated.tick_outcome_of_tickStepAt_honest facts S Sched x
        hexec.idealization.root_injective hexec.honestRootsNew hn' hΔ hq (fun t'' ht'' => hwh t'' (le_trans ht'' hhi')))
  have hdtime : (x[d + 1].time : Int) = (x[d].time : Int) := by
    exact_mod_cast congrArg (fun j : Nat => (j : Int)) (Restated.deliver_time facts S Sched x hdlbl)
  have hdm1 : d + 1 ≤ m := Nat.succ_le_of_lt hdm
  have hbodym : C ∈ (x[m][w].st).st.bodies :=
    of_decide_eq_true (Restated.processed_mono facts S Sched x w (NamedObject.block C) hdm1
      (decide_eq_true hbody))
  refine ⟨?_, ?_⟩
  · rw [Restated.bodies_image_eq_T facts S Sched x m w]
    exact Finset.mem_image_of_mem NamedBlock.erase hbodym
  · have hmemTd : C.erase ∈ (x[d + 1][w].st).st.core.T := by
      rw [Restated.bodies_image_eq_T facts S Sched x (d + 1) w]
      exact Finset.mem_image_of_mem NamedBlock.erase hbody
    obtain ⟨σ, hσ, hσlt⟩ :=
      Restated.block_stamp_lt_of_time facts S Sched x (d + 1) w (Γ := (Restated.Vocabulary.Execution.Setup.a M S ρ) + S.E.Δ) hmemTd
        (by rw [hdtime]; exact hdlt)
    exact ⟨σ, Restated.block_stamp_carry facts S Sched x hdm1 w hσ, hσlt⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- On the premises of `block_held_before_period` for every body `C` of `v_1` after the tick that
    some attestation of `v_1`'s round-`ρ` action read names: if the attestation `a` of that action
    read names the root `root`, then some body `C` of `v_1` after the tick has the root `root`,
    `w`'s tree after `m` steps resolves `root` to `C.erase`, and that block is stamped there before
    every cutoff `c ≥ S.a ρ + Δ`. -/
theorem attested_block_resolves (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {b₀ b₁ : Int} (hsync : Restated.SynchronyFromWakeOutside M S x b₀ b₁)
    (hcatch : Restated.CatchUpOnWakeOutside M S x b₀ b₁) (hmult : AwakeAtMultiples S Sched)
    (htd : Restated.TimeDiverges M x) {ρ n m : Nat} (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S ρ)))
    (hgst : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S ρ)) (hb₀ : (Restated.Vocabulary.Execution.Setup.a M S ρ) + S.E.Δ ≤ b₀)
    {v_1 : V} (hv_1m : Restated.HonestThrough M Sched x m v_1) {w : V}
    (hm : (Restated.Vocabulary.Execution.Setup.a M S ρ) + S.E.Δ ≤ (x[m].time : Int))
    (hw : w ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S ρ)) (x[m].time : Int))
    (hwm : Restated.HonestThrough M Sched x m w)
    (hadm : ∀ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies →
      ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v_1].st) v_1 ρ,
      a.confirmed = some C.root →
      Restated.ReaderAdmitsInPhase M S Sched x 0 ((Restated.Vocabulary.Execution.Setup.a M S ρ) + S.E.Δ) w C)
    (a : NamedAttestation V)
    (ha : a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v_1].st) v_1 ρ)
    (root : BlockId) (hroot : a.confirmed = some root) :
    ∃ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies ∧ C.root = root ∧
      Block.find? (x[m][w].st).st.core.T root = some C.erase ∧
      ∀ c : Int, (Restated.Vocabulary.Execution.Setup.a M S ρ) + S.E.Δ ≤ c →
        stampedBefore (x[m][w].st).st.core.timestamp_block c C.erase = true := by
  have hn1 := (Restated.tickStepAt_time facts x hn).1
  have hv_1n : Restated.HonestThrough M Sched x (n + 1) v_1 := fun t ht =>
    hv_1m t (le_trans ht (by rw [hn1]; linarith [S.E.Δ_pos]))
  obtain ⟨C, hC, hCroot⟩ := Restated.hhead_mem_of_tick facts S Sched x n ρ v_1 a ha root hroot
  obtain ⟨hmem, σ, hσ, hσlt⟩ :=
    Restated.block_held_before_period facts S Sched x hexec hsync hcatch hmult htd hn hgst hb₀ hv_1n hC hm hw
      hwm (hadm C hC a ha (by rw [hroot, hCroot]))
  refine ⟨C, hC, hCroot, ?_, fun c hc => stampedBefore_of_lt hσ
    (lt_of_lt_of_le hσlt (WithBot.coe_le_coe.mpr hc))⟩
  rw [← hCroot, ← Proofs.NamedWire.erase_root]
  exact Restated.find_of_mem_tree_honest facts S Sched x hexec hwm hmem

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- On the premises of `token_raw_in_view` and of `attested_block_resolves`, if moreover every body
    of `v_1` after the tick that some attestation of `v_1`'s round-`ρ` action read names is
    compatible with `w`'s finalized block after `m` steps, then for every round `q` with
    `ρ + 1 ≤ q ≤ ρ + η_SG`, every phase `p`, every attestation `a` of that action read and every
    outcome `Y` of `v_1`'s ready view of `w`'s round-`q` grade at the phase's early cutoff, the
    token of `a` is in `Y`. -/
theorem token_ready_in_view (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {b₀ b₁ : Int} (hsync : Restated.SynchronyFromWakeOutside M S x b₀ b₁)
    (hcatch : Restated.CatchUpOnWakeOutside M S x b₀ b₁) (hmult : AwakeAtMultiples S Sched)
    (htd : Restated.TimeDiverges M x) {ρ n m : Nat} (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S ρ)))
    (hgst : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S ρ)) (hb₀ : (Restated.Vocabulary.Execution.Setup.a M S ρ) + S.E.Δ ≤ b₀)
    {v_1 w : V} (hv_1 : v_1 ∈ Restated.attestersAt M S Sched ρ) (hv_1m : Restated.HonestThrough M Sched x m v_1)
    (hm : (Restated.Vocabulary.Execution.Setup.a M S ρ) + S.E.Δ ≤ (x[m].time : Int))
    (hw : w ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S ρ)) (x[m].time : Int))
    (hwm : Restated.HonestThrough M Sched x m w)
    (hadm : ∀ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies →
      ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v_1].st) v_1 ρ,
      a.confirmed = some C.root →
      Restated.ReaderAdmitsInPhase M S Sched x 0 ((Restated.Vocabulary.Execution.Setup.a M S ρ) + S.E.Δ) w C)
    (hcompat : ∀ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies →
      ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v_1].st) v_1 ρ,
      a.confirmed = some C.root →
      Block.compatible C.erase (x[m][w].st).st.core.F = true)
    {q : Nat} (hq₁ : ρ + 1 ≤ q) (hq₂ : q ≤ ρ + S.hc.η_SG) (p : Protocol.Phase) :
    ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v_1].st) v_1 ρ,
    ∀ Y, M.readyView (M.gradeView (M.toHealing (x[m][w].st).st.core)) (x[m][w].st).st.core.F
          S.hc.η_SG q (M.early S.E S.hc q p) v_1 ⇢ Y →
      M.token (M.sgVote a.erase) ∈ Y := by
  intro a ha Y hY
  have hc := Restated.action_delta_le_early_of_lt facts S hq₁ p
  obtain ⟨X, hX⟩ := facts.gr.rawInputs_nonempty (M.gradeView (M.toHealing (x[m][w].st).st.core))
    S.hc.η_SG q (M.early S.E S.hc q p) v_1
  have hraw := (Restated.token_raw_in_view facts S Sched x hexec hsync hn hgst hb₀ hv_1 hv_1m hm hw hwm hq₁ hq₂
    hc a ha).1 X hX
  have hconf : (M.sgVote a.erase).confirmed = a.confirmed := facts.sto.sgVote_confirmed a
  obtain ⟨b, hb⟩ := facts.gr.bodyReady_nonempty (M.gradeView (M.toHealing (x[m][w].st).st.core))
    (x[m][w].st).st.core.F (M.early S.E S.hc q p) (M.sgVote a.erase)
  have hready : b = true := by
    cases hcase : a.confirmed with
    | none => exact facts.gr.bodyReady_of_no_head _ _ _ _ (hconf.trans hcase) b hb
    | some root =>
        obtain ⟨C, hC, hCroot, hfind, hstamp⟩ :=
          Restated.attested_block_resolves facts S Sched x hexec hsync hcatch hmult htd hn hgst hb₀ hv_1m hm hw
            hwm hadm a ha root hcase
        refine facts.gr.bodyReady_of_head _ _ _ _ (hconf.trans hcase) ?_
          (by rw [facts.gr.gradeView_timestamp_block]; exact hstamp _ hc)
          (hcompat C hC a ha (by rw [hcase, hCroot])) b hb
        rw [facts.gr.Sts_gradeView_T]; exact hfind
  exact facts.gr.token_mem_readyView _ _ _ _ _ _ X hX hraw b hb hready Y hY

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- On the premises of `token_ready_in_view`, for every round `q` with `ρ + 1 ≤ q ≤ ρ + η_SG`, every
    phase `p` and every outcome `Re` of `v_1`'s ready view of `w`'s round-`q` grade at the phase's
    early cutoff, some token in `Re` has round at least `ρ`. -/
theorem exists_ready_token_ge (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {b₀ b₁ : Int} (hsync : Restated.SynchronyFromWakeOutside M S x b₀ b₁)
    (hcatch : Restated.CatchUpOnWakeOutside M S x b₀ b₁) (hmult : AwakeAtMultiples S Sched)
    (htd : Restated.TimeDiverges M x) {ρ n m : Nat} (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S ρ)))
    (hgst : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S ρ)) (hb₀ : (Restated.Vocabulary.Execution.Setup.a M S ρ) + S.E.Δ ≤ b₀)
    {v_1 w : V} (hv_1 : v_1 ∈ Restated.attestersAt M S Sched ρ) (hv_1m : Restated.HonestThrough M Sched x m v_1)
    (hm : (Restated.Vocabulary.Execution.Setup.a M S ρ) + S.E.Δ ≤ (x[m].time : Int))
    (hw : w ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S ρ)) (x[m].time : Int))
    (hwm : Restated.HonestThrough M Sched x m w)
    (hadm : ∀ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies →
      ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v_1].st) v_1 ρ,
      a.confirmed = some C.root →
      Restated.ReaderAdmitsInPhase M S Sched x 0 ((Restated.Vocabulary.Execution.Setup.a M S ρ) + S.E.Δ) w C)
    (hcompat : ∀ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies →
      ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v_1].st) v_1 ρ,
      a.confirmed = some C.root →
      Block.compatible C.erase (x[m][w].st).st.core.F = true)
    {q : Nat} (hq₁ : ρ + 1 ≤ q) (hq₂ : q ≤ ρ + S.hc.η_SG) (p : Protocol.Phase) :
    ∀ Re, M.readyView (M.gradeView (M.toHealing (x[m][w].st).st.core))
        (x[m][w].st).st.core.F S.hc.η_SG q (M.early S.E S.hc q p) v_1 ⇢ Re →
      ∃ tok ∈ Re, ρ ≤ tok.round := by
  intro Re hRe
  obtain ⟨a, ha⟩ := (pGF% actionAttestationFrom_nonempty_gf) facts (Setup.alwaysAwake S)
    (x[n][v_1].st) v_1 ρ
  refine ⟨_, Restated.token_ready_in_view facts S Sched x hexec hsync hcatch hmult htd hn hgst hb₀ hv_1 hv_1m hm
    hw hwm hadm hcompat hq₁ hq₂ p a ha Re hRe, ?_⟩
  rw [facts.gr.token_round, facts.sto.sgVote_round]
  exact le_of_eq (Restated.actionAttestationFrom_round facts (Setup.alwaysAwake S) _ v_1 ρ a ha).symm

end

end DecoupledConsensusModel.Sts.Restated
