import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bK_FreshAttestersW
import Proofs.Claims.Restated.Claim13bK_GradeOld
import Proofs.Claims.Restated.Claim13bK_StableRootFor
import Proofs.Claims.Restated.Claim13bStepConeIter
import Proofs.Claims.Restated.Claim13bStepGrade
import Proofs.Claims.Restated.Claim13bStepKit
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bStepKitStore
import Proofs.Claims.Restated.Claim13bStepKitTick
import Proofs.Claims.Restated.Claim13bStepRoots
import Proofs.Claims.Restated.Claim13bStepSG
import Proofs.Claims.Restated.Claim13bSyncView
import Proofs.Claims.Restated.Claim13bW_FrameAsleep
import Proofs.Claims.Restated.Claim13beRoute3_3
import Proofs.Claims.Restated.ClaimAsyncK_Attest
import Proofs.Claims.Restated.ClaimAsyncK_Defs
import Proofs.Claims.Restated.ClaimAsyncK_GradeFor
import Proofs.Claims.Restated.ClaimAsyncK_NoConflictingQuorum
import Proofs.Claims.Restated.ClaimAsyncK_StableRecord
import Proofs.Claims.Restated.ClaimAsyncK_TokensHeld
import Proofs.Claims.Restated.CommonViewOfFinalizedDescendantsFacts
import Proofs.Claims.Restated.ProcessIdempotent
import Proofs.Claims.Restated.ProcessedFlip
import Proofs.Claims.Restated.Projection
import Proofs.Claims.Restated.VocabularyAssumptionsLemmas
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bK_FreshAttestersW
import Model.Conditions.Claim13bK_GradeOldHeads
import Model.Conditions.Claim13bStepKitTick
import Model.Conditions.Claim13bStepSG
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Proofs.Claims.Spec2Claims.Claim13bStepSGMove
import Model.Conditions.ClaimAsyncK_Attest
import Model.Conditions.ClaimAsyncK_Defs
import Model.Conditions.ClaimAsyncK_Handover
import Model.Conditions.ClaimAsyncK_PeriodInduction
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Sts_Spec2Claims_ClaimStableThroughAsyncPeriod
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedActionReads
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring

/-!
# Grades and attestations through the asynchronous period

Theorems over a model `M : Record.Model V` with facts `facts : Record.Facts M`: tokens held and
resolved by a validator awake only through `S.a ρ + Δ`, `P` graded through the period from resolved
tokens, and the attestations of a validator whose fork-choice root descends from `P`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

local macro "pAT% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.ClaimAsyncK_Attest)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "pGF% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.ClaimAsyncK_GradeFor)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

private theorem round_cases_pi (q c ρ : ℕ) (a : q ≤ c) (b : c ≤ ρ) (h : ρ ≤ q + 1) :
    (ρ = c ∧ (q + 1 = c ∨ q + 1 = c + 1)) ∨ (ρ = c + 1 ∧ q + 1 = c + 1) := by
  omega

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- On an execution whose time diverges, some step `m₀` has `x[m₀].time = S.a ρ + Δ`, and every step
    whose time is at or after `S.a ρ + Δ` is at or after `m₀`. -/
theorem exists_step_at_action_delta (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (htd : Restated.TimeDiverges M x) (ρ : Nat) :
    ∃ m₀ : Nat, (x[m₀].time : Int) = (Restated.Vocabulary.Execution.Setup.a M S ρ) + S.E.Δ ∧
      ∀ m : Nat, (Restated.Vocabulary.Execution.Setup.a M S ρ) + S.E.Δ ≤ (x[m].time : Int) → m₀ ≤ m := by
  have hpos : 0 < (Restated.Vocabulary.Execution.Setup.a M S ρ) + S.E.Δ := by linarith only [Restated.action_pos facts S ρ, S.E.Δ_pos]
  obtain ⟨k₁, hk₁⟩ := Restated.exists_tickStepAt facts x htd hpos
  obtain ⟨h1, h0⟩ := Restated.tickStepAt_time facts x hk₁
  refine ⟨k₁ + 1, h1, fun m hm => ?_⟩
  by_contra hcon
  have := Restated.time_mono_int facts S Sched x (show m ≤ k₁ by omega)
  linarith

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- With `w` awake at every time of `[S.a ρ, S.a ρ + Δ]`, for every round-`ρ` attestation `a` that
    `v_1`'s action can compute from its node state at step `n`, the SG-vote projection of `a` is in
    `w`'s grade-view pool of round `ρ` after `m` steps, with a stamp strictly before `S.a ρ + Δ`. -/
theorem token_held_window (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {b₀ b₁ : Int} (hsync : Restated.SynchronyFromWakeOutside M S x b₀ b₁) (htd : Restated.TimeDiverges M x)
    {ρ n m : Nat}
    (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S ρ))) (hgst : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S ρ)) (hb₀ : (Restated.Vocabulary.Execution.Setup.a M S ρ) + S.E.Δ ≤ b₀)
    {v_1 w : V} (hv_1 : v_1 ∈ Restated.activeRoundW M S Sched ρ) (hv_1m : Restated.HonestThrough M Sched x m v_1)
    (hm : (Restated.Vocabulary.Execution.Setup.a M S ρ) + S.E.Δ ≤ (x[m].time : Int))
    (hw : w ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S ρ)) ((Restated.Vocabulary.Execution.Setup.a M S ρ) + S.E.Δ))
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
  obtain ⟨m₀, hm₀t, -⟩ := Restated.exists_step_at_action_delta facts S Sched x htd ρ
  have hv_1m₀ : Restated.HonestThrough M Sched x m₀ v_1 := fun t ht =>
    hv_1m t (le_trans ht (by rw [hm₀t]; exact hm))
  obtain ⟨d, hnd, hlbl, hdlo, hdlt⟩ :=
    Restated.token_delivered_before_period facts S Sched x hsync hn hgst hb₀ hv_1 hv_1m₀ (le_of_eq hm₀t.symm)
      (by rw [hm₀t]; exact hw) (facts.ndRun.tick_outcome_sts S Sched x hexec.idealization.root_injective hexec.honestRootsNew) a ha
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
    mem_awake_of_awakeThroughout Sched hw (by rw [hdtime]; exact hdlo)
      (by rw [hdtime]; exact le_of_lt hdlt)
  have hv : HonestThroughTime Sched (x[d + 1].time : Int) v_1 := fun t ht =>
    hv_1m t (le_trans ht hd1le)
  have hawT : w ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S a.round)) (x[d + 1].time : Int) := by
    rw [ha_round]
    exact awakeThroughout_mono Sched hw le_rfl (by rw [hdtime]; exact le_of_lt hdlt)
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
    Restated.attest_recorded_of_mem_view_awake facts S Sched x hview haw hv hexec.toUnforgeability ha_idx
      hawT hwh hexp hroom
      (fun n' hn' => by
        rw [ha_round] at hn' ⊢
        exact Restated.tick_outcome_of_tickStepAt_honest facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew
          hn' (Restated.action_emod_delta facts S ρ)
          (Finset.mem_sdiff.2 ⟨mem_awake_of_awakeThroughout Sched hw le_rfl (by linarith),
            hwm _ (by linarith)⟩)
          (fun t' ht' => hwm t' (by linarith)))
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

/-- With `w` awake at every time of `[S.a ρ, S.a ρ + Δ]` and `hadm` holding for every attestation
    `v_1`'s action can compute from its node state at step `n`: if one such attestation `a` names
    the root `root`, then some body `C` of `v_1` after the tick has the root `root`, `w`'s tree
    after `m` steps resolves `root` to `C.erase`, and that block is stamped there before every
    cutoff from `S.a ρ + Δ` on. -/
theorem attested_block_resolves_window (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {b₀ b₁ : Int} (hsync : Restated.SynchronyFromWakeOutside M S x b₀ b₁)
    (hcatch : Restated.CatchUpOnWakeOutside M S x b₀ b₁) (hmult : AwakeAtMultiples S Sched)
    (htd : Restated.TimeDiverges M x) {ρ n m : Nat} (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S ρ)))
    (hgst : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S ρ)) (hb₀ : (Restated.Vocabulary.Execution.Setup.a M S ρ) + S.E.Δ ≤ b₀)
    {v_1 : V} (hv_1m : Restated.HonestThrough M Sched x m v_1) {w : V}
    (hm : (Restated.Vocabulary.Execution.Setup.a M S ρ) + S.E.Δ ≤ (x[m].time : Int))
    (hw : w ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S ρ)) ((Restated.Vocabulary.Execution.Setup.a M S ρ) + S.E.Δ))
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
  obtain ⟨m₀, hm₀t, hm₀le⟩ := Restated.exists_step_at_action_delta facts S Sched x htd ρ
  have hm₀m : m₀ ≤ m := hm₀le m hm
  have hn1 := (Restated.tickStepAt_time facts x hn).1
  have hv_1n : Restated.HonestThrough M Sched x (n + 1) v_1 := fun t ht =>
    hv_1m t (le_trans ht (by rw [hn1]; linarith [S.E.Δ_pos]))
  have hwm₀ : Restated.HonestThrough M Sched x m₀ w := fun t ht =>
    hwm t (le_trans ht (Restated.time_mono_int facts S Sched x hm₀m))
  obtain ⟨C, hC, hCroot⟩ := Restated.hhead_mem_of_tick facts S Sched x n ρ v_1 a ha root hroot
  obtain ⟨hmem, σ, hσ, hσlt⟩ :=
    Restated.block_held_before_period facts S Sched x hexec hsync hcatch hmult htd hn hgst hb₀ hv_1n hC
      (le_of_eq hm₀t.symm) (by rw [hm₀t]; exact hw) hwm₀ (hadm C hC a ha (by rw [hroot, hCroot]))
  obtain ⟨D, hD, hDe⟩ := Restated.exists_named_of_mem_tree facts S Sched x m₀ w hmem
  have hDm : D ∈ (x[m][w].st).st.bodies := by
    have h := Restated.processed_mono facts S Sched x w (NamedObject.block D) hm₀m
      (by simpa only [Restated.Vocabulary.Execution.Object.processed, decide_eq_true_eq] using hD)
    simpa only [Restated.Vocabulary.Execution.Object.processed, decide_eq_true_eq] using h
  have hmemm : C.erase ∈ (x[m][w].st).st.core.T := by
    rw [Restated.bodies_image_eq_T facts S Sched x m w, ← hDe]
    exact Finset.mem_image_of_mem NamedBlock.erase hDm
  have hσm := Restated.block_stamp_carry facts S Sched x hm₀m w hσ
  refine ⟨C, hC, hCroot, ?_, fun c hc => stampedBefore_of_lt hσm
    (lt_of_lt_of_le hσlt (WithBot.coe_le_coe.mpr hc))⟩
  rw [← hCroot, ← Proofs.NamedWire.erase_root]
  exact Restated.find_of_mem_tree_honest facts S Sched x hexec hwm hmemm

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- With `w` awake at every time of `[S.a ρ, S.a ρ + Δ]` and `hadm` and `hcompat` holding for every
    attestation `v_1`'s action can compute from its node state at step `n`: for every round `q` with
    `ρ + 1 ≤ q ≤ ρ + η_SG`, every phase `p` and every outcome `Re` of `w`'s ready view of `v_1` for
    the round-`q` grade at the phase's early cutoff, some token in `Re` has round at least `ρ`. -/
theorem exists_ready_token_ge_window (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {b₀ b₁ : Int} (hsync : Restated.SynchronyFromWakeOutside M S x b₀ b₁)
    (hcatch : Restated.CatchUpOnWakeOutside M S x b₀ b₁) (hmult : AwakeAtMultiples S Sched)
    (htd : Restated.TimeDiverges M x) {ρ n m : Nat} (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S ρ)))
    (hgst : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S ρ)) (hb₀ : (Restated.Vocabulary.Execution.Setup.a M S ρ) + S.E.Δ ≤ b₀)
    {v_1 w : V} (hv_1 : v_1 ∈ Restated.activeRoundW M S Sched ρ) (hv_1m : Restated.HonestThrough M Sched x m v_1)
    (hm : (Restated.Vocabulary.Execution.Setup.a M S ρ) + S.E.Δ ≤ (x[m].time : Int))
    (hw : w ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S ρ)) ((Restated.Vocabulary.Execution.Setup.a M S ρ) + S.E.Δ))
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
  obtain ⟨a, ha⟩ := (pGF% actionAttestationFrom_nonemptyGradeFor) facts (Setup.alwaysAwake S)
    (x[n][v_1].st) v_1 ρ
  have hc := Restated.action_delta_le_early_of_lt facts S hq₁ p
  obtain ⟨hmem, stamp, hlt, hts⟩ :=
    Restated.token_held_window facts S Sched x hexec hsync htd hn hgst hb₀ hv_1 hv_1m hm hw hwm
      a ha
  have hlo : q - S.hc.η_SG ≤ ρ := by omega
  have hhi : ρ < q := by omega
  have hwin : ρ ∈ M.latest_window S.hc.η_SG q :=
    facts.fc.mem_latest_window hlo hhi
  obtain ⟨X, hX⟩ := facts.gr.rawInputs_nonempty (M.gradeView (M.toHealing (x[m][w].st).st.core))
    S.hc.η_SG q (M.early S.E S.hc q p) v_1
  have hraw : M.sgVote a.erase ∈ X :=
    facts.gr.mem_rawInputs_of_stamp _ S.hc.η_SG q ρ (M.early S.E S.hc q p) v_1 hwin hmem
      ((facts.sto.sgVote_val _).trans
        (Restated.actionAttestationFrom_val_index facts (Setup.alwaysAwake S) (x[n][v_1].st) v_1 ρ a ha))
      hts (lt_of_lt_of_le hlt hc) X hX
  have hconf : (M.sgVote a.erase).confirmed = a.confirmed := facts.sto.sgVote_confirmed a
  obtain ⟨b, hb⟩ := facts.gr.bodyReady_nonempty (M.gradeView (M.toHealing (x[m][w].st).st.core))
    (x[m][w].st).st.core.F (M.early S.E S.hc q p) (M.sgVote a.erase)
  have hready : b = true := by
    cases hcase : a.confirmed with
    | none => exact facts.gr.bodyReady_of_no_head _ _ _ _ (hconf.trans hcase) b hb
    | some root =>
        obtain ⟨C, hC, hCroot, hfind, hstamp⟩ :=
          Restated.attested_block_resolves_window facts S Sched x hexec hsync hcatch hmult htd hn hgst hb₀
            hv_1m hm hw hwm hadm a ha root hcase
        refine facts.gr.bodyReady_of_head _ _ _ _ (hconf.trans hcase) ?_
          (by rw [facts.gr.gradeView_timestamp_block]; exact hstamp _ hc)
          (hcompat C hC a ha (by rw [hcase, hCroot])) b hb
        rw [facts.gr.Sts_gradeView_T]; exact hfind
  refine ⟨_, facts.gr.token_mem_readyView _ _ _ _ _ _ X hX hraw b hb hready Re hRe, ?_⟩
  rw [facts.gr.token_round, facts.sto.sgVote_round]
  exact le_of_eq (Restated.actionAttestationFrom_round facts (Setup.alwaysAwake S) _ v_1 ρ a ha).symm

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If `tok` is in an outcome `Re` of `v`'s ready view of the grade view `gv` at the cutoff `c`,
    names the root `root`, and every block `root` resolves to in `gv`'s tree is `P` or a descendant
    of `P`, then every outcome of the test whether `tok`'s key covers `P` in `gv`'s tree is `true`. -/
theorem head_covers_of_ready_resolved (facts : Record.Facts M) (gv : M.GV) (F : Block V) (η ρ : Round)
    (c : Int) (v : V) {tok : Protocol.Token (Option BlockId)} {root : BlockId} {P : Block V}
    {Re : Finset (Protocol.Token (Option BlockId))} (hRe : M.readyView gv F η ρ c v ⇢ Re)
    (hrdy : tok ∈ Re) (hkey : tok.key = some root)
    (hB : ∀ B : Block V, Block.find? gv.T root = some B → Block.Preceq P B) :
    ∀ b : Bool, M.head_covers gv.T P tok.key ⇢ b → b = true := by
  intro b hb
  obtain ⟨B, hfind⟩ := facts.gr.find_of_mem_readyView gv F η ρ c v Re hRe hrdy hkey
  rw [hkey] at hb
  exact facts.gr.head_covers_of_find hfind (hB B hfind) b hb

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Let `v_1` be honest through step `m` and `q₀` a round. If some token of `v_1` in the outcome
    `Re` of `w`'s early ready view has round at least `q₀`, and every token of `v_1` of round at
    least `q₀` in the outcome `Wl` of `w`'s raw view at the late cutoff names a root every
    resolution of which in `w`'s tree is `P` or a descendant of `P`, then every outcome of the test
    whether `v_1` supports `P` is `true`. -/
theorem positive_of_tokens_cover_resolved (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {m : Nat} {w v_1 : V} (hv_1 : Restated.HonestThrough M Sched x m v_1) {ρ q₀ : Nat}
    {p : Protocol.Phase} {P : Block V}
    {Re : Finset (Protocol.Token (Option BlockId))}
    (hRe : M.readyView (M.gradeView (M.toHealing (x[m][w].st).st.core))
        (x[m][w].st).st.core.F S.hc.η_SG ρ (M.early S.E S.hc ρ p) v_1 ⇢ Re)
    (hready : ∃ tok ∈ Re, q₀ ≤ tok.round)
    {Wl : Finset (Protocol.Token (Option BlockId))}
    (hWl : M.rawView (M.gradeView (M.toHealing (x[m][w].st).st.core)) S.hc.η_SG ρ
        (M.late S.E S.hc ρ p) v_1 ⇢ Wl)
    (hcover : ∀ tok ∈ Wl, q₀ ≤ tok.round →
      ∃ root : BlockId, tok.key = some root ∧
        ∀ B : Block V, Block.find? (M.gradeView (M.toHealing (x[m][w].st).st.core)).T root = some B →
          Block.Preceq P B) :
    ∀ b : Bool, M.positive (M.gradeView (M.toHealing (x[m][w].st).st.core)) (x[m][w].st).st.core.F
      S.hc.η_SG ρ (M.early S.E S.hc ρ p) (M.late S.E S.hc ρ p) v_1 P ⇢ b → b = true := by
  intro b hb
  have hel := facts.gr.early_le_late S.E S.hc ρ p
  obtain ⟨t₀, ht₀, hq₀⟩ := hready
  obtain ⟨u₀, hu₀, hmax⟩ := Finset.exists_max_image Re (fun t => t.round) ⟨t₀, ht₀⟩
  have hu₀q : q₀ ≤ u₀.round := le_trans hq₀ (hmax t₀ ht₀)
  obtain ⟨Xe, hXe⟩ := facts.gr.rawView_nonempty (M.gradeView (M.toHealing (x[m][w].st).st.core))
    S.hc.η_SG ρ (M.early S.E S.hc ρ p) v_1
  have hu₀raw : u₀ ∈ Wl :=
    facts.gr.rawView_mono _ S.hc.η_SG ρ hel v_1 Xe hXe Wl hWl
      (facts.gr.readyView_subset_rawView _ _ S.hc.η_SG ρ _ v_1 Re hRe Xe hXe hu₀)
  have hcov' : ∀ k, M.head_covers (M.gradeView (M.toHealing (x[m][w].st).st.core)).T P k ⇢
      (fun k => (facts.gr.head_covers_nonempty
        (M.gradeView (M.toHealing (x[m][w].st).st.core)).T P k).choose) k :=
    fun k => (facts.gr.head_covers_nonempty _ P k).choose_spec
  have hcovers : ∀ (c : Int) (Rc : Finset (Protocol.Token (Option BlockId))),
      M.readyView (M.gradeView (M.toHealing (x[m][w].st).st.core))
        (x[m][w].st).st.core.F S.hc.η_SG ρ c v_1 ⇢ Rc →
      ∀ tok ∈ Rc, tok ∈ Wl → q₀ ≤ tok.round →
      (fun k => (facts.gr.head_covers_nonempty
        (M.gradeView (M.toHealing (x[m][w].st).st.core)).T P k).choose) tok.key = true := by
    intro c Rc hRc tok hrdy hraw hq
    obtain ⟨root, hkey, hB⟩ := hcover tok hraw hq
    exact Restated.head_covers_of_ready_resolved facts _ _ S.hc.η_SG ρ c v_1 hRc hrdy hkey hB _
      (hcov' tok.key)
  obtain ⟨Rl, hRl⟩ := facts.gr.readyView_nonempty (M.gradeView (M.toHealing (x[m][w].st).st.core))
    (x[m][w].st).st.core.F S.hc.η_SG ρ (M.late S.E S.hc ρ p) v_1
  refine facts.gr.positive_of_conditions _ _ S.hc.η_SG ρ _ _ v_1 P u₀ Re hRe hu₀ hmax _ hcov'
    (hcovers _ Re hRe u₀ hu₀ hu₀raw hu₀q) Wl hWl ?_ Rl hRl ?_ b hb
  · intro y hy z hz _ hyz
    obtain ⟨n₁, htick₁, hk₁⟩ :=
      Restated.rawView_key_of_honest_at facts S Sched x hexec hv_1 hWl hy rfl
    obtain ⟨n₂, htick₂, hk₂⟩ :=
      Restated.rawView_key_of_honest_at facts S Sched x hexec hv_1 hWl hz hyz.symm
    have hnn : n₂ = n₁ := Restated.tickStepAt_unique facts x htick₂ htick₁
    subst hnn
    obtain ⟨a, ha⟩ := (pGF% actionAttestationFrom_nonemptyGradeFor) facts (Setup.alwaysAwake S)
      (x[n₂][v_1].st) v_1 y.round
    rw [hk₁ a ha, hk₂ a ha]
  · intro y hy hlt
    exact hcovers _ Rl hRl y hy
      (facts.gr.readyView_subset_rawView _ _ S.hc.η_SG ρ _ v_1 Rl hRl Wl hWl hy)
      (le_trans hu₀q (le_of_lt hlt))

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- For a round `ρ` from `r + 1` to `r + η_SG + 1`, at the last step before round `ρ`'s phase-`p`
    instant, let `H` be the members of `activeRoundWThroughNextCountedAt S Sched r ρ` that the
    adversary does not hold at the opening of round `ρ + 1`. Under
    `fixedRoundSleepinessCountedW S Sched r`, if `Re u` and `Wl u` are outcomes of `u`'s early ready
    view and late raw view for every validator `u`, every member of `H` has a token of round at
    least `r + 1` in its `Re`, and every token of a member of `H` in its `Wl` of a round at least
    `r + 1` names a root every resolution of which in `w`'s tree is a descendant of `P`, then every
    outcome of `w`'s grade test for `P` at round `ρ` and phase `p` is `true`. -/
theorem gradeBool_period_of_tokens_resolved (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (htd : Restated.TimeDiverges M x) (hmono : Sched.MonotoneCorruption) {r : Nat}
    (hfix : Restated.fixedRoundSleepinessCountedW M S Sched r) {ρ : Nat} (hρ₁ : r + 1 ≤ ρ)
    (hρ₂ : ρ ≤ r + S.hc.η_SG + 1) {m : Nat} {w : V} {p : Protocol.Phase}
    (hm : Restated.stepBeforeInstant M x m (M.domain S.E S.hc ρ p)) {P : Block V}
    (Re : V → Finset (Protocol.Token (Option BlockId)))
    (hRe : ∀ u, M.readyView (M.gradeView (M.toHealing (x[m][w].st).st.core))
      (x[m][w].st).st.core.F S.hc.η_SG ρ (M.early S.E S.hc ρ p) u ⇢ Re u)
    (hready : ∀ v_1 ∈ Restated.activeRoundWThroughNextCountedAt M S Sched r ρ \
        Sched.adv (M.opening S.E S.hc (ρ + 1)),
      ∃ tok ∈ Re v_1, r + 1 ≤ tok.round)
    (Wl : V → Finset (Protocol.Token (Option BlockId)))
    (hWl : ∀ u, M.rawView (M.gradeView (M.toHealing (x[m][w].st).st.core)) S.hc.η_SG ρ
      (M.late S.E S.hc ρ p) u ⇢ Wl u)
    (hcover : ∀ v_1 ∈ Restated.activeRoundWThroughNextCountedAt M S Sched r ρ \
        Sched.adv (M.opening S.E S.hc (ρ + 1)),
      ∀ tok ∈ Wl v_1, r + 1 ≤ tok.round →
        ∃ root : BlockId, tok.key = some root ∧
          ∀ B : Block V, Block.find? (M.gradeView (M.toHealing (x[m][w].st).st.core)).T root = some B →
            Block.Preceq P B) :
    ∀ g : Bool, M.gradeBool S.E (M.gradeView (M.toHealing (x[m][w].st).st.core))
        (x[m][w].st).st.core.F S.hc.η_SG ρ (M.early S.E S.hc ρ p) (M.late S.E S.hc ρ p) P ⇢ g →
      g = true := by
  intro g hg
  have hel := facts.gr.early_le_late S.E S.hc ρ p
  have hpos : ∀ v_1 ∈ Restated.activeRoundWThroughNextCountedAt M S Sched r ρ \
      Sched.adv (M.opening S.E S.hc (ρ + 1)), ∀ b : Bool,
      M.positive (M.gradeView (M.toHealing (x[m][w].st).st.core)) (x[m][w].st).st.core.F
        S.hc.η_SG ρ (M.early S.E S.hc ρ p) (M.late S.E S.hc ρ p) v_1 P ⇢ b → b = true :=
    fun v_1 hv_1 => Restated.positive_of_tokens_cover_resolved facts S Sched x hexec
      (Restated.honestThrough_of_mem_countedAt facts S Sched x htd hmono (by omega) hm hv_1)
      (hRe v_1) (hready v_1 hv_1) (hWl v_1) (hcover v_1 hv_1)
  have hw := Restated.hhalf_of_fixedRoundSleepinessCountedW facts S Sched x hexec htd hmono hfix
    hρ₁ hρ₂ (w := w) hm Wl hWl
  have hposf : ∀ u, M.positive (M.gradeView (M.toHealing (x[m][w].st).st.core))
      (x[m][w].st).st.core.F S.hc.η_SG ρ (M.early S.E S.hc ρ p)
      (M.late S.E S.hc ρ p) u P ⇢
      (fun u => (facts.gr.positive_nonempty (M.gradeView (M.toHealing (x[m][w].st).st.core))
        (x[m][w].st).st.core.F S.hc.η_SG ρ (M.early S.E S.hc ρ p)
        (M.late S.E S.hc ρ p) u P).choose) u :=
    fun u => (facts.gr.positive_nonempty _ _ _ _ _ _ u P).choose_spec
  exact facts.gr.gradeBool_of_supporters S.E _ _ _ _ _ _ P _ _ hposf Wl hWl hel
    (fun u hu => hpos u hu _ (hposf u)) hw g hg

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If `P` is the fork-choice root of the node state `before` or an ancestor of it, then for every
    node state `nr` of `before`'s round-`ρ` action read and every grade read `g` of `nr`'s frame at
    `nr`'s healing store, `P` is the SG vote selected at `nr`'s healing store with `g` or an
    ancestor of it, and an ancestor of `g`'s grade-2 block whenever it has one. -/
theorem preceq_actionSGVote_of_fgRoot (facts : Record.Facts M) (S : Setup V) (before : M.N) (ρ : Round)
    {P : Block V}
    (hPr : Block.Preceq P (M.get_fg_root (M.toHealing before.st.core).toFG)) :
    ∀ nr ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        before ρ,
    ∀ g : Protocol.GradeRead V,
      M.frameGradeRead nr.cache S.E S.hc (M.toHealing nr.st.core) ρ ⇢ g →
    Block.Preceq P (M.currentSGVote (M.toHealing nr.st.core) g) ∧
      ∀ q : Block V, g.Q2 = some q → Block.Preceq P q := by
  intro nr hnr g hg
  have hPr' : Block.Preceq P (M.get_fg_root (M.toHealing nr.st.core).toFG) := by
    rw [(pAT% actionReadFrom_fgRoot_att) facts (Setup.alwaysAwake S) before ρ nr hnr]; exact hPr
  obtain ⟨a, ha⟩ := facts.gr.anchor_nonempty S.E S.hc (M.toHealing nr.st.core) ρ
    (M.readFrame nr.cache (M.toHealing nr.st.core) ρ).g1
  have hga : g.anchor = a := facts.gr.frameGradeRead_anchor _ _ _ _ _ g hg a ha
  obtain ⟨o, ho⟩ := facts.gr.grade2Block_nonempty (M.toHealing nr.st.core)
    (M.readFrame nr.cache (M.toHealing nr.st.core) ρ)
  have hgQ : g.Q2 = o := facts.nd.Sts_gradeContract_read_Q2 nr.cache S.E S.hc _ ρ g
    ((facts.nd.gradeContract_read nr.cache S.E S.hc _ ρ g).2 hg) o ho
  have hA : Block.Preceq P g.anchor := by
    rw [hga]
    exact facts.gr.preceq_anchor_of_fgRoot S.E S.hc _ ρ _ hPr' a ha
  have hQ : ∀ q : Block V, g.Q2 = some q → Block.Preceq P q := by
    intro q hq
    rw [hgQ] at hq
    exact preceq_trans_Preceq hPr' (facts.gr.fgRoot_preceq_grade2Block o ho hq)
  exact ⟨facts.gr.preceq_currentSGVote_of_cases hA hQ (fun _ => hPr'), hQ⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If `n` is the tick step at `S.a ρ`, `u` is honest through the step after the tick, and `P` is
    `u`'s fork-choice root after `n` steps or an ancestor of it, then for every node state `nr` of
    `u`'s round-`ρ` action read after `n` steps and every outcome `D` of the attestation duty at
    `nr`, every block `C` of `u`'s tree after the tick whose root is the `confirmed` field of `D`'s
    attestation is `P` or has `P` as an ancestor. -/
theorem attest_covers_of_fgRoot (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {ρ : Round} {n : Nat} {u : V} (hvh : Restated.HonestThrough M Sched x (n + 1) u) {P : Block V}
    (hPr : Block.Preceq P (M.get_fg_root (M.toHealing (x[n][u].st).st.core).toFG)) :
    ∀ nr ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (x[n][u].st) ρ,
    ∀ D, M.duties_attest_with (M.gradeContract nr.cache) S.E S.hc ((Setup.alwaysAwake S).node u)
        nr.st nr.record ⇢ D →
    ∀ C : NamedBlock V, C ∈ (x[n + 1][u].st).st.bodies →
      D.2.2.confirmed = some C.root →
      Block.Preceq P C.erase := by
  intro nr hnr D hD C hC hconf
  obtain ⟨g, hg'⟩ := facts.gr.read_nonempty (M.gradeContract nr.cache) S.E S.hc
    (M.toHealing nr.st.core) ρ
  have hg := (facts.nd.gradeContract_read nr.cache S.E S.hc _ ρ g).1 hg'
  have hsgP := (Restated.preceq_actionSGVote_of_fgRoot facts S (x[n][u].st) ρ hPr nr hnr g hg).1
  have hvhn : Restated.HonestThrough M Sched x n u := fun t ht =>
    hvh t (le_trans ht (Restated.time_mono_int facts S Sched x (Nat.le_succ n)))
  rw [Restated.attest_confirmed_eq_sgVote facts S (x[n][u].st) u ρ nr hnr D hD g hg] at hconf
  obtain ⟨E, hElog, hEe⟩ := Restated.exists_inLog_erase_actionSGVote facts S Sched x hvhn ρ nr hnr g hg
  have hCE : C.erase = E.erase := by
    refine Restated.erase_eq_of_root_eq_inLog facts S Sched x hexec (Restated.blockInLog_of_mem_bodies facts S Sched hvh hC)
      hElog ?_
    rw [← Proofs.NamedWire.erase_root E, hEe]
    exact (Option.some_inj.mp hconf).symm
  rw [hCE, hEe]
  exact hsgP

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- On the premises of `attest_covers_of_fgRoot`, for every node state `nr` of `u`'s round-`ρ`
    action read after `n` steps and every outcome `D` of the attestation duty at `nr` whose
    attestation carries a height vote for height `h` bound to the root `root`, every block on the
    wire whose root is `root` is an ancestor or a descendant of `P`. -/
theorem attest_heightPair_compatible_of_fgRoot (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {ρ : Round} {n : Nat} (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S ρ))) {u : V}
    (hvh : Restated.HonestThrough M Sched x (n + 1) u) {P : Block V}
    (hPr : Block.Preceq P (M.get_fg_root (M.toHealing (x[n][u].st).st.core).toFG)) :
    ∀ nr ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (x[n][u].st) ρ,
    ∀ D, M.duties_attest_with (M.gradeContract nr.cache) S.E S.hc ((Setup.alwaysAwake S).node u)
        nr.st nr.record ⇢ D →
    ∀ (h : Height) (root : BlockId) (tmo : Bool),
      D.2.2.height_pair = NamedHeightPair.vote h root tmo →
      ∀ C : NamedBlock V, Restated.blockInLog M S Sched x C → C.root = root →
        Block.Compatible P C.erase := by
  intro nr hnr D hD h root tmo hvote C hC hCroot
  obtain ⟨g, hg'⟩ := facts.gr.read_nonempty (M.gradeContract nr.cache) S.E S.hc
    (M.toHealing nr.st.core) ρ
  have hg := (facts.nd.gradeContract_read nr.cache S.E S.hc _ ρ g).1 hg'
  have hQ := (Restated.preceq_actionSGVote_of_fgRoot facts S (x[n][u].st) ρ hPr nr hnr g hg).2
  have hvhn : Restated.HonestThrough M Sched x n u := fun t ht =>
    hvh t (le_trans ht (Restated.time_mono_int facts S Sched x (Nat.le_succ n)))
  have hRd := (pAT% actionReadFrom_round_att) facts S (x[n][u].st) ρ nr hnr
  obtain ⟨A2, hA2⟩ := facts.dt.grade2_block_with_nonempty (M.gradeContract nr.cache) S.E S.hc
    (M.toHealing nr.st.core) ρ
  obtain ⟨o, ho'⟩ := facts.dt.fg_source_with_nonempty (M.gradeContract nr.cache) S.E S.hc
    (M.toHealing nr.st.core) ρ A2
  have ho : Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M (Setup.alwaysAwake S) nr ⇢ o := by
    refine ((pAT% returns_bind_iff_att) _ _ _).2 ⟨A2, ?_, ?_⟩
    · show M.grade2_block_with (M.gradeContract nr.cache) S.E S.hc (M.toHealing nr.st.core)
        (M.round_of S.hc (M.toHealing nr.st.core).s) ⇢ A2
      rw [hRd]; exact hA2
    · show M.fg_source_with (M.gradeContract nr.cache) S.E S.hc (M.toHealing nr.st.core)
        (M.round_of S.hc (M.toHealing nr.st.core).s) A2 ⇢ o
      rw [hRd]; exact ho'
  obtain ⟨Cfg, rfl, hCfg⟩ := Restated.entry_preceq_source_of_honest facts S Sched x hexec hn hvhn
    nr hnr D hD hvote o ho
  obtain ⟨Q, hQ', hQCfg⟩ := facts.dt.fg_source_with_some _ _ _ _ _ (some Cfg) ho' rfl
  have hA2g : A2 = g.Q2 :=
    facts.nd.gradeContract_grade2_block_with nr.cache S.E S.hc _ ρ g hg A2 hA2
  exact compatible_iff_Compatible.mpr
    (compatible_of_preceq_common_Preceq
      (preceq_trans_Preceq (hQ Q (by rw [← hA2g]; exact hQ')) hQCfg)
      (hCfg C hC hCroot))

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Let `d`, round `(q + 1)`'s domain instant of the phase `p`, be positive, a multiple of `Δ` and
    in round `q` or `q + 1`; let step `k` be the tick at a time `τ` of round `q + 1` after `d`, `u`
    be awake and not held at `d`, `u`'s grade test for `P` at the last step before `d` be able to
    return `true`, `u`'s tick at every tick step at `d` have an outcome, `u`'s finalized block lie
    on one chain with `P` at every step up to `k`, and the store `st` have a finalized block on one
    chain with `P`. Then for every cache `c` that `u`'s phase tick at `τ` can return from its node
    state after `k` steps, the round-`(q + 1)` frame read at `st` from `c` holds for the phase `p` a
    block `e` with `P ⪯ e`. -/
theorem tickFrame_phase_preceq_of_graded (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (htd : Restated.TimeDiverges M x) {q : Round}
    {p : Protocol.Phase}
    (hdpos : 0 < M.domain S.E S.hc (q + 1) p)
    (hdvd : M.domain S.E S.hc (q + 1) p % S.E.Δ = 0)
    (hdρ : (M.round_of S.hc (S.E.slotOf (M.domain S.E S.hc (q + 1) p))) = q ∨
      (M.round_of S.hc (S.E.slotOf (M.domain S.E S.hc (q + 1) p))) = q + 1)
    {τ : Int} {k : Nat} (hk : Restated.tickStepAt M x k τ)
    (hτρ : (M.round_of S.hc (S.E.slotOf τ)) = q + 1)
    (hdτ : M.domain S.E S.hc (q + 1) p < τ) {u : V}
    (hu : u ∈ Sched.awake (M.domain S.E S.hc (q + 1) p) \
      Sched.adv (M.domain S.E S.hc (q + 1) p))
    {P : Block V}
    (hgr : ∀ m : Nat, Restated.stepBeforeInstant M x m (M.domain S.E S.hc (q + 1) p) →
      M.gradeBool S.E (M.gradeView (M.toHealing (x[m][u].st).st.core))
        (x[m][u].st).st.core.F S.hc.η_SG (q + 1) (M.early S.E S.hc (q + 1) p)
        (M.late S.E S.hc (q + 1) p) P ⇢ true)
    (hPF : ∀ j : Nat, j ≤ k → Block.compatible P (x[j][u].st).st.core.F = true)
    (st : M.HS) (hst : Block.compatible P st.F = true)
    (hne : ∀ m : Nat, Restated.tickStepAt M x m (M.domain S.E S.hc (q + 1) p) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) u (Record.wakeStage M Sched (M.domain S.E S.hc (q + 1) p) x[m] u)
          (M.domain S.E S.hc (q + 1) p) ⇢ out) :
    ∀ c : M.Cache, M.onPhaseTick S.E S.hc (M.toHealing (x[k][u].st).st.core) τ
        (x[k][u].st).cache ⇢ c →
    ∃ e : Block V,
      M.phaseResult (M.readFrame c st (q + 1)) p = some (some e) ∧ Block.Preceq P e := by
  have _hr_0 : M.reachedNode (x[k][u].st) := Record.reachedNode_sts facts S Sched x k u
  intro c hc
  obtain ⟨m, hm⟩ := Restated.exists_tickStepAt facts x htd hdpos
  have hmB := Restated.stepBeforeInstant_of_tickStepAt facts x hm
  obtain ⟨hm1, hm0⟩ := Restated.tickStepAt_time facts x hm
  obtain ⟨hk1, hk0⟩ := Restated.tickStepAt_time facts x hk
  have hmk : m + 1 ≤ k := by
    by_contra hcon
    have h1 := Restated.time_mono_int facts S Sched x (show k + 1 ≤ m + 1 by omega)
    linarith
  have hg := hgr m hmB
  obtain ⟨H, hH, hPH⟩ := facts.gr.Sts_exists_mem_T_preceq_of_gradeBool _ _ _ _ _ _ _ _ true hg rfl
  have hPT : P ∈ (M.gradeView (M.toHealing (x[m][u].st).st.core)).T := by
    rw [facts.gr.Sts_gradeView_T] at hH ⊢
    exact Restated.mem_T_of_preceq_sts facts S Sched x m u hH hPH
  classical
  have hgne := fun B : Block V => facts.gr.gradeBool_nonempty S.E
    (M.gradeView (M.toHealing (x[m][u].st).st.core)) (x[m][u].st).st.core.F S.hc.η_SG (q + 1)
    (M.early S.E S.hc (q + 1) p) (M.late S.E S.hc (q + 1) p) B
  let gf : Block V → Bool := fun B => if B = P then true else (hgne B).choose
  have hgf : ∀ B : Block V, M.gradeBool S.E (M.gradeView (M.toHealing (x[m][u].st).st.core))
      (x[m][u].st).st.core.F S.hc.η_SG (q + 1) (M.early S.E S.hc (q + 1) p)
      (M.late S.E S.hc (q + 1) p) B ⇢ gf B := by
    intro B
    by_cases hBP : B = P
    · have : gf B = true := if_pos hBP
      rw [this, hBP]; exact hg
    · have : gf B = (hgne B).choose := if_neg hBP
      rw [this]; exact (hgne B).choose_spec
  have hgfP : gf P = true := if_pos rfl
  obtain ⟨fr, hfr⟩ := facts.gr.freezeRoot_nonempty S.E
    (M.gradeView (M.toHealing (x[m][u].st).st.core)) (x[m][u].st).st.core.F S.hc.η_SG (q + 1)
    (M.early S.E S.hc (q + 1) p) (M.late S.E S.hc (q + 1) p)
  obtain ⟨D, hD, hPD⟩ := facts.gr.preceq_freezeRoot S.E _ _ _ _ _ _ gf hgf hPT hgfP
    (fun B _ B' _ hB hB' => facts.gr.compatible_of_gradeBool_phase S.E S.hc _ _ _ p
      (gf B) (hgf B) hB (gf B') (hgf B') hB') fr hfr
  have hnone : M.phaseResult (M.cacheAtRound (x[m][u].st).cache (q + 1)) p
      = none := by
    cases hpr : M.phaseResult (M.cacheAtRound (x[m][u].st).cache (q + 1)) p with
    | none => rfl
    | some o =>
        exfalso
        rcases Restated.cacheResultsAfterDomain_sts facts S Sched x m u (q + 1) p o hpr with h | h
        · exact Nat.succ_ne_zero q h
        · linarith
  obtain ⟨τm, hl, hτm⟩ := hm
  obtain ⟨out₁, hout, hstm⟩ : ∃ out₁ : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) u (Record.wakeStage M Sched (τm : Int) x[m] u) (τm : Int) ⇢ out₁ ∧
        x[m + 1][u].st = out₁.1 := by
    rcases Restated.st_succ_of_tick_awake facts S Sched x u hl (by rw [hτm]; exact hu)
      (by rw [hτm]; exact hdvd) with h | ⟨hno, -⟩
    · exact h
    · obtain ⟨out, hout⟩ := hne m ⟨τm, hl, hτm⟩
      rw [← hτm] at hout
      exact absurd hout (hno out)
  obtain ⟨c₁, hc₁⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
    (M.toHealing (x[m][u].st).st.core) (M.domain S.E S.hc (q + 1) p) (x[m][u].st).cache
  have hc1 : (x[m + 1][u].st).cache = M.clipCache (x[m + 1][u].st).st.core.F c₁ := by
    rw [hstm]
    have _hr_s1 := Record.reachedNode_wakeStage facts S Sched x (m) u (↑τm)
    exact facts.nd.namedNode_tick_cache _ u _ _ out₁ hout c₁
      (by rw [Record.wakeStage_st facts, Record.wakeStage_cache facts, hτm]; exact hc₁)
  have hfr' : M.freezeRoot S.E (M.gradeView (M.toHealing (x[m][u].st).st.core))
      (M.toHealing (x[m][u].st).st.core).toFG.F S.hc.η_SG (q + 1) (M.early S.E S.hc (q + 1) p)
      (M.late S.E S.hc (q + 1) p) ⇢ fr := by
    rw [facts.sto.Sts_toHealing_F]
    exact hfr
  have hwrite : M.phaseResult (M.cacheAtRound c₁ (q + 1)) p
      = some (fr.map (fun B => M.clipGrade B (M.toHealing (x[m][u].st).st.core).toFG.F)) := by
    rcases hdρ with h | h
    · exact facts.gr.phaseResult_onPhaseTick_domain S.E S.hc _ _ _ (by rw [h]) rfl hnone
        c₁ hc₁ fr hfr'
    · exact facts.gr.phaseResult_onPhaseTick_domain_current S.E S.hc _ _ (le_of_lt hdpos) _ h rfl hnone
        c₁ hc₁ fr hfr'
  rw [hD, Option.map_some, facts.sto.Sts_toHealing_F] at hwrite
  have hbase : Restated.PhaseEntryAbove M S Sched x q p P (m + 1) u := by
    refine ⟨?_, ?_, M.clipGrade (M.clipGrade D (x[m][u].st).st.core.F)
      (x[m + 1][u].st).st.core.F, ?_, ?_⟩
    · rw [hc1, facts.gr.clipCache_round, facts.gr.onPhaseTick_round _ _ _ _ _ c₁ hc₁]
      rcases hdρ with h | h
      · rw [h]
      · rw [h]; exact Nat.le_succ q
    · rw [hc1, facts.gr.clipCache_round, facts.gr.onPhaseTick_round _ _ _ _ _ c₁ hc₁, hm1]
    · rw [hc1]; exact facts.gr.phaseResult_clipCache_some hwrite
    · exact facts.gr.preceq_clipGrade (hPF (m + 1) hmk) _ (facts.gr.preceq_clipGrade (hPF m (by omega)) D hPD)
  have hendk : (M.round_of S.hc (S.E.slotOf (x[k].time : Int))) ≤ q + 1 := by
    rw [← hτρ]; exact Restated.roundAt_mono_sr facts S (by linarith)
  obtain ⟨hq0, hq1, e, he, hPe⟩ := Restated.phaseEntryAbove_kept facts S Sched x hmk hbase hendk hPF
  have hcases := round_cases_pi _ _ ((M.round_of S.hc (S.E.slotOf τ))) hq0
    (by rw [hτρ]; exact le_trans hq1 hendk) (le_of_eq hτρ)
  have _hrr_s1 := facts.nd.reachedRead_of_node _ (Record.reachedNode_sts facts S Sched x k u)
  have hkept := facts.gr.phaseResult_onPhaseTick_kept S.E S.hc (M.toHealing (x[k][u].st).st.core)
    τ (x[k][u].st).cache he hcases c hc
  have hst' : Block.compatible P st.toFG.F = true := hst
  exact ⟨M.clipGrade (M.clipGrade e (M.toHealing (x[k][u].st).st.core).toFG.F) st.toFG.F,
    facts.gr.readFrame_phase_of_cache hkept,
    facts.gr.preceq_clipGrade hst' _
      (by rw [facts.sto.Sts_toHealing_F]; exact facts.gr.preceq_clipGrade (hPF k le_rfl) e hPe)⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If `ρ ≥ 1` and `m` is the last step before round `ρ`'s phase-`p` domain instant, then
    `x[m].time + 1` is that instant. -/
theorem time_of_stepBefore_domain (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (htd : Restated.TimeDiverges M x) {ρ : Nat} (hρ : 1 ≤ ρ)
    {p : Protocol.Phase} {m : Nat}
    (hm : Restated.stepBeforeInstant M x m (M.domain S.E S.hc ρ p)) :
    (x[m].time : Int) + 1 = M.domain S.E S.hc ρ p := by
  obtain ⟨q, rfl⟩ : ∃ q : Nat, ρ = q + 1 := ⟨ρ - 1, by omega⟩
  obtain ⟨hdpos, -, -, -, -⟩ := Restated.domain_facts_att facts S q p
  obtain ⟨m', hm'⟩ := Restated.exists_tickStepAt facts x htd hdpos
  have hmm := Restated.stepBeforeInstant_unique_sr facts S Sched x hm (Restated.stepBeforeInstant_of_tickStepAt facts x hm')
  rw [hmm]
  exact (Restated.tickStepAt_time facts x hm').2

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If the adversary holds `v` at no time up to step `m`, and step `k`'s time is at or before step
    `m`'s, then the adversary holds `v` at no time up to step `k`. -/
theorem honestThrough_of_time_le (facts : Record.Facts M) {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (Record.protocolOf M S) Sched} {m k : Nat} {v : V} (h : Restated.HonestThrough M Sched x m v)
    (hkm : (x[k].time : Int) ≤ (x[m].time : Int)) : Restated.HonestThrough M Sched x k v :=
  fun t ht => h t (le_trans ht hkm)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If step `d`'s time is strictly before step `k`'s, then `d < k`. -/
theorem lt_of_time_lt (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    {d k : Nat} (h : (x[d].time : Int) < (x[k].time : Int)) : d < k := by
  by_contra hcon
  have := Restated.time_mono_int facts S Sched x (Nat.le_of_not_lt hcon)
  linarith

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If the adversary has held `v_1` at no time up to step `m`, then every token in an outcome `X` of
    `w`'s raw view of `v_1` for the round-`ρ` grade, at any cutoff, has a round less than `ρ`, and
    some tick step `n'` at that round's action instant has `v_1` awake there and the token's key
    equal to the `confirmed` field of every attestation that `v_1`'s action of that round can
    compute from its node state at `n'`. -/
theorem rawView_token_facts (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {m : Nat} {w v_1 : V} (hv_1 : Restated.HonestThrough M Sched x m v_1) {ρ : Nat} {c : Int}
    {tok : Protocol.Token (Option BlockId)}
    {X : Finset (Protocol.Token (Option BlockId))}
    (hX : M.rawView (M.gradeView (M.toHealing (x[m][w].st).st.core)) S.hc.η_SG ρ c v_1 ⇢ X)
    (htok : tok ∈ X) :
    tok.round < ρ ∧ ∃ n' : Nat, Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S tok.round)) ∧
      v_1 ∈ Sched.awake ((Restated.Vocabulary.Execution.Setup.a M S tok.round)) ∧
      ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n'][v_1].st) v_1 tok.round,
        tok.key = a.confirmed := by
  have hwin := Restated.rawView_round_mem_window facts (Restated.sgVotesRoundIndexed_sts facts S Sched x m w) S.hc.η_SG ρ c
    v_1 X hX tok htok
  refine ⟨facts.fc.mem_latest_window_lt hwin, ?_⟩
  obtain ⟨Y, hY⟩ := facts.gr.rawInputs_nonempty
    (M.gradeView (M.toHealing (x[m][w].st).st.core)) S.hc.η_SG ρ c v_1
  obtain ⟨y, hy, hyt⟩ := (facts.gr.mem_rawView_iff _ _ _ _ _ tok X hX Y hY).mp htok
  obtain ⟨⟨k, -, hyk⟩, hyidx, -⟩ := facts.gr.rawInputs_mem_window _ _ _ _ _ Y hY hy
  have hykround : y.round = k := Restated.sgVotesRoundIndexed_sts facts S Sched x m w k y hyk
  have hymem : y ∈ (M.gradeView (M.toHealing (x[m][w].st).st.core)).sg_votes y.round := by
    rw [hykround]; exact hyk
  obtain ⟨n', htick', hawk, hyeq⟩ :=
    Restated.token_of_honest_sender facts S Sched x hexec hv_1 hymem hyidx
  have hyq : y.round = tok.round := by rw [← facts.gr.token_round y, hyt]
  rw [hyq] at htick' hawk hyeq
  refine ⟨n', htick', hawk, fun a ha => ?_⟩
  rw [← hyt, facts.gr.token_key, hyeq a ha, facts.sto.sgVote_confirmed]

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If `v_1` is honest through the step after the tick `n'` at `S.a q`, `a` is a round-`q`
    attestation `v_1`'s action can compute from its node state at `n'` and names the root `root`,
    every body of `v_1` after that tick whose root such an attestation names is a descendant of `P`,
    and `root` resolves in the tree of `w` (honest through `m`) after `m` steps to `B`, then `B` is
    `P` or a descendant of `P`. -/
theorem preceq_of_find_attested (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {q n' : Nat} {v_1 : V} (hv_1 : Restated.HonestThrough M Sched x (n' + 1) v_1) {P : Block V}
    (hcov : ∀ C : NamedBlock V, C ∈ (x[n' + 1][v_1].st).st.bodies →
      ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n'][v_1].st) v_1 q,
      a.confirmed = some C.root →
      Block.Preceq P C.erase)
    {root : BlockId}
    (a : NamedAttestation V)
    (ha : a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n'][v_1].st) v_1 q)
    (hroot : a.confirmed = some root)
    {m : Nat} {w : V} (hwm : Restated.HonestThrough M Sched x m w) {B : Block V}
    (hfind : Block.find? (M.gradeView (M.toHealing (x[m][w].st).st.core)).T root = some B) :
    Block.Preceq P B := by
  rw [facts.gr.Sts_gradeView_T] at hfind
  have hBT := Proofs.HealingLemmas.find?_mem hfind
  have hBr := Proofs.HealingLemmas.find?_root hfind
  obtain ⟨D, hD, hDe⟩ := Restated.exists_named_of_mem_tree facts S Sched x m w hBT
  obtain ⟨C, hC, hCroot⟩ := Restated.hhead_mem_of_tick facts S Sched x n' q v_1 a ha root hroot
  have hCD : C.erase = D.erase :=
    Restated.erase_eq_of_root_eq_inLog facts S Sched x hexec (Restated.blockInLog_of_mem_bodies facts S Sched hv_1 hC)
      (Restated.blockInLog_of_mem_bodies facts S Sched hwm hD)
      (by rw [hCroot, ← Proofs.NamedWire.erase_root D, hDe, hBr])
  rw [← hDe, ← hCD]
  exact hcov C hC a ha (by rw [hroot, hCroot])

end

local macro "pGFs% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.ClaimAsyncK_GradeFor)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- From any node state `before`, validator `v`'s round-`ρ` action read can compute some attestation
    `a`, and `a.confirmed` is `some root` for some block root `root`. -/
private theorem exists_attestation_confirmed_pi (facts : Record.Facts M) (S : Setup V)
    (before : M.N) (v : V) (ρ : Round) :
    ∃ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) before v ρ,
      ∃ root : BlockId, a.confirmed = some root := by
  obtain ⟨a, ha⟩ := (pGFs% actionAttestationFrom_nonemptyGradeFor) facts (Setup.alwaysAwake S)
    before v ρ
  obtain ⟨nr, hnr, ns, rec, hD⟩ := id ha
  obtain ⟨g, hg'⟩ := facts.gr.read_nonempty (M.gradeContract nr.cache) S.E S.hc
    (M.toHealing nr.st.core) ρ
  have hg := (facts.nd.gradeContract_read nr.cache S.E S.hc _ ρ g).1 hg'
  exact ⟨a, ha, _, Restated.attest_confirmed_eq_sgVote facts S before v ρ nr hnr (ns, rec, a) hD g hg⟩

/-- If `C` is in the store's tree, the store's finalized block is an ancestor of `C`, some block `W`
    of the store's tree is a descendant of `C` whose recorded chain-state height is at least the
    store's `h_max` minus one, and the store's fork-choice root is an ancestor of `C`, then `C` is
    in the store's filtered block tree. -/
private theorem mem_filtered_of_parts_pi (facts : Record.Facts M) (st : M.S) {C W : Block V}
    (hC : C ∈ st.T) (hF : Block.Preceq st.F C)
    (hW : W ∈ st.T) (hCW : Block.Preceq C W) (hh : st.h_max - 1 ≤ (st.σ W).h)
    (hroot : Block.Preceq (M.get_fg_root (M.toHealing st).toFG) C) :
    C ∈ M.get_filtered_block_tree (M.toHealing st).toFG := by
  refine facts.fc.mem_get_filtered_block_tree_of_parts (M.toHealing st) ?_ ?_ ?_ hCW ?_ hroot
  · rw [facts.sto.toHealing_T]; exact hC
  · rw [facts.sto.ModelProperties_toHealing_F]; exact hF
  · rw [facts.sto.toHealing_T]; exact hW
  · rw [facts.sto.ModelProperties_toHealing_h_max, facts.sto.ModelProperties_toHealing_σ]
    exact hh

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Let `ρ` be a round from `r + 2` to `r + η_SG + 1`, `m` the last step before one of its
    phase-domain instants, `u` a member of `activeRoundWThroughNext S Sched r` honest through `m`,
    and `k` a step at a strictly later time at which `u`'s finalized block is an ancestor of `P`. If
    the hand-over facts hold for `P` at round `r`, `RoundAttestsAbove` holds at every round from
    `r + 2` to `ρ − 1`, the participation premise holds, and the delivery premises hold before
    `b₀ ≥ S.a (r + 1) + Δ`, then every outcome of the grade test of `P` for round `ρ` at that phase,
    on `u`'s store after `m` steps, is `true`. -/
theorem graded_period_of_rounds (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {b₀ b₁ : Int} (hsync : Restated.SynchronyFromWakeOutside M S x b₀ b₁)
    (hcatch : Restated.CatchUpOnWakeOutside M S x b₀ b₁) (hmult : AwakeAtMultiples S Sched)
    (htd : Restated.TimeDiverges M x) (hmono : Sched.MonotoneCorruption) {r : Nat} {P : Block V}
    (hP : Restated.StableHandover M S Sched x r P) (hfix : Restated.fixedRoundSleepinessCountedW M S Sched r)
    (hgst : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1))) (hb₀ : (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) + S.E.Δ ≤ b₀)
    {ρ : Nat} (hρ₁ : r + 2 ≤ ρ) (hρ₂ : ρ ≤ r + S.hc.η_SG + 1)
    (hR : ∀ q : Nat, r + 2 ≤ q → q < ρ → Restated.RoundAttestsAbove M S Sched x r P q)
    {p : Protocol.Phase} {m : Nat} (hm : Restated.stepBeforeInstant M x m (M.domain S.E S.hc ρ p))
    {u : V} (hu : u ∈ Restated.activeRoundWThroughNext M S Sched r) (hum : Restated.HonestThrough M Sched x m u)
    {k : Nat} (hmk : (x[m].time : Int) < (x[k].time : Int))
    (hFk : Block.Preceq (x[k][u].st).st.core.F P) :
    ∀ g : Bool, M.gradeBool S.E (M.gradeView (M.toHealing (x[m][u].st).st.core))
        (x[m][u].st).st.core.F S.hc.η_SG ρ (M.early S.E S.hc ρ p) (M.late S.E S.hc ρ p) P ⇢ g →
      g = true := by
  intro g hg
  have hd := S.E.Δ_pos
  obtain ⟨n₁, hn₁⟩ := Restated.exists_tickStepAt facts x htd (Restated.action_pos facts S (r + 1))
  obtain ⟨hn₁1, -⟩ := Restated.tickStepAt_time facts x hn₁
  have hmt : (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) + S.E.Δ ≤ (x[m].time : Int) :=
    Restated.action_delta_le_time_of_stepBefore facts S Sched x htd (show r + 1 + 1 ≤ ρ by omega) hm
  have hwin : u ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)) + S.E.Δ) := by
    have h1 := Restated.healA_succ facts S r
    have h2 := twelve_delta_le_wAttest_kit S
    have hle : (M.a S.hc S.E.Δ r) - wAttest S ≤ (M.a S.hc S.E.Δ (r + 1)) := by linarith
    unfold Restated.activeRoundWThroughNext at hu
    exact awakeThroughout_sub Sched hle le_rfl hu
  have hFd : ∀ d : Nat, (x[d].time : Int) < (x[k].time : Int) →
      Block.Preceq (x[d][u].st).st.core.F P := fun d hd' =>
    preceq_trans_Preceq (Restated.F_mono facts S Sched x u (le_of_lt (Restated.lt_of_time_lt facts S Sched x hd'))) hFk
  choose Re hRe using fun v_1 : V => facts.gr.readyView_nonempty
    (M.gradeView (M.toHealing (x[m][u].st).st.core)) (x[m][u].st).st.core.F S.hc.η_SG ρ
    (M.early S.E S.hc ρ p) v_1
  choose Wl hWl using fun v_1 : V => facts.gr.rawView_nonempty
    (M.gradeView (M.toHealing (x[m][u].st).st.core)) S.hc.η_SG ρ (M.late S.E S.hc ρ p) v_1
  refine Restated.gradeBool_period_of_tokens_resolved facts S Sched x hexec htd hmono hfix (by omega)
    hρ₂ hm Re hRe ?_ Wl hWl ?_ g hg
  · -- `hready`: the round-`(r + 1)` token of each counted member
    intro v_1 hv_1
    have hv_1c := (Finset.mem_sdiff.1 hv_1).1
    have hv_1A := Restated.activeRoundWThroughNextCountedAt_subset facts S Sched r ρ hv_1c
    have hv_1W := Restated.activeRoundWThroughNext_subset_activeRoundW_succ facts S Sched r hv_1A
    have hv_1m := Restated.honestThrough_of_mem_countedAt facts S Sched x htd hmono (by omega) hm hv_1
    have hv_1n : Restated.HonestThrough M Sched x (n₁ + 1) v_1 :=
      Restated.honestThrough_of_time_le facts hv_1m (by rw [hn₁1]; linarith)
    have hcov := hP.covers (r + 1) (Or.inr rfl) n₁ hn₁ v_1 hv_1W hv_1n
    exact Restated.exists_ready_token_ge_window facts S Sched x hexec hsync hcatch hmult htd hn₁ hgst hb₀
      hv_1W hv_1m hmt hwin hum
      (fun C hC a ha hconf d v_0 _ _ _ hdle => Or.inl
        (preceq_eq_true_iff_Preceq.mpr
          (preceq_trans_Preceq (hFd d (by linarith)) (hcov C hC a ha hconf))))
      (fun C hC a ha hconf => compatible_of_cases
        (Or.inr (preceq_trans_Preceq (hFd m hmk) (hcov C hC a ha hconf))))
      (q := ρ) (by omega) (by omega) p (Re v_1) (hRe v_1)
  · -- `hcover`: every raw token of round at least `r + 1` covers `P` where it resolves
    intro v_1 hv_1 tok htok hq
    have hv_1c := (Finset.mem_sdiff.1 hv_1).1
    have hv_1A := Restated.activeRoundWThroughNextCountedAt_subset facts S Sched r ρ hv_1c
    have hv_1m := Restated.honestThrough_of_mem_countedAt facts S Sched x htd hmono (by omega) hm hv_1
    obtain ⟨hlt, n', hn', hawk, hkey⟩ :=
      Restated.rawView_token_facts facts S Sched x hexec hv_1m (hWl v_1) htok
    obtain ⟨hn'1, -⟩ := Restated.tickStepAt_time facts x hn'
    have hSq : (Restated.Vocabulary.Execution.Setup.a M S tok.round) + S.E.Δ ≤ (x[m].time : Int) :=
      Restated.action_delta_le_time_of_stepBefore facts S Sched x htd (show tok.round + 1 ≤ ρ by omega) hm
    have hv_1n : Restated.HonestThrough M Sched x (n' + 1) v_1 :=
      Restated.honestThrough_of_time_le facts hv_1m (by rw [hn'1]; linarith)
    obtain ⟨a, ha, root, hconf⟩ :=
      exists_attestation_confirmed_pi facts S (x[n'][v_1].st) v_1 tok.round
    refine ⟨root, (hkey a ha).trans hconf, fun B hB => ?_⟩
    have hcov : ∀ C : NamedBlock V, C ∈ (x[n' + 1][v_1].st).st.bodies →
        ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n'][v_1].st) v_1 tok.round,
        a.confirmed = some C.root →
        Block.Preceq P C.erase := by
      by_cases hr1 : tok.round = r + 1
      · have hv_1W := Restated.activeRoundWThroughNext_subset_activeRoundW_succ facts S Sched r hv_1A
        rw [hr1] at hn' ⊢
        exact hP.covers (r + 1) (Or.inr rfl) n' hn' v_1 hv_1W hv_1n
      · have hq2 : r + 2 ≤ tok.round := by omega
        have hnot : v_1 ∉ Restated.attestersNotAwakeSinceFirstCutoffIn M S Sched (r + 2) (ρ - 1) := by
          unfold Restated.activeRoundWThroughNextCountedAt at hv_1c
          exact (Finset.mem_sdiff.1 hv_1c).2
        have hawT : v_1 ∈ Sched.awakeThroughout
            (M.early S.E S.hc tok.round .g2 - S.E.Δ) ((Restated.Vocabulary.Execution.Setup.a M S tok.round)) := by
          by_contra hcon
          apply hnot
          unfold Restated.attestersNotAwakeSinceFirstCutoffIn
          exact Finset.mem_biUnion.2 ⟨tok.round, Finset.mem_Icc.2 ⟨hq2, by omega⟩,
            Finset.mem_sdiff.2 ⟨hawk, hcon⟩⟩
        exact fun C hC a' ha' hconf' =>
          (hR tok.round hq2 hlt n' hn' v_1 hv_1A hv_1n hawT a' ha').1 C hC hconf'
    exact Restated.preceq_of_find_attested facts S Sched x hexec hv_1n hcov a ha hconf hum hB

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Let `m` be the last step before one of round `r + 1`'s phase-domain instants, `w` honest through
    `m` and awake at every time from `S.a r` to `x[m].time`, and `k` a step after `m` at which `w`'s
    finalized block is an ancestor of `P`. If the hand-over facts hold for `P` at round `r`,
    round-level sleepiness holds from a time at or before the opening of round `r + 1`, and the
    delivery premises hold before `b₀ ≥ S.a r + Δ`, then every outcome of the grade test of `P` for
    round `r + 1` at that phase, on `w`'s store after `m` steps, is `true`. -/
theorem graded_base_reader (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {b₀ b₁ : Int} (hsync : Restated.SynchronyFromWakeOutside M S x b₀ b₁)
    (hcatch : Restated.CatchUpOnWakeOutside M S x b₀ b₁) (hmult : AwakeAtMultiples S Sched)
    (htd : Restated.TimeDiverges M x) (hmono : Sched.MonotoneCorruption) {tE : Int}
    (hrs : Restated.roundSleepinessW M S Sched tE) {r : Nat} {P : Block V}
    (hP : Restated.StableHandover M S Sched x r P)
    (htE : tE ≤ M.opening S.E S.hc (r + 1))
    (hgst : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S r)) (hb₀ : (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ ≤ b₀)
    {p : Protocol.Phase} {m : Nat}
    (hm : Restated.stepBeforeInstant M x m (M.domain S.E S.hc (r + 1) p))
    {w : V} (hw : w ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S r)) (x[m].time : Int))
    (hwm : Restated.HonestThrough M Sched x m w)
    {k : Nat} (hmk : (x[m].time : Int) < (x[k].time : Int))
    (hFk : Block.Preceq (x[k][w].st).st.core.F P) :
    ∀ g : Bool, M.gradeBool S.E (M.gradeView (M.toHealing (x[m][w].st).st.core))
        (x[m][w].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) p)
        (M.late S.E S.hc (r + 1) p) P ⇢ g → g = true := by
  intro g hg
  have hd := S.E.Δ_pos
  have hη := S.hc.η_SG_ge_one
  obtain ⟨n, hn⟩ := Restated.exists_tickStepAt facts x htd (Restated.action_pos facts S r)
  obtain ⟨hn1, -⟩ := Restated.tickStepAt_time facts x hn
  have hmt : (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ ≤ (x[m].time : Int) :=
    Restated.action_delta_le_time_of_stepBefore facts S Sched x htd (show r + 1 ≤ r + 1 from le_rfl) hm
  have hFd : ∀ d : Nat, (x[d].time : Int) < (x[k].time : Int) →
      Block.Preceq (x[d][w].st).st.core.F P := fun d hd' =>
    preceq_trans_Preceq (Restated.F_mono facts S Sched x w (le_of_lt (Restated.lt_of_time_lt facts S Sched x hd'))) hFk
  have hmember : ∀ v_1 ∈ Restated.freshAttestersW M S Sched x r m,
      v_1 ∈ Restated.activeRoundW M S Sched r ∧ Restated.HonestThrough M Sched x m v_1 ∧
      Restated.HonestThrough M Sched x (n + 1) v_1 ∧
      ∀ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies →
        ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v_1].st) v_1 r,
        a.confirmed = some C.root →
        Block.Preceq P C.erase := by
    intro v_1 hv_1
    obtain ⟨hv_1W, hv_1m⟩ := (Restated.mem_freshAttestersW facts).mp hv_1
    have hv_1n : Restated.HonestThrough M Sched x (n + 1) v_1 :=
      Restated.honestThrough_of_time_le facts hv_1m (by rw [hn1]; linarith)
    exact ⟨hv_1W, hv_1m, hv_1n, hP.covers r (Or.inl rfl) n hn v_1 hv_1W hv_1n⟩
  have hadm : ∀ v_1 ∈ Restated.freshAttestersW M S Sched x r m,
      ∀ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies →
        ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v_1].st) v_1 r,
        a.confirmed = some C.root →
        Restated.ReaderAdmitsInPhase M S Sched x 0 ((Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ) w C := by
    intro v_1 hv_1 C hC a ha hconf d v_0 _ _ _ hdle
    exact Or.inl (preceq_eq_true_iff_Preceq.mpr (preceq_trans_Preceq (hFd d (by linarith))
      ((hmember v_1 hv_1).2.2.2 C hC a ha hconf)))
  choose Re hRe using fun v_1 : V => facts.gr.readyView_nonempty
    (M.gradeView (M.toHealing (x[m][w].st).st.core)) (x[m][w].st).st.core.F S.hc.η_SG (r + 1)
    (M.early S.E S.hc (r + 1) p) v_1
  choose Wl hWl using fun v_1 : V => facts.gr.rawView_nonempty
    (M.gradeView (M.toHealing (x[m][w].st).st.core)) S.hc.η_SG (r + 1)
    (M.late S.E S.hc (r + 1) p) v_1
  refine (Restated.gradeBool_base_of_tokens facts S Sched x hexec htd hmono hrs htE hm
    Re hRe ?_ Wl hWl ?_).1 g hg
  · intro v_1 hv_1
    obtain ⟨hv_1W, hv_1m, -, hcov⟩ := hmember v_1 hv_1
    exact Restated.exists_ready_token_ge facts S Sched x hexec hsync hcatch hmult htd hn hgst hb₀ hv_1W
      hv_1m hmt hw hwm (hadm v_1 hv_1)
      (fun C hC a ha hconf => compatible_of_cases
        (Or.inr (preceq_trans_Preceq (hFd m hmk) (hcov C hC a ha hconf))))
      (q := r + 1) le_rfl (Nat.add_le_add_left hη r) p (Re v_1) (hRe v_1)
  · intro v_1 hv_1 tok htok hq
    obtain ⟨-, hv_1m, -, hcov⟩ := hmember v_1 hv_1
    have hle := Restated.rawView_round_le facts S Sched x m w r _ v_1 (Wl v_1) (hWl v_1) tok htok
    have hround : tok.round = r := le_antisymm hle hq
    obtain ⟨n', hn', hkey⟩ :=
      Restated.rawView_key_of_honest_at facts S Sched x hexec hv_1m (hWl v_1) htok hround
    have hnn : n' = n := Restated.tickStepAt_unique facts x hn' hn
    rw [hnn] at hkey
    obtain ⟨a, ha, root, hconf⟩ := exists_attestation_confirmed_pi facts S (x[n][v_1].st) v_1 r
    obtain ⟨C, hC, hCroot, hfind, -⟩ :=
      Restated.attested_block_resolves facts S Sched x hexec hsync hcatch hmult htd hn hgst hb₀ hv_1m hmt
        hw hwm (hadm v_1 hv_1) a ha root hconf
    refine ⟨root, C.erase, (hkey a ha).trans hconf, ?_, hcov C hC a ha (by rw [hconf, hCroot])⟩
    rw [facts.gr.Sts_gradeView_T]
    exact hfind

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Let `n₁` be the tick step at `S.a (r + 1)` and `k ≥ n₁ + 1` a step whose time is before
    `S.a (r + η_SG + 1)`. If the hand-over facts hold for `P` at round `r` and `RoundAttestsAbove`
    holds at every round from `r + 2` whose action instant is at or before `x[k].time`, then
    `VotesClassified S Sched x r P n₁ k` holds. -/
theorem votesClassified_of_rounds (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hwakes : Restated.WakesAtActionInstants M S Sched) (hsleeps : Restated.SleepsAfterActionInstants M S Sched)
    {r : Nat} {P : Block V} (hP : Restated.StableHandover M S Sched x r P)
    {n₁ : Nat} (hn₁ : Restated.tickStepAt M x n₁ ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)))) {k : Nat} (hk : n₁ + 1 ≤ k)
    (hkt : (x[k].time : Int) < (Restated.Vocabulary.Execution.Setup.a M S (r + S.hc.η_SG + 1)))
    (hR : ∀ q : Nat, r + 2 ≤ q → (Restated.Vocabulary.Execution.Setup.a M S q) ≤ (x[k].time : Int) →
      Restated.RoundAttestsAbove M S Sched x r P q) :
    Restated.VotesClassified M S Sched x r P n₁ k := by
  intro u a h root tmo hu ha hsent hpair
  obtain ⟨-, k', hk'k, htick, hawk, out, hout, hemit⟩ :=
    Restated.attest_round_of_sent facts S Sched x (tB := (x[k].time : Int)) hu hexec.toUnforgeability ha
      le_rfl hsent
  have _hr_s2 := Record.reachedNode_wakeStage facts S Sched x (k') u (Restated.Vocabulary.Execution.Setup.a M S a.round)
  have _hv_s3 := Record.runs_as_wakeStage facts S Sched x (k') u (Restated.Vocabulary.Execution.Setup.a M S a.round)
  have haeq := Restated.attest_of_tick_eq facts S u _ a.round hout hemit
  rw [Restated.actionAttestationFrom_wakeStage facts (Setup.alwaysAwake S) Sched _ x[k'] u a.round] at haeq
  have hamem : a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[k'][u].st) u a.round := by
    obtain ⟨a', ha'⟩ := (pGFs% actionAttestationFrom_nonemptyGradeFor) facts (Setup.alwaysAwake S)
      (x[k'][u].st) u a.round
    have haa := haeq a' ha'
    rw [← haa] at ha'
    exact ha'
  obtain ⟨hk'1, hk'0⟩ := Restated.tickStepAt_time facts x htick
  obtain ⟨hn₁1, -⟩ := Restated.tickStepAt_time facts x hn₁
  by_cases hq : a.round ≤ r + 1
  · -- an attestation of a round at most `r + 1`: in the sent log at the hand-over
    have hk'n : k' + 1 ≤ n₁ + 1 := by
      by_contra hcon
      have h1 := Restated.time_mono_int facts S Sched x (show n₁ + 1 ≤ k' by omega)
      have h2 := Restated.healA_mono facts S hq
      have h3 : (Restated.Vocabulary.Execution.Setup.a M S a.round) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) := h2
      linarith
    have hrunk : M.awake_for_grade2 (Setup.alwaysAwake S) u
        (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S a.round) x[k'] u) a.round := by
      by_contra hno
      have h0 := facts.nd.tick_at_action_asleep (Setup.alwaysAwake S) u _ a.round out hout hno
      rw [h0] at hemit
      exact List.not_mem_nil hemit
    have hemit' := Restated.attest_emitted_at_tick_from facts S Sched x htick hawk ⟨out, hout⟩ hrunk a hamem
    have hsent' := Restated.mem_sent_of_le facts x hk'n hemit'
    have hun : Restated.HonestThrough M Sched x (n₁ + 1) u :=
      Restated.honestThrough_of_time_le facts hu (Restated.time_mono_int facts S Sched x hk)
    exact Restated.votesClassified_of_handover facts S Sched x r P hP hn₁ u a h root tmo hun ha hsent' hpair
  · -- an attestation of a later round
    have hq' : r + 2 ≤ a.round := Nat.succ_le_of_lt (Nat.lt_of_not_le hq)
    have hSq : (Restated.Vocabulary.Execution.Setup.a M S a.round) ≤ (x[k].time : Int) := by
      rw [← hk'1]; exact Restated.time_mono_int facts S Sched x hk'k
    have hq2 : a.round ≤ r + S.hc.η_SG := by
      by_contra hcon
      have h1 : r + S.hc.η_SG + 1 ≤ a.round := Nat.succ_le_of_lt (Nat.lt_of_not_le hcon)
      have h2 : (Restated.Vocabulary.Execution.Setup.a M S (r + S.hc.η_SG + 1)) ≤ (Restated.Vocabulary.Execution.Setup.a M S a.round) := Restated.healA_mono facts S h1
      linarith
    have huW := Restated.active_of_nonEmpty_heightVote facts S Sched x hwakes hsleeps
      (Finset.mem_sdiff.1 hawk).1 a hamem hpair
    by_cases hin : u ∈ Restated.activeRoundWThroughNext M S Sched r
    · left
      have hawT : u ∈ Sched.awakeThroughout (M.early S.E S.hc a.round .g2 - S.E.Δ)
          ((Restated.Vocabulary.Execution.Setup.a M S a.round)) := by
        have h1 := Restated.early_g2_eq_healA facts S a.round
        have h2 := twelve_delta_le_wAttest_kit S
        have hle : (M.a S.hc S.E.Δ a.round) - wAttest S
            ≤ M.early S.E S.hc a.round .g2 - S.E.Δ := by rw [h1]; linarith
        unfold Restated.activeRoundW at huW
        exact awakeThroughout_sub Sched hle le_rfl huW
      have huk' : Restated.HonestThrough M Sched x (k' + 1) u :=
        Restated.honestThrough_of_time_le facts hu (Restated.time_mono_int facts S Sched x hk'k)
      exact (hR a.round hq' hSq k' htick u hin huk' hawT a hamem).2 h root tmo hpair
    · right; right
      unfold Restated.activeOutsideFixedIn
      exact Finset.mem_sdiff.2 ⟨Finset.mem_biUnion.2
        ⟨a.round, Finset.mem_Icc.2 ⟨hq', hq2⟩, huW⟩, hin⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- For a round `ρ` from `r + 2` to `r + η_SG`, under the delivery premises before
    `b₀ ≥ S.a (r + 1) + Δ`, the participation premise, the long-term condition at
    `S.a (r + η_SG + 1)` and the hand-over facts for `P` at round `r`: if `RoundAttestsAbove` holds
    at every round from `r + 2` to `ρ − 1`, it holds at `ρ`. -/
theorem roundAttestsAbove_step (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {b₀ b₁ : Int} (hsync : Restated.SynchronyFromWakeOutside M S x b₀ b₁)
    (hcatch : Restated.CatchUpOnWakeOutside M S x b₀ b₁) (hmult : AwakeAtMultiples S Sched)
    (hwakes : Restated.WakesAtActionInstants M S Sched) (hsleeps : Restated.SleepsAfterActionInstants M S Sched)
    (htd : Restated.TimeDiverges M x) (hmono : Sched.MonotoneCorruption) {r : Nat} {P : Block V}
    (hP : Restated.StableHandover M S Sched x r P) (hfix : Restated.fixedRoundSleepinessCountedW M S Sched r)
    (hlt : Restated.longTermConditionUpToW M S Sched r ((Restated.Vocabulary.Execution.Setup.a M S (r + S.hc.η_SG + 1))))
    (hgst : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1))) (hb₀ : (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) + S.E.Δ ≤ b₀)
    {ρ : Nat} (hρ₁ : r + 2 ≤ ρ) (hρ₂ : ρ ≤ r + S.hc.η_SG)
    (hR : ∀ q : Nat, r + 2 ≤ q → q < ρ → Restated.RoundAttestsAbove M S Sched x r P q) :
    Restated.RoundAttestsAbove M S Sched x r P ρ := by
  intro n hn u hu hun hawT a ha
  obtain ⟨nr, hnr, ns, rec, hD⟩ := ha
  have hd := S.E.Δ_pos
  obtain ⟨n₁, hn₁⟩ := Restated.exists_tickStepAt facts x htd (Restated.action_pos facts S (r + 1))
  obtain ⟨hn₁1, -⟩ := Restated.tickStepAt_time facts x hn₁
  obtain ⟨hnt1, hnt0⟩ := Restated.tickStepAt_time facts x hn
  have hρa : (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) < (Restated.Vocabulary.Execution.Setup.a M S ρ) := by
    have h1 := Restated.healA_succ facts S (r + 1)
    have h2 := twelve_delta_le_wAttest_kit S
    have h3 : (Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1)) ≤ (Restated.Vocabulary.Execution.Setup.a M S ρ) := Restated.healA_mono facts S (by omega)
    have h4 : (Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1)) = (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) + wAttest S := h1
    linarith
  have hk : n₁ + 1 ≤ n := by
    by_contra hcon
    have h1 := Restated.time_mono_int facts S Sched x (show n + 1 ≤ n₁ + 1 by omega)
    linarith
  have hρη : (Restated.Vocabulary.Execution.Setup.a M S ρ) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + S.hc.η_SG + 1)) := Restated.healA_mono facts S (by omega)
  have hnt : (x[n].time : Int) < (Restated.Vocabulary.Execution.Setup.a M S (r + S.hc.η_SG + 1)) := by linarith
  have hvc := Restated.votesClassified_of_rounds facts S Sched x hexec hwakes hsleeps hP hn₁ hk hnt
    (fun q hq hSq => hR q hq (by
      by_contra hcon
      have := Restated.healA_mono facts S (Nat.le_of_not_lt hcon)
      have h' : (Restated.Vocabulary.Execution.Setup.a M S ρ) ≤ (Restated.Vocabulary.Execution.Setup.a M S q) := this
      linarith))
  have hltn := Restated.longTermConditionUpToW_mono facts S Sched r hmono (le_of_lt hnt) hlt
  have hun' : Restated.HonestThrough M Sched x n u :=
    Restated.honestThrough_of_time_le facts hun (Restated.time_mono_int facts S Sched x (Nat.le_succ n))
  obtain ⟨hFc, -⟩ := Restated.honest_roots_of_classified facts S Sched x hexec hmono hvc hltn hk hun'
  by_cases hPF : Block.Preceq P (x[n][u].st).st.core.F
  · have hPr := preceq_trans_Preceq hPF (Restated.F_preceq_fgRoot_sts facts S Sched x n u)
    exact ⟨fun C hC hconf =>
        Restated.attest_covers_of_fgRoot facts S Sched x hexec hun hPr nr hnr (ns, rec, a) hD C hC hconf,
      fun h root tmo hvote C hC hCroot =>
        Restated.attest_heightPair_compatible_of_fgRoot facts S Sched x hexec hn hun hPr nr hnr
          (ns, rec, a) hD h root tmo hvote C hC hCroot⟩
  · have hFP : Block.Preceq (x[n][u].st).st.core.F P :=
    (compatible_cases (compatible_iff_Compatible.mp hFc)).resolve_left hPF
    have hρq : ρ - 1 + 1 = ρ := by omega
    have hdl : ∀ p : Protocol.Phase,
        M.domain S.E S.hc ρ p < (Restated.Vocabulary.Execution.Setup.a M S ρ) := by
      intro p
      have h := (Restated.domain_facts_att facts S (ρ - 1) p).2.2.2.2
      rw [hρq] at h
      exact h
    have hgr : ∀ (p : Protocol.Phase) (m : Nat),
        Restated.stepBeforeInstant M x m (M.domain S.E S.hc ρ p) →
        M.gradeBool S.E (M.gradeView (M.toHealing (x[m][u].st).st.core))
          (x[m][u].st).st.core.F S.hc.η_SG ρ (M.early S.E S.hc ρ p)
          (M.late S.E S.hc ρ p) P ⇢ true := by
      intro p m hm
      have hmd := Restated.time_of_stepBefore_domain facts S Sched x htd (show 1 ≤ ρ by omega) hm
      have hdl' := hdl p
      have hmn : (x[m].time : Int) < (x[n].time : Int) := by linarith
      obtain ⟨g, hg⟩ := facts.gr.gradeBool_nonempty S.E
        (M.gradeView (M.toHealing (x[m][u].st).st.core)) (x[m][u].st).st.core.F S.hc.η_SG ρ
        (M.early S.E S.hc ρ p) (M.late S.E S.hc ρ p) P
      have hgt := Restated.graded_period_of_rounds facts S Sched x hexec hsync hcatch hmult htd hmono hP
        hfix hgst hb₀ hρ₁ (by omega) hR hm hu
        (Restated.honestThrough_of_time_le facts hun' (le_of_lt hmn)) hmn hFP g hg
      rw [hgt] at hg
      exact hg
    obtain ⟨hdpos, -⟩ := Restated.domain_facts_att facts S (ρ - 1) .g2
    rw [hρq] at hdpos
    obtain ⟨m₂, hm₂⟩ := Restated.exists_tickStepAt facts x htd hdpos
    have hm₂B := Restated.stepBeforeInstant_of_tickStepAt facts x hm₂
    have hg2 := hgr .g2 m₂ hm₂B
    obtain ⟨H, hH, hPH⟩ :=
      facts.gr.Sts_exists_mem_T_preceq_of_gradeBool _ _ _ _ _ _ _ _ true hg2 rfl
    have hPT : P ∈ (x[m₂][u].st).st.core.T := Restated.mem_T_of_preceq_sts facts S Sched x m₂ u
      (by rw [← facts.gr.Sts_gradeView_T]; exact hH) hPH
    obtain ⟨Pn, hPn, hPe⟩ := Restated.exists_named_of_mem_tree facts S Sched x m₂ u hPT
    have hm₂n : m₂ ≤ n := by
      have hmd := Restated.time_of_stepBefore_domain facts S Sched x htd (show 1 ≤ ρ by omega) hm₂B
      have hdl' := hdl .g2
      exact le_of_lt (Restated.lt_of_time_lt facts S Sched x (by linarith))
    have hPnn : Pn ∈ (x[n][u].st).st.bodies :=
      of_decide_eq_true (Restated.processed_mono facts S Sched x u (NamedObject.block Pn) hm₂n
        (decide_eq_true hPn))
    have hroot := Restated.mem_filtered_or_root_of_classified facts S Sched x hexec hmono hvc hltn hk hun'
      hPnn hPe
    exact ⟨fun C hC hconf =>
        Restated.attest_covers_of_graded facts S Sched x hexec htd
          (Nat.lt_of_lt_of_le (Nat.succ_pos _) hρ₁) hn hawT hun hgr hFc hroot nr hnr (ns, rec, a) hD
          C hC hconf,
      fun h root tmo hvote C hC hCroot =>
        Restated.attest_heightPair_compatible_of_graded facts S Sched x hexec htd
          (Nat.lt_of_lt_of_le (Nat.succ_pos _) hρ₁) hn hawT hun hgr hFc hroot nr hnr (ns, rec, a) hD
          h root tmo hvote C hC hCroot⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- On the premises of `roundAttestsAbove_step`, `RoundAttestsAbove` holds at every round from
    `r + 2` to `r + η_SG`. -/
theorem roundAttestsAbove_all (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {b₀ b₁ : Int} (hsync : Restated.SynchronyFromWakeOutside M S x b₀ b₁)
    (hcatch : Restated.CatchUpOnWakeOutside M S x b₀ b₁) (hmult : AwakeAtMultiples S Sched)
    (hwakes : Restated.WakesAtActionInstants M S Sched) (hsleeps : Restated.SleepsAfterActionInstants M S Sched)
    (htd : Restated.TimeDiverges M x) (hmono : Sched.MonotoneCorruption) {r : Nat} {P : Block V}
    (hP : Restated.StableHandover M S Sched x r P) (hfix : Restated.fixedRoundSleepinessCountedW M S Sched r)
    (hlt : Restated.longTermConditionUpToW M S Sched r ((Restated.Vocabulary.Execution.Setup.a M S (r + S.hc.η_SG + 1))))
    (hgst : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1))) (hb₀ : (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) + S.E.Δ ≤ b₀) :
    ∀ ρ : Nat, r + 2 ≤ ρ → ρ ≤ r + S.hc.η_SG → Restated.RoundAttestsAbove M S Sched x r P ρ := by
  intro ρ
  induction ρ using Nat.strong_induction_on with
  | _ ρ ih =>
      intro h1 h2
      exact Restated.roundAttestsAbove_step facts S Sched x hexec hsync hcatch hmult hwakes hsleeps htd
        hmono hP hfix hlt hgst hb₀ h1 h2 (fun q hq hqρ => ih q hqρ hq (by omega))

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Let step `k` be the tick at slot `s`'s confirmation instant `τ`, strictly after `S.a (r + 1)`
    and strictly before `S.a (r + η_SG + 1)`, and `w` a member of
    `activeRoundWThroughNext S Sched r`, honest through `k + 1` and awake at every time from
    `S.a r − wAttest S` to `τ`, whose finalized block after `k` steps is an ancestor of `P` and
    whose justified block there lies on one chain with `P`. Under the premises of the period and
    `RoundAttestsAbove` at every round of `[r + 2, r + η_SG]`, for every outcome `c` of `w`'s cache
    update at that tick, every block `G` the stable root read with `c` can return lies on one chain
    with `P`. -/
theorem stableRoot_compatible_at_tick (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {b₀ b₁ : Int} (hsync : Restated.SynchronyFromWakeOutside M S x b₀ b₁)
    (hcatch : Restated.CatchUpOnWakeOutside M S x b₀ b₁) (hmult : AwakeAtMultiples S Sched)
    (htd : Restated.TimeDiverges M x) (hmono : Sched.MonotoneCorruption) {tE : Int}
    (hrs : Restated.roundSleepinessW M S Sched tE) {r : Nat} {P : Block V}
    (hP : Restated.StableHandover M S Sched x r P) (hfix : Restated.fixedRoundSleepinessCountedW M S Sched r)
    (htE : tE ≤ M.opening S.E S.hc (r + 1)) (hgst : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S r))
    (hb₀ : (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) + S.E.Δ ≤ b₀)
    (hR : ∀ q : Nat, r + 2 ≤ q → q ≤ r + S.hc.η_SG → Restated.RoundAttestsAbove M S Sched x r P q)
    {w : V} (hwA : w ∈ Restated.activeRoundWThroughNext M S Sched r) {k : Nat} {s : Slot}
    (hks : Restated.tickStepAt M x k (M.confirmation_time S.E s))
    (hwr : w ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S r) - wAttest S) (x[k + 1].time : Int))
    (hwk : Restated.HonestThrough M Sched x (k + 1) w)
    (hτ₁ : (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) < M.confirmation_time S.E s)
    (hτ₂ : M.confirmation_time S.E s < (Restated.Vocabulary.Execution.Setup.a M S (r + S.hc.η_SG + 1)))
    (hFk : Block.Preceq (x[k][w].st).st.core.F P)
    (hJk : Block.Compatible P (x[k][w].st).st.core.J) :
    ∀ c : M.Cache, M.onPhaseTick S.E S.hc (M.toHealing (x[k][w].st).st.core)
        (M.confirmation_time S.E s) (x[k][w].st).cache ⇢ c →
    ∀ G : Block V,
      (M.gradeContract c).stableRoot S.E S.hc
          (M.toHealing (M.ns_setClock S.E (x[k][w].st).st
            (M.confirmation_time S.E s)).core)
          ((M.round_of S.hc) (M.ns_setClock S.E (x[k][w].st).st
            (M.confirmation_time S.E s)).core.s) ⇢ some G →
      Block.Compatible P G := by
  intro c hc G hG
  have hd := S.E.Δ_pos
  obtain ⟨hk1, hk0⟩ := Restated.tickStepAt_time facts x hks
  rw [facts.hd.Sts_setClock_core_s] at hG
  have hρ'₁ : r + 1 ≤ (M.round_of S.hc (S.E.slotOf (M.confirmation_time S.E s))) := by
    rw [← Restated.round_of_slotOf_action facts S (r + 1)]
    exact Restated.roundAt_mono_sr facts S (le_of_lt hτ₁)
  have hρ'₂ : (M.round_of S.hc (S.E.slotOf (M.confirmation_time S.E s)))
      ≤ r + S.hc.η_SG + 1 := by
    rw [← Restated.round_of_slotOf_action facts S (r + S.hc.η_SG + 1)]
    exact Restated.roundAt_mono_sr facts S (le_of_lt hτ₂)
  obtain ⟨q, hq⟩ : ∃ q : Nat,
      (M.round_of S.hc (S.E.slotOf (M.confirmation_time S.E s))) = q + 1 :=
    ⟨(M.round_of S.hc (S.E.slotOf (M.confirmation_time S.E s))) - 1,
      (Nat.sub_add_cancel (le_trans (Nat.succ_le_succ (Nat.zero_le r)) hρ'₁)).symm⟩
  rw [hq] at hG hρ'₁ hρ'₂
  obtain ⟨hdpos, hdvd, hdρ, hdlo, hdhi⟩ := Restated.domain_facts_att facts S q .g2
  have hτpos : (0 : Int) ≤ M.confirmation_time S.E s := by
    have := Restated.action_pos facts S (r + 1); linarith
  have hdτ : M.domain S.E S.hc (q + 1) .g2 < M.confirmation_time S.E s := by
    by_contra hcon
    have hle : M.confirmation_time S.E s
        < slotStart S.E.Δ ((M.opening_slot S.hc (q + 1))) := by
      have hdom := facts.gr.gammaNeg1_eq_domain_g2_succ S q
      have hcon' := not_lt.mp hcon
      linarith
    have hsl := slotOf_lt_of_lt_slotStart S hτpos hle
    have hro := Restated.round_of_le_of_lt_opening_slot_sr facts S hsl
    rw [hq] at hro
    exact Nat.not_succ_le_self q hro
  have hearly := Restated.early_g2_eq_healA facts S (q + 1)
  have hsucc := Restated.healA_succ facts S q
  have hW12 := twelve_delta_le_wAttest_kit S
  have hrq : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (Restated.Vocabulary.Execution.Setup.a M S q) := Restated.healA_mono facts S (by omega)
  have hdlo' : (Restated.Vocabulary.Execution.Setup.a M S r) - wAttest S ≤ M.domain S.E S.hc (q + 1) .g2 := by
    have h1 : (M.a S.hc S.E.Δ (q + 1)) = (M.a S.hc S.E.Δ q) + wAttest S := hsucc
    have h2 : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (M.a S.hc S.E.Δ q) := hrq
    have h3 : M.early S.E S.hc (q + 1) .g2 - S.E.Δ ≤ M.domain S.E S.hc (q + 1) .g2 :=
      hdlo
    rw [hearly] at h3
    have h4 : 0 ≤ wAttest S := by linarith
    linarith
  have hdk : M.domain S.E S.hc (q + 1) .g2 ≤ (x[k + 1].time : Int) := by
    rw [hk1]; exact le_of_lt hdτ
  have hu : w ∈ Sched.awake (M.domain S.E S.hc (q + 1) .g2) \
      Sched.adv (M.domain S.E S.hc (q + 1) .g2) :=
    Finset.mem_sdiff.2 ⟨mem_awake_of_awakeThroughout Sched hwr hdlo' hdk, hwk _ hdk⟩
  have hgr : ∀ m : Nat, Restated.stepBeforeInstant M x m (M.domain S.E S.hc (q + 1) .g2) →
      M.gradeBool S.E (M.gradeView (M.toHealing (x[m][w].st).st.core))
        (x[m][w].st).st.core.F S.hc.η_SG (q + 1) (M.early S.E S.hc (q + 1) .g2)
        (M.late S.E S.hc (q + 1) .g2) P ⇢ true := by
    intro m hm
    have hmd := Restated.time_of_stepBefore_domain facts S Sched x htd (Nat.succ_pos q) hm
    have hmk : (x[m].time : Int) < (x[k].time : Int) := by linarith
    have hwm : Restated.HonestThrough M Sched x m w := Restated.honestThrough_of_time_le facts hwk (by linarith)
    obtain ⟨g, hg⟩ := facts.gr.gradeBool_nonempty S.E
      (M.gradeView (M.toHealing (x[m][w].st).st.core)) (x[m][w].st).st.core.F S.hc.η_SG (q + 1)
      (M.early S.E S.hc (q + 1) .g2) (M.late S.E S.hc (q + 1) .g2) P
    suffices hgt : g = true by rw [hgt] at hg; exact hg
    by_cases hq0 : q = r
    · subst hq0
      have hra : (Restated.Vocabulary.Execution.Setup.a M S q) ≤ (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) := Restated.healA_mono facts S (Nat.le_succ q)
      have hb₀r : (Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ ≤ b₀ := by linarith
      have hw : w ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S q)) (x[m].time : Int) :=
        awakeThroughout_sub Sched (by have : 0 ≤ wAttest S := by linarith
                                      linarith) (by linarith) hwr
      exact Restated.graded_base_reader facts S Sched x hexec hsync hcatch hmult htd hmono hrs hP htE hgst
        hb₀r hm hw hwm hmk hFk g hg
    · have hra : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) := Restated.healA_mono facts S (Nat.le_succ r)
      exact Restated.graded_period_of_rounds facts S Sched x hexec hsync hcatch hmult htd hmono hP hfix
        (le_trans hgst hra) hb₀ (ρ := q + 1) (by omega) hρ'₂
        (fun q' h1 h2 => hR q' h1 (Nat.lt_succ_iff.mp (lt_of_lt_of_le h2 hρ'₂))) hm hwA hwm hmk hFk
        g hg
  have hPF : ∀ j : Nat, j ≤ k → Block.compatible P (x[j][w].st).st.core.F = true :=
    fun j hj => compatible_of_cases (Or.inr (preceq_trans_Preceq (Restated.F_mono facts S Sched x w hj) hFk))
  have hst : Block.compatible P (M.toHealing (M.ns_setClock S.E (x[k][w].st).st
      (M.confirmation_time S.E s)).core).toFG.F = true := by
    rw [facts.hd.setClock_toHealing_F]; exact hPF k le_rfl
  have hτρ : (M.round_of S.hc (S.E.slotOf (M.confirmation_time S.E s))) = q + 1 := hq
  obtain ⟨e, he, hPe⟩ := Restated.tickFrame_phase_preceq_of_graded facts S Sched x htd hdpos hdvd hdρ hks
    hτρ hdτ hu hgr hPF _ hst
    (fun m hm => Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew
      hmono hm hdvd hu) c hc
  rw [facts.gr.Sts_phaseResult_g2] at he
  have hfg : Block.Compatible P (M.get_fg_root (M.toHealing (M.ns_setClock S.E
      (x[k][w].st).st (M.confirmation_time S.E s)).core).toFG) := by
    rcases facts.fc.get_fg_root_eq_J_or_F (M.ns_setClock S.E (x[k][w].st).st
        (M.confirmation_time S.E s)).core with h | h
    · rw [h, facts.hd.setClock_core_J]; exact hJk
    · rw [h, facts.hd.setClock_core_F]; exact compatible_iff_Compatible.mpr (hPF k le_rfl)
  exact Restated.stableRoot_compatible_of_frame facts c S.E S.hc _ (q + 1) he hPe hfg hG

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Let `n₁` be the tick step at `S.a (r + 1)` and `w` a validator honest through `n₁ + 1` and awake
    at every time from `S.a r − wAttest S` to `S.a (r + 1)`. Under the hand-over facts for `P` at
    round `r` and the premises of the period, `P` is an ancestor of `w`'s finalized block or of its
    stable record after `n₁ + 1` steps. -/
theorem reader_base (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {b₀ b₁ : Int} (hsync : Restated.SynchronyFromWakeOutside M S x b₀ b₁)
    (hcatch : Restated.CatchUpOnWakeOutside M S x b₀ b₁) (hmult : AwakeAtMultiples S Sched)
    (htd : Restated.TimeDiverges M x) (hmono : Sched.MonotoneCorruption) {tE : Int}
    (hrs : Restated.roundSleepinessW M S Sched tE) {r : Nat} {P : Block V}
    (hP : Restated.StableHandover M S Sched x r P)
    (hlt : Restated.longTermConditionUpToW M S Sched r ((Restated.Vocabulary.Execution.Setup.a M S (r + S.hc.η_SG + 1))))
    (htE : tE ≤ M.opening S.E S.hc (r + 1)) (hgst : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S r))
    (hb₀ : (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ ≤ b₀)
    {n₁ : Nat} (hn₁ : Restated.tickStepAt M x n₁ ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)))) {w : V}
    (hwr : w ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S r) - wAttest S) ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (hwn : Restated.HonestThrough M Sched x (n₁ + 1) w) :
    Block.Preceq P (x[n₁ + 1][w].st).st.core.F ∨
      Block.Preceq P (x[n₁ + 1][w].st).st.core.latest_stable := by
  by_cases hPF : Block.Preceq P (x[n₁ + 1][w].st).st.core.F
  · exact Or.inl hPF
  right
  have hd := S.E.Δ_pos
  obtain ⟨hFc, hJc⟩ := hP.roots n₁ hn₁ w hwn
  have hFP : Block.Preceq (x[n₁ + 1][w].st).st.core.F P :=
    (compatible_cases (compatible_iff_Compatible.mp hFc)).resolve_left hPF
  obtain ⟨hFeq, hJeq, -, hHeq, hTeq, hBeq⟩ := Restated.tick_tree_fields_at_action facts S Sched x hn₁ w
  obtain ⟨hn1, hn0⟩ := Restated.tickStepAt_time facts x hn₁
  have hcto := Restated.confirmation_time_opening_slot facts S (r + 1)
  have hn₁c : Restated.tickStepAt M x n₁ (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1)))) := by
    rw [hcto]; exact hn₁
  have hW12 := twelve_delta_le_wAttest_kit S
  have haw : w ∈ Sched.awake (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1)))) \
      Sched.adv (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1)))) := by
    rw [hcto]
    have hsucc := Restated.healA_succ facts S r
    exact Finset.mem_sdiff.2 ⟨mem_awake_of_awakeThroughout Sched hwr (by
      show (M.a S.hc S.E.Δ r) - wAttest S ≤ (M.a S.hc S.E.Δ (r + 1)); linarith) le_rfl,
      hwn _ (le_of_eq hn1.symm)⟩
  have hneTick := Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew
    hmono hn₁c (by rw [hcto]; exact Restated.action_emod_delta facts S (r + 1)) haw
  have hrun : M.awake_for_grade2 (Setup.alwaysAwake S) w
      (Record.wakeStage M Sched (M.confirmation_time S.E (M.opening_slot S.hc (r + 1))) x[n₁] w)
      (M.round_of S.hc (M.opening_slot S.hc (r + 1) + 1)) := by
    have hround1 : M.round_of S.hc (M.opening_slot S.hc (r + 1) + 1) = r + 1 :=
      facts.gr.round_of_opening_slot_add S.hc (r + 1) (by have := S.hc.R_ge_three; omega)
    obtain ⟨τ, hlbl, hτ⟩ := id hn₁
    rw [hround1, hcto]
    have hle : (M.a S.hc S.E.Δ r) - wAttest S ≤ M.early S.E S.hc (r + 1) .g2 - S.E.Δ := by
      have h1 := Restated.early_g2_eq_healA facts S (r + 1)
      have h2 : M.a S.hc S.E.Δ (r + 1) = M.a S.hc S.E.Δ r + wAttest S := Restated.healA_succ facts S r
      rw [h1]; linarith
    exact Restated.run_fact_g2 facts S Sched x n₁ τ (r + 1) w hlbl hτ
      (awakeThroughout_sub Sched hle le_rfl hwr)
      (fun t' ht' => hwn t' (by rw [hn1, ← hτ]; exact ht'))
  refine Restated.stable_record_step_at_confirmation_tick facts S Sched x hn₁c haw
    (fun c hc G hG => Or.inl ?_) hneTick hrun
  have hround : (M.round_of S.hc) (M.ns_setClock S.E (x[n₁][w].st).st
      (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1))))).core.s = r + 1 := by
    rw [facts.hd.Sts_setClock_core_s, hcto]
    exact Restated.round_of_slotOf_action facts S (r + 1)
  rw [hround] at hG
  obtain ⟨hdpos, hdvd, hdρ, hdlo, hdhi⟩ := Restated.domain_facts_att facts S r .g2
  have hearly := Restated.early_g2_eq_healA facts S (r + 1)
  have hsucc := Restated.healA_succ facts S r
  have hdlo' : (Restated.Vocabulary.Execution.Setup.a M S r) - wAttest S ≤ M.domain S.E S.hc (r + 1) .g2 := by
    have h1 : (M.a S.hc S.E.Δ (r + 1)) = (M.a S.hc S.E.Δ r) + wAttest S := hsucc
    have h3 : M.early S.E S.hc (r + 1) .g2 - S.E.Δ ≤ M.domain S.E S.hc (r + 1) .g2 :=
      hdlo
    rw [hearly] at h3
    show (M.a S.hc S.E.Δ r) - wAttest S ≤ _
    linarith
  have hu : w ∈ Sched.awake (M.domain S.E S.hc (r + 1) .g2) \
      Sched.adv (M.domain S.E S.hc (r + 1) .g2) :=
    Finset.mem_sdiff.2 ⟨mem_awake_of_awakeThroughout Sched hwr hdlo' (le_of_lt hdhi),
      hwn _ (by rw [hn1]; exact le_of_lt hdhi)⟩
  have hFn : Block.Preceq (x[n₁][w].st).st.core.F P := by rw [← hFeq]; exact hFP
  have hgr : ∀ m : Nat, Restated.stepBeforeInstant M x m (M.domain S.E S.hc (r + 1) .g2) →
      M.gradeBool S.E (M.gradeView (M.toHealing (x[m][w].st).st.core))
        (x[m][w].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) .g2)
        (M.late S.E S.hc (r + 1) .g2) P ⇢ true := by
    intro m hm
    have hmd := Restated.time_of_stepBefore_domain facts S Sched x htd (Nat.succ_pos r) hm
    have hmk : (x[m].time : Int) < (x[n₁].time : Int) := by linarith
    have hwm : Restated.HonestThrough M Sched x m w := Restated.honestThrough_of_time_le facts hwn (by linarith)
    have hw : w ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S r)) (x[m].time : Int) :=
      awakeThroughout_sub Sched (by linarith) (by linarith) hwr
    obtain ⟨g, hg⟩ := facts.gr.gradeBool_nonempty S.E
      (M.gradeView (M.toHealing (x[m][w].st).st.core)) (x[m][w].st).st.core.F S.hc.η_SG (r + 1)
      (M.early S.E S.hc (r + 1) .g2) (M.late S.E S.hc (r + 1) .g2) P
    have hgt := Restated.graded_base_reader facts S Sched x hexec hsync hcatch hmult htd hmono hrs hP htE
      hgst hb₀ hm hw hwm hmk hFn g hg
    rw [hgt] at hg
    exact hg
  have hPF' : ∀ j : Nat, j ≤ n₁ → Block.compatible P (x[j][w].st).st.core.F = true :=
    fun j hj => compatible_of_cases (Or.inr (preceq_trans_Preceq (Restated.F_mono facts S Sched x w hj) hFn))
  have hst : Block.compatible P (M.toHealing (M.ns_setClock S.E (x[n₁][w].st).st
      (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1))))).core).toFG.F = true := by
    rw [facts.hd.setClock_toHealing_F]; exact hPF' n₁ le_rfl
  have hτρ : (M.round_of S.hc) (S.E.slotOf
      (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1))))) = r + 1 := by
    rw [hcto]; exact Restated.round_of_slotOf_action facts S (r + 1)
  have hdτ : M.domain S.E S.hc (r + 1) .g2
      < M.confirmation_time S.E ((M.opening_slot S.hc (r + 1))) := by
    rw [hcto]; exact hdhi
  obtain ⟨e, he, hPee⟩ := Restated.tickFrame_phase_preceq_of_graded facts S Sched x htd hdpos hdvd hdρ hn₁c
    hτρ hdτ hu hgr hPF' _ hst
    (fun m hm => Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew
      hmono hm hdvd hu) c hc
  rw [facts.gr.Sts_phaseResult_g2] at he
  obtain ⟨m₂, hm₂⟩ := Restated.exists_tickStepAt facts x htd hdpos
  have hm₂B := Restated.stepBeforeInstant_of_tickStepAt facts x hm₂
  obtain ⟨H, hH, hPH⟩ :=
    facts.gr.Sts_exists_mem_T_preceq_of_gradeBool _ _ _ _ _ _ _ _ true (hgr m₂ hm₂B) rfl
  have hPT₂ : P ∈ (x[m₂][w].st).st.core.T := Restated.mem_T_of_preceq_sts facts S Sched x m₂ w
    (by rw [← facts.gr.Sts_gradeView_T]; exact hH) hPH
  obtain ⟨Pn, hPn, hPe⟩ := Restated.exists_named_of_mem_tree facts S Sched x m₂ w hPT₂
  have hm₂n : m₂ ≤ n₁ + 1 := by
    have hmd := Restated.time_of_stepBefore_domain facts S Sched x htd (Nat.succ_pos r) hm₂B
    exact le_of_lt (Restated.lt_of_time_lt facts S Sched x (by rw [hn1]; linarith))
  have hPnn : Pn ∈ (x[n₁ + 1][w].st).st.bodies :=
    of_decide_eq_true (Restated.processed_mono facts S Sched x w (NamedObject.block Pn) hm₂n
      (decide_eq_true hPn))
  have hvc₀ := Restated.votesClassified_of_handover facts S Sched x r P hP hn₁
  have hlt₀ : Restated.longTermConditionUpToW M S Sched r (x[n₁ + 1].time : Int) := by
    refine Restated.longTermConditionUpToW_mono facts S Sched r hmono ?_ hlt
    rw [hn1]; exact Restated.healA_mono facts S (by omega)
  obtain ⟨W, hW, hPW, hh⟩ :=
    Restated.viable_witness_of_classified facts S Sched x hexec hmono hvc₀ hlt₀ le_rfl hwn hPnn hPe
  have hPT : P ∈ (x[n₁][w].st).st.core.T := by
    rw [← hTeq, Restated.bodies_image_eq_T facts S Sched x (n₁ + 1) w, ← hPe]
    exact Finset.mem_image_of_mem _ hPnn
  have hWT : W ∈ (x[n₁][w].st).st.core.T := by rw [← hTeq]; exact hW
  have hσ : (x[n₁][w].st).st.core.σ W = (x[n₁ + 1][w].st).st.core.σ W := by
    obtain ⟨D, hD, hDe⟩ := Restated.exists_named_of_mem_tree facts S Sched x (n₁ + 1) w hW
    have hD₀ : D ∈ (x[n₁][w].st).st.bodies := by rw [← hBeq]; exact hD
    rw [← hDe, (Restated.nodeInvariant_sts facts S Sched x n₁ w).1.1.1.2.2.2.2 D hD₀,
      (Restated.nodeInvariant_sts facts S Sched x (n₁ + 1) w).1.1.1.2.2.2.2 D hD]
  have hh₀ : (x[n₁][w].st).st.core.h_max - 1 ≤ ((x[n₁][w].st).st.core.σ W).h := by
    rw [hσ, ← hHeq]; exact hh
  have hFP₀ : Block.Preceq (x[n₁][w].st).st.core.F P := hFn
  have hPtree : P ∈ M.get_filtered_block_tree
        (M.toHealing (M.ns_setClock S.E (x[n₁][w].st).st
          (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1))))).core).toFG ∨
      Block.Preceq P (M.get_fg_root
        (M.toHealing (M.ns_setClock S.E (x[n₁][w].st).st
          (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1))))).core).toFG) := by
    have hJ₀ : Block.Compatible P (x[n₁][w].st).st.core.J := by rw [← hJeq]; exact hJc
    rcases facts.fc.get_fg_root_eq_J_or_F (M.ns_setClock S.E (x[n₁][w].st).st
        (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1))))).core with hr | hr
    · rcases compatible_cases (compatible_iff_Compatible.mp hJ₀) with hPJ | hJP
      · right; rw [hr, facts.hd.setClock_core_J]; exact hPJ
      · left
        refine mem_filtered_of_parts_pi facts _ ?_ ?_ ?_ hPW ?_ (by rw [hr, facts.hd.setClock_core_J]; exact hJP)
        · rw [facts.hd.Sts_setClock_core_T]; exact hPT
        · rw [facts.hd.setClock_core_F]; exact hFP₀
        · rw [facts.hd.Sts_setClock_core_T]; exact hWT
        · rw [facts.hd.setClock_core_h_max, facts.hd.Sts_setClock_core_σ]; exact hh₀
    · left
      refine mem_filtered_of_parts_pi facts _ ?_ ?_ ?_ hPW ?_ (by rw [hr, facts.hd.setClock_core_F]; exact hFn)
      · rw [facts.hd.Sts_setClock_core_T]; exact hPT
      · rw [facts.hd.setClock_core_F]; exact hFP₀
      · rw [facts.hd.Sts_setClock_core_T]; exact hWT
      · rw [facts.hd.setClock_core_h_max, facts.hd.Sts_setClock_core_σ]; exact hh₀
  exact Restated.stableRoot_preceq_of_frame facts c S.E S.hc _ (r + 1) he hPee hPtree hG

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Let `n₁` be the tick step at `S.a (r + 1)`, and `w` honest through a step `j` whose time is at
    or after `S.a (r + 1) + Δ` and before `S.a (r + η_SG + 1)`, awake at every time from
    `S.a r − wAttest S` to `x[j].time`. Under the premises of the period and `RoundAttestsAbove` at
    every round of `[r + 2, r + η_SG]`, at every step `k` from `n₁ + 1` to `j`, `P` is an ancestor
    of `w`'s finalized block or of its stable record. -/
theorem reader_preceq_invariant (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {b₀ b₁ : Int} (hsync : Restated.SynchronyFromWakeOutside M S x b₀ b₁)
    (hcatch : Restated.CatchUpOnWakeOutside M S x b₀ b₁) (hmult : AwakeAtMultiples S Sched)
    (hwakes : Restated.WakesAtActionInstants M S Sched) (hsleeps : Restated.SleepsAfterActionInstants M S Sched)
    (htd : Restated.TimeDiverges M x) (hmono : Sched.MonotoneCorruption) {tE : Int}
    (hrs : Restated.roundSleepinessW M S Sched tE) {r : Nat} {P : Block V}
    (hP : Restated.StableHandover M S Sched x r P) (hfix : Restated.fixedRoundSleepinessCountedW M S Sched r)
    (hlt : Restated.longTermConditionUpToW M S Sched r ((Restated.Vocabulary.Execution.Setup.a M S (r + S.hc.η_SG + 1))))
    (htE : tE ≤ M.opening S.E S.hc (r + 1)) (hgst : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S r))
    (hb₀ : (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) + S.E.Δ ≤ b₀)
    (hR : ∀ q : Nat, r + 2 ≤ q → q ≤ r + S.hc.η_SG → Restated.RoundAttestsAbove M S Sched x r P q)
    {n₁ : Nat} (hn₁ : Restated.tickStepAt M x n₁ ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)))) {w : V} {j : Nat}
    (hwj : Restated.HonestThrough M Sched x j w)
    (hwr : w ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S r) - wAttest S) (x[j].time : Int))
    (hjA : (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) + S.E.Δ ≤ (x[j].time : Int))
    (hjt : (x[j].time : Int) < (Restated.Vocabulary.Execution.Setup.a M S (r + S.hc.η_SG + 1))) :
    ∀ k : Nat, n₁ + 1 ≤ k → k ≤ j →
      Block.Preceq P (x[k][w].st).st.core.F ∨
        Block.Preceq P (x[k][w].st).st.core.latest_stable := by
  have hd := S.E.Δ_pos
  obtain ⟨hn1, hn0⟩ := Restated.tickStepAt_time facts x hn₁
  have hra : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) := Restated.healA_mono facts S (Nat.le_succ r)
  have hb₀r : (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ ≤ b₀ := by linarith
  have hwA : w ∈ Restated.activeRoundWThroughNext M S Sched r :=
    Restated.mem_activeRoundWThroughNext_of_reader facts S Sched hwr hjA
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
      intro hj
      exact Restated.reader_base facts S Sched x hexec hsync hcatch hmult htd hmono hrs hP hlt htE hgst hb₀r
        hn₁ (awakeThroughout_sub Sched le_rfl (by linarith) hwr)
        (Restated.honestThrough_of_time_le facts hwj (Restated.time_mono_int facts S Sched x hj))
  | succ k hk ih =>
      intro hkj
      have hkj' : k ≤ j := Nat.le_of_succ_le hkj
      rcases ih hkj' with hF | hrec
      · exact Or.inl (preceq_trans_Preceq hF (Restated.F_mono facts S Sched x w (Nat.le_succ k)))
      · by_cases hPF : Block.Preceq P (x[k][w].st).st.core.F
        · exact Or.inl (preceq_trans_Preceq hPF (Restated.F_mono facts S Sched x w (Nat.le_succ k)))
        · right
          have hkt1 : (x[k + 1].time : Int) ≤ (x[j].time : Int) := Restated.time_mono_int facts S Sched x hkj
          have hkt0 : (x[k].time : Int) ≤ (x[k + 1].time : Int) :=
            Restated.time_mono_int facts S Sched x (Nat.le_succ k)
          have hkt : (x[k].time : Int) < (Restated.Vocabulary.Execution.Setup.a M S (r + S.hc.η_SG + 1)) := by linarith
          have hvc := Restated.votesClassified_of_rounds facts S Sched x hexec hwakes hsleeps hP hn₁ hk hkt
            (fun q hq hSq => hR q hq (by
              by_contra hcon
              have h1 : r + S.hc.η_SG + 1 ≤ q := Nat.succ_le_of_lt (Nat.lt_of_not_le hcon)
              have h2 : (Restated.Vocabulary.Execution.Setup.a M S (r + S.hc.η_SG + 1)) ≤ (Restated.Vocabulary.Execution.Setup.a M S q) := Restated.healA_mono facts S h1
              linarith))
          have hltk := Restated.longTermConditionUpToW_mono facts S Sched r hmono (le_of_lt hkt) hlt
          have hwk : Restated.HonestThrough M Sched x k w := Restated.honestThrough_of_time_le facts hwj (by linarith)
          obtain ⟨hFc, hJc⟩ := Restated.honest_roots_of_classified facts S Sched x hexec hmono hvc hltk hk hwk
          have hFP : Block.Preceq (x[k][w].st).st.core.F P :=
            (compatible_cases (compatible_iff_Compatible.mp hFc)).resolve_left hPF
          refine Restated.preceq_latest_stable_succ facts S Sched x w k hrec
            (fun s hks _ c hc G hG => ?_) (facts.ndRun.tick_outcome_sts S Sched x hexec.idealization.root_injective hexec.honestRootsNew)
          obtain ⟨hk1, hk0⟩ := Restated.tickStepAt_time facts x hks
          have hnk : (x[n₁ + 1].time : Int) ≤ (x[k].time : Int) := Restated.time_mono_int facts S Sched x hk
          exact Restated.stableRoot_compatible_at_tick facts S Sched x hexec hsync hcatch hmult htd hmono hrs
            hP hfix htE hgst hb₀ hR hwA hks
            (awakeThroughout_sub Sched le_rfl hkt1 hwr)
            (Restated.honestThrough_of_time_le facts hwj hkt1) (by linarith) (by linarith) hFP hJc
            c hc G hG

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- In an execution whose synchrony and catch-up on wake hold outside `[b₀, b₁)`, with round-level
    sleepiness from a time at or before round `r`'s opening, GST at or before `S.a r`, the period
    starting after round `r + 1`'s attestations are delivered, the participation premise over the
    validators awake through rounds `r` and `r + 1`, the long-term condition at
    `S.a (r + η_SG + 1)`, and the hand-over facts for `P` at round `r`: every validator `w` honest
    through a step `j` whose time is at or after `b₀` and before `S.a (r + η_SG + 1)`, and awake at
    every time from `S.a r − wAttest S` to that step's time, has `P` as its stable output after `j`
    steps or as an ancestor of it. -/
theorem stablePersists_throughPeriod_ofHandover (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (tE b₀ b₁ : Int) (r : Nat) (P : Block V)
    (hmono : Sched.MonotoneCorruption)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWakeOutside M S x b₀ b₁)
    (hmult : AwakeAtMultiples S Sched)
    (hwakes : Restated.WakesAtActionInstants M S Sched) (hsleeps : Restated.SleepsAfterActionInstants M S Sched)
    (hcatch : Restated.CatchUpOnWakeOutside M S x b₀ b₁)
    (htd : Restated.TimeDiverges M x)
    (hrs : Restated.roundSleepinessW M S Sched tE) (htE : tE ≤ M.opening S.E S.hc r)
    (hgst : S.E.t_GST ≤ (M.a S.hc S.E.Δ r))
    (hb₀ : Restated.periodAfterRound M S r b₀)
    (hfix : Restated.fixedRoundSleepinessCountedW M S Sched r)
    (hlt : Restated.longTermConditionUpToW M S Sched r ((M.a S.hc S.E.Δ (r + S.hc.η_SG + 1))))
    (hP : Restated.StableHandover M S Sched x r P) :
    ∀ (w : V) (j : Nat), Restated.HonestThrough M Sched x j w →
      b₀ ≤ (x[j].time : Int) →
      (x[j].time : Int) < (M.a S.hc S.E.Δ (r + S.hc.η_SG + 1)) →
      w ∈ Sched.awakeThroughout ((M.a S.hc S.E.Δ r) - wAttest S) (x[j].time : Int) →
      Block.Preceq P (M.get_stable (x[j][w].st).st.core) := by
  intro w j hwj hjb hjt hwr
  have hd := S.E.Δ_pos
  have hb₀' : (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) + S.E.Δ ≤ b₀ := hb₀
  have hjA : (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) + S.E.Δ ≤ (x[j].time : Int) := le_trans hb₀' hjb
  have htE' : tE ≤ M.opening S.E S.hc (r + 1) :=
    le_trans htE (facts.gr.Sts_opening_mono S (Nat.le_succ r))
  have hgst' : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) := le_trans hgst (Restated.healA_mono facts S (Nat.le_succ r))
  have hR := Restated.roundAttestsAbove_all facts S Sched x hexec hsync hcatch hmult hwakes hsleeps htd hmono
    hP hfix hlt hgst' hb₀'
  obtain ⟨n₁, hn₁⟩ := Restated.exists_tickStepAt facts x htd (Restated.action_pos facts S (r + 1))
  obtain ⟨hn1, hn0⟩ := Restated.tickStepAt_time facts x hn₁
  have hjn : n₁ + 1 ≤ j := Restated.lt_of_time_lt facts S Sched x (by linarith)
  rcases Restated.reader_preceq_invariant facts S Sched x hexec hsync hcatch hmult hwakes hsleeps htd hmono
      hrs hP hfix hlt htE' hgst hb₀' hR hn₁ hwj hwr hjA hjt j hjn le_rfl with hF | hrec
  · exact preceq_trans_Preceq hF (facts.hd.finalized_preceq_get_stable _)
  · have hvc := Restated.votesClassified_of_rounds facts S Sched x hexec hwakes hsleeps hP hn₁ hjn hjt
      (fun q hq hSq => hR q hq (by
        by_contra hcon
        have h1 : r + S.hc.η_SG + 1 ≤ q := Nat.succ_le_of_lt (Nat.lt_of_not_le hcon)
        have h2 : (Restated.Vocabulary.Execution.Setup.a M S (r + S.hc.η_SG + 1)) ≤ (Restated.Vocabulary.Execution.Setup.a M S q) := Restated.healA_mono facts S h1
        linarith))
    have hltj := Restated.longTermConditionUpToW_mono facts S Sched r hmono (le_of_lt hjt) hlt
    obtain ⟨hFc, -⟩ := Restated.honest_roots_of_classified facts S Sched x hexec hmono hvc hltj hjn hwj
    exact facts.hd.preceq_get_stable_of_record _ hrec hFc

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- `stablePersists_throughPeriod_ofHandover` at the hand-over round `r + 1`, with the long-term
    condition replaced by `outsideAttestersUnderThird S Sched (r + 1)`, the adversary under a third
    at every time up to `tSafe`, and `S.a (r + η_SG + 2) ≤ tSafe`: every validator honest through a
    step `j` whose time is at or after `b₀` and before `S.a (r + η_SG + 2)`, awake at every time
    from `S.a (r + 1) − wAttest S` to that time, has `P` as its stable output after `j` steps or as
    an ancestor of it. -/
theorem stablePersists_throughPeriod_atPage (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (tE b₀ b₁ tSafe : Int) (r : Nat) (P : Block V)
    (hmono : Sched.MonotoneCorruption)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWakeOutside M S x b₀ b₁)
    (hmult : AwakeAtMultiples S Sched)
    (hwakes : Restated.WakesAtActionInstants M S Sched) (hsleeps : Restated.SleepsAfterActionInstants M S Sched)
    (hcatch : Restated.CatchUpOnWakeOutside M S x b₀ b₁)
    (htd : Restated.TimeDiverges M x)
    (hrs : Restated.roundSleepinessW M S Sched tE) (htE : tE ≤ M.opening S.E S.hc (r + 1))
    (hgst : S.E.t_GST ≤ (M.a S.hc S.E.Δ (r + 1)))
    (hb₀ : Restated.periodAfterRound M S (r + 1) b₀)
    (hfix : Restated.fixedRoundSleepinessCountedW M S Sched (r + 1))
    (hout : Restated.outsideAttestersUnderThird M S Sched (r + 1))
    (hadv : ∀ t : Int, t ≤ tSafe →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hsafe : (M.a S.hc S.E.Δ (r + S.hc.η_SG + 2)) ≤ tSafe)
    (hP : Restated.StableHandover M S Sched x (r + 1) P) :
    ∀ (w : V) (j : Nat), Restated.HonestThrough M Sched x j w →
      b₀ ≤ (x[j].time : Int) →
      (x[j].time : Int) < (M.a S.hc S.E.Δ (r + S.hc.η_SG + 2)) →
      w ∈ Sched.awakeThroughout ((M.a S.hc S.E.Δ (r + 1)) - wAttest S) (x[j].time : Int) →
      Block.Preceq P (M.get_stable (x[j][w].st).st.core) := by
  have heq : r + 1 + S.hc.η_SG + 1 = r + S.hc.η_SG + 2 := by
    rw [Nat.add_right_comm r 1 S.hc.η_SG]
  have hlt : Restated.longTermConditionUpToW M S Sched (r + 1) ((M.a S.hc S.E.Δ (r + 1 + S.hc.η_SG + 1))) :=
    Restated.longTermConditionUpToW_of_thirds facts S Sched (r + 1) tSafe _ (by rw [heq]; exact hsafe) hadv hout
  intro w j hwj hjb hjt hwr
  exact Restated.stablePersists_throughPeriod_ofHandover facts S Sched x tE b₀ b₁ (r + 1) P hmono hexec hsync
    hmult hwakes hsleeps hcatch htd hrs htE hgst hb₀ hfix hlt hP w j hwj hjb
    (by rw [heq]; exact hjt) hwr

end

end DecoupledConsensusModel.Sts.Restated
