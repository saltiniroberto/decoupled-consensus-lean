import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bStepAnchor
import Proofs.Claims.Restated.Claim13bStepFin
import Proofs.Claims.Restated.Claim13bStepGrade
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bStepKitTick
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bStepKitTick
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# Quorums and honest signers

Every quorum has a member the adversary does not hold, and the consequences for honest signers of
quorums and for the height targets behind a finalized block, under `roundSleepinessW`, stated over a
model `M : Record.Model V`.
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

/-- Under `roundSleepinessW`, at any round `r₀ ≥ 1` whose opening is at or after `anchor`, every set
    of validators whose weight reaches the finality threshold has a member that the adversary does
    not hold at the opening of round `r₀ + 1`. -/
theorem exists_nonAdv_of_quorum (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) {anchor : Int}
    (hrsW : Restated.roundSleepinessW M S Sched anchor) {r₀ : Nat} (hr₀ : 1 ≤ r₀)
    (hanchor : anchor ≤ M.opening S.E S.hc r₀)
    {A : Finset V} (hq : S.E.q ≤ S.E.electorate.weightOf A) :
    ∃ v ∈ A, v ∉ Sched.adv (M.opening S.E S.hc (r₀ + 1)) := by
  classical
  by_contra hex
  have hsub : A ⊆ Sched.adv (M.opening S.E S.hc (r₀ + 1)) := by
    intro v hv
    by_contra hadv
    exact hex ⟨v, hv, hadv⟩
  have hrs' := hrsW r₀ hr₀ hanchor
  have hleft := S.E.electorate.weightOf_mono
    (Finset.subset_union_left (s₁ := Sched.adv (M.opening S.E S.hc (r₀ + 1)))
      (s₂ := Restated.attestersIn M S Sched (r₀ - S.hc.η_SG) (r₀ - 1) \
        (Restated.activeRoundW M S Sched (r₀ - 1) \ Sched.adv (M.opening S.E S.hc (r₀ + 1)))))
  have hfresh : Restated.activeRoundW M S Sched (r₀ - 1) \ Sched.adv (M.opening S.E S.hc (r₀ + 1))
      ⊆ Finset.univ \ Sched.adv (M.opening S.E S.hc (r₀ + 1)) := by
    intro v hv
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, (Finset.mem_sdiff.mp hv).2⟩
  have hright := S.E.electorate.weightOf_mono hfresh
  have hcompl := S.E.electorate.weightOf_add_weightOf_sdiff
    (Sched.adv (M.opening S.E S.hc (r₀ + 1)))
  have hA := S.E.electorate.weightOf_mono hsub
  have hqW : 2 * S.E.electorate.totalWeight ≤ 3 * S.E.q :=
    two_mul_totalWeight_le_three_mul_q S.E
  omega

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Under `roundSleepinessW`, from the anchor on, every quorum `Q` has a member honest through the
    step `n' + 1` of the round-`(r + 1)` tick. -/
theorem exists_honest_quorum_signer_ofRoundSleepinessW (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {tE : Int}
    (hmono : Sched.MonotoneCorruption)
    (hrsW : Restated.roundSleepinessW M S Sched tE)
    {r : Round} {n' : Nat} (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (htE : tE ≤ M.opening S.E S.hc r)
    {Q : Finset V} (hQ : S.E.electorate.IsQuorum Q) :
    ∃ signer ∈ Q, Restated.HonestThrough M Sched x (n' + 1) signer := by
  have htime : (x[n' + 1].time : Int) = (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) := (Restated.tickStepAt_time facts x hn').1
  have hopen : (x[n' + 1].time : Int) ≤ M.opening S.E S.hc (r + 1 + 1) := by
    rw [htime]
    -- One delay after round `r + 1`'s action instant is at or before round `r + 2`'s opening.
    have h1 := facts.gr.action_delta_le_early S S.hc.R_ge_three (Nat.lt_succ_self (r + 1))
    have h2 := facts.gr.early_g2_le_opening S (r + 1 + 1)
    have hd := S.E.Δ_pos
    show M.a S.hc S.E.Δ _ ≤ _
    linarith
  obtain ⟨signer, hsigner, hadv⟩ :=
    Restated.exists_nonAdv_of_quorum facts S Sched hrsW (r₀ := r + 1) (Nat.le_add_left 1 r)
      (le_trans htE (facts.gr.Sts_opening_mono S (Nat.le_succ r))) ((isQuorum_iff_q_le S.E Q).mp hQ)
  refine ⟨signer, hsigner, ?_⟩
  intro t ht hmem
  exact hadv (hmono t (M.opening S.E S.hc (r + 1 + 1)) (le_trans ht hopen) hmem)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- From any node state `before`, validator `v`'s round-`r` action read can compute some
    attestation. -/
private theorem actionAttestationFrom_nonempty_quorum (facts : Record.Facts M) (S : Setup V)
    (before : M.N) (v : V) (r : Round) :
    ∃ a, a ∈ Restated.actionAttestationFrom M S before v r := by
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc before.st.core.toHealing
    (Restated.Vocabulary.Execution.Setup.a M S r) before.cache
  obtain ⟨st, hst⟩ := facts.dt.duties_update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc
    (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r))
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
  obtain ⟨D, hD⟩ := facts.dt.attest_with_nonempty (M.gradeContract (M.mkNode st before.record c).cache)
    S.E S.hc (S.node v) (M.mkNode st before.record c).st (M.mkNode st before.record c).record
  exact ⟨D.2.2, M.mkNode st before.record c, ⟨c, hc, st, hst, rfl⟩, D.1, D.2.1, hD⟩

/-- Under `roundSleepinessW`, either a validator's store has finalized nothing but genesis, or its
    store holds a block `X` its finalized block descends from, and some validator `q`, honest
    through the successor of its send step and not held by the adversary up to the opening of round
    `r₀ + 1`, signed at its round's action tick an attestation whose height pair is a vote naming
    `X` at the height the store records for its finalized block. -/
theorem finalized_honest_target_ofRoundSleepinessW (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) {tE : Int}
    (hrsW : Restated.roundSleepinessW M S Sched tE)
    {r₀ : Round} (hr₀ : 1 ≤ r₀) (htE : tE ≤ M.opening S.E S.hc r₀)
    {i : Nat} {v : V} (hv : Restated.HonestThrough M Sched x i v)
    (hi : (x[i].time : Int) ≤ M.opening S.E S.hc (r₀ + 1)) :
    (x[i][v].st).st.core.F = Block.genesis ∨
      ∃ (X : NamedBlock V) (q : V) (a : NamedAttestation V) (k : Nat) (tmo : Bool),
        X ∈ (x[i][v].st).st.bodies ∧
        Block.Preceq (x[i][v].st).st.core.F X.erase ∧
        k < i ∧ Restated.tickStepAt M x k ((Restated.Vocabulary.Execution.Setup.a M S a.round)) ∧ q ∈ Sched.awake ((Restated.Vocabulary.Execution.Setup.a M S a.round)) ∧
        Restated.HonestThrough M Sched x (k + 1) q ∧
        HonestThroughTime Sched (M.opening S.E S.hc (r₀ + 1)) q ∧
        (∀ a' ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[k][q].st) q a.round,
          a = a') ∧
        (⟨q, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[k + 1].sent ∧
        a.height_pair = NamedHeightPair.vote
          ((x[i][v].st).st.core.σ (x[i][v].st).st.core.F).h X.root tmo := by
  classical
  rcases Restated.finalized_target_witness facts S Sched x hexec hv with hgen | ⟨X, hXmem, hFX, Q, hQ, hsign⟩
  · exact Or.inl hgen
  · right
    obtain ⟨q, hqQ, hqadv⟩ := Restated.exists_nonAdv_of_quorum facts S Sched hrsW hr₀ htE
      ((isQuorum_iff_q_le S.E Q).mp hQ)
    have hqhon : Restated.HonestThrough M Sched x i q := by
      intro t ht hmem
      exact hqadv (hmono t (M.opening S.E S.hc (r₀ + 1)) (le_trans ht hi) hmem)
    obtain ⟨carrier, a, tmo, hcarrier, ha, hval, hpair⟩ := hsign q hqQ
    have hlog : (⟨a.val_index, NamedObject.attest a⟩ : SignedMsg V (NamedObject V))
        ∈ x[i].sent :=
      Restated.carried_vote_in_log facts S Sched x hexec hcarrier ha (by rw [hval]; exact hqhon)
    have hlog' : (⟨q, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[i].sent := by
      rw [← hval]; exact hlog
    have hhonT : HonestThroughTime Sched ((x[i].time : Int)) q := fun t ht => hqhon t ht
    obtain ⟨-, k, hki, htick, hawk, out, hout, hemit⟩ :=
      Restated.attest_round_of_sent facts S Sched x (tB := (x[i].time : Int)) hhonT
        hexec.toUnforgeability hval (le_refl _) hlog'
    have heq : ∀ a' ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[k][q].st) q a.round,
        a = a' := by
      have hA : Restated.actionAttestationFrom M (Setup.alwaysAwake S)
          (Record.wakeStage M Sched ((Restated.Vocabulary.Execution.Setup.a M S a.round)) x[k] q) q
            a.round =
          Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[k][q].st) q a.round := by
        simp only [Restated.actionAttestationFrom,
          Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom, Record.wakeStage_st facts,
          Record.wakeStage_record facts, Record.wakeStage_cache facts]
      rw [← hA]
      have _hr_s1 := Record.reachedNode_wakeStage facts S Sched x (k) q (Restated.Vocabulary.Execution.Setup.a M S a.round)
      have _hv_s2 := Record.runs_as_wakeStage facts S Sched x (k) q (Restated.Vocabulary.Execution.Setup.a M S a.round)
      exact Restated.attest_of_tick_eq facts S q _ a.round hout hemit
    obtain ⟨a₁, ha₁⟩ := actionAttestationFrom_nonempty_quorum facts (Setup.alwaysAwake S)
      (x[k][q].st) q a.round
    have hsent : (⟨q, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[k + 1].sent := by
      rw [heq a₁ ha₁]
      -- the tick emitted `a`, so its node state passed the grade-2 awake test of `a`'s round
      exact Restated.attest_emitted_at_tick_from facts S Sched x htick hawk ⟨out, hout⟩
        (facts.nd.tick_attestation_fields (Setup.alwaysAwake S) q _ _ (Record.runs_as_wakeStage facts S Sched x _ _ _) out hout a hemit).2.1 a₁ ha₁
    have hqk : Restated.HonestThrough M Sched x (k + 1) q := by
      intro t ht hmem
      refine hqadv (hmono t (M.opening S.E S.hc (r₀ + 1)) ?_ hmem)
      exact le_trans ht
        (le_trans (Restated.time_mono_int facts S Sched x (Nat.succ_le_of_lt hki)) hi)
    have hqT : HonestThroughTime Sched (M.opening S.E S.hc (r₀ + 1)) q :=
      fun t ht hmem => hqadv (hmono t (M.opening S.E S.hc (r₀ + 1)) ht hmem)
    exact ⟨X, q, a, k, tmo, hXmem, hFX, hki, htick, (Finset.mem_sdiff.1 hawk).1, hqk, hqT, heq,
      hsent, hpair⟩

end

end DecoupledConsensusModel.Sts.Restated
