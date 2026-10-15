import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bW_Schedule
import Proofs.Claims.Restated.ProcessedFlip
import Proofs.Claims.Restated.Redelivery
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_NamedNode
import Model.Conditions.Claim13bStepKitTick
import Model.Conditions.Claim13bStepSG
import Model.Conditions.Claim13bW_FrameAsleep
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedActionReads
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# Phase caches are written while awake

Every non-empty root of a validator's phase cache was written at a phase-domain instant the
validator was awake at, and the consequences for the height pairs of attestations of validators
asleep at those instants. Stated over a model `M : Record.Model V`.
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

/-- If `FramePhaseAwake` holds for the cache `c`, it holds for `c` clipped to any block `F`. -/
theorem framePhaseAwake_clipCache (facts : Record.Facts M) (S : Setup V) {Sched : Schedule V} {v : V}
    {c : M.Cache} (F : Block V) (h : Restated.FramePhaseAwake M S Sched v c) :
    Restated.FramePhaseAwake M S Sched v (M.clipCache F c) := by
  intro r₁ p root hr
  obtain ⟨root₀, h₀, -⟩ := facts.gr.phaseResult_clipCache hr
  exact h r₁ p root₀ h₀

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If `FramePhaseAwake` holds for a cache and `v` is awake at `t`, it holds for every cache a phase
    tick at `t` can leave, from any store `st`. -/
theorem framePhaseAwake_onPhaseTick (facts : Record.Facts M) (S : Setup V) {Sched : Schedule V} {v : V}
    (st : M.HS) {t : Int} {c : M.Cache}
    (hv : v ∈ Sched.awake t) (h : Restated.FramePhaseAwake M S Sched v c) :
    ∀ c' : M.Cache, M.onPhaseTick S.E S.hc st t c ⇢ c' →
    Restated.FramePhaseAwake M S Sched v c' := by
  intro c' hc' r₁ p root hr
  choose g hg using fun B => facts.gr.gradeBool_nonempty S.E (M.gradeView st) st.toFG.F
    S.hc.η_SG r₁ (M.early S.E S.hc r₁ p) (M.late S.E S.hc r₁ p) B
  rcases facts.gr.phaseResult_onPhaseTick S.E S.hc st t c c' hc' hr g hg with
    ⟨root₀, h₀, -⟩ | ⟨ht, -⟩
  · exact h r₁ p root₀ h₀
  · rw [← ht]; exact hv

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- At every step `k`, every non-empty root `v`'s phase cache holds for a round and a phase was
    written at a phase-domain instant `v` was awake at. -/
theorem framePhaseAwake_sts (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V) (k : Nat) :
    Restated.FramePhaseAwake M S Sched v (x[k][v].st).cache := by
  have _hr_0 : M.reachedNode (x[0][v].st) := Record.reachedNode_sts facts S Sched x 0 v
  induction k with
  | zero =>
      obtain ⟨-, hn, -⟩ := x.init
      have h0 : (x[0][v].st) = M.initial (Setup.alwaysAwake S) v := by
        show ((x.cfg 0)[v]).st = _
        rw [hn v]; rfl
      intro r₁ p root hr
      rw [h0] at hr
      exact absurd hr (facts.nd.initial_cache_phaseResult_ne (Setup.alwaysAwake S) v r₁ p root)
  | succ k ih =>
      have _hr_k : M.reachedNode (x[k][v].st) := Record.reachedNode_sts facts S Sched x k v
      cases hl : x.lbl k with
      | tickAllAwake τ =>
          have _hr_w : M.reachedNode (Record.wakeStage M Sched (τ : Int) x[k] v) :=
            Record.reachedNode_wakeStage facts S Sched x k v τ
          rcases Restated.st_succ_of_tick facts S Sched x v hl with
            ⟨hvτ, -, out₁, hout, hst⟩ | hst
          · obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
              (Record.wakeStage M Sched (τ : Int) x[k] v).st.core.toHealing (τ : Int)
              (Record.wakeStage M Sched (τ : Int) x[k] v).cache
            rw [hst, Restated.Vocabulary.Proofs.NamedNode.tick_cache_eq facts _ _ _ _ out₁ hout c hc]
            rw [Record.wakeStage_st facts, Record.wakeStage_cache facts] at hc
            exact Restated.framePhaseAwake_clipCache facts S _
              (Restated.framePhaseAwake_onPhaseTick facts S _ (Finset.mem_sdiff.1 hvτ).1 ih c hc)
          · rw [hst, Record.wakeStage_cache facts]; exact ih
      | deliver p m =>
          by_cases hp : p = v
          · subst hp
            rcases Restated.st_succ_of_deliver facts S Sched x hl with hst | ⟨-, hst⟩
            · rw [Restated.Vocabulary.Proofs.NamedNode.process_cache_eq facts _ _ _ _ hst]
              exact Restated.framePhaseAwake_clipCache facts S _ ih
            · rw [hst]; exact ih
          · rw [Restated.getElem_succ_of_deliver_ne facts S Sched x hl hp]
            exact ih
      | custom _ ev => exact ev.elim
      | adversarial p m =>
          rw [Restated.getElem_succ_of_adversarial facts S Sched x hl]
          exact ih
      | forward p m =>
          rw [Restated.getElem_succ_of_forward facts S Sched x hl]
          exact ih

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If some round-`r` action frame that `v` can read from its node state after `n` steps offers a
    non-empty root for the phase `p`, then `v` was awake at round `r`'s phase-`p` domain instant. -/
theorem awake_of_actionFrame_phaseResult (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (n : Nat) (v : V) (r : Round) (p : Protocol.Phase)
    (root : Block V) (f : M.Frame) (hf : f ∈ Restated.actionFrame M S (x[n][v].st) r)
    (h : M.phaseResult f p = some (some root)) :
    v ∈ Sched.awake (M.domain S.E S.hc r p) := by
  obtain ⟨m, ⟨c, hc, st0, -, rfl⟩, rfl⟩ := hf
  dsimp only at h
  rw [facts.nd.mkNode_cache] at h
  obtain ⟨root₀, h₀, -⟩ := facts.gr.readFrame_phase_provenance _ _ _ h
  choose g hg using fun B => facts.gr.gradeBool_nonempty S.E
    (M.gradeView (x[n][v].st).st.core.toHealing) (x[n][v].st).st.core.toHealing.toFG.F
    S.hc.η_SG r (M.early S.E S.hc r p) (M.late S.E S.hc r p) B
  rcases facts.gr.phaseResult_onPhaseTick S.E S.hc _ ((Restated.Vocabulary.Execution.Setup.a M S r))
      _ c hc h₀ g hg with ⟨root₁, h₁, -⟩ | ⟨ht, -⟩
  · exact Restated.framePhaseAwake_sts facts S Sched x v n r p root₁ h₁
  · -- every phase-domain instant of round `r` is strictly before its action instant
    have hlt : M.domain S.E S.hc r p < Restated.Vocabulary.Execution.Setup.a M S r := by
      have hd := S.E.Δ_pos
      have h5 := facts.gr.domain_add_five_delta_le_action S r p
      show M.domain S.E S.hc r p < M.a S.hc S.E.Δ r
      linarith
    exact absurd ht (ne_of_gt hlt)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For every node state `n` of the round-`r` action read from `before`, if the round-`r` frame read
    from `n`'s cache and store offers no non-empty grade-2 root, every attestation the attestation
    duty can compute on `n` carries the empty height pair. -/
theorem heightPair_empty_of_actionFrame_g2 (facts : Record.Facts M) (S : Setup V) (before : M.N) (v : V)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
      before r,
    (∀ root : Block V, (M.readFrame n.cache (M.toHealing n.st.core) r).g2 ≠ some (some root)) →
    ∀ D, M.duties_attest_with (M.gradeContract n.cache) S.E S.hc ((Setup.alwaysAwake S).node v)
      n.st n.record ⇢ D →
    D.2.2.height_pair = NamedHeightPair.empty := by
  intro n hn hg2 D hD
  have hR : M.round_of S.hc (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.s = r := by
    obtain ⟨c, -, st0, hst0, rfl⟩ := id hn
    rewrite [facts.sto.toHealing_s, facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [(facts.dt.named_confirmation_clock _ _ _ _ _ st0 hst0).2,
      facts.hd.ModelProperties_setClock_core_s]
    exact Restated.Vocabulary.Proofs.HealingLemmas.round_of_slotOf_a facts S r
  obtain ⟨G, hG⟩ := facts.gr.read_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) r
  have hQ : G.Q2 = none := by
    obtain ⟨o, ho⟩ := facts.gr.grade2Block_nonempty (M.toHealing n.st.core)
      (M.readFrame n.cache (M.toHealing n.st.core) r)
    rw [facts.nd.Sts_gradeContract_read_Q2 n.cache S.E S.hc _ r G hG o ho]
    cases o with
    | none => rfl
    | some Q =>
        obtain ⟨clipped, hclipped, -⟩ := facts.gr.grade2Block_some _ ho rfl
        exact absurd hclipped (hg2 clipped)
  obtain ⟨A, hA⟩ := facts.dt.round_action_with_nonempty (M.gradeContract n.cache) S.E S.hc
    ((Setup.alwaysAwake S).node v) (M.toHealing n.st.core) n.record
  rw [facts.dt.attest_with_row _ _ _ _ _ _ D hD A hA]
  exact facts.dt.round_action_with_height_pair_of_Q2_none _ _ _ _ _ _ G (by rw [hR]; exact hG) hQ A hA

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- A validator asleep at round `r`'s grade-2 domain instant puts the empty height pair in every
    round-`r` attestation it can compute from its node state after any step `n`. -/
theorem emptyHeightPair_of_asleep_at_g2 (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    {r : Round} {n : Nat} {v : V}
    (hasleep : v ∉ Sched.awake (M.domain S.E S.hc r .g2)) :
    ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v].st) v r,
      a.height_pair = NamedHeightPair.empty := by
  intro a ⟨m, hm, ns, rec, hD⟩
  refine Restated.heightPair_empty_of_actionFrame_g2 facts S _ v r m hm ?_ (ns, rec, a) hD
  intro root hroot
  exact hasleep (Restated.awake_of_actionFrame_phaseResult facts S Sched x n v r .g2 root
    _ ⟨m, hm, rfl⟩ (by rw [facts.gr.Sts_phaseResult_g2]; exact hroot))

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Under `WakesAtActionInstants` and `SleepsAfterActionInstants`, a validator awake at round `r`'s
    action instant, one of whose round-`r` attestations computed from its node state after `n` steps
    carries a non-empty height pair, was awake throughout the attester window before that instant. -/
theorem active_of_nonEmpty_heightVote (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hw : Restated.WakesAtActionInstants M S Sched) (hs : Restated.SleepsAfterActionInstants M S Sched)
    {r : Round} {n : Nat} {v : V} {h₀ : Height} {root : BlockId} {tmo : Bool}
    (hv : v ∈ Sched.awake ((Restated.Vocabulary.Execution.Setup.a M S r)))
    (a : NamedAttestation V)
    (ha : a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v].st) v r)
    (hne : a.height_pair = NamedHeightPair.vote h₀ root tmo) :
    v ∈ Restated.activeRoundW M S Sched r := by
  by_cases h1 : v ∈ Sched.awake ((Restated.Vocabulary.Execution.Setup.a M S r) - 1)
  · exact Restated.active_of_awake_prev facts S Sched hw hv h1
  · have hempty := Restated.emptyHeightPair_of_asleep_at_g2 facts S Sched x (n := n)
      (Restated.asleep_at_domain facts S Sched hs h1 .g2) a ha
    rw [hempty] at hne
    cases hne

end

end DecoupledConsensusModel.Sts.Restated
