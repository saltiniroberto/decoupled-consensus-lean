import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bDirection
import Proofs.Claims.Restated.Claim13bStepAnchor
import Proofs.Claims.Restated.Claim13bStepGrade
import Proofs.Claims.Restated.Claim13bStepKitStore
import Proofs.Claims.Restated.Claim13bStepKitTick
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bStepKitTick
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# Height votes and the signer's maximum height

The height a non-empty height vote names is at most the maximum height the signer's store held at
the tick that signed it. Stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

open scoped DC in
/-- `m >>= k` can return `b` exactly when `m` can return some `a` from which `k a` can return `b`. -/
private theorem returns_bind_iff_r11 {α β : Type} (m : DC.NDRE α) (k : α → DC.NDRE β) (b : β) :
    (m >>= k) ⇢ b ↔ ∃ a, m ⇢ a ∧ k a ⇢ b := by
  unfold Record.Returns
  simp only [ExceptT.run_bind, Set.bind_def]
  constructor
  · intro h
    obtain ⟨e, he, hb⟩ := Set.mem_iUnion₂.mp h
    cases e with
    | ok a => exact ⟨a, he, hb⟩
    | error err => simp at hb
  · rintro ⟨a, ha, hb⟩
    exact Set.mem_iUnion₂.mpr ⟨_, ha, hb⟩

section
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If a validator `v` the adversary holds at no time up to step `n'` has an attestation it authored
    in the sent log after `n'` steps whose height pair is a vote for height `h'`, then some step `k`
    before `n'` is the tick at that attestation's round's action instant, and `h'` is at most the
    maximum height `v`'s own store records at that step. -/
theorem heightVote_le_hmax_at_tick (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    {v : V} {n' : Nat} {a : NamedAttestation V} {h' : Height} {entry : BlockId} {tmo : Bool}
    (hv : Restated.HonestThrough M Sched x n' v) (hunf : Restated.Unforgeability M S x) (hidx : a.val_index = v)
    (hsent : (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n'].sent)
    (hpair : a.height_pair = NamedHeightPair.vote h' entry tmo) :
    ∃ k : Nat, k < n' ∧ Restated.tickStepAt M x k ((Restated.Vocabulary.Execution.Setup.a M S a.round)) ∧
      h' ≤ (x[k][v].st).st.core.h_max := by
  classical
  obtain ⟨-, k, hkn, htick, -, out, hout, hmem⟩ :=
    Restated.attest_round_of_sent facts S Sched x hv hunf hidx (le_refl ((x[n'].time : Nat) : Int)) hsent
  obtain ⟨w, hw, hwv⟩ := Restated.stateBeforeTime_runOf_action facts S Sched x htick v
  have hw' : w ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M (Setup.alwaysAwake S)
      (Record.runOfM M S Sched x v (k + 1))
      (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) a.round) := hw
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc (w v).st.core.toHealing
    (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) a.round) (w v).cache
  obtain ⟨st, hst⟩ := facts.dt.duties_update_confirmation_with_nonempty (M.gradeContract c) S.E
    S.hc (M.ns_setClock S.E (w v).st
      (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) a.round))
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) a.round) - 1)
  have hn : M.mkNode st (w v).record c ∈
      Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (w v) a.round := ⟨c, hc, st, hst, rfl⟩
  have hnmem : M.mkNode st (w v).record c ∈
      Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt M (Setup.alwaysAwake S)
        (Record.runOfM M S Sched x v (k + 1)) v a.round := ⟨w, hw', hn⟩
  obtain ⟨D, hD⟩ := facts.dt.attest_with_nonempty (M.gradeContract (M.mkNode st (w v).record c).cache)
    S.E S.hc ((Setup.alwaysAwake S).node v) (M.mkNode st (w v).record c).st
    (M.mkNode st (w v).record c).record
  have haeq : a = D.2.2 := by
    have _hr_s1 := Record.reachedNode_wakeStage facts S Sched x (k) v (Restated.Vocabulary.Execution.Setup.a M S a.round)
    have _hv_s2 := Record.runs_as_wakeStage facts S Sched x (k) v (Restated.Vocabulary.Execution.Setup.a M S a.round)
    refine Restated.attest_of_tick_eq facts S v
      (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S a.round) x[k] v) a.round
      hout hmem D.2.2 ?_
    have hread : Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S a.round) x[k] v) a.round =
        Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
          (w v) a.round := by
      unfold Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom
      rw [Record.wakeStage_st facts, Record.wakeStage_cache facts, Record.wakeStage_record facts,
        hwv]
    exact ⟨_, by rw [hread]; exact hn, D.1, D.2.1, hD⟩
  have hpair' : D.2.2.height_pair = NamedHeightPair.vote h' entry tmo := by
    rw [← haeq]
    exact hpair
  obtain ⟨A2, hA2⟩ := facts.dt.grade2_block_with_nonempty
    (M.gradeContract (M.mkNode st (w v).record c).cache)
    (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc (M.toHealing (M.mkNode st (w v).record c).st.core)
    (M.round_of (Setup.alwaysAwake S).hc (M.toHealing (M.mkNode st (w v).record c).st.core).s)
  obtain ⟨o, ho⟩ := facts.dt.fg_source_with_nonempty
    (M.gradeContract (M.mkNode st (w v).record c).cache)
    (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc (M.toHealing (M.mkNode st (w v).record c).st.core)
    (M.round_of (Setup.alwaysAwake S).hc (M.toHealing (M.mkNode st (w v).record c).st.core).s) A2
  have hsrc : Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M (Setup.alwaysAwake S)
      (M.mkNode st (w v).record c) ⇢ o :=
    (returns_bind_iff_r11 _ _ _).2 ⟨A2, hA2, ho⟩
  obtain ⟨Cfg, rfl, hCfgh, -⟩ :=
    Restated.source_of_actionAttestation_heightPair facts (Setup.alwaysAwake S)
      (Record.runOfM M S Sched x v (k + 1)) v a.round _ hnmem D hD hpair' o hsrc
  have hCfgT : Cfg ∈ (w v).st.core.T :=
    Restated.fgSource_mem_stateBeforeTime' facts (Setup.alwaysAwake S)
      (Record.runOfM M S Sched x v (k + 1)) v a.round w hw' _ hn hsrc
  have hσ : (M.mkNode st (w v).record c).st.core.σ = (w v).st.core.σ := by
    rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    obtain ⟨X, hX⟩ := facts.dt.update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc
      (M.ns_setClock S.E (w v).st
        (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) a.round)).core
      (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) a.round) - 1)
    rw [facts.dt.named_update_confirmation_with_core _ _ _ _ _ st hst X hX,
      facts.dt.update_confirmation_with_σ _ _ _ _ _ X hX, facts.hd.ModelProperties_setClock_core_σ]
  rw [hσ, hwv] at hCfgh
  rw [hwv] at hCfgT
  have hbound := Restated.treeHeightsLeHMax_sts facts S Sched x k v Cfg hCfgT
  rw [hCfgh] at hbound
  exact ⟨k, hkn, htick, hbound⟩

end

end DecoupledConsensusModel.Sts.Restated
