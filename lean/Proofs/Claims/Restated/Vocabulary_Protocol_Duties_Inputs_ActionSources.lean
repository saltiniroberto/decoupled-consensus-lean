import Proofs.Vocabulary.Protocol.Duties.Inputs.ActionSources
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_ModelVocabulary_Healing_Schedule
import Proofs.Vocabulary.Protocol.Schedule.NamedTick
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedActionReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Healing_Action
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring

/-!
# The sources of a round action

Theorems over a model `M : Record.Model V` and its facts `facts : Record.Facts M`: what a tick at a
round's action time sends, the timing of the action, and the FG source of an action read, which is
in the store's block tree, fixes the height pair of the action's attestation, and has a retained
named body.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedActionSources
open Execution NamedActionReads

/-- For every outcome `out₁` of `v`'s tick at round `r`'s action time from `before`, every node
    state `n` of the action read `actionReadFrom M S before r` and every outcome `D` of the
    attestation duty on `n`, either `before` passes the grade-2 awake test `M.awake_for_grade2` of
    round `r` and `out₁` sends the one attestation of `D`, or it does not and `out₁` sends nothing. -/
theorem Vocabulary.Proofs.NamedActionSources.tick_at_action (facts : Record.Facts M) (S : Setup V) (v : V) (before : M.N) (r : Round) : ∀ out₁, M.tick S v before ((Restated.Vocabulary.Execution.Setup.a M S r)) ⇢ out₁ →
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
    ∀ D, M.duties_attest_with (M.gradeContract n.cache) S.E S.hc (S.node v) n.st n.record ⇢ D →
    ∀ (hn : M.reachedNode before := by trivial) (hv : M.runs_as before v := by trivial),
    (M.awake_for_grade2 S v before r ∧ out₁.2 = [NamedObject.attest D.2.2]) ∨
      (¬ M.awake_for_grade2 S v before r ∧ out₁.2 = []) := by
  intro out hout n hn D hD _hn _hv
  obtain ⟨c, hc, st, hst, rfl⟩ := hn
  rw [facts.nd.mkNode_cache, facts.nd.mkNode_st, facts.nd.mkNode_record,
    facts.dt.duties_attest_with_store_with_cache] at hD
  by_cases hrun : M.awake_for_grade2 S v before r
  · exact Or.inl ⟨hrun, facts.nd.tick_at_action_awake S v before r out hout c hc st hst D hD hrun⟩
  · exact Or.inr ⟨hrun, facts.nd.tick_at_action_asleep S v before r out hout hrun⟩

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedActionSources
open Execution NamedActionReads

/-- If the named store `st` satisfies the confirmation-membership invariant, `A2` is an outcome of
    the grade-2 block of `st`'s core store at round `r` under the grade contract of `cache`, and the
    FG source at `A2` can return `raw`, then `raw` is in `st`'s core block tree. -/
theorem Vocabulary.Proofs.NamedActionSources.frame_fg_source_mem (facts : Record.Facts M) (S : Setup V) (cache : M.Cache)
    (st : M.NS) (r : Round)
    (hinv : Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant M S.E S.cfg st)
    {raw : Block V}
    (A2 : Option (Block V))
    (hA2 : M.grade2_block_with (M.gradeContract cache) S.E S.hc (M.toHealing st.core) r ⇢ A2)
    (hs : M.fg_source_with (M.gradeContract cache)
      S.E S.hc (M.toHealing st.core) r A2 ⇢ some raw) : raw ∈ st.core.T :=
  facts.dt.frame_fg_source_mem S cache st r hinv A2 hA2 _ hs rfl

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedActionSources
open Execution NamedActionReads

/-- The slot of round `r`'s action time is positive, the action time is the support cutoff of its
    slot, and every node state of the action read `actionReadFrom M S before r` has its core store's
    slot in round `r`. -/
theorem Vocabulary.Proofs.NamedActionSources.action_timing (facts : Record.Facts M) (S : Setup V) (before : M.N) (r : Round) :
    0 < S.E.slotOf ((Restated.Vocabulary.Execution.Setup.a M S r)) ∧
    (Restated.Vocabulary.Execution.Setup.a M S r) = M.support_cutoff S.E (S.E.slotOf ((Restated.Vocabulary.Execution.Setup.a M S r))) ∧
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      (M.round_of S.hc n.st.core.s) = r := by
  have hslot : S.E.slotOf ((Restated.Vocabulary.Execution.Setup.a M S r)) =
      M.opening_slot S.hc r + 1 := by
    rw [Restated.Vocabulary.Execution.Setup.a, facts.sch.a_eq_confirmation_time]
    exact facts.sch.Optimistic_slotOf_confirmation_time S.E _
  refine ⟨by rw [hslot]; exact Nat.succ_pos _, ?_, ?_⟩
  · rw [hslot, Restated.Vocabulary.Execution.Setup.a, facts.sch.a_eq_confirmation_time,
      facts.sch.confirmation_time_eq_support_cutoff_succ]
  · intro n hn
    obtain ⟨c, hc, st, hst, rfl⟩ := hn
    rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [(facts.dt.named_confirmation_clock _ _ _ _ _ st hst).2,
      facts.hd.ModelProperties_setClock_core_s]
    exact Restated.Vocabulary.Proofs.HealingLemmas.round_of_slotOf_a facts S r

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedActionSources
open Execution NamedActionReads

/-- For every node state `n` that `v`'s action read at round `r` can be, if the row of an outcome of
    the attestation duty on `n` carries the height pair `(h, entry, timeout)`, then every outcome of
    the FG source of `n` is some block whose height in `n`'s core store is `h` and whose entry root
    there is `entry`. -/
theorem Vocabulary.Proofs.NamedActionSources.action_source (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (v : V) (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Proofs.HealingSurface.actionReadAt M S rho v r,
    ∀ h entry timeout,
      ∀ D, M.duties_attest_with (M.gradeContract n.cache) S.E S.hc (S.node v) n.st
          n.record ⇢ D →
      D.2.2.height_pair = .vote h entry timeout →
      ∀ o, Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ o →
      ∃ Cfg, o = some Cfg ∧
        (n.st.core.σ Cfg).h = h ∧
        (n.st.core.σ Cfg).T_h.root = entry := by
  intro n _ h entry timeout D hD hp o ho
  let gc := M.gradeContract n.cache
  obtain ⟨A, hA⟩ := facts.dt.round_action_with_nonempty gc S.E S.hc (S.node v)
    (M.toHealing n.st.core) n.record
  have hpair : A.2.height_pair = .vote h entry timeout := by
    rw [← facts.dt.attest_with_row gc S.E S.hc (S.node v) n.st n.record D hD A hA]
    exact hp
  obtain ⟨I, hI⟩ := facts.dt.with_attestation_input_nonempty gc S.E S.hc (S.node v)
    (M.toHealing n.st.core)
  obtain ⟨nu, hfields⟩ := facts.dt.round_action_names_source gc S.E S.hc
    (S.node v) (M.toHealing n.st.core) n.record h entry timeout A hA hpair I hI
  have hdec : ∃ A2, M.grade2_block_with gc S.E S.hc (M.toHealing n.st.core)
      (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ A2 ∧
      M.fg_source_with gc S.E S.hc (M.toHealing n.st.core)
        (M.round_of S.hc (M.toHealing n.st.core).s) A2 ⇢ o := by
    simp only [Restated.Vocabulary.Proofs.HealingSurface.actionFGSource, Record.Returns,
      ExceptT.run_bind, Set.bind_def, Set.mem_iUnion] at ho
    obtain ⟨x, hx, hb⟩ := ho
    cases x with
    | ok a => exact ⟨a, hx, hb⟩
    | error e => simp at hb
  obtain ⟨A2, hA2, hF⟩ := hdec
  rw [facts.dt.with_attestation_input_id_fields gc S.E S.hc (S.node v) _ I hI A2 hA2 o hF,
    facts.sto.ModelProperties_toHealing_σ] at hfields
  obtain ⟨Cfg, hCfg, hvalues⟩ := Option.map_eq_some_iff.mp hfields
  exact ⟨Cfg, hCfg, congrArg Prod.fst hvalues,
    congrArg (fun x : Height × BlockId × Bool => x.2.1) hvalues⟩

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedActionSources
open Execution NamedActionReads

/-- If the named store `st` satisfies the confirmation-membership invariant, so does `st` with the
    grade cache `c` written into it. -/
private theorem invariant_store_with_cache (facts : Record.Facts M) (E : Env V)
    (cfg : Protocol.HeightConfig) (st : M.NS) (c : M.Cache)
    (h : Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant M E cfg st) :
    Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant M E cfg
      (M.store_with_cache st c) := by
  simp only [Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant,
    Restated.Vocabulary.Proofs.NamedStoreRoots.Invariant, Restated.Vocabulary.Proofs.NamedStore.Coherent,
    Restated.Vocabulary.Proofs.NamedStore.TreeView, Restated.Vocabulary.Proofs.NamedStore.ErasureUnique,
    Restated.Vocabulary.Proofs.NamedStore.NamedParentClosed, Restated.Vocabulary.Proofs.NamedStore.PoolView,
    Restated.Vocabulary.Proofs.NamedStore.DerivedView, Restated.Vocabulary.Proofs.NamedStoreRoots.RootsInTree,
    Restated.Vocabulary.Proofs.NamedConfirmationMembership.Confirmed,
    facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView, facts.nd.store_with_cache_bodies,
    facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_sg_votes,
    facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau,
    facts.nd.store_with_cache_core_attestations] at h ⊢
  exact h

/-- For every node state `n` that `v`'s action read at round `r` can be, if the FG source of `n` can
    return `Cfg`, then some named block `C` held in `n`'s store erases to `Cfg`, `n`'s core store
    maps `Cfg` to the chain state `M.derive_named` gives `C`, and the FG confirmation witness of `n`
    can return that chain state's `T_h`. -/
theorem Vocabulary.Proofs.NamedActionSources.action_witness (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (v : V) (r : Round) : ∀ w₁ ∈ Restated.Vocabulary.Proofs.HealingSurface.actionReadAt M S rho v r,
    ∀ Cfg, Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S w₁ ⇢
        some Cfg →
      ∃ C : NamedBlock V,
        C ∈ w₁.st.bodies ∧ C.erase = Cfg ∧
        w₁.st.core.σ Cfg =
          M.derive_named S.E S.cfg C ∧
        Restated.Vocabulary.Proofs.HealingSurface.fgConfirmationWitness M S w₁ ⇢
          some (M.derive_named S.E S.cfg C).T_h := by
  intro n hn Cfg hCfg
  have hinv : Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant M S.E S.cfg n.st := by
    obtain ⟨w, hw, c, hc, st, hst, hn⟩ := hn
    rewrite [hn, facts.nd.mkNode_st]
    exact invariant_store_with_cache facts S.E S.cfg st c
      (facts.dt.invariant_update_gradeContract c S.E S.hc S.cfg _ _
        (facts.hd.invariant_clock S.E S.cfg _ _
          (Restated.Vocabulary.Proofs.NamedRuntime.stateBeforeTime_invariants facts S rho _ v w hw).1)
        st hst)
  have hcoh : Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg n.st := hinv.1.1
  have hdec : ∃ A2, M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
      (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ A2 ∧
      M.fg_source_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
        (M.round_of S.hc (M.toHealing n.st.core).s) A2 ⇢ some Cfg := by
    have ho := hCfg
    simp only [Restated.Vocabulary.Proofs.HealingSurface.actionFGSource, Record.Returns,
      ExceptT.run_bind, Set.bind_def, Set.mem_iUnion] at ho
    obtain ⟨x, hx, hb⟩ := ho
    cases x with
    | ok a => exact ⟨a, hx, hb⟩
    | error e => simp at hb
  obtain ⟨A2, hA2, hF⟩ := hdec
  have hmem : Cfg ∈ n.st.core.T := Restated.Vocabulary.Proofs.NamedActionSources.frame_fg_source_mem facts S n.cache n.st
    ((M.round_of S.hc (M.toHealing n.st.core).s)) hinv A2 hA2 hF
  rw [hcoh.1] at hmem
  obtain ⟨C, hC, hErase⟩ := Finset.mem_image.mp hmem
  have hDerived : n.st.core.σ Cfg = M.derive_named S.E S.cfg C := by
    rw [← hErase]
    exact hcoh.2.2.2.2 C hC
  refine ⟨C, hC, hErase, hDerived, ?_⟩
  rw [← hDerived]
  simp only [Restated.Vocabulary.Proofs.HealingSurface.fgConfirmationWitness, Record.Returns,
    ExceptT.run_map]
  exact ⟨_, hCfg, rfl⟩

end

end DecoupledConsensusModel.Sts.Restated
