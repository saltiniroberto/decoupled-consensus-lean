import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bStepConeIter
import Proofs.Claims.Restated.Claim13beRoute3_45
import Proofs.Claims.Restated.Claim13beRoute3_46
import Proofs.Claims.Restated.Claim13beRoute3_48
import Proofs.Claims.Restated.Claim13beRoute3_48b
import Proofs.Claims.Restated.Claim13beRoute3_49
import Proofs.Claims.Restated.Claim13beRoute3_54
import Proofs.Claims.Restated.Claim13beRoute3_58
import Proofs.Claims.Restated.Claim13beRoute3_60b
import Proofs.Claims.Restated.Claim13beRoute3_61
import Proofs.Claims.Restated.Claim13beRoute3_62
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_ModelVocabulary_Healing_Schedule
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_Ladder
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_RowTrace
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_SlotInduction
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_42c
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.RunVocabulary
import Model.Conditions.Vocabulary_Internal_Definitions_NamedLifecycle
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGradeQueries
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Internal_HealingSurface
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedHeadReads
import Proofs.Vocabulary.Internal.Legacy.Definitions.NamedVoteConsumers
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_ModelVocabulary_Healing_Schedule
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Vocabulary.Protocol.Grades
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_FinalityFilterInterference
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_SeedCeiling
import Proofs.Vocabulary.Protocol.Grades.RelativeOneChain
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring

/-!
# Grades, round ceilings and settlement while heights hold

Theorems over a model `M : Record.Model V` and its facts, read along a path `W` of a run with the
admissible fields `hf`. While every member of the honest sets has `h_j + 2 ≤ Mh` and `h_max = Mh`,
they give genesis graded, the freeze root present, the first round ceiling and its carry to later
rounds, grade-1 settlement, the height of voted heads and the compatibility of action carriers.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

/-! ## Helpers -/

section
set_option autoImplicit false
open scoped DC
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Proofs.HealingSurface

/-- In a run sorted by key, the worlds strictly before the time `t` are the worlds before the event
    of index `strictEventIndex rho t`. -/
private theorem stateBeforeTime_eq_strict₆₄b (S : Setup V) (rho : Record.Run V)
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f)) (t : Time) :
    Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t =
      Record.stateBeforeOf M S rho (strictEventIndex rho t) := by
  have hpre : rho.events.filter (fun e => decide (e.time < t)) =
      rho.events.take (rho.events.filter (fun e => decide (e.time < t))).length := by
    refine List.prefix_iff_eq_take.mp ?_
    rw [DecoupledConsensusModel.Proofs.Bridges.filter_eq_takeWhile_of_pairwise
      (R := fun e f => Record.Event.key e ≤ Record.Event.key f) ?_ _ hsorted]
    · exact List.takeWhile_prefix _
    · intro e f hk hf
      simp only [decide_eq_true_eq] at hf ⊢
      exact lt_of_le_of_lt (Restated.time_le_of_key_le hk) hf
  show (rho.events.filter (fun e => decide (e.time < t))).foldlM (Record.worldStepOf M S)
      (fun v => M.initial S v) =
    (rho.events.take (rho.events.filter (fun e => decide (e.time < t))).length).foldlM
      (Record.worldStepOf M S) (fun v => M.initial S v)
  rw [← hpre]

/-- In a run sorted by key, the world of a path `W` before the event of index
    `strictEventIndex rho t` is a world strictly before `t`. -/
private theorem mem_stateBeforeTime_along₆₄b {S : Setup V} {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (t : Time) :
    W (strictEventIndex rho t) ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t := by
  rw [stateBeforeTime_eq_strict₆₄b S rho hsorted]
  exact (hW _).1

/-- The round-`r` action read from `before` has a node state on which the grade-2 block read and the
    SG vote selector each can return a value. -/
private theorem exists_actionSG₆₄b (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∃ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      ∃ g, M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ g ∧
        ∃ B, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) g ⇢ B := by
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc before.st.core.toHealing
    (Restated.Vocabulary.Execution.Setup.a M S r) before.cache
  obtain ⟨st, hst⟩ := facts.dt.duties_update_confirmation_with_nonempty (M.gradeContract c) S.E
    S.hc (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r))
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
  refine ⟨M.mkNode st before.record c, ⟨c, hc, st, hst, rfl⟩, ?_⟩
  obtain ⟨g, hg⟩ := facts.dt.grade2_block_with_nonempty
    (M.gradeContract (M.mkNode st before.record c).cache) S.E S.hc
    (M.toHealing (M.mkNode st before.record c).st.core)
    (M.round_of S.hc (M.toHealing (M.mkNode st before.record c).st.core).s)
  obtain ⟨B, hB⟩ := facts.dt.get_sg_vote_with_nonempty
    (M.gradeContract (M.mkNode st before.record c).cache) S.E S.hc
    (M.toHealing (M.mkNode st before.record c).st.core)
    (M.round_of S.hc (M.toHealing (M.mkNode st before.record c).st.core).s) g
  exact ⟨g, hg, B, hB⟩

/-- Every node state of the round-`r` action read from `before` has the finalized block of
    `before`'s core store. -/
private theorem actionReadFrom_F₆₄b (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      n.st.core.F = before.st.core.F := by
  rintro _ ⟨c, -, st, hst, rfl⟩
  obtain ⟨X, hX⟩ := facts.dt.update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc
    (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r)).core
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
  rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.dt.named_update_confirmation_with_core _ _ _ _ _ st hst X hX,
    facts.dt.update_confirmation_with_F _ _ _ _ _ X hX, facts.hd.setClock_core_F]

/-- If `f <$> m` can return `b`, then `m` can return some `a` with `f a = b`. -/
private theorem returns_map_elim₆₄b {α β : Type} (f : α → β) (m : DC.NDRE α) (b : β)
    (h : (f <$> m) ⇢ b) : ∃ a, m ⇢ a ∧ f a = b := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image] at h
  obtain ⟨e, he, hb⟩ := h
  cases e with
  | ok a => exact ⟨a, he, by simpa [Except.map] using hb⟩
  | error err => simp [Except.map] at hb

/-- If the grade-2 selection of `n` at round `r` can return `some Q`, the finalized block of `n`'s
    core store is an ancestor of `Q`. -/
private theorem nodeQ2_F_preceq₆₄b (facts : Record.Facts M) (S : Setup V) (n : M.N) (r : Round)
    {Q : Block V} (hQ : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ some Q) :
    Block.Preceq n.st.core.F Q := by
  unfold Restated.Vocabulary.Internal.PhaseGrades.nodeQ2
    Restated.Vocabulary.Internal.PhaseGrades.nodeRead at hQ
  obtain ⟨G, hG, hGQ⟩ := returns_map_elim₆₄b _ _ _ hQ
  obtain ⟨x, hx⟩ := facts.gr.grade2Block_nonempty (M.toHealing n.st.core)
    (M.readFrame n.cache (M.toHealing n.st.core) r)
  have hxQ : x = some Q :=
    (facts.nd.ModelProperties_gradeContract_read_Q2 n.cache S.E S.hc (M.toHealing n.st.core) r G hG
      x hx).symm.trans hGQ
  have hmem := facts.gr.mem_filtered_of_grade2Block x hx hxQ
  have h := facts.fc.q10_filtered_F hmem
  rwa [facts.sto.Sts_toHealing_F] at h

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.HealingLemmas

/-- Along the path `W` with the admissible fields `hf`, if `0 < q`, `S.a q` is in the horizon and
    `lo ≤ opening (q − η_SG)`, then for every member `v` of the set for `domain q g0` and every node
    state of `v`'s round-`q` action read whose Q2 can return `some Q`, every outcome of the grade-1
    store grade of `Q` on `v`'s store in `W` before `domain q .g1` is `true`. -/
theorem namedG1At_of_nodeQ2On (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {q : Round} (hq : 0 < q) (hhor : (Restated.Vocabulary.Execution.Setup.a M S q) ≤ rho.horizon)
    (hlo : lo ≤ M.opening S.E S.hc (q - S.hc.η_SG)) :
    ∀ v ∈ Hs (M.domain S.E S.hc q .g0), ∀ Q : Block V,
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v) q,
      Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n q ⇢ some Q →
      ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
        (W (strictEventIndex rho (M.domain S.E S.hc q .g1)) v).st q .g1 Q ⇢ b → b = true := by
  intro v hv Q n hn hQ
  have hvL1 : v ∈ Hs (M.late S.E S.hc q .g1) :=
    hHs _ _ ((facts.gr.q10_late_g1_le_domain_g2 S q).trans (facts.gr.domain_le_domain_g0 S q .g2)) hv
  have hG2 := Restated.selectedQ2_storeGrade_at_g2DomainOn facts S Hs Xb hf n hn hQ
  obtain ⟨b2, hb2⟩ := facts.gr.gradeBool_nonempty S.E
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc q .g2)) v).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc q .g2)) v).st.core.F
    S.hc.η_SG q (M.early S.E S.hc q .g2) (M.late S.E S.hc q .g2) Q
  have hb2t : b2 = true := hG2 b2 hb2
  subst hb2t
  have hFQ : Block.Preceq n.st.core.F Q := nodeQ2_F_preceq₆₄b facts S n q hQ
  have hFn := actionReadFrom_F₆₄b facts S _ q n hn
  have hFB : Block.Preceq
      (W (strictEventIndex rho (M.domain S.E S.hc q .g1)) v).st.core.F Q := by
    refine preceq_trans_Preceq
      (Restated.seedRel_stateBeforeTime_F_monoOn facts S Hs Xb hf v (facts.gr.domain_le_a S q .g1)) ?_
    rw [← hFn]
    exact hFQ
  exact Restated.q10_grade_crossOn facts S rho Hs Xb hf hHs hHsXb v q hvL1 hq hlo Q hFB hb2

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.HealingLemmas

/-- Along the path `W` with the admissible fields `hf`, if `u` is in the set for `t` and `z` is in
    an outcome `X` of the raw round-`r` inputs of `u` on `w`'s store in `W` before `t`, then for
    some round `k`, `z` is `⟨u, k, some C.root⟩` for every block `C` the SG selector can return on a
    node state of `u`'s round-`k` action read along `W`. -/
theorem seedQ2_rawInput_eq_actionOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {w u : V} {t : Time} (hu : u ∈ Hs t) {r : Round} {cutoff : Time}
    {z : Protocol.SGVote V}
    (X : Finset (Protocol.SGVote V))
    (hX : M.rawInputs
      (M.gradeView (M.toHealing (W (strictEventIndex rho t) w).st.core))
      S.hc.η_SG r cutoff u ⇢ X)
    (hz : z ∈ X) :
    ∃ k : Round, ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S k)) u) k,
      ∀ g, M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ g →
      ∀ C, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) g ⇢ C →
      z = (⟨u, k, some C.root⟩ : Protocol.SGVote V) := by
  obtain ⟨⟨k, -, hzk⟩, hzidx, -⟩ := facts.gr.rawInputs_mem_window _ S.hc.η_SG r cutoff u X hX hz
  rw [facts.gr.gradeView_sg_votes, ← facts.sto.Sts_toHealing_sg_votes] at hzk
  exact ⟨k, Restated.honestSGVote_eq_actionSGVoteAt_of_mem_storeBeforeTimeOn facts
    S Hs Xb hf hHs hu hzk hzidx⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.HealingLemmas

/-- Two members of the same round in one outcome of the raw round-`r` inputs of a member `u` of the
    set for `t`, on `w`'s store in `W` before `t`, are equal. -/
private theorem seedQ2_rawInputs_eq_of_round₆₄b (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {w u : V} {t : Time} (hu : u ∈ Hs t) {r : Round} {cutoff : Time}
    (Y : Finset (Protocol.SGVote V))
    (hY : M.rawInputs
      (M.gradeView (M.toHealing (W (strictEventIndex rho t) w).st.core))
      S.hc.η_SG r cutoff u ⇢ Y)
    {zx zy : Protocol.SGVote V} (hzx : zx ∈ Y) (hzy : zy ∈ Y) (hround : zx.round = zy.round) :
    zx = zy := by
  obtain ⟨kx, hkx⟩ := Restated.seedQ2_rawInput_eq_actionOn facts S Hs Xb hf hHs hu Y hY hzx
  obtain ⟨ky, hky⟩ := Restated.seedQ2_rawInput_eq_actionOn facts S Hs Xb hf hHs hu Y hY hzy
  obtain ⟨nx, hnx, gx, hgx, Cx, hCx⟩ := exists_actionSG₆₄b facts S
    (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S kx)) u) kx
  obtain ⟨ny, hny, gy, hgy, Cy, hCy⟩ := exists_actionSG₆₄b facts S
    (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S ky)) u) ky
  have hxe := hkx nx hnx gx hgx Cx hCx
  have hye := hky ny hny gy hgy Cy hCy
  have hkk : kx = ky := by
    have h := hround
    rw [hxe, hye] at h
    exact h
  subst hkk
  rw [hkx ny hny gy hgy Cy hCy, hye]

/-- Every member of an outcome of the interpreted round-`r` inputs of a member `u` of the set for
    `t` confirms a root that the tree of that store's grade view resolves to a block. -/
private theorem seedQ2_readyInput_find₆₄b (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {w u : V} {t : Time} (hu : u ∈ Hs t) {r : Round}
    {cutoff : Time} {z : Protocol.SGVote V}
    (I : Finset (Protocol.SGVote V))
    (hI : M.interpretedInputs
      (M.gradeView (M.toHealing (W (strictEventIndex rho t) w).st.core))
      (W (strictEventIndex rho t) w).st.core.F S.hc.η_SG r cutoff u ⇢ I)
    (hz : z ∈ I) :
    ∃ (root : BlockId) (H : Block V), z.confirmed = some root ∧
      Block.find? (M.gradeView (M.toHealing (W (strictEventIndex rho t) w).st.core)).T root =
        some H := by
  obtain ⟨R, hR⟩ := facts.gr.rawInputs_nonempty
    (M.gradeView (M.toHealing (W (strictEventIndex rho t) w).st.core)) S.hc.η_SG r cutoff u
  obtain ⟨bz, hbz⟩ := facts.gr.bodyReady_nonempty
    (M.gradeView (M.toHealing (W (strictEventIndex rho t) w).st.core))
    (W (strictEventIndex rho t) w).st.core.F cutoff z
  obtain ⟨hzR, hready⟩ := (facts.gr.mem_interpretedInputs_iff I hI R hR bz hbz).mp hz
  obtain ⟨k, hzk⟩ := Restated.seedQ2_rawInput_eq_actionOn facts S Hs Xb hf hHs hu R hR hzR
  obtain ⟨n, hn, g, hg, C, hC⟩ := exists_actionSG₆₄b facts S
    (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S k)) u) k
  have hconf : z.confirmed = some C.root := by
    rw [hzk n hn g hg C hC]
  cases hfind : Block.find?
      (M.gradeView (M.toHealing (W (strictEventIndex rho t) w).st.core)).T C.root with
  | none =>
    have hfalse := facts.gr.bodyReady_eq_false_of_find_none _ _ cutoff z hconf hfind bz hbz
    rw [hready] at hfalse
    exact absurd hfalse (by simp)
  | some H => exact ⟨C.root, H, hconf, hfind⟩

/-- For every member `z` of an outcome of the interpreted round-`r` inputs of a member `u` of the
    set for `t`, every outcome of the test whether the key of `z`'s token covers genesis in the tree
    of that store's grade view is `true`. -/
private theorem seedQ2_readyInput_head_covers₆₄b (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {w u : V} {t : Time} (hu : u ∈ Hs t) {r : Round}
    {cutoff : Time} {z : Protocol.SGVote V}
    (I : Finset (Protocol.SGVote V))
    (hI : M.interpretedInputs
      (M.gradeView (M.toHealing (W (strictEventIndex rho t) w).st.core))
      (W (strictEventIndex rho t) w).st.core.F S.hc.η_SG r cutoff u ⇢ I)
    (hz : z ∈ I) :
    ∀ b : Bool, M.head_covers
      (M.gradeView (M.toHealing (W (strictEventIndex rho t) w).st.core)).T Block.genesis
      (M.token z).key ⇢ b → b = true := by
  intro b hb
  obtain ⟨root, H, hconf, hfind⟩ := seedQ2_readyInput_find₆₄b facts S Hs Xb hf hHs hu I hI hz
  rw [facts.gr.token_key, hconf] at hb
  exact facts.gr.head_covers_of_find hfind
    (preceq_eq_true_iff_Preceq.mp (Protocol.preceq_genesis H)) b hb

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.HealingLemmas

/-- Along the path `W` with the admissible fields `hf`, if `u` is in the set for `t`, the test
    whether `u` opposes genesis on `w`'s store in `W` before `t` cannot return `true`. -/
theorem seedQ2_honest_not_opposing_genesisOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {w u : V} {t : Time} (hu : u ∈ Hs t) {r : Round} {ea la : Time}
    (hopp : M.opposing
      (M.gradeView (M.toHealing (W (strictEventIndex rho t) w).st.core))
      (W (strictEventIndex rho t) w).st.core.F S.hc.η_SG r ea la u
      Block.genesis ⇢ true) : False := by
  set gv := M.gradeView (M.toHealing (W (strictEventIndex rho t) w).st.core) with hgv
  set F := (W (strictEventIndex rho t) w).st.core.F with hF
  let cov : Option BlockId → Bool := fun k =>
    Classical.choose (facts.gr.head_covers_nonempty gv.T Block.genesis k)
  have hcov' : ∀ k, M.head_covers gv.T Block.genesis k ⇢ cov k := fun k =>
    Classical.choose_spec (facts.gr.head_covers_nonempty gv.T Block.genesis k)
  obtain ⟨Re, hRe⟩ := facts.gr.readyView_nonempty gv F S.hc.η_SG r ea u
  obtain ⟨Rl, hRl⟩ := facts.gr.readyView_nonempty gv F S.hc.η_SG r la u
  obtain ⟨Wv, hWv⟩ := facts.gr.rawView_nonempty gv S.hc.η_SG r la u
  rcases facts.gr.conditions_of_opposing gv F S.hc.η_SG r ea la u Block.genesis true hopp rfl
      Re hRe Rl hRl Wv hWv cov hcov' with ⟨x, hx, -, hnot⟩ | ⟨x, hx, y, hy, -, hround, hkey⟩
  · obtain ⟨Il, hIl⟩ := facts.gr.interpretedInputs_nonempty gv F S.hc.η_SG r la u
    obtain ⟨z, hz, rfl⟩ := (facts.gr.mem_readyView_iff Rl hRl Il hIl).mp hx
    exact hnot (seedQ2_readyInput_head_covers₆₄b facts S Hs Xb hf hHs hu Il hIl hz (cov _) (hcov' _))
  · obtain ⟨Y, hY⟩ := facts.gr.rawInputs_nonempty gv S.hc.η_SG r la u
    obtain ⟨zx, hzx, rfl⟩ := (facts.gr.mem_rawView_iff gv S.hc.η_SG r la u x Wv hWv Y hY).mp hx
    obtain ⟨zy, hzy, rfl⟩ := (facts.gr.mem_rawView_iff gv S.hc.η_SG r la u y Wv hWv Y hY).mp hy
    rw [facts.gr.token_round, facts.gr.token_round] at hround
    apply hkey
    rw [seedQ2_rawInputs_eq_of_round₆₄b facts S Hs Xb hf hHs hu Y hY hzx hzy hround]

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.HealingLemmas

/-- Along the path `W` with the admissible fields `hf`, if `u` is in the set for `t`, `ea ≤ la`, and
    the ready view of `u` at `ea` on `w`'s store in `W` before `t` can return a non-empty set `Re`,
    then every outcome of the test whether `u` is positive for genesis there is `true`. -/
theorem seedQ2_honest_positive_genesisOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {w u : V} {t : Time} (hu : u ∈ Hs t) {r : Round} {ea la : Time}
    (hcut : ea ≤ la)
    (Re : Finset (Protocol.Token (Option BlockId)))
    (hRe : M.readyView
      (M.gradeView (M.toHealing (W (strictEventIndex rho t) w).st.core))
      (W (strictEventIndex rho t) w).st.core.F S.hc.η_SG r ea u ⇢ Re)
    (hne : Re.Nonempty) :
    ∀ b : Bool, M.positive
      (M.gradeView (M.toHealing (W (strictEventIndex rho t) w).st.core))
      (W (strictEventIndex rho t) w).st.core.F S.hc.η_SG r ea la u
      Block.genesis ⇢ b → b = true := by
  intro b hb
  set gv := M.gradeView (M.toHealing (W (strictEventIndex rho t) w).st.core) with hgv
  set F := (W (strictEventIndex rho t) w).st.core.F with hF
  let cov : Option BlockId → Bool := fun k =>
    Classical.choose (facts.gr.head_covers_nonempty gv.T Block.genesis k)
  have hcov' : ∀ k, M.head_covers gv.T Block.genesis k ⇢ cov k := fun k =>
    Classical.choose_spec (facts.gr.head_covers_nonempty gv.T Block.genesis k)
  obtain ⟨u₀, hu₀, hmax⟩ := Finset.exists_max_image Re (fun x => x.round) hne
  obtain ⟨Ie, hIe⟩ := facts.gr.interpretedInputs_nonempty gv F S.hc.η_SG r ea u
  have hcovU : cov u₀.key = true := by
    obtain ⟨z, hz, rfl⟩ := (facts.gr.mem_readyView_iff Re hRe Ie hIe).mp hu₀
    exact seedQ2_readyInput_head_covers₆₄b facts S Hs Xb hf hHs hu Ie hIe hz (cov _) (hcov' _)
  obtain ⟨Wv, hWv⟩ := facts.gr.rawView_nonempty gv S.hc.η_SG r la u
  have hclean : ∀ x ∈ Wv, ∀ y ∈ Wv, u₀.round ≤ x.round → x.round = y.round → x.key = y.key := by
    intro x hx y hy _ hxy
    obtain ⟨Y, hY⟩ := facts.gr.rawInputs_nonempty gv S.hc.η_SG r la u
    obtain ⟨zx, hzx, rfl⟩ := (facts.gr.mem_rawView_iff gv S.hc.η_SG r la u x Wv hWv Y hY).mp hx
    obtain ⟨zy, hzy, rfl⟩ := (facts.gr.mem_rawView_iff gv S.hc.η_SG r la u y Wv hWv Y hY).mp hy
    rw [facts.gr.token_round, facts.gr.token_round] at hxy
    rw [seedQ2_rawInputs_eq_of_round₆₄b facts S Hs Xb hf hHs hu Y hY hzx hzy hxy]
  obtain ⟨Rl, hRl⟩ := facts.gr.readyView_nonempty gv F S.hc.η_SG r la u
  have hlater : ∀ x ∈ Rl, u₀.round < x.round → cov x.key = true := by
    intro x hx _
    obtain ⟨Il, hIl⟩ := facts.gr.interpretedInputs_nonempty gv F S.hc.η_SG r la u
    obtain ⟨z, hz, rfl⟩ := (facts.gr.mem_readyView_iff Rl hRl Il hIl).mp hx
    exact seedQ2_readyInput_head_covers₆₄b facts S Hs Xb hf hHs hu Il hIl hz (cov _) (hcov' _)
  exact facts.gr.positive_of_conditions gv F S.hc.η_SG r ea la u Block.genesis u₀ Re hRe hu₀ hmax
    cov hcov' hcovU Wv hWv hclean Rl hRl hlater b hb

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.HealingLemmas

/-- Along the path `W` with the admissible fields `hf` and the weight bound `hfb`, if `0 < c`,
    `S.a c` is in the horizon, `lo ≤ S.a (c − 1)`, every member of the set for `S.a (c − 1)` has
    `h_max = Mh` in `W` before that time, every member of the set for `domain c p` has `h_max = Mh`
    and `h_j + 2 ≤ Mh` in `W` before it, and every member of the set for `S.a (c − 1) + Δ` is awake
    at `c − 1`, then for every member `v` of the set for `domain c p`, every outcome of the
    phase-`p` store grade of genesis at round `c` on `v`'s store in `W` before `domain c p` is
    `true`. -/
theorem relativeGrade_genesis_of_gateOffWindowOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hfb : BelowOneThirdOn S rho Hs)
    {Mh : Height} {c : Round} (hc : 0 < c) (p : Phase)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S c) ≤ rho.horizon)
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (c - 1)))
    (hprev : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (c - 1))),
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (c - 1))) u).st.h_max = Mh)
    (hfrontier : ∀ w ∈ Hs (M.domain S.E S.hc c p),
      (W (strictEventIndex rho (M.domain S.E S.hc c p)) w).st.h_max = Mh)
    (hgateOff : ∀ w ∈ Hs (M.domain S.E S.hc c p),
      (W (strictEventIndex rho (M.domain S.E S.hc c p)) w).st.h_j + 2 ≤ Mh)
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (c - 1)) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S (c - 1))) → M.awake_for_grade2 S u (W j u) (c - 1)) :
    ∀ v ∈ Hs (M.domain S.E S.hc c p),
      ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
        (W (strictEventIndex rho (M.domain S.E S.hc c p)) v).st c p
        Block.genesis ⇢ b → b = true := by
  have hΔ := S.E.Δ_pos
  have hdomHorP : M.domain S.E S.hc c p ≤ rho.horizon :=
    (facts.gr.domain_le_a S c p).trans hhor
  have hqr : c - 1 < c := Nat.sub_lt hc Nat.one_pos
  have hprevt : (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) + S.E.Δ ≤ M.domain S.E S.hc c p :=
    (facts.gr.action_delta_le_early S S.hc.R_ge_three hqr).trans (facts.gr.early_g2_lt_domain S c p).le
  have hmaj : Restated.GradeFormingMajorityOn M S rho W Hs (Hs (M.domain S.E S.hc c p)) c :=
    Restated.gradeFormingMajority_of_admissible_belowOneThirdOn facts S Hs Xb hf hHs hfb hc
      hprevt hdomHorP hpost hA
  have hwindow : Restated.RelativeCarrierWindowAtOn M S rho W
      (fun t => W (strictEventIndex rho t)) Hs (c - 1) p :=
    Restated.relativeCarrierWindowAt_of_gateOffOn facts S Hs Xb hf hHs hHsXb hc hpost hprev
      hfrontier hgateOff hdomHorP hA
  have hpred : c - 1 + 1 = c := Nat.sub_add_cancel (Nat.succ_le_iff.mpr hc)
  have horder : M.early S.E S.hc c p ≤ M.domain S.E S.hc c p := by
    have h1 := facts.gr.early_add_two_delta_le_domain S c p
    linarith
  unfold Restated.RelativeCarrierWindowAtOn at hwindow
  rw [hpred] at hwindow
  intro v hv b hb
  have hpositive : ∀ u ∈ Restated.honestRoundVotersOn M S rho W Hs (c - 1) ∩
        Hs (M.domain S.E S.hc c p),
      ∀ b' : Bool, M.positive
        (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc c p)) v).st.core))
        (W (strictEventIndex rho (M.domain S.E S.hc c p)) v).st.core.F
        S.hc.η_SG c (M.early S.E S.hc c p) (M.late S.E S.hc c p) u Block.genesis ⇢ b' →
        b' = true := by
    intro u hu
    obtain ⟨huV, huX⟩ := Finset.mem_inter.mp hu
    have huEarly : u ∈ Hs (M.early S.E S.hc c p) := hHs _ _ horder huX
    obtain ⟨na, hna, g, hg, A, hAsel⟩ := exists_actionSG₆₄b facts S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (c - 1))) u) (c - 1)
    obtain ⟨I, hI⟩ := facts.gr.interpretedInputs_nonempty
      (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc c p)) v).st.core))
      (W (strictEventIndex rho (M.domain S.E S.hc c p)) v).st.core.F
      S.hc.η_SG c (M.early S.E S.hc c p) u
    obtain ⟨y, hy, -, -, -⟩ := hwindow v hv u huV huEarly na hna g hg A hAsel I hI
    obtain ⟨Re, hRe⟩ := facts.gr.readyView_nonempty
      (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc c p)) v).st.core))
      (W (strictEventIndex rho (M.domain S.E S.hc c p)) v).st.core.F
      S.hc.η_SG c (M.early S.E S.hc c p) u
    exact Restated.seedQ2_honest_positive_genesisOn facts S Hs Xb hf hHs huX
      (facts.gr.q10_early_le_late S c p) Re hRe
      ⟨M.token y, (facts.gr.mem_readyView_iff Re hRe I hI).mpr ⟨y, hy, rfl⟩⟩
  have hopposing : ∀ u, M.opposing
        (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc c p)) v).st.core))
        (W (strictEventIndex rho (M.domain S.E S.hc c p)) v).st.core.F
        S.hc.η_SG c (M.early S.E S.hc c p) (M.late S.E S.hc c p) u Block.genesis ⇢ true →
      u ∈ (Finset.univ \ Hs (M.domain S.E S.hc c p)) ∪
        Restated.staleHistoricalVotersOn M S rho W Hs c := by
    intro u hu
    refine Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ u, fun huX => ?_⟩)
    exact Restated.seedQ2_honest_not_opposing_genesisOn facts S Hs Xb hf hHs huX hu
  exact Restated.phaseGrade_of_gradeFormingMajorityOn facts S rho W Hs (Hs (M.domain S.E S.hc c p)) c
    _ _ Block.genesis _ _ hmaj hpositive hopposing b hb

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.HealingLemmas

/-- Under the hypotheses of `relativeGrade_genesis_of_gateOffWindowOn`, for every member `v` of the
    set for `domain c p`, every outcome of the phase-`p` freeze root at round `c` on `v`'s store in
    `W` before `domain c p` is some block. -/
theorem storeRoot_isSome_of_gateOffWindowOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hfb : BelowOneThirdOn S rho Hs)
    {Mh : Height} {c : Round} (hc : 0 < c) (p : Phase)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S c) ≤ rho.horizon)
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (c - 1)))
    (hprev : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (c - 1))),
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (c - 1))) u).st.h_max = Mh)
    (hfrontier : ∀ w ∈ Hs (M.domain S.E S.hc c p),
      (W (strictEventIndex rho (M.domain S.E S.hc c p)) w).st.h_max = Mh)
    (hgateOff : ∀ w ∈ Hs (M.domain S.E S.hc c p),
      (W (strictEventIndex rho (M.domain S.E S.hc c p)) w).st.h_j + 2 ≤ Mh)
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (c - 1)) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S (c - 1))) → M.awake_for_grade2 S u (W j u) (c - 1)) :
    ∀ v ∈ Hs (M.domain S.E S.hc c p),
      ∀ fr : Option (Block V), Restated.Vocabulary.Internal.PhaseGrades.storeRoot M S.E S.hc
        (W (strictEventIndex rho (M.domain S.E S.hc c p)) v).st c p ⇢ fr →
      ∃ raw : Block V, fr = some raw := by
  have hgrades := Restated.relativeGrade_genesis_of_gateOffWindowOn facts S Hs Xb hf hHs hHsXb
    hfb hc p hhor hpost hprev hfrontier hgateOff hA
  intro v hv fr hfr
  obtain ⟨b, hb⟩ := facts.gr.gradeBool_nonempty S.E
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc c p)) v).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc c p)) v).st.core.F
    S.hc.η_SG c (M.early S.E S.hc c p) (M.late S.E S.hc c p) Block.genesis
  have hbt : b = true := hgrades v hv b hb
  have hmem : Block.genesis ∈ (M.gradeView (M.toHealing
      (W (strictEventIndex rho (M.domain S.E S.hc c p)) v).st.core)).T := by
    rw [facts.gr.Sts_gradeView_T]
    exact (Restated.genesis_mem_and_stamp_storeBeforeTimeOn facts S Hs Xb hf v
      (M.domain S.E S.hc c p) (M.domain S.E S.hc c p)).1
  obtain ⟨raw, hraw, -⟩ := facts.gr.q10_freeze_of_graded S.E _ _ S.hc.η_SG c
    (facts.gr.q10_early_le_late S c p) hmem b hb hbt fr hfr
  exact ⟨raw, hraw⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.HealingLemmas

/-- Under the hypotheses of `relativeGrade_genesis_of_gateOffWindowOn` at phase `g2`, for every
    member `v` of the set for `domain c g2` and every node state `n` of `v`'s round-`c` action read
    along `W`, every grade read that `n`'s contract can return at round `c` has its raw grade-2 test
    true. -/
theorem nodeRawG2_of_gateOffFrameOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hfb : BelowOneThirdOn S rho Hs)
    {Mh : Height} {c : Round} (hc : 0 < c)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S c) ≤ rho.horizon)
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (c - 1)))
    (hprev : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (c - 1))),
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (c - 1))) u).st.h_max = Mh)
    (hfrontier : ∀ w ∈ Hs (M.domain S.E S.hc c .g2),
      (W (strictEventIndex rho (M.domain S.E S.hc c .g2)) w).st.h_max = Mh)
    (hgateOff : ∀ w ∈ Hs (M.domain S.E S.hc c .g2),
      (W (strictEventIndex rho (M.domain S.E S.hc c .g2)) w).st.h_j + 2 ≤ Mh)
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (c - 1)) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S (c - 1))) → M.awake_for_grade2 S u (W j u) (c - 1)) :
    ∀ v ∈ Hs (M.domain S.E S.hc c .g2),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v) c,
      Restated.Vocabulary.Internal.PhaseGrades.nodeRawG2 M S n c := by
  have hroots := Restated.storeRoot_isSome_of_gateOffWindowOn facts S Hs Xb hf hHs hHsXb hfb
    hc .g2 hhor hpost hprev hfrontier hgateOff hA
  have hgat : lo ≤ M.domain S.E S.hc c .g2 :=
    hpost.trans ((le_add_of_nonneg_right S.E.Δ_pos.le).trans
      ((facts.gr.action_delta_le_early S S.hc.R_ge_three
        (Nat.sub_lt hc Nat.one_pos)).trans (facts.gr.early_le_domain S c)))
  intro v hv n hn g hg
  obtain ⟨fr, hfr⟩ := facts.gr.freezeRoot_nonempty S.E
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc c .g2)) v).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc c .g2)) v).st.core.F
    S.hc.η_SG c (M.early S.E S.hc c .g2) (M.late S.E S.hc c .g2)
  obtain ⟨raw, rfl⟩ := hroots v hv fr hfr
  have hframe := Restated.actionFrame_g2On facts S Hs Xb hf hc hhor hv hgat n hn (some raw) hfr
  rw [facts.nd.gradeContract_read_rawG2 n.cache S.E S.hc (M.toHealing n.st.core) c g hg, hframe]
  rfl

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Statements.Instantiation

/-- For every node state `n`, the voter's filtered block tree of `n`'s core store, its two vote
    views and the in-tree head computed from them can each return a value. -/
private theorem voterHead_outcome₆₄b (facts : Record.Facts M) (S : Setup V) (n : M.N) :
    ∃ (T : Finset (Block V)) (L L' : Finset (GoldfishVote V)) (H : Block V),
      M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T ∧
      M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L ∧
      M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' ∧
      M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
        (M.toHealing n.st.core) T L L' (n.st.core.s - 1) ⇢ H := by
  obtain ⟨T, hT⟩ := facts.fc.voter_filtered_block_tree_nonempty S.E n.st.core n.st.core.s
  obtain ⟨L, hL⟩ := facts.fc.voter_view_nonempty S.E
    (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s
  obtain ⟨L', hL'⟩ := facts.fc.voter_support_view_nonempty S.E
    (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s
  obtain ⟨H, hH⟩ := facts.fc.get_head_in_tree_with_layer_nonempty (M.gradeContract n.cache) S.E
    S.hc (M.toHealing n.st.core) T L L' (n.st.core.s - 1)
  exact ⟨T, L, L', H, hT, hL, hL', hH⟩

/-- Along the path `W` with the admissible fields `hf`, if the vote time `t` of round `q`'s last
    slot `s0` is in the horizon, `C` is an ancestor of every head a committee member of `s0` in the
    set for `t` voted at `s0`, `lo ≤ t`, and every such member passes the grade-1 awake test of
    `s0`'s round at its tick events at `t` (`hrun`), then the slot-`s0` votes of the set form a cone
    over `C`. -/
theorem seedBoundaryCone_of_belowHeadsOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {q : Round} {C : Block V}
    (hvoteHor : M.vote_time S.E
      ((M.opening_slot S.hc (q + 1)) - 1) ≤ rho.horizon)
    (hbelow : ∀ X : NamedBlock V,
      Restated.NamedHonestHeadOn M S rho W
        (fun _ => Hs (M.vote_time S.E ((M.opening_slot S.hc (q + 1)) - 1))) Xb
        ((M.opening_slot S.hc (q + 1)) - 1) X →
        Block.Preceq C X.erase)
    (hlo : lo ≤ M.vote_time S.E ((M.opening_slot S.hc (q + 1)) - 1))
    (hrun : ∀ w ∈ S.E.committee ((M.opening_slot S.hc (q + 1)) - 1),
      w ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc (q + 1)) - 1)) →
      ∀ j : Nat, rho.events[j]? = some
        (Record.Event.tick w (M.vote_time S.E ((M.opening_slot S.hc (q + 1)) - 1))) →
      M.awake_for_grade1 S w (W j w) (M.round_of S.hc ((M.opening_slot S.hc (q + 1)) - 1))) :
    Restated.NamedHonestVotesConeOn M S rho W Hs Xb ((M.opening_slot S.hc (q + 1)) - 1)
      (fun X => Block.Preceq C X) := by
  intro w hw hwcommittee
  have hs : 0 < (M.opening_slot S.hc (q + 1)) - 1 := by
    have hmul : 2 ≤ (M.opening_slot S.hc (q + 1)) := by
      rw [facts.gr.opening_slot_succ]
      exact le_trans S.hc.R_ge_two (Nat.le_add_left _ _)
    exact Nat.sub_pos_iff_lt.mpr ((by decide : 1 < 2).trans_le hmul)
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
    (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc (q + 1)) - 1))) w).st.core.toHealing
    (M.vote_time S.E ((M.opening_slot S.hc (q + 1)) - 1))
    (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc (q + 1)) - 1))) w).cache
  obtain ⟨T, L, L', Hd, hT, hL, hL', hHd⟩ := voterHead_outcome₆₄b facts S
    (M.mkNode
      (M.ns_setClock S.E
        (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc (q + 1)) - 1))) w).st
        (M.vote_time S.E ((M.opening_slot S.hc (q + 1)) - 1)))
      (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc (q + 1)) - 1))) w).record c)
  obtain ⟨H, hHerase, hHrun⟩ := Restated.seedVoteDutyHead_runBlockOn facts S Hs Xb hf (hHsXb _ hw)
    ((M.opening_slot S.hc (q + 1)) - 1) c hc T hT L hL L' hL' Hd hHd
  have hHemit := Restated.seedVoteDutyHead_emitsOn facts S Hs Xb hf hw hs hwcommittee hvoteHor
    hlo c hc (hrun w hwcommittee hw) T hT L hL L' hL' Hd hHd
  have hHemit' : Restated.Vocabulary.Execution.NamedRun.emits M S rho W w
      (.gfVote ⟨w, (M.opening_slot S.hc (q + 1)) - 1, H.erase.root⟩)
      (M.vote_time S.E ((M.opening_slot S.hc (q + 1)) - 1)) := by
    rw [hHerase]; exact hHemit
  have hHhead : Restated.NamedHonestHeadOn M S rho W
      (fun _ => Hs (M.vote_time S.E ((M.opening_slot S.hc (q + 1)) - 1))) Xb
      ((M.opening_slot S.hc (q + 1)) - 1) H :=
    ⟨w, hw, hwcommittee, hHrun, hHemit'⟩
  exact ⟨H, hbelow H hHhead, hHrun, hHemit'⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Statements.Instantiation

/-- Along the path `W` with the admissible fields `hf`, the honest committees `hcom` and the weight
    bound `hfb`: if `t_GST ≤ S.a q`, `t_GST` is at most the vote time of round `q`'s last slot `s0`,
    `s0`'s confirmation time is in the horizon, every head voted at `s0` by a committee member of
    the set for its vote time has height at least `Mh − 1` (`hheadThin`), some run block with a
    descendant of height at least `Mh − 1` descends from every round-`q` action block of the set for
    `S.a q` and is an ancestor of every such head (`hentry`), the next round's regime `hreg` holds,
    `lo ≤ S.a q`, `lo` is at most that vote time, and the awake hypotheses `hA` and `hrun` hold,
    then some named block is a round ceiling at `Mh` for round `q + 1`. -/
theorem exists_roundCeiling_of_seedBoundaryAdoptionOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hfb : BelowOneThirdOn S rho Hs)
    {Mh : Height} {q : Round}
    (hpostAction : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S q))
    (hpostBoundaryVote : S.E.t_GST ≤
      M.vote_time S.E ((M.opening_slot S.hc (q + 1)) - 1))
    (hboundaryConfirmationInHorizon :
      M.confirmation_time S.E
        ((M.opening_slot S.hc (q + 1)) - 1) ≤ rho.horizon)
    (hheadThin : ∀ X : NamedBlock V,
      Restated.NamedHonestHeadOn M S rho W
        (fun _ => Hs (M.vote_time S.E ((M.opening_slot S.hc (q + 1)) - 1))) Xb
        ((M.opening_slot S.hc (q + 1)) - 1) X →
      Mh - 1 ≤ (M.derive_named S.E S.cfg X).h)
    (hentry : ∃ C : NamedBlock V, Restated.RunBlockOn M S rho W Xb C ∧
      (∃ Wn : NamedBlock V, Restated.RunBlockOn M S rho W Xb Wn ∧
        Block.Preceq C.erase Wn.erase ∧ Mh - 1 ≤ (M.derive_named S.E S.cfg Wn).h) ∧
      (∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
        ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v) q,
        ∀ g, M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
            (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ g →
        ∀ B, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
            (M.round_of S.hc (M.toHealing n.st.core).s) g ⇢ B →
          Block.Preceq B C.erase) ∧
      ∀ X : NamedBlock V,
        Restated.NamedHonestHeadOn M S rho W
          (fun _ => Hs (M.vote_time S.E ((M.opening_slot S.hc (q + 1)) - 1))) Xb
          ((M.opening_slot S.hc (q + 1)) - 1) X →
        Block.Preceq C.erase X.erase)
    (hreg : Restated.RoundCeilingNextRegimeAtOn M S rho (fun t => W (strictEventIndex rho t)) Hs Mh q)
    (hloAction : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S q))
    (hlo : lo ≤ M.vote_time S.E ((M.opening_slot S.hc (q + 1)) - 1))
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S q)) → M.awake_for_grade2 S u (W j u) q)
    (hrun : ∀ w ∈ S.E.committee ((M.opening_slot S.hc (q + 1)) - 1),
      w ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc (q + 1)) - 1)) →
      ∀ j : Nat, rho.events[j]? = some
        (Record.Event.tick w (M.vote_time S.E ((M.opening_slot S.hc (q + 1)) - 1))) →
      M.awake_for_grade1 S w (W j w) (M.round_of S.hc ((M.opening_slot S.hc (q + 1)) - 1))) :
    ∃ B : NamedBlock V,
      Restated.RoundCeilingAtOn M S rho W (fun t => W (strictEventIndex rho t)) Hs Xb Mh (q + 1) B := by
  obtain ⟨C, hCrun, ⟨Wn, hWrun, hCW, hWthin⟩, hcarriers, hbelow⟩ := hentry
  have hvoteHor : M.vote_time S.E
      ((M.opening_slot S.hc (q + 1)) - 1) ≤ rho.horizon :=
    (facts.sch.Protocol_vote_time_le_confirmation_time S.E _).trans
      hboundaryConfirmationInHorizon
  obtain ⟨B, hB, _⟩ := Restated.roundCeiling_base_of_carrierFrontierOn facts S Hs Xb hf hHs
    hHsXb hcom hfb hpostAction hpostBoundaryVote hboundaryConfirmationInHorizon hCrun hWrun
    hCW hWthin hcarriers
    (Restated.seedBoundaryCone_of_belowHeadsOn facts S Hs Xb hf hHsXb hvoteHor
      hbelow hlo hrun)
    hheadThin hreg hloAction hlo hA
  exact ⟨B, hB⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Statements.Instantiation

/-- Along the path `W` with the admissible fields `hf` and the weight bound `hfb`: if
    `gstLagged S ≤ S.a base`, `base + 1 ≤ q`, `S.a (q + 2)` is in the horizon, every member of the
    set for every time `read` from `S.a base` to `S.a (q + 2)` has `h_j + 2 ≤ Mh` and `h_max = Mh`
    in `W` before `read` (`hwindow`), `lo ≤ S.a base`, and the grade-2 awake hypotheses `hA` and
    `hAbase` hold, then the regime of round `q` holds at `Mh`: the bounds on `t_GST` and on the
    horizon at round `q`'s duties, the heights of the members of the set for `S.a q`, round `q`
    ready for grading, its grade-2 selections not interfering with those members' stores, and the
    next-round regime. -/
theorem seedRoundRegime_of_windowOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hfb : BelowOneThirdOn S rho Hs)
    {Mh : Height} {base q : Round}
    (hpostBase : gstLagged S ≤ (Restated.Vocabulary.Execution.Setup.a M S base))
    (hbaseq : base + 1 ≤ q)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S (q + 2)) ≤ rho.horizon)
    (hwindow : ∀ read : Time, (Restated.Vocabulary.Execution.Setup.a M S base) ≤ read →
      read ≤ (Restated.Vocabulary.Execution.Setup.a M S (q + 2)) →
      ∀ w ∈ Hs read,
        (W (strictEventIndex rho read) w).st.h_j + 2 ≤ Mh ∧
          (W (strictEventIndex rho read) w).st.h_max = Mh)
    (hloBase : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S base))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k)
    (hAbase : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S base) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S base)) → M.awake_for_grade2 S u (W j u) base) :
    S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S q) ∧
    S.E.t_GST ≤ M.proposal_time S.E ((M.opening_slot S.hc q)) ∧
    S.E.t_GST ≤ M.vote_time S.E ((M.opening_slot S.hc (q + 1)) - 1) ∧
    M.confirmation_time S.E ((M.opening_slot S.hc q)) ≤ rho.horizon ∧
    M.confirmation_time S.E ((M.opening_slot S.hc (q + 1)) - 1) ≤ rho.horizon ∧
    (∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v).st.h_max = Mh) ∧
    (∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v).st.h_j + 2 ≤ Mh) ∧
    Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho q ∧
    (∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)), ∀ Q : Block V,
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) u) q,
      Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n q ⇢ some Q →
      ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
        Restated.Vocabulary.Proofs.HealingSurface.FinalityFilterNoninterferenceAtRead M S rho w
          (Restated.Vocabulary.Execution.Setup.a M S q)
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q))) Q) ∧
    Restated.RoundCeilingNextRegimeAtOn M S rho (fun t => W (strictEventIndex rho t)) Hs Mh q := by
  have hR : 2 ≤ S.hc.R := S.hc.R_ge_two
  have hΔ := S.E.Δ_pos
  have hqpos : 0 < q := Nat.lt_of_lt_of_le (Nat.succ_pos base) hbaseq
  have hqPredAdd : q - 1 + 1 = q :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt hqpos)
  have hbasePred : base ≤ q - 1 := Nat.le_sub_one_of_lt hbaseq
  have hpostPredLagged : gstLagged S ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) :=
    hpostBase.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hbasePred)
  have hpostActionLagged : gstLagged S ≤ (Restated.Vocabulary.Execution.Setup.a M S q) :=
    hpostBase.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S ((Nat.le_succ base).trans hbaseq))
  have hpostPred : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) :=
    (t_GST_le_gstLagged S).trans hpostPredLagged
  have hpostAction : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S q) :=
    (t_GST_le_gstLagged S).trans hpostActionLagged
  have hloPred : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) :=
    hloBase.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hbasePred)
  have hsucc : (M.opening_slot S.hc (q + 1)) =
      (M.opening_slot S.hc q) + S.hc.R := facts.gr.opening_slot_succ_eq S.hc q
  have hopenBoundary : (M.opening_slot S.hc q) ≤
      (M.opening_slot S.hc (q + 1)) - 1 := by
    rw [hsucc]
    exact Nat.le_sub_one_of_lt (Nat.lt_add_of_pos_right (Nat.lt_of_lt_of_le Nat.zero_lt_two hR))
  have hpostProposal : S.E.t_GST ≤
      M.proposal_time S.E ((M.opening_slot S.hc q)) := by
    refine hpostPred.trans ?_
    refine (le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans ?_
    exact Restated.Vocabulary.Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt facts S
      (by simpa only [hqPredAdd] using Nat.sub_lt hqpos Nat.zero_lt_one)
  have hpostBoundaryVote : S.E.t_GST ≤
      M.vote_time S.E ((M.opening_slot S.hc (q + 1)) - 1) := by
    refine hpostProposal.trans ?_
    refine (le_of_lt (facts.sch.proposal_time_lt_vote_time S.E _)).trans ?_
    exact facts.sch.vote_time_mono_slots S.E hopenBoundary
  have hactionHor : (Restated.Vocabulary.Execution.Setup.a M S q) ≤ rho.horizon :=
    (Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_add_right q 2)).trans hhor
  have hopeningHor : M.confirmation_time S.E
      ((M.opening_slot S.hc q)) ≤ rho.horizon := by
    rw [Restated.confirmation_time_opening_slot facts S q]
    exact hactionHor
  have hnextActionHor : (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) ≤ rho.horizon :=
    (Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.add_le_add_left (by decide : 1 ≤ 2) q)).trans hhor
  have hboundaryHor : M.confirmation_time S.E
      ((M.opening_slot S.hc (q + 1)) - 1) ≤ rho.horizon := by
    refine (Restated.confirmationTime_mono_l58 facts S.E (Nat.sub_le _ 1)).trans ?_
    rw [Restated.confirmation_time_opening_slot facts S (q + 1)]
    exact hnextActionHor
  have hbaseAction : (Restated.Vocabulary.Execution.Setup.a M S base) ≤ (Restated.Vocabulary.Execution.Setup.a M S q) :=
    Restated.Vocabulary.Proofs.Assembly.a_mono facts S ((Nat.le_succ base).trans hbaseq)
  have hqq2 : (Restated.Vocabulary.Execution.Setup.a M S q) ≤ (Restated.Vocabulary.Execution.Setup.a M S (q + 2)) :=
    Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_add_right q 2)
  have hfrontier : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v).st.h_max = Mh :=
    fun v hv => (hwindow ((Restated.Vocabulary.Execution.Setup.a M S q)) hbaseAction hqq2 v hv).2
  have hgate : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v).st.h_j + 2 ≤ Mh :=
    fun v hv => (hwindow ((Restated.Vocabulary.Execution.Setup.a M S q)) hbaseAction hqq2 v hv).1
  have hprevFrontier : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1))),
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) v).st.h_max = Mh :=
    fun v hv =>
      (hwindow ((Restated.Vocabulary.Execution.Setup.a M S (q - 1)))
        (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hbasePred)
        (Restated.Vocabulary.Proofs.Assembly.a_mono facts S ((Nat.sub_le q 1).trans (Nat.le_add_right q 2)))
        v hv).2
  have hready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho q := by
    refine Restated.Vocabulary.Proofs.HealingSurface.gradeRoundReady_of_action_horizon facts S ?_ (le_refl q) hactionHor
    have h := Restated.Vocabulary.Proofs.HealingSurface.gstLagged_le_Γ_neg1_succ facts S (q - 1) hpostPredLagged
    rwa [hqPredAdd] at h
  have hdomainHor : M.domain S.E S.hc q .g2 ≤ rho.horizon :=
    (facts.gr.domain_le_a S q .g2).trans hactionHor
  have hprevt : (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) + S.E.Δ ≤ M.domain S.E S.hc q .g2 :=
    (facts.gr.action_delta_le_early S S.hc.R_ge_three
      (Nat.sub_lt hqpos Nat.one_pos)).trans (facts.gr.early_le_domain S q)
  have hbaseDomain : (Restated.Vocabulary.Execution.Setup.a M S base) ≤ M.domain S.E S.hc q .g2 :=
    (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hbasePred).trans ((le_add_of_nonneg_right hΔ.le).trans hprevt)
  have hdomainEnd : M.domain S.E S.hc q .g2 ≤ (Restated.Vocabulary.Execution.Setup.a M S (q + 2)) :=
    (facts.gr.domain_le_a S q .g2).trans hqq2
  have hfrontierD : ∀ w ∈ Hs (M.domain S.E S.hc q .g2),
      (W (strictEventIndex rho (M.domain S.E S.hc q .g2)) w).st.h_max = Mh :=
    fun w hw => (hwindow _ hbaseDomain hdomainEnd w hw).2
  have hgateD : ∀ w ∈ Hs (M.domain S.E S.hc q .g2),
      (W (strictEventIndex rho (M.domain S.E S.hc q .g2)) w).st.h_j + 2 ≤ Mh :=
    fun w hw => (hwindow _ hbaseDomain hdomainEnd w hw).1
  -- The grade-2 awake test at round `q - 1`: `hAbase` when `q - 1 = base`, otherwise `hA (q - 1)`.
  have hAprev : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1)) + S.E.Δ), ∀ j : Nat,
      rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) →
      M.awake_for_grade2 S u (W j u) (q - 1) := by
    rcases eq_or_lt_of_le hbasePred with hb | hb
    · rw [← hb]
      exact hAbase
    · exact hA (q - 1) (Restated.lo_le_early_g2_sub_delta_of_action_lt facts S hloBase hb)
  have hrel : Restated.RelativeCarrierWindowAtOn M S rho W
      (fun t => W (strictEventIndex rho t)) Hs (q - 1) .g2 :=
    Restated.relativeCarrierWindowAt_of_gateOffOn facts S Hs Xb hf hHs hHsXb hqpos hloPred
      hprevFrontier hfrontierD hgateD hdomainHor hAprev
  have hmajority : Restated.GradeFormingMajorityOn M S rho W Hs (Hs (M.domain S.E S.hc q .g2)) q :=
    Restated.gradeFormingMajority_of_admissible_belowOneThirdOn facts S Hs Xb hf hHs hfb hqpos
      hprevt hdomainHor hloPred hAprev
  have hsettled := Restated.selectedG2SettledAt_of_gateOffOn facts S Hs Xb
    (Hs (M.domain S.E S.hc q .g2)) hf hHs hHsXb hqpos hrel hmajority (subset_refl _) hloPred
    hprevFrontier hfrontier hgate hactionHor
  have hlastSlot : Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S (q + 1) - 1 ≤
      (M.opening_slot S.hc (q + 2)) := by
    show M.opening_slot S.hc (q + 1 + 1) - 1 - 1 ≤ M.opening_slot S.hc (q + 2)
    exact (Nat.sub_le _ 1).trans (Nat.sub_le _ 1)
  have hlastLe : M.confirmation_time S.E
      (Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S (q + 1) - 1) ≤
        (Restated.Vocabulary.Execution.Setup.a M S (q + 2)) :=
    (Restated.confirmationTime_mono_l58 facts S.E hlastSlot).trans
      (Restated.confirmation_time_opening_slot facts S (q + 2)).le
  have hnext : Restated.RoundCeilingNextRegimeAtOn M S rho
      (fun t => W (strictEventIndex rho t)) Hs Mh q :=
    Restated.roundCeilingNextRegime_of_windowOn facts S Hs hpostAction (hlastLe.trans hhor)
      (fun read hlo' hhi w hw => hwindow read (hbaseAction.trans hlo') (hhi.trans hlastLe) w hw)
  exact ⟨hpostAction, hpostProposal, hpostBoundaryVote, hopeningHor, hboundaryHor, hfrontier, hgate,
    hready, hsettled, hnext⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Statements.Instantiation

/-- Along the path `W` with the admissible fields `hf`, the honest committees `hcom` and the weight
    bound `hfb`, under the hypotheses of `seedRoundRegime_of_windowOn` from `base` to `q + 2` and
    the conditions `hheadThin` and `hentry` on the heads voted at round `q`'s last slot, some named
    block is a round ceiling at `Mh` for round `q + 1`. -/
theorem exists_roundCeiling_of_window_of_adoptionOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hfb : BelowOneThirdOn S rho Hs)
    {Mh : Height} {base q : Round}
    (hpostBase : gstLagged S ≤ (Restated.Vocabulary.Execution.Setup.a M S base))
    (hbaseq : base + 1 ≤ q)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S (q + 2)) ≤ rho.horizon)
    (hwindow : ∀ read : Time, (Restated.Vocabulary.Execution.Setup.a M S base) ≤ read →
      read ≤ (Restated.Vocabulary.Execution.Setup.a M S (q + 2)) →
      ∀ w ∈ Hs read,
        (W (strictEventIndex rho read) w).st.h_j + 2 ≤ Mh ∧
          (W (strictEventIndex rho read) w).st.h_max = Mh)
    (hheadThin : ∀ X : NamedBlock V,
      Restated.NamedHonestHeadOn M S rho W
        (fun _ => Hs (M.vote_time S.E ((M.opening_slot S.hc (q + 1)) - 1))) Xb
        ((M.opening_slot S.hc (q + 1)) - 1) X →
      Mh - 1 ≤ (M.derive_named S.E S.cfg X).h)
    (hentry : ∃ C : NamedBlock V, Restated.RunBlockOn M S rho W Xb C ∧
      (∃ Wn : NamedBlock V, Restated.RunBlockOn M S rho W Xb Wn ∧
        Block.Preceq C.erase Wn.erase ∧ Mh - 1 ≤ (M.derive_named S.E S.cfg Wn).h) ∧
      (∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
        ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v) q,
        ∀ g, M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
            (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ g →
        ∀ B, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
            (M.round_of S.hc (M.toHealing n.st.core).s) g ⇢ B →
          Block.Preceq B C.erase) ∧
      ∀ X : NamedBlock V,
        Restated.NamedHonestHeadOn M S rho W
          (fun _ => Hs (M.vote_time S.E ((M.opening_slot S.hc (q + 1)) - 1))) Xb
          ((M.opening_slot S.hc (q + 1)) - 1) X →
        Block.Preceq C.erase X.erase)
    (hloBase : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S base))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k)
    (hAbase : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S base) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S base)) → M.awake_for_grade2 S u (W j u) base) :
    ∃ B : NamedBlock V,
      Restated.RoundCeilingAtOn M S rho W (fun t => W (strictEventIndex rho t)) Hs Xb Mh (q + 1) B := by
  obtain ⟨hpostAction, -, hpostBoundaryVote, -, hboundaryHor, -, -, -, -, hnext⟩ :=
    Restated.seedRoundRegime_of_windowOn facts S Hs Xb hf hHs hHsXb hfb hpostBase hbaseq hhor
      hwindow hloBase hA hAbase
  have hqpos : 0 < q := Nat.lt_of_lt_of_le (Nat.succ_pos base) hbaseq
  have hqPredAdd : q - 1 + 1 = q := Nat.sub_add_cancel (Nat.succ_le_of_lt hqpos)
  have hbasePred : base ≤ q - 1 := Nat.le_sub_one_of_lt hbaseq
  have hloPred : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) :=
    hloBase.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hbasePred)
  have hloAction : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S q) :=
    hloBase.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S ((Nat.le_succ base).trans hbaseq))
  have hopenBoundary : (M.opening_slot S.hc q) ≤ (M.opening_slot S.hc (q + 1)) - 1 := by
    rw [facts.gr.opening_slot_succ_eq S.hc q]
    exact Nat.le_sub_one_of_lt
      (Nat.lt_add_of_pos_right (Nat.lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two))
  have hloVote : lo ≤ M.vote_time S.E ((M.opening_slot S.hc (q + 1)) - 1) := by
    refine hloPred.trans ?_
    refine (le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans ?_
    refine (Restated.Vocabulary.Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt facts S
      (by simpa only [hqPredAdd] using Nat.sub_lt hqpos Nat.zero_lt_one)).trans ?_
    refine (le_of_lt (facts.sch.proposal_time_lt_vote_time S.E _)).trans ?_
    exact facts.sch.vote_time_mono_slots S.E hopenBoundary
  -- Every committee member of round `q`'s last slot passes the grade-1 awake test at its vote
  -- ticks.
  have hrunLast : ∀ w ∈ S.E.committee ((M.opening_slot S.hc (q + 1)) - 1),
      w ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc (q + 1)) - 1)) →
      ∀ j : Nat, rho.events[j]? = some
        (Record.Event.tick w (M.vote_time S.E ((M.opening_slot S.hc (q + 1)) - 1))) →
      M.awake_for_grade1 S w (W j w)
        (M.round_of S.hc ((M.opening_slot S.hc (q + 1)) - 1)) := by
    intro w _ hw j hj
    have hround : M.round_of S.hc ((M.opening_slot S.hc (q + 1)) - 1) = q := by
      have hR : 3 ≤ S.hc.R := S.hc.R_ge_three
      have hsucc : M.opening_slot S.hc (q + 1) = M.opening_slot S.hc q + S.hc.R :=
        facts.gr.opening_slot_succ_eq S.hc q
      apply facts.gr.round_of_eq_of_opening_succ_le_of_lt_next_opening S.hc
      · rw [hsucc]; exact Nat.le_sub_one_of_lt (Nat.add_lt_add_left (by omega) _)
      · rw [hsucc]; exact Nat.sub_lt (by omega) Nat.one_pos
    have hwin : lo ≤ M.early S.E S.hc
        (M.round_of S.hc ((M.opening_slot S.hc (q + 1)) - 1)) .g1 - S.E.Δ := by
      rw [hround]
      have h1 := Restated.lo_le_early_g2_sub_delta_of_action_lt facts S hloBase hbaseq
      have h2 := facts.gr.q10_early_g2_le_early_g1 S q
      linarith
    exact hf.awake_g1 _ _ j _ (Or.inr rfl) hj hw hwin
  exact Restated.exists_roundCeiling_of_seedBoundaryAdoptionOn facts S Hs Xb hf hHs hHsXb hcom
    hfb hpostAction hpostBoundaryVote hboundaryHor hheadThin hentry hnext hloAction hloVote
    (hA q (Restated.lo_le_early_g2_sub_delta_of_action_lt facts S hloBase hbaseq)) hrunLast

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Statements.Instantiation

/-- Along the path `W` with the admissible fields `hf`, the honest committees `hcom` and the weight
    bound `hfb`: if every member of the set for each time from `S.a base` on has `h_j + 2 ≤ Mh` and
    `h_max = Mh` (`hwindow`), round `first` has a round ceiling at `Mh` on `C` (`hbase`),
    `base + 1 ≤ first`, the bounds on `lo` hold and the awake hypotheses `hA` and `hAbase` hold,
    then every round from `first` to `last` has a round ceiling at `Mh` on a descendant of `C`. -/
theorem roundCeiling_through_of_windowOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hfb : BelowOneThirdOn S rho Hs)
    {Mh : Height} {base first last : Round} {C : NamedBlock V}
    (hpostBase : gstLagged S ≤ (Restated.Vocabulary.Execution.Setup.a M S base))
    (hbaseFirst : base + 1 ≤ first)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S (last + 2)) ≤ rho.horizon)
    (hwindow : ∀ read : Time, (Restated.Vocabulary.Execution.Setup.a M S base) ≤ read →
      read ≤ (Restated.Vocabulary.Execution.Setup.a M S (last + 1)) →
      ∀ w ∈ Hs read,
        (W (strictEventIndex rho read) w).st.h_j + 2 ≤ Mh ∧
          (W (strictEventIndex rho read) w).st.h_max = Mh)
    (hbase : Restated.RoundCeilingAtOn M S rho W (fun t => W (strictEventIndex rho t)) Hs Xb Mh first C)
    (hloBase : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S base))
    (hlo : lo ≤ M.vote_time S.E ((M.opening_slot S.hc first) - 1))
    (hloOpen : lo ≤ M.opening S.E S.hc (first - S.hc.η_SG))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k)
    (hAbase : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S base) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S base)) → M.awake_for_grade2 S u (W j u) base) :
    ∀ k : Round, first ≤ k → k ≤ last →
      ∃ B : NamedBlock V,
        Restated.RoundCeilingAtOn M S rho W (fun t => W (strictEventIndex rho t)) Hs Xb Mh k B ∧
        Block.Preceq C.erase B.erase := by
  intro k hfirstk hklast
  exact Restated.roundCeiling_through_or_rebaseOn facts S Hs Xb hf hHs hHsXb hcom hfb
    (last := last) hbase
    (fun (j : Round) (hjlo : first ≤ j) (hjhi : j < last) =>
      (Restated.seedRoundRegime_of_windowOn facts S Hs Xb hf hHs hHsXb hfb hpostBase
        (hbaseFirst.trans hjlo)
        ((Restated.Vocabulary.Proofs.Assembly.a_mono facts S
          (Nat.add_le_add_right (Nat.le_of_lt hjhi) 2)).trans hhor)
        (fun read hlo' hhi w hw => hwindow read hlo'
          (hhi.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S
            (Nat.add_le_add_right (Nat.succ_le_of_lt hjhi) 1))) w hw) hloBase hA hAbase).2.2.2.2.2.2.2.2.2)
    hlo hloOpen hA k hfirstk hklast

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- Along the path `W` with the admissible fields `hf`: if `0 < r`, the carrier window `hwindow` and
    the grade-forming majority `hmajority` over `X` hold, `X` is inside the set for `domain r g1`,
    and every round-`(r − 1)` action carrier of a member of the set for `S.a (r − 1)` does not
    interfere with the store of any member of the set for `S.a r` (`hquiet`), then every block `B`
    for which every outcome of the grade-1 store grade, on the store in `W` before `domain r g1` of
    a member of the set for `domain r g1`, is `true` does not interfere with the store of any member
    of the set for `S.a r` in `W` before `S.a r`. -/
theorem namedLiveG1SettledAt_of_previousActionCarriersQuietOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb X : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {r : Round} (hr : 0 < r)
    (hwindow : Restated.RelativeCarrierWindowAtOn M S rho W
      (fun t => W (strictEventIndex rho t)) Hs (r - 1) .g1)
    (hmajority : Restated.GradeFormingMajorityOn M S rho W Hs X r)
    (hX : X ⊆ Hs (M.domain S.E S.hc r .g1))
    (hquiet : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (r - 1))),
      ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r - 1))) u) (r - 1),
        ∀ A2 : Option (Block V), M.grade2_block_with (M.gradeContract n.cache) S.E S.hc
            (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ A2 →
        ∀ A : Block V, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc
            (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s) A2 ⇢ A →
          Restated.Vocabulary.Proofs.HealingSurface.FinalityFilterNoninterferenceAtRead M S rho w
            (Restated.Vocabulary.Execution.Setup.a M S r)
            (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r))) A) :
    ∀ u ∈ Hs (M.domain S.E S.hc r .g1), ∀ B : Block V,
      (∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
        (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) u).st r .g1 B ⇢ b → b = true) →
      ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)),
        Restated.Vocabulary.Proofs.HealingSurface.FinalityFilterNoninterferenceAtRead M S rho w
          (Restated.Vocabulary.Execution.Setup.a M S r)
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r))) B := by
  intro u hu B hgrade w hw
  have hpred : r - 1 + 1 = r := Nat.sub_add_cancel hr
  obtain ⟨b0, hb0⟩ := facts.gr.gradeBool_nonempty S.E
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) u).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) u).st.core.F
    S.hc.η_SG r (M.early S.E S.hc r .g1) (M.late S.E S.hc r .g1) B
  have hb0t : b0 = true := hgrade b0 hb0
  subst hb0t
  have hgrade' : M.gradeBool S.E
      (M.gradeView (M.toHealing
        (W (strictEventIndex rho (M.domain S.E S.hc ((r - 1) + 1) .g1)) u).st.core))
      (W (strictEventIndex rho (M.domain S.E S.hc ((r - 1) + 1) .g1)) u).st.core.F
      S.hc.η_SG ((r - 1) + 1) (M.early S.E S.hc ((r - 1) + 1) .g1)
      (M.late S.E S.hc ((r - 1) + 1) .g1) B ⇢ true := by
    rw [hpred]
    exact hb0
  have hmajority' : Restated.GradeFormingMajorityOn M S rho W Hs X (r - 1 + 1) := by
    rw [hpred]
    exact hmajority
  have hX' : X ⊆ Hs (M.domain S.E S.hc (r - 1 + 1) .g1) := by
    rw [hpred]
    exact hX
  have hu' : u ∈ Hs (M.domain S.E S.hc (r - 1 + 1) .g1) := by
    rw [hpred]
    exact hu
  obtain ⟨v, hv, hBcarrier⟩ := Restated.relativeGrade_has_roundCarrierOn facts
    S Hs Xb X hf hHs hwindow hmajority' hX' hu' hgrade'
  have hvHon : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (r - 1))) :=
    ((Restated.honestRoundVoters_iffOn facts S rho W hf.onePath Hs v (r - 1)).mp hv).1
  obtain ⟨nr, hnr, A2, hA2, Bk, hBk⟩ := exists_actionSG₆₄b facts S
    (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r - 1))) v) (r - 1)
  exact Restated.ancestorOn facts S Hs Xb hf (hBcarrier nr hnr A2 hA2 Bk hBk)
    (hquiet v hvHon w hw nr hnr A2 hA2 Bk hBk)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- Along the path `W` with the admissible fields `hf` and the weight bound `hfb`: if `0 < r`,
    `lo ≤ S.a (r − 1)`, every member of the set for `S.a (r − 1)` has `h_max = Mh`, every member of
    the sets for `S.a r` and for `domain r g1` has `h_max = Mh` and `h_j + 2 ≤ Mh`, each in `W`
    before that time, `S.a r` is in the horizon, and every member of the set for `S.a (r − 1) + Δ`
    is awake at `r − 1`, then every block `B` for which every outcome of the grade-1 store grade, on
    the store in `W` before `domain r g1` of a member of the set for `domain r g1`, is `true` does
    not interfere with the store of any member of the set for `S.a r` in `W` before `S.a r`. -/
theorem namedLiveG1SettledAt_of_gateOffOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hfb : BelowOneThirdOn S rho Hs) {r : Round} (hr : 0 < r)
    {Mh : Height} (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (r - 1)))
    (hprev : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (r - 1))),
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r - 1))) u).st.h_max = Mh)
    (hfrontier : ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)),
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) w).st.h_max = Mh)
    (hgateOff : ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)),
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) w).st.h_j + 2 ≤ Mh)
    (hfrontierG1 : ∀ w ∈ Hs (M.domain S.E S.hc r .g1),
      (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st.h_max = Mh)
    (hgateOffG1 : ∀ w ∈ Hs (M.domain S.E S.hc r .g1),
      (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st.h_j + 2 ≤ Mh)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon)
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (r - 1)) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S (r - 1))) → M.awake_for_grade2 S u (W j u) (r - 1)) :
    ∀ u ∈ Hs (M.domain S.E S.hc r .g1), ∀ B : Block V,
      (∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
        (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) u).st r .g1 B ⇢ b → b = true) →
      ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)),
        Restated.Vocabulary.Proofs.HealingSurface.FinalityFilterNoninterferenceAtRead M S rho w
          (Restated.Vocabulary.Execution.Setup.a M S r)
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r))) B := by
  have hquiet := Restated.previousActionCarriersQuietAt_of_gateOffOn facts S Hs Xb hf hHs hHsXb
    hf.slashableBound hr hpost hprev hfrontier hgateOff hhor
  have hG1Hor : M.domain S.E S.hc r .g1 ≤ rho.horizon :=
    (facts.gr.domain_le_a S r .g1).trans hhor
  have hwindow : Restated.RelativeCarrierWindowAtOn M S rho W
      (fun t => W (strictEventIndex rho t)) Hs (r - 1) .g1 :=
    Restated.relativeCarrierWindowAt_of_gateOffOn facts S Hs Xb hf hHs hHsXb hr hpost hprev
      hfrontierG1 hgateOffG1 hG1Hor hA
  have hprevt : (Restated.Vocabulary.Execution.Setup.a M S (r - 1)) + S.E.Δ ≤ M.domain S.E S.hc r .g1 :=
    (facts.gr.action_delta_le_early S S.hc.R_ge_three
      (Nat.sub_lt hr Nat.one_pos)).trans (facts.gr.early_g2_lt_domain S r .g1).le
  have hmajority : Restated.GradeFormingMajorityOn M S rho W Hs (Hs (M.domain S.E S.hc r .g1)) r :=
    Restated.gradeFormingMajority_of_admissible_belowOneThirdOn facts S Hs Xb hf hHs hfb hr
      hprevt hG1Hor hpost hA
  exact Restated.namedLiveG1SettledAt_of_previousActionCarriersQuietOn facts
    S Hs Xb (Hs (M.domain S.E S.hc r .g1)) hf hHs hr hwindow hmajority (subset_refl _) hquiet

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Statements.Instantiation

/-- For any worlds `Wt` before each time: if `t_GST ≤ S.a c`, `S.a (c + 2)` is in the horizon and
    the frame `hframe` holds from `c` to `c + 2`, then the next-round regime read from `Wt` holds at
    `Mh` and `c`. -/
theorem regime_of_gateOffFrameOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} {Wt : Time → V → M.N} (Hs : Int → Finset V)
    {Mh : Height} {c : Round}
    (hpostAction : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S c))
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S (c + 2)) ≤ rho.horizon)
    (hframe : Restated.NamedGateOffFrameAtOn M S rho Wt Hs Mh c (c + 2)) :
    Restated.RoundCeilingNextRegimeAtOn M S rho Wt Hs Mh c := by
  have hlastSlot : Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S (c + 1) - 1 ≤
      (M.opening_slot S.hc (c + 2)) := by
    show M.opening_slot S.hc (c + 1 + 1) - 1 - 1 ≤ M.opening_slot S.hc (c + 2)
    exact (Nat.sub_le _ 1).trans (Nat.sub_le _ 1)
  have hlastLe : M.confirmation_time S.E
      (Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S (c + 1) - 1) ≤
        (Restated.Vocabulary.Execution.Setup.a M S (c + 2)) :=
    (Restated.confirmationTime_mono_l58 facts S.E hlastSlot).trans
      (Restated.confirmation_time_opening_slot facts S (c + 2)).le
  exact Restated.roundCeilingNextRegime_of_windowOn facts S Hs hpostAction (hlastLe.trans hhor)
    (fun read hlo hhi w hw => hframe read hlo (hhi.trans hlastLe) w hw)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Statements.Instantiation

/-- Along the path `W` with the admissible fields `hf`, if the slot-`d` votes of the set form a cone
    over `C` (`hcone`), then every head a committee member of `d` in the set for `vote_time d` voted
    descends from `C`. -/
theorem honestHead_preceq_of_coneOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {d : Slot} {C : Block V}
    (hcone : Restated.NamedHonestVotesConeOn M S rho W Hs Xb d (fun X => Block.Preceq C X)) :
    ∀ X : Block V, Restated.HonestHeadOn M S rho W (fun _ => Hs (M.vote_time S.E d)) Xb d X →
      Block.Preceq C X := by
  intro X hX
  obtain ⟨x, hxVote, hxCommittee, ⟨Xn, hXerase, hXrun⟩, hXemit⟩ := hX
  obtain ⟨Y, hCY, hYrun, hYemit⟩ := hcone x hxVote hxCommittee
  have hvote : (⟨x, d, X.root⟩ : GoldfishVote V) =
      ⟨x, d, Y.erase.root⟩ :=
    Restated.emits_gfVote_uniqueOn facts S Hs Xb hf hXemit hYemit rfl
  have hXY : Xn.erase = Y.erase :=
    Restated.runBlock_eq_of_root_eqOn facts W Xb hf.rootCollisionFree hXrun hYrun
      (by simpa only [hXerase] using congrArg GoldfishVote.head hvote)
  rw [← hXerase, hXY]
  exact hCY

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Statements.Instantiation

/-- Along the path `W` with the admissible fields `hf`: if `0 < d`, `vote_time d` is in the horizon,
    every member of the set for `vote_time d` has `h_max = Mh` at its vote-duty store (`hfrontier`)
    and every head its vote-duty head computation can return is a run block of height at least that
    `h_max − 1` (`hband`), `lo ≤ vote_time d`, and every committee member of `d` in that set passes
    the grade-1 awake test at its tick events at `vote_time d` (`hrun`), then every head a committee
    member of `d` in that set voted has height at least `Mh − 1`. -/
theorem headThin_of_bandOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {Mh : Height} {d : Slot} (hd : 0 < d)
    (hhor : M.vote_time S.E d ≤ rho.horizon)
    (hfrontier : ∀ w ∈ Hs (M.vote_time S.E d),
      (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core d).h_max = Mh)
    (hband : ∀ w ∈ Hs (M.vote_time S.E d),
      ∀ c : M.Cache, M.onPhaseTick S.E S.hc
          (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core.toHealing
          (M.vote_time S.E d)
          (W (strictEventIndex rho (M.vote_time S.E d)) w).cache ⇢ c →
      let n := M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st (M.vote_time S.E d))
        (W (strictEventIndex rho (M.vote_time S.E d)) w).record c
      ∀ T : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T →
      ∀ L : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
      ∀ L' : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
      ∀ Hd : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
          (M.toHealing n.st.core) T L L' (n.st.core.s - 1) ⇢ Hd →
      ∃ Hn : NamedBlock V, Hn.erase = Hd ∧ Restated.RunBlockOn M S rho W Xb Hn ∧
        (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core d).h_max - 1 ≤
          (M.derive_named S.E S.cfg Hn).h)
    (hgat : lo ≤ M.vote_time S.E d)
    (hrun : ∀ w ∈ S.E.committee d, w ∈ Hs (M.vote_time S.E d) →
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w (M.vote_time S.E d)) →
      M.awake_for_grade1 S w (W j w) (M.round_of S.hc d)) :
    ∀ X : NamedBlock V,
      Restated.NamedHonestHeadOn M S rho W (fun _ => Hs (M.vote_time S.E d)) Xb d X →
        Mh - 1 ≤ (M.derive_named S.E S.cfg X).h := by
  intro X hX
  obtain ⟨x, hxVote, hxCommittee, hXrun, hXemit⟩ := hX
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
    (W (strictEventIndex rho (M.vote_time S.E d)) x).st.core.toHealing
    (M.vote_time S.E d)
    (W (strictEventIndex rho (M.vote_time S.E d)) x).cache
  obtain ⟨T, L, L', Hd, hT, hL, hL', hHd⟩ := voterHead_outcome₆₄b facts S
    (M.mkNode
      (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) x).st (M.vote_time S.E d))
      (W (strictEventIndex rho (M.vote_time S.E d)) x).record c)
  have hemit := Restated.seedVoteDutyHead_emitsOn facts S Hs Xb hf hxVote hd hxCommittee hhor
    hgat c hc (hrun x hxCommittee hxVote) T hT L hL L' hL' Hd hHd
  have hrootEq : X.erase.root = Hd.root :=
    congrArg GoldfishVote.head
      (Restated.emits_gfVote_uniqueOn facts S Hs Xb hf hXemit hemit rfl)
  obtain ⟨H, hHerase, hHrun, hheight⟩ := hband x hxVote c hc T hT L hL L' hL' Hd hHd
  have hrootNamed : X.root = H.root := by
    rw [← Proofs.NamedWire.erase_root X, ← Proofs.NamedWire.erase_root H, hHerase]
    exact hrootEq
  have hXH : X = H :=
    hf.rootCollisionFree.root_injective
      X H hXrun hHrun X H (Or.inl (Proofs.NamedAncestry.named_self X))
      (Or.inr (Proofs.NamedAncestry.named_self H)) hrootNamed
  rw [hXH]
  simpa only [hfrontier x hxVote] using hheight

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Statements.Instantiation

/-- Along the path `W` with the admissible fields `hf` and the honest committees `hcom`: if for
    every member `v` of the set for `S.a c` and every round-`c` action carrier `A` of `v` the votes
    at the slot after round `c`'s opening form a cone over `A` (`hclaim1`), then the round-`c`
    action carriers of the members of the set for `S.a c` are pairwise compatible. -/
theorem honestActionCarriersOneChainAt_of_secondSlotConeOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    (hcom : Restated.HonestCommitteesOn M S Hs) {c : Round}
    (hclaim1 : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S c)),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v) c,
      ∀ g, M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ g →
      ∀ A, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) g ⇢ A →
      Restated.NamedHonestVotesConeOn M S rho W Hs Xb ((M.opening_slot S.hc c) + 1)
        (fun X => Block.Preceq A X)) :
    ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S c)),
      ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S c)),
      ∀ nu ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) u) c,
      ∀ gu, M.grade2_block_with (M.gradeContract nu.cache) S.E S.hc (M.toHealing nu.st.core)
          (M.round_of S.hc (M.toHealing nu.st.core).s) ⇢ gu →
      ∀ Au, M.get_sg_vote_with (M.gradeContract nu.cache) S.E S.hc (M.toHealing nu.st.core)
          (M.round_of S.hc (M.toHealing nu.st.core).s) gu ⇢ Au →
      ∀ nv ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v) c,
      ∀ gv, M.grade2_block_with (M.gradeContract nv.cache) S.E S.hc (M.toHealing nv.st.core)
          (M.round_of S.hc (M.toHealing nv.st.core).s) ⇢ gv →
      ∀ Av, M.get_sg_vote_with (M.gradeContract nv.cache) S.E S.hc (M.toHealing nv.st.core)
          (M.round_of S.hc (M.toHealing nv.st.core).s) gv ⇢ Av →
      Block.compatible Au Av = true := by
  intro u hu v hv nu hnu gu hgu Au hAu nv hnv gv hgv Av hAv
  have hpositive :
      0 < ((S.E.committee ((M.opening_slot S.hc c) + 1)) ∩
        Hs (M.confirmation_time S.E ((M.opening_slot S.hc c) + 1))).card := by
    have hc := hcom ((M.opening_slot S.hc c) + 1)
    omega
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hpositive
  have hwCommittee : w ∈ S.E.committee ((M.opening_slot S.hc c) + 1) :=
    (Finset.mem_inter.mp hw).1
  have hwVote : w ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc c) + 1)) :=
    hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E _) (Finset.mem_inter.mp hw).2
  obtain ⟨X, hXu, hXrun, hXemit⟩ := hclaim1 u hu nu hnu gu hgu Au hAu w hwVote hwCommittee
  obtain ⟨Y, hYv, hYrun, hYemit⟩ := hclaim1 v hv nv hnv gv hgv Av hAv w hwVote hwCommittee
  have hXY : X.erase = Y.erase :=
    Restated.runBlock_eq_of_root_eqOn facts W Xb hf.rootCollisionFree hXrun hYrun
      (congrArg GoldfishVote.head
        (Restated.emits_gfVote_uniqueOn facts S Hs Xb hf hXemit hYemit rfl))
  rw [hXY] at hXu
  exact compatible_of_common_honest_goldfish_head hXu hYv

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Statements.Instantiation

/-- For a path `W` and worlds `Wt`: if `P` has height at least `Mh − 1` and
    `GateOffOpeningAdoptionOn` holds at round `q` for `P` (`hadoption`), then
    `SeedBandCarrierCoverAtOn` holds at `Mh` and `q`, its carriers read from the world `Wt (S.a q)`. -/
theorem seedBandCarrierCover_of_adoption_windowOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} {W : Nat → V → M.N} {Wt : Time → V → M.N}
    (Hs : Int → Finset V) (Xb : Finset V)
    {Mh : Height} {q : Round}
    {P : NamedBlock V}
    (hband : Mh - 1 ≤ (M.derive_named S.E S.cfg P).h)
    (hadoption : Restated.GateOffOpeningAdoptionOn M S rho W Wt Hs Xb q P) :
    Restated.SeedBandCarrierCoverAtOn M S rho W Hs Xb Mh q
      (Wt (Restated.Vocabulary.Execution.Setup.a M S q)) :=
  ⟨P, hadoption.lifecycle.runBlock, hband, hadoption.actionCover⟩

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Statements.Instantiation

end

end DecoupledConsensusModel.Sts.Restated
