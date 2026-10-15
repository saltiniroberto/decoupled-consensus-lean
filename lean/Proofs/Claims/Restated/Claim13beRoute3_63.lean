import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13beRoute3_47
import Proofs.Claims.Restated.Claim13beRoute3_48b
import Proofs.Claims.Restated.Claim13beRoute3_53b
import Proofs.Claims.Restated.Claim13beRoute3_55
import Proofs.Claims.Restated.Claim13beRoute3_58
import Proofs.Claims.Restated.Claim13beRoute3_59
import Proofs.Claims.Restated.Claim13beRoute3_60
import Proofs.Claims.Restated.Claim13beRoute3_61
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_ModelVocabulary_Healing_Schedule
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_ActionSourceCore
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_SeedEntryCanonical
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_RowTrace
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.RunVocabulary
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGradeQueries
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
import Model.Conditions.Vocabulary_Internal_HealingSurface
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_ModelVocabulary_Healing_Schedule
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_Grades_RelativeCrossReader
import Model.Record.Wiring

/-!
# Grade-0 compatibility, selected Q2s and active anchors along a path

Theorems over a model `M : Record.Model V` and its facts `facts : Record.Facts M`, with every store
read in a world of the bundle's path `W`: compatibility of grade-0 blocks with a clear block, the
readiness of a selected Q2 for the cross-reader transport, the opening slot's instants, the selected
Q2 under a named frame, the selector cone's first interior slot, and the bodies and grades of an
active action-read anchor.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

/-! ### Helpers -/

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Proofs.HealingSurface
open scoped DC

/-- In a run sorted by key, the worlds strictly before the instant `t` are the worlds before the
    event of index `strictEventIndex rho t`. -/
private theorem stateBeforeTime_eq_strict₆₃ (S : Setup V) (rho : Record.Run V)
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
private theorem mem_stateBeforeTime_along₆₃ {S : Setup V} {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (t : Time) :
    W (strictEventIndex rho t) ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t := by
  rw [stateBeforeTime_eq_strict₆₃ S rho hsorted]
  exact (hW _).1

/-- For every path `W` of `rho`, `W (m + k)` is among the worlds the events `m` to `m + k - 1` of
    `rho` lead to from `W m`. -/
private theorem onePath_reach₆₃ {S : Setup V} {rho : Record.Run V}
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (m : Nat) :
    ∀ k : Nat, W (m + k) ∈ ((rho.events.drop m).take k).foldlM (Record.worldStepOf M S) (W m) := by
  intro k
  induction k with
  | zero => exact Set.mem_singleton _
  | succ k ih =>
    have hstep := (hW (m + k)).2
    rw [Nat.add_sub_cancel_left] at hstep
    rw [List.take_add, List.foldlM_append, Set.bind_def, List.drop_drop]
    refine Set.mem_iUnion₂.mpr ⟨W (m + k), ih, ?_⟩
    rw [← Nat.add_assoc]
    exact hstep

/-- For every path `W` of `rho` and `m ≤ n`, `W n` is among the worlds the events `m` to `n - 1` of
    `rho` lead to from `W m`. -/
private theorem onePath_slice₆₃ {S : Setup V} {rho : Record.Run V}
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) {m n : Nat}
    (hmn : m ≤ n) :
    W n ∈ ((rho.events.drop m).take (n - m)).foldlM (Record.worldStepOf M S) (W m) := by
  have h := onePath_reach₆₃ W hW m (n - m)
  rwa [Nat.add_sub_of_le hmn] at h

/-- Along a path `W` of a run, for `j ≤ n`, the finalized block of `v`'s core store in `W j` is an
    ancestor of the one in `W n`. -/
private theorem F_mono_along₆₃ (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (v : V)
    {j n : Nat} (hjn : j ≤ n) : Block.Preceq (W j v).st.core.F (W n v).st.core.F :=
  Restated.Vocabulary.Protocol.stateBefore_F_mono facts S rho v hjn (W j) (hW j).1 (W n)
    (onePath_slice₆₃ W hW hjn)

/-- If `f <$> m` can return `b`, then `m` can return some `a` with `f a = b`. -/
private theorem returns_map_elim₆₃ {α β : Type} (f : α → β) (m : DC.NDRE α) (b : β)
    (h : (f <$> m) ⇢ b) : ∃ a, m ⇢ a ∧ f a = b := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image] at h
  obtain ⟨e, he, hb⟩ := h
  cases e with
  | ok a => exact ⟨a, he, by simpa [Except.map] using hb⟩
  | error err => simp [Except.map] at hb

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
open DecoupledConsensusModel.Internal.NamedRecoveryRead
local macro "rsh% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.Grades.RecoveryInitialSourceNamedHistory)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Under the bundle with path `W`, if `0 < r`, `S.a r` is within the horizon, `w` is in the set for
    `domain r g0` with `lo ≤ domain r g0`, `L` is in the block tree of `w`'s node state in
    `W (strictEventIndex rho (domain r .g0))` and its grade-0 test there can return `true`, `n` is a
    node state of `w`'s round-`r` action read along `W`, `L` descends from `n`'s finalized block,
    and the clear test of `B` at `n` can return `true`, then `L` and `B` are compatible. -/
theorem relativeG0_compatible_clearSource_of_finalizedPreceq_historyOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {r : Round} (hr : 0 < r) (hactionHor : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon)
    {w : V} (hw : w ∈ Hs (M.domain S.E S.hc r .g0)) {L B : Block V}
    (hLtree : L ∈ (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) w).st.core.T)
    (hLgrade : Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
      (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) w).st r .g0 L ⇢ true)
    {n : M.N}
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) w) r)
    (hFL : Block.Preceq n.st.core.F L)
    (hBclear : Restated.Vocabulary.Internal.PhaseGrades.nodeClear M S n r B ⇢ true)
    (hgat : lo ≤ M.domain S.E S.hc r .g0) :
    Block.compatible L B = true := by
  obtain ⟨fr, hfr⟩ := facts.gr.freezeRoot_nonempty S.E
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) w).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) w).st.core.F
    S.hc.η_SG r (M.early S.E S.hc r .g0) (M.late S.E S.hc r .g0)
  obtain ⟨raw, rfl, hLraw⟩ := facts.gr.q10_freeze_of_graded
    S.E
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) w).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) w).st.core.F
    S.hc.η_SG r (facts.gr.q10_early_le_late S r .g0)
    (by rw [facts.gr.Sts_gradeView_T]; exact hLtree) true hLgrade rfl _ hfr
  have hframe :
      (M.readFrame n.cache (M.toHealing n.st.core) r).g0 =
        some (some (M.clipGrade raw n.st.core.F)) := by
    simpa only [Option.map_some] using
      Restated.actionFrame_g0On facts S Hs Xb hf hr hactionHor hw hgat n hn (some raw) hfr
  have hLclip : Block.Preceq L (M.clipGrade raw n.st.core.F) := by
    apply (facts.gr.q10_retained_prefix raw n.st.core.F L ?_).mpr hLraw
    exact compatible_of_cases (Or.inr hFL)
  have hBclip : Block.compatible B (M.clipGrade raw n.st.core.F) = true := by
    obtain ⟨g, hg, hgB⟩ := returns_map_elim₆₃ _ _ _ hBclear
    have hg' := (facts.nd.gradeContract_read n.cache S.E S.hc (M.toHealing n.st.core) r g).1 hg
    rw [facts.gr.frameGradeRead_clear _ _ _ _ _ g hg'] at hgB
    exact facts.gr.compatible_of_clear hgB hframe
  apply compatible_of_cases
  rcases compatible_cases hBclip with hBclip | hclipB
  · exact preceq_linear_Preceq hLclip hBclip
  · exact Or.inl (preceq_trans_Preceq hLclip hclipB)

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
open DecoupledConsensusModel.Internal.NamedRecoveryRead
local macro "rsh% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.Grades.RecoveryInitialSourceNamedHistory)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Under the bundle with path `W`, if `0 < r`, round `r` is ready, `p` is in the set for
    `domain r g0` and `lo ≤ early r g2`, then for every node state `n` of `p`'s round-`r` action
    read along `W`, every `w` in the set for `domain r g1` and every `Q` the Q2 read at `n` can
    return as `some Q`, the cross-reader body-ready condition from `p` to `w` holds for `Q` at their
    node states in `W (strictEventIndex rho (domain r .g2))` and
    `W (strictEventIndex rho (domain r .g1))`. -/
theorem actionQ2_crossReaderBodyReadyGuard_historyOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {r : Round} (hr : 0 < r) (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho r)
    {p : V} (hp : p ∈ Hs (M.domain S.E S.hc r .g0))
    (hlo : lo ≤ M.early S.E S.hc r .g2) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) p) r,
    ∀ w, w ∈ Hs (M.domain S.E S.hc r .g1) → ∀ Q,
      Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ some Q →
      Restated.Vocabulary.Proofs.HealingSurface.CrossReaderBodyReadyGuard M S rho r p w
        (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) p)
        (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w) Q := by
  have hsb : Restated.SlashableBoundOn M S rho W Xb := hf.slashableBound
  have hg2g0 : M.domain S.E S.hc r .g2 ≤ M.domain S.E S.hc r .g0 :=
    facts.gr.domain_le_domain_g0 S r .g2
  have hpG2 : p ∈ Hs (M.domain S.E S.hc r .g2) := hHs _ _ hg2g0 hp
  intro n hn w hw Q hQ
  have hdomainAction : M.domain S.E S.hc r .g0 ≤ (Restated.Vocabulary.Execution.Setup.a M S r) :=
    facts.gr.domain_le_a S r .g0
  have hg1g0 := facts.gr.domain_g1_add_delta_le_domain_g0 S r
  have hmono : Block.Preceq
      (W (strictEventIndex rho (M.domain S.E S.hc r .g1 + S.E.Δ)) p).st.core.F
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) p).st.core.F :=
    F_mono_along₆₃ facts S hf.onePath p
      (Restated.strict_lengths_mono rho (hg1g0.trans hdomainAction))
  have hnF : n.st.core.F =
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) p).st.core.F := by
    obtain ⟨c, -, st, hst, rfl⟩ := hn
    obtain ⟨X, hX⟩ := facts.dt.update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc
      (M.ns_setClock S.E (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) p).st
        (Restated.Vocabulary.Execution.Setup.a M S r)).core
      (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
    rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.dt.named_update_confirmation_with_core _ _ _ _ _ st hst X hX,
      facts.dt.update_confirmation_with_F _ _ _ _ _ X hX, facts.hd.setClock_core_F]
  have hFQAction : Block.Preceq
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) p).st.core.F Q := by
    have hactive := Restated.Vocabulary.Proofs.HealingSurface.actionQ2_mem_filteredTree facts S rho p r
      _ (mem_stateBeforeTime_along₆₃ hf.sorted hf.onePath _) n hn hQ
    have hFQ := facts.fc.q10_filtered_F hactive
    rw [← hnF, ← facts.sto.Sts_toHealing_F]
    exact hFQ
  have hpost : lo ≤ M.domain S.E S.hc r .g1 :=
    hlo.trans ((facts.gr.early_le_domain S r).trans (facts.gr.domain_g2_le_domain_g1 S r))
  have hpRelay : p ∈ Hs (M.domain S.E S.hc r .g1 + S.E.Δ) := hHs _ _ hg1g0 hp
  have hrelay : Block.Preceq
      (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st.core.F
      (W (strictEventIndex rho (M.domain S.E S.hc r .g1 + S.E.Δ)) p).st.core.F :=
    Restated.finalized_preceq_of_evidence_deliveredOn facts
      S Hs Xb hf hHs hHsXb hsb hw hpRelay hpost rfl (hg1g0.trans ready.2)
  have hforward : ∀ sender u root H,
      ∀ I, M.interpretedInputs
        (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) p).st.core))
        (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) p).st.core.F
        S.hc.η_SG r (M.early S.E S.hc r .g2) sender ⇢ I → u ∈ I →
      ∀ c, M.localCovers
        (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) p).st.core))
        u.confirmed Q ⇢ c → c = true →
      u.confirmed = some root →
      Block.find?
        (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) p).st.core)).T
          root = some H →
      Block.Preceq (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st.core.F H := by
    intro sender u root Head _ _ _ c hc hct hconf hfind
    have hQHead : Block.Preceq Q Head := by
      rw [hconf] at hc
      exact facts.gr.preceq_of_localCovers_of_find c hc hct hfind
    exact preceq_trans_Preceq hrelay
      (preceq_trans_Preceq hmono (preceq_trans_Preceq hFQAction hQHead))
  have hfinalized :=
    Restated.crossReaderFinalizedBelow_of_finalitySafety_and_relayOn facts
      S Hs Xb hf hHs hHsXb hsb hlo ready.2 hpG2 hw hforward
  exact Restated.crossReaderBodyReadyGuard_of_finalizedBelowOn facts
    S Hs Xb hf hHs hHsXb hr hlo ready.2 hpG2 hw hfinalized

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
open DecoupledConsensusModel.Internal.NamedRecoveryRead
local macro "rsh% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.Grades.RecoveryInitialSourceNamedHistory)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- With `t` the proposal instant of `opening_slot r`, round `r`'s grade-0 domain instant is
    `t + Δ`, the support cutoff is `t + 2Δ`, the view freeze `t + 3Δ`, the vote instant of the next
    slot `t + 5Δ`, and `S.a r` is `t + 6Δ`. -/
theorem openingInstants_l63 (facts : Record.Facts M) (S : Setup V) (r : Round) :
    M.domain S.E S.hc r .g0 =
        M.proposal_time S.E ((M.opening_slot S.hc r)) + S.E.Δ ∧
      M.vote_time S.E ((M.opening_slot S.hc r)) =
        M.proposal_time S.E ((M.opening_slot S.hc r)) + S.E.Δ ∧
      M.support_cutoff S.E ((M.opening_slot S.hc r)) =
        M.proposal_time S.E ((M.opening_slot S.hc r)) + 2 * S.E.Δ ∧
      M.view_freeze S.E ((M.opening_slot S.hc r)) =
        M.proposal_time S.E ((M.opening_slot S.hc r)) + 3 * S.E.Δ ∧
      M.vote_time S.E ((M.opening_slot S.hc r) + 1) =
        M.proposal_time S.E ((M.opening_slot S.hc r)) + 5 * S.E.Δ ∧
      (Restated.Vocabulary.Execution.Setup.a M S r) = M.proposal_time S.E ((M.opening_slot S.hc r)) + 6 * S.E.Δ := by
  obtain ⟨h1, h2, h3, -, h5, h6⟩ := facts.sch.slot_instants_l55 S.E ((M.opening_slot S.hc r))
  have hg0 : M.domain S.E S.hc r .g0 =
      M.proposal_time S.E ((M.opening_slot S.hc r)) + S.E.Δ := by
    rw [facts.gr.domain_g0_eq_opening, facts.gr.opening_eq_proposal_time]
  refine ⟨hg0, h1, h2, h3, h5, ?_⟩
  rw [Restated.a_eq_confirmation_opening_l58 facts S r, h6]

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Internal.NamedRecoveryRead

end

/-! ## Selected Q2s at an action read -/

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- Under the bundle with path `W`, if `n` is a node state of `v`'s round-`r` action read along `W`
    and the Q2 of `n` can return `some Q`, then `0 < r`. -/
theorem selectedQ2_round_pos_named_historyOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} {r : Round} {Q : Block V} {n : M.N}
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r)
    (hQ : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ some Q) :
    0 < r := by
  apply Nat.pos_of_ne_zero
  intro hzero
  subst hzero
  have hgrade := Restated.selectedQ2_storeGrade_at_g2DomainOn facts S Hs Xb hf n hn hQ
  obtain ⟨b, hb⟩ := facts.gr.gradeBool_nonempty S.E
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc 0 .g2)) v).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc 0 .g2)) v).st.core.F
    S.hc.η_SG 0 (M.early S.E S.hc 0 .g2) (M.late S.E S.hc 0 .g2) Q
  have h1 : b = true := hgrade b hb
  have h2 : b = false := facts.gr.gradeBool_round_zero _ _ _ _ _ _ _ _ hb
  rw [h1] at h2
  cases h2

/-- Under the bundle with path `W`, if `v ∈ Xb` and `D` is a body of a node state of `v`'s round-`r`
    action read along `W`, then `D` is a run block along `W` through `Xb`. -/
theorem actionBody_runBlock_named_historyOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} (hv : v ∈ Xb) {r : Round} {D : NamedBlock V} {n : M.N}
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r)
    (hD : D ∈ n.st.bodies) :
    Restated.RunBlockOn M S rho W Xb D :=
  Restated.actionBody_runBlock_genuineOn facts S Hs Xb hf hv hn hD

/-- Under the bundle with path `W`, if round `r` is ready, `p` is in the set for `domain r g2`, `n`
    is a node state of `p`'s round-`r` action read along `W` whose Q2 can return `some Q.erase` and
    which holds `Q` at height `blocked + 1` descending from `Tprev`, the named frame over `X` holds
    along `W` at `blocked` up to `stop`, the largest `h_max` over `X` in `W stop` is less than
    `blocked + 2`, `w` is in the set for `read` and in `X`, `domain r g2 + Δ ≤ read`, `read`'s event
    index is at most `stop`, `read` is within the horizon and `lo ≤ early r g2`, then `Q.erase` is
    in the filtered tree of `w`'s node state in `W (strictEventIndex rho read)`. -/
theorem selectedQ2_filtered_at_read_of_namedFrame_historyOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb X : Finset V) {lo : Int}
    {W : Nat → V → M.N} {Wt : Time → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hXXb : X ⊆ Xb)
    {r : Round} (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho r)
    {p : V} (hp : p ∈ Hs (M.domain S.E S.hc r .g2)) {Q : NamedBlock V} {n : M.N}
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) p) r)
    (hselected : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ some Q.erase)
    (hQmem : Q ∈ n.st.bodies)
    {stop : Nat} {blocked : Height} {Tprev : NamedBlock V} {c0 : Round}
    (hframe : Restated.NamedHeightRegimeFrameOn M S rho W Wt Hs X Xb blocked stop Tprev c0)
    (hQheight : (M.derive_named S.E S.cfg Q).h = blocked + 1)
    (hTQ : NamedBlock.Preceq Tprev Q)
    (hfrontier : (X.sup fun u => (W stop u).st.core.h_max) < blocked + 2)
    {w : V} {read : Time} (hw : w ∈ Hs read) (hwX : w ∈ X)
    (hdelivery : M.domain S.E S.hc r .g2 + S.E.Δ ≤ read)
    (hreadPrefix : strictEventIndex rho read ≤ stop)
    (hreadHor : read ≤ rho.horizon)
    (hlo : lo ≤ M.early S.E S.hc r .g2) :
    Q.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
      (W (strictEventIndex rho read) w) := by
  have hpXb : p ∈ Xb := hHsXb _ hp
  have hQrun : Restated.RunBlockOn M S rho W Xb Q :=
    Restated.actionBody_runBlock_named_historyOn facts S Hs Xb hf hpXb hn hQmem
  have htargetFQ : Block.Preceq (W (strictEventIndex rho read) w).st.core.F Q.erase :=
    hframe.floor w hwX _ hreadPrefix Q hQrun
      (by rw [hQheight]; exact Nat.le_succ blocked) hTQ
  have hQsource : Q ∈ (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) p).st.bodies :=
    Restated.selectedQ2_body_at_captureOn facts S Hs Xb hf hpXb hn hselected hQmem
  have hloDomain : lo ≤ M.domain S.E S.hc r .g2 :=
    hlo.trans (facts.gr.early_le_domain S r)
  have hpMax : p ∈ Hs (max (M.domain S.E S.hc r .g2) lo) := by
    rw [max_eq_left hloDomain]
    exact hp
  have hdeadline : max (M.domain S.E S.hc r .g2) lo + S.E.Δ ≤ read := by
    rw [max_eq_left hloDomain]
    exact hdelivery
  obtain ⟨hQtarget, -, -⟩ :=
    Restated.healthy_head_body_at_read_after_gst_admitOn facts S rho Hs Xb hf hHs hHsXb p w Q
      (M.domain S.E S.hc r .g2) read read hpMax hw hQsource hdeadline (le_refl _) hreadHor
      htargetFQ
  exact (hframe.fgRoot_preceq_and_filteredMem facts
    Hs hf hXXb hfrontier hwX hreadPrefix hQtarget hQheight hTQ).2

/-- Under the bundle with path `W` and the slashable bound, if `0 < r`, round `r` is ready, `p` is
    in the set for `domain r g2`, `n` is a node state of `p`'s round-`r` action read along `W` whose
    Q2 can return `some Q.erase` and which holds `Q` at height `blocked + 1` descending from
    `Tprev`, the named frame over `X` holds along `W` at `blocked` up to `stop`, round `r`'s action
    instant has event index at most `stop`, the largest `h_max` over `X` in `W stop` is less than
    `blocked + 2`, `w` is in the set for `domain r g1` and in `X`, and `lo ≤ opening (r − η_SG)`,
    then `Q.erase` is in the filtered tree of `w`'s node state in
    `W (strictEventIndex rho (domain r .g1))` and every outcome of its grade-1 store grade there is
    `true`. -/
theorem selectedQ2_g1Domain_data_of_namedFrame_historyOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb X : Finset V) {lo : Int}
    {W : Nat → V → M.N} {Wt : Time → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hXXb : X ⊆ Xb)
    (hsb : Restated.SlashableBoundOn M S rho W Xb)
    {r : Round} (hr : 0 < r) (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho r)
    {p : V} (hp : p ∈ Hs (M.domain S.E S.hc r .g2)) {Q : NamedBlock V} {n : M.N}
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) p) r)
    (hselected : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ some Q.erase)
    (hQmem : Q ∈ n.st.bodies)
    {stop : Nat} {blocked : Height} {Tprev : NamedBlock V} {c0 : Round}
    (hframe : Restated.NamedHeightRegimeFrameOn M S rho W Wt Hs X Xb blocked stop Tprev c0)
    (hQheight : (M.derive_named S.E S.cfg Q).h = blocked + 1)
    (hTQ : NamedBlock.Preceq Tprev Q)
    (hactionPrefix : strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r) ≤ stop)
    (hfrontier : (X.sup fun u => (W stop u).st.core.h_max) < blocked + 2)
    {w : V} (hw : w ∈ Hs (M.domain S.E S.hc r .g1)) (hwX : w ∈ X)
    (hlo : lo ≤ M.opening S.E S.hc (r - S.hc.η_SG)) :
    Q.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
        (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w) ∧
      ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
        (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st r .g1 Q.erase ⇢ b →
          b = true := by
  have hgst : lo ≤ M.early S.E S.hc r .g2 :=
    facts.gr.lo_le_early_g2_of_window_start S hr hlo
  have hdomainAction : M.domain S.E S.hc r .g1 ≤ (Restated.Vocabulary.Execution.Setup.a M S r) :=
    facts.gr.domain_le_a S r .g1
  have hdomainPrefix : strictEventIndex rho (M.domain S.E S.hc r .g1) ≤ stop :=
    (Restated.strict_lengths_mono rho hdomainAction).trans hactionPrefix
  have hpXb : p ∈ Xb := hHsXb _ hp
  have hQrun : Restated.RunBlockOn M S rho W Xb Q :=
    Restated.actionBody_runBlock_named_historyOn facts S Hs Xb hf hpXb hn hQmem
  have htargetFQ : Block.Preceq
      (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st.core.F Q.erase :=
    hframe.floor w hwX _ hdomainPrefix Q hQrun
      (by rw [hQheight]; exact Nat.le_succ blocked) hTQ
  have hg1g0 : M.domain S.E S.hc r .g1 ≤ M.domain S.E S.hc r .g0 :=
    facts.gr.domain_le_domain_g0 S r .g1
  have hfiltered := Restated.selectedQ2_filtered_at_read_of_namedFrame_historyOn facts
    S Hs Xb X hf hHs hHsXb hXXb ready hp hn hselected hQmem hframe hQheight hTQ
      hfrontier hw hwX (facts.gr.domain_g2_add_delta_le_domain_g1 S r)
      hdomainPrefix (hg1g0.trans ready.2) hgst
  have hforward : ∀ sender u root H,
      ∀ I, M.interpretedInputs
        (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) p).st.core))
        (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) p).st.core.F
        S.hc.η_SG r (M.early S.E S.hc r .g2) sender ⇢ I → u ∈ I →
      ∀ c, M.localCovers
        (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) p).st.core))
        u.confirmed Q.erase ⇢ c → c = true →
      u.confirmed = some root →
      Block.find?
        (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) p).st.core)).T
          root = some H →
      Block.Preceq (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st.core.F H := by
    intro sender u root H _ _ _ c hc hct hconf hfind
    exact preceq_trans_Preceq htargetFQ (by
      rw [hconf] at hc
      exact facts.gr.preceq_of_localCovers_of_find c hc hct hfind)
  have hbelowReaders := Restated.crossReaderFinalizedBelow_of_finalitySafety_and_relayOn facts
    S Hs Xb hf hHs hHsXb hsb hgst ready.2 hp hw hforward
  have hguard := Restated.crossReaderBodyReadyGuard_of_finalizedBelowOn facts
    S Hs Xb hf hHs hHsXb hr hgst ready.2 hp hw hbelowReaders
  have hG2 := Restated.selectedQ2_storeGrade_at_g2DomainOn facts S Hs Xb hf n hn hselected
  obtain ⟨b2, hb2⟩ := facts.gr.gradeBool_nonempty S.E
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) p).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) p).st.core.F
    S.hc.η_SG r (M.early S.E S.hc r .g2) (M.late S.E S.hc r .g2) Q.erase
  have hb2t : b2 = true := hG2 b2 hb2
  subst hb2t
  refine ⟨hfiltered, ?_⟩
  exact Restated.storeGrade_g1_of_storeGrade_g2_cross_readerOn facts
    S rho Hs Xb hf hHs hHsXb r hlo ready.2 p w hp hw Q.erase hb2 hguard

end

/-! ## The selector cone at the first interior slot -/

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open scoped DC

/-- If `m` can return `a` and `k a` can return `b`, then `m >>= k` can return `b`. -/
private theorem returns_bind_intro₆₃w {α β : Type} (m : DC.NDRE α) (k : α → DC.NDRE β) (a : α)
    (b : β) (ha : m ⇢ a) (hb : k a ⇢ b) : (m >>= k) ⇢ b := by
  unfold Record.Returns at *
  simp only [ExceptT.run_bind, Set.bind_def]
  exact Set.mem_iUnion₂.mpr ⟨_, ha, hb⟩

/-- The action FG source of a node state has an outcome. -/
private theorem actionFGSource_nonempty₆₃w (facts : Record.Facts M) (S : Setup V) (n : M.N) :
    ∃ o, Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ o := by
  obtain ⟨g, hg⟩ := facts.dt.grade2_block_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s)
  obtain ⟨F, hF⟩ := facts.dt.fg_source_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s) g
  exact ⟨F, returns_bind_intro₆₃w _ _ g F hg hF⟩

/-- If the Q2 of a node state at round `r` can return `some Q`, then the grade-2 block computed with
    that node state's contract at round `r` can return `some Q`. -/
private theorem grade2_of_nodeQ2₆₃w (facts : Record.Facts M) (S : Setup V) {n : M.N} {r : Round}
    {Q : Block V}
    (h : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ some Q) :
    M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core) r ⇢ some Q := by
  obtain ⟨g, hg, hgQ⟩ := returns_map_elim₆₃ _ _ _ h
  have hg' := (facts.nd.gradeContract_read n.cache S.E S.hc (M.toHealing n.st.core) r g).1 hg
  obtain ⟨x, hx⟩ := facts.dt.grade2_block_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) r
  have hxg := facts.nd.gradeContract_grade2_block_with n.cache S.E S.hc (M.toHealing n.st.core) r
    g hg' x hx
  rw [hxg, hgQ] at hx
  exact hx

/-- Setting the clock of a store does not change the filtered block tree of its core store. -/
private theorem setClock_filtered₆₃w (facts : Record.Facts M) (S : Setup V) (st : M.NS)
    (t : Time) :
    M.get_filtered_block_tree (M.toHealing (M.ns_setClock S.E st t).core).toFG =
      M.get_filtered_block_tree (M.toHealing st.core).toFG := by
  rw [facts.hd.setClock_core_eq_store_with_t_s]
  exact facts.fc.get_filtered_block_tree_toHealing_clock _ _ _

/-- The number of events strictly before the seed attestation's action instant is less than `stop`. -/
private theorem actionPrefix_lt₆₃w (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {Xb : Finset V} {lo : Int}
    {W : Nat → V → M.N} {Wt : Time → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {start stop : Nat} {blocked : Height} {i : Nat}
    {a : NamedAttestation V} {ta : Time} {Cfg : NamedBlock V} {T : Block V}
    (hseed : Restated.PrefixFGSelectorConeAtOn M S rho W Wt Hs Xb start stop blocked i a ta Cfg T) :
    strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round) < stop := by
  have hle : strictEventIndex rho ta ≤ i := by
    by_contra hnot
    have hlt : i < strictEventIndex rho ta := Nat.lt_of_not_ge hnot
    unfold strictEventIndex at hlt
    have hmem : Record.Event.tick a.val_index ta ∈
        rho.events.filter (fun e => decide (e.time < ta)) := by
      rw [Restated.filter_eq_takeOn facts S Hs Xb hf _ (Restated.downward_lt ta)]
      exact List.mem_of_getElem? (by
        rw [List.getElem?_take_of_lt hlt]
        exact hseed.exactTick)
    have himpossible := (List.mem_filter.mp hmem).2
    simp only [decide_eq_true_eq, Record.Event.time] at himpossible
    exact lt_irrefl ta himpossible
  rw [hseed.actionTime_eq] at hle
  exact hle.trans_lt hseed.indexLtStop

/-- The seed attestation's action instant is within the horizon. -/
private theorem actionHorizon₆₃w
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {Xb : Finset V} {lo : Int}
    {W : Nat → V → M.N} {Wt : Time → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {start stop : Nat} {blocked : Height} {i : Nat}
    {a : NamedAttestation V} {ta : Time} {Cfg : NamedBlock V} {T : Block V}
    (hseed : Restated.PrefixFGSelectorConeAtOn M S rho W Wt Hs Xb start stop blocked i a ta Cfg T) :
    Restated.Vocabulary.Execution.Setup.a M S a.round ≤ rho.horizon := by
  have h := (hf.in_horizon (Record.Event.tick a.val_index ta)
    (List.mem_of_getElem? hseed.exactTick)).2
  simpa only [Record.Event.time, hseed.actionTime_eq, Record.Event.time] using h

/-- Under the bundle with path `W`, if the selector cone holds for `a` with source `Cfg` and
    checkpoint `T`, the window over `X` at `blocked + 1` holds before `first`, the named frame over
    `X` holds at `blocked` up to `first − 1`, round `a.round` is ready, `n` is a node state of the
    signer's round-`a.round` action read along `W` whose Q2 can return `some Cfg.erase`, and
    `lo ≤ opening (a.round − η_SG)`, then for every member `w` of the set for the vote instant of
    `opening_slot a.round + 1`, every outcome of the head at `w`'s vote-duty read of that slot
    descends from `T`, and the votes of that slot along `W` form a cone over `T`. -/
theorem PrefixFGSelectorConeAtOn.selectedSource_firstInterior_of_frame_named_history
    (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {Xb X : Finset V} {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hX : ∀ t : Int, 0 ≤ t → Hs t ⊆ X) (hXXb : X ⊆ Xb)
    {start first : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg Tprev : NamedBlock V} {T : Block V} {c0 : Round}
    (hseed : Restated.PrefixFGSelectorConeAtOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs Xb start first blocked i a ta Cfg T)
    (hfirst : Restated.HeightWindowAtOn M S rho W X (blocked + 1) first)
    (hframe : Restated.NamedHeightRegimeFrameOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs X Xb blocked (first - 1) Tprev c0)
    (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho a.round)
    {n : M.N}
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) a.val_index)
      a.round)
    (hselected : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n a.round ⇢ some Cfg.erase)
    (hlo : lo ≤ M.opening S.E S.hc (a.round - S.hc.η_SG)) :
    (∀ w ∈ Hs (M.vote_time S.E (M.opening_slot S.hc a.round + 1)),
      ∀ c : M.Cache, M.onPhaseTick S.E S.hc
        (M.toHealing (W (strictEventIndex rho
          (M.vote_time S.E (M.opening_slot S.hc a.round + 1))) w).st.core)
        (M.vote_time S.E (M.opening_slot S.hc a.round + 1))
        (W (strictEventIndex rho
          (M.vote_time S.E (M.opening_slot S.hc a.round + 1))) w).cache ⇢ c →
      let nv := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho
          (M.vote_time S.E (M.opening_slot S.hc a.round + 1))) w).st
        (M.vote_time S.E (M.opening_slot S.hc a.round + 1)))
        (W (strictEventIndex rho
          (M.vote_time S.E (M.opening_slot S.hc a.round + 1))) w).record c
      ∀ tree : Finset (Block V), M.voter_filtered_block_tree S.E nv.st.core nv.st.core.s ⇢ tree →
      ∀ votes : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing nv.st.core).toFG.toSG.toGoldfishStore nv.st.core.s ⇢ votes →
      ∀ support : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing nv.st.core).toFG.toSG.toGoldfishStore
          nv.st.core.s ⇢ support →
      ∀ Xh : Block V,
        M.get_head_in_tree_with_layer (M.gradeContract nv.cache) S.E S.hc (M.toHealing nv.st.core)
          tree votes support (nv.st.core.s - 1) ⇢ Xh →
        Block.Preceq T Xh) ∧
      Restated.NamedHonestVotesConeOn M S rho W Hs Xb (M.opening_slot S.hc a.round + 1)
        (fun Y => Block.Preceq T Y) := by
  have hr : 0 < a.round :=
    Restated.selectedQ2_round_pos_named_historyOn facts S Hs Xb hf hn hselected
  have hgst : lo ≤ M.early S.E S.hc a.round .g2 :=
    facts.gr.lo_le_early_g2_of_window_start S hr hlo
  have hlopos : 0 < lo := hf.lo_pos
  have hactionBefore :
      strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round) < first :=
    actionPrefix_lt₆₃w facts hf hseed
  have hprefix :
      strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round) ≤ first - 1 :=
    Nat.le_sub_one_of_lt hactionBefore
  have hfrontier : (X.sup fun u => (W (first - 1) u).st.core.h_max) < blocked + 2 := by
    have hstopLt : first - 1 < first :=
      Nat.sub_lt (Nat.zero_lt_of_lt hactionBefore) Nat.zero_lt_one
    exact (hfirst.before _ hstopLt).trans_lt (Nat.lt_succ_self (blocked + 1))
  have hhor : Restated.Vocabulary.Execution.Setup.a M S a.round ≤ rho.horizon :=
    actionHorizon₆₃w hf hseed
  have hsigner : a.val_index ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S a.round) := by
    have h := hseed.signerHonest
    rw [hseed.actionTime_eq] at h
    exact h
  have hsignerG2 : a.val_index ∈ Hs (M.domain S.E S.hc a.round .g2) :=
    hHs _ _ (facts.gr.domain_le_a S a.round .g2) hsigner
  have hsrc : Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ some Cfg.erase := by
    obtain ⟨o, ho⟩ := actionFGSource_nonempty₆₃w facts S n
    have ho' := hseed.exactFGSource n hn o ho
    rw [ho'] at ho
    exact ho
  have hTprevCfg : NamedBlock.Preceq Tprev Cfg :=
    hframe.sourceAbove a.val_index a.round hsigner hprefix hhor n hn
      Cfg (hseed.sourceMem n hn) hsrc hseed.sourceDerivedHeight
  have hTCfg : Block.Preceq T Cfg.erase := by
    rw [hseed.checkpointDerived]
    exact facts.csAdded.derive_named_T_h_preceq S.E S.cfg Cfg
  have hs : 0 < M.opening_slot S.hc a.round + 1 := Nat.succ_pos _
  have hround : M.round_of S.hc (M.opening_slot S.hc a.round + 1) = a.round :=
    facts.gr.HealingLemmas_round_of_opening_succ S.hc a.round
  have hread : M.domain S.E S.hc a.round .g1 <
      M.vote_time S.E (M.opening_slot S.hc a.round + 1) := by
    rw [facts.gr.Sts_domain_g1_eq_opening, facts.gr.opening_eq_proposal_time]
    exact (facts.sch.proposal_time_lt_vote_time S.E (M.opening_slot S.hc a.round)).trans_le
      (facts.sch.vote_time_mono_slots S.E (Nat.le_succ _))
  have hta : M.vote_time S.E (M.opening_slot S.hc a.round + 1) ≤
      Restated.Vocabulary.Execution.Setup.a M S a.round :=
    (Restated.Vocabulary.Protocol.next_vote_time_lt_action facts S a.round).le
  have hvotePrefix :
      strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc a.round + 1)) ≤ first - 1 :=
    Nat.le_sub_one_of_lt
      ((Restated.strict_lengths_mono rho hta).trans_lt hactionBefore)
  have hvoteHor : M.vote_time S.E (M.opening_slot S.hc a.round + 1) ≤ rho.horizon :=
    hta.trans hhor
  have hg1Hor : M.domain S.E S.hc a.round .g1 ≤ rho.horizon :=
    (facts.gr.domain_le_domain_g0 S a.round .g1).trans ready.2
  have hdelivery : M.domain S.E S.hc a.round .g2 + S.E.Δ ≤
      M.vote_time S.E (M.opening_slot S.hc a.round + 1) :=
    (facts.gr.domain_g2_add_delta_le_domain_g1 S a.round).trans hread.le
  have hlog1 : lo ≤ M.domain S.E S.hc a.round .g1 :=
    hgst.trans ((facts.gr.early_le_domain S a.round).trans
      (facts.gr.domain_g2_le_domain_g1 S a.round))
  have hsource : M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
      a.round ⇢ some Cfg.erase := grade2_of_nodeQ2₆₃w facts S hselected
  have hsb : Restated.SlashableBoundOn M S rho W Xb := hf.slashableBound
  have hvoteMem : ∀ w ∈ Hs (M.vote_time S.E (M.opening_slot S.hc a.round + 1)),
      w ∈ Hs (M.domain S.E S.hc a.round .g1) ∧ w ∈ X := by
    intro w hw
    exact ⟨hHs _ _ hread.le hw, hX _ (by linarith) hw⟩
  have hdata : ∀ w ∈ Hs (M.vote_time S.E (M.opening_slot S.hc a.round + 1)),
      Cfg.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc a.round .g1)) w) ∧
        Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
          (W (strictEventIndex rho (M.domain S.E S.hc a.round .g1)) w).st
          a.round .g1 Cfg.erase ⇢ true := by
    intro w hw
    obtain ⟨h1, h2⟩ := Restated.selectedQ2_g1Domain_data_of_namedFrame_historyOn facts
      S Hs Xb X hf hHs hHsXb hXXb hsb hr ready hsignerG2 hn hselected (hseed.sourceMem n hn)
        hframe hseed.sourceDerivedHeight hTprevCfg hprefix hfrontier
        (hvoteMem w hw).1 (hvoteMem w hw).2 hlo
    obtain ⟨b, hb⟩ := facts.gr.gradeBool_nonempty S.E
      (M.gradeView (M.toHealing
        (W (strictEventIndex rho (M.domain S.E S.hc a.round .g1)) w).st.core))
      (W (strictEventIndex rho (M.domain S.E S.hc a.round .g1)) w).st.core.F
      S.hc.η_SG a.round (M.early S.E S.hc a.round .g1) (M.late S.E S.hc a.round .g1) Cfg.erase
    have hbt : b = true := h2 b hb
    subst hbt
    exact ⟨h1, hb⟩
  have hvote : ∀ w ∈ Hs (M.vote_time S.E (M.opening_slot S.hc a.round + 1)),
      Cfg.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc a.round + 1))) w) := by
    intro w hw
    exact Restated.selectedQ2_filtered_at_read_of_namedFrame_historyOn facts
      S Hs Xb X hf hHs hHsXb hXXb ready hsignerG2 hn hselected (hseed.sourceMem n hn) hframe
        hseed.sourceDerivedHeight hTprevCfg hfrontier hw (hvoteMem w hw).2
        hdelivery hvotePrefix hvoteHor hgst
  have hvoteSet : ∀ w ∈ Hs (M.vote_time S.E (M.opening_slot S.hc a.round + 1)),
      Cfg.erase ∈ M.get_filtered_block_tree (M.toHealing (M.ns_setClock S.E
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc a.round + 1))) w).st
        (M.vote_time S.E (M.opening_slot S.hc a.round + 1))).core).toFG := by
    intro w hw
    rw [setClock_filtered₆₃w facts S]
    exact hvote w hw
  refine ⟨?_, ?_⟩
  · intro w hw c hc nv tree htree votes hvotes support hsupport Xh hXh
    have hactive : Cfg.erase ∈ M.get_filtered_block_tree (M.toHealing nv.st.core).toFG := by
      have hst : nv.st = M.store_with_cache (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc a.round + 1))) w).st (M.vote_time S.E (M.opening_slot S.hc a.round + 1))) _ := facts.nd.mkNode_st _ _ _
      rw [hst]
      try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
      exact hvoteSet w hw
    have hpre := Restated.selectedActionG2_preceq_sameRoundVoteDutyHead_of_activeAtVoteOn facts
      S Hs Xb hf hr hsigner n hn hsource hround (hvoteMem w hw).1 hlog1
        hread hta hg1Hor (hdata w hw).1 (hdata w hw).2 (hvote w hw) (fun j hj => hf.tick_outcome j _ _ hj) c hc hactive
        tree htree votes hvotes support hsupport Xh hXh
    exact preceq_trans_Preceq hTCfg hpre
  ·
    have hwin : lo ≤ M.early S.E S.hc (M.round_of S.hc (M.opening_slot S.hc a.round + 1)) .g1 -
        S.E.Δ := by
      rw [hround]
      have h1 := facts.gr.early_g2_add_delta_le_early_g1 S a.round
      linarith
    have hconeCfg := Restated.honestVotesCone_of_selectedActionG2_of_readDispositionOn facts
      S Hs Xb hf hHs hHsXb hr ready hsigner n hn hsource hs hround hread hta hvoteHor hlog1
        (fun w hw _ => ⟨(hdata w hw).1, (hdata w hw).2, hvote w hw⟩)
        (fun w hw _ => Or.inr (hvoteSet w hw))
        (fun w hw _ j hj => hf.awake_g1 _ _ j _ (Or.inr rfl) hj hw hwin)
    intro w hw hcommittee
    obtain ⟨Y, hCfgY, hYrun, hYemit⟩ := hconeCfg w hw hcommittee
    exact ⟨Y, preceq_trans_Preceq hTCfg hCfgY, hYrun, hYemit⟩

end

/-! ## An active anchor of an action read -/

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Internal.NamedRecoveryRead
local macro "p48b% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_48b)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p59% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_59)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

/-- Under the bundle with path `W`, if `0 < r`, round `r` is ready, `w` is in the set for
    `domain r g1`, a node state `n` of `w`'s round-`r` action read along `W` has the grade-1 frame
    root `root` and active prefix `L` under it, and `lo ≤ early r g2`, then the root frozen at `w`'s
    store in `W (strictEventIndex rho (domain r .g1))` can be `some raw` for a block `raw` that `L`
    is an ancestor of. -/
private theorem activeActionAnchor_raw₆₃w (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {r : Round} (hr : 0 < r)
    (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho r)
    {w : V} (hw : w ∈ Hs (M.domain S.E S.hc r .g1)) {root L : Block V} {n : M.N}
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) w) r)
    (hframe : (M.readFrame n.cache (M.toHealing n.st.core) r).g1 = some (some root))
    (hactive : M.activePrefix (Restated.Vocabulary.Internal.PhaseGrades.filteredTree M n) root =
      some L)
    (hlo : lo ≤ M.early S.E S.hc r .g2) :
    ∃ raw : Block V,
      M.freezeRoot S.E
        (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st.core))
        (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st.core.F
        S.hc.η_SG r (M.early S.E S.hc r .g1) (M.late S.E S.hc r .g1) ⇢ some raw ∧
      Block.Preceq L raw := by
  have hg1Horizon : M.domain S.E S.hc r .g1 ≤ rho.horizon :=
    (facts.gr.domain_le_domain_g0 S r .g1).trans ready.2
  have hlog1 : lo ≤ M.domain S.E S.hc r .g1 :=
    hlo.trans ((facts.gr.early_le_domain S r).trans (facts.gr.domain_g2_le_domain_g1 S r))
  obtain ⟨fr, hfr⟩ := facts.gr.freezeRoot_nonempty S.E
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st.core.F
    S.hc.η_SG r (M.early S.E S.hc r .g1) (M.late S.E S.hc r .g1)
  have hmem := (p48b% mem_stateBeforeTime_path₄₈b) S rho hf.sorted W hf.onePath
    (Restated.Vocabulary.Execution.Setup.a M S r)
  have h := Restated.Vocabulary.Proofs.FrameForward.frame_phase_checkpoint_eq facts S rho w r .g1 _ _
    hmem
    (Restated.frame_phase_completedOn facts S rho Hs Xb hf w r hr .g1 hw
      (Restated.Vocabulary.Execution.Setup.a M S r)
      ((p48b% domain_lt_a₄₈b) facts S r .g1) le_rfl hg1Horizon hlog1 (fun j hj => hf.tick_outcome j _ _ hj) fr hfr)
    n.cache ((p48b% actionReadFrom_cache₄₈b) facts S _ r n hn)
  rewrite [facts.nd.mkNode_cache, facts.nd.mkNode_st] at h; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at h; rw [← (p48b% actionReadFrom_readFrame₄₈b) facts S _ r r n hn] at h
  have hphase : M.phaseResult (M.readFrame n.cache (M.toHealing n.st.core) r) .g1 =
      some (fr.map (fun B => M.clipGrade B n.st.core.F)) := by
    rw [(p48b% actionReadFrom_F₄₈b) facts S _ r n hn]
    exact h
  have hreadFrame := (facts.gr.phaseResult_g1 _).symm.trans hphase
  cases fr with
  | none => exact absurd (hframe.symm.trans hreadFrame) (by simp)
  | some raw =>
    have hrootEq : root = M.clipGrade raw n.st.core.F := by
      have hopt := hframe.symm.trans hreadFrame
      simpa using hopt
    refine ⟨raw, hfr, ?_⟩
    have hLroot : Block.Preceq L root :=
      preceq_eq_true_iff_Preceq.mp (facts.gr.activePrefix_preceq hactive)
    rw [hrootEq] at hLroot
    exact preceq_trans_Preceq hLroot (facts.gr.q10_clip_preceq raw n.st.core.F)

/-- Under the bundle with path `W`, if `0 < r`, round `r` is ready, `w` is in the set for
    `domain r g1`, a node state `n` of `w`'s round-`r` action read along `W` has the grade-1 frame
    root `root` and active prefix `L` under it, and `lo ≤ early r g2`, then every outcome of the
    grade-1 store grade of `L` at `w`'s store in `W (strictEventIndex rho (domain r .g1))` is
    `true`. -/
theorem activeActionAnchor_storeGrade_g1_named_historyOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {r : Round} (hr : 0 < r)
    (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho r)
    {w : V} (hw : w ∈ Hs (M.domain S.E S.hc r .g1)) {root L : Block V} {n : M.N}
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) w) r)
    (hframe : (M.readFrame n.cache (M.toHealing n.st.core) r).g1 = some (some root))
    (hactive : M.activePrefix (Restated.Vocabulary.Internal.PhaseGrades.filteredTree M n) root =
      some L)
    (hlo : lo ≤ M.early S.E S.hc r .g2) :
    ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
      (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st r .g1 L ⇢ b → b = true := by
  intro b hb
  obtain ⟨raw, hraw, hLraw⟩ := activeActionAnchor_raw₆₃w facts S Hs Xb hf hr ready hw hn
    hframe hactive hlo
  obtain ⟨braw, hbraw⟩ := facts.gr.gradeBool_nonempty S.E
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st.core.F
    S.hc.η_SG r (M.early S.E S.hc r .g1) (M.late S.E S.hc r .g1) raw
  have hrawT : braw = true := facts.gr.gradeBool_of_freezeRoot_eq_some (some raw) hraw rfl braw hbraw
  exact facts.csAdded.confirmation_phaseGrade_mono S.E S.hc _ _ r .g1 hLraw braw hbraw hrawT b hb

/-- Under the bundle with path `W`, if `0 < r`, round `r` is ready, `w` is in the set for
    `domain r g1`, a node state `n` of `w`'s round-`r` action read along `W` has the grade-1 frame
    root `root` and active prefix `L` under it, and `lo ≤ early r g2`, then some named `Ln` with
    erasure `L` is a body of `w`'s store in `W (strictEventIndex rho (domain r .g1))` and a run
    block along `W` through `Xb`. -/
theorem activeActionAnchor_namedBody_at_g1Domain_historyOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {r : Round} (hr : 0 < r)
    (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho r)
    {w : V} (hw : w ∈ Hs (M.domain S.E S.hc r .g1)) {root L : Block V} {n : M.N}
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) w) r)
    (hframe : (M.readFrame n.cache (M.toHealing n.st.core) r).g1 = some (some root))
    (hactive : M.activePrefix (Restated.Vocabulary.Internal.PhaseGrades.filteredTree M n) root =
      some L)
    (hlo : lo ≤ M.early S.E S.hc r .g2) :
    ∃ Ln : NamedBlock V, Ln.erase = L ∧
      Ln ∈ (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st.bodies ∧
      Restated.RunBlockOn M S rho W Xb Ln := by
  obtain ⟨raw, hraw, hLraw⟩ := activeActionAnchor_raw₆₃w facts S Hs Xb hf hr ready hw hn
    hframe hactive hlo
  set k := strictEventIndex rho (M.domain S.E S.hc r .g1) with hk
  have hrawTree : raw ∈ (W k w).st.core.T := by
    have h := facts.gr.mem_T_of_freezeRoot_eq_some _ hraw rfl
    rw [facts.gr.Sts_gradeView_T] at h
    exact h
  have hLtree : L ∈ (W k w).st.core.T := by
    have hpc : Restated.Vocabulary.Internal.ParentClosed M (W k w).st.core :=
      Restated.Vocabulary.Proofs.NamedStoreBridge.parentClosed_stateBefore facts S rho k w (W k)
        (hf.onePath k).1
    have h := Proofs.Records.mem_of_preceq hpc.2 L raw
      (by rw [facts.sto.toHealing_gs_T]; exact hrawTree) (preceq_eq_true_iff_Preceq.mpr hLraw)
    rw [facts.sto.toHealing_gs_T] at h
    exact h
  obtain ⟨Ln, hLn, hLnErase⟩ := (p59% exists_named_along₅₉) facts S hf.onePath k w hLtree
  exact ⟨Ln, hLnErase, hLn,
    Restated.runBlock_of_stateBefore_memOn facts S W Xb (hHsXb _ hw) hLn⟩

/-- Under the bundle with path `W`, if `0 < r`, round `r` is ready, `S.a r` is within the horizon,
    `p` is in the set for `domain r g0`, `w` in the set for `domain r g0 + Δ`, a node state `n` of
    `w`'s round-`r` action read along `W` has the grade-1 frame root `root` and active prefix `L`
    under it, and `lo ≤ early r g2`, then some named `Ln` with erasure `L` is a body of `p`'s store
    in `W (strictEventIndex rho (domain r .g0))` and of every node state of `p`'s round-`r` action
    read, `L` is a descendant of `p`'s finalized block there, and `Ln` is a run block along `W`
    through `Xb`. -/
theorem activeActionAnchor_namedBody_at_sourceG0_historyOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {r : Round} (hr : 0 < r)
    (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho r)
    (hactionHor : Restated.Vocabulary.Execution.Setup.a M S r ≤ rho.horizon)
    {p w : V} (hp : p ∈ Hs (M.domain S.E S.hc r .g0))
    (hw : w ∈ Hs (M.domain S.E S.hc r .g0 + S.E.Δ))
    {root L : Block V} {n : M.N}
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) w) r)
    (hframe : (M.readFrame n.cache (M.toHealing n.st.core) r).g1 = some (some root))
    (hactive : M.activePrefix (Restated.Vocabulary.Internal.PhaseGrades.filteredTree M n) root =
      some L)
    (hlo : lo ≤ M.early S.E S.hc r .g2) :
    ∃ Ln : NamedBlock V, Ln.erase = L ∧
      Ln ∈ (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) p).st.bodies ∧
      (∀ np ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) p) r,
        Ln ∈ np.st.bodies) ∧
      Block.Preceq (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) p).st.core.F L ∧
      Restated.RunBlockOn M S rho W Xb Ln := by
  have hΔ := S.E.Δ_pos
  have hg1Out : M.domain S.E S.hc r .g1 ≤ M.domain S.E S.hc r .g0 + S.E.Δ := by
    have h := facts.gr.domain_le_domain_g0 S r .g1
    linarith
  have hwG1 : w ∈ Hs (M.domain S.E S.hc r .g1) := hHs _ _ hg1Out hw
  obtain ⟨Ln, hLnErase, hLnG1, hLnRun⟩ :=
    Restated.activeActionAnchor_namedBody_at_g1Domain_historyOn facts
      S Hs Xb hf hHsXb hr ready hwG1 hn hframe hactive hlo
  have hLaction : L ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M n :=
    facts.gr.activePrefix_mem _ _ _ hactive
  have hpost : lo ≤ M.domain S.E S.hc r .g0 :=
    hlo.trans ((facts.gr.early_le_domain S r).trans (facts.gr.domain_le_domain_g0 S r .g2))
  have houtAction : M.domain S.E S.hc r .g0 + S.E.Δ ≤
      Restated.Vocabulary.Execution.Setup.a M S r := by
    have h5 := facts.gr.domain_add_five_delta_le_action S r .g0
    show M.domain S.E S.hc r .g0 + S.E.Δ ≤ M.a S.hc S.E.Δ r
    linarith
  have hrelay : Block.Preceq
      (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) p).st.core.F
      (W (strictEventIndex rho (M.domain S.E S.hc r .g0 + S.E.Δ)) w).st.core.F :=
    Restated.finalized_preceq_of_evidence_deliveredOn facts
      S Hs Xb hf hHs hHsXb hf.slashableBound hp hw hpost rfl (houtAction.trans hactionHor)
  have hmono : Block.Preceq
      (W (strictEventIndex rho (M.domain S.E S.hc r .g0 + S.E.Δ)) w).st.core.F
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) w).st.core.F :=
    F_mono_along₆₃ facts S hf.onePath w
      (Restated.strict_lengths_mono rho houtAction)
  have hactionL : Block.Preceq
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) w).st.core.F L := by
    have hFL := facts.fc.q10_filtered_F hLaction
    rw [facts.sto.Sts_toHealing_F, (p48b% actionReadFrom_F₄₈b) facts S _ r n hn] at hFL
    exact hFL
  have htargetF : Block.Preceq
      (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) p).st.core.F Ln.erase := by
    rw [hLnErase]
    exact preceq_trans_Preceq hrelay (preceq_trans_Preceq hmono hactionL)
  have hpostG1 : lo ≤ M.domain S.E S.hc r .g1 :=
    hlo.trans ((facts.gr.early_le_domain S r).trans (facts.gr.domain_g2_le_domain_g1 S r))
  have hdeadline : max (M.domain S.E S.hc r .g1) lo + S.E.Δ ≤ M.domain S.E S.hc r .g0 := by
    rw [max_eq_left hpostG1]
    exact facts.gr.domain_g1_add_delta_le_domain_g0 S r
  have hwMax : w ∈ Hs (max (M.domain S.E S.hc r .g1) lo) := by
    rw [max_eq_left hpostG1]
    exact hwG1
  obtain ⟨hLnG0, -, -⟩ :=
    Restated.healthy_head_body_at_read_after_gst_admitOn facts
      S rho Hs Xb hf hHs hHsXb w p Ln
        (M.domain S.E S.hc r .g1) (M.domain S.E S.hc r .g0)
        (M.domain S.E S.hc r .g0) hwMax hp hLnG1 hdeadline (le_refl _)
        ready.2 htargetF
  have hdomainAction : M.domain S.E S.hc r .g0 ≤ Restated.Vocabulary.Execution.Setup.a M S r :=
    facts.gr.domain_le_a S r .g0
  refine ⟨Ln, hLnErase, hLnG0, ?_, by rw [← hLnErase]; exact htargetF, hLnRun⟩
  intro np hnp
  rw [(p59% actionReadFrom_bodies₅₉) facts S _ r np hnp]
  exact (p59% bodies_mono_along₅₉) facts S hf.onePath p
    (Restated.strict_lengths_mono rho hdomainAction) hLnG0

end

/-! ## The selected source and the opening slot -/

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- Under the bundle with path `W`, if the selector cone holds for `a` with source `Cfg` and
    checkpoint `T`, the window over `X` at `blocked + 1` holds before `first`, the named frame over
    `X` holds at `blocked` up to `first − 1`, round `a.round` is ready, `n` is a node state of the
    signer's round-`a.round` action read along `W` whose Q2 can return `some Cfg.erase`, `w` is in
    the set for the vote instant of `opening_slot a.round`, and `lo ≤ opening (a.round − η_SG)`,
    then `Cfg.erase` is an ancestor of every outcome of the head at `w`'s vote-duty read of
    `opening_slot a.round`. -/
theorem PrefixFGSelectorConeAtOn.selectedSource_preceq_openingHead_of_namedFrame_history
    (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {Xb X : Finset V} {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hX : ∀ t : Int, 0 ≤ t → Hs t ⊆ X) (hXXb : X ⊆ Xb)
    {start first : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg Tprev : NamedBlock V} {T : Block V} {c0 : Round}
    (hseed : Restated.PrefixFGSelectorConeAtOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs Xb start first blocked i a ta Cfg T)
    (hfirst : Restated.HeightWindowAtOn M S rho W X (blocked + 1) first)
    (hframe : Restated.NamedHeightRegimeFrameOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs X Xb blocked (first - 1) Tprev c0)
    (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho a.round)
    {n : M.N}
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) a.val_index)
      a.round)
    (hselected : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n a.round ⇢ some Cfg.erase)
    {w : V} (hw : w ∈ Hs (M.vote_time S.E (M.opening_slot S.hc a.round)))
    (hlo : lo ≤ M.opening S.E S.hc (a.round - S.hc.η_SG)) :
    ∀ c : M.Cache, M.onPhaseTick S.E S.hc
        (M.toHealing (W (strictEventIndex rho
          (M.vote_time S.E (M.opening_slot S.hc a.round))) w).st.core)
        (M.vote_time S.E (M.opening_slot S.hc a.round))
        (W (strictEventIndex rho
          (M.vote_time S.E (M.opening_slot S.hc a.round))) w).cache ⇢ c →
      let nv := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho
          (M.vote_time S.E (M.opening_slot S.hc a.round))) w).st
        (M.vote_time S.E (M.opening_slot S.hc a.round)))
        (W (strictEventIndex rho
          (M.vote_time S.E (M.opening_slot S.hc a.round))) w).record c
      ∀ tree : Finset (Block V), M.voter_filtered_block_tree S.E nv.st.core nv.st.core.s ⇢ tree →
      ∀ votes : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing nv.st.core).toFG.toSG.toGoldfishStore nv.st.core.s ⇢ votes →
      ∀ support : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing nv.st.core).toFG.toSG.toGoldfishStore
          nv.st.core.s ⇢ support →
      ∀ Xh : Block V,
        M.get_head_in_tree_with_layer (M.gradeContract nv.cache) S.E S.hc (M.toHealing nv.st.core)
          tree votes support (nv.st.core.s - 1) ⇢ Xh →
        Block.Preceq Cfg.erase Xh := by
  have hr : 0 < a.round :=
    Restated.selectedQ2_round_pos_named_historyOn facts S Hs Xb hf hn hselected
  have hgst : lo ≤ M.early S.E S.hc a.round .g2 :=
    facts.gr.lo_le_early_g2_of_window_start S hr hlo
  have hlopos : 0 < lo := hf.lo_pos
  have hactionBefore :
      strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round) < first :=
    actionPrefix_lt₆₃w facts hf hseed
  have hprefix :
      strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round) ≤ first - 1 :=
    Nat.le_sub_one_of_lt hactionBefore
  have hfrontier : (X.sup fun u => (W (first - 1) u).st.core.h_max) < blocked + 2 := by
    have hstopLt : first - 1 < first :=
      Nat.sub_lt (Nat.zero_lt_of_lt hactionBefore) Nat.zero_lt_one
    exact (hfirst.before _ hstopLt).trans_lt (Nat.lt_succ_self (blocked + 1))
  have hhor : Restated.Vocabulary.Execution.Setup.a M S a.round ≤ rho.horizon :=
    actionHorizon₆₃w hf hseed
  have hsigner : a.val_index ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S a.round) := by
    have h := hseed.signerHonest
    rw [hseed.actionTime_eq] at h
    exact h
  have hsignerG2 : a.val_index ∈ Hs (M.domain S.E S.hc a.round .g2) :=
    hHs _ _ (facts.gr.domain_le_a S a.round .g2) hsigner
  have hsrc : Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ some Cfg.erase := by
    obtain ⟨o, ho⟩ := actionFGSource_nonempty₆₃w facts S n
    have ho' := hseed.exactFGSource n hn o ho
    rw [ho'] at ho
    exact ho
  have hTprevCfg : NamedBlock.Preceq Tprev Cfg :=
    hframe.sourceAbove a.val_index a.round hsigner hprefix hhor n hn
      Cfg (hseed.sourceMem n hn) hsrc hseed.sourceDerivedHeight
  have hround : M.round_of S.hc (M.opening_slot S.hc a.round) = a.round :=
    facts.gr.round_of_opening_slot_eq_schedule S.hc a.round
  have hread : M.domain S.E S.hc a.round .g1 <
      M.vote_time S.E (M.opening_slot S.hc a.round) := by
    rw [facts.gr.Sts_domain_g1_eq_opening, facts.gr.opening_eq_proposal_time]
    exact facts.sch.proposal_time_lt_vote_time S.E (M.opening_slot S.hc a.round)
  have hta : M.vote_time S.E (M.opening_slot S.hc a.round) ≤
      Restated.Vocabulary.Execution.Setup.a M S a.round :=
    (Restated.Vocabulary.Protocol.opening_vote_time_lt_action facts S a.round).le
  have hvotePrefix :
      strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc a.round)) ≤ first - 1 :=
    Nat.le_sub_one_of_lt
      ((Restated.strict_lengths_mono rho hta).trans_lt hactionBefore)
  have hvoteHor : M.vote_time S.E (M.opening_slot S.hc a.round) ≤ rho.horizon :=
    hta.trans hhor
  have hg1Hor : M.domain S.E S.hc a.round .g1 ≤ rho.horizon :=
    (facts.gr.domain_le_domain_g0 S a.round .g1).trans ready.2
  have hdelivery : M.domain S.E S.hc a.round .g2 + S.E.Δ ≤
      M.vote_time S.E (M.opening_slot S.hc a.round) :=
    (facts.gr.domain_g2_add_delta_le_domain_g1 S a.round).trans hread.le
  have hlog1 : lo ≤ M.domain S.E S.hc a.round .g1 :=
    hgst.trans ((facts.gr.early_le_domain S a.round).trans
      (facts.gr.domain_g2_le_domain_g1 S a.round))
  have hsource : M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
      a.round ⇢ some Cfg.erase := grade2_of_nodeQ2₆₃w facts S hselected
  have hwG1 : w ∈ Hs (M.domain S.E S.hc a.round .g1) := hHs _ _ hread.le hw
  have hwX : w ∈ X := hX _ (by linarith) hw
  obtain ⟨hd1, hd2⟩ := Restated.selectedQ2_g1Domain_data_of_namedFrame_historyOn facts
    S Hs Xb X hf hHs hHsXb hXXb hf.slashableBound hr ready hsignerG2 hn hselected
      (hseed.sourceMem n hn) hframe hseed.sourceDerivedHeight hTprevCfg hprefix hfrontier
      hwG1 hwX hlo
  obtain ⟨b, hb⟩ := facts.gr.gradeBool_nonempty S.E
    (M.gradeView (M.toHealing
      (W (strictEventIndex rho (M.domain S.E S.hc a.round .g1)) w).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc a.round .g1)) w).st.core.F
    S.hc.η_SG a.round (M.early S.E S.hc a.round .g1) (M.late S.E S.hc a.round .g1) Cfg.erase
  have hbt : b = true := hd2 b hb
  subst hbt
  have hvote := Restated.selectedQ2_filtered_at_read_of_namedFrame_historyOn facts
    S Hs Xb X hf hHs hHsXb hXXb ready hsignerG2 hn hselected (hseed.sourceMem n hn) hframe
      hseed.sourceDerivedHeight hTprevCfg hfrontier hw hwX hdelivery hvotePrefix hvoteHor hgst
  intro c hc nv tree htree votes hvotes support hsupport Xh hXh
  have hactive : Cfg.erase ∈ M.get_filtered_block_tree (M.toHealing nv.st.core).toFG := by
    have hst : nv.st = M.store_with_cache (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc a.round))) w).st (M.vote_time S.E (M.opening_slot S.hc a.round))) _ := facts.nd.mkNode_st _ _ _
    rw [hst]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    rw [setClock_filtered₆₃w facts S]
    exact hvote
  exact Restated.selectedActionG2_preceq_sameRoundVoteDutyHead_of_activeAtVoteOn facts
    S Hs Xb hf hr hsigner n hn hsource hround hwG1 hlog1
      hread hta hg1Hor hd1 hb hvote (fun j hj => hf.tick_outcome j _ _ hj) c hc hactive
      tree htree votes hvotes support hsupport Xh hXh

/-- Under the hypotheses of
    `PrefixFGSelectorConeAtOn.selectedSource_preceq_openingHead_of_namedFrame_history` and the
    committee majorities, if `w` is in the set for the support cutoff of `opening_slot a.round`,
    `cv` is an outcome of the phase tick at that slot's confirmation instant on `w`'s node state in
    `W` there, and `C` is confirmed at that slot on `w`'s tick store there with the contract of
    `cv`, then `Cfg.erase` and `C` are compatible. -/
theorem PrefixFGSelectorConeAtOn.selectedSource_compatible_genuineOpening_of_namedFrame_history
    (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {Xb X : Finset V} {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hX : ∀ t : Int, 0 ≤ t → Hs t ⊆ X) (hXXb : X ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {start first : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg Tprev : NamedBlock V} {T : Block V} {c0 : Round}
    (hseed : Restated.PrefixFGSelectorConeAtOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs Xb start first blocked i a ta Cfg T)
    (hfirst : Restated.HeightWindowAtOn M S rho W X (blocked + 1) first)
    (hframe : Restated.NamedHeightRegimeFrameOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs X Xb blocked (first - 1) Tprev c0)
    (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho a.round)
    {n : M.N}
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) a.val_index)
      a.round)
    (hselected : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n a.round ⇢ some Cfg.erase)
    {w : V} (hw : w ∈ Hs (M.support_cutoff S.E (M.opening_slot S.hc a.round)))
    {C : Block V}
    (cv : M.Cache)
    (hcv : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho
        (M.confirmation_time S.E (M.opening_slot S.hc a.round))) w).st.core.toHealing
      (M.confirmation_time S.E (M.opening_slot S.hc a.round))
      (W (strictEventIndex rho
        (M.confirmation_time S.E (M.opening_slot S.hc a.round))) w).cache ⇢ cv)
    (hgenuine : Restated.Vocabulary.Protocol.GenuineConfirmationWith M (M.gradeContract cv)
      S.E S.hc (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho
          (M.confirmation_time S.E (M.opening_slot S.hc a.round))) w).st.core
        (M.confirmation_time S.E (M.opening_slot S.hc a.round)))
      (M.opening_slot S.hc a.round) C)
    (hlo : lo ≤ M.opening S.E S.hc (a.round - S.hc.η_SG)) :
    Block.compatible Cfg.erase C = true := by
  have hr : 0 < a.round :=
    Restated.selectedQ2_round_pos_named_historyOn facts S Hs Xb hf hn hselected
  have hgst : lo ≤ M.early S.E S.hc a.round .g2 :=
    facts.gr.lo_le_early_g2_of_window_start S hr hlo
  have hopenPos : 0 < M.opening_slot S.hc a.round :=
    facts.gr.opening_slot_pos_of_round_pos S.hc hr
  have hpost : lo ≤ M.vote_time S.E (M.opening_slot S.hc a.round) := by
    have hlog1 : lo ≤ M.domain S.E S.hc a.round .g1 :=
      hgst.trans ((facts.gr.early_le_domain S a.round).trans
        (facts.gr.domain_g2_le_domain_g1 S a.round))
    have hread : M.domain S.E S.hc a.round .g1 <
        M.vote_time S.E (M.opening_slot S.hc a.round) := by
      rw [facts.gr.Sts_domain_g1_eq_opening, facts.gr.opening_eq_proposal_time]
      exact facts.sch.proposal_time_lt_vote_time S.E (M.opening_slot S.hc a.round)
    exact hlog1.trans hread.le
  have hconfHor : M.confirmation_time S.E (M.opening_slot S.hc a.round) ≤ rho.horizon := by
    rw [← facts.sch.a_eq_confirmation_time]
    exact actionHorizon₆₃w hf hseed
  have hwin : lo ≤ M.early S.E S.hc (M.round_of S.hc (M.opening_slot S.hc a.round)) .g1 - S.E.Δ := by
    rw [facts.gr.round_of_opening_slot_eq S.hc a.round]
    have h1 := facts.gr.early_g2_add_delta_le_early_g1 S a.round
    linarith
  refine Restated.genuineConfirmation_compatible_of_priorProtectedHeadsOn facts
    S Hs Xb hf hHs hHsXb hcom hw hopenPos hpost hconfHor cv hcv hgenuine ?_
    (fun x _ hxH j hj => hf.awake_g1 _ _ j _ (Or.inr rfl) hj
      (hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E _) hxH) hwin)
  intro z hz _
  have hzVote : z ∈ Hs (M.vote_time S.E (M.opening_slot S.hc a.round)) :=
    hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E _) hz
  have hhead := Restated.PrefixFGSelectorConeAtOn.selectedSource_preceq_openingHead_of_namedFrame_history
    facts hf hHs hHsXb hX hXXb hseed hfirst hframe ready hn hselected hzVote hlo
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
    (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc a.round))) z).st.core.toHealing
    (M.vote_time S.E (M.opening_slot S.hc a.round))
    (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc a.round))) z).cache
  refine ⟨c, hc, ?_⟩
  intro nz
  obtain ⟨Tz, hTz⟩ := facts.fc.voter_filtered_block_tree_nonempty S.E nz.st.core nz.st.core.s
  obtain ⟨L, hL⟩ := facts.fc.voter_view_nonempty S.E
    (M.toHealing nz.st.core).toFG.toSG.toGoldfishStore nz.st.core.s
  obtain ⟨L', hL'⟩ := facts.fc.voter_support_view_nonempty S.E
    (M.toHealing nz.st.core).toFG.toSG.toGoldfishStore nz.st.core.s
  obtain ⟨H, hH⟩ := facts.fc.get_head_in_tree_with_layer_nonempty (M.gradeContract nz.cache)
    S.E S.hc (M.toHealing nz.st.core) Tz L L' (nz.st.core.s - 1)
  exact ⟨Tz, hTz, L, hL, L', hL', H, hH, hhead c hc Tz hTz L hL L' hL' H hH⟩

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Internal.NamedRecoveryRead
local macro "p55% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_55)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

end

/-! ## Anchors compatible with the action FG source -/

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open scoped DC

/-- If `m` can return `a` and `f a = b`, then `f <$> m` can return `b`. -/
private theorem returns_map_intro₆₃w {α β : Type} (f : α → β) (m : DC.NDRE α) (a : α) (b : β)
    (h : m ⇢ a) (hb : f a = b) : (f <$> m) ⇢ b := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image]
  exact ⟨.ok a, h, by simp [Except.map, hb]⟩

/-- Along the bundle's path `W`, if `n` is a node state of `v`'s round-`r` action read and the
    action FG source of `n` can return `some B`, then the FG source of `n` at round `r` can return
    `some B`. -/
private theorem nodeFGSource_of_actionFGSource₆₃w (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} {Hs : Int → Finset V} {Xb : Finset V} {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} {r : Round} {B : Block V} (n : M.N)
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r)
    (hsource : Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ some B) :
    Restated.Vocabulary.Internal.PhaseGrades.nodeFGSource M S n r ⇢ some B := by
  have hmem := mem_stateBeforeTime_along₆₃ hf.sorted hf.onePath
    (Restated.Vocabulary.Execution.Setup.a M S r)
  have hnAt : n ∈ Restated.Vocabulary.Proofs.HealingSurface.actionReadAt M S rho v r := ⟨_, hmem, hn⟩
  have hround : M.round_of S.hc (M.toHealing n.st.core).s = r := by
    show M.round_of S.hc (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.s = r
    rw [facts.sto.toHealing_s]
    exact Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt_round facts S rho v r n hnAt
  have h : (do
      let g ← M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
        (M.round_of S.hc (M.toHealing n.st.core).s)
      M.fg_source_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
        (M.round_of S.hc (M.toHealing n.st.core).s) g) ⇢ some B := hsource
  rw [hround] at h
  exact h

/-- Under the bundle with path `W`, if `0 < r`, round `r` is ready, `S.a r` is within the horizon,
    `p` is in the set for `domain r g0` and `w` in the set for `domain r g1`, a node state `n` of
    `p`'s round-`r` action read along `W` has a Q2 that can return `some Q` and an action FG source
    that can return `some B`, every outcome of the grade-1 store grade of `L` at `w`'s store in
    `W (strictEventIndex rho (domain r .g1))` is `true`, `L` is the erasure of a body of `p`'s store
    in `W (strictEventIndex rho (domain r .g0))` and a descendant of `p`'s finalized block there,
    and `lo ≤ opening (r − η_SG)`, then `L` and `B` are compatible. -/
private theorem anchor_compatible_actionFGSource₆₃w (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {r : Round} (hr : 0 < r)
    (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho r)
    (hactionHor : Restated.Vocabulary.Execution.Setup.a M S r ≤ rho.horizon)
    {p w : V} (hp : p ∈ Hs (M.domain S.E S.hc r .g0))
    (hwG1 : w ∈ Hs (M.domain S.E S.hc r .g1))
    {Q B L : Block V} {n : M.N}
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) p) r)
    (hselected : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ some Q)
    (hsource : Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ some B)
    (hLgrade1 : ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
      (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st r .g1 L ⇢ b → b = true)
    (hLbody : ∃ Ln : NamedBlock V, Ln.erase = L ∧
      Ln ∈ (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) p).st.bodies)
    (hFg0L : Block.Preceq (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) p).st.core.F L)
    (hlo : lo ≤ M.opening S.E S.hc (r - S.hc.η_SG)) :
    Block.compatible L B = true := by
  have hgst : lo ≤ M.early S.E S.hc r .g2 :=
    facts.gr.lo_le_early_g2_of_window_start S hr hlo
  have hg2g0 : M.domain S.E S.hc r .g2 ≤ M.domain S.E S.hc r .g0 :=
    facts.gr.domain_le_domain_g0 S r .g2
  have hpG2 : p ∈ Hs (M.domain S.E S.hc r .g2) := hHs _ _ hg2g0 hp
  have hguard := Restated.actionQ2_crossReaderBodyReadyGuard_historyOn facts
    S Hs Xb hf hHs hHsXb hr ready hp hgst n hn w hwG1 Q hselected
  have hQgrade1 := Restated.selectedG2_G1_at_read_after_cutoffOn facts
    S Hs Xb hf hHs hHsXb ready hactionHor hpG2 hwG1 n hn hselected hguard hlo
  obtain ⟨bL, hbL⟩ := facts.gr.gradeBool_nonempty S.E
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st.core.F
    S.hc.η_SG r (M.early S.E S.hc r .g1) (M.late S.E S.hc r .g1) L
  obtain ⟨bQ, hbQ⟩ := facts.gr.gradeBool_nonempty S.E
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st.core.F
    S.hc.η_SG r (M.early S.E S.hc r .g1) (M.late S.E S.hc r .g1) Q
  have hbLt : bL = true := hLgrade1 bL hbL
  have hLQ : Block.compatible L Q = true :=
    Restated.Vocabulary.Proofs.HealingSurface.graded_oneChain_at_reader facts S.E
      (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st.core))
      (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st.core.F
      S.hc.η_SG r (facts.gr.early_g1_le_late_g1 S r) bL hbL hbLt bQ hbQ (hQgrade1 bQ hbQ)
  have hmemA := mem_stateBeforeTime_along₆₃ hf.sorted hf.onePath
    (Restated.Vocabulary.Execution.Setup.a M S r)
  have hsourceNode := nodeFGSource_of_actionFGSource₆₃w facts S hf n hn hsource
  have hQB : Block.Preceq Q B :=
    Restated.Vocabulary.Proofs.HealingSurface.preceq_actionFGSource_of_actionQ2 facts S rho p r
      _ hmemA n hn hselected (Proofs.ModelProperties.Preceq_self Q) hsourceNode
  rcases compatible_cases hLQ with hLQ | hQL
  · exact compatible_of_cases (Or.inl (preceq_trans_Preceq hLQ hQB))
  · rcases Restated.Vocabulary.Proofs.HealingSurface.actionFGSource_genuineClear_or_selectedG2_named
        facts S rho p r _ hmemA n hn hselected hsource with hclear | hlocal
    · obtain ⟨_, _, _, hwalk, _, _⟩ := hclear
      obtain ⟨Ln, hLnErase, hLnG0⟩ := hLbody
      have hLtree : L ∈ (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) p).st.core.T := by
        have hcoh := (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho
          (strictEventIndex rho (M.domain S.E S.hc r .g0)) p _ (hf.onePath _).1).1.1.1
        rw [hcoh.1, ← hLnErase]
        exact Finset.mem_image_of_mem NamedBlock.erase hLnG0
      have hgstG1 : lo ≤ M.early S.E S.hc r .g1 :=
        hgst.trans (facts.gr.early_g2_le_early_g1 S.E S.hc r)
      have hforward : ∀ sender u key Head,
          ∀ I, M.interpretedInputs
            (M.gradeView (M.toHealing
              (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st.core))
            (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st.core.F
            S.hc.η_SG r (M.early S.E S.hc r .g1) sender ⇢ I → u ∈ I →
          ∀ cc, M.localCovers
            (M.gradeView (M.toHealing
              (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st.core))
            u.confirmed L ⇢ cc → cc = true →
          u.confirmed = some key →
          Block.find?
            (M.gradeView (M.toHealing
              (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st.core)).T
              key = some Head →
          Block.Preceq (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) p).st.core.F Head := by
        intro sender u key Head _ _ _ cc hcc hcct hconf hfind
        apply preceq_trans_Preceq hFg0L
        rw [hconf] at hcc
        exact facts.gr.preceq_of_localCovers_of_find cc hcc hcct hfind
      have hbelowReaders :=
        Restated.g1G0CrossReaderFinalizedBelow_of_finalitySafety_and_relayOn facts
          S Hs Xb hf hHs hHsXb hf.slashableBound hgstG1 ready.2 hwG1 hp hforward
      have hguard0 := Restated.g1G0CrossReaderBodyReadyGuard_of_finalizedBelowOn facts
        S Hs Xb hf hHs hHsXb hr hgstG1 ready.2 hwG1 hp hbelowReaders
      subst hbLt
      have hLgrade0 := Restated.storeGrade_g0_of_storeGrade_g1_cross_readerOn facts
        S rho Hs Xb hf hHs hHsXb r hlo ready.2 w p hwG1 hp L hbL hguard0
      obtain ⟨b0, hb0⟩ := facts.gr.gradeBool_nonempty S.E
        (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) p).st.core))
        (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) p).st.core.F
        S.hc.η_SG r (M.early S.E S.hc r .g0) (M.late S.E S.hc r .g0) L
      have hb0t : b0 = true := hLgrade0 b0 hb0
      subst hb0t
      have hQaction := Restated.Vocabulary.Proofs.HealingSurface.actionQ2_mem_filteredTree facts
        S rho p r _ hmemA n hn hselected
      have hFQ : Block.Preceq n.st.core.F Q := by
        have h := facts.fc.q10_filtered_F hQaction
        rw [facts.sto.Sts_toHealing_F] at h
        exact h
      have hFL : Block.Preceq n.st.core.F L := preceq_trans_Preceq hFQ hQL
      have hBclear : Restated.Vocabulary.Internal.PhaseGrades.nodeClear M S n r B ⇢ true := by
        obtain ⟨G, hG⟩ := facts.gr.read_nonempty (M.gradeContract n.cache) S.E S.hc
          (M.toHealing n.st.core) r
        have htest := facts.gr.deepest_clear_test (hwalk G hG)
        exact returns_map_intro₆₃w (fun g => g.clear B) _ G true hG htest
      have hlog0 : lo ≤ M.domain S.E S.hc r .g0 :=
        (hgst.trans (facts.gr.early_le_domain S r)).trans hg2g0
      exact Restated.relativeG0_compatible_clearSource_of_finalizedPreceq_historyOn facts
        S Hs Xb hf hr hactionHor hp hLtree hb0 hn hFL hBclear hlog0
    · subst hlocal
      exact compatible_of_cases (Or.inr hQL)

/-- Under the bundle with path `W`, if `0 < r`, round `r` is ready, `S.a r` is within the horizon,
    `p` is in the set for `domain r g0` and `w` in the set for `domain r g0 + Δ`, a node state `n`
    of `p`'s round-`r` action read along `W` has a Q2 that can return `some Q` and an action FG
    source that can return `some B`, `w`'s vote-duty read at `opening_slot r + 1`, built with an
    outcome `c` of the phase tick, has the round-`r` grade-1 frame root `root` and active prefix `L`
    under it, and `lo ≤ opening (r − η_SG)`, then `L` and `B` are compatible. -/
theorem freshAnchor_compatible_actionFGSource_after_cutoff_namedOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {r : Round} (hr : 0 < r)
    (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho r)
    (hactionHor : Restated.Vocabulary.Execution.Setup.a M S r ≤ rho.horizon)
    {p w : V} (hp : p ∈ Hs (M.domain S.E S.hc r .g0))
    (hw : w ∈ Hs (M.domain S.E S.hc r .g0 + S.E.Δ))
    {Q B root L : Block V} {n : M.N}
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) p) r)
    (hselected : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ some Q)
    (hsource : Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ some B)
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (M.toHealing (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc r + 1))) w).st.core)
      (M.vote_time S.E (M.opening_slot S.hc r + 1))
      (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc r + 1))) w).cache ⇢ c)
    (hframe :
      (M.readFrame c
        (M.toHealing (M.ns_setClock S.E
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc r + 1))) w).st
          (M.vote_time S.E (M.opening_slot S.hc r + 1))).core) r).g1 =
        some (some root))
    (hactive : M.activePrefix
      (M.get_filtered_block_tree (M.toHealing (M.ns_setClock S.E
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc r + 1))) w).st
          (M.vote_time S.E (M.opening_slot S.hc r + 1))).core).toFG)
      root = some L)
    (hlo : lo ≤ M.opening S.E S.hc (r - S.hc.η_SG)) :
    Block.compatible L B = true := by
  have hΔ := S.E.Δ_pos
  have hgst : lo ≤ M.early S.E S.hc r .g2 :=
    facts.gr.lo_le_early_g2_of_window_start S hr hlo
  have hg1Out : M.domain S.E S.hc r .g1 ≤ M.domain S.E S.hc r .g0 + S.E.Δ := by
    have h := facts.gr.domain_le_domain_g0 S r .g1
    linarith
  have hwG1 : w ∈ Hs (M.domain S.E S.hc r .g1) := hHs _ _ hg1Out hw
  have hLgrade1 := Restated.activeVoterAnchor_storeGrade_g1On facts
    S Hs Xb hf hr ready hwG1 c hc hframe hactive hgst (fun j hj => hf.tick_outcome j _ _ hj)
  have hLvote := facts.gr.activePrefix_mem _ _ _ hactive
  obtain ⟨Ln, hLnErase, hLnG0, -, -⟩ :=
    Restated.activeVoterAnchor_namedBody_at_sourceG0_and_actionOn facts
      S Hs Xb hf hHs hHsXb hr ready hactionHor hp hw c hc hframe hactive hgst (fun j hj => hf.tick_outcome j _ _ hj)
  have hFg0L : Block.Preceq
      (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) p).st.core.F L :=
    Restated.sourceG0Finalized_preceq_firstInteriorActiveOn facts
      S Hs Xb hf hHs hHsXb ready hactionHor hp hw hLvote hgst
  exact anchor_compatible_actionFGSource₆₃w facts S Hs Xb hf hHs hHsXb hr ready hactionHor
    hp hwG1 hn hselected hsource hLgrade1 ⟨Ln, hLnErase, hLnG0⟩ hFg0L hlo

/-- Under the bundle with path `W`, if `0 < r`, round `r` is ready, `S.a r` is within the horizon,
    `p` is in the set for `domain r g0` and `w` in the set for `domain r g0 + Δ`, a node state `n`
    of `p`'s round-`r` action read along `W` has a Q2 that can return `some Q` and an action FG
    source that can return `some B`, a node state `nw` of `w`'s round-`r` action read along `W` has
    the grade-1 frame root `root` and active prefix `L` under it, and `lo ≤ opening (r − η_SG)`,
    then `L` and `B` are compatible. -/
theorem activeActionAnchor_compatible_actionFGSource_after_cutoff_namedOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {r : Round} (hr : 0 < r)
    (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho r)
    (hactionHor : Restated.Vocabulary.Execution.Setup.a M S r ≤ rho.horizon)
    {p w : V} (hp : p ∈ Hs (M.domain S.E S.hc r .g0))
    (hw : w ∈ Hs (M.domain S.E S.hc r .g0 + S.E.Δ))
    {Q B root L : Block V} {n : M.N}
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) p) r)
    (hselected : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ some Q)
    (hsource : Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ some B)
    {nw : M.N}
    (hnw : nw ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) w) r)
    (hframe : (M.readFrame nw.cache (M.toHealing nw.st.core) r).g1 = some (some root))
    (hactive : M.activePrefix (Restated.Vocabulary.Internal.PhaseGrades.filteredTree M nw) root =
      some L)
    (hlo : lo ≤ M.opening S.E S.hc (r - S.hc.η_SG)) :
    Block.compatible L B = true := by
  have hΔ := S.E.Δ_pos
  have hgst : lo ≤ M.early S.E S.hc r .g2 :=
    facts.gr.lo_le_early_g2_of_window_start S hr hlo
  have hg1Out : M.domain S.E S.hc r .g1 ≤ M.domain S.E S.hc r .g0 + S.E.Δ := by
    have h := facts.gr.domain_le_domain_g0 S r .g1
    linarith
  have hwG1 : w ∈ Hs (M.domain S.E S.hc r .g1) := hHs _ _ hg1Out hw
  have hLgrade1 := Restated.activeActionAnchor_storeGrade_g1_named_historyOn facts
    S Hs Xb hf hr ready hwG1 hnw hframe hactive hgst
  obtain ⟨Ln, hLnErase, hLnG0, -, hFg0L, -⟩ :=
    Restated.activeActionAnchor_namedBody_at_sourceG0_historyOn facts
      S Hs Xb hf hHs hHsXb hr ready hactionHor hp hw hnw hframe hactive hgst
  exact anchor_compatible_actionFGSource₆₃w facts S Hs Xb hf hHs hHsXb hr ready hactionHor
    hp hwG1 hn hselected hsource hLgrade1 ⟨Ln, hLnErase, hLnG0⟩ hFg0L hlo

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Internal.NamedRecoveryRead
local macro "p59% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_59)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

end

/-! ## The confirmation witness of a same-round height row -/

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Internal.NamedRecoveryRead
local macro "p51% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_51)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p59% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_59)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

/-- The round-`r` action read computed from any node state has a node state. -/
private theorem actionReadFrom_nonempty₆₃w (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∃ n, n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r := by
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc before.st.core.toHealing
    (Restated.Vocabulary.Execution.Setup.a M S r) before.cache
  obtain ⟨st, hst⟩ := facts.dt.duties_update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc
    (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r))
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
  exact ⟨_, c, hc, st, hst, rfl⟩

/-- Along the bundle's path `W`, the chain state that a node state of `v`'s round-`r` action read
    stores for the erasure of one of its bodies `D` is the chain state derived from `D`. -/
private theorem actionRead_σ_named₆₃w (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} {Hs : Int → Finset V} {Xb : Finset V} {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} {r : Round} {n : M.N}
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r)
    {D : NamedBlock V} (hD : D ∈ n.st.bodies) :
    n.st.core.σ D.erase = M.derive_named S.E S.cfg D := by
  rw [(p51% actionReadFrom_σ₅₁) facts S _ r n hn]
  exact Restated.Vocabulary.Proofs.NamedStoreBridge.derivedView_stateBefore facts S rho _ v _
    (hf.onePath _).1 D (by rw [← (p59% actionReadFrom_bodies₅₉) facts S _ r n hn]; exact hD)

/-- Under the bundle with path `W`, if the selector cone holds for `a` with source `Cfg` and
    checkpoint `T`, the window over `X` at `blocked + 1` holds before `first`, the named frame over
    `X` holds at `blocked` up to `first − 1`, round `a.round` is ready, `b`'s signer is in the set
    for `S.a b.round` and emits `b` along `W`, `b`'s height pair is at height `blocked + 1`,
    `a.round = b.round` and `lo ≤ opening (a.round − η_SG)`, then every outcome of the FG
    confirmation witness of every node state of `b`'s signer's round-`b.round` action read along `W`
    is `some T`. -/
theorem PrefixFGSelectorConeAtOn.confirmationWitness_of_sameRound_honestHeightRow_of_frame_named
    (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {Xb X : Finset V} {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hX : ∀ t : Int, 0 ≤ t → Hs t ⊆ X) (hXXb : X ⊆ Xb)
    {start first : Nat} {blocked : Height}
    {i : Nat} {a b : NamedAttestation V} {ta tb : Time}
    {Cfg : NamedBlock V} {T : Block V}
    (hseed : Restated.PrefixFGSelectorConeAtOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs Xb start first blocked i a ta Cfg T)
    (hfirst : Restated.HeightWindowAtOn M S rho W X (blocked + 1) first)
    {Tprev : NamedBlock V} {c0 : Round}
    (hframe : Restated.NamedHeightRegimeFrameOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs X Xb blocked (first - 1) Tprev c0)
    (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho a.round)
    (hb : b.val_index ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S b.round))
    (hemit : Restated.Vocabulary.Execution.NamedRun.emits M S rho W b.val_index (Object.attest b) tb)
    (hrow : b.height_pair.erase.height? = some (blocked + 1))
    (hround : a.round = b.round)
    (hlo : lo ≤ M.opening S.E S.hc (a.round - S.hc.η_SG)) :
    ∀ nb ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S b.round)) b.val_index)
      b.round,
    ∀ o : Option (Block V),
      Restated.Vocabulary.Proofs.HealingSurface.fgConfirmationWitness M S nb ⇢ o → o = some T := by
  intro nb hnb o ho
  have hsigner : a.val_index ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S a.round) := by
    have h := hseed.signerHonest
    rw [hseed.actionTime_eq] at h
    exact h
  have hAnonneg : 0 ≤ Restated.Vocabulary.Execution.Setup.a M S a.round := by
    show 0 ≤ M.a S.hc S.E.Δ a.round
    rw [facts.sch.a_eq_confirmation_time]
    exact (facts.sch.Optimistic_proposal_time_nonneg S.E _).trans
      (facts.sch.proposal_time_le_confirmation_time S.E _)
  have hbA : b.val_index ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S a.round) := by
    rw [hround]
    exact hb
  have hbX : b.val_index ∈ X := hX _ hAnonneg hbA
  have hnb' : nb ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) b.val_index)
      a.round := by
    rw [hround]
    exact hnb
  obtain ⟨os, hos, hmap⟩ := returns_map_elim₆₃ _ _ _ ho
  obtain ⟨-, -, hwit⟩ := Restated.honestEmittedHeightRow_exactFGSelectorWitnessOn facts
    S Hs Xb X hf hbX hemit hrow nb hnb
  obtain ⟨Cfg', T', hsource', hCfgMem', -, hheight', hT', -⟩ := hwit os hos
  subst hsource'
  have hoT' : o = some T' := by
    rw [← hmap]
    simp only [Option.map_some]
    rw [actionRead_σ_named₆₃w facts S hf hnb hCfgMem', hT']
  have hcut : strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round) < first :=
    actionPrefix_lt₆₃w facts hf hseed
  have hprefix :
      strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round) ≤ first - 1 :=
    Nat.le_sub_one_of_lt hcut
  have hfrontier : (X.sup fun u => (W (first - 1) u).st.core.h_max) < blocked + 2 := by
    have hstopLt : first - 1 < first := Nat.sub_lt (Nat.zero_lt_of_lt hcut) Nat.zero_lt_one
    exact (hfirst.before _ hstopLt).trans_lt (Nat.lt_succ_self (blocked + 1))
  have hhor : Restated.Vocabulary.Execution.Setup.a M S a.round ≤ rho.horizon :=
    actionHorizon₆₃w hf hseed
  obtain ⟨na, hna⟩ := actionReadFrom_nonempty₆₃w facts S
    (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) a.val_index)
    a.round
  have hsrcA : Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S na ⇢ some Cfg.erase := by
    obtain ⟨oa, hoa⟩ := actionFGSource_nonempty₆₃w facts S na
    have hoa' := hseed.exactFGSource na hna oa hoa
    rw [hoa'] at hoa
    exact hoa
  have hPrevCfg : NamedBlock.Preceq Tprev Cfg :=
    hframe.sourceAbove a.val_index a.round hsigner hprefix hhor na hna
      Cfg (hseed.sourceMem na hna) hsrcA hseed.sourceDerivedHeight
  have hPrevCfg' : NamedBlock.Preceq Tprev Cfg' :=
    hframe.sourceAbove b.val_index a.round hbA hprefix hhor nb hnb'
      Cfg' hCfgMem' hos hheight'
  have hsourceNode := nodeFGSource_of_actionFGSource₆₃w facts S hf na hna hsrcA
  have hsourceNode' := nodeFGSource_of_actionFGSource₆₃w facts S hf nb hnb' hos
  have hcompat : Block.compatible Cfg.erase Cfg'.erase = true :=
    Restated.actionFGSources_compatible_of_namedFrameOn facts
      S Hs Xb X hf hHs hHsXb hX hXXb ready hsigner hbA na hna hsourceNode nb hnb'
        hsourceNode' (hseed.sourceMem na hna) hCfgMem' hframe hseed.sourceDerivedHeight
        hheight' hPrevCfg hPrevCfg' hprefix hfrontier hhor hlo
  have hCfgRun := Restated.actionBody_runBlock_named_historyOn facts
    S Hs Xb hf (hHsXb _ hsigner) hna (hseed.sourceMem na hna)
  have hCfg'Run := Restated.actionBody_runBlock_named_historyOn facts
    S Hs Xb hf (hHsXb _ hb) hnb hCfgMem'
  have heq : T = T' := by
    rw [hseed.checkpointDerived, hT']
    rcases compatible_cases hcompat with hpre | hpre
    · exact facts.cs.entry_eq_on_plateau S.E S.cfg
        (Restated.namedPreceq_of_runBlock_erase_preceqOn facts Hs Xb hf hCfgRun hCfg'Run hpre)
        (hseed.sourceDerivedHeight.trans hheight'.symm)
    · exact (facts.cs.entry_eq_on_plateau S.E S.cfg
        (Restated.namedPreceq_of_runBlock_erase_preceqOn facts Hs Xb hf hCfg'Run hCfgRun hpre)
        (hheight'.trans hseed.sourceDerivedHeight.symm)).symm
  rw [hoT', heq]

end

/-! ## The opening confirmation's ancestors and the clear-source inputs -/

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- Under the bundle with path `W`, if round `r` is ready, `p` is in the set for the support cutoff
    of `opening_slot r`, `C` is confirmed at that slot on `p`'s tick store before the slot's
    confirmation instant, `B.erase` is an ancestor of `C`, a node state of `p`'s round-`r` action
    read holds `B` at height `blocked + 1` descending from `Tprev`, the named frame over `X` holds
    along `W` at `blocked` up to `stop`, `S.a r` has event index at most `stop` and is within the
    horizon, the largest `h_max` over `X` in `W stop` is less than `blocked + 2`, the reader is in
    the set for the view freeze of `opening_slot r` and in `X`, and `lo ≤ early r g2`, then
    `B.erase` is in the filtered tree of the reader's store, with its clock set, before the vote
    instant of `opening_slot r + 1`. -/
theorem ancestorGenuineConfirmation_filtered_at_nextVote_of_namedFrameOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb X : Finset V) {lo : Int}
    {W : Nat → V → M.N} {Wt : Time → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hXXb : X ⊆ Xb)
    {r : Round} (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho r)
    {p : V} (hp : p ∈ Hs (M.support_cutoff S.E (M.opening_slot S.hc r)))
    {B : NamedBlock V} {C : Block V}
    {contract : M.Contract}
    (hgenuine : Restated.Vocabulary.Protocol.GenuineConfirmationWith M contract S.E S.hc
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc r))) p).st.core
        (M.confirmation_time S.E (M.opening_slot S.hc r)))
      (M.opening_slot S.hc r) C)
    (hBC : Block.Preceq B.erase C)
    {np : M.N}
    (hnp : np ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) p) r)
    (hBmem : B ∈ np.st.bodies)
    {stop : Nat} {blocked : Height} {Tprev : NamedBlock V} {c0 : Round}
    (hframe : Restated.NamedHeightRegimeFrameOn M S rho W Wt Hs X Xb blocked stop Tprev c0)
    (hBheight : (M.derive_named S.E S.cfg B).h = blocked + 1)
    (hTB : NamedBlock.Preceq Tprev B)
    (hactionPrefix : strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r) ≤ stop)
    (hfrontier : (X.sup fun u => (W stop u).st.core.h_max) < blocked + 2)
    (hactionHor : Restated.Vocabulary.Execution.Setup.a M S r ≤ rho.horizon)
    {reader : V} (hreader : reader ∈ Hs (M.view_freeze S.E (M.opening_slot S.hc r)))
    (hreaderX : reader ∈ X)
    (hlo : lo ≤ M.early S.E S.hc r .g2) :
    B.erase ∈ M.get_filtered_block_tree (M.toHealing (M.ns_setClock S.E
      (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc r + 1))) reader).st
      (M.vote_time S.E (M.opening_slot S.hc r + 1))).core).toFG := by
  have hfloor : Restated.FinalityFloorAtOn M S rho W X Xb blocked stop Tprev.erase := by
    intro v hv n hn Y hYrun hYheight hTY
    have hTYnamed : NamedBlock.Preceq Tprev Y :=
      Restated.namedPreceq_of_runBlock_erase_preceqOn facts Hs Xb hf hframe.prevRun hYrun hTY
    exact hframe.floor v hv n hn Y hYrun hYheight hTYnamed
  have hbody := Restated.ancestorGenuineConfirmation_body_at_nextVote_of_floorOn facts
    S Hs Xb X hf hHs hHsXb ready hp hgenuine hBC hnp hBmem hfloor hBheight
      (Proofs.NamedWire.erase_preceq hTB) hactionPrefix hactionHor hreader hreaderX hlo
  rw [facts.hd.Sts_setClock_bodies] at hbody
  have hvotePrefix :
      strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc r + 1)) ≤ stop :=
    (Restated.strict_lengths_mono rho
      (Restated.Vocabulary.Protocol.next_vote_time_lt_action facts S r).le).trans hactionPrefix
  rw [setClock_filtered₆₃w facts S]
  exact (hframe.fgRoot_preceq_and_filteredMem facts
    Hs hf hXXb hfrontier hreaderX hvotePrefix hbody hBheight hTB).2

/-- Under the bundle with path `W`, if `0 < r`, round `r` is ready, the named frame over `X` holds
    along `W` at `H` up to `stop`, `S.a r` has event index at most `stop` and is within the horizon,
    the largest `h_max` over `X` in `W stop` is less than `H + 2`, and `lo ≤ opening (r − η_SG)`,
    then for every `p` in the set for `S.a r` and every node state `n` of its round-`r` action read
    whose Q2 can return `some A` but not `some B.erase`, whose action FG source can return
    `some B.erase`, and which holds `B` at height `H + 1`: for every `w` in the set for the vote
    instant of `opening_slot r + 1`, `B.erase` is in the filtered tree of `w`'s store there, and
    every outcome of the anchor of `w`'s vote-duty read there is compatible with `B.erase`. -/
theorem voterAnchorSourceClearInputsMain_of_namedFrame_sourceOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb X : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hX : ∀ t : Int, 0 ≤ t → Hs t ⊆ X) (hXXb : X ⊆ Xb)
    {r : Round} (hr : 0 < r)
    (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho r)
    (_hpostPrev : S.E.t_GST ≤ Restated.Vocabulary.Execution.Setup.a M S (r - 1))
    {stop : Nat} {H : Height} {Prev : NamedBlock V} {c0 : Round}
    (hframe : Restated.NamedHeightRegimeFrameOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs X Xb H stop Prev c0)
    (hactionPrefix : strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r) ≤ stop)
    (hfrontier : (X.sup fun u => (W stop u).st.core.h_max) < H + 2)
    (hactionHor : Restated.Vocabulary.Execution.Setup.a M S r ≤ rho.horizon)
    (hlo : lo ≤ M.opening S.E S.hc (r - S.hc.η_SG)) :
    ∀ {p : V} (A : Block V) (B : NamedBlock V),
      p ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S r) →
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) p) r,
      Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ some A →
      Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ some B.erase →
      B ∈ n.st.bodies →
      (M.derive_named S.E S.cfg B).h = H + 1 →
      ¬ (Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ some B.erase) →
      (∀ w ∈ Hs (M.vote_time S.E (M.opening_slot S.hc r + 1)),
        B.erase ∈ M.get_filtered_block_tree (M.toHealing (M.ns_setClock S.E
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc r + 1))) w).st
          (M.vote_time S.E (M.opening_slot S.hc r + 1))).core).toFG) ∧
      (∀ w ∈ Hs (M.vote_time S.E (M.opening_slot S.hc r + 1)), ∀ c : M.Cache,
        M.onPhaseTick S.E S.hc
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc r + 1))) w).st.core.toHealing
          (M.vote_time S.E (M.opening_slot S.hc r + 1))
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc r + 1))) w).cache ⇢ c →
        ∀ L : Block V,
          Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S
            (M.mkNode (M.ns_setClock S.E
              (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc r + 1))) w).st
              (M.vote_time S.E (M.opening_slot S.hc r + 1)))
              (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc r + 1))) w).record c)
            (M.round_of S.hc
              (M.mkNode (M.ns_setClock S.E
                (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc r + 1))) w).st
                (M.vote_time S.E (M.opening_slot S.hc r + 1)))
                (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc r + 1))) w).record
                c).st.core.s) ⇢ L →
          Block.compatible L B.erase = true) := by
  have hgst : lo ≤ M.early S.E S.hc r .g2 :=
    facts.gr.lo_le_early_g2_of_window_start S hr hlo
  have hlopos : 0 < lo := hf.lo_pos
  have hΔ := S.E.Δ_pos
  obtain ⟨hg0, hvt, hsc, hvf, hnext, hact⟩ := Restated.openingInstants_l63 facts S r
  have hpt := facts.sch.Optimistic_proposal_time_nonneg S.E (M.opening_slot S.hc r)
  intro p A B hpAct n hn hselected hsource hBmem hBheight hnot
  have hp : p ∈ Hs (M.support_cutoff S.E (M.opening_slot S.hc r)) :=
    hHs _ _ (by linarith) hpAct
  have hpG0 : p ∈ Hs (M.domain S.E S.hc r .g0) := hHs _ _ (by linarith) hpAct
  have hTB : NamedBlock.Preceq Prev B :=
    hframe.sourceAbove p r hpAct hactionPrefix hactionHor n hn B hBmem hsource hBheight
  have hmemA := mem_stateBeforeTime_along₆₃ hf.sorted hf.onePath
    (Restated.Vocabulary.Execution.Setup.a M S r)
  rcases Restated.Vocabulary.Proofs.HealingSurface.actionFGSource_genuineClear_or_selectedG2_named
      facts S rho p r _ hmemA n hn hselected hsource with hclear | hlocal
  · obtain ⟨C, hgenuine, -, -, -, hBC⟩ := hclear
    have hidx : strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r) =
        strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc r)) :=
      congrArg (strictEventIndex rho) (facts.sch.a_eq_confirmation_time S.hc S.E r)
    rw [hidx] at hgenuine
    have hnextT : ∀ w ∈ Hs (M.vote_time S.E (M.opening_slot S.hc r + 1)),
        B.erase ∈ M.get_filtered_block_tree (M.toHealing (M.ns_setClock S.E
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc r + 1))) w).st
          (M.vote_time S.E (M.opening_slot S.hc r + 1))).core).toFG := by
      intro w hw
      exact Restated.ancestorGenuineConfirmation_filtered_at_nextVote_of_namedFrameOn facts
        S Hs Xb X hf hHs hHsXb hXXb ready hp hgenuine hBC hn hBmem hframe hBheight hTB
          hactionPrefix hfrontier hactionHor (hHs _ _ (by linarith) hw)
          (hX _ (by linarith) hw) hgst
    refine ⟨hnextT, ?_⟩
    intro w hw c hc L hanchor
    have hmemV := mem_stateBeforeTime_along₆₃ hf.sorted hf.onePath
      (M.vote_time S.E (M.opening_slot S.hc r + 1))
    rcases Restated.Vocabulary.Proofs.HealingSurface.voterAnchorAt_cases facts S rho w
        (M.opening_slot S.hc r + 1) _ ⟨_, hmemV, c, hc, rfl⟩ L hanchor with hroot | hactive
    · refine compatible_of_cases (Or.inl ?_)
      rw [hroot]
      refine preceq_eq_true_iff_Preceq.mp (facts.fc.preceq_get_fg_root_of_mem_filtered ?_)
      rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
      exact hnextT w hw
    · obtain ⟨root, Anchor, hframeL, hactiveL, hanchorL⟩ := hactive
      subst hanchorL
      have hroundDuty : M.round_of S.hc
          (M.mkNode (M.ns_setClock S.E
            (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc r + 1))) w).st
            (M.vote_time S.E (M.opening_slot S.hc r + 1)))
            (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc r + 1))) w).record
            c).st.core.s = r := by
        rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.hd.Sts_setClock_core_s, facts.sch.slotOf_vote_time]
        exact facts.gr.HealingLemmas_round_of_opening_succ S.hc r
      rewrite [hroundDuty, facts.nd.mkNode_cache, facts.nd.mkNode_st] at hframeL; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at hframeL
      rewrite [facts.nd.mkNode_st] at hactiveL; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at hactiveL
      have hwOut : w ∈ Hs (M.domain S.E S.hc r .g0 + S.E.Δ) :=
        hHs _ _ (by linarith) hw
      exact Restated.freshAnchor_compatible_actionFGSource_after_cutoff_namedOn facts
        S Hs Xb hf hHs hHsXb hr ready hactionHor hpG0 hwOut hn hselected hsource
          c hc hframeL hactiveL hlo
  · exact False.elim (hnot (by rw [hlocal]; exact hselected))

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Internal.NamedRecoveryRead
local macro "p55% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_55)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p59% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_59)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

end

/-! ## The source round's SG emissions -/

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Internal.NamedRecoveryRead
local macro "rsh% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.Grades.RecoveryInitialSourceNamedHistory)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))
local macro "p48b% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_48b)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p59% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_59)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

/-- For every outcome `g` of the round-`r` grade read of a node state `n`, the anchor of `g` is the
    FG root of `n`'s store, or the active prefix `A` of the grade-1 entry `root` of `n`'s frame for
    round `r` in `n`'s filtered tree. -/
private theorem actionAnchor_cases_named_history₆₃w (facts : Record.Facts M) (S : Setup V)
    (n : M.N) (r : Round) :
    ∀ g, Restated.Vocabulary.Internal.PhaseGrades.nodeRead M S n r ⇢ g →
      g.anchor = M.get_fg_root (M.toHealing n.st.core).toFG ∨
      ∃ root A,
        (M.readFrame n.cache (M.toHealing n.st.core) r).g1 = some (some root) ∧
        M.activePrefix (Restated.Vocabulary.Internal.PhaseGrades.filteredTree M n) root = some A ∧
        g.anchor = A := by
  intro g hg
  obtain ⟨a0, ha0⟩ := facts.gr.anchor_nonempty S.E S.hc (M.toHealing n.st.core) r
    (M.readFrame n.cache (M.toHealing n.st.core) r).g1
  have hga := facts.nd.ModelProperties_gradeContract_read_anchor n.cache S.E S.hc
    (M.toHealing n.st.core) r g hg a0 ha0
  rcases facts.gr.anchor_cases S.E S.hc _ _ _ a0 ha0 with
    hroot0 | ⟨root, L, hframe, hactive, haL⟩
  · exact Or.inl (by rw [hga, hroot0])
  · exact Or.inr ⟨root, L, hframe, hactive, by rw [hga, haL]⟩

/-- Under the bundle with path `W` and the committee majorities, if the selector cone holds for `a`
    with source `Cfg` and checkpoint `T`, the window over `X` at `blocked + 1` holds before `first`,
    the named frame over `X` holds at `blocked` up to `first − 1` from `c0 ≤ a.round`, round
    `a.round` is ready, `t_GST ≤ S.a (a.round − 1)` and `lo ≤ opening (a.round − η_SG)`, then for
    every member `w` of the set for `S.a a.round` that emits its round-`a.round` attestation along
    `W`, every outcome of the SG vote of each node state of its action read is compatible with `T`. -/
theorem PrefixFGSelectorConeAtOn.sgEmissionsCompatible_of_source_of_frame_named
    (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {Xb X : Finset V} {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hX : ∀ t : Int, 0 ≤ t → Hs t ⊆ X) (hXXb : X ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {start first : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg Tprev : NamedBlock V} {T : Block V} {c0 : Round}
    (hseed : Restated.PrefixFGSelectorConeAtOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs Xb start first blocked i a ta Cfg T)
    (hfirst : Restated.HeightWindowAtOn M S rho W X (blocked + 1) first)
    (hframe : Restated.NamedHeightRegimeFrameOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs X Xb blocked (first - 1) Tprev c0)
    (_hc0 : c0 ≤ a.round)
    (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho a.round)
    (hpostPrev : S.E.t_GST ≤ Restated.Vocabulary.Execution.Setup.a M S (a.round - 1))
    (hlo : lo ≤ M.opening S.E S.hc (a.round - S.hc.η_SG)) :
    Restated.HonestSGEmissionsCompatibleAtRoundOn M S rho W
      (fun t => W (strictEventIndex rho t)) Hs a.round T := by
  have hlopos : 0 < lo := hf.lo_pos
  have hΔ := S.E.Δ_pos
  have hactionBefore :
      strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round) < first :=
    actionPrefix_lt₆₃w facts hf hseed
  have hprefix :
      strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round) ≤ first - 1 :=
    Nat.le_sub_one_of_lt hactionBefore
  have hfrontier : (X.sup fun u => (W (first - 1) u).st.core.h_max) < blocked + 2 := by
    have hstopLt : first - 1 < first :=
      Nat.sub_lt (Nat.zero_lt_of_lt hactionBefore) Nat.zero_lt_one
    exact (hfirst.before _ hstopLt).trans_lt (Nat.lt_succ_self (blocked + 1))
  have hhor : Restated.Vocabulary.Execution.Setup.a M S a.round ≤ rho.horizon :=
    actionHorizon₆₃w hf hseed
  have hsigner : a.val_index ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S a.round) := by
    have h := hseed.signerHonest
    rw [hseed.actionTime_eq] at h
    exact h
  have hTCfg : Block.Preceq T Cfg.erase := by
    rw [hseed.checkpointDerived]
    exact facts.csAdded.derive_named_T_h_preceq S.E S.cfg Cfg
  have hmemA := mem_stateBeforeTime_along₆₃ hf.sorted hf.onePath
    (Restated.Vocabulary.Execution.Setup.a M S a.round)
  have hca := Restated.Vocabulary.Proofs.HealingSurface.opening_confirmation_time_eq_action facts S
    a.round
  obtain ⟨na, hna⟩ := actionReadFrom_nonempty₆₃w facts S
    (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) a.val_index)
    a.round
  have hsrcA : Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S na ⇢ some Cfg.erase := by
    obtain ⟨oa, hoa⟩ := actionFGSource_nonempty₆₃w facts S na
    have hoa' := hseed.exactFGSource na hna oa hoa
    rw [hoa'] at hoa
    exact hoa
  have hCfgMem : Cfg ∈ na.st.bodies := hseed.sourceMem na hna
  obtain ⟨A, hA⟩ : ∃ A : Block V,
      Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S na a.round ⇢ some A := by
    obtain ⟨A2, hA2⟩ := facts.dt.grade2_block_with_nonempty (M.gradeContract na.cache) S.E S.hc
      (M.toHealing na.st.core) (M.round_of S.hc (M.toHealing na.st.core).s)
    obtain ⟨o, ho⟩ := facts.dt.fg_source_with_nonempty (M.gradeContract na.cache) S.E S.hc
      (M.toHealing na.st.core) (M.round_of S.hc (M.toHealing na.st.core).s) A2
    have hoEq : o = some Cfg.erase :=
      hseed.exactFGSource na hna o (returns_bind_intro₆₃w _ _ A2 o hA2 ho)
    have hround : M.round_of S.hc (M.toHealing na.st.core).s = a.round := by
      show M.round_of S.hc (M.toHealing na.st.core).toFG.toSG.toGoldfishStore.s = a.round
      rw [facts.sto.toHealing_s]
      exact Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt_round facts S rho a.val_index
        a.round na ⟨_, hmemA, hna⟩
    rw [hround] at hA2 ho
    obtain ⟨g0, hg0r⟩ := facts.gr.read_nonempty (M.gradeContract na.cache) S.E S.hc
      (M.toHealing na.st.core) a.round
    obtain ⟨A, hAeq⟩ := facts.dt.read_Q2_isSome_of_fg_source_with_grade2
      (M.gradeContract na.cache) S.E S.hc (M.toHealing na.st.core) a.round A2 hA2 o ho hoEq
      g0 hg0r
    exact ⟨A, returns_map_intro₆₃w (fun g : DecoupledConsensusModel.Protocol.GradeRead V => g.Q2)
      _ g0 (some A) hg0r hAeq⟩
  have hr : 0 < a.round := Restated.selectedQ2_round_pos_named_historyOn facts S Hs Xb hf hna hA
  have hgst : lo ≤ M.early S.E S.hc a.round .g2 :=
    facts.gr.lo_le_early_g2_of_window_start S hr hlo
  obtain ⟨hg0, hvt, hsc, hvf, hnext, hact⟩ := Restated.openingInstants_l63 facts S a.round
  have hpt := facts.sch.Optimistic_proposal_time_nonneg S.E (M.opening_slot S.hc a.round)
  have hsignerG0 : a.val_index ∈ Hs (M.domain S.E S.hc a.round .g0) :=
    hHs _ _ (by linarith) hsigner
  have hTprevCfg : NamedBlock.Preceq Tprev Cfg :=
    hframe.sourceAbove a.val_index a.round hsigner hprefix hhor na hna
      Cfg hCfgMem hsrcA hseed.sourceDerivedHeight
  have close
      (hfiltered : ∀ w, w ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S a.round) →
        ∀ nw ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) w) a.round,
        Cfg.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M nw)
      (hgenuineCompat : ∀ w, w ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S a.round) →
        ∀ cv : M.Cache,
        M.onPhaseTick S.E S.hc
          (W (strictEventIndex rho
            (M.confirmation_time S.E (M.opening_slot S.hc a.round))) w).st.core.toHealing
          (M.confirmation_time S.E (M.opening_slot S.hc a.round))
          (W (strictEventIndex rho
            (M.confirmation_time S.E (M.opening_slot S.hc a.round))) w).cache ⇢ cv →
        ∀ C,
        Restated.Vocabulary.Protocol.GenuineConfirmationWith M (M.gradeContract cv)
          S.E S.hc (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
            (W (strictEventIndex rho
              (M.confirmation_time S.E (M.opening_slot S.hc a.round))) w).st.core
            (M.confirmation_time S.E (M.opening_slot S.hc a.round)))
          (M.opening_slot S.hc a.round) C →
        Block.compatible Cfg.erase C = true) :
      Restated.HonestSGEmissionsCompatibleAtRoundOn M S rho W
        (fun t => W (strictEventIndex rho t)) Hs a.round T := by
    intro w hw n hn0 D hD hemit
    show ∀ A2 : Option (Block V),
      M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
        (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ A2 →
      ∀ G : Block V, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
        (M.round_of S.hc (M.toHealing n.st.core).s) A2 ⇢ G →
      G.compatible T = true
    intro A2 hA2 G hG
    have hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) w) a.round :=
      hn0
    have hnAt : n ∈ Restated.Vocabulary.Proofs.HealingSurface.actionReadAt M S rho w a.round :=
      ⟨_, hmemA, hn⟩
    have hwOut : w ∈ Hs (M.domain S.E S.hc a.round .g0 + S.E.Δ) :=
      hHs _ _ (by linarith) hw
    have hwG1 : w ∈ Hs (M.domain S.E S.hc a.round .g1) :=
      hHs _ _ (facts.gr.domain_le_a S a.round .g1) hw
    have hrootCfg : Block.Preceq (M.get_fg_root (M.toHealing n.st.core).toFG) Cfg.erase :=
      preceq_eq_true_iff_Preceq.mp
        (facts.fc.preceq_get_fg_root_of_mem_filtered (hfiltered w hw n hn))
    have hrootT : Block.compatible (M.get_fg_root (M.toHealing n.st.core).toFG) T = true :=
      (rsh% compatible_with_checkpoint_below_named_history)
        (compatible_of_cases (Or.inl hrootCfg)) hTCfg
    obtain ⟨g, hg⟩ := facts.gr.read_nonempty (M.gradeContract n.cache) S.E S.hc
      (M.toHealing n.st.core) a.round
    have hgR : Restated.Vocabulary.Internal.PhaseGrades.nodeRead M S n a.round ⇢ g := hg
    have hanchorCfg : Block.compatible g.anchor Cfg.erase = true := by
      rcases actionAnchor_cases_named_history₆₃w facts S n a.round g hgR with
        hroot | ⟨root, L, hframeL, hactiveL, hanchorL⟩
      · rw [hroot]
        exact compatible_of_cases (Or.inl hrootCfg)
      · rw [hanchorL]
        exact Restated.activeActionAnchor_compatible_actionFGSource_after_cutoff_namedOn facts
          S Hs Xb hf hHs hHsXb hr ready hhor hsignerG0 hwOut hna hA hsrcA hn
            hframeL hactiveL hlo
    have hanchorT : Block.compatible g.anchor T = true :=
      (rsh% compatible_with_checkpoint_below_named_history) hanchorCfg hTCfg
    have hliveT : Block.compatible n.st.core.live_confirmed T = true := by
      rcases Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt_liveConfirmed_genuine_or_fgRoot
          facts S rho w a.round _ hmemA n hn with ⟨C, hgenuine, hC⟩ | ⟨R, hRroot, hRlive⟩
      · rw [← hC]
        obtain ⟨cn, hcn, stn, hstn, hneq⟩ := hn
        have hcache : n.cache = cn := by
          subst hneq
          exact facts.nd.mkNode_cache _ _ _
        rw [hcache] at hgenuine
        rw [← hca] at hcn hgenuine
        have hCCfg : Block.compatible C Cfg.erase = true :=
          compatible_of_cases (compatible_cases (hgenuineCompat w hw cn hcn C hgenuine)).symm
        exact (rsh% compatible_with_checkpoint_below_named_history) hCCfg hTCfg
      · rw [← hRlive, hRroot,
          ← Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt_fgRoot_eq_openingConfStore facts
            S rho w a.round _ hmemA n hn]
        exact hrootT
    rcases Restated.Vocabulary.Proofs.HealingSurface.actionSGBlockAt_tiers facts S rho w a.round
        n hnAt g hgR A2 hA2 G hG with
      hwalk | ⟨Q, hQ, hout⟩ | ⟨_, _, hout⟩ | ⟨_, _, hout⟩
    · exact (rsh% compatible_ancestor_left_named_history) hwalk.2.1 hliveT
    · rw [hout]
      have hsel : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n a.round ⇢ some Q :=
        returns_map_intro₆₃w (fun g : DecoupledConsensusModel.Protocol.GradeRead V => g.Q2)
          _ g (some Q) hgR hQ
      have hanc : Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n a.round ⇢ g.anchor :=
        returns_map_intro₆₃w (fun g : DecoupledConsensusModel.Protocol.GradeRead V => g.anchor)
          _ g g.anchor hgR rfl
      exact (rsh% compatible_ancestor_left_named_history)
        (Restated.actionQ2_preceq_actionAnchorOn facts S Hs Xb hf hHs hHsXb hr hhor hwG1
          hlo n hn hsel g.anchor hanc)
        hanchorT
    · rw [hout]
      exact hrootT
    · rw [hout]
      exact hanchorT
  by_cases hlocal :
      Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S na a.round ⇢ some Cfg.erase
  · have hretained := Restated.sameRoundSourceQ2Retained_of_namedFrameOn facts
      S Hs Xb X hf hHs hHsXb hX hXXb ready hsigner na hna hlocal hsrcA
        hCfgMem hframe hseed.sourceDerivedHeight hprefix hfrontier hhor hgst
    apply close (fun w hw nw hnw => (hretained w (hHs _ _ (by linarith) hw)).2.2 nw hnw)
    intro w hw cv hcv C hgenuine
    exact hseed.selectedSource_compatible_genuineOpening_of_namedFrame_history facts
      hf hHs hHsXb hX hXXb hcom hfirst hframe ready hna hlocal
        (hHs _ _ (by linarith) hw) cv hcv hgenuine hlo
  · rcases Restated.Vocabulary.Proofs.HealingSurface.actionFGSource_genuineClear_or_selectedG2_named
        facts S rho a.val_index a.round _ hmemA na hna hA hsrcA with hclear | hsourceQ2
    · obtain ⟨C0, hgenuine0, -, -, -, hCfgC0⟩ := hclear
      obtain ⟨hnextT, -⟩ := Restated.voterAnchorSourceClearInputsMain_of_namedFrame_sourceOn facts
        S Hs Xb X hf hHs hHsXb hX hXXb hr ready hpostPrev hframe hprefix hfrontier hhor hlo
          A Cfg hsigner na hna hA hsrcA hCfgMem hseed.sourceDerivedHeight hlocal
      have hfiltered : ∀ w, w ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S a.round) →
          ∀ nw ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
            (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) w) a.round,
          Cfg.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M nw := by
        intro w hw nw hnw
        have hwVote : w ∈ Hs (M.vote_time S.E (M.opening_slot S.hc a.round + 1)) :=
          hHs _ _ (by linarith) hw
        have hwX : w ∈ X := hX _ (by linarith) hw
        have hbody := Restated.actionBody_at_action_of_nextVoteFilteredOn facts
          S Hs Xb hf (hHsXb _ hsigner) hna hCfgMem (hHsXb _ hw) (hnextT w hwVote) nw hnw
        rw [(p59% actionReadFrom_bodies₅₉) facts S _ a.round nw hnw] at hbody
        have hout := hframe.fgRoot_preceq_and_filteredMem facts
          Hs hf hXXb hfrontier hwX hprefix hbody hseed.sourceDerivedHeight hTprevCfg
        show Cfg.erase ∈ M.get_filtered_block_tree (M.toHealing nw.st.core).toFG
        rw [(p48b% actionReadFrom_filtered₄₈b) facts S _ a.round nw hnw]
        exact hout.2
      apply close hfiltered
      intro w hw cv hcv C hgenuine
      have hpost : lo ≤ M.proposal_time S.E (M.opening_slot S.hc a.round) := by
        have hlog1 : lo ≤ M.domain S.E S.hc a.round .g1 :=
          hgst.trans ((facts.gr.early_le_domain S a.round).trans
            (facts.gr.domain_g2_le_domain_g1 S a.round))
        rw [facts.gr.Sts_domain_g1_eq_opening, facts.gr.opening_eq_proposal_time] at hlog1
        exact hlog1
      have hconfHor : M.confirmation_time S.E (M.opening_slot S.hc a.round) ≤ rho.horizon := by
        rw [hca]
        exact hhor
      have hsignerConf : a.val_index ∈
          Hs (M.confirmation_time S.E (M.opening_slot S.hc a.round)) := by
        rw [hca]
        exact hsigner
      have hwConf : w ∈ Hs (M.confirmation_time S.E (M.opening_slot S.hc a.round)) := by
        rw [hca]
        exact hw
      obtain ⟨ca, hcna, sta, hsta, hneqa⟩ := hna
      have hcache : na.cache = ca := by
        subst hneqa
        exact facts.nd.mkNode_cache _ _ _
      rw [hcache] at hgenuine0
      rw [← hca] at hcna hgenuine0
      have hcompat := Restated.sameSlot_genuine_compatible_after_gstOn facts
        S Hs Xb hf hHs hHsXb hsignerConf hwConf hpost hconfHor ca hcna hgenuine0
          cv hcv hgenuine
      exact (rsh% compatible_ancestor_left_named_history) hCfgC0 hcompat
    · exact False.elim (hlocal (by rw [hsourceQ2]; exact hA))

end

/-! ## Checkpoint protection at the first interior slot -/

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open scoped DC

local macro "p59% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_59)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

set_option linter.unusedVariables false

omit [DecidableEq V] [Fintype V] in
/-- `m >>= k` can return `b` exactly when `m` can return some `a` and `k a` can return `b`. -/
private theorem returns_bind_iff₆₃x {α β : Type} (m : DC.NDRE α) (k : α → DC.NDRE β)
    (b : β) : (m >>= k) ⇢ b ↔ ∃ a, m ⇢ a ∧ k a ⇢ b := by
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

/-- Along the bundle's path `W`, if `n` is a node state of `v`'s round-`r` action read and the
    action FG source of `n` can return `some B`, then the Q2 of `n` at round `r` can return `some A`
    for some block `A`. -/
private theorem nodeQ2_some_of_actionFGSource₆₃x (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} {Hs : Int → Finset V} {Xb : Finset V} {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} {r : Round} {B : Block V} (n : M.N)
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r)
    (hsource : Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ some B) :
    ∃ A : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ some A := by
  have hsrc0 := nodeFGSource_of_actionFGSource₆₃w facts S hf n hn hsource
  unfold Restated.Vocabulary.Internal.PhaseGrades.nodeFGSource at hsrc0
  obtain ⟨A2, hA2, hsrc⟩ := (returns_bind_iff₆₃x _ _ _).1 hsrc0
  obtain ⟨Q2, hA2Q, -⟩ := facts.dt.fg_source_with_some _ _ _ _ _ _ hsrc rfl
  subst hA2Q
  obtain ⟨G, hG⟩ := facts.gr.read_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) r
  have hGQ : G.Q2 = some Q2 :=
    (facts.dt.grade2_block_with_eq_read_Q2 _ _ _ _ _ G hG _ hA2).symm
  have h : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ G.Q2 :=
    returns_map_intro₆₃w (fun g : GradeRead V => g.Q2) _ G _ hG rfl
  rw [hGQ] at h
  exact ⟨Q2, h⟩

/-- Under the bundle with path `W`, if the selector cone holds for `a` with source `Cfg` and
    checkpoint `T`, the window over `X` at `blocked + 1` holds before `first`, the named frame over
    `X` holds at `blocked` up to `first − 1` from `c0 ≤ a.round`, round `a.round` is ready,
    `t_GST ≤ S.a (a.round − 1)` and `lo ≤ opening (a.round − η_SG)`, then every head of every
    vote-duty read at `opening_slot a.round + 1` of a member of the set for that slot's vote instant
    is a descendant of `T`, and those votes along `W` form a cone over `T`. -/
theorem PrefixFGSelectorConeAtOn.checkpointProtection_firstInterior_of_frame_named
    (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {Xb X : Finset V} {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hX : ∀ t : Int, 0 ≤ t → Hs t ⊆ X) (hXXb : X ⊆ Xb)
    {start first : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg Tprev : NamedBlock V} {T : Block V} {c0 : Round}
    (hseed : Restated.PrefixFGSelectorConeAtOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs Xb start first blocked i a ta Cfg T)
    (hfirst : Restated.HeightWindowAtOn M S rho W X (blocked + 1) first)
    (hframe : Restated.NamedHeightRegimeFrameOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs X Xb blocked (first - 1) Tprev c0)
    (hc0 : c0 ≤ a.round)
    (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho a.round)
    (hpostPrev : S.E.t_GST ≤ Restated.Vocabulary.Execution.Setup.a M S (a.round - 1))
    (hlo : lo ≤ M.opening S.E S.hc (a.round - S.hc.η_SG)) :
    (∀ w ∈ Hs (M.vote_time S.E (M.opening_slot S.hc a.round + 1)), ∀ c : M.Cache,
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc a.round + 1))) w).st.core.toHealing
        (M.vote_time S.E (M.opening_slot S.hc a.round + 1))
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc a.round + 1))) w).cache ⇢ c →
      let n := M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc a.round + 1))) w).st
          (M.vote_time S.E (M.opening_slot S.hc a.round + 1)))
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc a.round + 1))) w).record c
      ∀ Tr : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ Tr →
      ∀ L : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
      ∀ L' : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
      ∀ H : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
          (M.toHealing n.st.core) Tr L L' (n.st.core.s - 1) ⇢ H →
        Block.Preceq T H) ∧
      Restated.NamedHonestVotesConeOn M S rho W Hs Xb (M.opening_slot S.hc a.round + 1)
        (fun Y => Block.Preceq T Y) := by
  have hΔ := S.E.Δ_pos
  have hactionBefore : strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round) < first :=
    actionPrefix_lt₆₃w facts hf hseed
  have hprefix : strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round) ≤ first - 1 :=
    Nat.le_sub_one_of_lt hactionBefore
  have hfrontier : (X.sup fun u => (W (first - 1) u).st.core.h_max) < blocked + 2 := by
    have hstopLt : first - 1 < first :=
      Nat.sub_lt (Nat.zero_lt_of_lt hactionBefore) Nat.zero_lt_one
    exact (hfirst.before _ hstopLt).trans_lt (Nat.lt_succ_self (blocked + 1))
  have hhor : Restated.Vocabulary.Execution.Setup.a M S a.round ≤ rho.horizon := actionHorizon₆₃w hf hseed
  have hsigner : a.val_index ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S a.round) := by
    have h := hseed.signerHonest
    rw [hseed.actionTime_eq] at h
    exact h
  have hTCfg : Block.Preceq T Cfg.erase := by
    rw [hseed.checkpointDerived]
    exact facts.csAdded.derive_named_T_h_preceq S.E S.cfg Cfg
  obtain ⟨n, hn⟩ := actionReadFrom_nonempty₆₃w facts S
    (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) a.val_index) a.round
  have hsrc : Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ some Cfg.erase := by
    obtain ⟨oa, hoa⟩ := actionFGSource_nonempty₆₃w facts S n
    have hoa' := hseed.exactFGSource n hn oa hoa
    rw [hoa'] at hoa
    exact hoa
  obtain ⟨A, hA⟩ := nodeQ2_some_of_actionFGSource₆₃x facts S hf n hn hsrc
  by_cases hlocal : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n a.round ⇢ some Cfg.erase
  · exact hseed.selectedSource_firstInterior_of_frame_named_history facts
      hf hHs hHsXb hX hXXb hfirst hframe ready hn hlocal hlo
  · have hmemA := mem_stateBeforeTime_along₆₃ hf.sorted hf.onePath (Restated.Vocabulary.Execution.Setup.a M S a.round)
    rcases Restated.Vocabulary.Proofs.HealingSurface.actionFGSource_genuineClear_or_selectedG2_named
        facts S rho a.val_index a.round _ hmemA n hn hA hsrc with
      ⟨C, hgenuine, -, -, -, hCfgC⟩ | hsourceQ2
    · have hr : 0 < a.round := Restated.selectedQ2_round_pos_named_historyOn facts S Hs Xb hf hn hA
      have hgst : lo ≤ M.early S.E S.hc a.round .g2 :=
        facts.gr.lo_le_early_g2_of_window_start S hr hlo
      obtain ⟨hg0, hvt, hsc, hvf, hnext, hact⟩ := Restated.openingInstants_l63 facts S a.round
      have hmain := Restated.voterAnchorSourceClearInputsMain_of_namedFrame_sourceOn facts
        S Hs Xb X hf hHs hHsXb hX hXXb hr ready hpostPrev hframe hprefix hfrontier hhor hlo
          A Cfg hsigner n hn hA hsrc (hseed.sourceMem n hn) hseed.sourceDerivedHeight hlocal
      have hca := Restated.Vocabulary.Proofs.HealingSurface.opening_confirmation_time_eq_action
        facts S a.round
      rw [← hca] at hgenuine
      rcases Restated.genuineClear_nextVoteCone_or_heightProgressThrough_of_mainInputsOn facts S Hs Xb hf hHs hHsXb ready hsigner hgenuine hCfgC hn
          (hseed.sourceMem n hn) hseed.sourceDerivedHeight hhor hmain.1 hmain.2
          (through := M.vote_time S.E (M.opening_slot S.hc a.round + 1)) (le_refl _) hgst with
        hprogress | hprotected
      · obtain ⟨w, hw, u, hu, hmax⟩ := hprogress
        exfalso
        have hpt := facts.sch.Optimistic_proposal_time_nonneg S.E (M.opening_slot S.hc a.round)
        have hwX : w ∈ X := hX (M.vote_time S.E (M.opening_slot S.hc a.round + 1)) (by linarith) hw
        have huAction : u < Restated.Vocabulary.Execution.Setup.a M S a.round := by linarith
        have hcursor : inclusiveEventIndex rho u ≤ strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round) := by
          rw [strictEventIndex_eq_inclusiveEventIndex_pred]
          exact inclusiveEventIndex_mono rho (Int.le_sub_one_iff.mpr huAction)
        have hmono : (W (inclusiveEventIndex rho u) w).st.core.h_max ≤
            (W (first - 1) w).st.core.h_max :=
          (p59% hMax_mono_along₅₉) facts S hf.onePath w (hcursor.trans hprefix)
        have hsup : (W (first - 1) w).st.core.h_max ≤
            (X.sup fun u => (W (first - 1) u).st.core.h_max) :=
          Finset.le_sup (f := fun u => (W (first - 1) u).st.core.h_max) hwX
        have hmax' : blocked + 1 + 2 ≤ (W (inclusiveEventIndex rho u) w).st.core.h_max := hmax
        have hnat : ∀ x y : Nat, x + 1 + 2 ≤ y → y < x + 2 → False := by
          intro x y h1 h2
          omega
        exact hnat _ _ (hmax'.trans (hmono.trans hsup)) hfrontier
      · refine ⟨?_, ?_⟩
        · intro w hw c hc nw Tr hTr L hL L' hL' H hH
          exact preceq_trans_Preceq hTCfg (hprotected.1 w hw c hc Tr hTr L hL L' hL' H hH)
        · intro w hw hcommittee
          obtain ⟨Y, hCfgY, hYrun, hYemit⟩ := hprotected.2 w hw hcommittee
          exact ⟨Y, preceq_trans_Preceq hTCfg hCfgY, hYrun, hYemit⟩
    · exact False.elim (hlocal (hsourceQ2 ▸ hA))

end

end DecoupledConsensusModel.Sts.Restated
