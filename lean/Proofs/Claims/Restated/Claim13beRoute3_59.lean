import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13beRoute3_45
import Proofs.Claims.Restated.Claim13beRoute3_45b
import Proofs.Claims.Restated.Claim13beRoute3_46
import Proofs.Claims.Restated.Claim13beRoute3_47b
import Proofs.Claims.Restated.Claim13beRoute3_48
import Proofs.Claims.Restated.Claim13beRoute3_48b
import Proofs.Claims.Restated.Claim13beRoute3_50
import Proofs.Claims.Restated.Claim13beRoute3_51
import Proofs.Claims.Restated.Claim13beRoute3_53b
import Proofs.Claims.Restated.Claim13beRoute3_54
import Proofs.Claims.Restated.Claim13beRoute3_56
import Proofs.Claims.Restated.Claim13beRoute3_56b
import Proofs.Claims.Restated.Claim13beRoute3_58
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Proofs.Claims.Restated.Vocabulary_Execution_OutageInputs
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_Adoption
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_Agreement
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_Confirmation
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_SGRepresentation
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_GradeFormsProducers
import Proofs.Vocabulary.Protocol.Grades.RelativeSupporter
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_TickBridges
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_Action
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_PostHealingReuse
import Proofs.Claims.Restated.Vocabulary_Protocol_Store_BoundaryRows
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_42c
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.RunVocabulary
import Model.Conditions.Vocabulary_Internal_Definitions_NamedLifecycle
import Model.Conditions.Vocabulary_Internal_Definitions_NamedOutageEntry
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGradeQueries
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
import Model.Conditions.Vocabulary_Internal_Internal_GradeReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedHeadReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedActionReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_MajoritySG_ForkChoice
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_ModelVocabulary_Healing_Schedule
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Vocabulary.Protocol.Grades
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_FinalityFilterRetention
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Conditions.Vocabulary_Protocol_Grades_RelativeCrossReader
import Model.Record.Wiring

/-!
# Grade-1 blocks under a ceiling, and the next-vote head

Theorems over a model `M : Record.Model V` and its facts `facts : Record.Facts M`, read along the
path `W` that the bundle `AdmissibleFieldsOn` binds: a selected Q2 has grade 2 at the grade-2 domain
read, the voter head under `NamedNextVoteAdoptionOn`, grade-1 blocks bounded by a ceiling of the
previous round's action blocks, and the bodies held at action and vote-duty reads.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

open scoped DC
/-! ### Helpers along the path `W` -/

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Proofs.HealingLemmas

/-- In a run sorted by key, the worlds strictly before the instant `t` are the worlds before the
    event whose index is `strictEventIndex rho t`. -/
private theorem stateBeforeTime_eq_strict₅₉ (S : Setup V) (rho : Record.Run V)
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

/-- In a run sorted by key, the world of a path `W` before the event whose index is
    `strictEventIndex rho t` is a world strictly before the instant `t`. -/
private theorem mem_stateBeforeTime_along₅₉ {S : Setup V} {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (t : Time) :
    W (strictEventIndex rho t) ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t := by
  rw [stateBeforeTime_eq_strict₅₉ S rho hsorted]
  exact (hW _).1

/-- For every path `W` of `rho`, `W (m + k)` is among the worlds the events `m` to `m + k - 1` of
    `rho` lead to from `W m`. -/
private theorem onePath_reach₅₉ {S : Setup V} {rho : Record.Run V}
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
private theorem onePath_slice₅₉ {S : Setup V} {rho : Record.Run V}
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) {m n : Nat}
    (hmn : m ≤ n) :
    W n ∈ ((rho.events.drop m).take (n - m)).foldlM (Record.worldStepOf M S) (W m) := by
  have h := onePath_reach₅₉ W hW m (n - m)
  rwa [Nat.add_sub_of_le hmn] at h

/-- Along a path `W` of a run, for `j ≤ n`, the finalized block of `v`'s core store in `W j` is an
    ancestor of the finalized block of `v`'s core store in `W n`. -/
private theorem F_mono_along₅₉ (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (v : V)
    {j n : Nat} (hjn : j ≤ n) : Block.Preceq (W j v).st.core.F (W n v).st.core.F :=
  Restated.Vocabulary.Protocol.stateBefore_F_mono facts S rho v hjn (W j) (hW j).1 (W n)
    (onePath_slice₅₉ W hW hjn)

/-- A block of the filtered block tree of a store is a descendant of the store's finalized block. -/
private theorem F_preceq_of_mem_filtered₅₉ (facts : Record.Facts M) (st : M.S) {C : Block V}
    (hC : C ∈ M.get_filtered_block_tree (M.toHealing st).toFG) : Block.Preceq st.F C := by
  have h := facts.fc.finalized_preceq_of_mem_get_filtered_block_tree hC
  rwa [facts.sto.Sts_toHealing_F] at h

open scoped DC in
/-- If `f <$> m` can return `b`, then `m` can return some `a` with `f a = b`. -/
private theorem returns_map_elim₅₉ {α β : Type} (f : α → β) (m : DC.NDRE α) (b : β)
    (h : (f <$> m) ⇢ b) : ∃ a, m ⇢ a ∧ f a = b := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image] at h
  obtain ⟨e, he, hb⟩ := h
  cases e with
  | ok a => exact ⟨a, he, by simpa [Except.map] using hb⟩
  | error err => simp [Except.map] at hb

open scoped DC in
/-- If `m` can return `a`, then `f <$> m` can return `f a`. -/
private theorem returns_map_intro₅₉ {α β : Type} (f : α → β) (m : DC.NDRE α) (a : α)
    (h : m ⇢ a) : (f <$> m) ⇢ f a := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image]
  exact ⟨_, h, rfl⟩

/-- Every outcome of the early confirmation votes of `st` at slot `s` is among its late confirmation
    votes. -/
private theorem confEarly_subset_late₅₉ (facts : Record.Facts M) (E : Env V) (st : M.S) (s : Slot) :
    ∀ e, Restated.Vocabulary.Protocol.confEarly M E st s ⇢ e →
      e ⊆ Restated.Vocabulary.Protocol.confLate M E st s := by
  intro e he u hu
  obtain ⟨τ, hτ, rfl⟩ := returns_map_elim₅₉ _ _ _ he
  rw [beforeCutoff, Finset.mem_filter] at hu
  refine DecoupledConsensusModel.Protocol.beforeCutoff_mono _
    (facts.sch.Protocol_support_cutoff_le_confirmation_time E s) _ ?_
  rw [beforeCutoff, Finset.mem_filter]
  exact ⟨hu.1, facts.sto.stampedBefore_vote_of_tau st τ hτ hu.2⟩

/-- Every outcome `votes` of the counted confirmation votes of `st` at slot `s` comes with an
    outcome `early` of the early confirmation votes, related to `votes` and the late confirmation
    votes as the confirmation numerator relates them. -/
private theorem confNumerator₅₉ (facts : Record.Facts M) (E : Env V) (st : M.S) (s : Slot)
    (votes : Finset (GoldfishVote V))
    (hvotes : Restated.Vocabulary.Protocol.confVotes M E st s ⇢ votes) :
    ∃ early, Restated.Vocabulary.Protocol.confEarly M E st s ⇢ early ∧
      Restated.Vocabulary.Protocol.Numerator M early
        (Restated.Vocabulary.Protocol.confLate M E st s) votes := by
  obtain ⟨e, he, rfl⟩ := returns_map_elim₅₉ _ _ _ hvotes
  exact ⟨e, he, ⟨confEarly_subset_late₅₉ facts E st s e he, rfl⟩⟩

/-- If every member of the set for `domain r .g2` has `C` active, with every outcome of its grade-2
    store grade `true`, in its node state in `W (strictEventIndex rho (domain r .g2))`, `v` is in
    the set for `domain r .g0`, and `C` is active at a node state `n` of `v`'s round-`r` action read
    from `W (strictEventIndex rho (S.a r))`, then `C` is an ancestor of every SG vote `n` can
    select. -/
private theorem formsW_preceq_actionSGBlockAt₅₉ (facts : Record.Facts M) (S : Setup V)
    {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int} {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {r : Round} (hr : 0 < r)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon) {C : Block V}
    (hformsW : ∀ v ∈ Hs (M.domain S.E S.hc r .g2),
      C ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v) ∧
        ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
          (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v).st r .g2 C ⇢ b → b = true)
    {v : V} (hv : v ∈ Hs (M.domain S.E S.hc r .g0))
    (n : M.N)
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r)
    (hactive : C ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M n)
    (hlo : lo ≤ M.opening S.E S.hc (r - S.hc.η_SG)) :
    ∀ A2 : Option (Block V), M.grade2_block_with (M.gradeContract n.cache) S.E S.hc
        (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ A2 →
    ∀ G : Block V, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
        (M.round_of S.hc (M.toHealing n.st.core).s) A2 ⇢ G → Block.Preceq C G := by
  have hvG2 : v ∈ Hs (M.domain S.E S.hc r .g2) :=
    hHs _ _ (facts.gr.domain_le_domain_g0 S r .g2) hv
  set d := W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v with hd
  obtain ⟨b, hb⟩ := facts.gr.gradeBool_nonempty S.E (M.gradeView (M.toHealing d.st.core))
    d.st.core.F S.hc.η_SG r (M.early S.E S.hc r .g2) (M.late S.E S.hc r .g2) C
  have hbtrue : b = true := (hformsW v hvG2).2 b hb
  subst hbtrue
  obtain ⟨G, hG⟩ := facts.gr.read_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) r
  have hGq : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ G.Q2 := by
    unfold Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 Restated.Vocabulary.Internal.PhaseGrades.nodeRead
    exact returns_map_intro₅₉ (fun g : DecoupledConsensusModel.Protocol.GradeRead V => g.Q2) _ G hG
  obtain ⟨Q, hQ, hCQ⟩ :=
    Restated.preceq_actionQ2_of_domainGradeOn facts S Hs Xb hf hHs hr hhor hv hlo
      (hformsW v hvG2).1 hb n hn hactive _ hGq
  rw [hQ] at hGq
  exact Restated.preceq_actionSGBlockAt_of_actionQ2On facts S Hs Xb hf hHs hHsXb hr hhor
    (hHs _ _ (facts.gr.domain_le_domain_g0 S r .g1) hv) hlo n hn hGq hCQ

/-- Under the bundle, with round `r`'s grade read at the world of `W` before the grade-2 domain
    instant, if `v` is in the set for `S.a r`, `w` is in the set for `S.a r + Δ`, `lo ≤ S.a r`, the
    cutoff of round `r + 1` is inside the horizon, `P` is active at a node state `n` of `v`'s
    round-`r` action read and at `w`'s core store in `W (strictEventIndex rho (S.a (r + 1)))`, and
    `lo ≤ opening (r − η_SG)`, then every SG vote `n` can select is in `w`'s store in that world,
    stamped before the cutoff. -/
private theorem formsW_actionSGBlockAt_visible₅₉ (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {r : Round} (hr : 0 < r) {P : Block V}
    (hformsW : ∀ v ∈ Hs (M.domain S.E S.hc r .g2),
      P ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v) ∧
        ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
          (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v).st r .g2 P ⇢ b → b = true)
    {v w : V} (hv : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)))
    (hw : w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ))
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S r))
    (hcut : Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (r + 1) ≤ rho.horizon)
    (n : M.N)
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r)
    (hownActive : P ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M n)
    (hactive : P ∈ M.get_filtered_block_tree
      (M.toHealing (W (strictEventIndex rho
        (Restated.Vocabulary.Execution.Setup.a M S (r + 1))) w).st.core).toFG)
    (hlo : lo ≤ M.opening S.E S.hc (r - S.hc.η_SG)) :
    ∀ A2 : Option (Block V), M.grade2_block_with (M.gradeContract n.cache) S.E S.hc
        (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ A2 →
    ∀ H : Block V, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
        (M.round_of S.hc (M.toHealing n.st.core).s) A2 ⇢ H →
    H ∈ (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r + 1))) w).st.T ∧
      stampedBefore
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r + 1))) w).st.timestamp_block
        (Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (r + 1)) H = true := by
  intro A2 hA2 H hH
  have hhor : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon :=
    le_trans (le_add_of_nonneg_right (le_of_lt S.E.Δ_pos))
      (le_trans (facts.gr.action_add_delta_le_next_Γ_neg1 S r) hcut)
  have hHsource : H ∈
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).st.core.T :=
    Restated.Vocabulary.Proofs.HealingSurface.actionSGBlockAt_mem_storeBeforeTime facts S rho v r _
      (mem_stateBeforeTime_along₅₉ hf.sorted hf.onePath _) n hn A2 hA2 H hH
  have hvDom : v ∈ Hs (M.domain S.E S.hc r .g0) :=
    hHs _ _ (facts.gr.domain_le_a S r .g0) hv
  have hPH : Block.Preceq P H :=
    formsW_preceq_actionSGBlockAt₅₉ facts S Hs Xb hf hHs hHsXb hr hhor
      hformsW hvDom n hn hownActive hlo A2 hA2 H hH
  rcases Restated.block_eq_genesis_or_acceptsBefore_of_mem_storeBeforeTimeOn facts
      S Hs Xb hf v ((Restated.Vocabulary.Execution.Setup.a M S r)) hHsource with
    hgen | ⟨D, i, t, hDerase, hacc, ht⟩
  · rw [hgen]
    exact Restated.genesis_mem_and_stamp_storeBeforeTimeOn facts S Hs Xb hf w
      ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)))
      (Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (r + 1))
  · have hHpos : 0 < D.slot := by
      have hDpar : D.erase.parent.slot < D.erase.slot :=
        Restated.Vocabulary.Protocol.parent_slot_lt_of_acceptsAt_block facts S W hf.onePath hacc
      have hslotEq : D.erase.slot = D.slot := Proofs.NamedWire.erase_slot D
      rw [hslotEq] at hDpar
      exact Nat.zero_lt_of_lt hDpar
    have hrelayRead : (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ ≤
        (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) :=
      le_trans (facts.gr.action_add_delta_le_next_Γ_neg1 S r)
        (le_of_lt (Restated.Vocabulary.Proofs.HealingSurface.next_Γ_neg1_lt_action facts S r))
    have hFP := F_preceq_of_mem_filtered₅₉ facts _ hactive
    have hFhist : ∀ j : Nat,
        j ≤ (rho.events.filter (fun e => decide (e.time <
          (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ))).length →
          Block.Preceq (W j w).st.core.F D.erase := by
      intro j hj
      have hjN : j ≤ strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) :=
        le_trans hj (Restated.strict_filter_length_mono rho hrelayRead)
      rw [hDerase]
      exact preceq_trans_Preceq (F_mono_along₅₉ facts S hf.onePath w hjN)
        (preceq_trans_Preceq hFP hPH)
    have hrelayHor : (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ ≤ rho.horizon :=
      le_trans (facts.gr.action_add_delta_le_next_Γ_neg1 S r) hcut
    have hvmax : v ∈ Hs (max t lo) := hHs _ _ (max_le (le_of_lt ht) hpost) hv
    obtain ⟨C, hCerase, j, t', hacc', ht'⟩ :=
      Restated.block_admittedBefore_of_accepted_after_cutoffOn facts
        S Hs Xb hf hHs hHsXb hvmax hw hHpos hacc ht hpost rfl hrelayHor hFhist
    have hadmitNext : Restated.Vocabulary.Protocol.AdmittedBefore M S rho W w H
        (Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (r + 1)) :=
      ⟨C, hCerase.trans hDerase, j, t', hacc', lt_of_lt_of_le ht'
        (facts.gr.action_add_delta_le_next_Γ_neg1 S r)⟩
    exact Restated.admittedBefore_mem_and_stamp_atOn facts S Hs Xb hf hadmitNext
      (le_of_lt (Restated.Vocabulary.Proofs.HealingSurface.next_Γ_neg1_lt_action facts S r))

/-- If `P` is active with every outcome of its grade-2 store grade `true` at every member of the set
    for `domain r .g2` in `W (strictEventIndex rho (domain r .g2))`, and `P` is active at the
    round-`r` action reads, at `S.a (r + 1)` and at the next grade-2 domain instant, then
    `CleanActionReadForOn` holds for `P` at round `r` along the worlds of `W`. -/
private theorem formsW_cleanActionReadFor₅₉ (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {r : Round} (hr : 0 < r) {P : Block V}
    (hformsW : ∀ v ∈ Hs (M.domain S.E S.hc r .g2),
      P ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v) ∧
        ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
          (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v).st r .g2 P ⇢ b → b = true)
    (hpost : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S r))
    (hcut : Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (r + 1) ≤ rho.horizon)
    (hownActive : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r,
      P ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M n)
    (hactive : ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))),
      P ∈ M.get_filtered_block_tree
        (M.toHealing
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r + 1))) w).st.core).toFG)
    (hactive_domain : ∀ w ∈ Hs (M.domain S.E S.hc (r + 1) .g2),
      P ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
        (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) .g2)) w))
    (hA : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick v (Restated.Vocabulary.Execution.Setup.a M S r)) → M.awake_for_grade2 S v (W j v) r)
    (hlo₁ : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S r))
    (hlo : lo ≤ M.opening S.E S.hc (r - S.hc.η_SG)) :
    Restated.CleanActionReadForOn M S rho Hs r (fun t => W (strictEventIndex rho t)) P := by
  have hhor : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon :=
    le_trans (le_add_of_nonneg_right (le_of_lt S.E.Δ_pos))
      (le_trans (facts.gr.action_add_delta_le_next_Γ_neg1 S r) hcut)
  have hrelayRead : (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ ≤
      (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) :=
    le_trans (facts.gr.action_add_delta_le_next_Γ_neg1 S r)
      (le_of_lt (Restated.Vocabulary.Proofs.HealingSurface.next_Γ_neg1_lt_action facts S r))
  refine ⟨hpost, hcut, hactive, hactive_domain, ?_⟩
  intro w hw v hvD
  dsimp only
  intro n hn g hg B hB
  have hv : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)) :=
    hHs _ _ (le_of_lt (lt_add_of_pos_right _ S.E.Δ_pos)) hvD
  have hvisible := formsW_actionSGBlockAt_visible₅₉ facts
    S Hs Xb hf hHs hHsXb hr hformsW hv (hHs _ _ hrelayRead hw) hlo₁ hcut n hn
    (hownActive v hv n hn) (hactive w hw) hlo g hg B hB
  obtain ⟨D, hDerase, hDrun⟩ :=
    Restated.runBlock_of_mem_core_T_stateBeforeTimeOn facts S Hs Xb hf (hHsXb _ hw)
      ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) hvisible.1
  have hfind : Block.find?
      (M.gradeView (M.toHealing
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r + 1))) w).st.core)).T
        B.root = some B := by
    apply Proofs.Optimistic.find?_eq_some_of_unique
    · rw [facts.gr.Sts_gradeView_T]
      exact hvisible.1
    · intro Y hY hroot
      rw [facts.gr.Sts_gradeView_T] at hY
      obtain ⟨DY, hDYerase, hDYrun⟩ :=
        Restated.runBlock_of_mem_core_T_stateBeforeTimeOn facts S Hs Xb hf (hHsXb _ hw)
          ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) hY
      have hrootN : DY.root = D.root := by
        rw [← Proofs.NamedWire.erase_root DY, ← Proofs.NamedWire.erase_root D,
          hDYerase, hDerase]
        exact hroot
      have heqN : DY = D :=
        hf.rootCollisionFree.root_injective DY D hDYrun hDrun DY D
          (Or.inl (Proofs.NamedAncestry.named_self DY))
          (Or.inr (Proofs.NamedAncestry.named_self D)) hrootN
      rw [← hDYerase, heqN]
      exact hDerase
  have hvote := Restated.actionSGVote_stamp_before_next_Γ_neg1On facts S Hs Xb hf hHs r hvD
    (hHs _ _ hrelayRead hw) hlo₁ hcut (hA v hvD) n hn g hg B hB
  have hblock : occurrenceBefore
      ((M.gradeView (M.toHealing
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r + 1))) w).st.core)).timestamp_block B)
      (Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (r + 1)) = true := by
    have h2 := hvisible.2
    rw [stampedBefore_eq_occurrenceBefore] at h2
    rw [facts.gr.gradeView_timestamp_block]
    exact h2
  have hvDom : v ∈ Hs (M.domain S.E S.hc r .g0) :=
    hHs _ _ (facts.gr.domain_le_a S r .g0) hv
  constructor
  · simp only [Protocol.sg_resolution_time, hfind]
    exact occurrenceBefore_max hvote hblock
  · intro b hb
    exact facts.gr.head_covers_of_find hfind
      (formsW_preceq_actionSGBlockAt₅₉ facts S Hs Xb hf hHs hHsXb hr
        hhor hformsW hvDom n hn (hownActive v hv n hn) hlo g hg B hB) b hb

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Proofs.HealingSurface

/-- The round-`r` action read from a node state `before` has a node state `n` on which the grade-2
    block read can return some `g` and the SG vote selector on `g` some block `B`. -/
private theorem exists_actionSG₅₉ (facts : Record.Facts M) (S : Setup V) (before : M.N)
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

/-- Every node state the round-`r` action read computed from `before` can give holds the bodies
    `before` holds. -/
private theorem actionReadFrom_bodies₅₉ (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ nr ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      nr.st.bodies = before.st.bodies := by
  rintro _ ⟨c, -, st, hst, rfl⟩
  rw [facts.nd.mkNode_st, facts.nd.store_with_cache_bodies,
    facts.dt.named_update_confirmation_with_bodies _ _ _ _ _ st hst,
    facts.hd.ModelProperties_setClock_bodies]

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

/-- Under the bundle along `W`, if `n` is a node state of `p`'s round-`r` action read from its node
    state in `W` before `S.a r` and the Q2 of `n` can return `some Q`, then every outcome of the
    grade-2 store grade of `Q` at `p`'s store in `W` before `domain r .g2` is `true`. -/
theorem selectedQ2_storeGrade_at_g2DomainOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {r : Round} {p : V} {Q : Block V}
    (n : M.N)
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) p) r)
    (hselected : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ some Q) :
    ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
      (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) p).st r .g2 Q ⇢ b → b = true := by
  intro b hb
  obtain ⟨raw, hraw, hQraw⟩ :=
    Restated.namedG2At_freezeRoot_of_nodeQ2On facts S Hs Xb hf n hn hselected
  obtain ⟨braw, hbraw⟩ := facts.gr.gradeBool_nonempty S.E
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) p).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) p).st.core.F
    S.hc.η_SG r (M.early S.E S.hc r .g2) (M.late S.E S.hc r .g2) raw
  exact facts.csAdded.confirmation_phaseGrade_mono S.E S.hc _ _ r .g2 hQraw braw hbraw
    (hraw braw hbraw) b hb

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

/-- If `n` is one of `w`'s vote reads of slot `s + 1`, `votes` is an outcome of the source's
    slot-`s` confirmation votes, every outcome of `B`'s Goldfish score over `votes` at slot `s` is
    more than half the source's late voter count, and the body of `NamedNextVoteAdoptionOn` for `B`
    holds at `n`, then `B` is an ancestor of every head the in-tree head computation at `n` can
    return. -/
theorem preceq_voterHeadAt_of_namedNextVoteAdoptionOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} {W : Nat → V → M.N} (Xb : Finset V) {source : M.S}
    {s : Slot} {B : Block V} {w : V}
    (n : M.N)
    (hn : n ∈ Restated.Vocabulary.Internal.NamedRecoveryRead.voteDutyRead M S rho w (s + 1))
    {votes : Finset (GoldfishVote V)}
    (hvotes : Restated.Vocabulary.Protocol.confVotes M S.E source s ⇢ votes)
    (heligible : ∀ g : ℕ, M.goldfish_score S.E source.T votes votes s B ⇢ g →
      M.voters_count S.E (Restated.Vocabulary.Protocol.confLate M S.E source s) s < 2 * g)
    (hadopt :
      (∀ votes' : Finset (GoldfishVote V), Restated.Vocabulary.Protocol.confVotes M S.E source s ⇢ votes' →
        ∀ L : Finset (GoldfishVote V),
          M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
        ∀ L' : Finset (GoldfishVote V),
          M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
        Restated.Vocabulary.Protocol.AdoptionTransport M source.T n.st.core.T votes'
          (Restated.Vocabulary.Protocol.confLate M S.E source s) L L' B) ∧
      (∀ L : Finset (GoldfishVote V),
          M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
        ∀ L' : Finset (GoldfishVote V),
          M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
        L' ⊆ L) ∧
      (∀ R : Block V, M.get_sg_root_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc n.st.core.s) ⇢ R →
        R.compatible B = true) ∧
      (∀ R : Block V, M.get_sg_root_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc n.st.core.s) ⇢ R →
        R ⪯ B →
          ∀ C : Block V, R ⪯ C → C ≠ R → C ⪯ B →
            ∀ T : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T →
              C ∈ T) ∧
      (∀ T : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T →
        ∀ L : Finset (GoldfishVote V),
          M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
        ∀ L' : Finset (GoldfishVote V),
          M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
        ∀ H : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
            (M.toHealing n.st.core) T L L' (n.st.core.s - 1) ⇢ H →
        ∃ C : NamedBlock V, C.erase = H ∧ Restated.RunBlockOn M S rho W Xb C) ∧
      (∀ u : GoldfishVote V,
        ∀ D : M.NS × Option (GoldfishVote V),
          M.duties_goldfish_vote_with (M.gradeContract n.cache) S.E S.hc (S.node w) n.st ⇢ D →
        D.2 = some u →
          Restated.Vocabulary.Execution.Run.emits M S rho W w (Object.gfVote u)
            (M.vote_time S.E (s + 1)))) :
    ∀ T : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T →
    ∀ L : Finset (GoldfishVote V),
      M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
    ∀ L' : Finset (GoldfishVote V),
      M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
    ∀ H : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
        (M.toHealing n.st.core) T L L' (n.st.core.s - 1) ⇢ H →
      Block.Preceq B H := by
  intro T hT L hL L' hL' H hH
  obtain ⟨htransport, hsub, hanchor, hpath, -, -⟩ := hadopt
  have hslot : n.st.core.s = s + 1 :=
    Restated.Vocabulary.Proofs.Optimistic.voteDutyRead_slot facts S rho w (s + 1) n hn
  have hprev : n.st.core.s - 1 = s := by
    rw [hslot]
    simp
  obtain ⟨R, hR⟩ := facts.fc.get_sg_root_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s)
  have hs : (M.toHealing n.st.core).s = n.st.core.s := facts.sto.toHealing_s n.st.core
  have hTn : (M.toHealing n.st.core).T = n.st.core.T := facts.sto.toHealing_T n.st.core
  have hR' : M.get_sg_root_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
      (M.round_of S.hc n.st.core.s) ⇢ R := by
    rw [hs] at hR
    exact hR
  have hX := (facts.fc.get_head_in_tree_split_with (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) T L L' (n.st.core.s - 1) R hR H).1 hH
  rw [hprev] at hX
  obtain ⟨early, -, hN⟩ := confNumerator₅₉ facts S.E source s votes hvotes
  exact Restated.Vocabulary.Protocol.goldfish_fork_choice_captures_of_confirmation facts
    S.E (M.toHealing n.st.core).σ (M.toHealing n.st.core).h_max source.T (M.toHealing n.st.core).T T
    (M.toHealing n.st.core).s early (Restated.Vocabulary.Protocol.confLate M S.E source s) votes L L' s
    hN (by rw [hTn]; exact htransport votes hvotes L hL L' hL')
    heligible (hsub L hL L' hL') (hanchor R hR')
    (fun hRB C hRC hCR hCB => hpath R hR' hRB C hRC hCR hCB T hT) H hX

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

/-- Under the bundle along `W` and the weight bound, if `0 < q`, `lo ≤ S.a (q - 1)`, round `q`'s
    grade-1 domain instant is within the horizon, every round-`(q - 1)` action block along `W` of
    every member of the set for `S.a (q - 1)` is an ancestor of `C`, `w` is in the set for
    `domain q g1` with the finalized block of its store in `W` before that instant an ancestor of
    `C`, every outcome of the grade-1 store grade of `B` there is `true`, and every member of the
    set for `S.a (q - 1) + Δ` is awake at `q - 1`, then `B ⪯ C`. -/
theorem namedG1_preceq_commonActionCeilingOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hfb : BelowOneThirdOn S rho Hs)
    {q : Round} (hq : 0 < q)
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 1)))
    (hhor : M.domain S.E S.hc q .g1 ≤ rho.horizon)
    {C : Block V}
    (hupper : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1))),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) v) (q - 1),
      ∀ g, M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ g →
      ∀ B, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) g ⇢ B →
        Block.Preceq B C)
    {w : V} (hw : w ∈ Hs (M.domain S.E S.hc q .g1))
    (hFC : Block.Preceq
      (W (strictEventIndex rho (M.domain S.E S.hc q .g1)) w).st.core.F C)
    {B : Block V}
    (hG1 : ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
      (W (strictEventIndex rho (M.domain S.E S.hc q .g1)) w).st q .g1 B ⇢ b → b = true)
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1)) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) → M.awake_for_grade2 S u (W j u) (q - 1)) :
    Block.Preceq B C := by
  have hW := hf.onePath
  have hlatest : q - 1 ∈ M.latest_window S.hc.η_SG q :=
    facts.fc.pred_mem_latest_window S.hc.η_SG q S.hc.η_SG_ge_one hq
  have hactionDeadline : (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) + S.E.Δ ≤
      M.early S.E S.hc q .g1 :=
    (facts.gr.action_delta_le_early S S.hc.R_ge_three (Nat.sub_lt hq (by decide))).trans
      (facts.gr.q10_early_g2_le_early_g1 S q)
  have hearlyDomain : M.early S.E S.hc q .g1 ≤ M.domain S.E S.hc q .g1 :=
    (facts.gr.q10_early_g1_le_domain_g2 S q).trans
      (facts.gr.q10_domain_g2_lt_domain_g1 S q).le
  have hearlyHor : M.early S.E S.hc q .g1 ≤ rho.horizon := hearlyDomain.trans hhor
  have hactionHor : (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) ≤ rho.horizon :=
    (le_add_of_nonneg_right S.E.Δ_pos.le).trans (hactionDeadline.trans hearlyHor)
  have hwE : w ∈ Hs (M.early S.E S.hc q .g1) := hHs _ _ hearlyDomain hw
  have hmemE : ∀ v ∈ Hs (M.domain S.E S.hc q .g1), v ∈ Hs (M.early S.E S.hc q .g1) :=
    fun v hv => hHs _ _ hearlyDomain hv
  have hmemAD : ∀ v ∈ Hs (M.domain S.E S.hc q .g1),
      v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1)) + S.E.Δ) :=
    fun v hv => hHs _ _ (hactionDeadline.trans hearlyDomain) hv
  have hmemA : ∀ v ∈ Hs (M.domain S.E S.hc q .g1),
      v ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) :=
    fun v hv => hHs _ _ (le_add_of_nonneg_right S.E.Δ_pos.le) (hmemAD v hv)
  -- Every member of the set for the domain instant emitted a round-`(q - 1)` action vote whose head
  -- is an ancestor of `C`, an interpreted input of `w`'s grade read.
  have hvoteIn : ∀ v ∈ Hs (M.domain S.E S.hc q .g1),
      ∃ (a : NamedAttestation V) (B : Block V) (Bn : NamedBlock V),
        a.val_index = v ∧ a.round = q - 1 ∧
        Restated.Vocabulary.Execution.NamedRun.emits M S rho W v (Object.attest a)
          (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) ∧
        a.confirmed = some B.root ∧ Bn.erase = B ∧ Restated.RunBlockOn M S rho W Xb Bn ∧
        Block.Preceq B C ∧
        ∀ Y, M.interpretedInputs
          (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc q .g1)) w).st.core))
          (W (strictEventIndex rho (M.domain S.E S.hc q .g1)) w).st.core.F
          S.hc.η_SG q (M.early S.E S.hc q .g1) v ⇢ Y → M.sgVote a.erase ∈ Y := by
    intro v hv
    have hvA := hmemA v hv
    obtain ⟨nv, hnv, g, hg, B, hB⟩ := exists_actionSG₅₉ facts S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) v) (q - 1)
    obtain ⟨D, hD⟩ := facts.dt.attest_with_nonempty (M.gradeContract nv.cache) S.E S.hc (S.node v)
      nv.st nv.record
    have hem := Restated.honest_emits_actionAttestationAtOn facts S Hs Xb hf (q - 1) hvA hactionHor
      hpost (hA v (hmemAD v hv)) (fun j hj => hf.tick_outcome j _ _ hj) nv hnv D hD
    have hsg := hem.2 g hg B hB
    have haval : D.2.2.val_index = v := by
      have h := congrArg Protocol.SGVote.val_index hsg
      rw [facts.sto.sgVote_val_index_eq_val_index, namedAttestation_erase_val_index] at h
      exact h
    have haround : D.2.2.round = q - 1 := by
      have h := congrArg Protocol.SGVote.round hsg
      rw [facts.sto.sgVote_round_eq_round, namedAttestation_erase_round] at h
      exact h
    have haconf : D.2.2.confirmed = some B.root := by
      have h := congrArg Protocol.SGVote.confirmed hsg
      rw [facts.sto.sgVote_confirmed_eq, namedAttestation_erase_confirmed] at h
      exact h
    obtain ⟨i, hi, -, -, -, -, hall⟩ :=
      Restated.Vocabulary.Proofs.NamedOutageInputs.emitted_attestation_head facts S rho W hW hem.1
    obtain ⟨ni, hni, -⟩ := exists_actionSG₅₉ facts S (W i v) D.2.2.round
    obtain ⟨H, hH, hHconf⟩ := hall ni hni
    have hHbody : H ∈ (W i v).st.bodies := by
      rw [← actionReadFrom_bodies₅₉ facts S _ _ ni hni]
      exact hH
    have hHrun : Restated.RunBlockOn M S rho W Xb H :=
      Restated.runBlock_of_stateBefore_memOn facts S W Xb (hHsXb _ hv) hHbody
    have hBmem : B ∈ (W (strictEventIndex rho
        (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) v).st.core.T :=
      Restated.Vocabulary.Proofs.HealingSurface.actionSGBlockAt_mem_storeBeforeTime facts S rho v (q - 1) _
        (mem_stateBeforeTime_along₅₉ hf.sorted hW _) nv hnv g hg B hB
    obtain ⟨Bn, hBnerase, hBnrun⟩ := Restated.runBlock_of_mem_core_T_stateBeforeTimeOn facts S Hs Xb
      hf (hHsXb _ hv) (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) hBmem
    have hrootEq : H.erase.root = Bn.erase.root := by
      rw [Proofs.NamedWire.erase_root, hBnerase]
      exact Option.some.inj (hHconf.symm.trans haconf)
    have hHB : H.erase = Bn.erase :=
      Restated.runBlock_eq_of_root_eqOn facts W Xb hf.rootCollisionFree hHrun hBnrun hrootEq
    have hBC : Block.Preceq B C := hupper v hvA nv hnv g hg B hB
    have hHC : Block.Preceq H.erase C := by
      rw [hHB, hBnerase]
      exact hBC
    have hmem := Restated.action_vote_mem_interpretedInputs_after_gst_common_upperOn facts
      S Hs Xb hf hHs hHsXb .g1 hlatest (hmemE v hv) hwE
      ⟨haval, haround, hem.1⟩ ⟨i, hi, ⟨ni, hni, hH⟩, hHconf⟩ hHC hFC
      (by rw [haround]; exact hpost)
      (by rw [haround, max_eq_left hpost]; exact hactionDeadline)
      hearlyDomain hearlyHor
    exact ⟨D.2.2, B, Bn, haval, haround, hem.1, haconf, hBnerase, hBnrun, hBC, hmem⟩
  -- The window majority over the set for the domain instant.
  have hwin : ∀ ins : V → Finset (Protocol.SGVote V),
      (∀ v, M.interpretedInputs
        (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc q .g1)) w).st.core))
        (W (strictEventIndex rho (M.domain S.E S.hc q .g1)) w).st.core.F
        S.hc.η_SG q (M.early S.E S.hc q .g1) v ⇢ ins v) →
      S.E.electorate.weightOf (Finset.univ \ Hs (M.domain S.E S.hc q .g1)) <
        S.E.electorate.weightOf ((Hs (M.domain S.E S.hc q .g1)).filter
          fun v => (ins v).Nonempty) := by
    intro ins hins
    have hsubset : Hs (M.domain S.E S.hc q .g1) ⊆
        (Hs (M.domain S.E S.hc q .g1)).filter fun v => (ins v).Nonempty := by
      intro v hv
      obtain ⟨a, -, -, -, -, -, -, -, -, -, hmem⟩ := hvoteIn v hv
      exact Finset.mem_filter.2 ⟨hv, ⟨_, hmem _ (hins v)⟩⟩
    exact lt_of_lt_of_le
      (by simpa only [HonestWeightMajority] using
        honestWeightMajorityOn_of_belowOneThirdOn hfb _ hhor)
      (S.E.electorate.weightOf_mono hsubset)
  -- One outcome of the grade-1 test of `B` at `w`'s store, which is `true`.
  obtain ⟨gB, hgB⟩ := facts.gr.gradeBool_nonempty S.E
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc q .g1)) w).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc q .g1)) w).st.core.F
    S.hc.η_SG q (M.early S.E S.hc q .g1) (M.late S.E S.hc q .g1) B
  have hgBtrue : gB = true := hG1 gB hgB
  -- A positive supporter of `B` in the set, with its latest interpreted input.
  obtain ⟨v, hv, I, hI, u, hu, head, hconf, hfind, -, hBhead, -, hmax⟩ :=
    facts.gr.exists_honest_max_positive_supporter_of_relativeGrade S.E S.hc hwin gB hgB hgBtrue
  obtain ⟨a, Bv, Bn, haval, haround, hemit, haconf, hBnerase, hBnrun, hBC, hmem⟩ := hvoteIn v hv
  have hqle : q - 1 ≤ u.round := by
    have h := hmax (M.sgVote a.erase) (hmem I hI)
    rw [facts.sto.sgVote_round_eq_round, namedAttestation_erase_round, haround] at h
    exact h
  obtain ⟨R, hR⟩ := facts.gr.rawInputs_nonempty
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc q .g1)) w).st.core))
    S.hc.η_SG q (M.early S.E S.hc q .g1) v
  obtain ⟨bu, hbu⟩ := facts.gr.bodyReady_nonempty
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc q .g1)) w).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc q .g1)) w).st.core.F
    (M.early S.E S.hc q .g1) u
  have huraw := ((facts.gr.mem_interpretedInputs_iff I hI R hR bu hbu).mp hu).1
  obtain ⟨b, -, hbround, hbproj, huwindow, -, hbemit⟩ :=
    Restated.rawInputs_traceOn facts S rho Hs Xb hf hHs (M.domain S.E S.hc q .g1)
      (M.early S.E S.hc q .g1) w S.hc.η_SG q v hv R hR huraw
  have hule : u.round ≤ q - 1 := Nat.le_sub_one_of_lt (facts.fc.window_bounds huwindow).2
  have huroundEq : u.round = q - 1 := Nat.le_antisymm hule hqle
  have hba : b = a := Restated.emits_attest_uniqueOn facts S Hs Xb hf hbemit hemit
    ((hbround.trans huroundEq).trans haround.symm)
  have huEq : u = M.sgVote a.erase := by
    rw [← hbproj, hba]
  have hheadRoot : head.root = Bv.root := by
    have huconf := congrArg Protocol.SGVote.confirmed huEq
    rw [facts.sto.sgVote_confirmed_eq, namedAttestation_erase_confirmed, hconf, haconf] at huconf
    exact Option.some.inj huconf
  have hheadMem : head ∈ (W (strictEventIndex rho (M.domain S.E S.hc q .g1)) w).st.core.T := by
    have h := Proofs.HealingLemmas.find?_mem hfind
    rw [facts.gr.Sts_gradeView_T] at h
    exact h
  obtain ⟨Headn, hHeaderase, hHeadrun⟩ := Restated.runBlock_of_mem_core_T_stateBeforeTimeOn facts
    S Hs Xb hf (hHsXb _ hw) (M.domain S.E S.hc q .g1) hheadMem
  have hheadBnRoot : Headn.erase.root = Bn.erase.root := by
    rw [hHeaderase, hBnerase]
    exact hheadRoot
  have hheadB : head = Bv := by
    rw [← hHeaderase, ← hBnerase]
    exact Restated.runBlock_eq_of_root_eqOn facts W Xb hf.rootCollisionFree hHeadrun hBnrun hheadBnRoot
  rw [hheadB] at hBhead
  exact preceq_trans_Preceq hBhead hBC

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

/-- Under the bundle along `W` and the weight bound, if the justification root of `w`'s store in `W`
    before `read` is fixed at `H`, `lo ≤ read`, `read + Δ` is at most the opening proposal instant
    `t` of `q`, `t` is within the horizon, the largest `h_max` over the set for `t` in `W` after the
    events at or before `t` is at most `H`, `lo ≤ S.a (q − 1)`, that justification root is an
    ancestor of `C`, every round-`(q − 1)` action block along `W` of every member of the set for
    `S.a (q − 1)` is an ancestor of `C`, `x` is in the set for `domain q g1`, every outcome of the
    grade-1 store grade of `B` at `x`'s store in `W` before that instant is `true`, and every member
    of the set for `S.a (q − 1) + Δ` is awake at `q − 1`, then `B ⪯ C`. -/
theorem namedG1_preceq_fixedRootActionCeilingOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hfb : BelowOneThirdOn S rho Hs)
    {H : Height} {w : V} {read : Time}
    (hfix : Restated.FixedHeightJustificationRootAtReadOn M S rho W Hs Xb H w read
      (W (strictEventIndex rho read)))
    {q : Round} (hq : 0 < q)
    (hpostRead : lo ≤ read)
    (hproposalDelay : read + S.E.Δ ≤
      M.proposal_time S.E ((M.opening_slot S.hc q)))
    (hproposalHor : M.proposal_time S.E
      ((M.opening_slot S.hc q)) ≤ rho.horizon)
    (hproposalCap : ((Hs (M.proposal_time S.E (M.opening_slot S.hc q))).sup fun u =>
      (W (inclusiveEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q))) u).st.core.h_max) ≤ H)
    (hpostPreviousAction : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 1)))
    {C : Block V}
    (hJC : Block.Preceq (W (strictEventIndex rho read) w).st.J C)
    (hupper : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1))),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) v) (q - 1),
      ∀ g, M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ g →
      ∀ B, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) g ⇢ B →
        Block.Preceq B C)
    {x : V} (hx : x ∈ Hs (M.domain S.E S.hc q .g1)) {B : Block V}
    (hG1 : ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
      (W (strictEventIndex rho (M.domain S.E S.hc q .g1)) x).st q .g1 B ⇢ b → b = true)
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1)) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) → M.awake_for_grade2 S u (W j u) (q - 1)) :
    Block.Preceq B C := by
  have hopen : M.domain S.E S.hc q .g1 =
      M.proposal_time S.E ((M.opening_slot S.hc q)) := by
    rw [facts.gr.Sts_domain_g1_eq_opening, facts.gr.opening_eq_proposal_time]
  have hxP : x ∈ Hs (M.proposal_time S.E ((M.opening_slot S.hc q))) := by
    rw [← hopen]; exact hx
  obtain ⟨hrootX, -⟩ :=
    Restated.fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRiseOn facts
      S Hs Xb hf hHs hHsXb hf.slashableBound hfix hxP hpostRead
        hproposalDelay hproposalHor hproposalCap
  have hFJ := Restated.Vocabulary.Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime facts
    S rho (M.proposal_time S.E (M.opening_slot S.hc q)) x _
    (mem_stateBeforeTime_along₅₉ hf.sorted hf.onePath _)
  have hrootFloor := facts.fc.preceq_get_fg_root_of_F
    (st := (M.toHealing (W (strictEventIndex rho
      (M.proposal_time S.E (M.opening_slot S.hc q))) x).st.core).toFG)
    (by
      rw [facts.sto.Sts_toHealing_F, facts.sto.Sts_toHealing_J]
      exact preceq_eq_true_iff_Preceq.mpr hFJ)
  rw [facts.sto.Sts_toHealing_F] at hrootFloor
  have hFC : Block.Preceq
      (W (strictEventIndex rho (M.domain S.E S.hc q .g1)) x).st.core.F C := by
    rw [hopen]
    refine preceq_trans_Preceq (preceq_eq_true_iff_Preceq.mp ?_) hJC
    rw [← hrootX]
    exact hrootFloor
  exact Restated.namedG1_preceq_commonActionCeilingOn facts S Hs Xb hf hHs hHsXb hfb hq
    hpostPreviousAction (by rw [hopen]; exact hproposalHor) hupper hx hFC hG1 hA

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

/-- Under the bundle along `W`, the committee majority and the weight bound, if the justification
    root of `w`'s store in `W` before `read` is fixed at `H`, `2 ≤ q`, that root has grade 2 at
    round `q − 1` at every member of the set for `domain (q − 1) g2` and is in the filtered tree of
    every member of the set for `S.a (q − 1)`, the opening root lock holds along `W`, and the
    instants and caps of `namedG1_preceq_fixedRootActionCeilingOn` hold, then some member of the set
    for `S.a (q − 1)` has an action block `C` that is a descendant of every round-`(q − 1)` action
    block of that set, slot `opening_slot q − 1`'s committee votes into the descendants of `C`, and
    every grade-1 block of round `q` at a member of the set for `domain q g1` is an ancestor of `C`. -/
theorem fixedRoot_namedG1CommonCeilingOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hfb : BelowOneThirdOn S rho Hs)
    {H : Height} {w : V} {read : Time}
    (hfix : Restated.FixedHeightJustificationRootAtReadOn M S rho W Hs Xb H w read
      (W (strictEventIndex rho read)))
    {q : Round} (hqTwo : 2 ≤ q)
    (hforms : ∀ v ∈ Hs (M.domain S.E S.hc (q - 1) .g2),
      (W (strictEventIndex rho read) w).st.J ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc (q - 1) .g2)) v) ∧
        ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
          (W (strictEventIndex rho (M.domain S.E S.hc (q - 1) .g2)) v).st (q - 1) .g2
          (W (strictEventIndex rho read) w).st.J ⇢ b → b = true)
    (hwindow : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1))),
      (W (strictEventIndex rho read) w).st.J ∈ M.get_filtered_block_tree (M.toHealing
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) v).st.core).toFG)
    {wd : V → M.N}
    (hlock : Restated.SGTargetOpeningConeRootLockOn M S rho W Hs Xb H (q - 1)
      ((M.opening_slot S.hc q) - 1) wd
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1)))))
    (hpostRead : lo ≤ read)
    (hproposalDelay : read + S.E.Δ ≤
      M.proposal_time S.E ((M.opening_slot S.hc q)))
    (hproposalHor : M.proposal_time S.E
      ((M.opening_slot S.hc q)) ≤ rho.horizon)
    (hproposalCap : ((Hs (M.proposal_time S.E (M.opening_slot S.hc q))).sup fun u =>
      (W (inclusiveEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q))) u).st.core.h_max) ≤ H)
    (hpostPreviousAction : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 1)))
    (hloOpen : lo ≤ M.opening S.E S.hc (q - 1 - S.hc.η_SG))
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1)) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) → M.awake_for_grade2 S u (W j u) (q - 1)) :
    ∃ C : Block V, ∃ v0 : V,
      v0 ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1))) ∧
        (∃ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
            (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) v0) (q - 1),
          ∃ g, M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
              (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ g ∧
            M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
              (M.round_of S.hc (M.toHealing n.st.core).s) g ⇢ C) ∧
        (∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1))),
          ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
            (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) v) (q - 1),
          ∀ g, M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
              (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ g →
          ∀ B, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
              (M.round_of S.hc (M.toHealing n.st.core).s) g ⇢ B →
            Block.Preceq B C) ∧
        Restated.NamedHonestVotesConeOn M S rho W Hs Xb ((M.opening_slot S.hc q) - 1)
          (fun Y => Block.Preceq C Y) ∧
        ∀ {x : V}, x ∈ Hs (M.domain S.E S.hc q .g1) → ∀ {B : Block V},
          (∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
            (W (strictEventIndex rho (M.domain S.E S.hc q .g1)) x).st q .g1 B ⇢ b → b = true) →
          Block.Preceq B C := by
  have hq : 0 < q := (by decide : 0 < 2).trans_le hqTwo
  obtain ⟨C, ⟨v0, hv0, n0, hn0, g0, hg0, hC0⟩, hupper, hcone⟩ :=
    Restated.fixedRoot_commonActionCeiling_of_lockOn facts S Hs Xb hf hHs hcom hlock
  have hqPrev : 0 < q - 1 :=
    Nat.sub_pos_of_lt ((by decide : 1 < 2).trans_le hqTwo)
  have hactionHor : (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) ≤ rho.horizon := by
    have hlt : q - 1 < q := Nat.sub_lt hq (by decide)
    exact (Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans
      ((Restated.Vocabulary.Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt facts S hlt).trans
        hproposalHor)
  have hv0g0 : v0 ∈ Hs (M.domain S.E S.hc (q - 1) .g0) :=
    hHs _ _ (facts.gr.domain_le_a S (q - 1) .g0) hv0
  have hJactive : (W (strictEventIndex rho read) w).st.J ∈
      Restated.Vocabulary.Internal.PhaseGrades.filteredTree M n0 :=
    Restated.Vocabulary.Proofs.HealingSurface.activeAtAction_of_retainedAtRead facts S (v := v0) _
      (mem_stateBeforeTime_along₅₉ hf.sorted hf.onePath _) (hwindow v0 hv0) n0 hn0
  have hJC : Block.Preceq (W (strictEventIndex rho read) w).st.J C :=
    formsW_preceq_actionSGBlockAt₅₉ facts S Hs Xb hf hHs hHsXb hqPrev hactionHor hforms
      hv0g0 n0 hn0 hJactive hloOpen g0 hg0 C hC0
  refine ⟨C, v0, hv0, ⟨n0, hn0, g0, hg0, hC0⟩, hupper, hcone, ?_⟩
  intro x hx B hG1
  exact Restated.namedG1_preceq_fixedRootActionCeilingOn facts S Hs Xb hf hHs hHsXb hfb hfix hq
    hpostRead hproposalDelay hproposalHor hproposalCap hpostPreviousAction hJC hupper hx hG1 hA

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

/-- The public form of `fixedRoot_namedG1CommonCeilingOn`, with the same hypotheses and conclusion. -/
theorem fixedRoot_namedG1CommonCeiling_publicOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hfb : BelowOneThirdOn S rho Hs)
    {H : Height} {w : V} {read : Time}
    (hfix : Restated.FixedHeightJustificationRootAtReadOn M S rho W Hs Xb H w read
      (W (strictEventIndex rho read)))
    {q : Round} (hqTwo : 2 ≤ q)
    (hforms : ∀ v ∈ Hs (M.domain S.E S.hc (q - 1) .g2),
      (W (strictEventIndex rho read) w).st.J ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc (q - 1) .g2)) v) ∧
        ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
          (W (strictEventIndex rho (M.domain S.E S.hc (q - 1) .g2)) v).st (q - 1) .g2
          (W (strictEventIndex rho read) w).st.J ⇢ b → b = true)
    (hwindow : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1))),
      (W (strictEventIndex rho read) w).st.J ∈ M.get_filtered_block_tree (M.toHealing
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) v).st.core).toFG)
    {wd : V → M.N}
    (hlock : Restated.SGTargetOpeningConeRootLockOn M S rho W Hs Xb H (q - 1)
      ((M.opening_slot S.hc q) - 1) wd
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1)))))
    (hpostRead : lo ≤ read)
    (hproposalDelay : read + S.E.Δ ≤
      M.proposal_time S.E ((M.opening_slot S.hc q)))
    (hproposalHor : M.proposal_time S.E
      ((M.opening_slot S.hc q)) ≤ rho.horizon)
    (hproposalCap : ((Hs (M.proposal_time S.E (M.opening_slot S.hc q))).sup fun u =>
      (W (inclusiveEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q))) u).st.core.h_max) ≤ H)
    (hpostPreviousAction : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 1)))
    (hloOpen : lo ≤ M.opening S.E S.hc (q - 1 - S.hc.η_SG))
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1)) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) → M.awake_for_grade2 S u (W j u) (q - 1)) :
    ∃ C : Block V, ∃ v0 : V,
      v0 ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1))) ∧
        (∃ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
            (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) v0) (q - 1),
          ∃ g, M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
              (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ g ∧
            M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
              (M.round_of S.hc (M.toHealing n.st.core).s) g ⇢ C) ∧
        (∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1))),
          ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
            (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) v) (q - 1),
          ∀ g, M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
              (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ g →
          ∀ B, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
              (M.round_of S.hc (M.toHealing n.st.core).s) g ⇢ B →
            Block.Preceq B C) ∧
        Restated.NamedHonestVotesConeOn M S rho W Hs Xb ((M.opening_slot S.hc q) - 1)
          (fun Y => Block.Preceq C Y) ∧
        ∀ {x : V}, x ∈ Hs (M.domain S.E S.hc q .g1) → ∀ {B : Block V},
          (∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
            (W (strictEventIndex rho (M.domain S.E S.hc q .g1)) x).st q .g1 B ⇢ b → b = true) →
          Block.Preceq B C :=
  Restated.fixedRoot_namedG1CommonCeilingOn facts S Hs Xb hf hHs hHsXb hcom hfb hfix hqTwo
    hforms hwindow hlock hpostRead hproposalDelay hproposalHor hproposalCap
    hpostPreviousAction hloOpen hA

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

/-- If slot `s`'s committee votes along `W` into the descendants of `C`, and every block with grade
    1 at round `r + 1` at the store in `Wt (domain (r + 1) .g1)` of a member of the set for
    `domain (r + 1) g1` is an ancestor of `C`, then `NamedG1ConcentrationOn` holds along `W` and
    `Wt` at `r`, `s`. -/
theorem namedG1Concentration_of_commonCeilingOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V)
    {W : Nat → V → M.N} (Wt : Time → V → M.N)
    {r : Round} {s : Slot} {C : Block V}
    (hcone : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s (fun Y => Block.Preceq C Y))
    (hbelow : ∀ {x : V}, x ∈ Hs (M.domain S.E S.hc (r + 1) .g1) → ∀ {B : Block V},
      (∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
        (Wt (M.domain S.E S.hc (r + 1) .g1) x).st (r + 1) .g1 B ⇢ b → b = true) →
      Block.Preceq B C) :
    Restated.NamedG1ConcentrationOn M S rho W Wt Hs Xb r s := by
  refine ⟨?_, ?_⟩
  · intro x B hx hG1
    have hBC : Block.Preceq B C := hbelow hx hG1
    intro y hy hcommittee
    obtain ⟨Y, hCY, hYrun, hemit⟩ := hcone y hy hcommittee
    exact ⟨Y, preceq_trans_Preceq hBC hCY, hYrun, hemit⟩
  · intro x₁ x₂ B₁ B₂ hx₁ hx₂ hG1₁ hG1₂
    exact compatible_of_preceq_common_Preceq
      (hbelow hx₁ hG1₁) (hbelow hx₂ hG1₂)

/-- Under the hypotheses of `fixedRoot_namedG1CommonCeilingOn` along `W`, `NamedG1ConcentrationOn`
    holds along `W` and the worlds `fun t => W (strictEventIndex rho t)` at round `q − 1` and slot
    `opening_slot q − 1`. -/
theorem namedG1Concentration_of_fixedRootLockOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hfb : BelowOneThirdOn S rho Hs)
    {H : Height} {w : V} {read : Time}
    (hfix : Restated.FixedHeightJustificationRootAtReadOn M S rho W Hs Xb H w read
      (W (strictEventIndex rho read)))
    {q : Round} (hqTwo : 2 ≤ q)
    (hforms : ∀ v ∈ Hs (M.domain S.E S.hc (q - 1) .g2),
      (W (strictEventIndex rho read) w).st.J ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc (q - 1) .g2)) v) ∧
        ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
          (W (strictEventIndex rho (M.domain S.E S.hc (q - 1) .g2)) v).st (q - 1) .g2
          (W (strictEventIndex rho read) w).st.J ⇢ b → b = true)
    (hwindow : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1))),
      (W (strictEventIndex rho read) w).st.J ∈ M.get_filtered_block_tree (M.toHealing
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) v).st.core).toFG)
    {wd : V → M.N}
    (hlock : Restated.SGTargetOpeningConeRootLockOn M S rho W Hs Xb H (q - 1)
      ((M.opening_slot S.hc q) - 1) wd
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1)))))
    (hpostRead : lo ≤ read)
    (hproposalDelay : read + S.E.Δ ≤
      M.proposal_time S.E ((M.opening_slot S.hc q)))
    (hproposalHor : M.proposal_time S.E
      ((M.opening_slot S.hc q)) ≤ rho.horizon)
    (hproposalCap : ((Hs (M.proposal_time S.E (M.opening_slot S.hc q))).sup fun u =>
      (W (inclusiveEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q))) u).st.core.h_max) ≤ H)
    (hpostPreviousAction : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 1)))
    (hloOpen : lo ≤ M.opening S.E S.hc (q - 1 - S.hc.η_SG))
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1)) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) → M.awake_for_grade2 S u (W j u) (q - 1)) :
    Restated.NamedG1ConcentrationOn M S rho W (fun t => W (strictEventIndex rho t)) Hs Xb (q - 1)
      ((M.opening_slot S.hc q) - 1) := by
  obtain ⟨C, _v0, _hv0, _hCv0, _hupper, hcone, hbelow⟩ :=
    Restated.fixedRoot_namedG1CommonCeilingOn facts S Hs Xb hf hHs hHsXb hcom hfb hfix hqTwo
      hforms hwindow hlock hpostRead hproposalDelay hproposalHor hproposalCap
      hpostPreviousAction hloOpen hA
  have hpred : q - 1 + 1 = q := Nat.sub_add_cancel ((by decide : 0 < 2).trans_le hqTwo)
  refine Restated.namedG1Concentration_of_commonCeilingOn facts S Hs Xb
    (fun t => W (strictEventIndex rho t)) hcone ?_
  intro x hx B hB
  simp only [hpred] at hx hB
  exact hbelow hx hB

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

/-- Under the bundle along `W` and the weight bound, if the justification root of `w`'s store in `W`
    before `read` is fixed at `H`, `2 ≤ q`, that root has grade 2 at round `q − 1` at every member
    of the set for `domain (q − 1) g2`, is in the filtered tree of every member of the sets for
    `S.a (q − 1)`, `domain q g2` and `S.a q` at its store before that instant, round `q`'s opening
    proposer is in the set for its proposal instant, and the instants and caps of
    `namedG1_preceq_fixedRootActionCeilingOn` hold, then every outcome of the grade-1 store grade of
    round `q` of that root at the opening proposer's store in `W` before `domain q g1` is `true`. -/
theorem namedG1At_fixedRootTarget_of_retainedPreviousGradeOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hfb : BelowOneThirdOn S rho Hs)
    {H : Height} {w : V} {read : Time}
    (hfix : Restated.FixedHeightJustificationRootAtReadOn M S rho W Hs Xb H w read
      (W (strictEventIndex rho read)))
    {q : Round} (hqTwo : 2 ≤ q)
    (hforms : ∀ v ∈ Hs (M.domain S.E S.hc (q - 1) .g2),
      (W (strictEventIndex rho read) w).st.J ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc (q - 1) .g2)) v) ∧
        ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
          (W (strictEventIndex rho (M.domain S.E S.hc (q - 1) .g2)) v).st (q - 1) .g2
          (W (strictEventIndex rho read) w).st.J ⇢ b → b = true)
    (hwindow : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1))),
      (W (strictEventIndex rho read) w).st.J ∈ M.get_filtered_block_tree (M.toHealing
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) v).st.core).toFG)
    (hdomainWindow : ∀ v ∈ Hs (M.domain S.E S.hc q .g2),
      (W (strictEventIndex rho read) w).st.J ∈ M.get_filtered_block_tree (M.toHealing
        (W (strictEventIndex rho (M.domain S.E S.hc q .g2)) v).st.core).toFG)
    (hpostRead : lo ≤ read)
    (hpostPreviousAction : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 1)))
    (hcut : Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ q ≤ rho.horizon)
    (hactionHor : (Restated.Vocabulary.Execution.Setup.a M S q) ≤ rho.horizon)
    (hactiveAtAction : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
      (W (strictEventIndex rho read) w).st.J ∈ M.get_filtered_block_tree (M.toHealing
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v).st.core).toFG)
    (hprop : S.E.proposer ((M.opening_slot S.hc q)) ∈
      Hs (M.proposal_time S.E ((M.opening_slot S.hc q))))
    (hproposalDelay : read + S.E.Δ ≤
      M.proposal_time S.E ((M.opening_slot S.hc q)))
    (hproposalHor : M.proposal_time S.E
      ((M.opening_slot S.hc q)) ≤ rho.horizon)
    (hproposalCap : ((Hs (M.proposal_time S.E (M.opening_slot S.hc q))).sup fun u =>
      (W (inclusiveEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q))) u).st.core.h_max) ≤ H)
    (hlo₁ : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 1)))
    (hloOpen : lo ≤ M.opening S.E S.hc (q - 1 - S.hc.η_SG))
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1)) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) → M.awake_for_grade2 S u (W j u) (q - 1)) :
    ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
      (W (strictEventIndex rho (M.domain S.E S.hc q .g1))
        (S.E.proposer (M.opening_slot S.hc q))).st q .g1
      (W (strictEventIndex rho read) w).st.J ⇢ b → b = true := by
  set J := (W (strictEventIndex rho read) w).st.J with hJ
  set p := S.E.proposer ((M.opening_slot S.hc q)) with hp
  have hq : 0 < q := (by decide : 0 < 2).trans_le hqTwo
  have hqPrev : 0 < q - 1 :=
    Nat.sub_pos_of_lt ((by decide : 1 < 2).trans_le hqTwo)
  have hq1 : q - 1 + 1 = q := Nat.sub_add_cancel hq
  have hopen : M.domain S.E S.hc q .g1 =
      M.proposal_time S.E ((M.opening_slot S.hc q)) := by
    rw [facts.gr.Sts_domain_g1_eq_opening, facts.gr.opening_eq_proposal_time]
  have hpG1 : p ∈ Hs (M.domain S.E S.hc q .g1) := by
    rw [hopen]; exact hprop
  have hpG2 : p ∈ Hs (M.domain S.E S.hc q .g2) :=
    hHs _ _ (facts.gr.q10_domain_g2_lt_domain_g1 S q).le hpG1
  have hownActive : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1))),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) v) (q - 1),
      J ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M n := by
    intro v hv
    exact Restated.Vocabulary.Proofs.HealingSurface.activeAtAction_of_retainedAtRead facts S (v := v)
      _ (mem_stateBeforeTime_along₅₉ hf.sorted hf.onePath _) (hwindow v hv)
  have hclean : Restated.CleanActionReadForOn M S rho Hs (q - 1)
      (fun t => W (strictEventIndex rho t)) J :=
    formsW_cleanActionReadFor₅₉ facts S Hs Xb hf hHs hHsXb hqPrev hforms
      hpostPreviousAction (by rw [hq1]; exact hcut) hownActive
      (by rw [hq1]; exact hactiveAtAction) (by rw [hq1]; exact hdomainWindow) hA hlo₁ hloOpen
  have hmajority : HonestWeightMajorityOn S rho Hs := fun t ht =>
    AlignedRoundLemmas.honestWeightMajority_of_belowOneThird (S := S) (hfb t ht)
  have hne : (Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1 + 1)))).Nonempty := by
    rw [hq1]
    exact nonempty_of_honestWeightMajority_l54 (hmajority _ hactionHor)
  have hformsQ := Restated.namedGradeFormsAt_of_cleanActionReadOn facts S Hs Xb hf hHs hHsXb
    hmajority hclean hne hlo₁ hA
  rw [hq1] at hformsQ
  have hG2 : ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
      (W (strictEventIndex rho (M.domain S.E S.hc q .g2)) p).st q .g2 J ⇢ b → b = true :=
    (hformsQ p hpG2).2
  obtain ⟨b2, hb2⟩ := facts.gr.gradeBool_nonempty S.E
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc q .g2)) p).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc q .g2)) p).st.core.F
    S.hc.η_SG q (M.early S.E S.hc q .g2) (M.late S.E S.hc q .g2) J
  have hG2true : Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
      (W (strictEventIndex rho (M.domain S.E S.hc q .g2)) p).st q .g2 J ⇢ true := by
    have h := hG2 b2 hb2
    subst h
    exact hb2
  have hgst : lo ≤ M.early S.E S.hc q .g2 := by
    exact hlo₁.trans
      ((le_add_of_nonneg_right S.E.Δ_pos.le).trans
        (facts.gr.action_delta_le_early S S.hc.R_ge_three
          (Nat.sub_lt hq (by decide))))
  have hloOpenQ : lo ≤ M.opening S.E S.hc (q - S.hc.η_SG) :=
    hloOpen.trans (facts.gr.NamedOutageClosure_opening_mono S
      (Nat.sub_le_sub_right (Nat.sub_le q 1) S.hc.η_SG))
  have hdomainG0Hor : M.domain S.E S.hc q .g0 ≤ rho.horizon :=
    (facts.gr.domain_le_a S q .g0).trans hactionHor
  obtain ⟨hroot, -⟩ :=
    Restated.fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRiseOn facts
      S Hs Xb hf hHs hHsXb hf.slashableBound hfix hprop hpostRead
        hproposalDelay hproposalHor hproposalCap
  have hFJ := Restated.Vocabulary.Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime facts
    S rho (M.proposal_time S.E (M.opening_slot S.hc q)) p _
    (mem_stateBeforeTime_along₅₉ hf.sorted hf.onePath _)
  have hrootFloor := facts.fc.preceq_get_fg_root_of_F
    (st := (M.toHealing (W (strictEventIndex rho
      (M.proposal_time S.E (M.opening_slot S.hc q))) p).st.core).toFG)
    (by
      rw [facts.sto.Sts_toHealing_F, facts.sto.Sts_toHealing_J]
      exact preceq_eq_true_iff_Preceq.mpr hFJ)
  rw [facts.sto.Sts_toHealing_F] at hrootFloor
  have hFg1J : Block.Preceq
      (W (strictEventIndex rho (M.domain S.E S.hc q .g1)) p).st.core.F J := by
    rw [hopen]
    refine preceq_eq_true_iff_Preceq.mp ?_
    rw [hJ, ← hroot]
    exact hrootFloor
  have hforward : ∀ sender u root Head,
      ∀ I, M.interpretedInputs
        (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc q .g2)) p).st.core))
        (W (strictEventIndex rho (M.domain S.E S.hc q .g2)) p).st.core.F
        S.hc.η_SG q (M.early S.E S.hc q .g2) sender ⇢ I → u ∈ I →
      ∀ c, M.localCovers
        (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc q .g2)) p).st.core))
        u.confirmed J ⇢ c → c = true →
      u.confirmed = some root →
      Block.find?
        (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc q .g2)) p).st.core)).T
          root = some Head →
      Block.Preceq (W (strictEventIndex rho (M.domain S.E S.hc q .g1)) p).st.core.F Head := by
    intro sender u root Head I _ _ c hc hctrue hconf hfind
    rw [hconf] at hc
    exact preceq_trans_Preceq hFg1J (facts.gr.preceq_of_localCovers_of_find c hc hctrue hfind)
  have hbelow := Restated.crossReaderFinalizedBelow_of_finalitySafety_and_relayOn facts
    S Hs Xb hf hHs hHsXb hf.slashableBound hgst hdomainG0Hor hpG2 hpG1 hforward
  have hguard := Restated.crossReaderBodyReadyGuard_of_finalizedBelowOn facts
    S Hs Xb hf hHs hHsXb hq hgst hdomainG0Hor hpG2 hpG1 hbelow
  exact Restated.storeGrade_g1_of_storeGrade_g2_cross_readerOn facts
    S rho Hs Xb hf hHs hHsXb q hloOpenQ hdomainG0Hor p p hpG2 hpG1 J hG2true hguard

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

/-! ## Bodies held at action and vote-duty reads -/

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

/-- A block of the tree of `v`'s core store in `W i` is the erasure of a named body of `v`'s store
    in `W i`. -/
private theorem exists_named_along₅₉ (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (i : Nat)
    (v : V) {B : Block V} (hB : B ∈ (W i v).st.core.T) :
    ∃ D ∈ (W i v).st.bodies, D.erase = B :=
  Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore facts S rho i v (W i)
    (hW i).1 hB

/-- Along a path `W` of a run, for `i ≤ j`, the bodies of `v`'s store in `W i` are bodies of `v`'s
    store in `W j`. -/
private theorem bodies_mono_along₅₉ (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (v : V)
    {i j : Nat} (hij : i ≤ j) : (W i v).st.bodies ⊆ (W j v).st.bodies :=
  Restated.Vocabulary.Proofs.NamedBodyRetention.stateBefore_bodies_mono facts S rho v hij (W i)
    (hW i).1 (W j) (onePath_slice₅₉ W hW hij)

/-- Two run blocks read through `Xb` along `W` with the same erasure are equal, when the run blocks
    read through `Xb` are free of root collisions. -/
private theorem runBlock_eq_of_erase_eq₅₉ {S : Setup V} {rho : Record.Run V} {W : Nat → V → M.N}
    {Xb : Finset V} (hfree : Restated.RootCollisionFreeOn M S rho W Xb)
    {D B : NamedBlock V} (hD : Restated.RunBlockOn M S rho W Xb D)
    (hB : Restated.RunBlockOn M S rho W Xb B) (h : D.erase = B.erase) : D = B := by
  have hroot : D.root = B.root := by
    rw [← Proofs.NamedWire.erase_root D, h, Proofs.NamedWire.erase_root]
  exact hfree.root_injective D B hD hB D B (Or.inl (Proofs.NamedAncestry.named_self D))
    (Or.inr (Proofs.NamedAncestry.named_self B)) hroot

/-- If `v ∈ Xb`, `n` is a node state of `v`'s round-`r` action read computed from the world of `W`
    strictly before `S.a r`, and `D` is a body of `n`'s store, then `D` is a run block read through
    `Xb` along `W`. -/
theorem actionBody_runBlock_genuineOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} (hv : v ∈ Xb) {r : Round} {n : M.N}
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r)
    {D : NamedBlock V} (hD : D ∈ n.st.bodies) :
    Restated.RunBlockOn M S rho W Xb D :=
  Restated.actionBody_runBlockOn facts S Hs Xb hf hv hn hD

/-- If `p, w ∈ Xb`, `B` is a body of a node state of `p`'s round-`r` action read computed from the
    world of `W` strictly before `S.a r`, and `B.erase` is in the finality-filtered tree of `w`'s
    store in the world of `W` strictly before slot `s`'s vote instant with its clock set to that
    instant, then that store holds `B`. -/
theorem actionBody_at_voteDuty_of_filteredOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {r : Round} {p : V} (hp : p ∈ Xb) {np : M.N}
    (hnp : np ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) p) r)
    {B : NamedBlock V}
    (hBmem : B ∈ np.st.bodies)
    {w : V} (hw : w ∈ Xb) {s : Slot}
    (hfiltered : B.erase ∈ M.get_filtered_block_tree
      (M.toHealing (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) w).st
        (M.vote_time S.E s)).core).toFG) :
    B ∈ (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) w).st
      (M.vote_time S.E s)).bodies := by
  have hrawPre : B.erase ∈ (W (strictEventIndex rho (M.vote_time S.E s)) w).st.core.T := by
    have h := facts.fc.get_filtered_block_tree_subset _ hfiltered
    rw [facts.sto.toHealing_gs_T, facts.hd.Sts_setClock_core_T] at h
    exact h
  obtain ⟨D, hD, hDerase⟩ := exists_named_along₅₉ facts S hf.onePath _ w hrawPre
  have hDrun : Restated.RunBlockOn M S rho W Xb D :=
    Restated.runBlock_of_stateBefore_memOn facts S W Xb hw hD
  have hBrun : Restated.RunBlockOn M S rho W Xb B :=
    Restated.actionBody_runBlock_genuineOn facts S Hs Xb hf hp hnp hBmem
  obtain rfl := runBlock_eq_of_erase_eq₅₉ hf.rootCollisionFree hDrun hBrun hDerase
  rw [facts.hd.Sts_setClock_bodies]
  exact hD

/-- If `p, w ∈ Xb`, `B` is a body of a node state of `p`'s round-`r` action read computed from the
    world of `W` strictly before `S.a r`, and `B.erase` is in the finality-filtered tree of `w`'s
    store in the world of `W` strictly before the vote instant of slot `opening_slot r + 1`, with
    its clock set to that instant, then `B` is a body of every node state of `w`'s round-`r` action
    read computed from the world of `W` strictly before `S.a r`. -/
theorem actionBody_at_action_of_nextVoteFilteredOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {r : Round} {p : V} (hp : p ∈ Xb) {np : M.N}
    (hnp : np ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) p) r)
    {B : NamedBlock V}
    (hBmem : B ∈ np.st.bodies)
    {w : V} (hw : w ∈ Xb)
    (hfiltered : B.erase ∈ M.get_filtered_block_tree
      (M.toHealing (M.ns_setClock S.E
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc r + 1))) w).st
        (M.vote_time S.E (M.opening_slot S.hc r + 1))).core).toFG) :
    ∀ nw ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) w) r,
      B ∈ nw.st.bodies := by
  intro nw hnw
  have hvote := Restated.actionBody_at_voteDuty_of_filteredOn facts S Hs Xb hf hp hnp hBmem hw
    hfiltered
  rw [facts.hd.Sts_setClock_bodies] at hvote
  rw [actionReadFrom_bodies₅₉ facts S _ r nw hnw]
  exact bodies_mono_along₅₉ facts S hf.onePath w
    (strictEventIndex_mono rho (Restated.Vocabulary.Protocol.next_vote_time_lt_action facts S r).le)
    hvote

/-- If `p ∈ Xb`, `n` is a node state of `p`'s round-`r` action read computed from the world of `W`
    strictly before `S.a r`, the Q2 of `n` can return `some Q.erase` and `n`'s store holds `Q`, then
    `p`'s store in the world of `W` strictly before round `r`'s grade-2 domain instant holds `Q`. -/
theorem selectedQ2_body_at_captureOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {r : Round} {p : V} (hp : p ∈ Xb) {Q : NamedBlock V} {n : M.N}
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) p) r)
    (hselected : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ some Q.erase)
    (hQmem : Q ∈ n.st.bodies) :
    Q ∈ (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) p).st.bodies := by
  have hQrun : Restated.RunBlockOn M S rho W Xb Q :=
    Restated.actionBody_runBlock_genuineOn facts S Hs Xb hf hp hn hQmem
  obtain ⟨cc, hcc, st', hst', rfl⟩ := hn
  unfold Restated.Vocabulary.Internal.PhaseGrades.nodeQ2
    Restated.Vocabulary.Internal.PhaseGrades.nodeRead at hselected
  obtain ⟨G, hG, hGQ⟩ := returns_map_elim₅₉ _ _ _ hselected
  obtain ⟨x, hx⟩ := facts.dt.grade2_block_with_nonempty
    (M.gradeContract (M.mkNode st' (W (strictEventIndex rho
      (Restated.Vocabulary.Execution.Setup.a M S r)) p).record cc).cache) S.E S.hc
    (M.toHealing (M.mkNode st' (W (strictEventIndex rho
      (Restated.Vocabulary.Execution.Setup.a M S r)) p).record cc).st.core) r
  have hxQ : x = some Q.erase :=
    (facts.dt.grade2_block_with_eq_read_Q2 _ S.E S.hc _ r G hG x hx).trans hGQ
  rw [hxQ] at hx
  obtain ⟨j, raw, -, hj, hfreeze, hQraw⟩ :=
    facts.grRun.q2_capture_at_action_read_along S rho W hf.onePath
      (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) p r Q.erase cc hcc st'
      hst' hx
  obtain ⟨fr, hfr⟩ := facts.gr.freezeRoot_nonempty S.E (M.gradeView (M.toHealing (W j p).st.core))
    (W j p).st.core.F S.hc.η_SG r (M.early S.E S.hc r .g2) (M.late S.E S.hc r .g2)
  have hrawTree : raw ∈ (W j p).st.core.T := by
    have h := facts.gr.mem_T_of_freezeRoot_eq_some fr hfr (hfreeze fr hfr)
    rw [facts.gr.Sts_gradeView_T] at h
    exact h
  have hQTree : Q.erase ∈ (W j p).st.core.T := by
    have hpc : Restated.Vocabulary.Internal.ParentClosed M (W j p).st.core :=
      Restated.Vocabulary.Proofs.NamedStoreBridge.parentClosed_stateBefore facts S rho j p (W j)
        (hf.onePath j).1
    have h := Proofs.Records.mem_of_preceq hpc.2 Q.erase raw
      (by rw [facts.sto.toHealing_gs_T]; exact hrawTree) (preceq_eq_true_iff_Preceq.mpr hQraw)
    rw [facts.sto.toHealing_gs_T] at h
    exact h
  obtain ⟨D, hD, hDerase⟩ := exists_named_along₅₉ facts S hf.onePath j p hQTree
  have hDrun : Restated.RunBlockOn M S rho W Xb D :=
    Restated.runBlock_of_stateBefore_memOn facts S W Xb hp hD
  obtain rfl := runBlock_eq_of_erase_eq₅₉ hf.rootCollisionFree hDrun hQrun hDerase
  rcases Restated.stateBefore_tick_eq_stateBeforeTimeOn facts S Hs Xb hf hj with h | h
  · rw [← h]
    exact hD
  · rw [h, (facts.nd.wake_st_record _).1] at hD
    exact hD

/-- Under the bundle along `W`, if round `r` is ready (`GradeRoundReady`), `p`, in the set for
    `domain r g2`, has a node state of its round-`r` action read whose Q2 can return `some Q.erase`
    and whose store holds `Q`, `FinalityFloorAtOn` over `X` holds along `W` up to `stop` at
    `blocked` from `Tprev ⪯ Q`, `Q` is at height `blocked + 1`, and round `r`'s action read is
    before `stop`, then every `reader` in `X` and in the set for `domain r g1` holds `Q` at every
    node state of its round-`r` action read and at its store in the world of `W` strictly before the
    vote instant of round `r`'s opening slot, with its clock set to that instant. -/
theorem selectedQ2_body_at_action_and_openingVote_of_floorOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb X : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {r : Round} (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho r)
    {p : V} (hp : p ∈ Hs (M.domain S.E S.hc r .g2)) {Q : NamedBlock V} {n : M.N}
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) p) r)
    (hselected : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ some Q.erase)
    (hQmem : Q ∈ n.st.bodies)
    {stop : Nat} {blocked : Height} {Tprev : Block V}
    (hfloor : Restated.FinalityFloorAtOn M S rho W X Xb blocked stop Tprev)
    (hQheight : (M.derive_named S.E S.cfg Q).h = blocked + 1)
    (hTQ : Block.Preceq Tprev Q.erase)
    (hactionPrefix : strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r) ≤ stop)
    {reader : V} (hreader : reader ∈ Hs (M.domain S.E S.hc r .g1)) (hreaderX : reader ∈ X)
    (hlo : lo ≤ M.early S.E S.hc r .g2) :
    (∀ nr ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) reader) r,
        Q ∈ nr.st.bodies) ∧
      Q ∈ (M.ns_setClock S.E
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc r))) reader).st
        (M.vote_time S.E (M.opening_slot S.hc r))).bodies := by
  have hpXb : p ∈ Xb := hHsXb _ hp
  have hQsource : Q ∈ (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) p).st.bodies :=
    Restated.selectedQ2_body_at_captureOn facts S Hs Xb hf hpXb hn hselected hQmem
  have hQrun : Restated.RunBlockOn M S rho W Xb Q :=
    Restated.actionBody_runBlock_genuineOn facts S Hs Xb hf hpXb hn hQmem
  have hpostSource : lo ≤ M.domain S.E S.hc r .g2 := hlo.trans (facts.gr.early_le_domain S r)
  have hdeadline : max (M.domain S.E S.hc r .g2) lo + S.E.Δ ≤ M.domain S.E S.hc r .g1 := by
    rw [max_eq_left hpostSource]
    exact facts.gr.domain_g2_add_delta_le_domain_g1 S r
  have hpMax : p ∈ Hs (max (M.domain S.E S.hc r .g2) lo) := by
    rw [max_eq_left hpostSource]
    exact hp
  have horder : M.domain S.E S.hc r .g1 ≤ M.vote_time S.E (M.opening_slot S.hc r) := by
    rw [facts.gr.Sts_domain_g1_eq_opening, facts.gr.opening_eq_proposal_time]
    exact (facts.sch.proposal_time_lt_vote_time S.E _).le
  have hcut : M.domain S.E S.hc r .g1 ≤ rho.horizon :=
    (facts.gr.domain_le_domain_g0 S r .g1).trans ready.2
  have hvoteAction : M.vote_time S.E (M.opening_slot S.hc r) ≤
      Restated.Vocabulary.Execution.Setup.a M S r := by
    calc
      M.vote_time S.E (M.opening_slot S.hc r) ≤ M.confirmation_time S.E (M.opening_slot S.hc r) :=
        facts.sch.Protocol_vote_time_le_confirmation_time S.E _
      _ = Restated.Vocabulary.Execution.Setup.a M S r :=
        Restated.Vocabulary.Proofs.HealingSurface.opening_confirmation_time_eq_action facts S r
  have hvotePrefix : strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc r)) ≤ stop :=
    (strictEventIndex_mono rho hvoteAction).trans hactionPrefix
  have hFvote : Block.Preceq
      (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc r))) reader).st.core.F
      Q.erase :=
    hfloor.storeF_preceq_sourceHeightBlock facts hreaderX hvotePrefix hQrun hQheight hTQ
  have hQvote := Restated.healthy_head_body_at_read_after_gst_admitOn facts
    S rho Hs Xb hf hHs hHsXb p reader Q
      (M.domain S.E S.hc r .g2) (M.domain S.E S.hc r .g1)
      (M.vote_time S.E (M.opening_slot S.hc r)) hpMax hreader hQsource hdeadline horder hcut
      hFvote
  refine ⟨?_, ?_⟩
  · intro nr hnr
    rw [actionReadFrom_bodies₅₉ facts S _ r nr hnr]
    exact bodies_mono_along₅₉ facts S hf.onePath reader (strictEventIndex_mono rho hvoteAction)
      hQvote.1
  · rw [facts.hd.Sts_setClock_bodies]
    exact hQvote.1

/-- Under the bundle along `W`, if `0 < r`, round `r` is ready (`GradeRoundReady`), `w` is in the
    set for `domain r g1`, `w`'s tick at `domain r g1` has an outcome, `c` is an outcome of the
    phase tick at the vote instant of slot `opening_slot r + 1` on `w`'s node state in the world of
    `W` strictly before that instant, the grade-1 frame read with `c` on `w`'s store there with its
    clock set holds `root`, and `L` is the active prefix of `root` in that store's filtered tree,
    then every outcome of the grade-1 store grade of `L` at `w`'s store in the world of `W` strictly
    before `domain r g1` is `true`. -/
theorem activeVoterAnchor_storeGrade_g1On (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {r : Round} (hr : 0 < r)
    (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho r)
    {w : V} (hw : w ∈ Hs (M.domain S.E S.hc r .g1)) {root L : Block V}
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
    (hlo : lo ≤ M.early S.E S.hc r .g2)
    (hneTick : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w (M.domain S.E S.hc r .g1)) →
      ∃ out : M.N × List (NamedObject V), M.tick S w (W j w) (M.domain S.E S.hc r .g1) ⇢ out) :
    ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
      (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st r .g1 L ⇢ b → b = true := by
  intro b hb
  set t := M.vote_time S.E (M.opening_slot S.hc r + 1) with ht
  set d := W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w with hd
  have hround : M.round_of S.hc (S.E.slotOf t) = r := by
    rw [ht, facts.sch.slotOf_vote_time]
    exact facts.gr.HealingLemmas_round_of_opening_succ S.hc r
  have hdomainVote : M.domain S.E S.hc r .g1 < t := by
    rw [ht, facts.gr.Sts_domain_g1_eq_opening, facts.gr.opening_eq_proposal_time]
    exact (facts.sch.proposal_time_mono S.E (Nat.le_succ _)).trans_lt
      (facts.sch.proposal_time_lt_vote_time S.E _)
  have hvoteAction : t ≤ Restated.Vocabulary.Execution.Setup.a M S r :=
    (Restated.Vocabulary.Protocol.next_vote_time_lt_action facts S r).le
  have hg1Horizon : M.domain S.E S.hc r .g1 ≤ rho.horizon :=
    (facts.gr.domain_le_domain_g0 S r .g1).trans ready.2
  have hlog1 : lo ≤ M.domain S.E S.hc r .g1 :=
    hlo.trans ((facts.gr.early_le_domain S r).trans (facts.gr.domain_g2_le_domain_g1 S r))
  obtain ⟨fr, hfr⟩ := facts.gr.freezeRoot_nonempty S.E (M.gradeView (M.toHealing d.st.core))
    d.st.core.F S.hc.η_SG r (M.early S.E S.hc r .g1) (M.late S.E S.hc r .g1)
  have hbase := Restated.frame_phase_completedOn facts S rho Hs Xb hf w r hr .g1 hw t hdomainVote
    hvoteAction hg1Horizon hlog1 hneTick fr hfr
  have hprepared := facts.grRun.frame_phase_prepared_eq_of_outcomes S rho w r .g1 t hround _
    (W (strictEventIndex rho t)) (mem_stateBeforeTime_along₅₉ hf.sorted hf.onePath t) hbase c hc
  rw [facts.gr.phaseResult_g1, hframe] at hprepared
  cases fr with
  | none => simp at hprepared
  | some raw =>
    have hrootEq : root = M.clipGrade raw (W (strictEventIndex rho t) w).st.core.F := by
      simpa using hprepared
    have hLroot : Block.Preceq L root := facts.gr.preceq_of_activePrefix_eq_some hactive
    have hLraw : Block.Preceq L raw := by
      rw [hrootEq] at hLroot
      exact preceq_trans_Preceq hLroot (facts.gr.q10_clip_preceq raw _)
    obtain ⟨braw, hbraw⟩ := facts.gr.gradeBool_nonempty S.E
      (M.gradeView (M.toHealing d.st.core)) d.st.core.F
      S.hc.η_SG r (M.early S.E S.hc r .g1) (M.late S.E S.hc r .g1) raw
    exact facts.csAdded.confirmation_phaseGrade_mono S.E S.hc _ _ r .g1 hLraw braw hbraw
      (facts.gr.gradeBool_of_freezeRoot_eq_some _ hfr rfl braw hbraw) b hb

/-- A `GenuineConfirmation` of `B` gives an outcome `early` of the early confirmation votes, the
    confirmation votes it filters to, and scores `sc` of them for which `B`'s score is more than
    half the late voter count. -/
private theorem genuine_eligible₅₉ (facts : Record.Facts M) {contract : M.Contract} {E : Env V}
    {hc : Protocol.HealConfig} {st : M.S} {s : Slot} {B : Block V}
    (hB : Restated.Vocabulary.Protocol.GenuineConfirmation M (contract := contract) E hc st s B) :
    ∃ (early : Finset (GoldfishVote V)) (sc : Block V → Nat),
      Restated.Vocabulary.Protocol.confEarly M E st s ⇢ early ∧
      Restated.Vocabulary.Protocol.confVotes M E st s ⇢
        early.filter (fun x => M.no_second_vote_in (Restated.Vocabulary.Protocol.confLate M E st s) x = true) ∧
      (∀ B', M.goldfish_score E st.T
        (early.filter (fun x => M.no_second_vote_in (Restated.Vocabulary.Protocol.confLate M E st s) x = true))
        (early.filter (fun x => M.no_second_vote_in (Restated.Vocabulary.Protocol.confLate M E st s) x = true))
        s B' ⇢ sc B') ∧
      M.voters_count E (Restated.Vocabulary.Protocol.confLate M E st s) s < 2 * sc B := by
  obtain ⟨tm, htm⟩ := facts.sto.tau_nonempty st
  obtain ⟨R, hR⟩ := facts.fc.get_sg_root_with_nonempty contract E hc st.toHealing
    (M.round_of hc st.s)
  have hearly : Restated.Vocabulary.Protocol.confEarly M E st s ⇢
      beforeCutoff tm (M.support_cutoff E s) (st.pool s) :=
    returns_map_intro₅₉ _ _ _ htm
  have hu := returns_map_intro₅₉
    (fun e => e.filter (fun x => M.no_second_vote_in (Restated.Vocabulary.Protocol.confLate M E st s) x = true))
    _ _ hearly
  choose sc hsc using fun B' => facts.fc.goldfish_score_nonempty E st.T
    ((beforeCutoff tm (M.support_cutoff E s) (st.pool s)).filter
      (fun x => M.no_second_vote_in (Restated.Vocabulary.Protocol.confLate M E st s) x = true))
    ((beforeCutoff tm (M.support_cutoff E s) (st.pool s)).filter
      (fun x => M.no_second_vote_in (Restated.Vocabulary.Protocol.confLate M E st s) x = true)) s B'
  obtain ⟨H, hH⟩ := facts.fc.ghost_nonempty R (Restated.Vocabulary.Protocol.confTree M st) sc
    (fun B' => decide (Restated.Vocabulary.Protocol.confCount M E st s < 2 * sc B'))
  have helig := hB.genuine R hR _ hu sc hsc H hH
  obtain ⟨st', hst'⟩ := facts.dt.update_confirmation_with_nonempty contract E hc st s
  have hW := facts.hd.update_confirmation_with_live_confirmed_of_eligible contract E hc st s tm htm
    R hR sc hsc H hH helig st' hst'
  have hBH : B = H := (hB.selected st' hst').symm.trans hW
  subst hBH
  exact ⟨_, sc, hearly, hu, hsc, of_decide_eq_true helig⟩

/-- The store a tick at `t` hands its first duty, staged from `n`'s core store, has the block tree
    of `n`'s core store. -/
private theorem tickStore_T₅₉ (facts : Record.Facts M) {S : Setup V} (n : M.N) (t : Time) :
    (Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t).T = n.st.core.T := by
  rw [Restated.Vocabulary.Proofs.Optimistic.tickStore,
    ← facts.hd.setClock_core_eq_store_with_t_s S.E n.st t, facts.hd.Sts_setClock_core_T]

/-- The store a tick at `t` hands its first duty, staged from `n`'s core store, has the block stamps
    of `n`'s core store. -/
private theorem tickStore_timestamp_block₅₉ (facts : Record.Facts M) {S : Setup V} (n : M.N)
    (t : Time) :
    (Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t).timestamp_block =
      n.st.core.timestamp_block := by
  rw [Restated.Vocabulary.Proofs.Optimistic.tickStore,
    ← facts.hd.setClock_core_eq_store_with_t_s S.E n.st t, facts.hd.setClock_core_timestamp_block]

omit [DecidableEq V] [Fintype V] in
/-- For `Δ > 0`, if `a` and `b` are multiples of `Δ` and `a < b`, then `a + Δ ≤ b`. -/
private theorem add_delta_le_of_lt_emod₅₉ {Δ a b : Int} (hΔ : 0 < Δ) (ha : a % Δ = 0)
    (hb : b % Δ = 0) (hab : a < b) : a + Δ ≤ b := by
  obtain ⟨k, rfl⟩ := Int.dvd_of_emod_eq_zero ha
  obtain ⟨l, rfl⟩ := Int.dvd_of_emod_eq_zero hb
  have hkl : k < l := by
    by_contra h
    have h' : l ≤ k := not_lt.mp h
    have : Δ * l ≤ Δ * k := Int.mul_le_mul_of_nonneg_left h' (le_of_lt hΔ)
    omega
  have h1 : k + 1 ≤ l := hkl
  have h2 : Δ * (k + 1) ≤ Δ * l := Int.mul_le_mul_of_nonneg_left h1 (le_of_lt hΔ)
  rw [Int.mul_add, Int.mul_one] at h2
  exact h2

/-- A slot's support cutoff plus one delay is at most the slot's view freeze. -/
private theorem support_cutoff_add_delta_le_view_freeze₅₉ (facts : Record.Facts M) (S : Setup V)
    (s : Slot) : M.support_cutoff S.E s + S.E.Δ ≤ M.view_freeze S.E s := by
  obtain ⟨k, hk⟩ := (facts.sch.publicTime_iff S (M.view_freeze S.E s)).mpr
    ⟨s, Or.inr (Or.inr (Or.inr rfl))⟩
  have hb : M.view_freeze S.E s % S.E.Δ = 0 := by
    rw [hk]
    exact Int.mul_emod_left _ _
  exact add_delta_le_of_lt_emod₅₉ S.E.Δ_pos (facts.sch.support_cutoff_emod_delta S s) hb
    (facts.sch.Optimistic_support_cutoff_lt_view_freeze S.E s)

/-- In a named store whose bodies contain genesis and the parent of each body, every named ancestor
    of a held body is held. -/
private theorem namedAncestor_mem₅₉ {st : M.NS}
    (hpc : Restated.Vocabulary.Proofs.NamedStore.NamedParentClosed M st) {A B : NamedBlock V}
    (hB : B ∈ st.bodies) (hAB : NamedBlock.Preceq A B) : A ∈ st.bodies := by
  revert hB hAB
  induction B with
  | genesis =>
      intro hB hAB
      simp only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] at hAB
      exact hAB ▸ hB
  | node p s r gv gsv ats proposer ih =>
      intro hB hAB
      simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hAB
      rcases hAB with rfl | hparent
      · exact hB
      · exact ih (by simpa only [NamedBlock.parent] using hpc.2 _ hB)
          (by unfold NamedBlock.Preceq; exact hparent)

/-- Under the bundle along `W`, if `p`, in the set for `support_cutoff (opening_slot r)`, has
    `GenuineConfirmation` of `C` at the opening slot on its confirmation store read from `W`,
    `B ⪯ C` is a body of a node state of `p`'s round-`r` action read at height `blocked + 1` that is
    a descendant of `Tprev`, `FinalityFloorAtOn` over `X` holds along `W` up to `stop`, and round
    `r`'s action read is before `stop`, then for every `reader` in `X` and in the set for
    `view_freeze (opening_slot r)`, the reader's store in the world of `W` strictly before the vote
    instant of slot `opening_slot r + 1`, with its clock set to that instant, holds `B`. -/
theorem ancestorGenuineConfirmation_body_at_nextVote_of_floorOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb X : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
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
    {stop : Nat} {blocked : Height} {Tprev : Block V}
    (hfloor : Restated.FinalityFloorAtOn M S rho W X Xb blocked stop Tprev)
    (hBheight : (M.derive_named S.E S.cfg B).h = blocked + 1)
    (hTB : Block.Preceq Tprev B.erase)
    (hactionPrefix : strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r) ≤ stop)
    (hactionHor : Restated.Vocabulary.Execution.Setup.a M S r ≤ rho.horizon)
    {reader : V} (hreader : reader ∈ Hs (M.view_freeze S.E (M.opening_slot S.hc r)))
    (hreaderX : reader ∈ X)
    (hlo : lo ≤ M.early S.E S.hc r .g2) :
    B ∈ (M.ns_setClock S.E
      (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc r + 1))) reader).st
      (M.vote_time S.E (M.opening_slot S.hc r + 1))).bodies := by
  set s := M.opening_slot S.hc r with hs
  set j := strictEventIndex rho (M.confirmation_time S.E s) with hj
  set cw := Restated.Vocabulary.Proofs.Optimistic.tickStore M S (W j p).st.core
    (M.confirmation_time S.E s) with hcw
  set late := Restated.Vocabulary.Protocol.confLate M S.E cw s with hlate
  have hBscope : Restated.RunBlockOn M S rho W Xb B :=
    Restated.actionBody_runBlock_genuineOn facts S Hs Xb hf (hHsXb _ hp) hnp hBmem
  have hvoteAction : M.vote_time S.E (s + 1) ≤ Restated.Vocabulary.Execution.Setup.a M S r :=
    (Restated.Vocabulary.Protocol.next_vote_time_lt_action facts S r).le
  have hvotePrefix : strictEventIndex rho (M.vote_time S.E (s + 1)) ≤ stop :=
    (strictEventIndex_mono rho hvoteAction).trans hactionPrefix
  have hFvote : Block.Preceq
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) reader).st.core.F B.erase :=
    hfloor.storeF_preceq_sourceHeightBlock facts hreaderX hvotePrefix hBscope hBheight hTB
  have hpcRead := (Restated.voteDuty_parentClosed_agrees_rootInjectiveOn facts S Hs Xb hf
    (hHsXb _ hreader) (s + 1)).1
  have hgenuine' : Restated.Vocabulary.Protocol.GenuineConfirmation M (contract := contract)
      S.E S.hc cw s C :=
    ⟨hgenuine.selected, hgenuine.genuine⟩
  obtain ⟨early, sc, hearly, hcvq, hsc, helig⟩ := genuine_eligible₅₉ facts hgenuine'
  obtain ⟨τ, hτ, hτe⟩ := returns_map_elim₅₉ _ _ _ hearly
  have hel : early ⊆ late := by
    intro u hu
    rw [← hτe, mem_beforeCutoff_iff] at hu
    have h1 := facts.sto.stampedBefore_vote_of_tau cw τ hτ hu.2
    exact Protocol.beforeCutoff_mono _ (facts.sch.Protocol_support_cutoff_le_confirmation_time S.E s) _
      ((mem_beforeCutoff_iff _ _ _ _).mpr ⟨hu.1, h1⟩)
  obtain ⟨R, hR⟩ := facts.fc.raw_supporters_nonempty cw.T
    (early.filter (fun x => M.no_second_vote_in late x = true))
    (early.filter (fun x => M.no_second_vote_in late x = true)) s C
  have hscR : sc C = R.card :=
    facts.fc.Numerator_score_eq_supporters early late _ hel rfl S.E cw.T s C (sc C) (hsc C) R hR
  choose tu htu using fun u => facts.fc.targets_under_nonempty cw.T C u
  have hpositive : 0 < R.card := by
    rw [hscR] at helig
    omega
  obtain ⟨x, hxSupport⟩ := Finset.card_pos.mp hpositive
  obtain ⟨_, u, hu, hus, htargets⟩ :=
    (facts.fc.mem_supporters_iff (_E := S.E) R hR tu htu).mp hxSupport
  obtain ⟨head, hfind, -, hChead⟩ := (facts.fc.targets_under_iff (tu u) (htu u)).mp htargets
  have hCheadP : Block.Preceq C head := preceq_eq_true_iff_Preceq.mp hChead
  by_cases hgen : head = Block.genesis
  · subst head
    have hCgen : C = Block.genesis :=
      Block.preceq_antisymm hChead (Protocol.preceq_genesis C)
    subst C
    have hBgen : B.erase = Block.genesis := eq_genesis_of_Preceq_genesis hBC
    have hBeq : B = NamedBlock.genesis := eq_named_genesis_of_erase_eq_genesis hBgen
    subst B
    exact hpcRead.1
  · have hheadSource : head ∈ (W j p).st.core.T := by
      have h := Proofs.HealingLemmas.find?_mem hfind
      rw [hcw, tickStore_T₅₉ facts] at h
      exact h
    have huEarly : u ∈ early :=
      (Finset.mem_filter.mp ((facts.sch.mem_votes_by_iff _ _ _).mp hu).1).1
    have hresolved : stampedBefore τ (M.support_cutoff S.E s) u = true := by
      rw [← hτe, mem_beforeCutoff_iff] at huEarly
      exact huEarly.2
    have hheadStamp : stampedBefore cw.timestamp_block (M.support_cutoff S.E s) head = true :=
      facts.sto.stampedBefore_block_of_tau _ hfind τ hτ hresolved
    obtain ⟨Hn, hHnPre, hHnErase⟩ := exists_named_along₅₉ facts S hf.onePath j p hheadSource
    have hstampPre : stampedBefore (W j p).st.core.timestamp_block
        (M.support_cutoff S.E s) Hn.erase = true := by
      rw [hcw, tickStore_timestamp_block₅₉ facts, ← hHnErase] at hheadStamp
      exact hheadStamp
    have hpostSupport : lo ≤ M.support_cutoff S.E s := by
      have h1 := facts.gr.early_g2_le_opening S r
      rw [facts.gr.opening_eq_proposal_time] at h1
      have h2 := facts.sch.proposal_time_lt_vote_time S.E (M.opening_slot S.hc r)
      have h3 := Restated.vote_time_lt_support_cutoff_l49 facts S (M.opening_slot S.hc r)
      linarith
    have hHsupport : Hn ∈ (W (strictEventIndex rho (M.support_cutoff S.E s)) p).st.bodies :=
      Restated.body_mem_stateBeforeTime_of_public_stampedBeforeOn facts S rho Hs Xb hf hp
        (Restated.Vocabulary.Protocol.publicTime_support_cutoff facts S s) hpostSupport hHnPre
        hstampPre
    have hdeadline : max (M.support_cutoff S.E s) lo + S.E.Δ ≤ M.view_freeze S.E s := by
      rw [max_eq_left hpostSupport]
      exact support_cutoff_add_delta_le_view_freeze₅₉ facts S s
    have hpMax : p ∈ Hs (max (M.support_cutoff S.E s) lo) := by
      rw [max_eq_left hpostSupport]
      exact hp
    have hviewVote : M.view_freeze S.E s ≤ M.vote_time S.E (s + 1) :=
      (facts.sch.view_freeze_lt_vote_time_succ S.E s).le
    have hviewHorizon : M.view_freeze S.E s ≤ rho.horizon :=
      hviewVote.trans (hvoteAction.trans hactionHor)
    have hBHn : Block.Preceq B.erase Hn.erase := by
      rw [hHnErase]
      exact preceq_trans_Preceq hBC hCheadP
    obtain ⟨hHvote, -, -⟩ :=
      Restated.healthy_head_body_at_read_after_gst_admitOn facts
        S rho Hs Xb hf hHs hHsXb p reader Hn
          (M.support_cutoff S.E s) (M.view_freeze S.E s) (M.vote_time S.E (s + 1)) hpMax hreader
          hHsupport hdeadline hviewVote hviewHorizon (preceq_trans_Preceq hFvote hBHn)
    have hHscope : Restated.RunBlockOn M S rho W Xb Hn :=
      Restated.runBlock_of_stateBefore_memOn facts S W Xb (hHsXb _ hreader) hHvote
    have hBH : NamedBlock.Preceq B Hn :=
      Restated.namedPreceq_of_runBlock_erase_preceqOn facts Hs Xb hf hBscope hHscope hBHn
    exact namedAncestor_mem₅₉ hpcRead
      (by rw [facts.hd.Sts_setClock_bodies]; exact hHvote) hBH

/-- `m >>= k` can return `b` exactly when `m` can return some `a` from which `k a` can return `b`. -/
private theorem returns_bind_iff₅₉ {α β : Type} (m : DC.NDRE α) (k : α → DC.NDRE β) (b : β) :
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

/-- If `P` is an outcome of the voter's processed block tree of the core store of `st` with the
    cache `c` written in, then the voter candidate tree of `st`'s own core store can return the
    filtered tree drawn from `P` on the core store with `c` written in. -/
private theorem candidate_tree_store_with_cache₅₉ (facts : Record.Facts M) (E : Env V) (st : M.NS)
    (c : M.Cache) (P : Finset (Block V))
    (hP : M.voter_processed_block_tree E
      (M.toHealing (M.store_with_cache st c).core).toFG.toSG.toGoldfishStore
      (M.toHealing (M.store_with_cache st c).core).s ⇢ P) :
    Restated.Vocabulary.Proofs.Optimistic.voter_candidate_tree M E (M.toHealing st.core) ⇢
      M.get_filtered_block_tree_from (M.toHealing (M.store_with_cache st c).core).toFG P := by
  have hs : ∀ x : M.S, (M.toHealing x).s = x.s := fun x => facts.sto.toHealing_gs_s x
  have hP1 := hP
  rw [hs, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_voter_processed_block_tree] at hP1
  have hP0 : M.voter_processed_block_tree E (M.toHealing st.core).toFG.toSG.toGoldfishStore
      (M.toHealing st.core).s ⇢ P := by
    rw [hs]
    exact hP1
  obtain ⟨X, hX⟩ := facts.fc.voter_filtered_block_tree_nonempty E st.core st.core.s
  have hX1 : M.voter_filtered_block_tree E (M.store_with_cache st c).core
      (M.store_with_cache st c).core.s ⇢ X := by
    rw [facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_voter_filtered_block_tree]
    exact hX
  rw [facts.fc.voter_candidate_tree_eq_protocol_voter_filtered_block_tree E _ P hP X hX1,
    ← facts.fc.voter_candidate_tree_eq_protocol_voter_filtered_block_tree E _ P hP0 X hX]
  unfold Restated.Vocabulary.Proofs.Optimistic.voter_candidate_tree
  exact (returns_bind_iff₅₉ _ _ _).mpr ⟨P, hP0, (Record.returns_pure _ _).2 rfl⟩

/-- Along a path `W` of a run, for `j ≤ n`, the `h_max` of `v`'s core store in `W j` is at most the
    one in `W n`. -/
private theorem hMax_mono_along₅₉ (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (v : V)
    {j n : Nat} (hjn : j ≤ n) : (W j v).st.core.h_max ≤ (W n v).st.core.h_max :=
  Restated.Vocabulary.Proofs.HealingSurface.stateBefore_hMax_mono facts S rho v hjn (W j) (hW j).1
    (W n) (onePath_slice₅₉ W hW hjn)

/-- Under the bundle along `W`, if `p`, in the set for `support_cutoff (opening_slot r)`, has
    `GenuineConfirmation` of `C` on its confirmation store read from `W`, `B ⪯ C` is at height
    `H + 1`, no member of the set for `vote_time (opening_slot r + 1)` has `h_max ≥ H + 3` along `W`
    at an instant up to `through`, with `through` at or after that instant, and `w`, in that set,
    holds `B` and has it in the filtered tree of its store in the world of `W` strictly before that
    vote instant with its clock set, then `B.erase` is in every outcome of the voter candidate tree
    of that store. -/
theorem ancestorGenuineConfirmation_candidate_at_nextVoteOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {r : Round} (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho r)
    (hactionHor : Restated.Vocabulary.Execution.Setup.a M S r ≤ rho.horizon)
    {p : V} (hp : p ∈ Hs (M.support_cutoff S.E (M.opening_slot S.hc r)))
    {B : NamedBlock V} {C : Block V}
    {contract : M.Contract}
    (hgenuine : Restated.Vocabulary.Protocol.GenuineConfirmationWith M contract S.E S.hc
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc r))) p).st.core
        (M.confirmation_time S.E (M.opening_slot S.hc r)))
      (M.opening_slot S.hc r) C)
    (hBC : Block.Preceq B.erase C)
    {H : Height}
    (hBheight : (M.derive_named S.E S.cfg B).h = H + 1)
    {through : Time}
    (hno : ¬ ∃ v ∈ Hs (M.vote_time S.E (M.opening_slot S.hc r + 1)), ∃ u ≤ through,
      H + 1 + 2 ≤ (W (inclusiveEventIndex rho u) v).st.h_max)
    (hvoteThrough : M.vote_time S.E (M.opening_slot S.hc r + 1) ≤ through)
    {w : V} (hw : w ∈ Hs (M.vote_time S.E (M.opening_slot S.hc r + 1)))
    (hBbody : B ∈ (M.ns_setClock S.E
      (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc r + 1))) w).st
      (M.vote_time S.E (M.opening_slot S.hc r + 1))).bodies)
    (hBfiltered : B.erase ∈ M.get_filtered_block_tree
      (M.toHealing (M.ns_setClock S.E
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc r + 1))) w).st
        (M.vote_time S.E (M.opening_slot S.hc r + 1))).core).toFG)
    (hlo : lo ≤ M.early S.E S.hc r .g2) :
    ∀ T : Finset (Block V), Restated.Vocabulary.Proofs.Optimistic.voter_candidate_tree M S.E
      (M.toHealing (M.ns_setClock S.E
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc r + 1))) w).st
        (M.vote_time S.E (M.opening_slot S.hc r + 1))).core) ⇢ T → B.erase ∈ T := by
  intro T hT
  set s := M.opening_slot S.hc r with hs
  set kv := strictEventIndex rho (M.vote_time S.E (s + 1)) with hkv
  have hcore : (M.ns_setClock S.E (W kv w).st (M.vote_time S.E (s + 1))).core =
      Restated.Vocabulary.Proofs.Optimistic.voteStore M S (W kv w).st.core (s + 1) := by
    rw [Restated.Vocabulary.Proofs.Optimistic.voteStore,
      Restated.Vocabulary.Proofs.Optimistic.tickStore,
      ← facts.hd.setClock_core_eq_store_with_t_s S.E (W kv w).st (M.vote_time S.E (s + 1))]
  rw [hcore] at hT hBfiltered
  set duty := Restated.Vocabulary.Proofs.Optimistic.voteStore M S (W kv w).st.core (s + 1) with hduty
  have hrootB : Block.Preceq (M.get_fg_root (M.toHealing duty).toFG) B.erase :=
    preceq_eq_true_iff_Preceq.mp (facts.fc.preceq_get_fg_root_of_mem_filtered hBfiltered)
  have hrootC : Block.Preceq (M.get_fg_root (M.toHealing duty).toFG) C :=
    preceq_trans_Preceq hrootB hBC
  have hpost : lo ≤ M.proposal_time S.E s := by
    have h1 := facts.gr.early_g2_le_opening S r
    rw [facts.gr.opening_eq_proposal_time] at h1
    exact hlo.trans h1
  have hsourceHor : M.confirmation_time S.E s ≤ rho.horizon := by
    rw [hs, Restated.Vocabulary.Proofs.HealingSurface.opening_confirmation_time_eq_action facts S r]
    exact hactionHor
  have hviewVote : M.view_freeze S.E s ≤ M.vote_time S.E (s + 1) :=
    (facts.sch.view_freeze_lt_vote_time_succ S.E s).le
  have hwView : w ∈ Hs (M.view_freeze S.E s) := hHs _ _ hviewVote hw
  have hloView : lo ≤ M.view_freeze S.E s := by
    have h2 := facts.sch.proposal_time_lt_vote_time S.E s
    have h3 := Restated.vote_time_lt_support_cutoff_l49 facts S s
    have h4 := facts.sch.Optimistic_support_cutoff_lt_view_freeze S.E s
    linarith
  obtain ⟨P, hP, hTP⟩ := (returns_bind_iff₅₉ _ _ _).mp hT
  obtain rfl := (Record.returns_pure _ _).1 hTP
  have hg : Restated.Vocabulary.Protocol.GenuineConfirmation M (contract := contract) S.E S.hc
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.confirmation_time S.E s)) p).st.core
        (M.confirmation_time S.E s)) s C :=
    ⟨hgenuine.selected, hgenuine.genuine⟩
  have hCprocessed : C ∈ P :=
    Restated.voterProcessedTarget_of_genuineConfirmation_after_gstOn facts S Hs Xb hf hHs
      hHsXb hp hwView hpost hsourceHor hg hrootC P hP
  have hBprocessed : B.erase ∈ P :=
    Restated.ancestorProcessed_of_voterProcessedOn facts S Hs Xb hf hwView P hP hCprocessed
      hloView B.erase hBC
  have hBpre : B ∈ (W kv w).st.bodies := by
    rw [facts.hd.Sts_setClock_bodies] at hBbody
    exact hBbody
  have hview := Restated.Vocabulary.Proofs.NamedStoreBridge.derivedView_stateBefore facts S rho kv w
    (W kv) (hf.onePath kv).1 B hBpre
  have hσ : duty.σ = (W kv w).st.core.σ := by
    have h := facts.hd.Sts_setClock_core_σ S.E (W kv w).st (M.vote_time S.E (s + 1))
    rw [hcore] at h
    exact h
  have hhm : duty.h_max = (W kv w).st.core.h_max := by
    have h := facts.hd.setClock_core_h_max S.E (W kv w).st (M.vote_time S.E (s + 1))
    rw [hcore] at h
    exact h
  have hstored : (duty.σ B.erase).h = H + 1 := by
    rw [hσ, hview]
    exact hBheight
  have hmax : duty.h_max ≤ H + 2 := by
    by_contra hnot
    have hgt : H + 1 + 1 < (W kv w).st.core.h_max := by
      rw [← hhm]
      exact Nat.lt_of_not_ge hnot
    have hgtAt : H + 1 + 1 <
        (W (inclusiveEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.h_max :=
      lt_of_lt_of_le hgt (hMax_mono_along₅₉ facts S hf.onePath w
        (strictEventIndex_le_inclusiveEventIndex rho _))
    exact hno ⟨w, hw, M.vote_time S.E (s + 1), hvoteThrough, Nat.succ_le_iff.mpr hgtAt⟩
  refine facts.fc.mem_get_filtered_block_tree_from_of_parts_explicit (M.toHealing duty).toFG
    hBprocessed (facts.fc.finalized_preceq_of_mem_get_filtered_block_tree hBfiltered) hBprocessed
    (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _)) ?_ hrootB
  rw [facts.sto.ModelProperties_toHealing_h_max, facts.sto.ModelProperties_toHealing_σ, hstored]
  exact Nat.sub_le_iff_le_add.mpr hmax

/-- If `v ∈ Xb`, `n` is a node state of `v`'s round-`r` action read computed from the world of `W`
    strictly before `S.a r`, and `D` is a body of `n`'s store, then `D` is a run block read through
    `Xb` along `W`. -/
theorem actionBody_runBlock_k6On (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} (hv : v ∈ Xb) {r : Round} {n : M.N}
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r)
    {D : NamedBlock V} (hD : D ∈ n.st.bodies) :
    Restated.RunBlockOn M S rho W Xb D :=
  Restated.actionBody_runBlockOn facts S Hs Xb hf hv hn hD

/-- A slot's proposal instant plus two delays is at most the slot's support cutoff. -/
private theorem proposal_time_add_two_delta_le_support_cutoff₅₉ (facts : Record.Facts M)
    (S : Setup V) (s : Slot) :
    M.proposal_time S.E s + 2 * S.E.Δ ≤ M.support_cutoff S.E s := by
  have h1 := add_delta_le_of_lt_emod₅₉ S.E.Δ_pos (facts.sch.proposal_time_emod_delta_inclX S.E s)
    (facts.sch.vote_time_emod_delta S s) (facts.sch.proposal_time_lt_vote_time S.E s)
  have h2 := add_delta_le_of_lt_emod₅₉ S.E.Δ_pos (facts.sch.vote_time_emod_delta S s)
    (facts.sch.support_cutoff_emod_delta S s) (Restated.vote_time_lt_support_cutoff_l49 facts S s)
  linarith

/-- Under the bundle along `W`, if round `r` is ready (`GradeRoundReady`), `S.a r` is within the
    horizon, `p` is in the set for `domain r g0`, `w` is in the set for `domain r g0 + Δ`, and `L`
    is in the filtered tree of `w`'s store in the world of `W` strictly before the vote instant of
    slot `opening_slot r + 1` with its clock set, then the finalized block of `p`'s core store in
    the world of `W` strictly before `domain r g0` is an ancestor of `L`. -/
theorem sourceG0Finalized_preceq_firstInteriorActiveOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {r : Round} (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho r)
    (hactionHor : Restated.Vocabulary.Execution.Setup.a M S r ≤ rho.horizon)
    {p w : V} (hp : p ∈ Hs (M.domain S.E S.hc r .g0))
    (hw : w ∈ Hs (M.domain S.E S.hc r .g0 + S.E.Δ))
    {L : Block V}
    (hL : L ∈ M.get_filtered_block_tree
      (M.toHealing (M.ns_setClock S.E
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc r + 1))) w).st
        (M.vote_time S.E (M.opening_slot S.hc r + 1))).core).toFG)
    (hlo : lo ≤ M.early S.E S.hc r .g2) :
    Block.Preceq (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) p).st.core.F L := by
  have hpost : lo ≤ M.domain S.E S.hc r .g0 :=
    hlo.trans ((facts.gr.early_le_domain S r).trans (facts.gr.domain_le_domain_g0 S r .g2))
  have houtVote : M.domain S.E S.hc r .g0 + S.E.Δ ≤ M.vote_time S.E (M.opening_slot S.hc r + 1) := by
    rw [facts.gr.domain_g0_eq_opening, facts.gr.opening_eq_proposal_time]
    have h1 := proposal_time_add_two_delta_le_support_cutoff₅₉ facts S (M.opening_slot S.hc r)
    have h2 := facts.sch.Optimistic_support_cutoff_lt_view_freeze S.E (M.opening_slot S.hc r)
    have h3 := facts.sch.view_freeze_lt_vote_time_succ S.E (M.opening_slot S.hc r)
    linarith
  have hvoteHor : M.vote_time S.E (M.opening_slot S.hc r + 1) ≤ rho.horizon :=
    (Restated.Vocabulary.Protocol.next_vote_time_lt_action facts S r).le.trans hactionHor
  have hrelay := Restated.finalized_preceq_of_evidence_deliveredOn facts S Hs Xb hf hHs hHsXb
    hf.slashableBound hp hw hpost rfl (houtVote.trans hvoteHor)
  have hmono := F_mono_along₅₉ facts S hf.onePath w (strictEventIndex_mono rho houtVote)
  have hvoteL : Block.Preceq
      (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc r + 1))) w).st.core.F L := by
    have h := F_preceq_of_mem_filtered₅₉ facts _ hL
    rw [facts.hd.setClock_core_F] at h
    exact h
  exact preceq_trans_Preceq hrelay (preceq_trans_Preceq hmono hvoteL)

/-- Under the hypotheses of `activeVoterAnchor_storeGrade_g1On`, the freeze root of `w`'s grade view
    in the world of `W` strictly before `domain r g1` can return some `raw` of which `L` is an
    ancestor. -/
private theorem activeVoterAnchor_raw₅₉ (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {r : Round} (hr : 0 < r)
    (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho r)
    {w : V} (hw : w ∈ Hs (M.domain S.E S.hc r .g1)) {root L : Block V}
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
    (hlo : lo ≤ M.early S.E S.hc r .g2)
    (hneTick : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w (M.domain S.E S.hc r .g1)) →
      ∃ out : M.N × List (NamedObject V), M.tick S w (W j w) (M.domain S.E S.hc r .g1) ⇢ out) :
    ∃ raw : Block V,
      M.freezeRoot S.E
        (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st.core))
        (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st.core.F S.hc.η_SG r
        (M.early S.E S.hc r .g1) (M.late S.E S.hc r .g1) ⇢ some raw ∧
      Block.Preceq L raw := by
  set t := M.vote_time S.E (M.opening_slot S.hc r + 1) with ht
  set d := W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w with hd
  have hround : M.round_of S.hc (S.E.slotOf t) = r := by
    rw [ht, facts.sch.slotOf_vote_time]
    exact facts.gr.HealingLemmas_round_of_opening_succ S.hc r
  have hdomainVote : M.domain S.E S.hc r .g1 < t := by
    rw [ht, facts.gr.Sts_domain_g1_eq_opening, facts.gr.opening_eq_proposal_time]
    exact (facts.sch.proposal_time_mono S.E (Nat.le_succ _)).trans_lt
      (facts.sch.proposal_time_lt_vote_time S.E _)
  have hvoteAction : t ≤ Restated.Vocabulary.Execution.Setup.a M S r :=
    (Restated.Vocabulary.Protocol.next_vote_time_lt_action facts S r).le
  have hg1Horizon : M.domain S.E S.hc r .g1 ≤ rho.horizon :=
    (facts.gr.domain_le_domain_g0 S r .g1).trans ready.2
  have hlog1 : lo ≤ M.domain S.E S.hc r .g1 :=
    hlo.trans ((facts.gr.early_le_domain S r).trans (facts.gr.domain_g2_le_domain_g1 S r))
  obtain ⟨fr, hfr⟩ := facts.gr.freezeRoot_nonempty S.E (M.gradeView (M.toHealing d.st.core))
    d.st.core.F S.hc.η_SG r (M.early S.E S.hc r .g1) (M.late S.E S.hc r .g1)
  have hbase := Restated.frame_phase_completedOn facts S rho Hs Xb hf w r hr .g1 hw t hdomainVote
    hvoteAction hg1Horizon hlog1 hneTick fr hfr
  have hprepared := facts.grRun.frame_phase_prepared_eq_of_outcomes S rho w r .g1 t hround _
    (W (strictEventIndex rho t)) (mem_stateBeforeTime_along₅₉ hf.sorted hf.onePath t) hbase c hc
  rw [facts.gr.phaseResult_g1, hframe] at hprepared
  cases fr with
  | none => simp at hprepared
  | some raw =>
    have hrootEq : root = M.clipGrade raw (W (strictEventIndex rho t) w).st.core.F := by
      simpa using hprepared
    have hLroot : Block.Preceq L root := facts.gr.preceq_of_activePrefix_eq_some hactive
    refine ⟨raw, hfr, ?_⟩
    rw [hrootEq] at hLroot
    exact preceq_trans_Preceq hLroot (facts.gr.q10_clip_preceq raw _)

/-- Under the bundle along `W`, if `0 < r`, round `r` is ready (`GradeRoundReady`), `w` is in the
    set for `domain r g1`, `w`'s tick at `domain r g1` has an outcome, the grade-1 frame read with
    an outcome `c` of the phase tick on `w`'s next-vote store holds `root`, and `L` is the active
    prefix of `root` in that store's filtered tree, then some named `Ln` with `Ln.erase = L` is a
    body of `w`'s store in the world of `W` strictly before `domain r g1` and a run block read
    through `Xb` along `W`. -/
theorem activeVoterAnchor_namedBody_at_g1DomainOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {r : Round} (hr : 0 < r)
    (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho r)
    {w : V} (hw : w ∈ Hs (M.domain S.E S.hc r .g1)) {root L : Block V}
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
    (hlo : lo ≤ M.early S.E S.hc r .g2)
    (hneTick : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w (M.domain S.E S.hc r .g1)) →
      ∃ out : M.N × List (NamedObject V), M.tick S w (W j w) (M.domain S.E S.hc r .g1) ⇢ out) :
    ∃ Ln : NamedBlock V, Ln.erase = L ∧
      Ln ∈ (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st.bodies ∧
      Restated.RunBlockOn M S rho W Xb Ln := by
  obtain ⟨raw, hraw, hLraw⟩ := activeVoterAnchor_raw₅₉ facts S Hs Xb hf hr ready hw c hc hframe
    hactive hlo hneTick
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
  obtain ⟨Ln, hLn, hLnErase⟩ := exists_named_along₅₉ facts S hf.onePath k w hLtree
  exact ⟨Ln, hLnErase, hLn,
    Restated.runBlock_of_stateBefore_memOn facts S W Xb (hHsXb _ hw) hLn⟩

/-- Under the bundle along `W`, if `0 < r`, round `r` is ready (`GradeRoundReady`), `S.a r` is
    within the horizon, `p` is in the set for `domain r g0`, `w` is in the set for
    `domain r g0 + Δ`, `w`'s tick at `domain r g1` has an outcome, and `L` is the active prefix of
    the grade-1 frame root read with an outcome `c` of the phase tick on `w`'s next-vote store, then
    some named `Ln` with `Ln.erase = L` is a body of `p`'s store in the world of `W` strictly before
    `domain r g0`, a body of every node state of `p`'s round-`r` action read, and a run block read
    through `Xb` along `W`. -/
theorem activeVoterAnchor_namedBody_at_sourceG0_and_actionOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {r : Round} (hr : 0 < r)
    (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho r)
    (hactionHor : Restated.Vocabulary.Execution.Setup.a M S r ≤ rho.horizon)
    {p w : V} (hp : p ∈ Hs (M.domain S.E S.hc r .g0))
    (hw : w ∈ Hs (M.domain S.E S.hc r .g0 + S.E.Δ))
    {root L : Block V}
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
    (hlo : lo ≤ M.early S.E S.hc r .g2)
    (hneTick : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w (M.domain S.E S.hc r .g1)) →
      ∃ out : M.N × List (NamedObject V), M.tick S w (W j w) (M.domain S.E S.hc r .g1) ⇢ out) :
    ∃ Ln : NamedBlock V, Ln.erase = L ∧
      Ln ∈ (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) p).st.bodies ∧
      (∀ np ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) p) r,
        Ln ∈ np.st.bodies) ∧
      Restated.RunBlockOn M S rho W Xb Ln := by
  have hΔ := S.E.Δ_pos
  have hg1g0 : M.domain S.E S.hc r .g1 ≤ M.domain S.E S.hc r .g0 + S.E.Δ := by
    have h := facts.gr.domain_le_domain_g0 S r .g1
    linarith
  have hwG1 : w ∈ Hs (M.domain S.E S.hc r .g1) := hHs _ _ hg1g0 hw
  obtain ⟨Ln, hLnErase, hLnG1, hLnRun⟩ :=
    Restated.activeVoterAnchor_namedBody_at_g1DomainOn facts S Hs Xb hf hHsXb hr ready hwG1 c hc
      hframe hactive hlo hneTick
  have hLvote := facts.gr.activePrefix_mem _ _ _ hactive
  have htargetF : Block.Preceq
      (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) p).st.core.F Ln.erase := by
    rw [hLnErase]
    exact Restated.sourceG0Finalized_preceq_firstInteriorActiveOn facts S Hs Xb hf hHs hHsXb ready
      hactionHor hp hw hLvote hlo
  have hpost : lo ≤ M.domain S.E S.hc r .g1 :=
    hlo.trans ((facts.gr.early_le_domain S r).trans (facts.gr.domain_g2_le_domain_g1 S r))
  have hdeadline : max (M.domain S.E S.hc r .g1) lo + S.E.Δ ≤ M.domain S.E S.hc r .g0 := by
    rw [max_eq_left hpost]
    exact facts.gr.domain_g1_add_delta_le_domain_g0 S r
  have hwMax : w ∈ Hs (max (M.domain S.E S.hc r .g1) lo) := by
    rw [max_eq_left hpost]
    exact hwG1
  obtain ⟨hLnG0, -, -⟩ :=
    Restated.healthy_head_body_at_read_after_gst_admitOn facts
      S rho Hs Xb hf hHs hHsXb w p Ln
        (M.domain S.E S.hc r .g1) (M.domain S.E S.hc r .g0)
        (M.domain S.E S.hc r .g0) hwMax hp hLnG1 hdeadline (le_refl _)
        ready.2 htargetF
  have hdomainAction : M.domain S.E S.hc r .g0 ≤ Restated.Vocabulary.Execution.Setup.a M S r :=
    facts.gr.domain_le_a S r .g0
  refine ⟨Ln, hLnErase, hLnG0, ?_, hLnRun⟩
  intro np hnp
  rw [actionReadFrom_bodies₅₉ facts S _ r np hnp]
  exact bodies_mono_along₅₉ facts S hf.onePath p (strictEventIndex_mono rho hdomainAction) hLnG0

/-- Under the bundle along `W`, if round `r` is ready (`GradeRoundReady`), the named height-regime
    frame over `X` holds along `W` at `H` up to `stop`, round `r`'s action read is before `stop`,
    the largest `h_max` over `X` in `W stop` is less than `H + 2`, and `p` in the set for `S.a r`
    has a node state of its round-`r` action read whose Q2 and whose action FG source can return
    `some Q.erase`, with `Q` held there at height `H + 1`, then `Q.erase` is in the filtered tree of
    every member of the set for `domain r g1` in the world of `W` strictly before that instant, and
    in the filtered tree of the store, with its clock set, of every member of the set for
    `vote_time (opening_slot r)` in the world of `W` strictly before that instant. -/
theorem voterAnchorSourceQ2Inputs_of_namedHeightRegimeFrame_at_sourceOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb X : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hX : ∀ t : Int, 0 ≤ t → Hs t ⊆ X) (hXXb : X ⊆ Xb)
    {r : Round} (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho r)
    {stop : Nat} {H : Height} {Prev : NamedBlock V} {c0 : Round}
    (hframe : Restated.NamedHeightRegimeFrameOn M S rho W
      (fun t => W (strictEventIndex rho t)) Hs X Xb H stop Prev c0)
    (hactionPrefix : strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r) ≤ stop)
    (hfrontier : (X.sup fun u => (W stop u).st.core.h_max) < H + 2)
    (hactionHor : Restated.Vocabulary.Execution.Setup.a M S r ≤ rho.horizon)
    {p : V} (hpAct : p ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S r)) (Q : NamedBlock V)
    {n : M.N}
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) p) r)
    (hselected : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ some Q.erase)
    (hsource : Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ some Q.erase)
    (hQmem : Q ∈ n.st.bodies)
    (hQheight : (M.derive_named S.E S.cfg Q).h = H + 1)
    (hlo : lo ≤ M.early S.E S.hc r .g2) :
    (∀ w ∈ Hs (M.domain S.E S.hc r .g1),
        Q.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w)) ∧
      ∀ w ∈ Hs (M.vote_time S.E (M.opening_slot S.hc r)),
        Q.erase ∈ M.get_filtered_block_tree
          (M.toHealing (M.ns_setClock S.E
            (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc r))) w).st
            (M.vote_time S.E (M.opening_slot S.hc r))).core).toFG := by
  have hp : p ∈ Hs (M.domain S.E S.hc r .g2) := hHs _ _ (facts.gr.domain_le_a S r .g2) hpAct
  have hlopos : 0 < lo := hf.lo_pos
  have hpost : lo ≤ M.domain S.E S.hc r .g2 := hlo.trans (facts.gr.early_le_domain S r)
  have hg2g1 : M.domain S.E S.hc r .g2 ≤ M.domain S.E S.hc r .g1 :=
    facts.gr.domain_g2_le_domain_g1 S r
  have hPrevQ : NamedBlock.Preceq Prev Q :=
    hframe.sourceAbove p r hpAct hactionPrefix hactionHor n hn Q hQmem hsource hQheight
  have hPrevQErase : Block.Preceq Prev.erase Q.erase := Proofs.NamedWire.erase_preceq hPrevQ
  have hQrun : Restated.RunBlockOn M S rho W Xb Q :=
    Restated.actionBody_runBlock_k6On facts S Hs Xb hf (hHsXb _ hp) hn hQmem
  have hfloor : Restated.FinalityFloorAtOn M S rho W X Xb H stop Prev.erase := by
    intro v hv k hk Y hYrun hYheight hPrevY
    exact hframe.floor v hv k hk Y hYrun hYheight
      (Restated.namedPreceq_of_runBlock_erase_preceqOn facts Hs Xb hf hframe.prevRun hYrun hPrevY)
  have hQsource : Q ∈ (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) p).st.bodies :=
    Restated.selectedQ2_body_at_captureOn facts S Hs Xb hf (hHsXb _ hp) hn hselected hQmem
  refine ⟨?_, ?_⟩
  · intro w hw
    have hwX : w ∈ X := hX _ (by linarith) hw
    have hdomainPrefix : strictEventIndex rho (M.domain S.E S.hc r .g1) ≤ stop :=
      (strictEventIndex_mono rho (facts.gr.domain_le_a S r .g1)).trans hactionPrefix
    have htargetFQ : Block.Preceq
        (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st.core.F Q.erase :=
      hframe.floor w hwX _ hdomainPrefix Q hQrun (by rw [hQheight]; exact Nat.le_succ H) hPrevQ
    have hdeadline : max (M.domain S.E S.hc r .g2) lo + S.E.Δ ≤ M.domain S.E S.hc r .g1 := by
      rw [max_eq_left hpost]
      exact facts.gr.domain_g2_add_delta_le_domain_g1 S r
    have hpMax : p ∈ Hs (max (M.domain S.E S.hc r .g2) lo) := by
      rw [max_eq_left hpost]
      exact hp
    have hg1Hor : M.domain S.E S.hc r .g1 ≤ rho.horizon :=
      (facts.gr.domain_le_domain_g0 S r .g1).trans ready.2
    obtain ⟨hbody, -, -⟩ :=
      Restated.healthy_head_body_at_read_after_gst_admitOn facts
        S rho Hs Xb hf hHs hHsXb p w Q
          (M.domain S.E S.hc r .g2) (M.domain S.E S.hc r .g1)
          (M.domain S.E S.hc r .g1) hpMax hw hQsource hdeadline (le_refl _)
          hg1Hor htargetFQ
    exact (hframe.fgRoot_preceq_and_filteredMem facts Hs hf hXXb hfrontier hwX hdomainPrefix hbody
      hQheight hPrevQ).2
  · intro w hw
    have hg1Vote : M.domain S.E S.hc r .g1 ≤ M.vote_time S.E (M.opening_slot S.hc r) := by
      rw [facts.gr.Sts_domain_g1_eq_opening, facts.gr.opening_eq_proposal_time]
      exact (facts.sch.proposal_time_lt_vote_time S.E _).le
    have hwG1 : w ∈ Hs (M.domain S.E S.hc r .g1) := hHs _ _ hg1Vote hw
    have hwX : w ∈ X := hX _ (by linarith) hwG1
    have hbodies := Restated.selectedQ2_body_at_action_and_openingVote_of_floorOn facts
      S Hs Xb X hf hHs hHsXb ready hp hn hselected hQmem hfloor hQheight hPrevQErase
        hactionPrefix hwG1 hwX hlo
    have hvoteAction : M.vote_time S.E (M.opening_slot S.hc r) ≤
        Restated.Vocabulary.Execution.Setup.a M S r := by
      calc
        M.vote_time S.E (M.opening_slot S.hc r) ≤
            M.confirmation_time S.E (M.opening_slot S.hc r) :=
          facts.sch.Protocol_vote_time_le_confirmation_time S.E _
        _ = Restated.Vocabulary.Execution.Setup.a M S r :=
          Restated.Vocabulary.Proofs.HealingSurface.opening_confirmation_time_eq_action facts S r
    have hvotePrefix : strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc r)) ≤ stop :=
      (strictEventIndex_mono rho hvoteAction).trans hactionPrefix
    have hbody := hbodies.2
    rw [facts.hd.Sts_setClock_bodies] at hbody
    have hfiltered := (hframe.fgRoot_preceq_and_filteredMem facts Hs hf hXXb hfrontier hwX
      hvotePrefix hbody hQheight hPrevQ).2
    rw [facts.hd.setClock_core_eq_store_with_t_s]
    exact Eq.mpr (congrArg (fun T => Q.erase ∈ T)
      (facts.fc.get_filtered_block_tree_set_clock_slot _ _ _)) hfiltered

/-- Under the bundle along `W`, if `0 < c`, round `c` is ready (`GradeRoundReady`),
    `lo ≤ opening (c − η_SG)`, `v` in the set for `S.a c` has a node state of its round-`c` action
    read whose Q2 can return `some Q`, and `Q` is in the filtered tree of every member of the set
    for `domain c g1`, and of the vote-duty store of every member of the set for
    `vote_time (opening_slot c)`, in the worlds of `W` strictly before those instants, then every
    committee member of `c`'s opening slot in the set for its vote instant votes, along `W`, for a
    descendant of `Q`. -/
theorem selectedQ2_openingVotesConeOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {c : Round} (hc : 0 < c)
    (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho c)
    {v : V} (hv : v ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S c)) {Q : Block V}
    {n : M.N}
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v) c)
    (hQ : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n c ⇢ some Q)
    (hK6 : (∀ w ∈ Hs (M.domain S.E S.hc c .g1),
        Q ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc c .g1)) w)) ∧
      ∀ w ∈ Hs (M.vote_time S.E (M.opening_slot S.hc c)),
        Q ∈ M.get_filtered_block_tree
          (M.toHealing (M.ns_setClock S.E
            (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc c))) w).st
            (M.vote_time S.E (M.opening_slot S.hc c))).core).toFG)
    (hlo : lo ≤ M.opening S.E S.hc (c - S.hc.η_SG)) :
    Restated.NamedHonestVotesConeOn M S rho W Hs Xb (M.opening_slot S.hc c)
      (fun Y => Block.Preceq Q Y) := by
  have hopenPos : 0 < M.opening_slot S.hc c := facts.gr.opening_slot_pos S hc
  have hround : M.round_of S.hc (M.opening_slot S.hc c) = c :=
    facts.gr.round_of_opening_slot_eq S.hc c
  have hread : M.domain S.E S.hc c .g1 < M.vote_time S.E (M.opening_slot S.hc c) := by
    rw [facts.gr.Sts_domain_g1_eq_opening, facts.gr.opening_eq_proposal_time]
    exact facts.sch.proposal_time_lt_vote_time S.E _
  have hvoteAction : M.vote_time S.E (M.opening_slot S.hc c) ≤
      Restated.Vocabulary.Execution.Setup.a M S c := by
    calc
      M.vote_time S.E (M.opening_slot S.hc c) ≤
          M.confirmation_time S.E (M.opening_slot S.hc c) :=
        facts.sch.Protocol_vote_time_le_confirmation_time S.E _
      _ = Restated.Vocabulary.Execution.Setup.a M S c :=
        Restated.Vocabulary.Proofs.HealingSurface.opening_confirmation_time_eq_action facts S c
  have hvoteHorizon : M.vote_time S.E (M.opening_slot S.hc c) ≤ rho.horizon := by
    have hr2 := ready.2
    rw [facts.gr.domain_g0_eq_opening, facts.gr.opening_eq_proposal_time,
      ← facts.sch.Γ_0_eq_proposal_time S.hc S.E c, facts.sch.Γ_1_eq_vote_time S.hc S.E c] at hr2
    exact hr2
  have hgst : lo ≤ M.early S.E S.hc c .g2 := facts.gr.lo_le_early_g2_of_window_start S hc hlo
  have hg2g1 : M.domain S.E S.hc c .g2 ≤ M.domain S.E S.hc c .g1 :=
    facts.gr.domain_g2_le_domain_g1 S c
  have hgat : lo ≤ M.domain S.E S.hc c .g1 :=
    hgst.trans ((facts.gr.early_le_domain S c).trans hg2g1)
  have hvG2 : v ∈ Hs (M.domain S.E S.hc c .g2) :=
    hHs _ _ ((hg2g1.trans hread.le).trans hvoteAction) hv
  have hsource : M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
      c ⇢ some Q := by
    have hQ' := hQ
    unfold Restated.Vocabulary.Internal.PhaseGrades.nodeQ2
      Restated.Vocabulary.Internal.PhaseGrades.nodeRead at hQ'
    obtain ⟨G, hG, hGQ⟩ := returns_map_elim₅₉ _ _ _ hQ'
    obtain ⟨x, hx⟩ := facts.dt.grade2_block_with_nonempty (M.gradeContract n.cache) S.E S.hc
      (M.toHealing n.st.core) c
    have hxQ : x = some Q :=
      (facts.dt.grade2_block_with_eq_read_Q2 _ S.E S.hc _ c G hG x hx).trans hGQ
    rw [hxQ] at hx
    exact hx
  have hG2 := Restated.selectedQ2_storeGrade_at_g2DomainOn facts S Hs Xb hf n hn hQ
  have hG2true : Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
      (W (strictEventIndex rho (M.domain S.E S.hc c .g2)) v).st c .g2 Q ⇢ true := by
    obtain ⟨b, hb⟩ := facts.gr.gradeBool_nonempty S.E
      (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc c .g2)) v).st.core))
      (W (strictEventIndex rho (M.domain S.E S.hc c .g2)) v).st.core.F
      S.hc.η_SG c (M.early S.E S.hc c .g2) (M.late S.E S.hc c .g2) Q
    have hbt : b = true := hG2 b hb
    rw [hbt] at hb
    exact hb
  -- The opening voters pass the grade-1 awake test at their vote ticks.
  have hwin : lo ≤ M.early S.E S.hc (M.round_of S.hc (M.opening_slot S.hc c)) .g1 - S.E.Δ := by
    rw [hround]
    have h1 := facts.gr.early_g2_add_delta_le_early_g1 S c
    linarith
  refine Restated.honestVotesCone_of_selectedActionG2_of_readDispositionOn facts
    S Hs Xb hf hHs hHsXb hc ready hv n hn hsource hopenPos hround hread hvoteAction
      hvoteHorizon hgat ?_ ?_
      (fun w hw _ j hj => hf.awake_g1 _ _ j _ (Or.inr rfl) hj hw hwin)
  · intro w hw _
    have hwG1 : w ∈ Hs (M.domain S.E S.hc c .g1) := hHs _ _ hread.le hw
    have htarget := hK6.1 w hwG1
    have hFQ : Block.Preceq
        (W (strictEventIndex rho (M.domain S.E S.hc c .g1)) w).st.core.F Q :=
      F_preceq_of_mem_filtered₅₉ facts _ htarget
    have hfinalized :=
      Restated.crossReaderFinalizedBelow_of_finalitySafety_and_relayOn facts
        S Hs Xb hf hHs hHsXb hf.slashableBound hgst ready.2 hvG2 hwG1 (B := Q)
        (by
          intro sender u root Head I _ _ cb hcb hcbt hconf hfind
          refine preceq_trans_Preceq hFQ ?_
          obtain ⟨b', hb'⟩ := facts.gr.head_covers_nonempty
            (M.gradeView (M.toHealing
              (W (strictEventIndex rho (M.domain S.E S.hc c .g2)) v).st.core)).T Q u.confirmed
          have hb't : b' = true :=
            (facts.gr.localCovers_eq_true_iff _ _ _ cb hcb b' hb').mp hcbt
          rw [hconf] at hb'
          exact facts.gr.preceq_of_head_covers_of_find b' hb' hb't hfind)
    have hguard := Restated.crossReaderBodyReadyGuard_of_finalizedBelowOn facts
      S Hs Xb hf hHs hHsXb hc hgst ready.2 hvG2 hwG1 hfinalized
    have hG1 := Restated.storeGrade_g1_of_storeGrade_g2_cross_readerOn facts
      S rho Hs Xb hf hHs hHsXb c hlo ready.2 v w hvG2 hwG1 Q hG2true hguard
    have hG1true : Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
        (W (strictEventIndex rho (M.domain S.E S.hc c .g1)) w).st c .g1 Q ⇢ true := by
      obtain ⟨b, hb⟩ := facts.gr.gradeBool_nonempty S.E
        (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc c .g1)) w).st.core))
        (W (strictEventIndex rho (M.domain S.E S.hc c .g1)) w).st.core.F
        S.hc.η_SG c (M.early S.E S.hc c .g1) (M.late S.E S.hc c .g1) Q
      have hbt : b = true := hG1 b hb
      rw [hbt] at hb
      exact hb
    have hopen := hK6.2 w hw
    rw [facts.hd.setClock_core_eq_store_with_t_s] at hopen
    exact ⟨htarget, hG1true, Eq.mp (congrArg (fun T => Q ∈ T)
      (facts.fc.get_filtered_block_tree_set_clock_slot _ _ _)) hopen⟩
  · intro w hw _
    exact Or.inr (hK6.2 w hw)

end

/-! ## The next-vote cone or height progress -/

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

/-- If `st` has `GenuineConfirmation` of `C` at slot `s` and `T` is an ancestor of `C`, then some
    outcome `votes` of the confirmation votes of `st` at `s` is such that every outcome of `T`'s
    Goldfish score over `votes` is more than half the late voter count. -/
private theorem ancestor_eligible₅₉ (facts : Record.Facts M) {contract : M.Contract} {E : Env V}
    {hc : Protocol.HealConfig} {st : M.S} {s : Slot} {T C : Block V}
    (hTC : Block.Preceq T C)
    (hC : Restated.Vocabulary.Protocol.GenuineConfirmation M (contract := contract) E hc st s C) :
    ∃ votes : Finset (GoldfishVote V), Restated.Vocabulary.Protocol.confVotes M E st s ⇢ votes ∧
      ∀ g : ℕ, M.goldfish_score E st.T votes votes s T ⇢ g →
        M.voters_count E (Restated.Vocabulary.Protocol.confLate M E st s) s < 2 * g := by
  obtain ⟨early, sc, hearly, hvotes, hsc, hlt⟩ := genuine_eligible₅₉ facts hC
  generalize hvv : early.filter
    (fun x => M.no_second_vote_in (Restated.Vocabulary.Protocol.confLate M E st s) x = true) = votes
    at hvotes hsc
  refine ⟨votes, hvotes, fun g hg => ?_⟩
  have hN := facts.fc.Numerator_score_eq_supporters early
    (Restated.Vocabulary.Protocol.confLate M E st s) votes
    (confEarly_subset_late₅₉ facts E st s early hearly) hvv.symm E st.T s
  obtain ⟨RT, hRT⟩ := facts.fc.raw_supporters_nonempty st.T votes votes s T
  obtain ⟨RC, hRC⟩ := facts.fc.raw_supporters_nonempty st.T votes votes s C
  have hgT := hN T g hg RT hRT
  have hgC := hN C (sc C) (hsc C) RC hRC
  have hsubs : RC ⊆ RT := Restated.Vocabulary.Protocol.supporters_mono facts E st.T votes votes s
    (C := T) (B := C) (preceq_eq_true_iff_Preceq.mpr hTC) RC hRC RT hRT
  rw [hgT]
  rw [hgC] at hlt
  exact lt_of_lt_of_le hlt (Nat.mul_le_mul_left 2 (Finset.card_le_card hsubs))

/-- Under the bundle along `W`, if `p`, in the set for `S.a r`, has `GenuineConfirmation` of `C` on
    its confirmation store read from `W` at the opening slot, `B ⪯ C` is a body of a node state of
    `p`'s round-`r` action read at height `H + 1`, every member of the set for
    `vote_time (opening_slot r + 1)` has `B` in the filtered tree of its vote-duty store along `W`,
    and every anchor its vote-duty read can give is compatible with `B`, then either some member of
    that set has `h_max ≥ H + 3` along `W` at an instant up to `through`, or every head of every
    member's vote-duty read is `B` or a descendant of `B`, and every member of that set on the
    committee of slot `opening_slot r + 1` emits along `W` a vote for a run block that is `B` or a
    descendant of `B`. -/
theorem genuineClear_nextVoteCone_or_heightProgressThrough_of_mainInputsOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {r : Round} (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho r)
    {p : V} (hp : p ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S r)) {B : NamedBlock V} {C : Block V}
    {contract : M.Contract}
    (hgenuine : Restated.Vocabulary.Protocol.GenuineConfirmationWith M contract S.E S.hc
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc r))) p).st.core
        (M.confirmation_time S.E (M.opening_slot S.hc r)))
      (M.opening_slot S.hc r) C)
    (hBC : Block.Preceq B.erase C)
    {n : M.N}
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) p) r)
    (hBmem : B ∈ n.st.bodies)
    {H : Height}
    (hBheight : (M.derive_named S.E S.cfg B).h = H + 1)
    (hactionHor : Restated.Vocabulary.Execution.Setup.a M S r ≤ rho.horizon)
    (hmainTarget : ∀ w ∈ Hs (M.vote_time S.E (M.opening_slot S.hc r + 1)),
      B.erase ∈ M.get_filtered_block_tree (M.toHealing (M.ns_setClock S.E
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc r + 1))) w).st
        (M.vote_time S.E (M.opening_slot S.hc r + 1))).core).toFG)
    (hmainAnchor : ∀ w ∈ Hs (M.vote_time S.E (M.opening_slot S.hc r + 1)), ∀ c : M.Cache,
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
        Block.compatible L B.erase = true)
    {through : Time}
    (hvoteThrough : M.vote_time S.E (M.opening_slot S.hc r + 1) ≤ through)
    (hlo : lo ≤ M.early S.E S.hc r .g2) :
    (∃ v ∈ Hs (M.vote_time S.E (M.opening_slot S.hc r + 1)), ∃ u ≤ through,
      H + 1 + 2 ≤ (W (inclusiveEventIndex rho u) v).st.h_max) ∨
    ((∀ w ∈ Hs (M.vote_time S.E (M.opening_slot S.hc r + 1)), ∀ c : M.Cache,
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc r + 1))) w).st.core.toHealing
        (M.vote_time S.E (M.opening_slot S.hc r + 1))
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc r + 1))) w).cache ⇢ c →
      let n := M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc r + 1))) w).st
          (M.vote_time S.E (M.opening_slot S.hc r + 1)))
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc r + 1))) w).record c
      ∀ Tr : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ Tr →
      ∀ L : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
      ∀ L' : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
      ∀ H : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
          (M.toHealing n.st.core) Tr L L' (n.st.core.s - 1) ⇢ H →
        Block.Preceq B.erase H) ∧
      Restated.NamedHonestVotesConeOn M S rho W Hs Xb (M.opening_slot S.hc r + 1)
        (fun Y => Block.Preceq B.erase Y)) := by
  have hca := Restated.Vocabulary.Proofs.HealingSurface.opening_confirmation_time_eq_action facts S r
  have hpost : lo ≤ M.proposal_time S.E (M.opening_slot S.hc r) := by
    have h1 := facts.gr.early_g2_le_opening S r
    rw [facts.gr.opening_eq_proposal_time] at h1
    exact hlo.trans h1
  -- The voters of slot `opening_slot r + 1` pass the grade-1 awake test at their vote ticks.
  have hwinNext : lo ≤ M.early S.E S.hc (M.round_of S.hc (M.opening_slot S.hc r + 1)) .g1 - S.E.Δ := by
    rw [facts.gr.HealingLemmas_round_of_opening_succ S.hc r]
    have h1 := facts.gr.early_g2_add_delta_le_early_g1 S r
    linarith
  have hsourceHor : M.confirmation_time S.E (M.opening_slot S.hc r) ≤ rho.horizon := by
    rw [hca]
    exact hactionHor
  have hvoteHor : M.vote_time S.E (M.opening_slot S.hc r + 1) ≤ rho.horizon :=
    (Restated.Vocabulary.Protocol.next_vote_time_lt_action facts S r).le.trans hactionHor
  have hpConf : p ∈ Hs (M.confirmation_time S.E (M.opening_slot S.hc r)) := by
    rw [hca]
    exact hp
  have hpSupport : p ∈ Hs (M.support_cutoff S.E (M.opening_slot S.hc r)) :=
    hHs _ _ (facts.sch.Protocol_support_cutoff_le_confirmation_time S.E _) hpConf
  have hloVote : lo ≤ M.vote_time S.E (M.opening_slot S.hc r + 1) := by
    have h2 := facts.sch.proposal_time_lt_vote_time S.E (M.opening_slot S.hc r)
    have h3 := Restated.vote_time_lt_support_cutoff_l49 facts S (M.opening_slot S.hc r)
    have h4 := facts.sch.Optimistic_support_cutoff_lt_view_freeze S.E (M.opening_slot S.hc r)
    have h5 := facts.sch.view_freeze_lt_vote_time_succ S.E (M.opening_slot S.hc r)
    linarith
  have hg : Restated.Vocabulary.Protocol.GenuineConfirmation M (contract := contract) S.E S.hc
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc r))) p).st.core
        (M.confirmation_time S.E (M.opening_slot S.hc r))) (M.opening_slot S.hc r) C :=
    ⟨hgenuine.selected, hgenuine.genuine⟩
  by_cases hprogress : ∃ v ∈ Hs (M.vote_time S.E (M.opening_slot S.hc r + 1)), ∃ u ≤ through,
      H + 1 + 2 ≤ (W (inclusiveEventIndex rho u) v).st.h_max
  · exact Or.inl hprogress
  · right
    have hand : ∀ {a b : Prop}, a → (a → b) → a ∧ b := fun ha hb => ⟨ha, hb ha⟩
    refine hand ?_ ?_
    · intro w hw c hc n Tr hTr L hL L' hL' Hd hHd
      have hst : n.st = M.store_with_cache (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc r + 1))) w).st (M.vote_time S.E (M.opening_slot S.hc r + 1))) _ := facts.nd.mkNode_st _ _ _
      have hmemn : n ∈ Restated.Vocabulary.Internal.NamedRecoveryRead.voteDutyRead M S rho w
          (M.opening_slot S.hc r + 1) :=
        ⟨W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc r + 1))),
          mem_stateBeforeTime_along₅₉ hf.sorted hf.onePath _, c, hc, rfl⟩
      have hfilt := hmainTarget w hw
      have hbody := Restated.actionBody_at_voteDuty_of_filteredOn facts S Hs Xb hf (hHsXb _ hp) hn
        hBmem (hHsXb _ hw) hfilt
      by_cases hex : ∃ R : Block V, M.get_sg_root_with (M.gradeContract n.cache) S.E S.hc
          (M.toHealing n.st.core) (M.round_of S.hc n.st.core.s) ⇢ R ∧ ¬ Block.Preceq R B.erase
      · obtain ⟨R, hR, hnot⟩ := hex
        obtain ⟨G, hG⟩ := facts.gr.read_nonempty (M.gradeContract n.cache) S.E S.hc
          (M.toHealing n.st.core) (M.round_of S.hc n.st.core.s)
        have hRG : R = G.anchor :=
          facts.fc.get_sg_root_with_eq_read_anchor _ S.E S.hc _ _ G hG R hR
        have hRA : Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n
            (M.round_of S.hc n.st.core.s) ⇢ R := by
          rw [hRG]
          exact returns_map_intro₅₉ (fun g : GradeRead V => g.anchor) _ G hG
        have hcompat := hmainAnchor w hw c hc R hRA
        rcases compatible_cases hcompat with hRB | hBR
        · exact absurd hRB hnot
        · exact preceq_trans_Preceq hBR
            (Restated.Vocabulary.Proofs.HealingSurface.voterAnchorAt_preceq_voterHeadAt facts S rho w
              (M.opening_slot S.hc r + 1) n hmemn R hRA Tr hTr L hL L' hL' Hd hHd)
      · have hall : ∀ R : Block V, M.get_sg_root_with (M.gradeContract n.cache) S.E S.hc
            (M.toHealing n.st.core) (M.round_of S.hc n.st.core.s) ⇢ R → Block.Preceq R B.erase :=
          fun R hR => Classical.byContradiction fun h => hex ⟨R, hR, h⟩
        obtain ⟨P, hP⟩ := facts.fc.voter_processed_block_tree_nonempty S.E
          (M.toHealing n.st.core).toFG.toSG.toGoldfishStore (M.toHealing n.st.core).s
        have hK : Restated.Vocabulary.Proofs.Optimistic.voter_candidate_tree M S.E
            (M.toHealing n.st.core) ⇢
              M.get_filtered_block_tree_from (M.toHealing n.st.core).toFG P :=
          (returns_bind_iff₅₉ _ _ _).mpr ⟨P, hP, (Record.returns_pure _ _).2 rfl⟩
        have hcand : B.erase ∈ M.get_filtered_block_tree_from (M.toHealing n.st.core).toFG P := by
          refine Restated.ancestorGenuineConfirmation_candidate_at_nextVoteOn facts S Hs Xb hf
            hHs hHsXb ready hactionHor hpSupport hgenuine hBC hBheight hprogress hvoteThrough hw
            hbody hfilt hlo _ ?_
          have hP' := hP
          rw [hst] at hP'
          rw [hst]
          exact candidate_tree_store_with_cache₅₉ facts S.E _ _ P hP'
        have hadopt := Restated.nextVoteAdoption_of_frozenCandidateAtReadOn facts S Hs Xb hf
          hHs hHsXb hpConf hpost hsourceHor hw c hc hK hcand hall
          (fun j hj => hf.awake_g1 _ _ j _ (Or.inr rfl) hj hw hwinNext)
        obtain ⟨votes, hvotes, helig⟩ := ancestor_eligible₅₉ facts hBC hg
        exact Restated.preceq_voterHeadAt_of_namedNextVoteAdoptionOn facts S Xb n hmemn hvotes
          helig hadopt Tr hTr L hL L' hL' Hd hHd
    · intro hheads
      unfold Restated.NamedHonestVotesConeOn
      intro x hx hcomm
      obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc r + 1))) x).st.core.toHealing
        (M.vote_time S.E (M.opening_slot S.hc r + 1))
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc r + 1))) x).cache
      have hem := Restated.named_voter_head_emitsOn facts S Hs Xb hf hHsXb hx
        (Nat.succ_pos (M.opening_slot S.hc r)) hcomm hvoteHor hloVote c hc
        (fun j hj => hf.awake_g1 _ _ j _ (Or.inr rfl) hj hx hwinNext)
      have hhd := hheads x hx c hc
      let n : M.N := M.mkNode
        (M.ns_setClock S.E
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc r + 1))) x).st
          (M.vote_time S.E (M.opening_slot S.hc r + 1)))
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc r + 1))) x).record c
      obtain ⟨T, hT⟩ := facts.fc.voter_filtered_block_tree_nonempty S.E n.st.core n.st.core.s
      obtain ⟨L, hL⟩ := facts.fc.voter_view_nonempty S.E
        (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s
      obtain ⟨L', hL'⟩ := facts.fc.voter_support_view_nonempty S.E
        (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s
      obtain ⟨Hd, hHd⟩ := facts.fc.get_head_in_tree_with_layer_nonempty (M.gradeContract n.cache)
        S.E S.hc (M.toHealing n.st.core) T L L' (n.st.core.s - 1)
      obtain ⟨Y, hYhead, hYrun, hYemit⟩ := hem T hT L hL L' hL' Hd hHd
      exact ⟨Y, by rw [hYhead]; exact hhd T hT L hL L' hL' Hd hHd, hYrun, hYemit⟩

end

end DecoupledConsensusModel.Sts.Restated
