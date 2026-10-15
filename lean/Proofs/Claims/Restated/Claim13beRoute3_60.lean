import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13beRoute3_25
import Proofs.Claims.Restated.Claim13beRoute3_45
import Proofs.Claims.Restated.Claim13beRoute3_46
import Proofs.Claims.Restated.Claim13beRoute3_47
import Proofs.Claims.Restated.Claim13beRoute3_48
import Proofs.Claims.Restated.Claim13beRoute3_48b
import Proofs.Claims.Restated.Claim13beRoute3_49
import Proofs.Claims.Restated.Claim13beRoute3_51b
import Proofs.Claims.Restated.Claim13beRoute3_53b
import Proofs.Claims.Restated.Claim13beRoute3_55
import Proofs.Claims.Restated.Claim13beRoute3_56b
import Proofs.Claims.Restated.Claim13beRoute3_57
import Proofs.Claims.Restated.Claim13beRoute3_58
import Proofs.Claims.Restated.Claim13beRoute3_59
import Proofs.Claims.Restated.Vocabulary_Execution_PreparedReadBridge
import Proofs.Claims.Restated.Vocabulary_Execution_RecoveryActionLiveSourceSplit
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_ActionSourceCore
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_Adoption
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_Agreement
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_Confirmation
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_RecoveryProposalConfirmationRead
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_SGTargetCanonicality
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_GradeFormsProducers
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_Interpolation
import Proofs.Vocabulary.Protocol.Grades.PostOutage
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_RecoveryGenuineClearNextVote
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_RelativeOneChain
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_FinalityMonotoneCore
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_TickBridges
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_PostHealingReuse
import Proofs.Claims.Restated.Vocabulary_Protocol_ValidatorClient_RecoveryTimeout
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.RunVocabulary
import Model.Conditions.Vocabulary_Internal_Definitions_NamedLifecycle
import Model.Conditions.Vocabulary_Internal_Definitions_NamedOutageEntry
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGradeQueries
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Internal_HealingSurface
import Model.Conditions.Vocabulary_Internal_Internal_GradeReads
import Model.Conditions.Vocabulary_Internal_Invariants
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedHeadReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedActionReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_ModelVocabulary_Goldfish_ForkChoice
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Vocabulary.Protocol.Grades
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Adoption
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Agreement
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Confirmation
import Model.Conditions.Vocabulary_Protocol_Grades_GoldfishConePersistence
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Conditions.Vocabulary_Protocol_Grades_ProposalLifecycleCore
import Model.Conditions.Vocabulary_Protocol_Grades_RelativeCrossReader
import Model.Conditions.Vocabulary_Protocol_Handlers_Blocks
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_Handlers_TickBridges
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring

/-!
# Selected Q2 blocks, voter anchors and FG sources under a fixed root

Theorems over a model `M : Record.Model V` and its facts `facts : Record.Facts M`, read along the
path `W` that the bundle `AdmissibleFieldsOn` binds: a selected Q2 is held as a run block, keeps its
grades at the readers of its round and is an ancestor of the voter heads of its round; a voter
anchor is compatible with a clear action block of the same round under a fixed FG root `J` and a
one-step height cap; and two action FG sources of one round are compatible.
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
open scoped DC
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- In a run sorted by key, the worlds strictly before the instant `t` are the worlds before the
    event whose index is `strictEventIndex rho t`. -/
private theorem stateBeforeTime_eq_strict₆₀ (S : Setup V) (rho : Record.Run V)
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
private theorem mem_stateBeforeTime_along₆₀ {S : Setup V} {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (t : Time) :
    W (strictEventIndex rho t) ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t := by
  rw [stateBeforeTime_eq_strict₆₀ S rho hsorted]
  exact (hW _).1

/-- For every path `W` of `rho`, `W (m + k)` is among the worlds the events `m` to `m + k - 1` of
    `rho` lead to from `W m`. -/
private theorem onePath_reach₆₀ {S : Setup V} {rho : Record.Run V}
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
private theorem onePath_slice₆₀ {S : Setup V} {rho : Record.Run V}
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) {m n : Nat}
    (hmn : m ≤ n) :
    W n ∈ ((rho.events.drop m).take (n - m)).foldlM (Record.worldStepOf M S) (W m) := by
  have h := onePath_reach₆₀ W hW m (n - m)
  rwa [Nat.add_sub_of_le hmn] at h

/-- Along a path `W` of a run, for `j ≤ n`, the finalized block of `v`'s core store in `W j` is an
    ancestor of the finalized block of `v`'s core store in `W n`. -/
private theorem F_mono_along₆₀ (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (v : V)
    {j n : Nat} (hjn : j ≤ n) : Block.Preceq (W j v).st.core.F (W n v).st.core.F :=
  Restated.Vocabulary.Protocol.stateBefore_F_mono facts S rho v hjn (W j) (hW j).1 (W n)
    (onePath_slice₆₀ W hW hjn)

/-- If `f <$> m` can return `b`, then `m` can return some `a` with `f a = b`. -/
private theorem returns_map_elim₆₀ {α β : Type} (f : α → β) (m : DC.NDRE α) (b : β)
    (h : (f <$> m) ⇢ b) : ∃ a, m ⇢ a ∧ f a = b := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image] at h
  obtain ⟨e, he, hb⟩ := h
  cases e with
  | ok a => exact ⟨a, he, by simpa [Except.map] using hb⟩
  | error err => simp [Except.map] at hb

/-- If `m` can return `a`, then `f <$> m` can return `f a`. -/
private theorem returns_map_intro₆₀ {α β : Type} (f : α → β) (m : DC.NDRE α) (a : α)
    (h : m ⇢ a) : (f <$> m) ⇢ f a := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image]
  exact ⟨_, h, rfl⟩

/-- Every node state the round-`r` action read computed from `before` can give has as its core store
    an outcome of the confirmation update of `before`'s store staged at round `r`'s action instant. -/
private theorem actionReadFrom_core₆₀ (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      ∃ st : M.NS, n.st = M.store_with_cache st n.cache ∧
      M.update_confirmation_with (M.gradeContract n.cache) S.E S.hc
        (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r)).core
        (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1) ⇢ st.core := by
  rintro _ ⟨c, -, st, hst, rfl⟩
  obtain ⟨X, hX⟩ := facts.dt.update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc
    (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r)).core
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
  refine ⟨st, by rw [facts.nd.mkNode_st, facts.nd.mkNode_cache], ?_⟩
  rw [facts.nd.mkNode_cache, facts.dt.named_update_confirmation_with_core _ _ _ _ _ st hst X hX]
  exact hX

/-- Every node state the round-`r` action read computed from `before` can give has the `h_max` of
    `before`'s core store. -/
private theorem actionReadFrom_h_max₆₀ (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      n.st.core.h_max = before.st.core.h_max := by
  intro n hn
  obtain ⟨st₀, hst₀, hX₀⟩ := actionReadFrom_core₆₀ facts S before r n hn
  rw [hst₀, facts.nd.store_with_cache_core_h_max,
    ← facts.sto.Sts_toHealing_h_max,
    facts.dt.update_confirmation_with_toHealing_h_max _ _ _ _ _ _
      hX₀,
    facts.hd.setClock_toHealing_h_max]

/-- The filtered block tree of a named store with its clock set to `t` is the filtered block tree of
    the named store. -/
private theorem setClock_filtered₆₀ (facts : Record.Facts M) (S : Setup V) (st : M.NS) (t : Time) :
    M.get_filtered_block_tree (M.toHealing (M.ns_setClock S.E st t).core).toFG =
      M.get_filtered_block_tree (M.toHealing st.core).toFG := by
  rw [facts.hd.setClock_core_eq_store_with_t_s]
  exact facts.fc.get_filtered_block_tree_set_clock_slot _ _ _

/-- The FG root of a named store with its clock set to `t` is the FG root of the named store. -/
private theorem setClock_fgRoot₆₀ (facts : Record.Facts M) (S : Setup V) (st : M.NS) (t : Time) :
    M.get_fg_root (M.toHealing (M.ns_setClock S.E st t).core).toFG =
      M.get_fg_root (M.toHealing st.core).toFG := by
  rw [facts.hd.setClock_core_eq_store_with_t_s]
  exact facts.fc.get_fg_root_set_clock_slot _ _ _

/-- If every outcome of a store grade is `true`, the store grade can return `true`. -/
private theorem storeGrade_true_of_all₆₀ (facts : Record.Facts M) (E : Env V)
    (hc : DecoupledConsensusModel.Protocol.HealConfig) (st : M.NS) (r : Round)
    (p : DecoupledConsensusModel.Protocol.Phase) (B : Block V)
    (h : ∀ b, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M E hc st r p B ⇢ b → b = true) :
    Restated.Vocabulary.Internal.PhaseGrades.storeGrade M E hc st r p B ⇢ true := by
  obtain ⟨b, hb⟩ := facts.gr.gradeBool_nonempty E (M.gradeView (M.toHealing st.core)) st.core.F
    hc.η_SG r (M.early E hc r p) (M.late E hc r p) B
  have hbt : b = true := h b hb
  subst hbt
  exact hb

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
local macro "sgf% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SGTargetCanonicalityFixedRoot)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Under the bundle along `W`, if `A` and `B` are run blocks read through `Xb` along `W` with the
    same erasure, then `A = B`. -/
theorem fixedRoot_runBlock_unique_of_erase_eqOn (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {Xb : Finset V} {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {A B : NamedBlock V} (hA : Restated.RunBlockOn M S rho W Xb A)
    (hB : Restated.RunBlockOn M S rho W Xb B)
    (herase : A.erase = B.erase) : A = B :=
  hf.rootCollisionFree.root_injective A B hA hB A B
    (Or.inl (Proofs.NamedAncestry.named_self A)) (Or.inr (Proofs.NamedAncestry.named_self B))
    (by rw [← Proofs.NamedWire.erase_root A, ← Proofs.NamedWire.erase_root B, herase])

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
local macro "sgf% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SGTargetCanonicalityFixedRoot)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Under the bundle along `W`, if `w ∈ Xb` and `B` is a named body of `w`'s store in
    `W (strictEventIndex rho read)`, then `B` is a run block read through `Xb` along `W`. -/
theorem fixedRoot_runBlock_of_body_at_readOn_SGTargetCanonicalityFixedRoot (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {w : V} (hw : w ∈ Xb) {read : Time} {B : NamedBlock V}
    (hB : B ∈ (W (strictEventIndex rho read) w).st.bodies) :
    Restated.RunBlockOn M S rho W Xb B :=
  Restated.runBlock_of_stateBefore_memOn facts S W Xb hw hB

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
local macro "sgf% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SGTargetCanonicalityFixedRoot)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Under the bundle along `W`, if `p ∈ Xb`, `n` is a node state of `p`'s round-`r` action read from
    its node state in `W` before `S.a r`, and the Q2 of `n` can return `some Q`, then some named run
    block read through `Xb` along `W`, with erasure `Q`, is a body of `p`'s store in `W` before
    `domain r .g2`. -/
theorem fixedRoot_selectedQ2_body_at_captureOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {r : Round} {p : V} (hp : p ∈ Xb) {Q : Block V}
    (n : M.N)
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) p) r)
    (hselected : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ some Q) :
    ∃ Qn : NamedBlock V,
      Qn ∈ (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) p).st.bodies ∧
      Qn.erase = Q ∧ Restated.RunBlockOn M S rho W Xb Qn := by
  obtain ⟨cc, hcc, st', hst', rfl⟩ := hn
  unfold Restated.Vocabulary.Internal.PhaseGrades.nodeQ2
    Restated.Vocabulary.Internal.PhaseGrades.nodeRead at hselected
  obtain ⟨G, hG, hGQ⟩ := returns_map_elim₆₀ _ _ _ hselected
  obtain ⟨x, hx⟩ := facts.dt.grade2_block_with_nonempty
    (M.gradeContract (M.mkNode st' (W (strictEventIndex rho
      (Restated.Vocabulary.Execution.Setup.a M S r)) p).record cc).cache) S.E S.hc
    (M.toHealing (M.mkNode st' (W (strictEventIndex rho
      (Restated.Vocabulary.Execution.Setup.a M S r)) p).record cc).st.core) r
  have hxQ : x = some Q :=
    (facts.dt.grade2_block_with_eq_read_Q2 _ S.E S.hc _ r G hG x hx).trans hGQ
  rw [hxQ] at hx
  obtain ⟨j, raw, -, hj, hfreeze, hQraw⟩ :=
    facts.grRun.q2_capture_at_action_read_along S rho W hf.onePath
      (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) p r Q cc hcc st' hst' hx
  obtain ⟨fr, hfr⟩ := facts.gr.freezeRoot_nonempty S.E (M.gradeView (M.toHealing (W j p).st.core))
    (W j p).st.core.F S.hc.η_SG r (M.early S.E S.hc r .g2) (M.late S.E S.hc r .g2)
  have hrawTree : raw ∈ (W j p).st.core.T := by
    rw [← facts.gr.Sts_gradeView_T]
    exact facts.gr.mem_T_of_freezeRoot_eq_some fr hfr (hfreeze fr hfr)
  have hQTree : Q ∈ (W j p).st.core.T := by
    have hpc := Restated.Vocabulary.Proofs.NamedStoreBridge.parentClosed_stateBefore facts S rho j p
      (W j) (hf.onePath j).1
    unfold Restated.Vocabulary.Internal.ParentClosed Record.Model.GS.parent_closed at hpc
    have hQ := Proofs.Records.mem_of_preceq hpc.2 Q raw
      (by rw [facts.sto.toHealing_T]; exact hrawTree)
      (Proofs.ModelProperties.preceq_eq_true_iff_Preceq.2 hQraw)
    rw [facts.sto.toHealing_T] at hQ
    exact hQ
  obtain ⟨D, hD, hDerase⟩ :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore facts S rho j p
      (W j) (hf.onePath j).1 hQTree
  have hjState := Restated.stateBefore_tick_eq_stateBeforeTimeOn facts S Hs Xb hf hj
  refine ⟨D, ?_, hDerase, Restated.runBlock_of_stateBefore_memOn facts S W Xb hp hD⟩
  rcases hjState with hjState | hjState
  · rw [← hjState]
    exact hD
  · rw [hjState, (facts.nd.wake_st_record _).1] at hD
    exact hD

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
local macro "sgf% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SGTargetCanonicalityFixedRoot)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Under the bundle along `W`, if `0 < r`, `w` is in the set for `domain r g1` with
    `lo ≤ domain r g1`, the Q2 of a node state of `p`'s round-`r` action read along `W` can return
    `some Q`, `Q` is in the tree of `w`'s store in `W` before `domain r g1`, where its grade-1 store
    grade can return `true`, and `Q` is in the filtered tree of `w`'s node state in `W` before the
    vote instant of a slot `s` of round `r` after `domain r g1` and not after `opening (r + 1)`,
    then for every outcome of the cache update there, `Q` is an ancestor of every head of the
    vote-duty read staged with it. -/
theorem fixedRoot_selectedQ2_preceq_voterHead_of_rawDomainOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {r : Round} (hr : 0 < r) {p w : V}
    (hw : w ∈ Hs (M.domain S.E S.hc r .g1)) {Q : Block V}
    (np : M.N)
    (hnp : np ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) p) r)
    (hQ : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S np r ⇢ some Q)
    {s : Slot} (hround : (M.round_of S.hc s) = r)
    (hread : M.domain S.E S.hc r .g1 <
      M.vote_time S.E s)
    (hnext : M.vote_time S.E s ≤
      M.opening S.E S.hc (r + 1))
    (hhor : M.domain S.E S.hc r .g1 ≤ rho.horizon)
    (hQdomain : Q ∈ (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st.core.T)
    (hgrade : Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
      (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st r .g1 Q ⇢ true)
    (hQread : Q ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
      (W (strictEventIndex rho (M.vote_time S.E s)) w))
    (hgat : lo ≤ M.domain S.E S.hc r .g1) :
    ∀ cc, M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E s)) w).st.core.toHealing (M.vote_time S.E s)
        (W (strictEventIndex rho (M.vote_time S.E s)) w).cache ⇢ cc →
      let n := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) w).st
        (M.vote_time S.E s)) (W (strictEventIndex rho (M.vote_time S.E s)) w).record cc
      ∀ T, M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T →
      ∀ L, M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
      ∀ L', M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore
          n.st.core.s ⇢ L' →
      ∀ H, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          T L L' (n.st.core.s - 1) ⇢ H →
      Block.Preceq Q H := by
  intro cc hcc n T hT L hL L' hL' H hH
  have hround' : (M.round_of S.hc)
      (S.E.slotOf (M.vote_time S.E s)) = r := by
    rw [facts.sch.slotOf_vote_time]
    exact hround
  set wv := W (strictEventIndex rho (M.vote_time S.E s)) w with hwv
  set w1 := W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w with hw1
  obtain ⟨fr, hfr⟩ := facts.gr.freezeRoot_nonempty S.E (M.gradeView (M.toHealing w1.st.core))
    w1.st.core.F S.hc.η_SG r (M.early S.E S.hc r .g1) (M.late S.E S.hc r .g1)
  have hbase := Restated.frame_phase_completed_in_roundOn facts
    S rho Hs Xb hf w r hr .g1 hw (M.vote_time S.E s)
    hread hnext hhor hgat (fun j hj => hf.tick_outcome j _ _ hj) fr hfr
  have hprepared := Restated.Vocabulary.Proofs.NamedOutageClosure.frame_phase_prepared_eq facts
    S rho w r .g1 (M.vote_time S.E s) hround' _ (W (strictEventIndex rho (M.vote_time S.E s)))
    (mem_stateBeforeTime_along₆₀ hf.sorted hf.onePath _) hbase cc hcc
  have hQT : Q ∈ (M.gradeView (M.toHealing w1.st.core)).T := by
    rw [facts.gr.Sts_gradeView_T]
    exact hQdomain
  obtain ⟨raw, hraw, hQraw⟩ := facts.gr.q10_freeze_of_graded S.E
    (M.gradeView (M.toHealing w1.st.core)) w1.st.core.F
    S.hc.η_SG r (facts.gr.q10_early_le_late S r .g1) hQT true hgrade rfl fr hfr
  have hframe : (M.readFrame cc (M.toHealing (M.ns_setClock S.E wv.st
      (M.vote_time S.E s)).core) r).g1 = some (some (M.clipGrade raw wv.st.core.F)) := by
    rw [← facts.gr.phaseResult_g1, hprepared, hraw]
    rfl
  have hQactive : Q ∈ M.get_filtered_block_tree (M.toHealing
      (M.ns_setClock S.E wv.st (M.vote_time S.E s)).core).toFG := by
    rw [setClock_filtered₆₀ facts S]
    exact hQread
  have hFQ : Block.Preceq wv.st.core.F Q := by
    have h := facts.fc.q10_filtered_F hQactive
    rw [facts.sto.Sts_toHealing_F, facts.hd.setClock_core_F] at h
    exact h
  have hQroot : Block.Preceq Q (M.clipGrade raw wv.st.core.F) :=
    (facts.gr.q10_retained_prefix raw wv.st.core.F Q
      (compatible_of_cases (Or.inr hFQ))).mpr hQraw
  have hroundRead : M.round_of S.hc n.st.core.s = r := by
    show M.round_of S.hc
      (M.mkNode (M.ns_setClock S.E wv.st (M.vote_time S.E s)) wv.record cc).st.core.s = r
    rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.hd.Sts_setClock_core_s]
    exact hround'
  obtain ⟨G, hG⟩ := facts.gr.read_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc n.st.core.s)
  have hA : Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n
      (M.round_of S.hc n.st.core.s) ⇢ G.anchor := by
    unfold Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor
      Restated.Vocabulary.Internal.PhaseGrades.nodeRead
    exact returns_map_intro₆₀ (fun g : DecoupledConsensusModel.Protocol.GradeRead V => g.anchor)
      _ G hG
  have hQA : Block.Preceq Q G.anchor := by
    have hG' := hG
    rw [hroundRead] at hG'
    change (M.gradeContract (M.mkNode (M.ns_setClock S.E wv.st (M.vote_time S.E s))
      wv.record cc).cache).read S.E S.hc (M.toHealing (M.mkNode (M.ns_setClock S.E wv.st
        (M.vote_time S.E s)) wv.record cc).st.core) r ⇢ G at hG'
    rewrite [facts.nd.mkNode_cache, facts.nd.mkNode_st] at hG'; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at hG'
    obtain ⟨a, ha⟩ := facts.gr.anchor_nonempty S.E S.hc
      (M.toHealing (M.ns_setClock S.E wv.st (M.vote_time S.E s)).core) r
      (M.readFrame cc (M.toHealing (M.ns_setClock S.E wv.st (M.vote_time S.E s)).core) r).g1
    rw [facts.nd.Sts_gradeContract_read_anchor cc S.E S.hc _ r G hG' a
      ((facts.gr.anchor_eq_of_filtered_fg_root S.E S.hc r _
        (facts.nd.store_with_cache_get_filtered_block_tree _ cc)
        (facts.nd.store_with_cache_get_fg_root _ cc) a).mpr
        (by simpa only [Record.Model.S.toHealing, facts.nd.store_with_cache_readFrame] using ha))]
    rw [hframe] at ha
    exact facts.gr.preceq_anchor_of_g1 _ _ _ _ hQactive hQroot a ha
  have hn : n ∈ Restated.Vocabulary.Internal.NamedRecoveryRead.voteDutyRead M S rho w s :=
    ⟨W (strictEventIndex rho (M.vote_time S.E s)), mem_stateBeforeTime_along₆₀ hf.sorted hf.onePath _,
      cc, hcc, rfl⟩
  exact preceq_trans_Preceq hQA
    (Restated.Vocabulary.Proofs.HealingSurface.voterAnchorAt_preceq_voterHeadAt facts S rho w s n hn
      _ hA T hT L hL L' hL' H hH)

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
local macro "sgf% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SGTargetCanonicalityFixedRoot)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Under the bundle along `W`, for every validator `w` and instants `c ≤ d`, the finalized block of
    `w`'s store in `W` before `c` is an ancestor of the finalized block of `w`'s store in `W` before
    `d`. -/
theorem fixedRoot_strict_finality_monoOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (w : V) {c d : Time} (hcd : c ≤ d) :
    Block.Preceq (W (strictEventIndex rho c) w).st.core.F
      (W (strictEventIndex rho d) w).st.core.F :=
  F_mono_along₆₀ facts S hf.onePath w
    (Restated.strict_lengths_mono rho hcd)

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
local macro "sgf% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SGTargetCanonicalityFixedRoot)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Under the bundle along `W`, if `0 < r`, round `r` is ready, `J` is a run block along `W`, `u` in
    the set for `S.a r` has a node state of its round-`r` action read whose Q2 can return `some Q`,
    `s` is an interior slot of round `r` with its vote instant within the horizon, every node state
    of the round-`r` action read of every member of the set for `S.a r` has FG root `J`, every
    member of the set for `vote_time s` has FG root `J` and `h_max` at most `J`'s height plus one at
    its store in `W` before `vote_time s` with the clock set to it, and `lo ≤ opening (r − η_SG)`,
    then every committee member of `s` in the set for `vote_time s` votes along `W` for a descendant
    of `Q`. -/
theorem honestVotesCone_of_selectedActionG2_exactFGRoot_heightCapOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {r : Round} (hr : 0 < r) (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho r)
    {J : NamedBlock V} (hJrun : Restated.RunBlockOn M S rho W Xb J)
    {u : V} (hu : u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r))) {Q : Block V}
    (nu : M.N)
    (hnu : nu ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) u) r)
    (hQ : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S nu r ⇢ some Q)
    {s : Slot} (hslo : (M.opening_slot S.hc r) + 1 ≤ s)
    (hshi : s < (M.opening_slot S.hc (r + 1)))
    (hhor : M.vote_time S.E s ≤ rho.horizon)
    (hactionRoot : ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) w) r,
      M.get_fg_root (M.toHealing n.st.core).toFG = J.erase)
    (hvoteRoot : ∀ w ∈ Hs (M.vote_time S.E s),
      M.get_fg_root (M.toHealing (M.ns_setClock S.E
        (W (strictEventIndex rho (M.vote_time S.E s)) w).st (M.vote_time S.E s)).core).toFG =
          J.erase)
    (hvoteCap : ∀ w ∈ Hs (M.vote_time S.E s),
      (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) w).st
        (M.vote_time S.E s)).core.h_max ≤ (M.derive_named S.E S.cfg J).h + 1)
    (hlo : lo ≤ M.opening S.E S.hc (r - S.hc.η_SG)) :
    Restated.NamedHonestVotesConeOn M S rho W Hs Xb s (fun X => Block.Preceq Q X) := by
  have hgst : lo ≤ M.early S.E S.hc r .g2 :=
    facts.gr.lo_le_early_g2_of_window_start S hr hlo
  have hs : 0 < s := lt_of_lt_of_le (Nat.zero_lt_succ _) hslo
  have hround : (M.round_of S.hc s) = r :=
    facts.gr.round_of_eq_of_opening_succ_le_of_lt_next_opening S.hc hslo hshi
  have hread : M.domain S.E S.hc r .g1 <
      M.vote_time S.E s := by
    rw [facts.gr.Sts_domain_g1_eq_opening, facts.gr.opening_eq_proposal_time]
    exact (facts.sch.proposal_time_lt_vote_time S.E
      ((M.opening_slot S.hc r))).trans_le
        (facts.sch.vote_time_mono_slots S.E
          (le_trans (Nat.le_succ _) hslo))
  have hnext : M.vote_time S.E s ≤
      M.opening S.E S.hc (r + 1) := by
    rw [facts.gr.opening_eq_proposal_time]
    exact (facts.sch.voteTime_lt_nextProposal_l86d S.E s).le.trans
      (facts.sch.proposal_time_mono S.E
        (Nat.succ_le_iff.mpr hshi))
  have hdomainHor : M.domain S.E S.hc r .g1 ≤ rho.horizon :=
    hread.le.trans hhor
  have hg2g1 : M.domain S.E S.hc r .g2 ≤
      M.domain S.E S.hc r .g1 :=
    facts.gr.domain_g2_le_domain_g1 S r
  have hg2a : M.domain S.E S.hc r .g2 ≤ (Restated.Vocabulary.Execution.Setup.a M S r) :=
    facts.gr.domain_le_a S r .g2
  have huG2 : u ∈ Hs (M.domain S.E S.hc r .g2) :=
    hHs _ _ hg2a hu
  have hJQ : Block.Preceq J.erase Q := by
    rw [← hactionRoot u hu nu hnu]
    exact preceq_eq_true_iff_Preceq.mp (facts.fc.preceq_get_fg_root_of_mem_filtered
      (Restated.Vocabulary.Proofs.HealingSurface.actionQ2_mem_filteredTree facts S rho u r _
        (mem_stateBeforeTime_along₆₀ hf.sorted hf.onePath _) nu hnu hQ))
  obtain ⟨Qn, hQsource, hQnErase, hQnRun⟩ :=
    Restated.fixedRoot_selectedQ2_body_at_captureOn facts S Hs Xb hf (hHsXb _ hu) nu hnu hQ
  have hpostSource : lo ≤ M.domain S.E S.hc r .g2 :=
    hgst.trans (facts.gr.early_le_domain S r)
  have hdeadline :
      max (M.domain S.E S.hc r .g2) lo + S.E.Δ ≤
        M.domain S.E S.hc r .g1 := by
    rw [max_eq_left hpostSource]
    exact facts.gr.domain_g2_add_delta_le_domain_g1 S r
  have huMax : u ∈ Hs (max (M.domain S.E S.hc r .g2) lo) := by
    rw [max_eq_left hpostSource]; exact huG2
  intro w hw hcommittee
  have hwG1 : w ∈ Hs (M.domain S.E S.hc r .g1) :=
    hHs _ _ hread.le hw
  have hrootW : M.get_fg_root (M.toHealing
      (W (strictEventIndex rho (M.vote_time S.E s)) w).st.core).toFG = J.erase :=
    (setClock_fgRoot₆₀ facts S _ (M.vote_time S.E s)).symm.trans (hvoteRoot w hw)
  have hFvoteJ : Block.Preceq
      (W (strictEventIndex rho (M.vote_time S.E s)) w).st.core.F J.erase := by
    have hFroot := facts.fc.preceq_get_fg_root_of_F
      (st := (M.toHealing (W (strictEventIndex rho (M.vote_time S.E s)) w).st.core).toFG)
      (by
        rw [facts.sto.Sts_toHealing_F, facts.sto.Sts_toHealing_J]
        exact preceq_eq_true_iff_Preceq.mpr
          (Restated.Vocabulary.Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime facts
            S rho (M.vote_time S.E s) w _ (mem_stateBeforeTime_along₆₀ hf.sorted hf.onePath _)))
    rw [hrootW, facts.sto.Sts_toHealing_F] at hFroot
    exact preceq_eq_true_iff_Preceq.mp hFroot
  have hFg1J : Block.Preceq
      (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st.core.F J.erase :=
    preceq_trans_Preceq
      (Restated.fixedRoot_strict_finality_monoOn facts S Hs Xb hf w hread.le)
      hFvoteJ
  have hFg1Q : Block.Preceq
      (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st.core.F Q :=
    preceq_trans_Preceq hFg1J hJQ
  have hQatG1 := Restated.healthy_head_body_at_read_after_gst_admitOn facts
    S rho Hs Xb hf hHs hHsXb u w Qn
      (M.domain S.E S.hc r .g2)
      (M.domain S.E S.hc r .g1)
      (M.domain S.E S.hc r .g1) huMax hwG1 hQsource hdeadline
      (le_refl _) hdomainHor (by rw [hQnErase]; exact hFg1Q)
  have hbelow := Restated.crossReaderFinalizedBelow_of_finalitySafety_and_relayOn facts
    S Hs Xb hf hHs hHsXb hf.slashableBound hgst ready.2 huG2 hwG1 (B := Q)
    (fun sender x root H I _ _ c hcover hc hconf hfind => by
      rw [hconf] at hcover
      exact preceq_trans_Preceq hFg1Q
        (facts.gr.preceq_of_localCovers_of_find c hcover hc hfind))
  have hguard := Restated.crossReaderBodyReadyGuard_of_finalizedBelowOn facts
    S Hs Xb hf hHs hHsXb hr hgst ready.2 huG2 hwG1 hbelow
  have hG2 := storeGrade_true_of_all₆₀ facts _ _ _ _ _ _
    (Restated.selectedQ2_storeGrade_at_g2DomainOn facts S Hs Xb hf nu hnu hQ)
  have hG1 := storeGrade_true_of_all₆₀ facts _ _ _ _ _ _
    (Restated.storeGrade_g1_of_storeGrade_g2_cross_readerOn facts
      S rho Hs Xb hf hHs hHsXb r hlo ready.2 u w huG2 hwG1 Q hG2 hguard)
  have hQvote := Restated.healthy_head_body_at_read_after_gst_admitOn facts
    S rho Hs Xb hf hHs hHsXb u w Qn
      (M.domain S.E S.hc r .g2)
      (M.domain S.E S.hc r .g1)
      (M.vote_time S.E s) huMax hwG1 hQsource hdeadline hread.le hdomainHor
      (by rw [hQnErase]; exact preceq_trans_Preceq hFvoteJ hJQ)
  obtain ⟨Jn, hJnQ, hJnErase⟩ :=
    Proofs.NamedAncestry.erased_ancestor_lift Qn (by simpa only [hQnErase] using hJQ)
  have hJnRun := Restated.blockInRun_of_ancestorOn facts S rho W Xb hQnRun hJnQ
  have hJnEq : Jn = J := Restated.fixedRoot_runBlock_unique_of_erase_eqOn facts
    hf hJnRun hJrun (hJnErase.trans rfl)
  have hheight : (M.derive_named S.E S.cfg J).h ≤
      (M.derive_named S.E S.cfg Qn).h := by
    rw [← hJnEq]
    exact facts.cs.derive_height_mono S.E S.cfg hJnQ
  have hQfiltered : Q ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
      (W (strictEventIndex rho (M.vote_time S.E s)) w) := by
    have hcap := hvoteCap w hw
    rw [facts.hd.setClock_core_h_max] at hcap
    exact Restated.Vocabulary.Proofs.HealingSurface.mem_filtered_of_mem_tree_of_exactFGRoot_heightCap
      facts S rho w (M.vote_time S.E s) _ (mem_stateBeforeTime_along₆₀ hf.sorted hf.onePath _)
      hQvote.1 hQnErase hrootW hJQ (hcap.trans (Nat.add_le_add_right hheight 1))
  have hgatD1 : lo ≤ M.domain S.E S.hc r .g1 :=
    hpostSource.trans hg2g1
  have hQdomain : Q ∈ (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st.core.T := by
    rw [← hQnErase]
    exact Proofs.HealingLemmas.find?_mem hQatG1.2.2
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
    (W (strictEventIndex rho (M.vote_time S.E s)) w).st.core.toHealing (M.vote_time S.E s)
    (W (strictEventIndex rho (M.vote_time S.E s)) w).cache
  set n := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) w).st
    (M.vote_time S.E s)) (W (strictEventIndex rho (M.vote_time S.E s)) w).record c with hn
  obtain ⟨T, hT⟩ := facts.fc.voter_filtered_block_tree_nonempty S.E n.st.core n.st.core.s
  obtain ⟨L, hL⟩ := facts.fc.voter_view_nonempty S.E
    (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s
  obtain ⟨L', hL'⟩ := facts.fc.voter_support_view_nonempty S.E
    (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s
  obtain ⟨Hd, hHd⟩ := facts.fc.get_head_in_tree_with_layer_nonempty (M.gradeContract n.cache) S.E
    S.hc (M.toHealing n.st.core) T L L' (n.st.core.s - 1)
  have hQhead := Restated.fixedRoot_selectedQ2_preceq_voterHead_of_rawDomainOn facts
    S Hs Xb hf hr hwG1 nu hnu hQ hround hread hnext hdomainHor hQdomain hG1 hQfiltered hgatD1
    c hc T hT L hL L' hL' Hd hHd
  -- `w` passes the grade-1 awake test at its vote ticks.
  have hwin : lo ≤ M.early S.E S.hc (M.round_of S.hc s) .g1 - S.E.Δ := by
    rw [hround]
    have h1 := facts.gr.early_g2_add_delta_le_early_g1 S r
    linarith
  obtain ⟨X, hXerase, hXrun, hXemit⟩ :=
    Restated.named_voter_head_emitsOn facts S Hs Xb hf hHsXb hw hs hcommittee hhor
      (hgatD1.trans hread.le) c hc (fun j hj => hf.awake_g1 _ _ j _ (Or.inr rfl) hj hw hwin)
      T hT L hL L' hL' Hd hHd
  exact ⟨X, by rw [hXerase]; exact hQhead, hXrun, hXemit⟩

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
local macro "sgf% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SGTargetCanonicalityFixedRoot)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Under the bundle along `W`, if `0 < r`, `s` is a slot of round `r` from its opening slot on with
    its vote instant not after `opening (r + 1)` and within the horizon, `w` is in the set for
    `domain r g1` with `lo ≤ domain r g1`, `c` is an outcome of `w`'s cache update at `vote_time s`
    in `W` before it, and the node state staged with `c` has grade-1 frame root `root` with active
    prefix `L`, then `L` is in the tree of `w`'s store in `W` before `domain r g1`, and every
    outcome of its grade-1 store grade there is `true`. -/
theorem fixedRoot_activeVoterAnchor_g1_dataOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {r : Round} (hr : 0 < r) {s : Slot}
    (hslo : (M.opening_slot S.hc r) ≤ s)
    (hround : (M.round_of S.hc s) = r)
    (hnext : M.vote_time S.E s ≤
      M.opening S.E S.hc (r + 1))
    (hvoteHor : M.vote_time S.E s ≤ rho.horizon)
    {w : V} (hw : w ∈ Hs (M.domain S.E S.hc r .g1))
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.vote_time S.E s)) w).st.core.toHealing (M.vote_time S.E s)
      (W (strictEventIndex rho (M.vote_time S.E s)) w).cache ⇢ c)
    {root L : Block V}
    (hframe : (M.readFrame
      (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) w).st
        (M.vote_time S.E s)) (W (strictEventIndex rho (M.vote_time S.E s)) w).record c).cache
      (M.toHealing (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) w).st
        (M.vote_time S.E s)) (W (strictEventIndex rho (M.vote_time S.E s)) w).record c).st.core)
        r).g1 = some (some root))
    (hactive : M.activePrefix
      (Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
        (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) w).st
          (M.vote_time S.E s)) (W (strictEventIndex rho (M.vote_time S.E s)) w).record c))
        root = some L)
    (hgat : lo ≤ M.domain S.E S.hc r .g1) :
    L ∈ (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st.core.T ∧
      ∀ b, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
        (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st r .g1 L ⇢ b → b = true := by
  have hround' : (M.round_of S.hc)
      (S.E.slotOf (M.vote_time S.E s)) = r := by
    rw [facts.sch.slotOf_vote_time]
    exact hround
  have hdomainVote : M.domain S.E S.hc r .g1 < M.vote_time S.E s := by
    rw [facts.gr.Sts_domain_g1_eq_opening, facts.gr.opening_eq_proposal_time]
    exact (facts.sch.proposal_time_mono S.E hslo).trans_lt
      (facts.sch.proposal_time_lt_vote_time S.E s)
  have hg1Hor : M.domain S.E S.hc r .g1 ≤ rho.horizon :=
    hdomainVote.le.trans hvoteHor
  set wv := W (strictEventIndex rho (M.vote_time S.E s)) w with hwv
  set w1 := W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w with hw1
  obtain ⟨fr, hfr⟩ := facts.gr.freezeRoot_nonempty S.E (M.gradeView (M.toHealing w1.st.core))
    w1.st.core.F S.hc.η_SG r (M.early S.E S.hc r .g1) (M.late S.E S.hc r .g1)
  have hbase := Restated.frame_phase_completed_in_roundOn facts
    S rho Hs Xb hf w r hr .g1 hw (M.vote_time S.E s)
    hdomainVote hnext hg1Hor hgat (fun j hj => hf.tick_outcome j _ _ hj) fr hfr
  have hprepared := Restated.Vocabulary.Proofs.NamedOutageClosure.frame_phase_prepared_eq facts
    S rho w r .g1 (M.vote_time S.E s) hround' _ (W (strictEventIndex rho (M.vote_time S.E s)))
    (mem_stateBeforeTime_along₆₀ hf.sorted hf.onePath _) hbase c hc
  have hreadFrame : (M.readFrame c (M.toHealing (M.ns_setClock S.E wv.st
      (M.vote_time S.E s)).core) r).g1 = some (fr.map (fun B => M.clipGrade B wv.st.core.F)) := by
    rw [← facts.gr.phaseResult_g1]
    exact hprepared
  rewrite [facts.nd.mkNode_cache, facts.nd.mkNode_st] at hframe; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at hframe
  have hactive' : M.activePrefix (M.get_filtered_block_tree
      (M.toHealing (M.ns_setClock S.E wv.st (M.vote_time S.E s)).core).toFG) root = some L := by
    have h := hactive
    simp only [Restated.Vocabulary.Internal.PhaseGrades.filteredTree] at h
    rewrite [facts.nd.mkNode_st] at h; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at h
    exact h
  cases fr with
  | none =>
      rw [hframe] at hreadFrame
      simp at hreadFrame
  | some raw =>
      have hrootEq : root = M.clipGrade raw wv.st.core.F := by
        rw [hframe] at hreadFrame
        simpa using hreadFrame
      have hLroot : Block.Preceq L root := facts.gr.preceq_of_activePrefix_eq_some hactive'
      have hLraw : Block.Preceq L raw := by
        rw [hrootEq] at hLroot
        exact preceq_trans_Preceq hLroot (facts.gr.q10_clip_preceq raw wv.st.core.F)
      have hrawTree : raw ∈ w1.st.core.T := by
        have h := facts.gr.mem_T_of_freezeRoot_eq_some (some raw) hfr rfl
        rw [facts.gr.Sts_gradeView_T] at h
        exact h
      have hLtree : L ∈ w1.st.core.T := by
        have hpc := Restated.Vocabulary.Proofs.NamedStoreBridge.parentClosed_stateBeforeTime facts S rho
          (M.domain S.E S.hc r .g1) w _ (mem_stateBeforeTime_along₆₀ hf.sorted hf.onePath _)
        unfold Restated.Vocabulary.Internal.ParentClosed Record.Model.GS.parent_closed at hpc
        have hL := Proofs.Records.mem_of_preceq hpc.2 L raw
          (by rw [facts.sto.toHealing_T]; exact hrawTree)
          (preceq_eq_true_iff_Preceq.mpr hLraw)
        rw [facts.sto.toHealing_T] at hL
        exact hL
      refine ⟨hLtree, ?_⟩
      intro b hb
      obtain ⟨braw, hbraw⟩ := facts.gr.gradeBool_nonempty S.E (M.gradeView (M.toHealing w1.st.core))
        w1.st.core.F S.hc.η_SG r (M.early S.E S.hc r .g1) (M.late S.E S.hc r .g1) raw
      have hrawTrue := facts.gr.gradeBool_of_freezeRoot_eq_some (some raw) hfr rfl braw hbraw
      exact facts.csAdded.confirmation_phaseGrade_mono S.E S.hc _ _ r .g1 hLraw braw hbraw
        hrawTrue b hb

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
local macro "sgf% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SGTargetCanonicalityFixedRoot)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Under the bundle along `W`, if `0 < r`, `S.a r` is within the horizon, `u` is in the set for
    `domain r g0` with `lo ≤ domain r g0`, `L` is in the tree of `u`'s store in `W` before
    `domain r g0`, where its grade-0 store grade can return `true`, `n` is a node state of `u`'s
    round-`r` action read along `W` with `L` in its filtered tree, and the clear test of `n` for `B`
    can return `true`, then `L` and `B` are compatible. -/
theorem fixedRoot_g0_compatible_clearSourceOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {r : Round} (hr : 0 < r) (hactionHor : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon)
    {u : V} (hu : u ∈ Hs (M.domain S.E S.hc r .g0))
    {L B : Block V}
    (hLtree : L ∈ (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) u).st.core.T)
    (hLgrade : Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
      (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) u).st r .g0 L ⇢ true)
    (n : M.N)
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) u) r)
    (hLaction : L ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M n)
    (hBclear : Restated.Vocabulary.Internal.PhaseGrades.nodeClear M S n r B ⇢ true)
    (hgat : lo ≤ M.domain S.E S.hc r .g0) :
    Block.compatible L B = true := by
  set w0 := W (strictEventIndex rho (M.domain S.E S.hc r .g0)) u with hw0
  obtain ⟨fr, hfr⟩ := facts.gr.freezeRoot_nonempty S.E (M.gradeView (M.toHealing w0.st.core))
    w0.st.core.F S.hc.η_SG r (M.early S.E S.hc r .g0) (M.late S.E S.hc r .g0)
  obtain ⟨raw, hraw, hLraw⟩ := facts.gr.q10_freeze_of_graded S.E
    (M.gradeView (M.toHealing w0.st.core)) w0.st.core.F
    S.hc.η_SG r (facts.gr.early_le_late S.E S.hc r .g0)
    (by rw [facts.gr.Sts_gradeView_T]; exact hLtree) true hLgrade rfl fr hfr
  have hframe : (M.readFrame n.cache (M.toHealing n.st.core) r).g0 =
      some (some (M.clipGrade raw n.st.core.F)) := by
    have h := Restated.actionFrame_g0On facts S Hs Xb hf hr hactionHor hu hgat n hn fr hfr
    rw [hraw] at h
    exact h
  have hFL : Block.Preceq n.st.core.F L := by
    have h := facts.fc.finalized_preceq_of_mem_get_filtered_block_tree hLaction
    rw [facts.sto.ModelProperties_toHealing_F] at h
    exact h
  have hLclip : Block.Preceq L (M.clipGrade raw n.st.core.F) := by
    apply (facts.gr.q10_retained_prefix raw n.st.core.F L ?_).mpr hLraw
    exact compatible_of_cases (Or.inr hFL)
  have hBclip : Block.compatible B (M.clipGrade raw n.st.core.F) = true := by
    unfold Restated.Vocabulary.Internal.PhaseGrades.nodeClear
      Restated.Vocabulary.Internal.PhaseGrades.nodeRead at hBclear
    obtain ⟨g, hg, hgB⟩ := returns_map_elim₆₀ _ _ _ hBclear
    have hg' := (facts.nd.gradeContract_read n.cache S.E S.hc _ r g).mp hg
    rw [facts.gr.frameGradeRead_clear n.cache S.E S.hc _ r g hg'] at hgB
    rw [← facts.gr.clear_of_g0 hframe B]
    exact hgB
  rcases compatible_cases hBclip with hBclip | hclipB
  · exact compatible_of_cases (Proofs.ModelProperties.Preceq_linear hLclip hBclip)
  · exact compatible_of_cases (Or.inl (preceq_trans_Preceq hLclip hclipB))

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
local macro "sgf% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SGTargetCanonicalityFixedRoot)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Under the bundle along `W` and the slashable bound, if `0 < r`, round `r` is ready, `S.a r` is
    within the horizon, `J` is a run block along `W`, `u` is in the set for `domain r g0`, `s` is an
    interior slot of round `r` with its vote instant within the horizon, `w` is in the set for
    `domain r g1`, `c` is an outcome of `w`'s cache update at `vote_time s` and the node state
    staged with `c` has grade-1 frame root `root` with active prefix `L`, `nu` is a node state of
    `u`'s round-`r` action read along `W` with FG root `J` and `h_max` at most `J`'s height plus
    one, `w`'s store in `W` before `vote_time s` with the clock set to it has FG root `J`, the clear
    test of `nu` for `B` can return `true`, `B` is an outcome of the SG vote selector on `nu`, and
    `lo ≤ opening (r − η_SG)`, then every anchor outcome of the node state staged with `c` is
    compatible with `B`. -/
theorem voterAnchorAt_compatible_actionSGBlockAtOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hsb : Restated.SlashableBoundOn M S rho W Xb)
    {r : Round} (hr : 0 < r) (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho r)
    (hactionHor : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon)
    {J : NamedBlock V} (hJrun : Restated.RunBlockOn M S rho W Xb J)
    {u : V} (hu : u ∈ Hs (M.domain S.E S.hc r .g0)) {s : Slot}
    (hslo : (M.opening_slot S.hc r) + 1 ≤ s)
    (hshi : s < (M.opening_slot S.hc (r + 1)))
    (hvoteHor : M.vote_time S.E s ≤ rho.horizon)
    {w : V} (hw : w ∈ Hs (M.domain S.E S.hc r .g1))
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.vote_time S.E s)) w).st.core.toHealing (M.vote_time S.E s)
      (W (strictEventIndex rho (M.vote_time S.E s)) w).cache ⇢ c)
    {root L B : Block V}
    (hframe : (M.readFrame
      (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) w).st
        (M.vote_time S.E s)) (W (strictEventIndex rho (M.vote_time S.E s)) w).record c).cache
      (M.toHealing (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) w).st
        (M.vote_time S.E s)) (W (strictEventIndex rho (M.vote_time S.E s)) w).record c).st.core)
        r).g1 = some (some root))
    (hactive : M.activePrefix
      (Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
        (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) w).st
          (M.vote_time S.E s)) (W (strictEventIndex rho (M.vote_time S.E s)) w).record c))
        root = some L)
    (nu : M.N)
    (hnu : nu ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) u) r)
    (hactionRoot : M.get_fg_root (M.toHealing nu.st.core).toFG = J.erase)
    (hactionCap : nu.st.core.h_max ≤ (M.derive_named S.E S.cfg J).h + 1)
    (hvoteRoot : M.get_fg_root (M.toHealing (M.ns_setClock S.E
        (W (strictEventIndex rho (M.vote_time S.E s)) w).st (M.vote_time S.E s)).core).toFG =
        J.erase)
    (hBclear : Restated.Vocabulary.Internal.PhaseGrades.nodeClear M S nu r B ⇢ true)
    (A2 : Option (Block V))
    (hA2 : M.grade2_block_with (M.gradeContract nu.cache) S.E S.hc (M.toHealing nu.st.core)
      (M.round_of S.hc (M.toHealing nu.st.core).s) ⇢ A2)
    (htarget : M.get_sg_vote_with (M.gradeContract nu.cache) S.E S.hc (M.toHealing nu.st.core)
      (M.round_of S.hc (M.toHealing nu.st.core).s) A2 ⇢ B)
    (hlo : lo ≤ M.opening S.E S.hc (r - S.hc.η_SG)) :
    ∀ A, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S
      (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) w).st
        (M.vote_time S.E s)) (W (strictEventIndex rho (M.vote_time S.E s)) w).record c)
      (M.round_of S.hc (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) w).st
        (M.vote_time S.E s)) (W (strictEventIndex rho (M.vote_time S.E s)) w).record c).st.core.s) ⇢ A →
    Block.compatible A B = true := by
  intro A hA
  set wv := W (strictEventIndex rho (M.vote_time S.E s)) w with hwv
  set wa := W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) u with hwa
  set w1 := W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w with hw1
  set w0 := W (strictEventIndex rho (M.domain S.E S.hc r .g0)) u with hw0
  have hround : (M.round_of S.hc s) = r :=
    facts.gr.round_of_eq_of_opening_succ_le_of_lt_next_opening S.hc hslo hshi
  have hnext : M.vote_time S.E s ≤
      M.opening S.E S.hc (r + 1) := by
    rw [facts.gr.opening_eq_proposal_time]
    exact (facts.sch.voteTime_lt_nextProposal_l86d S.E s).le.trans
      (facts.sch.proposal_time_mono S.E (Nat.succ_le_iff.mpr hshi))
  have hgst : lo ≤ M.early S.E S.hc r .g2 :=
    facts.gr.lo_le_early_g2_of_window_start S hr hlo
  have hgstG1 : lo ≤ M.early S.E S.hc r .g1 :=
    hgst.trans (facts.gr.early_g2_le_early_g1 S.E S.hc r)
  have hgstDomain : lo ≤ M.domain S.E S.hc r .g1 :=
    hgstG1.trans (facts.gr.early_g1_le_domain_g1 S r)
  have hgstDomain0 : lo ≤ M.domain S.E S.hc r .g0 :=
    hgstDomain.trans (facts.gr.domain_le_domain_g0 S r .g1)
  obtain ⟨hLtreeG1, hLgrade1⟩ := Restated.fixedRoot_activeVoterAnchor_g1_dataOn facts
    S Hs Xb hf hr ((Nat.le_succ _).trans hslo) hround hnext hvoteHor hw c hc
      hframe hactive hgstDomain
  have hactive' : M.activePrefix (M.get_filtered_block_tree
      (M.toHealing (M.ns_setClock S.E wv.st (M.vote_time S.E s)).core).toFG) root = some L := by
    have h := hactive
    simp only [Restated.Vocabulary.Internal.PhaseGrades.filteredTree] at h
    rewrite [facts.nd.mkNode_st] at h; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at h
    exact h
  have hLvote : L ∈ M.get_filtered_block_tree
      (M.toHealing (M.ns_setClock S.E wv.st (M.vote_time S.E s)).core).toFG :=
    facts.gr.activePrefix_mem _ _ _ hactive'
  have hJL : Block.Preceq J.erase L := by
    rw [← hvoteRoot]
    exact preceq_eq_true_iff_Preceq.mp (facts.fc.preceq_get_fg_root_of_mem_filtered hLvote)
  obtain ⟨Ln, hLnG1, hLnErase⟩ :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime facts S rho
      (M.domain S.E S.hc r .g1) w _ (mem_stateBeforeTime_along₆₀ hf.sorted hf.onePath _) hLtreeG1
  have hLnRun : Restated.RunBlockOn M S rho W Xb Ln :=
    Restated.fixedRoot_runBlock_of_body_at_readOn_SGTargetCanonicalityFixedRoot facts
      S Hs Xb hf (hHsXb _ hw) hLnG1
  have hdeadline :
      max (M.domain S.E S.hc r .g1) lo + S.E.Δ ≤
        M.domain S.E S.hc r .g0 := by
    rw [max_eq_left hgstDomain]
    exact facts.gr.domain_g1_add_delta_le_domain_g0 S r
  have hwMax : w ∈ Hs (max (M.domain S.E S.hc r .g1) lo) := by
    rw [max_eq_left hgstDomain]; exact hw
  have hrootA : M.get_fg_root (M.toHealing wa.st.core).toFG = J.erase :=
    (Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt_fgRoot_eq_storeBeforeTime facts S rho u r
      _ (mem_stateBeforeTime_along₆₀ hf.sorted hf.onePath _) nu hnu).symm.trans hactionRoot
  have hFActionJ : Block.Preceq wa.st.core.F J.erase := by
    have hFroot := facts.fc.preceq_get_fg_root_of_F
      (st := (M.toHealing wa.st.core).toFG)
      (by
        rw [facts.sto.Sts_toHealing_F, facts.sto.Sts_toHealing_J]
        exact preceq_eq_true_iff_Preceq.mpr
          (Restated.Vocabulary.Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime facts
            S rho (Restated.Vocabulary.Execution.Setup.a M S r) u _
            (mem_stateBeforeTime_along₆₀ hf.sorted hf.onePath _)))
    rw [hrootA, facts.sto.Sts_toHealing_F] at hFroot
    exact preceq_eq_true_iff_Preceq.mp hFroot
  have hFActionL : Block.Preceq wa.st.core.F L :=
    preceq_trans_Preceq hFActionJ hJL
  have hdomainAction : M.domain S.E S.hc r .g0 ≤ (Restated.Vocabulary.Execution.Setup.a M S r) :=
    facts.gr.domain_le_a S r .g0
  have hF0L : Block.Preceq w0.st.core.F L :=
    preceq_trans_Preceq
      (Restated.fixedRoot_strict_finality_monoOn facts S Hs Xb hf u hdomainAction)
      hFActionL
  have hLnG0 := Restated.healthy_head_body_at_read_after_gst_admitOn facts
    S rho Hs Xb hf hHs hHsXb w u Ln
      (M.domain S.E S.hc r .g1)
      (M.domain S.E S.hc r .g0)
      (M.domain S.E S.hc r .g0) hwMax hu hLnG1 hdeadline
      (le_refl _) ready.2 (by rw [hLnErase]; exact hF0L)
  have hLnAction := Restated.healthy_head_body_at_read_after_gst_admitOn facts
    S rho Hs Xb hf hHs hHsXb w u Ln
      (M.domain S.E S.hc r .g1)
      (M.domain S.E S.hc r .g0) ((Restated.Vocabulary.Execution.Setup.a M S r)) hwMax hu hLnG1
      hdeadline hdomainAction ready.2 (by rw [hLnErase]; exact hFActionL)
  obtain ⟨Jn, hJnLn, hJnErase⟩ := Proofs.NamedAncestry.erased_ancestor_lift Ln
    (by simpa only [hLnErase] using hJL)
  have hJnRun := Restated.blockInRun_of_ancestorOn facts S rho W Xb hLnRun hJnLn
  have hJnEq : Jn = J := Restated.fixedRoot_runBlock_unique_of_erase_eqOn facts
    hf hJnRun hJrun (hJnErase.trans rfl)
  have hheight : (M.derive_named S.E S.cfg J).h ≤
      (M.derive_named S.E S.cfg Ln).h := by
    rw [← hJnEq]
    exact facts.cs.derive_height_mono S.E S.cfg hJnLn
  have hLaction : L ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M nu := by
    have hcap : wa.st.core.h_max ≤ (M.derive_named S.E S.cfg J).h + 1 := by
      rw [← actionReadFrom_h_max₆₀ facts S wa r nu hnu]
      exact hactionCap
    have hfiltered :=
      Restated.Vocabulary.Proofs.HealingSurface.mem_filtered_of_mem_tree_of_exactFGRoot_heightCap facts
        S rho u ((Restated.Vocabulary.Execution.Setup.a M S r)) _
        (mem_stateBeforeTime_along₆₀ hf.sorted hf.onePath _) hLnAction.1 hLnErase hrootA hJL
        (hcap.trans (Nat.add_le_add_right hheight 1))
    show L ∈ M.get_filtered_block_tree (M.toHealing nu.st.core).toFG
    rw [Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt_filteredTree facts S rho u r
      _ (mem_stateBeforeTime_along₆₀ hf.sorted hf.onePath _) nu hnu]
    exact hfiltered
  have hbelow := Restated.g1G0CrossReaderFinalizedBelow_of_finalitySafety_and_relayOn facts
    S Hs Xb hf hHs hHsXb hsb hgstG1 ready.2 hw hu (B := L)
    (fun sender x key Head I _ _ cb hcover hcb hconf hfind => by
      apply preceq_trans_Preceq hF0L
      rw [hconf] at hcover
      exact facts.gr.preceq_of_localCovers_of_find cb hcover hcb hfind)
  have hguard := Restated.g1G0CrossReaderBodyReadyGuard_of_finalizedBelowOn facts
    S Hs Xb hf hHs hHsXb hr hgstG1 ready.2 hw hu hbelow
  have hLgrade0 := Restated.storeGrade_g0_of_storeGrade_g1_cross_readerOn facts
    S rho Hs Xb hf hHs hHsXb r hlo ready.2 w u hw hu L
    (storeGrade_true_of_all₆₀ facts _ _ _ _ _ _ hLgrade1) hguard
  have hLtreeG0 : L ∈ w0.st.core.T := by
    rw [← hLnErase]
    exact Proofs.HealingLemmas.find?_mem hLnG0.2.2
  have hcompat := Restated.fixedRoot_g0_compatible_clearSourceOn facts
    S Hs Xb hf hr hactionHor hu hLtreeG0 (storeGrade_true_of_all₆₀ facts _ _ _ _ _ _ hLgrade0)
    nu hnu hLaction hBclear hgstDomain0
  have hroundRead : M.round_of S.hc
      (M.mkNode (M.ns_setClock S.E wv.st (M.vote_time S.E s)) wv.record c).st.core.s = r := by
    rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.hd.Sts_setClock_core_s, facts.sch.slotOf_vote_time]
    exact hround
  have hAL : A = L := by
    rw [hroundRead] at hA
    unfold Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor
      Restated.Vocabulary.Internal.PhaseGrades.nodeRead at hA
    obtain ⟨g, hg, rfl⟩ := returns_map_elim₆₀ _ _ _ hA
    rewrite [facts.nd.mkNode_cache, facts.nd.mkNode_st] at hg; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at hg
    rewrite [facts.nd.mkNode_cache, facts.nd.mkNode_st] at hframe; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at hframe
    obtain ⟨a, ha⟩ := facts.gr.anchor_nonempty S.E S.hc
      (M.toHealing (M.ns_setClock S.E wv.st (M.vote_time S.E s)).core) r
      (M.readFrame c (M.toHealing (M.ns_setClock S.E wv.st (M.vote_time S.E s)).core) r).g1
    rw [facts.nd.Sts_gradeContract_read_anchor c S.E S.hc _ r g hg a
      ((facts.gr.anchor_eq_of_filtered_fg_root S.E S.hc r _
        (facts.nd.store_with_cache_get_filtered_block_tree _ c)
        (facts.nd.store_with_cache_get_fg_root _ c) a).mpr
        (by simpa only [Record.Model.S.toHealing, facts.nd.store_with_cache_readFrame] using ha))]
    rw [hframe] at ha
    exact facts.gr.anchor_of_activePrefix _ _ _ _ hactive' a ha
  rw [hAL]
  exact hcompat

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
local macro "sgf% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SGTargetCanonicalityFixedRoot)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Under the bundle along `W` and the slashable bound, if `0 < r`, round `r` is ready, `S.a r` is
    within the horizon, `J` is a run block along `W`, `u` is in the set for `domain r g0`, `nu` is a
    node state of `u`'s round-`r` action read along `W`, `G` is an outcome of its grade read at
    round `r` with Q2 `some Q` and deepest clear block `T` from `G.anchor`, `T` is an outcome of the
    SG vote selector on `nu`, `s` is an interior slot of round `r` with its vote instant within the
    horizon, `w` is in the set for `domain r g1`, `nu` has FG root `J` and `h_max` at most `J`'s
    height plus one, `w`'s store in `W` before `vote_time s` with the clock set to it has FG root
    `J`, `lo ≤ opening (r − η_SG)`, and `c` is an outcome of `w`'s cache update at `vote_time s`,
    then every anchor outcome of the node state staged with `c` is compatible with `T`. -/
theorem
    interiorVoteFreshAnchor_compatible_actionSGBlockAt_of_gradeFormsAt_exactFGRoot_heightCapOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hsb : Restated.SlashableBoundOn M S rho W Xb)
    {r : Round} (hr : 0 < r) (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho r)
    (hactionHor : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon)
    {J : NamedBlock V} (hJrun : Restated.RunBlockOn M S rho W Xb J)
    {u : V} (hu : u ∈ Hs (M.domain S.E S.hc r .g0))
    {Q T : Block V}
    (nu : M.N)
    (hnu : nu ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) u) r)
    (G : DecoupledConsensusModel.Protocol.GradeRead V)
    (hG : Restated.Vocabulary.Internal.PhaseGrades.nodeRead M S nu r ⇢ G)
    (hQ : G.Q2 = some Q)
    (hclear : M.deepest_clear (some G.anchor) nu.st.core.live_confirmed G.clear = some T)
    (A2 : Option (Block V))
    (hA2 : M.grade2_block_with (M.gradeContract nu.cache) S.E S.hc (M.toHealing nu.st.core)
      (M.round_of S.hc (M.toHealing nu.st.core).s) ⇢ A2)
    (htarget : M.get_sg_vote_with (M.gradeContract nu.cache) S.E S.hc (M.toHealing nu.st.core)
      (M.round_of S.hc (M.toHealing nu.st.core).s) A2 ⇢ T)
    {s : Slot} (hslo : (M.opening_slot S.hc r) + 1 ≤ s)
    (hshi : s < (M.opening_slot S.hc (r + 1)))
    (hvoteHor : M.vote_time S.E s ≤ rho.horizon)
    {w : V} (hw : w ∈ Hs (M.domain S.E S.hc r .g1))
    (hactionRoot : M.get_fg_root (M.toHealing nu.st.core).toFG = J.erase)
    (hactionCap : nu.st.core.h_max ≤ (M.derive_named S.E S.cfg J).h + 1)
    (hvoteRoot : M.get_fg_root (M.toHealing (M.ns_setClock S.E
        (W (strictEventIndex rho (M.vote_time S.E s)) w).st (M.vote_time S.E s)).core).toFG =
        J.erase)
    (hlo : lo ≤ M.opening S.E S.hc (r - S.hc.η_SG))
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.vote_time S.E s)) w).st.core.toHealing (M.vote_time S.E s)
      (W (strictEventIndex rho (M.vote_time S.E s)) w).cache ⇢ c) :
    ∀ A, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S
      (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) w).st
        (M.vote_time S.E s)) (W (strictEventIndex rho (M.vote_time S.E s)) w).record c)
      (M.round_of S.hc (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) w).st
        (M.vote_time S.E s)) (W (strictEventIndex rho (M.vote_time S.E s)) w).record c).st.core.s) ⇢ A →
    Block.compatible A T = true := by
  intro A hA
  have hg1g0 : M.domain S.E S.hc r .g1 ≤ M.domain S.E S.hc r .g0 :=
    facts.gr.domain_le_domain_g0 S r .g1
  have huG1 : u ∈ Hs (M.domain S.E S.hc r .g1) :=
    hHs _ _ hg1g0 hu
  have hq : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S nu r ⇢ some Q := by
    have h := returns_map_intro₆₀ (fun g : DecoupledConsensusModel.Protocol.GradeRead V => g.Q2)
      _ G hG
    rw [hQ] at h
    exact h
  have hTclear : Restated.Vocabulary.Internal.PhaseGrades.nodeClear M S nu r T ⇢ true := by
    have h := returns_map_intro₆₀
      (fun g : DecoupledConsensusModel.Protocol.GradeRead V => g.clear T) _ G hG
    rw [facts.gr.deepest_clear_test hclear] at h
    exact h
  have hJQ : Block.Preceq J.erase Q := by
    rw [← hactionRoot]
    exact preceq_eq_true_iff_Preceq.mp (facts.fc.preceq_get_fg_root_of_mem_filtered
      (Restated.Vocabulary.Proofs.HealingSurface.actionQ2_mem_filteredTree facts S rho u r _
        (mem_stateBeforeTime_along₆₀ hf.sorted hf.onePath _) nu hnu hq))
  have hQT : Block.Preceq Q T :=
    Restated.preceq_actionSGBlockAt_of_actionQ2On facts S Hs Xb hf hHs hHsXb hr hactionHor
      huG1 hlo nu hnu hq (preceq_eq_true_iff_Preceq.mp (Block.preceq_self Q)) A2 hA2 T htarget
  have hn : M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) w).st
      (M.vote_time S.E s)) (W (strictEventIndex rho (M.vote_time S.E s)) w).record c ∈
      Restated.Vocabulary.Internal.NamedRecoveryRead.voteDutyRead M S rho w s :=
    ⟨W (strictEventIndex rho (M.vote_time S.E s)), mem_stateBeforeTime_along₆₀ hf.sorted hf.onePath _,
      c, hc, rfl⟩
  rcases Restated.Vocabulary.Proofs.HealingSurface.voterAnchorAt_cases facts S rho w s _ hn A hA with
    hroot | ⟨root, L, hframe, hactive, -⟩
  · rewrite [hroot, facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [hvoteRoot]
    exact compatible_of_cases (Or.inl (preceq_trans_Preceq hJQ hQT))
  · have hroundRead : M.round_of S.hc
        (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) w).st
          (M.vote_time S.E s)) (W (strictEventIndex rho (M.vote_time S.E s)) w).record c).st.core.s =
        r := by
      rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.hd.Sts_setClock_core_s, facts.sch.slotOf_vote_time]
      exact facts.gr.round_of_eq_of_opening_succ_le_of_lt_next_opening S.hc hslo hshi
    rw [hroundRead] at hframe
    exact Restated.voterAnchorAt_compatible_actionSGBlockAtOn facts
      S Hs Xb hf hHs hHsXb hsb hr ready hactionHor hJrun hu hslo hshi hvoteHor hw c hc
        hframe hactive nu hnu hactionRoot hactionCap hvoteRoot hTclear A2 hA2 htarget hlo A hA

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
local macro "sgf% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SGTargetCanonicalityFixedRoot)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-! ### Vote-duty, confirmation and grade helpers -/

open scoped DC

/-- The store the slot-`s` vote duty reads, staged from `n`'s core store, is the core store of `n`'s
    store with the clock set to the slot's vote instant. -/
private theorem voteStore_eq₆₀s (facts : Record.Facts M) (S : Setup V) (n : M.N) (s : Slot) :
    Restated.Vocabulary.Proofs.Optimistic.voteStore M S n.st.core s =
      (M.ns_setClock S.E n.st (M.vote_time S.E s)).core := by
  rw [Restated.Vocabulary.Proofs.Optimistic.voteStore, Restated.Vocabulary.Proofs.Optimistic.tickStore,
    facts.hd.setClock_core_eq_store_with_t_s]

/-- The slot of the healing view of the vote-duty store of slot `s` staged from `n`'s core store is
    `s`. -/
private theorem voteStore_hs_s₆₀s (facts : Record.Facts M) (S : Setup V) (n : M.N) (s : Slot) :
    (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S n.st.core s)).s = s := by
  show (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S n.st.core
    s)).toFG.toSG.toGoldfishStore.s = s
  rw [facts.sto.toHealing_gs_s]
  show (Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core (M.vote_time S.E s)).s = s
  rw [Restated.Vocabulary.Proofs.Optimistic.tickStore,
    ← facts.hd.setClock_core_eq_store_with_t_s S.E n.st, facts.hd.Sts_setClock_core_s,
    facts.sch.slotOf_vote_time]

/-- Every SG root the grade contract of `n`'s cache can return for `n`'s healing store at round `r`
    is an outcome of `n`'s anchor at `r`. -/
private theorem nodeAnchor_of_sgRoot₆₀s (facts : Record.Facts M) (S : Setup V) (n : M.N) (r : Round)
    {R : Block V}
    (hR : M.get_sg_root_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core) r ⇢ R) :
    Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n r ⇢ R := by
  obtain ⟨G, hG⟩ := facts.gr.read_nonempty (M.gradeContract n.cache) S.E S.hc
    n.st.core.toHealing r
  have hanchor := (facts.nd.gradeContract_sgRoot_eq_frameAnchor n.cache S.E S.hc _ r R).1 hR
  have hGR : G.anchor = R := facts.nd.Sts_gradeContract_read_anchor n.cache S.E S.hc _ r G hG R hanchor
  rw [← hGR]
  unfold Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor Restated.Vocabulary.Internal.PhaseGrades.nodeRead
  unfold Record.Returns at hG ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image]
  exact ⟨_, hG, rfl⟩

/-- If `votes` with the support votes `support` give a cone of support for the descendants of `B`
    over `Hon` at slot `k`, in the tree `T`, and `votes` is a valid vote set for `k`, then every
    outcome of `B`'s supporter set has more than half of the voters counted in `votes` at `k`. -/
private theorem supporterMajority_of_cone₆₀s (facts : Record.Facts M) (E : Env V)
    {T : Finset (Block V)} {votes support : Finset (GoldfishVote V)} {k : Slot} {Hon : Finset V}
    {B : Block V}
    (hcone : Restated.Vocabulary.Proofs.Optimistic.ConeSupport M E T votes support votes k Hon
      (fun X => Block.Preceq B X))
    (hvalid : Protocol.VoteSetValid E k votes) :
    ∀ sup : Finset V, Restated.Vocabulary.Protocol.goldfishSupporters M E T votes support k B ⇢ sup →
      M.voters_count E votes k < 2 * sup.card := by
  intro sup hsup
  obtain ⟨t, ht⟩ : ∃ t : GoldfishVote V → Bool, ∀ u, M.targets_under T B u ⇢ t u :=
    ⟨fun u => (facts.fc.targets_under_nonempty T B u).choose,
      fun u => (facts.fc.targets_under_nonempty T B u).choose_spec⟩
  have hsub : (E.committee k) ∩ Hon ⊆ sup := by
    intro x hx
    rw [Finset.mem_inter] at hx
    obtain ⟨u, hu, hux, hus, X, hfind, hXslot, hBX⟩ := hcone.vote x hx.1 hx.2
    refine (facts.fc.mem_supporters_iff (_E := E) sup hsup t ht).2
      ⟨hcone.no_equiv x hx.1 hx.2, u, ?_, hus, ?_⟩
    · exact (facts.sch.mem_votes_by_iff support x u).2 ⟨hu, hux⟩
    · exact (facts.fc.targets_under_iff (t u) (ht u)).2
        ⟨X, hfind, hXslot, preceq_eq_true_iff_Preceq.mpr hBX⟩
  have hcard := Finset.card_le_card hsub
  have hcount := facts.fc.voters_count_le_committee E votes k hvalid
  have hmaj := hcone.majority
  omega

omit [DecidableEq V] [Fintype V] in
/-- `m >>= k` can return `b` exactly when `m` can return some `a` from which `k a` can return `b`. -/
private theorem returns_bind_iff₆₀s {α β : Type} (m : DC.NDRE α) (k : α → DC.NDRE β) (b : β) :
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

/-- Every outcome of the early confirmation votes of `st` at slot `s` is among the late confirmation
    votes. -/
private theorem confEarly_subset_late₆₀s (facts : Record.Facts M) (E : Env V) (st : M.S) (s : Slot) :
    ∀ e, Restated.Vocabulary.Protocol.confEarly M E st s ⇢ e →
      e ⊆ Restated.Vocabulary.Protocol.confLate M E st s := by
  intro e he u hu
  obtain ⟨τ, hτ, rfl⟩ := returns_map_elim₆₀ _ _ _ he
  rw [beforeCutoff, Finset.mem_filter] at hu
  refine DecoupledConsensusModel.Protocol.beforeCutoff_mono _
    (facts.sch.Protocol_support_cutoff_le_confirmation_time E s) _ ?_
  rw [beforeCutoff, Finset.mem_filter]
  exact ⟨hu.1, facts.sto.stampedBefore_vote_of_tau st τ hτ hu.2⟩

/-- If `B` is a `GenuineConfirmation` of `st` at slot `s` under `contract`, then there are an
    outcome `early` of the early confirmation votes of `st` at `s` and a choice `sc` of one Goldfish
    score outcome per block, over the votes of `early` with no second vote in the late votes, such
    that those votes are an outcome of the confirmation votes and the count of the late voters is
    less than twice `sc B`. -/
private theorem genuine_eligible₆₀s (facts : Record.Facts M) {contract : M.Contract} {E : Env V}
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
    returns_map_intro₆₀ _ _ _ htm
  have hu := returns_map_intro₆₀
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

/-- If the source's early, late and counted votes have the confirmation numerator's shape, the
    transport from the source tree to the target tree holds for `B`, `g` is an outcome of `B`'s
    Goldfish score over the source votes with the late voter count less than `2 * g`, the target
    support votes are among the target votes, `A` is compatible with `B`, and every block strictly
    between `A` and `B` is in `tree` when `A ⪯ B`, then `B` is an ancestor of every outcome of the
    Goldfish fork choice from `A`. -/
private theorem captures_of_confirmation_one₆₀s (facts : Record.Facts M)
    (E : Env V) (σ : Block V → M.CS) (h_max : Height)
    (sourceTree targetTree tree : Finset (Block V)) (cur : Slot)
    (sourceEarly sourceLate sourceVotes targetVotes targetSupport :
      Finset (GoldfishVote V)) (s : Slot) {A B : Block V}
    (hN : Restated.Vocabulary.Protocol.Numerator M sourceEarly sourceLate sourceVotes)
    (hT : Restated.Vocabulary.Protocol.AdoptionTransport M sourceTree targetTree sourceVotes sourceLate
      targetVotes targetSupport B)
    (g : ℕ) (hg : M.goldfish_score E sourceTree sourceVotes sourceVotes s B ⇢ g)
    (heligible : M.voters_count E sourceLate s < 2 * g)
    (hsub : targetSupport ⊆ targetVotes)
    (hcompatible : Block.compatible A B = true)
    (hpath : Block.Preceq A B →
      ∀ C : Block V, Block.Preceq A C → C ≠ A → Block.Preceq C B →
        C ∈ tree) :
    ∀ X : Block V, M.goldfish_fork_choice E σ h_max targetTree cur A tree
        targetVotes targetSupport s ⇢ X → Block.Preceq B X := by
  intro X hX
  have hS := fun u => facts.fc.targets_under_nonempty sourceTree B u
  have hTt := fun u => facts.fc.targets_under_nonempty targetTree B u
  let tS : GoldfishVote V → Bool := fun u => Classical.choose (hS u)
  let tT : GoldfishVote V → Bool := fun u => Classical.choose (hTt u)
  have htS : ∀ u, M.targets_under sourceTree B u ⇢ tS u := fun u => Classical.choose_spec (hS u)
  have htT : ∀ u, M.targets_under targetTree B u ⇢ tT u := fun u => Classical.choose_spec (hTt u)
  obtain ⟨sS, hsS⟩ := facts.fc.raw_supporters_nonempty sourceTree sourceVotes sourceVotes s B
  obtain ⟨sT, hsT⟩ := facts.fc.raw_supporters_nonempty targetTree targetVotes targetSupport s B
  have hforward : ∀ u ∈ sourceVotes, tS u = true →
      (u ∈ targetSupport ∧ tT u = true) ∨ M.equivocates targetVotes u.val_index = true := by
    intro u hu htu
    rcases hT.forward u hu (tS u) (htS u) htu with ⟨hmem, hall⟩ | heq
    · exact Or.inl ⟨hmem, hall (tT u) (htT u)⟩
    · exact Or.inr heq
  have hadopt := facts.fc.confirmation_adoption hN.early_late hN.filtered tS htS tT htT hforward
    hT.backward g hg heligible sS hsS sT hsT
  exact facts.fc.goldfish_fork_choice_captures_supporter_majority E σ h_max targetTree tree cur
    targetVotes targetSupport s hsub sT hsT hadopt.2 hcompatible hpath X hX

/-- If every member of the set for `domain q .g2` has `P` active, with every outcome of its grade-2
    store grade `true`, in its node state in `W (strictEventIndex rho (domain q .g2))`, `reader` is
    in that set and `S.a q ≤ read`, then `P` is in `reader`'s store in
    `W (strictEventIndex rho read)`. -/
private theorem formsW_processedAtRead₆₀s (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {q : Round} {P : Block V}
    (hformsW : ∀ v ∈ Hs (M.domain S.E S.hc q .g2),
      P ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc q .g2)) v) ∧
        ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
          (W (strictEventIndex rho (M.domain S.E S.hc q .g2)) v).st q .g2 P ⇢ b → b = true)
    {reader : V} (hreader : reader ∈ Hs (M.domain S.E S.hc q .g2))
    {read : Time} (hle : (Restated.Vocabulary.Execution.Setup.a M S q) ≤ read) :
    P ∈ (W (strictEventIndex rho read) reader).st.T := by
  have hdle : M.domain S.E S.hc q .g2 ≤ read := (facts.gr.domain_le_a S q .g2).trans hle
  have hsource : P ∈
      (W (strictEventIndex rho (M.domain S.E S.hc q .g2)) reader).st.core.T := by
    have hfiltered := (hformsW reader hreader).1
    have htree := facts.fc.get_filtered_block_tree_subset _ hfiltered
    rw [facts.sto.toHealing_gs_T] at htree
    exact htree
  have hmn : strictEventIndex rho (M.domain S.E S.hc q .g2) ≤ strictEventIndex rho read :=
    Restated.strict_filter_length_mono rho hdle
  exact Restated.Vocabulary.Proofs.stateBefore_T_subset facts S rho reader
    _ (hf.onePath _).1 _ hmn _ (onePath_slice₆₀ W hf.onePath hmn) hsource

/-- Every node state the round-`r` action read computed from `before` can give has the tree of
    `before`'s core store. -/
private theorem actionReadFrom_T₆₀s (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      n.st.core.T = before.st.core.T := by
  intro n hn
  obtain ⟨st₀, hst₀, hX₀⟩ := actionReadFrom_core₆₀ facts S before r n hn
  rw [hst₀, facts.nd.store_with_cache_core_T,
    facts.dt.update_confirmation_with_T _ _ _ _ _ _ hX₀,
    facts.hd.ModelProperties_setClock_core_T]

/-- Every node state the round-`r` action read computed from `before` can give has the FG root of
    `before`'s core store. -/
private theorem actionReadFrom_fgRoot₆₀s (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      M.get_fg_root (M.toHealing n.st.core).toFG = M.get_fg_root (M.toHealing before.st.core).toFG := by
  intro n hn
  obtain ⟨st₀, hst₀, hX₀⟩ := actionReadFrom_core₆₀ facts S before r n hn
  rw [hst₀, facts.nd.store_with_cache_get_fg_root,
    facts.dt.update_confirmation_with_toHealing_fg_root _ _ _ _ _ _
    hX₀, facts.hd.setClock_core_eq_store_with_t_s]
  exact facts.fc.get_fg_root_toHealing_clock _ _ _

/-- Under the bundle along `W`, if `J` and `T` are run blocks along `W` with `J.erase ⪯ T.erase`,
    `0 < d`, `w` is in the set for `view_freeze (d − 1)`, `w`'s vote read at `d` has FG root `J` and
    `h_max` at most `J`'s height plus one, `T.erase` is in an outcome of `w`'s voter-processed tree
    at `d`, and `lo ≤ view_freeze (d − 1)`, then `T.erase` is in every outcome of the voter's
    filtered block tree of that read, and so is every block strictly between an anchor outcome of
    that read and `T.erase`. -/
theorem fixedRoot_targetCandidateAndPathOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {J T : NamedBlock V} (hJrun : Restated.RunBlockOn M S rho W Xb J)
    (hTrun : Restated.RunBlockOn M S rho W Xb T) (hJT : Block.Preceq J.erase T.erase)
    {w : V} {d : Slot} (hd : 0 < d)
    (hw : w ∈ Hs (M.view_freeze S.E (d - 1)))
    (hroot : M.get_fg_root (M.toHealing (M.ns_setClock S.E
      (W (strictEventIndex rho (M.vote_time S.E d)) w).st (M.vote_time S.E d)).core).toFG =
        J.erase)
    (hcap : (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st
      (M.vote_time S.E d)).core.h_max ≤ (M.derive_named S.E S.cfg J).h + 1)
    (P : Finset (Block V))
    (hP : M.voter_processed_block_tree S.E
      (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core d)).toFG.toSG.toGoldfishStore
      (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core d)).s ⇢ P)
    (hprocessed : T.erase ∈ P)
    (hgat : lo ≤ M.view_freeze S.E (d - 1))
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core.toHealing
      (M.vote_time S.E d) (W (strictEventIndex rho (M.vote_time S.E d)) w).cache ⇢ c) :
    let n := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st
      (M.vote_time S.E d)) (W (strictEventIndex rho (M.vote_time S.E d)) w).record c
    ∀ K : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ K →
      T.erase ∈ K ∧
      ∀ A : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n
          (M.round_of S.hc n.st.core.s) ⇢ A →
        ∀ D : Block V, Block.Preceq A D → D ≠ A → Block.Preceq D T.erase → D ≠ T.erase →
          D ∈ K := by
  intro n K hK
  have hwmem := mem_stateBeforeTime_along₆₀ hf.sorted hf.onePath (M.vote_time S.E d)
  have hnst : n.st = M.store_with_cache (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st (M.vote_time S.E d)) _ := facts.nd.mkNode_st _ _ _
  have hslot : n.st.core.s = d := by
    rw [hnst]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    rw [facts.hd.Sts_setClock_core_s, facts.sch.slotOf_vote_time]
  have hP' : M.voter_processed_block_tree S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore
      n.st.core.s ⇢ P := by
    have h := hP
    rw [voteStore_hs_s₆₀s facts, voteStore_eq₆₀s facts] at h
    rw [hslot, hnst, facts.nd.store_with_cache_voter_processed_block_tree]
    exact h
  have hraw : T.erase ∈ (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core.T := by
    have h := facts.fc.mem_T_of_mem_voter_processed_block_tree _ _ _ P hP' hprocessed
    rw [facts.sto.toHealing_gs_T, hnst] at h
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at h
    rw [facts.hd.Sts_setClock_core_T] at h
    exact h
  obtain ⟨T', hT'body, hT'erase⟩ :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime facts S rho
      (M.vote_time S.E d) w _ hwmem hraw
  have hT'run : Restated.RunBlockOn M S rho W Xb T' :=
    Restated.fixedRoot_runBlock_of_body_at_readOn_SGTargetCanonicalityFixedRoot facts
      S Hs Xb hf (hHsXb _ hw) hT'body
  have hT'eq : T' = T := Restated.fixedRoot_runBlock_unique_of_erase_eqOn facts
    hf hT'run hTrun hT'erase
  rw [hT'eq] at hT'body
  have hview := Restated.Vocabulary.Proofs.NamedStoreBridge.derivedView_stateBeforeTime facts
    S rho (M.vote_time S.E d) w _ hwmem T hT'body
  have hstored : (n.st.core.σ T.erase).h = (M.derive_named S.E S.cfg T).h := by
    rw [hnst]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    rw [facts.hd.Sts_setClock_core_σ, hview]
  obtain ⟨J', hJ'T, hJ'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift T hJT
  have hJ'run := Restated.blockInRun_of_ancestorOn facts S rho W Xb hTrun hJ'T
  have hJ'eq : J' = J := Restated.fixedRoot_runBlock_unique_of_erase_eqOn facts
    hf hJ'run hJrun hJ'erase
  have hheightJT : (M.derive_named S.E S.cfg J).h ≤ (M.derive_named S.E S.cfg T).h := by
    rw [← hJ'eq]
    exact facts.cs.derive_height_mono S.E S.cfg hJ'T
  have hcap' : n.st.core.h_max ≤ (M.derive_named S.E S.cfg J).h + 1 := by
    rw [hnst]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    exact hcap
  have hheight : n.st.core.h_max - 1 ≤ (n.st.core.σ T.erase).h := by
    rw [hstored]
    exact Nat.sub_le_iff_le_add.mpr (hcap'.trans (Nat.add_le_add_right hheightJT 1))
  have hFJ : Block.Preceq n.st.core.F n.st.core.J := by
    rw [hnst]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    rw [facts.hd.setClock_core_F, facts.hd.setClock_core_J]
    exact Restated.Vocabulary.Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime facts
      S rho (M.vote_time S.E d) w _ hwmem
  have hFroot := facts.fc.finalized_preceq_get_fg_root _ hFJ
  have hrootT : Block.Preceq (M.get_fg_root (M.toHealing n.st.core).toFG) T.erase := by
    rw [hnst]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    rw [hroot]
    exact hJT
  refine ⟨facts.hd.mem_voter_filtered_block_tree_of_parts S.E n.st.core n.st.core.s P hP'
    hprocessed (Proofs.ModelProperties.Preceq_trans hFroot hrootT) hprocessed
    (Proofs.ModelProperties.Preceq_self _) hheight hrootT K hK, ?_⟩
  intro A hA D hAD _hDA hDT _hDT
  have hDproc : D ∈ P :=
    Restated.ancestorProcessed_of_voterProcessedOn facts S Hs Xb hf (s := d - 1) hw P
      (by simpa only [Nat.sub_add_cancel hd] using hP) hprocessed hgat D hDT
  have hrootD : Block.Preceq (M.get_fg_root (M.toHealing n.st.core).toFG) D :=
    Proofs.ModelProperties.Preceq_trans
      (Restated.Vocabulary.Proofs.w4_fgRoot_preceq_nodeAnchor facts S n _ A hA) hAD
  exact facts.hd.mem_voter_filtered_block_tree_of_parts S.E n.st.core n.st.core.s P hP' hDproc
    (Proofs.ModelProperties.Preceq_trans hFroot hrootD) hprocessed hDT hheight hrootD K hK

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
local macro "sgf% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SGTargetCanonicalityFixedRoot)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

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
local macro "sgf% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SGTargetCanonicalityFixedRoot)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Under the bundle along `W` and the slashable bound, if `0 < r`, round `r` is ready, `J` and `T`
    are run blocks with `J.erase ⪯ T.erase`, `u` in the set for `S.a r` selects `Q` and has clear
    target `T.erase` as its action carrier, `u`'s confirmation store at the opening slot has
    `GenuineConfirmationWith` of `C` with `T.erase ⪯ C`, `S.a r` is within the horizon, `u`'s action
    store has FG root `J` and `h_max` at most `J`'s height plus one, every member of the set for the
    first interior vote instant has FG root `J` and `h_max` at most `J`'s height plus one at its
    vote read there, and `lo ≤ opening (r − η_SG)`, then every committee member of the first
    interior slot in that set votes along `W` for a descendant of `T.erase`. -/
theorem honestVotesCone_succ_of_ancestorGenuineConfirmation_exactFGRoot_heightCapOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hsb : Restated.SlashableBoundOn M S rho W Xb)
    {r : Round} (hr : 0 < r) (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho r)
    {J T : NamedBlock V} (hJrun : Restated.RunBlockOn M S rho W Xb J)
    (hTrun : Restated.RunBlockOn M S rho W Xb T) (hJT : Block.Preceq J.erase T.erase)
    {u : V} (hu : u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r))) {Q C : Block V}
    (nu : M.N)
    (hnu : nu ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) u) r)
    (G : Protocol.GradeRead V)
    (hG : Restated.Vocabulary.Internal.PhaseGrades.nodeRead M S nu r ⇢ G)
    (hQ : G.Q2 = some Q)
    (hclear : M.deepest_clear (some G.anchor) nu.st.core.live_confirmed G.clear = some T.erase)
    (A2 : Option (Block V))
    (hA2 : M.grade2_block_with (M.gradeContract nu.cache) S.E S.hc (M.toHealing nu.st.core)
      (M.round_of S.hc (M.toHealing nu.st.core).s) ⇢ A2)
    (htarget : M.get_sg_vote_with (M.gradeContract nu.cache) S.E S.hc (M.toHealing nu.st.core)
      (M.round_of S.hc (M.toHealing nu.st.core).s) A2 ⇢ T.erase)
    {contract : M.Contract}
    (hgenuine : Restated.Vocabulary.Protocol.GenuineConfirmationWith M contract S.E S.hc
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc r))) u).st.core
        (M.confirmation_time S.E (M.opening_slot S.hc r)))
      ((M.opening_slot S.hc r)) C)
    (hTC : Block.Preceq T.erase C)
    (hactionHor : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon)
    (hactionRoot : M.get_fg_root (M.toHealing nu.st.core).toFG = J.erase)
    (hactionCap : nu.st.core.h_max ≤ (M.derive_named S.E S.cfg J).h + 1)
    (hvoteRoot : ∀ w ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc r) + 1)),
      M.get_fg_root (M.toHealing (M.ns_setClock S.E
        (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc r) + 1))) w).st
        (M.vote_time S.E ((M.opening_slot S.hc r) + 1))).core).toFG = J.erase)
    (hvoteCap : ∀ w ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc r) + 1)),
      (M.ns_setClock S.E
        (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc r) + 1))) w).st
        (M.vote_time S.E ((M.opening_slot S.hc r) + 1))).core.h_max ≤
          (M.derive_named S.E S.cfg J).h + 1)
    (hlo : lo ≤ M.opening S.E S.hc (r - S.hc.η_SG)) :
    Restated.NamedHonestVotesConeOn M S rho W Hs Xb ((M.opening_slot S.hc r) + 1)
      (fun X => Block.Preceq T.erase X) := by
  have hpost : lo ≤ M.proposal_time S.E (M.opening_slot S.hc r) := by
    have h := facts.gr.lo_le_domain_of_window_start S hr hlo .g1
    rwa [facts.gr.Sts_domain_g1_eq_opening, facts.gr.opening_eq_proposal_time] at h
  have hsourceHor : M.confirmation_time S.E (M.opening_slot S.hc r) ≤ rho.horizon := by
    rw [Restated.Vocabulary.Proofs.HealingSurface.opening_confirmation_time_eq_action facts S r]
    exact hactionHor
  have hvoteHor : M.vote_time S.E ((M.opening_slot S.hc r) + 1) ≤ rho.horizon :=
    (Restated.Vocabulary.Protocol.next_vote_time_lt_action facts S r).le.trans hactionHor
  have huConf : u ∈ Hs (M.confirmation_time S.E (M.opening_slot S.hc r)) := by
    rw [Restated.Vocabulary.Proofs.HealingSurface.opening_confirmation_time_eq_action facts S r]
    exact hu
  have huSC : u ∈ Hs (M.support_cutoff S.E (M.opening_slot S.hc r)) :=
    hHs _ _ (facts.sch.Protocol_support_cutoff_le_confirmation_time S.E _) huConf
  have huG0 : u ∈ Hs (M.domain S.E S.hc r .g0) := hHs _ _ (facts.gr.domain_le_a S r .g0) hu
  have hgenuine' : Restated.Vocabulary.Protocol.GenuineConfirmation M (contract := contract) S.E S.hc
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc r))) u).st.core
        (M.confirmation_time S.E (M.opening_slot S.hc r)))
      (M.opening_slot S.hc r) C :=
    ⟨hgenuine.selected, hgenuine.genuine⟩
  intro w hw hcommittee
  -- `w` passes the grade-1 awake test at its vote ticks.
  have hrunw : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w
      (M.vote_time S.E (M.opening_slot S.hc r + 1))) →
      M.awake_for_grade1 S w (W j w) (M.round_of S.hc (M.opening_slot S.hc r + 1)) := by
    have hwin : lo ≤ M.early S.E S.hc (M.round_of S.hc (M.opening_slot S.hc r + 1)) .g1 - S.E.Δ := by
      rw [facts.gr.HealingLemmas_round_of_opening_succ S.hc r]
      have h1 := facts.gr.lo_le_early_g2_of_window_start S hr hlo
      have h2 := facts.gr.early_g2_add_delta_le_early_g1 S r
      linarith
    intro j hj
    exact hf.awake_g1 _ _ j _ (Or.inr rfl) hj hw hwin
  have hwVF : w ∈ Hs (M.view_freeze S.E (M.opening_slot S.hc r)) :=
    hHs _ _ (facts.sch.view_freeze_lt_vote_time_succ S.E _).le hw
  have hloVote : lo ≤ M.vote_time S.E ((M.opening_slot S.hc r) + 1) :=
    hpost.trans ((facts.sch.proposal_time_lt_vote_time S.E _).le.trans
      (facts.sch.vote_time_mono_slots S.E (Nat.le_succ _)))
  have hloVF : lo ≤ M.view_freeze S.E (M.opening_slot S.hc r) :=
    hpost.trans ((facts.sch.proposal_time_lt_vote_time S.E _).le.trans
      (facts.sch.vote_time_le_view_freeze S.E _))
  have hwG1 : w ∈ Hs (M.domain S.E S.hc r .g1) := by
    refine hHs _ _ ?_ hw
    rw [facts.gr.Sts_domain_g1_eq_opening, facts.gr.opening_eq_proposal_time]
    exact (facts.sch.proposal_time_lt_vote_time S.E _).le.trans
      (facts.sch.vote_time_mono_slots S.E (Nat.le_succ _))
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
    (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc r) + 1))) w).st.core.toHealing
    (M.vote_time S.E ((M.opening_slot S.hc r) + 1))
    (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc r) + 1))) w).cache
  set n := M.mkNode (M.ns_setClock S.E
      (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc r) + 1))) w).st
      (M.vote_time S.E ((M.opening_slot S.hc r) + 1)))
    (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc r) + 1))) w).record c
    with hn_def
  have hnst : n.st = M.store_with_cache (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc r) + 1))) w).st (M.vote_time S.E ((M.opening_slot S.hc r) + 1))) _ := facts.nd.mkNode_st _ _ _
  have hnmem : n ∈ Restated.Vocabulary.Internal.NamedRecoveryRead.voteDutyRead M S rho w
      ((M.opening_slot S.hc r) + 1) :=
    ⟨_, mem_stateBeforeTime_along₆₀ hf.sorted hf.onePath _, c, hc, rfl⟩
  have hroot := hvoteRoot w hw
  have hcap := hvoteCap w hw
  have hrootC : Block.Preceq
      (M.get_fg_root (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc r) + 1))) w).st.core
        ((M.opening_slot S.hc r) + 1))).toFG) C := by
    rw [voteStore_eq₆₀s facts, hroot]
    exact Proofs.ModelProperties.Preceq_trans hJT hTC
  have hCproc := Restated.voterProcessedTarget_of_genuineConfirmation_after_gstOn facts
    S Hs Xb hf hHs hHsXb huSC hwVF hpost hsourceHor hgenuine' hrootC
  obtain ⟨P, hP⟩ := facts.fc.voter_processed_block_tree_nonempty S.E
    (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
      (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc r) + 1))) w).st.core
      ((M.opening_slot S.hc r) + 1))).toFG.toSG.toGoldfishStore
    (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
      (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc r) + 1))) w).st.core
      ((M.opening_slot S.hc r) + 1))).s
  have hTP : T.erase ∈ P := Restated.ancestorProcessed_of_voterProcessedOn facts
    S Hs Xb hf hwVF P hP (hCproc P hP) hloVF T.erase hTC
  have hcandpath := Restated.fixedRoot_targetCandidateAndPathOn facts S Hs Xb hf hHsXb
    hJrun hTrun hJT (d := (M.opening_slot S.hc r) + 1) (Nat.succ_pos _)
    (by simpa only [Nat.add_sub_cancel] using hwVF) hroot hcap P hP hTP
    (by simpa only [Nat.add_sub_cancel] using hloVF) c hc
  have hcompat := Restated.interiorVoteFreshAnchor_compatible_actionSGBlockAt_of_gradeFormsAt_exactFGRoot_heightCapOn
    facts S Hs Xb hf hHs hHsXb hsb hr ready hactionHor hJrun huG0 nu hnu G hG hQ hclear
    A2 hA2 htarget (le_refl _)
    (by
      calc
        (M.opening_slot S.hc r) + 1 < (M.opening_slot S.hc r) + S.hc.R :=
          Nat.add_lt_add_left (lt_of_lt_of_le (by decide : 1 < 2) S.hc.R_ge_two) _
        _ = (M.opening_slot S.hc (r + 1)) := (facts.gr.opening_slot_succ_eq S.hc r).symm)
    hvoteHor hwG1 hactionRoot hactionCap hroot hlo c hc
  have hslot : n.st.core.s = (M.opening_slot S.hc r) + 1 := by
    rw [hnst]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    rw [facts.hd.Sts_setClock_core_s, facts.sch.slotOf_vote_time]
  obtain ⟨T0, hT0⟩ := facts.fc.voter_filtered_block_tree_nonempty S.E n.st.core n.st.core.s
  obtain ⟨L, hL⟩ := facts.fc.voter_view_nonempty S.E
    (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s
  obtain ⟨L', hL'⟩ := facts.fc.voter_support_view_nonempty S.E
    (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s
  obtain ⟨H, hH⟩ := facts.fc.get_head_in_tree_with_layer_nonempty (M.gradeContract n.cache) S.E
    S.hc (M.toHealing n.st.core) T0 L L' (n.st.core.s - 1)
  have hhead : Block.Preceq T.erase H := by
    by_cases hall : ∀ R : Block V, M.get_sg_root_with (M.gradeContract n.cache) S.E S.hc
        (M.toHealing n.st.core) (M.round_of S.hc n.st.core.s) ⇢ R → Block.Preceq R T.erase
    · obtain ⟨P1, hP1⟩ := facts.fc.voter_processed_block_tree_nonempty S.E
        (M.toHealing n.st.core).toFG.toSG.toGoldfishStore (M.toHealing n.st.core).s
      have hK : Restated.Vocabulary.Proofs.Optimistic.voter_candidate_tree M S.E
          (M.toHealing n.st.core) ⇢
            M.get_filtered_block_tree_from (M.toHealing n.st.core).toFG P1 := by
        unfold Restated.Vocabulary.Proofs.Optimistic.voter_candidate_tree
        exact (returns_bind_iff₆₀s _ _ _).2 ⟨P1, hP1, (Record.returns_pure _ _).2 rfl⟩
      have hTK : T.erase ∈ M.get_filtered_block_tree_from (M.toHealing n.st.core).toFG P1 := by
        rw [facts.fc.voter_candidate_tree_eq_protocol_voter_filtered_block_tree S.E n.st.core P1
          hP1 T0 hT0]
        exact (hcandpath T0 hT0).1
      obtain ⟨htransport, hsub, hanchorCompat, hpath, -, -⟩ :=
        Restated.nextVoteAdoption_of_frozenCandidateAtReadOn facts S Hs Xb hf hHs hHsXb
          huConf hpost hsourceHor hw c hc hK hTK hall hrunw
      obtain ⟨early, sc, hearly, hvotes, hsc, helig⟩ := genuine_eligible₆₀s facts hgenuine'
      have hscT : sc C ≤ sc T.erase :=
        facts.fc.goldfish_score_le_of_Preceq _ _ _ _ _ hTC _ (hsc C) _ (hsc T.erase)
      have hel := confEarly_subset_late₆₀s facts S.E _ _ early hearly
      obtain ⟨R, hR⟩ := facts.fc.get_sg_root_with_nonempty (M.gradeContract n.cache) S.E S.hc
        (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s)
      have hs' : (M.toHealing n.st.core).s = n.st.core.s := facts.sto.toHealing_s n.st.core
      have hTn : (M.toHealing n.st.core).T = n.st.core.T := facts.sto.toHealing_T n.st.core
      have hR' : M.get_sg_root_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc n.st.core.s) ⇢ R := by
        rw [hs'] at hR
        exact hR
      have hprev : n.st.core.s - 1 = M.opening_slot S.hc r := by
        rw [hslot]
        simp
      have hX := (facts.fc.get_head_in_tree_split_with (M.gradeContract n.cache) S.E S.hc
        (M.toHealing n.st.core) T0 L L' (n.st.core.s - 1) R hR H).1 hH
      rw [hprev] at hX
      exact captures_of_confirmation_one₆₀s facts S.E (M.toHealing n.st.core).σ
        (M.toHealing n.st.core).h_max _ (M.toHealing n.st.core).T T0 (M.toHealing n.st.core).s
        early _ _ L L' (M.opening_slot S.hc r) ⟨hel, rfl⟩
        (by rw [hTn]; exact htransport _ hvotes L hL L' hL')
        (sc T.erase) (hsc T.erase) (by omega) (hsub L hL L' hL') (hanchorCompat R hR')
        (fun hRB D hRD hDR hDB => hpath R hR' hRB D hRD hDR hDB T0 hT0) H hX
    · push_neg at hall
      obtain ⟨R, hR, hRT⟩ := hall
      have hA := nodeAnchor_of_sgRoot₆₀s facts S n _ hR
      rcases compatible_cases (hcompat R hA) with hRT' | hTR
      · exact absurd hRT' hRT
      · exact Proofs.ModelProperties.Preceq_trans hTR
          (Restated.Vocabulary.Proofs.HealingSurface.voterAnchorAt_preceq_voterHeadAt facts
            S rho w _ n hnmem R hA T0 hT0 L hL L' hL' H hH)
  obtain ⟨X, hXH, hXrun, hXemit⟩ := Restated.named_voter_head_emitsOn facts S Hs Xb hf
    hHsXb hw (Nat.succ_pos _) hcommittee hvoteHor hloVote c hc hrunw T0 hT0 L hL L' hL' H hH
  exact ⟨X, by rw [hXH]; exact hhead, hXrun, hXemit⟩

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
local macro "sgf% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SGTargetCanonicalityFixedRoot)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Under the bundle along `W`, for every validator `w` and slot `s`, every outcome of the voter
    view of `w`'s vote read at `s`, staged from `W (strictEventIndex rho (vote_time s))`, is a valid
    vote set at the slot before. -/
theorem fixedRoot_preparedVoteViewValidOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (w : V) (s : Slot) :
    let st := (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) w).st
      (M.vote_time S.E s)).core
    ∀ Y : Finset (GoldfishVote V),
      M.voter_view S.E (M.toHealing st).toFG.toSG.toGoldfishStore st.s ⇢ Y →
      Protocol.VoteSetValid S.E (st.s - 1) Y :=
  Restated.corePreparedVoteViewValidOn facts S Hs Xb hf w s

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
local macro "sgf% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SGTargetCanonicalityFixedRoot)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Under the bundle along `W` and the committee majority, if `0 < s`, `lo ≤ vote_time s`,
    `vote_time (s + 1)` is within the horizon, every committee member of `s` in the set for its vote
    instant voted along `W` a run block with `C` as an ancestor, `w` is in the set for
    `support_cutoff s`, and `w`'s vote read of `s + 1` has the cone's vote inputs at `C`, then `C`
    is an ancestor of every head of that read. -/
theorem fixedRoot_goldfishConeStepOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {s : Slot} (hs : 0 < s)
    (hpost : lo ≤ M.vote_time S.E s)
    (hvoteHor : M.vote_time S.E (s + 1) ≤ rho.horizon)
    {C : Block V}
    (hnames : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s (fun X => Block.Preceq C X))
    {w : V} (hw : w ∈ Hs (M.support_cutoff S.E s))
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
      (M.vote_time S.E (s + 1))
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ c) :
    let n := M.mkNode
      (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
        (M.vote_time S.E (s + 1)))
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c
    Restated.Vocabulary.Proofs.HealingSurface.GoldfishConeVoteInputs M S rho s C w n →
    ∀ T : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T →
    ∀ L : Finset (GoldfishVote V),
      M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
    ∀ L' : Finset (GoldfishVote V),
      M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
    ∀ H : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
        (M.toHealing n.st.core) T L L' (n.st.core.s - 1) ⇢ H →
      Block.Preceq C H := by
  intro n hinputs T hT L hL L' hL' H hH
  obtain ⟨hcand, hrootC, hanch, hpathI⟩ := hinputs
  have hnst : n.st = M.store_with_cache (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st (M.vote_time S.E (s + 1))) _ := facts.nd.mkNode_st _ _ _
  have hslot : n.st.core.s = s + 1 := by
    rw [hnst]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    rw [facts.hd.Sts_setClock_core_s, facts.sch.slotOf_vote_time]
  have hcutVote : M.support_cutoff S.E s ≤ M.vote_time S.E (s + 1) :=
    facts.sch.support_cutoff_le_vote_time_succ S.E s
  have hcutHor : M.support_cutoff S.E s ≤ rho.horizon := hcutVote.trans hvoteHor
  have havailable := Restated.honestHeadsAvailableBefore_of_namedPostHealingConeOn facts
    S Hs Xb hf hHs hHsXb hw hpost hcutHor (by have h := hrootC; rw [hnst] at h; (try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at h); exact h) hnames
  have hresolve := Restated.headsResolveIn_storeBeforeTime_of_availableBefore_atOn facts
    S Hs Xb hf (hHsXb _ hw) s hcutVote havailable
  have hGammaConf : M.vote_time S.E (s + 1) ≤ M.confirmation_time S.E s := by
    have h := facts.sch.vote_time_succ_add_delta_le_confirmation_time S.E s
    linarith [S.E.Δ_pos]
  have hTgs : (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.T =
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.T := by
    rw [facts.sto.toHealing_gs_T, hnst]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    rw [facts.hd.Sts_setClock_core_T]
  have hbase := Restated.canonicalSuffixConeSupportVoterViewOn facts
    S Hs Xb hf hHs hHsXb hcom hs hpost hcutHor hnames hw hcutVote hGammaConf
    (gst := (M.toHealing n.st.core).toFG.toSG.toGoldfishStore)
    (by
      funext k
      rw [facts.sto.toHealing_gs_gf_votes, hnst, facts.nd.store_with_cache_core_gf_votes,
        facts.hd.setClock_core_gf_votes])
    (by
      rw [facts.sto.toHealing_gs_timestamp_vote, hnst, facts.nd.store_with_cache_core_timestamp_vote,
        facts.hd.setClock_core_timestamp_vote])
    hTgs
    (by
      rw [hTgs, facts.sto.toHealing_gs_timestamp_block, hnst, facts.nd.store_with_cache_core_timestamp_block,
        facts.hd.setClock_core_timestamp_block]
      exact hresolve)
  have hcone : Restated.Vocabulary.Proofs.Optimistic.ConeSupport M S.E n.st.core.T L L' L
      (n.st.core.s - 1) (Hs (M.confirmation_time S.E s)) (fun X => Block.Preceq C X) := by
    have h := hbase L (by rw [← hslot]; exact hL) L' (by rw [← hslot]; exact hL')
    rw [facts.sto.toHealing_gs_T] at h
    rw [hslot, Nat.add_sub_cancel]
    exact h
  have hvalid : Protocol.VoteSetValid S.E (n.st.core.s - 1) L := by
    have h := Restated.fixedRoot_preparedVoteViewValidOn facts S Hs Xb hf w (s + 1) L
      (by have h := hL; rw [hnst] at h; (try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at h); exact h)
    rw [hnst]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    exact h
  have hmaj := supporterMajority_of_cone₆₀s facts S.E hcone hvalid
  obtain ⟨R, hR⟩ := facts.fc.get_sg_root_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s)
  have hs' : (M.toHealing n.st.core).s = n.st.core.s := facts.sto.toHealing_s n.st.core
  have hR' : M.get_sg_root_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
      (M.round_of S.hc n.st.core.s) ⇢ R := by
    rw [hs'] at hR
    exact hR
  have hA := nodeAnchor_of_sgRoot₆₀s facts S n _ hR'
  have hHf := (facts.fc.get_head_in_tree_split_with _ S.E S.hc _ T L L' _ R hR H).1 hH
  obtain ⟨sup, hsup⟩ := facts.fc.raw_supporters_nonempty n.st.core.T L L' (n.st.core.s - 1) C
  have hTeq : (M.toHealing n.st.core).T = n.st.core.T := facts.sto.toHealing_T n.st.core
  rw [hTeq] at hHf
  exact facts.fc.goldfish_fork_choice_captures_supporter_majority _ _ _ _ _ _ _ _ _ hcone.sub
    sup hsup (hmaj sup hsup) (hanch R hA)
    (fun _ D hRD hDne hDC => by
      by_cases hEq : D = C
      · rw [hEq]
        exact hcand T hT
      · exact hpathI R hA T hT D hRD hDne hDC hEq) H hHf

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
local macro "sgf% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SGTargetCanonicalityFixedRoot)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Under the bundle along `W`, the committee majority and the slashable bound, with the hypotheses
    of `honestVotesCone_succ_of_ancestorGenuineConfirmation_exactFGRoot_heightCapOn`, if `s` is an
    interior slot of round `r` with its vote instant within the horizon and at every interior slot
    `d` every member of the set for `vote_time d` has FG root `J` and `h_max` at most `J`'s height
    plus one at its vote read, then every committee member of `s` in the set for `vote_time s` votes
    along `W` for a descendant of `T.erase`. -/
theorem
    honestVotesCone_on_roundInterior_of_ancestorGenuineConfirmation_exactFGRoot_heightCapOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hsb : Restated.SlashableBoundOn M S rho W Xb)
    {r : Round} (hr : 0 < r) (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho r)
    {J T : NamedBlock V} (hJrun : Restated.RunBlockOn M S rho W Xb J)
    (hTrun : Restated.RunBlockOn M S rho W Xb T) (hJT : Block.Preceq J.erase T.erase)
    {u : V} (hu : u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r))) {Q C : Block V}
    (nu : M.N)
    (hnu : nu ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) u) r)
    (G : Protocol.GradeRead V)
    (hG : Restated.Vocabulary.Internal.PhaseGrades.nodeRead M S nu r ⇢ G)
    (hQ : G.Q2 = some Q)
    (hclear : M.deepest_clear (some G.anchor) nu.st.core.live_confirmed G.clear = some T.erase)
    (A2 : Option (Block V))
    (hA2 : M.grade2_block_with (M.gradeContract nu.cache) S.E S.hc (M.toHealing nu.st.core)
      (M.round_of S.hc (M.toHealing nu.st.core).s) ⇢ A2)
    (htarget : M.get_sg_vote_with (M.gradeContract nu.cache) S.E S.hc (M.toHealing nu.st.core)
      (M.round_of S.hc (M.toHealing nu.st.core).s) A2 ⇢ T.erase)
    {contract : M.Contract}
    (hgenuine : Restated.Vocabulary.Protocol.GenuineConfirmationWith M contract S.E S.hc
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc r))) u).st.core
        (M.confirmation_time S.E (M.opening_slot S.hc r)))
      ((M.opening_slot S.hc r)) C)
    (hTC : Block.Preceq T.erase C)
    {s : Slot} (hslo : (M.opening_slot S.hc r) + 1 ≤ s)
    (hshi : s < (M.opening_slot S.hc (r + 1)))
    (hactionHor : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon)
    (hvoteHor : M.vote_time S.E s ≤ rho.horizon)
    (hactionRoot : M.get_fg_root (M.toHealing nu.st.core).toFG = J.erase)
    (hactionCap : nu.st.core.h_max ≤ (M.derive_named S.E S.cfg J).h + 1)
    (hvoteRoot : ∀ d : Slot,
      (M.opening_slot S.hc r) + 1 ≤ d →
      d < (M.opening_slot S.hc (r + 1)) → ∀ w ∈ Hs (M.vote_time S.E d),
      M.get_fg_root (M.toHealing (M.ns_setClock S.E
        (W (strictEventIndex rho (M.vote_time S.E d)) w).st (M.vote_time S.E d)).core).toFG =
          J.erase)
    (hvoteCap : ∀ d : Slot,
      (M.opening_slot S.hc r) + 1 ≤ d →
      d < (M.opening_slot S.hc (r + 1)) → ∀ w ∈ Hs (M.vote_time S.E d),
      (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st
        (M.vote_time S.E d)).core.h_max ≤ (M.derive_named S.E S.cfg J).h + 1)
    (hlo : lo ≤ M.opening S.E S.hc (r - S.hc.η_SG)) :
    Restated.NamedHonestVotesConeOn M S rho W Hs Xb s (fun X => Block.Preceq T.erase X) := by
  have hloNext : (M.opening_slot S.hc r) + 1 < (M.opening_slot S.hc (r + 1)) := hslo.trans_lt hshi
  have hseed :=
    Restated.honestVotesCone_succ_of_ancestorGenuineConfirmation_exactFGRoot_heightCapOn facts
      S Hs Xb hf hHs hHsXb hsb hr ready hJrun hTrun hJT hu nu hnu G hG hQ hclear A2 hA2
      htarget hgenuine hTC hactionHor hactionRoot hactionCap
      (hvoteRoot _ (le_refl _) hloNext) (hvoteCap _ (le_refl _) hloNext) hlo
  have hpostSource : lo ≤ M.proposal_time S.E (M.opening_slot S.hc r) := by
    have h := facts.gr.lo_le_domain_of_window_start S hr hlo .g1
    rwa [facts.gr.Sts_domain_g1_eq_opening, facts.gr.opening_eq_proposal_time] at h
  have hpostLo : lo ≤ M.vote_time S.E ((M.opening_slot S.hc r) + 1) :=
    hpostSource.trans ((facts.sch.proposal_time_lt_vote_time S.E _).le.trans
      (facts.sch.vote_time_mono_slots S.E (Nat.le_succ _)))
  have huConf : u ∈ Hs (M.confirmation_time S.E (M.opening_slot S.hc r)) := by
    rw [Restated.Vocabulary.Proofs.HealingSurface.opening_confirmation_time_eq_action facts S r]
    exact hu
  have huSC : u ∈ Hs (M.support_cutoff S.E (M.opening_slot S.hc r)) :=
    hHs _ _ (facts.sch.Protocol_support_cutoff_le_confirmation_time S.E _) huConf
  have huG0 : u ∈ Hs (M.domain S.E S.hc r .g0) := hHs _ _ (facts.gr.domain_le_a S r .g0) hu
  have hgenuine' : Restated.Vocabulary.Protocol.GenuineConfirmation M (contract := contract) S.E S.hc
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc r))) u).st.core
        (M.confirmation_time S.E (M.opening_slot S.hc r)))
      (M.opening_slot S.hc r) C :=
    ⟨hgenuine.selected, hgenuine.genuine⟩
  have hfold : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s
      (fun X => Block.Preceq T.erase X) ∨ False :=
    Restated.honestVotesCone_or_exit_of_bounded_foldOn facts S rho W Hs Xb hslo hseed (by
      intro k hklo hkhi hcone
      apply Or.inl
      have hkPos : 0 < k := (Nat.succ_pos _).trans_le hklo
      have hdlo : (M.opening_slot S.hc r) + 1 ≤ k + 1 := hklo.trans (Nat.le_succ k)
      have hdhi : k + 1 < (M.opening_slot S.hc (r + 1)) :=
        (Nat.succ_le_iff.mpr hkhi).trans_lt hshi
      have hdHor : M.vote_time S.E (k + 1) ≤ rho.horizon :=
        (facts.sch.vote_time_mono_slots S.E (Nat.succ_le_iff.mpr hkhi)).trans hvoteHor
      have hpostK : lo ≤ M.vote_time S.E k :=
        hpostLo.trans (facts.sch.vote_time_mono_slots S.E hklo)
      intro w hw hcommittee
      have hwVF : w ∈ Hs (M.view_freeze S.E k) :=
        hHs _ _ (facts.sch.view_freeze_lt_vote_time_succ S.E k).le hw
      have hwSC : w ∈ Hs (M.support_cutoff S.E k) :=
        hHs _ _ (facts.sch.support_cutoff_le_vote_time_succ S.E k) hw
      have hloVF : lo ≤ M.view_freeze S.E k :=
        hpostK.trans (facts.sch.vote_time_le_view_freeze S.E k)
      have hwG1 : w ∈ Hs (M.domain S.E S.hc r .g1) := by
        refine hHs _ _ ?_ hw
        rw [facts.gr.Sts_domain_g1_eq_opening, facts.gr.opening_eq_proposal_time]
        exact (facts.sch.proposal_time_lt_vote_time S.E _).le.trans
          (facts.sch.vote_time_mono_slots S.E ((Nat.le_succ _).trans hdlo))
      have hroot := hvoteRoot (k + 1) hdlo hdhi w hw
      have hcap := hvoteCap (k + 1) hdlo hdhi w hw
      have hrootC : Block.Preceq
          (M.get_fg_root (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
            (W (strictEventIndex rho (M.vote_time S.E (k + 1))) w).st.core (k + 1))).toFG) C := by
        rw [voteStore_eq₆₀s facts, hroot]
        exact Proofs.ModelProperties.Preceq_trans hJT hTC
      have hCproc :=
        Restated.voterProcessedTarget_of_genuineConfirmation_at_laterVoteDuty_after_gstOn facts
          S Hs Xb hf hHs hHsXb huSC hwVF hklo hpostSource hdHor hgenuine' hrootC
      obtain ⟨P, hP⟩ := facts.fc.voter_processed_block_tree_nonempty S.E
        (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E (k + 1))) w).st.core (k + 1))).toFG.toSG.toGoldfishStore
        (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E (k + 1))) w).st.core (k + 1))).s
      have hTP : T.erase ∈ P := Restated.ancestorProcessed_of_voterProcessedOn facts
        S Hs Xb hf hwVF P hP (hCproc P hP) hloVF T.erase hTC
      obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E (k + 1))) w).st.core.toHealing
        (M.vote_time S.E (k + 1)) (W (strictEventIndex rho (M.vote_time S.E (k + 1))) w).cache
      set n := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (k + 1))) w).st
          (M.vote_time S.E (k + 1))) (W (strictEventIndex rho (M.vote_time S.E (k + 1))) w).record c
        with hn_def
      have hnst : n.st = M.store_with_cache (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (k + 1))) w).st (M.vote_time S.E (k + 1))) _ := facts.nd.mkNode_st _ _ _
      have hcandpath := Restated.fixedRoot_targetCandidateAndPathOn facts S Hs Xb hf hHsXb
        hJrun hTrun hJT (d := k + 1) (Nat.succ_pos k)
        (by simpa only [Nat.add_sub_cancel] using hwVF) hroot hcap P hP hTP
        (by simpa only [Nat.add_sub_cancel] using hloVF) c hc
      have hanchor :=
        Restated.interiorVoteFreshAnchor_compatible_actionSGBlockAt_of_gradeFormsAt_exactFGRoot_heightCapOn
          facts S Hs Xb hf hHs hHsXb hsb hr ready hactionHor hJrun huG0 nu hnu G hG hQ hclear
          A2 hA2 htarget hdlo hdhi hdHor hwG1 hactionRoot hactionCap hroot hlo c hc
      have hstep := Restated.fixedRoot_goldfishConeStepOn facts S Hs Xb hf hHs hHsXb hcom
        hkPos hpostK hdHor hcone hwSC c hc
        ⟨fun K hK => (hcandpath K hK).1,
          by rw [hnst, facts.nd.store_with_cache_get_fg_root, hroot]; exact hJT,
          hanchor,
          fun A hA K hK D hAD hDA hDT hDne => (hcandpath K hK).2 A hA D hAD hDA hDT hDne⟩
      obtain ⟨T0, hT0⟩ := facts.fc.voter_filtered_block_tree_nonempty S.E n.st.core n.st.core.s
      obtain ⟨L, hL⟩ := facts.fc.voter_view_nonempty S.E
        (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s
      obtain ⟨L', hL'⟩ := facts.fc.voter_support_view_nonempty S.E
        (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s
      obtain ⟨H, hH⟩ := facts.fc.get_head_in_tree_with_layer_nonempty (M.gradeContract n.cache)
        S.E S.hc (M.toHealing n.st.core) T0 L L' (n.st.core.s - 1)
      have hloVote : lo ≤ M.vote_time S.E (k + 1) :=
        hpostK.trans (facts.sch.vote_time_mono_slots S.E (Nat.le_succ k))
      -- `w` passes the grade-1 awake test at its vote ticks.
      have hwin : lo ≤ M.early S.E S.hc (M.round_of S.hc (k + 1)) .g1 - S.E.Δ := by
        rw [facts.gr.round_of_eq_of_opening_succ_le_of_lt_next_opening S.hc hdlo hdhi]
        have h1 := facts.gr.lo_le_early_g2_of_window_start S hr hlo
        have h2 := facts.gr.early_g2_add_delta_le_early_g1 S r
        linarith
      obtain ⟨X, hXH, hXrun, hXemit⟩ := Restated.named_voter_head_emitsOn facts S Hs Xb hf
        hHsXb hw (Nat.succ_pos k) hcommittee hdHor hloVote c hc
        (fun j hj => hf.awake_g1 _ _ j _ (Or.inr rfl) hj hw hwin) T0 hT0 L hL L' hL' H hH
      exact ⟨X, by rw [hXH]; exact hstep T0 hT0 L hL L' hL' H hH, hXrun, hXemit⟩)
  exact hfold.resolve_right False.elim

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
local macro "sgf% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SGTargetCanonicalityFixedRoot)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Under the bundle along `W`, if every member of the set for `domain r g2` has `J` active, with
    every outcome of its grade-2 store grade `true`, in its node state in
    `W (strictEventIndex rho (domain r g2))`, and `v` is in that set, then `J` is in the tree of
    `v`'s core store in `W (strictEventIndex rho (S.a r))`. -/
theorem fixedRoot_namedGrade_processedAtActionOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {r : Round} {J : Block V}
    (hforms : ∀ v ∈ Hs (M.domain S.E S.hc r .g2),
      J ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v) ∧
        ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
          (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v).st r .g2 J ⇢ b → b = true)
    {v : V} (hv : v ∈ Hs (M.domain S.E S.hc r .g2)) :
    J ∈ (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).st.core.T :=
  formsW_processedAtRead₆₀s facts S Hs Xb hf hforms hv (le_refl _)

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
local macro "sgf% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SGTargetCanonicalityFixedRoot)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Under the bundle along `W` and the committee majority, if `0 < r`, round `r` is ready, `J` is a
    run block along `W` whose erasure has grade 2 in round `r` at every member of the set for
    `domain r g2`, `s` is an interior slot of round `r`, `S.a r` and `vote_time s` are within the
    horizon, every action read of every member of the set for `S.a r` has FG root `J` and `h_max` at
    most `J`'s height plus one, the store of every member of the set for `vote_time d` at every
    interior slot `d` has FG root `J` and `h_max` at most `J`'s height plus one, and
    `lo ≤ opening (r − η_SG)`, then for every member `v` of the set for `S.a r` and every block `A`
    the SG vote selector can return at a node state of `v`'s round-`r` action read, every committee
    member of `s` in the set for `vote_time s` votes along `W` for a descendant of `A`. -/
theorem sgTargetConeCanonicality_of_gradeFormsAt_exactFGRoot_heightCapOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {r : Round} (hr : 0 < r) (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho r)
    {J : NamedBlock V} (hJrun : Restated.RunBlockOn M S rho W Xb J)
    (hforms : ∀ v ∈ Hs (M.domain S.E S.hc r .g2),
      J.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v) ∧
        ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
          (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v).st r .g2 J.erase ⇢ b → b = true)
    {s : Slot} (hslo : (M.opening_slot S.hc r) + 1 ≤ s)
    (hshi : s < (M.opening_slot S.hc (r + 1)))
    (hactionHor : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon)
    (hvoteHor : M.vote_time S.E s ≤ rho.horizon)
    (hactionRoot : ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) w) r,
      M.get_fg_root (M.toHealing n.st.core).toFG = J.erase)
    (hactionCap : ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) w) r,
      n.st.core.h_max ≤ (M.derive_named S.E S.cfg J).h + 1)
    (hvoteRoot : ∀ d : Slot,
      (M.opening_slot S.hc r) + 1 ≤ d →
      d < (M.opening_slot S.hc (r + 1)) → ∀ w ∈ Hs (M.vote_time S.E d),
      M.get_fg_root (M.toHealing (M.ns_setClock S.E
        (W (strictEventIndex rho (M.vote_time S.E d)) w).st (M.vote_time S.E d)).core).toFG =
          J.erase)
    (hvoteCap : ∀ d : Slot,
      (M.opening_slot S.hc r) + 1 ≤ d →
      d < (M.opening_slot S.hc (r + 1)) → ∀ w ∈ Hs (M.vote_time S.E d),
      (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st
        (M.vote_time S.E d)).core.h_max ≤ (M.derive_named S.E S.cfg J).h + 1)
    (hlo : lo ≤ M.opening S.E S.hc (r - S.hc.η_SG)) :
    ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r,
      ∀ g : Option (Block V), M.grade2_block_with (M.gradeContract n.cache) S.E S.hc
          (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ g →
      ∀ A : Block V, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc
          (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s) g ⇢ A →
        Restated.NamedHonestVotesConeOn M S rho W Hs Xb s (fun X => Block.Preceq A X) := by
  have hsb : Restated.SlashableBoundOn M S rho W Xb := hf.slashableBound
  intro v hv n hn g hg A hA
  have hvG2 := hHs _ _ (facts.gr.domain_le_a S r .g2) hv
  have hvG1 := hHs _ _ (facts.gr.domain_le_a S r .g1) hv
  have hvG0 := hHs _ _ (facts.gr.domain_le_a S r .g0) hv
  have hwmem := mem_stateBeforeTime_along₆₀ hf.sorted hf.onePath
    (Restated.Vocabulary.Execution.Setup.a M S r)
  have hJraw := Restated.fixedRoot_namedGrade_processedAtActionOn facts S Hs Xb hf hforms hvG2
  obtain ⟨J', hJ'body, hJ'erase⟩ :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime facts S rho
      (Restated.Vocabulary.Execution.Setup.a M S r) v _ hwmem hJraw
  have hJ'run : Restated.RunBlockOn M S rho W Xb J' :=
    Restated.fixedRoot_runBlock_of_body_at_readOn_SGTargetCanonicalityFixedRoot facts
      S Hs Xb hf (hHsXb _ hv) hJ'body
  have hJ'eq : J' = J := Restated.fixedRoot_runBlock_unique_of_erase_eqOn facts
    hf hJ'run hJrun hJ'erase
  rw [hJ'eq] at hJ'body
  have hrootW : M.get_fg_root (M.toHealing
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).st.core).toFG =
        J.erase :=
    (actionReadFrom_fgRoot₆₀s facts S _ r n hn).symm.trans (hactionRoot v hv n hn)
  have hcapW : (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).st.core.h_max ≤
      (M.derive_named S.E S.cfg J).h + 1 := by
    rw [← actionReadFrom_h_max₆₀ facts S _ r n hn]
    exact hactionCap v hv n hn
  have hJactiveW :=
    Restated.Vocabulary.Proofs.HealingSurface.mem_filtered_of_mem_tree_of_exactFGRoot_heightCap
      facts S rho v (Restated.Vocabulary.Execution.Setup.a M S r) _ hwmem hJ'body rfl hrootW
      (Proofs.ModelProperties.Preceq_self J.erase) hcapW
  have hJactive := Restated.Vocabulary.Proofs.HealingSurface.activeAtAction_of_retainedAtRead facts
    S (v := v) _ hwmem hJactiveW n hn
  obtain ⟨G, hG⟩ := facts.gr.read_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) r
  have hG' : Restated.Vocabulary.Internal.PhaseGrades.nodeRead M S n r ⇢ G := by
    unfold Restated.Vocabulary.Internal.PhaseGrades.nodeRead
    exact hG
  have hGq : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ G.Q2 := by
    unfold Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 Restated.Vocabulary.Internal.PhaseGrades.nodeRead
    exact returns_map_intro₆₀ (fun g : DecoupledConsensusModel.Protocol.GradeRead V => g.Q2) _ G hG
  obtain ⟨bg, hbg⟩ := facts.gr.gradeBool_nonempty S.E
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) v).st.core.F S.hc.η_SG r
    (M.early S.E S.hc r .g2) (M.late S.E S.hc r .g2) J.erase
  have hbgtrue : bg = true := (hforms v hvG2).2 bg hbg
  subst hbgtrue
  obtain ⟨Q, hQo, hJQ⟩ :=
    Restated.preceq_actionQ2_of_domainGradeOn facts S Hs Xb hf hHs hr hactionHor hvG0 hlo
      (hforms v hvG2).1 hbg n hn hJactive _ hGq
  have hQ2 : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ some Q := by
    rw [← hQo]
    exact hGq
  have hQA : Block.Preceq Q A :=
    Restated.preceq_actionSGBlockAt_of_actionQ2On facts S Hs Xb hf hHs hHsXb hr hactionHor
      hvG1 hlo n hn hQ2 (Proofs.ModelProperties.Preceq_self Q) g hg A hA
  have hJA : Block.Preceq J.erase A := Proofs.ModelProperties.Preceq_trans hJQ hQA
  have hAraw : A ∈
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).st.core.T := by
    rw [← actionReadFrom_T₆₀s facts S _ r n hn]
    exact Restated.Vocabulary.Proofs.HealingSurface.actionSGBlockAt_mem_actionStore_of_actionQ2 facts
      S rho v r _ hwmem n hn hQ2 g hg A hA
  obtain ⟨T, hTbody, hTerase⟩ :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime facts S rho
      (Restated.Vocabulary.Execution.Setup.a M S r) v _ hwmem hAraw
  have hTrun : Restated.RunBlockOn M S rho W Xb T :=
    Restated.fixedRoot_runBlock_of_body_at_readOn_SGTargetCanonicalityFixedRoot facts
      S Hs Xb hf (hHsXb _ hv) hTbody
  have hJT : Block.Preceq J.erase T.erase := by
    rw [hTerase]
    exact hJA
  have hselected : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s (fun X => Block.Preceq Q X) :=
    Restated.honestVotesCone_of_selectedActionG2_exactFGRoot_heightCapOn facts
      S Hs Xb hf hHs hHsXb hr ready hJrun hv n hn hQ2 hslo hshi hvoteHor
      hactionRoot (hvoteRoot s hslo hshi) (hvoteCap s hslo hshi) hlo
  rcases Restated.Vocabulary.Proofs.HealingSurface.actionSGBlockAt_clear_or_selectedG2 facts S rho
      _ hwmem n hn G hG' hQo g hg A hA with ⟨U, hclearU, hAU⟩ | hAQ
  · have hclearT : M.deepest_clear (some G.anchor) n.st.core.live_confirmed G.clear =
        some T.erase := by
      have hl : (M.toHealing n.st.core).live_confirmed = n.st.core.live_confirmed :=
        facts.sto.toHealing_live_confirmed n.st.core
      have h := hclearU
      rw [hl, ← hAU, ← hTerase] at h
      exact h
    rcases Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt_liveConfirmed_genuine_or_fgRoot
        facts S rho v r _ hwmem n hn with ⟨C, hgenuine, hClive⟩ | ⟨R, hRroot, hRlive⟩
    · have hTC : Block.Preceq T.erase C := by
        rw [hClive]
        exact facts.gr.deepest_clear_Preceq hclearT
      have hgenuine' : Restated.Vocabulary.Protocol.GenuineConfirmationWith M (M.gradeContract n.cache)
          S.E S.hc
          (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
            (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc r))) v).st.core
            (M.confirmation_time S.E (M.opening_slot S.hc r)))
          (M.opening_slot S.hc r) C := by
        rw [Restated.Vocabulary.Proofs.HealingSurface.opening_confirmation_time_eq_action facts S r]
        rw [Restated.Vocabulary.Proofs.HealingSurface.opening_confirmation_time_eq_action facts S r]
          at hgenuine
        exact hgenuine
      have hcone :=
        Restated.honestVotesCone_on_roundInterior_of_ancestorGenuineConfirmation_exactFGRoot_heightCapOn
          facts S Hs Xb hf hHs hHsXb hcom hsb hr ready hJrun hTrun hJT hv n hn G hG'
          hQo hclearT g hg (by rw [hTerase]; exact hA) hgenuine' hTC hslo hshi
          hactionHor hvoteHor (hactionRoot v hv n hn) (hactionCap v hv n hn) hvoteRoot hvoteCap hlo
      rw [← hTerase]
      exact hcone
    · have hRroot' : R = M.get_fg_root (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc r))) v).st.core
          (M.confirmation_time S.E (M.opening_slot S.hc r)))).toFG := by
        rw [Restated.Vocabulary.Proofs.HealingSurface.opening_confirmation_time_eq_action facts S r]
        rw [Restated.Vocabulary.Proofs.HealingSurface.opening_confirmation_time_eq_action facts S r]
          at hRroot
        exact hRroot
      have hTQ := (Restated.clearTarget_eq_fgRoot_and_selectedG2_of_selectedG2On facts
        S Hs Xb hf hHs hHsXb hr hactionHor hvG1 n hn G hG' hQo hclearT hRroot' hRlive
        hlo).2
      have hAQ : A = Q := by
        rw [← hTerase]
        exact hTQ
      rw [hAQ]
      exact hselected
  · rw [hAQ]
    exact hselected

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas

/-! ## Selected Q2 blocks retained in the same round -/

/-- Under the bundle along `W` and the slashable bound, if `0 < r`, round `r` is ready,
    `lo ≤ opening (r − η_SG)`, `p` is in the set for `domain r g2`, `n` is a node state of `p`'s
    round-`r` action read along `W` whose Q2 can return `some Q`, `w` is in the set for
    `domain r g0`, and `Q` is in the filtered trees of `w`'s node states in `W` before `domain r g1`
    and before `domain r g0`, then every outcome of `w`'s grade-1 store grade of `Q` before
    `domain r g1` and of its grade-0 store grade of `Q` before `domain r g0` is `true`. -/
theorem selectedQ2_g1_g0_at_reader_pointwiseOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hsb : Restated.SlashableBoundOn M S rho W Xb) {r : Round} (hr : 0 < r)
    (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho r)
    {p w : V} (hp : p ∈ Hs (M.domain S.E S.hc r .g2)) (hw : w ∈ Hs (M.domain S.E S.hc r .g0))
    {Q : Block V}
    (n : M.N)
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) p) r)
    (hQ : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ some Q)
    (hQg1 : Q ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
      (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w))
    (hQg0 : Q ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
      (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) w))
    (hlo : lo ≤ M.opening S.E S.hc (r - S.hc.η_SG)) :
    (∀ b, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
        (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st r .g1 Q ⇢ b → b = true) ∧
      (∀ b, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
        (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) w).st r .g0 Q ⇢ b → b = true) := by
  have hgst : lo ≤ M.early S.E S.hc r .g2 :=
    facts.gr.lo_le_early_g2_of_window_start S hr hlo
  have hg1g0 : M.domain S.E S.hc r .g1 ≤ M.domain S.E S.hc r .g0 := by
    have h := facts.gr.domain_g1_add_delta_le_domain_g0 S r
    have hd := S.E.Δ_pos
    linarith
  have hwG1 : w ∈ Hs (M.domain S.E S.hc r .g1) := hHs _ _ hg1g0 hw
  have hFg1Q : Block.Preceq (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st.core.F Q := by
    have h := facts.fc.finalized_preceq_of_mem_get_filtered_block_tree hQg1
    rw [facts.sto.ModelProperties_toHealing_F] at h
    exact h
  have hbelowReaders := Restated.crossReaderFinalizedBelow_of_finalitySafety_and_relayOn facts
    S Hs Xb hf hHs hHsXb hsb hgst ready.2 hp hwG1 (B := Q) (by
      intro sender u root H I _ _ c hc hct hconf hfind
      rw [hconf] at hc
      exact Proofs.ModelProperties.Preceq_trans hFg1Q
        (facts.gr.preceq_of_localCovers_of_find c hc hct hfind))
  have hguard := Restated.crossReaderBodyReadyGuard_of_finalizedBelowOn facts
    S Hs Xb hf hHs hHsXb hr hgst ready.2 hp hwG1 hbelowReaders
  have hG2 := Restated.selectedQ2_storeGrade_at_g2DomainOn facts S Hs Xb hf n hn hQ
  have hG1 := Restated.storeGrade_g1_of_storeGrade_g2_cross_readerOn facts
    S rho Hs Xb hf hHs hHsXb r hlo ready.2 p w hp hwG1 Q
    (storeGrade_true_of_all₆₀ facts S.E S.hc _ r .g2 Q hG2) hguard
  have hgstG1 : lo ≤ M.early S.E S.hc r .g1 :=
    hgst.trans (facts.gr.early_g2_le_early_g1 S.E S.hc r)
  have hFg0Q : Block.Preceq (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) w).st.core.F Q := by
    have h := facts.fc.finalized_preceq_of_mem_get_filtered_block_tree hQg0
    rw [facts.sto.ModelProperties_toHealing_F] at h
    exact h
  have hbelow0 :=
    Restated.g1G0CrossReaderFinalizedBelow_of_finalitySafety_and_relayOn facts
      S Hs Xb hf hHs hHsXb hsb hgstG1 ready.2 hwG1 hw (B := Q) (by
        intro sender u root H I _ _ c hc hct hconf hfind
        rw [hconf] at hc
        exact Proofs.ModelProperties.Preceq_trans hFg0Q
          (facts.gr.preceq_of_localCovers_of_find c hc hct hfind))
  have hguard0 := Restated.g1G0CrossReaderBodyReadyGuard_of_finalizedBelowOn facts
    S Hs Xb hf hHs hHsXb hr hgstG1 ready.2 hwG1 hw hbelow0
  exact ⟨hG1, Restated.storeGrade_g0_of_storeGrade_g1_cross_readerOn facts
    S rho Hs Xb hf hHs hHsXb r hlo ready.2 w w hwG1 hw Q
    (storeGrade_true_of_all₆₀ facts S.E S.hc _ r .g1 Q hG1) hguard0⟩

/-- Under the bundle along `W`, if `0 < r`, `S.a r` is within the horizon, `w` is in the set for
    `domain r g0` with `lo ≤ domain r g0`, `Q` is in the filtered tree of `w`'s node state in `W`
    before `domain r g0`, where its grade-0 store grade can return `true`, `n` is a node state of
    `w`'s round-`r` action read along `W` with `Q` in its filtered tree, and the clear test of `n`
    for `C` can return `true`, then `Q` and `C` are compatible. -/
theorem g0Grade_compatible_clearSource_pointwiseOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {r : Round} (hr : 0 < r) (hactionHor : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon)
    {w : V} (hw : w ∈ Hs (M.domain S.E S.hc r .g0)) {Q C : Block V}
    (hQgrade : Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
      (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) w).st r .g0 Q ⇢ true)
    (hQg0 : Q ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
      (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) w))
    (n : M.N)
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) w) r)
    (hQaction : Q ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M n)
    (hCclear : Restated.Vocabulary.Internal.PhaseGrades.nodeClear M S n r C ⇢ true)
    (hgat : lo ≤ M.domain S.E S.hc r .g0) :
    Block.compatible Q C = true := by
  have hQtree : Q ∈ (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) w).st.core.T := by
    have h := facts.fc.get_filtered_block_tree_subset _ hQg0
    rw [facts.sto.toHealing_T] at h
    exact h
  exact Restated.fixedRoot_g0_compatible_clearSourceOn facts S Hs Xb hf hr hactionHor hw
    hQtree hQgrade n hn hQaction hCclear hgat

/-- Under the bundle along `W`, if `n` is a node state of `v`'s round-`r` action read along `W` and
    the Q2 of `n` can return `some Q`, then `0 < r`. -/
theorem nodeQ2_round_pos_pointwiseOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} {r : Round} {Q : Block V}
    (n : M.N)
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r)
    (hQ : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ some Q) : 0 < r := by
  apply Nat.pos_of_ne_zero
  intro hzero
  subst hzero
  have hgrade := Restated.selectedQ2_storeGrade_at_g2DomainOn facts S Hs Xb hf n hn hQ
  obtain ⟨b, hb⟩ := facts.gr.gradeBool_nonempty S.E
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc 0 .g2)) v).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc 0 .g2)) v).st.core.F S.hc.η_SG 0
    (M.early S.E S.hc 0 .g2) (M.late S.E S.hc 0 .g2) Q
  have h1 : b = true := hgrade b hb
  have h0 : b = false := facts.gr.gradeBool_round_zero _ _ _ _ _ _ _ b hb
  rw [h1] at h0
  cases h0

/-- Under the bundle along `W` and the slashable bound, if `0 < r`, round `r` is ready, `S.a r` is
    within the horizon, `lo ≤ opening (r − η_SG)`, `p` is in the set for `domain r g2`, `n` is a
    node state of `p`'s round-`r` action read along `W` whose Q2 can return `some Q`, every member
    of the set for `domain r g0` has `Q` in the filtered trees of its node states in `W` before
    `domain r g1` and before `domain r g0` and of every node state of its round-`r` action read, `w`
    is in that set, `nw` is a node state of `w`'s round-`r` action read along `W`, `G` is an outcome
    of the grade-contract read of `nw` at round `r`, and the walk from `C` to `nw`'s live confirmed
    block with the clear test of `G` returns `X`, then `Q` and `X` are compatible. -/
theorem selectedQ2_compatible_genuineSource_pointwiseOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hsb : Restated.SlashableBoundOn M S rho W Xb) {r : Round} (hr : 0 < r)
    (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho r)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon)
    {p w : V} (hp : p ∈ Hs (M.domain S.E S.hc r .g2)) (hw : w ∈ Hs (M.domain S.E S.hc r .g0))
    {Q C X : Block V}
    (n : M.N)
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) p) r)
    (hQ : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ some Q)
    (hretained : ∀ z, z ∈ Hs (M.domain S.E S.hc r .g0) →
      Q ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
        (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) z) ∧
      Q ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
        (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) z) ∧
      ∀ nz ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) z) r,
        Q ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M nz)
    (nw : M.N)
    (hnw : nw ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) w) r)
    (G : GradeRead V)
    (hG : (M.gradeContract nw.cache).read S.E S.hc (M.toHealing nw.st.core) r ⇢ G)
    (hwalk : M.deepest_clear (some C) nw.st.core.live_confirmed G.clear = some X)
    (hlo : lo ≤ M.opening S.E S.hc (r - S.hc.η_SG)) :
    Block.compatible Q X = true := by
  have hgat : lo ≤ M.domain S.E S.hc r .g0 := by
    have hgst := facts.gr.lo_le_early_g2_of_window_start S hr hlo
    have h1 := facts.gr.early_g2_le_opening S r
    have h0 := facts.gr.domain_g0_eq_opening S r
    have hd := S.E.Δ_pos
    linarith
  obtain ⟨-, hQG0⟩ := Restated.selectedQ2_g1_g0_at_reader_pointwiseOn facts
    S Hs Xb hf hHs hHsXb hsb hr ready hp hw n hn hQ (hretained w hw).1
      (hretained w hw).2.1 hlo
  have hXtrue : G.clear X = true := facts.gr.deepest_clear_test hwalk
  have hXclear : Restated.Vocabulary.Internal.PhaseGrades.nodeClear M S nw r X ⇢ G.clear X :=
    returns_map_intro₆₀ (fun g : GradeRead V => g.clear X) _ G hG
  rw [hXtrue] at hXclear
  exact Restated.g0Grade_compatible_clearSource_pointwiseOn facts S Hs Xb hf hr hhor hw
    (storeGrade_true_of_all₆₀ facts S.E S.hc _ r .g0 Q hQG0)
    (hretained w hw).2.1 nw hnw ((hretained w hw).2.2 nw hnw) hXclear hgat

open scoped DC in
/-- Along the bundle's path `W`, if `n` is a node state of `v`'s round-`r` action read and the FG
    source of `n` at round `r` can return `some B`, then the Q2 of `n` can return some `Q`, and
    either `B = Q`, or there are a cache `cv` the phase tick of `v`'s node state in `W` before the
    confirmation instant of round `r`'s opening slot can return and a block `Cc` with
    `GenuineConfirmationWith` under the contract of `cv` on the tick staging of that node state's
    core store, such that `B` is an ancestor of `Cc` and, for every outcome `G` of `n`'s
    grade-contract read, the walk from `Q` to `n`'s live confirmed block with the clear test of `G`
    returns `B`. -/
private theorem fgSource_cases₆₀p (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} {r : Round} {B : Block V} (n : M.N)
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r)
    (hsource : Restated.Vocabulary.Internal.PhaseGrades.nodeFGSource M S n r ⇢ some B) :
    ∃ Q : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ some Q ∧
      ((∃ (cv : M.Cache) (Cc : Block V),
          M.onPhaseTick S.E S.hc
            (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc r))) v).st.core.toHealing
            (M.confirmation_time S.E (M.opening_slot S.hc r))
            (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc r))) v).cache ⇢ cv ∧
          Restated.Vocabulary.Protocol.GenuineConfirmationWith M (M.gradeContract cv) S.E S.hc
            (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
              (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc r))) v).st.core
              (M.confirmation_time S.E (M.opening_slot S.hc r))) (M.opening_slot S.hc r) Cc ∧
          (∀ G : GradeRead V,
            (M.gradeContract n.cache).read S.E S.hc (M.toHealing n.st.core) r ⇢ G →
            M.deepest_clear (some Q) n.st.core.live_confirmed G.clear = some B) ∧
          Block.Preceq B Cc) ∨ B = Q) := by
  have hmem := mem_stateBeforeTime_along₆₀ hf.sorted hf.onePath
    (Restated.Vocabulary.Execution.Setup.a M S r)
  have hnAt : n ∈ Restated.Vocabulary.Proofs.HealingSurface.actionReadAt M S rho v r := ⟨_, hmem, hn⟩
  have hround : M.round_of S.hc (M.toHealing n.st.core).s = r := by
    show M.round_of S.hc (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.s = r
    rw [facts.sto.toHealing_s]
    exact Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt_round facts S rho v r n hnAt
  have hsource' : Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ some B := by
    show (do
      let g ← M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
        (M.round_of S.hc (M.toHealing n.st.core).s)
      M.fg_source_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
        (M.round_of S.hc (M.toHealing n.st.core).s) g) ⇢ some B
    rw [hround]
    exact hsource
  have hsrc0 := hsource
  unfold Restated.Vocabulary.Internal.PhaseGrades.nodeFGSource at hsrc0
  obtain ⟨A2, hA2, hsrc⟩ := (returns_bind_iff₆₀s _ _ _).1 hsrc0
  obtain ⟨Q2, hA2Q, -⟩ := facts.dt.fg_source_with_some _ _ _ _ _ _ hsrc rfl
  subst hA2Q
  obtain ⟨G, hG⟩ := facts.gr.read_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) r
  have hGQ : G.Q2 = some Q2 :=
    (facts.dt.grade2_block_with_eq_read_Q2 _ _ _ _ _ G hG _ hA2).symm
  have hq : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ some Q2 := by
    have h : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ G.Q2 :=
      returns_map_intro₆₀ (fun g : GradeRead V => g.Q2) _ G hG
    rwa [hGQ] at h
  refine ⟨Q2, hq, ?_⟩
  rcases Restated.Vocabulary.Proofs.HealingSurface.actionFGSource_genuineClear_or_selectedG2_named
      facts S rho v r _ hmem n hn hq hsource' with ⟨Cc, hgen, -, hwalk, -, hBC⟩ | hBQ
  · left
    obtain ⟨c, hc, st, hst, rfl⟩ := hn
    rw [facts.nd.mkNode_cache] at hgen
    rw [Restated.Vocabulary.Proofs.HealingSurface.opening_confirmation_time_eq_action facts S r]
    rw [Restated.Vocabulary.Proofs.HealingSurface.opening_confirmation_time_eq_action facts S r]
      at hgen
    exact ⟨c, Cc, hc, hgen, hwalk, hBC⟩
  · exact Or.inr hBQ

/-- Under the bundle along `W` and the slashable bound, if round `r` is ready, `p` and `w` are in
    the set for `S.a r`, `np` and `nw` are node states of their round-`r` action reads along `W`
    whose FG sources can return `some B` and `some C`, each source is retained by every member of
    the set for `domain r g0` (in its node states in `W` before `domain r g1` and `domain r g0` and
    in every node state of its round-`r` action read) whenever the Q2 of its reader's node state can
    return it, `S.a r` is within the horizon, and `lo ≤ opening (r − η_SG)`, then `B` and `C` are
    compatible. -/
theorem actionFGSources_compatible_sameRound_pointwiseOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hsb : Restated.SlashableBoundOn M S rho W Xb) {r : Round}
    (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho r)
    {p w : V} (hp : p ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)))
    (hw : w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)))
    {B C : Block V}
    (np : M.N)
    (hnp : np ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) p) r)
    (hB : Restated.Vocabulary.Internal.PhaseGrades.nodeFGSource M S np r ⇢ some B)
    (nw : M.N)
    (hnw : nw ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) w) r)
    (hC : Restated.Vocabulary.Internal.PhaseGrades.nodeFGSource M S nw r ⇢ some C)
    (hBretained : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S np r ⇢ some B →
      ∀ z, z ∈ Hs (M.domain S.E S.hc r .g0) →
        B ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) z) ∧
        B ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) z) ∧
        ∀ nz ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) z) r,
          B ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M nz)
    (hCretained : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S nw r ⇢ some C →
      ∀ z, z ∈ Hs (M.domain S.E S.hc r .g0) →
        C ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) z) ∧
        C ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) z) ∧
        ∀ nz ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) z) r,
          C ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M nz)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon)
    (hlo : lo ≤ M.opening S.E S.hc (r - S.hc.η_SG)) : Block.compatible B C = true := by
  obtain ⟨Qp, hQp, hcasesP⟩ := fgSource_cases₆₀p facts S Hs Xb hf np hnp hB
  obtain ⟨Qw, hQw, hcasesW⟩ := fgSource_cases₆₀p facts S Hs Xb hf nw hnw hC
  have hr := Restated.nodeQ2_round_pos_pointwiseOn facts S Hs Xb hf np hnp hQp
  have hg0a : M.domain S.E S.hc r .g0 ≤ (Restated.Vocabulary.Execution.Setup.a M S r) :=
    facts.gr.domain_le_a S r .g0
  have hg2a : M.domain S.E S.hc r .g2 ≤ (Restated.Vocabulary.Execution.Setup.a M S r) :=
    facts.gr.domain_le_a S r .g2
  have hpG2 : p ∈ Hs (M.domain S.E S.hc r .g2) := hHs _ _ hg2a hp
  have hwG2 : w ∈ Hs (M.domain S.E S.hc r .g2) := hHs _ _ hg2a hw
  have hwG0 : w ∈ Hs (M.domain S.E S.hc r .g0) := hHs _ _ hg0a hw
  have hpG0 : p ∈ Hs (M.domain S.E S.hc r .g0) := hHs _ _ hg0a hp
  rcases hcasesP with ⟨cp, X, hcp, hX, hwalkP, hBX⟩ | hBQ
  · rcases hcasesW with ⟨cw, Y, hcw, hY, hwalkW, hCY⟩ | hCQ
    · have hpost : lo ≤ M.proposal_time S.E (M.opening_slot S.hc r) := by
        rw [← facts.gr.opening_eq_proposal_time]
        exact (facts.gr.lo_le_early_g2_of_window_start S hr hlo).trans
          (facts.gr.early_g2_le_opening S r)
      have hconfHor : M.confirmation_time S.E (M.opening_slot S.hc r) ≤ rho.horizon := by
        rwa [Restated.Vocabulary.Proofs.HealingSurface.opening_confirmation_time_eq_action facts S r]
      have hpConf : p ∈ Hs (M.confirmation_time S.E (M.opening_slot S.hc r)) := by
        rw [Restated.Vocabulary.Proofs.HealingSurface.opening_confirmation_time_eq_action facts S r]
        exact hp
      have hwConf : w ∈ Hs (M.confirmation_time S.E (M.opening_slot S.hc r)) := by
        rw [Restated.Vocabulary.Proofs.HealingSurface.opening_confirmation_time_eq_action facts S r]
        exact hw
      have hXY := Restated.sameSlot_genuine_compatible_after_gstOn facts
        S Hs Xb hf hHs hHsXb hpConf hwConf hpost hconfHor cp hcp hX cw hcw hY
      rcases compatible_cases hXY with hXY | hYX
      · exact compatible_of_preceq_common_Preceq
          (preceq_trans_Preceq hBX hXY) hCY
      · exact compatible_of_preceq_common_Preceq
          hBX (preceq_trans_Preceq hCY hYX)
    · subst hCQ
      obtain ⟨G, hG⟩ := facts.gr.read_nonempty (M.gradeContract np.cache) S.E S.hc
        (M.toHealing np.st.core) r
      have hQB := Restated.selectedQ2_compatible_genuineSource_pointwiseOn facts
        S Hs Xb hf hHs hHsXb hsb hr ready hhor hwG2 hpG0 nw hnw hQw (hCretained hQw)
        np hnp G hG (hwalkP G hG) hlo
      exact compatible_of_cases (compatible_cases hQB).symm
  · subst hBQ
    have hQpRetained := hBretained hQp
    rcases hcasesW with ⟨cw, Y, hcw, hY, hwalkW, hCY⟩ | hCQ
    · obtain ⟨G, hG⟩ := facts.gr.read_nonempty (M.gradeContract nw.cache) S.E S.hc
        (M.toHealing nw.st.core) r
      exact Restated.selectedQ2_compatible_genuineSource_pointwiseOn facts
        S Hs Xb hf hHs hHsXb hsb hr ready hhor hpG2 hwG0 np hnp hQp hQpRetained
        nw hnw G hG (hwalkW G hG) hlo
    · subst hCQ
      have hQwRetained := hCretained hQw
      obtain ⟨-, hQpG0⟩ := Restated.selectedQ2_g1_g0_at_reader_pointwiseOn facts
        S Hs Xb hf hHs hHsXb hsb hr ready hpG2 hwG0 np hnp hQp (hQpRetained w hwG0).1
          (hQpRetained w hwG0).2.1 hlo
      obtain ⟨-, hQwG0⟩ := Restated.selectedQ2_g1_g0_at_reader_pointwiseOn facts
        S Hs Xb hf hHs hHsXb hsb hr ready hwG2 hwG0 nw hnw hQw (hQwRetained w hwG0).1
          (hQwRetained w hwG0).2.1 hlo
      obtain ⟨b, hb⟩ := facts.gr.gradeBool_nonempty S.E
        (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) w).st.core))
        (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) w).st.core.F S.hc.η_SG r
        (M.early S.E S.hc r .g0) (M.late S.E S.hc r .g0) B
      obtain ⟨b', hb'⟩ := facts.gr.gradeBool_nonempty S.E
        (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) w).st.core))
        (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) w).st.core.F S.hc.η_SG r
        (M.early S.E S.hc r .g0) (M.late S.E S.hc r .g0) C
      exact Restated.Vocabulary.Proofs.HealingSurface.graded_oneChain_at_reader facts S.E
        (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) w).st.core))
        (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) w).st.core.F
        S.hc.η_SG r (facts.gr.early_le_late S.E S.hc r .g0)
        b hb (hQpG0 b hb) b' hb' (hQwG0 b' hb')

/-! ### Theorems that read the named frame -/

open scoped DC in
/-- Along the bundle's path `W`, if `n` is a node state of `v`'s round-`r` action read and the FG
    source of `n` at round `r` can return `some B`, then the action FG source of `n` (the FG source
    at the round of `n`'s own slot) can return `some B`. -/
private theorem actionFGSource_of_nodeFGSource₆₀p (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} {Hs : Int → Finset V} {Xb : Finset V} {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} {r : Round} {B : Block V} (n : M.N)
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r)
    (hsource : Restated.Vocabulary.Internal.PhaseGrades.nodeFGSource M S n r ⇢ some B) :
    Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ some B := by
  have hmem := mem_stateBeforeTime_along₆₀ hf.sorted hf.onePath
    (Restated.Vocabulary.Execution.Setup.a M S r)
  have hnAt : n ∈ Restated.Vocabulary.Proofs.HealingSurface.actionReadAt M S rho v r := ⟨_, hmem, hn⟩
  have hround : M.round_of S.hc (M.toHealing n.st.core).s = r := by
    show M.round_of S.hc (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.s = r
    rw [facts.sto.toHealing_s]
    exact Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt_round facts S rho v r n hnAt
  show (do
    let g ← M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
      (M.round_of S.hc (M.toHealing n.st.core).s)
    M.fg_source_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
      (M.round_of S.hc (M.toHealing n.st.core).s) g) ⇢ some B
  rw [hround]
  exact hsource

/-- Under the bundle along `W`, if round `r` is ready, the named height-regime frame over `X` holds
    along `W` at `H` up to `stop`, round `r`'s action read is before `stop`, the largest `h_max`
    over `X` in `W stop` is less than `H + 2`, and `p` in the set for `S.a r` has a node state of
    its round-`r` action read along `W` whose Q2 and whose action FG source can return
    `some Q.erase`, with `Q` held there at height `H + 1`, then every member of the set for
    `domain r g0` has `Q.erase` in the filtered trees of its node states in `W` before `domain r g1`
    and before `domain r g0`, and of every node state of its round-`r` action read along `W`. -/
theorem sameRoundSourceQ2Retained_of_namedFrameOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb X : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hX : ∀ t : Int, 0 ≤ t → Hs t ⊆ X) (hXXb : X ⊆ Xb)
    {r : Round} (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho r)
    {p : V} (hpAct : p ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r))) {Q : NamedBlock V}
    (n : M.N)
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) p) r)
    (hselected : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ some Q.erase)
    (hsource : Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ some Q.erase)
    (hQmem : Q ∈ n.st.bodies)
    {stop : Nat} {H : Height} {Prev : NamedBlock V} {c0 : Round}
    (hframe : Restated.NamedHeightRegimeFrameOn M S rho W
      (fun t => W (strictEventIndex rho t)) Hs X Xb H stop Prev c0)
    (hQheight : (M.derive_named S.E S.cfg Q).h = H + 1)
    (hactionPrefix : strictEventIndex rho ((Restated.Vocabulary.Execution.Setup.a M S r)) ≤ stop)
    (hfrontier : (X.sup fun u => (W stop u).st.core.h_max) < H + 2)
    (hactionHor : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon)
    (hlo : lo ≤ M.early S.E S.hc r .g2) :
    ∀ w, w ∈ Hs (M.domain S.E S.hc r .g0) →
      Q.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w) ∧
      Q.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) w) ∧
      ∀ nw ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) w) r,
        Q.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M nw := by
  have hp : p ∈ Hs (M.domain S.E S.hc r .g2) :=
    hHs _ _ (facts.gr.domain_le_a S r .g2) hpAct
  have hlopos : 0 < lo := hf.lo_pos
  have hd := S.E.Δ_pos
  have hg1g0 : M.domain S.E S.hc r .g1 ≤ M.domain S.E S.hc r .g0 := by
    have h := facts.gr.domain_g1_add_delta_le_domain_g0 S r
    linarith
  have hg2g0 : M.early S.E S.hc r .g2 ≤ M.domain S.E S.hc r .g0 := by
    have h1 := facts.gr.early_g2_le_opening S r
    have h0 := facts.gr.domain_g0_eq_opening S r
    linarith
  have hdom : M.domain S.E S.hc r .g0 = M.vote_time S.E (M.opening_slot S.hc r) := by
    rw [facts.gr.domain_g0_eq_opening, facts.gr.opening_eq_proposal_time,
      ← facts.sch.Γ_0_eq_proposal_time, facts.sch.Γ_1_eq_vote_time]
  have hinputs := Restated.voterAnchorSourceQ2Inputs_of_namedHeightRegimeFrame_at_sourceOn facts
    S Hs Xb X hf hHs hHsXb hX hXXb ready hframe hactionPrefix hfrontier hactionHor hpAct Q
      hn hselected hsource hQmem hQheight hlo
  intro w hw
  have hwG1 : w ∈ Hs (M.domain S.E S.hc r .g1) := hHs _ _ hg1g0 hw
  have hwX : w ∈ X := hX _ (by linarith) hw
  have hG1 := hinputs.1 w hwG1
  have hG0 : Q.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
      (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) w) := by
    have h := hinputs.2 w (by rw [← hdom]; exact hw)
    rw [setClock_filtered₆₀ facts S] at h
    rw [hdom]
    exact h
  have hPrevQ : NamedBlock.Preceq Prev Q :=
    hframe.sourceAbove p r hpAct hactionPrefix hactionHor n hn Q hQmem hsource hQheight
  have hfloor : Restated.FinalityFloorAtOn M S rho W X Xb H stop Prev.erase := by
    intro v hv k hk Y hYrun hYheight hPrevY
    exact hframe.floor v hv k hk Y hYrun hYheight
      (Restated.namedPreceq_of_runBlock_erase_preceqOn facts Hs Xb hf hframe.prevRun hYrun hPrevY)
  have hbodies := Restated.selectedQ2_body_at_action_and_openingVote_of_floorOn facts
    S Hs Xb X hf hHs hHsXb ready hp hn hselected hQmem hfloor hQheight
      (Proofs.NamedWire.erase_preceq hPrevQ) hactionPrefix hwG1 hwX hlo
  refine ⟨hG1, hG0, ?_⟩
  intro nw hnw
  obtain ⟨st0, hst0, hcore⟩ := actionReadFrom_core₆₀ facts S
    (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) w) r nw hnw
  have hbody : Q ∈
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) w).st.bodies := by
    have h := hbodies.1 nw hnw
    obtain ⟨c, -, st, hst, rfl⟩ := hnw
    rw [facts.nd.mkNode_st, facts.nd.store_with_cache_bodies,
      facts.dt.named_update_confirmation_with_bodies _ _ _ _ _ st hst,
      facts.hd.ModelProperties_setClock_bodies] at h
    exact h
  have hfiltered := hframe.fgRoot_preceq_and_filteredMem facts
    Hs hf hXXb hfrontier hwX hactionPrefix hbody hQheight hPrevQ
  show Q.erase ∈ M.get_filtered_block_tree (M.toHealing nw.st.core).toFG
  rw [hst0, facts.nd.store_with_cache_get_filtered_block_tree,
    facts.dt.update_confirmation_with_toHealing_filtered _ _ _ _ _ _ hcore, setClock_filtered₆₀ facts S]
  exact hfiltered.2

/-- Under the bundle along `W`, if round `r` is ready, `p` and `v` are in the set for `S.a r`, `np`
    and `nv` are node states of their round-`r` action reads along `W` whose FG sources can return
    `some Bn.erase` and `some Cn.erase`, with `Bn` and `Cn` held by them at height `H + 1`, the
    named frame over `X` holds along `W` at `H` up to `stop`, round `r`'s action read is before
    `stop`, the largest `h_max` over `X` in `W stop` is less than `H + 2`, `S.a r` is within the
    horizon, and `lo ≤ opening (r − η_SG)`, then `Bn.erase` and `Cn.erase` are compatible. -/
theorem actionFGSources_compatible_of_namedFrameOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb X : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hX : ∀ t : Int, 0 ≤ t → Hs t ⊆ X) (hXXb : X ⊆ Xb)
    {r : Round} (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho r)
    {p v : V} (hp : p ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)))
    (hv : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)))
    {Bn Cn : NamedBlock V}
    (np : M.N)
    (hnp : np ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) p) r)
    (hB : Restated.Vocabulary.Internal.PhaseGrades.nodeFGSource M S np r ⇢ some Bn.erase)
    (nv : M.N)
    (hnv : nv ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r)
    (hC : Restated.Vocabulary.Internal.PhaseGrades.nodeFGSource M S nv r ⇢ some Cn.erase)
    (hBmem : Bn ∈ np.st.bodies)
    (hCmem : Cn ∈ nv.st.bodies)
    {stop : Nat} {H : Height} {Prev : NamedBlock V} {c0 : Round}
    (hframe : Restated.NamedHeightRegimeFrameOn M S rho W
      (fun t => W (strictEventIndex rho t)) Hs X Xb H stop Prev c0)
    (hBheight : (M.derive_named S.E S.cfg Bn).h = H + 1)
    (hCheight : (M.derive_named S.E S.cfg Cn).h = H + 1)
    (_hPrevB : NamedBlock.Preceq Prev Bn)
    (_hPrevC : NamedBlock.Preceq Prev Cn)
    (hactionPrefix : strictEventIndex rho ((Restated.Vocabulary.Execution.Setup.a M S r)) ≤ stop)
    (hfrontier : (X.sup fun u => (W stop u).st.core.h_max) < H + 2)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon)
    (hlo : lo ≤ M.opening S.E S.hc (r - S.hc.η_SG)) :
    Block.compatible Bn.erase Cn.erase = true := by
  obtain ⟨Qp, hQp, -⟩ := fgSource_cases₆₀p facts S Hs Xb hf np hnp hB
  have hr := Restated.nodeQ2_round_pos_pointwiseOn facts S Hs Xb hf np hnp hQp
  have hgst : lo ≤ M.early S.E S.hc r .g2 :=
    facts.gr.lo_le_early_g2_of_window_start S hr hlo
  have hBsource := actionFGSource_of_nodeFGSource₆₀p facts S hf np hnp hB
  have hCsource := actionFGSource_of_nodeFGSource₆₀p facts S hf nv hnv hC
  exact Restated.actionFGSources_compatible_sameRound_pointwiseOn facts S Hs Xb hf hHs hHsXb
    hf.slashableBound ready hp hv np hnp hB nv hnv hC
    (fun hselected => Restated.sameRoundSourceQ2Retained_of_namedFrameOn facts
      S Hs Xb X hf hHs hHsXb hX hXXb ready hp np hnp hselected hBsource hBmem hframe
        hBheight hactionPrefix hfrontier hhor hgst)
    (fun hselected => Restated.sameRoundSourceQ2Retained_of_namedFrameOn facts
      S Hs Xb X hf hHs hHsXb hX hXXb ready hv nv hnv hselected hCsource hCmem hframe
        hCheight hactionPrefix hfrontier hhor hgst)
    hhor hlo

end

end DecoupledConsensusModel.Sts.Restated
