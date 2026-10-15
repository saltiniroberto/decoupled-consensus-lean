import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bStepConeIter
import Proofs.Claims.Restated.Claim13beRoute3_45
import Proofs.Claims.Restated.Claim13beRoute3_45b
import Proofs.Claims.Restated.Claim13beRoute3_46
import Proofs.Claims.Restated.Claim13beRoute3_47b
import Proofs.Claims.Restated.Claim13beRoute3_48
import Proofs.Claims.Restated.Claim13beRoute3_48b
import Proofs.Claims.Restated.Claim13beRoute3_49
import Proofs.Claims.Restated.Claim13beRoute3_49b
import Proofs.Claims.Restated.Claim13beRoute3_50
import Proofs.Claims.Restated.Claim13beRoute3_50b
import Proofs.Claims.Restated.Claim13beRoute3_51
import Proofs.Claims.Restated.Claim13beRoute3_52
import Proofs.Claims.Restated.Claim13beRoute3_52b
import Proofs.Claims.Restated.Claim13beRoute3_53b
import Proofs.Claims.Restated.Vocabulary_Execution_Acceptance
import Proofs.Claims.Restated.Vocabulary_Execution_ExcludesRefute
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Proofs.Claims.Restated.Vocabulary_Execution_PreparedReadBridge
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_Generic_EvaluationStore
import Proofs.Claims.Restated.Vocabulary_ModelVocabulary_Healing_Schedule
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_Agreement
import Model.Vocabulary.Protocol.Grades
import Proofs.Vocabulary.ModelVocabulary
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeDelivery
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.Records
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Records
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_Interpolation
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_JointHistoryProducers
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_Main
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_ProposalParent
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_RowTrace
import Model.Conditions.Vocabulary_Internal_Invariants
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_BlockAdmission
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreRoots
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_TickBridges
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_Action
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_Alignment
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_42c
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.RunVocabulary
import Model.Conditions.Vocabulary_Internal_Definitions_NamedLifecycle
import Model.Conditions.Vocabulary_Internal_Definitions_NamedOutageEntry
import Model.Conditions.Vocabulary_Internal_Definitions_NamedResult23Statements
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGradeQueries
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Internal_Internal_GradeReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ConfirmationScore
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedHeadReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedActionReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedReceiptCalls
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Node
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Objects
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_ModelVocabulary_Healing_Schedule
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Agreement
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_FinalityFilterRetention
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Proofs.Vocabulary.Protocol.ForkChoice.Views.ProposalCore
import Model.Conditions.Vocabulary_Protocol_Grades_GradeFormsBridge
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Conditions.Vocabulary_Protocol_Grades_ProposalLifecycleCore
import Model.Conditions.Vocabulary_Protocol_Grades_RelativeCrossReader
import Model.Conditions.Vocabulary_Protocol_Handlers_Blocks
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_Handlers_TickBridges
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_54

/-!
# Clean action reads and grades of the next round

Theorems read along the path `W` of a run satisfying `AdmissibleFieldsOn`, over a model
`M : Record.Model V` and its facts, where a clean read is `CleanActionReadForOn` at the worlds
`fun t => W (strictEventIndex rho t)`: a cleanly read `P` is an ancestor of the action blocks of
round `r` and is graded by the readers of round `r + 1`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

open scoped DC

/-! ### Helpers -/

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Proofs.HealingSurface

/-- In a run sorted by key, the worlds strictly before `t` are the worlds before the event of index
    `strictEventIndex rho t`. -/
private theorem stateBeforeTime_eq_strict₅₄ (S : Setup V) (rho : Record.Run V)
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

/-- In a run sorted by key, the world `W (strictEventIndex rho t)` of a path `W` is a world strictly
    before `t`. -/
private theorem mem_stateBeforeTime_along₅₄ {S : Setup V} {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (t : Time) :
    W (strictEventIndex rho t) ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t := by
  rw [stateBeforeTime_eq_strict₅₄ S rho hsorted]
  exact (hW _).1

/-- Along a path `W` of `rho`, `W (m + k)` is among the worlds the events `m` to `m + k - 1` lead to
    from `W m`. -/
private theorem onePath_reach₅₄ {S : Setup V} {rho : Record.Run V}
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

/-- Along a path `W` of `rho`, for `m ≤ n`, `W n` is among the worlds the events `m` to `n - 1` lead
    to from `W m`. -/
private theorem onePath_slice₅₄ {S : Setup V} {rho : Record.Run V}
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) {m n : Nat}
    (hmn : m ≤ n) :
    W n ∈ ((rho.events.drop m).take (n - m)).foldlM (Record.worldStepOf M S) (W m) := by
  have h := onePath_reach₅₄ W hW m (n - m)
  rwa [Nat.add_sub_of_le hmn] at h

/-- Along a path `W`, for `j ≤ n`, `v`'s finalized block in `W j` is an ancestor of its finalized
    block in `W n`. -/
private theorem F_mono_along₅₄ (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (v : V)
    {j n : Nat} (hjn : j ≤ n) : Block.Preceq (W j v).st.core.F (W n v).st.core.F :=
  Restated.Vocabulary.Protocol.stateBefore_F_mono facts S rho v hjn (W j) (hW j).1 (W n)
    (onePath_slice₅₄ W hW hjn)

omit [DecidableEq V] [Fintype V] in
private theorem strict_mono₅₄ (rho : Record.Run V) {t t' : Time} (h : t ≤ t') :
    strictEventIndex rho t ≤ strictEventIndex rho t' :=
  Restated.strict_lengths_mono rho h

/-- A block of the filtered block tree of a store is a descendant of the store's finalized block. -/
private theorem F_preceq_of_mem_filtered₅₄ (facts : Record.Facts M) (st : M.S) {C : Block V}
    (hC : C ∈ M.get_filtered_block_tree (M.toHealing st).toFG) : Block.Preceq st.F C := by
  have h := facts.fc.finalized_preceq_of_mem_get_filtered_block_tree hC
  rwa [facts.sto.Sts_toHealing_F] at h

/-- The round-`r` action read from `before` has a node state on which the grade-2 block read and
    then the SG vote selector each return some value. -/
private theorem exists_actionSG₅₄ (facts : Record.Facts M) (S : Setup V) (before : M.N)
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

/-- If `v` is in the set for `time`, an SG vote signed by `v` among the round-`k` SG votes of the
    grade view of `w`'s core store in `W (strictEventIndex rho time)` is `⟨v, k, some C.root⟩` for
    every block `C` of `v`'s round-`k` action read. -/
private theorem vote_eq_of_mem_gradeView₅₄ (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {w v : V} {time : Time} {k : Round} {z : Protocol.SGVote V}
    (hv : v ∈ Hs time)
    (hz : z ∈ (M.gradeView (M.toHealing (W (strictEventIndex rho time) w).st.core)).sg_votes k)
    (hzidx : z.val_index = v) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S k)) v) k,
      ∀ g, M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ g →
      ∀ C, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) g ⇢ C →
      z = (⟨v, k, some C.root⟩ : Protocol.SGVote V) := by
  have hz' : z ∈ (M.toHealing (W (strictEventIndex rho time) w).st.core).toFG.toSG.sg_votes k := by
    have h := hz
    rw [facts.gr.gradeView_sg_votes] at h
    rw [facts.sto.Sts_toHealing_sg_votes]
    exact h
  exact Restated.honestSGVote_eq_actionSGVoteAt_of_mem_storeBeforeTimeOn facts S Hs Xb hf hHs hv
    hz' hzidx

/-- If `v` is in the set for `time`, an SG vote signed by `v` among the round-`k` SG votes of the
    grade view of `w`'s core store in `W (strictEventIndex rho time)` is of round `k`. -/
private theorem vote_round_of_mem_gradeView₅₄ (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {w v : V} {time : Time} {k : Round} {z : Protocol.SGVote V}
    (hv : v ∈ Hs time)
    (hz : z ∈ (M.gradeView (M.toHealing (W (strictEventIndex rho time) w).st.core)).sg_votes k)
    (hzidx : z.val_index = v) : z.round = k := by
  obtain ⟨n, hn, g, hg, C, hC⟩ :=
    exists_actionSG₅₄ facts S (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S k)) v) k
  rw [vote_eq_of_mem_gradeView₅₄ facts S Hs Xb hf hHs hv hz hzidx n hn g hg C hC]

/-- If `f <$> m` can return `b`, then `m` can return some `a` with `f a = b`. -/
private theorem returns_map_elim₅₄ {α β : Type} (f : α → β) (m : DC.NDRE α) (b : β)
    (h : (f <$> m) ⇢ b) : ∃ a, m ⇢ a ∧ f a = b := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image] at h
  obtain ⟨e, he, hb⟩ := h
  cases e with
  | ok a => exact ⟨a, he, by simpa [Except.map] using hb⟩
  | error err => simp [Except.map] at hb

/-- If `m` can return `a`, then `f <$> m` can return `f a`. -/
private theorem returns_map_intro₅₄ {α β : Type} (f : α → β) (m : DC.NDRE α) (a : α)
    (h : m ⇢ a) : (f <$> m) ⇢ f a := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image]
  exact ⟨_, h, rfl⟩

/-- If `lo ≤ S.a r` and `r < k`, then `lo ≤ early k .g2 − Δ`. -/
theorem lo_le_early_g2_sub_delta_of_action_lt (facts : Record.Facts M) (S : Setup V) {lo : Int}
    {r k : Round} (hlo : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S r)) (hrk : r < k) :
    lo ≤ M.early S.E S.hc k .g2 - S.E.Δ :=
  le_sub_iff_add_le.mpr ((Int.add_le_add_right hlo S.E.Δ).trans
    (facts.gr.action_delta_le_early S S.hc.R_ge_three hrk))

/-- If `0 < X ≤ k` and `lo ≤ opening (X − η_SG)`, then `lo ≤ early k .g2 − Δ`. -/
theorem lo_le_early_g2_sub_delta_of_opening (facts : Record.Facts M) (S : Setup V) {lo : Int}
    {X k : Round} (hX : 0 < X) (hlo : lo ≤ M.opening S.E S.hc (X - S.hc.η_SG)) (hXk : X ≤ k) :
    lo ≤ M.early S.E S.hc k .g2 - S.E.Δ := by
  have hη := S.hc.η_SG_ge_one
  have h1 : M.opening S.E S.hc (X - S.hc.η_SG) ≤ M.opening S.E S.hc (k - 1) :=
    facts.gr.NamedOutageClosure_opening_mono S
      ((Nat.sub_le_sub_left hη X).trans (Nat.sub_le_sub_right hXk 1))
  have h2 := facts.gr.opening_add_le_of_lt S (Nat.sub_lt (lt_of_lt_of_le hX hXk) Nat.one_pos)
  have h3 := facts.gr.opening_sub_five_delta_le_early_g2 S k
  have hΔ := S.E.Δ_pos
  linarith

/-- If `r + 2 ≤ c`, then `r < c - 1`. -/
theorem lt_pred_of_add_two_le_l54 {r c : Nat} (h : r + 2 ≤ c) : r < c - 1 := by
  omega

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- `S.a r + Δ` is at most round `r + 1`'s grade-2 domain time. -/
theorem action_add_delta_le_domain_g2_succ_l54 (facts : Record.Facts M) (S : Setup V) (r : Round) :
    (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ ≤ M.domain S.E S.hc (r + 1) .g2 :=
  (facts.gr.action_delta_le_early S S.hc.R_ge_three (Nat.lt_succ_self r)).trans
    (facts.gr.early_le_domain S (r + 1))

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- If `P` is cleanly read at round `r` along `W`, `w` is in the set for `S.a (r + 1)` and `v` in
    the set for `S.a r + Δ`, then `P` is an ancestor of every block the SG vote selector can return
    on every node state of `v`'s round-`r` action read. -/
theorem cleanActionRead_preceq_actionSGBlockAt_localOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {r : Round} {P : Block V}
    (hclean : Restated.CleanActionReadForOn M S rho Hs r (fun t => W (strictEventIndex rho t)) P)
    {w v : V} (hw : w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (hv : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ)) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r,
      let gc := M.gradeContract n.cache
      let st := M.toHealing n.st.core
      let k := M.round_of S.hc st.s
      ∀ g, M.grade2_block_with gc S.E S.hc st k ⇢ g →
      ∀ C : Block V, M.get_sg_vote_with gc S.E S.hc st k g ⇢ C →
      Block.Preceq P C := by
  intro n hn gc st k g hg C hC
  have hres := hclean.resolved_support w hw v hv n hn g hg C hC
  obtain ⟨b, hb⟩ := facts.gr.head_covers_nonempty
    (M.gradeView (M.toHealing
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r + 1))) w).st.core)).T
    P (some C.root)
  obtain ⟨X, hfind, hcov⟩ := facts.gr.exists_find_of_head_covers b hb (hres.2 b hb)
  have hXmem : X ∈
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r + 1))) w).st.core.T := by
    have h' := Proofs.HealingLemmas.find?_mem hfind
    rw [facts.gr.Sts_gradeView_T] at h'
    exact h'
  have hCmem : C ∈
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).st.core.T :=
    Restated.Vocabulary.Proofs.HealingSurface.actionSGBlockAt_mem_storeBeforeTime facts S rho v r _
      (mem_stateBeforeTime_along₅₄ hf.sorted hf.onePath _) n hn g hg C hC
  obtain ⟨Xn, hXnErase, hXrun⟩ :=
    Restated.runBlock_of_mem_core_T_stateBeforeTimeOn facts S Hs Xb hf (hHsXb _ hw) ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) hXmem
  obtain ⟨Cn, hCnErase, hCrun⟩ :=
    Restated.runBlock_of_mem_core_T_stateBeforeTimeOn facts S Hs Xb hf (hHsXb _ hv) ((Restated.Vocabulary.Execution.Setup.a M S r)) hCmem
  have hroot : X.root = C.root := Proofs.HealingLemmas.find?_root hfind
  have hrootN : Xn.root = Cn.root := by
    rw [← Proofs.NamedWire.erase_root Xn, ← Proofs.NamedWire.erase_root Cn,
      hXnErase, hCnErase, hroot]
  have hXC : Xn = Cn :=
    hf.rootCollisionFree.root_injective Xn Cn
      hXrun hCrun Xn Cn (Or.inl (Proofs.NamedAncestry.named_self Xn))
      (Or.inr (Proofs.NamedAncestry.named_self Cn)) hrootN
  have hXCerase : X = C := by
    calc
      X = Xn.erase := hXnErase.symm
      _ = Cn.erase := congrArg NamedBlock.erase hXC
      _ = C := hCnErase
  rw [hXCerase] at hcov
  exact hcov

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- If every tick has an outcome, `P` is cleanly read at round `r` along `W`, `w` is in the set for
    `dom₂ (r + 1)`, `v` in the set for `S.a r + Δ` and awake at `r`, `w₀` in the set for
    `S.a (r + 1)`, and `lo ≤ S.a r`, then for every block `C` of `v`'s round-`r` action read,
    `⟨v, r, some C.root⟩` is in every outcome of the interpreted inputs of `v` at `w`'s node state
    in `W (strictEventIndex rho (dom₂ (r + 1)))`, and every outcome of its local cover of `P` there
    is `true`. -/
theorem actionSGVoteAt_interpreted_early_of_cleanActionReadOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {r : Round} {P : Block V}
    (hclean : Restated.CleanActionReadForOn M S rho Hs r (fun t => W (strictEventIndex rho t)) P)
    {w v : V} (hw : w ∈ Hs (M.domain S.E S.hc (r + 1) .g2)) (hv : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ))
    {w₀ : V} (hw₀ : w₀ ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (hlo : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S r)) (hA : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick v (Restated.Vocabulary.Execution.Setup.a M S r)) → M.awake_for_grade2 S v (W j v) r) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r,
      let gc := M.gradeContract n.cache
      let st := M.toHealing n.st.core
      let k := M.round_of S.hc st.s
      ∀ g, M.grade2_block_with gc S.E S.hc st k ⇢ g →
      ∀ C : Block V, M.get_sg_vote_with gc S.E S.hc st k g ⇢ C →
      (∀ I, M.interpretedInputs
          (M.gradeView (M.toHealing
            (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) .g2)) w).st.core))
          (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) .g2)) w).st.core.F
          S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) .g2) v ⇢ I →
        (⟨v, r, some C.root⟩ : Protocol.SGVote V) ∈ I) ∧
      ∀ b, M.localCovers
          (M.gradeView (M.toHealing
            (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) .g2)) w).st.core))
          (some C.root) P ⇢ b → b = true := by
  intro n hn gc st k g hg C hC
  have hdeadline : (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ ≤ rho.horizon :=
    (facts.gr.action_add_delta_le_next_Γ_neg1 S r).trans hclean.cutoff_in_horizon
  have hEarly : (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ ≤ M.early S.E S.hc (r + 1) .g2 :=
    facts.gr.action_delta_le_early S S.hc.R_ge_three
      (Nat.lt_succ_self r)
  have hDomLe : (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ ≤ M.domain S.E S.hc (r + 1) .g2 :=
    Restated.action_add_delta_le_domain_g2_succ_l54 facts S r
  have hwΔ : w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ) := hHs _ _ hDomLe hw
  have hmemA := mem_stateBeforeTime_along₅₄ hf.sorted hf.onePath
    (Restated.Vocabulary.Execution.Setup.a M S r)
  obtain ⟨D, hD⟩ := facts.dt.attest_with_nonempty (M.gradeContract n.cache) S.E S.hc (S.node v)
    n.st n.record
  have haD : D.2.2 ∈ Restated.actionAttestationFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) v r :=
    ⟨n, hn, D.1, D.2.1, hD⟩
  have hsg : M.sgVote D.2.2.erase = (⟨v, r, some C.root⟩ : Protocol.SGVote V) :=
    Restated.Vocabulary.Proofs.HealingSurface.sgVote_actionAttestationAt facts S rho v r _ hmemA
      n hn D hD g hg C hC
  have hround : D.2.2.round = r := by
    have h := facts.sto.sgVote_round D.2.2
    rw [hsg] at h
    exact h.symm
  obtain ⟨j', e', hj', hjt', hrow⟩ := Restated.actionAttestationAt_rows_before_deltaOn facts S Hs Xb
    hf hHs r hv hwΔ hlo hdeadline hA D.2.2 haD
  have hrow' : D.2.2 ∈ (W (j' + 1) w).st.sg_rows D.2.2.round := by
    rw [hround]
    exact hrow
  have hearlyEvent : e'.time < M.early S.E S.hc (r + 1) .g2 := hjt'.trans_le hEarly
  have hDomain' : e'.time < M.domain S.E S.hc (r + 1) .g2 :=
    lt_of_lt_of_le hearlyEvent (facts.gr.early_le_domain S (r + 1))
  have hpool' : (⟨v, r, some C.root⟩ : Protocol.SGVote V) ∈
      (M.toHealing (W (j' + 1) w).st.core).toFG.toSG.sg_votes r := by
    rw [facts.sto.Sts_toHealing_sg_votes]
    have hp := facts.sto.pool_view_mem (W (j' + 1) w).st
      (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho (j' + 1) w
        (W (j' + 1)) (hf.onePath (j' + 1)).1).1.1.1.2.2.2.1
      _ hrow'
    rw [hround] at hp
    have himg := Finset.mem_image_of_mem M.sgVote hp
    rw [hsg] at himg
    exact himg
  have huPool := Restated.sgVote_mem_stateBeforeTime_of_postOn facts S Hs Xb hf hj' hDomain' hpool'
  have huD : (⟨v, r, some C.root⟩ : Protocol.SGVote V) ∈
      (M.gradeView (M.toHealing
        (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) .g2)) w).st.core)).sg_votes r := by
    rw [facts.gr.gradeView_sg_votes, ← facts.sto.Sts_toHealing_sg_votes]
    exact huPool
  have hstamp0 := Restated.timestamp_sg_vote_before_of_mem_post_eventOn facts
    S Hs Xb hf hj' hrow' hearlyEvent
  rw [hsg] at hstamp0
  have hstampD := Restated.timestamp_sg_vote_stateBeforeTime_of_postOn facts
    S Hs Xb hf hj' hDomain' hpool'
  have hstamp : occurrenceBefore ((M.gradeView (M.toHealing
      (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) .g2)) w).st.core)).timestamp_sg_vote
      (⟨v, r, some C.root⟩ : Protocol.SGVote V)) (M.early S.E S.hc (r + 1) .g2) = true := by
    rw [facts.gr.gradeView_timestamp_sg_vote]
    change occurrenceBefore ((W (strictEventIndex rho (M.domain S.E S.hc (r + 1) .g2)) w).st.timestamp_sg_vote
      _) _ = true
    rw [hstampD]
    exact hstamp0
  have hwindow : r ∈ M.latest_window S.hc.η_SG (r + 1) := by
    simpa only [Nat.add_sub_cancel] using
      facts.fc.pred_mem_latest_window S.hc.η_SG (r + 1)
        S.hc.η_SG_ge_one (Nat.succ_pos r)
  have hCpre : Block.Preceq P C :=
    Restated.cleanActionRead_preceq_actionSGBlockAt_localOn facts S Hs Xb hf hHsXb hclean hw₀ hv
      n hn g hg C hC
  have hCsource : C ∈
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).st.core.T :=
    Restated.Vocabulary.Proofs.HealingSurface.actionSGBlockAt_mem_storeBeforeTime facts S rho v r _
      hmemA n hn g hg C hC
  have hactiveDom := hclean.active_domain w hw
  have hFP : Block.Preceq
      (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) .g2)) w).st.core.F P :=
    F_preceq_of_mem_filtered₅₄ facts _ hactiveDom
  have hvisible : C ∈ (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) .g2)) w).st.core.T ∧
      stampedBefore (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) .g2)) w).st.core.timestamp_block
        (M.early S.E S.hc (r + 1) .g2) C = true := by
    rcases Restated.block_eq_genesis_or_acceptsBefore_of_mem_storeBeforeTimeOn facts
        S Hs Xb hf v ((Restated.Vocabulary.Execution.Setup.a M S r)) hCsource with
      hgen | ⟨D', i, t, hDerase, hacc, ht⟩
    · rw [hgen]
      exact Restated.genesis_mem_and_stamp_storeBeforeTimeOn facts S Hs Xb hf w
          (M.domain S.E S.hc (r + 1) .g2) (M.early S.E S.hc (r + 1) .g2)
    · have hDpos : 0 < D'.slot := by
        rw [← Proofs.NamedWire.erase_slot]
        exact Nat.zero_lt_of_lt
          (Restated.Vocabulary.Protocol.parent_slot_lt_of_acceptsAt_block facts S W hf.onePath hacc)
      have hvmax : v ∈ Hs (max t lo) :=
        hHs _ _ ((max_le (le_of_lt ht) hlo).trans
          (le_of_lt (lt_add_of_pos_right _ S.E.Δ_pos))) hv
      have hFhist : ∀ j : Nat,
          j ≤ (rho.events.filter (fun e =>
            decide (e.time < (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ))).length →
          Block.Preceq (W j w).st.core.F D'.erase := by
        intro j hj
        have h1 := F_mono_along₅₄ facts S hf.onePath w (hj.trans (strict_mono₅₄ rho hDomLe))
        rw [hDerase]
        exact preceq_trans_Preceq (preceq_trans_Preceq h1 hFP) hCpre
      have hadmitD := Restated.block_admittedBefore_of_accepted_after_cutoffOn facts
        S Hs Xb hf hHs hHsXb hvmax hwΔ hDpos hacc ht hlo rfl hdeadline hFhist
      rw [hDerase] at hadmitD
      have hvisible' := Restated.admittedBefore_mem_and_stamp_atOn facts
        (Gamma := (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ)
        (Gamma' := M.domain S.E S.hc (r + 1) .g2) S Hs Xb hf hadmitD hDomLe
      refine ⟨hvisible'.1, ?_⟩
      have hstampGamma := hvisible'.2
      rw [stampedBefore_eq_occurrenceBefore] at hstampGamma ⊢
      exact occurrenceBefore_mono hEarly hstampGamma
  have hfind : Block.find?
      (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) .g2)) w).st.core.T C.root = some C := by
    apply Proofs.Optimistic.find?_eq_some_of_unique hvisible.1
    intro X hX hroot
    obtain ⟨Xn, hXnErase, hXrun⟩ :=
      Restated.runBlock_of_mem_core_T_stateBeforeTimeOn facts S Hs Xb hf (hHsXb _ hw)
        (M.domain S.E S.hc (r + 1) .g2) hX
    obtain ⟨Cn, hCnErase, hCrun⟩ :=
      Restated.runBlock_of_mem_core_T_stateBeforeTimeOn facts S Hs Xb hf (hHsXb _ hw)
        (M.domain S.E S.hc (r + 1) .g2) hvisible.1
    have hrootN : Xn.root = Cn.root := by
      rw [← Proofs.NamedWire.erase_root Xn, ← Proofs.NamedWire.erase_root Cn,
        hXnErase, hCnErase, hroot]
    have hXC := hf.rootCollisionFree.root_injective
      Xn Cn hXrun hCrun Xn Cn (Or.inl (Proofs.NamedAncestry.named_self Xn))
      (Or.inr (Proofs.NamedAncestry.named_self Cn)) hrootN
    rw [← hXnErase, hXC, hCnErase]
  have hFC : Block.Preceq
      (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) .g2)) w).st.core.F C :=
    preceq_trans_Preceq hFP hCpre
  have hfindGV : Block.find? (M.gradeView (M.toHealing
      (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) .g2)) w).st.core)).T C.root = some C := by
    rw [facts.gr.Sts_gradeView_T]
    exact hfind
  have hblockStamp : stampedBefore (M.gradeView (M.toHealing
      (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) .g2)) w).st.core)).timestamp_block
      (M.early S.E S.hc (r + 1) .g2) C = true := by
    rw [facts.gr.gradeView_timestamp_block]
    exact hvisible.2
  have hbody := facts.gr.bodyReady_of_find (u := (⟨v, r, some C.root⟩ : Protocol.SGVote V))
    rfl hfindGV hblockStamp (compatible_of_cases (Or.inr hFC))
  refine ⟨fun I hI => ?_, fun b hb => facts.gr.localCovers_of_find hfindGV hCpre b hb⟩
  obtain ⟨R, hR⟩ := facts.gr.rawInputs_nonempty (M.gradeView (M.toHealing
      (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) .g2)) w).st.core)) S.hc.η_SG (r + 1)
    (M.early S.E S.hc (r + 1) .g2) v
  obtain ⟨bb, hbb⟩ := facts.gr.bodyReady_nonempty (M.gradeView (M.toHealing
      (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) .g2)) w).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) .g2)) w).st.core.F
    (M.early S.E S.hc (r + 1) .g2) (⟨v, r, some C.root⟩ : Protocol.SGVote V)
  refine (facts.gr.mem_interpretedInputs_iff I hI R hR bb hbb).mpr ⟨?_, hbody bb hbb⟩
  exact facts.gr.mem_rawInputs_of_occurrenceBefore _ S.hc.η_SG (r + 1) r _ v hwindow huD rfl
    hstamp R hR

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- If every tick has an outcome, `P` is cleanly read at round `r` along `W`, `w` and `v` are in the
    set for `dom₂ (r + 1)`, `w₀` is in the set for `S.a (r + 1)`, `lo ≤ S.a r` and `v` is awake at
    `r`, then every outcome of the test whether `v` is positive for `P`, on `w`'s node state in
    `W (strictEventIndex rho (dom₂ (r + 1)))` for round `r + 1`'s grade 2, is `true`. -/
theorem relativePositive_of_cleanActionReadOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {r : Round} {P : Block V}
    (hclean : Restated.CleanActionReadForOn M S rho Hs r (fun t => W (strictEventIndex rho t)) P)
    {w v : V} (hw : w ∈ Hs (M.domain S.E S.hc (r + 1) .g2))
    (hv : v ∈ Hs (M.domain S.E S.hc (r + 1) .g2))
    {w₀ : V} (hw₀ : w₀ ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (hlo : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S r)) (hA : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick v (Restated.Vocabulary.Execution.Setup.a M S r)) → M.awake_for_grade2 S v (W j v) r) :
    ∀ b, M.positive
        (M.gradeView (M.toHealing
          (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) .g2)) w).st.core))
        (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) .g2)) w).st.core.F
        S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) .g2) (M.late S.E S.hc (r + 1) .g2) v P ⇢ b →
      b = true := by
  intro b hb
  have hvΔ : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ) := hHs _ _ (Restated.action_add_delta_le_domain_g2_succ_l54 facts S r) hv
  obtain ⟨n, hn, g, hg, C, hC⟩ := exists_actionSG₅₄ facts S
    (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r
  have hmain := Restated.actionSGVoteAt_interpreted_early_of_cleanActionReadOn facts
    S Hs Xb hf hHs hHsXb hclean hw hvΔ hw₀ hlo hA n hn g hg C hC
  set nD := W (strictEventIndex rho (M.domain S.E S.hc (r + 1) .g2)) w with hnD
  set gv := M.gradeView (M.toHealing nD.st.core) with hgv
  set F := nD.st.core.F with hF
  set ea := M.early S.E S.hc (r + 1) .g2 with hea
  set la := M.late S.E S.hc (r + 1) .g2 with hla
  set u : Protocol.SGVote V := ⟨v, r, some C.root⟩ with hu
  let cov : Option BlockId → Bool := fun k => Classical.choose (facts.gr.head_covers_nonempty gv.T P k)
  have hcov' : ∀ k, M.head_covers gv.T P k ⇢ cov k := fun k =>
    Classical.choose_spec (facts.gr.head_covers_nonempty gv.T P k)
  have hcovU : cov (M.token u).key = true := by
    rw [facts.gr.token_key]
    obtain ⟨lb, hlb⟩ := facts.gr.localCovers_nonempty gv (some C.root) P
    obtain ⟨H, hfH, hPH⟩ := facts.gr.exists_find_of_localCovers lb hlb (hmain.2 lb hlb)
    exact facts.gr.head_covers_of_find hfH hPH (cov _) (hcov' _)
  have hround_le : ∀ (c : Time) (X : Finset (Protocol.Token (Option BlockId))),
      M.readyView gv F S.hc.η_SG (r + 1) c v ⇢ X → ∀ x ∈ X, x.round ≤ r := by
    intro c X hX x hx
    obtain ⟨I, hI⟩ := facts.gr.interpretedInputs_nonempty gv F S.hc.η_SG (r + 1) c v
    obtain ⟨z, hz, rfl⟩ := (facts.gr.mem_readyView_iff X hX I hI).mp hx
    obtain ⟨R, hR⟩ := facts.gr.rawInputs_nonempty gv S.hc.η_SG (r + 1) c v
    obtain ⟨bz, hbz⟩ := facts.gr.bodyReady_nonempty gv F c z
    have hzR := ((facts.gr.mem_interpretedInputs_iff I hI R hR bz hbz).mp hz).1
    obtain ⟨⟨k, hk', hzk⟩, hzidx, -⟩ := facts.gr.rawInputs_mem_window gv S.hc.η_SG (r + 1) c v R hR hzR
    have hklt : k < r + 1 := (facts.fc.window_bounds hk').2
    have hzround : z.round = k :=
      vote_round_of_mem_gradeView₅₄ facts S Hs Xb hf hHs hv hzk hzidx
    rw [facts.gr.token_round, hzround]
    exact Nat.le_of_lt_succ hklt
  obtain ⟨Re, hRe⟩ := facts.gr.readyView_nonempty gv F S.hc.η_SG (r + 1) ea v
  obtain ⟨I, hI⟩ := facts.gr.interpretedInputs_nonempty gv F S.hc.η_SG (r + 1) ea v
  have hmem : M.token u ∈ Re := (facts.gr.mem_readyView_iff Re hRe I hI).mpr ⟨u, hmain.1 I hI, rfl⟩
  have hlatest : ∀ x ∈ Re, x.round ≤ (M.token u).round := by
    intro x hx
    rw [facts.gr.token_round]
    exact hround_le ea Re hRe x hx
  obtain ⟨Wv, hWv⟩ := facts.gr.rawView_nonempty gv S.hc.η_SG (r + 1) la v
  have hclean' : ∀ x ∈ Wv, ∀ y ∈ Wv, (M.token u).round ≤ x.round → x.round = y.round →
      x.key = y.key := by
    intro x hx y hy _ hxy
    obtain ⟨Y, hY⟩ := facts.gr.rawInputs_nonempty gv S.hc.η_SG (r + 1) la v
    obtain ⟨xv, hxv, rfl⟩ := (facts.gr.mem_rawView_iff gv S.hc.η_SG (r + 1) la v x Wv hWv Y hY).mp hx
    obtain ⟨yv, hyv, rfl⟩ := (facts.gr.mem_rawView_iff gv S.hc.η_SG (r + 1) la v y Wv hWv Y hY).mp hy
    obtain ⟨⟨kx, -, hxpool⟩, hxidx, -⟩ := facts.gr.rawInputs_mem_window gv S.hc.η_SG (r + 1) la v Y hY hxv
    obtain ⟨⟨ky, -, hypool⟩, hyidx, -⟩ := facts.gr.rawInputs_mem_window gv S.hc.η_SG (r + 1) la v Y hY hyv
    have hxround := vote_round_of_mem_gradeView₅₄ facts S Hs Xb hf hHs hv hxpool hxidx
    have hyround := vote_round_of_mem_gradeView₅₄ facts S Hs Xb hf hHs hv hypool hyidx
    rw [facts.gr.token_round, facts.gr.token_round] at hxy
    have hkyx : ky = kx := hyround.symm.trans (hxy.symm.trans hxround)
    rw [hkyx] at hypool
    obtain ⟨n', hn', g', hg', C', hC'⟩ := exists_actionSG₅₄ facts S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S kx)) v) kx
    have hxe := vote_eq_of_mem_gradeView₅₄ facts S Hs Xb hf hHs hv hxpool hxidx n' hn' g' hg' C' hC'
    have hye := vote_eq_of_mem_gradeView₅₄ facts S Hs Xb hf hHs hv hypool hyidx n' hn' g' hg' C' hC'
    exact congrArg (fun z => (M.token z).key) (hxe.trans hye.symm)
  obtain ⟨Rl, hRl⟩ := facts.gr.readyView_nonempty gv F S.hc.η_SG (r + 1) la v
  have hlater : ∀ x ∈ Rl, (M.token u).round < x.round → cov x.key = true := by
    intro x hx hlt
    rw [facts.gr.token_round] at hlt
    exact absurd (hround_le la Rl hRl x hx) (Nat.not_le_of_lt hlt)
  exact facts.gr.positive_of_conditions gv F S.hc.η_SG (r + 1) ea la v P (M.token u) Re hRe hmem
    hlatest cov hcov' hcovU Wv hWv hclean' Rl hRl hlater b hb

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- If every tick has an outcome, `P` is cleanly read at round `r` along `W`, `w` is in the set for
    `dom₂ (r + 1)`, `w₀` in the set for `S.a (r + 1)`, `lo ≤ S.a r`, every member of the set for
    `S.a r + Δ` is awake at `r`, and the test whether `v` opposes `P` on `w`'s node state in
    `W (strictEventIndex rho (dom₂ (r + 1)))` can return `true`, then `v` is not in the set for
    `dom₂ (r + 1)`. -/
theorem relativeOpposingNotHonest_of_cleanActionReadOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {r : Round} {P : Block V}
    (hclean : Restated.CleanActionReadForOn M S rho Hs r (fun t => W (strictEventIndex rho t)) P)
    {w v : V} (hw : w ∈ Hs (M.domain S.E S.hc (r + 1) .g2))
    (hopp : M.opposing
        (M.gradeView (M.toHealing
          (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) .g2)) w).st.core))
        (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) .g2)) w).st.core.F
        S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) .g2) (M.late S.E S.hc (r + 1) .g2) v P ⇢ true)
    {w₀ : V} (hw₀ : w₀ ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (hlo : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S r)) (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S r)) → M.awake_for_grade2 S u (W j u) r) :
    v ∉ Hs (M.domain S.E S.hc (r + 1) .g2) := by
  intro hv
  have hvΔ : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ) := hHs _ _ (Restated.action_add_delta_le_domain_g2_succ_l54 facts S r) hv
  obtain ⟨n, hn, g, hg, C, hC⟩ := exists_actionSG₅₄ facts S
    (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r
  have hmain := Restated.actionSGVoteAt_interpreted_early_of_cleanActionReadOn facts
    S Hs Xb hf hHs hHsXb hclean hw hvΔ hw₀ hlo (hA v hvΔ) n hn g hg C hC
  set nD := W (strictEventIndex rho (M.domain S.E S.hc (r + 1) .g2)) w with hnD
  set gv := M.gradeView (M.toHealing nD.st.core) with hgv
  set F := nD.st.core.F with hF
  set ea := M.early S.E S.hc (r + 1) .g2 with hea
  set la := M.late S.E S.hc (r + 1) .g2 with hla
  set u : Protocol.SGVote V := ⟨v, r, some C.root⟩ with hu
  let cov : Option BlockId → Bool := fun k => Classical.choose (facts.gr.head_covers_nonempty gv.T P k)
  have hcov' : ∀ k, M.head_covers gv.T P k ⇢ cov k := fun k =>
    Classical.choose_spec (facts.gr.head_covers_nonempty gv.T P k)
  have hcovU : cov (M.token u).key = true := by
    rw [facts.gr.token_key]
    obtain ⟨lb, hlb⟩ := facts.gr.localCovers_nonempty gv (some C.root) P
    obtain ⟨H, hfH, hPH⟩ := facts.gr.exists_find_of_localCovers lb hlb (hmain.2 lb hlb)
    exact facts.gr.head_covers_of_find hfH hPH (cov _) (hcov' _)
  obtain ⟨Re, hRe⟩ := facts.gr.readyView_nonempty gv F S.hc.η_SG (r + 1) ea v
  obtain ⟨I, hI⟩ := facts.gr.interpretedInputs_nonempty gv F S.hc.η_SG (r + 1) ea v
  have hmem : M.token u ∈ Re := (facts.gr.mem_readyView_iff Re hRe I hI).mpr ⟨u, hmain.1 I hI, rfl⟩
  obtain ⟨Rl, hRl⟩ := facts.gr.readyView_nonempty gv F S.hc.η_SG (r + 1) la v
  obtain ⟨Wv, hWv⟩ := facts.gr.rawView_nonempty gv S.hc.η_SG (r + 1) la v
  rcases facts.gr.conditions_of_opposing gv F S.hc.η_SG (r + 1) ea la v P true hopp rfl Re hRe Rl hRl
      Wv hWv cov hcov' with ⟨x, hx, hguard, hnot⟩ | ⟨x, hx, y, hy, _hguard, hround, hkey⟩
  · obtain ⟨Il, hIl⟩ := facts.gr.interpretedInputs_nonempty gv F S.hc.η_SG (r + 1) la v
    obtain ⟨z, hz, rfl⟩ := (facts.gr.mem_readyView_iff Rl hRl Il hIl).mp hx
    obtain ⟨R, hR⟩ := facts.gr.rawInputs_nonempty gv S.hc.η_SG (r + 1) la v
    obtain ⟨bz, hbz⟩ := facts.gr.bodyReady_nonempty gv F la z
    have hzR := ((facts.gr.mem_interpretedInputs_iff Il hIl R hR bz hbz).mp hz).1
    obtain ⟨⟨k, hk', hzk⟩, hzidx, -⟩ := facts.gr.rawInputs_mem_window gv S.hc.η_SG (r + 1) la v R hR hzR
    have hklt : k < r + 1 := (facts.fc.window_bounds hk').2
    have hzround : z.round = k :=
      vote_round_of_mem_gradeView₅₄ facts S Hs Xb hf hHs hv hzk hzidx
    have hmax := hguard (M.token u) hmem
    rw [facts.gr.token_round, facts.gr.token_round, hzround] at hmax
    have hkEq : k = r := Nat.le_antisymm (Nat.le_of_lt_succ hklt) hmax
    rw [hkEq] at hzk
    have hzu : z = u := vote_eq_of_mem_gradeView₅₄ facts S Hs Xb hf hHs hv hzk hzidx n hn g hg C hC
    apply hnot
    rw [hzu]
    exact hcovU
  · obtain ⟨Y, hY⟩ := facts.gr.rawInputs_nonempty gv S.hc.η_SG (r + 1) la v
    obtain ⟨xv, hxv, rfl⟩ := (facts.gr.mem_rawView_iff gv S.hc.η_SG (r + 1) la v x Wv hWv Y hY).mp hx
    obtain ⟨yv, hyv, rfl⟩ := (facts.gr.mem_rawView_iff gv S.hc.η_SG (r + 1) la v y Wv hWv Y hY).mp hy
    obtain ⟨⟨kx, -, hxpool⟩, hxidx, -⟩ := facts.gr.rawInputs_mem_window gv S.hc.η_SG (r + 1) la v Y hY hxv
    obtain ⟨⟨ky, -, hypool⟩, hyidx, -⟩ := facts.gr.rawInputs_mem_window gv S.hc.η_SG (r + 1) la v Y hY hyv
    have hxround := vote_round_of_mem_gradeView₅₄ facts S Hs Xb hf hHs hv hxpool hxidx
    have hyround := vote_round_of_mem_gradeView₅₄ facts S Hs Xb hf hHs hv hypool hyidx
    rw [facts.gr.token_round, facts.gr.token_round] at hround
    have hkyx : ky = kx := hyround.symm.trans (hround.symm.trans hxround)
    rw [hkyx] at hypool
    obtain ⟨n', hn', g', hg', C', hC'⟩ := exists_actionSG₅₄ facts S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S kx)) v) kx
    have hxe := vote_eq_of_mem_gradeView₅₄ facts S Hs Xb hf hHs hv hxpool hxidx n' hn' g' hg' C' hC'
    have hye := vote_eq_of_mem_gradeView₅₄ facts S Hs Xb hf hHs hv hypool hyidx n' hn' g' hg' C' hC'
    exact hkey (congrArg (fun z => (M.token z).key) (hxe.trans hye.symm))

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- If the weight outside `X` together with the stale historical voters of `r` is less than the
    weight of the round-`(r − 1)` voters inside `X` along `W`, every outcome of the positive test of
    such a voter for `C` is `true`, and every validator whose opposing test of `C` can return `true`
    is outside `X` or a stale historical voter, then every outcome of the grade test of `C` is
    `true`. -/
theorem phaseGrade_of_gradeFormingMajorityOn (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N) (Hs : Int → Finset V) (X : Finset V)
    (r : Round) (gv : M.GV) (F C : Block V) (ea la : Time)
    (hmajority : Restated.GradeFormingMajorityOn M S rho W Hs X r)
    (hpositive : ∀ v ∈ Restated.honestRoundVotersOn M S rho W Hs (r - 1) ∩ X,
      ∀ b, M.positive gv F S.hc.η_SG r ea la v C ⇢ b → b = true)
    (hopposing : ∀ v, M.opposing gv F S.hc.η_SG r ea la v C ⇢ true →
      v ∈ (Finset.univ \ X) ∪ Restated.staleHistoricalVotersOn M S rho W Hs r) :
    ∀ g, M.gradeBool S.E gv F S.hc.η_SG r ea la C ⇢ g → g = true := by
  intro g hg
  let pos : V → Bool := fun v =>
    Classical.choose (facts.gr.positive_nonempty gv F S.hc.η_SG r ea la v C)
  have hpos : ∀ v, M.positive gv F S.hc.η_SG r ea la v C ⇢ pos v := fun v =>
    Classical.choose_spec (facts.gr.positive_nonempty gv F S.hc.η_SG r ea la v C)
  let opp : V → Bool := fun v =>
    Classical.choose (facts.gr.opposing_nonempty gv F S.hc.η_SG r ea la v C)
  have hopp : ∀ v, M.opposing gv F S.hc.η_SG r ea la v C ⇢ opp v := fun v =>
    Classical.choose_spec (facts.gr.opposing_nonempty gv F S.hc.η_SG r ea la v C)
  refine facts.gr.gradeBool_of_weight_lt S.E gv F S.hc.η_SG r ea la C opp hopp pos hpos ?_ g hg
  have hleft := S.E.electorate.weightOf_mono
    (show (Finset.univ.filter fun u => opp u = true) ⊆
        (Finset.univ \ X) ∪ Restated.staleHistoricalVotersOn M S rho W Hs r from
      fun u hu => hopposing u (by
        have h := hopp u
        rw [(Finset.mem_filter.mp hu).2] at h
        exact h))
  have hright := S.E.electorate.weightOf_mono
    (show Restated.honestRoundVotersOn M S rho W Hs (r - 1) ∩ X ⊆
        Finset.univ.filter fun u => pos u = true from
      fun u hu => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpositive u hu (pos u) (hpos u)⟩)
  exact hleft.trans_lt (hmajority.trans_le hright)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- If `P` is cleanly read at round `r` along `W` and `w` is in the set for `dom₂ (r + 1)`, then `P`
    is in the filtered tree of `w`'s node state in `W (strictEventIndex rho (dom₂ (r + 1)))`. -/
theorem relativeG2Active_of_cleanActionReadOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (_hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {r : Round} {P : Block V}
    (hclean : Restated.CleanActionReadForOn M S rho Hs r (fun t => W (strictEventIndex rho t)) P)
    {w : V} (hw : w ∈ Hs (M.domain S.E S.hc (r + 1) .g2)) :
    P ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
      (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) .g2)) w) :=
  hclean.active_domain w hw

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- If every tick has an outcome, `P` is cleanly read at round `r` along `W`, the set for
    `S.a (r + 1)` has a member, `lo ≤ S.a r`, and every member of the set for `S.a r + Δ` is awake
    at `r`, then at the node states of `W (strictEventIndex rho (dom₂ (r + 1)))`, `P` is in the
    filtered tree of every member of the set for `dom₂ (r + 1)`, each member counts every member as
    positive for `P`, and a validator a member may count as opposing `P` is outside that set. -/
theorem relativeG2Support_of_cleanActionReadOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {r : Round} {P : Block V}
    (hclean : Restated.CleanActionReadForOn M S rho Hs r (fun t => W (strictEventIndex rho t)) P)
    (hne : (Hs ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)))).Nonempty)
    (hlo : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S r)) (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S r)) → M.awake_for_grade2 S u (W j u) r) :
    (∀ w ∈ Hs (M.domain S.E S.hc (r + 1) .g2),
      P ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
        (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) .g2)) w)) ∧
    (∀ w ∈ Hs (M.domain S.E S.hc (r + 1) .g2), ∀ v ∈ Hs (M.domain S.E S.hc (r + 1) .g2),
      ∀ b, M.positive
          (M.gradeView (M.toHealing
            (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) .g2)) w).st.core))
          (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) .g2)) w).st.core.F
          S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) .g2) (M.late S.E S.hc (r + 1) .g2) v P ⇢ b →
        b = true) ∧
    (∀ w ∈ Hs (M.domain S.E S.hc (r + 1) .g2), ∀ v : V,
      M.opposing
          (M.gradeView (M.toHealing
            (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) .g2)) w).st.core))
          (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) .g2)) w).st.core.F
          S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) .g2) (M.late S.E S.hc (r + 1) .g2) v P ⇢ true →
        v ∉ Hs (M.domain S.E S.hc (r + 1) .g2)) := by
  obtain ⟨w₀, hw₀⟩ := hne
  refine ⟨?_, ?_, ?_⟩
  · exact fun w hw => Restated.relativeG2Active_of_cleanActionReadOn facts S Hs Xb hf hclean hw
  · intro w hw v hv
    exact Restated.relativePositive_of_cleanActionReadOn facts S Hs Xb hf hHs hHsXb hclean hw hv
      hw₀ hlo (hA v (hHs _ _ (Restated.action_add_delta_le_domain_g2_succ_l54 facts S r) hv))
  · intro w hw v hopp
    exact Restated.relativeOpposingNotHonest_of_cleanActionReadOn facts S Hs Xb hf hHs hHsXb
      hclean hw hopp hw₀ hlo hA

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- If every tick has an outcome, the set has an honest weight majority at every time up to the
    horizon, `P` is cleanly read at round `r` along `W`, the set for `S.a (r + 1)` has a member,
    `lo ≤ S.a r`, and every member of the set for `S.a r + Δ` is awake at `r`, then every member of
    the set for `dom₂ (r + 1)` has `P` in the filtered tree of its node state in
    `W (strictEventIndex rho (dom₂ (r + 1)))` and every outcome of the grade-2 store grade of `P` at
    round `r + 1` there is `true`. -/
theorem namedGradeFormsAt_of_cleanActionReadOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hmajority : HonestWeightMajorityOn S rho Hs)
    {r : Round} {P : Block V}
    (hclean : Restated.CleanActionReadForOn M S rho Hs r (fun t => W (strictEventIndex rho t)) P)
    (hne : (Hs ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)))).Nonempty)
    (hlo : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S r)) (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S r)) → M.awake_for_grade2 S u (W j u) r) :
    ∀ v ∈ Hs (M.domain S.E S.hc (r + 1) .g2),
      P ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) .g2)) v) ∧
        ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
          (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) .g2)) v).st (r + 1) .g2 P ⇢ b →
          b = true := by
  have hdomHor : M.domain S.E S.hc (r + 1) .g2 ≤ rho.horizon := by
    rw [← facts.gr.gammaNeg1_eq_domain_g2_succ S r]
    exact hclean.cutoff_in_horizon
  have hsup := Restated.relativeG2Support_of_cleanActionReadOn facts S Hs Xb hf hHs hHsXb
    hclean hne hlo hA
  intro w hw
  refine ⟨hsup.1 w hw, ?_⟩
  intro b hb
  set nD := W (strictEventIndex rho (M.domain S.E S.hc (r + 1) .g2)) w with hnD
  let pos : V → Bool := fun v => Classical.choose (facts.gr.positive_nonempty
    (M.gradeView (M.toHealing nD.st.core)) nD.st.core.F S.hc.η_SG (r + 1)
    (M.early S.E S.hc (r + 1) .g2) (M.late S.E S.hc (r + 1) .g2) v P)
  have hpos : ∀ v, M.positive (M.gradeView (M.toHealing nD.st.core)) nD.st.core.F S.hc.η_SG
      (r + 1) (M.early S.E S.hc (r + 1) .g2) (M.late S.E S.hc (r + 1) .g2) v P ⇢ pos v := fun v =>
    Classical.choose_spec (facts.gr.positive_nonempty
      (M.gradeView (M.toHealing nD.st.core)) nD.st.core.F S.hc.η_SG (r + 1)
      (M.early S.E S.hc (r + 1) .g2) (M.late S.E S.hc (r + 1) .g2) v P)
  let opp : V → Bool := fun v => Classical.choose (facts.gr.opposing_nonempty
    (M.gradeView (M.toHealing nD.st.core)) nD.st.core.F S.hc.η_SG (r + 1)
    (M.early S.E S.hc (r + 1) .g2) (M.late S.E S.hc (r + 1) .g2) v P)
  have hopp : ∀ v, M.opposing (M.gradeView (M.toHealing nD.st.core)) nD.st.core.F S.hc.η_SG
      (r + 1) (M.early S.E S.hc (r + 1) .g2) (M.late S.E S.hc (r + 1) .g2) v P ⇢ opp v := fun v =>
    Classical.choose_spec (facts.gr.opposing_nonempty
      (M.gradeView (M.toHealing nD.st.core)) nD.st.core.F S.hc.η_SG (r + 1)
      (M.early S.E S.hc (r + 1) .g2) (M.late S.E S.hc (r + 1) .g2) v P)
  exact facts.gr.phaseGrade_of_honestPositiveSupport S.E (M.gradeView (M.toHealing nD.st.core))
    nD.st.core.F (Hs (M.domain S.E S.hc (r + 1) .g2)) S.hc.η_SG (r + 1)
    (M.early S.E S.hc (r + 1) .g2) (M.late S.E S.hc (r + 1) .g2) P pos hpos opp hopp
    (hmajority _ hdomHor) (fun v hv => hsup.2.1 w hw v hv (pos v) (hpos v))
    (fun v hv hvX => hsup.2.2 w hw v (hv ▸ hopp v) hvX) b hb

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- The conclusion of `namedGradeFormsAt_of_cleanActionReadOn`, from the hypothesis that `P` is an
    ancestor of every round-`r` action carrier of the set for `S.a r` computed from
    `W (strictEventIndex rho (S.a r))` and is in the filtered tree of every member's healing store
    at `S.a (r + 1)` and node state at `dom₂ (r + 1)`, with `S.E.t_GST ≤ S.a r` and round `r + 1`'s
    earliest grade cutoff inside the horizon, in place of a clean read. -/
theorem namedGradeFormsAt_succ_of_actionCarriersCover_and_next_activeOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hmajority : HonestWeightMajorityOn S rho Hs)
    {r : Round} {P : Block V}
    (hcover : Restated.ActionCarriersCoverOn M S rho Hs r P
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r))))
    (hpost : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S r))
    (hcut : Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (r + 1) ≤ rho.horizon)
    (hactive : ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))),
      P ∈ M.get_filtered_block_tree
        (M.toHealing
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r + 1))) w).st.core).toFG)
    (hactiveDomain : ∀ w ∈ Hs (M.domain S.E S.hc (r + 1) .g2),
      P ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
        (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) .g2)) w))
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S r)) → M.awake_for_grade2 S u (W j u) r)
    (hlo : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S r))
    (hne : (Hs ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)))).Nonempty) :
    ∀ v ∈ Hs (M.domain S.E S.hc (r + 1) .g2),
      P ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) .g2)) v) ∧
        ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
          (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) .g2)) v).st (r + 1) .g2 P ⇢ b →
          b = true := by
  have hclean := Restated.cleanActionReadFor_of_actionCarriersCover_and_next_activeOn facts
    S Hs Xb hf hHs hHsXb hcover hpost hcut hactive hactiveDomain hA hlo
  exact Restated.namedGradeFormsAt_of_cleanActionReadOn facts S Hs Xb hf hHs hHsXb hmajority
    hclean hne hlo hA

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- The conclusion of `namedGradeFormsAt_succ_of_actionCarriersCover_and_next_activeOn`, with the
    carrier hypothesis replaced by: `F` is an ancestor of the FG root of every node state of every
    member's round-`r` action store. -/
theorem namedGradeFormsAt_succ_of_fgRootFloorOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hmajority : HonestWeightMajorityOn S rho Hs)
    {r : Round} {P F : Block V}
    (hfloor : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)),
      ∀ n ∈ Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt M S rho v r,
        Block.Preceq F (M.get_fg_root (M.toHealing n.st.core).toFG))
    (hpost : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S r))
    (hcut : Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (r + 1) ≤ rho.horizon)
    (hactive : ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))),
      F ∈ M.get_filtered_block_tree
        (M.toHealing
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r + 1))) w).st.core).toFG)
    (hactiveDomain : ∀ w ∈ Hs (M.domain S.E S.hc (r + 1) .g2),
      F ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
        (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) .g2)) w))
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S r)) → M.awake_for_grade2 S u (W j u) r)
    (hlo : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S r))
    (hne : (Hs ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)))).Nonempty) :
    ∀ v ∈ Hs (M.domain S.E S.hc (r + 1) .g2),
      F ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) .g2)) v) ∧
        ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
          (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) .g2)) v).st (r + 1) .g2 F ⇢ b →
          b = true :=
  Restated.namedGradeFormsAt_succ_of_actionCarriersCover_and_next_activeOn facts
    S Hs Xb hf hHs hHsXb hmajority
    (Restated.actionCarriersCover_of_fgRootFloorOn facts S rho Hs hfloor _
      (mem_stateBeforeTime_along₅₄ hf.sorted hf.onePath _))
    hpost hcut hactive hactiveDomain hA hlo hne

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- If `1 ≤ c`, the relative carrier window of round `c - 1` holds at grade 1 along `W`, the
    grade-forming majority of `c` holds with counted set `X` inside the set for `c`'s grade-1 domain
    time, `v` is in that set, and the grade-1 store grade of `B` at round `c` on `v`'s store in
    `W (strictEventIndex rho (dom₁ c))` can return `true`, then some member `u` of the set for
    `S.a (c - 1)` has `B` as an ancestor of every block of its round-`(c - 1)` action read. -/
theorem namedG1At_preceq_honestPreviousActionCarrierOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb X : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {c : Round} (hc : 1 ≤ c)
    (hwindow : Restated.RelativeCarrierWindowAtOn M S rho W
      (fun t => W (strictEventIndex rho t)) Hs (c - 1)
      DecoupledConsensusModel.Protocol.Phase.g1)
    (hmajority : Restated.GradeFormingMajorityOn M S rho W Hs X c)
    (hX : X ⊆ Hs (M.domain S.E S.hc c .g1))
    {v : V} (hv : v ∈ Hs (M.domain S.E S.hc c .g1))
    {B : Block V}
    (hG1 : Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
      (W (strictEventIndex rho (M.domain S.E S.hc c .g1)) v).st c .g1 B ⇢ true) :
    ∃ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (c - 1))),
      ∀ nr ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (c - 1))) u) (c - 1),
        let gc := M.gradeContract nr.cache
        let st := M.toHealing nr.st.core
        let kk := M.round_of S.hc st.s
        ∀ A2, M.grade2_block_with gc S.E S.hc st kk ⇢ A2 →
        ∀ Bk, M.get_sg_vote_with gc S.E S.hc st kk A2 ⇢ Bk →
        Block.Preceq B Bk := by
  have hpredSucc : c - 1 + 1 = c := Nat.sub_add_cancel hc
  have hmaj : Restated.GradeFormingMajorityOn M S rho W Hs X (c - 1 + 1) := by
    rw [hpredSucc]
    exact hmajority
  have hX' : X ⊆ Hs (M.domain S.E S.hc (c - 1 + 1) .g1) := by
    rw [hpredSucc]
    exact hX
  have hv' : v ∈ Hs (M.domain S.E S.hc (c - 1 + 1) .g1) := by
    rw [hpredSucc]
    exact hv
  have hgrade : M.gradeBool S.E
      (M.gradeView (M.toHealing
        (W (strictEventIndex rho (M.domain S.E S.hc (c - 1 + 1) .g1)) v).st.core))
      (W (strictEventIndex rho (M.domain S.E S.hc (c - 1 + 1) .g1)) v).st.core.F
      S.hc.η_SG (c - 1 + 1)
      (M.early S.E S.hc (c - 1 + 1) .g1)
      (M.late S.E S.hc (c - 1 + 1) .g1) B ⇢ true := by
    rw [hpredSucc]
    exact hG1
  obtain ⟨u, hu, hBu⟩ :=
    Restated.relativeGrade_has_roundCarrierOn facts S Hs Xb X hf hHs hwindow hmaj hX' hv' hgrade
  exact ⟨u, ((Restated.honestRoundVoters_iffOn facts S rho W hf.onePath Hs u (c - 1)).mp hu).1, hBu⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- If the Q2 read of a node state `n` of `v`'s round-`c` action read along `W` can return `some Q`,
    then some block `raw` with `Q` as an ancestor has every outcome of its grade-2 store grade at
    round `c` on `v`'s store in `W (strictEventIndex rho (dom₂ c))` equal to `true`. -/
theorem namedG2At_freezeRoot_of_nodeQ2On (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} {c : Round} {Q : Block V}
    (n : M.N)
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v) c)
    (hQ : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n c ⇢ some Q) :
    ∃ raw : Block V,
      (∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
        (W (strictEventIndex rho (M.domain S.E S.hc c .g2)) v).st c .g2 raw ⇢ b → b = true) ∧
      Block.Preceq Q raw := by
  obtain ⟨cc, hcc, st', hst', rfl⟩ := hn
  unfold Restated.Vocabulary.Internal.PhaseGrades.nodeQ2
    Restated.Vocabulary.Internal.PhaseGrades.nodeRead at hQ
  obtain ⟨G, hG, hGQ⟩ := returns_map_elim₅₄ _ _ _ hQ
  obtain ⟨x, hx⟩ := facts.dt.grade2_block_with_nonempty
    (M.gradeContract (M.mkNode st' (W (strictEventIndex rho
      (Restated.Vocabulary.Execution.Setup.a M S c)) v).record cc).cache) S.E S.hc
    (M.toHealing (M.mkNode st' (W (strictEventIndex rho
      (Restated.Vocabulary.Execution.Setup.a M S c)) v).record cc).st.core) c
  have hxQ : x = some Q :=
    (facts.dt.grade2_block_with_eq_read_Q2 _ S.E S.hc _ c G hG x hx).trans hGQ
  rw [hxQ] at hx
  obtain ⟨j, raw, -, hj, hfreeze, hQraw⟩ :=
    facts.grRun.q2_capture_at_action_read_along S rho W hf.onePath
      (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v c Q cc hcc st' hst' hx
  refine ⟨raw, ?_, hQraw⟩
  intro b hb
  have hjSt : (W j v).st =
      (W (strictEventIndex rho (M.domain S.E S.hc c Phase.g2)) v).st := by
    rcases Restated.stateBefore_tick_eq_stateBeforeTimeOn facts S Hs Xb hf hj with h | h
    · rw [h]
    · rw [h, (facts.nd.wake_st_record _).1]
  rw [← hjSt] at hb
  obtain ⟨fr, hfr⟩ := facts.gr.freezeRoot_nonempty S.E (M.gradeView (M.toHealing (W j v).st.core))
    (W j v).st.core.F S.hc.η_SG c (M.early S.E S.hc c .g2) (M.late S.E S.hc c .g2)
  exact facts.gr.gradeBool_of_freezeRoot_eq_some fr hfr (hfreeze fr hfr) b hb

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- If every tick has an outcome, `SlashableBoundOn` holds, `0 < c`, `lo ≤ early c .g2`,
    `lo ≤ opening (c − η_SG)`, `v` is in the set for `dom₂ c` and `w` in the set for `dom₁ c`, `w`'s
    finalized block in `W (strictEventIndex rho (dom₁ c))` is an ancestor of `Q`, and the grade-2
    store grade of `Q` at round `c` on `v`'s store in `W (strictEventIndex rho (dom₂ c))` can return
    `true`, then every outcome of the grade-1 store grade of `Q` at round `c` on `w`'s store there
    is `true`. -/
theorem namedG1At_of_namedG2At_finalizedPreceqOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hsb : Restated.SlashableBoundOn M S rho W Xb)
    {c : Round} (hc : 0 < c)
    (hgst : lo ≤ M.early S.E S.hc c .g2)
    (hhor : M.domain S.E S.hc c .g0 ≤ rho.horizon)
    {v w : V} (hv : v ∈ Hs (M.domain S.E S.hc c .g2))
    (hw : w ∈ Hs (M.domain S.E S.hc c .g1)) {Q : Block V}
    (hFQ : Block.Preceq
      (W (strictEventIndex rho (M.domain S.E S.hc c .g1)) w).st.core.F Q)
    (hG2 : Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
      (W (strictEventIndex rho (M.domain S.E S.hc c .g2)) v).st c .g2 Q ⇢ true)
    (hlo : lo ≤ M.opening S.E S.hc (c - S.hc.η_SG)) :
    ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
      (W (strictEventIndex rho (M.domain S.E S.hc c .g1)) w).st c .g1 Q ⇢ b → b = true := by
  have hbelow := Restated.crossReaderFinalizedBelow_of_finalitySafety_and_relayOn facts
    S Hs Xb hf hHs hHsXb hsb hgst hhor hv hw (B := Q) (by
      intro sender u root H I _hI _hu cc hcc hct hconf hfind
      rw [hconf] at hcc
      exact preceq_trans_Preceq hFQ (facts.gr.preceq_of_localCovers_of_find cc hcc hct hfind))
  have guard := Restated.crossReaderBodyReadyGuard_of_finalizedBelowOn facts
    S Hs Xb hf hHs hHsXb hc hgst hhor hv hw hbelow
  exact Restated.storeGrade_g1_of_storeGrade_g2_cross_readerOn facts S rho Hs Xb hf hHs hHsXb
    c hlo hhor v w hv hw Q hG2 guard

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- For `t ≤ t'`, the finalized block of `v`'s core store in `W (strictEventIndex rho t)` is an
    ancestor of the one in `W (strictEventIndex rho t')`. -/
theorem seedRel_stateBeforeTime_F_monoOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo) (v : V)
    {t t' : Time} (htt' : t ≤ t') :
    Block.Preceq (W (strictEventIndex rho t) v).st.core.F
      (W (strictEventIndex rho t') v).st.core.F :=
  F_mono_along₅₄ facts S hf.onePath v (strict_mono₅₄ rho htt')

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- The conclusion of `namedG1At_of_namedG2At_finalizedPreceqOn` for an ancestor `Q` of a block `P`
    graded 2 at `v`, when `dom₁ c` is at most `vote_time d` and `Q` is in the filtered tree of `w`'s
    store in `W (strictEventIndex rho (vote_time d))` with its clock set to `vote_time d`. -/
theorem namedG1At_of_gradedAncestor_activeAtDutyReadOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hsb : Restated.SlashableBoundOn M S rho W Xb)
    {c : Round} (hc : 0 < c) {d : Slot}
    (hdomainVote : M.domain S.E S.hc c .g1 ≤
      M.vote_time S.E d)
    (hgst : lo ≤ M.early S.E S.hc c .g2)
    (hhor : M.domain S.E S.hc c .g0 ≤ rho.horizon)
    {v w : V} (hv : v ∈ Hs (M.domain S.E S.hc c .g2))
    (hw : w ∈ Hs (M.domain S.E S.hc c .g1)) {Q P : Block V}
    (hQP : Block.Preceq Q P)
    (hQactive : Q ∈ M.get_filtered_block_tree (M.toHealing
      (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st
        (M.vote_time S.E d)).core).toFG)
    (hG2 : Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
      (W (strictEventIndex rho (M.domain S.E S.hc c .g2)) v).st c .g2 P ⇢ true)
    (hlo : lo ≤ M.opening S.E S.hc (c - S.hc.η_SG)) :
    ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
      (W (strictEventIndex rho (M.domain S.E S.hc c .g1)) w).st c .g1 Q ⇢ b → b = true := by
  have hFduty : Block.Preceq
      (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core.F Q := by
    have h := facts.fc.q10_filtered_F hQactive
    rw [facts.sto.Sts_toHealing_F, facts.hd.setClock_core_F] at h
    exact h
  have hFQ : Block.Preceq
      (W (strictEventIndex rho (M.domain S.E S.hc c .g1)) w).st.core.F Q :=
    preceq_trans_Preceq (Restated.seedRel_stateBeforeTime_F_monoOn facts S Hs Xb hf w hdomainVote)
      hFduty
  have hP := Restated.namedG1At_of_namedG2At_finalizedPreceqOn facts S Hs Xb hf hHs hHsXb hsb hc hgst hhor
    hv hw (preceq_trans_Preceq hFQ hQP) hG2 hlo
  intro bA hbA
  obtain ⟨bB, hbB⟩ := facts.gr.gradeBool_nonempty S.E
    (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc c .g1)) w).st.core).gradeView
    (W (strictEventIndex rho (M.domain S.E S.hc c .g1)) w).st.core.F S.hc.η_SG c
    (M.early S.E S.hc c .g1) (M.late S.E S.hc c .g1) P
  exact facts.csAdded.confirmation_phaseGrade_mono S.E S.hc _ _ c .g1 hQP bB hbB (hP bB hbB) bA hbA

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- If every tick has an outcome, `0 < c`, slot `d` is a slot of round `c` from its opening slot on
    with `vote_time d` at most the opening of `c + 1` and inside the horizon, `w` is in the set for
    `dom₁ c`, the grade-1 store grade of `Q` on `w`'s store in `W (strictEventIndex rho (dom₁ c))`
    can return `true`, `Q` is in the filtered tree of `w`'s store staged at `vote_time d`, and
    `lo ≤ domain c .g1`, then `Q` is an ancestor of every anchor of `w`'s vote-duty read of `d`. -/
theorem preceq_voterAnchorAt_of_dutyReadGradeOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {c : Round} (hc : 0 < c) {d : Slot}
    (hslo : (M.opening_slot S.hc c) ≤ d)
    (hround : (M.round_of S.hc d) = c)
    (hnext : M.vote_time S.E d ≤ M.opening S.E S.hc (c + 1))
    (hvoteHor : M.vote_time S.E d ≤ rho.horizon)
    {w : V} (hw : w ∈ Hs (M.domain S.E S.hc c .g1))
    {Q : Block V}
    (hQgrade : Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
      (W (strictEventIndex rho (M.domain S.E S.hc c .g1)) w).st c .g1 Q ⇢ true)
    (hQactive : Q ∈ M.get_filtered_block_tree (M.toHealing
      (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st
        (M.vote_time S.E d)).core).toFG)
    (hgat : lo ≤ M.domain S.E S.hc c .g1) :
    ∀ cc, M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core.toHealing (M.vote_time S.E d)
        (W (strictEventIndex rho (M.vote_time S.E d)) w).cache ⇢ cc →
      let n := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st
        (M.vote_time S.E d)) (W (strictEventIndex rho (M.vote_time S.E d)) w).record cc
      ∀ A, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n (M.round_of S.hc n.st.core.s) ⇢ A →
        Block.Preceq Q A := by
  intro cc hcc
  dsimp only
  intro A hA
  have hround' : (M.round_of S.hc)
      (S.E.slotOf (M.vote_time S.E d)) = c := by
    rw [facts.sch.slotOf_vote_time]
    exact hround
  have hdomainVote : M.domain S.E S.hc c .g1 <
      M.vote_time S.E d := by
    have h0 := facts.gr.domain_g1_add_delta_le_domain_g0 S c
    have h1 := facts.gr.domain_add_five_delta_le_action S c .g0
    have h2 : M.confirmation_time S.E (M.opening_slot S.hc c) = M.a S.hc S.E.Δ c :=
      Restated.confirmation_time_opening_slot facts S c
    have h3 := facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E (M.opening_slot S.hc c)
    have h4 := facts.sch.slotStart_add_delta_eq_vote_time S.E (M.opening_slot S.hc c)
    have h5 := facts.sch.vote_time_mono S.E hslo
    have h6 := S.E.Δ_pos
    linarith
  have hg1Hor : M.domain S.E S.hc c .g1 ≤ rho.horizon :=
    hdomainVote.le.trans hvoteHor
  set wv := W (strictEventIndex rho (M.vote_time S.E d)) w with hwv
  set w1 := W (strictEventIndex rho (M.domain S.E S.hc c .g1)) w with hw1
  obtain ⟨fr, hfr⟩ := facts.gr.freezeRoot_nonempty S.E (M.gradeView (M.toHealing w1.st.core))
    w1.st.core.F S.hc.η_SG c (M.early S.E S.hc c .g1) (M.late S.E S.hc c .g1)
  have hbase := Restated.frame_phase_completed_in_roundOn facts
    S rho Hs Xb hf w c hc .g1 hw (M.vote_time S.E d)
    hdomainVote hnext hg1Hor hgat (fun j hj => hf.tick_outcome j _ _ hj) fr hfr
  have hprepared := Restated.Vocabulary.Proofs.NamedOutageClosure.frame_phase_prepared_eq facts
    S rho w c .g1 (M.vote_time S.E d) hround' _ (W (strictEventIndex rho (M.vote_time S.E d)))
    (mem_stateBeforeTime_along₅₄ hf.sorted hf.onePath _) hbase cc hcc
  have hQT : Q ∈ (M.gradeView (M.toHealing w1.st.core)).T := by
    obtain ⟨H, hHmem, hQH⟩ := facts.gr.ModelProperties_exists_mem_T_preceq_of_gradeBool S.E
      (M.toHealing w1.st.core) w1.st.core.F S.hc.η_SG c (M.early S.E S.hc c .g1)
      (M.late S.E S.hc c .g1) true hQgrade rfl
    have hpc := Restated.Vocabulary.Proofs.NamedStoreBridge.parentClosed_stateBeforeTime facts S rho
      (M.domain S.E S.hc c .g1) w (W (strictEventIndex rho (M.domain S.E S.hc c .g1)))
      (mem_stateBeforeTime_along₅₄ hf.sorted hf.onePath _)
    unfold Restated.Vocabulary.Internal.ParentClosed Record.Model.GS.parent_closed at hpc
    have hQ := Proofs.Records.mem_of_preceq hpc.2 Q H
      hHmem (Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mpr hQH)
    rw [facts.sto.toHealing_T] at hQ
    rw [facts.gr.Sts_gradeView_T]
    exact hQ
  obtain ⟨raw, hraw, hQraw⟩ := facts.gr.q10_freeze_of_graded S.E
    (M.gradeView (M.toHealing w1.st.core)) w1.st.core.F
    S.hc.η_SG c (facts.gr.q10_early_le_late S c .g1) hQT true hQgrade rfl fr hfr
  have hframe : (M.readFrame cc (M.toHealing (M.ns_setClock S.E wv.st (M.vote_time S.E d)).core) c).g1 =
      some (some (M.clipGrade raw wv.st.core.F)) := by
    rw [← facts.gr.phaseResult_g1, hprepared, hraw]
    rfl
  have hFQ : Block.Preceq wv.st.core.F Q := by
    have h := facts.fc.q10_filtered_F hQactive
    rw [facts.sto.Sts_toHealing_F, facts.hd.setClock_core_F] at h
    exact h
  have hQroot : Block.Preceq Q (M.clipGrade raw wv.st.core.F) :=
    (facts.gr.q10_retained_prefix raw wv.st.core.F Q
      (compatible_of_cases (Or.inr hFQ))).mpr hQraw
  have hroundRead : M.round_of S.hc
      (M.mkNode (M.ns_setClock S.E wv.st (M.vote_time S.E d)) wv.record cc).st.core.s = c := by
    rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.hd.Sts_setClock_core_s]
    exact hround'
  rw [hroundRead] at hA
  unfold Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor
    Restated.Vocabulary.Internal.PhaseGrades.nodeRead at hA
  obtain ⟨g, hg, rfl⟩ := returns_map_elim₅₄ _ _ _ hA
  rewrite [facts.nd.mkNode_cache, facts.nd.mkNode_st] at hg; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at hg
  obtain ⟨a, ha⟩ := facts.gr.anchor_nonempty S.E S.hc
    (M.toHealing (M.ns_setClock S.E wv.st (M.vote_time S.E d)).core) c
    (M.readFrame cc (M.toHealing (M.ns_setClock S.E wv.st (M.vote_time S.E d)).core) c).g1
  have ha' : M.anchor S.E S.hc
      (M.toHealing (M.store_with_cache (M.ns_setClock S.E wv.st (M.vote_time S.E d)) cc).core) c
      (M.readFrame cc (M.toHealing (M.store_with_cache (M.ns_setClock S.E wv.st (M.vote_time S.E d))
        cc).core) c).g1 ⇢ a := by
    rw [facts.nd.store_with_cache_readFrame]
    exact (facts.gr.anchor_eq_of_filtered_fg_root S.E S.hc c _
      (facts.nd.store_with_cache_get_filtered_block_tree _ _)
      (facts.nd.store_with_cache_get_fg_root _ _) a).2 ha
  rw [facts.nd.Sts_gradeContract_read_anchor cc S.E S.hc _ c g hg a ha']
  rw [hframe] at ha
  exact facts.gr.preceq_anchor_of_g1 _ _ _ _ hQactive hQroot a ha

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- Under the hypotheses of `preceq_voterAnchorAt_of_dutyReadGradeOn`, every outcome of `w`'s
    in-tree head computation at its vote-duty read of `d` is a descendant of `Q`. -/
theorem preceq_voterHeadAt_of_dutyReadGradeOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {c : Round} (hc : 0 < c) {d : Slot}
    (hslo : (M.opening_slot S.hc c) ≤ d)
    (hround : (M.round_of S.hc d) = c)
    (hnext : M.vote_time S.E d ≤ M.opening S.E S.hc (c + 1))
    (hvoteHor : M.vote_time S.E d ≤ rho.horizon)
    {w : V} (hw : w ∈ Hs (M.domain S.E S.hc c .g1))
    {Q : Block V}
    (hQgrade : Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
      (W (strictEventIndex rho (M.domain S.E S.hc c .g1)) w).st c .g1 Q ⇢ true)
    (hQactive : Q ∈ M.get_filtered_block_tree (M.toHealing
      (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st
        (M.vote_time S.E d)).core).toFG)
    (hgat : lo ≤ M.domain S.E S.hc c .g1) :
    ∀ cc, M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core.toHealing (M.vote_time S.E d)
        (W (strictEventIndex rho (M.vote_time S.E d)) w).cache ⇢ cc →
      let n := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st
        (M.vote_time S.E d)) (W (strictEventIndex rho (M.vote_time S.E d)) w).record cc
      ∀ T, M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T →
      ∀ L, M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
      ∀ L', M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore
          n.st.core.s ⇢ L' →
      ∀ H, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          T L L' (n.st.core.s - 1) ⇢ H →
      Block.Preceq Q H := by
  intro cc hcc n T hT L hL L' hL' H hH
  obtain ⟨G, hG⟩ := facts.gr.read_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc n.st.core.s)
  have hA : Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n
      (M.round_of S.hc n.st.core.s) ⇢ G.anchor := by
    unfold Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor
      Restated.Vocabulary.Internal.PhaseGrades.nodeRead
    exact returns_map_intro₅₄ (fun g : DecoupledConsensusModel.Protocol.GradeRead V => g.anchor) _ G hG
  have hQA := Restated.preceq_voterAnchorAt_of_dutyReadGradeOn facts S Hs Xb hf hc hslo
    hround hnext hvoteHor hw hQgrade hQactive hgat cc hcc _ hA
  have hn : n ∈ Restated.Vocabulary.Internal.NamedRecoveryRead.voteDutyRead M S rho w d :=
    ⟨W (strictEventIndex rho (M.vote_time S.E d)), mem_stateBeforeTime_along₅₄ hf.sorted hf.onePath _,
      cc, hcc, rfl⟩
  exact preceq_trans_Preceq hQA
    (Restated.Vocabulary.Proofs.HealingSurface.voterAnchorAt_preceq_voterHeadAt facts S rho w d n hn
      _ hA T hT L hL L' hL' H hH)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- If the Q2 read of a node state of `v`'s round-`c` action read can return `some Q`, `Q` is in the
    filtered tree of `w`'s store staged at `vote_time d`, and the hypotheses of
    `namedG1At_of_namedG2At_finalizedPreceqOn` and `preceq_voterAnchorAt_of_dutyReadGradeOn` on
    rounds, slots and sets hold, then every outcome of `w`'s in-tree head computation at its
    vote-duty read of `d` is a descendant of `Q`. -/
theorem preceq_voterHeadAt_of_nodeQ2_activeAtDutyReadOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hsb : Restated.SlashableBoundOn M S rho W Xb)
    {c : Round} (hc : 0 < c) {d : Slot}
    (hslo : (M.opening_slot S.hc c) ≤ d)
    (hround : (M.round_of S.hc d) = c)
    (hnext : M.vote_time S.E d ≤ M.opening S.E S.hc (c + 1))
    (hvoteHor : M.vote_time S.E d ≤ rho.horizon)
    (hgst : lo ≤ M.early S.E S.hc c .g2)
    (hhor : M.domain S.E S.hc c .g0 ≤ rho.horizon)
    {v w : V} (hv : v ∈ Hs (M.domain S.E S.hc c .g2))
    (hw : w ∈ Hs (M.domain S.E S.hc c .g1)) {Q : Block V}
    (n : M.N)
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v) c)
    (hQ : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n c ⇢ some Q)
    (hQactive : Q ∈ M.get_filtered_block_tree (M.toHealing
      (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st
        (M.vote_time S.E d)).core).toFG)
    (hlo : lo ≤ M.opening S.E S.hc (c - S.hc.η_SG)) :
    ∀ cc, M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core.toHealing (M.vote_time S.E d)
        (W (strictEventIndex rho (M.vote_time S.E d)) w).cache ⇢ cc →
      let n := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st
        (M.vote_time S.E d)) (W (strictEventIndex rho (M.vote_time S.E d)) w).record cc
      ∀ T, M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T →
      ∀ L, M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
      ∀ L', M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore
          n.st.core.s ⇢ L' →
      ∀ H, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          T L L' (n.st.core.s - 1) ⇢ H →
      Block.Preceq Q H := by
  have hdomainVote : M.domain S.E S.hc c .g1 ≤
      M.vote_time S.E d := by
    have h0 := facts.gr.domain_g1_add_delta_le_domain_g0 S c
    have h1 := facts.gr.domain_add_five_delta_le_action S c .g0
    have h2 : M.confirmation_time S.E (M.opening_slot S.hc c) = M.a S.hc S.E.Δ c :=
      Restated.confirmation_time_opening_slot facts S c
    have h3 := facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E (M.opening_slot S.hc c)
    have h4 := facts.sch.slotStart_add_delta_eq_vote_time S.E (M.opening_slot S.hc c)
    have h5 := facts.sch.vote_time_mono S.E hslo
    have h6 := S.E.Δ_pos
    linarith
  have hgat : lo ≤ M.domain S.E S.hc c .g1 :=
    hgst.trans ((facts.gr.early_le_domain S c).trans
      (facts.gr.domain_g2_le_domain_g1 S c))
  obtain ⟨raw, hrawGrade, hQraw⟩ :=
    Restated.namedG2At_freezeRoot_of_nodeQ2On facts S Hs Xb hf n hn hQ
  set d2 := W (strictEventIndex rho (M.domain S.E S.hc c .g2)) v with hd2
  obtain ⟨b2, hb2⟩ := facts.gr.gradeBool_nonempty S.E (M.gradeView (M.toHealing d2.st.core))
    d2.st.core.F S.hc.η_SG c (M.early S.E S.hc c .g2) (M.late S.E S.hc c .g2) raw
  have hb2true : b2 = true := hrawGrade b2 hb2
  subst hb2true
  have hG1 := Restated.namedG1At_of_gradedAncestor_activeAtDutyReadOn facts S Hs Xb hf hHs hHsXb
    hsb hc hdomainVote hgst hhor hv hw hQraw hQactive hb2 hlo
  set d1 := W (strictEventIndex rho (M.domain S.E S.hc c .g1)) w with hd1
  obtain ⟨b1, hb1⟩ := facts.gr.gradeBool_nonempty S.E (M.gradeView (M.toHealing d1.st.core))
    d1.st.core.F S.hc.η_SG c (M.early S.E S.hc c .g1) (M.late S.E S.hc c .g1) Q
  have hb1true : b1 = true := hG1 b1 hb1
  subst hb1true
  exact Restated.preceq_voterHeadAt_of_dutyReadGradeOn facts S Hs Xb hf hc hslo hround hnext
    hvoteHor hw hb1 hQactive hgat

end

/-! ### Helpers of the second half -/

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface

/-- In a run sorted by key, the worlds strictly before `t` are the worlds before the event of index
    `strictEventIndex rho t`. -/
private theorem stateBeforeTime_eq_strict₅₄s (S : Setup V) (rho : Record.Run V)
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

/-- In a run sorted by key, the world `W (strictEventIndex rho t)` of a path `W` is a world strictly
    before `t`. -/
private theorem mem_stateBeforeTime_along₅₄s {S : Setup V} {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (t : Time) :
    W (strictEventIndex rho t) ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t := by
  rw [stateBeforeTime_eq_strict₅₄s S rho hsorted]
  exact (hW _).1

/-- Along a path `W` of `rho`, `W (m + k)` is among the worlds the events `m` to `m + k - 1` lead to
    from `W m`. -/
private theorem onePath_reach₅₄s {S : Setup V} {rho : Record.Run V}
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

/-- Along a path `W` of `rho`, for `m ≤ n`, `W n` is among the worlds the events `m` to `n - 1` lead
    to from `W m`. -/
private theorem onePath_slice₅₄s {S : Setup V} {rho : Record.Run V}
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) {m n : Nat}
    (hmn : m ≤ n) :
    W n ∈ ((rho.events.drop m).take (n - m)).foldlM (Record.worldStepOf M S) (W m) := by
  have h := onePath_reach₅₄s W hW m (n - m)
  rwa [Nat.add_sub_of_le hmn] at h

omit [DecidableEq V] [Fintype V] in
/-- In a run sorted by key, every event of index less than `strictEventIndex rho t` is at a time
    before `t`. -/
private theorem time_lt_of_lt_strict₅₄s {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f)) (t : Time) :
    ∀ (j : Nat) (e : Record.Event V), j < strictEventIndex rho t → rho.events[j]? = some e →
      e.time < t := by
  intro j e hj he
  have hpre : rho.events.filter (fun e => decide (e.time < t)) =
      rho.events.take (rho.events.filter (fun e => decide (e.time < t))).length := by
    refine List.prefix_iff_eq_take.mp ?_
    rw [DecoupledConsensusModel.Proofs.Bridges.filter_eq_takeWhile_of_pairwise
      (R := fun e f => Record.Event.key e ≤ Record.Event.key f) ?_ _ hsorted]
    · exact List.takeWhile_prefix _
    · intro e f hk hf
      simp only [decide_eq_true_eq] at hf ⊢
      exact lt_of_le_of_lt (Restated.time_le_of_key_le hk) hf
  have hj' : j < (rho.events.filter (fun e => decide (e.time < t))).length := hj
  have hmem : e ∈ rho.events.filter (fun e => decide (e.time < t)) := by
    rw [hpre]
    exact List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hj']; exact he)
  have hp := (List.mem_filter.mp hmem).2
  simpa only [decide_eq_true_eq] using hp

/-- The store `tickStore` stages at `t` from `n`'s core store has the tree of `n`'s core store. -/
private theorem tickStore_T₅₄s (facts : Record.Facts M) {S : Setup V} (n : M.N) (t : Time) :
    (Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t).T = n.st.core.T := by
  rw [Restated.Vocabulary.Proofs.Optimistic.tickStore,
    ← facts.hd.setClock_core_eq_store_with_t_s S.E n.st t, facts.hd.Sts_setClock_core_T]

/-- The store `tickStore` stages at `t` from `n`'s core store has the block stamps of `n`'s core
    store. -/
private theorem tickStore_timestamp_block₅₄s (facts : Record.Facts M) {S : Setup V} (n : M.N)
    (t : Time) :
    (Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t).timestamp_block =
      n.st.core.timestamp_block := by
  rw [Restated.Vocabulary.Proofs.Optimistic.tickStore,
    ← facts.hd.setClock_core_eq_store_with_t_s S.E n.st t, facts.hd.setClock_core_timestamp_block]

/-- The core store of `n`'s store with its clock set to `t` is the store `tickStore` stages from
    `n`'s core store at `t`. -/
private theorem setClock_core_tickStore₅₄s (facts : Record.Facts M) (S : Setup V) (n : M.N)
    (t : Time) :
    (M.ns_setClock S.E n.st t).core = Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t := by
  rw [Restated.Vocabulary.Proofs.Optimistic.tickStore, facts.hd.setClock_core_eq_store_with_t_s]

/-- Writing a cache into a store leaves the confirmation tree of its core store unchanged. -/
private theorem confTree_swc₅₄s (facts : Record.Facts M) (st : M.NS) (c : M.Cache) :
    Restated.Vocabulary.Protocol.confTree M (M.store_with_cache st c).core =
      Restated.Vocabulary.Protocol.confTree M st.core := by
  unfold Restated.Vocabulary.Protocol.confTree Record.Model.S.toHealing
  rw [facts.nd.store_with_cache_get_filtered_block_tree]

/-- Writing a cache into a store leaves the confirmation root of its core store unchanged. -/
private theorem confRoot_swc₅₄s (facts : Record.Facts M) (st : M.NS) (c : M.Cache) :
    Restated.Vocabulary.Protocol.confRoot M (M.store_with_cache st c).core =
      Restated.Vocabulary.Protocol.confRoot M st.core := by
  unfold Restated.Vocabulary.Protocol.confRoot Record.Model.S.toHealing
  rw [facts.nd.store_with_cache_get_fg_root]

/-- Writing a cache into a store leaves the late vote set of its core store unchanged. -/
private theorem confLate_swc₅₄s (facts : Record.Facts M) (st : M.NS) (c : M.Cache) (E : Env V)
    (s : Slot) :
    Restated.Vocabulary.Protocol.confLate M E (M.store_with_cache st c).core s =
      Restated.Vocabulary.Protocol.confLate M E st.core s := by
  unfold Restated.Vocabulary.Protocol.confLate
  rw [facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_pool]

/-- Writing a cache into a store leaves the confirmation vote set of its core store unchanged. -/
private theorem confVotes_swc₅₄s (facts : Record.Facts M) (st : M.NS) (c : M.Cache) (E : Env V)
    (s : Slot) :
    Restated.Vocabulary.Protocol.confVotes M E (M.store_with_cache st c).core s =
      Restated.Vocabulary.Protocol.confVotes M E st.core s := by
  unfold Restated.Vocabulary.Protocol.confVotes Restated.Vocabulary.Protocol.confEarly
  rw [confLate_swc₅₄s facts, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_pool]

/-- The SG root read under the grade contract of any cache `c'` is the same on a store with a cache
    `c` written in as on the store itself. -/
private theorem sgRoot_store_with_cache₅₄s (facts : Record.Facts M) (E : Env V)
    (hc : Protocol.HealConfig) (st : M.NS) (c c' : M.Cache) (r : Round) (x : Block V) :
    M.get_sg_root_with (M.gradeContract c') E hc (M.toHealing (M.store_with_cache st c).core) r ⇢ x ↔
      M.get_sg_root_with (M.gradeContract c') E hc (M.toHealing st.core) r ⇢ x := by
  rw [facts.nd.gradeContract_sgRoot_eq_frameAnchor, facts.nd.gradeContract_sgRoot_eq_frameAnchor,
    facts.nd.store_with_cache_readFrame]
  exact facts.gr.anchor_eq_of_filtered_fg_root E hc r _
    (facts.nd.store_with_cache_get_filtered_block_tree st c) (facts.nd.store_with_cache_get_fg_root st c) x

open scoped DC in
/-- If `m` can return `a`, then `f <$> m` can return `f a`. -/
private theorem returns_map_intro₅₄s {α β : Type} (f : α → β) (m : DC.NDRE α) (a : α)
    (h : m ⇢ a) : (f <$> m) ⇢ f a := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image]
  exact ⟨_, h, rfl⟩

/-- `confVotes` of every store at every slot has an outcome. -/
private theorem confVotes_nonempty₅₄s (facts : Record.Facts M) (E : Env V) (st : M.S) (s : Slot) :
    ∃ u, Restated.Vocabulary.Protocol.confVotes M E st s ⇢ u := by
  obtain ⟨tm, htm⟩ := facts.sto.tau_nonempty st
  exact ⟨_, returns_map_intro₅₄s _ _ _ (returns_map_intro₅₄s _ _ _ htm)⟩

/-- The late votes `confLate` of the store `tickStore` stages from `st` are those of `st`. -/
private theorem confLate_tickStore₅₄s (facts : Record.Facts M) (S : Setup V) (st : M.S) (t : Time)
    (s : Slot) :
    Restated.Vocabulary.Protocol.confLate M S.E (Restated.Vocabulary.Proofs.Optimistic.tickStore M S st t) s =
      Restated.Vocabulary.Protocol.confLate M S.E st s := by
  rw [Restated.Vocabulary.Protocol.confLate, Restated.Vocabulary.Protocol.confLate,
    Restated.Vocabulary.Proofs.Optimistic.tickStore, facts.sto.pool_set_clock_slot,
    facts.sto.store_with_t_s_timestamp_vote]

/-- Every outcome of `confirmationVotes` of `st` at slot `s` is an outcome of `confVotes` of `st` at
    slot `s`. -/
private theorem confVotes_of_confirmationVotes₅₄s (E : Env V) (st : M.S) (s : Slot)
    (cv : Finset (GoldfishVote V))
    (h : Restated.Vocabulary.Internal.confirmationVotes M E st s ⇢ cv) :
    Restated.Vocabulary.Protocol.confVotes M E st s ⇢ cv := h

/-- Slot `s`'s vote time is before its support cutoff. -/
private theorem vote_time_lt_support_cutoff₅₄s (facts : Record.Facts M) (S : Setup V) (s : Slot) :
    M.vote_time S.E s < M.support_cutoff S.E s := by
  rcases lt_or_gt_of_ne (facts.sch.support_cutoff_ne_vote_time S.E s) with h | h
  · exfalso
    have h1 := facts.sch.support_cutoff_lt_vote_time_imp_lt_proposal_time S.E h
    have h2 := facts.sch.proposal_time_slotOf_le S.E (le_of_lt (facts.sch.support_cutoff_pos S s))
    rw [facts.sch.slotOf_support_cutoff] at h2
    exact absurd h1 (not_lt.mpr h2)
  · exact h

omit [DecidableEq V] [Fintype V] in
/-- For `Δ > 0`, if `a` and `b` are multiples of `Δ` and `a < b`, then `a + Δ ≤ b`. -/
private theorem add_delta_le_of_lt_emod₅₄s {Δ a b : Int} (hΔ : 0 < Δ) (ha : a % Δ = 0)
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

/-- A slot's vote time plus one delay is at most its support cutoff. -/
private theorem vote_time_add_delta_le_support_cutoff₅₄s (facts : Record.Facts M) (S : Setup V)
    (s : Slot) : M.vote_time S.E s + S.E.Δ ≤ M.support_cutoff S.E s :=
  add_delta_le_of_lt_emod₅₄s S.E.Δ_pos (facts.sch.vote_time_emod_delta S s)
    (facts.sch.support_cutoff_emod_delta S s) (vote_time_lt_support_cutoff₅₄s facts S s)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- If `v` is in the set for slot `s`'s support cutoff, `lo ≤ vote_time s`, the support cutoff is
    inside the horizon and at most `d`, the FG root of `v`'s core store in
    `W (strictEventIndex rho d)` is an ancestor of `B`, and every committee member of `s` in the set
    for its vote time voted along `W` a run block with `B` as an ancestor, then every head voted by
    such a member is genesis or admitted by `v` along `W` before the support cutoff. -/
private theorem honestHeadsAvailableBefore_core₅₄s (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {s : Slot} {v : V} (hv : v ∈ Hs (M.support_cutoff S.E s))
    (hpost : lo ≤ M.vote_time S.E s)
    (hhor : M.support_cutoff S.E s ≤ rho.horizon)
    {d : Time} (hd : M.support_cutoff S.E s ≤ d)
    {B : Block V}
    (hroot : Block.Preceq
      (M.get_fg_root (M.toHealing (W (strictEventIndex rho d) v).st.core).toFG) B)
    (hvotes : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s
      (fun X => Block.Preceq B X)) :
    Restated.HonestHeadsAvailableBeforeOn M S rho W Hs Xb s v
      (M.support_cutoff S.E s) := by
  intro X hhead
  by_cases hgen : X = Block.genesis
  · exact Or.inl hgen
  right
  obtain ⟨x, hx, hcommittee, ⟨C, hCX, hCrun⟩, hXemit⟩ := hhead
  have hxvote : x ∈ Hs (M.vote_time S.E s) :=
    hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E s) hx
  have hCemit : Restated.Vocabulary.Execution.NamedRun.emits M S rho W x
      (.gfVote ⟨x, s, C.erase.root⟩) (M.vote_time S.E s) := by
    simpa only [hCX] using hXemit
  set n := strictEventIndex rho (M.vote_time S.E s) with hn
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc (W n x).st.core.toHealing
    (M.vote_time S.E s) (W n x).cache
  have hCmem := Restated.emittedHead_mem_voteDutyStoreOn facts S Hs Xb hf (hHsXb _ hx)
    hCrun hCemit c hc
  rw [facts.nd.mkNode_st] at hCmem
  try simp only [facts.nd.store_with_cache_bodies, confTree_swc₅₄s facts, confRoot_swc₅₄s facts, confLate_swc₅₄s facts, confVotes_swc₅₄s facts, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at hCmem
  try rw [setClock_core_tickStore₅₄s facts S] at hCmem
  rw [tickStore_T₅₄s facts] at hCmem
  obtain ⟨Y, hBY, hYrun, hYemit⟩ := hvotes x hxvote hcommittee
  have hvoteEq : (⟨x, s, X.root⟩ : GoldfishVote V) =
      ⟨x, s, Y.erase.root⟩ :=
    Restated.emits_gfVote_uniqueOn facts S Hs Xb hf hXemit hYemit rfl
  have hrootXY : X.root = Y.erase.root :=
    congrArg GoldfishVote.head hvoteEq
  have hrootNamed : C.root = Y.root := by
    rw [← Proofs.NamedWire.erase_root C, ← Proofs.NamedWire.erase_root Y, hCX]
    exact hrootXY
  have hCY : C = Y :=
    hf.rootCollisionFree.root_injective C Y
      hCrun hYrun C Y (Or.inl (Proofs.NamedAncestry.named_self C))
      (Or.inr (Proofs.NamedAncestry.named_self Y)) hrootNamed
  have hBX : Block.Preceq B C.erase := by
    rw [hCY]
    exact hBY
  obtain ⟨D, hDbody, hDerase⟩ :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore facts S rho n x
      (W n) (hf.onePath n).1 hCmem
  have hDrun := Restated.blockInRun_of_directOn facts S rho W Xb
    (Restated.directBlock_of_prefixOn facts S rho W Xb (hHsXb _ hx) n hDbody)
  have hrootCD : C.root = D.root := by
    calc
      C.root = C.erase.root := (Proofs.NamedWire.erase_root C).symm
      _ = D.erase.root := (congrArg Block.root hDerase).symm
      _ = D.root := Proofs.NamedWire.erase_root D
  have hCD : C = D :=
    hf.rootCollisionFree.root_injective C D
      hCrun hDrun C D (Or.inl (Proofs.NamedAncestry.named_self C))
      (Or.inr (Proofs.NamedAncestry.named_self D)) hrootCD
  have hCbody : C ∈ (W n x).st.bodies := by
    rw [hCD]
    exact hDbody
  have hprocessed : Restated.Vocabulary.Execution.Object.processed M (W n x).st
      (Object.block C) = true := by
    simpa only [Restated.Vocabulary.Execution.Object.processed, decide_eq_true_eq] using hCbody
  rcases Restated.Vocabulary.Protocol.acceptsAt_block_of_processed facts S rho x W hf.onePath n C
      hprocessed with
    hgen' | ⟨j, hjn, t, hacc⟩
  · have hXgen : X = Block.genesis := by
      rw [← hCX, hgen', erase_named_genesis]
    exact False.elim (hgen hXgen)
  · obtain ⟨-, e, he, -, het⟩ := hacc.1
    have ht : t < M.vote_time S.E s := by
      rw [← het]
      exact time_lt_of_lt_strict₅₄s hf.sorted _ j e hjn he
    have hCpos : 0 < C.slot := by
      have hparent := Restated.Vocabulary.Protocol.parent_slot_lt_of_acceptsAt_block facts S W
        hf.onePath hacc
      rw [Proofs.NamedWire.erase_slot] at hparent
      exact Nat.zero_lt_of_lt hparent
    have hxmax : x ∈ Hs (max t lo) :=
      hHs _ _ (max_le (le_of_lt ht) hpost) hxvote
    have hvd := vote_time_add_delta_le_support_cutoff₅₄s facts S s
    rw [← hCX]
    apply Restated.block_admittedBefore_of_accepted_after_cutoffOn facts
      S Hs Xb hf hHs hHsXb hxmax hv hCpos hacc
        (lt_of_lt_of_le ht (le_sub_iff_add_le.mpr hvd)) (hpost.trans (le_sub_iff_add_le.mpr hvd))
        (Int.sub_add_cancel _ _) hhor
    intro k hk
    have hkd : k ≤ strictEventIndex rho d :=
      hk.trans (Restated.strict_filter_length_mono rho hd)
    exact preceq_trans_Preceq
      (Restated.Vocabulary.Proofs.finalized_preceq_at_prefix_of_storeBeforeRoot_preceq facts
        S rho hf.sorted (w := v) hkd (W k) (hf.onePath k).1 _ (onePath_slice₅₄s W hf.onePath hkd)
        hroot) hBX

end

/-! ### Clean reads from the grade at one world of `W` -/

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Proofs.HealingLemmas

/-- Along a path `W`, for `j ≤ n`, `v`'s finalized block in `W j` is an ancestor of its finalized
    block in `W n`. -/
private theorem F_mono_along₅₄s (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (v : V)
    {j n : Nat} (hjn : j ≤ n) : Block.Preceq (W j v).st.core.F (W n v).st.core.F :=
  Restated.Vocabulary.Protocol.stateBefore_F_mono facts S rho v hjn (W j) (hW j).1 (W n)
    (onePath_slice₅₄s W hW hjn)

/-- A block of the filtered block tree of a store is a descendant of the store's finalized block. -/
private theorem F_preceq_of_mem_filtered₅₄s (facts : Record.Facts M) (st : M.S) {C : Block V}
    (hC : C ∈ M.get_filtered_block_tree (M.toHealing st).toFG) : Block.Preceq st.F C := by
  have h := facts.fc.finalized_preceq_of_mem_get_filtered_block_tree hC
  rwa [facts.sto.Sts_toHealing_F] at h

/-- If every member of the set for `domain q .g2` has `P` active, with every outcome of its grade-2
    store grade `true`, in its node state in `W (strictEventIndex rho (domain q .g2))`, `reader` is
    in that set and `S.a q ≤ read`, then `P` is in `reader`'s store in
    `W (strictEventIndex rho read)`. -/
private theorem formsW_processedAtRead₅₄s (facts : Record.Facts M)
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
    _ (hf.onePath _).1 _ hmn _ (onePath_slice₅₄s W hf.onePath hmn) hsource

/-- If every member of the set for `domain r .g2` has `C` active, with every outcome of its grade-2
    store grade `true`, in its node state in `W (strictEventIndex rho (domain r .g2))`, `v` is in
    the set for `domain r .g0`, and `C` is active at a node state `n` of `v`'s round-`r` action
    read, then `C` is an ancestor of every SG vote `n` can select. -/
private theorem formsW_preceq_actionSGBlockAt₅₄s (facts : Record.Facts M) (S : Setup V)
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
    exact returns_map_intro₅₄s (fun g : DecoupledConsensusModel.Protocol.GradeRead V => g.Q2) _ G hG
  obtain ⟨Q, hQ, hCQ⟩ :=
    Restated.preceq_actionQ2_of_domainGradeOn facts S Hs Xb hf hHs hr hhor hv hlo
      (hformsW v hvG2).1 hb n hn hactive _ hGq
  rw [hQ] at hGq
  exact Restated.preceq_actionSGBlockAt_of_actionQ2On facts S Hs Xb hf hHs hHsXb hr hhor
    (hHs _ _ (facts.gr.domain_le_domain_g0 S r .g1) hv) hlo n hn hGq hCQ

/-- With the grade of round `r` read in `W (strictEventIndex rho (domain r .g2))`, `v` in the set
    for `S.a r`, `w` in the set for `S.a r + Δ`, `lo ≤ S.a r`, `lo ≤ opening (r − η_SG)`, and `P`
    active at a node state `n` of `v`'s round-`r` action read and at `w`'s core store in
    `W (strictEventIndex rho (S.a (r + 1)))`, every SG vote `n` can select is in that store, stamped
    before round `r + 1`'s earliest grade cutoff. -/
private theorem formsW_actionSGBlockAt_visible₅₄s (facts : Record.Facts M)
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
      (mem_stateBeforeTime_along₅₄s hf.sorted hf.onePath _) n hn A2 hA2 H hH
  have hvDom : v ∈ Hs (M.domain S.E S.hc r .g0) :=
    hHs _ _ (facts.gr.domain_le_a S r .g0) hv
  have hPH : Block.Preceq P H :=
    formsW_preceq_actionSGBlockAt₅₄s facts S Hs Xb hf hHs hHsXb hr hhor
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
    have hFP := F_preceq_of_mem_filtered₅₄s facts _ hactive
    have hFhist : ∀ j : Nat,
        j ≤ (rho.events.filter (fun e => decide (e.time <
          (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ))).length →
          Block.Preceq (W j w).st.core.F D.erase := by
      intro j hj
      have hjN : j ≤ strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) :=
        le_trans hj (Restated.strict_filter_length_mono rho hrelayRead)
      rw [hDerase]
      exact preceq_trans_Preceq (F_mono_along₅₄s facts S hf.onePath w hjN)
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

/-- A clean action read, with the grade of round `r` read,
    for every member of the set for `domain r .g2`, at its node state in
    `W (strictEventIndex rho (domain r .g2))`. -/
private theorem formsW_cleanActionReadFor₅₄s (facts : Record.Facts M)
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
  have hvisible := formsW_actionSGBlockAt_visible₅₄s facts
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
      (formsW_preceq_actionSGBlockAt₅₄s facts S Hs Xb hf hHs hHsXb hr
        hhor hformsW hvDom n hn (hownActive v hv n hn) hlo g hg B hB) b hb

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- If the validators outside the set weigh less than a third at every time up to the horizon,
    `0 < r0`, `Q.erase` has the grade of round `r0` at the world of `W` before its grade-2 domain
    time, `Q` is a run block of height at least `Mh − 1`, `1 ≤ Mh`, every member of the set for each
    read time in `[S.a r0, S.a q]` has `h_max = Mh` and `h_j + 2 ≤ Mh` there, `lo ≤ S.a r0`,
    `lo ≤ opening (r0 − η_SG)`, and the members of the set for `S.a k + Δ` are awake at `k` for
    `r0 ≤ k < q`, then for every round `k` in `[r0, q]`, `Q.erase` has the grade of `k` and is
    active at the round-`k` action read of every member of the set for `S.a k`. -/
theorem namedGradeFormsAt_persists_through_gateOffActionWindowOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hfb : BelowOneThirdOn S rho Hs)
    {Mh : Height} {r0 q : Round} {Q : NamedBlock V}
    (hr0 : 0 < r0)
    (hseed : ∀ v ∈ Hs (M.domain S.E S.hc r0 .g2),
      Q.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc r0 .g2)) v) ∧
        ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
          (W (strictEventIndex rho (M.domain S.E S.hc r0 .g2)) v).st r0 .g2 Q.erase ⇢ b → b = true)
    (hQrun : Restated.RunBlockOn M S rho W Xb Q)
    (hQheight : Mh - 1 ≤ (M.derive_named S.E S.cfg Q).h)
    (hM : 1 ≤ Mh)
    (hpost : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S r0))
    (hendpoint : (Restated.Vocabulary.Execution.Setup.a M S q) ≤ rho.horizon)
    (hframe : ∀ read : Time, (Restated.Vocabulary.Execution.Setup.a M S r0) ≤ read →
      read ≤ (Restated.Vocabulary.Execution.Setup.a M S q) →
      ∀ w ∈ Hs read,
        (W (strictEventIndex rho read) w).st.h_max = Mh ∧
          (W (strictEventIndex rho read) w).st.h_j + 2 ≤ Mh)
    (hlo : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S r0))
    (hloOpen : lo ≤ M.opening S.E S.hc (r0 - S.hc.η_SG))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → r0 ≤ k → k < q → ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    ∀ k, r0 ≤ k → k ≤ q →
      (∀ v ∈ Hs (M.domain S.E S.hc k .g2),
        Q.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
            (W (strictEventIndex rho (M.domain S.E S.hc k .g2)) v) ∧
          ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
            (W (strictEventIndex rho (M.domain S.E S.hc k .g2)) v).st k .g2 Q.erase ⇢ b →
            b = true) ∧
        ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k)),
          ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
            (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S k)) w) k,
          Q.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M n := by
  have hsb : Restated.SlashableBoundOn M S rho W Xb := hf.slashableBound
  have hmajority : HonestWeightMajorityOn S rho Hs :=
    honestWeightMajorityOn_of_belowOneThirdOn hfb
  have hretain : ∀ (k : Round),
      (∀ v ∈ Hs (M.domain S.E S.hc k .g2),
        Q.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
            (W (strictEventIndex rho (M.domain S.E S.hc k .g2)) v) ∧
          ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
            (W (strictEventIndex rho (M.domain S.E S.hc k .g2)) v).st k .g2 Q.erase ⇢ b →
            b = true) →
      ∀ read : Time, (Restated.Vocabulary.Execution.Setup.a M S k) ≤ read →
      (Restated.Vocabulary.Execution.Setup.a M S r0) ≤ read →
      read ≤ (Restated.Vocabulary.Execution.Setup.a M S q) →
      ∀ w ∈ Hs read,
        Q.erase ∈ M.get_filtered_block_tree
          (M.toHealing (W (strictEventIndex rho read) w).st.core).toFG := by
    intro k hforms read hread hlo' hhi w hw
    have hwdom : w ∈ Hs (M.domain S.E S.hc k .g2) :=
      hHs _ _ ((facts.gr.domain_le_a S k .g2).trans hread) hw
    have hprocessed : Q.erase ∈ (W (strictEventIndex rho read) w).st.T :=
      formsW_processedAtRead₅₄s facts S Hs Xb hf hforms hwdom hread
    have hfr := hframe read hlo' hhi w hw
    exact Restated.frontierBlock_filtered_of_gateOffOn facts S Hs Xb hf hsb (hHsXb _ hw)
      (hhi.trans hendpoint) hprocessed rfl hQrun hQheight hM hfr.1 hfr.2
  have hactivity : ∀ (k : Round), r0 ≤ k → k ≤ q →
      (∀ v ∈ Hs (M.domain S.E S.hc k .g2),
        Q.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
            (W (strictEventIndex rho (M.domain S.E S.hc k .g2)) v) ∧
          ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
            (W (strictEventIndex rho (M.domain S.E S.hc k .g2)) v).st k .g2 Q.erase ⇢ b →
            b = true) →
      ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k)),
        ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S k)) w) k,
        Q.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M n := by
    intro k hlo' hhi hforms w hw
    exact Restated.Vocabulary.Proofs.HealingSurface.activeAtAction_of_retainedAtRead facts S (v := w)
      _ (mem_stateBeforeTime_along₅₄s hf.sorted hf.onePath _)
      (hretain k hforms ((Restated.Vocabulary.Execution.Setup.a M S k)) le_rfl
        (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hlo')
        (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hhi) w hw)
  have hgrade : ∀ k, r0 ≤ k → k ≤ q →
      ∀ v ∈ Hs (M.domain S.E S.hc k .g2),
        Q.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
            (W (strictEventIndex rho (M.domain S.E S.hc k .g2)) v) ∧
          ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
            (W (strictEventIndex rho (M.domain S.E S.hc k .g2)) v).st k .g2 Q.erase ⇢ b →
            b = true := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro hr0k hkq
        rcases eq_or_lt_of_le hr0k with hEq | hlt
        · subst k
          exact hseed
        · cases k with
          | zero => exact (Nat.not_lt_zero _ hlt).elim
          | succ k =>
              have hr0k' : r0 ≤ k := Nat.le_of_lt_succ hlt
              have hkq' : k ≤ q := (Nat.le_succ k).trans hkq
              have hprev := ih k (Nat.lt_succ_self k) hr0k' hkq'
              have hkpos : 0 < k := lt_of_lt_of_le hr0 hr0k'
              have hpostk : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S k) :=
                hpost.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hr0k')
              have hlok : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S k) :=
                hlo.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hr0k')
              have hloOpenk : lo ≤
                  M.opening S.E S.hc (k - S.hc.η_SG) :=
                hloOpen.trans (facts.gr.NamedOutageClosure_opening_mono S (Nat.sub_le_sub_right hr0k' _))
              have hloNext : (Restated.Vocabulary.Execution.Setup.a M S r0) ≤
                  (Restated.Vocabulary.Execution.Setup.a M S (k + 1)) :=
                Restated.Vocabulary.Proofs.Assembly.a_mono facts S (hr0k'.trans (Nat.le_succ k))
              have hhiNext : (Restated.Vocabulary.Execution.Setup.a M S (k + 1)) ≤
                  (Restated.Vocabulary.Execution.Setup.a M S q) :=
                Restated.Vocabulary.Proofs.Assembly.a_mono facts S hkq
              have hcut : Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (k + 1) ≤
                  rho.horizon :=
                (le_of_lt (Restated.Vocabulary.Proofs.HealingSurface.next_Γ_neg1_lt_action facts S k)).trans
                  (hhiNext.trans hendpoint)
              have hcutLo : (Restated.Vocabulary.Execution.Setup.a M S k) ≤
                  Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (k + 1) :=
                le_trans (Int.le_add_of_nonneg_right (le_of_lt S.E.Δ_pos))
                  (facts.gr.action_add_delta_le_next_Γ_neg1 S k)
              have hcutHi : Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (k + 1) ≤
                  (Restated.Vocabulary.Execution.Setup.a M S q) :=
                (le_of_lt (Restated.Vocabulary.Proofs.HealingSurface.next_Γ_neg1_lt_action facts S k)).trans
                  hhiNext
              have hactiveNext : ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (k + 1))),
                  Q.erase ∈ M.get_filtered_block_tree (M.toHealing
                    (W (strictEventIndex rho
                      (Restated.Vocabulary.Execution.Setup.a M S (k + 1))) w).st.core).toFG :=
                fun w hw => hretain k hprev ((Restated.Vocabulary.Execution.Setup.a M S (k + 1)))
                  (Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_succ k)) hloNext hhiNext w hw
              have hdomain : ∀ w ∈ Hs (M.domain S.E S.hc (k + 1) .g2),
                  Q.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
                    (W (strictEventIndex rho (M.domain S.E S.hc (k + 1) .g2)) w) := by
                intro x hx
                have hdom : M.domain S.E S.hc (k + 1) .g2 =
                    Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (k + 1) :=
                  (facts.gr.gammaNeg1_eq_domain_g2_succ S k).symm
                rw [hdom] at hx ⊢
                exact hretain k hprev _ hcutLo
                  ((Restated.Vocabulary.Proofs.Assembly.a_mono facts S hr0k').trans hcutLo) hcutHi x hx
              have hAk := hA k
                (Restated.lo_le_early_g2_sub_delta_of_opening facts S hkpos hloOpenk le_rfl)
                hr0k' (Nat.lt_of_succ_le hkq)
              have hne : (Hs ((Restated.Vocabulary.Execution.Setup.a M S (k + 1)))).Nonempty :=
                nonempty_of_honestWeightMajority_l54
                  (hmajority _ (hhiNext.trans hendpoint))
              exact Restated.namedGradeFormsAt_of_cleanActionReadOn facts S Hs Xb hf hHs hHsXb
                hmajority
                (formsW_cleanActionReadFor₅₄s facts S Hs Xb hf hHs hHsXb hkpos hprev hpostk hcut
                  (hactivity k hr0k' hkq' hprev) hactiveNext hdomain hAk hlok hloOpenk)
                hne hlok hAk
  exact fun k hlo' hhi => ⟨hgrade k hlo' hhi, hactivity k hlo' hhi (hgrade k hlo' hhi)⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- If `x ∈ Xb`, `C` is a run block read through `Xb` along `W`, and `x` emitted along `W` at slot
    `s`'s vote time the Goldfish vote with head `C`, then for every outcome `c` of the phase tick on
    `x`'s node state in `W (strictEventIndex rho (vote_time s))`, `C.erase` is in the tree of the
    read staged from that node state with `c`. -/
theorem named_emittedHead_mem_voteDutyReadOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {x : V} (hx : x ∈ Xb) {s : Slot} {C : NamedBlock V}
    (hCrun : Restated.blockInRunOn M S rho W Xb C)
    (hemit : Restated.Vocabulary.Execution.NamedRun.emits M S rho W x
      (.gfVote ⟨x, s, C.erase.root⟩) (M.vote_time S.E s)) :
    ∀ c : M.Cache, M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E s)) x).st.core.toHealing
        (M.vote_time S.E s) (W (strictEventIndex rho (M.vote_time S.E s)) x).cache ⇢ c →
    C.erase ∈ (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) x).st
      (M.vote_time S.E s)) (W (strictEventIndex rho (M.vote_time S.E s)) x).record c).st.core.T :=
  Restated.emittedHead_mem_voteDutyStoreOn facts S Hs Xb hf hx hCrun hemit

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- If `v` is in the set for slot `s`'s support cutoff, `lo ≤ vote_time s`, the support cutoff is
    inside the horizon, the root of `v`'s confirmation store at `confirmation_time s` is an ancestor
    of `B`, and every committee member of `s` in the set for its vote time voted along `W` a run
    block with `B` as an ancestor, then every head voted by a committee member of `s` in the set for
    its confirmation time is genesis or admitted by `v` before the support cutoff. -/
theorem honestHeadsAvailableBefore_of_postHealingConeOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {s : Slot} {v : V} (hv : v ∈ Hs (M.support_cutoff S.E s))
    (hpost : lo ≤ M.vote_time S.E s)
    (hhor : M.support_cutoff S.E s ≤ rho.horizon)
    {B : Block V}
    (hroot : Block.Preceq
      (Restated.Vocabulary.Protocol.confRoot M (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core
        (M.confirmation_time S.E s))) B)
    (hvotes : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s
      (fun X => Block.Preceq B X)) :
    Restated.HonestHeadsAvailableBeforeOn M S rho W Hs Xb s v
      (M.support_cutoff S.E s) := by
  have hroot' : Block.Preceq (M.get_fg_root (M.toHealing
      (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core).toFG) B := by
    have h' := hroot
    rw [Restated.Vocabulary.Protocol.confRoot, Restated.Vocabulary.Proofs.Optimistic.tickStore,
      facts.fc.get_fg_root_toHealing_clock] at h'
    exact h'
  exact honestHeadsAvailableBefore_core₅₄s facts S Hs Xb hf hHs hHsXb hv hpost hhor
    (facts.sch.Sts_support_cutoff_le_confirmation_time S.E s) hroot' hvotes

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- Under the hypotheses of `honestHeadsAvailableBefore_of_postHealingConeOn`, every head voted
    along `W` by a committee member of `s` in the set for its confirmation time resolves in `v`'s
    confirmation store at `confirmation_time s`. -/
theorem headsResolveIn_confStore_of_postHealingConeOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {s : Slot} {v : V} (hv : v ∈ Hs (M.support_cutoff S.E s))
    (hpost : lo ≤ M.vote_time S.E s)
    (hhor : M.support_cutoff S.E s ≤ rho.horizon)
    {B : Block V}
    (hroot : Block.Preceq
      (Restated.Vocabulary.Protocol.confRoot M (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core
        (M.confirmation_time S.E s))) B)
    (hvotes : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s
      (fun X => Block.Preceq B X)) :
    Restated.HeadsResolveInOn M S rho W Hs Xb s
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core
        (M.confirmation_time S.E s)).T
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core
        (M.confirmation_time S.E s)).timestamp_block := by
  exact Restated.headsResolveIn_confStore_of_availableBeforeOn facts S Hs Xb hf (hHsXb _ hv) s
    (Restated.honestHeadsAvailableBefore_of_postHealingConeOn facts
      S Hs Xb hf hHs hHsXb hv hpost hhor hroot hvotes)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- If the proposer of `s + 1` is in the set for slot `s`'s support cutoff, `lo ≤ vote_time s`, the
    support cutoff is inside the horizon, the FG root of the proposer's duty store at
    `proposal_time (s + 1)` is an ancestor of `B`, and every committee member of `s` in the set for
    its vote time voted along `W` a run block with `B` as an ancestor, then every head voted by a
    committee member of `s` in the set for its confirmation time is genesis or admitted by the
    proposer before the support cutoff. -/
theorem honestHeadsAvailableBefore_of_proposerDutyPostHealingConeOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {s : Slot}
    (hprop : S.E.proposer (s + 1) ∈ Hs (M.support_cutoff S.E s))
    (hpost : lo ≤ M.vote_time S.E s)
    (hhor : M.support_cutoff S.E s ≤ rho.horizon)
    {B : Block V}
    (hroot : Block.Preceq
      (M.get_fg_root
        (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).st.core
          (M.proposal_time S.E (s + 1)))).toFG) B)
    (hvotes : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s
      (fun X => Block.Preceq B X)) :
    Restated.HonestHeadsAvailableBeforeOn M S rho W Hs Xb s (S.E.proposer (s + 1))
      (M.support_cutoff S.E s) := by
  have hroot' : Block.Preceq (M.get_fg_root (M.toHealing
      (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).st.core).toFG)
      B := by
    have h' := hroot
    rw [Restated.Vocabulary.Proofs.Optimistic.tickStore] at h'
    erw [facts.fc.get_fg_root_toHealing_clock] at h'
    exact h'
  exact honestHeadsAvailableBefore_core₅₄s facts S Hs Xb hf hHs hHsXb hprop hpost hhor
    (facts.sch.support_cutoff_le_proposal_time_succ S.E s) hroot' hvotes

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- Under the hypotheses of `honestHeadsAvailableBefore_of_proposerDutyPostHealingConeOn`, every
    head voted along `W` by a committee member of `s` in the set for its confirmation time resolves
    in the duty store of the proposer of `s + 1`. -/
theorem headsResolveIn_proposerDutyStore_of_postHealingConeOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {s : Slot}
    (hpost : lo ≤ M.vote_time S.E s)
    (hhor : M.support_cutoff S.E s ≤ rho.horizon)
    (hprop : S.E.proposer (s + 1) ∈ Hs (M.support_cutoff S.E s))
    {B : Block V}
    (hroot : Block.Preceq
      (M.get_fg_root
        (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).st.core
          (M.proposal_time S.E (s + 1)))).toFG) B)
    (hvotes : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s
      (fun X => Block.Preceq B X)) :
    Restated.HeadsResolveInOn M S rho W Hs Xb s
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).st.core
        (M.proposal_time S.E (s + 1))).T
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).st.core
        (M.proposal_time S.E (s + 1))).timestamp_block := by
  have havailable := Restated.honestHeadsAvailableBefore_of_proposerDutyPostHealingConeOn facts
    S Hs Xb hf hHs hHsXb hprop hpost hhor hroot hvotes
  have hresolve := Restated.headsResolveIn_storeBeforeTime_of_availableBefore_atOn facts
    S Hs Xb hf (hHsXb _ hprop) s (facts.sch.support_cutoff_le_proposal_time_succ S.E s) havailable
  rw [tickStore_T₅₄s facts, tickStore_timestamp_block₅₄s facts]
  exact hresolve

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Statements.Instantiation

/-- If `v ∈ Xb`, `B` is a run block read through `Xb` along `W`, `c` is an outcome of the phase tick
    on `v`'s node state before slot `s`'s confirmation time, and `B.erase` is in the candidate tree
    of the read staged from that node state with `c`, then that read finds `B.erase` by its root. -/
theorem find?_eq_some_confStore_of_candidateOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {s : Slot} {v : V} (hv : v ∈ Xb) {B : NamedBlock V}
    (_hBrun : Restated.blockInRunOn M S rho W Xb B)
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core.toHealing
      (M.confirmation_time S.E s) (W (strictEventIndex rho (M.confirmation_time S.E s)) v).cache ⇢ c)
    (hB : B.erase ∈ Restated.Vocabulary.Protocol.confTree M
      (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st
        (M.confirmation_time S.E s)) (W (strictEventIndex rho (M.confirmation_time S.E s)) v).record
        c).st.core) :
    Block.find? (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st
        (M.confirmation_time S.E s)) (W (strictEventIndex rho (M.confirmation_time S.E s)) v).record
        c).st.core.T B.erase.root =
      some B.erase := by
  rw [facts.nd.mkNode_st] at hB ⊢
  try simp only [facts.nd.store_with_cache_bodies, confTree_swc₅₄s facts, confRoot_swc₅₄s facts, confLate_swc₅₄s facts, confVotes_swc₅₄s facts, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at hB ⊢
  try rw [setClock_core_tickStore₅₄s facts S] at hB
  try rw [setClock_core_tickStore₅₄s facts S] at ⊢
  exact Restated.confFind_of_candidateOn facts S Hs Xb hf hv hB

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Statements.Instantiation

/-- If more than half of every slot's committee is in the set for its confirmation time, `0 < s`,
    `lo ≤ vote_time s`, `B` is a run block every committee member of `s` in the set for its vote
    time voted, `v` is in the set for `s`'s support cutoff, and `B` is in the candidate tree of
    `v`'s confirmation read and a descendant of its FG root, then for every outcome of the
    confirmation votes of that read, the committee members of `s` in the set for its confirmation
    time support `B`. -/
theorem honestSupport_confVotes_after_gst_of_namesOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {s : Slot} (hs : 0 < s)
    (hpost : lo ≤ M.vote_time S.E s)
    (hhor : M.confirmation_time S.E s ≤ rho.horizon)
    {B : NamedBlock V} (hBrun : Restated.blockInRunOn M S rho W Xb B)
    (hnames : Restated.NamedHonestVotesNameOn M S rho W Hs s B.erase)
    {v : V} (hv : v ∈ Hs (M.support_cutoff S.E s))
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core.toHealing
      (M.confirmation_time S.E s) (W (strictEventIndex rho (M.confirmation_time S.E s)) v).cache ⇢ c)
    (hroot : Block.Preceq
      (M.get_fg_root
        (M.toHealing (M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st (M.confirmation_time S.E s))
          (W (strictEventIndex rho (M.confirmation_time S.E s)) v).record c).st.core).toFG) B.erase)
    (hcandidate : B.erase ∈ Restated.Vocabulary.Protocol.confTree M
      (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st (M.confirmation_time S.E s))
        (W (strictEventIndex rho (M.confirmation_time S.E s)) v).record c).st.core) :
    ∀ cv, Restated.Vocabulary.Internal.confirmationVotes M S.E
        (M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st (M.confirmation_time S.E s))
          (W (strictEventIndex rho (M.confirmation_time S.E s)) v).record c).st.core s ⇢ cv →
    HonestSupport S.E
      (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st (M.confirmation_time S.E s))
        (W (strictEventIndex rho (M.confirmation_time S.E s)) v).record c).st.core.T
      cv s (Hs (M.confirmation_time S.E s)) B.erase := by
  have hfind := Restated.find?_eq_some_confStore_of_candidateOn facts S Hs Xb hf (hHsXb _ hv) hBrun
    c hc hcandidate
  intro cv hcv
  rw [facts.nd.mkNode_st] at hroot hcandidate hcv hfind ⊢
  try simp only [facts.nd.store_with_cache_bodies, confTree_swc₅₄s facts, confRoot_swc₅₄s facts, confLate_swc₅₄s facts, confVotes_swc₅₄s facts, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at hroot hcandidate hcv hfind ⊢
  try rw [setClock_core_tickStore₅₄s facts S] at hroot
  try rw [setClock_core_tickStore₅₄s facts S] at hcandidate
  try rw [setClock_core_tickStore₅₄s facts S] at hcv
  try rw [setClock_core_tickStore₅₄s facts S] at hfind
  try rw [setClock_core_tickStore₅₄s facts S] at ⊢
  have hcv' := confVotes_of_confirmationVotes₅₄s S.E _ s cv hcv
  try rw [confVotes_swc₅₄s facts, setClock_core_tickStore₅₄s facts S] at hcv'
  have hvotes : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s
      (fun X => Block.Preceq B.erase X) :=
    Restated.honestVotesCone_preceqOn facts S rho W Hs Xb s hBrun hnames
  have hresolve := Restated.headsResolveIn_confStore_of_postHealingConeOn facts
    S Hs Xb hf hHs hHsXb hv hpost
      (le_trans (facts.sch.Sts_support_cutoff_le_confirmation_time S.E s) hhor)
      hroot hvotes
  have hsupport : HonestSupport S.E
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core
        (M.confirmation_time S.E s)).T
      cv s (Hs (M.confirmation_time S.E s)) B.erase := by
    apply Restated.honestSupport_of_namesOn facts S rho W Hs s B.erase hcom hHs hnames hfind cv hcv'
    intro u hus huHon huCommittee hemit
    have huVote : u.val_index ∈ Hs (M.vote_time S.E s) :=
      hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E s) huHon
    have hnamed := hnames u.val_index huVote huCommittee
    have hueq : u = ⟨u.val_index, s, B.erase.root⟩ :=
      Restated.emits_gfVote_uniqueOn facts S Hs Xb hf hemit hnamed
        (by simpa only using hus)
    have hresolvedB := hresolve B.erase
      ⟨u.val_index, huHon, huCommittee, ⟨B, rfl, hBrun⟩, hnamed⟩
    have harr : Proofs.Optimistic.HeadArrivesBefore
        (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core
          (M.confirmation_time S.E s)).T
        (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core
          (M.confirmation_time S.E s)).timestamp_block
        (M.support_cutoff S.E s) u := by
      refine ⟨B.erase, ?_, hresolvedB.2⟩
      rw [hueq]
      simpa only using hresolvedB.1
    exact Restated.canonicalSuffixHonestVoteCountedOn facts
      S Hs Xb hf hHs hHsXb hs hpost hhor v hv u hus huHon hemit harr cv hcv'
  exact hsupport

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Statements.Instantiation

/-- If more than half of every slot's committee is in the set for its confirmation time, `0 < s`,
    `lo ≤ vote_time s`, `lo ≤ proposal_time s`, the proposer of `s` is in the set for
    `confirmation_time s` and proposed `B` along `W`, the committee's vote stores extend `B`, and
    every reader in that set has the local confirmation facts for `B`, then every such reader's
    `live_confirmed` in `W (inclusiveEventIndex rho (confirmation_time s))` is `B.erase`. -/
theorem proposedBlock_liveConfirmed_after_gst_of_localReadsOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {s : Slot} (hs : 0 < s)
    (hpost : lo ≤ M.vote_time S.E s)
    (hhor : M.confirmation_time S.E s ≤ rho.horizon)
    (hprop : S.E.proposer s ∈ Hs (M.confirmation_time S.E s))
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core.toHealing
      (M.proposal_time S.E s)
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).cache ⇢ c)
    {B : NamedBlock V}
    (hB : M.proposal_with (M.gradeContract c)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc (S.node (S.E.proposer s))
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
        (M.proposal_time S.E s)) ⇢ some B)
    (hstores : Restated.VoteStoresExtendOn M S rho Hs s
      (W (strictEventIndex rho (M.vote_time S.E s))) B)
    (hread : ∀ v ∈ Hs (M.confirmation_time S.E s), ∀ cc : M.Cache,
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core.toHealing
        (M.confirmation_time S.E s)
        (W (strictEventIndex rho (M.confirmation_time S.E s)) v).cache ⇢ cc →
      let n := M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st (M.confirmation_time S.E s))
        (W (strictEventIndex rho (M.confirmation_time S.E s)) v).record cc
      Block.Preceq (M.get_fg_root (M.toHealing n.st.core).toFG) B.erase ∧
        (∀ A, Restated.Vocabulary.Internal.namedConfirmationAnchor M S n ⇢ A →
          Block.Preceq A B.erase) ∧
        B.erase ∈ Restated.Vocabulary.Protocol.confTree M n.st.core)
    (hgat : lo ≤ M.proposal_time S.E s)
    (hrunVote : ∀ v ∈ Hs (M.vote_time S.E s), v ∈ S.E.committee s →
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick v (M.vote_time S.E s)) →
        M.awake_for_grade1 S v (W j v) (M.round_of S.hc s))
    (hrunProp : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick (S.E.proposer s) (M.proposal_time S.E s)) →
      M.awake_for_grade1 S (S.E.proposer s) (W j (S.E.proposer s)) (M.round_of S.hc s))
    (hrunConf : ∀ v ∈ Hs (M.confirmation_time S.E s),
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick v (M.confirmation_time S.E s)) →
        M.awake_for_grade2 (Setup.alwaysAwake S) v (W j v) (M.round_of S.hc (s + 1))) :
    ∀ v ∈ Hs (M.confirmation_time S.E s),
      (W (inclusiveEventIndex rho (M.confirmation_time S.E s)) v).st.live_confirmed =
        B.erase := by
  have hvoteHor : M.vote_time S.E s ≤ rho.horizon :=
    (facts.sch.Protocol_vote_time_le_confirmation_time S.E s).trans hhor
  have hnames := Restated.honestVotesName_of_voteStoresExtendOn facts
    S Hs Xb hf hs hvoteHor hpost hstores (fun _ _ _ j hj => hf.tick_outcome j _ _ hj) hrunVote
  have hBrun : Restated.blockInRunOn M S rho W Xb B :=
    Restated.proposedBlockAt_blockInRun_of_admissibleOn facts S Hs Xb hf hHs hHsXb s hs hprop
      ((facts.sch.proposal_time_le_confirmation_time S.E s).trans hhor) hgat
      (fun j hj => hf.tick_outcome j _ _ hj) hrunProp c hc hB
  intro v hv
  have hvCut : v ∈ Hs (M.support_cutoff S.E s) :=
    hHs _ _ (facts.sch.Sts_support_cutoff_le_confirmation_time S.E s) hv
  have hlocal := hread v hv
  set tc := M.confirmation_time S.E s with htc
  set wv := W (strictEventIndex rho tc) v with hwv
  obtain ⟨cc, hcc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc wv.st.core.toHealing tc wv.cache
  have hwmem := mem_stateBeforeTime_along₅₄s hf.sorted hf.onePath tc
  obtain ⟨hroot, hanchorAll, hcand⟩ := hlocal cc hcc
  obtain ⟨A, hA⟩ := facts.fc.get_sg_root_with_nonempty (M.gradeContract cc) S.E S.hc
    (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S wv.st.core tc))
    (M.round_of S.hc (Restated.Vocabulary.Proofs.Optimistic.tickStore M S wv.st.core tc).s)
  have hAnamed : Restated.Vocabulary.Internal.namedConfirmationAnchor M S
      (M.mkNode (M.ns_setClock S.E wv.st tc) wv.record cc) ⇢ A := by
    rw [Restated.Vocabulary.Internal.namedConfirmationAnchor, facts.nd.mkNode_cache, facts.nd.mkNode_st,
      sgRoot_store_with_cache₅₄s facts, facts.nd.store_with_cache_core_s, setClock_core_tickStore₅₄s facts S]
    exact hA
  have hanchor := hanchorAll A hAnamed
  have hpath := Restated.Vocabulary.Protocol.confPath_of_candidate facts S (B := B) _ hwmem cc hcc
    (by simpa only [facts.nd.mkNode_st, setClock_core_tickStore₅₄s facts S, confTree_swc₅₄s facts, confRoot_swc₅₄s facts, confLate_swc₅₄s facts, confVotes_swc₅₄s facts, facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] using hcand) A hAnamed
  obtain ⟨votes, hvotes⟩ := confVotes_nonempty₅₄s facts S.E
    (M.mkNode (M.ns_setClock S.E wv.st tc) wv.record cc).st.core s
  have hsupport := Restated.honestSupport_confVotes_after_gst_of_namesOn facts
    S Hs Xb hf hHs hHsXb hcom hs hpost hhor hBrun hnames hvCut cc hcc hroot hcand votes hvotes
  rw [facts.nd.mkNode_st] at hsupport hvotes
  try simp only [facts.nd.store_with_cache_bodies, confTree_swc₅₄s facts, confRoot_swc₅₄s facts, confLate_swc₅₄s facts, confVotes_swc₅₄s facts, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at hsupport hvotes
  try rw [setClock_core_tickStore₅₄s facts S] at hsupport
  try rw [setClock_core_tickStore₅₄s facts S] at hvotes
  have hvalid : Protocol.VoteSetValid S.E s
      (Restated.Vocabulary.Protocol.confLate M S.E
        (Restated.Vocabulary.Proofs.Optimistic.tickStore M S wv.st.core tc) s) := by
    rw [confLate_tickStore₅₄s facts S]
    exact Restated.voteSetValid_confLate_stateBeforeTimeOn facts S Hs Xb hf v tc s
  have hgatConf : lo ≤ tc :=
    hpost.trans (facts.sch.Protocol_vote_time_le_confirmation_time S.E s)
  obtain ⟨D, hD⟩ := facts.dt.duties_update_confirmation_with_nonempty (M.gradeContract cc) S.E S.hc
    (M.ns_setClock S.E wv.st tc) s
  obtain ⟨X, hX⟩ := facts.dt.update_confirmation_with_nonempty (M.gradeContract cc) S.E S.hc
    (M.ns_setClock S.E wv.st tc).core s
  have hDX := facts.dt.namedDuties_update_confirmation_with_core _ _ _ _ _ D hD X hX
  have hXcore : (M.ns_setClock S.E wv.st tc).core =
      Restated.Vocabulary.Proofs.Optimistic.tickStore M S wv.st.core tc :=
    facts.hd.setClock_core_eq_store_with_t_s S.E wv.st tc
  rw [hXcore] at hX
  have hXlive := Restated.Vocabulary.Protocol.live_confirmed_eq_with facts (M.gradeContract cc)
    S.E S.hc _ s (Hs tc) B.erase votes hvotes hsupport hvalid A hA hanchor hpath X hX
  rw [Restated.live_confirmed_eq_updateOn facts S Hs Xb hf s hv hhor hgatConf
    (fun j hj => hf.tick_outcome j _ _ hj) (hrunConf v hv) cc hcc D hD]
  rw [← hXlive, ← hDX]
  rfl

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Statements.Instantiation

/-- The form of `proposedBlock_liveConfirmed_after_gst_of_localReadsOn` at round `r`'s opening slot,
    whose confirmation time is `S.a r`: every node state of the round-`r` action read of every
    reader in the set for `S.a r` has `live_confirmed = B.erase`. -/
theorem openingProposal_liveConfirmed_actionStore_after_gst_of_localReadsOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {r : Round} (hr : 0 < r)
    (hpost : lo ≤
      M.vote_time S.E ((M.opening_slot S.hc r)))
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon)
    (hprop : S.E.proposer ((M.opening_slot S.hc r)) ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)))
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc r)))
        (S.E.proposer (M.opening_slot S.hc r))).st.core.toHealing
      (M.proposal_time S.E (M.opening_slot S.hc r))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc r)))
        (S.E.proposer (M.opening_slot S.hc r))).cache ⇢ c)
    {B : NamedBlock V}
    (hB : M.proposal_with (M.gradeContract c)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc (S.node (S.E.proposer (M.opening_slot S.hc r)))
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc r)))
        (S.E.proposer (M.opening_slot S.hc r))).st
        (M.proposal_time S.E (M.opening_slot S.hc r))) ⇢ some B)
    (hstores : Restated.VoteStoresExtendOn M S rho Hs ((M.opening_slot S.hc r))
      (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc r)))) B)
    (hread : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)), ∀ cc : M.Cache,
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc r))) v).st.core.toHealing
        (M.confirmation_time S.E (M.opening_slot S.hc r))
        (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc r))) v).cache ⇢ cc →
      let n := M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc r))) v).st
          (M.confirmation_time S.E (M.opening_slot S.hc r)))
        (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc r))) v).record cc
      Block.Preceq (M.get_fg_root (M.toHealing n.st.core).toFG) B.erase ∧
        (∀ A, Restated.Vocabulary.Internal.namedConfirmationAnchor M S n ⇢ A →
          Block.Preceq A B.erase) ∧
        B.erase ∈ Restated.Vocabulary.Protocol.confTree M n.st.core)
    (hgat : lo ≤ M.proposal_time S.E ((M.opening_slot S.hc r)))
    (hrunVote : ∀ v ∈ Hs (M.vote_time S.E (M.opening_slot S.hc r)), v ∈ S.E.committee (M.opening_slot S.hc r) →
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick v (M.vote_time S.E (M.opening_slot S.hc r))) →
        M.awake_for_grade1 S v (W j v) (M.round_of S.hc (M.opening_slot S.hc r)))
    (hrunProp : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick (S.E.proposer (M.opening_slot S.hc r))
        (M.proposal_time S.E (M.opening_slot S.hc r))) →
      M.awake_for_grade1 S (S.E.proposer (M.opening_slot S.hc r)) (W j (S.E.proposer (M.opening_slot S.hc r)))
        (M.round_of S.hc (M.opening_slot S.hc r)))
    (hrunConf : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)),
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick v (M.confirmation_time S.E (M.opening_slot S.hc r))) →
        M.awake_for_grade2 (Setup.alwaysAwake S) v (W j v) (M.round_of S.hc (M.opening_slot S.hc r + 1))) :
    ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r,
      n.st.core.live_confirmed = B.erase := by
  have hs : 0 < (M.opening_slot S.hc r) := facts.gr.opening_slot_pos_of_round_pos S.hc hr
  have hconf : M.confirmation_time S.E
      ((M.opening_slot S.hc r)) = (Restated.Vocabulary.Execution.Setup.a M S r) :=
    (Restated.Vocabulary.Protocol.a_eq_confirmation_time facts S.hc S.E r).symm
  have hall := Restated.proposedBlock_liveConfirmed_after_gst_of_localReadsOn facts
    S Hs Xb hf hHs hHsXb hcom hs hpost (by rw [hconf]; exact hhor)
      (by rw [hconf]; exact hprop) c hc hB hstores
      (fun v hv => hread v (by rw [← hconf]; exact hv)) hgat hrunVote hrunProp
      (fun v hv => hrunConf v (by rw [← hconf]; exact hv))
  intro v hv n hn
  have hvConf : v ∈ Hs (M.confirmation_time S.E ((M.opening_slot S.hc r))) := by
    rw [hconf]; exact hv
  have hrecorded := hall v hvConf
  have hslot : S.E.slotOf ((Restated.Vocabulary.Execution.Setup.a M S r)) - 1 = (M.opening_slot S.hc r) := by
    have hsc : (Restated.Vocabulary.Execution.Setup.a M S r) =
        M.support_cutoff S.E ((M.opening_slot S.hc r) + 1) :=
      Restated.Vocabulary.Protocol.a_eq_support_cutoff_succ facts S.hc S.E r
    rw [hsc, facts.sch.slotOf_support_cutoff]
    exact Nat.add_sub_cancel ((M.opening_slot S.hc r)) 1
  obtain ⟨c', hc', st, hst, rfl⟩ := hn
  rw [hslot] at hst
  rw [← hconf] at hc' hst
  have hbridge := Restated.live_confirmed_eq_updateOn facts S Hs Xb hf
      ((M.opening_slot S.hc r)) hvConf
      (by rw [hconf]; exact hhor)
      (hpost.trans (facts.sch.Protocol_vote_time_le_confirmation_time S.E _))
      (fun j hj => hf.tick_outcome j _ _ hj) (hrunConf v hv) c' hc' st hst
  rw [hrecorded] at hbridge
  rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
  exact hbridge.symm

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- If more than half of every slot's committee is in the set for its confirmation time, `0 < s`,
    `lo ≤ vote_time s`, `v` is in the set for `s`'s support cutoff, every committee member of `s` in
    the set for its vote time voted along `W` a run block with `B.erase` as an ancestor, and the FG
    root and every confirmation anchor of `v`'s confirmation read are ancestors of `B.erase`, which
    is in its candidate tree, then for every outcome `D` of `v`'s confirmation update,
    `GenuineConfirmationWith` holds of `D.live_confirmed` and `B.erase ⪯ D.live_confirmed`. -/
theorem genuineConfirmationAndPreceq_of_postHealingConeOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {s : Slot} (hs : 0 < s)
    (hpost : lo ≤ M.vote_time S.E s)
    (hhor : M.confirmation_time S.E s ≤ rho.horizon)
    {v : V} (hv : v ∈ Hs (M.support_cutoff S.E s)) {B : NamedBlock V}
    (hvotes : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s
      (fun X => Block.Preceq B.erase X))
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core.toHealing
      (M.confirmation_time S.E s) (W (strictEventIndex rho (M.confirmation_time S.E s)) v).cache ⇢ c)
    (hroot : Block.Preceq
      (M.get_fg_root
        (M.toHealing (M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st (M.confirmation_time S.E s))
          (W (strictEventIndex rho (M.confirmation_time S.E s)) v).record c).st.core).toFG) B.erase)
    (hanchor : ∀ A, Restated.Vocabulary.Internal.namedConfirmationAnchor M S
      (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st (M.confirmation_time S.E s))
        (W (strictEventIndex rho (M.confirmation_time S.E s)) v).record c) ⇢ A →
      Block.Preceq A B.erase)
    (hcandidate : B.erase ∈ Restated.Vocabulary.Protocol.confTree M
      (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st (M.confirmation_time S.E s))
        (W (strictEventIndex rho (M.confirmation_time S.E s)) v).record c).st.core) :
    ∀ D : M.S, M.update_confirmation_with (M.gradeContract c) S.E S.hc
        (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core
          (M.confirmation_time S.E s)) s ⇢ D →
    Restated.Vocabulary.Protocol.GenuineConfirmationWith M (M.gradeContract c) S.E S.hc
        (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core
          (M.confirmation_time S.E s)) s D.live_confirmed ∧
      Block.Preceq B.erase D.live_confirmed := by
  have hcut : M.support_cutoff S.E s ≤ rho.horizon :=
    le_trans (facts.sch.Sts_support_cutoff_le_confirmation_time S.E s) hhor
  set tc := M.confirmation_time S.E s with htc
  set wv := W (strictEventIndex rho tc) v with hwv
  set st := Restated.Vocabulary.Proofs.Optimistic.tickStore M S wv.st.core tc with hst
  have hwmem := mem_stateBeforeTime_along₅₄s hf.sorted hf.onePath tc
  rw [facts.nd.mkNode_st] at hroot hcandidate
  try simp only [facts.nd.store_with_cache_bodies, confTree_swc₅₄s facts, confRoot_swc₅₄s facts, confLate_swc₅₄s facts, confVotes_swc₅₄s facts, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at hroot hcandidate
  try rw [setClock_core_tickStore₅₄s facts S] at hroot
  try rw [setClock_core_tickStore₅₄s facts S] at hcandidate
  have hresolve := Restated.headsResolveIn_confStore_of_postHealingConeOn facts
    S Hs Xb hf hHs hHsXb hv hpost hcut hroot hvotes
  have hsupport := Restated.coneSupport_confVotes_after_gstOn facts
    S Hs Xb hf hHs hHsXb hcom hs hpost hhor hvotes hv hresolve
  have hvalid : Protocol.VoteSetValid S.E s (Restated.Vocabulary.Protocol.confLate M S.E st s) := by
    rw [hst, confLate_tickStore₅₄s facts S]
    exact Restated.voteSetValid_confLate_stateBeforeTimeOn facts S Hs Xb hf v tc s
  have hAnamed : ∀ A, Restated.Vocabulary.Protocol.confAnchorWith M (M.gradeContract c) S.E S.hc st ⇢ A →
      Restated.Vocabulary.Internal.namedConfirmationAnchor M S
        (M.mkNode (M.ns_setClock S.E wv.st tc) wv.record c) ⇢ A := by
    intro A hA
    rw [Restated.Vocabulary.Internal.namedConfirmationAnchor, facts.nd.mkNode_cache, facts.nd.mkNode_st,
      sgRoot_store_with_cache₅₄s facts, facts.nd.store_with_cache_core_s, setClock_core_tickStore₅₄s facts S]
    exact hA
  have helig : ∀ A, Restated.Vocabulary.Protocol.confAnchorWith M (M.gradeContract c) S.E S.hc st ⇢ A →
      ∀ u, Restated.Vocabulary.Protocol.confVotes M S.E st s ⇢ u →
      ∀ sc : Block V → Nat, (∀ B', M.goldfish_score S.E st.T u u s B' ⇢ sc B') →
      ∀ H, M.ghost A (Restated.Vocabulary.Protocol.confTree M st) sc
          (fun B' => decide (Restated.Vocabulary.Protocol.confCount M S.E st s < 2 * sc B')) ⇢ H →
      Block.Preceq B.erase H ∧
        decide (Restated.Vocabulary.Protocol.confCount M S.E st s < 2 * sc H) = true := by
    intro A hA u hu sc hsc H hH
    have hcs := hsupport u hu
    have hAB : Block.Preceq A B.erase := hanchor A (hAnamed A hA)
    have hpath := Restated.Vocabulary.Protocol.confPath_of_candidate facts S (B := B) _ hwmem c hc
      hcandidate A (hAnamed A hA)
    have hpass : Block.Preceq B.erase H :=
      facts.fc.ghost_passes_cone S.E st.T (Restated.Vocabulary.Protocol.confTree M st) u u
        (Restated.Vocabulary.Protocol.confLate M S.E st s) s (Hs tc)
        hcs.majority hcs.counted hcs.sub hcs.no_equiv hcs.vote hvalid hAB hpath sc hsc H hH
    refine ⟨hpass, ?_⟩
    rcases facts.fc.ghost_eligible A (Restated.Vocabulary.Protocol.confTree M st) sc _ H hH with
      hEq | hel
    · subst hEq
      exact decide_eq_true
        (facts.fc.ConeSupport_eligible S.E st.T u u (Restated.Vocabulary.Protocol.confLate M S.E st s)
          s (Hs tc) (fun X => Block.Preceq B.erase X)
          hcs.majority hcs.counted hcs.sub hcs.no_equiv hcs.vote hvalid
          (fun X hX => preceq_eq_true_iff_Preceq.mpr (preceq_trans_Preceq hAB hX)) (sc H) (hsc H))
    · exact hel
  intro D hD
  obtain ⟨tm, htm⟩ := facts.sto.tau_nonempty st
  obtain ⟨A, hA⟩ := facts.fc.get_sg_root_with_nonempty (M.gradeContract c) S.E S.hc
    (M.toHealing st) (M.round_of S.hc st.s)
  have hu : Restated.Vocabulary.Protocol.confVotes M S.E st s ⇢
      ((_root_.DecoupledConsensusModel.beforeCutoff tm (M.support_cutoff S.E s) (st.pool s)).filter
        (fun u => M.no_second_vote_in
          (_root_.DecoupledConsensusModel.beforeCutoff st.timestamp_vote tc (st.pool s)) u = true)) :=
    returns_map_intro₅₄s _ _ _ (returns_map_intro₅₄s _ _ _ htm)
  have hscore : ∀ B' : Block V, ∃ g, M.goldfish_score S.E st.T
      ((_root_.DecoupledConsensusModel.beforeCutoff tm (M.support_cutoff S.E s) (st.pool s)).filter
        (fun u => M.no_second_vote_in
          (_root_.DecoupledConsensusModel.beforeCutoff st.timestamp_vote tc (st.pool s)) u = true))
      ((_root_.DecoupledConsensusModel.beforeCutoff tm (M.support_cutoff S.E s) (st.pool s)).filter
        (fun u => M.no_second_vote_in
          (_root_.DecoupledConsensusModel.beforeCutoff st.timestamp_vote tc (st.pool s)) u = true))
      s B' ⇢ g :=
    fun B' => facts.fc.goldfish_score_nonempty _ _ _ _ _ _
  choose sc hsc using hscore
  obtain ⟨H, hH⟩ := facts.fc.ghost_nonempty A (Restated.Vocabulary.Protocol.confTree M st) sc
    (fun B' => decide (Restated.Vocabulary.Protocol.confCount M S.E st s < 2 * sc B'))
  obtain ⟨hpassH, heligH⟩ := helig A hA _ hu sc hsc H hH
  have hlive := facts.hd.update_confirmation_with_live_confirmed_of_eligible (M.gradeContract c)
    S.E S.hc st s tm htm A hA sc hsc H hH heligH
  have hDH : D.live_confirmed = H := hlive D hD
  refine ⟨⟨fun st' hst' => by rw [hlive st' hst', hDH], ?_⟩, by rw [hDH]; exact hpassH⟩
  intro A' hA' u' hu' sc' hsc' H' hH'
  exact (helig A' hA' u' hu' sc' hsc' H' hH').2

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Statements.Instantiation

end

end DecoupledConsensusModel.Sts.Restated
