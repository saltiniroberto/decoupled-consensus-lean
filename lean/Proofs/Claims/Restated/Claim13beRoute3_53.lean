import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13beRoute3_45
import Proofs.Claims.Restated.Claim13beRoute3_45b
import Proofs.Claims.Restated.Claim13beRoute3_46
import Proofs.Claims.Restated.Claim13beRoute3_48
import Proofs.Claims.Restated.Claim13beRoute3_48b
import Proofs.Claims.Restated.Claim13beRoute3_49
import Proofs.Claims.Restated.Claim13beRoute3_50b
import Proofs.Claims.Restated.Claim13beRoute3_51
import Proofs.Claims.Restated.Claim13beRoute3_52
import Proofs.Claims.Restated.Vocabulary_Execution_Acceptance
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_ProposalBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Evidence_ProvenanceBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_Anchor
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_BlockAdmission
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_HMaxMonotone
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_42c
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.RunVocabulary
import Model.Conditions.Vocabulary_Internal_Internal_GradeReads
import Model.Conditions.Vocabulary_Internal_Invariants
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedReceiptCalls
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Objects
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_ModelVocabulary_Healing_Schedule
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Model.Conditions.Vocabulary_Protocol_Grades_LegacyVocabulary
import Model.Conditions.Vocabulary_Protocol_Handlers_Blocks
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_25
import Proofs.Claims.Spec2Claims.Claim13beRoute3_53

/-!
# Grade 2 from the previous round's action votes, and timing facts

Theorems read along the path `W` of a run satisfying `AdmissibleFieldsOn`, over a model
`M : Record.Model V` and its facts: a reader's grade view of round `r + 1` resolves the action votes
of round `r` and grades their common ancestor at 2, the largest `h_max` over the sets does not fall
across one delay, and inequalities between the instants of the schedule.
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

/-- Along the path `W` of the bundle, `W (strictEventIndex rho t)` is a world strictly before `t`. -/
private theorem mem_stateBeforeTime_along₅₃ (facts : Record.Facts M) {S : Setup V}
    {rho : Record.Run V}
    {Hs : Int → Finset V} {Xb : Finset V} {lo : Int} {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo) (t : Time) :
    W (strictEventIndex rho t) ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t := by
  rw [Restated.stateBeforeTime_eq_stateBefore_strictEventIndexOn facts S Hs Xb hf t]
  exact (hf.onePath _).1

/-- Along a path `W` of `rho`, `W (m + k)` is among the worlds the events `m` to `m + k - 1` lead to
    from `W m`. -/
private theorem onePath_reach₅₃ {S : Setup V} {rho : Record.Run V}
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
private theorem onePath_slice₅₃ {S : Setup V} {rho : Record.Run V}
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) {m n : Nat}
    (hmn : m ≤ n) :
    W n ∈ ((rho.events.drop m).take (n - m)).foldlM (Record.worldStepOf M S) (W m) := by
  have h := onePath_reach₅₃ W hW m (n - m)
  rwa [Nat.add_sub_of_le hmn] at h

/-- Along a path `W`, for `j ≤ n`, `v`'s finalized block in `W j` is an ancestor of its finalized
    block in `W n`. -/
private theorem F_mono_along₅₃ (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (v : V)
    {j n : Nat} (hjn : j ≤ n) : Block.Preceq (W j v).st.core.F (W n v).st.core.F :=
  Restated.Vocabulary.Protocol.stateBefore_F_mono facts S rho v hjn (W j) (hW j).1 (W n)
    (onePath_slice₅₃ W hW hjn)

/-- Along a path `W`, for `j ≤ n`, `v`'s `h_max` in `W j` is at most its `h_max` in `W n`. -/
private theorem hMax_mono_along₅₃ (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (v : V)
    {j n : Nat} (hjn : j ≤ n) : (W j v).st.core.h_max ≤ (W n v).st.core.h_max :=
  Restated.Vocabulary.Proofs.HealingSurface.stateBefore_hMax_mono facts S rho v hjn (W j) (hW j).1
    (W n) (onePath_slice₅₃ W hW hjn)

/-- A block of the filtered block tree of a store is a descendant of the store's finalized block. -/
private theorem F_preceq_of_mem_filtered₅₃ (facts : Record.Facts M) (st : M.S) {C : Block V}
    (hC : C ∈ M.get_filtered_block_tree (M.toHealing st).toFG) : Block.Preceq st.F C := by
  have h := facts.fc.finalized_preceq_of_mem_get_filtered_block_tree hC
  rwa [facts.sto.Sts_toHealing_F] at h

/-- The round-`r` action read computed from any node state `before` has a node state. -/
private theorem actionReadFrom_nonempty₅₃ (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∃ n, n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r := by
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc before.st.core.toHealing
    (Restated.Vocabulary.Execution.Setup.a M S r) before.cache
  obtain ⟨st, hst⟩ := facts.dt.duties_update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc
    (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r))
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
  exact ⟨_, c, hc, st, hst, rfl⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- If `w` is in the set for `S.a (r + 1)`, `v` in the set for `S.a r + Δ` and awake at `r`, `B` is
    a block the SG selector can pick in `v`'s action read, `P` is an ancestor of `B` and in the
    filtered tree of `w`'s core store in `W (strictEventIndex rho (S.a (r + 1)))`, and `lo ≤ S.a r`,
    then that store's grade view resolves `⟨v, r, some B.root⟩` before round `r + 1`'s earliest
    grade cutoff, and every outcome of the test whether its head covers `P` is `true`. -/
theorem seedActionRead_resolvedSupport_at_storeOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {r : Round} {P : Block V} {w : V} (hw : w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    {v : V} (hv : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ))
    (n : M.N)
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r)
    (A2 : Option (Block V))
    (hA2 : M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
      (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ A2)
    (B : Block V)
    (hB : M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
      (M.round_of S.hc (M.toHealing n.st.core).s) A2 ⇢ B)
    (hPHv : Block.Preceq P B)
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S r))
    (hcut : Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (r + 1) ≤ rho.horizon)
    (hactiveW : P ∈ M.get_filtered_block_tree
      (M.toHealing (W (strictEventIndex rho
        (Restated.Vocabulary.Execution.Setup.a M S (r + 1))) w).st.core).toFG)
    (hA : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick v (Restated.Vocabulary.Execution.Setup.a M S r)) → M.awake_for_grade2 S v (W j v) r) :
    let gv := M.gradeView (M.toHealing (W (strictEventIndex rho
      (Restated.Vocabulary.Execution.Setup.a M S (r + 1))) w).st.core)
    occurrenceBefore
        (Protocol.sg_resolution_time gv.T gv.timestamp_block gv.timestamp_sg_vote
          (⟨v, r, some B.root⟩ : Protocol.SGVote V))
        (Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (r + 1)) = true ∧
      ∀ b : Bool, M.head_covers gv.T P (some B.root) ⇢ b → b = true := by
  intro gv
  have hrelayRead : (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ ≤
      (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) :=
    le_trans (facts.gr.action_add_delta_le_next_Γ_neg1 S r)
      (le_of_lt (Restated.Vocabulary.Proofs.HealingSurface.next_Γ_neg1_lt_action facts S r))
  have hwΔ : w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ) := hHs _ _ hrelayRead hw
  have hva : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)) :=
    hHs _ _ (le_of_lt (lt_add_of_pos_right _ S.E.Δ_pos)) hv
  have hHsource : B ∈
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).st.core.T :=
    Restated.Vocabulary.Proofs.HealingSurface.actionSGBlockAt_mem_storeBeforeTime facts S rho v r _
      (mem_stateBeforeTime_along₅₃ facts hf _) n hn A2 hA2 B hB
  have hvisible : B ∈
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r + 1))) w).st.T ∧
      stampedBefore
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r + 1))) w).st.timestamp_block
        (Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (r + 1)) B = true := by
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
      have hFP := F_preceq_of_mem_filtered₅₃ facts _ hactiveW
      have hFhist : ∀ j : Nat,
          j ≤ (rho.events.filter (fun e => decide (e.time <
            (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ))).length →
            Block.Preceq (W j w).st.core.F D.erase := by
        intro j hj
        have hjN : j ≤ strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) :=
          le_trans hj (Restated.strict_filter_length_mono rho hrelayRead)
        rw [hDerase]
        exact preceq_trans_Preceq (F_mono_along₅₃ facts S hf.onePath w hjN)
          (preceq_trans_Preceq hFP hPHv)
      have hrelayHor : (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ ≤ rho.horizon :=
        le_trans (facts.gr.action_add_delta_le_next_Γ_neg1 S r) hcut
      have hvmax : v ∈ Hs (max t lo) := hHs _ _ (max_le (le_of_lt ht) hpost) hva
      obtain ⟨C, hCerase, j, t', hacc', ht'⟩ :=
        Restated.block_admittedBefore_of_accepted_after_cutoffOn facts
          S Hs Xb hf hHs hHsXb hvmax hwΔ hHpos hacc ht hpost rfl hrelayHor hFhist
      have hadmitNext : Restated.Vocabulary.Protocol.AdmittedBefore M S rho W w B
          (Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (r + 1)) :=
        ⟨C, hCerase.trans hDerase, j, t', hacc', lt_of_lt_of_le ht'
          (facts.gr.action_add_delta_le_next_Γ_neg1 S r)⟩
      exact Restated.admittedBefore_mem_and_stamp_atOn facts S Hs Xb hf hadmitNext
        (le_of_lt (Restated.Vocabulary.Proofs.HealingSurface.next_Γ_neg1_lt_action facts S r))
  have hvoteStamp := Restated.actionSGVote_stamp_before_next_Γ_neg1On facts S Hs Xb hf hHs r
    hv hwΔ hpost hcut hA n hn A2 hA2 B hB
  obtain ⟨Hn, hHnErase, hHrun⟩ :=
    Restated.runBlock_of_mem_core_T_stateBeforeTimeOn facts S Hs Xb hf (hHsXb _ hw)
      ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) hvisible.1
  have hfind : Block.find? gv.T B.root = some B := by
    apply Proofs.Optimistic.find?_eq_some_of_unique
    · show B ∈ (M.gradeView (M.toHealing (W (strictEventIndex rho
        (Restated.Vocabulary.Execution.Setup.a M S (r + 1))) w).st.core)).T
      rw [facts.gr.Sts_gradeView_T]
      exact hvisible.1
    · intro Y hY hroot
      have hY' : Y ∈ (W (strictEventIndex rho
          (Restated.Vocabulary.Execution.Setup.a M S (r + 1))) w).st.core.T := by
        have h : Y ∈ (M.gradeView (M.toHealing (W (strictEventIndex rho
            (Restated.Vocabulary.Execution.Setup.a M S (r + 1))) w).st.core)).T := hY
        rw [facts.gr.Sts_gradeView_T] at h
        exact h
      obtain ⟨Yn, hYnErase, hYrun⟩ :=
        Restated.runBlock_of_mem_core_T_stateBeforeTimeOn facts S Hs Xb hf (hHsXb _ hw)
          ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) hY'
      have hrootN : Yn.root = Hn.root :=
        (Proofs.NamedWire.erase_root Yn).symm.trans
          (((congrArg Block.root hYnErase).trans hroot).trans
            (congrArg Block.root hHnErase.symm) |>.trans (Proofs.NamedWire.erase_root Hn))
      have hYH := hf.rootCollisionFree.root_injective
        Yn Hn hYrun hHrun Yn Hn
        (Or.inl (Proofs.NamedAncestry.named_self Yn))
        (Or.inr (Proofs.NamedAncestry.named_self Hn)) hrootN
      rw [← hYnErase, hYH]
      exact hHnErase
  have hblock : occurrenceBefore (gv.timestamp_block B)
      (Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (r + 1)) = true := by
    have h := hvisible.2
    rw [stampedBefore_eq_occurrenceBefore] at h
    show occurrenceBefore ((M.gradeView (M.toHealing (W (strictEventIndex rho
        (Restated.Vocabulary.Execution.Setup.a M S (r + 1))) w).st.core)).timestamp_block B) _ = true
    rw [facts.gr.gradeView_timestamp_block]
    exact h
  constructor
  · simp only [Protocol.sg_resolution_time, hfind]
    exact occurrenceBefore_max hvoteStamp hblock
  · exact facts.gr.head_covers_of_find hfind hPHv

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- If `w` and `v` are in the set for `S.a (r + 1)`, `v` is awake at `r`, `lo ≤ S.a r`, and `w`'s
    grade view `gv` of `r + 1` resolves `⟨v, r, some B.root⟩` before round `r + 1`'s earliest grade
    cutoff with a head covering `P`, then `w`'s summary of `v` in `gv` is timed before that cutoff,
    its head covers `P`, and it records no equivocation before the grade-2 cutoff. -/
theorem seedGradeRead_honestSupport_at_storeOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {r : Round} {P : Block V} {w : V} (hw : w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    {v : V} (hv : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S r))
    (hcut : Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (r + 1) ≤ rho.horizon)
    (n : M.N)
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r)
    (A2 : Option (Block V))
    (hA2 : M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
      (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ A2)
    (B : Block V)
    (hB : M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
      (M.round_of S.hc (M.toHealing n.st.core).s) A2 ⇢ B)
    (cov : Block V → Option BlockId → Bool)
    (hcov : Restated.Vocabulary.Protocol.HeadCoversOutcomes M
      (M.gradeView (M.toHealing (W (strictEventIndex rho
        (Restated.Vocabulary.Execution.Setup.a M S (r + 1))) w).st.core)).T cov)
    (hresolved :
      occurrenceBefore
          (Protocol.sg_resolution_time
            (M.gradeView (M.toHealing (W (strictEventIndex rho
              (Restated.Vocabulary.Execution.Setup.a M S (r + 1))) w).st.core)).T
            (M.gradeView (M.toHealing (W (strictEventIndex rho
              (Restated.Vocabulary.Execution.Setup.a M S (r + 1))) w).st.core)).timestamp_block
            (M.gradeView (M.toHealing (W (strictEventIndex rho
              (Restated.Vocabulary.Execution.Setup.a M S (r + 1))) w).st.core)).timestamp_sg_vote
            (⟨v, r, some B.root⟩ : Protocol.SGVote V))
          (Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (r + 1)) = true ∧
        cov P (some B.root) = true)
    (hA : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick v (Restated.Vocabulary.Execution.Setup.a M S r)) → M.awake_for_grade2 S v (W j v) r) :
    let gv := M.gradeView (M.toHealing (W (strictEventIndex rho
      (Restated.Vocabulary.Execution.Setup.a M S (r + 1))) w).st.core)
    occurrenceBefore
        (Restated.Vocabulary.Protocol.summary M gv (r + 1) v).t_v
        (Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (r + 1)) = true ∧
      cov P (Restated.Vocabulary.Protocol.summary M gv (r + 1) v).C_v = true ∧
        occurrenceAtLeast
          (Restated.Vocabulary.Protocol.summary M gv (r + 1) v).e_v
          (Restated.Vocabulary.Protocol.HealConfig.Γ_2 M S.hc S.E.Δ (r + 1)) = true := by
  intro gv
  have hrelayRead : (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) :=
    le_trans (facts.gr.action_add_delta_le_next_Γ_neg1 S r)
      (le_of_lt (Restated.Vocabulary.Proofs.HealingSurface.next_Γ_neg1_lt_action facts S r))
  let u : Protocol.SGVote V := ⟨v, r, some B.root⟩
  let batch := Protocol.sg_votes_by (Restated.Vocabulary.Protocol.round_batch M gv (r + 1)) v
  let tau := Protocol.sg_resolution_time gv.T
    gv.timestamp_block gv.timestamp_sg_vote
  let headed := batch.filter (fun x =>
    x.confirmed.isSome ∧ Protocol.sg_resolved gv.T x = true)
  have huBatch : u ∈ batch :=
    Restated.actionSGVote_mem_next_round_batchOn facts S Hs Xb hf hHs r (hHs _ _ hrelayRead hv)
      (hHs _ _ hrelayRead hw) hpost hcut hA n hn A2 hA2 B hB
  have hut : occurrenceBefore (tau u)
      (Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (r + 1)) = true :=
    hresolved.1
  have huResolved : Protocol.sg_resolved gv.T u = true := by
    cases hfind : Block.find? gv.T B.root with
    | none =>
        simp only [tau, u, Protocol.sg_resolution_time, hfind] at hut
        rw [occurrenceBefore_none] at hut
        exact absurd hut Bool.false_ne_true
    | some H =>
        simp [u, Protocol.sg_resolved, hfind]
  have huHeaded : u ∈ headed := by
    apply Finset.mem_filter.mpr
    refine ⟨huBatch, ?_⟩
    exact ⟨by simp [u], huResolved⟩
  have hcard0 := Restated.roundBatch_card_le_one_stateBeforeTimeOn facts
    S Hs Xb hf hHs (t := (Restated.Vocabulary.Execution.Setup.a M S (r + 1))) (w := w) (r := r + 1) (v := v) hv
  have hcard : batch.card ≤ 1 := hcard0
  have hheadedCard : headed.card ≤ 1 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans hcard
  have hfirst : Protocol.batch_first? tau headed = some u :=
    Proofs.Optimistic.batch_first?_of_card_le_one huHeaded hheadedCard
  have hsummaryC : (Restated.Vocabulary.Protocol.summary M gv (r + 1) v).C_v = u.confirmed := by
    change (Protocol.batch_first? tau headed).bind
      Protocol.SGVote.confirmed = u.confirmed
    rw [hfirst]
    rfl
  have hsummaryT : (Restated.Vocabulary.Protocol.summary M gv (r + 1) v).t_v = tau u := by
    change (Protocol.batch_first? tau headed).elim none tau = tau u
    rw [hfirst]
    simp
  have heNone : (Restated.Vocabulary.Protocol.summary M gv (r + 1) v).e_v = none := by
    rw [Restated.Vocabulary.Proofs.Optimistic.summary_e_v_eq facts]
    exact Proofs.Optimistic.equivocation_instant_eq_none hcard
  refine ⟨?_, ?_, ?_⟩
  · rw [hsummaryT]
    exact hut
  · rw [hsummaryC]
    exact hresolved.2
  · rw [heNone, occurrenceAtLeast, occurrenceBefore_none]
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

/-- If `w` is in the set for `S.a (r + 1)`, `H` is a subset of that set of weight at least `m` whose
    members are awake at `r` and have round-`r` action blocks that are descendants of `P`,
    `lo ≤ S.a r`, and `P` is in the filtered tree of `w`'s core store in
    `W (strictEventIndex rho (S.a (r + 1)))`, then every outcome of `G2` for `P` at round `r + 1` on
    that store's grade view is `true`. -/
theorem seedG2_of_carrierQuorum_at_storeOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {r : Round} {P : Block V} {w : V} (hw : w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    {H : Finset V} (hsub : H ⊆ Hs ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (hweight : S.E.m ≤ S.E.electorate.weightOf H)
    (nf : V → M.N)
    (hn : ∀ v ∈ H, nf v ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r)
    (A2f : V → Option (Block V))
    (hA2 : ∀ v ∈ H, M.grade2_block_with (M.gradeContract (nf v).cache) S.E S.hc
      (M.toHealing (nf v).st.core) (M.round_of S.hc (M.toHealing (nf v).st.core).s) ⇢ A2f v)
    (Bf : V → Block V)
    (hB : ∀ v ∈ H, M.get_sg_vote_with (M.gradeContract (nf v).cache) S.E S.hc
      (M.toHealing (nf v).st.core) (M.round_of S.hc (M.toHealing (nf v).st.core).s) (A2f v) ⇢ Bf v)
    (hcover : ∀ v ∈ H, Block.Preceq P (Bf v))
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S r))
    (hcut : Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (r + 1) ≤ rho.horizon)
    (hactiveW : P ∈ M.get_filtered_block_tree
      (M.toHealing (W (strictEventIndex rho
        (Restated.Vocabulary.Execution.Setup.a M S (r + 1))) w).st.core).toFG)
    (hA : ∀ v ∈ H, ∀ j : Nat, rho.events[j]? = some (Record.Event.tick v (Restated.Vocabulary.Execution.Setup.a M S r)) → M.awake_for_grade2 S v (W j v) r) :
    let gv := M.gradeView (M.toHealing (W (strictEventIndex rho
      (Restated.Vocabulary.Execution.Setup.a M S (r + 1))) w).st.core)
    ∀ g ∈ Restated.Vocabulary.Protocol.G2 M S.E gv S.hc (r + 1) P, g = true := by
  intro gv g hg
  obtain ⟨cov, hcov, rfl⟩ := hg
  have hrelayRead : (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ ≤
      (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) :=
    le_trans (facts.gr.action_add_delta_le_next_Γ_neg1 S r)
      (le_of_lt (Restated.Vocabulary.Proofs.HealingSurface.next_Γ_neg1_lt_action facts S r))
  simp only [Restated.Vocabulary.Protocol.G2_withCovers, decide_eq_true_eq]
  unfold Restated.Vocabulary.Protocol.direct_support_withCovers
  refine le_trans hweight (S.E.electorate.weightOf_mono ?_)
  intro v hv
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ v, ?_⟩
  have hres := Restated.seedActionRead_resolvedSupport_at_storeOn facts S Hs Xb hf hHs hHsXb
    hw (hHs _ _ hrelayRead (hsub hv)) (nf v) (hn v hv) (A2f v) (hA2 v hv) (Bf v) (hB v hv)
    (hcover v hv) hpost hcut hactiveW (hA v hv)
  exact Restated.seedGradeRead_honestSupport_at_storeOn facts S Hs Xb hf hHs hw (hsub hv)
    hpost hcut (nf v) (hn v hv) (A2f v) (hA2 v hv) (Bf v) (hB v hv) cov hcov
    ⟨hres.1, hres.2 _ (hcov P _)⟩ (hA v hv)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- If the set for `S.a (r + 1)` has an honest weight majority, `w` is in it, `P` is an ancestor of
    every round-`r` action carrier of the set for `S.a r`, `lo ≤ S.a r`, `P` is in the filtered tree
    of `w`'s core store in `W (strictEventIndex rho (S.a (r + 1)))`, and every member of the set for
    `S.a (r + 1)` is awake at `r`, then every outcome of `G2` for `P` at round `r + 1` on that
    store's grade view is `true`. -/
theorem seedG2_of_actionCarriersCover_at_storeOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {r : Round}
    (hmajority : Execution.HonestWeightMajority S (Hs ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)))))
    {P : Block V} {w : V} (hw : w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (hcover : Restated.ActionCarriersCoverOn M S rho Hs r P
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r))))
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S r))
    (hcut : Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (r + 1) ≤ rho.horizon)
    (hactiveW : P ∈ M.get_filtered_block_tree
      (M.toHealing (W (strictEventIndex rho
        (Restated.Vocabulary.Execution.Setup.a M S (r + 1))) w).st.core).toFG)
    (hA : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick v (Restated.Vocabulary.Execution.Setup.a M S r)) → M.awake_for_grade2 S v (W j v) r) :
    let gv := M.gradeView (M.toHealing (W (strictEventIndex rho
      (Restated.Vocabulary.Execution.Setup.a M S (r + 1))) w).st.core)
    ∀ g ∈ Restated.Vocabulary.Protocol.G2 M S.E gv S.hc (r + 1) P, g = true := by
  have hle : (Restated.Vocabulary.Execution.Setup.a M S r) ≤
      (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) := le_trans
    (le_of_lt (lt_add_of_pos_right _ S.E.Δ_pos))
    (le_trans (facts.gr.action_add_delta_le_next_Γ_neg1 S r)
      (le_of_lt (Restated.Vocabulary.Proofs.HealingSurface.next_Γ_neg1_lt_action facts S r)))
  choose nf hn using fun v => actionReadFrom_nonempty₅₃ facts S
    (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r
  choose A2f hA2 using fun v => facts.dt.grade2_block_with_nonempty
    (M.gradeContract (nf v).cache) S.E S.hc (M.toHealing (nf v).st.core)
    (M.round_of S.hc (M.toHealing (nf v).st.core).s)
  choose Bf hB using fun v => facts.dt.get_sg_vote_with_nonempty
    (M.gradeContract (nf v).cache) S.E S.hc (M.toHealing (nf v).st.core)
    (M.round_of S.hc (M.toHealing (nf v).st.core).s) (A2f v)
  exact Restated.seedG2_of_carrierQuorum_at_storeOn facts S Hs Xb hf hHs hHsXb hw
    (Finset.Subset.refl _) (honestWeight_ge_m hmajority) nf (fun v _ => hn v) A2f
    (fun v _ => hA2 v) Bf (fun v _ => hB v)
    (fun v hv => hcover v (hHs _ _ hle hv) (nf v) (hn v) (A2f v) (hA2 v) (Bf v) (hB v))
    hpost hcut hactiveW hA

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation

/-- If `p` is in the set for `t`, `lo ≤ t`, `t + Δ < u`, `u` is inside the horizon and `w` is in the
    set for `u`, then the `h_max` of `p`'s core store in `W (inclusiveEventIndex rho t)` is at most
    the `h_max` of `w`'s core store in `W (inclusiveEventIndex rho u)`. -/
theorem storeAt_hMax_le_of_relay_l56 (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {p w : V} {t u : Time} (hp : p ∈ Hs t) (hlo : lo ≤ t)
    (htu : t + S.E.Δ < u) (huHor : u ≤ rho.horizon) (hw : w ∈ Hs u) :
    (W (inclusiveEventIndex rho t) p).st.core.h_max ≤
      (W (inclusiveEventIndex rho u) w).st.core.h_max := by
  have hwXb : w ∈ Xb := hHsXb _ hw
  have hpXb : p ∈ Xb := hHsXb _ hp
  set n := inclusiveEventIndex rho t with hn
  obtain ⟨D, hDmem, hDh⟩ :=
    Restated.Vocabulary.Proofs.NamedMaximumCarrier.maximum_carrier_stateBefore facts S rho n p
      (W n) (hf.onePath n).1
  rw [← hDh]
  have hprocessed : Restated.Vocabulary.Execution.Object.processed M (W n p).st (Object.block D) = true :=
    decide_eq_true hDmem
  rcases Restated.Vocabulary.Protocol.acceptsAt_block_of_processed facts S rho p W hf.onePath n D
      hprocessed with hgen | ⟨i, hin, t', hacc⟩
  · set N := strictEventIndex rho u with hN
    have hgenesis : (Block.genesis : Block V) ∈ (W N w).st.core.T :=
      (Restated.genesis_mem_and_stamp_storeBeforeTimeOn facts S Hs Xb hf w u u).1
    obtain ⟨G, hG, hGerase⟩ :=
      Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore facts S rho N w
        (W N) (hf.onePath N).1 hgenesis
    have hbound := Restated.Vocabulary.Proofs.NamedStoreBridge.heights_le_hMax_stateBefore facts S rho
      N w (W N) (hf.onePath N).1 G hG
    have hGgen : G = NamedBlock.genesis := eq_named_genesis_of_erase_eq_genesis hGerase
    rw [hgen]
    rw [hGgen] at hbound
    exact hbound.trans (Restated.storeBeforeTime_hMax_le_storeAtOn facts S Hs Xb hf w u)
  · obtain ⟨-, e, he, -, het⟩ := hacc.1
    have hetime : e.time ≤ t := by
      have htrue := Restated.filter_true_of_index_ltOn facts S Hs Xb hf
        (fun f : Record.Event V => decide (f.time ≤ t))
        (fun e₁ f₁ hkey hf₁ => by
          simp only [decide_eq_true_eq] at hf₁ ⊢
          exact le_trans (Restated.time_le_of_key_le hkey) hf₁) hin he
      simpa only [decide_eq_true_eq] using htrue
    have htRead : t' ≤ t := by rw [← het]; exact hetime
    have hDrun : Restated.RunBlockOn M S rho W Xb D :=
      Restated.runBlock_of_stateBefore_memOn facts S W Xb hpXb hDmem
    have hDpos : 0 < D.slot := by
      have h' := Restated.Vocabulary.Protocol.parent_slot_lt_of_acceptsAt_block facts S W hf.onePath hacc
      rw [Proofs.NamedWire.erase_slot] at h'
      exact Nat.zero_lt_of_lt h'
    have hpMax : p ∈ Hs (max t' lo) := hHs _ _ (max_le htRead hlo) hp
    by_cases hcase : (M.derive_named S.E S.cfg D).h ≤
        (W (strictEventIndex rho u) w).st.core.h_max
    · exact hcase.trans (Restated.storeBeforeTime_hMax_le_storeAtOn facts S Hs Xb hf w u)
    · exfalso
      have hlt : (W (strictEventIndex rho u) w).st.core.h_max <
          (M.derive_named S.E S.cfg D).h := Nat.lt_of_not_ge hcase
      have hFhist : ∀ j : Nat,
          j ≤ (rho.events.filter (fun e => decide (e.time < u))).length →
            Block.Preceq (W j w).st.core.F D.erase := by
        intro j hj
        have hpreCap : (W j w).st.core.h_max ≤ (W (strictEventIndex rho u) w).st.core.h_max :=
          hMax_mono_along₅₃ facts S hf.onePath w hj
        obtain ⟨Dst, hDstMem, hDstF, hDstBound⟩ :=
          Restated.Vocabulary.Proofs.Bridges.storeFinalizationOnChain_stateBefore facts S rho j w
            (W j) (hf.onePath j).1
        have hDstRun : Restated.RunBlockOn M S rho W Xb Dst :=
          Restated.runBlock_of_stateBefore_memOn facts S W Xb hwXb hDstMem
        have hcrossed : (M.derive_named S.E S.cfg Dst).h_F <
            (M.derive_named S.E S.cfg D).h :=
          lt_of_lt_of_le (hDstBound.trans_le hpreCap) (le_of_lt hlt)
        have hpreceq := Restated.finalized_preceq_of_height_ltOn facts S rho W Xb D Dst
          hf.slashableBound hf.rootCollisionFree hDrun hDstRun hcrossed
        rwa [hDstF] at hpreceq
      have htIn : t' < u - S.E.Δ := by
        apply (lt_sub_iff_add_lt).2
        linarith
      have hgst : lo ≤ u - S.E.Δ := by
        apply (le_sub_iff_add_le).2
        linarith [S.E.Δ_pos]
      have hadmit : Restated.Vocabulary.Protocol.AdmittedBefore M S rho W w D.erase u :=
        Restated.block_admittedBefore_of_accepted_after_cutoffOn facts S Hs Xb hf hHs hHsXb hpMax hw hDpos
          hacc htIn hgst (sub_add_cancel u S.E.Δ) huHor hFhist
      have hmemErased : D.erase ∈ (W (strictEventIndex rho u) w).st.core.T :=
        (Restated.admittedBefore_mem_and_stampOn facts S Hs Xb hf hadmit).1
      have hbody : D ∈ (W (strictEventIndex rho u) w).st.bodies :=
        Restated.namedMem_of_erasedMem_stateBeforeTimeOn facts S Hs Xb hf hwXb hDrun hmemErased
      have hle := Restated.Vocabulary.Proofs.NamedStoreBridge.heights_le_hMax_stateBefore facts S rho
        _ w _ (hf.onePath _).1 D hbody
      exact absurd hle (not_le.mpr hlt)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation

/-- If `lo ≤ t`, `t + Δ < u`, `u` is inside the horizon and the set for `u` has a member, then the
    largest `h_max` of the members of the set for `t` in `W (inclusiveEventIndex rho t)` is at most
    the largest of the members of the set for `u` in `W (inclusiveEventIndex rho u)`. -/
theorem honestHMaxAtOn_le_of_relay_l56 (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {t u : Time} (hlo : lo ≤ t) (htu : t + S.E.Δ < u) (huHor : u ≤ rho.horizon)
    (hne : (Hs u).Nonempty) :
    ((Hs t).sup fun v => (W (inclusiveEventIndex rho t) v).st.core.h_max) ≤
      (Hs u).sup fun v => (W (inclusiveEventIndex rho u) v).st.core.h_max := by
  obtain ⟨w, hw⟩ := hne
  refine Finset.sup_le fun p hp => ?_
  exact (Restated.storeAt_hMax_le_of_relay_l56 facts S Hs Xb hf hHs hHsXb hp hlo htu huHor hw).trans
    (Finset.le_sup (f := fun v => (W (inclusiveEventIndex rho u) v).st.core.h_max) hw)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation

/-- Under `HonestCommitteesOn`, the set for any time `t` is not empty. -/
theorem nonempty_of_honestCommitteesOn_l56 (facts : Record.Facts M)
    (S : Setup V) (Hs : Int → Finset V)
    (hcom : Restated.HonestCommitteesOn M S Hs) (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (t : Time) :
    (Hs t).Nonempty := by
  obtain ⟨s, hs⟩ := facts.sch.exists_confirmation_time_ge S t
  have hmajority := hcom s
  have hpos : 0 < ((S.E.committee s) ∩ Hs (M.confirmation_time S.E s)).card := by
    omega
  obtain ⟨v, hvmem⟩ := Finset.card_pos.mp hpos
  exact ⟨v, hHs _ _ hs (Finset.mem_inter.mp hvmem).2⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation

/-- If `k ≤ k'`, `lo ≤ S.a k` and `S.a k'` is inside the horizon, the largest `h_max` over the set
    for `S.a k` at that time is at most the largest over the set for `S.a k'` at that time. -/
theorem honestHMaxAtOn_action_mono_l56 (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {k k' : Round} (hkk : k ≤ k') (hlo : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S k)) (hhor : (Restated.Vocabulary.Execution.Setup.a M S k') ≤ rho.horizon) :
    ((Hs (Restated.Vocabulary.Execution.Setup.a M S k)).sup fun v =>
        (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S k)) v).st.core.h_max) ≤
      (Hs (Restated.Vocabulary.Execution.Setup.a M S k')).sup fun v =>
        (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S k')) v).st.core.h_max := by
  rcases eq_or_lt_of_le hkk with heq | hlt
  · rw [heq]
  · have hstep := Restated.action_add_one_add_delta_le_next_action_l52 facts S k
    have hmono : (Restated.Vocabulary.Execution.Setup.a M S (k + 1)) ≤ (Restated.Vocabulary.Execution.Setup.a M S k') := Restated.Vocabulary.Proofs.Assembly.a_mono facts S hlt
    exact Restated.honestHMaxAtOn_le_of_relay_l56 facts S Hs Xb hf hHs hHsXb hlo
      (by linarith) hhor
      (Restated.nonempty_of_honestCommitteesOn_l56 facts S Hs hcom hHs _)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation

/-- One delay after any grade domain time of round `r` is strictly before round `r`'s action time. -/
theorem domain_add_delta_lt_action_l56 (facts : Record.Facts M) (S : Setup V) (r : Round)
    (p : Protocol.Phase) :
    M.domain S.E S.hc r p + S.E.Δ < (Restated.Vocabulary.Execution.Setup.a M S r) := by
  have h := facts.gr.domain_add_five_delta_le_action S r p
  have hΔ := S.E.Δ_pos
  show M.domain S.E S.hc r p + S.E.Δ < M.a S.hc S.E.Δ r
  linarith

/-- One delay after the proposal time of round `q`'s opening slot is strictly before round `q`'s
    action time. -/
theorem openingProposal_add_delta_lt_action_l56 (facts : Record.Facts M) (S : Setup V) (q : Round) :
    M.proposal_time S.E ((M.opening_slot S.hc q)) + S.E.Δ < (Restated.Vocabulary.Execution.Setup.a M S q) := by
  have hpv := facts.sch.proposal_time_lt_vote_time S.E (M.opening_slot S.hc q)
  have hv := facts.sch.slotStart_add_delta_eq_vote_time S.E (M.opening_slot S.hc q)
  have hc := facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E (M.opening_slot S.hc q)
  have ha := facts.sch.a_eq_confirmation_time S.hc S.E q
  have hΔ := S.E.Δ_pos
  show M.proposal_time S.E (M.opening_slot S.hc q) + S.E.Δ < M.a S.hc S.E.Δ q
  rw [ha]
  linarith

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation

/-- If `k < e`, then `S.a k + Δ < S.a e`. -/
theorem action_add_delta_lt_action_of_lt_l67 (facts : Record.Facts M) (S : Setup V) {k e : Round} (h : k < e) :
    (Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ < (Restated.Vocabulary.Execution.Setup.a M S e) :=
  lt_of_lt_of_le
    (lt_of_le_of_lt (facts.gr.action_add_delta_le_next_Γ_neg1 S k) (Restated.Vocabulary.Proofs.HealingSurface.next_Γ_neg1_lt_action facts S k))
    (Restated.Vocabulary.Proofs.Assembly.a_mono facts S h)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation

/-- If `d ≤ opening_slot q`, then `vote_time d + Δ < S.a q`. -/
theorem vote_add_delta_lt_action_l53 (facts : Record.Facts M) (S : Setup V) {d : Slot} {q : Round}
    (hd : d ≤ (M.opening_slot S.hc q)) :
    M.vote_time S.E d + S.E.Δ < (Restated.Vocabulary.Execution.Setup.a M S q) := by
  have hmono := facts.sch.vote_time_mono S.E hd
  have hv := facts.sch.slotStart_add_delta_eq_vote_time S.E (M.opening_slot S.hc q)
  have hc := facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E (M.opening_slot S.hc q)
  have ha := facts.sch.a_eq_confirmation_time S.hc S.E q
  have hΔ := S.E.Δ_pos
  show M.vote_time S.E d + S.E.Δ < M.a S.hc S.E.Δ q
  rw [ha]
  linarith

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation

/-- `proposal_time (opening_slot q + 2) + Δ < S.a (q + 1)`. -/
theorem plusTwoProposal_add_delta_lt_nextAction_l53 (facts : Record.Facts M) (S : Setup V) (q : Round) :
    M.proposal_time S.E ((M.opening_slot S.hc q) + 2) + S.E.Δ < (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) :=
  lt_of_le_of_lt
    (Int.add_le_add_right
      (facts.sch.proposal_time_mono S.E (facts.gr.plusTwo_slot_le_nextOpening_l53 S q)) S.E.Δ)
    (Restated.openingProposal_add_delta_lt_action_l56 facts S (q + 1))

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation

/-- If `u`'s store in `W (strictEventIndex rho read)` is a fixed-height justification root at `Mh`,
    `lo ≤ read`, `read + Δ` is at most the proposal time `P` of slot `opening_slot q + 2`, round `q`
    is a carrier round, `q + 1 ≤ endpoint`, and the members of the set for `S.a endpoint` have
    `h_max` at most `Mh` there, then every outcome of the proposal duty at `P` is a run block, its
    proposer is in the set for the slot's confirmation time, and the proposer's store before `P` has
    `u`'s justified block as FG root and `h_max` equal to `Mh`. -/
theorem fixedRoot_plusTwoProposal_factsOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {Mh : Height} {u : V} {read : Time}
    (hfix : Restated.FixedHeightJustificationRootAtReadOn M S rho W Hs Xb Mh u read
      (W (strictEventIndex rho read)))
    {q endpoint : Round}
    (hpost : lo ≤ read)
    (hdelay : read + S.E.Δ ≤
      M.proposal_time S.E ((M.opening_slot S.hc q) + 2))
    (hcarrier : Restated.ProposerCarrierAtOn M S Hs q)
    (hqEnd : q + 1 ≤ endpoint)
    (hendHor : (Restated.Vocabulary.Execution.Setup.a M S endpoint) ≤ rho.horizon)
    (hcapEnd : ((Hs (Restated.Vocabulary.Execution.Setup.a M S endpoint)).sup fun v =>
      (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S endpoint)) v).st.core.h_max) ≤ Mh)
    (hneTick : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick (S.E.proposer ((M.opening_slot S.hc q) + 2)) (M.proposal_time S.E ((M.opening_slot S.hc q) + 2))) →
      ∃ out : M.N × List (NamedObject V), M.tick S (S.E.proposer ((M.opening_slot S.hc q) + 2)) (W j (S.E.proposer ((M.opening_slot S.hc q) + 2))) (M.proposal_time S.E ((M.opening_slot S.hc q) + 2)) ⇢ out)
    (hrun : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick (S.E.proposer ((M.opening_slot S.hc q) + 2)) (M.proposal_time S.E ((M.opening_slot S.hc q) + 2))) →
      M.awake_for_grade1 S (S.E.proposer ((M.opening_slot S.hc q) + 2))
        (W j (S.E.proposer ((M.opening_slot S.hc q) + 2))) (M.round_of S.hc ((M.opening_slot S.hc q) + 2))) :
    ∀ c : M.Cache, M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q) + 2)))
        (S.E.proposer ((M.opening_slot S.hc q) + 2))).st.core.toHealing
      (M.proposal_time S.E ((M.opening_slot S.hc q) + 2))
      (W (strictEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q) + 2)))
        (S.E.proposer ((M.opening_slot S.hc q) + 2))).cache ⇢ c →
    ∀ o : Option (NamedBlock V), M.proposal_with (M.gradeContract c)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc
      (S.node (S.E.proposer ((M.opening_slot S.hc q) + 2)))
      (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q) + 2)))
          (S.E.proposer ((M.opening_slot S.hc q) + 2))).st
        (M.proposal_time S.E ((M.opening_slot S.hc q) + 2))) ⇢ o →
    ∃ Bplus : NamedBlock V,
      o = some Bplus ∧
      Restated.RunBlockOn M S rho W Xb Bplus ∧
      S.E.proposer ((M.opening_slot S.hc q) + 2) ∈
        Hs (M.confirmation_time S.E ((M.opening_slot S.hc q) + 2)) ∧
      M.proposal_time S.E ((M.opening_slot S.hc q) + 2) ≤ rho.horizon ∧
      M.get_fg_root
          (W (strictEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q) + 2)))
            (S.E.proposer ((M.opening_slot S.hc q) + 2))).st.toHealing.toFG =
        (W (strictEventIndex rho read) u).st.J ∧
      (W (strictEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q) + 2)))
        (S.E.proposer ((M.opening_slot S.hc q) + 2))).st.h_max = Mh := by
  intro c hc o ho
  have hprop : S.E.proposer ((M.opening_slot S.hc q) + 2) ∈
      Hs (M.confirmation_time S.E ((M.opening_slot S.hc q) + 2)) :=
    hcarrier 2 (by decide)
  have hpropP : S.E.proposer ((M.opening_slot S.hc q) + 2) ∈
      Hs (M.proposal_time S.E ((M.opening_slot S.hc q) + 2)) :=
    hHs _ _ (facts.sch.proposal_time_le_confirmation_time S.E _) hprop
  have hlt := Restated.plusTwoProposal_add_delta_lt_nextAction_l53 facts S q
  have hproposalAction : M.proposal_time S.E
      ((M.opening_slot S.hc q) + 2) ≤ (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) := by
    have := S.E.Δ_pos
    linarith
  have hproposalEnd : M.proposal_time S.E
      ((M.opening_slot S.hc q) + 2) ≤ (Restated.Vocabulary.Execution.Setup.a M S endpoint) :=
    hproposalAction.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hqEnd)
  have hproposalHor : M.proposal_time S.E
      ((M.opening_slot S.hc q) + 2) ≤ rho.horizon :=
    hproposalEnd.trans hendHor
  have hgat : lo ≤ M.proposal_time S.E ((M.opening_slot S.hc q) + 2) := by
    have := S.E.Δ_pos
    linarith
  have hproposalCap : ((Hs (M.proposal_time S.E ((M.opening_slot S.hc q) + 2))).sup fun v =>
      (W (inclusiveEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q) + 2))) v).st.core.h_max)
        ≤ Mh :=
    (Restated.honestHMaxAtOn_le_of_relay_l56 facts S Hs Xb hf hHs hHsXb hgat
      (lt_of_lt_of_le hlt (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hqEnd)) hendHor
      (Restated.nonempty_of_honestCommitteesOn_l56 facts S Hs hcom hHs _)).trans hcapEnd
  have hrootMax :=
    Restated.fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRiseOn facts
      S Hs Xb hf hHs hHsXb hf.slashableBound hfix hpropP hpost hdelay hproposalHor hproposalCap
  have hmem : o ∈ Restated.Vocabulary.Statements.Instantiation.proposedBlockAt M S rho
      ((M.opening_slot S.hc q) + 2) :=
    ⟨_, ⟨W (strictEventIndex rho (M.proposal_time S.E ((M.opening_slot S.hc q) + 2))),
      mem_stateBeforeTime_along₅₃ facts hf _, c, hc, rfl⟩,
      by rw [facts.nd.mkNode_cache, facts.nd.mkNode_st, facts.dt.proposal_with_store_with_cache]
         exact ho⟩
  obtain ⟨Bplus, rfl⟩ :=
    Restated.Vocabulary.Proofs.HealingSurface.proposedBlockAt_isSome facts S rho
      ((M.opening_slot S.hc q) + 2) o hmem
  have hblock : Restated.RunBlockOn M S rho W Xb Bplus :=
    Restated.proposedBlockAt_blockInRun_of_admissibleOn facts S Hs Xb hf hHs hHsXb
      ((M.opening_slot S.hc q) + 2)
      ((by decide : (0 : Nat) < 2).trans_le (Nat.le_add_left _ _))
      hprop hproposalHor hgat hneTick hrun c hc ho
  exact ⟨Bplus, rfl, hblock, hprop, hproposalHor, hrootMax.1, hrootMax.2⟩

end

end DecoupledConsensusModel.Sts.Restated
