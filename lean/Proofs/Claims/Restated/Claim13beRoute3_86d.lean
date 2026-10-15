import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13beRoute3_45
import Proofs.Claims.Restated.Claim13beRoute3_46
import Proofs.Claims.Restated.Claim13beRoute3_47
import Proofs.Claims.Restated.Claim13beRoute3_48b
import Proofs.Claims.Restated.Claim13beRoute3_49
import Proofs.Claims.Restated.Claim13beRoute3_53b
import Proofs.Claims.Restated.Claim13beRoute3_54
import Proofs.Claims.Restated.Claim13beRoute3_54b
import Proofs.Claims.Restated.Claim13beRoute3_60
import Proofs.Claims.Restated.Claim13beRoute3_61
import Proofs.Claims.Restated.Claim13beRoute3_62
import Proofs.Claims.Restated.Claim13beRoute3_63
import Proofs.Claims.Restated.Claim13beRoute3_64b
import Proofs.Claims.Restated.Claim13beRoute3_70
import Proofs.Claims.Restated.Claim13beRoute3_86c
import Proofs.Claims.Restated.Claim13beRoute3_87
import Proofs.Claims.Restated.Vocabulary_Execution_PreparedReadBridge
import Proofs.Claims.Restated.Vocabulary_ModelVocabulary_Healing_Schedule
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_ActionSourceCore
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_SeedEntryCanonical
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Views_RecoveryVoteCone
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_Grades
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_Ladder
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_RelativeSeedK3
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_TickBridges
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_PostHealingReuse
import Proofs.Claims.Restated.Vocabulary_Protocol_Store_BoundaryRows
import Proofs.Claims.Restated.Vocabulary_Protocol_ValidatorClient_RecordClean
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.RunVocabulary
import Model.Conditions.Vocabulary_Internal_Definitions_NamedLifecycle
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGradeQueries
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
import Model.Conditions.Vocabulary_Internal_HealingSurface
import Model.Conditions.Vocabulary_Internal_Invariants
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedHeadReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_ModelVocabulary_Healing_Schedule
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_Grades_RelativeCrossReader
import Proofs.Vocabulary.Protocol.Grades.RelativeOneChain
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_86d

/-!
# Prepared anchors and SG blocks after the progress deadline

Theorems over a model `M : Record.Model V`, read along one path `W` of the run: genesis graded given
the relative carrier window, raw grade-2 frames at actions after the progress deadline, the bound on
a selected Q2, and the compatibility of a voter's prepared anchor with the SG blocks of round
`c + 1`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

local macro "p64b% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_64b)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p62% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_62)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p60% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_60)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

section
set_option autoImplicit false
open scoped DC
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs

/-- Along a path `W`, the tree of `v`'s store in `W i` is contained in the tree of its store in
    `W j` for `i ≤ j`. -/
private theorem T_mono_along₈₆d (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (v : V)
    {i j : Nat} (hij : i ≤ j) : (W i v).st.core.T ⊆ (W j v).st.core.T := by
  have hslice : W j ∈ ((rho.events.drop i).take (j - i)).foldlM (Record.worldStepOf M S) (W i) := by
    have h := (p62% onePath_reach₆₂s) W hW i (j - i)
    rwa [Nat.add_sub_of_le hij] at h
  exact Restated.Vocabulary.Proofs.stateBefore_T_subset facts S rho v (W i) (hW i).1 j hij (W j) hslice

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
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- Given the relative carrier window of round `c − 1` and phase `p` along the path `W`, genesis is
    graded at phase `p` of round `c` by every member of the set for that phase's domain instant:
    every outcome of its store grade on the member's store in `W` before the domain instant is
    `true`. -/
theorem relativeGrade_genesis_of_windowOn_l86d (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    (hfb : BelowOneThirdOn S rho Hs)
    {c : Round} (hc : 0 < c) (p : Phase)
    (hdomHorP : M.domain S.E S.hc c p ≤ rho.horizon)
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (c - 1)))
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (c - 1)) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S (c - 1))) → M.awake_for_grade2 S u (W j u) (c - 1))
    (hwindow : Restated.RelativeCarrierWindowAtOn M S rho W
      (fun t => W (strictEventIndex rho t)) Hs (c - 1) p) :
    ∀ v ∈ Hs (M.domain S.E S.hc c p),
      ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
        (W (strictEventIndex rho (M.domain S.E S.hc c p)) v).st c p
        Block.genesis ⇢ b → b = true := by
  have hΔ := S.E.Δ_pos
  have hqr : c - 1 < c := Nat.sub_lt hc Nat.one_pos
  have hprevt : (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) + S.E.Δ ≤ M.domain S.E S.hc c p :=
    (facts.gr.action_delta_le_early S S.hc.R_ge_three hqr).trans (facts.gr.early_g2_lt_domain S c p).le
  have hmaj : Restated.GradeFormingMajorityOn M S rho W Hs (Hs (M.domain S.E S.hc c p)) c :=
    Restated.gradeFormingMajority_of_admissible_belowOneThirdOn facts S Hs Xb hf hHs hfb hc
      hprevt hdomHorP hpost hA
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
    obtain ⟨na, hna, g, hg, A, hAsel⟩ := (p64b% exists_actionSG₆₄b) facts S
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
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- For a round `c` at or after the progress deadline, every member of the set for round `(c + 1)`'s
    grade-2 domain instant has a raw grade-2 root at its round-`(c + 1)` action read along `W`:
    every grade read its contract can return there passes the raw grade-2 test. -/
theorem nodeRawG2_at_action_after_recovery_deadlineOn (facts : Record.Facts M)
    {delayExtra : Nat}
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hbelow : BelowOneThirdOn S rho Hs)
    {rGST gap : Round} {t₀ : Int} (hrec : Restated.MultiProposerRecurrenceOn M S Hs gap t₀ rho.horizon)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    {c : Round} (hc : fgSafetyProgressDeadline S rho rGST gap delayExtra ≤ c)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) ≤ rho.horizon)
    (hloPost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    (hloOpen : lo ≤ M.opening S.E S.hc (rGST + 2 - S.hc.η_SG))
    (ht₀ : t₀ ≤ (Restated.Vocabulary.Execution.Setup.a M S (rGST + 2)))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    ∀ v ∈ Hs (M.domain S.E S.hc (c + 1) .g2),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (c + 1))) v) (c + 1),
      Restated.Vocabulary.Internal.PhaseGrades.nodeRawG2 M S n (c + 1) := by
  have hdomainHor : M.domain S.E S.hc (c + 1) .g2 ≤ rho.horizon :=
    (facts.gr.domain_le_a S (c + 1) .g2).trans hhor
  have hwindow : Restated.RelativeCarrierWindowAtOn M S rho W
      (fun t => W (strictEventIndex rho t)) Hs c .g2 :=
    Restated.relativeCarrierWindowAt_after_recovery_deadlineOn facts S Hs Xb hf hHs hHsXb hcom
      hbelow hrec hdelay hpost hc hdomainHor hloPost hloOpen ht₀ hA
  have hloc : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S c) :=
    hloPost.trans ((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone
      (le_trans (by
        unfold fgSafetyProgressDeadline
        exact (Nat.le_add_right rGST 1).trans (Nat.le_add_right (rGST + 1) _)) hc))
  have hrc : rGST < c := lt_of_lt_of_le (by
    unfold fgSafetyProgressDeadline
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self rGST) (Nat.le_add_right (rGST + 1) _)) hc
  have hkc : lo ≤ M.early S.E S.hc c .g2 - S.E.Δ :=
    Restated.lo_le_early_g2_sub_delta_of_action_lt facts S hloPost hrc
  have hgrades := Restated.relativeGrade_genesis_of_windowOn_l86d facts S Hs Xb hf hHs hbelow
    (c := c + 1) (Nat.succ_pos c) .g2 hdomainHor (by simpa only [Nat.add_sub_cancel] using hloc)
    (by simpa only [Nat.add_sub_cancel] using hA c hkc)
    (by simpa only [Nat.add_sub_cancel] using hwindow)
  have hgat : lo ≤ M.domain S.E S.hc (c + 1) .g2 :=
    hloc.trans (Restated.Vocabulary.Proofs.NamedOutageClosure.action_le_domain facts S S.hc.R_ge_three (Nat.lt_succ_self c))
  intro v hv n hn g hg
  obtain ⟨b, hb⟩ := facts.gr.gradeBool_nonempty S.E
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc (c + 1) .g2)) v).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc (c + 1) .g2)) v).st.core.F
    S.hc.η_SG (c + 1) (M.early S.E S.hc (c + 1) .g2) (M.late S.E S.hc (c + 1) .g2) Block.genesis
  have hbt : b = true := hgrades v hv b hb
  have hmem : Block.genesis ∈ (M.gradeView (M.toHealing
      (W (strictEventIndex rho (M.domain S.E S.hc (c + 1) .g2)) v).st.core)).T := by
    rw [facts.gr.Sts_gradeView_T]
    exact (Restated.genesis_mem_and_stamp_storeBeforeTimeOn facts S Hs Xb hf v
      (M.domain S.E S.hc (c + 1) .g2) (M.domain S.E S.hc (c + 1) .g2)).1
  obtain ⟨fr, hfr⟩ := facts.gr.freezeRoot_nonempty S.E
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc (c + 1) .g2)) v).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc (c + 1) .g2)) v).st.core.F
    S.hc.η_SG (c + 1) (M.early S.E S.hc (c + 1) .g2) (M.late S.E S.hc (c + 1) .g2)
  obtain ⟨raw, hraw, -⟩ := facts.gr.q10_freeze_of_graded S.E _ _ S.hc.η_SG (c + 1)
    (facts.gr.q10_early_le_late S (c + 1) .g2) hmem b hb hbt fr hfr
  subst hraw
  have hframe := Restated.actionFrame_g2On facts S Hs Xb hf (Nat.succ_pos c) hhor hv hgat n hn
    (some raw) hfr
  rw [facts.nd.gradeContract_read_rawG2 n.cache S.E S.hc (M.toHealing n.st.core) (c + 1) g hg, hframe]
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
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- For every node state `n` that `w` can hold before round `r`'s phase-`p` domain instant, if the
    store grade of `n`'s store can grade `Q` at phase `p` of round `r`, then `Q` is in the tree of
    `n`'s store. -/
theorem storeGrade_mem_domainTree_source_l86d (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) {r : Round} {w : V}
    {p : DecoupledConsensusModel.Protocol.Phase} {Q : Block V} :
    ∀ n ∈ Restated.Vocabulary.Internal.PhaseGrades.readAt M S rho (M.domain S.E S.hc r p) w,
    Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc n.st r p Q ⇢ true →
    Q ∈ n.st.core.T := by
  intro n hn hgrade
  obtain ⟨W, hW, rfl⟩ := hn
  have hg : M.gradeBool S.E
      (M.gradeView (M.toHealing (W w).st.core)) (W w).st.core.F S.hc.η_SG r
      (M.early S.E S.hc r p) (M.late S.E S.hc r p) Q ⇢ true := hgrade
  obtain ⟨H, hHT, hQH⟩ :=
    facts.gr.ModelProperties_exists_mem_T_preceq_of_gradeBool _ _ _ _ _ _ _ true hg rfl
  have hpc := Restated.Vocabulary.Proofs.NamedStoreBridge.parentClosed_stateBeforeTime facts S rho
    (M.domain S.E S.hc r p) w W hW
  unfold Restated.Vocabulary.Internal.ParentClosed Record.Model.GS.parent_closed at hpc
  have hQ := Proofs.Records.mem_of_preceq hpc.2 Q H hHT
    (Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mpr hQH)
  rw [facts.sto.toHealing_T] at hQ
  exact hQ

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
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- After the progress deadline, if the Q2 read at a node state of `v`'s round-`c` action read along
    `W` can return `Q`'s erasure, then that erasure is in the filtered tree of `u`'s store in `W`
    before a later `read`, or an ancestor of that store's FG root. -/
theorem selectedG2_filteredMem_or_preceq_root_after_GST_ancestorOn (facts : Record.Facts M)
    {delayExtra : Nat}
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hbelow : BelowOneThirdOn S rho Hs)
    {rGST gap : Round} {t₀ : Int} (hrec : Restated.MultiProposerRecurrenceOn M S Hs gap t₀ rho.horizon)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    {c : Round} (hc : fgSafetyProgressDeadline S rho rGST gap delayExtra ≤ c)
    (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho c) (hchor : (Restated.Vocabulary.Execution.Setup.a M S c) ≤ rho.horizon)
    {read : Time}
    (hread : (Restated.Vocabulary.Execution.Setup.a M S (fgSafetyProgressDeadline S rho rGST gap delayExtra)) ≤ read)
    (hcut : Restated.Vocabulary.Protocol.HealConfig.Γ_0 M S.hc S.E.Δ c ≤ read)
    (hhor : read ≤ rho.horizon) (hnext : read ≤ (Restated.Vocabulary.Execution.Setup.a M S (c + 1)))
    {u v : V} (hu : u ∈ Hs read) (hv : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S c))) (hAv : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick v (Restated.Vocabulary.Execution.Setup.a M S c)) → M.awake_for_grade2 S v (W j v) c)
    {Q : NamedBlock V}
    {nv : M.N}
    (hnv : nv ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v) c)
    (hQ : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S nv c ⇢ some Q.erase)
    (hloc : lo ≤ M.opening S.E S.hc (c - S.hc.η_SG))
    (hloPost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    (hloOpen : lo ≤ M.opening S.E S.hc (rGST + 2 - S.hc.η_SG))
    (ht₀ : t₀ ≤ (Restated.Vocabulary.Execution.Setup.a M S (rGST + 2)))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    Q.erase ∈ M.get_filtered_block_tree
        (M.toHealing (W (strictEventIndex rho read) u).st.core).toFG ∨
      Block.Preceq Q.erase
        (M.get_fg_root (M.toHealing (W (strictEventIndex rho read) u).st.core).toFG) := by
  have hdeadlinePos : 0 < fgSafetyProgressDeadline S rho rGST gap delayExtra := by
    unfold fgSafetyProgressDeadline
    exact (Nat.zero_lt_succ rGST).trans_le (Nat.le_add_right (rGST + 1) _)
  have hcpos : 0 < c := hdeadlinePos.trans_le hc
  have hdomain : M.domain S.E S.hc c .g1 = Restated.Vocabulary.Protocol.HealConfig.Γ_0 M S.hc S.E.Δ c := by
    rw [facts.gr.Sts_domain_g1_eq_opening, facts.gr.opening_eq_proposal_time]
    exact (facts.sch.Γ_0_eq_proposal_time S.hc S.E c).symm
  have hvDom : ∀ p : Phase, v ∈ Hs (M.domain S.E S.hc c p) :=
    fun p => hHs _ _ (facts.gr.domain_le_a S c p) hv
  have huG1 : u ∈ Hs (M.domain S.E S.hc c .g1) := hHs _ _ (hdomain.trans_le hcut) hu
  obtain ⟨hloEarly, -, -, -⟩ := Restated.loBounds_l70 facts S hcpos hloc
  have hguard := Restated.actionQ2_crossReaderBodyReadyGuard_historyOn facts S Hs Xb hf hHs hHsXb
    hcpos ready (hvDom .g0) hloEarly nv hnv u huG1 Q.erase hQ
  have hG1 := Restated.selectedG2_G1_at_read_after_cutoffOn facts S Hs Xb hf hHs hHsXb ready hchor
    (hvDom .g2) huG1 nv hnv hQ hguard hloc
  obtain ⟨b, hb⟩ := facts.gr.gradeBool_nonempty S.E
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc c .g1)) u).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc c .g1)) u).st.core.F
    S.hc.η_SG c (M.early S.E S.hc c .g1) (M.late S.E S.hc c .g1) Q.erase
  have hbt : b = true := hG1 b hb
  subst hbt
  have hW := hf.onePath
  have hmemG1 := (p64b% mem_stateBeforeTime_along₆₄b) hf.sorted hW (M.domain S.E S.hc c .g1)
  have hQdomain : Q.erase ∈ (W (strictEventIndex rho (M.domain S.E S.hc c .g1)) u).st.core.T :=
    Restated.storeGrade_mem_domainTree_source_l86d facts S rho _ ⟨_, hmemG1, rfl⟩ hb
  have hQread : Q.erase ∈ (W (strictEventIndex rho read) u).st.core.T :=
    T_mono_along₈₆d facts S hW u (strictEventIndex_mono rho (hdomain.trans_le hcut)) hQdomain
  have hmemRead := (p64b% mem_stateBeforeTime_along₆₄b) hf.sorted hW read
  obtain ⟨Qn, hQnbody, hQnerase⟩ :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime facts S rho read u _
      hmemRead hQread
  have hQnrun : Restated.RunBlockOn M S rho W Xb Qn :=
    Restated.lifecycle_runBlock_of_mem_storeBeforeTimeOn facts S Hs Xb hf (hHsXb _ hu) hQnbody
  obtain ⟨A2, hA2⟩ := facts.dt.grade2_block_with_nonempty (M.gradeContract nv.cache) S.E S.hc
    (M.toHealing nv.st.core) (M.round_of S.hc (M.toHealing nv.st.core).s)
  obtain ⟨G, hG⟩ := facts.dt.get_sg_vote_with_nonempty (M.gradeContract nv.cache) S.E S.hc
    (M.toHealing nv.st.core) (M.round_of S.hc (M.toHealing nv.st.core).s) A2
  have hQsg : Block.Preceq Q.erase G :=
    Restated.preceq_actionSGBlockAt_of_actionQ2On facts S Hs Xb hf hHs hHsXb hcpos hchor
      (hvDom .g1) hloc nv hnv hQ (preceq_eq_true_iff_Preceq.mp (Block.preceq_self Q.erase)) A2 hA2 G hG
  have hQnsg : Block.Preceq Qn.erase G := by
    rw [hQnerase]
    exact hQsg
  have hsplit := Restated.actionSGBlock_filteredMem_or_preceq_root_after_GST_ancestorOn facts
    S Hs Xb hf hHs hHsXb hcom hbelow hrec hdelay hpost hc hchor hread hhor hnext hu hv hAv
      hQnrun hnv hA2 hG hQnsg hQnbody hloPost hloOpen ht₀ hA
  simpa only [hQnerase] using hsplit

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
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- After the progress deadline plus one round, if the Q2 read at a node state of `p`'s round-`c`
    action read along `W` can return `Q`, then at the vote-duty read of every later slot `d` of
    round `c` by a member of the set for `vote_time d`, `Q` is an ancestor of the FG root or in the
    filtered tree. -/
theorem actionQ2_preceq_fgRoot_or_activeAtVoteDuty_after_deadlineOn (facts : Record.Facts M)
    {delayExtra : Nat}
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hbelow : BelowOneThirdOn S rho Hs)
    {rGST gap : Round} {t₀ : Int} (hrec : Restated.MultiProposerRecurrenceOn M S Hs gap t₀ rho.horizon)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    {c : Round} (hc : fgSafetyProgressDeadline S rho rGST gap delayExtra + 1 ≤ c)
    (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho c) (hchor : (Restated.Vocabulary.Execution.Setup.a M S c) ≤ rho.horizon)
    {p : V} (hp : p ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S c))) (hAp : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick p (Restated.Vocabulary.Execution.Setup.a M S c)) → M.awake_for_grade2 S p (W j p) c) {Q : Block V}
    {np : M.N}
    (hnp : np ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) p) c)
    (hQ : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S np c ⇢ some Q)
    {d : Slot} (hround : (M.round_of S.hc d) = c)
    (hvoteHor : M.vote_time S.E d ≤ rho.horizon)
    (hnext : M.vote_time S.E d ≤ (Restated.Vocabulary.Execution.Setup.a M S (c + 1)))
    {w : V} (hw : w ∈ Hs (M.vote_time S.E d))
    (hloPost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    (hloOpen : lo ≤ M.opening S.E S.hc (rGST + 2 - S.hc.η_SG))
    (ht₀ : t₀ ≤ (Restated.Vocabulary.Execution.Setup.a M S (rGST + 2)))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    ∀ cc : M.Cache,
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core.toHealing (M.vote_time S.E d)
        (W (strictEventIndex rho (M.vote_time S.E d)) w).cache ⇢ cc →
    Block.Preceq Q (M.get_fg_root (M.toHealing
        (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st
          (M.vote_time S.E d))
          (W (strictEventIndex rho (M.vote_time S.E d)) w).record cc).st.core).toFG) ∨
      Q ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
        (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st
          (M.vote_time S.E d))
          (W (strictEventIndex rho (M.vote_time S.E d)) w).record cc) := by
  have hdead : fgSafetyProgressDeadline S rho rGST gap delayExtra ≤ c := (Nat.le_succ _).trans hc
  have hcut : Restated.Vocabulary.Protocol.HealConfig.Γ_0 M S.hc S.E.Δ c ≤ M.vote_time S.E d :=
    Restated.Vocabulary.Proofs.HealingSurface.Γ_0_le_vote_time_of_round_eq facts S hround
  have hread : (Restated.Vocabulary.Execution.Setup.a M S (fgSafetyProgressDeadline S rho rGST gap delayExtra)) ≤
      M.vote_time S.E d := by
    have h1 : Restated.Vocabulary.Execution.Setup.a M S
          (fgSafetyProgressDeadline S rho rGST gap delayExtra) ≤
        Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ
          (fgSafetyProgressDeadline S rho rGST gap delayExtra + 1) := by
      have h := facts.gr.action_add_delta_le_next_Γ_neg1 S
        (fgSafetyProgressDeadline S rho rGST gap delayExtra)
      have hΔ := S.E.Δ_pos
      unfold Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 Restated.Vocabulary.Execution.Setup.a
      linarith
    exact le_trans
      (le_trans h1 (Restated.Vocabulary.Proofs.HealingSurface.Γ_neg1_mono facts S.hc S.E.Δ_pos hc))
      (le_trans (le_of_lt (Restated.Vocabulary.Proofs.HealingLemmas.Γ_neg1_lt_Γ_0 facts S.hc S.E.Δ_pos c))
        hcut)
  have hloc : lo ≤ M.opening S.E S.hc (c - S.hc.η_SG) := by
    refine hloOpen.trans (facts.gr.NamedOutageClosure_opening_mono S ?_)
    have h2 : rGST + 2 ≤ c := by
      have hbase : rGST + 1 ≤ fgSafetyProgressDeadline S rho rGST gap delayExtra := by
        unfold fgSafetyProgressDeadline
        exact Nat.le_add_right _ _
      exact (Nat.succ_le_succ hbase).trans hc
    exact Nat.sub_le_sub_right h2 _
  have hW := hf.onePath
  have hmemA := (p64b% mem_stateBeforeTime_along₆₄b) hf.sorted hW
    (Restated.Vocabulary.Execution.Setup.a M S c)
  have hQtree := Restated.Vocabulary.Proofs.HealingSurface.actionQ2_mem_filteredTree facts S rho p c _
    hmemA np hnp hQ
  have hQcore : Q ∈ np.st.core.T :=
    Restated.Vocabulary.Proofs.HealingSurface.mem_T_of_mem_filteredTree facts hQtree
  have hcoh := (Restated.Vocabulary.Proofs.HealingSurface.actionRead_invariant facts S rho p c _
    hmemA np hnp).1.1.1
  rw [hcoh] at hQcore
  obtain ⟨Qn, _hQnbody, hQnerase⟩ := Finset.mem_image.mp hQcore
  have hQnamed : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S np c ⇢ some Qn.erase := by
    rw [hQnerase]
    exact hQ
  have hsplit := Restated.selectedG2_filteredMem_or_preceq_root_after_GST_ancestorOn facts
    S Hs Xb hf hHs hHsXb hcom hbelow hrec hdelay hpost hdead ready hchor hread hcut
      hvoteHor hnext hw hp hAp hnp hQnamed hloc hloPost hloOpen ht₀ hA
  intro cc hcc
  rw [hQnerase] at hsplit
  rcases hsplit with hactive | hroot
  · refine Or.inr ?_
    show Q ∈ M.get_filtered_block_tree
      (M.toHealing (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st
        (M.vote_time S.E d))
        (W (strictEventIndex rho (M.vote_time S.E d)) w).record cc).st.core).toFG
    rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [(p60% setClock_filtered₆₀) facts S]
    exact hactive
  · refine Or.inl ?_
    rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [(p60% setClock_fgRoot₆₀) facts S]
    exact hroot

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
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- If `t_GST ≤ S.a rGST`, `lo ≤ opening (rGST + 2 − η_SG)`, the progress deadline from `rGST` is at
    most `c` and `S.a (c + 1)` is in the horizon, then `lo ≤ opening (c + 1 − η_SG)`,
    `lo ≤ early (c + 1) g2`, `lo ≤ domain (c + 1) g1`, `lo ≤ S.a (c + 1)` and round `c + 1` is
    ready. -/
theorem roundBounds_after_deadline_l86d (facts : Record.Facts M)
    {delayExtra : Nat}
    (S : Setup V) {rho : Record.Run V} {lo : Int} {rGST gap : Round}
    (hpost : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    (hloOpen : lo ≤ M.opening S.E S.hc (rGST + 2 - S.hc.η_SG))
    {c : Round} (hc : fgSafetyProgressDeadline S rho rGST gap delayExtra ≤ c)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) ≤ rho.horizon) :
    lo ≤ M.opening S.E S.hc (c + 1 - S.hc.η_SG) ∧
      lo ≤ M.early S.E S.hc (c + 1) .g2 ∧
      lo ≤ M.domain S.E S.hc (c + 1) .g1 ∧
      lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) ∧
      Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho (c + 1) := by
  have hbase : rGST + 1 ≤ fgSafetyProgressDeadline S rho rGST gap delayExtra := by
    unfold fgSafetyProgressDeadline
    exact Nat.le_add_right _ _
  have hroundDead : rGST + 2 ≤ c + 1 := Nat.succ_le_succ (hbase.trans hc)
  have hloc : lo ≤ M.opening S.E S.hc (c + 1 - S.hc.η_SG) :=
    hloOpen.trans (facts.gr.NamedOutageClosure_opening_mono S (Nat.sub_le_sub_right hroundDead _))
  obtain ⟨hloEarly, -, -, hloA⟩ := Restated.loBounds_l70 facts S (Nat.succ_pos c) hloc
  have hearlyG1 : M.early S.E S.hc (c + 1) .g2 ≤ M.domain S.E S.hc (c + 1) .g1 :=
    (facts.gr.early_g2_lt_domain S (c + 1) .g1).le
  exact ⟨hloc, hloEarly, hloEarly.trans hearlyG1, hloA,
    Restated.Vocabulary.Proofs.HealingSurface.gradeRoundReady_of_action_horizon facts S (Restated.Vocabulary.Proofs.HealingSurface.gstLagged_le_Γ_neg1_of_gst_le_a facts S rGST hpost)
      hroundDead hhor⟩

end

/-! ## The voter's prepared anchor -/

section
set_option autoImplicit false
open scoped DC
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- After the progress deadline, every anchor that `w`'s vote-duty read of a slot `d` of round
    `c + 1` along `W` can give is on one chain with the FG root of every node state of `p`'s
    round-`(c + 1)` action read along `W`. -/
theorem voterAnchorAt_compatible_actionFGRoot_after_GSTOn (facts : Record.Facts M)
    {delayExtra : Nat}
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hbelow : BelowOneThirdOn S rho Hs)
    {rGST gap : Round} {t₀ : Int}
    (hrec : Restated.MultiProposerRecurrenceOn M S Hs gap t₀ rho.horizon)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    {c : Round} (hc : fgSafetyProgressDeadline S rho rGST gap delayExtra ≤ c)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) ≤ rho.horizon)
    {d : Slot} (hdlo : (M.opening_slot S.hc (c + 1)) + 1 ≤ d)
    (hshor : M.vote_time S.E d + S.E.Δ ≤ rho.horizon)
    {p w : V} (hp : p ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (c + 1))))
    (hw : w ∈ Hs (M.vote_time S.E d))
    (hloPost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    (hloOpen : lo ≤ M.opening S.E S.hc (rGST + 2 - S.hc.η_SG))
    (ht₀ : t₀ ≤ (Restated.Vocabulary.Execution.Setup.a M S (rGST + 2)))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    ∀ cc : M.Cache,
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core.toHealing
        (M.vote_time S.E d)
        (W (strictEventIndex rho (M.vote_time S.E d)) w).cache ⇢ cc →
      let n := M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st
          (M.vote_time S.E d))
        (W (strictEventIndex rho (M.vote_time S.E d)) w).record cc
      ∀ A0 : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n
          (M.round_of S.hc n.st.core.s) ⇢ A0 →
      ∀ np ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (c + 1))) p) (c + 1),
        Block.compatible A0 (M.get_fg_root (M.toHealing np.st.core).toFG) = true := by
  intro cc hcc n A0 hA0 np hnp
  have hread :
      (Restated.Vocabulary.Execution.Setup.a M S
        (fgSafetyProgressDeadline S rho rGST gap delayExtra)) ≤
        (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) :=
    (Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone
      (hc.trans (Nat.le_succ c))
  have hs : (M.opening_slot S.hc)
      (fgSafetyProgressDeadline S rho rGST gap delayExtra) + 1 ≤ d :=
    (Nat.add_le_add_right (facts.gr.opening_slot_le_of_le S.hc (hc.trans (Nat.le_succ c)))
      1).trans hdlo
  have hnextSlot : (M.opening_slot S.hc (c + 1)) + 2 ≤ d + 1 := Nat.succ_le_succ hdlo
  have hnext : (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) ≤ M.vote_time S.E (d + 1) :=
    (Restated.Vocabulary.Protocol.action_lt_vote_time_two_after facts S (c + 1)).le.trans
      (facts.sch.vote_time_mono_slots S.E hnextSlot)
  have hnmem : n ∈ Restated.Vocabulary.Internal.NamedRecoveryRead.voteDutyRead M S rho w d :=
    ⟨W (strictEventIndex rho (M.vote_time S.E d)),
      (p64b% mem_stateBeforeTime_along₆₄b) hf.sorted hf.onePath _, cc, hcc, rfl⟩
  obtain ⟨Tr, hTr⟩ : ∃ Tr, M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ Tr :=
    facts.fc.voter_filtered_block_tree_nonempty _ _ _
  obtain ⟨L, hL⟩ : ∃ L,
      M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L :=
    facts.fc.voter_view_nonempty _ _ _
  obtain ⟨L', hL'⟩ : ∃ L',
      M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' :=
    facts.fc.voter_support_view_nonempty _ _ _
  obtain ⟨H, hH⟩ : ∃ H, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
      (M.toHealing n.st.core) Tr L L' (n.st.core.s - 1) ⇢ H :=
    facts.fc.get_head_in_tree_with_layer_nonempty _ _ _ _ _ _ _ _
  have h1 := Restated.Vocabulary.Proofs.HealingSurface.voterAnchorAt_preceq_voterHeadAt facts S rho
    w d n hnmem A0 hA0 Tr hTr L hL L' hL' H hH
  have h2 := Restated.fgRoot_preceq_previousHead_after_GSTOn facts S Hs Xb hf hHs hHsXb hcom
    hbelow hrec hdelay hpost hread hhor hs hnext hshor hp hloPost hloOpen ht₀ hA w hw cc hcc
    Tr hTr L hL L' hL' H hH
  rw [(p60% actionReadFrom_fgRoot₆₀s) facts S _ _ np hnp]
  exact compatible_of_preceq_common_Preceq h1 h2

/-- After the progress deadline, if a node state of `p`'s round-`(c + 1)` action read along `W` can
    return `Q` both as its Q2 and as its SG block, then every anchor that a later vote-duty read of
    an interior slot of round `c + 1` along `W` can give is on one chain with `Q`. -/
theorem voterAnchorAt_compatible_actionSGBlock_selectedQ2_after_GSTOn (facts : Record.Facts M)
    {delayExtra : Nat}
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hbelow : BelowOneThirdOn S rho Hs)
    {rGST gap : Round} {t₀ : Int}
    (hrec : Restated.MultiProposerRecurrenceOn M S Hs gap t₀ rho.horizon)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    {c : Round} (hc : fgSafetyProgressDeadline S rho rGST gap delayExtra ≤ c)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) ≤ rho.horizon)
    {d : Slot} (hdlo : (M.opening_slot S.hc (c + 1)) + 1 ≤ d)
    (hdhi : d < (M.opening_slot S.hc (c + 1 + 1)))
    (hvoteHor : M.vote_time S.E d ≤ rho.horizon)
    {p w : V} (hp : p ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (c + 1))))
    (hAp : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick p (Restated.Vocabulary.Execution.Setup.a M S (c + 1))) → M.awake_for_grade2 S p (W j p) (c + 1))
    (hw : w ∈ Hs (M.vote_time S.E d))
    {Q : Block V}
    {np : M.N}
    (hnp : np ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (c + 1))) p) (c + 1))
    (hQ : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S np (c + 1) ⇢ some Q)
    {A2 : Option (Block V)}
    (hA2 : M.grade2_block_with (M.gradeContract np.cache) S.E S.hc (M.toHealing np.st.core)
      (M.round_of S.hc (M.toHealing np.st.core).s) ⇢ A2)
    (hsg : M.get_sg_vote_with (M.gradeContract np.cache) S.E S.hc (M.toHealing np.st.core)
      (M.round_of S.hc (M.toHealing np.st.core).s) A2 ⇢ Q)
    (hloPost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    (hloOpen : lo ≤ M.opening S.E S.hc (rGST + 2 - S.hc.η_SG))
    (ht₀ : t₀ ≤ (Restated.Vocabulary.Execution.Setup.a M S (rGST + 2)))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    ∀ cc : M.Cache,
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core.toHealing
        (M.vote_time S.E d)
        (W (strictEventIndex rho (M.vote_time S.E d)) w).cache ⇢ cc →
      let n := M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st
          (M.vote_time S.E d))
        (W (strictEventIndex rho (M.vote_time S.E d)) w).record cc
      ∀ A0 : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n
          (M.round_of S.hc n.st.core.s) ⇢ A0 →
        Block.compatible A0 Q = true := by
  intro cc hcc n A0 hA0
  have hround : (M.round_of S.hc d) = c + 1 :=
    facts.gr.round_of_eq_of_opening_succ_le_of_lt_next_opening S.hc hdlo hdhi
  have hnextFrame : M.vote_time S.E d ≤ M.opening S.E S.hc (c + 1 + 1) := by
    rw [facts.gr.opening_eq_proposal_time]
    exact (facts.sch.voteTime_lt_nextProposal_l86d S.E d).le.trans
      (facts.sch.proposal_time_mono S.E (Nat.succ_le_of_lt hdhi))
  obtain ⟨hloc, hloEarly, hgatG1, -, ready⟩ :=
    Restated.roundBounds_after_deadline_l86d facts S hpost hloOpen hc hhor
  have hcut : Restated.Vocabulary.Protocol.HealConfig.Γ_0 M S.hc S.E.Δ (c + 1) ≤
      M.vote_time S.E d :=
    Restated.Vocabulary.Proofs.HealingSurface.Γ_0_le_vote_time_of_round_eq facts S hround
  have hdomG1 : M.domain S.E S.hc (c + 1) .g1 =
      Restated.Vocabulary.Protocol.HealConfig.Γ_0 M S.hc S.E.Δ (c + 1) := by
    rw [facts.gr.Sts_domain_g1_eq_opening, facts.gr.opening_eq_proposal_time]
    exact (facts.sch.Γ_0_eq_proposal_time S.hc S.E (c + 1)).symm
  have hwG1 : w ∈ Hs (M.domain S.E S.hc (c + 1) .g1) := hHs _ _ (hdomG1.trans_le hcut) hw
  have hpDom : ∀ q : Phase, p ∈ Hs (M.domain S.E S.hc (c + 1) q) :=
    fun q => hHs _ _ (facts.gr.domain_le_a S (c + 1) q) hp
  have hnst : n.st = M.store_with_cache (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st (M.vote_time S.E d)) _ := facts.nd.mkNode_st _ _ _
  have hnmem : n ∈ Restated.Vocabulary.Internal.NamedRecoveryRead.voteDutyRead M S rho w d :=
    ⟨W (strictEventIndex rho (M.vote_time S.E d)),
      (p64b% mem_stateBeforeTime_along₆₄b) hf.sorted hf.onePath _, cc, hcc, rfl⟩
  rcases Restated.Vocabulary.Proofs.HealingSurface.voterAnchorAt_cases facts S rho w d n hnmem A0
      hA0 with hroot | ⟨root, L, hframe, hactive, hanchor⟩
  · rw [hroot, hnst]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    rw [(p60% setClock_fgRoot₆₀) facts S]
    have hdeadlineVote :
        (Restated.Vocabulary.Execution.Setup.a M S
          (fgSafetyProgressDeadline S rho rGST gap delayExtra)) ≤ M.vote_time S.E d := by
      have h1 : Restated.Vocabulary.Execution.Setup.a M S
            (fgSafetyProgressDeadline S rho rGST gap delayExtra) ≤
          Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ
            (fgSafetyProgressDeadline S rho rGST gap delayExtra + 1) := by
        have h := facts.gr.action_add_delta_le_next_Γ_neg1 S
          (fgSafetyProgressDeadline S rho rGST gap delayExtra)
        have hΔ := S.E.Δ_pos
        unfold Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 Restated.Vocabulary.Execution.Setup.a
        linarith
      exact le_trans
        (le_trans h1 (Restated.Vocabulary.Proofs.HealingSurface.Γ_neg1_mono facts S.hc S.E.Δ_pos
          (Nat.succ_le_succ hc)))
        (le_trans (le_of_lt (Restated.Vocabulary.Proofs.HealingLemmas.Γ_neg1_lt_Γ_0 facts S.hc
          S.E.Δ_pos (c + 1))) hcut)
    have hnext : M.vote_time S.E d ≤ (Restated.Vocabulary.Execution.Setup.a M S (c + 1 + 1)) :=
      (facts.sch.vote_time_mono_slots S.E (Nat.le_of_lt hdhi)).trans
        (Restated.Vocabulary.Protocol.opening_vote_time_lt_action facts S (c + 1 + 1)).le
    exact Restated.fgRoot_compatible_actionSGBlock_at_read_after_GSTOn_l86c facts S Hs Xb hf
      hHs hHsXb hcom hbelow hrec hdelay hpost (hc.trans (Nat.le_succ c)) hhor hdeadlineVote
      hvoteHor hnext hw hp hAp hloPost hloOpen ht₀ hA np hnp A2 hA2 Q hsg
  · have hroundRead : (M.round_of S.hc n.st.core.s) = c + 1 := by
      rw [hnst]
      try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
      rw [facts.hd.Sts_setClock_core_s, facts.sch.slotOf_vote_time]
      exact hround
    rw [hroundRead] at hframe
    obtain ⟨-, hLgrade⟩ := Restated.fixedRoot_activeVoterAnchor_g1_dataOn facts S Hs Xb hf
      (Nat.succ_pos c) ((Nat.le_succ _).trans hdlo) hround hnextFrame hvoteHor hwG1 cc hcc hframe
      hactive hgatG1
    have hguard := Restated.actionQ2_crossReaderBodyReadyGuard_historyOn facts S Hs Xb hf
      hHs hHsXb (Nat.succ_pos c) ready (hpDom .g0) hloEarly np hnp w hwG1 Q hQ
    have hQgrade := Restated.selectedG2_G1_at_read_after_cutoffOn facts S Hs Xb hf hHs
      hHsXb ready hhor (hpDom .g2) hwG1 np hnp hQ hguard hloc
    obtain ⟨bL, hbL⟩ := facts.gr.gradeBool_nonempty S.E
      (M.gradeView (M.toHealing
        (W (strictEventIndex rho (M.domain S.E S.hc (c + 1) .g1)) w).st.core))
      (W (strictEventIndex rho (M.domain S.E S.hc (c + 1) .g1)) w).st.core.F
      S.hc.η_SG (c + 1) (M.early S.E S.hc (c + 1) .g1) (M.late S.E S.hc (c + 1) .g1) L
    obtain ⟨bQ, hbQ⟩ := facts.gr.gradeBool_nonempty S.E
      (M.gradeView (M.toHealing
        (W (strictEventIndex rho (M.domain S.E S.hc (c + 1) .g1)) w).st.core))
      (W (strictEventIndex rho (M.domain S.E S.hc (c + 1) .g1)) w).st.core.F
      S.hc.η_SG (c + 1) (M.early S.E S.hc (c + 1) .g1) (M.late S.E S.hc (c + 1) .g1) Q
    have hbLt : bL = true := hLgrade bL hbL
    have hbQt : bQ = true := hQgrade bQ hbQ
    subst hbLt
    subst hbQt
    rw [hanchor]
    exact Restated.Vocabulary.Proofs.HealingSurface.relativeSeed_sameReaderG1_compatible facts S rho
      (c + 1) w _
      ⟨_, (p64b% mem_stateBeforeTime_along₆₄b) hf.sorted hf.onePath
        (M.domain S.E S.hc (c + 1) .g1), rfl⟩ hbL hbQ

/-- After the progress deadline, if at a node state of `p`'s round-`(c + 1)` action read along `W`
    the clear test of `B` can return `true` and the SG vote selector can return `B`, then every
    anchor that a later vote-duty read of an interior slot of round `c + 1` along `W` can give is on
    one chain with `B`. -/
theorem voterAnchorAt_compatible_actionSGBlock_clear_after_GSTOn (facts : Record.Facts M)
    {delayExtra : Nat}
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hbelow : BelowOneThirdOn S rho Hs)
    {rGST gap : Round} {t₀ : Int}
    (hrec : Restated.MultiProposerRecurrenceOn M S Hs gap t₀ rho.horizon)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    {c : Round} (hc : fgSafetyProgressDeadline S rho rGST gap delayExtra ≤ c)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) ≤ rho.horizon)
    {d : Slot} (hdlo : (M.opening_slot S.hc (c + 1)) + 1 ≤ d)
    (hdhi : d < (M.opening_slot S.hc (c + 1 + 1)))
    (hvoteHor : M.vote_time S.E d ≤ rho.horizon)
    (hshor : M.vote_time S.E d + S.E.Δ ≤ rho.horizon)
    {p w : V} (hp : p ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (c + 1))))
    (hAp : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick p (Restated.Vocabulary.Execution.Setup.a M S (c + 1))) → M.awake_for_grade2 S p (W j p) (c + 1))
    (hw : w ∈ Hs (M.vote_time S.E d))
    {B : Block V}
    {np : M.N}
    (hnp : np ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (c + 1))) p) (c + 1))
    (hclear : Restated.Vocabulary.Internal.PhaseGrades.nodeClear M S np (c + 1) B ⇢ true)
    {A2 : Option (Block V)}
    (hA2 : M.grade2_block_with (M.gradeContract np.cache) S.E S.hc (M.toHealing np.st.core)
      (M.round_of S.hc (M.toHealing np.st.core).s) ⇢ A2)
    (hsg : M.get_sg_vote_with (M.gradeContract np.cache) S.E S.hc (M.toHealing np.st.core)
      (M.round_of S.hc (M.toHealing np.st.core).s) A2 ⇢ B)
    (hloPost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    (hloOpen : lo ≤ M.opening S.E S.hc (rGST + 2 - S.hc.η_SG))
    (ht₀ : t₀ ≤ (Restated.Vocabulary.Execution.Setup.a M S (rGST + 2)))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    ∀ cc : M.Cache,
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core.toHealing
        (M.vote_time S.E d)
        (W (strictEventIndex rho (M.vote_time S.E d)) w).cache ⇢ cc →
      let n := M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st
          (M.vote_time S.E d))
        (W (strictEventIndex rho (M.vote_time S.E d)) w).record cc
      ∀ A0 : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n
          (M.round_of S.hc n.st.core.s) ⇢ A0 →
        Block.compatible A0 B = true := by
  intro cc hcc n A0 hA0
  have hround : (M.round_of S.hc d) = c + 1 :=
    facts.gr.round_of_eq_of_opening_succ_le_of_lt_next_opening S.hc hdlo hdhi
  have hnextFrame : M.vote_time S.E d ≤ M.opening S.E S.hc (c + 1 + 1) := by
    rw [facts.gr.opening_eq_proposal_time]
    exact (facts.sch.voteTime_lt_nextProposal_l86d S.E d).le.trans
      (facts.sch.proposal_time_mono S.E (Nat.succ_le_of_lt hdhi))
  obtain ⟨hloc, hloEarly, hgatG1, -, -⟩ :=
    Restated.roundBounds_after_deadline_l86d facts S hpost hloOpen hc hhor
  have hcut : Restated.Vocabulary.Protocol.HealConfig.Γ_0 M S.hc S.E.Δ (c + 1) ≤
      M.vote_time S.E d :=
    Restated.Vocabulary.Proofs.HealingSurface.Γ_0_le_vote_time_of_round_eq facts S hround
  have hdomG1 : M.domain S.E S.hc (c + 1) .g1 =
      Restated.Vocabulary.Protocol.HealConfig.Γ_0 M S.hc S.E.Δ (c + 1) := by
    rw [facts.gr.Sts_domain_g1_eq_opening, facts.gr.opening_eq_proposal_time]
    exact (facts.sch.Γ_0_eq_proposal_time S.hc S.E (c + 1)).symm
  have hwG1 : w ∈ Hs (M.domain S.E S.hc (c + 1) .g1) := hHs _ _ (hdomG1.trans_le hcut) hw
  have hpDom : ∀ q : Phase, p ∈ Hs (M.domain S.E S.hc (c + 1) q) :=
    fun q => hHs _ _ (facts.gr.domain_le_a S (c + 1) q) hp
  have hg1g0 : M.domain S.E S.hc (c + 1) .g1 ≤ M.domain S.E S.hc (c + 1) .g0 :=
    facts.gr.domain_le_domain_g0 S (c + 1) .g1
  have hdomG0Hor : M.domain S.E S.hc (c + 1) .g0 ≤ rho.horizon :=
    (facts.gr.domain_le_a S (c + 1) .g0).trans hhor
  have hnst : n.st = M.store_with_cache (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st (M.vote_time S.E d)) _ := facts.nd.mkNode_st _ _ _
  have hnmem : n ∈ Restated.Vocabulary.Internal.NamedRecoveryRead.voteDutyRead M S rho w d :=
    ⟨W (strictEventIndex rho (M.vote_time S.E d)),
      (p64b% mem_stateBeforeTime_along₆₄b) hf.sorted hf.onePath _, cc, hcc, rfl⟩
  rcases Restated.Vocabulary.Proofs.HealingSurface.voterAnchorAt_cases facts S rho w d n hnmem A0
      hA0 with hroot | ⟨root, L, hframe, hactive, hanchor⟩
  · rw [hroot, hnst]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    rw [(p60% setClock_fgRoot₆₀) facts S]
    have hdeadlineVote :
        (Restated.Vocabulary.Execution.Setup.a M S
          (fgSafetyProgressDeadline S rho rGST gap delayExtra)) ≤ M.vote_time S.E d := by
      have h1 : Restated.Vocabulary.Execution.Setup.a M S
            (fgSafetyProgressDeadline S rho rGST gap delayExtra) ≤
          Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ
            (fgSafetyProgressDeadline S rho rGST gap delayExtra + 1) := by
        have h := facts.gr.action_add_delta_le_next_Γ_neg1 S
          (fgSafetyProgressDeadline S rho rGST gap delayExtra)
        have hΔ := S.E.Δ_pos
        unfold Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 Restated.Vocabulary.Execution.Setup.a
        linarith
      exact le_trans
        (le_trans h1 (Restated.Vocabulary.Proofs.HealingSurface.Γ_neg1_mono facts S.hc S.E.Δ_pos
          (Nat.succ_le_succ hc)))
        (le_trans (le_of_lt (Restated.Vocabulary.Proofs.HealingLemmas.Γ_neg1_lt_Γ_0 facts S.hc
          S.E.Δ_pos (c + 1))) hcut)
    have hnext : M.vote_time S.E d ≤ (Restated.Vocabulary.Execution.Setup.a M S (c + 1 + 1)) :=
      (facts.sch.vote_time_mono_slots S.E (Nat.le_of_lt hdhi)).trans
        (Restated.Vocabulary.Protocol.opening_vote_time_lt_action facts S (c + 1 + 1)).le
    exact Restated.fgRoot_compatible_actionSGBlock_at_read_after_GSTOn_l86c facts S Hs Xb hf
      hHs hHsXb hcom hbelow hrec hdelay hpost (hc.trans (Nat.le_succ c)) hhor hdeadlineVote
      hvoteHor hnext hw hp hAp hloPost hloOpen ht₀ hA np hnp A2 hA2 B hsg
  · have hroundRead : (M.round_of S.hc n.st.core.s) = c + 1 := by
      rw [hnst]
      try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
      rw [facts.hd.Sts_setClock_core_s, facts.sch.slotOf_vote_time]
      exact hround
    rw [hroundRead] at hframe
    obtain ⟨-, hLgrade⟩ := Restated.fixedRoot_activeVoterAnchor_g1_dataOn facts S Hs Xb hf
      (Nat.succ_pos c) ((Nat.le_succ _).trans hdlo) hround hnextFrame hvoteHor hwG1 cc hcc hframe
      hactive hgatG1
    have hrootCompat := Restated.voterAnchorAt_compatible_actionFGRoot_after_GSTOn facts S Hs Xb
      hf hHs hHsXb hcom hbelow hrec hdelay hpost hc hhor hdlo hshor hp hw hloPost hloOpen
      ht₀ hA cc hcc A0 hA0 np hnp
    rw [hanchor] at hrootCompat ⊢
    have hmemA := (p64b% mem_stateBeforeTime_along₆₄b) hf.sorted hf.onePath
      (Restated.Vocabulary.Execution.Setup.a M S (c + 1))
    rcases (show Block.Preceq L (M.get_fg_root (M.toHealing np.st.core).toFG) ∨
        Block.Preceq (M.get_fg_root (M.toHealing np.st.core).toFG) L from
      compatible_cases hrootCompat) with hLroot | hrootL
    · exact compatible_of_cases (Or.inl (preceq_trans_Preceq hLroot
        (Restated.Vocabulary.Proofs.HealingSurface.actionFGRoot_preceq_actionSGBlockAt facts S rho p
          (c + 1) _ hmemA np hnp A2 hA2 B hsg)))
    · have hnpF : np.st.core.F =
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (c + 1))) p).st.core.F :=
        (p64b% actionReadFrom_F₆₄b) facts S _ _ np hnp
      have hFroot : Block.Preceq np.st.core.F (M.get_fg_root (M.toHealing np.st.core).toFG) := by
        rw [hnpF, (p60% actionReadFrom_fgRoot₆₀s) facts S _ _ np hnp]
        exact Restated.finalizedRoot_preceq_fgRootOn facts S Hs Xb hf
      have hFL : Block.Preceq np.st.core.F L := preceq_trans_Preceq hFroot hrootL
      have hgstG1 : lo ≤ M.early S.E S.hc (c + 1) .g1 :=
        hloEarly.trans (facts.gr.early_g2_le_early_g1 S.E S.hc (c + 1))
      have hF0L : Block.Preceq
          (W (strictEventIndex rho (M.domain S.E S.hc (c + 1) .g0)) p).st.core.F L :=
        preceq_trans_Preceq
          (Restated.incl_strict_F_monoOn facts S rho Hs Xb hf p
            (facts.gr.domain_le_a S (c + 1) .g0))
          (by rw [← hnpF]; exact hFL)
      have hfinalized := Restated.g1G0CrossReaderFinalizedBelow_of_finalitySafety_and_relayOn facts
        S Hs Xb hf hHs hHsXb hf.slashableBound hgstG1 hdomG0Hor hwG1 (hpDom .g0) (B := L)
        (by
          intro sender u key H I _ _ c' hcov hc' hconf hfind
          apply preceq_trans_Preceq hF0L
          rw [hconf] at hcov
          exact facts.gr.preceq_of_localCovers_of_find c' hcov hc' hfind)
      have hguard := Restated.g1G0CrossReaderBodyReadyGuard_of_finalizedBelowOn facts
        S Hs Xb hf hHs hHsXb (Nat.succ_pos c) hgstG1 hdomG0Hor hwG1 (hpDom .g0) hfinalized
      obtain ⟨bL, hbL⟩ := facts.gr.gradeBool_nonempty S.E
        (M.gradeView (M.toHealing
          (W (strictEventIndex rho (M.domain S.E S.hc (c + 1) .g1)) w).st.core))
        (W (strictEventIndex rho (M.domain S.E S.hc (c + 1) .g1)) w).st.core.F
        S.hc.η_SG (c + 1) (M.early S.E S.hc (c + 1) .g1) (M.late S.E S.hc (c + 1) .g1) L
      have hbLt : bL = true := hLgrade bL hbL
      subst hbLt
      have hG0 := Restated.storeGrade_g0_of_storeGrade_g1_cross_readerOn facts
        S rho Hs Xb hf hHs hHsXb (c + 1) hloc hdomG0Hor w p hwG1 (hpDom .g0) L hbL hguard
      obtain ⟨b0, hb0⟩ := facts.gr.gradeBool_nonempty S.E
        (M.gradeView (M.toHealing
          (W (strictEventIndex rho (M.domain S.E S.hc (c + 1) .g0)) p).st.core))
        (W (strictEventIndex rho (M.domain S.E S.hc (c + 1) .g0)) p).st.core.F
        S.hc.η_SG (c + 1) (M.early S.E S.hc (c + 1) .g0) (M.late S.E S.hc (c + 1) .g0) L
      have hb0t : b0 = true := hG0 b0 hb0
      subst hb0t
      exact Restated.relativeG0_compatible_clearSource_of_finalizedPreceq_historyOn facts
        S Hs Xb hf (Nat.succ_pos c) hhor (hpDom .g0)
        (Restated.Vocabulary.Proofs.HealingSurface.storeGrade_g0_mem_domainTree facts S rho _
          ⟨_, (p64b% mem_stateBeforeTime_along₆₄b) hf.sorted hf.onePath
            (M.domain S.E S.hc (c + 1) .g0), rfl⟩ hb0)
        hb0 hnp hFL hclear (hgatG1.trans hg1g0)

/-- After the progress deadline, every anchor that `w`'s vote-duty read of an interior slot of round
    `c + 1` along `W` can give is on one chain with every SG block that `p`'s round-`(c + 1)` action
    read along `W` can select. -/
theorem voterAnchorAt_firstInterior_compatible_actionSGBlock_after_GSTOn (facts : Record.Facts M)
    {delayExtra : Nat}
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hbelow : BelowOneThirdOn S rho Hs)
    {rGST gap : Round} {t₀ : Int}
    (hrec : Restated.MultiProposerRecurrenceOn M S Hs gap t₀ rho.horizon)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    {c : Round} (hc : fgSafetyProgressDeadline S rho rGST gap delayExtra ≤ c)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) ≤ rho.horizon)
    {d : Slot} (hdlo : (M.opening_slot S.hc (c + 1)) + 1 ≤ d)
    (hdhi : d < (M.opening_slot S.hc (c + 1 + 1)))
    (hvoteHor : M.vote_time S.E d ≤ rho.horizon)
    (hshor : M.vote_time S.E d + S.E.Δ ≤ rho.horizon)
    {p w : V} (hp : p ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (c + 1))))
    (hAp : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick p (Restated.Vocabulary.Execution.Setup.a M S (c + 1))) → M.awake_for_grade2 S p (W j p) (c + 1))
    (hw : w ∈ Hs (M.vote_time S.E d))
    (hloPost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    (hloOpen : lo ≤ M.opening S.E S.hc (rGST + 2 - S.hc.η_SG))
    (ht₀ : t₀ ≤ (Restated.Vocabulary.Execution.Setup.a M S (rGST + 2)))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    ∀ cc : M.Cache,
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core.toHealing
        (M.vote_time S.E d)
        (W (strictEventIndex rho (M.vote_time S.E d)) w).cache ⇢ cc →
      let n := M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st
          (M.vote_time S.E d))
        (W (strictEventIndex rho (M.vote_time S.E d)) w).record cc
      ∀ A0 : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n
          (M.round_of S.hc n.st.core.s) ⇢ A0 →
      ∀ np ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (c + 1))) p) (c + 1),
      ∀ A2 : Option (Block V),
        M.grade2_block_with (M.gradeContract np.cache) S.E S.hc (M.toHealing np.st.core)
          (M.round_of S.hc (M.toHealing np.st.core).s) ⇢ A2 →
      ∀ G : Block V,
        M.get_sg_vote_with (M.gradeContract np.cache) S.E S.hc (M.toHealing np.st.core)
          (M.round_of S.hc (M.toHealing np.st.core).s) A2 ⇢ G →
        Block.compatible A0 G = true := by
  intro cc hcc n A0 hA0 np hnp A2 hA2 G hG
  have hraw := Restated.nodeRawG2_at_action_after_recovery_deadlineOn facts S Hs Xb hf hHs
    hHsXb hcom hbelow hrec hdelay hpost hc hhor hloPost hloOpen ht₀ hA p
    (hHs _ _ (facts.gr.domain_le_a S (c + 1) .g2) hp) np hnp
  obtain ⟨g, hg⟩ : ∃ g, Restated.Vocabulary.Internal.PhaseGrades.nodeRead M S np (c + 1) ⇢ g :=
    facts.gr.read_nonempty _ _ _ _ _
  have hnpMem : np ∈ Restated.Vocabulary.Proofs.HealingSurface.actionReadAt M S rho p (c + 1) :=
    ⟨W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (c + 1))),
      (p64b% mem_stateBeforeTime_along₆₄b) hf.sorted hf.onePath _, hnp⟩
  rcases Restated.Vocabulary.Proofs.HealingSurface.actionSGBlockAt_tiers_of_rawG2 facts S rho p
      (c + 1) np hnpMem g hg (hraw g hg) A2 hA2 G hG with hclear | ⟨Q, hQ, hsg⟩ | hsg
  · have hcl : Restated.Vocabulary.Internal.PhaseGrades.nodeClear M S np (c + 1) G ⇢ g.clear G :=
      (p60% returns_map_intro₆₀) (fun x : Protocol.GradeRead V => x.clear G)
        (Restated.Vocabulary.Internal.PhaseGrades.nodeRead M S np (c + 1)) g hg
    rw [hclear.2.2] at hcl
    exact Restated.voterAnchorAt_compatible_actionSGBlock_clear_after_GSTOn facts S Hs Xb hf
      hHs hHsXb hcom hbelow hrec hdelay hpost hc hhor hdlo hdhi hvoteHor hshor hp hAp hw hnp hcl
      hA2 hG hloPost hloOpen ht₀ hA cc hcc A0 hA0
  · have hq : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S np (c + 1) ⇢ g.Q2 :=
      (p60% returns_map_intro₆₀) (fun x : Protocol.GradeRead V => x.Q2)
        (Restated.Vocabulary.Internal.PhaseGrades.nodeRead M S np (c + 1)) g hg
    rw [hQ] at hq
    subst hsg
    exact Restated.voterAnchorAt_compatible_actionSGBlock_selectedQ2_after_GSTOn facts S Hs Xb hf
      hHs hHsXb hcom hbelow hrec hdelay hpost hc hhor hdlo hdhi hvoteHor hp hAp hw hnp hq
      hA2 hG hloPost hloOpen ht₀ hA cc hcc A0 hA0
  · rw [hsg]
    exact Restated.voterAnchorAt_compatible_actionFGRoot_after_GSTOn facts S Hs Xb hf hHs
      hHsXb hcom hbelow hrec hdelay hpost hc hhor hdlo hshor hp hw hloPost hloOpen ht₀ hA cc hcc
      A0 hA0 np hnp

end

end DecoupledConsensusModel.Sts.Restated
