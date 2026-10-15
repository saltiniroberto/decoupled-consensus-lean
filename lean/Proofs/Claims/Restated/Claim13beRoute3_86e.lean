import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bK_ConeAnchor
import Proofs.Claims.Restated.Claim13beRoute3_44
import Proofs.Claims.Restated.Claim13beRoute3_47
import Proofs.Claims.Restated.Claim13beRoute3_48b
import Proofs.Claims.Restated.Claim13beRoute3_49
import Proofs.Claims.Restated.Claim13beRoute3_54
import Proofs.Claims.Restated.Claim13beRoute3_55
import Proofs.Claims.Restated.Claim13beRoute3_58
import Proofs.Claims.Restated.Claim13beRoute3_59
import Proofs.Claims.Restated.Claim13beRoute3_60
import Proofs.Claims.Restated.Claim13beRoute3_65
import Proofs.Claims.Restated.Claim13beRoute3_65b
import Proofs.Claims.Restated.Claim13beRoute3_71
import Proofs.Claims.Restated.Claim13beRoute3_86c
import Proofs.Claims.Restated.Claim13beRoute3_86d
import Proofs.Claims.Restated.Vocabulary_Execution_EmissionShape
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Proofs.Claims.Restated.Vocabulary_Execution_PreparedReadBridge
import Proofs.Claims.Restated.Vocabulary_Execution_RecoveryActionLiveSourceSplit
import Proofs.Claims.Restated.Vocabulary_ModelVocabulary_Healing_Schedule
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_ActionConfirmationCore
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_RecoveryProposalConfirmationRead
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_SeedEntryCanonical
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Views_RecoveryVoteCone
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_Grades
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_Ladder
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_SGFirstInteriorAnchorNamed
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_W4GSTZeroOpeningLifecycle
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_Action
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_PostHealingReuse
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_SlotInduction
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.RunAll
import Model.Conditions.RunVocabulary
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Internal_Definitions_NamedLifecycle
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGradeQueries
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Internal_HealingSurface
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedHeadReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_ModelVocabulary_Healing_Schedule
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Adoption
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Agreement
import Model.Conditions.Vocabulary_Protocol_Grades_GoldfishConePersistence
import Model.Conditions.Vocabulary_Protocol_Grades_ProposalLifecycleCore
import Model.Conditions.Vocabulary_Protocol_Handlers_Blocks
import Model.Conditions.Vocabulary_Protocol_Handlers_TickBridges
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_86e

/-!
# SG blocks are ancestors of later heads after the progress deadline

Theorems over a model `M : Record.Model V`, read along one path `W` of the run: after the progress
deadline, every SG block of round `c + 1` selected by a member of the set is an ancestor of every
head from the round's first interior slot on, by an induction over slots.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

/-- Refers to a private theorem of `Proofs.Claims.Restated.Claim13beRoute3_64b` by name. -/
local macro "p64b% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_64b)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- Refers to a private theorem of `Proofs.Claims.Restated.Claim13beRoute3_60` by name. -/
local macro "p60% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_60)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- Refers to a private theorem of `Proofs.Claims.Restated.Claim13beRoute3_59` by name. -/
local macro "p59% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_59)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- Refers to a private theorem of `Proofs.Claims.Restated.Claim13beRoute3_55` by name. -/
local macro "p55% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_55)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- Refers to a private theorem of `Proofs.Claims.Restated.Claim13beRoute3_71` by name. -/
local macro "p71% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_71)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- Refers to a private theorem of `Proofs.Claims.Restated.Claim13beRoute3_86c` by name. -/
local macro "p86c% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_86c)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs

/-- The action instant of round `r` is at or before the earliest grade cutoff of round `r + 1`. -/
private theorem a_le_Γ_neg1_succ₈₆e (facts : Record.Facts M) (S : Setup V) (r : Round) :
    Restated.Vocabulary.Execution.Setup.a M S r ≤
      Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (r + 1) := by
  have h := facts.gr.action_add_delta_le_next_Γ_neg1 S r
  have hΔ := S.E.Δ_pos
  unfold Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 Restated.Vocabulary.Execution.Setup.a
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
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- If `lo ≤ S.a rGST`, the progress deadline from `rGST` is at most `c` and `S.a (c + 1)` is in the
    horizon, then `lo ≤ proposal_time (opening_slot (c + 1))`, the deadline's action instant is
    before `vote_time (opening_slot (c + 1) + 1)`, and that vote instant is in the horizon. -/
theorem firstInterior_schedule_l86e (facts : Record.Facts M)
    {delayExtra : Nat}
    (S : Setup V) {rho : Record.Run V} {lo : Int} {rGST gap c : Round}
    (hloPost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    (hc : fgSafetyProgressDeadline S rho rGST gap delayExtra ≤ c)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) ≤ rho.horizon) :
    lo ≤ M.proposal_time S.E ((M.opening_slot S.hc (c + 1))) ∧
      (Restated.Vocabulary.Execution.Setup.a M S (fgSafetyProgressDeadline S rho rGST gap delayExtra)) <
        M.vote_time S.E ((M.opening_slot S.hc (c + 1)) + 1) ∧
      M.vote_time S.E ((M.opening_slot S.hc (c + 1)) + 1) ≤ rho.horizon := by
  have hGSTdead : rGST ≤ fgSafetyProgressDeadline S rho rGST gap delayExtra := by
    unfold fgSafetyProgressDeadline
    exact (Nat.le_succ rGST).trans (Nat.le_add_right _ _)
  have hloc : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S c) := hloPost.trans ((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone (hGSTdead.trans hc))
  have hround : (M.round_of S.hc ((M.opening_slot S.hc (c + 1)) + 1)) = c + 1 :=
    facts.gr.round_of_eq_of_opening_succ_le_of_lt_next_opening S.hc (le_refl _)
      (facts.gr.firstInterior_lt_nextOpening_l86e S (c + 1))
  have hcut := Restated.Vocabulary.Proofs.HealingSurface.Γ_0_le_vote_time_of_round_eq facts S hround
  refine ⟨(hloc.trans (a_le_Γ_neg1_succ₈₆e facts S c)).trans
    ((Restated.Vocabulary.Proofs.HealingLemmas.Γ_neg1_lt_Γ_0 facts S.hc S.E.Δ_pos (c + 1)).le.trans
      (le_of_eq (facts.sch.Γ_0_eq_proposal_time S.hc S.E (c + 1)))), ?_,
    (Restated.Vocabulary.Protocol.next_vote_time_lt_action facts S (c + 1)).le.trans hhor⟩
  exact (((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone hc).trans
    (a_le_Γ_neg1_succ₈₆e facts S c)).trans_lt
    ((Restated.Vocabulary.Proofs.HealingLemmas.Γ_neg1_lt_Γ_0 facts S.hc S.E.Δ_pos (c + 1)).trans_le
      hcut)

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

/-- If `lo ≤ S.a r` and `r < k`, then `lo` is at or before one delay before round `k`'s early
    grade-1 cutoff. -/
private theorem lo_le_early_g1₈₆e (facts : Record.Facts M) (S : Setup V) {lo : Int} {r k : Round}
    (hlo : lo ≤ Restated.Vocabulary.Execution.Setup.a M S r) (hrk : r < k) :
    lo ≤ M.early S.E S.hc k .g1 - S.E.Δ := by
  have h1 := facts.gr.action_delta_le_early S S.hc.R_ge_three hrk
  have h2 := facts.gr.q10_early_g2_le_early_g1 S k
  have h3 : lo ≤ M.a S.hc S.E.Δ r := hlo
  linarith

/-- A round at or after the progress deadline from `rGST` is after `rGST`. -/
private theorem rGST_lt_of_deadline_le₈₆e {delayExtra : Nat} (S : Setup V) {rho : Record.Run V}
    {rGST gap c : Round} (hc : fgSafetyProgressDeadline S rho rGST gap delayExtra ≤ c) :
    rGST < c := by
  have h : rGST + 1 ≤ fgSafetyProgressDeadline S rho rGST gap delayExtra := by
    unfold fgSafetyProgressDeadline
    exact Nat.le_add_right _ _
  exact lt_of_lt_of_le (Nat.lt_of_succ_le h) hc

/-- After the progress deadline, if `C` satisfies `GenuineConfirmationWith` for `v`'s confirmation
    store at round `(c + 1)`'s opening slot along `W`, and `G ⪯ C` is an SG block that `v`'s
    round-`(c + 1)` action read along `W` can select, then `G` is an ancestor of every head that
    `w`'s vote-duty read of the first interior slot along `W` can return. -/
theorem actionSGBlock_preceq_firstInteriorHead_of_genuine_after_GST_namedOn (facts : Record.Facts M)
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
    {v w : V} (hv : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (c + 1)))) (hAv : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick v (Restated.Vocabulary.Execution.Setup.a M S (c + 1))) → M.awake_for_grade2 S v (W j v) (c + 1))
    (hw : w ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc (c + 1)) + 1)))
    {C : Block V}
    (cv : M.Cache)
    (hcv : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (c + 1))) v).st.core.toHealing
      (Restated.Vocabulary.Execution.Setup.a M S (c + 1))
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (c + 1))) v).cache ⇢ cv)
    (hC : Restated.Vocabulary.Protocol.GenuineConfirmationWith M (M.gradeContract cv) S.E S.hc
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc (c + 1)))) v).st.core
        (M.confirmation_time S.E (M.opening_slot S.hc (c + 1))))
      ((M.opening_slot S.hc (c + 1))) C)
    {nv : M.N}
    (hnv : nv ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (c + 1))) v) (c + 1))
    {A2 : Option (Block V)}
    (hA2 : M.grade2_block_with (M.gradeContract nv.cache) S.E S.hc (M.toHealing nv.st.core)
      (M.round_of S.hc (M.toHealing nv.st.core).s) ⇢ A2)
    {G : Block V}
    (hG : M.get_sg_vote_with (M.gradeContract nv.cache) S.E S.hc (M.toHealing nv.st.core)
      (M.round_of S.hc (M.toHealing nv.st.core).s) A2 ⇢ G)
    (hBC : Block.Preceq G C)
    (hloPost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    (hloOpen : lo ≤ M.opening S.E S.hc (rGST + 2 - S.hc.η_SG))
    (ht₀ : t₀ ≤ (Restated.Vocabulary.Execution.Setup.a M S (rGST + 2)))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    ∀ cc : M.Cache,
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc (c + 1) + 1))) w).st.core.toHealing
        (M.vote_time S.E (M.opening_slot S.hc (c + 1) + 1))
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc (c + 1) + 1))) w).cache ⇢ cc →
      let n := M.mkNode
        (M.ns_setClock S.E
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc (c + 1) + 1))) w).st
          (M.vote_time S.E (M.opening_slot S.hc (c + 1) + 1)))
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc (c + 1) + 1))) w).record cc
      ∀ Tr : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ Tr →
      ∀ L : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
      ∀ L' : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
      ∀ H : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
          (M.toHealing n.st.core) Tr L L' (n.st.core.s - 1) ⇢ H →
        Block.Preceq G H := by
  intro cc hcc n Tr hTr L hL L' hL' H hH
  obtain ⟨hpostOpening, -, hvoteHor⟩ := Restated.firstInterior_schedule_l86e facts S hloPost hc hhor
  have hconfA : M.confirmation_time S.E (M.opening_slot S.hc (c + 1)) =
      Restated.Vocabulary.Execution.Setup.a M S (c + 1) :=
    Restated.Vocabulary.Proofs.HealingSurface.opening_confirmation_time_eq_action facts S (c + 1)
  have hsourceHor : M.confirmation_time S.E (M.opening_slot S.hc (c + 1)) ≤ rho.horizon := by
    rw [hconfA]; exact hhor
  have hspos : 0 < M.opening_slot S.hc (c + 1) :=
    (Nat.zero_le _).trans_lt (facts.gr.firstInterior_lt_nextOpening_l86e S c)
  have hinst := facts.sch.slot_instants_l55 S.E (M.opening_slot S.hc (c + 1))
  have hΔ := S.E.Δ_pos
  have hpostVote : lo ≤ M.vote_time S.E (M.opening_slot S.hc (c + 1)) :=
    hpostOpening.trans (facts.sch.proposal_time_lt_vote_time S.E _).le
  have hvConf : v ∈ Hs (M.confirmation_time S.E (M.opening_slot S.hc (c + 1))) := by
    rw [hconfA]; exact hv
  have hvSC : v ∈ Hs (M.support_cutoff S.E (M.opening_slot S.hc (c + 1))) := by
    refine hHs _ _ ?_ hvConf
    linarith [hinst.2.1, hinst.2.2.2.2.2]
  have hwFreeze : w ∈ Hs (M.view_freeze S.E (M.opening_slot S.hc (c + 1))) :=
    hHs _ _ (facts.sch.view_freeze_lt_vote_time_succ S.E _).le hw
  have hloFreeze : lo ≤ M.view_freeze S.E (M.opening_slot S.hc (c + 1)) := by
    linarith [hinst.2.2.1]
  have hcv' : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc (c + 1)))) v).st.core.toHealing
      (M.confirmation_time S.E (M.opening_slot S.hc (c + 1)))
      (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc (c + 1)))) v).cache ⇢ cv := by
    rw [hconfA]; exact hcv
  have hCg : Restated.Vocabulary.Protocol.GenuineConfirmation M (contract := M.gradeContract cv)
      S.E S.hc
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc (c + 1)))) v).st.core
        (M.confirmation_time S.E (M.opening_slot S.hc (c + 1))))
      (M.opening_slot S.hc (c + 1)) C :=
    ⟨hC.selected, hC.genuine⟩
  have hwinC1 : lo ≤ M.early S.E S.hc (c + 1) .g1 - S.E.Δ :=
    lo_le_early_g1₈₆e facts S hloPost (Nat.lt_succ_of_lt (rGST_lt_of_deadline_le₈₆e S hc))
  have hrunO : ∀ x ∈ S.E.committee (M.opening_slot S.hc (c + 1)),
      x ∈ Hs (M.confirmation_time S.E (M.opening_slot S.hc (c + 1))) →
      ∀ j : Nat, rho.events[j]? =
          some (Record.Event.tick x (M.vote_time S.E (M.opening_slot S.hc (c + 1)))) →
        M.awake_for_grade1 S x (W j x) (M.round_of S.hc (M.opening_slot S.hc (c + 1))) := by
    intro x _ hx j hj
    have hwin : lo ≤ M.early S.E S.hc (M.round_of S.hc (M.opening_slot S.hc (c + 1))) .g1 -
        S.E.Δ := by
      rw [facts.gr.round_of_opening_slot_eq S.hc (c + 1)]
      exact hwinC1
    exact hf.awake_g1 _ _ j _ (Or.inr rfl) hj
      (hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E _) hx) hwin
  have hrunW : ∀ j : Nat, rho.events[j]? =
      some (Record.Event.tick w (M.vote_time S.E (M.opening_slot S.hc (c + 1) + 1))) →
      M.awake_for_grade1 S w (W j w) (M.round_of S.hc (M.opening_slot S.hc (c + 1) + 1)) := by
    intro j hj
    have hwin : lo ≤ M.early S.E S.hc (M.round_of S.hc (M.opening_slot S.hc (c + 1) + 1)) .g1 -
        S.E.Δ := by
      rw [facts.gr.HealingLemmas_round_of_opening_succ S.hc (c + 1)]
      exact hwinC1
    exact hf.awake_g1 _ _ j _ (Or.inr rfl) hj hw hwin
  obtain ⟨u, hu, -, hCu⟩ :=
    Restated.genuineConfirmation_exists_honestVoteSupporter_after_gstOn facts S Hs Xb hf hHs
      hHsXb hcom hvSC hspos hpostVote hsourceHor cv hcv' hC hrunO
  have huVote : u ∈ Hs (M.vote_time S.E (M.opening_slot S.hc (c + 1))) :=
    hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E _) hu
  obtain ⟨cu0, hcu0⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
    (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc (c + 1)))) u).st.core.toHealing
    (M.vote_time S.E (M.opening_slot S.hc (c + 1)))
    (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc (c + 1)))) u).cache
  let nu : M.N := M.mkNode
    (M.ns_setClock S.E
      (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc (c + 1)))) u).st
      (M.vote_time S.E (M.opening_slot S.hc (c + 1))))
    (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc (c + 1)))) u).record cu0
  obtain ⟨Tr0, hTr0⟩ := facts.fc.voter_filtered_block_tree_nonempty S.E nu.st.core nu.st.core.s
  obtain ⟨L0, hL0⟩ := facts.fc.voter_view_nonempty S.E
    (M.toHealing nu.st.core).toFG.toSG.toGoldfishStore nu.st.core.s
  obtain ⟨L0', hL0'⟩ := facts.fc.voter_support_view_nonempty S.E
    (M.toHealing nu.st.core).toFG.toSG.toGoldfishStore nu.st.core.s
  obtain ⟨H0, hH0⟩ := facts.fc.get_head_in_tree_with_layer_nonempty (M.gradeContract nu.cache)
    S.E S.hc (M.toHealing nu.st.core) Tr0 L0 L0' (nu.st.core.s - 1)
  have hBprev : Block.Preceq G H0 :=
    preceq_trans_Preceq hBC (hCu cu0 hcu0 Tr0 hTr0 L0 hL0 L0' hL0' H0 hH0)
  obtain ⟨g, hg⟩ := facts.gr.read_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc n.st.core.s)
  have hA0 : Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n
      (M.round_of S.hc n.st.core.s) ⇢ g.anchor :=
    (p60% returns_map_intro₆₀) (fun x : Protocol.GradeRead V => x.anchor) _ g hg
  have hnmem : n ∈ Restated.Vocabulary.Internal.NamedRecoveryRead.voteDutyRead M S rho w
      (M.opening_slot S.hc (c + 1) + 1) :=
    ⟨W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc (c + 1) + 1))),
      (p64b% mem_stateBeforeTime_along₆₄b) hf.sorted hf.onePath _, cc, hcc, rfl⟩
  have hanchorCompat : Block.compatible g.anchor G = true :=
    Restated.voterAnchorAt_firstInterior_compatible_actionSGBlock_after_GSTOn facts S Hs Xb hf
      hHs hHsXb hcom hbelow hrec hdelay hpost hc hhor (le_refl _)
      (facts.gr.firstInterior_lt_nextOpening_l86e S (c + 1)) hvoteHor
      (Restated.Vocabulary.Proofs.HealingSurface.firstInterior_vote_add_delta_le_horizon facts S hhor)
      hv hAv hw hloPost hloOpen ht₀ hA cc hcc g.anchor hA0 nv hnv A2 hA2 G hG
  have hheadA : Block.Preceq g.anchor H :=
    Restated.Vocabulary.Proofs.HealingSurface.voterAnchorAt_preceq_voterHeadAt facts S rho w _ n hnmem
      g.anchor hA0 Tr hTr L hL L' hL' H hH
  have hheadR : Block.Preceq (M.get_fg_root (M.toHealing n.st.core).toFG) H :=
    Restated.Vocabulary.Proofs.HealingSurface.fgRoot_preceq_voterHeadAt facts S rho w _ n hnmem
      Tr hTr L hL L' hL' H hH
  rcases compatible_cases hanchorCompat with hanchorB | hBanchor
  · have hnst : n.st = M.store_with_cache _ _ := facts.nd.mkNode_st _ _ _
    have hs : ∀ x : M.S, (M.toHealing x).s = x.s := fun x => facts.sto.toHealing_gs_s x
    have hrootB : Block.Preceq (M.get_fg_root (M.toHealing n.st.core).toFG) G :=
      preceq_trans_Preceq
        (Restated.Vocabulary.Proofs.w4_fgRoot_preceq_nodeAnchor facts S n _ g.anchor hA0) hanchorB
    have hrootBare : Block.Preceq
        (M.get_fg_root (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc (c + 1) + 1))) w).st.core
          (M.opening_slot S.hc (c + 1) + 1))).toFG) G := by
      have h := hrootB
      rw [hnst, facts.nd.store_with_cache_get_fg_root, ← (p60% voteStore_eq₆₀s) facts S] at h
      exact h
    have hCprocessed := Restated.voterProcessedTarget_of_genuineConfirmation_after_gstOn facts S Hs
      Xb hf hHs hHsXb hvSC hwFreeze hpostOpening hsourceHor hCg
      (preceq_trans_Preceq hrootBare hBC)
    have hslotH : (M.toHealing n.st.core).s = M.opening_slot S.hc (c + 1) + 1 := by
      show (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.s = _
      rw [facts.sto.toHealing_gs_s, hnst, facts.nd.store_with_cache_core_s, facts.hd.Sts_setClock_core_s,
        facts.sch.slotOf_vote_time]
    obtain ⟨P, hP⟩ := facts.fc.voter_processed_block_tree_nonempty S.E
      (M.toHealing n.st.core).toFG.toSG.toGoldfishStore (M.toHealing n.st.core).s
    have hP' : M.voter_processed_block_tree S.E
        (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc (c + 1) + 1))) w).st.core
          (M.opening_slot S.hc (c + 1) + 1))).toFG.toSG.toGoldfishStore
        (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc (c + 1) + 1))) w).st.core
          (M.opening_slot S.hc (c + 1) + 1))).s ⇢ P := by
      have h := hP
      rw [hs, hnst, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_voter_processed_block_tree,
        ← (p60% voteStore_eq₆₀s) facts S] at h
      rw [hs]
      exact h
    have hCP : C ∈ P := hCprocessed P hP'
    have hGP : G ∈ P := Restated.ancestorProcessed_of_voterProcessedOn facts S Hs Xb hf
      hwFreeze P hP' hCP hloFreeze G hBC
    have hP1 : M.voter_processed_block_tree S.E
        (M.toHealing n.st.core).toFG.toSG.toGoldfishStore (M.opening_slot S.hc (c + 1) + 1) ⇢ P := by
      rw [hslotH] at hP; exact hP
    have hsDead : M.opening_slot S.hc (fgSafetyProgressDeadline S rho rGST gap delayExtra) + 1 ≤
        M.opening_slot S.hc (c + 1) :=
      (Nat.add_le_add_right (facts.gr.opening_slot_le_of_le S.hc hc) 1).trans
        (facts.gr.firstInterior_lt_nextOpening_l86e S c).le
    rcases Restated.honestPreviousHead_voterCandidateMem_or_preceq_root_after_GST_namedOn facts S Hs
        Xb hf hHs hHsXb hcom hbelow hrec hdelay hpost hsDead hvoteHor hw huVote hcu0 hTr0 hL0
        hL0' hH0 hBprev hcc hP1 hGP hloPost hloOpen ht₀ hA Tr hTr with hcandidate | hBroot
    · have hK : Restated.Vocabulary.Proofs.Optimistic.voter_candidate_tree M S.E
          (M.toHealing n.st.core) ⇢
            M.get_filtered_block_tree_from (M.toHealing n.st.core).toFG P := by
        unfold Restated.Vocabulary.Proofs.Optimistic.voter_candidate_tree
        exact ((p60% returns_bind_iff₆₀s) _ _ _).2 ⟨P, hP, (Record.returns_pure _ _).2 rfl⟩
      have hGK : G ∈ M.get_filtered_block_tree_from (M.toHealing n.st.core).toFG P := by
        rw [facts.fc.voter_candidate_tree_eq_protocol_voter_filtered_block_tree S.E n.st.core P
          hP Tr hTr]
        exact hcandidate
      have hTr' := hTr
      rw [hnst, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_voter_filtered_block_tree,
        ← (p60% voteStore_eq₆₀s) facts S] at hTr'
      replace hK : Restated.Vocabulary.Proofs.Optimistic.voter_candidate_tree M S.E (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc (c + 1) + 1))) w).st.core
          (M.opening_slot S.hc (c + 1) + 1))) ⇢
          M.get_filtered_block_tree_from (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc (c + 1) + 1))) w).st.core
          (M.opening_slot S.hc (c + 1) + 1))).toFG P := by
        unfold Restated.Vocabulary.Proofs.Optimistic.voter_candidate_tree
        exact ((p60% returns_bind_iff₆₀s) _ _ _).2 ⟨P, hP', (Record.returns_pure _ _).2 rfl⟩
      replace hGK : G ∈ M.get_filtered_block_tree_from (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc (c + 1) + 1))) w).st.core
          (M.opening_slot S.hc (c + 1) + 1))).toFG P := by
        rw [facts.fc.voter_candidate_tree_eq_protocol_voter_filtered_block_tree S.E _ P hP' Tr hTr']
        exact hcandidate
      rcases Restated.nextVoteAdoption_of_recovery_after_gst_compatibleOn facts S Hs Xb hf hHs
          hHsXb hvConf hw hpostOpening hsourceHor cc hcc hrootBare hA0
          (compatible_of_cases (Or.inl hanchorB)) hK hGK hrunW with hBanchor | hadopt
      · exact preceq_trans_Preceq hBanchor hheadA
      · obtain ⟨votes, hvotes, helig⟩ := (p59% ancestor_eligible₅₉) facts hBC hCg
        exact Restated.preceq_voterHeadAt_of_namedNextVoteAdoptionOn facts S Xb n hnmem hvotes
          helig hadopt Tr hTr L hL L' hL' H hH
    · exact preceq_trans_Preceq hBroot hheadR
  · exact preceq_trans_Preceq hBanchor hheadA

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

/-- After the progress deadline, every SG block that `v`'s round-`(c + 1)` action read along `W` can
    select is an ancestor of every head that `w`'s vote-duty read of the round's first interior slot
    along `W` can return. -/
theorem actionSGBlock_preceq_firstInteriorHead_after_GST_namedOn (facts : Record.Facts M)
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
    {v w : V} (hv : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (c + 1)))) (hAv : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick v (Restated.Vocabulary.Execution.Setup.a M S (c + 1))) → M.awake_for_grade2 S v (W j v) (c + 1))
    (hw : w ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc (c + 1)) + 1)))
    (hloPost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    (hloOpen : lo ≤ M.opening S.E S.hc (rGST + 2 - S.hc.η_SG))
    (ht₀ : t₀ ≤ (Restated.Vocabulary.Execution.Setup.a M S (rGST + 2)))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    ∀ cc : M.Cache,
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc (c + 1) + 1))) w).st.core.toHealing
        (M.vote_time S.E (M.opening_slot S.hc (c + 1) + 1))
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc (c + 1) + 1))) w).cache ⇢ cc →
      let n := M.mkNode
        (M.ns_setClock S.E
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc (c + 1) + 1))) w).st
          (M.vote_time S.E (M.opening_slot S.hc (c + 1) + 1)))
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc (c + 1) + 1))) w).record cc
      ∀ Tr : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ Tr →
      ∀ L : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
      ∀ L' : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
      ∀ H : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
          (M.toHealing n.st.core) Tr L L' (n.st.core.s - 1) ⇢ H →
      ∀ nv ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (c + 1))) v) (c + 1),
      ∀ A2 : Option (Block V),
        M.grade2_block_with (M.gradeContract nv.cache) S.E S.hc (M.toHealing nv.st.core)
          (M.round_of S.hc (M.toHealing nv.st.core).s) ⇢ A2 →
      ∀ G : Block V,
        M.get_sg_vote_with (M.gradeContract nv.cache) S.E S.hc (M.toHealing nv.st.core)
          (M.round_of S.hc (M.toHealing nv.st.core).s) A2 ⇢ G →
        Block.Preceq G H := by
  intro cc hcc n Tr hTr L hL L' hL' H hH nv hnv A2 hA2 G hG
  obtain ⟨-, -, hvoteHor⟩ := Restated.firstInterior_schedule_l86e facts S hloPost hc hhor
  have hround : (M.round_of S.hc (M.opening_slot S.hc (c + 1) + 1)) = c + 1 :=
    facts.gr.round_of_eq_of_opening_succ_le_of_lt_next_opening S.hc (le_refl _)
      (facts.gr.firstInterior_lt_nextOpening_l86e S (c + 1))
  have hnextFrame : M.vote_time S.E (M.opening_slot S.hc (c + 1) + 1) ≤
      M.opening S.E S.hc (c + 1 + 1) := by
    rw [facts.gr.opening_eq_proposal_time]
    exact (facts.sch.voteTime_lt_nextProposal_l86d S.E _).le.trans
      (facts.sch.proposal_time_mono S.E
        (Nat.succ_le_of_lt (facts.gr.firstInterior_lt_nextOpening_l86e S (c + 1))))
  have hnext : M.vote_time S.E (M.opening_slot S.hc (c + 1) + 1) ≤
      (Restated.Vocabulary.Execution.Setup.a M S (c + 1 + 1)) :=
    (Restated.Vocabulary.Protocol.next_vote_time_lt_action facts S (c + 1)).le.trans
      ((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone (Nat.le_succ _))
  obtain ⟨hloc, hloEarly, -, -, ready⟩ :=
    Restated.roundBounds_after_deadline_l86d facts S hpost hloOpen hc hhor
  have hslotDead : (M.opening_slot S.hc (fgSafetyProgressDeadline S rho rGST gap delayExtra)) + 1 ≤
      M.opening_slot S.hc (c + 1) + 1 :=
    Nat.add_le_add_right (facts.gr.opening_slot_le_of_le S.hc (hc.trans (Nat.le_succ c))) 1
  have hshor : M.vote_time S.E (M.opening_slot S.hc (c + 1) + 1) + S.E.Δ ≤ rho.horizon :=
    Restated.Vocabulary.Proofs.HealingSurface.firstInterior_vote_add_delta_le_horizon facts S hhor
  have hnmem : n ∈ Restated.Vocabulary.Internal.NamedRecoveryRead.voteDutyRead M S rho w
      (M.opening_slot S.hc (c + 1) + 1) :=
    ⟨W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc (c + 1) + 1))),
      (p64b% mem_stateBeforeTime_along₆₄b) hf.sorted hf.onePath _, cc, hcc, rfl⟩
  have hheadR : Block.Preceq (M.get_fg_root (M.toHealing n.st.core).toFG) H :=
    Restated.Vocabulary.Proofs.HealingSurface.fgRoot_preceq_voterHeadAt facts S rho w _ n hnmem
      Tr hTr L hL L' hL' H hH
  have hrootHead : Block.Preceq
      (M.get_fg_root (M.toHealing
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (c + 1))) v).st.core).toFG)
      H :=
    Restated.fgRoot_preceq_previousHead_after_GSTOn facts S Hs Xb hf hHs hHsXb hcom hbelow
      hrec hdelay hpost
      ((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone
        (hc.trans (Nat.le_succ c))) hhor hslotDead
      (Restated.Vocabulary.Protocol.action_lt_vote_time_two_after facts S (c + 1)).le hshor hv
      hloPost hloOpen ht₀ hA w hw cc hcc Tr hTr L hL L' hL' H hH
  have hraw := Restated.nodeRawG2_at_action_after_recovery_deadlineOn facts S Hs Xb hf hHs
    hHsXb hcom hbelow hrec hdelay hpost hc hhor hloPost hloOpen ht₀ hA v
    (hHs _ _ (facts.gr.domain_le_a S (c + 1) .g2) hv) nv hnv
  obtain ⟨g, hg⟩ : ∃ g, Restated.Vocabulary.Internal.PhaseGrades.nodeRead M S nv (c + 1) ⇢ g :=
    facts.gr.read_nonempty _ _ _ _ _
  have hmemA := (p64b% mem_stateBeforeTime_along₆₄b) hf.sorted hf.onePath
    (Restated.Vocabulary.Execution.Setup.a M S (c + 1))
  have hnvMem : nv ∈ Restated.Vocabulary.Proofs.HealingSurface.actionReadAt M S rho v (c + 1) :=
    ⟨W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (c + 1))), hmemA, hnv⟩
  have hnvRoot : M.get_fg_root (M.toHealing nv.st.core).toFG =
      M.get_fg_root (M.toHealing
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (c + 1))) v).st.core).toFG :=
    (p60% actionReadFrom_fgRoot₆₀s) facts S _ _ nv hnv
  rcases Restated.Vocabulary.Proofs.HealingSurface.actionSGBlockAt_tiers_of_rawG2 facts S rho v
      (c + 1) nv hnvMem g hg (hraw g hg) A2 hA2 G hG with hclear | ⟨Q, hQ, hsg⟩ | hsg
  · rcases Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt_liveConfirmed_genuine_or_fgRoot
        facts S rho v (c + 1) _ hmemA nv hnv with ⟨C, hC, hClive⟩ | ⟨R, hRroot, hRlive⟩
    · have hconfA : M.confirmation_time S.E (M.opening_slot S.hc (c + 1)) =
          Restated.Vocabulary.Execution.Setup.a M S (c + 1) :=
        Restated.Vocabulary.Proofs.HealingSurface.opening_confirmation_time_eq_action facts S (c + 1)
      have hnv' := hnv
      obtain ⟨cv, hcv, stv, -, hnveq⟩ := hnv'
      have hcache : nv.cache = cv := by rw [hnveq]; exact facts.nd.mkNode_cache _ _ _
      rw [hcache] at hC
      have hC' : Restated.Vocabulary.Protocol.GenuineConfirmationWith M (M.gradeContract cv) S.E S.hc
          (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
            (W (strictEventIndex rho
              (M.confirmation_time S.E (M.opening_slot S.hc (c + 1)))) v).st.core
            (M.confirmation_time S.E (M.opening_slot S.hc (c + 1))))
          (M.opening_slot S.hc (c + 1)) C := by
        have hW : W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc (c + 1)))) =
            W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (c + 1))) := by
          rw [hconfA]
        rw [hW]; exact hC
      exact Restated.actionSGBlock_preceq_firstInteriorHead_of_genuine_after_GST_namedOn facts S Hs
        Xb hf hHs hHsXb hcom hbelow hrec hdelay hpost hc hhor hv hAv hw cv hcv hC'
        hnv hA2 hG (by rw [hClive]; exact hclear.2.1)
        hloPost hloOpen ht₀ hA cc hcc Tr hTr L hL L' hL' H hH
    · have hBroot : Block.Preceq G
          (M.get_fg_root (M.toHealing
            (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (c + 1))) v).st.core).toFG) := by
        rw [← hnvRoot,
          Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt_fgRoot_eq_openingConfStore facts S
            rho v (c + 1) _ hmemA nv hnv, ← hRroot, hRlive]
        exact hclear.2.1
      exact preceq_trans_Preceq hBroot hrootHead
  · subst hsg
    have hq : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S nv (c + 1) ⇢ g.Q2 :=
      (p60% returns_map_intro₆₀) (fun x : Protocol.GradeRead V => x.Q2)
        (Restated.Vocabulary.Internal.PhaseGrades.nodeRead M S nv (c + 1)) g hg
    rw [hQ] at hq
    rcases Restated.actionQ2_preceq_fgRoot_or_activeAtVoteDuty_after_deadlineOn facts S Hs Xb hf
        hHs hHsXb hcom hbelow hrec hdelay hpost (Nat.succ_le_succ hc) ready hhor hv hAv hnv
        hq hround hvoteHor hnext hw hloPost hloOpen ht₀ hA cc hcc with hQroot | hQactive
    · exact preceq_trans_Preceq hQroot hheadR
    · have hcut : Restated.Vocabulary.Protocol.HealConfig.Γ_0 M S.hc S.E.Δ (c + 1) ≤
          M.vote_time S.E (M.opening_slot S.hc (c + 1) + 1) :=
        Restated.Vocabulary.Proofs.HealingSurface.Γ_0_le_vote_time_of_round_eq facts S hround
      have hdomG1 : M.domain S.E S.hc (c + 1) .g1 =
          Restated.Vocabulary.Protocol.HealConfig.Γ_0 M S.hc S.E.Δ (c + 1) := by
        rw [facts.gr.Sts_domain_g1_eq_opening, facts.gr.opening_eq_proposal_time]
        exact (facts.sch.Γ_0_eq_proposal_time S.hc S.E (c + 1)).symm
      have hwG1 : w ∈ Hs (M.domain S.E S.hc (c + 1) .g1) := hHs _ _ (hdomG1.trans_le hcut) hw
      have hQactive' : G ∈ M.get_filtered_block_tree (M.toHealing
          (M.ns_setClock S.E
            (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc (c + 1) + 1))) w).st
            (M.vote_time S.E (M.opening_slot S.hc (c + 1) + 1))).core).toFG := by
        have h := hQactive
        unfold Restated.Vocabulary.Internal.PhaseGrades.filteredTree at h
        rewrite [facts.nd.mkNode_st] at h; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at h
        exact h
      exact Restated.preceq_voterHeadAt_of_nodeQ2_activeAtDutyReadOn facts S Hs Xb hf hHs hHsXb
        hf.slashableBound (Nat.succ_pos c) (Nat.le_succ _) hround hnextFrame hvoteHor
        hloEarly ((facts.gr.domain_le_a S (c + 1) .g0).trans hhor)
        (hHs _ _ (facts.gr.domain_le_a S (c + 1) .g2) hv) hwG1 nv hnv hq hQactive' hloc
        cc hcc Tr hTr L hL L' hL' H hH
  · rw [hsg, hnvRoot]
    exact hrootHead

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

/-- If every head picked from slot `s`'s committee is genesis or admitted by `w` before
    `support_cutoff s`, `X` is such a head and `B ⪯ X`, then `B` is in every outcome of the
    processed tree at slot `s + 1` of every node state that `w`'s vote-duty read of slot `s + 1`
    along `W` can give. -/
theorem voterProcessed_of_availableBefore_of_honestHeadOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {s : Slot} {B X : Block V} {w : V}
    (havailable : Restated.HonestHeadsAvailableBeforeOn M S rho W Hs Xb s w (M.support_cutoff S.E s))
    (hhead : Restated.HonestHeadOn M S rho W Hs Xb s X)
    (hBX : Block.Preceq B X) :
    ∀ cu : M.Cache,
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
        (M.vote_time S.E (s + 1))
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ cu →
      ∀ P : Finset (Block V),
        M.voter_processed_block_tree S.E
          (M.toHealing (M.mkNode
            (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
              (M.vote_time S.E (s + 1)))
            (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record
            cu).st.core).toFG.toSG.toGoldfishStore (s + 1) ⇢ P →
        B ∈ P := by
  intro cu _hcu P hP
  rcases havailable X hhead with hXgen | hXadmit
  · have hBgen : B = Block.genesis :=
      Block.preceq_antisymm (preceq_eq_true_iff_Preceq.mpr (hXgen ▸ hBX))
        (Protocol.preceq_genesis B)
    subst B
    have hgenesis := Restated.genesis_mem_and_stamp_storeBeforeTimeOn facts S Hs Xb hf w
      (M.vote_time S.E (s + 1)) (M.view_freeze S.E s)
    refine facts.fc.mem_voter_processed_block_tree_of_stamped _ _ _ ?_ ?_ P hP
    · rewrite [facts.sto.toHealing_gs_T, facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.hd.Sts_setClock_core_T]
      exact hgenesis.1
    · rewrite [facts.sto.toHealing_gs_timestamp_block, facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.hd.setClock_core_timestamp_block, Nat.add_sub_cancel]
      exact hgenesis.2
  · have hvisibleB := Restated.admittedBefore_ancestor_mem_and_stamp_atOn facts S Hs Xb hf hXadmit hBX
      (le_trans (le_of_lt (facts.sch.Optimistic_support_cutoff_lt_view_freeze S.E s))
        (le_of_lt (facts.sch.view_freeze_lt_vote_time_succ S.E s)))
    have hBstampFreeze :
        stampedBefore
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.timestamp_block
          (M.view_freeze S.E s) B = true := by
      have hBstampCut := hvisibleB.2
      rw [stampedBefore_eq_occurrenceBefore] at hBstampCut ⊢
      exact occurrenceBefore_mono
        (le_of_lt (facts.sch.Optimistic_support_cutoff_lt_view_freeze S.E s)) hBstampCut
    refine facts.fc.mem_voter_processed_block_tree_of_stamped _ _ _ ?_ ?_ P hP
    · rewrite [facts.sto.toHealing_gs_T, facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.hd.Sts_setClock_core_T]
      exact hvisibleB.1
    · rewrite [facts.sto.toHealing_gs_timestamp_block, facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.hd.setClock_core_timestamp_block, Nat.add_sub_cancel]
      exact hBstampFreeze

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

/-- If `lo ≤ S.a rGST` and `s` is after the progress deadline's opening slot, then
    `lo ≤ vote_time s`. -/
theorem lo_le_vote_after_deadline_l86e (facts : Record.Facts M)
    {delayExtra : Nat}
    (S : Setup V) {rho : Record.Run V} {lo : Int} {rGST gap : Round}
    (hloPost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    {s : Slot}
    (hs : (M.opening_slot S.hc (fgSafetyProgressDeadline S rho rGST gap delayExtra)) + 1 ≤ s) :
    lo ≤ M.vote_time S.E s := by
  have hround : rGST + 1 ≤ fgSafetyProgressDeadline S rho rGST gap delayExtra := by
    unfold fgSafetyProgressDeadline
    exact Nat.le_add_right _ _
  have hslot : (M.opening_slot S.hc (rGST + 1)) ≤ s :=
    (facts.gr.opening_slot_le_of_le S.hc hround).trans ((Nat.le_succ _).trans hs)
  have hcutVote : Restated.Vocabulary.Protocol.HealConfig.Γ_0 M S.hc S.E.Δ (rGST + 1) ≤
      M.vote_time S.E ((M.opening_slot S.hc (rGST + 1))) := by
    have h2 := facts.sch.Γ_1_eq_vote_time S.hc S.E (rGST + 1)
    have hΔ := S.E.Δ_pos
    unfold Restated.Vocabulary.Protocol.HealConfig.Γ_0
    linarith
  exact ((hloPost.trans (a_le_Γ_neg1_succ₈₆e facts S rGST)).trans
    (Restated.Vocabulary.Proofs.HealingLemmas.Γ_neg1_lt_Γ_0 facts S.hc S.E.Δ_pos (rGST + 1)).le).trans
    (hcutVote.trans (facts.sch.vote_time_mono_slots S.E hslot))

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

/-- The slot step after the progress deadline: if `B` is an ancestor of every head at slot `s` of
    every member of the set for `vote_time s`, and on one chain with every anchor at `s + 1` of
    every member of the set for `vote_time (s + 1)`, then `B` is an ancestor of every head at
    `s + 1` of those members, all read along `W`. -/
theorem allHonestHeads_succ_of_voterAnchorCompatible_after_GST_namedOn (facts : Record.Facts M)
    {delayExtra : Nat}
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hbelow : BelowOneThirdOn S rho Hs)
    {rGST gap : Round} {t₀ : Int} (hrec : Restated.MultiProposerRecurrenceOn M S Hs gap t₀ rho.horizon)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    {s : Slot}
    (hs : (M.opening_slot S.hc (fgSafetyProgressDeadline S rho rGST gap delayExtra)) + 1 ≤ s)
    (hhor : M.vote_time S.E (s + 1) ≤ rho.horizon)
    {B : Block V}
    (hheads : ∀ w ∈ Hs (M.vote_time S.E s), ∀ cc : M.Cache,
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E s)) w).st.core.toHealing
        (M.vote_time S.E s)
        (W (strictEventIndex rho (M.vote_time S.E s)) w).cache ⇢ cc →
      let n := M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) w).st (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) w).record cc
      ∀ Tr : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ Tr →
      ∀ L : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
      ∀ L' : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
      ∀ H : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
          (M.toHealing n.st.core) Tr L L' (n.st.core.s - 1) ⇢ H →
        Block.Preceq B H)
    (hanchors : ∀ w ∈ Hs (M.vote_time S.E (s + 1)), ∀ cc : M.Cache,
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
        (M.vote_time S.E (s + 1))
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ cc →
      let n := M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
          (M.vote_time S.E (s + 1)))
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record cc
      ∀ A0 : Block V,
        Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n (M.round_of S.hc n.st.core.s) ⇢ A0 →
        Block.compatible A0 B = true)
    (hloPost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    (hloOpen : lo ≤ M.opening S.E S.hc (rGST + 2 - S.hc.η_SG))
    (ht₀ : t₀ ≤ (Restated.Vocabulary.Execution.Setup.a M S (rGST + 2)))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    ∀ w ∈ Hs (M.vote_time S.E (s + 1)), ∀ cc : M.Cache,
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
        (M.vote_time S.E (s + 1))
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ cc →
      let n := M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
          (M.vote_time S.E (s + 1)))
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record cc
      ∀ Tr : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ Tr →
      ∀ L : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
      ∀ L' : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
      ∀ H : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
          (M.toHealing n.st.core) Tr L L' (n.st.core.s - 1) ⇢ H →
        Block.Preceq B H := by
  intro w hw cc hcc n Tr hTr L hL L' hL' H hH
  have hsPos : 0 < s := (Nat.zero_lt_succ _).trans_le hs
  have hprevHor : M.vote_time S.E s ≤ rho.horizon :=
    (facts.sch.vote_time_mono_slots S.E (Nat.le_succ s)).trans hhor
  have hpostVote : lo ≤ M.vote_time S.E s := Restated.lo_le_vote_after_deadline_l86e facts S hloPost hs
  have hwinS : lo ≤ M.early S.E S.hc (M.round_of S.hc s) .g1 - S.E.Δ := by
    have hdr : fgSafetyProgressDeadline S rho rGST gap delayExtra ≤ M.round_of S.hc s := by
      have h := facts.gr.round_of_mono S.hc ((Nat.le_succ _).trans hs)
      rwa [facts.gr.round_of_opening_slot_eq] at h
    exact lo_le_early_g1₈₆e facts S hloPost (rGST_lt_of_deadline_le₈₆e S hdr)
  have hnames : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s (fun X => Block.Preceq B X) := by
    intro x hx hcommittee
    obtain ⟨c0, hc0⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
      (W (strictEventIndex rho (M.vote_time S.E s)) x).st.core.toHealing (M.vote_time S.E s)
      (W (strictEventIndex rho (M.vote_time S.E s)) x).cache
    have hem := Restated.named_voter_head_emitsOn facts S Hs Xb hf hHsXb hx hsPos hcommittee
      hprevHor hpostVote c0 hc0
      (fun j hj => hf.awake_g1 _ _ j _ (Or.inr rfl) hj hx hwinS)
    have hhd := hheads x hx c0 hc0
    let nx : M.N := M.mkNode
      (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) x).st (M.vote_time S.E s))
      (W (strictEventIndex rho (M.vote_time S.E s)) x).record c0
    obtain ⟨T0, hT0⟩ := facts.fc.voter_filtered_block_tree_nonempty S.E nx.st.core nx.st.core.s
    obtain ⟨L0, hL0⟩ := facts.fc.voter_view_nonempty S.E
      (M.toHealing nx.st.core).toFG.toSG.toGoldfishStore nx.st.core.s
    obtain ⟨L0', hL0'⟩ := facts.fc.voter_support_view_nonempty S.E
      (M.toHealing nx.st.core).toFG.toSG.toGoldfishStore nx.st.core.s
    obtain ⟨Hd, hHd⟩ := facts.fc.get_head_in_tree_with_layer_nonempty (M.gradeContract nx.cache)
      S.E S.hc (M.toHealing nx.st.core) T0 L0 L0' (nx.st.core.s - 1)
    obtain ⟨Y, hYhead, hYrun, hYemit⟩ := hem T0 hT0 L0 hL0 L0' hL0' Hd hHd
    exact ⟨Y, by rw [hYhead]; exact hhd T0 hT0 L0 hL0 L0' hL0' Hd hHd, hYrun, hYemit⟩
  have hcutHor : M.support_cutoff S.E s ≤ rho.horizon :=
    (facts.sch.support_cutoff_le_vote_time_succ S.E s).trans hhor
  have hwSC : w ∈ Hs (M.support_cutoff S.E s) :=
    hHs _ _ (facts.sch.support_cutoff_le_vote_time_succ S.E s) hw
  have hwPrev : w ∈ Hs (M.vote_time S.E s) :=
    hHs _ _ (facts.sch.vote_time_mono_slots S.E (Nat.le_succ s)) hw
  have hnst : n.st = M.store_with_cache (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st (M.vote_time S.E (s + 1))) _ := facts.nd.mkNode_st _ _ _
  have hnmem : n ∈ Restated.Vocabulary.Internal.NamedRecoveryRead.voteDutyRead M S rho w (s + 1) :=
    ⟨W (strictEventIndex rho (M.vote_time S.E (s + 1))),
      (p64b% mem_stateBeforeTime_along₆₄b) hf.sorted hf.onePath _, cc, hcc, rfl⟩
  obtain ⟨g, hg⟩ := facts.gr.read_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc n.st.core.s)
  have hA0 : Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n
      (M.round_of S.hc n.st.core.s) ⇢ g.anchor :=
    (p60% returns_map_intro₆₀) (fun x : Protocol.GradeRead V => x.anchor) _ g hg
  have hheadA : Block.Preceq g.anchor H :=
    Restated.Vocabulary.Proofs.HealingSurface.voterAnchorAt_preceq_voterHeadAt facts S rho w _ n hnmem
      g.anchor hA0 Tr hTr L hL L' hL' H hH
  have hheadR : Block.Preceq (M.get_fg_root (M.toHealing n.st.core).toFG) H :=
    Restated.Vocabulary.Proofs.HealingSurface.fgRoot_preceq_voterHeadAt facts S rho w _ n hnmem
      Tr hTr L hL L' hL' H hH
  rcases compatible_cases (hanchors w hw cc hcc g.anchor hA0) with hanchorB | hBanchor
  · by_cases hBroot : Block.Preceq B (M.get_fg_root (M.toHealing n.st.core).toFG)
    · exact preceq_trans_Preceq hBroot hheadR
    have hrootB : Block.Preceq (M.get_fg_root (M.toHealing n.st.core).toFG) B :=
      preceq_trans_Preceq
        (Restated.Vocabulary.Proofs.w4_fgRoot_preceq_nodeAnchor facts S n _ g.anchor hA0) hanchorB
    have havailable := Restated.honestHeadsAvailableBefore_of_namedPostHealingConeOn facts S Hs Xb
      hf hHs hHsXb hwSC hpostVote hcutHor (by have h := hrootB; rw [hnst] at h; (try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at h); exact h) hnames
    have hpositive : 0 < ((S.E.committee s) ∩ Hs (M.confirmation_time S.E s)).card := by
      have hmajority := hcom s
      omega
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hpositive
    have hxCommittee : x ∈ S.E.committee s := (Finset.mem_inter.mp hx).1
    have hxConf : x ∈ Hs (M.confirmation_time S.E s) := (Finset.mem_inter.mp hx).2
    have hxVote : x ∈ Hs (M.vote_time S.E s) :=
      hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E s) hxConf
    obtain ⟨X, hBX, hXrun, hXemit⟩ := hnames x hxVote hxCommittee
    have hXhead : Restated.HonestHeadOn M S rho W Hs Xb s X.erase :=
      ⟨x, hxConf, hxCommittee, ⟨X, rfl, hXrun⟩, hXemit⟩
    obtain ⟨P, hP⟩ := facts.fc.voter_processed_block_tree_nonempty S.E
      (M.toHealing n.st.core).toFG.toSG.toGoldfishStore (s + 1)
    have hprocessed : ∀ {D : Block V}, Block.Preceq D B → D ∈ P := fun {D} hDB =>
      Restated.voterProcessed_of_availableBefore_of_honestHeadOn facts S Hs Xb hf havailable hXhead
        (preceq_trans_Preceq hDB hBX) cc hcc P hP
    obtain ⟨cw0, hcw0⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
      (W (strictEventIndex rho (M.vote_time S.E s)) w).st.core.toHealing (M.vote_time S.E s)
      (W (strictEventIndex rho (M.vote_time S.E s)) w).cache
    let nw : M.N := M.mkNode
      (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) w).st (M.vote_time S.E s))
      (W (strictEventIndex rho (M.vote_time S.E s)) w).record cw0
    obtain ⟨Tw0, hTw0⟩ := facts.fc.voter_filtered_block_tree_nonempty S.E nw.st.core nw.st.core.s
    obtain ⟨Lw0, hLw0⟩ := facts.fc.voter_view_nonempty S.E
      (M.toHealing nw.st.core).toFG.toSG.toGoldfishStore nw.st.core.s
    obtain ⟨Lw0', hLw0'⟩ := facts.fc.voter_support_view_nonempty S.E
      (M.toHealing nw.st.core).toFG.toSG.toGoldfishStore nw.st.core.s
    obtain ⟨Hw0, hHw0⟩ := facts.fc.get_head_in_tree_with_layer_nonempty (M.gradeContract nw.cache)
      S.E S.hc (M.toHealing nw.st.core) Tw0 Lw0 Lw0' (nw.st.core.s - 1)
    have hBHw : Block.Preceq B Hw0 :=
      hheads w hwPrev cw0 hcw0 Tw0 hTw0 Lw0 hLw0 Lw0' hLw0' Hw0 hHw0
    have hcand : ∀ {D : Block V}, Block.Preceq D B →
        ∀ Tu : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ Tu →
          D ∈ Tu ∨ Block.Preceq D (M.get_fg_root (M.toHealing n.st.core).toFG) := fun {D} hDB =>
      Restated.honestPreviousHead_voterCandidateMem_or_preceq_root_after_GST_namedOn facts S Hs Xb
        hf hHs hHsXb hcom hbelow hrec hdelay hpost hs hhor hw hwPrev hcw0 hTw0 hLw0 hLw0'
        hHw0 (preceq_trans_Preceq hDB hBHw) hcc hP (hprocessed hDB) hloPost hloOpen ht₀ hA
    refine Restated.fixedRoot_goldfishConeStepOn facts S Hs Xb hf hHs hHsXb hcom hsPos
      hpostVote hhor hnames hwSC cc hcc ⟨?_, hrootB, ?_, ?_⟩ Tr hTr L hL L' hL' H hH
    · intro T hT
      exact (hcand (Proofs.ModelProperties.Preceq_self B) T hT).resolve_right hBroot
    · intro A hAout
      exact hanchors w hw cc hcc A hAout
    · intro A hAout T hT D hAD hDA hDB _hDBne
      rcases hcand hDB T hT with hDcandidate | hDroot
      · exact hDcandidate
      · exact (hDA (Proofs.ModelProperties.Preceq_antisymm
          (preceq_trans_Preceq hDroot
            (Restated.Vocabulary.Proofs.w4_fgRoot_preceq_nodeAnchor facts S n _ A hAout)) hAD)).elim
  · exact preceq_trans_Preceq hBanchor hheadA

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

/-- After the progress deadline, every SG block that `v`'s round-`(c + 1)` action read along `W` can
    select is an ancestor of every head that `w`'s vote-duty read along `W` can return at every slot
    `d` from the round's first interior slot on, with `vote_time d + Δ` in the horizon. -/
theorem actionSGBlock_preceq_voterHeadAt_after_GSTOn (facts : Record.Facts M)
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
    {d : Slot} (hd : (M.opening_slot S.hc (c + 1)) + 1 ≤ d)
    (hhor : M.vote_time S.E d + S.E.Δ ≤ rho.horizon)
    {v w : V} (hv : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (c + 1)))) (hAv : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick v (Restated.Vocabulary.Execution.Setup.a M S (c + 1))) → M.awake_for_grade2 S v (W j v) (c + 1))
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
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st (M.vote_time S.E d))
        (W (strictEventIndex rho (M.vote_time S.E d)) w).record cc
      ∀ Tr : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ Tr →
      ∀ L : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
      ∀ L' : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
      ∀ H : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
          (M.toHealing n.st.core) Tr L L' (n.st.core.s - 1) ⇢ H →
      ∀ nv ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (c + 1))) v) (c + 1),
      ∀ A2 : Option (Block V),
        M.grade2_block_with (M.gradeContract nv.cache) S.E S.hc (M.toHealing nv.st.core)
          (M.round_of S.hc (M.toHealing nv.st.core).s) ⇢ A2 →
      ∀ G : Block V,
        M.get_sg_vote_with (M.gradeContract nv.cache) S.E S.hc (M.toHealing nv.st.core)
          (M.round_of S.hc (M.toHealing nv.st.core).s) A2 ⇢ G →
        Block.Preceq G H := by
  intro cc hcc n Tr hTr L hL L' hL' H hH nv hnv A2 hA2 G hG
  have hΔ := S.E.Δ_pos
  have hsourceHor : (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) ≤ rho.horizon := by
    have hinst := facts.sch.slot_instants_l55 S.E (M.opening_slot S.hc (c + 1))
    have hconfA :=
      Restated.Vocabulary.Proofs.HealingSurface.opening_confirmation_time_eq_action facts S (c + 1)
    have hmono := facts.sch.vote_time_mono_slots S.E hd
    linarith [hinst.2.2.2.2.1, hinst.2.2.2.2.2]
  have hstartRound : (M.round_of S.hc (M.opening_slot S.hc (c + 1) + 1)) = c + 1 :=
    facts.gr.round_of_eq_of_opening_succ_le_of_lt_next_opening S.hc (le_refl _)
      (facts.gr.firstInterior_lt_nextOpening_l86e S (c + 1))
  have hstartDead : (M.opening_slot S.hc)
      (fgSafetyProgressDeadline S rho rGST gap delayExtra) + 1 ≤ M.opening_slot S.hc (c + 1) + 1 :=
    Nat.add_le_add_right (facts.gr.opening_slot_mono S (hc.trans (Nat.le_succ c))) 1
  have hGSTdead : rGST ≤ fgSafetyProgressDeadline S rho rGST gap delayExtra := by
    unfold fgSafetyProgressDeadline
    exact (Nat.le_succ rGST).trans (Nat.le_add_right _ _)
  have hall : ∀ j : Slot, M.opening_slot S.hc (c + 1) + 1 ≤ j →
      M.vote_time S.E j + S.E.Δ ≤ rho.horizon →
      ∀ u ∈ Hs (M.vote_time S.E j), ∀ cu : M.Cache,
        M.onPhaseTick S.E S.hc
          (W (strictEventIndex rho (M.vote_time S.E j)) u).st.core.toHealing
          (M.vote_time S.E j)
          (W (strictEventIndex rho (M.vote_time S.E j)) u).cache ⇢ cu →
        let nj := M.mkNode
          (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E j)) u).st (M.vote_time S.E j))
          (W (strictEventIndex rho (M.vote_time S.E j)) u).record cu
        ∀ T1 : Finset (Block V), M.voter_filtered_block_tree S.E nj.st.core nj.st.core.s ⇢ T1 →
        ∀ L1 : Finset (GoldfishVote V),
          M.voter_view S.E (M.toHealing nj.st.core).toFG.toSG.toGoldfishStore nj.st.core.s ⇢ L1 →
        ∀ L1' : Finset (GoldfishVote V),
          M.voter_support_view S.E (M.toHealing nj.st.core).toFG.toSG.toGoldfishStore
            nj.st.core.s ⇢ L1' →
        ∀ H1 : Block V, M.get_head_in_tree_with_layer (M.gradeContract nj.cache) S.E S.hc
            (M.toHealing nj.st.core) T1 L1 L1' (nj.st.core.s - 1) ⇢ H1 →
          Block.Preceq G H1 := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      intro hj hjor u hu cu hcu nj T1 hT1 L1 hL1 L1' hL1' H1 hH1
      by_cases hbase : j = M.opening_slot S.hc (c + 1) + 1
      · subst hbase
        exact Restated.actionSGBlock_preceq_firstInteriorHead_after_GST_namedOn facts S Hs Xb hf
          hHs hHsXb hcom hbelow hrec hdelay hpost hc hsourceHor hv hAv hu hloPost hloOpen ht₀
          hA cu hcu T1 hT1 L1 hL1 L1' hL1' H1 hH1 nv hnv A2 hA2 G hG
      · cases j with
        | zero => exact absurd hj (Nat.not_succ_le_zero _)
        | succ s =>
          have hsPrev : M.opening_slot S.hc (c + 1) + 1 ≤ s :=
            Nat.le_of_lt_succ (lt_of_le_of_ne hj (Ne.symm hbase))
          have hsDead := hstartDead.trans hsPrev
          have hprevHor : M.vote_time S.E s + S.E.Δ ≤ rho.horizon :=
            (Int.add_le_add_right (facts.sch.vote_time_mono_slots S.E (Nat.le_succ s)) _).trans hjor
          have hprevHeads := ih s (Nat.lt_succ_self s) hsPrev hprevHor
          have hreadHor : M.vote_time S.E (s + 1) ≤ rho.horizon :=
            (Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans hjor
          have hanchors : ∀ z ∈ Hs (M.vote_time S.E (s + 1)), ∀ cz : M.Cache,
              M.onPhaseTick S.E S.hc
                (W (strictEventIndex rho (M.vote_time S.E (s + 1))) z).st.core.toHealing
                (M.vote_time S.E (s + 1))
                (W (strictEventIndex rho (M.vote_time S.E (s + 1))) z).cache ⇢ cz →
              let nz := M.mkNode
                (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) z).st
                  (M.vote_time S.E (s + 1)))
                (W (strictEventIndex rho (M.vote_time S.E (s + 1))) z).record cz
              ∀ A0 : Block V,
                Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S nz
                  (M.round_of S.hc nz.st.core.s) ⇢ A0 →
                Block.compatible A0 G = true := by
            intro z hz cz hcz nz A0 hA0
            obtain ⟨hlower, hupper⟩ := facts.gr.slot_round_bounds_l86e S (s + 1)
            have hrLower : c + 1 ≤ (M.round_of S.hc (s + 1)) := by
              rw [← hstartRound]
              exact facts.gr.round_of_mono S.hc hj
            by_cases hrEq : (M.round_of S.hc (s + 1)) = c + 1
            · rw [hrEq] at hupper
              exact Restated.voterAnchorAt_firstInterior_compatible_actionSGBlock_after_GSTOn facts S
                Hs Xb hf hHs hHsXb hcom hbelow hrec hdelay hpost hc hsourceHor hj hupper
                hreadHor hjor hv hAv hz hloPost hloOpen ht₀ hA cz hcz A0 hA0 nv hnv A2 hA2 G hG
            · have hrGt : c + 1 < (M.round_of S.hc (s + 1)) := lt_of_le_of_ne hrLower (Ne.symm hrEq)
              obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hrGt)
              have hrk : M.round_of S.hc (s + 1) = c + m + 1 + 1 := by
                rw [hm, Nat.succ_add, Nat.add_right_comm c 1 m]
              have hk₀ : c ≤ c + m := Nat.le_add_right _ _
              generalize c + m = k₀ at hrk hk₀
              rw [hrk] at hlower hupper
              have hpred : M.round_of S.hc (s + 1) - 1 = k₀ + 1 := by rw [hrk]; rfl
              have hkPredDead : fgSafetyProgressDeadline S rho rGST gap delayExtra ≤ k₀ :=
                hc.trans hk₀
              have hkFirstLt : (M.opening_slot S.hc (k₀ + 1)) + 1 < s + 1 :=
                (facts.gr.firstInterior_lt_nextOpening_l86e S (k₀ + 1)).trans_le hlower
              have hkStart : M.opening_slot S.hc (c + 1) + 1 ≤ (M.opening_slot S.hc (k₀ + 1)) + 1 :=
                Nat.add_le_add_right (facts.gr.opening_slot_mono S (Nat.succ_le_succ hk₀)) 1
              have hkFirstHor :
                  M.vote_time S.E ((M.opening_slot S.hc (k₀ + 1)) + 1) + S.E.Δ ≤ rho.horizon :=
                (Int.add_le_add_right
                  (facts.sch.vote_time_mono_slots S.E (Nat.le_of_lt hkFirstLt)) _).trans hjor
              have hkActionHor : (Restated.Vocabulary.Execution.Setup.a M S (k₀ + 1)) ≤ rho.horizon :=
                ((Restated.Vocabulary.Protocol.action_lt_vote_time_two_after facts S (k₀ + 1)).le.trans
                  (facts.sch.vote_time_mono_slots S.E (Nat.succ_le_of_lt hkFirstLt))).trans hreadHor
              obtain ⟨y, hy⟩ := Finset.card_pos.mp (by
                have hmajority := hcom ((M.opening_slot S.hc (k₀ + 1)) + 1)
                show 0 < ((S.E.committee ((M.opening_slot S.hc (k₀ + 1)) + 1)) ∩
                  Hs (M.confirmation_time S.E ((M.opening_slot S.hc (k₀ + 1)) + 1))).card
                omega)
              have hyVote : y ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc (k₀ + 1)) + 1)) :=
                hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E _)
                  (Finset.mem_inter.mp hy).2
              obtain ⟨cy, hcy⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
                (W (strictEventIndex rho
                  (M.vote_time S.E (M.opening_slot S.hc (k₀ + 1) + 1))) y).st.core.toHealing
                (M.vote_time S.E (M.opening_slot S.hc (k₀ + 1) + 1))
                (W (strictEventIndex rho
                  (M.vote_time S.E (M.opening_slot S.hc (k₀ + 1) + 1))) y).cache
              let ny : M.N := M.mkNode
                (M.ns_setClock S.E
                  (W (strictEventIndex rho
                    (M.vote_time S.E (M.opening_slot S.hc (k₀ + 1) + 1))) y).st
                  (M.vote_time S.E (M.opening_slot S.hc (k₀ + 1) + 1)))
                (W (strictEventIndex rho
                  (M.vote_time S.E (M.opening_slot S.hc (k₀ + 1) + 1))) y).record cy
              obtain ⟨Ty, hTy⟩ :=
                facts.fc.voter_filtered_block_tree_nonempty S.E ny.st.core ny.st.core.s
              obtain ⟨Ly, hLy⟩ := facts.fc.voter_view_nonempty S.E
                (M.toHealing ny.st.core).toFG.toSG.toGoldfishStore ny.st.core.s
              obtain ⟨Ly', hLy'⟩ := facts.fc.voter_support_view_nonempty S.E
                (M.toHealing ny.st.core).toFG.toSG.toGoldfishStore ny.st.core.s
              obtain ⟨Hy, hHy⟩ := facts.fc.get_head_in_tree_with_layer_nonempty
                (M.gradeContract ny.cache) S.E S.hc (M.toHealing ny.st.core) Ty Ly Ly'
                (ny.st.core.s - 1)
              have hBHead : Block.Preceq G Hy :=
                ih ((M.opening_slot S.hc (k₀ + 1)) + 1) hkFirstLt hkStart hkFirstHor y hyVote cy hcy
                  Ty hTy Ly hLy Ly' hLy' Hy hHy
              have hhistory : Restated.HonestSGEmissionsCompatibleAtRoundOn M S rho W
                  (fun t => W (strictEventIndex rho t)) Hs (k₀ + 1) G := by
                intro x hx nx hnx D hD hemit _ _ _ A2x hA2x Gx hGx
                have hnxMem : nx ∈ Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt M S rho x
                    (k₀ + 1) :=
                  ⟨W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (k₀ + 1))),
                    (p64b% mem_stateBeforeTime_along₆₄b) hf.sorted hf.onePath _, hnx⟩
                have hshape := Restated.Vocabulary.Proofs.HealingSurface.actionAttestationAt_shape facts
                  S rho x (k₀ + 1) nx hnxMem D hD A2x hA2x Gx hGx
                have hxAwake : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick x
                    (Restated.Vocabulary.Execution.Setup.a M S (k₀ + 1))) →
                    M.awake_for_grade2 S x (W j x) (k₀ + 1) := by
                  intro j hj
                  obtain ⟨i', hi', h⟩ := Restated.Vocabulary.Proofs.Optimistic.emits_attest_awake
                    facts S W hf.onePath hemit
                  rw [hshape.2.1] at h
                  rw [← Restated.tick_index_eq_of_unique hf.tickIndexUnique hi' hj]
                  exact h
                have hSGHead :=
                  Restated.actionSGBlock_preceq_firstInteriorHead_after_GST_namedOn facts S Hs Xb hf
                    hHs hHsXb hcom hbelow hrec hdelay hpost (c := k₀) hkPredDead hkActionHor
                    hx hxAwake hyVote hloPost hloOpen ht₀ hA cy hcy Ty hTy Ly hLy Ly' hLy' Hy hHy
                    nx hnx A2x hA2x Gx hGx
                exact compatible_of_preceq_common_Preceq hSGHead hBHead
              have hdeadlineRead :
                  (Restated.Vocabulary.Execution.Setup.a M S
                    (fgSafetyProgressDeadline S rho rGST gap delayExtra)) ≤
                    M.vote_time S.E (s + 1) :=
                (Restated.Vocabulary.Protocol.action_lt_vote_time_two_after facts S _).le.trans
                  (facts.sch.vote_time_mono_slots S.E (Nat.succ_le_succ hsDead))
              have hzPrev : z ∈ Hs (M.vote_time S.E s) :=
                hHs _ _ (facts.sch.vote_time_mono_slots S.E (Nat.le_succ s)) hz
              obtain ⟨cz0, hcz0⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
                (W (strictEventIndex rho (M.vote_time S.E s)) z).st.core.toHealing
                (M.vote_time S.E s) (W (strictEventIndex rho (M.vote_time S.E s)) z).cache
              let nz0 : M.N := M.mkNode
                (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) z).st
                  (M.vote_time S.E s))
                (W (strictEventIndex rho (M.vote_time S.E s)) z).record cz0
              obtain ⟨Tz, hTz⟩ :=
                facts.fc.voter_filtered_block_tree_nonempty S.E nz0.st.core nz0.st.core.s
              obtain ⟨Lz, hLz⟩ := facts.fc.voter_view_nonempty S.E
                (M.toHealing nz0.st.core).toFG.toSG.toGoldfishStore nz0.st.core.s
              obtain ⟨Lz', hLz'⟩ := facts.fc.voter_support_view_nonempty S.E
                (M.toHealing nz0.st.core).toFG.toSG.toGoldfishStore nz0.st.core.s
              obtain ⟨Hz, hHz⟩ := facts.fc.get_head_in_tree_with_layer_nonempty
                (M.gradeContract nz0.cache) S.E S.hc (M.toHealing nz0.st.core) Tz Lz Lz'
                (nz0.st.core.s - 1)
              have hGHz : Block.Preceq G Hz :=
                hprevHeads z hzPrev cz0 hcz0 Tz hTz Lz hLz Lz' hLz' Hz hHz
              have hrootPre := Restated.fgRoot_preceq_previousHead_after_GSTOn facts S Hs Xb hf
                hHs hHsXb hcom hbelow hrec hdelay hpost hdeadlineRead hreadHor hsDead (le_refl _)
                hprevHor hz hloPost hloOpen ht₀ hA z hzPrev cz0 hcz0 Tz hTz Lz hLz Lz' hLz' Hz hHz
              have hroot : Block.compatible
                  (M.get_fg_root (M.toHealing (M.mkNode (M.ns_setClock S.E
                    (W (strictEventIndex rho (M.vote_time S.E (s + 1))) z).st
                    (M.vote_time S.E (s + 1)))
                    (W (strictEventIndex rho (M.vote_time S.E (s + 1))) z).record cz).st.core).toFG)
                  G = true := by
                rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [(p60% setClock_fgRoot₆₀) facts S]
                exact compatible_of_preceq_common_Preceq hrootPre hGHz
              have hsgPost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (k₀ + 1)) :=
                hloPost.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S
                  (hGSTdead.trans (hkPredDead.trans (Nat.le_succ _))))
              have hcut : Restated.Vocabulary.Protocol.HealConfig.Γ_0 M S.hc S.E.Δ
                  (M.round_of S.hc (s + 1)) ≤ M.vote_time S.E (s + 1) :=
                Restated.Vocabulary.Proofs.HealingSurface.Γ_0_le_vote_time_of_round_eq facts S rfl
              have hdomG1 : M.domain S.E S.hc ((M.round_of S.hc (s + 1))) .g1 =
                  Restated.Vocabulary.Protocol.HealConfig.Γ_0 M S.hc S.E.Δ
                    (M.round_of S.hc (s + 1)) := by
                rw [facts.gr.Sts_domain_g1_eq_opening, facts.gr.opening_eq_proposal_time]
                exact (facts.sch.Γ_0_eq_proposal_time S.hc S.E _).symm
              have hzG1 : z ∈ Hs (M.domain S.E S.hc ((M.round_of S.hc (s + 1))) .g1) :=
                hHs _ _ (hdomG1.trans_le hcut) hz
              have hconfHor : M.confirmation_time S.E s ≤ rho.horizon := by
                have hinst := facts.sch.slot_instants_l55 S.E s
                linarith [hinst.2.2.2.2.1, hinst.2.2.2.2.2]
              have hkA : lo ≤ M.early S.E S.hc (k₀ + 1) .g2 - S.E.Δ :=
                Restated.lo_le_early_g2_sub_delta_of_action_lt facts S hloPost
                  (Nat.lt_succ_of_lt (rGST_lt_of_deadline_le₈₆e S hkPredDead))
              exact Restated.voterAnchorAt_compatible_of_previousSGHistory_namedOn facts S Hs Xb hf
                hHs hHsXb hbelow hconfHor (by rw [hrk]; exact Nat.succ_pos _)
                (by rw [hpred]; exact hhistory) (by rw [hpred]; exact hsgPost) hzG1 cz hcz hroot
                (by rw [hpred]; exact hA (k₀ + 1) hkA) A0 hA0
          exact Restated.allHonestHeads_succ_of_voterAnchorCompatible_after_GST_namedOn facts S Hs Xb
            hf hHs hHsXb hcom hbelow hrec hdelay hpost hsDead hreadHor hprevHeads hanchors
            hloPost hloOpen ht₀ hA u hu cu hcu T1 hT1 L1 hL1 L1' hL1' H1 hH1
  exact hall d hd hhor w hw cc hcc Tr hTr L hL L' hL' H hH

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
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- In the run `R` of the first `n` steps of the execution `x`, read along the path
    `W := Restated.runAllPath M S Sched x v₀ n`: for a round `c` at or after the progress deadline
    and a slot `d` from the first interior slot of round `c + 1` on with `vote_time d + Δ` within
    the horizon, if `v` is not held at `S.a (c + 1)` and `w` is not held at `vote_time d`, then
    every SG block `v`'s round-`(c + 1)` action read can select is an ancestor of every head `w`'s
    vote-duty read of slot `d` can return. -/
theorem actionSGBlock_preceq_voterHeadAt_runAll_notHeld (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v₀ : V) (n : Nat)
    {tGAT tAwakeEnd : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tAwakeEnd →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hn : (x[n].time : Int) ≤ tAwakeEnd)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tAwakeEnd gap)
    {c : Round}
    (hc : fgSafetyProgressDeadline (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } : Record.Run V)
        (Restated.roundAt M S tGAT + S.hc.η_SG) gap (Setup.alwaysAwake S).extraRounds ≤ c)
    {d : Slot} (hd : (M.opening_slot S.hc (c + 1)) + 1 ≤ d)
    (hhor : M.vote_time S.E d + S.E.Δ ≤
      ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } :
        Record.Run V).horizon)
    {v w : V} (hv : v ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (c + 1))))
    (hw : w ∈ notHeldAt Sched (M.vote_time S.E d)) :
    let R : Record.Run V :=
      { Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) }
    let W := Restated.runAllPath M S Sched x v₀ n
    ∀ cc : M.Cache,
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex R (M.vote_time S.E d)) w).st.core.toHealing
        (M.vote_time S.E d)
        (W (strictEventIndex R (M.vote_time S.E d)) w).cache ⇢ cc →
      let nw := M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex R (M.vote_time S.E d)) w).st (M.vote_time S.E d))
        (W (strictEventIndex R (M.vote_time S.E d)) w).record cc
      ∀ Tr : Finset (Block V), M.voter_filtered_block_tree S.E nw.st.core nw.st.core.s ⇢ Tr →
      ∀ L : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing nw.st.core).toFG.toSG.toGoldfishStore nw.st.core.s ⇢ L →
      ∀ L' : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing nw.st.core).toFG.toSG.toGoldfishStore
          nw.st.core.s ⇢ L' →
      ∀ H : Block V, M.get_head_in_tree_with_layer (M.gradeContract nw.cache) S.E S.hc
          (M.toHealing nw.st.core) Tr L L' (nw.st.core.s - 1) ⇢ H →
      ∀ nv ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
          (W (strictEventIndex R
            (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (c + 1))) v) (c + 1),
      ∀ A2 : Option (Block V),
        M.grade2_block_with (M.gradeContract nv.cache) S.E S.hc (M.toHealing nv.st.core)
          (M.round_of S.hc (M.toHealing nv.st.core).s) ⇢ A2 →
      ∀ G : Block V,
        M.get_sg_vote_with (M.gradeContract nv.cache) S.E S.hc (M.toHealing nv.st.core)
          (M.round_of S.hc (M.toHealing nv.st.core).s) A2 ⇢ G →
        Block.Preceq G H := by
  intro R W
  obtain ⟨hpost, -, hloOpen, ht₀⟩ := Restated.roundAt_bounds_l71 facts S hgst
  have hkC : tGAT + 1 ≤ M.early S.E S.hc (c + 1) .g2 - S.E.Δ :=
    Restated.lo_le_early_g2_sub_delta_of_action_lt facts S (Restated.roundAt_lo_le_rGST_l71 facts S tGAT)
      (Nat.lt_succ_of_lt (rGST_lt_of_deadline_le₈₆e (Setup.alwaysAwake S) hc))
  exact Restated.actionSGBlock_preceq_voterHeadAt_after_GSTOn facts
    (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ
    (Restated.admissibleFieldsOn_runAll_notHeld facts S Sched x v₀ n hsync hmono hawake hgst hcv
      hvalid hawm hthird hn)
    (fun _ _ h => notHeldAt_anti hmono h) (fun _ => Finset.subset_univ _)
    (Restated.honestCommitteesOn_notHeld facts S Sched hcom)
    (Restated.belowOneThirdOn_runAll_notHeld facts S Sched x v₀ n hthird hn)
    (Restated.multiProposerRecurrenceOn_runAll_notHeld facts S Sched x v₀ n hrec hn)
    (Setup.timeoutDelayBound _) hpost hc hd hhor hv
    (fun j hj => Restated.awake_g2_action_runAllPath facts S Sched x v₀ n hmono hawake hn
      (c + 1) hkC v j hj) hw
    (Restated.roundAt_lo_le_rGST_l71 facts S tGAT) hloOpen ht₀
    (fun k hk u _ j hj => Restated.awake_g2_action_runAllPath facts S Sched x v₀ n hmono hawake hn
      k hk u j hj)

end

end DecoupledConsensusModel.Sts.Restated
