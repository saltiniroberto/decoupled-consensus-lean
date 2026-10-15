import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13beRoute3_44
import Proofs.Claims.Restated.Claim13beRoute3_46
import Proofs.Claims.Restated.Claim13beRoute3_49
import Proofs.Claims.Restated.Claim13beRoute3_51
import Proofs.Claims.Restated.Claim13beRoute3_52
import Proofs.Claims.Restated.Claim13beRoute3_54
import Proofs.Claims.Restated.Claim13beRoute3_58
import Proofs.Claims.Restated.Claim13beRoute3_61
import Proofs.Claims.Restated.Claim13beRoute3_62
import Proofs.Claims.Restated.Claim13beRoute3_65b
import Proofs.Claims.Restated.Claim13beRoute3_71
import Proofs.Claims.Restated.Claim13beRoute3_72
import Proofs.Claims.Restated.Claim13beRoute3_86
import Proofs.Claims.Restated.Claim13beRoute3_86b
import Proofs.Claims.Restated.Claim13beRoute3_86e
import Proofs.Claims.Restated.Claim13beRoute3_86f
import Proofs.Claims.Restated.Claim13beRoute3_87
import Proofs.Claims.Restated.Vocabulary_Execution_CarrierInteriorAdoption
import Proofs.Claims.Restated.Vocabulary_Execution_ExcludesRefute
import Proofs.Claims.Restated.Vocabulary_ModelVocabulary_Healing_Schedule
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_ProposalBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_Grades
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_PostHealingContinuation
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.Claim13beRoute3_72
import Model.Conditions.RunAll
import Model.Conditions.RunVocabulary
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Internal_Definitions_NamedLifecycle
import Model.Conditions.Vocabulary_Internal_Definitions_NamedProposalPivot
import Model.Conditions.Vocabulary_Internal_Definitions_NamedResult23Statements
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Internal_Invariants
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedHeadReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ProposalSourcesInternal
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_FGForkChoice_Finality
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_ModelVocabulary_Healing_Schedule
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Agreement
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_SGOpeningFrozenSuffix
import Proofs.Vocabulary.Protocol.ForkChoice.Views.ProposalCore
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Protocol_Handlers_Blocks
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring

/-!
# The opening proposal after the progress deadline

Theorems over a model `M : Record.Model V`, read along one path `W` of the run: at an opening at
least two rounds after the progress deadline, every member of the set votes the opening proposal,
has it as live confirmation at the round's action, and finds it clear at its action read.
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
/-- Refers to a private theorem of `Proofs.Claims.Restated.Claim13beRoute3_58` by name. -/
local macro "p58% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_58)
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
/-- Refers to a private theorem of `Proofs.Claims.Restated.Claim13beRoute3_86f` by name. -/
local macro "p86f% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_86f)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

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
open DecoupledConsensusModel.Statements.Instantiation

/-- Every node state `n0` has, at every instant `t`, some head `H` it can vote: the cache update,
    the voter's filtered block tree, the two voter views and the in-tree head each have an outcome. -/
private theorem exists_headOutcome₈₆g (facts : Record.Facts M) (S : Setup V) (n0 : M.N)
    (t : Time) :
    ∃ H : Block V, ∃ cw : M.Cache,
      M.onPhaseTick S.E S.hc n0.st.core.toHealing t n0.cache ⇢ cw ∧
      let nw := M.mkNode (M.ns_setClock S.E n0.st t) n0.record cw
      ∃ T : Finset (Block V), M.voter_filtered_block_tree S.E nw.st.core nw.st.core.s ⇢ T ∧
      ∃ L : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing nw.st.core).toFG.toSG.toGoldfishStore nw.st.core.s ⇢ L ∧
      ∃ L' : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing nw.st.core).toFG.toSG.toGoldfishStore
          nw.st.core.s ⇢ L' ∧
      M.get_head_in_tree_with_layer (M.gradeContract nw.cache) S.E S.hc
        (M.toHealing nw.st.core) T L L' (nw.st.core.s - 1) ⇢ H := by
  obtain ⟨cw, hcw⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc n0.st.core.toHealing t n0.cache
  obtain ⟨T, hT⟩ := facts.fc.voter_filtered_block_tree_nonempty S.E
    (M.mkNode (M.ns_setClock S.E n0.st t) n0.record cw).st.core
    (M.mkNode (M.ns_setClock S.E n0.st t) n0.record cw).st.core.s
  obtain ⟨L, hL⟩ := facts.fc.voter_view_nonempty S.E
    (M.toHealing (M.mkNode (M.ns_setClock S.E n0.st t) n0.record cw).st.core).toFG.toSG.toGoldfishStore
    (M.mkNode (M.ns_setClock S.E n0.st t) n0.record cw).st.core.s
  obtain ⟨L', hL'⟩ := facts.fc.voter_support_view_nonempty S.E
    (M.toHealing (M.mkNode (M.ns_setClock S.E n0.st t) n0.record cw).st.core).toFG.toSG.toGoldfishStore
    (M.mkNode (M.ns_setClock S.E n0.st t) n0.record cw).st.core.s
  obtain ⟨H, hH⟩ := facts.fc.get_head_in_tree_with_layer_nonempty
    (M.gradeContract (M.mkNode (M.ns_setClock S.E n0.st t) n0.record cw).cache) S.E S.hc
    (M.toHealing (M.mkNode (M.ns_setClock S.E n0.st t) n0.record cw).st.core) T L L'
    ((M.mkNode (M.ns_setClock S.E n0.st t) n0.record cw).st.core.s - 1)
  exact ⟨H, cw, hcw, T, hT, L, hL, L', hL', hH⟩

/-- After the progress deadline, every block the SG vote selector can return at a round-`(m − 1)`
    action read along `W` of a member of the set for `S.a (m − 1)` is an ancestor of the parent of
    every proposal input of the opening proposer's read `pn`. -/
private theorem actionSGBlock_preceq_proposedParent_afterDeadlineOn₈₆g (facts : Record.Facts M)
    {delayExtra : Nat}
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hbelow : BelowOneThirdOn S rho Hs)
    {rGST gap : Round} {t₀ : Int} (hrec : Restated.MultiProposerRecurrenceOn M S Hs gap t₀ rho.horizon)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    {m : Round} (hm : fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ m)
    (hhor : M.vote_time S.E ((M.opening_slot S.hc m)) ≤ rho.horizon)
    (hopening : S.E.proposer ((M.opening_slot S.hc m)) ∈
      Hs (M.confirmation_time S.E ((M.opening_slot S.hc m))))
    {P : NamedBlock V}
    (cp : M.Cache)
    (hcp : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
        (S.E.proposer (M.opening_slot S.hc m))).st.core.toHealing
      (M.proposal_time S.E (M.opening_slot S.hc m))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
        (S.E.proposer (M.opening_slot S.hc m))).cache ⇢ cp)
    (hP : M.proposal_with (M.gradeContract cp) .poolAndCarried S.E S.hc
      (S.node (S.E.proposer (M.opening_slot S.hc m)))
      (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
          (S.E.proposer (M.opening_slot S.hc m))).st
        (M.proposal_time S.E (M.opening_slot S.hc m)))
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
          (S.E.proposer (M.opening_slot S.hc m))).record cp).st ⇢ some P)
    (hloPost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    (hloOpen : lo ≤ M.opening S.E S.hc (rGST + 2 - S.hc.η_SG))
    (ht₀ : t₀ ≤ (Restated.Vocabulary.Execution.Setup.a M S (rGST + 2)))
    (hAll : ∀ (k : Round) (u : V), lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → u ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S k) → ∀ (j : Nat), rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (m - 1))),
      ∀ nv ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (m - 1))) u) (m - 1),
      ∀ A2 : Option (Block V),
        M.grade2_block_with (M.gradeContract nv.cache) S.E S.hc (M.toHealing nv.st.core)
          (M.round_of S.hc (M.toHealing nv.st.core).s) ⇢ A2 →
      ∀ G : Block V,
        M.get_sg_vote_with (M.gradeContract nv.cache) S.E S.hc (M.toHealing nv.st.core)
          (M.round_of S.hc (M.toHealing nv.st.core).s) A2 ⇢ G →
      ∀ I : Protocol.ProposalInput V,
        Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract cp) S.E S.hc
          (S.node (S.E.proposer (M.opening_slot S.hc m)))
          (M.toHealing (M.mkNode (M.ns_setClock S.E
            (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
              (S.E.proposer (M.opening_slot S.hc m))).st
            (M.proposal_time S.E (M.opening_slot S.hc m)))
            (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
              (S.E.proposer (M.opening_slot S.hc m))).record cp).st.core) ⇢ I →
        Block.Preceq G I.parent := by
  intro u hu nv hnv A2 hA2 G hG I hI
  have hex := fun w : V => exists_headOutcome₈₆g facts S
    (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc m) - 1))) w)
    (M.vote_time S.E ((M.opening_slot S.hc m) - 1))
  choose head hheadAll using hex
  obtain ⟨E, -, -, -, hsg, hpar, -, -⟩ :=
    Restated.openingPivot_afterDeadlineOn facts S Hs Xb hf hHs hHsXb hcom hbelow hrec hdelay
      hpost hm hhor hopening cp hcp hP hloPost hloOpen ht₀ hAll head (fun w _ => hheadAll w)
  exact preceq_trans_Preceq (hsg u hu nv hnv A2 hA2 G hG) (hpar I hI)

/-- The candidate score bridge does not depend on the grade caches written into the proposer's and
    the voter's stores. -/
private theorem scoreBridge_store_with_cache₈₆g (facts : Record.Facts M) {S : Setup V} {rho : Record.Run V}
    {s : Slot} {v : V} {P : NamedBlock V} {n : M.N} {X Y : M.NS} {c c' : M.Cache}
    (h : Restated.Vocabulary.Proofs.HealingSurface.NamedProposalCandidateScoreBridge M S rho s v P n
      X.core Y.core) :
    Restated.Vocabulary.Proofs.HealingSurface.NamedProposalCandidateScoreBridge M S rho s v P n
      (M.store_with_cache X c).core (M.store_with_cache Y c').core := by
  intro C hC1 hC2 Yv hY Z hZ
  rw [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_T]
  rw [facts.nd.store_with_cache_get_filtered_block_tree] at hC2
  rw [facts.nd.store_with_cache_voter_view] at hY
  rw [facts.nd.store_with_cache_voter_support_view] at hZ
  exact h C hC1 hC2 Yv hY Z hZ

/-- For a round `m` at least two rounds after the progress deadline whose opening proposer is in the
    set and proposes `P` along `W`: for every member `v` of the set for the opening's vote instant,
    every vote-duty read of `v` at the opening slot, every outcome `T₀` of its filtered block tree
    and every proposal input `I`, the vote store extends to `P` over `T₀` without `P` with parent
    `I.parent`, and every head the read can vote is `P`. -/
theorem openingProposal_voteStoreExtends_afterDeadlineOn (facts : Record.Facts M)
    {delayExtra : Nat}
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hbelow : BelowOneThirdOn S rho Hs)
    {rGST gap : Round} {t₀ : Int} (hrec : Restated.MultiProposerRecurrenceOn M S Hs gap t₀ rho.horizon)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    {m : Round} (hm : fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ m)
    (hhor : M.vote_time S.E ((M.opening_slot S.hc m)) ≤ rho.horizon)
    (hopening : S.E.proposer ((M.opening_slot S.hc m)) ∈
      Hs (M.confirmation_time S.E ((M.opening_slot S.hc m))))
    {P : NamedBlock V}
    (cp : M.Cache)
    (hcp : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
        (S.E.proposer (M.opening_slot S.hc m))).st.core.toHealing
      (M.proposal_time S.E (M.opening_slot S.hc m))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
        (S.E.proposer (M.opening_slot S.hc m))).cache ⇢ cp)
    (hP : M.proposal_with (M.gradeContract cp) .poolAndCarried S.E S.hc
      (S.node (S.E.proposer (M.opening_slot S.hc m)))
      (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
          (S.E.proposer (M.opening_slot S.hc m))).st
        (M.proposal_time S.E (M.opening_slot S.hc m)))
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
          (S.E.proposer (M.opening_slot S.hc m))).record cp).st ⇢ some P)
    (hloPost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    (hloOpen : lo ≤ M.opening S.E S.hc (rGST + 2 - S.hc.η_SG))
    (ht₀ : t₀ ≤ (Restated.Vocabulary.Execution.Setup.a M S (rGST + 2)))
    (hAll : ∀ (k : Round) (u : V), lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → u ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S k) → ∀ (j : Nat), rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    ∀ v ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc m))),
    ∀ cv : M.Cache, M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc m))) v).st.core.toHealing
        (M.vote_time S.E (M.opening_slot S.hc m))
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc m))) v).cache ⇢ cv →
      let mv := M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc m))) v).st
          (M.vote_time S.E (M.opening_slot S.hc m)))
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc m))) v).record cv
      ∀ T₀ : Finset (Block V), M.voter_filtered_block_tree S.E mv.st.core mv.st.core.s ⇢ T₀ →
      ∀ I : Protocol.ProposalInput V,
        Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract cp) S.E S.hc
          (S.node (S.E.proposer (M.opening_slot S.hc m)))
          (M.toHealing (M.mkNode (M.ns_setClock S.E
            (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
              (S.E.proposer (M.opening_slot S.hc m))).st
            (M.proposal_time S.E (M.opening_slot S.hc m)))
            (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
              (S.E.proposer (M.opening_slot S.hc m))).record cp).st.core) ⇢ I →
      Restated.Vocabulary.Proofs.Optimistic.NamedVoteStoreExtends M S rho v ((M.opening_slot S.hc m))
        mv (T₀.erase P.erase) I.parent P := by
  classical
  have hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ →
      ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat,
      rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) →
      M.awake_for_grade2 S u (W j u) k :=
    fun k hk u hu => hAll k u hk (hHs _ _ (le_add_of_nonneg_right S.E.Δ_pos.le) hu)
  obtain ⟨hdeadlineSlot, hdeadlineTwo, _hinterior, hdPos, hdSucc, hcEq, hqEq, hcDeadline,
    hdeadlineTwoD⟩ := facts.gr.openingSlots_l86f S hm
  set D := fgSafetyProgressDeadline S rho rGST gap delayExtra with hDdef
  set start := (M.opening_slot S.hc m) with hstartdef
  set d := start - 1 with hddef
  set wp := W (strictEventIndex rho (M.proposal_time S.E start)) (S.E.proposer start) with hwpdef
  set pn := M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E start)) wp.record cp
    with hpndef
  have hpnst : pn.st = M.store_with_cache (M.ns_setClock S.E wp.st (M.proposal_time S.E start)) cp :=
    facts.nd.mkNode_st _ _ _
  have hpncache : pn.cache = cp := facts.nd.mkNode_cache _ _ _
  have hpncore : pn.st = M.store_with_cache _ _ := facts.nd.mkNode_st _ _ _
  have hpread : pn ∈ Restated.Vocabulary.Statements.Instantiation.proposerReadAt M S rho start :=
    (p58% mkNode_mem_confirmationReadAt₅₈) hf.sorted hf.onePath _ _ cp hcp
  have hPn : M.proposal_with (M.gradeContract pn.cache) .poolAndCarried S.E S.hc
      (S.node (S.E.proposer start)) pn.st ⇢ some P := by
    rw [hpncache]
    exact hP
  have hPclock : M.proposal_with (M.gradeContract cp)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc (S.node (S.E.proposer start))
      (M.ns_setClock S.E wp.st (M.proposal_time S.E start)) ⇢ some P := by
    have h := hP
    rw [hpnst, facts.dt.proposal_with_store_with_cache] at h
    exact h
  have hGSTdead : rGST ≤ D := by
    rw [hDdef]
    unfold fgSafetyProgressDeadline
    exact (Nat.le_succ rGST).trans (Nat.le_add_right _ _)
  obtain ⟨hi1, hi2, hi3, hi4, hi5, hi6⟩ := facts.sch.slot_instants_l55 S.E d
  have hpS : M.proposal_time S.E start = M.proposal_time S.E d + 4 * S.E.Δ := by
    rw [← hdSucc]
    exact hi4
  have hvS : M.vote_time S.E start = M.proposal_time S.E d + 5 * S.E.Δ := by
    rw [← hdSucc]
    exact hi5
  have hΔ := S.E.Δ_pos
  have hstartPos : 0 < start := lt_of_lt_of_le hdPos (Nat.sub_le start 1)
  have hproposalHor : M.proposal_time S.E start ≤ rho.horizon :=
    (facts.sch.proposal_time_lt_vote_time S.E start).le.trans hhor
  have hprevVoteHor : M.vote_time S.E d ≤ rho.horizon :=
    (facts.sch.vote_time_mono_slots S.E (Nat.sub_le start 1)).trans hhor
  have hprevDelta : M.vote_time S.E d + S.E.Δ ≤ rho.horizon := by linarith
  have hsupportHor : M.support_cutoff S.E d ≤ rho.horizon := by linarith
  have hdeadlineProposal : (Restated.Vocabulary.Execution.Setup.a M S D) ≤ M.proposal_time S.E start :=
    (Restated.Vocabulary.Protocol.action_lt_proposal_time_two_after facts S D).le.trans
      (facts.sch.proposal_time_mono S.E hdeadlineTwo)
  have hdeadlineVote : (Restated.Vocabulary.Execution.Setup.a M S D) ≤ M.vote_time S.E start :=
    hdeadlineProposal.trans (facts.sch.proposal_time_lt_vote_time S.E start).le
  have hloD : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S D) :=
    hloPost.trans ((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone hGSTdead)
  have hloProposal : lo ≤ M.proposal_time S.E start := hloD.trans hdeadlineProposal
  have hloVoteD : lo ≤ M.vote_time S.E d :=
    Restated.lo_le_vote_after_deadline_l86e facts S hloPost hdeadlineSlot
  have hloProposalD : lo ≤ M.proposal_time S.E d :=
    hloD.trans ((Restated.Vocabulary.Protocol.action_lt_proposal_time_two_after facts S D).le.trans
      (facts.sch.proposal_time_mono S.E hdeadlineTwoD))
  have hloFreezeD : lo ≤ M.view_freeze S.E d := by linarith
  have hpropConf : S.E.proposer start ∈ Hs (M.confirmation_time S.E start) := hopening
  have hpropVote : S.E.proposer start ∈ Hs (M.vote_time S.E start) :=
    hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E start) hpropConf
  have hvoteNext : M.vote_time S.E start ≤ M.confirmation_time S.E d := by linarith
  have hrm1 : rGST < m - 1 := by
    rw [← hcEq]; exact Nat.lt_succ_of_le (hGSTdead.trans hcDeadline)
  have hkM1 : lo ≤ M.early S.E S.hc (m - 1) .g2 - S.E.Δ :=
    Restated.lo_le_early_g2_sub_delta_of_action_lt facts S hloPost hrm1
  have hwinD : lo ≤ M.early S.E S.hc (M.round_of S.hc d) .g1 - S.E.Δ := by
    have hD1 : rGST + 1 ≤ D := by
      rw [hDdef]
      unfold fgSafetyProgressDeadline
      exact Nat.le_add_right _ _
    have hDd : D ≤ M.round_of S.hc d := by
      have h := facts.gr.round_of_mono S.hc ((Nat.le_succ _).trans hdeadlineSlot)
      rwa [facts.gr.round_of_opening_slot_eq] at h
    have h1 := facts.gr.action_delta_le_early S S.hc.R_ge_three
      (lt_of_lt_of_le (Nat.lt_of_succ_le hD1) hDd)
    have h2 := facts.gr.q10_early_g2_le_early_g1 S (M.round_of S.hc d)
    have h3 : lo ≤ M.a S.hc S.E.Δ rGST := hloPost
    linarith
  have hwinStart : lo ≤ M.early S.E S.hc (M.round_of S.hc start) .g1 - S.E.Δ := by
    rw [hstartdef, facts.gr.round_of_opening_slot_eq S.hc m]
    have h1 := Restated.lo_le_early_g2_sub_delta_of_action_lt facts S hloPost
      (lt_of_lt_of_le hrm1 (Nat.sub_le m 1))
    have h2 := facts.gr.q10_early_g2_le_early_g1 S m
    linarith
  have hrunP : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick (S.E.proposer start)
      (M.proposal_time S.E start)) →
      M.awake_for_grade1 S (S.E.proposer start) (W j (S.E.proposer start)) (M.round_of S.hc start) :=
    fun j hj => hf.awake_g1 _ _ j _ (Or.inl rfl) hj
      (hHs _ _ (facts.sch.proposal_time_le_confirmation_time S.E start) hpropConf) hwinStart
  have hex := fun w : V => exists_headOutcome₈₆g facts S
    (W (strictEventIndex rho (M.vote_time S.E d)) w) (M.vote_time S.E d)
  choose head hheadAll using hex
  obtain ⟨E, hErun, hEheads, hEmax, hupper, hEparent, hsourceAnchor, hsourceBandσ⟩ :=
    Restated.openingPivot_afterDeadlineOn facts S Hs Xb hf hHs hHsXb hcom hbelow hrec hdelay
      hpost hm hhor hopening cp hcp hP hloPost hloOpen ht₀ hAll head (fun w _ => hheadAll w)
  have hreadBound : ∀ {read : Time}, (Restated.Vocabulary.Execution.Setup.a M S D) ≤ read →
      read ≤ rho.horizon → read ≤ M.confirmation_time S.E d → ∀ {u : V}, u ∈ Hs read →
      Block.Preceq
        (M.get_fg_root (M.toHealing (W (strictEventIndex rho read) u).st.core).toFG) E.erase := by
    intro read hread hreadHor hnext u hu
    apply hEmax
    intro w hw
    obtain ⟨c, hc, T, hT, L, hL, L', hL', hH⟩ := hheadAll w
    exact Restated.fgRoot_preceq_previousHead_through_confirmation_after_GSTOn facts S Hs Xb hf
      hHs hHsXb hcom hbelow hrec hdelay hpost hread hreadHor hdeadlineSlot hnext hprevDelta
      hu hloPost hloOpen ht₀ hA w hw c hc T hT L hL L' hL' (head w) hH
  have hcone : Restated.NamedHonestVotesConeOn M S rho W Hs Xb d
      (fun X => Block.Preceq E.erase X) := by
    intro x hx hcommittee
    obtain ⟨c, hc, T, hT, L, hL, L', hL', hH⟩ := hheadAll x
    obtain ⟨X, hXhead, hXrun, hXemit⟩ :=
      Restated.named_voter_head_emitsOn facts S Hs Xb hf hHsXb hx hdPos hcommittee
        hprevVoteHor hloVoteD c hc
        (fun j hj => hf.awake_g1 _ _ j _ (Or.inr rfl) hj hx hwinD) T hT L hL L' hL' (head x) hH
    exact ⟨X, by rw [hXhead]; exact hEheads x hx, hXrun, hXemit⟩
  have hcut : Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ m ≤ rho.horizon := by
    unfold Restated.Vocabulary.Protocol.HealConfig.Γ_neg1
    rw [facts.sch.Γ_0_eq_proposal_time S.hc S.E m]
    linarith
  have hpostPrev : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (m - 1)) :=
    hloD.trans ((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone
      (hcDeadline.trans (Nat.sub_le (m - 1) 1)))
  have hroundStart : (M.round_of S.hc (d + 1)) = m - 1 + 1 := by
    rw [hdSucc, hqEq, hstartdef]
    exact facts.gr.round_of_opening_slot_eq_schedule S.hc m
  intro v hv cv hcv mv T₀ hT₀ I hI
  have hmvst : mv.st = M.store_with_cache (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E start)) v).st (M.vote_time S.E start)) _ := facts.nd.mkNode_st _ _ _
  have hmvbodies : mv.st.bodies = (M.ns_setClock S.E
      (W (strictEventIndex rho (M.vote_time S.E start)) v).st (M.vote_time S.E start)).bodies :=
    (facts.nd.mkNode_st _ _ _).symm ▸ facts.nd.store_with_cache_bodies _ _
  have hmvread : mv ∈ Restated.Vocabulary.Internal.NamedRecoveryRead.voteDutyRead M S rho v start :=
    (p58% mkNode_mem_confirmationReadAt₅₈) hf.sorted hf.onePath _ _ cv hcv
  have hσmv : ∀ X : Block V, mv.st.core.σ X =
      (W (strictEventIndex rho (M.vote_time S.E start)) v).st.core.σ X := by
    intro X
    rw [hmvst]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    rw [facts.hd.Sts_setClock_core_σ]
  have hhmaxmv : mv.st.core.h_max =
      (W (strictEventIndex rho (M.vote_time S.E start)) v).st.core.h_max := by
    rw [hmvst]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    rw [facts.hd.setClock_core_h_max]
  have hI' : Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract pn.cache) S.E S.hc
      (S.node (S.E.proposer start)) (M.toHealing pn.st.core) ⇢ I := by
    rw [hpncache]
    exact hI
  obtain ⟨Parent, hParent, hParentErase⟩ :=
    Restated.Vocabulary.Proofs.HealingSurface.proposedBlockAt_parent facts S rho start pn hpread hPn
      I hI'
  have hEParent : Block.Preceq E.erase Parent.erase := by
    rw [hParentErase]
    exact hEparent I hI
  obtain ⟨hparOpt, hIP⟩ := (p58% parent_preceq_of_proposal₅₈s) facts S rho start pn hpread hPn I hI'
  have hEP : Block.Preceq E.erase P.erase := preceq_trans_Preceq (hEparent I hI) hIP
  have hPrun : Restated.RunBlockOn M S rho W Xb P :=
    Restated.proposedBlock_runBlockOn facts S Hs Xb hf hHs hHsXb hstartPos hpropConf hproposalHor
      hloProposal (fun j hj => hf.tick_outcome j _ _ hj) hrunP cp hcp hPclock
  have hrootW : ∀ w ∈ Hs (M.vote_time S.E start), Block.Preceq
      (M.get_fg_root (M.toHealing
        (W (strictEventIndex rho (M.vote_time S.E start)) w).st.core).toFG) E.erase :=
    fun w hw => hreadBound hdeadlineVote hhor hvoteNext hw
  have hFhist : ∀ w ∈ Hs (M.vote_time S.E start),
      ∀ i : Nat, i ≤ (rho.events.filter (fun e => decide (e.time < M.vote_time S.E start))).length →
        Block.Preceq (W i w).st.core.F P.erase := by
    intro w hw i hi
    have hi' : i ≤ strictEventIndex rho (M.vote_time S.E start) := hi
    exact Restated.Vocabulary.Proofs.finalized_preceq_at_prefix_of_storeBeforeRoot_preceq facts S rho
      hf.sorted (w := w) hi' (W i) (hf.onePath i).1 _ ((p55% onePath_slice₅₅b) W hf.onePath hi')
      (preceq_trans_Preceq (hrootW w hw) hEP)
  have hadmit := Restated.proposedBlock_admittedBefore_vote_after_gstOn facts S Hs Xb hf hHs
    hHsXb hstartPos hpropConf hloProposal hhor cp hcp hPclock hFhist hrunP
  obtain ⟨Tt, hTtrun, hTtband, hTtheads⟩ :=
    (p86f% exists_namedCommonPreviousHeadAncestor_in_frontierBand_after_GSTOn₈₆f) facts S Hs Xb
      hf hHs hHsXb hcom hbelow hrec hdelay hpost hdeadlineVote hhor hdeadlineSlot hvoteNext
      hprevDelta hv hloPost hloOpen ht₀ hA
  have hTtE : Block.Preceq Tt.erase E.erase := by
    apply hEmax
    intro w hw
    obtain ⟨c, hc, T, hT, L, hL, L', hL', hH⟩ := hheadAll w
    exact hTtheads w hw c hc T hT L hL L' hL' (head w) hH
  have hTtP : Block.Preceq Tt.erase P.erase := preceq_trans_Preceq hTtE hEP
  have hTtPNamed : NamedBlock.Preceq Tt P :=
    Restated.namedPreceq_of_runBlock_erase_preceqOn facts Hs Xb hf hTtrun hPrun hTtP
  have hTtENamed : NamedBlock.Preceq Tt E :=
    Restated.namedPreceq_of_runBlock_erase_preceqOn facts Hs Xb hf hTtrun hErun hTtE
  have hmemV := (p64b% mem_stateBeforeTime_along₆₄b) hf.sorted hf.onePath (M.vote_time S.E start)
  have hPmem0 : P.erase ∈ (W (strictEventIndex rho (M.vote_time S.E start)) v).st.core.T :=
    (Restated.admittedBefore_mem_and_stamp_atOn facts S Hs Xb hf (hadmit v hv) (le_refl _)).1
  have hPbody := Restated.namedBody_of_mem_storeBeforeTime_l86f facts S Hs Xb hf (hHsXb _ hv)
    hPmem0 hPrun
  have hPview := Restated.Vocabulary.Proofs.NamedStoreBridge.derivedView_stateBeforeTime facts S rho
    (M.vote_time S.E start) v _ hmemV P hPbody
  have hPbandmv : mv.st.core.h_max - 1 ≤ (mv.st.core.σ P.erase).h := by
    rw [hσmv, hhmaxmv, hPview]
    exact hTtband.trans (facts.cs.derive_height_mono S.E S.cfg hTtPNamed)
  have hEmem0 : E.erase ∈ (W (strictEventIndex rho (M.vote_time S.E start)) v).st.core.T := by
    have hpc := Restated.Vocabulary.Proofs.NamedStoreBridge.parentClosed_stateBeforeTime facts S rho
      (M.vote_time S.E start) v _ hmemV
    unfold Restated.Vocabulary.Internal.ParentClosed Record.Model.GS.parent_closed at hpc
    rw [facts.sto.toHealing_gs_T] at hpc
    exact Proofs.Records.mem_of_preceq hpc.2 E.erase P.erase hPmem0
      (preceq_eq_true_iff_Preceq.2 hEP)
  have hEbody0 := Restated.namedBody_of_mem_storeBeforeTime_l86f facts S Hs Xb hf (hHsXb _ hv)
    hEmem0 hErun
  have hEview := Restated.Vocabulary.Proofs.NamedStoreBridge.derivedView_stateBeforeTime facts S rho
    (M.vote_time S.E start) v _ hmemV E hEbody0
  have hEbody : E ∈ mv.st.bodies := by
    rw [hmvbodies, facts.hd.Sts_setClock_bodies]
    exact hEbody0
  have hEband : mv.st.core.h_max - 1 ≤ (M.derive_named S.E S.cfg E).h := by
    rw [hhmaxmv]
    exact hTtband.trans (facts.cs.derive_height_mono S.E S.cfg hTtENamed)
  have hEmemv : E.erase ∈ mv.st.core.T := by
    rw [hmvst]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    rw [facts.hd.Sts_setClock_core_T]
    exact hEmem0
  have hrootmv : Block.Preceq (M.get_fg_root (M.toHealing mv.st.core).toFG) E.erase := by
    rw [hmvst]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    rw [(p60% setClock_fgRoot₆₀) facts S]
    exact hrootW v hv
  have hne : E.erase ≠ P.erase := by
    intro heq
    have hdepth := Block.preceq_depth_le (preceq_eq_true_iff_Preceq.2 (hEparent I hI))
    have hstrict := Protocol.depth_of_parent? hparOpt
    rw [heq] at hdepth
    omega
  have hvFreeze : v ∈ Hs (M.view_freeze S.E d) :=
    hHs _ _ (by linarith) hv
  have hint := Restated.interiorProposal_candidateAndPivotPathOn facts S Hs Xb hf hstartPos
    (v := v) hvFreeze hloFreezeD cp hcp hP hParent (hadmit v hv)
    (by have h := hPbandmv; rw [hmvst] at h; (try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at h); rw [← (p60% voteStore_eq₆₀s) facts S] at h; exact h) (by have h := hrootmv; rw [hmvst] at h; (try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at h); rw [← (p60% voteStore_eq₆₀s) facts S] at h; exact h) hEParent hne cv hcv
  have hanchor : ∀ A0 : Block V,
      Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S mv (M.round_of S.hc mv.st.core.s) ⇢ A0 →
      Block.Preceq A0 E.erase := by
    have h := Restated.voterAnchorAt_preceq_of_previousCarriersOn facts S Hs Xb hf hHs hHsXb
      hbelow (q := m - 1) (s := d) hroundStart hpostPrev (by rw [hqEq]; exact hcut)
      (by rw [hdSucc]; exact hhor) hupper (w := v) (by rw [hdSucc]; exact hv)
      (by rw [hdSucc]; have h := hrootmv; rw [hmvst] at h; (try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at h); rw [← (p60% voteStore_eq₆₀s) facts S] at h; exact h) (hA (m - 1) hkM1) cv (by rw [hdSucc]; exact hcv)
    rw [hdSucc] at h
    exact h
  obtain ⟨A0, hA0⟩ := (p58% nodeAnchor_outcome₅₈) facts S mv (M.round_of S.hc mv.st.core.s)
  have hcandT : ∀ T : Finset (Block V),
      M.voter_filtered_block_tree S.E mv.st.core mv.st.core.s ⇢ T → P.erase ∈ T :=
    fun T hT => (hint A0 hA0 T hT).1
  have hghost0 := Restated.pivot_preceq_proposalFreeHead_bandOn facts S Hs Xb hf hHs hHsXb
    hcom hdPos hloVoteD hsupportHor (v := v) (A := E) (B := P)
    (by rw [hdSucc]; exact hv) cp (by rw [hdSucc]; exact hcp) (by rw [hdSucc]; exact hP) hcone
    cv (by rw [hdSucc]; exact hcv) (A0 := A0) (by rw [hdSucc]; exact hA0) (hanchor A0 hA0)
    (by rw [hdSucc]; exact hEbody) (by rw [hdSucc]; exact hEband) (I := I)
    (by rw [hdSucc]; exact hI) (hEparent I hI)
  rw [hdSucc] at hghost0
  have hFJ : Block.Preceq mv.st.core.F mv.st.core.J := by
    rw [hmvst]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    rw [facts.hd.setClock_core_F, facts.hd.setClock_core_J]
    exact Restated.Vocabulary.Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime facts
      S rho (M.vote_time S.E start) v _ hmemV
  have hproposalFiltered : P.erase ∈ M.get_filtered_block_tree (M.toHealing mv.st.core).toFG :=
    facts.fc.voter_filtered_block_tree_subset_filtered S.E mv.st.core T₀ hT₀ (hcandT T₀ hT₀)
  have hpivotFiltered : E.erase ∈ M.get_filtered_block_tree (M.toHealing mv.st.core).toFG :=
    facts.fc.mem_filtered_of_preceq (st := (M.toHealing mv.st.core).toFG)
      (by rw [facts.sto.Sts_toHealing_F, facts.sto.Sts_toHealing_J]; exact preceq_eq_true_iff_Preceq.2 hFJ)
      hproposalFiltered (by rw [facts.sto.toHealing_gs_T]; exact hEmemv)
      (preceq_eq_true_iff_Preceq.2 hEP) (preceq_eq_true_iff_Preceq.2 hrootmv)
  have hcoreInputs : Restated.Vocabulary.Proofs.HealingSurface.NamedFrozenProposalSuffixCoreInputs M
      S rho start E.erase v P pn mv :=
    { sourceAnchor := hsourceAnchor
      pivotTarget := hpivotFiltered
      proposalCandidate := hcandT
      pivotAnchorCompatible := fun A hA =>
        compatible_of_preceq_common_Preceq (hanchor A hA)
          (Proofs.ModelProperties.Preceq_self E.erase)
      proposalAnchorCompatible := fun A hA =>
        compatible_of_preceq_common_Preceq (preceq_trans_Preceq (hanchor A hA) hEP)
          (Proofs.ModelProperties.Preceq_self P.erase) }
  have htargetBandσ : (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E start)) v).st.core start).h_max - 1 ≤
      ((Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E start)) v).st.core start).σ E.erase).h := by
    rw [(p60% voteStore_eq₆₀s) facts S, facts.hd.setClock_core_h_max, facts.hd.Sts_setClock_core_σ, hEview]
    exact hTtband.trans (facts.cs.derive_height_mono S.E S.cfg hTtENamed)
  have hsuffix := Restated.namedProposalPivotSuffixTransfer_of_pivotBandOn facts S Hs Xb hf
    hHs hHsXb hstartPos hloProposalD hpropVote hv hhor cp hcp hPn cv hcv hcoreInputs hsourceBandσ
    htargetBandσ
  have hscoreBridge := Restated.namedProposalCandidateScoreBridge_afterGSTOn facts S Hs Xb hf
    hHs hHsXb hstartPos hloProposalD hpropVote hv hhor cp hcp hPn
    (by have h := hproposalFiltered; rw [hmvst] at h; (try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at h); rw [← (p60% voteStore_eq₆₀s) facts S] at h; exact h)
  have hscoreBridge' : Restated.Vocabulary.Proofs.HealingSurface.NamedProposalCandidateScoreBridge M
      S rho start v P pn pn.st.core mv.st.core := by
    rw [hpncore, hmvst]
    apply scoreBridge_store_with_cache₈₆g facts
    rw [← (p60% voteStore_eq₆₀s) facts S, ← (p86f% tickStore_eq₈₆f) facts]
    exact hscoreBridge
  have hscore : ∀ psv : List (GoldfishVote V),
      M.proposer_support_view (M.toHealing pn.st.core).toFG.toSG.toGoldfishStore pn.st.core.s ⇢ psv →
      ∀ srcScore : Block V → ℕ,
        (∀ B : Block V, M.goldfish_score S.E pn.st.core.T
          (M.proposer_view (M.toHealing pn.st.core).toFG.toSG.toGoldfishStore pn.st.core.s).toFinset
          psv.toFinset (pn.st.core.s - 1) B ⇢ srcScore B) →
      ∀ vv : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing mv.st.core).toFG.toSG.toGoldfishStore mv.st.core.s ⇢ vv →
      ∀ vsv : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing mv.st.core).toFG.toSG.toGoldfishStore mv.st.core.s ⇢ vsv →
      ∀ tgtScore : Block V → ℕ,
        (∀ B : Block V, M.goldfish_score S.E mv.st.core.T vv vsv (mv.st.core.s - 1) B ⇢ tgtScore B) →
      ∀ C' : Block V, C' ∈ M.get_filtered_block_tree (M.toHealing pn.st.core).toFG →
        C' ∈ T₀.erase P.erase → tgtScore C' = srcScore C' := by
    intro psv hpsv srcScore hsrc vv hvv vsv hvsv tgtScore htgt C' hC'n hC'T
    exact Restated.Vocabulary.Proofs.HealingSurface.carrierInterior_scoreEq_of_scoreBridge facts S
      (rho := rho) (s := start) (v := v) (P := P) pn hpread mv hmvread hPn hscoreBridge' C' hC'n
      T₀ hT₀ hC'T vv hvv vsv hvsv psv hpsv _ (htgt C') _ (hsrc C')
  have hcompat : Block.compatible A0 P.erase = true :=
    compatible_of_preceq_common_Preceq (preceq_trans_Preceq (hanchor A0 hA0) hEP)
      (Proofs.ModelProperties.Preceq_self P.erase)
  obtain ⟨R, hR⟩ := facts.fc.get_sg_root_with_nonempty (M.gradeContract pn.cache) S.E S.hc
    (M.toHealing pn.st.core) (M.round_of S.hc pn.st.core.s)
  have hRE : Block.Preceq R E.erase :=
    hsourceAnchor R ((p60% nodeAnchor_of_sgRoot₆₀s) facts S pn _ hR)
  exact Restated.namedProposalWalkTransferred_of_frozenCompatiblePivotOn facts S Hs Xb hf
    (s := start) (pivot := E.erase) (hHsXb _ hpropVote) (hHsXb _ hv) cp hcp cv hcv hPn
    T₀ hT₀ (hcandT T₀ hT₀) A0 hA0 hcompat R hR hRE I hI' (hEparent I hI)
    (fun vv hvv vsv hvsv sc hsc el hel G hG => hghost0 T₀ hT₀ vv hvv vsv hvsv sc hsc el hel G hG)
    hsuffix hscore

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
open DecoupledConsensusModel.Statements.Instantiation

/-- For a round `m` at least two rounds after the progress deadline whose opening proposer is in the
    set and proposes `P` along `W`, with `S.a m` in the horizon: at every confirmation read of the
    opening slot by a member of the set for `S.a m`, the FG root and every confirmation anchor are
    ancestors of `P`, and `P` is in the confirmation candidate tree. -/
theorem openingProposal_confirmationRead_afterDeadlineOn (facts : Record.Facts M)
    {delayExtra : Nat}
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hbelow : BelowOneThirdOn S rho Hs)
    {rGST gap : Round} {t₀ : Int} (hrec : Restated.MultiProposerRecurrenceOn M S Hs gap t₀ rho.horizon)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    {m : Round} (hm : fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ m)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S m) ≤ rho.horizon)
    (hopening : S.E.proposer ((M.opening_slot S.hc m)) ∈
      Hs (M.confirmation_time S.E ((M.opening_slot S.hc m))))
    {P : NamedBlock V}
    (cp : M.Cache)
    (hcp : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
        (S.E.proposer (M.opening_slot S.hc m))).st.core.toHealing
      (M.proposal_time S.E (M.opening_slot S.hc m))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
        (S.E.proposer (M.opening_slot S.hc m))).cache ⇢ cp)
    (hP : M.proposal_with (M.gradeContract cp) .poolAndCarried S.E S.hc
      (S.node (S.E.proposer (M.opening_slot S.hc m)))
      (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
          (S.E.proposer (M.opening_slot S.hc m))).st
        (M.proposal_time S.E (M.opening_slot S.hc m)))
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
          (S.E.proposer (M.opening_slot S.hc m))).record cp).st ⇢ some P)
    (hloPost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    (hloOpen : lo ≤ M.opening S.E S.hc (rGST + 2 - S.hc.η_SG))
    (ht₀ : t₀ ≤ (Restated.Vocabulary.Execution.Setup.a M S (rGST + 2)))
    (hAll : ∀ (k : Round) (u : V), lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → u ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S k) → ∀ (j : Nat), rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S m)), ∀ cc : M.Cache,
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc m))) v).st.core.toHealing
        (M.confirmation_time S.E (M.opening_slot S.hc m))
        (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc m))) v).cache ⇢ cc →
      let n := M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc m))) v).st
          (M.confirmation_time S.E (M.opening_slot S.hc m)))
        (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc m))) v).record cc
      Block.Preceq (M.get_fg_root (M.toHealing n.st.core).toFG) P.erase ∧
        (∀ A, Restated.Vocabulary.Internal.namedConfirmationAnchor M S n ⇢ A →
          Block.Preceq A P.erase) ∧
        P.erase ∈ Restated.Vocabulary.Protocol.confTree M n.st.core := by
  classical
  have hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ →
      ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat,
      rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) →
      M.awake_for_grade2 S u (W j u) k :=
    fun k hk u hu => hAll k u hk (hHs _ _ (le_add_of_nonneg_right S.E.Δ_pos.le) hu)
  obtain ⟨hdeadlineSlot, hdeadlineTwo, _hinterior, hdPos, hdSucc, hcEq, hqEq, hcDeadline,
    _hdeadlineTwoD⟩ := facts.gr.openingSlots_l86f S hm
  have hconfA : M.confirmation_time S.E (M.opening_slot S.hc m) =
      (Restated.Vocabulary.Execution.Setup.a M S m) :=
    (Restated.Vocabulary.Protocol.a_eq_confirmation_time facts S.hc S.E m).symm
  have hround : (M.round_of S.hc ((M.opening_slot S.hc m) + 1)) = m - 1 + 1 := by
    rw [hqEq]
    exact facts.gr.HealingLemmas_round_of_opening_succ S.hc m
  set D := fgSafetyProgressDeadline S rho rGST gap delayExtra with hDdef
  set start := (M.opening_slot S.hc m) with hstartdef
  set wp := W (strictEventIndex rho (M.proposal_time S.E start)) (S.E.proposer start) with hwpdef
  set pn := M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E start)) wp.record cp
    with hpndef
  have hpnst : pn.st = M.store_with_cache (M.ns_setClock S.E wp.st (M.proposal_time S.E start)) cp :=
    facts.nd.mkNode_st _ _ _
  have hpncache : pn.cache = cp := facts.nd.mkNode_cache _ _ _
  have hpread : pn ∈ Restated.Vocabulary.Statements.Instantiation.proposerReadAt M S rho start :=
    (p58% mkNode_mem_confirmationReadAt₅₈) hf.sorted hf.onePath _ _ cp hcp
  have hPn : M.proposal_with (M.gradeContract pn.cache) .poolAndCarried S.E S.hc
      (S.node (S.E.proposer start)) pn.st ⇢ some P := by
    rw [hpncache]
    exact hP
  have hPclock : M.proposal_with (M.gradeContract cp)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc (S.node (S.E.proposer start))
      (M.ns_setClock S.E wp.st (M.proposal_time S.E start)) ⇢ some P := by
    have h := hP
    rw [hpnst, facts.dt.proposal_with_store_with_cache] at h
    exact h
  obtain ⟨hi1, hi2, hi3, hi4, hi5, hi6⟩ := facts.sch.slot_instants_l55 S.E start
  have hΔ := S.E.Δ_pos
  have hconfHor : M.confirmation_time S.E start ≤ rho.horizon := by rw [hconfA]; exact hhor
  have hvoteHor : M.vote_time S.E start ≤ rho.horizon := by linarith
  have hvoteDelta : M.vote_time S.E start + S.E.Δ ≤ rho.horizon := by linarith
  have hproposalHor : M.proposal_time S.E start ≤ rho.horizon := by linarith
  have hvoteConf : M.vote_time S.E start ≤ M.confirmation_time S.E start :=
    facts.sch.Protocol_vote_time_le_confirmation_time S.E start
  have hGSTdead : rGST ≤ D := by
    rw [hDdef]
    unfold fgSafetyProgressDeadline
    exact (Nat.le_succ rGST).trans (Nat.le_add_right _ _)
  have hdeadlineProposal : (Restated.Vocabulary.Execution.Setup.a M S D) ≤ M.proposal_time S.E start :=
    (Restated.Vocabulary.Protocol.action_lt_proposal_time_two_after facts S D).le.trans
      (facts.sch.proposal_time_mono S.E hdeadlineTwo)
  have hdeadlineVote : (Restated.Vocabulary.Execution.Setup.a M S D) ≤ M.vote_time S.E start := by
    linarith
  have hdeadlineRead : (Restated.Vocabulary.Execution.Setup.a M S D) ≤ M.confirmation_time S.E start := by
    linarith
  have hstartSlot : (M.opening_slot S.hc D) + 1 ≤ start :=
    hdeadlineSlot.trans (Nat.sub_le start 1)
  have hloD : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S D) :=
    hloPost.trans ((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone hGSTdead)
  have hloProposal : lo ≤ M.proposal_time S.E start := hloD.trans hdeadlineProposal
  have hstartPos : 0 < start := lt_of_lt_of_le hdPos (Nat.sub_le start 1)
  have hpropConf : S.E.proposer start ∈ Hs (M.confirmation_time S.E start) := hopening
  have hcut : Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ m ≤ rho.horizon := by
    unfold Restated.Vocabulary.Protocol.HealConfig.Γ_neg1
    rw [facts.sch.Γ_0_eq_proposal_time S.hc S.E m]
    linarith
  have hpostPrev : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (m - 1)) :=
    hloD.trans ((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone
      (hcDeadline.trans (Nat.sub_le (m - 1) 1)))
  have hrm1 : rGST < m - 1 := by
    rw [← hcEq]; exact Nat.lt_succ_of_le (hGSTdead.trans hcDeadline)
  have hkM1 : lo ≤ M.early S.E S.hc (m - 1) .g2 - S.E.Δ :=
    Restated.lo_le_early_g2_sub_delta_of_action_lt facts S hloPost hrm1
  have hwinStart : lo ≤ M.early S.E S.hc (M.round_of S.hc start) .g1 - S.E.Δ := by
    rw [hstartdef, facts.gr.round_of_opening_slot_eq S.hc m]
    have h1 := Restated.lo_le_early_g2_sub_delta_of_action_lt facts S hloPost
      (lt_of_lt_of_le hrm1 (Nat.sub_le m 1))
    have h2 := facts.gr.q10_early_g2_le_early_g1 S m
    linarith
  have hrunP : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick (S.E.proposer start)
      (M.proposal_time S.E start)) →
      M.awake_for_grade1 S (S.E.proposer start) (W j (S.E.proposer start)) (M.round_of S.hc start) :=
    fun j hj => hf.awake_g1 _ _ j _ (Or.inl rfl) hj
      (hHs _ _ (facts.sch.proposal_time_le_confirmation_time S.E start) hpropConf) hwinStart
  obtain ⟨I, hI⟩ := facts.dt.with_proposal_input_nonempty (M.gradeContract cp) S.E S.hc
    (S.node (S.E.proposer start)) (M.toHealing pn.st.core)
  have hI' : Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract pn.cache) S.E S.hc
      (S.node (S.E.proposer start)) (M.toHealing pn.st.core) ⇢ I := by
    rw [hpncache]
    exact hI
  obtain ⟨-, hIP⟩ := (p58% parent_preceq_of_proposal₅₈s) facts S rho start pn hpread hPn I hI'
  have hsgParent := actionSGBlock_preceq_proposedParent_afterDeadlineOn₈₆g facts S Hs Xb hf
    hHs hHsXb hcom hbelow hrec hdelay hpost hm hvoteHor hopening cp hcp hP hloPost hloOpen ht₀ hAll
  have hupperP : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (m - 1))),
      ∀ nu ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (m - 1))) u) (m - 1),
      ∀ g, M.grade2_block_with (M.gradeContract nu.cache) S.E S.hc (M.toHealing nu.st.core)
          (M.round_of S.hc (M.toHealing nu.st.core).s) ⇢ g →
      ∀ B, M.get_sg_vote_with (M.gradeContract nu.cache) S.E S.hc (M.toHealing nu.st.core)
          (M.round_of S.hc (M.toHealing nu.st.core).s) g ⇢ B →
        Block.Preceq B P.erase :=
    fun u hu nu hnu g hg B hB => preceq_trans_Preceq (hsgParent u hu nu hnu g hg B hB I hI) hIP
  have hstores := Restated.openingProposal_voteStoreExtends_afterDeadlineOn facts S Hs Xb hf
    hHs hHsXb hcom hbelow hrec hdelay hpost hm hvoteHor hopening cp hcp hP hloPost hloOpen ht₀ hAll
  have hrootVote : ∀ w ∈ Hs (M.vote_time S.E start), Block.Preceq
      (M.get_fg_root (M.toHealing
        (W (strictEventIndex rho (M.vote_time S.E start)) w).st.core).toFG) P.erase := by
    intro w hw
    obtain ⟨Hd, cw, hcw, Tr, hTr, L, hL, L', hL', hHd⟩ := exists_headOutcome₈₆g facts S
      (W (strictEventIndex rho (M.vote_time S.E start)) w) (M.vote_time S.E start)
    have hHdP : Hd = P.erase :=
      (hstores w hw cw hcw Tr hTr I hI).head Tr hTr L hL L' hL' Hd hHd
    have h := Restated.fgRoot_preceq_previousHead_through_confirmation_after_GSTOn facts S Hs Xb hf
      hHs hHsXb hcom hbelow hrec hdelay hpost hdeadlineVote hvoteHor hstartSlot hvoteConf
      hvoteDelta hw hloPost hloOpen ht₀ hA w hw cw hcw Tr hTr L hL L' hL' Hd hHd
    rw [hHdP] at h
    exact h
  have hadmit := Restated.proposedBlock_admittedBefore_vote_after_gstOn facts S Hs Xb hf hHs
    hHsXb hstartPos hpropConf hloProposal hvoteHor cp hcp hPclock (by
      intro w hw i hi
      have hi' : i ≤ strictEventIndex rho (M.vote_time S.E start) := hi
      exact Restated.Vocabulary.Proofs.finalized_preceq_at_prefix_of_storeBeforeRoot_preceq facts S
        rho hf.sorted (w := w) hi' (W i) (hf.onePath i).1 _
        ((p55% onePath_slice₅₅b) W hf.onePath hi') (hrootVote w hw)) hrunP
  have hPrun : Restated.RunBlockOn M S rho W Xb P :=
    Restated.proposedBlock_runBlockOn facts S Hs Xb hf hHs hHsXb hstartPos hpropConf hproposalHor
      hloProposal (fun j hj => hf.tick_outcome j _ _ hj) hrunP cp hcp hPclock
  intro v hv cc hcc n
  have hvConf : v ∈ Hs (M.confirmation_time S.E start) := by rw [hconfA]; exact hv
  have hvVote : v ∈ Hs (M.vote_time S.E start) := hHs _ _ hvoteConf hvConf
  obtain ⟨Hd, cw, hcw, Tr, hTr, L, hL, L', hL', hHd⟩ := exists_headOutcome₈₆g facts S
    (W (strictEventIndex rho (M.vote_time S.E start)) v) (M.vote_time S.E start)
  have hHdP : Hd = P.erase :=
    (hstores v hvVote cw hcw Tr hTr I hI).head Tr hTr L hL L' hL' Hd hHd
  have hrootHead : Block.Preceq
      (M.get_fg_root (M.toHealing
        (W (strictEventIndex rho (M.confirmation_time S.E start)) v).st.core).toFG) P.erase := by
    have h := Restated.fgRoot_preceq_previousHead_through_confirmation_after_GSTOn facts S Hs Xb hf
      hHs hHsXb hcom hbelow hrec hdelay hpost hdeadlineRead hconfHor hstartSlot (le_refl _)
      hvoteDelta hvConf hloPost hloOpen ht₀ hA v hvVote cw hcw Tr hTr L hL L' hL' Hd hHd
    rw [hHdP] at h
    exact h
  have hnst : n.st = M.store_with_cache (M.ns_setClock S.E (W (strictEventIndex rho (M.confirmation_time S.E start)) v).st (M.confirmation_time S.E start)) _ := facts.nd.mkNode_st _ _ _
  have hroot : Block.Preceq (M.get_fg_root (M.toHealing n.st.core).toFG) P.erase := by
    rw [hnst]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    rw [(p60% setClock_fgRoot₆₀) facts S]
    exact hrootHead
  have hrootConf : Block.Preceq
      (Restated.Vocabulary.Protocol.confRoot M
        (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.confirmation_time S.E start)) v).st.core
          (M.confirmation_time S.E start)))
      P.erase := by
    show Block.Preceq (M.get_fg_root (M.toHealing
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.confirmation_time S.E start)) v).st.core
        (M.confirmation_time S.E start))).toFG) P.erase
    rw [(p86f% tickStore_eq₈₆f) facts, (p60% setClock_fgRoot₆₀) facts S]
    exact hrootHead
  have hmemC := (p64b% mem_stateBeforeTime_along₆₄b) hf.sorted hf.onePath
    (M.confirmation_time S.E start)
  have hPmemC : P.erase ∈
      (W (strictEventIndex rho (M.confirmation_time S.E start)) v).st.core.T :=
    (Restated.admittedBefore_mem_and_stamp_atOn facts S Hs Xb hf (hadmit v hvVote) hvoteConf).1
  have hPbody := Restated.namedBody_of_mem_storeBeforeTime_l86f facts S Hs Xb hf (hHsXb _ hvConf)
    hPmemC hPrun
  have hPview := Restated.Vocabulary.Proofs.NamedStoreBridge.derivedView_stateBeforeTime facts S rho
    (M.confirmation_time S.E start) v _ hmemC P hPbody
  obtain ⟨T, hTrun, hTband, hTheads⟩ :=
    (p86f% exists_namedCommonPreviousHeadAncestor_in_frontierBand_after_GSTOn₈₆f) facts S Hs Xb
      hf hHs hHsXb hcom hbelow hrec hdelay hpost hdeadlineRead hconfHor hstartSlot (le_refl _)
      hvoteDelta hvConf hloPost hloOpen ht₀ hA
  have hTP : Block.Preceq T.erase P.erase := by
    have h := hTheads v hvVote cw hcw Tr hTr L hL L' hL' Hd hHd
    rw [hHdP] at h
    exact h
  have hTPNamed : NamedBlock.Preceq T P :=
    Restated.namedPreceq_of_runBlock_erase_preceqOn facts Hs Xb hf hTrun hPrun hTP
  have hFJ0 := Restated.Vocabulary.Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
    facts S rho (M.confirmation_time S.E start) v _ hmemC
  have hFroot : Block.Preceq
      (W (strictEventIndex rho (M.confirmation_time S.E start)) v).st.core.F
      (M.get_fg_root (M.toHealing
        (W (strictEventIndex rho (M.confirmation_time S.E start)) v).st.core).toFG) := by
    have hFJ' : Block.preceq
        (M.toHealing (W (strictEventIndex rho (M.confirmation_time S.E start)) v).st.core).toFG.F
        (M.toHealing (W (strictEventIndex rho (M.confirmation_time S.E start)) v).st.core).toFG.J
          = true := by
      rw [facts.sto.Sts_toHealing_F, facts.sto.Sts_toHealing_J]
      exact preceq_eq_true_iff_Preceq.2 hFJ0
    have h := preceq_eq_true_iff_Preceq.1 (facts.fc.preceq_get_fg_root_of_F hFJ')
    rw [facts.sto.Sts_toHealing_F] at h
    exact h
  refine ⟨hroot, ?_, ?_⟩
  · exact Restated.confirmationAnchorAt_preceq_of_previousCarriersOn facts S Hs Xb hf hHs
      hHsXb hbelow (q := m - 1) (s := start) hround hpostPrev (by rw [hqEq]; exact hcut) hconfHor
      hupperP (w := v) hvConf hrootConf (hA (m - 1) hkM1) cc hcc
  · show P.erase ∈ M.get_filtered_block_tree (M.toHealing n.st.core).toFG
    refine facts.fc.mem_get_filtered_block_tree_of_parts (M.toHealing n.st.core) (C := P.erase)
      (W := P.erase) ?_ ?_ ?_ (Proofs.ModelProperties.Preceq_self _) ?_ hroot
    · rw [facts.sto.toHealing_gs_T, hnst]
      try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
      rw [facts.hd.Sts_setClock_core_T]
      exact hPmemC
    · rw [facts.sto.Sts_toHealing_F, hnst]
      try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
      rw [facts.hd.setClock_core_F]
      exact preceq_trans_Preceq hFroot hrootHead
    · rw [facts.sto.toHealing_gs_T, hnst]
      try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
      rw [facts.hd.Sts_setClock_core_T]
      exact hPmemC
    · rw [facts.sto.Sts_toHealing_h_max, facts.sto.Sts_toHealing_σ, hnst,
        facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_σ,
        facts.hd.setClock_core_h_max, facts.hd.Sts_setClock_core_σ, hPview]
      exact hTband.trans (facts.cs.derive_height_mono S.E S.cfg hTPNamed)

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
open DecoupledConsensusModel.Statements.Instantiation

/-- For a round `m` at least two rounds after the progress deadline, with `S.a m` in the horizon,
    whose opening proposer is in the set and proposes `P` along `W`: every member of the set for the
    opening's vote instant can vote only `P` at the opening slot; every round-`m` action read of a
    member of the set for `S.a m` has live confirmation `P`; and `P` passes the clear test at every
    round-`m` action read of a member of the set for round `m`'s grade-0 domain instant. -/
theorem openingAdoption_afterDeadlineOn (facts : Record.Facts M)
    {delayExtra : Nat}
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hbelow : BelowOneThirdOn S rho Hs)
    {rGST gap : Round} {t₀ : Int} (hrec : Restated.MultiProposerRecurrenceOn M S Hs gap t₀ rho.horizon)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    {m : Round} (hm : fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ m)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S m) ≤ rho.horizon)
    (hopening : S.E.proposer ((M.opening_slot S.hc m)) ∈
      Hs (M.confirmation_time S.E ((M.opening_slot S.hc m))))
    {P : NamedBlock V}
    (cp : M.Cache)
    (hcp : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
        (S.E.proposer (M.opening_slot S.hc m))).st.core.toHealing
      (M.proposal_time S.E (M.opening_slot S.hc m))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
        (S.E.proposer (M.opening_slot S.hc m))).cache ⇢ cp)
    (hP : M.proposal_with (M.gradeContract cp) .poolAndCarried S.E S.hc
      (S.node (S.E.proposer (M.opening_slot S.hc m)))
      (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
          (S.E.proposer (M.opening_slot S.hc m))).st
        (M.proposal_time S.E (M.opening_slot S.hc m)))
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
          (S.E.proposer (M.opening_slot S.hc m))).record cp).st ⇢ some P)
    (hloPost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    (hloOpen : lo ≤ M.opening S.E S.hc (rGST + 2 - S.hc.η_SG))
    (ht₀ : t₀ ≤ (Restated.Vocabulary.Execution.Setup.a M S (rGST + 2)))
    (hAll : ∀ (k : Round) (u : V), lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → u ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S k) → ∀ (j : Nat), rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    (∀ v ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc m))), ∀ cc : M.Cache,
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc m))) v).st.core.toHealing
        (M.vote_time S.E (M.opening_slot S.hc m))
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc m))) v).cache ⇢ cc →
      let n := M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc m))) v).st
          (M.vote_time S.E (M.opening_slot S.hc m)))
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc m))) v).record cc
      ∀ Tr : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ Tr →
      ∀ L : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
      ∀ L' : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
      ∀ H : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
          (M.toHealing n.st.core) Tr L L' (n.st.core.s - 1) ⇢ H →
        H = P.erase) ∧
    (∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S m)),
      ∀ nu ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S m)) u) m,
      nu.st.core.live_confirmed = P.erase) ∧
    (∀ u ∈ Hs (M.domain S.E S.hc m .g0),
      ∀ nu ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S m)) u) m,
      ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.nodeClear M S nu m P.erase ⇢ b →
        b = true) := by
  classical
  obtain ⟨_hdeadlineSlot, hdeadlineTwo, _hinterior, hdPos, hdSucc, hcEq, hqEq, hcDeadline,
    _hdeadlineTwoD⟩ := facts.gr.openingSlots_l86f S hm
  have hconfA : M.confirmation_time S.E ((M.opening_slot S.hc m)) =
      (Restated.Vocabulary.Execution.Setup.a M S m) :=
    (Restated.Vocabulary.Protocol.a_eq_confirmation_time facts S.hc S.E m).symm
  have hconfHor : M.confirmation_time S.E ((M.opening_slot S.hc m)) ≤ rho.horizon := by
    rw [hconfA]; exact hhor
  have hvoteHor : M.vote_time S.E ((M.opening_slot S.hc m)) ≤ rho.horizon :=
    (facts.sch.Protocol_vote_time_le_confirmation_time S.E _).trans hconfHor
  have hstores := Restated.openingProposal_voteStoreExtends_afterDeadlineOn facts S Hs Xb hf
    hHs hHsXb hcom hbelow hrec hdelay hpost hm hvoteHor hopening cp hcp hP hloPost hloOpen ht₀ hAll
  have hGSTdead : rGST ≤ fgSafetyProgressDeadline S rho rGST gap delayExtra := by
    unfold fgSafetyProgressDeadline
    exact (Nat.le_succ rGST).trans (Nat.le_add_right _ _)
  have hloD : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (fgSafetyProgressDeadline S rho rGST gap delayExtra)) :=
    hloPost.trans ((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone hGSTdead)
  have hloProposal : lo ≤ M.proposal_time S.E ((M.opening_slot S.hc m)) :=
    hloD.trans ((Restated.Vocabulary.Protocol.action_lt_proposal_time_two_after facts S _).le.trans
      (facts.sch.proposal_time_mono S.E hdeadlineTwo))
  have hmPos : 0 < m := lt_of_lt_of_le (Nat.succ_pos 1) ((Nat.le_add_left 2 _).trans hm)
  have hrm1 : rGST < m - 1 := by
    rw [← hcEq]; exact Nat.lt_succ_of_le (hGSTdead.trans hcDeadline)
  have hkM1 : lo ≤ M.early S.E S.hc (m - 1) .g2 - S.E.Δ :=
    Restated.lo_le_early_g2_sub_delta_of_action_lt facts S hloPost hrm1
  have hkM : lo ≤ M.early S.E S.hc m .g2 - S.E.Δ :=
    Restated.lo_le_early_g2_sub_delta_of_action_lt facts S hloPost
      (lt_of_lt_of_le hrm1 (Nat.sub_le m 1))
  have hwinM : lo ≤ M.early S.E S.hc (M.round_of S.hc (M.opening_slot S.hc m)) .g1 - S.E.Δ := by
    rw [facts.gr.round_of_opening_slot_eq S.hc m]
    have h2 := facts.gr.q10_early_g2_le_early_g1 S m
    linarith
  have hpropConf : S.E.proposer (M.opening_slot S.hc m) ∈
      Hs (M.confirmation_time S.E (M.opening_slot S.hc m)) := hopening
  have hrunP : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick (S.E.proposer (M.opening_slot S.hc m))
      (M.proposal_time S.E (M.opening_slot S.hc m))) →
      M.awake_for_grade1 S (S.E.proposer (M.opening_slot S.hc m))
        (W j (S.E.proposer (M.opening_slot S.hc m))) (M.round_of S.hc (M.opening_slot S.hc m)) :=
    fun j hj => hf.awake_g1 _ _ j _ (Or.inl rfl) hj
      (hHs _ _ (facts.sch.proposal_time_le_confirmation_time S.E _) hpropConf) hwinM
  have hrunV : ∀ v ∈ Hs (M.vote_time S.E (M.opening_slot S.hc m)), v ∈ S.E.committee (M.opening_slot S.hc m) →
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick v (M.vote_time S.E (M.opening_slot S.hc m))) →
        M.awake_for_grade1 S v (W j v) (M.round_of S.hc (M.opening_slot S.hc m)) :=
    fun _ hv _ j hj => hf.awake_g1 _ _ j _ (Or.inr rfl) hj hv hwinM
  have hrunConf : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S m)),
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick v (M.confirmation_time S.E (M.opening_slot S.hc m))) →
        M.awake_for_grade2 (Setup.alwaysAwake S) v (W j v) (M.round_of S.hc (M.opening_slot S.hc m + 1)) := by
    intro v hv j hj
    have hround : M.round_of S.hc (M.opening_slot S.hc m + 1) = m := by
      have hR : 3 ≤ S.hc.R := S.hc.R_ge_three
      apply facts.gr.round_of_eq_of_opening_succ_le_of_lt_next_opening S.hc (le_refl _)
      rw [facts.gr.opening_slot_succ_eq S.hc m]
      exact Nat.add_lt_add_left (by omega) _
    refine hf.awake_g2 _ _ j hj (by rw [hconfA]; exact hv) ?_
    rw [hround]
    exact hkM
  have hPclock : M.proposal_with (M.gradeContract cp)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc
      (S.node (S.E.proposer (M.opening_slot S.hc m)))
      (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
          (S.E.proposer (M.opening_slot S.hc m))).st
        (M.proposal_time S.E (M.opening_slot S.hc m))) ⇢ some P := by
    have h := hP
    rw [facts.nd.mkNode_st, facts.dt.proposal_with_store_with_cache] at h
    exact h
  obtain ⟨I, hI⟩ := facts.dt.with_proposal_input_nonempty (M.gradeContract cp) S.E S.hc
    (S.node (S.E.proposer (M.opening_slot S.hc m)))
    (M.toHealing (M.mkNode (M.ns_setClock S.E
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
        (S.E.proposer (M.opening_slot S.hc m))).st
      (M.proposal_time S.E (M.opening_slot S.hc m)))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc m)))
        (S.E.proposer (M.opening_slot S.hc m))).record cp).st.core)
  refine ⟨?_, ?_, ?_⟩
  · intro v hv cc hcc n Tr hTr L hL L' hL' H hH
    exact (hstores v hv cc hcc Tr hTr I hI).head Tr hTr L hL L' hL' H hH
  · have hread := Restated.openingProposal_confirmationRead_afterDeadlineOn facts S Hs Xb hf
      hHs hHsXb hcom hbelow hrec hdelay hpost hm hhor hopening cp hcp hP hloPost hloOpen ht₀ hAll
    have hstoresOn : Restated.VoteStoresExtendOn M S rho Hs ((M.opening_slot S.hc m))
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc m)))) P := by
      intro v hv _ c hc
      obtain ⟨T₀, hT₀⟩ := facts.fc.voter_filtered_block_tree_nonempty S.E
        (M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc m))) v).st
          (M.vote_time S.E (M.opening_slot S.hc m)))
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc m))) v).record c).st.core
        (M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc m))) v).st
          (M.vote_time S.E (M.opening_slot S.hc m)))
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc m))) v).record c).st.core.s
      exact ⟨T₀.erase P.erase, I.parent, hstores v hv c hc T₀ hT₀ I hI⟩
    exact Restated.openingProposal_liveConfirmed_actionStore_after_gst_of_localReadsOn facts S Hs Xb
      hf hHs hHsXb hcom hmPos
      (hloProposal.trans (facts.sch.proposal_time_lt_vote_time S.E _).le) hhor
      (by rw [← hconfA]; exact hopening) cp hcp hPclock hstoresOn hread hloProposal
      hrunV hrunP hrunConf
  · have hsgParent := actionSGBlock_preceq_proposedParent_afterDeadlineOn₈₆g facts S Hs Xb hf
      hHs hHsXb hcom hbelow hrec hdelay hpost hm hvoteHor hopening cp hcp hP hloPost hloOpen ht₀
      hAll
    have hdomHor : M.domain S.E S.hc m .g0 ≤ rho.horizon :=
      (facts.gr.domain_le_a S m .g0).trans hhor
    have hwindow : Restated.RelativeCarrierWindowAtOn M S rho W
        (fun t => W (strictEventIndex rho t)) Hs (m - 1) .g0 :=
      Restated.relativeCarrierWindowAt_after_recovery_deadlineOn facts S Hs Xb hf hHs hHsXb
        hcom hbelow hrec hdelay hpost (r := m - 1) (hcDeadline.trans (Nat.sub_le (m - 1) 1))
        (by rw [hqEq]; exact hdomHor) hloPost hloOpen ht₀
        (fun k hk u hu => hAll k u hk (hHs _ _ (le_add_of_nonneg_right S.E.Δ_pos.le) hu))
    exact Restated.g0ClearAtAction_of_relativeCarrierWindowOn facts S Hs Xb hf hHs hbelow hmPos
      hhor ((facts.gr.domain_le_a S m .g2).trans hhor)
      (hloD.trans ((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone
        (hcDeadline.trans (Nat.sub_le (m - 1) 1))))
      hwindow cp hcp hPclock
      (fun u hu nu hnu A2 hA2 G hG I' hI' => hsgParent u hu nu hnu A2 hA2 G hG I' hI')
      (fun u hu => hAll (m - 1) u hkM1 (hHs _ _ (le_add_of_nonneg_right S.E.Δ_pos.le) hu))

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
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog

/-- In the run `R` of the first `n` steps of the execution `x`, along the path
    `W = Restated.runAllPath M S Sched x v₀ n`, for a round `c` at least two rounds after the
    progress deadline with `S.a c` within the horizon, whose opening proposer is not held at its
    confirmation instant and proposes `P`: every validator not held at the opening's vote instant
    can vote only `P` there; every validator not held at `S.a c` has live confirmation `P` at its
    round-`c` action read; and `P` passes the clear test at the round-`c` action read of every
    validator not held at round `c`'s grade-0 domain instant. -/
theorem openingAdoption_at_strongWindow_afterDeadline (facts : Record.Facts M)
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
    {c : Round} (hc : Restated.deadlineRoundW M S tGAT gap + 2 ≤ c)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c) ≤
      ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } :
        Record.Run V).horizon)
    (hopening : S.E.proposer ((M.opening_slot S.hc c)) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c))))
    {P : NamedBlock V} :
    let R : Record.Run V :=
      { Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) }
    let W := Restated.runAllPath M S Sched x v₀ n
    let wp := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c)))
      (S.E.proposer (M.opening_slot S.hc c))
    ∀ cp : M.Cache,
      M.onPhaseTick S.E S.hc wp.st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc c)) wp.cache ⇢ cp →
      let pn := M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E (M.opening_slot S.hc c)))
        wp.record cp
      M.proposal_with (M.gradeContract cp) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc c))) pn.st ⇢ some P →
    (∀ v ∈ notHeldAt Sched (M.vote_time S.E ((M.opening_slot S.hc c))), ∀ cc : M.Cache,
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex R (M.vote_time S.E (M.opening_slot S.hc c))) v).st.core.toHealing
        (M.vote_time S.E (M.opening_slot S.hc c))
        (W (strictEventIndex R (M.vote_time S.E (M.opening_slot S.hc c))) v).cache ⇢ cc →
      let nv := M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex R (M.vote_time S.E (M.opening_slot S.hc c))) v).st
          (M.vote_time S.E (M.opening_slot S.hc c)))
        (W (strictEventIndex R (M.vote_time S.E (M.opening_slot S.hc c))) v).record cc
      ∀ Tr : Finset (Block V), M.voter_filtered_block_tree S.E nv.st.core nv.st.core.s ⇢ Tr →
      ∀ L : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing nv.st.core).toFG.toSG.toGoldfishStore nv.st.core.s ⇢ L →
      ∀ L' : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing nv.st.core).toFG.toSG.toGoldfishStore nv.st.core.s ⇢ L' →
      ∀ H : Block V, M.get_head_in_tree_with_layer (M.gradeContract nv.cache) S.E S.hc
          (M.toHealing nv.st.core) Tr L L' (nv.st.core.s - 1) ⇢ H →
        H = P.erase) ∧
    (∀ u ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c)),
      ∀ nu ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (W (strictEventIndex R (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c)) u) c,
      nu.st.core.live_confirmed = P.erase) ∧
    (∀ u ∈ notHeldAt Sched (M.domain S.E S.hc c .g0),
      ∀ nu ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (W (strictEventIndex R (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c)) u) c,
      ∀ b : Bool,
        Restated.Vocabulary.Internal.PhaseGrades.nodeClear M (Setup.alwaysAwake S) nu c P.erase ⇢ b →
        b = true) := by
  intro R W wp cp hcp pn hP
  obtain ⟨hpost, -, hloOpen, ht₀⟩ := Restated.roundAt_bounds_l71 facts S hgst
  exact Restated.openingAdoption_afterDeadlineOn facts
    (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ
    (Restated.admissibleFieldsOn_runAll_notHeld facts S Sched x v₀ n hsync hmono hawake hgst hcv
      hvalid hawm hthird hn)
    (fun _ _ h => notHeldAt_anti hmono h) (fun _ => Finset.subset_univ _)
    (Restated.honestCommitteesOn_notHeld facts S Sched hcom)
    (Restated.belowOneThirdOn_runAll_notHeld facts S Sched x v₀ n hthird hn)
    (Restated.multiProposerRecurrenceOn_runAll_notHeld facts S Sched x v₀ n hrec hn)
    (Setup.timeoutDelayBound _) hpost
    (by rw [Restated.fgSafetyProgressDeadline_eq_deadlineRoundW facts]; exact hc)
    hhor hopening cp hcp hP (Restated.roundAt_lo_le_rGST_l71 facts S tGAT) hloOpen ht₀
    (fun k u hk _ j hj => Restated.awake_g2_action_runAllPath facts S Sched x v₀ n hmono hawake hn
      k hk u j hj)

end

end DecoupledConsensusModel.Sts.Restated
