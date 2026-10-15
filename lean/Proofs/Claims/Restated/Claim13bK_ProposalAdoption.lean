import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13b
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bInvariantActiveSinceW
import Proofs.Claims.Restated.Claim13bK_ConfirmedInclusion
import Proofs.Claims.Restated.Claim13bK_WindowProposalSent
import Proofs.Claims.Restated.Claim13bStepCone
import Proofs.Claims.Restated.Claim13beRoute3_42
import Proofs.Claims.Restated.Claim13beRoute3_44
import Proofs.Claims.Restated.Claim13beRoute3_46
import Proofs.Claims.Restated.Claim13beRoute3_47b
import Proofs.Claims.Restated.Claim13beRoute3_49
import Proofs.Claims.Restated.Claim13beRoute3_50b
import Proofs.Claims.Restated.Claim13beRoute3_51
import Proofs.Claims.Restated.Claim13beRoute3_52
import Proofs.Claims.Restated.Claim13beRoute3_56
import Proofs.Claims.Restated.Claim13beRoute3_58
import Proofs.Claims.Restated.Claim13beRoute3_61
import Proofs.Claims.Restated.Claim13beRoute3_65b
import Proofs.Claims.Restated.Claim13beRoute3_71
import Proofs.Claims.Restated.Claim13beRoute3_72
import Proofs.Claims.Restated.Claim13beRoute3_73
import Proofs.Claims.Restated.Claim13beRoute3_85c
import Proofs.Claims.Restated.Claim13beRoute3_85d
import Proofs.Claims.Restated.Claim13beRoute3_86
import Proofs.Claims.Restated.Claim13beRoute3_86b
import Proofs.Claims.Restated.Claim13beRoute3_86e
import Proofs.Claims.Restated.Claim13beRoute3_86f
import Proofs.Claims.Restated.Claim13beRoute3_88
import Proofs.Claims.Restated.RunAll
import Proofs.Claims.Restated.Vocabulary_Execution_CarrierInteriorAdoption
import Proofs.Claims.Restated.Vocabulary_Execution_ExcludesRefute
import Proofs.Claims.Restated.Vocabulary_ModelVocabulary_Healing_Schedule
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_ProposalBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_Grades
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_PostHealingContinuation
import Proofs.Claims.Restated.Vocabulary_Protocol_ValidatorClient_BlockEmission
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActiveJoint
import Model.Conditions.Claim13bInvariantActiveSinceW
import Model.Conditions.Claim13bK_ConfirmedInclusion
import Model.Conditions.Claim13bK_ConfirmedSettle
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13bStepCone
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.Claim13beRoute3_72
import Model.Conditions.Claim13beRoute3_74
import Model.Conditions.Claim13beRoute3_83
import Model.Conditions.RunAll
import Model.Conditions.RunVocabulary
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Internal_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Definitions_NamedLifecycle
import Model.Conditions.Vocabulary_Internal_Definitions_NamedProposalPivot
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Internal_Invariants
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedHeadReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ProposalSourcesInternal
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedReceiptCalls
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_ModelVocabulary_Healing_Schedule
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Agreement
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_ReaderLocalCone
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_SGOpeningFrozenSuffix
import Proofs.Vocabulary.Protocol.ForkChoice.Views.ProposalCore
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Protocol_Handlers_Blocks
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bK_ProposalAdoption

/-!
# Honest proposals after the progress deadline

Facts on the proposals of slots two rounds after the progress deadline, read along a path `W` of the
run or along the path the execution follows, stated over a model `M : Record.Model V` and its facts
`facts : Record.Facts M`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

/-- Names a private theorem of the module `Proofs.Claims.Restated.Claim13beRoute3_51`. -/
local macro "p51% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_51)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- Names a private theorem of the module `Proofs.Claims.Restated.Claim13beRoute3_55`. -/
local macro "p55% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_55)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- Names a private theorem of the module `Proofs.Claims.Restated.Claim13beRoute3_56`. -/
local macro "p56% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_56)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- Names a private theorem of the module `Proofs.Claims.Restated.Claim13beRoute3_58`. -/
local macro "p58% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_58)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- Names a private theorem of the module `Proofs.Claims.Restated.Claim13beRoute3_60`. -/
local macro "p60% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_60)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- Names a private theorem of the module `Proofs.Claims.Restated.Claim13beRoute3_64b`. -/
local macro "p64b% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_64b)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- Names a private theorem of the module `Proofs.Claims.Restated.Claim13beRoute3_71`. -/
local macro "p71% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_71)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- Names a private theorem of the module `Proofs.Claims.Restated.Claim13beRoute3_73`. -/
local macro "p73% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_73)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- Names a private theorem of the module `Proofs.Claims.Restated.Claim13beRoute3_83`. -/
local macro "p83% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_83)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- Names a private theorem of the module `Proofs.Claims.Restated.Claim13beRoute3_86c`. -/
local macro "p86c% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_86c)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- Names a private theorem of the module `Proofs.Claims.Restated.Claim13beRoute3_86f`. -/
local macro "p86f% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_86f)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- Names a private theorem of the module `Proofs.Claims.Restated.Claim13beRoute3_86g`. -/
local macro "p86g% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_86g)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation

/-- If the bundle `AdmissibleFieldsOn` holds along `W` for the family `Hs`, and the family `Hs'` has
    the same set as `Hs` at every instant up to the run's horizon, then the bundle holds along `W`
    for `Hs'`. -/
theorem admissibleFieldsOn_of_eqUpToHorizon_i1b (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    {Hs Hs' : Int → Finset V} {Xb : Finset V} {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (heq : ∀ t : Int, t ≤ rho.horizon → Hs' t = Hs t) :
    Restated.AdmissibleFieldsOn M S rho W Hs' Xb lo := by
  have hΔ := S.E.Δ_pos
  exact
    { lo_pos := hf.lo_pos
      horizon_nonneg := hf.horizon_nonneg
      sorted := hf.sorted
      in_horizon := hf.in_horizon
      tick_public := hf.tick_public
      tickIndexUnique := hf.tickIndexUnique
      wire := hf.wire
      onePath := hf.onePath
      tick_outcome := hf.tick_outcome
      receipt_outcome := hf.receipt_outcome
      awake_g1 := fun s u j τ hτ he hu hlo =>
        hf.awake_g1 s u j τ hτ he
          (by rw [← heq τ (hf.in_horizon _ (List.mem_of_getElem? he)).2]; exact hu) hlo
      awake_g2 := fun s u j he hu hlo =>
        hf.awake_g2 s u j he
          (by
            rw [← heq (M.confirmation_time S.E s) (hf.in_horizon _ (List.mem_of_getElem? he)).2]
            exact hu) hlo
      deps := hf.deps
      tick_total := fun t hlo v hv hpub hhor =>
        hf.tick_total t hlo v (by rw [← heq t hhor]; exact hv) hpub hhor
      broadcast := by
        intro v o t hv hem w hw hlo hhor hexcl
        have h1 : t ≤ rho.horizon := by linarith
        exact hf.broadcast v o t (by rw [← heq t h1]; exact hv) hem w
          (by rw [← heq _ hhor]; exact hw) hlo hhor hexcl
      relay_block := by
        intro v i B t hv hacc w hw hpw hhor hexcl
        have h1 : max t lo ≤ rho.horizon := by linarith
        exact hf.relay_block v i B t (by rw [← heq _ h1]; exact hv) hacc w
          (by rw [← heq _ hhor]; exact hw) hpw hhor hexcl
      relay_block_admit := by
        intro v i B t hv hacc w hw hpw hhor hexcl
        have h1 : max t lo ≤ rho.horizon := by linarith
        exact hf.relay_block_admit v i B t (by rw [← heq _ h1]; exact hv) hacc w
          (by rw [← heq _ hhor]; exact hw) hpw hhor hexcl
      relay_gf_vote := by
        intro v i u t hv hacc hproc hlo w hw hpw hhor
        have h1 : t ≤ rho.horizon := by linarith
        exact hf.relay_gf_vote v i u t (by rw [← heq t h1]; exact hv) hacc hproc hlo w
          (by rw [← heq _ hhor]; exact hw) hpw hhor
      relay_gf_vote_handled := by
        intro v i u t hv hacc hlo w hw hpw hhor
        have h1 : t ≤ rho.horizon := by linarith
        exact hf.relay_gf_vote_handled v i u t (by rw [← heq t h1]; exact hv) hacc hlo w
          (by rw [← heq _ hhor]; exact hw) hpw hhor
      two_cutoff := by
        intro r c₂ source i a t hsource hacc hlo hc₂ hwin target htarget hpw hhor
        have h1 : t ≤ rho.horizon := by linarith
        have h2 : t + S.E.Δ ≤ rho.horizon := by linarith
        exact hf.two_cutoff r c₂ source i a t (by rw [← heq t h1]; exact hsource) hacc hlo hc₂
          hwin target (by rw [← heq _ h2]; exact htarget) hpw hhor
      unforgeable := by
        intro v o t hp u hu hauth
        have h1 := Restated.processes_time_le_horizonOn facts S Hs Xb hf hp
        exact hf.unforgeable v o t hp u (by rw [← heq t h1]; exact hu) hauth
      carried_gf := by
        intro v B t hp u hu hval
        have h1 := Restated.processes_time_le_horizonOn facts S Hs Xb hf hp
        exact hf.carried_gf v B t hp u hu (by rw [← heq t h1]; exact hval)
      carried_attest := by
        intro v B t hp a ha hval
        have h1 := Restated.processes_time_le_horizonOn facts S Hs Xb hf hp
        exact hf.carried_attest v B t hp a ha (by rw [← heq t h1]; exact hval)
      rootCollisionFree := hf.rootCollisionFree
      slashableBound := hf.slashableBound }

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation

/-- If more than half of every slot's committee is in the set of `Hs` for the slot's confirmation
    instant, and every set of `Hs` is inside the set of `Hs'` for the same instant, then the same
    holds for `Hs'`. -/
theorem honestCommitteesOn_of_subset_i1b (facts : Record.Facts M) (S : Setup V) {Hs Hs' : Int → Finset V}
    (hc : Restated.HonestCommitteesOn M S Hs) (hsub : ∀ t : Int, Hs t ⊆ Hs' t) :
    Restated.HonestCommitteesOn M S Hs' := by
  intro s
  exact lt_of_lt_of_le (hc s)
    (Nat.mul_le_mul_left 2 (Finset.card_le_card (Finset.inter_subset_inter_left (hsub _))))

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation

/-- If the carrier recurrence holds for `Hs` and every set of `Hs` is inside the set of `Hs'` for
    the same instant, then it holds for `Hs'`. -/
theorem multiProposerRecurrenceOn_of_subset_i1b (facts : Record.Facts M) (S : Setup V) {Hs Hs' : Int → Finset V}
    {gap : Nat} {t₀ tEnd : Int} (hr : Restated.MultiProposerRecurrenceOn M S Hs gap t₀ tEnd)
    (hsub : ∀ t : Int, Hs t ⊆ Hs' t) :
    Restated.MultiProposerRecurrenceOn M S Hs' gap t₀ tEnd := by
  intro r h0 h1
  obtain ⟨r', hr1, hr2, hc⟩ := hr r h0 h1
  exact ⟨r', hr1, hr2, fun k hk => hsub _ (hc k hk)⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- The round and slot bounds of a slot `start` at or after the opening slot of round `D + 2`, with
    `r = round_of start` and `d = start − 1`: among them `D + 2 ≤ r`, `0 < d`, `d + 1 = start` and
    `opening_slot r ≤ start < opening_slot (r + 1)`. -/
theorem generalSlots_i1b (facts : Record.Facts M) (S : Setup V) {D : Round} {start : Slot}
    (hs : (M.opening_slot S.hc (D + 2)) ≤ start) :
    D + 2 ≤ (M.round_of S.hc start) ∧
      (M.opening_slot S.hc D) + 1 ≤ start - 1 ∧
      (M.opening_slot S.hc D) + 2 ≤ start ∧
      (M.opening_slot S.hc ((M.round_of S.hc start) - 1)) + 1 ≤ start - 1 ∧
      0 < start - 1 ∧
      start - 1 + 1 = start ∧
      (M.round_of S.hc start) - 2 + 1 = (M.round_of S.hc start) - 1 ∧
      (M.round_of S.hc start) - 1 + 1 = (M.round_of S.hc start) ∧
      D ≤ (M.round_of S.hc start) - 2 ∧
      (M.opening_slot S.hc D) + 2 ≤ start - 1 ∧
      (M.opening_slot S.hc ((M.round_of S.hc start))) ≤ start ∧
      start < (M.opening_slot S.hc ((M.round_of S.hc start) + 1)) := by
  have hopenR : (M.opening_slot S.hc ((M.round_of S.hc start))) ≤ start :=
    facts.gr.opening_slot_round_of_le_slot S.hc start
  have hnextR : start < (M.opening_slot S.hc ((M.round_of S.hc start) + 1)) :=
    facts.gr.lt_opening_slot_round_of_succ S.hc start
  have hrGe : D + 2 ≤ (M.round_of S.hc start) := by
    by_contra hlt
    have hle : (M.round_of S.hc start) + 1 ≤ D + 2 := Nat.succ_le_of_lt (Nat.lt_of_not_le hlt)
    exact lt_irrefl start ((hnextR.trans_le (facts.gr.opening_slot_mono S hle)).trans_le hs)
  obtain ⟨hcEq, hqEq, hcD⟩ := roundArith_l86f D ((M.round_of S.hc start)) hrGe
  have hy : (M.opening_slot S.hc ((M.round_of S.hc start) - 1)) + S.hc.R ≤ start := by
    have h : (M.opening_slot S.hc ((M.round_of S.hc start) - 1)) + S.hc.R =
        (M.opening_slot S.hc ((M.round_of S.hc start))) := by
      rw [← facts.gr.opening_slot_succ S.hc ((M.round_of S.hc start) - 1), hqEq]
    rw [h]; exact hopenR
  have hx : (M.opening_slot S.hc D) + 2 * S.hc.R ≤ start := by
    have h : (M.opening_slot S.hc D) + 2 * S.hc.R = (M.opening_slot S.hc (D + 2)) := by
      rw [facts.gr.opening_slot_add S.hc D 2]
    rw [h]; exact hs
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := slotBookkeeping_i1b _ _ _ _ S.hc.R_ge_two hy hx
  exact ⟨hrGe, h1, h2, h3, h4, h5, hcEq, hqEq, hcD, h6, hopenR, hnextR⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- Under the bundle along `W`, if `start` is a slot of round `q + 1`, every block the SG vote
    selector can return at the round-`q` action read of a member of the set for `S.a q` is an
    ancestor of `C`, and `start`'s proposer is in the set for its proposal instant with its FG root
    an ancestor of `C`, then every outcome of the anchor of `start`'s proposal read is an ancestor
    of `C`. -/
theorem proposalAnchor_preceq_of_previousCarriersOn_i1b (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hfb : BelowOneThirdOn S rho Hs)
    {q : Round} {start : Slot}
    (hslo : (M.opening_slot S.hc (q + 1)) ≤ start)
    (hshi : start < (M.opening_slot S.hc (q + 1 + 1)))
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S q))
    (hcut : Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (q + 1) ≤ rho.horizon)
    (hproposalHor : M.proposal_time S.E start ≤ rho.horizon)
    {C : Block V}
    (hupper : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v) q,
      ∀ g, M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ g →
      ∀ B, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) g ⇢ B →
        Block.Preceq B C)
    (hprop : S.E.proposer start ∈ Hs (M.proposal_time S.E start))
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E start)) (S.E.proposer start)).st.core.toHealing
      (M.proposal_time S.E start)
      (W (strictEventIndex rho (M.proposal_time S.E start)) (S.E.proposer start)).cache ⇢ c)
    (hroot : Block.Preceq
      (M.get_fg_root (M.toHealing (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E start)) (S.E.proposer start)).st
        (M.proposal_time S.E start))
        (W (strictEventIndex rho (M.proposal_time S.E start)) (S.E.proposer start)).record c).st.core).toFG)
      C)
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S q)) → M.awake_for_grade2 S u (W j u) q)
    (hgat : lo ≤ M.domain S.E S.hc (q + 1) .g1) :
    ∀ A : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S
      (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E start)) (S.E.proposer start)).st
        (M.proposal_time S.E start))
        (W (strictEventIndex rho (M.proposal_time S.E start)) (S.E.proposer start)).record c)
      (M.round_of S.hc (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E start)) (S.E.proposer start)).st
        (M.proposal_time S.E start))
        (W (strictEventIndex rho (M.proposal_time S.E start)) (S.E.proposer start)).record c).st.core.s)
        ⇢ A →
      Block.Preceq A C := by
  have hround : M.round_of S.hc (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E start)) (S.E.proposer start)).st
        (M.proposal_time S.E start))
        (W (strictEventIndex rho (M.proposal_time S.E start)) (S.E.proposer start)).record c).st.core.s
      = q + 1 := by
    have hr : (M.round_of S.hc start) = q + 1 := by
      rcases Nat.eq_or_lt_of_le hslo with heq | hlt
      · rw [← heq]; exact facts.gr.round_of_opening_slot_eq_schedule S.hc (q + 1)
      · exact facts.gr.round_of_eq_of_opening_succ_le_of_lt_next_opening S.hc hlt hshi
    rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.hd.Sts_setClock_core_s, facts.sch.slotOf_proposal_time]
    exact hr
  rw [hround]
  rcases Nat.eq_or_lt_of_le hslo with heq | hlt
  · subst heq
    exact Restated.fixedRoot_preparedProposalAnchor_preceq_of_previousCarriersOn facts S Hs Xb hf
      hHs hHsXb hfb hpost hcut hproposalHor hupper hprop c hc hroot hA
  · exact Restated.interiorProposalAnchor_preceq_of_previousCarriersOn_l85d facts S Hs Xb hf
      hHs hHsXb hfb hpost hcut hlt hshi hproposalHor hupper hprop c hc hroot hA hgat

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- Under the bundle along `W`, if `opening_slot (D + 2) ≤ start`, `start`'s vote instant is in the
    horizon and `start`'s proposer is in the set for its confirmation instant, then some run block
    `E` is the greatest common ancestor of the heads the members vote at `start − 1`, every
    round-`(r − 1)` SG block of a member is an ancestor of `E`, `E` is an ancestor of the proposed
    parent, every outcome of the proposer's prepared anchor is an ancestor of `E`, and `E`'s stored
    height at the proposer's duty store is at least that store's `h_max − 1`. -/
theorem slotPivot_afterDeadlineOn_i1b (facts : Record.Facts M)
    {delayExtra : Nat}
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hbelow : BelowOneThirdOn S rho Hs)
    {rGST gap : Round} {t₀ : Int} (hrec : Restated.MultiProposerRecurrenceOn M S Hs gap t₀ rho.horizon)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    {start : Slot}
    (hstart : (M.opening_slot S.hc (fgSafetyProgressDeadline S rho rGST gap delayExtra + 2)) ≤ start)
    (hhor : M.vote_time S.E start ≤ rho.horizon)
    (hopening : S.E.proposer start ∈
      Hs (M.confirmation_time S.E start))
    (cp : M.Cache)
    (hcp : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E start))
        (S.E.proposer start)).st.core.toHealing
      (M.proposal_time S.E start)
      (W (strictEventIndex rho (M.proposal_time S.E start))
        (S.E.proposer start)).cache ⇢ cp)
    (hloPost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    (hloOpen : lo ≤ M.opening S.E S.hc (rGST + 2 - S.hc.η_SG))
    (ht₀ : t₀ ≤ (Restated.Vocabulary.Execution.Setup.a M S (rGST + 2)))
    (hAll : ∀ (k : Round) (u : V), lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → u ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S k) → ∀ (j : Nat), rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k)
    (head : V → Block V)
    (hhead : ∀ w ∈ Hs (M.vote_time S.E (start - 1)), ∃ c : M.Cache,
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E (start - 1))) w).st.core.toHealing
        (M.vote_time S.E (start - 1))
        (W (strictEventIndex rho (M.vote_time S.E (start - 1))) w).cache ⇢ c ∧
      let n := M.mkNode
        (M.ns_setClock S.E
          (W (strictEventIndex rho (M.vote_time S.E (start - 1))) w).st
          (M.vote_time S.E (start - 1)))
        (W (strictEventIndex rho (M.vote_time S.E (start - 1))) w).record c
      ∃ T : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T ∧
      ∃ L : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L ∧
      ∃ L' : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' ∧
      M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
        (M.toHealing n.st.core) T L L' (n.st.core.s - 1) ⇢ head w) :
    ∃ E : NamedBlock V,
      Restated.RunBlockOn M S rho W Xb E ∧
      (∀ w ∈ Hs (M.vote_time S.E (start - 1)),
        Block.Preceq E.erase (head w)) ∧
      (∀ B : Block V,
        (∀ w ∈ Hs (M.vote_time S.E (start - 1)), Block.Preceq B (head w)) →
        Block.Preceq B E.erase) ∧
      (∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S ((M.round_of S.hc start) - 1))),
        ∀ nv ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
            (W (strictEventIndex rho
              (Restated.Vocabulary.Execution.Setup.a M S ((M.round_of S.hc start) - 1))) u)
            ((M.round_of S.hc start) - 1),
        ∀ A2 : Option (Block V),
          M.grade2_block_with (M.gradeContract nv.cache) S.E S.hc (M.toHealing nv.st.core)
            (M.round_of S.hc (M.toHealing nv.st.core).s) ⇢ A2 →
        ∀ G : Block V,
          M.get_sg_vote_with (M.gradeContract nv.cache) S.E S.hc (M.toHealing nv.st.core)
            (M.round_of S.hc (M.toHealing nv.st.core).s) A2 ⇢ G →
          Block.Preceq G E.erase) ∧
      (∀ I : Protocol.ProposalInput V,
        Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract cp) S.E S.hc
          (S.node (S.E.proposer start))
          (M.toHealing (M.mkNode (M.ns_setClock S.E
            (W (strictEventIndex rho (M.proposal_time S.E start))
              (S.E.proposer start)).st
            (M.proposal_time S.E start))
            (W (strictEventIndex rho (M.proposal_time S.E start))
              (S.E.proposer start)).record cp).st.core) ⇢ I →
        Block.Preceq E.erase I.parent) ∧
      (∀ A0 : Block V,
        Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S
          (M.mkNode (M.ns_setClock S.E
            (W (strictEventIndex rho (M.proposal_time S.E start))
              (S.E.proposer start)).st
            (M.proposal_time S.E start))
            (W (strictEventIndex rho (M.proposal_time S.E start))
              (S.E.proposer start)).record cp)
          (M.round_of S.hc (M.mkNode (M.ns_setClock S.E
            (W (strictEventIndex rho (M.proposal_time S.E start))
              (S.E.proposer start)).st
            (M.proposal_time S.E start))
            (W (strictEventIndex rho (M.proposal_time S.E start))
              (S.E.proposer start)).record cp).st.core.s) ⇢ A0 →
        Block.Preceq A0 E.erase) ∧
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.proposal_time S.E start))
            (S.E.proposer start)).st.core
          (M.proposal_time S.E start)).h_max - 1 ≤
        ((Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.proposal_time S.E start))
            (S.E.proposer start)).st.core
          (M.proposal_time S.E start)).σ E.erase).h := by
  classical
  have hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ →
      ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat,
      rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) →
      M.awake_for_grade2 S u (W j u) k :=
    fun k hk u hu => hAll k u hk (hHs _ _ (le_add_of_nonneg_right S.E.Δ_pos.le) hu)
  obtain ⟨hrGe, hdeadlineSlot, hdeadlineTwo, hinterior, hdPos, hdSucc, hcEq, hqEq, hcDeadline,
    -, hopenR, hnextR⟩ := Restated.generalSlots_i1b facts S hstart
  set D := fgSafetyProgressDeadline S rho rGST gap delayExtra with hDdef
  set r := (M.round_of S.hc start) with hrdef
  set d := start - 1 with hddef
  set wp := W (strictEventIndex rho (M.proposal_time S.E start)) (S.E.proposer start) with hwpdef
  set pn := M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E start)) wp.record cp
    with hpndef
  have hpnst : pn.st = M.store_with_cache (M.ns_setClock S.E wp.st (M.proposal_time S.E start)) _ := facts.nd.mkNode_st _ _ _
  have hpncache : pn.cache = cp := facts.nd.mkNode_cache _ _ _
  have hpncore : pn.st = M.store_with_cache _ _ := facts.nd.mkNode_st _ _ _
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
  have hloVoteD : lo ≤ M.vote_time S.E d :=
    Restated.lo_le_vote_after_deadline_l86e facts S hloPost hdeadlineSlot
  have hkM1 : lo ≤ M.early S.E S.hc (r - 1) .g2 - S.E.Δ :=
    Restated.lo_le_early_g2_sub_delta_of_action_lt facts S hloPost
      (by rw [← hcEq]; exact Nat.lt_succ_of_le (hGSTdead.trans hcDeadline))
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
  have hpropConf : S.E.proposer start ∈ Hs (M.confirmation_time S.E start) := hopening
  have hpropVote : S.E.proposer start ∈ Hs (M.vote_time S.E start) :=
    hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E start) hpropConf
  have hpropProposal : S.E.proposer start ∈ Hs (M.proposal_time S.E start) :=
    hHs _ _ (facts.sch.proposal_time_lt_vote_time S.E start).le hpropVote
  have hpropSC : S.E.proposer (d + 1) ∈ Hs (M.support_cutoff S.E d) := by
    rw [hdSucc]
    refine hHs _ _ ?_ hpropProposal
    linarith
  have houts := hhead
  obtain ⟨E, hErun, hEheads, hEmax⟩ :=
    Restated.exists_namedGreatestPreviousHeadOn facts S Hs Xb hf hHs hHsXb hcom hdPos
      hprevVoteHor hloVoteD head hhead
      (fun w _ hw j hj => hf.awake_g1 _ _ j _ (Or.inr rfl) hj hw hwinD)
  have hupper : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (r - 1))),
      ∀ nv ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r - 1))) u) (r - 1),
      ∀ A2 : Option (Block V),
        M.grade2_block_with (M.gradeContract nv.cache) S.E S.hc (M.toHealing nv.st.core)
          (M.round_of S.hc (M.toHealing nv.st.core).s) ⇢ A2 →
      ∀ G : Block V,
        M.get_sg_vote_with (M.gradeContract nv.cache) S.E S.hc (M.toHealing nv.st.core)
          (M.round_of S.hc (M.toHealing nv.st.core).s) A2 ⇢ G →
        Block.Preceq G E.erase := by
    intro u hu nv hnv A2 hA2 G hG
    apply hEmax
    intro w hw
    obtain ⟨c, hc, T, hT, L, hL, L', hL', hH⟩ := houts w hw
    exact Restated.actionSGBlock_preceq_voterHeadAt_after_GSTOn facts S Hs Xb hf hHs hHsXb
      hcom hbelow hrec hdelay hpost (c := r - 2) hcDeadline (by rw [hcEq]; exact hinterior)
      hprevDelta (by rw [hcEq]; exact hu)
      (hAll _ _ (by rw [hcEq]; exact hkM1) (by rw [hcEq]; exact hu)) hw hloPost hloOpen ht₀ hA
      c hc T hT L hL L' hL' (head w) hH nv (by rw [hcEq]; exact hnv) A2 hA2 G hG
  have hreadBound : ∀ {read : Int}, (Restated.Vocabulary.Execution.Setup.a M S D) ≤ read →
      read ≤ rho.horizon → read ≤ M.confirmation_time S.E d → ∀ {u : V}, u ∈ Hs read →
      Block.Preceq
        (M.get_fg_root (M.toHealing (W (strictEventIndex rho read) u).st.core).toFG) E.erase := by
    intro read hread hreadHor hnext u hu
    apply hEmax
    intro w hw
    obtain ⟨c, hc, T, hT, L, hL, L', hL', hH⟩ := houts w hw
    exact Restated.fgRoot_preceq_previousHead_through_confirmation_after_GSTOn facts S Hs Xb hf
      hHs hHsXb hcom hbelow hrec hdelay hpost hread hreadHor hdeadlineSlot hnext hprevDelta
      hu hloPost hloOpen ht₀ hA w hw c hc T hT L hL L' hL' (head w) hH
  have hproposalNext : M.proposal_time S.E start ≤ M.confirmation_time S.E d := by linarith
  have hvoteNext : M.vote_time S.E start ≤ M.confirmation_time S.E d := by linarith
  have hsourceRoot : Block.Preceq (M.get_fg_root (M.toHealing pn.st.core).toFG) E.erase := by
    rw [hpnst]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    rw [(p60% setClock_fgRoot₆₀) facts S]
    exact hreadBound hdeadlineProposal hproposalHor hproposalNext hpropProposal
  have hcut : Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ r ≤ rho.horizon := by
    have hpr := facts.sch.proposal_time_mono S.E hopenR
    unfold Restated.Vocabulary.Protocol.HealConfig.Γ_neg1
    rw [facts.sch.Γ_0_eq_proposal_time S.hc S.E r]
    linarith
  have hpostPrev : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (r - 1)) :=
    hloD.trans ((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone
      (hcDeadline.trans (Nat.sub_le (r - 1) 1)))
  have hopenDeadline : (M.opening_slot S.hc D) + 2 ≤ (M.opening_slot S.hc r) :=
    (facts.gr.plusTwo_slot_le_nextOpening_l53 S D).trans
      (facts.gr.opening_slot_mono S ((Nat.succ_le_succ (Nat.le_succ D)).trans hrGe))
  have hgat : lo ≤ M.domain S.E S.hc (r - 1 + 1) .g1 := by
    rw [hqEq, facts.gr.Sts_domain_g1_eq_opening, facts.gr.opening_eq_proposal_time]
    exact hloD.trans ((Restated.Vocabulary.Protocol.action_lt_proposal_time_two_after facts S D).le.trans
      (facts.sch.proposal_time_mono S.E hopenDeadline))
  have hsourceAnchor : ∀ A0 : Block V,
      Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S pn
        (M.round_of S.hc pn.st.core.s) ⇢ A0 → Block.Preceq A0 E.erase :=
    Restated.proposalAnchor_preceq_of_previousCarriersOn_i1b facts S Hs Xb hf hHs hHsXb hbelow
      (q := r - 1) (by rw [hqEq]; exact hopenR) (by rw [hqEq]; exact hnextR) hpostPrev
      (by rw [hqEq]; exact hcut) hproposalHor hupper hpropProposal cp hcp hsourceRoot (hA (r - 1) hkM1) hgat
  obtain ⟨Ts, hTsrun, hTsband, hTsheads⟩ :=
    Restated.exists_namedCommonPreviousHeadAncestor_in_frontierBand_through_confirmation_after_GSTOn facts S Hs Xb
      hf hHs hHsXb hcom hbelow hrec hdelay hpost hdeadlineProposal hproposalHor hdeadlineSlot
      hproposalNext hprevDelta hpropProposal hloPost hloOpen ht₀ hA
  have hTsE : Block.Preceq Ts.erase E.erase := by
    apply hEmax
    intro w hw
    obtain ⟨c, hc, T, hT, L, hL, L', hL', hH⟩ := houts w hw
    exact hTsheads w hw c hc T hT L hL L' hL' (head w) hH
  have hTsENamed : NamedBlock.Preceq Ts E :=
    Restated.namedPreceq_of_runBlock_erase_preceqOn facts Hs Xb hf hTsrun hErun hTsE
  have hsourceBand : wp.st.core.h_max - 1 ≤ (M.derive_named S.E S.cfg E).h :=
    hTsband.trans (facts.cs.derive_height_mono S.E S.cfg hTsENamed)
  have hcone : Restated.NamedHonestVotesConeOn M S rho W Hs Xb d
      (fun X => Block.Preceq E.erase X) := by
    intro x hx hcommittee
    obtain ⟨c, hc, T, hT, L, hL, L', hL', hH⟩ := houts x hx
    obtain ⟨X, hXhead, hXrun, hXemit⟩ :=
      Restated.named_voter_head_emitsOn facts S Hs Xb hf hHsXb hx hdPos hcommittee
        hprevVoteHor hloVoteD c hc
        (fun j hj => hf.awake_g1 _ _ j _ (Or.inr rfl) hj hx hwinD) T hT L hL L' hL' (head x) hH
    exact ⟨X, by rw [hXhead]; exact hEheads x hx, hXrun, hXemit⟩
  have hrootCompat : Block.compatible (M.get_fg_root (M.toHealing pn.st.core).toFG) E.erase = true :=
    compatible_of_preceq_common_Preceq hsourceRoot (Proofs.ModelProperties.Preceq_self E.erase)
  have hsupport := Restated.fixedRoot_preparedProposalConeSupport_of_namedConeOn facts S Hs Xb hf
    hHs hHsXb hcom hdPos hloVoteD hsupportHor hpropSC cp (by rw [hdSucc]; exact hcp)
    (by rw [hdSucc]; exact hsourceRoot) hcone
  rw [hdSucc] at hsupport
  have hvalid := Restated.proposerDutyStore_proposer_view_valid_coreOn facts S Hs Xb hf start
  have hproposerVoteRoot : Block.Preceq
      (M.get_fg_root (M.toHealing (M.ns_setClock S.E
        (W (strictEventIndex rho (M.vote_time S.E (d + 1))) (S.E.proposer (d + 1))).st
        (M.vote_time S.E (d + 1))).core).toFG) E.erase := by
    rw [(p60% setClock_fgRoot₆₀) facts S, hdSucc]
    exact hreadBound hdeadlineVote hhor hvoteNext hpropVote
  have hmemP := (p64b% mem_stateBeforeTime_along₆₄b) hf.sorted hf.onePath
    (M.proposal_time S.E start)
  have hmemW : E.erase ∈ wp.st.core.T := by
    have havailable := Restated.honestHeadsAvailableBefore_of_namedPostHealingConeOn facts S Hs Xb
      hf hHs hHsXb hpropSC hloVoteD hsupportHor hproposerVoteRoot hcone
    have hxcPos : 0 < ((S.E.committee d) ∩ Hs (M.confirmation_time S.E d)).card := by
      have hc := hcom d
      omega
    obtain ⟨x0, hx0⟩ := Finset.card_pos.mp hxcPos
    have hx0c := (Finset.mem_inter.mp hx0).1
    have hx0conf := (Finset.mem_inter.mp hx0).2
    have hx0vote : x0 ∈ Hs (M.vote_time S.E d) :=
      hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E d) hx0conf
    obtain ⟨X, hXE, hXrun, hXemit⟩ := hcone x0 hx0vote hx0c
    have hXhead : Restated.HonestHeadOn M S rho W Hs Xb d X.erase :=
      ⟨x0, hx0conf, hx0c, ⟨X, rfl, hXrun⟩, hXemit⟩
    rcases havailable X.erase hXhead with hgen | hadmit
    · have hEgen : E.erase = Block.genesis :=
        eq_genesis_of_Preceq_genesis (hgen ▸ hXE)
      rw [hEgen]
      exact (Restated.genesis_mem_and_stamp_storeBeforeTimeOn facts S Hs Xb hf (S.E.proposer start)
          (M.proposal_time S.E start) (M.proposal_time S.E start)).1
    · have hXT := (Restated.admittedBefore_mem_and_stamp_atOn facts S Hs Xb hf hadmit
        (facts.sch.support_cutoff_le_proposal_time_succ S.E d)).1
      rw [hdSucc] at hXT
      have hpc := Restated.Vocabulary.Proofs.NamedStoreBridge.parentClosed_stateBeforeTime facts S rho
        (M.proposal_time S.E start) (S.E.proposer start) _ hmemP
      unfold Restated.Vocabulary.Internal.ParentClosed Record.Model.GS.parent_closed at hpc
      rw [facts.sto.toHealing_gs_T] at hpc
      exact Proofs.Records.mem_of_preceq hpc.2 E.erase X.erase hXT
        (preceq_eq_true_iff_Preceq.2 hXE)
  have hEbody : E ∈ wp.st.bodies :=
    Restated.namedBody_of_mem_storeBeforeTime_l86f facts S Hs Xb hf (hHsXb _ hpropProposal)
      hmemW hErun
  have hview := Restated.Vocabulary.Proofs.NamedStoreBridge.derivedView_stateBeforeTime facts S rho
    (M.proposal_time S.E start) (S.E.proposer start) _ hmemP E hEbody
  have hσ : (pn.st.core.σ E.erase).h = (M.derive_named S.E S.cfg E).h := by
    rw [hpnst]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    rw [facts.hd.Sts_setClock_core_σ]
    exact congrArg (fun z => z.h) hview
  have hbandpn : pn.st.core.h_max - 1 ≤ (pn.st.core.σ E.erase).h := by
    rw [hσ, hpnst]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    rw [facts.hd.setClock_core_h_max]
    exact hsourceBand
  have hmem : E.erase ∈ pn.st.core.T := by
    rw [hpnst]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    rw [facts.hd.Sts_setClock_core_T]
    exact hmemW
  have hwitness : Restated.Vocabulary.Proofs.HealingSurface.CanonicalConeWitness M pn.st.core E.erase :=
    ⟨E.erase, hmem, Proofs.ModelProperties.Preceq_self _, hbandpn⟩
  have hEparent := Restated.fixedRoot_preparedProposalHead_preceq_of_coneOn facts S Hs Xb
    (Hs (M.confirmation_time S.E d)) hf cp hcp hrootCompat hwitness
    (fun R hR => hsourceAnchor R ((p60% nodeAnchor_of_sgRoot₆₀s) facts S pn _
      (by rw [hpncache]; exact hR)))
    hsupport (by rw [hpncore]; (try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]); rw [← (p86f% tickStore_eq₈₆f) facts]
                 exact hvalid)
  refine ⟨E, hErun, hEheads, hEmax, hupper, hEparent, hsourceAnchor, ?_⟩
  have h := hbandpn
  rw [hpncore] at h
  try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at h
  rw [← (p86f% tickStore_eq₈₆f) facts] at h
  exact h

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- The candidate score bridge for the read `n` does not depend on the grade caches written into the
    proposer and voter stores. -/
private theorem scoreBridge_store_with_cache_pa (facts : Record.Facts M) {S : Setup V} {rho : Record.Run V}
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

/-- Under the premises of `slotPivot_afterDeadlineOn_i1b` along `W`, for every proposal `P` of
    `start`'s proposer, every member `v` of the set for `start`'s vote instant and every vote-duty
    read of `v` at `start`, the vote store extends to `P` and every head that read can vote is `P`. -/
theorem slotProposal_voteStoreExtends_afterDeadlineOn_i1b (facts : Record.Facts M)
    {delayExtra : Nat}
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hbelow : BelowOneThirdOn S rho Hs)
    {rGST gap : Round} {t₀ : Int} (hrec : Restated.MultiProposerRecurrenceOn M S Hs gap t₀ rho.horizon)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    {start : Slot}
    (hstart : (M.opening_slot S.hc (fgSafetyProgressDeadline S rho rGST gap delayExtra + 2)) ≤ start)
    (hhor : M.vote_time S.E start ≤ rho.horizon)
    (hopening : S.E.proposer start ∈
      Hs (M.confirmation_time S.E start))
    {P : NamedBlock V}
    (cp : M.Cache)
    (hcp : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E start))
        (S.E.proposer start)).st.core.toHealing
      (M.proposal_time S.E start)
      (W (strictEventIndex rho (M.proposal_time S.E start))
        (S.E.proposer start)).cache ⇢ cp)
    (hP : M.proposal_with (M.gradeContract cp) .poolAndCarried S.E S.hc
      (S.node (S.E.proposer start))
      (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E start))
          (S.E.proposer start)).st
        (M.proposal_time S.E start))
        (W (strictEventIndex rho (M.proposal_time S.E start))
          (S.E.proposer start)).record cp).st ⇢ some P)
    (hloPost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    (hloOpen : lo ≤ M.opening S.E S.hc (rGST + 2 - S.hc.η_SG))
    (ht₀ : t₀ ≤ (Restated.Vocabulary.Execution.Setup.a M S (rGST + 2)))
    (hAll : ∀ (k : Round) (u : V), lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → u ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S k) → ∀ (j : Nat), rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    ∀ v ∈ Hs (M.vote_time S.E start),
    ∀ cv : M.Cache, M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E start)) v).st.core.toHealing
        (M.vote_time S.E start)
        (W (strictEventIndex rho (M.vote_time S.E start)) v).cache ⇢ cv →
      let mv := M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E start)) v).st
          (M.vote_time S.E start))
        (W (strictEventIndex rho (M.vote_time S.E start)) v).record cv
      ∀ T₀ : Finset (Block V), M.voter_filtered_block_tree S.E mv.st.core mv.st.core.s ⇢ T₀ →
      ∀ I : Protocol.ProposalInput V,
        Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract cp) S.E S.hc
          (S.node (S.E.proposer start))
          (M.toHealing (M.mkNode (M.ns_setClock S.E
            (W (strictEventIndex rho (M.proposal_time S.E start))
              (S.E.proposer start)).st
            (M.proposal_time S.E start))
            (W (strictEventIndex rho (M.proposal_time S.E start))
              (S.E.proposer start)).record cp).st.core) ⇢ I →
      Restated.Vocabulary.Proofs.Optimistic.NamedVoteStoreExtends M S rho v start
        mv (T₀.erase P.erase) I.parent P := by
  classical
  have hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ →
      ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat,
      rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) →
      M.awake_for_grade2 S u (W j u) k :=
    fun k hk u hu => hAll k u hk (hHs _ _ (le_add_of_nonneg_right S.E.Δ_pos.le) hu)
  obtain ⟨-, hdeadlineSlot, hdeadlineTwo, -, hdPos, hdSucc, hcEq, hqEq, hcDeadline,
    hdeadlineTwoD, hopenR, -⟩ := Restated.generalSlots_i1b facts S hstart
  set D := fgSafetyProgressDeadline S rho rGST gap delayExtra with hDdef
  set r := (M.round_of S.hc start) with hrdef
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
  have hloProposalD : lo ≤ M.proposal_time S.E d :=
    hloD.trans ((Restated.Vocabulary.Protocol.action_lt_proposal_time_two_after facts S D).le.trans
      (facts.sch.proposal_time_mono S.E hdeadlineTwoD))
  have hloFreezeD : lo ≤ M.view_freeze S.E d := by linarith
  have hpropConf : S.E.proposer start ∈ Hs (M.confirmation_time S.E start) := hopening
  have hpropVote : S.E.proposer start ∈ Hs (M.vote_time S.E start) :=
    hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E start) hpropConf
  have hvoteNext : M.vote_time S.E start ≤ M.confirmation_time S.E d := by linarith
  have hex := fun w : V => (p86g% exists_headOutcome₈₆g) facts S
    (W (strictEventIndex rho (M.vote_time S.E d)) w) (M.vote_time S.E d)
  choose head hheadAll using hex
  obtain ⟨E, hErun, hEheads, hEmax, hupper, hEparent, hsourceAnchor, hsourceBandσ⟩ :=
    Restated.slotPivot_afterDeadlineOn_i1b facts S Hs Xb hf hHs hHsXb hcom hbelow hrec hdelay
      hpost hstart hhor hopening cp hcp hloPost hloOpen ht₀ hAll head (fun w _ => hheadAll w)
  have hreadBound : ∀ {read : Int}, (Restated.Vocabulary.Execution.Setup.a M S D) ≤ read →
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
  have hcut : Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ r ≤ rho.horizon := by
    have hpr := facts.sch.proposal_time_mono S.E hopenR
    unfold Restated.Vocabulary.Protocol.HealConfig.Γ_neg1
    rw [facts.sch.Γ_0_eq_proposal_time S.hc S.E r]
    linarith
  have hpostPrev : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (r - 1)) :=
    hloD.trans ((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone
      (hcDeadline.trans (Nat.sub_le (r - 1) 1)))
  have hroundStart : (M.round_of S.hc (d + 1)) = r - 1 + 1 := by
    rw [hdSucc, hqEq]
  have hD1 : rGST + 1 ≤ D := by
    rw [hDdef]
    unfold fgSafetyProgressDeadline
    exact Nat.le_add_right _ _
  have hkM1 : lo ≤ M.early S.E S.hc (r - 1) .g2 - S.E.Δ :=
    Restated.lo_le_early_g2_sub_delta_of_action_lt facts S hloPost
      (by rw [← hcEq]; exact Nat.lt_succ_of_le (hGSTdead.trans hcDeadline))
  have hwinR : lo ≤ M.early S.E S.hc r .g1 - S.E.Δ := by
    have h1 := facts.gr.action_delta_le_early S S.hc.R_ge_three
      (lt_of_lt_of_le (Nat.lt_of_succ_le hD1) (hcDeadline.trans (Nat.sub_le r 2)))
    have h2 := facts.gr.q10_early_g2_le_early_g1 S r
    have h3 : lo ≤ M.a S.hc S.E.Δ rGST := hloPost
    linarith
  have hrunP : ∀ j : Nat, rho.events[j]? =
      some (Record.Event.tick (S.E.proposer start) (M.proposal_time S.E start)) →
      M.awake_for_grade1 S (S.E.proposer start) (W j (S.E.proposer start)) (M.round_of S.hc start) :=
    fun j hj => hf.awake_g1 _ _ j _ (Or.inl rfl) hj
      (hHs _ _ (facts.sch.proposal_time_lt_vote_time S.E start).le hpropVote) hwinR
  intro v hv cv hcv mv T₀ hT₀ I hI
  have hmvst : mv.st = M.store_with_cache (M.ns_setClock S.E
      (W (strictEventIndex rho (M.vote_time S.E start)) v).st (M.vote_time S.E start)) cv :=
    facts.nd.mkNode_st _ _ _
  have hmvread : mv ∈ Restated.Vocabulary.Internal.NamedRecoveryRead.voteDutyRead M S rho v start :=
    (p58% mkNode_mem_confirmationReadAt₅₈) hf.sorted hf.onePath _ _ cv hcv
  have hσmv : ∀ X : Block V, mv.st.core.σ X =
      (W (strictEventIndex rho (M.vote_time S.E start)) v).st.core.σ X := by
    intro X
    rw [hmvst, facts.nd.store_with_cache_core_σ, facts.hd.Sts_setClock_core_σ]
  have hhmaxmv : mv.st.core.h_max =
      (W (strictEventIndex rho (M.vote_time S.E start)) v).st.core.h_max := by
    rw [hmvst, facts.nd.store_with_cache_core_h_max, facts.hd.setClock_core_h_max]
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
    Restated.exists_namedCommonPreviousHeadAncestor_in_frontierBand_through_confirmation_after_GSTOn facts S Hs Xb
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
    rw [hmvst, facts.nd.store_with_cache_bodies, facts.hd.Sts_setClock_bodies]
    exact hEbody0
  have hEband : mv.st.core.h_max - 1 ≤ (M.derive_named S.E S.cfg E).h := by
    rw [hhmaxmv]
    exact hTtband.trans (facts.cs.derive_height_mono S.E S.cfg hTtENamed)
  have hEmemv : E.erase ∈ mv.st.core.T := by
    rw [hmvst, facts.nd.store_with_cache_core_T, facts.hd.Sts_setClock_core_T]
    exact hEmem0
  have hrootmv : Block.Preceq (M.get_fg_root (M.toHealing mv.st.core).toFG) E.erase := by
    rw [hmvst, facts.nd.store_with_cache_get_fg_root, (p60% setClock_fgRoot₆₀) facts S]
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
      hbelow (q := r - 1) (s := d) hroundStart hpostPrev (by rw [hqEq]; exact hcut)
      (by rw [hdSucc]; exact hhor) hupper (w := v) (by rw [hdSucc]; exact hv)
      (by rw [hdSucc]; have h := hrootmv; rw [hmvst] at h; (try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at h); rw [← (p60% voteStore_eq₆₀s) facts S] at h; exact h) (hA (r - 1) hkM1) cv (by rw [hdSucc]; exact hcv)
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
    rw [hmvst, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.hd.setClock_core_F, facts.hd.setClock_core_J]
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
    apply scoreBridge_store_with_cache_pa facts
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
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel.Proofs.HealingSurface

/-- In an sts execution with unforgeable signatures, if `s`'s proposer is honest through the instant
    of `x[N]`, emits the named block `P` of slot `s` along the path the execution follows, and
    `proposedBlockAtStep S x i s B` holds at a step `i` at or before `x[N]`, then `B` is the erasure
    of `P`. -/
theorem proposedBlockAtStep_eq_of_emits_i1b (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (v₀ : V) {N i : Nat} {s : Slot} {B : Block V}
    {P : NamedBlock V} {Hs : Int → Finset V} {Xb : Finset V} {lo : Int}
    (hf : Restated.AdmissibleFieldsOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v₀ N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v₀ N) Hs Xb lo)
    (hunf : Restated.Unforgeability M S x)
    (hprop : HonestThroughTime Sched (x[N].time : Int) (S.E.proposer s))
    (hlt : M.proposal_time S.E s < (x[N].time : Int))
    (hPslot : P.slot = s)
    (hPemit : Restated.Vocabulary.Execution.NamedRun.emits M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v₀ N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v₀ N) (S.E.proposer s) (.block P) (M.proposal_time S.E s))
    (hB : Restated.proposedBlockAtStep M S x i s B) (hi : (x[i].time : Int) ≤ (x[N].time : Int)) :
    B = P.erase := by
  obtain ⟨k, hk, hktick, hsent⟩ := Restated.mem_sent_of_emits_runAll facts S Sched x v₀ hPemit
  have hauth : NamedObject.author (NamedObject.block P) = some (S.E.proposer s) :=
    Restated.author_of_emits facts (Setup.alwaysAwake S) _ _ hf.onePath hPemit
  have hBP : Restated.proposedBlockAtStep M S x (k + 1) s P.erase :=
    ⟨P, hsent, rfl, hPslot, (author_block P).symm.trans hauth⟩
  have hk1 : (x[k + 1].time : Int) = M.proposal_time S.E s := (Restated.tickStepAt_time facts x hktick).1
  exact Restated.proposedBlockAtStep_unique_g1 facts S Sched x hunf
    (fun t ht => hprop t (ht.trans hi))
    (fun t ht => hprop t (ht.trans (by rw [hk1]; exact hlt.le))) hB hBP

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas

/-- If `Hs` keeps the adversary's weight less than one third at every instant up to the horizon of
    `rho`, and `Hs'` equals `Hs` at every such instant, then so does `Hs'`. -/
private theorem belowOneThirdOn_of_eqUpToHorizon_recordRun (S : Setup V) {rho : Record.Run V}
    {Hs Hs' : Int → Finset V} (hb : Restated.BelowOneThirdOn S rho Hs)
    (heq : ∀ t : Int, t ≤ rho.horizon → Hs' t = Hs t) :
    Restated.BelowOneThirdOn S rho Hs' := by
  intro t ht
  rw [heq t ht]
  exact hb t ht

/-- Under synchrony from wake, monotone corruption and the premises from `tGAT` to `tHi`,
    `HonestProposalHeadsAtOwnSlot` holds from the opening slot of the second round after the
    progress deadline up to `tHi`: at every such slot whose proposer is not held up to its vote
    instant, every honest active committee member votes for the block that proposer sent. -/
theorem honestProposalHeadsAtOwnSlot_i1b (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    {tGAT tHi : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tHi → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tHi →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tHi gap) :
    Restated.HonestProposalHeadsAtOwnSlot M S Sched x
      ((M.opening_slot S.hc (Restated.deadlineRoundW M S tGAT gap + 2))) tHi := by
  intro s i B hs₀ hct hprop hB hi v m hv hm G hG
  set N := m + 1 with hNdef
  obtain ⟨hNt, -⟩ := Restated.tickStepAt_time facts x hm
  have hNt' : (x[N].time : Int) = M.vote_time S.E s := hNt
  have hvc : M.vote_time S.E s ≤ M.confirmation_time S.E s :=
    facts.sch.Sts_vote_time_le_confirmation_time S s
  have hn : (x[N].time : Int) ≤ tHi := by rw [hNt']; exact hvc.trans hct
  set rho : Record.Run V := { Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) }
    with hrho
  have hhorT : rho.horizon = (x[N].time : Int) := rfl
  have heq : ∀ t : Int, t ≤ rho.horizon →
      notHeldUpTo_i1b Sched (x[N].time : Int) t = notHeldAt Sched t :=
    fun t ht => notHeldUpTo_eq_i1b Sched (by rw [← hhorT]; exact ht)
  have hsub : ∀ t : Int, notHeldAt Sched t ⊆ notHeldUpTo_i1b Sched (x[N].time : Int) t :=
    notHeldAt_subset_notHeldUpTo_i1b hmono (x[N].time : Int)
  have hf := Restated.admissibleFieldsOn_of_eqUpToHorizon_i1b facts (Setup.alwaysAwake S)
    (Restated.admissibleFieldsOn_runAll_notHeld facts S Sched x v N hsync hmono hawake hgst hcv hvalid hawm
      hthird hn) heq
  have hbelow := belowOneThirdOn_of_eqUpToHorizon_recordRun (Setup.alwaysAwake S)
    (Restated.belowOneThirdOn_runAll_notHeld facts S Sched x v N hthird hn) heq
  have hcomOn := Restated.honestCommitteesOn_of_subset_i1b facts (Setup.alwaysAwake S)
    (Restated.honestCommitteesOn_notHeld facts S Sched hcom) hsub
  have hrecOn := Restated.multiProposerRecurrenceOn_of_subset_i1b facts (Setup.alwaysAwake S)
    (Restated.multiProposerRecurrenceOn_runAll_notHeld facts S Sched x v N hrec hn) hsub
  have hHs : ∀ t t' : Int, t ≤ t' →
      notHeldUpTo_i1b Sched (x[N].time : Int) t' ⊆ notHeldUpTo_i1b Sched (x[N].time : Int) t :=
    fun _ _ h => notHeldUpTo_anti_i1b hmono (x[N].time : Int) h
  have hHsXb : ∀ t : Int, notHeldUpTo_i1b Sched (x[N].time : Int) t ⊆ (Finset.univ : Finset V) :=
    fun _ => Finset.subset_univ _
  obtain ⟨hpost, -, hloOpen, ht₀⟩ := Restated.roundAt_bounds_l71 facts S hgst
  have hloPost := Restated.roundAt_lo_le_rGST_l71 facts S tGAT
  have hstart : (M.opening_slot (Setup.alwaysAwake S).hc)
      (fgSafetyProgressDeadline (Setup.alwaysAwake S) rho (Restated.roundAt M S tGAT + S.hc.η_SG) gap
        (Setup.alwaysAwake S).extraRounds + 2) ≤ s := by
    rw [Restated.fgSafetyProgressDeadline_eq_deadlineRoundW facts]; exact hs₀
  obtain ⟨hrGe, -, hdeadlineTwo, -, hdPos, hdSucc, -⟩ := Restated.generalSlots_i1b facts S hs₀
  have hspos : 0 < s := Nat.lt_of_lt_of_le hdPos (Nat.sub_le s 1)
  have hwinS : tGAT + 1 ≤ M.early S.E S.hc (M.round_of S.hc s) .g1 - S.E.Δ := by
    have hlt : Restated.roundAt M S tGAT + S.hc.η_SG < M.round_of S.hc s :=
      lt_of_le_of_lt (Restated.rGST_le_deadlineRoundW_l85c facts S tGAT gap)
        (lt_of_lt_of_le (Nat.lt_succ_self _) ((Nat.le_succ _).trans hrGe))
    have h1 := facts.gr.action_delta_le_early S S.hc.R_ge_three hlt
    have h2 := facts.gr.q10_early_g2_le_early_g1 S (M.round_of S.hc s)
    have h3 : tGAT + 1 ≤ M.a S.hc S.E.Δ (Restated.roundAt M S tGAT + S.hc.η_SG) := hloPost
    linarith
  have hhor : M.vote_time S.E s ≤ rho.horizon := by rw [hhorT, hNt']
  have hproposalHor : M.proposal_time S.E s ≤ rho.horizon :=
    (facts.sch.proposal_time_lt_vote_time S.E s).le.trans hhor
  have hlo : tGAT + 1 ≤ M.proposal_time S.E s :=
    hloPost.trans (((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone (Restated.rGST_le_deadlineRoundW_l85c facts S tGAT gap)).trans
      ((Restated.Vocabulary.Protocol.action_lt_proposal_time_two_after facts S _).le.trans (facts.sch.proposal_time_mono S.E hdeadlineTwo)))
  have hminT : min (M.confirmation_time S.E s) (x[N].time : Int) =
      M.vote_time S.E s := by
    rw [hNt']; exact min_eq_right hvc
  have hpropConf : S.E.proposer s ∈
      notHeldUpTo_i1b Sched (x[N].time : Int) (M.confirmation_time S.E s) := by
    rw [notHeldUpTo_i1b, hminT, mem_notHeldAt]
    exact hprop _ le_rfl
  set W := Restated.runAllPath M S Sched x v N with hWdef
  set wp := W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s) with hwpdef
  obtain ⟨cp, hcp⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc wp.st.core.toHealing
    (M.proposal_time S.E s) wp.cache
  obtain ⟨o, ho⟩ := facts.dt.proposal_with_nonempty (M.gradeContract cp)
    Protocol.ProposalRowSource.poolAndCarried S.E S.hc
    ((Setup.alwaysAwake S).node (S.E.proposer s))
    (M.ns_setClock S.E wp.st (M.proposal_time S.E s))
  obtain ⟨P, rfl, hPslot, hPemit⟩ := Restated.proposedBlockAt_emits_of_honestOn facts (Setup.alwaysAwake S)
    (notHeldUpTo_i1b Sched (x[N].time : Int)) Finset.univ hf hHs s hspos hpropConf hproposalHor hlo
    (fun j hj => hf.tick_outcome j _ _ hj)
    (fun j hj => hf.awake_g1 _ _ j _ (Or.inl rfl) hj
      (hHs _ _ (facts.sch.proposal_time_le_confirmation_time S.E _) hpropConf)
      (by show tGAT + 1 ≤ M.early S.E S.hc (M.round_of S.hc s) .g1 - S.E.Δ; exact hwinS))
    cp hcp _ ho
  have hP : M.proposal_with (M.gradeContract cp) Protocol.ProposalRowSource.poolAndCarried S.E S.hc
      ((Setup.alwaysAwake S).node (S.E.proposer s))
      (M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E s)) wp.record cp).st ⇢ some P := by
    rewrite [facts.nd.mkNode_st, facts.dt.proposal_with_store_with_cache]
    exact ho
  have hheads := Restated.slotProposal_voteStoreExtends_afterDeadlineOn_i1b facts (Setup.alwaysAwake S)
    (notHeldUpTo_i1b Sched (x[N].time : Int)) Finset.univ hf hHs hHsXb hcomOn hbelow hrecOn
    (Setup.timeoutDelayBound _) hpost hstart hhor hpropConf cp hcp hP hloPost hloOpen ht₀
    (fun k u hk _ j hj => Restated.awake_g2_action_runAllPath facts S Sched x v N hmono hawake hn
      k hk u j hj)
  have hvVote : v ∈ notHeldUpTo_i1b Sched (x[N].time : Int) (M.vote_time S.E s) := by
    rw [notHeldUpTo_eq_i1b Sched (le_of_eq (by rw [hNt']))]
    exact notHeldAt_anti hmono hvc (mem_notHeldAt.mpr ((Restated.mem_HonSlot facts).mp hv).2.2)
  have hunf : Restated.Unforgeability M S x := hvalid.toUnforgeability
  have hlt : M.proposal_time S.E s < (x[N].time : Int) := by
    rw [hNt']; exact facts.sch.proposal_time_lt_vote_time S.E s
  have hBP : B = P.erase := Restated.proposedBlockAtStep_eq_of_emits_i1b facts S Sched x v hf hunf
    (by rw [hNt']; exact hprop) hlt hPslot hPemit hB (by rw [hNt']; exact hi)
  obtain ⟨cc, hcc, n, rfl, Tr, hTr, L, hL, L', hL', hH⟩ :=
    ((p73% gfHeadFrom_returns_iff₇₃) facts S _ _ G).1 hG
  have hstv : Restated.runAllPath M S Sched x v N
      (strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (M.vote_time (Setup.alwaysAwake S).E s)) v = x[m][v].st :=
    Restated.stateBeforeTime_runAll_tick facts S Sched x v hm (le_refl N) v
  obtain ⟨I, hI⟩ := facts.dt.with_proposal_input_nonempty (M.gradeContract cp) S.E S.hc
    ((Setup.alwaysAwake S).node (S.E.proposer s))
    (M.toHealing (M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E s)) wp.record cp).st.core)
  have hheadsv := hheads v hvVote
  rw [← hstv] at hcc hTr hL hL' hH
  have hGP : G = P.erase := (hheadsv cc hcc Tr hTr I hI).head Tr hTr L hL L' hL' G hH
  rw [hGP, hBP]
  exact preceq_eq_true_iff_Preceq.mp (Block.preceq_self _)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas

/-- Under the premises of `honestProposalHeadsAtOwnSlot_i1b` up to `tHi`, the phase length bound up
    to `tE` and the recurrence of strong openings from `tGAT` to `tE`,
    `HonestProposalHeadsAtOwnSlot` holds from the switch round's opening slot up to `tHi`. -/
theorem honestProposalHeadsAtOwnSlot_fromSwitch_i1b (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    {tGAT tE tHi : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tHi → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tHi →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tHi gap)
    (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hrecE : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap) :
    Restated.HonestProposalHeadsAtOwnSlot M S Sched x ((M.opening_slot S.hc (Restated.switchRound M S tE))) tHi := by
  let rho₀ : Record.Run V := { honest := ∅, horizon := 0, events := [] }
  have hr : Restated.deadlineRoundW M S tGAT gap + 2 ≤ Restated.switchRound M S tE :=
    (Restated.deadlineRoundW_add_two_le_rebased_l88 facts S Sched rho₀ hgst hlen hrecE).trans
      (Restated.rebasedDeadlineRoundW_le_switchRound facts S tGAT tE gap rho₀ hgst hlen)
  have h := Restated.honestProposalHeadsAtOwnSlot_i1b facts S Sched x hsync hmono hawake hgst hcv hvalid hawm
    hthird hcom hrec
  intro s i B hs₀ hct hprop hB hi
  exact h s i B ((facts.gr.opening_slot_mono S hr).trans hs₀) hct hprop hB hi

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas

/-- If the joint invariant holds at a round `r₀` at or after the switch round, slot `s` is at or
    after round `r₀`'s third slot with its confirmation instant at or before `tHi`, and `s`'s
    proposer, not held up to `s`'s vote instant, sent `B` by that instant, then every honest active
    member of the committee of every slot from `s` on votes for a descendant of `B`. -/
theorem honestProposal_ancestorOfHonestHeadsFrom_i1b (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hsync : Restated.SynchronyFromWake M S x)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE)
    (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hcs : Restated.committeeSleepinessW M S Sched tE)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hw : Restated.WakesAtActionInstants M S Sched) (hs : Restated.SleepsAfterActionInstants M S Sched)
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.BasePreviousRoundSGCompatibleWithAnchorAtRound M S Sched x v r N
        (Restated.runAllPath M S Sched x v N) T)
    (hclear : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round) (n₀ : Nat),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S r)) →
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T)
    (hB' : Restated.BaseJustifiedHighAtSwitchRoundW M S Sched x tGAT tE gap)
    {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    {T_W : NamedBlock V} (hAW : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W)
    (hJswitch : ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) - 1
        ≤ (x[n₁].time : Int) →
      n₁ ≤ n_W → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T_W.erase)
    {r₀ : Round} {n₀ : Nat} {T₀ : NamedBlock V}
    (hr₀ : Restated.switchRound M S tE ≤ r₀) (hTW₀ : Block.Preceq T_W.erase T₀.erase)
    (hJ₀ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r₀ n₀ n_W T₀)
    {tHi : Int}
    (hphaseHi : ∀ t : Int, tGAT ≤ t → t ≤ tHi →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hthirdHi : ∀ t : Int, t ≤ tHi →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hrecHi : Restated.strongOpeningsRecurFrom M S Sched tGAT tHi gap)
    {s : Slot} (hs0 : (M.opening_slot S.hc r₀) + 2 ≤ s)
    (hct : M.confirmation_time S.E s ≤ tHi)
    (hprop : HonestThroughTime Sched (M.vote_time S.E s) (S.E.proposer s))
    {i : Nat} {B : Block V} (hB : Restated.proposedBlockAtStep M S x i s B)
    (hi : (x[i].time : Int) ≤ M.vote_time S.E s) :
    Restated.AncestorOfHonestHeadsFrom M S Sched x B s := by
  have hadopt := Restated.honestProposalHeadsAtOwnSlot_fromSwitch_i1b facts S Sched x hsync hmono hphaseHi hgst
    hcv hexec hmult hthirdHi hcom hrecHi hlen hrec
  have hs₀ : (M.opening_slot S.hc (Restated.switchRound M S tE)) ≤ s :=
    (facts.gr.opening_slot_mono S hr₀).trans ((Nat.le_add_right _ 2).trans hs0)
  exact Restated.honestProposal_ancestorOfHonestHeadsFrom_i1 facts S Sched x tE hexec hmono htd tGAT gap hgst hlen
    hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear hB' hnW hAW hJswitch hr₀
    hTW₀ hJ₀ hadopt hs0 hs₀ hct hprop hB hi

end

end DecoupledConsensusModel.Sts.Restated
