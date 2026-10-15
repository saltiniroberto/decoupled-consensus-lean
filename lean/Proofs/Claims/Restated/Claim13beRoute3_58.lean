import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13beRoute3_45
import Proofs.Claims.Restated.Claim13beRoute3_45b
import Proofs.Claims.Restated.Claim13beRoute3_46
import Proofs.Claims.Restated.Claim13beRoute3_47
import Proofs.Claims.Restated.Claim13beRoute3_48b
import Proofs.Claims.Restated.Claim13beRoute3_49
import Proofs.Claims.Restated.Claim13beRoute3_50
import Proofs.Claims.Restated.Claim13beRoute3_50b
import Proofs.Claims.Restated.Claim13beRoute3_51
import Proofs.Claims.Restated.Claim13beRoute3_52
import Proofs.Claims.Restated.Claim13beRoute3_54
import Proofs.Claims.Restated.Claim13beRoute3_54b
import Proofs.Claims.Restated.Claim13beRoute3_55
import Proofs.Claims.Restated.Claim13beRoute3_56
import Proofs.Claims.Restated.Claim13beRoute3_57
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Proofs.Claims.Restated.Vocabulary_Execution_RecoveryActionLiveSourceSplit
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_Generic_EvaluationStore
import Proofs.Claims.Restated.Vocabulary_ModelVocabulary_Healing_Schedule
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_ProposalBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_RecoveryProposalConfirmationRead
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_ProposalParent
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_W4GSTZeroOpeningLifecycle
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreRoots
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_TickBridges
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_SlotInduction
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_42c
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.RunVocabulary
import Model.Conditions.Vocabulary_Internal_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Definitions_NamedLifecycle
import Model.Conditions.Vocabulary_Internal_Definitions_NamedProposalPivot
import Model.Conditions.Vocabulary_Internal_Definitions_NamedResult23Statements
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Internal_Internal_GradeReads
import Model.Conditions.Vocabulary_Internal_Invariants
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedHeadReads
import Proofs.Vocabulary.Internal.Legacy.Definitions.NamedVoteConsumers
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ProposalSourcesInternal
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Node
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Healing_Action
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_ModelVocabulary_Goldfish_ForkChoice
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Agreement
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_SGOpeningFrozenSuffix
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_SeedCeiling
import Proofs.Vocabulary.Protocol.ForkChoice.Views.ProposalCore
import Model.Conditions.Vocabulary_Protocol_Grades_GoldfishConePersistence
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Conditions.Vocabulary_Protocol_Grades_ProposalLifecycleCore
import Model.Conditions.Vocabulary_Protocol_Handlers_Blocks
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_Handlers_TickBridges
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_25
import Proofs.Claims.Spec2Claims.Claim13beRoute3_58

/-!
# Goldfish vote cones and the round ceiling

Theorems over a model `M : Record.Model V` and its facts `facts : Record.Facts M`, read along the
path `W` that the bundle `AdmissibleFieldsOn` binds: inequalities between a slot's instants, the
Goldfish cone step and its induction over slots, thin heads, the relay of a vote cone to the next
duty, and what the round ceiling `RoundCeilingAtOn` gives for the votes, confirmations and opening
proposal of a round.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- If `0 < q`, then `opening_slot q − 1 + 1 = opening_slot q`. -/
theorem openingSlot_pred_succ_l58 (facts : Record.Facts M) (S : Setup V) {q : Round} (hq : 0 < q) :
    (M.opening_slot S.hc q) - 1 + 1 = (M.opening_slot S.hc q) :=
  Nat.sub_add_cancel (Nat.succ_le_iff.mpr (facts.gr.openingSlot_pos_l58 S hq))

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- The opening slot of `q` is before the last slot of `q`. -/
theorem openingSlot_lt_seedRoundLastSlot_l58 (facts : Record.Facts M) (S : Setup V) (q : Round) :
    (M.opening_slot S.hc q) < Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q := by
  have h := facts.gr.firstInterior_lt_nextOpening_l86e S q
  show M.opening_slot S.hc q < M.opening_slot S.hc (q + 1) - 1
  exact Nat.lt_sub_of_add_lt h

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- The opening slot of `q` is at most the slot before the last slot of `q`. -/
theorem openingSlot_le_seedRoundLastSlot_pred_l58 (facts : Record.Facts M) (S : Setup V) (q : Round) :
    (M.opening_slot S.hc q) ≤ Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q - 1 :=
  Nat.le_pred_of_lt (Restated.openingSlot_lt_seedRoundLastSlot_l58 facts S q)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- A later slot has a later confirmation instant: if `a ≤ b`, then
    `confirmation_time a ≤ confirmation_time b`. -/
theorem confirmationTime_mono_l58 (facts : Record.Facts M) (E : Env V) {a b : Slot} (hab : a ≤ b) :
    M.confirmation_time E a ≤ M.confirmation_time E b := by
  rw [facts.sch.confirmation_time_eq_support_cutoff_succ,
    facts.sch.confirmation_time_eq_support_cutoff_succ]
  exact Restated.Vocabulary.Proofs.Optimistic.support_cutoff_mono facts E (Nat.add_le_add_right hab 1)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- The action instant of a round is the confirmation instant of its opening slot:
    `S.a q = confirmation_time (opening_slot q)`. -/
theorem a_eq_confirmation_opening_l58 (facts : Record.Facts M) (S : Setup V) (q : Round) :
    (Restated.Vocabulary.Execution.Setup.a M S q) = M.confirmation_time S.E ((M.opening_slot S.hc q)) := by
  rw [Restated.Vocabulary.Execution.Setup.a, Restated.Vocabulary.Protocol.a_eq_confirmation_time facts]

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- A later slot has a later vote instant: if `a ≤ b`, then `vote_time a ≤ vote_time b`. -/
theorem vote_time_mono_l58 (facts : Record.Facts M) (E : Env V) {a b : Slot} (hab : a ≤ b) :
    M.vote_time E a ≤ M.vote_time E b :=
  facts.sch.vote_time_mono_slots E hab

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- A slot's vote instant is at or before its view freeze: `vote_time s ≤ view_freeze s`. -/
theorem vote_time_le_view_freeze_l58 (facts : Record.Facts M) (E : Env V) (s : Slot) :
    M.vote_time E s ≤ M.view_freeze E s :=
  facts.sch.vote_time_le_view_freeze E s

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- A slot's vote instant is at or before the next slot's proposal instant:
    `vote_time s ≤ proposal_time (s + 1)`. -/
theorem vote_time_le_proposal_time_succ_l58 (facts : Record.Facts M) (E : Env V) (s : Slot) :
    M.vote_time E s ≤ M.proposal_time E (s + 1) :=
  le_of_lt (facts.sch.voteTime_lt_nextProposal_l86d E s)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- A slot's proposal instant is at or before its vote instant: `proposal_time s ≤ vote_time s`. -/
theorem proposal_time_le_vote_time_l58 (facts : Record.Facts M) (E : Env V) (s : Slot) :
    M.proposal_time E s ≤ M.vote_time E s :=
  le_of_lt (facts.sch.proposal_time_lt_vote_time E s)

end

/-! ## Helpers -/

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open scoped DC

/-- In a run sorted by key, the worlds strictly before the instant `t` are the worlds before the
    event whose index is `strictEventIndex rho t`. -/
private theorem stateBeforeTime_eq_strict₅₈ (S : Setup V) (rho : Record.Run V)
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
private theorem mem_stateBeforeTime_along₅₈ {S : Setup V} {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (t : Time) :
    W (strictEventIndex rho t) ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t := by
  rw [stateBeforeTime_eq_strict₅₈ S rho hsorted]
  exact (hW _).1

/-- On a path `W` of a run sorted by key, the node state staged at `t` from `v`'s node state in
    `W (strictEventIndex rho t)`, with an outcome `c` of the cache update there, is one of `v`'s
    prepared reads at `t`. -/
private theorem mkNode_mem_confirmationReadAt₅₈ {S : Setup V} {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (v : V)
    (t : Time) (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc (W (strictEventIndex rho t) v).st.core.toHealing t
      (W (strictEventIndex rho t) v).cache ⇢ c) :
    M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho t) v).st t)
        (W (strictEventIndex rho t) v).record c ∈
      Restated.Vocabulary.Execution.NamedActionReads.confirmationReadAt M S rho v t :=
  ⟨W (strictEventIndex rho t), mem_stateBeforeTime_along₅₈ hsorted hW t, c, hc, rfl⟩

omit [DecidableEq V] [Fintype V] in
/-- If `m` can return `a`, then `f <$> m` can return `f a`. -/
private theorem returns_map_intro₅₈ {α β : Type} (f : α → β) (m : DC.NDRE α) (a : α)
    (h : m ⇢ a) : (f <$> m) ⇢ f a := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image]
  exact ⟨_, h, rfl⟩

/-- For every node state `n`, the voter's filtered block tree of `n`'s core store at its slot, the
    voter's two vote views of it, and the in-tree head computed from them under the grade contract
    of `n`'s cache can each return a value. -/
private theorem voterHead_outcome₅₈ (facts : Record.Facts M) (S : Setup V) (n : M.N) :
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

/-- For every node state `n` and round `r`, the anchor of `n` at `r` can return some block. -/
private theorem nodeAnchor_outcome₅₈ (facts : Record.Facts M) (S : Setup V) (n : M.N)
    (r : Round) :
    ∃ A : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n r ⇢ A := by
  obtain ⟨G, hG⟩ := facts.gr.read_nonempty (M.gradeContract n.cache) S.E S.hc
    n.st.core.toHealing r
  exact ⟨G.anchor, returns_map_intro₅₈ (fun g : Protocol.GradeRead V => g.anchor) _ G hG⟩

/-- For every node state `x` and instant `t`, the cache update at `t` on `x` can return some cache
    `c`, and the filtered block tree and the FG root of the core store of the node state staged at
    `t` from `x` with `c` are those of the store `tickStore` stages at `t` from `x`'s core store. -/
private theorem exists_read_of_world₅₈ (facts : Record.Facts M) (S : Setup V) (x : M.N)
    (t : Time) :
    ∃ c : M.Cache, M.onPhaseTick S.E S.hc x.st.core.toHealing t x.cache ⇢ c ∧
      M.get_filtered_block_tree
          (M.toHealing (M.mkNode (M.ns_setClock S.E x.st t) x.record c).st.core).toFG =
        M.get_filtered_block_tree
          (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S x.st.core t)).toFG ∧
      M.get_fg_root (M.toHealing (M.mkNode (M.ns_setClock S.E x.st t) x.record c).st.core).toFG =
        M.get_fg_root (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S x.st.core t)).toFG := by
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc x.st.core.toHealing t x.cache
  refine ⟨c, hc, ?_, ?_⟩
  · rw [facts.nd.mkNode_st, facts.nd.store_with_cache_get_filtered_block_tree,
      Restated.Vocabulary.Proofs.Optimistic.tickStore, facts.hd.setClock_core_eq_store_with_t_s]
  · rw [facts.nd.mkNode_st, facts.nd.store_with_cache_get_fg_root,
      Restated.Vocabulary.Proofs.Optimistic.tickStore, facts.hd.setClock_core_eq_store_with_t_s]

/-- In a setup's schedule, slot `s`'s vote instant is at or before its view freeze. -/
private theorem vote_time_le_view_freeze₅₈ (facts : Record.Facts M) (S : Setup V) (s : Slot) :
    M.vote_time S.E s ≤ M.view_freeze S.E s :=
  le_of_lt ((Restated.vote_time_lt_support_cutoff_l49 facts S s).trans
    (facts.sch.Sts_support_cutoff_lt_view_freeze S.E s))

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- Under the bundle along `W`, if `v` is in the set for slot `s`'s support cutoff,
    `lo ≤ vote_time s`, the support cutoff is inside the horizon, the FG root of `v`'s store in
    `W (strictEventIndex rho (vote_time (s + 1)))` staged to `vote_time (s + 1)` is an ancestor of
    `B`, and every committee member of `s` in the set for `s`'s vote instant voted a run block with
    `B` as an ancestor, then every head voted by a committee member of `s` in the set for its
    confirmation instant is genesis or admitted by `v` before the support cutoff. -/
theorem honestHeadsAvailableBefore_of_namedPostHealingCone_coreOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {s : Slot} {v : V} (hv : v ∈ Hs (M.support_cutoff S.E s))
    (hpost : lo ≤ M.vote_time S.E s)
    (hhor : M.support_cutoff S.E s ≤ rho.horizon)
    {B : Block V}
    (hroot : Block.Preceq
      (M.get_fg_root
        (M.toHealing (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) v).st
          (M.vote_time S.E (s + 1))).core).toFG) B)
    (hnames : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s
      (fun X => Block.Preceq B X)) :
    ∀ X : Block V, Restated.HonestHeadOn M S rho W Hs Xb s X →
      X = Block.genesis ∨ Restated.Vocabulary.Protocol.AdmittedBefore M S rho W v X
        (M.support_cutoff S.E s) :=
  Restated.coreHonestHeadsAvailableOn facts S Hs Xb hf hHs hHsXb hv hpost hhor hroot hnames

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- Under the bundle along `W` and the hypotheses of
    `honestHeadsAvailableBefore_of_namedPostHealingCone_coreOn`, every head voted by a committee
    member of slot `s` in the set for its confirmation instant is genesis or admitted by `v` before
    `s`'s support cutoff. -/
theorem honestHeadsAvailableBefore_of_namedPostHealingConeOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {s : Slot} {v : V} (hv : v ∈ Hs (M.support_cutoff S.E s))
    (hpost : lo ≤ M.vote_time S.E s)
    (hhor : M.support_cutoff S.E s ≤ rho.horizon)
    {B : Block V}
    (hroot : Block.Preceq
      (M.get_fg_root
        (M.toHealing (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) v).st
          (M.vote_time S.E (s + 1))).core).toFG) B)
    (hnames : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s
      (fun X => Block.Preceq B X)) :
    ∀ X : Block V, Restated.HonestHeadOn M S rho W Hs Xb s X →
      X = Block.genesis ∨ Restated.Vocabulary.Protocol.AdmittedBefore M S rho W v X
        (M.support_cutoff S.E s) :=
  Restated.honestHeadsAvailableBefore_of_namedPostHealingCone_coreOn facts
    S Hs Xb hf hHs hHsXb hv hpost hhor hroot hnames

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- Under the bundle along `W`, if `lo ≤ vote_time s`, `confirmation_time s` is inside the horizon,
    every committee member of `s` in the set for `s`'s vote instant voted a run block with `C` as an
    ancestor, `H` is a head picked from `s`'s committee in the set for `confirmation_time s`, `w` is
    in the set for `support_cutoff s`, and the FG root of `w`'s vote-duty store of `s + 1` is an
    ancestor of `C`, then `H` is in every outcome of the voter's processed block tree of that store. -/
theorem honestHead_voterProcessed_at_nextDuty_of_postHealingConeOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {s : Slot} (hpost : lo ≤ M.vote_time S.E s)
    (hhor : M.confirmation_time S.E s ≤ rho.horizon)
    {C H : Block V}
    (hvotes : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s
      (fun X => Block.Preceq C X))
    (hH : Restated.HonestHeadOn M S rho W Hs Xb s H)
    {w : V} (hw : w ∈ Hs (M.support_cutoff S.E s))
    (hroot : Block.Preceq
      (M.get_fg_root
        (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1))).toFG) C) :
    let duty := Restated.Vocabulary.Proofs.Optimistic.voteStore M S
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1)
    ∀ P : Finset (Block V), M.voter_processed_block_tree S.E
      (M.toHealing duty).toFG.toSG.toGoldfishStore (M.toHealing duty).s ⇢ P → H ∈ P := by
  have hcore : Restated.Vocabulary.Proofs.Optimistic.voteStore M S
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1) =
      (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
        (M.vote_time S.E (s + 1))).core := by
    show Restated.Vocabulary.Proofs.Optimistic.tickStore M S _ _ = _
    rw [Restated.Vocabulary.Proofs.Optimistic.tickStore, facts.hd.setClock_core_eq_store_with_t_s]
  rw [hcore] at hroot
  exact Restated.coreHonestHeadProcessedAtNextDutyOn facts S Hs Xb hf hHs hHsXb hpost hhor hvotes hH
    hw hroot

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- Under the bundle along `W`, if `w` is in the set for `vote_time s`, `0 < s`, `w` is on `s`'s
    committee, `vote_time s` is inside the horizon, `lo ≤ vote_time s`, and `w`'s node state at each
    of its ticks at `vote_time s` passes the grade-1 awake test of `s`'s round, then every head of
    `w`'s vote-duty read of `s` is the erasure of a run block `C` read through `Xb` along `W`, and
    `w` emits along `W` at `vote_time s` the Goldfish vote of slot `s` for `C`'s root. -/
theorem named_voter_head_emitsOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {w : V} {s : Slot} (hw : w ∈ Hs (M.vote_time S.E s))
    (hs : 0 < s) (hcommittee : w ∈ S.E.committee s)
    (hhor : M.vote_time S.E s ≤ rho.horizon)
    (hgat : lo ≤ M.vote_time S.E s)
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.vote_time S.E s)) w).st.core.toHealing
      (M.vote_time S.E s)
      (W (strictEventIndex rho (M.vote_time S.E s)) w).cache ⇢ c)
    (hrun : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w (M.vote_time S.E s)) →
      M.awake_for_grade1 S w (W j w) (M.round_of S.hc s)) :
    let n := M.mkNode
      (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) w).st (M.vote_time S.E s))
      (W (strictEventIndex rho (M.vote_time S.E s)) w).record c
    ∀ T : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T →
    ∀ L : Finset (GoldfishVote V),
      M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
    ∀ L' : Finset (GoldfishVote V),
      M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
    ∀ Hd : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
        (M.toHealing n.st.core) T L L' (n.st.core.s - 1) ⇢ Hd →
    ∃ C : NamedBlock V, C.erase = Hd ∧
      Restated.blockInRunOn M S rho W Xb C ∧
      Restated.Vocabulary.Execution.NamedRun.emits M S rho W w
        (Object.gfVote ⟨w, s, C.erase.root⟩)
        (M.vote_time S.E s) :=
  Restated.coreVoterHeadEmitsOn facts S Hs Xb hf hHsXb hw hs hcommittee hhor hgat c hc hrun

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- Under the bundle along `W` and the committee majority, if `0 < s`, `lo ≤ vote_time s`,
    `confirmation_time s` is inside the horizon, every committee member of `s` in the set for `s`'s
    vote instant voted a run block with `C` as an ancestor, and `w`, in the set for
    `vote_time (s + 1)`, has the cone's vote inputs at `C`, then `w`'s vote-duty read of `s + 1` has
    cone support for `C`'s descendants over the set for `confirmation_time s`, a supporter majority
    for `C`, and every block between its anchor and `C` in its filtered tree, with a majority, and
    eligible. -/
theorem goldfishCone_pathEligible_coreOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {s : Slot} (hs : 0 < s)
    (hpost : lo ≤ M.vote_time S.E s)
    (hhor : M.confirmation_time S.E s ≤ rho.horizon)
    {C : Block V}
    (hnames : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s
      (fun X => Block.Preceq C X))
    {w : V} (hw : w ∈ Hs (M.vote_time S.E (s + 1)))
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
      (M.vote_time S.E (s + 1))
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ c)
    (hinputs : Restated.Vocabulary.Proofs.HealingSurface.GoldfishConeVoteInputs M S rho s C w
      (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
        (M.vote_time S.E (s + 1))) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c)) :
    let n := M.mkNode
      (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
        (M.vote_time S.E (s + 1)))
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c
    let st := n.st.core
    ∀ votes : Finset (GoldfishVote V),
      M.voter_view S.E (M.toHealing st).toFG.toSG.toGoldfishStore st.s ⇢ votes →
    ∀ support : Finset (GoldfishVote V),
      M.voter_support_view S.E (M.toHealing st).toFG.toSG.toGoldfishStore st.s ⇢ support →
    Restated.Vocabulary.Proofs.Optimistic.ConeSupport M S.E st.T votes support votes (st.s - 1)
        (Hs (M.confirmation_time S.E s)) (fun X => Block.Preceq C X) ∧
      (∀ sup : Finset V, Restated.Vocabulary.Protocol.goldfishSupporters M S.E st.T votes support
          (st.s - 1) C ⇢ sup →
        M.voters_count S.E votes (st.s - 1) < 2 * sup.card) ∧
      ∀ A : Block V,
        Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n (M.round_of S.hc st.s) ⇢ A →
      ∀ D : Block V, Block.Preceq A D → D ≠ A → Block.Preceq D C →
        (∀ T : Finset (Block V), M.voter_filtered_block_tree S.E st st.s ⇢ T → D ∈ T) ∧
          ((st.σ D.parent).h < st.h_max - 1 ∨
            ∀ g : Nat, M.goldfish_score S.E st.T votes support (st.s - 1) D ⇢ g →
              M.voters_count S.E votes (st.s - 1) < 2 * g) ∧
          ∀ b : Bool, M.goldfish_eligible S.E st.σ st.h_max st.T st.s
            votes support (st.s - 1) D ⇢ b → b = true :=
  Restated.coreGoldfishConePathEligibleOn facts S Hs Xb hf hHs hHsXb hcom hs hpost hhor hnames
    hw c hc hinputs

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- Under the bundle along `W` and the hypotheses of `goldfishCone_pathEligible_coreOn`, `w`'s
    vote-duty read of `s + 1` has cone support for `C`'s descendants, a supporter majority for `C`,
    and every block between its anchor and `C` in its filtered tree, with a majority, and eligible. -/
theorem goldfishCone_pathEligibleOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {s : Slot} (hs : 0 < s)
    (hpost : lo ≤ M.vote_time S.E s)
    (hhor : M.confirmation_time S.E s ≤ rho.horizon)
    {C : Block V}
    (hnames : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s
      (fun X => Block.Preceq C X))
    {w : V} (hw : w ∈ Hs (M.vote_time S.E (s + 1)))
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
      (M.vote_time S.E (s + 1))
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ c)
    (hinputs : Restated.Vocabulary.Proofs.HealingSurface.GoldfishConeVoteInputs M S rho s C w
      (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
        (M.vote_time S.E (s + 1))) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c)) :
    let n := M.mkNode
      (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
        (M.vote_time S.E (s + 1)))
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c
    let st := n.st.core
    ∀ votes : Finset (GoldfishVote V),
      M.voter_view S.E (M.toHealing st).toFG.toSG.toGoldfishStore st.s ⇢ votes →
    ∀ support : Finset (GoldfishVote V),
      M.voter_support_view S.E (M.toHealing st).toFG.toSG.toGoldfishStore st.s ⇢ support →
    Restated.Vocabulary.Proofs.Optimistic.ConeSupport M S.E st.T votes support votes (st.s - 1)
        (Hs (M.confirmation_time S.E s)) (fun X => Block.Preceq C X) ∧
      (∀ sup : Finset V, Restated.Vocabulary.Protocol.goldfishSupporters M S.E st.T votes support
          (st.s - 1) C ⇢ sup →
        M.voters_count S.E votes (st.s - 1) < 2 * sup.card) ∧
      ∀ A : Block V,
        Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n (M.round_of S.hc st.s) ⇢ A →
      ∀ D : Block V, Block.Preceq A D → D ≠ A → Block.Preceq D C →
        (∀ T : Finset (Block V), M.voter_filtered_block_tree S.E st st.s ⇢ T → D ∈ T) ∧
          ((st.σ D.parent).h < st.h_max - 1 ∨
            ∀ g : Nat, M.goldfish_score S.E st.T votes support (st.s - 1) D ⇢ g →
              M.voters_count S.E votes (st.s - 1) < 2 * g) ∧
          ∀ b : Bool, M.goldfish_eligible S.E st.σ st.h_max st.T st.s
            votes support (st.s - 1) D ⇢ b → b = true :=
  Restated.goldfishCone_pathEligible_coreOn facts S Hs Xb hf hHs hHsXb hcom hs hpost hhor
    hnames hw c hc hinputs

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- Under the bundle along `W` and the committee majority, if `0 < s`, `lo ≤ vote_time s`,
    `confirmation_time s` is inside the horizon, every committee member of `s` in the set for `s`'s
    vote instant voted a run block with `C` as an ancestor, and `w`, in the set for
    `vote_time (s + 1)`, has the cone's vote inputs at `C`, then `C` is an ancestor of every head of
    `w`'s vote-duty read of slot `s + 1`. -/
theorem goldfishCone_stepOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {s : Slot} (hs : 0 < s)
    (hpost : lo ≤ M.vote_time S.E s)
    (hhor : M.confirmation_time S.E s ≤ rho.horizon)
    {C : Block V}
    (hnames : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s
      (fun X => Block.Preceq C X))
    {w : V} (hw : w ∈ Hs (M.vote_time S.E (s + 1)))
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
      (M.vote_time S.E (s + 1))
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ c)
    (hinputs : Restated.Vocabulary.Proofs.HealingSurface.GoldfishConeVoteInputs M S rho s C w
      (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
        (M.vote_time S.E (s + 1))) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c)) :
    let n := M.mkNode
      (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
        (M.vote_time S.E (s + 1)))
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c
    ∀ T : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T →
    ∀ L : Finset (GoldfishVote V),
      M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
    ∀ L' : Finset (GoldfishVote V),
      M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
    ∀ H : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
        (M.toHealing n.st.core) T L L' (n.st.core.s - 1) ⇢ H →
      Block.Preceq C H :=
  Restated.goldfishCone_stepOn'_WeakGoldfishCone facts S Hs Xb hf hHs hHsXb hcom hs hpost hhor
    hnames hw c hc
    { rootSide := fun A hA T hT =>
        Or.inl ⟨hinputs.root, hinputs.candidate T hT,
          fun D hAD hDA hDC hDne => hinputs.path A hA T hT D hAD hDA hDC hDne⟩
      anchor := hinputs.anchor }

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- Under the bundle along `W` and the committee majority, if `0 < s`, `lo ≤ vote_time s`,
    `confirmation_time s` is inside the horizon, every committee member of `s` in the set for `s`'s
    vote instant voted a run block with `C` as an ancestor, and `w`, in the set for
    `vote_time (s + 1)`, has the cone's root-side vote inputs at `C`, then `C` is an ancestor of
    every head of `w`'s vote-duty read of slot `s + 1`. -/
theorem goldfishCone_stepOn'_GoldfishCone (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {s : Slot} (hs : 0 < s)
    (hpost : lo ≤ M.vote_time S.E s)
    (hhor : M.confirmation_time S.E s ≤ rho.horizon)
    {C : Block V}
    (hnames : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s
      (fun X => Block.Preceq C X))
    {w : V} (hw : w ∈ Hs (M.vote_time S.E (s + 1)))
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
      (M.vote_time S.E (s + 1))
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ c)
    (hinputs : Restated.Vocabulary.Proofs.HealingSurface.GoldfishConeVoteInputs' M S rho s C w
      (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
        (M.vote_time S.E (s + 1))) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c)) :
    let n := M.mkNode
      (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
        (M.vote_time S.E (s + 1)))
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c
    ∀ T : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T →
    ∀ L : Finset (GoldfishVote V),
      M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
    ∀ L' : Finset (GoldfishVote V),
      M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
    ∀ H : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
        (M.toHealing n.st.core) T L L' (n.st.core.s - 1) ⇢ H →
      Block.Preceq C H :=
  Restated.goldfishCone_stepOn'_WeakGoldfishCone facts S Hs Xb hf hHs hHsXb hcom hs hpost hhor
    hnames hw c hc hinputs

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- Under the bundle along `W` and the committee majority, if `0 < s0`, `lo ≤ vote_time s0`,
    `confirmation_time s1` is inside the horizon, every committee member of `s0` in the set for its
    vote instant voted a run block with `C` as an ancestor, every slot from `s0` to `s1` has the
    cone's slot inputs at `C`, and the committee members of each later slot pass the grade-1 awake
    test at their vote ticks, then every slot from `s0` to `s1 + 1` has that vote cone, and for
    every slot `s` from `s0` to `s1`, every block confirmed (`GenuineConfirmationWith`) by the store
    a member of the set for `confirmation_time s` stages at that instant is a descendant of `C`. -/
theorem goldfishCone_inductionOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {s0 s1 : Slot} (hs0 : 0 < s0)
    (hpost : lo ≤ M.vote_time S.E s0)
    (hhor : M.confirmation_time S.E s1 ≤ rho.horizon)
    {C : Block V}
    (hseed : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s0
      (fun X => Block.Preceq C X))
    (hsupply : ∀ s : Slot, s0 ≤ s → s ≤ s1 →
      Restated.GoldfishConeSlotInputsOn M S rho (fun t => W (strictEventIndex rho t)) Hs s C)
    (hrun : ∀ s : Slot, s0 < s → s ≤ s1 + 1 → ∀ w ∈ S.E.committee s, w ∈ Hs (M.vote_time S.E s) →
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w (M.vote_time S.E s)) →
        M.awake_for_grade1 S w (W j w) (M.round_of S.hc s)) :
    (∀ s : Slot, s0 ≤ s → s ≤ s1 + 1 →
      Restated.NamedHonestVotesConeOn M S rho W Hs Xb s (fun X => Block.Preceq C X)) ∧
    (∀ s : Slot, s0 ≤ s → s ≤ s1 → ∀ w ∈ Hs (M.confirmation_time S.E s),
      ∀ c : M.Cache, M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.confirmation_time S.E s)) w).st.core.toHealing
        (M.confirmation_time S.E s)
        (W (strictEventIndex rho (M.confirmation_time S.E s)) w).cache ⇢ c →
      ∀ D : Block V,
        Restated.Vocabulary.Protocol.GenuineConfirmationWith M (M.gradeContract c) S.E S.hc
          (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
            (W (strictEventIndex rho (M.confirmation_time S.E s)) w).st.core
            (M.confirmation_time S.E s)) s D →
        Block.Preceq C D) := by
  have hfold : ∀ n : Nat, s0 + n ≤ s1 + 1 →
      Restated.NamedHonestVotesConeOn M S rho W Hs Xb (s0 + n) (fun X => Block.Preceq C X) := by
    intro n
    induction n with
    | zero =>
        intro _
        simpa only [Nat.add_zero] using hseed
    | succ n ih =>
        intro hupper
        let s := s0 + n
        have hsLe : s ≤ s1 := by
          have hupper' : (s0 + n) + 1 ≤ s1 + 1 := by
            simpa only [Nat.add_succ] using hupper
          simpa only [s] using Nat.le_of_succ_le_succ hupper'
        have hprev : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s
            (fun X => Block.Preceq C X) := by
          simpa only [s] using ih (hsLe.trans (Nat.le_succ s1))
        have hsPos : 0 < s := hs0.trans_le (Nat.le_add_right s0 n)
        have hpostS : lo ≤ M.vote_time S.E s :=
          hpost.trans (Restated.vote_time_mono_l58 facts S.E (Nat.le_add_right s0 n))
        have hhorS : M.confirmation_time S.E s ≤ rho.horizon :=
          (Restated.confirmationTime_mono_l58 facts S.E hsLe).trans hhor
        have hvoteNextHor : M.vote_time S.E (s + 1) ≤ rho.horizon :=
          le_trans (le_trans (le_of_lt (lt_add_of_pos_right _ S.E.Δ_pos))
            (facts.sch.vote_time_succ_add_delta_le_confirmation_time S.E s)) hhorS
        have hpostNext : lo ≤ M.vote_time S.E (s + 1) :=
          hpostS.trans (Restated.vote_time_mono_l58 facts S.E (Nat.le_succ s))
        intro w hw hwcommittee
        have hw' : w ∈ Hs (M.vote_time S.E (s + 1)) := hw
        obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
          (M.vote_time S.E (s + 1)) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache
        obtain ⟨T, L, L', Hd, hT, hL, hL', hHd⟩ := voterHead_outcome₅₈ facts S
          (M.mkNode
            (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
              (M.vote_time S.E (s + 1)))
            (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c)
        obtain ⟨X, hCX, hXrun, hXemit⟩ := Restated.named_voter_head_emitsOn facts S Hs Xb hf
          hHsXb (s := s + 1) hw' (Nat.succ_pos s) hwcommittee hvoteNextHor hpostNext c hc
          (hrun (s + 1) (Nat.lt_succ_of_le (Nat.le_add_right s0 n))
            (Nat.succ_le_succ hsLe) w hwcommittee hw')
          T hT L hL L' hL' Hd hHd
        have hhead : Block.Preceq C X.erase := by
          rw [hCX]
          exact Restated.goldfishCone_stepOn facts S Hs Xb hf hHs hHsXb hcom hsPos hpostS hhorS
            hprev hw' c hc ((hsupply s (Nat.le_add_right s0 n) hsLe).vote w hw' c hc) T hT L hL L' hL'
            Hd hHd
        exact ⟨X, hhead, hXrun, hXemit⟩
  have hvotes : ∀ s : Slot, s0 ≤ s → s ≤ s1 + 1 →
      Restated.NamedHonestVotesConeOn M S rho W Hs Xb s (fun X => Block.Preceq C X) := by
    intro s hs0s hss1
    have heq : s0 + (s - s0) = s := Nat.add_sub_of_le hs0s
    simpa only [heq] using hfold (s - s0) (by simpa only [heq] using hss1)
  refine ⟨hvotes, ?_⟩
  intro s hs0s hss1 w hw c hc D hgenuine
  have hsPos : 0 < s := hs0.trans_le hs0s
  have hpostS : lo ≤ M.vote_time S.E s :=
    hpost.trans (Restated.vote_time_mono_l58 facts S.E hs0s)
  have hhorS : M.confirmation_time S.E s ≤ rho.horizon :=
    (Restated.confirmationTime_mono_l58 facts S.E hss1).trans hhor
  exact Restated.goldfishCone_confirmationOn facts S Hs Xb hf hHs hHsXb hcom hsPos hpostS hhorS
    (hvotes s hs0s (hss1.trans (Nat.le_succ s1)))
    (hHs _ _ (facts.sch.Sts_support_cutoff_le_confirmation_time S.E s) hw)
    c hc ((hsupply s hs0s hss1).confirmation w hw c hc) hgenuine

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

/-- Under the committee majority, if `C` is a run block read through `Xb` of height at least
    `Mh − 1`, and every committee member of `s` in the set for `s`'s vote instant voted along `W` a
    run block with `C` as an ancestor, then some head picked from `s`'s committee in the set for
    `confirmation_time s` is a descendant of `C` of height at least `Mh − 1`. -/
theorem thinHonestHeadAt_of_thin_endpointOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {s : Slot} {C : NamedBlock V} {Mh : Height}
    (hCrun : Restated.RunBlockOn M S rho W Xb C)
    (hCheight : Mh - 1 ≤ (M.derive_named S.E S.cfg C).h)
    (hvotes : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s (fun X => Block.Preceq C.erase X)) :
    Restated.ThinHonestHeadAtOn M S rho W Hs Xb Mh s C.erase := by
  have hpositive : 0 < ((S.E.committee s) ∩ Hs (M.confirmation_time S.E s)).card := by
    have hc := hcom s
    omega
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hpositive
  have hwCommittee : w ∈ S.E.committee s := (Finset.mem_inter.mp hw).1
  have hwHonest : w ∈ Hs (M.confirmation_time S.E s) := (Finset.mem_inter.mp hw).2
  obtain ⟨H, hCH, hHrun, hHemit⟩ := hvotes w
    (hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E s) hwHonest) hwCommittee
  have hnamed : NamedBlock.Preceq C H :=
    Restated.namedPreceq_of_runBlock_erase_preceqOn facts Hs Xb hf hCrun hHrun hCH
  exact ⟨H, ⟨w, hwHonest, hwCommittee, hHrun, hHemit⟩, hCH,
    hCheight.trans
      (facts.cs.derive_height_mono S.E S.cfg hnamed)⟩

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

/-- For worlds `Wt` before each instant, if `0 < q`, every read from `Wt` of every member of the set
    for the opening slot's vote instant has the boundary step's vote inputs at `C`, every slot of
    round `q` before its last has the cone's slot inputs at `C`, and `C` is in the filtered tree of
    every round-`q` action store and of the opening proposer's duty store, then `C` is a descendant
    of every finality root and a member of every filtered tree read from `Wt` in round `q`
    (`RoundCeilingAboveRootAtOn`, `RoundCeilingActiveAtOn`). -/
theorem roundCeiling_readSupport_of_inputsOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} {Wt : Time → V → M.N} (Hs : Int → Finset V) {q : Round} {C : Block V}
    (hq : 0 < q)
    (hopening : ∀ w ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc q) - 1 + 1)), ∀ c : M.Cache,
      M.onPhaseTick S.E S.hc (Wt (M.vote_time S.E ((M.opening_slot S.hc q) - 1 + 1)) w).st.core.toHealing
        (M.vote_time S.E ((M.opening_slot S.hc q) - 1 + 1))
        (Wt (M.vote_time S.E ((M.opening_slot S.hc q) - 1 + 1)) w).cache ⇢ c →
      Restated.Vocabulary.Proofs.HealingSurface.GoldfishConeVoteInputs M S rho ((M.opening_slot S.hc q) - 1) C w
        (M.mkNode (M.ns_setClock S.E (Wt (M.vote_time S.E ((M.opening_slot S.hc q) - 1 + 1)) w).st
          (M.vote_time S.E ((M.opening_slot S.hc q) - 1 + 1)))
          (Wt (M.vote_time S.E ((M.opening_slot S.hc q) - 1 + 1)) w).record c))
    (hround : ∀ s : Slot,
      (M.opening_slot S.hc q) ≤ s → s < Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q →
        Restated.GoldfishConeSlotInputsOn M S rho Wt Hs s C)
    (haction : ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
      C ∈ M.get_filtered_block_tree
        (M.toHealing (Wt (Restated.Vocabulary.Execution.Setup.a M S q) w).st.core).toFG)
    (hproposer : S.E.proposer ((M.opening_slot S.hc q)) ∈
        Hs (M.confirmation_time S.E ((M.opening_slot S.hc q))) →
      C ∈ M.get_filtered_block_tree (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (Wt (M.proposal_time S.E (M.opening_slot S.hc q)) (S.E.proposer (M.opening_slot S.hc q))).st.core
        (M.proposal_time S.E (M.opening_slot S.hc q)))).toFG) :
    Restated.RoundCeilingAboveRootAtOn M S rho Wt Hs q C ∧
      Restated.RoundCeilingActiveAtOn M S rho Wt Hs q C := by
  have hvote : ∀ d : Slot,
      (M.opening_slot S.hc q) ≤ d → d ≤ Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q →
        ∀ w ∈ Hs (M.vote_time S.E d), ∀ c : M.Cache,
          M.onPhaseTick S.E S.hc (Wt (M.vote_time S.E d) w).st.core.toHealing (M.vote_time S.E d)
            (Wt (M.vote_time S.E d) w).cache ⇢ c →
          Restated.Vocabulary.Proofs.HealingSurface.GoldfishConeVoteInputs M S rho (d - 1) C w
            (M.mkNode (M.ns_setClock S.E (Wt (M.vote_time S.E d) w).st (M.vote_time S.E d))
              (Wt (M.vote_time S.E d) w).record c) := by
    intro d hdlo hdhi w hw
    have hdpos : 0 < d := lt_of_lt_of_le (facts.gr.openingSlot_pos_l58 S hq) hdlo
    have hsucc : d - 1 + 1 = d := Nat.sub_add_cancel (Nat.succ_le_iff.mpr hdpos)
    by_cases heq : d = (M.opening_slot S.hc q)
    · subst heq
      have h := hopening w (by rw [Restated.openingSlot_pred_succ_l58 facts S hq]; exact hw)
      rw [Restated.openingSlot_pred_succ_l58 facts S hq] at h
      exact h
    · have hdlt : (M.opening_slot S.hc q) < d :=
        lt_of_le_of_ne hdlo (Ne.symm heq)
      have hpredLo : (M.opening_slot S.hc q) ≤ d - 1 := Nat.le_pred_of_lt hdlt
      have hpredLt : d - 1 < Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q :=
        lt_of_lt_of_le (Nat.sub_lt hdpos Nat.zero_lt_one) hdhi
      have h := (hround (d - 1) hpredLo hpredLt).vote w (by rw [hsucc]; exact hw)
      rw [hsucc] at h
      exact h
  have hactive : Restated.RoundCeilingActiveAtOn M S rho Wt Hs q C :=
    { voteDuty := by
        intro d hdlo hdhi w hw
        obtain ⟨c, hc, hcore, -⟩ := exists_read_of_world₅₈ facts S (Wt (M.vote_time S.E d) w)
          (M.vote_time S.E d)
        have hin := hvote d hdlo hdhi w hw c hc
        obtain ⟨T, hT⟩ := facts.fc.voter_filtered_block_tree_nonempty S.E
          (M.mkNode (M.ns_setClock S.E (Wt (M.vote_time S.E d) w).st (M.vote_time S.E d))
            (Wt (M.vote_time S.E d) w).record c).st.core
          (M.mkNode (M.ns_setClock S.E (Wt (M.vote_time S.E d) w).st (M.vote_time S.E d))
            (Wt (M.vote_time S.E d) w).record c).st.core.s
        have h := facts.fc.voter_filtered_block_tree_subset_filtered S.E _ T hT (hin.candidate T hT)
        rw [hcore] at h
        exact h
      confirmation := by
        intro s hslo hshi w hw
        obtain ⟨c, hc, hcore, -⟩ := exists_read_of_world₅₈ facts S (Wt (M.confirmation_time S.E s) w)
          (M.confirmation_time S.E s)
        have h := ((hround s hslo hshi).confirmation w hw c hc).candidate
        unfold Restated.Vocabulary.Internal.PhaseGrades.filteredTree at h
        rw [hcore] at h
        exact h
      action := haction
      proposer := hproposer }
  refine ⟨?_, hactive⟩
  exact
    { voteDuty := by
        intro d hdlo hdhi w hw
        obtain ⟨c, hc, -, hcore⟩ := exists_read_of_world₅₈ facts S (Wt (M.vote_time S.E d) w)
          (M.vote_time S.E d)
        have h := (hvote d hdlo hdhi w hw c hc).root
        rw [hcore] at h
        exact h
      confirmation := by
        intro s hslo hshi w hw
        obtain ⟨c, hc, -, hcore⟩ := exists_read_of_world₅₈ facts S (Wt (M.confirmation_time S.E s) w)
          (M.confirmation_time S.E s)
        have h := ((hround s hslo hshi).confirmation w hw c hc).root
        rw [hcore] at h
        exact h
      action := by
        intro w hw
        exact preceq_eq_true_iff_Preceq.1
          (facts.fc.preceq_get_fg_root_of_mem_filtered (haction w hw))
      proposer := by
        intro hp
        exact preceq_eq_true_iff_Preceq.1
          (facts.fc.preceq_get_fg_root_of_mem_filtered (hproposer hp)) }

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

/-- Under the bundle along `W`, if `w` is in the set for `vote_time d`, `0 < d`, `w` is on `d`'s
    committee, `vote_time d` is inside the horizon, `lo ≤ vote_time d`, and `w`'s node state at each
    of its ticks at `vote_time d` passes the grade-1 awake test of `d`'s round, then `w` emits along
    `W` at `vote_time d` the Goldfish vote of slot `d` for every head of its vote-duty read. -/
theorem seedVoteDutyHead_emitsOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {w : V} {d : Slot} (hw : w ∈ Hs (M.vote_time S.E d)) (hd : 0 < d)
    (hwCommittee : w ∈ S.E.committee d)
    (hhor : M.vote_time S.E d ≤ rho.horizon)
    (hgat : lo ≤ M.vote_time S.E d)
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core.toHealing
      (M.vote_time S.E d)
      (W (strictEventIndex rho (M.vote_time S.E d)) w).cache ⇢ c)
    (hrun : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w (M.vote_time S.E d)) →
      M.awake_for_grade1 S w (W j w) (M.round_of S.hc d)) :
    let n := M.mkNode
      (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st (M.vote_time S.E d))
      (W (strictEventIndex rho (M.vote_time S.E d)) w).record c
    ∀ T : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T →
    ∀ L : Finset (GoldfishVote V),
      M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
    ∀ L' : Finset (GoldfishVote V),
      M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
    ∀ H : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
        (M.toHealing n.st.core) T L L' (n.st.core.s - 1) ⇢ H →
      Restated.Vocabulary.Execution.Run.emits M S rho W w
        (Object.gfVote ⟨w, d, H.root⟩)
        (M.vote_time S.E d) :=
  Restated.voterHead_emits_of_coreOn facts S Hs Xb hf hw hd hwCommittee hhor hgat c hc hrun

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

/-- If `w ∈ Xb`, every head of `w`'s vote-duty read of slot `d`, staged from
    `W (strictEventIndex rho (vote_time d))`, is the erasure of a run block read through `Xb` along
    `W`. -/
theorem seedVoteDutyHead_runBlockOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {w : V} (hw : w ∈ Xb) (d : Slot)
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core.toHealing
      (M.vote_time S.E d)
      (W (strictEventIndex rho (M.vote_time S.E d)) w).cache ⇢ c) :
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
    ∃ H : NamedBlock V, H.erase = Hd ∧ Restated.RunBlockOn M S rho W Xb H :=
  Restated.voterHead_runBlock_of_coreOn facts S Hs Xb hf hw d c hc

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

/-- Under the bundle along `W`, if `vote_time (s + 1)` is inside the horizon, every member of the
    set for `vote_time (s + 1)` has the cone's vote inputs at `C`, every anchor outcome of its
    vote-duty read of `s + 1` is an ancestor of `C`, and its vote store of `s + 1` has `h_max` equal
    to `Mh`, the committee members of `s + 1` pass the grade-1 awake test at their vote ticks, `X`
    is a head picked from the committee of `s + 1` in the set for its confirmation instant, and
    `lo ≤ view_freeze s`, then `X` has height at least `Mh − 1`. -/
theorem seedHeadThin_of_voteInputsOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {Mh : Height} {s : Slot} {C : Block V}
    (hhor : M.vote_time S.E (s + 1) ≤ rho.horizon)
    (hinputs : ∀ w ∈ Hs (M.vote_time S.E (s + 1)), ∀ c : M.Cache,
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
        (M.vote_time S.E (s + 1))
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ c →
      Restated.Vocabulary.Proofs.HealingSurface.GoldfishConeVoteInputs M S rho s C w
        (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
          (M.vote_time S.E (s + 1))) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c))
    (hanchor : ∀ w ∈ Hs (M.vote_time S.E (s + 1)), ∀ c : M.Cache,
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
        (M.vote_time S.E (s + 1))
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ c →
      let n := M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
          (M.vote_time S.E (s + 1)))
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c
      ∀ A : Block V,
        Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n (M.round_of S.hc n.st.core.s) ⇢ A →
        Block.Preceq A C)
    (hfrontier : ∀ w ∈ Hs (M.vote_time S.E (s + 1)),
      (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1)).h_max = Mh)
    {X : NamedBlock V} (hX : Restated.NamedHonestHeadOn M S rho W Hs Xb (s + 1) X)
    (hgat : lo ≤ M.view_freeze S.E s)
    (hrun : ∀ w ∈ S.E.committee (s + 1), w ∈ Hs (M.vote_time S.E (s + 1)) →
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w (M.vote_time S.E (s + 1))) →
        M.awake_for_grade1 S w (W j w) (M.round_of S.hc (s + 1))) :
    Mh - 1 ≤ (M.derive_named S.E S.cfg X).h := by
  obtain ⟨w, hwConf, hwCommittee, hXrun, hXemit⟩ := hX
  have hw : w ∈ Hs (M.vote_time S.E (s + 1)) :=
    hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E (s + 1)) hwConf
  have hfreezeVote : M.view_freeze S.E s ≤ M.vote_time S.E (s + 1) :=
    le_of_lt (facts.sch.view_freeze_lt_vote_time_succ S.E s)
  have hwFreeze : w ∈ Hs (M.view_freeze S.E s) := hHs _ _ hfreezeVote hw
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
    (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
    (M.vote_time S.E (s + 1)) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache
  obtain ⟨T, L, L', Hd, hT, hL, hL', hHd⟩ := voterHead_outcome₅₈ facts S
    (M.mkNode
      (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
        (M.vote_time S.E (s + 1)))
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c)
  obtain ⟨A, hA⟩ := nodeAnchor_outcome₅₈ facts S
    (M.mkNode
      (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
        (M.vote_time S.E (s + 1)))
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c)
    (M.round_of S.hc (M.mkNode
      (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
        (M.vote_time S.E (s + 1)))
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c).st.core.s)
  have hYemit :=
    Restated.seedVoteDutyHead_emitsOn facts S Hs Xb hf hw (Nat.succ_pos s) hwCommittee hhor
      (hgat.trans hfreezeVote) c hc (hrun w hwCommittee hw) T hT L hL L' hL' Hd hHd
  have hrootEq : X.erase.root = Hd.root :=
    congrArg GoldfishVote.head
      (Restated.emits_gfVote_uniqueOn facts S Hs Xb hf hXemit hYemit rfl)
  obtain ⟨H, hHerase, hHrun, hfloor⟩ :=
    Restated.voteDutyHead_height_ge_frontier_sub_one_of_candidateOn facts
      S Hs Xb hf hHsXb hwFreeze c hc (hinputs w hw c hc) A hA (hanchor w hw c hc A hA) hgat
      T hT L hL L' hL' Hd hHd
  have hrootNamed : X.root = H.root := by
    rw [← Proofs.NamedWire.erase_root X, ← Proofs.NamedWire.erase_root H, hHerase]
    exact hrootEq
  have hXH : X = H :=
    hf.rootCollisionFree.root_injective
      X H hXrun hHrun X H (Or.inl (Proofs.NamedAncestry.named_self X))
      (Or.inr (Proofs.NamedAncestry.named_self H)) hrootNamed
  rw [hXH]
  rw [hfrontier w hw] at hfloor
  exact hfloor

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

/-- Under the committee majority and the hypotheses of `seedHeadThin_of_voteInputsOn`, if every
    committee member of `s + 1` in the set for its vote instant voted along `W` a run block with `E`
    as an ancestor, then some head picked from the committee of `s + 1` in the set for its
    confirmation instant is a descendant of `E` of height at least `Mh − 1`. -/
theorem seedThinHead_of_voteInputsOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {Mh : Height} {s : Slot} {C E : Block V}
    (hhor : M.vote_time S.E (s + 1) ≤ rho.horizon)
    (hinputs : ∀ w ∈ Hs (M.vote_time S.E (s + 1)), ∀ c : M.Cache,
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
        (M.vote_time S.E (s + 1))
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ c →
      Restated.Vocabulary.Proofs.HealingSurface.GoldfishConeVoteInputs M S rho s C w
        (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
          (M.vote_time S.E (s + 1))) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c))
    (hanchor : ∀ w ∈ Hs (M.vote_time S.E (s + 1)), ∀ c : M.Cache,
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
        (M.vote_time S.E (s + 1))
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ c →
      let n := M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
          (M.vote_time S.E (s + 1)))
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c
      ∀ A : Block V,
        Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n (M.round_of S.hc n.st.core.s) ⇢ A →
        Block.Preceq A C)
    (hfrontier : ∀ w ∈ Hs (M.vote_time S.E (s + 1)),
      (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1)).h_max = Mh)
    (hcone : Restated.NamedHonestVotesConeOn M S rho W Hs Xb (s + 1) (fun X => Block.Preceq E X))
    (hgat : lo ≤ M.view_freeze S.E s)
    (hrun : ∀ w ∈ S.E.committee (s + 1), w ∈ Hs (M.vote_time S.E (s + 1)) →
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w (M.vote_time S.E (s + 1))) →
        M.awake_for_grade1 S w (W j w) (M.round_of S.hc (s + 1))) :
    Restated.ThinHonestHeadAtOn M S rho W Hs Xb Mh (s + 1) E := by
  have hpositive :
      0 < ((S.E.committee (s + 1)) ∩ Hs (M.confirmation_time S.E (s + 1))).card := by
    have hc := hcom (s + 1)
    omega
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hpositive
  have hwCommittee : w ∈ S.E.committee (s + 1) := (Finset.mem_inter.mp hw).1
  have hwHonest : w ∈ Hs (M.confirmation_time S.E (s + 1)) := (Finset.mem_inter.mp hw).2
  obtain ⟨X, hEX, hXrun, hXemit⟩ := hcone w
    (hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E (s + 1)) hwHonest) hwCommittee
  have hX : Restated.NamedHonestHeadOn M S rho W Hs Xb (s + 1) X :=
    ⟨w, hwHonest, hwCommittee, hXrun, hXemit⟩
  exact ⟨X, hX, hEX,
    Restated.seedHeadThin_of_voteInputsOn facts S Hs Xb hf hHs hHsXb hhor hinputs hanchor
      hfrontier hX hgat hrun⟩

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

/-- If `RoundCeilingAtOn` holds at `q` for `C`, `d` is a slot of round `q` and `w` is in the set for
    `vote_time d`, then every read of `w` staged from `Wt (vote_time d)` has the cone's vote inputs
    at `C` for slot `d − 1`. -/
theorem roundCeiling_voteInputsOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V)
    {W : Nat → V → M.N} {Wt : Time → V → M.N} {Mh : Height} {q : Round} {C : NamedBlock V}
    (h : Restated.RoundCeilingAtOn M S rho W Wt Hs Xb Mh q C)
    {d : Slot} (hdlo : (M.opening_slot S.hc q) ≤ d)
    (hdhi : d ≤ Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q)
    {w : V} (hw : w ∈ Hs (M.vote_time S.E d)) :
    ∀ c : M.Cache, M.onPhaseTick S.E S.hc
        (Wt (M.vote_time S.E d) w).st.core.toHealing (M.vote_time S.E d)
        (Wt (M.vote_time S.E d) w).cache ⇢ c →
      Restated.Vocabulary.Proofs.HealingSurface.GoldfishConeVoteInputs M S rho (d - 1) C.erase w
        (M.mkNode (M.ns_setClock S.E (Wt (M.vote_time S.E d) w).st
          (M.vote_time S.E d)) (Wt (M.vote_time S.E d) w).record c) := by
  have hdpos : 0 < d := lt_of_lt_of_le (facts.gr.openingSlot_pos_l58 S h.roundPositive) hdlo
  have hsucc : d - 1 + 1 = d := Nat.sub_add_cancel (Nat.succ_le_iff.mpr hdpos)
  by_cases heq : d = (M.opening_slot S.hc q)
  · subst heq
    have h' := h.openingStepInputs w
      (by rw [Restated.openingSlot_pred_succ_l58 facts S h.roundPositive]; exact hw)
    beta_reduce at h'
    rw [Restated.openingSlot_pred_succ_l58 facts S h.roundPositive] at h'
    exact h'
  · have hdlt : (M.opening_slot S.hc q) < d := lt_of_le_of_ne hdlo (Ne.symm heq)
    have hpredLo : (M.opening_slot S.hc q) ≤ d - 1 := Nat.le_pred_of_lt hdlt
    have hpredLt : d - 1 < Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q :=
      lt_of_lt_of_le (Nat.sub_lt hdpos Nat.zero_lt_one) hdhi
    have h' := (h.roundInputs (d - 1) hpredLo hpredLt).vote w (by rw [hsucc]; exact hw)
    beta_reduce at h'
    rw [hsucc] at h'
    exact h'

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

/-- If `RoundCeilingAtOn` holds at `q` and `d` is at most round `q`'s last slot, then `vote_time d`
    is inside the horizon. -/
theorem roundCeiling_voteInHorizonOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V)
    {W : Nat → V → M.N} {Wt : Time → V → M.N} {Mh : Height} {q : Round} {C : NamedBlock V}
    (h : Restated.RoundCeilingAtOn M S rho W Wt Hs Xb Mh q C)
    {d : Slot} (hdhi : d ≤ Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q) :
    M.vote_time S.E d ≤ rho.horizon := by
  have hlastPos : 0 < Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q :=
    Nat.zero_lt_of_lt (Restated.openingSlot_lt_seedRoundLastSlot_l58 facts S q)
  have hpred : Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q - 1 + 1 = Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q :=
    Nat.sub_add_cancel (Nat.succ_le_iff.mpr hlastPos)
  have hlastToConf : M.vote_time S.E (Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q) ≤
      M.confirmation_time S.E (Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q - 1) := by
    have hle := facts.sch.vote_time_succ_add_delta_le_confirmation_time S.E
      (Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q - 1)
    rw [hpred] at hle
    exact le_trans (le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)) hle
  exact (facts.sch.vote_time_mono_slots S.E hdhi).trans
    (hlastToConf.trans h.roundConfirmationInHorizon)

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

/-- Under the bundle along `W`, if `RoundCeilingAtOn` holds at `q` for `C`, `d` is a slot of round
    `q`, `X` is a head picked from `d`'s committee in the set for its confirmation instant,
    `lo ≤ vote_time (opening_slot q − 1)`, and `d`'s committee members pass the grade-1 awake test
    at their vote ticks, then `X` has height at least `Mh − 1`. -/
theorem roundCeiling_headThinOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {Mh : Height} {q : Round} {C : NamedBlock V}
    (h : Restated.RoundCeilingAtOn M S rho W (fun t => W (strictEventIndex rho t)) Hs Xb Mh q C)
    {d : Slot} (hdlo : (M.opening_slot S.hc q) ≤ d)
    (hdhi : d ≤ Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q)
    {X : NamedBlock V} (hX : Restated.NamedHonestHeadOn M S rho W Hs Xb d X)
    (hlo : lo ≤ M.vote_time S.E ((M.opening_slot S.hc q) - 1))
    (hrun : ∀ w ∈ S.E.committee d, w ∈ Hs (M.vote_time S.E d) →
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w (M.vote_time S.E d)) →
        M.awake_for_grade1 S w (W j w) (M.round_of S.hc d)) :
    Mh - 1 ≤ (M.derive_named S.E S.cfg X).h := by
  have hdpos : 0 < d := lt_of_lt_of_le (facts.gr.openingSlot_pos_l58 S h.roundPositive) hdlo
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 :=
    ⟨d - 1, (Nat.sub_add_cancel (Nat.succ_le_iff.mpr hdpos)).symm⟩
  have hlastPos : 0 < Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q :=
    Nat.zero_lt_of_lt (Restated.openingSlot_lt_seedRoundLastSlot_l58 facts S q)
  have hlastPred : Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q - 1 + 1 = Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q :=
    Nat.sub_add_cancel (Nat.succ_le_iff.mpr hlastPos)
  have hvoteHor : M.vote_time S.E (d' + 1) ≤ rho.horizon :=
    Restated.roundCeiling_voteInHorizonOn facts S Hs Xb h hdhi
  have hloPred : lo ≤ M.vote_time S.E d' :=
    hlo.trans (Restated.vote_time_mono_l58 facts S.E (Nat.sub_le_iff_le_add.mpr hdlo))
  have hloFreeze : lo ≤ M.view_freeze S.E d' :=
    hloPred.trans (vote_time_le_view_freeze₅₈ facts S d')
  have hinputs : ∀ w ∈ Hs (M.vote_time S.E (d' + 1)), ∀ c : M.Cache,
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E (d' + 1))) w).st.core.toHealing
        (M.vote_time S.E (d' + 1))
        (W (strictEventIndex rho (M.vote_time S.E (d' + 1))) w).cache ⇢ c →
      Restated.Vocabulary.Proofs.HealingSurface.GoldfishConeVoteInputs M S rho d' C.erase w
        (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (d' + 1))) w).st
          (M.vote_time S.E (d' + 1))) (W (strictEventIndex rho (M.vote_time S.E (d' + 1))) w).record c) := by
    intro w hw c hc
    have hin := Restated.roundCeiling_voteInputsOn facts S Hs Xb h hdlo hdhi hw c hc
    rwa [Nat.add_sub_cancel] at hin
  have hanchor : ∀ w ∈ Hs (M.vote_time S.E (d' + 1)), ∀ c : M.Cache,
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E (d' + 1))) w).st.core.toHealing
        (M.vote_time S.E (d' + 1))
        (W (strictEventIndex rho (M.vote_time S.E (d' + 1))) w).cache ⇢ c →
      let n := M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (d' + 1))) w).st
          (M.vote_time S.E (d' + 1)))
        (W (strictEventIndex rho (M.vote_time S.E (d' + 1))) w).record c
      ∀ A : Block V,
        Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n (M.round_of S.hc n.st.core.s) ⇢ A →
        Block.Preceq A C.erase := by
    intro w hw c hc n A hA
    exact h.voteAnchor (d' + 1) hdlo hdhi w hw c hc A hA
  have hfrontier : ∀ w ∈ Hs (M.vote_time S.E (d' + 1)),
      (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E (d' + 1))) w).st.core (d' + 1)).h_max = Mh :=
    fun w hw => h.gateOff.voteFrontier (d' + 1) hdlo (by rw [hlastPred]; exact hdhi) w hw
  exact Restated.seedHeadThin_of_voteInputsOn facts S Hs Xb hf hHs hHsXb hvoteHor hinputs
    hanchor hfrontier hX hloFreeze hrun

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

/-- Under the bundle along `W` and the committee majority, if `RoundCeilingAtOn` holds at `q`, `d`
    is a slot of round `q`, every committee member of `d` in the set for its vote instant voted a
    run block with `E` as an ancestor, `lo ≤ vote_time (opening_slot q − 1)`, and `d`'s committee
    members pass the grade-1 awake test at their vote ticks, then some head picked from `d`'s
    committee in the set for its confirmation instant is a descendant of `E` of height at least
    `Mh − 1`. -/
theorem roundCeiling_thinHead_of_coneOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {Mh : Height} {q : Round} {C : NamedBlock V} {E : Block V}
    (h : Restated.RoundCeilingAtOn M S rho W (fun t => W (strictEventIndex rho t)) Hs Xb Mh q C)
    {d : Slot} (hdlo : (M.opening_slot S.hc q) ≤ d)
    (hdhi : d ≤ Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q)
    (hcone : Restated.NamedHonestVotesConeOn M S rho W Hs Xb d (fun X => Block.Preceq E X))
    (hlo : lo ≤ M.vote_time S.E ((M.opening_slot S.hc q) - 1))
    (hrun : ∀ w ∈ S.E.committee d, w ∈ Hs (M.vote_time S.E d) →
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w (M.vote_time S.E d)) →
        M.awake_for_grade1 S w (W j w) (M.round_of S.hc d)) :
    Restated.ThinHonestHeadAtOn M S rho W Hs Xb Mh d E := by
  have hpositive :
      0 < ((S.E.committee d) ∩ Hs (M.confirmation_time S.E d)).card := by
    have hc := hcom d
    omega
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hpositive
  have hwCommittee : w ∈ S.E.committee d := (Finset.mem_inter.mp hw).1
  have hwHonest : w ∈ Hs (M.confirmation_time S.E d) := (Finset.mem_inter.mp hw).2
  obtain ⟨X, hEX, hXrun, hXemit⟩ := hcone w
    (hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E d) hwHonest) hwCommittee
  have hX : Restated.NamedHonestHeadOn M S rho W Hs Xb d X :=
    ⟨w, hwHonest, hwCommittee, hXrun, hXemit⟩
  exact ⟨X, hX, hEX,
    Restated.roundCeiling_headThinOn facts S Hs Xb hf hHs hHsXb h hdlo hdhi hX hlo hrun⟩

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

/-- Under the bundle along `W` and the committee majority, if `0 < q`,
    `lo ≤ vote_time (opening_slot q − 1)`, that slot's confirmation instant is inside the horizon,
    every committee member of that slot in the set for its vote instant voted a run block with `C`
    as an ancestor, every member of the set for the opening slot's vote instant has the boundary
    step's vote inputs at `C`, and the opening slot's committee members pass the grade-1 awake test
    at their vote ticks, then every committee member of the opening slot in the set for its vote
    instant voted a run block with `C` as an ancestor. -/
theorem seedOpeningVotes_of_coneOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {q : Round} (hq : 0 < q) {C : Block V}
    (hpostPrev : lo ≤ M.vote_time S.E ((M.opening_slot S.hc q) - 1))
    (hprevConfHor : M.confirmation_time S.E
      ((M.opening_slot S.hc q) - 1) ≤ rho.horizon)
    (hlastVotes : Restated.NamedHonestVotesConeOn M S rho W Hs Xb ((M.opening_slot S.hc q) - 1)
      (fun X => Block.Preceq C X))
    (hopeningStepInputs : ∀ w ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc q) - 1 + 1)), ∀ c : M.Cache,
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc q) - 1 + 1))) w).st.core.toHealing
        (M.vote_time S.E ((M.opening_slot S.hc q) - 1 + 1))
        (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc q) - 1 + 1))) w).cache ⇢ c →
      Restated.Vocabulary.Proofs.HealingSurface.GoldfishConeVoteInputs M S rho ((M.opening_slot S.hc q) - 1) C w
        (M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc q) - 1 + 1))) w).st
          (M.vote_time S.E ((M.opening_slot S.hc q) - 1 + 1)))
          (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc q) - 1 + 1))) w).record c))
    (hrun : ∀ w ∈ S.E.committee (M.opening_slot S.hc q),
      w ∈ Hs (M.vote_time S.E (M.opening_slot S.hc q)) →
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w (M.vote_time S.E (M.opening_slot S.hc q))) →
        M.awake_for_grade1 S w (W j w) (M.round_of S.hc (M.opening_slot S.hc q))) :
    Restated.NamedHonestVotesConeOn M S rho W Hs Xb ((M.opening_slot S.hc q))
      (fun X => Block.Preceq C X) := by
  intro w hw hwcommittee
  have hrunw := hrun w hwcommittee hw
  have hspos : 0 < (M.opening_slot S.hc q) - 1 := facts.gr.openingSlot_pred_pos_l58 S hq
  have heq : (M.opening_slot S.hc q) - 1 + 1 = M.opening_slot S.hc q :=
    Restated.openingSlot_pred_succ_l58 facts S hq
  clear hrun
  revert hspos heq hpostPrev hprevConfHor hlastVotes hopeningStepInputs
  generalize M.opening_slot S.hc q - 1 = s
  intro hpostPrev hprevConfHor hlastVotes hopeningStepInputs hspos heq
  rw [← heq] at hw hwcommittee hrunw ⊢
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
    (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
    (M.vote_time S.E (s + 1)) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache
  obtain ⟨T, L, L', Hd, hT, hL, hL', hHd⟩ := voterHead_outcome₅₈ facts S
    (M.mkNode
      (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
        (M.vote_time S.E (s + 1)))
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c)
  have hvoteHor : M.vote_time S.E (s + 1) ≤ rho.horizon :=
    le_trans (le_trans (le_of_lt (lt_add_of_pos_right _ S.E.Δ_pos))
      (facts.sch.vote_time_succ_add_delta_le_confirmation_time S.E s)) hprevConfHor
  have hloNext : lo ≤ M.vote_time S.E (s + 1) :=
    hpostPrev.trans (Restated.vote_time_mono_l58 facts S.E (Nat.le_succ s))
  obtain ⟨X, hXerase, hXrun, hXemit⟩ := Restated.named_voter_head_emitsOn facts S Hs Xb hf
    hHsXb hw (Nat.succ_pos s) hwcommittee hvoteHor hloNext c hc hrunw T hT L hL L' hL' Hd hHd
  have hhead := Restated.goldfishCone_stepOn facts S Hs Xb hf hHs hHsXb hcom hspos hpostPrev
    hprevConfHor hlastVotes hw c hc (hopeningStepInputs w hw c hc) T hT L hL L' hL' Hd hHd
  refine ⟨X, ?_, hXrun, hXemit⟩
  show Block.Preceq C X.erase
  rw [hXerase]
  exact hhead

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

/-- Under the bundle along `W` and the committee majority, if `0 < q`,
    `lo ≤ vote_time (opening_slot q − 1)` and `lo ≤ vote_time (opening_slot q)`, the two
    confirmation instants are inside the horizon, the boundary slot's vote cone and the boundary
    step's inputs hold at `C`, the opening slot's committee members pass the grade-1 awake test at
    their vote ticks, `w` is in the set for the opening slot's support cutoff and has the cone's
    confirmation inputs, and `D` is confirmed (`GenuineConfirmationWith`) by `w`'s store staged at
    the opening slot's confirmation instant, then `C` is an ancestor of `D`. -/
theorem seedOpeningConfirmation_of_coneOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {q : Round} (hq : 0 < q) {C D : Block V}
    (hpostPrev : lo ≤ M.vote_time S.E ((M.opening_slot S.hc q) - 1))
    (hprevConfHor : M.confirmation_time S.E
      ((M.opening_slot S.hc q) - 1) ≤ rho.horizon)
    (hpostOpening : lo ≤ M.vote_time S.E ((M.opening_slot S.hc q)))
    (hopeningHor : M.confirmation_time S.E
      ((M.opening_slot S.hc q)) ≤ rho.horizon)
    (hlastVotes : Restated.NamedHonestVotesConeOn M S rho W Hs Xb ((M.opening_slot S.hc q) - 1)
      (fun X => Block.Preceq C X))
    (hopeningStepInputs : ∀ w ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc q) - 1 + 1)), ∀ c : M.Cache,
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc q) - 1 + 1))) w).st.core.toHealing
        (M.vote_time S.E ((M.opening_slot S.hc q) - 1 + 1))
        (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc q) - 1 + 1))) w).cache ⇢ c →
      Restated.Vocabulary.Proofs.HealingSurface.GoldfishConeVoteInputs M S rho ((M.opening_slot S.hc q) - 1) C w
        (M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc q) - 1 + 1))) w).st
          (M.vote_time S.E ((M.opening_slot S.hc q) - 1 + 1)))
          (W (strictEventIndex rho (M.vote_time S.E ((M.opening_slot S.hc q) - 1 + 1))) w).record c))
    {w : V} (hw : w ∈ Hs (M.support_cutoff S.E ((M.opening_slot S.hc q))))
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q))) w).st.core.toHealing
      (M.confirmation_time S.E (M.opening_slot S.hc q))
      (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q))) w).cache ⇢ c)
    (hconfInputs : Restated.Vocabulary.Proofs.HealingSurface.GoldfishConeConfirmationInputs M S rho
      ((M.opening_slot S.hc q)) C w
      (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q))) w).st
        (M.confirmation_time S.E (M.opening_slot S.hc q)))
        (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q))) w).record c))
    (hD : Restated.Vocabulary.Protocol.GenuineConfirmationWith M (M.gradeContract c) S.E S.hc
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q))) w).st.core
        (M.confirmation_time S.E (M.opening_slot S.hc q)))
      (M.opening_slot S.hc q) D)
    (hrun : ∀ w ∈ S.E.committee (M.opening_slot S.hc q),
      w ∈ Hs (M.vote_time S.E (M.opening_slot S.hc q)) →
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w (M.vote_time S.E (M.opening_slot S.hc q))) →
        M.awake_for_grade1 S w (W j w) (M.round_of S.hc (M.opening_slot S.hc q))) :
    Block.Preceq C D :=
  Restated.goldfishCone_confirmationOn facts S Hs Xb hf hHs hHsXb hcom
    (facts.gr.openingSlot_pos_l58 S hq) hpostOpening hopeningHor
    (Restated.seedOpeningVotes_of_coneOn facts S Hs Xb hf hHs hHsXb hcom hq hpostPrev
      hprevConfHor hlastVotes hopeningStepInputs hrun) hw c hc hconfInputs hD

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

/-- Under the bundle along `W` and the committee majority, if `RoundCeilingAtOn` holds at `q` for
    `C`, `lo ≤ vote_time (opening_slot q − 1)`, and the opening slot's committee members pass the
    grade-1 awake test at their vote ticks, then every committee member of the opening slot in the
    set for its vote instant voted a run block with `C` as an ancestor. -/
theorem roundCeiling_openingVotesOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {Mh : Height} {q : Round} {C : NamedBlock V}
    (h : Restated.RoundCeilingAtOn M S rho W (fun t => W (strictEventIndex rho t)) Hs Xb Mh q C)
    (hlo : lo ≤ M.vote_time S.E ((M.opening_slot S.hc q) - 1))
    (hrun : ∀ w ∈ S.E.committee (M.opening_slot S.hc q),
      w ∈ Hs (M.vote_time S.E (M.opening_slot S.hc q)) →
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w (M.vote_time S.E (M.opening_slot S.hc q))) →
        M.awake_for_grade1 S w (W j w) (M.round_of S.hc (M.opening_slot S.hc q))) :
    Restated.NamedHonestVotesConeOn M S rho W Hs Xb ((M.opening_slot S.hc q))
      (fun X => Block.Preceq C.erase X) :=
  Restated.seedOpeningVotes_of_coneOn facts S Hs Xb hf hHs hHsXb hcom h.roundPositive hlo
    h.previousConfirmationInHorizon h.lastVotes h.openingStepInputs hrun

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

/-- Under the bundle along `W` and the committee majority, if `RoundCeilingAtOn` holds at `q` for
    `C`, `w` is in the set for the opening slot's confirmation instant, `D` is confirmed
    (`GenuineConfirmationWith`) by `w`'s store staged at that instant,
    `lo ≤ vote_time (opening_slot q − 1)`, and the opening slot's committee members pass the grade-1
    awake test at their vote ticks, then `C` is an ancestor of `D`. -/
theorem roundCeiling_openingConfirmationOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {Mh : Height} {q : Round} {C : NamedBlock V} {D : Block V}
    (h : Restated.RoundCeilingAtOn M S rho W (fun t => W (strictEventIndex rho t)) Hs Xb Mh q C)
    {w : V} (hw : w ∈ Hs (M.confirmation_time S.E ((M.opening_slot S.hc q))))
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q))) w).st.core.toHealing
      (M.confirmation_time S.E (M.opening_slot S.hc q))
      (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q))) w).cache ⇢ c)
    (hD : Restated.Vocabulary.Protocol.GenuineConfirmationWith M (M.gradeContract c) S.E S.hc
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q))) w).st.core
        (M.confirmation_time S.E (M.opening_slot S.hc q)))
      (M.opening_slot S.hc q) D)
    (hlo : lo ≤ M.vote_time S.E ((M.opening_slot S.hc q) - 1))
    (hrun : ∀ w ∈ S.E.committee (M.opening_slot S.hc q),
      w ∈ Hs (M.vote_time S.E (M.opening_slot S.hc q)) →
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w (M.vote_time S.E (M.opening_slot S.hc q))) →
        M.awake_for_grade1 S w (W j w) (M.round_of S.hc (M.opening_slot S.hc q))) :
    Block.Preceq C.erase D := by
  have hopeningHor : M.confirmation_time S.E
      ((M.opening_slot S.hc q)) ≤ rho.horizon :=
    (Restated.confirmationTime_mono_l58 facts S.E
      (Restated.openingSlot_le_seedRoundLastSlot_pred_l58 facts S q)).trans
      h.roundConfirmationInHorizon
  exact Restated.seedOpeningConfirmation_of_coneOn facts S Hs Xb hf hHs hHsXb hcom
    h.roundPositive hlo h.previousConfirmationInHorizon
    (hlo.trans (Restated.vote_time_mono_l58 facts S.E (Nat.sub_le _ _)))
    hopeningHor h.lastVotes h.openingStepInputs
    (hHs _ _ (facts.sch.Sts_support_cutoff_le_confirmation_time S.E _) hw) c hc
    ((h.roundInputs ((M.opening_slot S.hc q)) (le_refl _)
      (Restated.openingSlot_lt_seedRoundLastSlot_l58 facts S q)).confirmation w hw c hc) hD hrun

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

/-- Under the bundle along `W`, if `RoundCeilingAtOn` holds at `q`, `v` and `w` are in the set for
    the opening slot's confirmation instant, `D` and `E` are confirmed (`GenuineConfirmationWith`)
    by their stores staged at that instant, and `lo ≤ vote_time (opening_slot q − 1)`, then `D` and
    `E` are compatible. -/
theorem roundCeiling_openingConfirmationsCompatibleOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {Mh : Height} {q : Round} {C : NamedBlock V} {D E : Block V}
    (h : Restated.RoundCeilingAtOn M S rho W (fun t => W (strictEventIndex rho t)) Hs Xb Mh q C)
    {v w : V} (hv : v ∈ Hs (M.confirmation_time S.E ((M.opening_slot S.hc q))))
    (hw : w ∈ Hs (M.confirmation_time S.E ((M.opening_slot S.hc q))))
    (cv : M.Cache)
    (hcv : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q))) v).st.core.toHealing
      (M.confirmation_time S.E (M.opening_slot S.hc q))
      (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q))) v).cache ⇢ cv)
    (hD : Restated.Vocabulary.Protocol.GenuineConfirmationWith M (M.gradeContract cv) S.E S.hc
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q))) v).st.core
        (M.confirmation_time S.E (M.opening_slot S.hc q)))
      (M.opening_slot S.hc q) D)
    (cw : M.Cache)
    (hcw : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q))) w).st.core.toHealing
      (M.confirmation_time S.E (M.opening_slot S.hc q))
      (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q))) w).cache ⇢ cw)
    (hE : Restated.Vocabulary.Protocol.GenuineConfirmationWith M (M.gradeContract cw) S.E S.hc
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q))) w).st.core
        (M.confirmation_time S.E (M.opening_slot S.hc q)))
      (M.opening_slot S.hc q) E)
    (hlo : lo ≤ M.vote_time S.E ((M.opening_slot S.hc q) - 1)) :
    Block.compatible D E = true := by
  have hopeningHor : M.confirmation_time S.E
      ((M.opening_slot S.hc q)) ≤ rho.horizon :=
    (Restated.confirmationTime_mono_l58 facts S.E
      (Restated.openingSlot_le_seedRoundLastSlot_pred_l58 facts S q)).trans
      h.roundConfirmationInHorizon
  have hloProp : lo ≤ M.proposal_time S.E ((M.opening_slot S.hc q)) := by
    have hle := Restated.vote_time_le_proposal_time_succ_l58 facts S.E ((M.opening_slot S.hc q) - 1)
    rw [Restated.openingSlot_pred_succ_l58 facts S h.roundPositive] at hle
    exact hlo.trans hle
  exact Restated.sameSlot_genuine_compatible_after_gstOn facts
    S Hs Xb hf hHs hHsXb hv hw hloProp hopeningHor cv hcv hD cw hcw hE

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

/-- Under the bundle along `W` and the committee majority, if `RoundCeilingAtOn` holds at `q` for
    `C`, `lo ≤ vote_time (opening_slot q − 1)`, and every slot's committee members pass the grade-1
    awake test at their vote ticks, then at every slot of round `q` every committee member in the
    set for its vote instant voted a run block with `C` as an ancestor. -/
theorem roundCeiling_votesThroughOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {Mh : Height} {q : Round} {C : NamedBlock V}
    (h : Restated.RoundCeilingAtOn M S rho W (fun t => W (strictEventIndex rho t)) Hs Xb Mh q C)
    (hlo : lo ≤ M.vote_time S.E ((M.opening_slot S.hc q) - 1))
    (hrun : ∀ s : Slot, (M.opening_slot S.hc q) ≤ s →
      s ≤ Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q →
      ∀ w ∈ S.E.committee s, w ∈ Hs (M.vote_time S.E s) →
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w (M.vote_time S.E s)) →
        M.awake_for_grade1 S w (W j w) (M.round_of S.hc s)) :
    ∀ s : Slot, (M.opening_slot S.hc q) ≤ s →
      s ≤ Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q →
      Restated.NamedHonestVotesConeOn M S rho W Hs Xb s (fun X => Block.Preceq C.erase X) := by
  have hopenPos : 0 < (M.opening_slot S.hc q) := facts.gr.openingSlot_pos_l58 S h.roundPositive
  have hlastPredConf : M.confirmation_time S.E
      (Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q - 1) ≤ rho.horizon :=
    h.roundConfirmationInHorizon
  have hlastPos : 0 < Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q :=
    Nat.zero_lt_of_lt (Restated.openingSlot_lt_seedRoundLastSlot_l58 facts S q)
  have hlastEq : Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q - 1 + 1 =
      Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q :=
    Nat.sub_add_cancel (Nat.succ_le_iff.mpr hlastPos)
  have hfold := Restated.goldfishCone_inductionOn facts
    S Hs Xb hf hHs hHsXb hcom hopenPos (hlo.trans (Restated.vote_time_mono_l58 facts S.E (Nat.sub_le _ _)))
      hlastPredConf
      (Restated.roundCeiling_openingVotesOn facts S Hs Xb hf hHs hHsXb hcom h hlo
        (hrun _ le_rfl (Nat.le_of_lt (Restated.openingSlot_lt_seedRoundLastSlot_l58 facts S q))))
      (fun s hlo' hhi => h.roundInputs s hlo'
        (Nat.lt_of_le_of_lt hhi (Nat.sub_lt
          (Nat.zero_lt_of_lt (Restated.openingSlot_lt_seedRoundLastSlot_l58 facts S q))
          Nat.zero_lt_one)))
      (fun s hlt hle => hrun s (Nat.le_of_lt hlt) (hlastEq ▸ hle))
      (s0 := (M.opening_slot S.hc q)) (s1 := Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q - 1)
  intro s hlo' hhi
  apply hfold.1 s hlo'
  rw [hlastEq]
  exact hhi

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

/-! ### Path and vote-duty helpers -/

open scoped DC

/-- In a run sorted by key, the worlds strictly before the instant `t` are the worlds before the
    event whose index is `strictEventIndex rho t`. -/
private theorem stateBeforeTime_eq_strict₅₈s (S : Setup V) (rho : Record.Run V)
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
private theorem mem_stateBeforeTime_along₅₈s {S : Setup V} {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (t : Time) :
    W (strictEventIndex rho t) ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t := by
  rw [stateBeforeTime_eq_strict₅₈s S rho hsorted]
  exact (hW _).1

/-- The store the slot-`s` vote duty reads, staged from `n`'s core store, is the core store of `n`'s
    store with the clock set to the slot's vote instant. -/
private theorem voteStore_eq₅₈s (facts : Record.Facts M) (S : Setup V) (n : M.N) (s : Slot) :
    Restated.Vocabulary.Proofs.Optimistic.voteStore M S n.st.core s =
      (M.ns_setClock S.E n.st (M.vote_time S.E s)).core := by
  rw [Restated.Vocabulary.Proofs.Optimistic.voteStore, Restated.Vocabulary.Proofs.Optimistic.tickStore,
    facts.hd.setClock_core_eq_store_with_t_s]

/-- The slot of the healing view of the vote-duty store of slot `s` staged from `n`'s core store is
    `s`. -/
private theorem voteStore_hs_s₅₈s (facts : Record.Facts M) (S : Setup V) (n : M.N) (s : Slot) :
    (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S n.st.core s)).s = s := by
  show (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S n.st.core
    s)).toFG.toSG.toGoldfishStore.s = s
  rw [facts.sto.toHealing_gs_s]
  show (Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core (M.vote_time S.E s)).s = s
  rw [Restated.Vocabulary.Proofs.Optimistic.tickStore,
    ← facts.hd.setClock_core_eq_store_with_t_s S.E n.st, facts.hd.Sts_setClock_core_s,
    facts.sch.slotOf_vote_time]

/-- The store a tick at `t` hands its first duty, staged from `n`'s core store, has the tree of
    `n`'s core store. -/
private theorem tickStore_T₅₈s (facts : Record.Facts M) {S : Setup V} (n : M.N) (t : Time) :
    (Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t).T = n.st.core.T := by
  rw [Restated.Vocabulary.Proofs.Optimistic.tickStore,
    ← facts.hd.setClock_core_eq_store_with_t_s S.E n.st t, facts.hd.Sts_setClock_core_T]

/-- The store a tick at `t` hands its first duty, staged from `n`'s core store, has the `h_max` of
    `n`'s core store. -/
private theorem tickStore_h_max₅₈s (facts : Record.Facts M) {S : Setup V} (n : M.N) (t : Time) :
    (Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t).h_max = n.st.core.h_max := by
  rw [Restated.Vocabulary.Proofs.Optimistic.tickStore,
    ← facts.hd.setClock_core_eq_store_with_t_s S.E n.st t, facts.hd.setClock_core_h_max]

/-- The store a tick at `t` hands its first duty, staged from `n`'s core store, has the justified
    height `h_j` of `n`'s core store. -/
private theorem tickStore_h_j₅₈s (facts : Record.Facts M) {S : Setup V} (n : M.N) (t : Time) :
    (Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t).h_j = n.st.core.h_j := by
  rw [Restated.Vocabulary.Proofs.Optimistic.tickStore,
    ← facts.hd.setClock_core_eq_store_with_t_s S.E n.st t, ← facts.sto.toHealing_h_j,
    facts.hd.setClock_toHealing_h_j]

/-- The store a tick at `t` hands its first duty, staged from `n`'s core store, has the FG root of
    `n`'s core store. -/
private theorem tickStore_fgRoot₅₈s (facts : Record.Facts M) {S : Setup V} (n : M.N) (t : Time) :
    M.get_fg_root (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t)).toFG =
      M.get_fg_root (M.toHealing n.st.core).toFG :=
  facts.fc.get_fg_root_set_clock_slot _ _ _

/-- The store a tick at `t` hands its first duty, staged from `n`'s core store, has the filtered
    block tree of `n`'s core store. -/
private theorem tickStore_filtered₅₈s (facts : Record.Facts M) {S : Setup V} (n : M.N) (t : Time) :
    M.get_filtered_block_tree
        (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t)).toFG =
      M.get_filtered_block_tree (M.toHealing n.st.core).toFG :=
  facts.fc.get_filtered_block_tree_set_clock_slot _ _ _

/-- Every SG root the grade contract of `n`'s cache can return for `n`'s healing store at round `r`
    is an outcome of `n`'s anchor at `r`. -/
private theorem nodeAnchor_of_sgRoot₅₈s (facts : Record.Facts M) (S : Setup V) (n : M.N) (r : Round)
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
private theorem supporterMajority_of_cone₅₈s (facts : Record.Facts M) (E : Env V)
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

/-- For a node state `n` among the proposal reads of slot `s` and a block `P` the proposal duty can
    return at `n`, the parent of every proposal input `n` can produce is an ancestor of `P`'s
    erasure. -/
private theorem parent_preceq_of_proposal₅₈s (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (s : Slot) (n : M.N)
    (hn : n ∈ Restated.Vocabulary.Statements.Instantiation.proposerReadAt M S rho s) {P : NamedBlock V}
    (hP : M.proposal_with (M.gradeContract n.cache) .poolAndCarried S.E S.hc
      (S.node (S.E.proposer s)) n.st ⇢ some P)
    (I : Protocol.ProposalInput V)
    (hI : Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract n.cache) S.E S.hc
      (S.node (S.E.proposer s)) (M.toHealing n.st.core) ⇢ I) :
    P.erase.parent? = some I.parent ∧ Block.Preceq I.parent P.erase := by
  obtain ⟨p, hp, hpe⟩ :=
    Restated.Vocabulary.Proofs.HealingSurface.proposedBlockAt_parent facts S rho s n hn hP I hI
  have hpar : P.erase.parent? = some I.parent := by
    rw [Proofs.NamedWire.erase_parent_optional, hp, ← hpe]
    rfl
  exact ⟨hpar, Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mp (Protocol.preceq_of_parent? hpar)⟩

omit [DecidableEq V] [Fintype V] in
/-- If `f <$> m` can return `b`, then `m` can return some `a` with `f a = b`. -/
private theorem returns_map_elim₅₈s {α β : Type} (f : α → β) (m : DC.NDRE α) (b : β)
    (h : (f <$> m) ⇢ b) : ∃ a, m ⇢ a ∧ f a = b := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image] at h
  obtain ⟨e, he, hx⟩ := h
  cases e with
  | ok a =>
    simp [Except.map] at hx
    exact ⟨a, he, hx⟩
  | error err => simp [Except.map] at hx

omit [DecidableEq V] [Fintype V] in
/-- `m >>= k` can return `b` exactly when `m` can return some `a` from which `k a` can return `b`. -/
private theorem returns_bind_iff₅₈s {α β : Type} (m : DC.NDRE α) (k : α → DC.NDRE β) (b : β) :
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

/-- Under the bundle along `W`, if `w` is in the set for `view_freeze s`, `C` is in an outcome of
    the voter's filtered block tree of `w`'s vote-duty read of `s + 1` on `W`, and
    `lo ≤ view_freeze s`, then every block strictly between an anchor outcome of that read and `C`
    is in the same tree outcome. -/
theorem votePathAt_of_candidateOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {w : V} {s : Slot} (hw : w ∈ Hs (M.view_freeze S.E s))
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
      (M.vote_time S.E (s + 1)) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ c)
    (hgat : lo ≤ M.view_freeze S.E s) :
    let n := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
      (M.vote_time S.E (s + 1))) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c
    ∀ T : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T →
    ∀ C : Block V, C ∈ T →
    ∀ A, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n (M.round_of S.hc n.st.core.s) ⇢ A →
    ∀ D : Block V, Block.Preceq A D → D ≠ A → Block.Preceq D C → D ≠ C → D ∈ T := by
  intro n T hT C hC A hA D hAD _hDne hDC _hDneC
  have hwmem := mem_stateBeforeTime_along₅₈s hf.sorted hf.onePath (M.vote_time S.E (s + 1))
  have hnst : n.st = M.store_with_cache (M.ns_setClock S.E
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st (M.vote_time S.E (s + 1))) c :=
    facts.nd.mkNode_st _ _ _
  obtain ⟨Q, hQ⟩ := facts.fc.voter_processed_block_tree_nonempty S.E
    (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s
  obtain ⟨hCproc, -, ⟨Y, hYproc, hCY, hheight⟩, -⟩ :=
    facts.hd.voter_filtered_block_tree_cases S.E n.st.core n.st.core.s T hT hC Q hQ
  have hQ' : M.voter_processed_block_tree S.E
      (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1))).toFG.toSG.toGoldfishStore
      (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1))).s ⇢ Q := by
    have h := hQ
    rw [hnst, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_voter_processed_block_tree] at h
    have hs : ∀ st : M.S, (M.toHealing st).s = st.s := fun st => facts.sto.toHealing_gs_s st
    rw [voteStore_eq₅₈s facts, hs]
    exact h
  have hDproc : D ∈ Q :=
    Restated.ancestorProcessed_of_voterProcessedOn facts S Hs Xb hf hw Q hQ' hCproc hgat D hDC
  have hFJ : Block.Preceq n.st.core.F n.st.core.J := by
    rw [hnst, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.hd.setClock_core_F,
      facts.hd.setClock_core_J]
    exact Restated.Vocabulary.Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime facts
      S rho (M.vote_time S.E (s + 1)) w _ hwmem
  have hroot : Block.Preceq (M.get_fg_root (M.toHealing n.st.core).toFG) D :=
    Proofs.ModelProperties.Preceq_trans
      (Restated.Vocabulary.Proofs.w4_fgRoot_preceq_nodeAnchor facts S n _ A hA) hAD
  have hFD : Block.Preceq n.st.core.F D :=
    Proofs.ModelProperties.Preceq_trans (facts.fc.finalized_preceq_get_fg_root _ hFJ) hroot
  exact facts.hd.mem_voter_filtered_block_tree_of_parts S.E n.st.core n.st.core.s Q hQ hDproc hFD
    hYproc (Proofs.ModelProperties.Preceq_trans hDC hCY) hheight hroot T hT

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

/-- Under the bundle along `W` and the slashable bound, if `lo ≤ vote_time s`, `confirmation_time s`
    is inside the horizon, the vote cone of `s` holds at `C`, some head picked from `s`'s committee
    is a descendant of `C` of height at least `Mh − 1`, `w` is in the set for `vote_time (s + 1)`,
    and its vote-duty store of `s + 1` has `h_max = Mh`, `h_j + 2 ≤ Mh` and an FG root that is an
    ancestor of `C`, then `C` is in every outcome of the voter candidate tree of that store, and so
    is every block strictly between an anchor outcome of `w`'s vote-duty read and `C`. -/
theorem seedRelayVoteFactsOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hsb : Restated.SlashableBoundOn M S rho W Xb)
    {s : Slot} (hpost : lo ≤ M.vote_time S.E s)
    (hhor : M.confirmation_time S.E s ≤ rho.horizon)
    {C : Block V} {Mh : Height}
    (hvotes : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s (fun X => Block.Preceq C X))
    (hthin : Restated.ThinHonestHeadAtOn M S rho W Hs Xb Mh s C)
    {w : V} (hw : w ∈ Hs (M.vote_time S.E (s + 1)))
    (hfrontier : (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1)).h_max = Mh)
    (hgate : (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1)).h_j + 2 ≤ Mh)
    (hroot : Block.Preceq
      (M.get_fg_root
        (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1))).toFG) C)
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
      (M.vote_time S.E (s + 1)) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ c) :
    let n := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
      (M.vote_time S.E (s + 1))) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c
    ∀ K : Finset (Block V), Restated.Vocabulary.Proofs.Optimistic.voter_candidate_tree M S.E
        (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1))) ⇢ K →
      C ∈ K ∧
      ∀ A, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n (M.round_of S.hc n.st.core.s) ⇢ A →
      ∀ D : Block V, Block.Preceq A D → D ≠ A → Block.Preceq D C → D ≠ C → D ∈ K := by
  intro n K hK
  set i := strictEventIndex rho (M.vote_time S.E (s + 1)) with hi_def
  set st := Restated.Vocabulary.Proofs.Optimistic.voteStore M S (W i w).st.core (s + 1) with hst_def
  have hnst : n.st = M.store_with_cache (M.ns_setClock S.E (W i w).st (M.vote_time S.E (s + 1))) c :=
    facts.nd.mkNode_st _ _ _
  have hK' := hK
  unfold Restated.Vocabulary.Proofs.Optimistic.voter_candidate_tree at hK'
  obtain ⟨P0, hP0, hKP⟩ := (returns_bind_iff₅₈s _ _ _).mp hK'
  have hKeq := (Record.returns_pure _ _).1 hKP
  obtain ⟨H, hHhonest, hCH, hHheight⟩ := hthin
  obtain ⟨x, hxHonest, hxCommittee, hHrun, hHemit⟩ := hHhonest
  have hHhonest' : Restated.HonestHeadOn M S rho W Hs Xb s H.erase :=
    ⟨x, hxHonest, hxCommittee, ⟨H, rfl, hHrun⟩, hHemit⟩
  have hwCut : w ∈ Hs (M.support_cutoff S.E s) :=
    hHs _ _ (facts.sch.support_cutoff_le_vote_time_succ S.E s) hw
  have hwFreeze : w ∈ Hs (M.view_freeze S.E s) :=
    hHs _ _ (le_of_lt (facts.sch.view_freeze_lt_vote_time_succ S.E s)) hw
  have hgatFreeze : lo ≤ M.view_freeze S.E s :=
    hpost.trans (Restated.vote_time_le_view_freeze_l58 facts S.E s)
  have hHprocessed : H.erase ∈ P0 :=
    Restated.honestHead_voterProcessed_at_nextDuty_of_postHealingConeOn facts
      S Hs Xb hf hHs hHsXb hpost hhor hvotes hHhonest' hwCut hroot P0 hP0
  have hHmem : H.erase ∈ (W i w).st.T := by
    have hdata := facts.fc.mem_T_of_mem_voter_processed_block_tree _ _ _ P0 hP0 hHprocessed
    rw [facts.sto.toHealing_gs_T, hst_def, voteStore_eq₅₈s facts, facts.hd.Sts_setClock_core_T] at hdata
    exact hdata
  have hvoteHor : M.vote_time S.E (s + 1) ≤ rho.horizon := by
    exact le_trans (le_of_lt (lt_of_lt_of_le (lt_add_of_pos_right _ S.E.Δ_pos)
      (facts.sch.vote_time_succ_add_delta_le_confirmation_time S.E s))) hhor
  have hM : 1 ≤ Mh :=
    (Nat.succ_le_succ (Nat.zero_le 1)).trans ((Nat.le_add_left 2 st.h_j).trans hgate)
  have hfilteredPre := Restated.frontierAncestor_filtered_of_gateOffOn facts
    S Hs Xb hf hsb (hHsXb _ hw) hvoteHor hHmem rfl hHrun hCH hHheight hM
      (by rw [hst_def, Restated.Vocabulary.Proofs.Optimistic.voteStore, tickStore_h_max₅₈s facts] at hfrontier
          exact hfrontier)
      (by rw [hst_def, Restated.Vocabulary.Proofs.Optimistic.voteStore, tickStore_h_j₅₈s facts] at hgate
          exact hgate)
      (by rw [hst_def, Restated.Vocabulary.Proofs.Optimistic.voteStore, tickStore_fgRoot₅₈s facts] at hroot
          exact hroot)
  have hfiltered : C ∈ M.get_filtered_block_tree (M.toHealing st).toFG := by
    rw [hst_def, Restated.Vocabulary.Proofs.Optimistic.voteStore, tickStore_filtered₅₈s facts]
    exact hfilteredPre
  have hmax : st.h_max ≤ (M.derive_named S.E S.cfg H).h + 1 := by
    rw [hfrontier]
    exact Nat.sub_le_iff_le_add.mp hHheight
  have hduty : (M.ns_setClock S.E (W i w).st (M.vote_time S.E (s + 1))).core = st := by
    rw [hst_def, voteStore_eq₅₈s facts]
  have hcand : ∀ {X : Block V}, Block.Preceq X H.erase →
      X ∈ M.get_filtered_block_tree (M.toHealing st).toFG → X ∈ K := by
    intro X hXH hX
    have h := Restated.namedAncestorCandidate_of_processedDescendant_and_hMaxOn facts
      S Hs Xb hf hHsXb hwFreeze (C := X) (H := H)
    simp only [← hi_def, hduty] at h
    rw [hKeq]
    exact h P0 hP0 hHprocessed hHrun hXH hX hmax hgatFreeze
  have hCK := hcand hCH hfiltered
  refine ⟨hCK, ?_⟩
  intro A hA D hAD hDne hDC hDneC
  obtain ⟨T, hT⟩ := facts.fc.voter_filtered_block_tree_nonempty S.E n.st.core n.st.core.s
  have hCT : C ∈ T := by
    have hT' := hT
    rw [hnst, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_voter_filtered_block_tree,
      hduty] at hT'
    rw [← facts.fc.voter_candidate_tree_eq_protocol_voter_filtered_block_tree S.E st P0 hP0 T hT', ← hKeq]
    exact hCK
  have hDT := Restated.votePathAt_of_candidateOn facts S Hs Xb hf hwFreeze c hc hgatFreeze
    T hT C hCT A hA D hAD hDne hDC hDneC
  have hDfull : D ∈ M.get_filtered_block_tree (M.toHealing st).toFG := by
    have h := facts.fc.voter_filtered_block_tree_subset_filtered S.E n.st.core T hT hDT
    rw [hnst, facts.nd.store_with_cache_get_filtered_block_tree, hduty] at h
    exact h
  exact hcand (Proofs.ModelProperties.Preceq_trans hDC hCH) hDfull

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

/-- Under the bundle along `W` and the slashable bound, if `lo ≤ vote_time s`, `confirmation_time s`
    is inside the horizon, the vote cone of `s` and a thin head of `s` hold at `C`, `w` is in the
    set for `support_cutoff s`, and its confirmation store of `s` has `h_max = Mh`, `h_j + 2 ≤ Mh`
    and a root that is an ancestor of `C`, then `C` is in that store's confirmation tree, and so is
    every block strictly between an outcome of `w`'s confirmation anchor and `C`. -/
theorem seedRelayConfirmationFactsOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hsb : Restated.SlashableBoundOn M S rho W Xb)
    {s : Slot} (hpost : lo ≤ M.vote_time S.E s)
    (hhor : M.confirmation_time S.E s ≤ rho.horizon)
    {C : Block V} {Mh : Height}
    (hvotes : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s (fun X => Block.Preceq C X))
    (hthin : Restated.ThinHonestHeadAtOn M S rho W Hs Xb Mh s C)
    {w : V} (hw : w ∈ Hs (M.support_cutoff S.E s))
    (hfrontier : (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
      (W (strictEventIndex rho (M.confirmation_time S.E s)) w).st.core
      (M.confirmation_time S.E s)).h_max = Mh)
    (hgate : (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
      (W (strictEventIndex rho (M.confirmation_time S.E s)) w).st.core
      (M.confirmation_time S.E s)).h_j + 2 ≤ Mh)
    (hroot : Block.Preceq (Restated.Vocabulary.Protocol.confRoot M
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.confirmation_time S.E s)) w).st.core
        (M.confirmation_time S.E s))) C)
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.confirmation_time S.E s)) w).st.core.toHealing
      (M.confirmation_time S.E s) (W (strictEventIndex rho (M.confirmation_time S.E s)) w).cache ⇢ c) :
    C ∈ Restated.Vocabulary.Protocol.confTree M (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.confirmation_time S.E s)) w).st.core (M.confirmation_time S.E s)) ∧
      ∀ A : Block V, Restated.Vocabulary.Internal.namedConfirmationAnchor M S
        (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.confirmation_time S.E s)) w).st
          (M.confirmation_time S.E s))
          (W (strictEventIndex rho (M.confirmation_time S.E s)) w).record c) ⇢ A →
      ∀ D : Block V, Block.Preceq A D → D ≠ A → Block.Preceq D C → D ≠ C →
        D ∈ Restated.Vocabulary.Protocol.confTree M (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.confirmation_time S.E s)) w).st.core (M.confirmation_time S.E s)) := by
  set i := strictEventIndex rho (M.confirmation_time S.E s) with hi_def
  have hwmem := mem_stateBeforeTime_along₅₈s hf.sorted hf.onePath (M.confirmation_time S.E s)
  obtain ⟨H, hHhonest, hCH, hHheight⟩ := hthin
  obtain ⟨x, hxHonest, hxCommittee, hHrun, hHemit⟩ := hHhonest
  have hHhonest' : Restated.HonestHeadOn M S rho W Hs Xb s H.erase :=
    ⟨x, hxHonest, hxCommittee, ⟨H, rfl, hHrun⟩, hHemit⟩
  have hresolve := Restated.headsResolveIn_confStore_of_postHealingConeOn facts
    S Hs Xb hf hHs hHsXb hw hpost ((facts.sch.Sts_support_cutoff_le_confirmation_time S.E s).trans hhor)
      hroot hvotes
  have hfind := (hresolve H.erase hHhonest').1
  have hHmem : H.erase ∈ (Restated.Vocabulary.Proofs.Optimistic.tickStore M S (W i w).st.core
      (M.confirmation_time S.E s)).T :=
    Proofs.HealingLemmas.find?_mem hfind
  have hHpre : H.erase ∈ (W i w).st.T := by
    rw [tickStore_T₅₈s facts] at hHmem
    exact hHmem
  have hM : 1 ≤ Mh :=
    (Nat.succ_le_succ (Nat.zero_le 1)).trans
      ((Nat.le_add_left 2 (Restated.Vocabulary.Proofs.Optimistic.tickStore M S (W i w).st.core
        (M.confirmation_time S.E s)).h_j).trans hgate)
  have hfilteredPre := Restated.frontierAncestor_filtered_of_gateOffOn facts
    S Hs Xb hf hsb (hHsXb _ hw) hhor hHpre rfl hHrun hCH hHheight hM
      (by rw [tickStore_h_max₅₈s facts] at hfrontier
          exact hfrontier)
      (by rw [tickStore_h_j₅₈s facts] at hgate
          exact hgate)
      (by rw [Restated.Vocabulary.Protocol.confRoot, Restated.Vocabulary.Proofs.Optimistic.tickStore,
            facts.fc.get_fg_root_set_clock_slot] at hroot
          exact hroot)
  have hfiltered : C ∈ Restated.Vocabulary.Protocol.confTree M
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S (W i w).st.core (M.confirmation_time S.E s)) := by
    rw [Restated.Vocabulary.Protocol.confTree, Restated.Vocabulary.Proofs.Optimistic.tickStore,
      facts.fc.get_filtered_block_tree_set_clock_slot]
    exact hfilteredPre
  have hCT : C ∈ (W i w).st.core.T := by
    have hmem := facts.fc.get_filtered_block_tree_subset _ hfilteredPre
    rw [facts.sto.toHealing_T] at hmem
    exact hmem
  obtain ⟨Cn, _, hCnerase⟩ :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime facts S rho
      (M.confirmation_time S.E s) w (W i) hwmem hCT
  have hCnfiltered : Cn.erase ∈ Restated.Vocabulary.Protocol.confTree M
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S (W i w).st.core (M.confirmation_time S.E s)) := by
    rw [hCnerase]
    exact hfiltered
  refine ⟨hfiltered, ?_⟩
  intro A hA D hAD hne hDC _
  exact Restated.Vocabulary.Protocol.confPath_of_candidate facts S (W i) hwmem c hc hCnfiltered A hA D
    hAD hne (by rw [hCnerase]; exact hDC)

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

/-- Under the bundle along `W` and the committee majority, if `0 < s`, `lo ≤ vote_time s`,
    `confirmation_time s` is inside the horizon, the vote cone of `s` holds at `C`, every member of
    the set for `vote_time (s + 1)` has the cone's vote inputs at `C`, and the committee members of
    `s + 1` pass the grade-1 awake test at their vote ticks, then the vote cone of `s + 1` holds at
    `C`. -/
theorem seedHonestVotesCone_succOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {s : Slot} (hs : 0 < s)
    (hpost : lo ≤ M.vote_time S.E s)
    (hhor : M.confirmation_time S.E s ≤ rho.horizon)
    {C : Block V}
    (hvotes : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s (fun X => Block.Preceq C X))
    (hinputs : ∀ w ∈ Hs (M.vote_time S.E (s + 1)), ∀ c : M.Cache,
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
        (M.vote_time S.E (s + 1))
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ c →
      Restated.Vocabulary.Proofs.HealingSurface.GoldfishConeVoteInputs M S rho s C w
        (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
          (M.vote_time S.E (s + 1))) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c))
    (hrun : ∀ w ∈ S.E.committee (s + 1), w ∈ Hs (M.vote_time S.E (s + 1)) →
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w (M.vote_time S.E (s + 1))) →
        M.awake_for_grade1 S w (W j w) (M.round_of S.hc (s + 1))) :
    Restated.NamedHonestVotesConeOn M S rho W Hs Xb (s + 1) (fun X => Block.Preceq C X) := by
  intro w hw hwcommittee
  have hrunw := hrun w hwcommittee hw
  set i := strictEventIndex rho (M.vote_time S.E (s + 1)) with hi_def
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc (W i w).st.core.toHealing
    (M.vote_time S.E (s + 1)) (W i w).cache
  set n := M.mkNode (M.ns_setClock S.E (W i w).st (M.vote_time S.E (s + 1))) (W i w).record c
    with hn_def
  obtain ⟨T, hT⟩ := facts.fc.voter_filtered_block_tree_nonempty S.E n.st.core n.st.core.s
  obtain ⟨L, hL⟩ := facts.fc.voter_view_nonempty S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore
    n.st.core.s
  obtain ⟨L', hL'⟩ := facts.fc.voter_support_view_nonempty S.E
    (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s
  obtain ⟨Hd, hHd⟩ := facts.fc.get_head_in_tree_with_layer_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) T L L' (n.st.core.s - 1)
  have hhead : Block.Preceq C Hd :=
    Restated.goldfishCone_stepOn facts S Hs Xb hf hHs hHsXb hcom hs hpost hhor hvotes hw
      c hc (hinputs w hw c hc) T hT L hL L' hL' Hd hHd
  obtain ⟨H, hHerase, hHrun⟩ :=
    Restated.seedVoteDutyHead_runBlockOn facts S Hs Xb hf (hHsXb _ hw) (s + 1) c hc T hT L hL L' hL'
      Hd hHd
  have hvoteHor : M.vote_time S.E (s + 1) ≤ rho.horizon :=
    le_trans (le_of_lt (lt_of_lt_of_le (lt_add_of_pos_right _ S.E.Δ_pos)
      (facts.sch.vote_time_succ_add_delta_le_confirmation_time S.E s))) hhor
  refine ⟨H, ?_, hHrun, ?_⟩
  · rw [hHerase]
    exact hhead
  · rw [hHerase]
    exact Restated.seedVoteDutyHead_emitsOn facts S Hs Xb hf hw (Nat.succ_pos s) hwcommittee
      hvoteHor (hpost.trans (Restated.vote_time_mono_l58 facts S.E (Nat.le_succ s))) c hc hrunw
      T hT L hL L' hL' Hd hHd

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

/-- Under the bundle along `W` and the committee majority, if `v` is in the set for
    `support_cutoff s`, `0 < s`, `lo ≤ vote_time s`, `confirmation_time s` is inside the horizon,
    `B` is confirmed (`GenuineConfirmationWith`) by `v`'s confirmation store of `s`, and `s`'s
    committee members pass the grade-1 awake test at their vote ticks, then some member of `s`'s
    committee in the set for `confirmation_time s` has `B` as an ancestor of every head of its
    vote-duty read of `s`. -/
theorem genuineConfirmation_exists_honestVoteSupporter_ceilingOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {v : V} {s : Slot} (hv : v ∈ Hs (M.support_cutoff S.E s)) (hs : 0 < s)
    {B : Block V}
    (hpost : lo ≤ M.vote_time S.E s)
    (hhor : M.confirmation_time S.E s ≤ rho.horizon)
    (cv : M.Cache)
    (hcv : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core.toHealing
      (M.confirmation_time S.E s)
      (W (strictEventIndex rho (M.confirmation_time S.E s)) v).cache ⇢ cv)
    (hgenuine : Restated.Vocabulary.Protocol.GenuineConfirmationWith M (M.gradeContract cv)
      S.E S.hc (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core (M.confirmation_time S.E s)) s B)
    (hrun : ∀ x ∈ S.E.committee s, x ∈ Hs (M.confirmation_time S.E s) →
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick x (M.vote_time S.E s)) →
        M.awake_for_grade1 S x (W j x) (M.round_of S.hc s)) :
    ∃ x ∈ Hs (M.confirmation_time S.E s), x ∈ S.E.committee s ∧
      ∀ c : M.Cache, M.onPhaseTick S.E S.hc
          (W (strictEventIndex rho (M.vote_time S.E s)) x).st.core.toHealing
          (M.vote_time S.E s)
          (W (strictEventIndex rho (M.vote_time S.E s)) x).cache ⇢ c →
      let n := M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) x).st (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) x).record c
      ∀ T : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T →
      ∀ L : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
      ∀ L' : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
      ∀ H : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
          (M.toHealing n.st.core) T L L' (n.st.core.s - 1) ⇢ H →
        Block.Preceq B H :=
  Restated.genuineConfirmation_exists_honestVoteSupporter_after_gstOn facts
    S Hs Xb hf hHs hHsXb hcom hv hs hpost hhor cv hcv hgenuine hrun

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

/-- Under the bundle along `W` and the committee majority, if `RoundCeilingAtOn` holds at `q` for
    `C`, `v` is in the set for `S.a q`, `lo ≤ vote_time (opening_slot q − 1)`, and the opening
    slot's committee members pass the grade-1 awake test at their vote ticks, then for every node
    state `n` of `v`'s round-`q` action read, `n.live_confirmed` is either confirmed
    (`GenuineConfirmationWith`) by `v`'s store staged to the opening slot's confirmation instant and
    a descendant of `C`, or an ancestor of `C`. -/
theorem roundCeiling_openingOutput_genuine_or_preceqOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {Mh : Height} {q : Round} {C : NamedBlock V}
    (h : Restated.RoundCeilingAtOn M S rho W (fun t => W (strictEventIndex rho t)) Hs Xb Mh q C)
    {v : V} (hv : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)))
    (hlo : lo ≤ M.vote_time S.E ((M.opening_slot S.hc q) - 1))
    (hrun : ∀ w ∈ S.E.committee (M.opening_slot S.hc q),
      w ∈ Hs (M.vote_time S.E (M.opening_slot S.hc q)) →
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w (M.vote_time S.E (M.opening_slot S.hc q))) →
        M.awake_for_grade1 S w (W j w) (M.round_of S.hc (M.opening_slot S.hc q))) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v) q,
    (Restated.Vocabulary.Protocol.GenuineConfirmationWith M (M.gradeContract n.cache) S.E S.hc
        (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v).st.core
          (M.confirmation_time S.E (M.opening_slot S.hc q)))
        (M.opening_slot S.hc q) n.live_confirmed ∧
      Block.Preceq C.erase n.live_confirmed) ∨
    Block.Preceq n.live_confirmed C.erase := by
  intro n hn
  have ha := Restated.a_eq_confirmation_opening_l58 facts S q
  have hvConf : v ∈ Hs (M.confirmation_time S.E ((M.opening_slot S.hc q))) := by
    rw [← ha]
    exact hv
  have hwmem := mem_stateBeforeTime_along₅₈s hf.sorted hf.onePath (Restated.Vocabulary.Execution.Setup.a M S q)
  have hsplit := Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt_liveConfirmed_genuine_or_fgRoot
    facts S rho v q _ hwmem n hn
  obtain ⟨c, hc, st, -, rfl⟩ := hn
  rw [facts.nd.mkNode_cache]
  rw [facts.nd.mkNode_cache] at hsplit
  rcases hsplit with ⟨D, hD, hDeq⟩ | ⟨R, hReq, hReeq⟩
  · left
    have hlive : (M.mkNode st (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v).record
        c).live_confirmed = D := hDeq.symm
    rw [hlive]
    refine ⟨hD, ?_⟩
    rw [ha] at hc hD
    exact Restated.roundCeiling_openingConfirmationOn facts S Hs Xb hf hHs hHsXb hcom h hvConf c hc hD hlo
      hrun
  · right
    have hlive : (M.mkNode st (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v).record
        c).live_confirmed = R := hReeq.symm
    rw [hlive, hReq]
    rw [ha] at hc
    set j := strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q)) with hj_def
    obtain ⟨A, hA⟩ := facts.fc.get_sg_root_with_nonempty (M.gradeContract c) S.E S.hc
      (M.toHealing (M.mkNode (M.ns_setClock S.E (W j v).st (M.confirmation_time S.E (M.opening_slot S.hc q)))
        (W j v).record c).st.core)
      (M.round_of S.hc (M.mkNode (M.ns_setClock S.E (W j v).st
        (M.confirmation_time S.E (M.opening_slot S.hc q))) (W j v).record c).st.core.s)
    have hrootA := facts.fc.fg_root_Preceq_get_sg_root_with_gradeContract c S.E S.hc _ _ A hA
    rw [facts.nd.mkNode_st, facts.nd.store_with_cache_get_fg_root, facts.hd.setClock_core_eq_store_with_t_s]
      at hrootA
    have hAmem : Restated.Vocabulary.Internal.namedConfirmationAnchor M S
        (M.mkNode (M.ns_setClock S.E (W j v).st (M.confirmation_time S.E (M.opening_slot S.hc q)))
          (W j v).record c) ⇢ A := by
      unfold Restated.Vocabulary.Internal.namedConfirmationAnchor
      rw [facts.nd.mkNode_cache]
      exact hA
    have hAC := h.confirmationAnchor ((M.opening_slot S.hc q)) (Nat.sub_le _ _)
      (Restated.openingSlot_lt_seedRoundLastSlot_l58 facts S q) v hvConf c hc A hAmem
    have hidx : strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q) = j := by
      rw [hj_def, ha]
    rw [hidx]
    exact Proofs.ModelProperties.Preceq_trans hrootA hAC

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

/-- If `B` has slot `s` and is in the filtered tree of `v`'s vote-duty store of `s` read along `W`,
    then `B` is in every outcome of the voter candidate tree of that store. -/
theorem seedCeiling_currentSlot_voterCandidate_of_filteredOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} {s : Slot} {B : Block V}
    (hslot : B.slot = s)
    (hB : B ∈ M.get_filtered_block_tree
      (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s)).toFG) :
    ∀ K : Finset (Block V), Restated.Vocabulary.Proofs.Optimistic.voter_candidate_tree M S.E
      (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s)) ⇢ K → B ∈ K := by
  intro K hK
  set st := Restated.Vocabulary.Proofs.Optimistic.voteStore M S
    (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s with hst_def
  unfold Restated.Vocabulary.Proofs.Optimistic.voter_candidate_tree at hK
  obtain ⟨P0, hP0, hKP⟩ := (returns_bind_iff₅₈s _ _ _).mp hK
  rw [(Record.returns_pure _ _).1 hKP]
  have hBT : B ∈ st.T := by
    have h := facts.fc.get_filtered_block_tree_subset _ hB
    rw [facts.sto.toHealing_T] at h
    exact h
  obtain ⟨Y, hYT, hBY, hheight⟩ := facts.fc.viable_witness_of_mem_get_filtered_block_tree hB
  have hYT' : Y ∈ st.T := by
    rw [facts.sto.toHealing_gs_T] at hYT
    exact hYT
  have hYB : Y = B :=
    Restated.voteDutyStore_terminal_of_preceqOn facts S Hs Xb hf (v := v) (s := s) hslot hYT' hBY
  subst Y
  have hBgs : B ∈ (M.toHealing st).toFG.toSG.toGoldfishStore.T := by
    rw [facts.sto.toHealing_gs_T]
    exact hBT
  have hprocessed : B ∈ P0 := by
    refine facts.fc.mem_voter_processed_block_tree_of_proposal _ _ _ hBgs hBgs ?_
      (Proofs.ModelProperties.Preceq_self B) P0 hP0
    rw [hst_def, voteStore_hs_s₅₈s facts]
    exact hslot
  exact facts.fc.mem_get_filtered_block_tree_from_of_parts_explicit _ hprocessed
    (facts.fc.finalized_preceq_of_mem_get_filtered_block_tree hB)
    hprocessed (Proofs.ModelProperties.Preceq_self B) hheight
    (preceq_eq_true_iff_Preceq.1 (facts.fc.preceq_get_fg_root_of_mem_filtered hB))

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

/-- Under the bundle along `W` and the committee majority, if `0 < s`, `lo ≤ vote_time s`,
    `support_cutoff s` is in the horizon, the proposer of slot `s + 1` is in the set for
    `support_cutoff s`, the FG root of its proposal read is an ancestor of `T`, and slot `s`'s
    committee votes into the descendants of `T`, then for every outcome of the proposer's support
    view, the proposal read's views give cone support for the descendants of `T` over the set for
    `confirmation_time s`. -/
theorem seedProposerConeSupport_of_namedConeOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs) {s : Slot}
    (hs : 0 < s) (hpost : lo ≤ M.vote_time S.E s)
    (hhor : M.support_cutoff S.E s ≤ rho.horizon)
    (hprop : S.E.proposer (s + 1) ∈ Hs (M.support_cutoff S.E s)) {T : Block V}
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).st.core.toHealing
      (M.proposal_time S.E (s + 1))
      (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).cache ⇢ c)
    (hroot : Block.Preceq
      (M.get_fg_root (M.toHealing (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).st
        (M.proposal_time S.E (s + 1)))
        (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).record
        c).st.core).toFG) T)
    (hnames : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s
      (fun X => Block.Preceq T X)) :
    let n := M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).st
        (M.proposal_time S.E (s + 1)))
        (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).record c
    ∀ L : List (GoldfishVote V),
      M.proposer_support_view (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
    Restated.Vocabulary.Proofs.Optimistic.ConeSupport M S.E n.st.core.T
      (M.proposer_view (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s).toFinset
      L.toFinset
      (M.proposer_view (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s).toFinset
      (n.st.core.s - 1)
      (Hs (M.confirmation_time S.E s))
      (fun X => Block.Preceq T X) :=
  Restated.fixedRoot_preparedProposalConeSupport_of_namedConeOn facts S Hs Xb hf hHs hHsXb hcom hs
    hpost hhor hprop c hc hroot hnames

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

/-- Under the bundle along `W` and the committee majority, if `0 < s`, `lo ≤ vote_time s`,
    `support_cutoff s` is inside the horizon, the proposer of `s + 1` is in the set for
    `support_cutoff s`, slot `s`'s committee votes into the descendants of `T`, and `T` is in the
    filtered tree of the proposer's duty store, then for every anchor outcome of the proposer's read
    compatible with `T`, `T` is an ancestor of the parent of every proposal input that read can
    produce. -/
theorem coneTarget_preceq_nextProposedParent_namedOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {s : Slot} (hs : 0 < s)
    (hpost : lo ≤ M.vote_time S.E s)
    (hhor : M.support_cutoff S.E s ≤ rho.horizon)
    (hprop : S.E.proposer (s + 1) ∈ Hs (M.support_cutoff S.E s))
    {T : Block V}
    (hcone : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s (fun X => Block.Preceq T X))
    (hactive : T ∈ M.get_filtered_block_tree
      (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).st.core
        (M.proposal_time S.E (s + 1)))).toFG)
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).st.core.toHealing
      (M.proposal_time S.E (s + 1))
      (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).cache ⇢ c) :
    let n := M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).st
        (M.proposal_time S.E (s + 1)))
        (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).record c
    ∀ A : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n
        (M.round_of S.hc n.st.core.s) ⇢ A →
      Block.compatible A T = true →
    ∀ I : Protocol.ProposalInput V,
      Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract n.cache) S.E S.hc
        (S.node (S.E.proposer (s + 1))) (M.toHealing n.st.core) ⇢ I →
      Block.Preceq T I.parent := by
  intro n A hA hcompat I hI
  set ip := strictEventIndex rho (M.proposal_time S.E (s + 1)) with hip_def
  set p := S.E.proposer (s + 1) with hp_def
  have hwp := mem_stateBeforeTime_along₅₈s hf.sorted hf.onePath (M.proposal_time S.E (s + 1))
  set st := n.st.core with hst_def
  have hn_st : n.st = M.store_with_cache (M.ns_setClock S.E (W ip p).st (M.proposal_time S.E (s + 1))) c :=
    facts.nd.mkNode_st _ _ _
  have hactive' : T ∈ M.get_filtered_block_tree (M.toHealing st).toFG := by
    rw [hst_def, hn_st, facts.nd.store_with_cache_get_filtered_block_tree,
      facts.hd.setClock_core_eq_store_with_t_s]
    exact hactive
  have hroot : Block.Preceq (M.get_fg_root (M.toHealing st).toFG) T :=
    preceq_eq_true_iff_Preceq.mp (facts.fc.preceq_get_fg_root_of_mem_filtered hactive')
  have hsupport := Restated.seedProposerConeSupport_of_namedConeOn facts S Hs Xb hf hHs hHsXb
    hcom hs hpost hhor hprop c hc hroot hcone
  obtain ⟨L, hL⟩ := facts.fc.proposer_support_view_nonempty
    (M.toHealing st).toFG.toSG.toGoldfishStore (M.toHealing st).toFG.toSG.toGoldfishStore.s
  have hL' : M.proposer_support_view (M.toHealing st).toFG.toSG.toGoldfishStore st.s ⇢ L := by
    rw [← facts.sto.toHealing_gs_s]
    exact hL
  have hcone' := hsupport L hL'
  have hvalid : Protocol.VoteSetValid S.E (st.s - 1)
      (M.proposer_view (M.toHealing st).toFG.toSG.toGoldfishStore st.s).toFinset := by
    rw [hst_def, hn_st, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_proposer_view,
      facts.hd.setClock_core_eq_store_with_t_s]
    exact Restated.proposerDutyStore_proposer_view_valid_coreOn facts S Hs Xb hf (s + 1)
  have hpc : Restated.Vocabulary.Internal.ParentClosed M st := by
    have h := Restated.Vocabulary.Proofs.NamedStoreBridge.parentClosed_stateBeforeTime facts S rho
      (M.proposal_time S.E (s + 1)) p _ hwp
    unfold Restated.Vocabulary.Internal.ParentClosed Record.Model.GS.parent_closed at h ⊢
    rw [facts.sto.toHealing_T] at h ⊢
    rw [hst_def, hn_st, facts.nd.store_with_cache_core_T, facts.hd.Sts_setClock_core_T]
    exact h
  have hFJ : Block.Preceq st.F st.J := by
    rw [hst_def, hn_st, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J,
      facts.hd.setClock_core_F, facts.hd.setClock_core_J]
    exact Restated.Vocabulary.Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime facts
      S rho (M.proposal_time S.E (s + 1)) p _ hwp
  have hTT : T ∈ st.T := by
    have h := facts.fc.get_filtered_block_tree_subset _ hactive'
    rw [facts.sto.toHealing_T] at h
    exact h
  obtain ⟨R, hR⟩ := facts.fc.get_sg_root_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing st) (M.round_of S.hc st.s)
  have hRA : A = R := by
    unfold Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor Restated.Vocabulary.Internal.PhaseGrades.nodeRead
      at hA
    obtain ⟨G, hG, hGA⟩ := returns_map_elim₅₈s _ _ _ hA
    rw [← hGA]
    exact facts.nd.Sts_gradeContract_read_anchor n.cache S.E S.hc _ _ G hG R
      ((facts.nd.gradeContract_sgRoot_eq_frameAnchor n.cache S.E S.hc _ _ R).1 hR)
  subst hRA
  have hR' : M.get_sg_root_with (M.gradeContract n.cache) S.E S.hc (M.toHealing st)
      (M.round_of S.hc (M.toHealing st).toFG.toSG.toGoldfishStore.s) ⇢ A := by
    rw [facts.sto.toHealing_gs_s]
    exact hR
  have hfgsg : Block.Preceq (M.get_fg_root (M.toHealing st).toFG) A :=
    facts.fc.fg_root_Preceq_get_sg_root_with_gradeContract n.cache S.E S.hc (M.toHealing st) _ A hR
  have hpath : ∀ C : Block V, Block.Preceq A C → C ≠ A → Block.Preceq C T →
      C ∈ M.get_filtered_block_tree (M.toHealing st).toFG := by
    intro C hAC _ hCT
    have hpc' := hpc
    unfold Restated.Vocabulary.Internal.ParentClosed Record.Model.GS.parent_closed at hpc'
    rw [facts.sto.toHealing_T] at hpc'
    have hCmem : C ∈ st.T :=
      Proofs.Records.mem_of_preceq hpc'.2 C T hTT (preceq_eq_true_iff_Preceq.mpr hCT)
    exact facts.fc.mem_filtered_of_preceq
      (by
        rw [facts.sto.ModelProperties_toHealing_F, facts.sto.ModelProperties_toHealing_J]
        exact preceq_eq_true_iff_Preceq.mpr hFJ)
      hactive' (by rw [facts.sto.toHealing_T]; exact hCmem) (preceq_eq_true_iff_Preceq.mpr hCT)
      (preceq_eq_true_iff_Preceq.mpr (preceq_trans_Preceq hfgsg hAC))
  obtain ⟨H, hH⟩ := facts.fc.get_head_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing st)
    (M.proposer_view (M.toHealing st).toFG.toSG.toGoldfishStore
      (M.toHealing st).toFG.toSG.toGoldfishStore.s).toFinset
    L.toFinset ((M.toHealing st).toFG.toSG.toGoldfishStore.s - 1)
  have hparent : I.parent = H :=
    facts.dt.with_proposal_input_id_parent (M.gradeContract n.cache) S.E S.hc
      (S.node p) (M.toHealing st) I hI L hL H hH
  rw [hparent]
  have hfc := (facts.gr.get_head_with_eq_fork_choice (M.gradeContract n.cache) S.E S.hc
    (M.toHealing st) _ _ _ A hR' H).mp hH
  rw [facts.sto.toHealing_gs_s] at hfc
  obtain ⟨sup, hsup⟩ := facts.fc.raw_supporters_nonempty st.T
    (M.proposer_view (M.toHealing st).toFG.toSG.toGoldfishStore st.s).toFinset L.toFinset (st.s - 1) T
  have hmaj := supporterMajority_of_cone₅₈s facts S.E hcone' hvalid sup hsup
  have hTeq : (M.toHealing st).toFG.toSG.toGoldfishStore.T = st.T := facts.sto.toHealing_gs_T _
  rw [hTeq] at hfc
  exact facts.fc.goldfish_fork_choice_captures_supporter_majority _ _ _ _ _ _ _ _ _ hcone'.sub
    sup hsup hmaj hcompat (fun _ => hpath) H hfc

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

/-- Under the bundle along `W` and the committee majority, if round `q`'s opening proposers are in
    the family's sets, `RoundCeilingAtOn` holds at `q` for `C`, and
    `lo ≤ vote_time (opening_slot q − 1)`, then the opening proposer's anchor and every opening
    voter's anchor are ancestors of `C`, `C` is an ancestor of the opening proposal's parent, every
    opening confirmer's confirmation anchor is an ancestor of the opening proposal, and every
    previous action carrier is an ancestor of that parent. -/
theorem openingAnchorsAligned_of_roundCeilingOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {Mh : Height} {q : Round} {C : NamedBlock V}
    (hcarrier : Restated.ProposerCarrierAtOn M S Hs q)
    (h : Restated.RoundCeilingAtOn M S rho W (fun t => W (strictEventIndex rho t)) Hs Xb Mh q C)
    (hlo : lo ≤ M.vote_time S.E ((M.opening_slot S.hc q) - 1)) :
    let wp := W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
      (S.E.proposer (M.opening_slot S.hc q))
    (∀ c : M.Cache, M.onPhaseTick S.E S.hc wp.st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc q)) wp.cache ⇢ c →
      ∀ a : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S
        (M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E (M.opening_slot S.hc q))) wp.record c)
        q ⇢ a → a ⪯ C.erase) ∧
    (∀ v ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc q))), ∀ c : M.Cache,
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st.core.toHealing
        (M.vote_time S.E (M.opening_slot S.hc q))
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).cache ⇢ c →
      let n := M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st
          (M.vote_time S.E (M.opening_slot S.hc q)))
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).record c
      ∀ B : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n
        (M.round_of S.hc n.st.core.s) ⇢ B → B ⪯ C.erase) ∧
    (∀ c : M.Cache, M.onPhaseTick S.E S.hc wp.st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc q)) wp.cache ⇢ c →
      ∀ I : Protocol.ProposalInput V,
        Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract c) S.E S.hc
          (S.node (S.E.proposer (M.opening_slot S.hc q)))
          (M.toHealing (M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E (M.opening_slot S.hc q)))
            wp.record c).st.core) ⇢ I →
        C.erase ⪯ I.parent) ∧
    (∀ v ∈ Hs (M.confirmation_time S.E ((M.opening_slot S.hc q))), ∀ P : NamedBlock V,
      ∀ c : M.Cache, M.onPhaseTick S.E S.hc wp.st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc q)) wp.cache ⇢ c →
      M.proposal_with (M.gradeContract c) .poolAndCarried S.E S.hc
        (S.node (S.E.proposer (M.opening_slot S.hc q)))
        (M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E (M.opening_slot S.hc q)))
          wp.record c).st ⇢ some P →
      ∀ c' : M.Cache, M.onPhaseTick S.E S.hc
          (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q))) v).st.core.toHealing
          (M.confirmation_time S.E (M.opening_slot S.hc q))
          (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q))) v).cache ⇢ c' →
      ∀ B : Block V, Restated.Vocabulary.Internal.namedConfirmationAnchor M S
          (M.mkNode (M.ns_setClock S.E
            (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q))) v).st
            (M.confirmation_time S.E (M.opening_slot S.hc q)))
            (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q))) v).record c') ⇢ B →
        B ⪯ P.erase) ∧
    (∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1))),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) v) (q - 1),
      ∀ g, M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ g →
      ∀ B, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) g ⇢ B →
      ∀ c : M.Cache, M.onPhaseTick S.E S.hc wp.st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc q)) wp.cache ⇢ c →
      ∀ I : Protocol.ProposalInput V,
        Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract c) S.E S.hc
          (S.node (S.E.proposer (M.opening_slot S.hc q)))
          (M.toHealing (M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E (M.opening_slot S.hc q)))
            wp.record c).st.core) ⇢ I →
        B ⪯ I.parent) := by
  intro wp
  have hprop0 : S.E.proposer ((M.opening_slot S.hc q)) ∈
      Hs (M.confirmation_time S.E ((M.opening_slot S.hc q))) := by
    simpa only [Nat.add_zero] using hcarrier 0 (by decide)
  have hsourceAnchor := h.proposerAnchorCeiling hprop0
  have hpriorSucc : (M.opening_slot S.hc q) - 1 + 1 = (M.opening_slot S.hc q) :=
    Restated.openingSlot_pred_succ_l58 facts S h.roundPositive
  have hpriorPos : 0 < (M.opening_slot S.hc q) - 1 := facts.gr.openingSlot_pred_pos_l58 S h.roundPositive
  have hsupportHor : M.support_cutoff S.E
      ((M.opening_slot S.hc q) - 1) ≤ rho.horizon :=
    (facts.sch.Sts_support_cutoff_le_confirmation_time S.E _).trans
      h.previousConfirmationInHorizon
  have hcutConf : M.support_cutoff S.E ((M.opening_slot S.hc q) - 1) ≤
      M.confirmation_time S.E ((M.opening_slot S.hc q)) :=
    (facts.sch.Sts_support_cutoff_le_confirmation_time S.E _).trans
      (Restated.confirmationTime_mono_l58 facts S.E (Nat.sub_le _ _))
  have hwp := mem_stateBeforeTime_along₅₈s hf.sorted hf.onePath
    (M.proposal_time S.E (M.opening_slot S.hc q))
  -- The proposal read on `W` is one of the opening slot's proposal reads.
  have hread : ∀ c : M.Cache, M.onPhaseTick S.E S.hc wp.st.core.toHealing
      (M.proposal_time S.E (M.opening_slot S.hc q)) wp.cache ⇢ c →
      M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E (M.opening_slot S.hc q))) wp.record c ∈
        Restated.Vocabulary.Statements.Instantiation.proposerReadAt M S rho (M.opening_slot S.hc q) :=
    fun c hc => ⟨_, hwp, c, hc, rfl⟩
  have hreadSlot : ∀ c : M.Cache,
      (M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E (M.opening_slot S.hc q))) wp.record
        c).st.core.s = M.opening_slot S.hc q := by
    intro c
    rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.hd.Sts_setClock_core_s, facts.sch.slotOf_proposal_time]
  have hparent : ∀ c : M.Cache, M.onPhaseTick S.E S.hc wp.st.core.toHealing
      (M.proposal_time S.E (M.opening_slot S.hc q)) wp.cache ⇢ c →
      ∀ I : Protocol.ProposalInput V,
        Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract c) S.E S.hc
          (S.node (S.E.proposer (M.opening_slot S.hc q)))
          (M.toHealing (M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E (M.opening_slot S.hc q)))
            wp.record c).st.core) ⇢ I →
        C.erase ⪯ I.parent := by
    intro c hc I hI
    obtain ⟨A, hA⟩ := nodeAnchor_outcome₅₈ facts S
      (M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E (M.opening_slot S.hc q))) wp.record c)
      (M.round_of S.hc (M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E (M.opening_slot S.hc q)))
        wp.record c).st.core.s)
    have hAC : A ⪯ C.erase := by
      have hA' := hA
      rw [hreadSlot, facts.gr.round_of_opening_slot_eq] at hA'
      exact hsourceAnchor c hc A hA'
    have hpropCut : S.E.proposer ((M.opening_slot S.hc q) - 1 + 1) ∈
        Hs (M.support_cutoff S.E ((M.opening_slot S.hc q) - 1)) := by
      rw [hpriorSucc]
      exact hHs _ _ hcutConf hprop0
    exact Restated.coneTarget_preceq_nextProposedParent_namedOn facts S Hs Xb hf hHs hHsXb hcom
      (s := M.opening_slot S.hc q - 1) hpriorPos hlo hsupportHor hpropCut h.lastVotes
      (by rw [hpriorSucc]; exact h.proposerActive hprop0)
      c (by rw [hpriorSucc]; exact hc) A (by rw [hpriorSucc]; exact hA)
      (compatible_of_preceq_common_Preceq hAC
        (preceq_eq_true_iff_Preceq.mp (Block.preceq_self C.erase))) I
      (by rw [hpriorSucc, facts.nd.mkNode_cache]; exact hI)
  refine ⟨hsourceAnchor, ?_, hparent, ?_, ?_⟩
  · intro v hv
    exact h.voteAnchor ((M.opening_slot S.hc q)) (le_refl _)
      (Nat.le_of_lt (Restated.openingSlot_lt_seedRoundLastSlot_l58 facts S q)) v hv
  · intro v hv P c hc hP c' hc' B hB
    obtain ⟨I, hI⟩ := facts.dt.with_proposal_input_nonempty (M.gradeContract c) S.E S.hc
      (S.node (S.E.proposer (M.opening_slot S.hc q)))
      (M.toHealing (M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E (M.opening_slot S.hc q)))
        wp.record c).st.core)
    have hP' : M.proposal_with (M.gradeContract (M.mkNode (M.ns_setClock S.E wp.st
          (M.proposal_time S.E (M.opening_slot S.hc q))) wp.record c).cache) .poolAndCarried S.E S.hc
        (S.node (S.E.proposer (M.opening_slot S.hc q)))
        (M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E (M.opening_slot S.hc q)))
          wp.record c).st ⇢ some P := by
      rw [facts.nd.mkNode_cache]
      exact hP
    have hI' : Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract (M.mkNode
          (M.ns_setClock S.E wp.st (M.proposal_time S.E (M.opening_slot S.hc q))) wp.record c).cache)
        S.E S.hc (S.node (S.E.proposer (M.opening_slot S.hc q)))
        (M.toHealing (M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E (M.opening_slot S.hc q)))
          wp.record c).st.core) ⇢ I := by
      rw [facts.nd.mkNode_cache]
      exact hI
    exact preceq_trans_Preceq
      (h.confirmationAnchor ((M.opening_slot S.hc q)) (Nat.sub_le _ _)
        (Restated.openingSlot_lt_seedRoundLastSlot_l58 facts S q) v hv c' hc' B hB)
      (preceq_trans_Preceq (hparent c hc I hI)
        (parent_preceq_of_proposal₅₈s facts S rho _ _ (hread c hc) hP' I hI').2)
  · intro v hv n hn g hg B hB c hc I hI
    exact preceq_trans_Preceq (h.previousCarriers v hv n hn g hg B hB) (hparent c hc I hI)

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

/-- Under the bundle along `W` and the committee majority, if `P` is a proposal of the opening
    proposer's read on `W`, `RoundCeilingAtOn` holds at `q` for `C`, the opening is aligned at `C`
    on that read, `v` is in the set for the opening slot's vote instant, and
    `lo ≤ vote_time (opening_slot q − 1)`, then `C` is an ancestor of every head of `v`'s
    proposal-free target walk at its vote-duty read of the opening slot. -/
theorem roundCeiling_targetWalkPassesOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {Mh : Height} {q : Round} {C P : NamedBlock V}
    (cp : M.Cache)
    (hcp : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))).st.core.toHealing
      (M.proposal_time S.E (M.opening_slot S.hc q))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))).cache ⇢ cp)
    (hP : M.proposal_with (M.gradeContract cp) .poolAndCarried S.E S.hc
      (S.node (S.E.proposer (M.opening_slot S.hc q)))
      (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
          (S.E.proposer (M.opening_slot S.hc q))).st
        (M.proposal_time S.E (M.opening_slot S.hc q)))
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
          (S.E.proposer (M.opening_slot S.hc q))).record cp).st ⇢ some P)
    (h : Restated.RoundCeilingAtOn M S rho W (fun t => W (strictEventIndex rho t)) Hs Xb Mh q C)
    (haligned :
      let wp := W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))
      (∀ c : M.Cache, M.onPhaseTick S.E S.hc wp.st.core.toHealing
          (M.proposal_time S.E (M.opening_slot S.hc q)) wp.cache ⇢ c →
        ∀ a : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S
          (M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E (M.opening_slot S.hc q))) wp.record c)
          q ⇢ a → a ⪯ C.erase) ∧
      (∀ v ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc q))), ∀ c : M.Cache,
        M.onPhaseTick S.E S.hc
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st.core.toHealing
          (M.vote_time S.E (M.opening_slot S.hc q))
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).cache ⇢ c →
        let n := M.mkNode (M.ns_setClock S.E
            (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st
            (M.vote_time S.E (M.opening_slot S.hc q)))
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).record c
        ∀ B : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n
          (M.round_of S.hc n.st.core.s) ⇢ B → B ⪯ C.erase) ∧
      (∀ c : M.Cache, M.onPhaseTick S.E S.hc wp.st.core.toHealing
          (M.proposal_time S.E (M.opening_slot S.hc q)) wp.cache ⇢ c →
        ∀ I : Protocol.ProposalInput V,
          Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract c) S.E S.hc
            (S.node (S.E.proposer (M.opening_slot S.hc q)))
            (M.toHealing (M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E (M.opening_slot S.hc q)))
              wp.record c).st.core) ⇢ I →
          C.erase ⪯ I.parent) ∧
      (∀ v ∈ Hs (M.confirmation_time S.E ((M.opening_slot S.hc q))), ∀ P : NamedBlock V,
        ∀ c : M.Cache, M.onPhaseTick S.E S.hc wp.st.core.toHealing
          (M.proposal_time S.E (M.opening_slot S.hc q)) wp.cache ⇢ c →
        M.proposal_with (M.gradeContract c) .poolAndCarried S.E S.hc
          (S.node (S.E.proposer (M.opening_slot S.hc q)))
          (M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E (M.opening_slot S.hc q)))
            wp.record c).st ⇢ some P →
        ∀ c' : M.Cache, M.onPhaseTick S.E S.hc
            (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q))) v).st.core.toHealing
            (M.confirmation_time S.E (M.opening_slot S.hc q))
            (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q))) v).cache ⇢ c' →
        ∀ B : Block V, Restated.Vocabulary.Internal.namedConfirmationAnchor M S
            (M.mkNode (M.ns_setClock S.E
              (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q))) v).st
              (M.confirmation_time S.E (M.opening_slot S.hc q)))
              (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q))) v).record c') ⇢ B →
          B ⪯ P.erase) ∧
      (∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1))),
        ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
            (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) v) (q - 1),
        ∀ g, M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
            (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ g →
        ∀ B, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
            (M.round_of S.hc (M.toHealing n.st.core).s) g ⇢ B →
        ∀ c : M.Cache, M.onPhaseTick S.E S.hc wp.st.core.toHealing
          (M.proposal_time S.E (M.opening_slot S.hc q)) wp.cache ⇢ c →
        ∀ I : Protocol.ProposalInput V,
          Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract c) S.E S.hc
            (S.node (S.E.proposer (M.opening_slot S.hc q)))
            (M.toHealing (M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E (M.opening_slot S.hc q)))
              wp.record c).st.core) ⇢ I →
          B ⪯ I.parent))
    {v : V} (hv : v ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc q))))
    (hlo : lo ≤ M.vote_time S.E ((M.opening_slot S.hc q) - 1))
    (cv : M.Cache)
    (hcv : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st.core.toHealing
      (M.vote_time S.E (M.opening_slot S.hc q))
      (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).cache ⇢ cv) :
    let m := M.mkNode (M.ns_setClock S.E
      (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st
      (M.vote_time S.E (M.opening_slot S.hc q)))
      (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).record cv
    ∀ A : Block V,
      Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S m (M.round_of S.hc m.st.core.s) ⇢ A →
    ∀ T₀ : Finset (Block V), M.voter_filtered_block_tree S.E m.st.core m.st.core.s ⇢ T₀ →
    ∀ vv : Finset (GoldfishVote V),
      M.voter_view S.E (M.toHealing m.st.core).toFG.toSG.toGoldfishStore m.st.core.s ⇢ vv →
    ∀ vsv : Finset (GoldfishVote V),
      M.voter_support_view S.E (M.toHealing m.st.core).toFG.toSG.toGoldfishStore m.st.core.s ⇢ vsv →
    ∀ sc : Block V → ℕ,
      (∀ B : Block V, M.goldfish_score S.E m.st.core.T vv vsv (m.st.core.s - 1) B ⇢ sc B) →
    ∀ el : Block V → Bool,
      (∀ B : Block V, M.goldfish_eligible S.E m.st.core.σ m.st.core.h_max m.st.core.T m.st.core.s
        vv vsv (m.st.core.s - 1) B ⇢ el B) →
    ∀ G : Block V, M.ghost A (T₀.erase P.erase) sc el ⇢ G → Block.Preceq C.erase G := by
  intro m A hA T₀ hT₀ vv hvv vsv hvsv sc hsc el hel G hG
  have hpriorPos : 0 < M.opening_slot S.hc q - 1 := facts.gr.openingSlot_pred_pos_l58 S h.roundPositive
  have hpriorSucc : M.opening_slot S.hc q - 1 + 1 = M.opening_slot S.hc q :=
    Restated.openingSlot_pred_succ_l58 facts S h.roundPositive
  have hv' : v ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc q) - 1 + 1)) := by
    rw [hpriorSucc]
    exact hv
  have hcv' : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q - 1 + 1))) v).st.core.toHealing
      (M.vote_time S.E (M.opening_slot S.hc q - 1 + 1))
      (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q - 1 + 1))) v).cache ⇢ cv := by
    rw [hpriorSucc]; exact hcv
  have hinputs1 := h.openingStepInputs v hv' cv hcv'
  have hinputs : Restated.Vocabulary.Proofs.HealingSurface.GoldfishConeVoteInputs M S rho
      (M.opening_slot S.hc q - 1) C.erase v m := by
    have h2 := hinputs1
    simp only [hpriorSucc] at h2
    exact h2
  have hwalk := Restated.goldfishCone_pathEligibleOn facts S Hs Xb hf hHs hHsXb hcom hpriorPos
    hlo h.previousConfirmationInHorizon h.lastVotes hv' cv hcv' hinputs1
  simp only [hpriorSucc] at hwalk
  obtain ⟨hcone, hmaj, -⟩ := hwalk vv hvv vsv hvsv
  -- The proposal's parent, from the proposer's read on `W`.
  have hpread : M.mkNode (M.ns_setClock S.E
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))).st (M.proposal_time S.E (M.opening_slot S.hc q)))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))).record cp ∈
      Restated.Vocabulary.Statements.Instantiation.proposerReadAt M S rho (M.opening_slot S.hc q) :=
    mkNode_mem_confirmationReadAt₅₈ hf.sorted hf.onePath _ _ cp hcp
  obtain ⟨I, hI⟩ := facts.dt.with_proposal_input_nonempty (M.gradeContract cp) S.E S.hc
    (S.node (S.E.proposer (M.opening_slot S.hc q)))
    (M.toHealing (M.mkNode (M.ns_setClock S.E
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))).st (M.proposal_time S.E (M.opening_slot S.hc q)))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))).record cp).st.core)
  have hCI : C.erase ⪯ I.parent := haligned.2.2.1 cp hcp I hI
  obtain ⟨hparent, hHP⟩ := parent_preceq_of_proposal₅₈s facts S rho _ _ hpread
    (by rw [facts.nd.mkNode_cache]; exact hP) I (by rw [facts.nd.mkNode_cache]; exact hI)
  have hPne : C.erase ≠ P.erase := by
    intro heq
    have hPH : Block.Preceq P.erase I.parent := by
      rw [← heq]
      exact hCI
    have hEq : P.erase = I.parent := Proofs.ModelProperties.Preceq_antisymm hPH hHP
    rw [hEq] at hparent
    have hdepth := depth_of_parent? hparent
    omega
  have hCT : C.erase ∈ T₀ := hinputs.candidate T₀ hT₀
  have hcompat : Block.compatible A C.erase = true := hinputs.anchor A hA
  have hpath : Block.Preceq A C.erase → ∀ D : Block V, Block.Preceq A D → D ≠ A →
      Block.Preceq D C.erase → D ∈ T₀.erase P.erase := by
    intro _ D hAD hDne hDC
    have hDT : D ∈ T₀ := by
      by_cases hEq : D = C.erase
      · rw [hEq]
        exact hCT
      · exact hinputs.path A hA T₀ hT₀ D hAD hDne hDC hEq
    refine Finset.mem_erase.mpr ⟨?_, hDT⟩
    intro hDP
    rw [hDP] at hDC
    exact hPne (Proofs.ModelProperties.Preceq_antisymm (preceq_trans_Preceq hCI hHP) hDC)
  obtain ⟨sup, hsup⟩ := facts.fc.raw_supporters_nonempty m.st.core.T vv vsv (m.st.core.s - 1) C.erase
  have hfc := (facts.fc.goldfish_fork_choice_eq_ghost S.E m.st.core.σ m.st.core.h_max m.st.core.T
    m.st.core.s A (T₀.erase P.erase) vv vsv (m.st.core.s - 1) sc hsc el hel G).mpr hG
  exact facts.fc.goldfish_fork_choice_captures_supporter_majority _ _ _ _ _ _ _ _ _ hcone.sub
    sup hsup (hmaj sup hsup) hcompat hpath G hfc

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

/-- Under the bundle along `W`, if `0 < q`, round `q`'s opening proposers are in the family's sets,
    `P` is a proposal of the opening proposer's read on `W` of height at least `Mh − 1`, `1 ≤ Mh`,
    `S.a (q + 1)` is inside the horizon, `v ∈ Xb` holds `P` at its opening vote-duty store with
    `h_max = Mh` and `h_j + 2 ≤ Mh`, `lo ≤ proposal_time (opening_slot q)`, and the opening proposer
    passes the grade-1 awake test at its proposal tick, then `P` is in the filtered tree of that
    store and in every outcome of the voter's filtered block tree at every vote-duty read of `v` on
    `W`. -/
theorem seedCeiling_proposalCandidateAtVoteOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {Mh : Height} {q : Round} {P : NamedBlock V} {v : V}
    (hq : 0 < q)
    (hcarrier : Restated.ProposerCarrierAtOn M S Hs q)
    (cp : M.Cache)
    (hcp : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))).st.core.toHealing
      (M.proposal_time S.E (M.opening_slot S.hc q))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))).cache ⇢ cp)
    (hP : M.proposal_with (M.gradeContract cp) .poolAndCarried S.E S.hc
      (S.node (S.E.proposer (M.opening_slot S.hc q)))
      (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
          (S.E.proposer (M.opening_slot S.hc q))).st
        (M.proposal_time S.E (M.opening_slot S.hc q)))
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
          (S.E.proposer (M.opening_slot S.hc q))).record cp).st ⇢ some P)
    (hnextActionHor : (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) ≤ rho.horizon)
    (hheight : Mh - 1 ≤ (M.derive_named S.E S.cfg P).h)
    (hM : 1 ≤ Mh)
    (hv : v ∈ Xb)
    (hproposalAtVote :
      P.erase ∈ (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st.core
        (M.opening_slot S.hc q)).T)
    (hvoteFrontier :
      (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st.core
        (M.opening_slot S.hc q)).h_max = Mh)
    (hvoteGateOff :
      (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st.core
        (M.opening_slot S.hc q)).h_j + 2 ≤ Mh)
    (hgat : lo ≤ M.proposal_time S.E ((M.opening_slot S.hc q)))
    (hrun : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick (S.E.proposer (M.opening_slot S.hc q))
        (M.proposal_time S.E (M.opening_slot S.hc q))) →
      M.awake_for_grade1 S (S.E.proposer (M.opening_slot S.hc q))
        (W j (S.E.proposer (M.opening_slot S.hc q))) (M.round_of S.hc (M.opening_slot S.hc q))) :
    P.erase ∈ M.get_filtered_block_tree
        (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st.core
          (M.opening_slot S.hc q))).toFG ∧
      ∀ cv : M.Cache, M.onPhaseTick S.E S.hc
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st.core.toHealing
          (M.vote_time S.E (M.opening_slot S.hc q))
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).cache ⇢ cv →
        let m := M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st
          (M.vote_time S.E (M.opening_slot S.hc q)))
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).record cv
        ∀ T : Finset (Block V), M.voter_filtered_block_tree S.E m.st.core m.st.core.s ⇢ T →
          P.erase ∈ T := by
  have hs : 0 < (M.opening_slot S.hc q) := facts.gr.openingSlot_pos_l58 S hq
  have hprop : S.E.proposer ((M.opening_slot S.hc q)) ∈
      Hs (M.confirmation_time S.E ((M.opening_slot S.hc q))) := by
    simpa only [Nat.add_zero] using hcarrier 0 (by decide)
  have hactionHor : (Restated.Vocabulary.Execution.Setup.a M S q) ≤ rho.horizon :=
    (Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_succ q)).trans hnextActionHor
  have hconfHor :
      M.confirmation_time S.E ((M.opening_slot S.hc q)) ≤ rho.horizon := by
    rw [← Restated.a_eq_confirmation_opening_l58 facts S q]
    exact hactionHor
  have hvoteHor :
      M.vote_time S.E ((M.opening_slot S.hc q)) ≤ rho.horizon :=
    (facts.sch.Protocol_vote_time_le_confirmation_time S.E _).trans hconfHor
  have hproposalHor :
      M.proposal_time S.E ((M.opening_slot S.hc q)) ≤ rho.horizon :=
    (facts.sch.proposal_time_le_confirmation_time S.E _).trans hconfHor
  have hrunP : Restated.RunBlockOn M S rho W Xb P :=
    Restated.proposedBlockAt_blockInRun_of_admissibleOn facts S Hs Xb hf hHs hHsXb
      ((M.opening_slot S.hc q)) hs hprop hproposalHor hgat (fun j hj => hf.tick_outcome j _ _ hj)
      hrun cp hcp
      (by rw [facts.nd.mkNode_st, facts.dt.proposal_with_store_with_cache] at hP; exact hP)
  have hfiltered : P.erase ∈ M.get_filtered_block_tree
      (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st.core
        (M.opening_slot S.hc q))).toFG := by
    rw [Restated.Vocabulary.Proofs.Optimistic.voteStore, tickStore_filtered₅₈s facts]
    rw [Restated.Vocabulary.Proofs.Optimistic.voteStore, tickStore_T₅₈s facts] at hproposalAtVote
    rw [Restated.Vocabulary.Proofs.Optimistic.voteStore, tickStore_h_max₅₈s facts] at hvoteFrontier
    rw [Restated.Vocabulary.Proofs.Optimistic.voteStore, tickStore_h_j₅₈s facts] at hvoteGateOff
    exact Restated.frontierBlock_filtered_of_gateOffOn facts S Hs Xb hf hf.slashableBound hv hvoteHor
      hproposalAtVote rfl hrunP hheight hM hvoteFrontier hvoteGateOff
  have hpread : M.mkNode (M.ns_setClock S.E
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))).st (M.proposal_time S.E (M.opening_slot S.hc q)))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))).record cp ∈
      Restated.Vocabulary.Statements.Instantiation.proposerReadAt M S rho (M.opening_slot S.hc q) :=
    mkNode_mem_confirmationReadAt₅₈ hf.sorted hf.onePath _ _ cp hcp
  have hslot : P.erase.slot = (M.opening_slot S.hc q) := by
    rw [Proofs.NamedWire.erase_slot]
    exact Restated.Vocabulary.Proofs.HealingSurface.proposedBlockAt_slot facts S rho
      ((M.opening_slot S.hc q)) (some P) ⟨_, hpread, by rw [facts.nd.mkNode_cache]; exact hP⟩ rfl
  refine ⟨hfiltered, ?_⟩
  intro cv _hcv m T hT
  have hmst : m.st = M.store_with_cache (M.ns_setClock S.E
      (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st
      (M.vote_time S.E (M.opening_slot S.hc q))) cv := facts.nd.mkNode_st _ _ _
  have hT' : M.voter_filtered_block_tree S.E
      (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st.core (M.opening_slot S.hc q))
      (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st.core (M.opening_slot S.hc q)).s ⇢ T := by
    have h := hT
    rw [hmst, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_voter_filtered_block_tree,
      ← voteStore_eq₅₈s facts] at h
    exact h
  obtain ⟨P0, hP0⟩ := facts.fc.voter_processed_block_tree_nonempty S.E
    (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st.core (M.opening_slot S.hc q))).toFG.toSG.toGoldfishStore
    (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st.core (M.opening_slot S.hc q))).s
  have hK : Restated.Vocabulary.Proofs.Optimistic.voter_candidate_tree M S.E (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st.core (M.opening_slot S.hc q))) ⇢
      M.get_filtered_block_tree_from (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st.core (M.opening_slot S.hc q))).toFG P0 := by
    unfold Restated.Vocabulary.Proofs.Optimistic.voter_candidate_tree
    exact (returns_bind_iff₅₈s _ _ _).mpr ⟨P0, hP0, (Record.returns_pure _ _).mpr rfl⟩
  rw [← facts.fc.voter_candidate_tree_eq_protocol_voter_filtered_block_tree S.E _ P0 hP0 T hT']
  have hcand := Restated.seedCeiling_currentSlot_voterCandidate_of_filteredOn facts S Hs Xb hf
    hslot hfiltered
  exact hcand _ hK

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

/-- Under the bundle along `W` and the committee majority, if round `q`'s opening proposers are in
    the family's sets, `P` is the opening proposal, `RoundCeilingAtOn` holds at `q` for `C`, the
    opening is aligned at `C`, `S.a (q + 1)` is inside the horizon, `P` has height at least
    `Mh − 1`, `1 ≤ Mh`, every member of the set for the opening vote instant holds `P` at its
    opening vote duty with `h_max = Mh` and `h_j + 2 ≤ Mh`,
    `lo ≤ proposal_time (opening_slot q − 1)`, the proposer's duty store has `h_max = Mh`, and the
    opening proposer passes the grade-1 awake test at its proposal tick, then every committee member
    of the opening slot in the set for its vote instant has a vote store whose walk extends to `P`. -/
theorem proposalWalkTransferred_of_roundCeilingOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {Mh : Height} {q : Round} {C P : NamedBlock V}
    (hcarrier : Restated.ProposerCarrierAtOn M S Hs q)
    (cp : M.Cache)
    (hcp : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))).st.core.toHealing
      (M.proposal_time S.E (M.opening_slot S.hc q))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))).cache ⇢ cp)
    (hP : M.proposal_with (M.gradeContract cp) .poolAndCarried S.E S.hc
      (S.node (S.E.proposer (M.opening_slot S.hc q)))
      (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
          (S.E.proposer (M.opening_slot S.hc q))).st
        (M.proposal_time S.E (M.opening_slot S.hc q)))
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
          (S.E.proposer (M.opening_slot S.hc q))).record cp).st ⇢ some P)
    (h : Restated.RoundCeilingAtOn M S rho W (fun t => W (strictEventIndex rho t)) Hs Xb Mh q C)
    (haligned :
      let wp := W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))
      (∀ c : M.Cache, M.onPhaseTick S.E S.hc wp.st.core.toHealing
          (M.proposal_time S.E (M.opening_slot S.hc q)) wp.cache ⇢ c →
        ∀ a : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S
          (M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E (M.opening_slot S.hc q))) wp.record c)
          q ⇢ a → a ⪯ C.erase) ∧
      (∀ v ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc q))), ∀ c : M.Cache,
        M.onPhaseTick S.E S.hc
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st.core.toHealing
          (M.vote_time S.E (M.opening_slot S.hc q))
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).cache ⇢ c →
        let n := M.mkNode (M.ns_setClock S.E
            (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st
            (M.vote_time S.E (M.opening_slot S.hc q)))
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).record c
        ∀ B : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n
          (M.round_of S.hc n.st.core.s) ⇢ B → B ⪯ C.erase) ∧
      (∀ c : M.Cache, M.onPhaseTick S.E S.hc wp.st.core.toHealing
          (M.proposal_time S.E (M.opening_slot S.hc q)) wp.cache ⇢ c →
        ∀ I : Protocol.ProposalInput V,
          Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract c) S.E S.hc
            (S.node (S.E.proposer (M.opening_slot S.hc q)))
            (M.toHealing (M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E (M.opening_slot S.hc q)))
              wp.record c).st.core) ⇢ I →
          C.erase ⪯ I.parent) ∧
      (∀ v ∈ Hs (M.confirmation_time S.E ((M.opening_slot S.hc q))), ∀ P : NamedBlock V,
        ∀ c : M.Cache, M.onPhaseTick S.E S.hc wp.st.core.toHealing
          (M.proposal_time S.E (M.opening_slot S.hc q)) wp.cache ⇢ c →
        M.proposal_with (M.gradeContract c) .poolAndCarried S.E S.hc
          (S.node (S.E.proposer (M.opening_slot S.hc q)))
          (M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E (M.opening_slot S.hc q)))
            wp.record c).st ⇢ some P →
        ∀ c' : M.Cache, M.onPhaseTick S.E S.hc
            (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q))) v).st.core.toHealing
            (M.confirmation_time S.E (M.opening_slot S.hc q))
            (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q))) v).cache ⇢ c' →
        ∀ B : Block V, Restated.Vocabulary.Internal.namedConfirmationAnchor M S
            (M.mkNode (M.ns_setClock S.E
              (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q))) v).st
              (M.confirmation_time S.E (M.opening_slot S.hc q)))
              (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q))) v).record c') ⇢ B →
          B ⪯ P.erase) ∧
      (∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1))),
        ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
            (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) v) (q - 1),
        ∀ g, M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
            (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ g →
        ∀ B, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
            (M.round_of S.hc (M.toHealing n.st.core).s) g ⇢ B →
        ∀ c : M.Cache, M.onPhaseTick S.E S.hc wp.st.core.toHealing
          (M.proposal_time S.E (M.opening_slot S.hc q)) wp.cache ⇢ c →
        ∀ I : Protocol.ProposalInput V,
          Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract c) S.E S.hc
            (S.node (S.E.proposer (M.opening_slot S.hc q)))
            (M.toHealing (M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E (M.opening_slot S.hc q)))
              wp.record c).st.core) ⇢ I →
          B ⪯ I.parent))
    (hnextActionHor : (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) ≤ rho.horizon)
    (hheight : Mh - 1 ≤ (M.derive_named S.E S.cfg P).h)
    (hM : 1 ≤ Mh)
    (hproposalAtVote : ∀ v ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc q))),
      P.erase ∈ (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st.core
        (M.opening_slot S.hc q)).T)
    (hvoteFrontier : ∀ v ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc q))),
      (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st.core
        (M.opening_slot S.hc q)).h_max = Mh)
    (hvoteGateOff : ∀ v ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc q))),
      (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q))) v).st.core
        (M.opening_slot S.hc q)).h_j + 2 ≤ Mh)
    (hpostFrozenSnapshot : lo ≤
      M.proposal_time S.E ((M.opening_slot S.hc q) - 1))
    (hproposerFrontier :
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
          (S.E.proposer (M.opening_slot S.hc q))).st.core
        (M.proposal_time S.E (M.opening_slot S.hc q))).h_max = Mh)
    (hrun : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick (S.E.proposer (M.opening_slot S.hc q))
        (M.proposal_time S.E (M.opening_slot S.hc q))) →
      M.awake_for_grade1 S (S.E.proposer (M.opening_slot S.hc q))
        (W j (S.E.proposer (M.opening_slot S.hc q))) (M.round_of S.hc (M.opening_slot S.hc q))) :
    Restated.VoteStoresExtendOn M S rho Hs ((M.opening_slot S.hc q))
      (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q)))) P := by
  have hprop : S.E.proposer ((M.opening_slot S.hc q)) ∈
      Hs (M.confirmation_time S.E ((M.opening_slot S.hc q))) := by
    simpa only [Nat.add_zero] using hcarrier 0 (by decide)
  have hpropVote : S.E.proposer ((M.opening_slot S.hc q)) ∈
      Hs (M.vote_time S.E ((M.opening_slot S.hc q))) :=
    hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E _) hprop
  have hpriorSucc : (M.opening_slot S.hc q) - 1 + 1 = (M.opening_slot S.hc q) :=
    Restated.openingSlot_pred_succ_l58 facts S h.roundPositive
  have hs : 0 < (M.opening_slot S.hc q) := facts.gr.openingSlot_pos_l58 S h.roundPositive
  have hlo : lo ≤ M.vote_time S.E ((M.opening_slot S.hc q) - 1) :=
    hpostFrozenSnapshot.trans (Restated.proposal_time_le_vote_time_l58 facts S.E _)
  have hgatProp : lo ≤ M.proposal_time S.E ((M.opening_slot S.hc q)) := by
    have hle := Restated.vote_time_le_proposal_time_succ_l58 facts S.E ((M.opening_slot S.hc q) - 1)
    rw [hpriorSucc] at hle
    exact hlo.trans hle
  have hactionHor : (Restated.Vocabulary.Execution.Setup.a M S q) ≤ rho.horizon :=
    (Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_succ q)).trans hnextActionHor
  have hconfHor :
      M.confirmation_time S.E ((M.opening_slot S.hc q)) ≤ rho.horizon := by
    rw [← Restated.a_eq_confirmation_opening_l58 facts S q]
    exact hactionHor
  have hvoteHor :
      M.vote_time S.E ((M.opening_slot S.hc q)) ≤ rho.horizon :=
    (facts.sch.Protocol_vote_time_le_confirmation_time S.E _).trans hconfHor
  have hproposalHor :
      M.proposal_time S.E ((M.opening_slot S.hc q)) ≤ rho.horizon :=
    (facts.sch.proposal_time_le_confirmation_time S.E _).trans hconfHor
  set ip := strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)) with hip_def
  set p := S.E.proposer (M.opening_slot S.hc q) with hp_def
  set n := M.mkNode (M.ns_setClock S.E (W ip p).st (M.proposal_time S.E (M.opening_slot S.hc q)))
    (W ip p).record cp with hn_def
  have hnread : n ∈ Restated.Vocabulary.Statements.Instantiation.proposerReadAt M S rho
      (M.opening_slot S.hc q) :=
    mkNode_mem_confirmationReadAt₅₈ hf.sorted hf.onePath _ _ cp hcp
  have hncache : n.cache = cp := facts.nd.mkNode_cache _ _ _
  have hn_st : n.st = M.store_with_cache (M.ns_setClock S.E (W ip p).st
      (M.proposal_time S.E (M.opening_slot S.hc q))) cp := by
    rw [hn_def, facts.nd.mkNode_st]
  have hnround : M.round_of S.hc n.st.core.s = q := by
    rewrite [hn_def, facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.hd.Sts_setClock_core_s, facts.sch.slotOf_proposal_time,
      facts.gr.round_of_opening_slot_eq]
  have hP' : M.proposal_with (M.gradeContract n.cache) .poolAndCarried S.E S.hc
      (S.node p) n.st ⇢ some P := by
    rw [hncache]
    exact hP
  -- The proposal input of `n` and its parent.
  obtain ⟨I, hI⟩ := facts.dt.with_proposal_input_nonempty (M.gradeContract cp) S.E S.hc
    (S.node p) (M.toHealing n.st.core)
  have hI' : Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract n.cache) S.E S.hc
      (S.node p) (M.toHealing n.st.core) ⇢ I := by
    rw [hncache]
    exact hI
  have hCI : C.erase ⪯ I.parent := haligned.2.2.1 cp hcp I hI
  have hIP := (parent_preceq_of_proposal₅₈s facts S rho _ n hnread hP' I hI').2
  obtain ⟨R, hR⟩ := facts.fc.get_sg_root_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc n.st.core.s)
  have hsourceNode : ∀ A, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n
      (M.round_of S.hc n.st.core.s) ⇢ A → Block.Preceq A C.erase := by
    intro A hA
    rw [hnround] at hA
    exact haligned.1 cp hcp A hA
  have hRC : Block.Preceq R C.erase := hsourceNode R (nodeAnchor_of_sgRoot₅₈s facts S n _ hR)
  intro v hv _hcommittee cv hcv
  set iv := strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q)) with hiv_def
  set m := M.mkNode (M.ns_setClock S.E (W iv v).st (M.vote_time S.E (M.opening_slot S.hc q)))
    (W iv v).record cv with hm_def
  have hm_st : m.st = M.store_with_cache (M.ns_setClock S.E (W iv v).st
      (M.vote_time S.E (M.opening_slot S.hc q))) cv := by
    rw [hm_def, facts.nd.mkNode_st]
  have hms : m.st.core.s = M.opening_slot S.hc q := by
    rewrite [hm_def, facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.hd.Sts_setClock_core_s, facts.sch.slotOf_vote_time]
  have hv' : v ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc q) - 1 + 1)) := by
    rw [hpriorSucc]
    exact hv
  have hinputs : Restated.Vocabulary.Proofs.HealingSurface.GoldfishConeVoteInputs M S rho
      (M.opening_slot S.hc q - 1) C.erase v m := by
    have h2 := h.openingStepInputs v hv' cv (by rw [hpriorSucc]; exact hcv)
    simp only [hpriorSucc] at h2
    exact h2
  obtain ⟨hfiltered, hcandidate⟩ :=
    Restated.seedCeiling_proposalCandidateAtVoteOn facts S Hs Xb hf hHs hHsXb h.roundPositive
      hcarrier cp hcp hP hnextActionHor hheight hM (hHsXb _ hv) (hproposalAtVote v hv)
      (hvoteFrontier v hv) (hvoteGateOff v hv) hgatProp hrun
  have hcandm := hcandidate cv hcv
  have hfilteredm : P.erase ∈ M.get_filtered_block_tree (M.toHealing m.st.core).toFG := by
    rw [hm_st, facts.nd.store_with_cache_get_filtered_block_tree, facts.hd.setClock_core_eq_store_with_t_s]
    exact hfiltered
  obtain ⟨T₀, hT₀⟩ := facts.fc.voter_filtered_block_tree_nonempty S.E m.st.core m.st.core.s
  obtain ⟨A, hA⟩ := nodeAnchor_outcome₅₈ facts S m (M.round_of S.hc m.st.core.s)
  have hAP : Block.Preceq A P.erase :=
    preceq_trans_Preceq (haligned.2.1 v hv cv hcv A hA) (preceq_trans_Preceq hCI hIP)
  have hcompat : Block.compatible A P.erase = true :=
    compatible_of_preceq_common_Preceq hAP (preceq_eq_true_iff_Preceq.mp (Block.preceq_self P.erase))
  -- The frozen suffix inputs at `n` and `m`.
  have hsuffixInputs : Restated.Vocabulary.Proofs.HealingSurface.NamedFrozenProposalSuffixInputs M S rho
      (M.opening_slot S.hc q) C.erase v P n m :=
    { sourceAnchor := hsourceNode
      pivotTarget := facts.fc.voter_filtered_block_tree_subset_filtered S.E m.st.core T₀ hT₀
        (hinputs.candidate T₀ hT₀)
      proposalCandidate := hcandm
      pivotAnchorCompatible := fun A' hA' => hinputs.anchor A' hA'
      proposalAnchorCompatible := fun A' hA' =>
        compatible_of_preceq_common_Preceq
          (preceq_trans_Preceq (haligned.2.1 v hv cv hcv A' hA') (preceq_trans_Preceq hCI hIP))
          (preceq_eq_true_iff_Preceq.mp (Block.preceq_self P.erase))
      sameHMax := by
        rw [hn_st, hm_st, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_max,
          facts.hd.setClock_core_h_max, facts.hd.setClock_core_h_max]
        have h1 := hproposerFrontier
        have h2 := hvoteFrontier v hv
        rw [tickStore_h_max₅₈s facts] at h1
        rw [Restated.Vocabulary.Proofs.Optimistic.voteStore, tickStore_h_max₅₈s facts] at h2
        exact h1.trans h2.symm }
  have hsuffix := Restated.namedProposalPivotSuffixTransfer_of_frozenProposalNoRiseOn facts S Hs Xb hf
    hHs hHsXb hs hpostFrozenSnapshot hpropVote hv hvoteHor cp hcp hP' cv hcv hsuffixInputs
  -- The target walk passes through `C`.
  have hghost := Restated.roundCeiling_targetWalkPassesOn facts S Hs Xb hf hHs hHsXb hcom
    cp hcp hP h haligned hv hlo cv hcv A hA T₀ hT₀
  have hraw := Restated.voter_raw_extra_equivocates_proposal_afterGSTOn facts S Hs Xb hf hHs
    (s := M.opening_slot S.hc q) hs hpostFrozenSnapshot hpropVote hv hproposalHor cp hcp hP' cv hcv
    hfilteredm
  have hsc := Restated.namedWalkScore_target_eq_source_of_proposalCandidateOn facts Hs Xb hf hHs hHsXb
    (s := M.opening_slot S.hc q - 1) (P := P) (v := v)
  simp only [hpriorSucc] at hsc
  have hscore : ∀ psv : List (GoldfishVote V),
      M.proposer_support_view (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ psv →
      ∀ srcScore : Block V → ℕ,
        (∀ B : Block V, M.goldfish_score S.E n.st.core.T
          (M.proposer_view (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s).toFinset
          psv.toFinset (n.st.core.s - 1) B ⇢ srcScore B) →
      ∀ vv : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing m.st.core).toFG.toSG.toGoldfishStore m.st.core.s ⇢ vv →
      ∀ vsv : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing m.st.core).toFG.toSG.toGoldfishStore m.st.core.s ⇢ vsv →
      ∀ tgtScore : Block V → ℕ,
        (∀ B : Block V, M.goldfish_score S.E m.st.core.T vv vsv (m.st.core.s - 1) B ⇢ tgtScore B) →
      ∀ C' : Block V, C' ∈ M.get_filtered_block_tree (M.toHealing n.st.core).toFG →
        C' ∈ T₀.erase P.erase → tgtScore C' = srcScore C' := by
    intro psv hpsv srcScore hsrc vv hvv vsv hvsv tgtScore htgt C' hC'n hC'T
    have hvv' := hvv
    rw [hms] at hvv'
    exact hsc cp hcp cv hcv hP' hpostFrozenSnapshot hprop hvoteHor hproposalHor hv T₀ hT₀
      (hcandm T₀ hT₀) vv hvv (hraw vv hvv') vsv hvsv psv hpsv C' hC'n hC'T _ (htgt C') _ (hsrc C')
  exact ⟨T₀.erase P.erase, I.parent,
    Restated.namedProposalWalkTransferred_of_frozenCompatiblePivotOn facts S Hs Xb hf
      (s := M.opening_slot S.hc q) (pivot := C.erase) (hHsXb _ hprop) (hHsXb _ hv) cp hcp cv hcv hP'
      T₀ hT₀ (hcandm T₀ hT₀) A hA hcompat R hR hRC I hI' hCI hghost hsuffix hscore⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Statements.Instantiation

/-- Under the bundle along `W` and the committee majority, if `0 < s`, `lo ≤ vote_time s`,
    `confirmation_time s` is inside the horizon, `P` is a proposal of the read of slot `s + 1`'s
    proposer, which is in `Xb`, the vote cone of `s` holds at `A`, every SG root outcome of that
    read is an ancestor of `A`, `A` is an ancestor of the parent of every proposal input of that
    read, and every committee member of `s + 1` in the set for its vote instant has the frozen
    opening vote facts and the score agreement at its vote-duty reads on `W`, then every such member
    has, at every vote-duty read on `W`, a vote store whose walk extends to `P`. -/
theorem fixedHeightJustificationRoot_namedOpeningVoteStoresExtendOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {s : Slot} (hs : 0 < s)
    (hpost : lo ≤ M.vote_time S.E s)
    (hconfHor : M.confirmation_time S.E s ≤ rho.horizon)
    {A : Block V} {P : NamedBlock V}
    (cp : M.Cache)
    (hcp : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).st.core.toHealing
      (M.proposal_time S.E (s + 1))
      (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).cache ⇢ cp) :
    let n := M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).st
        (M.proposal_time S.E (s + 1)))
        (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).record cp
    M.proposal_with (M.gradeContract n.cache) .poolAndCarried S.E S.hc
      (S.node (S.E.proposer (s + 1))) n.st ⇢ some P →
    S.E.proposer (s + 1) ∈ Xb →
    Restated.NamedHonestVotesConeOn M S rho W Hs Xb s (fun X => Block.Preceq A X) →
    (∀ R : Block V, M.get_sg_root_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
      (M.round_of S.hc n.st.core.s) ⇢ R → Block.Preceq R A) →
    (∀ I : Protocol.ProposalInput V,
      Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract n.cache) S.E S.hc
        (S.node (S.E.proposer (s + 1))) (M.toHealing n.st.core) ⇢ I → Block.Preceq A I.parent) →
    (∀ v ∈ Hs (M.vote_time S.E (s + 1)), v ∈ S.E.committee (s + 1) →
      ∀ cv : M.Cache, M.onPhaseTick S.E S.hc
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) v).st.core.toHealing
          (M.vote_time S.E (s + 1))
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) v).cache ⇢ cv →
        Restated.Vocabulary.Proofs.HealingSurface.NamedSGOpeningFrozenVoteAt M S rho s A v P n
          (M.mkNode (M.ns_setClock S.E
            (W (strictEventIndex rho (M.vote_time S.E (s + 1))) v).st (M.vote_time S.E (s + 1)))
            (W (strictEventIndex rho (M.vote_time S.E (s + 1))) v).record cv)) →
    (∀ v ∈ Hs (M.vote_time S.E (s + 1)),
      ∀ cv : M.Cache, M.onPhaseTick S.E S.hc
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) v).st.core.toHealing
          (M.vote_time S.E (s + 1))
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) v).cache ⇢ cv →
      let m := M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) v).st (M.vote_time S.E (s + 1)))
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) v).record cv
      ∀ T₀ : Finset (Block V), M.voter_filtered_block_tree S.E m.st.core m.st.core.s ⇢ T₀ →
      ∀ psv : List (GoldfishVote V),
        M.proposer_support_view (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ psv →
      ∀ srcScore : Block V → ℕ,
        (∀ B : Block V, M.goldfish_score S.E n.st.core.T
          (M.proposer_view (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s).toFinset
          psv.toFinset (n.st.core.s - 1) B ⇢ srcScore B) →
      ∀ vv : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing m.st.core).toFG.toSG.toGoldfishStore m.st.core.s ⇢ vv →
      ∀ vsv : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing m.st.core).toFG.toSG.toGoldfishStore m.st.core.s ⇢ vsv →
      ∀ tgtScore : Block V → ℕ,
        (∀ B : Block V, M.goldfish_score S.E m.st.core.T vv vsv (m.st.core.s - 1) B ⇢ tgtScore B) →
      ∀ C : Block V, C ∈ M.get_filtered_block_tree (M.toHealing n.st.core).toFG →
        C ∈ T₀.erase P.erase → tgtScore C = srcScore C) →
    Restated.VoteStoresExtendOn M S rho Hs (s + 1)
      (W (strictEventIndex rho (M.vote_time S.E (s + 1)))) P := by
  intro n hP hprop hcone hsourceAnchor hpivotParent hfrozen hscore v hv hcommittee cv hcv
  set m := M.mkNode (M.ns_setClock S.E
    (W (strictEventIndex rho (M.vote_time S.E (s + 1))) v).st (M.vote_time S.E (s + 1)))
    (W (strictEventIndex rho (M.vote_time S.E (s + 1))) v).record cv with hm_def
  have frozen : Restated.Vocabulary.Proofs.HealingSurface.NamedSGOpeningFrozenVoteAt M S rho s A v P n m :=
    hfrozen v hv hcommittee cv hcv
  have hinputs : Restated.Vocabulary.Proofs.HealingSurface.GoldfishConeVoteInputs M S rho s A v m :=
    { candidate := fun T hT => Finset.mem_of_mem_erase (frozen.pivotCandidate T hT)
      root := by
        obtain ⟨T, hT⟩ := facts.fc.voter_filtered_block_tree_nonempty S.E m.st.core m.st.core.s
        have hAT := Finset.mem_of_mem_erase (frozen.pivotCandidate T hT)
        exact preceq_eq_true_iff_Preceq.1 (facts.fc.preceq_get_fg_root_of_mem_filtered
          (facts.fc.voter_filtered_block_tree_subset_filtered S.E m.st.core T hT hAT))
      anchor := fun a ha => frozen.pivotAnchorCompatible a ha
      path := fun a ha T hT D hAD hDne hDA _ =>
        Finset.mem_of_mem_erase (frozen.pivotPath a ha T hT
          (preceq_trans_Preceq hAD hDA) D hAD hDne hDA) }
  have hwalk := Restated.goldfishCone_pathEligibleOn facts S Hs Xb hf hHs hHsXb hcom hs hpost
    hconfHor hcone hv cv hcv hinputs
  obtain ⟨T₀, hT₀⟩ := facts.fc.voter_filtered_block_tree_nonempty S.E m.st.core m.st.core.s
  obtain ⟨A', hA'⟩ := nodeAnchor_outcome₅₈ facts S m (M.round_of S.hc m.st.core.s)
  have hghost : ∀ vv : Finset (GoldfishVote V),
      M.voter_view S.E (M.toHealing m.st.core).toFG.toSG.toGoldfishStore m.st.core.s ⇢ vv →
      ∀ vsv : Finset (GoldfishVote V),
      M.voter_support_view S.E (M.toHealing m.st.core).toFG.toSG.toGoldfishStore m.st.core.s ⇢ vsv →
      ∀ sc : Block V → ℕ,
      (∀ B : Block V, M.goldfish_score S.E m.st.core.T vv vsv (m.st.core.s - 1) B ⇢ sc B) →
      ∀ el : Block V → Bool,
      (∀ B : Block V, M.goldfish_eligible S.E m.st.core.σ m.st.core.h_max m.st.core.T m.st.core.s
        vv vsv (m.st.core.s - 1) B ⇢ el B) →
      ∀ G : Block V, M.ghost A' (T₀.erase P.erase) sc el ⇢ G → Block.Preceq A G := by
    intro vv hvv vsv hvsv sc hsc el hel G hG
    obtain ⟨hconeS, hmaj, -⟩ := hwalk vv hvv vsv hvsv
    obtain ⟨sup, hsup⟩ := facts.fc.raw_supporters_nonempty m.st.core.T vv vsv (m.st.core.s - 1) A
    have hfc := (facts.fc.goldfish_fork_choice_eq_ghost S.E m.st.core.σ m.st.core.h_max m.st.core.T
      m.st.core.s A' (T₀.erase P.erase) vv vsv (m.st.core.s - 1) sc hsc el hel G).mpr hG
    exact facts.fc.goldfish_fork_choice_captures_supporter_majority _ _ _ _ _ _ _ _ _ hconeS.sub
      sup hsup (hmaj sup hsup) (frozen.pivotAnchorCompatible A' hA')
      (fun hAA => frozen.pivotPath A' hA' T₀ hT₀ hAA) G hfc
  obtain ⟨R, hR⟩ := facts.fc.get_sg_root_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc n.st.core.s)
  obtain ⟨I, hI⟩ := facts.dt.with_proposal_input_nonempty (M.gradeContract n.cache) S.E S.hc
    (S.node (S.E.proposer (s + 1))) (M.toHealing n.st.core)
  exact ⟨T₀.erase P.erase, I.parent,
    Restated.namedProposalWalkTransferred_of_frozenCompatiblePivotOn facts S Hs Xb hf
      (s := s + 1) (pivot := A) hprop (hHsXb _ hv) cp hcp cv hcv hP
      T₀ hT₀ (frozen.proposalCandidate T₀ hT₀) A' hA' (frozen.proposalAnchorCompatible A' hA')
      R hR (hsourceAnchor R hR) I hI (hpivotParent I hI) hghost frozen.suffix
      (hscore v hv cv hcv T₀ hT₀)⟩

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Statements.Instantiation

end

end DecoupledConsensusModel.Sts.Restated
