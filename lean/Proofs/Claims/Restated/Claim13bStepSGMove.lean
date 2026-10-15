import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bDirection
import Proofs.Claims.Restated.Claim13bStepAnchor
import Proofs.Claims.Restated.Claim13bStepConeIter
import Proofs.Claims.Restated.Claim13bStepGrade
import Proofs.Claims.Restated.Claim13bStepKitConfirm
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bStepKitTick
import Proofs.Claims.Restated.Projection
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_EntryHeight
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bK_FreshAttestersW
import Model.Conditions.Claim13bStepAnchor
import Model.Conditions.Claim13bStepGrade
import Model.Conditions.Claim13bStepKitRelay
import Model.Conditions.Claim13bStepKitTick
import Model.Conditions.Claim13bStepSG
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedActionReads
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bStepSGMove

/-!
# Moving the anchor from round `r` to round `r + 1`

The finality-gadget source of a round action, ancestry between blocks in play, the round-`r` anchor
as an ancestor of the round-`(r + 1)` anchor, and the confirmed blocks of two honest validators'
action reads lying on one chain. Stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

open scoped DC in
/-- `m >>= k` can return `b` exactly when `m` can return some `a` from which `k a` can return `b`. -/
private theorem returns_bind_iff_sgMove {α β : Type} (m : DC.NDRE α) (k : α → DC.NDRE β) (b : β) :
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

open scoped DC in
/-- If `m` can return `a`, then `f <$> m` can return `f a`. -/
private theorem returns_map_intro_sgMove {α β : Type} (f : α → β) (m : DC.NDRE α) (a : α)
    (h : m ⇢ a) : (f <$> m) ⇢ f a := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image]
  exact ⟨_, h, rfl⟩

open scoped DC in
/-- If `a` is a member of the set `s`, then the lift of `s` can return `a`. -/
private theorem returns_lift_intro_sgMove {α : Type} (s : Set α) (a : α) (h : a ∈ s) :
    (ExceptT.lift s : DC.NDRE α) ⇢ a := by
  unfold Record.Returns
  simp only [ExceptT.run_lift, Set.fmap_eq_image, Set.mem_image]
  exact ⟨a, h, rfl⟩

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For every node state `n` of round `r₁`'s action read from `before`, if the finality-gadget
    source at `n` can return `Cfg`, then `Cfg` is an ancestor of the confirmed block of `n`'s
    healing store, or every grade read at `n`'s cache and store has `Cfg` as its grade-2 candidate. -/
theorem source_cases (facts : Record.Facts M) (S : Setup V) (before : M.N) (r₁ : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        before r₁, ∀ (Cfg : Block V),
    Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M (Setup.alwaysAwake S) n ⇢ some Cfg →
    Block.Preceq Cfg (M.toHealing n.st.core).live_confirmed ∨
      ∀ g, M.frameGradeRead n.cache S.E S.hc (M.toHealing n.st.core) r₁ ⇢ g →
        g.Q2 = some Cfg := by
  intro n hn Cfg hsrc
  have hR : M.round_of S.hc (M.toHealing n.st.core).s = r₁ := by
    obtain ⟨c, -, D, hD, rfl⟩ := hn
    obtain ⟨X, hX⟩ := facts.dt.update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc
      (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core
      (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1)
    rw [facts.nd.mkNode_st, Record.Model.HS.s, facts.sto.toHealing_gs_s,
      facts.nd.store_with_cache_core_s, facts.dt.named_update_confirmation_with_core _ _ _ _ _ D hD X hX,
      ← facts.sto.toHealing_gs_s, facts.dt.update_confirmation_with_toHealing_s _ _ _ _ _ X hX,
      facts.sto.toHealing_gs_s, facts.hd.Sts_setClock_core_s]
    exact Restated.Vocabulary.Proofs.HealingLemmas.round_of_slotOf_a facts S r₁
  obtain ⟨A2, hA2, hF⟩ := (returns_bind_iff_sgMove _ _ _).1 hsrc
  change M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
    (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ A2 at hA2
  change M.fg_source_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
    (M.round_of S.hc (M.toHealing n.st.core).s) A2 ⇢ some Cfg at hF
  rw [hR] at hA2 hF
  rcases facts.dt.fg_source_cases _ S.E S.hc _ r₁ (some Cfg) hF rfl with hpre | hQ
  · exact Or.inl hpre
  · refine Or.inr fun g hg => ?_
    rw [← facts.nd.gradeContract_grade2_block_with n.cache S.E S.hc _ r₁ g hg A2 hA2]
    exact hQ

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If the erasure of one block the execution put in play is an ancestor of the erasure of another,
    then the first is a named ancestor of the second. -/
theorem namedPreceq_of_blockInLog (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (hroot : Restated.RootCollisionFreeInLog M S Sched x)
    {A B : NamedBlock V} (hA : Restated.blockInLog M S Sched x A) (hB : Restated.blockInLog M S Sched x B)
    (h : Block.Preceq A.erase B.erase) : NamedBlock.Preceq A B := by
  obtain ⟨A', hA'B, hA'er⟩ := Proofs.NamedAncestry.erased_ancestor_lift B h
  have hA'root : A'.root = A.root := by
    rw [← Proofs.NamedWire.erase_root A', hA'er, Proofs.NamedWire.erase_root A]
  have hA'eq : A' = A :=
    hroot.root_injective B A hB hA A' A (Or.inl hA'B)
      (Or.inr (Proofs.NamedAncestry.named_self A)) hA'root
  rw [← hA'eq]
  exact hA'B

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If a block the execution put in play is named by its own replay as its chain-state height's
    entry, and it lies on one chain with another block in play whose chain-state height is at least
    its own, then it is an ancestor of that block. -/
theorem preceq_of_entry_compatible_sts (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (hroot : Restated.RootCollisionFreeInLog M S Sched x)
    {A B : NamedBlock V} (hA : Restated.blockInLog M S Sched x A) (hB : Restated.blockInLog M S Sched x B)
    (hentry : (M.derive_named S.E S.cfg A).T_h = A.erase)
    (hcomp : Block.compatible A.erase B.erase = true)
    (hh : (M.derive_named S.E S.cfg A).h ≤ (M.derive_named S.E S.cfg B).h) :
    Block.Preceq A.erase B.erase := by
  rcases compatible_cases hcomp with hle | hge
  · exact hle
  · have hBA : NamedBlock.Preceq B A := Restated.namedPreceq_of_blockInLog facts S Sched x hroot hB hA hge
    have hmono : (M.derive_named S.E S.cfg B).h ≤ (M.derive_named S.E S.cfg A).h :=
      facts.cs.derive_height_mono S.E S.cfg hBA
    have hheq : (M.derive_named S.E S.cfg B).h = (M.derive_named S.E S.cfg A).h :=
      le_antisymm hmono hh
    have hTh : (M.derive_named S.E S.cfg B).T_h
        = (M.derive_named S.E S.cfg A).T_h :=
      facts.cs.entry_eq_on_plateau S.E S.cfg hBA hheq
    have hgeo : Block.Preceq (M.derive_named S.E S.cfg B).T_h B.erase :=
      Restated.Vocabulary.Proofs.NamedEntryHeight.entry_geometry_ancestor facts S.E S.cfg B
    rw [hTh, hentry] at hgeo
    exact hgeo

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The core store of every node state of the round-`r` action read from `before` has the
    chain-state map of `before`'s core store. -/
private theorem actionReadFrom_σ_sgMove (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      n.st.core.σ = before.st.core.σ := by
  rintro _ ⟨c, -, st, hst, rfl⟩
  rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
  obtain ⟨X, hX⟩ := facts.dt.update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc
    (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r)).core
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
  rw [facts.dt.named_update_confirmation_with_core _ _ _ _ _ st hst X hX,
    facts.dt.update_confirmation_with_σ _ _ _ _ _ X hX, facts.hd.ModelProperties_setClock_core_σ]

/-- If a fresh honest attester `q`'s round-`(r + 1)` height vote carries the height `h₀` and the
    root `entry`, then for every node state `n` of `q`'s round-`(r + 1)` action read from its node
    state at step `n'` and every outcome `D` of the attestation duty at `n` with that vote, every
    outcome of the finality-gadget source at `n` is a block `Cfg` of which the body `C` with root
    `entry` is an ancestor. -/
theorem entry_preceq_source (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {r : Round} {n' : Nat} (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)))) {q : V}
    (hq : q ∈ Restated.freshAttesters M S Sched x (r + 1) (n' + 1))
    {h₀ : Height} {entry : BlockId} {tmo : Bool}
    {C : NamedBlock V} (hC : C ∈ (x[n'][q].st).st.bodies) (hCroot : C.root = entry) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (x[n'][q].st) (r + 1),
    ∀ D, M.duties_attest_with (M.gradeContract n.cache) S.E S.hc ((Setup.alwaysAwake S).node q)
        n.st n.record ⇢ D →
    D.2.2.height_pair = NamedHeightPair.vote h₀ entry tmo →
    ∀ o, Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M (Setup.alwaysAwake S) n ⇢ o →
    ∃ Cfg : Block V, o = some Cfg ∧ Block.Preceq C.erase Cfg := by
  classical
  intro n hn D hD hvote o ho
  have hhon : Restated.HonestThrough M Sched x n' q := by
    intro t ht
    exact Restated.honestThrough_of_mem_freshAttesters facts hq t
      (le_trans ht (Restated.time_mono_int facts S Sched x (Nat.le_succ n')))
  obtain ⟨w₀, hw₀, hw₀q⟩ := Restated.stateBeforeTime_runOf_action facts S Sched x hn' q
  have hw₀' : w₀ ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M (Setup.alwaysAwake S)
      (Record.runOfM M S Sched x q (n' + 1))
      (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (r + 1)) := hw₀
  have hnw : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M
      (Setup.alwaysAwake S) (w₀ q) (r + 1) := by
    rw [hw₀q]; exact hn
  have hn₀ : n ∈ Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt M (Setup.alwaysAwake S)
        (Record.runOfM M S Sched x q (n' + 1)) q (r + 1) :=
    ⟨w₀, hw₀', hnw⟩
  obtain ⟨Cfg, rfl, hCfgh, hCfgroot⟩ :=
    Restated.source_of_actionAttestation_heightPair facts (Setup.alwaysAwake S)
      (Record.runOfM M S Sched x q (n' + 1)) q (r + 1) n hn₀ D hD hvote o ho
  have hCfgT := Restated.fgSource_mem_stateBeforeTime' facts (Setup.alwaysAwake S)
    (Record.runOfM M S Sched x q (n' + 1)) q (r + 1) w₀ hw₀' n hnw ho
  have hco := (Restated.Vocabulary.Proofs.NamedRuntime.stateBeforeTime_invariants facts (Setup.alwaysAwake S)
    (Record.runOfM M S Sched x q (n' + 1)) ((Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (r + 1))) q
    w₀ hw₀').1.1.1
  have hCfgroot' : ((x[n'][q].st).st.core.σ Cfg).T_h.root = entry := by
    rw [← actionReadFrom_σ_sgMove facts (Setup.alwaysAwake S) (x[n'][q].st) (r + 1) n hn]
    exact hCfgroot
  rw [hw₀q] at hCfgT hco
  rw [hco.1] at hCfgT
  obtain ⟨Cfgn, hCfgnMem, hCfgnErase⟩ := Finset.mem_image.mp hCfgT
  have hσ : (x[n'][q].st).st.core.σ Cfg = M.derive_named S.E S.cfg Cfgn := by
    have hd := hco.2.2.2.2 Cfgn hCfgnMem
    rw [hCfgnErase] at hd
    exact hd
  obtain ⟨E0, hE0le, hE0er, hE0h⟩ :=
    facts.cs.entry_ancestor_same_height S.E S.cfg Cfgn
  have hE0mem : E0 ∈ (x[n'][q].st).st.bodies :=
    Restated.mem_bodies_of_preceq hco.2.2.1 hCfgnMem hE0le
  have hE0root : E0.root = C.root := by
    rw [← Proofs.NamedWire.erase_root E0, hE0er, ← hσ, hCfgroot']
    exact hCroot.symm
  have hClog : Restated.blockInLog M S Sched x C := Restated.blockInLog_of_mem_bodies facts S Sched hhon hC
  have hE0log : Restated.blockInLog M S Sched x E0 := Restated.blockInLog_of_mem_bodies facts S Sched hhon hE0mem
  have hE0eq : E0 = C :=
    hexec.idealization.root_injective E0 C hE0log hClog E0 C
      (Or.inl (Proofs.NamedAncestry.named_self E0))
      (Or.inr (Proofs.NamedAncestry.named_self C)) hE0root
  refine ⟨Cfg, rfl, ?_⟩
  rw [← hE0eq, ← hCfgnErase]
  exact Proofs.NamedWire.erase_preceq hE0le

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The round-`r` anchor `T` is an ancestor of the round-`(r + 1)` anchor read along a choice `att`
    of the round-`(r + 1)` action attestations. -/
theorem old_preceq_new (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {r : Round} {n' : Nat} (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    {att : V → NamedAttestation V} (hatt : Restated.ActionAttestationsOf M S Sched x r n' att)
    {T : NamedBlock V}
    (hT : Restated.blockInLog M S Sched x T)
    (hTentry : (M.derive_named S.E S.cfg T).T_h = T.erase)
    (hcomp : Block.compatible T.erase (Restated.newAnchor M S Sched x r n' att T).erase = true) :
    Block.Preceq T.erase (Restated.newAnchor M S Sched x r n' att T).erase := by
  refine Restated.preceq_of_entry_compatible_sts facts S Sched x hexec.idealization hT
    (Restated.newAnchor_blockInLog facts S Sched x hT) hTentry hcomp ?_
  rw [Restated.newAnchor_height facts S Sched x hn' hatt T]
  exact le_max_left _ _

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For every choice `att` of attestations, if the round-`r` anchor `T`'s own replay names it as its
    chain-state height's entry, then so does the replay of the round-`(r + 1)` anchor read along
    `att`. -/
theorem newAnchor_entry (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {r : Round} {n' : Nat}
    {att : V → NamedAttestation V} {T : NamedBlock V}
    (hTentry : (M.derive_named S.E S.cfg T).T_h = T.erase) :
    (M.derive_named S.E S.cfg (Restated.newAnchor M S Sched x r n' att T)).T_h
      = (Restated.newAnchor M S Sched x r n' att T).erase := by
  classical
  by_cases hex : ∃ C : NamedBlock V, Restated.NewAnchorSpec M S Sched x r n' att T C
  · have hchoice : Restated.newAnchor M S Sched x r n' att T = hex.choose := by
      show (if h : ∃ C : NamedBlock V, Restated.NewAnchorSpec M S Sched x r n' att T C then h.choose else T)
        = hex.choose
      rw [dif_pos hex]
    rw [hchoice]
    exact hex.choose_spec.2.2.1
  · have hchoice : Restated.newAnchor M S Sched x r n' att T = T := by
      show (if h : ∃ C : NamedBlock V, Restated.NewAnchorSpec M S Sched x r n' att T C then h.choose else T)
        = T
      rw [dif_neg hex]
    rw [hchoice]
    exact hTentry

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For a store `hs` round `(r + 1)`'s action can read from `before`, the fork-choice root of
    `before`'s store stamped with the confirmation time of round `r + 1`'s opening slot is an
    ancestor of `T` when `hs`'s finalized block is and, if `hs`'s running height maximum is one more
    than its justified height, `hs`'s justified block is too. -/
theorem confRoot_setClock_preceq_ofAction (facts : Record.Facts M) (S : Setup V) (before : M.N) (r : Round)
    {T : Block V} (hs : M.HS) (hhs : hs ∈ Restated.actionHealingStore M S before (r + 1))
    (hF : Block.Preceq hs.F T)
    (hJ : hs.h_max = hs.h_j + 1 → Block.Preceq hs.J T) :
    Block.Preceq (Restated.Vocabulary.Protocol.confRoot M (M.ns_setClock S.E before.st
      (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1))))).core) T := by
  obtain ⟨c, hc, X, hX, st₀, hst₀, rfl⟩ := Restated.actionHealingStore_eq facts S before (r + 1) hs hhs
  obtain ⟨hF₀, hJ₀, hhj₀, hhm₀, hlc₀, hT₀, hs₀, hσ₀⟩ :=
    Restated.HS_fields_store_with_cache facts c hst₀
  simp only [hF₀, hJ₀, hhj₀, hhm₀, hlc₀, hT₀, hs₀, hσ₀] at *
  rw [Record.Model.HS.F, facts.hd.update_confirmation_with_toHealing_F _ _ _ _ _ X hX,
    facts.hd.setClock_toHealing_F] at hF
  rw [Record.Model.HS.h_max, Record.Model.HS.h_j, Record.Model.HS.J,
    facts.dt.update_confirmation_with_toHealing_h_max _ _ _ _ _ X hX,
    facts.dt.update_confirmation_with_toHealing_h_j _ _ _ _ _ X hX,
    facts.dt.update_confirmation_with_toHealing_J _ _ _ _ _ X hX,
    facts.hd.setClock_toHealing_h_max, facts.hd.setClock_toHealing_h_j, facts.hd.setClock_toHealing_J] at hJ
  unfold Restated.Vocabulary.Protocol.confRoot
  rw [Record.Model.S.toHealing]
  refine facts.fc.fgRoot_preceq_ofJustifiedBranch ?_ ?_
  · rw [facts.hd.setClock_toHealing_F]
    exact hF
  · rw [facts.hd.setClock_toHealing_h_max, facts.hd.setClock_toHealing_h_j, facts.hd.setClock_toHealing_J]
    exact hJ

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Stamping the clock of a store does not change which blocks pass the confirmation eligibility
    test for slot `s`. -/
private theorem confEligible_setClock_sgMove (facts : Record.Facts M) (E : Env V) (st : M.NS)
    (t : Int) (s : Slot) :
    Restated.Vocabulary.Protocol.confEligible M E (M.ns_setClock E st t).core s
      = Restated.Vocabulary.Protocol.confEligible M E st.core s := by
  have htau : (M.ns_setClock E st t).core.tau = st.core.tau :=
    facts.sto.tau_eq_of_fields (facts.hd.Sts_setClock_core_T E st t)
      (facts.hd.setClock_core_timestamp_block E st t) (facts.hd.setClock_core_timestamp_vote E st t)
  have hpool : (M.ns_setClock E st t).core.pool s = st.core.pool s :=
    facts.hd.Sts_setClock_core_pool E st t s
  unfold Restated.Vocabulary.Protocol.confEligible
    Restated.Vocabulary.Protocol.confCount Restated.Vocabulary.Protocol.confVotes
    Restated.Vocabulary.Protocol.confEarly Restated.Vocabulary.Protocol.confLate
  rw [htau, hpool, facts.hd.setClock_core_timestamp_vote, facts.hd.Sts_setClock_core_T]

/-- For every store `hs` the round-`r₁` action read can give from `before`, the block `hs` holds as
    confirmed either passes some outcome of the confirmation eligibility test of `before`'s store
    for the slot before the action instant's slot, or is the fork-choice root of `before`'s store
    stamped with the action instant. -/
private theorem actionHealingStore_live_confirmed_cases (facts : Record.Facts M) (S : Setup V)
    (before : M.N) (r₁ : Round) (hs : M.HS)
    (hhs : hs ∈ Restated.actionHealingStore M S before r₁) :
    (∃ el : Block V → Bool, Restated.Vocabulary.Protocol.confEligible M S.E before.st.core
        (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1) ⇢ el ∧
        el hs.live_confirmed = true) ∨
      hs.live_confirmed
        = Restated.Vocabulary.Protocol.confRoot M
            (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core := by
  classical
  obtain ⟨c, hc, X, hX, st₀, hst₀, rfl⟩ := Restated.actionHealingStore_eq facts S before r₁ hs hhs
  obtain ⟨hF₀, hJ₀, hhj₀, hhm₀, hlc₀, hT₀, hs₀, hσ₀⟩ :=
    Restated.HS_fields_store_with_cache facts c hst₀
  simp only [hF₀, hJ₀, hhj₀, hhm₀, hlc₀, hT₀, hs₀, hσ₀] at *
  rw [Record.Model.HS.live_confirmed, facts.sto.toHealing_live_confirmed]
  by_cases hroot : X.live_confirmed = Restated.Vocabulary.Protocol.confRoot M
      (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core
  · exact Or.inr hroot
  · left
    obtain ⟨tm, htm⟩ := facts.sto.tau_nonempty
      (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core
    obtain ⟨R, hR⟩ := facts.fc.get_sg_root_with_nonempty (M.gradeContract c) S.E S.hc
      (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core.toHealing
      (M.round_of S.hc
        (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core.s)
    obtain ⟨score, hscore⟩ : ∃ score : Block V → ℕ, ∀ B, M.goldfish_score S.E
        (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core.T
        ((beforeCutoff tm (M.support_cutoff S.E (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1))
          ((M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core.pool
            (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1))).filter
          (fun u => M.no_second_vote_in (Restated.Vocabulary.Protocol.confLate M S.E
            (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core
            (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1)) u = true))
        ((beforeCutoff tm (M.support_cutoff S.E (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1))
          ((M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core.pool
            (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1))).filter
          (fun u => M.no_second_vote_in (Restated.Vocabulary.Protocol.confLate M S.E
            (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core
            (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1)) u = true))
        (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1) B ⇢ score B :=
      ⟨fun B => (facts.fc.goldfish_score_nonempty _ _ _ _ _ B).choose,
        fun B => (facts.fc.goldfish_score_nonempty _ _ _ _ _ B).choose_spec⟩
    obtain ⟨W, hW⟩ := facts.fc.ghost_nonempty R
      (M.get_filtered_block_tree
        (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core.toHealing.toFG)
      score
      (fun B => decide (Restated.Vocabulary.Protocol.confCount M S.E
        (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core
        (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1) < 2 * score B))
    have hwalk := facts.hd.update_confirmation_with_live_confirmed_walk_or_fgRoot
      (M.gradeContract c) S.E S.hc
      (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core
      (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1) tm htm R hR score hscore W hW X hX
    have hgen := facts.hd.update_confirmation_with_live_confirmed_genuine_or_fgRoot
      (M.gradeContract c) S.E S.hc
      (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core
      (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1) tm htm R hR score hscore W hW X hX
    rcases hwalk with hwalk | hfg
    · rcases hgen with ⟨-, -, hel⟩ | hfg
      · refine ⟨fun B => decide (Restated.Vocabulary.Protocol.confCount M S.E
          (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core
          (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1) < 2 * score B), ?_, ?_⟩
        · rw [← confEligible_setClock_sgMove facts S.E before.st
            (Restated.Vocabulary.Execution.Setup.a M S r₁)]
          refine (returns_bind_iff_sgMove _ _ _).2 ⟨_, returns_map_intro_sgMove _ _ _
            (returns_map_intro_sgMove _ _ _ htm), ?_⟩
          refine (returns_bind_iff_sgMove _ _ _).2 ⟨score, returns_lift_intro_sgMove _ _ hscore, ?_⟩
          exact (Record.returns_pure _ _).2 rfl
        · rw [hwalk]
          exact hel
      · exact absurd hfg hroot
    · exact absurd hfg hroot

/-- For a store `hsv` round `(r + 1)`'s action can read from `v`'s node state at step `n'` and a
    store `hsw` it can read from `w`'s, if each one's confirmed block lies on one chain with `T`,
    each one's finalized block is an ancestor of `T`, and each one's justified block is an ancestor
    of `T` when its running height maximum is one more than its justified height, then the confirmed
    blocks of `hsv` and `hsw` lie on one chain. -/
theorem live_confirmed_pairwise (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hrelay : Restated.GfVoteRelayAtAccept M S x) (htd : Restated.TimeDiverges M x)
    {r : Round} {n' : Nat} {v w : V} {T : NamedBlock V}
    (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (hgst : S.E.t_GST ≤ slotStart S.E.Δ ((M.opening_slot S.hc (r + 1))))
    (hv : Restated.HonestThrough M Sched x n' v) (hw : Restated.HonestThrough M Sched x n' w)
    (hvr : v ∉ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)))) (hwr : w ∉ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (hawv : v ∈ Sched.awakeThroughout
      (slotStart S.E.Δ ((M.opening_slot S.hc (r + 1))) - S.E.Δ)
      (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1)))))
    (haww : w ∈ Sched.awakeThroughout
      (slotStart S.E.Δ ((M.opening_slot S.hc (r + 1))) - S.E.Δ)
      (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1)))))
    (hsv : M.HS) (hhsv : hsv ∈ Restated.actionHealingStore M S (x[n'][v].st) (r + 1))
    (hsw : M.HS) (hhsw : hsw ∈ Restated.actionHealingStore M S (x[n'][w].st) (r + 1))
    (hconfv : Block.compatible hsv.live_confirmed T.erase = true)
    (hconfw : Block.compatible hsw.live_confirmed T.erase = true)
    (hFv : Block.Preceq hsv.F T.erase)
    (hFw : Block.Preceq hsw.F T.erase)
    (hJv : hsv.h_max = hsv.h_j + 1 → Block.Preceq hsv.J T.erase)
    (hJw : hsw.h_max = hsw.h_j + 1 → Block.Preceq hsw.J T.erase)
    (hneTickv : ∀ (n'' : Nat) (t : Int), Restated.tickStepAt M x n'' t → t % S.E.Δ = 0 → v ∈ Sched.awake t \ Sched.adv t →
      slotStart S.E.Δ (M.opening_slot S.hc (r + 1)) ≤ t →
      t ≤ M.confirmation_time S.E (M.opening_slot S.hc (r + 1)) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched t x[n''] v) t ⇢ out)
    (hneTickw : ∀ (n'' : Nat) (t : Int), Restated.tickStepAt M x n'' t → t % S.E.Δ = 0 → w ∈ Sched.awake t \ Sched.adv t →
      slotStart S.E.Δ (M.opening_slot S.hc (r + 1)) ≤ t →
      t ≤ M.confirmation_time S.E (M.opening_slot S.hc (r + 1)) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched t x[n''] w) t ⇢ out) :
    Block.compatible hsv.live_confirmed hsw.live_confirmed = true := by
  classical
  have hct : M.confirmation_time S.E ((M.opening_slot S.hc (r + 1))) = (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) :=
    Restated.confirmation_time_opening_slot facts S (r + 1)
  have hn'' : Restated.tickStepAt M x n' (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1)))) := by
    rw [hct]; exact hn'
  -- the fork-choice roots the two fallbacks return are ancestors of `T`
  have hrootv := Restated.confRoot_setClock_preceq_ofAction facts S (x[n'][v].st) r hsv hhsv hFv hJv
  have hrootw := Restated.confRoot_setClock_preceq_ofAction facts S (x[n'][w].st) r hsw hhsw hFw hJw
  rw [hct] at hrootv hrootw
  -- each action read's confirmed block passes the eligibility test or is that root
  have hcv := actionHealingStore_live_confirmed_cases facts S (x[n'][v].st) (r + 1) hsv hhsv
  have hcw := actionHealingStore_live_confirmed_cases facts S (x[n'][w].st) (r + 1) hsw hhsw
  rw [Restated.slotOf_a_sub_one facts S (r + 1)] at hcv hcw
  rcases hcv with ⟨elv, helv, hev⟩ | hfv <;> rcases hcw with ⟨elw, helw, hew⟩ | hfw
  · exact Restated.confirmed_compatible_sts_of_gfVoteRelay facts S Sched x hexec hrelay htd hn''
      (facts.gr.opening_slot_pos S (Nat.succ_pos r)) hgst hv hw hawv haww helv hev helw hew
      hneTickv hneTickw
  · rw [hfw]
    exact Protocol.compatible_comm
      (Protocol.compatible_of_preceq_of_compatible hrootw (Protocol.compatible_comm hconfv))
  · rw [hfv]
    exact Protocol.compatible_of_preceq_of_compatible hrootv (Protocol.compatible_comm hconfw)
  · rw [hfv, hfw]
    exact compatible_of_preceq_common_Preceq hrootv hrootw

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For every choice `att` of attestations, the round-`(r + 1)` anchor read along `att` is one of
    the blocks the execution put in play. -/
theorem inPlay_field_at_new_anchor (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {r : Round} {n' : Nat}
    {att : V → NamedAttestation V} {T : NamedBlock V}
    (hT : Restated.blockInLog M S Sched x T) :
    Restated.blockInLog M S Sched x (Restated.newAnchor M S Sched x r n' att T) :=
  Restated.newAnchor_blockInLog facts S Sched x hT

end

end DecoupledConsensusModel.Sts.Restated
