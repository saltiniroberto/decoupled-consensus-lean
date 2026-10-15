import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bK_ProposalAdoption
import Proofs.Claims.Restated.Claim13beRoute3_44
import Proofs.Claims.Restated.Claim13beRoute3_45
import Proofs.Claims.Restated.Claim13beRoute3_45b
import Proofs.Claims.Restated.Claim13beRoute3_46
import Proofs.Claims.Restated.Claim13beRoute3_47
import Proofs.Claims.Restated.Claim13beRoute3_51
import Proofs.Claims.Restated.Claim13beRoute3_55
import Proofs.Claims.Restated.Claim13beRoute3_58
import Proofs.Claims.Restated.Claim13beRoute3_65b
import Proofs.Claims.Restated.Claim13beRoute3_67b
import Proofs.Claims.Restated.Claim13beRoute3_71
import Proofs.Claims.Restated.Claim13beRoute3_72
import Proofs.Claims.Restated.Claim13beRoute3_85b
import Proofs.Claims.Restated.Claim13beRoute3_85d
import Proofs.Claims.Restated.Claim13beRoute3_86e
import Proofs.Claims.Restated.Claim13beRoute3_86f
import Proofs.Claims.Restated.Claim13beRoute3_86g
import Proofs.Claims.Restated.Vocabulary_Objects_ActionRound
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_NamedNjGap
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_ProposalBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_ReaderLocalCone
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_RecoveryProposalConfirmationRead
import Proofs.Claims.Restated.Vocabulary_ModelVocabulary_Healing_Schedule
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_W4GSTZeroOpeningLifecycle
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedDutyReads
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_TickBridges
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_GSTZeroActionHead
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_MovingChainRoundRead
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_SlotInduction
import Model.Conditions.Claim13bK_ActionHeads
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
import Model.Conditions.Vocabulary_Internal_Invariants
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedHeadReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ProposalSourcesInternal
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Agreement
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Internal_Definitions_NamedResult23Statements
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_FinalityPairCore
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring

/-!
# Honest action heads at a strong window

Over a model `M : Record.Model V`: an honest action head descends from a block every counted
committee member voted, and after the deadline round the honest action heads of a round equal the
proposal of the slot after the round's opening (`honestActionHeadsAtStrongWindow_f1b2`). A
validator's round-`r` action store is a node state of its action read, staged from its node state in
the path's world strictly before `S.a r`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

/-- A private theorem of the module `Proofs.Claims.Restated.Claim13beRoute3_51`, by name. -/
local macro "p51% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_51)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- A private theorem of the module `Proofs.Claims.Restated.Claim13beRoute3_58`, by name. -/
local macro "p58% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_58)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- A private theorem of the module `Proofs.Claims.Restated.Claim13beRoute3_60`, by name. -/
local macro "p60% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_60)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- A private theorem of the module `Proofs.Claims.Restated.Claim13beRoute3_64b`, by name. -/
local macro "p64b% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_64b)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- A private theorem of the module `Proofs.Claims.Restated.Claim13beRoute3_71`, by name. -/
local macro "p71% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_71)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- A private theorem of the module `Proofs.Claims.Restated.Claim13beRoute3_86g`, by name. -/
local macro "p86g% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_86g)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- A private theorem of the module `Proofs.Claims.Restated.Claim13beRoute3_56`, by name. -/
local macro "p56% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_56)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

open scoped DC in
/-- If `m` can return `a`, then `f <$> m` can return `f a`. -/
private theorem returns_map_intro_ah {α β : Type} (f : α → β) (m : DC.NDRE α) (a : α)
    (h : m ⇢ a) : (f <$> m) ⇢ f a := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image]
  exact ⟨_, h, rfl⟩

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

/-- The SG root under the grade contract of any cache `c'`, read from the healing view of a store
    with cache `c` written in, is the one read from the store's own healing view. -/
private theorem sgRoot_store_with_cache_ah (facts : Record.Facts M) {E : Env V}
    {hc : Protocol.HealConfig} {st : M.NS} {c c' : M.Cache} {r : Round} {x : Block V} :
    M.get_sg_root_with (M.gradeContract c') E hc (M.toHealing (M.store_with_cache st c).core) r ⇢ x ↔
      M.get_sg_root_with (M.gradeContract c') E hc (M.toHealing st.core) r ⇢ x := by
  rw [facts.nd.gradeContract_sgRoot_eq_frameAnchor, facts.nd.gradeContract_sgRoot_eq_frameAnchor,
    facts.nd.store_with_cache_readFrame]
  exact facts.gr.anchor_eq_of_filtered_fg_root E hc r _
    (facts.nd.store_with_cache_get_filtered_block_tree st c) (facts.nd.store_with_cache_get_fg_root st c) x

/-- For a round `c` with `rD + 2 ≤ c` and `S.a c` within the horizon of `R_n`, whose opening
    proposer is not held at the opening slot's confirmation instant: along the path the execution
    follows, for every proposal `P` of the opening proposer, every validator `v` not held at
    `S.a c`, every node state `nv` of its round-`c` action read and every outcome `Rt` of the SG
    root at `nv` for round `c`, `Rt` is an ancestor of `P`. -/
theorem actionSGRoot_preceq_openingProposal_f1b2 (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v₀ : V) (n : Nat)
    {tGAT tL : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tL → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tL →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hn : (x[n].time : Int) ≤ tL)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tL gap)
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
    ∀ v ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M S c)),
      ∀ nv ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (W (strictEventIndex R (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c)) v) c,
      ∀ Rt : Block V,
        M.get_sg_root_with (M.gradeContract nv.cache) S.E S.hc (M.toHealing nv.st.core) c ⇢ Rt →
        Block.Preceq Rt P.erase := by
  intro R W wp cp hcp pn hP v hv nv hnv Rt hRt
  obtain ⟨hpost, -, hloOpen, ht₀⟩ := Restated.roundAt_bounds_l71 facts S hgst
  have hf := Restated.admissibleFieldsOn_runAll_notHeld facts S Sched x v₀ n hsync hmono hawake hgst hcv
    hvalid hawm hthird hn
  have hread := Restated.openingProposal_confirmationRead_afterDeadlineOn facts
    (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ hf
    (fun _ _ h => notHeldAt_anti hmono h) (fun _ => Finset.subset_univ _)
    (Restated.honestCommitteesOn_notHeld facts S Sched hcom)
    (Restated.belowOneThirdOn_runAll_notHeld facts S Sched x v₀ n hthird hn)
    (Restated.multiProposerRecurrenceOn_runAll_notHeld facts S Sched x v₀ n hrec hn)
    (Setup.timeoutDelayBound _) hpost
    (by rw [Restated.fgSafetyProgressDeadline_eq_deadlineRoundW facts]; exact hc)
    hhor hopening cp hcp hP (Restated.roundAt_lo_le_rGST_l71 facts S tGAT) hloOpen ht₀
    (fun k u hk _ j hj => Restated.awake_g2_action_runAllPath facts S Sched x v₀ n hmono hawake hn
      k hk u j hj) v hv
  have hct : M.confirmation_time (Setup.alwaysAwake S).E (M.opening_slot (Setup.alwaysAwake S).hc c) =
      Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c :=
    (Restated.Vocabulary.Protocol.a_eq_confirmation_time facts S.hc S.E c).symm
  rw [hct] at hread
  -- `Rt` is the anchor of an outcome `g` of `nv`'s grade read, so an outcome of `nv`'s anchor
  obtain ⟨g, hg⟩ := facts.gr.read_nonempty (M.gradeContract nv.cache) S.E S.hc
    (M.toHealing nv.st.core) c
  have hRg := facts.fc.get_sg_root_with_eq_read_anchor _ S.E S.hc _ c g hg Rt hRt
  have hanchor : Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M (Setup.alwaysAwake S) nv c ⇢ Rt := by
    rw [hRg]
    exact returns_map_intro_ah _ _ g hg
  have hmem := (p64b% mem_stateBeforeTime_along₆₄b) hf.sorted hf.onePath
    (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c)
  have hconfA := (Restated.Vocabulary.Proofs.w4_confAnchorWith_eq_nodeAnchor facts (Setup.alwaysAwake S) R v c
    _ hmem nv hnv Rt).2 hanchor
  obtain ⟨cc, hcc, st, hst, rfl⟩ := hnv
  refine (hread cc hcc).2.1 Rt ?_
  unfold Restated.Vocabulary.Internal.namedConfirmationAnchor
  rewrite [facts.nd.mkNode_cache, facts.nd.mkNode_st, sgRoot_store_with_cache_ah facts]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
  rw [facts.nd.mkNode_cache] at hconfA
  unfold Restated.Vocabulary.Protocol.confAnchorWith Restated.Vocabulary.Proofs.Optimistic.tickStore at hconfA
  rw [← facts.hd.setClock_core_eq_store_with_t_s] at hconfA
  rw [hct] at hconfA
  exact hconfA

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

/-- Under `hf` along the path `W` and the committee majority, with `0 < q`, `lo ≤ vote_time q`,
    `support_cutoff q` in the horizon and equal to `S.a r`, `v` in the set for `S.a r`, `B` the
    erasure of a run block along `W` of slot at most `q`, every committee member of `q` in the set
    for `q`'s vote instant voting `B` at that instant, `n` a node state of `v`'s round-`r` action
    read on `W`, `B` in the filtered tree of `n`'s store, and every outcome of the SG root at `n`
    for round `r` an ancestor of `B`: `B` is an ancestor of every block the action head computed on
    `n` can return. -/
theorem preceq_actionHeadAt_of_votesOn_f1b2 (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {q : Slot} (hq : 0 < q) (hpost : lo ≤ M.vote_time S.E q)
    (hhor : M.support_cutoff S.E q ≤ rho.horizon)
    {r : Round} (ha : (Restated.Vocabulary.Execution.Setup.a M S r) = M.support_cutoff S.E q)
    {v : V} (hv : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)))
    {B : Block V} {Bn : NamedBlock V} (hBn : Bn.erase = B)
    (hBrun : Restated.RunBlockOn M S rho W Xb Bn)
    (hBslot : B.slot ≤ q)
    (hvotes : ∀ x ∈ Hs (M.vote_time S.E q), x ∈ S.E.committee q →
      Restated.Vocabulary.Execution.NamedRun.emits M S rho W x (.gfVote ⟨x, q, B.root⟩)
        (M.vote_time S.E q))
    (n : M.N)
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r)
    (hactive : B ∈ M.get_filtered_block_tree (M.toHealing n.st.core).toFG)
    (hsg : ∀ Rt : Block V,
      M.get_sg_root_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core) r ⇢ Rt →
      Block.Preceq Rt B) :
    ∀ H : Block V, Restated.Vocabulary.Proofs.HealingSurface.actionHeadWith M (M.gradeContract n.cache)
        S.E S.hc (M.toHealing n.st.core) ⇢ H →
    Block.Preceq B H := by
  classical
  intro H hH
  obtain ⟨res, hres, hHres⟩ := hH
  have hmemA := (p64b% mem_stateBeforeTime_along₆₄b) hf.sorted hf.onePath
    (Restated.Vocabulary.Execution.Setup.a M S r)
  -- the action read's core store against the store of the path's world
  have hT : n.st.core.T =
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).st.core.T :=
    Restated.Vocabulary.Protocol.actionStoreAt_T facts S rho v r _ hmemA n hn
  have hpool : n.st.core.pool q =
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).st.core.pool q :=
    Restated.Vocabulary.Protocol.actionStoreAt_pool facts S rho v r q _ hmemA n hn
  have hslot : n.st.core.s = q :=
    Restated.Vocabulary.Protocol.actionStoreAt_slot_of_action_eq_cutoff facts S rho v r q ha n
      ⟨_, hmemA, hn⟩
  have hfilt := Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt_filteredTree_eq_storeBeforeTime
    facts S rho v r _ hmemA n hn
  have hfg := Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt_fgRoot_eq_storeBeforeTime
    facts S rho v r _ hmemA n hn
  have hsS : (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.s = q := by
    rw [facts.sto.toHealing_gs_s, hslot]
  have hTS : (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.T = n.st.core.T :=
    facts.sto.toHealing_gs_T n.st.core
  have hvcut : v ∈ Hs (M.support_cutoff S.E q) := by rw [← ha]; exact hv
  have hvoteConf : M.vote_time S.E q ≤ M.confirmation_time S.E q :=
    facts.sch.Protocol_vote_time_le_confirmation_time S.E q
  have hsuppConf : M.support_cutoff S.E q ≤ M.confirmation_time S.E q :=
    facts.sch.Protocol_support_cutoff_le_confirmation_time S.E q
  -- the pool the head is computed over, and its resolved part
  set raw : Finset (GoldfishVote V) :=
    M.store_pool (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).st.core q
    with hrawdef
  have hrawEq : M.gs_pool (M.toHealing n.st.core).toFG.toSG.toGoldfishStore q = raw := by
    rw [facts.sto.toHealing_gs_pool]
    exact hpool
  have hresT : ∀ u, M.resolved n.st.core.T u ⇢ res u := by
    intro u
    have h := hres u
    unfold Record.Model.HS.T at h
    rw [hTS] at h
    exact h
  have hHq : M.get_head_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core) raw
      (raw.filter (fun u => res u = true)) q ⇢ H := by
    have h : M.get_head_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
        (M.gs_pool (M.toHealing n.st.core).toFG.toSG.toGoldfishStore
          (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.s)
        ((M.gs_pool (M.toHealing n.st.core).toFG.toSG.toGoldfishStore
          (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.s).filter (fun u => res u = true))
        (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.s ⇢ H := hHres
    rw [hsS, hrawEq] at h
    exact h
  -- `B` is held, and found by its root
  have hBT : B ∈ n.st.core.T := by
    have h := facts.fc.get_filtered_block_tree_subset _ hactive
    rw [hTS] at h
    exact h
  have hBTw : B ∈ (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).st.core.T := by
    rw [← hT]; exact hBT
  have hfind : Block.find? n.st.core.T B.root = some B := by
    apply Proofs.Optimistic.find?_eq_some_of_unique hBT
    intro Y hY hroot
    have hYw : Y ∈ (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).st.core.T := by
      rw [← hT]; exact hY
    obtain ⟨Yn, hYnErase, hYrun⟩ :=
      Restated.runBlock_of_mem_core_T_stateBeforeTimeOn facts S Hs Xb hf (hHsXb _ hv)
        (Restated.Vocabulary.Execution.Setup.a M S r) hYw
    have hrootN : Yn.root = Bn.root := by
      rw [← Proofs.NamedWire.erase_root Yn, ← Proofs.NamedWire.erase_root Bn, hYnErase, hBn]
      exact hroot
    have hYB := hf.rootCollisionFree.root_injective Yn Bn hYrun hBrun Yn Bn
      (Or.inl (Proofs.NamedAncestry.named_self Yn))
      (Or.inr (Proofs.NamedAncestry.named_self Bn)) hrootN
    rw [← hYnErase, hYB, hBn]
  -- the cone support in the pool
  have hss : raw.filter (fun u => res u = true) ⊆ raw := Finset.filter_subset _ _
  have hne : ∀ x ∈ S.E.committee q, x ∈ Hs (M.confirmation_time S.E q) →
      M.equivocates raw x = false := by
    intro x _ hx
    exact Restated.pool_no_honest_equivocationOn facts S Hs Xb hf hHs v
      (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r))
      (T := (Restated.Vocabulary.Execution.Setup.a M S r))
      (fun j e hj he => ((p51% time_lt_of_lt_strict₅₁) hf.sorted he hj).le) q
      (hHs _ _ (by rw [ha]; exact hsuppConf) hx)
  have hvote : ∀ x ∈ S.E.committee q, x ∈ Hs (M.confirmation_time S.E q) →
      ∃ X : Block V, Block.Preceq B X ∧ X.slot ≤ q ∧
        (⟨x, q, X.root⟩ : GoldfishVote V) ∈ raw.filter (fun u => res u = true) ∧
        Block.find? n.st.core.T X.root = some X := by
    intro x hxCommittee hxHonest
    have hemit := hvotes x (hHs _ _ hvoteConf hxHonest) hxCommittee
    have hcut := Restated.gfVote_in_cutoff_view_after_gstOn facts S Hs Xb hf hHs
      (hHs _ _ hsuppConf hxHonest) hq hpost hemit rfl hvcut
      (Restated.Vocabulary.Execution.Setup.a M S r) (Restated.Vocabulary.Execution.Setup.a M S r)
      (by rw [ha]) (by rw [ha]) hhor
    have hpoolx : (⟨x, q, B.root⟩ : GoldfishVote V) ∈ raw :=
      ((mem_beforeCutoff_iff _ _ _ _).mp hcut).1
    refine ⟨B, Proofs.ModelProperties.Preceq_self B, hBslot,
      Finset.mem_filter.mpr ⟨hpoolx, ?_⟩, hfind⟩
    exact (facts.sto.resolved_eq_true_iff n.st.core.T _ _ (hresT _)).2 ⟨B, hfind, hBslot⟩
  have hcone := Restated.Vocabulary.Proofs.Optimistic.coneSupport_of_named_votes facts (E := S.E)
    (T := n.st.core.T) (votes := raw) (support := raw.filter (fun u => res u = true)) (late := raw)
    (s := q) (Hon := Hs (M.confirmation_time S.E q)) (tgt := fun X => Block.Preceq B X)
    (hcom q) (subset_refl _) hss hne hvote
  have hvalid : Protocol.VoteSetValid S.E q raw :=
    Restated.voteSetValid_pool_stateBeforeOn facts S Hs Xb hf v
      (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) q
  have hmaj := (p60% supporterMajority_of_cone₆₀s) facts S.E hcone hvalid
  -- the round of the action store's slot
  have hround : M.round_of S.hc q = r := by
    have h := Restated.Vocabulary.Proofs.HealingLemmas.ActionRound.round_of_slotOf_a facts S r
    rw [ha, facts.sch.slotOf_support_cutoff] at h
    exact h
  -- one outcome of the SG root: the anchor of the fork choice
  obtain ⟨R0, hR0⟩ := facts.fc.get_sg_root_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.s)
  have hfork := (facts.gr.get_head_with_eq_fork_choice (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) raw (raw.filter (fun u => res u = true)) q R0 hR0 H).1 hHq
  rw [hTS] at hfork
  have hR0r : M.get_sg_root_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core) r ⇢ R0 := by
    have h := hR0
    rw [hsS, hround] at h
    exact h
  have hR0B : Block.Preceq R0 B := hsg R0 hR0r
  have hcompat : Block.compatible R0 B = true :=
    compatible_of_preceq_common_Preceq hR0B (Proofs.ModelProperties.Preceq_self B)
  -- the path from the SG root to `B` is in the filtered tree
  have hpath : Block.Preceq R0 B → ∀ C : Block V, Block.Preceq R0 C → C ≠ R0 → Block.Preceq C B →
      C ∈ M.get_filtered_block_tree (M.toHealing n.st.core).toFG := by
    intro _ C hAC _ hCB
    have hpc := Restated.Vocabulary.Proofs.NamedStoreBridge.parentClosed_stateBeforeTime facts S rho
      (Restated.Vocabulary.Execution.Setup.a M S r) v _ hmemA
    unfold Restated.Vocabulary.Internal.ParentClosed Record.Model.GS.parent_closed at hpc
    rw [facts.sto.toHealing_gs_T] at hpc
    have hCTw : C ∈ (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).st.core.T :=
      Proofs.Records.mem_of_preceq hpc.2 C B hBTw (preceq_eq_true_iff_Preceq.mpr hCB)
    have hFJ := Restated.Vocabulary.Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
      facts S rho (Restated.Vocabulary.Execution.Setup.a M S r) v _ hmemA
    rw [hfilt]
    refine facts.fc.mem_filtered_of_preceq
      (st := (M.toHealing
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).st.core).toFG)
      ?_ (by rw [← hfilt]; exact hactive) ?_ (preceq_eq_true_iff_Preceq.mpr hCB) ?_
    · rw [preceq_eq_true_iff_Preceq, facts.sto.Sts_toHealing_F, facts.sto.Sts_toHealing_J]
      exact hFJ
    · rw [facts.sto.toHealing_gs_T]
      exact hCTw
    · rw [← hfg]
      exact preceq_eq_true_iff_Preceq.mpr (preceq_trans_Preceq
        (facts.fc.fg_root_Preceq_get_sg_root_with_gradeContract n.cache S.E S.hc
          (M.toHealing n.st.core) _ R0 hR0) hAC)
  obtain ⟨sup, hsup⟩ := facts.fc.raw_supporters_nonempty n.st.core.T raw
    (raw.filter (fun u => res u = true)) q B
  exact facts.fc.goldfish_fork_choice_captures_supporter_majority S.E _ _ n.st.core.T
    (M.get_filtered_block_tree (M.toHealing n.st.core).toFG) _ raw
    (raw.filter (fun u => res u = true)) q hss sup hsup (hmaj sup hsup) hcompat hpath H hfork

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

/-- Under `hf` along the path `W`: if the tree of `v`'s store in `W` strictly before `t` holds `B`,
    `A ⪯ B` and `A ≠ B`, then `A`'s slot is less than `B`'s. -/
theorem slot_lt_of_preceq_ne_of_mem_storeBeforeTimeOn_f1b2 (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} {t : Int} {A B : Block V}
    (hB : B ∈ (W (strictEventIndex rho t) v).st.core.T)
    (hAB : Block.Preceq A B) (hne : A ≠ B) :
    A.slot < B.slot := by
  by_cases hg : B = Block.genesis
  · subst hg
    exact absurd (eq_genesis_of_Preceq_genesis hAB) hne
  · have hpar := parent?_eq_some_parent_of_ne_genesis hg
    have hAp : Block.Preceq A B.parent := preceq_eq_true_iff_Preceq.mp
      (Proofs.Optimistic.preceq_parent_of_ne hpar (preceq_eq_true_iff_Preceq.mpr hAB) hne)
    have hpmem : B.parent ∈ (W (strictEventIndex rho t) v).st.core.T :=
      Restated.ancestor_mem_storeBeforeTimeOn facts S Hs Xb hf (t := t) hB
        (preceq_eq_true_iff_Preceq.mp (Protocol.preceq_of_parent? hpar))
    exact lt_of_le_of_lt
      (Restated.preceq_slot_le_of_mem_storeBeforeTimeOn facts S Hs Xb hf _ hpmem A hAp)
      (Restated.parent_slot_lt_of_mem_storeBeforeTimeOn facts S Hs Xb hf hB hg)

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

/-- Under `hf` along the path `W`, if `B` has slot `o_c + 1`, then for every node state `n` of `v`'s
    round-`c` action read on `W` and every block `H` the action head computed on `n` can return,
    `B ⪯ H` implies `H = B`. -/
theorem actionHeadAt_eq_of_plusOne_preceqOn_f1b2 (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {c : Round} {v : V} {B : Block V}
    (hBslot : B.slot = (M.opening_slot S.hc c) + 1) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v) c,
    ∀ H : Block V, Restated.Vocabulary.Proofs.HealingSurface.actionHeadWith M (M.gradeContract n.cache)
        S.E S.hc (M.toHealing n.st.core) ⇢ H →
    Block.Preceq B H → H = B := by
  intro n hn H hH hpre
  have hmem : H ∈ (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v).st.core.T :=
    Restated.Vocabulary.Proofs.HealingSurface.actionHeadWith_mem_storeBeforeTime facts S v c _
      ((p64b% mem_stateBeforeTime_along₆₄b) hf.sorted hf.onePath _) n hn H hH
  have hactionLe : (Restated.Vocabulary.Execution.Setup.a M S c) ≤ M.proposal_time S.E ((M.opening_slot S.hc c) + 2) :=
    (Restated.interiorInstants_l85d facts S c).1
  have hupper : H.slot < (M.opening_slot S.hc c) + 2 :=
    Restated.block_slot_lt_of_mem_beforeTime_of_le_proposalOn facts S Hs Xb hf (Nat.succ_pos _) hactionLe hmem
  by_contra hne
  have hlt := Restated.slot_lt_of_preceq_ne_of_mem_storeBeforeTimeOn_f1b2 facts S Hs Xb hf hmem hpre
    (fun h => hne h.symm)
  rw [hBslot] at hlt
  exact absurd hupper (Nat.not_lt.mpr hlt)

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

/-- For a round `c` with `rD + 2 ≤ c` and `S.a c ≤ x[n].time`, whose opening proposer and the
    proposer of the slot after the opening are not held at their slots' confirmation instants: along
    the path the execution follows, `Restated.HonestActionHeadsAtStrongWindow` holds for every block
    the proposer of the slot after `c`'s opening can propose and every choice of one round-`c`
    action head per validator not held at `S.a c`. -/
theorem honestActionHeadsAtStrongWindow_f1b2 (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v₀ : V) (n : Nat)
    {tGAT tL : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tL → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tL →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hn : (x[n].time : Int) ≤ tL)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tL gap)
    {c : Round} (hc : Restated.deadlineRoundW M S tGAT gap + 2 ≤ c)
    (hAcHor : (Restated.Vocabulary.Execution.Setup.a M S c) ≤ (x[n].time : Int))
    (hopening : S.E.proposer ((M.opening_slot S.hc c)) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c))))
    (hopening₁ : S.E.proposer ((M.opening_slot S.hc c) + 1) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c) + 1))) :
    let R : Record.Run V :=
      { Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) }
    let W := Restated.runAllPath M S Sched x v₀ n
    let wp₁ := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c + 1)))
      (S.E.proposer (M.opening_slot S.hc c + 1))
    ∀ cp₁ : M.Cache,
      M.onPhaseTick S.E S.hc wp₁.st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc c + 1)) wp₁.cache ⇢ cp₁ →
      let pn₁ := M.mkNode
        (M.ns_setClock S.E wp₁.st (M.proposal_time S.E (M.opening_slot S.hc c + 1))) wp₁.record cp₁
    ∀ p : Option (NamedBlock V),
      M.proposal_with (M.gradeContract cp₁) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc c + 1))) pn₁.st ⇢ p →
    ∀ head : V → Block V,
      (∀ v ∈ notHeldAt Sched (Restated.Vocabulary.Execution.Setup.a M S c),
        ∃ nv ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
          (W (strictEventIndex R (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c)) v) c,
        Restated.Vocabulary.Proofs.HealingSurface.actionHeadWith M (M.gradeContract nv.cache)
          S.E S.hc (M.toHealing nv.st.core) ⇢ head v) →
    Restated.HonestActionHeadsAtStrongWindow M S Sched x v₀ n c p head := by
  intro R W wp₁ cp₁ hcp₁ pn₁ p hp head hhead
  classical
  intro P₁ hpP₁ v hv
  subst hpP₁
  obtain ⟨nv, hnv, hheadv⟩ := hhead v hv
  obtain ⟨q, rfl⟩ : ∃ q : Round, c = q + 1 :=
    Nat.exists_eq_succ_of_ne_zero (by
      intro h0; rw [h0] at hc; exact absurd hc (Nat.not_succ_le_zero _ ∘ fun h =>
        (Nat.le_add_left 1 _).trans ((Nat.le_succ _).trans h)))
  set o := (M.opening_slot S.hc (q + 1)) with ho
  -- the family at `R_n`
  have hf := Restated.admissibleFieldsOn_runAll_notHeld facts S Sched x v₀ n hsync hmono hawake
    hgst hcv hvalid hawm hthird hn
  have hHs : ∀ t t' : Int, t ≤ t' → notHeldAt Sched t' ⊆ notHeldAt Sched t :=
    fun _ _ h => notHeldAt_anti hmono h
  have hHsXb : ∀ t : Int, notHeldAt Sched t ⊆ (Finset.univ : Finset V) :=
    fun _ => Finset.subset_univ _
  have hcomOn := Restated.honestCommitteesOn_notHeld facts S Sched hcom
  have hbelow := Restated.belowOneThirdOn_runAll_notHeld facts S Sched x v₀ n hthird hn
  have hrecOn := Restated.multiProposerRecurrenceOn_runAll_notHeld facts S Sched x v₀ n hrec hn
  obtain ⟨hpost, -, hloOpen, ht₀⟩ := Restated.roundAt_bounds_l71 facts S hgst
  have hloPost := Restated.roundAt_lo_le_rGST_l71 facts S tGAT
  -- the grade-2 awake test at every action tick whose round's window start is after `tGAT`
  have hA : ∀ k : Round, tGAT + 1 ≤ M.early S.E S.hc k .g2 - S.E.Δ →
      ∀ u ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat,
      R.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) →
      M.awake_for_grade2 (Setup.alwaysAwake S) u (W j u) k :=
    fun k hk u _ j hj => Restated.awake_g2_action_runAllPath facts S Sched x v₀ n hmono hawake hn
      k hk u j hj
  have hDq : Restated.deadlineRoundW M S tGAT gap ≤ q :=
    Nat.le_of_succ_le_succ ((Nat.le_succ _).trans hc)
  have hD : Restated.fgSafetyProgressDeadline (Setup.alwaysAwake S) R
      (Restated.roundAt M S tGAT + S.hc.η_SG) gap (Setup.alwaysAwake S).extraRounds =
      Restated.deadlineRoundW M S tGAT gap :=
    Restated.fgSafetyProgressDeadline_eq_deadlineRoundW facts S R tGAT gap
  obtain ⟨hopos, hgatO⟩ := Restated.openingBounds_afterDeadline_l85d facts S hc
  -- the instants
  have ha : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (q + 1)) =
      M.support_cutoff S.E (o + 1) := by
    rw [← Restated.Vocabulary.Proofs.HealingSurface.opening_confirmation_time_eq_action facts
      (Setup.alwaysAwake S) (q + 1)]
    exact facts.sch.confirmation_time_eq_support_cutoff_succ S.E o
  have hΔ := S.E.Δ_pos
  obtain ⟨hv1, hs1, -, -, -, -⟩ := facts.sch.slot_instants_l55 S.E (o + 1)
  have hvs : M.vote_time S.E (o + 1) ≤ M.support_cutoff S.E (o + 1) := by linarith
  have hvoteA : M.vote_time S.E (o + 1) ≤
      (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (q + 1)) := by
    rw [ha]; exact hvs
  have hAcHor' : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (q + 1)) ≤
      R.horizon := hAcHor
  have hvote1Hor : M.vote_time S.E (o + 1) ≤ R.horizon := hvoteA.trans hAcHor'
  have hlo1 : tGAT + 1 ≤ M.vote_time S.E (o + 1) :=
    hgatO.trans ((facts.sch.proposal_time_mono S.E (Nat.le_succ o)).trans
      (facts.sch.proposal_time_lt_vote_time S.E (o + 1)).le)
  have hprop1Hor : M.proposal_time S.E (o + 1) ≤ R.horizon :=
    (facts.sch.proposal_time_lt_vote_time S.E (o + 1)).le.trans hvote1Hor
  have hgat1 : tGAT + 1 ≤ M.proposal_time S.E (o + 1) :=
    hgatO.trans (facts.sch.proposal_time_mono S.E (Nat.le_succ o))
  have hv' : v ∈ notHeldAt Sched
      (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (q + 1)) := hv
  have hvVote : v ∈ notHeldAt Sched (M.vote_time S.E (o + 1)) := hHs _ _ hvoteA hv'
  have hp1Vote : S.E.proposer (o + 1) ∈ notHeldAt Sched (M.vote_time S.E (o + 1)) :=
    hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E (o + 1)) hopening₁
  have hconfA : M.confirmation_time S.E o = (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) :=
    Restated.Vocabulary.Proofs.HealingSurface.opening_confirmation_time_eq_action facts S (q + 1)
  have hp0 : S.E.proposer o ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M S (q + 1))) := by
    rw [← hconfA]; exact hopening
  -- one proposal `P` of the opening slot on the path: the proposal duty has an outcome, and
  -- every outcome is a block
  obtain ⟨cp, hcp⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
    (W (strictEventIndex R (M.proposal_time S.E o)) (S.E.proposer o)).st.core.toHealing
    (M.proposal_time S.E o)
    (W (strictEventIndex R (M.proposal_time S.E o)) (S.E.proposer o)).cache
  obtain ⟨p0, hp0P⟩ := facts.dt.proposal_with_nonempty (M.gradeContract cp)
    Protocol.ProposalRowSource.poolAndCarried S.E S.hc
    ((Setup.alwaysAwake S).node (S.E.proposer o))
    (M.ns_setClock S.E (W (strictEventIndex R (M.proposal_time S.E o)) (S.E.proposer o)).st
      (M.proposal_time S.E o))
  obtain ⟨P, rfl⟩ := Restated.Vocabulary.Proofs.HealingSurface.proposedBlockAt_isSome facts
    (Setup.alwaysAwake S) R o p0
    ((p56% proposedBlockAt_mem₅₆h) facts (Setup.alwaysAwake S) hf o cp hcp hp0P)
  have hP : M.proposal_with (M.gradeContract cp) .poolAndCarried S.E S.hc
      ((Setup.alwaysAwake S).node (S.E.proposer o))
      (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex R (M.proposal_time S.E o)) (S.E.proposer o)).st
        (M.proposal_time S.E o))
        (W (strictEventIndex R (M.proposal_time S.E o)) (S.E.proposer o)).record cp).st ⇢ some P := by
    rw [facts.nd.mkNode_st, facts.dt.proposal_with_store_with_cache]
    exact hp0P
  -- the SG block of round `q + 1` is `P`: one such block of `P`'s own proposer
  have hsg := Restated.sgBlock_eq_openingProposal_runAll_notHeld facts S Sched x v₀ n hsync hmono
    hawake hgst hcv hvalid hawm hthird hn hcom hrec hc hAcHor hopening cp hcp hP
  obtain ⟨nv0, hnv0, g0, hg0, G0, hG0⟩ := (p56% exists_actionSG₅₆) facts (Setup.alwaysAwake S)
    (W (strictEventIndex R (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (q + 1)))
      (S.E.proposer o)) (q + 1)
  have hG0P : G0 = P.erase := hsg _ hp0 nv0 hnv0 g0 hg0 G0 hG0
  -- the window-start bound of round `q + 1` (from `tGAT + 1 ≤ S.a rGST`, `rGST < q + 1`)
  have hkq : tGAT + 1 ≤ M.early S.E S.hc (q + 1) .g2 - S.E.Δ :=
    Restated.lo_le_early_g2_sub_delta_of_action_lt facts S hloPost
      (Nat.lt_succ_of_le ((Restated.rGST_le_deadlineRoundW_l85c facts S tGAT gap).trans hDq))
  have hfirst := fun (w : V) (hw : w ∈ notHeldAt Sched (M.vote_time S.E (o + 1))) =>
    Restated.actionSGBlock_preceq_firstInteriorHead_after_GST_namedOn facts (Setup.alwaysAwake S)
      (notHeldAt Sched) Finset.univ hf hHs hHsXb hcomOn hbelow hrecOn
      (Setup.timeoutDelayBound _) hpost (by rw [hD]; exact hDq) hAcHor hp0
      (fun j hj => Restated.awake_g2_action_runAllPath facts S Sched x v₀ n hmono hawake hn
        (q + 1) hkq _ j hj) hw hloPost
      hloOpen ht₀ hA
  -- the heads at `o + 1` are `P₁`
  have hstart : (M.opening_slot S.hc) (Restated.fgSafetyProgressDeadline
      (Setup.alwaysAwake S) R (Restated.roundAt M S tGAT + S.hc.η_SG) gap
      (Setup.alwaysAwake S).extraRounds + 2) ≤ o + 1 := by
    rw [hD]; exact (facts.gr.opening_slot_mono S hc).trans (Nat.le_succ _)
  have hP₁clock : M.proposal_with (M.gradeContract cp₁)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc
      ((Setup.alwaysAwake S).node (S.E.proposer (o + 1)))
      (M.ns_setClock S.E wp₁.st (M.proposal_time S.E (o + 1))) ⇢ some P₁ := by
    have h := hp
    rw [facts.nd.mkNode_st, facts.dt.proposal_with_store_with_cache] at h
    exact h
  have hstores := Restated.slotProposal_voteStoreExtends_afterDeadlineOn_i1b facts
    (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ hf hHs hHsXb hcomOn hbelow hrecOn
    (Setup.timeoutDelayBound _) hpost hstart hvote1Hor hopening₁ cp₁ hcp₁ hp hloPost hloOpen ht₀
    (fun k u hk _ j hj => Restated.awake_g2_action_runAllPath facts S Sched x v₀ n hmono hawake hn
      k hk u j hj)
  obtain ⟨I, hI⟩ := facts.dt.with_proposal_input_nonempty (M.gradeContract cp₁) S.E S.hc
    ((Setup.alwaysAwake S).node (S.E.proposer (o + 1))) (M.toHealing pn₁.st.core)
  -- `P ⪯ P₁`, at the proposer of `o + 1`
  obtain ⟨H1, c1, hc1, Tr1, hTr1, L1, hL1, L1', hL1', hH1⟩ :=
    (p86g% exists_headOutcome₈₆g) facts (Setup.alwaysAwake S)
      (W (strictEventIndex R (M.vote_time S.E (o + 1))) (S.E.proposer (o + 1)))
      (M.vote_time S.E (o + 1))
  have hH1P : H1 = P₁.erase :=
    (hstores _ hp1Vote c1 hc1 Tr1 hTr1 I hI).head Tr1 hTr1 L1 hL1 L1' hL1' H1 hH1
  have hPP₁ : Block.Preceq P.erase P₁.erase := by
    have h := hfirst _ hp1Vote c1 hc1 Tr1 hTr1 L1 hL1 L1' hL1' H1 hH1 nv0 hnv0 g0 hg0 G0 hG0
    rw [hG0P, hH1P] at h
    exact h
  -- the grade-1 awake test at the duty ticks of slot `o + 1`: the bundle's clause `awake_g1`,
  -- with the window-start bound of round `q + 1` from `hkq`
  have hround1 : M.round_of S.hc (o + 1) = q + 1 := facts.gr.HealingLemmas_round_of_opening_succ S.hc _
  have hwin1 : tGAT + 1 ≤ M.early S.E S.hc (M.round_of S.hc (o + 1)) .g1 - S.E.Δ := by
    rw [hround1]
    have h2 := facts.gr.q10_early_g2_le_early_g1 S (q + 1)
    linarith
  -- every committee member of `o + 1` not held at its vote instant votes `P₁`
  have hvotes : ∀ w ∈ notHeldAt Sched (M.vote_time S.E (o + 1)),
      w ∈ S.E.committee (o + 1) →
      Restated.Vocabulary.Execution.NamedRun.emits M (Setup.alwaysAwake S) R W w
        (.gfVote ⟨w, o + 1, P₁.erase.root⟩) (M.vote_time S.E (o + 1)) := by
    intro w hw hcomm
    obtain ⟨H, cw, hcw, Tr, hTr, L, hL, L', hL', hH⟩ :=
      (p86g% exists_headOutcome₈₆g) facts (Setup.alwaysAwake S)
        (W (strictEventIndex R (M.vote_time S.E (o + 1))) w) (M.vote_time S.E (o + 1))
    obtain ⟨C, hCerase, -, hCemit⟩ := Restated.named_voter_head_emitsOn facts
      (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ hf hHsXb hw (Nat.succ_pos o) hcomm
      hvote1Hor hlo1 cw hcw (fun j hj => hf.awake_g1 _ _ j _ (Or.inr rfl) hj hw hwin1)
      Tr hTr L hL L' hL' H hH
    have hHP : H = P₁.erase :=
      (hstores w hw cw hcw Tr hTr I hI).head Tr hTr L hL L' hL' H hH
    rw [hCerase, hHP] at hCemit
    exact hCemit
  -- `P₁` is a run block of slot `o + 1`
  have hP₁run := Restated.proposedBlock_runBlockOn facts (Setup.alwaysAwake S) (notHeldAt Sched)
    Finset.univ hf hHs hHsXb (Nat.succ_pos o) hopening₁ hprop1Hor hgat1
    (fun j hj => hf.tick_outcome j _ _ hj)
    (fun j hj => hf.awake_g1 _ _ j _ (Or.inl rfl) hj
      (hHs _ _ (facts.sch.proposal_time_le_confirmation_time S.E _) hopening₁) hwin1) cp₁ hcp₁
    hP₁clock
  have hP₁slot : P₁.erase.slot = o + 1 := by
    rw [Proofs.NamedWire.erase_slot]
    exact Restated.Vocabulary.Proofs.Optimistic.proposedBlockAt_slot facts (Setup.alwaysAwake S) R
      (o + 1) (some P₁) ((p56% proposedBlockAt_mem₅₆h) facts (Setup.alwaysAwake S) hf (o + 1) cp₁
        hcp₁ hP₁clock) rfl
  -- the SG root and the FG root of `v`'s action store
  have hsgRoot := Restated.actionSGRoot_preceq_openingProposal_f1b2 facts S Sched x v₀ n hsync
    hmono hawake hgst hcv hvalid hawm hthird hn hcom hrec hc hAcHor' hopening cp hcp hP v hv
    nv hnv
  have hsgP₁ : ∀ Rt : Block V,
      M.get_sg_root_with (M.gradeContract nv.cache) S.E S.hc (M.toHealing nv.st.core) (q + 1) ⇢ Rt →
      Block.Preceq Rt P₁.erase :=
    fun Rt hRt => preceq_trans_Preceq (hsgRoot Rt hRt) hPP₁
  have hmemA := (p64b% mem_stateBeforeTime_along₆₄b) hf.sorted hf.onePath
    (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (q + 1))
  have hfilt := Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt_filteredTree_eq_storeBeforeTime
    facts (Setup.alwaysAwake S) R v (q + 1) _ hmemA nv hnv
  have hfg := Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt_fgRoot_eq_storeBeforeTime
    facts (Setup.alwaysAwake S) R v (q + 1) _ hmemA nv hnv
  obtain ⟨R0, hR0⟩ := facts.fc.get_sg_root_with_nonempty (M.gradeContract nv.cache) S.E S.hc
    (M.toHealing nv.st.core) (q + 1)
  have hrootP₁ : Block.Preceq
      (M.get_fg_root (M.toHealing
        (W (strictEventIndex R (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (q + 1)))
          v).st.core).toFG)
      P₁.erase := by
    rw [← hfg]
    exact preceq_trans_Preceq
      (facts.fc.fg_root_Preceq_get_sg_root_with_gradeContract nv.cache S.E S.hc
        (M.toHealing nv.st.core) _ R0 hR0) (hsgP₁ R0 hR0)
  -- `P₁` is in `v`'s filtered tree at the action read
  have hDread : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S))
      (Restated.fgSafetyProgressDeadline (Setup.alwaysAwake S) R
      (Restated.roundAt M S tGAT + S.hc.η_SG) gap (Setup.alwaysAwake S).extraRounds) ≤
      (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (q + 1)) := by
    rw [hD]
    exact (Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone
      (hDq.trans (Nat.le_succ q))
  have hslotD : (M.opening_slot S.hc) (Restated.fgSafetyProgressDeadline
      (Setup.alwaysAwake S) R (Restated.roundAt M S tGAT + S.hc.η_SG) gap
      (Setup.alwaysAwake S).extraRounds) + 1 ≤ o + 1 := by
    rw [hD]
    exact Nat.succ_le_succ (facts.gr.opening_slot_mono S (hDq.trans (Nat.le_succ q)))
  have hnext : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (q + 1)) ≤
      M.confirmation_time S.E (o + 1) := by
    rw [ha]; exact facts.sch.Protocol_support_cutoff_le_confirmation_time S.E (o + 1)
  have hshor : M.vote_time S.E (o + 1) + S.E.Δ ≤ R.horizon := by
    have hsup : M.vote_time S.E (o + 1) + S.E.Δ = M.support_cutoff S.E (o + 1) := by linarith
    rw [hsup, ← ha]; exact hAcHor'
  obtain ⟨T, hTrun, hTband, hTheads⟩ :=
    Restated.exists_namedCommonPreviousHeadAncestor_in_frontierBand_through_confirmation_after_GSTOn
      facts (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ hf hHs hHsXb hcomOn hbelow
      hrecOn (Setup.timeoutDelayBound _) hpost hDread hAcHor' hslotD hnext hshor hv' hloPost
      hloOpen ht₀ hA
  obtain ⟨Hv, cv, hcv', Trv, hTrv, Lv, hLv, Lv', hLv', hHv⟩ :=
    (p86g% exists_headOutcome₈₆g) facts (Setup.alwaysAwake S)
      (W (strictEventIndex R (M.vote_time S.E (o + 1))) v) (M.vote_time S.E (o + 1))
  have hHvP : Hv = P₁.erase :=
    (hstores v hvVote cv hcv' Trv hTrv I hI).head Trv hTrv Lv hLv Lv' hLv' Hv hHv
  have hTP₁ : Block.Preceq T.erase P₁.erase := by
    have h := hTheads v hvVote cv hcv' Trv hTrv Lv hLv Lv' hLv' Hv hHv
    rw [hHvP] at h
    exact h
  have hheadVote := Restated.voteDutyHead_mem_voteDutyStoreOn facts (Setup.alwaysAwake S)
    (notHeldAt Sched) Finset.univ hf v (o + 1) cv hcv' Trv hTrv Lv hLv Lv' hLv' Hv hHv
  have hHvoteT : Hv ∈ (W (strictEventIndex R (M.vote_time S.E (o + 1))) v).st.core.T := by
    have h := hheadVote
    rw [(p60% voteStore_eq₆₀s) facts, facts.hd.Sts_setClock_core_T] at h
    exact h
  have hP₁mem : P₁.erase ∈
      (W (strictEventIndex R (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (q + 1)))
        v).st.core.T := by
    rw [← hHvP]
    exact Restated.seedStore_T_subsetOn facts (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ hf
      v hvoteA hHvoteT
  have hpc := Restated.Vocabulary.Proofs.NamedStoreBridge.parentClosed_stateBeforeTime facts
    (Setup.alwaysAwake S) R (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (q + 1)) v
    _ hmemA
  have hFJ := Restated.Vocabulary.Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
    facts (Setup.alwaysAwake S) R
    (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (q + 1)) v _ hmemA
  have hband :
      (W (strictEventIndex R (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (q + 1)))
        v).st.core.h_max - 1 ≤
      ((W (strictEventIndex R (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (q + 1)))
        v).st.core.σ P₁.erase).h := by
    have hbody := Restated.namedBody_of_mem_storeBeforeTime_l86f facts (Setup.alwaysAwake S)
      (notHeldAt Sched) Finset.univ hf (Finset.mem_univ v) hP₁mem hP₁run
    have hview := Restated.Vocabulary.Proofs.NamedStoreBridge.derivedView_stateBeforeTime facts
      (Setup.alwaysAwake S) R (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (q + 1))
      v _ hmemA P₁ hbody
    rw [hview]
    have hTP₁n := Restated.namedPreceq_of_runBlock_erase_preceqOn facts (notHeldAt Sched)
      Finset.univ hf hTrun hP₁run hTP₁
    exact hTband.trans (facts.cs.derive_height_mono S.E S.cfg hTP₁n)
  have hactive : P₁.erase ∈ M.get_filtered_block_tree (M.toHealing nv.st.core).toFG := by
    rw [hfilt]
    exact Restated.Vocabulary.Proofs.HealingSurface.canonicalConeSegment_mem_filtered_of_root_preceq
      facts hpc hFJ hrootP₁ hP₁mem hband
      (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _))
      (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _))
  -- `P₁` is an ancestor of the action head, and the slot gives equality
  have hpre := Restated.preceq_actionHeadAt_of_votesOn_f1b2 facts (Setup.alwaysAwake S)
    (notHeldAt Sched) Finset.univ hf hHs hHsXb hcomOn (Nat.succ_pos o) hlo1
    (le_trans (le_of_eq ha.symm) hAcHor') ha hv' rfl hP₁run (le_of_eq hP₁slot) hvotes nv hnv
    hactive hsgP₁
  exact Restated.actionHeadAt_eq_of_plusOne_preceqOn_f1b2 facts (Setup.alwaysAwake S)
    (notHeldAt Sched) Finset.univ hf hP₁slot nv hnv (head v) hheadv (hpre _ hheadv)

end

end DecoupledConsensusModel.Sts.Restated
