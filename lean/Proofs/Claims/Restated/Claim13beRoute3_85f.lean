import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bInvariantActiveSinceW
import Proofs.Claims.Restated.Claim13beRoute3_44
import Proofs.Claims.Restated.Claim13beRoute3_45
import Proofs.Claims.Restated.Claim13beRoute3_46
import Proofs.Claims.Restated.Claim13beRoute3_58
import Proofs.Claims.Restated.Claim13beRoute3_72
import Proofs.Claims.Restated.Claim13beRoute3_76
import Proofs.Claims.Restated.Claim13beRoute3_77
import Proofs.Claims.Restated.Claim13beRoute3_82
import Proofs.Claims.Restated.Claim13beRoute3_83
import Proofs.Claims.Restated.Claim13beRoute3_85
import Proofs.Claims.Restated.Claim13beRoute3_85b
import Proofs.Claims.Restated.Claim13beRoute3_85c
import Proofs.Claims.Restated.Claim13beRoute3_85d
import Proofs.Claims.Restated.Claim13beRoute3_85e
import Proofs.Claims.Restated.Claim13beRoute3_86e
import Proofs.Claims.Restated.Claim13beRoute3_86g
import Proofs.Claims.Restated.RunAll
import Proofs.Claims.Restated.Vocabulary_Execution_SeedActionRowCarriage
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_ProposalBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_W4NamedJustificationMonotone
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_TickBridges
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_Action
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActiveSinceW
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.Claim13beRoute3_72
import Model.Conditions.Claim13beRoute3_83
import Model.Conditions.RunAll
import Model.Conditions.RunVocabulary
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedHeadReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ProposalSourcesInternal
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_ChainState_W4FKChainJustification
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_85f

/-!
# A justified-height bound at the switch round

From the strong windows of the phase, some tick before the vote instant of `o_rW + 1` leaves every
honest validator with a justified height at least that of the anchor at the re-based deadline round,
so every validator honest through the switch round's tick step holds such a height. The steps are
the target and progress quorums from planned honest rows, the window's justification, and the
exclusion of a climb between two windows. Stated over a model `M : Record.Model V`, in an execution
in which every tick has an outcome.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

/-- A private theorem of the page `lean/Proofs/Claims/Restated/Claim13beRoute3_51.lean`, by name. -/
local macro "p51% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_51)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- A private theorem of the page `lean/Proofs/Claims/Restated/Claim13beRoute3_56.lean`, by name. -/
local macro "p56% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_56)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- A private theorem of the page `lean/Proofs/Claims/Restated/Claim13beRoute3_58.lean`, by name. -/
local macro "p58% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_58)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- A private theorem of the page `lean/Proofs/Claims/Restated/Claim13beRoute3_71.lean`, by name. -/
local macro "p71% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_71)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- A private theorem of the page `lean/Proofs/Claims/Restated/Claim13beRoute3_74.lean`, by name. -/
local macro "p74% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_74)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- A private theorem of the page `lean/Proofs/Claims/Restated/Claim13beRoute3_86g.lean`, by name. -/
local macro "p86g% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_86g)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog

/-- Every attestation the attestation duty of `v`'s node can return on a node state `n` names `v` as
    its signer. -/
private theorem attest_val_index₈₅f (facts : Record.Facts M) (S : Setup V) (v : V) (n : M.N) :
    ∀ D, M.duties_attest_with (M.gradeContract n.cache) S.E S.hc (S.node v) n.st n.record ⇢ D →
      D.2.2.val_index = v := by
  intro D hD
  obtain ⟨A, hA⟩ := facts.dt.round_action_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (S.node v) (M.toHealing n.st.core) n.record
  rw [facts.dt.attest_with_row (M.gradeContract n.cache) S.E S.hc (S.node v) n.st n.record D hD A hA,
    facts.dt.round_action_with_val_index _ _ _ _ _ _ A hA]
  exact S.node_val_index v

/-- On a path `W` of a run sorted by key, the proposer of slot `s` has an outcome `c` of its cache
    update at the slot's proposal instant and a named block the proposal duty can return on the read
    built from `c`. -/
private theorem exists_proposal₈₅f (facts : Record.Facts M) {S : Setup V} {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (s : Slot) :
    ∃ (c : M.Cache) (B : NamedBlock V),
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core.toHealing
        (M.proposal_time S.E s)
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).cache ⇢ c ∧
      M.proposal_with (M.gradeContract c) .poolAndCarried S.E S.hc (S.node (S.E.proposer s))
        (M.mkNode
          (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
            (M.proposal_time S.E s))
          (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record c).st ⇢ some B := by
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
    (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core.toHealing
    (M.proposal_time S.E s)
    (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).cache
  obtain ⟨o, ho⟩ := facts.dt.proposal_with_nonempty (M.gradeContract c) .poolAndCarried S.E S.hc
    (S.node (S.E.proposer s))
    (M.mkNode
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
        (M.proposal_time S.E s))
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record c).st
  obtain ⟨B, rfl⟩ := Restated.Vocabulary.Proofs.HealingSurface.proposedBlockAt_isSome facts S rho s o
    ⟨_, (p58% mkNode_mem_confirmationReadAt₅₈) hsorted hW _ _ c hc,
      by rw [facts.nd.mkNode_cache]; exact ho⟩
  exact ⟨c, B, hc, ho⟩

/-- On a path `W` of a run sorted by key, a named block the proposal duty of slot `s`'s proposer can
    return, on the read built from an outcome of its cache update at the slot's proposal instant,
    has slot `s`. -/
private theorem proposal_slot₈₅f (facts : Record.Facts M) {S : Setup V} {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (s : Slot)
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core.toHealing
      (M.proposal_time S.E s)
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).cache ⇢ c)
    {B : NamedBlock V}
    (hB : M.proposal_with (M.gradeContract c) .poolAndCarried S.E S.hc (S.node (S.E.proposer s))
      (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
          (M.proposal_time S.E s))
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record c).st ⇢ some B) :
    B.slot = s :=
  Restated.Vocabulary.Proofs.Optimistic.proposedBlockAt_slot facts S rho s (some B)
    ⟨_, (p58% mkNode_mem_confirmationReadAt₅₈) hsorted hW _ _ c hc,
      by rw [facts.nd.mkNode_cache]; exact hB⟩ rfl

/-- For rounds `q ≤ c` with `c + 1 ≤ r`, the vote instant of `o_c + 2` is positive and at most one
    instant before the vote instant of `o_r + 1`, and so is `S.a q`. -/
theorem assemblyInstants_l85f (facts : Record.Facts M) (S : Setup V) {q c r : Round} (hqc : q ≤ c) (hcr : c + 1 ≤ r) :
    0 < M.vote_time S.E ((M.opening_slot S.hc c) + 2) ∧
    M.vote_time S.E ((M.opening_slot S.hc c) + 2) ≤
      M.vote_time S.E ((M.opening_slot S.hc r) + 1) - 1 ∧
    0 < (Restated.Vocabulary.Execution.Setup.a M S q) ∧
    (Restated.Vocabulary.Execution.Setup.a M S q) ≤ M.vote_time S.E ((M.opening_slot S.hc r) + 1) - 1 := by
  have hΔ : (1 : Int) ≤ S.E.Δ := S.E.Δ_pos
  have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  have hqc' : (q : Int) ≤ (c : Int) := by exact_mod_cast hqc
  have hcr' : (c : Int) + 1 ≤ (r : Int) := by exact_mod_cast hcr
  have hq0 : (0 : Int) ≤ (q : Int) := by positivity
  have hp : ∀ x : Round, ∀ n : Nat, M.proposal_time S.E ((M.opening_slot S.hc x) + n)
      = 4 * S.E.Δ * (S.hc.R : Int) * (x : Int) + 4 * S.E.Δ * (n : Int) := by
    intro x n
    induction n with
    | zero =>
      rw [Nat.add_zero, Restated.proposal_time_opening_eq_l85d facts]
      push_cast
      ring
    | succ k ih =>
      have h := (facts.sch.slot_instants_l55 S.E ((M.opening_slot S.hc x) + k)).2.2.2.1
      rw [← Nat.add_assoc, h, ih]
      push_cast
      ring
  have hv : ∀ x : Round, ∀ n : Nat, M.vote_time S.E ((M.opening_slot S.hc x) + n)
      = 4 * S.E.Δ * (S.hc.R : Int) * (x : Int) + 4 * S.E.Δ * (n : Int) + S.E.Δ := by
    intro x n
    rw [(facts.sch.slot_instants_l55 S.E ((M.opening_slot S.hc x) + n)).1, hp]
  rw [hv, hv, Restated.action_eq_l85d facts]
  push_cast
  have hc0 : (0 : Int) ≤ 4 * S.E.Δ * ((c : Int) * (S.hc.R : Int)) := by positivity
  have hq0' : (0 : Int) ≤ 4 * S.E.Δ * ((q : Int) * (S.hc.R : Int)) := by positivity
  refine ⟨by nlinarith, ?_, by nlinarith, ?_⟩
  · have h0 : ((c : Int) + 1) * (S.hc.R : Int) ≤ (r : Int) * (S.hc.R : Int) :=
      mul_le_mul_of_nonneg_right hcr' (by positivity)
    have h1 : 4 * S.E.Δ * (((c : Int) + 1) * (S.hc.R : Int)) ≤
        4 * S.E.Δ * ((r : Int) * (S.hc.R : Int)) :=
      mul_le_mul_of_nonneg_left h0 (by positivity)
    nlinarith
  · have h0 : ((q : Int) + 1) * (S.hc.R : Int) ≤ (r : Int) * (S.hc.R : Int) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h1 : 4 * S.E.Δ * (((q : Int) + 1) * (S.hc.R : Int)) ≤
        4 * S.E.Δ * ((r : Int) * (S.hc.R : Int)) :=
      mul_le_mul_of_nonneg_left h0 (by positivity)
    nlinarith

/-- If step `m` is the tick at `t`, every validator not held at `t` holds a justified height at
    least `H` after `m` steps, `t ≤ x[n₁].time`, and `v` is honest through step `n₁`, then `v` holds
    a justified height at least `H` after `n₁` steps. -/
theorem hj_ge_of_tickBound_l85f (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    {m : Nat} {t : Int} (hm : Restated.tickStepAt M x m t) {H : Height}
    (hbound : ∀ w ∈ notHeldAt Sched t, H ≤ (x[m][w].st).st.core.h_j)
    {n₁ : Nat} {v : V} (ht : t ≤ (x[n₁].time : Int)) (hv : Restated.HonestThrough M Sched x n₁ v) :
    H ≤ (x[n₁][v].st).st.core.h_j := by
  have hvt : v ∈ notHeldAt Sched t := mem_notHeldAt.mpr (hv t ht)
  have hmn : m ≤ n₁ := by
    by_contra hcon
    have hle : x[n₁].time ≤ x[m].time := Restated.time_mono facts S Sched x (Nat.le_of_not_le hcon)
    have hle' : (x[n₁].time : Int) ≤ (x[m].time : Int) := by exact_mod_cast hle
    have h0 := (Restated.tickStepAt_time facts x hm).2
    linarith
  exact (hbound v hvt).trans (Restated.h_j_mono_sts facts S Sched x v hmn)

/-- If some tick at a time `t` at most one instant before the vote instant of `o_rW + 1` leaves
    every validator not held at `t` with a justified height at least `H`, then at every step from
    one instant before that vote instant on, every validator honest through that step holds a
    justified height at least `H`. -/
theorem hlowShape_of_tickBound_l85f (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    {r : Round} {m : Nat} {t : Int}
    (hm : Restated.tickStepAt M x m t)
    (ht : t ≤ M.vote_time S.E ((M.opening_slot S.hc r) + 1) - 1) {H : Height}
    (hbound : ∀ w ∈ notHeldAt Sched t, H ≤ (x[m][w].st).st.core.h_j) :
    ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc r) + 1) - 1 ≤ (x[n₁].time : Int) →
      Restated.HonestThrough M Sched x n₁ v → H ≤ (x[n₁][v].st).st.core.h_j :=
  fun _ _ h1 hv => Restated.hj_ge_of_tickBound_l85f facts S Sched x hm hbound (ht.trans h1) hv

/-- For every node state that `o_c`'s proposer can hold at `o_c`'s proposal instant, round `c − 1`
    is in the row window of its core store. -/
theorem inWindow_prevRound_at_opening_l85f (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (c : Round) : ∀ w₁ ∈ Restated.Vocabulary.Statements.Instantiation.proposerReadAt M S rho ((M.opening_slot S.hc c)),
    M.inWindow S.hc
      w₁.st.core (c - 1) = true := by
  intro w₁ hw₁
  have hslot : w₁.st.core.s = M.opening_slot S.hc c := by
    simp only [Restated.Vocabulary.Statements.Instantiation.proposerReadAt,
      Restated.Vocabulary.Execution.NamedActionReads.confirmationReadAt] at hw₁
    obtain ⟨w, -, c', -, rfl⟩ := hw₁
    rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.hd.Sts_setClock_core_s]
    exact facts.sch.slotOf_proposal_time S.E _
  have hround : (M.round_of S.hc ((M.opening_slot S.hc c))) = c :=
    facts.gr.round_of_opening_slot_eq S.hc c
  have hone : 1 ≤ S.hc.η_SG := S.hc.η_SG_ge_one
  rw [facts.dt.inWindow_iff, hslot, hround]
  exact ⟨Nat.sub_le_sub_left hone c, Nat.sub_le c 1⟩

/-- In an execution in which every tick has an outcome, along the path `W` of the run up to step
    `n`: under the premises of `openingRow_coveredAtProposal_runAll_l85c`, if `B`'s parent is at
    `P`'s height with `P`'s entry and every round-`c` row every validator not held at `S.a c` can
    sign along `W` is `vote h(P) T_h(P) false`, then for proposals `P`, `P'`, `B` of the reads on
    `W` whose slot-`s` read has round `c` in its row window, `B` covers a target quorum over its
    parent's chain state. -/
theorem targetQuorumCovered_of_plannedRows_l85f (facts : Record.Facts M)
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
    {c : Round} (hc3 : Restated.deadlineRoundW M S tGAT gap + 3 ≤ c)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c) ≤
      ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } : Record.Run V).horizon)
    (hopening : S.E.proposer (M.opening_slot S.hc c) ∈
      notHeldAt Sched (M.confirmation_time S.E (M.opening_slot S.hc c)))
    (hopeningPrev : S.E.proposer (M.opening_slot S.hc (c - 1)) ∈
      notHeldAt Sched (M.confirmation_time S.E (M.opening_slot S.hc (c - 1))))
    {P P' : NamedBlock V}
    {s : Slot} {B : NamedBlock V}
    (hPB : NamedBlock.Preceq P B.parent)
    (hBheight : (M.derive_named S.E S.cfg B.parent).h =
      (M.derive_named S.E S.cfg P).h)
    (hBentry : (M.derive_named S.E S.cfg B.parent).T_h =
      (M.derive_named S.E S.cfg P).T_h)
    (hprop : S.E.proposer s ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c) + S.E.Δ))
    (hphor : M.proposal_time S.E s ≤
      ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } : Record.Run V).horizon)
    (hdelay : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c) + S.E.Δ ≤ M.proposal_time S.E s)
    (hplanned : ∀ u ∈ notHeldAt Sched (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c),
      ∀ nu ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (Restated.runAllPath M S Sched x v₀ n
          (strictEventIndex ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } : Record.Run V)
            (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c)) u) c,
      ∀ D, M.duties_attest_with (M.gradeContract nu.cache) S.E S.hc ((Setup.alwaysAwake S).node u)
        nu.st nu.record ⇢ D →
        D.2.2.height_pair = .vote (M.derive_named S.E S.cfg P).h
          (M.derive_named S.E S.cfg P).T_h.root false) :
    let R : Record.Run V :=
      { Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) }
    let W := Restated.runAllPath M S Sched x v₀ n
    let wp := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c))) (S.E.proposer (M.opening_slot S.hc c))
    ∀ cp : M.Cache,
      M.onPhaseTick S.E S.hc wp.st.core.toHealing (M.proposal_time S.E (M.opening_slot S.hc c)) wp.cache ⇢ cp →
      let pn := M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E (M.opening_slot S.hc c))) wp.record cp
      M.proposal_with (M.gradeContract cp) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc c))) pn.st ⇢ some P →
    let wp' := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc (c - 1)))) (S.E.proposer (M.opening_slot S.hc (c - 1)))
    ∀ cp' : M.Cache,
      M.onPhaseTick S.E S.hc wp'.st.core.toHealing (M.proposal_time S.E (M.opening_slot S.hc (c - 1))) wp'.cache ⇢ cp' →
      let pn' := M.mkNode (M.ns_setClock S.E wp'.st (M.proposal_time S.E (M.opening_slot S.hc (c - 1)))) wp'.record cp'
      M.proposal_with (M.gradeContract cp') .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc (c - 1)))) pn'.st ⇢ some P' →
    let wb := W (strictEventIndex R (M.proposal_time S.E s)) (S.E.proposer s)
    ∀ cb : M.Cache,
      M.onPhaseTick S.E S.hc wb.st.core.toHealing (M.proposal_time S.E s) wb.cache ⇢ cb →
      let pnb := M.mkNode (M.ns_setClock S.E wb.st (M.proposal_time S.E s)) wb.record cb
      M.proposal_with (M.gradeContract cb) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer s)) pnb.st ⇢ some B →
      M.inWindow S.hc pnb.st.core c = true →
    Restated.Vocabulary.Proofs.HealingSurface.NamedTargetQuorumCoveredByChild M S.E
      (M.derive_named S.E S.cfg B.parent) B := by
  intro R W wp cp hcp pn hP wp' cp' hcp' pn' hP' wb cb hcb pnb hB hinWindow
  have hbelow := Restated.belowOneThirdOn_runAll_notHeld facts S Sched x v₀ n hthird hn
    (M.proposal_time S.E s) hphor
  refine ⟨notHeldAt Sched (M.proposal_time S.E s),
    (isQuorum_iff_q_le S.E _).mpr (Proofs.AlignedRoundLemmas.honestQuorum_of_belowOneThird hbelow), ?_⟩
  intro i hi
  have hiA : i ∈ notHeldAt Sched (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c) :=
    notHeldAt_anti hmono ((le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans hdelay) hi
  obtain ⟨nv, hnv⟩ := (p74% actionReadFrom_nonempty₇₄) facts (Setup.alwaysAwake S)
    (W (strictEventIndex R (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c)) i) c
  obtain ⟨D, hD⟩ := facts.dt.attest_with_nonempty (M.gradeContract nv.cache) S.E S.hc
    ((Setup.alwaysAwake S).node i) nv.st nv.record
  have hpl := hplanned i hiA nv hnv D hD
  rcases Restated.openingRow_coveredAtProposal_runAll_l85c facts S Sched x v₀ n hsync hmono hawake hgst hcv
      hvalid hawm hthird hn hcom hrec hc3 hhor hopening hopeningPrev hPB hBheight hprop
      hphor hdelay hi cp hcp hP cp' hcp' hP' cb hcb hB hinWindow nv hnv D hD (Or.inl hpl) with
    ⟨-, -, htp⟩ | hmem
  · exact Or.inl (htp hpl)
  · refine Or.inr ⟨_, hmem, attest_val_index₈₅f facts (Setup.alwaysAwake S) i nv D hD, ?_⟩
    rw [hpl, hBheight, hBentry]

/-- In an execution in which every tick has an outcome, along the path `W` of the run up to step
    `n`: under the premises of `openingRow_coveredAtProposal_runAll_l85c`, if `B`'s parent is at
    `P`'s height with `P`'s entry and every round-`c` row every validator not held at `S.a c` can
    sign along `W` is `vote h(P) T_h(P) b` for some bit `b`, then for proposals `P`, `P'`, `B` of
    the reads on `W` whose slot-`s` read has round `c` in its row window, some quorum's members are
    each in the parent's progress set or sign a row of `B` matching the parent's height and entry. -/
theorem progressQuorum_of_entryRows_l85f (facts : Record.Facts M)
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
    {c : Round} (hc3 : Restated.deadlineRoundW M S tGAT gap + 3 ≤ c)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c) ≤
      ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } : Record.Run V).horizon)
    (hopening : S.E.proposer (M.opening_slot S.hc c) ∈
      notHeldAt Sched (M.confirmation_time S.E (M.opening_slot S.hc c)))
    (hopeningPrev : S.E.proposer (M.opening_slot S.hc (c - 1)) ∈
      notHeldAt Sched (M.confirmation_time S.E (M.opening_slot S.hc (c - 1))))
    {P P' : NamedBlock V}
    {s : Slot} {B : NamedBlock V}
    (hPB : NamedBlock.Preceq P B.parent)
    (hBheight : (M.derive_named S.E S.cfg B.parent).h =
      (M.derive_named S.E S.cfg P).h)
    (hBentry : (M.derive_named S.E S.cfg B.parent).T_h =
      (M.derive_named S.E S.cfg P).T_h)
    (hprop : S.E.proposer s ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c) + S.E.Δ))
    (hphor : M.proposal_time S.E s ≤
      ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } : Record.Run V).horizon)
    (hdelay : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c) + S.E.Δ ≤ M.proposal_time S.E s)
    (hrows : ∀ u ∈ notHeldAt Sched (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c),
      ∀ nu ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (Restated.runAllPath M S Sched x v₀ n
          (strictEventIndex ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } : Record.Run V)
            (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c)) u) c,
      ∀ D, M.duties_attest_with (M.gradeContract nu.cache) S.E S.hc ((Setup.alwaysAwake S).node u)
        nu.st nu.record ⇢ D →
        D.2.2.height_pair = .vote (M.derive_named S.E S.cfg P).h
          (M.derive_named S.E S.cfg P).T_h.root false ∨
        D.2.2.height_pair = .vote (M.derive_named S.E S.cfg P).h
          (M.derive_named S.E S.cfg P).T_h.root true) :
    let R : Record.Run V :=
      { Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) }
    let W := Restated.runAllPath M S Sched x v₀ n
    let wp := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c))) (S.E.proposer (M.opening_slot S.hc c))
    ∀ cp : M.Cache,
      M.onPhaseTick S.E S.hc wp.st.core.toHealing (M.proposal_time S.E (M.opening_slot S.hc c)) wp.cache ⇢ cp →
      let pn := M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E (M.opening_slot S.hc c))) wp.record cp
      M.proposal_with (M.gradeContract cp) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc c))) pn.st ⇢ some P →
    let wp' := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc (c - 1)))) (S.E.proposer (M.opening_slot S.hc (c - 1)))
    ∀ cp' : M.Cache,
      M.onPhaseTick S.E S.hc wp'.st.core.toHealing (M.proposal_time S.E (M.opening_slot S.hc (c - 1))) wp'.cache ⇢ cp' →
      let pn' := M.mkNode (M.ns_setClock S.E wp'.st (M.proposal_time S.E (M.opening_slot S.hc (c - 1)))) wp'.record cp'
      M.proposal_with (M.gradeContract cp') .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc (c - 1)))) pn'.st ⇢ some P' →
    let wb := W (strictEventIndex R (M.proposal_time S.E s)) (S.E.proposer s)
    ∀ cb : M.Cache,
      M.onPhaseTick S.E S.hc wb.st.core.toHealing (M.proposal_time S.E s) wb.cache ⇢ cb →
      let pnb := M.mkNode (M.ns_setClock S.E wb.st (M.proposal_time S.E s)) wb.record cb
      M.proposal_with (M.gradeContract cb) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer s)) pnb.st ⇢ some B →
      M.inWindow S.hc pnb.st.core c = true →
    ∃ Q : Finset V, S.E.electorate.IsQuorum Q ∧ ∀ i ∈ Q,
      i ∈ (M.derive_named S.E S.cfg B.parent).progress ∨
      ∃ a ∈ B.attestations, a.val_index = i ∧
        a.height_pair.matchesEntry (M.derive_named S.E S.cfg B.parent).h
          (M.derive_named S.E S.cfg B.parent).T_h.root = true := by
  intro R W wp cp hcp pn hP wp' cp' hcp' pn' hP' wb cb hcb pnb hB hinWindow
  have hbelow := Restated.belowOneThirdOn_runAll_notHeld facts S Sched x v₀ n hthird hn
    (M.proposal_time S.E s) hphor
  refine ⟨notHeldAt Sched (M.proposal_time S.E s),
    (isQuorum_iff_q_le S.E _).mpr (Proofs.AlignedRoundLemmas.honestQuorum_of_belowOneThird hbelow), ?_⟩
  intro i hi
  have hiA : i ∈ notHeldAt Sched (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c) :=
    notHeldAt_anti hmono ((le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans hdelay) hi
  obtain ⟨nv, hnv⟩ := (p74% actionReadFrom_nonempty₇₄) facts (Setup.alwaysAwake S)
    (W (strictEventIndex R (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c)) i) c
  obtain ⟨D, hD⟩ := facts.dt.attest_with_nonempty (M.gradeContract nv.cache) S.E S.hc
    ((Setup.alwaysAwake S).node i) nv.st nv.record
  have hpl := hrows i hiA nv hnv D hD
  rcases Restated.openingRow_coveredAtProposal_runAll_l85c facts S Sched x v₀ n hsync hmono hawake hgst hcv
      hvalid hawm hthird hn hcom hrec hc3 hhor hopening hopeningPrev hPB hBheight hprop
      hphor hdelay hi cp hcp hP cp' hcp' hP' cb hcb hB hinWindow nv hnv D hD hpl with
    ⟨-, hprog, -⟩ | hmem
  · exact Or.inl hprog
  · refine Or.inr ⟨_, hmem, attest_val_index₈₅f facts (Setup.alwaysAwake S) i nv D hD, ?_⟩
    rw [hBheight, hBentry]
    rcases hpl with h | h <;>
      · rw [h]; exact matchesEntry_vote_iff.mpr ⟨rfl, rfl⟩

/-- For `1 ≤ c`, `S.a (c − 1) + Δ` is at most the proposal instant of `o_c`, which is at most
    `S.a c`, and `o_c = o_{c − 1} + R`. -/
theorem openingInstants_l85f (facts : Record.Facts M) (S : Setup V) {c : Round} (hc : 1 ≤ c) :
    (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) + S.E.Δ ≤ M.proposal_time S.E ((M.opening_slot S.hc c)) ∧
    M.proposal_time S.E ((M.opening_slot S.hc c)) ≤ (Restated.Vocabulary.Execution.Setup.a M S c) ∧
    (M.opening_slot S.hc c) = (M.opening_slot S.hc (c - 1)) + S.hc.R := by
  obtain ⟨k, rfl⟩ : ∃ k : Nat, c = k + 1 := ⟨c - 1, nat_succ_pred_l85f c hc⟩
  have hΔ : (1 : Int) ≤ S.E.Δ := S.E.Δ_pos
  have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  have hk0 : (0 : Int) ≤ (k : Int) := by positivity
  simp only [Nat.add_sub_cancel]
  refine ⟨?_, ?_, ?_⟩
  · rw [Restated.action_eq_l85d facts, Restated.proposal_time_opening_eq_l85d facts]
    push_cast
    nlinarith
  · rw [Restated.action_eq_l85d facts, Restated.proposal_time_opening_eq_l85d facts]
    linarith
  · exact facts.gr.opening_slot_succ_mk S.hc k

/-- In an execution in which every tick has an outcome, under the premises of
    `prevOpeningProposal_preceq_proposedParent_runAll_notHeld`, for proposals `P` and `P'` of the
    two opening proposers' reads on the path `W`, `P` is not genesis and `P'` is an ancestor of
    `P`'s parent as named blocks. -/
theorem prevOpening_namedPreceq_parent_l85f (facts : Record.Facts M)
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
    {c : Round} (hc3 : Restated.deadlineRoundW M S tGAT gap + 3 ≤ c)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c) ≤
      ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } : Record.Run V).horizon)
    (hopening : S.E.proposer (M.opening_slot S.hc c) ∈
      notHeldAt Sched (M.confirmation_time S.E (M.opening_slot S.hc c)))
    (hopeningPrev : S.E.proposer (M.opening_slot S.hc (c - 1)) ∈
      notHeldAt Sched (M.confirmation_time S.E (M.opening_slot S.hc (c - 1))))
    {P P' : NamedBlock V} :
    let R : Record.Run V :=
      { Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) }
    let W := Restated.runAllPath M S Sched x v₀ n
    let wp := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c))) (S.E.proposer (M.opening_slot S.hc c))
    ∀ cp : M.Cache,
      M.onPhaseTick S.E S.hc wp.st.core.toHealing (M.proposal_time S.E (M.opening_slot S.hc c)) wp.cache ⇢ cp →
      let pn := M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E (M.opening_slot S.hc c))) wp.record cp
      M.proposal_with (M.gradeContract cp) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc c))) pn.st ⇢ some P →
    let wp' := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc (c - 1)))) (S.E.proposer (M.opening_slot S.hc (c - 1)))
    ∀ cp' : M.Cache,
      M.onPhaseTick S.E S.hc wp'.st.core.toHealing (M.proposal_time S.E (M.opening_slot S.hc (c - 1))) wp'.cache ⇢ cp' →
      let pn' := M.mkNode (M.ns_setClock S.E wp'.st (M.proposal_time S.E (M.opening_slot S.hc (c - 1)))) wp'.record cp'
      M.proposal_with (M.gradeContract cp') .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc (c - 1)))) pn'.st ⇢ some P' →
    P ≠ .genesis ∧ NamedBlock.Preceq P' P.parent := by
  intro R W wp cp hcp pn hP wp' cp' hcp' pn' hP'
  have hf := Restated.admissibleFieldsOn_runAll_notHeld facts S Sched x v₀ n hsync hmono hawake hgst hcv hvalid
    hawm hthird hn
  have hE2 := Restated.prevOpeningProposal_preceq_proposedParent_runAll_notHeld facts S Sched x v₀ n hsync hmono
    hawake hgst hcv hvalid hawm hthird hn hcom hrec hc3 hhor hopening hopeningPrev
    cp hcp hP cp' hcp' hP'
  have hPrun := (Restated.openingProposal_runBlock_runAll_l85c facts S Sched x v₀ n hsync hmono hawake hgst hcv
    hvalid hawm hthird hn ((Nat.le_succ _).trans hc3) hhor hopening cp hcp hP).1
  have hhor' : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (c - 1)) ≤
      ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } : Record.Run V).horizon :=
    ((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone (Nat.sub_le c 1)).trans hhor
  have hP'run := (Restated.openingProposal_runBlock_runAll_l85c facts S Sched x v₀ n hsync hmono hawake hgst hcv
    hvalid hawm hthird hn (c := c - 1) (nat_prev_round_l85f _ _ hc3) hhor' hopeningPrev
    cp' hcp' hP').1
  have hpncache : pn.cache = cp := facts.nd.mkNode_cache _ _ _
  have hpread : pn ∈ Restated.Vocabulary.Statements.Instantiation.proposerReadAt M
      (Setup.alwaysAwake S) R (M.opening_slot S.hc c) :=
    (p58% mkNode_mem_confirmationReadAt₅₈) hf.sorted hf.onePath _ _ cp hcp
  have hPn : M.proposal_with (M.gradeContract pn.cache) .poolAndCarried S.E S.hc
      ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc c))) pn.st ⇢ some P := by
    rw [hpncache]
    exact hP
  obtain ⟨I, hI⟩ := facts.dt.with_proposal_input_nonempty (M.gradeContract cp) S.E S.hc
    ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc c))) (M.toHealing pn.st.core)
  obtain ⟨p, hp, hperase⟩ := Restated.Vocabulary.Proofs.HealingSurface.proposedBlockAt_parent facts
    (Setup.alwaysAwake S) R (M.opening_slot S.hc c) pn hpread hPn I (by rw [hpncache]; exact hI)
  have hE2I : Block.Preceq P'.erase I.parent := hE2 I hI
  clear hE2
  cases P with
  | genesis => cases hp
  | node pp sl rt vs sp rows proposer =>
    simp only [NamedBlock.parent?] at hp
    have hpp : pp = p := Option.some.inj hp
    subst hpp
    refine ⟨(by intro h; cases h), ?_⟩
    have hprun : Restated.RunBlockOn M (Setup.alwaysAwake S) R W Finset.univ pp :=
      Restated.blockInRun_of_ancestorOn facts (Setup.alwaysAwake S) R W Finset.univ hPrun (by
        have hpar := parent_namedPreceq_l85 (.node pp sl rt vs sp rows proposer)
        rw [Proofs.ModelProperties.named_parent_node] at hpar
        exact hpar)
    rw [Proofs.ModelProperties.named_parent_node]
    exact Restated.namedPreceq_of_runBlock_erase_preceqOn facts (notHeldAt Sched) Finset.univ hf hP'run hprun
      (by rw [hperase]; exact hE2I)

/-- In an execution in which every tick has an outcome, along the path `W` of the run up to step
    `n`: under the premises of `windowParent_l85d`, if `c` is at least four rounds after the
    deadline round, the proposers of `o_c`, `o_c + 1`, `o_c + 2`, `o_{c − 1}` and `o_{c − 2}` are
    not held at their confirmation instants, `nj(P) = false`, every round-`c` row of every validator
    not held at `S.a c` is `vote h(P) T_h(P) false`, and every round-`(c − 1)` row of every
    validator not held at `S.a (c − 1)` is `vote h(P') T_h(P') false` when `nj(P') = false`, then
    for proposals `P`, `P₂`, `P'`, `P''` of those slots' reads on `W`: `h(P) ≤ h_j(P₂)` and
    `P ⪯ P₂`. -/
theorem windowJustified_exec_l85f (facts : Record.Facts M) 
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v₀ : V) (n : Nat)
    {tGAT tE : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hn : (x[n].time : Int) ≤ tE)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    {c : Round} (hc4 : Restated.deadlineRoundW M S tGAT gap + 4 ≤ c)
    (hvoteHor : M.vote_time S.E ((M.opening_slot S.hc c) + 2) ≤ (x[n].time : Int))
    (hprops : ∀ k < 3, S.E.proposer ((M.opening_slot S.hc c) + k) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c) + k)))
    (hopeningPrev : S.E.proposer (M.opening_slot S.hc (c - 1)) ∈
      notHeldAt Sched (M.confirmation_time S.E (M.opening_slot S.hc (c - 1))))
    (hopeningPrev2 : S.E.proposer (M.opening_slot S.hc (c - 2)) ∈
      notHeldAt Sched (M.confirmation_time S.E (M.opening_slot S.hc (c - 2))))
    {P P₂ P' P'' : NamedBlock V}
    (hnj : (M.derive_named S.E S.cfg P).nj = false)
    (hplannedC : ∀ u ∈ notHeldAt Sched (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c),
      ∀ nu ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (Restated.runAllPath M S Sched x v₀ n
          (strictEventIndex ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } : Record.Run V)
            (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c)) u) c,
      ∀ D, M.duties_attest_with (M.gradeContract nu.cache) S.E S.hc ((Setup.alwaysAwake S).node u)
        nu.st nu.record ⇢ D →
        D.2.2.height_pair = .vote (M.derive_named S.E S.cfg P).h
          (M.derive_named S.E S.cfg P).T_h.root false)
    (hplannedM : ∀ u ∈ notHeldAt Sched (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (c - 1)),
      (M.derive_named S.E S.cfg P').nj = false →
      ∀ nu ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (Restated.runAllPath M S Sched x v₀ n
          (strictEventIndex ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } : Record.Run V)
            (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (c - 1))) u) (c - 1),
      ∀ D, M.duties_attest_with (M.gradeContract nu.cache) S.E S.hc ((Setup.alwaysAwake S).node u)
        nu.st nu.record ⇢ D →
        D.2.2.height_pair = .vote (M.derive_named S.E S.cfg P').h
          (M.derive_named S.E S.cfg P').T_h.root false) :
    let R : Record.Run V :=
      { Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) }
    let W := Restated.runAllPath M S Sched x v₀ n
    let wp := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c))) (S.E.proposer (M.opening_slot S.hc c))
    ∀ cp : M.Cache,
      M.onPhaseTick S.E S.hc wp.st.core.toHealing (M.proposal_time S.E (M.opening_slot S.hc c)) wp.cache ⇢ cp →
      let pn := M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E (M.opening_slot S.hc c))) wp.record cp
      M.proposal_with (M.gradeContract cp) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc c))) pn.st ⇢ some P →
    let wp₂ := W (strictEventIndex R (M.proposal_time S.E ((M.opening_slot S.hc c) + 2))) (S.E.proposer ((M.opening_slot S.hc c) + 2))
    ∀ cp₂ : M.Cache,
      M.onPhaseTick S.E S.hc wp₂.st.core.toHealing (M.proposal_time S.E ((M.opening_slot S.hc c) + 2)) wp₂.cache ⇢ cp₂ →
      let pn₂ := M.mkNode (M.ns_setClock S.E wp₂.st (M.proposal_time S.E ((M.opening_slot S.hc c) + 2))) wp₂.record cp₂
      M.proposal_with (M.gradeContract cp₂) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer ((M.opening_slot S.hc c) + 2))) pn₂.st ⇢ some P₂ →
    let wp' := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc (c - 1)))) (S.E.proposer (M.opening_slot S.hc (c - 1)))
    ∀ cp' : M.Cache,
      M.onPhaseTick S.E S.hc wp'.st.core.toHealing (M.proposal_time S.E (M.opening_slot S.hc (c - 1))) wp'.cache ⇢ cp' →
      let pn' := M.mkNode (M.ns_setClock S.E wp'.st (M.proposal_time S.E (M.opening_slot S.hc (c - 1)))) wp'.record cp'
      M.proposal_with (M.gradeContract cp') .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc (c - 1)))) pn'.st ⇢ some P' →
    let wp'' := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc (c - 2)))) (S.E.proposer (M.opening_slot S.hc (c - 2)))
    ∀ cp'' : M.Cache,
      M.onPhaseTick S.E S.hc wp''.st.core.toHealing (M.proposal_time S.E (M.opening_slot S.hc (c - 2))) wp''.cache ⇢ cp'' →
      let pn'' := M.mkNode (M.ns_setClock S.E wp''.st (M.proposal_time S.E (M.opening_slot S.hc (c - 2)))) wp''.record cp''
      M.proposal_with (M.gradeContract cp'') .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc (c - 2)))) pn''.st ⇢ some P'' →
    (M.derive_named S.E S.cfg P).h ≤ (M.derive_named S.E S.cfg P₂).h_j ∧
      NamedBlock.Preceq P P₂ := by
  intro R W wp cp hcp pn hP wp₂ cp₂ hcp₂ pn₂ hP₂ wp' cp' hcp' pn' hP' wp'' cp'' hcp'' pn'' hP''
  have hopening : S.E.proposer (M.opening_slot S.hc c) ∈
      notHeldAt Sched (M.confirmation_time S.E (M.opening_slot S.hc c)) := by
    simpa only [Nat.add_zero] using hprops 0 (by decide)
  have hprop2 := hprops 2 (by decide)
  obtain ⟨hAc, -, -, -, hAcDelta, hpv⟩ := Restated.interiorInstants_l85d facts S c
  have hAcHor : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c) ≤ (x[n].time : Int) := hAc.trans (hpv.trans hvoteHor)
  obtain ⟨hc2, hc3, hc1, hc3', hsub⟩ := nat_window_rounds_l85f _ _ hc4
  have hf := Restated.admissibleFieldsOn_runAll_notHeld facts S Sched x v₀ n hsync hmono hawake hgst hcv hvalid
    hawm hthird hn
  obtain ⟨hP₂ne, hPQ, hQslot2, hsl⟩ := Restated.windowParent_l85d facts S Sched x v₀ n hsync hmono hawake hgst
    hcv hvalid hawm hthird hn hcom hrec hc2 hvoteHor hopening hprop2 cp hcp hP cp₂ hcp₂ hP₂
  obtain ⟨hPne, hPm⟩ := Restated.prevOpening_namedPreceq_parent_l85f facts S Sched x v₀ n hsync hmono hawake
    hgst hcv hvalid hawm hthird hn hcom hrec hc3 hAcHor hopening hopeningPrev
    cp hcp hP cp' hcp' hP'
  have hPmslot : P'.slot = (M.opening_slot S.hc (c - 1)) :=
    proposal_slot₈₅f facts hf.sorted hf.onePath _ cp' hcp' hP'
  obtain ⟨hAmDelta, hpropA, hoc⟩ := Restated.openingInstants_l85f facts S hc1
  have hQslot : P₂.parent.slot + 1 ≤ (M.opening_slot S.hc (c - 1)) + S.cfg.timeoutDelay := by
    exact nat_slot_budget_l85f _ _ _ _ _ hQslot2 hoc S.hc.R_ge_three S.timeout_rounds.2
  have hpropHor : M.proposal_time S.E ((M.opening_slot S.hc c) + 2) ≤ (x[n].time : Int) :=
    hpv.trans hvoteHor
  have hprop2' : S.E.proposer ((M.opening_slot S.hc c) + 2) ∈
      notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c) + S.E.Δ) :=
    notHeldAt_anti hmono (hAcDelta.trans (facts.sch.proposal_time_le_confirmation_time S.E _))
      hprop2
  have hp₂read : pn₂ ∈ Restated.Vocabulary.Statements.Instantiation.proposerReadAt M
      (Setup.alwaysAwake S) R ((M.opening_slot S.hc c) + 2) :=
    (p58% mkNode_mem_confirmationReadAt₅₈) hf.sorted hf.onePath _ _ cp₂ hcp₂
  have hpread : pn ∈ Restated.Vocabulary.Statements.Instantiation.proposerReadAt M
      (Setup.alwaysAwake S) R (M.opening_slot S.hc c) :=
    (p58% mkNode_mem_confirmationReadAt₅₈) hf.sorted hf.onePath _ _ cp hcp
  have hcov2 : (M.derive_named S.E S.cfg P₂.parent).h =
        (M.derive_named S.E S.cfg P).h →
      (M.derive_named S.E S.cfg P₂.parent).T_h =
        (M.derive_named S.E S.cfg P).T_h →
      Restated.Vocabulary.Proofs.HealingSurface.NamedTargetQuorumCoveredByChild M S.E
        (M.derive_named S.E S.cfg P₂.parent) P₂ := fun hQH hT =>
    Restated.targetQuorumCovered_of_plannedRows_l85f facts S Sched x v₀ n hsync hmono hawake hgst hcv hvalid
      hawm hthird hn hcom hrec hc3 hAcHor hopening hopeningPrev (P := P) (P' := P')
      (s := (M.opening_slot S.hc c) + 2) (B := P₂) hPQ hQH hT hprop2'
      hpropHor hAcDelta hplannedC cp hcp hP cp' hcp' hP' cp₂ hcp₂ hP₂
      (Restated.Vocabulary.Proofs.HealingSurface.inWindow_round_at_plusTwo facts (Setup.alwaysAwake S) R c pn₂ hp₂read)
  have hAmHor : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (c - 1)) ≤ (x[n].time : Int) :=
    ((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone (Nat.sub_le c 1)).trans hAcHor
  have hpropP : S.E.proposer (M.opening_slot S.hc c) ∈
      notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (c - 1)) + S.E.Δ) :=
    notHeldAt_anti hmono (hAmDelta.trans (facts.sch.proposal_time_le_confirmation_time S.E _))
      hopening
  have hpropHorP : M.proposal_time S.E (M.opening_slot S.hc c) ≤ (x[n].time : Int) :=
    hpropA.trans hAcHor
  have hP'P : NamedBlock.Preceq P' P := namedPreceq_trans_l85 hPm (parent_namedPreceq_l85 P)
  have hcovc : (M.derive_named S.E S.cfg P').h = (M.derive_named S.E S.cfg P).h →
      (M.derive_named S.E S.cfg P.parent).h = (M.derive_named S.E S.cfg P).h →
      (M.derive_named S.E S.cfg P.parent).T_h = (M.derive_named S.E S.cfg P').T_h →
      Restated.Vocabulary.Proofs.HealingSurface.NamedTargetQuorumCoveredByChild M S.E
        (M.derive_named S.E S.cfg P.parent) P := fun hPmH hparH hTpar => by
    have hnj' : (M.derive_named S.E S.cfg P').nj = false := by
      rw [facts.csAdded.nj_eq_on_plateau_l85 S.E S.cfg hP'P hPmH]; exact hnj
    have key := Restated.targetQuorumCovered_of_plannedRows_l85f facts S Sched x v₀ n hsync hmono hawake hgst hcv
      hvalid hawm hthird hn hcom hrec (c := c - 1) hc3' hAmHor hopeningPrev
      (by rw [hsub]; exact hopeningPrev2) (P := P') (P' := P'') (s := (M.opening_slot S.hc c)) (B := P) hPm
      (hparH.trans hPmH.symm) hTpar hpropP hpropHorP hAmDelta
      (fun u hu => hplannedM u hu hnj')
    rw [hsub] at key
    exact key cp' hcp' hP' cp'' hcp'' hP'' cp hcp hP
      (Restated.inWindow_prevRound_at_opening_l85f facts (Setup.alwaysAwake S) R c pn hpread)
  exact ⟨facts.csAdded.windowJustified_l85d S.E S.cfg hsl hPne hP₂ne hnj hPm hPmslot hPQ hQslot hcov2 hcovc,
    namedPreceq_trans_l85 hPQ (parent_namedPreceq_l85 P₂)⟩

/-- In an execution in which every tick has an outcome, along the path `W` of the run up to step
    `n`: if `c` is at least two rounds after the deadline round, `c + 1 ≤ c'`,
    `S.a c' ≤ x[n].time ≤ tE`, and the proposers of `o_c` and `o_{c'}` are not held at their
    confirmation instants, then for proposals `P` and `P'` of their reads on `W`, `P ⪯ P'`. -/
theorem openingProposal_namedPreceq_later_l85f (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v₀ : V) (n : Nat)
    {tGAT tE : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hn : (x[n].time : Int) ≤ tE)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    {c c' : Round} (hc : Restated.deadlineRoundW M S tGAT gap + 2 ≤ c) (hcc : c + 1 ≤ c')
    (hhor : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c') ≤ (x[n].time : Int))
    (hopening : S.E.proposer (M.opening_slot S.hc c) ∈
      notHeldAt Sched (M.confirmation_time S.E (M.opening_slot S.hc c)))
    (hopening' : S.E.proposer (M.opening_slot S.hc c') ∈
      notHeldAt Sched (M.confirmation_time S.E (M.opening_slot S.hc c')))
    {P P' : NamedBlock V} :
    let R : Record.Run V :=
      { Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) }
    let W := Restated.runAllPath M S Sched x v₀ n
    let wp := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c))) (S.E.proposer (M.opening_slot S.hc c))
    ∀ cp : M.Cache,
      M.onPhaseTick S.E S.hc wp.st.core.toHealing (M.proposal_time S.E (M.opening_slot S.hc c)) wp.cache ⇢ cp →
      let pn := M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E (M.opening_slot S.hc c))) wp.record cp
      M.proposal_with (M.gradeContract cp) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc c))) pn.st ⇢ some P →
    let wp' := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c'))) (S.E.proposer (M.opening_slot S.hc c'))
    ∀ cp' : M.Cache,
      M.onPhaseTick S.E S.hc wp'.st.core.toHealing (M.proposal_time S.E (M.opening_slot S.hc c')) wp'.cache ⇢ cp' →
      let pn' := M.mkNode (M.ns_setClock S.E wp'.st (M.proposal_time S.E (M.opening_slot S.hc c'))) wp'.record cp'
      M.proposal_with (M.gradeContract cp') .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc c'))) pn'.st ⇢ some P' →
    NamedBlock.Preceq P P' := by
  intro R W wp cp hcp pn hP wp' cp' hcp' pn' hP'
  obtain ⟨h1, hdk⟩ := nat_later_round_l85f _ _ hc
  have hc2' : Restated.deadlineRoundW M S tGAT gap + 2 ≤ c' := hc.trans ((Nat.le_succ c).trans hcc)
  have hAc : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c) ≤ (x[n].time : Int) :=
    ((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone ((Nat.le_succ c).trans hcc)).trans hhor
  have hf := Restated.admissibleFieldsOn_runAll_notHeld facts S Sched x v₀ n hsync hmono hawake hgst hcv hvalid
    hawm hthird hn
  have hPrun := (Restated.openingProposal_runBlock_runAll_l85c facts S Sched x v₀ n hsync hmono hawake hgst hcv
    hvalid hawm hthird hn hc hAc hopening cp hcp hP).1
  have hP'run := (Restated.openingProposal_runBlock_runAll_l85c facts S Sched x v₀ n hsync hmono hawake hgst hcv
    hvalid hawm hthird hn hc2' hhor hopening' cp' hcp' hP').1
  have hconf' : (Restated.Vocabulary.Execution.Setup.a M S c') = M.confirmation_time S.E (M.opening_slot S.hc c') :=
    Restated.a_eq_confirmation_opening_l58 facts S c'
  have hvote : M.vote_time S.E (M.opening_slot S.hc c') ≤
      M.confirmation_time S.E (M.opening_slot S.hc c') :=
    facts.sch.Protocol_vote_time_le_confirmation_time S.E _
  have hvhor : M.vote_time S.E (M.opening_slot S.hc c') + S.E.Δ ≤ (x[n].time : Int) := by
    have hhor2 : M.confirmation_time S.E (M.opening_slot S.hc c') ≤ (x[n].time : Int) := by
      rw [← hconf']; exact hhor
    have hΔ := S.E.Δ_pos
    obtain ⟨hv0, -, -, -, -, hc0⟩ := facts.sch.slot_instants_l55 S.E (M.opening_slot S.hc c')
    linarith
  have hw1 : S.E.proposer (M.opening_slot S.hc c') ∈
      notHeldAt Sched (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c) :=
    notHeldAt_anti hmono (((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone ((Nat.le_succ c).trans hcc)).trans
      (le_of_eq hconf')) hopening'
  have hw2 : S.E.proposer (M.opening_slot S.hc c') ∈
      notHeldAt Sched (M.vote_time S.E (M.opening_slot S.hc c')) :=
    notHeldAt_anti hmono hvote hopening'
  have hsg := Restated.sgBlock_eq_openingProposal_runAll_notHeld facts S Sched x v₀ n hsync hmono hawake hgst hcv
    hvalid hawm hthird hn hcom hrec hc hAc hopening cp hcp hP
  have hhead := (Restated.openingAdoption_at_strongWindow_afterDeadline facts S Sched x v₀ n hsync hmono hawake
    hgst hcv hvalid hawm hthird hn hcom hrec hc2' hhor hopening' cp' hcp' hP').1
  obtain ⟨H, cw, hcw, Tr, hTr, L, hL, L', hL', hH⟩ :=
    (p86g% exists_headOutcome₈₆g) facts (Setup.alwaysAwake S)
      (W (strictEventIndex R (M.vote_time S.E (M.opening_slot S.hc c'))) (S.E.proposer (M.opening_slot S.hc c')))
      (M.vote_time S.E (M.opening_slot S.hc c'))
  obtain ⟨nv0, hnv0, g0, hg0, G0, hG0⟩ := (p56% exists_actionSG₅₆) facts (Setup.alwaysAwake S)
    (W (strictEventIndex R (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c)) (S.E.proposer (M.opening_slot S.hc c'))) c
  have hG0P : G0 = P.erase := hsg _ hw1 nv0 hnv0 g0 hg0 G0 hG0
  have hHP' : H = P'.erase := hhead _ hw2 cw hcw Tr hTr L hL L' hL' H hH
  have hGH : Block.Preceq G0 H := by
    have hc1eq : c = (c - 1) + 1 := nat_succ_pred_l85f c h1
    have hk : Restated.fgSafetyProgressDeadline (Setup.alwaysAwake S) R
        (Restated.roundAt M S tGAT + S.hc.η_SG) gap (Setup.alwaysAwake S).extraRounds ≤ c - 1 := by
      rw [Restated.fgSafetyProgressDeadline_eq_deadlineRoundW facts]
      exact hdk
    have hd : (M.opening_slot S.hc ((c - 1) + 1)) + 1 ≤ (M.opening_slot S.hc c') := by
      rw [← hc1eq]
      calc (M.opening_slot S.hc c) + 1 ≤ (M.opening_slot S.hc c) + S.hc.R :=
            Nat.add_le_add_left (le_trans (by decide) S.hc.R_ge_three) _
        _ = (M.opening_slot S.hc (c + 1)) := (facts.gr.opening_slot_succ S.hc c).symm
        _ ≤ (M.opening_slot S.hc c') := facts.gr.opening_slot_le_of_le S.hc hcc
    have hSG := Restated.actionSGBlock_preceq_voterHeadAt_runAll_notHeld facts S Sched x v₀ n hsync hmono hawake
      hgst hcv hvalid hawm hthird hn hcom hrec (c := c - 1) (d := (M.opening_slot S.hc c')) hk hd hvhor
      (v := S.E.proposer (M.opening_slot S.hc c')) (w := S.E.proposer (M.opening_slot S.hc c'))
      (by rw [← hc1eq]; exact hw1) hw2
    rw [← hc1eq] at hSG
    exact hSG cw hcw Tr hTr L hL L' hL' H hH nv0 hnv0 g0 hg0 G0 hG0
  rw [hG0P, hHP'] at hGH
  exact Restated.namedPreceq_of_runBlock_erase_preceqOn facts (notHeldAt Sched) Finset.univ hf hPrun hP'run hGH

/-- In an execution in which every tick has an outcome, along the path `W` of the run up to step
    `n`: under the premises of `windowParent_l85d` at `c₂`, if `gap + 2 ≤ K`, `c₁` is at least two
    and `c₂` at least four rounds after the deadline round, `c₁ + tD / R ≤ c₂ ≤ c₁ + tD / R + gap`,
    the proposers of `o_{c₁}`, `o_{c₂}`, `o_{c₂} + 1`, `o_{c₂} + 2`, `o_{c₂ − 1}` and `o_{c₂ − 2}`
    are not held at their confirmation instants, `P₁` and `P₂` both have the `nj` bit set, and every
    round-`(c₂ − 1)` row of every validator not held at `S.a (c₂ − 1)` is `vote h(Pm) T_h(Pm) b` for
    some bit `b`, then for proposals `P₁`, `P₂`, `B`, `Pm`, `Pmm` of those slots' reads on `W`:
    `h(P₁) ≤ h_j(P₂)`. -/
theorem climb_excluded_l85f (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v₀ : V) (n : Nat)
    {tGAT tE : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hn : (x[n].time : Int) ≤ tE)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    (hgap : gap + 2 ≤ S.cfg.K)
    {c₁ c₂ : Round} (hc₁ : Restated.deadlineRoundW M S tGAT gap + 2 ≤ c₁)
    (hc₂ : Restated.deadlineRoundW M S tGAT gap + 4 ≤ c₂)
    (hlo : c₁ + S.cfg.timeoutDelay / S.hc.R ≤ c₂)
    (hhi : c₂ ≤ c₁ + S.cfg.timeoutDelay / S.hc.R + gap)
    (hvoteHor : M.vote_time S.E ((M.opening_slot S.hc c₂) + 2) ≤ (x[n].time : Int))
    (hopening₁ : S.E.proposer (M.opening_slot S.hc c₁) ∈
      notHeldAt Sched (M.confirmation_time S.E (M.opening_slot S.hc c₁)))
    (hprops₂ : ∀ k < 3, S.E.proposer ((M.opening_slot S.hc c₂) + k) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c₂) + k)))
    (hopeningM : S.E.proposer (M.opening_slot S.hc (c₂ - 1)) ∈
      notHeldAt Sched (M.confirmation_time S.E (M.opening_slot S.hc (c₂ - 1))))
    (hopeningMM : S.E.proposer (M.opening_slot S.hc (c₂ - 2)) ∈
      notHeldAt Sched (M.confirmation_time S.E (M.opening_slot S.hc (c₂ - 2))))
    {P₁ P₂ B Pm Pmm : NamedBlock V}
    (hnj₁ : (M.derive_named S.E S.cfg P₁).nj = true)
    (hnj₂ : (M.derive_named S.E S.cfg P₂).nj = true)
    (hrowsM : ∀ u ∈ notHeldAt Sched (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (c₂ - 1)),
      ∀ nu ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (Restated.runAllPath M S Sched x v₀ n
          (strictEventIndex ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } : Record.Run V)
            (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (c₂ - 1))) u) (c₂ - 1),
      ∀ D, M.duties_attest_with (M.gradeContract nu.cache) S.E S.hc ((Setup.alwaysAwake S).node u)
        nu.st nu.record ⇢ D →
        D.2.2.height_pair = .vote (M.derive_named S.E S.cfg Pm).h
          (M.derive_named S.E S.cfg Pm).T_h.root false ∨
        D.2.2.height_pair = .vote (M.derive_named S.E S.cfg Pm).h
          (M.derive_named S.E S.cfg Pm).T_h.root true) :
    let R : Record.Run V :=
      { Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) }
    let W := Restated.runAllPath M S Sched x v₀ n
    let wp₁ := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c₁))) (S.E.proposer (M.opening_slot S.hc c₁))
    ∀ cp₁ : M.Cache,
      M.onPhaseTick S.E S.hc wp₁.st.core.toHealing (M.proposal_time S.E (M.opening_slot S.hc c₁)) wp₁.cache ⇢ cp₁ →
      let pn₁ := M.mkNode (M.ns_setClock S.E wp₁.st (M.proposal_time S.E (M.opening_slot S.hc c₁))) wp₁.record cp₁
      M.proposal_with (M.gradeContract cp₁) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc c₁))) pn₁.st ⇢ some P₁ →
    let wp₂ := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c₂))) (S.E.proposer (M.opening_slot S.hc c₂))
    ∀ cp₂ : M.Cache,
      M.onPhaseTick S.E S.hc wp₂.st.core.toHealing (M.proposal_time S.E (M.opening_slot S.hc c₂)) wp₂.cache ⇢ cp₂ →
      let pn₂ := M.mkNode (M.ns_setClock S.E wp₂.st (M.proposal_time S.E (M.opening_slot S.hc c₂))) wp₂.record cp₂
      M.proposal_with (M.gradeContract cp₂) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc c₂))) pn₂.st ⇢ some P₂ →
    let wb := W (strictEventIndex R (M.proposal_time S.E ((M.opening_slot S.hc c₂) + 2))) (S.E.proposer ((M.opening_slot S.hc c₂) + 2))
    ∀ cb : M.Cache,
      M.onPhaseTick S.E S.hc wb.st.core.toHealing (M.proposal_time S.E ((M.opening_slot S.hc c₂) + 2)) wb.cache ⇢ cb →
      let pnb := M.mkNode (M.ns_setClock S.E wb.st (M.proposal_time S.E ((M.opening_slot S.hc c₂) + 2))) wb.record cb
      M.proposal_with (M.gradeContract cb) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer ((M.opening_slot S.hc c₂) + 2))) pnb.st ⇢ some B →
    let wpm := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc (c₂ - 1)))) (S.E.proposer (M.opening_slot S.hc (c₂ - 1)))
    ∀ cpm : M.Cache,
      M.onPhaseTick S.E S.hc wpm.st.core.toHealing (M.proposal_time S.E (M.opening_slot S.hc (c₂ - 1))) wpm.cache ⇢ cpm →
      let pnm := M.mkNode (M.ns_setClock S.E wpm.st (M.proposal_time S.E (M.opening_slot S.hc (c₂ - 1)))) wpm.record cpm
      M.proposal_with (M.gradeContract cpm) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc (c₂ - 1)))) pnm.st ⇢ some Pm →
    let wpmm := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc (c₂ - 2)))) (S.E.proposer (M.opening_slot S.hc (c₂ - 2)))
    ∀ cpmm : M.Cache,
      M.onPhaseTick S.E S.hc wpmm.st.core.toHealing (M.proposal_time S.E (M.opening_slot S.hc (c₂ - 2))) wpmm.cache ⇢ cpmm →
      let pnmm := M.mkNode (M.ns_setClock S.E wpmm.st (M.proposal_time S.E (M.opening_slot S.hc (c₂ - 2)))) wpmm.record cpmm
      M.proposal_with (M.gradeContract cpmm) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc (c₂ - 2)))) pnmm.st ⇢ some Pmm →
    (M.derive_named S.E S.cfg P₁).h ≤ (M.derive_named S.E S.cfg P₂).h_j := by
  intro R W wp₁ cp₁ hcp₁ pn₁ hP₁ wp₂ cp₂ hcp₂ pn₂ hP₂ wb cb hcb pnb hB wpm cpm hcpm pnm hPm
    wpmm cpmm hcpmm pnmm hPmm
  by_contra hlt
  have hlt' : (M.derive_named S.E S.cfg P₂).h_j < (M.derive_named S.E S.cfg P₁).h :=
    Nat.lt_of_not_le hlt
  obtain ⟨hc2, hc3, hc1, hc3', hsub⟩ := nat_window_rounds_l85f _ _ hc₂
  have hopening₂ : S.E.proposer (M.opening_slot S.hc c₂) ∈
      notHeldAt Sched (M.confirmation_time S.E (M.opening_slot S.hc c₂)) := by
    simpa only [Nat.add_zero] using hprops₂ 0 (by decide)
  have hprop2 := hprops₂ 2 (by decide)
  obtain ⟨hAc, -, -, -, -, hpv⟩ := Restated.interiorInstants_l85d facts S c₂
  have hAcHor : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c₂) ≤ (x[n].time : Int) := hAc.trans (hpv.trans hvoteHor)
  have hf := Restated.admissibleFieldsOn_runAll_notHeld facts S Sched x v₀ n hsync hmono hawake hgst hcv hvalid
    hawm hthird hn
  obtain ⟨-, hP₂B', -, hslB⟩ := Restated.windowParent_l85d facts S Sched x v₀ n hsync hmono hawake hgst hcv
    hvalid hawm hthird hn hcom hrec hc2 hvoteHor hopening₂ hprop2 cp₂ hcp₂ hP₂ cb hcb hB
  have hP₂B : NamedBlock.Preceq P₂ B := namedPreceq_trans_l85 hP₂B' (parent_namedPreceq_l85 B)
  have hsl : ∀ X : NamedBlock V, NamedBlock.Preceq X P₂ → X ≠ .genesis →
      X.parent.slot < X.slot := fun X hX hne => hslB X (namedPreceq_trans_l85 hX hP₂B) hne
  obtain ⟨hP₂ne, hPmPar⟩ := Restated.prevOpening_namedPreceq_parent_l85f facts S Sched x v₀ n hsync hmono hawake
    hgst hcv hvalid hawm hthird hn hcom hrec hc3 hAcHor hopening₂ hopeningM
    cp₂ hcp₂ hP₂ cpm hcpm hPm
  have hRpos : 0 < S.hc.R := lt_of_lt_of_le (by decide) S.hc.R_ge_three
  have hm2 : 2 ≤ S.cfg.timeoutDelay / S.hc.R :=
    (Nat.le_div_iff_mul_le hRpos).mpr (by simpa only [Nat.mul_comm] using S.timeout_rounds.2)
  have hc1M : c₁ + 1 ≤ c₂ - 1 := nat_gap_rounds_l85f _ _ _ hlo hm2
  have hAmHor : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (c₂ - 1)) ≤ (x[n].time : Int) :=
    ((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone (Nat.sub_le c₂ 1)).trans hAcHor
  have hP₁Pm := Restated.openingProposal_namedPreceq_later_l85f facts S Sched x v₀ n hsync hmono hawake hgst hcv
    hvalid hawm hthird hn hcom hrec hc₁ hc1M hAmHor hopening₁ hopeningM
    cp₁ hcp₁ hP₁ cpm hcpm hPm
  have hPmP₂ : NamedBlock.Preceq Pm P₂ := namedPreceq_trans_l85 hPmPar (parent_namedPreceq_l85 P₂)
  have hP₁P₂ : NamedBlock.Preceq P₁ P₂ := namedPreceq_trans_l85 hP₁Pm hPmP₂
  have h1m := facts.cs.derive_height_mono S.E S.cfg hP₁Pm
  have hm2' := facts.cs.derive_height_mono S.E S.cfg hPmP₂
  have hslot₁ : P₁.slot = (M.opening_slot S.hc c₁) :=
    proposal_slot₈₅f facts hf.sorted hf.onePath _ cp₁ hcp₁ hP₁
  have hslot₂ : P₂.slot = (M.opening_slot S.hc c₂) :=
    proposal_slot₈₅f facts hf.sorted hf.onePath _ cp₂ hcp₂ hP₂
  have hd : c₂ = c₁ + (c₂ - c₁) :=
    (fun (a b t : Nat) (h : a + t ≤ b) => (by omega : b = a + (b - a))) _ _ _ hlo
  have hfar : (M.opening_slot S.hc c₁) + S.cfg.timeoutDelay ≤ (M.opening_slot S.hc c₂) := by
    rw [hd, facts.gr.opening_slot_add]
    have h := nat_window_far_l85f 0 (c₂ - c₁) S.hc.R S.cfg.timeoutDelay S.timeout_rounds.1
      ((fun (a b t : Nat) (h : a + t ≤ b) => (by omega : 0 + t ≤ b - a)) _ _ _ hlo)
    rw [Nat.zero_mul, Nat.zero_add] at h
    exact Nat.add_le_add_left h _
  rcases lt_or_eq_of_le (h1m.trans hm2') with hlt12 | heq
  ·
    have hK1 : S.cfg.K ∣ (M.derive_named S.E S.cfg P₁).h := by
      by_contra hK
      rw [facts.csAdded.nj_false_of_not_dvd_l85 S.E S.cfg P₁ hK] at hnj₁
      exact Bool.false_ne_true hnj₁
    have hK2 : S.cfg.K ∣ (M.derive_named S.E S.cfg P₂).h := by
      by_contra hK
      rw [facts.csAdded.nj_false_of_not_dvd_l85 S.E S.cfg P₂ hK] at hnj₂
      exact Bool.false_ne_true hnj₂
    have hreach := nat_dvd_step_l85f _ _ _ hK1 hK2 hlt12
    have hsp := facts.csAdded.progress_spacing_l85 S.E S.cfg hsl hP₁P₂ (k := S.cfg.K)
      (nat_one_le_of_l85f _ _ hgap) hlt'
      (fun j hj1 hjK => nat_not_dvd_add_l85f _ _ _ hK1 hj1 hjK) hreach
    rw [hslot₁, hslot₂, hd, facts.gr.opening_slot_add] at hsp
    exact nat_climb_far_l85f 0 (c₂ - c₁) _ _ _ _ S.timeout_rounds.1 S.timeout_rounds.2 hgap
      ((fun (a b t g : Nat) (h : b ≤ a + t + g) => (by omega : b - a ≤ 0 + t + g)) _ _ _ _ hhi)
      ((fun (o y z R : Nat) (h : o + 1 + y ≤ o + z) => (by omega : 0 * R + 1 + y ≤ z)) _ _ _ _ hsp)
  ·
    have hPmH : (M.derive_named S.E S.cfg Pm).h = (M.derive_named S.E S.cfg P₂).h :=
      Nat.le_antisymm hm2' (heq ▸ h1m)
    obtain ⟨hAmDelta, -, -⟩ := Restated.openingInstants_l85f facts S hc1
    have hpropP₂ : S.E.proposer (M.opening_slot S.hc c₂) ∈
        notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (c₂ - 1)) + S.E.Δ) :=
      notHeldAt_anti hmono (hAmDelta.trans (facts.sch.proposal_time_le_confirmation_time S.E _))
        hopening₂
    have hpropHorP₂ : M.proposal_time S.E (M.opening_slot S.hc c₂) ≤ (x[n].time : Int) :=
      (Restated.openingInstants_l85f facts S hc1).2.1.trans hAcHor
    have hpread₂ : pn₂ ∈ Restated.Vocabulary.Statements.Instantiation.proposerReadAt M
        (Setup.alwaysAwake S) R (M.opening_slot S.hc c₂) :=
      (p58% mkNode_mem_confirmationReadAt₅₈) hf.sorted hf.onePath _ _ cp₂ hcp₂
    have hyoung := facts.csAdded.climb_entryYoung_l85 S.E S.cfg hP₂ne hPmPar hPmH (fun hparH hTpar => by
      have key := Restated.progressQuorum_of_entryRows_l85f facts S Sched x v₀ n hsync hmono hawake hgst hcv hvalid hawm
        hthird hn hcom hrec (c := c₂ - 1) hc3' hAmHor hopeningM
        (by rw [hsub]; exact hopeningMM) (P := Pm) (P' := Pmm) (s := (M.opening_slot S.hc c₂)) (B := P₂) hPmPar
        (hparH.trans hPmH.symm) hTpar hpropP₂ hpropHorP₂ hAmDelta hrowsM
      rw [hsub] at key
      exact key cpm hcpm hPm cpmm hcpmm hPmm cp₂ hcp₂ hP₂
        (Restated.inWindow_prevRound_at_opening_l85f facts (Setup.alwaysAwake S) R c₂ pn₂ hpread₂))
    have hT : (M.derive_named S.E S.cfg P₁).T_h = (M.derive_named S.E S.cfg P₂).T_h :=
      facts.cs.entry_eq_on_plateau S.E S.cfg hP₁P₂ heq
    obtain ⟨E₀, hE₀, -, -, hE₀s⟩ := Restated.entry_named_l85 facts S.E S.cfg P₁
    have hE₀le := (slot_le_of_namedPreceq_l85 hsl hE₀ hP₁P₂).1
    rw [hslot₂, ← hT, ← hE₀s] at hyoung
    rw [hslot₁] at hE₀le
    exact nat_plateau_far_l85f _ _ _ _ hyoung hE₀le hfar

/-- In an execution in which every tick has an outcome, along the path `W` of the run up to step
    `N`: if `rD' + 1 ≤ q`, `q + 1 ≤ rW`, `S.a q ≤ x[N].time ≤ tE` and `T_D'` is an anchor at the
    re-based deadline round `rD'`, then for proposals `P` and `P'` of the opening proposers' reads
    of `q` and `q − 1` on `W`, either every round-`q` row of every validator not held at `S.a q` is
    `vote h(P) T_h(P) b`, with `b = false` when `nj(P) = false`, or some tick step `m` at a time `t`
    at most one instant before the vote instant of `o_rW + 1` leaves every validator not held at `t`
    with a justified height at least `h(T_D')`. -/
theorem plannedRows_or_tickBound_l85f (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v₀ : V) (N : Nat)
    {tGAT tE : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    (hlen : tGAT + (Restated.healingLengthη M S gap + (Restated.constants M S).period) ≤ tE) (htd : Restated.TimeDiverges M x)
    {T_D' : NamedBlock V}
    (hA : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.rebasedDeadlineRoundW M S tGAT gap) T_D')
    (hnW : (x[N].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) (hn : (x[N].time : Int) ≤ tE)
    {q : Round} (hq' : Restated.rebasedDeadlineRoundW M S tGAT gap + 1 ≤ q)
    (hq3 : Restated.deadlineRoundW M S tGAT gap + 3 ≤ q) (hqW : q + 1 ≤ Restated.switchRound M S tE)
    (hqhor : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) q) ≤ (x[N].time : Int))
    (hopening : S.E.proposer (M.opening_slot S.hc q) ∈
      notHeldAt Sched (M.confirmation_time S.E (M.opening_slot S.hc q)))
    (hopeningPrev : S.E.proposer (M.opening_slot S.hc (q - 1)) ∈
      notHeldAt Sched (M.confirmation_time S.E (M.opening_slot S.hc (q - 1))))
    {P P' : NamedBlock V} :
    let R : Record.Run V :=
      { Restated.runAll M S Sched x v₀ N with honest := notHeldAt Sched (x[N].time : Int) }
    let W := Restated.runAllPath M S Sched x v₀ N
    let wp := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc q))) (S.E.proposer (M.opening_slot S.hc q))
    ∀ cp : M.Cache,
      M.onPhaseTick S.E S.hc wp.st.core.toHealing (M.proposal_time S.E (M.opening_slot S.hc q)) wp.cache ⇢ cp →
      let pn := M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E (M.opening_slot S.hc q))) wp.record cp
      M.proposal_with (M.gradeContract cp) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc q))) pn.st ⇢ some P →
    let wp' := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc (q - 1)))) (S.E.proposer (M.opening_slot S.hc (q - 1)))
    ∀ cp' : M.Cache,
      M.onPhaseTick S.E S.hc wp'.st.core.toHealing (M.proposal_time S.E (M.opening_slot S.hc (q - 1))) wp'.cache ⇢ cp' →
      let pn' := M.mkNode (M.ns_setClock S.E wp'.st (M.proposal_time S.E (M.opening_slot S.hc (q - 1)))) wp'.record cp'
      M.proposal_with (M.gradeContract cp') .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc (q - 1)))) pn'.st ⇢ some P' →
    (∀ u ∈ notHeldAt Sched (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) q),
      ∀ nu ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (W (strictEventIndex R (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) q)) u) q,
      ∀ D, M.duties_attest_with (M.gradeContract nu.cache) S.E S.hc ((Setup.alwaysAwake S).node u)
        nu.st nu.record ⇢ D →
      (D.2.2.height_pair =
            .vote (M.derive_named S.E S.cfg P).h
              (M.derive_named S.E S.cfg P).T_h.root false ∨
          D.2.2.height_pair =
            .vote (M.derive_named S.E S.cfg P).h
              (M.derive_named S.E S.cfg P).T_h.root true) ∧
        ((M.derive_named S.E S.cfg P).nj = false →
          D.2.2.height_pair =
            .vote (M.derive_named S.E S.cfg P).h
              (M.derive_named S.E S.cfg P).T_h.root false)) ∨
    ∃ (m : Nat) (t : Int), Restated.tickStepAt M x m t ∧
      t ≤ M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) - 1 ∧
      ∀ w ∈ notHeldAt Sched t,
        (M.derive_named S.E S.cfg T_D').h ≤ (x[m][w].st).st.core.h_j := by
  intro R W wp cp hcp pn hP wp' cp' hcp' pn' hP'
  have htop := Restated.openingProposal_height_ge_rebasedAnchor_l85d facts S Sched x v₀ N hsync hmono hawake
    hgst hcv hvalid hawm hthird hn hcom hrec hA hq' hqhor hopening cp hcp hP
  rcases Restated.honestRow_atOpening_planned_runAll_l85e facts S Sched x v₀ N hsync hmono hawake hgst hcv hvalid
      hawm hthird hcom hrec hlen htd hA hnW hq3 hqhor hopening hopeningPrev htop
      cp hcp hP cp' hcp' hP' with
    hpl | hst
  · exact Or.inl hpl
  · right
    obtain ⟨-, -, hpos, hle⟩ := Restated.assemblyInstants_l85f facts S (q := q) (c := q) le_rfl hqW
    obtain ⟨mq, hmq⟩ := Restated.exists_tickStepAt facts x htd hpos
    have hmqN : mq + 1 ≤ N := by
      by_contra hcon
      have hle' : x[N].time ≤ x[mq].time := Restated.time_mono facts S Sched x (by omega)
      have hle'' : (x[N].time : Int) ≤ (x[mq].time : Int) := by exact_mod_cast hle'
      have h0 := (Restated.tickStepAt_time facts x hmq).2
      have hq : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) q) = (Restated.Vocabulary.Execution.Setup.a M S q) := rfl
      linarith
    refine ⟨mq, (Restated.Vocabulary.Execution.Setup.a M S q), hmq, hle, fun w hw => htop.trans ?_⟩
    have h := hst w hw
    have hstep := Restated.stateBeforeTime_runAll_tick facts S Sched x v₀ hmq hmqN w
    exact h.trans (le_of_eq (congrArg (fun z => z.st.core.h_j) hstep))

/-- In an execution in which every tick has an outcome, under the phase's premises, for every anchor
    `T_D'` at the re-based deadline round there are a step `m` and a time `t` such that step `m` is
    the tick at `t`, `t` is at most one instant before the vote instant of `o_rW + 1`, and every
    validator not held at `t` holds a justified height at least `h(T_D')` after `m` steps. -/
theorem exists_tickBound_l85f (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (tGAT tE : Int) (gap : Nat)
    (hgap : gap + 2 ≤ S.cfg.K)
    (hlen : tGAT + (Restated.healingLengthη M S gap + (Restated.constants M S).period) ≤ tE)
    (hgst : S.E.t_GST ≤ tGAT) (hmono : Sched.MonotoneCorruption)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (htd : Restated.TimeDiverges M x)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    {T_D' : NamedBlock V}
    (hA : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.rebasedDeadlineRoundW M S tGAT gap) T_D') :
    ∃ (m : Nat) (t : Int), Restated.tickStepAt M x m t ∧
      t ≤ M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) - 1 ∧
      ∀ w ∈ notHeldAt Sched t,
        (M.derive_named S.E S.cfg T_D').h ≤ (x[m][w].st).st.core.h_j := by
  have hlen' : tGAT + Restated.healingLengthη M S gap ≤ tE := Restated.healingLength_le_of_kit_l76 facts S hlen
  have v₀ : V := S.E.proposer 0
  obtain ⟨c₁, c₂, hc₁, hlo, hhi, hc₂W, hwin⟩ := Restated.twoStrongWindows_l85d facts S Sched hgst hlen' hrec
  obtain ⟨hprops₁, hprev₁, hprev2₁⟩ := hwin c₁ (Or.inl rfl)
  obtain ⟨hprops₂, hprev₂, hprev2₂⟩ := hwin c₂ (Or.inr rfl)
  obtain ⟨h4₁, h4₂, h2₁, h12, hq'₁, hq'₂, hq'₁m, hq'₂m, h3₁, h3₂, h3₁m, h3₂m, hW₁, hW₁m, hW₂m,
    hsub₁, hsub₂⟩ := nat_assembly_rounds_l85f (Restated.deadlineRoundW M S tGAT gap) gap c₁ c₂
      (S.cfg.timeoutDelay / S.hc.R) (Restated.switchRound M S tE) hc₁ hlo hc₂W
  obtain ⟨hpos, htW, -, -⟩ := Restated.assemblyInstants_l85f facts S (q := c₂) le_rfl hc₂W
  obtain ⟨m, hm⟩ := Restated.exists_tickStepAt facts x htd hpos
  have htime : (x[m + 1].time : Int) = M.vote_time S.E ((M.opening_slot S.hc c₂) + 2) :=
    (Restated.tickStepAt_time facts x hm).1
  have hrW : Restated.rebasedDeadlineRoundW M S tGAT gap ≤ Restated.switchRound M S tE :=
    Restated.rebasedDeadlineRoundW_le_switchRound facts S tGAT tE gap (Restated.runAll M S Sched x v₀ 0) hgst hlen'
  have hrD : Restated.deadlineRoundW M S tGAT gap ≤ Restated.switchRound M S tE :=
    (Restated.deadlineRoundW_le_rebased facts S tGAT gap).trans hrW
  obtain ⟨-, hWE⟩ := Restated.window_in_phase_atRound facts S tGAT tE gap hgst hlen' hrD le_rfl
  have hvW : M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) - 1 ≤
      (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)) := by
    have h1 := Restated.vote_time_succ_le_confirmation_time_l77 facts S ((M.opening_slot S.hc (Restated.switchRound M S tE)))
    rw [← Restated.a_eq_confirmation_opening_l58 facts] at h1
    linarith
  have hnW : (x[m + 1].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)) := by
    rw [htime]; exact htW.trans hvW
  have hn : (x[m + 1].time : Int) ≤ tE := hnW.trans hWE
  have htE : M.vote_time S.E ((M.opening_slot S.hc c₂) + 2) ≤ tE := htime ▸ hn
  obtain ⟨hAc₂, -, -, -, -, hpv₂⟩ := Restated.interiorInstants_l85d facts S c₂
  have hA₂ : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c₂) ≤ (x[m + 1].time : Int) := by
    rw [htime]; exact hAc₂.trans hpv₂
  have hA₁ : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c₁) ≤ (x[m + 1].time : Int) :=
    ((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone h12).trans hA₂
  have hA₁m : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (c₁ - 1)) ≤ (x[m + 1].time : Int) :=
    ((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone (Nat.sub_le c₁ 1)).trans hA₁
  have hA₂m : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (c₂ - 1)) ≤ (x[m + 1].time : Int) :=
    ((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone (Nat.sub_le c₂ 1)).trans hA₂
  have hvt₂ : M.vote_time S.E ((M.opening_slot S.hc c₂) + 2) ≤ (x[m + 1].time : Int) :=
    le_of_eq htime.symm
  have hvt₁' : M.vote_time S.E ((M.opening_slot S.hc c₁) + 2) ≤
      M.vote_time S.E ((M.opening_slot S.hc c₂) + 2) :=
    Restated.vote_time_mono_l58 facts S.E (Nat.add_le_add_right (facts.gr.opening_slot_mono S h12) 2)
  have hvt₁ : M.vote_time S.E ((M.opening_slot S.hc c₁) + 2) ≤ (x[m + 1].time : Int) :=
    hvt₁'.trans hvt₂
  have hf := Restated.admissibleFieldsOn_runAll_notHeld facts S Sched x v₀ (m + 1) hsync hmono hawake hgst hcv
    hexec hmult hthird hn
  obtain ⟨cp₁, P₁, hcp₁, hP₁⟩ := exists_proposal₈₅f facts hf.sorted hf.onePath (M.opening_slot S.hc c₁)
  obtain ⟨cb₁, B₁, hcb₁, hB₁⟩ := exists_proposal₈₅f facts hf.sorted hf.onePath ((M.opening_slot S.hc c₁) + 2)
  obtain ⟨cm₁, M₁, hcm₁, hM₁⟩ := exists_proposal₈₅f facts hf.sorted hf.onePath (M.opening_slot S.hc (c₁ - 1))
  obtain ⟨cmm₁, MM₁, hcmm₁, hMM₁⟩ := exists_proposal₈₅f facts hf.sorted hf.onePath (M.opening_slot S.hc (c₁ - 2))
  obtain ⟨cp₂, P₂, hcp₂, hP₂⟩ := exists_proposal₈₅f facts hf.sorted hf.onePath (M.opening_slot S.hc c₂)
  obtain ⟨cb₂, B₂, hcb₂, hB₂⟩ := exists_proposal₈₅f facts hf.sorted hf.onePath ((M.opening_slot S.hc c₂) + 2)
  obtain ⟨cm₂, M₂, hcm₂, hM₂⟩ := exists_proposal₈₅f facts hf.sorted hf.onePath (M.opening_slot S.hc (c₂ - 1))
  obtain ⟨cmm₂, MM₂, hcmm₂, hMM₂⟩ := exists_proposal₈₅f facts hf.sorted hf.onePath (M.opening_slot S.hc (c₂ - 2))
  have hopening₁ : S.E.proposer (M.opening_slot S.hc c₁) ∈
      notHeldAt Sched (M.confirmation_time S.E (M.opening_slot S.hc c₁)) := by
    simpa only [Nat.add_zero] using hprops₁ 0 (by decide)
  have hopening₂ : S.E.proposer (M.opening_slot S.hc c₂) ∈
      notHeldAt Sched (M.confirmation_time S.E (M.opening_slot S.hc c₂)) := by
    simpa only [Nat.add_zero] using hprops₂ 0 (by decide)
  rcases Restated.plannedRows_or_tickBound_l85f facts S Sched x v₀ (m + 1) hsync hmono hawake hgst hcv hexec
      hmult hthird hcom hrec hlen htd hA hnW hn hq'₁ h3₁ hW₁ hA₁ hopening₁ hprev₁ (P := P₁) (P' := M₁)
      cp₁ hcp₁ hP₁ cm₁ hcm₁ hM₁ with
    hC₁ | hdone
  swap
  · exact hdone
  have key₁ := Restated.plannedRows_or_tickBound_l85f facts S Sched x v₀ (m + 1) hsync hmono hawake hgst hcv hexec
      hmult hthird hcom hrec hlen htd hA hnW hn (q := c₁ - 1) hq'₁m h3₁m hW₁m hA₁m hprev₁
      (by rw [hsub₁]; exact hprev2₁) (P := M₁) (P' := MM₁)
  rw [hsub₁] at key₁
  rcases key₁ cm₁ hcm₁ hM₁ cmm₁ hcmm₁ hMM₁ with hCm₁ | hdone
  swap
  · exact hdone
  rcases Restated.plannedRows_or_tickBound_l85f facts S Sched x v₀ (m + 1) hsync hmono hawake hgst hcv hexec
      hmult hthird hcom hrec hlen htd hA hnW hn hq'₂ h3₂ hc₂W hA₂ hopening₂ hprev₂ (P := P₂) (P' := M₂)
      cp₂ hcp₂ hP₂ cm₂ hcm₂ hM₂ with
    hC₂ | hdone
  swap
  · exact hdone
  have key₂ := Restated.plannedRows_or_tickBound_l85f facts S Sched x v₀ (m + 1) hsync hmono hawake hgst hcv hexec
      hmult hthird hcom hrec hlen htd hA hnW hn (q := c₂ - 1) hq'₂m h3₂m hW₂m hA₂m hprev₂
      (by rw [hsub₂]; exact hprev2₂) (P := M₂) (P' := MM₂)
  rw [hsub₂] at key₂
  rcases key₂ cm₂ hcm₂ hM₂ cmm₂ hcmm₂ hMM₂ with hCm₂ | hdone
  swap
  · exact hdone
  have htop₁ := Restated.openingProposal_height_ge_rebasedAnchor_l85d facts S Sched x v₀ (m + 1) hsync hmono
    hawake hgst hcv hexec hmult hthird hn hcom hrec hA hq'₁ hA₁ hopening₁ cp₁ hcp₁ hP₁
  have htop₂ := Restated.openingProposal_height_ge_rebasedAnchor_l85d facts S Sched x v₀ (m + 1) hsync hmono
    hawake hgst hcv hexec hmult hthird hn hcom hrec hA hq'₂ hA₂ hopening₂ cp₂ hcp₂ hP₂
  refine ⟨m, M.vote_time S.E ((M.opening_slot S.hc c₂) + 2), hm, htW, fun w hw => ?_⟩
  by_cases hnj₁ : (M.derive_named S.E S.cfg P₁).nj = false
  · obtain ⟨hJ, hPB⟩ := Restated.windowJustified_exec_l85f facts S Sched x v₀ (m + 1) hsync hmono hawake hgst
      hcv hexec hmult hthird hn hcom hrec h4₁ hvt₁ hprops₁ hprev₁ hprev2₁
      (P := P₁) (P₂ := B₁) (P' := M₁) (P'' := MM₁) hnj₁
      (fun u hu nu hnu D hD => (hC₁ u hu nu hnu D hD).2 hnj₁)
      (fun u hu hnj' nu hnu D hD => (hCm₁ u hu nu hnu D hD).2 hnj')
      cp₁ hcp₁ hP₁ cb₁ hcb₁ hB₁ cm₁ hcm₁ hM₁ cmm₁ hcmm₁ hMM₁
    have hheld := (Restated.windowProposal_held_atTick_l85d facts S Sched x v₀ hsync hmono hawake hgst hcv hexec
      hmult hthird hcom hrec h2₁ hm hvt₁' htE hopening₁ (hprops₁ 2 (by decide)) hPB
      hw cp₁ hcp₁ hP₁ cb₁ hcb₁ hB₁).2
    exact htop₁.trans (hJ.trans hheld)
  have hnj₁' : (M.derive_named S.E S.cfg P₁).nj = true := by
    simpa only [Bool.not_eq_false] using hnj₁
  have h2₂ : Restated.deadlineRoundW M S tGAT gap + 2 ≤ c₂ := h2₁.trans h12
  by_cases hnj₂ : (M.derive_named S.E S.cfg P₂).nj = false
  · obtain ⟨hJ, hPB⟩ := Restated.windowJustified_exec_l85f facts S Sched x v₀ (m + 1) hsync hmono hawake hgst
      hcv hexec hmult hthird hn hcom hrec h4₂ hvt₂ hprops₂ hprev₂ hprev2₂
      (P := P₂) (P₂ := B₂) (P' := M₂) (P'' := MM₂) hnj₂
      (fun u hu nu hnu D hD => (hC₂ u hu nu hnu D hD).2 hnj₂)
      (fun u hu hnj' nu hnu D hD => (hCm₂ u hu nu hnu D hD).2 hnj')
      cp₂ hcp₂ hP₂ cb₂ hcb₂ hB₂ cm₂ hcm₂ hM₂ cmm₂ hcmm₂ hMM₂
    have hheld := (Restated.windowProposal_held_atTick_l85d facts S Sched x v₀ hsync hmono hawake hgst hcv hexec
      hmult hthird hcom hrec h2₂ hm le_rfl htE hopening₂ (hprops₂ 2 (by decide)) hPB
      hw cp₂ hcp₂ hP₂ cb₂ hcb₂ hB₂).2
    exact htop₂.trans (hJ.trans hheld)
  have hnj₂' : (M.derive_named S.E S.cfg P₂).nj = true := by
    simpa only [Bool.not_eq_false] using hnj₂
  have hclimb := Restated.climb_excluded_l85f facts S Sched x v₀ (m + 1) hsync hmono hawake hgst hcv hexec hmult
    hthird hn hcom hrec hgap h2₁ h4₂ hlo hhi hvt₂ hopening₁ hprops₂ hprev₂ hprev2₂
    (P₁ := P₁) (P₂ := P₂) (B := B₂) (Pm := M₂) (Pmm := MM₂) hnj₁' hnj₂'
    (fun u hu nu hnu D hD => (hCm₂ u hu nu hnu D hD).1)
    cp₁ hcp₁ hP₁ cp₂ hcp₂ hP₂ cb₂ hcb₂ hB₂ cm₂ hcm₂ hM₂ cmm₂ hcmm₂ hMM₂
  obtain ⟨-, hPQ, -, -⟩ := Restated.windowParent_l85d facts S Sched x v₀ (m + 1) hsync hmono hawake hgst hcv hexec
    hmult hthird hn hcom hrec h2₂ hvt₂ hopening₂ (hprops₂ 2 (by decide)) cp₂ hcp₂ hP₂ cb₂ hcb₂ hB₂
  have hPB : NamedBlock.Preceq P₂ B₂ := namedPreceq_trans_l85 hPQ (parent_namedPreceq_l85 B₂)
  have hheld := (Restated.windowProposal_held_atTick_l85d facts S Sched x v₀ hsync hmono hawake hgst hcv hexec
    hmult hthird hcom hrec h2₂ hm le_rfl htE hopening₂ (hprops₂ 2 (by decide)) hPB hw
    cp₂ hcp₂ hP₂ cb₂ hcb₂ hB₂).2
  exact htop₁.trans (hclimb.trans
    ((Restated.Vocabulary.Proofs.HealingSurface.namedJustification_le_of_preceq facts S.E S.cfg hPB).trans hheld))

/-- In an execution in which every tick has an outcome, under the phase's premises, for every step
    `n_W` that is the tick at the switch round's action instant, every anchor `T_D'` at the re-based
    deadline round, and every step `n₁ ≤ n_W` whose time is at least one instant before the vote
    instant of `o_rW + 1`, every validator honest through step `n₁` holds a justified height at
    least `h(T_D')` after `n₁` steps. -/
theorem hlow_of_premises_l85f (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (tGAT tE : Int) (gap : Nat)
    (hgap : gap + 2 ≤ S.cfg.K)
    (hlen : tGAT + (Restated.healingLengthη M S gap + (Restated.constants M S).period) ≤ tE)
    (hgst : S.E.t_GST ≤ tGAT) (hmono : Sched.MonotoneCorruption)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched)
    (hwakes : Restated.WakesAtActionInstants M S Sched) (hsleeps : Restated.SleepsAfterActionInstants M S Sched)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (htd : Restated.TimeDiverges M x)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    (hsl : sleepinessW S Sched tE) (hrs : Restated.roundSleepinessW M S Sched tE)
    (hcs : Restated.committeeSleepinessW M S Sched tE) :
    ∀ n_W : Nat, Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) →
      ∀ T_D' : NamedBlock V,
      Restated.AnchorAtRound M S Sched x tGAT tE (Restated.rebasedDeadlineRoundW M S tGAT gap) T_D' →
      ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) - 1
        ≤ (x[n₁].time : Int) →
      n₁ ≤ n_W → Restated.HonestThrough M Sched x n₁ v →
      (M.derive_named S.E S.cfg T_D').h ≤ (x[n₁][v].st).st.core.h_j := by
  intro n_W _ T_D' hA v n₁ ht₁ _ hv
  obtain ⟨m, t, hm, ht, hb⟩ := Restated.exists_tickBound_l85f facts S Sched x tGAT tE gap hgap hlen hgst hmono
    hexec hsync hmult hcv htd hcom hthird hawake hrec hA
  exact Restated.hlowShape_of_tickBound_l85f facts S Sched x hm ht hb v n₁ ht₁ hv

/-- Under the phase's premises, `Restated.BaseJustifiedHighAtSwitchRoundW M S Sched x tGAT tE gap`:
    for every anchor `T_D'` at the re-based deadline round, every step `n_W` that is the tick at the
    switch round's action instant and every validator honest through `n_W`, the justified height its
    store holds after `n_W` steps is at least `h(T_D')`. -/
theorem baseJustifiedHighAtSwitchRoundW_of_phase (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (tGAT tE : Int) (gap : Nat)
    (hgap : gap + 2 ≤ S.cfg.K)
    (hlen : tGAT + (Restated.healingLengthη M S gap + (Restated.constants M S).period) ≤ tE)
    (hgst : S.E.t_GST ≤ tGAT) (hmono : Sched.MonotoneCorruption)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched)
    (hwakes : Restated.WakesAtActionInstants M S Sched) (hsleeps : Restated.SleepsAfterActionInstants M S Sched)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (htd : Restated.TimeDiverges M x)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    (hsl : sleepinessW S Sched tE) (hrs : Restated.roundSleepinessW M S Sched tE)
    (hcs : Restated.committeeSleepinessW M S Sched tE) :
    Restated.BaseJustifiedHighAtSwitchRoundW M S Sched x tGAT tE gap := by
  intro T_D' hA n_W hnW v hv
  obtain ⟨m, t, hm, ht, hb⟩ := Restated.exists_tickBound_l85f facts S Sched x tGAT tE gap hgap hlen hgst hmono
    hexec hsync hmult hcv htd hcom hthird hawake hrec hA
  have h1 := (Restated.tickStepAt_time facts x hnW).2
  have h2 := Restated.vote_time_succ_le_confirmation_time_l77 facts S ((M.opening_slot S.hc (Restated.switchRound M S tE)))
  rw [Restated.a_eq_confirmation_opening_l58 facts] at h1
  exact Restated.hlowShape_of_tickBound_l85f facts S Sched x hm ht hb v n_W (by linarith) hv

end

end DecoupledConsensusModel.Sts.Restated
