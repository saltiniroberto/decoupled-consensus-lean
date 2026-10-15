import Proofs.Instance.Model
import Model.Record.Facts
import Proofs.Instance.Facts.ForkChoice
import Proofs.Instance.Facts.SubtypeEqualities

/-!
# Saved grades and chain-state conditions at `Model.specDraft`

The fields of `NodeFacts` saying that writing saved grades into a node store changes no core field
and no routine read on the core store, the field `StoreFacts.rootFresh_of_distinct`, and the fields
`HandlersFacts.update_finality_F_of_conditions` and `HandlersFacts.chainStateInTree_of_derived`,
proved at `Model.specDraft`.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

open SpecDraftRecord
open DecoupledConsensusModel.Execution
open scoped DC

theorem _root_.SpecDraftRecord.NodeFacts.specDraft_store_with_cache_core_T :
    ∀ (st : (Model.specDraft (V := V)).NS) (c : (Model.specDraft (V := V)).Cache),
      ((Model.specDraft (V := V)).store_with_cache st c).core.T = st.core.T := by
  intro st c
  rfl

theorem _root_.SpecDraftRecord.NodeFacts.specDraft_store_with_cache_core_F :
    ∀ (st : (Model.specDraft (V := V)).NS) (c : (Model.specDraft (V := V)).Cache),
      ((Model.specDraft (V := V)).store_with_cache st c).core.F = st.core.F := by
  intro st c
  rfl

theorem _root_.SpecDraftRecord.NodeFacts.specDraft_store_with_cache_core_J :
    ∀ (st : (Model.specDraft (V := V)).NS) (c : (Model.specDraft (V := V)).Cache),
      ((Model.specDraft (V := V)).store_with_cache st c).core.J = st.core.J := by
  intro st c
  rfl

theorem _root_.SpecDraftRecord.NodeFacts.specDraft_store_with_cache_core_s :
    ∀ (st : (Model.specDraft (V := V)).NS) (c : (Model.specDraft (V := V)).Cache),
      ((Model.specDraft (V := V)).store_with_cache st c).core.s = st.core.s := by
  intro st c
  rfl

theorem _root_.SpecDraftRecord.NodeFacts.specDraft_store_with_cache_core_t :
    ∀ (st : (Model.specDraft (V := V)).NS) (c : (Model.specDraft (V := V)).Cache),
      ((Model.specDraft (V := V)).store_with_cache st c).core.t = st.core.t := by
  intro st c
  rfl

theorem _root_.SpecDraftRecord.NodeFacts.specDraft_store_with_cache_core_h_max :
    ∀ (st : (Model.specDraft (V := V)).NS) (c : (Model.specDraft (V := V)).Cache),
      ((Model.specDraft (V := V)).store_with_cache st c).core.h_max = st.core.h_max := by
  intro st c
  rfl

theorem _root_.SpecDraftRecord.NodeFacts.specDraft_store_with_cache_core_h_j :
    ∀ (st : (Model.specDraft (V := V)).NS) (c : (Model.specDraft (V := V)).Cache),
      ((Model.specDraft (V := V)).store_with_cache st c).core.h_j = st.core.h_j := by
  intro st c
  rfl

theorem _root_.SpecDraftRecord.NodeFacts.specDraft_store_with_cache_core_σ :
    ∀ (st : (Model.specDraft (V := V)).NS) (c : (Model.specDraft (V := V)).Cache),
      ((Model.specDraft (V := V)).store_with_cache st c).core.σ = st.core.σ := by
  intro st c
  rfl

theorem _root_.SpecDraftRecord.NodeFacts.specDraft_store_with_cache_core_timestamp_block :
    ∀ (st : (Model.specDraft (V := V)).NS) (c : (Model.specDraft (V := V)).Cache),
      ((Model.specDraft (V := V)).store_with_cache st c).core.timestamp_block = st.core.timestamp_block := by
  intro st c
  rfl

theorem _root_.SpecDraftRecord.NodeFacts.specDraft_store_with_cache_core_timestamp_vote :
    ∀ (st : (Model.specDraft (V := V)).NS) (c : (Model.specDraft (V := V)).Cache),
      ((Model.specDraft (V := V)).store_with_cache st c).core.timestamp_vote = st.core.timestamp_vote := by
  intro st c
  rfl

theorem _root_.SpecDraftRecord.NodeFacts.specDraft_store_with_cache_core_timestamp_sg_vote :
    ∀ (st : (Model.specDraft (V := V)).NS) (c : (Model.specDraft (V := V)).Cache),
      ((Model.specDraft (V := V)).store_with_cache st c).core.timestamp_sg_vote = st.core.timestamp_sg_vote := by
  intro st c
  rfl

theorem _root_.SpecDraftRecord.NodeFacts.specDraft_store_with_cache_core_gf_votes :
    ∀ (st : (Model.specDraft (V := V)).NS) (c : (Model.specDraft (V := V)).Cache),
      ((Model.specDraft (V := V)).store_with_cache st c).core.gf_votes = st.core.gf_votes := by
  intro st c
  rfl

theorem _root_.SpecDraftRecord.NodeFacts.specDraft_store_with_cache_core_pool :
    ∀ (st : (Model.specDraft (V := V)).NS) (c : (Model.specDraft (V := V)).Cache),
      ((Model.specDraft (V := V)).store_with_cache st c).core.pool = st.core.pool := by
  intro st c
  rfl

theorem _root_.SpecDraftRecord.NodeFacts.specDraft_store_with_cache_core_live_confirmed :
    ∀ (st : (Model.specDraft (V := V)).NS) (c : (Model.specDraft (V := V)).Cache),
      ((Model.specDraft (V := V)).store_with_cache st c).core.live_confirmed = st.core.live_confirmed := by
  intro st c
  rfl

theorem _root_.SpecDraftRecord.NodeFacts.specDraft_store_with_cache_core_latest_confirmed :
    ∀ (st : (Model.specDraft (V := V)).NS) (c : (Model.specDraft (V := V)).Cache),
      ((Model.specDraft (V := V)).store_with_cache st c).core.latest_confirmed = st.core.latest_confirmed := by
  intro st c
  rfl

theorem _root_.SpecDraftRecord.NodeFacts.specDraft_store_with_cache_core_latest_stable :
    ∀ (st : (Model.specDraft (V := V)).NS) (c : (Model.specDraft (V := V)).Cache),
      ((Model.specDraft (V := V)).store_with_cache st c).core.latest_stable = st.core.latest_stable := by
  intro st c
  rfl

theorem _root_.SpecDraftRecord.NodeFacts.specDraft_store_with_cache_get_fg_root :
    ∀ (st : (Model.specDraft (V := V)).NS) (c : (Model.specDraft (V := V)).Cache),
      (Model.specDraft (V := V)).get_fg_root ((Model.specDraft (V := V)).toHealing ((Model.specDraft (V := V)).store_with_cache st c).core).toFG =
        (Model.specDraft (V := V)).get_fg_root ((Model.specDraft (V := V)).toHealing st.core).toFG := by
  intro st c
  rfl

theorem _root_.SpecDraftRecord.NodeFacts.specDraft_store_with_cache_get_filtered_block_tree :
    ∀ (st : (Model.specDraft (V := V)).NS) (c : (Model.specDraft (V := V)).Cache),
      (Model.specDraft (V := V)).get_filtered_block_tree ((Model.specDraft (V := V)).toHealing ((Model.specDraft (V := V)).store_with_cache st c).core).toFG =
        (Model.specDraft (V := V)).get_filtered_block_tree ((Model.specDraft (V := V)).toHealing st.core).toFG := by
  intro st c
  rfl

theorem _root_.SpecDraftRecord.NodeFacts.specDraft_store_with_cache_voter_filtered_block_tree :
    ∀ (st : (Model.specDraft (V := V)).NS) (c : (Model.specDraft (V := V)).Cache) (E : DecoupledConsensusModel.Env V) (s : DecoupledConsensusModel.Slot),
      (Model.specDraft (V := V)).voter_filtered_block_tree E ((Model.specDraft (V := V)).store_with_cache st c).core s =
        (Model.specDraft (V := V)).voter_filtered_block_tree E st.core s := by
  intro st c E s
  rfl

theorem _root_.SpecDraftRecord.NodeFacts.specDraft_store_with_cache_voter_processed_block_tree :
    ∀ (st : (Model.specDraft (V := V)).NS) (c : (Model.specDraft (V := V)).Cache) (E : DecoupledConsensusModel.Env V) (s : DecoupledConsensusModel.Slot),
      (Model.specDraft (V := V)).voter_processed_block_tree E ((Model.specDraft (V := V)).toHealing ((Model.specDraft (V := V)).store_with_cache st c).core).toFG.toSG.toGoldfishStore s =
        (Model.specDraft (V := V)).voter_processed_block_tree E ((Model.specDraft (V := V)).toHealing st.core).toFG.toSG.toGoldfishStore s := by
  intro st c E s
  rfl

theorem _root_.SpecDraftRecord.NodeFacts.specDraft_store_with_cache_voter_view :
    ∀ (st : (Model.specDraft (V := V)).NS) (c : (Model.specDraft (V := V)).Cache) (E : DecoupledConsensusModel.Env V) (s : DecoupledConsensusModel.Slot),
      (Model.specDraft (V := V)).voter_view E ((Model.specDraft (V := V)).toHealing ((Model.specDraft (V := V)).store_with_cache st c).core).toFG.toSG.toGoldfishStore s =
        (Model.specDraft (V := V)).voter_view E ((Model.specDraft (V := V)).toHealing st.core).toFG.toSG.toGoldfishStore s := by
  intro st c E s
  rfl

theorem _root_.SpecDraftRecord.NodeFacts.specDraft_store_with_cache_voter_support_view :
    ∀ (st : (Model.specDraft (V := V)).NS) (c : (Model.specDraft (V := V)).Cache) (E : DecoupledConsensusModel.Env V) (s : DecoupledConsensusModel.Slot),
      (Model.specDraft (V := V)).voter_support_view E ((Model.specDraft (V := V)).toHealing ((Model.specDraft (V := V)).store_with_cache st c).core).toFG.toSG.toGoldfishStore s =
        (Model.specDraft (V := V)).voter_support_view E ((Model.specDraft (V := V)).toHealing st.core).toFG.toSG.toGoldfishStore s := by
  intro st c E s
  rfl

theorem _root_.SpecDraftRecord.NodeFacts.specDraft_store_with_cache_proposer_view :
    ∀ (st : (Model.specDraft (V := V)).NS) (c : (Model.specDraft (V := V)).Cache) (s : DecoupledConsensusModel.Slot),
      (Model.specDraft (V := V)).proposer_view ((Model.specDraft (V := V)).toHealing ((Model.specDraft (V := V)).store_with_cache st c).core).toFG.toSG.toGoldfishStore s =
        (Model.specDraft (V := V)).proposer_view ((Model.specDraft (V := V)).toHealing st.core).toFG.toSG.toGoldfishStore s := by
  intro st c s
  rfl

theorem _root_.SpecDraftRecord.NodeFacts.specDraft_store_with_cache_proposer_support_view :
    ∀ (st : (Model.specDraft (V := V)).NS) (c : (Model.specDraft (V := V)).Cache) (s : DecoupledConsensusModel.Slot),
      (Model.specDraft (V := V)).proposer_support_view ((Model.specDraft (V := V)).toHealing ((Model.specDraft (V := V)).store_with_cache st c).core).toFG.toSG.toGoldfishStore s =
        (Model.specDraft (V := V)).proposer_support_view ((Model.specDraft (V := V)).toHealing st.core).toFG.toSG.toGoldfishStore s := by
  intro st c s
  rfl

theorem _root_.SpecDraftRecord.NodeFacts.specDraft_store_with_cache_get_head_in_tree_with_layer :
    ∀ (st : (Model.specDraft (V := V)).NS) (c : (Model.specDraft (V := V)).Cache) (k : (Model.specDraft (V := V)).Contract) (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig) (T : Finset (Block V)) (W U : Finset (DecoupledConsensusModel.GoldfishVote V)) (s : DecoupledConsensusModel.Slot),
      (Model.specDraft (V := V)).get_head_in_tree_with_layer k E hc ((Model.specDraft (V := V)).toHealing ((Model.specDraft (V := V)).store_with_cache st c).core) T W U s =
        (Model.specDraft (V := V)).get_head_in_tree_with_layer k E hc ((Model.specDraft (V := V)).toHealing st.core) T W U s := by
  intro st c k E hc T W U s
  rfl

theorem _root_.SpecDraftRecord.NodeFacts.specDraft_store_with_cache_get_head_in_tree_with :
    ∀ (st : (Model.specDraft (V := V)).NS) (c : (Model.specDraft (V := V)).Cache) (k : (Model.specDraft (V := V)).Contract) (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig) (T : Finset (Block V)) (W U : Finset (DecoupledConsensusModel.GoldfishVote V)) (s : DecoupledConsensusModel.Slot),
      (Model.specDraft (V := V)).get_head_in_tree_with k E hc ((Model.specDraft (V := V)).store_with_cache st c).core T W U s =
        (Model.specDraft (V := V)).get_head_in_tree_with k E hc st.core T W U s := by
  intro st c k E hc T W U s
  rfl

theorem _root_.SpecDraftRecord.NodeFacts.specDraft_store_with_cache_grade2_block_with :
    ∀ (st : (Model.specDraft (V := V)).NS) (c : (Model.specDraft (V := V)).Cache) (k : (Model.specDraft (V := V)).Contract) (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig) (r : DecoupledConsensusModel.Round),
      (Model.specDraft (V := V)).grade2_block_with k E hc ((Model.specDraft (V := V)).toHealing ((Model.specDraft (V := V)).store_with_cache st c).core) r =
        (Model.specDraft (V := V)).grade2_block_with k E hc ((Model.specDraft (V := V)).toHealing st.core) r := by
  intro st c k E hc r
  rfl

theorem _root_.SpecDraftRecord.NodeFacts.specDraft_store_with_cache_get_sg_vote_with :
    ∀ (st : (Model.specDraft (V := V)).NS) (c : (Model.specDraft (V := V)).Cache) (k : (Model.specDraft (V := V)).Contract) (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig) (r : DecoupledConsensusModel.Round) (o : Option (Block V)),
      (Model.specDraft (V := V)).get_sg_vote_with k E hc ((Model.specDraft (V := V)).toHealing ((Model.specDraft (V := V)).store_with_cache st c).core) r o =
        (Model.specDraft (V := V)).get_sg_vote_with k E hc ((Model.specDraft (V := V)).toHealing st.core) r o := by
  intro st c k E hc r o
  rfl

theorem _root_.SpecDraftRecord.NodeFacts.specDraft_store_with_cache_onPhaseTick :
    ∀ (st : (Model.specDraft (V := V)).NS) (c : (Model.specDraft (V := V)).Cache) (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig) (t : DecoupledConsensusModel.Time) (c' : (Model.specDraft (V := V)).Cache),
      (Model.specDraft (V := V)).onPhaseTick E hc ((Model.specDraft (V := V)).toHealing ((Model.specDraft (V := V)).store_with_cache st c).core) t c' =
        (Model.specDraft (V := V)).onPhaseTick E hc ((Model.specDraft (V := V)).toHealing st.core) t c' := by
  intro st c E hc t c'
  rfl

theorem _root_.SpecDraftRecord.NodeFacts.specDraft_store_with_cache_readFrame :
    ∀ (st : (Model.specDraft (V := V)).NS) (c : (Model.specDraft (V := V)).Cache) (c' : (Model.specDraft (V := V)).Cache) (r : DecoupledConsensusModel.Round),
      (Model.specDraft (V := V)).readFrame c' ((Model.specDraft (V := V)).toHealing ((Model.specDraft (V := V)).store_with_cache st c).core) r =
        (Model.specDraft (V := V)).readFrame c' ((Model.specDraft (V := V)).toHealing st.core) r := by
  intro st c c' r
  rfl

theorem _root_.SpecDraftRecord.NodeFacts.specDraft_store_with_cache_frameGradeRead :
    ∀ (st : (Model.specDraft (V := V)).NS) (c : (Model.specDraft (V := V)).Cache) (c' : (Model.specDraft (V := V)).Cache) (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig) (r : DecoupledConsensusModel.Round),
      (Model.specDraft (V := V)).frameGradeRead c' E hc ((Model.specDraft (V := V)).toHealing ((Model.specDraft (V := V)).store_with_cache st c).core) r =
        (Model.specDraft (V := V)).frameGradeRead c' E hc ((Model.specDraft (V := V)).toHealing st.core) r := by
  intro st c c' E hc r
  rfl

theorem _root_.SpecDraftRecord.NodeFacts.specDraft_store_with_cache_currentSGVote :
    ∀ (st : (Model.specDraft (V := V)).NS) (c : (Model.specDraft (V := V)).Cache) (g : DecoupledConsensusModel.Protocol.GradeRead V),
      (Model.specDraft (V := V)).currentSGVote ((Model.specDraft (V := V)).toHealing ((Model.specDraft (V := V)).store_with_cache st c).core) g =
        (Model.specDraft (V := V)).currentSGVote ((Model.specDraft (V := V)).toHealing st.core) g := by
  intro st c g
  rfl

theorem _root_.SpecDraftRecord.NodeFacts.specDraft_store_with_cache_inWindow :
    ∀ (st : (Model.specDraft (V := V)).NS) (c : (Model.specDraft (V := V)).Cache) (hc : DecoupledConsensusModel.Protocol.HealConfig) (r : DecoupledConsensusModel.Round),
      (Model.specDraft (V := V)).inWindow hc ((Model.specDraft (V := V)).store_with_cache st c).core r =
        (Model.specDraft (V := V)).inWindow hc st.core r := by
  intro st c hc r
  rfl

theorem _root_.SpecDraftRecord.NodeFacts.specDraft_store_with_cache_store_pool :
    ∀ (st : (Model.specDraft (V := V)).NS) (c : (Model.specDraft (V := V)).Cache) (s : DecoupledConsensusModel.Slot),
      (Model.specDraft (V := V)).store_pool ((Model.specDraft (V := V)).store_with_cache st c).core s =
        (Model.specDraft (V := V)).store_pool st.core s := by
  intro st c s
  rfl

theorem _root_.SpecDraftRecord.NodeFacts.specDraft_store_with_cache_gradeView :
    ∀ (st : (Model.specDraft (V := V)).NS) (c : (Model.specDraft (V := V)).Cache),
      (Model.specDraft (V := V)).gradeView ((Model.specDraft (V := V)).toHealing ((Model.specDraft (V := V)).store_with_cache st c).core) =
        (Model.specDraft (V := V)).gradeView ((Model.specDraft (V := V)).toHealing st.core) := by
  intro st c
  rfl

end DecoupledConsensusModel.Sts.Record

namespace DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

open SpecDraftRecord
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

theorem _root_.SpecDraftRecord.StoreFacts.specDraft_rootFresh_of_distinct :
    ∀ (st : (Model.specDraft (V := V)).S) (B : Block V), (∀ C ∈ st.T, C.root = B.root → C = B) →
      (Model.specDraft (V := V)).rootFresh st B := by
  intro st B h₁
  exact h₁

end DecoupledConsensusModel.Sts.Record

namespace DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

open SpecDraftRecord
open DecoupledConsensusModel.Execution
open scoped DC

/-- The field `update_finality_F_of_conditions` of `HandlersFacts` at `Model.specDraft`: when `σ`
    names blocks of `st`'s tree, `st.F` is a strict ancestor of `σ.F`, `σ.F` is an ancestor of the
    merged justified block, and `σ.F` is in the viable tree, the finality update of `st` with `σ`
    has finalized block `σ.F`. -/
theorem _root_.SpecDraftRecord.HandlersFacts.specDraft_update_finality_F_of_conditions :
    ∀ (st : (Model.specDraft (V := V)).S) (σ : (Model.specDraft (V := V)).CS) (hσ : (Model.specDraft (V := V)).chainStateInTree st σ),
      Block.prec st.F σ.F = true →
      Block.preceq σ.F
        (if Block.preceq st.F σ.J && decide (Protocol.HeightId.mk st.h_j st.J.root <
            Protocol.HeightId.mk σ.h_j σ.J.root) then σ.J else st.J) = true →
      σ.F ∈ (Model.specDraft (V := V)).viable_tree st.σ st.F (max st.h_max σ.h) st.T →
      ((Model.specDraft (V := V)).update_finality st σ).F = σ.F := by
  intro st σ hσ h₁ h₂ h₃
  obtain ⟨hFσ, hJσ, hJst⟩ := hσ
  obtain ⟨-, hd, hpc, hF⟩ := st.property
  have hinj := hd.injOn_toProof
  have hstrict : st.val.F.ancestorStrict (Spec.Protocol.ChainState.F σ) = true := by
    change Block.prec st.val.F.toProof (Spec.Protocol.ChainState.F σ).toProof = true at h₁
    simp only [Block.prec, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h₁
    simp only [Spec.Block.ancestorStrict, Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not]
    refine ⟨fun h => h₁.1 (by rw [h]), ?_⟩
    rw [← Spec.Block.toProof_preceq_of_injOn st.val.T hinj hpc hF hFσ]
    exact h₁.2
  have hteq : (Block.preceq st.F σ.J && decide (Protocol.HeightId.mk st.h_j st.J.root <
      Protocol.HeightId.mk σ.h_j σ.J.root)) =
      (st.val.F.ancestorEq (Spec.Protocol.ChainState.J σ) &&
        decide (toLex (st.val.h_j, st.val.J.root) <
          toLex (Spec.Protocol.ChainState.h_j σ,
            (Spec.Protocol.ChainState.J σ).root))) := by
    show (Block.preceq st.val.F.toProof (Spec.Protocol.ChainState.J σ).toProof &&
      decide (Protocol.HeightId.mk st.val.h_j st.val.J.toProof.root <
        Protocol.HeightId.mk (Spec.Protocol.ChainState.h_j σ)
          (Spec.Protocol.ChainState.J σ).toProof.root)) = _
    rw [Spec.Block.toProof_preceq_of_injOn st.val.T hinj hpc hF hJσ,
      Spec.Block.toProof_root, Spec.Block.toProof_root]
    congr 1
    exact decide_eq_decide.2 (Spec.Protocol.heightId_mk_toProof_lt _ _ _ _)
  rw [hteq] at h₂
  have hanc : (Spec.Protocol.ChainState.F σ).ancestorEq
      (if (st.val.F.ancestorEq (Spec.Protocol.ChainState.J σ) &&
        decide (toLex (st.val.h_j, st.val.J.root) <
          toLex (Spec.Protocol.ChainState.h_j σ,
            (Spec.Protocol.ChainState.J σ).root)))
      then Spec.Protocol.ChainState.J σ else st.val.J) = true := by
    by_cases hc : (st.val.F.ancestorEq (Spec.Protocol.ChainState.J σ) &&
        decide (toLex (st.val.h_j, st.val.J.root) <
          toLex (Spec.Protocol.ChainState.h_j σ,
            (Spec.Protocol.ChainState.J σ).root))) = true
    · rw [if_pos hc] at h₂ ⊢
      change Block.preceq (Spec.Protocol.ChainState.F σ).toProof
        (Spec.Protocol.ChainState.J σ).toProof = true at h₂
      rwa [Spec.Block.toProof_preceq_of_injOn st.val.T hinj hpc hFσ hJσ] at h₂
    · rw [if_neg hc] at h₂ ⊢
      change Block.preceq (Spec.Protocol.ChainState.F σ).toProof st.val.J.toProof = true at h₂
      rwa [Spec.Block.toProof_preceq_of_injOn st.val.T hinj hpc hFσ hJst] at h₂
  have hviable : Spec.Protocol.ChainState.F σ ∈
      Spec.Protocol.viable_tree st.val.σ st.val.F
        (max st.val.h_max (Spec.Protocol.ChainState.h σ)) st.val.T := by
    rw [ForkChoiceFacts.specDraft_mem_viable_tree_iff] at h₃
    obtain ⟨⟨-, hFF⟩, W, hW, hσW, hh⟩ := h₃
    change W ∈ st.val.T.image Spec.Block.toProof at hW
    obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.1 hW
    simp only [Spec.Protocol.viable_tree, Spec.Protocol.finalized_descendants,
      Spec.Protocol.viable, Finset.mem_filter, decide_eq_true_eq]
    refine ⟨⟨hFσ, ?_⟩, Y, hY, ?_, ?_⟩
    · rw [← Spec.Block.toProof_preceq_of_injOn st.val.T hinj hpc hF hFσ]
      exact DecoupledConsensusModel.Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mpr hFF
    · show (Spec.Protocol.ChainState.F σ).ancestorEq Y = true
      rw [← Spec.Block.toProof_preceq_of_injOn st.val.T hinj hpc hFσ hY]
      exact DecoupledConsensusModel.Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mpr hσW
    · change max st.val.h_max (Spec.Protocol.ChainState.h σ) - 1 ≤
        (st.val.σ (st.val.blockOfImage Y.toProof)).h at hh
      rwa [Spec.Store.blockOfImage_toProof_of_mem st.val hd hY] at hh
  show (Handlers.updateFinalityWith st.val σ).F.toProof = (Spec.Protocol.ChainState.F σ).toProof
  unfold Handlers.updateFinalityWith
  simp only [Id.run, pure]
  split_ifs with h1 h2 h3
  · rfl
  · exfalso
    apply h2
    have hc : (st.val.F.ancestorEq (Spec.Protocol.ChainState.J σ) &&
        decide (toLex (st.val.h_j, st.val.J.root) <
          toLex (Spec.Protocol.ChainState.h_j σ,
            (Spec.Protocol.ChainState.J σ).root))) = true := h1
    rw [if_pos hc] at hanc
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨hstrict, hanc⟩, hviable⟩
  · rfl
  · exfalso
    apply h3
    have hc : ¬ (st.val.F.ancestorEq (Spec.Protocol.ChainState.J σ) &&
        decide (toLex (st.val.h_j, st.val.J.root) <
          toLex (Spec.Protocol.ChainState.h_j σ,
            (Spec.Protocol.ChainState.J σ).root))) = true := h1
    rw [if_neg hc] at hanc
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨hstrict, hanc⟩, hviable⟩

/-- The field `chainStateInTree_of_derived` of `HandlersFacts` at `Model.specDraft`: at a reached
    node store whose tree is the erasure of its bodies and holds `B`'s parent, if `unpacked` keeps
    every chain state that names blocks of `st`'s store part naming its own blocks, and writes at
    `B` the transition from its parent's chain state, then that chain state names blocks of
    `unpacked`. -/
theorem _root_.SpecDraftRecord.HandlersFacts.specDraft_chainStateInTree_of_derived :
    ∀ (E : Env V) (cfg : Protocol.HeightConfig) (st : (Model.specDraft (V := V)).NS) (B : NamedBlock V)
        (unpacked : (Model.specDraft (V := V)).S),
      (∀ D ∈ st.bodies, st.core.σ D.erase = (Model.specDraft (V := V)).derive_named E cfg D) →
      st.core.T = st.bodies.image NamedBlock.erase → B.parent ∈ st.bodies →
      (∀ σ, (Model.specDraft (V := V)).chainStateInTree st.core σ → (Model.specDraft (V := V)).chainStateInTree unpacked σ) →
      unpacked.σ B.erase = (Model.specDraft (V := V)).named_transition E cfg (st.core.σ B.erase.parent) B →
      ∀ (hn : (Model.specDraft (V := V)).reachedStore st),
      (Model.specDraft (V := V)).chainStateInTree unpacked (unpacked.σ B.erase) := by
  intro E cfg st B unpacked _h₁ h₂ h₃ h₄ h₅ hn
  obtain ⟨⟨hJT, hcs, -⟩, -, -⟩ := reachedStore_elim hn
  obtain ⟨-, hd, -, -⟩ := st.property
  rw [h₅]
  apply h₄
  have hpar : B.erase.parent ∈ st.val.T.image Spec.Block.toProof := by
    have hmem : B.parent.erase ∈ st.core.T := by
      rw [h₂]
      exact Finset.mem_image_of_mem _ h₃
    rw [DecoupledConsensusModel.Proofs.NamedWire.erase_parent]
    exact hmem
  obtain ⟨Y, hY, hYe⟩ := Finset.mem_image.1 hpar
  have hps : st.core.σ B.erase.parent = st.val.σ Y := by
    show st.val.σ (st.val.blockOfImage B.erase.parent) = st.val.σ Y
    rw [← hYe, Spec.Store.blockOfImage_toProof_of_mem st.val hd hY]
  rw [hps]
  obtain ⟨-, hTh, hJ, hF⟩ := hcs Y hY
  have key := SubtypeEqualities.state_transition_blocks
    (Spec.Config.toSpec E unreadHealConfig cfg) (Spec.Provisional.toSpec E)
    (st.val.σ Y) (Spec.Block.toSpecNamed B)
  obtain ⟨-, -, hJ', hF'⟩ := key
  show (Spec.Protocol.state_transition (Spec.Config.toSpec E unreadHealConfig cfg)
    (Spec.Provisional.toSpec E) (st.val.σ Y) (Spec.Block.toSpecNamed B)).F ∈ st.val.T ∧
    (Spec.Protocol.state_transition (Spec.Config.toSpec E unreadHealConfig cfg)
    (Spec.Provisional.toSpec E) (st.val.σ Y) (Spec.Block.toSpecNamed B)).J ∈ st.val.T ∧
    st.val.J ∈ st.val.T
  refine ⟨?_, ?_, hJT⟩
  · rcases hF' with e | e <;> rw [e]
    · exact hF
    · exact hJ
  · rcases hJ' with e | e <;> rw [e]
    · exact hJ
    · exact hTh

end DecoupledConsensusModel.Sts.Record
