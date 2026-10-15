import Model.Record.Wiring
import Model.Record.ModelSpellings
import Proofs.Claims.Spec2Claims.Claim13bK_ConfirmedSettleEarlier
import Proofs.Claims.Spec2Claims.Claim13bModel_domain
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.Adoption
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.Agreement
import Proofs.Vocabulary.Protocol.Handlers.SGArrival
import Proofs.Vocabulary.ModelProperties.Block_parent
import Proofs.Vocabulary.ModelProperties.update_finality
import Proofs.Vocabulary.Protocol.ChainState.DerivationGeometry
import Proofs.Vocabulary.Protocol.ValidatorClient.SlashableBound
import Proofs.Vocabulary.Protocol.Schedule.SlotInduction
import Proofs.Vocabulary.ModelProperties.NamedActions_proposal_with
import Proofs.Vocabulary.Protocol.ChainState.ProposalBridge
import Proofs.Claims.Spec2Claims.Claim13bStepKitConfirm
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.Confirmation
import Proofs.Vocabulary.Protocol.Grades.Main
import Proofs.Vocabulary.Protocol.Grades.ProposalParent
import Proofs.Vocabulary.Protocol.Handlers.Pool
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.HeightProgressClosurescoreEq
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.ProposalSnapshotBridge
import Proofs.Claims.Spec2Claims.Claim13bK_GradeOldHeads
import Proofs.Claims.Spec2Claims.Claim13bModel_goldfish_score

/-!
# The fork-choice facts

`ForkChoiceFacts` holds the facts about the fork-choice routines of a model `M : Model V` that hold
on arbitrary inputs. `ForkChoiceRunFacts` holds the facts about runs of these routines.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

/-- The facts about the fork-choice routines of the model `M`: the FG root, the filtered block tree,
    the SG root, the head, the walk `ghost`, the Goldfish fork choice, its score and eligibility
    test, the voter and proposer views and the vote count. -/
structure ForkChoiceFacts (M : Model V) : Prop where
  /-- If slot `k`'s committee has fewer members than twice its members in `Hon`, no committee member
      in `Hon` equivocates in `votes`, every committee member in `Hon` has a slot-`k` vote in
      `support` whose head resolves in `T` to a descendant of `B`, the votes are valid for slot `k`,
      `A` is an ancestor of `B`, and every block strictly after `A` on the way to `B` is in `tree`,
      then every outcome of `M.goldfish_fork_choice` started from `A` over `tree` is a descendant of
      `B`. -/
  goldfish_passes_cone : ∀ (E : Env V) (σ : Block V → M.CS) (h_max : Height) (T tree : Finset (Block V)) (cur : Slot) (votes support : Finset (GoldfishVote V)) (k : Slot) (Hon : Finset V) {A B : Block V} (hmaj : (E.committee k).card < 2 * ((E.committee k) ∩ Hon).card) (hcounted : votes ⊆ votes) (hsub : support ⊆ votes) (hno : ∀ x ∈ E.committee k, x ∈ Hon → M.equivocates votes x = false) (hvote : ∀ x ∈ E.committee k, x ∈ Hon → ∃ u ∈ support, u.val_index = x ∧ u.slot = k ∧ ∃ X : Block V, Block.find? T u.head = some X ∧ X.slot ≤ u.slot ∧ Block.Preceq B X) (hvalid : Protocol.VoteSetValid E k votes) (hAB : Block.Preceq A B) (hpath : ∀ C : Block V, Block.Preceq A C → C ≠ A → Block.Preceq C B → C ∈ tree) (X : Block V) (hX : M.goldfish_fork_choice E σ h_max T cur A tree votes support k ⇢ X), Block.Preceq B X
  /-- If slot `s`'s committee has fewer members than twice its members in `Hon`, `votes ⊆ late`, no
      committee member in `Hon` equivocates in `votes`, every committee member in `Hon` has a
      slot-`s` vote in `support` whose head resolves in `T` to a descendant of `B`, the late votes
      are valid for slot `s`, `A` is an ancestor of `B`, and every block strictly after `A` on the
      way to `B` is in `tree`, then every outcome of the walk `M.ghost` from `A` over `tree`, scored
      by an outcome of `M.goldfish_score` and admitting a block whose score is more than half of the
      late voters, is a descendant of `B`. -/
  ghost_passes_cone : ∀ (E : Env V) (T tree : Finset (Block V)) (votes support late : Finset (GoldfishVote V)) (s : Slot) (Hon : Finset V) {A B : Block V} (hmaj : (E.committee s).card < 2 * ((E.committee s) ∩ Hon).card) (hcounted : votes ⊆ late) (hsub : support ⊆ votes) (hno : ∀ x ∈ E.committee s, x ∈ Hon → M.equivocates votes x = false) (hvote : ∀ x ∈ E.committee s, x ∈ Hon → ∃ u ∈ support, u.val_index = x ∧ u.slot = s ∧ ∃ X : Block V, Block.find? T u.head = some X ∧ X.slot ≤ u.slot ∧ Block.Preceq B X) (hvalid : Protocol.VoteSetValid E s late) (hAB : Block.Preceq A B) (hpath : ∀ C : Block V, Block.Preceq A C → C ≠ A → Block.Preceq C B → C ∈ tree) (score : Block V → ℕ) (hscore : ∀ C, M.goldfish_score E T votes support s C ⇢ score C) (X : Block V) (hX : M.ghost A tree score (fun C => decide (M.voters_count E late s < 2 * score C)) ⇢ X), Block.Preceq B X
  /-- Two blocks that pass the strict-majority test at two views that see each other's counted votes
      are ancestor-comparable. -/
  eligible_compatible : ∀ {E : Env V} {Tv Tw : Finset (Block V)}
    {earlyv latev votesv earlyw latew votesw : Finset (GoldfishVote V)} {s : Slot}
    {C D : Block V}
    (hNv_early_late : earlyv ⊆ latev)
    (hNv_filtered : votesv = earlyv.filter (fun u => M.no_second_vote_in latev u = true))
    (hNw_early_late : earlyw ⊆ latew)
    (hNw_filtered : votesw = earlyw.filter (fun u => M.no_second_vote_in latew u = true))
    (hvw_transfer : ∀ u ∈ votesv, u ∈ latew ∨ M.equivocates latew u.val_index = true)
    (hvw_resolve : ∀ u ∈ votesv, ∀ B C : Block V,
      Block.find? Tv u.head = some B → Block.find? Tw u.head = some C → B = C)
    (hwv_transfer : ∀ u ∈ votesw, u ∈ latev ∨ M.equivocates latev u.val_index = true)
    (hwv_resolve : ∀ u ∈ votesw, ∀ B C : Block V,
      Block.find? Tw u.head = some B → Block.find? Tv u.head = some C → B = C)
    (gC : ℕ) (hgC : M.goldfish_score E Tv votesv votesv s C ⇢ gC)
    (hC : M.voters_count E latev s < 2 * gC)
    (gD : ℕ) (hgD : M.goldfish_score E Tw votesw votesw s D ⇢ gD)
    (hD : M.voters_count E latew s < 2 * gD),
    Block.compatible C D = true
  /-- Under the frame contract of a cache, the FG root of `st` is an ancestor of every outcome of
      the SG root `M.get_sg_root_with`, or that outcome itself. -/
  fg_root_preceq_get_sg_root_with_frame : ∀ (c : M.Cache) (E : Env V) (hc : Protocol.HealConfig) (st : M.HS) (r : Round) (R : Block V), M.get_sg_root_with (M.frameContract c) E hc st r ⇢ R → Block.Preceq (M.get_fg_root st.toFG) R
  /-- A vote in the slot-`(s - 1)` pool of `gst` stamped before the view freeze of slot `s - 1` is
      in every outcome of the slot-`s` support view `M.voter_support_view E gst s`. -/
  Optimistic_mem_voter_support_view_of_pool : ∀ (E : Env V) (gst : M.GS) (s : Slot)
    {u : GoldfishVote V} (τ : TimestampMap (GoldfishVote V)), M.gs_tau gst ⇢ τ →
    u ∈ beforeCutoff τ (M.view_freeze E (s - 1)) (M.gs_pool gst (s - 1)) →
    ∀ Y : Finset (GoldfishVote V), M.voter_support_view E gst s ⇢ Y → u ∈ Y
  /-- For every outcome `R` of the SG root, the head `M.get_head_in_tree_with` under `contract` at
      `st` can return a block `X` exactly when the Goldfish fork choice started at `R`, over the
      same tree, votes and slot, can return `X`. -/
  get_head_in_tree_split_with : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (st : M.HS) (tree : Finset (Block V)) (votes support_votes : Finset (GoldfishVote V)) (k : Slot)
    (R : Block V), M.get_sg_root_with contract E hc st ((M.round_of hc st.s)) ⇢ R →
    ∀ X : Block V, M.get_head_in_tree_with_layer contract E hc st tree votes support_votes k ⇢ X ↔
      M.goldfish_fork_choice E st.σ st.h_max st.T st.s R tree votes support_votes k ⇢ X
  /-- The voter's filtered block tree is the filtered block tree, from `st`'s FG view, over the
      blocks the voter has processed. -/
  voter_candidate_tree_eq_protocol_voter_filtered_block_tree : ∀ (E : Env V) (st : M.S)
    (P : Finset (Block V)),
    M.voter_processed_block_tree E (M.toHealing st).toFG.toSG.toGoldfishStore (M.toHealing st).s ⇢ P →
    ∀ X : Finset (Block V), M.voter_filtered_block_tree E st st.s ⇢ X →
    M.get_filtered_block_tree_from (M.toHealing st).toFG P = X
  /-- A confirmation's supporters carry to the target view: if the source score of `B` is more than
      half of the source voters and the votes relayed between the two views agree as the hypotheses
      state, then the source supporters of `B` are a subset of the target supporters, which are more
      than half of the target voters. -/
  confirmation_adoption : ∀ {E : Env V} {sourceTree targetTree : Finset (Block V)}
    {sourceEarly sourceLate sourceVotes targetVotes targetSupport : Finset (GoldfishVote V)}
    {s : Slot} {B : Block V}
    (hN_early_late : sourceEarly ⊆ sourceLate)
    (hN_filtered : sourceVotes = sourceEarly.filter (fun u => M.no_second_vote_in sourceLate u = true))
    (tS : GoldfishVote V → Bool) (htS : ∀ u, M.targets_under sourceTree B u ⇢ tS u)
    (tT : GoldfishVote V → Bool) (htT : ∀ u, M.targets_under targetTree B u ⇢ tT u)
    (hT_forward : ∀ u ∈ sourceVotes, tS u = true →
      (u ∈ targetSupport ∧ tT u = true) ∨
        M.equivocates targetVotes u.val_index = true)
    (hT_backward : ∀ u ∈ targetVotes, u ∈ sourceLate ∨ M.equivocates sourceLate u.val_index = true)
    (g : ℕ) (hg : M.goldfish_score E sourceTree sourceVotes sourceVotes s B ⇢ g)
    (heligible : M.voters_count E sourceLate s < 2 * g)
    (sS : Finset V) (hsS : M.raw_supporters sourceTree sourceVotes sourceVotes s B ⇢ sS)
    (sT : Finset V) (hsT : M.raw_supporters targetTree targetVotes targetSupport s B ⇢ sT),
    sS ⊆ sT ∧ M.voters_count E targetVotes s < 2 * sT.card
  /-- If the Goldfish tree of `st` contains genesis and the parent of each of its non-genesis
      blocks, `st.F` is an ancestor of `st.J`, the FG root of `st` is an ancestor of `P`, `W` is in
      `st.T` with chain-state height at least `st.h_max - 1`, and `D` is a descendant of `P` and an
      ancestor of `W`, then `D` is in the filtered block tree of `st`. -/
  canonicalConeSegment_mem_filtered_of_root_preceq : ∀ {st : M.S} (hpc : Block.genesis ∈ (M.toHealing st).toFG.toSG.toGoldfishStore.T ∧ ∀ B ∈ (M.toHealing st).toFG.toSG.toGoldfishStore.T, B.parent? = none ∨ B.parent ∈ (M.toHealing st).toFG.toSG.toGoldfishStore.T) (hFJ : Block.Preceq st.F st.J) {P W D : Block V} (hrootP : Block.Preceq (M.get_fg_root (M.toHealing st).toFG) P) (hWT : W ∈ st.T) (hheight : st.h_max - 1 ≤ (st.σ W).h) (hPD : Block.Preceq P D) (hDW : Block.Preceq D W), D ∈ M.get_filtered_block_tree (M.toHealing st).toFG
  /-- If `support ⊆ votes`, an outcome of `M.raw_supporters T votes support s B` has more than half
      of the voters, `A` and `B` are compatible, and every block strictly after `A` on the way to
      `B` is in `tree`, then `B` is an ancestor of every outcome of the Goldfish fork choice from
      `A`, or that outcome itself. -/
  goldfish_fork_choice_captures_supporter_majority : ∀ (E : Env V) (σ : Block V → M.CS)
    (h_max : Height) (T tree : Finset (Block V)) (cur : Slot)
    (votes support : Finset (GoldfishVote V)) (s : Slot) {A B : Block V}
    (hsub : support ⊆ votes)
    (sup : Finset V) (hsup : M.raw_supporters T votes support s B ⇢ sup)
    (hmajority : M.voters_count E votes s < 2 * sup.card)
    (hcompatible : Block.compatible A B = true)
    (hpath : Block.Preceq A B → ∀ C : Block V, Block.Preceq A C → C ≠ A → Block.Preceq C B → C ∈ tree)
    (X : Block V) (hX : M.goldfish_fork_choice E σ h_max T cur A tree votes support s ⇢ X),
    Block.Preceq B X
  /-- For every outcome `R` of `M.raw_supporters T votes support_votes s B`, `x` is in `R` exactly
      when `x` does not equivocate in `votes` and has a slot-`s` vote in `support_votes` whose
      target test against `B` answers `true`. -/
  mem_supporters_iff : ∀ {_E : Env V} {T : Finset (Block V)} {votes support_votes : Finset (GoldfishVote V)} {s : Slot} {B : Block V} {x : V} (R : Finset V) (hR : M.raw_supporters T votes support_votes s B ⇢ R) (t : GoldfishVote V → Bool) (ht : ∀ u, M.targets_under T B u ⇢ t u), x ∈ R ↔ M.equivocates votes x = false ∧ ∃ u ∈ M.votes_by support_votes x, u.slot = s ∧ t u = true
  /-- The FG root of the healing view does not read the store's time or slot. -/
  get_fg_root_toHealing_clock : ∀ (st : M.S) (t : Time) (s : Slot),
    M.get_fg_root (M.store_with_t_s st t s).toHealing.toFG = M.get_fg_root st.toHealing.toFG
  /-- The filtered block tree of the healing view does not read the store's time or slot. -/
  get_filtered_block_tree_toHealing_clock : ∀ (st : M.S) (t : Time) (s : Slot),
    M.get_filtered_block_tree (M.store_with_t_s st t s).toHealing.toFG =
      M.get_filtered_block_tree st.toHealing.toFG
  /-- `B` is in the viable tree of `σ`, `F`, `h_max` and `T` exactly when `B` is in `T`, `F ⪯ B`,
      and some `W` in `T` with `B ⪯ W` has chain-state height at least `h_max - 1`. -/
  mem_viable_tree_iff : ∀ (σ : Block V → M.CS) (F : Block V) (h_max : Height)
    (T : Finset (Block V)) (B : Block V),
    B ∈ M.viable_tree σ F h_max T ↔
      (B ∈ T ∧ Block.Preceq F B) ∧ ∃ W ∈ T, Block.Preceq B W ∧ h_max - 1 ≤ (σ W).h
  /-- The filtered block tree of the FG store `st` over the set `blocks` is a subset of `blocks`. -/
  get_filtered_block_tree_from_subset : ∀ (st : M.FGS) (blocks : Finset (Block V)),
    M.get_filtered_block_tree_from st blocks ⊆ blocks
  /-- A step of the walk from `H` that returns `some C` lands on an eligible child `C` of `H` that
      is in the tree. -/
  ghost_step_child : ∀ {tree : Finset (Block V)} {score : Block V → ℕ}
    {eligible : Block V → Bool} {H C : Block V} (o : Option (Block V)),
    M.ghost_step tree score eligible H ⇢ o → o = some C →
      C ∈ tree ∧ C.parent? = some H ∧ eligible C = true
  /-- A walk of the source tree that ends at `H` carries to the target tree through a block `bridge`
      between the source anchor and `H`: under the hypotheses relating the two trees' steps,
      eligibility and scores, the target walk also ends at `H`. -/
  ghost_transport_via_bridge_of_target_passes : ∀ {sourceTree targetTree : Finset (Block V)}
    {sourceScore targetScore : Block V → ℕ} {sourceEligible targetEligible : Block V → Bool}
    {sourceAnchor targetAnchor bridge H : Block V},
    DecoupledConsensusModel.Execution.RootInjectiveBelow sourceTree →
    DecoupledConsensusModel.Execution.RootInjectiveBelow targetTree →
    ∀ G : Block V, M.ghost sourceAnchor sourceTree sourceScore sourceEligible ⇢ G → G = H →
    Block.Preceq sourceAnchor bridge → Block.Preceq bridge H → Block.Preceq targetAnchor H →
    (∀ (C : Block V), Block.Preceq targetAnchor C → C ≠ targetAnchor → Block.Preceq C H →
      C ∈ targetTree) →
    ∀ G' : Block V, M.ghost targetAnchor targetTree targetScore targetEligible ⇢ G' →
    Block.Preceq bridge G' →
    ∀ step : Block V → Option (Block V),
    (∀ X, M.ghost_step sourceTree sourceScore sourceEligible X ⇢ step X) →
    (∀ (X C : Block V), Block.Preceq bridge X → Block.Preceq X H → X ≠ H →
      step X = some C → Block.Preceq C H →
      C ∈ targetTree ∧ targetEligible C = true) →
    (∀ (X C : Block V), Block.Preceq bridge X → Block.Preceq X H → C ∈ targetTree →
      C.parent? = some X → targetEligible C = true →
      C ∈ sourceTree ∧ sourceEligible C = true) →
    (∀ C ∈ sourceTree, C ∈ targetTree → targetScore C = sourceScore C) →
    (∀ C ∈ targetTree, C.parent? = some H → targetEligible C = false) ∧ G' = H
  /-- The FG root does not read the store's time or slot. -/
  get_fg_root_set_clock_slot : ∀ (st : M.S) (t : Int) (s : Slot),
    M.get_fg_root (M.store_with_t_s st t s).toHealing.toFG = M.get_fg_root st.toHealing.toFG
  /-- The filtered block tree does not read the store's time or slot. -/
  get_filtered_block_tree_set_clock_slot : ∀ (st : M.S) (t : Int) (s : Slot),
    M.get_filtered_block_tree (M.store_with_t_s st t s).toHealing.toFG =
      M.get_filtered_block_tree st.toHealing.toFG
  /-- If `C` is in `blocks`, `st.F ⪯ C`, some `W` in `blocks` with `C ⪯ W` has chain-state height at
      least `st.h_max - 1`, and the FG root of `st` is an ancestor of `C` or `C` itself, then `C` is
      in the filtered block tree of `st` over `blocks`. -/
  mem_get_filtered_block_tree_from_of_parts_explicit : ∀ (st : M.FGS) {blocks : Finset (Block V)}
    {C W : Block V}, C ∈ blocks → Block.Preceq st.F C → W ∈ blocks → Block.Preceq C W →
    st.h_max - 1 ≤ (st.σ W).h → Block.Preceq (M.get_fg_root st) C →
    C ∈ M.get_filtered_block_tree_from st blocks
  /-- A block `B` of the filtered block tree of `st` over `blocks` is in `blocks`, has `st.F ⪯ B`,
      has a descendant or itself `W` in `blocks` with chain-state height at least `st.h_max - 1`,
      and has the FG root of `st` as an ancestor or itself. -/
  mem_get_filtered_block_tree_from_parts : ∀ {st : M.FGS} {blocks : Finset (Block V)}
    {B : Block V}, B ∈ M.get_filtered_block_tree_from st blocks →
    B ∈ blocks ∧ Block.Preceq st.F B ∧ (∃ W ∈ blocks, Block.Preceq B W ∧ st.h_max - 1 ≤ (st.σ W).h) ∧
      Block.Preceq (M.get_fg_root st) B
  /-- A slot-`s` vote in the pool of `gs` stamped before slot `s`'s view freeze is in every outcome
      of the voter view `M.voter_view E gs (s + 1)`. -/
  mem_voter_view_of_pool : ∀ (E : Env V) (gs : M.GS) (s : Slot) {u : GoldfishVote V},
    u ∈ gs.pool s → ∀ {τ : Stamp}, gs.timestamp_vote u = some τ →
    τ < ((M.view_freeze E s : Int) : Stamp) →
    ∀ Y : Finset (GoldfishVote V), M.voter_view E gs (s + 1) ⇢ Y → u ∈ Y
  /-- `M.no_second_vote_in late vote` is `true` exactly when every vote of `late` is `vote` itself
      or has another signer. -/
  no_second_vote_in_eq_true_iff : ∀ (late : Finset (GoldfishVote V)) (vote : GoldfishVote V),
    M.no_second_vote_in late vote = true ↔ ∀ u ∈ late, u = vote ∨ u.val_index ≠ vote.val_index
  /-- If every vote of `late` is `vote` itself or has another signer, then
      `M.no_second_vote_in late vote` is `true`. -/
  no_second_vote_in_of_forall : ∀ {late : Finset (GoldfishVote V)} {vote : GoldfishVote V},
    (∀ u ∈ late, u = vote ∨ u.val_index ≠ vote.val_index) → M.no_second_vote_in late vote = true
  /-- A block `C` of the filtered block tree of `st` over `blocks` is in `blocks`, has `st.F ⪯ C`,
      has a descendant or itself `W` in `blocks` with chain-state height at least `st.h_max - 1`,
      and has the FG root of `st` as an ancestor or itself. -/
  parts_of_mem_get_filtered_block_tree_from : ∀ {st : M.FGS} {blocks : Finset (Block V)}
    {C : Block V}, C ∈ M.get_filtered_block_tree_from st blocks →
    ((C ∈ blocks ∧ Block.Preceq st.F C) ∧ ∃ W ∈ blocks, Block.Preceq C W ∧ st.h_max - 1 ≤ (st.σ W).h) ∧
      Block.Preceq (M.get_fg_root st) C
  /-- The slot-`k` proposer view does not read the store's time or slot. -/
  proposer_view_set_clock_slot : ∀ (st : M.S) (t : Int) (s k : Slot),
    M.proposer_view (M.store_with_t_s st t s).toHealing.toFG.toSG.toGoldfishStore k =
      M.proposer_view st.toHealing.toFG.toSG.toGoldfishStore k
  /-- The slot-`k` voter view does not read the store's time or slot. -/
  voter_view_set_clock_slot : ∀ (E : Env V) (st : M.S) (t : Int) (s k : Slot) (Y : Finset (GoldfishVote V)),
    M.voter_view E (M.store_with_t_s st t s).toHealing.toFG.toSG.toGoldfishStore k ⇢ Y ↔
      M.voter_view E st.toHealing.toFG.toSG.toGoldfishStore k ⇢ Y
  /-- Under the grade contract of a cache, the FG root of `st` is an ancestor of every outcome of
      the SG root `M.get_sg_root_with`, or that outcome itself. -/
  fg_root_Preceq_get_sg_root_with_gradeContract : ∀ (c : M.Cache) (E : Env V) (hc : Protocol.HealConfig) (st : M.HS) (r : Round) (R : Block V), M.get_sg_root_with (M.gradeContract c) E hc st r ⇢ R → Block.Preceq (M.get_fg_root st.toFG) R
  /-- Every block of the filtered block tree of `st` is a descendant of `st.F` or `st.F` itself. -/
  finalized_preceq_of_mem_get_filtered_block_tree : ∀ {st : M.FGS} {B : Block V} (hB : B ∈ M.get_filtered_block_tree st), Block.Preceq st.F B
  /-- Two stores with the same `F`, `J`, `h_j` and `h_max` have the same FG root. -/
  get_fg_root_toHealing_eq_of_fields : ∀ {st st' : M.S} (hF : st.F = st'.F) (hJ : st.J = st'.J) (hhj : st.h_j = st'.h_j) (hmax : st.h_max = st'.h_max), M.get_fg_root (M.toHealing st).toFG = M.get_fg_root (M.toHealing st').toFG
  /-- When `st.h_max = st.h_j + 1`, the FG root of `st` is `st.J`. -/
  get_fg_root_toHealing_of_eq : ∀ (st : M.S) (h : st.h_max = st.h_j + 1), M.get_fg_root (M.toHealing st).toFG = st.J
  /-- When `st.h_max ≠ st.h_j + 1`, the FG root of `st` is `st.F`. -/
  get_fg_root_toHealing_of_ne : ∀ (st : M.S) (h : ¬ st.h_max = st.h_j + 1), M.get_fg_root (M.toHealing st).toFG = st.F
  /-- If the anchor of the contract's grade read at the store's round is in `T` and the candidate
      tree is a subset of `T`, every outcome of the head `M.get_head_in_tree_with_layer` over that
      tree is in `T`. -/
  ModelProperties_get_head_in_tree_with_layer_mem : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (st : M.HS) (tree : Finset (Block V)) (votes support : Finset (GoldfishVote V)) (k : Slot) {T : Finset (Block V)} (G : GradeRead V) (hG : contract.read E hc st ((M.round_of hc st.toFG.toSG.toGoldfishStore.s)) ⇢ G) (hanchor : G.anchor ∈ T) (htree : tree ⊆ T) (X : Block V) (hX : M.get_head_in_tree_with_layer contract E hc st tree votes support k ⇢ X), X ∈ T
  /-- If an outcome of the SG root under `contract` at `st`'s round is in `st`'s filtered block
      tree, every outcome of the head `M.get_head_with contract E hc st votes support k` is in that
      tree. -/
  get_head_with_mem_filtered : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (st : M.HS) (votes support : Finset (GoldfishVote V)) (k : Slot) (R : Block V) (hR : M.get_sg_root_with contract E hc st ((M.round_of hc st.toFG.toSG.toGoldfishStore.s)) ⇢ R) (hanchor : R ∈
    M.get_filtered_block_tree st.toFG) (X : Block V) (hX : M.get_head_with contract E hc st votes support k ⇢ X), X ∈
    M.get_filtered_block_tree st.toFG
  /-- Every outcome of the SG root `M.get_sg_root_with contract E hc st r` is the anchor of every
      outcome of the grade read `contract.read E hc st r`. -/
  get_sg_root_with_eq_read_anchor : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (st : M.HS) (r : Round) (G : GradeRead V), contract.read E hc st r ⇢ G → ∀ R : Block V, M.get_sg_root_with contract E hc st r ⇢ R → R = G.anchor
  /-- Under the grade contract of a cache, if the FG root of `st` is in `st`'s filtered block tree,
      every outcome of the SG root `M.get_sg_root_with` is in that tree. -/
  get_sg_root_with_gradeContract_mem_filtered : ∀ (c : M.Cache) (E : Env V) (hc : Protocol.HealConfig) (st : M.HS) (r : Round) (hroot : M.get_fg_root st.toFG ∈ M.get_filtered_block_tree st.toFG) (R : Block V) (hR : M.get_sg_root_with (M.gradeContract c) E hc st r ⇢ R), R ∈
    M.get_filtered_block_tree st.toFG
  /-- If `nd`'s validator is in the committee of slot `s` of `st`'s core store, the vote of every
      outcome of its Goldfish vote duty is its slot-`s` vote for the root of the head that the fork
      choice under `contract` returns over the voter's filtered block tree and vote views. -/
  goldfish_vote_with_snd_of_mem_committee : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : M.NS) (hcom : nd.val_index ∈ E.committee st.core.s)
    (D : M.NS × Option (GoldfishVote V)) (hD : M.duties_goldfish_vote_with contract E hc nd st ⇢ D)
    (tree : Finset (Block V)) (htree : M.voter_filtered_block_tree E st.core st.core.s ⇢ tree)
    (votes : Finset (GoldfishVote V)) (hvotes : M.voter_view E (M.toHealing st.core).toFG.toSG.toGoldfishStore st.core.s ⇢ votes)
    (support : Finset (GoldfishVote V)) (hsupport : M.voter_support_view E (M.toHealing st.core).toFG.toSG.toGoldfishStore st.core.s ⇢ support)
    (H : Block V) (hH : M.get_head_in_tree_with_layer contract E hc (M.toHealing st.core) tree votes support (st.core.s - 1) ⇢ H),
    D.2 = some ⟨nd.val_index, st.core.s, H.root⟩
  /-- The anchor of the contract's grade read at the store's round is an ancestor of every outcome
      of the head `M.get_head_in_tree_with_layer`, or that outcome itself. -/
  read_anchor_preceq_get_head_in_tree_with_layer : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (st : M.HS) (tree : Finset (Block V)) (votes support : Finset (GoldfishVote V)) (k : Slot) (G : GradeRead V) (hG : contract.read E hc st ((M.round_of hc st.toFG.toSG.toGoldfishStore.s)) ⇢ G) (X : Block V) (hX : M.get_head_in_tree_with_layer contract E hc st tree votes support k ⇢ X), Block.Preceq G.anchor X
  /-- If `r − eta ≤ k` and `k < r`, then `k` is in `M.latest_window eta r`. -/
  mem_latest_window : ∀ {eta r k : Round} (hlo : r - eta ≤ k) (hhi : k < r), k ∈ M.latest_window eta r
  /-- Every block `B` of the filtered block tree of `st` has `st.F ⪯ B`. -/
  q10_filtered_F : ∀ {st : M.FGS} {B : Block V} (h : B ∈ M.get_filtered_block_tree st), Block.Preceq st.F B
  /-- A round `k` of `M.latest_window eta r` has `r − eta ≤ k` and `k < r`. -/
  window_bounds : ∀ {eta r k : Nat} (hk : k ∈ M.latest_window eta r), r - eta ≤ k ∧ k < r
  /-- An outcome `G` of the walk `M.ghost A tree score eligible` is `B` when `A` and `B` are
      compatible, `B ⪯ G` whenever `A ⪯ B`, `A = B` whenever `B ⪯ A`, and no block of `tree` other
      than `B` is a descendant of `B`. -/
  ghost_eq_of_compatible_anchor_and_terminal : ∀ {tree : Finset (Block V)} {score : Block V → Nat} {eligible : Block V → Bool} {A B : Block V} (G : Block V) (hG : M.ghost A tree score eligible ⇢ G) (hcompat : Block.compatible A B = true) (hforward : Block.Preceq A B →
    Block.Preceq B G) (hanchorTerminal : Block.Preceq B A → A = B) (htreeTerminal : ∀ X ∈ tree, Block.Preceq B X → X = B), G = B
  /-- If `B` is an eligible child of `H` not in `tree`, no block of `tree` with parent `H` is
      eligible, no block of `tree` has parent `B`, and the walk `M.ghost A tree score eligible` ends
      at `H`, then the walk over `insert B tree` ends at `B`. -/
  ghost_insert_eq : ∀ {tree : Finset (Block V)} {score : Block V → Nat} {eligible : Block V → Bool} {A B H : Block V} (hpar : B.parent? = some H) (helig : eligible B = true) (hnotin : B ∉ tree) (hstop : ∀ C ∈ tree, C.parent? = some H → eligible C = false) (hfresh : ∀ C ∈ tree, C.parent? ≠ some B) (G : Block V) (hG : M.ghost A tree score eligible ⇢ G) (hwalk : G = H) (G' : Block V) (hG' : M.ghost A (insert B tree) score eligible ⇢ G'), G' = B
  /-- An outcome of `M.goldfish_eligible` for `B` is `true` exactly when the chain-state height of
      `B`'s parent is less than `h_max − 1`, or the voter count is less than twice `B`'s Goldfish
      score, or `B`'s slot is `cur`. -/
  goldfish_eligible_iff : ∀ (E : Env V) (σ : Block V → M.CS) (h_max : Height) (T : Finset (Block V)) (cur : Slot) (votes support_votes : Finset (GoldfishVote V)) (s : Slot) (B : Block V) (e : Bool) (he : M.goldfish_eligible E σ h_max T cur votes support_votes s B ⇢ e) (g : ℕ) (hg : M.goldfish_score E T votes support_votes s B ⇢ g), e = true ↔
    ((σ B.parent).h < h_max - 1 ∨
    M.voters_count E votes s <
    2 * g ∨
    B.slot = cur)
  /-- The filtered block tree of `st` is a subset of `st`'s processed block tree. -/
  get_filtered_block_tree_subset : ∀ (st : M.FGS), M.get_filtered_block_tree st ⊆ st.toSG.toGoldfishStore.T
  /-- Every outcome of the walk `M.ghost anchor tree score eligible` is `anchor` or a block of
      `tree`. -/
  ghost_mem : ∀ (anchor : Block V) (tree : Finset (Block V)) (score : Block V → Nat) (eligible : Block V → Bool) (G : Block V), M.ghost anchor tree score eligible ⇢ G → G = anchor ∨
    G ∈ tree
  /-- If `st.F ⪯ st.J`, `P` is in `st`'s filtered block tree, `R` is in `st`'s processed block tree
      with `R ⪯ P`, and the FG root of `st` is an ancestor of `R` or `R` itself, then `R` is in the
      filtered block tree. -/
  mem_filtered_of_preceq : ∀ {st : M.FGS} {P R : Block V} (hFJ : Block.preceq st.F st.J = true) (hP : P ∈ M.get_filtered_block_tree st) (hRT : R ∈ st.toSG.toGoldfishStore.T) (hRP : Block.preceq R P = true) (hroot : Block.preceq (M.get_fg_root st) R = true), R ∈ M.get_filtered_block_tree st
  /-- If `st.F ⪯ st.J`, then `st.F` is an ancestor of the FG root of `st`, or that root itself. -/
  preceq_get_fg_root_of_F : ∀ {st : M.FGS} (hFJ : Block.preceq st.F st.J = true), Block.preceq st.F (M.get_fg_root st) = true
  /-- The FG root of `st` is an ancestor of every block of `st`'s filtered block tree, or that block
      itself. -/
  preceq_get_fg_root_of_mem_filtered : ∀ {st : M.FGS} {B : Block V} (hB : B ∈ M.get_filtered_block_tree st), Block.preceq (M.get_fg_root st) B = true
  /-- If `B` is in the tree of `st`, has slot `s`, and every Goldfish vote included in `B` is of the
      slot before `B`'s, then those votes are in every outcome of the slot-`s` voter view
      `M.voter_view E st s`. -/
  carried_raw_subset_voter_view : ∀ (E : Env V) (st : M.GS) {s : Slot} {B : Block V} (hB : B ∈ st.T) (hBslot : B.slot = s) (hslots : ∀ u ∈ B.gf_votes, u.slot + 1 = B.slot) (Y : Finset (GoldfishVote V)) (hY : M.voter_view E st s ⇢ Y), B.gf_votes.toFinset ⊆ Y
  /-- Every outcome of the walk `M.ghost anchor tree score eligible` is `anchor` or a block that
      passes `eligible`. -/
  ghost_eligible : ∀ (anchor : Block V) (tree : Finset (Block V)) (score : Block V → Nat) (eligible : Block V → Bool) (G : Block V), M.ghost anchor tree score eligible ⇢ G → G = anchor ∨
    eligible G = true
  /-- `anchor` is an ancestor of every outcome of the walk `M.ghost anchor tree score eligible`, or
      that outcome itself. -/
  ghost_preceq : ∀ (anchor : Block V) (tree : Finset (Block V)) (score : Block V → Nat) (eligible : Block V → Bool) (G : Block V), M.ghost anchor tree score eligible ⇢ G → Block.Preceq anchor G
  /-- If `1 ≤ etaSG` and `0 < r`, then `r − 1` is in `M.latest_window etaSG r`. -/
  pred_mem_latest_window : ∀ (etaSG r : Round) (heta : 1 ≤ etaSG) (hr : 0 < r), r - 1 ∈ M.latest_window etaSG r
  /-- An outcome of the supporter test `M.targets_under T B u` is `true` exactly when `u`'s head
      resolves in `T` to a block `B'` of slot at most `u`'s slot with `B ⪯ B'`. -/
  targets_under_iff : ∀ {T : Finset (Block V)} {B : Block V} {u : GoldfishVote V} (b : Bool), M.targets_under T B u ⇢ b → (b = true ↔
    ∃ B', Block.find? T u.head = some B' ∧ B'.slot ≤ u.slot ∧
    Block.preceq B B' = true)
  /-- If every support vote of every block of `st`'s tree is among that block's Goldfish votes,
      every outcome of the support view `M.voter_support_view E st s` is a subset of every outcome
      of the voter view `M.voter_view E st s`. -/
  voter_support_view_subset : ∀ (E : Env V) (st : M.GS) (s : Slot) (hsub : ∀ B ∈ st.T, ∀ u ∈ B.gf_support_votes, u ∈ B.gf_votes) (Y : Finset (GoldfishVote V)) (hY : M.voter_support_view E st s ⇢ Y) (Z : Finset (GoldfishVote V)) (hZ : M.voter_view E st s ⇢ Z), Y ⊆ Z
  /-- If `late` satisfies `Protocol.VoteSetValid E s late`, the voter count
      `M.voters_count E late s` is at most the size of slot `s`'s committee. -/
  voters_count_le_committee : ∀ (E : Env V) (late : Finset (GoldfishVote V)) (s : Slot) (hvalid : Protocol.VoteSetValid E s late), M.voters_count E late s ≤ (E.committee s).card
  /-- If every validator of `X` participates in `votes`, then `X` has at most
      `M.voters_count E votes s` members. -/
  card_le_voters_count_of_participates : ∀ (E : Env V) (votes : Finset (GoldfishVote V)) (s : Slot) (X : Finset V) (h : ∀ x ∈ X, M.participates votes x = true), X.card ≤ M.voters_count E votes s
  /-- Under the grade contract of a cache, the FG root of `st` is an ancestor of every outcome of
      the head `M.get_head_in_tree_with_layer`, or that outcome itself. -/
  fgRoot_Preceq_get_head_in_tree_with_layer_gradeContract : ∀ (c : M.Cache) (E : Env V) (hc : Protocol.HealConfig) (st : M.HS) (tree : Finset (Block V)) (votes support : Finset (GoldfishVote V)) (k : Slot) (X : Block V), M.get_head_in_tree_with_layer (M.gradeContract c) E hc st tree votes
    support k ⇢ X → Block.Preceq (M.get_fg_root st.toFG) X
  /-- The FG root of `stH` is compatible with `T` when `stH.F ⪯ T` and, if `h_max = h_j + 1`, the
      justified block is compatible with `T`. -/
  fgRoot_compatible_ofJustifiedBranch : ∀ {stH : M.HS} {T : Block V} (hF : Block.Preceq stH.toFG.F T) (hJ : stH.toFG.h_max = stH.toFG.h_j + 1 → Block.compatible stH.toFG.J T = true), Block.compatible (M.get_fg_root stH.toFG) T = true
  /-- The FG root of `stH` is compatible with `B` when the finalized block is and, if
      `h_max = h_j + 1`, the justified block is. -/
  fgRoot_compatible_of_compatible : ∀ {stH : M.HS} {B : Block V} (hF : Block.compatible stH.toFG.F B = true) (hJ : stH.toFG.h_max = stH.toFG.h_j + 1 → Block.compatible stH.toFG.J B = true), Block.compatible (M.get_fg_root stH.toFG) B = true
  /-- The FG root of `stH` is an ancestor of `T` when both the finalized and the justified block
      are. -/
  fgRoot_preceq : ∀ {stH : M.HS} {T : Block V} (hF : Block.Preceq stH.toFG.F T) (hJ : Block.Preceq stH.toFG.J T), Block.Preceq (M.get_fg_root stH.toFG) T
  /-- The FG root of `stH` is an ancestor of `T` when the finalized block is and, if
      `h_max = h_j + 1`, the justified block is. -/
  fgRoot_preceq_ofJustifiedBranch : ∀ {stH : M.HS} {T : Block V} (hF : Block.Preceq stH.toFG.F T) (hJ : stH.toFG.h_max = stH.toFG.h_j + 1 → Block.Preceq stH.toFG.J T), Block.Preceq (M.get_fg_root stH.toFG) T
  /-- If `st.F ⪯ st.J`, then `st.F` is an ancestor of the FG root of `st` or that root itself. -/
  finalized_preceq_get_fg_root : ∀ (st : M.S) (hFJ : Block.Preceq st.F st.J), Block.Preceq st.F (M.get_fg_root (M.toHealing st).toFG)
  /-- The FG root of `st` is `st.J` or `st.F`. -/
  get_fg_root_eq_J_or_F : ∀ (st : M.S), M.get_fg_root (M.toHealing st).toFG = st.J ∨
    M.get_fg_root (M.toHealing st).toFG = st.F
  /-- Every outcome of the head `M.get_head_in_tree_with_layer` over `tree` is the anchor of the
      contract's grade read at `st`'s round, or a block of `tree`. -/
  get_head_in_tree_with_layer_anchor_or_mem : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (st : M.S) (tree : Finset (Block V)) (votes support : Finset (GoldfishVote V)) (k : Slot) (G : GradeRead V) (hG : contract.read E hc (M.toHealing st) (M.round_of hc st.s) ⇢ G) (X : Block V) (hX : M.get_head_in_tree_with_layer contract E hc (M.toHealing st) tree votes support k ⇢ X), X =
    G.anchor ∨
    X ∈
    tree
  /-- If `T` holds an outcome of the SG root the contract reads at the store's round and every block
      of `tree`, every outcome of the head `M.get_head_in_tree_with_layer` over `tree` is in `T`. -/
  Sts_get_head_in_tree_with_layer_mem : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (st : M.HS) (tree : Finset (Block V)) (votes support : Finset (GoldfishVote V)) (k : Slot) {T : Finset (Block V)} (R : Block V) (hR : M.get_sg_root_with contract E hc st ((M.round_of hc st.toFG.toSG.toGoldfishStore.s)) ⇢ R) (hA : R ∈ T) (htree : tree ⊆ T) (X : Block V) (hX : M.get_head_in_tree_with_layer contract E hc st tree votes support k ⇢ X), X ∈ T
  /-- Under the grade contract of a cache, if the FG root of `st` is in `st`'s tree, every outcome
      of the head `M.get_head_with` is in `st`'s tree. -/
  get_head_with_gradeContract_mem : ∀ (c : M.Cache) (E : Env V) (hc : Protocol.HealConfig) (st : M.HS) (votes support : Finset (GoldfishVote V)) (k : Slot) (hroot : M.get_fg_root st.toFG ∈ st.toFG.toSG.toGoldfishStore.T) (X : Block V) (hX : M.get_head_with (M.gradeContract c) E hc st votes support k ⇢ X), X
    ∈ st.toFG.toSG.toGoldfishStore.T
  /-- If no two distinct blocks of `tree` or their ancestors share a root, and `C` in `tree` has as
      its parent an outcome of the Goldfish fork choice from `A` through `tree`, then every outcome
      of `M.goldfish_eligible` for `C` with the same parameters is `false`. -/
  goldfish_eligible_eq_false_of_parent_fork_choice : ∀ {E : Env V} {σ : Block V → M.CS} {h_max : Height} {T : Finset (Block V)} {cur : Slot} {A : Block V} {tree : Finset (Block V)} {votes support : Finset (GoldfishVote V)} {s : Slot} {C : Block V} (hroot : Execution.RootInjectiveBelow tree) (hC : C ∈ tree) (X : Block V) (hX : M.goldfish_fork_choice E σ h_max T cur A tree votes support s ⇢ X) (hparent : C.parent? =
    some X) (e : Bool) (he : M.goldfish_eligible E σ h_max T cur votes support s C ⇢ e), e = false
  /-- If no two blocks of `tree` share a root, and `C` in `tree` has as its parent an outcome of the
      head `M.get_head_in_tree_with_layer` over `tree`, then every outcome of the Goldfish
      eligibility test of `C` at `st` with the same votes and slot is `false`. -/
  goldfish_eligible_false_of_parent_head : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (st : M.S) (tree : Finset (Block V)) (votes support : Finset (GoldfishVote V)) (k : Slot) {C : Block V} (hroot : Execution.RootInjectiveBelow tree) (hC : C ∈ tree) (X : Block V) (hX : M.get_head_in_tree_with_layer contract E hc (M.toHealing st) tree votes support k ⇢ X) (hparent : C.parent? = some
    X) (e : Bool) (he : M.goldfish_eligible E st.σ st.h_max st.T st.s votes support k C ⇢ e), e = false
  /-- When the proposer's Goldfish fork choice returns `P`, the voter's runs through a common block
      `Y ⪯ P`, the two stores agree on scores, voter count and the chain from `Y` to `P` as the
      hypotheses state, and `B` is the only block of `Tv` of slot `cur`, a child of `P` with no
      child in `Tv`, then the voter's fork choice returns `B`. -/
  goldfish_fork_choice_eq_child_of_pivot : ∀ (E : Env V) {σp σv : Block V → M.CS} {hp hv : Height} {TPs TVs Tp Tv : Finset (Block V)} {cur : Slot} {votesP supportP votesV supportV : Finset (GoldfishVote V)} {s' : Slot} {Ap Av Y P B : Block V} (hrootP : RootInjectiveBelow Tp) (hrootV : RootInjectiveBelow Tv) (GP : Block V) (hGP : M.goldfish_fork_choice E σp hp TPs cur Ap Tp votesP supportP s' ⇢ GP) (hsource : GP = P) (hApY : Block.Preceq Ap Y) (hAvY : Block.Preceq Av Y) (hYP : Block.Preceq Y P) (GV : Block V) (hGV : M.goldfish_fork_choice E σv hv TVs cur Av Tv votesV supportV s' ⇢ GV) (hpasses : Block.Preceq Y
    GV) (hhP : ∀ X, Block.Preceq Y X → Block.Preceq X P → hp - 1 ≤ (σp X).h) (hhV : ∀ X, Block.Preceq Y X → Block.Preceq X P → hv - 1 ≤ (σv X).h) (scV : Block V → ℕ) (hscV : ∀ C, M.goldfish_score E TVs votesV supportV s' C ⇢ scV C) (scP : Block V → ℕ) (hscP : ∀ C, M.goldfish_score E TPs votesP supportP s' C ⇢ scP C) (hscore : ∀ C, Block.Preceq Y C →
    scV C =
    scP C) (hcount : M.voters_count E votesV s' = M.voters_count E votesP s') (hpathV : ∀ C, Block.Preceq Y C → C ≠ Y → Block.Preceq C P → C ∈ Tv) (hchildV : ∀ X C, Block.Preceq Y X → Block.Preceq X P → C ∈ Tv → C.parent? = some X →
    C.slot ≠ cur → C ∈ Tp) (hBonly : ∀ C ∈ Tv, C.slot = cur → C = B) (hB : B ∈ Tv) (hBpar : B.parent? = some P) (hBslot : B.slot = cur) (hfresh : ∀ C ∈ Tv, C.parent? ≠ some B), GV = B
  /-- The Goldfish fork choice from `A` through `tree` can return `X` exactly when the walk
      `M.ghost` from `A` through `tree`, scored by an outcome of the Goldfish score and accepting by
      an outcome of the Goldfish eligibility test, can return `X`. -/
  goldfish_fork_choice_eq_ghost : ∀ (E : Env V) (σ : Block V → M.CS) (h_max : Height) (T : Finset (Block V)) (cur : Slot) (A : Block V) (tree : Finset (Block V)) (votes support : Finset (GoldfishVote V)) (s : Slot)
    (score : Block V → ℕ) (hscore : ∀ B, M.goldfish_score E T votes support s B ⇢ score B)
    (elig : Block V → Bool) (helig : ∀ B, M.goldfish_eligible E σ h_max T cur votes support s B ⇢ elig B)
    (X : Block V), M.goldfish_fork_choice E σ h_max T cur A tree votes support s ⇢ X ↔
    M.ghost A tree score elig ⇢ X
  /-- Two vote-set pairs with the same equivocators and the same non-equivocating supporters of `C`
      give `C` the same Goldfish score. -/
  goldfish_score_eq_of_iff : ∀ (E : Env V) {T T' : Finset (Block V)} {votes support votes' support' : Finset (GoldfishVote V)} (s : Slot) (C : Block V) (heq : ∀ w : V, M.equivocates votes w = M.equivocates votes' w) (t : GoldfishVote V → Bool) (ht : ∀ u, M.targets_under T C u ⇢ t u) (t' : GoldfishVote V → Bool) (ht' : ∀ u, M.targets_under T' C u ⇢ t' u) (hsup : ∀ w : V, M.equivocates votes w = false →
    ((∃ u ∈ support, u.val_index = w ∧ u.slot = s ∧ t u = true) ↔
    (∃ u ∈ support', u.val_index = w ∧ u.slot = s ∧
    t' u = true))) (g : ℕ) (hg : M.goldfish_score E T votes support s C ⇢ g) (g' : ℕ) (hg' : M.goldfish_score E T' votes' support' s C ⇢ g'), g =
    g'
  /-- A block of an outcome of the voter's processed block tree of `gs` is in `gs`'s tree. -/
  mem_T_of_mem_voter_processed_block_tree : ∀ (E : Env V) (gs : M.GS) (s : Slot) {B : Block V} (P : Finset (Block V)) (hP : M.voter_processed_block_tree E gs s ⇢ P) (h : B ∈ P), B ∈ gs.T
  /-- If `C` is in `st`'s tree, `st.F ⪯ C`, some `W` in `st`'s tree with `C ⪯ W` has chain-state
      height at least `st.h_max - 1`, and the FG root of `st` is an ancestor of `C` or `C` itself,
      then `C` is in `st`'s filtered block tree. -/
  mem_get_filtered_block_tree_of_parts : ∀ (st : M.HS) {C W : Block V} (hC : C ∈ st.toFG.toSG.toGoldfishStore.T) (hF : Block.Preceq st.toFG.F C) (hW : W ∈ st.toFG.toSG.toGoldfishStore.T) (hCW : Block.Preceq C W) (hh : st.toFG.h_max - 1 ≤ (st.toFG.σ W).h) (hroot : Block.Preceq (M.get_fg_root st.toFG) C), C ∈ M.get_filtered_block_tree st.toFG
  /-- A round `k` of `M.latest_window eta r` has `r − eta ≤ k`. -/
  mem_latest_window_ge : ∀ {eta r k : Round} (hk : k ∈ M.latest_window eta r), r - eta ≤ k
  /-- A round `k` of `M.latest_window eta r` has `k < r`. -/
  mem_latest_window_lt : ∀ {eta r k : Round} (hk : k ∈ M.latest_window eta r), k < r
  /-- A vote `u` is in an outcome of the slot-`s` proposer support view of `gs` exactly when it is
      among `gs`'s slot-`(s − 1)` Goldfish votes and its resolution test answers `true`. -/
  mem_proposer_support_view_iff : ∀ (gs : M.GS) (s : Slot) (u : GoldfishVote V) (L : List (GoldfishVote V)) (hL : M.proposer_support_view gs s ⇢ L) (b : Bool) (hb : M.resolved gs.T u ⇢ b), u ∈ L ↔
    u ∈ gs.gf_votes (s - 1) ∧ b = true
  /-- If `B` and `P` are in `gs`'s tree, `P` has slot `s`, and `B ⪯ P`, then `B` is in every outcome
      of the voter's processed block tree of `gs` at slot `s`. -/
  mem_voter_processed_block_tree_of_proposal : ∀ (E : Env V) (gs : M.GS) (s : Slot) {B P : Block V} (hT : B ∈ gs.T) (hP : P ∈ gs.T) (hPs : P.slot = s) (hBP : Block.Preceq B P) (Q : Finset (Block V)) (hQ : M.voter_processed_block_tree E gs s ⇢ Q), B ∈ Q
  /-- A block of `gs`'s tree with slot `s` is in every outcome of the voter's processed block tree
      of `gs` at slot `s`. -/
  mem_voter_processed_block_tree_of_slot : ∀ (E : Env V) (gs : M.GS) (s : Slot) {B : Block V} (hB : B ∈ gs.T) (hs : B.slot = s) (Q : Finset (Block V)) (hQ : M.voter_processed_block_tree E gs s ⇢ Q), B ∈ Q
  /-- A block of `gs`'s tree stamped before the view freeze of slot `s − 1` is in every outcome of
      the voter's processed block tree of `gs` at slot `s`. -/
  mem_voter_processed_block_tree_of_stamped : ∀ (E : Env V) (gs : M.GS) (s : Slot) {B : Block V} (hT : B ∈ gs.T) (hst : stampedBefore gs.timestamp_block (M.view_freeze E (s - 1)) B = true) (Q : Finset (Block V)) (hQ : M.voter_processed_block_tree E gs s ⇢ Q), B ∈ Q
  /-- A resolved slot-`(s − 1)` vote in the support list of a slot-`s` block of `gs`'s tree is in
      every outcome of the slot-`s` support view of `gs`. -/
  mem_voter_support_view_of_carried : ∀ (E : Env V) (gs : M.GS) (s : Slot) {u : GoldfishVote V} {X : Block V} (hX : X ∈ gs.T) (hXs : X.slot = s) (hu : u ∈ X.gf_support_votes) (b : Bool) (hb : M.resolved gs.T u ⇢ b) (hres : b = true) (hus : u.slot = s - 1) (Y : Finset (GoldfishVote V)) (hY : M.voter_support_view E gs s ⇢ Y), u ∈ Y
  /-- A slot-`(s − 1)` Goldfish vote included in a slot-`s` block of `gs`'s tree is in every outcome
      of the slot-`s` voter view of `gs`. -/
  mem_voter_view_of_carried : ∀ (E : Env V) (gs : M.GS) (s : Slot) {u : GoldfishVote V} {X : Block V} (hX : X ∈ gs.T) (hXs : X.slot = s) (hu : u ∈ X.gf_votes) (hus : u.slot = s - 1) (Y : Finset (GoldfishVote V)) (hY : M.voter_view E gs s ⇢ Y), u ∈ Y
  /-- If an outcome of the Goldfish vote duty of `nd` on `st` returns the vote `u`, then `nd`'s
      validator is in the committee of slot `s` of `st`'s core store, and `u` is its slot-`s` vote
      for the root of the head that the fork choice under `contract` returns over the voter's
      filtered block tree and vote views. -/
  namedDuties_goldfish_vote_with_snd_eq_some : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : M.NS) {u : GoldfishVote V}
    (D : M.NS × Option (GoldfishVote V)) (hD : M.duties_goldfish_vote_with contract E hc nd st ⇢ D) (h : D.2 = some u)
    (tree : Finset (Block V)) (htree : M.voter_filtered_block_tree E st.core st.core.s ⇢ tree)
    (votes : Finset (GoldfishVote V)) (hvotes : M.voter_view E (M.toHealing st.core).toFG.toSG.toGoldfishStore st.core.s ⇢ votes)
    (support : Finset (GoldfishVote V)) (hsupport : M.voter_support_view E (M.toHealing st.core).toFG.toSG.toGoldfishStore st.core.s ⇢ support)
    (H : Block V) (hH : M.get_head_in_tree_with_layer contract E hc (M.toHealing st.core) tree votes support (st.core.s - 1) ⇢ H),
    nd.val_index ∈ E.committee st.core.s ∧
    u = ⟨nd.val_index, st.core.s, H.root⟩
  /-- If an outcome of the Goldfish vote duty of `nd` on `st` signs the vote `u`, the head of `u` is
      the root of the head `M.get_head_in_tree_with_layer` computes over the voter's tree and vote
      views. -/
  namedDuties_goldfish_vote_with_snd_head : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : M.NS) {u : GoldfishVote V}
    (D : M.NS × Option (GoldfishVote V)) (hD : M.duties_goldfish_vote_with contract E hc nd st ⇢ D) (h : D.2 = some u)
    (tree : Finset (Block V)) (htree : M.voter_filtered_block_tree E st.core st.core.s ⇢ tree)
    (votes : Finset (GoldfishVote V)) (hvotes : M.voter_view E (M.toHealing st.core).toFG.toSG.toGoldfishStore st.core.s ⇢ votes)
    (support : Finset (GoldfishVote V)) (hsupport : M.voter_support_view E (M.toHealing st.core).toFG.toSG.toGoldfishStore st.core.s ⇢ support)
    (H : Block V) (hH : M.get_head_in_tree_with_layer contract E hc (M.toHealing st.core) tree votes support (st.core.s - 1) ⇢ H),
    u.head = H.root
  /-- A block `C` of the filtered block tree of `st` is in `st`'s tree, has `st.F ⪯ C`, has a
      descendant or itself `W` in `st`'s tree with chain-state height at least `st.h_max - 1`, and
      has the FG root of `st` as an ancestor or itself. -/
  parts_of_mem_get_filtered_block_tree : ∀ {st : M.FGS} {C : Block V} (h : C ∈ M.get_filtered_block_tree st), ((C ∈ st.toSG.toGoldfishStore.T ∧ Block.Preceq st.F C) ∧
    ∃ W, W ∈ st.toSG.toGoldfishStore.T ∧ Block.Preceq C W ∧ st.h_max - 1 ≤ (st.σ W).h) ∧
    Block.Preceq (M.get_fg_root st) C
  /-- The slot-`s` proposer view of `gs` is the list of `gs`'s slot-`(s − 1)` Goldfish votes. -/
  proposer_view_eq : ∀ (gs : M.GS) (s : Slot), M.proposer_view gs s = gs.gf_votes (s - 1)
  /-- The votes of the slot-`s` proposer view of `gs` are the set `M.gs_pool gs (s − 1)`. -/
  proposer_view_toFinset : ∀ (gs : M.GS) (s : Slot), (M.proposer_view gs s).toFinset = (M.gs_pool gs (s - 1))
  /-- An outcome of the supporter test `M.targets_under T B u` is `true` exactly when `u`'s head
      resolves in `T` to a block `X` of slot at most `u`'s slot with `B ⪯ X`. -/
  targets_under_eq_true_iff : ∀ (T : Finset (Block V)) (B : Block V) (u : GoldfishVote V) (b : Bool) (hb : M.targets_under T B u ⇢ b), b = true ↔
    ∃ X, Block.find? T u.head = some X ∧ X.slot ≤ u.slot ∧ Block.Preceq B X
  /-- A block `B` of the filtered block tree of `st` has a descendant or itself `W` in `st`'s tree
      with chain-state height at least `st.h_max - 1`. -/
  viable_witness_of_mem_get_filtered_block_tree : ∀ {st : M.FGS} {B : Block V} (hB : B ∈ M.get_filtered_block_tree st), ∃ W ∈ st.toSG.toGoldfishStore.T, Block.Preceq B W ∧ st.h_max - 1 ≤ (st.σ W).h
  /-- A block of an outcome of the voter's processed block tree of `gs` at slot `s` is in `gs`'s
      tree, and either was stamped before the view freeze of slot `s − 1` or is an ancestor of a
      slot-`s` block of `gs`'s tree, or that block itself. -/
  voter_processed_block_tree_cases : ∀ (E : Env V) (gs : M.GS) (s : Slot) {B : Block V} (Q : Finset (Block V)) (hQ : M.voter_processed_block_tree E gs s ⇢ Q) (h : B ∈ Q), B ∈ gs.T ∧
    (stampedBefore gs.timestamp_block (M.view_freeze E (s - 1)) B = true ∨
    ∃ P ∈ gs.T, P.slot = s ∧ Block.Preceq B P)
  /-- A vote of an outcome of the slot-`s` support view of `gs` is either a vote of
      `M.gs_pool gs (s − 1)` whose head resolves in `gs`'s tree to a block of slot at most the
      vote's, with both stamped before slot `s − 1`'s view freeze, or a resolved slot-`(s − 1)` vote
      of the support list of a slot-`s` block of `gs`'s tree. -/
  voter_support_view_cases : ∀ (E : Env V) (gs : M.GS) (s : Slot) {u : GoldfishVote V} (Y : Finset (GoldfishVote V)) (hY : M.voter_support_view E gs s ⇢ Y) (h : u ∈ Y) (b : Bool) (hb : M.resolved gs.T u ⇢ b), (u ∈ (M.gs_pool gs (s - 1)) ∧ ∃ X : Block V, Block.find? gs.T u.head = some X ∧
    X.slot ≤ u.slot ∧ ∃ τ σ : Stamp, gs.timestamp_vote u = some τ ∧
    gs.timestamp_block X = some σ ∧
    τ < ((M.view_freeze E (s - 1) : Int) : Stamp) ∧
    σ < ((M.view_freeze E (s - 1) : Int) : Stamp)) ∨
    ∃ X ∈ gs.T, X.slot = s ∧ u ∈ X.gf_support_votes ∧
    b = true ∧ u.slot = s - 1
  /-- A vote of an outcome of the slot-`s` voter view of `gs` is either a vote of
      `M.gs_pool gs (s − 1)` stamped before slot `s − 1`'s view freeze, or a slot-`(s − 1)` Goldfish
      vote included in a slot-`s` block of `gs`'s tree. -/
  voter_view_cases : ∀ (E : Env V) (gs : M.GS) (s : Slot) {u : GoldfishVote V} (Y : Finset (GoldfishVote V)) (hY : M.voter_view E gs s ⇢ Y) (h : u ∈ Y), (u ∈ (M.gs_pool gs (s - 1)) ∧ ∃ τ : Stamp, gs.timestamp_vote u = some τ ∧
    τ < ((M.view_freeze E (s - 1) : Int) : Stamp)) ∨
    ∃ X ∈ gs.T, X.slot = s ∧ u ∈ X.gf_votes ∧ u.slot = s - 1
  /-- A vote of an outcome of the slot-`s` voter view of `gs` is either in `beforeCutoff` of
      `M.gs_pool gs (s − 1)` at slot `s − 1`'s view freeze, or a slot-`(s − 1)` Goldfish vote
      included in a slot-`s` block of `gs`'s tree. -/
  voter_view_cases_beforeCutoff : ∀ (E : Env V) (gs : M.GS) (s : Slot) {u : GoldfishVote V} (Y : Finset (GoldfishVote V)) (hY : M.voter_view E gs s ⇢ Y) (h : u ∈ Y), u ∈ beforeCutoff gs.timestamp_vote (M.view_freeze E (s - 1)) ((M.gs_pool gs (s - 1))) ∨
    ∃ X ∈ gs.T, X.slot = s ∧ u ∈ X.gf_votes ∧ u.slot = s - 1
  /-- Two vote sets with the same participants have the same voter count, at any two slots. -/
  voters_count_eq_of_participates : ∀ (E : Env V) {votes votes' : Finset (GoldfishVote V)} (s s' : Slot) (h : ∀ w : V, M.participates votes w = M.participates votes' w), M.voters_count E votes s = M.voters_count E votes' s'
  /-- If the anchor of an outcome of the grade read `gc.read` at the round of `st`'s slot is in
      `st`'s tree, every outcome of the head `M.get_head_with gc E hc st votes support k` is in
      `st`'s tree. -/
  NamedProposalParent_get_head_with_mem : ∀ (gc : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (st : M.HS) (votes support : Finset (GoldfishVote V)) (k : Slot) (G : GradeRead V),
    gc.read E hc st (M.round_of hc st.toFG.toSG.toGoldfishStore.s) ⇢ G → G.anchor ∈ st.toFG.toSG.toGoldfishStore.T →
    ∀ X : Block V, M.get_head_with gc E hc st votes support k ⇢ X → X ∈ st.toFG.toSG.toGoldfishStore.T
  /-- Every supporter test `M.targets_under T B u` has an outcome. -/
  targets_under_nonempty : ∀ (T : Finset (Block V)) (B : Block V) (u : GoldfishVote V),
    ∃ b, M.targets_under T B u ⇢ b
  /-- Every Goldfish score `M.goldfish_score` has an outcome. -/
  goldfish_score_nonempty : ∀ (E : Env V) (T : Finset (Block V)) (votes support_votes : Finset (GoldfishVote V))
    (s : Slot) (B : Block V), ∃ g : ℕ, M.goldfish_score E T votes support_votes s B ⇢ g
  /-- Every voter's filtered block tree `M.voter_filtered_block_tree` has an outcome. -/
  voter_filtered_block_tree_nonempty : ∀ (E : Env V) (st : M.S) (s : Slot),
    ∃ T : Finset (Block V), M.voter_filtered_block_tree E st s ⇢ T
  /-- Every voter view `M.voter_view` has an outcome. -/
  voter_view_nonempty : ∀ (E : Env V) (gst : M.GS) (s : Slot),
    ∃ W : Finset (GoldfishVote V), M.voter_view E gst s ⇢ W
  /-- Every voter support view `M.voter_support_view` has an outcome. -/
  voter_support_view_nonempty : ∀ (E : Env V) (gst : M.GS) (s : Slot),
    ∃ U : Finset (GoldfishVote V), M.voter_support_view E gst s ⇢ U
  /-- Every head `M.get_head_in_tree_with_layer` under a contract has an outcome. -/
  get_head_in_tree_with_layer_nonempty : ∀ (contract : M.Contract) (E : Env V) (hc : HealConfig)
    (st : M.HS) (tree : Finset (Block V)) (votes support_votes : Finset (GoldfishVote V)) (k : Slot),
    ∃ X : Block V, M.get_head_in_tree_with_layer contract E hc st tree votes support_votes k ⇢ X
  /-- Every supporter set `M.raw_supporters` has an outcome. -/
  raw_supporters_nonempty : ∀ (T : Finset (Block V)) (votes support_votes : Finset (GoldfishVote V)) (s : Slot)
    (B : Block V), ∃ sup : Finset V, M.raw_supporters T votes support_votes s B ⇢ sup
  /-- Every proposer support view `M.proposer_support_view` has an outcome. -/
  proposer_support_view_nonempty : ∀ (gs : M.GS) (s : Slot),
    ∃ L : List (GoldfishVote V), M.proposer_support_view gs s ⇢ L
  /-- Every head `M.get_head_with` under a contract has an outcome. -/
  get_head_with_nonempty : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (st : M.HS)
    (votes support : Finset (GoldfishVote V)) (k : Slot),
    ∃ X : Block V, M.get_head_with contract E hc st votes support k ⇢ X
  /-- Every SG root `M.get_sg_root_with` under a contract has an outcome. -/
  get_sg_root_with_nonempty : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (st : M.HS)
    (r : Round), ∃ R : Block V, M.get_sg_root_with contract E hc st r ⇢ R
  /-- Every Goldfish eligibility test `M.goldfish_eligible` has an outcome. -/
  goldfish_eligible_nonempty : ∀ (E : Env V) (σ : Block V → M.CS) (h_max : Height) (T : Finset (Block V))
    (cur : Slot) (votes support : Finset (GoldfishVote V)) (s : Slot) (B : Block V),
    ∃ b : Bool, M.goldfish_eligible E σ h_max T cur votes support s B ⇢ b
  /-- Every voter's processed block tree `M.voter_processed_block_tree` has an outcome. -/
  voter_processed_block_tree_nonempty : ∀ (E : Env V) (gs : M.GS) (s : Slot),
    ∃ P : Finset (Block V), M.voter_processed_block_tree E gs s ⇢ P
  /-- If slot `s`'s committee has fewer members than twice its members in `Hon`, `votes ⊆ late`, no
      committee member in `Hon` equivocates in `votes`, every committee member in `Hon` has a
      slot-`s` vote in `support` whose head resolves in `T` to a block `tgt` admits, the late votes
      are valid for slot `s`, and `C` is an ancestor of every block `tgt` admits, then the late
      voters of slot `s` are fewer than twice every outcome of `C`'s Goldfish score. -/
  ConeSupport_eligible : ∀ (E : Env V) (T : Finset (Block V)) (votes support late : Finset (GoldfishVote V)) (s : Slot) (Hon : Finset V) (tgt : Block V → Prop) {C : Block V} (hmaj : (E.committee s).card < 2 * ((E.committee s) ∩ Hon).card) (hcounted : votes ⊆ late) (hsub : support ⊆ votes) (hno : ∀ x ∈ E.committee s, x ∈ Hon → M.equivocates votes x = false) (hvote : ∀ x ∈ E.committee s, x ∈ Hon → ∃ u ∈ support, u.val_index = x ∧ u.slot = s ∧ ∃ X : Block V, Block.find? T u.head = some X ∧ X.slot ≤ u.slot ∧ tgt X) (hvalid : Protocol.VoteSetValid E s late) (hC : ∀ X : Block V, tgt X → Block.preceq C X = true) (g : ℕ) (hg : M.goldfish_score E T votes support s C ⇢ g), M.voters_count E late s < 2 * g
  /-- If `D ⪯ C`, every outcome of `C`'s Goldfish score is at most every outcome of `D`'s, over the
      same tree, votes and slot. -/
  goldfish_score_le_of_Preceq : ∀ (E : Env V) (T : Finset (Block V))
    (votes support : Finset (GoldfishVote V)) (s : Slot) {C D : Block V},
    Block.Preceq D C →
    ∀ gC : ℕ, M.goldfish_score E T votes support s C ⇢ gC →
    ∀ gD : ℕ, M.goldfish_score E T votes support s D ⇢ gD →
    gC ≤ gD
  /-- Every outcome of the voter's filtered block tree of `st` at `st`'s slot is a subset of the
      filtered block tree of `st`'s healing view. -/
  voter_filtered_block_tree_subset_filtered : ∀ (E : Env V) (st : M.S) (X : Finset (Block V)),
    M.voter_filtered_block_tree E st st.s ⇢ X → X ⊆ M.get_filtered_block_tree (M.toHealing st).toFG
  /-- Every walk `M.ghost` has an outcome. -/
  ghost_nonempty : ∀ (A : Block V) (tree : Finset (Block V)) (score : Block V → ℕ) (elig : Block V → Bool), ∃ X : Block V, M.ghost A tree score elig ⇢ X
  /-- Every step `M.ghost_step` of the walk has an outcome. -/
  ghost_step_nonempty : ∀ (tree : Finset (Block V)) (score : Block V → ℕ) (eligible : Block V → Bool)
    (H : Block V), ∃ o : Option (Block V), M.ghost_step tree score eligible H ⇢ o
  /-- If `early ⊆ late` and `votes` is the votes of `early` with no second vote in `late`, then
      every outcome of the Goldfish score of `B` with `votes` in both vote arguments equals the size
      of every outcome of the supporters of `B` with the same arguments. -/
  Numerator_score_eq_supporters : ∀ (early late votes : Finset (GoldfishVote V)), early ⊆ late →
    votes = early.filter (fun u => M.no_second_vote_in late u = true) →
    ∀ (E : Env V) (T : Finset (Block V)) (s : Slot) (B : Block V) (sc : Nat),
    M.goldfish_score E T votes votes s B ⇢ sc →
    ∀ R : Finset V, M.raw_supporters T votes votes s B ⇢ R → sc = R.card

/-- The facts about runs of the fork-choice routines of the model `M`; it has no field. -/
structure ForkChoiceRunFacts (M : Model V) : Prop where


end DecoupledConsensusModel.Sts.Record
