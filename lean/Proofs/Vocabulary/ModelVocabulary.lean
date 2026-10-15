import Model.Record.Model
import Proofs.Vocabulary.ChainStateVocabulary

/-!
# The instance `Model.vocabulary` of the record

`Model.vocabulary` fills the record `Model` with the model's own structures, fields and routines; each
member whose value is a set of outcomes is the routine's one outcome, and `wake` is the identity.
The simp set `record_vocabulary` is declared here.
-/

set_option autoImplicit false

/-- The simp set of the equivalences `Sts.X … ↔ Record.X Model.vocabulary …` between a definition
    naming a routine of the record and its statement over the record at the instance
    `Model.vocabulary`. -/
register_simp_attr record_vocabulary

namespace DecoupledConsensusModel.Sts.Record

open DecoupledConsensusModel.Protocol (HeightConfig HealConfig)
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The model's own structures and routines as an instance of the record `Model`; the node's tick
    and receipt, which never fail and never pick, are each wrapped as their one outcome. -/
def Model.vocabulary : Model V where
  toChainStateModel := DecoupledConsensusModel.Sts.Record.vocabulary
  GS := Protocol.GoldfishStore V
  S := Protocol.Store V
  SGS := Protocol.SGStore V
  FGS := Protocol.FGStore V
  R := Protocol.Record
  NR := Protocol.NamedRecord
  HS := Protocol.HealingStore V
  GV := Protocol.GradeView V
  Frame := Protocol.Frame V
  Cache := Protocol.Cache V
  Contract := Protocol.GradeContract V
  NS := Protocol.NamedStore V
  N := Execution.NamedNodeState V
  L := fun (σ : Protocol.ChainState V) => σ.L
  cs_s := fun (σ : Protocol.ChainState V) => σ.s
  finalize := fun (σ : Protocol.ChainState V) => σ.finalize
  cs_initial := Protocol.ChainState.initial
  advance_height := Protocol.advance_height
  slashable := Protocol.slashable
  e1Fields := Protocol.e1Fields
  e1Slashable := Protocol.e1Slashable
  e2Slashable := Protocol.e2Slashable
  sameValidator := Protocol.sameValidator
  transition_rows := Protocol.transition_rows
  nonjustifiable := Protocol.nonjustifiable
  cs_with_F_h_F := fun (σ : Protocol.ChainState V) B h => { σ with F := B, h_F := h }
  proposal_time := Protocol.proposal_time
  proposal_wake_start := fun S s => Protocol.proposal_time S.E s - S.E.Δ
  vote_time := Protocol.vote_time
  support_cutoff := Protocol.support_cutoff
  view_freeze := Protocol.view_freeze
  confirmation_time := Protocol.confirmation_time
  votes_by := Protocol.votes_by
  equivocates := Protocol.equivocates
  participates := Protocol.participates
  gs_s := fun x => x.s
  gs_T := fun x => x.T
  gs_timestamp_block := fun x => x.timestamp_block
  gs_timestamp_vote := fun x => x.timestamp_vote
  gs_gf_votes := fun x => x.gf_votes
  gs_live_confirmed := fun x => x.live_confirmed
  store_t := fun x => x.t
  store_s := fun x => x.s
  store_T := fun x => x.T
  store_timestamp_block := fun x => x.timestamp_block
  store_timestamp_vote := fun x => x.timestamp_vote
  store_timestamp_sg_vote := fun x => x.timestamp_sg_vote
  store_σ := fun x => x.σ
  store_gf_votes := fun x => x.gf_votes
  store_sg_votes := fun x => x.sg_votes
  store_F := fun x => x.F
  store_J := fun x => x.J
  store_h_j := fun x => x.h_j
  store_h_max := fun x => x.h_max
  store_live_confirmed := fun x => x.live_confirmed
  store_latest_confirmed := fun x => x.latest_confirmed
  store_latest_stable := fun x => x.latest_stable
  store_tau := fun a => pure (Protocol.Store.tau a)
  toHealing := Protocol.Store.toHealing
  store_pool := Protocol.Store.pool
  sgVote := Protocol.sgVote
  store_sg_pool := Protocol.Store.sg_pool
  resolved := fun a b => pure (Protocol.resolved a b)
  gs_pool := Protocol.GoldfishStore.pool
  gs_tau := fun a => pure (Protocol.GoldfishStore.tau a)
  store_with_t_s := fun st t s => { st with t := t, s := s }
  store_with_cache := fun st _ => st
  contractCache := fun _ => Protocol.initialCache
  store_with_h_max := fun st h => { st with h_max := h }
  store_with_J_h_j := fun st B h => { st with J := B, h_j := h }
  store_with_σ_T_timestamp_block := fun st σ' T' τ' =>
    { st with σ := σ', T := T', timestamp_block := τ' }
  store_init := Protocol.Store.init
  toGoldfishStore := fun x => x.toGoldfishStore
  sgs_sg_votes := fun x => x.sg_votes
  toSG := fun x => x.toSG
  fg_σ := fun x => x.σ
  fg_F := fun x => x.F
  fg_J := fun x => x.J
  fg_h_j := fun x => x.h_j
  fg_h_max := fun x => x.h_max
  get_fg_root := Protocol.get_fg_root
  get_filtered_block_tree := Protocol.get_filtered_block_tree
  get_sg_root_with := fun a b c d e => pure (Protocol.get_sg_root_with a b c d e)
  voter_processed_block_tree := fun a b c => pure (Protocol.voter_processed_block_tree a b c)
  voter_view := fun a b c => pure (Protocol.voter_view a b c)
  voters_count := Protocol.voters_count
  latest_window := Protocol.latest_window
  goldfish_score := fun a b c d e f => pure (Protocol.goldfish_score a b c d e f)
  voter_support_view := fun a b c => pure (Protocol.voter_support_view a b c)
  proposer_view := Protocol.proposer_view
  get_head_with := fun a b c d e f g => pure (Protocol.get_head_with a b c d e f g)
  ghost := fun a b c d => pure (Protocol.ghost a b c d)
  proposer_support_view := fun a b => pure (Protocol.proposer_support_view a b)
  goldfish_eligible := fun a b c d e f g h i => pure (Protocol.goldfish_eligible a b c d e f g h i)
  targets_under := fun a b c => pure (Protocol.targets_under a b c)
  goldfish_fork_choice := fun a b c d e f g h i j =>
    pure (Protocol.goldfish_fork_choice a b c d e f g h i j)
  get_head_in_tree_with_layer := fun a b c d e f g h =>
    pure (Protocol.get_head_in_tree_with_layer a b c d e f g h)
  viable_tree := Protocol.viable_tree
  no_second_vote_in := Protocol.no_second_vote_in
  viable := Protocol.viable
  finalized_descendants := Protocol.finalized_descendants
  ghost_step := fun a b c d => pure (Protocol.ghost_step a b c d)
  get_filtered_block_tree_from := Protocol.get_filtered_block_tree_from
  raw_participants := Protocol.raw_participants
  raw_supporters := fun a b c d e => pure (Protocol.raw_supporters a b c d e)
  target := fun x => x.target
  timeout := fun x => x.timeout
  lock := fun x => x.lock
  legacy := fun x => x.legacy
  nr_timeoutHistory := fun x => x.timeoutHistory
  own_lock := Protocol.own_lock
  height_pair := Protocol.height_pair
  create_attestation := Protocol.create_attestation
  finality_pair := Protocol.finality_pair
  encodeHeight := Protocol.NamedRecord.encodeHeight
  record_attestation := Protocol.record_attestation
  toFG := fun x => x.toFG
  gv_T := fun x => x.T
  gv_timestamp_block := fun x => x.timestamp_block
  gv_tree := fun x => x.tree
  gv_sg_votes := fun x => x.sg_votes
  gv_timestamp_sg_vote := fun x => x.timestamp_sg_vote
  g0 := fun x => x.g0
  g1 := fun x => x.g1
  g2 := fun x => x.g2
  round := fun x => x.round
  cache_current := fun x => x.current
  read := fun x a b c d => pure (x.read a b c d)
  confirmationSG := fun gc a b c d =>
    pure ((match gc.confirmationSG with | .optional select => select) a b c d)
  stableRoot := fun x a b c d => pure (x.stableRoot a b c d)
  contract_sgVote := fun x => x.sgVote
  mkContract := fun rd sv sel sr =>
    { read := rd, sgVote := sv, confirmationSG := .optional sel, stableRoot := sr }
  opening_slot := Protocol.HealConfig.opening_slot
  domain := Protocol.domain
  opening := Protocol.opening
  round_of := Protocol.HealConfig.round_of
  gradeView := Protocol.HealingStore.gradeView
  early := Protocol.early
  late := Protocol.late
  gradeBool := fun a b c d e f g h => pure (Protocol.gradeBool a b c d e f g h)
  onPhaseTick := fun a b c d e => pure (Protocol.onPhaseTick a b c d e)
  readFrame := Protocol.readFrame
  a := Protocol.HealConfig.a
  phaseResult := Protocol.phaseResult
  activePrefix := Protocol.activePrefix
  rawView := fun a b c d e => pure (Protocol.rawView a b c d e)
  clipCache := Protocol.clipCache
  clipGrade := Protocol.clipGrade
  rawInputs := fun a b c d e => pure (Protocol.rawInputs a b c d e)
  frameContract := Protocol.frameContract
  readyView := fun a b c d e f => pure (Protocol.readyView a b c d e f)
  currentSGVote := Protocol.currentSGVote
  cacheAtRound := Protocol.cacheAtRound
  interpretedInputs := fun a b c d e f => pure (Protocol.interpretedInputs a b c d e f)
  freezeRoot := fun a b c d e f g => pure (Protocol.freezeRoot a b c d e f g)
  anchor := fun a b c d e => pure (Protocol.anchor a b c d e)
  localCovers := fun a b c => pure (Protocol.localCovers a b c)
  positive := fun a b c d e f g h => pure (Protocol.positive a b c d e f g h)
  grade2Block := fun a b => pure (Protocol.grade2Block a b)
  deepest_clear := Protocol.deepest_clear
  frameStableRoot := fun a b c d e => pure (Protocol.frameStableRoot a b c d e)
  opposing := fun a b c d e f g h => pure (Protocol.opposing a b c d e f g h)
  token := Protocol.token
  head_covers := fun a b c => pure (Protocol.head_covers a b c)
  clipResult := Protocol.clipResult
  frameSGCandidate := fun a b c d e => pure (Protocol.frameSGCandidate a b c d e)
  allClosed := Protocol.allClosed
  bodyReady := fun a b c d => pure (Protocol.bodyReady a b c d)
  frameGradeRead := fun a b c d e => pure (Protocol.frameGradeRead a b c d e)
  Opposes := Protocol.Opposes
  Supports := Protocol.Supports
  CleanFrom := Protocol.CleanFrom
  clipFrame := Protocol.clipFrame
  alignRound := Protocol.alignRound
  pendingFrame := Protocol.pendingFrame
  domainOffset := Protocol.Phase.domainOffset
  earlyOffset := Protocol.Phase.earlyOffset
  lateOffset := Protocol.Phase.lateOffset
  clear := Protocol.clear
  chain_of := Protocol.chain_of
  putPhase := Protocol.putPhase
  chain_up := Protocol.chain_up
  core := fun x => x.core
  sameCore := fun a b => a = b
  bodies := fun x => x.bodies
  sg_rows := fun x => x.sg_rows
  ns_setClock := Protocol.NamedStore.setClock
  get_stable := Protocol.get_stable
  round_votes := Protocol.round_votes
  on_block_with := Protocol.NamedAdmission.on_block_with
  admit_row := Protocol.NamedAdmission.admit_row
  update_confirmation_with := fun a b c d e => pure (Protocol.update_confirmation_with a b c d e)
  on_goldfish_vote_checked := Protocol.on_goldfish_vote_checked
  get_confirmed := Protocol.get_confirmed
  carried_attestations_admissible := Protocol.carried_attestations_admissible
  on_sg_vote := Protocol.on_sg_vote
  admit_rows := Protocol.NamedAdmission.admit_rows
  advance_confirmed := Protocol.advance_confirmed
  ns_process_block_core := Protocol.NamedStore.process_block_core
  voter_filtered_block_tree := fun a b c => pure (Protocol.voter_filtered_block_tree a b c)
  floor_on_stable := Protocol.floor_on_stable
  on_block_using := Protocol.on_block_using
  on_block_checked_using := Protocol.on_block_checked_using
  on_goldfish_vote := Protocol.on_goldfish_vote
  goldfish_vote_with := fun a b c d e => pure (Protocol.goldfish_vote_with a b c d e)
  ns_initial := Protocol.NamedStore.initial
  update_finality := Protocol.update_finality
  admit_carried := Protocol.NamedAdmission.admit_carried
  get_head_in_tree_with := fun a b c d e f g h =>
    pure (Protocol.get_head_in_tree_with a b c d e f g h)
  state_transition := Protocol.state_transition
  ns_with_core := fun ns c => { ns with core := c }
  commitBlock := Protocol.NamedStore.commitBlock
  duties_propose_block_with := fun a b c d e f =>
    pure (Protocol.NamedDuties.propose_block_with a b c d e f)
  duties_attest_with := fun a b c d e f => pure (Protocol.NamedDuties.attest_with a b c d e f)
  duties_update_confirmation_with := fun a b c d e =>
    pure (Protocol.NamedDuties.update_confirmation_with a b c d e)
  inWindow := Protocol.ProposalRows.inWindow
  round_action_with := fun a b c d e f => pure (Protocol.NamedActions.round_action_with a b c d e f)
  duties_goldfish_vote_with := fun a b c d e =>
    pure (Protocol.NamedDuties.goldfish_vote_with a b c d e)
  grade2_block_with := fun a b c d e => pure (Protocol.grade2_block_with a b c d e)
  proposal_with := fun a b c d e f => pure (Protocol.NamedActions.proposal_with a b c d e f)
  select := fun a b c => pure (Protocol.NamedProposalRows.select a b c)
  parentBody? := fun a b => pure (Protocol.NamedActions.parentBody? a b)
  proposalRows := Protocol.NamedProposalRows.proposalRows
  fg_source_with := fun a b c d e f => pure (Protocol.fg_source_with a b c d e f)
  get_sg_vote_with := fun a b c d e f => pure (Protocol.get_sg_vote_with a b c d e f)
  processedRows := Protocol.NamedProposalRows.processedRows
  with_proposal_input := fun a b c d e f => pure (Protocol.with_proposal_input a b c d e f)
  creatorInput := Protocol.NamedActions.creatorInput
  get_fg_vote_with := fun a b c d e f => pure (Protocol.get_fg_vote_with a b c d e f)
  chainRows := Protocol.NamedProposalRows.chainRows
  with_attestation_input := fun a b c d e f => pure (Protocol.with_attestation_input a b c d e f)
  carriedRows := fun a b => pure (Protocol.NamedProposalRows.carriedRows a b)
  eligibleBody := Protocol.NamedProposalRows.eligibleBody
  orderedBodies := fun a => pure (Protocol.NamedProposalRows.orderedBodies a)
  poolRows := Protocol.NamedProposalRows.poolRows
  st := fun x => x.st
  record := fun x => x.record
  cache := fun x => x.cache
  gradeContract := Execution.NamedProfile.gradeContract
  initial := fun _ _ => Execution.NamedNode.initial
  wake := id
  wakeEvents := false
  runs_as := fun _ _ => True
  reachedNode := fun _ => True
  reachedStore := fun _ => True
  reachedCore := fun _ => True
  reachedRead := fun _ _ => True
  chainStateInTree := fun _ _ => True
  rootFresh := fun _ _ => True
  awake_for_grade1 := fun _ _ _ _ => True
  awake_for_grade2 := fun S v _ r => (S.node v).awake r = true
  tick := fun S v n t => pure (Execution.NamedNode.tick S v n t)
  process := fun S n o => pure (Execution.NamedNode.process S n o)
  postCore := Execution.NamedReceiptCalls.postCore
  receipt_process := Execution.NamedReceipt.process
  make_grades_compatible_with_finalized := id
  mkNode := fun st r c => ⟨st, r, c⟩
  chain_attestations := DecoupledConsensusModel.chain_attestations
  HasSlashableWeightBetween := DecoupledConsensusModel.HasSlashableWeightBetween
  store_attestations := DecoupledConsensusModel.store_attestations
  SlashableBetween := DecoupledConsensusModel.SlashableBetween
  HasIntersectionWeight := DecoupledConsensusModel.HasIntersectionWeight

end DecoupledConsensusModel.Sts.Record
