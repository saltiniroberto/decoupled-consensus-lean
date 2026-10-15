import Proofs.Instance.Members.ChainStateToHandlers
import Proofs.Instance.Members.ForkChoiceGrades
import Proofs.Instance.Members.DutiesNode
import Proofs.Instance.StoreOk
import Proofs.Instance.RunInvariant

/-!
# The spec's model as an instance of the record

`Model.specDraft` fills every member of the record `Model V` with the spec's types and routines, the
stores and node states restricted to those that meet `NoRaise.StoreOk` (`OkStore V`, `OkNode V`).
`Model.specDraftBase` is the same model at the spec's unrestricted store and node types. The members
that add a block to the tree are defined in the namespace `SpecDraftRecord.OkMember`.
-/

set_option autoImplicit false

namespace SpecDraftRecord.OkMember

open DecoupledConsensusModel (Block NamedBlock Env TimestampMap)
open DecoupledConsensusModel.Protocol (HeightConfig HealConfig CarriedAdmission)
open SpecDraftRecord.NoRaise
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-- Record member `on_block_with` on `OkStore V`: `Member.on_block_with` at the store's value,
    except that the store is returned unchanged when another block of its tree has the root of
    `Block.toSpecNamed B` (`RootHeldByOther`). -/
def on_block_with (adm : CarriedAdmission) (E : Env V) (hc : HealConfig) (cfg : HeightConfig)
    (st : OkStore V) (B : NamedBlock V) : OkStore V :=
  if h : RootHeldByOther st.val.T (Spec.Block.toSpecNamed B) then st
  else ⟨Member.on_block_with adm E hc cfg st.val B, OkStore.on_block _ _ st.property h⟩

/-- Record member `ns_process_block_core` on `OkStore V`: `Member.ns_process_block_core` at the
    store's value, except that the store is returned unchanged when another block of its tree has
    the root of `Block.toSpecNamed B` (`RootHeldByOther`). -/
def ns_process_block_core (E : Env V) (hc : HealConfig) (cfg : HeightConfig) (st : OkStore V)
    (B : NamedBlock V) : OkStore V :=
  if h : RootHeldByOther st.val.T (Spec.Block.toSpecNamed B) then st
  else ⟨Member.ns_process_block_core E hc cfg st.val B, OkStore.admitBlockCore _ _ st.property h⟩

/-- Record member `on_block_using` on `OkStore V`: `Member.on_block_using` at the store's value,
    except that the store is returned unchanged when another block of its tree has the root of
    `st.val.blockOfImage B` (`RootHeldByOther`). -/
def on_block_using (E : Env V) (st : OkStore V) (B : Block V)
    (buildState : Member.CS V → Member.CS V) : OkStore V :=
  if h : RootHeldByOther st.val.T (st.val.blockOfImage B) then st
  else ⟨Member.on_block_using E st.val B buildState, OkStore.onBlockUsing _ st.property h _⟩

/-- Record member `postCore` on `OkStore V`: `Member.postCore` at the store's value, except that the
    store is returned unchanged when another block of its tree has the root of `Block.toSpecNamed B`
    (`RootHeldByOther`). -/
def postCore (S : DecoupledConsensusModel.Execution.Setup V) (st : OkStore V)
    (B : NamedBlock V) : OkStore V :=
  if h : RootHeldByOther st.val.T (Spec.Block.toSpecNamed B) then st
  else ⟨Member.postCore S st.val B, OkStore.admitBlockCore _ _ st.property h⟩

/-- Record member `receipt_process` on `OkStore V`: `Member.receipt_process` at the store's value,
    except that the store is returned unchanged when `o` is a block whose root another block of the
    tree has (`objectRootHeldByOther`). -/
def receipt_process (S : DecoupledConsensusModel.Execution.Setup V) (st : OkStore V)
    (o : DecoupledConsensusModel.Execution.NamedObject V) : OkStore V :=
  if h : objectRootHeldByOther st.val.T o then st
  else ⟨Member.receipt_process S st.val o, OkStore.receipt_process S st.property h⟩

/-- Record member `store_with_σ_T_timestamp_block` on `OkStore V`: `st` with the chain states `σ'`
    written, and also the tree `T'` and the block stamps `τ'` when the written store meets `TreeOk`. -/
def store_with_σ_T_timestamp_block (st : OkStore V) (σ' : Block V → Member.CS V)
    (T' : Finset (Block V)) (τ' : TimestampMap (Block V)) : OkStore V :=
  if h : TreeOk (Member.store_with_σ_T_timestamp_block st.val σ' T' τ') then
    ⟨Member.store_with_σ_T_timestamp_block st.val σ' T' τ', OkStore.of_treeOk st.property _ _ _ h⟩
  else ⟨{ st.val with σ := fun B => σ' B.toProof }, st.property⟩

/-- Record member `on_block_checked_using` on `OkStore V`: `handle st` when every attestation `B`
    includes passes `Protocol.included_attestations_admissible`, and `st` otherwise. -/
def on_block_checked_using (handle : OkStore V → OkStore V) (hc : HealConfig) (st : OkStore V)
    (B : Block V) : OkStore V :=
  if Spec.Protocol.included_attestations_admissible
      (Spec.Config.toSpec (ChainStateToHandlers.unreadEnv (V := V)) hc
        unreadHeightConfig) (Spec.Block.toSpec B) then handle st
  else st

/-- Record member `mkContract` on `OkStore V`: the initial saved grades
    `Protocol.initial_saved_grades`, whatever the four arguments. -/
def mkContract
    (_rd : Env V → HealConfig → OkStore V → DecoupledConsensusModel.Round →
      DecoupledConsensusModel.Protocol.GradeRead V)
    (_sv : OkStore V → DecoupledConsensusModel.Protocol.GradeRead V → Block V)
    (_sel : Env V → HealConfig → OkStore V → DecoupledConsensusModel.Slot → Option (Block V))
    (_sr : Env V → HealConfig → OkStore V → DecoupledConsensusModel.Round → Option (Block V)) :
    Spec.SavedGrades V :=
  Spec.Protocol.initial_saved_grades

/-! ## The two cases of each admitting member -/

/-- `on_block_with` returns `st` when another block of the tree has the root of
    `Block.toSpecNamed B`. -/
theorem on_block_with_of_held {adm : CarriedAdmission} {E : Env V} {hc : HealConfig}
    {cfg : HeightConfig} {st : OkStore V} {B : NamedBlock V}
    (h : RootHeldByOther st.val.T (Spec.Block.toSpecNamed B)) :
    on_block_with adm E hc cfg st B = st := dif_pos h

/-- When no other block of the tree has the root of `Block.toSpecNamed B`, the value of
    `on_block_with` is `Member.on_block_with` at the store's value. -/
theorem on_block_with_val_of_not_held {adm : CarriedAdmission} {E : Env V} {hc : HealConfig}
    {cfg : HeightConfig} {st : OkStore V} {B : NamedBlock V}
    (h : ¬ RootHeldByOther st.val.T (Spec.Block.toSpecNamed B)) :
    (on_block_with adm E hc cfg st B).val = Member.on_block_with adm E hc cfg st.val B := by
  unfold on_block_with
  rw [dif_neg h]

/-- `ns_process_block_core` returns `st` when another block of the tree has the root of
    `Block.toSpecNamed B`. -/
theorem ns_process_block_core_of_held {E : Env V} {hc : HealConfig} {cfg : HeightConfig}
    {st : OkStore V} {B : NamedBlock V}
    (h : RootHeldByOther st.val.T (Spec.Block.toSpecNamed B)) :
    ns_process_block_core E hc cfg st B = st := dif_pos h

/-- When no other block of the tree has the root of `Block.toSpecNamed B`, the value of
    `ns_process_block_core` is `Member.ns_process_block_core` at the store's value. -/
theorem ns_process_block_core_val_of_not_held {E : Env V} {hc : HealConfig} {cfg : HeightConfig}
    {st : OkStore V} {B : NamedBlock V}
    (h : ¬ RootHeldByOther st.val.T (Spec.Block.toSpecNamed B)) :
    (ns_process_block_core E hc cfg st B).val = Member.ns_process_block_core E hc cfg st.val B := by
  unfold ns_process_block_core
  rw [dif_neg h]

/-- When no other block of the tree has the root of `st.val.blockOfImage B`, the value of
    `on_block_using` is `Member.on_block_using` at the store's value. -/
theorem on_block_using_val_of_not_held {E : Env V} {st : OkStore V} {B : Block V}
    {buildState : Member.CS V → Member.CS V}
    (h : ¬ RootHeldByOther st.val.T (st.val.blockOfImage B)) :
    (on_block_using E st B buildState).val = Member.on_block_using E st.val B buildState := by
  unfold on_block_using
  rw [dif_neg h]

/-- `postCore` returns `st` when another block of the tree has the root of `Block.toSpecNamed B`. -/
theorem postCore_of_held {S : DecoupledConsensusModel.Execution.Setup V} {st : OkStore V}
    {B : NamedBlock V} (h : RootHeldByOther st.val.T (Spec.Block.toSpecNamed B)) :
    postCore S st B = st := dif_pos h

/-- When no other block of the tree has the root of `Block.toSpecNamed B`, the value of `postCore`
    is `Member.postCore` at the store's value. -/
theorem postCore_val_of_not_held {S : DecoupledConsensusModel.Execution.Setup V} {st : OkStore V}
    {B : NamedBlock V} (h : ¬ RootHeldByOther st.val.T (Spec.Block.toSpecNamed B)) :
    (postCore S st B).val = Member.postCore S st.val B := by
  unfold postCore
  rw [dif_neg h]

/-- `receipt_process` returns `st` when `o` is a block whose root another block of the tree has. -/
theorem receipt_process_of_held {S : DecoupledConsensusModel.Execution.Setup V} {st : OkStore V}
    {o : DecoupledConsensusModel.Execution.NamedObject V} (h : objectRootHeldByOther st.val.T o) :
    receipt_process S st o = st := dif_pos h

/-- When `o` is not a block whose root another block of the tree has, the value of `receipt_process`
    is `Member.receipt_process` at the store's value. -/
theorem receipt_process_val_of_not_held {S : DecoupledConsensusModel.Execution.Setup V}
    {st : OkStore V} {o : DecoupledConsensusModel.Execution.NamedObject V}
    (h : ¬ objectRootHeldByOther st.val.T o) :
    (receipt_process S st o).val = Member.receipt_process S st.val o := by
  unfold receipt_process
  rw [dif_neg h]

end SpecDraftRecord.OkMember

namespace DecoupledConsensusModel.Sts.Record

open SpecDraftRecord

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-- The spec's model at the spec's own types: the type members are the spec's types, and every other
    member is `SpecDraftRecord.Member.<member>`. -/
def Model.specDraftBase : Model V where
  CS := Spec.Protocol.ChainState V
  h := Member.h
  T_h := Member.T_h
  nj := Member.nj
  J := Member.J
  h_j := Member.h_j
  F := Member.F
  h_F := Member.h_F
  progress := Member.progress
  target_participation := Member.target_participation
  Binding := Member.Binding V
  targeted := Member.targeted
  process_attestation := Member.process_attestation
  process_attestation_with := Member.process_attestation_with
  fold_rows := Member.fold_rows
  process_height_events := Member.process_height_events
  finalityReady := Member.finalityReady
  targetReady := Member.targetReady
  progReady := Member.progReady
  named_transition := Member.named_transition
  derive_named := Member.derive_named
  conflictsWithFinality := Member.conflictsWithFinality
  e2Fields := Member.e2Fields
  Slashable := Member.Slashable
  GS := Spec.Store V
  S := Spec.Store V
  SGS := Spec.Store V
  FGS := Spec.Store V
  R := Spec.SigningHistory
  NR := Spec.SigningHistory
  HS := Spec.Store V
  GV := Spec.Store V
  Frame := Spec.RoundGrades V
  Cache := Spec.SavedGrades V
  Contract := Spec.SavedGrades V
  NS := Spec.Store V
  N := Spec.NodeState V
  L := Member.L
  cs_s := Member.cs_s
  finalize := Member.finalize
  cs_initial := Member.cs_initial
  advance_height := Member.advance_height
  slashable := Member.slashable
  e1Fields := Member.e1Fields
  e1Slashable := Member.e1Slashable
  e2Slashable := Member.e2Slashable
  sameValidator := Member.sameValidator
  transition_rows := Member.transition_rows
  nonjustifiable := Member.nonjustifiable
  cs_with_F_h_F := Member.cs_with_F_h_F
  proposal_time := Member.proposal_time
  proposal_wake_start := Member.proposal_wake_start
  vote_time := Member.vote_time
  support_cutoff := Member.support_cutoff
  view_freeze := Member.view_freeze
  confirmation_time := Member.confirmation_time
  votes_by := Member.votes_by
  equivocates := Member.equivocates
  participates := Member.participates
  gs_s := Member.gs_s
  gs_T := Member.gs_T
  gs_timestamp_block := Member.gs_timestamp_block
  gs_timestamp_vote := Member.gs_timestamp_vote
  gs_gf_votes := Member.gs_gf_votes
  gs_live_confirmed := Member.gs_live_confirmed
  store_t := Member.store_t
  store_s := Member.store_s
  store_T := Member.store_T
  store_timestamp_block := Member.store_timestamp_block
  store_timestamp_vote := Member.store_timestamp_vote
  store_timestamp_sg_vote := Member.store_timestamp_sg_vote
  store_σ := Member.store_σ
  store_gf_votes := Member.store_gf_votes
  store_sg_votes := Member.store_sg_votes
  store_F := Member.store_F
  store_J := Member.store_J
  store_h_j := Member.store_h_j
  store_h_max := Member.store_h_max
  store_live_confirmed := Member.store_live_confirmed
  store_latest_confirmed := Member.store_latest_confirmed
  store_latest_stable := Member.store_latest_stable
  store_tau := Member.store_tau
  toHealing := Member.toHealing
  store_pool := Member.store_pool
  sgVote := Member.sgVote
  store_sg_pool := Member.store_sg_pool
  resolved := Member.resolved
  gs_pool := Member.gs_pool
  gs_tau := Member.gs_tau
  store_with_t_s := Member.store_with_t_s
  store_with_h_max := Member.store_with_h_max
  store_with_J_h_j := Member.store_with_J_h_j
  store_with_σ_T_timestamp_block := Member.store_with_σ_T_timestamp_block
  store_init := Member.store_init
  toGoldfishStore := Member.toGoldfishStore
  sgs_sg_votes := Member.sgs_sg_votes
  toSG := Member.toSG
  fg_σ := Member.fg_σ
  fg_F := Member.fg_F
  fg_J := Member.fg_J
  fg_h_j := Member.fg_h_j
  fg_h_max := Member.fg_h_max
  get_fg_root := Member.get_fg_root
  get_filtered_block_tree := Member.get_filtered_block_tree
  get_sg_root_with := Member.get_sg_root_with
  voter_processed_block_tree := Member.voter_processed_block_tree
  voter_view := Member.voter_view
  voters_count := Member.voters_count
  latest_window := Member.latest_window
  goldfish_score := Member.goldfish_score
  voter_support_view := Member.voter_support_view
  proposer_view := Member.proposer_view
  get_head_with := Member.get_head_with
  ghost := Member.ghost
  proposer_support_view := Member.proposer_support_view
  goldfish_eligible := Member.goldfish_eligible
  targets_under := Member.targets_under
  goldfish_fork_choice := Member.goldfish_fork_choice
  get_head_in_tree_with_layer := Member.get_head_in_tree_with_layer
  viable_tree := Member.viable_tree
  no_second_vote_in := Member.no_second_vote_in
  viable := Member.viable
  finalized_descendants := Member.finalized_descendants
  ghost_step := Member.ghost_step
  get_filtered_block_tree_from := Member.get_filtered_block_tree_from
  raw_participants := Member.raw_participants
  raw_supporters := Member.raw_supporters
  target := Member.target
  timeout := Member.timeout
  lock := Member.lock
  legacy := Member.legacy
  nr_timeoutHistory := Member.nr_timeoutHistory
  own_lock := Member.own_lock
  height_pair := Member.height_pair
  create_attestation := Member.create_attestation
  finality_pair := Member.finality_pair
  encodeHeight := Member.encodeHeight
  record_attestation := Member.record_attestation
  toFG := Member.toFG
  gv_T := Member.gv_T
  gv_timestamp_block := Member.gv_timestamp_block
  gv_tree := Member.gv_tree
  gv_sg_votes := Member.gv_sg_votes
  gv_timestamp_sg_vote := Member.gv_timestamp_sg_vote
  g0 := Member.g0
  g1 := Member.g1
  g2 := Member.g2
  round := Member.round
  cache_current := Member.cache_current
  read := Member.read
  confirmationSG := Member.confirmationSG
  stableRoot := Member.stableRoot
  contract_sgVote := Member.contract_sgVote
  mkContract := Member.mkContract
  opening_slot := Member.opening_slot
  domain := Member.domain
  opening := Member.opening
  round_of := Member.round_of
  gradeView := Member.gradeView
  early := Member.early
  late := Member.late
  gradeBool := Member.gradeBool
  onPhaseTick := Member.onPhaseTick
  readFrame := Member.readFrame
  a := Member.a
  phaseResult := Member.phaseResult
  activePrefix := Member.activePrefix
  rawView := Member.rawView
  clipCache := Member.clipCache
  clipGrade := Member.clipGrade
  rawInputs := Member.rawInputs
  frameContract := Member.frameContract
  readyView := Member.readyView
  currentSGVote := Member.currentSGVote
  cacheAtRound := Member.cacheAtRound
  interpretedInputs := Member.interpretedInputs
  freezeRoot := Member.freezeRoot
  anchor := Member.anchor
  localCovers := Member.localCovers
  positive := Member.positive
  grade2Block := Member.grade2Block
  deepest_clear := Member.deepest_clear
  frameStableRoot := Member.frameStableRoot
  opposing := Member.opposing
  token := Member.token
  head_covers := Member.head_covers
  clipResult := Member.clipResult
  frameSGCandidate := Member.frameSGCandidate
  allClosed := Member.allClosed
  bodyReady := Member.bodyReady
  frameGradeRead := Member.frameGradeRead
  Opposes := Member.Opposes
  Supports := Member.Supports
  CleanFrom := Member.CleanFrom
  clipFrame := Member.clipFrame
  alignRound := Member.alignRound
  pendingFrame := Member.pendingFrame
  domainOffset := Member.domainOffset
  earlyOffset := Member.earlyOffset
  lateOffset := Member.lateOffset
  clear := Member.clear
  chain_of := Member.chain_of
  putPhase := Member.putPhase
  chain_up := Member.chain_up
  core := Member.core
  sameCore := Member.sameCore
  bodies := Member.bodies
  sg_rows := Member.sg_rows
  ns_setClock := Member.ns_setClock
  get_stable := Member.get_stable
  round_votes := Member.round_votes
  on_block_with := Member.on_block_with
  admit_row := Member.admit_row
  update_confirmation_with := Member.update_confirmation_with
  on_goldfish_vote_checked := Member.on_goldfish_vote_checked
  get_confirmed := Member.get_confirmed
  carried_attestations_admissible := Member.carried_attestations_admissible
  on_sg_vote := Member.on_sg_vote
  admit_rows := Member.admit_rows
  advance_confirmed := Member.advance_confirmed
  ns_process_block_core := Member.ns_process_block_core
  voter_filtered_block_tree := Member.voter_filtered_block_tree
  floor_on_stable := Member.floor_on_stable
  on_block_using := Member.on_block_using
  on_block_checked_using := Member.on_block_checked_using
  on_goldfish_vote := Member.on_goldfish_vote
  goldfish_vote_with := Member.goldfish_vote_with
  ns_initial := Member.ns_initial
  update_finality := Member.update_finality
  admit_carried := Member.admit_carried
  get_head_in_tree_with := Member.get_head_in_tree_with
  state_transition := Member.state_transition
  ns_with_core := Member.ns_with_core
  commitBlock := Member.commitBlock
  duties_propose_block_with := Member.duties_propose_block_with
  duties_attest_with := Member.duties_attest_with
  duties_update_confirmation_with := Member.duties_update_confirmation_with
  inWindow := Member.inWindow
  round_action_with := Member.round_action_with
  duties_goldfish_vote_with := Member.duties_goldfish_vote_with
  grade2_block_with := Member.grade2_block_with
  proposal_with := Member.proposal_with
  select := Member.select
  parentBody? := Member.parentBody?
  proposalRows := Member.proposalRows
  fg_source_with := Member.fg_source_with
  get_sg_vote_with := Member.get_sg_vote_with
  processedRows := Member.processedRows
  with_proposal_input := Member.with_proposal_input
  creatorInput := Member.creatorInput
  get_fg_vote_with := Member.get_fg_vote_with
  chainRows := Member.chainRows
  with_attestation_input := Member.with_attestation_input
  carriedRows := Member.carriedRows
  eligibleBody := Member.eligibleBody
  orderedBodies := Member.orderedBodies
  poolRows := Member.poolRows
  st := Member.st
  record := Member.record
  cache := Member.cache
  gradeContract := Member.gradeContract
  initial := Member.initial
  wake := Member.wake
  wakeEvents := Member.wakeEvents
  runs_as := Member.runs_as
  reachedNode := fun n => SubtypeEqualities.RunStoreInv n.st ∧ HandlersRunFacts.ConfirmedInTree n.st ∧
    Spec.Store.ContractInTree n.st.T n.st.saved_grades
  reachedStore := fun st => SubtypeEqualities.RunStoreInv st ∧ HandlersRunFacts.ConfirmedInTree st ∧
    Spec.Store.ContractInTree st.T st.saved_grades
  reachedCore := fun st => SubtypeEqualities.RunStoreInv st ∧ HandlersRunFacts.ConfirmedInTree st ∧
    Spec.Store.ContractInTree st.T st.saved_grades
  reachedRead := fun st c => SubtypeEqualities.RunStoreInv st ∧ HandlersRunFacts.ConfirmedInTree st ∧
    Spec.Store.ContractInTree st.T c
  chainStateInTree := fun st σ => σ.F ∈ st.T ∧ σ.J ∈ st.T ∧ st.J ∈ st.T
  rootFresh := fun st B => ∀ C ∈ Member.store_T st, C.root = B.root → C = B
  awake_for_grade1 := Member.awake_for_grade1
  awake_for_grade2 := Member.awake_for_grade2
  tick := Member.tick
  process := Member.process
  postCore := Member.postCore
  receipt_process := Member.receipt_process
  make_grades_compatible_with_finalized := Member.make_grades_compatible_with_finalized
  mkNode := Member.mkNode
  store_with_cache := Member.store_with_cache
  contractCache := Member.contractCache
  chain_attestations := Member.chain_attestations
  HasSlashableWeightBetween := Member.HasSlashableWeightBetween
  store_attestations := Member.store_attestations
  SlashableBetween := Member.SlashableBetween
  HasIntersectionWeight := Member.HasIntersectionWeight

/-- The spec's model: the type members are the spec's types with the stores and node states
    restricted to those whose store meets `StoreOk` (`OkStore V`, `OkNode V`), and every other
    member is `SpecDraftRecord.Member.<member>` read on those types, or
    `SpecDraftRecord.OkMember.<member>`. -/
def Model.specDraft : Model V where
  CS := Spec.Protocol.ChainState V
  h := Member.h
  T_h := Member.T_h
  nj := Member.nj
  J := Member.J
  h_j := Member.h_j
  F := Member.F
  h_F := Member.h_F
  progress := Member.progress
  target_participation := Member.target_participation
  Binding := Member.Binding V
  targeted := Member.targeted
  process_attestation := Member.process_attestation
  process_attestation_with := Member.process_attestation_with
  fold_rows := Member.fold_rows
  process_height_events := Member.process_height_events
  finalityReady := Member.finalityReady
  targetReady := Member.targetReady
  progReady := Member.progReady
  named_transition := Member.named_transition
  derive_named := Member.derive_named
  conflictsWithFinality := Member.conflictsWithFinality
  e2Fields := Member.e2Fields
  Slashable := Member.Slashable
  GS := OkStore V
  S := OkStore V
  SGS := OkStore V
  FGS := OkStore V
  R := Spec.SigningHistory
  NR := Spec.SigningHistory
  HS := OkStore V
  GV := OkStore V
  Frame := Spec.RoundGrades V
  Cache := Spec.SavedGrades V
  Contract := Spec.SavedGrades V
  NS := OkStore V
  N := OkNode V
  L := Member.L
  cs_s := Member.cs_s
  finalize := Member.finalize
  cs_initial := Member.cs_initial
  advance_height := Member.advance_height
  slashable := Member.slashable
  e1Fields := Member.e1Fields
  e1Slashable := Member.e1Slashable
  e2Slashable := Member.e2Slashable
  sameValidator := Member.sameValidator
  transition_rows := Member.transition_rows
  nonjustifiable := Member.nonjustifiable
  cs_with_F_h_F := Member.cs_with_F_h_F
  proposal_time := Member.proposal_time
  proposal_wake_start := Member.proposal_wake_start
  vote_time := Member.vote_time
  support_cutoff := Member.support_cutoff
  view_freeze := Member.view_freeze
  confirmation_time := Member.confirmation_time
  votes_by := Member.votes_by
  equivocates := Member.equivocates
  participates := Member.participates
  gs_s := fun st => Member.gs_s st.val
  gs_T := fun st => Member.gs_T st.val
  gs_timestamp_block := fun st => Member.gs_timestamp_block st.val
  gs_timestamp_vote := fun st => Member.gs_timestamp_vote st.val
  gs_gf_votes := fun st a1 => Member.gs_gf_votes st.val a1
  gs_live_confirmed := fun st => Member.gs_live_confirmed st.val
  store_t := fun st => Member.store_t st.val
  store_s := fun st => Member.store_s st.val
  store_T := fun st => Member.store_T st.val
  store_timestamp_block := fun st => Member.store_timestamp_block st.val
  store_timestamp_vote := fun st => Member.store_timestamp_vote st.val
  store_timestamp_sg_vote := fun st => Member.store_timestamp_sg_vote st.val
  store_σ := fun st a1 => Member.store_σ st.val a1
  store_gf_votes := fun st a1 => Member.store_gf_votes st.val a1
  store_sg_votes := fun st a1 => Member.store_sg_votes st.val a1
  store_F := fun st => Member.store_F st.val
  store_J := fun st => Member.store_J st.val
  store_h_j := fun st => Member.store_h_j st.val
  store_h_max := fun st => Member.store_h_max st.val
  store_live_confirmed := fun st => Member.store_live_confirmed st.val
  store_latest_confirmed := fun st => Member.store_latest_confirmed st.val
  store_latest_stable := fun st => Member.store_latest_stable st.val
  store_tau := fun st => Member.store_tau st.val
  toHealing := fun st => ⟨Member.toHealing st.val, st.property⟩
  store_pool := fun st a1 => Member.store_pool st.val a1
  sgVote := Member.sgVote
  store_sg_pool := fun st a1 => Member.store_sg_pool st.val a1
  resolved := Member.resolved
  gs_pool := fun st a1 => Member.gs_pool st.val a1
  gs_tau := fun st => Member.gs_tau st.val
  store_with_t_s := fun st a1 a2 => ⟨Member.store_with_t_s st.val a1 a2, st.property⟩
  store_with_h_max := fun st a1 => ⟨Member.store_with_h_max st.val a1, st.property⟩
  store_with_J_h_j := fun st a1 a2 => ⟨Member.store_with_J_h_j st.val a1 a2, st.property⟩
  store_with_σ_T_timestamp_block := OkMember.store_with_σ_T_timestamp_block
  store_init := ⟨Member.store_init, OkStore.init⟩
  toGoldfishStore := fun st => ⟨Member.toGoldfishStore st.val, st.property⟩
  sgs_sg_votes := fun st a1 => Member.sgs_sg_votes st.val a1
  toSG := fun st => ⟨Member.toSG st.val, st.property⟩
  fg_σ := fun st a1 => Member.fg_σ st.val a1
  fg_F := fun st => Member.fg_F st.val
  fg_J := fun st => Member.fg_J st.val
  fg_h_j := fun st => Member.fg_h_j st.val
  fg_h_max := fun st => Member.fg_h_max st.val
  get_fg_root := fun st => Member.get_fg_root st.val
  get_filtered_block_tree := fun st => Member.get_filtered_block_tree st.val
  get_sg_root_with := fun a1 a2 a3 st a4 => Member.get_sg_root_with a1 a2 a3 st.val a4
  voter_processed_block_tree := fun a1 st a2 => Member.voter_processed_block_tree a1 st.val a2
  voter_view := fun a1 st a2 => Member.voter_view a1 st.val a2
  voters_count := Member.voters_count
  latest_window := Member.latest_window
  goldfish_score := Member.goldfish_score
  voter_support_view := fun a1 st a2 => Member.voter_support_view a1 st.val a2
  proposer_view := fun st a1 => Member.proposer_view st.val a1
  get_head_with := fun a1 a2 a3 st a4 a5 a6 => Member.get_head_with a1 a2 a3 st.val a4 a5 a6
  ghost := Member.ghost
  proposer_support_view := fun st a1 => Member.proposer_support_view st.val a1
  goldfish_eligible := Member.goldfish_eligible
  targets_under := Member.targets_under
  goldfish_fork_choice := Member.goldfish_fork_choice
  get_head_in_tree_with_layer := fun a1 a2 a3 st a4 a5 a6 a7 =>
    Member.get_head_in_tree_with_layer a1 a2 a3 st.val a4 a5 a6 a7
  viable_tree := Member.viable_tree
  no_second_vote_in := Member.no_second_vote_in
  viable := Member.viable
  finalized_descendants := Member.finalized_descendants
  ghost_step := Member.ghost_step
  get_filtered_block_tree_from := fun st a1 => Member.get_filtered_block_tree_from st.val a1
  raw_participants := Member.raw_participants
  raw_supporters := Member.raw_supporters
  target := Member.target
  timeout := Member.timeout
  lock := Member.lock
  legacy := Member.legacy
  nr_timeoutHistory := Member.nr_timeoutHistory
  own_lock := Member.own_lock
  height_pair := Member.height_pair
  create_attestation := Member.create_attestation
  finality_pair := Member.finality_pair
  encodeHeight := Member.encodeHeight
  record_attestation := Member.record_attestation
  toFG := fun st => ⟨Member.toFG st.val, st.property⟩
  gv_T := fun st => Member.gv_T st.val
  gv_timestamp_block := fun st => Member.gv_timestamp_block st.val
  gv_tree := fun st => Member.gv_tree st.val
  gv_sg_votes := fun st a1 => Member.gv_sg_votes st.val a1
  gv_timestamp_sg_vote := fun st => Member.gv_timestamp_sg_vote st.val
  g0 := Member.g0
  g1 := Member.g1
  g2 := Member.g2
  round := Member.round
  cache_current := Member.cache_current
  read := fun a1 a2 a3 st a4 => Member.read a1 a2 a3 st.val a4
  confirmationSG := fun a1 a2 a3 st a4 => Member.confirmationSG a1 a2 a3 st.val a4
  stableRoot := fun a1 a2 a3 st a4 => Member.stableRoot a1 a2 a3 st.val a4
  contract_sgVote := fun a1 st a2 => Member.contract_sgVote a1 st.val a2
  mkContract := OkMember.mkContract
  opening_slot := Member.opening_slot
  domain := Member.domain
  opening := Member.opening
  round_of := Member.round_of
  gradeView := fun st => ⟨Member.gradeView st.val, st.property⟩
  early := Member.early
  late := Member.late
  gradeBool := fun a1 st a2 a3 a4 a5 a6 a7 => Member.gradeBool a1 st.val a2 a3 a4 a5 a6 a7
  onPhaseTick := fun a1 a2 st a3 a4 => Member.onPhaseTick a1 a2 st.val a3 a4
  readFrame := fun a1 st a2 => Member.readFrame a1 st.val a2
  a := Member.a
  phaseResult := Member.phaseResult
  activePrefix := Member.activePrefix
  rawView := fun st a1 a2 a3 a4 => Member.rawView st.val a1 a2 a3 a4
  clipCache := Member.clipCache
  clipGrade := Member.clipGrade
  rawInputs := fun st a1 a2 a3 a4 => Member.rawInputs st.val a1 a2 a3 a4
  frameContract := Member.frameContract
  readyView := fun st a1 a2 a3 a4 a5 => Member.readyView st.val a1 a2 a3 a4 a5
  currentSGVote := fun st a1 => Member.currentSGVote st.val a1
  cacheAtRound := Member.cacheAtRound
  interpretedInputs := fun st a1 a2 a3 a4 a5 => Member.interpretedInputs st.val a1 a2 a3 a4 a5
  freezeRoot := fun a1 st a2 a3 a4 a5 a6 => Member.freezeRoot a1 st.val a2 a3 a4 a5 a6
  anchor := fun a1 a2 st a3 a4 => Member.anchor a1 a2 st.val a3 a4
  localCovers := fun st a1 a2 => Member.localCovers st.val a1 a2
  positive := fun st a1 a2 a3 a4 a5 a6 a7 => Member.positive st.val a1 a2 a3 a4 a5 a6 a7
  grade2Block := fun st a1 => Member.grade2Block st.val a1
  deepest_clear := Member.deepest_clear
  frameStableRoot := fun a1 a2 a3 st a4 => Member.frameStableRoot a1 a2 a3 st.val a4
  opposing := fun st a1 a2 a3 a4 a5 a6 a7 => Member.opposing st.val a1 a2 a3 a4 a5 a6 a7
  token := Member.token
  head_covers := Member.head_covers
  clipResult := Member.clipResult
  frameSGCandidate := fun a1 a2 a3 st a4 => Member.frameSGCandidate a1 a2 a3 st.val a4
  allClosed := Member.allClosed
  bodyReady := fun st a1 a2 a3 => Member.bodyReady st.val a1 a2 a3
  frameGradeRead := fun a1 a2 a3 st a4 => Member.frameGradeRead a1 a2 a3 st.val a4
  Opposes := Member.Opposes
  Supports := Member.Supports
  CleanFrom := Member.CleanFrom
  clipFrame := Member.clipFrame
  alignRound := Member.alignRound
  pendingFrame := Member.pendingFrame
  domainOffset := Member.domainOffset
  earlyOffset := Member.earlyOffset
  lateOffset := Member.lateOffset
  clear := Member.clear
  chain_of := Member.chain_of
  putPhase := Member.putPhase
  chain_up := Member.chain_up
  core := fun st => ⟨Member.core st.val, st.property⟩
  sameCore := fun st st2 => Member.sameCore st.val st2.val
  bodies := fun st => Member.bodies st.val
  sg_rows := fun st a1 => Member.sg_rows st.val a1
  ns_setClock := fun a1 st a2 => ⟨Member.ns_setClock a1 st.val a2, st.property⟩
  get_stable := fun st => Member.get_stable st.val
  round_votes := fun st a1 => Member.round_votes st.val a1
  on_block_with := OkMember.on_block_with
  admit_row := fun a1 st a2 =>
    ⟨Member.admit_row a1 st.val a2, OkStore.admit_attestation _ st.property _⟩
  update_confirmation_with := fun a1 a2 a3 st a4 =>
    preimageOutcomes Subtype.val (Member.update_confirmation_with a1 a2 a3 st.val a4)
  on_goldfish_vote_checked := fun a1 st a2 =>
    ⟨Member.on_goldfish_vote_checked a1 st.val a2, OkStore.on_goldfish_vote_checked _ st.property _⟩
  get_confirmed := fun st => Member.get_confirmed st.val
  carried_attestations_admissible := Member.carried_attestations_admissible
  on_sg_vote := fun a1 st a2 =>
    ⟨Member.on_sg_vote a1 st.val a2, OkStore.admit_attestation _ st.property _⟩
  admit_rows := fun a1 st a2 =>
    ⟨Member.admit_rows a1 st.val a2, OkStore.admit_attestations _ st.property _⟩
  advance_confirmed := Member.advance_confirmed
  ns_process_block_core := OkMember.ns_process_block_core
  voter_filtered_block_tree := fun a1 st a2 => Member.voter_filtered_block_tree a1 st.val a2
  floor_on_stable := Member.floor_on_stable
  on_block_using := OkMember.on_block_using
  on_block_checked_using := OkMember.on_block_checked_using
  on_goldfish_vote := fun st a1 =>
    ⟨Member.on_goldfish_vote st.val a1, OkStore.on_goldfish_vote st.property _⟩
  goldfish_vote_with := fun a1 a2 a3 a4 st =>
    preimageOutcomes (Prod.map Subtype.val id) (Member.goldfish_vote_with a1 a2 a3 a4 st.val)
  ns_initial := ⟨Member.ns_initial, OkStore.init⟩
  update_finality := fun st a1 =>
    ⟨Member.update_finality st.val a1, OkStore.updateFinalityWith st.property _⟩
  admit_carried := fun a1 a2 st st2 a3 =>
    ⟨Member.admit_carried a1 a2 st.val st2.val a3, OkStore.admitCarried _ _ st2.property _⟩
  get_head_in_tree_with := fun a1 a2 a3 st a4 a5 a6 a7 =>
    Member.get_head_in_tree_with a1 a2 a3 st.val a4 a5 a6 a7
  state_transition := Member.state_transition
  ns_with_core := fun st st2 => ⟨Member.ns_with_core st.val st2.val, st2.property⟩
  commitBlock := fun st st2 a1 => ⟨Member.commitBlock st.val st2.val a1, st2.property⟩
  duties_propose_block_with := fun a1 a2 a3 a4 a5 st =>
    preimageOutcomes (Prod.map Subtype.val id)
      (Member.duties_propose_block_with a1 a2 a3 a4 a5 st.val)
  duties_attest_with := fun a1 a2 a3 a4 st a5 =>
    preimageOutcomes (Prod.map Subtype.val id) (Member.duties_attest_with a1 a2 a3 a4 st.val a5)
  duties_update_confirmation_with := fun a1 a2 a3 st a4 =>
    preimageOutcomes Subtype.val (Member.duties_update_confirmation_with a1 a2 a3 st.val a4)
  inWindow := fun a1 st a2 => Member.inWindow a1 st.val a2
  round_action_with := fun a1 a2 a3 a4 st a5 => Member.round_action_with a1 a2 a3 a4 st.val a5
  duties_goldfish_vote_with := fun a1 a2 a3 a4 st =>
    preimageOutcomes (Prod.map Subtype.val id) (Member.duties_goldfish_vote_with a1 a2 a3 a4 st.val)
  grade2_block_with := fun a1 a2 a3 st a4 => Member.grade2_block_with a1 a2 a3 st.val a4
  proposal_with := fun a1 a2 a3 a4 a5 st => Member.proposal_with a1 a2 a3 a4 a5 st.val
  select := fun a1 a2 st => Member.select a1 a2 st.val
  parentBody? := fun st a1 => Member.parentBody? st.val a1
  proposalRows := Member.proposalRows
  fg_source_with := fun a1 a2 a3 st a4 a5 => Member.fg_source_with a1 a2 a3 st.val a4 a5
  get_sg_vote_with := fun a1 a2 a3 st a4 a5 => Member.get_sg_vote_with a1 a2 a3 st.val a4 a5
  processedRows := fun a1 st => Member.processedRows a1 st.val
  with_proposal_input := fun a1 a2 a3 a4 st a5 => Member.with_proposal_input a1 a2 a3 a4 st.val a5
  creatorInput := Member.creatorInput
  get_fg_vote_with := fun a1 a2 a3 st a4 a5 => Member.get_fg_vote_with a1 a2 a3 st.val a4 a5
  chainRows := Member.chainRows
  with_attestation_input := fun a1 a2 a3 a4 st a5 =>
    Member.with_attestation_input a1 a2 a3 a4 st.val a5
  carriedRows := fun a1 st => Member.carriedRows a1 st.val
  eligibleBody := fun a1 st a2 => Member.eligibleBody a1 st.val a2
  orderedBodies := fun st => Member.orderedBodies st.val
  poolRows := fun a1 st => Member.poolRows a1 st.val
  st := fun n => ⟨Member.st n.val, n.property⟩
  record := fun n => Member.record n.val
  cache := fun n => Member.cache n.val
  gradeContract := Member.gradeContract
  initial := fun a1 a2 => ⟨Member.initial a1 a2, OkStore.init⟩
  wake := fun n => ⟨Member.wake n.val, n.property⟩
  wakeEvents := Member.wakeEvents
  runs_as := fun n a1 => Member.runs_as n.val a1
  reachedNode := fun n => SubtypeEqualities.RunStoreInv n.val.st ∧
    HandlersRunFacts.ConfirmedInTree n.val.st ∧
    Spec.Store.ContractInTree n.val.st.T n.val.st.saved_grades
  reachedStore := fun st => SubtypeEqualities.RunStoreInv st.val ∧
    HandlersRunFacts.ConfirmedInTree st.val ∧ Spec.Store.ContractInTree st.val.T st.val.saved_grades
  reachedCore := fun st => SubtypeEqualities.RunStoreInv st.val ∧
    HandlersRunFacts.ConfirmedInTree st.val ∧ Spec.Store.ContractInTree st.val.T st.val.saved_grades
  reachedRead := fun st c => SubtypeEqualities.RunStoreInv st.val ∧
    HandlersRunFacts.ConfirmedInTree st.val ∧ Spec.Store.ContractInTree st.val.T c
  chainStateInTree := fun st σ => σ.F ∈ st.val.T ∧ σ.J ∈ st.val.T ∧ st.val.J ∈ st.val.T
  rootFresh := fun st B => ∀ C ∈ Member.store_T st.val, C.root = B.root → C = B
  awake_for_grade1 := fun a1 a2 n a3 => Member.awake_for_grade1 a1 a2 n.val a3
  awake_for_grade2 := fun a1 a2 n a3 => Member.awake_for_grade2 a1 a2 n.val a3
  tick := fun a1 a2 n a3 =>
    preimageOutcomes (Prod.map Subtype.val id) (Member.tick a1 a2 n.val a3)
  process := fun a1 n a2 =>
    preimageOutcomes Subtype.val (Member.process a1 n.val a2)
  postCore := OkMember.postCore
  receipt_process := OkMember.receipt_process
  make_grades_compatible_with_finalized := fun st =>
    ⟨Member.make_grades_compatible_with_finalized st.val, st.property⟩
  mkNode := fun st a1 a2 => ⟨Member.mkNode st.val a1 a2, st.property⟩
  store_with_cache := fun st a1 => ⟨Member.store_with_cache st.val a1, st.property⟩
  contractCache := Member.contractCache
  chain_attestations := Member.chain_attestations
  HasSlashableWeightBetween := Member.HasSlashableWeightBetween
  store_attestations := fun st => Member.store_attestations st.val
  SlashableBetween := Member.SlashableBetween
  HasIntersectionWeight := Member.HasIntersectionWeight

end DecoupledConsensusModel.Sts.Record

namespace SpecDraftRecord

open DecoupledConsensusModel.Sts.Record
open SpecDraftRecord.NoRaise

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-- At `Model.specDraft`, the store of a node state a run reaches satisfies `RunStoreInv` and
    `ConfirmedInTree`, and its saved grades name blocks of its tree. -/
theorem reached_elim {n : OkNode V} (hn : (Model.specDraft (V := V)).reachedNode n) :
    SubtypeEqualities.RunStoreInv n.val.st ∧ HandlersRunFacts.ConfirmedInTree n.val.st ∧
      Spec.Store.ContractInTree n.val.st.T n.val.st.saved_grades :=
  hn

/-- At `Model.specDraft`, a named store a run reaches satisfies `RunStoreInv` and `ConfirmedInTree`,
    and its saved grades name blocks of its tree. -/
theorem reachedStore_elim {st : OkStore V} (hst : (Model.specDraft (V := V)).reachedStore st) :
    SubtypeEqualities.RunStoreInv st.val ∧ HandlersRunFacts.ConfirmedInTree st.val ∧
      Spec.Store.ContractInTree st.val.T st.val.saved_grades :=
  hst

/-- At `Model.specDraft`, a store a run reaches satisfies `RunStoreInv` and `ConfirmedInTree`, and
    its saved grades name blocks of its tree. -/
theorem reachedCore_elim {st : OkStore V} (hst : (Model.specDraft (V := V)).reachedCore st) :
    SubtypeEqualities.RunStoreInv st.val ∧ HandlersRunFacts.ConfirmedInTree st.val ∧
      Spec.Store.ContractInTree st.val.T st.val.saved_grades :=
  hst

/-- At `Model.specDraft`, a store a run reaches with the saved grades `c` satisfies `RunStoreInv`
    and `ConfirmedInTree`, and `c` names blocks of its tree. -/
theorem reachedRead_elim {st : OkStore V} {c : Spec.SavedGrades V}
    (hst : (Model.specDraft (V := V)).reachedRead st c) :
    SubtypeEqualities.RunStoreInv st.val ∧ HandlersRunFacts.ConfirmedInTree st.val ∧
      Spec.Store.ContractInTree st.val.T c :=
  hst

end SpecDraftRecord
