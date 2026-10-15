import Model.Record.ChainState
import Model.Vocabulary
import Spec.Defs.Nondet

/-!
# The record of a model

The structure `Model`: for each family of the protocol (chain state, schedule, store, fork choice,
validator client, grades, handlers, duties and the tick, node, evidence), the types, the readers of
those types and the operations over them. A proof can be stated over an arbitrary model
`M : Model V`. After the structure, each reader and operation over one of the record's types is
spelled as a field of that type, so that a proof writes `st.F` or `n.st.core`.
-/

set_option autoImplicit false

/-- The simp set of the equations of the embedding `Record.Run.ofVocabulary` into the record's run
    type: each reading of an embedded run equals the same reading of the run it embeds. -/
register_simp_attr record_ofVocabulary

namespace DecoupledConsensusModel.Sts.Record

open DecoupledConsensusModel.Protocol (HeightConfig HealConfig SGVote Token GradeRead Phase
  CarriedAdmission ProposalRowSource)
open DecoupledConsensusModel.Execution (NamedObject Setup)

/-- `m ⇢ a`: the routine call `m`, whose value is the set of its outcomes (`DC.NDRE`), can return
    the value `a`. A failure is not an answer. -/
def Returns {α : Type} (m : DC.NDRE α) (a : α) : Prop := Except.ok a ∈ m.run

@[inherit_doc] scoped infix:50 " ⇢ " => Returns

/-- A model of the protocol: the chain-state family's record and, for the other families, their
    types, the readers of those types and the routines over them. -/
structure Model (V : Type) [DecidableEq V] [Fintype V] extends ChainStateModel V where
  -- The type members.
  /-- The type of Goldfish stores, the base of the chain of store types. -/
  GS : Type
  /-- The type of stores, the node's cumulative store. -/
  S : Type
  /-- The type of SG stores: a Goldfish store with the SG votes. -/
  SGS : Type
  /-- The type of FG stores: an SG store with the chain states and the finality fields. -/
  FGS : Type
  /-- The type of a validator's signing records. -/
  R : Type
  /-- The type of named signing records: a signing record with its history of timeout votes. -/
  NR : Type
  /-- The type of healing stores: the store as the grades read it. -/
  HS : Type
  /-- The type of grade views: the part of a store one grade reads. -/
  GV : Type
  /-- The type of grade frames: the three grades of one round. -/
  Frame : Type
  /-- The type of grade caches: the node's saved grades, a round and two frames. -/
  Cache : Type
  /-- The type of grade contracts: the grade routines a duty calls. -/
  Contract : Type
  /-- The type of named stores: a store with the named blocks and the named attestation rows. -/
  NS : Type
  /-- The type of node states: a named store, a named signing record and a grade cache. -/
  N : Type
  -- The chain-state family: the routines and readers beyond ChainStateModel.
  /-- The latest block of a chain state, the block whose transition produced it. -/
  L : CS → Block V
  /-- The slot of a chain state, the slot of its latest block. -/
  cs_s : CS → Slot
  /-- The validators counted towards finalizing the justified block of a chain state. -/
  finalize : CS → Finset V
  /-- The initial chain state, the one before any block: its latest block, justified block and
      finalized block are genesis, its height is `1` and its justified and finalized heights are
      `0`. -/
  cs_initial : CS
  /-- The chain state moved to the next height, with the latest block as the new height's entry and
      the participation sets cleared. -/
  advance_height : HeightConfig → CS → CS
  /-- Whether two attestations are slashable under either condition, as a `Bool`. -/
  slashable : CombinedAttestation V → CombinedAttestation V → Bool
  /-- E1's field conflict, before the one-signer test: one attestation's finality pair conflicts
      with the other's height pair. -/
  e1Fields : CombinedAttestation V → CombinedAttestation V → Bool
  /-- E1 slashability: one signer, and E1's field conflict. -/
  e1Slashable : CombinedAttestation V → CombinedAttestation V → Bool
  /-- E2 slashability: one signer, and E2's field conflict. -/
  e2Slashable : CombinedAttestation V → CombinedAttestation V → Bool
  /-- Whether two attestations have one signer. -/
  sameValidator : CombinedAttestation V → CombinedAttestation V → Bool
  /-- A block's rows folded into a chain state through a row interpretation, followed by the height
      events. -/
  transition_rows :
    {Row : Type} → Binding Row → Env V → HeightConfig → CS → Block V → List Row → CS
  /-- The nonjustifiability rule: the height is a multiple of `K` and lies more than `D` heights
      past the finalized height. -/
  nonjustifiable : HeightConfig → Height → Height → Bool
  /-- A chain state with its finalized block and finalized height replaced. -/
  cs_with_F_h_F : CS → Block V → Height → CS
  -- The schedule family.
  /-- The proposal instant of a slot. -/
  proposal_time : Env V → Slot → Time
  /-- The instant from which the proposer of slot `s` must have been awake, without interruption up
      to `s`'s proposal instant, for its tick at that instant to propose. -/
  proposal_wake_start : Setup V → Slot → Int
  /-- The Goldfish vote instant of a slot. -/
  vote_time : Env V → Slot → Time
  /-- The support cutoff of a slot. -/
  support_cutoff : Env V → Slot → Time
  /-- The view freeze of a slot. -/
  view_freeze : Env V → Slot → Time
  /-- The confirmation instant of a slot. -/
  confirmation_time : Env V → Slot → Time
  /-- The votes of one validator in a set. -/
  votes_by : Finset (GoldfishVote V) → V → Finset (GoldfishVote V)
  /-- Whether a validator equivocates in a set of votes. -/
  equivocates : Finset (GoldfishVote V) → V → Bool
  /-- Whether a validator participates in a set of votes. -/
  participates : Finset (GoldfishVote V) → V → Bool
  -- The store family.
  /-- The current slot of a Goldfish store. -/
  gs_s : GS → Slot
  /-- The processed block tree of a Goldfish store. -/
  gs_T : GS → Finset (Block V)
  /-- The receipt stamps of blocks in a Goldfish store. -/
  gs_timestamp_block : GS → TimestampMap (Block V)
  /-- The receipt stamps of Goldfish votes in a Goldfish store. -/
  gs_timestamp_vote : GS → TimestampMap (GoldfishVote V)
  /-- The processed Goldfish votes of a slot in a Goldfish store. -/
  gs_gf_votes : GS → Slot → List (GoldfishVote V)
  /-- The block the last evaluated slot confirmed, in a Goldfish store. -/
  gs_live_confirmed : GS → Block V
  /-- The current time of a store. -/
  store_t : S → Time
  /-- The current slot of a store. -/
  store_s : S → Slot
  /-- The processed block tree of a store. -/
  store_T : S → Finset (Block V)
  /-- The receipt stamps of blocks in a store. -/
  store_timestamp_block : S → TimestampMap (Block V)
  /-- The receipt stamps of Goldfish votes in a store. -/
  store_timestamp_vote : S → TimestampMap (GoldfishVote V)
  /-- The receipt stamps of SG votes in a store. -/
  store_timestamp_sg_vote : S → TimestampMap (SGVote V)
  /-- The chain state a store holds for each block. -/
  store_σ : S → Block V → CS
  /-- The processed Goldfish votes of a slot in a store. -/
  store_gf_votes : S → Slot → List (GoldfishVote V)
  /-- The processed attestations of a round in a store. -/
  store_sg_votes : S → Round → List (CombinedAttestation V)
  /-- The finalized block of a store. -/
  store_F : S → Block V
  /-- The justified block of a store. -/
  store_J : S → Block V
  /-- The height of the justified block of a store. -/
  store_h_j : S → Height
  /-- The largest chain-state height a store has seen. -/
  store_h_max : S → Height
  /-- The block a store confirms for voting. -/
  store_live_confirmed : S → Block V
  /-- The block a store last recorded as confirmed. -/
  store_latest_confirmed : S → Block V
  /-- The block a store last recorded as stable. -/
  store_latest_stable : S → Block V
  /-- The outcomes of the resolution times of a store's Goldfish votes. -/
  store_tau : S → DC.NDRE (TimestampMap (GoldfishVote V))
  /-- The store read as a healing store. -/
  toHealing : S → HS
  /-- The processed Goldfish votes of a slot, as a set. -/
  store_pool : S → Slot → Finset (GoldfishVote V)
  /-- The SG vote of an attestation. -/
  sgVote : CombinedAttestation V → SGVote V
  /-- The processed attestations of a round, as a set. -/
  store_sg_pool : S → Round → Finset (CombinedAttestation V)
  /-- The outcomes of the test whether a block tree holds the valid head of a vote. -/
  resolved : Finset (Block V) → GoldfishVote V → DC.NDRE Bool
  /-- The processed Goldfish votes of a slot in a Goldfish store, as a set. -/
  gs_pool : GS → Slot → Finset (GoldfishVote V)
  /-- The outcomes of the resolution time of each Goldfish vote in a Goldfish store. -/
  gs_tau : GS → DC.NDRE (TimestampMap (GoldfishVote V))
  /-- A store with its time and its slot replaced. -/
  store_with_t_s : S → Time → Slot → S
  /-- A store with its largest seen height replaced. -/
  store_with_h_max : S → Height → S
  /-- A store with its justified block and justified height replaced. -/
  store_with_J_h_j : S → Block V → Height → S
  /-- A store with its chain states, its processed block tree and its block receipt stamps replaced. -/
  store_with_σ_T_timestamp_block :
    S → (Block V → CS) → Finset (Block V) → TimestampMap (Block V) → S
  /-- The initial store, the one before any receipt. -/
  store_init : S
  -- The fork choice family.
  /-- The Goldfish store an SG store extends. -/
  toGoldfishStore : SGS → GS
  /-- The processed SG votes of a round. -/
  sgs_sg_votes : SGS → Round → Finset (SGVote V)
  /-- The SG store an FG store extends. -/
  toSG : FGS → SGS
  /-- The chain state after each block, in an FG store. -/
  fg_σ : FGS → Block V → CS
  /-- The finalized block of an FG store. -/
  fg_F : FGS → Block V
  /-- The justified block of an FG store. -/
  fg_J : FGS → Block V
  /-- The justified height of an FG store. -/
  fg_h_j : FGS → Height
  /-- The largest chain-state height an FG store has seen. -/
  fg_h_max : FGS → Height
  /-- The FG root of an FG store. -/
  get_fg_root : FGS → Block V
  /-- The filtered block tree of an FG store. -/
  get_filtered_block_tree : FGS → Finset (Block V)
  /-- The outcomes of the SG root of a round through a grade contract. -/
  get_sg_root_with : Contract → Env V → HealConfig → HS → Round → DC.NDRE (Block V)
  /-- The outcomes of the processed-block view of a slot's voter. -/
  voter_processed_block_tree : Env V → GS → Slot → DC.NDRE (Finset (Block V))
  /-- The outcomes of the raw vote view of a slot's voter. -/
  voter_view : Env V → GS → Slot → DC.NDRE (Finset (GoldfishVote V))
  /-- The number of committee voters of a slot in a set of votes. -/
  voters_count : Env V → Finset (GoldfishVote V) → Slot → ℕ
  /-- The rounds of the latest window. -/
  latest_window : Round → Round → List Round
  /-- The outcomes of the Goldfish score of a block. -/
  goldfish_score :
    Env V → Finset (Block V) → Finset (GoldfishVote V) → Finset (GoldfishVote V) → Slot → Block V →
      DC.NDRE ℕ
  /-- The outcomes of the support vote view of a slot's voter. -/
  voter_support_view : Env V → GS → Slot → DC.NDRE (Finset (GoldfishVote V))
  /-- The raw vote view of a slot's proposer. -/
  proposer_view : GS → Slot → List (GoldfishVote V)
  /-- The outcomes of the head of the fork choice through a grade contract. -/
  get_head_with :
    Contract → Env V → HealConfig → HS → Finset (GoldfishVote V) → Finset (GoldfishVote V) → Slot →
      DC.NDRE (Block V)
  /-- The outcomes of the GHOST walk. -/
  ghost : Block V → Finset (Block V) → (Block V → ℕ) → (Block V → Bool) → DC.NDRE (Block V)
  /-- The outcomes of the support vote view of a slot's proposer. -/
  proposer_support_view : GS → Slot → DC.NDRE (List (GoldfishVote V))
  /-- The outcomes of the Goldfish eligibility test. -/
  goldfish_eligible :
    Env V → (Block V → CS) → Height → Finset (Block V) → Slot → Finset (GoldfishVote V) →
      Finset (GoldfishVote V) → Slot → Block V → DC.NDRE Bool
  /-- The outcomes of the test whether a vote targets a descendant of a block. -/
  targets_under : Finset (Block V) → Block V → GoldfishVote V → DC.NDRE Bool
  /-- The outcomes of the Goldfish fork choice. -/
  goldfish_fork_choice :
    Env V → (Block V → CS) → Height → Finset (Block V) → Slot → Block V → Finset (Block V) →
      Finset (GoldfishVote V) → Finset (GoldfishVote V) → Slot → DC.NDRE (Block V)
  /-- The outcomes of the head of the fork choice in a given tree. -/
  get_head_in_tree_with_layer :
    Contract → Env V → HealConfig → HS → Finset (Block V) → Finset (GoldfishVote V) →
      Finset (GoldfishVote V) → Slot → DC.NDRE (Block V)
  /-- The viable tree: the descendants of the finalized block in a tree that have, in that tree, a
      descendant whose chain state stands at least at the largest seen height minus one. -/
  viable_tree : (Block V → CS) → Block V → Height → Finset (Block V) → Finset (Block V)
  /-- Whether a set of votes holds no second vote by a vote's validator. -/
  no_second_vote_in : Finset (GoldfishVote V) → GoldfishVote V → Bool
  /-- The viability test: some descendant of a block in the tree has a chain state at least at the
      largest seen height minus one. -/
  viable : (Block V → CS) → Height → Finset (Block V) → Block V → Bool
  /-- The descendants of the finalized block in a tree. -/
  finalized_descendants : Block V → Finset (Block V) → Finset (Block V)
  /-- The outcomes of one step of the GHOST walk: the eligible child of the highest score, if any. -/
  ghost_step :
    Finset (Block V) → (Block V → ℕ) → (Block V → Bool) → Block V → DC.NDRE (Option (Block V))
  /-- The filtered block tree of an FG store over a given set of blocks: the viable tree recomputed
      inside the set, then its descendants of the FG root. -/
  get_filtered_block_tree_from : FGS → Finset (Block V) → Finset (Block V)
  /-- The validators represented in a set of votes. -/
  raw_participants : Finset (GoldfishVote V) → Finset V
  /-- The outcomes of the validators that support a block at a slot: not equivocating in the votes,
      and with a support vote of that slot for a descendant of the block. -/
  raw_supporters :
    Finset (Block V) → Finset (GoldfishVote V) → Finset (GoldfishVote V) → Slot → Block V →
      DC.NDRE (Finset V)
  -- The validator client family.
  /-- The target a signing record holds at a height. -/
  target : R → Height → Option BlockId
  /-- Whether a signing record has a timeout vote at a height. -/
  timeout : R → Height → Bool
  /-- The lock a signing record holds at a height. -/
  lock : R → Height → Option BlockId
  /-- The signing record a named signing record holds. -/
  legacy : NR → R
  /-- The timeout history a named signing record holds. -/
  nr_timeoutHistory : NR → Finset (Height × BlockId)
  /-- The lock a signing record uses for its next vote. -/
  own_lock : R → Height → Option FinalityPair → Option BlockId
  /-- The height pair of the next attestation. -/
  height_pair : R → Option (Height × BlockId × Bool) → Option FinalityPair → HeightPair
  /-- The signing of one attestation: the updated record and the attestation signed. -/
  create_attestation :
    R → V → Round → Option BlockId → Option (Height × BlockId × Bool) → Height → BlockId → Height →
      R × CombinedAttestation V
  /-- The finality pair of the next attestation. -/
  finality_pair : R → Height → BlockId → Height → Option FinalityPair
  /-- The named form of a height pair. -/
  encodeHeight : Option (Height × BlockId × Bool) → HeightPair → NamedHeightPair
  /-- A signing record after it records an attestation's finality pair as a lock and its height pair
      as a target or a timeout vote. -/
  record_attestation : R → CombinedAttestation V → R
  -- The grades family.
  /-- The FG store a healing store extends. -/
  toFG : HS → FGS
  /-- The processed block tree of a grade view. -/
  gv_T : GV → Finset (Block V)
  /-- The receipt stamps of blocks in a grade view. -/
  gv_timestamp_block : GV → TimestampMap (Block V)
  /-- The filtered block tree of a grade view. -/
  gv_tree : GV → Finset (Block V)
  /-- The SG votes of a round in a grade view. -/
  gv_sg_votes : GV → Round → Finset (SGVote V)
  /-- The receipt stamps of SG votes in a grade view. -/
  gv_timestamp_sg_vote : GV → TimestampMap (SGVote V)
  /-- The grade-0 result of a frame. -/
  g0 : Frame → Option (Option (Block V))
  /-- The grade-1 result of a frame. -/
  g1 : Frame → Option (Option (Block V))
  /-- The grade-2 result of a frame. -/
  g2 : Frame → Option (Option (Block V))
  /-- The round of a grade cache. -/
  round : Cache → Round
  /-- The grades of a grade cache's round. -/
  cache_current : Cache → Frame
  /-- The outcomes of the grade read of a contract. -/
  read : Contract → Env V → HealConfig → HS → Round → DC.NDRE (GradeRead V)
  /-- The outcomes of the optional SG candidate of a contract. -/
  confirmationSG : Contract → Env V → HealConfig → HS → Slot → DC.NDRE (Option (Block V))
  /-- The outcomes of the stable-record root of a contract. -/
  stableRoot : Contract → Env V → HealConfig → HS → Round → DC.NDRE (Option (Block V))
  /-- The SG vote a contract computes from a healing store and a grade read. -/
  contract_sgVote : Contract → HS → GradeRead V → Block V
  /-- The grade contract built from its four parts. -/
  mkContract :
    (Env V → HealConfig → HS → Round → GradeRead V) → (HS → GradeRead V → Block V) →
      (Env V → HealConfig → HS → Slot → Option (Block V)) →
      (Env V → HealConfig → HS → Round → Option (Block V)) → Contract
  /-- The first slot of a round. -/
  opening_slot : HealConfig → Round → Slot
  /-- The instant a grade of a round is computed. -/
  domain : Env V → HealConfig → Round → Phase → Time
  /-- The opening instant of a round. -/
  opening : Env V → HealConfig → Round → Time
  /-- The round of a slot. -/
  round_of : HealConfig → Slot → Round
  /-- The grade view of a healing store. -/
  gradeView : HS → GV
  /-- The early cutoff of a grade of a round. -/
  early : Env V → HealConfig → Round → Phase → Time
  /-- The late cutoff of a grade of a round. -/
  late : Env V → HealConfig → Round → Phase → Time
  /-- The outcomes of the grade test of a block. -/
  gradeBool : Env V → GV → Block V → Round → Round → Time → Time → Block V → DC.NDRE Bool
  /-- The outcomes of the grade cache after the grades due at an instant. -/
  onPhaseTick : Env V → HealConfig → HS → Time → Cache → DC.NDRE Cache
  /-- The frame of a round read from a cache. -/
  readFrame : Cache → HS → Round → Frame
  /-- The action instant of a round. -/
  a : HealConfig → Time → Round → Time
  /-- The result of one grade in a frame. -/
  phaseResult : Frame → Phase → Option (Option (Block V))
  /-- The active prefix of a block in a tree. -/
  activePrefix : Finset (Block V) → Block V → Option (Block V)
  /-- The outcomes of the raw SG tokens of a validator. -/
  rawView : GV → Round → Round → Time → V → DC.NDRE (Finset (Token (Option BlockId)))
  /-- A grade cache clipped at a finalized block. -/
  clipCache : Block V → Cache → Cache
  /-- One grade clipped at a finalized block. -/
  clipGrade : Block V → Block V → Block V
  /-- The outcomes of the raw SG votes of a validator. -/
  rawInputs : GV → Round → Round → Time → V → DC.NDRE (Finset (SGVote V))
  /-- The grade contract of a cache. -/
  frameContract : Cache → Contract
  /-- The outcomes of the interpreted SG tokens of a validator. -/
  readyView : GV → Block V → Round → Round → Time → V → DC.NDRE (Finset (Token (Option BlockId)))
  /-- The SG vote of one grade read. -/
  currentSGVote : HS → GradeRead V → Block V
  /-- The frame a cache holds for a round. -/
  cacheAtRound : Cache → Round → Frame
  /-- The outcomes of the interpreted SG votes of a validator. -/
  interpretedInputs : GV → Block V → Round → Round → Time → V → DC.NDRE (Finset (SGVote V))
  /-- The outcomes of the freeze root of a grade. -/
  freezeRoot : Env V → GV → Block V → Round → Round → Time → Time → DC.NDRE (Option (Block V))
  /-- The outcomes of the anchor of a round's grades. -/
  anchor : Env V → HealConfig → HS → Round → Option (Option (Block V)) → DC.NDRE (Block V)
  /-- The outcomes of the test whether a token covers a block locally. -/
  localCovers : GV → Option BlockId → Block V → DC.NDRE Bool
  /-- The outcomes of the test whether a validator supports a block. -/
  positive : GV → Block V → Round → Round → Time → Time → V → Block V → DC.NDRE Bool
  /-- The outcomes of the grade-2 block of a frame. -/
  grade2Block : HS → Frame → DC.NDRE (Option (Block V))
  /-- The deepest ancestor of a block that passes a test and, when a block is given, is a descendant
      of it. -/
  deepest_clear : Option (Block V) → Block V → (Block V → Bool) → Option (Block V)
  /-- The outcomes of the stable root a cache gives for a round. -/
  frameStableRoot : Cache → Env V → HealConfig → HS → Round → DC.NDRE (Option (Block V))
  /-- The outcomes of the test whether a validator opposes a block. -/
  opposing : GV → Block V → Round → Round → Time → Time → V → Block V → DC.NDRE Bool
  /-- The token of an SG vote. -/
  token : SGVote V → Token (Option BlockId)
  /-- The outcomes of the test whether a head covers a block. -/
  head_covers : Finset (Block V) → Block V → Option BlockId → DC.NDRE Bool
  /-- One grade result clipped at a finalized block. -/
  clipResult : Block V → Option (Option (Block V)) → Option (Option (Block V))
  /-- The outcomes of the SG candidate a cache gives for a slot. -/
  frameSGCandidate : Cache → Env V → HealConfig → HS → Slot → DC.NDRE (Option (Block V))
  /-- Whether every grade of a frame is computed. -/
  allClosed : Frame → Bool
  /-- The outcomes of the test whether an SG vote's confirmed root is ready in a grade view: no
      root, or a root of the view received before the cutoff and compatible with the finalized
      block. -/
  bodyReady : GV → Block V → Time → SGVote V → DC.NDRE Bool
  /-- The outcomes of the grade read of a round taken from a cache: the anchor, the grade-2 block,
      the clear test and whether grade 2 holds a block. -/
  frameGradeRead : Cache → Env V → HealConfig → HS → Round → DC.NDRE (GradeRead V)
  /-- The opposition condition on tokens, a proposition: a late token after every early one whose
      key does not cover the block, or two raw tokens of one round after every early one with
      different keys. -/
  Opposes : {Key Target : Type} → (Key → Target → Prop) → Finset (Token Key) →
    Finset (Token Key) → Finset (Token Key) → Target → Prop
  /-- The support condition on tokens, a proposition: an early token of the latest round covers the
      block, the raw tokens are clean from its round, and every later late token covers the block. -/
  Supports : {Key Target : Type} → (Key → Target → Prop) → Finset (Token Key) →
    Finset (Token Key) → Finset (Token Key) → Target → Prop
  /-- Whether a set of tokens has, from a round on, no two tokens of one round with different keys,
      a proposition. -/
  CleanFrom : {Key : Type} → Finset (Token Key) → ℕ → Prop
  /-- A frame with each of its three results clipped at a finalized block. -/
  clipFrame : Block V → Frame → Frame
  /-- A cache moved to a round: unchanged at its round, its next frame made current at the following
      round, both frames pending otherwise. -/
  alignRound : Cache → Round → Cache
  /-- The frame with no grade computed. -/
  pendingFrame : Frame
  /-- The offset, in delays from a round's opening, of the instant a grade is computed. -/
  domainOffset : Phase → ℤ
  /-- The offset, in delays from a round's opening, of a grade's early cutoff. -/
  earlyOffset : Phase → ℤ
  /-- The offset, in delays from a round's opening, of a grade's late cutoff. -/
  lateOffset : Phase → ℤ
  /-- The clear test of a frame: a block is clear when grade 0 holds no block or a block compatible
      with it. -/
  clear : Frame → Block V → Bool
  /-- The ancestors of a block, the block first and genesis last. -/
  chain_of : Block V → List (Block V)
  /-- A frame with one grade's result set. -/
  putPhase : Frame → Phase → Option (Block V) → Frame
  /-- The ancestors of a block within a number of parent steps, the block first. -/
  chain_up : ℕ → Block V → List (Block V)
  -- The handlers family.
  /-- The store a named store holds. -/
  core : NS → S
  /-- Whether two stores count as the same store part. -/
  sameCore : S → S → Prop
  /-- The named blocks a named store holds. -/
  bodies : NS → Finset (NamedBlock V)
  /-- The named attestation rows of a round. -/
  sg_rows : NS → Round → List (NamedAttestation V)
  /-- The named store with its clock set. -/
  ns_setClock : Env V → NS → Time → NS
  /-- The stable block of a store. -/
  get_stable : S → Block V
  /-- The confirmed roots a validator has voted in a round. -/
  round_votes : S → CombinedAttestation V → Finset (Option BlockId)
  /-- The receipt of a named block. -/
  on_block_with : CarriedAdmission → Env V → HealConfig → HeightConfig → NS → NamedBlock V → NS
  /-- The receipt of one named attestation. -/
  admit_row : HealConfig → NS → NamedAttestation V → NS
  /-- The outcomes of the confirmation update of a store. -/
  update_confirmation_with : Contract → Env V → HealConfig → S → Slot → DC.NDRE S
  /-- The receipt of a Goldfish vote after its checks. -/
  on_goldfish_vote_checked : Env V → S → GoldfishVote V → S
  /-- The confirmed block of a store. -/
  get_confirmed : S → Block V
  /-- Whether a block's attestations may be admitted. -/
  carried_attestations_admissible : HealConfig → Block V → Bool
  /-- The receipt of an attestation. -/
  on_sg_vote : HealConfig → S → CombinedAttestation V → S
  /-- The receipt of a list of named attestations. -/
  admit_rows : HealConfig → NS → List (NamedAttestation V) → NS
  /-- The advance of a confirmation record. -/
  advance_confirmed : Block V → Block V → Block V
  /-- A named store after its store processes a block. -/
  ns_process_block_core : Env V → HealConfig → HeightConfig → NS → NamedBlock V → NS
  /-- The outcomes of the filtered block tree of a slot's voter. -/
  voter_filtered_block_tree : Env V → S → Slot → DC.NDRE (Finset (Block V))
  /-- The confirmation record kept a descendant of the stable record. -/
  floor_on_stable : Block V → Block V → Block V → Block V
  /-- The processing of a block with a given chain-state transition. -/
  on_block_using : Env V → S → Block V → (CS → CS) → S
  /-- The processing of a block after its checks. -/
  on_block_checked_using : (S → S) → HealConfig → S → Block V → S
  /-- The receipt of a Goldfish vote. -/
  on_goldfish_vote : S → GoldfishVote V → S
  /-- The outcomes of the Goldfish vote duty on a store. -/
  goldfish_vote_with :
    Contract → Env V → HealConfig → Protocol.Node V → S → DC.NDRE (S × Option (GoldfishVote V))
  /-- The initial named store. -/
  ns_initial : NS
  /-- The finality fields of a store updated from a chain state. -/
  update_finality : S → CS → S
  /-- The receipt of the attestations a block includes. -/
  admit_carried : CarriedAdmission → HealConfig → NS → NS → NamedBlock V → NS
  /-- The outcomes of the head of the fork choice in a given tree, on a store. -/
  get_head_in_tree_with :
    Contract → Env V → HealConfig → S → Finset (Block V) → Finset (GoldfishVote V) →
      Finset (GoldfishVote V) → Slot → DC.NDRE (Block V)
  /-- The chain-state transition by a block: the slot, then the block's attestations, then the
      latest block, then the height events. -/
  state_transition : Env V → HeightConfig → CS → Block V → CS
  /-- A named store with its store replaced. -/
  ns_with_core : NS → S → NS
  /-- A named store after its store part is replaced by a store that processed a block: the new
      store, with the named block added to the named blocks when the new store holds the block and
      the old one did not. -/
  commitBlock : NS → S → NamedBlock V → NS
  -- The duties and the tick family.
  /-- The outcomes of the proposal duty. -/
  duties_propose_block_with :
    Contract → Env V → HealConfig → HeightConfig → Protocol.Node V → NS →
      DC.NDRE (NS × Option (NamedBlock V))
  /-- The outcomes of the attestation duty. -/
  duties_attest_with :
    Contract → Env V → HealConfig → Protocol.Node V → NS → NR →
      DC.NDRE (NS × NR × NamedAttestation V)
  /-- The outcomes of the confirmation duty. -/
  duties_update_confirmation_with : Contract → Env V → HealConfig → NS → Slot → DC.NDRE NS
  /-- Whether a round is in the proposal window of a store. -/
  inWindow : HealConfig → S → Round → Bool
  /-- The outcomes of the round action. -/
  round_action_with :
    Contract → Env V → HealConfig → Protocol.Node V → HS → NR → DC.NDRE (NR × NamedAttestation V)
  /-- The outcomes of the Goldfish vote duty. -/
  duties_goldfish_vote_with :
    Contract → Env V → HealConfig → Protocol.Node V → NS → DC.NDRE (NS × Option (GoldfishVote V))
  /-- The outcomes of the grade-2 block of a round through a grade contract. -/
  grade2_block_with : Contract → Env V → HealConfig → HS → Round → DC.NDRE (Option (Block V))
  /-- The outcomes of the block a proposer builds. -/
  proposal_with :
    Contract → ProposalRowSource → Env V → HealConfig → Protocol.Node V → NS →
      DC.NDRE (Option (NamedBlock V))
  /-- The outcomes of the attestations a proposal includes. -/
  select : ProposalRowSource → HealConfig → NS → DC.NDRE (List (NamedAttestation V))
  /-- The outcomes of the named block of a parent. -/
  parentBody? : NS → Block V → DC.NDRE (Option (NamedBlock V))
  /-- The rows a proposal on a parent includes. -/
  proposalRows : NamedBlock V → List (NamedAttestation V) → List (NamedAttestation V)
  /-- The outcomes of the FG source of a round through a grade contract. -/
  fg_source_with :
    Contract → Env V → HealConfig → HS → Round → Option (Block V) → DC.NDRE (Option (Block V))
  /-- The outcomes of the SG vote of a round through a grade contract. -/
  get_sg_vote_with :
    Contract → Env V → HealConfig → HS → Round → Option (Block V) → DC.NDRE (Block V)
  /-- The processed rows a proposal may include. -/
  processedRows : HealConfig → NS → List (NamedAttestation V)
  /-- The outcomes of the proposal duty's read of a healing store, handed to a continuation: the
      head, the slot, the root and the votes a proposal includes. -/
  with_proposal_input :
    {Result : Type} → Contract → Env V → HealConfig → Protocol.Node V → HS →
      (Protocol.ProposalInput V → Result) → DC.NDRE Result
  /-- An attestation input converted to the signing record's input, field by field. -/
  creatorInput : Protocol.AttestationInput V → Protocol.NamedRecord.Input V
  /-- The outcomes of the finality-gadget fields an attestation reads: the source fields, and the
      justified height, the justified root and the finalized height of the head's chain state. -/
  get_fg_vote_with :
    Contract → Env V → HealConfig → HS → Round → Option (Block V) →
      DC.NDRE (Option (Height × BlockId × Bool) × Height × BlockId × Height)
  /-- The named attestations included in a named block and its ancestors. -/
  chainRows : NamedBlock V → List (NamedAttestation V)
  /-- The outcomes of the attestation duty's read of a healing store, handed to a continuation: the
      validator, the round, the SG vote and the finality-gadget fields. -/
  with_attestation_input :
    {Result : Type} → Contract → Env V → HealConfig → Protocol.Node V → HS →
      (Protocol.AttestationInput V → Result) → DC.NDRE Result
  /-- The outcomes of the named attestations included in the named blocks of a named store that may
      be re-included, restricted to the rounds of the proposal window. -/
  carriedRows : HealConfig → NS → DC.NDRE (List (NamedAttestation V))
  /-- Whether a named block's attestations may be re-included: its round is in the proposal window
      and its attestations are admissible. -/
  eligibleBody : HealConfig → NS → NamedBlock V → Bool
  /-- The outcomes of the named blocks of a named store ordered by root, a root held by two blocks
      dropped. -/
  orderedBodies : NS → DC.NDRE (List (NamedBlock V))
  /-- The processed named attestations of a named store whose round is in the proposal window. -/
  poolRows : HealConfig → NS → List (NamedAttestation V)
  -- The node family.
  /-- The named store of a node state. -/
  st : N → NS
  /-- The named signing record of a node state. -/
  record : N → NR
  /-- The grade cache of a node state. -/
  cache : N → Cache
  /-- The grade contract of a cache. -/
  gradeContract : Cache → Contract
  /-- The node state validator `v` starts from under setup `S`. -/
  initial : Setup V → V → N
  /-- The node state after a wake. -/
  wake : N → N
  /-- Whether a validator's run over this model records its wakes as events. -/
  wakeEvents : Bool
  /-- Whether a node state runs as a validator, a proposition. -/
  runs_as : N → V → Prop
  /-- Whether a node state is one a run reaches, a proposition. -/
  reachedNode : (n : N) → Prop
  /-- Whether a named store is one a run reaches, a proposition. -/
  reachedStore : (st : NS) → Prop
  /-- Whether a store is one a run reaches, a proposition. -/
  reachedCore : (st : S) → Prop
  /-- Whether a healing store read with a grade cache is a pair a run reaches, a proposition. -/
  reachedRead : (st : HS) → (c : Cache) → Prop
  /-- Whether a chain state names tree blocks of a store, a proposition. -/
  chainStateInTree : (st : S) → (σ : CS) → Prop
  /-- Whether a block's root is new to a store, a proposition. -/
  rootFresh : (st : S) → (B : Block V) → Prop
  /-- The awake test of round `r`'s proposal and Goldfish vote: whether validator `v`'s tick on node
      state `n` under setup `S` runs round `r`'s grade-1 duties. -/
  awake_for_grade1 : (S : Setup V) → (v : V) → (n : N) → (r : Round) → Prop
  /-- The awake test of round `r`'s confirmation and attestation: whether validator `v`'s tick on
      node state `n` under setup `S` runs round `r`'s grade-2 duties. -/
  awake_for_grade2 : (S : Setup V) → (v : V) → (n : N) → (r : Round) → Prop
  /-- The node's tick at an instant: the set of its outcomes, each the new node state with the
      objects it sends, or the failure. -/
  tick : Setup V → V → N → Int → DC.NDRE (N × List (NamedObject V))
  /-- The node's receipt of a delivered object: the set of its outcomes, each a node state or the
      failure. -/
  process : Setup V → N → NamedObject V → DC.NDRE N
  /-- The named store after a block's core processing. -/
  postCore : Setup V → NS → NamedBlock V → NS
  /-- The named store's receipt of an object. -/
  receipt_process : Setup V → NS → NamedObject V → NS
  /-- The named store with every block of its saved grades replaced by its deepest ancestor
      compatible with the store's finalized block. -/
  make_grades_compatible_with_finalized : NS → NS
  /-- The node state made of a named store, a named signing record and a grade cache. -/
  mkNode : NS → NR → Cache → N
  /-- A named store with its saved grades replaced. -/
  store_with_cache : NS → Cache → NS
  /-- The grade cache that a duty run with the grade contract `k` writes into the store it returns. -/
  contractCache : (k : Contract) → Cache
  -- The evidence family.
  /-- The attestations a chain includes. -/
  chain_attestations : Block V → Finset (CombinedAttestation V)
  /-- Slashable weight between two sets of attestations. -/
  HasSlashableWeightBetween :
    Env V → Finset (CombinedAttestation V) → Finset (CombinedAttestation V) → Prop
  /-- The attestations a store holds. -/
  store_attestations : S → Finset (CombinedAttestation V)
  /-- A validator has a slashable pair between two sets of attestations, a proposition: one
      attestation from each set, both signed by the validator, slashable. -/
  SlashableBetween : Finset (CombinedAttestation V) → Finset (CombinedAttestation V) → V → Prop
  /-- A set of validators has the weight of the intersection of two quorums, a proposition:
      `2q ≤ W + w(S)`. -/
  HasIntersectionWeight : Env V → Finset V → Prop

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The readers, spelled as fields of the record's types -/

/-- `gs.s` is the reader `M.gs_s gs`: the current slot of `gs`. -/
def Model.GS.s {M : Model V} (gs : M.GS) : Slot :=
  M.gs_s gs

/-- `gs.T` is the reader `M.gs_T gs`: the blocks `gs` has processed. -/
def Model.GS.T {M : Model V} (gs : M.GS) : Finset (Block V) :=
  M.gs_T gs

/-- `gs.timestamp_block` is the reader `M.gs_timestamp_block gs`: the instant at which `gs` received
    each block. -/
def Model.GS.timestamp_block {M : Model V} (gs : M.GS) : TimestampMap (Block V) :=
  M.gs_timestamp_block gs

/-- `gs.timestamp_vote` is the reader `M.gs_timestamp_vote gs`: the instant at which `gs` received
    each Goldfish vote. -/
def Model.GS.timestamp_vote {M : Model V} (gs : M.GS) : TimestampMap (GoldfishVote V) :=
  M.gs_timestamp_vote gs

/-- `gs.gf_votes` is the reader `M.gs_gf_votes gs`: the Goldfish votes of slot `s` that `gs` has
    processed. -/
def Model.GS.gf_votes {M : Model V} (gs : M.GS) : Slot → List (GoldfishVote V) :=
  M.gs_gf_votes gs

/-- `gs.live_confirmed` is the reader `M.gs_live_confirmed gs`: the block `gs` last confirmed. -/
def Model.GS.live_confirmed {M : Model V} (gs : M.GS) : Block V :=
  M.gs_live_confirmed gs

/-- `st.t` is the reader `M.store_t st`: the current time of `st`. -/
def Model.S.t {M : Model V} (st : M.S) : Time :=
  M.store_t st

/-- `st.s` is the reader `M.store_s st`: the current slot of `st`. -/
def Model.S.s {M : Model V} (st : M.S) : Slot :=
  M.store_s st

/-- `st.T` is the reader `M.store_T st`: the blocks `st` has processed. -/
def Model.S.T {M : Model V} (st : M.S) : Finset (Block V) :=
  M.store_T st

/-- `st.timestamp_block` is the reader `M.store_timestamp_block st`: the instant at which `st`
    received each block. -/
def Model.S.timestamp_block {M : Model V} (st : M.S) : TimestampMap (Block V) :=
  M.store_timestamp_block st

/-- `st.timestamp_vote` is the reader `M.store_timestamp_vote st`: the instant at which `st`
    received each Goldfish vote. -/
def Model.S.timestamp_vote {M : Model V} (st : M.S) : TimestampMap (GoldfishVote V) :=
  M.store_timestamp_vote st

/-- `st.timestamp_sg_vote` is the reader `M.store_timestamp_sg_vote st`: the instant at which `st`
    received each SG vote. -/
def Model.S.timestamp_sg_vote {M : Model V} (st : M.S) : TimestampMap (SGVote V) :=
  M.store_timestamp_sg_vote st

/-- `st.σ` is the reader `M.store_σ st`: the chain state `st` holds for block `B`. -/
def Model.S.σ {M : Model V} (st : M.S) : Block V → M.CS :=
  M.store_σ st

/-- `st.gf_votes` is the reader `M.store_gf_votes st`: the Goldfish votes of slot `s` that `st` has
    processed. -/
def Model.S.gf_votes {M : Model V} (st : M.S) : Slot → List (GoldfishVote V) :=
  M.store_gf_votes st

/-- `st.sg_votes` is the reader `M.store_sg_votes st`: the attestations of round `r` that `st` has
    processed. -/
def Model.S.sg_votes {M : Model V} (st : M.S) : Round → List (CombinedAttestation V) :=
  M.store_sg_votes st

/-- `st.F` is the reader `M.store_F st`: the finalized block of `st`. -/
def Model.S.F {M : Model V} (st : M.S) : Block V :=
  M.store_F st

/-- `st.J` is the reader `M.store_J st`: the justified block of `st`. -/
def Model.S.J {M : Model V} (st : M.S) : Block V :=
  M.store_J st

/-- `st.h_j` is the reader `M.store_h_j st`: the justified height of `st`. -/
def Model.S.h_j {M : Model V} (st : M.S) : Height :=
  M.store_h_j st

/-- `st.h_max` is the reader `M.store_h_max st`: the largest height `st` has seen. -/
def Model.S.h_max {M : Model V} (st : M.S) : Height :=
  M.store_h_max st

/-- `st.live_confirmed` is the reader `M.store_live_confirmed st`: the block `st` confirms for
    voting. -/
def Model.S.live_confirmed {M : Model V} (st : M.S) : Block V :=
  M.store_live_confirmed st

/-- `st.latest_confirmed` is the reader `M.store_latest_confirmed st`: the block `st` last recorded
    as confirmed. -/
def Model.S.latest_confirmed {M : Model V} (st : M.S) : Block V :=
  M.store_latest_confirmed st

/-- `st.latest_stable` is the reader `M.store_latest_stable st`: the block `st` last recorded as
    stable. -/
def Model.S.latest_stable {M : Model V} (st : M.S) : Block V :=
  M.store_latest_stable st

/-- `st.tau` is the reader `M.store_tau st`: the outcomes of the resolution times of `st`'s Goldfish
    votes. -/
def Model.S.tau {M : Model V} (st : M.S) : DC.NDRE (TimestampMap (GoldfishVote V)) :=
  M.store_tau st

/-- `sg.toGoldfishStore` is the reader `M.toGoldfishStore sg`: the Goldfish store part of `sg`. -/
def Model.SGS.toGoldfishStore {M : Model V} (sg : M.SGS) : M.GS :=
  M.toGoldfishStore sg

/-- `sg.sg_votes` is the reader `M.sgs_sg_votes sg`: the SG votes of round `r` that `sg` has
    processed. -/
def Model.SGS.sg_votes {M : Model V} (sg : M.SGS) : Round → Finset (SGVote V) :=
  M.sgs_sg_votes sg

/-- `fg.toSG` is the reader `M.toSG fg`: the SG store part of `fg`. -/
def Model.FGS.toSG {M : Model V} (fg : M.FGS) : M.SGS :=
  M.toSG fg

/-- `fg.σ` is the reader `M.fg_σ fg`: the chain state `fg` holds for block `B`. -/
def Model.FGS.σ {M : Model V} (fg : M.FGS) : Block V → M.CS :=
  M.fg_σ fg

/-- `fg.F` is the reader `M.fg_F fg`: the finalized block of `fg`. -/
def Model.FGS.F {M : Model V} (fg : M.FGS) : Block V :=
  M.fg_F fg

/-- `fg.J` is the reader `M.fg_J fg`: the justified block of `fg`. -/
def Model.FGS.J {M : Model V} (fg : M.FGS) : Block V :=
  M.fg_J fg

/-- `fg.h_j` is the reader `M.fg_h_j fg`: the justified height of `fg`. -/
def Model.FGS.h_j {M : Model V} (fg : M.FGS) : Height :=
  M.fg_h_j fg

/-- `fg.h_max` is the reader `M.fg_h_max fg`: the largest height `fg` has seen. -/
def Model.FGS.h_max {M : Model V} (fg : M.FGS) : Height :=
  M.fg_h_max fg

/-- `rec.target` is the reader `M.target rec`: the target `rec` has voted at height `h`, if any. -/
def Model.R.target {M : Model V} (rec : M.R) : Height → Option BlockId :=
  M.target rec

/-- `rec.timeout` is the reader `M.timeout rec`: whether `rec` has voted a timeout at height `h`. -/
def Model.R.timeout {M : Model V} (rec : M.R) : Height → Bool :=
  M.timeout rec

/-- `rec.lock` is the reader `M.lock rec`: the block `rec` is locked on at height `h`, if any. -/
def Model.R.lock {M : Model V} (rec : M.R) : Height → Option BlockId :=
  M.lock rec

/-- `nr.legacy` is the reader `M.legacy nr`: the signing record part of `nr`. -/
def Model.NR.legacy {M : Model V} (nr : M.NR) : M.R :=
  M.legacy nr

/-- `nr.timeoutHistory` is the reader `M.nr_timeoutHistory nr`: the pairs of a height and a block
    that `nr` has recorded as timeout annotations. -/
def Model.NR.timeoutHistory {M : Model V} (nr : M.NR) : Finset (Height × BlockId) :=
  M.nr_timeoutHistory nr

/-- `hs.toFG` is the reader `M.toFG hs`: the FG store part of `hs`. -/
def Model.HS.toFG {M : Model V} (hs : M.HS) : M.FGS :=
  M.toFG hs

/-- `gv.T` is the reader `M.gv_T gv`: the blocks of `gv`. -/
def Model.GV.T {M : Model V} (gv : M.GV) : Finset (Block V) :=
  M.gv_T gv

/-- `gv.timestamp_block` is the reader `M.gv_timestamp_block gv`: the instant at which each block of
    `gv` was received. -/
def Model.GV.timestamp_block {M : Model V} (gv : M.GV) : TimestampMap (Block V) :=
  M.gv_timestamp_block gv

/-- `gv.tree` is the reader `M.gv_tree gv`: the tree the grades of `gv` walk. -/
def Model.GV.tree {M : Model V} (gv : M.GV) : Finset (Block V) :=
  M.gv_tree gv

/-- `gv.sg_votes` is the reader `M.gv_sg_votes gv`: the SG votes of round `r` in `gv`. -/
def Model.GV.sg_votes {M : Model V} (gv : M.GV) : Round → Finset (SGVote V) :=
  M.gv_sg_votes gv

/-- `gv.timestamp_sg_vote` is the reader `M.gv_timestamp_sg_vote gv`: the instant at which each SG
    vote of `gv` was received. -/
def Model.GV.timestamp_sg_vote {M : Model V} (gv : M.GV) : TimestampMap (SGVote V) :=
  M.gv_timestamp_sg_vote gv

/-- `fr.g0` is the reader `M.g0 fr`: the grade-0 result `fr` holds, if computed. -/
def Model.Frame.g0 {M : Model V} (fr : M.Frame) : Option (Option (Block V)) :=
  M.g0 fr

/-- `fr.g1` is the reader `M.g1 fr`: the grade-1 result `fr` holds, if computed. -/
def Model.Frame.g1 {M : Model V} (fr : M.Frame) : Option (Option (Block V)) :=
  M.g1 fr

/-- `fr.g2` is the reader `M.g2 fr`: the grade-2 result `fr` holds, if computed. -/
def Model.Frame.g2 {M : Model V} (fr : M.Frame) : Option (Option (Block V)) :=
  M.g2 fr

/-- `c.round` is the reader `M.round c`: the round `c` holds grades for. -/
def Model.Cache.round {M : Model V} (c : M.Cache) : Round :=
  M.round c

/-- `c.current` is the reader `M.cache_current c`: the grade frame `c` holds for its round. -/
def Model.Cache.current {M : Model V} (c : M.Cache) : M.Frame :=
  M.cache_current c

/-- `gc.read` is the reader `M.read gc`: the outcomes of `gc`'s grade read. -/
def Model.Contract.read {M : Model V} (gc : M.Contract) :
    Env V → HealConfig → M.HS → Round → DC.NDRE (GradeRead V) :=
  M.read gc

/-- `gc.confirmationSG` is the reader `M.confirmationSG gc`: the outcomes of `gc`'s SG candidate
    selection. -/
def Model.Contract.confirmationSG {M : Model V} (gc : M.Contract) :
    Env V → HealConfig → M.HS → Slot → DC.NDRE (Option (Block V)) :=
  M.confirmationSG gc

/-- `gc.stableRoot` is the reader `M.stableRoot gc`: the outcomes of `gc`'s stable-root read. -/
def Model.Contract.stableRoot {M : Model V} (gc : M.Contract) :
    Env V → HealConfig → M.HS → Round → DC.NDRE (Option (Block V)) :=
  M.stableRoot gc

/-- `gc.sgVote` is the reader `M.contract_sgVote gc`: the block `gc` votes for, from a healing store
    and a grade read. -/
def Model.Contract.sgVote {M : Model V} (gc : M.Contract) : M.HS → GradeRead V → Block V :=
  M.contract_sgVote gc

/-- `ns.core` is the reader `M.core ns`: the store part of `ns`. -/
def Model.NS.core {M : Model V} (ns : M.NS) : M.S :=
  M.core ns

/-- `ns.bodies` is the reader `M.bodies ns`: the named blocks `ns` holds. -/
def Model.NS.bodies {M : Model V} (ns : M.NS) : Finset (NamedBlock V) :=
  M.bodies ns

/-- `ns.sg_rows` is the reader `M.sg_rows ns`: the named attestations of round `r` that `ns` holds. -/
def Model.NS.sg_rows {M : Model V} (ns : M.NS) : Round → List (NamedAttestation V) :=
  M.sg_rows ns

/-- `n.st` is the reader `M.st n`: the named store part of `n`. -/
def Model.N.st {M : Model V} (n : M.N) : M.NS :=
  M.st n

/-- `n.record` is the reader `M.record n`: the signing record part of `n`. -/
def Model.N.record {M : Model V} (n : M.N) : M.NR :=
  M.record n

/-- `n.cache` is the reader `M.cache n`: the grade cache part of `n`. -/
def Model.N.cache {M : Model V} (n : M.N) : M.Cache :=
  M.cache n

/-! ## The operations over one of the record's types, spelled as fields of that type -/

/-- `st.toHealing` is the operation `M.toHealing st`: the healing store that `st` stands for. -/
def Model.S.toHealing {M : Model V} (st : M.S) : M.HS :=
  M.toHealing st

/-- `st.pool s` is the operation `M.store_pool st s`: the set of Goldfish votes of slot `s` that
    `st` has processed. -/
def Model.S.pool {M : Model V} (st : M.S) (s : Slot) : Finset (GoldfishVote V) :=
  M.store_pool st s

/-- `st.sg_pool r` is the operation `M.store_sg_pool st r`: the set of attestations of round `r`
    that `st` has processed. -/
def Model.S.sg_pool {M : Model V} (st : M.S) (r : Round) : Finset (CombinedAttestation V) :=
  M.store_sg_pool st r

/-- `gs.pool s` is the operation `M.gs_pool gs s`: the set of Goldfish votes of slot `s` that `gs`
    has processed. -/
def Model.GS.pool {M : Model V} (gs : M.GS) (s : Slot) : Finset (GoldfishVote V) :=
  M.gs_pool gs s

/-- `gs.tau` is the operation `M.gs_tau gs`: the outcomes of the resolution times of `gs`'s Goldfish
    votes. -/
def Model.GS.tau {M : Model V} (gs : M.GS) : DC.NDRE (TimestampMap (GoldfishVote V)) :=
  M.gs_tau gs

/-- `hs.gradeView` is the operation `M.gradeView hs`: the part of `hs` the grades read. -/
def Model.HS.gradeView {M : Model V} (hs : M.HS) : M.GV :=
  M.gradeView hs

/-- `ns.setClock E t` is the operation `M.ns_setClock E ns t`: the named store `ns` with its time
    set to `t`. -/
def Model.NS.setClock {M : Model V} (E : Env V) (ns : M.NS) (t : Time) : M.NS :=
  M.ns_setClock E ns t

/-- `ns.process_block_core E hc cfg B` is the operation `M.ns_process_block_core E hc cfg ns B`: the
    named store `ns` after its store processes block `B`. -/
def Model.NS.process_block_core {M : Model V} (E : Env V) (hc : HealConfig) (cfg : HeightConfig)
    (ns : M.NS) (B : NamedBlock V) : M.NS :=
  M.ns_process_block_core E hc cfg ns B

/-- `ns.commitBlock st B` is the operation `M.commitBlock ns st B`: `ns` with store `st`, and with
    `B` among its named blocks if `st` newly holds `B`. -/
def Model.NS.commitBlock {M : Model V} (ns : M.NS) (st : M.S) (B : NamedBlock V) : M.NS :=
  M.commitBlock ns st B

end DecoupledConsensusModel.Sts.Record
