import Proofs.Instance.Members.Base

/-!
# Members of `Model.spec`: chain state to handlers

One definition per member of `Model V` in the families of the chain state, the schedule, the store,
the validator client, the handlers and the evidence, each named as the member in the namespace
`SpecRecord.Member` and given by the spec's behaviour. The instance `Model.spec` fills the
record with them.
-/

set_option autoImplicit false

namespace SpecRecord

open DecoupledConsensusModel (Block GoldfishVote CombinedAttestation NamedBlock NamedAttestation
  Env BlockId HeightPair FinalityPair NamedHeightPair Height Slot Round Time TimestampMap)
open DecoupledConsensusModel.Protocol (HeightConfig HealConfig SGVote CarriedAdmission)
open Spec (Config Provisional)
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Helpers -/

namespace ChainStateToHandlers

/-- The environment given to `Config.toSpec` and `Provisional.toSpec` by members whose routine reads
    none: delay `Δ = 1`, `t_GST = 0`, `default` as the proposer of every slot, empty committees, and
    every weight `1`. -/
def unreadEnv [Inhabited V] : Env V where
  Δ := 1
  Δ_pos := Int.one_pos
  t_GST := 0
  t_GST_nonneg := le_refl 0
  proposer := fun _ => default
  committees := ⟨fun _ => ∅⟩
  electorate := ⟨fun _ => 1, fun _ => Nat.one_pos⟩

/-- `Spec.Block.toSpec` as an embedding, so that a finite set of blocks is mapped with `Finset.map`. -/
def blockToSpecEmb : Block V ↪ Spec.Block V :=
  ⟨Spec.Block.toSpec, fun a b h => by
    have h' := congrArg Spec.Block.toProof h
    simpa only [Spec.Block.toProof_toSpec] using h'⟩

/-- `Spec.GoldfishVote.toSpec` as an embedding. -/
def goldfishVoteToSpecEmb : GoldfishVote V ↪ Spec.GoldfishVote V :=
  ⟨Spec.GoldfishVote.toSpec, fun a b h => by
    have h' := congrArg Spec.GoldfishVote.toProof h
    simpa only [Spec.GoldfishVote.toProof_toSpec] using h'⟩

/-- `sentGoldfishVote objs`: the first Goldfish vote among the objects `objs`, mapped by `toProof`,
    or `none` when there is none. -/
def sentGoldfishVote (objs : List (Spec.NamedObject V)) : Option (GoldfishVote V) :=
  objs.findSome? fun
    | .gfVote u => some u.toProof
    | _ => none

/-- `fieldsToSpec fields`: the optional triple of a height, a root and a flag, with the root mapped
    by `BlockId.toSpec`. -/
def fieldsToSpec (fields : Option (Height × BlockId × Bool)) :
    Option (Height × Spec.BlockId × Bool) :=
  fields.map fun f => (f.1, Spec.BlockId.toSpec f.2.1, f.2.2)

end ChainStateToHandlers

open ChainStateToHandlers

namespace Member

/-! ## The chain-state record `ChainStateModel` -/

/-- The type member `CS`: the spec's chain state `Spec.Protocol.ChainState V`. -/
abbrev CS (V : Type) : Type := Spec.Protocol.ChainState V

/-- The reader `h`: the height of `σ`. -/
def h (σ : CS V) : Height := σ.toProof.h

/-- The reader `T_h`: the block that took `σ` into its current height. -/
def T_h (σ : CS V) : Block V := σ.toProof.T_h

/-- The reader `nj`: whether `σ`'s current height is nonjustifiable. -/
def nj (σ : CS V) : Bool := σ.toProof.nj

/-- The reader `J`: the justified block of `σ`. -/
def J (σ : CS V) : Block V := σ.toProof.J

/-- The reader `h_j`: the justified height of `σ`. -/
def h_j (σ : CS V) : Height := σ.toProof.h_j

/-- The reader `F`: the finalized block of `σ`. -/
def F (σ : CS V) : Block V := σ.toProof.F

/-- The reader `h_F`: the finalized height of `σ`. -/
def h_F (σ : CS V) : Height := σ.toProof.h_F

/-- The reader `progress`: the validators `σ` counts towards progress at its current height. -/
def progress (σ : CS V) : Finset V := σ.toProof.progress

/-- The reader `target_participation`: the validators `σ` counts towards the target quorum at its
    current height. -/
def target_participation (σ : CS V) : Finset V := σ.toProof.target_participation

/-- The type member `Binding`: an interpretation of rows of type `Row`, a map from a row to an
    attestation. -/
abbrev Binding (V : Type) (Row : Type) : Type := Row → Spec.Attestation V

/-- The member `targeted`: a named attestation read as the spec's attestation,
    `Attestation.toSpecNamed`. -/
def targeted : Binding V (NamedAttestation V) := Spec.Attestation.toSpecNamed

/-- The member `process_attestation`: `σ` with the attestation `Attestation.toSpec a` counted by
    `Protocol.process_attestation`. -/
def process_attestation (σ : CS V) (a : CombinedAttestation V) : CS V :=
  Spec.Protocol.process_attestation σ (Spec.Attestation.toSpec a)

/-- The member `process_attestation_with`: `σ` with the attestation `b row` counted by
    `Protocol.process_attestation`. -/
def process_attestation_with {Row : Type} (b : Binding V Row) (σ : CS V) (row : Row) : CS V :=
  Spec.Protocol.process_attestation σ (b row)

/-- The member `fold_rows`: `Protocol.process_attestations` of `σ` at the spec form of `B` and the
    attestations `b` gives the rows. -/
def fold_rows {Row : Type} (b : Binding V Row) (σ : CS V) (B : Block V) (rows : List Row) :
    CS V :=
  Spec.Protocol.process_attestations σ (Spec.Block.toSpec B) (rows.map b)

/-- The member `process_height_events`: `Protocol.process_height_events` at
    `Config.toSpec E unreadHealConfig cfg` and `Provisional.toSpec E`. -/
def process_height_events (E : Env V) (cfg : HeightConfig) (σ : CS V) : CS V :=
  Spec.Protocol.process_height_events (Config.toSpec E unreadHealConfig cfg)
    (Provisional.toSpec E) σ

/-- The member `finalityReady`: `Protocol.finalityReady` at `Provisional.toSpec E`. -/
def finalityReady (E : Env V) (σ : CS V) : Bool :=
  Spec.Protocol.finalityReady (Provisional.toSpec E) σ

/-- The member `targetReady`: `Protocol.targetReady` at `Provisional.toSpec E`. -/
def targetReady (E : Env V) (σ : CS V) : Bool :=
  Spec.Protocol.targetReady (Provisional.toSpec E) σ

/-- The member `progReady`: `Protocol.progReady` at `Config.toSpec E unreadHealConfig cfg` and
    `Provisional.toSpec E`. -/
def progReady (E : Env V) (cfg : HeightConfig) (σ : CS V) : Bool :=
  Spec.Protocol.progReady (Config.toSpec E unreadHealConfig cfg) (Provisional.toSpec E) σ

/-- The member `named_transition`: `Protocol.state_transition` at
    `Config.toSpec E unreadHealConfig cfg`, `Provisional.toSpec E` and `Block.toSpecNamed B`. -/
def named_transition (E : Env V) (cfg : HeightConfig) (σ : CS V) (B : NamedBlock V) : CS V :=
  Spec.Protocol.state_transition (Config.toSpec E unreadHealConfig cfg)
    (Provisional.toSpec E) σ (Spec.Block.toSpecNamed B)

/-- The member `derive_named`: the chain state of a named block, the initial chain state at genesis
    and `named_transition` of the parent's chain state otherwise. -/
def derive_named (E : Env V) (cfg : HeightConfig) : NamedBlock V → CS V
  | .genesis => Spec.Protocol.ChainState.initial
  | B@(.node p _ _ _ _ _ _) => named_transition E cfg (derive_named E cfg p) B

/-- The member `conflictsWithFinality`: `DecoupledConsensusModel.Protocol.conflictsWithFinality`. -/
def conflictsWithFinality : HeightPair → FinalityPair → Bool :=
  DecoupledConsensusModel.Protocol.conflictsWithFinality

/-- The member `e2Fields`: `DecoupledConsensusModel.Protocol.e2Fields`. -/
def e2Fields (left right : CombinedAttestation V) : Bool :=
  DecoupledConsensusModel.Protocol.e2Fields left right

/-- The member `Slashable`: `DecoupledConsensusModel.Protocol.Slashable`. -/
def Slashable (left right : CombinedAttestation V) : Prop :=
  DecoupledConsensusModel.Protocol.Slashable left right

/-! ## The chain state beyond `ChainStateModel` -/

/-- The reader `L`: the latest block of `σ`. -/
def L (σ : CS V) : Block V := σ.toProof.L

/-- The reader `cs_s`: the slot of `σ`. -/
def cs_s (σ : CS V) : Slot := σ.toProof.s

/-- The reader `finalize`: the validators `σ` counts towards finalizing its justified block. -/
def finalize (σ : CS V) : Finset V := σ.toProof.finalize

/-- The member `cs_initial`: the initial chain state `Protocol.ChainState.initial`. -/
def cs_initial : CS V := Spec.Protocol.ChainState.initial

/-- The member `advance_height`: `Protocol.advance_height` at
    `Config.toSpec unreadEnv unreadHealConfig cfg`. -/
def advance_height [Inhabited V] (cfg : HeightConfig) (σ : CS V) : CS V :=
  Spec.Protocol.advance_height (Config.toSpec (unreadEnv (V := V)) unreadHealConfig cfg) σ

/-- The member `slashable`: `DecoupledConsensusModel.Protocol.slashable`. -/
def slashable (left right : CombinedAttestation V) : Bool :=
  DecoupledConsensusModel.Protocol.slashable left right

/-- The member `e1Fields`: `DecoupledConsensusModel.Protocol.e1Fields`. -/
def e1Fields (left right : CombinedAttestation V) : Bool :=
  DecoupledConsensusModel.Protocol.e1Fields left right

/-- The member `e1Slashable`: `DecoupledConsensusModel.Protocol.e1Slashable`. -/
def e1Slashable (left right : CombinedAttestation V) : Bool :=
  DecoupledConsensusModel.Protocol.e1Slashable left right

/-- The member `e2Slashable`: `DecoupledConsensusModel.Protocol.e2Slashable`. -/
def e2Slashable (left right : CombinedAttestation V) : Bool :=
  DecoupledConsensusModel.Protocol.e2Slashable left right

/-- The member `sameValidator`: `DecoupledConsensusModel.Protocol.sameValidator`. -/
def sameValidator (left right : CombinedAttestation V) : Bool :=
  DecoupledConsensusModel.Protocol.sameValidator left right

/-- The member `transition_rows`: `fold_rows` followed by `Protocol.process_height_events` at
    `Config.toSpec E unreadHealConfig cfg` and `Provisional.toSpec E`. -/
def transition_rows {Row : Type} (b : Binding V Row) (E : Env V) (cfg : HeightConfig) (σ : CS V)
    (B : Block V) (rows : List Row) : CS V :=
  Spec.Protocol.process_height_events (Config.toSpec E unreadHealConfig cfg)
    (Provisional.toSpec E) (fold_rows b σ B rows)

/-- The member `nonjustifiable`: `Protocol.nonjustifiable` at
    `Config.toSpec unreadEnv unreadHealConfig cfg`, the environment taken over the validator type
    `Unit`. -/
def nonjustifiable (cfg : HeightConfig) (h h_F : Height) : Bool :=
  Spec.Protocol.nonjustifiable
    (Config.toSpec (unreadEnv (V := Unit)) unreadHealConfig cfg) h h_F

/-- The member `cs_with_F_h_F`: `σ` with finalized block `Spec.Block.toSpec B` and finalized height
    `h`. -/
def cs_with_F_h_F (σ : CS V) (B : Block V) (h : Height) : CS V :=
  { σ with F := Spec.Block.toSpec B, h_F := h }

/-! ## The schedule -/

/-- The member `proposal_time`: `Config.proposal_time` at
    `Config.toSpec E unreadHealConfig unreadHeightConfig`. -/
def proposal_time (E : Env V) (s : Slot) : Time :=
  (Config.toSpec E unreadHealConfig unreadHeightConfig).proposal_time s

/-- The member `vote_time`: `Config.vote_time` at
    `Config.toSpec E unreadHealConfig unreadHeightConfig`. -/
def vote_time (E : Env V) (s : Slot) : Time :=
  (Config.toSpec E unreadHealConfig unreadHeightConfig).vote_time s

/-- The member `support_cutoff`: `Config.gf_confirmation_time` at
    `Config.toSpec E unreadHealConfig unreadHeightConfig`. -/
def support_cutoff (E : Env V) (s : Slot) : Time :=
  (Config.toSpec E unreadHealConfig unreadHeightConfig).gf_confirmation_time s

/-- The member `view_freeze`: `Config.view_freeze` at
    `Config.toSpec E unreadHealConfig unreadHeightConfig`. -/
def view_freeze (E : Env V) (s : Slot) : Time :=
  (Config.toSpec E unreadHealConfig unreadHeightConfig).view_freeze s

/-- The member `confirmation_time`: `Config.confirmation_time` at
    `Config.toSpec E unreadHealConfig unreadHeightConfig`. -/
def confirmation_time (E : Env V) (s : Slot) : Time :=
  (Config.toSpec E unreadHealConfig unreadHeightConfig).confirmation_time s

/-- The member `proposal_wake_start`: `grade1_window_start` of the round of slot `s` at
    `(Setup.toSpec S).C`, the start of the window throughout which slot `s`'s proposer must be awake
    to propose. -/
def proposal_wake_start (S : DecoupledConsensusModel.Execution.Setup V) (s : Slot) : Int :=
  Spec.grade1_window_start (Setup.toSpec S).C ((Setup.toSpec S).C.round_of s)

/-- The member `votes_by`: `Protocol.votes_by` at the spec forms of the votes, mapped back: the
    votes of validator `v` in the set. -/
def votes_by (votes : Finset (GoldfishVote V)) (v : V) : Finset (GoldfishVote V) :=
  (Spec.Protocol.votes_by (votes.map goldfishVoteToSpecEmb) v).map
    Spec.GoldfishVote.toProofEmb

/-- The member `equivocates`: `Protocol.equivocates` at the spec forms of the votes: whether `v` has
    two different votes in the set. -/
def equivocates (votes : Finset (GoldfishVote V)) (v : V) : Bool :=
  Spec.Protocol.equivocates (votes.map goldfishVoteToSpecEmb) v

/-- The member `participates`: `Protocol.participates` at the spec forms of the votes: whether `v`
    has a vote in the set. -/
def participates (votes : Finset (GoldfishVote V)) (v : V) : Bool :=
  Spec.Protocol.participates (votes.map goldfishVoteToSpecEmb) v

/-! ## The store -/

/-- The reader `gs_s`: the current slot of `st`. -/
def gs_s (st : Spec.Store V) : Slot :=
  st.toProof.toHealing.toFG.toSG.toGoldfishStore.s

/-- The reader `gs_T`: the blocks `st` has processed. -/
def gs_T (st : Spec.Store V) : Finset (Block V) :=
  st.toProof.toHealing.toFG.toSG.toGoldfishStore.T

/-- The reader `gs_timestamp_block`: the time at which `st` received each block. -/
def gs_timestamp_block (st : Spec.Store V) : TimestampMap (Block V) :=
  st.toProof.toHealing.toFG.toSG.toGoldfishStore.timestamp_block

/-- The reader `gs_timestamp_vote`: the time at which `st` received each Goldfish vote. -/
def gs_timestamp_vote (st : Spec.Store V) : TimestampMap (GoldfishVote V) :=
  st.toProof.toHealing.toFG.toSG.toGoldfishStore.timestamp_vote

/-- The reader `gs_gf_votes`: the Goldfish votes of slot `s` that `st` has processed. -/
def gs_gf_votes (st : Spec.Store V) (s : Slot) : List (GoldfishVote V) :=
  st.toProof.toHealing.toFG.toSG.toGoldfishStore.gf_votes s

/-- The reader `gs_live_confirmed`: the block `st` confirms for voting. -/
def gs_live_confirmed (st : Spec.Store V) : Block V :=
  st.toProof.toHealing.toFG.toSG.toGoldfishStore.live_confirmed

/-- The reader `store_t`: the current time of `st`. -/
def store_t (st : Spec.Store V) : Time := st.toProof.t

/-- The reader `store_s`: the current slot of `st`. -/
def store_s (st : Spec.Store V) : Slot := st.toProof.s

/-- The reader `store_T`: the blocks `st` has processed. -/
def store_T (st : Spec.Store V) : Finset (Block V) := st.toProof.T

/-- The reader `store_timestamp_block`: the time at which `st` received each block. -/
def store_timestamp_block (st : Spec.Store V) : TimestampMap (Block V) :=
  st.toProof.timestamp_block

/-- The reader `store_timestamp_vote`: the time at which `st` received each Goldfish vote. -/
def store_timestamp_vote (st : Spec.Store V) : TimestampMap (GoldfishVote V) :=
  st.toProof.timestamp_vote

/-- The reader `store_timestamp_sg_vote`: the time at which `st` received each SG vote. -/
def store_timestamp_sg_vote (st : Spec.Store V) : TimestampMap (SGVote V) :=
  st.toProof.timestamp_sg_vote

/-- The reader `store_σ`: the chain state `st` holds for the block `st.blockOfImage B`. -/
def store_σ (st : Spec.Store V) (B : Block V) : CS V :=
  st.σ (st.blockOfImage B)

/-- The reader `store_gf_votes`: the Goldfish votes of slot `s` that `st` has processed. -/
def store_gf_votes (st : Spec.Store V) (s : Slot) : List (GoldfishVote V) :=
  st.toProof.gf_votes s

/-- The reader `store_sg_votes`: the attestations of round `r` that `st` has processed. -/
def store_sg_votes (st : Spec.Store V) (r : Round) : List (CombinedAttestation V) :=
  st.toProof.sg_votes r

/-- The reader `store_F`: the finalized block of `st`. -/
def store_F (st : Spec.Store V) : Block V := st.toProof.F

/-- The reader `store_J`: the justified block of `st`. -/
def store_J (st : Spec.Store V) : Block V := st.toProof.J

/-- The reader `store_h_j`: the justified height of `st`. -/
def store_h_j (st : Spec.Store V) : Height := st.toProof.h_j

/-- The reader `store_h_max`: the largest height `st` has seen. -/
def store_h_max (st : Spec.Store V) : Height := st.toProof.h_max

/-- The reader `store_live_confirmed`: the block `st` confirms for voting. -/
def store_live_confirmed (st : Spec.Store V) : Block V := st.toProof.live_confirmed

/-- The reader `store_latest_confirmed`: the block `st` last recorded as confirmed. -/
def store_latest_confirmed (st : Spec.Store V) : Block V := st.toProof.latest_confirmed

/-- The reader `store_latest_stable`: the block `st` last recorded as stable. -/
def store_latest_stable (st : Spec.Store V) : Block V := st.toProof.latest_stable

/-- The member `store_tau`: the resolution times of `st`. Its one outcome maps each vote `st` has
    stamped to the answer of `Store.tau` on its spec form, and every other vote to `none`; there is
    no outcome when `Store.tau` fails on a stamped vote. -/
def store_tau (st : Spec.Store V) : DC.NDRE (TimestampMap (GoldfishVote V)) :=
  ExceptT.mk {x | ∃ f : TimestampMap (GoldfishVote V),
    (∀ u : GoldfishVote V, (st.timestamp_vote (Spec.GoldfishVote.toSpec u)).isSome →
      st.tau (Spec.GoldfishVote.toSpec u) = .ok (f u)) ∧
    (∀ u : GoldfishVote V, st.timestamp_vote (Spec.GoldfishVote.toSpec u) = none →
      f u = none) ∧
    x = .ok f}

/-- The member `toHealing`: the identity. -/
def toHealing (st : Spec.Store V) : Spec.Store V := st

/-- The member `store_pool`: `Store.pool`, mapped: the Goldfish votes of slot `s` that `st` has
    processed. -/
def store_pool (st : Spec.Store V) (s : Slot) : Finset (GoldfishVote V) :=
  (st.pool s).map Spec.GoldfishVote.toProofEmb

/-- The member `sgVote`: `Protocol.sgVote` at `Attestation.toSpec a`, mapped: the validator, round
    and confirmed block of `a`. -/
def sgVote (a : CombinedAttestation V) : SGVote V :=
  (Spec.Protocol.sgVote (Spec.Attestation.toSpec a)).toProof

/-- The member `store_sg_pool`: the images under `Attestation.toProof` of `Store.sg_pool`, the
    attestations of round `r` that `st` has processed. -/
def store_sg_pool (st : Spec.Store V) (r : Round) : Finset (CombinedAttestation V) :=
  (st.sg_pool r).image Spec.Attestation.toProof

/-- The member `resolved`: the outcome of `Protocol.resolved` at the spec forms of the tree and the
    vote, with `orVocabulary` supplying an answer where that routine raises. -/
def resolved (T : Finset (Block V)) (u : GoldfishVote V) : DC.NDRE Bool :=
  successOutcomes (orVocabulary
    (Spec.Protocol.resolved (T.map blockToSpecEmb) (Spec.GoldfishVote.toSpec u))
    (DecoupledConsensusModel.Protocol.resolved T u))

/-- The member `gs_pool`: `Store.pool`, mapped: the Goldfish votes of slot `s` that `st` has
    processed. -/
def gs_pool (st : Spec.Store V) (s : Slot) : Finset (GoldfishVote V) :=
  (st.pool s).map Spec.GoldfishVote.toProofEmb

/-- The member `gs_tau`: the member `store_tau`. -/
def gs_tau (st : Spec.Store V) : DC.NDRE (TimestampMap (GoldfishVote V)) :=
  store_tau st

/-- The member `store_with_t_s`: `st` with time `t` and slot `s`. -/
def store_with_t_s (st : Spec.Store V) (t : Time) (s : Slot) : Spec.Store V :=
  { st with t := t, s := s }

/-- The member `store_with_h_max`: `st` with largest seen height `h`. -/
def store_with_h_max (st : Spec.Store V) (h : Height) : Spec.Store V :=
  { st with h_max := h }

/-- The member `store_with_J_h_j`: `st` with justified block `st.blockOfImage B` and justified
    height `h`. -/
def store_with_J_h_j (st : Spec.Store V) (B : Block V) (h : Height) :
    Spec.Store V :=
  { st with J := st.blockOfImage B, h_j := h }

/-- The member `store_with_σ_T_timestamp_block`: `st` with chain state `σ' B.toProof` for each block
    `B`, tree the blocks `st.blockOfImage` gives for the blocks of `T'`, and block stamp
    `τ' B.toProof` for each block `B`. -/
def store_with_σ_T_timestamp_block (st : Spec.Store V) (σ' : Block V → CS V)
    (T' : Finset (Block V)) (τ' : TimestampMap (Block V)) : Spec.Store V :=
  { st with
    σ := fun B => σ' B.toProof
    T := T'.map st.blockOfImageEmb
    timestamp_block := fun B => τ' B.toProof }

/-- The member `store_init`: the initial store `Store.init`. -/
def store_init : Spec.Store V := Spec.Store.init

/-! ## The validator client -/

/-- The reader `target`: the target `sh` has voted at height `h`, if any. -/
def target (sh : Spec.SigningHistory) (h : Height) : Option BlockId :=
  sh.toProof.legacy.target h

/-- The reader `timeout`: whether `sh` has voted a timeout at height `h`. -/
def timeout (sh : Spec.SigningHistory) (h : Height) : Bool :=
  sh.toProof.legacy.timeout h

/-- The reader `lock`: the block `sh` is locked on at height `h`, if any. -/
def lock (sh : Spec.SigningHistory) (h : Height) : Option BlockId :=
  sh.toProof.legacy.lock h

/-- The member `legacy`: the signing history `sh` with its timeout votes erased,
    `{ sh with timeouts := ∅ }`. -/
def legacy (sh : Spec.SigningHistory) : Spec.SigningHistory :=
  { sh with timeouts := ∅ }

/-- The reader `nr_timeoutHistory`: the pairs of a height and a block that `sh` has recorded as
    timeout votes. -/
def nr_timeoutHistory (sh : Spec.SigningHistory) : Finset (Height × BlockId) :=
  sh.toProof.timeoutHistory

/-- The member `own_lock`: `Protocol.own_lock` at the spec form of the finality pair, mapped: the
    block `sh` treats as its lock at height `h`. -/
def own_lock (sh : Spec.SigningHistory) (h : Height) (fp : Option FinalityPair) :
    Option BlockId :=
  (Spec.Protocol.own_lock sh h (fp.map Spec.FinalityPair.toSpec)).map
    Spec.BlockId.toProof

/-- The member `height_pair`: `Protocol.height_pair` at the spec forms of the triple and the
    finality pair, mapped: the height pair `sh` signs next. -/
def height_pair (sh : Spec.SigningHistory) (fields : Option (Height × BlockId × Bool))
    (fp : Option FinalityPair) : HeightPair :=
  (Spec.Protocol.height_pair sh (fieldsToSpec fields)
    (fp.map Spec.FinalityPair.toSpec)).toProof

/-- The member `create_attestation`: `Protocol.create_attestation` at the spec forms of the
    confirmed root, the triple and the justified root, its attestation mapped: the updated signing
    history and the attestation `sh` signs. -/
def create_attestation (sh : Spec.SigningHistory) (v : V) (r : Round)
    (confirmed : Option BlockId) (fields : Option (Height × BlockId × Bool)) (h_j : Height)
    (J : BlockId) (h_F : Height) : Spec.SigningHistory × CombinedAttestation V :=
  Prod.map id Spec.Attestation.toProof
    (Spec.Protocol.create_attestation sh v r
      (confirmed.map Spec.BlockId.toSpec) (fieldsToSpec fields) h_j
      (Spec.BlockId.toSpec J) h_F)

/-- The member `finality_pair`: `Protocol.finality_pair` at the spec form of the justified root,
    mapped: the finality pair `sh` signs next, if any. -/
def finality_pair (sh : Spec.SigningHistory) (h_j : Height) (J : BlockId) (h_F : Height) :
    Option FinalityPair :=
  (Spec.Protocol.finality_pair sh h_j (Spec.BlockId.toSpec J) h_F).map
    Spec.FinalityPair.toProof

/-- The member `encodeHeight`: `DecoupledConsensusModel.Protocol.NamedRecord.encodeHeight`, the
    height pair written with the entry it names. -/
def encodeHeight (fields : Option (Height × BlockId × Bool)) (pair : HeightPair) :
    NamedHeightPair :=
  DecoupledConsensusModel.Protocol.NamedRecord.encodeHeight fields pair

/-- The member `record_attestation`: `sh` after `Protocol.record_attestation` records
    `Attestation.toSpec a`. -/
def record_attestation (sh : Spec.SigningHistory) (a : CombinedAttestation V) :
    Spec.SigningHistory :=
  Spec.Protocol.record_attestation sh (Spec.Attestation.toSpec a)

/-! ## The handlers -/

/-- The member `core`: the identity. -/
def core : Spec.Store V → Spec.Store V := id

/-- The member `sameCore`: `a` and `b` have equal images under `Store.toProof`. -/
def sameCore (a b : Spec.Store V) : Prop := a.toProof = b.toProof

/-- The reader `bodies`: the blocks of `st`'s tree, each mapped by `Block.toProofNamed`. -/
def bodies (st : Spec.Store V) : Finset (NamedBlock V) :=
  st.T.map Spec.Block.toProofNamedEmb

/-- The reader `sg_rows`: the attestations of round `r` that `st` holds, as named attestations. -/
def sg_rows (st : Spec.Store V) (r : Round) : List (NamedAttestation V) :=
  st.toProofNamed.sg_rows r

/-- The member `ns_setClock`: `st` with its time set to `t` and its slot to the slot of `t`. -/
def ns_setClock (E : Env V) (st : Spec.Store V) (t : Time) : Spec.Store V :=
  { st with t := t, s := (Config.toSpec E unreadHealConfig unreadHeightConfig).slotOf t }

/-- The member `get_stable`: `Protocol.get_stable` on `st` read through its tree (`Store.ofImage`),
    mapped: the block `st` exposes as stable. -/
def get_stable (st : Spec.Store V) : Block V :=
  (Spec.Protocol.get_stable (Spec.Store.ofImage st)).toProof

/-- The member `round_votes`: `Protocol.round_votes` at `Attestation.toSpec a`, each root mapped:
    the roots `a`'s validator has voted in `a`'s round, in `st`. -/
def round_votes (st : Spec.Store V) (a : CombinedAttestation V) :
    Finset (Option BlockId) :=
  (Spec.Protocol.round_votes st (Spec.Attestation.toSpec a)).map
    (Function.Embedding.optionMap Spec.BlockId.toProofEmb)

/-- The member `on_block_with`: `Protocol.on_block` at `Config.toSpec E hc cfg`,
    `Provisional.toSpec E` and `Block.toSpecNamed B`, the store `st` after it receives the named
    block `B`. The argument `_admission` is not read. -/
def on_block_with (_admission : CarriedAdmission) (E : Env V) (hc : HealConfig)
    (cfg : HeightConfig) (st : Spec.Store V) (B : NamedBlock V) :
    Spec.Store V :=
  Spec.Protocol.on_block (Config.toSpec E hc cfg) (Provisional.toSpec E) st
    (Spec.Block.toSpecNamed B)

/-- The member `admit_row`: `Protocol.admit_attestation` at
    `Config.toSpec unreadEnv hc unreadHeightConfig` and `Attestation.toSpecNamed a`, the store `st`
    after it receives the named attestation `a`. -/
def admit_row [Inhabited V] (hc : HealConfig) (st : Spec.Store V)
    (a : NamedAttestation V) : Spec.Store V :=
  Spec.Protocol.admit_attestation
    (Config.toSpec (unreadEnv (V := V)) hc unreadHeightConfig) st
    (Spec.Attestation.toSpecNamed a)

/-- The member `update_confirmation_with`: the outcomes of slot `s`'s `Protocol.update_confirmation`
    at `Config.toSpec E hc unreadHeightConfig`, on `st` read through its tree with its saved grades
    replaced by `c` read through the tree, brought to the store's round and filled; no outcome when
    the routine fails. The store returned holds `c` as given. -/
def update_confirmation_with (c : Spec.SavedGrades V) (E : Env V) (hc : HealConfig)
    (st : Spec.Store V) (s : Slot) : DC.NDRE (Spec.Store V) :=
  successOutcomes
    ((Spec.Protocol.update_confirmation (Config.toSpec E hc unreadHeightConfig)
      { Spec.Store.ofImage st with saved_grades := fill (Spec.Protocol.advance_to_round
          (st.contractOfImage c) ((Config.toSpec E hc unreadHeightConfig).round_of st.s)) } s).map
      fun out => { out with saved_grades := c })

/-- The member `on_goldfish_vote_checked`: `Protocol.on_goldfish_vote_checked` at
    `Provisional.toSpec E` and the spec form of `u`, the store `st` after it receives `u`. -/
def on_goldfish_vote_checked (E : Env V) (st : Spec.Store V) (u : GoldfishVote V) :
    Spec.Store V :=
  Spec.Protocol.on_goldfish_vote_checked (Provisional.toSpec E) st
    (Spec.GoldfishVote.toSpec u)

/-- The member `get_confirmed`: `Protocol.get_confirmed` on `st` read through its tree
    (`Store.ofImage`), mapped: the block `st` exposes as confirmed. -/
def get_confirmed (st : Spec.Store V) : Block V :=
  (Spec.Protocol.get_confirmed (Spec.Store.ofImage st)).toProof

/-- The member `carried_attestations_admissible`: `Protocol.included_attestations_admissible` at the
    spec form of `B`: whether every attestation `B` includes is of `B`'s round or an earlier one. -/
def carried_attestations_admissible [Inhabited V] (hc : HealConfig) (B : Block V) : Bool :=
  Spec.Protocol.included_attestations_admissible
    (Config.toSpec (unreadEnv (V := V)) hc unreadHeightConfig) (Spec.Block.toSpec B)

/-- The member `on_sg_vote`: `Protocol.admit_attestation` at
    `Config.toSpec unreadEnv hc unreadHeightConfig` and `Attestation.toSpec a`, the store `st` after
    it receives `a`. -/
def on_sg_vote [Inhabited V] (hc : HealConfig) (st : Spec.Store V)
    (a : CombinedAttestation V) : Spec.Store V :=
  Spec.Protocol.admit_attestation
    (Config.toSpec (unreadEnv (V := V)) hc unreadHeightConfig) st
    (Spec.Attestation.toSpec a)

/-- The member `admit_rows`: `Protocol.admit_attestations` at
    `Config.toSpec unreadEnv hc unreadHeightConfig` and the spec forms of the named attestations,
    the store `st` after it receives each of them in order. -/
def admit_rows [Inhabited V] (hc : HealConfig) (st : Spec.Store V)
    (rows : List (NamedAttestation V)) : Spec.Store V :=
  Spec.Protocol.admit_attestations
    (Config.toSpec (unreadEnv (V := V)) hc unreadHeightConfig) st
    (rows.map Spec.Attestation.toSpecNamed)

/-- The member `advance_confirmed`: `Protocol.advance_confirmed` at the spec forms of the blocks,
    mapped: `old` when `candidate` is an ancestor of it, `candidate` otherwise. -/
def advance_confirmed (old candidate : Block V) : Block V :=
  (Spec.Protocol.advance_confirmed (Spec.Block.toSpec old)
    (Spec.Block.toSpec candidate)).toProof

/-- The member `ns_process_block_core`: `Handlers.admitBlockCore` at `Config.toSpec E hc cfg`,
    `Provisional.toSpec E` and `Block.toSpecNamed B`, the store `st` after it admits `B`, its
    attestations not yet admitted. -/
def ns_process_block_core (E : Env V) (hc : HealConfig) (cfg : HeightConfig)
    (st : Spec.Store V) (B : NamedBlock V) : Spec.Store V :=
  Handlers.admitBlockCore (Config.toSpec E hc cfg) (Provisional.toSpec E) st
    (Spec.Block.toSpecNamed B)

/-- The member `voter_filtered_block_tree`: the outcomes of `Protocol.voter_filtered_block_tree` for
    slot `s` on `st` read through its tree, each block mapped; no outcome when a tree block has no
    stamp. -/
def voter_filtered_block_tree (E : Env V) (st : Spec.Store V) (s : Slot) :
    DC.NDRE (Finset (Block V)) :=
  successOutcomes
    ((Spec.Protocol.voter_filtered_block_tree
      (Config.toSpec E unreadHealConfig unreadHeightConfig) (Spec.Store.ofImage st) s).map
      (fun T => T.image Spec.Block.toProof))

/-- The member `floor_on_stable`: `Protocol.floor_on_stable` at the spec forms of the blocks,
    mapped: `candidate` when it is a descendant of `stable`; otherwise `old` when it is one;
    otherwise `stable`. -/
def floor_on_stable (stable candidate old : Block V) : Block V :=
  (Spec.Protocol.floor_on_stable (Spec.Block.toSpec stable)
    (Spec.Block.toSpec candidate) (Spec.Block.toSpec old)).toProof

/-- The member `on_block_using`: `Handlers.onBlockUsing` at `Provisional.toSpec E`, the block
    `st.blockOfImage B` and the chain-state builder `buildState`. -/
def on_block_using (E : Env V) (st : Spec.Store V) (B : Block V)
    (buildState : CS V → CS V) : Spec.Store V :=
  Handlers.onBlockUsing (Provisional.toSpec E) st (st.blockOfImage B) buildState

/-- The member `on_block_checked_using`: `handle st` when the attestations the spec form of `B`
    includes pass `Protocol.included_attestations_admissible`, and `st` otherwise. -/
def on_block_checked_using [Inhabited V] (handle : Spec.Store V → Spec.Store V)
    (hc : HealConfig) (st : Spec.Store V) (B : Block V) : Spec.Store V :=
  Handlers.onBlockCheckedUsing (Config.toSpec (unreadEnv (V := V)) hc unreadHeightConfig)
    handle st (Spec.Block.toSpec B)

/-- The member `on_goldfish_vote`: `Protocol.on_goldfish_vote` at the spec form of `u`, the store
    `st` after it stores `u`. -/
def on_goldfish_vote (st : Spec.Store V) (u : GoldfishVote V) : Spec.Store V :=
  Spec.Protocol.on_goldfish_vote st (Spec.GoldfishVote.toSpec u)

/-- The member `goldfish_vote_with`: the outcomes of the Goldfish vote duty `Protocol.goldfish_vote`
    of `nd.val_index` on `st` read through its tree with its saved grades replaced by `c` read
    through the tree, brought to the store's round and filled; each outcome is the returned store
    and the vote the duty broadcast, if any. No outcome when the duty fails. -/
def goldfish_vote_with (c : Spec.SavedGrades V) (E : Env V) (hc : HealConfig)
    (nd : DecoupledConsensusModel.Protocol.Node V) (st : Spec.Store V) :
    DC.NDRE (Spec.Store V × Option (GoldfishVote V)) :=
  successOutcomes
    (((Spec.Protocol.goldfish_vote (Config.toSpec E hc unreadHeightConfig)
      (Provisional.toSpec E) nd.val_index
        { Spec.Store.ofImage st with saved_grades := fill (Spec.Protocol.advance_to_round
            (st.contractOfImage c) ((Config.toSpec E hc unreadHeightConfig).round_of st.s)) }
        ).run []).map
      (fun out => ({ out.1 with saved_grades := c }, sentGoldfishVote out.2)))

/-- The member `ns_initial`: the initial store `Store.init`. -/
def ns_initial : Spec.Store V := Spec.Store.init

/-- The member `update_finality`: `Handlers.updateFinalityWith st σ`, the store `st` with its
    finality fields taken from `σ`. -/
def update_finality (st : Spec.Store V) (σ : CS V) : Spec.Store V :=
  Handlers.updateFinalityWith st σ

/-- The member `admit_carried`: `Handlers.admitCarried` at `Block.toSpecNamed B`, the store `after`
    with the attestations `B` includes admitted when `B` is newly in its tree. The argument
    `_admission` is not read. -/
def admit_carried [Inhabited V] (_admission : CarriedAdmission) (hc : HealConfig)
    (before after : Spec.Store V) (B : NamedBlock V) : Spec.Store V :=
  Handlers.admitCarried (Config.toSpec (unreadEnv (V := V)) hc unreadHeightConfig) before after
    (Spec.Block.toSpecNamed B)

/-- The member `get_head_in_tree_with`: the outcomes of `Protocol.get_head_in_tree_with_layer` on
    `st` read through its tree with its saved grades replaced by `c` read through the tree, brought
    to the store's round and filled, at the blocks `st.blockOfImage` gives for `tree` and the spec
    forms of the two vote sets, the head mapped; no outcome when the routine fails. -/
def get_head_in_tree_with (c : Spec.SavedGrades V) (E : Env V) (hc : HealConfig)
    (st : Spec.Store V) (tree : Finset (Block V))
    (votes support_votes : Finset (GoldfishVote V)) (s : Slot) : DC.NDRE (Block V) :=
  successOutcomes
    ((Spec.Protocol.get_head_in_tree_with_layer (Config.toSpec E hc unreadHeightConfig)
      { Spec.Store.ofImage st with saved_grades := fill (Spec.Protocol.advance_to_round
          (st.contractOfImage c) ((Config.toSpec E hc unreadHeightConfig).round_of st.s)) }
        (tree.map st.blockOfImageEmb) (votes.map goldfishVoteToSpecEmb)
      (support_votes.map goldfishVoteToSpecEmb) s).map Spec.Block.toProof)

/-- The member `state_transition`: `Protocol.state_transition` at
    `Config.toSpec E unreadHealConfig cfg`, `Provisional.toSpec E` and `Block.toSpec B`, `σ` after
    the transition by block `B`. -/
def state_transition (E : Env V) (cfg : HeightConfig) (σ : CS V) (B : Block V) : CS V :=
  Spec.Protocol.state_transition (Config.toSpec E unreadHealConfig cfg)
    (Provisional.toSpec E) σ (Spec.Block.toSpec B)

/-- The member `ns_with_core`: the store `c`. -/
def ns_with_core (_ns c : Spec.Store V) : Spec.Store V := c

/-- The member `commitBlock`: the store `after`. -/
def commitBlock (_before after : Spec.Store V) (_B : NamedBlock V) :
    Spec.Store V :=
  after

/-! ## The evidence -/

/-- The member `chain_attestations`: `DecoupledConsensusModel.chain_attestations`, the attestations
    included in `B` or one of its ancestors. -/
def chain_attestations (B : Block V) : Finset (CombinedAttestation V) :=
  DecoupledConsensusModel.chain_attestations B

/-- The member `HasSlashableWeightBetween`: `DecoupledConsensusModel.HasSlashableWeightBetween`. -/
def HasSlashableWeightBetween (E : Env V) (A₁ A₂ : Finset (CombinedAttestation V)) : Prop :=
  DecoupledConsensusModel.HasSlashableWeightBetween E A₁ A₂

/-- The member `store_attestations`: the attestations included in a block of `st`'s tree or one of
    its ancestors. -/
def store_attestations (st : Spec.Store V) : Finset (CombinedAttestation V) :=
  (st.T.image Spec.Block.toProof).biUnion DecoupledConsensusModel.chain_attestations

/-- The member `SlashableBetween`: `DecoupledConsensusModel.SlashableBetween`, some attestation in
    `A₁` and one in `A₂`, both signed by `i`, are slashable. -/
def SlashableBetween (A₁ A₂ : Finset (CombinedAttestation V)) (i : V) : Prop :=
  DecoupledConsensusModel.SlashableBetween A₁ A₂ i

/-- The member `HasIntersectionWeight`: `DecoupledConsensusModel.HasIntersectionWeight`. -/
def HasIntersectionWeight (E : Env V) (S : Finset V) : Prop :=
  DecoupledConsensusModel.HasIntersectionWeight E S

end Member

end SpecRecord
