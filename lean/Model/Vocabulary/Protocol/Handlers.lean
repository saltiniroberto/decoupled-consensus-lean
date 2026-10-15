module
public import Model.Vocabulary.Objects.Blocks
public import Model.Vocabulary.Protocol.Store
public import Model.Vocabulary.Protocol.ChainState
public import Model.Vocabulary.Protocol.Schedule
public import Model.Vocabulary.Protocol.Grades

@[expose] public section

/-!
# Store handlers and duties

The confirmation record updates, the finality update, the block, Goldfish vote and SG vote handlers,
the confirmation update and the Goldfish vote duty, with the admission paths for named objects.
-/

section
/-! ## Confirmation record update -/

namespace DecoupledConsensusModel
namespace Protocol

variable {V : Type} [DecidableEq V]

/-- `candidate` replaces `old` unless it is an ancestor of, or equal to, `old`. -/
def advance_confirmed (old candidate : Block V) : Block V :=
  if Block.preceq candidate old then old else candidate

/-- The confirmation record floored on the stable record: `candidate` when `stable ⪯ candidate`;
    else `old` when `stable ⪯ old`; else `stable`. -/
@[irreducible] def floor_on_stable (stable candidate old : Block V) : Block V :=
  if Block.preceq stable candidate then candidate
  else if Block.preceq stable old then old else stable

end Protocol
end DecoupledConsensusModel
end

section
/-! ## Store handlers -/

namespace DecoupledConsensusModel
namespace Protocol

open Protocol (ChainState HeightConfig)
open Protocol (SGVote)

variable {V : Type} [DecidableEq V] [Fintype V]

def state_transition (E : Env V) (cfg : HeightConfig) (σ : ChainState V)
    (B : Block V) : ChainState V :=
  let afterSlot := { σ with s := B.slot }
  let afterAttestations := B.attestations.foldl Protocol.process_attestation afterSlot
  Protocol.process_height_events E cfg { afterAttestations with L := B }

/-! ## The finality update -/

/-- `update_finality(Σ, σ)`: raise `h_max` to at least `σ.h`; then take `σ`'s justification when
    `Σ.F ⪯ σ.J` and `(σ.h_j, σ.J.root)` is greater; then take `σ.F` as finalized when it is a strict
    descendant of `Σ.F`, an ancestor of or equal to `Σ.J`, and in the viable tree. Each step reads
    the store the previous one produced. -/
def update_finality (st : Store V) (σ : ChainState V) : Store V :=
  let afterMax : Store V := { st with h_max := max st.h_max σ.h }
  let afterJustification : Store V :=
    if Block.preceq afterMax.F σ.J &&
        decide (Protocol.HeightId.mk afterMax.h_j afterMax.J.root <
          Protocol.HeightId.mk σ.h_j σ.J.root) then
      { afterMax with J := σ.J, h_j := σ.h_j }
    else afterMax
  if Block.prec afterJustification.F σ.F &&
      Block.preceq σ.F afterJustification.J &&
      decide (σ.F ∈ Protocol.viable_tree afterJustification.σ
        afterJustification.F afterJustification.h_max afterJustification.T) then
    { afterJustification with F := σ.F }
  else afterJustification

/-! ## The store handlers -/

/-- `on_goldfish_vote(Σ, vote)`: rejects a vote outside slots `Σ.s − 1` and `Σ.s`, a duplicate, or a
    vote of a validator already equivocating in its slot; otherwise appends the vote to its slot and
    stamps it. -/
def on_goldfish_vote (st : Store V) (vote : GoldfishVote V) : Store V :=
  if vote.slot < st.s - 1 ∨ st.s < vote.slot ∨ vote ∈ st.gf_votes vote.slot then
    st
  else if Protocol.equivocates (st.pool vote.slot) vote.val_index then
    st
  else
    { st with
      gf_votes := fun k =>
        if k = vote.slot then st.gf_votes k ++ [vote] else st.gf_votes k
      timestamp_vote := fun u =>
        if u = vote then some (st.t : Stamp) else st.timestamp_vote u }

/-- `on_goldfish_vote` for a vote whose validator is in its slot's committee; other votes are
    rejected. -/
def on_goldfish_vote_checked (E : Env V) (st : Store V)
    (vote : GoldfishVote V) : Store V :=
  if vote.val_index ∉ E.committee vote.slot then st else on_goldfish_vote st vote

/-- The block handler: rejects a block from a future slot, already held, with an unknown parent, not
    a descendant of `Σ.F`, with the wrong proposer, or with a slot not later than its parent's;
    otherwise stores its chain state, built by `buildState` from the parent's, adds it to the tree
    with its stamp, processes the Goldfish votes it includes, and runs `update_finality`. -/
def on_block_using (E : Env V) (st : Store V) (B : Block V)
    (buildState : ChainState V → ChainState V) : Store V :=
  if st.s < B.slot ∨ B ∈ st.T ∨ B.parent ∉ st.T then
    st
  else if !Block.preceq st.F B then
    st
  else if B.proposer? ≠ some (E.proposer B.slot) then
    st
  else if ¬ (B.parent.slot < B.slot) then
    st
  else
    let state := buildState (st.σ B.parent)
    let stored : Store V :=
      { st with
        σ := fun C => if C = B then state else st.σ C
        T := insert B st.T
        timestamp_block := fun C =>
          if C = B then some (st.t : Stamp) else st.timestamp_block C }
    let unpacked := B.gf_votes.foldl (on_goldfish_vote_checked E) stored
    update_finality unpacked (unpacked.σ B)

/-- The block handler `on_block_using` with its default chain-state builder. -/
def on_block (E : Env V) (cfg : HeightConfig) (st : Store V) (B : Block V) :
    Store V :=
  on_block_using E st B
    (fun parentState => state_transition E cfg parentState B)

/-- A block is admissible only when every carried attestation is from its slot's
round or an earlier round. -/
def carried_attestations_admissible (hc : Protocol.HealConfig) (B : Block V) : Bool :=
  B.attestations.all (fun a => decide (a.round ≤ hc.round_of B.slot))

/-- Runs `handle` on the store when `B`'s attestations are admissible; otherwise the store is
    unchanged. -/
def on_block_checked_using (handle : Store V → Store V) (hc : Protocol.HealConfig)
    (st : Store V) (B : Block V) : Store V :=
  if carried_attestations_admissible hc B then handle st else st

/-- The receiver's block handler: `on_block`, run only when `carried_attestations_admissible` holds. -/
def on_block_checked (E : Env V) (hc : Protocol.HealConfig) (cfg : HeightConfig)
    (st : Store V) (B : Block V) : Store V :=
  on_block_checked_using (fun current => on_block E cfg current B) hc st B

/-- The confirmed blocks, by root, of `a`'s validator among the stored SG votes of `a`'s round. -/
def round_votes (st : Store V) (a : CombinedAttestation V) : Finset (Option BlockId) :=
  ((st.sg_pool a.round).filter (fun b => b.val_index = a.val_index)).image
    (fun b => b.confirmed)

/-- `on_sg_vote(Σ, a)`: rejects an attestation whose round is outside
    `[round(Σ.s) − η_SG, round(Σ.s)]`, whose confirmed block its validator already voted in that
    round, or whose validator already has two distinct confirmed blocks in that round; otherwise
    appends it to its round and stamps its SG vote. -/
def on_sg_vote (hc : Protocol.HealConfig) (st : Store V)
    (a : CombinedAttestation V) : Store V :=
  if a.round < hc.round_of st.s - hc.η_SG ∨ hc.round_of st.s < a.round ∨
      a.confirmed ∈ round_votes st a ∨ (round_votes st a).card = 2 then
    st
  else
    { st with
      sg_votes := fun r =>
        if r = a.round then st.sg_votes r ++ [a] else st.sg_votes r
      timestamp_sg_vote := fun u =>
        if u = sgVote a then some (st.t : Stamp) else st.timestamp_sg_vote u }

/-- `update_confirmation(Σ, s)`: walk from the SG root over the filtered block tree with the
    Goldfish score of the slot-`s` window votes; set `live_confirmed` to the result when it passes
    the majority test and to `get_fg_root` otherwise; advance `latest_stable` to the stable root,
    and floor `latest_confirmed` on it. -/
def update_confirmation_with (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (st : Store V)
    (s : Slot) : Store V :=
  let early_votes := beforeCutoff st.tau (Protocol.support_cutoff E s) (st.pool s)
  let late_votes :=
    beforeCutoff st.timestamp_vote (Protocol.confirmation_time E s) (st.pool s)
  let support_votes :=
    early_votes.filter (fun vote =>
      Protocol.no_second_vote_in late_votes vote = true)
  let count := Protocol.voters_count E late_votes s
  let score := Protocol.goldfish_score E st.T support_votes support_votes s
  let eligible := fun B => decide (count < 2 * score B)
  let tree := Protocol.get_filtered_block_tree st.toHealing.toFG
  let root := Protocol.get_fg_root st.toHealing.toFG
  let A := Protocol.get_sg_root_with contract E hc st.toHealing (hc.round_of st.s)
  let H := Protocol.ghost A tree score eligible
  let C := if eligible H then H else root
  { st with
    live_confirmed := C
    latest_stable :=
      match contract.stableRoot E hc st.toHealing (hc.round_of st.s) with
      | some G => advance_confirmed st.latest_stable G
      | none => st.latest_stable
    latest_confirmed :=
      floor_on_stable
        (match contract.stableRoot E hc st.toHealing (hc.round_of st.s) with
          | some G => advance_confirmed st.latest_stable G
          | none => st.latest_stable)
        (match contract.confirmationSG with
          | .optional select =>
            if eligible H then advance_confirmed st.latest_confirmed H
            else
              match select E hc st.toHealing s with
              | some candidate => advance_confirmed st.latest_confirmed candidate
              | none => st.latest_confirmed)
        st.latest_confirmed }

/-! ## The duties -/

/-- The head in `tree` on the store's healing layer; only the Goldfish child domain is restricted to
    `tree`. -/
def get_head_in_tree_with (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (st : Store V)
    (tree : Finset (Block V)) (votes support_votes : Finset (GoldfishVote V))
    (k : Slot) : Block V :=
  Protocol.get_head_in_tree_with_layer contract E hc st.toHealing tree votes support_votes k

/-- The voter's filtered block tree: `get_filtered_block_tree_from` over the voter's block view
    `voter_processed_block_tree`. -/
def voter_filtered_block_tree (E : Env V) (st : Store V) (s : Slot) :
    Finset (Block V) :=
  let blocks :=
    Protocol.voter_processed_block_tree E st.toHealing.toFG.toSG.toGoldfishStore s
  Protocol.get_filtered_block_tree_from st.toHealing.toFG blocks

/-- `goldfish_vote(Σ)`: a member of the current slot's committee votes for the head of the voter's
    filtered block tree, computed from the voter's raw and support views, and processes its own
    vote. -/
def goldfish_vote_with (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V)
    (st : Store V) : Store V × Option (GoldfishVote V) :=
  let s := st.s
  let votes := Protocol.voter_view E st.toHealing.toFG.toSG.toGoldfishStore s
  let support_votes := Protocol.voter_support_view E st.toHealing.toFG.toSG.toGoldfishStore s
  let tree := voter_filtered_block_tree E st s
  let H := get_head_in_tree_with contract E hc st tree votes support_votes (s - 1)
  if nd.val_index ∈ E.committee s then
    let vote : GoldfishVote V := ⟨nd.val_index, s, H.root⟩
    (on_goldfish_vote_checked E st vote, some vote)
  else
    (st, none)

end Protocol
end DecoupledConsensusModel
end

section
/-! ## The client-facing chains -/

namespace DecoupledConsensusModel
namespace Protocol

variable {V : Type} [DecidableEq V]

/-- The stable output: `latest_stable` when it is a descendant of, or equal to, `Σ.F`; `Σ.F`
    otherwise. -/
def get_stable (st : Store V) : Block V :=
  if Block.preceq st.F st.latest_stable then st.latest_stable else st.F

/-- The confirmed output: `latest_confirmed` when it is a descendant of, or equal to, `get_stable`;
    `get_stable` otherwise. -/
def get_confirmed (st : Store V) : Block V :=
  if Block.preceq (get_stable st) st.latest_confirmed then st.latest_confirmed
  else get_stable st

end Protocol
end DecoupledConsensusModel
end

section
namespace DecoupledConsensusModel
namespace Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

inductive CarriedAdmission where
  | alsoCarried
  deriving DecidableEq

end Protocol
end DecoupledConsensusModel
end

section
/-! ## The named store -/
namespace DecoupledConsensusModel.Protocol

structure NamedStore (V : Type) where
  core : Store V
  bodies : Finset (NamedBlock V)
  sg_rows : Round → List (NamedAttestation V)

namespace NamedStore
variable {V : Type} [DecidableEq V] [Fintype V]

def initial : NamedStore V := ⟨Store.init, {NamedBlock.genesis}, fun _ => []⟩

/-- The named store with its clock set to `t` and its slot to the slot of `t`. -/
def setClock (E : Env V) (st : NamedStore V) (t : Time) : NamedStore V :=
  { st with core := { st.core with t := t, s := E.slotOf t } }

/-- The named store after the core handler produced `after`: `B` is added to the named blocks when
    the handler newly inserted `B`'s erasure into the tree. -/
def commitBlock (before : NamedStore V) (after : Store V) (B : NamedBlock V) : NamedStore V :=
  if B.erase ∉ before.core.T ∧ B.erase ∈ after.T then
    { before with core := after, bodies := insert B before.bodies }
  else { before with core := after }

/-- The named block handler core: when `B`'s named parent is held, the receiver's block handler runs
    on `B`'s erasure with the chain state built by `named_transition`, and `B` is committed. -/
def process_block_core (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) (st : NamedStore V) (B : NamedBlock V) : NamedStore V :=
  if B.parent ∉ st.bodies then st else
    let after := on_block_checked_using
      (fun current => on_block_using E current B.erase
        (fun parentState => Protocol.named_transition E cfg parentState B)) hc st.core B.erase
    commitBlock st after B

end NamedStore
end DecoupledConsensusModel.Protocol
end

section
/-! ## Admitting named attestations -/
namespace DecoupledConsensusModel.Protocol.NamedAdmission
variable {V : Type} [DecidableEq V] [Fintype V]

/-- Admits a named attestation through `on_sg_vote`; the named row is kept when its erasure newly
    enters the SG votes of its round. -/
def admit_row (hc : Protocol.HealConfig) (st : NamedStore V) (row : NamedAttestation V) :
    NamedStore V :=
  let after := on_sg_vote hc st.core row.erase
  if row.erase ∉ st.core.sg_pool row.round ∧ row.erase ∈ after.sg_pool row.round then
    { st with
      core := after
      sg_rows := fun r => if r = row.round then st.sg_rows r ++ [row] else st.sg_rows r }
  else { st with core := after }

def admit_rows (hc : Protocol.HealConfig) (st : NamedStore V)
    (rows : List (NamedAttestation V)) : NamedStore V := rows.foldl (admit_row hc) st

/-- Admits the attestations of `B` when `B` was newly added to the named blocks. -/
def admit_carried (admission : CarriedAdmission) (hc : Protocol.HealConfig)
    (before after : NamedStore V) (B : NamedBlock V) : NamedStore V :=
  if B ∉ before.bodies ∧ B ∈ after.bodies then admit_rows hc after B.attestations else after

/-- The named block handler: `process_block_core`, then the admission of the attestations of a newly
    added block. -/
def on_block_with (admission : CarriedAdmission) (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) (st : NamedStore V) (B : NamedBlock V) : NamedStore V :=
  admit_carried admission hc st (NamedStore.process_block_core E hc cfg st B) B

end DecoupledConsensusModel.Protocol.NamedAdmission
end

section
/-! ## The tick timetable -/
namespace DecoupledConsensusModel.Protocol.TickScheduler

structure TickOps (State Record BlockOut VoteOut AttOut : Type) where
  clock : State → Time → Slot → State
  slot : State → Slot
  proposal : State → State × Option BlockOut
  vote : State → State × Option VoteOut
  confirmation : State → Slot → State
  attestation : State → Record → State × Record × AttOut

/-- One tick at time `t`: set the clock; propose at the proposal time when the node is the slot's
    proposer; vote at the vote time; update the previous slot's confirmation at the support cutoff;
    and attest at the round action time when the node is awake for the round. Each duty reads the
    state the previous one produced. -/
def runWith {V State Record BlockOut VoteOut AttOut Out Result : Type}
    [DecidableEq V] [Fintype V] (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V)
    (ops : TickOps State Record BlockOut VoteOut AttOut)
    (blockOut : BlockOut → Out) (voteOut : VoteOut → Out) (attOut : AttOut → Out)
    (finish : State → Record → List Out → Result)
    (st : State) (record : Record) (t : Time) : Result :=
  let s := E.slotOf t
  let st0 := ops.clock st t s
  let st1 :=
    if 0 < s ∧ t = Protocol.proposal_time E s ∧ E.proposer s = nd.val_index then
      (ops.proposal st0).1
    else st0
  let emitted1 : List Out :=
    if 0 < s ∧ t = Protocol.proposal_time E s ∧ E.proposer s = nd.val_index then
      match (ops.proposal st0).2 with
      | none => []
      | some B => [blockOut B]
    else []
  let st2 :=
    if 0 < s ∧ t = Protocol.vote_time E s then (ops.vote st1).1
    else st1
  let emitted2 : List Out :=
    if 0 < s ∧ t = Protocol.vote_time E s then
      (ops.vote st1).2.toList.map voteOut
    else []
  let st3 :=
    if 0 < s ∧ t = Protocol.support_cutoff E s then ops.confirmation st2 (s - 1)
    else st2
  if t = hc.a E.Δ (hc.round_of (ops.slot st3)) ∧
      nd.awake (hc.round_of (ops.slot st3)) = true then
    let attested := ops.attestation st3 record
    finish attested.1 attested.2.1 (emitted1 ++ emitted2 ++ [attOut attested.2.2])
  else
    finish st3 record (emitted1 ++ emitted2)

end DecoupledConsensusModel.Protocol.TickScheduler
end

end
