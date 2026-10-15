import Model.Record.Wiring
import Model.Record.ModelSpellings
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Proofs.Vocabulary.Protocol.Handlers.FinalizationBridge
import Proofs.Vocabulary.Protocol.Duties.Inputs.ActionSources
import Proofs.Vocabulary.Protocol.Duties.Proposals.Actions
import Proofs.Vocabulary.ModelProperties.NamedDuties_update_confirmation_with
import Proofs.Vocabulary.Execution.BodyRetention
import Proofs.Vocabulary.Protocol.Store.RawSource
import Proofs.Vocabulary.Protocol.Grades.Interpolation
import Proofs.Vocabulary.Protocol.Handlers.HMaxMonotone
import Proofs.Vocabulary.Protocol.Handlers.NumericStore
import Proofs.Vocabulary.Protocol.Handlers.JustificationCarrier
import Proofs.Vocabulary.Protocol.Handlers.Proposer
import Proofs.Vocabulary.Protocol.Handlers.TickBridges
import Proofs.Vocabulary.ModelProperties.confirmationReadFrom
import Proofs.Vocabulary.Protocol.Schedule.ReceiptCallsF1
import Proofs.Vocabulary.Protocol.Handlers.HMaxCore
import Proofs.Vocabulary.Protocol.Handlers.BlockAdmission
import Proofs.Vocabulary.Protocol.Handlers.AdoptionConstructor
import Proofs.Vocabulary.Execution.ReceiptCalls
import Proofs.Vocabulary.Protocol.Handlers.JustificationBound
import Proofs.Vocabulary.Protocol.Handlers.BlockStamp
import Proofs.Vocabulary.Protocol.Handlers.HandlerAdmissionGuards
import Proofs.Vocabulary.Protocol.Schedule.HeldSkipProducers
import Proofs.Vocabulary.ModelProperties.NamedReceiptCalls_postCore
import Proofs.Vocabulary.Execution.OutageActionInputs
import Proofs.Vocabulary.ModelProperties.with_attestation_input
import Proofs.Vocabulary.Protocol.ValidatorClient.RecordFresh
import Proofs.Vocabulary.Protocol.ValidatorClient.RecordTargetHistory
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.Agreement
import Proofs.Vocabulary.Protocol.Handlers.SGArrival
import Proofs.Vocabulary.Protocol.Handlers.RawRelay
import Proofs.Vocabulary.Execution.HealthyLocalFacts
import Proofs.Vocabulary.Protocol.Handlers.Admission
import Model.Conditions.Vocabulary_Protocol_Handlers_Pool
import Proofs.Vocabulary.Protocol.Handlers.StoreBridge
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedStore_initial
import Proofs.Vocabulary.Protocol.Handlers.Pool
import Proofs.Claims.Spec2Claims.Claim13bModel_opening
import Proofs.Claims.ProcessedFlip
import Proofs.Vocabulary.Protocol.Grades.Main
import Proofs.Vocabulary.Protocol.Schedule.AdoptionTransport
import Proofs.Vocabulary.Protocol.Handlers.GoldfishVotePool
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.GradeBootstrapCore
import Proofs.Vocabulary.Execution.FinalizedViable
import Proofs.Vocabulary.Protocol.Handlers.Blocks
import Proofs.Claims.Spec2Claims.Claim13beRoute3_5
import Proofs.Claims.Spec2Claims.Claim13beRoute3_4
import Proofs.Vocabulary.Protocol.Handlers.SGArrivalStampCarrier

/-!
# The facts structures of the handlers family

`HandlersFacts` holds the facts about single routines of the handlers family that the proofs over a
model `M : Model V` call, and `HandlersRunFacts` holds the facts of the same family that mention an
execution or a run.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

open DecoupledConsensusModel.Execution
open Protocol (ChainState HeightConfig)
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.BlockProcessingDefaults
open Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution
open Protocol (derive_named)
open Protocol (Record)
open Protocol (HealConfig)
open DecoupledConsensusModel.Proofs.ModelProperties
open DecoupledConsensusModel.Proofs.NamedAdmission
open Protocol.NamedAdmission
open DecoupledConsensusModel.Proofs.NamedFinalityMonotone
open Execution Protocol
open DecoupledConsensusModel.Proofs.NamedStore
open Protocol.NamedStore
open BlockProcessingDefaults
open Internal Execution
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Statements.Instantiation
open Internal.NamedRecoveryRead
open Protocol (ChainState)
open Protocol (Record HeightId)
open DecoupledConsensusModel.Protocol
open Protocol (HeightConfig)
open scoped DC

/-- The facts about the handlers routines of the model `M` that the proofs over it call. -/
structure HandlersFacts (M : Model V) : Prop where
  /-- Admitting the rows `rows` into a coherent named store keeps its clock and the receipt stamps
      of its rows at or before `bound`. -/
  sgArrival_rows_data : ∀ (S : Setup V) (bound : Time) (st : M.NS) (rows : List (NamedAttestation V)),
    Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg st →
    (st.core.t ≤ bound ∧ ∀ k (a : NamedAttestation V), a ∈ st.sg_rows k →
      a.round = k ∧ ∃ stamp : Time, stamp ≤ bound ∧
        st.core.timestamp_sg_vote (M.sgVote a.erase) = some (stamp : Stamp)) →
    ((M.admit_rows S.hc st rows).core.t ≤ bound ∧
      ∀ k (a : NamedAttestation V), a ∈ (M.admit_rows S.hc st rows).sg_rows k →
        a.round = k ∧ ∃ stamp : Time, stamp ≤ bound ∧
          (M.admit_rows S.hc st rows).core.timestamp_sg_vote (M.sgVote a.erase) = some (stamp : Stamp))
  /-- Admitting the rows `rows` into a coherent named store returns a coherent named store. -/
  NamedAdmission_coherent_admit_rows : ∀ (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (st : M.NS)
    (rows : List (NamedAttestation V)),
    Restated.Vocabulary.Proofs.NamedStore.Coherent M E cfg st →
    Restated.Vocabulary.Proofs.NamedStore.Coherent M E cfg (M.admit_rows hc st rows)
  /-- The confirmation update at slot `s` writes to `live_confirmed` either the block the
      confirmation walk ends at or the FG root of `st`, for every outcome of the walk and of the
      update. -/
  update_confirmation_with_live_confirmed_walk_or_fgRoot : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (st : M.S) (s : Slot)
    (tm : TimestampMap (GoldfishVote V)) (htm : st.tau ⇢ tm)
    (R : Block V) (hR : M.get_sg_root_with contract E hc st.toHealing (M.round_of hc st.s) ⇢ R)
    (score : Block V → ℕ)
    (hscore : ∀ B, M.goldfish_score E st.T
      ((_root_.DecoupledConsensusModel.beforeCutoff tm (M.support_cutoff E s) (st.pool s)).filter (fun u => M.no_second_vote_in (_root_.DecoupledConsensusModel.beforeCutoff st.timestamp_vote (M.confirmation_time E s) (st.pool s)) u = true))
      ((_root_.DecoupledConsensusModel.beforeCutoff tm (M.support_cutoff E s) (st.pool s)).filter (fun u => M.no_second_vote_in (_root_.DecoupledConsensusModel.beforeCutoff st.timestamp_vote (M.confirmation_time E s) (st.pool s)) u = true))
      s B ⇢ score B)
    (W : Block V) (hW : M.ghost R (M.get_filtered_block_tree st.toHealing.toFG) score
      (fun B => decide (M.voters_count E (_root_.DecoupledConsensusModel.beforeCutoff st.timestamp_vote (M.confirmation_time E s) (st.pool s)) s < 2 * score B)) ⇢ W)
    (st' : M.S) (hst' : M.update_confirmation_with contract E hc st s ⇢ st'),
    st'.live_confirmed = W ∨ st'.live_confirmed = M.get_fg_root (M.toHealing st).toFG
  /-- Every block of the initial core tree is of a slot at or before the slot of the initial core
      store. -/
  treeSlotBounded_init : ∀ B : Block V, B ∈ (M.ns_initial : M.NS).core.T → B.slot ≤ (M.ns_initial : M.NS).core.s
  /-- In the initial core store, every block of the tree has a block stamp, every block stamp is of
      a block of the tree, and no block stamp is later than the clock. -/
  blockStamps_init : ((∀ B : Block V, B ∈ (M.ns_initial : M.NS).core.T → ((M.ns_initial : M.NS).core.timestamp_block B).isSome = true) ∧
      (∀ B : Block V, ((M.ns_initial : M.NS).core.timestamp_block B).isSome = true → B ∈ (M.ns_initial : M.NS).core.T) ∧
      (∀ (B : Block V) (c : Stamp), (M.ns_initial : M.NS).core.timestamp_block B = some c →
        c ≤ ((M.ns_initial : M.NS).core.t : Stamp)))
  /-- If `B` is in the tree of `st` with chain state `σ`, `st.F` is an ancestor of `B` or `B`
      itself, and `st.F` is in the tree with a descendant whose chain-state height is at least
      `st.h_max - 1`, then the same holds of `M.update_finality st σ`. -/
  finalizedViable_update_finality : ∀ (st : M.S) (σ : M.CS) {B : Block V}, B ∈ st.T → st.σ B = σ →
    Block.preceq st.F B = true →
    (st.F ∈ st.T ∧ ∃ W ∈ st.T, Block.Preceq st.F W ∧ st.h_max - 1 ≤ (st.σ W).h) →
    ((M.update_finality st σ).F ∈ (M.update_finality st σ).T ∧
      ∃ W ∈ (M.update_finality st σ).T, Block.Preceq (M.update_finality st σ).F W ∧
        (M.update_finality st σ).h_max - 1 ≤ ((M.update_finality st σ).σ W).h)
  /-- When the block handler newly keeps a block `B` that includes a Goldfish vote `u` of a
      committee member for slot `st.s - 1` or `st.s`, and `st.t < Γ`, the returned store pools `u`
      in its slot stamped before `Γ`, or `u`'s validator equivocates among that pool's votes stamped
      before `Γ`. -/
  block_carried_before_deadline_or_equivocates : ∀ (S : Setup V) (st : M.NS)
    (B : NamedBlock V) (u : GoldfishVote V) (Γ : Time),
    Restated.Vocabulary.Protocol.PoolStamps M st.core → B ∉ st.bodies →
    B ∈ (M.on_block_with .alsoCarried S.E S.hc S.cfg st B).bodies →
    u ∈ B.erase.gf_votes → u.val_index ∈ S.E.committee u.slot →
    ¬ u.slot < st.core.s - 1 → ¬ st.core.s < u.slot → st.core.t < Γ →
    u ∈ _root_.DecoupledConsensusModel.beforeCutoff
        (M.on_block_with .alsoCarried S.E S.hc S.cfg st B).core.timestamp_vote Γ
        (M.store_pool (M.on_block_with .alsoCarried S.E S.hc S.cfg st B).core u.slot) ∨
      M.equivocates
        (_root_.DecoupledConsensusModel.beforeCutoff
          (M.on_block_with .alsoCarried S.E S.hc S.cfg st B).core.timestamp_vote Γ
          (M.store_pool (M.on_block_with .alsoCarried S.E S.hc S.cfg st B).core u.slot))
        u.val_index = true
  /-- If `st` satisfies `PoolStamps`, the vote `u` is for slot `st.s - 1` or `st.s`, and `st.t < Γ`,
      then after `M.on_goldfish_vote st u` the vote `u` is in its slot's pool stamped before `Γ`, or
      `u`'s validator equivocates among that pool's votes stamped before `Γ`. -/
  on_goldfish_vote_beforeCutoff_or_equivocates : ∀ (st : M.S) (u : GoldfishVote V) (Γ : Time),
    Restated.Vocabulary.Protocol.PoolStamps M st →
    ¬ u.slot < st.s - 1 → ¬ st.s < u.slot → st.t < Γ →
    u ∈ _root_.DecoupledConsensusModel.beforeCutoff (M.on_goldfish_vote st u).timestamp_vote Γ
        (M.store_pool (M.on_goldfish_vote st u) u.slot) ∨
      M.equivocates
        (_root_.DecoupledConsensusModel.beforeCutoff (M.on_goldfish_vote st u).timestamp_vote Γ
          (M.store_pool (M.on_goldfish_vote st u) u.slot)) u.val_index = true
  /-- For every outcome of the confirmation update at slot `s`, either `live_confirmed` is a block
      and the confirmation walk's block passes the test that the count of late voters is less than
      twice its score, or `live_confirmed` is the FG root of `st`. -/
  update_confirmation_with_live_confirmed_genuine_or_fgRoot : ∀ (contract : M.Contract) (E : Env V)
    (hc : Protocol.HealConfig) (st : M.S) (s : Slot)
    (tm : TimestampMap (GoldfishVote V)) (htm : st.tau ⇢ tm)
    (R : Block V) (hR : M.get_sg_root_with contract E hc st.toHealing (M.round_of hc st.s) ⇢ R)
    (score : Block V → ℕ)
    (hscore : ∀ B, M.goldfish_score E st.T
      ((_root_.DecoupledConsensusModel.beforeCutoff tm (M.support_cutoff E s) (st.pool s)).filter (fun u => M.no_second_vote_in (_root_.DecoupledConsensusModel.beforeCutoff st.timestamp_vote (M.confirmation_time E s) (st.pool s)) u = true))
      ((_root_.DecoupledConsensusModel.beforeCutoff tm (M.support_cutoff E s) (st.pool s)).filter (fun u => M.no_second_vote_in (_root_.DecoupledConsensusModel.beforeCutoff st.timestamp_vote (M.confirmation_time E s) (st.pool s)) u = true))
      s B ⇢ score B)
    (W : Block V) (hW : M.ghost R (M.get_filtered_block_tree st.toHealing.toFG) score
      (fun B => decide (M.voters_count E (_root_.DecoupledConsensusModel.beforeCutoff st.timestamp_vote (M.confirmation_time E s) (st.pool s)) s < 2 * score B)) ⇢ W)
    (st' : M.S) (hst' : M.update_confirmation_with contract E hc st s ⇢ st'),
    (∃ C : Block V, st'.live_confirmed = C ∧
        decide (M.voters_count E (_root_.DecoupledConsensusModel.beforeCutoff st.timestamp_vote (M.confirmation_time E s) (st.pool s)) s < 2 * score W) = true) ∨
      st'.live_confirmed = M.get_fg_root (M.toHealing st).toFG
  /-- The core store of the initial named store satisfies `PoolStamps`. -/
  poolStamps_initial : Restated.Vocabulary.Protocol.PoolStamps M (M.ns_initial : M.NS).core
  /-- The core store of `M.ns_with_core st c` is `c`. -/
  ns_with_core_core : ∀ (st : M.NS) (c : M.S), (M.ns_with_core st c).core = c
  /-- A row that the block handler newly admits is of a round at most the round of the store's slot. -/
  rawRelay_block_new_round_floor : ∀ (S : Setup V) (st : M.NS) (B : NamedBlock V) (a : NamedAttestation V),
    a ∉ st.sg_rows a.round →
    a ∈ (M.on_block_with .alsoCarried S.E S.hc S.cfg st B).sg_rows a.round →
    a.round ≤ M.round_of S.hc st.core.s
  /-- A row that `M.admit_row` newly admits is of a round at most the round of the store's slot. -/
  rawRelay_new_row_round_floor : ∀ (hc : Protocol.HealConfig) (st : M.NS) (incoming a : NamedAttestation V),
    a ∉ st.sg_rows a.round → a ∈ (M.admit_row hc st incoming).sg_rows a.round →
    a.round ≤ M.round_of hc st.core.s
  /-- Replacing the core store of `ns` by the checked Goldfish-vote handler's result on it keeps the
      named attestation rows of `ns`. -/
  ns_with_core_sg_rows : ∀ (E : Env V) (ns : M.NS) (u : GoldfishVote V) (st : M.S)
    (hafter : M.on_goldfish_vote_checked E ns.core u = st),
    (M.ns_with_core ns st).sg_rows = ns.sg_rows
  /-- A body newly admitted by the block handler has a slot at most the store's slot, names its
      slot's proposer, has a parent of an earlier slot, and includes only attestations that pass the
      admission test. -/
  new_body_guards : ∀ (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig)
    (st : M.NS) (B : NamedBlock V), B ∉ st.bodies →
    B ∈ (M.on_block_with .alsoCarried E hc cfg st B).bodies →
    B.erase.slot ≤ st.core.s ∧ B.erase.proposer? = some (E.proposer B.erase.slot) ∧
      B.erase.parent.slot < B.erase.slot ∧ M.carried_attestations_admissible hc B.erase = true
  /-- Replacing the core store of `st` by the checked Goldfish-vote handler's result on it keeps the
      bodies of `st`. -/
  ns_with_core_bodies : ∀ (E : Env V) (st : M.NS) (u : GoldfishVote V) (c : M.S)
    (hafter : M.on_goldfish_vote_checked E st.core u = c),
    (M.ns_with_core st c).bodies = st.bodies
  /-- Setting the clock of a named store to `t` keeps the confirmation-membership invariant. -/
  invariant_clock : ∀ (E : Env V) (cfg : Protocol.HeightConfig) (st : M.NS) (t : Time)
    (h : Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant M E cfg st),
    Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant M E cfg (M.ns_setClock E st t)
  /-- Some block of the initial core tree has a chain state whose justification and justification
      height are the initial core store's own. -/
  initial_core_justifier : ∃ D ∈ (M.ns_initial : M.NS).core.T,
    ((M.ns_initial : M.NS).core.σ D).J = (M.ns_initial : M.NS).core.J ∧
    ((M.ns_initial : M.NS).core.σ D).h_j = (M.ns_initial : M.NS).core.h_j
  /-- A row newly admitted by `M.admit_row` was not in its round's attestation set of the core store
      and is in that set after `M.on_sg_vote`. -/
  full_new_core_guard : ∀ (hc : Protocol.HealConfig) (st : M.NS) (a : NamedAttestation V)
    (hpre : a ∉ st.sg_rows a.round) (hpost : a ∈ (M.admit_row hc st a).sg_rows a.round),
    a.erase ∉ M.store_sg_pool st.core a.round ∧
      a.erase ∈ M.store_sg_pool (M.on_sg_vote hc st.core a.erase) a.round
  /-- The checked Goldfish-vote handler keeps the chain-state map `σ` and the fields `F`, `J` and
      `h_j` of the store. -/
  coreEq_on_goldfish_vote_checked : ∀ (E : Env V) (st : M.S) (u : GoldfishVote V),
    (M.on_goldfish_vote_checked E st u).σ = st.σ ∧ (M.on_goldfish_vote_checked E st u).F = st.F ∧
      (M.on_goldfish_vote_checked E st u).J = st.J ∧ (M.on_goldfish_vote_checked E st u).h_j = st.h_j
  /-- If `M.on_sg_vote` newly adds the erasure of `row` to its round's attestation set, then `row`
      is among the named rows of its round after `M.admit_row hc st row`. -/
  NamedAdmission_admitted_original_row : ∀ (hc : Protocol.HealConfig) (st : M.NS) (row : NamedAttestation V)
    (hpre : row.erase ∉ M.store_sg_pool st.core row.round)
    (hpost : row.erase ∈ M.store_sg_pool (M.on_sg_vote hc st.core row.erase) row.round),
    row ∈ (M.admit_row hc st row).sg_rows row.round
  /-- A tick keeps every Goldfish vote of the core store's slot-`k` list signed by a member of
      `S.E.committee k`. -/
  committeePools_on_tick_emit : ∀ (S : Setup V) (v : V) (before : M.N) (t : Time) (out : M.N × List (NamedObject V)), M.tick S v before t ⇢ out → (∀ (k : Slot) (u : GoldfishVote V), u ∈ before.st.core.gf_votes k → u.val_index ∈ S.E.committee k) → ∀ (k : Slot) (u : GoldfishVote V), u ∈ out.1.st.core.gf_votes k → u.val_index ∈ S.E.committee k
  /-- A Goldfish vote in a slot list after the checked Goldfish-vote handler was already in that
      list, or is the vote `u` it was handed. -/
  mem_gf_votes_on_goldfish_vote_checked : ∀ (E : Env V) (st : M.S) (u : GoldfishVote V) (k : Slot)
    {y : GoldfishVote V} (h : y ∈ (M.on_goldfish_vote_checked E st u).gf_votes k),
    y ∈ st.gf_votes k ∨ y = u
  /-- A Goldfish vote in a slot list after the named block core was already in that list, or is
      included in `B` and `B.erase` newly entered the tree. -/
  process_block_core_gf_votes_upper : ∀ (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig)
    (st : M.NS) (B : NamedBlock V) (k : Slot) (y : GoldfishVote V),
    y ∈ (M.ns_process_block_core E hc cfg st B).core.gf_votes k →
      y ∈ st.core.gf_votes k ∨
        (y ∈ B.gf_votes ∧ B.erase ∉ st.core.T ∧
          B.erase ∈ (M.ns_process_block_core E hc cfg st B).core.T)
  /-- If `b` is already in its round's attestation set, `M.on_sg_vote` keeps the stamp of `b`'s SG
      vote. -/
  on_sg_vote_existing_row_stamp : ∀ (hc : Protocol.HealConfig) (st : M.S) (incoming b : CombinedAttestation V)
    (hb : b ∈ M.store_sg_pool st b.round),
    (M.on_sg_vote hc st incoming).timestamp_sg_vote (M.sgVote b) = st.timestamp_sg_vote (M.sgVote b)
  /-- If the honest validators `Hon` support `B` in the slot-`s` confirmation votes, the late votes
      are a valid vote set, and for every outcome `R` of the SG root `B` is a descendant of `R` with
      every block strictly between them in the filtered block tree, then every outcome of the
      confirmation update at slot `s` confirms `B`. -/
  live_confirmed_eq_with : ∀ (contract : M.Contract) (E : Env V) (hc : HealConfig) (st : M.S) (s : Slot) (Hon : Finset V) (B : Block V) (tm : TimestampMap (GoldfishVote V)) (htm : st.tau ⇢ tm) (hsup : _root_.DecoupledConsensusModel.Protocol.HonestSupport E st.T ((_root_.DecoupledConsensusModel.beforeCutoff tm (M.support_cutoff E s) (st.pool s)).filter (fun u => M.no_second_vote_in (_root_.DecoupledConsensusModel.beforeCutoff st.timestamp_vote (M.confirmation_time E s) (st.pool s)) u = true)) s Hon B) (hvalid : _root_.DecoupledConsensusModel.Protocol.VoteSetValid E s (_root_.DecoupledConsensusModel.beforeCutoff st.timestamp_vote (M.confirmation_time E s) (st.pool s))) (R : Block V) (hR : M.get_sg_root_with contract E hc st.toHealing (M.round_of hc st.s) ⇢ R) (hpre : Block.Preceq R B) (hpath : ∀ C : Block V, Block.Preceq R C → C ≠ R → Block.Preceq C B → C ∈ M.get_filtered_block_tree st.toHealing.toFG) (st' : M.S) (hst' : M.update_confirmation_with contract E hc st s ⇢ st'), st'.live_confirmed = B
  /-- Setting the clock of a named store keeps the SG-vote lists of its core store. -/
  setClock_core_sg_votes : ∀ (E : Env V) (st : M.NS) (t : Int), (M.ns_setClock E st t).core.sg_votes = st.core.sg_votes
  /-- The checked Goldfish-vote handler keeps every vote and stamp of the store, and keeps the four
      pool conditions: every vote in a bucket is for its slot, every pooled vote is stamped, every
      stamped vote is pooled in its slot's bucket, and no stamp is later than `st.t`. -/
  poolStep_on_goldfish_vote_checked : ∀ (E : Env V) (st : M.S) (u : GoldfishVote V),
    ((∀ (k : Slot) (x : GoldfishVote V), x ∈ st.gf_votes k → x.slot = k) ∧
      (∀ (k : Slot) (x : GoldfishVote V), x ∈ st.gf_votes k → (st.timestamp_vote x).isSome = true) ∧
      (∀ x : GoldfishVote V, (st.timestamp_vote x).isSome = true → x ∈ st.gf_votes x.slot) ∧
      (∀ (x : GoldfishVote V) (c : Stamp), st.timestamp_vote x = some c → c ≤ (st.t : Stamp))) →
    ((∀ (k : Slot) (x : GoldfishVote V), x ∈ st.gf_votes k → x ∈ (M.on_goldfish_vote_checked E st u).gf_votes k) ∧
      (∀ (x : GoldfishVote V) (c : Stamp), st.timestamp_vote x = some c →
        (M.on_goldfish_vote_checked E st u).timestamp_vote x = some c)) ∧
    ((∀ (k : Slot) (x : GoldfishVote V), x ∈ (M.on_goldfish_vote_checked E st u).gf_votes k → x.slot = k) ∧
      (∀ (k : Slot) (x : GoldfishVote V), x ∈ (M.on_goldfish_vote_checked E st u).gf_votes k →
        ((M.on_goldfish_vote_checked E st u).timestamp_vote x).isSome = true) ∧
      (∀ x : GoldfishVote V, ((M.on_goldfish_vote_checked E st u).timestamp_vote x).isSome = true →
        x ∈ (M.on_goldfish_vote_checked E st u).gf_votes x.slot) ∧
      (∀ (x : GoldfishVote V) (c : Stamp), (M.on_goldfish_vote_checked E st u).timestamp_vote x = some c →
        c ≤ ((M.on_goldfish_vote_checked E st u).t : Stamp)))
  /-- If `st` satisfies the four pool conditions, `u` is for slot `st.s - 1` or `st.s`, and `u`'s
      validator does not equivocate in `st.pool u.slot`, then after `M.on_goldfish_vote st u` the
      vote `u` is in its slot's bucket with a stamp no later than `st.t`. -/
  mem_and_stamp_of_process : ∀ (st : M.S) (u : GoldfishVote V),
    (∀ (k : Slot) (x : GoldfishVote V), x ∈ st.gf_votes k → x.slot = k) →
    (∀ (k : Slot) (x : GoldfishVote V), x ∈ st.gf_votes k → (st.timestamp_vote x).isSome = true) →
    (∀ x : GoldfishVote V, (st.timestamp_vote x).isSome = true → x ∈ st.gf_votes x.slot) →
    (∀ (x : GoldfishVote V) (c : Stamp), st.timestamp_vote x = some c → c ≤ (st.t : Stamp)) →
    ¬ u.slot < st.s - 1 → ¬ st.s < u.slot → M.equivocates (st.pool u.slot) u.val_index = false →
    u ∈ (M.on_goldfish_vote st u).gf_votes u.slot ∧
      ∃ c : Stamp, (M.on_goldfish_vote st u).timestamp_vote u = some c ∧ c ≤ (st.t : Stamp)
  /-- `M.on_sg_vote` keeps every attestation of every round's attestation set. -/
  sg_pool_subset_on_sg_vote : ∀ (hc : Protocol.HealConfig) (st : M.S) (a : CombinedAttestation V) (r : Round),
    M.store_sg_pool st r ⊆ M.store_sg_pool (M.on_sg_vote hc st a) r
  /-- If `after` is already a store part, the core of `M.commitBlock before after B` is `after`. -/
  commitBlock_core : ∀ (before : M.NS) (after : M.S) (B : NamedBlock V)
    (hafter : (M.ns_with_core before after).core = after),
    (M.commitBlock before after B).core = after
  /-- The checked block handler, run on a named store's core with the chain states built by
      `M.named_transition`, returns a store part. -/
  on_block_checked_using_store_part : ∀ (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) (before : M.NS) (B : NamedBlock V),
    (M.ns_with_core before
        (M.on_block_checked_using
          (fun current => M.on_block_using E current B.erase
            (fun ps => M.named_transition E cfg ps B)) hc before.core B.erase)).core =
      M.on_block_checked_using
        (fun current => M.on_block_using E current B.erase
          (fun ps => M.named_transition E cfg ps B)) hc before.core B.erase
  /-- The core store of the initial named store is `M.store_init`. -/
  initial_core : (M.ns_initial : M.NS).core = M.store_init
  /-- The core store of the initial named store maps every block to the initial chain state
      `M.cs_initial`. -/
  initial_core_σ : (M.ns_initial : M.NS).core.σ = fun _ => M.cs_initial
  /-- A named block after `M.commitBlock before after B` was among the named blocks of `before`, or
      is `B` and `B.erase` was newly inserted into the tree. -/
  mem_commitBlock_bodies : ∀ (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig)
    {before : M.NS} {after : M.S} {B D : NamedBlock V}
    (hafter : (M.ns_process_block_core E hc cfg before B).core = after)
    (hheld : B ∈ (M.commitBlock before after B).bodies → B.erase ∈ before.core.T →
      B ∈ before.bodies),
    D ∈ (M.commitBlock before after B).bodies →
      (B.erase ∉ before.core.T ∧ B.erase ∈ after.T) ∧ D = B ∨ D ∈ before.bodies
  /-- If the named block core newly inserts `B.erase` into the tree, then `B` is among the named
      blocks of `M.commitBlock before after B`. -/
  mem_commitBlock_bodies_of_fresh : ∀ (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) {before : M.NS} {after : M.S} {B : NamedBlock V}
    (hafter : (M.ns_process_block_core E hc cfg before B).core = after),
    B.erase ∉ before.core.T ∧ B.erase ∈ after.T → B ∈ (M.commitBlock before after B).bodies
  /-- If `B`'s named parent is held, the named block core's result has the same core store as the
      commit of the checked block handler's result. -/
  process_block_core_of_parent_mem : ∀ (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) {st : M.NS} {B : NamedBlock V}, B.parent ∈ st.bodies →
    ∀ (hn : M.reachedStore st := by trivial),
    M.sameCore (M.ns_process_block_core E hc cfg st B).core
      (M.commitBlock st
        (M.on_block_checked_using
          (fun current => M.on_block_using E current B.erase
            (fun ps => M.named_transition E cfg ps B)) hc st.core B.erase) B).core
  /-- If `B`'s named parent is held, the named blocks of the named block core's result are those of
      the commit of that result's own core store. -/
  process_block_core_bodies_eq_commit : ∀ (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) {st : M.NS} {B : NamedBlock V}, B.parent ∈ st.bodies →
    (M.ns_process_block_core E hc cfg st B).bodies =
      (M.commitBlock st (M.ns_process_block_core E hc cfg st B).core B).bodies
  /-- When the store's finalized block is a strict ancestor of `σ.F`, `σ.F` is an ancestor of the
      justified block the justification step leaves, and `σ.F` is in the viable tree,
      `M.update_finality st σ` finalizes `σ.F`. -/
  update_finality_F_of_conditions : ∀ (st : M.S) (σ : M.CS) (hσ : M.chainStateInTree st σ),
    Block.prec st.F σ.F = true →
    Block.preceq σ.F
      (if Block.preceq st.F σ.J && decide (Protocol.HeightId.mk st.h_j st.J.root <
          Protocol.HeightId.mk σ.h_j σ.J.root) then σ.J else st.J) = true →
    σ.F ∈ M.viable_tree st.σ st.F (max st.h_max σ.h) st.T →
    (M.update_finality st σ).F = σ.F
  /-- When the block handler builds the chain state of `B.erase` from its parent's by
      `M.named_transition`, that chain state names blocks of the resulting store `unpacked`. -/
  chainStateInTree_of_derived : ∀ (E : Env V) (cfg : Protocol.HeightConfig) (st : M.NS) (B : NamedBlock V)
      (unpacked : M.S),
    (∀ D ∈ st.bodies, st.core.σ D.erase = M.derive_named E cfg D) →
    st.core.T = st.bodies.image NamedBlock.erase → B.parent ∈ st.bodies →
    (∀ σ, M.chainStateInTree st.core σ → M.chainStateInTree unpacked σ) →
    unpacked.σ B.erase = M.named_transition E cfg (st.core.σ B.erase.parent) B →
    ∀ (hn : M.reachedStore st := by trivial),
    M.chainStateInTree unpacked (unpacked.σ B.erase)
  /-- If `after` is already a store part, the core of `M.commitBlock before after B` is `after`. -/
  commit_core : ∀ (before : M.NS) (after : M.S) (B : NamedBlock V)
    (hafter : (M.ns_with_core before after).core = after),
    (M.commitBlock before after B).core = after
  /-- If `after` is the core store of the named block core's result, `M.commitBlock before after B`
      keeps the named attestation rows of `before`. -/
  commit_rows : ∀ (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig)
    (before : M.NS) (after : M.S) (B : NamedBlock V)
    (hafter : (M.ns_process_block_core E hc cfg before B).core = after),
    (M.commitBlock before after B).sg_rows = before.sg_rows
  /-- If `after` is the core store of the named block core's result, `M.commitBlock before after B`
      keeps every named block of `before`. -/
  mem_commitBlock_bodies_of_mem : ∀ (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) {before : M.NS} {after : M.S} {B D : NamedBlock V}
    (hafter : (M.ns_process_block_core E hc cfg before B).core = after),
    D ∈ before.bodies → D ∈ (M.commitBlock before after B).bodies
  /-- If every attestation `B` includes is admissible, the checked block handler returns
      `handle st`. -/
  on_block_checked_using_eq_handle : ∀ (handle : M.S → M.S) (hc : Protocol.HealConfig)
    (st : M.S) {B : Block V}, M.carried_attestations_admissible hc B = true →
    M.on_block_checked_using handle hc st B = handle st
  /-- When the named block core newly holds `B`, the named block handler returns the receipt of the
      attestations `B` includes on that core's result. -/
  on_block_with_of_new : ∀ (admission : Protocol.CarriedAdmission) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (st : M.NS) (B : NamedBlock V),
    B ∉ st.bodies → B ∈ (M.ns_process_block_core E hc cfg st B).bodies →
    M.on_block_with admission E hc cfg st B =
      M.admit_rows hc (M.ns_process_block_core E hc cfg st B) B.attestations
  /-- Unless the named block core newly holds `B`, the named block handler returns the core's
      result. -/
  on_block_with_of_not_new : ∀ (admission : Protocol.CarriedAdmission) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (st : M.NS) (B : NamedBlock V),
    ¬ (B ∉ st.bodies ∧ B ∈ (M.ns_process_block_core E hc cfg st B).bodies) →
    M.on_block_with admission E hc cfg st B = M.ns_process_block_core E hc cfg st B
  /-- When the admission test rejects the attestation `a` (stale, ahead of the store's round, its
      confirmed block already recorded for its signer and round, or two already recorded),
      `M.on_sg_vote` returns the store unchanged. -/
  on_sg_vote_of_rejected : ∀ (hc : Protocol.HealConfig) (st : M.S) (a : CombinedAttestation V),
    a.round < M.round_of hc st.s - hc.η_SG ∨ M.round_of hc st.s < a.round ∨
      a.confirmed ∈ M.round_votes st a ∨ (M.round_votes st a).card = 2 →
    M.on_sg_vote hc st a = st
  /-- If an outcome of the contract's stable root for the store's round is a block `G` that is an
      ancestor of `latest_stable`, every outcome of the confirmation update keeps `latest_stable`
      and writes a `latest_confirmed` that is a descendant of it. -/
  update_confirmation_with_keeps_stable_of_root_preceq : ∀ (contract : M.Contract) (E : Env V)
    (hc : Protocol.HealConfig) (st : M.S) (s : Slot) {G : Block V},
    ∀ x : Option (Block V), contract.stableRoot E hc st.toHealing (M.round_of hc st.s) ⇢ x →
    x = some G →
    Block.Preceq G st.latest_stable →
    ∀ st' : M.S, M.update_confirmation_with contract E hc st s ⇢ st' →
    st'.latest_stable = st.latest_stable ∧
      Block.Preceq st.latest_stable st'.latest_confirmed
  /-- If an outcome of the contract's stable root for the store's round is a block `G`, every
      outcome of the confirmation update has `latest_stable` equal to `M.advance_confirmed` of the
      old `latest_stable` with `G`. -/
  update_confirmation_with_latest_stable_of_root : ∀ (contract : M.Contract) (E : Env V)
    (hc : Protocol.HealConfig) (st : M.S) (s : Slot) {G : Block V},
    ∀ x : Option (Block V), contract.stableRoot E hc st.toHealing (M.round_of hc st.s) ⇢ x →
    x = some G →
    ∀ st' : M.S, M.update_confirmation_with contract E hc st s ⇢ st' →
    st'.latest_stable =
      M.advance_confirmed st.latest_stable G
  /-- The core of `M.admit_row hc st a` is, up to `M.sameCore`, the store `M.on_sg_vote` returns on
      the core of `st` and the erasure of `a`. -/
  Execution_admit_row_core : ∀ (hc : Protocol.HealConfig) (st : M.NS) (a : NamedAttestation V),
    M.sameCore (M.admit_row hc st a).core (M.on_sg_vote hc st.core a.erase)
  /-- The checked Goldfish-vote handler keeps the store's time `t`. -/
  on_goldfish_vote_checked_time : ∀ (E : Env V) (st : M.S) (u : GoldfishVote V), (M.on_goldfish_vote_checked E st u).t = st.t
  /-- `M.on_sg_vote` keeps the store's time `t`. -/
  on_sg_vote_time : ∀ (hc : Protocol.HealConfig) (st : M.S) (a : CombinedAttestation V), (M.on_sg_vote hc st a).t = st.t
  /-- `M.update_finality` keeps the store's time `t`. -/
  update_finality_time : ∀ (st : M.S) (σ : M.CS), (M.update_finality st σ).t = st.t
  /-- The checked block handler returns the store unchanged on a block already in its tree. -/
  checked_existing : ∀ (E : Env V) (hc : Protocol.HealConfig) (st : M.S) (B : Block V) (buildState : M.CS → M.CS) (hB : B ∈ st.T), M.on_block_checked_using
    (fun current => M.on_block_using E current B buildState) hc st B = st
  /-- The named blocks after `M.on_block_with` are those after the named block core
      `M.ns_process_block_core`. -/
  on_block_with_bodies_eq : ∀ (S : Setup V) (admission : Protocol.CarriedAdmission) (st : M.NS) (B : NamedBlock V), (M.on_block_with admission S.E S.hc S.cfg st B).bodies =
    (M.ns_process_block_core S.E S.hc S.cfg st B).bodies
  /-- The `h_max` of `M.update_finality st sigma` is the larger of `st.h_max` and the height of
      `sigma`. -/
  update_finality_h_max_eq : ∀ (st : M.S) (sigma : M.CS), (M.update_finality st sigma).h_max = max st.h_max sigma.h
  /-- For a block `B` newly held in `after`, the carried-row admission returns
      `M.admit_rows hc after B.attestations`. -/
  admit_carried_of_new : ∀ (admission : Protocol.CarriedAdmission) (hc : Protocol.HealConfig) {before after : M.NS} {B : NamedBlock V} (hnew : B ∉ before.bodies) (hheld : B ∈ after.bodies), M.admit_carried admission hc before after B =
    M.admit_rows hc after B.attestations
  /-- `M.carried_attestations_admissible hc B` holds exactly when every attestation `B` includes is
      of a round at most the round of `B`'s slot. -/
  carried_attestations_admissible_eq_true_iff : ∀ (hc : Protocol.HealConfig) (B : Block V), M.carried_attestations_admissible hc B = true ↔
    ∀ a ∈ B.attestations, a.round ≤ (M.round_of hc B.slot)
  /-- The initial named store holds the genesis body alone. -/
  initial_bodies : (M.ns_initial : M.NS).bodies = {NamedBlock.genesis}
  /-- The initial core store's finalized block is genesis. -/
  initial_core_F : (M.ns_initial : M.NS).core.F = Block.genesis
  /-- The initial core store's justified block is genesis. -/
  initial_core_J : (M.ns_initial : M.NS).core.J = Block.genesis
  /-- The initial core store's block tree is genesis alone. -/
  initial_core_T : (M.ns_initial : M.NS).core.T = {Block.genesis}
  /-- The initial core store's justified height `h_j` is `0`. -/
  initial_core_h_j : (M.ns_initial : M.NS).core.h_j = 0
  /-- In the initial core store, `h_j < h_max`. -/
  initial_core_h_j_lt_h_max : (M.ns_initial : M.NS).core.h_j <
    (M.ns_initial : M.NS).core.h_max
  /-- The initial core store's `h_max` is `1`. -/
  initial_core_h_max : (M.ns_initial : M.NS).core.h_max = 1
  /-- The initial core store holds no Goldfish vote in `M.store_pool` at any slot. -/
  initial_core_not_mem_pool : ∀ (k : Slot) (u : GoldfishVote V), u ∉ (M.store_pool (M.ns_initial : M.NS).core k)
  /-- The initial core store holds no attestation in `M.store_sg_pool` at any round. -/
  initial_core_not_mem_sg_pool : ∀ (r : Round) (a : CombinedAttestation V), a ∉ (M.store_sg_pool (M.ns_initial : M.NS).core r)
  /-- The initial core store's slot is `0`. -/
  initial_core_s : (M.ns_initial : M.NS).core.s = 0
  /-- The initial core store's time is `0`. -/
  initial_core_t : (M.ns_initial : M.NS).core.t = 0
  /-- In the initial core store, every block's chain-state height is at most `h_max`. -/
  initial_core_σ_h_le_h_max : ∀ (B : Block V), ((M.ns_initial : M.NS).core.σ B).h ≤
    (M.ns_initial : M.NS).core.h_max
  /-- The initial named store holds no SG row at any round. -/
  initial_sg_rows : ∀ (r : Round), (M.ns_initial : M.NS).sg_rows r = []
  /-- If the attestations `B` includes are admissible, the checked block handler returns
      `handle st`. -/
  on_block_checked_using_of_admissible : ∀ (handle : M.S → M.S) (hc : Protocol.HealConfig) (st : M.S) {B : Block V} (h : M.carried_attestations_admissible hc B = true), M.on_block_checked_using handle hc st B = handle st
  /-- If the attestations `B` includes are not admissible, the checked block handler returns `st`. -/
  on_block_checked_using_of_not_admissible : ∀ (handle : M.S → M.S) (hc : Protocol.HealConfig) (st : M.S) {B : Block V} (h : ¬ M.carried_attestations_admissible hc B = true), M.on_block_checked_using handle hc st B = st
  /-- The block-processing body returns the store unchanged when it rejects `B`: `B`'s slot is later
      than the store's, `B` is already in the tree, `B`'s parent is not, `st.F` is not an ancestor
      of `B`, `B`'s proposer is not its slot's proposer, or `B`'s parent's slot is not earlier than
      `B`'s. -/
  on_block_using_of_rejected : ∀ (E : Env V) (st : M.S) (B : Block V) (buildState : M.CS → M.CS) (h : (st.s < B.slot ∨ B ∈ st.T ∨ B.parent ∉ st.T) ∨ (!Block.preceq st.F B) = true ∨
    B.proposer? ≠ some (E.proposer B.slot) ∨ ¬ (B.parent.slot < B.slot)), M.on_block_using E st B buildState = st
  /-- The finalized block after `M.on_block_with` is the one after the named block core
      `M.ns_process_block_core`. -/
  on_block_with_core_F : ∀ (admission : Protocol.CarriedAdmission) (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (st : M.NS) (B : NamedBlock V), (M.on_block_with admission E hc cfg st B).core.F =
    (M.ns_process_block_core E hc cfg st B).core.F
  /-- If `u`'s validator is in the committee of `u`'s slot, the checked Goldfish-vote handler
      returns `M.on_goldfish_vote st u`. -/
  on_goldfish_vote_checked_of_mem_committee : ∀ (E : Env V) (st : M.S) (u : GoldfishVote V) (h : u.val_index ∈ E.committee u.slot), M.on_goldfish_vote_checked E st u = M.on_goldfish_vote st u
  /-- If `B`'s named parent is not among the bodies of `st`, the named block core returns `st`. -/
  process_block_core_of_parent_not_mem : ∀ (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) {st : M.NS} {B : NamedBlock V} (h : B.parent ∉ st.bodies), M.ns_process_block_core E hc cfg st B = st
  /-- Setting the clock of a named store keeps its bodies. -/
  ModelProperties_setClock_bodies : ∀ (E : Env V) (st : M.NS) (t : Time), (M.ns_setClock E st t).bodies = st.bodies
  /-- Setting the clock of a named store keeps the block tree of its core store. -/
  ModelProperties_setClock_core_T : ∀ (E : Env V) (st : M.NS) (t : Time), (M.ns_setClock E st t).core.T = st.core.T
  /-- Setting the clock of a named store keeps the Goldfish votes `M.store_pool` of its core store. -/
  ModelProperties_setClock_core_pool : ∀ (E : Env V) (st : M.NS) (t : Time), (M.store_pool (M.ns_setClock E st t).core) = (M.store_pool st.core)
  /-- Setting the clock of a named store to `t` sets its core store's slot to `E.slotOf t`. -/
  ModelProperties_setClock_core_s : ∀ (E : Env V) (st : M.NS) (t : Time), (M.ns_setClock E st t).core.s = E.slotOf t
  /-- Setting the clock of a named store to `t` sets its core store's time to `t`. -/
  ModelProperties_setClock_core_t : ∀ (E : Env V) (st : M.NS) (t : Time), (M.ns_setClock E st t).core.t = t
  /-- Setting the clock of a named store keeps the chain-state map of its core store. -/
  ModelProperties_setClock_core_σ : ∀ (E : Env V) (st : M.NS) (t : Time), (M.ns_setClock E st t).core.σ = st.core.σ
  /-- Every outcome of the voter's filtered block tree is a subset of the store's block tree. -/
  ModelProperties_voter_filtered_block_tree_subset : ∀ (E : Env V) (st : M.S) (s : Slot) (X : Finset (Block V)), M.voter_filtered_block_tree E st s ⇢ X → X ⊆ st.T
  /-- `M.admit_row` keeps the named blocks. -/
  NamedAdmission_admit_row_bodies : ∀ (hc : Protocol.HealConfig) (st : M.NS) (row : NamedAttestation V), (M.admit_row hc st row).bodies = st.bodies
  /-- The core of `M.admit_row hc st row` is, up to `M.sameCore`, the store `M.on_sg_vote` returns
      on the core of `st` and the erasure of `row`. -/
  NamedAdmission_admit_row_core : ∀ (hc : Protocol.HealConfig) (st : M.NS) (row : NamedAttestation V),
    M.sameCore (M.admit_row hc st row).core (M.on_sg_vote hc st.core row.erase)
  /-- If `M.on_sg_vote` leaves the core of `st` unchanged on the erasure of `row`, then
      `M.admit_row hc st row` is `st`. -/
  admit_row_of_core_noop : ∀ (hc : Protocol.HealConfig) (st : M.NS) (row : NamedAttestation V) (h : M.on_sg_vote hc st.core row.erase = st.core), M.admit_row hc st row = st
  /-- The core of `M.admit_rows hc st rows` is, up to `M.sameCore`, the fold of `M.on_sg_vote hc`
      over the erasures of `rows`, in order, from the core of `st`. -/
  admit_rows_core : ∀ (hc : Protocol.HealConfig) (st : M.NS) (rows : List (NamedAttestation V)),
    M.sameCore (M.admit_rows hc st rows).core
      ((rows.map NamedAttestation.erase).foldl (M.on_sg_vote hc) st.core)
  /-- Stores related by `M.sameCore` have the same time. -/
  sameCore_t : ∀ {a b : M.S}, M.sameCore a b → a.t = b.t
  /-- Stores related by `M.sameCore` have the same current slot. -/
  sameCore_s : ∀ {a b : M.S}, M.sameCore a b → a.s = b.s
  /-- Stores related by `M.sameCore` have the same block tree. -/
  sameCore_T : ∀ {a b : M.S}, M.sameCore a b → a.T = b.T
  /-- Stores related by `M.sameCore` have the same block receipt stamps. -/
  sameCore_timestamp_block : ∀ {a b : M.S}, M.sameCore a b → a.timestamp_block = b.timestamp_block
  /-- Stores related by `M.sameCore` have the same Goldfish-vote receipt stamps. -/
  sameCore_timestamp_vote : ∀ {a b : M.S}, M.sameCore a b → a.timestamp_vote = b.timestamp_vote
  /-- Stores related by `M.sameCore` have the same SG-vote receipt stamps. -/
  sameCore_timestamp_sg_vote : ∀ {a b : M.S}, M.sameCore a b → a.timestamp_sg_vote = b.timestamp_sg_vote
  /-- Stores related by `M.sameCore` have the same Goldfish votes. -/
  sameCore_gf_votes : ∀ {a b : M.S}, M.sameCore a b → a.gf_votes = b.gf_votes
  /-- Stores related by `M.sameCore` have the same finalized block. -/
  sameCore_F : ∀ {a b : M.S}, M.sameCore a b → a.F = b.F
  /-- Stores related by `M.sameCore` have the same attestation sets `M.store_sg_pool`. -/
  sameCore_store_sg_pool : ∀ {a b : M.S}, M.sameCore a b → M.store_sg_pool a = M.store_sg_pool b
  /-- If `B` is newly held and its attestations are `earlierRows ++ row :: suffix`, the carried-row
      admission from `after` admits `earlierRows`, then `row`, then `suffix`. -/
  carried_row_prefix : ∀ (hc : Protocol.HealConfig) (before after : M.NS) (B : NamedBlock V) (earlierRows suffix : List (NamedAttestation V)) (row : NamedAttestation V) (hrows : B.attestations = earlierRows ++ row :: suffix) (hnew : B ∉ before.bodies) (hheld : B ∈ after.bodies), M.admit_carried .alsoCarried hc before after B =
    M.admit_rows hc (M.admit_row hc (M.admit_rows hc after earlierRows) row) suffix
  /-- The named block handler keeps the core store's time and slot. -/
  on_block_clock : ∀ (admission : Protocol.CarriedAdmission) (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (st : M.NS) (B : NamedBlock V), (M.on_block_with admission E hc cfg st B).core.t = st.core.t ∧
    (M.on_block_with admission E hc cfg st B).core.s = st.core.s
  /-- The named block core keeps the core store's time and slot. -/
  process_block_clock : ∀ (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (st : M.NS) (B : NamedBlock V), (M.ns_process_block_core E hc cfg st B).core.t = st.core.t ∧
    (M.ns_process_block_core E hc cfg st B).core.s = st.core.s
  /-- The finalized block before the named block core is an ancestor of the finalized block after
      it, or that block itself. -/
  process_block_core_F : ∀ (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (st : M.NS) (B : NamedBlock V), Block.Preceq st.core.F
    (M.ns_process_block_core E hc cfg st B).core.F
  /-- The block-processing body either returns `st`, or adds `B` to the tree with the chain state
      `build` applied to its parent's, keeping `F`, `J`, `h_j` and `h_max`, and then returns
      `M.update_finality` of that store at `B`'s chain state. -/
  raw_eq_or_accepted : ∀ (E : Env V) (st : M.S) (B : Block V) (build : M.CS → M.CS), M.on_block_using E st B build = st ∨
    ∃ u : M.S,
    u.T = insert B st.T ∧ u.F = st.F ∧ u.J = st.J ∧ u.h_j = st.h_j ∧
    u.h_max = st.h_max ∧
    u.σ = (fun C => if C = B then build (st.σ B.parent) else st.σ C) ∧
    (∀ σ, M.chainStateInTree st σ → M.chainStateInTree u σ) ∧
    B ∉ st.T ∧ Block.preceq st.F B = true ∧
    M.on_block_using E st B build = M.update_finality u (u.σ B)
  /-- A named attestation among its round's rows after `M.admit_row` admits `incoming` was already
      among them, or is `incoming`. -/
  admit_row_mem_cases : ∀ (hc : Protocol.HealConfig) (st : M.NS) (incoming a : NamedAttestation V) (h : a ∈ (M.admit_row hc st incoming).sg_rows a.round), a ∈ st.sg_rows a.round ∨ a = incoming
  /-- `M.admit_row` keeps every named attestation among its round's rows. -/
  admit_row_mem_mono : ∀ (hc : Protocol.HealConfig) (st : M.NS) (incoming a : NamedAttestation V) (h : a ∈ st.sg_rows a.round), a ∈ (M.admit_row hc st incoming).sg_rows a.round
  /-- `M.admit_rows` keeps every named attestation among its round's rows. -/
  admit_rows_mem_mono : ∀ (hc : Protocol.HealConfig) (st : M.NS) (rows : List (NamedAttestation V)) (a : NamedAttestation V) (h : a ∈ st.sg_rows a.round), a ∈ (M.admit_rows hc st rows).sg_rows a.round
  /-- A named attestation newly among its round's rows after `M.admit_rows` is admitted at some
      position `j` of `rows`: it is absent after the first `j` entries and present once it is
      admitted next. -/
  admit_rows_new_marker : ∀ (hc : Protocol.HealConfig) (st : M.NS) (rows : List (NamedAttestation V)) (a : NamedAttestation V) (hpre : a ∉ st.sg_rows a.round) (hpost : a ∈ (M.admit_rows hc st rows).sg_rows a.round), ∃ j, j < rows.length ∧ rows[j]? = some a ∧
    a ∉ (M.admit_rows hc st (rows.take j)).sg_rows a.round ∧
    a ∈ (M.admit_row hc
    (M.admit_rows hc st (rows.take j)) a).sg_rows a.round
  /-- The finalized block `st.F` is an ancestor of `M.get_stable st`, or that block itself. -/
  finalized_preceq_get_stable : ∀ (st : M.S), Block.Preceq st.F (M.get_stable st)
  /-- A vote cast by an outcome of the Goldfish vote duty is signed by the node's validator and is
      of the store's slot. -/
  goldfish_vote_with_snd : ∀ (contract : M.Contract) (E : Env V) (hc : HealConfig) (nd : Protocol.Node V) (st : M.S) {u : GoldfishVote V} (out : M.S × Option (GoldfishVote V)) (hout : M.goldfish_vote_with contract E hc nd st ⇢ out) (h : out.2 = some u), u.val_index = nd.val_index ∧ u.slot = st.s
  /-- The checked Goldfish-vote handler keeps the store's slot `s`. -/
  on_goldfish_vote_checked_slot : ∀ (E : Env V) (st : M.S) (u : GoldfishVote V), (M.on_goldfish_vote_checked E st u).s = st.s
  /-- `M.on_sg_vote` keeps the store's slot `s`. -/
  on_sg_vote_slot : ∀ (hc : HealConfig) (st : M.S) (a : CombinedAttestation V), (M.on_sg_vote hc st a).s = st.s
  /-- The named block core keeps the SG votes of every round of the core store. -/
  process_block_core_sg_votes : ∀ (E : Env V) (hc : HealConfig) (cfg : HeightConfig) (st : M.NS) (B : NamedBlock V), (M.ns_process_block_core E hc cfg st B).core.sg_votes =
    st.core.sg_votes
  /-- The checked Goldfish-vote handler keeps the finalized block `F`. -/
  on_goldfish_vote_checked_F : ∀ (E : Env V) (st : M.S) (vote : GoldfishVote V), (M.on_goldfish_vote_checked E st vote).F = st.F
  /-- The checked Goldfish-vote handler keeps the block tree `T`. -/
  on_goldfish_vote_checked_T : ∀ (E : Env V) (st : M.S) (vote : GoldfishVote V), (M.on_goldfish_vote_checked E st vote).T = st.T
  /-- The checked Goldfish-vote handler keeps `h_max`. -/
  on_goldfish_vote_checked_h_max : ∀ (E : Env V) (st : M.S) (vote : GoldfishVote V), (M.on_goldfish_vote_checked E st vote).h_max = st.h_max
  /-- `M.on_sg_vote` keeps the finalized block `F`. -/
  on_sg_vote_F : ∀ (hc : HealConfig) (st : M.S) (a : CombinedAttestation V), (M.on_sg_vote hc st a).F = st.F
  /-- `M.on_sg_vote` keeps the block tree `T`. -/
  on_sg_vote_T : ∀ (hc : HealConfig) (st : M.S) (a : CombinedAttestation V), (M.on_sg_vote hc st a).T = st.T
  /-- `M.on_sg_vote` keeps `h_max`. -/
  on_sg_vote_h_max : ∀ (hc : HealConfig) (st : M.S) (a : CombinedAttestation V), (M.on_sg_vote hc st a).h_max = st.h_max
  /-- `st.F` is an ancestor of the finalized block of `M.update_finality st σ`, or that block
      itself. -/
  update_finality_F : ∀ (st : M.S) (σ : M.CS), Block.preceq st.F (M.update_finality st σ).F = true
  /-- `M.update_finality` keeps the block tree `T`. -/
  update_finality_T : ∀ (st : M.S) (σ : M.CS), (M.update_finality st σ).T = st.T
  /-- `M.update_finality` never lowers `h_max`. -/
  update_finality_h_max_mono : ∀ (st : M.S) (sigma : M.CS), st.h_max ≤ (M.update_finality st sigma).h_max
  /-- `M.update_finality` never lowers the pair of the justified height and the justified block's
      root, in the order of `HeightId`. -/
  update_finality_heightId : ∀ (st : M.S) (σ : M.CS), HeightId.mk st.h_j st.J.root ≤
    HeightId.mk (M.update_finality st σ).h_j
    (M.update_finality st σ).J.root
  /-- `M.update_finality` keeps the finalized block an ancestor of the justified block, or that
      block itself. -/
  update_finality_preceq : ∀ (st : M.S) (σ : M.CS) (h : Block.preceq st.F st.J = true), Block.preceq (M.update_finality st σ).F
    (M.update_finality st σ).J = true
  /-- `M.update_finality` keeps the chain-state map `σ`. -/
  update_finality_σ : ∀ (st : M.S) (σ : M.CS), (M.update_finality st σ).σ = st.σ
  /-- `M.admit_row` keeps the named blocks. -/
  Protocol_admit_row_bodies : ∀ (hc : HealConfig) (st : M.NS) (a : NamedAttestation V), (M.admit_row hc st a).bodies = st.bodies
  /-- `M.admit_row` keeps the block tree of the core store. -/
  admit_row_core_T : ∀ (hc : HealConfig) (st : M.NS) (a : NamedAttestation V), (M.admit_row hc st a).core.T = st.core.T
  /-- `M.admit_rows` keeps the named blocks and the block tree of the core store. -/
  admit_rows_bodies_and_core_T : ∀ (hc : HealConfig), ∀ (rows : List (NamedAttestation V)) (st : M.NS),
    (M.admit_rows hc st rows).bodies = st.bodies ∧
    (M.admit_rows hc st rows).core.T = st.core.T
  /-- Every outcome of the Goldfish vote duty keeps the block tree, whatever the grade contract. -/
  goldfish_vote_with_T : ∀ (contract : M.Contract) (E : Env V) (hc : HealConfig) (nd : Protocol.Node V) (st : M.S) (out : M.S × Option (GoldfishVote V)), M.goldfish_vote_with contract E hc nd st ⇢ out → out.1.T = st.T
  /-- The finalized block before the named block handler is an ancestor of the finalized block after
      it, or that block itself. -/
  on_block_with_F : ∀ (admission : Protocol.CarriedAdmission) (E : Env V) (hc : HealConfig) (cfg : HeightConfig) (st : M.NS) (B : NamedBlock V), Block.Preceq st.core.F
    (M.on_block_with admission E hc cfg st B).core.F
  /-- A named block newly present after `M.on_block_with` on the block `B'` is `B'`, and its erasure
      is in the resulting core tree. -/
  on_block_with_new_body : ∀ (adm : Protocol.CarriedAdmission) (S : Setup V) (before : M.NS) (B' C : NamedBlock V) (hpre : C ∉ before.bodies) (hpost : C ∈ (M.on_block_with adm S.E S.hc S.cfg before B').bodies), C = B' ∧
    C.erase ∈ (M.on_block_with adm S.E S.hc S.cfg before B').core.T
  /-- The checked Goldfish-vote handler keeps the block receipt stamps. -/
  on_goldfish_vote_checked_timestamp_block : ∀ (E : Env V) (st : M.S) (u : GoldfishVote V), (M.on_goldfish_vote_checked E st u).timestamp_block =
    st.timestamp_block
  /-- `M.on_sg_vote` keeps the Goldfish votes. -/
  on_sg_vote_gf_votes : ∀ (hc : HealConfig) (st : M.S) (a : CombinedAttestation V), (M.on_sg_vote hc st a).gf_votes = st.gf_votes
  /-- `M.on_sg_vote` keeps the block receipt stamps. -/
  on_sg_vote_timestamp_block : ∀ (hc : HealConfig) (st : M.S) (a : CombinedAttestation V), (M.on_sg_vote hc st a).timestamp_block = st.timestamp_block
  /-- `M.on_sg_vote` keeps the Goldfish-vote receipt stamps. -/
  on_sg_vote_timestamp_vote : ∀ (hc : HealConfig) (st : M.S) (a : CombinedAttestation V), (M.on_sg_vote hc st a).timestamp_vote = st.timestamp_vote
  /-- `M.update_finality` keeps the Goldfish votes. -/
  update_finality_gf_votes : ∀ (st : M.S) (σ : M.CS), (M.update_finality st σ).gf_votes = st.gf_votes
  /-- `M.update_finality` keeps the block receipt stamps. -/
  update_finality_timestamp_block : ∀ (st : M.S) (σ : M.CS), (M.update_finality st σ).timestamp_block = st.timestamp_block
  /-- `M.update_finality` keeps the Goldfish-vote receipt stamps. -/
  update_finality_timestamp_vote : ∀ (st : M.S) (σ : M.CS), (M.update_finality st σ).timestamp_vote = st.timestamp_vote
  /-- `M.advance_confirmed old c` is `old`, or a block that is not an ancestor of `old`. -/
  advance_confirmed_eq_or_not_preceq : ∀ (old c : Block V), M.advance_confirmed old c = old ∨
    ¬ Block.Preceq (M.advance_confirmed old c) old
  /-- `M.advance_confirmed old c` is `old` with `c` an ancestor of `old` or `old` itself, or it is
      `c`. -/
  advance_confirmed_values : ∀ (old c : Block V), (Block.Preceq c old ∧ M.advance_confirmed old c = old) ∨
    M.advance_confirmed old c = c
  /-- `M.floor_on_stable stable cand old` is `cand`, or `old`, or a block that is not an ancestor of
      `old`. -/
  floor_on_stable_cases : ∀ (stable cand old : Block V), M.floor_on_stable stable cand old = cand ∨
    M.floor_on_stable stable cand old = old ∨
    ¬ Block.Preceq (M.floor_on_stable stable cand old) old
  /-- `stable` is an ancestor of `M.floor_on_stable stable candidate old`, or that block itself. -/
  floor_on_stable_stable_preceq : ∀ (stable candidate old : Block V), Block.Preceq stable (M.floor_on_stable stable candidate old)
  /-- `M.floor_on_stable stable cand old` is `cand` with `stable ⪯ cand`, or `old` with
      `stable ⪯ old`, or `stable`. -/
  floor_on_stable_values : ∀ (stable cand old : Block V), (Block.Preceq stable cand ∧ M.floor_on_stable stable cand old = cand) ∨
    (Block.Preceq stable old ∧ M.floor_on_stable stable cand old = old) ∨
    M.floor_on_stable stable cand old = stable
  /-- `M.get_confirmed st` is `st.latest_confirmed` or `M.get_stable st`. -/
  get_confirmed_eq_or : ∀ (st : M.S), M.get_confirmed st = st.latest_confirmed ∨
    M.get_confirmed st = M.get_stable st
  /-- If the old store's `F`, `latest_stable` and `latest_confirmed` are ancestors of the new
      store's, the new `F` and `latest_stable` lie on one chain, and the new `M.get_stable` and
      `latest_confirmed` lie on one chain, then the old `M.get_confirmed` is an ancestor of the new
      one. -/
  get_confirmed_preceq_of_fields : ∀ (old new : M.S) (hF : Block.Preceq old.F new.F) (hL : Block.Preceq old.latest_stable new.latest_stable) (hC : Block.Preceq old.latest_confirmed new.latest_confirmed) (hFL : Block.compatible new.F new.latest_stable = true) (hSC : Block.compatible (M.get_stable new) new.latest_confirmed = true), Block.Preceq (M.get_confirmed old) (M.get_confirmed new)
  /-- If `M.get_stable st` and `st.latest_confirmed` lie on one chain, both are ancestors of
      `M.get_confirmed st`. -/
  get_confirmed_upper : ∀ (st : M.S) (h : Block.compatible (M.get_stable st) st.latest_confirmed = true), Block.Preceq (M.get_stable st) (M.get_confirmed st) ∧
    Block.Preceq st.latest_confirmed (M.get_confirmed st)
  /-- Either `M.get_stable st` is an ancestor of `st.latest_confirmed` and `M.get_confirmed st` is
      `st.latest_confirmed`, or `M.get_confirmed st` is `M.get_stable st`. -/
  get_confirmed_values : ∀ (st : M.S), (Block.Preceq (M.get_stable st) st.latest_confirmed ∧
    M.get_confirmed st = st.latest_confirmed) ∨
    M.get_confirmed st = M.get_stable st
  /-- For every outcome `R` of the SG root of the store's round, the head `M.get_head_in_tree_with`
      computes over `tree` can return `X` exactly when the Goldfish fork choice started from `R`
      through `tree` can. -/
  get_head_in_tree_with_eq_fork_choice : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (st : M.S) (tree : Finset (Block V)) (votes support : Finset (GoldfishVote V)) (s : Slot)
    (R : Block V), M.get_sg_root_with contract E hc (M.toHealing st) (M.round_of hc st.s) ⇢ R →
    ∀ X : Block V, M.get_head_in_tree_with contract E hc st tree votes support s ⇢ X ↔
    M.goldfish_fork_choice E (M.toHealing st).toFG.σ (M.toHealing st).toFG.h_max st.T st.s
    R tree
    votes support s ⇢ X
  /-- `M.get_head_in_tree_with` at the store `st` can return `X` exactly when
      `M.get_head_in_tree_with_layer` with the same arguments at `st`'s healing view can. -/
  get_head_in_tree_with_eq_layer : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (st : M.S) (tree : Finset (Block V)) (votes support : Finset (GoldfishVote V)) (k : Slot)
    (X : Block V), M.get_head_in_tree_with contract E hc st tree votes support k ⇢ X ↔
    M.get_head_in_tree_with_layer contract E hc (M.toHealing st) tree votes support k ⇢ X
  /-- Every outcome of the SG root of the store's round is an ancestor of every outcome of the head
      `M.get_head_in_tree_with` computes at the store, or that head itself. -/
  get_sg_root_with_preceq_get_head_in_tree_with_store : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (st : M.S) (tree : Finset (Block V)) (votes support : Finset (GoldfishVote V)) (s : Slot)
    (R : Block V), M.get_sg_root_with contract E hc (M.toHealing st) (M.round_of hc st.s) ⇢ R →
    ∀ H : Block V, M.get_head_in_tree_with contract E hc st tree votes support s ⇢ H →
    Block.Preceq R H
  /-- `M.get_stable st` is `st.latest_stable` or `st.F`. -/
  get_stable_eq_or : ∀ (st : M.S), M.get_stable st = st.latest_stable ∨ M.get_stable st = st.F
  /-- If the old store's `F` and `latest_stable` are ancestors of the new store's, and the new `F`
      and `latest_stable` lie on one chain, then the old `M.get_stable` is an ancestor of the new
      one. -/
  get_stable_preceq_of_fields : ∀ (old new : M.S) (hF : Block.Preceq old.F new.F) (hL : Block.Preceq old.latest_stable new.latest_stable) (hFL : Block.compatible new.F new.latest_stable = true), Block.Preceq (M.get_stable old) (M.get_stable new)
  /-- If `st.F` and `st.latest_stable` lie on one chain, both are ancestors of `M.get_stable st`. -/
  get_stable_upper : ∀ (st : M.S) (h : Block.compatible st.F st.latest_stable = true), Block.Preceq st.F (M.get_stable st) ∧
    Block.Preceq st.latest_stable (M.get_stable st)
  /-- The block-processing body adds `B` to the tree when `B`'s slot is at most the store's, `B` is
      new, its parent is held, `st.F` is an ancestor of `B`, `B` names its slot's proposer, its
      parent is of an earlier slot, and `M.rootFresh st B` holds. -/
  mem_T_on_block_using : ∀ (E : Env V) (st : M.S) (B : Block V) (build : M.CS → M.CS) (hslot : B.slot ≤ st.s) (hnew : B ∉ st.T) (hpar : B.parent ∈ st.T) (hfin : Block.preceq st.F B = true) (hprop : B.proposer? = some (E.proposer B.slot)) (hpslot : B.parent.slot < B.slot)
    -- no block of `st`'s tree has `B`'s root unless it is `B`
    (hroot : M.rootFresh st B),
    B ∈ (M.on_block_using E st B build).T
  /-- The named block handler keeps every named block the named block core holds. -/
  mem_on_block_with_bodies_of_mem_core : ∀ (admission : Protocol.CarriedAdmission) (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (st : M.NS) (B : NamedBlock V) {D : NamedBlock V} (hD : D ∈ (M.ns_process_block_core E hc cfg st B).bodies), D ∈ (M.on_block_with admission E hc cfg st B).bodies
  /-- When the admission test does not reject the attestation `a`, `M.on_sg_vote` adds `a` to its
      round's attestation set. -/
  mem_on_sg_vote_sg_pool_of_not : ∀ (hc : Protocol.HealConfig) (st : M.S) (a : CombinedAttestation V) (h : ¬ (a.round < (M.round_of hc st.s) - hc.η_SG ∨ (M.round_of hc st.s) < a.round ∨
    a.confirmed ∈ M.round_votes st a ∨ (M.round_votes st a).card = 2)), a ∈ (M.store_sg_pool (M.on_sg_vote hc st a) a.round)
  /-- `o` is in `M.round_votes st a` exactly when some attestation of `a`'s round in
      `M.store_sg_pool` is signed by `a`'s validator and confirms `o`. -/
  mem_round_votes_iff : ∀ (st : M.S) (a : CombinedAttestation V) (o : Option BlockId), o ∈ M.round_votes st a ↔
    ∃ b ∈ (M.store_sg_pool st a.round), b.val_index = a.val_index ∧ b.confirmed = o
  /-- A block `C` of an outcome of the voter's processed tree is in every outcome of the voter's
      filtered tree when `st.F` is an ancestor of `C`, `C` is an ancestor of a block of that tree
      whose chain-state height is at least `st.h_max − 1`, and the FG root is an ancestor of `C`. -/
  mem_voter_filtered_block_tree_of_parts : ∀ (E : Env V) (st : M.S) (s : Slot) {C Y : Block V} (P : Finset (Block V)) (hP : M.voter_processed_block_tree E (M.toHealing st).toFG.toSG.toGoldfishStore s ⇢ P) (hC : C ∈ P) (hF : Block.Preceq st.F C) (hY : Y ∈ P) (hCY : Block.Preceq C Y) (hh : st.h_max - 1 ≤ (st.σ Y).h) (hroot : Block.Preceq (M.get_fg_root (M.toHealing st).toFG) C) (X : Finset (Block V)) (hX : M.voter_filtered_block_tree E st s ⇢ X), C ∈ X
  /-- The initial core store's `h_max` is `1`. -/
  namedStore_initial_h_max : (M.ns_initial : M.NS).core.h_max = 1
  /-- The checked Goldfish-vote handler returns the store unchanged on a vote already in its slot's
      list. -/
  on_goldfish_vote_checked_of_mem : ∀ (E : Env V) (st : M.S) (u : GoldfishVote V) (h : u ∈ st.gf_votes u.slot), M.on_goldfish_vote_checked E st u = st
  /-- When the admission test does not reject the attestation `a`, `M.on_sg_vote` stamps `a`'s SG
      vote with the store's time `st.t`. -/
  on_sg_vote_timestamp_of_admitted : ∀ (hc : Protocol.HealConfig) (st : M.S) (a : CombinedAttestation V) (h : ¬ (a.round < (M.round_of hc st.s) - hc.η_SG ∨ (M.round_of hc st.s) < a.round ∨
    a.confirmed ∈ M.round_votes st a ∨ (M.round_votes st a).card = 2)), (M.on_sg_vote hc st a).timestamp_sg_vote (M.sgVote a) =
    some (st.t : Stamp)
  /-- `c` is an ancestor of `M.advance_confirmed old c`, or that block itself. -/
  preceq_advance_confirmed_candidate : ∀ (old c : Block V), Block.Preceq c (M.advance_confirmed old c)
  /-- If `stable` and `cand` lie on one chain and `X` is an ancestor of `cand`, then `X` is an
      ancestor of `M.floor_on_stable stable cand old`. -/
  preceq_floor_on_stable_of_compatible : ∀ {X stable cand : Block V} (old : Block V) (hc : Block.compatible stable cand = true) (hX : Block.Preceq X cand), Block.Preceq X (M.floor_on_stable stable cand old)
  /-- If `P` is an ancestor of `st.latest_stable` or that block itself, and `P` and `st.F` lie on
      one chain, then `P` is an ancestor of `M.get_stable st` or that block itself. -/
  preceq_get_stable_of_record : ∀ (st : M.S) {P : Block V} (hL : Block.Preceq P st.latest_stable) (hF : Block.Compatible P st.F), Block.Preceq P (M.get_stable st)
  /-- The named block core keeps the named attestation rows. -/
  process_block_core_sg_rows_eq : ∀ (S : Setup V) (st : M.NS) (B : NamedBlock V), (M.ns_process_block_core S.E S.hc S.cfg st B).sg_rows = st.sg_rows
  /-- Setting the clock of a named store keeps its bodies. -/
  Sts_setClock_bodies : ∀ (E : Env V) (st : M.NS) (t : Int), (M.ns_setClock E st t).bodies = st.bodies
  /-- Setting the clock of a named store keeps its core store's finalized block. -/
  setClock_core_F : ∀ (E : Env V) (st : M.NS) (t : Int), (M.ns_setClock E st t).core.F = st.core.F
  /-- Setting the clock of a named store keeps its core store's justified block. -/
  setClock_core_J : ∀ (E : Env V) (st : M.NS) (t : Int), (M.ns_setClock E st t).core.J = st.core.J
  /-- Setting the clock of a named store keeps its core store's block tree. -/
  Sts_setClock_core_T : ∀ (E : Env V) (st : M.NS) (t : Int), (M.ns_setClock E st t).core.T = st.core.T
  /-- Setting the clock of a named store keeps its core store's Goldfish votes of every slot. -/
  setClock_core_gf_votes : ∀ (E : Env V) (st : M.NS) (t : Int) (s : Slot), (M.ns_setClock E st t).core.gf_votes s = st.core.gf_votes s
  /-- Setting the clock of a named store keeps its core store's `h_max`. -/
  setClock_core_h_max : ∀ (E : Env V) (st : M.NS) (t : Int), (M.ns_setClock E st t).core.h_max = st.core.h_max
  /-- Setting the clock of a named store keeps its core store's `latest_confirmed`. -/
  setClock_core_latest_confirmed : ∀ (E : Env V) (st : M.NS) (t : Int), (M.ns_setClock E st t).core.latest_confirmed = st.core.latest_confirmed
  /-- Setting the clock of a named store keeps its core store's `latest_stable`. -/
  setClock_core_latest_stable : ∀ (E : Env V) (st : M.NS) (t : Int), (M.ns_setClock E st t).core.latest_stable = st.core.latest_stable
  /-- Setting the clock of a named store keeps its core store's Goldfish votes `M.store_pool` of
      every slot. -/
  Sts_setClock_core_pool : ∀ (E : Env V) (st : M.NS) (t : Int) (s : Slot), (M.store_pool (M.ns_setClock E st t).core s) = (M.store_pool st.core s)
  /-- Setting the clock of a named store to `t` sets its core store's slot to `E.slotOf t`. -/
  Sts_setClock_core_s : ∀ (E : Env V) (st : M.NS) (t : Int), (M.ns_setClock E st t).core.s = E.slotOf t
  /-- Setting the clock of a named store to `t` sets its core store's time to `t`. -/
  Sts_setClock_core_t : ∀ (E : Env V) (st : M.NS) (t : Int), (M.ns_setClock E st t).core.t = t
  /-- Setting the clock of a named store keeps its core store's block receipt stamps. -/
  setClock_core_timestamp_block : ∀ (E : Env V) (st : M.NS) (t : Int), (M.ns_setClock E st t).core.timestamp_block = st.core.timestamp_block
  /-- Setting the clock of a named store keeps its core store's Goldfish-vote receipt stamps. -/
  setClock_core_timestamp_vote : ∀ (E : Env V) (st : M.NS) (t : Int), (M.ns_setClock E st t).core.timestamp_vote = st.core.timestamp_vote
  /-- Setting the clock of a named store keeps its core store's chain-state map. -/
  Sts_setClock_core_σ : ∀ (E : Env V) (st : M.NS) (t : Int), (M.ns_setClock E st t).core.σ = st.core.σ
  /-- Setting the clock of a named store keeps the grade view of its core store's healing view. -/
  setClock_gradeView : ∀ (E : Env V) (st : M.NS) (t : Int), (M.gradeView (M.toHealing (M.ns_setClock E st t).core))
    = (M.gradeView (M.toHealing st.core))
  /-- Setting the clock of a named store keeps its SG rows. -/
  setClock_sg_rows : ∀ (E : Env V) (st : M.NS) (t : Int), (M.ns_setClock E st t).sg_rows = st.sg_rows
  /-- Setting the clock of a named store keeps the finalized block of its healing view. -/
  setClock_toHealing_F : ∀ (E : Env V) (st : M.NS) (t : Int), (M.toHealing (M.ns_setClock E st t).core).toFG.F = st.core.F
  /-- Setting the clock of a named store keeps the justified block of its healing view. -/
  setClock_toHealing_J : ∀ (E : Env V) (st : M.NS) (t : Int), (M.toHealing (M.ns_setClock E st t).core).toFG.J = st.core.J
  /-- Setting the clock of a named store keeps the block tree of its healing view. -/
  setClock_toHealing_T : ∀ (E : Env V) (st : M.NS) (t : Int), (M.toHealing (M.ns_setClock E st t).core).toFG.toSG.toGoldfishStore.T = st.core.T
  /-- Setting the clock of a named store keeps the `h_j` of its healing view. -/
  setClock_toHealing_h_j : ∀ (E : Env V) (st : M.NS) (t : Int), (M.toHealing (M.ns_setClock E st t).core).toFG.h_j = st.core.h_j
  /-- Setting the clock of a named store keeps the `h_max` of its healing view. -/
  setClock_toHealing_h_max : ∀ (E : Env V) (st : M.NS) (t : Int), (M.toHealing (M.ns_setClock E st t).core).toFG.h_max = st.core.h_max
  /-- Setting the clock of a named store keeps the chain-state map of its healing view. -/
  setClock_toHealing_σ : ∀ (E : Env V) (st : M.NS) (t : Int), (M.toHealing (M.ns_setClock E st t).core).toFG.σ = st.core.σ
  /-- Every outcome of the confirmation update keeps the filtered block tree. -/
  update_confirmation_with_filtered : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (st : M.S) (s : Slot)
    (st' : M.S), M.update_confirmation_with contract E hc st s ⇢ st' → M.get_filtered_block_tree
    (M.toHealing st').toFG
    = M.get_filtered_block_tree (M.toHealing st).toFG
  /-- Every outcome of the confirmation update keeps the finalized block. -/
  update_confirmation_with_toHealing_F : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (st : M.S) (s : Slot) (st' : M.S), M.update_confirmation_with contract E hc st s ⇢ st' → (M.toHealing st').toFG.F = (M.toHealing st).toFG.F
  /-- A block `C` of an outcome of the voter's filtered tree is in every outcome of the voter's
      processed tree, has `st.F` as an ancestor, is an ancestor of a block of that tree whose
      chain-state height is at least `st.h_max − 1`, and has the FG root as an ancestor. -/
  voter_filtered_block_tree_cases : ∀ (E : Env V) (st : M.S) (s : Slot) {C : Block V} (X : Finset (Block V)) (hX : M.voter_filtered_block_tree E st s ⇢ X) (hC : C ∈ X) (P : Finset (Block V)) (hP : M.voter_processed_block_tree E (M.toHealing st).toFG.toSG.toGoldfishStore s ⇢ P), C ∈ P ∧
    Block.Preceq st.F C ∧
    (∃ Y ∈ P,
    Block.Preceq C Y ∧ st.h_max - 1 ≤ (st.σ Y).h) ∧
    Block.Preceq (M.get_fg_root (M.toHealing st).toFG) C
  /-- Every outcome of the voter's filtered block tree is a subset of the store's block tree. -/
  Sts_voter_filtered_block_tree_subset : ∀ (E : Env V) (st : M.S) (s : Slot) (X : Finset (Block V)), M.voter_filtered_block_tree E st s ⇢ X → X ⊆ st.T
  /-- Setting the clock of a named store to `t` writes its core store's time to `t` and slot to
      `E.slotOf t`, and nothing else. -/
  setClock_core_eq_store_with_t_s : ∀ (E : Env V) (st : M.NS) (t : Time),
    (M.ns_setClock E st t).core = M.store_with_t_s st.core t (E.slotOf t)
  /-- Setting the clock of a coherent named store keeps it coherent. -/
  coherent_clock : ∀ (E : Env V) (cfg : Protocol.HeightConfig) (st : M.NS) (t : Time),
    Restated.Vocabulary.Proofs.NamedStore.Coherent M E cfg st →
    Restated.Vocabulary.Proofs.NamedStore.Coherent M E cfg (M.ns_setClock E st t)
  /-- If the confirmation walk's block `W` passes the test that the count of late voters is less
      than twice its score, every outcome of the confirmation update at slot `s` writes `W` to
      `live_confirmed`, for every outcome of the walk. -/
  update_confirmation_with_live_confirmed_of_eligible : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (st : M.S) (s : Slot)
    (tm : TimestampMap (GoldfishVote V)) (htm : st.tau ⇢ tm)
    (R : Block V) (hR : M.get_sg_root_with contract E hc st.toHealing (M.round_of hc st.s) ⇢ R)
    (score : Block V → ℕ)
    (hscore : ∀ B, M.goldfish_score E st.T
      ((_root_.DecoupledConsensusModel.beforeCutoff tm (M.support_cutoff E s) (st.pool s)).filter (fun u => M.no_second_vote_in (_root_.DecoupledConsensusModel.beforeCutoff st.timestamp_vote (M.confirmation_time E s) (st.pool s)) u = true))
      ((_root_.DecoupledConsensusModel.beforeCutoff tm (M.support_cutoff E s) (st.pool s)).filter (fun u => M.no_second_vote_in (_root_.DecoupledConsensusModel.beforeCutoff st.timestamp_vote (M.confirmation_time E s) (st.pool s)) u = true))
      s B ⇢ score B)
    (W : Block V) (hW : M.ghost R (M.get_filtered_block_tree st.toHealing.toFG) score
      (fun B => decide (M.voters_count E (_root_.DecoupledConsensusModel.beforeCutoff st.timestamp_vote (M.confirmation_time E s) (st.pool s)) s < 2 * score B)) ⇢ W),
    decide (M.voters_count E (_root_.DecoupledConsensusModel.beforeCutoff st.timestamp_vote (M.confirmation_time E s) (st.pool s)) s < 2 * score W) = true →
    ∀ (st' : M.S), M.update_confirmation_with contract E hc st s ⇢ st' →
    st'.live_confirmed = W
  /-- Every outcome of the confirmation update writes to `latest_confirmed` the block
      `M.floor_on_stable` of the new `latest_stable`, a candidate, and the old `latest_confirmed`;
      the candidate is the old `latest_confirmed`, or `M.advance_confirmed` of it with the walk's
      block when that block passes the eligibility test, or with a block the contract's SG candidate
      selection can return. -/
  update_confirmation_with_latest_confirmed_cases : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (st : M.S) (s : Slot)
    (tm : TimestampMap (GoldfishVote V)) (htm : st.tau ⇢ tm)
    (R : Block V) (hR : M.get_sg_root_with contract E hc st.toHealing (M.round_of hc st.s) ⇢ R)
    (score : Block V → ℕ)
    (hscore : ∀ B, M.goldfish_score E st.T
      ((_root_.DecoupledConsensusModel.beforeCutoff tm (M.support_cutoff E s) (st.pool s)).filter (fun u => M.no_second_vote_in (_root_.DecoupledConsensusModel.beforeCutoff st.timestamp_vote (M.confirmation_time E s) (st.pool s)) u = true))
      ((_root_.DecoupledConsensusModel.beforeCutoff tm (M.support_cutoff E s) (st.pool s)).filter (fun u => M.no_second_vote_in (_root_.DecoupledConsensusModel.beforeCutoff st.timestamp_vote (M.confirmation_time E s) (st.pool s)) u = true))
      s B ⇢ score B)
    (W : Block V) (hW : M.ghost R (M.get_filtered_block_tree st.toHealing.toFG) score
      (fun B => decide (M.voters_count E (_root_.DecoupledConsensusModel.beforeCutoff st.timestamp_vote (M.confirmation_time E s) (st.pool s)) s < 2 * score B)) ⇢ W)
    (st' : M.S) (hst' : M.update_confirmation_with contract E hc st s ⇢ st'),
    ∃ cand : Block V,
      st'.latest_confirmed = M.floor_on_stable st'.latest_stable cand st.latest_confirmed ∧
      (cand = st.latest_confirmed ∨
        (decide (M.voters_count E (_root_.DecoupledConsensusModel.beforeCutoff st.timestamp_vote (M.confirmation_time E s) (st.pool s)) s < 2 * score W) = true ∧
          cand = M.advance_confirmed st.latest_confirmed W) ∨
        ∃ G : Block V, contract.confirmationSG E hc st.toHealing s ⇢ some G ∧
          cand = M.advance_confirmed st.latest_confirmed G)
  /-- If the confirmation walk's block `W` passes the eligibility test, every outcome of the
      confirmation update writes to `latest_confirmed` the block `M.floor_on_stable` of the new
      `latest_stable`, `M.advance_confirmed` of the old `latest_confirmed` with `W`, and the old
      `latest_confirmed`. -/
  update_confirmation_with_latest_confirmed_of_eligible : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (st : M.S) (s : Slot)
    (tm : TimestampMap (GoldfishVote V)) (htm : st.tau ⇢ tm)
    (R : Block V) (hR : M.get_sg_root_with contract E hc st.toHealing (M.round_of hc st.s) ⇢ R)
    (score : Block V → ℕ)
    (hscore : ∀ B, M.goldfish_score E st.T
      ((_root_.DecoupledConsensusModel.beforeCutoff tm (M.support_cutoff E s) (st.pool s)).filter (fun u => M.no_second_vote_in (_root_.DecoupledConsensusModel.beforeCutoff st.timestamp_vote (M.confirmation_time E s) (st.pool s)) u = true))
      ((_root_.DecoupledConsensusModel.beforeCutoff tm (M.support_cutoff E s) (st.pool s)).filter (fun u => M.no_second_vote_in (_root_.DecoupledConsensusModel.beforeCutoff st.timestamp_vote (M.confirmation_time E s) (st.pool s)) u = true))
      s B ⇢ score B)
    (W : Block V) (hW : M.ghost R (M.get_filtered_block_tree st.toHealing.toFG) score
      (fun B => decide (M.voters_count E (_root_.DecoupledConsensusModel.beforeCutoff st.timestamp_vote (M.confirmation_time E s) (st.pool s)) s < 2 * score B)) ⇢ W),
    decide (M.voters_count E (_root_.DecoupledConsensusModel.beforeCutoff st.timestamp_vote (M.confirmation_time E s) (st.pool s)) s < 2 * score W) = true →
    ∀ (st' : M.S), M.update_confirmation_with contract E hc st s ⇢ st' →
    st'.latest_confirmed = M.floor_on_stable st'.latest_stable
      (M.advance_confirmed st.latest_confirmed W) st.latest_confirmed

/-- The facts about runs of the handlers family of the model `M` that the proofs over it call. -/
structure HandlersRunFacts (M : Model V) : Prop where
  /-- In every world the events of `rho` before time `t` reach from the initial world, the finalized
      block of `v`'s store is in its tree with a descendant whose chain-state height is at least
      `h_max - 1`. -/
  finalizedViable_stateBeforeTime : ∀ (S : Setup V) (rho : Record.Run V) (t : Time) (v : V),
    ∀ w₁ ∈ (rho.events.filter (fun e => decide (e.time < t))).foldlM (worldStepOf M S)
        (fun u => M.initial S u),
      (w₁ v).st.core.F ∈ (w₁ v).st.core.T ∧ ∃ W ∈ (w₁ v).st.core.T,
        Block.Preceq (w₁ v).st.core.F W ∧ (w₁ v).st.core.h_max - 1 ≤ ((w₁ v).st.core.σ W).h
  /-- In every world the events of `rho` before time `t` reach from the initial world, every row in
      bucket `r` of `v`'s store is of round `r`. -/
  sgRowRounds_stateBeforeTime : ∀ (S : Setup V) (rho : Record.Run V) (t : Time) (v : V),
    ∀ w₁ ∈ (rho.events.filter (fun e => decide (e.time < t))).foldlM (worldStepOf M S)
        (fun u => M.initial S u),
      ∀ (r : Round), ∀ row ∈ (w₁ v).st.sg_rows r, row.round = r
  /-- If `0 ≤ bound` and every event of `rho` before index `i` is at time at most `bound`, then
      before the `i`-th event `reader`'s clock is at most `bound`, and every row it holds for a
      round `k` is of round `k` with an SG-vote stamp at most `bound`. -/
  sgArrival_prefix_data : ∀ (S : Setup V) (rho : Record.Run V) (bound : Time) (hzero : 0 ≤ bound) (i : Nat)
    (hbefore : ∀ j (e : Record.Event V), j < i → rho.events[j]? = some e → e.time ≤ bound) (reader : V),
    ∀ w ∈ stateBeforeOf M S rho i,
      (w reader).st.core.t ≤ bound ∧
        ∀ k (a : NamedAttestation V), a ∈ (w reader).st.sg_rows k →
          a.round = k ∧ ∃ stamp : Time, stamp ≤ bound ∧
            (w reader).st.core.timestamp_sg_vote (M.sgVote a.erase) = some (stamp : Stamp)
  /-- Before the `i`-th event of `rho`, `v`'s store has `h_j < h_max`. -/
  justificationBelowMax_stateBefore : ∀ (S : Setup V) (rho : Record.Run V) (i : Nat) (v : V),
    ∀ w₁ ∈ stateBeforeOf M S rho i, (w₁ v).st.core.h_j < (w₁ v).st.core.h_max
  /-- In every world the events of `rho` before time `t` reach from the initial world, `v`'s store
      has `h_j < h_max`. -/
  justificationBelowMax_stateBeforeTime : ∀ (S : Setup V) (rho : Record.Run V) (t : Time) (v : V),
    ∀ w₁ ∈ (rho.events.filter (fun e => decide (e.time < t))).foldlM (worldStepOf M S)
        (fun u => M.initial S u),
      (w₁ v).st.core.h_j < (w₁ v).st.core.h_max
  /-- Before the `i`-th event of `rho`, every body `v` holds derives a justified height at most its
      store's `h_j`. -/
  noHighJustifications_stateBefore : ∀ (S : Setup V) (rho : Record.Run V) (i : Nat) (v : V),
    ∀ w₁ ∈ stateBeforeOf M S rho i,
      ∀ B ∈ (w₁ v).st.bodies, (M.derive_named S.E S.cfg B).h_j ≤ (w₁ v).st.core.h_j
  /-- In every world the events of `rho` before time `t` reach from the initial world, every body
      `v` holds derives a justified height at most its store's `h_j`. -/
  noHighJustifications_stateBeforeTime : ∀ (S : Setup V) (rho : Record.Run V) (t : Time) (v : V),
    ∀ w₁ ∈ (rho.events.filter (fun e => decide (e.time < t))).foldlM (worldStepOf M S)
        (fun u => M.initial S u),
      ∀ B ∈ (w₁ v).st.bodies, (M.derive_named S.E S.cfg B).h_j ≤ (w₁ v).st.core.h_j
  /-- For `i ≤ j`, a named body `reader` holds before the `i`-th event of `rho` is still held before
      the `j`-th, with the same block stamp. -/
  stateBefore_body_stamp_mono : ∀ (S : Setup V) (rho : Record.Run V) (reader : V) {i j : Nat}
    (hij : i ≤ j) {B : NamedBlock V},
    ∀ w₁ ∈ stateBeforeOf M S rho i,
    B ∈ (w₁ reader).st.bodies →
    ∀ w₂ ∈ ((rho.events.drop i).take (j - i)).foldlM (worldStepOf M S) w₁,
    B ∈ (w₂ reader).st.bodies ∧
      (w₂ reader).st.core.timestamp_block B.erase =
        (w₁ reader).st.core.timestamp_block B.erase
  /-- For `m ≤ n`, the justified height of `v`'s store before the `m`-th event of `rho` is at most
      its justified height before the `n`-th. -/
  stateBefore_h_j_mono : ∀ (S : Setup V) (rho : Record.Run V) (v : V) {m n : Nat} (hmn : m ≤ n),
    ∀ w₁ ∈ stateBeforeOf M S rho m,
    ∀ w₂ ∈ ((rho.events.drop m).take (n - m)).foldlM (worldStepOf M S) w₁,
      (w₁ v).st.core.h_j ≤ (w₂ v).st.core.h_j
  /-- Before the `i`-th event of `rho`, some body `v` holds derives `v`'s store's finalized block,
      with a finalized height less than the store's `h_max`. -/
  finalization_carrier_stateBefore : ∀ (S : Setup V) (rho : Record.Run V) (i : Nat) (v : V)
    (w : V → M.N) (hw : w ∈ stateBeforeOf M S rho i),
    ∃ D : NamedBlock V, D ∈ (w v).st.bodies ∧
      (M.derive_named S.E S.cfg D).F = (w v).st.core.F ∧
      (M.derive_named S.E S.cfg D).h_F < (w v).st.core.h_max
  /-- In every world the events of `rho` before time `t` reach from the initial world, some body `v`
      holds derives `v`'s store's finalized block, with a finalized height less than the store's
      `h_max`. -/
  finalization_carrier_stateBeforeTime : ∀ (S : Setup V) (rho : Record.Run V) (t : Time) (v : V)
    (w : V → M.N)
    (hw : w ∈ (rho.events.filter (fun e => decide (e.time < t))).foldlM (worldStepOf M S)
      (fun u => M.initial S u)),
    ∃ D : NamedBlock V, D ∈ (w v).st.bodies ∧
      (M.derive_named S.E S.cfg D).F = (w v).st.core.F ∧
      (M.derive_named S.E S.cfg D).h_F < (w v).st.core.h_max
  /-- In every world the events of `rho` before time `t` reach from the initial world, some body `v`
      holds derives a chain state whose height is its store's `h_max`. -/
  maximum_carrier_stateBeforeTime : ∀ (S : Setup V) (rho : Record.Run V) (t : Time) (v : V),
    ∀ w₁ ∈ (rho.events.filter (fun e => decide (e.time < t))).foldlM (worldStepOf M S)
        (fun u => M.initial S u),
    ∃ D : NamedBlock V, D ∈ (w₁ v).st.bodies ∧
      (M.derive_named S.E S.cfg D).h = (w₁ v).st.core.h_max
  /-- Before the `i`-th event of `rho`, some body `v` holds derives a chain state whose height is
      its store's `h_max`. -/
  maximum_carrier_stateBefore : ∀ (S : Setup V) (rho : Record.Run V) (i : Nat) (v : V),
    ∀ w₁ ∈ stateBeforeOf M S rho i,
    ∃ D : NamedBlock V, D ∈ (w₁ v).st.bodies ∧
      (M.derive_named S.E S.cfg D).h = (w₁ v).st.core.h_max
  /-- For `i ≤ j`, an attestation row `reader` holds before the `i`-th event of `rho` is still held
      before the `j`-th, with the same SG-vote stamp. -/
  stateBefore_sg_row_stamp_mono : ∀ (S : Setup V) (rho : Record.Run V) (reader : V) {i j : Nat}
    (hij : i ≤ j) {a : NamedAttestation V},
    ∀ w₁ ∈ stateBeforeOf M S rho i,
    a ∈ (w₁ reader).st.sg_rows a.round →
    ∀ w₂ ∈ ((rho.events.drop i).take (j - i)).foldlM (worldStepOf M S) w₁,
    a ∈ (w₂ reader).st.sg_rows a.round ∧
      (w₂ reader).st.core.timestamp_sg_vote (M.sgVote a.erase) =
        (w₁ reader).st.core.timestamp_sg_vote (M.sgVote a.erase)
  /-- Before the first event of `rho`, every validator holds the genesis body. -/
  genesis_mem_stateBefore_zero : ∀ (S : Setup V) (rho : Record.Run V) (v : V) (w : V → M.N)
    (hw : w ∈ stateBeforeOf M S rho 0), (NamedBlock.genesis : NamedBlock V) ∈ (w v).st.bodies

end DecoupledConsensusModel.Sts.Record
