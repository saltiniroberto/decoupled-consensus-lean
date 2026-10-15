import Model.Record.Wiring
import Proofs.Vocabulary.Protocol.Handlers.TickBridges
import Model.Record.ModelSpellings
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
import Proofs.Vocabulary.ModelProperties.confirmationReadFrom
import Proofs.Vocabulary.Protocol.Schedule.ReceiptCallsF1
import Proofs.Vocabulary.Protocol.Handlers.HandlerAdmissionGuards
import Proofs.Vocabulary.Protocol.Schedule.HeldSkipProducers
import Proofs.Vocabulary.ModelProperties.NamedReceiptCalls_postCore
import Proofs.Vocabulary.Execution.OutageActionInputs
import Proofs.Vocabulary.ModelProperties.with_attestation_input
import Proofs.Vocabulary.Protocol.ValidatorClient.RecordFresh
import Proofs.Vocabulary.Protocol.ValidatorClient.RecordTargetHistory
import Proofs.Vocabulary.Protocol.Handlers.RawRelay
import Proofs.Vocabulary.Execution.HealthyLocalFacts
import Proofs.Vocabulary.Protocol.Handlers.Admission
import Proofs.Vocabulary.ModelProperties.Block_parent
import Proofs.Vocabulary.ModelProperties.update_finality
import Proofs.Vocabulary.Protocol.ChainState.DerivationGeometry
import Proofs.Vocabulary.Protocol.ValidatorClient.SlashableBound
import Proofs.Vocabulary.Protocol.Schedule.SlotInduction
import Proofs.Claims.Spec2Claims.Claim13beRoute3_45b
import Proofs.Claims.Spec2Claims.Claim13bModel_Block_preceq
import Proofs.Claims.Spec2Claims.Claim13bModel_proposer_view
import Proofs.Claims.Spec2Claims.Claim13bModel_own_lock
import Proofs.Claims.Spec2Claims.Claim13bModel_Store_tau_mk
import Proofs.Vocabulary.Protocol.Handlers.Pool
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.HeightProgressClosurescoreEq
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.ProposalSnapshotBridge

/-!
# Facts of the store routines

`StoreFacts` holds the facts a model `M` provides about its store routines: the healing view
`M.toHealing`, the sets of processed Goldfish votes and attestations, the SG vote of an attestation,
the test `M.resolved` and the resolution times `st.tau`. `StoreRunFacts` holds further facts about
ticks, receipts and runs.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

/-- The facts about the store routines of a model `M`. -/
structure StoreFacts (M : Model V) : Prop where
  /-- Two stores with the same block tree, block stamps and vote stamps have the same resolution
      times `tau`. -/
  tau_eq_of_fields : ∀ {st st' : M.S} (hT : st.T = st'.T)
    (hb : st.timestamp_block = st'.timestamp_block)
    (hv : st.timestamp_vote = st'.timestamp_vote), st.tau = st'.tau
  /-- Writing a store's clock and slot keeps its vote stamps. -/
  store_with_t_s_timestamp_vote : ∀ (st : M.S) (t : Time) (s : Slot),
    (M.store_with_t_s st t s).timestamp_vote = st.timestamp_vote
  /-- Writing a store's chain states, tree `T'` and block stamps gives a store whose tree is `T'`,
      when the blocks of `T'` have distinct roots, each has a stamp, `T'` holds each one's parent,
      and `T'` holds `st.F`. -/
  store_with_σ_T_timestamp_block_T : ∀ (st : M.S) (σ' : Block V → M.CS) (T' : Finset (Block V))
    (τ' : TimestampMap (Block V))
    (hT : ∀ A ∈ T', ∀ D ∈ T', A.root = D.root → A = D)
    (hτ : ∀ A ∈ T', (τ' A).isSome = true)
    (hpar : ∀ A ∈ T', A.parent ∈ T')
    (hF : st.F ∈ T'),
    (M.store_with_σ_T_timestamp_block st σ' T' τ').T = T'
  /-- Writing a store's chain states, tree and block stamps keeps its `h_max`. -/
  store_with_σ_T_timestamp_block_h_max : ∀ (st : M.S) (σ' : Block V → M.CS)
    (T' : Finset (Block V)) (τ' : TimestampMap (Block V)),
    (M.store_with_σ_T_timestamp_block st σ' T' τ').h_max = st.h_max
  /-- Writing a store's chain states, tree and block stamps keeps its justified block. -/
  store_with_σ_T_timestamp_block_J : ∀ (st : M.S) (σ' : Block V → M.CS) (T' : Finset (Block V))
    (τ' : TimestampMap (Block V)), (M.store_with_σ_T_timestamp_block st σ' T' τ').J = st.J
  /-- Writing a store's chain states, tree and block stamps keeps its justification height `h_j`. -/
  store_with_σ_T_timestamp_block_h_j : ∀ (st : M.S) (σ' : Block V → M.CS)
    (T' : Finset (Block V)) (τ' : TimestampMap (Block V)),
    (M.store_with_σ_T_timestamp_block st σ' T' τ').h_j = st.h_j
  /-- If every round's SG votes of `st`'s core store are the erasures of `st`'s rows of that round,
      every named attestation in `st`'s rows of its round has its erasure in `M.store_sg_pool` of
      that round. -/
  pool_view_mem : ∀ (st : M.NS), (∀ r, st.core.sg_votes r = (st.sg_rows r).map NamedAttestation.erase) →
    ∀ (row : NamedAttestation V), row ∈ st.sg_rows row.round →
      row.erase ∈ M.store_sg_pool st.core row.round
  /-- Writing a store's chain states to `σ'`, with its tree and block stamps, gives a store whose
      chain states are `σ'`. -/
  store_with_σ_T_timestamp_block_σ : ∀ (st : M.S) (σ' : Block V → M.CS) (T' : Finset (Block V))
    (τ' : TimestampMap (Block V)), (M.store_with_σ_T_timestamp_block st σ' T' τ').σ = σ'
  /-- Writing a store's chain states, tree and block stamps keeps its finalized block. -/
  store_with_σ_T_timestamp_block_F : ∀ (st : M.S) (σ' : Block V → M.CS) (T' : Finset (Block V))
    (τ' : TimestampMap (Block V)), (M.store_with_σ_T_timestamp_block st σ' T' τ').F = st.F
  /-- Writing a store's clock and slot to `t` and `s` gives a store whose slot is `s`. -/
  store_with_t_s_s : ∀ (st : M.S) (t : Time) (s : Slot), (M.store_with_t_s st t s).s = s
  /-- Every Goldfish vote of slot `k` in the initial store `M.store_init` is signed by a member of
      `E.committee k`. -/
  committeePools_init : ∀ (E : Env V) (k : Slot) (u : GoldfishVote V), u ∈ (M.store_init : M.S).gf_votes k → u.val_index ∈ E.committee k
  /-- If `st.t ≤ t` and `st`'s Goldfish votes are in their slot's list, stamped exactly when pooled,
      with no stamp later than `st.t`, then `M.store_with_t_s st t s` keeps every vote and stamp of
      `st` and satisfies the same conditions. -/
  poolStep_tickStore : ∀ (st : M.S) (t : Time) (s : Slot), st.t ≤ t →
    ((∀ (k : Slot) (x : GoldfishVote V), x ∈ st.gf_votes k → x.slot = k) ∧
      (∀ (k : Slot) (x : GoldfishVote V), x ∈ st.gf_votes k → (st.timestamp_vote x).isSome = true) ∧
      (∀ x : GoldfishVote V, (st.timestamp_vote x).isSome = true → x ∈ st.gf_votes x.slot) ∧
      (∀ (x : GoldfishVote V) (c : Stamp), st.timestamp_vote x = some c → c ≤ (st.t : Stamp))) →
    ((∀ (k : Slot) (x : GoldfishVote V), x ∈ st.gf_votes k → x ∈ (M.store_with_t_s st t s).gf_votes k) ∧
      (∀ (x : GoldfishVote V) (c : Stamp), st.timestamp_vote x = some c →
        (M.store_with_t_s st t s).timestamp_vote x = some c)) ∧
    ((∀ (k : Slot) (x : GoldfishVote V), x ∈ (M.store_with_t_s st t s).gf_votes k → x.slot = k) ∧
      (∀ (k : Slot) (x : GoldfishVote V), x ∈ (M.store_with_t_s st t s).gf_votes k →
        ((M.store_with_t_s st t s).timestamp_vote x).isSome = true) ∧
      (∀ x : GoldfishVote V, ((M.store_with_t_s st t s).timestamp_vote x).isSome = true →
        x ∈ (M.store_with_t_s st t s).gf_votes x.slot) ∧
      (∀ (x : GoldfishVote V) (c : Stamp), (M.store_with_t_s st t s).timestamp_vote x = some c →
        c ≤ ((M.store_with_t_s st t s).t : Stamp)))
  /-- Writing a store's clock and slot keeps its Goldfish vote pool of every slot. -/
  pool_set_clock_slot : ∀ (st : M.S) (t : Int) (s k : Slot),
    (M.store_with_t_s st t s).pool k = st.pool k
  /-- `u` is in `M.store_pool st k` exactly when `u` is in the list `st.gf_votes k`. -/
  mem_pool_iff : ∀ (st : M.S) (k : Slot) (u : GoldfishVote V),
    u ∈ M.store_pool st k ↔ u ∈ st.gf_votes k
  /-- `b` is in `M.store_sg_pool st r` exactly when `b` is in the list `st.sg_votes r`. -/
  ModelProperties_mem_sg_pool_iff : ∀ (st : M.S) (r : Round) (b : CombinedAttestation V),
    b ∈ M.store_sg_pool st r ↔ b ∈ st.sg_votes r
  /-- The healing view `M.toHealing st` has `st`'s finalized block. -/
  ModelProperties_toHealing_F : ∀ (st : M.S), (M.toHealing st).toFG.F = st.F
  /-- The healing view `M.toHealing st` has `st`'s justified block. -/
  ModelProperties_toHealing_J : ∀ (st : M.S), (M.toHealing st).toFG.J = st.J
  /-- The healing view `M.toHealing st` has `st`'s block tree. -/
  toHealing_T : ∀ (st : M.S), (M.toHealing st).toFG.toSG.toGoldfishStore.T = st.T
  /-- The healing view `M.toHealing st` has `st`'s `h_max`. -/
  ModelProperties_toHealing_h_max : ∀ (st : M.S), (M.toHealing st).toFG.h_max = st.h_max
  /-- The healing view `M.toHealing st` has `st`'s `live_confirmed`. -/
  toHealing_live_confirmed : ∀ (st : M.S),
    (M.toHealing st).toFG.toSG.toGoldfishStore.live_confirmed = st.live_confirmed
  /-- The healing view `M.toHealing st` has `st`'s slot. -/
  toHealing_s : ∀ (st : M.S), (M.toHealing st).toFG.toSG.toGoldfishStore.s = st.s
  /-- The round-`r` SG votes of the healing view `M.toHealing st` are the images under `M.sgVote` of
      `M.store_sg_pool st r`. -/
  ModelProperties_toHealing_sg_votes : ∀ (st : M.S) (r : Round),
    (M.toHealing st).toFG.toSG.sg_votes r = (M.store_sg_pool st r).image M.sgVote
  /-- The healing view `M.toHealing st` has `st`'s chain states `σ`. -/
  ModelProperties_toHealing_σ : ∀ (st : M.S), (M.toHealing st).toFG.σ = st.σ
  /-- The SG vote of `a.erase` names the confirmed block `a.confirmed`. -/
  sgVote_confirmed : ∀ (a : NamedAttestation V), (M.sgVote a.erase).confirmed = a.confirmed
  /-- The SG vote of `a.erase` has the round `a.round`. -/
  sgVote_round : ∀ (a : NamedAttestation V), (M.sgVote a.erase).round = a.round
  /-- The SG vote of `a.erase` has the validator index `a.val_index`. -/
  sgVote_val : ∀ (a : NamedAttestation V), (M.sgVote a.erase).val_index = a.val_index
  /-- The healing view `M.toHealing st` has `st`'s slot. -/
  toHealing_slot : ∀ (st : M.S), (M.toHealing st).toFG.toSG.toGoldfishStore.s = st.s
  /-- If the head of the Goldfish vote `u` resolves in `st`'s tree to `H`, and `u` is stamped before
      the cutoff `Γ` under an outcome `tm` of `st.tau`, then the slot of `H` is at most the slot of
      `u`. -/
  head_slot_le_of_tau : ∀ (st : M.S) {Γ : Time} {u : GoldfishVote V} {H : Block V}
    (hfind : Block.find? st.T u.head = some H)
    (tm : TimestampMap (GoldfishVote V)) (htm : st.tau ⇢ tm)
    (h : stampedBefore tm Γ u = true),
    H.slot ≤ u.slot
  /-- `u` is in `M.gs_pool gs s` exactly when `u` is in the list `gs.gf_votes s`. -/
  mem_goldfishStore_pool_iff : ∀ (gs : M.GS) (s : Slot) (u : GoldfishVote V),
    u ∈ M.gs_pool gs s ↔ u ∈ gs.gf_votes s
  /-- `c` is in `M.store_sg_pool st r` exactly when `c` is in the list `st.sg_votes r`. -/
  Sts_mem_sg_pool_iff : ∀ (st : M.S) (r : Round) (c : CombinedAttestation V),
    c ∈ M.store_sg_pool st r ↔ c ∈ st.sg_votes r
  /-- `u` is in `M.store_pool st s` exactly when `u` is in the list `st.gf_votes s`. -/
  mem_store_pool_iff : ∀ (st : M.S) (s : Slot) (u : GoldfishVote V),
    u ∈ M.store_pool st s ↔ u ∈ st.gf_votes s
  /-- Two stores with the same lists `gf_votes` have the same `M.store_pool` at every slot. -/
  pool_eq_of_gf_votes_eq : ∀ {st st' : M.S} (h : st.gf_votes = st'.gf_votes) (k : Slot),
    M.store_pool st k = M.store_pool st' k
  /-- Every outcome of `M.resolved T u` is `true` exactly when `u`'s head resolves in `T` to a block
      of a slot at most `u`'s. -/
  resolved_eq_true_iff : ∀ (T : Finset (Block V)) (u : GoldfishVote V) (b : Bool),
    M.resolved T u ⇢ b →
    (b = true ↔ ∃ X : Block V, Block.find? T u.head = some X ∧ X.slot ≤ u.slot)
  /-- The SG vote of an attestation names the attestation's confirmed block. -/
  sgVote_confirmed_eq : ∀ (A : CombinedAttestation V), (M.sgVote A).confirmed = A.confirmed
  /-- Two attestations with the same validator, round and confirmed block have the same SG vote. -/
  sgVote_eq_of_fields : ∀ {A A' : CombinedAttestation V} (h₁ : A.val_index = A'.val_index)
    (h₂ : A.round = A'.round) (h₃ : A.confirmed = A'.confirmed), M.sgVote A = M.sgVote A'
  /-- Two named attestations with the same validator, round and confirmed block have the same SG
      vote. -/
  sgVote_erase_eq_of_fields : ∀ {a b : NamedAttestation V} (h₁ : a.val_index = b.val_index)
    (h₂ : a.round = b.round) (h₃ : a.confirmed = b.confirmed),
    M.sgVote a.erase = M.sgVote b.erase
  /-- The SG vote of an attestation has the attestation's round. -/
  sgVote_round_eq_round : ∀ (A : CombinedAttestation V), (M.sgVote A).round = A.round
  /-- The SG vote of an attestation has the attestation's validator. -/
  sgVote_val_index_eq_val_index : ∀ (A : CombinedAttestation V),
    (M.sgVote A).val_index = A.val_index
  /-- If `u`'s head resolves in `st`'s tree to `H` and `u` is stamped before `Γ` under an outcome
      `tm` of `st.tau`, then `H` is stamped before `Γ` under `st.timestamp_block`. -/
  stampedBefore_block_of_tau : ∀ (st : M.S) {Γ : Time} {u : GoldfishVote V} {H : Block V}
    (hfind : Block.find? st.T u.head = some H)
    (tm : TimestampMap (GoldfishVote V)) (htm : st.tau ⇢ tm)
    (h : stampedBefore tm Γ u = true),
    stampedBefore st.timestamp_block Γ H = true
  /-- If `u`'s head resolves in `st`'s tree to a block `H` of a slot at most `u`'s, and both `u` and
      `H` are stamped before `Γ`, then `u` is stamped before `Γ` under every outcome of `st.tau`. -/
  stampedBefore_store_tau_of : ∀ (st : M.S) {Γ : Time} {u : GoldfishVote V} {H : Block V}
    (hfind : Block.find? st.T u.head = some H) (hslot : H.slot ≤ u.slot)
    (hv : stampedBefore st.timestamp_vote Γ u = true)
    (hH : stampedBefore st.timestamp_block Γ H = true)
    (tm : TimestampMap (GoldfishVote V)) (htm : st.tau ⇢ tm),
    stampedBefore tm Γ u = true
  /-- If `u`'s head resolves in the Goldfish store `gs`'s tree to a block `H` of a slot at most
      `u`'s, and both `u` and `H` are stamped before `Γ`, then `u` is stamped before `Γ` under every
      outcome of `gs.tau`. -/
  stampedBefore_tau_of : ∀ (gs : M.GS) {Γ : Time} {u : GoldfishVote V} {H : Block V}
    (hfind : Block.find? gs.T u.head = some H) (hslot : H.slot ≤ u.slot)
    (hv : stampedBefore gs.timestamp_vote Γ u = true)
    (hH : stampedBefore gs.timestamp_block Γ H = true)
    (tm : TimestampMap (GoldfishVote V)) (htm : gs.tau ⇢ tm),
    stampedBefore tm Γ u = true
  /-- If `u` is stamped before `Γ` under an outcome of `st.tau`, then `u` is stamped before `Γ`
      under `st.timestamp_vote`. -/
  stampedBefore_vote_of_tau : ∀ (st : M.S) {Γ : Time} {u : GoldfishVote V}
    (tm : TimestampMap (GoldfishVote V)) (htm : st.tau ⇢ tm)
    (h : stampedBefore tm Γ u = true),
    stampedBefore st.timestamp_vote Γ u = true
  /-- If `u`'s head resolves in `st`'s tree to a block `X` of a slot at most `u`'s, and `st` stamps
      `u` at `τ` and `X` at `σ`, then every outcome of `st.tau` gives `u` the larger of `τ` and `σ`. -/
  tau_eq_max : ∀ (st : M.S) {u : GoldfishVote V} {X : Block V}
    (hX : Block.find? st.T u.head = some X) (hXs : X.slot ≤ u.slot) {τ σ : Stamp}
    (hτ : st.timestamp_vote u = some τ) (hσ : st.timestamp_block X = some σ)
    (tm : TimestampMap (GoldfishVote V)) (htm : st.tau ⇢ tm),
    tm u = some (max τ σ)
  /-- If `u`'s head resolves in the Goldfish store `gs`'s tree to a block `X` of a slot at most
      `u`'s, and `gs` stamps `u` at `τ` and `X` at `σ`, then every outcome of `gs.tau` gives `u` the
      larger of `τ` and `σ`. -/
  tau_eq_max_gf : ∀ (gs : M.GS) {u : GoldfishVote V} {X : Block V}
    (hX : Block.find? gs.T u.head = some X) (hXs : X.slot ≤ u.slot) {τ σ : Stamp}
    (hτ : gs.timestamp_vote u = some τ) (hσ : gs.timestamp_block X = some σ)
    (tm : TimestampMap (GoldfishVote V)) (htm : gs.tau ⇢ tm),
    tm u = some (max τ σ)
  /-- The healing view `M.toHealing st` has `st`'s finalized block. -/
  Sts_toHealing_F : ∀ (st : M.S), (M.toHealing st).toFG.F = st.F
  /-- The healing view `M.toHealing st` has `st`'s justified block. -/
  Sts_toHealing_J : ∀ (st : M.S), (M.toHealing st).toFG.J = st.J
  /-- The Goldfish store of the healing view `M.toHealing st` has `st`'s block tree. -/
  toHealing_gs_T : ∀ (st : M.S), (M.toHealing st).toFG.toSG.toGoldfishStore.T = st.T
  /-- The Goldfish store of the healing view `M.toHealing st` has `st`'s Goldfish vote list of every
      slot. -/
  toHealing_gs_gf_votes : ∀ (st : M.S) (s : Slot),
    (M.toHealing st).toFG.toSG.toGoldfishStore.gf_votes s = st.gf_votes s
  /-- The Goldfish store of the healing view `M.toHealing st` has `M.store_pool st s` as its vote
      pool of slot `s`. -/
  toHealing_gs_pool : ∀ (st : M.S) (s : Slot),
    M.gs_pool (M.toHealing st).toFG.toSG.toGoldfishStore s = M.store_pool st s
  /-- The Goldfish store of the healing view `M.toHealing st` has `st`'s slot. -/
  toHealing_gs_s : ∀ (st : M.S), (M.toHealing st).toFG.toSG.toGoldfishStore.s = st.s
  /-- The Goldfish store of the healing view `M.toHealing st` has `st`'s block stamps. -/
  toHealing_gs_timestamp_block : ∀ (st : M.S),
    (M.toHealing st).toFG.toSG.toGoldfishStore.timestamp_block = st.timestamp_block
  /-- The Goldfish store of the healing view `M.toHealing st` has `st`'s vote stamps. -/
  toHealing_gs_timestamp_vote : ∀ (st : M.S),
    (M.toHealing st).toFG.toSG.toGoldfishStore.timestamp_vote = st.timestamp_vote
  /-- The healing view `M.toHealing st` has `st`'s justification height `h_j`. -/
  toHealing_h_j : ∀ (st : M.S), (M.toHealing st).toFG.h_j = st.h_j
  /-- The healing view `M.toHealing st` has `st`'s `h_max`. -/
  Sts_toHealing_h_max : ∀ (st : M.S), (M.toHealing st).toFG.h_max = st.h_max
  /-- The round-`r` SG votes of the healing view `M.toHealing st` are the images under `M.sgVote` of
      `M.store_sg_pool st r`. -/
  Sts_toHealing_sg_votes : ∀ (st : M.S) (r : Round),
    (M.toHealing st).toFG.toSG.sg_votes r = (M.store_sg_pool st r).image M.sgVote
  /-- The healing view `M.toHealing st` has `st`'s chain states `σ`. -/
  Sts_toHealing_σ : ∀ (st : M.S), (M.toHealing st).toFG.σ = st.σ
  /-- The resolution test `M.resolved T u` has an outcome. -/
  resolved_nonempty : ∀ (T : Finset (Block V)) (u : GoldfishVote V),
    ∃ b : Bool, M.resolved T u ⇢ b
  /-- The resolution times `st.tau` of a store have an outcome. -/
  tau_nonempty : ∀ (st : M.S), ∃ tm : TimestampMap (GoldfishVote V), st.tau ⇢ tm
  /-- If `st` is a named store a run reaches, so is `st` with its clock set to `t`. -/
  reachedStore_setClock : ∀ (E : Env V) (st : M.NS) (t : Time),
    M.reachedStore st → M.reachedStore (M.ns_setClock E st t)
  /-- If every block of `st`'s tree with `B`'s root is `B`, then `M.rootFresh st B`. -/
  rootFresh_of_distinct : ∀ (st : M.S) (B : Block V), (∀ C ∈ st.T, C.root = B.root → C = B) →
    M.rootFresh st B

/-- Further facts about the store routines of a model `M`, about ticks, receipts and runs. -/
structure StoreRunFacts (M : Model V) : Prop where
  /-- For every outcome `out` of `v`'s tick at `t` from `n`, a round-`r` attestation in the
      `sg_pool` of `out.1`'s core store is in that of `n`'s, or some object `out` sends carries it. -/
  tick_sg_pool_mem : ∀ (S : Setup V) (v : V) (n : M.N) (t : Time) (r : Round)
    {b : CombinedAttestation V} (out : M.N × List (NamedObject V)), M.tick S v n t ⇢ out →
    b ∈ out.1.st.core.sg_pool r →
      b ∈ n.st.core.sg_pool r ∨ ∃ o ∈ out.2, DecoupledConsensusModel.Proofs.Optimistic.CarriesRow o b
  /-- In every world the run `rho` can reach before its `i`-th event, every named attestation in the
      round-`k` rows of a validator's store has round `k`. -/
  row_round_stateBefore : ∀ (S : Setup V) (rho : Record.Run V) (i : Nat) (reader : V) (k : Round)
    (a : NamedAttestation V) (w : V → M.N) (hw : w ∈ stateBeforeOf M S rho i)
    (ha : a ∈ (w reader).st.sg_rows k), a.round = k
  /-- For every node state `n'` that `n`'s receipt of `o` can return, a round-`r` attestation in the
      `sg_pool` of `n'`'s core store is in that of `n`'s, or `o` carries it. -/
  process_sg_pool_mem : ∀ (S : Setup V) (n : M.N) (o : NamedObject V) (r : Round)
    {b : CombinedAttestation V} (n' : M.N), M.process S n o ⇢ n' →
    b ∈ n'.st.core.sg_pool r →
      b ∈ n.st.core.sg_pool r ∨ DecoupledConsensusModel.Proofs.Optimistic.CarriesRow o b
  /-- For every outcome `out` of `v`'s tick at `t` from `n`, a vote in the slot-`k` list of
      `out.1`'s core store is in that of `n`'s, or `out` sends it, or `out` sends a block that
      carries it. -/
  tick_gf_votes_mem : ∀ (S : Setup V) (v : V) (n : M.N) (t : Time) (k : Slot)
    {u : GoldfishVote V} (out : M.N × List (NamedObject V)), M.tick S v n t ⇢ out →
    u ∈ out.1.st.core.gf_votes k →
      u ∈ n.st.core.gf_votes k ∨ NamedObject.gfVote u ∈ out.2 ∨
        ∃ B : NamedBlock V, NamedObject.block B ∈ out.2 ∧ u ∈ B.gf_votes
  /-- For every node state `n'` that `n`'s receipt of `o` can return, a vote in the slot-`k` list of
      `n'`'s core store is in that of `n`'s, or `o` is that vote, or `o` is a block that carries it. -/
  process_gf_votes_mem : ∀ (S : Setup V) (n : M.N) (o : NamedObject V) (k : Slot)
    {u : GoldfishVote V} (n' : M.N), M.process S n o ⇢ n' →
    u ∈ n'.st.core.gf_votes k →
      u ∈ n.st.core.gf_votes k ∨ o = NamedObject.gfVote u ∨
        ∃ B : NamedBlock V, o = NamedObject.block B ∧ u ∈ B.gf_votes

end DecoupledConsensusModel.Sts.Record
