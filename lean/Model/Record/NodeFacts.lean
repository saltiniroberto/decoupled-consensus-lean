import Model.Record.Wiring
import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.Node
import Proofs.Claims.Spec2Claims.Claim13bModel_Env_committee_gst
import Model.Record.ModelSpellings
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Records
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
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
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
import Proofs.Vocabulary.Protocol.ChainState.DerivationGeometry
import Proofs.Vocabulary.Protocol.ValidatorClient.SlashableBound
import Proofs.Vocabulary.Protocol.Schedule.SlotInduction
import Proofs.Vocabulary.Protocol.Handlers.StoreBridge
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedStore_initial
import Proofs.Vocabulary.Protocol.Handlers.Pool
import Proofs.Claims.Spec2Claims.Claim13bModel_opening
import Proofs.Claims.ProcessedFlip
import Model.Conditions.Vocabulary_Protocol_Handlers_Pool
import Proofs.Vocabulary.Protocol.ChainState.W4FKChainFinalityWrite
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Claim13beRoute3_23
import Proofs.Claims.Spec2Claims.Claim13beRoute3_23
import Proofs.Vocabulary.Protocol.Duties.Proposals.ProposalRows
import Model.Conditions.Vocabulary_Protocol_Handlers_AcceptanceTiming
import Proofs.Vocabulary.ModelProperties.update_confirmation_with
import Proofs.Vocabulary.Protocol.Handlers.AcceptanceTiming
import Proofs.Vocabulary.Protocol.Handlers.Blocks
import Model.Conditions.Claim13bStepKitConfirm
import Proofs.Claims.Spec2Claims.Claim13bStepKitConfirm
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.Confirmation
import Proofs.Claims.Spec2Claims.Claim13beRoute3_5
import Proofs.Claims.Spec2Claims.Claim13beRoute3_4
import Proofs.Vocabulary.Protocol.Handlers.SGArrivalStampCarrier
import Model.Conditions.Vocabulary_Execution_W4FKChainAdvanceFold
import Proofs.Vocabulary.Protocol.Store.PublicCutSG
import Proofs.Vocabulary.Protocol.Grades.Q10Frame
import Proofs.Claims.Spec2Claims.Claim13beRoute3_53b

/-!
# Facts of the node routines

`NodeFacts` holds the facts a model `M` provides about one call of its node routines (tick, receipt,
wake, the node-state constructors) on an arbitrary input. `NodeRunFacts` holds its facts about
executions and runs of those routines.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

open DecoupledConsensusModel.Execution
open scoped DC

/-- The facts about the node routines of a model `M`, each about one call on an arbitrary input. -/
structure NodeFacts (M : Model V) : Prop where
  /-- Every outcome of `v`'s tick at `t` from `n` keeps the block shape of the tree: if every block
      of `n`'s tree other than genesis names its slot's proposer, has a parent of a strictly earlier
      slot and carries only admissible attestations, so does every such block of the outcome's tree. -/
  treeBlockShapedStep_node_tick : ∀ (S : Setup V) (v : V) (n : M.N) (t : Int)
    (out : M.N × List (NamedObject V)) (hout : M.tick S v n t ⇢ out),
    (∀ B : Block V, B ∈ n.st.core.T → B ≠ Block.genesis →
      B.proposer? = some (S.E.proposer B.slot) ∧ B.parent.slot < B.slot ∧
        M.carried_attestations_admissible S.hc B = true) →
    ∀ B : Block V, B ∈ out.1.st.core.T → B ≠ Block.genesis →
      B.proposer? = some (S.E.proposer B.slot) ∧ B.parent.slot < B.slot ∧
        M.carried_attestations_admissible S.hc B = true
  /-- Every node state `n'` that `n`'s receipt of `o` can return keeps the block shape of the tree:
      if every block of `n`'s tree other than genesis names its slot's proposer, has a parent of a
      strictly earlier slot and carries only admissible attestations, so does every such block of
      `n'`'s tree. -/
  treeBlockShapedStep_node_process : ∀ (S : Setup V) (n : M.N) (o : NamedObject V) (n' : M.N)
    (hn' : M.process S n o ⇢ n'),
    (∀ B : Block V, B ∈ n.st.core.T → B ≠ Block.genesis →
      B.proposer? = some (S.E.proposer B.slot) ∧ B.parent.slot < B.slot ∧
        M.carried_attestations_admissible S.hc B = true) →
    ∀ B : Block V, B ∈ n'.st.core.T → B ≠ Block.genesis →
      B.proposer? = some (S.E.proposer B.slot) ∧ B.parent.slot < B.slot ∧
        M.carried_attestations_admissible S.hc B = true
  /-- If the slot of `n`'s store is at or before the slot of `t`, the four clauses of `SgMono` hold
      from `n`'s store to the store of every outcome of `v`'s tick at `t` from `n`. -/
  sgMono_node_tick : ∀ (S : Setup V) (v : V) (n : M.N) (t : Int),
    n.st.core.s ≤ S.E.slotOf t → ∀ (out : M.N × List (NamedObject V)),
    M.tick S v n t ⇢ out → Restated.SgMono M S.hc n.st out.1.st
  /-- The four clauses of `SgMono` hold from the store `st` to the store the receipt of `o` returns
      on `st`. -/
  sgMono_process : ∀ (S : Setup V) (st : M.NS) (o : NamedObject V),
    Restated.SgMono M S.hc st (M.receipt_process S st o)
  /-- If `o` is a block `B` and no block `n` holds has `B`'s root unless it is `B`, then `n`'s
      receipt of `o` has some outcome `n'`. -/
  process_nonempty : ∀ (S : Setup V) (n : M.N) (o : NamedObject V)
    (hroot : ∀ B : NamedBlock V, o = NamedObject.block B →
      ∀ C ∈ n.st.bodies, C.root = B.root → C = B),
    ∃ n' : M.N, M.process S n o ⇢ n'
  /-- Two outcomes of `v`'s tick at `t` from `n` with equal node states send the same objects. -/
  tick_send_eq_of_state : ∀ (S : Setup V) (v : V) (n : M.N) (t : Time)
    (out out' : M.N × List (NamedObject V)), M.tick S v n t ⇢ out → M.tick S v n t ⇢ out' →
    out.1 = out'.1 → out.2 = out'.2
  /-- The cache of the node state `M.mkNode st rc c` is `c`. -/
  mkNode_cache : ∀ (st : M.NS) (rc : M.NR) (c : M.Cache), (M.mkNode st rc c).cache = c
  /-- If `n`'s signing record has no timeout entry at height `h` and holds the lock `T` at `h`, so
      does the signing record of every outcome of `v`'s tick at `t` from `n`. -/
  finalitySafeAt_on_tick_emit : ∀ (S : Setup V) (v : V) (n : M.N) (t : Time) {h : Height}
    {T : BlockId} (hs : n.record.legacy.timeout h = false ∧ n.record.legacy.lock h = some T)
    (out : M.N × List (NamedObject V)) (hout : M.tick S v n t ⇢ out),
    out.1.record.legacy.timeout h = false ∧ out.1.record.legacy.lock h = some T
  /-- If an outcome `out` of `v`'s tick at `t` from `n` sends an attestation `a` whose finality pair
      is `(h, T)`, the signing record of `out` has no timeout entry at height `h` and holds the lock
      `T` at `h`. -/
  on_tick_emit_finalitySafeAt_of_mem : ∀ (S : Setup V) (v : V) (n : M.N) (t : Time)
    (out : M.N × List (NamedObject V)) (hout : M.tick S v n t ⇢ out)
    {a : NamedAttestation V} (hmem : NamedObject.attest a ∈ out.2) {h : Height} {T : BlockId}
    (hfp : a.finality_pair = some ⟨h, T⟩),
    out.1.record.legacy.timeout h = false ∧ out.1.record.legacy.lock h = some T
  /-- If an outcome `out` of `v`'s tick at `t` from `n` sends an attestation `a` whose height pair
      is the timeout at `h`, the signing record of `out` holds a timeout entry at height `h`. -/
  on_tick_emit_timeout_true_of_mem : ∀ (S : Setup V) (v : V) (n : M.N) (t : Time)
    (out : M.N × List (NamedObject V)) (hout : M.tick S v n t ⇢ out)
    {a : NamedAttestation V} (hmem : NamedObject.attest a ∈ out.2) {h : Height}
    (hhp : a.erase.height_pair = HeightPair.timeout h),
    out.1.record.legacy.timeout h = true
  /-- If the named store `st` is coherent, its clock is at or before `bound`, and every named
      attestation in its rows of a round `k` has round `k` and a receipt stamp at or before `bound`,
      then the same holds of the store the receipt of `o` returns on `st`. -/
  rawRelay_process_data : ∀ (S : Setup V) (bound : Time) (st : M.NS) (o : NamedObject V),
    Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg st →
    (st.core.t ≤ bound ∧ ∀ k (a : NamedAttestation V), a ∈ st.sg_rows k →
      a.round = k ∧ ∃ stamp : Time, stamp ≤ bound ∧
        st.core.timestamp_sg_vote (M.sgVote a.erase) = some (stamp : Stamp)) →
    ((M.receipt_process S st o).core.t ≤ bound ∧
      ∀ k (a : NamedAttestation V), a ∈ (M.receipt_process S st o).sg_rows k →
        a.round = k ∧ ∃ stamp : Time, stamp ≤ bound ∧
          (M.receipt_process S st o).core.timestamp_sg_vote (M.sgVote a.erase) = some (stamp : Stamp))
  /-- If the named store `before` is coherent, so is the named store after the core call on `B`. -/
  coherent_postCore : ∀ (S : Setup V) (before : M.NS) (B : NamedBlock V),
    DecoupledConsensusModel.Sts.Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg before →
    DecoupledConsensusModel.Sts.Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg (M.postCore S before B)
  /-- If `n`'s signing record holds a timeout entry at height `h`, so does the signing record of
      every outcome of `v`'s tick at `t` from `n`. -/
  timeout_mono_on_tick_emit : ∀ (S : Setup V) (v : V) (n : M.N) (t : Time)
    {h : Height} (hs : n.record.legacy.timeout h = true)
    (out : M.N × List (NamedObject V)) (hout : M.tick S v n t ⇢ out),
    out.1.record.legacy.timeout h = true
  /-- If `n`'s signing record holds no timeout entry at height `h` and the signing record of an
      outcome `out` of `v`'s tick at `t` from `n` holds one, then `out` sends an attestation whose
      height pair is the timeout at `h`. -/
  on_tick_emit_timeout_introduced : ∀ (S : Setup V) (v : V) (n : M.N) (t : Time)
    {h : Height} (hpre : n.record.legacy.timeout h = false)
    (out : M.N × List (NamedObject V)) (hout : M.tick S v n t ⇢ out)
    (hpost : out.1.record.legacy.timeout h = true),
    ∃ a : NamedAttestation V,
      NamedObject.attest a ∈ out.2 ∧ a.erase.height_pair = HeightPair.timeout h
  /-- If `n`'s signing record holds no lock at height `h` and the signing record of an outcome `out`
      of `v`'s tick at `t` from `n` holds the lock `T` at `h`, then `out` sends an attestation whose
      finality pair is `(h, T)`. -/
  on_tick_emit_lock_introduced : ∀ (S : Setup V) (v : V) (n : M.N) (t : Time)
    {h : Height} {T : BlockId} (hpre : n.record.legacy.lock h = none)
    (out : M.N × List (NamedObject V)) (hout : M.tick S v n t ⇢ out)
    (hpost : out.1.record.legacy.lock h = some T),
    ∃ a : NamedAttestation V,
      NamedObject.attest a ∈ out.2 ∧ a.finality_pair = some ⟨h, T⟩
  /-- If `n`'s signing record holds no target at height `h` and the signing record of an outcome
      `out` of `v`'s tick at `t` from `n` holds the target `T` at `h`, then `out` sends an
      attestation whose height pair is the target `(h, T)`. -/
  on_tick_emit_target_introduced : ∀ (S : Setup V) (v : V) (n : M.N) (t : Time)
    {h : Height} {T : BlockId} (hpre : n.record.legacy.target h = none)
    (out : M.N × List (NamedObject V)) (hout : M.tick S v n t ⇢ out)
    (hpost : out.1.record.legacy.target h = some T),
    ∃ a : NamedAttestation V,
      NamedObject.attest a ∈ out.2 ∧ a.erase.height_pair = HeightPair.target h T
  /-- If every block of `n`'s tree has a chain-state height at most `n`'s `h_max`, then the `h_max`
      of every outcome of `v`'s tick at `t` from `n` is at most `n`'s `h_max` plus one. -/
  node_tick_h_max_le_succ : ∀ (S : Setup V) (v : V) (n : M.N) (t : Time)
    (hbound : ∀ B ∈ n.st.core.T, (n.st.core.σ B).h ≤ n.st.core.h_max)
    (out : M.N × List (NamedObject V)) (hout : M.tick S v n t ⇢ out),
    out.1.st.core.h_max ≤ n.st.core.h_max + 1
  /-- If every block of `n`'s tree has a chain-state height at most `n`'s `h_max`, then the `h_max`
      of every node state `n'` that `n`'s receipt of `o` can return is at most `n`'s `h_max` plus
      one. -/
  node_process_h_max_le_succ : ∀ (S : Setup V) (n : M.N) (o : NamedObject V)
    (hbound : ∀ B ∈ n.st.core.T, (n.st.core.σ B).h ≤ n.st.core.h_max)
    (n' : M.N) (hn' : M.process S n o ⇢ n'),
    n'.st.core.h_max ≤ n.st.core.h_max + 1
  /-- For every world `w'` that the event `e` can lead to from `w`, every named block validator `v`
      holds in `w` it also holds in `w'`. -/
  step_bodies_subset : ∀ (S : Setup V) (w : V → M.N) (e : Record.Event V) (v : V)
    (w' : V → M.N) (hw' : w' ∈ worldStepOf M S w e), (w v).st.bodies ⊆ (w' v).st.bodies
  /-- The `h_max` of `n`'s store is at most the `h_max` of the store of every outcome of `v`'s tick
      at `t` from `n`. -/
  tick_h_max_mono : ∀ (S : Setup V) (v : V) (n : M.N) (t : Time)
    (out : M.N × List (NamedObject V)) (hout : M.tick S v n t ⇢ out),
    n.st.core.h_max ≤ out.1.st.core.h_max
  /-- The `h_max` of `n`'s store is at most the `h_max` of the store of every node state `n'` that
      `n`'s receipt of `o` can return. -/
  process_h_max_mono : ∀ (S : Setup V) (n : M.N) (o : NamedObject V) (n' : M.N)
    (hn' : M.process S n o ⇢ n'), n.st.core.h_max ≤ n'.st.core.h_max
  /-- If every block of the tree of `n`'s core store has a chain-state height at most that store's
      `h_max`, the same holds of the core store of every outcome of `v`'s tick at `t` from `n`. -/
  tick_core_bound : ∀ (S : Setup V) (v : V) (n : M.N) (t : Time)
    (out : M.N × List (NamedObject V)) (hout : M.tick S v n t ⇢ out),
    (∀ B ∈ n.st.core.T, (n.st.core.σ B).h ≤ n.st.core.h_max) →
      ∀ B ∈ out.1.st.core.T, (out.1.st.core.σ B).h ≤ out.1.st.core.h_max
  /-- If every block of the tree of `n`'s core store has a chain-state height at most that store's
      `h_max`, the same holds of the core store of every node state `n'` that `n`'s receipt of `o`
      can return. -/
  process_core_bound : ∀ (S : Setup V) (n : M.N) (o : NamedObject V) (n' : M.N)
    (hn' : M.process S n o ⇢ n'),
    (∀ B ∈ n.st.core.T, (n.st.core.σ B).h ≤ n.st.core.h_max) →
      ∀ B ∈ n'.st.core.T, (n'.st.core.σ B).h ≤ n'.st.core.h_max
  /-- If `n`'s named store is coherent and some block of its core store's tree has a chain state
      whose justification and justification height are the store's own, the same holds of the core
      store of every outcome of `v`'s tick at `t` from `n`. -/
  tick_core_justifier : ∀ (S : Setup V) (v : V) (n : M.N) (t : Time)
    (out : M.N × List (NamedObject V)) (hout : M.tick S v n t ⇢ out),
    Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg n.st →
    (∃ D ∈ n.st.core.T, (n.st.core.σ D).J = n.st.core.J ∧ (n.st.core.σ D).h_j = n.st.core.h_j) →
      ∃ D ∈ out.1.st.core.T, (out.1.st.core.σ D).J = out.1.st.core.J ∧
        (out.1.st.core.σ D).h_j = out.1.st.core.h_j
  /-- If `n`'s named store is coherent and some block of its core store's tree has a chain state
      whose justification and justification height are the store's own, the same holds of the core
      store of every node state `n'` that `n`'s receipt of `o` can return. -/
  process_core_justifier : ∀ (S : Setup V) (n : M.N) (o : NamedObject V) (n' : M.N)
    (hn' : M.process S n o ⇢ n'),
    Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg n.st →
    (∃ D ∈ n.st.core.T, (n.st.core.σ D).J = n.st.core.J ∧ (n.st.core.σ D).h_j = n.st.core.h_j) →
      ∃ D ∈ n'.st.core.T, (n'.st.core.σ D).J = n'.st.core.J ∧ (n'.st.core.σ D).h_j = n'.st.core.h_j
  /-- If every block of the tree of `n`'s core store is genesis or was proposed by its slot's
      proposer, the same holds of the core store of every outcome of `v`'s tick at `t` from `n`. -/
  tick_proposerOk : ∀ (S : Setup V) (v : V) (n : M.N) (t : Time)
    (out : M.N × List (NamedObject V)) (hout : M.tick S v n t ⇢ out),
    (∀ B ∈ n.st.core.T, B = Block.genesis ∨ B.proposer? = some (S.E.proposer B.slot)) →
      ∀ B ∈ out.1.st.core.T, B = Block.genesis ∨ B.proposer? = some (S.E.proposer B.slot)
  /-- If every block of the tree of `n`'s core store is genesis or was proposed by its slot's
      proposer, the same holds of the core store of every node state `n'` that `n`'s receipt of `o`
      can return. -/
  process_proposerOk : ∀ (S : Setup V) (n : M.N) (o : NamedObject V) (n' : M.N)
    (hn' : M.process S n o ⇢ n'),
    (∀ B ∈ n.st.core.T, B = Block.genesis ∨ B.proposer? = some (S.E.proposer B.slot)) →
      ∀ B ∈ n'.st.core.T, B = Block.genesis ∨ B.proposer? = some (S.E.proposer B.slot)
  /-- If `n`'s signing record is lock-compatible, so is the signing record of every outcome of `v`'s
      tick at `t` from `n`. -/
  lockCompatible_on_tick_emit : ∀ (S : Setup V) (v : V) (n : M.N) (t : Time)
    (hla : Restated.Vocabulary.Proofs.Records.LockCompatible M n.record.legacy)
    (out : M.N × List (NamedObject V)) (hout : M.tick S v n t ⇢ out),
    Restated.Vocabulary.Proofs.Records.LockCompatible M out.1.record.legacy
  /-- If `n`'s signing record holds the lock `T` at height `h`, so does the signing record of every
      outcome of `v`'s tick at `t` from `n`. -/
  lock_mono_on_tick_emit : ∀ (S : Setup V) (v : V) (n : M.N) (t : Time)
    {h : Height} {T : BlockId} (hs : n.record.legacy.lock h = some T)
    (out : M.N × List (NamedObject V)) (hout : M.tick S v n t ⇢ out),
    out.1.record.legacy.lock h = some T
  /-- If `n`'s signing record holds the target `T` at height `h`, so does the signing record of
      every outcome of `v`'s tick at `t` from `n`. -/
  target_mono_on_tick_emit : ∀ (S : Setup V) (v : V) (n : M.N) (t : Time)
    {h : Height} {T : BlockId} (hs : n.record.legacy.target h = some T)
    (out : M.N × List (NamedObject V)) (hout : M.tick S v n t ⇢ out),
    out.1.record.legacy.target h = some T
  /-- If `n` runs as `v`, every attestation `a` an outcome `out` of `v`'s tick at `t` from `n` sends
      is, once erased, the attestation one call of `M.create_attestation` on `n`'s record returns,
      and `out`'s record is the record that call returns. -/
  on_tick_emit_attestation_created : ∀ (S : Setup V) (v : V) (n : M.N) (t : Time)
    (hv : M.runs_as n v)
    (out : M.N × List (NamedObject V)) (hout : M.tick S v n t ⇢ out)
    {a : NamedAttestation V} (hmem : NamedObject.attest a ∈ out.2),
    ∃ (r : Round) (confirmed : Option BlockId) (fields : Option (Height × BlockId × Bool))
      (h_j : Height) (J : BlockId) (h_F : Height),
      a.erase = (M.create_attestation n.record.legacy (S.node v).val_index r confirmed fields
          h_j J h_F).2 ∧
        out.1.record.legacy = (M.create_attestation n.record.legacy (S.node v).val_index r
          confirmed fields h_j J h_F).1
  /-- The signing record of the node state `M.mkNode st rc c` is `rc`. -/
  mkNode_record : ∀ (st : M.NS) (rc : M.NR) (c : M.Cache), (M.mkNode st rc c).record = rc
  /-- A wake changes neither the node's store nor its signing record. -/
  wake_st_record : ∀ n : M.N, (M.wake n).st = n.st ∧ (M.wake n).record = n.record
  /-- A wake keeps the grade cache. -/
  wake_cache : ∀ n : M.N, (M.wake n).cache = n.cache
  /-- Either the runs record the wakes, or `M.wake n = n` for every node state `n`. -/
  wake_events_or_id : M.wakeEvents = true ∨ ∀ n : M.N, M.wake n = n
  /-- Waking a node state twice gives the node state that waking it once gives. -/
  wake_idem : ∀ n : M.N, M.wake (M.wake n) = M.wake n
  /-- The named store of every initial node state satisfies the confirmation-membership invariant,
      and its named signing record satisfies the tick record invariant. -/
  initial_invariants : ∀ (S : Setup V) (v : V),
    Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant M S.E S.cfg (M.initial S v).st ∧
      Restated.Vocabulary.Proofs.NamedTickRecord.Invariant M (M.initial S v).record
  /-- If the named store of `n` satisfies the confirmation-membership invariant, so does the named
      store of every outcome of `v`'s tick at `t` from `n`. -/
  confirmation_invariant_tick : ∀ (S : Setup V) (v : V) (n : M.N) (t : Time)
    (h : Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant M S.E S.cfg n.st)
    (out : M.N × List (NamedObject V)) (hout : M.tick S v n t ⇢ out),
    Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant M S.E S.cfg out.1.st
  /-- If the named signing record of `n` satisfies the tick record invariant, so does the named
      signing record of every outcome of `v`'s tick at `t` from `n`. -/
  record_invariant_tick : ∀ (S : Setup V) (v : V) (n : M.N) (t : Time)
    (h : Restated.Vocabulary.Proofs.NamedTickRecord.Invariant M n.record)
    (out : M.N × List (NamedObject V)) (hout : M.tick S v n t ⇢ out),
    Restated.Vocabulary.Proofs.NamedTickRecord.Invariant M out.1.record
  /-- If `n`'s named store satisfies the confirmation-membership invariant and its named signing
      record the tick record invariant, the same holds of every node state `n'` that `n`'s receipt
      of `o` can return. -/
  invariants_process : ∀ (S : Setup V) (n : M.N) (o : NamedObject V)
    (hStore : Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant M S.E S.cfg n.st)
    (hRecord : Restated.Vocabulary.Proofs.NamedTickRecord.Invariant M n.record)
    (n' : M.N) (hn' : M.process S n o ⇢ n'),
    Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant M S.E S.cfg n'.st ∧
      Restated.Vocabulary.Proofs.NamedTickRecord.Invariant M n'.record
  /-- The named store of `M.mkNode st rc c` is `st` with the grade cache `c` written in. -/
  mkNode_st : ∀ (st : M.NS) (rc : M.NR) (c : M.Cache),
    (M.mkNode st rc c).st = M.store_with_cache st c
  /-- Writing a cache into a named store keeps its bodies. -/
  store_with_cache_bodies : ∀ (st : M.NS) (c : M.Cache),
    (M.store_with_cache st c).bodies = st.bodies
  /-- Writing a cache into a named store keeps its attestation rows of every round. -/
  store_with_cache_sg_rows : ∀ (st : M.NS) (c : M.Cache) (r : Round),
    (M.store_with_cache st c).sg_rows r = st.sg_rows r
  /-- Writing a grade cache into a named store keeps its core store's `T`. -/
  store_with_cache_core_T : ∀ (st : M.NS) (c : M.Cache),
    (M.store_with_cache st c).core.T = st.core.T
  /-- Writing a grade cache into a named store keeps its core store's `F`. -/
  store_with_cache_core_F : ∀ (st : M.NS) (c : M.Cache),
    (M.store_with_cache st c).core.F = st.core.F
  /-- Writing a grade cache into a named store keeps its core store's `J`. -/
  store_with_cache_core_J : ∀ (st : M.NS) (c : M.Cache),
    (M.store_with_cache st c).core.J = st.core.J
  /-- Writing a grade cache into a named store keeps its core store's `s`. -/
  store_with_cache_core_s : ∀ (st : M.NS) (c : M.Cache),
    (M.store_with_cache st c).core.s = st.core.s
  /-- Writing a grade cache into a named store keeps its core store's `t`. -/
  store_with_cache_core_t : ∀ (st : M.NS) (c : M.Cache),
    (M.store_with_cache st c).core.t = st.core.t
  /-- Writing a grade cache into a named store keeps its core store's `h_max`. -/
  store_with_cache_core_h_max : ∀ (st : M.NS) (c : M.Cache),
    (M.store_with_cache st c).core.h_max = st.core.h_max
  /-- Writing a grade cache into a named store keeps its core store's `h_j`. -/
  store_with_cache_core_h_j : ∀ (st : M.NS) (c : M.Cache),
    (M.store_with_cache st c).core.h_j = st.core.h_j
  /-- Writing a grade cache into a named store keeps its core store's `σ`. -/
  store_with_cache_core_σ : ∀ (st : M.NS) (c : M.Cache),
    (M.store_with_cache st c).core.σ = st.core.σ
  /-- Writing a grade cache into a named store keeps its core store's `timestamp_block`. -/
  store_with_cache_core_timestamp_block : ∀ (st : M.NS) (c : M.Cache),
    (M.store_with_cache st c).core.timestamp_block = st.core.timestamp_block
  /-- Writing a grade cache into a named store keeps its core store's `timestamp_vote`. -/
  store_with_cache_core_timestamp_vote : ∀ (st : M.NS) (c : M.Cache),
    (M.store_with_cache st c).core.timestamp_vote = st.core.timestamp_vote
  /-- Writing a grade cache into a named store keeps its core store's `timestamp_sg_vote`. -/
  store_with_cache_core_timestamp_sg_vote : ∀ (st : M.NS) (c : M.Cache),
    (M.store_with_cache st c).core.timestamp_sg_vote = st.core.timestamp_sg_vote
  /-- Writing a grade cache into a named store keeps its core store's `gf_votes`. -/
  store_with_cache_core_gf_votes : ∀ (st : M.NS) (c : M.Cache),
    (M.store_with_cache st c).core.gf_votes = st.core.gf_votes
  /-- Writing a grade cache into a named store keeps its core store's `pool`. -/
  store_with_cache_core_pool : ∀ (st : M.NS) (c : M.Cache),
    (M.store_with_cache st c).core.pool = st.core.pool
  /-- Writing a grade cache into a named store keeps its core store's `live_confirmed`. -/
  store_with_cache_core_live_confirmed : ∀ (st : M.NS) (c : M.Cache),
    (M.store_with_cache st c).core.live_confirmed = st.core.live_confirmed
  /-- Writing a grade cache into a named store keeps its core store's `latest_confirmed`. -/
  store_with_cache_core_latest_confirmed : ∀ (st : M.NS) (c : M.Cache),
    (M.store_with_cache st c).core.latest_confirmed = st.core.latest_confirmed
  /-- Writing a grade cache into a named store keeps its core store's `latest_stable`. -/
  store_with_cache_core_latest_stable : ∀ (st : M.NS) (c : M.Cache),
    (M.store_with_cache st c).core.latest_stable = st.core.latest_stable
  /-- Writing a grade cache into a named store keeps its core store's `sg_votes`. -/
  store_with_cache_core_sg_votes : ∀ (st : M.NS) (c : M.Cache),
    (M.store_with_cache st c).core.sg_votes = st.core.sg_votes
  /-- Writing a grade cache into a named store keeps its core store's attestation sets
      `M.store_sg_pool`. -/
  store_with_cache_core_sg_pool : ∀ (st : M.NS) (c : M.Cache),
    M.store_sg_pool (M.store_with_cache st c).core = M.store_sg_pool st.core
  /-- Writing a grade cache into a named store keeps its core store's `tau`. -/
  store_with_cache_core_tau : ∀ (st : M.NS) (c : M.Cache),
    (M.store_with_cache st c).core.tau = st.core.tau
  /-- Writing a grade cache into a named store keeps its core store's attestations
      `M.store_attestations`. -/
  store_with_cache_core_attestations : ∀ (st : M.NS) (c : M.Cache),
    M.store_attestations (M.store_with_cache st c).core = M.store_attestations st.core
  /-- `M.get_fg_root` gives the same block on the core store of `M.store_with_cache st c` as on
      `st`'s core store. -/
  store_with_cache_get_fg_root : ∀ (st : M.NS) (c : M.Cache),
    M.get_fg_root (M.toHealing (M.store_with_cache st c).core).toFG =
      M.get_fg_root (M.toHealing st.core).toFG
  /-- `M.get_filtered_block_tree` gives the same tree on the core store of `M.store_with_cache st c`
      as on `st`'s core store. -/
  store_with_cache_get_filtered_block_tree : ∀ (st : M.NS) (c : M.Cache),
    M.get_filtered_block_tree (M.toHealing (M.store_with_cache st c).core).toFG =
      M.get_filtered_block_tree (M.toHealing st.core).toFG
  /-- `M.voter_filtered_block_tree` gives the same tree on the core store of
      `M.store_with_cache st c` as on `st`'s core store. -/
  store_with_cache_voter_filtered_block_tree : ∀ (st : M.NS) (c : M.Cache) (E : DecoupledConsensusModel.Env V) (s : DecoupledConsensusModel.Slot),
    M.voter_filtered_block_tree E (M.store_with_cache st c).core s =
      M.voter_filtered_block_tree E st.core s
  /-- `M.voter_processed_block_tree` gives the same tree on the core store of
      `M.store_with_cache st c` as on `st`'s core store. -/
  store_with_cache_voter_processed_block_tree : ∀ (st : M.NS) (c : M.Cache) (E : DecoupledConsensusModel.Env V) (s : DecoupledConsensusModel.Slot),
    M.voter_processed_block_tree E (M.toHealing (M.store_with_cache st c).core).toFG.toSG.toGoldfishStore s =
      M.voter_processed_block_tree E (M.toHealing st.core).toFG.toSG.toGoldfishStore s
  /-- `M.voter_view` gives the same view on the core store of `M.store_with_cache st c` as on `st`'s
      core store. -/
  store_with_cache_voter_view : ∀ (st : M.NS) (c : M.Cache) (E : DecoupledConsensusModel.Env V) (s : DecoupledConsensusModel.Slot),
    M.voter_view E (M.toHealing (M.store_with_cache st c).core).toFG.toSG.toGoldfishStore s =
      M.voter_view E (M.toHealing st.core).toFG.toSG.toGoldfishStore s
  /-- `M.voter_support_view` gives the same view on the core store of `M.store_with_cache st c` as
      on `st`'s core store. -/
  store_with_cache_voter_support_view : ∀ (st : M.NS) (c : M.Cache) (E : DecoupledConsensusModel.Env V) (s : DecoupledConsensusModel.Slot),
    M.voter_support_view E (M.toHealing (M.store_with_cache st c).core).toFG.toSG.toGoldfishStore s =
      M.voter_support_view E (M.toHealing st.core).toFG.toSG.toGoldfishStore s
  /-- `M.proposer_view` gives the same view on the core store of `M.store_with_cache st c` as on
      `st`'s core store. -/
  store_with_cache_proposer_view : ∀ (st : M.NS) (c : M.Cache) (s : DecoupledConsensusModel.Slot),
    M.proposer_view (M.toHealing (M.store_with_cache st c).core).toFG.toSG.toGoldfishStore s =
      M.proposer_view (M.toHealing st.core).toFG.toSG.toGoldfishStore s
  /-- `M.proposer_support_view` gives the same view on the core store of `M.store_with_cache st c`
      as on `st`'s core store. -/
  store_with_cache_proposer_support_view : ∀ (st : M.NS) (c : M.Cache) (s : DecoupledConsensusModel.Slot),
    M.proposer_support_view (M.toHealing (M.store_with_cache st c).core).toFG.toSG.toGoldfishStore s =
      M.proposer_support_view (M.toHealing st.core).toFG.toSG.toGoldfishStore s
  /-- `M.get_head_in_tree_with_layer` gives the same result on the core store of
      `M.store_with_cache st c` as on `st`'s core store. -/
  store_with_cache_get_head_in_tree_with_layer : ∀ (st : M.NS) (c : M.Cache) (k : M.Contract) (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig) (T : Finset (Block V)) (W U : Finset (DecoupledConsensusModel.GoldfishVote V)) (s : DecoupledConsensusModel.Slot),
    M.get_head_in_tree_with_layer k E hc (M.toHealing (M.store_with_cache st c).core) T W U s =
      M.get_head_in_tree_with_layer k E hc (M.toHealing st.core) T W U s
  /-- `M.get_head_in_tree_with` gives the same result on the core store of `M.store_with_cache st c`
      as on `st`'s core store. -/
  store_with_cache_get_head_in_tree_with : ∀ (st : M.NS) (c : M.Cache) (k : M.Contract) (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig) (T : Finset (Block V)) (W U : Finset (DecoupledConsensusModel.GoldfishVote V)) (s : DecoupledConsensusModel.Slot),
    M.get_head_in_tree_with k E hc (M.store_with_cache st c).core T W U s =
      M.get_head_in_tree_with k E hc st.core T W U s
  /-- `M.grade2_block_with` gives the same result on the core store of `M.store_with_cache st c` as
      on `st`'s core store. -/
  store_with_cache_grade2_block_with : ∀ (st : M.NS) (c : M.Cache) (k : M.Contract) (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig) (r : DecoupledConsensusModel.Round),
    M.grade2_block_with k E hc (M.toHealing (M.store_with_cache st c).core) r =
      M.grade2_block_with k E hc (M.toHealing st.core) r
  /-- `M.get_sg_vote_with` gives the same result on the core store of `M.store_with_cache st c` as
      on `st`'s core store. -/
  store_with_cache_get_sg_vote_with : ∀ (st : M.NS) (c : M.Cache) (k : M.Contract) (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig) (r : DecoupledConsensusModel.Round) (o : Option (Block V)),
    M.get_sg_vote_with k E hc (M.toHealing (M.store_with_cache st c).core) r o =
      M.get_sg_vote_with k E hc (M.toHealing st.core) r o
  /-- `M.onPhaseTick` gives the same result on the core store of `M.store_with_cache st c` as on
      `st`'s core store. -/
  store_with_cache_onPhaseTick : ∀ (st : M.NS) (c : M.Cache) (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig) (t : DecoupledConsensusModel.Time) (c' : M.Cache),
    M.onPhaseTick E hc (M.toHealing (M.store_with_cache st c).core) t c' =
      M.onPhaseTick E hc (M.toHealing st.core) t c'
  /-- `M.readFrame` gives the same result on the core store of `M.store_with_cache st c` as on
      `st`'s core store. -/
  store_with_cache_readFrame : ∀ (st : M.NS) (c : M.Cache) (c' : M.Cache) (r : DecoupledConsensusModel.Round),
    M.readFrame c' (M.toHealing (M.store_with_cache st c).core) r =
      M.readFrame c' (M.toHealing st.core) r
  /-- `M.frameGradeRead` gives the same result on the core store of `M.store_with_cache st c` as on
      `st`'s core store. -/
  store_with_cache_frameGradeRead : ∀ (st : M.NS) (c : M.Cache) (c' : M.Cache) (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig) (r : DecoupledConsensusModel.Round),
    M.frameGradeRead c' E hc (M.toHealing (M.store_with_cache st c).core) r =
      M.frameGradeRead c' E hc (M.toHealing st.core) r
  /-- `M.currentSGVote` gives the same result on the core store of `M.store_with_cache st c` as on
      `st`'s core store. -/
  store_with_cache_currentSGVote : ∀ (st : M.NS) (c : M.Cache) (g : DecoupledConsensusModel.Protocol.GradeRead V),
    M.currentSGVote (M.toHealing (M.store_with_cache st c).core) g =
      M.currentSGVote (M.toHealing st.core) g
  /-- `M.inWindow` gives the same result on the core store of `M.store_with_cache st c` as on `st`'s
      core store. -/
  store_with_cache_inWindow : ∀ (st : M.NS) (c : M.Cache) (hc : DecoupledConsensusModel.Protocol.HealConfig) (r : DecoupledConsensusModel.Round),
    M.inWindow hc (M.store_with_cache st c).core r =
      M.inWindow hc st.core r
  /-- `M.store_pool` gives the same votes on the core store of `M.store_with_cache st c` as on
      `st`'s core store. -/
  store_with_cache_store_pool : ∀ (st : M.NS) (c : M.Cache) (s : DecoupledConsensusModel.Slot),
    M.store_pool (M.store_with_cache st c).core s =
      M.store_pool st.core s
  /-- `M.gradeView` gives the same result on the core store of `M.store_with_cache st c` as on
      `st`'s core store. -/
  store_with_cache_gradeView : ∀ (st : M.NS) (c : M.Cache),
    M.gradeView (M.toHealing (M.store_with_cache st c).core) =
      M.gradeView (M.toHealing st.core)
  /-- Every validator's initial node state is one a run reaches. -/
  reachedNode_initial : ∀ (S : Setup V) (v : V), M.reachedNode (M.initial S v)
  /-- If `n` is a node state a run reaches, so is `M.wake n`. -/
  reachedNode_wake : ∀ (n : M.N), M.reachedNode n → M.reachedNode (M.wake n)
  /-- If `n` runs as `v`, so does `M.wake n`. -/
  runs_as_wake : ∀ (n : M.N) (v : V), M.runs_as n v → M.runs_as (M.wake n) v
  /-- If `n` is a node state a run reaches, so is the node state of every outcome of `v`'s tick at
      `t` from `n`. -/
  reachedNode_tick : ∀ (S : Setup V) (v : V) (n : M.N) (t : Time) (out : M.N × List (NamedObject V)),
    M.tick S v n t ⇢ out → M.reachedNode n → M.reachedNode out.1
  /-- If `n` is a node state a run reaches, so is every node state `n'` that `n`'s receipt of `o`
      can return. -/
  reachedNode_process : ∀ (S : Setup V) (n : M.N) (o : NamedObject V) (n' : M.N),
    M.process S n o ⇢ n' → M.reachedNode n → M.reachedNode n'
  /-- If `n` is a node state a run reaches and `c` is an outcome of `M.onPhaseTick` at `t` from
      `n`'s store and cache, then `M.mkNode (M.ns_setClock E n.st t) n.record c` is a node state a
      run reaches. -/
  reachedNode_confirmationRead : ∀ (E : DecoupledConsensusModel.Env V)
    (hc : DecoupledConsensusModel.Protocol.HealConfig) (n : M.N) (t : DecoupledConsensusModel.Time)
    (c : M.Cache),
    M.onPhaseTick E hc n.st.core.toHealing t n.cache ⇢ c → M.reachedNode n →
    M.reachedNode (M.mkNode (M.ns_setClock E n.st t) n.record c)
  /-- If `n` is a node state a run reaches, `c` is an outcome of `M.onPhaseTick` at `t` from `n`'s
      store and cache, and `st` is an outcome of the confirmation duty with the contract
      `M.gradeContract c` on `n`'s store with its clock set to `t`, at the slot before `t`'s slot,
      then `M.mkNode st n.record c` is a node state a run reaches. -/
  reachedNode_confirmationDuty : ∀ (E : DecoupledConsensusModel.Env V)
    (hc : DecoupledConsensusModel.Protocol.HealConfig) (n : M.N) (t : DecoupledConsensusModel.Time)
    (c : M.Cache) (st : M.NS),
    M.onPhaseTick E hc n.st.core.toHealing t n.cache ⇢ c →
    M.duties_update_confirmation_with (M.gradeContract c) E hc (M.ns_setClock E n.st t)
      (E.slotOf t - 1) ⇢ st →
    M.reachedNode n → M.reachedNode (M.mkNode st n.record c)
  /-- The named store of a node state a run reaches is a store a run reaches. -/
  reachedStore_of_node : ∀ (n : M.N), M.reachedNode n → M.reachedStore n.st
  /-- The core store of a named store a run reaches is a store a run reaches. -/
  reachedCore_of_store : ∀ (st : M.NS), M.reachedStore st → M.reachedCore st.core
  /-- The core store, read as a healing store, and the grade cache of a node state a run reaches are
      a pair a run reaches. -/
  reachedRead_of_node : ∀ (n : M.N), M.reachedNode n → M.reachedRead n.st.core.toHealing n.cache
  /-- If every Goldfish vote of `n`'s core store at every slot `k` is signed by a member of
      `S.E.committee k`, the same holds of every node state `n'` that `n`'s receipt of `o` can
      return. -/
  committeePools_process : ∀ (S : Setup V) (n : M.N) (o : NamedObject V) (n' : M.N), M.process S n o ⇢ n' → (∀ (k : Slot) (u : GoldfishVote V), u ∈ n.st.core.gf_votes k → u.val_index ∈ S.E.committee k) → ∀ (k : Slot) (u : GoldfishVote V), u ∈ n'.st.core.gf_votes k → u.val_index ∈ S.E.committee k
  /-- For every node state `n'` that `n`'s receipt of `o` can return, the round-`r` attestations in
      `M.store_sg_pool` of `n`'s core store are in that of `n'`'s core store. -/
  sg_pool_subset_process : ∀ (S : Setup V) (n : M.N) (o : NamedObject V) (r : Round)
    (n' : M.N) (hn' : M.process S n o ⇢ n'),
    M.store_sg_pool n.st.core r ⊆ M.store_sg_pool n'.st.core r
  /-- For every outcome `out` of `v`'s tick at `t` from `n`, the round-`r` attestations in
      `M.store_sg_pool` of `n`'s core store are in that of `out.1`'s core store. -/
  sg_pool_subset_on_tick_emit : ∀ (S : Setup V) (v : V) (n : M.N) (t : Time) (r : Round)
    (out : M.N × List (NamedObject V)) (hout : M.tick S v n t ⇢ out),
    M.store_sg_pool n.st.core r ⊆ M.store_sg_pool out.1.st.core r
  /-- For every outcome `out` of `v`'s tick at `t` from `n` and every outcome `c` of `M.onPhaseTick`
      at `t` from `n`'s core store and cache, the grade cache of `out.1` is `c` clipped at the
      finalized block of `out.1`'s core store; the hypothesis `hn` says `n` is a node state a run
      reaches. -/
  tick_cache_eq : ∀ (S : Setup V) (v : V) (n : M.N) (t : Time)
    (out : M.N × List (NamedObject V)) (hout : M.tick S v n t ⇢ out)
    (c : M.Cache) (hcache : M.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache ⇢ c)
    (hn : M.reachedNode n := by trivial),
    out.1.cache = M.clipCache out.1.st.core.F c
  /-- For every outcome `out` of `v`'s tick at `t` from `n`, the round of `out.1`'s grade cache is
      the round of the slot of `t`. -/
  tick_cache_round : ∀ (S : Setup V) (v : V) (n : M.N) (t : Time)
    (out : M.N × List (NamedObject V)) (hout : M.tick S v n t ⇢ out),
    out.1.cache.round = M.round_of S.hc (S.E.slotOf t)
  /-- For every node state `n'` that `n`'s receipt of `o` can return, the grade cache of `n'` is
      `n`'s grade cache clipped at the finalized block of `n'`'s core store; the hypothesis `hn`
      says `n` is a node state a run reaches. -/
  process_cache_eq : ∀ (S : Setup V) (n : M.N) (o : NamedObject V) (n' : M.N)
    (hn' : M.process S n o ⇢ n') (hn : M.reachedNode n := by trivial), n'.cache = M.clipCache n'.st.core.F n.cache
  /-- The grade cache of every initial node state is unchanged by clipping it at the finalized block
      of its core store. -/
  cache_clipped_initial : ∀ (S : Setup V) (v : V),
    M.clipCache (M.initial S v).st.core.F (M.initial S v).cache = (M.initial S v).cache
  /-- For every outcome `out` of `v`'s tick at `t` from `n`, `out.1`'s grade cache is unchanged by
      clipping it at the finalized block of `out.1`'s core store. -/
  cache_clipped_tick : ∀ (S : Setup V) (v : V) (n : M.N) (t : Time)
    (out : M.N × List (NamedObject V)) (hout : M.tick S v n t ⇢ out),
    M.clipCache out.1.st.core.F out.1.cache = out.1.cache
  /-- For every node state `n'` that `n`'s receipt of `o` can return, `n'`'s grade cache is
      unchanged by clipping it at the finalized block of `n'`'s core store. -/
  cache_clipped_process : ∀ (S : Setup V) (n : M.N) (o : NamedObject V) (n' : M.N)
    (hn' : M.process S n o ⇢ n'), M.clipCache n'.st.core.F n'.cache = n'.cache
  /-- Every phase result of the current frame of an initial node state's grade cache is present and
      holds no block. -/
  initial_cache_current_phase : ∀ (S : Setup V) (v : V) (p : DecoupledConsensusModel.Protocol.Phase), M.phaseResult (M.initial S v).cache.current p = Option.some Option.none
  /-- Processing the Goldfish vote `u` at the store `st` replaces `st`'s core store by the one
      `M.on_goldfish_vote_checked` returns and keeps the rest of `st`. -/
  process_gfVote : ∀ (S : DecoupledConsensusModel.Execution.Setup V) (st : M.NS) (u : DecoupledConsensusModel.GoldfishVote V), M.receipt_process S st (DecoupledConsensusModel.Execution.NamedObject.gfVote u) = M.ns_with_core st (M.on_goldfish_vote_checked S.E st.core u)
  /-- For every outcome `g` of `M.frameGradeRead c` at `st` and `r`, every outcome of the grade-2
      block read through `M.gradeContract c` at `st` and `r` is the grade-2 candidate of `g`. -/
  gradeContract_grade2_block_with : ∀ (c : M.Cache) (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig) (st : M.HS) (r : DecoupledConsensusModel.Round)
    (g : DecoupledConsensusModel.Protocol.GradeRead V), M.frameGradeRead c E hc st r ⇢ g →
    ∀ x : Option (Block V), M.grade2_block_with (M.gradeContract c) E hc st r ⇢ x → x = g.Q2
  /-- The grade read of `M.gradeContract c` can return `g` at a store and a round exactly when
      `M.frameGradeRead c` can return `g` there. -/
  gradeContract_read : ∀ (c : M.Cache) (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig) (st : M.HS) (r : DecoupledConsensusModel.Round)
    (g : DecoupledConsensusModel.Protocol.GradeRead V), (M.gradeContract c).read E hc st r ⇢ g ↔ M.frameGradeRead c E hc st r ⇢ g
  /-- The SG vote of `M.gradeContract c` is `M.currentSGVote`. -/
  gradeContract_sgVote : ∀ (c : M.Cache), (M.gradeContract c).sgVote = M.currentSGVote
  /-- A node's receipt of an object is the same at the setup `S` and at `setupWithGST S g hg`, the
      setup `S` with its GST replaced by `g`. -/
  namedNodeProcess_setupWithGST : ∀ (S : DecoupledConsensusModel.Execution.Setup V) (g : ℤ) (hg : 0 ≤ g) (n : M.N) (o : DecoupledConsensusModel.Execution.NamedObject V), M.process (DecoupledConsensusModel.Sts.setupWithGST S g hg) n o = M.process S n o
  /-- A node's tick is the same at the setup `S` and at `setupWithGST S g hg`, the setup `S` with
      its GST replaced by `g`. -/
  namedNodeTick_setupWithGST : ∀ (S : DecoupledConsensusModel.Execution.Setup V) (g : ℤ) (hg : 0 ≤ g) (v : V) (n : M.N) (t : ℤ), M.tick (DecoupledConsensusModel.Sts.setupWithGST S g hg) v n t = M.tick S v n t
  /-- Every outcome of the proposal duty under the contract `gc` at the store `st` is either `st`
      and no block, or some block `B` with the store the receipt of `B` gives at `st`, in both cases
      with the cache `M.contractCache gc` written in; the hypothesis `hn` says `st` is a store a run
      reaches. -/
  named_propose_cases : ∀ (S : DecoupledConsensusModel.Execution.Setup V) (gc : M.Contract) (nd : DecoupledConsensusModel.Protocol.Node V) (st : M.NS)
    (out : M.NS × Option (NamedBlock V)), M.duties_propose_block_with gc S.E S.hc S.cfg nd st ⇢ out →
    ∀ (hn : M.reachedStore st := by trivial),
    out = (M.store_with_cache st (M.contractCache gc), Option.none) ∨ ∃ B, out = (M.store_with_cache (M.receipt_process S st (DecoupledConsensusModel.Execution.NamedObject.block B)) (M.contractCache gc), Option.some B)
  /-- Every outcome of the Goldfish vote duty under the contract `gc` at the store `st` is either
      `st` and no vote, or some vote `u` with the store the receipt of `u` gives at `st`, in both
      cases with the cache `M.contractCache gc` written in; the hypothesis `hn` says `st` is a store
      a run reaches. -/
  named_vote_cases : ∀ (S : DecoupledConsensusModel.Execution.Setup V) (gc : M.Contract) (nd : DecoupledConsensusModel.Protocol.Node V) (st : M.NS)
    (out : M.NS × Option (GoldfishVote V)), M.duties_goldfish_vote_with gc S.E S.hc nd st ⇢ out →
    ∀ (hn : M.reachedStore st := by trivial),
    out = (M.store_with_cache st (M.contractCache gc), Option.none) ∨ ∃ u, out = (M.store_with_cache (M.receipt_process S st (DecoupledConsensusModel.Execution.NamedObject.gfVote u)) (M.contractCache gc), Option.some u)
  /-- Delivering a Goldfish vote that the core store of `st` already holds for the vote's slot
      leaves `st` unchanged. -/
  process_gfVote_of_mem_pool : ∀ (S : DecoupledConsensusModel.Execution.Setup V) (st : M.NS) (u : DecoupledConsensusModel.GoldfishVote V), u ∈ st.core.pool u.slot → M.receipt_process S st (DecoupledConsensusModel.Execution.NamedObject.gfVote u) = st
  /-- If the receipt of `o` leaves `n`'s store unchanged and `n`'s cache is already clipped at that
      store's finalized block, every node state the receipt can return is `n`; the hypothesis `hn`
      says `n` is a node state a run reaches. -/
  process_node_of_store_id : ∀ (S : DecoupledConsensusModel.Execution.Setup V) (n : M.N) (o : DecoupledConsensusModel.Execution.NamedObject V), M.receipt_process S n.st o = n.st → M.clipCache n.st.core.F n.cache = n.cache → ∀ (n' : M.N), M.process S n o ⇢ n' → ∀ (hn : M.reachedNode n := by trivial), n' = n
  /-- For every outcome `g` of the grade read of `M.gradeContract c` at `st` and `r`, and every
      outcome `x` of the grade-2 block of the round-`r` frame read from `c` at `st`, the grade-2
      candidate of `g` is `x`. -/
  ModelProperties_gradeContract_read_Q2 : ∀ (c : M.Cache) (E : Env V) (hc : Protocol.HealConfig)
    (st : M.HS) (r : Round),
    ∀ g : DecoupledConsensusModel.Protocol.GradeRead V, (M.gradeContract c).read E hc st r ⇢ g →
    ∀ x : Option (Block V), M.grade2Block st (M.readFrame c st r) ⇢ x →
    g.Q2 = x
  /-- For every outcome `g` of the grade read of `M.gradeContract c` at `st` and `r`, and every
      outcome `a` of `M.anchor` at the grade-1 result of the round-`r` frame read from `c` at `st`,
      the anchor of `g` is `a`. -/
  ModelProperties_gradeContract_read_anchor : ∀ (c : M.Cache) (E : Env V)
    (hc : Protocol.HealConfig) (st : M.HS) (r : Round),
    ∀ g : DecoupledConsensusModel.Protocol.GradeRead V, (M.gradeContract c).read E hc st r ⇢ g →
    ∀ a : Block V, M.anchor E hc st r (M.readFrame c st r).g1 ⇢ a →
    g.anchor = a
  /-- The grade cache of every initial node state is at round `0`. -/
  initial_cache_round : ∀ (S : Setup V) (v : V), (M.initial S v).cache.round = 0
  /-- The signing record of every initial node state holds no lock at any height. -/
  initial_record_legacy_lock : ∀ (S : Setup V) (v : V) (H : Height), (M.initial S v).record.legacy.lock H = none
  /-- The signing record of every initial node state holds no target at any height. -/
  initial_record_legacy_target : ∀ (S : Setup V) (v : V) (h : Height), (M.initial S v).record.legacy.target h = none
  /-- The signing record of every initial node state holds no timeout entry at any height. -/
  initial_record_legacy_timeout : ∀ (S : Setup V) (v : V) (h : Height),
    (M.initial S v).record.legacy.timeout h = false
  /-- The store of every initial node state is the initial named store `M.ns_initial`. -/
  initial_st : ∀ (S : Setup V) (v : V), (M.initial S v).st = M.ns_initial
  /-- If `B` is not among the bodies of `before` but is among the bodies after the core call on `B`,
      the block handler on `B` at `before` returns the store that admitting `B`'s attestations
      returns, started from the store after the core call. -/
  on_block_with_eq_admit_rows_postCore : ∀ (S : Setup V) (before : M.NS) (B : NamedBlock V)
    (hnew : B ∉ before.bodies) (hheld : B ∈ (M.postCore S before B).bodies),
    M.on_block_with .alsoCarried S.E S.hc S.cfg before B =
      M.admit_rows S.hc (M.postCore S before B) B.attestations
  /-- Unless `B` is not among the bodies of `before` but is among the bodies after the core call on
      `B`, the block handler on `B` at `before` returns the store after the core call. -/
  on_block_with_eq_postCore_of_not_new : ∀ (S : Setup V) (before : M.NS) (B : NamedBlock V)
    (h : ¬ (B ∉ before.bodies ∧ B ∈ (M.postCore S before B).bodies)),
    M.on_block_with .alsoCarried S.E S.hc S.cfg before B = M.postCore S before B
  /-- If the erasure of `B` is already in the block tree of `before`, the core call on `B` keeps the
      bodies of `before`. -/
  postCore_bodies_of_erase_mem : ∀ (S : Setup V) (before : M.NS) (B : NamedBlock V)
    (h : B.erase ∈ before.core.T), (M.postCore S before B).bodies = before.bodies
  /-- The core call keeps the clock `t` and the slot `s` of the core store. -/
  postCore_clock : ∀ (S : Setup V) (before : M.NS) (B : NamedBlock V),
    (M.postCore S before B).core.t = before.core.t ∧
      (M.postCore S before B).core.s = before.core.s
  /-- Processing the attestation `a` at the store `st` gives the store `M.admit_row` returns. -/
  process_attest : ∀ (S : Setup V) (st : M.NS) (a : NamedAttestation V),
    M.receipt_process S st (.attest a) = M.admit_row S.hc st a
  /-- Processing the block `B` at the store `st` gives the store the block handler `M.on_block_with`
      returns, admitting the attestations `B` includes. -/
  process_block : ∀ (S : Setup V) (st : M.NS) (B : NamedBlock V),
    M.receipt_process S st (.block B) = M.on_block_with .alsoCarried S.E S.hc S.cfg st B
  /-- For every node state `n'` that `n`'s receipt of `o` can return, the store of `n'` is the store
      `M.receipt_process` returns on `n`'s store and `o`, with its saved grades made compatible with
      its finalized block. -/
  process_st : ∀ (S : Setup V) (n : M.N) (o : NamedObject V) (n' : M.N)
    (hn' : M.process S n o ⇢ n'),
    n'.st = M.make_grades_compatible_with_finalized (M.receipt_process S n.st o)
  /-- Making the saved grades compatible with the finalized block keeps the named blocks. -/
  make_grades_compatible_with_finalized_bodies : ∀ (ns : M.NS),
    (M.make_grades_compatible_with_finalized ns).bodies = ns.bodies
  /-- Making the saved grades compatible with the finalized block keeps the named attestation rows. -/
  make_grades_compatible_with_finalized_sg_rows : ∀ (ns : M.NS),
    (M.make_grades_compatible_with_finalized ns).sg_rows = ns.sg_rows
  /-- Making the saved grades compatible with the finalized block keeps the clock of the core store. -/
  make_grades_compatible_with_finalized_core_t : ∀ (ns : M.NS),
    (M.make_grades_compatible_with_finalized ns).core.t = ns.core.t
  /-- Making the saved grades compatible with the finalized block keeps the slot of the core store. -/
  make_grades_compatible_with_finalized_core_s : ∀ (ns : M.NS),
    (M.make_grades_compatible_with_finalized ns).core.s = ns.core.s
  /-- Making the saved grades compatible with the finalized block keeps the block tree of the core
      store. -/
  make_grades_compatible_with_finalized_core_T : ∀ (ns : M.NS),
    (M.make_grades_compatible_with_finalized ns).core.T = ns.core.T
  /-- Making the saved grades compatible with the finalized block keeps the finalized block of the
      core store. -/
  make_grades_compatible_with_finalized_core_F : ∀ (ns : M.NS),
    (M.make_grades_compatible_with_finalized ns).core.F = ns.core.F
  /-- Making the saved grades compatible with the finalized block keeps the Goldfish votes of the
      core store. -/
  make_grades_compatible_with_finalized_core_gf_votes : ∀ (ns : M.NS),
    (M.make_grades_compatible_with_finalized ns).core.gf_votes = ns.core.gf_votes
  /-- Making the saved grades compatible with the finalized block keeps the Goldfish vote stamps of
      the core store. -/
  make_grades_compatible_with_finalized_core_timestamp_vote : ∀ (ns : M.NS),
    (M.make_grades_compatible_with_finalized ns).core.timestamp_vote = ns.core.timestamp_vote
  /-- Making the saved grades compatible with the finalized block keeps the SG vote stamps of the
      core store. -/
  make_grades_compatible_with_finalized_core_timestamp_sg_vote : ∀ (ns : M.NS),
    (M.make_grades_compatible_with_finalized ns).core.timestamp_sg_vote = ns.core.timestamp_sg_vote
  /-- Making the saved grades compatible with the finalized block keeps the Goldfish vote pool of
      the core store. -/
  make_grades_compatible_with_finalized_core_pool : ∀ (ns : M.NS),
    (M.make_grades_compatible_with_finalized ns).core.pool = ns.core.pool
  /-- Making the saved grades compatible with the finalized block keeps the round votes of the core
      store. -/
  make_grades_compatible_with_finalized_core_round_votes : ∀ (ns : M.NS),
    M.round_votes (M.make_grades_compatible_with_finalized ns).core = M.round_votes ns.core
  /-- For every node state `n'` that `n`'s receipt of `o` can return, the finalized block of `n`'s
      store is an ancestor of, or equal to, that of `n'`'s store. -/
  node_process_F : ∀ (S : Setup V) (n : M.N) (o : NamedObject V) (n' : M.N)
    (hn' : M.process S n o ⇢ n'), Block.Preceq n.st.core.F n'.st.core.F
  /-- For every outcome `out` of `v`'s tick at `t` from `n`, the finalized block of `n`'s store is
      an ancestor of, or equal to, that of `out.1`'s store. -/
  node_tick_F : ∀ (S : Setup V) (v : V) (n : M.N) (t : Time)
    (out : M.N × List (NamedObject V)) (hout : M.tick S v n t ⇢ out),
    Block.Preceq n.st.core.F out.1.st.core.F
  /-- For every node state `n'` that `n`'s receipt of `o` can return, the round of `n'`'s grade
      cache is the round of `n`'s. -/
  process_cache_round : ∀ (S : Setup V) (n : M.N) (o : NamedObject V) (n' : M.N)
    (hn' : M.process S n o ⇢ n'), n'.cache.round = n.cache.round
  /-- For every node state `n'` that `n`'s receipt of `o` can return, the clock `t` and the slot `s`
      of `n'`'s core store are those of `n`'s. -/
  process_clock : ∀ (S : Setup V) (n : M.N) (o : NamedObject V) (n' : M.N)
    (hn' : M.process S n o ⇢ n'), n'.st.core.t = n.st.core.t ∧ n'.st.core.s = n.st.core.s
  /-- For every node state `n'` that `n`'s receipt of `o` can return, the signing record of `n'` is
      that of `n`. -/
  process_record_eq : ∀ (S : Setup V) (n : M.N) (o : NamedObject V) (n' : M.N)
    (hn' : M.process S n o ⇢ n'), n'.record = n.record
  /-- For every outcome `out` of `v`'s tick at `t` from `n`, the clock of `out.1`'s core store is
      `t` and its slot is the slot of `t`. -/
  tick_clock : ∀ (S : Setup V) (v : V) (n : M.N) (t : Time)
    (out : M.N × List (NamedObject V)) (hout : M.tick S v n t ⇢ out),
    out.1.st.core.t = t ∧ out.1.st.core.s = S.E.slotOf t
  /-- If the finalized block of `n`'s store is an ancestor of, or equal to, its justified block, the
      same holds of every node state `n'` that `n`'s receipt of `o` can return. -/
  frozen_process_preceq : ∀ (S : Setup V) (n : M.N) (o : NamedObject V)
    (h : Block.Preceq n.st.core.F n.st.core.J) (n' : M.N) (hn' : M.process S n o ⇢ n'),
    Block.Preceq n'.st.core.F n'.st.core.J
  /-- If the finalized block of `n`'s store is an ancestor of, or equal to, its justified block, the
      same holds of every outcome of `v`'s tick at `t` from `n`. -/
  frozen_tick_preceq : ∀ (S : Setup V) (v : V) (n : M.N) (t : Time)
    (h : Block.Preceq n.st.core.F n.st.core.J)
    (out : M.N × List (NamedObject V)) (hout : M.tick S v n t ⇢ out),
    Block.Preceq out.1.st.core.F out.1.st.core.J
  /-- For every node state `n'` that `n`'s receipt of `o` can return, `latest_confirmed` of `n'`'s
      core store is that of `n`'s. -/
  node_process_latest : ∀ (S : Setup V) (n : M.N) (o : NamedObject V) (n' : M.N)
    (hn' : M.process S n o ⇢ n'), n'.st.core.latest_confirmed = n.st.core.latest_confirmed
  /-- For every node state `n'` that `n`'s receipt of `o` can return, `latest_stable` of `n'`'s core
      store is that of `n`'s. -/
  node_process_stable : ∀ (S : Setup V) (n : M.N) (o : NamedObject V) (n' : M.N)
    (hn' : M.process S n o ⇢ n'), n'.st.core.latest_stable = n.st.core.latest_stable
  /-- For every outcome `g` of the grade read of `M.gradeContract c` at `st` and `r`, and every
      outcome `x` of `M.grade2Block st (M.readFrame c st r)`, the grade-2 block `g.Q2` is `x`. -/
  Sts_gradeContract_read_Q2 : ∀ (c : M.Cache) (E : Env V) (hc : Protocol.HealConfig) (st : M.HS)
    (r : Round), ∀ g : DecoupledConsensusModel.Protocol.GradeRead V, (M.gradeContract c).read E hc st r ⇢ g →
    ∀ x : Option (Block V), M.grade2Block st (M.readFrame c st r) ⇢ x → g.Q2 = x
  /-- For every outcome `g` of the grade read of `M.gradeContract c` at `st` and `r`, and every
      outcome `a` of `M.anchor` at the grade-1 result of the round-`r` frame read from `c` at `st`,
      the anchor of `g` is `a`. -/
  Sts_gradeContract_read_anchor : ∀ (c : M.Cache) (E : Env V) (hc : Protocol.HealConfig)
    (st : M.HS) (r : Round),
    ∀ g : DecoupledConsensusModel.Protocol.GradeRead V, (M.gradeContract c).read E hc st r ⇢ g →
    ∀ a : Block V, M.anchor E hc st r (M.readFrame c st r).g1 ⇢ a →
    g.anchor = a
  /-- For every outcome `g` of the grade read of `M.gradeContract c` at `st` and `r`, the raw
      grade-2 field of `g` holds exactly when the grade-2 result of the round-`r` frame read from
      `c` at `st` is a completed block. -/
  gradeContract_read_rawG2 : ∀ (c : M.Cache) (E : Env V) (hc : Protocol.HealConfig) (st : M.HS)
    (r : Round), ∀ g : DecoupledConsensusModel.Protocol.GradeRead V, (M.gradeContract c).read E hc st r ⇢ g → g.rawG2
      = ((((M.readFrame c st r).g2.bind id).isSome = true) : Prop)
  /-- The SG root read through `M.gradeContract c` at `st` and `r` can return `x` exactly when
      `M.anchor` at the grade-1 result of the round-`r` frame read from `c` at `st` can return `x`. -/
  gradeContract_sgRoot_eq_frameAnchor : ∀ (c : M.Cache) (E : Env V) (hc : Protocol.HealConfig)
    (st : M.HS) (r : Round) (x : Block V),
    M.get_sg_root_with (M.gradeContract c) E hc st r ⇢ x ↔ M.anchor E hc st r (M.readFrame c st r).g1 ⇢ x
  /-- The stable root of `M.gradeContract c` can return `x` exactly when `M.frameStableRoot c` can
      return `x`. -/
  gradeContract_stableRoot : ∀ (c : M.Cache) (E : Env V) (hc : Protocol.HealConfig) (st : M.HS)
    (r : Round) (x : Option (Block V)),
    (M.gradeContract c).stableRoot E hc st r ⇢ x ↔ M.frameStableRoot c E hc st r ⇢ x
  /-- Every body of an initial node state's store is genesis. -/
  initial_body_eq_genesis : ∀ (S : Setup V) (v : V) {D : NamedBlock V} (hD : D ∈ (M.initial S v).st.bodies),
    D = NamedBlock.genesis
  /-- No frame of an initial node state's grade cache has a phase result of the form
      `some (some root)`. -/
  initial_cache_phaseResult_ne : ∀ (S : Setup V) (v : V) (r₁ : Round) (p : Protocol.Phase) (root : Block V),
    M.phaseResult (M.cacheAtRound (M.initial S v).cache r₁) p ≠ some (some root)
  /-- The clock of an initial node state's store is `0`. -/
  initial_clock_eq_zero : ∀ (S : Setup V) (v : V), (M.initial S v).st.core.t = 0
  /-- The signing record of every initial node state holds no lock at any height. -/
  initial_record_lock : ∀ (S : Setup V) (v : V) (h : Height), (M.initial S v).record.legacy.lock h = none
  /-- The signing record of every initial node state holds no target at any height. -/
  initial_record_target : ∀ (S : Setup V) (v : V) (h : Height), (M.initial S v).record.legacy.target h = none
  /-- The store of every initial node state is `M.ns_initial`. -/
  initial_st_inclG2 : ∀ (S : Setup V) (v : V), (M.initial S v).st = (M.ns_initial : M.NS)
  /-- In every initial node state's store, genesis carries the block stamp `⊥`. -/
  initial_timestamp_genesis : ∀ (S : Setup V) (v : V), (M.initial S v).st.core.timestamp_block Block.genesis = some ⊥
  /-- For every node state `n'` that `n`'s receipt of `o` can return, the cache of `n'` is the cache
      of `n` clipped to the finalized block of `n'`'s store. -/
  namedNode_process_cache : ∀ (S : Setup V) (n : M.N) (o : NamedObject V) (n' : M.N)
    (hn' : M.process S n o ⇢ n') (hn : M.reachedNode n := by trivial), n'.cache = M.clipCache n'.st.core.F n.cache
  /-- For every outcome `out` of `v`'s tick at `t` from `n` and every outcome `c` of `M.onPhaseTick`
      at `t` from `n`'s store and cache, the cache of `out.1` is `c` clipped to the finalized block
      of `out.1`'s store. -/
  namedNode_tick_cache : ∀ (S : Setup V) (v : V) (n : M.N) (t : Int)
    (out : M.N × List (NamedObject V)) (hout : M.tick S v n t ⇢ out)
    (c : M.Cache) (hcache : M.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache ⇢ c)
    (hn : M.reachedNode n := by trivial),
    out.1.cache
      = M.clipCache out.1.st.core.F c
  /-- For every node state `n'` that `n`'s receipt of `o` can return, a named block `B` among `n'`'s
      bodies but not among `n`'s has its erasure stamped in `n'`'s store with the clock of `n`'s
      store. -/
  node_process_body_stamp : ∀ (S' : Setup V) (n : M.N) (o : NamedObject V) (n' : M.N)
    (hn' : M.process S' n o ⇢ n') (B : NamedBlock V) (h0 : B ∉ n.st.bodies)
    (h1 : B ∈ n'.st.bodies),
    n'.st.core.timestamp_block B.erase = some ((n.st.core.t : Int) : Stamp)
  /-- For every outcome `out` of `v`'s tick at `t` from `n`, a named block `B` among `out.1`'s
      bodies but not among `n`'s has its erasure stamped with `t` in `out.1`'s store. -/
  node_tick_body_stamp : ∀ (S' : Setup V) (v : V) (n : M.N) (t : Int)
    (out : M.N × List (NamedObject V)) (hout : M.tick S' v n t ⇢ out) (B : NamedBlock V)
    (h0 : B ∉ n.st.bodies) (h1 : B ∈ out.1.st.bodies),
    out.1.st.core.timestamp_block B.erase = some (t : Stamp)
  /-- The core call on `B` from `before` is `M.ns_process_block_core` under the setup's environment,
      healing configuration and height configuration. -/
  postCore_eq_process_block_core : ∀ (S : Setup V) (before : M.NS) (B : NamedBlock V),
    M.postCore S before B = M.ns_process_block_core S.E S.hc S.cfg before B
  /-- If `before` does not hold the parent body of `B`, the core call on `B` returns `before`. -/
  postCore_of_parent_not_mem : ∀ (S : Setup V) {before : M.NS} {B : NamedBlock V}
    (h : B.parent ∉ before.bodies), M.postCore S before B = before
  /-- The core call keeps the named SG rows. -/
  postCore_sg_rows : ∀ (S : Setup V) (before : M.NS) (B : NamedBlock V),
    (M.postCore S before B).sg_rows = before.sg_rows
  /-- The core call keeps the SG vote stamps. -/
  postCore_timestamp_sg_vote : ∀ (S : Setup V) (before : M.NS) (B : NamedBlock V),
    (M.postCore S before B).core.timestamp_sg_vote = before.core.timestamp_sg_vote
  /-- If every round's SG votes of `st`'s core store are the erasures of its named rows of that
      round, delivering an attestation `st` already holds among its rows of the attestation's round
      returns `st`. -/
  process_attest_of_mem_rows : ∀ (S : Setup V) (st : M.NS) (a : NamedAttestation V)
    (hPool : ∀ r, st.core.sg_votes r = (st.sg_rows r).map NamedAttestation.erase)
    (ha : a ∈ st.sg_rows a.round), M.receipt_process S st (NamedObject.attest a) = st
  /-- If `st`'s block tree is the erasure of its bodies, delivering a block `st` already holds among
      its bodies returns `st`. -/
  process_block_of_mem_bodies : ∀ (S : Setup V) (st : M.NS) (B : NamedBlock V)
    (hT : st.core.T = st.bodies.image NamedBlock.erase) (hB : B ∈ st.bodies),
    M.receipt_process S st (NamedObject.block B) = st
  /-- If the justified and finalized blocks of `st` are in its tree and an outcome of the round
      action under `M.gradeContract c` carries the finality pair `(h, T)`, then some block of `st`'s
      tree has a chain state whose justification height is `h`. -/
  round_action_head_mem_gradeContract : ∀ (c : M.Cache) (E : Env V) (hc : Protocol.HealConfig)
    (nd : Protocol.Node V) (st : M.S) (record : M.NR) (hJ : st.J ∈ st.T) (hF : st.F ∈ st.T)
    {h : Height} {T : BlockId}
    (out : M.NR × NamedAttestation V)
    (hout : M.round_action_with (M.gradeContract c) E hc nd st.toHealing record ⇢ out)
    (hp : out.2.finality_pair
      = some ⟨h, T⟩), ∃ Hd ∈ st.T, (st.σ Hd).h_j = h
  /-- For every node state `n'` that `n`'s receipt of `o` can return, the signing record of `n'` is
      that of `n`. -/
  process_record : ∀ (S : Setup V) (n : M.N) (o : NamedObject V) (n' : M.N)
    (hn' : M.process S n o ⇢ n'), n'.record = n.record
  /-- If an outcome of `v`'s tick at `t` from `n` sends the block `B`, then the slot of `t` is
      positive, `t` is that slot's proposal instant, `v` is that slot's proposer, and every outcome
      of the proposal duty, run with the frame contract of every outcome of `M.onPhaseTick` on `n`'s
      store with its clock set to `t`, has `B` as its block. -/
  block_mem_on_tick_emit : ∀ (S : Setup V) (v : V) (n : M.N) (t : Time)
    (out : M.N × List (NamedObject V)) (hout : M.tick S v n t ⇢ out) {B : NamedBlock V}
    (h : NamedObject.block B ∈ out.2)
    (hn : M.reachedNode n := by trivial) (hv : M.runs_as n v := by trivial),
    (0 < S.E.slotOf t ∧ t = M.proposal_time S.E (S.E.slotOf t) ∧
        S.E.proposer (S.E.slotOf t) = v) ∧
      ∀ (c : M.Cache), M.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache ⇢ c →
      ∀ (D : M.NS × Option (NamedBlock V)),
        M.duties_propose_block_with (M.frameContract c) S.E S.hc S.cfg (S.node v)
          (M.ns_setClock S.E n.st t) ⇢ D →
        D.2 = some B
  /-- If an outcome of `v`'s tick at `t` from `n` sends a block, `n` passes the grade-1 awake test
      `M.awake_for_grade1` of the round of `t`'s slot. -/
  block_mem_on_tick_emit_awake : ∀ (S : Setup V) (v : V) (n : M.N) (t : Time)
    (out : M.N × List (NamedObject V)), M.tick S v n t ⇢ out → ∀ {B : NamedBlock V},
    NamedObject.block B ∈ out.2 → M.awake_for_grade1 S v n (M.round_of S.hc (S.E.slotOf t))
  /-- If an outcome of `v`'s tick at `t` from `n` sends a Goldfish vote, `n` passes the grade-1
      awake test `M.awake_for_grade1` of the round of `t`'s slot. -/
  gfVote_mem_on_tick_emit_awake : ∀ (S : Setup V) (v : V) (n : M.N) (t : Time)
    (out : M.N × List (NamedObject V)), M.tick S v n t ⇢ out → ∀ {u : GoldfishVote V},
    NamedObject.gfVote u ∈ out.2 → M.awake_for_grade1 S v n (M.round_of S.hc (S.E.slotOf t))
  /-- If `n` fails the grade-1 awake test `M.awake_for_grade1` of the round of `t`'s slot, every
      outcome of `v`'s tick at `t` from `n` keeps `n`'s bodies and finalized block. -/
  tick_frame_of_not_awake_for_grade1 : ∀ (S : Setup V) (v : V) (n : M.N) (t : Time)
    (out : M.N × List (NamedObject V)), M.tick S v n t ⇢ out →
    ¬ M.awake_for_grade1 S v n (M.round_of S.hc (S.E.slotOf t)) →
    out.1.st.bodies = n.st.bodies ∧ out.1.st.core.F = n.st.core.F
  /-- If `n` fails the grade-2 awake test of the round of slot `s + 1`, every outcome of `v`'s tick
      at slot `s`'s confirmation time from `n`, under `Setup.alwaysAwake S`, keeps `n`'s
      `latest_confirmed` and `latest_stable`. -/
  tick_records_frame_of_not_awake_for_grade2 : ∀ (S : Setup V) (v : V) (n : M.N) (s : Slot)
    (out : M.N × List (NamedObject V)),
    M.tick (Setup.alwaysAwake S) v n (M.confirmation_time S.E s) ⇢ out →
    ¬ M.awake_for_grade2 (Setup.alwaysAwake S) v n (M.round_of S.hc (s + 1)) →
    out.1.st.core.latest_confirmed = n.st.core.latest_confirmed ∧
    out.1.st.core.latest_stable = n.st.core.latest_stable
  /-- If a named attestation `a` is not among the rows of its round in `n`'s store but is in the
      store of an outcome `out` of `v`'s tick at `t` from `n`, then `out` sends `a`, or `out` sends
      a block `B` and `a` is newly among those rows of the store the block handler returns on `B` at
      `n`'s store with its clock set to `t`. -/
  tick_new_full_row_origin : ∀ (S : Setup V) (v : V) (n : M.N) (t : Time)
    (out : M.N × List (NamedObject V)) (hout : M.tick S v n t ⇢ out)
    (a : NamedAttestation V) (hpre : a ∉ n.st.sg_rows a.round)
    (hpost : a ∈ out.1.st.sg_rows a.round),
    NamedObject.attest a ∈ out.2 ∨
      ∃ B, NamedObject.block B ∈ out.2 ∧
        a ∉ (M.ns_setClock S.E n.st t).sg_rows a.round ∧
        a ∈ (M.on_block_with .alsoCarried S.E S.hc S.cfg (M.ns_setClock S.E n.st t) B).sg_rows a.round
  /-- If `n`'s grade cache is unchanged by clipping at the finalized block of `n`'s core store, the
      same holds of `M.wake n`. -/
  wake_cache_clipped : ∀ n : M.N,
    M.clipCache n.st.core.F n.cache = n.cache →
    M.clipCache (M.wake n).st.core.F (M.wake n).cache = (M.wake n).cache
  /-- A store property `P` that holds of `n`'s store with its clock set to `t`, and is kept by the
      four duties (`hp`, `hv`, `hcf`, `ha`), by writing a grade cache (`hsc`) and by making the
      saved grades compatible with the finalized block (`hmg`), holds of the store of every outcome
      of `v`'s tick at `t` from `n`. -/
  named_tick_preserves : ∀ (P : M.NS → Prop) (S : Setup V) (v : V) (n : M.N) (t : Time)
    (hp : ∀ c : M.Cache, M.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache ⇢ c →
      ∀ st, P st → ∀ D : M.NS × Option (NamedBlock V),
        M.duties_propose_block_with (M.frameContract c) S.E S.hc S.cfg (S.node v) st ⇢ D → P D.1)
    (hv : ∀ c : M.Cache, M.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache ⇢ c →
      ∀ st, P st → ∀ D : M.NS × Option (GoldfishVote V),
        M.duties_goldfish_vote_with (M.frameContract c) S.E S.hc (S.node v) st ⇢ D → P D.1)
    (hcf : ∀ c : M.Cache, M.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache ⇢ c →
      ∀ st s, P st → ∀ st' : M.NS,
        M.duties_update_confirmation_with (M.frameContract c) S.E S.hc st s ⇢ st' → P st')
    (ha : ∀ c : M.Cache, M.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache ⇢ c →
      ∀ st record, P st → ∀ D : M.NS × M.NR × NamedAttestation V,
        M.duties_attest_with (M.frameContract c) S.E S.hc (S.node v) st record ⇢ D → P D.1)
    (hsc : ∀ st c, P st → P (M.store_with_cache st c))
    (hmg : ∀ st, P st → P (M.make_grades_compatible_with_finalized st))
    (h : P (M.ns_setClock S.E n.st t))
    (out : M.N × List (NamedObject V)) (hout : M.tick S v n t ⇢ out)
    (hn : M.reachedNode n := by trivial) (hruns : M.runs_as n v := by trivial),
    P out.1.st
  /-- If a Goldfish vote `u` is not in the pool of `n`'s store at `u`'s slot but is in that of an
      outcome `out` of `v`'s tick at `t` from `n`, then `out` sends `u`, or `out` sends a block `B`
      and `u` is newly in that pool of the store the block handler returns on `B` at `n`'s store
      with its clock set to `t`. -/
  tick_new_vote_origin : ∀ (S : Setup V) (v : V) (n : M.N) (t : Time)
    (out : M.N × List (NamedObject V)) (hout : M.tick S v n t ⇢ out) (u : GoldfishVote V)
    (hpre : u ∉ (M.store_pool n.st.core u.slot))
    (hpost : u ∈ (M.store_pool out.1.st.core u.slot)),
    NamedObject.gfVote u ∈ out.2 ∨
      ∃ B : NamedBlock V,
        NamedObject.block B ∈ out.2 ∧
        u ∉ (M.store_pool (M.ns_setClock S.E n.st t).core u.slot) ∧
        u ∈ (M.store_pool (M.on_block_with .alsoCarried S.E S.hc S.cfg
          (M.ns_setClock S.E n.st t) B).core u.slot)
  /-- If an outcome of `v`'s tick at `t` from `n` sends the Goldfish vote `u`, then the slot of `t`
      is positive, `t` is that slot's vote instant, every outcome of the vote duty (run with the
      frame contract of every outcome of `M.onPhaseTick` on `n`'s store with its clock set to `t`)
      has the vote `u`, `u` is signed by `v`, and `u`'s slot is the slot of `t`. -/
  gfVote_emitted_shape : ∀ (S : Setup V) (v : V) (n : M.N) (t : Time)
    (out : M.N × List (NamedObject V)) (hout : M.tick S v n t ⇢ out) (u : GoldfishVote V),
    NamedObject.gfVote u ∈ out.2 →
    ∀ (hn : M.reachedNode n := by trivial) (hv : M.runs_as n v := by trivial),
    0 < S.E.slotOf t ∧ t = M.vote_time S.E (S.E.slotOf t) ∧
      (∀ c : M.Cache, M.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache ⇢ c →
        ∀ D : M.NS × Option (GoldfishVote V),
          M.duties_goldfish_vote_with (M.frameContract c) S.E S.hc (S.node v)
            (M.ns_setClock S.E n.st t) ⇢ D → D.2 = some u) ∧
      u.val_index = v ∧ u.slot = S.E.slotOf t
  /-- Let `st0` be `n`'s store with its clock set to `t`. When `t` is the proposal instant of a
      positive slot whose proposer is `v` and `n` passes the grade-1 awake test of its round, every
      outcome of `v`'s tick at `t` has the bodies and core tree of the proposal duty's outcome on
      `st0`; otherwise, if `n` runs as `v`, those of `st0`. -/
  tick_bodies_and_coreT_from_proposal : ∀ (S : Setup V) (v : V) (n : M.N) (t : Time)
    (out : M.N × List (NamedObject V)) (hout : M.tick S v n t ⇢ out)
    (hn : M.reachedNode n := by trivial) (hv : M.runs_as n v := by trivial),
    let s := S.E.slotOf t
    let st0 := M.ns_setClock S.E n.st t
    ((0 < s ∧ t = M.proposal_time S.E s ∧ S.E.proposer s = (S.node v).val_index ∧
        M.awake_for_grade1 S v n (M.round_of S.hc s)) →
      ∀ c : M.Cache, M.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache ⇢ c →
      ∀ D : M.NS × Option (NamedBlock V),
        M.duties_propose_block_with (M.frameContract c) S.E S.hc S.cfg (S.node v) st0 ⇢ D →
        out.1.st.bodies = D.1.bodies ∧ out.1.st.core.T = D.1.core.T) ∧
    (M.runs_as n v →
      ¬ (0 < s ∧ t = M.proposal_time S.E s ∧ S.E.proposer s = (S.node v).val_index ∧
        M.awake_for_grade1 S v n (M.round_of S.hc s)) →
      out.1.st.bodies = st0.bodies ∧ out.1.st.core.T = st0.core.T)
  /-- If `before` passes the grade-2 awake test `M.awake_for_grade2` of round `r`, an outcome of
      `v`'s tick at round `r`'s action instant from `before` sends exactly the attestation of the
      attestation duty, run on the outcome `st` of the confirmation duty with the grade contract of
      the cache update's outcome `c` and `before`'s signing record. -/
  tick_at_action_awake : ∀ (S : Setup V) (v : V) (before : M.N) (r : Round)
    (out : M.N × List (NamedObject V)) (hout : M.tick S v before (M.a S.hc S.E.Δ r) ⇢ out)
    (c : M.Cache) (hc : M.onPhaseTick S.E S.hc before.st.core.toHealing (M.a S.hc S.E.Δ r) before.cache ⇢ c)
    (st : M.NS) (hst : M.duties_update_confirmation_with (M.gradeContract c) S.E S.hc
      (M.ns_setClock S.E before.st (M.a S.hc S.E.Δ r)) (S.E.slotOf (M.a S.hc S.E.Δ r) - 1) ⇢ st)
    (D : M.NS × M.NR × NamedAttestation V)
    (hD : M.duties_attest_with (M.gradeContract c) S.E S.hc (S.node v) st before.record ⇢ D)
    (hrun : M.awake_for_grade2 S v before r)
    (hn : M.reachedNode before := by trivial) (hv : M.runs_as before v := by trivial),
    out.2 = [NamedObject.attest D.2.2]
  /-- If `before` fails the grade-2 awake test `M.awake_for_grade2` of round `r`, every outcome of
      `v`'s tick at round `r`'s action instant from `before` sends nothing. -/
  tick_at_action_asleep : ∀ (S : Setup V) (v : V) (before : M.N) (r : Round)
    (out : M.N × List (NamedObject V)) (hout : M.tick S v before (M.a S.hc S.E.Δ r) ⇢ out)
    (hasleep : ¬ M.awake_for_grade2 S v before r),
    out.2 = []
  /-- For a positive slot `s`, if `n` passes the grade-2 awake test of `s`'s round under
      `Setup.alwaysAwake S`, then for every outcome of `v`'s tick at slot `s`'s support cutoff from
      `n`, its `live_confirmed` is that of the outcome `D` of the confirmation duty for slot
      `s - 1`, run with the grade contract of the cache update's outcome `c`. -/
  on_tick_emit_confirmation_of_outcomes : ∀ (S : Setup V) (v : V) (n : M.N) (s : Slot) (hs : 0 < s)
    (out : M.N × List (NamedObject V)) (hout : M.tick S v n (M.support_cutoff S.E s) ⇢ out)
    (c : M.Cache) (hc : M.onPhaseTick S.E S.hc n.st.core.toHealing (M.support_cutoff S.E s) n.cache ⇢ c)
    (D : M.NS) (hD : M.duties_update_confirmation_with (M.gradeContract c) S.E S.hc
      (M.ns_setClock S.E n.st (M.support_cutoff S.E s)) (s - 1) ⇢ D)
    (hrun : M.awake_for_grade2 (Setup.alwaysAwake S) v n (M.round_of S.hc s))
    (hn : M.reachedNode n := by trivial),
    out.1.st.core.live_confirmed = D.core.live_confirmed
  /-- For a positive slot `s`, if the Goldfish vote duty at slot `s`'s vote instant, run with the
      grade contract of the cache update's outcome `c`, can return the vote `u`, and `n` passes the
      grade-1 awake test of `s`'s round, then every outcome of `v`'s tick at that instant from `n`
      sends `u`. -/
  on_tick_emit_vote_mem_of_outcomes : ∀ (S : Setup V) (v : V) (n : M.N) (s : Slot) (hs : 0 < s)
    {u : GoldfishVote V}
    (c : M.Cache) (hc : M.onPhaseTick S.E S.hc n.st.core.toHealing (M.vote_time S.E s) n.cache ⇢ c)
    (D : M.NS × Option (GoldfishVote V))
    (hD : M.duties_goldfish_vote_with (M.gradeContract c) S.E S.hc (S.node v)
      (M.ns_setClock S.E n.st (M.vote_time S.E s)) ⇢ D)
    (hu : D.2 = some u)
    (out : M.N × List (NamedObject V)) (hout : M.tick S v n (M.vote_time S.E s) ⇢ out)
    (hrun : M.awake_for_grade1 S v n (M.round_of S.hc s))
    (hn : M.reachedNode n := by trivial) (hv : M.runs_as n v := by trivial),
    NamedObject.gfVote u ∈ out.2
  /-- For a positive slot `s` whose proposer is `v`, if the proposal duty at slot `s`'s proposal
      instant, run with the grade contract of the cache update's outcome `c`, can return the block
      `B`, and `n` passes the grade-1 awake test of `s`'s round, then every outcome of `v`'s tick at
      that instant from `n` sends `B`. -/
  on_tick_emit_proposal_mem_of_outcomes : ∀ (S : Setup V) (v : V) (n : M.N) (s : Slot) (hs : 0 < s)
    (hpr : S.E.proposer s = (S.node v).val_index) {B : NamedBlock V}
    (c : M.Cache) (hc : M.onPhaseTick S.E S.hc n.st.core.toHealing (M.proposal_time S.E s) n.cache ⇢ c)
    (D : M.NS × Option (NamedBlock V))
    (hD : M.duties_propose_block_with (M.gradeContract c) S.E S.hc S.cfg (S.node v)
      (M.ns_setClock S.E n.st (M.proposal_time S.E s)) ⇢ D)
    (hB : D.2 = some B)
    (out : M.N × List (NamedObject V)) (hout : M.tick S v n (M.proposal_time S.E s) ⇢ out)
    (hrun : M.awake_for_grade1 S v n (M.round_of S.hc s))
    (hn : M.reachedNode n := by trivial) (hv : M.runs_as n v := by trivial),
    NamedObject.block B ∈ out.2
  /-- If a named block `B` is not among the bodies of `n`'s store but is among those of an outcome
      `out` of `v`'s tick at `t` from `n`, then `out` sends `B`. -/
  tick_new_body_origin : ∀ (S : Setup V) (v : V) (n : M.N) (t : Time)
    (out : M.N × List (NamedObject V)) (hout : M.tick S v n t ⇢ out) (B : NamedBlock V)
    (hpre : B ∉ n.st.bodies) (hpost : B ∈ out.1.st.bodies),
    NamedObject.block B ∈ out.2
  /-- If `n` runs as `v` and an outcome of `v`'s tick at `t` from `n` sends the attestation `a`,
      then `t` is the action instant of `a`'s round, `n` passes the grade-2 awake test of that
      round, and `a` is signed by `v`. -/
  tick_attestation_fields : ∀ (S : Setup V) (v : V) (n : M.N) (t : Time)
    (hv : M.runs_as n v)
    (out : M.N × List (NamedObject V)) (hout : M.tick S v n t ⇢ out)
    (a : NamedAttestation V) (h : NamedObject.attest a ∈ out.2),
    t = M.a S.hc S.E.Δ a.round ∧ M.awake_for_grade2 S v n a.round ∧ a.val_index = v
  /-- If `t ≤ bound`, `n`'s named store is coherent, its clock is at or before `bound`, and every
      named attestation in its rows of a round `k` has round `k` and a receipt stamp at or before
      `bound`, then the same holds of the store of every outcome of `v`'s tick at `t` from `n`. -/
  rawRelay_tick_outcome_data : ∀ (S : Setup V) (v : V) (n : M.N) (t : Time)
    (out : M.N × List (NamedObject V)) (hout : M.tick S v n t ⇢ out) (bound : Time),
    t ≤ bound → Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg n.st →
    (n.st.core.t ≤ bound ∧ ∀ k (a : NamedAttestation V), a ∈ n.st.sg_rows k →
      a.round = k ∧ ∃ stamp : Time, stamp ≤ bound ∧
        n.st.core.timestamp_sg_vote (M.sgVote a.erase) = some (stamp : Stamp)) →
    (out.1.st.core.t ≤ bound ∧ ∀ k (a : NamedAttestation V), a ∈ out.1.st.sg_rows k →
      a.round = k ∧ ∃ stamp : Time, stamp ≤ bound ∧
        out.1.st.core.timestamp_sg_vote (M.sgVote a.erase) = some (stamp : Stamp))
  /-- For a positive slot `s` whose proposer is `v`, if `n` passes the grade-1 awake test of `s`'s
      round, every outcome of `v`'s tick at slot `s`'s proposal instant from `n` has the block
      stamps of the store of the proposal duty's outcome `D`. -/
  on_tick_emit_proposal_timestamp_block_of_outcomes : ∀ (S : Setup V) (v : V) (n : M.N) (s : Slot) (hs : 0 < s)
    (hprop : S.E.proposer s = (S.node v).val_index)
    (c : M.Cache) (hc : M.onPhaseTick S.E S.hc n.st.core.toHealing (M.proposal_time S.E s) n.cache ⇢ c)
    (D : M.NS × Option (NamedBlock V))
    (hD : M.duties_propose_block_with (M.gradeContract c) S.E S.hc S.cfg (S.node v)
      (M.ns_setClock S.E n.st (M.proposal_time S.E s)) ⇢ D)
    (out : M.N × List (NamedObject V)) (hout : M.tick S v n (M.proposal_time S.E s) ⇢ out)
    (hrun : M.awake_for_grade1 S v n (M.round_of S.hc s))
    (hn : M.reachedNode n := by trivial) (hv : M.runs_as n v := by trivial),
    out.1.st.core.timestamp_block = D.1.core.timestamp_block
  /-- If a named block `B` is not among the bodies of `n`'s store but is among those of an outcome
      `out` of `v`'s tick at `t` from `n`, then `B` is among the bodies `M.ns_process_block_core`
      returns on `B` at `n`'s store with its clock set to `t`, and that call's finalized block is
      `out`'s. -/
  tick_new_body_core : ∀ (S : Setup V) (v : V) (n : M.N) (t : Time)
    (out : M.N × List (NamedObject V)) (hout : M.tick S v n t ⇢ out)
    (B : NamedBlock V) (hpre : B ∉ n.st.bodies) (hpost : B ∈ out.1.st.bodies),
    B ∈ (M.ns_process_block_core S.E S.hc S.cfg (M.ns_setClock S.E n.st t) B).bodies ∧
      (M.ns_process_block_core S.E S.hc S.cfg (M.ns_setClock S.E n.st t) B).core.F =
        out.1.st.core.F
  /-- A receipt keeps every named block among the bodies, every Goldfish vote in its slot's list of
      the core store, and every named attestation among the rows of its round. -/
  processed_mono_receipt : ∀ (S : Setup V) (st : M.NS) (o' : NamedObject V),
    (∀ B : NamedBlock V, B ∈ st.bodies → B ∈ (M.receipt_process S st o').bodies) ∧
    (∀ u : GoldfishVote V, u ∈ st.core.gf_votes u.slot →
      u ∈ (M.receipt_process S st o').core.gf_votes u.slot) ∧
    (∀ a : NamedAttestation V, a ∈ st.sg_rows a.round →
      a ∈ (M.receipt_process S st o').sg_rows a.round)
  /-- A receipt of `o'` at `st` adds nothing but `o'` and what `o'` includes: a new named block is
      `o'`, and a new Goldfish vote or named attestation is `o'` or is included in the block `o'`
      when the core call on that block newly holds it. -/
  flip_of_process : ∀ (S : Setup V) (st : M.NS) (o' : NamedObject V),
    (∀ B : NamedBlock V, B ∉ st.bodies → B ∈ (M.receipt_process S st o').bodies →
      NamedObject.block B = o') ∧
    (∀ u : GoldfishVote V, u ∉ st.core.gf_votes u.slot →
      u ∈ (M.receipt_process S st o').core.gf_votes u.slot →
      NamedObject.gfVote u = o' ∨ ∃ B : NamedBlock V, o' = NamedObject.block B ∧
        (∃ j : Nat, B.gf_votes[j]? = some u) ∧ B.erase ∉ st.core.T ∧
        B.erase ∈ (M.postCore S st B).core.T) ∧
    (∀ a : NamedAttestation V, a ∉ st.sg_rows a.round →
      a ∈ (M.receipt_process S st o').sg_rows a.round →
      NamedObject.attest a = o' ∨ ∃ B : NamedBlock V, o' = NamedObject.block B ∧
        (∃ j : Nat, B.attestations[j]? = some a) ∧ B ∉ st.bodies ∧
        B ∈ (M.postCore S st B).bodies)
  /-- The receipt of a block, a Goldfish vote or a named attestation at `st` either returns `st` or
      returns a store that holds that object. -/
  receipt_noop_or_processed : ∀ (S : Setup V) (st : M.NS),
    (∀ B : NamedBlock V, M.receipt_process S st (NamedObject.block B) = st ∨
      B ∈ (M.receipt_process S st (NamedObject.block B)).bodies) ∧
    (∀ u : GoldfishVote V, M.receipt_process S st (NamedObject.gfVote u) = st ∨
      u ∈ (M.receipt_process S st (NamedObject.gfVote u)).core.gf_votes u.slot) ∧
    (∀ a : NamedAttestation V, M.receipt_process S st (NamedObject.attest a) = st ∨
      a ∈ (M.receipt_process S st (NamedObject.attest a)).sg_rows a.round)
  /-- With `st₀` for `n`'s store with its clock set to `t`, every outcome `out` of `v`'s tick at `t`
      from `n` keeps every block, Goldfish vote and named attestation `st₀` holds, and every one it
      newly holds is sent by `out` or is included in a block `out` sends and newly held by the core
      call on that block at `st₀`. -/
  addsOnlyCarried_node_tick : ∀ (S : Setup V) (v : V) (n : M.N) (t : Int)
    (out : M.N × List (NamedObject V)) (hout : M.tick S v n t ⇢ out),
    ((∀ B : NamedBlock V, B ∈ (M.ns_setClock S.E n.st t).bodies → B ∈ out.1.st.bodies) ∧
      (∀ u : GoldfishVote V, u ∈ (M.ns_setClock S.E n.st t).core.gf_votes u.slot →
        u ∈ out.1.st.core.gf_votes u.slot) ∧
      (∀ a : NamedAttestation V, a ∈ (M.ns_setClock S.E n.st t).sg_rows a.round →
        a ∈ out.1.st.sg_rows a.round)) ∧
    (∀ B : NamedBlock V, B ∉ (M.ns_setClock S.E n.st t).bodies → B ∈ out.1.st.bodies →
      NamedObject.block B ∈ out.2) ∧
    (∀ u : GoldfishVote V, u ∉ (M.ns_setClock S.E n.st t).core.gf_votes u.slot →
      u ∈ out.1.st.core.gf_votes u.slot →
      NamedObject.gfVote u ∈ out.2 ∨ ∃ B : NamedBlock V, NamedObject.block B ∈ out.2 ∧
        (∃ j : Nat, B.gf_votes[j]? = some u) ∧
        B.erase ∉ (M.ns_setClock S.E n.st t).core.T ∧
        B.erase ∈ (M.postCore S (M.ns_setClock S.E n.st t) B).core.T) ∧
    (∀ a : NamedAttestation V, a ∉ (M.ns_setClock S.E n.st t).sg_rows a.round →
      a ∈ out.1.st.sg_rows a.round →
      NamedObject.attest a ∈ out.2 ∨ ∃ B : NamedBlock V, NamedObject.block B ∈ out.2 ∧
        (∃ j : Nat, B.attestations[j]? = some a) ∧
        B ∉ (M.ns_setClock S.E n.st t).bodies ∧
        B ∈ (M.postCore S (M.ns_setClock S.E n.st t) B).bodies)
  /-- When `t` is the proposal instant of a positive slot whose proposer is `v` and `n` passes the
      grade-1 awake test of its round (`hdue`), every outcome of `v`'s tick at `t` from `n` has the
      Goldfish votes and vote stamps of the store of the proposal duty's outcome `D` on `n`'s store
      with its clock set to `t`. -/
  tick_fields_from_proposal : ∀ (S : Setup V) (v : V) (n : M.N) (t : Time)
    (out : M.N × List (NamedObject V)) (hout : M.tick S v n t ⇢ out)
    (hdue : 0 < S.E.slotOf t ∧ t = M.proposal_time S.E (S.E.slotOf t) ∧
      S.E.proposer (S.E.slotOf t) = (S.node v).val_index)
    (hrun : M.awake_for_grade1 S v n (M.round_of S.hc (S.E.slotOf t))),
    ∀ c : M.Cache, M.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache ⇢ c →
    ∀ D : M.NS × Option (NamedBlock V),
      M.duties_propose_block_with (M.frameContract c) S.E S.hc S.cfg (S.node v)
        (M.ns_setClock S.E n.st t) ⇢ D →
      ∀ (hn : M.reachedNode n := by trivial) (hv : M.runs_as n v := by trivial),
      out.1.st.core.gf_votes = D.1.core.gf_votes ∧
        out.1.st.core.timestamp_vote = D.1.core.timestamp_vote
  /-- If `n` passes the grade-1 awake test of the round of `t`'s slot and every outcome of the
      proposal stage `tickStage1` satisfies `NamedFinalityAdvance`, then so does the store of every
      outcome of `v`'s tick at `t` from `n`. -/
  advance_tick_of_stage1 : ∀ (S : Setup V) (v : V) (n : M.N) (t : Time)
    (out : M.N × List (NamedObject V)) (hout : M.tick S v n t ⇢ out)
    (hrun : M.awake_for_grade1 S v n (M.round_of S.hc (S.E.slotOf t))),
    (∀ c : M.Cache, M.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache ⇢ c →
      ∀ st₁ : M.NS,
        Restated.Vocabulary.Proofs.HealingSurface.tickStage1 M S (M.frameContract c) (S.node v) n.st t ⇢ st₁ →
        Restated.Vocabulary.Proofs.HealingSurface.NamedFinalityAdvance M S st₁) →
    ∀ (hn : M.reachedNode n := by trivial) (hv : M.runs_as n v := by trivial),
    Restated.Vocabulary.Proofs.HealingSurface.NamedFinalityAdvance M S out.1.st
  /-- If `before` passes the grade-2 awake test of round `r`, every outcome of `v`'s tick at round
      `r`'s action instant from `before` has the rows of the store of the attestation duty's outcome
      `D`, run on the outcome `st` of the confirmation duty with the grade contract of the cache
      update's outcome `c`. -/
  action_tick_store_of_outcomes : ∀ (S : Setup V) (v : V) (before : M.N) (r : Round)
    (hrun : M.awake_for_grade2 S v before r)
    (out : M.N × List (NamedObject V)) (hout : M.tick S v before (M.a S.hc S.E.Δ r) ⇢ out)
    (c : M.Cache) (hc : M.onPhaseTick S.E S.hc before.st.core.toHealing (M.a S.hc S.E.Δ r)
      before.cache ⇢ c)
    (st : M.NS) (hst : M.duties_update_confirmation_with (M.gradeContract c) S.E S.hc
      (M.ns_setClock S.E before.st (M.a S.hc S.E.Δ r)) (S.E.slotOf (M.a S.hc S.E.Δ r) - 1) ⇢ st)
    (D : M.NS × M.NR × NamedAttestation V)
    (hD : M.duties_attest_with (M.gradeContract c) S.E S.hc (S.node v) st before.record ⇢ D)
    (hn : M.reachedNode before := by trivial) (hv : M.runs_as before v := by trivial),
    out.1.st.sg_rows = D.1.sg_rows
  /-- Let `st0` be `n`'s store with its clock set to `t`. When `t` is the proposal instant of a
      positive slot whose proposer is `v` and `n` passes the grade-1 awake test of its round, every
      outcome of `v`'s tick at `t` holds every row of the proposal duty's outcome on `st0`;
      otherwise it holds every row of `st0`. -/
  tick_rows_after_proposal_of_outcomes : ∀ (S : Setup V) (v : V) (n : M.N) (t : Time)
    (out : M.N × List (NamedObject V)) (hout : M.tick S v n t ⇢ out)
    (hn : M.reachedNode n := by trivial) (hv : M.runs_as n v := by trivial),
    let s := S.E.slotOf t
    let st0 := M.ns_setClock S.E n.st t
    ((0 < s ∧ t = M.proposal_time S.E s ∧ S.E.proposer s = (S.node v).val_index ∧
        M.awake_for_grade1 S v n (M.round_of S.hc s)) →
      ∀ c : M.Cache, M.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache ⇢ c →
      ∀ D : M.NS × Option (NamedBlock V),
        M.duties_propose_block_with (M.frameContract c) S.E S.hc S.cfg (S.node v) st0 ⇢ D →
        ∀ a : NamedAttestation V, a ∈ D.1.sg_rows a.round → a ∈ out.1.st.sg_rows a.round) ∧
    (¬ (0 < s ∧ t = M.proposal_time S.E s ∧ S.E.proposer s = (S.node v).val_index ∧
        M.awake_for_grade1 S v n (M.round_of S.hc s)) →
      ∀ a : NamedAttestation V, a ∈ st0.sg_rows a.round → a ∈ out.1.st.sg_rows a.round)
  /-- If `before` is coherent, the core call newly inserts `B`, and the finalized block derived for
      `B` is a descendant of `before`'s finalized block and satisfies the stated ancestry conditions
      against `before`'s justified block and held bodies, then it is an ancestor of the finalized
      block after the core call. -/
  postCore_absorbs_finality : ∀ (S : Setup V) (before : M.NS) (B : NamedBlock V),
    DecoupledConsensusModel.Sts.Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg before →
    B.erase ∉ before.core.T →
    B.erase ∈ (M.postCore S before B).core.T →
    Block.Preceq before.core.F (M.derive_named S.E S.cfg B).F →
    (∀ A ∈ before.bodies,
      (M.derive_named S.E S.cfg A).J = (M.derive_named S.E S.cfg B).F →
      (M.derive_named S.E S.cfg A).h_j = (M.derive_named S.E S.cfg B).h_F →
      Block.Preceq (M.derive_named S.E S.cfg B).F before.core.J) →
    (∃ D ∈ before.bodies, (M.derive_named S.E S.cfg D).h = before.core.h_max) →
    (∀ D ∈ before.bodies,
      (M.derive_named S.E S.cfg B).h_F < (M.derive_named S.E S.cfg D).h →
      Block.Preceq (M.derive_named S.E S.cfg B).F D.erase) →
    ∀ (hn : M.reachedStore before := by trivial),
    Block.Preceq (M.derive_named S.E S.cfg B).F (M.postCore S before B).core.F
  /-- If `n`'s store is coherent, a named attestation `a` newly among the rows of its round in an
      outcome of `v`'s tick at `t` from `n` has SG vote stamp `t` there. -/
  node_tick_sg_row_stamp : ∀ (S' : Setup V) (v : V) (n : M.N) (t : Int)
    (out : M.N × List (NamedObject V)) (hout : M.tick S' v n t ⇢ out),
    DecoupledConsensusModel.Sts.Restated.Vocabulary.Proofs.NamedStore.Coherent M S'.E S'.cfg n.st →
    ∀ a : NamedAttestation V, a ∉ n.st.sg_rows a.round → a ∈ out.1.st.sg_rows a.round →
      out.1.st.core.timestamp_sg_vote (M.sgVote a.erase) = some (t : Stamp)
  /-- A named attestation `a` newly among the rows of its round in the store the receipt of `o`
      returns on `st` has as its SG vote stamp the clock of `st`. -/
  receipt_process_sg_row_stamp : ∀ (S' : Setup V) (st : M.NS) (o : NamedObject V)
    (a : NamedAttestation V), a ∉ st.sg_rows a.round →
    a ∈ (M.receipt_process S' st o).sg_rows a.round →
    (M.receipt_process S' st o).core.timestamp_sg_vote (M.sgVote a.erase) =
      some (st.core.t : Stamp)
  /-- For a positive slot `s`, if an outcome `out` of `v`'s tick at slot `s`'s vote instant from `n`
      sends the slot-`s` vote `u`, `n`'s Goldfish votes are well stamped with stamps at most its
      clock, its clock is at most the vote instant, and `u`'s sender does not equivocate in `n`'s
      slot-`s` pool, then `u` is in the slot-`s` list of `out.1`'s core store with a stamp at most
      the vote instant. -/
  tick_vote_pooled : ∀ (S : Setup V) (v : V) (n : M.N) (s : Slot) (u : GoldfishVote V)
    (out : M.N × List (NamedObject V)), M.tick S v n (M.vote_time S.E s) ⇢ out →
    0 < s → NamedObject.gfVote u ∈ out.2 → u.slot = s →
    (∀ (k : Slot) (x : GoldfishVote V), x ∈ n.st.core.gf_votes k → x.slot = k) →
    (∀ (k : Slot) (x : GoldfishVote V), x ∈ n.st.core.gf_votes k →
      (n.st.core.timestamp_vote x).isSome = true) →
    (∀ x : GoldfishVote V, (n.st.core.timestamp_vote x).isSome = true → x ∈ n.st.core.gf_votes x.slot) →
    (∀ (x : GoldfishVote V) (c : Stamp), n.st.core.timestamp_vote x = some c → c ≤ (n.st.core.t : Stamp)) →
    n.st.core.t ≤ M.vote_time S.E s →
    M.equivocates (M.store_pool n.st.core s) u.val_index = false →
    u ∈ out.1.st.core.gf_votes s ∧
      ∃ c : Stamp, out.1.st.core.timestamp_vote u = some c ∧ c ≤ (M.vote_time S.E s : Stamp)
  /-- The initial node state of `v` is the same at the setup `S` and at `setupWithGST S g hg`, the
      setup `S` with its GST replaced by `g`. -/
  initial_setupWithGST : ∀ (S : DecoupledConsensusModel.Execution.Setup V) (g : ℤ) (hg : 0 ≤ g) (v : V), M.initial (DecoupledConsensusModel.Sts.setupWithGST S g hg) v = M.initial S v
  /-- If `t` is the support cutoff of its positive slot `s` and neither its proposal nor its
      Goldfish vote instant, and `n` passes the grade-2 awake test of `s`'s round under
      `Setup.alwaysAwake S`, then every outcome of `v`'s tick at `t` from `n` holds the
      `latest_stable` and `latest_confirmed` of the outcome `D` of the confirmation update for slot
      `s - 1`. -/
  tick_records_at_confirmation_of_outcomes : ∀ (S : Setup V) (v : V) (n : M.N) (t : Int),
    0 < S.E.slotOf t → t ≠ M.proposal_time S.E (S.E.slotOf t) →
    t ≠ M.vote_time S.E (S.E.slotOf t) → t = M.support_cutoff S.E (S.E.slotOf t) →
    M.awake_for_grade2 (Setup.alwaysAwake S) v n (M.round_of S.hc (S.E.slotOf t)) →
    ∀ (out : M.N × List (NamedObject V)), M.tick S v n t ⇢ out →
    ∀ (c : M.Cache), M.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache ⇢ c →
    ∀ (D : M.S), M.update_confirmation_with (M.gradeContract c) S.E S.hc
      (M.ns_setClock S.E n.st t).core (S.E.slotOf t - 1) ⇢ D →
    ∀ (hn : M.reachedNode n := by trivial),
    out.1.st.core.latest_stable = D.latest_stable ∧
      out.1.st.core.latest_confirmed = D.latest_confirmed
  /-- If `t` is not the support cutoff of a positive slot, every outcome of `v`'s tick at `t` from
      `n` keeps `n`'s `latest_stable`. -/
  on_tick_emit_stable_of_ne : ∀ (S : Setup V) (v : V) (n : M.N) (t : Time)
    (h : ¬ (0 < S.E.slotOf t ∧ t = M.support_cutoff S.E (S.E.slotOf t)))
    (out : M.N × List (NamedObject V)) (hout : M.tick S v n t ⇢ out),
    out.1.st.core.latest_stable = n.st.core.latest_stable
  /-- If `t` is not the support cutoff of a positive slot, every outcome of `v`'s tick at `t` from
      `n` keeps `n`'s `latest_confirmed`. -/
  on_tick_emit_latest_of_ne : ∀ (S : Setup V) (v : V) (n : M.N) (t : Time)
    (h : ¬ (0 < S.E.slotOf t ∧ t = M.support_cutoff S.E (S.E.slotOf t)))
    (out : M.N × List (NamedObject V)) (hout : M.tick S v n t ⇢ out),
    out.1.st.core.latest_confirmed = n.st.core.latest_confirmed
  /-- The SG candidate of `M.gradeContract c` at `st` and `s` can return `x` exactly when
      `M.frameSGCandidate c E hc st s` can. -/
  gradeContract_confirmationSG : ∀ (c : M.Cache) (E : Env V) (hc : Protocol.HealConfig) (st : M.HS)
    (s : Slot) (x : Option (Block V)),
    (M.gradeContract c).confirmationSG E hc st s ⇢ x ↔ M.frameSGCandidate c E hc st s ⇢ x
  /-- The grade contract of a cache is its frame contract. -/
  gradeContract_eq_frameContract : ∀ (c : M.Cache), M.gradeContract c = M.frameContract c
  /-- If `t` is neither the proposal instant nor the Goldfish vote instant of its slot, every
      outcome of `v`'s tick at `t` from `n` keeps `F`, `J`, `h_j`, `h_max`, the block tree and the
      bodies of `n`'s store. -/
  tick_tree_fields_of_not_proposal_vote : ∀ (S : Setup V) (v : V) (n : M.N) (t : Time)
    (hnp : t ≠ M.proposal_time S.E (S.E.slotOf t))
    (hnv : t ≠ M.vote_time S.E (S.E.slotOf t))
    (out : M.N × List (NamedObject V)) (hout : M.tick S v n t ⇢ out),
    out.1.st.core.F = n.st.core.F ∧
      out.1.st.core.J = n.st.core.J ∧
      out.1.st.core.h_j = n.st.core.h_j ∧
      out.1.st.core.h_max = n.st.core.h_max ∧
      out.1.st.core.T = n.st.core.T ∧
      out.1.st.bodies = n.st.bodies

/-- The facts about executions and runs of the node routines of a model `M`. -/
structure NodeRunFacts (M : Model V) : Prop where
  /-- If every block of `n`'s core tree has a slot at most the slot of `n`'s core store, the same
      holds of every node state `n'` that `n`'s receipt of `o` can return. -/
  treeSlotStep_process : ∀ (S : Setup V) (n : M.N) (o : NamedObject V) (n' : M.N), M.process S n o ⇢ n' →
    (∀ B : Block V, B ∈ n.st.core.T → B.slot ≤ n.st.core.s) →
    (∀ B : Block V, B ∈ n'.st.core.T → B.slot ≤ n'.st.core.s)
  /-- For every node state `n'` that `n`'s receipt of `o` can return, `InsertsAt` at the clock of
      `n`'s core store holds from that core store to `n'`'s. -/
  insertsAt_process : ∀ (S : Setup V) (n : M.N) (o : NamedObject V) (n' : M.N),
    M.process S n o ⇢ n' → Restated.InsertsAt M S.E n.st.core.t n.st.core n'.st.core
  /-- If every block of `n`'s core tree has a block stamp, every block stamp is of a block of the
      tree, and no block stamp is later than the clock, then every node state `n'` that `n`'s
      receipt of `o` can return keeps every block and block stamp of `n`'s core store and satisfies
      the same three conditions. -/
  blockStep_process : ∀ (S : Setup V) (n : M.N) (o : NamedObject V) (n' : M.N), M.process S n o ⇢ n' →
    ((∀ B : Block V, B ∈ n.st.core.T → (n.st.core.timestamp_block B).isSome = true) ∧
      (∀ B : Block V, (n.st.core.timestamp_block B).isSome = true → B ∈ n.st.core.T) ∧
      (∀ (B : Block V) (c : Stamp), n.st.core.timestamp_block B = some c →
        c ≤ (n.st.core.t : Stamp))) →
    ∀ (hn : M.reachedNode n := by trivial),
    ((∀ B : Block V, B ∈ n.st.core.T → B ∈ n'.st.core.T) ∧
      (∀ (B : Block V) (c : Stamp), n.st.core.timestamp_block B = some c →
        n'.st.core.timestamp_block B = some c)) ∧
    ((∀ B : Block V, B ∈ n'.st.core.T → (n'.st.core.timestamp_block B).isSome = true) ∧
      (∀ B : Block V, (n'.st.core.timestamp_block B).isSome = true → B ∈ n'.st.core.T) ∧
      (∀ (B : Block V) (c : Stamp), n'.st.core.timestamp_block B = some c →
        c ≤ (n'.st.core.t : Stamp)))
  /-- For every node state `n'` that `n`'s receipt of `o` can return, `VoteInsertStep` holds from
      `n`'s core store to `n'`'s at the clock and slot of `n`'s core store. -/
  voteInsertStep_process : ∀ (S : Setup V) (n : M.N) (o : NamedObject V) (n' : M.N),
    M.process S n o ⇢ n' →
      Restated.Vocabulary.Protocol.VoteInsertStep M n.st.core.t n.st.core.s n.st.core n'.st.core
  /-- If the clock of `n`'s core store is at most `t`, `VoteInsertStep` holds at `t` and the slot of
      `t` from `n`'s core store to that of every outcome of `v`'s tick at `t` from `n`. -/
  voteInsertStep_onTickEmit : ∀ (S : Setup V) (v : V) (n : M.N) (t : Time)
    (out : M.N × List (NamedObject V)), M.tick S v n t ⇢ out → n.st.core.t ≤ t →
      Restated.Vocabulary.Protocol.VoteInsertStep M t (S.E.slotOf t) n.st.core out.1.st.core
  /-- For every node state `n'` that `n`'s receipt of `o` can return, `PoolStep` holds from `n`'s
      core store to `n'`'s. -/
  poolStep_process : ∀ (S : Setup V) (n : M.N) (o : NamedObject V) (n' : M.N),
    M.process S n o ⇢ n' → Restated.Vocabulary.Protocol.PoolStep M n.st.core n'.st.core
  /-- For every node state `n'` that `n`'s receipt of `o` can return, `live_confirmed` of `n'`'s
      store is that of `n`'s. -/
  process_live_confirmed : ∀ (S : Setup V) (n : M.N) (o : NamedObject V) (n' : M.N)
    (hn' : M.process S n o ⇢ n'), n'.st.core.live_confirmed = n.st.core.live_confirmed
  /-- In every world the run `rho` can reach before its first event, every body a validator holds is
      genesis. -/
  stateBefore_zero_body_eq_genesis : ∀ (S : Setup V) (rho : Record.Run V) (v : V) (w : V → M.N)
    (hw : w ∈ stateBeforeOf M S rho 0) {D : NamedBlock V} (hD : D ∈ (w v).st.bodies),
    D = NamedBlock.genesis
  /-- For a positive slot `s` whose proposer is awake from `M.proposal_wake_start S s` to the
      proposal instant and never held by the adversary up to it, every outcome of the proposer's
      tick at that instant, on its node state at the tick step `k` for that instant, sends some
      named block. -/
  tick_emits_proposal_inclX : ∀ (S : Setup V) (Sched : Framework.StsMultisetLog.Schedule V)
    (x : Framework.StsMultisetLog.AtomicExec (protocolOf M S) Sched) (k : Nat) {s : Slot}
    (hl : x.lbl k = Framework.StsMultisetLog.AtomicAction.tickAllAwake (M.proposal_time S.E s).toNat)
    (hhon : ∀ t' ≤ M.proposal_time S.E s, S.E.proposer s ∉ Sched.adv t')
    (hs : 0 < s)
    (hawake : S.E.proposer s ∈
      Sched.awakeThroughout (M.proposal_wake_start S s) (M.proposal_time S.E s))
    (out : M.N × List (NamedObject V))
    (hout : M.tick (Setup.alwaysAwake S) (S.E.proposer s) (x[k][S.E.proposer s].st)
      (M.proposal_time S.E s) ⇢ out),
    ∃ B : NamedBlock V, NamedObject.block B ∈ out.2
  /-- In an execution where no two blocks in play have distinct ancestors with one root, and no
      proposer holds a block with the root it is about to give its proposal, every tick at a tick
      step at `τ` of a validator awake at `τ` and never held by the adversary up to `τ` has an
      outcome. -/
  tick_outcome_sts : ∀ (S : Setup V) (Sched : Framework.StsMultisetLog.Schedule V)
    (x : Framework.StsMultisetLog.AtomicExec (protocolOf M S) Sched),
    (∀ B C : NamedBlock V,
      (∃ B' : NamedBlock V,
        ((∃ (i : Nat) (sm : Framework.StsMultisetLog.SignedMsg V (NamedObject V)),
            sm ∈ x[i].sent ∧ sm.msg = .block B') ∨
          (∃ (i : Nat) (v : V), (∀ t' ≤ (x[i].time : Int), v ∉ Sched.adv t') ∧
            B' ∈ x[i][v].st.st.bodies)) ∧
        NamedBlock.Preceq B B') →
      (∃ C' : NamedBlock V,
        ((∃ (i : Nat) (sm : Framework.StsMultisetLog.SignedMsg V (NamedObject V)),
            sm ∈ x[i].sent ∧ sm.msg = .block C') ∨
          (∃ (i : Nat) (v : V), (∀ t' ≤ (x[i].time : Int), v ∉ Sched.adv t') ∧
            C' ∈ x[i][v].st.st.bodies)) ∧
        NamedBlock.Preceq C C') →
      ∀ A D : NamedBlock V,
        (NamedBlock.Preceq A B ∨ NamedBlock.Preceq A C) →
        (NamedBlock.Preceq D B ∨ NamedBlock.Preceq D C) → A.root = D.root → A = D) →
    (∀ (k τ : Nat) (s : Slot), x.lbl k = Framework.StsMultisetLog.AtomicAction.tickAllAwake τ →
      (τ : Int) = M.proposal_time S.E s →
      (∀ t' ≤ (τ : Int), S.E.proposer s ∉ Sched.adv t') →
      ∀ B ∈ x[k][S.E.proposer s].st.st.bodies, B.root ≠ (S.node (S.E.proposer s)).new_root s) →
    ∀ (k τ : Nat) (v : V), x.lbl k = Framework.StsMultisetLog.AtomicAction.tickAllAwake τ →
      v ∈ Sched.awake (τ : Int) \ Sched.adv (τ : Int) →
      (∀ t' ≤ (τ : Int), v ∉ Sched.adv t') →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (wakeStage M Sched (τ : Int) x[k] v) (τ : Int) ⇢ out
  /-- In every world the run `rho` can reach before its `i`-th event, the node state of `v` runs as
      `v`. -/
  stateBeforeOf_runs_as : ∀ (S : Setup V) (rho : Record.Run V) (i : Nat) (w : V → M.N)
    (hw : w ∈ stateBeforeOf M S rho i) (v : V), M.runs_as (w v) v
  /-- In every world the run `rho` can reach before its `i`-th event, every node state is one a run
      reaches. -/
  stateBeforeOf_reachedNode : ∀ (S : Setup V) (rho : Record.Run V) (i : Nat) (w : V → M.N)
    (hw : w ∈ stateBeforeOf M S rho i) (v : V), M.reachedNode (w v)
  /-- If the clock of `n`'s core store is at most `t`, every block of its tree has a block stamp,
      every block stamp is of a block of the tree, and no block stamp is later than the clock, then
      every outcome of `v`'s tick at `t` from `n` keeps every block and block stamp of `n`'s core
      store and satisfies the same three conditions. -/
  blockStep_tick : ∀ (S : Setup V) (v : V) (n : M.N) (t : DecoupledConsensusModel.Time)
    (out : M.N × List (NamedObject V)), M.tick S v n t ⇢ out → n.st.core.t ≤ t →
    ((∀ B : Block V, B ∈ n.st.core.T → (n.st.core.timestamp_block B).isSome = true) ∧
      (∀ B : Block V, (n.st.core.timestamp_block B).isSome = true → B ∈ n.st.core.T) ∧
      (∀ (B : Block V) (c : Stamp), n.st.core.timestamp_block B = some c →
        c ≤ (n.st.core.t : Stamp))) →
    ∀ (hn : M.reachedNode n := by trivial),
    ((∀ B : Block V, B ∈ n.st.core.T → B ∈ out.1.st.core.T) ∧
      (∀ (B : Block V) (c : Stamp), n.st.core.timestamp_block B = some c →
        out.1.st.core.timestamp_block B = some c)) ∧
    ((∀ B : Block V, B ∈ out.1.st.core.T → (out.1.st.core.timestamp_block B).isSome = true) ∧
      (∀ B : Block V, (out.1.st.core.timestamp_block B).isSome = true → B ∈ out.1.st.core.T) ∧
      (∀ (B : Block V) (c : Stamp), out.1.st.core.timestamp_block B = some c →
        c ≤ (out.1.st.core.t : Stamp)))
  /-- If the slot of `n`'s core store is at most the slot of `t` and every block of `n`'s core tree
      has a slot at most that store's slot, the same holds of every outcome of `v`'s tick at `t`
      from `n`. -/
  treeSlotStep_tick : ∀ (S : Setup V) (v : V) (n : M.N) (t : Int)
    (out : M.N × List (NamedObject V)), M.tick S v n t ⇢ out → n.st.core.s ≤ S.E.slotOf t →
    (∀ B : Block V, B ∈ n.st.core.T → B.slot ≤ n.st.core.s) →
    (∀ B : Block V, B ∈ out.1.st.core.T → B.slot ≤ out.1.st.core.s)
  /-- At a tick step `k` whose instant `τ` is after one delay before round `r`'s grade-2 cutoff, a
      validator awake from that time to `τ` and never held by the adversary up to `τ` passes the
      grade-2 awake test of round `r` on the node state its tick at `τ` reads. -/
  run_fact_g2_at : ∀ (S : Setup V) (Sched : Framework.StsMultisetLog.Schedule V)
    (x : Framework.StsMultisetLog.AtomicExec (protocolOf M S) Sched) (k τ : Nat) (r : Round) (v : V),
    x.lbl k = Framework.StsMultisetLog.AtomicAction.tickAllAwake τ →
    M.early S.E S.hc r .g2 - S.E.Δ < (τ : Int) →
    v ∈ Sched.awakeThroughout (M.early S.E S.hc r .g2 - S.E.Δ) (τ : Int) →
    (∀ t' ≤ (τ : Int), v ∉ Sched.adv t') →
    M.awake_for_grade2 (Setup.alwaysAwake S) v (wakeStage M Sched (τ : Int) x[k] v) r
  /-- At a tick step `k` whose instant `τ` is after one delay before round `r`'s grade-1 cutoff, a
      validator awake from that time to `τ` and never held by the adversary up to `τ` passes the
      grade-1 awake test of round `r` on the node state its tick at `τ` reads. -/
  run_fact_g1_at : ∀ (S : Setup V) (Sched : Framework.StsMultisetLog.Schedule V)
    (x : Framework.StsMultisetLog.AtomicExec (protocolOf M S) Sched) (k τ : Nat) (r : Round) (v : V),
    x.lbl k = Framework.StsMultisetLog.AtomicAction.tickAllAwake τ →
    M.early S.E S.hc r .g1 - S.E.Δ < (τ : Int) →
    v ∈ Sched.awakeThroughout (M.early S.E S.hc r .g1 - S.E.Δ) (τ : Int) →
    (∀ t' ≤ (τ : Int), v ∉ Sched.adv t') →
    M.awake_for_grade1 (Setup.alwaysAwake S) v (wakeStage M Sched (τ : Int) x[k] v) r

end DecoupledConsensusModel.Sts.Record
