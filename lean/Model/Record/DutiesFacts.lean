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
import Proofs.Vocabulary.Protocol.Handlers.HandlerAdmissionGuards
import Proofs.Vocabulary.Protocol.Schedule.HeldSkipProducers
import Proofs.Vocabulary.ModelProperties.NamedReceiptCalls_postCore
import Proofs.Vocabulary.Execution.OutageActionInputs
import Proofs.Vocabulary.ModelProperties.with_attestation_input
import Proofs.Vocabulary.Protocol.ValidatorClient.RecordFresh
import Proofs.Vocabulary.Protocol.ValidatorClient.RecordTargetHistory
import Model.Conditions.Vocabulary_Protocol_Handlers_Pool
import Proofs.Vocabulary.Protocol.Handlers.StoreBridge
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedStore_initial
import Proofs.Vocabulary.Protocol.Handlers.Pool
import Proofs.Claims.Spec2Claims.Claim13bModel_opening
import Proofs.Claims.ProcessedFlip
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Proofs.Vocabulary.ModelProperties.NamedActions_proposal_with
import Proofs.Vocabulary.Protocol.ChainState.ProposalBridge
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedDuties_goldfish_vote_with
import Proofs.Vocabulary.Execution.W4FKChainAdvanceFold
import Proofs.Vocabulary.Protocol.Handlers.GoldfishVotePool
import Proofs.Claims.Spec2Claims.Claim13beRoute3_23
import Proofs.Vocabulary.Protocol.Duties.Proposals.ProposalRows
import Proofs.Vocabulary.ModelProperties.update_confirmation_with
import Proofs.Vocabulary.Protocol.Handlers.AcceptanceTiming
import Proofs.Vocabulary.Protocol.Handlers.Blocks
import Model.Conditions.Claim13bStepKitConfirm
import Proofs.Claims.Spec2Claims.Claim13bStepKitConfirm
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.Confirmation
import Proofs.Claims.Spec2Claims.Claim13beRoute3_5
import Proofs.Claims.Spec2Claims.Claim13beRoute3_4
import Proofs.Vocabulary.Protocol.Handlers.SGArrivalStampCarrier
import Proofs.Vocabulary.Protocol.ChainState.RawHeightCoverage
import Proofs.Claims.Spec2Claims.Claim13bK_ConfirmedSettle

/-!
# Facts of the duty and tick family

The structure `DutiesFacts`: facts that the duty and tick routines of a model `M : Model V` satisfy
on every input. The structure `DutiesRunFacts` is for facts about runs of the same family, and has
no field.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

open DecoupledConsensusModel.Execution
open Protocol (ChainState HeightConfig)
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Protocol (Record)
open Internal
open Execution
open DecoupledConsensusModel.Proofs.ModelProperties
open DecoupledConsensusModel.Proofs.NamedActions
open Protocol.NamedActions
open DecoupledConsensusModel.Proofs.NamedDuties
open Protocol.NamedDuties
open DecoupledConsensusModel.Proofs.Optimistic
open Protocol (HealConfig)
open Internal.NamedRecoveryRead
open Protocol
open DecoupledConsensusModel.Protocol
open Protocol (HeightConfig)

/-- Facts that the duty and tick routines of `M` satisfy on every input. -/
structure DutiesFacts (M : Model V) : Prop where
  /-- For every outcome `D` of the proposal duty on `st`, `InsertsAt` holds at `c` from the core
      store of `st` to the core store of `D`'s named store. -/
  insertsAt_named_propose : ∀ (E : Env V) (c : Int) (contract : M.Contract) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) (nd : Protocol.Node V) (st : M.NS)
    (D : M.NS × Option (NamedBlock V)), M.duties_propose_block_with contract E hc cfg nd st ⇢ D →
    Restated.InsertsAt M E c st.core D.1.core
  /-- For every outcome `D` of the Goldfish-vote duty on `st`, `InsertsAt` holds at `c` from the
      core store of `st` to the core store of `D`'s named store. -/
  insertsAt_named_vote : ∀ (E : Env V) (c : Int) (contract : M.Contract) (hc : Protocol.HealConfig)
    (nd : Protocol.Node V) (st : M.NS)
    (D : M.NS × Option (GoldfishVote V)), M.duties_goldfish_vote_with contract E hc nd st ⇢ D →
    Restated.InsertsAt M E c st.core D.1.core
  /-- For every outcome `D` of the confirmation duty for slot `s` on `st`, `InsertsAt` holds at `c`
      from the core store of `st` to the core store of `D`. -/
  insertsAt_named_confirmation : ∀ (E : Env V) (c : Int) (contract : M.Contract)
    (hc : Protocol.HealConfig) (st : M.NS) (s : Slot)
    (D : M.NS), M.duties_update_confirmation_with contract E hc st s ⇢ D →
    Restated.InsertsAt M E c st.core D.core
  /-- For every outcome `D` of the attestation duty on `st` and the signing record `record`,
      `InsertsAt` holds at `c` from the core store of `st` to the core store of `D`'s named store. -/
  insertsAt_named_attest : ∀ (E : Env V) (c : Int) (contract : M.Contract) (hc : Protocol.HealConfig)
    (nd : Protocol.Node V) (st : M.NS) (record : M.NR)
    (D : M.NS × M.NR × NamedAttestation V), M.duties_attest_with contract E hc nd st record ⇢ D →
    Restated.InsertsAt M E c st.core D.1.core
  /-- Every outcome `st'` of the confirmation update has the chain-state map `σ` of `st`. -/
  update_confirmation_with_σ : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (st : M.S) (s : Slot) (st' : M.S), M.update_confirmation_with contract E hc st s ⇢ st' → st'.σ = st.σ
  /-- If the FG root of `st` and an outcome `R` of `M.get_sg_root_with contract E hc` at `st`'s
      round are in `st`'s filtered block tree, then the `live_confirmed` block of every outcome
      `st'` of `M.update_confirmation_with contract E hc st s` is in that tree. -/
  update_confirmation_with_live_confirmed_mem_filtered : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (st : M.S) (s : Slot), M.get_fg_root (M.toHealing st).toFG ∈ M.get_filtered_block_tree (M.toHealing st).toFG → ∀ R : Block V, M.get_sg_root_with contract E hc (M.toHealing st) (M.round_of hc st.s) ⇢ R → R ∈ M.get_filtered_block_tree (M.toHealing st).toFG → ∀ st' : M.S, M.update_confirmation_with contract E hc st s ⇢ st' → st'.live_confirmed ∈ M.get_filtered_block_tree (M.toHealing st).toFG
  /-- Every row of an outcome `L` of the pool-and-carried selector at the named store `st` is among
      `st`'s pool rows or among every outcome `C` of its carried rows. -/
  mem_select_poolAndCarried : ∀ (hc : Protocol.HealConfig) (st : M.NS) {a : NamedAttestation V}
    (L : List (NamedAttestation V)), M.select .poolAndCarried hc st ⇢ L →
    a ∈ L → ∀ C : List (NamedAttestation V), M.carriedRows hc st ⇢ C → a ∈ M.poolRows hc st ∨ a ∈ C
  /-- For every outcome `D` of the Goldfish-vote duty on `st`, the core store of `D`'s named store
      has the finalized block of `st`'s core store. -/
  namedDuties_goldfish_vote_with_fst_core_F : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : M.NS) (D : M.NS × Option (GoldfishVote V)), M.duties_goldfish_vote_with contract E hc nd st ⇢ D → D.1.core.F = st.core.F
  /-- If the named store `st` satisfies the named-store root invariant at `E` and `cfg`, every
      outcome of the proposal duty on `st` under the grade contract of the cache `c` is some named
      block. -/
  proposal_with_gradeContract_isSome : ∀ (c : M.Cache) (source : DecoupledConsensusModel.Protocol.ProposalRowSource) (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig) (cfg : DecoupledConsensusModel.Protocol.HeightConfig) (nd : DecoupledConsensusModel.Protocol.Node V) (st : M.NS), DecoupledConsensusModel.Sts.Restated.Vocabulary.Proofs.NamedStoreRoots.Invariant M E cfg st → ∀ o : Option (NamedBlock V), M.proposal_with (M.gradeContract c) source E hc nd st ⇢ o → ∃ B, o = Option.some B
  /-- Every row of an outcome `L` of the pool-and-carried selector at the named store `st` has a
      round at most the round of `st`'s slot. -/
  selected_row_round_le : ∀ (hc : DecoupledConsensusModel.Protocol.HealConfig) (st : M.NS) {a : DecoupledConsensusModel.NamedAttestation V} (L : List (DecoupledConsensusModel.NamedAttestation V)), M.select .poolAndCarried hc st ⇢ L → a ∈ L → a.round ≤ M.round_of hc st.core.s
  /-- If the named store `st` satisfies the confirmation-membership invariant, then under the grade
      contract of any cache `c`, the confirmed root of every outcome `I` of the attestation input at
      the healing view of `st`'s core is the root of a block of `st`'s block tree. -/
  attestation_input_head_gradeContract : ∀ (c : M.Cache) (E : Env V) (hc : Protocol.HealConfig)
    (cfg : HeightConfig) (nd : Protocol.Node V) (st : M.NS)
    (h : Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant M E cfg st)
    (I : Protocol.AttestationInput V)
    (hI : M.with_attestation_input (M.gradeContract c) E hc nd (M.toHealing st.core) id ⇢ I),
    ∃ H ∈ st.core.T, I.confirmed = some H.root
  /-- If the named store `st` satisfies the confirmation-membership invariant, `A2` is an outcome of
      the grade-2 block of `st`'s core store at round `r` under the grade contract of `cache`, and
      an outcome of the FG source at `A2` is `raw`, then `raw` is in `st`'s core block tree. -/
  frame_fg_source_mem : ∀ (S : Setup V) (cache : M.Cache) (st : M.NS) (r : Round)
    (hinv : Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant M S.E S.cfg st)
    {raw : Block V}
    (A2 : Option (Block V)) (hA2 : M.grade2_block_with (M.gradeContract cache) S.E S.hc (M.toHealing st.core) r ⇢ A2)
    (o : Option (Block V)) (ho : M.fg_source_with (M.gradeContract cache) S.E S.hc (M.toHealing st.core) r A2 ⇢ o)
    (hs : o = some raw),
    raw ∈ st.core.T
  /-- If the row of an outcome `A` of the round action at the healing store `st` has the height pair
      `.vote h entry timeout`, then every outcome `I` of the attestation input at `st` under the
      same contract has the fields `(h, entry, nu)` for some `nu`. -/
  round_action_names_source : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig)
    (nd : Protocol.Node V) (st : M.HS) (record : M.NR) (h : Height) (entry : BlockId)
    (timeout : Bool)
    (A : M.NR × NamedAttestation V) (hA : M.round_action_with contract E hc nd st record ⇢ A)
    (hp : A.2.height_pair = .vote h entry timeout)
    (I : Protocol.AttestationInput V) (hI : M.with_attestation_input contract E hc nd st id ⇢ I),
    ∃ nu, I.fields = some (h, entry, nu)
  /-- If the named store `st` satisfies the confirmation-membership invariant, so does every outcome
      `D` of the confirmation duty under the grade contract of any cache `c`. -/
  invariant_update_gradeContract : ∀ (c : M.Cache) (E : Env V) (hc : Protocol.HealConfig)
    (cfg : HeightConfig) (st : M.NS) (s : Slot)
    (h : Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant M E cfg st)
    (D : M.NS) (hD : M.duties_update_confirmation_with (M.gradeContract c) E hc st s ⇢ D),
    Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant M E cfg D
  /-- For every outcome `A` of `M.round_action_with contract E hc nd st record`, every choice `res`
      of an outcome of the resolution test `M.resolved st.T u` per vote `u`, and every outcome `H`
      of `M.get_head_with` from `st`'s pool at `st`'s slot restricted to the votes `u` with
      `res u = true`, the finality pair of `A`'s attestation is the one `M.finality_pair` gives from
      the legacy record of `record` and the justified height, the justified block's root and the
      finalized height of `H`'s chain state. -/
  round_action_finality_pair_eq : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig)
    (nd : Protocol.Node V) (st : M.HS) (record : M.NR)
    (A : M.NR × NamedAttestation V) (hA : M.round_action_with contract E hc nd st record ⇢ A)
    (res : GoldfishVote V → Bool) (hres : ∀ u, M.resolved st.T u ⇢ res u)
    (H : Block V) (hH : M.get_head_with contract E hc st (st.toFG.toSG.toGoldfishStore.pool st.s)
      ((st.toFG.toSG.toGoldfishStore.pool st.s).filter (fun u => res u = true)) st.s ⇢ H),
    A.2.finality_pair =
      M.finality_pair record.legacy (st.σ H).h_j (st.σ H).J.root (st.σ H).h_F
  /-- If the legacy record of `record` has at height `h` the target nothing or `J`, the timeout bit
      clear and the lock nothing or `J`, then for every outcome `A` of
      `M.round_action_with contract E hc nd st record`, every choice `res` of an outcome of the
      resolution test per vote, and every outcome `H` of `M.get_head_with` from `st`'s pool at
      `st`'s slot restricted to the votes `u` with `res u = true`, if `H`'s chain state has
      justified height `h`, a justified block of root `J` and a finalized height less than `h`, then
      the finality pair of `A`'s attestation is `(h, J)`. -/
  namedRoundAction_finality_pair_of_record_guard : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig)
    (nd : Protocol.Node V) (st : M.HS) (record : M.NR) {h : Height} {J : BlockId}
    (htarget : record.legacy.target h = none ∨ record.legacy.target h = some J)
    (htimeout : record.legacy.timeout h = false)
    (hlock : record.legacy.lock h = none ∨ record.legacy.lock h = some J)
    (A : M.NR × NamedAttestation V) (hA : M.round_action_with contract E hc nd st record ⇢ A)
    (res : GoldfishVote V → Bool) (hres : ∀ u, M.resolved st.T u ⇢ res u)
    (H : Block V) (hH : M.get_head_with contract E hc st (st.toFG.toSG.toGoldfishStore.pool st.s)
      ((st.toFG.toSG.toGoldfishStore.pool st.s).filter (fun u => res u = true)) st.s ⇢ H)
    (hhj : (st.σ H).h_j = h) (hJ : (st.σ H).J.root = J) (hF : (st.σ H).h_F < h),
    A.2.finality_pair = some ⟨h, J⟩
  /-- For every outcome `A` of the round action at the healing store `st`, every outcome `A2` of the
      grade-2 block at the round of `st`'s slot, and every outcome `F` of the FG source at `A2`, the
      height pair of `A`'s row is `M.encodeHeight` applied to the height fields of `F` (its height,
      its entry's root and its `nj` bit) and to the height pair `M.height_pair` computes from the
      legacy record, those fields and `A`'s finality pair. -/
  named_round_action_height_pair : ∀ (contract : M.Contract) (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig) (nd : DecoupledConsensusModel.Protocol.Node V) (st : M.HS) (record : M.NR)
    (A : M.NR × NamedAttestation V) (hA : M.round_action_with contract E hc nd st record ⇢ A)
    (A2 : Option (Block V)) (hA2 : M.grade2_block_with contract E hc st (M.round_of hc st.s) ⇢ A2)
    (F : Option (Block V)) (hF : M.fg_source_with contract E hc st (M.round_of hc st.s) A2 ⇢ F),
    A.2.height_pair =
      M.encodeHeight (F.map
        (fun Q => ((st.σ Q).h, (st.σ Q).T_h.root, (st.σ Q).nj)))
        (M.height_pair record.legacy (F.map
          (fun Q => ((st.σ Q).h, (st.σ Q).T_h.root, (st.σ Q).nj))) A.2.finality_pair)
  /-- If an outcome of the proposal duty with the row source `source` at `st` is the block `B`, then
      for every outcome `input` of the proposal input at `st`'s healing view and every outcome `L`
      of `M.select source hc st`, `B`'s parent is a body of `st` that erases to `input`'s parent;
      `B`'s slot, root, Goldfish votes, Goldfish support votes and proposer are `input`'s; and `B`'s
      attestations are `M.proposalRows B.parent L`. The hypothesis `hn`, that `st` is a reached
      store, defaults to `trivial`. -/
  proposal_payload : ∀ (contract : M.Contract) (source : Protocol.ProposalRowSource) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : M.NS) (B : NamedBlock V)
    (o : Option (NamedBlock V)), M.proposal_with contract source E hc nd st ⇢ o → o = some B →
    ∀ input : Protocol.ProposalInput V, M.with_proposal_input contract E hc nd (M.toHealing st.core) id ⇢ input →
    ∀ L : List (NamedAttestation V), M.select source hc st ⇢ L →
    ∀ (hn : M.reachedStore st := by trivial),
    B.parent ∈ st.bodies ∧ B.parent.erase = input.parent ∧
    B.slot = input.slot ∧ B.root = input.root ∧
    B.gf_votes = input.gf_votes ∧ B.gf_support_votes = input.gf_support_votes ∧
    B.attestations = M.proposalRows B.parent L ∧
    B.proposer? = some input.proposer
  /-- If an outcome of the proposal duty at `st` is the block `B`, then for every outcome `input` of
      the proposal input at `st`'s healing view, `B` has a named parent that erases to `input`'s
      parent. -/
  proposal_with_parent? : ∀ (contract : M.Contract) (source : DecoupledConsensusModel.Protocol.ProposalRowSource) (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig) (nd : DecoupledConsensusModel.Protocol.Node V) (st : M.NS) (B : DecoupledConsensusModel.NamedBlock V) (o : Option (DecoupledConsensusModel.NamedBlock V)), M.proposal_with contract source E hc nd st ⇢ o → o = Option.some B → ∀ input : Protocol.ProposalInput V, M.with_proposal_input contract E hc nd (M.toHealing st.core) id ⇢ input → ∃ p, B.parent? = Option.some p ∧ p.erase = input.parent
  /-- For every outcome `I` of the attestation input at `st`, every outcome `A2` of the grade-2
      block of `st`'s round, and every outcome `W` of the SG vote at `st`'s round from `A2`, the
      confirmed root of `I` is the root of `W`. -/
  with_attestation_input_id_confirmed : ∀ (contract : M.Contract) (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig) (nd : DecoupledConsensusModel.Protocol.Node V) (st : M.HS)
    (I : Protocol.AttestationInput V) (hI : M.with_attestation_input contract E hc nd st id ⇢ I)
    (A2 : Option (Block V)) (hA2 : M.grade2_block_with contract E hc st ((M.round_of hc st.toFG.toSG.toGoldfishStore.s)) ⇢ A2)
    (W : Block V) (hW : M.get_sg_vote_with contract E hc st ((M.round_of hc st.toFG.toSG.toGoldfishStore.s)) A2 ⇢ W),
    I.confirmed = Option.some W.root
  /-- For every outcome `I` of the attestation input at `st`, every outcome `A2` of the grade-2
      block of `st`'s round, and every outcome `F` of the FG source at `st`'s round from `A2`, the
      height fields of `I` are absent when `F` is absent, and otherwise are the height, the entry's
      root and the `nj` bit of the chain state `st` holds at `F`. -/
  with_attestation_input_id_fields : ∀ (contract : M.Contract) (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig) (nd : DecoupledConsensusModel.Protocol.Node V) (st : M.HS)
    (I : Protocol.AttestationInput V) (hI : M.with_attestation_input contract E hc nd st id ⇢ I)
    (A2 : Option (Block V)) (hA2 : M.grade2_block_with contract E hc st ((M.round_of hc st.toFG.toSG.toGoldfishStore.s)) ⇢ A2)
    (F : Option (Block V)) (hF : M.fg_source_with contract E hc st ((M.round_of hc st.toFG.toSG.toGoldfishStore.s)) A2 ⇢ F),
    I.fields = Option.map (fun q ↦ ((st.toFG.σ q).h, (st.toFG.σ q).T_h.root, (st.toFG.σ q).nj)) F
  /-- For every outcome `P` of the proposal input at `st` and every outcome `L` of the proposer's
      view of `st`'s support votes at `st`'s slot, the support votes of `P` are `L`. -/
  with_proposal_input_id_gf_support_votes : ∀ (contract : M.Contract) (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig) (nd : DecoupledConsensusModel.Protocol.Node V) (st : M.HS)
    (P : Protocol.ProposalInput V) (hP : M.with_proposal_input contract E hc nd st id ⇢ P)
    (L : List (GoldfishVote V)) (hL : M.proposer_support_view st.toFG.toSG.toGoldfishStore st.toFG.toSG.toGoldfishStore.s ⇢ L),
    P.gf_support_votes = L
  /-- The Goldfish votes of every outcome `P` of the proposal input at `st` are the proposer's view
      of `st`'s Goldfish votes at `st`'s slot. -/
  with_proposal_input_id_gf_votes : ∀ (contract : M.Contract) (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig) (nd : DecoupledConsensusModel.Protocol.Node V) (st : M.HS)
    (P : Protocol.ProposalInput V) (hP : M.with_proposal_input contract E hc nd st id ⇢ P),
    P.gf_votes = M.proposer_view st.toFG.toSG.toGoldfishStore st.toFG.toSG.toGoldfishStore.s
  /-- For every outcome `P` of the proposal input at `st`, every outcome `L` of the proposer's view
      of `st`'s support votes at `st`'s slot, and every outcome `H` of `M.get_head_with` from the
      proposer's view of `st`'s Goldfish votes and `L` at the slot before `st`'s slot, the parent of
      `P` is `H`. -/
  with_proposal_input_id_parent : ∀ (contract : M.Contract) (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig) (nd : DecoupledConsensusModel.Protocol.Node V) (st : M.HS)
    (P : Protocol.ProposalInput V) (hP : M.with_proposal_input contract E hc nd st id ⇢ P)
    (L : List (GoldfishVote V)) (hL : M.proposer_support_view st.toFG.toSG.toGoldfishStore st.toFG.toSG.toGoldfishStore.s ⇢ L)
    (H : Block V) (hH : M.get_head_with contract E hc st (M.proposer_view st.toFG.toSG.toGoldfishStore st.toFG.toSG.toGoldfishStore.s).toFinset L.toFinset (st.toFG.toSG.toGoldfishStore.s - 1) ⇢ H),
    P.parent = H
  /-- The proposer of every outcome `P` of the proposal input at `st` for the node `nd` is `nd`'s
      validator. -/
  with_proposal_input_id_proposer : ∀ (contract : M.Contract) (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig) (nd : DecoupledConsensusModel.Protocol.Node V) (st : M.HS)
    (P : Protocol.ProposalInput V) (hP : M.with_proposal_input contract E hc nd st id ⇢ P),
    P.proposer = nd.val_index
  /-- The slot of every outcome `P` of the proposal input at `st` is `st`'s slot. -/
  with_proposal_input_id_slot : ∀ (contract : M.Contract) (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig) (nd : DecoupledConsensusModel.Protocol.Node V) (st : M.HS)
    (P : Protocol.ProposalInput V) (hP : M.with_proposal_input contract E hc nd st id ⇢ P),
    P.slot = st.toFG.toSG.toGoldfishStore.s
  /-- The root of every outcome `P` of the proposal input at `st` for the node `nd` is the root `nd`
      gives `P`'s slot. -/
  with_proposal_input_id_root : ∀ (contract : M.Contract) (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig) (nd : DecoupledConsensusModel.Protocol.Node V) (st : M.HS)
    (P : Protocol.ProposalInput V) (hP : M.with_proposal_input contract E hc nd st id ⇢ P),
    P.root = nd.new_root P.slot
  /-- For every outcome `C` of the carried rows of the named store `st` and every outcome `O` of
      `st`'s ordered bodies, a row is in `C` exactly when some block of `O` is eligible, includes
      the row, and the row's round is in `st`'s window. -/
  mem_carried_rows : ∀ (hc : DecoupledConsensusModel.Protocol.HealConfig) (st : M.NS) (row : DecoupledConsensusModel.NamedAttestation V)
    (C : List (DecoupledConsensusModel.NamedAttestation V)) (hC : M.carriedRows hc st ⇢ C)
    (O : List (DecoupledConsensusModel.NamedBlock V)) (hO : M.orderedBodies st ⇢ O),
    row ∈ C ↔ ∃ B ∈ O, M.eligibleBody hc st B = Bool.true ∧ row ∈ B.attestations ∧ M.inWindow hc st.core row.round = Bool.true
  /-- Every row of the proposal rows built on `parent` from `rows` is among `rows` and is not among
      the rows the chain of `parent` already includes. -/
  mem_proposalRows : ∀ (parent : DecoupledConsensusModel.NamedBlock V) (rows : List (DecoupledConsensusModel.NamedAttestation V)), ∀ row ∈ M.proposalRows parent rows, row ∈ rows ∧ row ∉ M.chainRows parent
  /-- If `row` is among `rows`, is not among the rows the chain of `parent` includes, and no other
      row of `rows` has its signer and round, then `row` is among the proposal rows built on
      `parent` from `rows`. -/
  mem_proposalRows_of_unique : ∀ (parent : DecoupledConsensusModel.NamedBlock V) (rows : List (DecoupledConsensusModel.NamedAttestation V)), ∀ row ∈ rows, row ∉ M.chainRows parent → (∀ b ∈ rows, b.val_index = row.val_index → b.round = row.round → b = row) → row ∈ M.proposalRows parent rows
  /-- Every block of every outcome of the ordered bodies of the named store `st` is among `st`'s
      bodies. -/
  ordered_bodies_mem : ∀ {st : M.NS} {B : DecoupledConsensusModel.NamedBlock V} (O : List (DecoupledConsensusModel.NamedBlock V)), M.orderedBodies st ⇢ O → B ∈ O → B ∈ st.bodies
  /-- A pool row of the named store `st` is among `st`'s processed rows. -/
  mem_processedRows_of_mem_poolRows : ∀ (hc : DecoupledConsensusModel.Protocol.HealConfig) (st : M.NS) {a : DecoupledConsensusModel.NamedAttestation V}, a ∈ M.poolRows hc st → a ∈ M.processedRows hc st
  /-- For every outcome `D` of the attestation duty on the named store `st` and every outcome `G` of
      the contract's grade read at the round of `st`'s slot, the `confirmed` field of `D`'s
      attestation is the root of the block `contract.sgVote` picks under `G`. -/
  namedDuties_attest_with_confirmed : ∀ (contract : M.Contract) (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig) (nd : DecoupledConsensusModel.Protocol.Node V) (st : M.NS) (record : M.NR)
    (D : M.NS × M.NR × NamedAttestation V) (hD : M.duties_attest_with contract E hc nd st record ⇢ D)
    (G : GradeRead V) (hG : contract.read E hc (M.toHealing st.core) (M.round_of hc (M.toHealing st.core).toFG.toSG.toGoldfishStore.s) ⇢ G),
    D.2.2.confirmed = Option.some (contract.sgVote (M.toHealing st.core) G).root
  /-- For every outcome `A` of the round action at the healing store `st` and every outcome `I` of
      the attestation input at `st`, the height pair of `A`'s row is `M.encodeHeight` applied to
      `I`'s height fields and some height pair. -/
  round_action_with_height_pair_input : ∀ (contract : M.Contract) (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig) (nd : DecoupledConsensusModel.Protocol.Node V) (st : M.HS) (record : M.NR)
    (A : M.NR × NamedAttestation V) (hA : M.round_action_with contract E hc nd st record ⇢ A)
    (I : Protocol.AttestationInput V) (hI : M.with_attestation_input contract E hc nd st id ⇢ I),
    ∃ pair, A.2.height_pair = M.encodeHeight I.fields pair
  /-- Every outcome `D` of the attestation duty at `st` leaves the time `t` and the current slot `s`
      of the core store unchanged. -/
  named_attest_clock : ∀ (gc : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : M.NS) (record : M.NR)
    (D : M.NS × M.NR × NamedAttestation V) (hD : M.duties_attest_with gc E hc nd st record ⇢ D),
    D.1.core.t = st.core.t ∧ D.1.core.s = st.core.s
  /-- Every outcome `D` of the confirmation duty at `st` leaves the time `t` and the current slot
      `s` of the core store unchanged. -/
  named_confirmation_clock : ∀ (gc : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (st : M.NS) (s : Slot)
    (D : M.NS) (hD : M.duties_update_confirmation_with gc E hc st s ⇢ D),
    D.core.t = st.core.t ∧ D.core.s = st.core.s
  /-- Every outcome `D` of the proposal duty at `st` leaves the time `t` and the current slot `s` of
      the core store unchanged. -/
  named_propose_clock : ∀ (gc : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (cfg : HeightConfig) (nd : Protocol.Node V) (st : M.NS)
    (D : M.NS × Option (NamedBlock V)) (hD : M.duties_propose_block_with gc E hc cfg nd st ⇢ D),
    D.1.core.t = st.core.t ∧ D.1.core.s = st.core.s
  /-- Every outcome `D` of the Goldfish-vote duty at `st` leaves the time `t` and the current slot
      `s` of the core store unchanged. -/
  named_vote_clock : ∀ (gc : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : M.NS)
    (D : M.NS × Option (GoldfishVote V)) (hD : M.duties_goldfish_vote_with gc E hc nd st ⇢ D),
    D.1.core.t = st.core.t ∧ D.1.core.s = st.core.s
  /-- If the block of an outcome `D` of the proposal duty at `st` is `B`, then the slot of `B` is
      the current slot of `st`'s core store. -/
  propose_block_with_slot : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (nd : Protocol.Node V) (st : M.NS) {B : NamedBlock V}
    (D : M.NS × Option (NamedBlock V)) (hD : M.duties_propose_block_with contract E hc cfg nd st ⇢ D)
    (hB : D.2 = some B), B.slot = st.core.s
  /-- For every outcome `D` of the attestation duty at `st` with the record `record` and every
      outcome `A` of the round action at `st`'s healing view with that record, the row of `D` is the
      row of `A`. -/
  attest_with_row : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : M.NS) (record : M.NR)
    (D : M.NS × M.NR × NamedAttestation V) (hD : M.duties_attest_with contract E hc nd st record ⇢ D)
    (A : M.NR × NamedAttestation V) (hA : M.round_action_with contract E hc nd (M.toHealing st.core) record ⇢ A),
    D.2.2 = A.2
  /-- If, for an outcome `G` of the contract's grade read, `M.deepest_clear` from the candidate `q`
      along the store's `live_confirmed` chain under `G`'s clearance test is `W`, then every outcome
      of the FG source at `q` is `W`. -/
  fg_source_with_some_of_deepest_clear : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (st : M.HS) (r : Round) {q W : Block V}
    (G : GradeRead V) (hG : contract.read E hc st r ⇢ G)
    (h : M.deepest_clear (some q) st.toFG.toSG.toGoldfishStore.live_confirmed G.clear = some W)
    (o : Option (Block V)) (ho : M.fg_source_with contract E hc st r (some q) ⇢ o), o = some W
  /-- If, for an outcome `G` of the contract's grade read, `M.deepest_clear` from the candidate `q`
      along the store's `live_confirmed` chain under `G`'s clearance test is `none`, then every
      outcome of the FG source at `q` is `q`. -/
  fg_source_with_some_of_deepest_clear_none : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (st : M.HS) (r : Round) {q : Block V}
    (G : GradeRead V) (hG : contract.read E hc st r ⇢ G)
    (h : M.deepest_clear (some q) st.toFG.toSG.toGoldfishStore.live_confirmed G.clear = none)
    (o : Option (Block V)) (ho : M.fg_source_with contract E hc st r (some q) ⇢ o), o = some q
  /-- Under the grade contract of the cache `c`, for every outcome `A2` of the grade-2 candidate at
      the store `st` and round `r`, every outcome `G` of the contract's grade read at `st` and `r`,
      and every outcome `W` of the SG vote at `st` and `r` from `A2`, `W` is `M.currentSGVote st G`. -/
  get_sg_vote_with_gradeContract_grade2 : ∀ (c : M.Cache) (E : Env V) (hc : Protocol.HealConfig) (st : M.HS) (r : Round)
    (A2 : Option (Block V)) (hA2 : M.grade2_block_with (M.gradeContract c) E hc st r ⇢ A2)
    (G : GradeRead V) (hG : (M.gradeContract c).read E hc st r ⇢ G)
    (W : Block V) (hW : M.get_sg_vote_with (M.gradeContract c) E hc st r A2 ⇢ W),
    W = M.currentSGVote st G
  /-- Under the grade contract of the cache `c`, if, for an outcome `G` of the contract's grade
      read, `M.deepest_clear` from `G`'s anchor along the store's `live_confirmed` chain under `G`'s
      clearance test is `B`, then every outcome of the SG vote is `B`, whatever grade-2 candidate is
      supplied. -/
  get_sg_vote_with_gradeContract_of_deepest_clear : ∀ (c : M.Cache) (E : Env V) (hc : Protocol.HealConfig) (st : M.HS) (r : Round) (A_G2 : Option (Block V)) {B : Block V}
    (G : GradeRead V) (hG : (M.gradeContract c).read E hc st r ⇢ G)
    (h : M.deepest_clear (some G.anchor) st.toFG.toSG.toGoldfishStore.live_confirmed G.clear = some B)
    (W : Block V) (hW : M.get_sg_vote_with (M.gradeContract c) E hc st r A_G2 ⇢ W), W = B
  /-- For every outcome `G` of the contract's grade read at `st` and `r`, every outcome of the
      grade-2 candidate at `st` and `r` is the grade-2 candidate `G.Q2`. -/
  grade2_block_with_eq_read_Q2 : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (st : M.HS) (r : Round)
    (G : GradeRead V) (hG : contract.read E hc st r ⇢ G)
    (Q : Option (Block V)) (hQ : M.grade2_block_with contract E hc st r ⇢ Q), Q = G.Q2
  /-- The round `r` is in the window of the store `st` exactly when
      `M.round_of hc st.s − hc.η_SG ≤ r ≤ M.round_of hc st.s`. -/
  inWindow_eq_true_iff : ∀ (hc : Protocol.HealConfig) (st : M.S) (r : Round), M.inWindow hc st r = true ↔
    (M.round_of hc st.s) - hc.η_SG ≤ r ∧ r ≤ (M.round_of hc st.s)
  /-- Every outcome of the confirmation duty has the bodies of `st`. -/
  named_update_confirmation_with_bodies : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (st : M.NS) (s : Slot)
    (D : M.NS) (hD : M.duties_update_confirmation_with contract E hc st s ⇢ D), D.bodies = st.bodies
  /-- For every outcome `D` of the confirmation duty and every outcome `X` of the confirmation
      update of `st`'s core store, with the same contract, environment, configuration and slot, the
      core store of `D` is `X`. -/
  named_update_confirmation_with_core : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (st : M.NS) (s : Slot)
    (D : M.NS) (hD : M.duties_update_confirmation_with contract E hc st s ⇢ D)
    (X : M.S) (hX : M.update_confirmation_with contract E hc st.core s ⇢ X), D.core = X
  /-- If an outcome of the proposal duty at `st` is the block `B`, then the slot of `B` is the slot
      of `st`'s core store. -/
  ModelProperties_proposal_with_slot : ∀ (contract : M.Contract) (source : Protocol.ProposalRowSource) (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : M.NS) (B : NamedBlock V)
    (o : Option (NamedBlock V)) (ho : M.proposal_with contract source E hc nd st ⇢ o) (h : o = some B), B.slot = st.core.s
  /-- If the block of an outcome `D` of the proposal duty at `st` is `B`, then `D` is the pair of
      `B` and the store `M.on_block_with .alsoCarried` returns on `B`, with the grade cache
      `M.contractCache contract` written into it. The hypothesis `hn`, that `st` is a reached store,
      defaults to `trivial`. -/
  propose_block_with_eq_of_snd : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (nd : Protocol.Node V) (st : M.NS) {B : NamedBlock V}
    (D : M.NS × Option (NamedBlock V)) (hD : M.duties_propose_block_with contract E hc cfg nd st ⇢ D)
    (h : D.2 = some B) (hn : M.reachedStore st := by trivial), D = (M.store_with_cache (M.on_block_with .alsoCarried E hc cfg st B) (M.contractCache contract), some B)
  /-- If an outcome of the proposal at `st` is absent, the store of every outcome of the proposal
      duty is `st`. -/
  propose_block_with_fst_of_none : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (nd : Protocol.Node V) (st : M.NS)
    (o : Option (NamedBlock V)) (ho : M.proposal_with contract .poolAndCarried E hc nd st ⇢ o) (h : o = none)
    (D : M.NS × Option (NamedBlock V)) (hD : M.duties_propose_block_with contract E hc cfg nd st ⇢ D), D.1 = st
  /-- If an outcome of the proposal at `st` is the block `B`, the store of every outcome of the
      proposal duty is the store `M.on_block_with .alsoCarried` returns on `B`, with the grade cache
      `M.contractCache contract` written into it. The hypothesis `hn`, that `st` is a reached store,
      defaults to `trivial`. -/
  propose_block_with_fst_of_some : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (nd : Protocol.Node V) (st : M.NS) {B : NamedBlock V}
    (o : Option (NamedBlock V)) (ho : M.proposal_with contract .poolAndCarried E hc nd st ⇢ o) (h : o = some B)
    (D : M.NS × Option (NamedBlock V)) (hD : M.duties_propose_block_with contract E hc cfg nd st ⇢ D)
    (hn : M.reachedStore st := by trivial),
    D.1 = M.store_with_cache (M.on_block_with .alsoCarried E hc cfg st B) (M.contractCache contract)
  /-- If, for an outcome `A2` of the grade-2 candidate for round `r`, an outcome of the FG source at
      `A2` is some block, then every outcome `G` of the contract's grade read for round `r` has some
      grade-2 candidate. -/
  read_Q2_isSome_of_fg_source_with_grade2 : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (st : M.HS) (r : Round) {B : Block V}
    (A2 : Option (Block V)) (hA2 : M.grade2_block_with contract E hc st r ⇢ A2)
    (o : Option (Block V)) (ho : M.fg_source_with contract E hc st r A2 ⇢ o) (h : o = some B)
    (G : GradeRead V) (hG : contract.read E hc st r ⇢ G), ∃ A, G.Q2 = some A
  /-- For every outcome `A` of the round action at the store `st`, every outcome `A2` of the grade-2
      candidate at the round of `st`'s slot, and every outcome `W` of the SG vote at that round from
      `A2`, the confirmed root of `A`'s row is the root of `W`. -/
  round_action_with_confirmed : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : M.HS) (record : M.NR)
    (A : M.NR × NamedAttestation V) (hA : M.round_action_with contract E hc nd st record ⇢ A)
    (A2 : Option (Block V)) (hA2 : M.grade2_block_with contract E hc st ((M.round_of hc st.toFG.toSG.toGoldfishStore.s)) ⇢ A2)
    (W : Block V) (hW : M.get_sg_vote_with contract E hc st ((M.round_of hc st.toFG.toSG.toGoldfishStore.s)) A2 ⇢ W),
    A.2.confirmed = some W.root
  /-- The round of the row of every outcome of the round action at the store `st` is the round of
      `st`'s slot. -/
  round_action_with_round : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : M.HS) (record : M.NR)
    (A : M.NR × NamedAttestation V) (hA : M.round_action_with contract E hc nd st record ⇢ A),
    A.2.round = (M.round_of hc st.toFG.toSG.toGoldfishStore.s)
  /-- The validator of the row of every outcome of the round action at the store `st` is the
      validator of the node `nd`. -/
  round_action_with_val_index : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : M.HS) (record : M.NR)
    (A : M.NR × NamedAttestation V) (hA : M.round_action_with contract E hc nd st record ⇢ A),
    A.2.val_index = nd.val_index
  /-- Every outcome `st'` of the confirmation update has the finalized block of `st`. -/
  update_confirmation_with_F : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (st : M.S) (s : Slot) (st' : M.S), M.update_confirmation_with contract E hc st s ⇢ st' → st'.F = st.F
  /-- Every outcome `st'` of the confirmation update has the block tree of `st`. -/
  update_confirmation_with_T : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (st : M.S) (s : Slot) (st' : M.S), M.update_confirmation_with contract E hc st s ⇢ st' → st'.T = st.T
  /-- Every outcome `st'` of the confirmation update has the same `M.store_pool` as `st`: the
      Goldfish votes processed for each slot. -/
  update_confirmation_with_pool : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (st : M.S) (s : Slot) (st' : M.S), M.update_confirmation_with contract E hc st s ⇢ st' → (M.store_pool st') = (M.store_pool st)
  /-- Every outcome `st'` of the confirmation update has the slot of `st`. -/
  update_confirmation_with_s : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (st : M.S) (s : Slot) (st' : M.S), M.update_confirmation_with contract E hc st s ⇢ st' → st'.s = st.s
  /-- The FG root of the healing view of every outcome `st'` of the confirmation update is the FG
      root of the healing view of `st`. -/
  update_confirmation_with_toHealing_fg_root : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (st : M.S) (s : Slot) (st' : M.S), M.update_confirmation_with contract E hc st s ⇢ st' → M.get_fg_root (M.toHealing st').toFG =
    M.get_fg_root (M.toHealing st).toFG
  /-- The filtered block tree of the healing view of every outcome `st'` of the confirmation update
      is the filtered block tree of the healing view of `st`. -/
  update_confirmation_with_toHealing_filtered : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (st : M.S) (s : Slot) (st' : M.S), M.update_confirmation_with contract E hc st s ⇢ st' → M.get_filtered_block_tree
    (M.toHealing st').toFG =
    M.get_filtered_block_tree (M.toHealing st).toFG
  /-- The grade view of the healing view of every outcome `st'` of the confirmation update is the
      grade view of the healing view of `st`. The hypothesis `hn`, that `st` is a reached core
      store, defaults to `trivial`. -/
  update_confirmation_with_toHealing_gradeView : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (st : M.S) (s : Slot) (st' : M.S), M.update_confirmation_with contract E hc st s ⇢ st' → ∀ (hn : M.reachedCore st := by trivial), (M.gradeView (M.toHealing st')) =
    (M.gradeView (M.toHealing st))
  /-- Every outcome `D` of the confirmation duty at `st` for the slot `s` has the bodies and the SG
      rows of `st`. -/
  confirmation_metadata : ∀ (gc : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (st : M.NS) (s : Slot)
    (D : M.NS) (hD : M.duties_update_confirmation_with gc E hc st s ⇢ D),
    D.bodies = st.bodies ∧ D.sg_rows = st.sg_rows
  /-- The named store of every outcome `D` of the Goldfish-vote duty at `st` has the bodies and the
      SG rows of `st`. -/
  goldfish_vote_metadata : ∀ (gc : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : M.NS)
    (D : M.NS × Option (GoldfishVote V)) (hD : M.duties_goldfish_vote_with gc E hc nd st ⇢ D),
    D.1.bodies = st.bodies ∧ D.1.sg_rows = st.sg_rows
  /-- If an outcome of the proposal at `st` with the row source `.poolAndCarried` is no block, then
      every outcome of the proposal duty is `(st, none)`. -/
  propose_none : ∀ (gc : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (nd : Protocol.Node V) (st : M.NS)
    (o : Option (NamedBlock V)) (ho : M.proposal_with gc .poolAndCarried E hc nd st ⇢ o) (h : o = none)
    (D : M.NS × Option (NamedBlock V)) (hD : M.duties_propose_block_with gc E hc cfg nd st ⇢ D), D = (st, none)
  /-- The core store of the named store of every outcome `D` of the Goldfish-vote duty at `st` has
      the SG votes `sg_votes` of `st`'s core store. -/
  goldfish_vote_with_sg_votes : ∀ (contract : M.Contract) (E : Env V) (hc : HealConfig) (nd : Protocol.Node V) (st : M.NS)
    (D : M.NS × Option (GoldfishVote V)) (hD : M.duties_goldfish_vote_with contract E hc nd st ⇢ D),
    D.1.core.sg_votes = st.core.sg_votes
  /-- If an outcome of the proposal at `st` with the row source `source` is the block `B`, then the
      Goldfish votes of `B` are the Goldfish votes `st`'s core store holds for the slot before its
      current slot. -/
  proposal_with_gf_votes : ∀ (contract : M.Contract) (source : Protocol.ProposalRowSource) (E : Env V) (hc : HealConfig) (nd : Protocol.Node V) (st : M.NS) {B : NamedBlock V}
    (o : Option (NamedBlock V)) (ho : M.proposal_with contract source E hc nd st ⇢ o) (hB : o = some B), B.gf_votes = st.core.gf_votes (st.core.s - 1)
  /-- If an outcome of the proposal at `st` with the row source `source` is the block `B`, then the
      slot of `B` is the current slot of `st`'s core store. -/
  Optimistic_proposal_with_slot : ∀ (contract : M.Contract) (source : Protocol.ProposalRowSource) (E : Env V) (hc : HealConfig) (nd : Protocol.Node V) (st : M.NS) {B : NamedBlock V}
    (o : Option (NamedBlock V)) (ho : M.proposal_with contract source E hc nd st ⇢ o) (hB : o = some B), B.slot = st.core.s
  /-- The finalized block of `st`'s core store is an ancestor of, or equal to, the finalized block
      of the core store of every outcome of the proposal duty at `st`. -/
  propose_block_with_F : ∀ (gc : M.Contract) (E : Env V) (hc : HealConfig) (cfg : HeightConfig) (nd : Protocol.Node V) (st : M.NS)
    (D : M.NS × Option (NamedBlock V)) (hD : M.duties_propose_block_with gc E hc cfg nd st ⇢ D),
    Block.Preceq st.core.F D.1.core.F
  /-- Every outcome of the attestation duty keeps the `live_confirmed` block of the core store. -/
  Sts_attest_with_live_confirmed : ∀ (gc : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : M.NS) (record : M.NR)
    (D : M.NS × M.NR × NamedAttestation V) (hD : M.duties_attest_with gc E hc nd st record ⇢ D),
    D.1.core.live_confirmed = st.core.live_confirmed
  /-- Every outcome of the attestation duty keeps the `latest_stable` and `latest_confirmed` of the
      core store. -/
  attest_with_records : ∀ (gc : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : M.NS) (record : M.NR)
    (D : M.NS × M.NR × NamedAttestation V) (hD : M.duties_attest_with gc E hc nd st record ⇢ D),
    D.1.core.latest_stable = st.core.latest_stable ∧
    D.1.core.latest_confirmed = st.core.latest_confirmed
  /-- If the row `a` is among the processed rows of the named store `st`, then `a` is among `st`'s
      SG rows of some round. -/
  exists_sg_rows_of_mem_processedRows : ∀ (hc : Protocol.HealConfig) (st : M.NS) {a : NamedAttestation V} (h : a ∈ M.processedRows hc st), ∃ k : Round, a ∈ st.sg_rows k
  /-- If an outcome of the FG source at the grade-2 candidate `A_G2` is the block `Cfg`, then `Cfg`
      is an ancestor of, or equal to, the store's `live_confirmed` block, or `A_G2 = some Cfg`. -/
  fg_source_cases : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (st : M.HS) (r₁ : Round) {A_G2 : Option (Block V)} {Cfg : Block V}
    (o : Option (Block V)) (ho : M.fg_source_with contract E hc st r₁ A_G2 ⇢ o) (h : o = some Cfg),
    Block.Preceq Cfg st.toFG.toSG.toGoldfishStore.live_confirmed ∨ A_G2 = some Cfg
  /-- If an outcome of the FG source at the grade-2 candidate `A_G2` is `B`, then `A_G2` is some
      block `q` with `q ⪯ B`. -/
  fg_source_with_some : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (st : M.HS) (r : Round) {A_G2 : Option (Block V)} {B : Block V}
    (o : Option (Block V)) (ho : M.fg_source_with contract E hc st r A_G2 ⇢ o) (h : o = some B),
    ∃ q : Block V, A_G2 = some q ∧ Block.Preceq q B
  /-- The round `r` is in the window of the store `st` exactly when
      `M.round_of hc st.s − hc.η_SG ≤ r ≤ M.round_of hc st.s`. -/
  inWindow_iff : ∀ (hc : Protocol.HealConfig) (st : M.S) (r : Round), M.inWindow hc st r = true ↔
    (M.round_of hc st.s) - hc.η_SG ≤ r ∧ r ≤ (M.round_of hc st.s)
  /-- A processed row of the named store `st` whose round is in `st`'s window is in every outcome of
      the rows `M.select source hc st`, for either row source. -/
  mem_select_of_processed_inWindow : ∀ (source : Protocol.ProposalRowSource) (hc : Protocol.HealConfig) (st : M.NS) {a : NamedAttestation V} (hproc : a ∈ M.processedRows hc st) (hw : M.inWindow hc st.core a.round = true)
    (L : List (NamedAttestation V)) (hL : M.select source hc st ⇢ L), a ∈ L
  /-- The named store of every outcome `D` of the attestation duty at `st` is the store
      `M.admit_row` returns when it admits `D`'s row into `st`, with the grade cache
      `M.contractCache contract` written into it. The hypothesis `hn`, that `st` is a reached store,
      defaults to `trivial`. -/
  namedDuties_attest_with_fst : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : M.NS) (record : M.NR)
    (D : M.NS × M.NR × NamedAttestation V) (hD : M.duties_attest_with contract E hc nd st record ⇢ D)
    (hn : M.reachedStore st := by trivial),
    D.1 = M.store_with_cache (M.admit_row hc st D.2.2) (M.contractCache contract)
  /-- For every outcome `D` of the attestation duty on `st` and every outcome `A` of the round
      action on `st`'s healing view with the record `record`, the named store of `D` is the store
      `M.admit_row` returns on `st` for `A`'s attestation, with the grade cache
      `M.contractCache contract` written into it. The hypothesis `hn`, that `st` is a reached store,
      defaults to `trivial`. -/
  namedDuties_attest_with_fst_eq_round_action : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : M.NS) (record : M.NR)
    (D : M.NS × M.NR × NamedAttestation V) (hD : M.duties_attest_with contract E hc nd st record ⇢ D)
    (A : M.NR × NamedAttestation V) (hA : M.round_action_with contract E hc nd (M.toHealing st.core) record ⇢ A)
    (hn : M.reachedStore st := by trivial),
    D.1 = M.store_with_cache (M.admit_row hc st A.2) (M.contractCache contract)
  /-- For every outcome `D` of the named Goldfish-vote duty and every outcome `G` of the
      Goldfish-vote duty on the named store's core store, the core store of `D`'s named store is
      `G`'s store. -/
  namedDuties_goldfish_vote_with_fst_core : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : M.NS)
    (D : M.NS × Option (GoldfishVote V)) (hD : M.duties_goldfish_vote_with contract E hc nd st ⇢ D)
    (G : M.S × Option (GoldfishVote V)) (hG : M.goldfish_vote_with contract E hc nd st.core ⇢ G),
    D.1.core = G.1
  /-- For every outcome `D` of the named Goldfish-vote duty on `st` and every outcome `G` of the
      Goldfish-vote duty on the core store of `st`, the vote, if any, of `D` is the vote of `G`. -/
  namedDuties_goldfish_vote_with_snd : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : M.NS)
    (D : M.NS × Option (GoldfishVote V)) (hD : M.duties_goldfish_vote_with contract E hc nd st ⇢ D)
    (G : M.S × Option (GoldfishVote V)) (hG : M.goldfish_vote_with contract E hc nd st.core ⇢ G),
    D.2 = G.2
  /-- Every outcome of the confirmation duty on the named store `st` has the bodies of `st`. -/
  namedDuties_update_confirmation_with_bodies : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (st : M.NS) (s : Slot)
    (D : M.NS) (hD : M.duties_update_confirmation_with contract E hc st s ⇢ D), D.bodies = st.bodies
  /-- For every outcome `D` of the named confirmation duty and every outcome `X` of the confirmation
      update of the core store, the core store of `D` is `X`. -/
  namedDuties_update_confirmation_with_core : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (st : M.NS) (s : Slot)
    (D : M.NS) (hD : M.duties_update_confirmation_with contract E hc st s ⇢ D)
    (X : M.S) (hX : M.update_confirmation_with contract E hc st.core s ⇢ X), D.core = X
  /-- A block `B` that an outcome of the proposal at the named store `st` names includes only
      attestations whose round is at most the round of `B`'s slot
      (`M.carried_attestations_admissible`). -/
  proposal_with_carried_admissible_inclG2 : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : M.NS) {B : NamedBlock V}
    (o : Option (NamedBlock V)) (ho : M.proposal_with contract .poolAndCarried E hc nd st ⇢ o) (hB : o = some B),
    M.carried_attestations_admissible hc B.erase = true
  /-- If an outcome of the proposal duty at the named store `st` proposes the block `B`, then every
      outcome of the proposal at `st` with the row source `.poolAndCarried` is `B`. -/
  proposal_with_eq_of_propose_block_with_snd : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (nd : Protocol.Node V) (st : M.NS) {B : NamedBlock V}
    (D : M.NS × Option (NamedBlock V)) (hD : M.duties_propose_block_with contract E hc cfg nd st ⇢ D) (h : D.2 = some B)
    (o : Option (NamedBlock V)) (ho : M.proposal_with contract .poolAndCarried E hc nd st ⇢ o), o = some B
  /-- If an outcome of the proposal with the row source `source` at the named store `st` is the
      block `B`, then every support vote included in `B` is among the Goldfish votes included in
      `B`. -/
  proposal_with_gf_support_subset : ∀ (contract : M.Contract) (source : Protocol.ProposalRowSource) (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : M.NS) {B : NamedBlock V}
    (o : Option (NamedBlock V)) (ho : M.proposal_with contract source E hc nd st ⇢ o) (h : o = some B),
    ∀ u ∈ B.gf_support_votes, u ∈ B.gf_votes
  /-- If an outcome of the proposal duty at `st` proposes the block `B`, then every outcome of the
      proposal at `st` with the row source `.poolAndCarried` is `B`. -/
  proposal_with_of_propose_block_with : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (nd : Protocol.Node V) (st : M.NS) {B : NamedBlock V}
    (D : M.NS × Option (NamedBlock V)) (hD : M.duties_propose_block_with contract E hc cfg nd st ⇢ D) (hB : D.2 = some B)
    (o : Option (NamedBlock V)) (ho : M.proposal_with contract .poolAndCarried E hc nd st ⇢ o), o = some B
  /-- If an outcome of the proposal at `st` with the row source `.poolAndCarried` is the block `B`,
      then every support vote included in `B` is among the Goldfish votes included in `B`. -/
  proposal_with_support_subset : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : M.NS) {B : NamedBlock V}
    (o : Option (NamedBlock V)) (ho : M.proposal_with contract .poolAndCarried E hc nd st ⇢ o) (hB : o = some B),
    ∀ u ∈ B.gf_support_votes, u ∈ B.gf_votes
  /-- If an outcome of the proposal at `st` with the row source `.poolAndCarried` is the block `B`,
      then the block of every outcome of the proposal duty at `st` is `B`. -/
  propose_block_with_snd_of_some : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (nd : Protocol.Node V) (st : M.NS) {B : NamedBlock V}
    (o : Option (NamedBlock V)) (ho : M.proposal_with contract .poolAndCarried E hc nd st ⇢ o) (h : o = some B)
    (D : M.NS × Option (NamedBlock V)) (hD : M.duties_propose_block_with contract E hc cfg nd st ⇢ D), D.2 = some B
  /-- A block that an outcome of the proposal duty of the node `nd` emits names `nd`'s validator as
      its proposer. -/
  proposer_of_propose_block_with : ∀ (gc : M.Contract) (E : Env V) (hc : HealConfig) (cfg : HeightConfig) (nd : Node V) (st : M.NS) (B : NamedBlock V)
    (D : M.NS × Option (NamedBlock V)) (hD : M.duties_propose_block_with gc E hc cfg nd st ⇢ D) (h : D.2 = some B),
    B.proposer? = some nd.val_index
  /-- If an outcome of the contract's grade read at the store `st`, for the round of `st`'s slot,
      has no grade-2 candidate, then the attestation of every outcome of the round action at `st`
      carries the empty height pair. -/
  round_action_with_height_pair_of_Q2_none : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : M.HS) (record : M.NR)
    (G : GradeRead V) (hG : contract.read E hc st ((M.round_of hc st.toFG.toSG.toGoldfishStore.s)) ⇢ G) (h : G.Q2 = none)
    (A : M.NR × NamedAttestation V) (hA : M.round_action_with contract E hc nd st record ⇢ A),
    A.2.height_pair = NamedHeightPair.empty
  /-- Every outcome `st'` of the confirmation update has the Goldfish votes `gf_votes` of `st`. -/
  update_confirmation_with_gf_votes : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (st : M.S) (s : Slot) (st' : M.S), M.update_confirmation_with contract E hc st s ⇢ st' → st'.gf_votes = st.gf_votes
  /-- Every outcome `st'` of the confirmation update has the time `t` of `st`. -/
  update_confirmation_with_t : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (st : M.S) (s : Slot) (st' : M.S), M.update_confirmation_with contract E hc st s ⇢ st' → st'.t = st.t
  /-- Every outcome `st'` of the confirmation update has the Goldfish-vote stamps `timestamp_vote`
      of `st`. -/
  update_confirmation_with_timestamp_vote : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (st : M.S) (s : Slot) (st' : M.S), M.update_confirmation_with contract E hc st s ⇢ st' → st'.timestamp_vote = st.timestamp_vote
  /-- Every outcome `st'` of the confirmation update has, in its healing view, the justified block
      `J` of `st`. -/
  update_confirmation_with_toHealing_J : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (st : M.S) (s : Slot) (st' : M.S), M.update_confirmation_with contract E hc st s ⇢ st' → (M.toHealing st').toFG.J = (M.toHealing st).toFG.J
  /-- Every outcome `st'` of the confirmation update has, in its healing view, the justified height
      `h_j` of `st`. -/
  update_confirmation_with_toHealing_h_j : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (st : M.S) (s : Slot) (st' : M.S), M.update_confirmation_with contract E hc st s ⇢ st' → (M.toHealing st').toFG.h_j
    = (M.toHealing st).toFG.h_j
  /-- Every outcome `st'` of the confirmation update has, in its healing view, the height maximum
      `h_max` of `st`. -/
  update_confirmation_with_toHealing_h_max : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (st : M.S) (s : Slot) (st' : M.S), M.update_confirmation_with contract E hc st s ⇢ st' → (M.toHealing st').toFG.h_max
    = (M.toHealing st).toFG.h_max
  /-- Every outcome `st'` of the confirmation update has, in its healing view, the slot of `st`. -/
  update_confirmation_with_toHealing_s : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (st : M.S) (s : Slot) (st' : M.S), M.update_confirmation_with contract E hc st s ⇢ st' → (M.toHealing st').toFG.toSG.toGoldfishStore.s = (M.toHealing st).toFG.toSG.toGoldfishStore.s
  /-- The Goldfish-vote duty on every named store has an outcome. -/
  goldfish_vote_with_nonempty : ∀ (gc : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : M.NS),
    ∃ D : M.NS × Option (GoldfishVote V), M.duties_goldfish_vote_with gc E hc nd st ⇢ D
  /-- If `v`'s tick at time `t` from the node state `n` has an outcome, `t` is the proposal time of
      a positive slot whose proposer is `v`, and `n` passes the grade-1 awake test of that slot's
      round, then for every outcome `c` of the phase tick at `t`, the proposal duty under the frame
      contract of `c`, run for `v` on `n`'s store with its clock set to `t`, has an outcome. The
      hypotheses `hn`, that `n` is a reached node state, and `hruns`, that `n` runs as `v`, default
      to `trivial`. -/
  propose_block_with_nonempty : ∀ (S : Setup V) (v : V) (n : M.N) (t : Time)
    (out : M.N × List (NamedObject V)) (hout : M.tick S v n t ⇢ out)
    (hs : 0 < S.E.slotOf t) (ht : t = M.proposal_time S.E (S.E.slotOf t))
    (hv : S.E.proposer (S.E.slotOf t) = v)
    (hawake : M.awake_for_grade1 S v n (M.round_of S.hc (S.E.slotOf t)))
    (c : M.Cache) (hc : M.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache ⇢ c)
    (hn : M.reachedNode n := by trivial) (hruns : M.runs_as n v := by trivial),
    ∃ D : M.NS × Option (NamedBlock V),
      M.duties_propose_block_with (M.frameContract c) S.E S.hc S.cfg (S.node v)
        (M.ns_setClock S.E n.st t) ⇢ D
  /-- The round action has an outcome. -/
  round_action_with_nonempty : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig)
    (nd : Protocol.Node V) (st : M.HS) (record : M.NR),
    ∃ A, M.round_action_with contract E hc nd st record ⇢ A
  /-- The attestation input, built with the identity continuation, has an outcome. -/
  with_attestation_input_nonempty : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig)
    (nd : Protocol.Node V) (st : M.HS),
    ∃ I : Protocol.AttestationInput V, M.with_attestation_input contract E hc nd st id ⇢ I
  /-- The attestation duty has an outcome. -/
  attest_with_nonempty : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig)
    (nd : Protocol.Node V) (st : M.NS) (record : M.NR),
    ∃ D, M.duties_attest_with contract E hc nd st record ⇢ D
  /-- The grade-2 block at round `r` has an outcome. -/
  grade2_block_with_nonempty : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig)
    (st : M.HS) (r : Round),
    ∃ A2, M.grade2_block_with contract E hc st r ⇢ A2
  /-- The SG vote at round `r` from `A2` has an outcome. -/
  get_sg_vote_with_nonempty : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig)
    (st : M.HS) (r : Round) (A2 : Option (Block V)),
    ∃ W, M.get_sg_vote_with contract E hc st r A2 ⇢ W
  /-- The confirmation update for slot `s` on `st` has an outcome. -/
  update_confirmation_with_nonempty : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig)
    (st : M.S) (s : Slot),
    ∃ X, M.update_confirmation_with contract E hc st s ⇢ X
  /-- `M.select source hc st` has an outcome. -/
  select_nonempty : ∀ (source : Protocol.ProposalRowSource) (hc : Protocol.HealConfig) (st : M.NS),
    ∃ L : List (NamedAttestation V), M.select source hc st ⇢ L
  /-- The proposal input, built with the identity continuation, has an outcome. -/
  with_proposal_input_nonempty : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig)
    (nd : Protocol.Node V) (st : M.HS),
    ∃ P : Protocol.ProposalInput V, M.with_proposal_input contract E hc nd st id ⇢ P
  /-- The proposal at a named store has an outcome. -/
  proposal_with_nonempty : ∀ (contract : M.Contract) (source : Protocol.ProposalRowSource) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : M.NS),
    ∃ o : Option (NamedBlock V), M.proposal_with contract source E hc nd st ⇢ o
  /-- `M.carriedRows hc st` has an outcome. -/
  carriedRows_nonempty : ∀ (hc : Protocol.HealConfig) (st : M.NS),
    ∃ C : List (NamedAttestation V), M.carriedRows hc st ⇢ C
  /-- `M.orderedBodies st` has an outcome. -/
  orderedBodies_nonempty : ∀ (st : M.NS),
    ∃ O : List (NamedBlock V), M.orderedBodies st ⇢ O
  /-- The confirmation duty on the named store `st` for slot `s` has an outcome. -/
  duties_update_confirmation_with_nonempty : ∀ (contract : M.Contract) (E : Env V)
    (hc : Protocol.HealConfig) (st : M.NS) (s : Slot),
    ∃ st' : M.NS, M.duties_update_confirmation_with contract E hc st s ⇢ st'
  /-- The FG source at round `r` from `A2` has an outcome. -/
  fg_source_with_nonempty : ∀ (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig)
    (st : M.HS) (r : Round) (A2 : Option (Block V)),
    ∃ F, M.fg_source_with contract E hc st r A2 ⇢ F
  /-- If every SG bucket of `st`'s core store is the erasure of `st`'s named rows of that round,
      then the erasures of `st`'s processed rows are the SG votes of the core store's rounds `0` to
      its current round, in order. -/
  processed_rows_erasure : ∀ (hc : Protocol.HealConfig) (st : M.NS),
    (∀ r, st.core.sg_votes r = (st.sg_rows r).map NamedAttestation.erase) →
    (M.processedRows hc st).map NamedAttestation.erase =
      (List.range ((M.round_of hc st.core.s) + 1)).flatMap st.core.sg_votes
  /-- An attestation is among the chain rows of the named block `B` exactly when it is among the
      attestations of `B`'s named chain. -/
  chainRows_iff_named_chain : ∀ (B : NamedBlock V) (a : NamedAttestation V),
    a ∈ M.chainRows B ↔ a ∈ Protocol.named_chain_attestations B
  /-- If the named store `st` is coherent, so is every outcome of the confirmation duty for slot `s`
      on `st`. -/
  coherent_confirmation : ∀ (gc : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig)
    (st : M.NS) (s : Slot),
    Restated.Vocabulary.Proofs.NamedStore.Coherent M E cfg st →
    ∀ D : M.NS, M.duties_update_confirmation_with gc E hc st s ⇢ D →
    Restated.Vocabulary.Proofs.NamedStore.Coherent M E cfg D
  /-- The attestation duty on `st` with the grade cache `c` written into it has the same outcomes as
      the attestation duty on `st`. -/
  duties_attest_with_store_with_cache : ∀ (gc : M.Contract) (E : Env V) (hc : Protocol.HealConfig)
    (nd : Protocol.Node V) (st : M.NS) (c : M.Cache) (record : M.NR),
    M.duties_attest_with gc E hc nd (M.store_with_cache st c) record =
      M.duties_attest_with gc E hc nd st record
  /-- If `D` is an outcome of the confirmation duty for slot `s` on `st` under the grade contract of
      `c`, then `D` with the cache `c` written into it is also an outcome of that duty. -/
  duties_update_confirmation_with_store_with_cache_outcome : ∀ (c : M.Cache) (E : Env V)
    (hc : Protocol.HealConfig) (st : M.NS) (s : Slot) (D : M.NS),
    M.duties_update_confirmation_with (M.gradeContract c) E hc st s ⇢ D →
    M.duties_update_confirmation_with (M.gradeContract c) E hc st s ⇢ M.store_with_cache D c
  /-- The Goldfish-vote duty on `st` with the grade cache `c` written into it has the same outcomes
      as the Goldfish-vote duty on `st`. -/
  duties_goldfish_vote_with_store_with_cache : ∀ (gc : M.Contract) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : M.NS) (c : M.Cache),
    M.duties_goldfish_vote_with gc E hc nd (M.store_with_cache st c) =
      M.duties_goldfish_vote_with gc E hc nd st
  /-- The proposal on `st` with the grade cache `c` written into it has the same outcomes as the
      proposal on `st`. -/
  proposal_with_store_with_cache : ∀ (gc : M.Contract) (src : Protocol.ProposalRowSource)
    (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : M.NS) (c : M.Cache),
    M.proposal_with gc src E hc nd (M.store_with_cache st c) = M.proposal_with gc src E hc nd st

/-- Facts about runs of the duty and tick family of `M`; it has no field. -/
structure DutiesRunFacts (M : Model V) : Prop where


end DecoupledConsensusModel.Sts.Record
