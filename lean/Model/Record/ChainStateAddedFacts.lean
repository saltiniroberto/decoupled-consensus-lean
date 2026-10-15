import Model.Record.Wiring
import Proofs.Vocabulary.Protocol.ChainState.NjGap
import Model.Record.ModelSpellings
import Model.Conditions.Vocabulary_Protocol_ChainState_NjGap
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
import Proofs.Claims.Spec2Claims.Claim13bK_GradeOld
import Proofs.Vocabulary.Protocol.ChainState.FinalityComparison
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedCeilingStep
import Proofs.Vocabulary.ModelProperties.Block_parent
import Proofs.Vocabulary.ModelProperties.update_finality
import Proofs.Vocabulary.Protocol.ChainState.DerivationGeometry
import Proofs.Vocabulary.Protocol.ValidatorClient.SlashableBound
import Proofs.Vocabulary.Protocol.Schedule.SlotInduction
import Proofs.Vocabulary.Protocol.ChainState.W4FKChainFinalityWrite
import Proofs.Vocabulary.Protocol.Duties.Proposals.ProposalRows
import Proofs.Vocabulary.Protocol.ChainState.RawHeightCoverage
import Proofs.Claims.Spec2Claims.Claim13bK_ConfirmedSettle

/-!
# Further facts of the chain-state family

The structure `ChainStateAddedFacts`: facts that the chain-state routines of a model `M : Model V`
satisfy on every input, beyond those of `ChainStateFacts`. The structure `ChainStateAddedRunFacts`
is for facts about runs of the same family, and has no field.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts.Record

open DecoupledConsensusModel.Protocol (HeightConfig)
open DecoupledConsensusModel.Execution (Setup)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Further facts that the chain-state routines of `M` satisfy on every input. -/
structure ChainStateAddedFacts (M : Model V) : Prop where
  /-- If `B` is not genesis, the chain state of `B`'s parent has justified height `h` and justified
      block `J`, each member of some quorum is in that chain state's `finalize` set or signs a row
      of `B` with finality pair `(h, J.root)`, and the parent's finalized height is less than `h`,
      then the chain state derived for `B` has finalized block `J` at finalized height `h`. -/
  namedFinalizedAt_of_finalityQuorumCoveredByChild : ∀ (E : Env V) (cfg : HeightConfig)
    {B : NamedBlock V} {J : Block V} {h : Height},
    B ≠ NamedBlock.genesis →
    ((M.derive_named E cfg B.parent).h_j = h ∧ (M.derive_named E cfg B.parent).J = J ∧
      ∃ Q : Finset V, E.electorate.IsQuorum Q ∧
        ∀ i ∈ Q,
          i ∈ M.finalize (M.derive_named E cfg B.parent) ∨
          ∃ a ∈ B.attestations,
            a.val_index = i ∧
            a.finality_pair = some ⟨h, J.root⟩) →
    (M.derive_named E cfg B.parent).h_F < h →
    (M.derive_named E cfg B).F = J ∧ (M.derive_named E cfg B).h_F = h
  /-- If `B` is not genesis, each member of some quorum is in the target participation of the chain
      state of `B`'s parent or signs a row of `B` that is the target vote for that chain state's
      height and entry, and that chain state's `nj` bit is clear, then the chain state derived for
      `B` has the parent's entry as its justified block, the parent's height as its justified
      height, and the parent's height plus one as its height. -/
  namedJustifiedAt_of_targetQuorumCoveredByChild : ∀ (E : Env V) (cfg : HeightConfig)
    {B : NamedBlock V},
    B ≠ NamedBlock.genesis →
    (∃ Q : Finset V, E.electorate.IsQuorum Q ∧
      ∀ i ∈ Q,
        i ∈ (M.derive_named E cfg B.parent).target_participation ∨
        ∃ a ∈ B.attestations,
          a.val_index = i ∧
          a.height_pair = NamedHeightPair.vote (M.derive_named E cfg B.parent).h
            (M.derive_named E cfg B.parent).T_h.root false) →
    (M.derive_named E cfg B.parent).nj = false →
    ((M.derive_named E cfg B).J = (M.derive_named E cfg B.parent).T_h ∧
      (M.derive_named E cfg B).h_j = (M.derive_named E cfg B.parent).h) ∧
    (M.derive_named E cfg B).h = (M.derive_named E cfg B.parent).h + 1
  /-- The finalized block of `B`'s chain state is an ancestor of, or equal to, its justified block. -/
  derive_named_finalized_preceq_justified : ∀ (E : Env V) (cfg : HeightConfig)
    (B : NamedBlock V),
    Block.preceq (M.derive_named E cfg B).F (M.derive_named E cfg B).J = true
  /-- The grade test passes for every ancestor of a block it passes for: if `A ⪯ B` and the outcome
      of the grade test of round `r` at phase `p` over the grade view `gv` is `true` for `B`, then
      every outcome of the same test for `A` is `true`. -/
  confirmation_phaseGrade_mono : ∀ (E : Env V) (hc : Protocol.HealConfig) (gv : M.GV) (F : Block V)
    (r : Round) (p : Protocol.Phase) {A B : Block V}, Block.Preceq A B →
    ∀ bB : Bool, M.gradeBool E gv F hc.η_SG r (M.early E hc r p) (M.late E hc r p) B ⇢ bB →
    bB = true →
    ∀ bA : Bool, M.gradeBool E gv F hc.η_SG r (M.early E hc r p) (M.late E hc r p) A ⇢ bA →
    bA = true
  /-- If the named rows `a` and `b` have the same validator, `a`'s height pair matches the entry
      `entry` at height `h`, `b`'s finality pair is `(h, finalized)`, and `entry ≠ finalized`, then
      the erasures of `a` and `b` are slashable. -/
  matching_finality_e1 : ∀ (a b : NamedAttestation V) (h : Height) (entry finalized : BlockId),
    a.val_index = b.val_index →
    a.height_pair.matchesEntry h entry = true →
    b.finality_pair = some ⟨h, finalized⟩ →
    entry ≠ finalized →
    M.Slashable a.erase b.erase
  /-- The chain state derived for every named block satisfies `NjEntry`. -/
  njEntry_derive_named : ∀ (E : Env V) (cfg : HeightConfig) (B : NamedBlock V),
    Restated.Vocabulary.Proofs.NjGap.NjEntry M cfg (M.derive_named E cfg B)
  /-- If `B`'s justified height is positive, some ancestor `J` of `B` erases to `B`'s justified
      block, stands at `B`'s justified height, is its own entry, and has `nj` false. -/
  namedJustification_ancestor_data : ∀ (E : Env V) (cfg : HeightConfig) (B : NamedBlock V),
    0 < (M.derive_named E cfg B).h_j →
      ∃ J : NamedBlock V, NamedBlock.Preceq J B ∧
        J.erase = (M.derive_named E cfg B).J ∧
        (M.derive_named E cfg J).h = (M.derive_named E cfg B).h_j ∧
        (M.derive_named E cfg J).T_h = J.erase ∧
        (M.derive_named E cfg J).nj = false
  /-- If `D`'s justified height is not `0`, some ancestor `J` of `D` erases to `D`'s justified
      block, and each member of some quorum signs an attestation, included in an ancestor of `D`,
      whose height pair is a vote for `D`'s justified height and `J`'s root with the timeout bit
      clear. -/
  justification_certificate : ∀ (E : Env V) (cfg : HeightConfig) (D : NamedBlock V),
    (M.derive_named E cfg D).h_j ≠ 0 →
      ∃ J : NamedBlock V, NamedBlock.Preceq J D ∧
        J.erase = (M.derive_named E cfg D).J ∧
        ∃ Q : Finset V, E.electorate.IsQuorum Q ∧
          ∀ signer ∈ Q, ∃ carrier : NamedBlock V, ∃ a : NamedAttestation V,
            NamedBlock.Preceq carrier D ∧ a ∈ carrier.attestations ∧
            a.val_index = signer ∧
            a.height_pair = .vote (M.derive_named E cfg D).h_j J.root false
  /-- If `D`'s finalized height is not `0`, some ancestor `F` of `D` erases to `D`'s finalized
      block, and each member of some quorum signs an attestation, included in an ancestor of `D`,
      whose finality pair is `D`'s finalized height with `F`'s root. -/
  finality_certificate : ∀ (E : Env V) (cfg : HeightConfig) (D : NamedBlock V)
    (hnz : (M.derive_named E cfg D).h_F ≠ 0),
    ∃ F : NamedBlock V, NamedBlock.Preceq F D ∧
      F.erase = (M.derive_named E cfg D).F ∧
      ∃ Q : Finset V, E.electorate.IsQuorum Q ∧
        ∀ signer ∈ Q, ∃ carrier : NamedBlock V, ∃ a : NamedAttestation V,
          NamedBlock.Preceq carrier D ∧ a ∈ carrier.attestations ∧
          a.val_index = signer ∧
          a.finality_pair = some ⟨(M.derive_named E cfg D).h_F, F.root⟩
  /-- After `M.cs_with_F_h_F σ B h`, the finalized block is `B` and its height is `h`, and `h`,
      `T_h`, `L`, `J`, `h_j`, `target_participation`, `progress`, `finalize` and `nj` are those of
      `σ`. -/
  cs_with_F_h_F_fields : ∀ (σ : M.CS) (B : Block V) (h : Height),
    (M.cs_with_F_h_F σ B h).F = B ∧ (M.cs_with_F_h_F σ B h).h_F = h ∧
    (M.cs_with_F_h_F σ B h).h = σ.h ∧ (M.cs_with_F_h_F σ B h).T_h = σ.T_h ∧
    M.L (M.cs_with_F_h_F σ B h) = M.L σ ∧ (M.cs_with_F_h_F σ B h).J = σ.J ∧
    (M.cs_with_F_h_F σ B h).h_j = σ.h_j ∧
    (M.cs_with_F_h_F σ B h).target_participation = σ.target_participation ∧
    (M.cs_with_F_h_F σ B h).progress = σ.progress ∧
    M.finalize (M.cs_with_F_h_F σ B h) = M.finalize σ ∧ (M.cs_with_F_h_F σ B h).nj = σ.nj
  /-- A validator `i` in the `finalize` set after `M.process_attestation σ a` was in `σ`'s
      `finalize` set, or is the validator of `a` and `a`'s finality pair is `σ`'s justified height
      with the root of `σ`'s justified block. -/
  mem_finalize_process_attestation : ∀ (σ : M.CS) (a : CombinedAttestation V) {i : V}
    (h : i ∈ M.finalize (M.process_attestation σ a)),
    i ∈ M.finalize σ ∨ (i = a.val_index ∧ a.finality_pair = some ⟨σ.h_j, σ.J.root⟩)
  /-- The chain state derived for the block `p.node s root votes support rows proposer` is the
      transition, by that block, of the chain state derived for `p`. -/
  derive_named_node : ∀ (E : DecoupledConsensusModel.Env V) (cfg : DecoupledConsensusModel.Protocol.HeightConfig) (p : DecoupledConsensusModel.NamedBlock V) (s : DecoupledConsensusModel.Slot) (root : DecoupledConsensusModel.BlockId) (votes support : List (DecoupledConsensusModel.GoldfishVote V)) (rows : List (DecoupledConsensusModel.NamedAttestation V)) (proposer : V), M.derive_named E cfg (p.node s root votes support rows proposer) = M.named_transition E cfg (M.derive_named E cfg p) (p.node s root votes support rows proposer)
  /-- If `B` is not genesis, the chain state derived for `B` is the transition, by `B`, of the chain
      state derived for `B`'s parent. -/
  derive_named_of_not_genesis : ∀ (E : DecoupledConsensusModel.Env V) (cfg : DecoupledConsensusModel.Protocol.HeightConfig) (B : DecoupledConsensusModel.NamedBlock V), B ≠ DecoupledConsensusModel.NamedBlock.genesis → M.derive_named E cfg B = M.named_transition E cfg (M.derive_named E cfg B.parent) B
  /-- If `A ⪯ B`, then `h_j(A) < h_j(B)`, or `h_j(A) = h_j(B)` and `J(A) = J(B)`. -/
  namedJustification_strict_or_eq_of_preceq : ∀ (E : Env V) (cfg : HeightConfig)
    {A B : NamedBlock V}, NamedBlock.Preceq A B →
      (M.derive_named E cfg A).h_j < (M.derive_named E cfg B).h_j ∨
        ((M.derive_named E cfg A).h_j = (M.derive_named E cfg B).h_j ∧
          (M.derive_named E cfg A).J = (M.derive_named E cfg B).J)
  /-- The chain state of genesis has justified height `0`. -/
  ModelProperties_derive_named_genesis_h_j : ∀ (E : Env V) (cfg : HeightConfig),
    (M.derive_named E cfg (.genesis : NamedBlock V)).h_j = 0
  /-- If `A ⪯ B` and `h(B) = h(A)`, then `nj(B) = nj(A)`. -/
  namedNj_eq_of_preceq_sameHeight : ∀ (E : Env V) (cfg : HeightConfig) {A B : NamedBlock V},
    NamedBlock.Preceq A B → (M.derive_named E cfg B).h = (M.derive_named E cfg A).h →
      (M.derive_named E cfg B).nj = (M.derive_named E cfg A).nj
  /-- `B`'s finalized height is `0`, or some ancestor `F` of `B` erases to `B`'s finalized block and
      stands at `B`'s finalized height. -/
  finalized_ancestor_height : ∀ (E : Env V) (cfg : HeightConfig) (B : NamedBlock V),
    (M.derive_named E cfg B).h_F = 0 ∨
      ∃ F : NamedBlock V, NamedBlock.Preceq F B ∧
        F.erase = (M.derive_named E cfg B).F ∧
        (M.derive_named E cfg F).h = (M.derive_named E cfg B).h_F
  /-- After the transition of `st` by `B`, either the height is `h(st)` and the entry is `T_h(st)`,
      or the height is `h(st) + 1` and the entry is `B`'s erasure. -/
  transition_height_entry_cases : ∀ (E : Env V) (cfg : HeightConfig) (st : M.CS)
    (B : NamedBlock V),
    ((M.named_transition E cfg st B).h = st.h ∧ (M.named_transition E cfg st B).T_h = st.T_h) ∨
      ((M.named_transition E cfg st B).h = st.h + 1 ∧
        (M.named_transition E cfg st B).T_h = B.erase)
  /-- If `h(node parent …) ≠ h(parent)`, then each member of some quorum signs an attestation,
      included in an ancestor of `node parent …`, whose height pair matches
      `(h(parent), T_h(parent).root)`. -/
  crossing_matching_quorum : ∀ (E : Env V) (cfg : HeightConfig) (parent : NamedBlock V)
    (slot : Slot) (root : BlockId) (votes support : List (GoldfishVote V))
    (rows : List (NamedAttestation V)) (proposer : V),
    (M.derive_named E cfg (.node parent slot root votes support rows proposer)).h ≠
        (M.derive_named E cfg parent).h →
      ∃ Q : Finset V, E.electorate.IsQuorum Q ∧
        ∀ signer ∈ Q, ∃ carrier : NamedBlock V, ∃ a : NamedAttestation V,
          NamedBlock.Preceq carrier (.node parent slot root votes support rows proposer) ∧
          a ∈ carrier.attestations ∧ a.val_index = signer ∧
          a.height_pair.matchesEntry (M.derive_named E cfg parent).h
            (M.derive_named E cfg parent).T_h.root = true
  /-- If `H` is a recovery height for `h_F0` (`Proofs.NjGap.RecoveryHeight cfg h_F0 H`), and every
      ancestor of `B` has finalized height at most `h_F0`, then `h_j(B) ≠ H`. -/
  h_j_ne_recovery_height_named : ∀ (E : Env V) (cfg : HeightConfig) {h_F0 H : Height},
    Proofs.NjGap.RecoveryHeight cfg h_F0 H → ∀ B : NamedBlock V,
      (∀ C : NamedBlock V, NamedBlock.Preceq C B → (M.derive_named E cfg C).h_F ≤ h_F0) →
        (M.derive_named E cfg B).h_j ≠ H
  /-- `T_h(B)` is an ancestor of `B`'s erasure. -/
  derive_named_T_h_preceq : ∀ (E : Env V) (cfg : HeightConfig) (B : NamedBlock V),
    Block.Preceq (M.derive_named E cfg B).T_h B.erase
  /-- If `a`'s height pair matches `(h, X)` and `X ≠ T`, then the height pair of `a`'s erasure
      conflicts with the finality pair `(h, T)`. -/
  conflictsWithFinality_erase_of_matchesEntry : ∀ {a : NamedAttestation V} {h : Height}
    {X T : BlockId}, a.height_pair.matchesEntry h X = true → X ≠ T →
      M.conflictsWithFinality a.erase.height_pair ⟨h, T⟩ = true
  /-- If `σ` passes the justification test, its target-participation set is a quorum. -/
  isQuorum_of_targetReady : ∀ {σ : M.CS} (E : Env V), M.targetReady E σ = true →
    E.electorate.IsQuorum σ.target_participation
  /-- If `Pc` is not genesis, `Pm ⪯ parent(Pc)`, `h(Pm) = h(Pc)`, and, when `parent(Pc)` has the
      height `h(Pc)` and the entry `T_h(Pm)`, each member of some quorum is in the parent's progress
      set or signs a row of `Pc` matching the parent's height and entry, then
      `Pc.slot < T_h(Pc).slot + timeoutDelay`. -/
  climb_entryYoung_l85 : ∀ (E : Env V) (cfg : HeightConfig) {Pm Pc : NamedBlock V},
    Pc ≠ .genesis → NamedBlock.Preceq Pm Pc.parent →
    (M.derive_named E cfg Pm).h = (M.derive_named E cfg Pc).h →
    ((M.derive_named E cfg Pc.parent).h = (M.derive_named E cfg Pc).h →
      (M.derive_named E cfg Pc.parent).T_h = (M.derive_named E cfg Pm).T_h →
      ∃ Q : Finset V, E.electorate.IsQuorum Q ∧ ∀ i ∈ Q,
        i ∈ (M.derive_named E cfg Pc.parent).progress ∨
          ∃ a ∈ Pc.attestations, a.val_index = i ∧
            a.height_pair.matchesEntry (M.derive_named E cfg Pc.parent).h
              (M.derive_named E cfg Pc.parent).T_h.root = true) →
    Pc.slot < (M.derive_named E cfg Pc).T_h.slot + cfg.timeoutDelay
  /-- For a block `B` other than genesis, `F(B)` is `F(parent(B))` or `J(parent(B))`. -/
  derive_named_F_cases : ∀ (E : Env V) (cfg : HeightConfig) {B : NamedBlock V},
    B ≠ .genesis →
      (M.derive_named E cfg B).F = (M.derive_named E cfg B.parent).F ∨
        (M.derive_named E cfg B).F = (M.derive_named E cfg B.parent).J
  /-- The finalized block of genesis is genesis. -/
  derive_named_genesis_F : ∀ (E : Env V) (cfg : HeightConfig),
    (M.derive_named E cfg (.genesis : NamedBlock V)).F = Block.genesis
  /-- The chain state of genesis has justified height `0`. -/
  Sts_derive_named_genesis_h_j : ∀ (E : Env V) (cfg : HeightConfig),
    (M.derive_named E cfg (.genesis : NamedBlock V)).h_j = 0
  /-- If `A ⪯ B`, then `h_j(A) ≤ h_j(B)`. -/
  derive_named_h_j_mono : ∀ (E : Env V) (cfg : HeightConfig) {A B : NamedBlock V},
    NamedBlock.Preceq A B → (M.derive_named E cfg A).h_j ≤ (M.derive_named E cfg B).h_j
  /-- If `h(B) ≥ 2`, then some ancestor `N` of `B` has `h(N) = h(B)` and `h(N) = h(parent(N)) + 1`. -/
  exists_crossing_ancestor : ∀ (E : Env V) (cfg : HeightConfig) (B : NamedBlock V),
    2 ≤ (M.derive_named E cfg B).h →
      ∃ N : NamedBlock V, NamedBlock.Preceq N B ∧
        (M.derive_named E cfg N).h = (M.derive_named E cfg B).h ∧
        (M.derive_named E cfg N).h = (M.derive_named E cfg N.parent).h + 1
  /-- If `h_F(D) ≠ 0`, there are ancestors `Fn` and `X` of `D` with `Fn`'s erasure equal to `F(D)`,
      `h(Fn) = h_F(D)`, `T_h(Fn)` equal to `Fn`'s erasure, `h(X) = h_F(D)`, and a quorum each of
      whose members signs an attestation, included in an ancestor of `D`, whose height pair is a
      vote at height `h_F(D)` for `X`'s root. -/
  finalized_entry_quorum : ∀ (E : Env V) (cfg : HeightConfig) (D : NamedBlock V),
    (M.derive_named E cfg D).h_F ≠ 0 →
      ∃ Fn X : NamedBlock V, NamedBlock.Preceq Fn D ∧ NamedBlock.Preceq X D ∧
        Fn.erase = (M.derive_named E cfg D).F ∧
        (M.derive_named E cfg Fn).h = (M.derive_named E cfg D).h_F ∧
        (M.derive_named E cfg Fn).T_h = Fn.erase ∧
        (M.derive_named E cfg X).h = (M.derive_named E cfg D).h_F ∧
        ∃ Q : Finset V, E.electorate.IsQuorum Q ∧ ∀ signer ∈ Q,
          ∃ (carrier : NamedBlock V) (a : NamedAttestation V) (tmo : Bool),
            NamedBlock.Preceq carrier D ∧ a ∈ carrier.attestations ∧ a.val_index = signer ∧
            a.height_pair = NamedHeightPair.vote (M.derive_named E cfg D).h_F X.root tmo
  /-- `h_F(D) = 0`, or some ancestor `Fn` of `D` erases to `F(D)`, has `h(Fn) = h_F(D)`, and has
      `T_h(Fn)` equal to `Fn`'s erasure. -/
  finalized_is_entry : ∀ (E : Env V) (cfg : HeightConfig) (D : NamedBlock V),
    (M.derive_named E cfg D).h_F = 0 ∨
      ∃ Fn : NamedBlock V, NamedBlock.Preceq Fn D ∧
        Fn.erase = (M.derive_named E cfg D).F ∧
        (M.derive_named E cfg Fn).h = (M.derive_named E cfg D).h_F ∧
        (M.derive_named E cfg Fn).T_h = Fn.erase
  /-- If `h_j(B) ≤ h_F(B)`, then `J(B)` is an ancestor of `F(B)`. -/
  justified_preceq_finalized_of_le_f1b1 : ∀ (E : Env V) (cfg : HeightConfig) (B : NamedBlock V),
    (M.derive_named E cfg B).h_j ≤ (M.derive_named E cfg B).h_F →
      Block.Preceq (M.derive_named E cfg B).J (M.derive_named E cfg B).F
  /-- If `A ⪯ B` and `h(A) = h(B)`, then `nj(A) = nj(B)`. -/
  nj_eq_on_plateau_l85 : ∀ (E : Env V) (cfg : HeightConfig) {A B : NamedBlock V},
    NamedBlock.Preceq A B → (M.derive_named E cfg A).h = (M.derive_named E cfg B).h →
      (M.derive_named E cfg A).nj = (M.derive_named E cfg B).nj
  /-- If `K` does not divide `h(B)`, then `nj(B) = false`. -/
  nj_false_of_not_dvd_l85 : ∀ (E : Env V) (cfg : HeightConfig) (B : NamedBlock V),
    ¬ cfg.K ∣ (M.derive_named E cfg B).h → (M.derive_named E cfg B).nj = false
  /-- If slots increase along `Z`'s chain, `A ⪯ Z`, `1 ≤ k`, `h_j(Z) < h(A)`, no `h(A) + j` with
      `1 ≤ j < k` is a multiple of `K`, and `h(A) + k ≤ h(Z)`, then
      `A.slot + 1 + (k − 1)·timeoutDelay ≤ Z.slot`. -/
  progress_spacing_l85 : ∀ (E : Env V) (cfg : HeightConfig) {A Z : NamedBlock V},
    (∀ X : NamedBlock V, NamedBlock.Preceq X Z → X ≠ .genesis → X.parent.slot < X.slot) →
    NamedBlock.Preceq A Z → ∀ {k : Nat}, 1 ≤ k →
    (M.derive_named E cfg Z).h_j < (M.derive_named E cfg A).h →
    (∀ j : Nat, 1 ≤ j → j < k → ¬ cfg.K ∣ (M.derive_named E cfg A).h + j) →
    (M.derive_named E cfg A).h + k ≤ (M.derive_named E cfg Z).h →
    A.slot + 1 + (k - 1) * cfg.timeoutDelay ≤ Z.slot
  /-- If slots increase along `P2`'s chain, `Pc` and `P2` are not genesis, `Pc`'s `nj` bit is clear,
      `Pm ⪯ parent(Pc)`, `Pm` is at slot `om`, `Pc ⪯ parent(P2)`,
      `parent(P2).slot + 1 ≤ om + timeoutDelay`, and two quorum conditions hold, then
      `h(Pc) ≤ h_j(P2)`.

      The first condition: when `parent(P2)` has the height and entry of `Pc`, each member of some
      quorum is in `parent(P2)`'s target participation or signs a row of `P2` that is the target
      vote for `parent(P2)`'s height and entry. The second: when `Pm` and `parent(Pc)` have the
      height of `Pc` and `parent(Pc)` has the entry of `Pm`, each member of some quorum is in
      `parent(Pc)`'s target participation or signs a row of `Pc` that is the target vote for
      `parent(Pc)`'s height and entry. -/
  windowJustified_l85d : ∀ (E : Env V) (cfg : HeightConfig) {Pm Pc P2 : NamedBlock V} {om : Slot},
    (∀ X : NamedBlock V, NamedBlock.Preceq X P2 → X ≠ .genesis → X.parent.slot < X.slot) →
    Pc ≠ .genesis → P2 ≠ .genesis →
    (M.derive_named E cfg Pc).nj = false →
    NamedBlock.Preceq Pm Pc.parent → Pm.slot = om →
    NamedBlock.Preceq Pc P2.parent →
    P2.parent.slot + 1 ≤ om + cfg.timeoutDelay →
    ((M.derive_named E cfg P2.parent).h = (M.derive_named E cfg Pc).h →
      (M.derive_named E cfg P2.parent).T_h = (M.derive_named E cfg Pc).T_h →
      ∃ Q : Finset V, E.electorate.IsQuorum Q ∧ ∀ i ∈ Q,
        i ∈ (M.derive_named E cfg P2.parent).target_participation ∨
          ∃ a ∈ P2.attestations, a.val_index = i ∧
            a.height_pair = NamedHeightPair.vote (M.derive_named E cfg P2.parent).h
              (M.derive_named E cfg P2.parent).T_h.root false) →
    ((M.derive_named E cfg Pm).h = (M.derive_named E cfg Pc).h →
      (M.derive_named E cfg Pc.parent).h = (M.derive_named E cfg Pc).h →
      (M.derive_named E cfg Pc.parent).T_h = (M.derive_named E cfg Pm).T_h →
      ∃ Q : Finset V, E.electorate.IsQuorum Q ∧ ∀ i ∈ Q,
        i ∈ (M.derive_named E cfg Pc.parent).target_participation ∨
          ∃ a ∈ Pc.attestations, a.val_index = i ∧
            a.height_pair = NamedHeightPair.vote (M.derive_named E cfg Pc.parent).h
              (M.derive_named E cfg Pc.parent).T_h.root false) →
    (M.derive_named E cfg Pc).h ≤ (M.derive_named E cfg P2).h_j
  /-- The latest block of the transition of `st` by `B` is `B`'s erasure. -/
  named_transition_latest : ∀ (E : Env V) (cfg : HeightConfig) (st : M.CS) (B : NamedBlock V),
    M.L (M.named_transition E cfg st B) = B.erase
  /-- The `finalize` set after applying `row` through the targeted interpretation equals the
      `finalize` set after applying `row`'s erasure directly. -/
  process_finality_eq : ∀ (st : M.CS) (row : NamedAttestation V),
    M.finalize (M.process_attestation_with M.targeted st row) =
      M.finalize (M.process_attestation st row.erase)
  /-- Applying one row through any interpretation leaves `L`, `h`, `T_h`, `J`, `h_j`, `F` and `h_F`
      unchanged. -/
  process_context_fields : ∀ {Row : Type} (binding : M.Binding Row) (st : M.CS) (row : Row),
    M.L (M.process_attestation_with binding st row) = M.L st ∧
      (M.process_attestation_with binding st row).h = st.h ∧
      (M.process_attestation_with binding st row).T_h = st.T_h ∧
      (M.process_attestation_with binding st row).J = st.J ∧
      (M.process_attestation_with binding st row).h_j = st.h_j ∧
      (M.process_attestation_with binding st row).F = st.F ∧
      (M.process_attestation_with binding st row).h_F = st.h_F
  /-- If `σ` passes the finality test, its `finalize` set is a quorum. -/
  isQuorum_of_finalityReady : ∀ {σ : M.CS} (E : Env V), M.finalityReady E σ = true →
    E.electorate.IsQuorum (M.finalize σ)
  /-- Advancing the height leaves the justified block unchanged. -/
  advance_height_J : ∀ {cfg : HeightConfig} {σ : M.CS}, (M.advance_height cfg σ).J = σ.J
  /-- Advancing the height leaves the justified height unchanged. -/
  advance_height_h_j : ∀ {cfg : HeightConfig} {σ : M.CS}, (M.advance_height cfg σ).h_j = σ.h_j
  /-- Advancing the height raises the height by one. -/
  advance_height_h : ∀ {cfg : HeightConfig} {σ : M.CS}, (M.advance_height cfg σ).h = σ.h + 1
  /-- `left` and `right` are not slashable exactly when `slashable left right = false`. -/
  not_Slashable_iff : ∀ (left right : CombinedAttestation V),
    ¬ M.Slashable left right ↔ M.slashable left right = false
  /-- `a` and `b` are slashable exactly when `slashable a b = true`. -/
  Slashable_iff : ∀ {a b : CombinedAttestation V}, M.Slashable a b ↔ M.slashable a b = true
  /-- If `K` divides `h` and `D < h − h_F`, then `nonjustifiable cfg h h_F = true`. -/
  nonjustifiable_of : ∀ {cfg : HeightConfig} {h h_F : Height},
    cfg.K ∣ h → cfg.D < h - h_F → M.nonjustifiable cfg h h_F = true
  /-- If `h_F ≤ cap` and `h` is nonjustifiable given `cap`, then `h` is nonjustifiable given `h_F`. -/
  nonjustifiable_of_le : ∀ {cfg : HeightConfig} {h h_F cap : Height},
    h_F ≤ cap → M.nonjustifiable cfg h cap = true → M.nonjustifiable cfg h h_F = true
  /-- If no finality pair of `left` conflicts with `right`'s height pair, and no finality pair of
      `right` conflicts with `left`'s height pair, then `e1Fields left right = false`. -/
  e1Fields_eq_false_of : ∀ (left right : CombinedAttestation V),
    (∀ p : FinalityPair, left.finality_pair = some p →
      M.conflictsWithFinality right.height_pair p = false) →
    (∀ q : FinalityPair, right.finality_pair = some q →
      M.conflictsWithFinality left.height_pair q = false) →
    M.e1Fields left right = false
  /-- If `e1Fields left right = false` and `e2Fields left right = false`, then
      `slashable left right = false`. -/
  slashable_eq_false_of_fields : ∀ (left right : CombinedAttestation V),
    M.e1Fields left right = false → M.e2Fields left right = false →
      M.slashable left right = false
  /-- The initial chain state stands at height `1`. -/
  chainState_initial_h : (M.cs_initial).h = 1
  /-- The chain state derived for `B` in the environment `S.E` with its GST replaced by `g` is the
      one derived in `S.E`. -/
  derive_named_setupWithGST : ∀ (S : Setup V) (g : Int) (hg : 0 ≤ g) (B : NamedBlock V),
    M.derive_named { S.E with t_GST := g, t_GST_nonneg := hg } S.cfg B =
      M.derive_named S.E S.cfg B
  /-- If `C ⪯ P`, the attestation `a` is on `P`'s named chain and not on `C`'s, `P` and `C` stand at
      the same height, and `a`'s height pair is a vote or a timeout for `C`'s height and entry root,
      then `a`'s signer is in `P`'s progress set. -/
  namedPair_mem_progress_of_suffix_same_height : ∀ (E : Env V) (cfg : HeightConfig)
    {C P : NamedBlock V} {a : NamedAttestation V},
    NamedBlock.Preceq C P → a ∈ Protocol.named_chain_attestations P →
    a ∉ Protocol.named_chain_attestations C →
    (M.derive_named E cfg P).h = (M.derive_named E cfg C).h →
    (a.height_pair = .vote (M.derive_named E cfg C).h (M.derive_named E cfg C).T_h.root false ∨
      a.height_pair = .vote (M.derive_named E cfg C).h (M.derive_named E cfg C).T_h.root true) →
    a.val_index ∈ (M.derive_named E cfg P).progress
  /-- If `C ⪯ P`, the attestation `a` is on `P`'s named chain and not on `C`'s, `P` and `C` stand at
      the same height, and `a`'s height pair is a vote for `C`'s height and entry root, then `a`'s
      signer is in `P`'s target participation set. -/
  namedTarget_mem_of_suffix_same_height : ∀ (E : Env V) (cfg : HeightConfig)
    {C P : NamedBlock V} {a : NamedAttestation V},
    NamedBlock.Preceq C P → a ∈ Protocol.named_chain_attestations P →
    a ∉ Protocol.named_chain_attestations C →
    (M.derive_named E cfg P).h = (M.derive_named E cfg C).h →
    a.height_pair = .vote (M.derive_named E cfg C).h (M.derive_named E cfg C).T_h.root false →
    a.val_index ∈ (M.derive_named E cfg P).target_participation

/-- Facts about runs of the chain-state family of `M`, beyond those of `ChainStateRunFacts`; it has
    no field. -/
structure ChainStateAddedRunFacts (M : Model V) : Prop where

end DecoupledConsensusModel.Sts.Record
