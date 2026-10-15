import Model.Vocabulary.Protocol.ChainState
import Proofs.Claims.ModelIrreducible
import Proofs.Vocabulary.Internal.ModelVocabulary.Substrate.Weights

/-!
# The record of the chain-state family

The record `ChainStateModel`: a type of chain states, readers for its fields, and the routines of
the chain-state family. Also the field spellings `σ.h`, `σ.J`, … of the readers, the two clauses
`ChainOrderOf` of the chain order, and the structure `ChainStateFacts` of facts the routines satisfy
on every input.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts.Record

open DecoupledConsensusModel.Protocol (HeightConfig)

/-- A model of the chain-state family: a type `CS` of chain states, readers for its fields, and the
    family's routines over `CS`. -/
structure ChainStateModel (V : Type) [DecidableEq V] [Fintype V] where
  /-- The type of chain states. -/
  CS : Type
  /-- The current height. -/
  h : CS → Height
  /-- The block that carried the chain into its current height. -/
  T_h : CS → Block V
  /-- The `nj` bit, set when the chain entered its current height. -/
  nj : CS → Bool
  /-- The latest justified block. -/
  J : CS → Block V
  /-- The height of the latest justified block. -/
  h_j : CS → Height
  /-- The latest finalized block. -/
  F : CS → Block V
  /-- The height of the latest finalized block. -/
  h_F : CS → Height
  /-- The validators counted towards progress at the current height. -/
  progress : CS → Finset V
  /-- The validators counted towards the target quorum at the current height. -/
  target_participation : CS → Finset V
  /-- The type of row interpretations for rows of type `Row`. -/
  Binding : Type → Type
  /-- The interpretation of named attestations by the entry they name. -/
  targeted : Binding (NamedAttestation V)
  /-- One attestation applied to a chain state. -/
  process_attestation : CS → CombinedAttestation V → CS
  /-- One row applied to a chain state through an interpretation. -/
  process_attestation_with : {Row : Type} → Binding Row → CS → Row → CS
  /-- A block's rows folded into a chain state. -/
  fold_rows : {Row : Type} → Binding Row → CS → Block V → List Row → CS
  /-- The height events applied after the rows. -/
  process_height_events : Env V → HeightConfig → CS → CS
  /-- The finality test. -/
  finalityReady : Env V → CS → Bool
  /-- The justification test. -/
  targetReady : Env V → CS → Bool
  /-- The progress test. -/
  progReady : Env V → HeightConfig → CS → Bool
  /-- The transition by a named block. -/
  named_transition : Env V → HeightConfig → CS → NamedBlock V → CS
  /-- The chain state of a named block. -/
  derive_named : Env V → HeightConfig → NamedBlock V → CS
  /-- Whether a height pair conflicts with a finality pair. -/
  conflictsWithFinality : HeightPair → FinalityPair → Bool
  /-- Whether two attestations are an E2 field conflict. -/
  e2Fields : CombinedAttestation V → CombinedAttestation V → Bool
  /-- Slashability of two attestations, as a proposition. -/
  Slashable : CombinedAttestation V → CombinedAttestation V → Prop

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The readers as fields of the chain state -/

/-- `σ.h` is the reader `M.h σ`: the height of `σ`. -/
def ChainStateModel.CS.h {M : ChainStateModel V} (σ : M.CS) : Height := M.h σ
/-- `σ.T_h` is the reader `M.T_h σ`: the entry block of `σ`'s height. -/
def ChainStateModel.CS.T_h {M : ChainStateModel V} (σ : M.CS) : Block V := M.T_h σ
/-- `σ.nj` is the reader `M.nj σ`: the `nj` bit of `σ`. -/
def ChainStateModel.CS.nj {M : ChainStateModel V} (σ : M.CS) : Bool := M.nj σ
/-- `σ.J` is the reader `M.J σ`: the justified block of `σ`. -/
def ChainStateModel.CS.J {M : ChainStateModel V} (σ : M.CS) : Block V := M.J σ
/-- `σ.h_j` is the reader `M.h_j σ`: the justified height of `σ`. -/
def ChainStateModel.CS.h_j {M : ChainStateModel V} (σ : M.CS) : Height := M.h_j σ
/-- `σ.F` is the reader `M.F σ`: the finalized block of `σ`. -/
def ChainStateModel.CS.F {M : ChainStateModel V} (σ : M.CS) : Block V := M.F σ
/-- `σ.h_F` is the reader `M.h_F σ`: the finalized height of `σ`. -/
def ChainStateModel.CS.h_F {M : ChainStateModel V} (σ : M.CS) : Height := M.h_F σ
/-- `σ.progress` is the reader `M.progress σ`: the progress set of `σ`. -/
def ChainStateModel.CS.progress {M : ChainStateModel V} (σ : M.CS) : Finset V := M.progress σ
/-- `σ.target_participation` is the reader `M.target_participation σ`: the target-participation set
    of `σ`. -/
def ChainStateModel.CS.target_participation {M : ChainStateModel V} (σ : M.CS) : Finset V :=
  M.target_participation σ

/-- Two clauses of the chain order of the chain state `σ`. -/
structure ChainOrderOf (M : ChainStateModel V) (σ : M.CS) : Prop where
  /-- The finalized height is at most the justified height: `h_F(σ) ≤ h_j(σ)`. -/
  heights_ordered : σ.h_F ≤ σ.h_j
  /-- The justified height is less than the height: `h_j(σ) < h(σ)`. -/
  justified_below_height : σ.h_j < σ.h

/-- Facts that the chain-state routines of `M` satisfy on every input. -/
structure ChainStateFacts (M : ChainStateModel V) : Prop where
  /-- Genesis's chain state stands at height `1`. -/
  derive_named_genesis_h : ∀ (E : Env V) (cfg : HeightConfig),
    (M.derive_named E cfg (.genesis : NamedBlock V)).h = 1
  /-- Every named block's chain state stands at height at least `1`. -/
  one_le_derive_named_h : ∀ (E : Env V) (cfg : HeightConfig) (B : NamedBlock V),
    1 ≤ (M.derive_named E cfg B).h
  /-- If `A ⪯ B`, then `h(A) ≤ h(B)`. -/
  derive_height_mono : ∀ (E : Env V) (cfg : HeightConfig) {A B : NamedBlock V},
    NamedBlock.Preceq A B → (M.derive_named E cfg A).h ≤ (M.derive_named E cfg B).h
  /-- If `A ⪯ B` and `h(A) = h(B)`, then `A` and `B` have the same entry. -/
  entry_eq_on_plateau : ∀ (E : Env V) (cfg : HeightConfig) {A B : NamedBlock V},
    NamedBlock.Preceq A B → (M.derive_named E cfg A).h = (M.derive_named E cfg B).h →
      (M.derive_named E cfg A).T_h = (M.derive_named E cfg B).T_h
  /-- Some ancestor of `B` at `B`'s height erases to `B`'s entry. -/
  entry_ancestor_same_height : ∀ (E : Env V) (cfg : HeightConfig) (B : NamedBlock V),
    ∃ entry : NamedBlock V, NamedBlock.Preceq entry B ∧
      entry.erase = (M.derive_named E cfg B).T_h ∧
      (M.derive_named E cfg entry).h = (M.derive_named E cfg B).h
  /-- `B`'s entry is an ancestor of `B`'s erasure. -/
  entry_geometry_ancestor : ∀ (E : Env V) (cfg : HeightConfig) (B : NamedBlock V),
    Block.Preceq (M.derive_named E cfg B).T_h B.erase
  /-- Every named block's chain state satisfies the two clauses `ChainOrderOf` of the chain order. -/
  chainOrder_derive_named : ∀ (E : Env V) (cfg : HeightConfig) (B : NamedBlock V),
    ChainOrderOf M (M.derive_named E cfg B)
  /-- `B`'s finalized block and its justified block are ancestors of `B`'s erasure. -/
  derive_named_anchors_preceq : ∀ (E : Env V) (cfg : HeightConfig) (B : NamedBlock V),
    Block.Preceq (M.derive_named E cfg B).F B.erase ∧
      Block.Preceq (M.derive_named E cfg B).J B.erase
  /-- `B`'s justified height is `0`, or some ancestor of `B` erases to `B`'s justified block and
      stands at `B`'s justified height. -/
  justified_ancestor_height : ∀ (E : Env V) (cfg : HeightConfig) (B : NamedBlock V),
    (M.derive_named E cfg B).h_j = 0 ∨
      ∃ J : NamedBlock V, NamedBlock.Preceq J B ∧
        J.erase = (M.derive_named E cfg B).J ∧
        (M.derive_named E cfg J).h = (M.derive_named E cfg B).h_j
  /-- If `B`'s justified height is positive, some ancestor `J` of `B` erases to `B`'s justified
      block, stands at `B`'s justified height, and is its own entry. -/
  namedJustification_selfTarget : ∀ (E : Env V) (cfg : HeightConfig) (B : NamedBlock V),
    0 < (M.derive_named E cfg B).h_j →
      ∃ J : NamedBlock V, NamedBlock.Preceq J B ∧
        J.erase = (M.derive_named E cfg B).J ∧
        (M.derive_named E cfg J).h = (M.derive_named E cfg B).h_j ∧
        (M.derive_named E cfg J).T_h = J.erase
  /-- If `B`'s finalized height is positive, some ancestor `F` of `B` erases to `B`'s finalized
      block, stands at `B`'s finalized height, and is its own entry. -/
  namedFinalization_selfTarget_deadline : ∀ (E : Env V) (cfg : HeightConfig) (B : NamedBlock V),
    0 < (M.derive_named E cfg B).h_F →
      ∃ F : NamedBlock V, NamedBlock.Preceq F B ∧
        F.erase = (M.derive_named E cfg B).F ∧
        (M.derive_named E cfg F).h = (M.derive_named E cfg B).h_F ∧
        (M.derive_named E cfg F).T_h = F.erase
  /-- Some ancestor `J` of `B` erases to `B`'s justified block and is its own entry. -/
  namedJustification_entry_ancestor : ∀ (E : Env V) (cfg : HeightConfig) (B : NamedBlock V),
    ∃ J : NamedBlock V, NamedBlock.Preceq J B ∧
      J.erase = (M.derive_named E cfg B).J ∧
      (M.derive_named E cfg J).T_h = J.erase
  /-- A justified height `0` names genesis as the justified block. -/
  justified_zero_is_genesis : ∀ (E : Env V) (cfg : HeightConfig) (D : NamedBlock V),
    (M.derive_named E cfg D).h_j = 0 → (M.derive_named E cfg D).J = Block.genesis
  /-- A finalized height `0` names genesis as the finalized block. -/
  finalized_zero_is_genesis : ∀ (E : Env V) (cfg : HeightConfig) (D : NamedBlock V),
    (M.derive_named E cfg D).h_F = 0 → (M.derive_named E cfg D).F = Block.genesis
  /-- If `D`'s finalized height is not `0`, some ancestor `F` of `D` erases to `D`'s finalized
      block, and each member of some quorum signs an attestation, included in an ancestor of `D`,
      whose finality pair is `D`'s finalized height with `F`'s root. -/
  finality_certificate : ∀ (E : Env V) (cfg : HeightConfig) (D : NamedBlock V),
    (M.derive_named E cfg D).h_F ≠ 0 →
      ∃ F : NamedBlock V, NamedBlock.Preceq F D ∧
        F.erase = (M.derive_named E cfg D).F ∧
        ∃ Q : Finset V, E.electorate.IsQuorum Q ∧
          ∀ signer ∈ Q, ∃ carrier : NamedBlock V, ∃ a : NamedAttestation V,
            NamedBlock.Preceq carrier D ∧ a ∈ carrier.attestations ∧
            a.val_index = signer ∧
            a.finality_pair = some ⟨(M.derive_named E cfg D).h_F, F.root⟩
  /-- For every height `h` with `1 ≤ h < h(C)`, some ancestor `X` of `C` stands at `h`, and each
      member of some quorum signs an attestation, included in an ancestor of `C`, whose height pair
      matches `h` and `X`'s root. -/
  height_crossing : ∀ (E : Env V) (cfg : HeightConfig) (C : NamedBlock V) (h : Height),
    1 ≤ h → h < (M.derive_named E cfg C).h →
      ∃ X : NamedBlock V, NamedBlock.Preceq X C ∧
        (M.derive_named E cfg X).h = h ∧
        ∃ Q : Finset V, E.electorate.IsQuorum Q ∧
          ∀ signer ∈ Q, ∃ carrier : NamedBlock V, ∃ a : NamedAttestation V,
            NamedBlock.Preceq carrier C ∧ a ∈ carrier.attestations ∧
            a.val_index = signer ∧ a.height_pair.matchesEntry h X.root = true
  /-- For every named block `B`, `h_j(B's parent) ≤ h_j(B)`. -/
  derive_named_h_j_parent_le : ∀ (E : Env V) (cfg : HeightConfig) (B : NamedBlock V),
    (M.derive_named E cfg B.parent).h_j ≤ (M.derive_named E cfg B).h_j
  /-- Across one block, the justified height is the parent's, or the parent's height with the
      parent's `nj` bit clear. -/
  derive_named_h_j_step_cases : ∀ (E : Env V) (cfg : HeightConfig) (p : NamedBlock V)
    (s : Slot) (root : BlockId) (votes support : List (GoldfishVote V))
    (rows : List (NamedAttestation V)) (proposer : V),
    (M.derive_named E cfg (.node p s root votes support rows proposer)).h_j =
        (M.derive_named E cfg p).h_j ∨
      ((M.derive_named E cfg (.node p s root votes support rows proposer)).h_j =
          (M.derive_named E cfg p).h ∧ (M.derive_named E cfg p).nj = false)
  /-- If `h(node p …) = h(p)`, then `nj(node p …) = nj(p)`. -/
  derive_named_node_nj_of_h_eq : ∀ (E : Env V) (cfg : HeightConfig) (p : NamedBlock V)
    (s : Slot) (root : BlockId) (votes support : List (GoldfishVote V))
    (rows : List (NamedAttestation V)) (proposer : V),
    (M.derive_named E cfg (.node p s root votes support rows proposer)).h =
        (M.derive_named E cfg p).h →
      (M.derive_named E cfg (.node p s root votes support rows proposer)).nj =
        (M.derive_named E cfg p).nj
  /-- The justified block of `B` is the erasure of an ancestor `J` of `B` that is its own height's
      entry, at `B`'s justified height unless that is `0` and `J` is genesis; the same holds for the
      finalized block. -/
  derive_named_checkpoint_entries : ∀ (E : Env V) (cfg : HeightConfig) (B : NamedBlock V),
    (∃ J : NamedBlock V, NamedBlock.Preceq J B ∧ J.erase = (M.derive_named E cfg B).J ∧
        (M.derive_named E cfg J).T_h = J.erase ∧
        (((M.derive_named E cfg B).h_j = 0 ∧ J = .genesis) ∨
          (M.derive_named E cfg J).h = (M.derive_named E cfg B).h_j)) ∧
      (∃ F : NamedBlock V, NamedBlock.Preceq F B ∧ F.erase = (M.derive_named E cfg B).F ∧
        (M.derive_named E cfg F).T_h = F.erase ∧
        (((M.derive_named E cfg B).h_F = 0 ∧ F = .genesis) ∨
          (M.derive_named E cfg F).h = (M.derive_named E cfg B).h_F))
  /-- If `T_h(p).slot + timeoutDelay ≤ s`, and every member of a quorum `Q` is in `progress(p)` or
      signs a row of the block whose height pair matches `(h(p), T_h(p).root)`, then
      `h(node p s …) = h(p) + 1`. -/
  derive_named_node_h_eq_succ_of_progressQuorum : ∀ (E : Env V) (cfg : HeightConfig)
    (p : NamedBlock V) (s : Slot) (root : BlockId) (gv gsv : List (GoldfishVote V))
    (rows : List (NamedAttestation V)) (proposer : V) (Q : Finset V),
    E.electorate.IsQuorum Q →
    (M.derive_named E cfg p).T_h.slot + cfg.timeoutDelay ≤ s →
    (∀ v ∈ Q, v ∈ (M.derive_named E cfg p).progress ∨
      ∃ a ∈ rows, a.val_index = v ∧
        a.height_pair.matchesEntry (M.derive_named E cfg p).h
          (M.derive_named E cfg p).T_h.root = true) →
    (M.derive_named E cfg (.node p s root gv gsv rows proposer)).h =
      (M.derive_named E cfg p).h + 1
  /-- If `hp` is not the timeout vote at `p`'s height, and `hp` is a target vote at that height only
      for `p`'s target, then `hp` does not conflict with `p`. -/
  conflictsWithFinality_eq_false_of : ∀ (hp : HeightPair) (p : FinalityPair),
    hp ≠ .timeout p.height → (∀ U : BlockId, hp = .target p.height U → U = p.target) →
      M.conflictsWithFinality hp p = false
  /-- If the target votes of `left` and `right` at any one height name the same target, the pair is
      not an E2 field conflict. -/
  e2Fields_eq_false_of : ∀ (left right : CombinedAttestation V),
    (∀ (h : Height) (T U : BlockId), left.height_pair = .target h T →
      right.height_pair = .target h U → T = U) →
    M.e2Fields left right = false
  /-- If neither attestation's finality pair conflicts with the other's height pair, and the pair is
      not an E2 field conflict, then the two are not slashable. -/
  not_Slashable_of_fields : ∀ (left right : CombinedAttestation V),
    (∀ p : FinalityPair, left.finality_pair = some p →
      M.conflictsWithFinality right.height_pair p = false) →
    (∀ q : FinalityPair, right.finality_pair = some q →
      M.conflictsWithFinality left.height_pair q = false) →
    M.e2Fields left right = false → ¬ M.Slashable left right

end DecoupledConsensusModel.Sts.Record
