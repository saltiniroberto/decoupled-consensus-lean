import Spec
import Model.Vocabulary

/-!
# The maps between the spec's object types and the model's

The maps from the spec's object types (blocks, votes, attestations, chain states, the store, the
node state, ...) to the types of `DecoupledConsensusModel`, the maps back, and their facts.
`toProof` drops the root of every timeout vote; `toProofNamed` maps a height pair, an attestation or
a block to its named form, drops nothing, and has `toSpecNamed` as its inverse.
-/

set_option autoImplicit false

namespace Spec

/-! ## Roots -/

namespace BlockId

/-- The root `b` as a `DecoupledConsensusModel.BlockId`, with the same value. -/
def toProof (b : BlockId) : DecoupledConsensusModel.BlockId := ⟨b.value⟩

/-- The root `b` of `DecoupledConsensusModel` as a spec root, with the same value. -/
def toSpec (b : DecoupledConsensusModel.BlockId) : BlockId := ⟨b.value⟩

/-- Mapping a root to `DecoupledConsensusModel.BlockId` and back gives the root. -/
@[simp] theorem toSpec_toProof (b : BlockId) : BlockId.toSpec b.toProof = b := rfl

/-- Mapping a `DecoupledConsensusModel.BlockId` to the spec's type and back gives the root. -/
@[simp] theorem toProof_toSpec (b : DecoupledConsensusModel.BlockId) :
    (BlockId.toSpec b).toProof = b := rfl

/-- `BlockId.toSpec ∘ BlockId.toProof` is the identity. -/
@[simp] theorem toSpec_comp_toProof : BlockId.toSpec ∘ BlockId.toProof = id := rfl

/-- `BlockId.toProof ∘ BlockId.toSpec` is the identity. -/
@[simp] theorem toProof_comp_toSpec : BlockId.toProof ∘ BlockId.toSpec = id := rfl

/-- `BlockId.toProof` is injective: two roots with the same image are equal. -/
theorem toProof_injective : Function.Injective BlockId.toProof :=
  Function.LeftInverse.injective toSpec_toProof

/-- Two roots have the same image under `BlockId.toProof` exactly when they are equal. -/
@[simp] theorem toProof_inj {a b : BlockId} : a.toProof = b.toProof ↔ a = b :=
  toProof_injective.eq_iff

/-- `BlockId.toProof` as an embedding, for `Finset.map`. -/
def toProofEmb : BlockId ↪ DecoupledConsensusModel.BlockId := ⟨toProof, toProof_injective⟩

/-- The function of the embedding `BlockId.toProofEmb` is `BlockId.toProof`. -/
@[simp] theorem coe_toProofEmb : ⇑toProofEmb = toProof := rfl

/-- `a.toProof < b.toProof` holds exactly when `a < b`. -/
@[simp] theorem toProof_lt {a b : BlockId} : a.toProof < b.toProof ↔ a < b := Iff.rfl

/-- `a.toProof ≤ b.toProof` holds exactly when `a ≤ b`. -/
@[simp] theorem toProof_le {a b : BlockId} : a.toProof ≤ b.toProof ↔ a ≤ b := Iff.rfl

/-- The genesis block's root maps to `DecoupledConsensusModel.genesisRoot`. -/
@[simp] theorem toProof_genesisRoot : genesisRoot.toProof = DecoupledConsensusModel.genesisRoot :=
  rfl

end BlockId

/-! ## Height pairs and finality pairs -/

namespace HeightPair

/-- The height pair `p` as a `DecoupledConsensusModel.HeightPair`: the root of a timeout vote is
    dropped, the root of a target vote is mapped by `BlockId.toProof`. -/
def toProof : HeightPair → DecoupledConsensusModel.HeightPair
  | .empty => .empty
  | .vote h _ true => .timeout h
  | .vote h entry false => .target h entry.toProof

/-- A `DecoupledConsensusModel.HeightPair` as a spec height pair; a timeout vote, which holds no
    root, gets the root `genesisRoot`. -/
def toSpec : DecoupledConsensusModel.HeightPair → HeightPair
  | .empty => .empty
  | .timeout h => .vote h genesisRoot true
  | .target h b => .vote h (BlockId.toSpec b) false

/-- Mapping a `DecoupledConsensusModel.HeightPair` to the spec's type and back gives the height
    pair. -/
@[simp] theorem toProof_toSpec (p : DecoupledConsensusModel.HeightPair) :
    (HeightPair.toSpec p).toProof = p := by
  cases p <;> rfl

/-- The height pair `p` as a `NamedHeightPair`: the same case, height and timeout flag, the root
    mapped by `BlockId.toProof`. -/
def toProofNamed : HeightPair → DecoupledConsensusModel.NamedHeightPair
  | .empty => .empty
  | .vote h entry timeout => .vote h entry.toProof timeout

/-- A `NamedHeightPair` as a spec height pair: the same case, height and timeout flag, the root
    mapped by `BlockId.toSpec`. -/
def toSpecNamed : DecoupledConsensusModel.NamedHeightPair → HeightPair
  | .empty => .empty
  | .vote h entry timeout => .vote h (BlockId.toSpec entry) timeout

/-- Mapping a height pair to a `NamedHeightPair` and back gives the height pair. -/
@[simp] theorem toSpecNamed_toProofNamed (p : HeightPair) :
    HeightPair.toSpecNamed p.toProofNamed = p := by
  cases p <;> rfl

/-- Mapping a `NamedHeightPair` to the spec's type and back gives it. -/
@[simp] theorem toProofNamed_toSpecNamed (p : DecoupledConsensusModel.NamedHeightPair) :
    (HeightPair.toSpecNamed p).toProofNamed = p := by
  cases p <;> rfl

/-- The `erase` of the named image of a height pair is its image. -/
@[simp] theorem toProofNamed_erase (p : HeightPair) : p.toProofNamed.erase = p.toProof := by
  cases p with
  | empty => rfl
  | vote h entry timeout => cases timeout <;> rfl

end HeightPair

namespace FinalityPair

/-- The finality pair `p` as a `DecoupledConsensusModel.FinalityPair`: the same height, the root
    mapped by `BlockId.toProof`. -/
def toProof (p : FinalityPair) : DecoupledConsensusModel.FinalityPair :=
  ⟨p.height, p.target.toProof⟩

/-- A `DecoupledConsensusModel.FinalityPair` as a spec finality pair: the same height, the root
    mapped by `BlockId.toSpec`. -/
def toSpec (p : DecoupledConsensusModel.FinalityPair) : FinalityPair :=
  ⟨p.height, BlockId.toSpec p.target⟩

/-- Mapping a finality pair to `DecoupledConsensusModel.FinalityPair` and back gives the finality
    pair. -/
@[simp] theorem toSpec_toProof (p : FinalityPair) : FinalityPair.toSpec p.toProof = p := rfl

/-- Mapping a `DecoupledConsensusModel.FinalityPair` to the spec's type and back gives it. -/
@[simp] theorem toProof_toSpec (p : DecoupledConsensusModel.FinalityPair) :
    (FinalityPair.toSpec p).toProof = p := rfl

/-- `FinalityPair.toSpec ∘ FinalityPair.toProof` is the identity. -/
@[simp] theorem toSpec_comp_toProof : FinalityPair.toSpec ∘ FinalityPair.toProof = id := rfl

/-- `FinalityPair.toProof ∘ FinalityPair.toSpec` is the identity. -/
@[simp] theorem toProof_comp_toSpec : FinalityPair.toProof ∘ FinalityPair.toSpec = id := rfl

end FinalityPair

/-! ## Goldfish votes and attestations -/

variable {V : Type}

namespace GoldfishVote

/-- The Goldfish vote `vote` as a `DecoupledConsensusModel.GoldfishVote`: the same validator and
    slot, the head root mapped by `BlockId.toProof`. -/
def toProof (vote : GoldfishVote V) : DecoupledConsensusModel.GoldfishVote V :=
  ⟨vote.val_index, vote.slot, vote.head.toProof⟩

/-- A `DecoupledConsensusModel.GoldfishVote` as a spec Goldfish vote: the same validator and slot,
    the head root mapped by `BlockId.toSpec`. -/
def toSpec (vote : DecoupledConsensusModel.GoldfishVote V) : GoldfishVote V :=
  ⟨vote.val_index, vote.slot, BlockId.toSpec vote.head⟩

/-- Mapping a Goldfish vote to `DecoupledConsensusModel.GoldfishVote` and back gives the vote. -/
@[simp] theorem toSpec_toProof (vote : GoldfishVote V) :
    GoldfishVote.toSpec vote.toProof = vote := rfl

/-- Mapping a `DecoupledConsensusModel.GoldfishVote` to the spec's type and back gives the vote. -/
@[simp] theorem toProof_toSpec (vote : DecoupledConsensusModel.GoldfishVote V) :
    (GoldfishVote.toSpec vote).toProof = vote := rfl

/-- `GoldfishVote.toSpec ∘ GoldfishVote.toProof` is the identity. -/
@[simp] theorem toSpec_comp_toProof :
    GoldfishVote.toSpec ∘ GoldfishVote.toProof = (id : GoldfishVote V → GoldfishVote V) := rfl

/-- `GoldfishVote.toProof ∘ GoldfishVote.toSpec` is the identity. -/
@[simp] theorem toProof_comp_toSpec :
    GoldfishVote.toProof ∘ GoldfishVote.toSpec =
      (id : DecoupledConsensusModel.GoldfishVote V → DecoupledConsensusModel.GoldfishVote V) := rfl

/-- `GoldfishVote.toProof` is injective: two votes with the same image are equal. -/
theorem toProof_injective : Function.Injective (GoldfishVote.toProof (V := V)) :=
  Function.LeftInverse.injective toSpec_toProof

/-- `GoldfishVote.toProof` as an embedding, for `Finset.map`. -/
def toProofEmb : GoldfishVote V ↪ DecoupledConsensusModel.GoldfishVote V :=
  ⟨toProof, toProof_injective⟩

/-- The function of the embedding `GoldfishVote.toProofEmb` is `GoldfishVote.toProof`. -/
@[simp] theorem coe_toProofEmb : ⇑(toProofEmb (V := V)) = toProof := rfl

end GoldfishVote

namespace Attestation

/-- The attestation `a` as a `CombinedAttestation`: the same validator and round, the other fields
    mapped by their `toProof`. The height pair's map drops the root of a timeout vote. -/
def toProof (a : Attestation V) : DecoupledConsensusModel.CombinedAttestation V :=
  ⟨a.val_index, a.round, a.confirmed.map BlockId.toProof, a.height_pair.toProof,
    a.finality_pair.map FinalityPair.toProof⟩

/-- A `CombinedAttestation` as a spec attestation, each field mapped by its `toSpec`; a timeout vote
    gets the root `genesisRoot`. -/
def toSpec (a : DecoupledConsensusModel.CombinedAttestation V) : Attestation V :=
  ⟨a.val_index, a.round, a.confirmed.map BlockId.toSpec, HeightPair.toSpec a.height_pair,
    a.finality_pair.map FinalityPair.toSpec⟩

/-- Mapping a `CombinedAttestation` to the spec's type and back gives it. -/
@[simp] theorem toProof_toSpec (a : DecoupledConsensusModel.CombinedAttestation V) :
    (Attestation.toSpec a).toProof = a := by
  cases a
  simp [toProof, toSpec, Option.map_map]

/-- `Attestation.toProof ∘ Attestation.toSpec` is the identity. -/
@[simp] theorem toProof_comp_toSpec :
    Attestation.toProof ∘ Attestation.toSpec =
      (id : DecoupledConsensusModel.CombinedAttestation V →
        DecoupledConsensusModel.CombinedAttestation V) :=
  funext toProof_toSpec

/-- The attestation `a` as a `NamedAttestation`: the same validator and round, the other fields
    mapped by their maps; nothing is dropped. -/
def toProofNamed (a : Attestation V) : DecoupledConsensusModel.NamedAttestation V :=
  ⟨a.val_index, a.round, a.confirmed.map BlockId.toProof, a.height_pair.toProofNamed,
    a.finality_pair.map FinalityPair.toProof⟩

/-- A `NamedAttestation` as a spec attestation, each field mapped by its own map back. -/
def toSpecNamed (a : DecoupledConsensusModel.NamedAttestation V) : Attestation V :=
  ⟨a.val_index, a.round, a.confirmed.map BlockId.toSpec, HeightPair.toSpecNamed a.height_pair,
    a.finality_pair.map FinalityPair.toSpec⟩

/-- Mapping an attestation to a `NamedAttestation` and back gives the attestation. -/
@[simp] theorem toSpecNamed_toProofNamed (a : Attestation V) :
    Attestation.toSpecNamed a.toProofNamed = a := by
  cases a
  simp [toProofNamed, toSpecNamed, Option.map_map]

/-- Mapping a `NamedAttestation` to the spec's type and back gives it. -/
@[simp] theorem toProofNamed_toSpecNamed (a : DecoupledConsensusModel.NamedAttestation V) :
    (Attestation.toSpecNamed a).toProofNamed = a := by
  cases a
  simp [toProofNamed, toSpecNamed, Option.map_map]

/-- `Attestation.toSpecNamed ∘ Attestation.toProofNamed` is the identity. -/
@[simp] theorem toSpecNamed_comp_toProofNamed :
    Attestation.toSpecNamed ∘ Attestation.toProofNamed = (id : Attestation V → Attestation V) :=
  funext toSpecNamed_toProofNamed

/-- `Attestation.toProofNamed ∘ Attestation.toSpecNamed` is the identity. -/
@[simp] theorem toProofNamed_comp_toSpecNamed :
    Attestation.toProofNamed ∘ Attestation.toSpecNamed =
      (id : DecoupledConsensusModel.NamedAttestation V →
        DecoupledConsensusModel.NamedAttestation V) :=
  funext toProofNamed_toSpecNamed

/-- `Attestation.toProofNamed` is injective: two attestations with the same named image are
equal. -/
theorem toProofNamed_injective : Function.Injective (Attestation.toProofNamed (V := V)) :=
  Function.LeftInverse.injective toSpecNamed_toProofNamed

/-- `Attestation.toProofNamed` as an embedding, for `Finset.map`. -/
def toProofNamedEmb : Attestation V ↪ DecoupledConsensusModel.NamedAttestation V :=
  ⟨toProofNamed, toProofNamed_injective⟩

/-- The function of the embedding `Attestation.toProofNamedEmb` is `Attestation.toProofNamed`. -/
@[simp] theorem coe_toProofNamedEmb : ⇑(toProofNamedEmb (V := V)) = toProofNamed := rfl

/-- The `erase` of the named image of an attestation is its image. -/
@[simp] theorem toProofNamed_erase (a : Attestation V) : a.toProofNamed.erase = a.toProof := by
  cases a
  simp [toProofNamed, toProof, DecoupledConsensusModel.NamedAttestation.erase]

/-- `NamedAttestation.erase ∘ Attestation.toProofNamed` is `Attestation.toProof`. -/
@[simp] theorem erase_comp_toProofNamed :
    DecoupledConsensusModel.NamedAttestation.erase ∘ Attestation.toProofNamed (V := V) =
      Attestation.toProof :=
  funext toProofNamed_erase

end Attestation

/-! ## Blocks -/

namespace Block

/-- The block `B` as a `DecoupledConsensusModel.Block`, part by part, each included attestation
    mapped by `Attestation.toProof`. Blocks that differ only in the roots of timeout votes they or
    their ancestors include have the same image. -/
def toProof : Block V → DecoupledConsensusModel.Block V
  | .genesis => .genesis
  | .node p s r votes support ats proposer =>
      .node p.toProof s r.toProof (votes.map GoldfishVote.toProof)
        (support.map GoldfishVote.toProof) (ats.map Attestation.toProof) proposer

/-- A `DecoupledConsensusModel.Block` as a spec block, each part mapped by its own `toSpec`; every
    timeout vote of an included attestation gets the root `genesisRoot`. -/
def toSpec : DecoupledConsensusModel.Block V → Block V
  | .genesis => .genesis
  | .node p s r votes support ats proposer =>
      .node (Block.toSpec p) s (BlockId.toSpec r) (votes.map GoldfishVote.toSpec)
        (support.map GoldfishVote.toSpec) (ats.map Attestation.toSpec) proposer

/-- Mapping a `DecoupledConsensusModel.Block` to the spec's type and back gives the block. -/
@[simp] theorem toProof_toSpec (B : DecoupledConsensusModel.Block V) :
    (Block.toSpec B).toProof = B := by
  induction B with
  | genesis => rfl
  | node p s r votes support ats proposer ih =>
      simp [toProof, toSpec, ih, List.map_map]

/-- `Block.toProof ∘ Block.toSpec` is the identity. -/
@[simp] theorem toProof_comp_toSpec :
    Block.toProof ∘ Block.toSpec =
      (id : DecoupledConsensusModel.Block V → DecoupledConsensusModel.Block V) :=
  funext toProof_toSpec

/-- `Block.toSpec` is injective. -/
theorem toSpec_injective : Function.Injective (Block.toSpec (V := V)) :=
  Function.LeftInverse.injective toProof_toSpec

/-- The block `B` as a `NamedBlock`, each included attestation mapped by `Attestation.toProofNamed`;
    nothing is dropped. -/
def toProofNamed : Block V → DecoupledConsensusModel.NamedBlock V
  | .genesis => .genesis
  | .node p s r votes support ats proposer =>
      .node p.toProofNamed s r.toProof (votes.map GoldfishVote.toProof)
        (support.map GoldfishVote.toProof) (ats.map Attestation.toProofNamed) proposer

/-- A `NamedBlock` as a spec block, each part mapped by its own map back. -/
def toSpecNamed : DecoupledConsensusModel.NamedBlock V → Block V
  | .genesis => .genesis
  | .node p s r votes support ats proposer =>
      .node (Block.toSpecNamed p) s (BlockId.toSpec r) (votes.map GoldfishVote.toSpec)
        (support.map GoldfishVote.toSpec) (ats.map Attestation.toSpecNamed) proposer

/-- Mapping a block to a `NamedBlock` and back gives the block. -/
@[simp] theorem toSpecNamed_toProofNamed (B : Block V) : Block.toSpecNamed B.toProofNamed = B := by
  induction B with
  | genesis => rfl
  | node p s r votes support ats proposer ih =>
      simp [toProofNamed, toSpecNamed, ih, List.map_map]

/-- Mapping a `NamedBlock` to the spec's type and back gives it. -/
@[simp] theorem toProofNamed_toSpecNamed (B : DecoupledConsensusModel.NamedBlock V) :
    (Block.toSpecNamed B).toProofNamed = B := by
  induction B with
  | genesis => rfl
  | node p s r votes support ats proposer ih =>
      simp [toProofNamed, toSpecNamed, ih, List.map_map]

/-- `Block.toProofNamed` is injective: two blocks with the same named image are equal. -/
theorem toProofNamed_injective : Function.Injective (Block.toProofNamed (V := V)) :=
  Function.LeftInverse.injective toSpecNamed_toProofNamed

/-- Two blocks have the same named image exactly when they are equal. -/
@[simp] theorem toProofNamed_inj {B C : Block V} : B.toProofNamed = C.toProofNamed ↔ B = C :=
  toProofNamed_injective.eq_iff

/-- `Block.toProofNamed` as an embedding, for `Finset.map`. -/
def toProofNamedEmb : Block V ↪ DecoupledConsensusModel.NamedBlock V :=
  ⟨toProofNamed, toProofNamed_injective⟩

/-- The function of the embedding `Block.toProofNamedEmb` is `Block.toProofNamed`. -/
@[simp] theorem coe_toProofNamedEmb : ⇑(toProofNamedEmb (V := V)) = toProofNamed := rfl

/-- The `erase` of the named image of a block is its image. -/
@[simp] theorem toProofNamed_erase (B : Block V) : B.toProofNamed.erase = B.toProof := by
  induction B with
  | genesis => rfl
  | node p s r votes support ats proposer ih =>
      simp [toProofNamed, toProof, DecoupledConsensusModel.NamedBlock.erase, ih, List.map_map]

/-- The image of the genesis block is the genesis block. -/
@[simp] theorem toProof_genesis :
    (Block.genesis : Block V).toProof = DecoupledConsensusModel.Block.genesis := rfl

/-- A block's image is the genesis block exactly when the block is the genesis block. -/
@[simp] theorem toProof_eq_genesis {B : Block V} :
    B.toProof = DecoupledConsensusModel.Block.genesis ↔ B = .genesis := by
  cases B <;> simp [toProof]

/-- The named image of the genesis block is the genesis `NamedBlock`. -/
@[simp] theorem toProofNamed_genesis :
    (Block.genesis : Block V).toProofNamed = DecoupledConsensusModel.NamedBlock.genesis := rfl

/-- A block's named image is the genesis `NamedBlock` exactly when the block is the genesis block. -/
@[simp] theorem toProofNamed_eq_genesis {B : Block V} :
    B.toProofNamed = DecoupledConsensusModel.NamedBlock.genesis ↔ B = .genesis := by
  cases B <;> simp [toProofNamed]

/-- The root of a block's image is the image of the block's root. -/
@[simp] theorem toProof_root (B : Block V) : B.toProof.root = B.root.toProof := by
  cases B <;> rfl

/-- The depth of a block's image is the depth of the block. -/
@[simp] theorem toProof_depth (B : Block V) : B.toProof.depth = B.depth := by
  induction B with
  | genesis => rfl
  | node p s r votes support ats proposer ih =>
      simp only [toProof, DecoupledConsensusModel.Block.depth, Block.depth, ih]

end Block

/-! ## Weights and committees -/

namespace Electorate

/-- The weights `E` as a `DecoupledConsensusModel.Electorate`, with the same weights. -/
def toProof [Fintype V] (E : Electorate V) : DecoupledConsensusModel.Electorate V :=
  ⟨E.weight, E.weight_pos⟩

/-- A `DecoupledConsensusModel.Electorate` as the spec's weights, with the same weights. -/
def toSpec [Fintype V] (E : DecoupledConsensusModel.Electorate V) : Electorate V :=
  ⟨E.weight, E.weight_pos⟩

/-- Mapping the weights to `DecoupledConsensusModel.Electorate` and back gives the weights. -/
@[simp] theorem toSpec_toProof [Fintype V] (E : Electorate V) :
    Electorate.toSpec E.toProof = E := rfl

/-- Mapping a `DecoupledConsensusModel.Electorate` to the spec's type and back gives it. -/
@[simp] theorem toProof_toSpec [Fintype V] (E : DecoupledConsensusModel.Electorate V) :
    (Electorate.toSpec E).toProof = E := rfl

end Electorate

namespace Committees

/-- The committees `K` as `DecoupledConsensusModel.Committees`, with the same members. -/
def toProof (K : Committees V) : DecoupledConsensusModel.Committees V := ⟨K.members⟩

/-- `DecoupledConsensusModel.Committees` as the spec's committees, with the same members. -/
def toSpec (K : DecoupledConsensusModel.Committees V) : Committees V := ⟨K.members⟩

/-- Mapping the committees to `DecoupledConsensusModel.Committees` and back gives the committees. -/
@[simp] theorem toSpec_toProof (K : Committees V) : Committees.toSpec K.toProof = K := rfl

/-- Mapping `DecoupledConsensusModel.Committees` to the spec's type and back gives the committees. -/
@[simp] theorem toProof_toSpec (K : DecoupledConsensusModel.Committees V) :
    (Committees.toSpec K).toProof = K := rfl

end Committees

/-! ## The objects a node sends -/

namespace NamedObject

/-- The object `o` as an `Execution.NamedObject`: the same case, a block mapped by
    `Block.toProofNamed`, a Goldfish vote by `GoldfishVote.toProof`, an attestation by
    `Attestation.toProofNamed`. -/
def toProof : NamedObject V → DecoupledConsensusModel.Execution.NamedObject V
  | .block B => .block B.toProofNamed
  | .gfVote vote => .gfVote vote.toProof
  | .attest a => .attest a.toProofNamed

/-- An `Execution.NamedObject` as a spec object: the same case, its content mapped by
    `Block.toSpecNamed`, `GoldfishVote.toSpec` or `Attestation.toSpecNamed`. -/
def toSpec : DecoupledConsensusModel.Execution.NamedObject V → NamedObject V
  | .block B => .block (Block.toSpecNamed B)
  | .gfVote vote => .gfVote (GoldfishVote.toSpec vote)
  | .attest a => .attest (Attestation.toSpecNamed a)

/-- Mapping an object to `Execution.NamedObject` and back gives the object. -/
@[simp] theorem toSpec_toProof (o : NamedObject V) : NamedObject.toSpec o.toProof = o := by
  cases o <;> simp [toProof, toSpec]

/-- Mapping an `Execution.NamedObject` to the spec's type and back gives the object. -/
@[simp] theorem toProof_toSpec (o : DecoupledConsensusModel.Execution.NamedObject V) :
    (NamedObject.toSpec o).toProof = o := by
  cases o <;> simp [toProof, toSpec]

end NamedObject

/-! ## Grade results, a round's grades and the saved grades -/

namespace GradeResult

/-- The grade result as an `Option (Option (Block V))`: `pending` maps to `none`, `computed G` to
    `some` of `G` with its block mapped by `Block.toProof`. -/
def toProof : GradeResult V → Option (Option (DecoupledConsensusModel.Block V))
  | .pending => none
  | .computed G => some (G.map Block.toProof)

/-- An `Option (Option (Block V))` as a grade result: `none` maps to `pending`, `some G` to
    `computed` of `G` with its block mapped by `Block.toSpec`. -/
def toSpec : Option (Option (DecoupledConsensusModel.Block V)) → GradeResult V
  | none => .pending
  | some G => .computed (G.map Block.toSpec)

/-- Mapping an `Option (Option (Block V))` to a grade result and back gives it. -/
@[simp] theorem toProof_toSpec (result : Option (Option (DecoupledConsensusModel.Block V))) :
    (GradeResult.toSpec result).toProof = result := by
  cases result with
  | none => rfl
  | some G => simp [toSpec, toProof, Option.map_map]

/-- The image of the pending result is `none`. -/
@[simp] theorem toProof_pending :
    (GradeResult.pending : GradeResult V).toProof = none := rfl

/-- The image of the result computed as `G` is `some` of `G` with its block mapped. -/
@[simp] theorem toProof_computed (G : Option (Block V)) :
    (GradeResult.computed G).toProof = some (G.map Block.toProof) := rfl

/-- The image of a grade result is `none` exactly when the result is pending. -/
@[simp] theorem toProof_eq_none {result : GradeResult V} :
    result.toProof = none ↔ result = .pending := by
  cases result <;> simp [toProof]

end GradeResult

namespace RoundGrades

/-- A round's grades as a `Protocol.Frame`: each of the three results mapped by
    `GradeResult.toProof`. -/
def toProof (g : RoundGrades V) : DecoupledConsensusModel.Protocol.Frame V :=
  ⟨g.g0.toProof, g.g1.toProof, g.g2.toProof⟩

/-- The grade-0 result of the image is the image of the grade-0 result. -/
@[simp] theorem toProof_g0 (g : RoundGrades V) : g.toProof.g0 = g.g0.toProof := rfl

/-- The grade-1 result of the image is the image of the grade-1 result. -/
@[simp] theorem toProof_g1 (g : RoundGrades V) : g.toProof.g1 = g.g1.toProof := rfl

/-- The grade-2 result of the image is the image of the grade-2 result. -/
@[simp] theorem toProof_g2 (g : RoundGrades V) : g.toProof.g2 = g.g2.toProof := rfl

end RoundGrades

namespace SavedGrades

/-- The saved grades as a `Protocol.Cache`: the same round, each of the two rounds' grades mapped by
    `RoundGrades.toProof`. -/
def toProof (c : SavedGrades V) : DecoupledConsensusModel.Protocol.Cache V :=
  ⟨c.round, c.current.toProof, c.next.toProof⟩

/-- The round of the image is the round of the saved grades. -/
@[simp] theorem toProof_round (c : SavedGrades V) : c.toProof.round = c.round := rfl

/-- The current round's grades of the image are the image of the current round's grades. -/
@[simp] theorem toProof_current (c : SavedGrades V) :
    c.toProof.current = c.current.toProof := rfl

/-- The next round's grades of the image are the image of the next round's grades. -/
@[simp] theorem toProof_next (c : SavedGrades V) : c.toProof.next = c.next.toProof := rfl

end SavedGrades

namespace Protocol

/-! ## The chain state -/

namespace ChainState

/-- The chain state `σ` as a `Protocol.ChainState`: the same slot, heights, flag and sets of
    validators, each of the blocks `L`, `T_h`, `J`, `F` mapped by `Block.toProof`. -/
def toProof (σ : ChainState V) : DecoupledConsensusModel.Protocol.ChainState V where
  L := σ.L.toProof
  s := σ.s
  h := σ.h
  T_h := σ.T_h.toProof
  nj := σ.nj
  target_participation := σ.target_participation
  progress := σ.progress
  finalize := σ.finalize
  J := σ.J.toProof
  h_j := σ.h_j
  F := σ.F.toProof
  h_F := σ.h_F

/-- A `Protocol.ChainState` as a spec chain state: each of its four blocks mapped by `Block.toSpec`,
    every other field the same. -/
def toSpec (σ : DecoupledConsensusModel.Protocol.ChainState V) : ChainState V where
  L := Block.toSpec σ.L
  s := σ.s
  h := σ.h
  T_h := Block.toSpec σ.T_h
  nj := σ.nj
  target_participation := σ.target_participation
  progress := σ.progress
  finalize := σ.finalize
  J := Block.toSpec σ.J
  h_j := σ.h_j
  F := Block.toSpec σ.F
  h_F := σ.h_F

/-- Mapping a `Protocol.ChainState` to the spec's type and back gives it. -/
@[simp] theorem toProof_toSpec (σ : DecoupledConsensusModel.Protocol.ChainState V) :
    (ChainState.toSpec σ).toProof = σ := by
  cases σ
  simp [toProof, toSpec]

/-- The image of the initial chain state is the initial chain state. -/
@[simp] theorem toProof_initial :
    (ChainState.initial : ChainState V).toProof =
      DecoupledConsensusModel.Protocol.ChainState.initial := rfl

/-- The latest block of the image is the image of the latest block. -/
@[simp] theorem toProof_L (σ : ChainState V) : σ.toProof.L = σ.L.toProof := rfl

/-- The slot of the image is the slot of the chain state. -/
@[simp] theorem toProof_s (σ : ChainState V) : σ.toProof.s = σ.s := rfl

/-- The height of the image is the height of the chain state. -/
@[simp] theorem toProof_h (σ : ChainState V) : σ.toProof.h = σ.h := rfl

/-- The block `T_h` of the image is the image of the chain state's `T_h`. -/
@[simp] theorem toProof_T_h (σ : ChainState V) : σ.toProof.T_h = σ.T_h.toProof := rfl

/-- The nonjustifiable flag of the image is the chain state's. -/
@[simp] theorem toProof_nj (σ : ChainState V) : σ.toProof.nj = σ.nj := rfl

/-- The target participation of the image is the chain state's. -/
@[simp] theorem toProof_target_participation (σ : ChainState V) :
    σ.toProof.target_participation = σ.target_participation := rfl

/-- The progress set of the image is the chain state's. -/
@[simp] theorem toProof_progress (σ : ChainState V) : σ.toProof.progress = σ.progress := rfl

/-- The finalize set of the image is the chain state's. -/
@[simp] theorem toProof_finalize (σ : ChainState V) : σ.toProof.finalize = σ.finalize := rfl

/-- The justified block of the image is the image of the justified block. -/
@[simp] theorem toProof_J (σ : ChainState V) : σ.toProof.J = σ.J.toProof := rfl

/-- The justification height of the image is the chain state's. -/
@[simp] theorem toProof_h_j (σ : ChainState V) : σ.toProof.h_j = σ.h_j := rfl

/-- The finalized block of the image is the image of the finalized block. -/
@[simp] theorem toProof_F (σ : ChainState V) : σ.toProof.F = σ.F.toProof := rfl

/-- The finalization height of the image is the chain state's. -/
@[simp] theorem toProof_h_F (σ : ChainState V) : σ.toProof.h_F = σ.h_F := rfl

end ChainState

/-! ## SG votes, justifications, tokens and phases -/

namespace SGVote

/-- The SG vote `u` as a `Protocol.SGVote`: the same validator and round, the confirmed root mapped
    by `BlockId.toProof`. -/
def toProof (u : SGVote V) : DecoupledConsensusModel.Protocol.SGVote V :=
  ⟨u.val_index, u.round, u.confirmed.map BlockId.toProof⟩

/-- A `Protocol.SGVote` as a spec SG vote: the same validator and round, the confirmed root mapped
    by `BlockId.toSpec`. -/
def toSpec (u : DecoupledConsensusModel.Protocol.SGVote V) : SGVote V :=
  ⟨u.val_index, u.round, u.confirmed.map BlockId.toSpec⟩

/-- Mapping an SG vote to `Protocol.SGVote` and back gives the vote. -/
@[simp] theorem toSpec_toProof (u : SGVote V) : SGVote.toSpec u.toProof = u := by
  cases u
  simp [toProof, toSpec, Option.map_map]

/-- Mapping a `Protocol.SGVote` to the spec's type and back gives the vote. -/
@[simp] theorem toProof_toSpec (u : DecoupledConsensusModel.Protocol.SGVote V) :
    (SGVote.toSpec u).toProof = u := by
  cases u
  simp [toProof, toSpec, Option.map_map]

/-- `SGVote.toProof` is injective: two SG votes with the same image are equal. -/
theorem toProof_injective : Function.Injective (SGVote.toProof (V := V)) :=
  Function.LeftInverse.injective toSpec_toProof

/-- `SGVote.toProof` as an embedding, for `Finset.map`. -/
def toProofEmb : SGVote V ↪ DecoupledConsensusModel.Protocol.SGVote V :=
  ⟨toProof, toProof_injective⟩

/-- The function of the embedding `SGVote.toProofEmb` is `SGVote.toProof`. -/
@[simp] theorem coe_toProofEmb : ⇑(toProofEmb (V := V)) = toProof := rfl

end SGVote

/-- `HeightId.mk h a.toProof < HeightId.mk h' b.toProof` holds exactly when `(h, a)` is less than
    `(h', b)` in lexicographic order. -/
@[simp] theorem heightId_mk_toProof_lt (h h' : Height) (a b : BlockId) :
    DecoupledConsensusModel.Protocol.HeightId.mk h a.toProof <
        DecoupledConsensusModel.Protocol.HeightId.mk h' b.toProof ↔
      (h, a) <[lex] (h', b) := by
  show toLex (h, a.toProof) < toLex (h', b.toProof) ↔ toLex (h, a) < toLex (h', b)
  simp only [Prod.Lex.toLex_lt_toLex, BlockId.toProof_lt]

namespace Token

/-- The token `x`, whose key is a confirmed root or `none`, as a `Protocol.Token`: the same round,
    the key mapped by `Option.map BlockId.toProof`. -/
def toProof (x : Token (Option BlockId)) :
    DecoupledConsensusModel.Protocol.Token (Option DecoupledConsensusModel.BlockId) :=
  ⟨x.round, x.key.map BlockId.toProof⟩

/-- A `Protocol.Token` whose key is a confirmed root or `none`, as a spec token: the same round, the
    key mapped by `Option.map BlockId.toSpec`. -/
def toSpec (x : DecoupledConsensusModel.Protocol.Token (Option DecoupledConsensusModel.BlockId)) :
    Token (Option BlockId) :=
  ⟨x.round, x.key.map BlockId.toSpec⟩

/-- Mapping a token to `Protocol.Token` and back gives the token. -/
@[simp] theorem toSpec_toProof (x : Token (Option BlockId)) : Token.toSpec x.toProof = x := by
  cases x
  simp [toProof, toSpec, Option.map_map]

/-- `Token.toProof` is injective: two tokens with the same image are equal. -/
theorem toProof_injective : Function.Injective Token.toProof :=
  Function.LeftInverse.injective toSpec_toProof

/-- `Token.toProof` as an embedding, for `Finset.map`. -/
def toProofEmb :
    Token (Option BlockId) ↪
      DecoupledConsensusModel.Protocol.Token (Option DecoupledConsensusModel.BlockId) :=
  ⟨toProof, toProof_injective⟩

/-- The function of the embedding `Token.toProofEmb` is `Token.toProof`. -/
@[simp] theorem coe_toProofEmb : ⇑toProofEmb = toProof := rfl

end Token

namespace Phase

/-- The phase `p` as a `Protocol.Phase`, the same one of `g0`, `g1`, `g2`. -/
def toProof : Phase → DecoupledConsensusModel.Protocol.Phase
  | .g0 => .g0
  | .g1 => .g1
  | .g2 => .g2

/-- A `Protocol.Phase` as a spec phase, the same one of `g0`, `g1`, `g2`. -/
def toSpec : DecoupledConsensusModel.Protocol.Phase → Phase
  | .g0 => .g0
  | .g1 => .g1
  | .g2 => .g2

/-- Mapping a phase to `Protocol.Phase` and back gives the phase. -/
@[simp] theorem toSpec_toProof (p : Phase) : Phase.toSpec p.toProof = p := by
  cases p <;> rfl

/-- Mapping a `Protocol.Phase` to the spec's type and back gives the phase. -/
@[simp] theorem toProof_toSpec (p : DecoupledConsensusModel.Protocol.Phase) :
    (Phase.toSpec p).toProof = p := by
  cases p <;> rfl

end Phase

/-! ## The inputs of the duties -/

namespace ProposalInput

/-- The proposal duty's input `x` as a `Protocol.ProposalInput`: the same slot and proposer, the
    parent, the root and the Goldfish votes mapped by their `toProof`. -/
def toProof (x : ProposalInput V) : DecoupledConsensusModel.Protocol.ProposalInput V :=
  ⟨x.parent.toProof, x.slot, x.root.toProof, x.gf_votes.map GoldfishVote.toProof,
    x.gf_support_votes.map GoldfishVote.toProof, x.proposer⟩

end ProposalInput

namespace AttestationInput

/-- The attestation duty's input `x` as a `Protocol.AttestationInput`: the same validator, round and
    heights, every root mapped by `BlockId.toProof`. -/
def toProof (x : AttestationInput V) : DecoupledConsensusModel.Protocol.AttestationInput V :=
  ⟨x.val_index, x.round, x.confirmed.map BlockId.toProof,
    x.fields.map (fun f => (f.1, f.2.1.toProof, f.2.2)), x.h_j, x.J.toProof, x.h_F⟩

end AttestationInput

/-! ## Grade reads -/

namespace GradeRead

/-- The grade read `g` as a `Protocol.GradeRead`: the anchor and the grade-2 candidate mapped by
    `Block.toProof`, the grade-0 test applied to the `Block.toSpec` form of its block, and the
    proposition `g.rawG2 = true`. -/
def toProof (g : GradeRead V) : DecoupledConsensusModel.Protocol.GradeRead V where
  anchor := g.anchor.toProof
  Q2 := g.Q2.map Block.toProof
  clear := fun B => g.clear (Block.toSpec B)
  rawG2 := g.rawG2 = true
  rawG2_decidable := inferInstance

end GradeRead

end Protocol

/-! ## The signing history -/

namespace SigningHistory

/-- The embedding that maps a timeout vote of the signing history, a height and a root, to the same
    height and the root's image under `BlockId.toProof`. -/
def timeoutToProofEmb : Height × BlockId ↪ Height × DecoupledConsensusModel.BlockId :=
  ⟨fun p => (p.1, p.2.toProof), fun p q h => by
    cases p
    cases q
    simp only [Prod.mk.injEq, BlockId.toProof_inj] at h
    rw [h.1, h.2]⟩

/-- The embedding that maps a height and a `DecoupledConsensusModel.BlockId` to the same height and
    the root's image under `BlockId.toSpec`. -/
def timeoutToSpecEmb : Height × DecoupledConsensusModel.BlockId ↪ Height × BlockId :=
  ⟨fun p => (p.1, BlockId.toSpec p.2), fun p q h => by
    cases p
    cases q
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have h2' := congrArg BlockId.toProof h2
    simp only [BlockId.toProof_toSpec] at h2'
    rw [h1, h2']⟩

/-- The function of `SigningHistory.timeoutToProofEmb` maps `(h, b)` to `(h, b.toProof)`. -/
@[simp] theorem timeoutToProofEmb_apply (p : Height × BlockId) :
    timeoutToProofEmb p = (p.1, p.2.toProof) := rfl

/-- The function of `SigningHistory.timeoutToSpecEmb` maps `(h, b)` to `(h, BlockId.toSpec b)`. -/
@[simp] theorem timeoutToSpecEmb_apply (p : Height × DecoupledConsensusModel.BlockId) :
    timeoutToSpecEmb p = (p.1, BlockId.toSpec p.2) := rfl

/-- The signing history `x` as a `Protocol.NamedRecord`: its three height-by-height fields form the
    `legacy` part, each root mapped by `BlockId.toProof`; its timeout votes form the
    `timeoutHistory`, mapped by `SigningHistory.timeoutToProofEmb`. -/
def toProof (x : SigningHistory) : DecoupledConsensusModel.Protocol.NamedRecord :=
  ⟨⟨fun h => (x.target h).map BlockId.toProof, x.timeout, fun h => (x.lock h).map BlockId.toProof⟩,
    x.timeouts.map timeoutToProofEmb⟩

/-- The target at height `h` in the image is the signing history's target at `h`, its root mapped. -/
@[simp] theorem toProof_legacy_target (x : SigningHistory) (h : Height) :
    x.toProof.legacy.target h = (x.target h).map BlockId.toProof := rfl

/-- The timeout flag at height `h` in the image is the signing history's. -/
@[simp] theorem toProof_legacy_timeout (x : SigningHistory) (h : Height) :
    x.toProof.legacy.timeout h = x.timeout h := rfl

/-- The lock at height `h` in the image is the signing history's lock at `h`, its root mapped. -/
@[simp] theorem toProof_legacy_lock (x : SigningHistory) (h : Height) :
    x.toProof.legacy.lock h = (x.lock h).map BlockId.toProof := rfl

/-- The timeout votes of the image are the signing history's, each root mapped. -/
@[simp] theorem toProof_timeoutHistory (x : SigningHistory) :
    x.toProof.timeoutHistory = x.timeouts.map timeoutToProofEmb := rfl

end SigningHistory

/-! ## Functions declared with the same body on both sides -/

/-- The spec's `pickUnique?` is `DecoupledConsensusModel.pickUnique?`. -/
theorem pickUnique?_eq : @pickUnique? = @DecoupledConsensusModel.pickUnique? := rfl

/-- The spec's `occurrenceBefore` is `DecoupledConsensusModel.occurrenceBefore`. -/
theorem occurrenceBefore_eq : occurrenceBefore = DecoupledConsensusModel.occurrenceBefore := by
  funext x Γ
  cases x <;> rfl

/-- When every member of `S` has a stamp in `ts`, the spec's `beforeCutoff ts Γ S` does not raise
    and returns `DecoupledConsensusModel.beforeCutoff ts Γ S`. -/
theorem beforeCutoff_eq_ok {α : Type} [DecidableEq α] (ts : TimestampMap α) (Γ : Time)
    (S : Finset α) (h : ∀ x ∈ S, ts x ≠ none) :
    beforeCutoff ts Γ S = .ok (DecoupledConsensusModel.beforeCutoff ts Γ S) := by
  induction S using Finset.induction_on with
  | empty => rfl
  | insert a S ha ih =>
    have ih' := ih (fun x hx => h x (Finset.mem_insert_of_mem hx))
    obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.mp (h a (Finset.mem_insert_self a S))
    unfold beforeCutoff Finset.filterM at ih' ⊢
    rw [Finset.fold_insert ha, ih']
    simp only [hu, Finset.unionM, DecoupledConsensusModel.beforeCutoff,
      DecoupledConsensusModel.stampedBefore, Finset.filter_insert, liftM, monadLift,
      MonadLift.monadLift, Option.elim]
    by_cases hlt : u < (Γ : Stamp)
    · simp [hlt, bind, Except.bind, pure, Except.pure]
    · simp [hlt, bind, Except.bind, pure, Except.pure]

/-- If `a` is the only member of `T` that passes `p`, then `pickUnique? T p = some a`. -/
theorem pickUnique?_eq_some {α : Type} [DecidableEq α] (T : Finset α) (p : α → Bool) (a : α)
    (ha : a ∈ T) (hp : p a = true) (hu : ∀ b ∈ T, p b = true → b = a) :
    pickUnique? T p = some a := by
  have h : ∃! b, b ∈ T ∧ p b = true := ⟨a, ⟨ha, hp⟩, fun b hb => hu b hb.1 hb.2⟩
  unfold pickUnique?
  rw [dif_pos h, Option.some.injEq]
  exact hu _ (Finset.choose_mem _ _ h) (Finset.choose_property _ _ h)

/-- `DecoupledConsensusModel.pickUnique? (T.map f) p` is the spec's `pickUnique?` on `T` with the
    test `p ∘ f`, its result mapped by `f`. -/
theorem pickUnique?_map {α β : Type} [DecidableEq α] [DecidableEq β] (T : Finset α) (f : α ↪ β)
    (p : β → Bool) :
    DecoupledConsensusModel.pickUnique? (T.map f) p = (pickUnique? T (fun a => p (f a))).map f := by
  unfold DecoupledConsensusModel.pickUnique? pickUnique?
  by_cases h : ∃! a, a ∈ T ∧ p (f a) = true
  · have h' : ∃! b, b ∈ T.map f ∧ p b = true := by
      obtain ⟨a, ⟨ha, hp⟩, hu⟩ := h
      refine ⟨f a, ⟨Finset.mem_map_of_mem f ha, hp⟩, ?_⟩
      rintro b ⟨hb, hpb⟩
      obtain ⟨a', ha', rfl⟩ := Finset.mem_map.mp hb
      rw [hu a' ⟨ha', hpb⟩]
    rw [dif_pos h', dif_pos h, Option.map_some, Option.some.injEq]
    exact h'.unique (Finset.choose_spec _ _ h')
      ⟨Finset.mem_map_of_mem f (Finset.choose_mem _ _ h), Finset.choose_property _ _ h⟩
  · have h' : ¬ ∃! b, b ∈ T.map f ∧ p b = true := by
      rintro ⟨b, ⟨hb, hp⟩, hu⟩
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hb
      exact h ⟨a, ⟨ha, hp⟩, fun a' ha' =>
        f.injective (hu (f a') ⟨Finset.mem_map_of_mem f ha'.1, ha'.2⟩)⟩
    rw [dif_neg h', dif_neg h]
    rfl

/-- For `f` injective on `T`, `DecoupledConsensusModel.pickUnique? (T.image f) p` is the spec's
    `pickUnique?` on `T` with the test `p ∘ f`, its result mapped by `f`. -/
theorem pickUnique?_image {α β : Type} [DecidableEq α] [DecidableEq β] (T : Finset α) (f : α → β)
    (hf : Set.InjOn f (↑T : Set α)) (p : β → Bool) :
    DecoupledConsensusModel.pickUnique? (T.image f) p = (pickUnique? T (fun a => p (f a))).map f := by
  unfold DecoupledConsensusModel.pickUnique? pickUnique?
  by_cases h : ∃! a, a ∈ T ∧ p (f a) = true
  · have h' : ∃! b, b ∈ T.image f ∧ p b = true := by
      obtain ⟨a, ⟨ha, hp⟩, hu⟩ := h
      refine ⟨f a, ⟨Finset.mem_image_of_mem f ha, hp⟩, ?_⟩
      rintro b ⟨hb, hpb⟩
      obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp hb
      rw [hu a' ⟨ha', hpb⟩]
    rw [dif_pos h', dif_pos h, Option.map_some, Option.some.injEq]
    exact h'.unique (Finset.choose_spec _ _ h')
      ⟨Finset.mem_image_of_mem f (Finset.choose_mem _ _ h), Finset.choose_property _ _ h⟩
  · have h' : ¬ ∃! b, b ∈ T.image f ∧ p b = true := by
      rintro ⟨b, ⟨hb, hp⟩, hu⟩
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
      exact h ⟨a, ⟨ha, hp⟩, fun a' ha' =>
        hf (Finset.mem_coe.mpr ha'.1) (Finset.mem_coe.mpr ha)
          (hu (f a') ⟨Finset.mem_image_of_mem f ha'.1, ha'.2⟩)⟩
    rw [dif_neg h', dif_neg h]
    rfl

/-!
## The store, one way

The store maps to `Protocol.Store` (`Store.toProof`) and to `Protocol.NamedStore`
(`Store.toProofNamed`), with no map back. Since two blocks of the tree can have the same image, the
image of the store reads a stamp and a chain state at a block through `Store.blockOfImage`.
-/

namespace Store

section

variable [DecidableEq V]

/-- The one block of the store's tree `st.T` whose image is `B`; `none` when the tree holds no such
    block, or more than one. -/
def blockWithImage? (st : Store V) (B : DecoupledConsensusModel.Block V) : Option (Block V) :=
  pickUnique? st.T (fun B' => decide (B'.toProof = B))

/-- When `Block.toProof` is injective on the tree `st.T`, the block of the tree with the image of a
    tree block `B` is `B`. -/
theorem blockWithImage?_toProof_of_mem (st : Store V)
    (hinj : Set.InjOn (Block.toProof (V := V)) (↑st.T : Set (Block V))) {B : Block V}
    (hB : B ∈ st.T) : st.blockWithImage? B.toProof = some B :=
  pickUnique?_eq_some st.T _ B hB (decide_eq_true rfl) (fun _ hB' h =>
    hinj (Finset.mem_coe.mpr hB') (Finset.mem_coe.mpr hB) (of_decide_eq_true h))

/-- The block `st.blockWithImage? B` returns is in the tree `st.T` and has the image `B`. -/
theorem blockWithImage?_eq_some (st : Store V) {B : DecoupledConsensusModel.Block V}
    {B' : Block V} (h : st.blockWithImage? B = some B') : B' ∈ st.T ∧ B'.toProof = B := by
  unfold blockWithImage? pickUnique? at h
  split at h
  · rename_i hex
    rw [Option.some.injEq] at h
    subst h
    exact ⟨Finset.choose_mem _ _ hex, of_decide_eq_true (Finset.choose_property _ _ hex)⟩
  · exact absurd h (by simp)

/-- The spec block that stands for the block `B` in the tree `T`: the genesis block for the genesis
    block, the one block of `T` whose image is `B` when there is exactly one, and otherwise `B`
    rebuilt on `T`. Its image is `B` in every case. -/
def blockOfImageIn (T : Finset (Block V)) : DecoupledConsensusModel.Block V → Block V
  | .genesis => .genesis
  | B@(.node p s r votes support ats proposer) =>
      (pickUnique? T (fun B' => decide (B'.toProof = B))).getD
        (.node (blockOfImageIn T p) s (BlockId.toSpec r) (votes.map GoldfishVote.toSpec)
          (support.map GoldfishVote.toSpec) (ats.map Attestation.toSpec) proposer)

/-- The spec block that stands for the block `B` on the store `st`, `blockOfImageIn st.T B`. -/
def blockOfImage (st : Store V) : DecoupledConsensusModel.Block V → Block V :=
  blockOfImageIn st.T

/-- The block that stands for `B` in the tree `T` has the image `B`. -/
@[simp] theorem toProof_blockOfImageIn (T : Finset (Block V))
    (B : DecoupledConsensusModel.Block V) : (blockOfImageIn T B).toProof = B := by
  induction B with
  | genesis => rfl
  | node p s r votes support ats proposer ih =>
      unfold blockOfImageIn
      cases h : pickUnique? T
          (fun B' => decide (B'.toProof = .node p s r votes support ats proposer)) with
      | none => simp [Block.toProof, ih, List.map_map]
      | some B' =>
          unfold pickUnique? at h
          split at h
          · rename_i hex
            rw [Option.some.injEq] at h
            subst h
            exact of_decide_eq_true (Finset.choose_property _ _ hex)
          · exact absurd h (by simp)

/-- The block that stands for `B` on the store `st` has the image `B`. -/
@[simp] theorem toProof_blockOfImage (st : Store V) (B : DecoupledConsensusModel.Block V) :
    (st.blockOfImage B).toProof = B :=
  toProof_blockOfImageIn st.T B

/-- `st.blockOfImage` is injective. -/
theorem blockOfImage_injective (st : Store V) : Function.Injective st.blockOfImage :=
  Function.LeftInverse.injective (g := Block.toProof) (toProof_blockOfImage st)

/-- `st.blockOfImage` as an embedding, for `Finset.map`. -/
def blockOfImageEmb (st : Store V) : DecoupledConsensusModel.Block V ↪ Block V :=
  ⟨st.blockOfImage, blockOfImage_injective st⟩

/-- The function of the embedding `st.blockOfImageEmb` is `st.blockOfImage`. -/
@[simp] theorem coe_blockOfImageEmb (st : Store V) : ⇑st.blockOfImageEmb = st.blockOfImage := rfl

/-- When `Block.toProof` is injective on the tree `st.T`, the block that stands for the image of a
    tree block `X` is `X`. -/
theorem blockOfImage_toProof_of_injOn (st : Store V)
    (hinj : Set.InjOn (Block.toProof (V := V)) (↑st.T : Set (Block V))) {X : Block V}
    (hX : X ∈ st.T) : st.blockOfImage X.toProof = X := by
  have hlook := blockWithImage?_toProof_of_mem st hinj hX
  cases X with
  | genesis => rfl
  | node p s r votes support ats proposer =>
      have hn : (Block.node p s r votes support ats proposer).toProof =
          .node p.toProof s r.toProof (votes.map GoldfishVote.toProof)
            (support.map GoldfishVote.toProof) (ats.map Attestation.toProof) proposer := rfl
      rw [hn] at hlook ⊢
      unfold blockOfImage blockOfImageIn
      unfold blockWithImage? at hlook
      rw [hlook]
      rfl

/-- When no two blocks of the tree `st.T` have the same root, the block that stands for the image of
    a tree block `X` is `X`. -/
theorem blockOfImage_toProof_of_mem (st : Store V)
    (hroots : ∀ B ∈ st.T, ∀ B' ∈ st.T, B.root = B'.root → B = B') {X : Block V}
    (hX : X ∈ st.T) : st.blockOfImage X.toProof = X := by
  have hinj : Set.InjOn (Block.toProof (V := V)) (↑st.T : Set (Block V)) := by
    intro B hB B' hB' h
    refine hroots B (Finset.mem_coe.mp hB) B' (Finset.mem_coe.mp hB') ?_
    have := congrArg DecoupledConsensusModel.Block.root h
    simpa only [Block.toProof_root, BlockId.toProof_inj] using this
  exact blockOfImage_toProof_of_injOn st hinj hX

/-- The store `st` as a `Protocol.Store`. The tree is the set of images of `st.T`; the stamp and
    chain state of a block `B` are read at `st.blockOfImage B`; the stamps of votes are read at the
    `toSpec` form of the vote; votes, attestations and blocks are mapped by their `toProof`. The
    field `sg_votes` holds `st.attestations`. -/
def toProof (st : Store V) : DecoupledConsensusModel.Protocol.Store V where
  t := st.t
  s := st.s
  T := st.T.image Block.toProof
  timestamp_block := fun B => st.timestamp_block (st.blockOfImage B)
  timestamp_vote := fun vote => st.timestamp_vote (GoldfishVote.toSpec vote)
  timestamp_sg_vote := fun u => st.timestamp_sg_vote (Protocol.SGVote.toSpec u)
  σ := fun B => (st.σ (st.blockOfImage B)).toProof
  gf_votes := fun s => (st.gf_votes s).map GoldfishVote.toProof
  sg_votes := fun r => (st.attestations r).map Attestation.toProof
  F := st.F.toProof
  J := st.J.toProof
  h_j := st.h_j
  h_max := st.h_max
  live_confirmed := st.live_confirmed.toProof
  latest_confirmed := st.latest_confirmed.toProof
  latest_stable := st.latest_stable.toProof

/-- The clock of the image is the store's clock. -/
@[simp] theorem toProof_t (st : Store V) : st.toProof.t = st.t := rfl

/-- The slot of the image is the store's slot. -/
@[simp] theorem toProof_s (st : Store V) : st.toProof.s = st.s := rfl

/-- The tree of the image is the set of the images of the blocks of the store's tree. -/
@[simp] theorem toProof_T (st : Store V) : st.toProof.T = st.T.image Block.toProof := rfl

/-- The stamp of a block `B` in the image is the store's stamp of `st.blockOfImage B`. -/
@[simp] theorem toProof_timestamp_block (st : Store V) (B : DecoupledConsensusModel.Block V) :
    st.toProof.timestamp_block B = st.timestamp_block (st.blockOfImage B) := rfl

/-- When `Block.toProof` is injective on the tree `st.T`, the stamp of the image of a tree block
    `B`, in the image of the store, is the store's stamp of `B`. -/
theorem toProof_timestamp_block_of_mem (st : Store V)
    (hinj : Set.InjOn (Block.toProof (V := V)) (↑st.T : Set (Block V))) {B : Block V}
    (hB : B ∈ st.T) : st.toProof.timestamp_block B.toProof = st.timestamp_block B := by
  rw [toProof_timestamp_block, blockOfImage_toProof_of_injOn st hinj hB]

/-- The stamp of a Goldfish vote in the image is the store's stamp of its `toSpec` form. -/
@[simp] theorem toProof_timestamp_vote (st : Store V)
    (vote : DecoupledConsensusModel.GoldfishVote V) :
    st.toProof.timestamp_vote vote = st.timestamp_vote (GoldfishVote.toSpec vote) := rfl

/-- The stamp of an SG vote in the image is the store's stamp of its `toSpec` form. -/
@[simp] theorem toProof_timestamp_sg_vote (st : Store V)
    (u : DecoupledConsensusModel.Protocol.SGVote V) :
    st.toProof.timestamp_sg_vote u = st.timestamp_sg_vote (Protocol.SGVote.toSpec u) := rfl

/-- The chain state of a block `B` in the image is the image of the store's chain state of
    `st.blockOfImage B`. -/
@[simp] theorem toProof_σ (st : Store V) (B : DecoupledConsensusModel.Block V) :
    st.toProof.σ B = (st.σ (st.blockOfImage B)).toProof := rfl

/-- When `Block.toProof` is injective on the tree `st.T`, the chain state of the image of a tree
    block `B`, in the image of the store, is the image of the store's chain state of `B`. -/
theorem toProof_σ_of_mem (st : Store V)
    (hinj : Set.InjOn (Block.toProof (V := V)) (↑st.T : Set (Block V))) {B : Block V}
    (hB : B ∈ st.T) : st.toProof.σ B.toProof = (st.σ B).toProof := by
  rw [toProof_σ, blockOfImage_toProof_of_injOn st hinj hB]

/-- The Goldfish votes of slot `s` in the image are the store's, each mapped. -/
@[simp] theorem toProof_gf_votes (st : Store V) (s : Slot) :
    st.toProof.gf_votes s = (st.gf_votes s).map GoldfishVote.toProof := rfl

/-- The field `sg_votes` of the image at round `r` is the store's attestations of round `r`, each
    mapped by `Attestation.toProof`. -/
@[simp] theorem toProof_sg_votes (st : Store V) (r : Round) :
    st.toProof.sg_votes r = (st.attestations r).map Attestation.toProof := rfl

/-- The finalized block of the image is the image of the store's finalized block. -/
@[simp] theorem toProof_F (st : Store V) : st.toProof.F = st.F.toProof := rfl

/-- The justified block of the image is the image of the store's justified block. -/
@[simp] theorem toProof_J (st : Store V) : st.toProof.J = st.J.toProof := rfl

/-- The justified height of the image is the store's. -/
@[simp] theorem toProof_h_j (st : Store V) : st.toProof.h_j = st.h_j := rfl

/-- The largest chain-state height of the image is the store's. -/
@[simp] theorem toProof_h_max (st : Store V) : st.toProof.h_max = st.h_max := rfl

/-- The block `live_confirmed` of the image is the image of the store's. -/
@[simp] theorem toProof_live_confirmed (st : Store V) :
    st.toProof.live_confirmed = st.live_confirmed.toProof := rfl

/-- The block `latest_confirmed` of the image is the image of the store's. -/
@[simp] theorem toProof_latest_confirmed (st : Store V) :
    st.toProof.latest_confirmed = st.latest_confirmed.toProof := rfl

/-- The block `latest_stable` of the image is the image of the store's. -/
@[simp] theorem toProof_latest_stable (st : Store V) :
    st.toProof.latest_stable = st.latest_stable.toProof := rfl

/-- The store `st` as a `Protocol.NamedStore`: the core is `st.toProof`, `bodies` are the blocks of
    `st.T` mapped by `Block.toProofNamed`, and `sg_rows r` are `st.attestations r` mapped by
    `Attestation.toProofNamed`. -/
def toProofNamed (st : Store V) : DecoupledConsensusModel.Protocol.NamedStore V where
  core := st.toProof
  bodies := st.T.map Block.toProofNamedEmb
  sg_rows := fun r => (st.attestations r).map Attestation.toProofNamed

/-- The core of `st.toProofNamed` is `st.toProof`. -/
@[simp] theorem toProofNamed_core (st : Store V) : st.toProofNamed.core = st.toProof := rfl

/-- The `bodies` of `st.toProofNamed` are the blocks of the store's tree, each mapped by
    `Block.toProofNamed`. -/
@[simp] theorem toProofNamed_bodies (st : Store V) :
    st.toProofNamed.bodies = st.T.map Block.toProofNamedEmb := rfl

/-- The `sg_rows r` of `st.toProofNamed` are the store's attestations of round `r`, each mapped by
    `Attestation.toProofNamed`. -/
@[simp] theorem toProofNamed_sg_rows (st : Store V) (r : Round) :
    st.toProofNamed.sg_rows r = (st.attestations r).map Attestation.toProofNamed := rfl

end

end Store

/-! ## The node state, one way -/

namespace NodeState

/-- The node state `n` as an `Execution.NamedNodeState`: the store `n.st.toProofNamed`, the signing
    record `n.signingHistory.toProof`, and the saved grades `n.st.saved_grades.toProof` as `cache`.
    The validator `n.v` and `n.awakeSince` are dropped. -/
def toProof [DecidableEq V] (n : NodeState V) :
    DecoupledConsensusModel.Execution.NamedNodeState V where
  st := n.st.toProofNamed
  record := n.signingHistory.toProof
  cache := n.st.saved_grades.toProof

/-- The store of the image is `n.st.toProofNamed`. -/
@[simp] theorem toProof_st [DecidableEq V] (n : NodeState V) :
    n.toProof.st = n.st.toProofNamed := rfl

/-- The signing record of the image is the image of the node's signing history. -/
@[simp] theorem toProof_record [DecidableEq V] (n : NodeState V) :
    n.toProof.record = n.signingHistory.toProof := rfl

/-- The `cache` of the image is the image of the store's saved grades. -/
@[simp] theorem toProof_cache [DecidableEq V] (n : NodeState V) :
    n.toProof.cache = n.st.saved_grades.toProof := rfl

end NodeState

/-! ## The parameters -/

section Parameters

variable [DecidableEq V] [Fintype V]

/-- The spec's parameters read from the environment `E`, the round schedule `hc` and the height
    parameters `cfg`: `Δ` from `E`, `R` and `η_SG` from `hc`, `K`, `D` and `timeoutDelay` from
    `cfg`. -/
def Config.toSpec (E : DecoupledConsensusModel.Env V)
    (hc : DecoupledConsensusModel.Protocol.HealConfig)
    (cfg : DecoupledConsensusModel.Protocol.HeightConfig) : Config where
  Δ := E.Δ
  Δ_pos := E.Δ_pos
  R := hc.R
  R_ge_three := hc.R_ge_three
  η_SG := hc.η_SG
  η_SG_ge_one := hc.η_SG_ge_one
  K := cfg.K
  D := cfg.D
  timeoutDelay := cfg.timeoutDelay
  K_ge_four := cfg.K_ge_four
  D_ge_two := cfg.D_ge_two

/-- The spec's provisional values read from the environment `E`: the same proposer of each slot, and
    the committees and the weights mapped by their own `toSpec`. -/
def Provisional.toSpec (E : DecoupledConsensusModel.Env V) : Provisional V where
  proposer := E.proposer
  committees := Committees.toSpec E.committees
  electorate := Electorate.toSpec E.electorate

/-- The spec's external values read from the set-up `S`: the root of the block validator `v`
    proposes in slot `s` is `BlockId.toSpec ((S.node v).new_root s)`. -/
def External.toSpec (S : DecoupledConsensusModel.Execution.Setup V) : External V where
  new_root := fun v s => BlockId.toSpec ((S.node v).new_root s)

end Parameters

/-! ## The functions on blocks, at the mapped blocks -/

section BlockFunctions

variable [DecidableEq V]

namespace Block

/-- The named image of `B` is an ancestor of, or equal to, the named image of `C` exactly when `B`
    is an ancestor of `C` or equal to it. -/
@[simp] theorem toProofNamed_preceq (B C : Block V) :
    DecoupledConsensusModel.NamedBlock.preceq B.toProofNamed C.toProofNamed = B.ancestorEq C := by
  induction C with
  | genesis =>
      simp only [toProofNamed_genesis, DecoupledConsensusModel.NamedBlock.preceq,
        Block.ancestorEq, toProofNamed_eq_genesis]
  | node p s r votes support ats proposer ih =>
      have h : (Block.node p s r votes support ats proposer).toProofNamed =
          .node p.toProofNamed s r.toProof (votes.map GoldfishVote.toProof)
            (support.map GoldfishVote.toProof) (ats.map Attestation.toProofNamed) proposer :=
        rfl
      rw [h, DecoupledConsensusModel.NamedBlock.preceq, ← h, ih]
      simp only [Block.ancestorEq, toProofNamed_inj]

/-- If `B` is an ancestor of `C` or equal to it, the image of `B` is an ancestor of the image of `C`
    or equal to it. -/
theorem toProof_preceq_of_ancestorEq (B C : Block V) (h : B.ancestorEq C = true) :
    DecoupledConsensusModel.Block.preceq B.toProof C.toProof = true := by
  induction C with
  | genesis =>
      simp only [Block.ancestorEq, decide_eq_true_eq] at h
      subst h
      simp [DecoupledConsensusModel.Block.preceq]
  | node p s r votes support ats proposer ih =>
      have hn : (Block.node p s r votes support ats proposer).toProof =
          .node p.toProof s r.toProof (votes.map GoldfishVote.toProof)
            (support.map GoldfishVote.toProof) (ats.map Attestation.toProof) proposer := rfl
      rw [hn, DecoupledConsensusModel.Block.preceq, ← hn]
      simp only [Block.ancestorEq, Bool.or_eq_true, decide_eq_true_eq] at h
      rcases h with h | h
      · simp [h]
      · simp [ih h]

/-- Among the blocks of a set `T` that holds the parent of each of its blocks and on which
    `Block.toProof` is injective, the image of `B` is an ancestor of, or equal to, the image of `C`
    exactly when `B` is an ancestor of `C` or equal to it. -/
theorem toProof_preceq_of_injOn (T : Finset (Block V))
    (hinj : Set.InjOn (Block.toProof (V := V)) (↑T : Set (Block V)))
    (hpar : ∀ B ∈ T, B.parent ∈ T) {B C : Block V} (hB : B ∈ T) (hC : C ∈ T) :
    DecoupledConsensusModel.Block.preceq B.toProof C.toProof = B.ancestorEq C := by
  induction C with
  | genesis =>
      simp only [toProof_genesis, DecoupledConsensusModel.Block.preceq, Block.ancestorEq,
        toProof_eq_genesis]
  | node p s r votes support ats proposer ih =>
      have hn : (Block.node p s r votes support ats proposer).toProof =
          .node p.toProof s r.toProof (votes.map GoldfishVote.toProof)
            (support.map GoldfishVote.toProof) (ats.map Attestation.toProof) proposer := rfl
      have hp : p ∈ T := hpar _ hC
      have heq : B.toProof = (Block.node p s r votes support ats proposer).toProof ↔
          B = Block.node p s r votes support ats proposer :=
        ⟨fun h => hinj (Finset.mem_coe.mpr hB) (Finset.mem_coe.mpr hC) h, fun h => by rw [h]⟩
      rw [hn, DecoupledConsensusModel.Block.preceq, ← hn, ih hp]
      simp only [Block.ancestorEq, heq]

/-- If `B` and `C` are compatible, so are their images. -/
theorem toProof_compatible_of_compatible (B C : Block V) (h : B.compatible C = true) :
    DecoupledConsensusModel.Block.compatible B.toProof C.toProof = true := by
  simp only [Block.compatible, Bool.or_eq_true] at h
  simp only [DecoupledConsensusModel.Block.compatible, Bool.or_eq_true]
  exact h.imp (toProof_preceq_of_ancestorEq B C) (toProof_preceq_of_ancestorEq C B)

/-- Among the blocks of a set `T` that holds the parent of each of its blocks and on which
    `Block.toProof` is injective, the images of two blocks are compatible exactly when the blocks
    are. -/
theorem toProof_compatible_of_injOn (T : Finset (Block V))
    (hinj : Set.InjOn (Block.toProof (V := V)) (↑T : Set (Block V)))
    (hpar : ∀ B ∈ T, B.parent ∈ T) {B C : Block V} (hB : B ∈ T) (hC : C ∈ T) :
    DecoupledConsensusModel.Block.compatible B.toProof C.toProof = B.compatible C := by
  simp only [DecoupledConsensusModel.Block.compatible, Block.compatible,
    toProof_preceq_of_injOn T hinj hpar hB hC, toProof_preceq_of_injOn T hinj hpar hC hB]

omit [DecidableEq V] in
/-- `deeper` on the images of two blocks is `deeper` on the blocks. -/
@[simp] theorem toProof_deeper (B C : Block V) :
    DecoupledConsensusModel.Block.deeper B.toProof C.toProof = Block.deeper B C := by
  simp only [DecoupledConsensusModel.Block.deeper, Block.deeper, toProof_depth, toProof_root,
    BlockId.toProof_lt]

/-- `isDeepestIn` on the images of the blocks of `T`, at the image of `B`, is `isDeepestIn T B`. -/
@[simp] theorem toProof_isDeepestIn (T : Finset (Block V)) (B : Block V) :
    DecoupledConsensusModel.Block.isDeepestIn (T.image Block.toProof) B.toProof =
      Block.isDeepestIn T B := by
  simp only [DecoupledConsensusModel.Block.isDeepestIn, Block.isDeepestIn,
    Finset.forall_mem_image, toProof_deeper]

/-- When `Block.toProof` is injective on `T`, `find?` on the images of the blocks of `T`, at the
    image of the root `r`, is the image of `find? T r`. -/
theorem toProof_find?_of_injOn (T : Finset (Block V))
    (hinj : Set.InjOn (Block.toProof (V := V)) (↑T : Set (Block V))) (r : BlockId) :
    DecoupledConsensusModel.Block.find? (T.image Block.toProof) r.toProof =
      (Block.find? T r).map Block.toProof := by
  unfold DecoupledConsensusModel.Block.find? Block.find?
  rw [pickUnique?_image T Block.toProof hinj]
  simp only [toProof_root, BlockId.toProof_inj]

/-- When `Block.toProof` is injective on `T`, `deepest?` of the images of the blocks of `T` is the
    image of `deepest? T`. -/
theorem toProof_deepest?_of_injOn (T : Finset (Block V))
    (hinj : Set.InjOn (Block.toProof (V := V)) (↑T : Set (Block V))) :
    DecoupledConsensusModel.Block.deepest? (T.image Block.toProof) =
      (Block.deepest? T).map Block.toProof := by
  unfold DecoupledConsensusModel.Block.deepest? Block.deepest?
  rw [pickUnique?_image T Block.toProof hinj]
  simp only [toProof_isDeepestIn]

end Block

end BlockFunctions

end Spec
