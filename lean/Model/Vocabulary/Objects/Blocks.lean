module
public import Mathlib.Data.Finset.Basic
public import Model.Vocabulary.Objects.Identifiers

@[expose] public section

/-!
# Blocks, votes and attestations

The wire objects: height and finality pairs, Goldfish votes, combined attestations and blocks, with
block ancestry, compatibility, the deepest-block order and tree resolution.
-/

section
/-! ## Height and finality pairs -/

namespace DecoupledConsensusModel

/-- The height pair of an attestation: a target vote `(h,T)` with `T ≠ ⊥`, an empty-target vote
    `(h,⊥)`, or the empty pair `(⊥,⊥)`. -/
inductive HeightPair where
  /-- The empty pair `(⊥,⊥)`; its height is `⊥`. -/
  | empty
  /-- An empty-target vote `(h,⊥)`. -/
  | timeout (height : Height)
  /-- A target vote `(h,T)` with `T ≠ ⊥`. -/
  | target (height : Height) (target : BlockId)
deriving DecidableEq, Repr

namespace HeightPair

end HeightPair

/-- The finality pair `(h_f, T_f)` with `T_f ≠ ⊥`; the empty finality pair is `none` of an
    `Option FinalityPair`. -/
structure FinalityPair where
  /-- The finality height `a.finalize_height`. -/
  height : Height
  /-- The finality target `a.finalize_target`. -/
  target : BlockId
deriving DecidableEq, Repr

end DecoupledConsensusModel
end

section
/-! ## Votes, attestations and blocks -/

namespace DecoupledConsensusModel

/-- A Goldfish vote `(v, s, B)`: the voter, the slot, and the block it names, by root. -/
structure GoldfishVote (V : Type) where
  /-- The voter. -/
  val_index : V
  /-- The slot of the vote. -/
  slot : Slot
  /-- The root of the block the vote names. -/
  head : BlockId
deriving DecidableEq, Repr

/-- A combined attestation: the validator, the round, the confirmed block, the height pair and the
    finality pair. -/
structure CombinedAttestation (V : Type) where
  /-- The attesting validator. -/
  val_index : V
  /-- The round of the attestation. -/
  round : Round
  /-- The root of the confirmed block (the SG vote); `none` in a timeout vote. -/
  confirmed : Option BlockId
  /-- The height pair `(a.height, a.target)`. -/
  height_pair : HeightPair
  /-- The finality pair `(a.finalize_height, a.finalize_target)`; `none` is the empty pair. -/
  finality_pair : Option FinalityPair
deriving DecidableEq, Repr

namespace CombinedAttestation

variable {V : Type}

end CombinedAttestation

/-- A block: genesis, or a node holding its parent and its fields. -/
inductive Block (V : Type) where
  /-- The genesis block; its slot is `0`, its root `genesisRoot`, and it has no parent. -/
  | genesis
  /-- A non-genesis block: its parent, slot, root, the Goldfish votes it includes, the subset of
      them resolved in the proposer's view at proposal time, its attestations, and its proposer. -/
  | node (parent : Block V) (slot : Slot) (root : BlockId)
      (gf_votes : List (GoldfishVote V))
      (gf_support_votes : List (GoldfishVote V))
      (attestations : List (CombinedAttestation V))
      (proposer : V)
deriving DecidableEq, Repr

namespace Block

variable {V : Type}

/-- The slot of a block; genesis is slot `0`. -/
def slot : Block V → Slot
  | .genesis => 0
  | .node _ s _ _ _ _ _ => s

/-- The root of a block. -/
def root : Block V → BlockId
  | .genesis => genesisRoot
  | .node _ _ r _ _ _ _ => r

/-- The parent of a block, `none` at genesis. -/
def parent? : Block V → Option (Block V)
  | .genesis => none
  | .node p _ _ _ _ _ _ => some p

/-- The parent of a block as a total function, genesis being its own parent. -/
def parent : Block V → Block V
  | .genesis => .genesis
  | .node p _ _ _ _ _ _ => p

/-- The Goldfish votes a block includes. -/
def gf_votes : Block V → List (GoldfishVote V)
  | .genesis => []
  | .node _ _ _ votes _ _ _ => votes

/-- The subset of a block's Goldfish votes resolved in the proposer's view at proposal time. -/
def gf_support_votes : Block V → List (GoldfishVote V)
  | .genesis => []
  | .node _ _ _ _ support _ _ => support

/-- The attestations a block includes. -/
def attestations : Block V → List (CombinedAttestation V)
  | .genesis => []
  | .node _ _ _ _ _ ats _ => ats

/-- The proposer of a block, `none` at genesis. -/
def proposer? : Block V → Option V
  | .genesis => none
  | .node _ _ _ _ _ _ i => some i

/-- The depth of a block: the number of parent edges from genesis. -/
def depth : Block V → Nat
  | .genesis => 0
  | .node p _ _ _ _ _ _ => p.depth + 1

section Ancestry

variable [DecidableEq V]

/-- `B ⪯ C`: `B = C`, or `B` is an ancestor of `C`; computed by following parents from `C`. -/
def preceq (B : Block V) : Block V → Bool
  | .genesis => decide (B = Block.genesis)
  | C@(.node p _ _ _ _ _ _) => decide (B = C) || preceq B p

/-- `B ≺ C`: `B` is a strict ancestor of `C`. -/
def prec (B C : Block V) : Bool :=
  !decide (B = C) && preceq B C

/-- `B ⪯ C` as a proposition. -/
def Preceq (B C : Block V) : Prop :=
  preceq B C = true

/-- `B ≺ C` as a proposition. -/
def Prec (B C : Block V) : Prop :=
  prec B C = true

instance (B C : Block V) : Decidable (Preceq B C) :=
  inferInstanceAs (Decidable (preceq B C = true))

instance (B C : Block V) : Decidable (Prec B C) :=
  inferInstanceAs (Decidable (prec B C = true))

/-- Two blocks are compatible when one is an ancestor of, or equal to, the other. -/
def compatible (B C : Block V) : Bool :=
  preceq B C || preceq C B

/-- One block is an ancestor of the other, or they are equal. -/
def Compatible (B C : Block V) : Prop :=
  Block.compatible B C = true

/-- The deepest order: `deeper B C` holds when `B` has greater depth than `C`, or equal depth and a
    greater root. -/
def deeper (B C : Block V) : Bool :=
  decide (C.depth < B.depth) ||
    (decide (C.depth = B.depth) && decide (C.root < B.root))

end Ancestry

end Block

section Pick

variable {α : Type} [DecidableEq α]

instance decidableExistsUniqueMem (T : Finset α) (p : α → Prop)
    [DecidablePred p] : Decidable (∃! a, a ∈ T ∧ p a) :=
  decidable_of_iff (∃ a ∈ T, p a ∧ ∀ b ∈ T, p b → b = a) <| by
    constructor
    · rintro ⟨a, haT, hpa, huniq⟩
      exact ⟨a, ⟨haT, hpa⟩, fun b hb => huniq b hb.1 hb.2⟩
    · rintro ⟨a, ⟨haT, hpa⟩, huniq⟩
      exact ⟨a, haT, hpa, fun b hbT hpb => huniq b ⟨hbT, hpb⟩⟩

/-- The unique member of `T` satisfying `p`, or `none` when there is no such
member or more than one. Computable, and total without a choice principle. -/
def pickUnique? (T : Finset α) (p : α → Bool) : Option α :=
  if h : ∃! a, a ∈ T ∧ p a = true then
    some (T.choose (fun a => p a = true) h)
  else
    none

end Pick

namespace Block

variable {V : Type} [DecidableEq V]

/-- The block of the tree `T` with root `r`; `none` when no block or more than one block of `T` has
    that root. -/
def find? (T : Finset (Block V)) (r : BlockId) : Option (Block V) :=
  pickUnique? T (fun B => decide (B.root = r))

/-- Whether no block of `T` beats `B` in the `deeper` order. -/
def isDeepestIn (T : Finset (Block V)) (B : Block V) : Bool :=
  decide (∀ C ∈ T, deeper C B = false)

/-- The deepest block of `T`: maximum depth, ties broken by the greater root; `none` on an empty
    tree, or when two distinct blocks share both depth and root. -/
def deepest? (T : Finset (Block V)) : Option (Block V) :=
  pickUnique? T (isDeepestIn T)

end Block

@[inherit_doc] scoped infix:50 " ⪯ " => Block.Preceq
@[inherit_doc] scoped infix:50 " ≺ " => Block.Prec

end DecoupledConsensusModel
end

end
