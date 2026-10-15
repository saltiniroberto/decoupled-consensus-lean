module
public import Model.Vocabulary.Objects.Blocks

@[expose] public section

/-!
# Named blocks and attestations

Blocks and attestations with their full signed payloads, including height votes that name their
entry block and whether they are timeouts, and their erasure to `Block` and `CombinedAttestation`.
-/

section
/-! ## Named height pairs and attestations -/
namespace DecoupledConsensusModel

inductive NamedHeightPair where
  | empty
  | vote (height : Height) (entry : BlockId) (timeout : Bool)
  deriving DecidableEq, Repr

namespace NamedHeightPair

/-- The height pair a named height pair erases to: a timeout vote erases to `.timeout h`, any other
    vote to `.target h entry`. -/
def erase : NamedHeightPair → HeightPair
  | .empty => .empty
  | .vote h entry timeout => if timeout then .timeout h else .target h entry

/-- Whether a named height pair is a vote, timeout or not, at `height` naming `entry`. -/
def matchesEntry (height : Height) (entry : BlockId) : NamedHeightPair → Bool
  | .empty => false
  | .vote h target _ => decide (h = height ∧ target = entry)

end NamedHeightPair

structure NamedAttestation (V : Type) where
  val_index : V
  round : Round
  confirmed : Option BlockId
  height_pair : NamedHeightPair
  finality_pair : Option FinalityPair
  deriving DecidableEq, Repr

namespace NamedAttestation

/-- The combined attestation a named attestation erases to; a timeout vote erases to a timeout pair. -/
def erase {V : Type} (row : NamedAttestation V) : CombinedAttestation V :=
  ⟨row.val_index, row.round, row.confirmed, row.height_pair.erase, row.finality_pair⟩

end NamedAttestation
end DecoupledConsensusModel
end

section
/-! ## Named blocks -/
namespace DecoupledConsensusModel

inductive NamedBlock (V : Type) where
  | genesis
  | node (parent : NamedBlock V) (slot : Slot) (root : BlockId)
      (gf_votes : List (GoldfishVote V)) (gf_support_votes : List (GoldfishVote V))
      (attestations : List (NamedAttestation V)) (proposer : V)
  deriving DecidableEq, Repr

namespace NamedBlock
variable {V : Type}

def slot : NamedBlock V → Slot
  | .genesis => 0
  | .node _ s _ _ _ _ _ => s

def root : NamedBlock V → BlockId
  | .genesis => genesisRoot
  | .node _ _ r _ _ _ _ => r

def parent : NamedBlock V → NamedBlock V
  | .genesis => .genesis
  | .node p _ _ _ _ _ _ => p

def gf_votes : NamedBlock V → List (GoldfishVote V)
  | .genesis => []
  | .node _ _ _ votes _ _ _ => votes

def attestations : NamedBlock V → List (NamedAttestation V)
  | .genesis => []
  | .node _ _ _ _ _ rows _ => rows

def proposer? : NamedBlock V → Option V
  | .genesis => none
  | .node _ _ _ _ _ _ proposer => some proposer

/-- The block a named block erases to: the same blocks, with every attestation erased. -/
def erase : NamedBlock V → Block V
  | .genesis => .genesis
  | .node p s r votes support rows proposer =>
      .node p.erase s r votes support (rows.map NamedAttestation.erase) proposer

section Ancestry
variable [DecidableEq V]

/-- `A ⪯ B` on named blocks: `A = B`, or `A` is an ancestor of `B`, comparing full named payloads. -/
def preceq (A : NamedBlock V) : NamedBlock V → Bool
  | .genesis => decide (A = .genesis)
  | B@(.node p _ _ _ _ _ _) => decide (A = B) || preceq A p

def Preceq (A B : NamedBlock V) : Prop := preceq A B = true

instance (A B : NamedBlock V) : Decidable (Preceq A B) :=
  inferInstanceAs (Decidable (preceq A B = true))

end Ancestry
end NamedBlock
end DecoupledConsensusModel
end

end
