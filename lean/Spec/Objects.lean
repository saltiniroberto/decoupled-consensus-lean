import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Prod.Lex
import Mathlib.Order.WithBot
import Spec.Defs.Notation

/-!
# The objects, and the functions on blocks and on instants

This file declares the types of `Spec`, with the functions that take a value of one of them
apart, and then the functions of `Spec` that read a block, a tree of blocks, an instant or a
stamp, and no record of the node.

The types, in the namespace `Spec`:

- the numbers `Slot`, `Height`, `Round`; the root of a block `BlockId`, with its order, and the
  genesis block's root `genesisRoot`;
- the instants `Time`, the stamps `Stamp`, the occurrences `Occurrence`, the maps of stamps
  `TimestampMap`, and the genesis block's stamp `genesisStamp`;
- the height pair `HeightPair` and the finality pair `FinalityPair` of an attestation, the
  Goldfish vote `GoldfishVote V`, the attestation `Attestation V`, and the block `Block V`
  with the functions that read its parts (`Block.slot`, `Block.root`, `Block.parent?`,
  `Block.parent`, `Block.gf_votes`, `Block.gf_support_votes`, `Block.attestations`,
  `Block.proposer?`, `Block.depth`);
- the weights of the validators `Electorate V` and the committees `Committees V`;
- the object a node sends and receives, `NamedObject V`;
- a grade result `GradeResult V`, with its reader `GradeResult.block` (read under a test that
  the result is not pending) and its passage into the raising type (`let G ← result` raises when
  `result` is pending), a round's grades `RoundGrades V` and the saved grades `SavedGrades V`;

and, in the namespace `Spec.Protocol`: the chain state `ChainState V`, the strong-gadget
vote `SGVote V`, the token `Token Key` a grade counts, the phase of a grade result `Phase`, and
the inputs of the two duties that build a block and an attestation, `ProposalInput V` and
`AttestationInput V`.

The functions that read no record of the node:

- on blocks: the ancestry tests `Block.ancestorEq` (an ancestor of a block, or the block itself),
  `Block.ancestorStrict` (an ancestor of a block that is not the block), `Block.AncestorEq` (the
  proposition, with its decision procedure) and `Block.compatible` (one of two blocks is an
  ancestor of the other, or they are equal); the order `Block.deeper`, by which a block is deeper
  than another; the lookups `Block.find?` (the block of a tree with a given root), `blockWithRoot` (the
  same lookup, raising when two blocks of the tree share the root), `Block.isDeepestIn` and
  `Block.deepest?` (the deepest block of a tree); and `pickUnique?`, the unique member of a set
  that passes a test, which the lookups call;
- on instants: `occurrenceBefore`, whether an occurrence is strictly earlier than an instant;
  `beforeCutoff`, the members of a set stamped strictly before an instant; and
  `Protocol.latest_window`, the rounds a grade reads;
- on Goldfish votes: `Protocol.resolved`, whether the tree holds a vote's head block, of a slot at
  most the vote's, and `Protocol.resolution_time`, the later of the vote's stamp and that block's
  stamp;
- on a tree and a block: `Protocol.activePrefix`, the deepest block of the tree that is an
  ancestor of the block, or the block itself.

The routines of `Spec` write a relation between two blocks with dot notation on its first
block: `A.ancestorEq B`, `A.ancestorStrict B`, `A.compatible B`, `A.deeper B`. The lookups, which
take a set of blocks first, are called as functions: `Block.deepest? T`, `blockWithRoot T r`.

The file opens with a notation, active in `Spec` and the namespaces inside it: inside a
`do` block, an `if` whose condition mentions `none`, `⊥` or `pending` hands the fact of its
condition to its branches, so that an optional value is read as `x.value` under the test
`if x ≠ none then`, and a grade result as `result.block` under the test
`if result ≠ .pending then`.

A second notation follows it, active in the same namespaces: inside a `do` block, the assignment
arrow takes a path of fields, so that `st.saved_grades.current.g1 ← e` writes `e` into that one
field of `st` and leaves the others as they were.

A third notation follows, active in the same namespaces: `p <[lex] q` says that the pair `p` is
smaller than the pair `q` in lexicographic order, so that the first components are compared, and
the second ones only when the first are equal. `update_finality` compares two justifications with
it, as pairs of a height and a root.

This file holds definitions only.
-/

open scoped DC

open DC (DRE)

namespace Spec

/-! ## Notation: an `if` that tests absence (`none`, `⊥` or `pending`) -/

/-- `mentionsAbsence c`: whether the condition `c` of an `if`, as written, contains the
identifier `none`, the symbol `⊥`, or the identifier `pending` (written `.pending` or
`GradeResult.pending`). -/
def mentionsAbsence (c : Lean.Syntax) : Bool :=
  (c.find? (fun s => (s.isIdent && s.getId == `none) ||
    (s.isAtom && s.getAtomVal == "⊥") ||
    (s.isIdent && (s.getId == `pending || s.getId == `GradeResult.pending)))).isSome

/- Inside a `do` block, an `if` whose condition mentions `none`, `⊥` or `pending` makes the fact
of its condition available to its branches, as a written `if _ : … then` does. The read `x.value`
of an optional value `x` takes a proof of `x ≠ none` that is not written, and finds it among those
facts: so `if x ≠ none then … x.value …` is accepted, an `else` branch under `if x = none then`
reads `x.value` too, and `x.value` with no test before it is not accepted. A condition written
with `⊥` for `none` is treated the same way. The read `result.block` of a grade result `result`
takes, in the same way, a proof of `result ≠ .pending` that is not written, and finds it under
`if result ≠ .pending then`. An `if` whose condition mentions none of the three is left as Lean
has it. The notation is active in this namespace and the namespaces inside it. -/
scoped macro_rules
  | `(doElem| if $c:term then $t:doSeq) => do
      unless mentionsAbsence c do Lean.Macro.throwUnsupported
      `(doElem| if _h : $c then $t)
  | `(doElem| if $c:term then $t:doSeq else $e:doSeq) => do
      unless mentionsAbsence c do Lean.Macro.throwUnsupported
      `(doElem| if _h : $c then $t else $e)

/-! ## Notation: the assignment arrow on a path of fields -/

open Lean in
/-- Inside a `do` block, `x.f.g ← e`, with two fields or more after the variable `x`, writes the
value `e` into the field reached by the path `f.g` of `x`, and leaves every other field of `x` as
it was: it stands for `x := { x with f.g := e }`. So `st.saved_grades.current.g1 ← e` writes
`e` into the grade-1 result of the current round's grades of the store `st`. An arrow with one
field after the variable, `x.f ← e`, is left to the assignment arrow of the notation in `Spec.Defs.Notation`, which
writes that one field. The notation is active in this namespace and the namespaces inside it. -/
scoped macro_rules
  | `(doElem| $x:ident ← $e) => do
      let comps := x.getId.components
      if comps.length < 3 then Macro.throwUnsupported
      let v := mkIdent comps.head!
      let path := mkIdent (comps.tail!.foldl (fun acc c => acc ++ c) Name.anonymous)
      `(doElem| $v:ident := { $v with $path:ident := $e })

/-! ## Notation: the lexicographic comparison of two pairs -/

/-- `p <[lex] q`: the pair `p` is smaller than the pair `q` in lexicographic order: the first
components are compared, and the second ones only when the first are equal. -/
scoped notation:50 p:51 " <[lex] " q:51 => toLex p < toLex q

/-! ## Slots, heights, rounds and roots -/

/-- A slot number. The genesis block has slot `0`. -/
abbrev Slot := Nat

/-- A height: the counter of the finality gadget, separate from the slot. A chain state is at one
height at a time and moves to the next one at a height event. -/
abbrev Height := Nat

/-- A round number. Round `r` is the slots `r * R` to `r * R + R − 1`, for the round length `R` of
the parameters. -/
abbrev Round := Nat

/-- The root of a block: the value that names the block. Roots are compared by a fixed order, the
order of their values. -/
structure BlockId where
  /-- The number the root is. Only its equality with another root and its order are read. -/
  value : Nat
deriving DecidableEq, Repr

/-- The fixed order on roots: the order of their values. It decides between two blocks of the same
depth (`Block.deeper`), and between two justified blocks of the same height. -/
instance : LinearOrder BlockId :=
  LinearOrder.lift' BlockId.value (fun _ _ equal => congrArg BlockId.mk equal)

/-- The root of the genesis block: `0`, the least root. -/
def genesisRoot : BlockId := ⟨0⟩

/-! ## Instants and stamps -/

/-- An instant: the node's time, an integer. -/
abbrev Time := Int

/-- A stamp: an instant, or `⊥`, earlier than every instant. `⊥` is the genesis block's stamp. -/
abbrev Stamp := WithBot Time

/-- An occurrence: the stamp at which something happens, or `none` when it never happens. `none`
is later than every instant, and `some ⊥` earlier than every instant. It is the type of the values
of a map of stamps (`TimestampMap`). -/
abbrev Occurrence := Option Stamp

/-- The genesis block's stamp, `⊥`. -/
def genesisStamp : Stamp := ⊥

/-- A map of stamps: for each object of type `α`, the stamp at which the store admitted it, or
`none` when the store has not admitted it. -/
abbrev TimestampMap (α : Type) := α → Option Stamp

/-! ## Height pairs, finality pairs, Goldfish votes, attestations and blocks -/

/-- The height pair of an attestation: the empty pair, or a vote at the height `height` for the
block whose root is `entry`. The vote is a target vote for that block when `timeout` is `false`,
and a timeout vote (the empty-target vote) at the height when `timeout` is `true`. A timeout vote
names no target; the block `entry` it names is the block it was cast on. -/
inductive HeightPair where
  /-- The empty pair: no height and no block. -/
  | empty
  /-- The vote at the height `height` for the block whose root is `entry`: a timeout vote, cast on
  that block, when `timeout` is `true`, and a target vote for that block otherwise. -/
  | vote (height : Height) (entry : BlockId) (timeout : Bool)
  deriving DecidableEq, Repr

/-- The finality pair of an attestation: a justification height and the root of the justified
block. An attestation with no finality pair holds `none` in its place. -/
structure FinalityPair where
  /-- The justification height. -/
  height : Height
  /-- The root of the justified block. -/
  target : BlockId
deriving DecidableEq, Repr

/-- A Goldfish vote: the validator `val_index` votes, at the slot `slot`, for the block whose root
is `head`. -/
structure GoldfishVote (V : Type) where
  /-- The validator that sends the vote. -/
  val_index : V
  /-- The slot of the vote. -/
  slot : Slot
  /-- The root of the block the vote is for. -/
  head : BlockId
deriving DecidableEq, Repr

/-- An attestation: the vote of the validator `val_index` at the round `round`, made of the block
it confirms, its height pair and its finality pair. -/
structure Attestation (V : Type) where
  /-- The validator that sends the attestation. -/
  val_index : V
  /-- The round of the attestation. -/
  round : Round
  /-- The root of the block the attestation confirms, or `none` when it confirms none. -/
  confirmed : Option BlockId
  /-- The height pair of the attestation. -/
  height_pair : HeightPair
  /-- The finality pair of the attestation, or `none` when it has none. -/
  finality_pair : Option FinalityPair
  deriving DecidableEq, Repr

/-- A block: the genesis block, or a block that holds its parent. The Goldfish votes and the
attestations a block includes name blocks by their roots. -/
inductive Block (V : Type) where
  /-- The genesis block. Its slot is `0`, its root is `genesisRoot`, and it has no parent. -/
  | genesis
  /-- The block with parent `parent`, slot `slot` and root `root`, which includes the Goldfish
  votes `gf_votes` and the attestations `attestations`, and whose proposer is the validator
  `proposer`. `gf_support_votes` is the list of the Goldfish votes of `gf_votes` that were resolved
  in the proposer's view when it proposed the block. -/
  | node (parent : Block V) (slot : Slot) (root : BlockId)
      (gf_votes : List (GoldfishVote V))
      (gf_support_votes : List (GoldfishVote V))
      (attestations : List (Attestation V))
      (proposer : V)
deriving DecidableEq, Repr

variable {V : Type} [DecidableEq V] [Fintype V]

namespace Block

/-- `B.slot`: the slot of the block `B`; `0` for the genesis block. -/
def slot : Block V → Slot
  | .genesis => 0
  | .node _ s _ _ _ _ _ => s

/-- `B.root`: the root of the block `B`; `genesisRoot` for the genesis block. -/
def root : Block V → BlockId
  | .genesis => genesisRoot
  | .node _ _ r _ _ _ _ => r

/-- `B.parent?`: the parent of the block `B`, or `none` for the genesis block. -/
def parent? : Block V → Option (Block V)
  | .genesis => none
  | .node p _ _ _ _ _ _ => p

/-- `B.parent`: the parent of the block `B`; the genesis block is its own parent. -/
def parent : Block V → Block V
  | .genesis => .genesis
  | .node p _ _ _ _ _ _ => p

/-- `B.gf_votes`: the Goldfish votes the block `B` includes; none for the genesis block. -/
def gf_votes : Block V → List (GoldfishVote V)
  | .genesis => []
  | .node _ _ _ votes _ _ _ => votes

/-- `B.gf_support_votes`: the Goldfish votes of `B.gf_votes` that were resolved in the proposer's
view when it proposed the block `B`; none for the genesis block. -/
def gf_support_votes : Block V → List (GoldfishVote V)
  | .genesis => []
  | .node _ _ _ _ support _ _ => support

/-- `B.attestations`: the attestations the block `B` includes; none for the genesis block. -/
def attestations : Block V → List (Attestation V)
  | .genesis => []
  | .node _ _ _ _ _ ats _ => ats

/-- `B.proposer?`: the validator that proposed the block `B`, or `none` for the genesis block. -/
def proposer? : Block V → Option V
  | .genesis => none
  | .node _ _ _ _ _ _ i => i

/-- `B.depth`: the number of parent edges from the block `B` to the genesis block. -/
def depth : Block V → Nat
  | .genesis => 0
  | .node p _ _ _ _ _ _ => p.depth + 1

end Block

/-! ## Weights and committees -/

/-- The weights of the validators: a fixed positive weight for each validator. -/
structure Electorate (V : Type) [Fintype V] where
  /-- `weight v`: the weight of the validator `v`. -/
  weight : V → Nat
  /-- Every weight is positive. -/
  weight_pos : ∀ i, 0 < weight i

/-- The committees: a set of validators for each slot. -/
structure Committees (V : Type) where
  /-- `members s`: the committee of the slot `s`. -/
  members : Slot → Finset V

/-! ## The objects a node sends and receives -/

/-- An object a node sends and receives: a block, a Goldfish vote, or an attestation. -/
inductive NamedObject (V : Type) where
  /-- The block `B`. -/
  | block (B : Block V)
  /-- The Goldfish vote `vote`. -/
  | gfVote (vote : GoldfishVote V)
  /-- An attestation. -/
  | attest (row : Attestation V)
  deriving DecidableEq, Repr

/-! ## A round's grades and the saved grades -/

/-- A grade result: not computed yet (`pending`), or computed (`computed G`), where `G` is the
block the computation returned, or `none` when no block passed. -/
inductive GradeResult (V : Type) where
  /-- The result is not computed yet. -/
  | pending
  /-- The result is computed: `G` is the block the computation returned, or `none` when no block
  passed. -/
  | computed (G : Option (Block V))
  deriving DecidableEq, Repr

/-- `result.block`: the block of the computed result `result`, or `none` when it was computed
with no block. It takes a proof, not written at the call, that `result` is not pending; Lean
finds it among the facts of the enclosing `if result ≠ .pending then`. A read with no such test
before it is refused. -/
def GradeResult.block (result : GradeResult V)
    (h : result ≠ .pending := by solve_by_elim [And.left, And.right]) : Option (Block V) :=
  match result, h with
  | .computed G, _ => G
  | .pending, h => absurd rfl h

/-- A grade result used where a routine that can raise expects a computation stands for "its
block, or raise when it is pending": `let G ← result` gives the block of a computed result (or
`none` when it was computed with no block) and raises when `result` is pending. -/
scoped instance : Coe (GradeResult V) (DRE (Option (Block V))) :=
  ⟨fun result => match result with
    | .pending => throw .error
    | .computed G => pure G⟩

/-- A round's grades: the three grade results `g0`, `g1`, `g2` of one round, each a
`GradeResult V`. -/
structure RoundGrades (V : Type) where
  /-- The grade-0 result. -/
  g0 : GradeResult V
  /-- The grade-1 result. -/
  g1 : GradeResult V
  /-- The grade-2 result. -/
  g2 : GradeResult V

/-- The saved grades: a round `round`, that round's grades `current`, and the next round's grades
`next`, each a `RoundGrades V`. `update_grades` writes a result at the instant it completes; a
result that was missed is never computed later. -/
structure SavedGrades (V : Type) where
  /-- The round the saved grades are aligned to. -/
  round : Round
  /-- The grades of the round `round`. -/
  current : RoundGrades V
  /-- The grades of the round after `round`. -/
  next : RoundGrades V

namespace Protocol

/-! ## The chain state -/

/-- A chain state: what the chain of blocks that ends at the block `L` has decided about heights,
justification and finality. -/
structure ChainState (V : Type) where
  /-- The latest block of the chain. -/
  L : Block V
  /-- The slot of `L`. -/
  s : Slot
  /-- The current height. -/
  h : Height
  /-- The block that took the chain state into the height `h`. -/
  T_h : Block V
  /-- Whether the height `h` is nonjustifiable; computed when the chain state enters `h`, and
  unchanged until it leaves `h`. -/
  nj : Bool
  /-- The validators whose target vote for the block `T_h` at the height `h` the chain state has
  counted. -/
  target_participation : Finset V
  /-- The validators whose target vote or timeout vote at the height `h` the chain state has
  counted. -/
  progress : Finset V
  /-- The validators whose finality pair for the justified block `J` at the height `h_j` the chain
  state has counted. -/
  finalize : Finset V
  /-- The latest justified block of the chain. -/
  J : Block V
  /-- The height of `J`'s justification. -/
  h_j : Height
  /-- The latest finalized block of the chain. -/
  F : Block V
  /-- The height of `F`'s finalization. -/
  h_F : Height
deriving DecidableEq

/-! ## Strong-gadget votes, tokens and phases -/

/-- A strong-gadget vote: the vote of the validator `val_index` at the round `round` for the block
whose root is `confirmed`, or for no block. -/
structure SGVote (V : Type) where
  /-- The validator that sends the vote. -/
  val_index : V
  /-- The round of the vote. -/
  round : Round
  /-- The root of the block the vote confirms, or `none`. -/
  confirmed : Option BlockId
deriving DecidableEq, Repr

/-- A token: a round `round` and a key `key`. A grade reads the tokens of the strong-gadget votes,
each the vote's round and the root it confirms (`token`). -/
structure Token (Key : Type*) where
  /-- The round of the token. -/
  round : Nat
  /-- The key of the token. -/
  key : Key
deriving DecidableEq

/-- The phase of a grade result. -/
inductive Phase where
  /-- The grade-0 result. -/
  | g0
  /-- The grade-1 result. -/
  | g1
  /-- The grade-2 result. -/
  | g2
  deriving DecidableEq

/-! ## The inputs of the duties that build a block and an attestation -/

/-- What the proposal duty reads off the store: the parent `parent`, the slot `slot` and the root
`root` of the new block, the Goldfish votes `gf_votes` it includes and those of them
`gf_support_votes` resolved in the proposer's view, and the proposer `proposer`. -/
structure ProposalInput (V : Type) where
  /-- The parent of the new block. -/
  parent : Block V
  /-- The slot of the new block. -/
  slot : Slot
  /-- The root of the new block. -/
  root : BlockId
  /-- The Goldfish votes the new block includes. -/
  gf_votes : List (GoldfishVote V)
  /-- The Goldfish votes of `gf_votes` resolved in the proposer's view. -/
  gf_support_votes : List (GoldfishVote V)
  /-- The proposer of the new block. -/
  proposer : V

/-- What the attestation duty reads off the store: the validator `val_index`, the round `round`,
the root `confirmed` of the confirmed block, the triple `fields` of a chain state's height, the
root of its target at that height and its flag saying the height is not justifiable (or `none`),
and the justification height `h_j`, the root `J` of the justified block and the finalization
height `h_F` of the head's chain state. -/
structure AttestationInput (V : Type) where
  /-- The validator that sends the attestation. -/
  val_index : V
  /-- The round of the attestation. -/
  round : Round
  /-- The root of the block the attestation confirms, or `none`. -/
  confirmed : Option BlockId
  /-- The height, the root of the target at that height, and the flag saying the height is not
  justifiable, of the chain state the height pair is built from; or `none`. The flag is the chain
  state's `nj`, not a timeout vote. -/
  fields : Option (Height × BlockId × Bool)
  /-- The justification height of the head's chain state. -/
  h_j : Height
  /-- The root of the justified block of the head's chain state. -/
  J : BlockId
  /-- The finalization height of the head's chain state. -/
  h_F : Height

end Protocol

/-! ## Ancestry and the deeper order -/

namespace Block

/-- `Block.ancestorEq B C`, written `B.ancestorEq C`: whether `B` is an ancestor of `C`, or `C`
itself. Computed by walking from `C` to its parent until the genesis block. -/
def ancestorEq (B : Block V) : Block V → Bool
  | .genesis => B = .genesis
  | C@(.node p _ _ _ _ _ _) => (B = C) || B.ancestorEq p

/-- `Block.ancestorStrict B C`, written `B.ancestorStrict C`: whether `B` is an ancestor of `C`
and is not `C`. -/
def ancestorStrict (B C : Block V) : Bool :=
  !(B = C) && B.ancestorEq C

/-- `Block.AncestorEq B C`, written `B.AncestorEq C`: the proposition that `B` is an ancestor of
`C`, or `C` itself (`B.ancestorEq C` is `true`). -/
def AncestorEq (B C : Block V) : Prop :=
  B.ancestorEq C = true

/-- `B.AncestorEq C` is decided by computing `B.ancestorEq C`. -/
instance (B C : Block V) : Decidable (B.AncestorEq C) :=
  inferInstanceAs (Decidable (B.ancestorEq C = true))

/-- `Block.compatible B C`, written `B.compatible C`: whether one of `B` and `C` is an ancestor of
the other, or they are equal. -/
def compatible (B C : Block V) : Bool :=
  B.ancestorEq C || C.ancestorEq B

/-- `Block.deeper B C`, written `B.deeper C`: whether `B` is deeper than `C`: `B` has the greater
depth (number of parent edges to the genesis block), or the two have the same depth and `B` has
the greater root. -/
def deeper (B C : Block V) : Bool :=
  (C.depth < B.depth) ||
    ((C.depth = B.depth) && (C.root < B.root))

end Block

/-! ## The unique member of a set that passes a test -/

section Pick

variable {α : Type} [DecidableEq α]

/-- Whether exactly one member of `T` satisfies `p` is decided by deciding whether some member
`a` of `T` satisfies `p` and every member of `T` that satisfies `p` is `a`. -/
instance decidableExistsUniqueMem (T : Finset α) (p : α → Prop)
    [DecidablePred p] : Decidable (∃! a, a ∈ T ∧ p a) :=
  decidable_of_iff (∃ a ∈ T, p a ∧ ∀ b ∈ T, p b → b = a) <| by
    constructor
    · rintro ⟨a, haT, hpa, huniq⟩
      exact ⟨a, ⟨haT, hpa⟩, fun b hb => huniq b hb.1 hb.2⟩
    · rintro ⟨a, ⟨haT, hpa⟩, huniq⟩
      exact ⟨a, haT, hpa, fun b hbT hpb => huniq b ⟨hbT, hpb⟩⟩

/-- `pickUnique? T p`: the one member of `T` for which `p` is `true`, or `none` when there is no
such member or more than one. -/
def pickUnique? (T : Finset α) (p : α → Bool) : Option α :=
  if h : ∃! a, a ∈ T ∧ p a = true then
    some (T.choose (fun a => p a = true) h)
  else
    none

end Pick

/-! ## Lookup by root and the deepest block -/

namespace Block

/-- `Block.find? T r`: the block of the tree `T` whose root is `r`, or `none` when `T` holds no
such block or more than one. -/
def find? (T : Finset (Block V)) (r : BlockId) : Option (Block V) :=
  pickUnique? T (fun B => B.root = r)

/-- `Block.isDeepestIn T B`: whether no block of `T` is deeper than `B` (`Block.deeper`). -/
def isDeepestIn (T : Finset (Block V)) (B : Block V) : Bool :=
  ∀ C ∈ T, C.deeper B = false

/-- `Block.deepest? T`: the deepest block of the tree `T`, the one of greatest depth and, among
those, of greatest root; `none` when `T` is empty, or when two blocks of `T` have both the
greatest depth and the same greatest root. -/
def deepest? (T : Finset (Block V)) : Option (Block V) :=
  pickUnique? T (isDeepestIn T)

end Block

/-- `blockWithRoot T r`: the block of the tree `T` whose root is `r`, or `none` when `T` holds no
such block.

Raises when two blocks of `T` have the root `r`: roots name blocks uniquely. -/
def blockWithRoot (T : Finset (Block V)) (r : BlockId) : DRE (Option (Block V)) := do
  if 2 ≤ |{B ∈ T | B.root = r}| then
    throw .error
  return Block.find? T r

/-! ## Instants -/

/-- `occurrenceBefore x Γ`: whether the occurrence `x` is strictly earlier than the instant `Γ`.
An occurrence that never happens (`x = none`) is not; the genesis block's stamp `⊥` is earlier
than every instant. -/
def occurrenceBefore (x : Occurrence) (Γ : Time) : Bool := Id.run do
  if x ≠ none then
    return x.value < (Γ : Stamp)
  return false

/-- `beforeCutoff ts Γ S`: the members of `S` whose stamp in the map `ts` is strictly before the
instant `Γ`.

Raises when a member of `S` has no stamp: every member of the sets this function is applied to
was stamped when it entered the set. -/
def beforeCutoff {α : Type} [DecidableEq α] (ts : TimestampMap α) (Γ : Time) (S : Finset α) :
    DRE (Finset α) :=
  S.filterM fun x => do
    let t_x ← ts x
    return t_x < (Γ : Stamp)

namespace Protocol

/-- `latest_window η_SG r`: the rounds from `r − η_SG` (or `0`, when `η_SG > r`) up to `r − 1`, in
ascending order; empty when `r = 0`. -/
def latest_window (η_SG : Round) (r : Round) : List Round :=
  List.range' (r - η_SG) (min r η_SG)

/-! ## The resolution of a Goldfish vote -/

/-- `Protocol.resolved T vote`: whether the Goldfish vote `vote` is resolved in the block tree
`T`: `T` holds a block `B` whose root is the vote's head root `vote.head`, and `B`'s slot is at
most the vote's slot. A vote whose head `T` does not hold is not resolved.

Raises when two blocks of `T` have the root `vote.head`: roots name blocks uniquely. -/
def resolved (T : Finset (Block V)) (vote : GoldfishVote V) : DRE Bool := do
  let B? ← blockWithRoot T vote.head
  if B? ≠ none then
    return B?.value.slot ≤ vote.slot
  return false

/-- `Protocol.resolution_time T tb tv vote`: the resolution time of the Goldfish vote `vote`, given
the block tree `T`, the block stamps `tb` and the vote stamps `tv`:

1. if `T` holds a block `H` whose root is `vote.head`, and `H`'s slot is at most `vote.slot`,
   the later of the vote's stamp `tv vote` and the block's stamp `tb H`;
2. otherwise `none` (the vote never resolves).

Raises when two blocks of `T` have the root `vote.head` (roots name blocks uniquely), when the
block `H` has no stamp (every block of the tree was stamped when it entered it), and when the
vote has no stamp (the function is read on the votes a store holds, each stamped when it was
admitted). -/
def resolution_time (T : Finset (Block V)) (tb : TimestampMap (Block V))
    (tv : TimestampMap (GoldfishVote V)) (vote : GoldfishVote V) : DRE Occurrence := do
  let H? ← blockWithRoot T vote.head
  if H? ≠ none then
    let H := H?.value
    if H.slot ≤ vote.slot then
      let t_vote ← tv vote
      let t_H ← tb H
      return some (max t_vote t_H)
  return none

/-! ## The active prefix of a block -/

/-- `Protocol.activePrefix tree root`: the deepest block of the tree `tree` that is an ancestor
of the block `root`, or `root` itself (`Block.deepest?`); `none` when `tree` holds no such block. -/
def activePrefix (tree : Finset (Block V)) (root : Block V) : Option (Block V) :=
  Block.deepest? {B ∈ tree | B.ancestorEq root}

end Protocol

end Spec
