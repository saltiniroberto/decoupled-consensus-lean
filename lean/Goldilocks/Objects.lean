module
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Prod.Lex
public import Mathlib.Order.WithBot
public import Spec2.Defs.Notation
public import Spec2.Defs.Raise

@[expose] public section

/-!
# The objects, and the functions on blocks and on times

Goldilocks composes an available chain, written AC, with a finality gadget, written FG. This file
declares the types both of them read, with the functions that take a value of one of them apart,
and then the functions that read a block, a tree of blocks, a time or a stamp, and no state of a
node. Everything is in the namespace `Goldilocks`.

The notations, active in `Goldilocks` and the namespaces inside it:

- inside a `do` block, an `if` whose condition mentions `none` or `⊥` hands the fact of its
  condition to its branches, so that an optional value is read as `x.value` under the test
  `if x ≠ none then`;
- inside a `do` block, the assignment arrow takes a path of fields, so that `st.a.b ← e` writes
  `e` into that one field of `st` and leaves the others as they were;
- `p <[lex] q`: the pair `p` is smaller than the pair `q` in lexicographic order;
- `funGetElem`: a function is read with brackets, `f[a]` for `f a`.

The types:

- the numbers `Slot`, `Height`, `Round`; the root of a block `BlockId`, with its order, and the
  genesis block's root `genesisRoot`; the class `RootOrder`, the fixed order that decides
  between two blocks of the same depth;
- the times `Time`, the stamps `Stamp`, the occurrences `Occurrence`, the maps of stamps
  `TimestampMap`, and the genesis block's stamp `genesisStamp`;
- the Goldfish vote `GoldfishVote V`, the finality pair `FinalityPair`, the height pair
  `HeightPair`, the attestation `Attestation V` with its content `AttestationContent` and the
  reader `Attestation.content`, and the block `Block V` with the functions that read its parts
  (`Block.slot`, `Block.root`, `Block.parent?`, `Block.parent`, `Block.votes`,
  `Block.support_votes`, `Block.attestations`, `Block.proposer?`, `Block.depth`);
- the frame `Frame V`, what the FG gives the AC;
- the object a node sends and receives, `NamedObject V`.

The functions that read no state of a node:

- on blocks: the ancestry tests `Block.ancestorEq`, `Block.ancestorStrict`, `Block.AncestorEq`
  (the proposition, with its decision procedure), `Block.compatible` and `Block.conflicts`; the
  order `Block.deeper`; the lookups `Block.find?`, `blockWithRoot`, `Block.isDeepestIn` and
  `Block.deepest?`; and `pickUnique?`, the unique member of a set that passes a test, with the
  decision procedure `decidableExistsUniqueMem` it reads;
- on times: `occurrenceBefore` and `beforeCutoff`;
- on Goldfish votes: `resolved` and `resolution_time`;
- on the validators: `validator_count V`, their number, and `quorum V`, two thirds of it rounded
  up. The weight of a set of validators `S` is its size `|S|`.

This file holds definitions only.
-/

open scoped DC

open DC (DRE)

namespace Goldilocks

/-! ## Notation: an `if` that tests absence (`none` or `⊥`) -/

/-- `mentionsAbsence c`: whether the condition `c` of an `if`, as written, contains the
identifier `none` or the symbol `⊥`. -/
meta def mentionsAbsence (c : Lean.Syntax) : Bool :=
  (c.find? (fun s => (s.isIdent && s.getId == `none) ||
    (s.isAtom && s.getAtomVal == "⊥"))).isSome

/- Inside a `do` block, an `if` whose condition mentions `none` or `⊥` makes the fact of its
condition available to its branches, as a written `if _ : … then` does. The read `x.value` of an
optional value `x` takes a proof of `x ≠ none` that is not written, and finds it among those
facts: so `if x ≠ none then … x.value …` is accepted, an `else` branch under `if x = none then`
reads `x.value` too, and `x.value` with no test before it is not accepted. A condition written
with `⊥` for `none` is treated the same way. An `if` whose condition mentions neither is left as
Lean has it. The notation is active in this namespace and the namespaces inside it. -/
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
it was: it stands for `x := { x with f.g := e }`. An arrow with one field after the variable,
`x.f ← e`, is left to the assignment arrow of `Spec2`'s notation, which writes that one field.
The notation is active in this namespace and the namespaces inside it. -/
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

/-! ## Notation: brackets on a function -/

/-- A total map read by application, written with the protocol's brackets: `f[a]` is `f a`.
Scoped to `Goldilocks`, so it is active only inside that namespace and the namespaces under
it. -/
scoped instance funGetElem {α β : Type} : GetElem (α → β) α β (fun _ _ => True) where
  getElem f a _ := f a

/-! ## Slots, heights, rounds and roots -/

/-- A slot number. The genesis block has slot `0`. -/
abbrev Slot := Nat

/-- A height: the counter of the finality gadget, separate from the slot. -/
abbrev Height := Nat

/-- A round number. Round `r` is the slots `r * R` to `r * R + R − 1`, for the round length `R` of
the parameters. -/
abbrev Round := Nat

/-- The root of a block: the value that names the block. -/
structure BlockId where
  /-- The number the root is. Only its equality with another root and its order are read. -/
  value : Nat
deriving DecidableEq, Repr

/-- The order on roots by their values. -/
instance : LinearOrder BlockId :=
  LinearOrder.lift' BlockId.value (fun _ _ equal => congrArg BlockId.mk equal)

/-- The root of the genesis block: `0`, the least root. -/
def genesisRoot : BlockId := ⟨0⟩

/-- The fixed order on roots that decides between two blocks of the same depth. -/
class RootOrder where
  /-- `before r r'`: whether the root `r` comes before the root `r'`. -/
  before : (r : BlockId) → (r' : BlockId) → Bool
  /-- No root comes before itself. -/
  irrefl : ∀ r : BlockId, before r r = false
  /-- A root that comes before a second one comes before every root the second comes before. -/
  trans : ∀ r r' r'' : BlockId, before r r' = true → before r' r'' = true → before r r'' = true
  /-- Of two different roots, one comes before the other. -/
  total : ∀ r r' : BlockId, r ≠ r' → before r r' = true ∨ before r' r = true

/-! ## Times and stamps -/

/-- A time: the node's clock, an integer. -/
abbrev Time := Int

/-- A stamp: a time, or `⊥`, earlier than every time. `⊥` is the genesis block's stamp. -/
abbrev Stamp := WithBot Time

/-- An occurrence: the stamp at which something happens, or `none` when it never happens. `none`
is later than every time, and `some ⊥` earlier than every time. It is the type of the values of a
map of stamps (`TimestampMap`). -/
abbrev Occurrence := Option Stamp

/-- The genesis block's stamp, `⊥`. -/
def genesisStamp : Stamp := ⊥

/-- A map of stamps: for each object of type `α`, the stamp at which the node admitted it, or
`none` when the node has not admitted it. -/
abbrev TimestampMap (α : Type) := α → Option Stamp

/-! ## Goldfish votes, finality pairs, height pairs, attestations and blocks -/

/-- A Goldfish vote: the validator `val_index` votes, at the slot `slot`, for the block whose root
is `head`. The vote names its head by root. -/
structure GoldfishVote (V : Type) where
  /-- The validator that sends the vote. -/
  val_index : V
  /-- The slot of the vote. -/
  slot : Slot
  /-- The root of the block the vote is for. -/
  head : BlockId
deriving DecidableEq, Repr

/-- A finality pair: a justification height and the root of the justified block. -/
structure FinalityPair where
  /-- The justification height. -/
  hf : Height
  /-- The root of the justified block. -/
  Tf : BlockId
deriving DecidableEq, Repr

/-- A height pair as a validator computes it before it attests: the empty pair, when it has no
vote to cast, or a vote at the height `height` for the block whose root is `entry`. The vote is a
target vote for that block when `timeout` is `false`, and a timeout at the height when `timeout`
is `true`. An attestation carries only a vote, in its fields `h`, `T` and `τ`. -/
inductive HeightPair where
  /-- The empty pair: no height and no block. -/
  | empty
  /-- The vote at the height `height` for the block whose root is `entry`: a timeout when
  `timeout` is `true`, and a target vote for that block otherwise. -/
  | vote (height : Height) (entry : BlockId) (timeout : Bool)
  deriving DecidableEq, Repr

/-- An attestation: a vote of the validator `val_index` at a height, with its finality pair. -/
structure Attestation (V : Type) where
  /-- The validator that sends the attestation. -/
  val_index : V
  /-- The height of the vote. -/
  h : Height
  /-- The root of the block the vote names: the block that took the validator's chain into the
  height `h`. -/
  T : BlockId
  /-- `false` for a target vote for the block `T`, `true` for a timeout at the height `h`. -/
  τ : Bool
  /-- The finality pair of the attestation, or `none` when it has none. -/
  finality_pair : Option FinalityPair
  deriving DecidableEq, Repr

/-- The content of an attestation: the attestation without the validator that sends it. -/
structure AttestationContent where
  /-- The height of the vote. -/
  h : Height
  /-- The root of the block the vote names. -/
  T : BlockId
  /-- `false` for a target vote for the block `T`, `true` for a timeout at the height `h`. -/
  τ : Bool
  /-- The finality pair, or `none` when there is none. -/
  finality_pair : Option FinalityPair
  deriving DecidableEq, Repr

/-- `a.content`: the content of the attestation `a`, its fields but the validator. -/
def Attestation.content {V : Type} (a : Attestation V) : AttestationContent :=
  AttestationContent.mk (h := a.h) (T := a.T) (τ := a.τ) (finality_pair := a.finality_pair)

/-- A block: the genesis block, or a block that holds its parent. The Goldfish votes and the
attestations a block includes name blocks by their roots. -/
inductive Block (V : Type) where
  /-- The genesis block. Its slot is `0`, its root is `genesisRoot`, and it has no parent. -/
  | genesis
  /-- The block with parent `parent`, slot `slot` and root `root`, which includes the Goldfish
  votes `votes` and the attestations `attestations`, and whose proposer is the validator
  `proposer`. `support_votes` is the list of the Goldfish votes of `votes` that were resolved in
  the proposer's view when it proposed the block. -/
  | node (parent : Block V) (slot : Slot) (root : BlockId)
      (votes : List (GoldfishVote V))
      (support_votes : List (GoldfishVote V))
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

/-- `B.votes`: the Goldfish votes the block `B` includes; none for the genesis block. -/
def votes : Block V → List (GoldfishVote V)
  | .genesis => []
  | .node _ _ _ votes _ _ _ => votes

/-- `B.support_votes`: the Goldfish votes of `B.votes` that were resolved in the proposer's view
when it proposed the block `B`; none for the genesis block. -/
def support_votes : Block V → List (GoldfishVote V)
  | .genesis => []
  | .node _ _ _ _ support _ _ => support

/-- `B.attestations`: the attestations the block `B` includes; none for the genesis block. -/
def attestations : Block V → List (Attestation V)
  | .genesis => []
  | .node _ _ _ _ _ ats _ => ats

/-- `B.proposer?`: the validator that proposed the block `B`, or `none` for the genesis block. -/
def proposer? : Block V → Option V
  | .genesis => none
  | .node _ _ _ _ _ _ v => v

/-- `B.depth`: the number of parent edges from the block `B` to the genesis block. -/
def depth : Block V → Nat
  | .genesis => 0
  | .node p _ _ _ _ _ _ => p.depth + 1

end Block

/-! ## The frame -/

/-- The frame: what the finality gadget gives the available chain. -/
structure Frame (V : Type) where
  /-- The blocks the finality gadget has accepted that are `F` or a descendant of `F`. -/
  tree : Finset (Block V)
  /-- A block of `tree`: the root of the fork choice. -/
  fc_root : Block V
  /-- Blocks of `tree` that are `fc_root` or a descendant of it: the blocks at which a walk for a
  head may stop. -/
  viable_heads : Finset (Block V)
  /-- The root of `tree`: the finalized block of the finality gadget. -/
  F : Block V

/-! ## The objects a node sends and receives -/

/-- An object a node sends and receives: a block, a Goldfish vote, or an attestation. -/
inductive NamedObject (V : Type) where
  /-- The block `B`. -/
  | block (B : Block V)
  /-- The Goldfish vote `vote`. -/
  | gfVote (vote : GoldfishVote V)
  /-- The attestation `a`. -/
  | attest (a : Attestation V)
  deriving DecidableEq, Repr

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

/-- `Block.conflicts B C`, written `B.conflicts C`: whether `B` and `C` are not compatible:
neither is an ancestor of the other, and they are not equal. -/
def conflicts (B C : Block V) : Bool :=
  !B.compatible C

/-- `Block.deeper B C`, written `B.deeper C`: whether `B` is deeper than `C`: `B` has the greater
depth (number of parent edges to the genesis block), or the two have the same depth and the root
of `C` comes before the root of `B` in the root order (`RootOrder.before`). -/
def deeper [RootOrder] (B C : Block V) : Bool :=
  (C.depth < B.depth) ||
    ((C.depth = B.depth) && (RootOrder.before C.root B.root))

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
def isDeepestIn [RootOrder] (T : Finset (Block V)) (B : Block V) : Bool :=
  ∀ C ∈ T, C.deeper B = false

/-- `Block.deepest? T`: the deepest block of the tree `T`: the one of greatest depth and, among
those, the one whose root every other such root comes before in the root order
(`RootOrder.before`); `none` when `T` is empty, or when two blocks of `T` have both the greatest
depth and the same root. -/
def deepest? [RootOrder] (T : Finset (Block V)) : Option (Block V) :=
  pickUnique? T (isDeepestIn T)

end Block

/-- `blockWithRoot T r`: the block of the tree `T` whose root is `r`, or `none` when `T` holds no
such block.

Raises when two blocks of `T` have the root `r`: roots name blocks uniquely. -/
def blockWithRoot (T : Finset (Block V)) (r : BlockId) : DRE (Option (Block V)) := do
  if 2 ≤ |{B ∈ T | B.root = r}| then
    throw .error
  return Block.find? T r

/-! ## Times -/

/-- `occurrenceBefore x t`: whether the occurrence `x` is strictly earlier than the time `t`.
An occurrence that never happens (`x = none`) is not; the genesis block's stamp `⊥` is earlier
than every time. -/
def occurrenceBefore (x : Occurrence) (t : Time) : Bool := Id.run do
  if x ≠ none then
    return x.value < (t : Stamp)
  return false

/-- `beforeCutoff ts t S`: the members of `S` whose stamp in the map `ts` is strictly before the
time `t`.

Raises when a member of `S` has no stamp: every member of the sets this function is applied to
was stamped when it entered the set. -/
def beforeCutoff {α : Type} [DecidableEq α] (ts : TimestampMap α) (t : Time) (S : Finset α) :
    DRE (Finset α) :=
  S.filterM fun x => do
    let t_x ← ts x
    return t_x < (t : Stamp)

/-! ## The resolution of a Goldfish vote -/

/-- `resolved T vote`: whether the Goldfish vote `vote` is resolved in the block tree `T`: `T`
holds a block `B` whose root is the vote's head root `vote.head`, and `B`'s slot is at most the
vote's slot. A vote whose head `T` does not hold is not resolved.

Raises when two blocks of `T` have the root `vote.head`: roots name blocks uniquely. -/
def resolved (T : Finset (Block V)) (vote : GoldfishVote V) : DRE Bool := do
  let B? ← blockWithRoot T vote.head
  if B? ≠ none then
    return B?.value.slot ≤ vote.slot
  return false

/-- `resolution_time T tb tv vote`: the resolution time of the Goldfish vote `vote`, given the
block tree `T`, the block stamps `tb` and the vote stamps `tv`:

1. if `T` holds a block `H` whose root is `vote.head`, and `H`'s slot is at most `vote.slot`,
   the later of the vote's stamp `tv vote` and the block's stamp `tb H`;
2. otherwise `none` (the vote never resolves).

Raises when two blocks of `T` have the root `vote.head` (roots name blocks uniquely), when the
block `H` has no stamp (every block of the tree was stamped when it entered it), and when the
vote has no stamp (the function is read on the votes a node holds, each stamped when it was
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

/-! ## The number of validators and the quorum -/

/-- `validator_count V`: the number of validators, `n`. Every validator has weight `1`. -/
def validator_count (V : Type) [Fintype V] : Nat := Fintype.card V

/-- `quorum V`: two thirds of the number of validators, rounded up, `⌈2 * n / 3⌉`, written
`(2 * n + 2) / 3` in natural numbers. A set of validators `S` is a quorum when
`quorum V ≤ |S|`. -/
def quorum (V : Type) [Fintype V] : Nat := (2 * validator_count V + 2) / 3

end Goldilocks
