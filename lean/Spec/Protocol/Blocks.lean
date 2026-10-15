import Spec.Protocol.ForkChoice.Views
import Spec.Protocol.ForkChoice.Head
import Spec.Protocol.Grades
import Spec.Protocol.GoldfishVotes
import Spec.Protocol.Attestations
import Spec.Broadcast
import Mathlib.Data.Finset.Sort
import Spec.Defs.Notation

/-!
# The blocks, over the flat store

This file is about one kind of object: the block. It holds the update of the store's finality
fields from a block's chain state, the block's admission into the store, and the duty that sends
one, the proposal. What a node does on receiving a block, `receive_block`, is in
`lean/Spec/Node.lean`, with every other routine the wiring calls. The routines here read the
flat store `Store V` of `lean/Spec/Store.lean`, and sit in the namespace
`Spec.Protocol`.

A block admits the Goldfish votes and the attestations it includes, so this file imports
`lean/Spec/Protocol/GoldfishVotes.lean` (for `on_goldfish_vote_checked`) and
`lean/Spec/Protocol/Attestations.lean` (for `admit_attestations`).

The finality update:

- `update_finality`: given a block, fold the chain state the store holds for it into the store's
  finality fields.

The admission:

- `block_admissible`: whether the store admits a block (the checks);
- `add_block`: write a block into the store's block tree, and the attestations it includes
  into the store's (the updates);
- `on_block`: accept a block when the store admits it.

The sending duty, the proposal:

- `proposal_input`: the proposal duty's read of the store;
- `in_admission_window`: whether a round is in the store's admission window;
- `all_attestations`, `sorted_block_roots`, `sorted_blocks`,
  `may_repropose_attestations_of`, `attestations_in_window`,
  `included_attestations_in_window`, `attestations_to_include`: the attestations a proposal may
  include, from the store's own and from those included in the blocks of its tree;
- `build_proposal`: the proposal;
- `propose_block`: the proposal duty. It runs in the monad `DREB` of
  `lean/Spec/Broadcast.lean`: it broadcasts the block it sends and returns what it changes.

`proposal_input` returns what the duty reads off the store, a value of the type
`ProposalInput`.

Functions that read no store, declared here before their callers:

- `included_attestations_admissible`: whether every attestation a block includes is of the
  block's slot's round or an earlier one;
- `attestations_on_chain`, `excludeOnChain`, `capPerSigner`, `proposal_attestations`: the
  attestations a proposal includes, from the candidates it may include.

**Arguments.** Every routine here that reads a parameter takes the parameters `C : Config` of
`lean/Spec/Config.lean`, and also the values `P : Provisional V` when it reads the proposer
of a slot or a committee, and the values `X : External V` when it reads the root of a new block
(`proposal_input`, `build_proposal`, `propose_block`).

**Raising.** `update_finality`, the admission routines and `in_admission_window`,
`all_attestations`, `sorted_block_roots`, `may_repropose_attestations_of`,
`attestations_in_window` are total. `sorted_blocks`,
`included_attestations_in_window`, `attestations_to_include`, `build_proposal` and
`propose_block` raise, as each docstring says: when two blocks of the store's tree `st.T` share a
root (`sorted_blocks`, `proposal_input` and the routines that call them); and when the `g1`
result of the store's round is pending (`proposal_input` and the routines that call it).

No routine of this file takes a function as an argument.

This file holds definitions only.
-/

open scoped DC

open DC (DRE)

namespace Spec.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]
variable (C : Config) (P : Provisional V) (X : External V)

/-! ## The finality update -/

/-- Fold the chain state of the block `B` into the store `st`'s finality fields. The routine
first reads `σ`, the chain state `st.σ[B]` that the store holds for `B`; none of the steps below
writes the state map `st.σ`, so `σ` stays `B`'s chain state throughout. Then three steps, in
order, each reading the store as the previous step left it:

1. the largest chain-state height `st.h_max` becomes the larger of itself and `σ.h`;
2. if the store's finalized block `st.F` is an ancestor of `σ.J` (or `σ.J` itself), and the pair
   (height `st.h_j`, root of `st.J`) is smaller than the pair (`σ.h_j`, root of `σ.J`) in
   lexicographic order, which compares the heights first and, when they are equal, the roots
   (written `<[lex]`), then the justified block and its height become `σ.J` and `σ.h_j`;
3. if `st.F` is a strict ancestor of `σ.F`, `σ.F` is an ancestor of the store's justified block
   `st.J` (or `st.J` itself), and `σ.F` passes the viability test `viable_tree` against the
   store's state map, finalized block, largest chain-state height and block tree, the finalized
   block becomes `σ.F`. -/
def update_finality (st : Store V) (B : Block V) : Store V := Id.run do
  let mut st := st
  let σ := st.σ[B]
  st.h_max ← max st.h_max σ.h
  if st.F.ancestorEq σ.J && (st.h_j, st.J.root) <[lex] (σ.h_j, σ.J.root) then
    st.J ← σ.J
    st.h_j ← σ.h_j
  if st.F.ancestorStrict σ.F && σ.F.ancestorEq st.J &&
      σ.F ∈ viable_tree st.σ st.F st.h_max st.T then
    st.F ← σ.F
  return st

/-! ## The admission -/

/-- Whether every attestation the block `B` includes is of `B`'s slot's round
`C.round_of B.slot` or an earlier round. -/
def included_attestations_admissible (B : Block V) : Bool :=
  B.attestations.all (fun a => a.round ≤ C.round_of B.slot)

/-- Whether the store `st` admits the block `B`. It returns false in each of these cases, tested in
order, and true otherwise:

1. the store's block tree `st.T` already holds `B`, or does not hold `B`'s parent;
2. some attestation that `B` includes is of a later round than `B`'s slot's round
   (`included_attestations_admissible` is false);
3. `B`'s slot is later than the store's slot `st.s`;
4. the store's finalized block `st.F` is not an ancestor of `B` (nor `B` itself);
5. `B`'s proposer is not the proposer of its slot;
6. `B`'s parent's slot is not earlier than `B`'s slot. -/
def block_admissible (st : Store V) (B : Block V) : Bool := Id.run do
  if B ∈ st.T || B.parent ∉ st.T then
    return false
  if ¬ included_attestations_admissible C B then
    return false
  if st.s < B.slot then
    return false
  if ¬ st.F.ancestorEq B then
    return false
  if B.proposer? ≠ P.proposer B.slot then
    return false
  if ¬ (B.parent.slot < B.slot) then
    return false
  return true

/-- Write the block `B` into the store `st`. Its caller has checked that the store admits `B`
(`block_admissible`). In order:

1. `B`'s chain state is stored: `state_transition` computes it from the chain state the store
   holds for `B`'s parent and from `B`, whose attestations it reads;
2. `B` enters the store's block tree `st.T`;
3. `B` is stamped with the store's time `st.t`;
4. each Goldfish vote `B` includes is passed to `on_goldfish_vote_checked`, in list order;
5. the finality fields are updated from `B`'s chain state, stored at step 1, by
   `update_finality`, which is passed `B` and reads that chain state from the store;
6. the attestations `B.attestations` that `B` includes are admitted with
   `admit_attestations`. -/
def add_block (st : Store V) (B : Block V) : Store V := Id.run do
  let mut st := st
  st.σ[B] ← state_transition C P st.σ[B.parent] B
  st.T ← st.T ∪ {B}
  st.timestamp_block[B] ← st.t
  for vote in B.gf_votes do
    st ← on_goldfish_vote_checked P st vote
  st ← update_finality st B
  st ← admit_attestations C st B.attestations
  return st

/-- Admit the block `B` into the store `st`: `add_block` writes it when
`block_admissible` says the store admits it, and otherwise `st` is returned unchanged. -/
def on_block (st : Store V) (B : Block V) : Store V := Id.run do
  if block_admissible C P st B then
    return add_block C P st B
  return st

/-! ## The proposal -/

/-- The proposal duty's read of the store `st` of the validator `v`.

With `s` the store's slot: the Goldfish votes `votes` the proposer counts at `s`
(`proposer_view`) and its support votes `support_votes` (`proposer_support_view`); the composed
head `H` from them for slot `s − 1` (`get_head_with`). The input is the parent `H`, the slot `s`,
the new block's root `X.new_root v s`, the two vote lists, and the proposer `v`.

Raises when `proposer_support_view` or `get_head_with` does: when two blocks of the store's tree
`st.T` share a root, or when the `g1` result of the store's round is pending. -/
def proposal_input (v : V) (st : Store V) : DRE (ProposalInput V) := do
  let s := st.s
  let votes := proposer_view st s
  let support_votes ← proposer_support_view st s
  let H ← get_head_with C st votes.toFinset support_votes.toFinset (s - 1)
  return ⟨H, s, X.new_root v s, votes, support_votes, v⟩

/-- Whether round `r` is in the store's admission window: from `η_SG` rounds before the store's
round `C.round_of st.s` to that round, both included. -/
def in_admission_window (st : Store V) (r : Round) : Bool :=
  C.round_of st.s - C.η_SG ≤ r && r ≤ C.round_of st.s

/-- The attestations the store holds, of every round from `0` to the store's round
`C.round_of st.s`, round by round and in each round in the order processed. -/
def all_attestations (st : Store V) : List (Attestation V) :=
  (List.range (C.round_of st.s + 1)).flatMap st.attestations

/-- The roots of the blocks of the store's tree `st.T`, without repetition, in increasing order. -/
def sorted_block_roots (st : Store V) : List BlockId :=
  ({B.root | B ∈ st.T}).sort (fun a b => a ≤ b)

/-- The blocks of the store's tree, one per root, in increasing order of root: for each root of
`sorted_block_roots st`, the block of `st.T` with that root.

Raises when two blocks of `st.T` share a root: roots name blocks uniquely. Every root of
`sorted_block_roots st` is the root of some block, so with distinct roots each has exactly one. -/
def sorted_blocks (st : Store V) : DRE (List (Block V)) :=
  (sorted_block_roots st).mapM fun root => do
    let B ← pickUnique? st.T (fun B => B.root = root)
    return B

/-- Whether the attestations the block `B` includes may be proposed again: `B`'s round is in the
store's admission window, and the attestations it includes are admissible
(`included_attestations_admissible`). -/
def may_repropose_attestations_of (st : Store V) (B : Block V) : Bool :=
  in_admission_window C st (C.round_of B.slot) &&
    included_attestations_admissible C B

/-- The store's attestations (`all_attestations`) whose own round is in the store's admission
window. -/
def attestations_in_window (st : Store V) : List (Attestation V) :=
  (all_attestations C st).filter (fun row => in_admission_window C st row.round)

/-- The attestations included in the store's eligible blocks, within the admission window: for
each block `B` of `sorted_blocks st`, in order, if `B` is eligible
(`may_repropose_attestations_of`), append those of `B`'s attestations whose own round is in the
store's admission window.

Raises when `sorted_blocks` does: when two blocks of `st.T` share a root. -/
def included_attestations_in_window (st : Store V) : DRE (List (Attestation V)) := do
  let bodies ← sorted_blocks st
  let mut rows := []
  for B in bodies do
    if may_repropose_attestations_of C st B then
      rows ← rows ++ B.attestations.filter (fun row => in_admission_window C st row.round)
  return rows

/-- The attestations a proposal may include: the store's own within the admission window
(`attestations_in_window`), followed by those included in its eligible blocks
(`included_attestations_in_window`).

Raises when `included_attestations_in_window` does: when two blocks of `st.T` share a root. -/
def attestations_to_include (st : Store V) : DRE (List (Attestation V)) := do
  let carried ← included_attestations_in_window C st
  return attestations_in_window C st ++ carried

/-- The attestations included in the block `B` and in each of its ancestors: those of `B` first,
then those of its parent's chain; none for the genesis block. -/
def attestations_on_chain : Block V → List (Attestation V)
  | .genesis => []
  | .node parent _ _ _ _ atts _ => atts ++ attestations_on_chain parent

/-- The attestations of `atts` that are not included in the block `head` nor in any of its
ancestors (`attestations_on_chain head`), in list order. -/
def excludeOnChain (head : Block V) (atts : List (Attestation V)) :
    List (Attestation V) :=
  atts.filter (fun a => a ∉ attestations_on_chain head)

/-- The first two different attestations of `atts` for each validator and round, in list
order. The attestations are read in order; one is kept when it is not kept already and fewer than
two of those kept have its validator and round. -/
def capPerSigner (atts : List (Attestation V)) : List (Attestation V) := Id.run do
  let mut kept := []
  for a in atts do
    if a ∉ kept &&
        (kept.filter (fun b => b.val_index = a.val_index && b.round = a.round)).length < 2 then
      kept ← kept ++ [a]
  return kept

/-- The attestations a proposal with parent `parent` includes, from the candidates `atts`: those
not already included in `parent` or one of its ancestors (`excludeOnChain`), then at most two
different ones per validator and round (`capPerSigner`). -/
def proposal_attestations (parent : Block V) (atts : List (Attestation V)) :
    List (Attestation V) :=
  capPerSigner (excludeOnChain parent atts)

/-- The proposal of the validator `v` on the store `st`.

Read the proposal duty's input from the store (`proposal_input`). Then: the attestations the
proposal may include (`attestations_to_include`), and the block whose parent is the input's parent
`input.parent`, with the input's slot, root, Goldfish votes and proposer, including the
attestations `proposal_attestations` keeps of those: the ones not already included in the parent
or one of its ancestors, at most two per validator and round.

Raises when the read does, or when two blocks of the store's tree share a root. -/
def build_proposal (v : V) (st : Store V) : DRE (Block V) := do
  let input ← proposal_input C X v st
  let rows ← attestations_to_include C st
  return .node (parent := input.parent) (slot := input.slot) (root := input.root)
    (gf_votes := input.gf_votes) (gf_support_votes := input.gf_support_votes)
    (attestations := proposal_attestations input.parent rows)
    (proposer := input.proposer)

/-- The proposal duty of the validator `v` on the store `st`.

Build the proposal `B` that `build_proposal` gives, broadcast it (`broadcast`), and
return the store with `B` admitted by `on_block` (the attestations it includes
admitted as well).

Raises when `build_proposal` does: when two blocks of the store's tree share a root, or when the
`g1` result of the store's round is pending; it then broadcasts nothing. The saved grades
`st.saved_grades` are not written. -/
def propose_block (v : V) (st : Store V) : DREB V (Store V) := do
  let B ← build_proposal C X v st
  broadcast (NamedObject.block B)
  return on_block C P st B

end Spec.Protocol
