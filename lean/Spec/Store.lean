import Spec.Defs.Notation
import Spec.Config
import Spec.Objects
import Spec.Protocol.ChainState

/-!
# The flat store

One record, `Store V`, holds everything a validator's node keeps about the protocol, apart from
the validator's own signing history: the clock and the slot, the block tree and the state of each
block, the stamps, the Goldfish votes and the attestations it has processed, the finality fields,
the three confirmation records, and the saved grades.

This file declares the record, its initial value, and the readers every routine of the flat store
uses: the vote sets of a slot and of a round, the resolution time of a vote, and the saved grades
of the store's round.

**The saved grades.** The saved grades `SavedGrades V` hold the three grade results of the round
they are aligned to and those of the next round, each result pending or computed, and a computed
result a block or none. The store keeps them in its field `saved_grades`, and `Store.G2`, `Store.G1` read it: the result of
their phase for the store's round, with its block replaced by its deepest ancestor compatible with
the store's finalized block, raising when that result is still pending.

**The strong-gadget vote of an attestation.** `Protocol.sgVote a`, declared here, is the
`(validator, round, confirmed)` projection of the attestation `a`.

**The reads of a round's grades.** Declared here, in the namespace `Spec.Protocol`:
`pending_round_grades` and `empty_round_grades`, a round's grades with every result pending or
computed with no block; `phaseResult`, the result of one phase; `initial_saved_grades`, the saved
grades of the initial store; and `saved_round_grades`, the grades of one round in the saved
grades. A routine reads the block of a result `result` with `let G ← result`, which raises when
`result` is pending.

**The routines on the saved grades.** The routines of the flat store that change the saved grades
call five definitions declared here, in the namespace `Spec.Protocol`, over the types
`SavedGrades V` and `RoundGrades V`: `advance_to_round`, which brings the saved grades to a round,
and `deepest_compatible_ancestor`, `make_result_compatible_with`,
`make_round_grades_compatible_with`, `make_saved_grades_compatible_with`, which replace a saved
block, the block of one saved result, the blocks of one round's grades and the blocks of all the
saved grades by their deepest ancestor compatible with a given block.
`deepest_compatible_ancestor` walks from the block to its parent in a `for` of `g.depth + 1` steps,
one per block from `g` to the genesis block.

**Blocks and attestations.** The field `T` holds the blocks the store has processed and the field
`attestations` the attestations. Their types `Block V` and `Attestation V` are declared in
`lean/Spec/Objects.lean`, with the types `GradeResult V`, `RoundGrades V` and
`SavedGrades V`.

**Attestations and strong-gadget votes.** The field `attestations` holds a round's attestations;
the reader `Store.sg_votes` gives the set of their `(validator, round, confirmed)` projections.

**The blocks the node exposes.** `get_stable` and `get_confirmed`, in the namespace
`Spec.Protocol`, read the stable and the confirmed block the node exposes off the store.
No routine of the draft calls them.

This file holds definitions only.
-/

open scoped DC

open Spec.Protocol (ChainState SGVote Phase)
open DC (DRE)

namespace Spec

variable {V : Type} [DecidableEq V] [Fintype V]

namespace Protocol

/-- The strong-gadget vote of the attestation `a`: its sender `a.val_index`, its round `a.round`
and its confirmed block `a.confirmed`. Two attestations that differ only in their height pair or
their finality pair give the same strong-gadget vote. -/
def sgVote (a : Attestation V) : SGVote V :=
  SGVote.mk (val_index := a.val_index) (round := a.round) (confirmed := a.confirmed)

section RoundGradesRead

/-! ## A round's grades and their reads

A round's grades `RoundGrades V` hold three saved grade results, `g0`, `g1` and `g2`, each a
`GradeResult V`: `pending` while it is not computed, and `computed G` once it is, where `G` is the
block the computation returned, or `none` when no block passed. -/

/-- The round's grades with every result pending. -/
def pending_round_grades : RoundGrades V := ⟨.pending, .pending, .pending⟩

/-- The round's grades with every result computed with no block. -/
def empty_round_grades : RoundGrades V := ⟨.computed none, .computed none, .computed none⟩

/-- `phaseResult grades p`: the result of phase `p` in the round's grades `grades`: `grades.g0`,
`grades.g1` or `grades.g2`. -/
def phaseResult (grades : RoundGrades V) (p : Phase) : GradeResult V :=
  if p = .g0 then grades.g0 else if p = .g1 then grades.g1 else grades.g2

/-- The saved grades of the initial store: round `0`, whose grades have every result computed with
no block (`empty_round_grades`), and the grades of round `1` with every result pending
(`pending_round_grades`). -/
def initial_saved_grades : SavedGrades V := ⟨0, empty_round_grades, pending_round_grades⟩

/-- `saved_round_grades c r`: the grades of round `r` in the saved grades `c`: `c.current` when `r`
is their round `c.round`, `c.next` when `r` is the next round `c.round + 1`, and the round's grades
with every result pending otherwise. -/
def saved_round_grades (c : SavedGrades V) (r : Round) : RoundGrades V :=
  if r = c.round then c.current
  else if r = c.round + 1 then c.next
  else pending_round_grades

end RoundGradesRead

section SavedGrades

/-! ## The routines on the saved grades

The saved grades `SavedGrades V` hold a round `c.round`, the grades of that round `c.current` and
the grades of the next round `c.next`. A round's grades `RoundGrades V` hold three saved grade
results, `g0`, `g1` and `g2`, each a `GradeResult V`: `pending` while it is not computed, and
`computed G` once it is, where `G` is the block the computation returned, or `none` when no block
passed. -/

/-- The deepest ancestor of the block `g` that is compatible with the block `F`, `g` itself
included: `g` when `g` is compatible with `F` (one of the two is an ancestor of the other, or they
are equal), and otherwise the same search from `g`'s parent. The genesis block is returned as it
is: it is compatible with every block. The loop's bound `g.depth + 1` is the number of blocks from
`g` to the genesis block. -/
def deepest_compatible_ancestor (g F : Block V) : Block V := Id.run do
  let mut g := g
  for _ in [:g.depth + 1] do
    if g.compatible F then
      return g
    g ← g.parent
  return g

/-- A saved grade result with its block replaced by its deepest ancestor compatible with the
block `F`: a computed result whose block `G = result.block` is a block becomes `computed` of
`deepest_compatible_ancestor G.value F`, the deepest ancestor of that block compatible with `F`;
the result `pending`, and a result computed with no block (`computed none`), are returned as
they are. -/
def make_result_compatible_with (F : Block V) (result : GradeResult V) : GradeResult V :=
  Id.run do
  if result ≠ .pending then
    let G := result.block
    if G ≠ none then
      return .computed (deepest_compatible_ancestor G.value F)
  return result

/-- The grades `f` of a round, with every saved block of their three results `g0`, `g1`, `g2`
replaced by its deepest ancestor compatible with the block `F` (`make_result_compatible_with`). -/
def make_round_grades_compatible_with (F : Block V) (f : RoundGrades V) : RoundGrades V :=
  ⟨make_result_compatible_with F f.g0, make_result_compatible_with F f.g1,
    make_result_compatible_with F f.g2⟩

/-- The saved grades `c` with every saved block of their two rounds' grades, `c.current` and
`c.next`, replaced by its deepest ancestor compatible with the block `F`
(`make_round_grades_compatible_with`). The round `c.round` is kept. -/
def make_saved_grades_compatible_with (F : Block V) (c : SavedGrades V) : SavedGrades V :=
  ⟨c.round, make_round_grades_compatible_with F c.current,
    make_round_grades_compatible_with F c.next⟩

/-- The saved grades `c` brought to round `r`:

1. when `r` is their round `c.round`, the saved grades `c` as they are;
2. when `r` is the next round `c.round + 1`, the saved grades of round `r` whose grades of round
   `r` are `c.next`, the grades `c` saved for that round, and whose grades of round `r + 1` have
   every result pending (`pending_round_grades`);
3. otherwise, the saved grades of round `r` whose two rounds' grades have every result pending.

No result is computed: a result `c` did not save is pending afterwards. -/
def advance_to_round (c : SavedGrades V) (r : Round) : SavedGrades V :=
  if r = c.round then c
  else if r = c.round + 1 then ⟨r, c.next, pending_round_grades⟩
  else ⟨r, pending_round_grades, pending_round_grades⟩

end SavedGrades

end Protocol

/-- A total map read by application, written with the protocol's brackets: `f[a]` is `f a`.
Scoped to `Spec`, so it is active only inside that namespace and the namespaces under
it. -/
scoped instance funGetElem {α β : Type} : GetElem (α → β) α β (fun _ _ => True) where
  getElem f a _ := f a

/-- The store of a validator's node.

- `t`, `s`: the current instant and the current slot.
- `T`: the tree of the blocks the store has processed; never pruned.
- `timestamp_block`, `timestamp_vote`, `timestamp_sg_vote`: the instant each block, Goldfish vote
  and strong-gadget vote was processed; `none` for one never processed.
- `σ`: the chain state after each block.
- `gf_votes s`: the Goldfish votes of slot `s` the store has processed, at most two per validator.
- `attestations r`: the attestations of round `r` the store has processed, at most two with
  distinct confirmed blocks per validator.
- `saved_grades`: the saved grades (read by `Store.G2`, `Store.G1`).
- `F`, `J`, `h_j`, `h_max`: the finalized block, the justified block, its height, and the largest
  chain-state height the store has seen.
- `live_confirmed`, `latest_confirmed`, `latest_stable`: the confirmed block the voting duties
  read, the confirmation record the node exposes, and the stable record. -/
structure Store (V : Type) where
  t : Time
  s : Slot
  T : Finset (Block V)
  timestamp_block : (B : Block V) → Option Stamp
  timestamp_vote : (vote : GoldfishVote V) → Option Stamp
  timestamp_sg_vote : (u : SGVote V) → Option Stamp
  σ : (B : Block V) → ChainState V
  gf_votes : (s : Slot) → List (GoldfishVote V)
  attestations : (r : Round) → List (Attestation V)
  saved_grades : SavedGrades V
  F : Block V
  J : Block V
  h_j : Height
  h_max : Height
  live_confirmed : Block V
  latest_confirmed : Block V
  latest_stable : Block V

namespace Store

section Readers

variable (C : Config)

/-! ## The initial store -/

/-- The initial store: the clock and the slot at `0`; the tree holds the genesis block only,
stamped at the least instant; no vote and no attestation; every block's chain state is the
initial one; the finalized block, the justified block and the three confirmation records are the
genesis block, the justified height is `0` and the largest chain-state height `1`; and the saved
grades are `Protocol.initial_saved_grades`
(round `0`, its grades computed with no block and the next round's grades pending). -/
def init : Store V where
  t := 0
  s := 0
  T := {Block.genesis}
  timestamp_block := fun B => if B = Block.genesis then some genesisStamp else none
  timestamp_vote := fun _ => none
  timestamp_sg_vote := fun _ => none
  σ := fun _ => Protocol.ChainState.initial
  gf_votes := fun _ => []
  attestations := fun _ => []
  saved_grades := Protocol.initial_saved_grades
  F := Block.genesis
  J := Block.genesis
  h_j := 0
  h_max := 1
  live_confirmed := Block.genesis
  latest_confirmed := Block.genesis
  latest_stable := Block.genesis

/-! ## The vote sets -/

/-- `st.pool s`: the Goldfish votes of slot `s` the store has processed, as a set. -/
def pool (st : Store V) (s : Slot) : Finset (GoldfishVote V) :=
  st.gf_votes[s].toFinset

/-- `st.sg_pool r`: the attestations of round `r` the store has processed, as a set. -/
def sg_pool (st : Store V) (r : Round) : Finset (Attestation V) :=
  st.attestations[r].toFinset

/-- `st.sg_votes r`: the strong-gadget votes of round `r`, each the `(validator, round,
confirmed)` projection of an attestation of `st.sg_pool r`. Every rule of the strong gadget and
every grade reads an attestation only through this projection. -/
def sg_votes (st : Store V) (r : Round) : Finset (SGVote V) :=
  {Protocol.sgVote a | a ∈ st.sg_pool r}

/-- `st.included_votes s`: the slot-`(s − 1)` Goldfish votes included in the slot-`s` blocks of
the store's tree `st.T`. -/
def included_votes (st : Store V) (s : Slot) : Finset (GoldfishVote V) :=
  {B ∈ st.T | B.slot = s}.biUnion fun B => {vote ∈ B.gf_votes.toFinset | vote.slot = s - 1}

/-- `st.included_support_votes s`: the slot-`(s − 1)` support votes included in the slot-`s`
blocks of the store's tree `st.T`. -/
def included_support_votes (st : Store V) (s : Slot) : Finset (GoldfishVote V) :=
  {B ∈ st.T | B.slot = s}.biUnion fun B =>
    {vote ∈ B.gf_support_votes.toFinset | vote.slot = s - 1}

/-- `st.sg_votes_in_window eta r`: the strong-gadget votes of the store for the rounds of the
latest window `latest_window eta r`. -/
def sg_votes_in_window (st : Store V) (eta r : Round) : Finset (SGVote V) :=
  (Protocol.latest_window eta r).toFinset.biUnion st.sg_votes

/-! ## The resolution time -/

/-- `st.tau vote`: the resolution time of the Goldfish vote `vote`, the later of the instant the
vote was processed and the instant its head block was, read over the store's tree and stamps;
`none` (never) while the tree holds no head block for the vote, or holds one of a later slot than
the vote's.

Raises when two blocks of `st.T` have the vote's head root, when the head block has no stamp, or
when the vote has no stamp. -/
def tau (st : Store V) (vote : GoldfishVote V) : DRE Occurrence :=
  Protocol.resolution_time st.T st.timestamp_block st.timestamp_vote vote

/-! ## The saved grades of the store's round -/

/-- `st.grade C p`: the saved grade of phase `p` for the store's round `C.round_of st.s`, a
block or `none`. In order:

1. `saved`, the grades of that round read from the saved grades (`saved_round_grades`);
2. `grades`, `saved` with every saved block replaced by its deepest ancestor compatible with the
   store's finalized block `st.F` (`make_round_grades_compatible_with`);
3. `G`, the block of the phase's result `phaseResult grades p`; this read raises when the result
   is pending.

Raises when that result is pending: the instant that completes it has not been processed. -/
def grade (st : Store V) (p : Phase) : DRE (Option (Block V)) := do
  let saved := Protocol.saved_round_grades st.saved_grades (C.round_of st.s)
  let grades := Protocol.make_round_grades_compatible_with st.F saved
  let G ← Protocol.phaseResult grades p
  return G

/-- `st.G2 C`: the store's grade-2 block of its round, or `none`; raises when the grade-2 result
of the round is pending. -/
def G2 (st : Store V) : DRE (Option (Block V)) := st.grade C .g2

/-- `st.G1 C`: the store's grade-1 block of its round, or `none`; raises when the grade-1 result
of the round is pending. -/
def G1 (st : Store V) : DRE (Option (Block V)) := st.grade C .g1

end Readers

end Store

namespace Protocol

/-! ## The stable and the confirmed block the node exposes -/

/-- The stable block the node exposes: the stable record `st.latest_stable` when the finalized
block `st.F` is an ancestor of it (or it itself), and `st.F` otherwise. -/
def get_stable (st : Store V) : Block V := Id.run do
  if st.F.ancestorEq st.latest_stable then
    return st.latest_stable
  return st.F

/-- The confirmed block the node exposes: the confirmation record `st.latest_confirmed` when the
stable block `get_stable st` is an ancestor of it (or it itself), and `get_stable st`
otherwise. -/
def get_confirmed (st : Store V) : Block V := Id.run do
  if (get_stable st).ancestorEq st.latest_confirmed then
    return st.latest_confirmed
  return get_stable st

end Protocol

end Spec
