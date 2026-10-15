import Spec.Protocol.ForkChoice.Head
import Spec.Defs.Notation

/-!
# The grade computation and the saved grades, over the flat store

The routines that compute a round's grades from the flat store `Store V` of
`lean/Spec/Store.lean`, and that read and write the store's saved grades, in the namespace
`Spec.Protocol`. Each routine's docstring says when it raises.

**The grade computation reads the store.** A grade reads four fields of the store: the block tree
`st.T`, the block stamps `st.timestamp_block`, the strong-gadget votes `st.sg_votes r` (the
`(validator, round, confirmed)` projections of the round's attestations) and their stamps
`st.timestamp_sg_vote`.

- `chain_up`, `chain_of`, `deepest_clear`: a block and its ancestors, and the deepest of them
  between a given ancestor and the block that passes a test;
- `head_covers`, `G0_compatible`: whether a root names a descendant of a block, and the grade-0
  test;
- `token`, `CleanFrom`, `Supports`, `Opposes`: the token of a strong-gadget vote, and the support
  and opposition tests on sets of tokens;
- `bodyReady`, `rawInputs`, `interpretedInputs`, `rawView`, `readyView`: the
  strong-gadget votes of a validator that a grade reads;
- `positive`, `opposing`, `gradeBool`, `freezeRoot`: the grade test and the deepest block that
  passes it;
- `graded_block`: that deepest block for a round and two cutoffs, against the store's finalized
  block.

**The saved grades are the store's field `saved_grades`.** The routines on them:

- `round_grades st r`: the grades of round `r` read from `st.saved_grades`, with every saved block
  replaced by its deepest ancestor compatible with `st.F`;
- `update_grades`: at an instant, bring the store's saved grades to the instant's round, compute
  each grade result whose instant it is, and replace every saved block by its deepest ancestor
  compatible with `st.F`;
- `ComputedGrades`, `computed_grades`, `rawG2`: the three grade blocks of a round once all three
  results are computed, and whether its grade-2 block is a block;
- `get_sg_root`, `stable_root`: the strong-gadget root a grade-1 block gives and the stable-record
  root a grade-2 block gives;
- `anchor`, `grade2Block`, `confirmation_candidate`, `round_stable_root`, `round_grade_read`: the
  reads of a round's grades that the duties use;
- `GradeRead`, `currentSGVote`: one grade read of a round, and the strong-gadget vote chosen from
  it.

No routine takes the saved grades as an argument: they are the store's. `confirmation_candidate`
reads the grade-2 block of the store's round as `st.G2 C`.

A routine reads the block of one grade result `result` with `let G ← result`, which raises when
`result` is pending (the passage of a grade result into the raising type, declared beside
`GradeResult` in `lean/Spec/Objects.lean`).

This file holds definitions only.
-/

open scoped DC

open DC (DRE)

namespace Spec

namespace Protocol

variable {V : Type} [DecidableEq V] [Fintype V]
variable (C : Config) (P : Provisional V)

section Chains

/-- `chain_up n B`: the block `B` and its ancestors, deepest first, at most `n + 1` blocks. When
`n = 0` it is `[B]`. Otherwise it is `B` followed by `chain_up (n − 1)` of `B`'s parent, or `[B]`
when `B` has no parent (`B` is the genesis block). -/
def chain_up : Nat → Block V → List (Block V)
  | 0, B => [B]
  | n + 1, B => Id.run do
    if B.parent? ≠ none then
      return B :: chain_up n B.parent?.value
    return [B]

/-- `chain_of B`: the block `B` and all its ancestors, deepest first, down to the genesis block
(`chain_up` with `B.depth` steps). -/
def chain_of (B : Block V) : List (Block V) :=
  chain_up B.depth B

/-- `deepest_clear floor C test`: the deepest block `B` (`Block.deepest?`) among `C` and its
ancestors such that `floor` is an ancestor of `B`, or `B` itself, and `B` passes `test`; `none`
when no such block exists. -/
def deepest_clear (floor C : Block V) (test : Block V → Bool) : Option (Block V) :=
  Block.deepest? {B ∈ (chain_of C).toFinset | floor.ancestorEq B && test B}

/-- `head_covers T B H`: whether the root `H` names a descendant of the block `B` in the tree `T`,
or `B` itself. When `H` is a root, it is whether `B` is an ancestor of the block of `T` with that
root, or that block itself. An empty root covers nothing.

Raises when `T` does not hold exactly one block with the root `H`. -/
def head_covers (T : Finset (Block V)) (B : Block V) (H : Option BlockId) : DRE Bool := do
  if H ≠ none then
    let head ← Block.find? T H.value
    return B.ancestorEq head
  return false

/-- `G0_compatible G0 B`: whether the block `B` passes the grade-0 test. The test holds when the
grade-0 block `G0` is `none`, or when `B` is compatible with it (one of the two is an ancestor of
the other). -/
def G0_compatible (G0 : Option (Block V)) (B : Block V) : Bool := Id.run do
  if G0 = none then
    return true
  else
    return B.compatible G0.value

end Chains

section Tokens

/-- `token u`: the token of the strong-gadget vote `u`, its round `u.round` and its confirmed root
`u.confirmed`. -/
def token (u : SGVote V) : Token (Option BlockId) := ⟨u.round, u.confirmed⟩

variable {Key : Type*}

/-- `CleanFrom raw r`: whether no two tokens of `raw` of one round, `r` or later, have different
keys. -/
def CleanFrom (raw : Finset (Token Key)) (r : Nat) : Prop :=
  ∀ x ∈ raw, ∀ y ∈ raw, r ≤ x.round → x.round = y.round → x.key = y.key

/-- `Supports covering early late raw`: whether some token `u` of `early` has the greatest round
in `early`, its key is in `covering`, `CleanFrom raw u.round` holds, and every token of `late` of a
round after `u.round` has its key in `covering`. -/
def Supports (covering : Finset Key) (early late raw : Finset (Token Key)) : Prop :=
  ∃ u ∈ early,
    (∀ x ∈ early, x.round ≤ u.round) ∧
    u.key ∈ covering ∧
    CleanFrom raw u.round ∧
    ∀ x ∈ late, u.round < x.round → x.key ∈ covering

/-- `Opposes covering early late raw`: whether some token of `late`, of a round at least every
round of `early`, has its key outside `covering`; or two tokens of `raw` of one round, at least
every round of `early`, have different keys. -/
def Opposes (covering : Finset Key) (early late raw : Finset (Token Key)) : Prop :=
  (∃ x ∈ late, (∀ u ∈ early, u.round ≤ x.round) ∧ x.key ∉ covering) ∨
  ∃ x ∈ raw, ∃ y ∈ raw, (∀ u ∈ early, u.round ≤ x.round) ∧ x.round = y.round ∧ x.key ≠ y.key

/-- `Supports covering early late raw` is decided by checking the tokens of the finite sets. -/
instance supportsDecidable [DecidableEq Key] (covering : Finset Key)
    (early late raw : Finset (Token Key)) : Decidable (Supports covering early late raw) := by
  unfold Supports CleanFrom
  infer_instance

/-- `Opposes covering early late raw` is decided by checking the tokens of the finite sets. -/
instance opposesDecidable [DecidableEq Key] (covering : Finset Key)
    (early late raw : Finset (Token Key)) : Decidable (Opposes covering early late raw) := by
  unfold Opposes
  infer_instance

end Tokens

section GradeComputation

/-- Whether the strong-gadget vote `u` is ready to be read in the store `st`, against the block
`F` and the cutoff `t`.

A vote that names no confirmed root is ready. A vote that names a root is ready when the store's
tree `st.T` holds a block `H` with that root, `H` was stamped strictly before `t`, and `H` is
compatible with `F`. A root that `st.T` does not hold is not ready.

Raises when two blocks of `st.T` have the vote's root (roots name blocks uniquely), and when the
block `H` has no stamp (every block of the tree was stamped when it entered it). -/
def bodyReady (st : Store V) (F : Block V) (t : Time) (u : SGVote V) : DRE Bool := do
  if u.confirmed ≠ none then
    let H? ← blockWithRoot st.T u.confirmed.value
    if H? ≠ none then
      let H := H?.value
      let t_H ← st.timestamp_block H
      return (t_H < (t : Stamp)) && H.compatible F
    return false
  return true

/-- The strong-gadget votes that the validator `v` sent for the rounds of the latest window
`latest_window eta r` and that the store `st` stamped strictly before `t`.

Raises when a strong-gadget vote of `st.sg_votes` in that window has no stamp in
`st.timestamp_sg_vote`: every vote of the store was stamped when it entered it. -/
def rawInputs (st : Store V) (eta r : Round) (t : Time) (v : V) :
    DRE (Finset (SGVote V)) := do
  let votes ← {u ∈ᴹ st.sg_votes_in_window eta r |
    u.val_index = v && (← st.timestamp_sg_vote u) < (t : Stamp)}
  return votes

/-- The strong-gadget votes of the validator `v` for the rounds of the latest window
`latest_window eta r`, stamped strictly before `t`, that are ready to be read in the store
`st` against the block `F` (`bodyReady`).

Raises when `rawInputs` raises (a vote of the window has no stamp) or when `bodyReady` raises on
one of those votes (two blocks of `st.T` share a root, or a block of `st.T` has no stamp). -/
def interpretedInputs (st : Store V) (F : Block V) (eta r : Round) (t : Time)
    (v : V) : DRE (Finset (SGVote V)) := do
  let raw ← rawInputs st eta r t v
  let ready ← {u ∈ᴹ raw | (← bodyReady st F t u)}
  return ready

/-- `R_v`: the tokens (round and confirmed root) of the votes `rawInputs st eta r t v`,
whether or not they are ready to be read. Raises when `rawInputs` raises. -/
def rawView (st : Store V) (eta r : Round) (t : Time) (v : V) :
    DRE (Finset (Token (Option BlockId))) := do
  let raw ← rawInputs st eta r t v
  return {token u | u ∈ raw}

/-- `resolved_votes`: the tokens (round and confirmed root) of the votes
`interpretedInputs st F eta r t v`, the votes of `v` that are ready to be read against `F`
by `t`. Raises when `interpretedInputs` raises. -/
def readyView (st : Store V) (F : Block V) (eta r : Round) (t : Time) (v : V) :
    DRE (Finset (Token (Option BlockId))) := do
  let ready ← interpretedInputs st F eta r t v
  return {token u | u ∈ ready}

/-- `supports(Σ, r, h, e, v, B)`: whether the validator `v` supports the block `B` in round `r`,
with the early cutoff `t_0` and the late cutoff `t_1`. Let
`E_v` be the ready tokens of `v` by `t_0`, `L_v` its ready tokens by `t_1`, and `R_v` its raw
tokens by `t_1`.

1. The roots among the tokens of `E_v` and `L_v` that cover `B` are computed first: a root covers
   `B` when `B` is an ancestor of the block of `st.T` with that root, or that block itself
   (`head_covers` over `st.T`; it raises when `st.T` does not hold exactly one block with it).
2. `v` supports `B` when some token `u` of `E_v` has the greatest round in `E_v`, `u`'s root
   covers `B`, no two raw tokens of `R_v` of one round from `u.round` on name different roots, and
   every token of `L_v` of a round after `u.round` covers `B` (`Supports`).

Raises when one of the three views raises. -/
def positive (st : Store V) (F : Block V) (eta r : Round) (t_0 t_1 : Time) (v : V)
    (B : Block V) : DRE Bool := do
  let E_v ← readyView st F eta r t_0 v
  let L_v ← readyView st F eta r t_1 v
  let R_v ← rawView st eta r t_1 v
  let covering ← {k ∈ᴹ {u.key | u ∈ E_v ∪ L_v} | (← head_covers st.T B k)}
  return Supports covering E_v L_v R_v

/-- `opposes(Σ, r, h, e, v, B)`: whether the validator `v` opposes the block `B` in round `r`,
with the early cutoff `t_0` and the late cutoff `t_1`. Let
`E_v` be the ready tokens of `v` by `t_0`, `L_v` its ready tokens by `t_1`, and `R_v` its raw
tokens by `t_1`.

1. The roots among the tokens of `L_v` that cover `B` are computed first (`head_covers` over
   `st.T`).
2. `v` opposes `B` when some token of `L_v`, of a round at least every round of `E_v`, does not
   cover `B`, or two raw tokens of `R_v` of one round, at least every round of `E_v`, name
   different roots (`Opposes`).

Raises when one of the three views raises. -/
def opposing (st : Store V) (F : Block V) (eta r : Round) (t_0 t_1 : Time) (v : V)
    (B : Block V) : DRE Bool := do
  let E_v ← readyView st F eta r t_0 v
  let L_v ← readyView st F eta r t_1 v
  let R_v ← rawView st eta r t_1 v
  let covering ← {k ∈ᴹ {u.key | u ∈ L_v} | (← head_covers st.T B k)}
  return Opposes covering E_v L_v R_v

/-- `relative_majority(Σ, r, h, e, B)`: whether the weight of the validators that support `B` in
the electorate `P.electorate` (`P.weightOf`) exceeds the weight of those that oppose
it, with the early cutoff `t_0` and the late cutoff `t_1`.

Raises when `positive` or `opposing` raises for some validator. -/
def gradeBool (st : Store V) (F : Block V) (eta r : Round) (t_0 t_1 : Time) (B : Block V) :
    DRE Bool := do
  let opposers ← {v ∈ᴹ Finset.univ | (← opposing st F eta r t_0 t_1 v B)}
  let supporters ← {v ∈ᴹ Finset.univ | (← positive st F eta r t_0 t_1 v B)}
  return P.weightOf opposers < P.weightOf supporters

/-- `graded_block(Σ, r, h, e)`: the deepest block of the store's tree `st.T` that passes the grade
test `gradeBool` with the early cutoff `t_0` and the late cutoff `t_1`, or `none` when no block of `st.T` passes it (or no single deepest one exists).

Raises when `gradeBool` raises on some block of `st.T`. -/
def freezeRoot (st : Store V) (F : Block V) (eta r : Round) (t_0 t_1 : Time) :
    DRE (Option (Block V)) := do
  let graded ← {B ∈ᴹ st.T | (← gradeBool P st F eta r t_0 t_1 B)}
  return Block.deepest? graded

end GradeComputation

section UpdateGrades

/-- `graded_block(Σ, r, h, e)`: the deepest block of the store's tree `st.T` that passes the grade
test of round `r` with the early cutoff `t_0` and the late cutoff `t_1`, read against the store's finalized block `st.F` with the lookback `C.η_SG`
(`freezeRoot`); `none` when no block of `st.T` passes it, or no single deepest one exists. It does
not read the store's saved grades `st.saved_grades`.

Raises when `freezeRoot` raises. -/
def graded_block (st : Store V) (r : Round) (t_0 t_1 : Time) : DRE (Option (Block V)) :=
  freezeRoot P st st.F C.η_SG r t_0 t_1

/-- `update_grades(Σ, t)`: update the store's saved grades `st.saved_grades` at the instant `t`,
reading the store `st`. Let `r` be the round of `t`, `C.round_of (C.slotOf t)`, and
`C.opening r` the instant round `r` opens. `C.Δ` is the delay bound. A saved result is `pending`
until it is computed, and `computed G` afterwards; each computation below saves `computed G`, with
`G` the value `graded_block` returns, a block or `none`.

1. Bring the saved grades to round `r` (`advance_to_round`): `st.saved_grades.current` are then
   round `r`'s grades and `st.saved_grades.next` round `r + 1`'s.
2. At `C.opening (r + 1) − C.Δ`, one delay before round `r + 1` opens, if round `r + 1`'s
   grade-2 result `st.saved_grades.next.g2` is pending: compute it, `graded_block` of round
   `r + 1` with the cutoffs `C.opening (r + 1) − 5 * C.Δ` and `C.opening (r + 1) − C.Δ`.
3. At `C.opening r`, the instant round `r` opens, if round `r`'s grade-1 result
   `st.saved_grades.current.g1` is pending: compute it, `graded_block` of round `r` with the
   cutoffs `C.opening r − 4 * C.Δ` and `C.opening r − 2 * C.Δ`.
4. At `C.opening r + C.Δ`, one delay after round `r` opens, if round `r`'s grade-0 result
   `st.saved_grades.current.g0` is pending: compute it, `graded_block` of round `r` with both
   cutoffs `C.opening r − 3 * C.Δ`.
5. Replace every block in the saved grades by its deepest ancestor compatible with the store's
   finalized block `st.F` (`make_saved_grades_compatible_with`).

A result already computed is never computed again, one computed with no block included.
`graded_block` does not read the saved grades, so each computation reads the store as it was
given. Every field of the store other than `saved_grades` is left as it was.

Each computation is written as two lines, `let G ← graded_block …` and the write of
`computed G` into the result, as in `st.saved_grades.next.g2 ← .computed G`; the arrow on a path
of fields is the draft's notation of `lean/Spec/Objects.lean`.

Raises when `graded_block` raises in step 2, 3 or 4. -/
def update_grades (st : Store V) (t : Time) : DRE (Store V) := do
  let mut st := st
  let r := C.round_of (C.slotOf t)
  st.saved_grades ← advance_to_round st.saved_grades r
  if t = C.opening (r + 1) - C.Δ && st.saved_grades.next.g2 = .pending then
    let G ← graded_block C P st (r + 1) (C.opening (r + 1) - 5 * C.Δ)
      (C.opening (r + 1) - C.Δ)
    st.saved_grades.next.g2 ← .computed G
  if t = C.opening r && st.saved_grades.current.g1 = .pending then
    let G ← graded_block C P st r (C.opening r - 4 * C.Δ) (C.opening r - 2 * C.Δ)
    st.saved_grades.current.g1 ← .computed G
  if t = C.opening r + C.Δ && st.saved_grades.current.g0 = .pending then
    let G ← graded_block C P st r (C.opening r - 3 * C.Δ) (C.opening r - 3 * C.Δ)
    st.saved_grades.current.g0 ← .computed G
  st.saved_grades ← make_saved_grades_compatible_with st.F st.saved_grades
  return st

end UpdateGrades

section RoundGrades

/-- The grades of round `r` read from the store's saved grades, in two steps:

1. `saved`, the grades of round `r` as the store saved them,
   `saved_round_grades st.saved_grades r` (the current round's grades, the next round's grades,
   or pending grades);
2. `saved` with every saved block replaced by its deepest ancestor compatible with the store's
   finalized block `st.F` (`make_round_grades_compatible_with`). -/
def round_grades (st : Store V) (r : Round) : RoundGrades V := Id.run do
  let saved := saved_round_grades st.saved_grades r
  return make_round_grades_compatible_with st.F saved

/-- The three grade blocks of a round once all three of its results are computed: `G2`, `G1`,
`G0`, each a block or `none` (no block passed that grade's test). A round's grades
`RoundGrades V` hold the three results, each of which may still be pending; the fields of
`ComputedGrades V` cannot be pending. -/
structure ComputedGrades (V : Type) where
  G2 : Option (Block V)
  G1 : Option (Block V)
  G0 : Option (Block V)

/-- `computed_grades grades`: the three grade blocks of the round's grades `grades`, read from
their results phase by phase. The read of a result raises when the result is pending, so the
routine raises exactly when one of the three results is pending. -/
def computed_grades (grades : RoundGrades V) : DRE (ComputedGrades V) := do
  let G2 ← grades.g2
  let G1 ← grades.g1
  let G0 ← grades.g0
  return ⟨G2, G1, G0⟩

/-- `rawG2 grades`: whether the grade-2 block of the round's grades `grades` is a block
(`G2 ≠ none`), read before the active prefix is taken. Raises exactly when the grade-2 result is
pending. -/
def rawG2 (grades : RoundGrades V) : DRE Bool := do
  let G2 ← (grades.g2 : DRE (Option (Block V)))
  return G2 ≠ none

/-- One grade read of a round, the inputs of the strong-gadget vote:

- `anchor`: the strong-gadget root the round's grade-1 block gives (`get_sg_root`);
- `Q2`: the grade-2 candidate, the active prefix of the round's grade-2 block, or `none`;
- `clear`: the grade-0 test, whether a block is compatible with the round's grade-0 block;
- `rawG2`: whether the round's grade-2 block is a block, before the active prefix is taken. -/
structure GradeRead (V : Type) where
  anchor : Block V
  Q2 : Option (Block V)
  clear : Block V → Bool
  rawG2 : Bool

/-- `get_sg_root(st)` for the grade-1 block `G1`: `A`, the active prefix `active_prefix st G1`,
and the fork-choice root `get_fg_root st` when `A` is `none` (no grade-1 block, or the fork-choice
root has passed it). -/
def get_sg_root (st : Store V) (G1 : Option (Block V)) : Block V := Id.run do
  let A := active_prefix st G1
  if A = none then
    return get_fg_root st
  else
    return A.value

/-- `stable_root(st)` for the grade-2 block `G2`: `A`, the active prefix `active_prefix st G2`, if
`A` is not `none`, and the fork-choice root `get_fg_root st` otherwise. -/
def stable_root (st : Store V) (G2 : Option (Block V)) : Block V := Id.run do
  let A := active_prefix st G2
  if A ≠ none then
    return A.value
  return get_fg_root st

/-- The anchor that the `g1` result `g1` of a round's grades gives, read against the store `st`:
the raising read of `g1`, then `get_sg_root`.

Raises exactly when `g1` is pending. -/
def anchor (st : Store V) (g1 : GradeResult V) : DRE (Block V) := do
  let G1 ← g1
  return get_sg_root st G1

/-- `A_G2`, the grade-2 candidate of the round's grades `grades`, read against the store `st`: the
active prefix `active_prefix st G2` of their grade-2 block `G2` (`computed_grades`).

The three grade results are read, and the routine raises when one of them is pending. -/
def grade2Block (st : Store V) (grades : RoundGrades V) : DRE (Option (Block V)) := do
  let G ← computed_grades grades
  return active_prefix st G.G2

/-- The strong-gadget candidate that the confirmation duty may adopt: the active prefix
`active_prefix st G2` of the store's grade-2 block `G2 = st.G2 C` of its round.

Raises exactly when that `g2` result is pending. -/
def confirmation_candidate (st : Store V) : DRE (Option (Block V)) := do
  let G2 ← st.G2 C
  return active_prefix st G2

/-- The stable-record root of round `r`, read from the store's saved grades: the raising read of
the `g2` result of the grades `round_grades st r`, then `stable_root`. The answer is a block.

Raises exactly when the `g2` result is pending. -/
def round_stable_root (st : Store V) (r : Round) : DRE (Block V) := do
  let grades := round_grades st r
  let G2 ← grades.g2
  return stable_root st G2

/-- The grade read of round `r` from the store's saved grades: the grades `round_grades st r`,
their anchor, their grade-2 candidate, their grade-0 test and their raw grade-2 test.

Raises exactly when one of the round's three results is pending. -/
def round_grade_read (st : Store V) (r : Round) : DRE (GradeRead V) := do
  let grades := round_grades st r
  let A ← anchor st grades.g1
  let Q2 ← grade2Block st grades
  let G0 ← grades.g0
  let raw ← rawG2 grades
  return ⟨A, Q2, G0_compatible G0, raw⟩

/-- `get_sg_vote`:the strong-gadget vote of a validator with store `st`, given the grade read
`grades`. Let `C` be `st.live_confirmed` and `A` be `grades.anchor`.

1. If some block `B` with `A ⪯ B ⪯ C` passes the grade-0 test `grades.clear`, the vote is the
   deepest such `B`.
2. Otherwise, if the grade-2 candidate `grades.Q2` is a block, the vote is that block.
3. Otherwise, if the round's grade-2 block exists (`grades.rawG2`), the fork-choice root has
   passed it, and the vote is that root `get_fg_root st`.
4. Otherwise the vote is `A`. -/
def currentSGVote (st : Store V) (grades : GradeRead V) : Block V := Id.run do
  let C := st.live_confirmed
  let A := grades.anchor
  let B? := deepest_clear A C grades.clear
  if B? ≠ none then
    return B?.value
  if grades.Q2 ≠ none then
    return grades.Q2.value
  if grades.rawG2 then
    return get_fg_root st
  return A

end RoundGrades

end Protocol

end Spec
