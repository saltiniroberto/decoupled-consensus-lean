import Spec.Protocol.ForkChoice.Views
import Spec.Protocol.ForkChoice.Head
import Spec.Protocol.Grades
import Spec.Protocol.ValidatorClient
import Spec.Broadcast
import Spec.Defs.Notation

/-!
# The attestations, over the flat store

This file is about one kind of object: the attestation. It holds the attestation's admission into
the store and the duty that sends one. What a node does on receiving an attestation,
`receive_attestation`, is in `lean/Spec/Node.lean`, with every other routine the
wiring calls. The routines here read the flat store `Store V` of `lean/Spec/Store.lean` and
the validator's signing history `SigningHistory` of
`lean/Spec/Protocol/ValidatorClient.lean`.

The admission, in the namespace `Spec.Protocol`:

- `round_votes`: the confirmed blocks a validator has named in a round;
- `attestation_admissible`: whether the store admits an attestation (the checks);
- `add_attestation`: write an attestation into the store (the updates);
- `admit_attestation`, `admit_attestations`: accept an attestation when the store admits
  it, and a list of attestations in order.

The sending duty, in the namespace `Spec.Protocol`:

- `grade2_block_with`: the grade-2 candidate of a round;
- `get_sg_vote_with`: the strong-gadget vote, for a grade-2 candidate;
- `fg_source_with`: the block whose chain state the attestation's height pair is read from;
- `get_fg_vote_with`: the finality-gadget fields of the attestation;
- `attestation_input`: the attestation duty's read of the store;
- `build_attestation`: the attestation and the signing history after signing;
- `attest`: the attestation duty. It runs in the monad `DREB` of
  `lean/Spec/Broadcast.lean`: it broadcasts the attestation it sends and returns what it
  changes.

`attestation_input` returns what the duty reads off the store, a value of the type
`AttestationInput`; `build_attestation` passes it to `create`.

**Arguments.** Every routine here that reads a parameter takes the parameters `C : Config` of
`lean/Spec/Config.lean`; none takes the values `P` or `X`. The reads of the duty take a round
`r`; the duty passes the store's round, `C.round_of st.s`.

**Raising.** `round_votes`, `attestation_admissible`, `add_attestation`, `admit_attestation` and
`admit_attestations` are total. The other routines raise when a grade result of the round they
read is pending, or when two blocks of the store's tree `st.T` share a root; each docstring says
which. The grades are read from the store's own saved grades `st.saved_grades`, through
`round_grades`, `grade2Block` and `round_grade_read` of `lean/Spec/Protocol/Grades.lean`.

This file holds definitions only.
-/

open scoped DC

open DC (DRE)

namespace Spec.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]
variable (C : Config)

/-! ## The admission -/

/-- The confirmed blocks that the sender of the attestation `a` has named in the attestations of
round `a.round` the store `st` holds, as a set: `{b.confirmed | b ∈ st.sg_pool a.round,
b.val_index = a.val_index}`. Two attestations naming the same confirmed block count once. -/
def round_votes (st : Store V) (a : Attestation V) : Finset (Option BlockId) :=
  {b.confirmed | b ∈ st.sg_pool a.round, b.val_index = a.val_index}

/-- Whether the store `st` admits the attestation `a`. With the store's round `C.round_of st.s`, it
returns false in each of these cases, and true otherwise:

1. `a`'s round `a.round` is earlier than the store's round less `C.η_SG`, or later than the
   store's round;
2. the confirmed blocks `round_votes st a` that `a`'s sender has named in round `a.round` already
   include `a`'s confirmed block;
3. those confirmed blocks already number two. -/
def attestation_admissible (st : Store V) (a : Attestation V) : Bool := Id.run do
  if a.round < C.round_of st.s - C.η_SG || C.round_of st.s < a.round ||
      a.confirmed ∈ round_votes st a || |round_votes st a| = 2 then
    return false
  return true

/-- Write the attestation `a` into the store `st`. Its caller has checked that the store admits `a`
(`attestation_admissible`). Two writes, in order:

1. `a` is appended to the store's round-`a.round` attestations `st.attestations a.round`;
2. `a`'s strong-gadget vote `sgVote a` (sender, round, confirmed block) is stamped with the
   store's time `st.t`. -/
def add_attestation (st : Store V) (a : Attestation V) : Store V := Id.run do
  let mut st := st
  st.attestations[a.round] ← st.attestations[a.round] ++ [a]
  st.timestamp_sg_vote[sgVote a] ← st.t
  return st

/-- Admit the attestation `row` into the store `st`: `add_attestation` writes it when
`attestation_admissible` says the store admits it, and otherwise `st` is returned unchanged. -/
def admit_attestation (st : Store V) (row : Attestation V) : Store V := Id.run do
  if attestation_admissible C st row then
    return add_attestation st row
  return st

/-- Admit each attestation of `rows` into the store `st` with `admit_attestation`, in
list order. -/
def admit_attestations (st : Store V) (rows : List (Attestation V)) :
    Store V := Id.run do
  let mut st := st
  for row in rows do
    st ← admit_attestation C st row
  return st

/-! ## The attestation's reads -/

/-- The grade-2 candidate `A_G2` of round `r`: `grade2Block` of the round's grades
`round_grades st r`, read against the store `st`.

Raises when one of the round's three grade results is pending. Read by the attestation duty, at
the round's action instant, after the three results complete. -/
def grade2_block_with (st : Store V) (r : Round) : DRE (Option (Block V)) := do
  let grades := round_grades st r
  grade2Block st grades

/-- The strong-gadget vote of round `r`, with the grade-2 candidate `A_G2` supplied by the
caller: the grade read of the round (`round_grade_read`), its grade-2 candidate replaced by
`A_G2`, given to `currentSGVote`.

Raises when one of the round's three grade results is pending. -/
def get_sg_vote_with (st : Store V) (r : Round) (A_G2 : Option (Block V)) : DRE (Block V) := do
  let mut grades ← round_grade_read st r
  grades.Q2 ← A_G2
  return currentSGVote st grades

/-- The finality-gadget source for the grade-2 candidate `A_G2` at round `r`: the block whose
chain state the attestation's height pair is read from.

When there is no candidate, none. Otherwise, with `q` the candidate and `G0` the round's grade-0
block (the `g0` result of the grades `round_grades st r`): the deepest block between `q` and the
store's live confirmed block that passes the grade-0 test `G0_compatible G0` (`deepest_clear`),
when there is one, and `q` itself when there is none.

Raises when there is a candidate and the round's `g0` result is pending. -/
def fg_source_with (st : Store V) (r : Round) (A_G2 : Option (Block V)) :
    DRE (Option (Block V)) := do
  if A_G2 ≠ none then
    let q := A_G2.value
    let grades := round_grades st r
    let G0 ← grades.g0
    let B? := deepest_clear q st.live_confirmed (G0_compatible G0)
    if B? ≠ none then
      return B?.value
    return q
  return none

/-- The finality-gadget fields of the attestation at round `r`, with grade-2 candidate `A_G2`.

The head `H` is the composed head at the store's slot `st.s` (`get_head_with`), from the store's
Goldfish votes of that slot `st.pool st.s` and, as support votes, those of them that are resolved
in the store's block tree `st.T`. The result has four parts:

1. when `fg_source_with` gives a block `q`, the triple of `q`'s chain state's height, the root of
   its target at that height, and its flag saying the height is not justifiable; otherwise none;
2. the justification height `h_j` of `H`'s chain state;
3. the root of its justified block `J`;
4. its finalization height `h_F`.

Raises when `resolved`, `get_head_with` or `fg_source_with` does: when two blocks of `st.T` share
a root, or when the store's round's `g1` result (for the head) or round `r`'s `g0` result (for the
source) is pending. -/
def get_fg_vote_with (st : Store V) (r : Round) (A_G2 : Option (Block V)) :
    DRE (Option (Height × BlockId × Bool) × Height × BlockId × Height) := do
  let votes := st.pool st.s
  let support_votes ← {u ∈ᴹ st.pool st.s | (← resolved st.T u)}
  let H ← get_head_with C st votes support_votes st.s
  let source ← fg_source_with st r A_G2
  let mut fields : Option (Height × BlockId × Bool) := none
  if source ≠ none then
    let q := source.value
    fields ← (st.σ[q].h, st.σ[q].T_h.root, st.σ[q].nj)
  return (fields, st.σ[H].h_j, st.σ[H].J.root, st.σ[H].h_F)

/-! ## The attestation duty -/

/-- The attestation duty's read of the store `st` of the validator `v`.

With `r` the round of the store's slot: the grade-2 candidate `A_G2` of round `r`
(`grade2_block_with`); the finality-gadget fields `fields`, `h_j`, `J`, `h_F` for `A_G2`
(`get_fg_vote_with`); the strong-gadget vote `C` for `A_G2` (`get_sg_vote_with`). The input is the
validator `v`, the round `r`, `C`'s root as the confirmed block, and the four
finality-gadget fields.

Raises when one of the three reads does: when a grade result of round `r` is pending, or when two
blocks of the store's tree `st.T` share a root. -/
def attestation_input (v : V) (st : Store V) : DRE (AttestationInput V) := do
  let r := C.round_of st.s
  let A_G2 ← grade2_block_with st r
  let (fields, h_j, J, h_F) ← get_fg_vote_with C st r A_G2
  let C ← get_sg_vote_with st r A_G2
  return ⟨v, r, C.root, fields, h_j, J, h_F⟩

/-- The attestation of the validator `v` on the store `st`, with the validator's signing history
`signingHistory`.

Read the attestation duty's input from the store (`attestation_input`); return the signing history
after signing and the attestation (`create` on the input).

Raises when the read does: when a grade result of the store's round is pending, or when two
blocks of the store's tree share a root. -/
def build_attestation (v : V) (st : Store V) (signingHistory : SigningHistory) :
    DRE (SigningHistory × Attestation V) := do
  let input ← attestation_input C v st
  return create signingHistory input

/-- The attestation duty of the validator `v` on the store `st`, with the validator's signing
history `signingHistory`. The caller passes the store as it is after the confirmation update of
the same instant.

Build the attestation `row` and the signing history after signing with `build_attestation`;
add `row` to the store with `admit_attestation`; broadcast `row` (`broadcast`); return
the store and the signing history.

Raises when `build_attestation` does; it then broadcasts nothing. The saved grades
`st.saved_grades` are not written. -/
def attest (v : V) (st : Store V) (signingHistory : SigningHistory) :
    DREB V (Store V × SigningHistory) := do
  let mut st := st
  let mut signingHistory := signingHistory
  let {fst ← signingHistory, snd := row} ⇐
    build_attestation C v st signingHistory
  st ← admit_attestation C st row
  broadcast (NamedObject.attest row)
  return (st, signingHistory)

end Spec.Protocol
