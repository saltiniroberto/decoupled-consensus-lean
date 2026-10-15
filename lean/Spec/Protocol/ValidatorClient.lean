import Spec.Defs.Notation
import Spec.Defs.Raise
import Spec.Store

/-!
# The validator's signing history, and the routines that read and write it

The validator's signing history `signingHistory` holds, for every height, the validator's first
target, whether it sent an empty-target vote, and the target of its first finality pair, and
beside them the set of the timeout votes it has sent, each as a height and the block the vote
names. The signing history belongs to the validator, not to the store.

This file declares the record `SigningHistory` of four fields, in the namespace `Spec`,
and its initial value `SigningHistory.initial`; then, in the namespace `Spec.Protocol`,
the routines over it:

- `finality_pair`: the finality pair the signing history allows, or none;
- `own_lock`: the lock `height_pair` reads, with the attestation's own finality pair standing in
  at its height;
- `height_pair`: the height pair the signing history allows;
- `record_attestation`: write an attestation about to be sent into the three maps;
- `create_attestation`: the two pair rules, the attestation, then the signing history;
- `create`: `create_attestation`, then the timeout vote the attestation holds (if any) added to
  the set `signingHistory.timeouts`.

**Two writes.** `record_attestation` writes the three maps and not
`signingHistory.timeouts`; `create` adds the timeout vote to `signingHistory.timeouts` after it.

**Absent values.** An `Option` that is read is tested with `if x ≠ none then … x.value …`, with the
extraction `Option.value`; the notation of `Objects.lean` hands the fact `x ≠ none` of the test to
the read under it. Where only a comparison is needed, the comparison is written
`x = y`, the value coerced.

**Writes.** The indexed write `signingHistory.lock[h] ← T` replaces the value of the map
`signingHistory.lock` at `h` and keeps every other height's.

`create` calls `rememberTimeout`, which reads no signing history and is declared before it: the
set of timeout votes with a height pair added when it is a timeout vote. The input of `create` is
the attestation duty's read of the store, of the type `AttestationInput`.

This file holds definitions only.
-/

open scoped DC

namespace Spec

/-- The validator's signing history: what the validator has signed, kept height by height. It is
read to decide what the next attestation may say.

- `target h`: the validator's first target at height `h`, or `none`;
- `timeout h`: whether it has sent an empty-target vote at height `h`;
- `lock h`: the target of its first finality pair at height `h`, or `none`;
- `timeouts`: the timeout votes it has sent, each as its height and the block it names. -/
structure SigningHistory where
  target : (h : Height) → Option BlockId
  timeout : (h : Height) → Bool
  lock : (h : Height) → Option BlockId
  timeouts : Finset (Height × BlockId)

namespace SigningHistory

/-- The initial signing history: no target, no empty-target vote and no lock at any height, and
no timeout vote sent. -/
def initial : SigningHistory where
  target := fun _ => none
  timeout := fun _ => false
  lock := fun _ => none
  timeouts := ∅

end SigningHistory

end Spec

namespace Spec.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The pair rules -/

/-- The finality pair a validator with signing history `signingHistory` signs, given the head's
chain state's justification height `h_j`, justified block `J` and finalization height `h_F`.

It returns `none` (no finality pair) when the justification is already finalized
(`h_j ≤ h_F`), when the signing history holds a target at `h_j` other than `J`, when it holds an
empty-target vote at `h_j`, or when it holds a lock at `h_j` other than `J`. Otherwise it returns
the pair `(h_j, J)`.

A validator that holds no target at `h_j` may therefore sign the pair. This routine does not
write the signing history; `record_attestation` does. -/
def finality_pair (signingHistory : SigningHistory) (h_j : Height) (J : BlockId) (h_F : Height) :
    Option FinalityPair := Id.run do
  if h_j ≤ h_F then
    return none
  if signingHistory.target[h_j] ≠ none && signingHistory.target[h_j] ≠ J then
    return none
  if signingHistory.timeout[h_j] then
    return none
  if signingHistory.lock[h_j] ≠ none && signingHistory.lock[h_j] ≠ J then
    return none
  return FinalityPair.mk (height := h_j) (target := J)

/-- The lock that `height_pair` reads at height `h_c`: when this attestation's own finality pair
`fp` is at height `h_c`, its target; otherwise the signing history's lock
`signingHistory.lock h_c`.

So one attestation never signs a height pair that contradicts its own finality pair. -/
def own_lock (signingHistory : SigningHistory) (h_c : Height) (fp : Option FinalityPair) :
    Option BlockId := Id.run do
  if fp ≠ none then
    let p := fp.value
    if p.height = h_c then
      return p.target
  return signingHistory.lock[h_c]

/-- The height pair a validator with signing history `signingHistory` signs. `fields` is
`(h_c, T_c, ν)` taken from a confirmed block's chain state: its height `h_c`, its target `T_c`,
and the flag `ν` saying the height is not justifiable; or `none` when there is nothing to offer.
`fp` is the finality pair of the same attestation.

The cases, tried in order:

Write "the target vote at `h_c`" for the vote at `h_c` for `T_c` that is not a timeout vote,
`.vote h_c T_c false`, and "the timeout vote at `h_c`" for the timeout vote at `h_c` cast on
`T_c`, `.vote h_c T_c true`.

1. `fields` is `none`: the empty pair.
2. The signing history holds an empty-target vote at `h_c`: the timeout vote at `h_c` again.
3. The lock at `h_c` (`own_lock signingHistory h_c fp`) is set: the target vote at `h_c` when the
   lock is `T_c`, and otherwise the empty pair, so a validator locked on another block abstains
   from the height.
4. The signing history holds a target at `h_c`: the target vote at `h_c` when that target is
   `T_c`, and otherwise the timeout vote at `h_c`.
5. The signing history holds nothing at `h_c`: the timeout vote at `h_c` when `ν` is set, and
   otherwise the target vote at `h_c`.

Both target tests are equalities of block roots, not ancestry. -/
def height_pair (signingHistory : SigningHistory) (fields : Option (Height × BlockId × Bool))
    (fp : Option FinalityPair) : HeightPair := Id.run do
  if fields ≠ none then
    let (h_c, T_c, ν) := fields.value
    if signingHistory.timeout[h_c] then
      return .vote h_c T_c true
    let lock := own_lock signingHistory h_c fp
    if lock ≠ none then
      if lock = T_c then
        return .vote h_c T_c false
      return .empty
    if signingHistory.target[h_c] ≠ none then
      if signingHistory.target[h_c] = T_c then
        return .vote h_c T_c false
      return .vote h_c T_c true
    if ν then
      return .vote h_c T_c true
    return .vote h_c T_c false
  return .empty

/-! ## The attestation and the signing history -/

/-- The height a height pair carries: `h` for a vote at `h`, a target vote or a timeout vote, and
`none` for the empty pair.

It is declared in the namespace of the type `HeightPair`, so a value `p : HeightPair`
reads it as `p.pairHeight?`. -/
def _root_.Spec.HeightPair.pairHeight? : HeightPair → Option Height
  | .empty => none
  | .vote h _ _ => h

/-- The target a height pair names: `T` for the target vote at `h` for `T`, and `none` for the
empty pair and for a timeout vote, whose block is not a target. Its height is
`HeightPair.pairHeight?`. -/
def _root_.Spec.HeightPair.target? : HeightPair → Option BlockId
  | .vote _ T false => T
  | _ => none

/-- Write attestation `a`, about to be sent, into the three maps of the signing history
`signingHistory`; the set `signingHistory.timeouts` is left unchanged (`create` writes it).

1. If `a` carries a finality pair `(h, T)`, set the lock at `h` to `T`.
2. Then by `a`'s height pair: the empty pair writes nothing; a timeout vote at `h` sets the
   signing history's empty-target flag at `h`; a target vote at `h` for `T` sets the target at `h`
   to `T` only when the signing history holds no target at `h` (the first target is kept). -/
def record_attestation (signingHistory : SigningHistory) (a : Attestation V) :
    SigningHistory := Id.run do
  let mut signingHistory := signingHistory
  if a.finality_pair ≠ none then
    let p := a.finality_pair.value
    signingHistory.lock[p.height] ← p.target
  if a.height_pair.pairHeight? ≠ none then
    let h := a.height_pair.pairHeight?.value
    if a.height_pair.target? ≠ none then
      if signingHistory.target[h] = none then
        signingHistory.target[h] ← a.height_pair.target?.value
    else
      signingHistory.timeout[h] ← true
  return signingHistory

/-- The attestation validator `v` sends at round `r`, built from the signing history
`signingHistory`, and the signing history after signing. `confirmed` is the confirmed block the
attestation names; `fields` is what `height_pair` reads; `h_j`, `J`, `h_F` are what
`finality_pair` reads.

First the finality pair, then the height pair (which reads the finality pair), then the
attestation, then the signing history with the attestation written into it. The signing history
is returned beside the attestation; this routine reads no store. -/
def create_attestation (signingHistory : SigningHistory) (v : V) (r : Round)
    (confirmed : Option BlockId) (fields : Option (Height × BlockId × Bool))
    (h_j : Height) (J : BlockId) (h_F : Height) :
    SigningHistory × Attestation V := Id.run do
  let mut signingHistory := signingHistory
  let fp := finality_pair signingHistory h_j J h_F
  let hp := height_pair signingHistory fields fp
  let a := Attestation.mk (val_index := v) (round := r)
    (confirmed := confirmed) (height_pair := hp) (finality_pair := fp)
  signingHistory ← record_attestation signingHistory a
  return (signingHistory, a)

/-! ## The timeout votes -/

/-- The timeout votes `history` with the height pair `pair` added when it is a timeout vote: the
timeout vote at `h` cast on `entry` adds `(h, entry)`; any other pair adds nothing. -/
def rememberTimeout (history : Finset (Height × BlockId)) (pair : HeightPair) :
    Finset (Height × BlockId) :=
  match pair with
  | .vote h entry true => history ∪ {(h, entry)}
  | _ => history

/-- The attestation for `input`, built from the signing history `signingHistory`, and the signing
history after signing.

Run `create_attestation` on `signingHistory` with `input`'s fields, which makes every pair
decision, builds the attestation and writes the three maps once; and when the attestation's
height pair is a timeout vote at height `h` cast on block `entry`, add `(h, entry)` to
`signingHistory.timeouts` (`rememberTimeout`). -/
def create (signingHistory : SigningHistory) (input : AttestationInput V) :
    SigningHistory × Attestation V := Id.run do
  let mut signingHistory := signingHistory
  let {fst ← signingHistory, snd := a} := create_attestation signingHistory input.val_index
    input.round input.confirmed input.fields input.h_j input.J input.h_F
  signingHistory.timeouts ← rememberTimeout signingHistory.timeouts a.height_pair
  return (signingHistory, a)

end Spec.Protocol
