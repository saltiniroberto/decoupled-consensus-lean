module
public import Goldilocks.Objects
public import Spec2.Defs.Notation
public import Spec2.Defs.Raise

@[expose] public section

/-!
# The anti-slashing record and the validator client

The anti-slashing record `Λ` holds, for every height, the first target the validator sent at that
height, whether it sent a timeout there, and the target of its first finality pair there; and the
set of the contents of the attestations it sent. The validator client decides what the validator's
next attestation says from `Λ` alone, and writes the attestation into `Λ` before it is sent.

This file declares, in the namespace `Goldilocks`:

- `SigningHistory`, the type of the anti-slashing record, and its initial value
  `SigningHistory.initial`;
- `finality_pair`: the finality pair the record allows, or none;
- `own_lock`: the lock `height_pair` reads, with the attestation's own finality pair standing in
  at its height;
- `height_pair`: the height pair the record allows;
- `HeightPair.height?` and `HeightPair.target?`: the height and the target a height pair names;
- `already_sent`: whether the record forbids a vote because of an attestation already sent;
- `record_attestation`: write an attestation about to be sent into the record;
- `create_attestation`: the two pair rules, the attestation, then the record.

This file holds definitions only.
-/

open scoped DC

namespace Goldilocks

/-! ## The anti-slashing record -/

/-- The anti-slashing record of a validator: what it has signed, kept height by height. It belongs
to the validator and persists through a restart of its node. -/
structure SigningHistory where
  /-- `target h`: the first target the validator sent at the height `h`, or `none`. -/
  target : (h : Height) → Option BlockId
  /-- `timeout h`: whether the validator sent a timeout at the height `h`. -/
  timeout : (h : Height) → Bool
  /-- `lock h`: the target of the validator's first finality pair at the height `h`, or `none`. -/
  lock : (h : Height) → Option BlockId
  /-- The contents of the attestations the validator sent. -/
  sent : Finset AttestationContent

/-- The initial anti-slashing record: no target, no timeout and no lock at any height, and no
attestation sent. -/
@[no_expose] def SigningHistory.initial : SigningHistory where
  target := fun _ => none
  timeout := fun _ => false
  lock := fun _ => none
  sent := ∅

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The pair rules -/

/-- The finality pair a validator with the anti-slashing record `Λ` signs, given the justification
height `h_j`, the root of the justified block `J` and the finalization height `h_F` of its source.

It returns `none` (no finality pair) when the justification is already finalized
(`h_j ≤ h_F`), when `Λ` holds a target at `h_j` other than `J`, when `Λ` holds a timeout at `h_j`,
or when `Λ` holds a lock at `h_j` other than `J`. Otherwise it returns the pair `(h_j, J)`. -/
@[no_expose] def finality_pair (Λ : SigningHistory) (h_j : Height) (J : BlockId) (h_F : Height) :
    Option FinalityPair := Id.run do
  if h_j ≤ h_F then
    return none
  if Λ.target[h_j] ≠ none && Λ.target[h_j] ≠ J then
    return none
  if Λ.timeout[h_j] then
    return none
  if Λ.lock[h_j] ≠ none && Λ.lock[h_j] ≠ J then
    return none
  return FinalityPair.mk (hf := h_j) (Tf := J)

/-- The lock that `height_pair` reads at the height `h_c`: when the attestation's own finality pair
`fp` is at the height `h_c`, its target; otherwise the record's lock `Λ.lock[h_c]`. -/
@[no_expose] def own_lock (Λ : SigningHistory) (h_c : Height) (fp : Option FinalityPair) :
    Option BlockId := Id.run do
  if fp ≠ none then
    let p := fp.value
    if p.hf = h_c then
      return p.Tf
  return Λ.lock[h_c]

/-- The height pair a validator with the anti-slashing record `Λ` signs. `fields` is the height
`h_c` of its source and the root `T_c` of the block that took the source into that height, or
`none` when there is no source. `fp` is the finality pair of the same attestation.

Write "the target at `h_c`" for the vote `.vote h_c T_c false`, and "the timeout at `h_c`" for
`.vote h_c T_c true`. The cases, tried in order:

1. `fields` is `none`: the empty pair.
2. `Λ` holds a timeout at `h_c`: the timeout at `h_c`.
3. The lock at `h_c` (`own_lock Λ h_c fp`) is set: the target at `h_c` when the lock is `T_c`, and
   otherwise the empty pair.
4. `Λ` holds no target at `h_c`, or holds `T_c` there: the target at `h_c`.
5. Otherwise: the timeout at `h_c`. -/
@[no_expose] def height_pair (Λ : SigningHistory) (fields : Option (Height × BlockId))
    (fp : Option FinalityPair) : HeightPair := Id.run do
  if fields ≠ none then
    let (h_c, T_c) := fields.value
    let lock := own_lock Λ h_c fp
    if Λ.timeout[h_c] then
      return .vote h_c T_c true
    if lock ≠ none then
      if lock = T_c then
        return .vote h_c T_c false
      return .empty
    if Λ.target[h_c] = none || Λ.target[h_c] = T_c then
      return .vote h_c T_c false
    return .vote h_c T_c true
  return .empty

/-- `p.height?`: the height of the height pair `p`: `h` for a vote at `h`, a target or a timeout,
and `none` for the empty pair. -/
@[no_expose] def HeightPair.height? : HeightPair → Option Height
  | .empty => none
  | .vote h _ _ => h

/-- `p.target?`: the target the height pair `p` names: `T` for the target vote at a height for
`T`, and `none` for the empty pair and for a timeout. -/
@[no_expose] def HeightPair.target? : HeightPair → Option BlockId
  | .vote _ T false => T
  | _ => none

/-! ## The attestation and the record -/

/-- `already_sent Λ h T τ`: whether the record `Λ` holds an attestation sent at the height `h` that
forbids the vote at `h` for `T` (a timeout when `τ` is `true`): any attestation at `h` forbids a
target vote, and an attestation at `h` for `T` forbids a timeout for `T`. So a validator sends a
target at a height only as its first vote there, and names each block at most once at a
height. -/
@[no_expose] def already_sent (Λ : SigningHistory) (h : Height) (T : BlockId) (τ : Bool) : Bool :=
  ∃ b ∈ Λ.sent, b.h = h ∧ (!τ ∨ b.T = T)

/-- The anti-slashing record `Λ` with the attestation `a`, about to be sent, written into it.

1. The content of `a` is added to `Λ.sent`.
2. If `a` has a finality pair `p`, the lock at `p.hf` is set to `p.Tf`.
3. If `a` is a target vote at the height `a.h` and `Λ` holds no target there, the target at `a.h`
   is set to `a.T`.
4. If `a` is a timeout at the height `a.h`, the timeout at `a.h` is set.

An attestation always carries a vote at a height (its fields `h`, `T`, `τ`), so steps 3 and 4 need
no test that a height is present. -/
@[no_expose] def record_attestation (Λ : SigningHistory) (a : Attestation V) : SigningHistory := Id.run do
  let mut Λ := Λ
  Λ.sent ← Λ.sent ∪ {a.content}
  if a.finality_pair ≠ none then
    let p := a.finality_pair.value
    Λ.lock[p.hf] ← p.Tf
  if !a.τ && Λ.target[a.h] = none then
    Λ.target[a.h] ← a.T
  if a.τ then
    Λ.timeout[a.h] ← true
  return Λ

/-- The attestation the validator `v` sends, built from its anti-slashing record `Λ`, and the record
after it; `none` in place of the attestation when it sends none. `h_c` and `T_c` are the height of
its source and the root of the block that took the source into that height; `h_j`, `J` and `h_F`
are its source's justification height, the root of its justified block and its finalization
height.

1. The finality pair `fp` (`finality_pair`) and the height pair (`height_pair`, which reads `fp`)
   are computed.
2. If the height pair is empty, no attestation is sent.
3. If the height pair is the vote at the height `h` for `T` (a timeout when `τ` is `true`) and `Λ`
   forbids it (`already_sent`), no attestation is sent.
4. If `fp` is at a height at least `h`, it is dropped: a finality pair is attached only at a height
   less than that of the vote.
5. The attestation of `v` with that vote and `fp` is written into `Λ` (`record_attestation`) and
   returned with the record. -/
@[no_expose] def create_attestation (Λ : SigningHistory) (v : V) (h_c : Height) (T_c : BlockId)
    (h_j : Height) (J : BlockId) (h_F : Height) :
    SigningHistory × Option (Attestation V) := Id.run do
  let mut Λ := Λ
  let mut fp := finality_pair Λ h_j J h_F
  let hp := height_pair Λ (h_c, T_c) fp
  match hp with
  | .empty => return (Λ, none)
  | .vote h T τ =>
    if already_sent Λ h T τ then
      return (Λ, none)
    if fp ≠ none then
      if h ≤ fp.value.hf then
        fp ← none
    let a := Attestation.mk (val_index := v) (h := h) (T := T) (τ := τ) (finality_pair := fp)
    Λ ← record_attestation Λ a
    return (Λ, a)

end Goldilocks
