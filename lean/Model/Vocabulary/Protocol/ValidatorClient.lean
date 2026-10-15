module
public import Model.Vocabulary.Protocol.ForkChoice.Goldfish
public import Model.Vocabulary.Objects.NamedBlocks

@[expose] public section

/-!
# The validator record and attestations

The anti-slashing record `Λ`, the finality-pair and height-pair rules, and the creation of a
combined attestation.
-/

section
/-! ## Attestation pair rules -/

namespace DecoupledConsensusModel
namespace Protocol

open Protocol (ChainState HeightConfig)

/-! ## The anti-slashing record -/

/-- The anti-slashing record `Λ`: for every height, the validator's first target, whether it emitted
    an empty-target vote, and the target of its first finality pair. -/
structure Record where
  /-- `Λ.target[h]`: the validator's first target at height `h`. -/
  target : Height → Option BlockId
  /-- `Λ.timeout[h]`: whether it emitted an empty-target vote at height `h`. -/
  timeout : Height → Bool
  /-- `Λ.lock[h]`: the target of its first finality pair at height `h`. -/
  lock : Height → Option BlockId

namespace Record

/-- The initial record: `(⊥, false, ⊥)` at every height. -/
def initial : Record where
  target := fun _ => none
  timeout := fun _ => false
  lock := fun _ => none

/-- `Λ.target[h] ← T`. -/
def with_target (Λ : Record) (h : Height) (T : BlockId) : Record :=
  { Λ with target := fun k => if k = h then some T else Λ.target k }

/-- `Λ.timeout[h] ← true`. -/
def with_timeout (Λ : Record) (h : Height) : Record :=
  { Λ with timeout := fun k => if k = h then true else Λ.timeout k }

/-- `Λ.lock[h] ← J`. -/
def with_lock (Λ : Record) (h : Height) (J : BlockId) : Record :=
  { Λ with lock := fun k => if k = h then some J else Λ.lock k }

end Record

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The pair rules -/

/-- `finality_pair(Λ, h_j, J, h_F)`: the pair `(h_j, J)` when `h_F < h_j`, the record's target at
    `h_j` is empty or `J`, no timeout is recorded at `h_j`, and the lock at `h_j` is empty or `J`;
    the empty pair otherwise. -/
def finality_pair (Λ : Record) (h_j : Height) (J : BlockId) (h_F : Height) :
    Option FinalityPair :=
  if h_F < h_j then
    if (Λ.target h_j = none ∨ Λ.target h_j = some J) ∧
        Λ.timeout h_j = false ∧
        (Λ.lock h_j = none ∨ Λ.lock h_j = some J) then
      some ⟨h_j, J⟩
    else
      none
  else
    none

/-- The lock `height_pair` reads at `h_c`: this attestation's own finality target when its height is
    `h_c`, the record's lock otherwise. -/
def own_lock (Λ : Record) (h_c : Height) (fp : Option FinalityPair) :
    Option BlockId :=
  match fp with
  | some p => if p.height = h_c then some p.target else Λ.lock h_c
  | none => Λ.lock h_c

/-- `height_pair(Λ, fields, fp)`: the empty pair without height fields. For fields `(h_c, T_c, ν)`:
    a timeout at `h_c` when one is recorded; else, when `own_lock` gives a lock, the target vote
    `(h_c, T_c)` if it is `T_c` and the empty pair otherwise; else, when a target is recorded, the
    target vote if it is `T_c` and a timeout otherwise; else a timeout when `ν` holds and the target
    vote otherwise. -/
def height_pair (Λ : Record) (fields : Option (Height × BlockId × Bool))
    (fp : Option FinalityPair) : HeightPair :=
  match fields with
  | none => .empty
  | some (h_c, T_c, ν) =>
    if Λ.timeout h_c then
      .timeout h_c
    else
      match own_lock Λ h_c fp with
      | some locked => if locked = T_c then .target h_c T_c else .empty
      | none =>
        match Λ.target h_c with
        | some recorded => if recorded = T_c then .target h_c T_c else .timeout h_c
        | none => if ν then .timeout h_c else .target h_c T_c

/-- `record_attestation(Λ, a)`: records `a`'s finality pair as the lock at its height, then records
    `a`'s timeout, or its target when none is recorded at that height. -/
def record_attestation (Λ : Record) (a : CombinedAttestation V) : Record :=
  let afterLock :=
    match a.finality_pair with
    | some p => Λ.with_lock p.height p.target
    | none => Λ
  match a.height_pair with
  | .empty => afterLock
  | .timeout h => afterLock.with_timeout h
  | .target h T => if afterLock.target h = none then afterLock.with_target h T else afterLock

/-- `create_attestation`: build the finality pair, then the height pair, then the attestation, and
    record it; returns the updated record and the attestation. -/
def create_attestation (Λ : Record) (val_index : V) (r : Round)
    (confirmed : Option BlockId) (fields : Option (Height × BlockId × Bool))
    (h_j : Height) (J : BlockId) (h_F : Height) :
    Record × CombinedAttestation V :=
  let fp := finality_pair Λ h_j J h_F
  let hp := height_pair Λ fields fp
  let a : CombinedAttestation V := ⟨val_index, r, confirmed, hp, fp⟩
  (record_attestation Λ a, a)

end Protocol
end DecoupledConsensusModel
end

section
/-! ## The named signing record -/
namespace DecoupledConsensusModel.Protocol

structure NamedRecord where
  legacy : Record
  timeoutHistory : Finset (Height × BlockId)

namespace NamedRecord

/-- The inputs of the signing client. -/
structure Input (V : Type) where
  val_index : V
  round : Round
  confirmed : Option BlockId
  fields : Option (Height × BlockId × Bool)
  h_j : Height
  J : BlockId
  h_F : Height

def initial : NamedRecord := ⟨Record.initial, ∅⟩

/-- The named height pair of a height pair built from `fields`: a target vote or a timeout carries
    the height and entry block of `fields`. -/
def encodeHeight (fields : Option (Height × BlockId × Bool))
    (pair : HeightPair) : NamedHeightPair :=
  match pair, fields with
  | .empty, _ => .empty
  | .target _ _, some (h, entry, _) => .vote h entry false
  | .timeout _, some (h, entry, _) => .vote h entry true
  | _, none => .empty

def encodeRow {V : Type} (fields : Option (Height × BlockId × Bool))
    (row : CombinedAttestation V) : NamedAttestation V :=
  ⟨row.val_index, row.round, row.confirmed, encodeHeight fields row.height_pair,
    row.finality_pair⟩

/-- Adds a timeout vote's height and entry to the timeout history; other pairs leave it unchanged. -/
def rememberTimeout (history : Finset (Height × BlockId)) : NamedHeightPair →
    Finset (Height × BlockId)
  | .vote h entry true => insert (h, entry) history
  | _ => history

def legacyCreate {V : Type} (record : Record) (input : Input V) :
    Record × CombinedAttestation V :=
  create_attestation record input.val_index input.round input.confirmed input.fields
    input.h_j input.J input.h_F

/-- The signing client on a named record: `create_attestation` on the record, its attestation
    encoded as a named attestation, and its timeout, if any, added to the timeout history. -/
def create {V : Type} (record : NamedRecord) (input : Input V) :
    NamedRecord × NamedAttestation V :=
  let old := legacyCreate record.legacy input
  let row := encodeRow input.fields old.2
  (⟨old.1, rememberTimeout record.timeoutHistory row.height_pair⟩, row)

end NamedRecord
end DecoupledConsensusModel.Protocol
end

end
