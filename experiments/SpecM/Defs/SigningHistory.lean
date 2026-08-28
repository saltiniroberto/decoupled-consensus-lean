import SpecM.Defs.Model

/-!
# The signing record

The durable per-height memory behind the attestation rules: `08_FinalityVote.lean` holds
the rules that fill the pairs a validator signs, and this record is what those rules read
and write. The store holds one as its field `Σ.history` (`Store.lean`), because the store is
one validator's state and the rules are store rules.
-/

set_option autoImplicit false

namespace DC

variable {Validator : Type} [Roots]

/-- The durable signing record a validator keeps per height: whether it signed an
    empty-target vote at `h`, the first named target it signed at `h`, and the target of
    the first finality pair it signed at `h`. Only the *first* signing of each kind at a
    height is remembered — the rules in `08_FinalityVote.lean` repeat what the record holds,
    and they write it into the store they return before the signature is released. -/
structure SigningHistory (Validator : Type) [Roots] where
  /-- An empty-target vote `(h, ⊥)` was signed at height `h`. -/
  signedEmptyTarget : (h : Nat) → Bool
  /-- The first named target signed at height `h`. -/
  firstTarget : (h : Nat) → Option (Block Validator)
  /-- The target in the first finality pair signed at height `h`. -/
  finalityTarget : (h : Nat) → Option (Block Validator)

/-- The record of a validator that has signed nothing anywhere: every validator's start. -/
def SigningHistory.gen : SigningHistory Validator where
  signedEmptyTarget _ := false
  firstTarget _ := ⊥
  finalityTarget _ := ⊥

/-- The durable write behind signing an empty-target vote `(h, ⊥)`. -/
def SigningHistory.saveEmptyTarget (H : SigningHistory Validator) (h : Nat) :
    SigningHistory Validator :=
  { H with signedEmptyTarget := Function.update H.signedEmptyTarget h true }

/-- The durable write behind signing a first named target `(h, T)`. -/
def SigningHistory.saveTarget (H : SigningHistory Validator) (h : Nat)
    (T : Block Validator) : SigningHistory Validator :=
  { H with firstTarget := Function.update H.firstTarget h (some T) }

/-- The durable write behind a finality pair's first release: record `J` as the
    height-`h` finality target. -/
def SigningHistory.saveFinalityTarget (H : SigningHistory Validator) (h : Nat)
    (J : Block Validator) : SigningHistory Validator :=
  { H with finalityTarget := Function.update H.finalityTarget h (some J) }

end DC
