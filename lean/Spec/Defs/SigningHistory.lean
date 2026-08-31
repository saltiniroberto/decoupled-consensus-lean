import Spec.Defs.Model

/-!
# The anti-slashing record `Λ`

The durable per-height memory behind the attestation rules:
`Λ = (target[·], timeout[·], lock[·])`, one entry per height, initially `(⊥, false, ⊥)`.
`08_FinalityVote.lean` holds the client rules that read it and the one routine that writes
it, `record_attestation`. The store holds one as its field `Σ.history` (`Store.lean`) —
the protocol keeps `Λ` beside the store rather than inside it, but this rendering's store
is one validator's whole state, so the record rides along; nothing else reads or writes it.
-/

set_option autoImplicit false

namespace DC

variable [BlockIds]

/-- The record `Λ`: per height, the first named target signed there, whether an
    empty-target vote was signed there, and the lock — the target of a finality pair
    signed there. `record_attestation` (`08_FinalityVote.lean`) is its only writer. -/
structure SigningHistory [BlockIds] where
  /-- `Λ.target[h]`: the first named target signed at height `h`, by identifier. -/
  target : (h : Nat) → Option BlockId
  /-- `Λ.timeout[h]`: an empty-target vote `(h, ⊥)` was signed at height `h`. -/
  timeout : (h : Nat) → Bool
  /-- `Λ.lock[h]`: the target of a finality pair signed at height `h`, by identifier. -/
  lock : (h : Nat) → Option BlockId

/-- The record of a validator that has signed nothing anywhere: every entry `(⊥, false, ⊥)`. -/
def SigningHistory.gen : SigningHistory where
  target _ := ⊥
  timeout _ := false
  lock _ := ⊥

end DC
