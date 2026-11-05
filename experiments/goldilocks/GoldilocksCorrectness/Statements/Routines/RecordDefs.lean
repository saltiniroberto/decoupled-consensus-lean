module
public import Goldilocks

@[expose] public section

/-!
# The vocabulary of the statements about the anti-slashing record

One definition the statements about the validator client read (`RecordStatements.lean`):

- `RecordConsistent Λ`, the anti-slashing record `Λ` is consistent: its three arrays say exactly
  what the contents it holds say, those contents carry no two targets at a height for different
  blocks and no vote against a finality pair, and no height holds both a timeout and a lock.


-/

set_option autoImplicit false

open scoped DC

namespace GoldilocksCorrectness.Statements.Routines

open Goldilocks

/-- `RecordConsistent Λ`: the anti-slashing record `Λ` is consistent.

The variables:
- `Λ`: the anti-slashing record, with its arrays `target`, `timeout`, `lock` and the set `sent` of
  the contents of the attestations sent.

Read aloud: the record's three arrays say exactly what the contents it holds say, and those
contents carry no two targets at a height for different blocks and no vote against a finality
pair; and no height holds both a timeout and a lock. -/
structure RecordConsistent (Λ : SigningHistory) : Prop where
  /-- Two target contents at one height name one block. -/
  oneTarget : ∀ c ∈ Λ.sent, ∀ c' ∈ Λ.sent, c.h = c'.h → c.τ = false → c'.τ = false → c.T = c'.T
  /-- Every content at the height of a finality pair the record sent names that pair's block. -/
  lockKept : ∀ c ∈ Λ.sent, ∀ p : FinalityPair, c.finality_pair = some p →
    ∀ c' ∈ Λ.sent, c'.h = p.hf → c'.T = p.Tf
  /-- `target h` is set exactly when a target content at `h` was sent, and to its block. -/
  targetRec : ∀ (h : Height) (T : BlockId),
    Λ.target h = some T ↔ ∃ c ∈ Λ.sent, c.h = h ∧ c.τ = false ∧ c.T = T
  /-- `timeout h` is set exactly when a timeout content at `h` was sent. -/
  timeoutRec : ∀ h : Height, Λ.timeout h = true ↔ ∃ c ∈ Λ.sent, c.h = h ∧ c.τ = true
  /-- `lock h` is set exactly when a content with a finality pair at `h` was sent, and to its
  block. -/
  lockRec : ∀ (h : Height) (T : BlockId),
    Λ.lock h = some T ↔ ∃ c ∈ Λ.sent, c.finality_pair = some ⟨h, T⟩
  /-- A height where the record holds a timeout holds no lock. -/
  timeoutUnlocked : ∀ h : Height, Λ.timeout h = true → Λ.lock h = none

end GoldilocksCorrectness.Statements.Routines
