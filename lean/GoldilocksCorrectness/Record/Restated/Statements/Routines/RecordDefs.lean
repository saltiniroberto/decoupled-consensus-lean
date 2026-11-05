module
public import GoldilocksCorrectness.Record.ModelSpellings
public import GoldilocksCorrectness.Record.ModelGoldilocks
public import GoldilocksCorrectness.Statements.Routines.RecordDefs

@[expose] public section

/-!
# The consistency of a node's anti-slashing record, over a model

The structure `RecordConsistent` of `GoldilocksCorrectness/Statements/Routines/RecordDefs.lean`
over a model `M`, a condition on a node state `n : M.N` read through the readers of its
anti-slashing record: `n.sentTarget`, `n.sentTimeout`, `n.sentLock` and `n.sentAttestations`. At
the spec's model it is the landed structure applied to the node's anti-slashing record (the equation
`goldilocks_RecordConsistent`, in the simp set `record_goldilocks`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Statements.Routines

open Goldilocks
open GoldilocksCorrectness.Record

variable {V : Type} [DecidableEq V] [Fintype V]

/-- `RecordConsistent M n`: the anti-slashing record of the node state `n` is consistent.

The variables:
- `M`: the model;
- `n`: the node state, with the readers `n.sentTarget`, `n.sentTimeout`, `n.sentLock` and the set
  `n.sentAttestations` of the contents of the attestations it has sent.

Read aloud: the record's three readers say exactly what the contents the node has sent say, and
those contents carry no two targets at a height for different blocks and no vote against a finality
pair; and no height holds both a timeout and a lock. -/
structure RecordConsistent (M : GoldilocksModel V) (n : M.N) : Prop where
  /-- Two target contents at one height name one block. -/
  oneTarget : ∀ c ∈ n.sentAttestations, ∀ c' ∈ n.sentAttestations, c.h = c'.h → c.τ = false →
    c'.τ = false → c.T = c'.T
  /-- Every content at the height of a finality pair the node sent names that pair's block. -/
  lockKept : ∀ c ∈ n.sentAttestations, ∀ p : FinalityPair, c.finality_pair = some p →
    ∀ c' ∈ n.sentAttestations, c'.h = p.hf → c'.T = p.Tf
  /-- `n.sentTarget h` is set exactly when a target content at `h` was sent, and to its block. -/
  targetRec : ∀ (h : Height) (T : BlockId),
    n.sentTarget h = some T ↔ ∃ c ∈ n.sentAttestations, c.h = h ∧ c.τ = false ∧ c.T = T
  /-- `n.sentTimeout h` is set exactly when a timeout content at `h` was sent. -/
  timeoutRec : ∀ h : Height, n.sentTimeout h = true ↔ ∃ c ∈ n.sentAttestations, c.h = h ∧ c.τ = true
  /-- `n.sentLock h` is set exactly when a content with a finality pair at `h` was sent, and to its
  block. -/
  lockRec : ∀ (h : Height) (T : BlockId),
    n.sentLock h = some T ↔ ∃ c ∈ n.sentAttestations, c.finality_pair = some ⟨h, T⟩
  /-- A height where the node's record holds a timeout holds no lock. -/
  timeoutUnlocked : ∀ h : Height, n.sentTimeout h = true → n.sentLock h = none

/-! ## At the spec's model -/

/-- At the spec's model, a consistent record is a record the landed `RecordConsistent` calls
consistent.

The variables:
- `n`: the node state.

Read aloud: the spec's model has the spec's consistent records. -/
@[record_goldilocks]
theorem goldilocks_RecordConsistent (n : NodeState V) :
    GoldilocksCorrectness.Statements.Routines.RecordConsistent n.Λ =
      RecordConsistent (Model.goldilocks (V := V)) n := by
  apply propext
  constructor
  · intro h
    exact ⟨h.1, h.2, h.3, h.4, h.5, h.6⟩
  · intro h
    exact ⟨h.1, h.2, h.3, h.4, h.5, h.6⟩

end GoldilocksCorrectness.Record.Statements.Routines
