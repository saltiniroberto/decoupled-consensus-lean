module
public import GoldilocksCorrectness.Record.Facts
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.RecordDefs

@[expose] public section

/-!
# AccountableValidatorClient, over a model

The validator-client theorem of `GoldilocksCorrectness/Proofs/Routines/Accountable.lean`
over a model `M` whose facts `F` hold: a consistent anti-slashing record forbids the
slashing conditions. (The page's other theorems are restated on
`Record/Restated/Proofs/Routines/Accountable.lean`, `AccountableFGState.lean` and
`AccountableChains.lean`.)

The recovery section at the end of the page states each landed theorem again, as the
landed statement (`type_of%`), and proves it from its record form at the spec's model
`Model.goldilocks` and its facts `goldilocksFacts`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Record
open GoldilocksCorrectness.Record.Statements.Routines (RecordConsistent
  goldilocks_RecordConsistent)
open GoldilocksCorrectness.Statements.Routines (E1 E2)

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded in the goal and in every
hypothesis: `omega` does not see a fact stated at either. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

variable {V : Type} [DecidableEq V] [Fintype V]

section

variable (M : GoldilocksModel V) (F : Facts M)
include M F

/-- Two attestations whose contents a consistent anti-slashing record holds form no E1 and no E2
pair.

The variables:
- `M`: the model; `F`: its facts;
- `n`: the node state; `a`, `a'`: the two attestations.

Read aloud: two attestations whose contents a consistent record holds form no E1 and no E2 pair. -/
theorem no_slashable_of_consistent (n : M.N) (hΛ : RecordConsistent M n)
    (a a' : Attestation V)
    -- the record holds the content of `a`
    (ha : a.content ∈ n.sentAttestations)
    -- the record holds the content of `a'`
    (ha' : a'.content ∈ n.sentAttestations) :
    ¬ E1 a a' ∧ ¬ E2 a a' := by
  refine ⟨?_, ?_⟩
  · rintro ⟨p, hp, hh, hT⟩
    exact hT (hΛ.lockKept a.content ha p hp a'.content ha' hh)
  · rintro ⟨hh, hτ, hτ', hT⟩
    exact hT (hΛ.oneTarget a.content ha a'.content ha' hh hτ hτ')

end

/-! ## At the spec's model -/

/-- The landed `GoldilocksCorrectness.Proofs.Routines.no_slashable_of_consistent`,
recovered from its record form at the spec's model, at
the anti-slashing record `n.Λ` of every node state `n`.

Read aloud: the landed `no_slashable_of_consistent` holds at the anti-slashing record `n.Λ` of every node state `n`, as the record's theorem at the
spec's model. -/
theorem no_slashable_of_consistent_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (n : NodeState V), type_of% (@GoldilocksCorrectness.Proofs.Routines.no_slashable_of_consistent V n.Λ) := by
  intro n
  simp only [goldilocks_RecordConsistent (V := V)]
  exact no_slashable_of_consistent Model.goldilocks goldilocksFacts n

end GoldilocksCorrectness.Record.Proofs.Routines
