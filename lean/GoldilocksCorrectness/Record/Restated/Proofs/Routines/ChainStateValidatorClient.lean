module
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Record

@[expose] public section

/-!
# ChainStateValidatorClient, over a model

The validator-client theorem of `GoldilocksCorrectness/Proofs/Routines/ChainState.lean`
over a model `M` whose facts `F` hold: a vote `height_pair` computes is at the source's
height and names the source's root. (The page's chain-state theorems are restated on
`Record/Restated/Proofs/Routines/ChainState.lean`.)

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

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded in the goal and in every
hypothesis: `omega` does not see a fact stated at either. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

variable {V : Type} [DecidableEq V] [Fintype V]

section

variable (M : GoldilocksModel V) (F : Facts M)
include M F

/-- A height pair `height_pair` computes from a source with the height `h_c` and the root `T_c`
that is a vote is at the height `h_c` and names `T_c`.

The variables:
- `M`: the model; `F`: its facts;
- `n`: the node state; `h_c`, `T_c`: the source's height and root; `fp`: the finality pair;
- `h`, `T`, `τ`: the vote.

Read aloud: a vote `height_pair` computes from the source `(h_c, T_c)` is at `h_c` for `T_c`. -/
theorem height_pair_vote {n : M.N} {h_c : Height} {T_c : BlockId}
    {fp : Option FinalityPair} {h : Height} {T : BlockId} {τ : Bool}
    (hp : M.height_pair n (some (h_c, T_c)) fp = .vote h T τ) :
    h = h_c ∧ T = T_c := by
  exact ⟨(height_pair_vote_cases M F hp).1, (height_pair_vote_cases M F hp).2.1⟩

end

/-! ## At the spec's model -/

/-- The landed `GoldilocksCorrectness.Proofs.Routines.height_pair_vote`,
recovered from its record form at the spec's model, at
the anti-slashing record `n.Λ` of every node state `n`.

Read aloud: the landed `height_pair_vote` holds at the anti-slashing record `n.Λ` of every node state `n`, as the record's theorem at the
spec's model. -/
theorem height_pair_vote_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (n : NodeState V), type_of% (@GoldilocksCorrectness.Proofs.Routines.height_pair_vote n.Λ) := by
  intro n
  exact height_pair_vote (n := n) Model.goldilocks goldilocksFacts

end GoldilocksCorrectness.Record.Proofs.Routines
