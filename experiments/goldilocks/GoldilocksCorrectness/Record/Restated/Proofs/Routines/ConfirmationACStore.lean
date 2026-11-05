module
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ACStore
public import GoldilocksCorrectness.Proofs.Routines.Confirmation

@[expose] public section

/-!
# ConfirmationACStore, over a model

The theorem of `GoldilocksCorrectness/Proofs/Routines/Confirmation.lean` on the reader
`live_lock_vetoes`, over a model `M` whose facts `F` hold: no live lock entry vetoes a block
compatible with the block of every live entry. (The page's theorems on the resolution time
`tau` are restated with the tick's family.)

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
open GoldilocksCorrectness.Proofs.Routines (conflicts_iff)

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded in the goal and in every
hypothesis: `omega` does not see a fact stated at either. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

variable {V : Type} [DecidableEq V] [Fintype V]

section

variable (M : GoldilocksModel V) (F : Facts M)
include M F

/-- No live lock entry vetoes `B` when the block of every live entry is compatible with `B`.

The variables:
- `M`: the model; `F`: its facts;
- `n`: the node state; `t`: the time; `B`: the block.

Read aloud: no live lock entry vetoes `B` when the block of every live entry is compatible with `B`. -/
theorem live_lock_vetoes_eq_false {n : M.N} {t : Time} {B : Block V}
    -- the block of every lock entry of `n` live at `t` is compatible with `B`
    (h : ∀ e ∈ n.lockEntries, M.is_live n t e = true → e.B.compatible B = true) :
    M.live_lock_vetoes n t B = false := by
  simp only [F.rd.live_lock_vetoes_eq, decide_eq_false_iff_not, not_exists, not_and]
  intro e he hlive hconf
  exact ((conflicts_iff _ _).1 hconf) (h e he hlive)

end

/-! ## At the spec's model -/

/-- The landed `GoldilocksCorrectness.Proofs.Routines.live_lock_vetoes_eq_false`,
recovered from its record form at the spec's model, at
the AC state `n.A` and the record `fg_to_ac n.S` of every node state `n`.

Read aloud: the landed `live_lock_vetoes_eq_false` holds at the AC state `n.A` and the record `fg_to_ac n.S` of every node state `n`, as the record's theorem at the
spec's model. -/
theorem live_lock_vetoes_eq_false_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (n : NodeState V), type_of% (@GoldilocksCorrectness.Proofs.Routines.live_lock_vetoes_eq_false V _ n.A (fg_to_ac n.S)) := by
  intro n
  exact live_lock_vetoes_eq_false (n := n) Model.goldilocks goldilocksFacts

end GoldilocksCorrectness.Record.Proofs.Routines
