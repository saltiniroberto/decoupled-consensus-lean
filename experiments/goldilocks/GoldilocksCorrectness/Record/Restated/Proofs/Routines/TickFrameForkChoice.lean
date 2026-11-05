module
public import GoldilocksCorrectness.Record.Facts
public import GoldilocksCorrectness.Proofs.Routines.TickFrame

@[expose] public section

/-!
# TickFrame, over a model: the fgroot is the anchor or an ancestor of it

The theorem `fc_root_ancestorEq_get_anchor` of `GoldilocksCorrectness/Proofs/Routines/TickFrame.lean`
over a model `M` whose facts `F` hold: the fgroot of a node state is its anchor or an ancestor of
it. The landed theorem reads an AC state `A` and a frame `Φ`; the record's anchor reads the node
state, so both are re-typed on `n`: `Φ` is the node's own frame `M.fg_to_ac n`. The page's other
reader theorems are on `Record/Restated/Proofs/Routines/TickFrameACStore.lean` and
`TickFrameDefs.lean`.

The recovery section at the end of the page states the landed theorem again, as the landed
statement (`type_of%`) at the AC state `n.A` and the frame `fg_to_ac n.S` of a node state `n`, and
proves it from its record form at the spec's model `Model.goldilocks` and its facts
`goldilocksFacts`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Record
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl deepest?_mem)

variable {V : Type} [DecidableEq V] [Fintype V]

section

variable (M : GoldilocksModel V) (F : Facts M)
include M F

/-- The anchor of every walk is the fgroot `(M.fg_to_ac n).fc_root` or a descendant of it: it is
the fgroot, or a block of the viable tree, every block of which is the fgroot or a descendant of it.

The variables:
- `M`: the model; `F`: its facts;
- `n`: the node state; `t`: the time the anchor is read at.

Read aloud: the fgroot of `n` is the anchor or an ancestor of it. -/
theorem fc_root_ancestorEq_get_anchor [RootOrder] (n : M.N) (t : Time) :
    (M.fg_to_ac n).fc_root.AncestorEq (M.get_anchor n t) := by
  rw [F.rd.get_anchor_eq]
  generalize hD : Block.deepest? {B ∈ M.viable_tree (M.fg_to_ac n) (M.fg_to_ac n).tree |
    M.is_locked n t B = true} = D
  cases D with
  | none => exact ancestorEq_refl _
  | some B =>
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, dite_true, Option.value, Option.get_some]
    have hmem := deepest?_mem hD
    simp only [Finset.mem_filter, F.rd.viable_tree_eq, Bool.and_eq_true] at hmem
    exact hmem.1.2.1

end

/-! ## At the spec's model -/

/-- The landed `GoldilocksCorrectness.Proofs.Routines.fc_root_ancestorEq_get_anchor`, recovered from
its record form at the spec's model, at the AC state `n.A` and the frame `fg_to_ac n.S` of every
node state `n`.

Read aloud: the landed `fc_root_ancestorEq_get_anchor` holds at the AC state and the frame of every
node state. -/
theorem fc_root_ancestorEq_get_anchor_recovered {V : Type} [DecidableEq V] [Fintype V] [RootOrder] :
    ∀ (n : NodeState V),
      type_of% (@GoldilocksCorrectness.Proofs.Routines.fc_root_ancestorEq_get_anchor V _ _ n.A
        (fg_to_ac n.S)) := by
  intro n t
  exact fc_root_ancestorEq_get_anchor Model.goldilocks goldilocksFacts n t

end GoldilocksCorrectness.Record.Proofs.Routines
