module
public import GoldilocksCorrectness.Record.Facts
public import GoldilocksCorrectness.Proofs.Routines.Lemma6

@[expose] public section

/-!
# Lemma 6, over a model

The theorem of `GoldilocksCorrectness/Proofs/Routines/Lemma6.lean` over a model `M` whose facts `F`
hold: the anchor `M.get_anchor n t` of a node state `n` is compatible with a block every live lock
of `n` and the fgroot of `n` are compatible with. The landed theorem reads an AC state `A` and a
frame `Φ`; the record's anchor reads the node state, so both are re-typed on `n`: `A`'s lock
entries are `n.lockEntries` and `Φ` is the node's own frame `M.fg_to_ac n`.

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
open GoldilocksCorrectness.Proofs.Routines (compatible_of_ancestorEq_compatible deepest?_mem)

variable {V : Type} [DecidableEq V] [Fintype V]

section

variable (M : GoldilocksModel V) (F : Facts M)
include M F

/-- **Lemma 6, the anchor is compatible with a block every live lock is compatible with.** The
anchor `M.get_anchor n t` is compatible with `R`, when the block of every lock entry of `n` live at
`t` is compatible with `R`, and the fgroot `(M.fg_to_ac n).fc_root` is compatible with `R`.

Why: the anchor is either the fgroot, or a locked block, which is an ancestor of the block of a
live entry, or that block; an ancestor of a block compatible with `R` is compatible with `R`.

The variables:
- `M`: the model; `F`: its facts;
- `n`: the node state; `t`: the time the anchor is read at; `R`: the block.

Read aloud: Lemma 6: the anchor at `t` is compatible with `R` when the block of every lock entry of
`n` live at `t` and the fgroot of `n` are. -/
theorem lem6_get_anchor_compatible [RootOrder] (n : M.N) (t : Time) (R : Block V)
    -- the block of every lock entry of `n` live at `t` is compatible with `R`
    (hEntries : ∀ e ∈ n.lockEntries, M.is_live n t e = true → e.B.compatible R = true)
    -- the fgroot of `n` is compatible with `R`
    (hRoot : (M.fg_to_ac n).fc_root.compatible R = true) :
    -- then the anchor is compatible with `R`
    (M.get_anchor n t).compatible R = true := by
  rw [F.rd.get_anchor_eq]
  generalize hD : Block.deepest? {B ∈ M.viable_tree (M.fg_to_ac n) (M.fg_to_ac n).tree |
    M.is_locked n t B = true} = D
  cases D with
  | none => exact hRoot
  | some B =>
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, dite_true, Option.value, Option.get_some]
    have hmem := deepest?_mem hD
    rw [Finset.mem_filter] at hmem
    have hlocked := hmem.2
    rw [F.rd.is_locked_eq, decide_eq_true_eq] at hlocked
    obtain ⟨e, he, hlive, hBe⟩ := hlocked
    exact compatible_of_ancestorEq_compatible hBe (hEntries e he hlive)

end

/-! ## At the spec's model -/

/-- The landed `GoldilocksCorrectness.Proofs.Routines.lem6_get_anchor_compatible`, recovered from its
record form at the spec's model, at the AC state `n.A` and the frame `fg_to_ac n.S` of every node
state `n`.

Read aloud: the landed `lem6_get_anchor_compatible` holds at the AC state and the frame of every
node state. -/
theorem lem6_get_anchor_compatible_recovered {V : Type} [DecidableEq V] [Fintype V] [RootOrder] :
    ∀ (n : NodeState V),
      type_of% (@GoldilocksCorrectness.Proofs.Routines.lem6_get_anchor_compatible V _ _ n.A
        (fg_to_ac n.S)) := by
  intro n t R hEntries hRoot
  exact lem6_get_anchor_compatible Model.goldilocks goldilocksFacts n t R hEntries hRoot

end GoldilocksCorrectness.Record.Proofs.Routines
