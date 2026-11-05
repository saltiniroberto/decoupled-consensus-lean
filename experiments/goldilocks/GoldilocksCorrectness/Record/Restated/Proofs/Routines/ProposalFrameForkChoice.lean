module
public import GoldilocksCorrectness.Record.Facts
public import GoldilocksCorrectness.Proofs.Routines.ProposalFrame

@[expose] public section

/-!
# ProposalFrame, over a model: the anchor and the live lock entries

The theorem `get_anchor_ancestorEq_of_entries` of
`GoldilocksCorrectness/Proofs/Routines/ProposalFrame.lean` over a model `M` whose facts `F` hold:
the anchor of a node state is a block `X` or an ancestor of it when every live lock entry's block and
the fgroot are. The landed theorem reads an AC state `A` and a frame `Φ`; the record's anchor reads
the node state, so both are re-typed on `n`: `A`'s lock entries are `n.lockEntries` and `Φ` is the
node's own frame `M.fg_to_ac n`. The page's two theorems about the Goldfish eligibility test read
no member of the record and are not restated.

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
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_trans deepest?_mem)

variable {V : Type} [DecidableEq V] [Fintype V]

section

variable (M : GoldilocksModel V) (F : Facts M)
include M F

/-- The anchor read at `t` is `X` or an ancestor of `X` when the block of every lock entry of `n`
live at `t` is `X` or an ancestor of `X`, and the fgroot `(M.fg_to_ac n).fc_root` is `X` or an
ancestor of `X`.

Why: the anchor is either the fgroot, or a locked block, which is the block of a live entry or an
ancestor of it.

The variables:
- `M`: the model; `F`: its facts;
- `n`: the node state; `t`: the time the anchor is read at; `X`: the block.

Read aloud: with no live lock past `X` and the fork choice rooted at `X` or before it, the anchor
is `X` or an ancestor of `X`. -/
theorem get_anchor_ancestorEq_of_entries [RootOrder] (n : M.N) (t : Time) (X : Block V)
    (hEntries : ∀ e ∈ n.lockEntries, M.is_live n t e = true → e.B.AncestorEq X)
    (hRoot : (M.fg_to_ac n).fc_root.AncestorEq X) :
    (M.get_anchor n t).AncestorEq X := by
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
    exact ancestorEq_trans hBe (hEntries e he hlive)

end

/-! ## At the spec's model -/

/-- The landed `GoldilocksCorrectness.Proofs.Routines.get_anchor_ancestorEq_of_entries`, recovered
from its record form at the spec's model, at the AC state `n.A` and the frame `fg_to_ac n.S` of
every node state `n`.

Read aloud: the landed `get_anchor_ancestorEq_of_entries` holds at the AC state and the frame of
every node state. -/
theorem get_anchor_ancestorEq_of_entries_recovered {V : Type} [DecidableEq V] [Fintype V]
    [RootOrder] :
    ∀ (n : NodeState V),
      type_of% (@GoldilocksCorrectness.Proofs.Routines.get_anchor_ancestorEq_of_entries V _ _ n.A
        (fg_to_ac n.S)) := by
  intro n t X hEntries hRoot
  exact get_anchor_ancestorEq_of_entries Model.goldilocks goldilocksFacts n t X hEntries hRoot

end GoldilocksCorrectness.Record.Proofs.Routines
