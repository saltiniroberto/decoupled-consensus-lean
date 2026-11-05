module
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Lemma6
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Lemma7
public import GoldilocksCorrectness.Statements.Routines.LockStatements

@[expose] public section

/-!
# LockStatementsForkChoice, over a model: Lemmas 6 and 7

The fork-choice statements of `GoldilocksCorrectness/Statements/Routines/LockStatements.lean` over a
model `M` whose facts `F` hold: Lemma 6, the anchor of a node state is compatible with a block
every live lock and the fgroot are compatible with (its AC state and frame re-typed on the node
state `n`: the lock entries `n.lockEntries`, the frame `M.fg_to_ac n`); Lemma 7, a start compatible
with a block starts towards it in the model's viable tree. Proved on
`Record/Restated/Proofs/Routines/Lemma6.lean` and `Lemma7.lean`.

The recovery section at the end of the page states each landed theorem again, as the landed
statement (`type_of%`), Lemma 6's at the AC state `n.A` and the frame `fg_to_ac n.S` of a node
state `n`, and proves it from its record form at the spec's model `Model.goldilocks` and its facts
`goldilocksFacts`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Statements.Routines

open Goldilocks
open GoldilocksCorrectness.Record
open GoldilocksCorrectness.Statements.Routines (StartsTowards)

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
    (M.get_anchor n t).compatible R = true :=
  GoldilocksCorrectness.Record.Proofs.Routines.lem6_get_anchor_compatible M F n t R hEntries hRoot

/-- **Lemma 7, a start compatible with a block starts towards it in the viable tree.** A start
`X` compatible with `R` starts towards `R` in the viable tree of `tree`, when `Φ.fc_root` is an
ancestor of `X` or `X`, every block after `X` up to `R` is in `tree`, and `tree` holds a viable
head `W` of the frame that is `R` or a descendant of `R`.

Why: when `R` is `X` or an ancestor of `X`, that is the first case of `StartsTowards`. Otherwise
every block after `X` up to `R` is in the viable tree.

The variables:
- `M`: the model; `F`: its facts;
- `Φ`: the frame; `tree`: the tree whose viable tree is walked;
- `X`: the start; `R`: the block the walk is to reach; `W`: the viable head.

Read aloud: Lemma 7: a start `X` compatible with `R`, with the fgroot `Φ.fc_root` an ancestor of `X`
or `X`, every block after `X` up to `R` in `tree`, and a viable head of `Φ` in `tree` that is `R` or
a descendant of `R`, starts towards `R` in the viable tree of `tree`. -/
theorem lem7_startsTowards_of_compatible (Φ : Frame V) (tree : Finset (Block V))
    (X R W : Block V)
    -- `X` is compatible with `R`
    (hXR : X.compatible R = true)
    -- `Φ.fc_root` is `X` or an ancestor of `X`
    (hRootX : Φ.fc_root.AncestorEq X)
    -- every block after `X` up to `R`, `R` included, is in `tree`
    (hPath : ∀ P : Block V, X.AncestorEq P → P ≠ X → P.AncestorEq R → P ∈ tree)
    -- `W` is a block of `tree` and a viable head of the frame
    (hW : W ∈ tree ∧ W ∈ Φ.viable_heads)
    -- `W` is `R` or a descendant of `R`
    (hRW : R.AncestorEq W) :
    -- then `X` starts towards `R` in the viable tree of `tree`
    StartsTowards X R (M.viable_tree Φ tree) :=
  GoldilocksCorrectness.Record.Proofs.Routines.lem7_startsTowards_of_compatible M F Φ tree X R W hXR
    hRootX hPath hW hRW

end

/-! ## At the spec's model -/

/-- The landed `GoldilocksCorrectness.Statements.Routines.lem6_get_anchor_compatible`, recovered from
its record form at the spec's model, at the AC state `n.A` and the frame `fg_to_ac n.S` of every
node state `n`.

Read aloud: the landed `lem6_get_anchor_compatible` holds at the AC state and the frame of every
node state. -/
theorem lem6_get_anchor_compatible_recovered {V : Type} [DecidableEq V] [Fintype V] [RootOrder] :
    ∀ (n : NodeState V),
      type_of% (@GoldilocksCorrectness.Statements.Routines.lem6_get_anchor_compatible V _ _ n.A
        (fg_to_ac n.S)) := by
  intro n t R hEntries hRoot
  exact lem6_get_anchor_compatible Model.goldilocks goldilocksFacts n t R hEntries hRoot

/-- The landed `GoldilocksCorrectness.Statements.Routines.lem7_startsTowards_of_compatible`,
recovered from its record form at the spec's model.

Read aloud: the landed `lem7_startsTowards_of_compatible` holds, as the record's theorem at the
spec's model. -/
theorem lem7_startsTowards_of_compatible_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Statements.Routines.lem7_startsTowards_of_compatible V _) := by
  exact lem7_startsTowards_of_compatible Model.goldilocks goldilocksFacts

end GoldilocksCorrectness.Record.Statements.Routines
