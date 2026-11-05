module
public import GoldilocksCorrectness.Proofs.Routines.Blocks
public import GoldilocksCorrectness.Proofs.Routines.Kit
import all Goldilocks.AC.ForkChoice
import all Goldilocks.AC.State

@[expose] public section

/-!
# Lemma 6: the anchor is compatible with a block every live lock is compatible with

The proof of `lem6_get_anchor_compatible`, stated in
`GoldilocksCorrectness/Statements/Routines/LockStatements.lean`.
-/

set_option autoImplicit false

open scoped DC

open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks

variable {V : Type} [DecidableEq V] [RootOrder]

/-- **Lemma 6, the anchor is compatible with a block every live lock is compatible with.** The
anchor `get_anchor A Φ t` is compatible with `R`, when the block of every lock entry of `A` live
at `t` is compatible with `R`, and `Φ.fc_root` is compatible with `R`.

Why: the anchor is either `Φ.fc_root`, or a locked block, which is an ancestor of the block of a
live entry, or that block; an ancestor of a block compatible with `R` is compatible with `R`.

The variables:
- `A`: the AC state; `Φ`: the frame; `t`: the time the anchor is read at;
- `R`: the block. -/
theorem lem6_get_anchor_compatible (A : ACState V) (Φ : Frame V) (t : Time) (R : Block V)
    -- the block of every lock entry of `A` live at `t` is compatible with `R`
    (hEntries : ∀ e ∈ A.lock_entries, is_live Φ t e = true → e.B.compatible R = true)
    -- `Φ.fc_root` is compatible with `R`
    (hRoot : Φ.fc_root.compatible R = true) :
    -- then the anchor is compatible with `R`
    (get_anchor A Φ t).compatible R = true := by
  simp only [get_anchor, Id.run]
  generalize hD : Block.deepest? {B ∈ viable_tree Φ Φ.tree | is_locked A Φ t B} = D
  cases D with
  | none => exact hRoot
  | some B =>
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, dite_true, Option.value, Option.get_some]
    have hmem := deepest?_mem hD
    rw [Finset.mem_filter] at hmem
    have hlocked := hmem.2
    simp only [is_locked, decide_eq_true_eq] at hlocked
    obtain ⟨e, he, hlive, hBe⟩ := hlocked
    exact compatible_of_ancestorEq_compatible hBe (hEntries e he hlive)

end GoldilocksCorrectness.Proofs.Routines
