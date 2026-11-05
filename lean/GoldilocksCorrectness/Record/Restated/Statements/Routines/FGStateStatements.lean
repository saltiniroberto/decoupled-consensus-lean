module
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.FGStateReadersContest
public import GoldilocksCorrectness.Statements.Routines.FGStateStatements

@[expose] public section

/-!
# FGStateStatements, over a model

The statements of `GoldilocksCorrectness/Statements/Routines/FGStateStatements.lean` over a model
`M` whose facts `F` hold: a contested node state is one height past its justification, and, under
the conditions of `not_contested_or_two_past`, a contested node state is justified past the block
`B`. Each is stated for a node state `n` satisfying the model's node invariant
`M.nodeInv C P X n`, with `hMax M C n` for the stored greatest height and `M.chainStateOf C B` for
the stored chain state of a block; the landed hypothesis that the stored chain states are the
blocks' own is dropped (over the record it always holds).

The recovery section at the end of the page states each landed theorem again, as the landed
statement (`type_of%`) at the FG state `n.S` of a node state `n` satisfying the spec's model's node
invariant, and proves it from its record form at the spec's model `Model.goldilocks` and its facts
`goldilocksFacts`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Statements.Routines

open Goldilocks
open GoldilocksCorrectness.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section

variable (M : GoldilocksModel V) (F : Facts M)
include M F

/-- **A contested node state is one height past its justification.** When `M.fg_contest n`, then
`hMax M C n = n.justifiedHeight + 1`.

Why: the first test of `fg_contest`.

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `hI`: `n` satisfies the model's node invariant.

Read aloud: a node is contested only when its greatest height is one past its justification
height. -/
theorem h_max_of_contested (C : Config) (P : Provisional V) (X : External V) (n : M.N)
    -- `n` satisfies the model's node invariant
    (hI : M.nodeInv C P X n)
    -- `n` is contested
    (hc : M.fg_contest n = true) :
    hMax M C n = n.justifiedHeight + 1 :=
  GoldilocksCorrectness.Record.Proofs.Routines.h_max_of_contested M F C P X n hI hc

/-- **Only a node justified past `B` can be contested.** Under the conditions of
`not_contested_or_two_past` (the justified block compatible with `B`, an entry at the height
`n.justifiedHeight > H`, and every progress certificate at a height greater than `H` on a chain of
the tree, for a block of that chain at its height, for a block compatible with `B`), a contested
node state has `h(B) + 1 ≤ n.justifiedHeight`.

Why: `not_contested_or_two_past` gives "not contested" or `h(B) + 2 ≤ hMax M C n`, and a contested
node state has `hMax M C n = n.justifiedHeight + 1`.

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `hI`: `n` satisfies the model's node invariant; `B`: the block; `H`: the height threshold.

Read aloud: inside and after the period, only a node justified past `B` can be contested. -/
theorem justified_past_of_contested (C : Config) (P : Provisional V) (X : External V) (n : M.N)
    -- `n` satisfies the model's node invariant
    (hI : M.nodeInv C P X n) (B : Block V) (H : ℕ)
    -- `n`'s justified block is compatible with `B`, an entry, at the height
    -- `n.justifiedHeight > H`
    (hJ : n.justified.AncestorEq B ∨ B.AncestorEq n.justified) (hJE : IsEntry M C n.justified)
    (hJh : (M.chainStateOf C n.justified).h = n.justifiedHeight) (hHj : H < n.justifiedHeight)
    -- the progress certificates at heights greater than `H` on the chains of the tree are for
    -- blocks compatible with `B`
    (hCert : ∀ D ∈ n.tree, ∀ (h : Height) (T : Block V), T.AncestorEq D →
      ProgressCertOn M D h T → H < h → (M.chainStateOf C T).h = h →
      (T.AncestorEq B ∨ B.AncestorEq T))
    -- `n` is contested
    (hc : M.fg_contest n = true) : (M.chainStateOf C B).h + 1 ≤ n.justifiedHeight :=
  GoldilocksCorrectness.Record.Proofs.Routines.justified_past_of_contested M F C P X n hI B H hJ
    hJE hJh hHj hCert hc

end

/-! ## At the spec's model -/

/-- The landed `GoldilocksCorrectness.Statements.Routines.h_max_of_contested`, recovered from its
record form at the spec's model, at the FG state `n.S` of every node state `n` satisfying the spec's
model's node invariant.

Read aloud: the landed `h_max_of_contested` holds at the FG state of every node state satisfying
the invariant. -/
theorem h_max_of_contested_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (C : Config) (P : Provisional V) (X : External V) (n : NodeState V),
      (Model.goldilocks (V := V)).nodeInv C P X n →
      type_of% (@GoldilocksCorrectness.Statements.Routines.h_max_of_contested V _ _ n.S) := by
  intro C P X n hI hc
  have h := h_max_of_contested Model.goldilocks goldilocksFacts C P X n hI hc
  rw [hMax_goldilocks hI] at h
  exact h

/-- The landed `GoldilocksCorrectness.Statements.Routines.justified_past_of_contested`, recovered
from its record form at the spec's model, at the FG state `n.S` of every node state `n` satisfying
the spec's model's node invariant.

Read aloud: the landed `justified_past_of_contested` holds at the FG state of every node state
satisfying the invariant. -/
theorem justified_past_of_contested_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (C : Config) (P : Provisional V) (X : External V) (n : NodeState V),
      (Model.goldilocks (V := V)).nodeInv C P X n →
      type_of% (@GoldilocksCorrectness.Statements.Routines.justified_past_of_contested V _ _ C
        n.S) := by
  intro C P X n hI B H _ hJ hJE hJh hHj hCert hc
  exact justified_past_of_contested Model.goldilocks goldilocksFacts C P X n hI B H hJ hJE hJh hHj
    (fun D hD h T hTD hc hH hT =>
      hCert D hD h T hTD (by rw [goldilocks_ProgressCertOn]; exact hc) hH hT) hc

end GoldilocksCorrectness.Record.Statements.Routines
