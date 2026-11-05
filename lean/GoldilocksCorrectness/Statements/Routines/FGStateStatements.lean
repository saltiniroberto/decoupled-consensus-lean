module
public import GoldilocksCorrectness.Proofs.Routines.FGStateReaders

@[expose] public section

/-!
# Two statements about the contest test of an FG state

`h_max_of_contested`: a contested FG state has `h_max = h_j + 1`; `justified_past_of_contested`:
under the conditions of `not_contested_or_two_past`, a contested FG state has
`h(B) + 1 ≤ h_j` for the block `B`. Proved in `Proofs/Routines/FGStateReaders.lean`.

Moved here unchanged from the execution pages.
-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

namespace GoldilocksCorrectness.Statements.Routines

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

/-- **A contested FG state is one height past its justification.** When `fg_contest n`, then
`n.h_max = n.h_j + 1`.

Why: the first test of `fg_contest`.

The variables:
- `n`: the FG state.

Read aloud: an FG state is contested only when its greatest height is one past its justification
height. -/
theorem h_max_of_contested (n : FGState V)
    -- `n` is contested
    (hc : fg_contest n = true) :
    n.h_max = n.h_j + 1 :=
  GoldilocksCorrectness.Proofs.Routines.h_max_of_contested n hc

/-- **Only a state justified past `B` can be contested.** Under the hypotheses of the landed
`not_contested_or_two_past` (the chain states computed, the justified block compatible with `B`,
an entry at the height `n.h_j > H`, and every certificate at a height greater than `H` on a held
chain, for a block of that chain at its height, for a block compatible with `B`), a contested FG
state has `h(B) + 1 ≤ n.h_j`.

Why: `not_contested_or_two_past` gives "not contested" or `h(B) + 2 ≤ n.h_max`, and a contested
state has `n.h_max = n.h_j + 1`.

The variables:
- `C`: the parameters; `n`: the FG state; `B`: the block; `H`: the height threshold.

Read aloud: inside and after the period, only a state justified past `B` can be contested. -/
theorem justified_past_of_contested (C : Config) (n : FGState V) (B : Block V) (H : ℕ)
    -- the chain states of `n`'s tree are the blocks' own
    (hσ : ChainStatesComputed C n)
    -- `n`'s justified block is compatible with `B`, an entry, at the height `n.h_j > H`
    (hJ : n.J.AncestorEq B ∨ B.AncestorEq n.J) (hJE : IsEntry C n.J)
    (hJh : (chainStateOf C n.J).h = n.h_j) (hHj : H < n.h_j)
    -- the certificates at heights greater than `H` on held chains are for blocks compatible
    -- with `B`
    (hCert : ∀ D ∈ n.T, ∀ (h : Height) (T : Block V), T.AncestorEq D →
      ProgressCertOn D h T → H < h → (chainStateOf C T).h = h → (T.AncestorEq B ∨ B.AncestorEq T))
    -- `n` is contested
    (hc : fg_contest n = true) : (chainStateOf C B).h + 1 ≤ n.h_j :=
  GoldilocksCorrectness.Proofs.Routines.justified_past_of_contested C n B H hσ hJ hJE hJh hHj
    hCert hc

end

end GoldilocksCorrectness.Statements.Routines
