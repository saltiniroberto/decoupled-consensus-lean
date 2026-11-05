module
public import GoldilocksCorrectness.Proofs.Routines.ChainStateOfCertified

@[expose] public section

/-!
# Three rounds of justification along a chain

`round_justified_of_spacing3`: for blocks `B ⪯ B'` with `h(B) + 1 ≤ h(B')`, `B'`'s slot at most
`δt` after the slot of `B`'s entry block `T_h(B)`, and the conditions of the statement,
`h(B) ≤ h_j(B')`. Proved in `Proofs/Routines/ChainStateOfCertified.lean`.

Moved here unchanged from the execution pages.
-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

namespace GoldilocksCorrectness.Statements.Routines

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [RootOrder] in
/-- **C5, the next opening within `δt` of the entry inherits the justification.** For blocks
`B ⪯ B'` with `h(B) + 1 ≤ h(B')`, `B'`'s slot at most `δt` after the slot of `B`'s entry `T_h(B)`,
every strict ancestor of `B'` of a smaller slot than `B'`, and the justification clause (when
`B'`'s parent is at `B`'s height, `B'`'s chain justified `h(B)` with `T_h(B)`):
`h(B) ≤ h_j(B')`.

Why: the block `Y ⪯ B'` that left the height `h(B)` (Lemma 67) has its parent at `B`'s height on
`B'`'s chain, hence with `B`'s entry; it took the justification branch, which sets `h_j` to `h(B)`,
or the timeout branch, whose test fails for a strict ancestor of `B'`; and when `Y` is `B'` the
justification clause gives it. The justification height never decreases along a chain
(`chainStateOf_h_j_h_F_mono`).

The variables:
- `C`: the parameters; `B`: the proposal at the earlier honest round opening slot; `B'`: the later one's.

Read aloud: when the next honest round opening slot is no later than `δt` slots after the entry, the height was
left by its justification, which the opening's chain inherits.

 -/
theorem round_justified_of_spacing3 (C : Config) (B B' : Block V)
    (hBB' : B.AncestorEq B') (hh : (chainStateOf C B).h + 1 ≤ (chainStateOf C B').h)
    (hslot : B'.slot ≤ (chainStateOf C B).T_h.slot + C.δt)
    (hanc : ∀ Y : Block V, Y.AncestorEq B' → Y ≠ B' → Y.slot < B'.slot)
    (hJ : (chainStateOf C B'.parent).h = (chainStateOf C B).h →
      (chainStateOf C B').h_j = (chainStateOf C B).h ∧
      (chainStateOf C B').J = (chainStateOf C B).T_h) :
    (chainStateOf C B).h ≤ (chainStateOf C B').h_j :=
  GoldilocksCorrectness.Proofs.Routines.round_justified_of_spacing3 C B B' hBB' hh hslot hanc hJ

end

end GoldilocksCorrectness.Statements.Routines
