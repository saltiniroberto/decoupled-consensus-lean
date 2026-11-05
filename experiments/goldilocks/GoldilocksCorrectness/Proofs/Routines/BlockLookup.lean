module
public import GoldilocksCorrectness.Proofs.Routines.Score

@[expose] public section

/-!
# Reading a block by its identifier

`resolved_eq_ok_true`: a Goldfish vote whose head is the root of a block `H` of the tree `T`, of
a slot at most the vote's, is resolved in `T` (`resolved T vote = .ok true`), when no two blocks
of `T` share a root. Its proof reads `blockWithRoot_eq_ok` and `find?_eq_some` of
`Proofs/Routines/Score.lean`.

Moved here unchanged from the execution pages.
-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Routines

section

open Goldilocks
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn)
variable {V : Type} [DecidableEq V]

/-- A vote whose head is the root of a block `H` of `T`, of a slot at most the vote's, is resolved
in `T`, when no two blocks of `T` share a root.

The variables:
- `T`: the tree; `vote`: the vote; `H`: its head block. -/
theorem resolved_eq_ok_true {T : Finset (Block V)} {vote : GoldfishVote V} {H : Block V}
    (hRoots : RootsNameBlocksIn T) (hH : H ∈ T) (hr : H.root = vote.head)
    (hs : H.slot ≤ vote.slot) : resolved T vote = .ok true := by
  simp only [resolved, blockWithRoot_eq_ok hRoots, find?_eq_some hRoots hH hr, dre_bind_ok,
    ne_eq, reduceCtorEq, not_false_eq_true, dite_true, Option.value, Option.get_some]
  show Except.ok _ = Except.ok _
  exact congrArg Except.ok (decide_eq_true hs)

end

end GoldilocksCorrectness.Proofs.Routines
