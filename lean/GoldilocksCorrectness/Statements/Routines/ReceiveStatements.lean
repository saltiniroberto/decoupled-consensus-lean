module
public import GoldilocksCorrectness.Proofs.Routines.Wiring

@[expose] public section

/-!
# The anchor of a lock holder, from the node state alone

`anchor_extends_B_of_inv_orTwoPast`: a node state that holds a live lock entry on a block `B`, whose
caches are compatible with `B` (`CachesCompatibleWith`), and whose FG state is not contested or has
the greatest chain-state height at least two past `B`'s, walks the AC fork choice from `B` or from a
descendant of `B`. Proved in `Proofs/Routines/Wiring.lean`.

Moved here unchanged from the execution pages.
-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

namespace GoldilocksCorrectness.Statements.Routines

section

open Goldilocks
open Goldilocks.Sts (Setup)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

section

variable (S : Setup V)

/-- **The anchor of a lock holder is `B` or a descendant of `B`, with the finality gadget not
contested or two past `B`.** At a node state `n` and time `t`: `n` holds a live lock entry on
`B`; every live entry is on a block compatible with `B`; the caches are compatible with `B`; every
held block at a chain-state height at least `h(B) + 2` descends from `B`; the finality gadget is
not contested, or `n.S.h_max ≥ h(B) + 2`; some held block has the chain-state height
`n.S.h_max`; no two held blocks share a root; and the chain states of the held blocks are
computed. Then `get_anchor n.A (fg_to_ac n.S) t` is `B` or a descendant of `B`.

Why: as `anchor_extends_B_of_inv`, except for the viable head on `B`'s chain: when
`h_max ≥ h(B) + 2`, the held block at `h_max` descends from `B` and is viable, since
`head_height_floor n.S` (the least chain-state height a viable block may have) is `h_max` or `h_max − 1`; otherwise the finality gadget is not
contested, `head_height_floor` is `h_max − 1 ≤ h(B)`, and `B` is viable.

Rendering note. Callers of the original:
`holder_vote_extends_B` (`Proofs/Executions/PeriodHolders.lean:538`) and the statement wrapper.
The copy's caller is `holder_vote_extends_B_orTwoPast`, whose own `hNC` is the disjunction. Read
aloud: the finality gadget may be contested, provided the top height is two past `B`'s.

The variables:
- `S`: the setup; `n`: the node state; `B`: the locked block; `t`: the time; `H`: the threshold of
  the old attestations; `d`: the lock's deadline;
- `hlock`, `hlive`: `n` holds `⟨B, d⟩`, live at `t`; `hlocks`: every live entry is on a block
  compatible with `B`; `hC`: the caches are compatible with `B`; `hTwo`: every held block at a
  chain-state height at least `h(B) + 2` descends from `B`; `hNC`: not contested, or `h_max` at
  least `h(B) + 2`; `hWit`: a held block has the height `n.S.h_max`; `hRootsT`: no two held blocks
  share a root; `hσ`: the chain states of the held blocks are computed.

Read aloud: a validator that holds the lock on `B` walks from `B` or from a descendant of `B`. -/
theorem anchor_extends_B_of_inv_orTwoPast (n : NodeState V) (B : Block V) (t : Time) (H : ℕ)
    (d : Time)
    (hlock : LockEntry.mk B d ∈ n.A.lock_entries)
    (hlive : is_live (fg_to_ac n.S) t (LockEntry.mk B d) = true)
    (hlocks : ∀ e ∈ n.A.lock_entries, is_live (fg_to_ac n.S) t e = true → e.B.compatible B = true)
    (hC : CachesCompatibleWith S B H n)
    (hTwo : ∀ D ∈ n.S.T, (chainStateOf S.C B).h + 2 ≤ (chainStateOf S.C D).h → B.AncestorEq D)
    (hNC : fg_contest n.S = false ∨ (chainStateOf S.C B).h + 2 ≤ n.S.h_max)
    (hWit : ∃ D ∈ n.S.T, (chainStateOf S.C D).h = n.S.h_max)
    (hRootsT : RootsNameBlocksIn n.S.T) (hσ : ChainStatesComputed S.C n.S) :
    B.AncestorEq (get_anchor n.A (fg_to_ac n.S) t) :=
  GoldilocksCorrectness.Proofs.Routines.anchor_extends_B_of_inv_orTwoPast S n B t H d hlock
    hlive hlocks hC hTwo hNC hWit hRootsT hσ

end

end

end GoldilocksCorrectness.Statements.Routines
