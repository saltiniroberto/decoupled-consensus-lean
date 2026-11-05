module
public import GoldilocksCorrectness.Proofs.Executions.Roots

@[expose] public section

/-!
# The statements relating the bounded roots premise to the landed one

The audited statements on `RootsNameBlocksUntil S Sched x t` (within the blocks honest validators
hold by the time `t`, a root names one block), proved in
`GoldilocksCorrectness/Proofs/Executions/Roots.lean`: it is monotone in `t`; the landed
`RootsNameBlocks S Sched x` is it at every `t`; and it fails only through
`RootCollisionHeldBy S Sched x t`, two distinct blocks held by `t` with one root.


-/

set_option autoImplicit false

open scoped DC

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec Schedule)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

variable {S : Setup V} {Sched : Schedule V} (x : AtomicExec (protocol S) Sched)

/-- **Being held by a time is monotone in the time.** A block an honest validator holds at a step
at a time at most `t` is held at a step at a time at most any `t' ≥ t`.

The variables:
- `x`: the execution; `t`, `t'`: the two bounds, `t ≤ t'`; `B`: the block.

Read aloud: a block held by `t` is held by every later time. -/
theorem inHonestTreeBy_mono {t t' : ℕ} (h : t ≤ t') {B : Block V} (hB : inHonestTreeBy x t B) :
    inHonestTreeBy x t' B :=
  GoldilocksCorrectness.Proofs.Executions.inHonestTreeBy_mono x h hB

/-- **A larger bound gives the smaller one.** When roots name blocks among what honest validators
hold by `t'`, they do among what is held by any `t ≤ t'`.

The variables:
- `x`: the execution; `t`, `t'`: the two bounds, `t ≤ t'`.

Read aloud: uniqueness among what is held by `t'` is uniqueness among what is held by `t ≤ t'`. -/
theorem RootsNameBlocksUntil.mono {x : AtomicExec (protocol S) Sched} {t t' : ℕ} (h : t ≤ t')
    (hR : RootsNameBlocksUntil S Sched x t') : RootsNameBlocksUntil S Sched x t :=
  GoldilocksCorrectness.Proofs.Executions.RootsNameBlocksUntil.mono h hR

/-- **A block held at some step is held by some time.** `inHonestTree x B` holds exactly when
`inHonestTreeBy x t B` holds for some time `t`.

The variables:
- `x`: the execution; `B`: the block.

Read aloud: an honest validator holds `B` at some step exactly when it does so by some time. -/
theorem inHonestTree_iff_exists_by (B : Block V) :
    inHonestTree x B ↔ ∃ t : ℕ, inHonestTreeBy x t B :=
  GoldilocksCorrectness.Proofs.Executions.inHonestTree_iff_exists_by x B

/-- **The landed premise is the bounded one at every bound.** `RootsNameBlocks S Sched x` holds
exactly when `RootsNameBlocksUntil S Sched x t` holds for every time `t`.

The variables:
- `x`: the execution.

Read aloud: roots name blocks among everything honest validators ever hold exactly when they do so
among what is held by every time `t`. -/
theorem rootsNameBlocks_iff_forall_until :
    RootsNameBlocks S Sched x ↔ ∀ t : ℕ, RootsNameBlocksUntil S Sched x t :=
  GoldilocksCorrectness.Proofs.Executions.rootsNameBlocks_iff_forall_until x

/-- **The landed premise gives the bounded one.** From `RootsNameBlocks S Sched x`, roots name
blocks among what honest validators hold by any time `t`.

The variables:
- `x`: the execution; `t`: the bound.

Read aloud: if roots name blocks among everything honest validators ever hold, they do among what
is held by `t`. -/
theorem rootsNameBlocksUntil_of_rootsNameBlocks (t : ℕ) (hR : RootsNameBlocks S Sched x) :
    RootsNameBlocksUntil S Sched x t :=
  GoldilocksCorrectness.Proofs.Executions.rootsNameBlocksUntil_of_rootsNameBlocks x t hR

/-- **Either the bounded premise or a collision.** For every time `t`, roots name blocks among what
honest validators hold by `t`, or two distinct blocks held by `t` have one root.

The variables:
- `x`: the execution; `t`: the bound.

Read aloud: the bounded premise fails only through a collision by `t`. -/
theorem rootsNameBlocksUntil_or_collision (t : ℕ) :
    RootsNameBlocksUntil S Sched x t ∨ RootCollisionHeldBy S Sched x t :=
  GoldilocksCorrectness.Proofs.Executions.rootsNameBlocksUntil_or_collision x t

/-- **The bounded premise fails exactly through a collision.** `RootsNameBlocksUntil S Sched x t`
is false exactly when `RootCollisionHeldBy S Sched x t` holds.

The variables:
- `x`: the execution; `t`: the bound.

Read aloud: roots fail to name blocks among what is held by `t` exactly when a collision has hit
two blocks held by `t`. -/
theorem not_rootsNameBlocksUntil_iff_collision (t : ℕ) :
    ¬ RootsNameBlocksUntil S Sched x t ↔ RootCollisionHeldBy S Sched x t :=
  GoldilocksCorrectness.Proofs.Executions.not_rootsNameBlocksUntil_iff_collision x t

end GoldilocksCorrectness.Statements.Executions
