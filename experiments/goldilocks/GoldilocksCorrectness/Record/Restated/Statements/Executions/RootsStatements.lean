module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Roots

@[expose] public section

/-!
# RootsStatements, over a model

The statements of `GoldilocksCorrectness/Statements/Executions/RootsStatements.lean` over a model
`M`, for an execution `x` of `protocolOf M S`, proved in
`Record/Restated/Proofs/Executions/Roots.lean`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Statements.Executions

open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V)

variable {S : Setup V} {A : Activity V} (x : Trace V (NamedObject V) M.N)

/-- **Being held by a time is monotone in the time.** A block an honest validator holds at a step
at a time at most `t` is held at a step at a time at most any `t' ≥ t`.

The variables:
- `M`: the model;
- `x`: the execution; `t`, `t'`: the two bounds, `t ≤ t'`; `B`: the block.

Read aloud: a block held by `t` is held by every later time. -/
theorem inHonestTreeBy_mono {t t' : ℕ} (h : t ≤ t') {B : Block V} (hB : inHonestTreeBy M A x t B) :
    inHonestTreeBy M A x t' B :=
  (GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_mono M) x (by exact_mod_cast h) hB

/-- **A larger bound gives the smaller one.** When roots name blocks among what honest validators
hold by `t'`, they do among what is held by any `t ≤ t'`.

The variables:
- `M`: the model;
- `x`: the execution; `t`, `t'`: the two bounds, `t ≤ t'`.

Read aloud: uniqueness among what is held by `t'` is uniqueness among what is held by `t ≤ t'`. -/
theorem RootsNameBlocksUntil.mono {x : Trace V (NamedObject V) M.N} {t t' : ℕ} (h : t ≤ t')
    (hR : RootsNameBlocksUntil M A x t') : RootsNameBlocksUntil M A x t :=
  (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) (by exact_mod_cast h) hR

/-- **Either the bounded premise or a collision.** For every time `t`, roots name blocks among what
honest validators hold by `t`, or two distinct blocks held by `t` have one root.

The variables:
- `M`: the model;
- `x`: the execution; `t`: the bound.

Read aloud: the bounded premise fails only through a collision by `t`. -/
theorem rootsNameBlocksUntil_or_collision (t : ℕ) :
    RootsNameBlocksUntil M A x t ∨ RootCollisionHeldBy M S A x t :=
  (GoldilocksCorrectness.Record.Proofs.Executions.rootsNameBlocksUntil_or_collision M) x t

/-- **The bounded premise fails exactly through a collision.** `RootsNameBlocksUntil M S Sched x t`
is false exactly when `RootCollisionHeldBy M S Sched x t` holds.

The variables:
- `M`: the model;
- `x`: the execution; `t`: the bound.

Read aloud: roots fail to name blocks among what is held by `t` exactly when a collision has hit
two blocks held by `t`. -/
theorem not_rootsNameBlocksUntil_iff_collision (t : ℕ) :
    ¬ RootsNameBlocksUntil M A x t ↔ RootCollisionHeldBy M S A x t :=
  (GoldilocksCorrectness.Record.Proofs.Executions.not_rootsNameBlocksUntil_iff_collision M) x t

end GoldilocksCorrectness.Record.Statements.Executions

