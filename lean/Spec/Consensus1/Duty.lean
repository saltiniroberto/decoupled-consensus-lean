import Spec.Consensus1.Store
import Spec.Consensus1.Nondet

/-!
# The duty monad: an ambient outbox over `NDRE`

**This file is not a specification.** It holds no protocol content — nothing here renders
a definition or a figure of the draft. It is the vocabulary that lets a duty *broadcast*
— the draft's own verb — instead of returning its messages (Roberto, 2026-08-24; probes
`scratch/DutyWriterProbe.lean` and, for the declined store-ambient variant,
`scratch/DutyMonadProbe.lean`).

## The design

A duty is `Store → … → DutyM (Store …)`: the store stays an explicit input and output —
Roberto declined the variant that made it ambient, and keeping it explicit is also what
keeps the instant autoparams attachable — while the **outbox** threads through the monad.
`broadcast m` puts a message in it; composition is function call, and a caller never
unions sends: an earlier duty's broadcasts are already in the outbox when a later duty
runs.

`DutyM` is `StateT` of the outbox over `NDRE`, so under the `abbrev` a duty is a function
`outbox → NDRE (α × outbox)`. Two consequences worth reading off that type: the base is
`NDRE` because the duty *bodies* pick and raise — the walk's tie, the picked listing, the
`σ[·]` and timestamp reads — which no smaller base admits; and the outbox sits *inside*
the nondeterminism, so each outcome carries its own sends (a duty that picks broadcasts
per pick, and a failing outcome broadcast nothing).

## Consuming a duty

There is no run inside the spec — the figures compose duties by calling them, and so do
the files here. The one boundary is `DutyM.outcomes`: the set of outcomes of a duty run
with nothing sent, each an answer — a `DutyResult`, the store afterwards with the
broadcasts — or the failure. The sts wiring consumes a duty as
`res ∈ (S.onTick i t p).outcomes`, and `Analysis/` statements quantify over the same set.
`DutyResult` itself lives in `Store.lean` and survives only at this boundary.
-/

set_option autoImplicit false

namespace Consensus1

variable {Validator : Type} [Roots] [DecidableEq Validator]

/-- The duty monad: the outbox threaded over the nondeterministic-raising base. The store
    is deliberately not in here — a duty takes and returns it explicitly. -/
abbrev DutyM (Validator : Type) (α : Type) :=
  StateT (Finset (Message Validator)) NDRE α

/-- The draft's own verb: put a message in the outbox. -/
def broadcast (m : Message Validator) : DutyM Validator Unit :=
  modify (· ∪ {m})

/-- The outcome set of a duty run with nothing sent: each element the failure, or a
    `DutyResult` — the store afterwards and everything broadcast along the way. The
    consumption boundary: the sts step and every `Analysis/` statement read a duty as
    `res ∈ (…).outcomes`, and nothing inside `Spec/` consumes one at all. -/
def DutyM.outcomes (d : DutyM Validator (Store Validator)) :
    Set (DRE (DutyResult Validator)) :=
  (do
    let (S, out) ← d.run ∅
    return { state := S, send := out } : NDRE (DutyResult Validator)).run

end Consensus1
