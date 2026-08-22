import Spec.Consensus1.Model

/-!
# Failure: one `Error`, and `ResultOrExcept`

**This file is not a specification.** It holds no protocol content — nothing here renders a
definition or a figure of the draft. It is the failure vocabulary the whole rendering shares,
kept out of the figure files so that each of those states what the draft says and nothing
else (Roberto, 2026-08-21).

A copy of `Spec/Consensus/Raise.lean` under this subtree's namespace, for the reason
`Notation.lean` gives: the renderings share nothing. One thing differs from that copy — the
`Finset.unionM` fold instances are absent, this rendering never filtering monadically.

The draft has no failures. Its state map is defined on every accepted block and its routines
run at the instants the schedule names, so every raise below is a rendering artifact: it marks
a place where this Lean cannot see what the draft's prose knows. The theorem worth having is
therefore that **nothing ever raises** on a store that keeps the coherence invariant, and that
belongs to `Analysis/`.

## Why one payload-free value

`Error` has no type parameter, one constructor, and distinguishes no cause. Three reasons, the
last one decisive:

* the error is a rendering artifact, so detail in it helps nobody — the fact worth proving is
  that it never fires;
* it keeps every signature short and every `do` block in a single error type, which is what
  `Monad (Except ε)` requires, `ε` being fixed across a bind;
* **a payload would make a monadic fold over a set ill-defined.** The other rendering's
  `Finset.filterM` needs its combining operation commutative, and the failure-failure case
  needs the two failures to be *equal* — which is `Subsingleton Error`. With a payload
  `Std.Commutative` is false, not merely unproved, because the result would depend on which
  failure the traversal met first. This rendering never filters monadically — Definition 5's
  set-builder reads the state map through the raw `Option` instead — so the instances are not
  here; the reason to keep the error payload-free is.

`ResultOrExcept α` is `Except Error α`, and the long name is deliberate: `Result` is too
common a word to take — `EStateM.Result` is in core, and a bare `Result` inside this namespace
would shadow it silently.
-/

set_option autoImplicit false

namespace Consensus1

/-- The one failure of this rendering, thrown by every routine that can fail and carrying
    nothing. `Σ.σ[B]` raises it when the map does not record `B`; anything added later raises
    the same value. See the module header for why it has no payload.

    Timing is deliberately not a failure. In this draft nothing tests its own instant:
    `on_tick` dispatches on the clock it was handed, and every routine it calls runs because
    the tick said so. -/
inductive Error where
  /-- The failure. -/
  | error

/-- Any two failures are the same failure. An `instance`, not a `theorem`, because `Spec/`
    holds no theorems — and it is what the two instances below cannot exist without. -/
instance : Subsingleton Error := ⟨fun e e' => by cases e; cases e'; rfl⟩

/-- `ResultOrExcept α` is an `α` or the failure: the result type of every routine that can
    raise, so no signature repeats the error type.

    **`abbrev`, not `def`** — measured 2026-08-21. It has to be reducible: instance synthesis
    does not unfold a plain `def`, so with one the `Monad` and `MonadExcept` instances are
    not found, `do` and `←` fail, and even `throw .error` cannot resolve its constructor. As
    an `abbrev` everything applies through it — `do`, `throw`, `←`, and `Except.toOption` and
    friends — while signatures and `#check` output read `ResultOrExcept α`. -/
abbrev ResultOrExcept (α : Type) := Except Error α

end Consensus1
