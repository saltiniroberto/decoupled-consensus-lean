import Spec.Consensus1.Model
import Spec.Consensus1.FinsetM

/-!
# Failure: one `Error`, and `ResultOrExcept`

**This file is not a specification.** It holds no protocol content — nothing here renders a
definition or a figure of the draft. It is the failure vocabulary the whole rendering shares,
kept out of the figure files so that each of those states what the draft says and nothing
else (Roberto, 2026-08-21).

A copy of `Spec/Consensus/Raise.lean` under this subtree's namespace, for the reason
`Notation.lean` gives: the renderings share nothing. The fold instances below are the same
copy's, at this subtree's own error type.

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
* **`Finset.filterM` and `Finset.imageM` could not be used over it otherwise.** Those folds
  need their combining operation commutative, and the failure-failure case needs the two
  failures to be *equal* — which is `Subsingleton Error`. Give `Error` a payload and
  `Std.Commutative` becomes false, not merely unproved, because the result would then depend
  on which failure the traversal met first. Figure 7's `viable` and `update_finality` are the
  consumers (2026-08-22, Roberto's call — a first form read the map through the raw `Option`
  inside the set-builders, which answered silently where this raises).

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

/-- `Finset.unionM` at `ResultOrExcept` is commutative — **and only because the failure
    carries no payload**. The failure-failure case needs the two failures to be equal, which
    is `Subsingleton Error`. -/
instance {α : Type} [DecidableEq α] :
    Std.Commutative (Finset.unionM (α := α) (m := ResultOrExcept)) where
  comm x y := by
    cases x <;> cases y
    all_goals simp only [Finset.unionM, Except.bind, bind, pure]
    all_goals first
      | rfl
      | exact congrArg _ (Subsingleton.elim _ _)
      | exact congrArg _ (Finset.union_comm _ _)

/-- And associative, for the same reason. -/
instance {α : Type} [DecidableEq α] :
    Std.Associative (Finset.unionM (α := α) (m := ResultOrExcept)) where
  assoc x y z := by
    cases x <;> cases y <;> cases z <;>
      simp only [Finset.unionM, Except.bind, bind, pure] <;>
      first
        | rfl
        | exact congrArg _ (Subsingleton.elim _ _)
        | exact congrArg _ (Finset.union_assoc _ _ _)

/-- The raising coercion out of `Option` (Roberto, 2026-08-24): in any raising `do`
    block, `let y ← x` with `x : Option α` binds the value and raises on `⊥` — total, the
    one failure. A `MonadLift`, not a `Coe`, because `←` resolves through lifts; the
    chain into `NDRE` composes through `Nondet.lean`'s `Except` lift. This is the
    subtree's extraction spelling wherever the body raises: where absence is a normal
    branch, a plain `if x ≠ ⊥` decides the branch and the bind behind it cannot raise.
    The cost accepted with it (Roberto, "let's see how it goes"): the extraction's safety
    is not checked at the site — dropping the test leaves compiling code that raises
    where a rule meant to fall through. The autoparam extraction that did check,
    `Option.value`, is parked in `OldDefs.lean`. -/
scoped instance : MonadLift Option ResultOrExcept :=
  ⟨fun x => x.elim (.error .error) .ok⟩

end Consensus1
