import Spec.Defs.Model
import Spec.Defs.FinsetM

/-!
# Failure: one `Error`, and `DRE`

**This file is not a specification.** It holds no protocol content — nothing here renders a
routine of the protocol. It is the failure vocabulary the routines of `Spec` share, kept out of
the routine files so that each of those states what the protocol does and nothing else.

The protocol has no failures. A routine of `Spec` raises where its Lean cannot see a fact its
caller ensures: `blockWithRoot` raises when two blocks of a tree share a root, a grade result
read with `let G ← result` raises when the result is still pending, and `let y ← x` raises when
the option `x` is `none`. The theorem worth having is therefore that **nothing ever raises** on
the stores a run reaches, and that does not belong to the spec.

## Why one payload-free value

`Error` has no type parameter, one constructor, and distinguishes no cause:

* the error is a rendering artifact, so detail in it helps nobody — the fact worth proving is
  that it never fires;
* it keeps every signature short and every `do` block in a single error type, which is what
  `Monad (Except ε)` requires, `ε` being fixed across a bind;
* **`Finset.filterM` could not be used over it otherwise.** That fold
  needs its combining operation commutative, and the failure-failure case needs the two
  failures to be *equal* — which is `Subsingleton Error`. Give `Error` a payload and
  `Std.Commutative` becomes false, not merely unproved, because the result would then depend
  on which failure the traversal met first. The routines of `Spec` that filter a set by a test
  that can raise (`beforeCutoff` of `lean/Spec/Objects.lean`, and routines of the files under
  `lean/Spec/Protocol/`) are the consumers.

`DRE α` is `Except Error α` — a *deterministic* result or exception, named as the
deterministic partner of `Nondet.lean`'s `NDRE`. (A bare `Result` would silently shadow
core's `EStateM.Result`, which is why the name is an acronym rather than the word.)
-/

set_option autoImplicit false

namespace DC

/-- The one failure of `Spec`, thrown by every routine that can fail and carrying nothing.
    The module header lists where it is raised, and says why it has no payload.

    Timing is deliberately not a failure. No routine tests its own instant: `tick`
    (`lean/Spec/Node.lean`) tests the instant it was handed against the schedule, and every
    routine it calls runs because that test passed. -/
inductive Error where
  /-- The failure. -/
  | error

/-- Any two failures are the same failure. An `instance`, not a `theorem`, because `lean/Spec/`
    holds no theorems — and it is what the two instances below cannot exist without. -/
instance : Subsingleton Error := ⟨fun e e' => by cases e; cases e'; rfl⟩

/-- `DRE α` is an `α` or the failure: the result type of every routine that can
    raise, so no signature repeats the error type.

    **`abbrev`, not `def`**. It has to be reducible: instance synthesis
    does not unfold a plain `def`, so with one the `Monad` and `MonadExcept` instances are
    not found, `do` and `←` fail, and even `throw .error` cannot resolve its constructor. As
    an `abbrev` everything applies through it — `do`, `throw`, `←`, and `Except.toOption` and
    friends — while signatures and `#check` output read `DRE α`. -/
abbrev DRE (α : Type) := Except Error α

/-- The pure extraction from an option: `x.value`, its `x ≠ ⊥` hypothesis (`⊥` is `none`)
    discharged by `solve_by_elim` from the facts of an enclosing `if x ≠ none then`; the
    notation at the head of `lean/Spec/Objects.lean` makes that `if` hand its condition to
    its branches. The raising lift below, `let y ← x`, covers the monadic bodies; this is
    the *pure* bodies' extraction, where no lift can fire. The extraction must sit
    inside the `if`'s then-branch — a do join point does not carry the
    hypothesis into the continuation (measured). The trap it carries: dot notation
    resolves fields in the type's own namespace only, hence the `_root_.` (a
    `DC.Option.value` is invisible to `x.value`). -/
def _root_.Option.value {α : Type} (x : Option α)
    (h : x ≠ ⊥ := by solve_by_elim [And.left, And.right]) : α :=
  x.get (Option.ne_none_iff_isSome.mp h)

/-- `Finset.unionM` at `DRE` is commutative — **and only because the failure
    carries no payload**. The failure-failure case needs the two failures to be equal, which
    is `Subsingleton Error`. -/
instance {α : Type} [DecidableEq α] :
    Std.Commutative (Finset.unionM (α := α) (m := DRE)) where
  comm x y := by
    cases x <;> cases y
    all_goals simp only [Finset.unionM, Except.bind, bind, pure]
    all_goals first
      | rfl
      | exact congrArg _ (Subsingleton.elim _ _)
      | exact congrArg _ (Finset.union_comm _ _)

/-- And associative, for the same reason. -/
instance {α : Type} [DecidableEq α] :
    Std.Associative (Finset.unionM (α := α) (m := DRE)) where
  assoc x y z := by
    cases x <;> cases y <;> cases z <;>
      simp only [Finset.unionM, Except.bind, bind, pure] <;>
      first
        | rfl
        | exact congrArg _ (Subsingleton.elim _ _)
        | exact congrArg _ (Finset.union_assoc _ _ _)

/-- The raising coercion out of `Option`: in any raising `do`
    block, `let y ← x` with `x : Option α` binds the value and raises on `⊥` — total, the
    one failure. A `MonadLift`, not a `Coe`, because `←` resolves through lifts; the
    chain into `NDRE` composes through `Nondet.lean`'s `Except` lift. This is the
    extraction spelling wherever the body raises: where absence is a normal
    branch, a plain `if x ≠ none` decides the branch and the bind behind it cannot raise.
    The accepted cost: the extraction's safety
    is not checked at the site — dropping the test leaves compiling code that raises
    where a rule meant to fall through. -/
scoped instance : MonadLift Option DRE :=
  ⟨fun x => x.elim (.error .error) .ok⟩

end DC
