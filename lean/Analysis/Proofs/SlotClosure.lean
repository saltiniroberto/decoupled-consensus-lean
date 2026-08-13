import Spec

/-!
# Proofs: closing slots

The argument behind Lemma 3. `Analysis/Lemmas.lean` holds the statement of record and calls into
here in one line.

`BlockPostState` and Definition 20's `actionState` are declared here rather than in
`Analysis/Lemmas.lean`, because the statement there needs them and that file may hold no
definitions beyond the statements themselves.

**The proof is outstanding.** What it needs is the invariant the paper argues in prose: the
height-event check cannot fire in a block post-state, because `state_transition` already ran it at
the block and left its conditions false. `process_slots` is a `while`, which is a least fixed point
that does not reduce, so read the `lean-proof-idioms` skill before attempting it.
-/

set_option autoImplicit false

namespace Decoupled

open scoped Decoupled
open Framework.StsMultisetLog

/-- `σ` is a **block post-state**: reachable from `ChainState.gen` by `stateTransition` along a
    chain of blocks. That is the paper's own term — Lemmas 4 and 10 say "every reachable block
    post-state".

    **Deliberately weaker than the paper's `σ[·]`.** Figure 3 (`alg:store`) admits a block only
    when the structural precheck passes and its claimed post-state root equals `root(σ')`, and
    neither the precheck nor a state-root function is modelled, so neither is required here. This
    predicate therefore holds of *more* states than `σ[·]` does, which makes a theorem carrying it
    as a hypothesis **stronger** than the paper's, and one that specialises to the paper's sentence
    when Figure 3 lands.

    It is not called `σ[·]`, and must not be: an earlier `replayChain` was withdrawn precisely for
    claiming to be that map while omitting both checks. -/
inductive BlockPostState {Node Root : Type} [DecidableEq Node] [DecidableEq Root]
    [Electorate Node] [Params] : ChainState Node Root → Prop
  /-- Genesis: the values Definition 13 (`def:chain-state`) lists, which Figure 1's **Genesis**
      block repeats. -/
  | gen : BlockPostState ChainState.gen
  /-- One accepted block later. -/
  | step {σ σ' : ChainState Node Root} {B : Blk Node Root} :
      BlockPostState σ → stateTransition σ B = .state σ' → BlockPostState σ'

/-- Definition 20 (`def:finality-action-state`): `σ_a[X] = process_slots(σ[X], slot(a))`, the state
    a signing action reads, got by closing exactly the slots before the action.

    The definition is that one application of `process_slots`, so this renders all of it. Written
    over a block post-state rather than over `σ[X]`, for the reason in `BlockPostState`.

    Definition 20's side condition `X.slot ≤ slot(a)` is `σ.L.slot ≤ t` here, and the lemmas that
    use this carry it rather than the definition, which is where the paper puts it. -/
def actionState {Node Root : Type} [DecidableEq Node] [DecidableEq Root]
    [Electorate Node] [Params] (σ : ChainState Node Root) (t : Time) : ChainState Node Root :=
  processSlots σ t

namespace Proofs

/-- Lemma 3 (`lem:empty-slot-noop`). Outstanding; see this file's header for what it needs. -/
theorem emptySlotNoop {Node Root : Type} [DecidableEq Node] [DecidableEq Root]
    [Electorate Node] [Params] :
    ∀ (σ : ChainState Node Root) (t : Time),
      BlockPostState σ → σ.L.slot ≤ t →
        (actionState σ t).L = σ.L ∧
        (actionState σ t).h = σ.h ∧
        (actionState σ t).s_h = σ.s_h ∧
        (actionState σ t).nj = σ.nj ∧
        (actionState σ t).J = σ.J ∧
        (actionState σ t).h_j = σ.h_j ∧
        (actionState σ t).F = σ.F ∧
        (actionState σ t).h_F = σ.h_F ∧
        (actionState σ t).P = σ.P ∧
        (actionState σ t).targetParticipation = σ.targetParticipation ∧
        (actionState σ t).progress = σ.progress := by
  sorry

end Proofs

end Decoupled
