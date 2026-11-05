module
public import GoldilocksCorrectness.Statements.Executions.InvariantDefs

@[expose] public section

/-!
# The delivery lemma: its vocabulary

What the delivery lemma (`lem12_honest_vote_delivered`) concludes for each honest voter of a
slot, as one definition over an AC state and a frame: the voter's vote for a block is held,
stamped and resolved strictly before two delays after the slot's start, the block is in the
frame's tree, and the vote is the voter's only vote of the slot in the pool
(`HeldEarlyVoteFor`). Its two corollaries make it the input of `lem8b` (`EarlyVoteOnceFor`) and
of `lem5` (`VotesOnceInPoolFor`). The same with the cutoff a parameter is `HeldEarlyVoteAt`;
the one theorem, `heldEarlyVoteFor_iff`, says the two agree at the cutoff `C.t_ s + 2 · C.Δ`, and
holds by definition.
-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

namespace GoldilocksCorrectness.Statements.Executions

open Goldilocks

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- `HeldEarlyVoteAt A Φ t s H_u u`: the AC state `A` holds `u`'s slot-`s` vote for the block
`H_u`, stamped strictly before the time `t`; `H_u` is in the frame's tree `Φ.tree`; the vote
resolves strictly before `t`; and it is `u`'s only slot-`s` vote in `A`'s pool. This is
`HeldEarlyVoteFor` with the cutoff a parameter.

The variables:
- `A`: the AC state; `Φ`: the frame; `t`: the cutoff;
- `s`: the slot of the vote; `H_u`: the block the vote is for; `u`: the voter.

Read aloud: `A` holds `u`'s slot-`s` vote for `H_u`, stamped strictly before `t`; `H_u` is in
`Φ.tree`; the vote resolves strictly before `t`; and it is `u`'s only slot-`s` vote in `A`'s
pool. -/
def HeldEarlyVoteAt (A : ACState V) (Φ : Frame V) (t : Time) (s : Slot) (H_u : Block V)
    (u : V) : Prop :=
  GoldfishVote.mk u s H_u.root ∈ A.pool s ∧
    (∃ τ : Stamp, A.timestamp_vote (GoldfishVote.mk u s H_u.root) = some τ ∧ τ < (t : Stamp)) ∧
    H_u ∈ Φ.tree ∧
    (∃ y : Stamp, A.tau Φ (GoldfishVote.mk u s H_u.root) = .ok (some y) ∧
      occurrenceBefore (some y) t = true) ∧
    ∀ vote' ∈ A.pool s, vote'.val_index = u → vote' = GoldfishVote.mk u s H_u.root

/-- `HeldEarlyVoteFor C A Φ s H_u u`: the AC state `A` holds `u`'s slot-`s` vote for the block
`H_u`, stamped strictly before `C.t_ s + 2 · C.Δ`; `H_u` is in the frame's tree `Φ.tree`; the
vote resolves (its head found in `Φ.tree`, the later of the two stamps) strictly before
`C.t_ s + 2 · C.Δ`; and it is `u`'s only slot-`s` vote in `A`'s pool.

The variables:
- `C`: the parameters; `A`: the AC state; `Φ`: the frame;
- `s`: the slot of the vote; `H_u`: the block the vote is for; `u`: the voter.

Read aloud: `A` holds `u`'s slot-`s` vote for `H_u`, stamped strictly before `C.t_ s + 2 · C.Δ`;
`H_u` is in `Φ.tree`; the vote resolves (its head found in `Φ.tree`, the later of the two stamps)
strictly before `C.t_ s + 2 · C.Δ`; and it is `u`'s only slot-`s` vote in `A`'s pool. -/
def HeldEarlyVoteFor (C : Config) (A : ACState V) (Φ : Frame V) (s : Slot) (H_u : Block V)
    (u : V) : Prop :=
  GoldfishVote.mk u s H_u.root ∈ A.pool s ∧
    (∃ τ : Stamp, A.timestamp_vote (GoldfishVote.mk u s H_u.root) = some τ ∧
      τ < ((C.t_ s + 2 * C.Δ : Time) : Stamp)) ∧
    H_u ∈ Φ.tree ∧
    (∃ y : Stamp, A.tau Φ (GoldfishVote.mk u s H_u.root) = .ok (some y) ∧
      occurrenceBefore (some y) (C.t_ s + 2 * C.Δ) = true) ∧
    ∀ vote' ∈ A.pool s, vote'.val_index = u → vote' = GoldfishVote.mk u s H_u.root

omit [Fintype V] [RootOrder] in
/-- `HeldEarlyVoteFor` is `HeldEarlyVoteAt` at the cutoff `C.t_ s + 2 · C.Δ`.

The variables:
- `C`: the parameters; `A`: the AC state; `Φ`: the frame;
- `s`: the slot of the vote; `H_u`: the block the vote is for; `u`: the voter.

Read aloud: `A` holds `u`'s early vote for `H_u` exactly when it holds it with the cutoff
`C.t_ s + 2 · C.Δ`. -/
theorem heldEarlyVoteFor_iff (C : Config) (A : ACState V) (Φ : Frame V) (s : Slot) (H_u : Block V)
    (u : V) : HeldEarlyVoteFor C A Φ s H_u u ↔ HeldEarlyVoteAt A Φ (C.t_ s + 2 * C.Δ) s H_u u :=
  Iff.rfl

end GoldilocksCorrectness.Statements.Executions
