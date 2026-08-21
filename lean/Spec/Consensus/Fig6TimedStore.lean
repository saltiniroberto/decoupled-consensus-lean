import Spec.Consensus.Fig5RoundRoots

/-!
# Figure 6 — Timed store

The two handlers that drive the timed store of Definition 10: `on_tick`, invoked whenever
time advances — scheduled instants are not skipped — and `on_attestation`, for an
attestation received directly or in a block. The store's timed fields themselves live on
`Store` in `Fig2FinalityStore.lean`, landed field by field as the figures consumed them;
with this file every Definition 10 field has its writer.

The `-- line n` comments use Figure 6's own line numbering, in the draft as of 2026-08-19.

## `propose_block` and the proposer are parameters

Line 5's test "this validator is the opening proposer" and line 6's `propose_block(Σ)` both
belong to the draft's Section 6, which is not drafted, and proposer assignment is outside
the draft's scope. So `on_tick` takes both as explicit parameters — the sanctioned shape
for a notion the draft has not yet written — and nothing here claims what proposing does.
The figure writes line 6 as a bare call; the parameter's type lets it mutate the store,
which Section 6 will settle.

## Both handlers return `ResultOrExcept`

`on_tick`'s lines 8 and 10 derive the round's SG and action roots, and those read `C(Σ)`,
hence the state map per viable leaf — see `viableLeaves` in `Fig2FinalityStore.lean`. A block
in `Σ.T` the map does not record therefore fails the whole tick.

`on_attestation` fails for a different reason: line 18 reads `Σ.head[r][i]`, and the row
bracket raises when there is no entry (`Fig2FinalityStore.lean`). The read is unreachable —
the branch above tested `i ∉ Σ.head[r]` — so this failure never fires on any store; it is the
price of writing line 18 the way the figure writes it, `α.head ≠ Σ.head[r][i]`, rather than
through an `Option` test.

## The `assert` is a reject exit

Line 2's `assert Σ.t < t` is a precondition on the caller. Rendered as: a stale tick —
`t` not past the clock — returns the store unchanged.

## Dispatch is by inversion

"`t = 4Δs` for some slot `s`" is `slotStartingAt t`; the round tests shift `t` by `Δ` and
`6Δ` and ask `roundStartingAt` — see `Fig3Schedule.lean`. The draft's phases never
coincide: a slot start is a multiple of `4Δ`, the two round tests sit at `Δ` and `2Δ` past
one, so at most the `t = t_r` and `t = 4Δs` branches fire together, exactly as the figure
intends at an opening slot's start.
-/

set_option autoImplicit false

namespace Consensus

variable {Validator : Type}

section Handlers
variable [DecidableEq Validator] [Electorate Validator] [Params] [Selection Validator]

/-- `on_tick(Σ, t)` (Figure 6, lines 1–11): set the clock and run the phase scheduled at
    this instant — the slot handler at a slot start, the opening proposer's
    `propose_block` at `t_r`, the SG-root derivation at the opening slot's vote time
    `t_r + Δ`, the action-root derivation at `a_r`. `isOpeningProposer` and `proposeBlock`
    are Section 6's, taken as parameters — see the module header. -/
def onTick (S : Store Validator) (t : Int)
    (isOpeningProposer : Nat → Bool)
    (proposeBlock : Store Validator → Nat → Store Validator) :
    ResultOrExcept (Store Validator) := do
  let mut S := S
  -- line 2: `assert Σ.t < t` — a stale tick leaves the store unchanged
  if ¬ (S.t < t) then
    return S
  S.t ← t                                                     -- line 2: `Σ.t ← t`
  if let some s := slotStartingAt t then                      -- line 3
    S ← onSlot S s                                            -- line 4
  if let some r := roundStartingAt t then                     -- line 5
    if isOpeningProposer r then
      S ← proposeBlock S r                                    -- line 6: `propose_block(Σ)`
  if let some r := roundStartingAt (t - Params.Δ) then        -- line 7: `t = t_r + Δ`
    S.sgRoot[r] ← some (← getSGRoot S r)                      -- line 8
  if let some r := roundStartingAt (t - 6 * Params.Δ) then    -- line 9: `t = a_r`
    S.actionRoot[r] ← some (← getActionRoot S r)              -- line 10
  return S                                                    -- line 11

/-- `on_attestation(Σ, α)` (Figure 6, lines 12–20): ignore an empty head; otherwise keep,
    per round and validator, the first processed nonempty head with its processing time,
    and the time at which a *different* head from the same validator was first processed —
    the equivocation time. Definition 11's support scores read these entries against the
    grade instants. -/
def onAttestation (S : Store Validator) (a : Attestation Validator) :
    ResultOrExcept (Store Validator) := do
  let mut S := S
  let i := a.validator                                        -- line 13
  let r := a.round
  -- line 14: `if α.head = ⊥ then return Σ`
  let some H := a.head | return S                             -- line 15
  if i ∉ S.head[r] then                                       -- line 16: `i ∉ Σ.head[r]`
    S.head[r][i] ← (H, S.t)                                   -- line 17
  else if H ≠ (← S.head[r][i]).1 ∧ i ∉ S.equiv[r] then        -- line 18
    S.equiv[r][i] ← S.t                                       -- line 19
  return S                                                    -- line 20

end Handlers

end Consensus
