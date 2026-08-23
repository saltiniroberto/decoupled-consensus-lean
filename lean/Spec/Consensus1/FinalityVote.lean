import Spec.Consensus1.Store

/-!
# The finality-vote rules: how an attestation's pairs are determined

`consensus-1.pdf` gives the attestation its shape (`Attestation` in `Model.lean`) and says
how processed attestations move the chain state (Figure 6), but it does not say how a
validator *fills* the height pair and the finality pair it signs. This file carries that
logic over from the first specification's voting strategy; the working source is its
rendering, `Spec/Defs/Voting.lean` (namespace `Decoupled`), whose module header maps every
definition back to that paper.

The strategy, in plain words. A validator keeps a durable per-height record of what it has
signed — `Σ.H`, a `SigningHistory` (the field in `Store.lean`): whether it signed an
empty target at a height, the first named target it signed there, and the target of the
first finality pair it signed there. Two store rules read that record and the store's
view, and each
returns its pair **and the updated store** — the record write rides the returned store, so
no signature is released before its record is durable:

* `Store.finalityVote` signs `(h_j, J)` — the latest justification — exactly when it is
  ahead of the finalization, on its chain, certified, and consistent with the record: the
  validator already signed `J` as its target at `h_j`, signed no empty target there, and
  its recorded finality target there is empty or `J` itself — written on first release.
* `Store.heightVote` signs the current-height pair under the ceiling `Σ.live_confirmed`,
  the block the validator currently takes as confirmed: it repeats what its record forces
  (an empty-target vote or a recorded target), and only with a silent record does it sign
  something new — an empty target when the height is nonjustifiable, else the confirmed
  state's target when that target sits at or below the ceiling.

`Store.fgVote` composes them, finality first, so the finality target written by the
finality rule is visible to the height rule's record read within the same attestation.

## What changed in the crossing, from `Spec/Defs/Voting.lean` to here

Each of these is a decision this file makes, listed so it can be revisited:

* **The rules are store rules, and the record is a store field** (Roberto, 2026-08-23; the
  first rendering stated them over explicit inputs, with the record threaded through).
  What each rule reads from the store is named in its docstring; the record write is the
  `Σ.H` write in the store it returns. The first rendering's store-free composition layer
  is likewise gone — `Store.fgVote`'s body is the composition.
* **The pair encodings are this subtree's.** The first rendering's `.timeout k` is
  `HeightPair.emptyTarget k` here, and its `.commit h J` is `FinalityPair.pair h J`; the
  record write `saveTimeout` is renamed `saveEmptyTarget` to match.
* **The ceiling is `Σ.live_confirmed`, and it always exists.** The first rendering's
  confirmed block was an `Option` — with none confirmed, the height rule signed nothing.
  This store's `live_confirmed` is a block from genesis on, so that case is
  unrepresentable and gone.
* **The context is the confirmed block's stored state, and the read raises.** The first
  rendering advanced that state to the action's slot (its `process_slots`) and answered
  with an empty pair when no state was recorded. This subtree stores post-states only and
  has no slot-advance on states, so the stored state is read as it is; and a confirmed
  block without a recorded state marks a store the handlers cannot build, so the read
  raises — the subtree's rule — instead of degrading to an empty pair.
* **The context target is always a block.** This subtree's `ChainState.T_h` is never `⊥`,
  so the first rendering's empty-target-field arm of its last case has nothing to match
  and is gone.
* **The two heights coincide, so their comparisons are gone.** The first rendering
  distinguished the current height `k` from the height `hC` of the confirmed block's own
  state only for a branch it never rendered; over the store both are the confirmed state's
  height, so its `hC ≥ k` conditions hold outright and are not written.
* **The round is the store's.** `r = round(Σ.s)`, as the SG duty derives it; the first
  rendering took `r` as an argument.
* **Two inputs stay explicit, as they were.** `head`: the rule producing the SG head is a
  separate concern (this subtree's confirmation rule), so the head the attestation carries
  is passed in. `hasJC`: whether the validator knows a justification certificate for
  `(h_j, J)` is knowledge of evidence, which nothing here models; it enters as a `Bool`.
-/

set_option autoImplicit false

namespace Consensus1

variable {Validator : Type} [Roots] [DecidableEq Validator] [Params]

/-- What a signing rule produces: the signed thing — a pair, or the whole attestation —
    and the store afterwards, its `Σ.H` already carrying the rule's record write. The
    `DutyResult` move, for the same reason: a named structure where a bare pair would
    make the caller remember which component is which. -/
structure SigningResult (Validator : Type) [Roots] (α : Type) where
  /-- What the rule signed. -/
  signed : α
  /-- The store afterwards. -/
  state : Store Validator

/-- The current-height signing rule: which height pair to sign, in five cases tried in
    order, the record having precedence over anything new.

    Reads from the store: the record `Σ.H`, the ceiling `Σ.live_confirmed` — the validator
    vouches for nothing beyond it, so a target is signed only when it lies on that block's
    chain — and, through the raising read of the ceiling's stored state, the current
    height `h`, its target and the nonjustifiable flag.

    The cases: (1) an empty target already signed at `h` is repeated; (2) a recorded
    finality target at `h` is repeated as a target; (3) a named target already signed at
    `h` is repeated, and when it
    no longer sits below the ceiling, an empty target is signed instead; (4) with a silent
    record and the height nonjustifiable, an empty target is signed; (5) with a silent
    record otherwise, the state's target is signed when it sits below the ceiling, else an
    empty target. A case that signs something new writes the record in the store it
    returns; a repeat returns the store untouched. -/
def Store.heightVote (S : Store Validator) :
    ResultOrExcept (SigningResult Validator (HeightPair Validator)) := do
  let mut S := S
  let C := S.liveConfirmed
  let σC ← S.σ[C]
  let h := σC.h
  if S.H.signedEmptyTarget h then                   -- case 1: repeat the empty target
    return { signed := .emptyTarget h, state := S }
  if S.H.finalityTarget h ≠ ⊥ then                  -- case 2: repeat the finality target
    let finalityTarget ← S.H.finalityTarget h
    if finalityTarget ⪯ C then return { signed := .target h finalityTarget, state := S }
    return { signed := .empty, state := S }
  if S.H.firstTarget h ≠ ⊥ then                     -- case 3: repeat the named target
    let target ← S.H.firstTarget h
    if target ⪯ C then return { signed := .target h target, state := S }
    S.H ← S.H.saveEmptyTarget h
    return { signed := .emptyTarget h, state := S }
  if σC.nj then                                     -- case 4: no record, nonjustifiable
    S.H ← S.H.saveEmptyTarget h
    return { signed := .emptyTarget h, state := S }
  let T := σC.T_h                                   -- case 5: no record, sign the state's
  if T ⪯ C then                                     --   target when it sits below `C`
    S.H ← S.H.saveTarget h T
    return { signed := .target h T, state := S }
  S.H ← S.H.saveEmptyTarget h
  return { signed := .emptyTarget h, state := S }

/-- The finality signing rule: sign `(h_j, J)` — the latest justification, read with its
    height and the finalization from the store — exactly when it is ahead of the
    finalization (`h_F < h_j`), on its chain (`F ⪯ J`), certified (`hasJC`), and
    consistent with the record: the validator already signed `J` as its target at `h_j`,
    signed no empty target there, and its recorded finality target there is empty or `J`
    itself. That record is written into the returned store on first release; the rule is
    total — every branch returns. -/
def Store.finalityVote (S : Store Validator) (hasJC : Bool) :
    SigningResult Validator (FinalityPair Validator) := Id.run do
  let mut S := S
  if S.h_F < S.h_j ∧ S.F ⪯ S.J ∧ hasJC ∧ S.H.firstTarget S.h_j = some S.J ∧
      ¬ S.H.signedEmptyTarget S.h_j ∧
      (S.H.finalityTarget S.h_j = ⊥ ∨ S.H.finalityTarget S.h_j = some S.J) then
    S.H ← S.H.saveFinalityTarget S.h_j S.J
    return { signed := .pair S.h_j S.J, state := S }
  return { signed := .empty, state := S }

/-- The combined attestation: the two pair rules evaluated **in order** — first the
    finality pair, whose record write rides the store the current-height rule then reads.
    That ordering is what keeps the two pairs of one attestation from contradicting each
    other; the claim itself is `Analysis/` matter. The round is `round(Σ.s)`; `head` and
    `hasJC` stay explicit — see the module header. The head is carried, not derived. -/
def Store.fgVote (i : Validator) (S : Store Validator) (head : Option (Block Validator))
    (hasJC : Bool) : ResultOrExcept (SigningResult Validator (Attestation Validator)) := do
  let fin := S.finalityVote hasJC                   -- first the finality pair
  let ht ← fin.state.heightVote                     -- then the current-height pair
  return { signed := Attestation.mk (validator := i) (round := round S.s) (head := head)
             (heightPair := ht.signed) (finalityPair := fin.signed),
           state := ht.state }

end Consensus1
