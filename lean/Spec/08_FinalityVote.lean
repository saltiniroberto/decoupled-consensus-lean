import Spec.Defs.Store
import Spec.Defs.Nondet

/-!
# The finality-vote rules: how an attestation's pairs are determined

The attestation's shape is `Model.lean`'s, and `06_StateTransition.lean` says how processed attestations
move the chain state; this file holds the rule a validator uses to *fill* the height pair
and the finality pair it signs.

The strategy, in plain words. A validator keeps a durable per-height record of what it has
signed — `Σ.history`, a `SigningHistory` (the field in `Store.lean`): whether it signed an
empty target at a height, the first named target it signed there, and the target of the
first finality pair it signed there. Two store rules read that record and the store's
view, and each
returns its pair **and the updated store** — the record write rides the returned store, so
no signature is released before its record is durable:

* `Store.finalityVote` signs `(h_j, J)` — the latest justification — exactly when it is
  ahead of the finalization, on its chain, and consistent with the record: the
  validator already signed `J` as its target at `h_j`, signed no empty target there, and
  its recorded finality target there is empty or `J` itself — written on first release.
* `Store.heightVote` signs the current-height pair under the ceiling `Σ.live_confirmed`,
  the block the validator currently takes as confirmed: it repeats what its record forces
  (an empty-target vote or a recorded target), and only with a silent record does it sign
  something new — an empty target when the height is nonjustifiable, else the confirmed
  state's target when that target sits at or below the ceiling.

`Store.fgVote` composes them, finality first, so the finality target written by the
finality rule is visible to the height rule's record read within the same vote, and
returns the two pairs as one `FGVote` with the store that carries both record writes. The
wire object is an attestation, which adds a head and a round; assembling and broadcasting
one belongs to whoever holds the head.
-/

set_option autoImplicit false

namespace DC

variable {Validator : Type} [Roots] [DecidableEq Validator] [Params]

/-- What a signing rule produces: the vote it signed — a height pair, a finality pair, or
    the two together — and the store afterwards, its `Σ.history` already carrying the
    rule's record write. A named structure, where a bare product would make the caller
    remember which component is which. -/
structure VoteAndStore (Validator : Type) [Roots] (α : Type) where
  /-- The vote the rule signed. -/
  vote : α
  /-- The store afterwards. -/
  state : Store Validator

/-- An FG vote: the two pairs a validator signs for the current height and for the
    finality it commits to. It is not itself a wire object — an attestation carries these
    two pairs together with a head and a round — so nothing outside the pairs belongs
    here. -/
structure FGVote (Validator : Type) [Roots] where
  /-- The current-height pair. -/
  heightPair : HeightPair Validator
  /-- The finality pair. -/
  finalityPair : FinalityPair Validator

/-- The current-height signing rule: which height pair to sign, in five cases tried in
    order, the record having precedence over anything new.

    Reads from the store: the record `Σ.history`, the ceiling `Σ.live_confirmed` — the validator
    vouches for nothing beyond it, so a target is signed only when it lies on that block's
    chain — and, through the raising read of the ceiling's stored state, the current
    height `h`, its target and the nonjustifiable flag.

    The cases: (1) an empty target already signed at `h` is repeated; (2) a recorded
    finality target at `h` is repeated as a target; (3) a named target already signed at
    `h` is repeated, and when it
    no longer sits below the ceiling, an empty target is signed instead; (4) with a silent
    record and the height nonjustifiable, an empty target is signed; (5) with a silent
    record otherwise, the state's target is signed when it sits below the ceiling, else an
    empty target. It touches no store field: `decide_height_vote` below is what records the
    signing and stores the pair.
-/
def Store.computeHeightVote (S : Store Validator) :
    DRE (HeightPair Validator) := do
  let C := S.liveConfirmed
  let σC ← S.σ[C]
  let h := σC.h
  if S.history.signedEmptyTarget h then                   -- case 1: repeat the empty target
    return .emptyTarget h
  if S.history.finalityTarget h ≠ ⊥ then                  -- case 2: repeat the finality target
    let finalityTarget ← S.history.finalityTarget h
    if finalityTarget ⪯ C then
      return .target h finalityTarget
    return .empty
  if S.history.firstTarget h ≠ ⊥ then                     -- case 3: repeat the named target
    let target ← S.history.firstTarget h
    if target ⪯ C then
      return .target h target
    return .emptyTarget h
  if σC.nj then                                     -- case 4: no record, nonjustifiable
    return .emptyTarget h
  let T := σC.T_h                                   -- case 5: no record, sign the state's
  if T ⪯ C then                                     --   target when it sits below `C`
    return .target h T
  return .emptyTarget h

/-- Sign the height pair `compute_height_vote` chose: store it as `Σ.height_pair`, and make
    its record durable — a named target as the height-`h` first target, an empty target as
    the height-`h` empty-target flag, the empty pair recording nothing.

    Both writes overwrite with the value a repeat already holds, so signing a pair the record
    already carries leaves the record unchanged. The one case where the write is new to this
    routine is a finality target repeated as a height target: it is now recorded as the
    height-`h` first target as well. -/
def Store.decideHeightVote (S : Store Validator) :
    DRE (Store Validator) := do
  let mut S := S
  let hp ← S.computeHeightVote
  match hp with
  | .target h T => S.history ← S.history.saveTarget h T
  | .emptyTarget h => S.history ← S.history.saveEmptyTarget h
  | .empty => pure ()
  S.heightPair ← hp
  return S

/-- The finality signing rule: sign `(h_j, J)` — the latest justification, read with its
    height and the finalization from the store — exactly when it is ahead of the
    finalization (`h_F < h_j`), on its chain (`F ⪯ J`), and consistent with the record:
    the validator already signed `J` as its target at `h_j`, signed no empty target
    there, and its recorded finality target there is empty or `J` itself. That record is
    written into the returned store on first release; the rule is total — every branch
    returns. No separate knowledge of the justification is asked for: justification is an
    on-chain fact — `Σ.J` and `Σ.h_j` read off replayed states whose justifying
    attestations sit inside blocks the validator has processed — so a coherent store's
    own chain is the evidence.
-/
def Store.finalityVote (S : Store Validator) :
    VoteAndStore Validator (FinalityPair Validator) := Id.run do
  let mut S := S
  if S.h_F < S.h_j ∧ S.F ⪯ S.J ∧ S.history.firstTarget S.h_j = S.J ∧
      ¬ S.history.signedEmptyTarget S.h_j ∧
      (S.history.finalityTarget S.h_j = ⊥ ∨ S.history.finalityTarget S.h_j = S.J) then
    S.history ← S.history.saveFinalityTarget S.h_j S.J
    return { vote := .pair S.h_j S.J, state := S }
  return { vote := .empty, state := S }

/-- The FG vote: the two pair rules evaluated **in order** — first the finality pair,
    whose record write rides the store the current-height rule then reads. That ordering
    is what keeps the two pairs of one vote from contradicting each other; the claim
    itself is `Analysis/` matter.

    It returns the vote and the store, whose `Σ.history` carries both record writes — so
    no signature is released before its record is durable. The height pair is read back from
    the `Σ.height_pair` that `decide_height_vote` wrote. What reaches the wire is an
    attestation, which adds a head and a round to these two pairs; assembling and
    broadcasting one is the concern of whoever holds the head, not of the rules that fill
    the pairs.
-/
def Store.fgVote (S : Store Validator) :
    DRE (VoteAndStore Validator (FGVote Validator)) := do
  let { vote := fp, state := S } := S.finalityVote  -- first the finality pair
  let S ← S.decideHeightVote                        -- then the current-height pair
  return { vote := { heightPair := S.heightPair, finalityPair := fp }, state := S }

end DC
