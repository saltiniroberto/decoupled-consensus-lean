import SpecM.Defs.Store
import SpecM.Defs.Nondet

/-!
# The finality-vote rules: how an attestation's pairs are determined

The attestation's shape is `Model.lean`'s, and `06_StateTransition.lean` says how processed attestations
move the chain state; this file holds the rule a validator uses to *fill* the height pair
and the finality pair it signs.

The strategy, in plain words. A validator keeps a durable per-height record of what it has
signed — `Σ.history`, a `SigningHistory` (the field in `Store.lean`): whether it signed an
empty target at a height, the first named target it signed there, and the target of the
first finality pair it signed there. Two rules read that record and the store's
view, and each carries its record write out with its pair, so no signature is released
before its record is durable:

* `Store.finalityVote` signs `(h_j, J)` — the latest justification — exactly when it is
  ahead of the finalization, on its chain, and consistent with the record: the
  validator already signed `J` as its target at `h_j`, signed no empty target there, and
  its recorded finality target there is empty or `J` itself — written on first release.
  It takes the store and returns it beside the pair.
* `heightVote` signs the current-height pair under the ceiling `Σ.live_confirmed`,
  the block the validator currently takes as confirmed: it repeats what its record forces
  (an empty-target vote or a recorded target), and only with a silent record does it sign
  something new — an empty target when the height is nonjustifiable, else the confirmed
  state's target when that target sits at or below the ceiling. **It threads the store
  through the monad instead**: it is a `DRES` (`Store.lean`), naming no store at its
  signature and returning the pair alone, and its two record writes are the named
  routines `recordEmptyTarget` and `recordTarget` below.

The two shapes standing side by side is what this copy of the spec exists to compare.

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

/-- Record that an empty target was signed at height `h`. The write the height rule's
    cases 3, 4 and 5 make when they sign an empty target with nothing recorded to repeat;
    it writes `Σ.history` and nothing else. -/
def recordEmptyTarget (h : Nat) : DRES Validator Unit :=
  modify fun S => { S with history := S.history.saveEmptyTarget h }

/-- Record `T` as the target signed at height `h`. The write the height rule's case 5
    makes when it signs the confirmed state's target; it writes `Σ.history` and nothing
    else. -/
def recordTarget (h : Nat) (T : Block Validator) : DRES Validator Unit :=
  modify fun S => { S with history := S.history.saveTarget h T }

/-- The current-height signing rule: which height pair to sign, in five cases tried in
    order, the record having precedence over anything new.

    The store is threaded rather than passed: the rule is a `DRES`, so no store appears at
    its signature and none is returned beside the pair (`Store.lean`). A caller holding a
    store runs it — `heightVote.run S`.

    Reads from the store: the record `Σ.history`, the ceiling `Σ.live_confirmed` — the validator
    vouches for nothing beyond it, so a target is signed only when it lies on that block's
    chain — and, through the raising read of the ceiling's stored state, the current
    height `h`, its target and the nonjustifiable flag. All five reads are taken from one
    binding of the store, `let S ← get`, made before any case runs; that binding is a
    value, so it does not see the record writes below, and no case reads after writing.

    The cases: (1) an empty target already signed at `h` is repeated; (2) a recorded
    finality target at `h` is repeated as a target; (3) a named target already signed at
    `h` is repeated, and when it
    no longer sits below the ceiling, an empty target is signed instead; (4) with a silent
    record and the height nonjustifiable, an empty target is signed; (5) with a silent
    record otherwise, the state's target is signed when it sits below the ceiling, else an
    empty target. A case that signs something new records it before returning; a repeat
    records nothing.
-/
def heightVote : DRES Validator (HeightPair Validator) := do
  let S ← get
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
    recordEmptyTarget h
    return .emptyTarget h
  if σC.nj then                                     -- case 4: no record, nonjustifiable
    recordEmptyTarget h
    return .emptyTarget h
  let T := σC.T_h                                   -- case 5: no record, sign the state's
  if T ⪯ C then                                     --   target when it sits below `C`
    recordTarget h T
    return .target h T
  recordEmptyTarget h
  return .emptyTarget h

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
    no signature is released before its record is durable. What reaches the wire is an
    attestation, which adds a head and a round to these two pairs; assembling and
    broadcasting one is the concern of whoever holds the head, not of the rules that fill
    the pairs.
-/
def Store.fgVote (S : Store Validator) :
    DRE (VoteAndStore Validator (FGVote Validator)) := do
  let { vote := fp, state := S } := S.finalityVote  -- first the finality pair
  let (hp, S) ← heightVote.run S                    -- then the current-height pair
  return { vote := { heightPair := hp, finalityPair := fp }, state := S }

end DC
