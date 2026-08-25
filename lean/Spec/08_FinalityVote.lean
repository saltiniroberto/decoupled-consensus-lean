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
finality rule is visible to the height rule's record read within the same attestation.
-/

set_option autoImplicit false

namespace DC

variable {Validator : Type} [Roots] [DecidableEq Validator] [Params]

/-- What a pair rule produces: the height or finality pair it signed, and the store
    afterwards, its `Σ.history` already carrying the rule's record write. A named structure,
    where a bare product would make the caller remember which component is which. -/
structure SigningResult (Validator : Type) [Roots] (α : Type) where
  /-- The pair the rule signed. -/
  pair : α
  /-- The store afterwards. -/
  state : Store Validator

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
    empty target. A case that signs something new writes the record in the store it
    returns; a repeat returns the store untouched.
-/
def Store.heightVote (S : Store Validator) :
    DRE (SigningResult Validator (HeightPair Validator)) := do
  let mut S := S
  let C := S.liveConfirmed
  let σC ← S.σ[C]
  let h := σC.h
  if S.history.signedEmptyTarget h then                   -- case 1: repeat the empty target
    return { pair := .emptyTarget h, state := S }
  if S.history.finalityTarget h ≠ ⊥ then                  -- case 2: repeat the finality target
    let finalityTarget ← S.history.finalityTarget h
    if finalityTarget ⪯ C then
      return { pair := .target h finalityTarget, state := S }
    return { pair := .empty, state := S }
  if S.history.firstTarget h ≠ ⊥ then                     -- case 3: repeat the named target
    let target ← S.history.firstTarget h
    if target ⪯ C then
      return { pair := .target h target, state := S }
    S.history ← S.history.saveEmptyTarget h
    return { pair := .emptyTarget h, state := S }
  if σC.nj then                                     -- case 4: no record, nonjustifiable
    S.history ← S.history.saveEmptyTarget h
    return { pair := .emptyTarget h, state := S }
  let T := σC.T_h                                   -- case 5: no record, sign the state's
  if T ⪯ C then                                     --   target when it sits below `C`
    S.history ← S.history.saveTarget h T
    return { pair := .target h T, state := S }
  S.history ← S.history.saveEmptyTarget h
  return { pair := .emptyTarget h, state := S }

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
    SigningResult Validator (FinalityPair Validator) := Id.run do
  let mut S := S
  if S.h_F < S.h_j ∧ S.F ⪯ S.J ∧ S.history.firstTarget S.h_j = S.J ∧
      ¬ S.history.signedEmptyTarget S.h_j ∧
      (S.history.finalityTarget S.h_j = ⊥ ∨ S.history.finalityTarget S.h_j = S.J) then
    S.history ← S.history.saveFinalityTarget S.h_j S.J
    return { pair := .pair S.h_j S.J, state := S }
  return { pair := .empty, state := S }

/-- The FG duty: the two pair rules evaluated **in order** — first the finality pair,
    whose record write rides the store the current-height rule then reads. That ordering
    is what keeps the two pairs of one attestation from contradicting each other; the
    claim itself is `Analysis/` matter.

    A `NDREB` duty, as every duty: the attestation leaves by `broadcast` —
    `Message.attestation`, the wire decision recorded on that constructor — and the
    returned store carries both record writes. The signer is the store's own `Σ.id`; the
    round is `round(Σ.s)`; `head` stays explicit — producing the SG head is the
    confirmation rule's concern, so the attestation carries the head it is given rather
    than deriving one.
-/
def Store.fgVote (S : Store Validator) (head : Option (Block Validator)) :
    NDREB Validator (Store Validator) := do
  let { pair := fp, state := S } := S.finalityVote  -- first the finality pair
  let { pair := hp, state := S } ← S.heightVote     -- then the current-height pair
  broadcast (Message.attestation (Attestation.mk (validator := S.id)
    (round := round S.s) (head := head) (heightPair := hp) (finalityPair := fp)))
  return S

end DC
