import Spec.Defs.Store
import Spec.Defs.Nondet

/-!
# The validator client: how an attestation's pairs are filled

The attestation's shape is `Model.lean`'s, and `06_StateTransition.lean` says how processed
attestations move the chain state; this file holds the client rules that fill the height
pair and the finality pair a validator signs. **No rule here reads the store.** Everything
a rule needs from the chain arrives as an argument — `get_fg_vote` (`09_Healing.lean`)
derives those arguments — and the one durable input is the anti-slashing record `Λ`
(`SigningHistory.lean`), which `record_attestation` below is the only writer of.

The strategy, in plain words. `Λ` remembers, per height, the first named target signed
there, whether an empty target was signed there, and the lock — the target of a finality
pair signed there. `finality_pair` signs the offered justification exactly when it is
ahead of the offered finalization and the record allows it; `height_pair` decides the
current-height pair in five cases, the record having precedence over anything new; and
one attestation's own finality pair stands in as the lock its height pair reads, so an
attestation cannot form E1 evidence against itself.

The two pair rules run in order — finality first, then height — and `record_attestation`
makes their writes durable before the attestation is released. In this rendering the pairs
are decided at the round's action instant `a_r` and staged, and the assembled attestation
goes out at the validator's own voting time (`Store.onTick`, `11_Duties.lean`).

## What `get_fg_vote` hands over

`FGVote` below is the tuple `(h_c, T_c, ν, h_j, J, h_F)` the protocol's `get_fg_vote`
returns: the height inputs — the confirmed state's height, target and nonjustifiable
flag, offered together or not at all — and the current-slot head state's justification
and finalization facts. The height inputs are `⊥` exactly when no fresh grade-2 quorum
exists.
-/

set_option autoImplicit false

namespace DC

variable [BlockIds]

/-- The height inputs of an FG vote: `(h_c, T_c, ν)` — the height, target and
    nonjustifiable flag of one chain state, the confirmed state `get_fg_vote` selects.
    One structure rather than three `Option`s, because the three are offered together or
    not at all. -/
structure HeightInputs [BlockIds] where
  /-- `h_c`, the state's height. -/
  h : Nat
  /-- `T_c`, the state's height target. -/
  T : BlockId
  /-- `ν`, the state's nonjustifiable flag. -/
  ν : Bool
deriving DecidableEq

/-- What `get_fg_vote` returns: the height inputs — `⊥` when no fresh grade-2 quorum
    exists — and the justification and finalization facts `(h_j, J, h_F)` of the
    current-slot head's chain state. The client rules below turn these into the two pairs
    an attestation carries. -/
structure FGVote [BlockIds] where
  /-- `(h_c, T_c, ν)`, or `⊥` when no height pair is to be offered. -/
  heightInputs : Option HeightInputs
  /-- `h_j`, the head state's justification height. -/
  h_j : Nat
  /-- `J`, the head state's justified block. -/
  J : BlockId
  /-- `h_F`, the head state's finalization height. -/
  h_F : Nat

/-! ## Figure `finality_pair(Λ, h_j, J, h_F)` -/
/-- The finality pair: sign `(h_j, J)` — a justification not yet finalized — exactly when
    the record allows it: the validator already signed `J` as its target at `h_j`, signed
    no empty target there, and its lock there is empty or `J` itself. No ancestry test:
    the client has no store to read one in. -/
def SigningHistory.finalityPair (Λ : SigningHistory) (h_j : Nat) (J : BlockId)
    (h_F : Nat) : FinalityPair := Id.run do
  if h_j > h_F ∧ Λ.target h_j = some J ∧ ¬ Λ.timeout h_j ∧
      (Λ.lock h_j = ⊥ ∨ Λ.lock h_j = some J) then
    return .pair h_j J
  return .empty

/-! ## Figure `height_pair(Λ, h_c, T_c, ν, h_f, T_f)` -/
/-- The height pair, in five cases tried in order, the record having precedence over
    anything new: (1) empty inputs sign the empty pair; (2) a recorded timeout repeats as
    an empty-target vote; (3) a lock repeats when it is the offered target, and otherwise
    the height is waited out with the empty pair — where the lock read is `Λ.lock[h_c]`
    **unless this attestation's own finality pair is at `h_c`, whose target then stands in**,
    so one attestation cannot form E1 evidence against itself; (4) a recorded target
    repeats when it is the offered target; (5) with a silent record, the offered target is
    adopted unless the height is nonjustifiable. Anything else times the height out. -/
def SigningHistory.heightPair (Λ : SigningHistory) (hi : Option HeightInputs)
    (fp : FinalityPair) : HeightPair := Id.run do
  if _ : hi ≠ ⊥ then
    let h := hi.value.h
    let T := hi.value.T
    let ν := hi.value.ν
    -- `lock ← Λ.lock[h_c]; if h_c = h_f then lock ← T_f` — this attestation's own lock
    let mut lock := Λ.lock h
    if fp.h = some h then
      lock ← fp.T
    if Λ.timeout h then                               -- case 2: a timeout repeats
      return .emptyTarget h
    if lock ≠ ⊥ then                                  -- case 3: a lock repeats
      if lock = some T then
        return .target h T
      return .empty                                   --   locked elsewhere: wait out the height
    if Λ.target h ≠ ⊥ then                            -- case 4: a recorded target repeats
      if Λ.target h = some T then
        return .target h T
    else if ¬ ν then                                  -- case 5: no record, adopt the target
      return .target h T
    return .emptyTarget h                             -- otherwise time out at `h_c`
  return .empty                                       -- case 1: nothing offered

/-! ## Figure `record_attestation(Λ, a)` -/
/-- The only writer of `Λ`. It reads exactly the attestation's two pairs, so it takes
    exactly those: a finality pair `(h_f, T_f)` writes the lock at `h_f`; a height pair
    with a named target records it as the height's first target, only when none is
    recorded yet; an empty-target vote sets the height's timeout. The empty pairs write
    nothing. -/
def SigningHistory.recordAttestation (Λ : SigningHistory) (hp : HeightPair)
    (fp : FinalityPair) : SigningHistory := Id.run do
  let mut Λ := Λ
  if _ : fp.h ≠ ⊥ then                                -- `Λ.lock[h_f] ← T_f`
    Λ.lock[fp.h.value] ← fp.T
  if _ : hp.T ≠ ⊥ ∧ hp.h ≠ ⊥ then                    -- the first named target is kept
    if Λ.target hp.h.value = ⊥ then
      Λ.target[hp.h.value] ← hp.T
  if _ : hp.T = ⊥ ∧ hp.h ≠ ⊥ then                    -- `Λ.timeout[h] ← true`
    Λ.timeout[hp.h.value] ← true
  return Λ

end DC
