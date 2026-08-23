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
signed (`SigningHistory`): whether it signed an empty target at a height, the first named
target it signed there, and the first finality-pair target it locked there. Two pure rules
read that record and the validator's current view, and each returns its pair **and the
updated record** — the write is part of the rule, so that no signature is released before
its record is durable:

* `finalityVote` signs `(h_j, J)` — the latest justification — exactly when it is ahead of
  the finalization, on its chain, certified, and consistent with the record: the validator
  already signed `J` as its target at `h_j`, signed no empty target there, and locked
  nothing else there. It locks `J` at `h_j` on first release.
* `heightVote` signs the current-height pair under a ceiling `C`, the block the validator
  currently takes as confirmed: it repeats what its record forces (an empty-target vote or
  a recorded target), and only with a silent record does it sign something new — an empty
  target when the height is nonjustifiable, else the context's target when that target
  sits at or below `C`.

`fgVote` composes them, finality first, so the lock written by the finality rule is
visible to the height rule's record read within the same attestation. `Store.fgVote` wires
the rules over this subtree's store.

## What changed in the crossing, from `Spec/Defs/Voting.lean` to here

Each of these is a decision this file makes, listed so it can be revisited:

* **The pair encodings are this subtree's.** The first rendering's `.timeout k` is
  `HeightPair.emptyTarget k` here, and its `.commit h J` is `FinalityPair.pair h J`; the
  record write `saveTimeout` is renamed `saveEmptyTarget` to match.
* **The store supplies all four fork-choice fields.** `(J, h_j)` and `(F, h_F)` are
  `Σ.J`, `Σ.h_j`, `Σ.F`, `Σ.h_F`. The first rendering kept `h_F` an explicit argument
  because its store had no such field; this store does.
* **The confirmed block is `Σ.live_confirmed`.** The first rendering's stand-in was its
  store's confirmation pick; this subtree's is the block the last evaluated slot
  confirmed.
* **The context state is `Σ.σ[live_confirmed]`, and the read raises.** The first
  rendering advanced the confirmed block's state to the action's slot (its `process_slots`)
  and answered with an empty pair when no state was recorded. This subtree stores
  post-states only and has no slot-advance on states, so the stored state is read as it
  is; and a confirmed block without a recorded state marks a store the handlers cannot
  build, so the read raises — the subtree's rule — instead of degrading to an empty pair.
* **The context target is always a block.** This subtree's `ChainState.T_h` is never `⊥`,
  so the first rendering's fallback for an empty target field has nothing to fall back
  from and is gone: the context's `T` is `some σ.T_h`.
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

/-- The durable signing record a validator keeps per height: whether it signed an
    empty-target vote at `h`, the first named target it signed at `h`, and the target of
    the first finality pair it signed at `h`. The rules below return the updated record
    together with the pair they sign, so every write completes before the signature is
    released. -/
structure SigningHistory (Validator : Type) [Roots] where
  /-- `τ(h)`: an empty-target vote `(h, ⊥)` was signed at height `h`. -/
  τ : Nat → Bool
  /-- `T(h)`: the first named target signed at height `h`. -/
  T : Nat → Option (Block Validator)
  /-- `lock(h)`: the target in the first finality pair signed at height `h`. -/
  lock : Nat → Option (Block Validator)

/-- The record of a validator that has signed nothing anywhere: every validator's start. -/
def SigningHistory.gen : SigningHistory Validator where
  τ _ := false
  T _ := ⊥
  lock _ := ⊥

/-- The durable write behind signing an empty-target vote `(k, ⊥)`. -/
def SigningHistory.saveEmptyTarget (H : SigningHistory Validator) (k : Nat) :
    SigningHistory Validator :=
  { H with τ := Function.update H.τ k true }

/-- The durable write behind signing a first named target `(k, T)`. -/
def SigningHistory.saveTarget (H : SigningHistory Validator) (k : Nat)
    (T : Block Validator) : SigningHistory Validator :=
  { H with T := Function.update H.T k (some T) }

/-- The durable write behind a finality pair's first release: lock `J` at `k`. -/
def SigningHistory.saveLock (H : SigningHistory Validator) (k : Nat)
    (J : Block Validator) : SigningHistory Validator :=
  { H with lock := Function.update H.lock k (some J) }

/-- The current-height signing rule: which height pair to sign, in five cases tried in
    order, the record having precedence over anything new.

    `C` is the ceiling: the block the validator currently takes as confirmed, and it
    vouches for nothing beyond it — a target is signed only when it lies on `C`'s chain
    (`T ⪯ C`), an empty target only when `C`'s own state has reached the height (`hC ≥ k`),
    and with `C = ⊥` nothing is signed at all. `k` is the current height, `T` the context's
    target for it, `ν` whether the height is nonjustifiable, `hC` the height of `C`'s own
    state (`Store.fgVote` passes `hC = k`), and `H` the durable record.

    The cases: (1) an empty target already signed at `k` is repeated; (2) a lock at `k` is
    repeated as a target; (3) a named target already signed at `k` is repeated, and when it
    no longer sits below `C`, an empty target is signed instead; (4) with a silent record
    and `ν`, an empty target is signed; (5) with a silent record and `¬ν`, the context's
    target is signed when it sits below `C`, else an empty target. Every empty-target
    signing requires `hC ≥ k`, and every branch that cannot sign returns the empty pair
    with the record untouched. -/
def heightVote (C : Option (Block Validator)) (k : Nat) (T : Option (Block Validator))
    (ν : Bool) (hC : Nat) (H : SigningHistory Validator) :
    HeightPair Validator × SigningHistory Validator :=
  if hc : C.isSome then
    let Cg := C.get hc
    if H.τ k then                                    -- case 1: repeat the empty target
      if hC ≥ k then (.emptyTarget k, H) else (.empty, H)
    else if hl : (H.lock k).isSome then              -- case 2: repeat the lock
      let T_L := (H.lock k).get hl
      if T_L ⪯ Cg then (.target k T_L, H) else (.empty, H)
    else if ht : (H.T k).isSome then                 -- case 3: repeat the named target
      let T₀ := (H.T k).get ht
      if T₀ ⪯ Cg then (.target k T₀, H)
      else if hC ≥ k then (.emptyTarget k, H.saveEmptyTarget k)
      else (.empty, H)
    else if ν then                                   -- case 4: no record, nonjustifiable
      if hC ≥ k then (.emptyTarget k, H.saveEmptyTarget k) else (.empty, H)
    else if h0 : T.isSome then                       -- case 5: no record, sign the target
      let T₀ := T.get h0
      if T₀ ⪯ Cg then (.target k T₀, H.saveTarget k T₀)
      else if hC ≥ k then (.emptyTarget k, H.saveEmptyTarget k)
      else (.empty, H)
    else if hC ≥ k then (.emptyTarget k, H.saveEmptyTarget k)
    else (.empty, H)
  else (.empty, H)                                   -- no confirmed block: sign nothing

/-- The finality signing rule: sign `(h_j, J)` — the latest justification — exactly when
    it is ahead of the finalization (`h_F < h_j`), on its chain (`F ⪯ J`), certified
    (`hasJC`), and consistent with the record: the validator already signed `J` as its
    target at `h_j`, signed no empty target there, and locked nothing else there. The lock
    is written on first release; the rule is total — every branch returns. -/
def finalityVote (J : Block Validator) (h_j : Nat) (F : Block Validator) (h_F : Nat)
    (hasJC : Bool) (H : SigningHistory Validator) :
    FinalityPair Validator × SigningHistory Validator :=
  if h_F < h_j ∧ F ⪯ J ∧ hasJC ∧ H.T h_j = some J ∧ H.τ h_j = false ∧
      (H.lock h_j = ⊥ ∨ H.lock h_j = some J) then
    (.pair h_j J, H.saveLock h_j J)
  else (.empty, H)

/-- The combined attestation: the two pair rules evaluated **in order** — first the
    finality pair, whose lock write is visible to the current-height rule's record read.
    That ordering is what keeps the two pairs of one attestation from contradicting each
    other; the claim itself is `Analysis/` matter. The head is carried, not derived. -/
def fgVote (i : Validator) (r : Nat) (head : Option (Block Validator))
    (J : Block Validator) (h_j : Nat) (F : Block Validator) (h_F : Nat) (hasJC : Bool)
    (C : Option (Block Validator)) (k : Nat) (T : Option (Block Validator)) (ν : Bool)
    (hC : Nat) (H : SigningHistory Validator) :
    Attestation Validator × SigningHistory Validator :=
  let (fp, H₁) := finalityVote J h_j F h_F hasJC H     -- first the finality pair
  let (hp, H₂) := heightVote C k T ν hC H₁             -- then the current-height pair
  (Attestation.mk (validator := i) (round := r) (head := head)
    (heightPair := hp) (finalityPair := fp), H₂)

/-- `fgVote` over the store: the fork-choice fields are the store's own
    (`Σ.J`, `Σ.h_j`, `Σ.F`, `Σ.h_F`), the round is `round(Σ.s)`, the confirmed block is
    `Σ.live_confirmed`, and the context is read off that block's stored state — its
    height, its `T_h` (always a block here), its nonjustifiable flag. The read raises when
    the confirmed block has no recorded state; the module header records that this is a
    departure from the first rendering, which answered with an empty pair. `head` and
    `hasJC` stay explicit — see the module header. -/
def Store.fgVote (i : Validator) (S : Store Validator) (head : Option (Block Validator))
    (hasJC : Bool) (H : SigningHistory Validator) :
    ResultOrExcept (Attestation Validator × SigningHistory Validator) := do
  let σC ← S.σ[S.liveConfirmed]
  -- `Consensus1.fgVote`, qualified: inside `Store.fgVote` the bare name is this def itself
  return Consensus1.fgVote
    (i := i)                      -- the signing validator
    (r := round S.s)              -- the attestation's round, from the store's slot
    (head := head)                -- the SG head the attestation carries; passed through
    (J := S.J) (h_j := S.h_j)     -- the latest justification, the store's
    (F := S.F) (h_F := S.h_F)     -- the latest finalization, the store's
    (hasJC := hasJC)              -- knowledge of the certificate; explicit input
    (C := some S.liveConfirmed)   -- the ceiling: the confirmed block
    (k := σC.h)                   -- the current height, the confirmed state's
    (T := some σC.T_h)            -- the context target, never `⊥` in this subtree
    (ν := σC.nj)                  -- the nonjustifiable flag, the confirmed state's
    (hC := σC.h)                  -- the confirmed state's height; equal to `k` here
    (H := H)                      -- the durable record, threaded through both rules

end Consensus1
