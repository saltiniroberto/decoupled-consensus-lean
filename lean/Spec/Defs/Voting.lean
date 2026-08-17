import Spec.HftFig2Store

/-!
# The healing paper's voting strategy — Definitions 12 and 47–50

`height_filter_healing.tex` Definition 12 (`def:signing-history`, lines 522–530), and
`recovery_core.tex` Definitions 47–50: `def:ordinary-current-target` (lines 1814–1869),
`def:height-vote-rule` (lines 1952–1981), `def:finality-vote-rule` (lines 1982–2012),
`def:fg-rule` (lines 2014–2033). Definitions only; the safety result these are built for —
`lem:signer-safety`, honest attestations are never E1- or E2-slashable — is `Analysis/`
work and is not here.

## What is rendered, and from which sentences

The signing rules are stated by the paper over explicit inputs — a confirmation gate
`C_i`, a context triple `(k, T, ν)`, the fork-choice fields `(J, h_j)` and `(F, h_F)`,
and the durable history `H_i` — and they are rendered here the same way: `heightVote` and
`finalityVote` are pure functions of those inputs, returning the signed pair **and the
updated history**, because the paper's "record and sign" and "writes each value before
releasing the signature" (Definition 12) make the write part of the rule. `fgVote` is
Definition 50's composition, finality first, so the lock write is visible to the
current-height rule's history read — the ordering the paper stresses, because it is what
keeps one attestation from being its own E1 pair.

## The hybrid supplies the inputs

`ordinaryContext` and `ordinaryVote` wire the rules over this project's store:

* **The gate is `getConfirmed`.** The paper's gate is `Q_i^r`, the deepest official
  confirmation (Definition 46, `def:official-confirmation`), whose derivation needs the
  recovery apparatus (grades, TSQ views, rounds — Definitions 28–46, none rendered). In
  the declared hybrid the store's own confirmation function stands in; the companion
  paper's voting rule (its Figure 4, `hft:alg:voting-rule`) reads its gate from
  `get_confirmed` the same way.
* **The context triple is Definition 47's own no-source-proposal branch.** Definition 47
  distinguishes a source-proposal case from a fallback the paper states explicitly: "it
  uses `Y_i = Q_i^r` and `σ_i = σ̄_i = σ_a[Q_i^r]` directly" (lines 1819–1823). That
  branch is what `ordinaryContext` renders: `σ_i` is the gate's finality action state —
  `process_slots(σ[X], slot)` per Definition 20 (`def:finality-action-state`), which the
  store's map makes spec-computable — and `(k, ν) = (σ_i.h, σ_i.nj)` with the target
  fallback of lines 1858–1860: `T_i = σ_i.T_h`, or `Y_i` itself when that field is empty
  and `Y_i.slot ≥ σ_i.s_h`. The source-proposal case needs round records this project
  does not have, and is not rendered.
* **Two inputs stay explicit, deliberately.** `h_F`: Definition 49 reads `(F, h_F)` from
  the fork-choice action state, and this project's store carries no `h_F` — Definition 10
  (`hft:def:store`) lists none — so the height is an argument until that gap is decided.
  `hasJC`: Definition 49's "it knows the justification certificate `JC(h_j, J)`"
  (Definition 21, `def:certificates`) is knowledge of evidence, a fact about what the
  validator has seen; it enters as a `Bool` and the execution layer will discharge it.

## What is deliberately absent

Definitions 28–46 (recovery timing, grades, official confirmations, source proposals),
the SG head derivation — `head` is an input, as Definition 50's attestation just carries
it — and the action schedule (when a validator votes), which is what would wire these
into `Spec/Protocol.lean`'s reaction and is a separate `NodeState` decision. Definition
12's "restores the values after restart" is about crashes, which the framework does not
model; the history is a value threaded through the rules here.
-/

set_option autoImplicit false

namespace Decoupled

open scoped Decoupled
open Framework.StsMultisetLog

variable {Node Root : Type}

/-- Definition 12 (`def:signing-history`, lines 522–530): "Validator `i` durably stores,
    for each height `h`, its first nonempty target `H_i.T(h)`, whether it signed a timeout
    `H_i.τ(h)`, and the target in its first finality pair `H_i.lock(h)`."

    One record per sentence clause; heights the validator never acted at hold `false`/`⊥`,
    which is what `gen` says. The definition's write discipline — "writes each value
    before releasing the signature" — is carried by the rules below returning the updated
    history together with the pair. -/
structure SigningHistory (Node Root : Type) where
  /-- `H_i.τ(h)`: a timeout was signed at height `h`. -/
  τ : Nat → Bool
  /-- `H_i.T(h)`: the first nonempty target signed at height `h`. -/
  T : Nat → Option (Blk Node Root)
  /-- `H_i.lock(h)`: the target in the first finality pair signed at height `h`. -/
  lock : Nat → Option (Blk Node Root)

namespace SigningHistory

/-- A history with nothing signed anywhere: every validator's starting point. -/
def gen : SigningHistory Node Root where
  τ _ := false
  T _ := ⊥
  lock _ := ⊥

/-- The durable write behind Definition 48's "record and sign `(k, ⊥)`". -/
def saveTimeout (H : SigningHistory Node Root) (k : Nat) : SigningHistory Node Root :=
  { H with τ := Function.update H.τ k true }

/-- The durable write behind Definition 48's "record and sign `(k, T)`": the first
    nonempty target at `k`. -/
def saveTarget (H : SigningHistory Node Root) (k : Nat) (T : Blk Node Root) :
    SigningHistory Node Root :=
  { H with T := Function.update H.T k (some T) }

/-- The durable write behind Definition 49's "records `H_i.lock(h_j) = J` before first
    release". -/
def saveLock (H : SigningHistory Node Root) (k : Nat) (J : Blk Node Root) :
    SigningHistory Node Root :=
  { H with lock := Function.update H.lock k (some J) }

end SigningHistory

section
variable [DecidableEq Node] [DecidableEq Root]

/-- Definition 48 (`def:height-vote-rule`, lines 1952–1981): the current-height signing
    rule, "choose in this order". `C` is the confirmation gate `C_i` (`⊥` → "the
    current-height pair is empty", line 1957); `(k, T, ν)` is Definition 47's context;
    `hC` is `σ_a[C_i].h`, the gate's closed-state height the rule compares against `k`
    (in `ordinaryVote`'s wiring the context state *is* the gate's, so `hC = k`); `H` is
    the durable history. Returns the pair and the history after the rule's own writes —
    "every durable write completes before signature release" (line 1976).

    The five numbered cases below are the definition's five, in its order — "timeout
    history has precedence over target history" (lines 1976–1977) is the order itself,
    and reaching case 4 or 5 means `τ(k)` false, `lock(k) = ⊥` and `T(k) = ⊥`, the
    definition's "with no history". -/
def heightVote (C : Option (Blk Node Root)) (k : Nat) (T : Option (Blk Node Root))
    (ν : Bool) (hC : Nat) (H : SigningHistory Node Root) :
    HeightPair Node Root × SigningHistory Node Root :=
  if let some Cg := C then
    if H.τ k then                                  -- case 1, lines 1959–1961:
      if hC ≥ k then (.timeout k, H)               --   repeat (k, ⊥) when σ_a[C].h ≥ k…
      else (.empty, H)                             --   …otherwise emit empty
    else if let some T_L := H.lock k then          -- case 2, lines 1962–1963:
      if T_L ⪯ Cg then (.target k T_L, H)          --   repeat (k, T_L) when T_L ⪯ C…
      else (.empty, H)                             --   …otherwise emit empty
    else if let some T₀ := H.T k then              -- case 3, lines 1964–1967:
      if T₀ ⪯ Cg then (.target k T₀, H)            --   repeat (k, T₀) when T₀ ⪯ C
      else if hC ≥ k then                          --   else record and sign (k, ⊥)
        (.timeout k, H.saveTimeout k)              --   when σ_a[C].h ≥ k…
      else (.empty, H)                             --   …otherwise emit empty
    else if ν then                                 -- case 4, lines 1968–1969: no history,
      if hC ≥ k then                               --   ν true: record and sign (k, ⊥)
        (.timeout k, H.saveTimeout k)              --   when σ_a[C].h ≥ k
      else (.empty, H)
    else if let some T₀ := T then                  -- case 5, lines 1970–1974: no history,
      if T₀ ⪯ Cg then                              --   ν false: record and sign (k, T)
        (.target k T₀, H.saveTarget k T₀)          --   when T ≠ ⊥ and T ⪯ C
      else if hC ≥ k then                          --   otherwise record and sign (k, ⊥)
        (.timeout k, H.saveTimeout k)              --   when σ_a[C].h ≥ k
      else (.empty, H)                             --   if neither test passes, emit empty
    else if hC ≥ k then
      (.timeout k, H.saveTimeout k)                -- case 5's T = ⊥ arm, same fallbacks
    else (.empty, H)
  else (.empty, H)                                 -- line 1957: C_i = ⊥ → empty

/-- Definition 49 (`def:finality-vote-rule`, lines 1982–2012): the independent finality
    signing rule. `(J, h_j)` and `(F, h_F)` are the fork-choice action state's fields
    (lines 1984–1989); `hasJC` is "it knows the justification certificate `JC(h_j, J)`"
    (lines 1993–1995), explicit here — see the module header. Signs `(h_j, J)` exactly
    when `h_j > h_F`, `F ⪯ J`, the certificate is known, `H.T(h_j) = J`,
    `H.τ(h_j) = false` and `H.lock(h_j) ∈ {⊥, J}` (lines 1990–1997); "records
    `H_i.lock(h_j) = J` before first release" (line 1997) is the returned history.
    "The rule is total" (line 1989): every branch returns. -/
def finalityVote (J : Blk Node Root) (h_j : Nat) (F : Blk Node Root) (h_F : Nat)
    (hasJC : Bool) (H : SigningHistory Node Root) :
    FinalityPair Node Root × SigningHistory Node Root :=
  if h_F < h_j ∧ F ⪯ J ∧ hasJC ∧ H.T h_j = some J ∧ H.τ h_j = false ∧
      (H.lock h_j = ⊥ ∨ H.lock h_j = some J) then
    (.commit h_j J, H.saveLock h_j J)
  else (.empty, H)

/-- Definition 50 (`def:fg-rule`, lines 2014–2033): the ordinary combined attestation.
    "Evaluates the two pair rules *in order*: first the finality pair …, whose durable
    lock write completes before the next step, then the current-height pair …, whose
    history read sees that write" (lines 2017–2021) — which is why `H₁` feeds
    `heightVote`. The paper says this ordering is what keeps the two fields of one
    attestation from ever forming E1 evidence (lines 2021–2023); that claim is
    `lem:signer-safety`, to be proved in `Analysis/`. "It signs the one attestation of
    Definition 8 (`def:fg-message`)" (line 2024); the SG head is carried, not derived
    (the attestation "contains no state-block root or confirmed-block root",
    lines 2024–2025). -/
def fgVote (i : Node) (r : Nat) (head : Option (Blk Node Root))
    (J : Blk Node Root) (h_j : Nat) (F : Blk Node Root) (h_F : Nat) (hasJC : Bool)
    (C : Option (Blk Node Root)) (k : Nat) (T : Option (Blk Node Root)) (ν : Bool)
    (hC : Nat) (H : SigningHistory Node Root) :
    Attestation Node Root × SigningHistory Node Root :=
  let (fp, H₁) := finalityVote J h_j F h_F hasJC H       -- first the finality pair
  let (hp, H₂) := heightVote C k T ν hC H₁               -- then the current-height pair
  ({ validator := i, round := r, head := head, heightPair := hp, finalityPair := fp }, H₂)

end

section
variable [DecidableEq Node] [DecidableEq Root] [Electorate Node] [Params]
  [BlockHash Node Root]

/-- Definition 47's context triple, carried with its gate. Named after the definition's
    own symbols: `(k_i, T_i, ν_i)` (lines 1856–1860). -/
structure VoteContext (Node Root : Type) where
  /-- The confirmation gate `C_i` the pair is checked against. -/
  gate : Blk Node Root
  /-- `k_i`, the current height. -/
  k : Nat
  /-- `T_i`, the current-height target, possibly `⊥`. -/
  T : Option (Blk Node Root)
  /-- `ν_i`, the nonjustifiable flag. -/
  ν : Bool

/-- Definition 47 (`def:ordinary-current-target`, lines 1814–1869), in its own
    no-source-proposal branch: "it uses `Y_i = Q_i^r` and `σ_i = σ̄_i = σ_a[Q_i^r]`
    directly when its deepest official confirmation `Q_i^r` is nonempty … and emits no
    current-height pair when `Q_i^r` is empty" (lines 1819–1824). The gate here is
    `getConfirmed S` — the hybrid's stand-in for `Q_i^r`, see the module header — and
    "emits no current-height pair" is the `none` this returns when the gate has no
    recorded state to read.

    `σ_i` is the gate's finality action state for the action's slot: Definition 20
    (`def:finality-action-state`), `σ_a[X] = process_slots(σ[X], slot(a))`, computable
    here because the store's map is `σ[·]`. Then `k_i = σ_i.h`, `ν_i = σ_i.nj`
    (line 1857) and "normally `T_i = σ_i.T_{k_i}`. If that target field is empty and
    `Y_i.slot ≥ σ_i.s_{k_i}`, set `T_i = Y_i`; otherwise set `T_i = ⊥`"
    (lines 1858–1860) — the `else` arm returns the field, which is `⊥` in exactly the
    remaining case. -/
def ordinaryContext [Omega Node Root] (S : Store Node Root) (t : Time) :
    Option (VoteContext Node Root) :=
  let C := getConfirmed S
  if let some σC := S.σ C then
    let σi := processSlots σC t
    some { gate := C, k := σi.h, ν := σi.nj,
           T := if σi.T_h = ⊥ ∧ C.slot ≥ σi.s_h then some C else σi.T_h }
  else none

/-- Definition 50 over the store: derive the gate and context, then `fgVote`. The
    fork-choice fields `(J, h_j)` and `F` are the store's (the hybrid's fork-choice
    state); `h_F` and `hasJC` stay explicit — see the module header. When the gate has no
    recorded state, the current-height pair is empty but the finality rule still runs:
    Definition 49 "is total: the fork-choice action state exists at every action,
    including one whose SG head and current-height pair are empty" (lines 1988–1990).
    `hC = k` because the context state is the gate's own — Definition 48's
    `σ_a[C_i].h ≥ k` check bites only in Definition 47's source-proposal branch, which is
    not rendered. -/
def ordinaryVote [Omega Node Root] (S : Store Node Root) (t : Time)
    (i : Node) (r : Nat) (head : Option (Blk Node Root))
    (h_F : Nat) (hasJC : Bool) (H : SigningHistory Node Root) :
    Attestation Node Root × SigningHistory Node Root :=
  if let some ctx := ordinaryContext S t then
    fgVote i r head S.J S.h_j S.F h_F hasJC (some ctx.gate) ctx.k ctx.T ctx.ν ctx.k H
  else
    fgVote i r head S.J S.h_j S.F h_F hasJC ⊥ 0 ⊥ false 0 H

end

end Decoupled
