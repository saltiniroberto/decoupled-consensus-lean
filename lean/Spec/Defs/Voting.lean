import Spec.HftFig2Store

/-!
# The healing paper's voting strategy — Definitions 12, 33–36, 45 and 47–50

`height_filter_healing.tex` Definition 12 (`def:signing-history`, lines 522–530) and
Assumption 3 (`ass:goldfish-committees`, lines 250–258); `recovery_core.tex`
Definitions 33 (`def:counting-rule`, lines 383–404), 34 (`def:sg-head`, lines 491–514),
35 (`def:grade-support`, lines 515–536), 36 (`def:grades`, lines 537–559),
45 (`def:recovery-goldfish-vote`, lines 1587–1603), 47 (`def:ordinary-current-target`,
lines 1814–1869), 48 (`def:height-vote-rule`, lines 1952–1981), 49
(`def:finality-vote-rule`, lines 1982–2012) and 50 (`def:fg-rule`, lines 2014–2033).
Definitions only; the safety result the FG rules are built for — Lemma 44
(`lem:signer-safety`), honest attestations are never E1- or E2-slashable — is `Analysis/`
work and is not here.

The paper's vote types, and where each lands in this file: the **current-height vote**
(target or timeout) and the **finality vote** are the FG signing rules, `heightVote` and
`finalityVote`, combined by `fgVote`; the **SG head** is the third field of the same
attestation — its signing condition is `sgHeadOk` and its supporting grade machinery is
`SGEquivocation`/`eligibleBatch`/`directSupport`/`favorableSupport`/`G3`–`G0`, while the
rule *producing* a head (Definition 46, via the stable root, Definitions 38–42) is not
rendered and `head` stays an input; the **raw Goldfish vote** is `goldfishVote`, the
vote-time GHOST walk over explicit votes, tree and root.

## What is rendered, and from which sentences

The signing rules are stated by the paper over explicit inputs — a block `C_i` the
validator currently takes as confirmed (the paper's word for it is avoided here; see
`heightVote`'s docstring for what `C_i` does), a context triple `(k, T, ν)`, the
fork-choice fields `(J, h_j)` and `(F, h_F)`, and the durable history `H_i` — and they
are rendered here the same way: `heightVote` and
`finalityVote` are pure functions of those inputs, returning the signed pair **and the
updated history**, because the paper's "record and sign" and "writes each value before
releasing the signature" (Definition 12) make the write part of the rule. `fgVote` is
Definition 50's composition, finality first, so the lock write is visible to the
current-height rule's history read — the ordering the paper stresses, because it is what
keeps one attestation from being its own E1 pair.

## The hybrid supplies the inputs

`ordinaryContext` and `ordinaryVote` wire the rules over this project's store:

* **The confirmed block is `getConfirmed`'s pick.** The paper's `C_i` is `Q_i^r`, the
  deepest official confirmation (Definition 46, `def:official-confirmation`), whose
  derivation needs the recovery apparatus (grades, TSQ views, rounds — Definitions 28–46,
  none rendered). In the declared hybrid the store's own confirmation function stands in;
  the companion paper's voting rule (its Figure 4, `hft:alg:voting-rule`) reads its
  confirmed block from `get_confirmed` the same way.
* **The context triple is Definition 47's own no-source-proposal branch.** Definition 47
  distinguishes a source-proposal case from a fallback the paper states explicitly: "it
  uses `Y_i = Q_i^r` and `σ_i = σ̄_i = σ_a[Q_i^r]` directly" (lines 1819–1823). That
  branch is what `ordinaryContext` renders: `σ_i` is the confirmed block's finality
  action state —
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

The stable-root machinery and its consumers — Definitions 28–32 and 37–44 and 46
(recovery timing and the four views, activation, walk standing, grade-root choices, TSQ
views and confirmations, stable root, action root, proposals, official confirmation) —
so the head *production* rule is absent while its signing condition (`sgHeadOk`) is
present, and the Goldfish walk's context (which votes, which tree, which root) enters as
arguments. Definition 37 (`def:active-grade`) is likewise absent: its third clause, "`B`
conflicts with no finalized root whose evidence `u` has processed", is evidence-relative
the way `hasJC` is, and it belongs with the stable root that consumes it. Also absent:
the action schedule (when a validator votes), which is what would wire these into
`Spec/Protocol.lean`'s reaction and is a separate `NodeState` decision. Definition 12's
"restores the values after restart" is about crashes, which the framework does not model;
the history is a value threaded through the rules here.
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
    rule, "choose in this order". `C` is the paper's `C_i` (`⊥` → "the current-height
    pair is empty", line 1957); `(k, T, ν)` is Definition 47's context; `hC` is
    `σ_a[C_i].h` (in `ordinaryVote`'s wiring the context state *is* `C`'s own, so
    `hC = k`); `H` is the durable history. Returns the pair and the history after the
    rule's own writes — "every durable write completes before signature release"
    (line 1976).

    In plain words, what `C` is: the block this validator currently takes as confirmed —
    in the paper its deepest official confirmation, here `getConfirmed`'s pick — and the
    rule signs nothing beyond it. Every branch checks its candidate against `C` before
    signing: a target is signed only when it lies on `C`'s chain (`T ⪯ C`), a timeout
    only when `C`'s own replayed state has reached height `k` (that is `hC ≥ k`), and
    with no confirmed block at all, nothing is signed. So `C` is the ceiling on what the
    validator will vouch for.

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
    attestation from ever forming E1 evidence (lines 2021–2023); that claim is Lemma 44
    (`lem:signer-safety`), to be proved in `Analysis/`. "It signs the one attestation of
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

/-- Definition 47 (`def:ordinary-current-target`)'s context triple, carried with the
    confirmed block it was read from. Named after the definition's own symbols: `C_i`
    and `(k_i, T_i, ν_i)` (lines 1856–1860). -/
structure VoteContext (Node Root : Type) where
  /-- `C_i`: the block the validator currently takes as confirmed. Every target the
      current-height rule signs must lie on this block's chain. -/
  C : Blk Node Root
  /-- `k_i`, the current height. -/
  k : Nat
  /-- `T_i`, the current-height target, possibly `⊥`. -/
  T : Option (Blk Node Root)
  /-- `ν_i`, the nonjustifiable flag. -/
  ν : Bool

/-- Definition 47 (`def:ordinary-current-target`, lines 1814–1869), in its own
    no-source-proposal branch: "it uses `Y_i = Q_i^r` and `σ_i = σ̄_i = σ_a[Q_i^r]`
    directly when its deepest official confirmation `Q_i^r` is nonempty … and emits no
    current-height pair when `Q_i^r` is empty" (lines 1819–1824). The confirmed block
    here is `getConfirmed S` — the hybrid's stand-in for `Q_i^r`, see the module
    header — and "emits no current-height pair" is the `none` this returns when that
    block has no recorded state to read.

    `σ_i` is the confirmed block's finality action state for the action's slot:
    Definition 20
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
    some { C := C, k := σi.h, ν := σi.nj,
           T := if σi.T_h = ⊥ ∧ C.slot ≥ σi.s_h then some C else σi.T_h }
  else none

/-- Definition 50 over the store: derive the confirmed block and its context, then
    `fgVote`. The fork-choice fields `(J, h_j)` and `F` are the store's (the hybrid's
    fork-choice state); `h_F` and `hasJC` stay explicit — see the module header. When the
    confirmed block has no recorded state, the current-height pair is empty but the
    finality rule still runs: Definition 49 "is total: the fork-choice action state
    exists at every action, including one whose SG head and current-height pair are
    empty" (lines 1988–1990). `hC = k` because the context state is the confirmed
    block's own — Definition 48's `σ_a[C_i].h ≥ k` check bites only in Definition 47's
    source-proposal branch, which is not rendered. -/
def ordinaryVote [Omega Node Root] (S : Store Node Root) (t : Time)
    (i : Node) (r : Nat) (head : Option (Blk Node Root))
    (h_F : Nat) (hasJC : Bool) (H : SigningHistory Node Root) :
    Attestation Node Root × SigningHistory Node Root :=
  if let some ctx := ordinaryContext S t then
    fgVote
      (i := i)           -- the signing validator; passed through from the caller
      (r := r)           -- the attestation's round; passed through from the caller
      (head := head)     -- the SG head the attestation carries; passed through
      (J := S.J)         -- the latest justified block; here the store's
      (h_j := S.h_j)     -- the latest justified height; here the store's
      (F := S.F)         -- the latest finalized block; here the store's
      (h_F := h_F)       -- the latest finalized height; explicit input, open decision
      (hasJC := hasJC)   -- knowledge of `JC(h_j, J)`; explicit input, open decision
      (C := some ctx.C)  -- the confirmed block `C_i`; here `getConfirmed`'s pick
      (k := ctx.k)       -- the current height `k_i`; here the context state's height
      (T := ctx.T)       -- the current-height target `T_i`; read off the context
      (ν := ctx.ν)       -- the nonjustifiable flag `ν_i`; the context state's `nj`
      (hC := ctx.k)      -- the context state's height `σ_a[C_i].h`; equal to `k` here
      (H := H)           -- the durable history, threaded through both pair rules
  else
    fgVote
      (i := i) (r := r) (head := head)          -- as in the branch above
      (J := S.J) (h_j := S.h_j) (F := S.F)      -- the store's fork-choice fields
      (h_F := h_F) (hasJC := hasJC)             -- the two explicit inputs
      (C := ⊥)           -- no recorded state at the confirmed block: the pair is empty
      (k := 0) (T := ⊥) (ν := false) (hC := 0)  -- unread once `C = ⊥`
      (H := H)           -- the finality rule still runs, and may write the lock

end

/-! ## Definition 34 — SG equivocation, the eligible batch, and the head condition -/

section
variable [DecidableEq Node] [DecidableEq Root]

/-- Definition 34 (`def:sg-head`, lines 491–514): "Two signed attestations from one
    identity in one round are SG equivocation exactly when their head fields differ and
    at least one is nonempty" (lines 504–506). Note an empty head against a nonempty one
    counts: silence is not a second head, but a second message disagreeing about the head
    is. -/
def SGEquivocation (a b : Attestation Node Root) : Bool :=
  decide (a.validator = b.validator ∧ a.round = b.round ∧ a.head ≠ b.head ∧
    (a.head ≠ ⊥ ∨ b.head ≠ ⊥))

/-- Definition 34 (`def:sg-head`), second paragraph (lines 508–511): "Round `r > 0`
    grades exactly the
    heads signed in round `r − 1`. Older and newer heads are ineligible. The first
    recovery round has an empty eligible batch." `X` is a view: the signed attestations
    the validator can see, per Definition 28 (`def:recovery-timing`)'s four snapshots,
    which enter the grade definitions below as explicit arguments. -/
def eligibleBatch (X : Finset (Attestation Node Root)) (r : Nat) :
    Finset (Attestation Node Root) :=
  if r = 0 then ∅ else X.filter fun a => a.round = r - 1 ∧ a.head ≠ ⊥

/-- `i` has an SG equivocation among the graded round's attestations in the view `X` —
    what Definition 35's "no SG equivocation by `i` in `X`" reads. Checked over `X`'s
    round-`(r − 1)` attestations unfiltered, because an empty head equivocates against a
    nonempty one and the eligible batch keeps only nonempty heads. -/
def equivocatesIn (i : Node) (X : Finset (Attestation Node Root)) (r : Nat) : Bool :=
  if r = 0 then false
  else decide (∃ a ∈ X, ∃ b ∈ X, a.validator = i ∧ a.round = r - 1 ∧
    SGEquivocation a b)

/-- Definition 34 (`def:sg-head`), the normative signing condition (lines 496–503):
    "An honest validator
    puts a head in that field only when `S_{i,act}^r ⪯ B` and `B` is viable in
    `Σ_{i,act}^r`."

    `S_{i,act}^r` is `simplex_root` of the fork-choice action state — healing
    Definition 26 (`def:finality-root`) and Figure 4 (`alg:fork-choice-state`), whose
    cascade "`J` if `hmax = h_j + 1` else `F`" is word for word the companion store's
    walk-from block `Store.FGWalkStart` (Figure 2, `hft:alg:store`, line 560). So over the hybrid
    the condition reads: the head sits at or above the store's walk-from block, and is
    viable there.

    In plain words: a validator may advertise a head only if the head extends the block
    its fork choice walks from, on a branch the height filter has not discarded. This is
    the condition an honest head must pass; the rule that *produces* a head satisfying it
    (Definition 46, `def:official-confirmation`) needs the stable-root machinery
    (Definitions 38–42) and is not rendered — `head` stays an input to `fgVote`. -/
def sgHeadOk (S : Store Node Root) (B : Blk Node Root) : Bool :=
  decide (S.FGWalkStart ⪯ B ∧ B ∈ viableTree S)

end

/-! ## Definitions 35 and 36 — support and the four SG grades -/

section
variable [DecidableEq Node] [DecidableEq Root] [Electorate Node]

/-- Definition 35 (`def:grade-support`, lines 515–536): `D_X(B)`, the identities "whose
    single eligible head `B_i` in `X` satisfies `B ⪯ B_i`, with no SG equivocation by
    `i` in `X`; an identity with SG equivocation supplies no direct support". No
    equivocation is what makes the eligible head single, so the set is spelled as the
    no-equivocation conjunct plus an eligible head above `B`. -/
def directSupporters (X : Finset (Attestation Node Root)) (r : Nat) (B : Blk Node Root) :
    Finset Node :=
  Electorate.V.filter fun i => ¬ equivocatesIn i X r ∧
    ∃ a ∈ eligibleBatch X r, a.validator = i ∧ ∃ hB, a.head = some hB ∧ B ⪯ hB

/-- Definition 35: `directSupport_X(B) = ∑_{i ∈ D_X(B)} w(i)`. -/
def directSupport (X : Finset (Attestation Node Root)) (r : Nat) (B : Blk Node Root) :
    Nat :=
  w(directSupporters X r B)

/-- Definition 35: `Φ_X(B)`, the identities "with an eligible head `B_i` in `X`
    satisfying `B ⪯ B_i`, together with every identity that has an SG equivocation in
    `X`, each identity counted once". -/
def favorableSupporters (X : Finset (Attestation Node Root)) (r : Nat)
    (B : Blk Node Root) : Finset Node :=
  Electorate.V.filter fun i => equivocatesIn i X r ∨
    ∃ a ∈ eligibleBatch X r, a.validator = i ∧ ∃ hB, a.head = some hB ∧ B ⪯ hB

/-- Definition 35: `favorableSupport_X(B) = ∑_{i ∈ Φ_X(B)} w(i)`. -/
def favorableSupport (X : Finset (Attestation Node Root)) (r : Nat) (B : Blk Node Root) :
    Nat :=
  w(favorableSupporters X r B)

/-- Definition 35: `D_u^{-,1}(B)`, the identities "whose unique eligible head is the same
    block `B_i` in both `X_u^-` and `X_u^1`, satisfies `B ⪯ B_i`, with no SG equivocation
    in `X_u^1`". Uniqueness in each view is the corresponding no-equivocation conjunct —
    a second differing message, empty head included, is exactly an equivocation. -/
def directSupportersTwoView (Xm X1 : Finset (Attestation Node Root)) (r : Nat)
    (B : Blk Node Root) : Finset Node :=
  Electorate.V.filter fun i => ¬ equivocatesIn i Xm r ∧ ¬ equivocatesIn i X1 r ∧
    ∃ a ∈ eligibleBatch Xm r, ∃ b ∈ eligibleBatch X1 r,
      a.validator = i ∧ b.validator = i ∧ a.head = b.head ∧
      ∃ hB, a.head = some hB ∧ B ⪯ hB

/-- Definition 36 (`def:grades`, lines 537–559): `G3_u(B) ⟺ directSupport_u^{-,1}(B) ≥ m`,
    over the `−Δ` and `+Δ` views `X_u^-` and `X_u^1` of Definition 28. -/
def G3 (Xm X1 : Finset (Attestation Node Root)) (r : Nat) (B : Blk Node Root) : Prop :=
  w(directSupportersTwoView Xm X1 r B)≥m

/-- Definition 36: `G2_u(B) ⟺ directSupport_{X_u^0}(B) ≥ m`. -/
def G2 (X0 : Finset (Attestation Node Root)) (r : Nat) (B : Blk Node Root) : Prop :=
  w(directSupporters X0 r B)≥m

/-- Definition 36: `G1_u(B) ⟺ favorableSupport_{X_u^1}(B) ≥ m`. -/
def G1 (X1 : Finset (Attestation Node Root)) (r : Nat) (B : Blk Node Root) : Prop :=
  w(favorableSupporters X1 r B)≥m

/-- Definition 36: `G0_u(B) ⟺ favorableSupport_{X_u^2}(B) ≥ m`. -/
def G0 (X2 : Finset (Attestation Node Root)) (r : Nat) (B : Blk Node Root) : Prop :=
  w(favorableSupporters X2 r B)≥m

end

/-! ## Definitions 33 and 45 — the raw Goldfish vote -/

/-- The raw Goldfish vote: Assumption 3 (`ass:goldfish-committees`,
    `height_filter_healing.tex` lines 250–258) has each slot's committee — "a known
    subset of `V`" — "cast that slot's raw Goldfish votes, counted one unit per member".
    The object names its signer, its slot, and the block it supports; the healing store
    keeps such votes as evidence (Definition 22, `def:stored-data`). How committees are
    drawn is outside the paper's scope and outside this rendering's. -/
structure GoldfishVote (Node Root : Type) where
  /-- The committee member casting the vote. -/
  validator : Node
  /-- The slot the vote belongs to. -/
  slot : Time
  /-- The block the vote supports. -/
  target : Blk Node Root
  deriving DecidableEq

section
variable [DecidableEq Node] [DecidableEq Root]

/-- The weight a walk assigns a block: the number of distinct voters in `votes` whose
    vote supports a block in `B`'s subtree — "counted one unit per member" (Assumption 3),
    and per Definition 33 (`def:counting-rule`, lines 383–404) counted "of the full known
    block tree, whether or not those blocks are in the candidate tree", which is why no
    tree constrains this count. The caller passes the votes that count — the slot's
    committee votes in the view the walk reads — so committee membership is the caller's
    fact, not re-checked here. A member voting for two conflicting descendants still
    counts once: the image collapses it. -/
def goldfishWeight (votes : Finset (GoldfishVote Node Root)) (B : Blk Node Root) : Nat :=
  ((votes.filter fun v => B ⪯ v.target).image fun v => v.validator).card

end

section
variable [DecidableEq Node] [DecidableEq Root] [BlockHash Node Root]

/-- Vote-time GHOST (Definition 45, `def:recovery-goldfish-vote`, lines 1587–1603),
    fuel-indexed: from the current block, step to the heaviest child *in the candidate
    tree* — Definition 33: "the candidate tree constrains the walk's choices, not the
    counted weights" — and stop when no child remains. Ties break by larger `hash(·)`,
    then by the list's order; the source breaks ties deterministically without fixing
    how, so the tie-break is this rendering's choice, recorded here.

    The fuel only serves termination: every step moves to a member of `tree` strictly
    deeper in the block tree, so `tree.length` steps suffice — the paper's totality
    statement is Lemma 20 (`lem:aged-walk-total`) — and exhausted fuel returns the
    current block,
    which no run started with `tree.length` reaches. The candidate tree is a list rather
    than a `Finset` so the walk stays computable and deterministic; its order matters
    only to break exact `(weight, hash)` ties. -/
def ghostFrom (votes : Finset (GoldfishVote Node Root)) (tree : List (Blk Node Root)) :
    Nat → Blk Node Root → Blk Node Root
  | 0, walkStart => walkStart
  | fuel + 1, walkStart =>
      let step := (tree.filter fun C => C.parent = some walkStart).foldl
        (fun best C =>
          match best with
          | none => some C
          | some D =>
              if goldfishWeight votes D < goldfishWeight votes C ∨
                  (goldfishWeight votes C = goldfishWeight votes D ∧
                    hash(D) < hash(C)) then
                some C
              else some D)
        none
      match step with
      | some next => ghostFrom votes tree fuel next
      | none => walkStart

/-- The walk, with the fuel it needs. -/
def ghost (votes : Finset (GoldfishVote Node Root)) (tree : List (Blk Node Root))
    (walkStart : Blk Node Root) : Blk Node Root :=
  ghostFrom votes tree tree.length walkStart

/-- Definition 45 (`def:recovery-goldfish-vote`, lines 1587–1603): the committee member
    "runs vote-time GHOST from its accepted stable root within the aged tree …, with the
    proposal-path exemption of Definition 33, and votes for that output". Which votes,
    which tree and which root are the recovery context — the frozen slot view and
    proposal-view merge of Definition 28, the aged trees of Definition 38
    (`def:tsq-views`), the proposal-path exemption, and the stable root of Definition 41
    (`def:stable-root`) — none of it rendered: they enter as the arguments, the same
    explicit-inputs pattern as the FG rules above. The rule itself is: walk, and vote the
    output. -/
def goldfishVote (i : Node) (s : Time) (votes : Finset (GoldfishVote Node Root))
    (tree : List (Blk Node Root)) (walkStart : Blk Node Root) : GoldfishVote Node Root :=
  { validator := i, slot := s, target := ghost votes tree walkStart }

end

/-! ## Definition 28 — the round schedule: when the votes above are cast -/

/-- Definition 28 (`def:recovery-timing`, lines 87–222): the recovery round layout, as
    the ambient clock the protocol's tick reaction reads. `start r` is the paper's `d_r`,
    round `r`'s first proposal time; `Δ` is the network-delivery bound. The paper's
    per-slot phase list (lines 172–178) is "`d` proposal, `d + Δ` vote, `d + 2Δ`
    confirmation input, `d + 3Δ` slot-view freeze", with slots `4Δ` long; the round's
    SG/FG action time is `a_r = d_r + 4Δ + 2Δ` (lines 146–150); and the public round
    spacing `a_r + Δ ≤ d_{r+1} − Δ` (lines 196–199) is carried in added form,
    `d_r + 8Δ ≤ d_{r+1}`, which also gives the definition's "contains at least two slots
    of length `4Δ`". How `d_r` values are chosen is the environment's business, exactly
    like the electorate: a class, so statements quantify over every schedule meeting the
    paper's constraints. Named `Rounds` because the framework already uses `Schedule` for
    the adversary's awake/corrupt choices. -/
class Rounds where
  /-- `d_r`, round `r`'s first proposal time. -/
  start : Nat → Time
  /-- `Δ`, the network-delivery bound. -/
  Δ : Time
  /-- The bound is positive — the phase offsets below are distinct. -/
  Δ_pos : 0 < Δ
  /-- The public round spacing (Definition 28, `def:recovery-timing`, lines 196–199),
      in added form: `a_r + Δ ≤ d_{r+1} − Δ`
      with `a_r = d_r + 6Δ` is `d_r + 8Δ ≤ d_{r+1}`. -/
  spaced : ∀ r, start r + 8 * Δ ≤ start (r + 1)

namespace Rounds
variable [Rounds]

/-- `a_r = d_r + 4Δ + 2Δ` (Definition 28, `def:recovery-timing`, lines 146–150): "two
    network-delivery bounds into the round's
    second slot", when the validator "performs the round's SG and FG action". -/
def SGFGVotingTime (r : Nat) : Time :=
  start r + 6 * Δ

/-- Which round a clock reading falls in: the `r` with `d_r ≤ t < d_{r+1}`, none before
    `d_0`. The bounded search is enough: `spaced` and `Δ_pos` grow `start` by at least 8
    per round, so the round number never exceeds the reading. -/
def roundAt (t : Time) : Option Nat :=
  (List.range (t + 1)).find? fun r => start r ≤ t ∧ t < start (r + 1)

/-- `t` is a Goldfish vote time of round `r`: the `+Δ` phase of one of the round's `4Δ`
    slots (Definition 28, `def:recovery-timing`, lines 172–178) — "Goldfish votes at
    `+Δ`" (line 200), and "every slot of the
    round runs ordinary Goldfish" (lines 191–193). The caller has established
    `start r ≤ t` via `roundAt`. -/
def isGoldfishVoteTime (r : Nat) (t : Time) : Bool :=
  decide ((t - start r) % (4 * Δ) = Δ)

end Rounds

end Decoupled
