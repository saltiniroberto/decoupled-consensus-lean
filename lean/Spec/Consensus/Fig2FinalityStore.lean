import Spec.Consensus.Fig1StateTransition

/-!
# Figure 2 — Finality store

The store of Definition 7, the viable subtree, root and head of Definition 8, and Figure 2's
five handlers: `on_slot`, `on_block`, `process_updates`, `fork_choice_root` and `get_head`.
A node tracks the blocks it has accepted and the finality values that root its fork choice;
blocks are replayed with Figure 1's `stateTransition`.

The `-- line n` comments use Figure 2's own line numbering, in the draft as of 2026-08-19.
The routines appear callee-first; the figure's order is `on_slot`, `on_block`,
`process_updates`, `fork_choice_root`, `get_head`.

## The draft's `Σ` is written `S`

`Σ` is a reserved token in Lean (the dependent-pair binder), not a usable identifier.
Store-valued variables are named `S` throughout, and nothing else in this subtree uses that
letter for a Lean binder.

## The state map is `Option`-valued

Definition 7 has `σ[·]` assign each accepted block its post-state. A total function
`Block → ChainState` would invent states for unaccepted blocks, so the field is
`Block → Option (ChainState Validator)` and an unaccepted block maps to `none`. That the
map is defined exactly on `T` is then a fact to prove about reachable stores, not a fact of
the type.

## `root_proposal[r]` registers only a nonempty root

The field is `Nat → Option (Block Validator)`: `none` until a round-`r` opening block
carrying a nonempty proposal root is processed, then that first root, permanently.
Definition 13 as drafted lets the round's *first* opening block claim the entry even with
`⊥`; conditioning the write on a nonempty root instead (Roberto, 2026-08-20) is what keeps
this a single `Option` — a two-level `Option` distinguishing "unset" from "set to `⊥`"
preceded it, and git history has it. The two rules differ only under an equivocating
opening proposer whose first-processed block carries `⊥`: the draft's rule then pins `⊥`,
this one adopts the equivocator's later nonempty root. The paper sentence to match is "the
proposal root of the first round-`r` opening block carrying one". The field is
Definition 10's; it lands here because Figure 2's `on_block` is its first writer.

## Two `let some … | return S` lines in `on_block`, both the reject exit

A parentless `B` — genesis — is the figure's `B.parent ∉ Σ.T` case, taken before the slot
test rather than inside line 7's disjunction; the effect is the same, the store unchanged.
And the parent's recorded state is read through the map's `Option`, so a parent in `T`
that the map misses also rejects — unreachable once the map-domain coherence invariant is
proved, the same seam the old rendering documents.

## Totality

Every handler returns a store; a block that fails admission leaves it unchanged — except
for the root-proposal registration of lines 5–6, which the figure runs *before* the
admission test, and this rendering does too.
-/

set_option autoImplicit false

namespace Consensus

variable {Validator : Type}

/-- The store (Definition 7 of the draft), in the draft's field order:
    `Σ = (s, T, σ[·], F, J, h_j, h_max)` — written `S`, see the module header — plus
    Definition 10's timed extension `(t, head[·], equiv[·], root_proposal[·], sg_root[·],
    action_root[·])`, the draft's `Σ += (…)`, landed field by field as Figures 2 and 4–6
    consumed it. Initially the per-round maps are empty; the scheduled hooks fill each
    round's entries, fixed after their scheduled writes. -/
structure Store (Validator : Type) where
  /-- `s`, the current slot. -/
  s : Nat
  /-- `T`, the tree of accepted blocks. -/
  T : Finset (Block Validator)
  /-- `σ[·]`, the state map: the post-state of each accepted block, `none` on a block
      outside `T` — see the module header. Read `S.σ B`. -/
  σ : Block Validator → Option (ChainState Validator)
  /-- `F`, the finalized block the store has adopted. Always accepted. -/
  F : Block Validator
  /-- `J`, the justified block rooting the store's fork choice. Always accepted. -/
  J : Block Validator
  /-- `h_j`, the height of the justified pair `(J, h_j)`. -/
  h_j : Nat
  /-- `h_max`, the greatest state-height the store has ever accepted. -/
  h_max : Nat
  /-- `root_proposal[·]` (Definition 10; here because `on_block` writes it): per round,
      `none` until an opening block of that round carrying a nonempty proposal root is
      processed, then that first root. See the module header for the deviation from
      Definition 13's first-block rule. -/
  rootProposal : Nat → Option (Block Validator)
  /-- `head[·]` (Definition 10; read by Figure 4's scores, written by Figure 6's
      `on_attestation`): per round and validator, the first processed nonempty attestation
      head with its processing time, `none` until one arrives. -/
  head : Nat → Validator → Option (Block Validator × Int)
  /-- `equiv[·]` (Definition 10; read by Figure 4, written by Figure 6): per round and
      validator, the time at which a head different from the stored one was first
      processed — the equivocation time — `none` while none was. -/
  equiv : Nat → Validator → Option Int
  /-- `sg_root[·]` (Definition 10; written by Figure 6 at the opening slot's vote time,
      read by Figure 5's `get_walk_root`): per round, the SG root derived at `t_r + Δ`,
      `none` until that write. Fixed after it. -/
  sgRoot : Nat → Option (Block Validator)
  /-- `action_root[·]` (Definition 10; written by Figure 6 at `a_r`): per round, the root
      Figure 5's `get_action_root` derived there — the anchor of the round's SG and FG
      outputs, which the draft's Section 6 will read. `none` until that write. -/
  actionRoot : Nat → Option (Block Validator)
  /-- `Σ.t` (Definition 10), the clock: the current time, set by every `on_tick`. Starts
      below time 0 — the draft leaves the initial value unstated, and `on_tick`'s
      precondition `Σ.t < t` must pass at `t = 0` — at `-1`, an arbitrary such value. -/
  t : Int
  /-- `Ω`, the draft's "available-chain data that selects among the candidates": pick a
      block from a nonempty set, the subtype carrying the membership proof so anything
      picked is one of the candidates — Definition 8's `get_head(Σ, Ω) ∈ C(Σ)`. Abstract
      until the draft's Section 5 defines it.

      **A store field, beyond Definitions 7 and 10** (Roberto, 2026-08-20): the draft
      passes `Ω` to `get_head` as call-time input, and the old rendering kept it ambient
      by typeclass and out of the store; carrying it here instead makes every selection —
      `get_head`, the deepest-picks, Section 5's confirmation when it lands — a function
      of the store alone. -/
  Ω : (s : Finset (Block Validator)) → s.Nonempty → {B // B ∈ s}

/-! ### `B ∈ S.σ` and `S.σ[B]`, through `Membership` and `GetElem`

The draft writes `Σ.σ[B]` unconditionally, its map being defined exactly on the accepted
blocks; here the field is `Option`-valued, so a bare read owes a proof that `B` is
recorded. These instances — ported from the old rendering, `Spec/Defs/Store.lean`, whose
header carries the measurements — let that proof stay anonymous: `B ∈ S.σ` is "the map is
defined at `B`" (definitionally `(S.σ B).isSome`), and `S.σ[B]` elaborates its side
condition with `get_elem_tactic`, which finds any hypothesis of that type in context,
named or not: `if _ : B ∈ S.σ then … S.σ[B] …` passes nothing by hand.

Two hazards, measured on the old rendering: the `∀ x ∈ s` binder does not reach the
bracket — write `∀ B (_ : B ∈ S.σ), …` — and `rw` on a store inside a bracket read fails
with "motive is not type correct" where `simp only` succeeds. -/

/-- `B ∈ σ`: the map is defined at `B`. -/
scoped instance stateMapMembership :
    Membership (Block Validator) (Block Validator → Option (ChainState Validator)) where
  mem σ B := (σ B).isSome

/-- The membership is a `Bool` in disguise, so an `if _ : B ∈ S.σ` can test it. The old
    rendering never needed this: it read the map only in statements. -/
scoped instance (σ : Block Validator → Option (ChainState Validator)) (B : Block Validator) :
    Decidable (B ∈ σ) :=
  inferInstanceAs (Decidable ((σ B).isSome = true))

/-- `σ[B]`: the state recorded for `B`, given that `B` is recorded. -/
scoped instance stateMapGetElem :
    GetElem (Block Validator → Option (ChainState Validator)) (Block Validator)
      (ChainState Validator) (fun σ B => B ∈ σ) where
  getElem σ B h := (σ B).get h

/-- `σ[B]?`: the same read with no side condition, which is the map itself. -/
scoped instance stateMapGetElemOpt :
    GetElem? (Block Validator → Option (ChainState Validator)) (Block Validator)
      (ChainState Validator) (fun σ B => B ∈ σ) where
  getElem? σ B := σ B

/-- The two agree, which is what lets the core `getElem?_pos`/`getElem?_neg` lemmas
    fire. -/
scoped instance stateMapLawfulGetElem :
    LawfulGetElem (Block Validator → Option (ChainState Validator)) (Block Validator)
      (ChainState Validator) (fun σ B => B ∈ σ) where
  getElem?_def σ B _ := by
    by_cases hb : B ∈ σ
    · rw [dif_pos hb]
      exact (Option.some_get hb).symm
    · rw [dif_neg hb]
      have hb' : ¬ (σ B).isSome = true := hb
      have h2 : σ B = none := by simpa using hb'
      exact h2

section StoreDefs
variable [DecidableEq Validator]

/-- The genesis store: `s = 0`, `T = {B_gen}`, `σ[B_gen]` the genesis state,
    `F = B_gen`, `(J, h_j) = (B_gen, 0)`, `h_max = 1`. The per-round maps start empty.
    The one field the draft's genesis prose does not fix is the validator's selection
    data `Ω`, so it is the argument. -/
def Store.gen (Ω : (s : Finset (Block Validator)) → s.Nonempty → {B // B ∈ s}) :
    Store Validator where
  s := 0
  T := {.genesis}
  σ := fun B => if B = .genesis then some .gen else none
  F := .genesis
  J := .genesis
  h_j := 0
  h_max := 1
  rootProposal := fun _ => none
  head := fun _ _ => none
  equiv := fun _ _ => none
  sgRoot := fun _ => none
  actionRoot := fun _ => none
  t := -1
  Ω := Ω

/-- The *leaves* of `Σ.T` (Definition 8 of the draft): the accepted blocks without
    accepted children. "Without accepted children" is written `∀ C ∈ S.T, C.parent ≠ some L`
    — no accepted block names `L` as its parent. -/
def leaves (S : Store Validator) : Finset (Block Validator) :=
  S.T.filter fun L => ∀ C ∈ S.T, C.parent ≠ some L

/-- `V(Σ)` (Definition 8 of the draft): the viable blocks. A block is *viable* when some
    leaf descending from it has state-height at least `Σ.h_max − 1`: its branch reaches
    within one height of the store's frontier. Viability is inherited by ancestors, so the
    set is prefix-closed — the draft's observation, not an extra clause.

    `∃ _ : L ∈ S.σ` is what lets the height be read as `S.σ[L].h`: the binder puts the
    membership in context, where the bracket's side condition finds it. A leaf the map
    misses therefore witnesses nothing — a member of `T` the map misses is a coherence
    invariant's business, not this definition's. -/
def viableSet (S : Store Validator) : Finset (Block Validator) :=
  S.T.filter fun B => ∃ L ∈ leaves S, B ⪯ L ∧ ∃ _ : L ∈ S.σ, S.σ[L].h ≥ S.h_max - 1

/-- `fork_choice_root(Σ)` (Figure 2, lines 20–23), Definition 8's fork-choice root: `Σ.J`
    while the justified pair sits one height under the store's frontier —
    `Σ.h_max = Σ.h_j + 1` — and `Σ.F` otherwise. -/
def forkChoiceRoot (S : Store Validator) : Block Validator := Id.run do
  if S.h_max = S.h_j + 1 then                                 -- line 21
    return S.J                                                -- line 22
  return S.F                                                  -- line 23

/-- `C(Σ)` (Definition 8 of the draft): the candidate tree — the viable blocks rooted at
    the fork-choice root. Fork choice selects a head within it. -/
def candidateTree (S : Store Validator) : Finset (Block Validator) :=
  (viableSet S).filter fun B => forkChoiceRoot S ⪯ B

end StoreDefs

/-! ## The handlers -/

/-- `on_slot(Σ, s)` (Figure 2, lines 1–3): advance the store's slot at the start of slot
    `s`, before any block of that slot is processed. -/
def onSlot (S : Store Validator) (s : Nat) : Store Validator := Id.run do
  let mut S := S
  S.s ← s                                                     -- line 2
  return S                                                    -- line 3

section Handlers
variable [DecidableEq Validator] [Electorate Validator] [Params] [BlockHash Validator]

/-- `process_updates(Σ, σ)` (Figure 2, lines 12–19): fold an offered post-state into the
    store. Raise `h_max`; replace the justified pair when the offer dominates in
    `(h, hash)` order and descends from `Σ.F`; advance the finalized block only to a viable
    proper descendant of `Σ.F` below `Σ.J`, pruning every accepted block conflicting with
    the new `Σ.F` — the pruned blocks remain available as signed evidence, outside this
    store. -/
def processUpdates (S : Store Validator) (σ : ChainState Validator) :
    Store Validator := Id.run do
  let mut S := S
  S.h_max ← max S.h_max σ.h                                   -- line 13
  -- line 14: `(σ.h_j, hash(σ.J)) > (Σ.h_j, hash(Σ.J))` is the strict lexicographic
  -- order, written out
  if S.F ⪯ σ.J ∧ (S.h_j < σ.h_j ∨ (σ.h_j = S.h_j ∧ hash(S.J) < hash(σ.J))) then
    S.J ← σ.J                                                 -- line 15
    S.h_j ← σ.h_j
  if S.F ≺ σ.F ∧ σ.F ⪯ S.J ∧ σ.F ∈ viableSet S then           -- line 16
    S.F ← σ.F                                                 -- line 17
    S.T ← S.T.filter fun B => B ∼ S.F                         -- line 18: keep the compatible
  return S                                                    -- line 19

/-- `on_block(Σ, B)` (Figure 2, lines 4–11). Lines 5–6 register the round's root proposal
    from the first opening block processed that carries one — before the admission test, so
    a block rejected below still claims its round's entry. Admission then wants the slot
    started, the parent accepted, and `B` descending from `Σ.F`; an admitted block is
    replayed with Figure 1's transition, stored, and its post-state offered to
    `process_updates`. -/
def onBlock (S : Store Validator) (B : Block Validator) : Store Validator := Id.run do
  let mut S := S
  -- line 5, strengthened: only a nonempty proposal root registers — see the module header
  if B.isOpening ∧ S.rootProposal (round B.slot) = none ∧ B.proposalRoot ≠ none then
    S.rootProposal[round B.slot] ← B.proposalRoot             -- line 6
  -- line 7: `if B.slot > Σ.s or B.parent ∉ Σ.T or Σ.F ⪯̸ B then return Σ`. A parentless
  -- `B` — genesis — is the `B.parent ∉ Σ.T` case, taken first; see the module header.
  let some p := B.parent | return S
  if B.slot > S.s ∨ p ∉ S.T ∨ ¬ S.F ⪯ B then
    return S                                                  -- line 8
  -- line 9: `Σ.σ[B] ← state_transition(Σ.σ[B.parent], B)`. The parent's state is read
  -- through the map's `Option`; a parent the map misses rejects — see the module header.
  let some σp := S.σ p | return S
  let σ' := stateTransition σp B
  S.σ[B] ← some σ'
  S.T ← S.T ∪ {B}                                             -- line 10
  return processUpdates S σ'                                  -- line 11

end Handlers

/-- `get_head(Σ, Ω)` (Figure 2, lines 24–25): a block in `C(Σ)`, selected by `Ω` — the
    store's own selection data, abstract until the draft's Section 5 is written. On an
    empty candidate tree — not excluded by the types, though a store the handlers built
    keeps its fork-choice root viable — the fork-choice root is returned, so the routine
    is total. -/
def getHead [DecidableEq Validator] (S : Store Validator) : Block Validator :=
  if h : (candidateTree S).Nonempty then (S.Ω (candidateTree S) h).val
  else forkChoiceRoot S

end Consensus
