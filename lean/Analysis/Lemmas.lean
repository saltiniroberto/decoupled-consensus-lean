import Spec

/-!
# The paper's numbered lemmas

*Height Filtering and Healing for a Simplex-Style Finality Variant*
(`height_filter_healing.tex`). Statements of record, one per numbered lemma, proved against the
specification in `Spec`.

**Being added one at a time.** The nine lemmas of Sections 3 and 4 were written in one pass on
2026-08-13 and withdrawn the same day, on instruction: each returns on its own, audited against
the paper by itself. `CONTEXT.md` records that decision. The groundwork below is kept from that
pass, because re-deriving it is the expensive part.

**Present so far: Lemma 3, and the two notions it needed — `BlockPostState` and
Definition 20's `finalityActionState`.**

## The nine lemmas, and what each waits on

Section 3 "Deterministic finality state machine" (lines 535–980) and Section 4 "Accountable
safety" (lines 981–1197). Theorem 5 (`thm:accountable-safety`) is in Section 4 too but is not a
lemma, so it is not one of these.

| № | `\label` | Lines | Statable today? |
| --- | --- | --- | --- |
| 3 | `lem:empty-slot-noop` | 879–891 | **yes, as a `theorem`** — landed |
| 4 | `lem:finalized-before-justified` | 920–931 | likely yes — see below |
| 5 | `lem:target-uniqueness` | 967–973 | no — Defs. 21 and 11 |
| 6 | `lem:height-progression` | 987–994 | **in part, and nothing is missing** — see below |
| 7 | `lem:height-target-freshness` | 1002–1009 | no — `σ[·]` at a named earlier block |
| 8 | `lem:chain-target-uniqueness` | 1029–1041 | likely yes, over two block post-states |
| 9 | `lem:target-bit-compression` | 1061–1073 | no — the paper gives it no formal shape |
| 10 | `lem:past-finalized` | 1092–1101 | no — Defs. 21 and 11 |
| 11 | `lem:finalized-chain` | 1139–1146 | no — Def. 21 and Ass. 1's fault bound |

**`BlockPostState` replaces `σ[B]` in most places, which is what unblocked Lemma 3.** The paper
writes `σ[B]` where it needs "the state of the chain ending at `B`". A block post-state *is* such a
state, and its own `L` field names that `B`, so a statement of the form "for the chain ending at
`B`" becomes "for a block post-state `σ`, with `B = σ.L`". Nothing about the store or the
state-root function is needed for that reading.

`σ[·]` as a *map* is still needed where a lemma reaches a **named earlier block's** state rather
than the current one — Lemma 7's "the chain's post-state at `T`" is the clear case, `T` being an
ancestor of `B`. Getting at that needs either Figure 3's map or a lemma relating `BlockPostState`
to ancestors.

So the count of five waiting on `σ[B]` was pessimistic. Lemma 3 is done; Lemmas 4, 8 and 10 look
expressible over `BlockPostState` too, and each will be checked when it is reached rather than
assumed here. Lemma 6's increment half remains independently statable, needing only
`advanceHeight`.

## What the specification does not yet carry

| Absent | Paper | Waited on by |
| --- | --- | --- |
| certificates, and "finalized at height `h`" | Def. 21 (`def:certificates`) | 5, 6, 10, 11 |
| the slashing conditions E1 and E2 | Def. 11 (`def:slashing`) | 5, 10 |
| Assumption 1's Byzantine weight `b` and `3b < W` | Ass. 1 (`ass:fixed-electorate`) | 11 |
| `σ[·]` as a map, for a *named earlier* block's state | Figure 3 (`alg:store`), `derive_block_states` | 7 |

`Electorate` carries `V`, `w` and `w_pos` only, which is why the fault bound is on that list.

**Two notions the paper numbers are not on it**, because the state machine already pins them
down: state-height (Def. 6, `def:state-height`) and the current-height target (Def. 7,
`def:current-height-target`) are `σ.h` and `σ.T_h` of the replayed state. Worth knowing before
anyone models them separately.

**Why `σ[·]` is not a fold of `stateTransition`**, which is what makes `BlockPostState` the
honest substitute rather than a shortcut. Measured against `height_filter_healing.tex:1555-1577`:
the map is built by `derive_block_states` in Figure 3 (`alg:store`), and a block enters it only
when all of

    structural_precheck(x, B, B.parent) = valid          -- Definition 24's first part
    state_transition(σ[B.parent], B) ≠ invalid
    B's claimed post-state root = root(σ')               -- needs a state-root function

hold, over the objects of a store `S` whose clock admits the block's slot. A withdrawn earlier pass
defined `replayChain` as the plain fold and called it `σ[B]`; it omitted the precheck and the
claimed-root check, so it accepted a block whose `claimedRoot` disagrees with its own post-state,
which Figure 3 rejects. `BlockPostState` omits the same two checks but does not claim to be
`σ[·]` — it is only a superset of it, which is why a theorem over it is stronger rather than wrong.

Note also that Definition 24 governs *when* `state_transition` is called and that it is total; the
map itself is Figure 3's. An earlier note here said the replay belonged in `Spec` under
Definition 24. It does not.

## Two shapes, when statements do start landing

Every lemma written down but unproved is one state — `MAPPING.md` marks it 🔨 *stated*. The Lean
shape is forced by how much vocabulary exists and is not a difference in progress:

* `theorem … := sorry` where the paper's sentence is expressible. `make dev` allows the `sorry`
  and counts it; `make check` refuses it.
* `def … : Prop`, taking the absent notion as an argument, where it is not. It must not be a
  `theorem`: over an unconstrained argument the claim would be *false* rather than unproved, and
  a `sorry` would hide that.

`make check` catches only the first shape, so green means "no `sorry`", not "the paper's results
are proved". `MAPPING.md` is what answers the second question.
-/

set_option autoImplicit false

namespace Decoupled

open scoped Decoupled
open Framework.StsMultisetLog

variable {Node Root : Type}

section
variable [DecidableEq Node] [DecidableEq Root] [Electorate Node] [Params]

/-! ## What the analysis quantifies over -/

/-- `σ` is a **block post-state**: reachable from `ChainState.gen` by `stateTransition` along a
    chain of blocks. That is the paper's own term — Lemmas 4 and 10 say "every reachable block
    post-state".

    **Deliberately weaker than the paper's `σ[·]`.** Figure 3 (`alg:store`) admits a block only
    when the structural precheck passes and its claimed post-state root equals `root(σ')`, and
    neither the precheck nor a state-root function is modelled, so neither is required here. This
    predicate therefore holds of *more* states than `σ[·]` does, which makes a theorem carrying it
    as a hypothesis **stronger** than the paper's, and one that specialises to the paper's sentence
    when Figure 3 lands.

    It is not called `σ[·]`, and must not be: the earlier `replayChain` was withdrawn precisely
    for claiming to be that map while omitting both checks. -/
inductive BlockPostState : ChainState Node Root → Prop
  /-- Genesis: the values Definition 13 (`def:chain-state`) lists, which Figure 1's **Genesis**
      block repeats. -/
  | gen : BlockPostState ChainState.gen
  /-- One accepted block later. -/
  | step {σ σ' : ChainState Node Root} {B : Blk Node Root} :
      BlockPostState σ → stateTransition σ B = .state σ' → BlockPostState σ'

/-- Definition 20 (`def:finality-action-state`): `σ_a[X] = process_slots(σ[X], slot(a))`, the state
    a signing action reads, got by closing exactly the slots before the action.

    The definition is that one application of `process_slots`, so this renders all of it. Written
    over a block post-state rather than over `σ[X]`, for the reason in `BlockPostState`.

    Definition 20's side condition `X.slot ≤ slot(a)` is `σ.L.slot ≤ t` here, and it is carried by
    the lemmas that use this rather than by the definition, which is where the paper puts it.

    It sits in the analysis rather than in `Spec` only because it reads a figure's routine, and
    `Spec/Defs/` is for what the figures read. Move it if that layering is settled otherwise. -/
def finalityActionState (σ : ChainState Node Root) (t : Time) : ChainState Node Root :=
  processSlots σ t

/-! ## Section 3 — deterministic finality state machine -/

/-- **Lemma 3** (`lem:empty-slot-noop`, lines 879–891): an empty slot never changes height,
    finality, or participation.

    Read aloud: closing empty slots can name a pending target, but can never advance the chain.

    The paper compares `σ_a[X]` with `σ[X]`. Definition 20 makes the first `process_slots` of the
    second, so the claim is about `process_slots` over a block post-state — which is why it needs
    neither Figure 3 nor Definition 20 as an argument, and is a `theorem` rather than a
    `def … : Prop`.

    **Stronger than the paper's sentence**, since `BlockPostState` admits more states than `σ[·]`.

    The conclusion lists every field of Definition 13 (`def:chain-state`) except the two the paper
    allows to differ: `s`, which the closure advances, and `T_h`, which it may fill. `h` is among
    the eleven, which is the paper's own emphasis and also how its closing clause — every height
    transition is consumed at a block — is expressed here.

    Two of the paper's words are avoided, it defining neither: "slot cursor" for `s`, and
    "materialized" for filling `T_h`.

    **The proof needs an invariant the paper argues in prose**: that the height-event check cannot
    fire in a block post-state, because `state_transition` already ran it at the block and left its
    conditions false. `process_slots` is a `while`, so read the `lean-proof-idioms` skill before
    attempting it. -/
theorem lemEmptySlotNoop :
    ∀ (σ : ChainState Node Root) (t : Time),
      BlockPostState σ → σ.L.slot ≤ t →
        (finalityActionState σ t).L = σ.L ∧
        (finalityActionState σ t).h = σ.h ∧
        (finalityActionState σ t).s_h = σ.s_h ∧
        (finalityActionState σ t).nj = σ.nj ∧
        (finalityActionState σ t).J = σ.J ∧
        (finalityActionState σ t).h_j = σ.h_j ∧
        (finalityActionState σ t).F = σ.F ∧
        (finalityActionState σ t).h_F = σ.h_F ∧
        (finalityActionState σ t).P = σ.P ∧
        (finalityActionState σ t).targetParticipation = σ.targetParticipation ∧
        (finalityActionState σ t).progress = σ.progress := by
  sorry

end

end Decoupled
