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

**Present so far: Lemma 3.**

## The nine lemmas, and what each waits on

Section 3 "Deterministic finality state machine" (lines 535–980) and Section 4 "Accountable
safety" (lines 981–1197). Theorem 5 (`thm:accountable-safety`) is in Section 4 too but is not a
lemma, so it is not one of these.

| № | `\label` | Lines | Statable today? |
| --- | --- | --- | --- |
| 3 | `lem:empty-slot-noop` | 879–891 | no — `σ[B]`, and Def. 20 |
| 4 | `lem:finalized-before-justified` | 920–931 | no — `σ[B]`; Def. 20 for the full sentence |
| 5 | `lem:target-uniqueness` | 967–973 | no — Defs. 21 and 11 |
| 6 | `lem:height-progression` | 987–994 | **in part, and nothing is missing** — see below |
| 7 | `lem:height-target-freshness` | 1002–1009 | no — `σ[B]`, twice |
| 8 | `lem:chain-target-uniqueness` | 1029–1041 | no — `σ[B]`, on two chains |
| 9 | `lem:target-bit-compression` | 1061–1073 | no — the paper gives it no formal shape |
| 10 | `lem:past-finalized` | 1092–1101 | no — `σ[B]`, and Defs. 21, 11, 20 |
| 11 | `lem:finalized-chain` | 1139–1146 | no — Def. 21 and Ass. 1's fault bound |

**Exactly one statement can be written today: the increment half of Lemma 6.** "Every height
transition increments the height by exactly one" is a claim about `advanceHeight`, which Figure 2
makes the only routine that changes `h`, and it mentions nothing absent. The lemma's other half —
that a transition *requires* a justification or progress certificate — needs Definition 21.

Everything else waits, and five of the nine wait on `σ[B]` alone: Lemmas 3, 4, 7, 8 and 10.

## What the specification does not yet carry

| Absent | Paper | Waited on by |
| --- | --- | --- |
| the finality action state `σ_a[X]` | Def. 20 (`def:finality-action-state`) | 3, 4, 10 |
| certificates, and "finalized at height `h`" | Def. 21 (`def:certificates`) | 5, 6, 10, 11 |
| the slashing conditions E1 and E2 | Def. 11 (`def:slashing`) | 5, 10 |
| Assumption 1's Byzantine weight `b` and `3b < W` | Ass. 1 (`ass:fixed-electorate`) | 11 |
| the replayed state `σ[B]` | Figure 3 (`alg:store`), `derive_block_states` | 3, 4, 7, 8, 10 |

`Electorate` carries `V`, `w` and `w_pos` only, which is why the fault bound is on that list.

**Two notions the paper numbers are not on it**, because the state machine already pins them
down: state-height (Def. 6, `def:state-height`) and the current-height target (Def. 7,
`def:current-height-target`) are `σ.h` and `σ.T_h` of the replayed state. Worth knowing before
anyone models them separately.

**`σ[B]` waits on Figure 3, and is not a fold of `stateTransition`.** Measured 2026-08-13 against
`height_filter_healing.tex:1555-1577`: the map is built by `derive_block_states` in Figure 3
(`alg:store`), and a block enters it only when

    structural_precheck(x, B, B.parent) = valid          -- Definition 24's first part
    state_transition(σ[B.parent], B) ≠ invalid
    B's claimed post-state root = root(σ')               -- a state-root function

all hold, over the objects of a store `S` whose clock admits the block's slot. The withdrawn pass
defined `replayChain` here as the plain fold of `stateTransition` from `ChainState.gen`, and that
was **not** a faithful `σ[B]`: it omitted the precheck and the claimed-root check, so it accepts a
block whose `claimedRoot` disagrees with its own post-state, which Figure 3 rejects.

An earlier note in this file and in `CONTEXT.md` said the replay "belongs in `Spec` under
Definition 24". That was wrong — Definition 24 governs *when* `state_transition` is called and
that it is total; the map itself is Figure 3's. So the four lemmas that quantify over `σ[B]` wait
on Figure 3, on a state-root function, and on the store of Definitions 22 and 23, none of which is
modelled. Five of the nine quantify over it — Lemmas 3, 4, 7, 8 and 10 — so it is the single
largest thing standing between this file and the paper's Sections 3 and 4.

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

/-! ## Section 3 — deterministic finality state machine -/

/-- **Lemma 3** (`lem:empty-slot-noop`, lines 879–891): an empty slot never changes height,
    finality, or participation.

    Read aloud: closing empty slots can name a pending target, but can never advance the chain.

    **Two arguments, because neither notion is modelled.** `blockState X` is the paper's
    `σ[X]`, the map Figure 3 (`alg:store`) builds in `derive_block_states`; `actionState X t` is
    its `σ_a[X]` at action slot `t`, which is Definition 20 (`def:finality-action-state`). Both
    shapes here are this file's guess and have to be checked when those land. That is why this is
    a `def … : Prop` and not a `theorem`: over unconstrained arguments the claim would be false
    rather than unproved.

    **What the conclusion says.** The paper allows `σ_a[X]` to differ from `σ[X]` in two fields
    only — `s`, advanced to the action slot, and `T_h`, which may gain a target name — so every
    other field of Definition 13 (`def:chain-state`) is required equal. `σ_a[X].h = σ[X].h` is
    among them, which is the paper's own emphasis and also how its closing clause, that every
    height transition is consumed at a block, is expressed here.

    Two words in the paper's sentence are avoided: it writes "slot cursor" for `s` and
    "materialized" for filling `T_h`, and defines neither. -/
def lemEmptySlotNoop
    (blockState : Blk Node Root → TransitionResult Node Root)
    (actionState : Blk Node Root → Time → TransitionResult Node Root) : Prop :=
  ∀ (X : Blk Node Root) (t : Time) (σ σa : ChainState Node Root),
    blockState X = .state σ → actionState X t = .state σa →
      σa.L = σ.L ∧ σa.h = σ.h ∧ σa.s_h = σ.s_h ∧ σa.nj = σ.nj ∧
      σa.J = σ.J ∧ σa.h_j = σ.h_j ∧ σa.F = σ.F ∧ σa.h_F = σ.h_F ∧ σa.P = σ.P ∧
      σa.targetParticipation = σ.targetParticipation ∧ σa.progress = σ.progress

end

end Decoupled
