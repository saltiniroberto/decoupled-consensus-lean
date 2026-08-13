import Spec

/-!
# The paper's numbered lemmas

*Height Filtering and Healing for a Simplex-Style Finality Variant*
(`height_filter_healing.tex`). Statements of record, one per numbered lemma, proved against the
specification in `Spec`.

**Nothing is stated yet.** This file declares nothing. The nine lemmas of Sections 3 and 4 were
written in one pass on 2026-08-13 and then withdrawn the same day, on instruction: they are to
be added one at a time, each audited against the paper on its own. `CONTEXT.md` records that
decision. What follows is the groundwork from that pass, kept because re-deriving it is the
expensive part.

## The nine lemmas, and what each waits on

Section 3 "Deterministic finality state machine" (lines 535–980) and Section 4 "Accountable
safety" (lines 981–1197). Theorem 5 (`thm:accountable-safety`) is in Section 4 too but is not a
lemma, so it is not one of these.

| № | `\label` | Lines | Statable today? |
| --- | --- | --- | --- |
| 3 | `lem:empty-slot-noop` | 879–891 | no — needs Def. 20 |
| 4 | `lem:finalized-before-justified` | 920–931 | in part — block post-states only |
| 5 | `lem:target-uniqueness` | 967–973 | no — needs Defs. 21 and 11 |
| 6 | `lem:height-progression` | 987–994 | in part — the increment half only |
| 7 | `lem:height-target-freshness` | 1002–1009 | yes |
| 8 | `lem:chain-target-uniqueness` | 1029–1041 | in part — conflicting-branch half only |
| 9 | `lem:target-bit-compression` | 1061–1073 | no — the paper gives it no formal shape |
| 10 | `lem:past-finalized` | 1092–1101 | no — needs Defs. 21, 11 and 20 |
| 11 | `lem:finalized-chain` | 1139–1146 | no — needs Def. 21 and Ass. 1's fault bound |

## What the specification does not yet carry

| Absent | Paper | Waited on by |
| --- | --- | --- |
| the finality action state `σ_a[X]` | Def. 20 (`def:finality-action-state`) | 3, 4, 10 |
| certificates, and "finalized at height `h`" | Def. 21 (`def:certificates`) | 5, 6, 10, 11 |
| the slashing conditions E1 and E2 | Def. 11 (`def:slashing`) | 5, 10 |
| Assumption 1's Byzantine weight `b` and `3b < W` | Ass. 1 (`ass:fixed-electorate`) | 11 |
| the chain replay `σ[B]` | part of Def. 24 (`def:total-raw-replay`) | 3, 4, 7, 10 |

`Electorate` carries `V`, `w` and `w_pos` only, which is why the fault bound is on that list.

**Two notions the paper numbers are not on it**, because the state machine already pins them
down: state-height (Def. 6, `def:state-height`) and the current-height target (Def. 7,
`def:current-height-target`) are `σ.h` and `σ.T_h` of the replayed state. Worth knowing before
anyone models them separately.

**The chain replay is the one to settle first**, since four lemmas quantify over it. The earlier
pass defined it inside this file as the fold of `stateTransition` from `ChainState.gen`, and that
is almost certainly the right content — but it belongs in `Spec` under Definition 24 rather than
here, and Definition 24 also carries slot eligibility conditions that are not modelled. Decide
where it lives before the first lemma that needs it.

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
