import Spec

/-!
# The numbered lemmas of Sections 3 and 4

*Height Filtering and Healing for a Simplex-Style Finality Variant*
(`height_filter_healing.tex`), Section 3 "Deterministic finality state machine" and Section 4
"Accountable safety". Nine lemmas, printed numbers 3 to 11.

**Nothing here is proved.** Every proof is `sorry`, which `make dev` allows and counts and
`make check` refuses. `make sorries` lists them.

## Two Lean shapes, one state

Every lemma here is in the same state: written down, not proved. The two shapes below are
forced by how much vocabulary the specification has, and are **not** a difference in progress.
`MAPPING.md` marks all of them 🔨 *stated* for that reason.

A lemma whose sentence the current vocabulary can express is a `theorem … := sorry`.

A lemma whose sentence quantifies over something this project has not modelled is a
`def … : Prop`, taking the absent notion as an explicit argument. It has to be a `def` rather
than a `theorem` because over an unconstrained argument the claim would be *false* rather than
unproved, and a `sorry` would hide that. Each becomes a `theorem` when its argument can be
replaced by a real definition.

**`make check` only catches the first shape.** A `def … : Prop` holds no `sorry`, so the strict
target passes it. Green means "no `sorry`", not "these lemmas are proved"; `MAPPING.md` is what
answers the second question.

## What is missing, and which lemma needs it

| Absent | Paper | Needed by |
| --- | --- | --- |
| the finality action state `σ_a[X]` | Def. 20 (`def:finality-action-state`) | Lemmas 3, 4, 10 |
| certificates, and "finalized at height `h`" | Def. 21 (`def:certificates`) | Lemmas 5, 6, 10, 11 |
| the slashing conditions E1 and E2 | Def. 11 (`def:slashing`) | Lemmas 5, 10 |
| Assumption 1's Byzantine weight `b` and `3b < W` | Ass. 1 (`ass:fixed-electorate`) | Lemma 11 |

`Electorate` carries `V`, `w` and `w_pos` only, which is why the fault bound is on that list.

Two notions the paper numbers are **not** on it, because the state machine already pins them
down: state-height (Def. 6, `def:state-height`) and the current-height target (Def. 7,
`def:current-height-target`) are `σ.h` and `σ.T_h` of the replayed state, so Lemmas 7 and 8 are
statable without new vocabulary.
-/

set_option autoImplicit false

namespace Decoupled

open scoped Decoupled
open Framework.StsMultisetLog

variable {Node Root : Type}

section
variable [DecidableEq Node] [DecidableEq Root] [Electorate Node] [Params]

/-! ## The chain replay, `σ[B]` -/

/-- `σ[B]`: the deterministic state derivation along the chain ending at `B`. `ChainState.gen`
    at genesis, then `stateTransition` at each block after it, so one failed check makes the
    whole chain `invalid`. Section 4's proofs walk exactly this.

    **This is not offered as Definition 24 (`def:total-raw-replay`).** That definition also
    carries slot eligibility conditions this project has not modelled, and `MAPPING.md` records
    only its "a state or `invalid`" half as rendered. What is written here is the fold of
    `stateTransition` and nothing more. Move it into the specification, under that number, when
    the rest of Definition 24 lands. -/
def replayChain : Blk Node Root → TransitionResult Node Root
  | .genesis => .state ChainState.gen
  | .mk p s n as r =>
      match replayChain p with
      | .state σ => stateTransition σ (.mk p s n as r)
      | .invalid => invalid

/-! ## Section 3 — deterministic finality state machine -/

/-- **Lemma 3** (`lem:empty-slot-noop`, lines 879–891): an empty slot never changes height,
    finality, or participation.

    Read aloud: closing empty slots can name a pending target but can never advance the chain.

    `actionState X t` stands for the paper's `σ_a[X]` at action slot `t`, which is
    Definition 20 (`def:finality-action-state`) and is **not modelled**. The shape here — a
    block and a slot giving a state or `invalid` — is this file's guess and has to be checked
    against that definition when it lands.

    The conclusion lists every field the paper says is unchanged. The two it permits to differ
    are `s`, advanced to the action slot, and `T_h`, which may gain a target name. The paper's
    final clause, that every height transition is consumed at a block, is what `σ_a[X].h = σ[X].h`
    expresses here. -/
def lemEmptySlotNoop
    (actionState : Blk Node Root → Time → TransitionResult Node Root) : Prop :=
  ∀ (X : Blk Node Root) (t : Time) (σ σa : ChainState Node Root),
    replayChain X = .state σ → actionState X t = .state σa →
      σa.L = σ.L ∧ σa.h = σ.h ∧ σa.nj = σ.nj ∧ σa.s_h = σ.s_h ∧
      σa.J = σ.J ∧ σa.h_j = σ.h_j ∧ σa.F = σ.F ∧ σa.h_F = σ.h_F ∧ σa.P = σ.P ∧
      σa.targetParticipation = σ.targetParticipation ∧ σa.progress = σ.progress

/-- **Lemma 4** (`lem:finalized-before-justified`, lines 920–931): the finalized block precedes
    the justified and latest blocks.

    Read aloud: finality never moves off the current chain or ahead of its latest justification.

    **Narrower than the paper's sentence.** The paper quantifies over "every reachable block
    post-state *and finality action state*"; this covers the block post-states only, because the
    finality action state is Definition 20 and is not modelled. `lemEmptySlotNoop` above is what
    would carry the other half once it is. -/
theorem lemFinalizedBeforeJustified :
    ∀ (B : Blk Node Root) (σ : ChainState Node Root),
      replayChain B = .state σ →
        σ.F ⪯ σ.J ∧ σ.J ⪯ σ.L ∧ σ.h_F ≤ σ.h_j ∧ σ.h_j < σ.h := by
  sorry

/-- **Lemma 5** (`lem:target-uniqueness`, lines 967–973): one height cannot justify two targets.

    Read aloud: one finality height cannot justify two forks without exposing one quorum
    intersection.

    `justCert T h Q` stands for "`Q` is the signer set of a justification certificate for target
    `T` at height `h`", which is Definition 21 (`def:certificates`), and `violatesE2` is the
    second slashing condition of Definition 11 (`def:slashing`). **Neither is modelled**; both
    shapes are this file's guess.

    `2 * q Node - W Node` is the paper's `2q - W` in `Nat` arithmetic, so the subtraction is
    truncated. That is harmless here because the bound is only interesting when `2q > W`, which
    Definition 3 gives. -/
def lemTargetUniqueness
    (justCert : Blk Node Root → Nat → Finset Node → Prop)
    (violatesE2 : Node → Prop) : Prop :=
  ∀ (T T' : Blk Node Root) (h : Nat) (Q Q' : Finset Node),
    justCert T h Q → justCert T' h Q' → ¬ (T ∼ T') →
      ∃ S : Finset Node, (∀ i ∈ S, violatesE2 i) ∧ w(S) ≥ 2 * q Node - W Node

/-! ## Section 4 — accountable safety -/

/-- **Lemma 6** (`lem:height-progression`, lines 987–994): a certificate advances the height by
    one.

    Read aloud: a chain cannot skip a finality height or advance it without a quorum.

    **Narrower than the paper's sentence.** This is the "increments the height by exactly one"
    half, stated about `advanceHeight`, which Figure 2 makes the only routine that changes `h`.
    The paper's second half — that a transition *requires* a justification or progress
    certificate — needs Definition 21 and is not stated. -/
theorem lemHeightProgression :
    ∀ (σ : ChainState Node Root) (justify : Option (Blk Node Root)) (start : Time),
      (advanceHeight σ justify start).h = σ.h + 1 := by
  sorry

/-- **Lemma 7** (`lem:height-target-freshness`, lines 1002–1009): a target bit names the
    current-height target.

    Read aloud: a target bit always refers to the first block of the current height, and is
    processed only by a later block.

    Statable as written. The paper's "the chain's post-state at `T` has current height `h`" is
    state-height, Definition 6 (`def:state-height`), which for a replayed chain is `σ.h` of
    `replayChain T` — so it needs no new vocabulary. `σ.Qtarget.Nonempty` is "a target is counted
    in `Q_target`": the state keeps bits rather than roots, so the target counted is `σ.T_h`,
    which is the lemma's point. -/
theorem lemHeightTargetFreshness :
    ∀ (B : Blk Node Root) (σ : ChainState Node Root),
      replayChain B = .state σ → σ.Qtarget.Nonempty →
        ∃ T : Blk Node Root, σ.T_h = some T ∧ T ≺ B ∧
          ∃ σT : ChainState Node Root, replayChain T = .state σT ∧ σT.h = σ.h := by
  sorry

/-- **Lemma 8** (`lem:chain-target-uniqueness`, lines 1029–1041): a chain has one current-height
    target.

    Read aloud: exact target votes transfer to every extension that contains their target, and
    the broader progress rule does not change the stored target.

    **Narrower than the paper's sentence**, which has three parts. This is the third: distinct
    current-height targets at one height lie on conflicting branches. The first part, that the
    target is the chain's unique first block at that height, is Definition 7
    (`def:current-height-target`) rather than a separate claim; the second, that a target vote
    transfers to every height-`h` branch containing `T` and gives it both bits, quantifies over
    branches of one chain and wants Definition 7 stated first. -/
theorem lemChainTargetUniqueness :
    ∀ (B B' : Blk Node Root) (σ σ' : ChainState Node Root) (T T' : Blk Node Root),
      replayChain B = .state σ → replayChain B' = .state σ' → σ.h = σ'.h →
        σ.T_h = some T → σ'.T_h = some T' → T ≠ T' → ¬ (T ∼ T') := by
  sorry

/-! ### Lemma 9 is not stated here

**Lemma 9** (`lem:target-bit-compression`, lines 1061–1073) says that for a given chain state,
all information the justification and progress rules need is contained in the two Boolean
arrays `target_participation` and `progress`, and that retaining the signed messages suffices
to prove E1 and E2 violations.

It is a sufficiency claim about the representation, and the paper gives it no formal shape:
"all information needed" is not a proposition about the model until someone chooses what
"needed" quantifies over. That is a modelling decision rather than a transcription, so it is
left out rather than guessed at, and `MAPPING.md` keeps its row absent. No declaration here
carries its name.

One honest reading, for whoever takes it on: two chain states agreeing on `Qtarget` and `Qprog`,
and on the fields the height rules read, produce the same `processHeightEvents` outcome. That is
a claim about this rendering and looks provable, but it is narrower than the paper's sentence,
and the half about E1 and E2 needs Definition 11 (`def:slashing`).
-/

/-- **Lemma 10** (`lem:past-finalized`, lines 1092–1101): a chain past a finalized height
    contains its finalized block.

    Read aloud: advancing past a finalized height must either include its finalized block or
    expose the same quorum-intersection fault.

    `finalized C h` is Definition 21 (`def:certificates`) and `e1Slashable` is the first slashing
    condition of Definition 11 (`def:slashing`). **Neither is modelled**; both shapes are this
    file's guess.

    Also narrower than the paper's sentence in the same way as Lemma 4: `σ` here is a block
    post-state, not "a block post-state or a finality action state derived from that chain",
    because Definition 20 is not modelled. The paper's `h ≥ 1` side condition is carried by
    `1 ≤ h`; at `h = 0` the finalized block is genesis and the claim is immediate. -/
def lemPastFinalized
    (finalized : Blk Node Root → Nat → Prop)
    (e1Slashable : Node → Prop) : Prop :=
  ∀ (C B : Blk Node Root) (h : Nat) (σ : ChainState Node Root),
    finalized C h → 1 ≤ h → replayChain B = .state σ → σ.h > h →
      C ⪯ B ∨ ∃ S : Finset Node, (∀ i ∈ S, e1Slashable i) ∧ w(S) ≥ 2 * q Node - W Node

/-- **Lemma 11** (`lem:finalized-chain`, lines 1139–1146): finalized blocks form a chain.

    Read aloud: an honest observer can order every finalized block by ancestry.

    `finalized` is Definition 21 (`def:certificates`), **not modelled**. `faultBound` stands for
    Assumption 1 (`ass:fixed-electorate`)'s `3b < W`; that assumption is titled "Fixed electorate
    and fault bound" and does state the inequality, but `Electorate` carries no Byzantine weight
    `b`, so the bound has no rendering to refer to and is taken as an argument. -/
def lemFinalizedChain
    (finalized : Blk Node Root → Nat → Prop)
    (faultBound : Prop) : Prop :=
  ∀ (C C' : Blk Node Root) (h h' : Nat),
    finalized C h → finalized C' h' → h ≤ h' → faultBound → C ⪯ C'

end

end Decoupled
