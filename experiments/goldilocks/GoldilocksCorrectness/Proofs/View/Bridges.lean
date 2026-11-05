module
public import GoldilocksCorrectness.Statements.View.SlotConclusionDefs
public import GoldilocksCorrectness.Statements.View.GoldilocksViewDefs
public import GoldilocksCorrectness.Statements.Executions.AsyncResilienceDefs
public import GoldilocksCorrectness.Statements.Executions.FinalityLivenessDefs

@[expose] public section

/-!
# The landed conclusions are their view forms, on the view of a Goldilocks execution

For a Goldilocks execution `x`, its view is `projectTrace nodeView x.toTrace`, and the vocabulary is
`Vocab.goldilocks`. Each landed conclusion of the top statements is defined as its view form on
that view, and each `…_unfold` lemma reads it back on the
execution's node states.

## The readers

- `goldilocks_compatible_iff`: `Vocab.goldilocks.Compatible` is the landed `Block.compatible`;
- `stepBeforeV_toTrace`, `stateBeforeV_nodeView`: the step at which a time is reached, and a
  validator's state then, are the landed `stepBefore` and `stateBefore`;
- `putsBlockV_goldilocks_iff`: a block put on the wire is the landed spelling, a signed block in
  the difference of two sent logs.

## The conclusions are their view forms

By `Iff.rfl`, since each landed conclusion is defined as its view form: `confirmedAgreeBetweenV_iff`,
`confirmedMonotoneBetweenV_iff`, `confirmedAgreeAfterHealingV_iff`,
`confirmedMonotoneAfterHealingV_iff`, `rootCollisionHeldByV_iff`, `rootCollisionAtProposalV_iff`,
`rootCollisionAtOpeningV_iff`, `confirmedIncludedBetweenV_iff`, `confirmedIncludedAfterHealingV_iff`,
`confirmedPersistsBetweenV_iff`, `finalizedCompatibleBetweenV_iff`, `confirmedPersistsFromV_iff`,
`finalizedCompatibleFromV_iff`, `finalityIncludedBetweenV_iff`, `finalityIncludedAfterHealingV_iff`.
With a proof: `finalizedCompatibleUpToV_iff` (Lemma 86's conclusion, which has no landed name) and
`proposalAtV_iff` (`ProposalAt` is not a conclusion and keeps its landed body).


-/

set_option autoImplicit false

open GoldilocksCorrectness.Statements.Routines (Δ slotStart supportCutoff proposalWindowStart
  confirmedOf)

namespace GoldilocksCorrectness.Proofs.View

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Network
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.View

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The readers -/

omit [Fintype V] in
/-- Two blocks are compatible in Goldilocks's vocabulary exactly when the landed
`Block.compatible` says so.

Why: both say that one block is the other or an ancestor of it, the vocabulary as a `Prop`, the
landed definition as a `Bool`.

The variables:
- `b`, `b'`: the two blocks.

Read aloud: the vocabulary's compatibility is Goldilocks's. -/
theorem goldilocks_compatible_iff (b b' : Block V) :
    (Vocab.goldilocks (V := V)).Compatible b b' ↔ b.compatible b' = true := by
  simp only [ViewVocab.Compatible, Vocab.goldilocks, Block.AncestorEq, Block.compatible,
    Bool.or_eq_true]

omit [Fintype V] in
/-- The validator `v` puts a message carrying the block `b` on the wire at the step `i` of a trace
`x` of Goldilocks objects exactly when `v`'s signed message `.block b` is among what that step adds
to the sent log.

Why: the only object carrying a block is the block itself (`blockOf`), so the signed message is
`v`'s `.block b`.

The variables:
- `x`: the trace; `i`: the step; `v`: the signer; `b`: the block.

Read aloud: putting a block on the wire is sending it. -/
theorem putsBlockV_goldilocks_iff {St Ev : Type} (x : Trace V (NamedObject V) St Ev) (i : ℕ)
    (v : V) (b : Block V) :
    PutsBlockV Vocab.goldilocks x i v b ↔
      (⟨v, NamedObject.block b⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent := by
  constructor
  · rintro ⟨⟨v', o⟩, hm, hv, hb⟩
    cases o with
    | block b' =>
      simp only [Vocab.goldilocks, blockOf, Option.some.injEq] at hb
      subst hv hb
      exact hm
    | gfVote _ => simp [Vocab.goldilocks, blockOf] at hb
    | attest _ => simp [Vocab.goldilocks, blockOf] at hb
  · intro h
    exact ⟨_, h, rfl, rfl⟩

section Execution

variable [RootOrder] {S : Setup V} {Sched : Schedule V} (x : AtomicExec (protocol S) Sched)

/-- The step at which the trace of `x` moves to the time `t` is the landed `stepBefore x t`.

Why: both are the first step whose label is the tick at `t`, `0` when there is none; they differ
only in how the search is decided.

The variables:
- `x`: the execution; `t`: the time.

Read aloud: the trace and the execution move to each time at the same step. -/
theorem stepBeforeV_toTrace (t : ℕ) : stepBeforeV x.toTrace t = stepBefore x t := by
  classical
  unfold stepBeforeV stepBefore
  by_cases h : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake t
  · have h' : ∃ i : ℕ, x.toTrace.lbl i = AtomicAction.tickAllAwake t := h
    rw [dif_pos h', dif_pos h]
    exact Nat.find_congr' Iff.rfl
  · have h' : ¬ ∃ i : ℕ, x.toTrace.lbl i = AtomicAction.tickAllAwake t := h
    rw [dif_neg h', dif_neg h]

/-- `v`'s view when the view of `x` moves to the time `t` is `nodeView` of the landed
`stateBefore x t v`.

The variables:
- `x`: the execution; `t`: the time; `v`: the validator.

Read aloud: what the view shows of `v` when the time becomes `t` is `v`'s node state then, read as
a view. -/
theorem stateBeforeV_nodeView (t : ℕ) (v : V) :
    stateBeforeV (projectTrace nodeView x.toTrace) t v = nodeView (stateBefore x t v) := by
  rw [stateBeforeV_projectTrace]
  unfold stateBeforeV
  rw [stepBeforeV_toTrace]
  rfl

/-! ## The conclusions are their view forms

Every landed conclusion is defined as its view form on the view of `x`, so each bridge
holds by `Iff.rfl`. Lemma 86's conclusion has no landed name; its bridge is the one proof of this
section. -/

/-- Lemma 86's conclusion on the view of `x`, read up to `t`, is its landed spelling (the last
disjunct of `lem86_healed_finality_safety_until`).

Why: field by field the same, the compatibility through `goldilocks_compatible_iff`.

The variables:
- `x`: the execution; `t`: the time up to which the steps are read.

Read aloud: on the view, two honest validators' finalized blocks are compatible up to `t` exactly
when they are in the execution. -/
theorem finalizedCompatibleUpToV_iff (t : ℕ) :
    FinalizedCompatibleUpToV Vocab.goldilocks Sched (projectTrace nodeView x.toTrace) t ↔
      ∀ (v₁ v₂ : V) (i j : ℕ), HonestThrough x i v₁ → HonestThrough x j v₂ →
        x[i].time ≤ t → x[j].time ≤ t →
        (x[i][v₁].st).S.F.compatible (x[j][v₂].st).S.F = true :=
  forall₄_congr fun _ _ _ _ => imp_congr_right fun _ => imp_congr_right fun _ =>
    imp_congr_right fun _ => imp_congr_right fun _ => goldilocks_compatible_iff _ _

/-- Lemma 90's agreement on the view of `x` is `ConfirmedAgreeBetween`, by `Iff.rfl`.

The variables:
- `x`: the execution; `tE`, `t`: the two ends.

Read aloud: on the view, the confirmed tips agree from `tE` up to `t` exactly when they do in the
execution. -/
theorem confirmedAgreeBetweenV_iff (tE t : ℕ) :
    ConfirmedAgreeBetweenV Vocab.goldilocks Sched (projectTrace nodeView x.toTrace) tE t ↔
      ConfirmedAgreeBetween S Sched x tE t := Iff.rfl

/-- Lemma 90's growth on the view of `x` is `ConfirmedMonotoneBetween`, by `Iff.rfl`.

The variables:
- `x`: the execution; `tE`, `t`: the two ends.

Read aloud: on the view, the confirmed tips grow from `tE` up to `t` exactly when they do in the
execution. -/
theorem confirmedMonotoneBetweenV_iff (tE t : ℕ) :
    ConfirmedMonotoneBetweenV Vocab.goldilocks Sched (projectTrace nodeView x.toTrace) tE t ↔
      ConfirmedMonotoneBetween S Sched x tE t := Iff.rfl

/-- Lemma 90's agreement with no upper end, on the view of `x`, is `ConfirmedAgreeAfterHealing`, by
`Iff.rfl`.

The variables:
- `x`: the execution; `tE`: the time from which the agreement holds.

Read aloud: on the view, the confirmed tips agree from `tE` on exactly when they do in the
execution. -/
theorem confirmedAgreeAfterHealingV_iff (tE : ℕ) :
    ConfirmedAgreeAfterHealingV Vocab.goldilocks Sched (projectTrace nodeView x.toTrace) tE ↔
      ConfirmedAgreeAfterHealing S Sched x tE := Iff.rfl

/-- Lemma 90's growth with no upper end, on the view of `x`, is `ConfirmedMonotoneAfterHealing`, by
`Iff.rfl`.

The variables:
- `x`: the execution; `tE`: the time from which the growth holds.

Read aloud: on the view, the confirmed tips grow from `tE` on exactly when they do in the
execution. -/
theorem confirmedMonotoneAfterHealingV_iff (tE : ℕ) :
    ConfirmedMonotoneAfterHealingV Vocab.goldilocks Sched (projectTrace nodeView x.toTrace) tE ↔
      ConfirmedMonotoneAfterHealing S Sched x tE := Iff.rfl

/-- The root collision held by `t`, on the view of `x`, is `RootCollisionHeldBy`, by `Iff.rfl`.

The variables:
- `x`: the execution; `t`: the bound on the time.

Read aloud: on the view, two blocks honest validators hold by `t` share a root exactly when they do
in the execution. -/
theorem rootCollisionHeldByV_iff (t : ℕ) :
    RootCollisionHeldByV Vocab.goldilocks Sched (projectTrace nodeView x.toTrace) t ↔
      RootCollisionHeldBy S Sched x t := Iff.rfl

/-- A proposal on the view of `x` is the landed `ProposalAt`.

Why: the tick is the same label; the block put on the wire through `putsBlockV_goldilocks_iff`.

The variables:
- `x`: the execution; `s`: the slot; `b`: the block.

Read aloud: on the view, `b` is slot `s`'s proposal exactly when it is in the execution. -/
theorem proposalAtV_iff (s : ℕ) (b : Block V) :
    ProposalAtV Vocab.goldilocks S (projectTrace nodeView x.toTrace) s b ↔ ProposalAt S Sched x s b :=
  exists_congr fun i => and_congr Iff.rfl
    (putsBlockV_goldilocks_iff (projectTrace nodeView x.toTrace) i (S.P.proposer s) b)

/-- A root collision at a proposal, on the view of `x`, is `RootCollisionAtProposal`, by `Iff.rfl`.

The variables:
- `x`: the execution; `s`: the slot; `b`: the proposal.

Read aloud: on the view, a block the proposer held has the proposal's root exactly when it has in
the execution. -/
theorem rootCollisionAtProposalV_iff (s : ℕ) (b : Block V) :
    RootCollisionAtProposalV Vocab.goldilocks S (projectTrace nodeView x.toTrace) s b ↔
      RootCollisionAtProposal S Sched x s b := Iff.rfl

/-- A root collision at an honest round opening slot, on the view of `x`, is
`RootCollisionAtOpening`, by `Iff.rfl`.

The variables:
- `x`: the execution; `r`: the rounds of the honest round opening slots; `m`: the index of the
  last one.

Read aloud: on the view, a collision hits an honest round opening slot's proposal exactly when it
does in the execution. -/
theorem rootCollisionAtOpeningV_iff (r : ℕ → ℕ) (m : ℕ) :
    RootCollisionAtOpeningV Vocab.goldilocks S (projectTrace nodeView x.toTrace) r m ↔
      RootCollisionAtOpening S Sched x r m := Iff.rfl

/-- Lemma 90's inclusion, read up to `t`, on the view of `x`, is `ConfirmedIncludedBetween`, by
`Iff.rfl`.

The variables:
- `x`: the execution; `tE`, `t`: the two ends.

Read aloud: on the view, honest proposals join the confirmed tips from `tE` and up to `t` exactly
when they do in the execution. -/
theorem confirmedIncludedBetweenV_iff (tE t : ℕ) :
    ConfirmedIncludedBetweenV Vocab.goldilocks S Sched (projectTrace nodeView x.toTrace) tE t ↔
      ConfirmedIncludedBetween S Sched x tE t := Iff.rfl

/-- Lemma 90's inclusion with no upper end, on the view of `x`, is `ConfirmedIncludedAfterHealing`,
by `Iff.rfl`.

The variables:
- `x`: the execution; `tE`: the time from which the slots are read.

Read aloud: on the view, honest proposals join the confirmed tips from `tE` exactly when they do in
the execution. -/
theorem confirmedIncludedAfterHealingV_iff (tE : ℕ) :
    ConfirmedIncludedAfterHealingV Vocab.goldilocks S Sched (projectTrace nodeView x.toTrace) tE ↔
      ConfirmedIncludedAfterHealing S Sched x tE := Iff.rfl

/-- The asynchrony statement's first conclusion, read up to `t`, on the view of `x`, is
`ConfirmedPersistsBetween`, by `Iff.rfl`.

The variables:
- `x`: the execution; `s`: the hand-over slot; `tAwakeEnd`: the time from which the confirmed tips
  are protected; `b₀`: the start of the period; `t`: the time up to which the later steps are read.

Read aloud: on the view, the confirmed tips persist exactly when they do in the execution. -/
theorem confirmedPersistsBetweenV_iff (s tAwakeEnd b₀ t : ℕ) :
    ConfirmedPersistsBetweenV Vocab.goldilocks S Sched (projectTrace nodeView x.toTrace) s
        tAwakeEnd b₀ t ↔
      ConfirmedPersistsBetween S Sched x s tAwakeEnd b₀ t := Iff.rfl

/-- The asynchrony statement's second conclusion, read up to `t`, on the view of `x`, is
`FinalizedCompatibleBetween`, by `Iff.rfl`.

The variables:
- `x`: the execution; `s`: the hand-over slot; `tAwakeEnd`: the time from which the confirmed tips
  are protected; `b₀`: the start of the period; `t`: the time up to which the later steps are read.

Read aloud: on the view, no honest finalized block conflicts with the protected confirmed blocks
exactly when none does in the execution. -/
theorem finalizedCompatibleBetweenV_iff (s tAwakeEnd b₀ t : ℕ) :
    FinalizedCompatibleBetweenV Vocab.goldilocks S Sched (projectTrace nodeView x.toTrace) s
        tAwakeEnd b₀ t ↔
      FinalizedCompatibleBetween S Sched x s tAwakeEnd b₀ t := Iff.rfl

/-- The asynchrony statement's first conclusion with no upper end, on the view of `x`, is
`ConfirmedPersistsFrom`, by `Iff.rfl`.

The variables:
- `x`: the execution; `s`: the hand-over slot; `tAwakeEnd`: the time from which the confirmed tips
  are protected; `b₀`: the start of the period.

Read aloud: on the view, the confirmed tips persist from `b₀` on exactly when they do in the
execution. -/
theorem confirmedPersistsFromV_iff (s tAwakeEnd b₀ : ℕ) :
    ConfirmedPersistsFromV Vocab.goldilocks S Sched (projectTrace nodeView x.toTrace) s
        tAwakeEnd b₀ ↔
      ConfirmedPersistsFrom S Sched x s tAwakeEnd b₀ := Iff.rfl

/-- The asynchrony statement's second conclusion with no upper end, on the view of `x`, is
`FinalizedCompatibleFrom`, by `Iff.rfl`.

The variables:
- `x`: the execution; `s`: the hand-over slot; `tAwakeEnd`: the time from which the confirmed tips
  are protected; `b₀`: the start of the period.

Read aloud: on the view, no honest finalized block from `b₀` on conflicts with the protected
confirmed blocks exactly when none does in the execution. -/
theorem finalizedCompatibleFromV_iff (s tAwakeEnd b₀ : ℕ) :
    FinalizedCompatibleFromV Vocab.goldilocks S Sched (projectTrace nodeView x.toTrace) s
        tAwakeEnd b₀ ↔
      FinalizedCompatibleFrom S Sched x s tAwakeEnd b₀ := Iff.rfl

/-- Lemma 98's conclusion, read up to `t`, on the view of `x`, is `FinalityIncludedBetween`, by
`Iff.rfl`.

The variables:
- `x`: the execution; `tE`, `t`: the two ends.

Read aloud: on the view, honest proposals are finalized as new blocks up to `t` exactly when they
are in the execution. -/
theorem finalityIncludedBetweenV_iff (tE t : ℕ) :
    FinalityIncludedBetweenV Vocab.goldilocks S Sched (projectTrace nodeView x.toTrace) (Δ S) tE t ↔
      FinalityIncludedBetween S Sched x (Δ S) tE t := Iff.rfl

/-- Lemma 98's conclusion with no upper end, on the view of `x`, is `FinalityIncludedAfterHealing`,
by `Iff.rfl`.

The variables:
- `x`: the execution; `tE`: the time from which the slots are read.

Read aloud: on the view, honest proposals are finalized as new blocks from `tE` exactly when they
are in the execution. -/
theorem finalityIncludedAfterHealingV_iff (tE : ℕ) :
    FinalityIncludedAfterHealingV Vocab.goldilocks S Sched (projectTrace nodeView x.toTrace) (Δ S)
        tE ↔
      FinalityIncludedAfterHealing S Sched x (Δ S) tE := Iff.rfl

/-! ## The conclusions read on the execution's node states

Each `…_unfold` states a conclusion definition with its body written on the execution's node states:
the confirmed tip as `confirmedOf`, the finalized block and the tree as the FG state's, a proposal
as a tick of the execution and a send in its sent log, and the compatibility as the `Bool`
`Block.compatible`. a proof that reads a
conclusion on the execution rewrites with them. -/

/-- `ConfirmedAgreeBetween S Sched x tE t` read on the execution: the confirmed tips (`confirmedOf`)
of `v₁` after `i` steps and of `v₂` after `j` steps are compatible (`Block.compatible`), for steps
at times from `tE` to `t` through which each has been honest.

Why: field by field the view form, the compatibility through `goldilocks_compatible_iff`.

The variables:
- `x`: the execution; `tE`, `t`: the two ends.

Read aloud: the agreement from `tE` up to `t` is the compatibility of the node states' confirmed
tips. -/
theorem confirmedAgreeBetween_unfold (tE t : ℕ) :
    ConfirmedAgreeBetween S Sched x tE t ↔
      ∀ (v₁ v₂ : V) (i j : ℕ), HonestThrough x i v₁ → HonestThrough x j v₂ →
        tE ≤ x[i].time → tE ≤ x[j].time → x[i].time ≤ t → x[j].time ≤ t →
        (confirmedOf (x[i][v₁].st)).compatible (confirmedOf (x[j][v₂].st)) = true :=
  forall₄_congr fun _ _ _ _ => imp_congr_right fun _ => imp_congr_right fun _ =>
    imp_congr_right fun _ => imp_congr_right fun _ => imp_congr_right fun _ =>
      imp_congr_right fun _ => goldilocks_compatible_iff _ _

/-- `ConfirmedAgreeAfterHealing S Sched x tE` read on the execution: the confirmed tips of two
validators, after steps at times at least `tE` through which each has been honest, are compatible
(`Block.compatible`).

Why: field by field the view form, the compatibility through `goldilocks_compatible_iff`.

The variables:
- `x`: the execution; `tE`: the time from which the agreement holds.

Read aloud: the agreement from `tE` on is the compatibility of the node states' confirmed tips. -/
theorem confirmedAgreeAfterHealing_unfold (tE : ℕ) :
    ConfirmedAgreeAfterHealing S Sched x tE ↔
      ∀ (v₁ v₂ : V) (i j : ℕ), HonestThrough x i v₁ → HonestThrough x j v₂ →
        tE ≤ x[i].time → tE ≤ x[j].time →
        (confirmedOf (x[i][v₁].st)).compatible (confirmedOf (x[j][v₂].st)) = true :=
  forall₄_congr fun _ _ _ _ => imp_congr_right fun _ => imp_congr_right fun _ =>
    imp_congr_right fun _ => imp_congr_right fun _ => goldilocks_compatible_iff _ _

/-- `ConfirmedMonotoneBetween S Sched x tE t` read on the execution, by `Iff.rfl`: `v`'s confirmed
tip (`confirmedOf`) after `i` steps is an ancestor of, or equal to, the one after `j ≥ i` steps.

The variables:
- `x`: the execution; `tE`, `t`: the two ends.

Read aloud: the growth from `tE` up to `t` is the growth of the node states' confirmed tips. -/
theorem confirmedMonotoneBetween_unfold (tE t : ℕ) :
    ConfirmedMonotoneBetween S Sched x tE t ↔
      ∀ (v : V) (i j : ℕ), i ≤ j → HonestThrough x j v → tE ≤ x[i].time → x[j].time ≤ t →
        (confirmedOf (x[i][v].st)).AncestorEq (confirmedOf (x[j][v].st)) := Iff.rfl

/-- `ConfirmedMonotoneAfterHealing S Sched x tE` read on the execution, by `Iff.rfl`.

The variables:
- `x`: the execution; `tE`: the time from which the growth holds.

Read aloud: the growth from `tE` on is the growth of the node states' confirmed tips. -/
theorem confirmedMonotoneAfterHealing_unfold (tE : ℕ) :
    ConfirmedMonotoneAfterHealing S Sched x tE ↔
      ∀ (v : V) (i j : ℕ), i ≤ j → HonestThrough x j v → tE ≤ x[i].time →
        (confirmedOf (x[i][v].st)).AncestorEq (confirmedOf (x[j][v].st)) := Iff.rfl

/-- `RootCollisionHeldBy S Sched x t` read on the execution, by `Iff.rfl`: two distinct blocks in
the FG state's trees of validators honest at steps at times at most `t` have the same root.

The variables:
- `x`: the execution; `t`: the bound on the time.

Read aloud: by `t`, two distinct blocks honest validators hold share a root. -/
theorem rootCollisionHeldBy_unfold (t : ℕ) :
    RootCollisionHeldBy S Sched x t ↔
      ∃ B B' : Block V, inHonestTreeBy x t B ∧ inHonestTreeBy x t B' ∧ B.root = B'.root ∧
        B ≠ B' := Iff.rfl

/-- `RootCollisionAtProposal S Sched x s B` read on the execution: some block in the FG state's tree
of the proposer of slot `s`, on its node state before the start of slot `s` (`stateBefore`), has
`B`'s root.

Why: the proposer's view when the time becomes the slot's start is its node state then
(`stateBeforeV_nodeView`).

The variables:
- `x`: the execution; `s`: the slot; `B`: the proposal.

Read aloud: a block the proposer held before the proposal's slot has the proposal's root. -/
theorem rootCollisionAtProposal_unfold (s : ℕ) (B : Block V) :
    RootCollisionAtProposal S Sched x s B ↔
      ∃ B' ∈ (stateBefore x (slotStart S s) (S.P.proposer s)).S.T, B'.root = B.root := by
  unfold RootCollisionAtProposal RootCollisionAtProposalV
  rw [stateBeforeV_nodeView]
  exact Iff.rfl

/-- `RootCollisionAtOpening S Sched x r m` read on the execution: for some `i ≤ m`, some proposal
`B` of slot `r i * R` (`ProposalAt`, a tick of the execution and a send in its sent log) has a root
collision at its proposal (`RootCollisionAtProposal`).

Why: a proposal on the view is `ProposalAt` (`proposalAtV_iff`).

The variables:
- `x`: the execution; `r`: the rounds of the honest round opening slots; `m`: the index of the
  last one.

Read aloud: some honest round opening slot's proposal has the root of a block its proposer already
held. -/
theorem rootCollisionAtOpening_unfold (r : ℕ → ℕ) (m : ℕ) :
    RootCollisionAtOpening S Sched x r m ↔
      ∃ i : ℕ, i ≤ m ∧ ∃ B : Block V, ProposalAt S Sched x (r i * S.C.R) B ∧
        RootCollisionAtProposal S Sched x (r i * S.C.R) B :=
  exists_congr fun i => and_congr_right fun _ => exists_congr fun b =>
    and_congr (proposalAtV_iff x (r i * S.C.R) b) Iff.rfl

/-- `ConfirmedIncludedBetween S Sched x tE t` read on the execution: the proposer's condition
written out, the proposal as a tick of the execution and a send in its sent log, the confirmed tips
as `confirmedOf` of the node states.

Why: a proposal on the view is a tick and a send of the execution (`proposalAtV_iff`), and the
view of a validator when the time becomes the support cutoff's successor is its node state then
(`stateBeforeV_nodeView`).

The variables:
- `x`: the execution; `tE`, `t`: the two ends.

Read aloud: the inclusion from `tE` and up to `t`, read on the node states. -/
theorem confirmedIncludedBetween_unfold (tE t : ℕ) :
    ConfirmedIncludedBetween S Sched x tE t ↔
      ∀ s : ℕ, tE ≤ slotStart S s → supportCutoff S (s + 1) ≤ t →
        (∀ t' : ℕ, proposalWindowStart S s ≤ t' → t' ≤ supportCutoff S (s + 1) →
          S.P.proposer s ∈ Sched.awake (t' : Int) ∧ S.P.proposer s ∉ Sched.adv (t' : Int)) →
        (∃ (i : ℕ) (B : Block V), x.lbl i = AtomicAction.tickAllAwake (slotStart S s) ∧
          (⟨S.P.proposer s, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
            x[i + 1].sent - x[i].sent) ∧
        ∀ (i : ℕ) (B : Block V), x.lbl i = AtomicAction.tickAllAwake (slotStart S s) →
          (⟨S.P.proposer s, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
            x[i + 1].sent - x[i].sent →
          RootCollisionAtProposal S Sched x s B ∨
          ((∀ v ∈ honestActiveAt S Sched s,
            confirmedOf (stateBefore x (supportCutoff S (s + 1) + 1) v) = B) ∧
          (∀ (v : V) (j s' : ℕ), HonestThrough x j v → s ≤ s' → v ∈ honestActiveAt S Sched s' →
            supportCutoff S (s' + 1) < x[j].time → x[j].time ≤ t →
            B.AncestorEq (confirmedOf (x[j][v].st)))) := by
  refine forall_congr' fun s => imp_congr_right fun _ => imp_congr_right fun _ =>
    imp_congr_right fun _ => ?_
  have hC : ∀ b : Block V, (∀ v ∈ honestActiveAt S Sched s,
      (stateBeforeV (projectTrace nodeView x.toTrace) (supportCutoff S (s + 1) + 1) v).C = b) ↔
      ∀ v ∈ honestActiveAt S Sched s,
        confirmedOf (stateBefore x (supportCutoff S (s + 1) + 1) v) = b := fun b =>
    forall₂_congr fun v _ => by rw [stateBeforeV_nodeView]; exact Iff.rfl
  refine and_congr ?_ ?_
  · constructor
    · rintro ⟨b, hb⟩
      obtain ⟨i, hl, hsent⟩ := (proposalAtV_iff x s b).1 hb
      exact ⟨i, b, hl, hsent⟩
    · rintro ⟨i, b, hl, hsent⟩
      exact ⟨b, (proposalAtV_iff x s b).2 ⟨i, hl, hsent⟩⟩
  · constructor
    · intro h i b hl hsent
      exact (h b ((proposalAtV_iff x s b).2 ⟨i, hl, hsent⟩)).imp_right
        fun h' => ⟨(hC b).1 h'.1, h'.2⟩
    · intro h b hb
      obtain ⟨i, hl, hsent⟩ := (proposalAtV_iff x s b).1 hb
      exact (h i b hl hsent).imp_right fun h' => ⟨(hC b).2 h'.1, h'.2⟩

/-- `ConfirmedIncludedAfterHealing S Sched x tE` read on the execution, as
`confirmedIncludedBetween_unfold` with no upper end.

Why: as `confirmedIncludedBetween_unfold`.

The variables:
- `x`: the execution; `tE`: the time from which the slots are read.

Read aloud: the inclusion from `tE`, read on the node states. -/
theorem confirmedIncludedAfterHealing_unfold (tE : ℕ) :
    ConfirmedIncludedAfterHealing S Sched x tE ↔
      ∀ s : ℕ, tE ≤ slotStart S s →
        (∀ t : ℕ, proposalWindowStart S s ≤ t → t ≤ supportCutoff S (s + 1) →
          S.P.proposer s ∈ Sched.awake (t : Int) ∧ S.P.proposer s ∉ Sched.adv (t : Int)) →
        (∃ (i : ℕ) (B : Block V), x.lbl i = AtomicAction.tickAllAwake (slotStart S s) ∧
          (⟨S.P.proposer s, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
            x[i + 1].sent - x[i].sent) ∧
        ∀ (i : ℕ) (B : Block V), x.lbl i = AtomicAction.tickAllAwake (slotStart S s) →
          (⟨S.P.proposer s, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
            x[i + 1].sent - x[i].sent →
          RootCollisionAtProposal S Sched x s B ∨
          ((∀ v ∈ honestActiveAt S Sched s,
            confirmedOf (stateBefore x (supportCutoff S (s + 1) + 1) v) = B) ∧
          (∀ (v : V) (j s' : ℕ), HonestThrough x j v → s ≤ s' → v ∈ honestActiveAt S Sched s' →
            supportCutoff S (s' + 1) < x[j].time →
            B.AncestorEq (confirmedOf (x[j][v].st)))) := by
  refine forall_congr' fun s => imp_congr_right fun _ => imp_congr_right fun _ => ?_
  have hC : ∀ b : Block V, (∀ v ∈ honestActiveAt S Sched s,
      (stateBeforeV (projectTrace nodeView x.toTrace) (supportCutoff S (s + 1) + 1) v).C = b) ↔
      ∀ v ∈ honestActiveAt S Sched s,
        confirmedOf (stateBefore x (supportCutoff S (s + 1) + 1) v) = b := fun b =>
    forall₂_congr fun v _ => by rw [stateBeforeV_nodeView]; exact Iff.rfl
  refine and_congr ?_ ?_
  · constructor
    · rintro ⟨b, hb⟩
      obtain ⟨i, hl, hsent⟩ := (proposalAtV_iff x s b).1 hb
      exact ⟨i, b, hl, hsent⟩
    · rintro ⟨i, b, hl, hsent⟩
      exact ⟨b, (proposalAtV_iff x s b).2 ⟨i, hl, hsent⟩⟩
  · constructor
    · intro h i b hl hsent
      exact (h b ((proposalAtV_iff x s b).2 ⟨i, hl, hsent⟩)).imp_right
        fun h' => ⟨(hC b).1 h'.1, h'.2⟩
    · intro h b hb
      obtain ⟨i, hl, hsent⟩ := (proposalAtV_iff x s b).1 hb
      exact (h i b hl hsent).imp_right fun h' => ⟨(hC b).2 h'.1, h'.2⟩

/-- `ConfirmedPersistsBetween S Sched x s tAwakeEnd b₀ t` read on the execution, by `Iff.rfl`.

The variables:
- `x`: the execution; `s`: the hand-over slot; `tAwakeEnd`: the time from which the confirmed tips
  are protected; `b₀`: the start of the period; `t`: the time up to which the later steps are read.

Read aloud: the persistence up to `t`, read on the node states' confirmed tips. -/
theorem confirmedPersistsBetween_unfold (s tAwakeEnd b₀ t : ℕ) :
    ConfirmedPersistsBetween S Sched x s tAwakeEnd b₀ t ↔
      ∀ (v : V) (T : ℕ) (P : Block V),
        HonestThrough x T v → tAwakeEnd ≤ x[T].time → x[T].time ≤ supportCutoff S (s + 1) →
        P.AncestorEq (confirmedOf (x[T][v].st)) →
        ∀ (w : V) (j : ℕ), HonestThrough x j w → w ∈ updaterAt S Sched s →
          b₀ ≤ x[j].time → x[j].time ≤ t →
          P.AncestorEq (confirmedOf (x[j][w].st)) := Iff.rfl

/-- `FinalizedCompatibleBetween S Sched x s tAwakeEnd b₀ t` read on the execution, by `Iff.rfl`.

The variables:
- `x`: the execution; `s`: the hand-over slot; `tAwakeEnd`: the time from which the confirmed tips
  are protected; `b₀`: the start of the period; `t`: the time up to which the later steps are read.

Read aloud: the finalized blocks' compatibility up to `t`, read on the node states. -/
theorem finalizedCompatibleBetween_unfold (s tAwakeEnd b₀ t : ℕ) :
    FinalizedCompatibleBetween S Sched x s tAwakeEnd b₀ t ↔
      ∀ (v : V) (T : ℕ) (P : Block V),
        HonestThrough x T v → tAwakeEnd ≤ x[T].time → x[T].time ≤ supportCutoff S (s + 1) →
        P.AncestorEq (confirmedOf (x[T][v].st)) →
        ∀ (w : V) (j : ℕ), HonestThrough x j w → b₀ ≤ x[j].time → x[j].time ≤ t →
          (P.AncestorEq (x[j][w].st).S.F ∨ (x[j][w].st).S.F.AncestorEq P) := Iff.rfl

/-- `ConfirmedPersistsFrom S Sched x s tAwakeEnd b₀` read on the execution, by `Iff.rfl`.

The variables:
- `x`: the execution; `s`: the hand-over slot; `tAwakeEnd`: the time from which the confirmed tips
  are protected; `b₀`: the start of the period.

Read aloud: the persistence from `b₀` on, read on the node states' confirmed tips. -/
theorem confirmedPersistsFrom_unfold (s tAwakeEnd b₀ : ℕ) :
    ConfirmedPersistsFrom S Sched x s tAwakeEnd b₀ ↔
      ∀ (v : V) (T : ℕ) (P : Block V),
        HonestThrough x T v → tAwakeEnd ≤ x[T].time → x[T].time ≤ supportCutoff S (s + 1) →
        P.AncestorEq (confirmedOf (x[T][v].st)) →
        ∀ (w : V) (j : ℕ), HonestThrough x j w → w ∈ updaterAt S Sched s → b₀ ≤ x[j].time →
          P.AncestorEq (confirmedOf (x[j][w].st)) := Iff.rfl

/-- `FinalizedCompatibleFrom S Sched x s tAwakeEnd b₀` read on the execution, by `Iff.rfl`.

The variables:
- `x`: the execution; `s`: the hand-over slot; `tAwakeEnd`: the time from which the confirmed tips
  are protected; `b₀`: the start of the period.

Read aloud: the finalized blocks' compatibility from `b₀` on, read on the node states. -/
theorem finalizedCompatibleFrom_unfold (s tAwakeEnd b₀ : ℕ) :
    FinalizedCompatibleFrom S Sched x s tAwakeEnd b₀ ↔
      ∀ (v : V) (T : ℕ) (P : Block V),
        HonestThrough x T v → tAwakeEnd ≤ x[T].time → x[T].time ≤ supportCutoff S (s + 1) →
        P.AncestorEq (confirmedOf (x[T][v].st)) →
        ∀ (w : V) (j : ℕ), HonestThrough x j w → b₀ ≤ x[j].time →
          (P.AncestorEq (x[j][w].st).S.F ∨ (x[j][w].st).S.F.AncestorEq P) := Iff.rfl

/-- `FinalityIncludedBetween S Sched x tE t` read on the execution: the proposal as a tick of the
execution and a send in its sent log, the finalized blocks as the FG states'.

Why: a proposal on the view is a tick and a send of the execution (`proposalAtV_iff`); the rest is
the view form's.

The variables:
- `x`: the execution; `tE`, `t`: the two ends.

Read aloud: Lemma 98's conclusion from `tE` and up to `t`, read on the node states. -/
theorem finalityIncludedBetween_unfold (tE t : ℕ) :
    FinalityIncludedBetween S Sched x (Δ S) tE t ↔
      ∀ (s r : ℕ), tE ≤ slotStart S s → HonestOpenerAt S Sched s → s ≤ r * S.C.R →
        FinalityWindowAt S Sched r → supportCutoff S ((r + 3) * S.C.R + 1) ≤ t →
        (∃ (i : ℕ) (B : Block V), x.lbl i = AtomicAction.tickAllAwake (slotStart S s) ∧
          (⟨S.P.proposer s, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
            x[i + 1].sent - x[i].sent) ∧
        ∀ (i : ℕ) (B : Block V), x.lbl i = AtomicAction.tickAllAwake (slotStart S s) →
          (⟨S.P.proposer s, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
            x[i + 1].sent - x[i].sent →
          RootCollisionAtProposal S Sched x s B ∨
          RootCollisionAtOpening S Sched x (fun i => r + i) 3 ∨
          ∀ (v : V) (j : ℕ), HonestThrough x j v →
            (∃ s' : ℕ, x[j].time ≤ supportCutoff S s' ∧ supportCutoff S s' ≤ t) →
            AwakeForDelayWithin S Sched (Δ S) v (slotStart S ((r + 3) * S.C.R)) x[j].time →
            B.AncestorEq (x[j][v].st).S.F ∧
            ∀ (u : V) (i' : ℕ), x[i'].time < slotStart S s →
              (x[i'][u].st).S.F ≠ (x[j][v].st).S.F := by
  refine forall₂_congr fun s r => imp_congr_right fun _ => imp_congr_right fun _ =>
    imp_congr_right fun _ => imp_congr_right fun _ => imp_congr_right fun _ => ?_
  refine and_congr ?_ ?_
  · constructor
    · rintro ⟨b, hb⟩
      obtain ⟨i, hl, hsent⟩ := (proposalAtV_iff x s b).1 hb
      exact ⟨i, b, hl, hsent⟩
    · rintro ⟨i, b, hl, hsent⟩
      exact ⟨b, (proposalAtV_iff x s b).2 ⟨i, hl, hsent⟩⟩
  · constructor
    · intro h i b hl hsent
      exact h b ((proposalAtV_iff x s b).2 ⟨i, hl, hsent⟩)
    · intro h b hb
      obtain ⟨i, hl, hsent⟩ := (proposalAtV_iff x s b).1 hb
      exact h i b hl hsent

/-- `FinalityIncludedBetweenEveryReader S Sched x tE t` read on the execution: the proposal as a
tick of the execution and a send in its sent log, the finalized blocks as the FG states'.

Why: a proposal on the view is a tick and a send of the execution (`proposalAtV_iff`); the rest is
the view form's.

The variables:
- `x`: the execution; `tE`, `t`: the two ends.

Read aloud: Lemma 98's conclusion from `tE` and up to `t`, with every reader up to `t`, read on
the node states. -/
theorem finalityIncludedBetweenEveryReader_unfold (tE t : ℕ) :
    FinalityIncludedBetweenEveryReader S Sched x (Δ S) tE t ↔
      ∀ (s r : ℕ), tE ≤ slotStart S s → HonestOpenerAt S Sched s → s ≤ r * S.C.R →
        FinalityWindowAt S Sched r → supportCutoff S ((r + 3) * S.C.R) ≤ t →
        (∃ (i : ℕ) (B : Block V), x.lbl i = AtomicAction.tickAllAwake (slotStart S s) ∧
          (⟨S.P.proposer s, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
            x[i + 1].sent - x[i].sent) ∧
        ∀ (i : ℕ) (B : Block V), x.lbl i = AtomicAction.tickAllAwake (slotStart S s) →
          (⟨S.P.proposer s, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
            x[i + 1].sent - x[i].sent →
          RootCollisionAtProposal S Sched x s B ∨
          RootCollisionAtOpening S Sched x (fun i => r + i) 3 ∨
          ∀ (v : V) (j : ℕ), HonestThrough x j v → x[j].time ≤ t →
            AwakeForDelayWithin S Sched (Δ S) v (slotStart S ((r + 3) * S.C.R)) x[j].time →
            B.AncestorEq (x[j][v].st).S.F ∧
            ∀ (u : V) (i' : ℕ), x[i'].time < slotStart S s →
              (x[i'][u].st).S.F ≠ (x[j][v].st).S.F := by
  refine forall₂_congr fun s r => imp_congr_right fun _ => imp_congr_right fun _ =>
    imp_congr_right fun _ => imp_congr_right fun _ => imp_congr_right fun _ => ?_
  refine and_congr ?_ ?_
  · constructor
    · rintro ⟨b, hb⟩
      obtain ⟨i, hl, hsent⟩ := (proposalAtV_iff x s b).1 hb
      exact ⟨i, b, hl, hsent⟩
    · rintro ⟨i, b, hl, hsent⟩
      exact ⟨b, (proposalAtV_iff x s b).2 ⟨i, hl, hsent⟩⟩
  · constructor
    · intro h i b hl hsent
      exact h b ((proposalAtV_iff x s b).2 ⟨i, hl, hsent⟩)
    · intro h b hb
      obtain ⟨i, hl, hsent⟩ := (proposalAtV_iff x s b).1 hb
      exact h i b hl hsent

/-- `FinalityIncludedAfterHealing S Sched x tE` read on the execution, as
`finalityIncludedBetween_unfold` with no upper end.

Why: as `finalityIncludedBetween_unfold`.

The variables:
- `x`: the execution; `tE`: the time from which the slots are read.

Read aloud: Lemma 98's conclusion from `tE`, read on the node states. -/
theorem finalityIncludedAfterHealing_unfold (tE : ℕ) :
    FinalityIncludedAfterHealing S Sched x (Δ S) tE ↔
      ∀ (s r : ℕ), tE ≤ slotStart S s → HonestOpenerAt S Sched s → s ≤ r * S.C.R →
        FinalityWindowAt S Sched r →
        (∃ (i : ℕ) (B : Block V), x.lbl i = AtomicAction.tickAllAwake (slotStart S s) ∧
          (⟨S.P.proposer s, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
            x[i + 1].sent - x[i].sent) ∧
        ∀ (i : ℕ) (B : Block V), x.lbl i = AtomicAction.tickAllAwake (slotStart S s) →
          (⟨S.P.proposer s, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
            x[i + 1].sent - x[i].sent →
          RootCollisionAtProposal S Sched x s B ∨
          RootCollisionAtOpening S Sched x (fun i => r + i) 3 ∨
          ∀ (v : V) (j : ℕ), HonestThrough x j v →
            AwakeForDelayWithin S Sched (Δ S) v (slotStart S ((r + 3) * S.C.R)) x[j].time →
            B.AncestorEq (x[j][v].st).S.F ∧
            ∀ (u : V) (i' : ℕ), x[i'].time < slotStart S s →
              (x[i'][u].st).S.F ≠ (x[j][v].st).S.F := by
  refine forall₂_congr fun s r => imp_congr_right fun _ => imp_congr_right fun _ =>
    imp_congr_right fun _ => imp_congr_right fun _ => ?_
  refine and_congr ?_ ?_
  · constructor
    · rintro ⟨b, hb⟩
      obtain ⟨i, hl, hsent⟩ := (proposalAtV_iff x s b).1 hb
      exact ⟨i, b, hl, hsent⟩
    · rintro ⟨i, b, hl, hsent⟩
      exact ⟨b, (proposalAtV_iff x s b).2 ⟨i, hl, hsent⟩⟩
  · constructor
    · intro h i b hl hsent
      exact h b ((proposalAtV_iff x s b).2 ⟨i, hl, hsent⟩)
    · intro h b hb
      obtain ⟨i, hl, hsent⟩ := (proposalAtV_iff x s b).1 hb
      exact h i b hl hsent

end Execution

end GoldilocksCorrectness.Proofs.View
