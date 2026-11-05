module
public import GoldilocksCorrectness.Record.Restated.Statements.View.SlotConclusionDefs
public import GoldilocksCorrectness.Record.Restated.Statements.View.GoldilocksViewDefs
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.AsyncResilienceDefs
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.FinalityLivenessDefs
public import GoldilocksCorrectness.Proofs.View.Bridges

@[expose] public section

/-!
# Bridges, over a model

The theorems of `GoldilocksCorrectness/Proofs/View/Bridges.lean` over a model `M`, for an execution
`x` of `protocolOf M S`, whose view is `projectTrace (nodeView M) x.toTrace`: the step and the node
state at a time read on the view, each conclusion its view form, and each conclusion read back on
the execution's node states. None reads a fact of the model. `goldilocks_compatible_iff` and
`putsBlockV_goldilocks_iff` name no member and read no execution; the twins read the landed ones.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open GoldilocksCorrectness.Statements.Routines (slotStart supportCutoff proposalWindowStart
  confirmedOf)

namespace GoldilocksCorrectness.Record.Proofs.View

open GoldilocksCorrectness.Proofs.View (goldilocks_compatible_iff putsBlockV_goldilocks_iff)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Statements.Network
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (Vocab.goldilocks)
open GoldilocksCorrectness.Statements.AbstractTrace.View (AwakeForDelayWithin)
open GoldilocksCorrectness.Record.Statements.View
open GoldilocksCorrectness.Statements.View (stateBeforeV_projectTrace)
open GoldilocksCorrectness.Statements.AbstractTrace.View (ConfirmedAgreeAfterHealingV ConfirmedAgreeBetweenV ConfirmedMonotoneAfterHealingV ConfirmedMonotoneBetweenV FinalizedCompatibleUpToV RootCollisionHeldByV)

variable {V : Type} [DecidableEq V] [Fintype V]
variable (M : GoldilocksModel V)

/-! ## The readers -/

section Execution

variable [RootOrder] {S : Setup V} {A : Activity V} (x : Trace V (NamedObject V) M.N)

/-! ## The conclusions are their view forms

Every landed conclusion is defined as its view form on the view of `x`, so each bridge
holds by `Iff.rfl`. Lemma 86's conclusion has no landed name; its bridge is the one proof of this
section. -/

/-- Lemma 86's conclusion on the view of `x`, read up to `t`, is its landed spelling (the last
disjunct of `lem86_healed_finality_safety_until`).

Why: field by field the same, the compatibility through `goldilocks_compatible_iff`.

The variables:
- `M`: the model;
- `x`: the execution; `t`: the time up to which the steps are read.

Read aloud: on the view, two honest validators' finalized blocks are compatible up to `t` exactly
when they are in the execution. -/
theorem finalizedCompatibleUpToV_iff (t : ℕ) :
    FinalizedCompatibleUpToV Vocab.goldilocks A ((x.map (nodeView M))) t ↔
      ∀ (v₁ v₂ : V) (i j : ℕ), x.HonestThrough A i v₁ → x.HonestThrough A j v₂ →
        x.time i ≤ t → x.time j ≤ t →
        (x.st i v₁).finalized.compatible (x.st j v₂).finalized = true :=
  forall₄_congr fun _ _ _ _ => imp_congr_right fun _ => imp_congr_right fun _ =>
    imp_congr_right fun _ => imp_congr_right fun _ => goldilocks_compatible_iff _ _

/-- Lemma 90's agreement on the view of `x` is `ConfirmedAgreeBetween`, by `Iff.rfl`.

The variables:
- `M`: the model;
- `x`: the execution; `tE`, `t`: the two ends.

Read aloud: on the view, the confirmed tips agree from `tE` up to `t` exactly when they do in the
execution. -/
theorem confirmedAgreeBetweenV_iff (tE t : ℕ) :
    ConfirmedAgreeBetweenV Vocab.goldilocks A ((x.map (nodeView M))) tE t ↔
      ConfirmedAgreeBetween M S A x tE t := Iff.rfl

/-- Lemma 90's growth on the view of `x` is `ConfirmedMonotoneBetween`, by `Iff.rfl`.

The variables:
- `M`: the model;
- `x`: the execution; `tE`, `t`: the two ends.

Read aloud: on the view, the confirmed tips grow from `tE` up to `t` exactly when they do in the
execution. -/
theorem confirmedMonotoneBetweenV_iff (tE t : ℕ) :
    ConfirmedMonotoneBetweenV Vocab.goldilocks A ((x.map (nodeView M))) tE t ↔
      ConfirmedMonotoneBetween M S A x tE t := Iff.rfl

/-- Lemma 90's agreement with no upper end, on the view of `x`, is `ConfirmedAgreeAfterHealing`, by
`Iff.rfl`.

The variables:
- `M`: the model;
- `x`: the execution; `tE`: the time from which the agreement holds.

Read aloud: on the view, the confirmed tips agree from `tE` on exactly when they do in the
execution. -/
theorem confirmedAgreeAfterHealingV_iff (tE : ℕ) :
    ConfirmedAgreeAfterHealingV Vocab.goldilocks A ((x.map (nodeView M))) tE ↔
      ConfirmedAgreeAfterHealing M S A x tE := Iff.rfl

/-- Lemma 90's growth with no upper end, on the view of `x`, is `ConfirmedMonotoneAfterHealing`, by
`Iff.rfl`.

The variables:
- `M`: the model;
- `x`: the execution; `tE`: the time from which the growth holds.

Read aloud: on the view, the confirmed tips grow from `tE` on exactly when they do in the
execution. -/
theorem confirmedMonotoneAfterHealingV_iff (tE : ℕ) :
    ConfirmedMonotoneAfterHealingV Vocab.goldilocks A ((x.map (nodeView M))) tE ↔
      ConfirmedMonotoneAfterHealing M S A x tE := Iff.rfl

/-- The root collision held by `t`, on the view of `x`, is `RootCollisionHeldBy`, by `Iff.rfl`.

The variables:
- `M`: the model;
- `x`: the execution; `t`: the bound on the time.

Read aloud: on the view, two blocks honest validators hold by `t` share a root exactly when they do
in the execution. -/
theorem rootCollisionHeldByV_iff (t : ℕ) :
    RootCollisionHeldByV Vocab.goldilocks A ((x.map (nodeView M))) t ↔
      RootCollisionHeldBy M S A x t := Iff.rfl

/-- A proposal on the view of `x` is the landed `ProposalAt`.

Why: the tick is the same label; the block put on the wire through `putsBlockV_goldilocks_iff`.

The variables:
- `M`: the model;
- `x`: the execution; `s`: the slot; `b`: the block.

Read aloud: on the view, `b` is slot `s`'s proposal exactly when it is in the execution. -/
theorem proposalAtV_iff (s : ℕ) (b : Block V) :
    ProposalAtV M Vocab.goldilocks S ((x.map (nodeView M))) s b ↔ ProposalAt M S x s b := by
  refine exists_congr fun i => and_congr Iff.rfl ?_
  constructor
  · rintro ⟨⟨v', o⟩, hm, hv, hb⟩
    cases o with
    | block b' =>
      simp only [Vocab.goldilocks, GoldilocksCorrectness.Statements.Executions.blockOf,
        Option.some.injEq] at hb
      subst hv hb
      exact hm
    | gfVote _ =>
      simp [Vocab.goldilocks, GoldilocksCorrectness.Statements.Executions.blockOf] at hb
    | attest _ =>
      simp [Vocab.goldilocks, GoldilocksCorrectness.Statements.Executions.blockOf] at hb
  · intro h
    exact ⟨_, h, rfl, rfl⟩

/-- A root collision at a proposal, on the view of `x`, is `RootCollisionAtProposal`, by `Iff.rfl`.

The variables:
- `M`: the model;
- `x`: the execution; `s`: the slot; `b`: the proposal.

Read aloud: on the view, a block the proposer held has the proposal's root exactly when it has in
the execution. -/
theorem rootCollisionAtProposalV_iff (s : ℕ) (b : Block V) :
    RootCollisionAtProposalV M Vocab.goldilocks S ((x.map (nodeView M))) s b ↔
      RootCollisionAtProposal M S A x s b := Iff.rfl

/-- A root collision at an honest round opening slot, on the view of `x`, is
`RootCollisionAtOpening`, by `Iff.rfl`.

The variables:
- `M`: the model;
- `x`: the execution; `r`: the rounds of the honest round opening slots; `m`: the index of the
  last one.

Read aloud: on the view, a collision hits an honest round opening slot's proposal exactly when it
does in the execution. -/
theorem rootCollisionAtOpeningV_iff (r : ℕ → ℕ) (m : ℕ) :
    RootCollisionAtOpeningV M Vocab.goldilocks S ((x.map (nodeView M))) r m ↔
      RootCollisionAtOpening M S A x r m := Iff.rfl

/-- Lemma 90's inclusion, read up to `t`, on the view of `x`, is `ConfirmedIncludedBetween`, by
`Iff.rfl`.

The variables:
- `M`: the model;
- `x`: the execution; `tE`, `t`: the two ends.

Read aloud: on the view, honest proposals join the confirmed tips from `tE` and up to `t` exactly
when they do in the execution. -/
theorem confirmedIncludedBetweenV_iff (tE t : ℕ) :
    ConfirmedIncludedBetweenV M Vocab.goldilocks S A ((x.map (nodeView M))) tE t ↔
      ConfirmedIncludedBetween M S A x tE t := Iff.rfl

/-- Lemma 90's inclusion with no upper end, on the view of `x`, is `ConfirmedIncludedAfterHealing`,
by `Iff.rfl`.

The variables:
- `M`: the model;
- `x`: the execution; `tE`: the time from which the slots are read.

Read aloud: on the view, honest proposals join the confirmed tips from `tE` exactly when they do in
the execution. -/
theorem confirmedIncludedAfterHealingV_iff (tE : ℕ) :
    ConfirmedIncludedAfterHealingV M Vocab.goldilocks S A ((x.map (nodeView M))) tE ↔
      ConfirmedIncludedAfterHealing M S A x tE := Iff.rfl

/-- The asynchrony statement's first conclusion, read up to `t`, on the view of `x`, is
`ConfirmedPersistsBetween`, by `Iff.rfl`.

The variables:
- `M`: the model;
- `x`: the execution; `s`: the hand-over slot; `tAwakeEnd`: the time from which the confirmed tips
  are protected; `b₀`: the start of the period; `t`: the time up to which the later steps are read.

Read aloud: on the view, the confirmed tips persist exactly when they do in the execution. -/
theorem confirmedPersistsBetweenV_iff (s tAwakeEnd b₀ t : ℕ) :
    ConfirmedPersistsBetweenV M Vocab.goldilocks S A ((x.map (nodeView M))) s
        tAwakeEnd b₀ t ↔
      ConfirmedPersistsBetween M S A x s tAwakeEnd b₀ t := Iff.rfl

/-- The asynchrony statement's second conclusion, read up to `t`, on the view of `x`, is
`FinalizedCompatibleBetween`, by `Iff.rfl`.

The variables:
- `M`: the model;
- `x`: the execution; `s`: the hand-over slot; `tAwakeEnd`: the time from which the confirmed tips
  are protected; `b₀`: the start of the period; `t`: the time up to which the later steps are read.

Read aloud: on the view, no honest finalized block conflicts with the protected confirmed blocks
exactly when none does in the execution. -/
theorem finalizedCompatibleBetweenV_iff (s tAwakeEnd b₀ t : ℕ) :
    FinalizedCompatibleBetweenV M Vocab.goldilocks S A ((x.map (nodeView M))) s
        tAwakeEnd b₀ t ↔
      FinalizedCompatibleBetween M S A x s tAwakeEnd b₀ t := Iff.rfl

/-- The asynchrony statement's first conclusion with no upper end, on the view of `x`, is
`ConfirmedPersistsFrom`, by `Iff.rfl`.

The variables:
- `M`: the model;
- `x`: the execution; `s`: the hand-over slot; `tAwakeEnd`: the time from which the confirmed tips
  are protected; `b₀`: the start of the period.

Read aloud: on the view, the confirmed tips persist from `b₀` on exactly when they do in the
execution. -/
theorem confirmedPersistsFromV_iff (s tAwakeEnd b₀ : ℕ) :
    ConfirmedPersistsFromV M Vocab.goldilocks S A ((x.map (nodeView M))) s
        tAwakeEnd b₀ ↔
      ConfirmedPersistsFrom M S A x s tAwakeEnd b₀ := Iff.rfl

/-- The asynchrony statement's second conclusion with no upper end, on the view of `x`, is
`FinalizedCompatibleFrom`, by `Iff.rfl`.

The variables:
- `M`: the model;
- `x`: the execution; `s`: the hand-over slot; `tAwakeEnd`: the time from which the confirmed tips
  are protected; `b₀`: the start of the period.

Read aloud: on the view, no honest finalized block from `b₀` on conflicts with the protected
confirmed blocks exactly when none does in the execution. -/
theorem finalizedCompatibleFromV_iff (s tAwakeEnd b₀ : ℕ) :
    FinalizedCompatibleFromV M Vocab.goldilocks S A ((x.map (nodeView M))) s
        tAwakeEnd b₀ ↔
      FinalizedCompatibleFrom M S A x s tAwakeEnd b₀ := Iff.rfl

/-- Lemma 98's conclusion, for the readers whose step is at or before some support cutoff at most
`t`, on the view of `x`, is `FinalityIncludedBetween`, by `Iff.rfl`.

The variables:
- `M`: the model;
- `x`: the execution; `Δs`: the sync delay; `tE`: the time from which the slots are read; `t`: the
  time that decides the readers.

Read aloud: on the view, honest proposals are finalized as new blocks, for the readers whose step
is at or before some support cutoff at most `t`, exactly when they are in the execution. -/
theorem finalityIncludedBetweenV_iff (Δs tE t : ℕ) :
    FinalityIncludedBetweenV M Vocab.goldilocks S A ((x.map (nodeView M))) Δs tE t ↔
      FinalityIncludedBetween M S A x Δs tE t := Iff.rfl

/-- Lemma 98's conclusion with no upper end, on the view of `x`, is `FinalityIncludedAfterHealing`,
by `Iff.rfl`.

The variables:
- `M`: the model;
- `x`: the execution; `Δs`: the sync delay; `tE`: the time from which the slots are read.

Read aloud: on the view, honest proposals are finalized as new blocks from `tE` exactly when they
are in the execution. -/
theorem finalityIncludedAfterHealingV_iff (Δs tE : ℕ) :
    FinalityIncludedAfterHealingV M Vocab.goldilocks S A ((x.map (nodeView M))) Δs tE ↔
      FinalityIncludedAfterHealing M S A x Δs tE := Iff.rfl

/-! ## The conclusions read on the execution's node states

Each `…_unfold` states a conclusion definition with its body written on the execution's node states:
the confirmed tip as `confirmedOf`, the finalized block and the tree as the FG state's, a proposal
as a tick of the execution and a send in its sent log, and the compatibility as the `Bool`
`Block.compatible`. a proof that reads a
conclusion on the execution rewrites with them. -/

/-- `ConfirmedAgreeBetween M S Sched x tE t` read on the execution: the confirmed tips
(`confirmedOf`) of `v₁` in the state step `i` leaves and of `v₂` in the state step `j` leaves are
compatible
(`Block.compatible`), for steps at times from `tE` to `t` through which each has been honest.

Why: field by field the view form, the compatibility through `goldilocks_compatible_iff`.

The variables:
- `M`: the model;
- `x`: the execution; `tE`, `t`: the two ends.

Read aloud: the agreement from `tE` up to `t` is the compatibility of the node states' confirmed
tips. -/
theorem confirmedAgreeBetween_unfold (tE : ℝ) (t : ℕ) :
    ConfirmedAgreeBetween M S A x tE t ↔
      ∀ (v₁ v₂ : V) (i j : ℕ), A.HonestThroughTime x (x.time i) v₁ → A.HonestThroughTime x (x.time j) v₂ →
        tE ≤ x.time i → tE ≤ x.time j → x.time i ≤ t → x.time j ≤ t →
        (M.ac_confirmed (x.st (i + 1) v₁)).compatible (M.ac_confirmed (x.st (j + 1) v₂)) = true :=
  forall₄_congr fun _ _ _ _ => imp_congr_right fun _ => imp_congr_right fun _ =>
    imp_congr_right fun _ => imp_congr_right fun _ => imp_congr_right fun _ =>
      imp_congr_right fun _ => goldilocks_compatible_iff _ _

/-- `ConfirmedAgreeAfterHealing M S Sched x tE` read on the execution: the confirmed tips of two
validators, after steps at times at least `tE` through which each has been honest, are compatible
(`Block.compatible`).

Why: field by field the view form, the compatibility through `goldilocks_compatible_iff`.

The variables:
- `M`: the model;
- `x`: the execution; `tE`: the time from which the agreement holds.

Read aloud: the agreement from `tE` on is the compatibility of the node states' confirmed tips. -/
theorem confirmedAgreeAfterHealing_unfold (tE : ℕ) :
    ConfirmedAgreeAfterHealing M S A x tE ↔
      ∀ (v₁ v₂ : V) (i j : ℕ), A.HonestThroughTime x (x.time i) v₁ → A.HonestThroughTime x (x.time j) v₂ →
        tE ≤ x.time i → tE ≤ x.time j →
        (M.ac_confirmed (x.st (i + 1) v₁)).compatible (M.ac_confirmed (x.st (j + 1) v₂)) = true :=
  forall₄_congr fun _ _ _ _ => imp_congr_right fun _ => imp_congr_right fun _ =>
    imp_congr_right fun _ => imp_congr_right fun _ => goldilocks_compatible_iff _ _

/-- `ConfirmedMonotoneBetween M S Sched x tE t` read on the execution, by `Iff.rfl`: `v`'s confirmed
tip (`confirmedOf`) in the state step `i` leaves is an ancestor of, or equal to, the one in the
state step `j ≥ i` leaves.

The variables:
- `M`: the model;
- `x`: the execution; `tE`, `t`: the two ends.

Read aloud: the growth from `tE` up to `t` is the growth of the node states' confirmed tips. -/
theorem confirmedMonotoneBetween_unfold (tE : ℝ) (t : ℕ) :
    ConfirmedMonotoneBetween M S A x tE t ↔
      ∀ (v : V) (i j : ℕ), i ≤ j → A.HonestThroughTime x (x.time j) v → tE ≤ x.time i → x.time j ≤ t →
        (M.ac_confirmed (x.st (i + 1) v)).AncestorEq (M.ac_confirmed (x.st (j + 1) v)) := Iff.rfl

/-- `ConfirmedMonotoneAfterHealing M S Sched x tE` read on the execution, by `Iff.rfl`.

The variables:
- `M`: the model;
- `x`: the execution; `tE`: the time from which the growth holds.

Read aloud: the growth from `tE` on is the growth of the node states' confirmed tips. -/
theorem confirmedMonotoneAfterHealing_unfold (tE : ℕ) :
    ConfirmedMonotoneAfterHealing M S A x tE ↔
      ∀ (v : V) (i j : ℕ), i ≤ j → A.HonestThroughTime x (x.time j) v → tE ≤ x.time i →
        (M.ac_confirmed (x.st (i + 1) v)).AncestorEq (M.ac_confirmed (x.st (j + 1) v)) := Iff.rfl

/-- `RootCollisionHeldBy M S Sched x t` read on the execution, by `Iff.rfl`: two distinct blocks in
the FG state's trees of validators honest at steps at times at most `t` have the same root.

The variables:
- `M`: the model;
- `x`: the execution; `t`: the bound on the time.

Read aloud: by `t`, two distinct blocks honest validators hold share a root. -/
theorem rootCollisionHeldBy_unfold (t : ℕ) :
    RootCollisionHeldBy M S A x t ↔
      ∃ B B' : Block V, inHonestTreeBy M A x t B ∧ inHonestTreeBy M A x t B' ∧ B.root = B'.root ∧
        B ≠ B' := Iff.rfl

/-- `RootCollisionAtProposal M S Sched x s B` read on the execution: some block in the FG state's
tree of the proposer of slot `s`, on the node state its tick to the start of slot `s` starts from
(`tickInput`), has `B`'s root.

Why: the view of the mapped trace at a step is the node state's view there, and the mapped trace has the
execution's labels, so its tick input is the view of the execution's tick input.

The variables:
- `M`: the model;
- `x`: the execution; `s`: the slot; `B`: the proposal.

Read aloud: a block the proposer held when its tick to the proposal's slot started has the proposal's
root. -/
theorem rootCollisionAtProposal_unfold (s : ℕ) (B : Block V) :
    RootCollisionAtProposal M S A x s B ↔
      ∃ B' ∈ (x.tickInput (S.P.proposer s) (M.slotStart S.C s)).tree, B'.root = B.root := by
  exact Iff.rfl

/-- `RootCollisionAtOpening M S Sched x r m` read on the execution: for some `i ≤ m`, some proposal
`B` of slot `r i * R` (`ProposalAt`, a tick of the execution and a send in its sent log) has a root
collision at its proposal (`RootCollisionAtProposal`).

Why: a proposal on the view is `ProposalAt` (`proposalAtV_iff`).

The variables:
- `M`: the model;
- `x`: the execution; `r`: the rounds of the honest round opening slots; `m`: the index of the
  last one.

Read aloud: some honest round opening slot's proposal has the root of a block its proposer already
held. -/
theorem rootCollisionAtOpening_unfold (r : ℕ → ℕ) (m : ℕ) :
    RootCollisionAtOpening M S A x r m ↔
      ∃ i : ℕ, i ≤ m ∧ ∃ B : Block V, ProposalAt M S x (r i * S.C.R) B ∧
        RootCollisionAtProposal M S A x (r i * S.C.R) B :=
  exists_congr fun i => and_congr_right fun _ => exists_congr fun b =>
    and_congr ((proposalAtV_iff M) x (r i * S.C.R) b) Iff.rfl

/-- `ConfirmedIncludedBetween M S Sched x tE t` read on the execution: the proposer's condition
written out, the proposal as a tick of the execution and a send in its sent log, the confirmed tips
as `confirmedOf` of the node states.

Why: a proposal on the view is a tick and a send of the execution (`proposalAtV_iff`), and the
view a validator's tick to the support cutoff leaves is its node state then (`x.map` maps each
node state, and keeps the steps).

The variables:
- `M`: the model;
- `x`: the execution; `tE`, `t`: the two ends.

Read aloud: the inclusion from `tE` and up to `t`, read on the node states. -/
theorem confirmedIncludedBetween_unfold (tE t : ℕ) :
    ConfirmedIncludedBetween M S A x tE t ↔
      ∀ s : ℕ, tE ≤ M.slotStart S.C s → M.supportCutoff S.C (s + 1) ≤ t →
        HonestOpenerAt M S A x s →
        (∃ (i : ℕ) (B : Block V), x.lbl i = Event.tick (S.P.proposer s) (M.slotStart S.C s) ∧
          (⟨S.P.proposer s, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
            x.sent (i + 1) - x.sent i) ∧
        ∀ (i : ℕ) (B : Block V), x.lbl i = Event.tick (S.P.proposer s) (M.slotStart S.C s) →
          (⟨S.P.proposer s, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
            x.sent (i + 1) - x.sent i →
          RootCollisionAtProposal M S A x s B ∨
          ((∀ v ∈ honestActiveAt M S A x s,
            (x.time (x.tickStep v (M.supportCutoff S.C (s + 1))) : ℝ) ≤ t →
            M.ac_confirmed (x.tickOutput v (M.supportCutoff S.C (s + 1))) = B) ∧
          (∀ (v : V) (j s' : ℕ), A.HonestThroughTime x (x.time j) v → s ≤ s' → v ∈ honestActiveAt M S A x s' →
            x.tickStep v (M.supportCutoff S.C (s' + 1)) ≤ j → M.supportCutoff S.C (s' + 1) ≤ t → x.time j ≤ t →
            B.AncestorEq (M.ac_confirmed (x.st (j + 1) v)))) := by
  refine forall_congr' fun s => imp_congr_right fun _ => imp_congr_right fun _ =>
    imp_congr_right fun _ => ?_
  refine and_congr ?_ ?_
  · constructor
    · rintro ⟨b, hb⟩
      obtain ⟨i, hl, hsent⟩ := ((proposalAtV_iff M) x s b).1 hb
      exact ⟨i, b, hl, hsent⟩
    · rintro ⟨i, b, hl, hsent⟩
      exact ⟨b, ((proposalAtV_iff M) x s b).2 ⟨i, hl, hsent⟩⟩
  · constructor
    · intro h i b hl hsent
      exact h b (((proposalAtV_iff M) x s b).2 ⟨i, hl, hsent⟩)
    · intro h b hb
      obtain ⟨i, hl, hsent⟩ := ((proposalAtV_iff M) x s b).1 hb
      exact h i b hl hsent

/-- `ConfirmedIncludedAfterHealing M S Sched x tE` read on the execution, as
`confirmedIncludedBetween_unfold` with no upper end.

Why: as `confirmedIncludedBetween_unfold`.

The variables:
- `M`: the model;
- `x`: the execution; `tE`: the time from which the slots are read.

Read aloud: the inclusion from `tE`, read on the node states. -/
theorem confirmedIncludedAfterHealing_unfold (tE : ℕ) :
    ConfirmedIncludedAfterHealing M S A x tE ↔
      ∀ s : ℕ, tE ≤ M.slotStart S.C s →
        HonestOpenerAt M S A x s →
        (∃ (i : ℕ) (B : Block V), x.lbl i = Event.tick (S.P.proposer s) (M.slotStart S.C s) ∧
          (⟨S.P.proposer s, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
            x.sent (i + 1) - x.sent i) ∧
        ∀ (i : ℕ) (B : Block V), x.lbl i = Event.tick (S.P.proposer s) (M.slotStart S.C s) →
          (⟨S.P.proposer s, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
            x.sent (i + 1) - x.sent i →
          RootCollisionAtProposal M S A x s B ∨
          ((∀ v ∈ honestActiveAt M S A x s,
            M.ac_confirmed (x.tickOutput v (M.supportCutoff S.C (s + 1))) = B) ∧
          (∀ (v : V) (j s' : ℕ), A.HonestThroughTime x (x.time j) v → s ≤ s' → v ∈ honestActiveAt M S A x s' →
            x.tickStep v (M.supportCutoff S.C (s' + 1)) ≤ j →
            B.AncestorEq (M.ac_confirmed (x.st (j + 1) v)))) := by
  refine forall_congr' fun s => imp_congr_right fun _ => imp_congr_right fun _ => ?_
  refine and_congr ?_ ?_
  · constructor
    · rintro ⟨b, hb⟩
      obtain ⟨i, hl, hsent⟩ := ((proposalAtV_iff M) x s b).1 hb
      exact ⟨i, b, hl, hsent⟩
    · rintro ⟨i, b, hl, hsent⟩
      exact ⟨b, ((proposalAtV_iff M) x s b).2 ⟨i, hl, hsent⟩⟩
  · constructor
    · intro h i b hl hsent
      exact h b (((proposalAtV_iff M) x s b).2 ⟨i, hl, hsent⟩)
    · intro h b hb
      obtain ⟨i, hl, hsent⟩ := ((proposalAtV_iff M) x s b).1 hb
      exact h i b hl hsent

/-- `ConfirmedPersistsBetween M S Sched x s tAwakeEnd b₀ t` read on the execution, by `Iff.rfl`.

The variables:
- `M`: the model;
- `x`: the execution; `s`: the hand-over slot; `tAwakeEnd`: the time from which the confirmed tips
  are protected; `b₀`: the start of the period; `t`: the time up to which the later steps are read.

Read aloud: the persistence up to `t`, read on the node states' confirmed tips. -/
theorem confirmedPersistsBetween_unfold (s tAwakeEnd b₀ t : ℕ) :
    ConfirmedPersistsBetween M S A x s tAwakeEnd b₀ t ↔
      ∀ (v : V) (T : ℕ) (P : Block V),
        A.HonestThroughTime x (x.time T) v → tAwakeEnd ≤ x.time T → x.time T ≤ M.supportCutoff S.C (s + 1) →
        (∀ (t : ℕ), (t : ℝ) ≤ x.time T → ∀ T' : ℕ, T ≤ T' → x.lbl T' ≠ Event.tick v t) →
        P.AncestorEq (M.ac_confirmed (x.st T v)) →
        ∀ (w : V) (j : ℕ), x.HonestThrough A j w → w ∈ updaterAt M S A x s →
          x.tickStep w (M.supportCutoff S.C (s + 1)) < j →
          b₀ ≤ x.time j → x.time j ≤ t →
          P.AncestorEq (M.ac_confirmed (x.st j w)) := Iff.rfl

/-- `FinalizedCompatibleBetween M S Sched x s tAwakeEnd b₀ t` read on the execution, by `Iff.rfl`.

The variables:
- `M`: the model;
- `x`: the execution; `s`: the hand-over slot; `tAwakeEnd`: the time from which the confirmed tips
  are protected; `b₀`: the start of the period; `t`: the time up to which the later steps are read.

Read aloud: the finalized blocks' compatibility up to `t`, read on the node states. -/
theorem finalizedCompatibleBetween_unfold (s tAwakeEnd b₀ t : ℕ) :
    FinalizedCompatibleBetween M S A x s tAwakeEnd b₀ t ↔
      ∀ (v : V) (T : ℕ) (P : Block V),
        A.HonestThroughTime x (x.time T) v → tAwakeEnd ≤ x.time T → x.time T ≤ M.supportCutoff S.C (s + 1) →
        (∀ (t : ℕ), (t : ℝ) ≤ x.time T → ∀ T' : ℕ, T ≤ T' → x.lbl T' ≠ Event.tick v t) →
        P.AncestorEq (M.ac_confirmed (x.st T v)) →
        ∀ (w : V) (j : ℕ), x.HonestThrough A j w → b₀ ≤ x.time j → x.time j ≤ t →
          (P.AncestorEq (x.st j w).finalized ∨ (x.st j w).finalized.AncestorEq P) := Iff.rfl

/-- `ConfirmedPersistsFrom M S Sched x s tAwakeEnd b₀` read on the execution, by `Iff.rfl`.

The variables:
- `M`: the model;
- `x`: the execution; `s`: the hand-over slot; `tAwakeEnd`: the time from which the confirmed tips
  are protected; `b₀`: the start of the period.

Read aloud: the persistence from `b₀` on, read on the node states' confirmed tips. -/
theorem confirmedPersistsFrom_unfold (s tAwakeEnd b₀ : ℕ) :
    ConfirmedPersistsFrom M S A x s tAwakeEnd b₀ ↔
      ∀ (v : V) (T : ℕ) (P : Block V),
        A.HonestThroughTime x (x.time T) v → tAwakeEnd ≤ x.time T → x.time T ≤ M.supportCutoff S.C (s + 1) →
        (∀ (t : ℕ), (t : ℝ) ≤ x.time T → ∀ T' : ℕ, T ≤ T' → x.lbl T' ≠ Event.tick v t) →
        P.AncestorEq (M.ac_confirmed (x.st T v)) →
        ∀ (w : V) (j : ℕ), x.HonestThrough A j w → w ∈ updaterAt M S A x s →
          x.tickStep w (M.supportCutoff S.C (s + 1)) < j → b₀ ≤ x.time j →
          P.AncestorEq (M.ac_confirmed (x.st j w)) := Iff.rfl

/-- `FinalizedCompatibleFrom M S Sched x s tAwakeEnd b₀` read on the execution, by `Iff.rfl`.

The variables:
- `M`: the model;
- `x`: the execution; `s`: the hand-over slot; `tAwakeEnd`: the time from which the confirmed tips
  are protected; `b₀`: the start of the period.

Read aloud: the finalized blocks' compatibility from `b₀` on, read on the node states. -/
theorem finalizedCompatibleFrom_unfold (s tAwakeEnd b₀ : ℕ) :
    FinalizedCompatibleFrom M S A x s tAwakeEnd b₀ ↔
      ∀ (v : V) (T : ℕ) (P : Block V),
        A.HonestThroughTime x (x.time T) v → tAwakeEnd ≤ x.time T → x.time T ≤ M.supportCutoff S.C (s + 1) →
        (∀ (t : ℕ), (t : ℝ) ≤ x.time T → ∀ T' : ℕ, T ≤ T' → x.lbl T' ≠ Event.tick v t) →
        P.AncestorEq (M.ac_confirmed (x.st T v)) →
        ∀ (w : V) (j : ℕ), x.HonestThrough A j w → b₀ ≤ x.time j →
          (P.AncestorEq (x.st j w).finalized ∨ (x.st j w).finalized.AncestorEq P) := Iff.rfl

/-- `FinalityIncludedBetween M S Sched x Δs tE t` read on the execution: the proposal as a tick of the
execution and a send in its sent log, the finalized blocks as the FG states'.

Why: a proposal on the view is a tick and a send of the execution (`proposalAtV_iff`); the rest is
the view form's.

The variables:
- `M`: the model;
- `x`: the execution; `Δs`: the sync delay; `tE`: the time from which the slots are read; `t`:
  the time that decides the readers: a reader's step is at or before some support cutoff at most
  `t`, as in `FinalityIncludedBetween`.

Read aloud: Lemma 98's conclusion from `tE`, for the readers whose step is at or before some
support cutoff at most `t`, read on the node states. -/
theorem finalityIncludedBetween_unfold (Δs tE t : ℕ) :
    FinalityIncludedBetween M S A x Δs tE t ↔
      ∀ (s r : ℕ), tE ≤ M.slotStart S.C s → HonestOpenerAt M S A x s → s ≤ r * S.C.R →
        FinalityWindowAt M S A x r → M.supportCutoff S.C ((r + 3) * S.C.R + 1) ≤ t →
        (∃ (i : ℕ) (B : Block V), x.lbl i = Event.tick (S.P.proposer s) (M.slotStart S.C s) ∧
          (⟨S.P.proposer s, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
            x.sent (i + 1) - x.sent i) ∧
        ∀ (i : ℕ) (B : Block V), x.lbl i = Event.tick (S.P.proposer s) (M.slotStart S.C s) →
          (⟨S.P.proposer s, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
            x.sent (i + 1) - x.sent i →
          RootCollisionAtProposal M S A x s B ∨
          RootCollisionAtOpening M S A x (fun i => r + i) 3 ∨
          ∀ (v : V) (j : ℕ), A.HonestThroughTime x (x.time j) v →
            (∃ s' : ℕ, x.time j ≤ M.supportCutoff S.C s' ∧ M.supportCutoff S.C s' ≤ t) →
            AwakeForDelayWithin S A x Δs v (M.slotStart S.C ((r + 3) * S.C.R)) j →
            B.AncestorEq (x.st j v).finalized ∧
            ∀ (u : V) (i' : ℕ), x.time i' < M.slotStart S.C s →
              (x.st i' u).finalized ≠ (x.st j v).finalized := by
  refine forall₂_congr fun s r => imp_congr_right fun _ => imp_congr_right fun _ =>
    imp_congr_right fun _ => imp_congr_right fun _ => imp_congr_right fun _ => ?_
  refine and_congr ?_ ?_
  · constructor
    · rintro ⟨b, hb⟩
      obtain ⟨i, hl, hsent⟩ := ((proposalAtV_iff M) x s b).1 hb
      exact ⟨i, b, hl, hsent⟩
    · rintro ⟨i, b, hl, hsent⟩
      exact ⟨b, ((proposalAtV_iff M) x s b).2 ⟨i, hl, hsent⟩⟩
  · constructor
    · intro h i b hl hsent
      exact h b (((proposalAtV_iff M) x s b).2 ⟨i, hl, hsent⟩)
    · intro h b hb
      obtain ⟨i, hl, hsent⟩ := ((proposalAtV_iff M) x s b).1 hb
      exact h i b hl hsent

/-- `FinalityIncludedAfterHealing M S Sched x Δs tE` read on the execution, as
`finalityIncludedBetween_unfold` with no upper end.

Why: as `finalityIncludedBetween_unfold`.

The variables:
- `M`: the model;
- `x`: the execution; `Δs`: the sync delay; `tE`: the time from which the slots are read.

Read aloud: Lemma 98's conclusion from `tE`, read on the node states. -/
theorem finalityIncludedAfterHealing_unfold (Δs tE : ℕ) :
    FinalityIncludedAfterHealing M S A x Δs tE ↔
      ∀ (s r : ℕ), tE ≤ M.slotStart S.C s → HonestOpenerAt M S A x s → s ≤ r * S.C.R →
        FinalityWindowAt M S A x r →
        (∃ (i : ℕ) (B : Block V), x.lbl i = Event.tick (S.P.proposer s) (M.slotStart S.C s) ∧
          (⟨S.P.proposer s, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
            x.sent (i + 1) - x.sent i) ∧
        ∀ (i : ℕ) (B : Block V), x.lbl i = Event.tick (S.P.proposer s) (M.slotStart S.C s) →
          (⟨S.P.proposer s, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
            x.sent (i + 1) - x.sent i →
          RootCollisionAtProposal M S A x s B ∨
          RootCollisionAtOpening M S A x (fun i => r + i) 3 ∨
          ∀ (v : V) (j : ℕ), A.HonestThroughTime x (x.time j) v →
            AwakeForDelayWithin S A x Δs v (M.slotStart S.C ((r + 3) * S.C.R)) j →
            B.AncestorEq (x.st j v).finalized ∧
            ∀ (u : V) (i' : ℕ), x.time i' < M.slotStart S.C s →
              (x.st i' u).finalized ≠ (x.st j v).finalized := by
  refine forall₂_congr fun s r => imp_congr_right fun _ => imp_congr_right fun _ =>
    imp_congr_right fun _ => imp_congr_right fun _ => ?_
  refine and_congr ?_ ?_
  · constructor
    · rintro ⟨b, hb⟩
      obtain ⟨i, hl, hsent⟩ := ((proposalAtV_iff M) x s b).1 hb
      exact ⟨i, b, hl, hsent⟩
    · rintro ⟨i, b, hl, hsent⟩
      exact ⟨b, ((proposalAtV_iff M) x s b).2 ⟨i, hl, hsent⟩⟩
  · constructor
    · intro h i b hl hsent
      exact h b (((proposalAtV_iff M) x s b).2 ⟨i, hl, hsent⟩)
    · intro h b hb
      obtain ⟨i, hl, hsent⟩ := ((proposalAtV_iff M) x s b).1 hb
      exact h i b hl hsent

end Execution

end GoldilocksCorrectness.Record.Proofs.View

