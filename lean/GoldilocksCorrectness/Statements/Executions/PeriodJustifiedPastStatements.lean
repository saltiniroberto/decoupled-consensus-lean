module
public import GoldilocksCorrectness.Proofs.Executions.PeriodJustifiedPast
public import GoldilocksCorrectness.Statements.Routines.FGStateStatements
public import GoldilocksCorrectness.Statements.Routines.ForkChoiceStatements

@[expose] public section

/-! kit statements, new, no landed statement changes. Proved in
`GoldilocksCorrectness/Proofs/Executions/PeriodJustifiedPast.lean`, which also carries the
helpers `viable_head_descends_of_justified_past`, `viable_tree_compatible`, `fc_root_compatible`,
`get_anchor_cases_viable`, `anchor_compatible` and `fork_choice_compatible`. Write `h(X)` for
`(chainStateOf C X).h`, the chain-state height of a block `X`.
-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (voteTime)

open GoldilocksCorrectness.Statements.Routines (IsEntry chainStateOf)

open GoldilocksCorrectness.Statements.Routines (ChainStatesComputed)

open GoldilocksCorrectness.Statements.Routines (CachesCompatibleWith)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Routines (ProgressCertOn)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- **A block on `B`'s side higher than `B` descends from `B`.** A block compatible with `B` whose
chain-state height is greater than `B`'s is `B` or a descendant of `B`.

Why: an ancestor of `B` has a chain-state height at most `B`'s.

The variables:
- `C`: the parameters; `B`: the block; `E`: the block compatible with `B`.

Read aloud: a block on `B`'s side that is higher than `B` is `B` or a descendant of `B`. -/
theorem descends_of_compatible_higher (C : Config) {B E : Block V}
    -- `E` is compatible with `B`
    (hc : E.AncestorEq B ∨ B.AncestorEq E)
    -- `E` is higher than `B`
    (hh : (chainStateOf C B).h < (chainStateOf C E).h) : B.AncestorEq E :=
  GoldilocksCorrectness.Proofs.Routines.descends_of_compatible_higher C hc hh

/-- **A justification past `B` spreads in one delay.** Under the hypotheses `P` of the period
after the hand-over slot `s` (with `GST` at or before the vote time of slot `s + 1`), with roots
naming blocks among what honest validators hold up to the vote time of slot `σ + 1`: take a slot
`σ ≥ s + 1` such that the votes of `σ` were not owed inside the period, a validator
`w ∈ honestActiveAt S Sched σ` whose caches before the vote time of `σ` are compatible with `B`
with justification height at least `h(B) + 1`, and a validator `u ∈ honestActiveAt S Sched (σ + 1)`
whose finalized block before the vote time of `σ + 1` is `B` or an ancestor of `B`. Then `u`'s
justification height before the vote time of `σ + 1` is at least `h(B) + 1`.

Why: `w` holds a block `D` whose chain state carries `w`'s justification (the witness of its
caches), and `B ⪯ D`; `D` reaches `u` one delay after `voteTime S σ` (the previous votes due
before the period) or after `supportCutoff S σ` (due after it), before `voteTime S (σ + 1)`; `u`'s
finalized block is an ancestor of `D`, and Lemma 57's cache bound makes `u`'s justification height
at least `D`'s.

 every
hypothesis is read.

The variables:
- `P`: the hypotheses of the period; `σ`: the slot of `w`'s vote; `w`: the voter justified past
  `B`; `u`: the voter of slot `σ + 1`.

Read aloud: when an honest active voter of slot `σ` has justified a block higher than `B`, every
honest active voter of the timely slot `σ + 1` whose finalized block is `B` or an ancestor of `B`
has too, before its vote. -/
theorem justified_past_spreads [RootOrder] {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (protocol S) Sched} {GST s : ℕ} {B : Block V} {H t₀ anchor tAwakeEnd b₀ b₁ : ℕ}
    -- the hypotheses of the period, with `GST` at or before the vote time of slot `s + 1`
    (P : AsyncHypsOfChainBlockGSTBeforeVotes S Sched x GST s B H t₀ anchor tAwakeEnd b₀ b₁)
    (σ : ℕ) (w u : V)
    -- roots name blocks among what honest validators hold up to the vote time of `σ + 1`
    (hRoots : RootsNameBlocksUntil S Sched x (voteTime S (σ + 1)))
    -- the slot is after the hand-over slot
    (hσ : s + 1 ≤ σ)
    -- the votes of slot `σ` were not owed inside the period
    (hgood : ¬ VotesOwedInPeriod S b₀ b₁ (σ + 1))
    -- `w` is awake through the duties of `σ` and honest at its update
    (hw : w ∈ honestActiveAt S Sched σ)
    -- `w`'s caches before the vote time of `σ` are compatible with `B`
    (hCw : CachesCompatibleWith S B H (stateBefore x (voteTime S σ) w))
    -- `w` is justified past `B` before the vote time of `σ`
    (hjw : (chainStateOf S.C B).h + 1 ≤ (stateBefore x (voteTime S σ) w).S.h_j)
    -- `u` is awake through the duties of `σ + 1` and honest at its update
    (hu : u ∈ honestActiveAt S Sched (σ + 1))
    -- `u`'s finalized block before the vote time of `σ + 1` is `B` or an ancestor of `B`
    (hFu : (stateBefore x (voteTime S (σ + 1)) u).S.F.AncestorEq B) :
    (chainStateOf S.C B).h + 1 ≤ (stateBefore x (voteTime S (σ + 1)) u).S.h_j :=
  GoldilocksCorrectness.Proofs.Executions.justified_past_spreads P σ w u hRoots hσ hgood hw hCw
    hjw hu hFu

end GoldilocksCorrectness.Statements.Executions
