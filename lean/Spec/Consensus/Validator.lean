import Spec.Consensus.Fig6TimedStore

/-!
# The honest validator

The draft's Section 6, which the pdf marks `[To be drafted.]` — so unlike the figure
files, nothing here renders existing text. The semantics are fixed by Roberto's dictation,
rule by rule (decided 2026-08-20), and the Lean is the primary artifact; the paper's
Section 6 can follow it. No figure, hence no figure number in the filename and no
`-- line n` comments.

What Sections 1–4 already fix, and this file calls rather than redefines: the SG/FG
action happens at `a_r` (Definition 9) and its outputs are anchored at `Σ.action_root[r]`
(Definition 15); the opening proposer's proposal root comes from `get_proposal_root`
(Definition 13); each Goldfish fork choice starts from the walk root (Definition 14).

Pure functions first: what to sign or build at each instant, as functions of the timed
store. The lean-sts execution wiring — sends, receipts, the network — is a later, separate
step.
-/

set_option autoImplicit false

namespace Consensus

variable {Validator Ω : Type}

section Actions
variable [DecidableEq Validator] [Electorate Validator] [Params]

/-- The veto on confirmation candidates (skeleton, standing in for a rule of Roberto's):
    `Q` is vetoed when some accepted block on the finalized chain, conflicting with `Q`,
    might still hold majority support — `G0`, in the role the old paper's strong G0 check
    gave it. Computed outside `goldfishConfirmation`, which sees only the already-filtered
    tree. -/
def vetoed (S : Store Validator Ω) (r : Nat) (Q : Block Validator) : Prop :=
  ∃ B ∈ S.T, S.F ⪯ B ∧ ¬ B ∼ Q ∧ G0 S r B

instance (S : Store Validator Ω) (r : Nat) (Q : Block Validator) : Decidable (vetoed S r Q) :=
  inferInstanceAs (Decidable (∃ B ∈ S.T, _))

/-- The blocks the round's confirmation may choose among: the walk start, together with the
    candidates above it that the veto does not exclude.

    **The walk start is never filtered out** (Roberto, 2026-08-20), even when it is itself
    vetoed. The veto says "do not move onto a vetoed block", not "do not vote": a validator
    always confirms at least the root its own fork choice anchored on. So this set is never
    empty, which is what makes the confirmation total.

    Skeleton to the extent `vetoed` is. -/
def confirmationCandidates (S : Store Validator Ω) (r : Nat) (walkStart : Block Validator) :
    Finset (Block Validator) :=
  {walkStart} ∪ (S.candidateTreeFrom walkStart).filter fun B => ¬ vetoed S r B

/-- `s` is a *subtree rooted at* `R`: `R` is in it, everything in it descends from `R`, and
    it has no gaps — every block lying between `R` and a member is itself a member. A walk
    from `R` can move within such a set one block at a time, never has to jump, and always
    has somewhere to be.

    `{R}` qualifies: it is what a walk from `R` sees when nothing above `R` is available.
    The empty set does not.

    **Nothing in `Spec/` consumes this**, deliberately: the walk is `Store`'s
    `goldfishConfirmation` field, whose type promises nothing about its argument, so
    tree-ness is a hypothesis for the theorems about executions that reason on the walk.
    It was briefly a hypothesis on the walk itself; git history has that, and `CONTEXT.md`
    records why it went. -/
def IsSubtreeFrom (R : Block Validator) (s : Finset (Block Validator)) : Prop :=
  R ∈ s ∧ (∀ B ∈ s, R ⪯ B) ∧ ∀ B ∈ s, ∀ C, R ⪯ C → C ⪯ B → C ∈ s

/-- Let the bracket's own tactic close a read by applying the hypotheses in context, so
    `S.σ[B]` needs nothing written after it (Roberto, 2026-08-21). `solve_by_elim` is
    general: it applies hypotheses and implications until the goal closes, so it needs no
    knowledge of this layer — the *assumptions* carry that. It is what lets the action
    assume its bridge as an implication rather than proving it, which is why **nothing in
    this file is a theorem**.

    The extension point in Lean 4.32.2 is `get_elem_tactic_extensible`;
    `get_elem_tactic_trivial` still parses but is deprecated and wired to nothing, so a
    clause added there is silently ignored (measured 2026-08-21). `macro_rules` has no
    scoped form, so this clause is tried at every `xs[i]` from here on, after `done` and
    `assumption` and before core's own alternatives. Two consequences: a bracket that fails
    downstream may report this search's failure rather than its own, and the search is a
    search — it will apply any implication in context that fits. -/
macro_rules
  | `(tactic| get_elem_tactic_extensible) => `(tactic| solve_by_elim)

/-- Validator `i`'s SG and FG action for round `r`, performed at `a_r`: the one combined
    attestation of the round, its SG half the head, its FG half the two pairs.

    Four hypotheses, all autoparams discharged by `assumption`, so a call site holding them
    writes nothing: `S.t = actionTime r`, that this is the round's action time; `hσ`, that
    accepted blocks have recorded states — the map-domain coherence the `Store` type does not
    enforce; `hRoot`, that the round's walk start is accepted; and `hConfirmed`, that the two
    together give the confirmation a recorded state. A statement supplying any of them must
    hold it as a *named* hypothesis, since `assumption` does not see anonymous arrow binders
    during statement elaboration (measured on `lemChainTargetFirstBlock`).

    **`hConfirmed` is assumed as an implication, not proved** (Roberto, 2026-08-21). It is
    provable — the candidates are filters of `Σ.T`, and `hRoot` covers the two walk-start
    cases — and commit `9f036b9` has that proof; assuming it instead is what keeps this file
    free of theorems, and it becomes a lemma of `Analysis/` when there is one, discharged at
    the call rather than assumed. The body still writes its reads plainly, `solve_by_elim`
    applying whichever hypotheses fit.

    Three earlier shapes are in git history: a bundle whose fields were shaped to the reads;
    hypotheses stating the reads' own side conditions, so plain reads needed no tactic at
    all; and general hypotheses with each read naming its proof in the `'…` form.

    `hRoot` stays assumed rather than derived because `get_action_root` returns either a
    block it has just tested for membership in `C(Σ)` or the fork-choice root: reaching it
    needs only that `Σ.J` and `Σ.F` are accepted, which Definition 7 states in prose and the
    type does not enforce, but it means reasoning through that routine's `Id.run do`.

    **The body is a skeleton, not a rule.** The pipeline as dictated so far, 2026-08-20,
    with the remaining inventions marked `skeleton:`. What it does:

    * the walk starts at `get_action_root(Σ, r)`, Definition 15's action root, **derived
      here rather than read from** `Σ.action_root[r]` (Roberto, 2026-08-20). `on_tick`
      writes that entry at this same instant, so on schedule the two agree; deriving it is
      what makes the walk start well-formed against the *current* store —
      `get_action_root` returns either a block of `C(Σ)` or the fork-choice root itself, so
      `Σ`'s fork-choice root always precedes it, and `candidateTreeFrom` of it is therefore
      a tree rather than one block floating above a gap. A stored root could not promise
      that, finality having moved on since the write;
    * derive the round's confirmation `C` with the store's walk from that start, over the
      candidates admitted by the veto "some accepted block on the finalized chain,
      conflicting with the candidate, might still hold majority support" — `G0`, playing
      the role the old paper's strong G0 check gave it. There is always a confirmation: the
      veto never removes the walk start itself, so the candidate set contains it;
    * head is `C`, and the current-height pair is read off `C`'s post-state — the exact
      target vote at a justifiable height, the empty-target (progress-only) vote at a
      nonjustifiable one, the same test Figure 1's justify event applies on receipt. **So
      the validator never abstains from the current-height pair**, where the old paper's
      rule did whenever no veto-free confirmation existed;
    * the finality half is independent of the confirmation, as in the old paper: read off
      the walk start's post-state, commit the latest justification `(h_j, J)` while it is
      unfinalized — heights in the two pairs always differ (`h_j < h`), so one honest
      attestation cannot trip slashing condition E1 against itself.

    Still consciously dropped from the old pipeline, each a decision to re-make: the
    source-proposal branch — the old rule prefers the graded proposal's state over the
    confirmation's — and the signing history, which the old rule filters every pair
    through. -/
def onSGFGVotingAction (i : Validator) (S : Store Validator Ω) (r : Nat)
    (_ : S.t = actionTime r := by assumption)
    (hσ : ∀ B, B ∈ S.T → B ∈ S.σ := by assumption)
    (hRoot : getActionRoot S r ∈ S.T := by assumption)
    (hConfirmed : (∀ B, B ∈ S.T → B ∈ S.σ) → getActionRoot S r ∈ S.T →
        (S.goldfishConfirmation (getActionRoot S r)
          (confirmationCandidates S r (getActionRoot S r))).val ∈ S.σ := by assumption) :
    Attestation Validator := Id.run do
  -- the walk start (Definition 15's action root): derived here from the current store
  -- rather than read from `Σ.action_root[r]`
  let walkStart := getActionRoot S r
  -- the confirmation: run Goldfish from the walk start over the candidates the veto
  -- admits, the walk start among them, so there is always one
  let C : Block Validator :=
    S.goldfishConfirmation walkStart (confirmationCandidates S r walkStart)
  -- skeleton: the finality half, independent of the confirmation, off the walk start's
  -- state. Both reads are plain: `solve_by_elim` closes the first from `hσ` and `hRoot`,
  -- the second by applying `hConfirmed` to them
  let σStart := S.σ[walkStart]
  let finalityPair : FinalityPair Validator :=
    if σStart.h_j > σStart.h_F then .pair σStart.h_j σStart.J else .empty
  -- skeleton: the current-height half, off the confirmation's state, no history
  let σC := S.σ[C]
  let heightPair : HeightPair Validator :=
    if σC.h % Params.K = 0 ∧ σC.h - σC.h_F > Params.D then .emptyTarget σC.h
    else .target σC.h σC.T_h
  return {
    validator := i
    round := r
    head := some C
    heightPair := heightPair
    finalityPair := finalityPair }

end Actions

end Consensus
