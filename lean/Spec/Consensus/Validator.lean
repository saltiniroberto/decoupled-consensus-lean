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

variable {Validator : Type}

section Actions
variable [DecidableEq Validator] [Electorate Validator] [Params]

/-- The veto on confirmation candidates (skeleton, standing in for a rule of Roberto's):
    `Q` is vetoed when some accepted block on the finalized chain, conflicting with `Q`,
    might still hold majority support — `G0`, in the role the old paper's strong G0 check
    gave it. Computed outside `goldfishConfirmation`, which sees only the already-filtered
    tree. -/
def vetoed (S : Store Validator) (r : Nat) (Q : Block Validator) : Prop :=
  ∃ B ∈ S.T, S.F ⪯ B ∧ ¬ B ∼ Q ∧ G0 S r B

instance (S : Store Validator) (r : Nat) (Q : Block Validator) : Decidable (vetoed S r Q) :=
  inferInstanceAs (Decidable (∃ B ∈ S.T, _))

/-- The blocks the round's confirmation may choose among: the walk start, together with the
    candidates above it that the veto does not exclude.

    **The walk start is never filtered out** (Roberto, 2026-08-20), even when it is itself
    vetoed. The veto says "do not move onto a vetoed block", not "do not vote": a validator
    always confirms at least the root its own fork choice anchored on. So this set is never
    empty, which is what makes the confirmation total.

    Skeleton to the extent `vetoed` is. -/
def confirmationCandidates (S : Store Validator) (r : Nat) (walkStart : Block Validator) :
    Finset (Block Validator) :=
  {walkStart} ∪ (S.candidateTreeFrom walkStart).filter fun B => ¬ vetoed S r B

/-- `s` is a *subtree rooted at* `R`: `R` is in it, everything in it descends from `R`, and
    it has no gaps — every block lying between `R` and a member is itself a member. A walk
    from `R` can move within such a set one block at a time, never has to jump, and always
    has somewhere to be.

    `{R}` qualifies: it is what a walk from `R` sees when nothing above `R` is available.
    The empty set does not, which is the point — see `goldfishConfirmation`. -/
def IsSubtreeFrom (R : Block Validator) (s : Finset (Block Validator)) : Prop :=
  R ∈ s ∧ (∀ B ∈ s, R ⪯ B) ∧ ∀ B ∈ s, ∀ C, R ⪯ C → C ⪯ B → C ∈ s

/-- The round's Goldfish confirmation (Roberto's rule, 2026-08-20): run the Goldfish fork
    choice from `walkStart` over exactly the blocks of `candidates`. **It always returns a
    block** — no `Option`.

    That totality is what `hCandidates` is for. `IsSubtreeFrom walkStart candidates`
    says the set contains `walkStart`, so it is nonempty and the selection has something to
    pick; and it says the set is gap-free, so a walk can traverse it a block at a time.
    Neither fact is proved here: nothing in `Spec/` discharges it, because tree-ness of the
    real argument rests on invariants of the stores the handlers build. The obligation
    belongs to a theorem about executions, and `CONTEXT.md` records what is owed.

    The walk itself is the draft's Section 5, undrafted, so the store's `Ω` stands for
    "run Goldfish from the walk start over this set", and the membership proof `Ω` carries
    is what makes the result one of the caller's candidates. `walkStart` is therefore read
    only through the hypothesis today, and the parameter is kept because a Goldfish fork
    choice without a starting point is not the notion this stands for. -/
def goldfishConfirmation (S : Store Validator) (walkStart : Block Validator)
    (candidates : Finset (Block Validator))
    (hCandidates : IsSubtreeFrom walkStart candidates) : Block Validator :=
  (S.Ω candidates ⟨walkStart, hCandidates.1⟩).val

/-- Validator `i`'s SG and FG action for round `r`, performed at `a_r`: the one combined
    attestation of the round, its SG half the head, its FG half the two pairs.

    Two hypotheses, both autoparams discharged by `assumption`, so a call site that holds
    them in context writes nothing and one that does not must prove them:

    * `S.t = actionTime r` — this is the round's action time;
    * `hCandidates` — the confirmation's candidate set is a subtree rooted at the anchor,
      which `goldfishConfirmation` requires and nothing here proves. It is passed straight
      through. See that definition on why the obligation belongs to a theorem about
      executions.

    A statement supplying either must hold it as a *named* hypothesis: `assumption` does
    not see anonymous arrow binders during statement elaboration (measured on
    `lemChainTargetFirstBlock`).

    **The body is a skeleton, not a rule.** The pipeline as dictated so far, 2026-08-20,
    with the remaining inventions marked `skeleton:`. What it does:

    * anchor at `A = get_action_root(Σ, r)`, **derived here rather than read from**
      `Σ.action_root[r]` (Roberto, 2026-08-20). `on_tick` writes that entry at this same
      instant, so on schedule the two agree; deriving it is what makes the anchor
      well-formed against the *current* store — `get_action_root` returns either a block
      of `C(Σ)` or the fork-choice root itself, so `Σ`'s fork-choice root always precedes
      `A`, and `candidateTreeFrom A` is therefore a tree rather than `{A}` floating above a
      gap. A stored root could not promise that, finality having moved on since the write;
    * derive the round's confirmation `C` with `goldfishConfirmation` from `A`, under the
      veto "some accepted block on the finalized chain, conflicting with the candidate,
      might still hold majority support" — `G0`, playing the role the old paper's strong G0
      check gave it. There is always a confirmation: the veto never removes `A` itself, so
      the candidate set contains it;
    * head is `C`, and the current-height pair is read off `C`'s post-state — the exact
      target vote at a justifiable height, the empty-target (progress-only) vote at a
      nonjustifiable one, the same test Figure 1's justify event applies on receipt. **So
      the validator never abstains from the current-height pair**, where the old paper's
      rule did whenever no veto-free confirmation existed;
    * the finality half is independent of the confirmation, as in the old paper: read off
      the anchor's post-state, commit the latest justification `(h_j, J)` while it is
      unfinalized — heights in the two pairs always differ (`h_j < h`), so one honest
      attestation cannot trip slashing condition E1 against itself.

    Still consciously dropped from the old pipeline, each a decision to re-make: the
    source-proposal branch — the old rule prefers the graded proposal's state over the
    confirmation's — and the signing history, which the old rule filters every pair
    through. -/
def onSGFGVotingAction (i : Validator) (S : Store Validator) (r : Nat)
    (_ : S.t = actionTime r := by assumption)
    (hCandidates : IsSubtreeFrom (getActionRoot S r)
        (confirmationCandidates S r (getActionRoot S r)) := by assumption) :
    Attestation Validator := Id.run do
  -- the anchor (Definition 15): the round's action root, derived here from the current
  -- store rather than read from `Σ.action_root[r]`
  let A := getActionRoot S r
  -- skeleton: the finality half, independent of the confirmation, off the anchor's state
  let finalityPair : FinalityPair Validator :=
    if _ : A ∈ S.σ then
      let σ := S.σ[A]
      if σ.h_j > σ.h_F then .pair σ.h_j σ.J else .empty
    else .empty
  -- the confirmation: run Goldfish from `A` over the candidates the veto admits, `A`
  -- among them, so there is always one
  let C := goldfishConfirmation S A (confirmationCandidates S r A) hCandidates
  if _ : C ∈ S.σ then
    let σ := S.σ[C]
    -- skeleton: the current-height half, off the confirmation's state, no history
    let heightPair : HeightPair Validator :=
      if σ.h % Params.K = 0 ∧ σ.h - σ.h_F > Params.D then .emptyTarget σ.h
      else .target σ.h σ.T_h
    return {
      validator := i
      round := r
      head := some C
      heightPair := heightPair
      finalityPair := finalityPair }
  -- skeleton: a confirmation the state map misses — no head, no height pair, the finality
  -- half still going out. Unreachable once the map's domain is known to cover `Σ.T`.
  return { validator := i, round := r, head := ⊥, heightPair := .empty
           finalityPair := finalityPair }

end Actions

end Consensus
