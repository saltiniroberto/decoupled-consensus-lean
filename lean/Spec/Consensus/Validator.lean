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

/-- Validator `i`'s SG and FG action for round `r`, performed at `a_r`: the one combined
    attestation of the round, its SG half the head, its FG half the two pairs.

    **The result is `Except`, and the reads raise** (Roberto, 2026-08-21). `Σ.σ⟦B⟧` is the
    raising read of `Fig2FinalityStore.lean`, so `let σ ← S.σ⟦B⟧` propagates a missing map
    entry to the caller and this routine carries **no hypotheses at all**. A caller writes
    the body it wants — a branch or a loop anywhere, the call at the end — and owes nothing
    at the call.

    What that replaced, and why: the four autoparams this took until 2026-08-21 —
    `S.t = actionTime r`, map-domain coherence, that the walk start is accepted, and that the
    confirmation has a recorded state. Three of them existed only to justify the two map
    reads, and the exception subsumes them. The fourth, the clock, is **still here, as the
    routine's first line**: it is not about a read, so nothing subsumes it, and it could not
    stay a hypothesis either — a caller whose body has a mutating branch before the call
    cannot supply one, the store after a join point being a variable nothing in scope can
    name. Checked and raised, it costs the caller nothing. Earlier shapes, all in git
    history: a bundle whose fields were shaped to the reads; hypotheses stating the reads'
    own side conditions; general hypotheses with each read naming its proof in the `'…` form;
    and general hypotheses with the bridge assumed as an implication and a `solve_by_elim`
    clause on the bracket's extension point.

    Reading the result: `let α ← onSGFGVotingAction i S r` inside another `Except` routine
    propagates the failure; `(onSGFGVotingAction i S r).toOption` turns it into an `Option`;
    and a caller that must return a store regardless — `on_tick`, when it dispatches this —
    writes `((onSGFGVotingAction i S r).toOption).elim S (onAttestation S)`, which leaves the
    store alone on a failure. `scratch/Probe.lean` has the three worked out.

    Nothing in this file is a theorem, and now nothing needs one. What `Analysis/` owes
    instead is the statement that the exception never fires: on a store whose accepted blocks
    all have recorded states, and whose action root is accepted, this returns `.ok`.

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
def onSGFGVotingAction (i : Validator) (S : Store Validator Ω) (r : Nat) :
    Except (StoreError Validator) (Attestation Validator) := do
  -- the precondition, checked rather than assumed: this runs at `a_r` and nowhere else
  if S.t ≠ actionTime r then
    throw (.wrongTime S.t (actionTime r))
  -- the walk start (Definition 15's action root): derived here from the current store
  -- rather than read from `Σ.action_root[r]`
  let walkStart := getActionRoot S r
  -- the confirmation: run Goldfish from the walk start over the candidates the veto
  -- admits, the walk start among them, so there is always one
  let C : Block Validator :=
    S.goldfishConfirmation walkStart (confirmationCandidates S r walkStart)
  -- skeleton: the finality half, independent of the confirmation, off the walk start's
  -- state. Both reads raise on a block the map does not record, and propagate
  let σStart ← S.σ⟦walkStart⟧
  let finalityPair : FinalityPair Validator :=
    if σStart.h_j > σStart.h_F then .pair σStart.h_j σStart.J else .empty
  -- skeleton: the current-height half, off the confirmation's state, no history
  let σC ← S.σ⟦C⟧
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
