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

/-- What the SG/FG action assumes of the store it acts on. **Stated here and discharged
    nowhere in `Spec/`** — these are facts about the stores the handlers build, so they
    belong to the theorems about executions.

    A structure rather than a list of hypotheses (Roberto, 2026-08-21): the next assumption
    becomes a field, and no signature changes. The fields are shaped as exactly what the
    action consumes, so `Spec/` only ever projects them — it never reasons from a general
    invariant to a particular read.

    One theorem will eventually establish the whole bundle for reachable stores; the
    ingredients are recorded in `CONTEXT.md`, the substantial one being that `Σ.T` is closed
    under taking ancestors. -/
structure ActionAssumptions (S : Store Validator Ω) : Prop where
  /-- The accepted blocks are exactly those with a recorded state — the map-domain
      coherence the `Store` type does not enforce. -/
  coherent : ∀ B, B ∈ S.T ↔ B ∈ S.σ
  /-- The round's walk start is accepted. `get_action_root` returns either a block it has
      just tested for membership in `C(Σ)` or the fork-choice root, so this needs only that
      `Σ.J` and `Σ.F` are accepted — which Definition 7 states in prose and the type does
      not enforce — but establishing it here would mean reasoning through that routine's
      `Id.run do`. -/
  walkStartAccepted : ∀ r, getActionRoot S r ∈ S.T

/-- Everything the round's walk can return is accepted: `candidateAccepted`, derived rather
    than assumed (Roberto, 2026-08-21). The candidates are a filter of `S.T` by way of
    `candidateTreeFrom` and `candidateTree`, so set reasoning reaches `S.T`; the two
    walk-start cases — the singleton inside `confirmationCandidates`, and the walk's own
    fallback — are what `walkStartAccepted` is for.

    **A theorem in `Spec/`**, under `CLAUDE.md`'s one exception: `stateAt`'s autoparam
    cannot exist without it. It is the price of stating the assumptions as two general facts
    instead of one tailored to the reads, and it needs maintaining whenever
    `confirmationCandidates`, `candidateTreeFrom` or `candidateTree` changes. -/
theorem mem_T_of_walkResult {S : Store Validator Ω} (hS : ActionAssumptions S) (r : Nat)
    {B : Block Validator}
    (h : B ∈ confirmationCandidates S r (getActionRoot S r) ∨ B = getActionRoot S r) :
    B ∈ S.T := by
  rcases h with h | rfl
  · simp only [confirmationCandidates, Store.candidateTreeFrom, Store.candidateTree,
      Finset.mem_union, Finset.mem_singleton, Finset.mem_filter] at h
    rcases h with rfl | ⟨h, _⟩
    · exact hS.walkStartAccepted r
    · rcases h with ⟨⟨hT, _⟩, _⟩ | rfl
      · exact hT
      · exact hS.walkStartAccepted r
  · exact hS.walkStartAccepted r

/-- The state a store's map records for `B`, with the proof that it records one taken as an
    **autoparam**. Three alternatives, in order: a hypothesis in context; `B` is the round's
    walk start, so `Or.inr rfl` carries it through `mem_T_of_walkResult`; or a witness that
    `B` is one of the round's candidates is in context, which is what the walk's result type
    supplies.

    Anything the alternatives do not cover must pass its proof by hand, and a call that can
    reach none of them fails where it stands.

    It takes the *map*, not the store: the store is recovered by unifying the goal `B ∈ m`
    with the bundle's conclusion, so it need not be an argument. And the body writes
    `(m B).get h` rather than any bracket, so nothing here expands back into itself. -/
def stateAt (m : Block Validator → Option (ChainState Validator)) (B : Block Validator)
    (h : B ∈ m := by
      solve
        | assumption
        | exact (ActionAssumptions.coherent (by assumption) _).mp
            (mem_T_of_walkResult (by assumption) _ (Or.inr rfl))
        | exact (ActionAssumptions.coherent (by assumption) _).mp
            (mem_T_of_walkResult (by assumption) _ (by assumption))) :
    ChainState Validator :=
  (m B).get h

/-- `S.σ⟦B⟧` — the state map read whose proof comes from `stateAt`'s autoparam, as against
    `S.σ[B]`, which keeps core's meaning and its `get_elem_tactic` (Roberto, 2026-08-21).

    Own brackets rather than core's. The earlier attempt claimed `S.σ[B]` itself, which
    needed a `macro_rules` clause matching identifiers whose last component is `σ` —
    name-directed, and unscopable, `macro_rules` having no scoped form. A `notation` cannot
    claim that spelling at all: `S.σ` lexes as one dotted identifier, so an atom `.σ[` is
    never reached, and core's bracket takes the parse. Measured, 2026-08-21, both of them.

    This form has neither problem. The `syntax` is `scoped`, so the parse exists only where
    this namespace is open; `noWs` keeps `f ⟦x⟧` — an application to a quotient class —
    parsing as before; and the term before the bracket is checked against `stateAt`'s first
    argument, so it is the type that decides, not a name. -/
scoped syntax:max term noWs "⟦" term "⟧" : term

macro_rules
  | `($m⟦$B⟧) => `(stateAt $m $B)

/-- Validator `i`'s SG and FG action for round `r`, performed at `a_r`: the one combined
    attestation of the round, its SG half the head, its FG half the two pairs.

    Two hypotheses, both autoparams discharged by `assumption`: `S.t = actionTime r`, that
    this is the round's action time, and `ActionAssumptions S`, the bundle above. A
    statement supplying either must hold it as a *named* hypothesis, since `assumption` does
    not see anonymous arrow binders during statement elaboration (measured on
    `lemChainTargetFirstBlock`).

    The bundle is what makes the body straight-line: both state reads are unconditional and
    written plainly, `S.σ⟦walkStart⟧` and `S.σ⟦C⟧`, their proofs supplied by `stateAt`'s
    autoparam — the walk start through `Or.inr rfl`, the confirmation through `hC`, which
    the destructuring `let` takes from the walk's result type alongside the block itself.
    Before the bundle, each read sat inside `if _ : … ∈ S.σ` with a fallback attestation
    carrying no head and no height pair, and that fallback was unreachable-once-proved
    rather than impossible.

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
    (hS : ActionAssumptions S := by assumption) :
    Attestation Validator := Id.run do
  -- the walk start (Definition 15's action root): derived here from the current store
  -- rather than read from `Σ.action_root[r]`
  let walkStart := getActionRoot S r
  -- the confirmation: run Goldfish from the walk start over the candidates the veto
  -- admits, the walk start among them, so there is always one. `⟨…⟩` and not `(…)`: the
  -- walk returns a subtype, not a pair
  let ⟨C, hC⟩ := S.goldfishConfirmation walkStart (confirmationCandidates S r walkStart)
  -- skeleton: the finality half, independent of the confirmation, off the walk start's
  -- state. Both reads take their proof from `stateAt`'s autoparam, `⟦…⟧` being that read
  let σStart := S.σ⟦walkStart⟧
  let finalityPair : FinalityPair Validator :=
    if σStart.h_j > σStart.h_F then .pair σStart.h_j σStart.J else .empty
  -- skeleton: the current-height half, off the confirmation's state, no history
  let σC := S.σ⟦C⟧
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
