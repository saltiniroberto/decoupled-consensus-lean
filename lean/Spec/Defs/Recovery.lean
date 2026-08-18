import Spec.Fig1SlotReplay
import Spec.Defs.Voting

/-!
# The recovery machinery — Definitions 29–32, 37–44 and 46, and the full Definition 47

`recovery_core.tex`: Definitions 29 (`def:rederivation`, lines 222–255),
30 (`def:activation-filter`, lines 257–294), 31 (`def:recovery-context`, lines 322–357),
32 (`def:walk-standing`, lines 359–380), 37 (`def:active-grade`, lines 560–571),
38 (`def:tsq-views`, lines 714–738), 39 (`def:tsq-confirmation`, lines 740–762),
40 (`def:grade-root-choice`, lines 1075–1121), 41 (`def:stable-root`, lines 1123–1191),
42 (`def:action-root`, lines 1256–1308), 43 (`def:recovery-proposal`, lines 1311–1397),
44 (`def:usable-honest-round`, lines 1399–1433), 46 (`def:official-confirmation`,
lines 1635–1706), and Definition 47 (`def:ordinary-current-target`, lines 1814–1869) in
full — both its branches, where `Spec/Defs/Voting.lean`'s `ordinaryContext` renders only
the no-source-proposal branch. Everything here is a pure function over explicit inputs;
`Spec/Protocol.lean` supplies them from the validator's state at the scheduled times.

## The identifications this file rests on (each decided earlier, reused here)

* A fork-choice state is a `Store`, and `simplexRoot(Σ)` is `Store.walkStartFromFGVotes` —
  the reading
  `sgHeadOk`'s docstring establishes. The three per-round states
  `Σ_sel`, `Σ_vote`, `Σ_act` of Definition 28 (`def:recovery-timing`) are store values
  derived at the round's cutoffs.
* The candidate tree `C(Σ)` of Definition 31 is the viable subtree at or above
  `Store.walkStartFromFGVotes`.

## Rendering decisions made in this file (Roberto asked for them, 2026-08-18)

1. **The activation filter is a snapshot substitution.** Definition 30 excludes a
   finality pair from root selection unless a block accepted by the preceding action
   cutoff `a_{r−1}` records it, and says the filter "is therefore a fixed function of the
   store at `a_{r−1}`" while "only the store maximum and block tree can change" within
   the round. So `cur.withJustificationAndFinalityFrom snap` keeps the current tree, state map and
   `hmax` and takes `(J, h_j, F)` from the snapshot — the store held at `a_{r−1}`, whose
   own selection fields are exactly the greatest pairs recorded by blocks accepted by
   then.
2. **Definition 31's aging witnesses are `blocksAcceptedByPrevSGFGVote`.** Its aged membership
   needs a witness "received *and accepted*" by `a_{r−1}`; the store does not record
   receipt times, and for honestly relayed blocks the definition itself says receipt and
   acceptance coincide. The witness set passed in is `snap.T`, the blocks accepted by the
   cutoff. The strict-receipt refinements this loses (Definition 28's selection cutoff,
   Definition 41's timeliness test) are noted at their use sites.
3. **"Processed finalized evidence" is what the store has replayed.** Definitions 29, 37,
   40–42 and 46 test blocks against "finalized roots whose evidence the validator has
   processed". Here evidence reaches a validator only through accepted blocks, so the
   processed finalized roots are the `F` fields of the recorded chain states:
   `processedFinalized`.
4. **`deepest` picks by depth, then `Ω`.** The paper's "deepest" selections are over sets
   its lemmas make chains (Corollary 2, `cor:g3-chain`; Lemma 27, `lem:tsq-uniqueness`),
   where the depth-maximal element is unique. Over an arbitrary `Finset` this function
   keeps the depth-maximal elements and lets `Omega.choose` pick — the same totalization
   device as `getConfirmed`, and on a chain `Ω` has no freedom.
5. **The `Finset` GHOST walk breaks ties by weight, then `hash(·)`, then `Ω`.**
   `Finset.toList` is noncomputable, so Definition 46's walk over the action state's
   candidate tree cannot reuse `ghostFrom`'s list rendering; `ghostWalk` is the same walk
   over the `Finset`, with Assumption 12 (`ass:recovery-goldfish`, lines 1487–1524)'s
   retained "deterministic tiebreak" rendered as larger `hash(·)` and then `Ω` — `Ω`
   never fires under the collision-freedom idealization (`HashInjective`).
6. **`h_F` and `hasJC` are discharged from the store**, closing the two inputs
   `Spec/Defs/Voting.lean`'s header left open. Definition 49 reads `(F, h_F)` from the
   fork-choice action state; every recorded chain state carries `h_F` (Definition 13,
   `def:chain-state`), so `Store.h_F` reads the height off the states that record `S.F`
   as their finalized block. Definition 49's "it knows the justification certificate
   `JC(h_j, J)`" (Definition 21, `def:certificates`, lines 945–967) is knowledge of a
   target quorum, its inclusions on one chain, and the height event that set the pair;
   a store whose recorded state replayed that event holds all three, so `Store.hasJC`
   asks for a recorded state carrying the pair.
7. **Committees and proposer selection are ambient classes.** Assumption 3
   (`ass:goldfish-committees`, `height_filter_healing.tex` lines 250–258) and
   Definition 43 both place the selection rules outside the paper's scope, so
   `Committees` and `ProposerSelection` are classes the way `Electorate` and `Omega`
   are: a statement binding them quantifies over every rule.

## What stays unrendered

The proposer's own branch — choosing a stable root, running the merged-view GHOST and
building the proposal block (Definition 43's honest-proposer paragraph, and Figure 5,
`alg:recovery-action`, steps 5–7) — because block *content* production (which attestations to
include) is a layer this project has not modelled anywhere. Proposals arrive as messages.
Definition 43's carried-view consistency check is subsumed: the store's own `on_block`
admission re-checks ancestry, so an unconnectable proposal block simply fails acceptance
membership. Definition 51 (`def:earlier-votes`, retransmission) is delivery policy, not
validator state, and stays with the network model.
-/

set_option autoImplicit false

namespace Decoupled

open scoped Decoupled
open Framework.StsMultisetLog

variable {Node Root : Type}

/-! ## Ambient interfaces: committees and proposer selection -/

/-- Assumption 3 (`ass:goldfish-committees`, `height_filter_healing.tex` lines 250–258):
    each slot has "a known subset of `V`" casting that slot's raw Goldfish votes. How
    committees are drawn is outside the paper's scope, so the assignment is a class, the
    way the electorate is. The slot is indexed by its vote time — the reading at which
    the members cast, which is the `slot` field their votes carry. -/
class Committees (Node : Type) where
  /-- The committee of the slot whose vote phase is the given reading. -/
  committee : Time → Finset Node

/-! ## The four grades are decidable

`G3`–`G0` (Definition 36, `def:grades`) are `Prop`-valued strict-majority tests; each is
definitionally a `StrictMajority`, which is decidable, so the instances below are
re-ascriptions, not proofs. They exist so the machinery here can branch on a grade. -/

section
variable [DecidableEq Node] [DecidableEq Root] [Electorate Node]

instance (Xm X1 : Finset (Attestation Node Root)) (r : Nat) (B : Blk Node Root) :
    Decidable (G3 Xm X1 r B) :=
  inferInstanceAs (Decidable (StrictMajority _))

instance (X0 : Finset (Attestation Node Root)) (r : Nat) (B : Blk Node Root) :
    Decidable (G2 X0 r B) :=
  inferInstanceAs (Decidable (StrictMajority _))

instance (X1 : Finset (Attestation Node Root)) (r : Nat) (B : Blk Node Root) :
    Decidable (G1 X1 r B) :=
  inferInstanceAs (Decidable (StrictMajority _))

instance (X2 : Finset (Attestation Node Root)) (r : Nat) (B : Blk Node Root) :
    Decidable (G0 X2 r B) :=
  inferInstanceAs (Decidable (StrictMajority _))

end

/-! ## Depth, the deepest pick, and the chain maximum -/

/-- How many blocks a chain has up to and including `B`. The paper's "deepest" selections
    compare blocks by chain position; this is that measure, off the ancestor list `Blk`
    carries structurally. -/
def depth (B : Blk Node Root) : Nat := (ancestors B).length

section
variable [DecidableEq Node] [DecidableEq Root]

/-- The deepest block of a set, or `⊥` on the empty set. The paper's "deepest" selections
    (Definitions 40, 46) are over sets its lemmas make chains, where the depth-maximal
    element is unique; over an arbitrary set this keeps the depth-maximal elements and
    lets `Ω` pick — rendering decision 4 in the module header. -/
def deepest [Omega Node Root] (s : Finset (Blk Node Root)) : Option (Blk Node Root) :=
  let top := s.filter fun B => ∀ C ∈ s, depth C ≤ depth B
  if h : top.Nonempty then some (Omega.choose top h).val else ⊥

/-- The deeper of two blocks on one chain: the descendant. Remark 11
    (`rem:stable-root-coherence`, lines 1193–1217) is what puts Definition 41's three
    roots on one chain, so their maximum needs no `Ω`. Off a chain (unreachable there)
    the second argument wins, deterministically. -/
def chainMax (a b : Blk Node Root) : Blk Node Root :=
  if b ⪯ a then a else b

end

/-! ## Definitions 30 and 31 — the activation filter and the candidate trees -/

section
variable [DecidableEq Node] [DecidableEq Root] [Electorate Node]

/-- Definition 30 (`def:activation-filter`, lines 257–294) — the paper's *activation
    filter*: material from the current store, verdicts (`J`, `h_j`, `F`) from the store
    at the previous SG/FG vote.

    **The paper's text, verbatim:**

    > A finality outcome takes effect in a validator's round-`r` selection, vote, and
    > action states when its evidence was processed by that validator's preceding-round
    > action cutoff `a_{r−1}`.
    >
    > For the first counted recovery round, the preceding action cutoff is the relay
    > point of Definition 53 (`def:relay-frontier`): every pre-window object has crossed
    > it, so the first round's activation filter and the aged viability test below are
    > total there, and the one-round staggering bound has its base case at that cutoff.
    >
    > This is implemented in the derivation, not merely asserted: the three per-round
    > states are derived by running the ordinary fork-choice derivation with the
    > *activation filter*: a justification or finalized pair is excluded from the
    > greatest-justification and greatest-finalized selection of every round-`r` state —
    > and treated as evidence — unless some block that was received *and accepted* by
    > `a_{r−1}` has a derived state recording that pair. Both conditions are fixed once
    > `a_{r−1}` has passed: receipt times are the store's `r_S` values, and a block
    > queued behind missing ancestry at the cutoff does not activate the pair this round
    > even if its ancestry arrives mid-round — honest relay carries required ancestry
    > with every block (Assumption 12, `ass:recovery-goldfish`), so for honestly relayed
    > blocks receipt and acceptance coincide. The filter is therefore a fixed function
    > of the store at `a_{r−1}`. The filtered derivation is the algorithm of
    > Definition 26 (`def:finality-root`) with this one added selection guard; `hmax`,
    > the viable subtree, and the Simplex root are all computed from the filtered
    > selection. All other processing is unchanged.
    >
    > In plain words, newly learned finality steers selection only from the next round;
    > Remark 9 (`rem:activation-stagger`) below records the two consequences used
    > throughout.

    **The same text, in this file's terminology** — activation filter → the
    justification-and-finality substitution, action → SG/FG vote, root → walk-start:

    > A finality outcome takes effect in a validator's round-`r` selection, vote, and
    > SG/FG-vote states when its evidence was processed by that validator's
    > preceding-round SG/FG-vote cutoff `a_{r−1}`.
    >
    > For the first counted recovery round, the preceding SG/FG-vote cutoff is the relay
    > point of Definition 53: every pre-window object has crossed it, so the first
    > round's substitution and the aged viability test below are total there, and the
    > one-round staggering bound has its base case at that cutoff.
    >
    > This is implemented in the derivation, not merely asserted: the three per-round
    > states are derived by running the ordinary fork-choice derivation with the
    > *justification-and-finality substitution*: a justification or finalized pair is
    > excluded from the greatest-justification and greatest-finalized selection of every
    > round-`r` state — and treated as evidence — unless some block that was received
    > *and accepted* by `a_{r−1}` has a derived state recording that pair. Both
    > conditions are fixed once `a_{r−1}` has passed: receipt times are the store's
    > `r_S` values, and a block queued behind missing ancestry at the cutoff does not
    > activate the pair this round even if its ancestry arrives mid-round — honest relay
    > carries required ancestry with every block, so for honestly relayed blocks receipt
    > and acceptance coincide. The substitution is therefore a fixed function of the
    > store at `a_{r−1}`. The substituted derivation is the algorithm of Definition 26
    > with this one added selection guard; `hmax`, the viable subtree, and the Simplex
    > walk-start are all computed from the substituted verdicts. All other processing is
    > unchanged.
    >
    > In plain words, newly learned finality steers selection only from the next round.

    Rendered as the fixed function the definition itself names — rendering decision 1:
    the per-round state keeps the current tree, map and `hmax` and takes its verdict
    fields `(J, h_j, F)` from `snap`, the store held at `a_{r−1}`, whose own fields are
    exactly the greatest pairs recorded by blocks accepted by then. `hmax`, the viable
    subtree and the walk-start are then "computed from the filtered selection", which is
    what the record update gives. -/
def Store.withJustificationAndFinalityFrom (cur snap : Store Node Root) :
    Store Node Root :=
  { cur with J := snap.J, h_j := snap.h_j, F := snap.F }

/-- Rendering decision 3: the finalized roots whose evidence this store has processed —
    the `F` field of every recorded chain state. Definitions 29, 37, 40–42 and 46 test
    grades and roots against these. A block the map misses contributes `S.F`, the root
    the store itself already holds. -/
def processedFinalized (S : Store Node Root) : Finset (Blk Node Root) :=
  S.T.image fun B => ((S.σ B).map fun st => st.F).getD S.F

/-- Definition 31 (`def:recovery-context`, lines 322–357):
    `C(Σ) = {B ∈ viableTree(Σ) : simplexRoot(Σ) ⪯ B}`, "a prefix-closed tree rooted at
    `simplexRoot(Σ)`. Its viability test always uses the store-global value `Σ.hmax`". -/
def candidateTree (S : Store Node Root) : Finset (Blk Node Root) :=
  (viableTree S).filter fun B => S.walkStartFromFGVotes ⪯ B

/-- Definition 31 (`def:recovery-context`, lines 322–358)'s aged variant `C⁻_u(Σ)` of the
    candidate tree — the paper's *backed candidate tree*, named here by what backs a member: a block
    stays in exactly when a block at-or-above it was accepted by the previous SG/FG-vote
    cutoff and still sits within one height of the current maximum.

    **The paper's text, verbatim (the aged-variant half of Definition 31):**

    > Write `C⁻_u(Σ)` for the *aged* variant of the candidate tree, used exactly where
    > this definition says so. For a *receiver's grade-root selection only*, the
    > viability test uses aged witnesses. A block `B ∈ C(Σ)` is in `C⁻_u(Σ)` exactly
    > when some block `W` with `B ⪯ W` was received *and accepted* by that validator's
    > preceding-round action cutoff `a_{r−1}` and has derived state-height
    > `σ[W].h ≥ Σ.hmax − 1`. Here `W = B` is allowed, whether `W` is a leaf of any tree
    > is irrelevant, and `Σ.hmax` is the deriving state's own current maximum. The
    > receipt-and-acceptance bound is the same condition as the activation filter, so a
    > witness queued behind missing ancestry at the cutoff does not count even if its
    > ancestry arrives later. A witness received or accepted later takes effect one
    > round later — in particular, a young branch that just raised `Σ.hmax` can leave
    > older branches, and even the walk root, without aged membership for one round; the
    > walk-standing rule of Definition 32 (`def:walk-standing`) below keeps every walk
    > defined regardless.
    >
    > In plain words, receivers age their witnesses by one round while the proposer does
    > not, and every recovery choice uses the main store's ordinary `hmax − 1` filter.

    **The same text, in this file's terminology** — backed candidate tree → the candidate tree
    backed by the previous SG/FG vote; aging witnesses → the backing blocks, those
    accepted by the previous SG/FG-vote cutoff; root → walk-start:

    > Write `C⁻_u(Σ)` for the candidate tree backed by the previous SG/FG vote, used
    > exactly where this definition says so. For a *receiver's grade-walk-start selection
    > only*, the viability test uses backing blocks accepted by the previous SG/FG-vote
    > cutoff. A block `B ∈ C(Σ)` is in `C⁻_u(Σ)` exactly when some block `W` with
    > `B ⪯ W` was received *and accepted* by that validator's preceding-round
    > SG/FG-vote cutoff `a_{r−1}` and has derived state-height `σ[W].h ≥ Σ.hmax − 1`.
    > Here `W = B` is allowed, whether `W` is a leaf of any tree is irrelevant, and
    > `Σ.hmax` is the deriving state's own current maximum. The receipt-and-acceptance
    > bound is the same condition as the justification-and-finality substitution, so a
    > backing block queued behind missing ancestry at the cutoff does not count even if
    > its ancestry arrives later. A backing block received or accepted later takes
    > effect one round later — in particular, a young branch that just raised `Σ.hmax`
    > can leave older branches, and even the walk's walk-start, without backed
    > membership for one round; the walk-standing rule of Definition 32 below keeps
    > every walk defined regardless.
    >
    > In plain words, receivers require their backing blocks to be a round old while the
    > proposer does not, and every recovery choice uses the main store's ordinary
    > `hmax − 1` filter.

    The backing blocks are the parameter `blocksAcceptedByPrevSGFGVote` — rendering
    decision 2 — and the state-height reads through the deriving store's own map and
    maximum. -/
def candidateTreeBackedByPrevSGFGVote (S : Store Node Root)
    (blocksAcceptedByPrevSGFGVote : Finset (Blk Node Root)) : Finset (Blk Node Root) :=
  (candidateTree S).filter fun B =>
    ∃ Wb ∈ blocksAcceptedByPrevSGFGVote,
      B ⪯ Wb ∧ (S.σ Wb).any fun st => st.h ≥ S.hmax - 1

/-- The backed candidate tree with Definition 33 (`def:counting-rule`, lines 382–403)'s
    proposal-path exemption: "Blocks on the accepted proposal's path — the proposed root
    `A_p^r` through the parent `Z_p^r` to the proposal block `B_p^r`, and their
    ancestors — are exempt from aging in the acceptance checks and the first-slot walk."
    A block at or below the proposal block is exactly a path block or one of its
    ancestors, so the exemption is the `⪯ B_p` disjunct; membership in the (unaged)
    candidate tree is still required. -/
def candidateTreeBackedByPrevSGFGVoteOrOnProposalPath (S : Store Node Root)
    (blocksAcceptedByPrevSGFGVote : Finset (Blk Node Root))
    (path : Option (Blk Node Root)) : Finset (Blk Node Root) :=
  (candidateTree S).filter fun B =>
    decide (B ∈ candidateTreeBackedByPrevSGFGVote S blocksAcceptedByPrevSGFGVote) ||
      path.any fun Bp => decide (B ⪯ Bp)

end

/-! ## Definitions 37 and 29 — active grades, and the mid-round re-derivation -/

section
variable [DecidableEq Node] [DecidableEq Root]

/-- The conjunct Definitions 29, 37, 40–42 and 46 repeat: `B` "conflicts with no
    finalized root whose evidence the validator has processed". `processedF` is
    `processedFinalized` of the consulted store — rendering decision 3. -/
def ConflictFree (processedF : Finset (Blk Node Root)) (B : Blk Node Root) : Prop :=
  ∀ Rf ∈ processedF, Compatible B Rf

instance (processedF : Finset (Blk Node Root)) (B : Blk Node Root) :
    Decidable (ConflictFree processedF B) :=
  inferInstanceAs (Decidable (∀ Rf ∈ processedF, Compatible B Rf))

/-- Definition 37 (`def:active-grade`, lines 560–571): "validator `u` uses grade `j` for
    `B` only when `G_j_u(B)` holds, `B` is in the accepted subtree rooted at `Σ.F`, and
    `B` conflicts with no finalized root whose evidence `u` has processed". The grade
    itself enters as the `holds` argument, so one filter serves all four grades. -/
def ActiveGrade (holds : Prop) (S : Store Node Root)
    (processedF : Finset (Blk Node Root)) (B : Blk Node Root) : Prop :=
  holds ∧ B ∈ S.T ∧ S.F ⪯ B ∧ ConflictFree processedF B

instance (holds : Prop) [Decidable holds] (S : Store Node Root)
    (processedF : Finset (Blk Node Root)) (B : Blk Node Root) :
    Decidable (ActiveGrade holds S processedF B) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- Definition 29 (`def:rederivation`, lines 222–255), at one slot boundary. The fixed
    root is effectively ungraded when it was classified ungraded at the vote time or its
    grade has since become inactive — the definition's one exit, "the root conflicts with
    a finalized root whose evidence the validator has since processed" — and an
    effectively ungraded root is re-derived exactly when "the validator's current state
    selects a Simplex root different from the fixed root". The re-derived root is the
    boundary state's own walk-from block, classified ungraded. A graded root whose grade
    stays active is never abandoned mid-round.

    **The paper's text, verbatim (Definition 29):**

    > The vote-time stable root is subject to one exception for ungraded roots: if the
    > fixed root is ungraded — the vote state's Simplex root, whether as fallback or as
    > an accepted ungraded proposed root, which equals that selection by the stable-root
    > rule of the proposal section; the graded alternative is specified with the same
    > rule — and, at a later slot boundary of the round, the validator's current state
    > selects a Simplex root different from the fixed root, it re-derives its stable
    > root at that boundary and uses the re-derived root for the round's remaining
    > slots. The test is deterministic: it compares the fixed root with the current
    > state's Simplex root, both locally derived. After re-derivation, every later
    > reference to the round's vote-time stable root — later-slot walks, the action-root
    > rule, and the action head — names the re-derived root. The re-derived root is
    > finality-backed by Definition 26 (`def:finality-root`); it follows the state's own
    > Simplex selection, which may sit below the abandoned justification when the
    > selection rule switches from a justification to the finalized root. A graded
    > stable root is never abandoned mid-round while its grade stays active, with one
    > exit: if the root's grade becomes inactive under Definition 37
    > (`def:active-grade`) — the root conflicts with a finalized root whose evidence the
    > validator has since processed — the root counts as ungraded from the next slot
    > boundary on and is subject to the same exception. Every ungraded root — fallback
    > or accepted ungraded proposed root — is subject to the exception.
    >
    > In plain words, an ungraded stable root follows the validator's own selection when
    > that selection moves mid-round, and a graded root is dropped only when finality
    > evidence kills its grade.

    **The same text, in this file's terminology** — root → walk-start, action → SG/FG
    vote:

    > The vote-time stable walk-start is subject to one exception for ungraded
    > walk-starts: if the fixed walk-start is ungraded — the vote state's Simplex
    > walk-start, whether as fallback or as an accepted ungraded proposed walk-start,
    > which equals that selection by the stable-walk-start rule of the proposal section;
    > the graded alternative is specified with the same rule — and, at a later slot
    > boundary of the round, the validator's current state selects a walk-start from FG votes
    > different from the fixed walk-start, it re-derives its stable walk-start at that
    > boundary and uses the re-derived walk-start for the round's remaining slots. The
    > test is deterministic: it compares the fixed walk-start with the current state's
    > walk-start from FG votes, both locally derived. After re-derivation, every later
    > reference to the round's vote-time stable walk-start — later-slot walks, the
    > SG/FG-vote walk-start rule, and the SG/FG-vote head — names the re-derived
    > walk-start. The re-derived walk-start is finality-backed by Definition 26; it
    > follows the state's own Simplex selection, which may sit below the abandoned
    > justification when the selection rule switches from a justification to the
    > finalized root. A graded stable walk-start is never abandoned mid-round while its
    > grade stays active, with one exit: if the walk-start's grade becomes inactive
    > under Definition 37 — the walk-start conflicts with a finalized root whose
    > evidence the validator has since processed — the walk-start counts as ungraded
    > from the next slot boundary on and is subject to the same exception. Every
    > ungraded walk-start — fallback or accepted ungraded proposed walk-start — is
    > subject to the exception.
    >
    > In plain words, an ungraded stable walk-start follows the validator's own
    > selection when that selection moves mid-round, and a graded walk-start is dropped
    > only when finality evidence kills its grade.
    In plain words: a root backed by a live grade stays put; a root that was only the
    validator's own selection follows that selection when it moves. -/
def rederive (cur : Store Node Root) (processedF : Finset (Blk Node Root))
    (walkStart : Blk Node Root) (graded : Bool) : Blk Node Root × Bool :=
  let live := graded ∧ ConflictFree processedF walkStart
  if ¬ live ∧ cur.walkStartFromFGVotes ≠ walkStart then (cur.walkStartFromFGVotes, false)
  else (walkStart, decide live)

end

/-! ## Definitions 38 and 39 — TSQ views and the available confirmation -/

section
variable [DecidableEq Node] [DecidableEq Root]

/-- Definition 38 (`def:tsq-views`, lines 714–738): member `i` "visibly equivocates in
    `X` when `X` contains two distinct votes of this slot signed by `i`". `s` is the
    slot's vote phase — the `slot` field the votes of that slot carry. -/
def visiblyEquivocates (X : Finset (GoldfishVote Node Root)) (s : Time) (i : Node) :
    Prop :=
  ∃ v ∈ X, ∃ v' ∈ X, v.slot = s ∧ v'.slot = s ∧
    v.validator = i ∧ v'.validator = i ∧ v ≠ v'

instance (X : Finset (GoldfishVote Node Root)) (s : Time) (i : Node) :
    Decidable (visiblyEquivocates X s i) :=
  inferInstanceAs (Decidable (∃ v ∈ X, ∃ v' ∈ X, v.slot = s ∧ v'.slot = s ∧
    v.validator = i ∧ v'.validator = i ∧ v ≠ v'))

/-- Definition 38: member `i` "supports block `B` in `X` … when `X` contains exactly one
    vote of this slot signed by `i` and that vote names a block in `B`'s subtree".
    Exactly one is at least one and no two distinct, so the spelling is a vote above `B`
    plus no visible equivocation. -/
def SupportsIn (X : Finset (GoldfishVote Node Root)) (s : Time) (i : Node)
    (B : Blk Node Root) : Prop :=
  ¬ visiblyEquivocates X s i ∧ ∃ v ∈ X, v.slot = s ∧ v.validator = i ∧ B ⪯ v.target

instance (X : Finset (GoldfishVote Node Root)) (s : Time) (i : Node) (B : Blk Node Root) :
    Decidable (SupportsIn X s i B) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Definition 38: "A participant in `X` is a committee member with at least one vote of
    this slot in `X`, timely or not." -/
def participants (X : Finset (GoldfishVote Node Root)) (s : Time)
    (committee : Finset Node) : Finset Node :=
  committee.filter fun i => ∃ v ∈ X, v.slot = s ∧ v.validator = i

/-- Definition 39 (`def:tsq-confirmation`, lines 740–762): the time-shifted support
    `ts_u(B)`, the members supporting `B` in both the support view `V⁻` (the freeze at
    `f = d + 2Δ`) and the evaluation view `V⁺` (at `e = d + 6Δ`). Counted by identity,
    one unit per member, per Definition 38. -/
def tsSupport (Vm Vp : Finset (GoldfishVote Node Root)) (s : Time)
    (committee : Finset Node) (B : Blk Node Root) : Nat :=
  (committee.filter fun i => SupportsIn Vm s i B ∧ SupportsIn Vp s i B).card

/-- Definition 39: "Block `B` is available-confirmed at `u` when `2 ts_u(B) > n_u`",
    with `n_u` the live participation — the participants counted in the evaluation view.

    In plain words: the support is frozen early and cleaned of every double vote visible
    late, the participation is counted late, and a strict majority of the late count
    confirms. -/
def AvailableConfirmed (Vm Vp : Finset (GoldfishVote Node Root)) (s : Time)
    (committee : Finset Node) (B : Blk Node Root) : Prop :=
  2 * tsSupport Vm Vp s committee B > (participants Vp s committee).card

instance (Vm Vp : Finset (GoldfishVote Node Root)) (s : Time) (committee : Finset Node)
    (B : Blk Node Root) : Decidable (AvailableConfirmed Vm Vp s committee B) :=
  inferInstanceAs (Decidable (_ > _))

end

/-! ## The `Finset` GHOST walk — Definitions 32 and 33 over a `Finset` tree -/

section
variable [DecidableEq Node] [DecidableEq Root] [BlockHash Node Root]

/-- One step of the recovery walk: among the tree's children of `B`, the heaviest under
    Definition 33 (`def:counting-rule`)'s weights — every known vote counts, the tree
    only constrains the choice — with ties broken by larger `hash(·)` and then `Ω`
    (rendering decision 5). `none` when `B` has no child in the tree, which is
    Definition 32 (`def:walk-standing`, lines 359–380)'s "a block with no viable …
    candidate child returns itself, exactly as ordinary GHOST returns a childless
    block". -/
def ghostStep [Omega Node Root] (votes : Finset (GoldfishVote Node Root))
    (tree : Finset (Blk Node Root)) (B : Blk Node Root) : Option (Blk Node Root) :=
  let children := tree.filter fun C => C.parent = some B
  let heaviest := children.filter fun C =>
    ∀ D ∈ children, goldfishWeight votes D ≤ goldfishWeight votes C
  let winners := heaviest.filter fun C => ∀ D ∈ heaviest, hash(D) ≤ hash(C)
  if h : winners.Nonempty then some (Omega.choose winners h).val else none

/-- The recovery walk, fuel-indexed like `ghostFrom` and total the same way
    (Lemma 20, `lem:aged-walk-total`, lines 468–480 — the walk "starts at the round's
    fixed root, each step moves to a viable … candidate child, and a block with no such
    child returns itself"). Per Definition 32 the root is walked from "whether or not
    that root is in the walk's candidate tree". Callers pass the tree's card as fuel:
    every step strictly deepens within the tree. -/
def ghostWalk [Omega Node Root] (votes : Finset (GoldfishVote Node Root))
    (tree : Finset (Blk Node Root)) : Nat → Blk Node Root → Blk Node Root
  | 0, B => B
  | fuel + 1, B =>
      match ghostStep votes tree B with
      | some C => ghostWalk votes tree fuel C
      | none => B

/-- Definition 45 (`def:recovery-goldfish-vote`, lines 1587–1602) over the wiring's
    `Finset` tree — the same rule as `goldfishVote`, walking `ghostWalk` instead of the
    explicit-list `ghost`. The caller passes the merged view's counted votes and the

    **The paper's text, verbatim (Definition 45, lines 1587–1602):**

    > At `d_r + Δ`, an honest committee member merges the recognized proposal's carried
    > ordinary view into its own frozen slot view — the receipt buffer is not merged
    > before the slot-view freeze — runs vote-time GHOST from its accepted stable root
    > within the aged tree `C⁻_u(Σ_{u,vote}^r)`, with the proposal-path exemption of
    > Definition 33 (`def:counting-rule`), and votes for that output; the walk is total
    > by Lemma 20 (`lem:aged-walk-total`). Without a recognized proposal it runs the
    > same rule on its frozen slot view and vote-state candidate tree. No SG head enters
    > either merge, and no walk recomputes `hmax` below the walk's root.
    >
    > In plain words, an accepted proposal supplies ordinary Goldfish data, not a forced
    > vote target.

    **The same text, in this file's terminology** — root → walk-start:

    > At `d_r + Δ`, an honest committee member merges the recognized proposal's carried
    > ordinary view into its own frozen slot view — the receipt buffer is not merged
    > before the slot-view freeze — runs vote-time GHOST from its accepted stable
    > walk-start within the backed candidate tree `C⁻_u(Σ_{u,vote}^r)`, with the proposal-path
    > exemption of Definition 33, and votes for that output; the walk is total by
    > Lemma 20. Without a recognized proposal it runs the same rule on its frozen slot
    > view and vote-state candidate tree. No SG head enters either merge, and no walk
    > recomputes `hmax` below the walk's walk-start.
    >
    > In plain words, an accepted proposal supplies ordinary Goldfish data, not a forced
    > vote target.
    walk's tree; the walk-standing rule of Definition 32 is inherited from `ghostWalk`. -/
def recoveryGoldfishVote [Omega Node Root] (i : Node) (s : Time)
    (votes : Finset (GoldfishVote Node Root)) (tree : Finset (Blk Node Root))
    (walkStart : Blk Node Root) : GoldfishVote Node Root :=
  { validator := i, slot := s, target := ghostWalk votes tree tree.card walkStart }

end

/-! ## Definition 43 — the recovery proposal, as the receiver sees it -/

/-- Definition 43 (`def:recovery-proposal`, lines 1311–1397): the first-slot proposal
    `(r, O_p^r, V_{p,GF}^r, A_p^r, tag_p^r, W_p^r, Z_p^r, B_p^r, π_p^r)`, one field per
    component, minus the credential `π_p^r` — "the ordinary Goldfish proposer credential
    … outside this paper's scope", played by the `ProposerSelection` class below — plus
    the signer, which the discard-both wrapper compares. The carried block context
    `O_p^r` exists "so that every receiver can connect and validate the proposal"; here a
    block carries its ancestry structurally, so connection needs no separate field, and
    the carried set is kept for the vote-referenced blocks it also names. -/
structure RecoveryProposal (Node Root : Type) where
  /-- The round `r` the proposal opens. -/
  r : Nat
  /-- `O_p^r`, the carried ordinary Goldfish blocks. -/
  carriedBlocks : Finset (Blk Node Root)
  /-- `V_{p,GF}^r`, "the proposer's set of raw Goldfish votes for the preceding slot" —
      the input of the proposal-view merge. -/
  carriedGoldfishVotes : Finset (GoldfishVote Node Root)
  /-- `A_p^r`, the proposed root. -/
  proposedWalkStart : Blk Node Root
  /-- `tag_p^r ∈ {graded, ungraded}`, which branch of Definition 41's item 2 the
      proposer claims. "The tag binds the branch." -/
  graded : Bool
  /-- `W_p^r`, the grade-2 witness when the tag is graded; empty otherwise. -/
  grade2Witness : Finset (Attestation Node Root)
  /-- `Z_p^r`, the parent the proposal block extends. -/
  parent : Blk Node Root
  /-- `B_p^r`, the proposal block. -/
  block : Blk Node Root
  /-- The proposal's signer — Definition 28's round proposer at this receiver. The
      discard-both rule compares signers. -/
  proposer : Node
  deriving DecidableEq

section
variable [DecidableEq Node] [DecidableEq Root]

/-- Definition 43's structural validity, the part a receiver can check without its store:
    the proposal is for this round, and "the proposal block is valid, has parent `Z_p^r`,
    and satisfies `S_{p,sel}^r ⪯ A_p^r ⪯ Z_p^r ≺ B_p^r`" — the first inequality is the
    proposer's own obligation and unobservable here; the rest is checked. Everything
    else Definition 41's items re-check per receiver. -/
def RecoveryProposal.wellFormed (p : RecoveryProposal Node Root) (r : Nat) : Prop :=
  p.r = r ∧ p.proposedWalkStart ⪯ p.parent ∧ p.block.parent = some p.parent

instance (p : RecoveryProposal Node Root) (r : Nat) : Decidable (p.wellFormed r) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

end

/-- Definition 28 (`def:recovery-timing`)'s receiver-local proposer selection: "at vote
    time each validator takes the winning eligible proposal among the round proposals in
    its own inclusive vote-time view, as the source's algorithm prescribes" — the
    source's rule, like the credential it reads, is outside the paper's scope, so the
    winner function is a class (rendering decision 7). `winner_mem` is the one fact
    every rule satisfies: the winner is among the candidates. -/
class ProposerSelection (Node Root : Type) where
  /-- The locally winning eligible proposal, if any. -/
  winner : Finset (RecoveryProposal Node Root) → Option (RecoveryProposal Node Root)
  /-- A winner comes from the candidate set. -/
  winner_mem : ∀ s p, winner s = some p → p ∈ s

/-! ## Definition 40 — grade-root choices -/

section
variable [DecidableEq Node] [DecidableEq Root] [Electorate Node] [BlockHash Node Root]
  [Omega Node Root]

/-- Definition 40 (`def:grade-root-choice`, lines 1075–1121), the proposer's choice: "the
    deepest block `A_p^r ∈ C(Σ_{p,sel}^r)` for which it has grade 2 and which conflicts
    with no finalized root whose evidence the proposer has processed", or "the
    selection-state Simplex root `S_{p,sel}^r` as an ungraded base root" when no graded
    block qualifies. Unused by the receiver-side wiring (the proposer branch is not
    rendered — module header) but stated, because the definition is. -/
def proposerRoot (Ssel : Store Node Root) (X0 : Finset (Attestation Node Root)) (r : Nat)
    (processedF : Finset (Blk Node Root)) : Blk Node Root :=
  (deepest ((candidateTree Ssel).filter fun B =>
    G2 X0 r B ∧ ConflictFree processedF B)).getD Ssel.walkStartFromFGVotes

/-- Definition 40, the receiver's lower root `L_u^r`: "the deepest *strict* grade-3 block
    in the backed candidate tree `C⁻_u(Σ_{u,sel}^r)` that remains in the backed candidate tree
    `C⁻_u(Σ_{u,vote}^r)` … or `S_{u,vote}^r` if no strict grade-3 block survives both
    trees", where strict means "strictly descends from that validator's own vote-state
    Simplex root". The definition's "a grade made irrelevant by a newly learned finalized
    root is not retained as a live lower bound" is the `ConflictFree` conjunct — the

    **The paper's text, verbatim (Definition 40, `def:grade-root-choice`,
    lines 1075–1121):**

    > Write `S_{u,sel}^r = simplexRoot(Σ_{u,sel}^r)`,
    > `S_{u,vote}^r = simplexRoot(Σ_{u,vote}^r)`,
    > `S_{u,act}^r = simplexRoot(Σ_{u,act}^r)`.
    >
    > *Proposer choice.* At `d_r`, proposer `p` chooses the deepest block
    > `A_p^r ∈ C(Σ_{p,sel}^r)` for which it has grade 2 and which conflicts with no
    > finalized root whose evidence the proposer has processed — the same
    > processed-finality guard every grade use obeys — and supplies a *grade-2 witness*:
    > a set of signed preceding-round SG heads of weight at least `m`, each supporting
    > `A_p^r`. Witness validity is positive-only — signatures and the eligible round —
    > and never asserts the absence of other messages from the proposer's view; the
    > receiver's own raw `G1_u` predicate, whose favorable counting tolerates
    > equivocation copies the proposer may have omitted, supplies the semantic
    > acceptance guard. If there is no graded block, the proposer proposes the
    > selection-state Simplex root `S_{p,sel}^r` as an ungraded base root.
    >
    > *Receiver lower root.* Throughout, call a graded block *strict* at a validator
    > when it strictly descends from that validator's own vote-state Simplex root
    > `S_{u,vote}^r`. At `d_r + Δ`, validator `u` chooses the deepest *strict* grade-3
    > block in the aged tree `C⁻_u(Σ_{u,sel}^r)` that remains in the aged tree
    > `C⁻_u(Σ_{u,vote}^r)` — unique by Corollary 2 (`cor:g3-chain`) — or `S_{u,vote}^r`
    > if no strict grade-3 block survives both trees. A grade-3 block equal to the
    > selection itself is subsumed by the fallback: the root is then the selection,
    > classified as ungraded for retention and re-derivation, so the two clauses name
    > one rule. Call this lower root `L_u^r`. Thus a grade made irrelevant by a newly
    > learned finalized root is not retained as a live lower bound. These fallback
    > clauses make both selections total.
    >
    > In plain words, the proposer offers its deepest grade-2 root or its own
    > selection, and each receiver fixes its own grade-3 lower bound.

    **The same text, in this file's terminology** — root → walk-start (`simplexRoot` is
    `Store.walkStartFromFGVotes`):

    > Write `S_{u,sel}^r = Σ_{u,sel}^r.walkStartFromFGVotes`,
    > `S_{u,vote}^r = Σ_{u,vote}^r.walkStartFromFGVotes`,
    > `S_{u,act}^r = Σ_{u,act}^r.walkStartFromFGVotes`.
    >
    > *Proposer choice.* At `d_r`, proposer `p` chooses the deepest block
    > `A_p^r ∈ C(Σ_{p,sel}^r)` for which it has grade 2 and which conflicts with no
    > finalized root whose evidence the proposer has processed — the same
    > processed-finality guard every grade use obeys — and supplies a *grade-2 witness*:
    > a set of signed preceding-round SG heads of weight at least `m`, each supporting
    > `A_p^r`. Witness validity is positive-only — signatures and the eligible round —
    > and never asserts the absence of other messages from the proposer's view; the
    > receiver's own raw `G1_u` predicate, whose favorable counting tolerates
    > equivocation copies the proposer may have omitted, supplies the semantic
    > acceptance guard. If there is no graded block, the proposer proposes the
    > selection-state walk-start from FG votes `S_{p,sel}^r` as an ungraded base walk-start.
    >
    > *Receiver lower walk-start.* Throughout, call a graded block *strict* at a
    > validator when it strictly descends from that validator's own vote-state Simplex
    > walk-start `S_{u,vote}^r`. At `d_r + Δ`, validator `u` chooses the deepest
    > *strict* grade-3 block in the backed candidate tree `C⁻_u(Σ_{u,sel}^r)` that remains in the
    > backed candidate tree `C⁻_u(Σ_{u,vote}^r)` — unique by Corollary 2 — or `S_{u,vote}^r` if no
    > strict grade-3 block survives both trees. A grade-3 block equal to the selection
    > itself is subsumed by the fallback: the walk-start is then the selection,
    > classified as ungraded for retention and re-derivation, so the two clauses name
    > one rule. Call this lower walk-start `L_u^r`. Thus a grade made irrelevant by a
    > newly learned finalized root is not retained as a live lower bound. These fallback
    > clauses make both selections total.
    >
    > In plain words, the proposer offers its deepest grade-2 walk-start or its own
    > selection, and each receiver fixes its own grade-3 lower bound.
    processed-finality filter every grade use obeys (Definition 37). -/
def lowerWalkStart (Ssel Svote : Store Node Root)
    (blocksAcceptedByPrevSGFGVote : Finset (Blk Node Root))
    (Xm X1 : Finset (Attestation Node Root)) (r : Nat)
    (processedF : Finset (Blk Node Root)) : Blk Node Root :=
  (deepest ((candidateTreeBackedByPrevSGFGVote Ssel blocksAcceptedByPrevSGFGVote).filter fun B =>
    Svote.walkStartFromFGVotes ⪯ B ∧ B ≠ Svote.walkStartFromFGVotes ∧ G3 Xm X1 r B ∧
    ConflictFree processedF B ∧
    B ∈ candidateTreeBackedByPrevSGFGVote Svote blocksAcceptedByPrevSGFGVote)).getD
    Svote.walkStartFromFGVotes

end

/-! ## Definition 41 — the stable root -/

section
variable [DecidableEq Node] [DecidableEq Root] [Electorate Node]

/-- Definition 43's grade-2 witness, as the receiver validates it: "a set of signed
    preceding-round SG heads of weight at least `m`, each supporting `A_p^r`", with
    validity "positive-only — signatures and the eligible round — and never asserts the
    absence of other messages". Each witness attestation is from round `r − 1` with a
    head at or above `A`, and the signers' weight is a strict majority; the semantic
    acceptance check is the receiver's own raw `G1`, in Definition 41's item 2. -/
def ValidG2Witness (Wit : Finset (Attestation Node Root)) (r : Nat)
    (A : Blk Node Root) : Prop :=
  (∀ a ∈ Wit, a.round + 1 = r ∧ ∃ hB, a.head = some hB ∧ A ⪯ hB) ∧
    StrictMajority (Wit.image fun a => a.validator)

instance (Wit : Finset (Attestation Node Root)) (r : Nat) (A : Blk Node Root) :
    Decidable (ValidG2Witness Wit r A) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- What the vote time fixes, for the rest of the round to read: the stable root, its
    classification for Definition 29's re-derivation — ungraded exactly when the root is
    the vote state's own Simplex selection, the classification Definition 29's opening
    sentence states — and the accepted distinguished proposal, which Definition 42's
    action cases and Definition 47's next-round source read. -/
structure VoteRoundOutcome (Node Root : Type) where
  /-- `R_{u,vote}^r`, the vote-time stable walk-start — the paper's "stable root". -/
  walkStart : Blk Node Root
  /-- Whether the root is graded — `false` exactly when it equals the vote-state
      Simplex selection. -/
  graded : Bool
  /-- The accepted distinguished proposal, `none` on every failure path. -/
  acceptedProposal : Option (RecoveryProposal Node Root)

/-- Definition 41 (`def:stable-root`, lines 1123–1191) — the paper's *stable root*, named
    here for its primary consumer: the round's Goldfish walks start from its output, and
    the SG/FG vote reuses it through Definition 42's admission. `prop` is the recognized
    distinguished proposal after Definition 43's wrapper (timely, unique winner), or
    `none`; `blocksAcceptedByPrevSGFGVote` ages both membership tests (rendering
    decision 2). The three acceptance items, in the definition's own order:

    **The paper's text, verbatim (Definition 41, `def:stable-root`, lines 1123–1191):**

    > The vote-time stable root is derived from the proposal and the grade roots of
    > Definition 40 (`def:grade-root-choice`) by the acceptance guards and fallback
    > below.
    >
    > *Acceptance guards.* A proposal is *timely* at receiver `u` when `u` receives it
    > strictly before its vote time `d_r + Δ`; timeliness and proposer equivocation are
    > decided in `u`'s vote-time view, locally and finally. For a proposal from `u`'s
    > round proposer that is timely at `u`, with no second distinct signed round
    > proposal by the same proposer in `u`'s vote-time view, let `Z_p^r` be its parent
    > and `B_p^r` its block. The receiver accepts the proposal exactly when:
    >
    > 1. either `L_u^r ⪯ A_p^r ⪯ Z_p^r` and `S_{u,vote}^r ⪯ Z_p^r` — and then
    >    `S_{u,vote}^r ⪯ A_p^r` holds automatically, by the first fact of Remark 11
    >    (`rem:stable-root-coherence`) below; or `A_p^r ≺ S_{u,vote}^r ⪯ Z_p^r` with
    >    `S_{u,vote}^r = Σ_{u,vote}^r.F` — the receiver's own newer finalized root
    >    already lies on the proposal path — and `L_u^r ⪯ Z_p^r`;
    > 2. either the raw predicate `G1_u(A_p^r)` holds, `A_p^r` conflicts with no
    >    finalized root whose evidence the receiver has processed — raw counting stays
    >    favorable to equivocation copies, but every grade use respects processed
    >    finality, as Definition 37 (`def:active-grade`) requires — and the proposal has
    >    a valid grade-2 witness, or `A_p^r` is ungraded and equals the receiver's own
    >    vote-time Simplex selection `S_{u,vote}^r` — in particular the genesis block,
    >    justified and finalized by stipulation, exactly when that is the selection. The
    >    proposal may carry justification or finality certificates; the receiver
    >    processes them as ordinary deliveries, and under the activation filter of
    >    Definition 30 (`def:activation-filter`) they enter root selection only at the
    >    next round boundary;
    > 3. the deepest block among `{A_p^r, L_u^r, S_{u,vote}^r}`, denoted
    >    `R_{u,vote}^r`, and the proposal block `B_p^r` are both in the aged tree
    >    `C⁻_u(Σ_{u,vote}^r)`, with the proposal-path exemption of Definition 33
    >    (`def:counting-rule`).
    >
    > The deepest root is used for ordinary Goldfish for the rest of the round;
    > Remark 11 below records why that deepest root is unique.
    >
    > *Failed-proposal fallback.* If the proposal fails these checks — or no proposal is
    > recognized, including the discard-both case — the vote-time stable root is `L_u^r`
    > when `L_u^r = S_{u,vote}^r`, or when the raw predicate `G1_u(L_u^r)` holds,
    > `L_u^r` conflicts with no finalized root whose evidence the receiver has
    > processed, and `L_u^r` is in the aged tree `C⁻_u(Σ_{u,vote}^r)`. In every such
    > case, write `R_{u,vote}^r` for the vote-time stable root so derived; the
    > action-root rule and the fallback SG-head rule consume this notation. Otherwise it
    > is `S_{u,vote}^r`.
    >
    > In plain words, G3 is the receiver's lower bound, G2 is the proposer's witness,
    > and G1 is the receiver's upper acceptance check. A receiver never moves behind its
    > lower root. If its own Simplex selection is a newer root on the honest proposal's
    > path, it starts farther forward on that same path rather than rejecting the
    > proposal. The raw G1 predicate authenticates a proposed root that may now be an
    > ancestor of the receiver's finalized root; that old root is not itself used for
    > fork choice or G0. An ungraded proposer root never moves a receiver at all: it is
    > accepted only when it already equals the receiver's own selection, so every strict
    > forward proposed root needs the graded branch. A root on another branch makes the
    > validator use its ordinary fallback.

    **The same text, in this file's terminology** — root → walk-start, action → SG/FG
    vote:

    > The vote-time stable walk-start is derived from the proposal and the grade
    > walk-starts of Definition 40 by the acceptance guards and fallback below.
    >
    > *Acceptance guards.* A proposal is *timely* at receiver `u` when `u` receives it
    > strictly before its vote time `d_r + Δ`; timeliness and proposer equivocation are
    > decided in `u`'s vote-time view, locally and finally. For a proposal from `u`'s
    > round proposer that is timely at `u`, with no second distinct signed round
    > proposal by the same proposer in `u`'s vote-time view, let `Z_p^r` be its parent
    > and `B_p^r` its block. The receiver accepts the proposal exactly when:
    >
    > 1. either `L_u^r ⪯ A_p^r ⪯ Z_p^r` and `S_{u,vote}^r ⪯ Z_p^r` — and then
    >    `S_{u,vote}^r ⪯ A_p^r` holds automatically, by the first fact of Remark 11
    >    below; or `A_p^r ≺ S_{u,vote}^r ⪯ Z_p^r` with `S_{u,vote}^r = Σ_{u,vote}^r.F`
    >    — the receiver's own newer finalized root already lies on the proposal path —
    >    and `L_u^r ⪯ Z_p^r`;
    > 2. either the raw predicate `G1_u(A_p^r)` holds, `A_p^r` conflicts with no
    >    finalized root whose evidence the receiver has processed — raw counting stays
    >    favorable to equivocation copies, but every grade use respects processed
    >    finality, as Definition 37 requires — and the proposal has a valid grade-2
    >    witness, or `A_p^r` is ungraded and equals the receiver's own vote-time Simplex
    >    selection `S_{u,vote}^r` — in particular the genesis block, justified and
    >    finalized by stipulation, exactly when that is the selection. The proposal may
    >    carry justification or finality certificates; the receiver processes them as
    >    ordinary deliveries, and under the activation filter of Definition 30 they
    >    enter walk-start selection only at the next round boundary;
    > 3. the deepest block among `{A_p^r, L_u^r, S_{u,vote}^r}`, denoted
    >    `R_{u,vote}^r`, and the proposal block `B_p^r` are both in the backed candidate tree
    >    `C⁻_u(Σ_{u,vote}^r)`, with the proposal-path exemption of Definition 33.
    >
    > The deepest walk-start is used for ordinary Goldfish for the rest of the round;
    > Remark 11 below records why that deepest walk-start is unique.
    >
    > *Failed-proposal fallback.* If the proposal fails these checks — or no proposal is
    > recognized, including the discard-both case — the vote-time stable walk-start is
    > `L_u^r` when `L_u^r = S_{u,vote}^r`, or when the raw predicate `G1_u(L_u^r)`
    > holds, `L_u^r` conflicts with no finalized root whose evidence the receiver has
    > processed, and `L_u^r` is in the backed candidate tree `C⁻_u(Σ_{u,vote}^r)`. In every such
    > case, write `R_{u,vote}^r` for the vote-time stable walk-start so derived; the
    > SG/FG-vote walk-start rule and the fallback SG-head rule consume this notation.
    > Otherwise it is `S_{u,vote}^r`.
    >
    > In plain words, G3 is the receiver's lower bound, G2 is the proposer's witness,
    > and G1 is the receiver's upper acceptance check. A receiver never moves behind its
    > lower walk-start. If its own Simplex selection is a newer walk-start on the honest
    > proposal's path, it starts farther forward on that same path rather than rejecting
    > the proposal. The raw G1 predicate authenticates a proposed walk-start that may
    > now be an ancestor of the receiver's finalized root; that old walk-start is not
    > itself used for fork choice or G0. An ungraded proposer walk-start never moves a
    > receiver at all: it is accepted only when it already equals the receiver's own
    > selection, so every strict forward proposed walk-start needs the graded branch. A
    > walk-start on another branch makes the validator use its ordinary fallback.
    1. "either `L_u^r ⪯ A_p^r ⪯ Z_p^r` and `S_{u,vote}^r ⪯ Z_p^r` … or
       `A_p^r ≺ S_{u,vote}^r ⪯ Z_p^r` with `S_{u,vote}^r = Σ_{u,vote}^r.F` … and
       `L_u^r ⪯ Z_p^r`";
    2. "either the raw predicate `G1_u(A_p^r)` holds, `A_p^r` conflicts with no finalized
       root whose evidence the receiver has processed … and the proposal has a valid
       grade-2 witness, or `A_p^r` is ungraded and equals the receiver's own vote-time
       Simplex selection" — the tag binds the branch (Definition 43);
    3. the deepest of `{A_p^r, L_u^r, S_{u,vote}^r}` — one chain by Remark 11
       (`rem:stable-root-coherence`), so
       `chainMax` — and `B_p^r` are both in the backed candidate tree, with the proposal-path
       exemption.

    On acceptance the deepest root is the round's; on any failure, the failed-proposal
    fallback: `L_u^r` when it equals the selection, or when raw `G1_u(L_u^r)` holds,
    `L_u^r` is conflict-free and in the backed candidate tree; otherwise `S_{u,vote}^r`.

    In plain words: G3 fixed the receiver's lower bound, G2 is the proposer's witness,
    G1 is the receiver's upper check, and a receiver never moves behind its lower root
    and never takes an ungraded root it did not already select. -/
def goldfishWalkStart (Svote : Store Node Root)
    (blocksAcceptedByPrevSGFGVote : Finset (Blk Node Root))
    (L : Blk Node Root) (X1 : Finset (Attestation Node Root)) (r : Nat)
    (processedF : Finset (Blk Node Root)) (prop : Option (RecoveryProposal Node Root)) :
    VoteRoundOutcome Node Root :=
  let fallback : VoteRoundOutcome Node Root :=
    if L = Svote.walkStartFromFGVotes then
      { walkStart := L, graded := false, acceptedProposal := none }
    else if G1 X1 r L ∧ ConflictFree processedF L ∧
        L ∈ candidateTreeBackedByPrevSGFGVote Svote blocksAcceptedByPrevSGFGVote then
      { walkStart := L, graded := true, acceptedProposal := none }
    else
      { walkStart := Svote.walkStartFromFGVotes, graded := false, acceptedProposal := none }
  if let some p := prop then
    let item1 :=
      (L ⪯ p.proposedWalkStart ∧ p.proposedWalkStart ⪯ p.parent ∧
        Svote.walkStartFromFGVotes ⪯ p.parent) ∨
      (p.proposedWalkStart ⪯ Svote.walkStartFromFGVotes ∧
        p.proposedWalkStart ≠ Svote.walkStartFromFGVotes ∧
        Svote.walkStartFromFGVotes ⪯ p.parent ∧
        Svote.walkStartFromFGVotes = Svote.F ∧ L ⪯ p.parent)
    let item2 :=
      (p.graded = true ∧ G1 X1 r p.proposedWalkStart ∧ ConflictFree processedF p.proposedWalkStart ∧
        ValidG2Witness p.grade2Witness r p.proposedWalkStart) ∨
      (p.graded = false ∧ p.proposedWalkStart = Svote.walkStartFromFGVotes)
    let Rv := chainMax (chainMax p.proposedWalkStart L) Svote.walkStartFromFGVotes
    let item3 :=
      Rv ∈ candidateTreeBackedByPrevSGFGVoteOrOnProposalPath Svote
        blocksAcceptedByPrevSGFGVote (some p.block) ∧
      p.block ∈ candidateTreeBackedByPrevSGFGVoteOrOnProposalPath Svote
        blocksAcceptedByPrevSGFGVote (some p.block)
    if item1 ∧ item2 ∧ item3 then
      { walkStart := Rv, graded := Rv ≠ Svote.walkStartFromFGVotes,
        acceptedProposal := some p }
    else fallback
  else fallback

end

/-! ## Definition 42 — the action root and its admission -/

section
variable [DecidableEq Node] [DecidableEq Root] [Electorate Node]

/-- Definition 42 (`def:action-root`, lines 1256–1308). `latestGoldfishWalkStart` is
    the round's vote-time stable root — after a mid-round re-derivation, the re-derived root. The cases, in the
    definition's order: proposal-free (no accepted proposal, or the accepted proposal
    block evicted from the action candidate tree while the root ancestry holds) reads no
    proposal block; off-path (the vote-time root or the action-state Simplex root not an
    ancestor of `B_p^r`) defines no action root; otherwise the admission — the root
    stays in `C(Σ_{u,act}^r)` (with `B_p^r`, in the proposal case) and "either equals
    the action-state Simplex root or has raw grade 1 while conflicting with no finalized
    root whose evidence the validator has processed by the action". `none` is the
    definition's abstention: "empty head, empty pair", total either way.

    **The paper's text, verbatim (Definition 42, `def:action-root`, lines 1256–1308):**

    > At `a_r`, the action root is the round's vote-time stable root — the re-derived
    > root, after a mid-round re-derivation. No forward move is ever required: the
    > action-state selection precedes the round's vote-time root and any re-derived
    > root, by Lemma 35 (`lem:no-forward-move`). The action evaluates the following
    > cases in order; the first that applies governs.
    >
    > 1. *Proposal-free.* If no unique proposal was accepted — a failed proposal, no
    >    timely proposal, or the discard-both case — or an accepted proposal block has
    >    left the action candidate tree while the root ancestry holds — a mid-round rise
    >    evicted the proposal — the action reads no proposal block at all: the ancestry
    >    condition of case 2 is vacuous, the validator sets
    >    `R_{u,act}^r = R_{u,vote}^r`, and only case 3's membership and admission tests
    >    apply. A superseded proposal costs its proposer the round's context, never the
    >    validator its outputs.
    > 2. *Off-path root.* If the vote-time root or `S_{u,act}^r` is not an ancestor of
    >    `B_p^r` — in particular when a re-derivation moved the vote-time root off the
    >    proposal's chain — no action root is defined and the validator emits no SG head
    >    or current-height pair.
    > 3. *Admission.* Otherwise the receiver uses the action root for SG and FG exactly
    >    when `B_p^r` — in the proposal case — and `R_{u,act}^r` remain in
    >    `C(Σ_{u,act}^r)`, and the action root either equals the action-state Simplex
    >    root or has raw grade 1 while conflicting with no finalized root whose evidence
    >    the validator has processed by the action — finality evidence processed after
    >    the vote thus withdraws a root from SG/FG use even when no slot boundary
    >    remains to re-derive it — and the validator abstains otherwise. When the
    >    vote-time root is an ungraded fallback equal to the round's justification
    >    selection and the action state has switched to the finalized root, this same
    >    admission decides: retention exactly when the root stays in the action
    >    candidate tree with raw grade 1 free of processed-finality conflict. Either
    >    outcome is a deterministic function of the deadline view, and the switch
    >    requires a mid-round maximum move, one of the separately handled cases.
    >
    > On failure of any case, every output of the action is fixed — empty head, empty
    > pair — so the action is total with or without a proposal. The vote-time stable
    > root remains fixed for ordinary Goldfish, subject only to the ungraded-fallback
    > re-derivation of Definition 29 (`def:rederivation`); the SG/FG action root is that
    > same root when the admission accepts it.
    >
    > In plain words, the action first decides whether a proposal is in play, then
    > whether the roots are on its chain, then whether the root is admissible; a
    > validator abstains only on a real conflict, never merely because a proposal was
    > superseded.

    **The same text, in this file's terminology** — root → walk-start, action → SG/FG
    vote, action state → filtered store at the SG/FG vote:

    > At `a_r`, the SG/FG-vote walk-start is the round's vote-time stable walk-start —
    > the re-derived walk-start, after a mid-round re-derivation. No forward move is
    > ever required: the filtered store's selection at the SG/FG vote precedes the
    > round's vote-time walk-start and any re-derived walk-start, by Lemma 35. The
    > SG/FG vote evaluates the following cases in order; the first that applies governs.
    >
    > 1. *Proposal-free.* If no unique proposal was accepted — a failed proposal, no
    >    timely proposal, or the discard-both case — or an accepted proposal block has
    >    left the candidate tree at the SG/FG vote while the walk-start ancestry holds —
    >    a mid-round rise evicted the proposal — the SG/FG vote reads no proposal block
    >    at all: the ancestry condition of case 2 is vacuous, the validator sets
    >    `R_{u,act}^r = R_{u,vote}^r`, and only case 3's membership and admission tests
    >    apply. A superseded proposal costs its proposer the round's context, never the
    >    validator its outputs.
    > 2. *Off-path walk-start.* If the vote-time walk-start or `S_{u,act}^r` is not an
    >    ancestor of `B_p^r` — in particular when a re-derivation moved the vote-time
    >    walk-start off the proposal's chain — no SG/FG-vote walk-start is defined and
    >    the validator emits no SG head or current-height pair.
    > 3. *Admission.* Otherwise the receiver uses the SG/FG-vote walk-start for SG and
    >    FG exactly when `B_p^r` — in the proposal case — and `R_{u,act}^r` remain in
    >    `C(Σ_{u,act}^r)`, and the SG/FG-vote walk-start either equals the filtered
    >    store's walk-start from FG votes or has raw grade 1 while conflicting with no
    >    finalized root whose evidence the validator has processed by the SG/FG vote —
    >    finality evidence processed after the vote thus withdraws a walk-start from
    >    SG/FG use even when no slot boundary remains to re-derive it — and the
    >    validator abstains otherwise. When the vote-time walk-start is an ungraded
    >    fallback equal to the round's justification selection and the filtered store
    >    has switched to the finalized root, this same admission decides: retention
    >    exactly when the walk-start stays in the candidate tree at the SG/FG vote with
    >    raw grade 1 free of processed-finality conflict. Either outcome is a
    >    deterministic function of the deadline view, and the switch requires a
    >    mid-round maximum move, one of the separately handled cases.
    >
    > On failure of any case, every output of the SG/FG vote is fixed — empty head,
    > empty pair — so the SG/FG vote is total with or without a proposal. The vote-time
    > stable walk-start remains fixed for ordinary Goldfish, subject only to the
    > ungraded-fallback re-derivation of Definition 29; the SG/FG-vote walk-start is
    > that same walk-start when the admission accepts it.
    >
    > In plain words, the SG/FG vote first decides whether a proposal is in play, then
    > whether the walk-starts are on its chain, then whether the walk-start is
    > admissible; a validator abstains only on a real conflict, never merely because a
    > proposal was superseded.
    In plain words: the action first decides whether a proposal is in play, then whether
    the roots are on its chain, then whether the root is admissible. -/
def sgfgVoteWalkStart
    -- `Σ_{u,act}^r`: the activation-filtered store at the SG/FG vote
    (filteredStoreAtSGFGVote : Store Node Root)
    -- the round's vote-time stable root — after a mid-round re-derivation, the re-derived root
    (latestGoldfishWalkStart : Blk Node Root)
    -- the round's accepted distinguished proposal, `none` on every failure path
    (acceptedProposal : Option (RecoveryProposal Node Root))
    -- `X_u^1`, the grade view raw grade 1 is tested in
    (attsAtRoundStartPlusΔ : Finset (Attestation Node Root)) (r : Nat)
    -- finalized roots whose evidence was processed by this reading
    (processedFinalizedAtSGFGVote : Finset (Blk Node Root)) : Option (Blk Node Root) :=
  let admittedWalkStart : Option (Blk Node Root) :=
    if latestGoldfishWalkStart ∈ candidateTree filteredStoreAtSGFGVote ∧
        (latestGoldfishWalkStart = filteredStoreAtSGFGVote.walkStartFromFGVotes ∨
          (G1 attsAtRoundStartPlusΔ r latestGoldfishWalkStart ∧
            ConflictFree processedFinalizedAtSGFGVote latestGoldfishWalkStart)) then
      some latestGoldfishWalkStart
    else none
  if let some p := acceptedProposal then
    if latestGoldfishWalkStart ⪯ p.block ∧
      filteredStoreAtSGFGVote.walkStartFromFGVotes ⪯ p.block then
      if p.block ∈ candidateTree filteredStoreAtSGFGVote then
        admittedWalkStart                           -- case 3, with the proposal in play
      else admittedWalkStart                        -- case 1: evicted proposal, root ancestry holds
    else none                                  -- case 2: off-path root
  else admittedWalkStart                            -- case 1: no accepted proposal

end

/-! ## Definition 46 — the strong G0 check, the official confirmation, and the SG head -/

section
variable [DecidableEq Node] [DecidableEq Root] [Electorate Node] [BlockHash Node Root]

/-- Definition 46 (`def:official-confirmation`, lines 1635–1706)'s veto: `Q` is veto-free
    "when no block conflicting with `Q` that descends from the action state's finalized
    root has a grade 0 in `X_u^2` that is active under Definition 37 evaluated at the
    grade-0 freeze: the activity filter counts exactly the finalized evidence the
    validator had processed by `d_r + 2Δ`". `pfFreeze` is that freeze-time evidence,
    snapshotted by the wiring. -/
def VetoFree (Sact : Store Node Root) (X2 : Finset (Attestation Node Root)) (r : Nat)
    (pfFreeze : Finset (Blk Node Root)) (Q : Blk Node Root) : Prop :=
  ∀ B ∈ Sact.T, Sact.F ⪯ B → ¬ Compatible B Q →
    ¬ ActiveGrade (G0 X2 r B) Sact pfFreeze B

instance (Sact : Store Node Root) (X2 : Finset (Attestation Node Root)) (r : Nat)
    (pfFreeze : Finset (Blk Node Root)) (Q : Blk Node Root) :
    Decidable (VetoFree Sact X2 r pfFreeze Q) :=
  inferInstanceAs (Decidable (∀ B ∈ Sact.T, Sact.F ⪯ B → ¬ Compatible B Q →
    ¬ ActiveGrade (G0 X2 r B) Sact pfFreeze B))

/-- What the action's head production fixes: the SG head, and the block the
    current-height rule checks its targets against — the paper's phrase for the latter
    is "the confirmation gate for the current-height pair"; in plain words, it is the
    deepest official confirmation `Q_u^r`, the ceiling on what the validator will vouch
    for, and it is empty whenever no official confirmation exists, even when a fallback
    head is still published. -/
structure ActionOutputs (Node Root : Type) where
  /-- The honest SG head: `Q_u^r` when nonempty, else the fallback `R_u^r`, else `⊥`. -/
  head : Option (Blk Node Root)
  /-- `Q_u^r`, the deepest official confirmation — Definition 48's `C_i`. -/
  C : Option (Blk Node Root)

/-- Definition 46 (`def:official-confirmation`, lines 1635–1706). Two abstentions come
    first: a failed action-state admission (`admittedWalkStart = none`, Definition 42) or the fixed
    stable root absent from the action candidate tree — the walk's own precondition —
    "takes the empty SG-head and current-height branches directly". Otherwise:
    `C` is the deepest available-confirmed block of the first slot's evaluation
    (Definition 39, over the support view `Vm` and evaluation view `Vp`); the action
    head `G_u^r` is the recovery walk from the fixed stable root within the action
    state's candidate tree, "counting the evaluated first slot's votes"; an official
    confirmation is veto-free, conflicts with no finalized root whose evidence was
    processed by the action, and satisfies `S_act ⪯ Q ⪯ C` and `Q ⪯ G`; `Q_u^r` is the
    deepest one. "When `Q_u^r ≠ ⊥`, the honest SG head is `Q_u^r`"; otherwise the head
    is the fallback `R_u^r` — "the deepest veto-free block between `S_{u,act}^r` and the
    round's action root" that is conflict-free — with an empty current-height side
    (`C := ⊥`).

    In plain words: the strong G0 check first looks for a confirmed block no active
    grade-0 majority vetoes; without one, the validator may still publish a veto-free
    prefix of its fixed root, but it cannot sign a current-height choice. -/
def officialConfirmation [Omega Node Root] (Sact : Store Node Root)
    (latestGoldfishWalkStart : Blk Node Root) (admittedWalkStart : Option (Blk Node Root))
    (committee : Finset Node)
    (s : Time) (Vm Vp : Finset (GoldfishVote Node Root))
    (X2 : Finset (Attestation Node Root)) (r : Nat)
    (pfFreeze processedF : Finset (Blk Node Root)) : ActionOutputs Node Root :=
  if admittedWalkStart = none ∨ latestGoldfishWalkStart ∉ candidateTree Sact then
    { head := ⊥, C := ⊥ }
  else
    let Cav := deepest (Sact.T.filter fun B => AvailableConfirmed Vm Vp s committee B)
    let G := ghostWalk (Vp.filter fun v => v.slot = s) (candidateTree Sact)
      (candidateTree Sact).card latestGoldfishWalkStart
    let officials :=
      match Cav with
      | some c =>
          Sact.T.filter fun Q =>
            VetoFree Sact X2 r pfFreeze Q ∧ ConflictFree processedF Q ∧
            Sact.walkStartFromFGVotes ⪯ Q ∧ Q ⪯ c ∧ Q ⪯ G
      | none => ∅
    match deepest officials with
    | some Q => { head := some Q, C := some Q }
    | none =>
        let fb :=
          match admittedWalkStart with
          | some Ra =>
              deepest (Sact.T.filter fun B =>
                Sact.walkStartFromFGVotes ⪯ B ∧ B ⪯ Ra ∧ VetoFree Sact X2 r pfFreeze B ∧
                ConflictFree processedF B)
          | none => ⊥   -- unreachable under the outer test; kept for totality
        { head := fb, C := ⊥ }

end

/-! ## Definition 47 in full, and the store-discharged finality inputs -/

section
variable [DecidableEq Node] [DecidableEq Root] [Electorate Node] [Params]

/-- Rendering decision 6, first half: `h_F` for Definition 49, read off the store. Every
    recorded chain state carries `(F, h_F)` (Definition 13, `def:chain-state`), and every
    state that records `S.F` as its greatest finalized block records the same height, so
    the join over them is that height — `0` before any state records it, matching the
    genesis pair `(genesis, 0)`. -/
def Store.h_F (S : Store Node Root) : Nat :=
  S.T.sup fun B => ((S.σ B).map fun st => if st.F = S.F then st.h_F else 0).getD 0

/-- Rendering decision 6, second half: Definition 49's "it knows the justification
    certificate `JC(h_j, J)`" (Definition 21, `def:certificates`, lines 945–967: the
    target quorum, its valid inclusions on one chain, and the height event that set
    `(J, h_j) = (T, h)`). A store holding a recorded state that replayed that height
    event holds all three pieces on that state's own chain, so the knowledge test is:
    some recorded state carries the store's justified pair. -/
def Store.hasJC (S : Store Node Root) : Bool :=
  decide (∃ B ∈ S.T, (S.σ B).any fun st => st.J = S.J ∧ st.h_j = S.h_j)

/-- Definition 47 (`def:ordinary-current-target`, lines 1814–1869), both branches, over
    an explicit confirmation and source. `deepestConfirmation` is the action's deepest
    official confirmation `Q_i^r` (Definition 46); `sourceProposal` is "the unique
    distinguished proposal
    from round `r − 1`, whose SG batch this action grades", or `none` when that round
    recognized none. With `Q_i^r` empty, no current-height pair (`none` — Definition 48
    then emits empty). Otherwise `σ̄_i = σ_a[Q_i^r]`, the confirmation's finality action
    state — `process_slots` to the action's reading, per Definition 20
    (`def:finality-action-state`), the same closure `ordinaryContext` uses. The source
    branch: "If `B ⪯ Q_i^r` and `σ_a[B].h = σ̄_i.h`, validator `i` uses `Y_i = B` and
    `σ_i = σ_a[B]` … Otherwise it uses `Y_i = Q_i^r` and `σ_i = σ̄_i`." Then
    `k_i = σ_i.h`, `ν_i = σ_i.nj`, and `T_i = σ_i.T_{k_i}`, with the fallback of
    lines 1858–1860: `Y_i` itself when that field is empty and
    `Y_i.slot ≥ σ_i.s_{k_i}`, else `⊥` — the `else` arm returns the field, `⊥` in
    exactly the remaining case.

    In plain words: a validator that confirms the graded round's proposal signs that
    proposal's height, target and nonjustifiable flag even when its own tip has moved,
    and one that does not falls back to its confirmed block's own state. The branch
    condition keeps `σ_a[C_i].h = k` in both cases, which is why the wiring passes
    `hC = k` to `heightVote`. -/
def recoveryContext (S : Store Node Root) (t : Time)
    (officialConfirmation sourceProposal : Option (Blk Node Root)) :
    Option (VoteContext Node Root) :=
  if let some Q := officialConfirmation then
    if let some σQ := S.σ Q then
      let σbar := processSlots σQ t
      let (Y, σi) :=
        match sourceProposal with
        | some B =>
            match S.σ B with
            | some σB =>
                let σsrc := processSlots σB t
                if B ⪯ Q ∧ σsrc.h = σbar.h then (B, σsrc) else (Q, σbar)
            | none => (Q, σbar)
        | none => (Q, σbar)
      some { C := Q, k := σi.h, ν := σi.nj,
             T := if σi.T_h = ⊥ ∧ Y.slot ≥ σi.s_h then some Y else σi.T_h }
    else none
  else none

end

/-! ## The assembled recovery action — Definition 50 over the machinery -/

section
variable [DecidableEq Node] [DecidableEq Root] [Electorate Node] [Params]
  [BlockHash Node Root]

/-- One recovery action, Figure 5 (`alg:recovery-action`, lines 2081–2125),
    steps 15–21: derive the
    action root's admission (Definition 42), the official confirmation and SG head
    (Definition 46), and the current-height context (Definition 47), then sign the one
    combined attestation of Definition 50 — `fgVote`, finality first, over the action
    state's `(J, h_j)`, `(F, h_F)` and certificate knowledge, all read off
    `filteredStoreAtSGFGVote` (rendering decision 6). The inputs are the round's records, in the
    order the wiring holds them, each said above its binder. -/
def castSGFGVote [Omega Node Root]
    -- the acting validator, the round, and the reading — the wiring calls this at `a_r`
    (i : Node) (r : Nat) (t : Time)
    -- `Σ_{u,act}^r`, the action state: the store under the activation filter at this reading
    (filteredStoreAtSGFGVote : Store Node Root)
    -- the round's stable root (Definition 41), as the records hold it
    (latestGoldfishWalkStart : Blk Node Root)
    -- the round's accepted distinguished proposal, `none` on every failure path
    (acceptedProposal : Option (RecoveryProposal Node Root))
    -- Definition 47's source proposal, from round `r − 1`
    (sourceProposal : Option (Blk Node Root))
    -- the evaluated first slot's committee, and that slot's vote phase `d_r + Δ`,
    -- which the TSQ views and the head walk both key on
    (committee : Finset Node) (firstSlotVoteTime : Time)
    -- `V⁻` and `V⁺` (Definition 38): the support-freeze view and the action-time view
    (votesAtSupportFreeze votesAtSGFGVote : Finset (GoldfishVote Node Root))
    -- the two late grade views, as `RoundState` holds them
    (attsAtRoundStartPlusΔ attsAtRoundStartPlus2Δ : Finset (Attestation Node Root))
    -- finalized roots whose evidence was processed by the grade-0 freeze (Definition 46's
    -- veto counts these) and by this reading
    (processedFinalizedAtFreeze processedFinalizedAtSGFGVote : Finset (Blk Node Root))
    -- `H_i`, Definition 12's durable signing history
    (history : SigningHistory Node Root) :
    Attestation Node Root × SigningHistory Node Root :=
  let admittedWalkStart := sgfgVoteWalkStart filteredStoreAtSGFGVote latestGoldfishWalkStart
    acceptedProposal
    attsAtRoundStartPlusΔ r processedFinalizedAtSGFGVote
  let outs := officialConfirmation filteredStoreAtSGFGVote latestGoldfishWalkStart
    admittedWalkStart committee
    firstSlotVoteTime votesAtSupportFreeze votesAtSGFGVote attsAtRoundStartPlus2Δ r
    processedFinalizedAtFreeze processedFinalizedAtSGFGVote
  match recoveryContext filteredStoreAtSGFGVote t outs.C sourceProposal with
  | some ctx =>
      fgVote
        (i := i) (r := r)
        (head := outs.head)      -- Definition 46's head: `Q_u^r`, or the fallback
        (J := filteredStoreAtSGFGVote.J) (h_j := filteredStoreAtSGFGVote.h_j)
        (F := filteredStoreAtSGFGVote.F)
        (h_F := filteredStoreAtSGFGVote.h_F) -- read off the action state — rendering decision 6
        (hasJC := filteredStoreAtSGFGVote.hasJC)    -- likewise
        (C := some ctx.C)        -- the confirmation `Q_i^r`, Definition 48's ceiling
        (k := ctx.k) (T := ctx.T) (ν := ctx.ν)
        (hC := ctx.k)            -- `σ_a[C_i].h = k` in both Definition 47 branches
        (H := history)
  | none =>
      fgVote
        (i := i) (r := r)
        (head := outs.head)      -- a fallback head may accompany the empty pair
        (J := filteredStoreAtSGFGVote.J) (h_j := filteredStoreAtSGFGVote.h_j)
        (F := filteredStoreAtSGFGVote.F)
        (h_F := filteredStoreAtSGFGVote.h_F) (hasJC := filteredStoreAtSGFGVote.hasJC)
        (C := ⊥)                 -- no official confirmation: the pair stays empty
        (k := 0) (T := ⊥) (ν := false) (hC := 0)   -- unread once `C = ⊥`
        (H := history)           -- the finality rule still runs (Definition 46's last line)

end

end Decoupled
