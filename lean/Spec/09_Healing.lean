import Spec.«03_AvailableConfirmation»
import Spec.«05_SGDuty»
import Spec.«07_FGStore»
import Spec.«08_FinalityVote»
import Spec.Defs.Nondet

/-!
# Healing: round grades, round roots, and the assembled tick

Round `r` grades the heads of the round-`(r−1)` SG votes, read from the stored votes
themselves, and uses the grades to fix one root per round: the proposer offers a root
in its opening block, each receiver checks it, and the accepted or fallback root anchors
the round's Goldfish walks and its SG and FG outputs.

The file is in three parts. First the support scores read from the stored votes, with the
grades defined over them. Then the round-root functions — proposal root, lower root, SG root,
and the round's root in both readings, the walk-root-then-action-root pair and the one-step
`get_sg_majority_start`. Then the layer as assembled: the tree the fork choice descends, the
single `GoldfishWalk` instance that makes it the protocol's, and `on_tick`.

## This is the last layer, so its readings are the protocol's

`Fig9.goldfishWalk` holds the tree every walk of the assembled protocol descends: rooted at
the SG fork choice run from the round's own root, over the height-filtered blocks with the
grade-0 blocks dropped. The `GoldfishWalk` instance below it is the only one in the spec, so
`get_head` (`01_GoldfishWalk.lean`), the duties that call it, and available confirmation
(`03_AvailableConfirmation.lean`) all run this reading without naming it. `on_tick` here is
the protocol's, and it is where the round's attestation is broadcast.

## What is not yet here

`Σ.root_proposal[r]` is written by nothing. Two figures would fill it: the proposer's
`get_proposal_root` call, which puts a root in its opening block, and the `process_block`
line that registers the first round-`r` opening block's root. Until they land,
`get_sg_root` always takes its fallback branch, since it reads that field to find a proposal
to accept.

## The tree the rules read

Every root function selects within `Fig7.getFilteredBlockTree`, the height-filtered blocks of
`07_FGStore.lean`, and falls back to `fork_choice_root(Σ)`. It names that reading rather than
going through the class, because the class's instance is this layer's own and would answer
with the grade-0 veto applied — a filter on what a walk may step onto, not on what may be a
round's root.

## "The deepest block" is a pick

Support counts descendants, so every grade is inherited by ancestors; and two conflicting
blocks cannot both hold a direct majority, so the blocks with grade 2, and those with
grade 3, lie on one chain — where "the deepest block" is the single `⪯`-maximal one.
That is a fact about the scores, not of the types, so the routines pick from `deepest G`,
the `⪯`-maximal blocks: on the sets the protocol builds the pick is from a singleton, and
nothing here assumes it.

## Extract

Healing gives each round one agreed root. Round `r` grades the heads of the
round-`(r−1)` SG votes against its grade instants `Γ_j = t_r + jΔ`, `j ∈ {−1, 0, 1, 2}`
(`t_r` the proposal time of the round's opening slot). The stored votes carry their
processing times, and only votes whose head is a block are stored; a validator has
equivocated as of an instant when two of its distinct votes were both processed before
it. The scores compare stored processing times against past instants, so a grade
evaluated at any time after its instants gives one fixed answer. Grades are signed
evidence.

## Extract — Definition (Support and grades)

Fix round `r`, block `B`, and `j ∈ {−1, 0, 1, 2}`. `H_j(B)` contains the validators
with a stored round-`(r−1)` vote processed before `Γ_j` whose head supports `B` (the
head descends from `B`), and `E_j` those with two distinct stored round-`(r−1)` votes
both processed before that instant. For round `0` there are no round-`(−1)` votes, so
every score is `0`. The support scores are

`S_j(B) = w(H_j(B) \ E_j)`, `S̄_j(B) = w(H_j(B) ∪ E_j)`, `S_{−1,1}(B) = w(H_{−1}(B) \ E_1)`

— `Γ_{−1}` supplies the head cutoff in `S_{−1,1}`; its equivocation cutoff is `Γ_1`. The
grades are

`G3(B) ⇔ S_{−1,1}(B) ≥ m`, `G2(B) ⇔ S_0(B) ≥ m`, `G1(B) ⇔ S̄_1(B) ≥ m`, `G0(B) ⇔ S̄_2(B) ≥ m`.

Support counts descendants, so every grade is inherited by ancestors; and two conflicting
blocks cannot both hold direct support `m`, so the blocks with grade 2, and those with
grade 3, lie on one chain.

## Extract

The round-root functions read the stored round entries and compute grades as needed. At
`t_r`, the round's opening proposer sets its opening block's proposal-root field to
`get_proposal_root(Σ, r)`: the deepest block in the filtered tree with grade 2, or the
current fork-choice root when no such block exists. `Σ.root_proposal[r]` is the proposal
root of the first round-`r` opening block processed — later opening blocks of the round
are ignored — and it is `⊥` while no opening block has arrived.

At the opening slot's vote time, a validator derives its round's SG root,
`get_sg_root(Σ, r)`, and stores it in `Σ.sg_root[r]`: with `R_low` the deepest block in
the filtered tree with grade 3 strictly descending from the fork-choice root (or that
root itself when there is none), the validator accepts the proposed root `R_prop` exactly
when `R_low ⪯ R_prop`, `R_prop` is in the filtered tree, and `G1(R_prop)`; otherwise the
SG root is `R_low`.

Each Goldfish fork choice then starts from `get_walk_root(Σ, r)`: the stored SG root
when the fork-choice root precedes it, else the fork-choice root. At `a_r`, the validator
derives the root anchoring its SG and FG outputs, `get_action_root(Σ, r)`: the walk root
when it is in the filtered tree and either equals the fork-choice root or has grade 1;
otherwise the fork-choice root itself — a validator's own selection needs no external
backing, while a round root adopted from others must still be viable and majority-backed
at signing time.

`get_round_root(Σ, r)` reads the round's root in one step, and is what the rest of the
protocol uses: the stored SG root, unless it is absent, does not descend from the
fork-choice root, or has left the filtered tree — in each of those cases the fork-choice
root itself. It differs from the pair above in two ways. The grade test is dropped, being
implied: a stored SG root was either accepted on grade 1 or is a grade-3 block, and grade
3 implies grade 1. And viability constrains the walk's anchor as well as the signed
outputs, so no walk starts from a block whose branch has died back.

-/

set_option autoImplicit false

namespace DC

variable {Validator : Type} [Roots] [DecidableEq Validator] [Electorate Validator] [Committees Validator] [RootComputation Validator] [Params]

open Params

/-- Validator `i` has a stored round-`k` SG vote, processed before instant `c`, whose
    head descends from `B`. The stored head is a `Block` — an empty-headed vote is never
    stored — so the ancestry test reads it directly. -/
def Store.headSupports (S : Store Validator) (k : Int) (i : Validator) (c : Int)
    (B : Block Validator) : Prop :=
  ∃ vt ∈ S.sgVotes[k], vt.vote.validator = i ∧ vt.time < c ∧ B ⪯ vt.vote.head

instance (S : Store Validator) (k : Int) (i : Validator) (c : Int) (B : Block Validator) :
    Decidable (S.headSupports k i c B) := inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- Validator `i` has equivocated in round `k` as of instant `c`: two distinct stored SG
    votes of its, both processed before `c` — the detection time is the later of the two
    stamps, so both must clear the cutoff. -/
def Store.equivBefore (S : Store Validator) (k : Int) (i : Validator) (c : Int) : Prop :=
  ∃ a ∈ S.sgVotes[k], ∃ b ∈ S.sgVotes[k],
    a.vote.validator = i ∧ b.vote.validator = i ∧ a.vote ≠ b.vote ∧
    a.time < c ∧ b.time < c

instance (S : Store Validator) (k : Int) (i : Validator) (c : Int) :
    Decidable (S.equivBefore k i c) := inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-! ## Figure `support_scores(Σ, r, j, B)` -/
/-- The pair `(S_j(B), S̄_j(B))` of round-`r` support scores
    for `B`, read from the round-`(r−1)` entries against the grade instant `Γ_j`.

    `H_j(B)` is the set of validators with a stored round-`(r−1)` vote processed before
    `Γ_j` whose head supports `B` — the head descends from `B`; `E_j` the set of those
    the stored votes catch equivocating before that instant. Then
    `S_j(B) = w(H_j(B) \ E_j)`, the
    support net of equivocators, and `S̄_j(B) = w(H_j(B) ∪ E_j)`, the support together
    with every equivocator. For round `0` the round-`(−1)` entries are empty, so every
    score is `0`. -/
def Store.supportScores (S : Store Validator) (r : Nat) (j : Int) (B : Block Validator) :
    Nat × Nat :=
  let Hj := {i ∈ Electorate.V (Validator := Validator) | S.headSupports (r - 1) i (Γ j r) B}
  let Ej := {i ∈ Electorate.V (Validator := Validator) | S.equivBefore (r - 1) i (Γ j r)}
  (w(Hj \ Ej), w(Hj ∪ Ej))  -- S_j(B), S̄_j(B)

/-! ## Figure `two_view_support(Σ, r, B)` -/
/-- `S_{−1,1}(B)`, the two-view score — support counted with
    the head cutoff at `Γ_{−1}` and the equivocation cutoff at `Γ_1`: the validators
    with a stored round-`(r−1)` vote processed before `Γ_{−1}` whose head supports `B`,
    net of those the stored votes catch equivocating before `Γ_1`. -/
def Store.twoViewSupport (S : Store Validator) (r : Nat) (B : Block Validator) : Nat :=
  let Hm := {i ∈ Electorate.V (Validator := Validator) | S.headSupports (r - 1) i (Γ (-1) r) B}  -- H_{−1}(B)
  let E1 := {i ∈ Electorate.V (Validator := Validator) | S.equivBefore (r - 1) i (Γ 1 r)}  -- E_1
  w(Hm \ E1)  -- S_{−1,1}(B)

/-- `G3(B)`: the two-view score reaches the majority threshold, `S_{−1,1}(B) ≥ m`. -/
def Store.G3 (S : Store Validator) (r : Nat) (B : Block Validator) : Prop :=
  S.twoViewSupport r B ≥ m Validator

instance (S : Store Validator) (r : Nat) (B : Block Validator) : Decidable (S.G3 r B) :=
  inferInstanceAs (Decidable (_ ≥ _))

/-- `G2(B)`: the direct score at the proposal instant reaches the majority threshold,
    `S_0(B) ≥ m` — the first component of `support_scores` at `j = 0`. -/
def Store.G2 (S : Store Validator) (r : Nat) (B : Block Validator) : Prop :=
  (S.supportScores r 0 B).1 ≥ m Validator

instance (S : Store Validator) (r : Nat) (B : Block Validator) : Decidable (S.G2 r B) :=
  inferInstanceAs (Decidable (_ ≥ _))

/-- `G1(B)`: the equivocator-inclusive score at the vote instant reaches the majority
    threshold, `S̄_1(B) ≥ m` — the second component of `support_scores` at `j = 1`. -/
def Store.G1 (S : Store Validator) (r : Nat) (B : Block Validator) : Prop :=
  (S.supportScores r 1 B).2 ≥ m Validator

instance (S : Store Validator) (r : Nat) (B : Block Validator) : Decidable (S.G1 r B) :=
  inferInstanceAs (Decidable (_ ≥ _))

/-- `G0(B)`: the equivocator-inclusive score at the support freeze reaches the majority
    threshold, `S̄_2(B) ≥ m` — the second component of `support_scores` at `j = 2`. No
    routine in this file reads it. -/
def Store.G0 (S : Store Validator) (r : Nat) (B : Block Validator) : Prop :=
  (S.supportScores r 2 B).2 ≥ m Validator

instance (S : Store Validator) (r : Nat) (B : Block Validator) : Decidable (S.G0 r B) :=
  inferInstanceAs (Decidable (_ ≥ _))

/-- The `⪯`-maximal blocks of `G`: those with no strict descendant in `G`. The round-root
    functions pick "the deepest block" from grade sets, which lie on one chain (the module
    header says why), so there the pick is from this set's single element; the pick stays
    honest when the set is not a chain. -/
def deepest (G : Finset (Block Validator)) : Finset (Block Validator) :=
  {B ∈ G | ∀ C ∈ G, ¬ B ≺ C}

/-! ## Figure `get_proposal_root(Σ, r)` -/
/-- The root the round's opening proposer offers in its opening
    block — the deepest block in the filtered tree with grade 2, or the fork-choice root
    when no such block exists. -/
def Store.getProposalRoot (S : Store Validator) (r : Nat) : NDRE (Block Validator) := do
  -- the proposer, at t_r
  let G := {B ∈ (← Fig7.getFilteredBlockTree S) | S.G2 r B}
  if G ≠ ∅ then
    let D ←ᵖ deepest G
    return D
  return S.forkChoiceRoot

/-! ## Figure `get_lower_root(Σ, r)` -/
/-- The receiver's fallback against the proposal — the deepest
    block in the filtered tree with grade 3 strictly descending from the fork-choice root,
    or the fork-choice root itself when there is none. -/
def Store.getLowerRoot (S : Store Validator) (r : Nat) : NDRE (Option (Block Validator)) := do
  let G := {B ∈ (← Fig7.getFilteredBlockTree S) | S.G3 r B ∧ S.forkChoiceRoot ≺ B}
  if G ≠ ∅ then
    let D ←ᵖ deepest G
    return D
  return ⊥

/-! ## Figure `get_sg_root(Σ, r)` -/
/-- The round's SG root, derived at the opening slot's vote time. The
    proposed root `R_prop` is accepted exactly when the lower root precedes it, it is in
    the filtered tree, and it holds grade 1; otherwise, and while no opening block has
    registered a proposal, the SG root is the lower root. -/
def Store.getSGRoot (S : Store Validator) (r : Nat) : NDRE (Option (Block Validator)) := do
  let Rlow ← S.getLowerRoot r
  if S.rootProposal[r] = ⊥ then
    return Rlow

  if Rlow = ⊥ then
    return ⊥

  let Rprop ← S.rootProposal[r]
  if (← Rlow) ⪯ Rprop ∧ Rprop ∈ (← Fig7.getFilteredBlockTree S) ∧ S.G1 r Rprop then
    return Rprop
  return Rlow

/-! ## Figure `get_walk_root(Σ, r)` -/
/-- Where a Goldfish walk of round `r` starts — the stored SG root when the fork-choice
    root precedes it, else the fork-choice root. It asks nothing of viability: a walk may
    start from a block outside the filtered tree, the tree constraining the walk's
    children rather than its anchor.

    `Σ.sg_root[r]` is read by the raising extraction, behind the `= ⊥` test. -/
def Store.getWalkRoot (S : Store Validator) (r : Nat) : DRE (Block Validator) := do
  let FCR := S.forkChoiceRoot
  if S.sgRoot[r] = ⊥ then
    return FCR
  let sgRoot ← S.sgRoot[r]
  if ¬ (FCR ⪯ sgRoot) then
    return FCR
  return sgRoot

/-! ## Figure `get_action_root(Σ, r)` -/
/-- The root anchoring the round's SG and FG outputs, derived at `a_r` — the walk root
    when it is in the filtered tree and either equals the fork-choice root or holds
    grade 1; otherwise the fork-choice root itself. A validator's own selection needs no
    external backing, while a round root adopted from others must still be viable and
    majority-backed at signing time. -/
def Store.getActionRoot (S : Store Validator) (r : Nat) : DRE (Block Validator) := do
  -- at a_r
  let FCR := S.forkChoiceRoot
  let R ← S.getWalkRoot r
  if R ∈ (← Fig7.getFilteredBlockTree S) ∧ (R = FCR ∨ S.G1 r R) then
    return R
  return FCR

/-! ## Figure `get_sg_majority_start(Σ, r)` -/
/-- Where round `r`'s SG walk starts, in one step: the stored SG root, unless it is absent,
    does not descend from the fork-choice root, or is no longer in the filtered tree — in each
    of which cases the fork-choice root itself. It is the round's root, so it is also what the
    round's SG and FG outputs anchor on.

    The two-step reading above and this one part company in two places. No grade is tested
    here: a stored SG root is either a proposal `get_sg_root` accepted on grade 1 or a
    grade-3 block it fell back to, and grade 3 implies grade 1, so `get_action_root`'s
    grade test restates what already holds. And viability constrains the walk's anchor
    here, where `get_walk_root` leaves it free — so a walk in this reading never starts
    from a block whose branch has died back, and never returns a head nothing can build
    on.

    `Σ.sg_root[r]` is read by the raising extraction, behind the `= ⊥` test. -/
def Store.getSGMajorityStart (S : Store Validator) (r : Nat) : DRE (Block Validator) := do
  let FCR := S.forkChoiceRoot
  if S.sgRoot[r] = ⊥ then
    return FCR
  let sgRoot ← S.sgRoot[r]
  if ¬ (FCR ⪯ sgRoot ∧ sgRoot ∈ (← Fig7.getFilteredBlockTree S)) then
    return FCR
  return sgRoot


/-- The blocks of `blocks` that the grade-0 veto leaves: a block is dropped when `blocks`
    holds one conflicting with it and it has grade 0 in the store's own round. -/
def Store.applyG0Veto (S : Store Validator) (blocks : Finset (Block Validator)) :
    Finset (Block Validator) := Id.run do
  let r := round S.s
  return {B ∈ blocks | ¬ (∃ B' ∈ blocks, ¬ (B' ∼ B) ∧ S.G0 r B)}

/-! ## Figure `get_goldfish_tree(Σ)` -/
/-- `get_goldfish_tree(Σ)` at this layer,
    and so the protocol's: rooted at the SG fork choice run from the round's own root
    (`get_sg_majority_start`) over the processed tree, holding the finality layer's filtered
    blocks with the grade-0 veto applied.

    This is the layer's whole change to the fork choice, and to available confirmation with
    it — both take their tree from here. `get_head` (`01_GoldfishWalk.lean`) is untouched. -/
def Fig9.getGoldfishFilteredBlockTree (S : Store Validator) : NDRE (BlockTree Validator) := do
  let r := round S.s
  let anchor ← S.majorityForkChoice (← S.getSGMajorityStart r) S.T r
  return { root := anchor, blocks := S.applyG0Veto (← Fig7.getFilteredBlockTree S) }
/-- This layer's reading of what the fork choice takes from the layer: the tree above, and
    the eligibility condition unchanged from the finality layer, `Fig7.goldfishEligible`.

    Named like the earlier layers' readings (`Fig1.goldfishWalk`), and the `instance` below is
    what makes this one the protocol's. -/
abbrev Fig9.goldfishWalk : GoldfishWalk Validator :=
  ⟨Fig9.getGoldfishFilteredBlockTree, Fig7.goldfishEligible⟩

/-- The protocol's fork choice is this layer's reading: `GoldfishWalk`
    (`Defs/GoldfishWalk.lean`) has exactly one instance, and it lives with the last reading,
    so `Store.getHead` and the duties of `02_GoldfishDuties.lean` run this layer's tree
    without naming it — the round's own root under the walk, through
    `get_sg_majority_start`, and the grade-0 blocks dropped. This layer defines no
    `Fig9.getHead`: `Store.getHead` under this instance is it. A later layer would take the
    fork choice over by moving this instance to its own reading, not by adding one. -/
scoped instance : GoldfishWalk Validator := Fig9.goldfishWalk

/-! ## Figure `on_tick(Σ, t)` -/
/-- `on_tick(Σ, t)` at this layer: the
    clock, then the round's three lines, then the slot's two duties.

    The clock first, as in every reading — `Σ.t` and `Σ.s` are what each line below tests, so
    an instant is compared against the tick that is running, never the one before it.

    Then the round. The SG root at `Γ_1 = t_r + Δ`: the round's root is derived once, there,
    and stored in `Σ.sg_root[r]`, and every later reader takes it from the field rather than
    deriving it again, which is what makes one round have one root. The height pair at the
    round's action instant: `decide_height_vote` settles what this validator will sign and
    records it. The attestation at `sgfg_voting(Σ.id, r)`, this validator's own time, which
    the schedule assumes rather than fixes — the finality pair is decided there, and the
    round's one combined attestation goes out carrying it, the head `sg_vote` returns, and the
    height pair settled earlier. That broadcast is the only line in the spec that puts an
    attestation on the wire.

    Then the slot's actions, `goldfish_on_tick`, the Goldfish layer's own. The round's lines
    come first because they share instants with them: `Γ_1` is the opening slot's vote time,
    and the action instant is the tick at which that slot's confirmation is evaluated. A walk
    run in this tick uses the root stored in this tick.

    The reading is written out rather than composed onto `Fig2.onTick`, for the reason
    `Defs/Tick.lean` gives: a call can only put the new lines wholly before or wholly after,
    and these go between. What it reuses instead are the two halves that reading is itself
    made of, so nothing is written twice.

    The `[SGSchedule Validator]` binder is for the attestation time. There is no
    `[GoldfishWalk Validator]` binder: the instance above is in scope where this is
    elaborated, so this layer's fork choice is fixed inside it, while the duties it calls keep
    their binders and stay generic. -/
def Fig9.onTick [SGSchedule Validator] (S : Store Validator) (t : Int)
    (isProposer : (s : Nat) → (i : Validator) → Bool) :
    NDREB Validator (Store Validator) := do
  let mut S := S
  S ← S.setClock t
  let r := round S.s
  -- the round's lines
  if _ : S.s > 0 ∧ S.t = roundStart r + (Δ : Int) then
    S.sgRoot[r] ⇐ S.getSGRoot r
  S ⇐ S.goldfishOnTick isProposer
  if _ : S.t = heightDecisionTime r then
    S ⇐ S.decideHeightVote
  if S.t = SGSchedule.sgfgVoting S.id r then
    let {vote := fp, state := S'} := S.decideFinalityVote
    S ← S'
    let sgHead := (← S.sgVote).head
    let a := Attestation.mk (validator := S.id) (round := r) (head := sgHead)
      (heightPair := S.heightPair) (finalityPair := fp)
    broadcast (Message.attestation a)                             -- then the slot's actions
  return S

/-- The protocol's tick is this layer's reading: `Tick` (`Defs/Tick.lean`) has exactly one
    instance, and it lives with the last reading, so whoever drives the clock writes
    `S.onTick t is_proposer` and gets this. A later layer would take the tick over by moving
    this instance to its own reading, not by adding one. -/
scoped instance [SGSchedule Validator] : Tick Validator := ⟨Fig9.onTick⟩

end DC
