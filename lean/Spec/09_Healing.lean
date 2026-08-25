import Spec.«07_FGStore»
import Spec.Defs.Nondet

/-!
# Healing: round grades and round roots

Round `r` grades the heads of the round-`(r−1)` attestations, through the store's
per-round head bookkeeping, and uses the grades to fix one SG root per round: the
proposer offers a root in its opening block, each receiver checks it, and the accepted or
fallback root anchors the round's Goldfish votes and its SG and FG outputs.

This file holds the two function groups of that mechanism: the support scores read from
the store's round entries, with the grades defined over them, and the round-root
functions — proposal root, lower root, SG root, walk root, action root.

## What is not yet here

The store fields these functions read — `Σ.head[·]`, `Σ.equiv[·]`, `Σ.root_proposal[·]`,
`Σ.sg_root[·]` (`Store.lean`) — are written by no routine yet: the handler lines that fill
them, the opening block's proposal-root field, and the fork-choice redirection through the
walk root land with their own figures. Until then this file's functions are defined and
unconsumed.

## The tree the rules read

Every root function selects within `get_filtered_block_tree(Σ)` and falls back to
`fork_choice_root(Σ)`, both of `07_FGStore.lean`. No new view is introduced.

## "The deepest block" is a pick

Support counts descendants, so every grade is inherited by ancestors; and two conflicting
blocks cannot both hold a direct majority, so the blocks with grade 2, and those with
grade 3, lie on one chain — where "the deepest block" is the single `⪯`-maximal one.
That is a fact about the scores, not of the types, so the routines pick from `deepest G`,
the `⪯`-maximal blocks: on the sets the protocol builds the pick is from a singleton, and
nothing here assumes it.

## Extract

Healing gives each round one agreed root. Round `r` grades the heads of the
round-`(r−1)` attestations against its grade instants `Γ_j = t_r + jΔ`, `j ∈ {−1, 0, 1, 2}`
(`t_r` the proposal time of the round's opening slot): the store keeps, per round and
validator, the first processed nonempty attestation head with its processing time
(`Σ.head[r][i]`), and the time at which a different head from the same validator was
first processed (`Σ.equiv[r][i]`). The scores compare stored processing times against
past instants, so a grade evaluated at any time after its instants gives one fixed
answer. Grades are signed evidence.

## Extract — Definition (Support and grades)

Fix round `r`, block `B`, and `j ∈ {−1, 0, 1, 2}`. `H_j(B)` contains the validators whose
stored round-`(r−1)` head was processed before `Γ_j` and supports `B` (the head descends
from `B`), and `E_j` those whose stored equivocation time is before that instant. For
round `0` the round-`(−1)` entries are empty, so every score is `0`. The support scores
are

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
SG root is `R_low`. Each Goldfish fork choice then starts from `get_walk_root(Σ, r)`: the
stored SG root when the fork-choice root precedes it, else the fork-choice root.

At `a_r`, the validator derives the root anchoring its SG and FG outputs,
`get_action_root(Σ, r)`: the walk root when it is in the filtered tree and either equals
the fork-choice root or has grade 1; otherwise the fork-choice root itself — a
validator's own selection needs no external backing, while a round root adopted from
others must still be viable and majority-backed at signing time.

-/

set_option autoImplicit false

namespace DC

variable {Validator : Type} [Roots] [DecidableEq Validator] [Electorate Validator] [Params]

/-- Validator `i` has a stored round-`k` SG vote, processed before instant `c`, whose
    head descends from `B`. The stored head is a `Block` — an empty-headed vote is never
    stored — so the ancestry test reads it directly. -/
def Store.headSupports (S : Store Validator) (k : Int) (i : Validator) (c : Int)
    (B : Block Validator) : Prop :=
  ∃ vt ∈ S.sgVotes k, vt.vote.validator = i ∧ vt.time < c ∧ B ⪯ vt.vote.head

instance (S : Store Validator) (k : Int) (i : Validator) (c : Int) (B : Block Validator) :
    Decidable (S.headSupports k i c B) := inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- Validator `i`'s stored round-`k` equivocation time is before instant `c`. Absent while
    no equivocation was processed, and an absent entry is before nothing. -/
def Store.equivBefore (S : Store Validator) (k : Int) (i : Validator) (c : Int) : Prop :=
  ∃ tE ∈ S.equiv k i, tE < c

instance (S : Store Validator) (k : Int) (i : Validator) (c : Int) :
    Decidable (S.equivBefore k i c) := inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-! ## Figure -/
/-- `support_scores(Σ, r, j, B)`: the pair `(S_j(B), S̄_j(B))` of round-`r` support scores
    for `B`, read from the round-`(r−1)` entries against the grade instant `Γ_j`.

    `H_j(B)` is the set of validators whose stored round-`(r−1)` head was processed before
    `Γ_j` and supports `B` — the head descends from `B`; `E_j` the set of those whose
    stored equivocation time is before that instant. Then `S_j(B) = w(H_j(B) \ E_j)`, the
    support net of equivocators, and `S̄_j(B) = w(H_j(B) ∪ E_j)`, the support together
    with every equivocator. For round `0` the round-`(−1)` entries are empty, so every
    score is `0`. -/
def Store.supportScores (S : Store Validator) (r : Nat) (j : Int) (B : Block Validator) :
    Nat × Nat :=
  let Hj := {i ∈ Electorate.V (Validator := Validator) | S.headSupports (r - 1) i (Γ j r) B}
  let Ej := {i ∈ Electorate.V (Validator := Validator) | S.equivBefore (r - 1) i (Γ j r)}
  (w(Hj \ Ej), w(Hj ∪ Ej))  -- S_j(B), S̄_j(B)

/-! ## Figure -/
/-- `two_view_support(Σ, r, B)`: `S_{−1,1}(B)`, the two-view score — support counted with
    the head cutoff at `Γ_{−1}` and the equivocation cutoff at `Γ_1`: the validators whose
    stored round-`(r−1)` head was processed before `Γ_{−1}` and supports `B`, net of those
    whose stored equivocation time is before `Γ_1`. -/
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

/-! ## Figure -/
/-- `get_proposal_root(Σ, r)`: the root the round's opening proposer offers in its opening
    block — the deepest block in the filtered tree with grade 2, or the fork-choice root
    when no such block exists. -/
def Store.getProposalRoot (S : Store Validator) (r : Nat) : NDRE (Block Validator) := do
  -- the proposer, at t_r
  let G := {B ∈ (← S.getFilteredBlockTree) | S.G2 r B}
  if G ≠ ∅ then
    let D ←ᵖ deepest G
    return D
  return S.forkChoiceRoot

/-! ## Figure -/
/-- `get_lower_root(Σ, r)`: the receiver's fallback against the proposal — the deepest
    block in the filtered tree with grade 3 strictly descending from the fork-choice root,
    or the fork-choice root itself when there is none. -/
def Store.getLowerRoot (S : Store Validator) (r : Nat) : NDRE (Block Validator) := do
  let G := {B ∈ (← S.getFilteredBlockTree) | S.G3 r B ∧ S.forkChoiceRoot ≺ B}
  if G ≠ ∅ then
    let D ←ᵖ deepest G
    return D
  return S.forkChoiceRoot

/-! ## Figure -/
/-- `get_sg_root(Σ, r)`: the round's SG root, derived at the opening slot's vote time. The
    proposed root `R_prop` is accepted exactly when the lower root precedes it, it is in
    the filtered tree, and it holds grade 1; otherwise, and while no opening block has
    registered a proposal, the SG root is the lower root. -/
def Store.getSGRoot (S : Store Validator) (r : Nat) : NDRE (Block Validator) := do
  let Rlow ← S.getLowerRoot r
  if S.rootProposal r = ⊥ then
    return Rlow
  let Rprop ← S.rootProposal r
  if Rlow ⪯ Rprop ∧ Rprop ∈ (← S.getFilteredBlockTree) ∧ S.G1 r Rprop then
    return Rprop
  return Rlow

/-! ## Figure -/
/-- `get_walk_root(Σ, r)`: where a Goldfish walk of round `r` starts — the stored SG root
    when the fork-choice root precedes it, else the fork-choice root.

    `Σ.sg_root[r]` is read by the raising extraction: the protocol runs this only after
    the round's SG root is stored, so behind that schedule the raise is unreachable. -/
def Store.getWalkRoot (S : Store Validator) (r : Nat) : DRE (Block Validator) := do
  let C := S.forkChoiceRoot
  let RSG ← S.sgRoot r
  if C ⪯ RSG then
    return RSG
  return C

/-! ## Figure -/
/-- `get_action_root(Σ, r)`: the root anchoring the round's SG and FG outputs, derived at
    `a_r` — the walk root when it is in the filtered tree and either equals the
    fork-choice root or holds grade 1; otherwise the fork-choice root itself. A
    validator's own selection needs no external backing, while a round root adopted from
    others must still be viable and majority-backed at signing time. -/
def Store.getActionRoot (S : Store Validator) (r : Nat) : DRE (Block Validator) := do
  -- at a_r
  let C := S.forkChoiceRoot
  let R ← S.getWalkRoot r
  if R ∈ (← S.getFilteredBlockTree) ∧ (R = C ∨ S.G1 r R) then
    return R
  return C

end DC
