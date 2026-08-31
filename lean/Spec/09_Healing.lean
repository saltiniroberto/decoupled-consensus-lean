import Spec.«05_SGDuty»
import Spec.«07_FGStore»
import Spec.«08_FinalityVote»
import Spec.Defs.Nondet

/-!
# The graded layer: grades, the SG root, the fork choice, and the two vote rules

Round `r` grades the round-`(r−1)` attestations, read from the pool by *resolution time*
against the round's grade instants `Γ_j = t_{rR} + jΔ`. The grades fix the round's SG root —
the anchor every walk of the round starts from — constrain what a validator signs through
the grade-0 veto, and select the fresh grade-2 quorum behind the height pair.

The file is in three parts. First the grade evidence read from the pool — the summary
support and the equivocation instant — with the three grades over it. Then the round's
root and the tree: `get_sg_root`, and the `BlockTree` every walk descends. Then the two
vote rules, `get_sg_vote` and `get_fg_vote`, which the tick (`11_Duties.lean`) runs.

## This is the last layer, so its readings are the protocol's

`get_goldfish_tree(Σ)` below is the tree every walk of the assembled protocol descends:
rooted at `get_sg_root(Σ, round(Σ.s))` over the finality layer's filtered blocks —
**no grade-0 veto**: the veto constrains what a validator signs, in `get_sg_vote` and
`get_fg_vote`, never where a walk may step. `get_head` sits beside it, and available
confirmation (`10_AvailableConfirmation.lean`) takes the same tree.

## The store caches none of this

The store does not cache a view, a quorum set, a support score, a grade, an anchor, a
viable tree, or a filtered tree: each is derived when used. The scores compare stored
processing and resolution times against past instants, so a grade evaluated at any time
after its instants gives one fixed answer.

## "The deepest block" is a pick

Two conflicting blocks cannot both hold a direct majority, so the blocks with grade 1, and
those with grade 2, lie on one chain — where "the deepest block" is the single `⪯`-maximal
one. That is a fact about the scores, not of the types, so the routines pick from
`S.deepest G`, the `⪯`-maximal blocks: on the sets the protocol builds the pick is from a
singleton, and nothing here assumes it.

## The grade summary's tie is a disjunction

`(t_v, C_v)` selects validator `v`'s earliest-*resolved* fresh vote with a named confirmed
block; the
protocol does not say how a tie in resolution time breaks. This rendering lets any
earliest-resolved vote answer: `v` supports `B` when *some* vote of minimal resolution
time names a confirmed block descending from `B`. Two votes tying exactly is an equivocation `e_v`
already prices.

## Extract

Round `r` grades the confirmed blocks of the round-`(r−1)` attestations against its grade
instants
`Γ_j = t_{rR} + jΔ`, `j ∈ {−1, 0, 1, 2}`. The evidence is read by resolution time: a vote
counts only once the store holds the block its vote names, and an empty confirmed block
never
carries a grade. A validator has equivocated as of an instant when two of its stored
round-`(r−1)` attestations with distinct confirmed blocks were both processed before it. Grades are
signed evidence.

## Extract — Definition (Grade summary and grades)

Fix round `r` and validator `v`, and let `v`'s *fresh* votes be its stored round-`(r−1)`
attestations. `(C_v, t_v)` is the confirmed block and resolution time of `v`'s
earliest-resolved
fresh vote with a named one — `(⊥, +∞)` when there is none — and `e_v` is the instant at
which two distinct fresh votes by `v` became visible, `+∞` while there is at most one.
The two support scores over a block `B` are

`direct_support(Σ, r, Γ_h, Γ_e, B) = w({v : t_v < Γ_h, B ⪯ C_v, e_v ≥ Γ_e})`

`favorable_support(Σ, r, Γ, B) = w({v : t_v < Γ_h, B ⪯ C_v} ∪ {v : e_v < Γ})`

— the direct score deletes the equivocators its instant has seen, the favorable score
credits them to every block. The grades, with `m = ⌊W/2⌋ + 1`:

`G2(B) ⇔ direct_support(Σ, r, Γ_{−1}, Γ_2, B) ≥ m`,
`G1(B) ⇔ direct_support(Σ, r, Γ_0, Γ_0, B) ≥ m`,
`G0(B) ⇔ favorable_support(Σ, r, Γ_1, B) ≥ m`.

`G2` is used from `Γ_2` on, `G1` from `Γ_0` on, `G0` from `Γ_1` on. Support counts
descendants, so every grade is inherited by ancestors; two conflicting blocks cannot both
hold a direct majority, so the grade-1 blocks, and the grade-2 blocks, lie on one chain.

## Extract — Definition (The veto, the root, and the tree)

`G0_conflict_free(Σ, r, B)` holds when no block of the filtered tree timestamped before
`Γ_1` conflicts with `B` and has grade 0 — the grade is on the vetoing block, and a block
learned after the freeze `Γ_1` never becomes a veto. `get_sg_root(Σ, r)` is the deepest
grade-1 block of the filtered tree, else `majority_fork_choice(Σ, get_fg_root(Σ), tree, r)`
— always a block. `get_goldfish_tree(Σ)` roots the filtered tree at
`get_sg_root(Σ, round(Σ.s))`; no veto is applied to it.

## Extract — Definition (The two vote rules)

At `a_r`, `A_G2` is the deepest grade-2 block of the filtered tree, `⊥` when there is
none. `get_sg_vote(Σ, r, A_G2)` is the deepest veto-free block between the anchor and the
confirmed block — `get_sg_root(Σ, r) ⪯ B ⪯ Σ.live_confirmed` with `G0_conflict_free` —
else `A_G2`, which needs no clearance test since a grade-2 block excludes every
conflicting grade-0 block, else the raw anchor, which keeps voting total.
`get_fg_vote(Σ, r, A_G2)` reads `(h_j, J, h_F)` off the *current-slot head's* chain state
`Σ.σ[H]` — the store keeps no `h_F` of its own — and offers a height pair only when
`A_G2 ≠ ⊥`, from the state of the deepest veto-free block between `A_G2` and
`Σ.live_confirmed`, else `A_G2` itself.

-/

set_option autoImplicit false

namespace DC

variable {Validator : Type} [BlockIds] [BlockIdentity Validator]
  [DecidableEq Validator] [Electorate Validator] [Params]

open Params

/-! ## New figure — The grade evidence and the grades -/

/-- Validator `v`'s grade summary supports `B` before the instant `c`: some *fresh* vote of
    `v` — a stored round-`k` attestation — has a named, processed confirmed block, its
    resolution time
    (the later of its stamp and that block's) is minimal among `v`'s such votes and precedes
    `c`, and the block descends from `B`. This is the protocol's `t_v < c ∧ B ⪯ C_v`, with
    the tie read as the module header says. -/
def Store.summarySupports (S : Store Validator) (k : Int) (v : Validator) (c : Int)
    (B : BlockId) : Prop :=
  ∃ e ∈ S.attestations[k], e.vote.validator = v ∧
    ∃ C ∈ e.vote.confirmed, C ∈ S.T ∧
      max e.time ((S.blockTime C).getD e.time) < c ∧
      (∀ e' ∈ S.attestations[k], e'.vote.validator = v →
        ∀ C' ∈ e'.vote.confirmed, C' ∈ S.T →
          max e.time ((S.blockTime C).getD e.time) ≤
            max e'.time ((S.blockTime C').getD e'.time)) ∧
      B ⪯[S] C

instance (S : Store Validator) (k : Int) (v : Validator) (c : Int) (B : BlockId) :
    Decidable (S.summarySupports k v c B) := inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- Validator `v` has equivocated in round `k` as of instant `c` — the protocol's
    `e_v < c`: two stored round-`k` attestations of its with distinct confirmed blocks,
    both processed
    before `c`. The detection time is the later of the two stamps, so both must clear the
    cutoff; the pair fields play no part, attestations differing only in them being one
    vote the pool never holds twice. -/
def Store.equivBefore (S : Store Validator) (k : Int) (v : Validator) (c : Int) : Prop :=
  ∃ a ∈ S.attestations[k], ∃ b ∈ S.attestations[k],
    a.vote.validator = v ∧ b.vote.validator = v ∧ a.vote.confirmed ≠ b.vote.confirmed ∧
    a.time < c ∧ b.time < c

instance (S : Store Validator) (k : Int) (v : Validator) (c : Int) :
    Decidable (S.equivBefore k v c) := inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-! ## Figure `direct_support(Σ, r, Γ_h, Γ_e, B)` -/
/-- The weight of the validators whose grade summary supports `B` before the instant
    `Γ_h`, net of those seen equivocating before the equivocation instant `Γ_e` —
    equivocators are deleted. Round `0` reads the empty round-`(−1)` pool, so every score
    is `0`. -/
def Store.directSupport (S : Store Validator) (r : Nat) (Γ_h Γ_e : Int) (B : BlockId) :
    Nat :=
  w({v ∈ Electorate.V | S.summarySupports (r - 1) v Γ_h B ∧ ¬ S.equivBefore (r - 1) v Γ_e})

/-! ## Figure `favorable_support(Σ, r, Γ, B)` -/
/-- The weight of the validators whose grade summary supports `B` before `Γ`, together
    with every validator seen equivocating before it — equivocators are credited. -/
def Store.favorableSupport (S : Store Validator) (r : Nat) (Γc : Int) (B : BlockId) :
    Nat :=
  w({v ∈ Electorate.V | S.summarySupports (r - 1) v Γc B ∨ S.equivBefore (r - 1) v Γc})

/-- `G2(B)`: a direct majority with the support cutoff at `Γ_{−1}` and the equivocation
    cutoff at `Γ_2`. Used from `Γ_2` on. -/
def Store.G2 (S : Store Validator) (r : Nat) (B : BlockId) : Prop :=
  S.directSupport r (Γ (-1) r) (Γ 2 r) B ≥ m Validator

instance (S : Store Validator) (r : Nat) (B : BlockId) : Decidable (S.G2 r B) :=
  inferInstanceAs (Decidable (_ ≥ _))

/-- `G1(B)`: a direct majority with both cutoffs at `Γ_0`. Used from `Γ_0` on. -/
def Store.G1 (S : Store Validator) (r : Nat) (B : BlockId) : Prop :=
  S.directSupport r (Γ 0 r) (Γ 0 r) B ≥ m Validator

instance (S : Store Validator) (r : Nat) (B : BlockId) : Decidable (S.G1 r B) :=
  inferInstanceAs (Decidable (_ ≥ _))

/-- `G0(B)`: a favorable majority at `Γ_1`. Used from `Γ_1` on. -/
def Store.G0 (S : Store Validator) (r : Nat) (B : BlockId) : Prop :=
  S.favorableSupport r (Γ 1 r) B ≥ m Validator

instance (S : Store Validator) (r : Nat) (B : BlockId) : Decidable (S.G0 r B) :=
  inferInstanceAs (Decidable (_ ≥ _))

/-- The `⪯[Σ]`-maximal blocks of `G`: those with no strict descendant in `G`. The routines
    below pick "the deepest block" from grade sets, which lie on one chain (the module
    header says why), so there the pick is from this set's single element; the pick stays
    honest when the set is not a chain. -/
def Store.deepest (S : Store Validator) (G : Finset BlockId) : Finset BlockId :=
  {B ∈ G | ∀ C ∈ G, ¬ B ≺[S] C}

/-! ## Figure `G0_conflict_free(Σ, r, B)` -/
/-- No block of the filtered tree, timestamped before `Γ_1`, conflicts with `B` and holds
    grade 0. **The grade is on the vetoing block `B'`, not on `B`**, and a block learned
    after the freeze `Γ_1` never becomes a veto — genesis's missing stamp is `−∞` and
    passes the freeze, and genesis conflicts nothing. It raises exactly where the filtered
    tree does. -/
def Store.G0ConflictFree (S : Store Validator) (r : Nat) (B : BlockId) : DRE Bool := do
  let vetoes := {B' ∈ (← Store.getFilteredBlockTree S) |
    (∀ t ∈ S.blockTime B', t < Γ 1 r) ∧ ¬ (B' ∼[S] B) ∧ S.G0 r B'}
  return vetoes = ∅

/-! ## New figure — The round's root, the tree, and the fork choice -/
/-! ## Figure `get_sg_root(Σ, r)` -/
/-- The round's SG root: the deepest grade-1 block of the filtered tree, else the majority
    fork choice from the FG root over it. Always a block, derived when used — the store
    caches no anchor. -/
def Store.getSGRoot (S : Store Validator) (r : Nat) : NDRE BlockId := do
  let tree ← Store.getFilteredBlockTree S
  let G := {B ∈ tree | S.G1 r B}
  if G ≠ ∅ then
    let D ←ᵖ S.deepest G
    return D
  return (← S.majorityForkChoice S.getFGRoot tree r)

/-! ## Figure `get_goldfish_tree(Σ)` -/
/-- The tree every walk of the assembled protocol descends: the finality layer's filtered
    blocks, rooted at the round's SG root. **No grade-0 veto**: the veto constrains what a
    validator signs, never where a walk may step. -/
def Store.getGoldfishTree (S : Store Validator) : NDRE (BlockTree) := do
  let r := round S.s
  let anchor ← S.getSGRoot r
  return { root := anchor, blocks := (← Store.getFilteredBlockTree S) }

/-! ## Figure -/
/-- `get_head(Σ, votes, k)`: the
    Goldfish walk over the tree above — descending from its root, stepping onto its blocks —
    testing the eligibility condition of `07_FGStore.lean`.

    It sits in this file because the tree does, and the tree is what the graded layer
    settles. Every caller writes `S.getHead votes k`; there is one definition and nothing
    redefines it. -/
def Store.getHead (S : Store Validator)
    (votes supportVotes : Finset (GoldfishVote Validator)) (k : Nat) : NDRE BlockId := do
  S.ghost (← S.getGoldfishTree) (S.goldfishScore votes supportVotes k)
    (S.goldfishEligible votes supportVotes k)

/-! ## New figure — The two vote rules -/

/-- `A_G2`: the deepest grade-2 block of the filtered tree, `⊥` when no block holds
    grade 2 — the fresh quorum both vote rules read at their own instants. The protocol
    derives it inline where the votes are made; a definition here, because this rendering
    makes the two votes at two instants and each needs it. -/
def Store.deepestG2 (S : Store Validator) (r : Nat) : NDRE (Option BlockId) := do
  let G := {B ∈ (← Store.getFilteredBlockTree S) | S.G2 r B}
  if G ≠ ∅ then
    let D ←ᵖ S.deepest G
    return some D
  return ⊥

/-! ## Figure `get_sg_vote(Σ, r, A_G2)` -/
/-- The confirmed block this validator signs for round `r`: the deepest veto-free block
    between the
    anchor and the confirmed block, else the grade-2 block — which needs no clearance
    test, a grade-2 block excluding every conflicting grade-0 block — else the raw
    anchor, which keeps voting total. -/
def Store.getSGVote (S : Store Validator) (r : Nat) (A_G2 : Option BlockId) :
    NDRE BlockId := do
  let C := S.liveConfirmed
  let A ← S.getSGRoot r
  let between ← {B ∈ᴹ S.T.keys | A ⪯[S] B ∧ B ⪯[S] C ∧ (← S.G0ConflictFree r B)}
  if between ≠ ∅ then
    let D ←ᵖ S.deepest between
    return D
  if A_G2 ≠ ⊥ then
    return (← A_G2)
  return A

/-! ## Figure `get_fg_vote(Σ, r, A_G2)` -/
/-- The FG vote's fields. `(h_j, J, h_F)` come from the *current-slot head's* chain state,
    `Σ.σ[H]` — which is why the store keeps no `h_F` of its own; the head is run on every
    held current-slot vote, the resolved ones supporting. The height inputs are offered
    only when a fresh grade-2 quorum exists: the state of the deepest veto-free block
    between `A_G2` and the confirmed block, else `A_G2` itself. The client rules
    (`08_FinalityVote.lean`) turn the result into the two pairs. -/
def Store.getFGVote (S : Store Validator) (r : Nat) (A_G2 : Option BlockId) :
    NDRE (FGVote) := do
  let votes := {e.vote | e ∈ S.gfVotes[S.s]}
  let supportVotes := {a ∈ votes | S.resolved a}
  let H ← S.getHead votes supportVotes S.s
  let σH ← S.σ[H]
  if A_G2 = ⊥ then
    return { heightInputs := ⊥, h_j := σH.h_j, J := σH.J, h_F := σH.h_F }
  let AG2 ← A_G2
  let C := S.liveConfirmed
  let between ← {B ∈ᴹ S.T.keys | AG2 ⪯[S] B ∧ B ⪯[S] C ∧ (← S.G0ConflictFree r B)}
  let Cfg ← if between ≠ ∅ then do
      let D ←ᵖ S.deepest between
      pure D
    else
      pure AG2
  let σC ← S.σ[Cfg]
  return { heightInputs := some ⟨σC.h, σC.T_h, σC.nj⟩,
           h_j := σH.h_j, J := σH.J, h_F := σH.h_F }

end DC
