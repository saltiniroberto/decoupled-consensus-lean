module
public import GoldilocksCorrectness.Proofs.Routines.Blocks
public import GoldilocksCorrectness.Proofs.Routines.Kit
public import GoldilocksCorrectness.Statements.Routines.WalkDefs
import all Goldilocks.AC.ForkChoice
import all Goldilocks.AC.State
import all Goldilocks.Config

@[expose] public section

/-!
# What the Goldfish score answers

When no two blocks of `Φ.tree` share a root, `supports` and `goldfish_score` answer, and the score
of a block `B` is the number of equivocators of `votes` plus the number of the validators in
`supportersOf Φ votes support_votes s B`: those that are not equivocators and have a slot-`s` vote
in `support_votes` whose head is the root of a block of `Φ.tree` that is `B` or a descendant of `B`.

- the answers: `blockWithRoot_eq_ok`, `find?_eq_some`, `supports_eq_ok`, `goldfish_score_eq_ok`;
- membership: `mem_supportersOf_iff`, `mem_participants_iff`, `mem_equivocators_iff`;
- the sets: `supportersOf_mono`, `supportersOf_subset_participants`,
  `disjoint_supportersOf_equivocators`, `equivocators_subset_participants`,
  `not_mem_equivocators_of_votesOnceFor`, `mem_supportersOf_of_votesOnceFor`,
  `not_mem_supportersOf_of_conflicts`, `sup_subset_participants`;
- the count: `card_add_le_voters_of_disjoint`, `card_add_le_voters`,
  `voters_count_lt_of_committee_majority`, `committee_card_le_of_majority`.
-/

set_option autoImplicit false

open scoped DC

open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Statements.Routines

variable {V : Type} [DecidableEq V]

/-! ## The answers -/

/-- When no two blocks of `T` share a root, `blockWithRoot T r` answers the block `Block.find? T r`.

The variables:
- `T`: the tree; `r`: the root looked up. -/
theorem blockWithRoot_eq_ok {T : Finset (Block V)} (hRoots : RootsNameBlocksIn T) (r : BlockId) :
    blockWithRoot T r = .ok (Block.find? T r) := by
  have hcard : ¬ 2 ≤ ({B ∈ T | B.root = r}).card := by
    have : ({B ∈ T | B.root = r}).card ≤ 1 := Finset.card_le_one.2 (fun a ha b hb => by
      simp only [Finset.mem_filter] at ha hb
      exact hRoots a ha.1 b hb.1 (ha.2.trans hb.2.symm))
    omega
  simp only [blockWithRoot, if_neg hcard]
  rfl

/-- When no two blocks of `T` share a root, `Block.find? T r` is the block of `T` with the root `r`.

The variables:
- `T`: the tree; `H`: the block of `T`; `r`: its root. -/
theorem find?_eq_some {T : Finset (Block V)} (hRoots : RootsNameBlocksIn T) {H : Block V}
    {r : BlockId} (hH : H ∈ T) (hr : H.root = r) : Block.find? T r = some H :=
  pickUnique?_eq_some hH (by simp [hr]) (fun b hb hpb => hRoots b hb H hH (by
    simp only [decide_eq_true_eq] at hpb
    rw [hpb, hr]))

/-- When no two blocks of `Φ.tree` share a root, `supports Φ B vote` answers whether some block of
`Φ.tree` has the vote's head as its root and is `B` or a descendant of `B`.

The variables:
- `Φ`: the frame; `B`: the block supported; `vote`: the vote. -/
theorem supports_eq_ok {Φ : Frame V} (hRoots : RootsNameBlocksIn Φ.tree) (B : Block V)
    (vote : GoldfishVote V) :
    supports Φ B vote = .ok (decide (∃ H ∈ Φ.tree, H.root = vote.head ∧ B.AncestorEq H)) := by
  simp only [supports, blockWithRoot_eq_ok hRoots, dre_bind_ok]
  generalize hX : Block.find? Φ.tree vote.head = X
  cases X with
  | none =>
    have hno : ¬ ∃ H ∈ Φ.tree, H.root = vote.head ∧ B.AncestorEq H := by
      rintro ⟨H, hH, hr, -⟩
      rw [find?_eq_some hRoots hH hr] at hX
      cases hX
    simp only [ne_eq, not_true_eq_false, dite_false, decide_eq_false hno]
    rfl
  | some H =>
    obtain ⟨hH, hr⟩ := mem_of_pickUnique?_eq_some hX
    simp only [decide_eq_true_eq] at hr
    have hiff : (∃ H' ∈ Φ.tree, H'.root = vote.head ∧ B.AncestorEq H') ↔ B.AncestorEq H := by
      constructor
      · rintro ⟨H', hH', hr', hBH'⟩
        rwa [hRoots H' hH' H hH (hr'.trans hr.symm)] at hBH'
      · exact fun hBH => ⟨H, hH, hr, hBH⟩
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, dite_true, Option.value, Option.get_some]
    show Except.ok _ = Except.ok _
    congr 1
    rw [Bool.eq_iff_iff, decide_eq_true_iff]
    exact hiff.symm

variable [Fintype V]

/-- `supportersOf Φ votes support_votes s B`: the validators that are not equivocators of `votes`
and have a slot-`s` vote in `support_votes` whose head is the root of a block of `Φ.tree` that is
`B` or a descendant of `B`.

The variables:
- `Φ`: the frame; `votes`, `support_votes`: the votes and the support votes counted;
- `s`: the slot of the votes; `B`: the block supported. -/
def supportersOf (Φ : Frame V) (votes support_votes : Finset (GoldfishVote V)) (s : Slot)
    (B : Block V) : Finset V :=
  (support_votes.filter fun vote => vote.val_index ∉ equivocators votes ∧ vote.slot = s ∧
    ∃ H ∈ Φ.tree, H.root = vote.head ∧ B.AncestorEq H).map' fun vote => vote.val_index

/-- When no two blocks of `Φ.tree` share a root, the Goldfish score of `B` answers the number of
equivocators of `votes` plus the number of `B`'s supporters.

The variables:
- `Φ`: the frame; `votes`, `support_votes`: the votes and the support votes counted;
- `s`: the slot of the votes; `B`: the block scored. -/
theorem goldfish_score_eq_ok {Φ : Frame V} (hRoots : RootsNameBlocksIn Φ.tree)
    (votes support_votes : Finset (GoldfishVote V)) (s : Slot) (B : Block V) :
    goldfish_score Φ votes support_votes s B =
      .ok ((equivocators votes).card + (supportersOf Φ votes support_votes s B).card) := by
  simp only [goldfish_score, supports_eq_ok hRoots, dre_bind_ok]
  rw [filterM_eq_ok_filter _ (fun vote => vote.val_index ∉ equivocators votes ∧ vote.slot = s ∧
    ∃ H ∈ Φ.tree, H.root = vote.head ∧ B.AncestorEq H) support_votes (fun vote _ => by
      show Except.ok _ = Except.ok _
      congr 1
      simp [Bool.and_assoc])]
  rfl

/-! ## Membership -/

/-- A validator is a supporter of `B` exactly when it is not an equivocator of `votes` and has a
slot-`s` vote in `support_votes` whose head is the root of a block of `Φ.tree` that is `B` or a
descendant of `B`.

The variables:
- `Φ`: the frame; `votes`, `support_votes`: the votes and the support votes counted;
- `s`: the slot of the votes; `B`: the block supported; `v`: the validator. -/
theorem mem_supportersOf_iff (Φ : Frame V) (votes support_votes : Finset (GoldfishVote V))
    (s : Slot) (B : Block V) (v : V) :
    v ∈ supportersOf Φ votes support_votes s B ↔
      ∃ vote ∈ support_votes, vote.val_index = v ∧ v ∉ equivocators votes ∧ vote.slot = s ∧
        ∃ H ∈ Φ.tree, H.root = vote.head ∧ B.AncestorEq H := by
  simp only [supportersOf, Finset.map', Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨vote, ⟨hvote, hne, hs, hH⟩, rfl⟩
    exact ⟨vote, hvote, rfl, hne, hs, hH⟩
  · rintro ⟨vote, hvote, rfl, hne, hs, hH⟩
    exact ⟨vote, ⟨hvote, hne, hs, hH⟩, rfl⟩

/-- A validator has a vote in `votes` exactly when it is a participant of `votes`.

The variables:
- `votes`: the votes; `v`: the validator. -/
theorem mem_participants_iff (votes : Finset (GoldfishVote V)) (v : V) :
    v ∈ participants votes ↔ ∃ vote ∈ votes, vote.val_index = v := by
  simp [participants, participates, votes_by, Finset.card_pos, Finset.filter_nonempty_iff]

/-- **The voter count, as a number of participants.** `voters_count votes` is the number of
validators with a vote in `votes`, the members of `participants votes`.

The variables:
- `votes`: the votes.

Read aloud: the voter count of `votes` is the number of participants of `votes`.

Added by the record migration, step 1h, for the execution proofs that read
`voters_count` through its body. -/
theorem voters_count_eq (votes : Finset (GoldfishVote V)) :
    voters_count votes = (participants votes).card := by
  rfl

/-- A validator is an equivocator of `votes` exactly when `votes` holds at least two of its votes.

The variables:
- `votes`: the votes; `v`: the validator. -/
theorem mem_equivocators_iff (votes : Finset (GoldfishVote V)) (v : V) :
    v ∈ equivocators votes ↔ 2 ≤ (votes_by votes v).card := by
  simp [equivocators, equivocates]

/-! ## The sets -/

/-- A supporter of a block supports each of its ancestors.

The variables:
- `Φ`: the frame; `votes`, `support_votes`: the votes and the support votes counted;
- `s`: the slot of the votes; `X`: the ancestor; `Y`: the block. -/
theorem supportersOf_mono {Φ : Frame V} {votes support_votes : Finset (GoldfishVote V)} {s : Slot}
    {X Y : Block V} (hXY : X.AncestorEq Y) :
    supportersOf Φ votes support_votes s Y ⊆ supportersOf Φ votes support_votes s X := by
  intro v hv
  rw [mem_supportersOf_iff] at hv ⊢
  obtain ⟨vote, hvote, hval, hne, hs, H, hH, hr, hYH⟩ := hv
  exact ⟨vote, hvote, hval, hne, hs, H, hH, hr, ancestorEq_trans hXY hYH⟩

/-- When the support votes are among the votes, every supporter of a block participates in the
votes.

The variables:
- `Φ`: the frame; `votes`, `support_votes`: the votes and the support votes counted;
- `s`: the slot of the votes; `B`: the block. -/
theorem supportersOf_subset_participants {Φ : Frame V}
    {votes support_votes : Finset (GoldfishVote V)} {s : Slot} {B : Block V}
    (hSupport : support_votes ⊆ votes) :
    supportersOf Φ votes support_votes s B ⊆ participants votes := by
  intro v hv
  obtain ⟨vote, hvote, hval, -⟩ := (mem_supportersOf_iff _ _ _ _ _ _).1 hv
  exact (mem_participants_iff _ _).2 ⟨vote, hSupport hvote, hval⟩

/-- No supporter of a block is an equivocator.

The variables:
- `Φ`: the frame; `votes`, `support_votes`: the votes and the support votes counted;
- `s`: the slot of the votes; `B`: the block. -/
theorem disjoint_supportersOf_equivocators {Φ : Frame V}
    {votes support_votes : Finset (GoldfishVote V)} {s : Slot} {B : Block V} :
    Disjoint (supportersOf Φ votes support_votes s B) (equivocators votes) := by
  rw [Finset.disjoint_left]
  intro v hv
  obtain ⟨-, -, -, hne, -⟩ := (mem_supportersOf_iff _ _ _ _ _ _).1 hv
  exact hne

/-- Every equivocator participates.

The variables:
- `votes`: the votes. -/
theorem equivocators_subset_participants (votes : Finset (GoldfishVote V)) :
    equivocators votes ⊆ participants votes := by
  intro v hv
  rw [mem_equivocators_iff] at hv
  obtain ⟨vote, hvote⟩ := Finset.card_pos.1 (by omega : 0 < (votes_by votes v).card)
  simp only [votes_by, Finset.mem_filter] at hvote
  exact (mem_participants_iff _ _).2 ⟨vote, hvote.1, hvote.2⟩

/-- A validator with only one vote in `votes` is not an equivocator.

The variables:
- `votes`: the votes; `vote`: the validator's one vote; `v`: the validator. -/
theorem not_mem_equivocators_of_unique {votes : Finset (GoldfishVote V)} {vote : GoldfishVote V}
    {v : V}
    -- every vote of `v` in `votes` is `vote`
    (hu : ∀ vote' ∈ votes, vote'.val_index = v → vote' = vote) : v ∉ equivocators votes := by
  rw [mem_equivocators_iff]
  have : (votes_by votes v).card ≤ 1 := Finset.card_le_one.2 (fun a ha b hb => by
    simp only [votes_by, Finset.mem_filter] at ha hb
    rw [hu a ha.1 ha.2, hu b hb.1 hb.2])
  omega

/-- A validator with one vote for `R`'s chain is not an equivocator.

The variables:
- `Φ`: the frame; `votes`, `support_votes`: the votes and the support votes counted;
- `s`: the slot of the votes; `R`: the block; `v`: the validator. -/
theorem not_mem_equivocators_of_votesOnceFor {Φ : Frame V}
    {votes support_votes : Finset (GoldfishVote V)} {s : Slot} {R : Block V} {v : V}
    (hv : VotesOnceFor Φ votes support_votes s R v) : v ∉ equivocators votes := by
  obtain ⟨vote, -, -, -, -, hu⟩ := hv
  exact not_mem_equivocators_of_unique hu

/-- A validator with one vote for `R`'s chain supports every ancestor of `R`, and `R`.

The variables:
- `Φ`: the frame; `votes`, `support_votes`: the votes and the support votes counted;
- `s`: the slot of the votes; `R`: the block; `X`: the ancestor; `v`: the validator. -/
theorem mem_supportersOf_of_votesOnceFor {Φ : Frame V}
    {votes support_votes : Finset (GoldfishVote V)} {s : Slot} {R X : Block V} {v : V}
    (hv : VotesOnceFor Φ votes support_votes s R v) (hXR : X.AncestorEq R) :
    v ∈ supportersOf Φ votes support_votes s X := by
  have hne := not_mem_equivocators_of_votesOnceFor hv
  obtain ⟨vote, hvote, hval, hs, ⟨H, hH, hr, hRH⟩, -⟩ := hv
  exact (mem_supportersOf_iff _ _ _ _ _ _).2
    ⟨vote, hvote, hval, hne, hs, H, hH, hr, ancestorEq_trans hXR hRH⟩

/-- A validator with one vote for `R`'s chain does not support a block that conflicts with `R`,
when the support votes are among the votes and no two blocks of `Φ.tree` share a root.

The variables:
- `Φ`: the frame; `votes`, `support_votes`: the votes and the support votes counted;
- `s`: the slot of the votes; `R`: the block; `D`: the conflicting block; `v`: the validator. -/
theorem not_mem_supportersOf_of_conflicts {Φ : Frame V}
    {votes support_votes : Finset (GoldfishVote V)} {s : Slot} {R D : Block V} {v : V}
    (hRoots : RootsNameBlocksIn Φ.tree) (hSupport : support_votes ⊆ votes)
    (hv : VotesOnceFor Φ votes support_votes s R v) (hD : D.conflicts R = true) :
    v ∉ supportersOf Φ votes support_votes s D := by
  intro hmem
  obtain ⟨vote, -, -, -, ⟨H, hH, hr, hRH⟩, hu⟩ := hv
  obtain ⟨vote', hvote', hval', -, -, H', hH', hr', hDH'⟩ :=
    (mem_supportersOf_iff _ _ _ _ _ _).1 hmem
  have hvv : vote' = vote := hu vote' (hSupport hvote') hval'
  subst hvv
  have hHH : H' = H := hRoots H' hH' H hH (hr'.trans hr.symm)
  subst hHH
  rw [conflicts_iff, compatible_iff] at hD
  exact hD (ancestorEq_compatible hDH' hRH)

/-- When the support votes are among the votes, every validator with one vote for `R`'s chain
participates in the votes.

The variables:
- `Φ`: the frame; `votes`, `support_votes`: the votes and the support votes counted;
- `s`: the slot of the votes; `R`: the block; `Sup`: the validators. -/
theorem sup_subset_participants {Φ : Frame V} {votes support_votes : Finset (GoldfishVote V)}
    {s : Slot} {R : Block V} {Sup : Finset V} (hSupport : support_votes ⊆ votes)
    (hSup : ∀ v ∈ Sup, VotesOnceFor Φ votes support_votes s R v) : Sup ⊆ participants votes := by
  intro v hv
  obtain ⟨vote, hvote, hval, -⟩ := hSup v hv
  exact (mem_participants_iff _ _).2 ⟨vote, hSupport hvote, hval⟩

/-! ## The count -/

/-- The equivocators, the supporters of `D` and a set `Sup` of participants that are not
equivocators and do not support `D` number at most the voters.

The variables:
- `Φ`: the frame; `votes`, `support_votes`: the votes and the support votes counted;
- `s`: the slot of the votes; `D`: the block; `Sup`: the validators. -/
theorem card_add_le_voters_of_disjoint {Φ : Frame V}
    {votes support_votes : Finset (GoldfishVote V)} {s : Slot} {D : Block V} {Sup : Finset V}
    (hSupport : support_votes ⊆ votes)
    -- every member of `Sup` participates
    (hSupP : Sup ⊆ participants votes)
    -- no member of `Sup` is an equivocator
    (hSupEq : Disjoint Sup (equivocators votes))
    -- no member of `Sup` supports `D`
    (hdisj : Disjoint (supportersOf Φ votes support_votes s D) Sup) :
    (equivocators votes).card + (supportersOf Φ votes support_votes s D).card + Sup.card ≤
      voters_count votes := by
  have h1 : Disjoint (equivocators votes) (supportersOf Φ votes support_votes s D) :=
    disjoint_supportersOf_equivocators.symm
  have h2 : Disjoint (equivocators votes ∪ supportersOf Φ votes support_votes s D) Sup :=
    Finset.disjoint_union_left.2 ⟨hSupEq.symm, hdisj⟩
  have hsub : equivocators votes ∪ supportersOf Φ votes support_votes s D ∪ Sup ⊆
      participants votes :=
    Finset.union_subset (Finset.union_subset (equivocators_subset_participants votes)
      (supportersOf_subset_participants hSupport)) hSupP
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint h2, Finset.card_union_of_disjoint h1] at hcard
  exact hcard

/-- When `D` conflicts with `R`, the equivocators, the supporters of `D` and the validators of
`Sup`, each with one vote for `R`'s chain, number at most the voters.

The variables:
- `Φ`: the frame; `votes`, `support_votes`: the votes and the support votes counted;
- `s`: the slot of the votes; `R`: the block; `D`: the conflicting block; `Sup`: the validators. -/
theorem card_add_le_voters {Φ : Frame V} {votes support_votes : Finset (GoldfishVote V)}
    {s : Slot} {R D : Block V} {Sup : Finset V} (hRoots : RootsNameBlocksIn Φ.tree)
    (hSupport : support_votes ⊆ votes)
    (hSup : ∀ v ∈ Sup, VotesOnceFor Φ votes support_votes s R v) (hD : D.conflicts R = true) :
    (equivocators votes).card + (supportersOf Φ votes support_votes s D).card + Sup.card ≤
      voters_count votes :=
  card_add_le_voters_of_disjoint hSupport (sup_subset_participants hSupport hSup)
    (Finset.disjoint_left.2 fun v hv => not_mem_equivocators_of_votesOnceFor (hSup v hv))
    (Finset.disjoint_right.2 fun v hv =>
      not_mem_supportersOf_of_conflicts hRoots hSupport (hSup v hv) hD)

omit [Fintype V] in
/-- When `Hs` outnumbers the rest of `Q`, `Q` is at most twice `Hs`.

The variables:
- `Q`: the committee; `Hs`: the validators outnumbering the rest of `Q`. -/
theorem committee_card_le_of_majority {Q Hs : Finset V}
    -- the members of `Q` outside `Hs` are fewer than `Hs`
    (hMajority : (Q \ Hs).card < Hs.card) :
    Q.card ≤ 2 * Hs.card := by
  have := Finset.card_le_card_sdiff_add_card (s := Q) (t := Hs)
  omega

/-- When every vote of `votes` is from a member of `Q` and `Hs` outnumbers the rest of `Q`, the
validators with a vote in `votes` are fewer than twice `Hs`.

The variables:
- `votes`: the votes; `Q`: the committee; `Hs`: the validators outnumbering the rest of `Q`. -/
theorem voters_count_lt_of_committee_majority {votes : Finset (GoldfishVote V)} {Q Hs : Finset V}
    -- every vote of `votes` is from a member of `Q`
    (hQ : ∀ vote ∈ votes, vote.val_index ∈ Q)
    -- the members of `Q` outside `Hs` are fewer than `Hs`
    (hMajority : (Q \ Hs).card < Hs.card) :
    voters_count votes < 2 * Hs.card := by
  have hsub : participants votes ⊆ Q := by
    intro v hv
    obtain ⟨vote, hvote, hval⟩ := (mem_participants_iff _ _).1 hv
    exact hval ▸ hQ vote hvote
  have h1 : voters_count votes ≤ Q.card := Finset.card_le_card hsub
  have := Finset.card_le_card_sdiff_add_card (s := Q) (t := Hs)
  omega

end GoldilocksCorrectness.Proofs.Routines
