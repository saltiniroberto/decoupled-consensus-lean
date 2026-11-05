module
public import GoldilocksCorrectness.Record.Facts
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ScoreDefs
public import GoldilocksCorrectness.Proofs.Routines.Score

@[expose] public section

/-!
# ScoreACStore, over a model

The theorems of `GoldilocksCorrectness/Proofs/Routines/Score.lean` on the readers of a set
of votes, over a model `M` whose facts `F` hold: the supporters of a block
(`supportersOf`, on `ScoreDefs.lean`), the participants and the equivocators of a set of
votes, and the counts. (The page's fork-choice theorems read the Goldfish score, which the
record has no member for.)

The recovery section at the end of the page states each landed theorem again, as the
landed statement (`type_of%`), and proves it from its record form at the spec's model
`Model.goldilocks` and its facts `goldilocksFacts`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Record
open GoldilocksCorrectness.Record.Proofs.Routines.ScoreDefs (supportersOf)
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn VotesOnceFor)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_compatible ancestorEq_trans
  compatible_iff conflicts_iff)

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded in the goal and in every
hypothesis: `omega` does not see a fact stated at either. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

variable {V : Type} [DecidableEq V] [Fintype V]

/-- `supportersOf Φ votes support_votes s B`: the validators that are not equivocators of `votes`
and have a slot-`s` vote in `support_votes` whose head is the root of a block of `Φ.tree` that is
`B` or a descendant of `B`.

The variables:
- `M`: the model;
- `Φ`: the frame; `votes`, `support_votes`: the votes and the support votes counted;
- `s`: the slot of the votes; `B`: the block supported.

Read aloud: the validators that are not equivocators of `votes` and have a slot-`s` vote in `support_votes` whose head is a block of `Φ.tree` that is `B` or a descendant of `B`. -/
def supportersOf (M : GoldilocksModel V) (Φ : Frame V) (votes support_votes : Finset (GoldfishVote V)) (s : Slot)
    (B : Block V) : Finset V :=
  (support_votes.filter fun vote => vote.val_index ∉ M.equivocators votes ∧ vote.slot = s ∧
    ∃ H ∈ Φ.tree, H.root = vote.head ∧ B.AncestorEq H).map' fun vote => vote.val_index

section

variable (M : GoldilocksModel V) (F : Facts M)
include M F

/-- A validator is a supporter of `B` exactly when it is not an equivocator of `votes` and has a
slot-`s` vote in `support_votes` whose head is the root of a block of `Φ.tree` that is `B` or a
descendant of `B`.

The variables:
- `M`: the model; `F`: its facts;
- `Φ`: the frame; `votes`, `support_votes`: the votes and the support votes counted;
- `s`: the slot of the votes; `B`: the block supported; `v`: the validator.

Read aloud: `v` supports `B` exactly when it is not an equivocator of `votes` and has a slot-`s` vote in `support_votes` whose head is a block of `Φ.tree` that is `B` or a descendant of `B`. -/
theorem mem_supportersOf_iff (Φ : Frame V) (votes support_votes : Finset (GoldfishVote V))
    (s : Slot) (B : Block V) (v : V) :
    v ∈ supportersOf M Φ votes support_votes s B ↔
      ∃ vote ∈ support_votes, vote.val_index = v ∧ v ∉ M.equivocators votes ∧ vote.slot = s ∧
        ∃ H ∈ Φ.tree, H.root = vote.head ∧ B.AncestorEq H := by
  simp only [supportersOf, Finset.map', Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨vote, ⟨hvote, hne, hs, hH⟩, rfl⟩
    exact ⟨vote, hvote, rfl, hne, hs, hH⟩
  · rintro ⟨vote, hvote, rfl, hne, hs, hH⟩
    exact ⟨vote, ⟨hvote, hne, hs, hH⟩, rfl⟩

/-- A validator has a vote in `votes` exactly when it is a participant of `votes`.

The variables:
- `M`: the model; `F`: its facts;
- `votes`: the votes; `v`: the validator.

Read aloud: `v` is a participant of `votes` exactly when `votes` holds a vote of `v`. -/
theorem mem_participants_iff (votes : Finset (GoldfishVote V)) (v : V) :
    v ∈ M.participants votes ↔ ∃ vote ∈ votes, vote.val_index = v := by
  simp [F.rd.participants_eq, F.rd.participates_eq, F.rd.votes_by_eq, Finset.card_pos, Finset.filter_nonempty_iff]

/-- **The voter count, as a number of participants.** `voters_count votes` is the number of
validators with a vote in `votes`, the members of `participants votes`.

The variables:
- `M`: the model; `F`: its facts;
- `votes`: the votes.

Read aloud: the voter count of `votes` is the number of participants of `votes`.

Added by the record migration, step 1h, for the execution proofs that read
`voters_count` through its body. -/
theorem voters_count_eq (votes : Finset (GoldfishVote V)) :
    M.voters_count votes = (M.participants votes).card :=
  F.rd.voters_count_eq votes

/-- A validator is an equivocator of `votes` exactly when `votes` holds at least two of its votes.

The variables:
- `M`: the model; `F`: its facts;
- `votes`: the votes; `v`: the validator.

Read aloud: `v` is an equivocator of `votes` exactly when `votes` holds at least two votes of `v`. -/
theorem mem_equivocators_iff (votes : Finset (GoldfishVote V)) (v : V) :
    v ∈ M.equivocators votes ↔ 2 ≤ (M.votes_by votes v).card := by
  simp [F.rd.equivocators_eq, F.rd.equivocates_eq]

/-- A supporter of a block supports each of its ancestors.

The variables:
- `M`: the model; `F`: its facts;
- `Φ`: the frame; `votes`, `support_votes`: the votes and the support votes counted;
- `s`: the slot of the votes; `X`: the ancestor; `Y`: the block.

Read aloud: a supporter of a block supports each of its ancestors. -/
theorem supportersOf_mono {Φ : Frame V} {votes support_votes : Finset (GoldfishVote V)} {s : Slot}
    {X Y : Block V} (hXY : X.AncestorEq Y) :
    supportersOf M Φ votes support_votes s Y ⊆ supportersOf M Φ votes support_votes s X := by
  intro v hv
  rw [(mem_supportersOf_iff M F)] at hv ⊢
  obtain ⟨vote, hvote, hval, hne, hs, H, hH, hr, hYH⟩ := hv
  exact ⟨vote, hvote, hval, hne, hs, H, hH, hr, ancestorEq_trans hXY hYH⟩

/-- When the support votes are among the votes, every supporter of a block participates in the
votes.

The variables:
- `M`: the model; `F`: its facts;
- `Φ`: the frame; `votes`, `support_votes`: the votes and the support votes counted;
- `s`: the slot of the votes; `B`: the block.

Read aloud: when the support votes are among the votes, every supporter of a block is a participant. -/
theorem supportersOf_subset_participants {Φ : Frame V}
    {votes support_votes : Finset (GoldfishVote V)} {s : Slot} {B : Block V}
    (hSupport : support_votes ⊆ votes) :
    supportersOf M Φ votes support_votes s B ⊆ M.participants votes := by
  intro v hv
  obtain ⟨vote, hvote, hval, -⟩ := ((mem_supportersOf_iff M F) _ _ _ _ _ _).1 hv
  exact ((mem_participants_iff M F) _ _).2 ⟨vote, hSupport hvote, hval⟩

/-- No supporter of a block is an equivocator.

The variables:
- `M`: the model; `F`: its facts;
- `Φ`: the frame; `votes`, `support_votes`: the votes and the support votes counted;
- `s`: the slot of the votes; `B`: the block.

Read aloud: no supporter of a block is an equivocator. -/
theorem disjoint_supportersOf_equivocators {Φ : Frame V}
    {votes support_votes : Finset (GoldfishVote V)} {s : Slot} {B : Block V} :
    Disjoint (supportersOf M Φ votes support_votes s B) (M.equivocators votes) := by
  rw [Finset.disjoint_left]
  intro v hv
  obtain ⟨-, -, -, hne, -⟩ := ((mem_supportersOf_iff M F) _ _ _ _ _ _).1 hv
  exact hne

/-- Every equivocator participates.

The variables:
- `M`: the model; `F`: its facts;
- `votes`: the votes.

Read aloud: every equivocator is a participant. -/
theorem equivocators_subset_participants (votes : Finset (GoldfishVote V)) :
    M.equivocators votes ⊆ M.participants votes := by
  intro v hv
  rw [(mem_equivocators_iff M F)] at hv
  obtain ⟨vote, hvote⟩ := Finset.card_pos.1 (by omega : 0 < (M.votes_by votes v).card)
  simp only [F.rd.votes_by_eq, Finset.mem_filter] at hvote
  exact ((mem_participants_iff M F) _ _).2 ⟨vote, hvote.1, hvote.2⟩

/-- A validator with only one vote in `votes` is not an equivocator.

The variables:
- `M`: the model; `F`: its facts;
- `votes`: the votes; `vote`: the validator's one vote; `v`: the validator.

Read aloud: a validator with only one vote in `votes` is not an equivocator. -/
theorem not_mem_equivocators_of_unique {votes : Finset (GoldfishVote V)} {vote : GoldfishVote V}
    {v : V}
    -- every vote of `v` in `votes` is `vote`
    (hu : ∀ vote' ∈ votes, vote'.val_index = v → vote' = vote) :
    v ∉ M.equivocators votes := by
  rw [(mem_equivocators_iff M F)]
  have : (M.votes_by votes v).card ≤ 1 := Finset.card_le_one.2 (fun a ha b hb => by
    simp only [F.rd.votes_by_eq, Finset.mem_filter] at ha hb
    rw [hu a ha.1 ha.2, hu b hb.1 hb.2])
  omega

/-- A validator with one vote for `R`'s chain is not an equivocator.

The variables:
- `M`: the model; `F`: its facts;
- `Φ`: the frame; `votes`, `support_votes`: the votes and the support votes counted;
- `s`: the slot of the votes; `R`: the block; `v`: the validator.

Read aloud: a validator with one vote for `R`'s chain is not an equivocator. -/
theorem not_mem_equivocators_of_votesOnceFor {Φ : Frame V}
    {votes support_votes : Finset (GoldfishVote V)} {s : Slot} {R : Block V} {v : V}
    (hv : VotesOnceFor Φ votes support_votes s R v) :
    v ∉ M.equivocators votes := by
  obtain ⟨vote, -, -, -, -, hu⟩ := hv
  exact (not_mem_equivocators_of_unique M F) hu

/-- A validator with one vote for `R`'s chain supports every ancestor of `R`, and `R`.

The variables:
- `M`: the model; `F`: its facts;
- `Φ`: the frame; `votes`, `support_votes`: the votes and the support votes counted;
- `s`: the slot of the votes; `R`: the block; `X`: the ancestor; `v`: the validator.

Read aloud: a validator with one vote for `R`'s chain supports `R` and every ancestor of `R`. -/
theorem mem_supportersOf_of_votesOnceFor {Φ : Frame V}
    {votes support_votes : Finset (GoldfishVote V)} {s : Slot} {R X : Block V} {v : V}
    (hv : VotesOnceFor Φ votes support_votes s R v) (hXR : X.AncestorEq R) :
    v ∈ supportersOf M Φ votes support_votes s X := by
  have hne := (not_mem_equivocators_of_votesOnceFor M F) hv
  obtain ⟨vote, hvote, hval, hs, ⟨H, hH, hr, hRH⟩, -⟩ := hv
  exact ((mem_supportersOf_iff M F) _ _ _ _ _ _).2
    ⟨vote, hvote, hval, hne, hs, H, hH, hr, ancestorEq_trans hXR hRH⟩

/-- A validator with one vote for `R`'s chain does not support a block that conflicts with `R`,
when the support votes are among the votes and no two blocks of `Φ.tree` share a root.

The variables:
- `M`: the model; `F`: its facts;
- `Φ`: the frame; `votes`, `support_votes`: the votes and the support votes counted;
- `s`: the slot of the votes; `R`: the block; `D`: the conflicting block; `v`: the validator.

Read aloud: a validator with one vote for `R`'s chain does not support a block that conflicts with `R`. -/
theorem not_mem_supportersOf_of_conflicts {Φ : Frame V}
    {votes support_votes : Finset (GoldfishVote V)} {s : Slot} {R D : Block V} {v : V}
    (hRoots : RootsNameBlocksIn Φ.tree) (hSupport : support_votes ⊆ votes)
    (hv : VotesOnceFor Φ votes support_votes s R v) (hD : D.conflicts R = true) :
    v ∉ supportersOf M Φ votes support_votes s D := by
  intro hmem
  obtain ⟨vote, -, -, -, ⟨H, hH, hr, hRH⟩, hu⟩ := hv
  obtain ⟨vote', hvote', hval', -, -, H', hH', hr', hDH'⟩ :=
    ((mem_supportersOf_iff M F) _ _ _ _ _ _).1 hmem
  have hvv : vote' = vote := hu vote' (hSupport hvote') hval'
  subst hvv
  have hHH : H' = H := hRoots H' hH' H hH (hr'.trans hr.symm)
  subst hHH
  rw [conflicts_iff, compatible_iff] at hD
  exact hD (ancestorEq_compatible hDH' hRH)

/-- When the support votes are among the votes, every validator with one vote for `R`'s chain
participates in the votes.

The variables:
- `M`: the model; `F`: its facts;
- `Φ`: the frame; `votes`, `support_votes`: the votes and the support votes counted;
- `s`: the slot of the votes; `R`: the block; `Sup`: the validators.

Read aloud: when the support votes are among the votes, every validator with one vote for `R`'s chain is a participant. -/
theorem sup_subset_participants {Φ : Frame V} {votes support_votes : Finset (GoldfishVote V)}
    {s : Slot} {R : Block V} {Sup : Finset V} (hSupport : support_votes ⊆ votes)
    (hSup : ∀ v ∈ Sup, VotesOnceFor Φ votes support_votes s R v) :
    Sup ⊆ M.participants votes := by
  intro v hv
  obtain ⟨vote, hvote, hval, -⟩ := hSup v hv
  exact ((mem_participants_iff M F) _ _).2 ⟨vote, hSupport hvote, hval⟩

/-- The equivocators, the supporters of `D` and a set `Sup` of participants that are not
equivocators and do not support `D` number at most the voters.

The variables:
- `M`: the model; `F`: its facts;
- `Φ`: the frame; `votes`, `support_votes`: the votes and the support votes counted;
- `s`: the slot of the votes; `D`: the block; `Sup`: the validators.

Read aloud: the equivocators, the supporters of `D` and a set of participants that are not equivocators and do not support `D` number at most the voters. -/
theorem card_add_le_voters_of_disjoint {Φ : Frame V}
    {votes support_votes : Finset (GoldfishVote V)} {s : Slot} {D : Block V} {Sup : Finset V}
    (hSupport : support_votes ⊆ votes)
    -- every member of `Sup` M.participates
    (hSupP : Sup ⊆ M.participants votes)
    -- no member of `Sup` is an equivocator
    (hSupEq : Disjoint Sup (M.equivocators votes))
    -- no member of `Sup` supports `D`
    (hdisj : Disjoint (supportersOf M Φ votes support_votes s D) Sup) :
    (M.equivocators votes).card + (supportersOf M Φ votes support_votes s D).card + Sup.card ≤
      M.voters_count votes := by
  have h1 : Disjoint (M.equivocators votes) (supportersOf M Φ votes support_votes s D) :=
    (disjoint_supportersOf_equivocators M F).symm
  have h2 : Disjoint (M.equivocators votes ∪ supportersOf M Φ votes support_votes s D) Sup :=
    Finset.disjoint_union_left.2 ⟨hSupEq.symm, hdisj⟩
  have hsub : M.equivocators votes ∪ supportersOf M Φ votes support_votes s D ∪ Sup ⊆
      M.participants votes :=
    Finset.union_subset (Finset.union_subset ((equivocators_subset_participants M F) votes)
      ((supportersOf_subset_participants M F) hSupport)) hSupP
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint h2, Finset.card_union_of_disjoint h1] at hcard
  rw [F.rd.voters_count_eq]
  exact hcard

/-- When `D` conflicts with `R`, the equivocators, the supporters of `D` and the validators of
`Sup`, each with one vote for `R`'s chain, number at most the voters.

The variables:
- `M`: the model; `F`: its facts;
- `Φ`: the frame; `votes`, `support_votes`: the votes and the support votes counted;
- `s`: the slot of the votes; `R`: the block; `D`: the conflicting block; `Sup`: the validators.

Read aloud: when `D` conflicts with `R`, the equivocators, the supporters of `D` and validators each with one vote for `R`'s chain number at most the voters. -/
theorem card_add_le_voters {Φ : Frame V} {votes support_votes : Finset (GoldfishVote V)}
    {s : Slot} {R D : Block V} {Sup : Finset V} (hRoots : RootsNameBlocksIn Φ.tree)
    (hSupport : support_votes ⊆ votes)
    (hSup : ∀ v ∈ Sup, VotesOnceFor Φ votes support_votes s R v) (hD : D.conflicts R = true) :
    (M.equivocators votes).card + (supportersOf M Φ votes support_votes s D).card + Sup.card ≤
      M.voters_count votes :=
  (card_add_le_voters_of_disjoint M F) hSupport ((sup_subset_participants M F) hSupport hSup)
    (Finset.disjoint_left.2 fun v hv => (not_mem_equivocators_of_votesOnceFor M F) (hSup v hv))
    (Finset.disjoint_right.2 fun v hv =>
      (not_mem_supportersOf_of_conflicts M F) hRoots hSupport (hSup v hv) hD)

/-- When every vote of `votes` is from a member of `Q` and `Hs` outnumbers the rest of `Q`, the
validators with a vote in `votes` are fewer than twice `Hs`.

The variables:
- `M`: the model; `F`: its facts;
- `votes`: the votes; `Q`: the committee; `Hs`: the validators outnumbering the rest of `Q`.

Read aloud: when every vote is from a member of `Q` and `Hs` outnumbers the rest of `Q`, the voters are fewer than twice `Hs`. -/
theorem voters_count_lt_of_committee_majority {votes : Finset (GoldfishVote V)} {Q Hs : Finset V}
    -- every vote of `votes` is from a member of `Q`
    (hQ : ∀ vote ∈ votes, vote.val_index ∈ Q)
    -- the members of `Q` outside `Hs` are fewer than `Hs`
    (hMajority : (Q \ Hs).card < Hs.card) :
    M.voters_count votes < 2 * Hs.card := by
  have hsub : M.participants votes ⊆ Q := by
    intro v hv
    obtain ⟨vote, hvote, hval⟩ := ((mem_participants_iff M F) _ _).1 hv
    exact hval ▸ hQ vote hvote
  have h1 : M.voters_count votes ≤ Q.card := by
    rw [F.rd.voters_count_eq]; exact Finset.card_le_card hsub
  have := Finset.card_le_card_sdiff_add_card (s := Q) (t := Hs)
  omega

end

/-! ## At the spec's model -/

/-- The landed `GoldilocksCorrectness.Proofs.Routines.mem_supportersOf_iff`,
recovered from its record form at the spec's model.

Read aloud: the landed `mem_supportersOf_iff` holds, as the record's theorem at the spec's
model. -/
theorem mem_supportersOf_iff_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.mem_supportersOf_iff V _ _) := by
  simp only [record_goldilocks]
  exact mem_supportersOf_iff Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.mem_participants_iff`,
recovered from its record form at the spec's model.

Read aloud: the landed `mem_participants_iff` holds, as the record's theorem at the spec's
model. -/
theorem mem_participants_iff_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.mem_participants_iff V _ _) := by
  exact mem_participants_iff Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.voters_count_eq`,
recovered from its record form at the spec's model.

Read aloud: the landed `voters_count_eq` holds, as the record's theorem at the spec's
model. -/
theorem voters_count_eq_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.voters_count_eq V _ _) := by
  exact voters_count_eq Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.mem_equivocators_iff`,
recovered from its record form at the spec's model.

Read aloud: the landed `mem_equivocators_iff` holds, as the record's theorem at the spec's
model. -/
theorem mem_equivocators_iff_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.mem_equivocators_iff V _ _) := by
  exact mem_equivocators_iff Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.supportersOf_mono`,
recovered from its record form at the spec's model.

Read aloud: the landed `supportersOf_mono` holds, as the record's theorem at the spec's
model. -/
theorem supportersOf_mono_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.supportersOf_mono V _ _) := by
  exact supportersOf_mono Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.supportersOf_subset_participants`,
recovered from its record form at the spec's model.

Read aloud: the landed `supportersOf_subset_participants` holds, as the record's theorem at the spec's
model. -/
theorem supportersOf_subset_participants_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.supportersOf_subset_participants V _ _) := by
  simp only [record_goldilocks]
  exact supportersOf_subset_participants Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.disjoint_supportersOf_equivocators`,
recovered from its record form at the spec's model.

Read aloud: the landed `disjoint_supportersOf_equivocators` holds, as the record's theorem at the spec's
model. -/
theorem disjoint_supportersOf_equivocators_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.disjoint_supportersOf_equivocators V _ _) := by
  simp only [record_goldilocks]
  exact @disjoint_supportersOf_equivocators V _ _ Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.equivocators_subset_participants`,
recovered from its record form at the spec's model.

Read aloud: the landed `equivocators_subset_participants` holds, as the record's theorem at the spec's
model. -/
theorem equivocators_subset_participants_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.equivocators_subset_participants V _ _) := by
  exact equivocators_subset_participants Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.not_mem_equivocators_of_unique`,
recovered from its record form at the spec's model.

Read aloud: the landed `not_mem_equivocators_of_unique` holds, as the record's theorem at the spec's
model. -/
theorem not_mem_equivocators_of_unique_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.not_mem_equivocators_of_unique V _ _) := by
  exact not_mem_equivocators_of_unique Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.not_mem_equivocators_of_votesOnceFor`,
recovered from its record form at the spec's model.

Read aloud: the landed `not_mem_equivocators_of_votesOnceFor` holds, as the record's theorem at the spec's
model. -/
theorem not_mem_equivocators_of_votesOnceFor_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.not_mem_equivocators_of_votesOnceFor V _ _) := by
  exact not_mem_equivocators_of_votesOnceFor Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.mem_supportersOf_of_votesOnceFor`,
recovered from its record form at the spec's model.

Read aloud: the landed `mem_supportersOf_of_votesOnceFor` holds, as the record's theorem at the spec's
model. -/
theorem mem_supportersOf_of_votesOnceFor_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.mem_supportersOf_of_votesOnceFor V _ _) := by
  exact mem_supportersOf_of_votesOnceFor Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.not_mem_supportersOf_of_conflicts`,
recovered from its record form at the spec's model.

Read aloud: the landed `not_mem_supportersOf_of_conflicts` holds, as the record's theorem at the spec's
model. -/
theorem not_mem_supportersOf_of_conflicts_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.not_mem_supportersOf_of_conflicts V _ _) := by
  exact not_mem_supportersOf_of_conflicts Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.sup_subset_participants`,
recovered from its record form at the spec's model.

Read aloud: the landed `sup_subset_participants` holds, as the record's theorem at the spec's
model. -/
theorem sup_subset_participants_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.sup_subset_participants V _ _) := by
  exact sup_subset_participants Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.card_add_le_voters_of_disjoint`,
recovered from its record form at the spec's model.

Read aloud: the landed `card_add_le_voters_of_disjoint` holds, as the record's theorem at the spec's
model. -/
theorem card_add_le_voters_of_disjoint_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.card_add_le_voters_of_disjoint V _ _) := by
  simp only [record_goldilocks]
  exact card_add_le_voters_of_disjoint Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.card_add_le_voters`,
recovered from its record form at the spec's model.

Read aloud: the landed `card_add_le_voters` holds, as the record's theorem at the spec's
model. -/
theorem card_add_le_voters_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.card_add_le_voters V _ _) := by
  simp only [record_goldilocks]
  exact card_add_le_voters Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.voters_count_lt_of_committee_majority`,
recovered from its record form at the spec's model.

Read aloud: the landed `voters_count_lt_of_committee_majority` holds, as the record's theorem at the spec's
model. -/
theorem voters_count_lt_of_committee_majority_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.voters_count_lt_of_committee_majority V _ _) := by
  exact voters_count_lt_of_committee_majority Model.goldilocks goldilocksFacts

end GoldilocksCorrectness.Record.Proofs.Routines
