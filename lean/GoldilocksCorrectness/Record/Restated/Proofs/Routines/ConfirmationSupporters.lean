module
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Confirmation
public import GoldilocksCorrectness.Proofs.Routines.Lemma30
public import GoldilocksCorrectness.Proofs.Routines.Lemma77
public import GoldilocksCorrectness.Proofs.Routines.Lemma77Compat
public import GoldilocksCorrectness.Proofs.Routines.Score
import all Goldilocks.AC.State

@[expose] public section

/-!
# The confirmation update over a majority of votes, over a model

The theorems of `GoldilocksCorrectness/Proofs/Routines/ConfirmationSupporters.lean`,
`Lemma77Compat.lean` and `Lemma36.lean` that count the votes the confirmation update reads, over a
model `M` whose facts `F` hold: each takes the record's predicate `ConfirmationUpdated M C P n t s n'`
where the landed theorem takes the spec's answer.

The update's support votes over the record (`SupportVotes`) are, under the facts, the library's
set `{vote ∈ early | no_second_vote_in late vote = true}` of the early and the late votes
(`supportVotes_eq`), and the record's voter count is the library's (`voters_count_eq_spec`); so the
walk the predicate names is the walk of the library's Goldfish score and test
(`confirmationUpdated_walk`), and the landed proofs' counting goes through unchanged.

The recovery section states the landed theorems again, as the landed statement (`type_of%`), at the
AC state `n.A` and the frame `fg_to_ac n.S` of a node state `n`, as on `Confirmation.lean`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

open DC (DRE)

namespace GoldilocksCorrectness.Record.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Record
open GoldilocksCorrectness.Record.Statements.Routines (ResolvesAt ConfirmationUpdated EarlyVotes
  LateVotes SupportVotes ConfirmationScore ConfirmationEligible EarlySupporterOf EarlyVoteOnceFor
  Lockable
  confirmationUpdated_at_node goldilocks_resolvesAt goldilocks_earlySupporterOf)
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn WalkEnd VotesOnceFor)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  compatible_of_ancestorEq_compatible occurrenceBefore_eq_true_iff mem_participants_iff
  voters_count_eq mem_equivocators_iff supportersOf mem_supportersOf_iff
  mem_supportersOf_of_votesOnceFor goldfish_score_eq_ok dre_bind_ok walkSteps_spec
  equivocators_support_eq_empty not_mem_equivocators_of_unique disjoint_supportersOf_equivocators
  equivocators_subset_participants supportersOf_subset_participants supportersOf_mono
  fast_test_eq_ok_true_iff)

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The vote sets over the library -/

/-- Under the facts, the record's `no_second_vote_in` is the library's.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: the record's no-second-vote test is the spec's. -/
theorem no_second_vote_in_eq_spec {M : GoldilocksModel V} (F : Facts M) :
    M.no_second_vote_in = Goldilocks.no_second_vote_in := by
  funext late vote
  rw [F.rd.no_second_vote_in_eq]
  simp only [Goldilocks.no_second_vote_in]

/-- Under the facts, the record's participants of a set of votes are the library's.

The variables:
- `M`: the model; `F`: its facts; `X`: the votes.

Read aloud: the record's participants are the spec's. -/
theorem participants_eq_spec {M : GoldilocksModel V} (F : Facts M)
    (X : Finset (GoldfishVote V)) : M.participants X = participants X := by
  ext v
  rw [mem_participants_iff, F.rd.participants_eq]
  simp [F.rd.participates_eq, F.rd.votes_by_eq, Finset.card_pos, Finset.filter_nonempty_iff]

/-- Under the facts, the record's voter count is the library's.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: the record's voter count is the spec's. -/
theorem voters_count_eq_spec {M : GoldilocksModel V} (F : Facts M) :
    M.voters_count = Goldilocks.voters_count := by
  funext X
  rw [F.rd.voters_count_eq, participants_eq_spec F, voters_count_eq]

/-- Under the facts, the support votes of the update are the early votes whose validator has no
second vote among the late votes, with the library's test.

The variables:
- `M`: the model; `F`: its facts; `C`: the configuration; `n`: the node state; `s'`: the slot.

Read aloud: the record's support votes are the spec's filter of the early votes. -/
theorem supportVotes_eq {M : GoldilocksModel V} (F : Facts M) (C : Config) (n : M.N) (s' : Slot) :
    SupportVotes M C n s' =
      {vote ∈ EarlyVotes M C n s' | no_second_vote_in (LateVotes M C n s') vote = true} := by
  unfold SupportVotes
  rw [no_second_vote_in_eq_spec F]

/-- A vote is early exactly when it is a vote of the slot that resolves strictly before
`C.t_ s' + 2 · C.Δ`.

The variables:
- `M`: the model; `C`: the configuration; `n`: the node state; `s'`: the slot; `vote`: the vote.

Read aloud: the early votes, by membership. -/
theorem mem_earlyVotes {M : GoldilocksModel V} {C : Config} {n : M.N} {s' : Slot}
    {vote : GoldfishVote V} :
    vote ∈ EarlyVotes M C n s' ↔ vote ∈ M.votesHeldSet n s' ∧
      ∃ y : Stamp, ResolvesAt M n vote y ∧ y < ((C.t_ s' + 2 * C.Δ : Time) : Stamp) := by
  simp only [EarlyVotes, Finset.mem_filter]

/-- A vote is late exactly when it is a vote of the slot stamped strictly before
`C.t_ s' + 6 · C.Δ`.

The variables:
- `M`: the model; `C`: the configuration; `n`: the node state; `s'`: the slot; `vote`: the vote.

Read aloud: the late votes, by membership. -/
theorem mem_lateVotes {M : GoldilocksModel V} {C : Config} {n : M.N} {s' : Slot}
    {vote : GoldfishVote V} :
    vote ∈ LateVotes M C n s' ↔ vote ∈ M.votesHeldSet n s' ∧
      ∃ τ : Stamp, n.voteStamp vote = some τ ∧ τ < ((C.t_ s' + 6 * C.Δ : Time) : Stamp) := by
  simp only [LateVotes, Finset.mem_filter]

/-- Every early vote is a late vote: a vote resolves no earlier than its stamp, and
`C.t_ s' + 2 · C.Δ` is before `C.t_ s' + 6 · C.Δ`.

The variables:
- `M`: the model; `C`: the configuration; `n`: the node state; `s'`: the slot.

Read aloud: the early votes are late votes. -/
theorem earlyVotes_subset_lateVotes {M : GoldilocksModel V} {C : Config} {n : M.N} {s' : Slot} :
    EarlyVotes M C n s' ⊆ LateVotes M C n s' := by
  intro vote hv
  obtain ⟨hp, y, hy, hlt⟩ := mem_earlyVotes.1 hv
  obtain ⟨τv, τH, H, hτv, -, -, -, -, rfl⟩ := hy
  refine mem_lateVotes.2 ⟨hp, τv, hτv, ?_⟩
  have hΔ : (0 : Int) < C.Δ := C.Δ_pos
  have hlt' : C.t_ s' + 2 * C.Δ < C.t_ s' + 6 * C.Δ :=
    Int.add_lt_add_left (Int.mul_lt_mul_of_pos_right (by decide) hΔ) _
  have hc : ((C.t_ s' + 2 * C.Δ : Time) : Stamp) < ((C.t_ s' + 6 * C.Δ : Time) : Stamp) :=
    WithBot.coe_lt_coe.2 hlt'
  exact lt_of_le_of_lt (le_max_left _ _) (lt_trans hlt hc)

/-- Every late vote is a vote of the slot `n` holds.

The variables:
- `M`: the model; `C`: the configuration; `n`: the node state; `s'`: the slot.

Read aloud: the late votes are votes `n` holds. -/
theorem lateVotes_subset {M : GoldilocksModel V} {C : Config} {n : M.N} {s' : Slot} :
    LateVotes M C n s' ⊆ M.votesHeldSet n s' :=
  fun _ hv => (mem_lateVotes.1 hv).1

/-- The walk the update of slot `s ≥ 1` reads, over the library's score and test: under the facts,
when no two blocks of the frame's tree share a root, the walk of the Goldfish score over the
support votes and the test `voters_count late < 2 · score`, from the frame's finalized block, ends
at some `H`; the test answers `b` on `H`; and the update saves `H` when `b` holds, nothing
otherwise.

The variables:
- `M`: the model; `F`: its facts; `C`, `P`: the parameters; `n`, `n'`: the node states before and
  after; `t`: the time; `s`: the slot.

Read aloud: the record's update walks the spec's score and test. -/
theorem confirmationUpdated_walk [RootOrder] {M : GoldilocksModel V} (F : Facts M) {C : Config}
    {P : Provisional V} {n n' : M.N} {t : Time} {s : Slot} (hs : 1 ≤ s)
    (hRoots : RootsNameBlocksIn (M.fg_to_ac n).tree)
    (hUpdate : ConfirmationUpdated M C P n t s n') :
    ∃ (H : Block V) (b : Bool),
      @WalkEnd V M.tieBreak (M.fg_to_ac n).tree
        (goldfish_score (M.fg_to_ac n)
          {vote ∈ EarlyVotes M C n (s - 1) | no_second_vote_in (LateVotes M C n (s - 1)) vote = true}
          {vote ∈ EarlyVotes M C n (s - 1) | no_second_vote_in (LateVotes M C n (s - 1)) vote = true}
          (s - 1))
        (fun B => do
          let k ← goldfish_score (M.fg_to_ac n)
            {vote ∈ EarlyVotes M C n (s - 1) | no_second_vote_in (LateVotes M C n (s - 1)) vote = true}
            {vote ∈ EarlyVotes M C n (s - 1) | no_second_vote_in (LateVotes M C n (s - 1)) vote = true}
            (s - 1) B
          pure (decide (voters_count (LateVotes M C n (s - 1)) < 2 * k)))
        (M.fg_to_ac n).F H ∧
      (do
          let k ← goldfish_score (M.fg_to_ac n)
            {vote ∈ EarlyVotes M C n (s - 1) | no_second_vote_in (LateVotes M C n (s - 1)) vote = true}
            {vote ∈ EarlyVotes M C n (s - 1) | no_second_vote_in (LateVotes M C n (s - 1)) vote = true}
            (s - 1) H
          pure (decide (voters_count (LateVotes M C n (s - 1)) < 2 * k)) : DRE Bool) = .ok b ∧
      n'.savedConfirmation (s - 1) = if b = true then some H else none := by
  obtain ⟨-, H, hW, hS, -⟩ := hUpdate.resolve_left fun h0 => Nat.one_le_iff_ne_zero.1 hs h0.1
  have hsc : ConfirmationScore M C n (s - 1) = goldfish_score (M.fg_to_ac n)
      {vote ∈ EarlyVotes M C n (s - 1) | no_second_vote_in (LateVotes M C n (s - 1)) vote = true}
      {vote ∈ EarlyVotes M C n (s - 1) | no_second_vote_in (LateVotes M C n (s - 1)) vote = true}
      (s - 1) := by
    funext B
    simp only [ConfirmationScore, supportVotes_eq F]
  have hel : ConfirmationEligible M C n (s - 1) = (fun B => do
      let k ← goldfish_score (M.fg_to_ac n)
        {vote ∈ EarlyVotes M C n (s - 1) | no_second_vote_in (LateVotes M C n (s - 1)) vote = true}
        {vote ∈ EarlyVotes M C n (s - 1) | no_second_vote_in (LateVotes M C n (s - 1)) vote = true}
        (s - 1) B
      pure (decide (voters_count (LateVotes M C n (s - 1)) < 2 * k))) := by
    funext B
    simp only [ConfirmationEligible, hsc, voters_count_eq_spec F]
  rw [hsc, hel] at hW
  rw [hel] at hS
  refine ⟨H, decide (voters_count (LateVotes M C n (s - 1)) < 2 *
    ((equivocators {vote ∈ EarlyVotes M C n (s - 1) |
        no_second_vote_in (LateVotes M C n (s - 1)) vote = true}).card +
      (supportersOf (M.fg_to_ac n)
        {vote ∈ EarlyVotes M C n (s - 1) | no_second_vote_in (LateVotes M C n (s - 1)) vote = true}
        {vote ∈ EarlyVotes M C n (s - 1) | no_second_vote_in (LateVotes M C n (s - 1)) vote = true}
        (s - 1) H).card)), hW, ?_, ?_⟩
  · simp only [goldfish_score_eq_ok hRoots, dre_bind_ok]
    rfl
  · rw [hS]
    simp only [goldfish_score_eq_ok hRoots, dre_bind_ok, pure, Except.pure, Except.ok.injEq]

/-- An early supporter of `B`, under a node whose slot-`s'` votes all have the slot `s'`, votes once
for `B`'s chain among the update's support votes.

The variables:
- `M`: the model; `C`: the configuration; `n`: the node state; `s'`: the slot; `B`: the block;
  `v`: the validator.

Read aloud: an early supporter's vote is a support vote, its validator's only one. -/
theorem votesOnceFor_of_earlySupporter {M : GoldilocksModel V} {C : Config} {n : M.N}
    {s' : Slot} {B : Block V} {v : V}
    (hSlot : ∀ vote ∈ M.votesHeldSet n s', vote.slot = s')
    (h : EarlySupporterOf M C n s' B v) :
    VotesOnceFor (M.fg_to_ac n)
      {vote ∈ EarlyVotes M C n s' | no_second_vote_in (LateVotes M C n s') vote = true}
      {vote ∈ EarlyVotes M C n s' | no_second_vote_in (LateVotes M C n s') vote = true} s' B v := by
  obtain ⟨vote, hvote, hval, hhead, ⟨y, hy, hx⟩, hu⟩ := h
  obtain ⟨y', hy', hlt⟩ := (occurrenceBefore_eq_true_iff _ _).1 hx
  obtain rfl := Option.some.inj hy'
  have hE : vote ∈ EarlyVotes M C n s' := mem_earlyVotes.2 ⟨hvote, y, hy, hlt⟩
  have hN : no_second_vote_in (LateVotes M C n s') vote = true := by
    simp only [no_second_vote_in, decide_eq_true_eq]
    intro u hu'
    by_cases huv : u.val_index = vote.val_index
    · exact Or.inl (hu u (lateVotes_subset hu') (huv.trans hval))
    · exact Or.inr huv
  exact ⟨vote, Finset.mem_filter.2 ⟨hE, hN⟩, hval, hSlot vote hvote, hhead,
    fun vote' hv' hval' =>
      hu vote' (lateVotes_subset (earlyVotes_subset_lateVotes (Finset.mem_filter.1 hv').1)) hval'⟩

/-- The validators with a late vote are validators with a vote `n` holds.

The variables:
- `M`: the model; `C`: the configuration; `n`: the node state; `s'`: the slot.

Read aloud: the late voters are among the voters. -/
theorem voters_count_late_le {M : GoldilocksModel V} {C : Config} {n : M.N} {s' : Slot} :
    voters_count (LateVotes M C n s') ≤ voters_count (M.votesHeldSet n s') := by
  rw [voters_count_eq, voters_count_eq]
  refine Finset.card_le_card fun v hv => ?_
  obtain ⟨vote, hvote, hval⟩ := (mem_participants_iff _ _).1 hv
  exact (mem_participants_iff _ _).2 ⟨vote, lateVotes_subset hvote, hval⟩

/-- The update's test accepts a block `X` that is an ancestor of `B`, or `B`, when every member of
`Hs` votes once for `B`'s chain among the support votes and the voters are fewer than twice `Hs`.

The variables:
- `M`: the model; `C`: the configuration; `n`: the node state; `s'`: the slot; `X`, `B`: the
  blocks; `Hs`: the supporters.

Read aloud: an ancestor of a majority's block passes the update's test. -/
theorem eligible_of_supporters [RootOrder] {M : GoldilocksModel V} {C : Config} {n : M.N}
    {s' : Slot} {X B : Block V} {Hs : Finset V}
    (hRoots : RootsNameBlocksIn (M.fg_to_ac n).tree) (hXB : X.AncestorEq B)
    (hSup : ∀ v ∈ Hs, VotesOnceFor (M.fg_to_ac n)
      {vote ∈ EarlyVotes M C n s' | no_second_vote_in (LateVotes M C n s') vote = true}
      {vote ∈ EarlyVotes M C n s' | no_second_vote_in (LateVotes M C n s') vote = true} s' B v)
    (hVoters : voters_count (M.votesHeldSet n s') < 2 * Hs.card) :
    (do
        let k ← goldfish_score (M.fg_to_ac n)
          {vote ∈ EarlyVotes M C n s' | no_second_vote_in (LateVotes M C n s') vote = true}
          {vote ∈ EarlyVotes M C n s' | no_second_vote_in (LateVotes M C n s') vote = true} s' X
        pure (decide (voters_count (LateVotes M C n s') < 2 * k)) : DRE Bool) = .ok true := by
  simp only [goldfish_score_eq_ok hRoots, dre_bind_ok]
  have hsub : Hs ⊆ supportersOf (M.fg_to_ac n)
      {vote ∈ EarlyVotes M C n s' | no_second_vote_in (LateVotes M C n s') vote = true}
      {vote ∈ EarlyVotes M C n s' | no_second_vote_in (LateVotes M C n s') vote = true} s' X :=
    fun v hv => mem_supportersOf_of_votesOnceFor (hSup v hv) hXB
  have hc := Finset.card_le_card hsub
  have hle := voters_count_late_le (M := M) (C := C) (n := n) (s' := s')
  show Except.ok _ = Except.ok _
  congr 1
  exact decide_eq_true (by omega)

/-! ## The twins -/

/-- The update of slot `s ≥ 1` saves a confirmation when every member of `Hs` is an early supporter
of the frame's finalized block, every vote of the slot has the slot `s − 1`, and the voters are
fewer than twice `Hs` (the record form of `update_confirmation_saves`).

The variables:
- `M`: the model; `F`: its facts; `C`, `P`: the parameters; `n`, `n'`: the node states before and
  after; `t`: the time; `s`: the slot; `Hs`: the supporters.

Read aloud: a voter majority for the finalized block makes the update save a confirmation. -/
theorem update_confirmation_saves [RootOrder] {M : GoldilocksModel V} (F : Facts M) {C : Config}
    {P : Provisional V} {n n' : M.N} {t : Time} {s : Slot} (Hs : Finset V)
    (hs : 1 ≤ s)
    (hRoots : RootsNameBlocksIn (M.fg_to_ac n).tree)
    (hHs : ∀ v ∈ Hs, EarlySupporterOf M C n (s - 1) (M.fg_to_ac n).F v)
    (hSlot : ∀ vote ∈ M.votesHeldSet n (s - 1), vote.slot = s - 1)
    (hVoters : M.voters_count (M.votesHeldSet n (s - 1)) < 2 * Hs.card)
    (hUpdate : ConfirmationUpdated M C P n t s n') :
    ∃ C' : Block V, n'.savedConfirmation (s - 1) = some C' := by
  rw [voters_count_eq_spec F] at hVoters
  obtain ⟨H, b, hW, hb, hS⟩ := confirmationUpdated_walk F hs hRoots hUpdate
  have hbt : b = true := by
    letI : GoldilocksCorrectness.Statements.Routines.TieBreak V := M.tieBreak
    rcases walkSteps_spec hW.1 with hHF | ⟨-, hel, -⟩
    · subst hHF
      exact Except.ok.inj (hb.symm.trans (eligible_of_supporters hRoots (ancestorEq_refl _)
        (fun v hv => votesOnceFor_of_earlySupporter hSlot (hHs v hv)) hVoters))
    · exact Except.ok.inj (hb.symm.trans hel)
  subst hbt
  exact ⟨H, by rw [hS]; rfl⟩

/-- The update of slot `s ≥ 1` saves a confirmation when every member of `Hs` is an early supporter
of a block `B` of which the frame's finalized block is an ancestor or which it is, every vote of the
slot has the slot `s − 1`, and the voters are fewer than twice `Hs` (the record form of
`update_confirmation_saves_of_supporters`).

The variables:
- `M`: the model; `F`: its facts; `C`, `P`: the parameters; `n`, `n'`: the node states before and
  after; `t`: the time; `s`: the slot; `B`: the block; `Hs`: the supporters.

Read aloud: a voter majority for a descendant of the finalized block makes the update save a
confirmation. -/
theorem update_confirmation_saves_of_supporters [RootOrder] {M : GoldilocksModel V} (F : Facts M)
    {C : Config} {P : Provisional V} {n n' : M.N} {t : Time} {s : Slot} (B : Block V)
    (Hs : Finset V)
    (hs : 1 ≤ s)
    (hRoots : RootsNameBlocksIn (M.fg_to_ac n).tree)
    (hF : (M.fg_to_ac n).F.AncestorEq B)
    (hHs : ∀ v ∈ Hs, EarlySupporterOf M C n (s - 1) B v)
    (hSlot : ∀ vote ∈ M.votesHeldSet n (s - 1), vote.slot = s - 1)
    (hVoters : M.voters_count (M.votesHeldSet n (s - 1)) < 2 * Hs.card)
    (hUpdate : ConfirmationUpdated M C P n t s n') :
    ∃ C' : Block V, n'.savedConfirmation (s - 1) = some C' := by
  rw [voters_count_eq_spec F] at hVoters
  obtain ⟨H, b, hW, hb, hS⟩ := confirmationUpdated_walk F hs hRoots hUpdate
  have hbt : b = true := by
    letI : GoldilocksCorrectness.Statements.Routines.TieBreak V := M.tieBreak
    rcases walkSteps_spec hW.1 with hHF | ⟨-, hel, -⟩
    · subst hHF
      exact Except.ok.inj (hb.symm.trans (eligible_of_supporters hRoots hF
        (fun v hv => votesOnceFor_of_earlySupporter hSlot (hHs v hv)) hVoters))
    · exact Except.ok.inj (hb.symm.trans hel)
  subst hbt
  exact ⟨H, by rw [hS]; rfl⟩

/-- A confirmation the update of slot `s' + 1` saves for slot `s'` is supported by a member of
every voter majority `Hs`, each member with exactly one slot-`s'` vote `vote u`, stamped strictly
before `C.t_ s' + 6 · C.Δ` (the record form of `update_confirmation_supporter`).

The variables:
- `M`: the model; `F`: its facts; `C`, `P`: the parameters; `n`, `n'`: the node states before and
  after; `t`: the time; `s'`: the slot of the votes; `Hs`: the voters; `vote`: each voter's vote;
  `X`: the confirmation.

Read aloud: a saved confirmation is supported by a member of every voter majority. -/
theorem update_confirmation_supporter [RootOrder] {M : GoldilocksModel V} (F : Facts M)
    {C : Config} {P : Provisional V} {n n' : M.N} {t : Time} {s' : Slot} (Hs : Finset V)
    (vote : V → GoldfishVote V)
    (hRoots : RootsNameBlocksIn (M.fg_to_ac n).tree)
    (hHs : ∀ u ∈ Hs, vote u ∈ M.votesHeldSet n s' ∧ (vote u).val_index = u ∧
      (∃ τ : Stamp, n.voteStamp (vote u) = some τ ∧
        τ < ((C.t_ s' + 6 * C.Δ : Time) : Stamp)) ∧
      ∀ vote' ∈ M.votesHeldSet n s', vote'.val_index = u → vote' = vote u)
    (hVoters : M.voters_count (M.votesHeldSet n s') < 2 * Hs.card)
    (hUpdate : ConfirmationUpdated M C P n t (s' + 1) n') (X : Block V)
    (hX : n'.savedConfirmation s' = some X) :
    ∃ u ∈ Hs, ∃ H ∈ (M.fg_to_ac n).tree, H.root = (vote u).head ∧ X.AncestorEq H := by
  rw [voters_count_eq_spec F] at hVoters
  obtain ⟨H, b, -, hb, hsaved⟩ :=
    confirmationUpdated_walk F (Nat.le_add_left 1 s') hRoots hUpdate
  simp only [Nat.add_sub_cancel] at hb hsaved
  rw [hX] at hsaved
  cases b with
  | false => simp at hsaved
  | true =>
  simp only [if_true, Option.some.injEq] at hsaved
  subst hsaved
  set sv := {vt ∈ EarlyVotes M C n s' | no_second_vote_in (LateVotes M C n s') vt = true} with hsv
  have hsvLate : sv ⊆ LateVotes M C n s' :=
    fun vt hv => earlyVotes_subset_lateVotes (Finset.mem_filter.1 hv).1
  have hsvPool : sv ⊆ M.votesHeldSet n s' := fun vt hv => lateVotes_subset (hsvLate hv)
  rw [goldfish_score_eq_ok hRoots] at hb
  simp only [dre_bind_ok] at hb
  have hb' : (Except.ok (decide (voters_count (LateVotes M C n s') < 2 * ((equivocators sv).card +
      (supportersOf (M.fg_to_ac n) sv sv s' X).card))) : DRE Bool) = Except.ok true := hb
  injection hb' with hb''
  have htest := of_decide_eq_true hb''
  by_contra hno
  push Not at hno
  have hPart : ∀ (u : V) (vt : GoldfishVote V), vt ∈ LateVotes M C n s' → vt.val_index = u →
      u ∈ participants (LateVotes M C n s') :=
    fun u vt hv hvu => (mem_participants_iff _ _).2 ⟨vt, hv, hvu⟩
  have hHsP : Hs ⊆ participants (LateVotes M C n s') := by
    intro u hu
    obtain ⟨hp, hval, ⟨τ, hτ, hτlt⟩, -⟩ := hHs u hu
    exact hPart u (vote u) (mem_lateVotes.2 ⟨hp, τ, hτ, hτlt⟩) hval
  have hEq : equivocators sv ⊆ participants (LateVotes M C n s') \ Hs := by
    intro u hu
    rw [mem_equivocators_iff] at hu
    obtain ⟨vt, hvt⟩ : (votes_by sv u).Nonempty := Finset.card_pos.1 (by omega)
    have hvt' := Finset.mem_filter.1 hvt
    refine Finset.mem_sdiff.2 ⟨hPart u vt (hsvLate hvt'.1) hvt'.2, fun huH => ?_⟩
    have hle : (votes_by sv u).card ≤ 1 := by
      refine Finset.card_le_one.2 (fun a ha c hc => ?_)
      have ha' := Finset.mem_filter.1 ha
      have hc' := Finset.mem_filter.1 hc
      rw [(hHs u huH).2.2.2 a (hsvPool ha'.1) ha'.2, (hHs u huH).2.2.2 c (hsvPool hc'.1) hc'.2]
    omega
  have hSupp : supportersOf (M.fg_to_ac n) sv sv s' X ⊆
      participants (LateVotes M C n s') \ Hs := by
    intro u hu
    obtain ⟨vt, hvt, hval, -, -, H', hH', hr, hXH⟩ := (mem_supportersOf_iff _ _ _ _ _ _).1 hu
    refine Finset.mem_sdiff.2 ⟨hPart u vt (hsvLate hvt) hval, fun huH => ?_⟩
    have hvv := (hHs u huH).2.2.2 vt (hsvPool hvt) hval
    rw [hvv] at hr
    exact hno u huH H' hH' hr hXH
  have hDisj : Disjoint (equivocators sv) (supportersOf (M.fg_to_ac n) sv sv s' X) := by
    rw [Finset.disjoint_left]
    intro u hu hu'
    obtain ⟨vt, -, hval, hne, -⟩ := (mem_supportersOf_iff _ _ _ _ _ _).1 hu'
    exact hne hu
  have hUnion := Finset.card_union_of_disjoint hDisj
  have hle := Finset.card_le_card (Finset.union_subset hEq hSupp)
  have hsd := Finset.card_sdiff_add_card_eq_card hHsP
  have hNpool := voters_count_late_le (M := M) (C := C) (n := n) (s' := s')
  rw [voters_count_eq, voters_count_eq] at hNpool
  rw [voters_count_eq] at htest hVoters
  omega

/-- A confirmation the update of slot `s ≥ 1` saves is compatible with `B`, when every member of
`Hs` has exactly one slot-`(s − 1)` vote, stamped strictly before `C.t_ (s − 1) + 6 · C.Δ`, whose
head blocks are compatible with `B`, and the voters are fewer than twice `Hs` (the record form of
`lem77c_update_confirmation_compatible_of_majority`).

The variables:
- `M`: the model; `F`: its facts; `C`, `P`: the parameters; `n`, `n'`: the node states before and
  after; `t`: the time; `s`: the slot; `B`: the block; `Hs`: the voters.

Read aloud: a majority voting compatibly with `B` makes the saved confirmation compatible with
`B`. -/
theorem lem77c_update_confirmation_compatible_of_majority [RootOrder] {M : GoldilocksModel V}
    (F : Facts M) {C : Config} {P : Provisional V} {n n' : M.N} {t : Time} {s : Slot}
    (B : Block V) (Hs : Finset V)
    (hs : 1 ≤ s)
    (hRoots : RootsNameBlocksIn (M.fg_to_ac n).tree)
    (hHs : ∀ u ∈ Hs, ∃ vote ∈ M.votesHeldSet n (s - 1), vote.val_index = u ∧
      (∃ τ : Stamp, n.voteStamp vote = some τ ∧
        τ < ((C.t_ (s - 1) + 6 * C.Δ : Time) : Stamp)) ∧
      (∀ vote' ∈ M.votesHeldSet n (s - 1), vote'.val_index = u → vote' = vote) ∧
      ∀ D ∈ (M.fg_to_ac n).tree, D.root = vote.head → D.compatible B = true)
    (hVoters : M.voters_count (M.votesHeldSet n (s - 1)) < 2 * Hs.card)
    (hUpdate : ConfirmationUpdated M C P n t s n') :
    ∀ C' : Block V, n'.savedConfirmation (s - 1) = some C' → C'.compatible B = true := by
  intro C' hC'
  rw [voters_count_eq_spec F] at hVoters
  obtain ⟨H, b, -, hb, hsaved⟩ := confirmationUpdated_walk F hs hRoots hUpdate
  rw [hsaved] at hC'
  split at hC'
  case isFalse => cases hC'
  case isTrue hbt =>
  cases hC'
  subst hbt
  by_contra hHB
  simp only [goldfish_score_eq_ok hRoots, dre_bind_ok, pure, Except.pure, Except.ok.injEq,
    decide_eq_true_eq] at hb
  set early := EarlyVotes M C n (s - 1)
  set late := LateVotes M C n (s - 1)
  have hLatePool : late ⊆ M.votesHeldSet n (s - 1) := lateVotes_subset
  have hSupLate : {vote ∈ early | no_second_vote_in late vote = true} ⊆ late :=
    fun vote hv => earlyVotes_subset_lateVotes (Finset.mem_filter.1 hv).1
  have hHsLate : Hs ⊆ participants late := by
    intro u hu
    obtain ⟨vote, hp, hval, ⟨τ, hts, hlt⟩, -, -⟩ := hHs u hu
    exact (mem_participants_iff _ _).2 ⟨vote, mem_lateVotes.2 ⟨hp, τ, hts, hlt⟩, hval⟩
  have hHsEq : Disjoint Hs (equivocators {vote ∈ early | no_second_vote_in late vote = true}) := by
    rw [Finset.disjoint_left]
    intro u hu
    obtain ⟨vote, -, -, -, huniq, -⟩ := hHs u hu
    exact not_mem_equivocators_of_unique fun vote' hv' hval' =>
      huniq vote' (hLatePool (hSupLate hv')) hval'
  have hHsSup : Disjoint (supportersOf (M.fg_to_ac n)
      {vote ∈ early | no_second_vote_in late vote = true}
      {vote ∈ early | no_second_vote_in late vote = true} (s - 1) C') Hs := by
    rw [Finset.disjoint_right]
    intro u hu hmem
    obtain ⟨vote, -, -, -, huniq, hroot⟩ := hHs u hu
    obtain ⟨vote', hv', hval', -, -, D, hD, hDr, hHD⟩ := (mem_supportersOf_iff _ _ _ _ _ _).1 hmem
    have hvv : vote' = vote := huniq vote' (hLatePool (hSupLate hv')) hval'
    subst hvv
    exact hHB (compatible_of_ancestorEq_compatible hHD (hroot D hD hDr))
  have hsub : equivocators {vote ∈ early | no_second_vote_in late vote = true} ∪
      supportersOf (M.fg_to_ac n) {vote ∈ early | no_second_vote_in late vote = true}
        {vote ∈ early | no_second_vote_in late vote = true} (s - 1) C' ∪ Hs ⊆
      participants late := by
    refine Finset.union_subset (Finset.union_subset ?_ ?_) hHsLate
    · intro u hu
      obtain ⟨vote, hv, hval⟩ :=
        (mem_participants_iff _ _).1 (equivocators_subset_participants _ hu)
      exact (mem_participants_iff _ _).2 ⟨vote, hSupLate hv, hval⟩
    · intro u hu
      obtain ⟨vote, hv, hval⟩ :=
        (mem_participants_iff _ _).1 (supportersOf_subset_participants (subset_refl _) hu)
      exact (mem_participants_iff _ _).2 ⟨vote, hSupLate hv, hval⟩
  have h1 : Disjoint (equivocators {vote ∈ early | no_second_vote_in late vote = true})
      (supportersOf (M.fg_to_ac n) {vote ∈ early | no_second_vote_in late vote = true}
        {vote ∈ early | no_second_vote_in late vote = true} (s - 1) C') :=
    disjoint_supportersOf_equivocators.symm
  have h2 : Disjoint (equivocators {vote ∈ early | no_second_vote_in late vote = true} ∪
      supportersOf (M.fg_to_ac n) {vote ∈ early | no_second_vote_in late vote = true}
        {vote ∈ early | no_second_vote_in late vote = true} (s - 1) C') Hs :=
    Finset.disjoint_union_left.2 ⟨hHsEq.symm, hHsSup⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint h2, Finset.card_union_of_disjoint h1] at hcard
  have hNle : voters_count late ≤ voters_count (M.votesHeldSet n (s - 1)) := voters_count_late_le
  rw [voters_count_eq, voters_count_eq] at hNle
  rw [voters_count_eq] at hb hVoters
  omega

/-- **Lemma 36 over the record.** When the update of slot `s ≥ 1` saves `C'`, every block `L` that
is `C'` or an ancestor of `C'` has a set `Sup` of early supporters whose double outnumbers the
slot's voters, and, when `L` is a fast block of `n'`, the committee of slot `s − 1`; this when no
two blocks of the frame's tree share a root and every vote of the slot is stamped strictly before
`C.t_ (s − 1) + 6 · C.Δ` (the record form of `lem36_confirmed_ancestor_early_supporters`).

The variables:
- `M`: the model; `F`: its facts; `C`, `P`: the parameters; `n`, `n'`: the node states before and
  after; `t`: the time; `s`: the slot; `C'`: the saved confirmation; `L`: the block.

Read aloud: a confirmed block's ancestors have early supporters. -/
theorem lem36_confirmed_ancestor_early_supporters [RootOrder] {M : GoldilocksModel V}
    (F : Facts M) {C : Config} {P : Provisional V} {n n' : M.N} {t : Time} {s : Slot}
    (C' L : Block V)
    -- the slot is not the first
    (hs : 1 ≤ s)
    -- no two blocks of the frame's tree share a root
    (hRoots : RootsNameBlocksIn (M.fg_to_ac n).tree)
    -- every vote of the slot is stamped strictly before the late cutoff
    (hLate : ∀ vote ∈ M.votesHeldSet n (s - 1), ∃ τ : Stamp, n.voteStamp vote = some τ ∧
      τ < ((C.t_ (s - 1) + 6 * C.Δ : Time) : Stamp))
    -- the update leaves `n'` and saves `C'`
    (hUpdate : ConfirmationUpdated M C P n t s n')
    (hSaved : n'.savedConfirmation (s - 1) = some C')
    -- `L` is `C'` or an ancestor of `C'`
    (hLC : L.AncestorEq C') :
    ∃ Sup : Finset V, (∀ u ∈ Sup, EarlySupporterOf M C n (s - 1) L u) ∧
      M.voters_count (M.votesHeldSet n (s - 1)) < 2 * Sup.card ∧
      (L ∈ n'.fastBlocks → (P.committee (s - 1)).card ≤ 2 * Sup.card) := by
  rw [voters_count_eq_spec F]
  obtain ⟨H, b, -, hb, hS⟩ := confirmationUpdated_walk F hs hRoots hUpdate
  rw [hSaved] at hS
  cases b with
  | false => simp at hS
  | true =>
  simp only [if_true, Option.some.injEq] at hS
  subst hS
  have hel : voters_count (LateVotes M C n (s - 1)) <
      2 * ((equivocators {vote ∈ EarlyVotes M C n (s - 1) |
          no_second_vote_in (LateVotes M C n (s - 1)) vote = true}).card +
        (supportersOf (M.fg_to_ac n)
          {vote ∈ EarlyVotes M C n (s - 1) | no_second_vote_in (LateVotes M C n (s - 1)) vote = true}
          {vote ∈ EarlyVotes M C n (s - 1) | no_second_vote_in (LateVotes M C n (s - 1)) vote = true}
          (s - 1) C').card) := by
    simp only [goldfish_score_eq_ok hRoots, dre_bind_ok, pure, Except.pure, Except.ok.injEq,
      decide_eq_true_eq] at hb
    exact hb
  have hEq := equivocators_support_eq_empty (EarlyVotes M C n (s - 1)) (LateVotes M C n (s - 1))
    earlyVotes_subset_lateVotes
  rw [hEq, Finset.card_empty, zero_add] at hel
  have hLP : LateVotes M C n (s - 1) = M.votesHeldSet n (s - 1) := by
    ext vote
    exact ⟨fun hv => lateVotes_subset hv, fun hv => mem_lateVotes.2 ⟨hv, hLate vote hv⟩⟩
  refine ⟨supportersOf (M.fg_to_ac n)
    {vote ∈ EarlyVotes M C n (s - 1) | no_second_vote_in (LateVotes M C n (s - 1)) vote = true}
    {vote ∈ EarlyVotes M C n (s - 1) | no_second_vote_in (LateVotes M C n (s - 1)) vote = true}
    (s - 1) L, ?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨vote, hvote, hval, -, -, hH⟩ := (mem_supportersOf_iff _ _ _ _ _ _).1 hu
    obtain ⟨hvE, hN⟩ := Finset.mem_filter.1 hvote
    obtain ⟨hvp, x, hx, hxl⟩ := mem_earlyVotes.1 hvE
    refine ⟨vote, hvp, hval, hH, ⟨x, hx, (occurrenceBefore_eq_true_iff _ _).2 ⟨x, rfl, hxl⟩⟩, ?_⟩
    intro vote' hvote' hval'
    simp only [no_second_vote_in, decide_eq_true_eq] at hN
    rcases hN vote' (hLP ▸ hvote') with h | h
    · exact h
    · exact absurd (hval'.trans hval.symm) h
  · have hle := Finset.card_le_card (supportersOf_mono (Φ := M.fg_to_ac n)
      (votes := {vote ∈ EarlyVotes M C n (s - 1) |
        no_second_vote_in (LateVotes M C n (s - 1)) vote = true})
      (support_votes := {vote ∈ EarlyVotes M C n (s - 1) |
        no_second_vote_in (LateVotes M C n (s - 1)) vote = true}) (s := s - 1) hLC)
    rw [← hLP]
    omega
  · intro hL
    obtain ⟨H', -, -, -, -, -, hf⟩ := confirmationUpdated_fast_cases hs hUpdate hL
    rw [supportVotes_eq F, fast_test_eq_ok_true_iff P hRoots, hEq, Finset.card_empty,
      zero_add] at hf
    exact hf

/-- **Lemmas 25 and 28 over the record.** The update of slot `s ≥ 1` saves `B`, a non-genesis block
of the frame's tree on the chain from the frame's finalized block, and advances the record of the
confirmed tip with it, when every member of `Hs` has exactly one slot-`(s − 1)` vote, early, with
head `B`, every vote of the slot has the slot `s − 1`, the voters are fewer than twice `Hs`, and
every live lock entry is compatible with `B`; when the committee is at most twice `Hs`, `B` is also
a fast block and `n'` holds a lock entry on `B` with the deadline `C.t_ (s − 1 + C.k) + 5 · C.Δ`
(the record form of `update_confirmation_of_voter_majority`).

The variables:
- `M`: the model; `F`: its facts; `C`, `P`: the parameters; `n`, `n'`: the node states before and
  after; `t`: the time; `s`: the slot; `B`: the block; `Hs`: the voters.

Read aloud: an early unanimous majority makes the update confirm, and with half the committee
lock, its block. -/
theorem update_confirmation_of_voter_majority [RootOrder] {M : GoldilocksModel V} (F : Facts M)
    {C : Config} {P : Provisional V} {n n' : M.N} {t : Time} {s : Slot} (B : Block V)
    (Hs : Finset V)
    (hs : 1 ≤ s)
    (hRoots : RootsNameBlocksIn (M.fg_to_ac n).tree)
    (hBne : B ≠ Block.genesis)
    (hF : (M.fg_to_ac n).F.AncestorEq B)
    (hPathF : ∀ P' : Block V, (M.fg_to_ac n).F.AncestorEq P' → P'.AncestorEq B →
      P' ∈ (M.fg_to_ac n).tree)
    (hHs : ∀ v ∈ Hs, EarlyVoteOnceFor M C n (s - 1) B v)
    (hSlot : ∀ vote ∈ M.votesHeldSet n (s - 1), vote.slot = s - 1)
    (hVoters : M.voters_count (M.votesHeldSet n (s - 1)) < 2 * Hs.card)
    (hNoVeto : ∀ e ∈ n.lockEntries, M.is_live n t e = true → e.B.compatible B = true)
    (hUpdate : ConfirmationUpdated M C P n t s n') :
    n'.savedConfirmation (s - 1) = some B ∧
      n'.latestConfirmed = M.advance (M.fg_to_ac n) n.latestConfirmed (some B) ∧
      ((P.committee (s - 1)).card ≤ 2 * Hs.card →
        B ∈ n'.fastBlocks ∧
        ∃ e ∈ n'.lockEntries, e.B = B ∧ e.d = C.t_ (s - 1 + C.k) + 5 * C.Δ) := by
  rw [voters_count_eq_spec F] at hVoters
  have hB : B ∈ (M.fg_to_ac n).tree := hPathF B hF (ancestorEq_refl B)
  obtain ⟨H, b, hW, hb, hS⟩ := confirmationUpdated_walk F hs hRoots hUpdate
  set early := EarlyVotes M C n (s - 1) with hearly
  set late := LateVotes M C n (s - 1) with hlate
  have hLatePool : late ⊆ M.votesHeldSet n (s - 1) := lateVotes_subset
  have hSupLate : {vote ∈ early | no_second_vote_in late vote = true} ⊆ late :=
    fun vote hv => earlyVotes_subset_lateVotes (Finset.mem_filter.1 hv).1
  have hSupPool : {vote ∈ early | no_second_vote_in late vote = true} ⊆
      M.votesHeldSet n (s - 1) := fun vote hv => hLatePool (hSupLate hv)
  have hMem : ∀ v ∈ Hs, ∃ vote ∈ {vote ∈ early | no_second_vote_in late vote = true},
      vote.val_index = v ∧ vote.slot = s - 1 ∧ vote.head = B.root ∧
      ∀ vote' ∈ {vote ∈ early | no_second_vote_in late vote = true},
        vote'.val_index = v → vote' = vote := by
    intro v hv
    obtain ⟨vote, hvote, hval, hhead, ⟨x, hx, hxo⟩, hu⟩ := hHs v hv
    obtain ⟨y, hy, hlt⟩ := (occurrenceBefore_eq_true_iff _ _).1 hxo
    obtain rfl := Option.some.inj hy
    have hE : vote ∈ early := mem_earlyVotes.2 ⟨hvote, x, hx, hlt⟩
    have hN : no_second_vote_in late vote = true := by
      simp only [no_second_vote_in, decide_eq_true_eq]
      intro u hu'
      by_cases huv : u.val_index = vote.val_index
      · exact Or.inl (hu u (hLatePool hu') (huv.trans hval))
      · exact Or.inr huv
    refine ⟨vote, Finset.mem_filter.2 ⟨hE, hN⟩, hval, hSlot vote hvote, hhead, ?_⟩
    intro vote' hv' hval'
    exact hu vote' (hSupPool hv') hval'
  have hNle : voters_count late ≤ voters_count (M.votesHeldSet n (s - 1)) := voters_count_late_le
  have hSupLe : voters_count {vote ∈ early | no_second_vote_in late vote = true} ≤
      voters_count late := by
    rw [voters_count_eq, voters_count_eq]
    refine Finset.card_le_card fun v hv => ?_
    obtain ⟨vote, hvote, hval⟩ := (mem_participants_iff _ _).1 hv
    exact (mem_participants_iff _ _).2 ⟨vote, hSupLate hvote, hval⟩
  -- the walk ends at `B`
  have hHB : H = B := by
    letI : GoldilocksCorrectness.Statements.Routines.TieBreak V := M.tieBreak
    exact GoldilocksCorrectness.Proofs.Routines.lem4_walkEnd_ends_at_unanimous_block
      (M.fg_to_ac n) {vote ∈ early | no_second_vote_in late vote = true}
      {vote ∈ early | no_second_vote_in late vote = true} (s - 1) (voters_count late)
      (M.fg_to_ac n).F B H (M.fg_to_ac n).tree Hs hF
      (fun P' hFP' _ hP'B => hPathF P' hFP' hP'B) hRoots (subset_refl _) hMem hB hSupLe
      (by omega) hW
  subst hHB
  -- `B` scores at least `Hs`
  have hSupB : Hs ⊆ supportersOf (M.fg_to_ac n)
      {vote ∈ early | no_second_vote_in late vote = true}
      {vote ∈ early | no_second_vote_in late vote = true} (s - 1) H := by
    intro v hv
    obtain ⟨vote, hvote, hval, hslot, hhead, hu⟩ := hMem v hv
    exact mem_supportersOf_of_votesOnceFor
      ⟨vote, hvote, hval, hslot, ⟨H, hB, hhead.symm, ancestorEq_refl H⟩, hu⟩ (ancestorEq_refl H)
  have hcard := Finset.card_le_card hSupB
  have hbt : b = true := by
    rw [goldfish_score_eq_ok hRoots] at hb
    simp only [dre_bind_ok] at hb
    have hb' := Except.ok.inj hb
    rw [← hb']
    exact decide_eq_true (by omega)
  subst hbt
  have hSaved : n'.savedConfirmation (s - 1) = some H := by rw [hS]; rfl
  have hv : M.live_lock_vetoes n t H = false := by
    rw [F.rd.live_lock_vetoes_eq, decide_eq_false_iff_not]
    rintro ⟨e, he, hl, hc⟩
    exact ((GoldilocksCorrectness.Proofs.Routines.conflicts_iff _ _).1 hc) (hNoVeto e he hl)
  obtain ⟨-, -, -, hv0⟩ := confirmationUpdated_saved_some hs hUpdate hSaved
  obtain ⟨hlat, hfast, -, hlock⟩ := hv0 hv
  refine ⟨hSaved, hlat, fun hHalf => ?_⟩
  have hft : fast_test P (M.fg_to_ac n) (SupportVotes M C n (s - 1)) (s - 1) H = .ok true := by
    rw [supportVotes_eq F, fast_test_eq_ok_true_iff P hRoots, ← hearly, ← hlate]
    omega
  have hL : Lockable M C P n (s - 1) H H := ⟨hB, hBne, ancestorEq_refl H, Or.inl hft⟩
  exact ⟨(hfast H).2 ⟨hB, hBne, ancestorEq_refl H, hft⟩,
    (hlock H hL fun _ h => h.2.2.1).2.2⟩

/-- **Lemma 77 over the record.** The confirmation the update of slot `s ≥ 1` saves, when it saves
one, is `B` or a descendant of `B`, when no two blocks of the frame's tree share a root, the frame's
finalized block is `B` or an ancestor of `B` with every block between them in the frame's tree,
every member of `Hs` is an early supporter of `B`, every vote of the slot has the slot `s − 1`, and
the voters are fewer than twice `Hs` (the record form of
`lem77_update_confirmation_extends_voter_majority_chain`).

The variables:
- `M`: the model; `F`: its facts; `C`, `P`: the parameters; `n`, `n'`: the node states before and
  after; `t`: the time; `s`: the slot; `B`: the block; `Hs`: the supporters.

Read aloud: the saved confirmation extends a voter majority's chain. -/
theorem lem77_update_confirmation_extends_voter_majority_chain [RootOrder]
    {M : GoldilocksModel V} (F : Facts M) {C : Config} {P : Provisional V} {n n' : M.N}
    {t : Time} {s : Slot} (B : Block V) (Hs : Finset V)
    (hs : 1 ≤ s)
    (hRoots : RootsNameBlocksIn (M.fg_to_ac n).tree)
    (hF : (M.fg_to_ac n).F.AncestorEq B)
    (hPathF : ∀ P' : Block V, (M.fg_to_ac n).F.AncestorEq P' → P'.AncestorEq B →
      P' ∈ (M.fg_to_ac n).tree)
    (hHs : ∀ v ∈ Hs, EarlySupporterOf M C n (s - 1) B v)
    (hSlot : ∀ vote ∈ M.votesHeldSet n (s - 1), vote.slot = s - 1)
    (hVoters : M.voters_count (M.votesHeldSet n (s - 1)) < 2 * Hs.card)
    (hUpdate : ConfirmationUpdated M C P n t s n') :
    ∀ C' : Block V, n'.savedConfirmation (s - 1) = some C' → B.AncestorEq C' := by
  intro C' hC'
  rw [voters_count_eq_spec F] at hVoters
  obtain ⟨H, b, hW, -, hS⟩ := confirmationUpdated_walk F hs hRoots hUpdate
  set early := EarlyVotes M C n (s - 1) with hearly
  set late := LateVotes M C n (s - 1) with hlate
  have hSupLate : {vote ∈ early | no_second_vote_in late vote = true} ⊆ late :=
    fun vote hv => earlyVotes_subset_lateVotes (Finset.mem_filter.1 hv).1
  have hMem : ∀ v ∈ Hs, VotesOnceFor (M.fg_to_ac n)
      {vote ∈ early | no_second_vote_in late vote = true}
      {vote ∈ early | no_second_vote_in late vote = true} (s - 1) B v :=
    fun v hv => votesOnceFor_of_earlySupporter hSlot (hHs v hv)
  have hNle : voters_count late ≤ voters_count (M.votesHeldSet n (s - 1)) := voters_count_late_le
  have hSupLe : voters_count {vote ∈ early | no_second_vote_in late vote = true} ≤
      voters_count late := by
    rw [voters_count_eq, voters_count_eq]
    refine Finset.card_le_card fun v hv => ?_
    obtain ⟨vote, hvote, hval⟩ := (mem_participants_iff _ _).1 hv
    exact (mem_participants_iff _ _).2 ⟨vote, hSupLate hvote, hval⟩
  have hBH : B.AncestorEq H := by
    letI : GoldilocksCorrectness.Statements.Routines.TieBreak V := M.tieBreak
    exact GoldilocksCorrectness.Proofs.Routines.lem1_walkEnd_extends_majority_block
      (M.fg_to_ac n) {vote ∈ early | no_second_vote_in late vote = true}
      {vote ∈ early | no_second_vote_in late vote = true} (s - 1) _ (voters_count late)
      (M.fg_to_ac n).F B H (M.fg_to_ac n).tree Hs
      (Or.inr ⟨hF, fun P' hFP' _ hP'B => hPathF P' hFP' hP'B⟩) hRoots (subset_refl _) hMem
      (by omega) (by omega)
      (fun D => ⟨_, by simp only [goldfish_score_eq_ok hRoots, dre_bind_ok]; rfl⟩)
      (fun D _ _ _ k hk hlt => by
        simp only [hk, dre_bind_ok]
        show Except.ok _ = Except.ok _
        rw [decide_eq_true hlt])
      hW
  rw [hS] at hC'
  split at hC'
  · cases hC'
    exact hBH
  · cases hC'

/-! ## At the spec's model -/

/-- The landed `GoldilocksCorrectness.Proofs.Routines.update_confirmation_saves`, recovered from its
record form at the spec's model, at the AC state `n.A` and the frame `fg_to_ac n.S` of every node
state `n` whose frame's tree has no two blocks sharing a root and whose lock entries all have a
deadline after `t`.

Read aloud: the landed theorem holds at every such node state. -/
theorem update_confirmation_saves_recovered {V : Type} [DecidableEq V] [Fintype V] [RootOrder] :
    ∀ (C : Config) (P : Provisional V) (n : NodeState V) (A' : ACState V) (t : Time) (s : Slot) (Hs : Finset V),
      (RootsNameBlocksIn (fg_to_ac n.S).tree ∧ ∀ e ∈ n.A.lock_entries, t < e.d) →
      type_of% (@GoldilocksCorrectness.Proofs.Routines.update_confirmation_saves V _ _ _ C P n.A A' (fg_to_ac n.S) t s Hs) := by
  intro C P n A' t s Hs hH hs hRoots hHs hSlot hVoters hUpdate
  exact update_confirmation_saves goldilocksFacts (n' := { n with A := A' }) Hs hs hRoots
    (fun v hv => (goldilocks_earlySupporterOf C n (s - 1) _ v hRoots).1 (hHs v hv)) hSlot hVoters
    (confirmationUpdated_at_node C P n t s A' hH hUpdate)

/-- The landed `GoldilocksCorrectness.Proofs.Routines.update_confirmation_supporter`, recovered from
its record form at the spec's model, at the AC state `n.A` and the frame `fg_to_ac n.S` of every
node state `n` whose frame's tree has no two blocks sharing a root and whose lock entries all have
a deadline after `t`.

Read aloud: the landed theorem holds at every such node state. -/
theorem update_confirmation_supporter_recovered {V : Type} [DecidableEq V] [Fintype V] [RootOrder] :
    ∀ (C : Config) (P : Provisional V) (n : NodeState V) (A' : ACState V) (t : Time) (s' : Slot) (Hs : Finset V) (vote : V → GoldfishVote V),
      (RootsNameBlocksIn (fg_to_ac n.S).tree ∧ ∀ e ∈ n.A.lock_entries, t < e.d) →
      type_of% (@GoldilocksCorrectness.Proofs.Routines.update_confirmation_supporter V _ _ _ C P n.A A' (fg_to_ac n.S) t s' Hs vote) := by
  intro C P n A' t s' Hs vote hH hRoots hHs hVoters hUpdate X hX
  exact update_confirmation_supporter goldilocksFacts (n' := { n with A := A' }) Hs vote hRoots
    hHs hVoters (confirmationUpdated_at_node C P n t (s' + 1) A' hH hUpdate) X hX

/-- The landed `GoldilocksCorrectness.Proofs.Routines.update_confirmation_saves_of_supporters`,
recovered from its record form at the spec's model, at the AC state `n.A` and the frame
`fg_to_ac n.S` of every node state `n` whose frame's tree has no two blocks sharing a root and
whose lock entries all have a deadline after `t`.

Read aloud: the landed theorem holds at every such node state. -/
theorem update_confirmation_saves_of_supporters_recovered {V : Type} [DecidableEq V] [Fintype V] [RootOrder] :
    ∀ (C : Config) (P : Provisional V) (n : NodeState V) (A' : ACState V) (t : Time) (s : Slot) (B : Block V) (Hs : Finset V),
      (RootsNameBlocksIn (fg_to_ac n.S).tree ∧ ∀ e ∈ n.A.lock_entries, t < e.d) →
      type_of% (@GoldilocksCorrectness.Proofs.Routines.update_confirmation_saves_of_supporters V _ _ _ C P n.A A' (fg_to_ac n.S) t s B Hs) := by
  intro C P n A' t s B Hs hH hs hRoots hF hHs hSlot hVoters hUpdate
  exact update_confirmation_saves_of_supporters goldilocksFacts (n' := { n with A := A' }) B Hs hs
    hRoots hF (fun v hv => (goldilocks_earlySupporterOf C n (s - 1) _ v hRoots).1 (hHs v hv))
    hSlot hVoters (confirmationUpdated_at_node C P n t s A' hH hUpdate)

/-- The landed `GoldilocksCorrectness.Proofs.Routines.lem77c_update_confirmation_compatible_of_majority`,
recovered from its record form at the spec's model, at the AC state `n.A` and the frame
`fg_to_ac n.S` of every node state `n` whose frame's tree has no two blocks sharing a root and
whose lock entries all have a deadline after `t`.

Read aloud: the landed theorem holds at every such node state. -/
theorem lem77c_update_confirmation_compatible_of_majority_recovered {V : Type} [DecidableEq V] [Fintype V] [RootOrder] :
    ∀ (C : Config) (P : Provisional V) (n : NodeState V) (A' : ACState V) (t : Time) (s : Slot) (B : Block V) (Hs : Finset V),
      (RootsNameBlocksIn (fg_to_ac n.S).tree ∧ ∀ e ∈ n.A.lock_entries, t < e.d) →
      type_of% (@GoldilocksCorrectness.Proofs.Routines.lem77c_update_confirmation_compatible_of_majority V _ _ _ C P n.A A' (fg_to_ac n.S) t s B Hs) := by
  intro C P n A' t s B Hs hH hs hRoots hHs hVoters hUpdate
  exact lem77c_update_confirmation_compatible_of_majority goldilocksFacts
    (n' := { n with A := A' }) B Hs hs hRoots hHs hVoters
    (confirmationUpdated_at_node C P n t s A' hH hUpdate)

end GoldilocksCorrectness.Record.Proofs.Routines
