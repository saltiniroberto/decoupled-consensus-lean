module
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ScoreACStore
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ACStoreDefs
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.ACStoreDefs

@[expose] public section

/-!
# ACStore, over a model

The theorems of `GoldilocksCorrectness/Proofs/Routines/ACStore.lean` on the node's votes and
lock entries, over a model `M` whose facts `F` hold: the relations between two node states
(`VotesInv`, `SlotKeyed`, `ACGrows`, `ACStampsAt`, on `ACStoreDefs.lean`) and their
`refl`, `trans` and `of_keeps` lemmas, and the readers of the votes and of the lock entries
as conditions. The page's theorems on the admission of a Goldfish vote and on the
resolution time `tau` read routines the record has no member for; they are restated with
the receipt's and the tick's families.

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
open GoldilocksCorrectness.Record.Statements.Routines (PoolKeyed PoolStamped)
open GoldilocksCorrectness.Record.Proofs.Routines (VotesInv KeepsVotes SlotKeyed ACGrows
  ACStampsAt)
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn VotesOnceFor)

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded in the goal and in every
hypothesis: `omega` does not see a fact stated at either. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

variable {V : Type} [DecidableEq V] [Fintype V]

section

variable (M : GoldilocksModel V) (F : Facts M)
include M F

/-- A validator is an equivocator of `votes` exactly when `votes` holds two distinct votes of it.

The variables:
- `M`: the model; `F`: its facts;
- `votes`: the votes; `v`: the validator.

Read aloud: `v` is an equivocator of `votes` exactly when `votes` holds two distinct votes of `v`. -/
theorem mem_equivocators_iff_two (votes : Finset (GoldfishVote V)) (v : V) :
    v ∈ M.equivocators votes ↔
      ∃ v₁ ∈ votes, ∃ v₂ ∈ votes, v₁ ≠ v₂ ∧ v₁.val_index = v ∧ v₂.val_index = v := by
  rw [(mem_equivocators_iff M F)]
  constructor
  · intro h
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h
    simp only [F.rd.votes_by_eq, Finset.mem_filter] at ha hb
    exact ⟨a, ha.1, b, hb.1, hab, ha.2, hb.2⟩
  · rintro ⟨v₁, h₁, v₂, h₂, hne, hi₁, hi₂⟩
    refine Finset.one_lt_card.mpr ⟨v₁, ?_, v₂, ?_, hne⟩
    · simp only [F.rd.votes_by_eq, Finset.mem_filter]
      exact ⟨h₁, hi₁⟩
    · simp only [F.rd.votes_by_eq, Finset.mem_filter]
      exact ⟨h₂, hi₂⟩

/-- `VotesInv` holds of an AC state with the same pool and vote stamps.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: `VotesInv` holds of an AC state with the same pool and vote stamps. -/
theorem VotesInv.of_keeps {P : Provisional V} {n n' : M.N} {t : Time}
    (hk : KeepsVotes M n n') (h : VotesInv M P n t) :
    VotesInv M P n' t := by
  obtain ⟨h1, h2, -⟩ := hk
  unfold VotesInv PoolKeyed PoolStamped
  rw [h1, h2]
  exact h

/-- `VotesInv` at a time holds at every later time.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: `VotesInv` at a time holds at every later time. -/
theorem VotesInv.mono {P : Provisional V} {n : M.N} {t t' : Time}
    (h : VotesInv M P n t) (ht : t ≤ t') :
    VotesInv M P n t' := by
  refine ⟨h.1, h.2.1, fun s vote hv τ hτ => ?_⟩
  exact le_trans (h.2.2 s vote hv τ hτ) (WithBot.coe_le_coe.mpr ht)

/-- An AC state holds nothing of votes beyond itself.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: an AC state holds nothing of votes beyond itself. -/
theorem ACStampsAt.refl (n : M.N) (τ : Time) :
    ACStampsAt M n n τ :=
  fun _ _ hv hn => absurd hv hn

/-- An AC state with the same pool holds nothing of votes beyond `n`.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: an AC state with the same pool holds nothing of votes beyond `n`. -/
theorem ACStampsAt.of_keeps {n n' : M.N} (hk : KeepsVotes M n n') (τ : Time) :
    ACStampsAt M n n' τ := by
  intro s vote hv hn
  rw [hk.1] at hv
  exact absurd hv hn

/-- `ACStampsAt` at one time composes along `ACGrows`: a vote beyond `n` in `n''` is beyond `n`
in `n'`, stamped `τ` there and kept, or beyond `n'` in `n''`.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: what `n''` holds of votes beyond `n` is stamped `τ`, when it is so from `n` to `n'` and from `n'` to `n''` and `n''` holds `n'`'s votes. -/
theorem ACStampsAt.trans {n n' n'' : M.N} {τ : Time} (h : ACStampsAt M n n' τ)
    (hg : ACGrows M n' n'') (h' : ACStampsAt M n' n'' τ) :
    ACStampsAt M n n'' τ := by
  intro s vote hv hn
  by_cases hv' : vote ∈ n'.votesHeld s
  · rw [hg.2 s vote hv']
    exact h s vote hv' hn
  · exact h' s vote hv hv'

/-- The pool filed by slot and committee is filed by slot.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: a pool filed by slot and committee is filed by slot. -/
theorem SlotKeyed.of_poolKeyed {P : Provisional V} {n : M.N} (h : PoolKeyed M P n) :
    SlotKeyed M n :=
  fun s vote hv => (h s vote hv).1

/-- An AC state holds its own votes and stamps.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: an AC state holds its own votes and stamps. -/
theorem ACGrows.refl (n : M.N) :
    ACGrows M n n :=
  ⟨fun _ => List.prefix_refl _, fun _ _ _ => rfl⟩

/-- `ACGrows` is transitive: a vote of the first state's pool is in the second's.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: `n''` holds `n`'s votes and stamps when `n'` holds `n`'s and `n''` holds `n'`'s. -/
theorem ACGrows.trans {n n' n'' : M.N} (h : ACGrows M n n') (h' : ACGrows M n' n'') :
    ACGrows M n n'' :=
  ⟨fun s => (h.1 s).trans (h'.1 s), fun s vote hv => by
    rw [h'.2 s vote ((h.1 s).subset hv), h.2 s vote hv]⟩

/-- An AC state with the same pool and vote stamps holds `n`'s votes and stamps.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: an AC state with the same pool and vote stamps holds `n`'s votes and stamps. -/
theorem ACGrows.of_keeps {n n' : M.N} (hk : KeepsVotes M n n') :
    ACGrows M n n' := by
  obtain ⟨h1, h2, -⟩ := hk
  refine ⟨fun s => ?_, fun s vote _ => ?_⟩
  · rw [h1]
  · rw [h2]

/-- `SlotKeyed` holds of an AC state with the same pool.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: `SlotKeyed` holds of an AC state with the same pool. -/
theorem SlotKeyed.of_keeps {n n' : M.N} (hk : KeepsVotes M n n') (h : SlotKeyed M n) :
    SlotKeyed M n' := by
  unfold SlotKeyed
  rw [hk.1]
  exact h

/-- Every vote of the pool `M.votesHeldSet n s` is stamped when `PoolStamped n` holds.

The variables:
- `M`: the model; `F`: its facts;
- `n`: the node state; `s`: the slot.

Read aloud: every vote of the pool of slot `s` is stamped. -/
theorem pool_stamped {n : M.N} (hPool : PoolStamped M n) (s : Slot) :
    ∀ vote ∈ M.votesHeldSet n s, n.voteStamp vote ≠ none := by
  intro vote hvote
  rw [F.rd.votesHeldSet_eq] at hvote
  exact hPool s vote (List.mem_toFinset.mp hvote)

/-- A set of votes in which `v` equivocates holds two distinct votes of `v`.

The variables:
- `M`: the model; `F`: its facts;
- `votes`: the set of votes; `v`: the validator.

Read aloud: a set of votes in which `v` equivocates holds two distinct votes of `v`. -/
theorem two_votes_of_equivocates {votes : Finset (GoldfishVote V)} {v : V}
    -- `v` M.equivocates in `votes`
    (h : M.equivocates votes v = true) :
    ∃ v₁ ∈ votes, ∃ v₂ ∈ votes, v₁ ≠ v₂ ∧ v₁.val_index = v ∧ v₂.val_index = v := by
  have h2 : 2 ≤ (M.votes_by votes v).card := by simpa [F.rd.equivocates_eq] using h
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h2
  simp only [F.rd.votes_by_eq, Finset.mem_filter] at ha hb
  exact ⟨a, ha.1, b, hb.1, hab, ha.2, hb.2⟩

/-- **The liveness test of a lock entry, as a condition.** `M.is_live n t e` answers `true` exactly
when the deadline of `e` is later than `t` and the block of `e` is a block of `(M.fg_to_ac n).tree`.

The variables:
- `M`: the model; `F`: its facts;
- `t`: the time; `e`: the lock entry.

Read aloud: a lock entry is live at `t` when its deadline is after `t` and its block is in the
frame's tree. -/
theorem is_live_iff (n : M.N) (t : Time) (e : M.LE) :
    M.is_live n t e = true ↔ t < e.d ∧ e.B ∈ (M.fg_to_ac n).tree := by
  simp only [F.rd.is_live_eq, Bool.and_eq_true, decide_eq_true_eq]

/-- **The liveness test of a lock entry fails, as a condition.** `M.is_live n t e` answers `false`
exactly when the deadline of `e` is at most `t` or the block of `e` is not a block of `(M.fg_to_ac n).tree`.

The variables:
- `M`: the model; `F`: its facts;
- `t`: the time; `e`: the lock entry.

Read aloud: a lock entry is not live at `t` when its deadline is at most `t` or its block is not
in the tree of `M.fg_to_ac n`. -/
theorem is_live_eq_false_iff (n : M.N) (t : Time) (e : M.LE) :
    M.is_live n t e = false ↔ e.d ≤ t ∨ e.B ∉ (M.fg_to_ac n).tree := by
  simp only [F.rd.is_live_eq, Bool.and_eq_false_iff, decide_eq_false_iff_not, not_lt]

/-- **The lock test of a block, as a condition.** `M.is_locked n t B'` answers `true` exactly when
some lock entry `e` of `n` is live at `t` (`is_live`) and `B'` is `e.B` or an ancestor of `e.B`.

The variables:
- `M`: the model; `F`: its facts;
- `n`: the node state; `t`: the time; `B'`: the block.

Read aloud: a block is locked at `t` when it is the block of a lock entry live at `t`, or an
ancestor of that block. -/
theorem is_locked_iff (n : M.N) (t : Time) (B' : Block V) :
    M.is_locked n t B' = true ↔
      ∃ e ∈ n.lockEntries, M.is_live n t e = true ∧ B'.ancestorEq e.B = true := by
  simp only [F.rd.is_locked_eq, decide_eq_true_eq]

/-- **n vote of the pool of a slot.** n vote is in `M.votesHeldSet n s` exactly when it is in the list
`n.votesHeld s` of the Goldfish votes `n` files under the slot `s`.

The variables:
- `M`: the model; `F`: its facts;
- `n`: the node state; `s`: the slot; `vote`: the vote.

Read aloud: the pool of a slot holds exactly the votes filed under that slot. -/
theorem mem_pool_iff (n : M.N) (s : Slot) (vote : GoldfishVote V) :
    vote ∈ M.votesHeldSet n s ↔ vote ∈ n.votesHeld s := by
  rw [F.rd.votesHeldSet_eq]
  exact List.mem_toFinset

/-- **A vote of a validator among a set of votes.** `vote` is in `votes_by votes v` exactly when it
is in `votes` and its validator is `v`.

The variables:
- `M`: the model; `F`: its facts;
- `votes`: the set of votes; `v`: the validator; `vote`: the vote.

Read aloud: the votes by `v` among `votes` are the votes of `votes` whose validator is `v`. -/
theorem mem_votes_by_iff (votes : Finset (GoldfishVote V)) (v : V) (vote : GoldfishVote V) :
    vote ∈ M.votes_by votes v ↔ vote ∈ votes ∧ vote.val_index = v := by
  simp only [F.rd.votes_by_eq, Finset.mem_filter]

/-- **A Goldfish vote included in the blocks of a slot.** `vote` is in `included_votes Φ s` exactly
when some block `B` of `Φ.tree` of slot `s` includes `vote` among its Goldfish votes and `vote`'s
slot is `s - 1`.

The variables:
- `M`: the model; `F`: its facts;
- `Φ`: the frame; `s`: the slot; `vote`: the vote.

Read aloud: the votes included at slot `s` are the slot-`(s − 1)` votes of the slot-`s` blocks of
the frame's tree. -/
theorem mem_included_votes_iff (Φ : Frame V) (s : Slot) (vote : GoldfishVote V) :
    vote ∈ M.included_votes Φ s ↔
      ∃ B, (B ∈ Φ.tree ∧ B.slot = s) ∧ vote ∈ B.votes ∧ vote.slot = s - 1 := by
  simp only [F.rd.included_votes_eq, Finset.mem_biUnion, Finset.mem_filter, List.mem_toFinset]

/-- **A support vote included in the blocks of a slot.** `vote` is in `included_support_votes Φ s`
exactly when some block `B` of `Φ.tree` of slot `s` includes `vote` among its support votes and
`vote`'s slot is `s - 1`.

The variables:
- `M`: the model; `F`: its facts;
- `Φ`: the frame; `s`: the slot; `vote`: the vote.

Read aloud: the support votes included at slot `s` are the slot-`(s − 1)` support votes of the
slot-`s` blocks of the frame's tree. -/
theorem mem_included_support_votes_iff (Φ : Frame V) (s : Slot) (vote : GoldfishVote V) :
    vote ∈ M.included_support_votes Φ s ↔
      ∃ B, (B ∈ Φ.tree ∧ B.slot = s) ∧ vote ∈ B.support_votes ∧ vote.slot = s - 1 := by
  simp only [F.rd.included_support_votes_eq, Finset.mem_biUnion, Finset.mem_filter, List.mem_toFinset]

end

/-! ## At the spec's model -/

/-- The landed `GoldilocksCorrectness.Proofs.Routines.mem_equivocators_iff_two`,
recovered from its record form at the spec's model.

Read aloud: the landed `mem_equivocators_iff_two` holds, as the record's theorem at the spec's
model. -/
theorem mem_equivocators_iff_two_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.mem_equivocators_iff_two V _ _) := by
  exact mem_equivocators_iff_two Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.VotesInv.of_keeps`,
recovered from its record form at the spec's model, at
the AC states `n.A`, `n'.A` of every two node states.

Read aloud: the landed `VotesInv.of_keeps` holds at the AC states `n.A`, `n'.A` of every two node states, as the record's theorem at the
spec's model. -/
theorem VotesInv.of_keeps_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (P : Provisional V) (n n' : NodeState V), type_of% (@GoldilocksCorrectness.Proofs.Routines.VotesInv.of_keeps V P n.A n'.A) := by
  intro P n n'
  simp only [record_goldilocks]
  exact VotesInv.of_keeps Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.VotesInv.mono`,
recovered from its record form at the spec's model, at
the AC state `n.A` of every node state `n`.

Read aloud: the landed `VotesInv.mono` holds at the AC state `n.A` of every node state `n`, as the record's theorem at the
spec's model. -/
theorem VotesInv.mono_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (P : Provisional V) (n : NodeState V), type_of% (@GoldilocksCorrectness.Proofs.Routines.VotesInv.mono V P n.A) := by
  intro P n
  simp only [record_goldilocks]
  exact VotesInv.mono Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.ACStampsAt.refl`,
recovered from its record form at the spec's model, at
the AC state `n.A` of every node state `n`.

Read aloud: the landed `ACStampsAt.refl` holds at the AC state `n.A` of every node state `n`, as the record's theorem at the
spec's model. -/
theorem ACStampsAt.refl_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (n : NodeState V), type_of% (@GoldilocksCorrectness.Proofs.Routines.ACStampsAt.refl V n.A) := by
  intro n
  simp only [record_goldilocks]
  exact ACStampsAt.refl Model.goldilocks goldilocksFacts n

/-- The landed `GoldilocksCorrectness.Proofs.Routines.ACStampsAt.of_keeps`,
recovered from its record form at the spec's model, at
the AC states `n.A`, `n'.A` of every two node states.

Read aloud: the landed `ACStampsAt.of_keeps` holds at the AC states `n.A`, `n'.A` of every two node states, as the record's theorem at the
spec's model. -/
theorem ACStampsAt.of_keeps_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (n n' : NodeState V), type_of% (@GoldilocksCorrectness.Proofs.Routines.ACStampsAt.of_keeps V n.A n'.A) := by
  intro n n'
  simp only [record_goldilocks]
  exact ACStampsAt.of_keeps Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.ACStampsAt.trans`,
recovered from its record form at the spec's model, at
the AC states `n.A`, `n'.A`, `n''.A` of every three node states.

Read aloud: the landed `ACStampsAt.trans` holds at the AC states `n.A`, `n'.A`, `n''.A` of every three node states, as the record's theorem at the
spec's model. -/
theorem ACStampsAt.trans_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (n n' n'' : NodeState V), type_of% (@GoldilocksCorrectness.Proofs.Routines.ACStampsAt.trans V n.A n'.A n''.A) := by
  intro n n' n''
  simp only [record_goldilocks]
  exact ACStampsAt.trans Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.SlotKeyed.of_poolKeyed`,
recovered from its record form at the spec's model, at
the AC state `n.A` of every node state `n`.

Read aloud: the landed `SlotKeyed.of_poolKeyed` holds at the AC state `n.A` of every node state `n`, as the record's theorem at the
spec's model. -/
theorem SlotKeyed.of_poolKeyed_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (P : Provisional V) (n : NodeState V), type_of% (@GoldilocksCorrectness.Proofs.Routines.SlotKeyed.of_poolKeyed V P n.A) := by
  intro P n
  simp only [record_goldilocks]
  exact SlotKeyed.of_poolKeyed Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.ACGrows.refl`,
recovered from its record form at the spec's model, at
the AC state `n.A` of every node state `n`.

Read aloud: the landed `ACGrows.refl` holds at the AC state `n.A` of every node state `n`, as the record's theorem at the
spec's model. -/
theorem ACGrows.refl_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (n : NodeState V), type_of% (@GoldilocksCorrectness.Proofs.Routines.ACGrows.refl V n.A) := by
  intro n
  simp only [record_goldilocks]
  exact ACGrows.refl Model.goldilocks goldilocksFacts n

/-- The landed `GoldilocksCorrectness.Proofs.Routines.ACGrows.trans`,
recovered from its record form at the spec's model, at
the AC states `n.A`, `n'.A`, `n''.A` of every three node states.

Read aloud: the landed `ACGrows.trans` holds at the AC states `n.A`, `n'.A`, `n''.A` of every three node states, as the record's theorem at the
spec's model. -/
theorem ACGrows.trans_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (n n' n'' : NodeState V), type_of% (@GoldilocksCorrectness.Proofs.Routines.ACGrows.trans V n.A n'.A n''.A) := by
  intro n n' n''
  simp only [record_goldilocks]
  exact ACGrows.trans Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.ACGrows.of_keeps`,
recovered from its record form at the spec's model, at
the AC states `n.A`, `n'.A` of every two node states.

Read aloud: the landed `ACGrows.of_keeps` holds at the AC states `n.A`, `n'.A` of every two node states, as the record's theorem at the
spec's model. -/
theorem ACGrows.of_keeps_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (n n' : NodeState V), type_of% (@GoldilocksCorrectness.Proofs.Routines.ACGrows.of_keeps V n.A n'.A) := by
  intro n n'
  simp only [record_goldilocks]
  exact ACGrows.of_keeps Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.SlotKeyed.of_keeps`,
recovered from its record form at the spec's model, at
the AC states `n.A`, `n'.A` of every two node states.

Read aloud: the landed `SlotKeyed.of_keeps` holds at the AC states `n.A`, `n'.A` of every two node states, as the record's theorem at the
spec's model. -/
theorem SlotKeyed.of_keeps_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (n n' : NodeState V), type_of% (@GoldilocksCorrectness.Proofs.Routines.SlotKeyed.of_keeps V n.A n'.A) := by
  intro n n'
  simp only [record_goldilocks]
  exact SlotKeyed.of_keeps Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.pool_stamped`,
recovered from its record form at the spec's model, at
the AC state `n.A` of every node state `n`.

Read aloud: the landed `pool_stamped` holds at the AC state `n.A` of every node state `n`, as the record's theorem at the
spec's model. -/
theorem pool_stamped_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (n : NodeState V), type_of% (@GoldilocksCorrectness.Proofs.Routines.pool_stamped V _ n.A) := by
  intro n
  simp only [record_goldilocks]
  exact pool_stamped (n := n) Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.two_votes_of_equivocates`,
recovered from its record form at the spec's model.

Read aloud: the landed `two_votes_of_equivocates` holds, as the record's theorem at the spec's
model. -/
theorem two_votes_of_equivocates_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.two_votes_of_equivocates V _) := by
  exact two_votes_of_equivocates Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.is_live_iff`,
recovered from its record form at the spec's model, at
the record `fg_to_ac n.S` of every node state `n`.

Read aloud: the landed `is_live_iff` holds at the record `fg_to_ac n.S` of every node state `n`, as the record's theorem at the
spec's model. -/
theorem is_live_iff_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (n : NodeState V), type_of% (@GoldilocksCorrectness.Proofs.Routines.is_live_iff V _ (fg_to_ac n.S)) := by
  intro n
  exact is_live_iff Model.goldilocks goldilocksFacts n

/-- The landed `GoldilocksCorrectness.Proofs.Routines.is_live_eq_false_iff`,
recovered from its record form at the spec's model, at
the record `fg_to_ac n.S` of every node state `n`.

Read aloud: the landed `is_live_eq_false_iff` holds at the record `fg_to_ac n.S` of every node state `n`, as the record's theorem at the
spec's model. -/
theorem is_live_eq_false_iff_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (n : NodeState V), type_of% (@GoldilocksCorrectness.Proofs.Routines.is_live_eq_false_iff V _ (fg_to_ac n.S)) := by
  intro n
  exact is_live_eq_false_iff Model.goldilocks goldilocksFacts n

/-- The landed `GoldilocksCorrectness.Proofs.Routines.is_locked_iff`,
recovered from its record form at the spec's model, at
the AC state `n.A` and the record `fg_to_ac n.S` of every node state `n`.

Read aloud: the landed `is_locked_iff` holds at the AC state `n.A` and the record `fg_to_ac n.S` of every node state `n`, as the record's theorem at the
spec's model. -/
theorem is_locked_iff_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (n : NodeState V), type_of% (@GoldilocksCorrectness.Proofs.Routines.is_locked_iff V _ n.A (fg_to_ac n.S)) := by
  intro n
  exact is_locked_iff Model.goldilocks goldilocksFacts n

/-- The landed `GoldilocksCorrectness.Proofs.Routines.mem_pool_iff`,
recovered from its record form at the spec's model, at
the AC state `n.A` of every node state `n`.

Read aloud: the landed `mem_pool_iff` holds at the AC state `n.A` of every node state `n`, as the record's theorem at the
spec's model. -/
theorem mem_pool_iff_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (n : NodeState V), type_of% (@GoldilocksCorrectness.Proofs.Routines.mem_pool_iff V _ n.A) := by
  intro n
  exact mem_pool_iff Model.goldilocks goldilocksFacts n

/-- The landed `GoldilocksCorrectness.Proofs.Routines.mem_votes_by_iff`,
recovered from its record form at the spec's model.

Read aloud: the landed `mem_votes_by_iff` holds, as the record's theorem at the spec's
model. -/
theorem mem_votes_by_iff_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.mem_votes_by_iff V _) := by
  exact mem_votes_by_iff Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.mem_included_votes_iff`,
recovered from its record form at the spec's model.

Read aloud: the landed `mem_included_votes_iff` holds, as the record's theorem at the spec's
model. -/
theorem mem_included_votes_iff_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.mem_included_votes_iff V _) := by
  exact mem_included_votes_iff Model.goldilocks goldilocksFacts

/-- The landed `GoldilocksCorrectness.Proofs.Routines.mem_included_support_votes_iff`,
recovered from its record form at the spec's model.

Read aloud: the landed `mem_included_support_votes_iff` holds, as the record's theorem at the spec's
model. -/
theorem mem_included_support_votes_iff_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.mem_included_support_votes_iff V _) := by
  exact mem_included_support_votes_iff Model.goldilocks goldilocksFacts

end GoldilocksCorrectness.Record.Proofs.Routines
