module
public import GoldilocksCorrectness.Proofs.Routines.Locks
public import GoldilocksCorrectness.Statements.Routines.ACStoreDefs
import all Goldilocks.AC.State
import all Goldilocks.Config

@[expose] public section

/-!
# The Goldfish vote pool of an AC state, and what the vote handler does to it

The relations between two AC states `A`, `A'` that the AC routines keep: `KeepsVotes A A'` (`A'`
has the pool, the vote stamps and the block stamps of `A`), `ACGrows A A'` (`A`'s votes of each
slot are a prefix of `A'`'s, with the same stamps), `ACStampsAt A A' τ` (what `A'` holds of votes
beyond `A` is stamped `τ`), with their `refl`, `trans` and `of_keeps` lemmas; the conditions
`VotesInv P A t` and `SlotKeyed A` on one AC state; what `on_goldfish_vote` does to the pool
(`on_goldfish_vote_cases`, `…_cases_new`, `…_votesInv`, `…_grows`, `…_new`, `…_new_slot`,
`…_timestamp_block`, `receive_gfVote_cases`); and the readers of the pool `tau`,
`equivocators` (`tau_eq_ok_some`, `tau_head_of_eq_some`, `mem_equivocators_iff_two`,
`two_votes_of_equivocates`, `pool_stamped`).

They read the AC routines and an AC state alone: no node state, no execution.

Moved here unchanged from the execution pages.
-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Routines

section

open Goldilocks
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn)
variable {V : Type} [DecidableEq V]

/-- A vote whose head is the root of a block `H` of `Φ.tree`, of a slot at most the vote's,
resolves at the later of its stamp and `H`'s, when no two blocks of `Φ.tree` share a root.

The variables:
- `A`: the AC state; `Φ`: the frame; `vote`: the vote; `H`: its head block;
- `τv`, `τH`: the two stamps. -/
theorem tau_eq_ok_some {A : ACState V} {Φ : Frame V} {vote : GoldfishVote V} {H : Block V}
    {τv τH : Stamp} (hRoots : RootsNameBlocksIn Φ.tree) (hH : H ∈ Φ.tree)
    (hr : H.root = vote.head) (hs : H.slot ≤ vote.slot)
    (hτv : A.timestamp_vote vote = some τv) (hτH : A.timestamp_block H = some τH) :
    A.tau Φ vote = .ok (some (max τv τH)) := by
  show resolution_time _ _ _ _ = _
  simp only [resolution_time, blockWithRoot_eq_ok hRoots, find?_eq_some hRoots hH hr,
    dre_bind_ok, ne_eq, reduceCtorEq, not_false_eq_true, dite_true, Option.value,
    Option.get_some, if_pos hs, hτv, hτH, liftM_some]
  rfl

/-- A vote that resolves has its head block in the tree, with a slot at most the vote's.

The variables:
- `A`: the AC state; `Φ`: the frame; `vote`: the vote; `y`: its resolution time. -/
theorem tau_head_of_eq_some {A : ACState V} {Φ : Frame V} {vote : GoldfishVote V} {y : Stamp}
    (hRoots : RootsNameBlocksIn Φ.tree) (h : A.tau Φ vote = .ok (some y)) :
    ∃ H ∈ Φ.tree, H.root = vote.head ∧ H.slot ≤ vote.slot := by
  simp only [ACState.tau, resolution_time] at h
  obtain ⟨H?, hH?, h1⟩ := dre_bind_eq_ok h
  rw [blockWithRoot_eq_ok hRoots] at hH?
  cases hH?
  cases hX : Block.find? Φ.tree vote.head with
  | none =>
    rw [hX] at h1
    simp only [ne_eq, not_true_eq_false, dite_false] at h1
    cases h1
  | some H =>
    rw [hX] at h1
    obtain ⟨hH, hr⟩ := mem_of_pickUnique?_eq_some hX
    simp only [decide_eq_true_eq] at hr
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, dite_true, Option.value,
      Option.get_some] at h1
    split at h1
    · rename_i hs
      exact ⟨H, hH, hr, hs⟩
    · cases h1

end

section

open Goldilocks
variable {V : Type} [DecidableEq V]
variable [Fintype V]

/-- A validator is an equivocator of `votes` exactly when `votes` holds two distinct votes of it.

The variables:
- `votes`: the votes; `v`: the validator. -/
theorem mem_equivocators_iff_two (votes : Finset (GoldfishVote V)) (v : V) :
    v ∈ equivocators votes ↔
      ∃ v₁ ∈ votes, ∃ v₂ ∈ votes, v₁ ≠ v₂ ∧ v₁.val_index = v ∧ v₂.val_index = v := by
  rw [mem_equivocators_iff]
  constructor
  · intro h
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h
    simp only [votes_by, Finset.mem_filter] at ha hb
    exact ⟨a, ha.1, b, hb.1, hab, ha.2, hb.2⟩
  · rintro ⟨v₁, h₁, v₂, h₂, hne, hi₁, hi₂⟩
    refine Finset.one_lt_card.mpr ⟨v₁, ?_, v₂, ?_, hne⟩
    · simp only [votes_by, Finset.mem_filter]
      exact ⟨h₁, hi₁⟩
    · simp only [votes_by, Finset.mem_filter]
      exact ⟨h₂, hi₂⟩

end

section

open GoldilocksCorrectness.Statements.Routines (PoolKeyed PoolStamped)

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

/-- `VotesInv P A t`: the pool of `A` is filed by slot and committee (`PoolKeyed`), its votes are
stamped (`PoolStamped`), and each vote's stamp is at most `t`.

Read aloud: the pool is well filed and stamped no later than `t`. -/
def VotesInv (P : Provisional V) (A : ACState V) (t : Time) : Prop :=
  PoolKeyed P A ∧ PoolStamped A ∧
    ∀ s : Slot, ∀ vote ∈ A.gf_votes s, ∀ τ : Stamp,
      A.timestamp_vote vote = some τ → τ ≤ (t : Stamp)

/-- `KeepsVotes A A'`: `A'` has the pool, the vote stamps and the block stamps of `A`.

Read aloud: `A'` holds what `A` holds of votes and stamps. -/
def KeepsVotes (A A' : ACState V) : Prop :=
  A'.gf_votes = A.gf_votes ∧ A'.timestamp_vote = A.timestamp_vote ∧
    A'.timestamp_block = A.timestamp_block

omit [DecidableEq V] [Fintype V] in
/-- `VotesInv` holds of an AC state with the same pool and vote stamps. -/
theorem VotesInv.of_keeps {P : Provisional V} {A A' : ACState V} {t : Time}
    (hk : KeepsVotes A A') (h : VotesInv P A t) : VotesInv P A' t := by
  obtain ⟨h1, h2, -⟩ := hk
  unfold VotesInv PoolKeyed PoolStamped
  rw [h1, h2]
  exact h

omit [DecidableEq V] [Fintype V] in
/-- `VotesInv` at a time holds at every later time. -/
theorem VotesInv.mono {P : Provisional V} {A : ACState V} {t t' : Time}
    (h : VotesInv P A t) (ht : t ≤ t') : VotesInv P A t' := by
  refine ⟨h.1, h.2.1, fun s vote hv τ hτ => ?_⟩
  exact le_trans (h.2.2 s vote hv τ hτ) (WithBot.coe_le_coe.mpr ht)

omit [Fintype V] in
/-- The admission of a Goldfish vote either keeps the AC state, or files the vote under its slot,
with its validator in that slot's committee, and stamps it with the admission time.

The variables:
- `C`, `P`: the parameters and the values; `A`: the AC state; `t`: the admission time;
  `vote`: the vote. -/
theorem on_goldfish_vote_cases (C : Config) (P : Provisional V) (A : ACState V) (t : Time)
    (vote : GoldfishVote V) :
    on_goldfish_vote C P A t vote = A ∨
      (vote.val_index ∈ P.committee vote.slot ∧
        on_goldfish_vote C P A t vote =
          { A with
            gf_votes := Function.update A.gf_votes vote.slot (A.gf_votes vote.slot ++ [vote])
            timestamp_vote := Function.update A.timestamp_vote vote (some (t : Stamp)) }) := by
  simp only [on_goldfish_vote, Id.run]
  split
  · exact Or.inl rfl
  split
  · exact Or.inl rfl
  rename_i h1 _
  refine Or.inr ⟨?_, rfl⟩
  by_contra hc
  apply h1
  simp [hc]

omit [Fintype V] in
/-- The admission of a Goldfish vote at a time `t ≤ t'` keeps `VotesInv` at `t'`: a vote it
files under `vote.slot` has that slot and passed the committee test, and is stamped with `t`.

The variables:
- `C`, `P`: the parameters and the values; `A`: the AC state; `t`: the admission time;
  `t'`: the bound; `vote`: the vote. -/
theorem on_goldfish_vote_votesInv (C : Config) (P : Provisional V) (A : ACState V) (t t' : Time)
    (vote : GoldfishVote V) (h : VotesInv P A t') (ht : t ≤ t') :
    VotesInv P (on_goldfish_vote C P A t vote) t' := by
  rcases on_goldfish_vote_cases C P A t vote with he | ⟨hc, he⟩
  · rw [he]; exact h
  rw [he]
  obtain ⟨hK, hS, hB⟩ := h
  refine ⟨fun s vote' hv' => ?_, fun s vote' hv' => ?_, fun s vote' hv' τ hτ => ?_⟩
  · simp only [Function.update_apply] at hv'
    split at hv'
    · rename_i hs
      subst hs
      rcases List.mem_append.mp hv' with hv' | hv'
      · exact hK _ vote' hv'
      · rw [List.mem_singleton.mp hv']
        exact ⟨rfl, hc⟩
    · exact hK s vote' hv'
  · simp only [Function.update_apply] at hv' ⊢
    split
    · simp
    · split at hv'
      · rename_i hne hs
        subst hs
        rcases List.mem_append.mp hv' with hv' | hv'
        · exact hS _ vote' hv'
        · exact absurd (List.mem_singleton.mp hv') hne
      · exact hS s vote' hv'
  · simp only [Function.update_apply] at hv' hτ
    split at hτ
    · cases hτ
      exact WithBot.coe_le_coe.mpr ht
    · split at hv'
      · rename_i hne hs
        subst hs
        rcases List.mem_append.mp hv' with hv' | hv'
        · exact hB _ vote' hv' τ hτ
        · exact absurd (List.mem_singleton.mp hv') hne
      · exact hB s vote' hv' τ hτ

omit [Fintype V] in
/-- The admission of a Goldfish vote keeps the block stamps.

The variables:
- `C`, `P`: the parameters and the values; `A`: the AC state; `t`: the admission time;
  `vote`: the vote. -/
theorem on_goldfish_vote_timestamp_block (C : Config) (P : Provisional V) (A : ACState V)
    (t : Time) (vote : GoldfishVote V) :
    (on_goldfish_vote C P A t vote).timestamp_block = A.timestamp_block := by
  rcases on_goldfish_vote_cases C P A t vote with he | ⟨-, he⟩ <;> rw [he]

end

end

section

open GoldilocksCorrectness.Statements.Routines (PoolKeyed)

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

/-- `SlotKeyed A`: every Goldfish vote filed under a slot `s` in `A` has the slot `s`.

The variables:
- `A`: the AC state.

Read aloud: the pool is filed by slot. -/
def SlotKeyed (A : ACState V) : Prop :=
  ∀ s : Slot, ∀ vote ∈ A.gf_votes s, vote.slot = s

/-- `ACGrows A A'`: for every slot, `A`'s Goldfish votes of that slot are a prefix of `A'`'s, and
every vote of `A`'s pool has the same stamp in `A'`.

The variables:
- `A`, `A'`: the two AC states.

Read aloud: `A'` holds `A`'s votes, in the same order, with the same stamps. -/
def ACGrows (A A' : ACState V) : Prop :=
  (∀ s : Slot, A.gf_votes s <+: A'.gf_votes s) ∧
    ∀ s : Slot, ∀ vote ∈ A.gf_votes s, A'.timestamp_vote vote = A.timestamp_vote vote

/-- `ACStampsAt A A' τ`: every Goldfish vote `A'` holds under a slot and `A` does not hold under
that slot is stamped `τ` in `A'`.

The variables:
- `A`, `A'`: the two AC states; `τ`: the time.

Read aloud: what `A'` holds of votes beyond `A` is stamped `τ`. -/
def ACStampsAt (A A' : ACState V) (τ : Time) : Prop :=
  ∀ s : Slot, ∀ vote ∈ A'.gf_votes s, vote ∉ A.gf_votes s →
    A'.timestamp_vote vote = some (τ : Stamp)

omit [DecidableEq V] [Fintype V] in
/-- An AC state holds nothing of votes beyond itself. -/
theorem ACStampsAt.refl (A : ACState V) (τ : Time) : ACStampsAt A A τ :=
  fun _ _ hv hn => absurd hv hn

omit [DecidableEq V] [Fintype V] in
/-- An AC state with the same pool holds nothing of votes beyond `A`. -/
theorem ACStampsAt.of_keeps {A A' : ACState V} (hk : KeepsVotes A A') (τ : Time) :
    ACStampsAt A A' τ := by
  intro s vote hv hn
  rw [hk.1] at hv
  exact absurd hv hn

omit [DecidableEq V] [Fintype V] in
/-- `ACStampsAt` at one time composes along `ACGrows`: a vote beyond `A` in `A''` is beyond `A`
in `A'`, stamped `τ` there and kept, or beyond `A'` in `A''`. -/
theorem ACStampsAt.trans {A A' A'' : ACState V} {τ : Time} (h : ACStampsAt A A' τ)
    (hg : ACGrows A' A'') (h' : ACStampsAt A' A'' τ) : ACStampsAt A A'' τ := by
  intro s vote hv hn
  by_cases hv' : vote ∈ A'.gf_votes s
  · rw [hg.2 s vote hv']
    exact h s vote hv' hn
  · exact h' s vote hv hv'

omit [DecidableEq V] [Fintype V] in
/-- The pool filed by slot and committee is filed by slot. -/
theorem SlotKeyed.of_poolKeyed {P : Provisional V} {A : ACState V} (h : PoolKeyed P A) :
    SlotKeyed A :=
  fun s vote hv => (h s vote hv).1

omit [DecidableEq V] [Fintype V] in
/-- An AC state holds its own votes and stamps. -/
theorem ACGrows.refl (A : ACState V) : ACGrows A A :=
  ⟨fun _ => List.prefix_refl _, fun _ _ _ => rfl⟩

omit [DecidableEq V] [Fintype V] in
/-- `ACGrows` is transitive: a vote of the first state's pool is in the second's. -/
theorem ACGrows.trans {A A' A'' : ACState V} (h : ACGrows A A') (h' : ACGrows A' A'') :
    ACGrows A A'' :=
  ⟨fun s => (h.1 s).trans (h'.1 s), fun s vote hv => by
    rw [h'.2 s vote ((h.1 s).subset hv), h.2 s vote hv]⟩

omit [DecidableEq V] [Fintype V] in
/-- An AC state with the same pool and vote stamps holds `A`'s votes and stamps. -/
theorem ACGrows.of_keeps {A A' : ACState V} (hk : KeepsVotes A A') : ACGrows A A' := by
  obtain ⟨h1, h2, -⟩ := hk
  refine ⟨fun s => ?_, fun s vote _ => ?_⟩
  · rw [h1]
  · rw [h2]

omit [DecidableEq V] [Fintype V] in
/-- `SlotKeyed` holds of an AC state with the same pool. -/
theorem SlotKeyed.of_keeps {A A' : ACState V} (hk : KeepsVotes A A') (h : SlotKeyed A) :
    SlotKeyed A' := by
  unfold SlotKeyed
  rw [hk.1]
  exact h

end

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- The admission of a Goldfish vote either keeps the AC state, or appends a vote it does not
hold under the vote's slot to that slot's votes, and stamps it with the admission time.

The variables:
- `C`, `P`: the parameters and the values; `A`: the AC state; `t`: the admission time;
  `vote`: the vote. -/
theorem on_goldfish_vote_cases_new (C : Config) (P : Provisional V) (A : ACState V) (t : Time)
    (vote : GoldfishVote V) :
    on_goldfish_vote C P A t vote = A ∨
      (vote ∉ A.gf_votes vote.slot ∧
        on_goldfish_vote C P A t vote =
          { A with
            gf_votes := Function.update A.gf_votes vote.slot (A.gf_votes vote.slot ++ [vote])
            timestamp_vote := Function.update A.timestamp_vote vote (some (t : Stamp)) }) := by
  simp only [on_goldfish_vote, Id.run]
  split
  · exact Or.inl rfl
  split
  · exact Or.inl rfl
  rename_i h1 _
  refine Or.inr ⟨?_, rfl⟩
  intro hm
  apply h1
  simp [fun_getElem, hm]

omit [Fintype V] in
/-- The admission at the time `t` of a Goldfish vote into a pool filed by slot keeps it filed by
slot, holds the pool's votes and stamps, keeps the block stamps, and stamps what it adds with `t`.

The variables:
- `C`, `P`: the parameters and the values; `A`: the AC state; `t`: the admission time;
  `vote`: the vote. -/
theorem on_goldfish_vote_grows (C : Config) (P : Provisional V) (A : ACState V) (t : Time)
    (vote : GoldfishVote V) (hk : SlotKeyed A) :
    SlotKeyed (on_goldfish_vote C P A t vote) ∧ ACGrows A (on_goldfish_vote C P A t vote) ∧
      (on_goldfish_vote C P A t vote).timestamp_block = A.timestamp_block ∧
      ACStampsAt A (on_goldfish_vote C P A t vote) t := by
  rcases on_goldfish_vote_cases_new C P A t vote with he | ⟨hnew, he⟩
  · rw [he]; exact ⟨hk, ACGrows.refl A, rfl, ACStampsAt.refl A t⟩
  rw [he]
  refine ⟨fun s vote' hv' => ?_, ⟨fun s => ?_, fun s vote' hv' => ?_⟩, rfl,
    fun s vote' hv' hn => ?_⟩
  · simp only [Function.update_apply] at hv'
    split at hv'
    · rename_i hs
      subst hs
      rcases List.mem_append.mp hv' with hv' | hv'
      · exact hk _ vote' hv'
      · rw [List.mem_singleton.mp hv']
    · exact hk s vote' hv'
  · show A.gf_votes s <+: Function.update A.gf_votes vote.slot (A.gf_votes vote.slot ++ [vote]) s
    rw [Function.update_apply]
    split
    · rename_i hs
      subst hs
      exact List.prefix_append _ _
    · exact List.prefix_refl _
  · show Function.update A.timestamp_vote vote (some (t : Stamp)) vote' = A.timestamp_vote vote'
    rw [Function.update_apply, if_neg]
    rintro rfl
    exact hnew (hk s vote' hv' ▸ hv')
  · -- a vote beyond `A` is `vote` itself, stamped `t`
    change vote' ∈ Function.update A.gf_votes vote.slot (A.gf_votes vote.slot ++ [vote]) s at hv'
    show Function.update A.timestamp_vote vote (some (t : Stamp)) vote' = some (t : Stamp)
    rw [Function.update_apply] at hv'
    split at hv'
    · rename_i hs
      subst hs
      rcases List.mem_append.mp hv' with hv' | hv'
      · exact absurd hv' hn
      · rw [List.mem_singleton.mp hv', Function.update_self]
    · exact absurd hv' hn

end

section

open GoldilocksCorrectness.Statements.Routines (PoolStamped)

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

section

variable [RootOrder]

omit [Fintype V] [RootOrder] in
/-- Every vote of the pool `A.pool s` is stamped when `PoolStamped A` holds.

The variables:
- `A`: the AC state; `s`: the slot. -/
theorem pool_stamped {A : ACState V} (hPool : PoolStamped A) (s : Slot) :
    ∀ vote ∈ A.pool s, A.timestamp_vote vote ≠ none :=
  fun vote hvote => hPool s vote (List.mem_toFinset.mp hvote)

end

end

end

section

open Goldilocks

section

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- The admission of a Goldfish vote adds to the pool only that vote.

The variables:
- `C`, `P`: the parameters and the values; `A`: the AC state; `t`: the admission time;
  `vote`: the vote. -/
theorem on_goldfish_vote_new (C : Config) (P : Provisional V) (A : ACState V) (t : Time)
    (vote : GoldfishVote V) :
    ∀ s : Slot, ∀ vote' ∈ (on_goldfish_vote C P A t vote).gf_votes s,
      vote' ∉ A.gf_votes s → vote' = vote := by
  intro s vote' hv hn
  rcases on_goldfish_vote_cases_new C P A t vote with he | ⟨-, he⟩
  · rw [he] at hv
    exact absurd hv hn
  · rw [he] at hv
    change vote' ∈ Function.update A.gf_votes vote.slot (A.gf_votes vote.slot ++ [vote]) s at hv
    rw [Function.update_apply] at hv
    split at hv
    · rename_i hs
      subst hs
      rcases List.mem_append.mp hv with hv | hv
      · exact absurd hv hn
      · exact List.mem_singleton.mp hv
    · exact absurd hv hn

end

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- The admission of a Goldfish vote adds to the pool only that vote, and only when its slot is at
most the slot of the admission time.

The variables:
- `C`, `P`: the parameters and the values; `A`: the AC state; `t`: the admission time;
  `vote`: the vote admitted; `s`: the slot; `vote'`: the vote added.

Read aloud: a vote is admitted only up to the current slot. -/
theorem on_goldfish_vote_new_slot (C : Config) (P : Provisional V) (A : ACState V) (t : Time)
    (vote : GoldfishVote V) (s : Slot) (vote' : GoldfishVote V)
    (hv : vote' ∈ (on_goldfish_vote C P A t vote).gf_votes s) (hn : vote' ∉ A.gf_votes s) :
    vote' = vote ∧ vote.slot ≤ C.slot t := by
  refine ⟨on_goldfish_vote_new C P A t vote s vote' hv hn, ?_⟩
  by_contra hs
  have h : on_goldfish_vote C P A t vote = A := by
    simp only [on_goldfish_vote, Id.run]
    rw [if_pos (by simp [Nat.lt_of_not_le hs])]
    rfl
  rw [h] at hv
  exact hn hv

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- A set of votes in which `v` equivocates holds two distinct votes of `v`.

The variables:
- `votes`: the set of votes; `v`: the validator. -/
theorem two_votes_of_equivocates {votes : Finset (GoldfishVote V)} {v : V}
    -- `v` equivocates in `votes`
    (h : equivocates votes v = true) :
    ∃ v₁ ∈ votes, ∃ v₂ ∈ votes, v₁ ≠ v₂ ∧ v₁.val_index = v ∧ v₂.val_index = v := by
  have h2 : 2 ≤ (votes_by votes v).card := by simpa [equivocates] using h
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h2
  simp only [votes_by, Finset.mem_filter] at ha hb
  exact ⟨a, ha.1, b, hb.1, hab, ha.2, hb.2⟩

omit [Fintype V] in
/-- What `on_goldfish_vote` does with a vote whose slot is the slot of the time or the one before,
and whose validator is in its slot's committee: the answer's pool of the vote's slot holds the
vote, or the pool already held two distinct votes of the vote's validator.

The variables:
- `C`, `P`: the parameters and the given values; `A`: the AC state; `t`: the time of the
  admission; `vote`: the vote. -/
theorem receive_gfVote_cases (C : Config) (P : Provisional V) (A : ACState V) (t : Time)
    (vote : GoldfishVote V)
    -- the vote's slot is the slot of `t`, or the one before
    (hs1 : C.slot t ≤ vote.slot + 1) (hs2 : vote.slot ≤ C.slot t)
    -- the vote's validator is in its slot's committee
    (hc : vote.val_index ∈ P.committee vote.slot) :
    vote ∈ (on_goldfish_vote C P A t vote).pool vote.slot ∨
      equivocates (A.pool vote.slot) vote.val_index = true := by
  have hlt1 : ¬ vote.slot < C.slot t - 1 := Nat.not_lt.mpr (Nat.sub_le_iff_le_add.mpr hs1)
  have hlt2 : ¬ C.slot t < vote.slot := Nat.not_lt.mpr hs2
  by_cases hin : vote ∈ A.gf_votes vote.slot
  · left
    have h : on_goldfish_vote C P A t vote = A := by
      simp only [on_goldfish_vote, Id.run, fun_getElem]
      rw [if_pos (by simp [hin])]
      rfl
    rw [h]
    exact List.mem_toFinset.mpr hin
  by_cases heq : equivocates (A.pool vote.slot) vote.val_index = true
  · exact Or.inr heq
  left
  have h : on_goldfish_vote C P A t vote =
      { A with
        gf_votes := Function.update A.gf_votes vote.slot (A.gf_votes vote.slot ++ [vote])
        timestamp_vote := Function.update A.timestamp_vote vote (some (t : Stamp)) } := by
    simp only [on_goldfish_vote, Id.run, fun_getElem]
    rw [if_neg (by simp [hlt1, hlt2, hc, hin]), if_neg heq]
    rfl
  rw [h]
  show vote ∈ (Function.update A.gf_votes vote.slot (A.gf_votes vote.slot ++ [vote]))[vote.slot].toFinset
  rw [fun_getElem, Function.update_self]
  exact List.mem_toFinset.mpr (List.mem_append_right _ (List.mem_singleton_self vote))

end

section

open Goldilocks

variable {V : Type} [DecidableEq V]

/-! ## The tests on lock entries and the readers of the pool, as conditions -/

/-- **The liveness test of a lock entry, as a condition.** `is_live Φ t e` answers `true` exactly
when the deadline of `e` is later than `t` and the block of `e` is a block of `Φ.tree`.

The variables:
- `Φ`: the frame; `t`: the time; `e`: the lock entry.

Read aloud: a lock entry is live at `t` when its deadline is after `t` and its block is in the
frame's tree. -/
theorem is_live_iff (Φ : Frame V) (t : Time) (e : LockEntry V) :
    is_live Φ t e = true ↔ t < e.d ∧ e.B ∈ Φ.tree := by
  simp only [is_live, Bool.and_eq_true, decide_eq_true_eq]

/-- **The liveness test of a lock entry fails, as a condition.** `is_live Φ t e` answers `false`
exactly when the deadline of `e` is at most `t` or the block of `e` is not a block of `Φ.tree`.

The variables:
- `Φ`: the frame; `t`: the time; `e`: the lock entry.

Read aloud: a lock entry is not live at `t` when its deadline is at most `t` or its block is not
in the frame's tree. -/
theorem is_live_eq_false_iff (Φ : Frame V) (t : Time) (e : LockEntry V) :
    is_live Φ t e = false ↔ e.d ≤ t ∨ e.B ∉ Φ.tree := by
  simp only [is_live, Bool.and_eq_false_iff, decide_eq_false_iff_not, not_lt]

/-- **The lock test of a block, as a condition.** `is_locked A Φ t B'` answers `true` exactly when
some lock entry `e` of `A` is live at `t` (`is_live`) and `B'` is `e.B` or an ancestor of `e.B`.

The variables:
- `A`: the AC state; `Φ`: the frame; `t`: the time; `B'`: the block.

Read aloud: a block is locked at `t` when it is the block of a lock entry live at `t`, or an
ancestor of that block. -/
theorem is_locked_iff (A : ACState V) (Φ : Frame V) (t : Time) (B' : Block V) :
    is_locked A Φ t B' = true ↔
      ∃ e ∈ A.lock_entries, is_live Φ t e = true ∧ B'.ancestorEq e.B = true := by
  simp only [is_locked, decide_eq_true_eq]

/-- **A vote of the pool of a slot.** A vote is in `A.pool s` exactly when it is in the list
`A.gf_votes s` of the Goldfish votes `A` files under the slot `s`.

The variables:
- `A`: the AC state; `s`: the slot; `vote`: the vote.

Read aloud: the pool of a slot holds exactly the votes filed under that slot. -/
theorem mem_pool_iff (A : ACState V) (s : Slot) (vote : GoldfishVote V) :
    vote ∈ A.pool s ↔ vote ∈ A.gf_votes s :=
  List.mem_toFinset

/-- **A vote of a validator among a set of votes.** `vote` is in `votes_by votes v` exactly when it
is in `votes` and its validator is `v`.

The variables:
- `votes`: the set of votes; `v`: the validator; `vote`: the vote.

Read aloud: the votes by `v` among `votes` are the votes of `votes` whose validator is `v`. -/
theorem mem_votes_by_iff (votes : Finset (GoldfishVote V)) (v : V) (vote : GoldfishVote V) :
    vote ∈ votes_by votes v ↔ vote ∈ votes ∧ vote.val_index = v := by
  simp only [votes_by, Finset.mem_filter]

end

section

open Goldilocks

variable {V : Type} [DecidableEq V]

/-- **A Goldfish vote included in the blocks of a slot.** `vote` is in `included_votes Φ s` exactly
when some block `B` of `Φ.tree` of slot `s` includes `vote` among its Goldfish votes and `vote`'s
slot is `s - 1`.

The variables:
- `Φ`: the frame; `s`: the slot; `vote`: the vote.

Read aloud: the votes included at slot `s` are the slot-`(s − 1)` votes of the slot-`s` blocks of
the frame's tree. -/
theorem mem_included_votes_iff (Φ : Frame V) (s : Slot) (vote : GoldfishVote V) :
    vote ∈ included_votes Φ s ↔
      ∃ B, (B ∈ Φ.tree ∧ B.slot = s) ∧ vote ∈ B.votes ∧ vote.slot = s - 1 := by
  simp only [included_votes, Finset.mem_biUnion, Finset.mem_filter, List.mem_toFinset]

/-- **A support vote included in the blocks of a slot.** `vote` is in `included_support_votes Φ s`
exactly when some block `B` of `Φ.tree` of slot `s` includes `vote` among its support votes and
`vote`'s slot is `s - 1`.

The variables:
- `Φ`: the frame; `s`: the slot; `vote`: the vote.

Read aloud: the support votes included at slot `s` are the slot-`(s − 1)` support votes of the
slot-`s` blocks of the frame's tree. -/
theorem mem_included_support_votes_iff (Φ : Frame V) (s : Slot) (vote : GoldfishVote V) :
    vote ∈ included_support_votes Φ s ↔
      ∃ B, (B ∈ Φ.tree ∧ B.slot = s) ∧ vote ∈ B.support_votes ∧ vote.slot = s - 1 := by
  simp only [included_support_votes, Finset.mem_biUnion, Finset.mem_filter, List.mem_toFinset]

/-- **The initial AC state, written out.** `ACState.initial` has no Goldfish vote under any slot,
no vote stamp, the genesis block alone stamped (with `genesisStamp`), no saved confirmation, no lock
entry, no fast block, and the genesis block as its latest confirmed block. Added by the record
migration, step 1f, for the execution proofs that read a field of the initial node state.

Read aloud: the AC state starts with no vote and no lock, the genesis block alone stamped and
confirmed. -/
theorem acState_initial_eq :
    (ACState.initial : ACState V) =
      { gf_votes := fun _ => [], timestamp_vote := fun _ => none,
        timestamp_block := fun B => if B = Block.genesis then some genesisStamp else none,
        saved_confirmation := fun _ => none, lock_entries := ∅, fast_blocks := ∅,
        latest_confirmed := Block.genesis } := by rfl

end

end GoldilocksCorrectness.Proofs.Routines
