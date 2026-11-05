module
public import GoldilocksCorrectness.Proofs.Routines.Confirmation
public import GoldilocksCorrectness.Proofs.Routines.Score
import all Goldilocks.AC.Confirmation
import all Goldilocks.AC.State
import all Goldilocks.Config
import all GoldilocksCorrectness.Statements.Routines.ScheduleDefs

@[expose] public section

/-!
# Lemma 30: two confirmation updates save compatible blocks

The proof of `lem30_saved_confirmations_compatible`, stated in
`GoldilocksCorrectness/Statements/Routines/ConfirmationStatements.lean`, and of the helper
`update_confirmation_saved_eligible`: a confirmation update that saves a block found it eligible.
-/

set_option autoImplicit false

open scoped DC

open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Statements.Routines

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

theorem update_confirmation_saved_eligible (C : Config) (P : Provisional V)
    (A A' : ACState V) (Φ : Frame V) (t : Time) (s : Slot) (B : Block V)
    (hs : 1 ≤ s) (hRoots : RootsNameBlocksIn Φ.tree)
    (hUpdate : update_confirmation C P A Φ t s = .ok A')
    (hSaved : A'.saved_confirmation (s - 1) = some B) :
    ∃ early late : Finset (GoldfishVote V),
      (∀ vote : GoldfishVote V, vote ∈ early ↔ vote ∈ A.pool (s - 1) ∧
        ∃ x : Stamp, A.tau Φ vote = .ok (some x) ∧
          x < ((C.t_ (s - 1) + 2 * C.Δ : Time) : Stamp)) ∧
      (∀ vote : GoldfishVote V, vote ∈ late ↔ vote ∈ A.pool (s - 1) ∧
        ∃ τ : Stamp, A.timestamp_vote vote = some τ ∧
          τ < ((C.t_ (s - 1) + 6 * C.Δ : Time) : Stamp)) ∧
      voters_count late <
        2 * ((equivocators {vote ∈ early | no_second_vote_in late vote = true}).card +
          (supportersOf Φ {vote ∈ early | no_second_vote_in late vote = true}
            {vote ∈ early | no_second_vote_in late vote = true} (s - 1) B).card) := by
  simp only [update_confirmation] at hUpdate
  rw [if_neg (Nat.one_le_iff_ne_zero.mp hs)] at hUpdate
  obtain ⟨early, hearly, h1⟩ := dre_bind_eq_ok hUpdate
  obtain ⟨late, hlate, h2⟩ := dre_bind_eq_ok h1
  obtain ⟨H, hH, h3⟩ := dre_bind_eq_ok h2
  obtain ⟨b, hb, h4⟩ := dre_bind_eq_ok h3
  refine ⟨early, late, mem_early_iff hearly, mem_beforeCutoff_iff hlate, ?_⟩
  -- the update saves `H` when `H` is eligible, and nothing otherwise
  have hSavedH : A'.saved_confirmation (s - 1) = if b = true then some H else none := by
    cases b
    · rw [if_neg (by decide)] at h4
      split at h4
      case isTrue hne => exact absurd rfl hne
      case isFalse =>
        simp only [pure, Except.pure, Except.ok.injEq] at h4
        subst h4
        exact Function.update_self _ _ _
    · rw [if_pos rfl] at h4
      split at h4
      case isFalse hne => exact absurd (Option.some_ne_none H) hne
      case isTrue =>
        split at h4
        case isFalse =>
          simp only [pure, Except.pure, Except.ok.injEq] at h4
          subst h4
          exact Function.update_self _ _ _
        case isTrue =>
          obtain ⟨fb, -, h5⟩ := dre_bind_eq_ok h4
          obtain ⟨lk, -, h6⟩ := dre_bind_eq_ok h5
          split at h6
          all_goals
            simp only [pure, Except.pure, Except.ok.injEq] at h6
            subst h6
            exact Function.update_self _ _ _
  rw [hSaved] at hSavedH
  cases b
  · simp at hSavedH
  · rw [if_pos rfl, Option.some.injEq] at hSavedH
    subst hSavedH
    rw [goldfish_score_eq_ok hRoots] at hb
    simp only [dre_bind_ok, pure, Except.pure, Except.ok.injEq] at hb
    exact of_decide_eq_true hb

omit [Fintype V] [RootOrder] in
/-- The early votes of a confirmation update are among its late votes. -/
theorem early_subset_late (C : Config) (A : ACState V) (Φ : Frame V) (s' : Slot)
    (early late : Finset (GoldfishVote V))
    (hE : ∀ vote : GoldfishVote V, vote ∈ early ↔ vote ∈ A.pool s' ∧
      ∃ x : Stamp, A.tau Φ vote = .ok (some x) ∧ x < ((C.t_ s' + 2 * C.Δ : Time) : Stamp))
    (hL : ∀ vote : GoldfishVote V, vote ∈ late ↔ vote ∈ A.pool s' ∧
      ∃ τ : Stamp, A.timestamp_vote vote = some τ ∧ τ < ((C.t_ s' + 6 * C.Δ : Time) : Stamp)) :
    early ⊆ late := by
  intro vote hv
  obtain ⟨hp, x, hτ, hx⟩ := (hE vote).1 hv
  obtain ⟨τ, hts, hτx⟩ := tau_eq_some_stamp hτ
  refine (hL vote).2 ⟨hp, τ, hts, ?_⟩
  have hΔ : (0 : Int) < C.Δ := C.Δ_pos
  -- `omega` ignores facts stated at `Time`, an `abbrev` of `Int`: the step is spelled out
  have hlt : C.t_ s' + 2 * C.Δ < C.t_ s' + 6 * C.Δ :=
    Int.add_lt_add_left (Int.mul_lt_mul_of_pos_right (by decide) hΔ) _
  have hc : ((C.t_ s' + 2 * C.Δ : Time) : Stamp) < ((C.t_ s' + 6 * C.Δ : Time) : Stamp) :=
    WithBot.coe_lt_coe.2 hlt
  exact lt_of_le_of_lt hτx (lt_trans hx hc)

omit [RootOrder] in
/-- When the early votes are among the late votes, no validator has two support votes. -/
theorem equivocators_support_eq_empty (early late : Finset (GoldfishVote V))
    (h : early ⊆ late) :
    equivocators {vote ∈ early | no_second_vote_in late vote = true} = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun v hv => ?_
  rw [mem_equivocators_iff] at hv
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by omega :
    1 < (votes_by {vote ∈ early | no_second_vote_in late vote = true} v).card)
  simp only [votes_by, Finset.mem_filter] at ha hb
  have hN := ha.1.2
  simp only [no_second_vote_in, decide_eq_true_eq] at hN
  rcases hN b (h hb.1.1) with h' | h'
  · exact hab h'.symm
  · exact h' (hb.2.trans ha.2.symm)

omit [RootOrder] in
/-- A supporter of a block at the first node has a late vote at the second node, when every early
vote of the first pool is in the second pool or the second pool holds two votes of its validator,
and every vote of the second pool is late there. -/
theorem supportersOf_subset_participants_of_reach (C : Config) (A₁ A₂ : ACState V)
    (Φ₁ : Frame V) (s' : Slot) (B : Block V) (early₁ late₁ late₂ : Finset (GoldfishVote V))
    (hE₁ : ∀ vote : GoldfishVote V, vote ∈ early₁ ↔ vote ∈ A₁.pool s' ∧
      ∃ x : Stamp, A₁.tau Φ₁ vote = .ok (some x) ∧ x < ((C.t_ s' + 2 * C.Δ : Time) : Stamp))
    (hPoolLate₂ : A₂.pool s' ⊆ late₂)
    (hReach₁₂ : ∀ vote ∈ A₁.pool s',
      (∃ y : Stamp, A₁.tau Φ₁ vote = .ok (some y) ∧
        occurrenceBefore (some y) (C.t_ s' + 2 * C.Δ) = true) →
      vote ∈ A₂.pool s' ∨
        ∃ u₁ ∈ A₂.pool s', ∃ u₂ ∈ A₂.pool s',
          u₁ ≠ u₂ ∧ u₁.val_index = vote.val_index ∧ u₂.val_index = vote.val_index) :
    supportersOf Φ₁ {vote ∈ early₁ | no_second_vote_in late₁ vote = true}
      {vote ∈ early₁ | no_second_vote_in late₁ vote = true} s' B ⊆ participants late₂ := by
  intro v hv
  obtain ⟨x, hx, hxv, -⟩ := (mem_supportersOf_iff _ _ _ _ _ _).1 hv
  obtain ⟨hxp, y, hτ, hy⟩ := (hE₁ x).1 (Finset.mem_filter.1 hx).1
  rcases hReach₁₂ x hxp ⟨y, hτ, (occurrenceBefore_eq_true_iff _ _).2 ⟨y, rfl, hy⟩⟩ with
    h | ⟨u₁, hu₁, -, -, -, hval, -⟩
  · exact (mem_participants_iff _ _).2 ⟨x, hPoolLate₂ h, hxv⟩
  · exact (mem_participants_iff _ _).2 ⟨u₁, hPoolLate₂ hu₁, hval.trans hxv⟩

omit [RootOrder] in
/-- A validator that supports `B₁` at the first node and `B₂` at the second makes `B₁` and `B₂`
compatible, when every early vote of the first pool is in the second pool or the second pool
holds two votes of its validator, every vote of the second pool is late there, and no two blocks
of the two frame trees share a root. -/
theorem compatible_of_common_supporter (C : Config) (A₁ A₂ : ACState V) (Φ₁ Φ₂ : Frame V)
    (s' : Slot) (B₁ B₂ : Block V) (early₁ late₁ early₂ late₂ : Finset (GoldfishVote V)) (v : V)
    (hRoots : RootsNameBlocksIn (Φ₁.tree ∪ Φ₂.tree))
    (hE₁ : ∀ vote : GoldfishVote V, vote ∈ early₁ ↔ vote ∈ A₁.pool s' ∧
      ∃ x : Stamp, A₁.tau Φ₁ vote = .ok (some x) ∧ x < ((C.t_ s' + 2 * C.Δ : Time) : Stamp))
    (hPoolLate₂ : A₂.pool s' ⊆ late₂)
    (hReach₁₂ : ∀ vote ∈ A₁.pool s',
      (∃ y : Stamp, A₁.tau Φ₁ vote = .ok (some y) ∧
        occurrenceBefore (some y) (C.t_ s' + 2 * C.Δ) = true) →
      vote ∈ A₂.pool s' ∨
        ∃ u₁ ∈ A₂.pool s', ∃ u₂ ∈ A₂.pool s',
          u₁ ≠ u₂ ∧ u₁.val_index = vote.val_index ∧ u₂.val_index = vote.val_index)
    (hv₁ : v ∈ supportersOf Φ₁ {vote ∈ early₁ | no_second_vote_in late₁ vote = true}
      {vote ∈ early₁ | no_second_vote_in late₁ vote = true} s' B₁)
    (hv₂ : v ∈ supportersOf Φ₂ {vote ∈ early₂ | no_second_vote_in late₂ vote = true}
      {vote ∈ early₂ | no_second_vote_in late₂ vote = true} s' B₂) :
    B₁.compatible B₂ = true := by
  obtain ⟨x, hx, hxv, -, -, H₁, hH₁, hr₁, hB₁⟩ := (mem_supportersOf_iff _ _ _ _ _ _).1 hv₁
  obtain ⟨y, hy, hyv, -, -, H₂, hH₂, hr₂, hB₂⟩ := (mem_supportersOf_iff _ _ _ _ _ _).1 hv₂
  obtain ⟨hxp, τ, hτ, hτc⟩ := (hE₁ x).1 (Finset.mem_filter.1 hx).1
  have hN := (Finset.mem_filter.1 hy).2
  simp only [no_second_vote_in, decide_eq_true_eq] at hN
  -- the first node's support vote of `v` is the second node's
  have hxy : x = y := by
    rcases hReach₁₂ x hxp ⟨τ, hτ, (occurrenceBefore_eq_true_iff _ _).2 ⟨τ, rfl, hτc⟩⟩ with
      h | ⟨u₁, hu₁, u₂, hu₂, hne, hval₁, hval₂⟩
    · rcases hN x (hPoolLate₂ h) with h' | h'
      · exact h'
      · exact absurd (hxv.trans hyv.symm) h'
    · have e₁ : u₁ = y := (hN u₁ (hPoolLate₂ hu₁)).resolve_right
        (fun h' => h' (hval₁.trans (hxv.trans hyv.symm)))
      have e₂ : u₂ = y := (hN u₂ (hPoolLate₂ hu₂)).resolve_right
        (fun h' => h' (hval₂.trans (hxv.trans hyv.symm)))
      exact absurd (e₁.trans e₂.symm) hne
  subst hxy
  have hH : H₁ = H₂ := hRoots H₁ (Finset.mem_union_left _ hH₁) H₂ (Finset.mem_union_right _ hH₂)
    (hr₁.trans hr₂.symm)
  subst hH
  exact (compatible_iff _ _).2 (ancestorEq_compatible hB₁ hB₂)

omit [RootOrder] in
/-- When the support votes are among `late`, every supporter of a block has a vote in `late`. -/
theorem supportersOf_support_subset_participants (Φ : Frame V) (s' : Slot) (B : Block V)
    (support late : Finset (GoldfishVote V)) (h : support ⊆ late) :
    supportersOf Φ support support s' B ⊆ participants late := by
  intro v hv
  obtain ⟨vote, hvote, hval, -⟩ := (mem_supportersOf_iff _ _ _ _ _ _).1 hv
  exact (mem_participants_iff _ _).2 ⟨vote, h hvote, hval⟩

/-- **Lemma 30, two confirmation updates save compatible blocks.** Two confirmation updates of
slot `s`, for the slot `s − 1`, on the AC states `A₁`, `A₂` and the frames `Φ₁`, `Φ₂`, that save
`C₁` and `C₂` as the confirmation of slot `s − 1`, save compatible blocks, when no two blocks of
the two frame trees share a root, every vote of either slot-`(s − 1)` pool is stamped strictly
before the late cutoff `C.t_ (s − 1) + 6 · C.Δ`, and every vote of either pool that resolves
strictly before `C.t_ (s − 1) + 2 · C.Δ` is in the other pool, or the other pool holds two
distinct votes of its validator.

Why: a saved block passed the eligibility test, fewer late voters than twice its score, and the
score counts the supporters only, since no validator has two support votes. If `C₁` and `C₂`
conflicted, no validator would support both, and the supporters of either have late votes at both
nodes, so each supporter set would outnumber the other.

The variables:
- `C`: the configuration; `P`: the provisional parameters, with the committees;
- `A₁`, `A₂`: the AC states before the two updates; `A₁'`, `A₂'`: the AC states after them;
- `Φ₁`, `Φ₂`: the two frames; `t₁`, `t₂`: the times of the two updates;
- `s`: the slot of the updates; `C₁`, `C₂`: the blocks saved.

Read aloud: two confirmation updates of slot `s` that save `C₁` and `C₂` for slot `s − 1` save
blocks on one chain, when a root names one block across the two trees, every pool vote is late,
and every early vote of either pool is in the other pool unless that pool holds two votes of its
validator. -/
theorem lem30_saved_confirmations_compatible (C : Config) (P : Provisional V)
    (A₁ A₁' A₂ A₂' : ACState V) (Φ₁ Φ₂ : Frame V) (t₁ t₂ : Time) (s : Slot) (C₁ C₂ : Block V)
    -- the slot is not the first
    (hs : 1 ≤ s)
    -- no two blocks of the two frame trees share a root
    (hRoots : RootsNameBlocksIn (Φ₁.tree ∪ Φ₂.tree))
    -- every vote of `A₁`'s slot-`(s − 1)` pool is stamped strictly before the late cutoff
    (hLate₁ : ∀ vote ∈ A₁.pool (s - 1), ∃ τ : Stamp, A₁.timestamp_vote vote = some τ ∧
      τ < ((C.t_ (s - 1) + 6 * C.Δ : Time) : Stamp))
    -- every vote of `A₂`'s slot-`(s − 1)` pool is stamped strictly before the late cutoff
    (hLate₂ : ∀ vote ∈ A₂.pool (s - 1), ∃ τ : Stamp, A₂.timestamp_vote vote = some τ ∧
      τ < ((C.t_ (s - 1) + 6 * C.Δ : Time) : Stamp))
    -- every vote of `A₁`'s pool that resolves strictly before `C.t_ (s − 1) + 2 · C.Δ` is in
    -- `A₂`'s pool, or `A₂`'s pool holds two distinct votes of its validator
    (hReach₁₂ : ∀ vote ∈ A₁.pool (s - 1),
      (∃ y : Stamp, A₁.tau Φ₁ vote = .ok (some y) ∧
        occurrenceBefore (some y) (C.t_ (s - 1) + 2 * C.Δ) = true) →
      vote ∈ A₂.pool (s - 1) ∨
        ∃ u₁ ∈ A₂.pool (s - 1), ∃ u₂ ∈ A₂.pool (s - 1),
          u₁ ≠ u₂ ∧ u₁.val_index = vote.val_index ∧ u₂.val_index = vote.val_index)
    -- every vote of `A₂`'s pool that resolves strictly before `C.t_ (s − 1) + 2 · C.Δ` is in
    -- `A₁`'s pool, or `A₁`'s pool holds two distinct votes of its validator
    (hReach₂₁ : ∀ vote ∈ A₂.pool (s - 1),
      (∃ y : Stamp, A₂.tau Φ₂ vote = .ok (some y) ∧
        occurrenceBefore (some y) (C.t_ (s - 1) + 2 * C.Δ) = true) →
      vote ∈ A₁.pool (s - 1) ∨
        ∃ u₁ ∈ A₁.pool (s - 1), ∃ u₂ ∈ A₁.pool (s - 1),
          u₁ ≠ u₂ ∧ u₁.val_index = vote.val_index ∧ u₂.val_index = vote.val_index)
    -- the update on `A₁`, `Φ₁` answers `A₁'` and saves `C₁`
    (hUpdate₁ : update_confirmation C P A₁ Φ₁ t₁ s = .ok A₁')
    (hSaved₁ : A₁'.saved_confirmation (s - 1) = some C₁)
    -- the update on `A₂`, `Φ₂` answers `A₂'` and saves `C₂`
    (hUpdate₂ : update_confirmation C P A₂ Φ₂ t₂ s = .ok A₂')
    (hSaved₂ : A₂'.saved_confirmation (s - 1) = some C₂) :
    -- then `C₁` and `C₂` are compatible
    C₁.compatible C₂ = true := by
  have hRoots₁ : RootsNameBlocksIn Φ₁.tree := fun B hB B' hB' h =>
    hRoots B (Finset.mem_union_left _ hB) B' (Finset.mem_union_left _ hB') h
  have hRoots₂ : RootsNameBlocksIn Φ₂.tree := fun B hB B' hB' h =>
    hRoots B (Finset.mem_union_right _ hB) B' (Finset.mem_union_right _ hB') h
  obtain ⟨e₁, l₁, he₁, hl₁, hel₁⟩ :=
    update_confirmation_saved_eligible C P A₁ A₁' Φ₁ t₁ s C₁ hs hRoots₁ hUpdate₁ hSaved₁
  obtain ⟨e₂, l₂, he₂, hl₂, hel₂⟩ :=
    update_confirmation_saved_eligible C P A₂ A₂' Φ₂ t₂ s C₂ hs hRoots₂ hUpdate₂ hSaved₂
  have hEL₁ := early_subset_late C A₁ Φ₁ (s - 1) e₁ l₁ he₁ hl₁
  have hEL₂ := early_subset_late C A₂ Φ₂ (s - 1) e₂ l₂ he₂ hl₂
  rw [equivocators_support_eq_empty e₁ l₁ hEL₁, Finset.card_empty, zero_add] at hel₁
  rw [equivocators_support_eq_empty e₂ l₂ hEL₂, Finset.card_empty, zero_add] at hel₂
  -- every pool vote is a late vote
  have hPL₁ : A₁.pool (s - 1) ⊆ l₁ := fun vote hv => (hl₁ vote).2 ⟨hv, hLate₁ vote hv⟩
  have hPL₂ : A₂.pool (s - 1) ⊆ l₂ := fun vote hv => (hl₂ vote).2 ⟨hv, hLate₂ vote hv⟩
  -- the support votes are late votes
  have hSL₁ : {vote ∈ e₁ | no_second_vote_in l₁ vote = true} ⊆ l₁ :=
    fun vote hv => hEL₁ (Finset.mem_filter.1 hv).1
  have hSL₂ : {vote ∈ e₂ | no_second_vote_in l₂ vote = true} ⊆ l₂ :=
    fun vote hv => hEL₂ (Finset.mem_filter.1 hv).1
  by_contra hne
  -- no validator supports both blocks
  have hdisj : Disjoint
      (supportersOf Φ₁ {vote ∈ e₁ | no_second_vote_in l₁ vote = true}
        {vote ∈ e₁ | no_second_vote_in l₁ vote = true} (s - 1) C₁)
      (supportersOf Φ₂ {vote ∈ e₂ | no_second_vote_in l₂ vote = true}
        {vote ∈ e₂ | no_second_vote_in l₂ vote = true} (s - 1) C₂) := by
    rw [Finset.disjoint_left]
    intro v hv₁ hv₂
    exact hne (compatible_of_common_supporter C A₁ A₂ Φ₁ Φ₂ (s - 1) C₁ C₂ e₁ l₁ e₂ l₂ v hRoots
      he₁ hPL₂ hReach₁₂ hv₁ hv₂)
  -- both supporter sets have late votes at each node
  have hc₂ := Finset.card_le_card (Finset.union_subset
    (supportersOf_subset_participants_of_reach C A₁ A₂ Φ₁ (s - 1) C₁ e₁ l₁ l₂ he₁ hPL₂ hReach₁₂)
    (supportersOf_support_subset_participants Φ₂ (s - 1) C₂ _ l₂ hSL₂))
  have hc₁ := Finset.card_le_card (Finset.union_subset
    (supportersOf_support_subset_participants Φ₁ (s - 1) C₁ _ l₁ hSL₁)
    (supportersOf_subset_participants_of_reach C A₂ A₁ Φ₂ (s - 1) C₂ e₂ l₂ l₁ he₂ hPL₁ hReach₂₁))
  rw [Finset.card_union_of_disjoint hdisj] at hc₁ hc₂
  have h₁ : (participants l₁).card = voters_count l₁ := rfl
  have h₂ : (participants l₂).card = voters_count l₂ := rfl
  omega

end GoldilocksCorrectness.Proofs.Routines
