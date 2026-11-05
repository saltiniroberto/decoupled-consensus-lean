module
public import GoldilocksCorrectness.Proofs.Routines.Lemma30
public import GoldilocksCorrectness.Statements.Routines.SupporterDefs
import all Goldilocks.AC.Confirmation
import all Goldilocks.AC.State
import all Goldilocks.Config
import all GoldilocksCorrectness.Statements.Routines.ScheduleDefs

@[expose] public section

/-!
# Lemma 36: a confirmed block's ancestors have early supporters

The proof of `lem36_confirmed_ancestor_early_supporters`, stated in
`GoldilocksCorrectness/Statements/Routines/ConfirmationStatements.lean`, and of the helper
`update_confirmation_fast_blocks_pass`: every fast block of a confirmation update's answer passed
the fast test on the update's support votes.
-/

set_option autoImplicit false

open scoped DC

open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Statements.Routines
open GoldilocksCorrectness.Statements.Routines (EarlySupporterOf)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- Every fast block `B` of the answer of the confirmation update of slot `s` passed the fast test
on the update's support votes: the early votes (those of the slot-`(s − 1)` pool resolving
strictly before `C.t_ (s − 1) + 2 · C.Δ`) whose validator has no second vote among the late votes
(those stamped strictly before `C.t_ (s − 1) + 6 · C.Δ`).

Why: the update empties the fast blocks, and writes them only as the blocks of its path passing
the fast test.

The variables:
- `C`: the configuration; `P`: the provisional parameters, with the committees;
- `A`: the AC state before the update; `A'`: the AC state after it; `Φ`: the frame;
- `t`: the time of the update; `s`: the slot of the update; `B`: the fast block. -/
theorem update_confirmation_fast_blocks_pass (C : Config) (P : Provisional V)
    (A A' : ACState V) (Φ : Frame V) (t : Time) (s : Slot) (B : Block V)
    -- the slot is not the first
    (hs : 1 ≤ s)
    -- the confirmation update of slot `s` answers `A'`
    (hUpdate : update_confirmation C P A Φ t s = .ok A')
    -- `B` is a fast block of the answer
    (hB : B ∈ A'.fast_blocks) :
    ∃ early late : Finset (GoldfishVote V),
      (∀ vote : GoldfishVote V, vote ∈ early ↔ vote ∈ A.pool (s - 1) ∧
        ∃ x : Stamp, A.tau Φ vote = .ok (some x) ∧
          x < ((C.t_ (s - 1) + 2 * C.Δ : Time) : Stamp)) ∧
      (∀ vote : GoldfishVote V, vote ∈ late ↔ vote ∈ A.pool (s - 1) ∧
        ∃ τ : Stamp, A.timestamp_vote vote = some τ ∧
          τ < ((C.t_ (s - 1) + 6 * C.Δ : Time) : Stamp)) ∧
      fast_test P Φ {vote ∈ early | no_second_vote_in late vote = true} (s - 1) B = .ok true := by
  simp only [update_confirmation] at hUpdate
  rw [if_neg (Nat.one_le_iff_ne_zero.mp hs)] at hUpdate
  obtain ⟨early, hearly, h1⟩ := dre_bind_eq_ok hUpdate
  obtain ⟨late, hlate, h2⟩ := dre_bind_eq_ok h1
  obtain ⟨H, -, h3⟩ := dre_bind_eq_ok h2
  obtain ⟨b, -, h4⟩ := dre_bind_eq_ok h3
  refine ⟨early, late, mem_early_iff hearly, mem_beforeCutoff_iff hlate, ?_⟩
  cases b
  · -- no block is saved: the fast blocks are emptied
    rw [if_neg (by decide)] at h4
    split at h4
    case isTrue hne => exact absurd rfl hne
    case isFalse =>
      simp only [pure, Except.pure, Except.ok.injEq] at h4
      subst h4
      simp at hB
  rw [if_pos rfl] at h4
  split at h4
  case isFalse hne => exact absurd (Option.some_ne_none H) hne
  split at h4
  case isFalse =>
    -- a live lock vetoes the confirmation: the fast blocks are emptied
    simp only [pure, Except.pure, Except.ok.injEq] at h4
    subst h4
    simp at hB
  obtain ⟨fb, hfb, h5⟩ := dre_bind_eq_ok h4
  obtain ⟨lk, -, h6⟩ := dre_bind_eq_ok h5
  -- the fast blocks are the blocks of the path passing the fast test
  have hfbA : A'.fast_blocks = fb := by
    split at h6
    all_goals
      simp only [pure, Except.pure, Except.ok.injEq] at h6
      subst h6
      rfl
  rw [hfbA] at hB
  exact ((mem_of_filterM_eq_ok_iff _ _ _ hfb B).1 hB).2

/-- **Lemma 36, a confirmed block's ancestors have early supporters.** When the confirmation
update of slot `s` saves `C'` as the confirmation of slot `s − 1`, every block `L` that is `C'` or
an ancestor of `C'` has a set `Sup` of validators such that each member of `Sup` has exactly one
slot-`(s − 1)` vote in `A`'s pool, resolving strictly before `C.t_ (s − 1) + 2 · C.Δ`, whose head
is a block of `Φ.tree` that is `L` or a descendant of `L`; the validators with a slot-`(s − 1)`
vote in the pool are fewer than twice `Sup`; and when `L` is a fast block of the answer, the
slot-`(s − 1)` committee is at most twice `Sup`. This holds when no two blocks of `Φ.tree` share a
root and every vote of the slot-`(s − 1)` pool is stamped strictly before the late cutoff
`C.t_ (s − 1) + 6 · C.Δ`.

Why: `Sup` is the set of supporters of `L` among the update's support votes. `C'` passed the
eligibility test, fewer late voters than twice its score; no validator has two support votes, so
the score is the number of `C'`'s supporters, and every supporter of `C'` supports `L`. Every
vote of the pool is late, so the late voters are the voters of the pool. A support vote is early
and its validator has no second late vote, hence no second vote in the pool. A fast block passed
the fast test, the committee at most twice its score, and the score of `L` is the size of `Sup`.

The variables:
- `C`: the configuration; `P`: the provisional parameters, with the committees;
- `A`: the AC state before the update; `A'`: the AC state after it; `Φ`: the frame;
- `t`: the time of the update; `s`: the slot of the update;
- `C'`: the confirmation saved; `L`: the block, `C'` or an ancestor of it.

Read aloud: when the update saves `C'` and `L` is `C'` or an ancestor of it, some set `Sup` of
validators each has exactly one slot-`(s − 1)` vote in the pool, resolving strictly before
`C.t_ (s − 1) + 2 · C.Δ`, heading a block of `Φ.tree` on `L`'s chain, and the pool's voters are
fewer than twice `Sup`; and when `L` is a fast block of the answer, the committee is at most twice
`Sup`. -/
theorem lem36_confirmed_ancestor_early_supporters (C : Config) (P : Provisional V)
    (A A' : ACState V) (Φ : Frame V) (t : Time) (s : Slot) (C' L : Block V)
    -- the slot is not the first
    (hs : 1 ≤ s)
    -- no two blocks of `Φ.tree` share a root
    (hRoots : RootsNameBlocksIn Φ.tree)
    -- every vote of the slot-`(s − 1)` pool is stamped strictly before the late cutoff
    (hLate : ∀ vote ∈ A.pool (s - 1), ∃ τ : Stamp, A.timestamp_vote vote = some τ ∧
      τ < ((C.t_ (s - 1) + 6 * C.Δ : Time) : Stamp))
    -- the update answers `A'` and saves `C'`
    (hUpdate : update_confirmation C P A Φ t s = .ok A')
    (hSaved : A'.saved_confirmation (s - 1) = some C')
    -- `L` is `C'` or an ancestor of `C'`
    (hLC : L.AncestorEq C') :
    ∃ Sup : Finset V, (∀ u ∈ Sup, EarlySupporterOf C A Φ (s - 1) L u) ∧
      voters_count (A.pool (s - 1)) < 2 * Sup.card ∧
      (L ∈ A'.fast_blocks → (P.committee (s - 1)).card ≤ 2 * Sup.card) := by
  obtain ⟨early, late, he, hl, hel⟩ :=
    update_confirmation_saved_eligible C P A A' Φ t s C' hs hRoots hUpdate hSaved
  have hEL := early_subset_late C A Φ (s - 1) early late he hl
  have hEq := equivocators_support_eq_empty early late hEL
  rw [hEq, Finset.card_empty, zero_add] at hel
  -- every vote of the pool is late, so the late votes are the pool
  have hLP : late = A.pool (s - 1) := by
    ext vote
    exact ⟨fun hv => ((hl vote).1 hv).1, fun hv => (hl vote).2 ⟨hv, hLate vote hv⟩⟩
  refine ⟨supportersOf Φ {vote ∈ early | no_second_vote_in late vote = true}
    {vote ∈ early | no_second_vote_in late vote = true} (s - 1) L, ?_, ?_, ?_⟩
  · -- each supporter of `L` is an early supporter of `L`
    intro u hu
    obtain ⟨vote, hvote, hval, -, -, hH⟩ := (mem_supportersOf_iff _ _ _ _ _ _).1 hu
    obtain ⟨hvE, hN⟩ := Finset.mem_filter.1 hvote
    obtain ⟨hvp, x, hτ, hx⟩ := (he vote).1 hvE
    refine ⟨vote, hvp, hval, hH, ⟨x, hτ, (occurrenceBefore_eq_true_iff _ _).2 ⟨x, rfl, hx⟩⟩, ?_⟩
    intro vote' hvote' hval'
    simp only [no_second_vote_in, decide_eq_true_eq] at hN
    rcases hN vote' (hLP ▸ hvote') with h | h
    · exact h
    · exact absurd (hval'.trans hval.symm) h
  · -- the supporters of `C'` support `L`
    have hle := Finset.card_le_card (supportersOf_mono (Φ := Φ)
      (votes := {vote ∈ early | no_second_vote_in late vote = true})
      (support_votes := {vote ∈ early | no_second_vote_in late vote = true}) (s := s - 1) hLC)
    rw [← hLP]
    omega
  · -- a fast block passed the fast test on the same support votes
    intro hL
    obtain ⟨early', late', he', hl', hfast⟩ :=
      update_confirmation_fast_blocks_pass C P A A' Φ t s L hs hUpdate hL
    have hee : early' = early := by
      ext vote
      rw [he', he]
    have hll : late' = late := by
      ext vote
      rw [hl', hl]
    subst hee hll
    simp only [fast_test, goldfish_score_eq_ok hRoots, dre_bind_ok, hEq, Finset.card_empty,
      zero_add, pure, Except.pure, Except.ok.injEq, decide_eq_true_eq] at hfast
    exact hfast

end GoldilocksCorrectness.Proofs.Routines
