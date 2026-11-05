module
public import GoldilocksCorrectness.Proofs.Routines.Confirmation
public import GoldilocksCorrectness.Proofs.Routines.Lemma4
import all Goldilocks.AC.Confirmation
import all Goldilocks.AC.State
import all Goldilocks.Config
import all GoldilocksCorrectness.Statements.Routines.ScheduleDefs

@[expose] public section

/-!
# Lemma 25: the confirmation update confirms a block a voter majority votes for early

The proof of `lem25_update_confirmation_confirms_voter_majority_block`, stated in
`GoldilocksCorrectness/Statements/Routines/ConfirmationStatements.lean`, and of the helper
`update_confirmation_of_voter_majority` it shares with Lemma 28: the saved confirmation and the
confirmed tip under the voter bound, and the fast block and the lock entry when the committee is
also at most twice `Hs`.
-/

set_option autoImplicit false

open scoped DC

open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Statements.Routines

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- The confirmation update of slot `s` saves `B` for the slot `s − 1` and advances the confirmed
tip with `B`, when fewer than twice `Hs` validators have a slot-`(s − 1)` vote in `A`'s pool,
every member of `Hs` votes once, early, for `B`, and no live lock conflicts with `B`; when the
slot-`(s − 1)` committee is also at most twice `Hs`, `B` is fast and locked.

Why: as for Lemma 8b, with the voters of the update bounded by the voters of the pool in place of
the committee; the fast test reads the committee size, so only it needs the half condition.

The variables:
- `C`: the configuration; `P`: the provisional parameters, with the committees;
- `A`: the AC state before the update; `A'`: the AC state after it; `Φ`: the frame;
- `t`: the time of the update; `s`: the slot of the update; `B`: the block confirmed;
- `Hs`: the validators voting early for `B`. -/
theorem update_confirmation_of_voter_majority (C : Config) (P : Provisional V)
    (A A' : ACState V) (Φ : Frame V) (t : Time) (s : Slot) (B : Block V) (Hs : Finset V)
    (hs : 1 ≤ s)
    (hRoots : RootsNameBlocksIn Φ.tree)
    (hBne : B ≠ Block.genesis)
    (hF : Φ.F.AncestorEq B)
    (hPathF : ∀ P' : Block V, Φ.F.AncestorEq P' → P'.AncestorEq B → P' ∈ Φ.tree)
    (hHs : ∀ v ∈ Hs, EarlyVoteOnceFor C A Φ (s - 1) B v)
    (hSlot : ∀ vote ∈ A.pool (s - 1), vote.slot = s - 1)
    (hVoters : voters_count (A.pool (s - 1)) < 2 * Hs.card)
    (hNoVeto : ∀ e ∈ A.lock_entries, is_live Φ t e = true → e.B.compatible B = true)
    (hUpdate : update_confirmation C P A Φ t s = .ok A') :
    A'.saved_confirmation (s - 1) = some B ∧
      A'.latest_confirmed = advance Φ A.latest_confirmed (some B) ∧
      ((P.committee (s - 1)).card ≤ 2 * Hs.card →
        B ∈ A'.fast_blocks ∧
        LockEntry.mk B (C.t_ (s - 1 + C.k) + 5 * C.Δ) ∈ A'.lock_entries) := by
  -- `B` is a block of `Φ.tree`
  have hB : B ∈ Φ.tree := hPathF B hF (ancestorEq_refl B)
  simp only [update_confirmation] at hUpdate
  rw [if_neg (Nat.one_le_iff_ne_zero.mp hs)] at hUpdate
  obtain ⟨early, hearly, h1⟩ := dre_bind_eq_ok hUpdate
  obtain ⟨late, hlate, h2⟩ := dre_bind_eq_ok h1
  obtain ⟨H, hH, h3⟩ := dre_bind_eq_ok h2
  obtain ⟨b, hb, h4⟩ := dre_bind_eq_ok h3
  -- the early votes are late votes, and both are votes of the pool
  have hEarly := mem_early_iff hearly
  have hLate := mem_beforeCutoff_iff hlate
  have hEarlyLate : early ⊆ late := by
    intro vote hv
    obtain ⟨hp, x, hτ, hx⟩ := (hEarly vote).1 hv
    obtain ⟨τ, hts, hτx⟩ := tau_eq_some_stamp hτ
    refine (hLate vote).2 ⟨hp, τ, hts, ?_⟩
    have hΔ : (0 : Int) < C.Δ := C.Δ_pos
    -- `omega` ignores facts stated at `Time`, an `abbrev` of `Int`: the step is spelled out
    have hlt : C.t_ (s - 1) + 2 * C.Δ < C.t_ (s - 1) + 6 * C.Δ :=
      Int.add_lt_add_left (Int.mul_lt_mul_of_pos_right (by decide) hΔ) _
    have hc : ((C.t_ (s - 1) + 2 * C.Δ : Time) : Stamp) <
        ((C.t_ (s - 1) + 6 * C.Δ : Time) : Stamp) := WithBot.coe_lt_coe.2 hlt
    exact lt_of_le_of_lt hτx (lt_trans hx hc)
  have hLatePool : late ⊆ A.pool (s - 1) := fun vote hv => ((hLate vote).1 hv).1
  have hSupLate : {vote ∈ early | no_second_vote_in late vote = true} ⊆ late :=
    fun vote hv => hEarlyLate (Finset.mem_filter.1 hv).1
  have hSupPool : {vote ∈ early | no_second_vote_in late vote = true} ⊆ A.pool (s - 1) :=
    fun vote hv => hLatePool (hSupLate hv)
  -- each member of `Hs` has its vote among the support votes, and no other
  have hMem : ∀ v ∈ Hs, ∃ vote ∈ {vote ∈ early | no_second_vote_in late vote = true},
      vote.val_index = v ∧ vote.slot = s - 1 ∧ vote.head = B.root ∧
      ∀ vote' ∈ {vote ∈ early | no_second_vote_in late vote = true},
        vote'.val_index = v → vote' = vote := by
    intro v hv
    obtain ⟨vote, hvote, hval, hhead, ⟨x, hτ, hx⟩, hu⟩ := hHs v hv
    obtain ⟨y, hy, hlt⟩ := (occurrenceBefore_eq_true_iff _ _).1 hx
    cases hy
    have hE : vote ∈ early := (hEarly vote).2 ⟨hvote, x, hτ, hlt⟩
    have hN : no_second_vote_in late vote = true := by
      simp only [no_second_vote_in, decide_eq_true_eq]
      intro u hu'
      by_cases huv : u.val_index = vote.val_index
      · exact Or.inl (hu u (hLatePool hu') (huv.trans hval))
      · exact Or.inr huv
    refine ⟨vote, Finset.mem_filter.2 ⟨hE, hN⟩, hval, hSlot vote hvote, hhead, ?_⟩
    intro vote' hv' hval'
    exact hu vote' (hSupPool hv') hval'
  -- the counting: the late voters are voters of the pool
  have hPartLate : participants late ⊆ participants (A.pool (s - 1)) := by
    intro v hv
    obtain ⟨vote, hvote, hval⟩ := (mem_participants_iff _ _).1 hv
    exact (mem_participants_iff _ _).2 ⟨vote, hLatePool hvote, hval⟩
  have hNle : voters_count late ≤ voters_count (A.pool (s - 1)) := Finset.card_le_card hPartLate
  have hPartSup : participants {vote ∈ early | no_second_vote_in late vote = true} ⊆
      participants late := by
    intro v hv
    obtain ⟨vote, hvote, hval⟩ := (mem_participants_iff _ _).1 hv
    exact (mem_participants_iff _ _).2 ⟨vote, hSupLate hvote, hval⟩
  have hSupLe : voters_count {vote ∈ early | no_second_vote_in late vote = true} ≤
      voters_count late := Finset.card_le_card hPartSup
  -- the walk ends at `B`
  have hHB : H = B := lem4_walk_ends_at_unanimous_block Φ
    {vote ∈ early | no_second_vote_in late vote = true}
    {vote ∈ early | no_second_vote_in late vote = true} (s - 1) (voters_count late) Φ.F B H
    Φ.tree Hs hF (fun P' hFP' _ hP'B => hPathF P' hFP' hP'B) hRoots (subset_refl _) hMem hB
    hSupLe (by omega) hH
  subst H
  -- `B` scores at least `Hs`
  have hSupB : Hs ⊆ supportersOf Φ {vote ∈ early | no_second_vote_in late vote = true}
      {vote ∈ early | no_second_vote_in late vote = true} (s - 1) B := by
    intro v hv
    obtain ⟨vote, hvote, hval, hslot, hhead, hu⟩ := hMem v hv
    exact mem_supportersOf_of_votesOnceFor
      ⟨vote, hvote, hval, hslot, ⟨B, hB, hhead.symm, ancestorEq_refl B⟩, hu⟩ (ancestorEq_refl B)
  have hScoreB := goldfish_score_eq_ok hRoots {vote ∈ early | no_second_vote_in late vote = true}
    {vote ∈ early | no_second_vote_in late vote = true} (s - 1) B
  have hScoreGe := Finset.card_le_card hSupB
  -- `B` is eligible
  rw [hScoreB] at hb
  have hbt : b = true := by
    simp only [dre_bind_ok, pure, Except.pure, Except.ok.injEq] at hb
    rw [← hb, decide_eq_true_eq]
    omega
  subst hbt
  rw [if_pos rfl] at h4
  split at h4
  case isFalse hne => exact absurd (Option.some_ne_none B) hne
  -- no live entry vetoes `B`
  split at h4
  case isFalse hveto =>
    exact absurd (by rw [Bool.not_eq_true']; exact live_lock_vetoes_eq_false hNoVeto) hveto
  -- the fast blocks and the lockable blocks
  obtain ⟨fb, hfb, h5⟩ := dre_bind_eq_ok h4
  obtain ⟨lk, hlk, h6⟩ := dre_bind_eq_ok h5
  -- the saved confirmation and the confirmed tip, whatever the deepest lockable block
  have hSaved : A'.saved_confirmation (s - 1) = some B ∧
      A'.latest_confirmed = advance Φ A.latest_confirmed (some B) ∧ A'.fast_blocks = fb ∧
      (Block.deepest? lk = some B →
        LockEntry.mk B (C.t_ (s - 1 + C.k) + 5 * C.Δ) ∈ A'.lock_entries) := by
    generalize hD : Block.deepest? lk = D at h6
    cases D with
    | none =>
      simp only [ne_eq, not_true_eq_false, dite_false, pure, Except.pure,
        Except.ok.injEq] at h6
      subst h6
      refine ⟨Function.update_self _ _ _, rfl, rfl, fun h => ?_⟩
      cases h
    | some D =>
      simp only [ne_eq, reduceCtorEq, not_false_eq_true, dite_true, Option.value, Option.get_some,
        pure, Except.pure, Except.ok.injEq] at h6
      subst h6
      refine ⟨Function.update_self _ _ _, rfl, rfl, fun h => ?_⟩
      cases h
      exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
  refine ⟨hSaved.1, hSaved.2.1, fun hHalf => ?_⟩
  -- under the half condition, `B` passes the fast test and is the deepest lockable block
  have hfast : fast_test P Φ {vote ∈ early | no_second_vote_in late vote = true} (s - 1) B =
      .ok true := by
    simp only [fast_test, hScoreB, dre_bind_ok]
    show Except.ok _ = Except.ok _
    congr 1
    rw [decide_eq_true_eq]
    omega
  have hBfb : B ∈ fb := by
    rw [mem_of_filterM_eq_ok_iff _ _ _ hfb]
    refine ⟨?_, hfast⟩
    rw [Finset.mem_filter]
    refine ⟨hB, ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hBne, ancestorEq_refl B⟩
  have hBlk : B ∈ lk := by
    rw [mem_of_filterM_eq_ok_iff _ _ _ hlk]
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨hB, ?_⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hBne, ancestorEq_refl B⟩
    · simp only [hfast, dre_bind_ok, Bool.true_or]
      rfl
  have hlkB : ∀ D ∈ lk, D.AncestorEq B := by
    intro D hD
    have hpath := ((mem_of_filterM_eq_ok_iff _ _ _ hlk D).1 hD).1
    simp only [Finset.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hpath
    exact hpath.2.2
  have hdeep : Block.deepest? lk = some B := deepest?_eq_some hBlk
    (fun D hD => depth_le_of_ancestorEq (hlkB D hD))
    (fun D hD hd => eq_of_ancestorEq_of_depth (hlkB D hD) hd.ge)
  exact ⟨hSaved.2.2.1 ▸ hBfb, hSaved.2.2.2 hdeep⟩

/-- **Lemma 25, the confirmation update confirms a block a voter majority votes for early.** The
confirmation update of slot `s`, for the slot `s − 1`, saves `B` as the confirmation of slot
`s − 1` and advances the record of the confirmed tip with `B`, when the roots of `Φ.tree` name its
blocks, `B` is not the genesis block, `Φ.F` is `B` or an ancestor of `B` with every block between
them in `Φ.tree`, every member of `Hs` has exactly one slot-`(s − 1)` vote in `A`'s pool, early and
with head `B`, every vote of the pool has the slot `s − 1`, fewer than twice `Hs` validators have
a vote in the pool, and no live lock entry conflicts with `B`.

Why: every early vote is a late vote, so the votes of `Hs` are support votes, and the late voters
are voters of the pool, fewer than twice `Hs`. Lemma 4 makes the walk from `Φ.F` end at `B`, and
`B`'s score is at least `|Hs|`, so `B` is eligible; no live entry vetoes `B`. The committee size
does not enter: only the fast test reads it, and Lemma 28 adds the half condition for the fast
block and the lock.

The variables:
- `C`: the configuration; `P`: the provisional parameters, with the committees;
- `A`: the AC state before the update; `A'`: the AC state after it; `Φ`: the frame;
- `t`: the time of the update; `s`: the slot of the update; `B`: the block confirmed;
- `Hs`: the validators voting early for `B`.

Read aloud: when fewer than twice `Hs` validators have a slot-`(s − 1)` vote in the pool, each
member of `Hs` voting once, early, for `B`, and no live lock conflicts with `B`, the update saves
`B` and advances the confirmed tip with `B`. -/
theorem lem25_update_confirmation_confirms_voter_majority_block (C : Config) (P : Provisional V)
    (A A' : ACState V) (Φ : Frame V) (t : Time) (s : Slot) (B : Block V) (Hs : Finset V)
    -- the slot is not the first
    (hs : 1 ≤ s)
    -- no two blocks of `Φ.tree` share a root
    (hRoots : RootsNameBlocksIn Φ.tree)
    -- `B` is not the genesis block
    (hBne : B ≠ Block.genesis)
    -- `Φ.F` is `B` or an ancestor of `B`
    (hF : Φ.F.AncestorEq B)
    -- every block from `Φ.F` to `B` is in `Φ.tree`
    (hPathF : ∀ P' : Block V, Φ.F.AncestorEq P' → P'.AncestorEq B → P' ∈ Φ.tree)
    -- each member of `Hs` has exactly one slot-`(s − 1)` vote in `A`'s pool, early, with head `B`
    (hHs : ∀ v ∈ Hs, EarlyVoteOnceFor C A Φ (s - 1) B v)
    -- every vote of `A`'s slot-`(s − 1)` pool has the slot `s − 1`
    (hSlot : ∀ vote ∈ A.pool (s - 1), vote.slot = s - 1)
    -- the validators with a slot-`(s − 1)` vote in `A`'s pool are fewer than twice `Hs`
    (hVoters : voters_count (A.pool (s - 1)) < 2 * Hs.card)
    -- the block of every lock entry of `A` live at `t` is compatible with `B`
    (hNoVeto : ∀ e ∈ A.lock_entries, is_live Φ t e = true → e.B.compatible B = true)
    -- the confirmation update of slot `s` answers `A'`
    (hUpdate : update_confirmation C P A Φ t s = .ok A') :
    -- then `B` is saved, and the confirmed tip advances with it
    A'.saved_confirmation (s - 1) = some B ∧
      A'.latest_confirmed = advance Φ A.latest_confirmed (some B) :=
  let h := update_confirmation_of_voter_majority C P A A' Φ t s B Hs hs hRoots hBne hF hPathF hHs
    hSlot hVoters hNoVeto hUpdate
  ⟨h.1, h.2.1⟩

end GoldilocksCorrectness.Proofs.Routines
