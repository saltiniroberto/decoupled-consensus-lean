module
public import GoldilocksCorrectness.Statements.Routines.ProposalDefs
public import GoldilocksCorrectness.Proofs.Routines.TickFrame
public import GoldilocksCorrectness.Proofs.Routines.Lemma6
import all Init.Data.List.Control
public import GoldilocksCorrectness.Proofs.Routines.Walk
import all Goldilocks.AC.ForkChoice
import all Goldilocks.AC.State
import all Goldilocks.Config

@[expose] public section

/-! The
unnumbered routine facts the proof of Lemma 19 (`Lemma19.lean`) and the proof of G0 over
executions read about the anchor, the Goldfish eligibility test and the proposal's counted sets.

## What is proved

- the anchor: `get_anchor_expireLocks` (deleting expired lock entries does not move it),
  `get_anchor_ancestorEq_of_entries` (Lemma 6's sibling with `AncestorEq` in place of
  `compatible`);
- the eligibility test: `goldfish_eligible_current_slot`, `goldfish_eligible_congr`;
- the counted sets: `List.mem_filterAuxM_ok_iff`, `List.mem_filterM_ok_iff` (a list filter with a
  test that may raise), `proposalCountedVotes_of_lists`.
-/

set_option autoImplicit false

open scoped DC

open DC (DRE)

/-! ## A list filter with a test that may raise -/

namespace List

/-- The answer of the accumulating list filter `filterAuxM p l acc` holds exactly the members of
`acc` and the members of `l` on which the test answers `true`.

The variables:
- `p`: the raising test; `l`: the list filtered; `acc`: the accumulator; `R`: the answer; `a`: the
  member tested. -/
theorem mem_filterAuxM_ok_iff {α ε : Type} (p : α → Except ε Bool) (l acc R : List α)
    (h : List.filterAuxM p l acc = .ok R) (a : α) :
    a ∈ R ↔ a ∈ acc ∨ (a ∈ l ∧ p a = .ok true) := by
  induction l generalizing acc with
  | nil =>
    have h' : (Except.ok acc : Except ε (List α)) = .ok R := h
    cases h'
    simp
  | cons b l ih =>
    have hstep : List.filterAuxM p (b :: l) acc =
        (p b >>= fun c => List.filterAuxM p l (cond c (b :: acc) acc)) := rfl
    rw [hstep] at h
    cases hb : p b with
    | error e => rw [hb] at h; cases h
    | ok c =>
      rw [hb] at h
      have h' : List.filterAuxM p l (cond c (b :: acc) acc) = .ok R := h
      rw [ih _ h']
      cases c with
      | true =>
        simp only [cond_true, List.mem_cons]
        constructor
        · rintro ((rfl | hacc) | ⟨hl, hp⟩)
          · exact Or.inr ⟨Or.inl rfl, hb⟩
          · exact Or.inl hacc
          · exact Or.inr ⟨Or.inr hl, hp⟩
        · rintro (hacc | ⟨rfl | hl, hp⟩)
          · exact Or.inl (Or.inr hacc)
          · exact Or.inl (Or.inl rfl)
          · exact Or.inr ⟨hl, hp⟩
      | false =>
        simp only [cond_false, List.mem_cons]
        constructor
        · rintro (hacc | ⟨hl, hp⟩)
          · exact Or.inl hacc
          · exact Or.inr ⟨Or.inr hl, hp⟩
        · rintro (hacc | ⟨rfl | hl, hp⟩)
          · exact Or.inl hacc
          · rw [hb] at hp; cases hp
          · exact Or.inr ⟨hl, hp⟩

/-- The answer of a list filter whose test may raise holds exactly the members of the list on
which the test answers `true`.

The variables:
- `p`: the raising test; `l`: the list filtered; `R`: the answer; `a`: the member tested. -/
theorem mem_filterM_ok_iff {α ε : Type} (p : α → Except ε Bool) (l R : List α)
    (h : l.filterM p = .ok R) (a : α) : a ∈ R ↔ a ∈ l ∧ p a = .ok true := by
  have hstep : l.filterM p =
      (List.filterAuxM p l [] >>= fun as => pure as.reverse) := rfl
  rw [hstep] at h
  cases hr : List.filterAuxM p l [] with
  | error e => rw [hr] at h; cases h
  | ok R' =>
    rw [hr] at h
    have h' : (Except.ok R'.reverse : Except ε (List α)) = .ok R := h
    cases h'
    rw [List.mem_reverse, mem_filterAuxM_ok_iff p l [] R' hr a]
    simp

end List

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Statements.Routines

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-! ## The anchor -/

omit [Fintype V] in
/-- Deleting the lock entries whose deadline is at most `t` does not move the anchor read at `t`:
a live entry at `t` already has its deadline strictly after `t`.

The variables:
- `A`: the AC state; `Φ`: the frame; `t`: the time the anchor is read at.

Read aloud: the anchor at `t` is the same before and after the expiry at `t`. -/
theorem get_anchor_expireLocks (A : ACState V) (Φ : Frame V) (t : Time) :
    get_anchor (expireLocks A t) Φ t = get_anchor A Φ t := by
  have hlock : ∀ B : Block V, is_locked (expireLocks A t) Φ t B = is_locked A Φ t B := by
    intro B
    unfold is_locked
    apply decide_eq_decide.mpr
    constructor
    · rintro ⟨e, he, hlive, hB⟩
      exact ⟨e, (Finset.mem_filter.mp he).1, hlive, hB⟩
    · rintro ⟨e, he, hlive, hB⟩
      refine ⟨e, Finset.mem_filter.mpr ⟨he, ?_⟩, hlive, hB⟩
      simp only [is_live, Bool.and_eq_true, decide_eq_true_eq] at hlive
      exact hlive.1
  unfold get_anchor
  rw [Finset.filter_congr (fun B _ => by rw [hlock B])]

omit [Fintype V] in
/-- The anchor read at `t` is `X` or an ancestor of `X` when the block of every lock entry live
at `t` is `X` or an ancestor of `X`, and `Φ.fc_root` is `X` or an ancestor of `X`.

Why: the anchor is either `Φ.fc_root`, or a locked block, which is the block of a live entry or an
ancestor of it.

The variables:
- `A`: the AC state; `Φ`: the frame; `t`: the time the anchor is read at;
- `X`: the block.

Read aloud: with no live lock past `X` and the fork choice rooted at `X` or before it, the anchor
is `X` or an ancestor of `X`. -/
theorem get_anchor_ancestorEq_of_entries (A : ACState V) (Φ : Frame V) (t : Time) (X : Block V)
    (hEntries : ∀ e ∈ A.lock_entries, is_live Φ t e = true → e.B.AncestorEq X)
    (hRoot : Φ.fc_root.AncestorEq X) :
    (get_anchor A Φ t).AncestorEq X := by
  simp only [get_anchor, Id.run]
  generalize hD : Block.deepest? {B ∈ viable_tree Φ Φ.tree | is_locked A Φ t B} = D
  cases D with
  | none => exact hRoot
  | some B =>
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, dite_true, Option.value, Option.get_some]
    have hmem := deepest?_mem hD
    rw [Finset.mem_filter] at hmem
    have hlocked := hmem.2
    simp only [is_locked, decide_eq_true_eq] at hlocked
    obtain ⟨e, he, hlive, hBe⟩ := hlocked
    exact ancestorEq_trans hBe (hEntries e he hlive)

/-! ## The eligibility test -/

omit [RootOrder] in
/-- The Goldfish eligibility test accepts every block of the current slot.

The variables:
- `C`: the configuration; `Φ`: the frame; `t`: the time;
- `votes`, `support_votes`: the votes and the support votes the score counts; `s`: their slot;
- `D`: the block tested.

Read aloud: a block of the slot of `t` is eligible at `t`. -/
theorem goldfish_eligible_current_slot (C : Config) (Φ : Frame V) (t : Time)
    (votes support_votes : Finset (GoldfishVote V)) (s : Slot) (D : Block V)
    (hD : D.slot = C.slot t) :
    goldfish_eligible C Φ t votes support_votes s D = .ok true := by
  simp only [goldfish_eligible, hD, if_true]
  split <;> rfl

omit [RootOrder] in
/-- Two Goldfish eligibility tests answer alike on `D` when they agree on whether `D`'s parent is
a viable head, read at times of one slot, give `D` the same score, and count the same number of
voters.

The variables:
- `C`: the configuration; `Φ_p`, `Φ_w`: the two frames; `t_p`, `t_w`: the two times;
- `votes_p`, `support_p`, `votes_w`, `support_w`: the votes and the support votes each counts;
- `s`: their slot; `D`: the block tested; `n`: its score at both.

Read aloud: two eligibility tests that see the same parent viability, slot, score and voter count
agree. -/
theorem goldfish_eligible_congr (C : Config) (Φ_p Φ_w : Frame V) (t_p t_w : Time)
    (votes_p support_p votes_w support_w : Finset (GoldfishVote V)) (s : Slot) (D : Block V)
    (n : ℕ)
    (hHeads : D.parent ∈ Φ_p.viable_heads ↔ D.parent ∈ Φ_w.viable_heads)
    (hSlot : C.slot t_p = C.slot t_w)
    (hScoreP : goldfish_score Φ_p votes_p support_p s D = .ok n)
    (hScoreW : goldfish_score Φ_w votes_w support_w s D = .ok n)
    (hVoters : voters_count votes_p = voters_count votes_w) :
    goldfish_eligible C Φ_p t_p votes_p support_p s D =
      goldfish_eligible C Φ_w t_w votes_w support_w s D := by
  simp only [goldfish_eligible, hScoreP, hScoreW, dre_bind_ok, hVoters, hSlot]
  by_cases hp : D.parent ∈ Φ_p.viable_heads
  · rw [if_neg (not_not.mpr hp), if_neg (not_not.mpr (hHeads.mp hp))]
  · rw [if_pos hp, if_pos (fun h => hp (hHeads.mpr h))]

/-! ## The counted sets -/

omit [Fintype V] [RootOrder] in
/-- The lists the proposal reads give the sets `ProposalCountedVotes` describes: `votes` is the
pool's list of slot `s`, and `support_votes` holds exactly its votes that resolve.

The variables:
- `A`: the AC state; `Φ`: the frame; `s`: the slot of the votes;
- `votes`, `support_votes`: the two lists.

Read aloud: the proposal's two lists, as sets, are the sets it counts. -/
theorem proposalCountedVotes_of_lists (A : ACState V) (Φ : Frame V) (s : Slot)
    (votes support_votes : List (GoldfishVote V))
    (hv : votes = A.gf_votes s)
    (hs : ∀ vote : GoldfishVote V, vote ∈ support_votes ↔
      vote ∈ votes ∧ ∃ y : Stamp, A.tau Φ vote = .ok (some y)) :
    ProposalCountedVotes A Φ s votes.toFinset support_votes.toFinset := by
  refine ⟨?_, fun vote => ?_⟩
  · rw [hv]
    rfl
  · rw [List.mem_toFinset, hs vote, hv]
    unfold ACState.pool
    rw [List.mem_toFinset]
    rfl

end GoldilocksCorrectness.Proofs.Routines
