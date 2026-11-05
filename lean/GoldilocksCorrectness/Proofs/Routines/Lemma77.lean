module
public import GoldilocksCorrectness.Proofs.Routines.Confirmation
public import GoldilocksCorrectness.Proofs.Routines.Lemma1
public import GoldilocksCorrectness.Statements.Routines.SupporterDefs
import all Goldilocks.AC.Confirmation
import all Goldilocks.AC.ForkChoice
import all Goldilocks.AC.State
import all Goldilocks.Config
import all GoldilocksCorrectness.Statements.Routines.ScheduleDefs

@[expose] public section

/-!
# Lemma 77: the confirmation update over a chain

The proofs of `lem77_update_confirmation_extends_voter_majority_chain` and of the kit fact
`saved_confirmation_F_ancestorEq`, stated in
`GoldilocksCorrectness/Statements/Routines/ChainConfirmationStatements.lean`, and of the helper
`update_confirmation_walk` they share: the confirmation the update saves is the end of its walk
when that end is eligible, and nothing otherwise.
-/

set_option autoImplicit false

open scoped DC

open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Statements.Routines
open GoldilocksCorrectness.Statements.Routines (EarlySupporterOf)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- The confirmation update of slot `s ≥ 1` computes its early votes `early` and late votes
`late` from `A.pool (s − 1)`, walks from `Φ.F` to a block `H` with the eligibility test of the
update, evaluates that test on `H` to `b`, and saves `H` as the confirmation of slot `s − 1` when
`b` is true, and nothing otherwise.

The variables:
- `C`: the configuration; `P`: the provisional parameters;
- `A`: the AC state before the update; `A'`: the AC state after it; `Φ`: the frame;
- `t`: the time of the update; `s`: the slot of the update. -/
theorem update_confirmation_walk (C : Config) (P : Provisional V) (A A' : ACState V)
    (Φ : Frame V) (t : Time) (s : Slot)
    (hs : 1 ≤ s)
    (hUpdate : update_confirmation C P A Φ t s = .ok A') :
    ∃ (early late : Finset (GoldfishVote V)) (H : Block V) (b : Bool),
      (∀ vote : GoldfishVote V, vote ∈ early ↔ vote ∈ A.pool (s - 1) ∧
        ∃ x : Stamp, A.tau Φ vote = .ok (some x) ∧
          x < ((C.t_ (s - 1) + 2 * C.Δ : Time) : Stamp)) ∧
      (∀ vote : GoldfishVote V, vote ∈ late ↔ vote ∈ A.pool (s - 1) ∧
        ∃ τ : Stamp, A.timestamp_vote vote = some τ ∧
          τ < ((C.t_ (s - 1) + 6 * C.Δ : Time) : Stamp)) ∧
      ghost Φ.F Φ.tree
          (goldfish_score Φ {vote ∈ early | no_second_vote_in late vote = true}
            {vote ∈ early | no_second_vote_in late vote = true} (s - 1))
          (fun B => do
            let n ← goldfish_score Φ {vote ∈ early | no_second_vote_in late vote = true}
              {vote ∈ early | no_second_vote_in late vote = true} (s - 1) B
            pure (decide (voters_count late < 2 * n))) = .ok H ∧
      (do
          let n ← goldfish_score Φ {vote ∈ early | no_second_vote_in late vote = true}
            {vote ∈ early | no_second_vote_in late vote = true} (s - 1) H
          pure (decide (voters_count late < 2 * n)) : DRE Bool) = .ok b ∧
      A'.saved_confirmation (s - 1) = if b = true then some H else none := by
  simp only [update_confirmation] at hUpdate
  rw [if_neg (Nat.one_le_iff_ne_zero.mp hs)] at hUpdate
  obtain ⟨early, hearly, h1⟩ := dre_bind_eq_ok hUpdate
  obtain ⟨late, hlate, h2⟩ := dre_bind_eq_ok h1
  obtain ⟨H, hH, h3⟩ := dre_bind_eq_ok h2
  obtain ⟨b, hb, h4⟩ := dre_bind_eq_ok h3
  refine ⟨early, late, H, b, mem_early_iff hearly, mem_beforeCutoff_iff hlate, hH, hb, ?_⟩
  cases b
  · simp only [Bool.false_eq_true, if_false, ne_eq, not_true_eq_false, dite_false, pure,
      Except.pure, Except.ok.injEq] at h4
    subst h4
    exact Function.update_self _ _ _
  · rw [if_pos rfl] at h4
    rw [if_pos rfl]
    split at h4
    case isFalse hne => exact absurd (Option.some_ne_none H) hne
    split at h4
    case isFalse =>
      simp only [pure, Except.pure, Except.ok.injEq] at h4
      subst h4
      exact Function.update_self _ _ _
    obtain ⟨fb, -, h5⟩ := dre_bind_eq_ok h4
    obtain ⟨lk, -, h6⟩ := dre_bind_eq_ok h5
    split at h6 <;>
    · simp only [pure, Except.pure, Except.ok.injEq] at h6
      subst h6
      exact Function.update_self _ _ _

/-- The confirmation the update of slot `s ≥ 1` saves for slot `s − 1`, when it saves one, is
`Φ.F` or a descendant of `Φ.F`.

Why: the saved block is the end of the walk `ghost` from `Φ.F`, which is `Φ.F` or a descendant of
it.

The variables:
- `C`: the configuration; `P`: the provisional parameters;
- `A`: the AC state before the update; `A'`: the AC state after it; `Φ`: the frame;
- `t`: the time of the update; `s`: the slot of the update. -/
theorem saved_confirmation_F_ancestorEq (C : Config) (P : Provisional V) (A A' : ACState V)
    (Φ : Frame V) (t : Time) (s : Slot)
    (hs : 1 ≤ s)
    (hUpdate : update_confirmation C P A Φ t s = .ok A') :
    ∀ C' : Block V, A'.saved_confirmation (s - 1) = some C' → Φ.F.AncestorEq C' := by
  intro C' hC'
  obtain ⟨early, late, H, b, -, -, hH, -, hsaved⟩ :=
    update_confirmation_walk C P A A' Φ t s hs hUpdate
  rw [hsaved] at hC'
  split at hC'
  · cases hC'
    rcases ghost_spec hH with h | ⟨h, -⟩
    · rw [h]
      exact ancestorEq_refl _
    · exact h
  · cases hC'

/-- **Lemma 77, the confirmation update over a chain, routine form.** The confirmation the update
of slot `s ≥ 1` saves for slot `s − 1`, when it saves one, is `B` or a descendant of `B`, when the
roots of `Φ.tree` name its blocks, `Φ.F` is `B` or an ancestor of `B` with every block between them
in `Φ.tree`, every member of `Hs` has exactly one slot-`(s − 1)` vote in `A`'s pool, early, with
its head a block of `Φ.tree` that is `B` or a descendant of `B`, every vote of the pool has the slot
`s − 1`, and fewer than twice `Hs` validators have a vote in the pool.

Why: every early vote is a late vote, so the votes of `Hs` are support votes, each the only
support vote of its validator, and the voters counted are fewer than twice `Hs`. Lemma 1 makes the
walk from `Φ.F` end at `B` or a descendant of `B`, and the update saves that end or nothing.

The variables:
- `C`: the configuration; `P`: the provisional parameters, with the committees;
- `A`: the AC state before the update; `A'`: the AC state after it; `Φ`: the frame;
- `t`: the time of the update; `s`: the slot of the update; `B`: the block whose chain the votes
  support; `Hs`: the validators voting early for `B`'s chain. -/
theorem lem77_update_confirmation_extends_voter_majority_chain (C : Config) (P : Provisional V)
    (A A' : ACState V) (Φ : Frame V) (t : Time) (s : Slot) (B : Block V) (Hs : Finset V)
    (hs : 1 ≤ s)
    (hRoots : RootsNameBlocksIn Φ.tree)
    (hF : Φ.F.AncestorEq B)
    (hPathF : ∀ P' : Block V, Φ.F.AncestorEq P' → P'.AncestorEq B → P' ∈ Φ.tree)
    (hHs : ∀ v ∈ Hs, EarlySupporterOf C A Φ (s - 1) B v)
    (hSlot : ∀ vote ∈ A.pool (s - 1), vote.slot = s - 1)
    (hVoters : voters_count (A.pool (s - 1)) < 2 * Hs.card)
    (hUpdate : update_confirmation C P A Φ t s = .ok A') :
    ∀ C' : Block V, A'.saved_confirmation (s - 1) = some C' → B.AncestorEq C' := by
  intro C' hC'
  obtain ⟨early, late, H, b, hEarly, hLate, hH, -, hsaved⟩ :=
    update_confirmation_walk C P A A' Φ t s hs hUpdate
  -- the early votes are late votes, and both are votes of the pool
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
  -- each member of `Hs` has one support vote, for `B`'s chain
  have hMem : ∀ v ∈ Hs, VotesOnceFor Φ {vote ∈ early | no_second_vote_in late vote = true}
      {vote ∈ early | no_second_vote_in late vote = true} (s - 1) B v := by
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
    exact ⟨vote, Finset.mem_filter.2 ⟨hE, hN⟩, hval, hSlot vote hvote, hhead,
      fun vote' hv' hval' => hu vote' (hSupPool hv') hval'⟩
  -- the counting: the support voters are late voters, and the late voters are voters of the pool
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
  -- the walk ends at `B` or a descendant of `B` (Lemma 1)
  have hBH : B.AncestorEq H := lem1_walk_extends_majority_block Φ
    {vote ∈ early | no_second_vote_in late vote = true}
    {vote ∈ early | no_second_vote_in late vote = true} (s - 1) _ (voters_count late) Φ.F B H
    Φ.tree Hs (Or.inr ⟨hF, fun P' hFP' _ hP'B => hPathF P' hFP' hP'B⟩) hRoots (subset_refl _)
    hMem (by omega) (by omega)
    (fun D => ⟨_, by simp only [goldfish_score_eq_ok hRoots, dre_bind_ok]; rfl⟩)
    (fun D _ _ _ n hn hlt => by
      simp only [hn, dre_bind_ok]
      show Except.ok _ = Except.ok _
      rw [decide_eq_true hlt])
    hH
  -- the update saves `H` or nothing
  rw [hsaved] at hC'
  split at hC'
  · cases hC'
    exact hBH
  · cases hC'

end GoldilocksCorrectness.Proofs.Routines
