module
public import GoldilocksCorrectness.Proofs.Routines.Lemma77
public import GoldilocksCorrectness.Proofs.Routines.Score
import all Goldilocks.AC.Confirmation
import all Goldilocks.AC.State
import all Goldilocks.Config
import all GoldilocksCorrectness.Statements.Routines.ScheduleDefs

@[expose] public section

/-! A new routine fact, the compatible variant of Lemma 77
(`lem77_update_confirmation_extends_voter_majority_chain`); Lemma 77 stays as it is. The audited
statement is in `Statements/Executions/ConfirmationCompatStatements.lean`.

The argument: a block `X` conflicting
with `B` is supported by no member of `Hs` (each member's one vote names a block compatible with
`B`, and a vote supports only that block's ancestors); the equivocators, the supporters of `X` and
`Hs` are disjoint sets of late voters, so twice `X`'s score is at most twice the late voters less
`Hs`, and with the voters fewer than twice `Hs` the test `voters_count late < 2 · score` of
`update_confirmation` fails for `X`. The saved confirmation passes that test.
-/

set_option autoImplicit false

open scoped DC

open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Statements.Routines

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **Lemma 77c, the confirmation update over a majority of votes compatible with `B`, routine
form.** The proof; the audited statement is in
`Statements/Executions/ConfirmationCompatStatements.lean`.

The variables:
- `C`: the configuration; `P`: the provisional parameters, with the committees;
- `A`: the AC state before the update; `A'`: the AC state after it; `Φ`: the frame;
- `t`: the time of the update; `s`: the slot of the update; `B`: the block; `Hs`: the
  validators whose votes are compatible with `B`. -/
theorem lem77c_update_confirmation_compatible_of_majority (C : Config) (P : Provisional V)
    (A A' : ACState V) (Φ : Frame V) (t : Time) (s : Slot) (B : Block V) (Hs : Finset V)
    (hs : 1 ≤ s)
    (hRoots : RootsNameBlocksIn Φ.tree)
    (hHs : ∀ u ∈ Hs, ∃ vote ∈ A.pool (s - 1), vote.val_index = u ∧
      (∃ τ : Stamp, A.timestamp_vote vote = some τ ∧
        τ < ((C.t_ (s - 1) + 6 * C.Δ : Time) : Stamp)) ∧
      (∀ vote' ∈ A.pool (s - 1), vote'.val_index = u → vote' = vote) ∧
      ∀ D ∈ Φ.tree, D.root = vote.head → D.compatible B = true)
    (hVoters : voters_count (A.pool (s - 1)) < 2 * Hs.card)
    (hUpdate : update_confirmation C P A Φ t s = .ok A') :
    ∀ C' : Block V, A'.saved_confirmation (s - 1) = some C' → C'.compatible B = true := by
  intro C' hC'
  obtain ⟨early, late, H, b, hEarly, hLate, -, hb, hsaved⟩ :=
    update_confirmation_walk C P A A' Φ t s hs hUpdate
  rw [hsaved] at hC'
  split at hC'
  case isFalse => cases hC'
  case isTrue hbt =>
  cases hC'
  subst hbt
  by_contra hHB
  -- the test the saved block passed
  simp only [goldfish_score_eq_ok hRoots, dre_bind_ok, pure, Except.pure, Except.ok.injEq,
    decide_eq_true_eq] at hb
  -- the support votes are late votes, and the late votes are votes of the pool
  have hLatePool : late ⊆ A.pool (s - 1) := fun vote hv => ((hLate vote).1 hv).1
  have hSupLate : {vote ∈ early | no_second_vote_in late vote = true} ⊆ late := by
    intro vote hv
    have hE := (Finset.mem_filter.1 hv).1
    obtain ⟨hp, x, hτ, hx⟩ := (hEarly vote).1 hE
    obtain ⟨τ, hts, hτx⟩ := tau_eq_some_stamp hτ
    refine (hLate vote).2 ⟨hp, τ, hts, ?_⟩
    have hΔ : (0 : Int) < C.Δ := C.Δ_pos
    have hlt : C.t_ (s - 1) + 2 * C.Δ < C.t_ (s - 1) + 6 * C.Δ :=
      Int.add_lt_add_left (Int.mul_lt_mul_of_pos_right (by decide) hΔ) _
    have hc : ((C.t_ (s - 1) + 2 * C.Δ : Time) : Stamp) <
        ((C.t_ (s - 1) + 6 * C.Δ : Time) : Stamp) := WithBot.coe_lt_coe.2 hlt
    exact lt_of_le_of_lt hτx (lt_trans hx hc)
  -- `Hs` are late voters, no equivocators, and no supporters of `H`
  have hHsLate : Hs ⊆ participants late := by
    intro u hu
    obtain ⟨vote, hp, hval, ⟨τ, hts, hlt⟩, -, -⟩ := hHs u hu
    exact (mem_participants_iff _ _).2 ⟨vote, (hLate vote).2 ⟨hp, τ, hts, hlt⟩, hval⟩
  have hHsEq : Disjoint Hs (equivocators {vote ∈ early | no_second_vote_in late vote = true}) := by
    rw [Finset.disjoint_left]
    intro u hu
    obtain ⟨vote, -, -, -, huniq, -⟩ := hHs u hu
    exact not_mem_equivocators_of_unique fun vote' hv' hval' =>
      huniq vote' (hLatePool (hSupLate hv')) hval'
  have hHsSup : Disjoint (supportersOf Φ {vote ∈ early | no_second_vote_in late vote = true}
      {vote ∈ early | no_second_vote_in late vote = true} (s - 1) C') Hs := by
    rw [Finset.disjoint_right]
    intro u hu hmem
    obtain ⟨vote, -, -, -, huniq, hroot⟩ := hHs u hu
    obtain ⟨vote', hv', hval', -, -, D, hD, hDr, hHD⟩ := (mem_supportersOf_iff _ _ _ _ _ _).1 hmem
    have hvv : vote' = vote := huniq vote' (hLatePool (hSupLate hv')) hval'
    subst hvv
    exact hHB (compatible_of_ancestorEq_compatible hHD (hroot D hD hDr))
  -- the count
  have hsub : equivocators {vote ∈ early | no_second_vote_in late vote = true} ∪
      supportersOf Φ {vote ∈ early | no_second_vote_in late vote = true}
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
      (supportersOf Φ {vote ∈ early | no_second_vote_in late vote = true}
        {vote ∈ early | no_second_vote_in late vote = true} (s - 1) C') :=
    disjoint_supportersOf_equivocators.symm
  have h2 : Disjoint (equivocators {vote ∈ early | no_second_vote_in late vote = true} ∪
      supportersOf Φ {vote ∈ early | no_second_vote_in late vote = true}
        {vote ∈ early | no_second_vote_in late vote = true} (s - 1) C') Hs :=
    Finset.disjoint_union_left.2 ⟨hHsEq.symm, hHsSup⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint h2, Finset.card_union_of_disjoint h1] at hcard
  have hNle : voters_count late ≤ voters_count (A.pool (s - 1)) := by
    refine Finset.card_le_card fun u hu => ?_
    obtain ⟨vote, hv, hval⟩ := (mem_participants_iff _ _).1 hu
    exact (mem_participants_iff _ _).2 ⟨vote, hLatePool hv, hval⟩
  unfold voters_count at hb hNle hVoters
  omega

end GoldilocksCorrectness.Proofs.Routines
