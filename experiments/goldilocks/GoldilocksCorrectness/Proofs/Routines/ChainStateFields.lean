module
public import GoldilocksCorrectness.Proofs.Routines.ChainState
import all Goldilocks.Config
import all Goldilocks.FG.ChainState
import all Goldilocks.FG.ValidatorClient

@[expose] public section

/-!
# The chain-state field lemmas

What the routines of the chain state write, beyond the record equations of
`GoldilocksCorrectness/Proofs/Routines/ChainState.lean`: who `process_attestation` adds to each
participation set (`process_attestation_target_mem`, `process_attestation_progress_mem`,
`process_attestation_finality_mem`); the fold of `process_attestations` with an invariant asked
only of the attestations folded (`foldl_process_attestation_inv`, `process_attestations_eq_foldl`);
and the three branches of `process_height_events` with its loop over the pending justifications,
which writes `F` and `h_F` only and, when it writes them, to a pending justification whose
finality participation is a quorum (`process_height_events_branches`).
-/

set_option autoImplicit false

open scoped DC

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks

variable {V : Type} [DecidableEq V]

/-! ## One attestation -/

/-- A validator of the target participation after `process_attestation σ a` was there before,
or is `a`'s validator and `a` is a target vote at `σ.h` naming `σ.T_h`.

The variables:
- `σ`: the chain state; `a`: the attestation counted; `v`: the validator. -/
theorem process_attestation_target_mem (σ : ChainState V) (a : Attestation V) (v : V)
    -- `v` is in the target participation after `a` is counted
    (hv : v ∈ (process_attestation σ a).target_participation) :
    v ∈ σ.target_participation ∨
      (v = a.val_index ∧ a.h = σ.h ∧ a.T = σ.T_h.root ∧ a.τ = false) := by
  revert hv
  simp only [process_attestation, Id.run]
  split_ifs <;> intro hv <;> first
    | exact Or.inl hv
    | (rcases Finset.mem_union.mp hv with hv | hv
       · exact Or.inl hv
       · rw [Finset.mem_singleton.mp hv]; exact Or.inr ⟨rfl, by simp_all⟩)

/-- A validator of the progress set after `process_attestation σ a` was there before, or is
`a`'s validator and `a` votes at `σ.h` naming `σ.T_h`.

The variables:
- `σ`: the chain state; `a`: the attestation counted; `v`: the validator. -/
theorem process_attestation_progress_mem (σ : ChainState V) (a : Attestation V) (v : V)
    -- `v` is in the progress set after `a` is counted
    (hv : v ∈ (process_attestation σ a).progress) :
    v ∈ σ.progress ∨ (v = a.val_index ∧ a.h = σ.h ∧ a.T = σ.T_h.root) := by
  revert hv
  simp only [process_attestation, Id.run]
  split_ifs <;> intro hv <;> first
    | exact Or.inl hv
    | (rcases Finset.mem_union.mp hv with hv | hv
       · exact Or.inl hv
       · rw [Finset.mem_singleton.mp hv]; exact Or.inr ⟨rfl, by simp_all⟩)

/-- A validator of the finality participation at `j` after `process_attestation σ a` was there
before, or is `a`'s validator and `a` carries a finality pair at `j` naming a pending
justification of `σ`.

The variables:
- `σ`: the chain state; `a`: the attestation counted; `j`: the height; `v`: the validator. -/
theorem process_attestation_finality_mem (σ : ChainState V) (a : Attestation V) (j : Height)
    (v : V)
    -- `v` is in the finality participation at `j` after `a` is counted
    (hv : v ∈ (process_attestation σ a).finality_participation j) :
    v ∈ σ.finality_participation j ∨
      (v = a.val_index ∧ ∃ p : FinalityPair, a.finality_pair = some p ∧ p.hf = j ∧
        is_pending σ p = true) := by
  revert hv
  simp only [process_attestation, Id.run]
  split_ifs with h1 h2 <;> intro hv <;> first
    | exact Or.inl hv
    | skip
  all_goals
    change v ∈ Function.update σ.finality_participation (a.finality_pair.value h1).hf
      (σ.finality_participation (a.finality_pair.value h1).hf ∪ {a.val_index}) j at hv
    rw [Function.update_apply] at hv
    split_ifs at hv with hj
    · rcases Finset.mem_union.mp hv with hv | hv
      · subst hj; exact Or.inl hv
      · rw [Finset.mem_singleton.mp hv]
        obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.mp h1
        refine Or.inr ⟨rfl, p, hp, ?_, ?_⟩
        · rw [hj, value_eq_of_eq_some hp]
        · rw [← value_eq_of_eq_some hp h1]; exact h2
    · exact Or.inl hv

/-! ## The attestations of a block -/

/-- A fold of `process_attestation` over `atts` from a state satisfying `Inv` ends at a state
satisfying `Inv`, when counting any attestation of `atts` keeps `Inv`.

The variables:
- `Inv`: the invariant; `atts`: the attestations counted; `σ`: the starting chain state. -/
theorem foldl_process_attestation_inv (Inv : ChainState V → Prop) (atts : List (Attestation V))
    (σ : ChainState V)
    -- the starting state satisfies `Inv`
    (hσ : Inv σ)
    -- counting an attestation of `atts` keeps `Inv`
    (hstep : ∀ a ∈ atts, ∀ σ' : ChainState V, Inv σ' → Inv (process_attestation σ' a)) :
    Inv (atts.foldl process_attestation σ) := by
  induction atts generalizing σ with
  | nil => exact hσ
  | cons a atts ih =>
      rw [List.foldl_cons]
      exact ih _ (hstep a List.mem_cons_self σ hσ)
        (fun a' ha' σ' h => hstep a' (List.mem_cons_of_mem _ ha') σ' h)

/-- `process_attestations σ B atts` is the fold of `process_attestation` over `atts` from `σ` with
the slot `B.slot`, with `B` as the latest block.

The variables:
- `σ`: the chain state; `B`: the block; `atts`: the attestations counted. -/
theorem process_attestations_eq_foldl (σ : ChainState V) (B : Block V)
    (atts : List (Attestation V)) :
    process_attestations σ B atts =
      { atts.foldl process_attestation { σ with s := B.slot } with L := B } := by
  simp only [process_attestations, Id.run, List.forIn_pure_yield_eq_foldl]
  rfl

/-! ## The height events -/

variable [Fintype V]

omit [DecidableEq V] in
/-- The three branches of `process_height_events C σ`, with the loop over the pending
justifications: the loop leaves `σ` with some `F'` and `h_F'`, which are `σ.F` and `σ.h_F`, or the
block and the height of a pending justification `e` whose finality participation
`σ.finality_participation e.j` is a quorum; then the justification branch, the timeout branch, or
neither, runs on the state the loop and the filter of the pending justifications left.

The variables:
- `C`: the parameters; `σ`: the chain state. -/
theorem process_height_events_branches (C : Config) (σ : ChainState V) :
    ∃ (F' : Block V) (h_F' : Height),
      ((F' = σ.F ∧ h_F' = σ.h_F) ∨
        ∃ e ∈ σ.pending_finality, F' = e.T ∧ h_F' = e.j ∧
          quorum V ≤ (σ.finality_participation e.j).card) ∧
      ((quorum V ≤ σ.target_participation.card ∧
          process_height_events C σ = advance_height
            { σ with
              pending_finality := newest C.K_W
                (σ.pending_finality.filter (fun e => decide (h_F' < e.j)) ++
                  [PendingPair.mk σ.h σ.T_h]),
              finality_participation := Function.update σ.finality_participation σ.h ∅,
              J := σ.T_h, h_j := σ.h, F := F', h_F := h_F' }) ∨
        (¬ quorum V ≤ σ.target_participation.card ∧ quorum V ≤ σ.progress.card ∧
          σ.T_h.slot + C.δt ≤ σ.s ∧
          process_height_events C σ = advance_height
            { σ with
              pending_finality := σ.pending_finality.filter (fun e => decide (h_F' < e.j)),
              F := F', h_F := h_F' }) ∨
        (¬ quorum V ≤ σ.target_participation.card ∧
          ¬ (quorum V ≤ σ.progress.card ∧ σ.T_h.slot + C.δt ≤ σ.s) ∧
          process_height_events C σ =
            { σ with
              pending_finality := σ.pending_finality.filter (fun e => decide (h_F' < e.j)),
              F := F', h_F := h_F' })) := by
  -- the loop writes `F` and `h_F` only, to a pending justification with a quorate participation
  obtain ⟨F', h_F', hu, hh⟩ : ∃ (F' : Block V) (h_F' : Height),
      forIn (m := Id) σ.pending_finality σ (fun (e : PendingPair V) (r : ChainState V) =>
        if quorum V ≤ r.finality_participation[e.j].card then
          pure (ForInStep.yield { r with F := e.T, h_F := e.j })
        else pure (ForInStep.yield r)) = (pure { σ with F := F', h_F := h_F' } : Id (ChainState V)) ∧
      ((F' = σ.F ∧ h_F' = σ.h_F) ∨
        ∃ e ∈ σ.pending_finality, F' = e.T ∧ h_F' = e.j ∧
          quorum V ≤ (σ.finality_participation e.j).card) := by
    refine forIn_step_inv σ.pending_finality σ _
      (fun r => ∃ (F' : Block V) (h_F' : Height),
        (r : Id (ChainState V)) = (pure { σ with F := F', h_F := h_F' } : Id (ChainState V)) ∧
        ((F' = σ.F ∧ h_F' = σ.h_F) ∨
          ∃ e ∈ σ.pending_finality, F' = e.T ∧ h_F' = e.j ∧
            quorum V ≤ (σ.finality_participation e.j).card))
      ⟨σ.F, σ.h_F, rfl, Or.inl ⟨rfl, rfl⟩⟩ ?_
    rintro e he r ⟨F', h_F', rfl, hh⟩
    split
    · rename_i hq
      exact ⟨_, rfl, e.T, e.j, rfl, Or.inr ⟨e, he, rfl, rfl, hq⟩⟩
    · exact ⟨_, rfl, F', h_F', rfl, hh⟩
  refine ⟨F', h_F', hh, ?_⟩
  simp only [process_height_events, Id.run]
  rw [hu, pure_bind]
  by_cases h1 : quorum V ≤ σ.target_participation.card
  · exact Or.inl ⟨h1, by simp only [h1, if_true]; rfl⟩
  · by_cases h2 : quorum V ≤ σ.progress.card ∧ σ.T_h.slot + C.δt ≤ σ.s
    · refine Or.inr (Or.inl ⟨h1, h2.1, h2.2, ?_⟩)
      simp only [h1, if_false, h2.1, h2.2, decide_true, Bool.and_self, if_true]
      rfl
    · refine Or.inr (Or.inr ⟨h1, h2, ?_⟩)
      have h2' : (decide (quorum V ≤ σ.progress.card) && decide (σ.T_h.slot + C.δt ≤ σ.s)) =
          false := by
        simpa [Bool.and_eq_true] using h2
      simp only [h1, if_false, h2', Bool.false_eq_true]
      rfl

end GoldilocksCorrectness.Proofs.Routines
