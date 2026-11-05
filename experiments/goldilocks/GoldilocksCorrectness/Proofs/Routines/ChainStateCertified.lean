module
public import GoldilocksCorrectness.Proofs.Routines.FinalityPair
import all Goldilocks.Config
import all Goldilocks.FG.ChainState
import all Goldilocks.FG.ValidatorClient

@[expose] public section

/-!
# The state transition over two pending pairs, and the first advance

`pending_pair_step`: one state transition keeps a pending justification, or finalizes at a height
at least its justification height; `first_advance_justified_or_timeout`: the first block of a chain
that leaves a height `h` took the justification branch or the timeout branch of the state
transition. Their proofs read `Proofs/Routines/FinalityPair.lean` or
`Proofs/Routines/Certificates.lean`.

Moved here unchanged from the execution pages.
-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded in the goal and in every
hypothesis: `omega` does not see a fact stated at either. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [RootOrder] in
/-- **Kit theorem, one state transition keeps a pending justification.** Take a pending
justification `e₀` of `σ` with at most one pending justification after it, and none unless
`σ.h ≥ h + 1`; `e₀.j < h ≤ σ.h`; and the state transition on the block `B` leaving a justification
height at most `h`. Then the transition finalizes at a height at least `e₀.j`, or it keeps `e₀`
pending in the same position, keeps every validator counted for `e₀.j`, and counts at `e₀.j` every
attestation of `B` with the finality pair `(e₀.j, e₀.T)`.

Why: counting the attestations keeps the pending list and adds to the participation at `e₀.j`
(`foldl_finality_participation`); the loop leaves `h_F'`, and when `h_F' < e₀.j` the filter keeps
`e₀` and its tail. A justification in this transition is at `σ.h`, at most `h`, so `σ.h = h` and the
tail is empty; then `newest` keeps `e₀` and the new pair (`K_W ≥ 2`), and the height becomes
`h + 1`. The participation at `e₀.j` is reset only by a justification at `e₀.j < σ.h`, which is not
this one.

The variables:
- `C`: the parameters; `σ`: the parent's chain state; `B`: the block; `e₀`: the pending
  justification; `h`: the bound on the justification height. -/
theorem pending_pair_step (C : Config) (σ : ChainState V) (B : Block V) (e₀ : PendingPair V)
    (h : Height)
    (hshape : ∃ l₁ l₂ : List (PendingPair V), σ.pending_finality = l₁ ++ e₀ :: l₂ ∧
      (l₂ = [] ∨ (l₂.length = 1 ∧ h + 1 ≤ σ.h)))
    (hj₀ : e₀.j < h) (hh : h ≤ σ.h)
    (hJ : (state_transition C σ B).h_j ≤ h) :
    e₀.j ≤ (state_transition C σ B).h_F ∨
      ((∃ l₁ l₂ : List (PendingPair V), (state_transition C σ B).pending_finality = l₁ ++ e₀ :: l₂ ∧
        (l₂ = [] ∨ (l₂.length = 1 ∧ h + 1 ≤ (state_transition C σ B).h))) ∧
      (∀ v ∈ σ.finality_participation e₀.j,
        v ∈ (state_transition C σ B).finality_participation e₀.j) ∧
      (∀ a ∈ B.attestations, a.finality_pair = some (FinalityPair.mk e₀.j e₀.T.root) →
        a.val_index ∈ (state_transition C σ B).finality_participation e₀.j)) := by
  obtain ⟨l₁, l₂, hpend, hl₂⟩ := hshape
  have he₀ : e₀ ∈ σ.pending_finality := by rw [hpend]; simp
  obtain ⟨tp, pr, fp, h1, -, -, -⟩ := process_attestations_eq σ B B.attestations
  have hfpeq : fp = (process_attestations σ B B.attestations).finality_participation := by
    rw [h1]
  -- the participation at `e₀.j` after the attestations are counted
  have hmono : ∀ v ∈ σ.finality_participation e₀.j, v ∈ fp e₀.j := by
    intro v hv
    rw [hfpeq, process_attestations_eq_foldl]
    exact foldl_finality_participation e₀.j e₀.T.root {v} B.attestations { σ with s := B.slot }
      ⟨e₀, he₀, rfl, rfl⟩
      (fun w hw => by rw [Finset.mem_singleton.1 hw]; exact Or.inl hv) v
      (Finset.mem_singleton_self v)
  have hadd : ∀ a ∈ B.attestations, a.finality_pair = some (FinalityPair.mk e₀.j e₀.T.root) →
      a.val_index ∈ fp e₀.j := by
    intro a ha hp
    rw [hfpeq, process_attestations_eq_foldl]
    exact foldl_finality_participation e₀.j e₀.T.root {a.val_index} B.attestations
      { σ with s := B.slot } ⟨e₀, he₀, rfl, rfl⟩
      (fun w hw => by rw [Finset.mem_singleton.1 hw]; exact Or.inr ⟨a, ha, rfl, hp⟩) a.val_index
      (Finset.mem_singleton_self _)
  obtain ⟨F', h_F', -, hc⟩ := process_height_events_cases C
    (process_attestations σ B B.attestations)
  rw [h1] at hc
  rw [state_transition_eq, h1] at hJ ⊢
  by_cases hF : e₀.j ≤ h_F'
  · left
    rcases hc with ⟨-, hR⟩ | ⟨-, -, -, hR⟩ | ⟨-, -, hR⟩ <;> rw [hR] <;> exact hF
  right
  have hF' : h_F' < e₀.j := Nat.lt_of_not_le hF
  have hfilt : σ.pending_finality.filter (fun e : PendingPair V => decide (h_F' < e.j)) =
      l₁.filter (fun e : PendingPair V => decide (h_F' < e.j)) ++
        e₀ :: l₂.filter (fun e : PendingPair V => decide (h_F' < e.j)) := by
    rw [hpend, List.filter_append, List.filter_cons_of_pos (by simpa using hF')]
  have hl₂f : l₂.filter (fun e : PendingPair V => decide (h_F' < e.j)) = [] ∨
      ((l₂.filter (fun e : PendingPair V => decide (h_F' < e.j))).length = 1 ∧ h + 1 ≤ σ.h) := by
    rcases hl₂ with rfl | ⟨hlen, hσ⟩
    · exact Or.inl rfl
    · rcases Nat.lt_or_ge (l₂.filter (fun e : PendingPair V => decide (h_F' < e.j))).length 1 with h0 | h0
      · exact Or.inl (List.length_eq_zero_iff.1 (by omega))
      · exact Or.inr ⟨le_antisymm (le_trans (List.length_filter_le _ _) hlen.le) h0, hσ⟩
  have hne : e₀.j ≠ σ.h := by omega_nat
  rcases hc with ⟨-, hR⟩ | ⟨-, -, -, hR⟩ | ⟨-, -, hR⟩ <;> rw [hR] at hJ ⊢
  · -- the justification branch: at `σ.h = h`, so nothing was after `e₀`
    simp only [advance_height_eq] at hJ ⊢
    have hσh : σ.h = h := le_antisymm hJ hh
    have hl₂0 : l₂.filter (fun e : PendingPair V => decide (h_F' < e.j)) = [] := by
      rcases hl₂f with h0 | ⟨-, hσ⟩
      · exact h0
      · omega_nat
    refine ⟨⟨(l₁.filter (fun e : PendingPair V => decide (h_F' < e.j))).drop
        ((l₁.filter (fun e : PendingPair V => decide (h_F' < e.j))).length + 2 - C.K_W),
        [PendingPair.mk σ.h σ.T_h], ?_, Or.inr ⟨rfl, by omega_nat⟩⟩, fun v hv => ?_,
        fun a ha hp => ?_⟩
    · rw [hfilt, hl₂0, List.append_assoc]
      rw [newest_append_of_length_le _ _ _ (by simp; have := C.K_W_ge_two; omega)]
      rfl
    · show v ∈ Function.update fp σ.h ∅ e₀.j
      rw [Function.update_of_ne hne]
      exact hmono v hv
    · show a.val_index ∈ Function.update fp σ.h ∅ e₀.j
      rw [Function.update_of_ne hne]
      exact hadd a ha hp
  · -- the timeout branch
    simp only [advance_height_eq]
    refine ⟨⟨l₁.filter (fun e : PendingPair V => decide (h_F' < e.j)), l₂.filter (fun e : PendingPair V => decide (h_F' < e.j)),
      hfilt, ?_⟩, hmono, hadd⟩
    rcases hl₂f with h0 | ⟨hlen, hσ⟩
    · exact Or.inl h0
    · exact Or.inr ⟨hlen, by omega_nat⟩
  · -- neither branch
    refine ⟨⟨l₁.filter (fun e : PendingPair V => decide (h_F' < e.j)), l₂.filter (fun e : PendingPair V => decide (h_F' < e.j)),
      hfilt, hl₂f⟩, hmono, hadd⟩

end

section

open GoldilocksCorrectness.Statements.Routines (chainStateOf)

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [RootOrder] in
/-- **The first advance past a height, with the justification height.** When `1 ≤ h` and the chain
state of `B` has a height greater than `h`, some block `Y`, `B` or an ancestor of `B` and not the
genesis block, has a parent at the height `h` and is itself at the height `h + 1`; and `Y`'s
justification height is `h`, or the slot of the parent's `T_h`, plus `δt`, is at most `Y`'s slot.

Why: as Lemma 67 (b) (`lem67b_first_advance_cases`), reading the branch of the state transition
that raised the height: the justification branch sets the justification height to the parent's
height, the timeout branch passed the slot test.

The variables:
- `C`: the parameters; `B`: the block; `h`: the height. -/
theorem first_advance_justified_or_timeout (C : Config) (B : Block V) (h : Height)
    (h1 : 1 ≤ h) (hlt : h < (chainStateOf C B).h) :
    ∃ Y : Block V, Y.AncestorEq B ∧ Y ≠ Block.genesis ∧
      (chainStateOf C Y.parent).h = h ∧ (chainStateOf C Y).h = h + 1 ∧
      ((chainStateOf C Y).h_j = h ∨ (chainStateOf C Y.parent).T_h.slot + C.δt ≤ Y.slot) := by
  induction B with
  | genesis =>
      exfalso
      have h0 : (chainStateOf C (Block.genesis : Block V)).h = 1 := rfl
      rw [h0] at hlt
      omega_nat
  | node p s r votes support ats v ih =>
      have hne : (Block.node p s r votes support ats v) ≠ Block.genesis := by intro h; cases h
      have hpB : p.AncestorEq (.node p s r votes support ats v) :=
        (ancestorEq_node_iff _ _ _ _ _ _ _ _).2 (Or.inr (ancestorEq_refl p))
      by_cases hp : h < (chainStateOf C p).h
      · obtain ⟨Y, hY, hY1, hY2, hY3, hY4⟩ := ih hp
        exact ⟨Y, ancestorEq_trans hY hpB, hY1, hY2, hY3, hY4⟩
      · have h2 := chainStateOf_height C _ hne
        change _ = (chainStateOf C p).h ∨ _ = (chainStateOf C p).h + 1 at h2
        have hadv : (chainStateOf C (.node p s r votes support ats v)).h =
            (chainStateOf C p).h + 1 := by
          rcases h2 with h2 | h2 <;> omega_nat
        have hhp : (chainStateOf C p).h = h := by omega_nat
        refine ⟨.node p s r votes support ats v, ancestorEq_refl _, hne, hhp, ?_, ?_⟩
        · rw [hadv, hhp]
        · change (chainStateOf C (.node p s r votes support ats v)).h_j = h ∨
            (chainStateOf C p).T_h.slot + C.δt ≤ s
          rw [chainStateOf_node] at hadv ⊢
          obtain ⟨tp, pr, fp, F', h_F', -, -, -, -, hc⟩ :=
            state_transition_cases C (chainStateOf C p) (.node p s r votes support ats v)
          rcases hc with ⟨-, hR⟩ | ⟨-, -, hδ, -⟩ | ⟨-, -, hR⟩
          · left
            rw [hR]
            exact hhp
          · right
            exact hδ
          · exfalso
            rw [hR] at hadv
            change (chainStateOf C p).h = (chainStateOf C p).h + 1 at hadv
            omega_nat

end

end

end GoldilocksCorrectness.Proofs.Routines
