module
public import GoldilocksCorrectness.Proofs.Routines.Blocks
public import Goldilocks.Node
import all Goldilocks.Config
import all Goldilocks.FG.ChainState
import all Goldilocks.FG.State
import all Goldilocks.FG.ValidatorClient
import all Goldilocks.Node

@[expose] public section

/-!
# The chain-state facts and the certificate, at the routine level

The proofs of the statements of `GoldilocksCorrectness/Statements/Routines/ChainStateStatements.lean`:
what the state transition `state_transition C σ B` of a block `B` does to the chain state `σ` of
its parent (Lemma 47, parts (a) to (c)), the certificate (Lemmas 51 and 51b), the inclusion of a
pool attestation in a proposal (Lemma 52), and two kit facts on attestations
(`valid_attestation_of_height`, `create_attestation_well_formed`).

The route: `process_attestation` writes only the participation sets
(`process_attestation_eq`), so `process_attestations` writes only those, the slot and the latest
block (`process_attestations_eq`); the loop over the pending justifications of
`process_height_events` writes only `F` and `h_F`, with `h_F` one of the pending heights or left
(`process_height_events_cases`), after which one of the three branches runs.
-/

set_option autoImplicit false

open scoped DC

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks

/-! ## A `for` loop whose body always continues -/

/-- A `for` loop over the list `l` from a value satisfying `Inv` ends at a value satisfying `Inv`,
when the body, on every element of `l` and every value satisfying `Inv`, continues with a value
satisfying `Inv`.

The variables:
- `l`: the list walked; `init`: the starting value; `body`: the loop's body; `Inv`: the
  invariant. -/
theorem forIn_step_inv {α β : Type} (l : List α) (init : β)
    (body : α → β → Id (ForInStep β)) (Inv : β → Prop) (hinit : Inv init)
    -- on every element of `l`, the body continues from a value satisfying `Inv` with one
    (hbody : ∀ a ∈ l, ∀ b, Inv b → ∃ b', body a b = pure (ForInStep.yield b') ∧ Inv b') :
    Inv (forIn (m := Id) l init body) := by
  induction l generalizing init with
  | nil => exact hinit
  | cons a l ih =>
      rw [List.forIn_cons]
      obtain ⟨b', hb', hI⟩ := hbody a List.mem_cons_self init hinit
      rw [hb']
      exact ih b' hI (fun a' ha' b hb => hbody a' (List.mem_cons_of_mem _ ha') b hb)

variable {V : Type} [DecidableEq V]

/-! ## One attestation -/

/-- Counting one attestation writes only the participation sets, adds to the sets
`target_participation` and `progress`, and adds the attestation's validator to `progress`, and
to `target_participation` when it is a target, when it votes at the height `σ.h` for `σ.T_h`.

The variables:
- `σ`: the chain state; `a`: the attestation counted. -/
theorem process_attestation_eq (σ : ChainState V) (a : Attestation V) :
    ∃ (tp pr : Finset V) (fp : Height → Finset V),
      process_attestation σ a =
        { σ with target_participation := tp, progress := pr, finality_participation := fp } ∧
      σ.target_participation ⊆ tp ∧ σ.progress ⊆ pr ∧
      (a.h = σ.h → a.T = σ.T_h.root →
        a.val_index ∈ pr ∧ (a.τ = false → a.val_index ∈ tp)) := by
  simp only [process_attestation, Id.run]
  split_ifs with h1 h2 h3 h4 h3 h4 h3 h4 <;>
    refine ⟨_, _, _, rfl, ?_, ?_, ?_⟩ <;>
    simp_all

/-- Counting the attestations of a list in order writes only the participation sets, adds to the
sets `target_participation` and `progress`, and adds the validator of each attestation of the list
that votes at the height `σ.h` for `σ.T_h` to `progress`, and to `target_participation` when it is
a target.

The variables:
- `atts`: the list counted; `σ`: the chain state it starts from. -/
theorem foldl_process_attestation_eq (atts : List (Attestation V)) (σ : ChainState V) :
    ∃ (tp pr : Finset V) (fp : Height → Finset V),
      atts.foldl process_attestation σ =
        { σ with target_participation := tp, progress := pr, finality_participation := fp } ∧
      σ.target_participation ⊆ tp ∧ σ.progress ⊆ pr ∧
      ∀ a ∈ atts, a.h = σ.h → a.T = σ.T_h.root →
        a.val_index ∈ pr ∧ (a.τ = false → a.val_index ∈ tp) := by
  induction atts generalizing σ with
  | nil => exact ⟨_, _, _, rfl, subset_refl _, subset_refl _, fun a ha => absurd ha List.not_mem_nil⟩
  | cons a atts ih =>
      obtain ⟨tp₁, pr₁, fp₁, h₁, htp₁, hpr₁, ha₁⟩ := process_attestation_eq σ a
      obtain ⟨tp₂, pr₂, fp₂, h₂, htp₂, hpr₂, ha₂⟩ := ih (process_attestation σ a)
      rw [List.foldl_cons, h₂, h₁]
      rw [h₁] at htp₂ hpr₂ ha₂
      refine ⟨tp₂, pr₂, fp₂, rfl, htp₁.trans htp₂, hpr₁.trans hpr₂, fun a' ha' hh hT => ?_⟩
      rcases List.mem_cons.mp ha' with rfl | ha'
      · obtain ⟨hp, ht⟩ := ha₁ hh hT
        exact ⟨hpr₂ hp, fun hτ => htp₂ (ht hτ)⟩
      · exact ha₂ a' ha' hh hT

/-- `process_attestations σ B atts` writes only the slot (`B`'s), the latest block (`B`) and the
participation sets; it adds to `target_participation` and `progress`, and adds the validator of
each attestation of `atts` that votes at the height `σ.h` for `σ.T_h` to `progress`, and to
`target_participation` when it is a target.

The variables:
- `σ`: the chain state; `B`: the block; `atts`: the attestations counted. -/
theorem process_attestations_eq (σ : ChainState V) (B : Block V) (atts : List (Attestation V)) :
    ∃ (tp pr : Finset V) (fp : Height → Finset V),
      process_attestations σ B atts =
        { σ with s := B.slot, L := B, target_participation := tp, progress := pr, finality_participation := fp } ∧
      σ.target_participation ⊆ tp ∧ σ.progress ⊆ pr ∧
      ∀ a ∈ atts, a.h = σ.h → a.T = σ.T_h.root →
        a.val_index ∈ pr ∧ (a.τ = false → a.val_index ∈ tp) := by
  obtain ⟨tp, pr, fp, h, htp, hpr, ha⟩ := foldl_process_attestation_eq atts { σ with s := B.slot }
  refine ⟨tp, pr, fp, ?_, htp, hpr, ha⟩
  simp only [process_attestations, Id.run, List.forIn_pure_yield_eq_foldl, h]
  rfl

/-! ## The height events -/

variable [Fintype V]

omit [DecidableEq V] in
/-- The three cases of `process_height_events C σ`: the loop over the pending justifications
leaves `σ` with some `F'` and `h_F'`, `h_F'` being `σ.h_F` or the height of a pending
justification; then the justification branch, the timeout branch, or neither, runs on the state
the loop and the filter of the pending justifications left.

The variables:
- `C`: the parameters; `σ`: the chain state. -/
theorem process_height_events_cases (C : Config) (σ : ChainState V) :
    ∃ (F' : Block V) (h_F' : Height),
      (h_F' = σ.h_F ∨ ∃ e ∈ σ.pending_finality, h_F' = e.j) ∧
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
  -- the loop writes `F` and `h_F` only
  obtain ⟨F', h_F', hu, hh⟩ : ∃ (F' : Block V) (h_F' : Height),
      forIn (m := Id) σ.pending_finality σ (fun (e : PendingPair V) (r : ChainState V) =>
        if quorum V ≤ r.finality_participation[e.j].card then
          pure (ForInStep.yield { r with F := e.T, h_F := e.j })
        else pure (ForInStep.yield r)) = (pure { σ with F := F', h_F := h_F' } : Id (ChainState V)) ∧
      (h_F' = σ.h_F ∨ ∃ e ∈ σ.pending_finality, h_F' = e.j) := by
    refine forIn_step_inv σ.pending_finality σ _
      (fun r => ∃ (F' : Block V) (h_F' : Height),
        (r : Id (ChainState V)) = (pure { σ with F := F', h_F := h_F' } : Id (ChainState V)) ∧
        (h_F' = σ.h_F ∨ ∃ e ∈ σ.pending_finality, h_F' = e.j))
      ⟨σ.F, σ.h_F, rfl, Or.inl rfl⟩ ?_
    rintro e he r ⟨F', h_F', rfl, hh⟩
    split
    · exact ⟨_, rfl, e.T, e.j, rfl, Or.inr ⟨e, he, rfl⟩⟩
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

/-! ## The state transition -/

omit [DecidableEq V] [Fintype V] in
/-- `advance_height σ` is `σ` with the height raised by one, `T_h` the latest block and the two
participation sets emptied. -/
theorem advance_height_eq (σ : ChainState V) :
    advance_height σ =
      { σ with h := σ.h + 1, T_h := σ.L, target_participation := ∅, progress := ∅ } := by rfl

/-- The state transition is the counting of the block's attestations, then the height events. -/
theorem state_transition_eq (C : Config) (σ : ChainState V) (B : Block V) :
    state_transition C σ B = process_height_events C (process_attestations σ B B.attestations) :=
  by rfl

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded in the goal and in every
hypothesis: `omega` does not see a fact stated at either. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

/-- What the state transition does, in one of three cases: the attestations are counted into the
participation sets `tp` and `pr` (which contain the parent's, and contain the validator of every
attestation of `B` at the height `σ.h` for `σ.T_h`, the targets in `tp`); the loop over the
pending justifications leaves `F'` and `h_F'`, `h_F'` being `σ.h_F` or a pending height; then the
justification branch, the timeout branch, or neither, runs.

The variables:
- `C`: the parameters; `σ`: the parent's chain state; `B`: the block. -/
theorem state_transition_cases (C : Config) (σ : ChainState V) (B : Block V) :
    ∃ (tp pr : Finset V) (fp : Height → Finset V) (F' : Block V) (h_F' : Height),
      σ.target_participation ⊆ tp ∧ σ.progress ⊆ pr ∧
      (∀ a ∈ B.attestations, a.h = σ.h → a.T = σ.T_h.root →
        a.val_index ∈ pr ∧ (a.τ = false → a.val_index ∈ tp)) ∧
      (h_F' = σ.h_F ∨ ∃ e ∈ σ.pending_finality, h_F' = e.j) ∧
      ((quorum V ≤ tp.card ∧
          state_transition C σ B =
            { σ with
              s := B.slot, L := B, h := σ.h + 1, T_h := B, target_participation := ∅,
              progress := ∅,
              pending_finality := newest C.K_W
                (σ.pending_finality.filter (fun e => decide (h_F' < e.j)) ++
                  [PendingPair.mk σ.h σ.T_h]),
              finality_participation := Function.update fp σ.h ∅,
              J := σ.T_h, h_j := σ.h, F := F', h_F := h_F' }) ∨
        (¬ quorum V ≤ tp.card ∧ quorum V ≤ pr.card ∧ σ.T_h.slot + C.δt ≤ B.slot ∧
          state_transition C σ B =
            { σ with
              s := B.slot, L := B, h := σ.h + 1, T_h := B, target_participation := ∅,
              progress := ∅,
              pending_finality := σ.pending_finality.filter (fun e => decide (h_F' < e.j)),
              finality_participation := fp, F := F', h_F := h_F' }) ∨
        (¬ quorum V ≤ tp.card ∧ ¬ (quorum V ≤ pr.card ∧ σ.T_h.slot + C.δt ≤ B.slot) ∧
          state_transition C σ B =
            { σ with
              s := B.slot, L := B, target_participation := tp, progress := pr,
              pending_finality := σ.pending_finality.filter (fun e => decide (h_F' < e.j)),
              finality_participation := fp, F := F', h_F := h_F' })) := by
  obtain ⟨tp, pr, fp, h1, htp, hpr, hmem⟩ := process_attestations_eq σ B B.attestations
  obtain ⟨F', h_F', hh, hc⟩ :=
    process_height_events_cases C (process_attestations σ B B.attestations)
  rw [h1] at hh hc
  refine ⟨tp, pr, fp, F', h_F', htp, hpr, hmem, hh, ?_⟩
  rw [state_transition_eq, h1]
  rcases hc with ⟨hq, hR⟩ | ⟨hq, hq', hs, hR⟩ | ⟨hq, hq', hR⟩
  · exact Or.inl ⟨hq, hR⟩
  · exact Or.inr (Or.inl ⟨hq, hq', hs, hR⟩)
  · exact Or.inr (Or.inr ⟨hq, hq', hR⟩)

/-! ## Lemma 47, parts (a) to (c), over the state transition -/

/-- **Lemma 47 (a), over the state transition.** The proof; the audited statement is in
`Statements/Routines/ChainStateStatements.lean`.

The variables:
- `C`: the parameters; `σ`: the parent's chain state; `B`: the block. -/
theorem lem47a_state_transition_bounds (C : Config) (σ : ChainState V) (B : Block V)
    (hj : σ.h_j < σ.h) (hF : σ.h_F ≤ σ.h_j)
    (hpend : ∀ e ∈ σ.pending_finality, e.j ≤ σ.h_j) :
    1 ≤ (state_transition C σ B).h ∧
      (state_transition C σ B).h_j < (state_transition C σ B).h ∧
      (state_transition C σ B).h_F ≤ (state_transition C σ B).h_j ∧
      ∀ e ∈ (state_transition C σ B).pending_finality, e.j ≤ (state_transition C σ B).h_j := by
  obtain ⟨tp, pr, fp, F', h_F', -, -, -, hh, hc⟩ := state_transition_cases C σ B
  have hF' : h_F' ≤ σ.h_j := by
    rcases hh with rfl | ⟨e, he, rfl⟩
    · exact hF
    · exact hpend e he
  rcases hc with ⟨-, hR⟩ | ⟨-, -, -, hR⟩ | ⟨-, -, hR⟩ <;> rw [hR]
  · refine ⟨by omega_nat, by omega_nat, by dsimp only; omega_nat, fun e he => ?_⟩
    dsimp only at he ⊢
    rcases List.mem_append.mp (List.mem_of_mem_drop he) with he | he
    · have := hpend e (List.mem_filter.mp he).1
      omega_nat
    · rw [List.mem_singleton.mp he]
  · refine ⟨by omega_nat, by dsimp only; omega_nat, by dsimp only; omega_nat, fun e he => ?_⟩
    exact hpend e (List.mem_filter.mp he).1
  · refine ⟨by dsimp only; omega_nat, by dsimp only; omega_nat, by dsimp only; omega_nat,
      fun e he => ?_⟩
    exact hpend e (List.mem_filter.mp he).1

/-- **Lemma 47 (b), over the state transition.** The proof; the audited statement is in
`Statements/Routines/ChainStateStatements.lean`.

The variables:
- `C`: the parameters; `σ`: the parent's chain state; `B`: the block. -/
theorem lem47b_state_transition_height (C : Config) (σ : ChainState V) (B : Block V) :
    (state_transition C σ B).h = σ.h ∨ (state_transition C σ B).h = σ.h + 1 := by
  obtain ⟨tp, pr, fp, F', h_F', -, -, -, -, hc⟩ := state_transition_cases C σ B
  rcases hc with ⟨-, hR⟩ | ⟨-, -, -, hR⟩ | ⟨-, -, hR⟩ <;> rw [hR]
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- **Lemma 47 (c), over the state transition.** The proof; the audited statement is in
`Statements/Routines/ChainStateStatements.lean`.

The variables:
- `C`: the parameters; `σ`: the parent's chain state; `B`: the block. -/
theorem lem47c_state_transition_T_h (C : Config) (σ : ChainState V) (B : Block V) :
    ((state_transition C σ B).h = σ.h → (state_transition C σ B).T_h = σ.T_h) ∧
      ((state_transition C σ B).h = σ.h + 1 → (state_transition C σ B).T_h = B) := by
  obtain ⟨tp, pr, fp, F', h_F', -, -, -, -, hc⟩ := state_transition_cases C σ B
  rcases hc with ⟨-, hR⟩ | ⟨-, -, -, hR⟩ | ⟨-, -, hR⟩ <;> rw [hR]
  · exact ⟨fun h => absurd h (by dsimp only; omega_nat), fun _ => rfl⟩
  · exact ⟨fun h => absurd h (by dsimp only; omega_nat), fun _ => rfl⟩
  · exact ⟨fun _ => rfl, fun h => absurd h (by dsimp only; omega_nat)⟩

/-- The justification of the state transition: the parent's justification is kept, or the
justified block becomes the parent's `T_h` at the parent's height.

The variables:
- `C`: the parameters; `σ`: the parent's chain state; `B`: the block. -/
theorem state_transition_justification (C : Config) (σ : ChainState V) (B : Block V) :
    ((state_transition C σ B).h_j = σ.h_j ∧ (state_transition C σ B).J = σ.J) ∨
      ((state_transition C σ B).h_j = σ.h ∧ (state_transition C σ B).J = σ.T_h) := by
  obtain ⟨tp, pr, fp, F', h_F', -, -, -, -, hc⟩ := state_transition_cases C σ B
  rcases hc with ⟨-, hR⟩ | ⟨-, -, -, hR⟩ | ⟨-, -, hR⟩ <;> rw [hR]
  · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩

/-! ## Lemmas 51 and 51b, the certificate -/

/-- **Lemma 51, a quorum of votes at the parent's height is a certificate.** The proof; the
audited statement is in `Statements/Routines/ChainStateStatements.lean`.

The variables:
- `C`: the parameters; `σ`: the parent's chain state; `B`: the block; `Q`: the quorum. -/
theorem lem51_quorum_is_certificate (C : Config) (σ : ChainState V) (B : Block V) (Q : Finset V)
    (hQ : quorum V ≤ Q.card)
    (hAtts : ∀ v ∈ Q, ∃ a ∈ B.attestations, a.val_index = v ∧ a.h = σ.h ∧ a.T = σ.T_h.root) :
    ((state_transition C σ B).h = σ.h + 1 ∨
      ((state_transition C σ B).h = σ.h ∧ Q ⊆ (state_transition C σ B).progress ∧
        B.slot < σ.T_h.slot + C.δt)) ∧
    ((∀ v ∈ Q, ∃ a ∈ B.attestations, a.val_index = v ∧ a.h = σ.h ∧ a.T = σ.T_h.root ∧
        a.τ = false) →
      (state_transition C σ B).h = σ.h + 1 ∧ (state_transition C σ B).J = σ.T_h ∧
        (state_transition C σ B).h_j = σ.h) := by
  obtain ⟨tp, pr, fp, F', h_F', -, -, hmem, -, hc⟩ := state_transition_cases C σ B
  have hQpr : Q ⊆ pr := by
    intro v hv
    obtain ⟨a, ha, rfl, hh, hT⟩ := hAtts v hv
    exact (hmem a ha hh hT).1
  have hQcard : quorum V ≤ pr.card := le_trans hQ (Finset.card_le_card hQpr)
  refine ⟨?_, fun hT => ?_⟩
  · rcases hc with ⟨-, hR⟩ | ⟨-, -, -, hR⟩ | ⟨-, hq', hR⟩ <;> rw [hR]
    · exact Or.inl rfl
    · exact Or.inl rfl
    · refine Or.inr ⟨rfl, hQpr, ?_⟩
      have hs : ¬ σ.T_h.slot + C.δt ≤ B.slot := fun hs => hq' ⟨hQcard, hs⟩
      omega_nat
  · have hQtp : Q ⊆ tp := by
      intro v hv
      obtain ⟨a, ha, rfl, hh, hT', hτ⟩ := hT v hv
      exact (hmem a ha hh hT').2 hτ
    have hq : quorum V ≤ tp.card := le_trans hQ (Finset.card_le_card hQtp)
    rcases hc with ⟨-, hR⟩ | ⟨hq', -, -, -⟩ | ⟨hq', -, -⟩
    · rw [hR]
      exact ⟨rfl, rfl, rfl⟩
    · exact absurd hq hq'
    · exact absurd hq hq'

/-- **Lemma 51b, the progress quorum advances the height at the timeout slot.** The proof; the
audited statement is in `Statements/Routines/ChainStateStatements.lean`.

The variables:
- `C`: the parameters; `σ`: the parent's chain state; `B`: the block. -/
theorem lem51b_progress_quorum_advances (C : Config) (σ : ChainState V) (B : Block V)
    (hQ : quorum V ≤ σ.progress.card)
    (hSlot : σ.T_h.slot + C.δt ≤ B.slot) :
    (state_transition C σ B).h = σ.h + 1 := by
  obtain ⟨tp, pr, fp, F', h_F', -, hpr, -, -, hc⟩ := state_transition_cases C σ B
  have hq : quorum V ≤ pr.card := le_trans hQ (Finset.card_le_card hpr)
  rcases hc with ⟨-, hR⟩ | ⟨-, -, -, hR⟩ | ⟨-, hq', -⟩
  · rw [hR]
  · rw [hR]
  · exact absurd ⟨hq, hSlot⟩ hq'

/-! ## Lemma 52 and the kit facts on attestations -/

omit [DecidableEq V] [Fintype V] in
/-- **Kit fact, an attestation at the parent's height naming its `T_h` is valid.** The proof; the
audited statement is in `Statements/Routines/ChainStateStatements.lean`.

The variables:
- `σ`: the chain state; `a`: the attestation. -/
theorem valid_attestation_of_height (σ : ChainState V) (a : Attestation V)
    (hh : a.h = σ.h) (hT : a.T = σ.T_h.root) : valid_attestation σ a = true := by
  simp [valid_attestation, Id.run, hh, hT]
  rfl

omit [Fintype V] in
/-- **Lemma 52, a valid pool attestation not on the parent's chain is included.** The proof; the
audited statement is in `Statements/Routines/ChainStateStatements.lean`.

The variables:
- `S`: the FG state; `H`: the parent; `a`: the attestation. -/
theorem lem52_pool_attestation_included [RootOrder] (S : FGState V) (H : Block V)
    (a : Attestation V) (hPool : a ∈ S.attestations)
    (hValid : valid_attestation (S.σ H) a = true) (hNew : on_chain a H = false) :
    a ∈ proposal_attestations S H := by
  simp only [proposal_attestations, List.mem_filter]
  refine ⟨hPool, ?_⟩
  simp only [Bool.and_eq_true, Bool.not_eq_true']
  exact ⟨hValid, hNew⟩

omit [DecidableEq V] [Fintype V] in
/-- A height pair `height_pair` computes from a source with the height `h_c` and the root `T_c`
that is a vote is at the height `h_c` and names `T_c`.

The variables:
- `Λ`: the record; `h_c`, `T_c`: the source's height and root; `fp`: the finality pair;
- `h`, `T`, `τ`: the vote. -/
theorem height_pair_vote {Λ : SigningHistory} {h_c : Height} {T_c : BlockId}
    {fp : Option FinalityPair} {h : Height} {T : BlockId} {τ : Bool}
    (hp : height_pair Λ (some (h_c, T_c)) fp = .vote h T τ) : h = h_c ∧ T = T_c := by
  simp only [height_pair, Id.run] at hp
  split_ifs at hp <;> injection hp with h1 h2 h3 <;> exact ⟨h1.symm, h2.symm⟩

omit [DecidableEq V] [Fintype V] in
/-- The extraction of an option known to be `some p` is `p`.

The variables:
- `x`: the option; `p`: its value; `h`: the proof that `x` is present. -/
theorem value_eq_of_eq_some {α : Type} {x : Option α} {p : α} (hx : x = some p)
    (h : x ≠ ⊥) : x.value h = p := by
  subst hx
  rfl

omit [DecidableEq V] [Fintype V] in
/-- An attestation is well formed exactly when its height is at least `1` and its finality pair,
when present, is at a lesser height.

The variables:
- `a`: the attestation. -/
theorem attestation_well_formed_iff (a : Attestation V) :
    attestation_well_formed a = true ↔
      1 ≤ a.h ∧ ∀ p : FinalityPair, a.finality_pair = some p → p.hf < a.h := by
  simp only [attestation_well_formed, Id.run]
  split
  · rename_i hfp
    obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.mp hfp
    rw [value_eq_of_eq_some hp]
    show (decide (1 ≤ a.h) && decide (p.hf < a.h)) = true ↔ _
    simp [hp]
  · rename_i hfp
    simp only [ne_eq, Decidable.not_not] at hfp
    show decide (1 ≤ a.h) = true ↔ _
    simp [hfp]

omit [DecidableEq V] [Fintype V] in
/-- **Kit fact, an attestation the validator client builds is well formed.** The proof; the
audited statement is in `Statements/Routines/ChainStateStatements.lean`.

The variables:
- `Λ`: the record; `v`: the validator; `h_c`, `T_c`: the source's height and root;
- `h_j`, `J`, `h_F`: the head's justification height, justified root and finalization height;
- `a`: the attestation built. -/
theorem create_attestation_well_formed (Λ : SigningHistory) (v : V) (h_c : Height)
    (T_c : BlockId) (h_j : Height) (J : BlockId) (h_F : Height) (a : Attestation V)
    (h1 : 1 ≤ h_c) (hBuilt : (create_attestation Λ v h_c T_c h_j J h_F).2 = some a) :
    attestation_well_formed a = true := by
  simp only [create_attestation, Id.run] at hBuilt
  split at hBuilt
  · cases hBuilt
  · rename_i h T τ hhp
    obtain ⟨rfl, rfl⟩ := height_pair_vote hhp
    split_ifs at hBuilt with hs hfp hle
    · injection hBuilt with hBuilt
      subst hBuilt
      exact (attestation_well_formed_iff _).2 ⟨h1, fun p hp => by cases hp⟩
    · injection hBuilt with hBuilt
      subst hBuilt
      refine (attestation_well_formed_iff _).2 ⟨h1, fun p hp => ?_⟩
      rw [value_eq_of_eq_some hp] at hle
      omega_nat
    · injection hBuilt with hBuilt
      subst hBuilt
      refine (attestation_well_formed_iff _).2 ⟨h1, fun p hp => ?_⟩
      simp only [ne_eq, Decidable.not_not] at hfp
      dsimp only at hp
      rw [hfp] at hp
      cases hp

end GoldilocksCorrectness.Proofs.Routines

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
variable {V : Type}
variable [DecidableEq V] [Fintype V]

/-- When the parent's chain state has its justification height less than its height, its
finalization height at most its justification height, and every pending justification at a height
at most its justification height, every pending justification of the chain state of `B` is at a
height greater than its finalization height.

Why: the pending justifications kept are those of height greater than the finalization height the
loop leaves; the one appended is at the parent's height, greater than that finalization height,
which is the parent's or a pending height.

The variables:
- `C`: the parameters; `σ`: the parent's chain state; `B`: the block. -/
theorem state_transition_pending_above (C : Config) (σ : ChainState V) (B : Block V)
    -- the parent's justification height is less than its height
    (hj : σ.h_j < σ.h)
    -- the parent's finalization height is at most its justification height
    (hF : σ.h_F ≤ σ.h_j)
    -- every pending justification of the parent is at a height at most its justification height
    (hpend : ∀ e ∈ σ.pending_finality, e.j ≤ σ.h_j) :
    ∀ e ∈ (state_transition C σ B).pending_finality, (state_transition C σ B).h_F < e.j := by
  obtain ⟨tp, pr, fp, F', h_F', -, -, -, hh, hc⟩ := state_transition_cases C σ B
  have hlt : h_F' < σ.h := by
    rcases hh with h | ⟨e, he, h⟩
    · rw [h]; omega_nat
    · have := hpend e he; rw [h]; omega_nat
  rcases hc with ⟨-, hR⟩ | ⟨-, -, -, hR⟩ | ⟨-, -, hR⟩ <;> rw [hR] <;> intro e he
  · rcases List.mem_append.mp (List.mem_of_mem_drop he) with he | he
    · exact of_decide_eq_true (List.mem_filter.mp he).2
    · rw [List.mem_singleton.mp he]; exact hlt
  · exact of_decide_eq_true (List.mem_filter.mp he).2
  · exact of_decide_eq_true (List.mem_filter.mp he).2

/-- When every pending justification of the parent's chain state is at a height greater than its
finalization height, the chain state of `B` has a finalization height at least the parent's.

The variables:
- `C`: the parameters; `σ`: the parent's chain state; `B`: the block. -/
theorem state_transition_h_F_mono (C : Config) (σ : ChainState V) (B : Block V)
    -- every pending justification of the parent is at a height greater than its finalization
    -- height
    (habove : ∀ e ∈ σ.pending_finality, σ.h_F < e.j) :
    σ.h_F ≤ (state_transition C σ B).h_F := by
  obtain ⟨tp, pr, fp, F', h_F', -, -, -, hh, hc⟩ := state_transition_cases C σ B
  have hge : σ.h_F ≤ h_F' := by
    rcases hh with h | ⟨e, he, h⟩
    · rw [h]
    · have := habove e he; rw [h]; exact le_of_lt this
  rcases hc with ⟨-, hR⟩ | ⟨-, -, -, hR⟩ | ⟨-, -, hR⟩ <;> rw [hR] <;> exact hge

/-- When the parent's justification height is less than its height, the chain state of `B` has a
justification height at least the parent's.

The variables:
- `C`: the parameters; `σ`: the parent's chain state; `B`: the block. -/
theorem state_transition_h_j_mono (C : Config) (σ : ChainState V) (B : Block V)
    -- the parent's justification height is less than its height
    (hj : σ.h_j < σ.h) : σ.h_j ≤ (state_transition C σ B).h_j := by
  rcases state_transition_justification C σ B with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
  exact le_of_lt hj

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

/-- **Kit fact, Lemma 51 with votes already counted.** When `quorum V ≤ |Q|` and every member of
`Q` is in the parent's progress set or has an attestation in `B` at the height `σ.h` naming
`σ.T_h`, the chain state of `B` has height `σ.h + 1`, or keeps `σ.h` with `Q` in its progress set
and `B`'s slot less than `δt` after `σ.T_h`'s; and when every member is in the parent's target
participation or has a target vote in `B` at that height naming `σ.T_h`, the chain state of `B`
has height `σ.h + 1`, justified block `σ.T_h` and justification height `σ.h`.

The variables:
- `C`: the parameters; `σ`: the parent's chain state; `B`: the block; `Q`: the quorum.

Read aloud: a quorum counted in the parent or voting in the block is a certificate. -/
theorem quorum_certificate_with_counted (C : Config) (σ : ChainState V) (B : Block V)
    (Q : Finset V)
    (hQ : quorum V ≤ Q.card)
    (hAtts : ∀ v ∈ Q, v ∈ σ.progress ∨
      ∃ a ∈ B.attestations, a.val_index = v ∧ a.h = σ.h ∧ a.T = σ.T_h.root) :
    ((state_transition C σ B).h = σ.h + 1 ∨
      ((state_transition C σ B).h = σ.h ∧ Q ⊆ (state_transition C σ B).progress ∧
        B.slot < σ.T_h.slot + C.δt)) ∧
    ((∀ v ∈ Q, v ∈ σ.target_participation ∨
        ∃ a ∈ B.attestations, a.val_index = v ∧ a.h = σ.h ∧ a.T = σ.T_h.root ∧
          a.τ = false) →
      (state_transition C σ B).h = σ.h + 1 ∧ (state_transition C σ B).J = σ.T_h ∧
        (state_transition C σ B).h_j = σ.h) := by
  obtain ⟨tp, pr, fp, F', h_F', htp, hpr, hmem, -, hc⟩ := state_transition_cases C σ B
  have hQpr : Q ⊆ pr := by
    intro v hv
    rcases hAtts v hv with h | ⟨a, ha, rfl, hh, hT⟩
    · exact hpr h
    · exact (hmem a ha hh hT).1
  have hQcard : quorum V ≤ pr.card := le_trans hQ (Finset.card_le_card hQpr)
  refine ⟨?_, fun hT => ?_⟩
  · rcases hc with ⟨-, hR⟩ | ⟨-, -, -, hR⟩ | ⟨-, hq', hR⟩ <;> rw [hR]
    · exact Or.inl rfl
    · exact Or.inl rfl
    · refine Or.inr ⟨rfl, hQpr, ?_⟩
      have hs : ¬ σ.T_h.slot + C.δt ≤ B.slot := fun hs => hq' ⟨hQcard, hs⟩
      unfold Slot at *
      omega
  · have hQtp : Q ⊆ tp := by
      intro v hv
      rcases hT v hv with h | ⟨a, ha, rfl, hh, hT', hτ⟩
      · exact htp h
      · exact (hmem a ha hh hT').2 hτ
    have hq : quorum V ≤ tp.card := le_trans hQ (Finset.card_le_card hQtp)
    rcases hc with ⟨-, hR⟩ | ⟨hq', -, -, -⟩ | ⟨hq', -, -⟩
    · rw [hR]
      exact ⟨rfl, rfl, rfl⟩
    · exact absurd hq hq'
    · exact absurd hq hq'

omit [DecidableEq V] [Fintype V] in
/-- A valid attestation is at the chain state's height naming its `T_h`, or at a lesser height.

The variables:
- `σ`: the chain state; `a`: the attestation. -/
theorem valid_attestation_cases (σ : ChainState V) (a : Attestation V)
    (h : valid_attestation σ a = true) : (a.h = σ.h ∧ a.T = σ.T_h.root) ∨ a.h < σ.h := by
  by_contra hn
  simp only [not_or, not_and, not_lt] at hn
  have : valid_attestation σ a = false := by
    simp only [valid_attestation, Id.run]
    split
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      exact absurd hc.2 (hn.1 hc.1)
    · split
      · show (_ && _ && decide (a.h < σ.h)) = false
        simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, not_lt]
        exact Or.inr hn.2
      · rfl
  rw [this] at h
  cases h

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [DecidableEq V] [Fintype V] [RootOrder] in
/-- `newest K l₁ ++ l₂`, when `l₂` has at most `K` elements, keeps all of `l₂`: it is a suffix of
`l₁` followed by `l₂`.

The variables:
- `K`: the bound; `l₁`, `l₂`: the two parts of the list. -/
theorem newest_append_of_length_le (K : Nat) (l₁ l₂ : List (PendingPair V))
    (h : l₂.length ≤ K) :
    newest K (l₁ ++ l₂) = l₁.drop (l₁.length + l₂.length - K) ++ l₂ := by
  unfold newest
  rw [List.length_append]
  exact List.drop_append_of_le_length (by omega)

omit [DecidableEq V] [Fintype V] [RootOrder] in
/-- An attestation whose finality pair names a pending justification of `σ`, at a height greater
than the pair's and less than `σ.h`, is valid against `σ` (the second case of
`valid_attestation`).

The variables:
- `σ`: the chain state; `a`: the attestation; `p`: its finality pair. -/
theorem valid_attestation_of_pending (σ : ChainState V) (a : Attestation V) (p : FinalityPair)
    (hp : a.finality_pair = some p) (hpend : is_pending σ p = true) (h1 : p.hf < a.h)
    (h2 : a.h < σ.h) : valid_attestation σ a = true := by
  have hne : a.finality_pair ≠ none := by rw [hp]; exact Option.some_ne_none p
  have hval : a.finality_pair.value hne = p := value_eq_of_eq_some hp hne
  simp only [valid_attestation, Id.run]
  split
  · rfl
  · show (is_pending σ (a.finality_pair.value hne) &&
      decide ((a.finality_pair.value hne).hf < a.h) && decide (a.h < σ.h)) = true
    rw [hval, hpend]
    simp only [Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨h1, h2⟩

end

/-! ## When a finality pair is pending (record migration, step 1c: a theorem the execution proof
`lem95_consecutive_openings_step` calls instead of opening `is_pending`) -/

section

open Goldilocks
variable {V : Type}

/-- `is_pending σ p` answers `true` exactly when some pending justification `e` of `σ` is at the
height `p.hf` and names a block whose root is `p.Tf`.

The variables:
- `σ`: the chain state; `p`: the finality pair.

Read aloud: a finality pair is pending in `σ` when it names the height and the block root of one
of `σ`'s pending justifications. -/
theorem is_pending_iff (σ : ChainState V) (p : FinalityPair) :
    is_pending σ p = true ↔ ∃ e ∈ σ.pending_finality, e.j = p.hf ∧ e.T.root = p.Tf := by
  simp only [is_pending, decide_eq_true_eq]

end

end GoldilocksCorrectness.Proofs.Routines
