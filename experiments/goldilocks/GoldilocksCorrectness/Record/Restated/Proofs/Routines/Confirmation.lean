module
public import GoldilocksCorrectness.Record.Facts
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.TickLocksGoldilocks
public import GoldilocksCorrectness.Proofs.Routines.Confirmation
public import GoldilocksCorrectness.Proofs.Routines.ConfirmationSupporters
public import GoldilocksCorrectness.Proofs.Routines.ConfirmedTip
public import GoldilocksCorrectness.Proofs.Routines.PeriodLocks
public import GoldilocksCorrectness.Proofs.Routines.Attestation
public import GoldilocksCorrectness.Proofs.Routines.Lemma36
public import GoldilocksCorrectness.Proofs.Routines.WalkEndLemmas

@[expose] public section

/-!
# The confirmation update, over a model

The theorems of `GoldilocksCorrectness/Proofs/Routines/Confirmation.lean`, `ConfirmedTip.lean`,
`PeriodLocks.lean`, `Attestation.lean`, `ConfirmationSupporters.lean` and `Lemma36.lean` about
what the confirmation update (`update_confirmation`) leaves, over a model `M`: each takes the
record's predicate `ConfirmationUpdated M C P n t s n'` where the landed theorem takes the spec's
answer, its other hypotheses read on `n`, its conclusion on `n'`. A landed conclusion about the
lock entries of the update's input reads, on `n`, the entries whose deadline is after `t`: the
tick runs the update after deleting the others. Two facts every theorem about the lock entries
reads are proved once: `confirmationUpdated_entries_keep` (the unexpired entries stay) and
`confirmationUpdated_entries_cases` (an entry of `n'` is an unexpired entry of `n` or the lock on
the deepest lockable block).

`update_confirmation_zero` restates the landed equation at slot `0` as what
`ConfirmationUpdated` says there; `advance_some` is about the reader `M.advance`.

The recovery section states the landed theorems again, as the landed statement (`type_of%`), at the
AC state `n.A` and the frame `fg_to_ac n.S` of a node state `n`, and proves each from its record
form at the spec's model through the bridge `confirmationUpdated_at_node`. Each recovery takes, as
a hypothesis the landed theorem does not have, that no two blocks of the tree of `fg_to_ac n.S`
share a root and that every lock entry of `n` has a deadline after `t` (the record's predicate
describes the update the tick runs, on the unexpired entries).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Record
open GoldilocksCorrectness.Record.Statements.Routines (ResolvesAt ConfirmationUpdated EarlyVotes
  LateVotes SupportVotes ConfirmationScore ConfirmationEligible Lockable deepest?_of_chain
  confirmationUpdated_at_node goldilocks_resolvesAt lockEntry_eq_mk)
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn WalkEnd)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans ancestorEq_compatible
  compatible_iff conflicts_iff compatible_of_ancestorEq_compatible walkEnd_mem_tree_or_eq
  ancestorEq_of_walkSteps)

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## What every theorem about the entries reads -/

/-- When some block is lockable under `H`, some lockable block `L` has every lockable block as an
ancestor or is that block: the lockable blocks are blocks of a tree and ancestors of `H`.

The variables:
- `M`: the model; `C`, `P`: the parameters; `n`: the node state; `s'`: the slot; `H`: the
  confirmation.

Read aloud: when a block is lockable, a deepest lockable block exists. -/
theorem exists_deepest_lockable [RootOrder] {M : GoldilocksModel V} {C : Config}
    {P : Provisional V} {n : M.N}
    {s' : Slot} {H : Block V} (hex : ∃ B : Block V, Lockable M C P n s' H B) :
    ∃ L : Block V, Lockable M C P n s' H L ∧
      ∀ B : Block V, Lockable M C P n s' H B → B.AncestorEq L := by
  classical
  let T := (M.fg_to_ac n).tree.filter fun B => Lockable M C P n s' H B
  have hT : ∀ B, B ∈ T ↔ Lockable M C P n s' H B := fun B => by
    simp only [T, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩
  obtain ⟨hsome, hnone⟩ := deepest?_of_chain (T := T) (X := H) fun B hB => ((hT B).1 hB).2.2.1
  obtain ⟨B₀, hB₀⟩ := hex
  cases hD : Block.deepest? T with
  | none =>
    have := (hT B₀).2 hB₀
    rw [hnone hD] at this
    exact absurd this (Finset.notMem_empty _)
  | some L =>
    obtain ⟨hL, hall⟩ := hsome L hD
    exact ⟨L, (hT L).1 hL, fun B hB => hall B ((hT B).2 hB)⟩

/-- Every lock entry of `n` with a deadline after `t` is an entry of `n'`.

The variables:
- `M`: the model; `C`, `P`: the parameters; `n`, `n'`: the node states before and after;
- `t`: the time; `s`: the slot.

Read aloud: the confirmation update deletes no unexpired lock. -/
theorem confirmationUpdated_entries_keep [RootOrder] {M : GoldilocksModel V} {C : Config}
    {P : Provisional V} {n n' : M.N} {t : Time} {s : Slot}
    (hCU : ConfirmationUpdated M C P n t s n') :
    ∀ e ∈ n.lockEntries, t < e.d → e ∈ n'.lockEntries := by
  intro e he hd
  rcases hCU with ⟨-, -, -, -, h⟩ | ⟨-, H, -, -, -, hNo, hYes⟩
  · exact (h e).2 ⟨he, hd⟩
  · by_cases hu : ConfirmationEligible M C n (s - 1) H = .ok true ∧ M.live_lock_vetoes n t H = false
    · obtain ⟨-, -, hnone, hsome⟩ := hYes hu.1 hu.2
      by_cases hex : ∃ B : Block V, Lockable M C P n (s - 1) H B
      · classical
        obtain ⟨L, hL, hall⟩ := exists_deepest_lockable hex
        exact (hsome L hL hall).2.1 e he hd
      · exact (hnone hex e).2 ⟨he, hd⟩
    · have hu' : ConfirmationEligible M C n (s - 1) H ≠ .ok true ∨
          M.live_lock_vetoes n t H = true := by
        by_cases h1 : ConfirmationEligible M C n (s - 1) H = .ok true
        · exact Or.inr (by simpa [h1] using hu)
        · exact Or.inl h1
      exact ((hNo hu').2.2 e).2 ⟨he, hd⟩

/-- What the update of slot `s ≥ 1` leaves when it saves `H` as the confirmation of slot `s − 1`:
the walk from the frame's finalized block ends at `H`, `H` passes the count test, and, with a live
lock entry vetoing `H`, nothing else changes but the expired entries; with none, the record
advances by `H`, the fast blocks and the lock entries are as `ConfirmationUpdated` says.

The variables:
- `M`: the model; `C`, `P`: the parameters; `n`, `n'`: the node states before and after;
- `t`: the time; `s`: the slot; `H`: the saved confirmation.

Read aloud: a saved confirmation is where the walk ends, it passes the test, and the veto decides
the rest. -/
theorem confirmationUpdated_saved_some [RootOrder] {M : GoldilocksModel V} {C : Config}
    {P : Provisional V} {n n' : M.N} {t : Time} {s : Slot} {H : Block V} (hs : 1 ≤ s)
    (hCU : ConfirmationUpdated M C P n t s n') (hS : n'.savedConfirmation (s - 1) = some H) :
    @WalkEnd V M.tieBreak (M.fg_to_ac n).tree (ConfirmationScore M C n (s - 1))
      (ConfirmationEligible M C n (s - 1)) (M.fg_to_ac n).F H ∧
    ConfirmationEligible M C n (s - 1) H = .ok true ∧
    (M.live_lock_vetoes n t H = true →
      n'.fastBlocks = ∅ ∧ n'.latestConfirmed = n.latestConfirmed ∧
      ∀ e' : M.LE, e' ∈ n'.lockEntries ↔ e' ∈ n.lockEntries ∧ t < e'.d) ∧
    (M.live_lock_vetoes n t H = false →
      n'.latestConfirmed = M.advance (M.fg_to_ac n) n.latestConfirmed (some H) ∧
      (∀ B : Block V, B ∈ n'.fastBlocks ↔ B ∈ (M.fg_to_ac n).tree ∧ B ≠ Block.genesis ∧
        B.AncestorEq H ∧
        fast_test P (M.fg_to_ac n) (SupportVotes M C n (s - 1)) (s - 1) B = .ok true) ∧
      ((¬ ∃ B : Block V, Lockable M C P n (s - 1) H B) →
        ∀ e' : M.LE, e' ∈ n'.lockEntries ↔ e' ∈ n.lockEntries ∧ t < e'.d) ∧
      (∀ L : Block V, Lockable M C P n (s - 1) H L →
        (∀ B : Block V, Lockable M C P n (s - 1) H B → B.AncestorEq L) →
        (∀ e' ∈ n'.lockEntries, (e' ∈ n.lockEntries ∧ t < e'.d) ∨
          (e'.B = L ∧ e'.d = C.t_ (s - 1 + C.k) + 5 * C.Δ)) ∧
        (∀ e ∈ n.lockEntries, t < e.d → e ∈ n'.lockEntries) ∧
        ∃ e' ∈ n'.lockEntries, e'.B = L ∧ e'.d = C.t_ (s - 1 + C.k) + 5 * C.Δ)) := by
  obtain ⟨-, H₀, hW, hS₀, -, hNo, hYes⟩ :=
    hCU.resolve_left fun h0 => Nat.one_le_iff_ne_zero.1 hs h0.1
  by_cases he : ConfirmationEligible M C n (s - 1) H₀ = .ok true
  · rw [if_pos he, hS] at hS₀
    obtain rfl := Option.some.inj hS₀
    exact ⟨hW, he, fun hv => hNo (Or.inr hv), fun hv => hYes he hv⟩
  · rw [if_neg he, hS] at hS₀
    exact absurd hS₀ (by simp)

/-- When the update of slot `s ≥ 1` saves no confirmation, the fast blocks of `n'` are empty, its
record of the confirmed tip is `n`'s and its lock entries are `n`'s unexpired ones.

The variables:
- `M`: the model; `C`, `P`: the parameters; `n`, `n'`: the node states before and after;
- `t`: the time; `s`: the slot.

Read aloud: without a confirmation, the update only empties the fast blocks and deletes the
expired locks. -/
theorem confirmationUpdated_saved_none [RootOrder] {M : GoldilocksModel V} {C : Config}
    {P : Provisional V} {n n' : M.N} {t : Time} {s : Slot} (hs : 1 ≤ s)
    (hCU : ConfirmationUpdated M C P n t s n') (hS : n'.savedConfirmation (s - 1) = none) :
    n'.fastBlocks = ∅ ∧ n'.latestConfirmed = n.latestConfirmed ∧
      ∀ e' : M.LE, e' ∈ n'.lockEntries ↔ e' ∈ n.lockEntries ∧ t < e'.d := by
  obtain ⟨-, H₀, -, hS₀, -, hNo, -⟩ :=
    hCU.resolve_left fun h0 => Nat.one_le_iff_ne_zero.1 hs h0.1
  by_cases he : ConfirmationEligible M C n (s - 1) H₀ = .ok true
  · rw [if_pos he, hS] at hS₀
    exact absurd hS₀ (by simp)
  · exact hNo (Or.inl he)

/-- A fast block of `n'` after the update of slot `s ≥ 1` is a non-genesis block of the tree of
`M.fg_to_ac n` on the chain of the saved confirmation `H`, which no live lock entry vetoes, and it
passes the fast test.

The variables:
- `M`: the model; `C`, `P`: the parameters; `n`, `n'`: the node states before and after;
- `t`: the time; `s`: the slot; `B`: the fast block.

Read aloud: a fast block is on the saved confirmation's chain and passes the fast test. -/
theorem confirmationUpdated_fast_cases [RootOrder] {M : GoldilocksModel V} {C : Config}
    {P : Provisional V} {n n' : M.N} {t : Time} {s : Slot} {B : Block V} (hs : 1 ≤ s)
    (hCU : ConfirmationUpdated M C P n t s n') (hB : B ∈ n'.fastBlocks) :
    ∃ H : Block V, n'.savedConfirmation (s - 1) = some H ∧ M.live_lock_vetoes n t H = false ∧
      B ∈ (M.fg_to_ac n).tree ∧ B ≠ Block.genesis ∧ B.AncestorEq H ∧
      fast_test P (M.fg_to_ac n) (SupportVotes M C n (s - 1)) (s - 1) B = .ok true := by
  cases hS : n'.savedConfirmation (s - 1) with
  | none =>
    rw [(confirmationUpdated_saved_none hs hCU hS).1] at hB
    exact absurd hB (Finset.notMem_empty _)
  | some H =>
    obtain ⟨-, -, hv1, hv0⟩ := confirmationUpdated_saved_some hs hCU hS
    cases hv : M.live_lock_vetoes n t H with
    | false => exact ⟨H, rfl, hv, ((hv0 hv).2.1 B).1 hB⟩
    | true =>
      rw [(hv1 hv).1] at hB
      exact absurd hB (Finset.notMem_empty _)

/-- A lock entry of `n'` after the update of slot `s` is an entry of `n` whose deadline is after
`t`, or, at `s ≥ 1`, the lock of the update: its block is lockable under the saved confirmation
`H`, which no live lock entry vetoes, and its deadline is `C.t_ (s − 1 + C.k) + 5 · C.Δ`.

The variables:
- `M`: the model; `C`, `P`: the parameters; `n`, `n'`: the node states before and after;
- `t`: the time; `s`: the slot.

Read aloud: a lock after the update is an unexpired lock of `n` or the update's new lock. -/
theorem confirmationUpdated_entries_cases [RootOrder] {M : GoldilocksModel V} {C : Config}
    {P : Provisional V} {n n' : M.N} {t : Time} {s : Slot}
    (hCU : ConfirmationUpdated M C P n t s n') :
    ∀ e' ∈ n'.lockEntries, (e' ∈ n.lockEntries ∧ t < e'.d) ∨
      (1 ≤ s ∧ ∃ H : Block V, n'.savedConfirmation (s - 1) = some H ∧
        M.live_lock_vetoes n t H = false ∧ Lockable M C P n (s - 1) H e'.B ∧
        e'.d = C.t_ (s - 1 + C.k) + 5 * C.Δ) := by
  intro e' he'
  by_cases hs0 : s = 0
  · rcases hCU with ⟨-, -, -, -, h⟩ | ⟨h, -⟩
    · exact Or.inl ((h e').1 he')
    · exact absurd hs0 (Nat.one_le_iff_ne_zero.1 h)
  have hs : 1 ≤ s := Nat.one_le_iff_ne_zero.2 hs0
  cases hS : n'.savedConfirmation (s - 1) with
  | none => exact Or.inl (((confirmationUpdated_saved_none hs hCU hS).2.2 e').1 he')
  | some H =>
    obtain ⟨-, -, hv1, hv0⟩ := confirmationUpdated_saved_some hs hCU hS
    cases hv : M.live_lock_vetoes n t H with
    | true => exact Or.inl (((hv1 hv).2.2 e').1 he')
    | false =>
      obtain ⟨-, -, hnone, hsome⟩ := hv0 hv
      by_cases hex : ∃ B : Block V, Lockable M C P n (s - 1) H B
      · obtain ⟨L, hL, hall⟩ := exists_deepest_lockable hex
        rcases (hsome L hL hall).1 e' he' with h | ⟨hB, hd⟩
        · exact Or.inl h
        · exact Or.inr ⟨hs, H, rfl, hv, hB ▸ hL, hd⟩
      · exact Or.inl (((hnone hex) e').1 he')

/-! ## The saved confirmation, the fast blocks and the lock on a fast confirmation -/

/-- A fast block after the update of slot `s ≥ 1` is the saved confirmation of slot `s − 1` or an
ancestor of it (the record form of `update_confirmation_fast_block_saved`).

The variables:
- `M`: the model; `C`, `P`: the parameters; `n`, `n'`: the node states before and after;
- `t`: the time; `s`: the slot; `B`: the fast block.

Read aloud: every fast block leads to the saved confirmation. -/
theorem update_confirmation_fast_block_saved [RootOrder] {M : GoldilocksModel V} {C : Config}
    {P : Provisional V} {n n' : M.N} {t : Time} {s : Slot} {B : Block V}
    -- the slot is not the first
    (hs : 1 ≤ s)
    -- the confirmation update of slot `s` leaves `n'`
    (hUpdate : ConfirmationUpdated M C P n t s n')
    -- `B` is a fast block of `n'`
    (hB : B ∈ n'.fastBlocks) :
    ∃ C' : Block V, n'.savedConfirmation (s - 1) = some C' ∧ B.AncestorEq C' := by
  obtain ⟨H, hS, -, -, -, hBH, -⟩ := confirmationUpdated_fast_cases hs hUpdate hB
  exact ⟨H, hS, hBH⟩

/-- When the update of slot `s ≠ 0` saves `B` and `B` is a fast block, `n'` holds a lock entry on
`B` with the deadline `C.t_ (s − 1 + C.k) + 5 · C.Δ`, and `B` is in the tree of `M.fg_to_ac n`
(the record form of `lock_entry_of_saved_fast`).

The variables:
- `M`: the model; `C`, `P`: the parameters; `n`, `n'`: the node states before and after;
- `t`: the time; `s`: the slot; `B`: the saved confirmation.

Read aloud: an update that saves a fast confirmation locks it. -/
theorem lock_entry_of_saved_fast [RootOrder] {M : GoldilocksModel V} {C : Config}
    {P : Provisional V} {n n' : M.N} {t : Time} {s : Slot} {B : Block V} (hs : s ≠ 0)
    (hUpdate : ConfirmationUpdated M C P n t s n')
    (hSaved : n'.savedConfirmation (s - 1) = some B)
    (hFast : B ∈ n'.fastBlocks) :
    (∃ e ∈ n'.lockEntries, e.B = B ∧ e.d = C.t_ (s - 1 + C.k) + 5 * C.Δ) ∧
      B ∈ (M.fg_to_ac n).tree := by
  have hs1 : 1 ≤ s := Nat.one_le_iff_ne_zero.2 hs
  obtain ⟨H, hS, hv, hT, hg, -, hf⟩ := confirmationUpdated_fast_cases hs1 hUpdate hFast
  rw [hSaved] at hS
  obtain rfl := Option.some.inj hS
  obtain ⟨-, -, -, hv0⟩ := confirmationUpdated_saved_some hs1 hUpdate hSaved
  obtain ⟨-, -, -, hsome⟩ := hv0 hv
  have hL : Lockable M C P n (s - 1) B B := ⟨hT, hg, ancestorEq_refl B, Or.inl hf⟩
  exact ⟨(hsome B hL fun _ h => h.2.2.1).2.2, hT⟩

/-- The update of slot `0` keeps the saved confirmations, the fast blocks and the record of the
confirmed tip, and keeps exactly the lock entries whose deadline is after `t` (the record form of
`update_confirmation_zero`).

The variables:
- `M`: the model; `C`, `P`: the parameters; `n`, `n'`: the node states before and after;
- `t`: the time.

Read aloud: at slot `0` the update only deletes the expired locks. -/
theorem update_confirmation_zero [RootOrder] {M : GoldilocksModel V} {C : Config}
    {P : Provisional V} {n n' : M.N} {t : Time}
    (hUpdate : ConfirmationUpdated M C P n t 0 n') :
    M.savedConfirmation n' = M.savedConfirmation n ∧ n'.fastBlocks = n.fastBlocks ∧
      n'.latestConfirmed = n.latestConfirmed ∧
      ∀ e' : M.LE, e' ∈ n'.lockEntries ↔ e' ∈ n.lockEntries ∧ t < e'.d := by
  rcases hUpdate with ⟨-, h⟩ | ⟨h, -⟩
  · exact h
  · exact absurd h (by decide)

/-- The update of slot `s` keeps the saved confirmation of every slot other than `s − 1` (the
record form of `update_confirmation_saved_ne`).

The variables:
- `M`: the model; `C`, `P`: the parameters; `n`, `n'`: the node states before and after;
- `t`: the time; `s`: the slot.

Read aloud: the update writes only the saved confirmation of the previous slot. -/
theorem update_confirmation_saved_ne [RootOrder] {M : GoldilocksModel V} {C : Config}
    {P : Provisional V} {n n' : M.N} {t : Time} {s : Slot}
    (hUpdate : ConfirmationUpdated M C P n t s n') :
    ∀ j : Slot, j ≠ s - 1 → n'.savedConfirmation j = n.savedConfirmation j := by
  rcases hUpdate with ⟨-, h, -⟩ | ⟨-, H, -, -, h, -⟩
  · exact fun j _ => congrFun h j
  · exact h

/-- When the update of slot `s ≠ 0` saves `C'`, every fast block is `C'` or an ancestor of `C'`
(the record form of `fast_blocks_ancestorEq_saved`).

The variables:
- `M`: the model; `C`, `P`: the parameters; `n`, `n'`: the node states before and after;
- `t`: the time; `s`: the slot; `C'`: the saved confirmation.

Read aloud: every fast block leads to the saved confirmation. -/
theorem fast_blocks_ancestorEq_saved [RootOrder] {M : GoldilocksModel V} {C : Config}
    {P : Provisional V} {n n' : M.N} {t : Time} {s : Slot} {C' : Block V} (hs : s ≠ 0)
    (hUpdate : ConfirmationUpdated M C P n t s n')
    (hSaved : n'.savedConfirmation (s - 1) = some C') :
    ∀ L ∈ n'.fastBlocks, L.AncestorEq C' := by
  intro L hL
  obtain ⟨H, hS, -, -, -, hLH, -⟩ :=
    confirmationUpdated_fast_cases (Nat.one_le_iff_ne_zero.2 hs) hUpdate hL
  rw [hSaved] at hS
  obtain rfl := Option.some.inj hS
  exact hLH

/-- A confirmation the update of slot `s ≥ 1` saves is the frame's finalized block or a block of
the frame's tree (the record form of `update_confirmation_saved_mem`).

The variables:
- `M`: the model; `C`, `P`: the parameters; `n`, `n'`: the node states before and after;
- `t`: the time; `s`: the slot; `C'`: the saved confirmation.

Read aloud: the saved confirmation is the finalized block or in the tree. -/
theorem update_confirmation_saved_mem [RootOrder] {M : GoldilocksModel V} {C : Config}
    {P : Provisional V} {n n' : M.N} {t : Time} {s : Slot}
    -- the update is of a slot after slot `0`
    (hs : 1 ≤ s)
    -- the update leaves `n'`
    (hUpdate : ConfirmationUpdated M C P n t s n') (C' : Block V)
    -- `n'` saves `C'` as the confirmation of slot `s − 1`
    (hC' : n'.savedConfirmation (s - 1) = some C') :
    C' = (M.fg_to_ac n).F ∨ C' ∈ (M.fg_to_ac n).tree := by
  letI : GoldilocksCorrectness.Statements.Routines.TieBreak V := M.tieBreak
  exact walkEnd_mem_tree_or_eq (confirmationUpdated_saved_some hs hUpdate hC').1

/-- When the update of slot `s ≥ 1` saves `C'`, `C'` is the frame's finalized block or a
descendant of it (the record form of `saved_confirmation_F_ancestorEq`).

The variables:
- `M`: the model; `C`, `P`: the parameters; `n`, `n'`: the node states before and after;
- `t`: the time; `s`: the slot.

Read aloud: the saved confirmation descends from the finalized block. -/
theorem saved_confirmation_F_ancestorEq [RootOrder] {M : GoldilocksModel V} {C : Config}
    {P : Provisional V} {n n' : M.N} {t : Time} {s : Slot}
    -- the slot is not the first
    (hs : 1 ≤ s)
    -- the confirmation update of slot `s` leaves `n'`
    (hUpdate : ConfirmationUpdated M C P n t s n') :
    ∀ C' : Block V, n'.savedConfirmation (s - 1) = some C' → (M.fg_to_ac n).F.AncestorEq C' := by
  intro C' hC'
  letI : GoldilocksCorrectness.Statements.Routines.TieBreak V := M.tieBreak
  exact ancestorEq_of_walkSteps (confirmationUpdated_saved_some hs hUpdate hC').1.1

/-! ## The record of the confirmed tip -/

/-- The reader `M.advance Φ old (some C')` answers `old` when `old` is in `Φ.tree` and `C'` is
`old` or an ancestor of it, and `C'` otherwise (the record form of `advance_some`).

The variables:
- `M`: the model; `F`: its facts; `Φ`: the frame; `old`: the record; `C'`: the confirmation.

Read aloud: the record stays when the confirmation is behind it in the tree, and moves to the
confirmation otherwise. -/
theorem advance_some {M : GoldilocksModel V} (F : Facts M) (Φ : Frame V) (old C' : Block V) :
    (old ∈ Φ.tree ∧ C'.AncestorEq old ∧ M.advance Φ old (some C') = old) ∨
      (¬ (old ∈ Φ.tree ∧ C'.AncestorEq old) ∧ M.advance Φ old (some C') = C') := by
  rw [F.rd.advance_eq]
  by_cases h : old ∈ Φ.tree ∧ C'.ancestorEq old = true
  · exact Or.inl ⟨h.1, h.2, if_pos h⟩
  · exact Or.inr ⟨h, if_neg h⟩

/-- The three cases of the record of the confirmed tip after the update of slot `s ≠ 0`: nothing is
saved and the record stays; a confirmation is saved, a live lock entry vetoes it and the record
stays; or no live lock entry vetoes it and the record advances by it (the record form of
`update_confirmation_latest_cases`).

The variables:
- `M`: the model; `C`, `P`: the parameters; `n`, `n'`: the node states before and after;
- `t`: the time; `s`: the slot.

Read aloud: the record moves only by a saved confirmation no live lock vetoes. -/
theorem update_confirmation_latest_cases [RootOrder] {M : GoldilocksModel V} {C : Config}
    {P : Provisional V} {n n' : M.N} {t : Time} {s : Slot}
    -- the update is of a slot after slot `0`
    (hs : s ≠ 0)
    -- the update leaves `n'`
    (hUpdate : ConfirmationUpdated M C P n t s n') :
    (n'.savedConfirmation (s - 1) = none ∧ n'.latestConfirmed = n.latestConfirmed) ∨
      ∃ C' : Block V, n'.savedConfirmation (s - 1) = some C' ∧
        ((M.live_lock_vetoes n t C' = true ∧ n'.latestConfirmed = n.latestConfirmed) ∨
          (M.live_lock_vetoes n t C' = false ∧
            n'.latestConfirmed = M.advance (M.fg_to_ac n) n.latestConfirmed (some C'))) := by
  have hs1 : 1 ≤ s := Nat.one_le_iff_ne_zero.2 hs
  cases hS : n'.savedConfirmation (s - 1) with
  | none => exact Or.inl ⟨rfl, (confirmationUpdated_saved_none hs1 hUpdate hS).2.1⟩
  | some C' =>
    obtain ⟨-, -, hv1, hv0⟩ := confirmationUpdated_saved_some hs1 hUpdate hS
    refine Or.inr ⟨C', rfl, ?_⟩
    cases hv : M.live_lock_vetoes n t C' with
    | true => exact Or.inl ⟨rfl, (hv1 hv).2.1⟩
    | false => exact Or.inr ⟨rfl, (hv0 hv).1⟩

/-- After the update of slot `s ≠ 0`, the record of the confirmed tip is `n`'s, or it is the saved
confirmation of slot `s − 1` and no live lock entry vetoes it (the record form of
`update_confirmation_latest_confirmed`).

The variables:
- `M`: the model; `F`: its facts; `C`, `P`: the parameters; `n`, `n'`: the node states before and
  after; `t`: the time; `s`: the slot.

Read aloud: a moved record is the unvetoed saved confirmation. -/
theorem update_confirmation_latest_confirmed [RootOrder] {M : GoldilocksModel V} (F : Facts M)
    {C : Config} {P : Provisional V} {n n' : M.N} {t : Time} {s : Slot}
    -- the update is of a slot after slot `0`
    (hs : s ≠ 0)
    -- the update leaves `n'`
    (hUpdate : ConfirmationUpdated M C P n t s n') :
    n'.latestConfirmed = n.latestConfirmed ∨
      (n'.savedConfirmation (s - 1) = some n'.latestConfirmed ∧
        M.live_lock_vetoes n t n'.latestConfirmed = false) := by
  rcases update_confirmation_latest_cases hs hUpdate with ⟨-, h⟩ | ⟨C', hS, ⟨-, h⟩ | ⟨hv, h⟩⟩
  · exact Or.inl h
  · exact Or.inl h
  · rcases advance_some F (M.fg_to_ac n) n.latestConfirmed C' with ⟨-, -, ha⟩ | ⟨-, ha⟩
    · exact Or.inl (h.trans ha)
    · rw [h, ha]
      exact Or.inr ⟨hS, hv⟩

/-! ## The fast blocks, the frame and a live lock -/

/-- A fast block after the update of slot `s ≥ 1` passes the fast test over the support votes made
of the early votes (the slot-`(s − 1)` votes of `n` resolving strictly before
`C.t_ (s − 1) + 2 · C.Δ`) whose validator has no second vote among the late votes (those stamped
strictly before `C.t_ (s − 1) + 6 · C.Δ`) (the record form of
`update_confirmation_fast_blocks_pass`).

The variables:
- `M`: the model; `C`, `P`: the parameters; `n`, `n'`: the node states before and after;
- `t`: the time; `s`: the slot; `B`: the fast block.

Read aloud: every fast block passes the fast test over the update's support votes. -/
theorem update_confirmation_fast_blocks_pass [RootOrder] {M : GoldilocksModel V} {C : Config}
    {P : Provisional V} {n n' : M.N} {t : Time} {s : Slot} {B : Block V}
    -- the slot is not the first
    (hs : 1 ≤ s)
    -- the confirmation update of slot `s` leaves `n'`
    (hUpdate : ConfirmationUpdated M C P n t s n')
    -- `B` is a fast block of `n'`
    (hB : B ∈ n'.fastBlocks) :
    ∃ early late : Finset (GoldfishVote V),
      (∀ vote : GoldfishVote V, vote ∈ early ↔ vote ∈ M.votesHeldSet n (s - 1) ∧
        ∃ x : Stamp, ResolvesAt M n vote x ∧ x < ((C.t_ (s - 1) + 2 * C.Δ : Time) : Stamp)) ∧
      (∀ vote : GoldfishVote V, vote ∈ late ↔ vote ∈ M.votesHeldSet n (s - 1) ∧
        ∃ τ : Stamp, n.voteStamp vote = some τ ∧
          τ < ((C.t_ (s - 1) + 6 * C.Δ : Time) : Stamp)) ∧
      fast_test P (M.fg_to_ac n) {vote ∈ early | M.no_second_vote_in late vote = true} (s - 1)
        B = .ok true := by
  classical
  obtain ⟨H, -, -, -, -, -, hf⟩ := confirmationUpdated_fast_cases hs hUpdate hB
  refine ⟨EarlyVotes M C n (s - 1), LateVotes M C n (s - 1), fun vote => ?_, fun vote => ?_, hf⟩
  · simp only [EarlyVotes, Finset.mem_filter]
  · simp only [LateVotes, Finset.mem_filter]

/-- What the update of slot `s` leaves, against the frame: the record of the confirmed tip is `n`'s
or a descendant of the frame's finalized block, a fast block is `n`'s or in the frame's tree, a
lock entry is `n`'s or on a non-genesis block of the frame's tree, and every unexpired lock entry
of `n` stays (the record form of `update_confirmation_in_frame`).

The variables:
- `M`: the model; `F`: its facts; `C`, `P`: the parameters; `n`, `n'`: the node states before and
  after; `t`: the time; `s'`: the slot.

Read aloud: whatever the update writes is in the frame. -/
theorem update_confirmation_in_frame [RootOrder] {M : GoldilocksModel V} (F : Facts M)
    {C : Config} {P : Provisional V} {n n' : M.N} {t : Time} {s' : Slot}
    (hUpdate : ConfirmationUpdated M C P n t s' n') :
    (n'.latestConfirmed = n.latestConfirmed ∨ (M.fg_to_ac n).F.AncestorEq n'.latestConfirmed) ∧
    (∀ D ∈ n'.fastBlocks, D ∈ n.fastBlocks ∨ D ∈ (M.fg_to_ac n).tree) ∧
    (∀ e ∈ n'.lockEntries, e ∈ n.lockEntries ∨
      (e.B ∈ (M.fg_to_ac n).tree ∧ e.B ≠ Block.genesis)) ∧
    (∀ e ∈ n.lockEntries, t < e.d → e ∈ n'.lockEntries) := by
  refine ⟨?_, ?_, fun e he => ?_, confirmationUpdated_entries_keep hUpdate⟩
  · by_cases hs0 : s' = 0
    · rcases hUpdate with ⟨-, -, -, h, -⟩ | ⟨h, -⟩
      · exact Or.inl h
      · exact absurd hs0 (Nat.one_le_iff_ne_zero.1 h)
    rcases update_confirmation_latest_cases hs0 hUpdate with ⟨-, h⟩ | ⟨C', hS, ⟨-, h⟩ | ⟨-, h⟩⟩
    · exact Or.inl h
    · exact Or.inl h
    · rcases advance_some F (M.fg_to_ac n) n.latestConfirmed C' with ⟨-, -, ha⟩ | ⟨-, ha⟩
      · exact Or.inl (h.trans ha)
      · rw [h, ha]
        exact Or.inr (saved_confirmation_F_ancestorEq (Nat.one_le_iff_ne_zero.2 hs0) hUpdate C' hS)
  · intro D hD
    by_cases hs0 : s' = 0
    · rcases hUpdate with ⟨-, -, h, -⟩ | ⟨h, -⟩
      · exact Or.inl (h ▸ hD)
      · exact absurd hs0 (Nat.one_le_iff_ne_zero.1 h)
    obtain ⟨-, -, -, hT, -⟩ :=
      confirmationUpdated_fast_cases (Nat.one_le_iff_ne_zero.2 hs0) hUpdate hD
    exact Or.inr hT
  · rcases confirmationUpdated_entries_cases hUpdate e he with h | ⟨-, H, -, -, hL, -⟩
    · exact Or.inl h.1
    · exact Or.inr ⟨hL.1, hL.2.1⟩

/-- Under a live lock entry `e` of `n` whose block is the record of the confirmed tip or an
ancestor of it, with the record in the frame's tree, the update of slot `s' ≠ 0` keeps `e.B` an
ancestor of the record or the record, writes fast blocks and new lock entries compatible with
`e.B`, and saves a confirmation compatible with `e.B` or vetoed by a live lock entry (the record
form of `update_confirmation_with_live_lock_of_mem`; the landed entry `LockEntry.mk B d` is `e`).

The variables:
- `M`: the model; `F`: its facts; `C`, `P`: the parameters; `n`, `n'`: the node states before and
  after; `t`: the time; `s'`: the slot; `e`: the live lock entry.

Read aloud: the update cannot leave a live lock's chain. -/
theorem update_confirmation_with_live_lock_of_mem [RootOrder] {M : GoldilocksModel V}
    (F : Facts M) {C : Config} {P : Provisional V} {n n' : M.N} {t : Time} {s' : Slot}
    (e : M.LE) (hs' : s' ≠ 0) (hUpdate : ConfirmationUpdated M C P n t s' n')
    (hlock : e ∈ n.lockEntries) (hlive : M.is_live n t e = true)
    (hin : n.latestConfirmed ∈ (M.fg_to_ac n).tree) (hold : e.B.AncestorEq n.latestConfirmed) :
    e.B.AncestorEq n'.latestConfirmed ∧
    (∀ D ∈ n'.fastBlocks, D.compatible e.B = true) ∧
    (∀ e' ∈ n'.lockEntries, e' ∈ n.lockEntries ∨ e'.B.compatible e.B = true) ∧
    (∀ C' : Block V, n'.savedConfirmation (s' - 1) = some C' →
      C'.compatible e.B = true ∨ M.live_lock_vetoes n t C' = true) := by
  have hs1 : 1 ≤ s' := Nat.one_le_iff_ne_zero.2 hs'
  -- a confirmation no live lock vetoes is compatible with `e.B`
  have hcomp : ∀ H : Block V, M.live_lock_vetoes n t H = false → e.B.compatible H = true := by
    intro H hv
    rw [F.rd.live_lock_vetoes_eq, decide_eq_false_iff_not] at hv
    by_contra hc
    exact hv ⟨e, hlock, hlive, (conflicts_iff _ _).2 hc⟩
  -- a block on the chain of a confirmation compatible with `e.B` is compatible with `e.B`
  have hchain : ∀ H D : Block V, e.B.compatible H = true → D.AncestorEq H →
      D.compatible e.B = true := fun H D hc hD =>
    compatible_of_ancestorEq_compatible hD ((compatible_iff _ _).2 ((compatible_iff _ _).1 hc).symm)
  refine ⟨?_, fun D hD => ?_, fun e' he' => ?_, fun C' hC' => ?_⟩
  · rcases update_confirmation_latest_cases hs' hUpdate with ⟨-, h⟩ | ⟨C', -, ⟨-, h⟩ | ⟨hv, h⟩⟩
    · rw [h]; exact hold
    · rw [h]; exact hold
    · rcases advance_some F (M.fg_to_ac n) n.latestConfirmed C' with ⟨-, -, ha⟩ | ⟨hno, ha⟩
      · rw [h, ha]; exact hold
      · rw [h, ha]
        rcases (compatible_iff _ _).1 (hcomp C' hv) with h1 | h1
        · exact h1
        · exact absurd ⟨hin, ancestorEq_trans h1 hold⟩ hno
  · obtain ⟨H, -, hv, -, -, hDH, -⟩ := confirmationUpdated_fast_cases hs1 hUpdate hD
    exact hchain H D (hcomp H hv) hDH
  · rcases confirmationUpdated_entries_cases hUpdate e' he' with h | ⟨-, H, -, hv, hL, -⟩
    · exact Or.inl h.1
    · exact Or.inr (hchain H e'.B (hcomp H hv) hL.2.2.1)
  · cases hv : M.live_lock_vetoes n t C' with
    | true => exact Or.inr rfl
    | false =>
      exact Or.inl ((compatible_iff _ _).2 ((compatible_iff _ _).1 (hcomp C' hv)).symm)

/-! ## At the spec's model -/

/-- The landed `GoldilocksCorrectness.Proofs.Routines.update_confirmation_fast_block_saved`,
recovered from its record form at the spec's model, at the AC state `n.A` and the frame
`fg_to_ac n.S` of every node state `n` whose frame's tree has no two blocks sharing a root and
whose lock entries all have a deadline after `t`.

Read aloud: the landed theorem holds at every such node state. -/
theorem update_confirmation_fast_block_saved_recovered {V : Type} [DecidableEq V] [Fintype V] [RootOrder] :
    ∀ (C : Config) (P : Provisional V) (n : NodeState V) (A' : ACState V) (t : Time) (s : Slot) (B : Block V),
      (RootsNameBlocksIn (fg_to_ac n.S).tree ∧ ∀ e ∈ n.A.lock_entries, t < e.d) →
      type_of% (@GoldilocksCorrectness.Proofs.Routines.update_confirmation_fast_block_saved V _ _ _ C P n.A A' (fg_to_ac n.S) t s B) := by
  intro C P n A' t s B hH hs hUpdate hB
  exact update_confirmation_fast_block_saved hs (confirmationUpdated_at_node C P n t s A' hH hUpdate)
    hB

/-- The landed `GoldilocksCorrectness.Proofs.Routines.lock_entry_of_saved_fast`, recovered from its
record form at the spec's model, at the AC state `n.A` and the frame `fg_to_ac n.S` of every node
state `n` whose frame's tree has no two blocks sharing a root and whose lock entries all have a
deadline after `t`.

Read aloud: the landed theorem holds at every such node state. -/
theorem lock_entry_of_saved_fast_recovered {V : Type} [DecidableEq V] [Fintype V] [RootOrder] :
    ∀ (C : Config) (P : Provisional V) (n : NodeState V) (A' : ACState V) (t : Time) (s : Slot) (B : Block V),
      (RootsNameBlocksIn (fg_to_ac n.S).tree ∧ ∀ e ∈ n.A.lock_entries, t < e.d) →
      type_of% (@GoldilocksCorrectness.Proofs.Routines.lock_entry_of_saved_fast V _ _ _ C P n.A A' (fg_to_ac n.S) t s B) := by
  intro C P n A' t s B hH hs hUpdate hSaved hFast
  obtain ⟨⟨e, he, hB, hd⟩, hT⟩ := lock_entry_of_saved_fast hs
    (confirmationUpdated_at_node C P n t s A' hH hUpdate) hSaved hFast
  have hee : e = LockEntry.mk B (C.t_ (s - 1 + C.k) + 5 * C.Δ) := lockEntry_eq_mk hB hd
  exact ⟨hee ▸ he, hT⟩

/-- The landed `GoldilocksCorrectness.Proofs.Routines.update_confirmation_saved_ne`, recovered from
its record form at the spec's model, at the AC state `n.A` and the frame `fg_to_ac n.S` of every
node state `n` whose frame's tree has no two blocks sharing a root and whose lock entries all have
a deadline after `t`.

Read aloud: the landed theorem holds at every such node state. -/
theorem update_confirmation_saved_ne_recovered {V : Type} [DecidableEq V] [Fintype V] [RootOrder] :
    ∀ (C : Config) (P : Provisional V) (n : NodeState V) (t : Time) (s : Slot),
      (RootsNameBlocksIn (fg_to_ac n.S).tree ∧ ∀ e ∈ n.A.lock_entries, t < e.d) →
      type_of% (@GoldilocksCorrectness.Proofs.Routines.update_confirmation_saved_ne V _ _ _ C P n.A (fg_to_ac n.S) t s) := by
  intro C P n t s hH A' hUpdate
  exact update_confirmation_saved_ne (confirmationUpdated_at_node C P n t s A' hH hUpdate)

/-- The landed `GoldilocksCorrectness.Proofs.Routines.fast_blocks_ancestorEq_saved`, recovered from
its record form at the spec's model, at the AC state `n.A` and the frame `fg_to_ac n.S` of every
node state `n` whose frame's tree has no two blocks sharing a root and whose lock entries all have
a deadline after `t`.

Read aloud: the landed theorem holds at every such node state. -/
theorem fast_blocks_ancestorEq_saved_recovered {V : Type} [DecidableEq V] [Fintype V] [RootOrder] :
    ∀ (C : Config) (P : Provisional V) (n : NodeState V) (A' : ACState V) (t : Time) (s : Slot) (C' : Block V),
      (RootsNameBlocksIn (fg_to_ac n.S).tree ∧ ∀ e ∈ n.A.lock_entries, t < e.d) →
      type_of% (@GoldilocksCorrectness.Proofs.Routines.fast_blocks_ancestorEq_saved V _ _ _ C P n.A A' (fg_to_ac n.S) t s C') := by
  intro C P n A' t s C' hH hs hUpdate hSaved
  exact fast_blocks_ancestorEq_saved hs (confirmationUpdated_at_node C P n t s A' hH hUpdate) hSaved

/-- The landed `GoldilocksCorrectness.Proofs.Routines.update_confirmation_saved_mem`, recovered from
its record form at the spec's model, at the AC state `n.A` and the frame `fg_to_ac n.S` of every
node state `n` whose frame's tree has no two blocks sharing a root and whose lock entries all have
a deadline after `t`.

Read aloud: the landed theorem holds at every such node state. -/
theorem update_confirmation_saved_mem_recovered {V : Type} [DecidableEq V] [Fintype V] [RootOrder] :
    ∀ (C : Config) (P : Provisional V) (n : NodeState V) (A' : ACState V) (t : Time) (s : Slot),
      (RootsNameBlocksIn (fg_to_ac n.S).tree ∧ ∀ e ∈ n.A.lock_entries, t < e.d) →
      type_of% (@GoldilocksCorrectness.Proofs.Routines.update_confirmation_saved_mem V _ _ _ C P n.A A' (fg_to_ac n.S) t s) := by
  intro C P n A' t s hH hs hUpdate C' hC'
  exact update_confirmation_saved_mem hs (confirmationUpdated_at_node C P n t s A' hH hUpdate) C'
    hC'

/-- The landed `GoldilocksCorrectness.Proofs.Routines.advance_some`, recovered from its record form
at the spec's model.

Read aloud: the landed theorem is the record's at the spec's model. -/
theorem advance_some_recovered {V : Type} [DecidableEq V] [Fintype V] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.advance_some V _) := by
  exact fun Φ old C' => advance_some (M := Model.goldilocks (V := V)) goldilocksFacts Φ old C'

/-- The landed `GoldilocksCorrectness.Proofs.Routines.update_confirmation_latest_cases`, recovered
from its record form at the spec's model, at the AC state `n.A` and the frame `fg_to_ac n.S` of
every node state `n` whose frame's tree has no two blocks sharing a root and whose lock entries all
have a deadline after `t`.

Read aloud: the landed theorem holds at every such node state. -/
theorem update_confirmation_latest_cases_recovered {V : Type} [DecidableEq V] [Fintype V] [RootOrder] :
    ∀ (C : Config) (P : Provisional V) (n : NodeState V) (A' : ACState V) (t : Time) (s : Slot),
      (RootsNameBlocksIn (fg_to_ac n.S).tree ∧ ∀ e ∈ n.A.lock_entries, t < e.d) →
      type_of% (@GoldilocksCorrectness.Proofs.Routines.update_confirmation_latest_cases V _ _ _ C P n.A A' (fg_to_ac n.S) t s) := by
  intro C P n A' t s hH hs hUpdate
  exact update_confirmation_latest_cases hs (confirmationUpdated_at_node C P n t s A' hH hUpdate)

/-- The landed `GoldilocksCorrectness.Proofs.Routines.update_confirmation_latest_confirmed`,
recovered from its record form at the spec's model, at the AC state `n.A` and the frame
`fg_to_ac n.S` of every node state `n` whose frame's tree has no two blocks sharing a root and
whose lock entries all have a deadline after `t`.

Read aloud: the landed theorem holds at every such node state. -/
theorem update_confirmation_latest_confirmed_recovered {V : Type} [DecidableEq V] [Fintype V] [RootOrder] :
    ∀ (C : Config) (P : Provisional V) (n : NodeState V) (A' : ACState V) (t : Time) (s : Slot),
      (RootsNameBlocksIn (fg_to_ac n.S).tree ∧ ∀ e ∈ n.A.lock_entries, t < e.d) →
      type_of% (@GoldilocksCorrectness.Proofs.Routines.update_confirmation_latest_confirmed V _ _ _ C P n.A A' (fg_to_ac n.S) t s) := by
  intro C P n A' t s hH hs hUpdate
  exact update_confirmation_latest_confirmed goldilocksFacts hs
    (confirmationUpdated_at_node C P n t s A' hH hUpdate)

/-- The landed `GoldilocksCorrectness.Proofs.Routines.update_confirmation_fast_blocks_pass`,
recovered from its record form at the spec's model, at the AC state `n.A` and the frame
`fg_to_ac n.S` of every node state `n` whose frame's tree has no two blocks sharing a root and
whose lock entries all have a deadline after `t`.

Read aloud: the landed theorem holds at every such node state. -/
theorem update_confirmation_fast_blocks_pass_recovered {V : Type} [DecidableEq V] [Fintype V] [RootOrder] :
    ∀ (C : Config) (P : Provisional V) (n : NodeState V) (A' : ACState V) (t : Time) (s : Slot) (B : Block V),
      (RootsNameBlocksIn (fg_to_ac n.S).tree ∧ ∀ e ∈ n.A.lock_entries, t < e.d) →
      type_of% (@GoldilocksCorrectness.Proofs.Routines.update_confirmation_fast_blocks_pass V _ _ _ C P n.A A' (fg_to_ac n.S) t s B) := by
  intro C P n A' t s B hH hs hUpdate hB
  obtain ⟨early, late, he, hl, hf⟩ := update_confirmation_fast_blocks_pass hs
    (confirmationUpdated_at_node C P n t s A' hH hUpdate) hB
  refine ⟨early, late, fun vote => ?_, hl, hf⟩
  rw [he vote]
  refine and_congr Iff.rfl (exists_congr fun x => and_congr ?_ Iff.rfl)
  exact (goldilocks_resolvesAt n vote x hH.1).symm

/-- The landed `GoldilocksCorrectness.Proofs.Routines.update_confirmation_in_frame`, recovered from
its record form at the spec's model, at the AC state `n.A` and the frame `fg_to_ac n.S` of every
node state `n` whose frame's tree has no two blocks sharing a root and whose lock entries all have
a deadline after `t`.

Read aloud: the landed theorem holds at every such node state. -/
theorem update_confirmation_in_frame_recovered {V : Type} [DecidableEq V] [Fintype V] [RootOrder] :
    ∀ (C : Config) (P : Provisional V) (n : NodeState V) (A' : ACState V) (t : Time) (s' : Slot),
      (RootsNameBlocksIn (fg_to_ac n.S).tree ∧ ∀ e ∈ n.A.lock_entries, t < e.d) →
      type_of% (@GoldilocksCorrectness.Proofs.Routines.update_confirmation_in_frame V _ _ _ C P n.A A' (fg_to_ac n.S) t s') := by
  intro C P n A' t s' hH hUpdate
  obtain ⟨h1, h2, h3, h4⟩ := update_confirmation_in_frame goldilocksFacts
    (confirmationUpdated_at_node C P n t s' A' hH hUpdate)
  exact ⟨h1, h2, h3, fun e he => h4 e he (hH.2 e he)⟩

/-- The landed `GoldilocksCorrectness.Proofs.Routines.update_confirmation_with_live_lock_of_mem`,
recovered from its record form at the spec's model, at the AC state `n.A` and the frame
`fg_to_ac n.S` of every node state `n` whose frame's tree has no two blocks sharing a root and
whose lock entries all have a deadline after `t`.

Read aloud: the landed theorem holds at every such node state. -/
theorem update_confirmation_with_live_lock_of_mem_recovered {V : Type} [DecidableEq V] [Fintype V] [RootOrder] :
    ∀ (C : Config) (P : Provisional V) (n : NodeState V) (A' : ACState V) (t : Time) (s' : Slot) (B : Block V) (d : Time),
      (RootsNameBlocksIn (fg_to_ac n.S).tree ∧ ∀ e ∈ n.A.lock_entries, t < e.d) →
      type_of% (@GoldilocksCorrectness.Proofs.Routines.update_confirmation_with_live_lock_of_mem V _ _ _ C P n.A A' (fg_to_ac n.S) t s' B d) := by
  intro C P n A' t s' B d hH hs' hUpdate hlock hlive hin hold
  exact update_confirmation_with_live_lock_of_mem goldilocksFacts (LockEntry.mk B d) hs'
    (confirmationUpdated_at_node C P n t s' A' hH hUpdate) hlock hlive hin hold

end GoldilocksCorrectness.Record.Proofs.Routines
