module
public import GoldilocksCorrectness.Proofs.Routines.NoRaise
import all Goldilocks.AC.Confirmation

@[expose] public section

/-!
# What the lock revocation keeps of an AC state

`revoke_locks_keepsVotes`, `revoke_locks_from`, `revoke_locks_grows_from`: the revocation
`revoke_locks` keeps the pool and the stamps of its input AC state (`KeepsVotes`, `ACGrows`), and
`revoke_locks_ok`: it raises no error.

They read the routine alone: no node state, no execution.

Moved here unchanged from the execution pages.
-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Routines

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

section

variable [RootOrder]

/-- Every answer of the revocation of the locks keeps the pool and the stamps: it writes the lock
entries only.

The variables:
- `P`: the values; `A`: the AC state; `Φ`: the frame; `t`: the time; `s`: the slot. -/
theorem revoke_locks_keepsVotes (P : Provisional V) (A : ACState V) (Φ : Frame V) (t : Time)
    (s : Slot) : DREPost (revoke_locks P A Φ t s) (KeepsVotes A) := by
  simp only [revoke_locks]
  repeat' first
    | exact DREPost.pure ⟨rfl, rfl, rfl⟩
    | refine DREPost.dite (fun _ => ?_) (fun _ => ?_)
    | refine DREPost.ite (fun _ => ?_) (fun _ => ?_)
    | refine DREPost.bind_any (fun _ => ?_)

/-- The revocation of the locks keeps "`VotesInv` at `t'`, with the block stamps of `A₀`". -/
theorem revoke_locks_from {P : Provisional V} {A₀ : ACState V} {t' : Time} (A : ACState V)
    (Φ : Frame V) (t : Time) (s : Slot)
    (h : VotesInv P A t' ∧ A.timestamp_block = A₀.timestamp_block) :
    DREPost (revoke_locks P A Φ t s)
      (fun A' => VotesInv P A' t' ∧ A'.timestamp_block = A₀.timestamp_block) :=
  (revoke_locks_keepsVotes P A Φ t s).mono (fun _ hk => ⟨h.1.of_keeps hk, hk.2.2.trans h.2⟩)

end

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

section

variable [RootOrder]

/-- The revocation of the locks keeps "filed by slot, holding `A₀`'s votes and stamps, with
`A₀`'s block stamps, what it holds beyond `A₀` stamped `t₀`". -/
theorem revoke_locks_grows_from {P : Provisional V} {A₀ : ACState V} {t₀ : Time} (A : ACState V)
    (Φ : Frame V) (t : Time) (s : Slot)
    (h : SlotKeyed A ∧ ACGrows A₀ A ∧ A.timestamp_block = A₀.timestamp_block ∧
      ACStampsAt A₀ A t₀) :
    DREPost (revoke_locks P A Φ t s)
      (fun A' => SlotKeyed A' ∧ ACGrows A₀ A' ∧ A'.timestamp_block = A₀.timestamp_block ∧
        ACStampsAt A₀ A' t₀) :=
  (revoke_locks_keepsVotes P A Φ t s).mono
    (fun _ hk => ⟨h.1.of_keeps hk, h.2.1.trans (ACGrows.of_keeps hk), hk.2.2.trans h.2.2.1,
      h.2.2.2.trans (ACGrows.of_keeps hk) (ACStampsAt.of_keeps hk t₀)⟩)

end

end

section

open GoldilocksCorrectness.Statements.Routines (PoolStamped)

section

open Goldilocks
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn)
variable {V : Type} [DecidableEq V] [Fintype V]

section

variable [RootOrder]

/-- The revocation of the locks answers when no two blocks of the frame's tree share a root, every
vote of the pool is stamped and every block of the frame's tree is stamped.

The variables:
- `P`: the provisional parameters; `A`: the AC state; `Φ`: the frame; `t`: the time; `s`: the
  slot. -/
theorem revoke_locks_ok (P : Provisional V) (A : ACState V) {Φ : Frame V}
    (hRoots : RootsNameBlocksIn Φ.tree) (t : Time) (s : Slot) (hPool : PoolStamped A)
    -- every block of the frame's tree is stamped
    (hb : ∀ H ∈ Φ.tree, A.timestamp_block H ≠ none) : DREOk (revoke_locks P A Φ t s) := by
  simp only [revoke_locks]
  refine DREOk.ite (fun _ => DREOk.pure _) (fun _ => ?_)
  exact DREOk.bind_any (imageM_ok_of_total _ _ (fun e _ =>
    moved_entry_ok P A hRoots _ _ s e (pool_stamped hPool _) hb)) (fun _ => DREOk.pure _)

end

end

end

end GoldilocksCorrectness.Proofs.Routines
