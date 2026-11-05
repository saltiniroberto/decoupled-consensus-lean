module
public import GoldilocksCorrectness.Proofs.Routines.ConfirmationSupporters
public import GoldilocksCorrectness.Proofs.Routines.ForkChoiceFacts
public import GoldilocksCorrectness.Proofs.Routines.RevokeLocks
public import GoldilocksCorrectness.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Proofs.Routines.TickFrame
import all Goldilocks.AC.Confirmation
import all Goldilocks.AC.Interface
import all Goldilocks.Config
import all GoldilocksCorrectness.Statements.Routines.ScheduleDefs

@[expose] public section

/-!
# The AC interface handlers raise no error

`ac_on_tick_ok`, `ac_proposal_ok`, `ac_to_fg_ok`: the handlers `ac_on_tick`, `ac_proposal` and
`ac_to_fg` of the AC interface raise no error on the inputs each names.

They read the handlers alone: no node state, no execution.

Moved here unchanged from the execution pages.
-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Routines

section

open GoldilocksCorrectness.Statements.Routines (PoolStamped)

section

open Goldilocks
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn)
variable {V : Type} [DecidableEq V] [Fintype V]

section

variable [RootOrder]

/-- The tick of the available chain answers when no two blocks of the frame's tree share a root,
the pool is well filed and stamped no later than `t` (`VotesInv`), and every block of the frame's
tree is stamped.

Why: `VotesInv` is what the revocation and the Goldfish vote duty keep (`revoke_locks_from`,
`goldfish_vote_from`), so the stamped pool reaches the confirmation update.

The variables:
- `C`: the configuration; `P`: the provisional parameters; `A`: the AC state; `Φ`: the frame;
  `t`: the time; `v`: the validator; `b`, `b'`: the two duty flags of the tick. -/
theorem ac_on_tick_ok (C : Config) (P : Provisional V) (A : ACState V) {Φ : Frame V}
    (hRoots : RootsNameBlocksIn Φ.tree) (t : Time) (v : V) (b b' : Bool)
    (hV : VotesInv P A t)
    -- every block of the frame's tree is stamped
    (hb : ∀ H ∈ Φ.tree, A.timestamp_block H ≠ none) :
    DREBOk (ac_on_tick C P A Φ t v b b') := by
  simp only [ac_on_tick]
  refine DREBOk.ite (fun _ => ?_) (fun _ => ?_)
  · -- the revocation, then the Goldfish vote duty
    refine DREBOk.bind (P := fun A' => VotesInv P A' t ∧ A'.timestamp_block = A.timestamp_block)
      (DREBOk.liftM (revoke_locks_ok P _ hRoots t _ hV.2.1 hb))
      (DREBPost.liftM (revoke_locks_from (A₀ := A) _ _ _ _ ⟨hV, rfl⟩)) (fun A₁ hA₁ => ?_)
    refine DREBOk.bind (P := fun A' => VotesInv P A' t ∧ A'.timestamp_block = A.timestamp_block)
      (goldfish_vote_ok C P A₁ hRoots t v hA₁.1.2.1 (fun H hH => by rw [hA₁.2]; exact hb H hH))
      (goldfish_vote_from (A₀ := A) C A₁ Φ t v le_rfl hA₁) (fun A₂ hA₂ => ?_)
    refine DREBOk.ite (fun _ => ?_) (fun _ => DREBOk.pure _)
    exact DREBOk.bind_any (DREBOk.liftM (update_confirmation_ok C P A₂ hRoots t _ hA₂.1.2.1
      (fun H hH => by rw [hA₂.2]; exact hb H hH))) (fun _ => DREBOk.pure _)
  · refine DREBOk.ite (fun _ => ?_) (fun _ => DREBOk.pure _)
    exact DREBOk.bind_any (DREBOk.liftM (update_confirmation_ok C P _ hRoots t _ hV.2.1 hb))
      (fun _ => DREBOk.pure _)

/-- The proposal of the available chain answers when no two blocks of the frame's tree share a
root, every vote of the pool is stamped and every block of the frame's tree is stamped.

The variables:
- `C`: the configuration; `A`: the AC state; `Φ`: the frame; `t`: the time. -/
theorem ac_proposal_ok (C : Config) (A : ACState V) {Φ : Frame V}
    (hRoots : RootsNameBlocksIn Φ.tree) (t : Time) (hPool : PoolStamped A)
    -- every block of the frame's tree is stamped
    (hb : ∀ H ∈ Φ.tree, A.timestamp_block H ≠ none) : DREOk (ac_proposal C A Φ t) := by
  simp only [ac_proposal]
  refine DREOk.bind_any (List.filterM_ok_of_total _ _ (fun vote hvote =>
    DREOk.bind_any (tau_ok A Φ vote hRoots (hPool _ vote hvote) hb) (fun _ => DREOk.pure _)))
    (fun _ => ?_)
  exact DREOk.bind_any (get_head_ok C A hRoots t _ _ _) (fun _ => DREOk.pure _)

/-- The source and the head the available chain hands the finality gadget answer when no two
blocks of the frame's tree share a root, every vote of the pool is stamped and every block of the
frame's tree is stamped.

The variables:
- `C`: the configuration; `A`: the AC state; `Φ`: the frame; `t`: the time. -/
theorem ac_to_fg_ok (C : Config) (A : ACState V) {Φ : Frame V}
    (hRoots : RootsNameBlocksIn Φ.tree) (t : Time) (hPool : PoolStamped A)
    -- every block of the frame's tree is stamped
    (hb : ∀ H ∈ Φ.tree, A.timestamp_block H ≠ none) : DREOk (ac_to_fg C A Φ t) := by
  simp only [ac_to_fg]
  refine DREOk.bind_any (List.filterM_ok_of_total _ _ (fun vote hvote =>
    DREOk.bind_any (tau_ok A Φ vote hRoots (hPool _ vote hvote) hb) (fun _ => DREOk.pure _)))
    (fun _ => ?_)
  exact DREOk.bind_any (get_head_ok C A hRoots t _ _ _) (fun _ => DREOk.pure _)

end

end

end

end GoldilocksCorrectness.Proofs.Routines

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

section

open Goldilocks
open GoldilocksCorrectness.Statements.Routines (expireLocks)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- What the tick of the available chain does to the record of the confirmed tip: it keeps it;
or, at the support cutoff of its slot with the confirmation test passing, it answers the answer
of the confirmation update of that slot on `expireLocks A t`.

The variables:
- `C`, `P`: the parameters and the values; `A`: the AC state; `Φ`: the frame; `t`: the time;
  `v`: the node's validator; `b`, `b'`: the vote test and the confirmation test. -/
theorem ac_on_tick_latest_cases (C : Config) (P : Provisional V) (A : ACState V) (Φ : Frame V)
    (t : Time) (v : V) (b b' : Bool) :
    DREBPost (ac_on_tick C P A Φ t v b b') (fun A₁ =>
      A₁.latest_confirmed = A.latest_confirmed ∨
      (t = C.t_ (C.slot t) + 2 * C.Δ ∧ b' = true ∧ ∃ A'' : ACState V,
        update_confirmation C P (expireLocks A t) Φ t (C.slot t) = .ok A'' ∧ A₁ = A'')) := by
  simp only [ac_on_tick]
  refine DREBPost.ite (fun hc => ?_) (fun hc => ?_)
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    refine DREBPost.bind
      (P := fun A' => revoke_locks P (expireLocks A t) Φ t (C.slot t) = .ok A')
      (DREBPost.liftM (fun _ h => h)) (fun A' hA' => ?_)
    refine DREBPost.bind (goldfish_vote_keepsConfirmation C P A' Φ t v) (fun A₂ h₂ => ?_)
    refine DREBPost.ite (fun hc' => ?_) (fun _ => DREBPost.pure ?_)
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc'
      exact absurd hc'.1 (voteTime_ne_cutoff hc.1)
    · have hs := revoke_locks_latest P (expireLocks A t) Φ t (C.slot t) A' hA'
      exact Or.inl (h₂.2.2.2.trans hs)
  · refine DREBPost.ite (fun hc' => ?_) (fun _ => DREBPost.pure ?_)
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc'
      refine DREBPost.bind
        (P := fun A'' => update_confirmation C P (expireLocks A t) Φ t (C.slot t) = .ok A'')
        (DREBPost.liftM (fun _ h => h)) (fun A'' hA'' => ?_)
      exact DREBPost.pure (Or.inr ⟨hc'.1, hc'.2, A'', hA'', rfl⟩)
    · exact Or.inl rfl

end

section

open Goldilocks
open GoldilocksCorrectness.Statements.Routines (expireLocks)
variable {V : Type} [DecidableEq V] [Fintype V]

section

variable [RootOrder]

/-- What the tick of the available chain does to the saved confirmations and the lock entries,
in three cases: it keeps the saved confirmations and keeps a subset of the lock entries; or, at
the vote time of its slot with the vote test passing, it keeps the saved confirmations and leaves
the lock entries of the revocation of that slot on `expireLocks A t`; or, at the support cutoff
of its slot with the confirmation test passing, it leaves the saved confirmations and the lock
entries of the confirmation update of that slot on `expireLocks A t`.

The variables:
- `C`, `P`: the parameters and the values; `A`: the AC state; `Φ`: the frame; `t`: the time;
  `v`: the node's validator; `b`, `b'`: the vote test and the confirmation test. -/
theorem ac_on_tick_cases (C : Config) (P : Provisional V) (A : ACState V) (Φ : Frame V)
    (t : Time) (v : V) (b b' : Bool) :
    DREBPost (ac_on_tick C P A Φ t v b b') (fun A₁ =>
      (A₁.saved_confirmation = A.saved_confirmation ∧ A₁.lock_entries ⊆ A.lock_entries) ∨
      (t = C.t_ (C.slot t) + C.Δ ∧ b = true ∧ ∃ A' : ACState V,
        revoke_locks P (expireLocks A t) Φ t (C.slot t) = .ok A' ∧
        A₁.saved_confirmation = A.saved_confirmation ∧ A₁.lock_entries = A'.lock_entries) ∨
      (t = C.t_ (C.slot t) + 2 * C.Δ ∧ b' = true ∧ ∃ A'' : ACState V,
        update_confirmation C P (expireLocks A t) Φ t (C.slot t) = .ok A'' ∧
        A₁.saved_confirmation = A''.saved_confirmation ∧
        A₁.lock_entries = A''.lock_entries)) := by
  simp only [ac_on_tick]
  refine DREBPost.ite (fun hc => ?_) (fun hc => ?_)
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    refine DREBPost.bind
      (P := fun A' => revoke_locks P (expireLocks A t) Φ t (C.slot t) = .ok A')
      (DREBPost.liftM (fun _ h => h)) (fun A' hA' => ?_)
    refine DREBPost.bind (goldfish_vote_keepsConfirmation C P A' Φ t v) (fun A₂ h₂ => ?_)
    refine DREBPost.ite (fun hc' => ?_) (fun _ => DREBPost.pure ?_)
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc'
      exact absurd hc'.1 (voteTime_ne_cutoff hc.1)
    · have hs := revoke_locks_saved P (expireLocks A t) Φ t (C.slot t) A' hA'
      exact Or.inr (Or.inl ⟨hc.1, hc.2, A', hA', h₂.2.1.trans hs, h₂.1⟩)
  · refine DREBPost.ite (fun hc' => ?_) (fun _ => DREBPost.pure ?_)
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc'
      refine DREBPost.bind
        (P := fun A'' => update_confirmation C P (expireLocks A t) Φ t (C.slot t) = .ok A'')
        (DREBPost.liftM (fun _ h => h)) (fun A'' hA'' => ?_)
      exact DREBPost.pure (Or.inr (Or.inr ⟨hc'.1, hc'.2, A'', hA'', rfl, rfl⟩))
    · exact Or.inl ⟨rfl, Finset.filter_subset _ _⟩

end

end

section

open Goldilocks
open GoldilocksCorrectness.Statements.Routines (expireLocks)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- What the tick of the available chain does to the lock entries, the record of the confirmed tip
and the fast blocks, in three cases: it leaves the lock entries of `expireLocks A t` and keeps the
other two fields; or, at the vote time of its slot with the vote test passing, it leaves the lock
entries of the revocation of that slot on `expireLocks A t` and keeps the other two fields; or, at
the support cutoff of its slot with the confirmation test passing, it leaves the three fields of
the confirmation update of that slot on `expireLocks A t`.

The variables:
- `C`, `P`: the parameters and the values; `A`: the AC state; `Φ`: the frame; `t`: the time;
  `v`: the node's validator; `b`, `b'`: the vote test and the confirmation test. -/
theorem ac_on_tick_period_cases (C : Config) (P : Provisional V) (A : ACState V) (Φ : Frame V)
    (t : Time) (v : V) (b b' : Bool) :
    DREBPost (ac_on_tick C P A Φ t v b b') (fun A₁ =>
      (A₁.lock_entries = (expireLocks A t).lock_entries ∧
        A₁.latest_confirmed = A.latest_confirmed ∧ A₁.fast_blocks = A.fast_blocks) ∨
      (t = C.t_ (C.slot t) + C.Δ ∧ ∃ A' : ACState V,
        revoke_locks P (expireLocks A t) Φ t (C.slot t) = .ok A' ∧
        A₁.lock_entries = A'.lock_entries ∧
        A₁.latest_confirmed = A.latest_confirmed ∧ A₁.fast_blocks = A.fast_blocks) ∨
      (t = C.t_ (C.slot t) + 2 * C.Δ ∧ ∃ A'' : ACState V,
        update_confirmation C P (expireLocks A t) Φ t (C.slot t) = .ok A'' ∧
        A₁.lock_entries = A''.lock_entries ∧
        A₁.latest_confirmed = A''.latest_confirmed ∧ A₁.fast_blocks = A''.fast_blocks)) := by
  simp only [ac_on_tick]
  refine DREBPost.ite (fun hc => ?_) (fun hc => ?_)
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    refine DREBPost.bind
      (P := fun A' => revoke_locks P (expireLocks A t) Φ t (C.slot t) = .ok A')
      (DREBPost.liftM (fun _ h => h)) (fun A' hA' => ?_)
    refine DREBPost.bind (goldfish_vote_keepsConfirmation C P A' Φ t v) (fun A₂ h₂ => ?_)
    refine DREBPost.ite (fun hc' => ?_) (fun _ => DREBPost.pure ?_)
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc'
      exact absurd hc'.1 (voteTime_ne_cutoff hc.1)
    · have hl := revoke_locks_latest P (expireLocks A t) Φ t (C.slot t) A' hA'
      have hf := revoke_locks_fast_blocks P (expireLocks A t) Φ t (C.slot t) A' hA'
      exact Or.inr (Or.inl ⟨hc.1, A', hA', h₂.1, h₂.2.2.2.trans hl, h₂.2.2.1.trans hf⟩)
  · refine DREBPost.ite (fun hc' => ?_) (fun _ => DREBPost.pure ?_)
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc'
      refine DREBPost.bind
        (P := fun A'' => update_confirmation C P (expireLocks A t) Φ t (C.slot t) = .ok A'')
        (DREBPost.liftM (fun _ h => h)) (fun A'' hA'' => ?_)
      exact DREBPost.pure (Or.inr (Or.inr ⟨hc'.1, A'', hA'', rfl, rfl, rfl⟩))
    · exact Or.inl ⟨rfl, rfl, rfl⟩

end

end GoldilocksCorrectness.Proofs.Routines
