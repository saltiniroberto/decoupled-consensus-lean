module
public import GoldilocksCorrectness.Proofs.Routines.Score
public import GoldilocksCorrectness.Proofs.Routines.DREPost
import all Goldilocks.AC.Confirmation
import all Goldilocks.AC.State

@[expose] public section

/-!
# What the revocation of the locks answers

The facts about the routines of the revocation (`opposes`, `opponents`, `moved_entry`) that the
proof of Lemma 5 reads: what `opposes` answers when the roots of the frame's tree name its blocks,
which validators the answer of `opponents` holds, and what an answered `moved_entry` says of the
entry it returns; and that every entry an answered revocation leaves is on a block of the frame's
tree. Each fact is read off the routine's answer, so none needs the routine to answer.
-/

set_option autoImplicit false

open scoped DC

open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Statements.Routines

/-! ## Binds -/

/-- A bind that answers ran its first step to an answer, and the continuation answered on it.

The variables:
- `x`: the first step; `f`: the continuation; `b`: the answer of the bind. -/
theorem dre_bind_eq_ok {α β : Type} {x : DRE α} {f : α → DRE β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a : α, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

variable {V : Type} [DecidableEq V]

/-! ## Conflicts -/

/-- Conflict is symmetric.

The variables:
- `X`, `Y`: the two blocks. -/
theorem conflicts_comm (X Y : Block V) : X.conflicts Y = Y.conflicts X := by
  simp only [Block.conflicts, Block.compatible, Bool.or_comm]

/-! ## `opposes` -/

/-- When no two blocks of `Φ.tree` share a root, `opposes Φ B' vote` answers whether some block of
`Φ.tree` has the vote's head as its root and conflicts with `B'`.

The variables:
- `Φ`: the frame; `B'`: the block opposed; `vote`: the vote. -/
theorem opposes_eq_ok {Φ : Frame V} (hRoots : RootsNameBlocksIn Φ.tree) (B' : Block V)
    (vote : GoldfishVote V) :
    opposes Φ B' vote =
      .ok (decide (∃ H ∈ Φ.tree, H.root = vote.head ∧ H.conflicts B' = true)) := by
  simp only [opposes, blockWithRoot_eq_ok hRoots, dre_bind_ok]
  generalize hX : Block.find? Φ.tree vote.head = X
  cases X with
  | none =>
    have hno : ¬ ∃ H ∈ Φ.tree, H.root = vote.head ∧ H.conflicts B' = true := by
      rintro ⟨H, hH, hr, -⟩
      rw [find?_eq_some hRoots hH hr] at hX
      cases hX
    simp only [ne_eq, not_true_eq_false, dite_false, decide_eq_false hno]
    rfl
  | some H =>
    obtain ⟨hH, hr⟩ := mem_of_pickUnique?_eq_some hX
    simp only [decide_eq_true_eq] at hr
    have hiff : (∃ H' ∈ Φ.tree, H'.root = vote.head ∧ H'.conflicts B' = true) ↔
        H.conflicts B' = true := by
      constructor
      · rintro ⟨H', hH', hr', hH'B⟩
        rwa [hRoots H' hH' H hH (hr'.trans hr.symm)] at hH'B
      · exact fun hHB => ⟨H, hH, hr, hHB⟩
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, dite_true, Option.value, Option.get_some]
    show Except.ok _ = Except.ok _
    congr 1
    rw [Bool.eq_iff_iff, decide_eq_true_iff]
    exact hiff.symm

/-! ## `opponents` -/

/-- Every validator not in `equivocators` with a vote in `votes` that resolves and opposes `B'`
is in the answer of `opponents A Φ votes equivocators B'`.

The variables:
- `A`: the AC state; `Φ`: the frame; `votes`: the votes counted;
- `equivocators`: the validators not counted; `B'`: the block opposed; `o`: the answer;
- `vote`: the validator's vote; `v`: the validator; `x`: the vote's resolution time. -/
theorem mem_opponents_of_eq_ok {A : ACState V} {Φ : Frame V} {votes : Finset (GoldfishVote V)}
    {equivocators : Finset V} {B' : Block V} {o : Finset V}
    (h : opponents A Φ votes equivocators B' = .ok o) {vote : GoldfishVote V} {v : V}
    -- the vote is one of `votes`, by `v`
    (hvote : vote ∈ votes) (hval : vote.val_index = v)
    -- `v` is not counted out
    (hne : v ∉ equivocators)
    -- the vote resolves at `x`
    {x : Stamp} (hτ : A.tau Φ vote = .ok (some x))
    -- the vote opposes `B'`
    (hopp : opposes Φ B' vote = .ok true) :
    v ∈ o := by
  simp only [opponents] at h
  obtain ⟨opposing, hfilter, hret⟩ := dre_bind_eq_ok h
  cases hret
  have hmem : vote ∈ opposing := by
    rw [mem_of_filterM_eq_ok_iff _ _ _ hfilter]
    refine ⟨hvote, ?_⟩
    simp only [hτ, hopp, dre_bind_ok, hval, hne]
    rfl
  simp only [Finset.map', Finset.mem_image]
  exact ⟨vote, hmem, hval⟩

/-! ## `moved_entry` -/

/-- An entry that `moved_entry` answers is on a block of `Φ.tree` that is `e.B` or an ancestor of
`e.B`, and whose opponents, counted twice, are fewer than the committee of slot `s − 1`.

The variables:
- `P`: the provisional parameters, with the committees; `A`: the AC state; `Φ`: the frame;
- `votes`: the votes counted; `equivocators`: the validators not counted; `s`: the slot;
- `e`: the entry moved; `e'`: the entry answered. -/
theorem moved_entry_eq_ok_some {P : Provisional V} {A : ACState V} {Φ : Frame V}
    {votes : Finset (GoldfishVote V)} {equivocators : Finset V} {s : Slot}
    [RootOrder] {e e' : LockEntry V}
    (h : moved_entry P A Φ votes equivocators s e = .ok (some e')) :
    e'.B ∈ Φ.tree ∧ e'.B.AncestorEq e.B ∧
      ∃ o : Finset V, opponents A Φ votes equivocators e'.B = .ok o ∧
        2 * o.card < (P.committee (s - 1)).card := by
  simp only [moved_entry] at h
  obtain ⟨candidates, hfilter, hret⟩ := dre_bind_eq_ok h
  generalize hD : Block.deepest? candidates = D at hret
  cases D with
  | none => cases hret
  | some B' =>
    have hB' : e'.B = B' := by
      simp only [ne_eq, reduceCtorEq, not_false_eq_true, dite_true, Option.value,
        Option.get_some] at hret
      cases hret
      rfl
    have hmem := deepest?_mem hD
    rw [mem_of_filterM_eq_ok_iff _ _ _ hfilter] at hmem
    obtain ⟨hT, hp⟩ := hmem
    obtain ⟨o, ho, hret'⟩ := dre_bind_eq_ok hp
    simp only [pure, Except.pure, Except.ok.injEq, Bool.and_eq_true, decide_eq_true_eq] at hret'
    obtain ⟨⟨-, hanc⟩, hcard⟩ := hret'
    rw [hB']
    exact ⟨hT, hanc, o, ho, hcard⟩

/-- After the revocation of the locks of slot `s`, every lock entry left is on a block of
`Φ.tree`.

Why: every entry left is an entry moved back, and `moved_entry` answers an entry on a block of
`Φ.tree`.

The variables:
- `P`: the provisional parameters; `A`: the AC state before the revocation; `A'`: the AC state
  after it; `Φ`: the frame; `t`: the time of the revocation; `s`: the slot of the revocation. -/
theorem revoke_locks_entry_mem_tree [Fintype V] [RootOrder] {P : Provisional V}
    {A A' : ACState V} {Φ : Frame V} {t : Time} {s : Slot}
    -- the slot is not the first
    (hs : 1 ≤ s)
    -- the revocation of slot `s` answers `A'`
    (hRevoke : revoke_locks P A Φ t s = .ok A') :
    ∀ e ∈ A'.lock_entries, e.B ∈ Φ.tree := by
  simp only [revoke_locks] at hRevoke
  rw [if_neg (Nat.one_le_iff_ne_zero.mp hs)] at hRevoke
  obtain ⟨moved, hmoved, hret⟩ := dre_bind_eq_ok hRevoke
  cases hret
  intro e he
  rw [present_mem_iff] at he
  obtain ⟨e₀, -, he₀⟩ := mem_of_imageM_eq_ok _ _ _ hmoved _ he
  exact (moved_entry_eq_ok_some he₀).1

end GoldilocksCorrectness.Proofs.Routines

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- Every answer of the revocation keeps the record of the confirmed tip: it writes the lock
entries only.

The variables:
- `P`: the values; `A`: the AC state; `Φ`: the frame; `t`: the time; `s`: the slot. -/
theorem revoke_locks_latest (P : Provisional V) (A : ACState V) (Φ : Frame V)
    (t : Time) (s : Slot) :
    DREPost (revoke_locks P A Φ t s) (fun A' => A'.latest_confirmed = A.latest_confirmed) := by
  simp only [revoke_locks]
  repeat' first
    | exact DREPost.pure rfl
    | refine DREPost.dite (fun _ => ?_) (fun _ => ?_)
    | refine DREPost.ite (fun _ => ?_) (fun _ => ?_)
    | refine DREPost.bind_any (fun _ => ?_)

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

/-- At slot `0` the revocation answers its input.

The variables:
- `P`: the values; `A`: the AC state; `Φ`: the frame; `t`: the time. -/
theorem revoke_locks_zero [RootOrder] (P : Provisional V) (A : ACState V) (Φ : Frame V)
    (t : Time) : revoke_locks P A Φ t 0 = .ok A := by
  simp only [revoke_locks]
  rfl

/-- Every answer of the revocation keeps the saved confirmations: it writes the lock entries
only.

The variables:
- `P`: the values; `A`: the AC state; `Φ`: the frame; `t`: the time; `s`: the slot. -/
theorem revoke_locks_saved [RootOrder] (P : Provisional V) (A : ACState V) (Φ : Frame V)
    (t : Time) (s : Slot) :
    DREPost (revoke_locks P A Φ t s) (fun A' => A'.saved_confirmation = A.saved_confirmation) := by
  simp only [revoke_locks]
  repeat' first
    | exact DREPost.pure rfl
    | refine DREPost.dite (fun _ => ?_) (fun _ => ?_)
    | refine DREPost.ite (fun _ => ?_) (fun _ => ?_)
    | refine DREPost.bind_any (fun _ => ?_)

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- Every answer of the revocation keeps the fast blocks: it writes the lock entries only.

The variables:
- `P`: the values; `A`: the AC state; `Φ`: the frame; `t`: the time; `s`: the slot. -/
theorem revoke_locks_fast_blocks (P : Provisional V) (A : ACState V) (Φ : Frame V)
    (t : Time) (s : Slot) :
    DREPost (revoke_locks P A Φ t s) (fun A' => A'.fast_blocks = A.fast_blocks) := by
  simp only [revoke_locks]
  repeat' first
    | exact DREPost.pure rfl
    | refine DREPost.dite (fun _ => ?_) (fun _ => ?_)
    | refine DREPost.ite (fun _ => ?_) (fun _ => ?_)
    | refine DREPost.bind_any (fun _ => ?_)

end

end GoldilocksCorrectness.Proofs.Routines
