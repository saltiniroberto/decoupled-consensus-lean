module
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.TickDefsGoldilocks
public import GoldilocksCorrectness.Proofs.Routines.PeriodLocks
public import GoldilocksCorrectness.Proofs.Routines.Confirmation
public import GoldilocksCorrectness.Proofs.Routines.WalkEndBridge
public import GoldilocksCorrectness.Proofs.Routines.Lemma35
public import GoldilocksCorrectness.Proofs.Routines.NoRaise
public import GoldilocksCorrectness.Proofs.Routines.Node
import all Goldilocks.AC.Confirmation
import all Goldilocks.AC.State

@[expose] public section

/-!
# The revocation and the confirmation update at the spec's model

At the spec's model `Model.goldilocks`, what the spec's revocation of the locks (`revoke_locks`)
and confirmation update (`update_confirmation`) answer satisfies the record's predicates
`LocksRevoked` and `ConfirmationUpdated`, when no two blocks of the tree of `fg_to_ac n.S` share a
root:

- `locksRevoked_of_revoke_locks_eq_ok`: the revocation of slot `s` at `t`, run on `n`'s AC state
  with its lock entries replaced by those of `n` whose deadline is after `t` (or by any set with
  the same members), answers an AC state whose lock entries a node state `n'` holds; then
  `LocksRevoked Model.goldilocks P n t s n'`;
- `confirmationUpdated_of_update_confirmation_eq_ok`: the same for the confirmation update, with
  the saved confirmations, the fast blocks, the lock entries and the record of the confirmed tip.

The proofs walk the spec's bodies. On the way: the deepest block of a set of ancestors of one
block (`deepest?_of_chain`), the opponents of a block (`opponentsOf_of_opponents_eq_ok`), the
block an entry moves back to (`moved_entry_spec`), the veto read on the AC state with the expired
entries removed (`live_lock_vetoes_expired`) and the slow test read after the update's first
writes (`slow_test_update_saved`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

open DC (DRE)

namespace GoldilocksCorrectness.Record.Statements.Routines

open Goldilocks
open GoldilocksCorrectness.Record
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn WalkEnd)
open GoldilocksCorrectness.Proofs.Routines (dre_bind_eq_ok dre_bind_ok mem_of_filterM_eq_ok_iff
  mem_of_imageM_eq_ok mem_imageM_of_eq_ok present_mem_iff deepest?_eq_some
  exists_deepest_member eq_of_ancestorEq_of_depth eq_of_ancestorEq_common ancestorEq_compatible
  ancestorEq_antisymm ancestorEq_refl opposes_eq_ok mem_opponents_of_eq_ok)

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The deepest block of a chain -/

/-- When every block of `T` is `X` or an ancestor of `X`, the deepest block of `T` is a member of
`T` of which every member of `T` is an ancestor or which is that member itself; and `T` has a
deepest block when it is nonempty.

The variables:
- `T`: the set; `X`: the block every member of `T` leads to.

Read aloud: on a chain, the deepest block is the one every other block leads to. -/
theorem deepest?_of_chain [RootOrder] {T : Finset (Block V)} {X : Block V}
    -- every member of `T` is `X` or an ancestor of `X`
    (hT : ∀ B ∈ T, B.AncestorEq X) :
    (∀ D : Block V, Block.deepest? T = some D → D ∈ T ∧ ∀ B ∈ T, B.AncestorEq D) ∧
      (Block.deepest? T = none → T = ∅) := by
  have key : T.Nonempty → ∃ D ∈ T, (∀ B ∈ T, B.AncestorEq D) ∧ Block.deepest? T = some D := by
    intro hne
    obtain ⟨D, hD, hmax⟩ := exists_deepest_member T hne
    have hle : ∀ B ∈ T, B.depth ≤ D.depth := by
      intro B hB
      have h := hmax B hB
      simp only [Block.deeper, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
      exact Nat.le_of_not_lt h.1
    have hall : ∀ B ∈ T, B.AncestorEq D := by
      intro B hB
      rcases ancestorEq_compatible (hT B hB) (hT D hD) with h | h
      · exact h
      · obtain rfl := eq_of_ancestorEq_of_depth h (hle B hB)
        exact ancestorEq_refl _
    exact ⟨D, hD, hall, deepest?_eq_some hD hle
      (fun B hB hd => eq_of_ancestorEq_common (hT B hB) (hT D hD) hd)⟩
  refine ⟨fun D' hD' => ?_, fun hnone => ?_⟩
  · have hne : T.Nonempty := ⟨D', GoldilocksCorrectness.Proofs.Routines.deepest?_mem hD'⟩
    obtain ⟨D, hD, hall, hdeep⟩ := key hne
    rw [hdeep] at hD'
    cases hD'
    exact ⟨hD, hall⟩
  · by_contra hne
    obtain ⟨D, -, -, hdeep⟩ := key (Finset.nonempty_iff_ne_empty.2 hne)
    rw [hdeep] at hnone
    cases hnone

/-! ## The revocation of the locks -/

open GoldilocksCorrectness.Proofs.Routines (KeepsVotes tau_of_keepsVotes pool_of_keepsVotes) in
/-- At the spec's model, the answer `o` of the spec's `opponents` on an AC state `A` with the votes
and stamps of `n.A`, over the frame `fg_to_ac n.S`, is the set `OpponentsOf` describes, when no
two blocks of the tree of `fg_to_ac n.S` share a root.

The variables:
- `n`: the node state; `A`: the AC state, with `n.A`'s votes and stamps;
- `votes`, `eqv`: the votes counted and the validators counted out; `B'`: the block; `o`: the
  answer;
- `hRoots`: no two blocks of the tree of `fg_to_ac n.S` share a root.

Read aloud: the spec's opponents of `B'` are the record's. -/
theorem opponentsOf_of_opponents_eq_ok (n : NodeState V) {A : ACState V}
    (hA : KeepsVotes n.A A) {votes : Finset (GoldfishVote V)} {eqv : Finset V} {B' : Block V}
    {o : Finset V} (hRoots : RootsNameBlocksIn (fg_to_ac n.S).tree)
    (h : opponents A (fg_to_ac n.S) votes eqv B' = .ok o) :
    OpponentsOf (Model.goldilocks (V := V)) n votes eqv B' o := by
  intro v
  constructor
  · intro hv
    have h0 := h
    simp only [opponents] at h0
    obtain ⟨opposing, hfilter, hret⟩ := dre_bind_eq_ok h0
    cases hret
    simp only [Finset.map', Finset.mem_image] at hv
    obtain ⟨vote, hvote, rfl⟩ := hv
    rw [mem_of_filterM_eq_ok_iff _ _ _ hfilter] at hvote
    obtain ⟨hvs, hp⟩ := hvote
    obtain ⟨τ, hτ, hp1⟩ := dre_bind_eq_ok hp
    obtain ⟨b, hb, hp2⟩ := dre_bind_eq_ok hp1
    simp only [pure, Except.pure, Except.ok.injEq, Bool.and_eq_true, decide_eq_true_eq] at hp2
    obtain ⟨⟨hne, hτne⟩, rfl⟩ := hp2
    rw [tau_of_keepsVotes hA] at hτ
    obtain ⟨y, rfl⟩ := Option.ne_none_iff_exists'.1 hτne
    rw [opposes_eq_ok hRoots] at hb
    simp only [Except.ok.injEq, decide_eq_true_eq] at hb
    exact ⟨hne, vote, hvs, rfl, ⟨y, (goldilocks_resolvesAt n vote y hRoots).1 hτ⟩, hb⟩
  · rintro ⟨hne, vote, hvote, hval, ⟨y, hy⟩, hopp⟩
    have hτ : A.tau (fg_to_ac n.S) vote = .ok (some y) := by
      rw [tau_of_keepsVotes hA]
      exact (goldilocks_resolvesAt n vote y hRoots).2 hy
    refine mem_opponents_of_eq_ok h hvote hval hne hτ ?_
    rw [opposes_eq_ok hRoots]
    simp only [Except.ok.injEq, decide_eq_true_eq]
    exact hopp

open GoldilocksCorrectness.Proofs.Routines (KeepsVotes tau_of_keepsVotes pool_of_keepsVotes) in
/-- At the spec's model, what the spec's `moved_entry` answers on an AC state `A` with the votes and
stamps of `n.A`, with the slot-`(s − 1)` votes of `A` and their equivocators: an entry with `e`'s
deadline on the block `e` moves back to (`MovesTo`), or none when `e` has no block to move back to
(`MoveCandidate`), when no two blocks of the tree of `fg_to_ac n.S` share a root.

The variables:
- `P`: the provisional parameters; `n`: the node state; `A`: the AC state, with `n.A`'s votes and
  stamps; `s`: the slot of the revocation; `e`: the entry; `b`: the answer;
- `hRoots`: no two blocks of the tree of `fg_to_ac n.S` share a root.

Read aloud: the spec moves an entry back to the record's block, or deletes it when there is
none. -/
theorem moved_entry_spec [RootOrder] (P : Provisional V) (n : NodeState V) {A : ACState V}
    (hA : KeepsVotes n.A A) (s : Slot) (e : LockEntry V) {b : Option (LockEntry V)}
    (hRoots : RootsNameBlocksIn (fg_to_ac n.S).tree)
    (h : moved_entry P A (fg_to_ac n.S) (A.pool (s - 1)) (equivocators (A.pool (s - 1))) s e =
      .ok b) :
    (∀ e' : LockEntry V, b = some e' →
      e'.d = e.d ∧ MovesTo (Model.goldilocks (V := V)) P n s e e'.B) ∧
    (b = none → ∀ B'' : Block V, ¬ MoveCandidate (Model.goldilocks (V := V)) P n s e B'') := by
  simp only [moved_entry] at h
  obtain ⟨candidates, hfilter, hret⟩ := dre_bind_eq_ok h
  have hpool : A.pool (s - 1) = n.A.pool (s - 1) := pool_of_keepsVotes hA _
  -- the candidates are the blocks `e` may move back to
  have hcand : ∀ B'' : Block V, B'' ∈ candidates ↔
      MoveCandidate (Model.goldilocks (V := V)) P n s e B'' := by
    intro B''
    rw [mem_of_filterM_eq_ok_iff _ _ _ hfilter]
    constructor
    · rintro ⟨hT, hp⟩
      obtain ⟨o, ho, hret'⟩ := dre_bind_eq_ok hp
      simp only [pure, Except.pure, Except.ok.injEq, Bool.and_eq_true,
        decide_eq_true_eq] at hret'
      obtain ⟨⟨hgen, hanc⟩, hcard⟩ := hret'
      rw [hpool] at ho
      exact ⟨hT, hgen, hanc, o, opponentsOf_of_opponents_eq_ok n hA hRoots ho, hcard⟩
    · rintro ⟨hT, hgen, hanc, o, ho, hcard⟩
      refine ⟨hT, ?_⟩
      -- the spec's opponents answer, and they are `o`
      obtain ⟨b', hb'⟩ :=
        GoldilocksCorrectness.Proofs.Routines.filterM_ok_total _ _ _ hfilter B'' hT
      rw [hb']
      obtain ⟨o', ho', hret'⟩ := dre_bind_eq_ok hb'
      rw [hpool] at ho'
      have hoo : o' = o := Finset.ext fun v =>
        ((opponentsOf_of_opponents_eq_ok n hA hRoots ho') v).trans (ho v).symm
      subst hoo
      simp only [pure, Except.pure, Except.ok.injEq] at hret'
      rw [← hret']
      simp only [Except.ok.injEq, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨hgen, hanc⟩, hcard⟩
  -- the candidates are ancestors of `e.B`
  have hchain : ∀ B'' ∈ candidates, B''.AncestorEq e.B := fun B'' hB'' => ((hcand B'').1 hB'').2.2.1
  obtain ⟨hsome, hnone⟩ := deepest?_of_chain hchain
  generalize hD : Block.deepest? candidates = D at hret
  cases D with
  | none =>
    cases hret
    refine ⟨fun e' he' => (by cases he'), fun _ B'' hB'' => ?_⟩
    have hemp := hnone hD
    have := (hcand B'').2 hB''
    rw [hemp] at this
    exact absurd this (Finset.notMem_empty _)
  | some B' =>
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, dite_true, Option.value,
      Option.get_some] at hret
    cases hret
    refine ⟨fun e' he' => ?_, fun h => (by cases h)⟩
    cases he'
    obtain ⟨hmem, hall⟩ := hsome B' hD
    exact ⟨rfl, (hcand B').1 hmem, fun B'' hB'' => hall B'' ((hcand B'').2 hB'')⟩

/-- Two blocks an entry moves back to are the same block.

The variables:
- `M`: the model; `P`: the provisional parameters; `n`: the node state; `s`: the slot;
- `e`: the entry; `B₁`, `B₂`: the two blocks.

Read aloud: the block an entry moves back to is unique. -/
theorem movesTo_unique {M : GoldilocksModel V} {P : Provisional V} {n : M.N} {s : Slot}
    {e : M.LE} {B₁ B₂ : Block V} (h₁ : MovesTo M P n s e B₁) (h₂ : MovesTo M P n s e B₂) :
    B₁ = B₂ :=
  ancestorEq_antisymm (h₂.2 B₁ h₁.1) (h₁.2 B₂ h₂.1)

/-- **The bridge for the revocation of the locks.** At the spec's model, when the spec's
revocation of slot `s` at `t`, run on `n`'s AC state with its lock entries replaced by a set `E`
of entries of `n` holding every entry of `n` with a deadline after `t` (and, at `s = 0`, only
such entries), over the frame `fg_to_ac n.S`, answers `A'`, and the node state `n'` has `A'`'s lock
entries, then `LocksRevoked` holds of `n` and `n'`, when no two blocks of the tree of
`fg_to_ac n.S` share a root. (The revocation of a slot after slot `0` reads the live entries only,
so `E` may hold expired entries of `n` there.)

The variables:
- `P`: the provisional parameters; `n`: the node state; `t`: the time; `s`: the slot;
- `E`: the lock entries the revocation starts from; `A'`: its answer; `n'`: the node state after;
- `hRoots`: no two blocks of the tree of `fg_to_ac n.S` share a root;
- `hsub`: every member of `E` is an entry of `n`;
- `hlive`: every entry of `n` with a deadline after `t` is a member of `E`;
- `h0`: at `s = 0`, every member of `E` has a deadline after `t`.

Read aloud: the spec's revocation satisfies the record's predicate. -/
theorem locksRevoked_of_revoke_locks_eq_ok [RootOrder] (P : Provisional V) (n : NodeState V)
    (t : Time) (s : Slot) (E : Finset (LockEntry V)) (A' : ACState V) (n' : NodeState V)
    (hRoots : RootsNameBlocksIn (fg_to_ac n.S).tree)
    (hsub : ∀ e ∈ E, e ∈ n.A.lock_entries)
    (hlive : ∀ e ∈ n.A.lock_entries, t < e.d → e ∈ E)
    (h0 : s = 0 → ∀ e ∈ E, t < e.d)
    (h : revoke_locks P { n.A with lock_entries := E } (fg_to_ac n.S) t s = .ok A')
    (hn' : n'.A.lock_entries = A'.lock_entries) :
    LocksRevoked (Model.goldilocks (V := V)) P n t s n' := by
  by_cases hs : s = 0
  · have h0' := h0 hs
    subst hs
    rw [GoldilocksCorrectness.Proofs.Routines.revoke_locks_zero] at h
    cases h
    refine Or.inl ⟨rfl, fun e' => ?_⟩
    show e' ∈ n'.A.lock_entries ↔ e' ∈ n.A.lock_entries ∧ t < e'.d
    rw [hn']
    exact ⟨fun he => ⟨hsub e' he, h0' e' he⟩, fun he => hlive e' he.1 he.2⟩
  refine Or.inr ⟨Nat.one_le_iff_ne_zero.2 hs, ?_, ?_⟩
  all_goals
    have hA : GoldilocksCorrectness.Proofs.Routines.KeepsVotes n.A
        { n.A with lock_entries := E } := ⟨rfl, rfl, rfl⟩
    simp only [revoke_locks] at h
    rw [if_neg hs] at h
    obtain ⟨moved, hmoved, hret⟩ := dre_bind_eq_ok h
    cases hret
  · intro e' he'
    have he0 : e' ∈ n'.A.lock_entries := he'
    rw [hn'] at he0
    have he'' : some e' ∈ moved := (present_mem_iff _ _).1 he0
    obtain ⟨e, he, hmv⟩ := mem_of_imageM_eq_ok _ _ _ hmoved _ he''
    have he2 : e ∈ Finset.filter (fun e => is_live (fg_to_ac n.S) t e = true) E := he
    rw [Finset.mem_filter] at he2
    obtain ⟨hd, hmt⟩ := (moved_entry_spec P n hA s e hRoots hmv).1 e' rfl
    exact ⟨e, hsub e he2.1, he2.2, hd, hmt⟩
  · intro e he hl B' hB'
    have hlive' : is_live (fg_to_ac n.S) t e = true := hl
    have hd : t < e.d := by
      simp only [is_live, Bool.and_eq_true, decide_eq_true_eq] at hlive'
      exact hlive'.1
    have hel : e ∈ live_entries { n.A with lock_entries := E } (fg_to_ac n.S) t := by
      exact Finset.mem_filter.2 ⟨hlive e he hd, hlive'⟩
    obtain ⟨b, hb, hbm⟩ := mem_imageM_of_eq_ok _ _ _ hmoved e hel
    obtain ⟨hsome, hnone⟩ := moved_entry_spec P n hA s e hRoots hb
    cases b with
    | none => exact absurd hB'.1 (hnone rfl B')
    | some e' =>
      obtain ⟨hd', hmt⟩ := hsome e' rfl
      refine ⟨e', ?_, movesTo_unique hmt hB', hd'⟩
      show e' ∈ n'.A.lock_entries
      rw [hn']
      exact (present_mem_iff _ _).2 hbm

/-! ## The confirmation update -/

/-- The veto read on an AC state `A₀` whose lock entries are those of `n` with a deadline after
`t` is the veto read on `n.A`: a live entry has its deadline after `t`.

The variables:
- `n`: the node state; `A₀`: the AC state; `Φ`: the frame; `t`: the time; `C'`: the block.

Read aloud: removing the expired entries changes no veto. -/
theorem live_lock_vetoes_expired (n : NodeState V) (A₀ : ACState V) (Φ : Frame V) (t : Time)
    (C' : Block V) (hE : ∀ e : LockEntry V, e ∈ A₀.lock_entries ↔ e ∈ n.A.lock_entries ∧ t < e.d) :
    live_lock_vetoes A₀ Φ t C' = live_lock_vetoes n.A Φ t C' := by
  unfold live_lock_vetoes
  rw [decide_eq_decide]
  constructor
  · rintro ⟨e, he, hl, hc⟩
    exact ⟨e, ((hE e).1 he).1, hl, hc⟩
  · rintro ⟨e, he, hl, hc⟩
    have hd : t < e.d := by
      simp only [is_live, Bool.and_eq_true, decide_eq_true_eq] at hl
      exact hl.1
    exact ⟨e, (hE e).2 ⟨he, hd⟩, hl, hc⟩

/-- A live lock entry of an AC state `A₀`, whose lock entries are those of `n` with a deadline after
`t`, that vetoes `C'` is a live lock entry of `n.A` that vetoes `C'`.

The variables:
- `n`: the node state; `A₀`: the AC state; `Φ`: the frame; `t`: the time; `C'`: the block.

Read aloud: a veto on the state with the expired entries removed is a veto on `n`. -/
theorem live_lock_vetoes_true_of {n : NodeState V} (A₀ : ACState V) {Φ : Frame V} {t : Time}
    {C' : Block V} (hv : ¬ (!live_lock_vetoes A₀ Φ t C') = true)
    (hE : ∀ e : LockEntry V, e ∈ A₀.lock_entries ↔ e ∈ n.A.lock_entries ∧ t < e.d) :
    live_lock_vetoes n.A Φ t C' = true := by
  rw [← live_lock_vetoes_expired n A₀ Φ t C' hE]
  simpa using hv

/-- No live lock entry of an AC state `A₀`, whose lock entries are those of `n` with a deadline
after `t`, vetoes `C'` exactly when none of `n.A` does.

The variables:
- `n`: the node state; `A₀`: the AC state; `Φ`: the frame; `t`: the time; `C'`: the block.

Read aloud: no veto on the state with the expired entries removed is no veto on `n`. -/
theorem live_lock_vetoes_false_of {n : NodeState V} (A₀ : ACState V) {Φ : Frame V} {t : Time}
    {C' : Block V} (hv : (!live_lock_vetoes A₀ Φ t C') = true)
    (hE : ∀ e : LockEntry V, e ∈ A₀.lock_entries ↔ e ∈ n.A.lock_entries ∧ t < e.d) :
    live_lock_vetoes n.A Φ t C' = false := by
  rw [← live_lock_vetoes_expired n A₀ Φ t C' hE]
  simpa using hv

open GoldilocksCorrectness.Proofs.Routines (KeepsVotes tau_of_keepsVotes mem_early_iff
  mem_beforeCutoff_iff slow_test_congr walkEnd_of_ghost_eq_ok update_confirmation_zero
  filterM_ok_total) in
/-- **The bridge for the confirmation update.** At the spec's model, when the spec's confirmation
update of slot `s` at `t`, run on `n`'s AC state with its lock entries replaced by a set `E` whose
members are the entries of `n` with a deadline after `t`, over the frame `fg_to_ac n.S`, answers
`A'`, and the node state `n'` has `A'`'s saved confirmations, fast blocks, lock entries and record
of the confirmed tip, then `ConfirmationUpdated` holds of `n` and `n'`, when no two blocks of the
tree of `fg_to_ac n.S` share a root.

The variables:
- `C`: the configuration; `P`: the provisional parameters; `n`: the node state; `t`: the time;
  `s`: the slot; `E`: the lock entries the update starts from; `A'`: its answer; `n'`: the node
  state after;
- `hRoots`: no two blocks of the tree of `fg_to_ac n.S` share a root;
- `hE`: the members of `E` are the entries of `n` with a deadline after `t`.

Read aloud: the spec's confirmation update satisfies the record's predicate. -/
theorem confirmationUpdated_of_update_confirmation_eq_ok [RootOrder] (C : Config)
    (P : Provisional V) (n : NodeState V) (t : Time) (s : Slot) (E : Finset (LockEntry V))
    (A' : ACState V) (n' : NodeState V)
    (hRoots : RootsNameBlocksIn (fg_to_ac n.S).tree)
    (hE : ∀ e : LockEntry V, e ∈ E ↔ e ∈ n.A.lock_entries ∧ t < e.d)
    (h : update_confirmation C P { n.A with lock_entries := E } (fg_to_ac n.S) t s = .ok A')
    (hS : n'.A.saved_confirmation = A'.saved_confirmation)
    (hF : n'.A.fast_blocks = A'.fast_blocks)
    (hL : n'.A.lock_entries = A'.lock_entries)
    (hC : n'.A.latest_confirmed = A'.latest_confirmed) :
    ConfirmationUpdated (Model.goldilocks (V := V)) C P n t s n' := by
  by_cases hs : s = 0
  · subst hs
    rw [update_confirmation_zero] at h
    cases h
    refine Or.inl ⟨rfl, hS, hF, hC, fun e' => ?_⟩
    show e' ∈ n'.A.lock_entries ↔ e' ∈ n.A.lock_entries ∧ t < e'.d
    rw [hL]
    exact hE e'
  have hs1 : 1 ≤ s := Nat.one_le_iff_ne_zero.2 hs
  refine Or.inr ⟨hs1, ?_⟩
  have hA : KeepsVotes n.A { n.A with lock_entries := E } := ⟨rfl, rfl, rfl⟩
  simp only [update_confirmation] at h
  rw [if_neg hs] at h
  obtain ⟨early, hearly, h1⟩ := dre_bind_eq_ok h
  obtain ⟨late, hlate, h2⟩ := dre_bind_eq_ok h1
  obtain ⟨H, hH, h3⟩ := dre_bind_eq_ok h2
  obtain ⟨b, hb, h4⟩ := dre_bind_eq_ok h3
  -- the early and the late votes are the record's
  have hEarly : early = EarlyVotes (Model.goldilocks (V := V)) C n (s - 1) := by
    ext vote
    rw [mem_early_iff hearly]
    simp only [EarlyVotes, Finset.mem_filter]
    refine and_congr Iff.rfl (exists_congr fun y => and_congr ?_ Iff.rfl)
    rw [tau_of_keepsVotes hA]
    exact goldilocks_resolvesAt n vote y hRoots
  have hLate : late = LateVotes (Model.goldilocks (V := V)) C n (s - 1) := by
    ext vote
    rw [mem_beforeCutoff_iff hlate]
    simp only [LateVotes, Finset.mem_filter]
    exact Iff.rfl
  subst hEarly hLate
  have hH' : ghost (fg_to_ac n.S).F (fg_to_ac n.S).tree
      (ConfirmationScore (Model.goldilocks (V := V)) C n (s - 1))
      (ConfirmationEligible (Model.goldilocks (V := V)) C n (s - 1)) = .ok H := hH
  have hb' : ConfirmationEligible (Model.goldilocks (V := V)) C n (s - 1) H = .ok b := hb
  have hWalk := walkEnd_of_ghost_eq_ok hRoots hH'
  refine ⟨H, hWalk, ?_⟩
  rw [hb']
  cases b
  · -- `H` fails the test: nothing is saved
    rw [if_neg (by decide)] at h4
    split at h4
    case isTrue hne => exact absurd rfl hne
    case isFalse =>
    simp only [pure, Except.pure, Except.ok.injEq] at h4
    subst h4
    refine ⟨?_, fun j hj => ?_, fun _ => ⟨?_, ?_, fun e' => ?_⟩, fun hf => ?_⟩
    · show n'.A.saved_confirmation (s - 1) = _
      rw [hS, if_neg (fun h => by cases h)]
      exact Function.update_self _ _ _
    · show n'.A.saved_confirmation j = n.A.saved_confirmation j
      rw [hS]
      exact Function.update_of_ne hj _ _
    · show n'.A.fast_blocks = ∅
      rw [hF]
    · show n'.A.latest_confirmed = n.A.latest_confirmed
      rw [hC]
    · show e' ∈ n'.A.lock_entries ↔ e' ∈ n.A.lock_entries ∧ t < e'.d
      rw [hL]
      exact hE e'
    · cases hf
  · rw [if_pos rfl] at h4
    split at h4
    case isFalse hne => exact absurd (Option.some_ne_none H) hne
    split at h4
    case isFalse hveto =>
      -- a live lock vetoes `H`
      simp only [pure, Except.pure, Except.ok.injEq] at h4
      subst h4
      have hx : live_lock_vetoes n.A (fg_to_ac n.S) t H = true :=
        live_lock_vetoes_true_of _ hveto hE
      refine ⟨?_, fun j hj => ?_, fun _ => ⟨?_, ?_, fun e' => ?_⟩, fun _ hv => ?_⟩
      · show n'.A.saved_confirmation (s - 1) = _
        rw [hS, if_pos rfl]
        exact Function.update_self _ _ _
      · show n'.A.saved_confirmation j = n.A.saved_confirmation j
        rw [hS]
        exact Function.update_of_ne hj _ _
      · show n'.A.fast_blocks = ∅
        rw [hF]
      · show n'.A.latest_confirmed = n.A.latest_confirmed
        rw [hC]
      · show e' ∈ n'.A.lock_entries ↔ e' ∈ n.A.lock_entries ∧ t < e'.d
        rw [hL]
        exact hE e'
      · have hv' : live_lock_vetoes n.A (fg_to_ac n.S) t H = false := hv
        rw [hx] at hv'
        cases hv'
    case isTrue hnv =>
    have hnv' : live_lock_vetoes n.A (fg_to_ac n.S) t H = false :=
      live_lock_vetoes_false_of _ hnv hE
    obtain ⟨fb, hfb, h5⟩ := dre_bind_eq_ok h4
    obtain ⟨lk, hlk, h6⟩ := dre_bind_eq_ok h5
    -- the fast blocks and the lockable blocks
    have hfbm : ∀ B : Block V, B ∈ fb ↔ B ∈ (fg_to_ac n.S).tree ∧ B ≠ Block.genesis ∧
        B.AncestorEq H ∧
        fast_test P (fg_to_ac n.S) (SupportVotes (Model.goldilocks (V := V)) C n (s - 1)) (s - 1)
          B = .ok true := by
      intro B
      rw [mem_of_filterM_eq_ok_iff _ _ _ hfb, Finset.mem_filter]
      simp only [Option.value, Option.get_some, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨fun ⟨⟨h1, h2, h3⟩, h4⟩ => ⟨h1, h2, h3, h4⟩, fun ⟨h1, h2, h3, h4⟩ => ⟨⟨h1, h2, h3⟩, h4⟩⟩
    have hlkm : ∀ B : Block V, B ∈ lk ↔ Lockable (Model.goldilocks (V := V)) C P n (s - 1) H B := by
      intro B
      rw [mem_of_filterM_eq_ok_iff _ _ _ hlk]
      constructor
      · rintro ⟨hpath, hp⟩
        rw [Finset.mem_filter] at hpath
        simp only [Option.value, Option.get_some, Bool.and_eq_true, decide_eq_true_eq] at hpath
        obtain ⟨f, hf, hret⟩ := dre_bind_eq_ok hp
        simp only [pure, Except.pure, Except.ok.injEq, Bool.or_eq_true] at hret
        refine ⟨hpath.1, hpath.2.1, hpath.2.2, ?_⟩
        rcases hret with hret | hret
        · subst hret
          exact Or.inl hf
        · refine Or.inr ?_
          rw [slow_test_congr C _ n.A _ _ _ ?_] at hret
          · exact hret
          · intro j hj
            exact Function.update_of_ne (Nat.ne_of_lt hj) _ _
      · rintro ⟨hT, hg, ha, hfs⟩
        have hpath : B ∈ {B ∈ (fg_to_ac n.S).tree | (B ≠ Block.genesis &&
            B.ancestorEq (some H).value) = true} := by
          rw [Finset.mem_filter]
          simp only [Option.value, Option.get_some, Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨hT, hg, ha⟩
        refine ⟨hpath, ?_⟩
        obtain ⟨b', hb'⟩ := filterM_ok_total _ _ _ hlk B hpath
        rw [hb']
        obtain ⟨f, hf, hret⟩ := dre_bind_eq_ok hb'
        simp only [pure, Except.pure, Except.ok.injEq] at hret
        rw [← hret]
        rcases hfs with hfs | hfs
        · have hff := hfs.symm.trans hf
          cases hff
          rfl
        · rw [slow_test_congr C _ n.A _ _ _ ?_]
          · have hfs' : slow_test C n.A (fg_to_ac n.S) (s - 1) B = true := hfs
            rw [hfs', Bool.or_true]
          · intro j hj
            exact Function.update_of_ne (Nat.ne_of_lt hj) _ _
    have hchain : ∀ B ∈ lk, B.AncestorEq H := fun B hB => ((hlkm B).1 hB).2.2.1
    obtain ⟨hsome, hnone⟩ := deepest?_of_chain hchain
    generalize hD : Block.deepest? lk = D at h6
    have hcommon : n'.A.saved_confirmation (s - 1) = some H ∧
        (∀ j : Slot, j ≠ s - 1 → n'.A.saved_confirmation j = n.A.saved_confirmation j) ∧
        n'.A.latest_confirmed = advance (fg_to_ac n.S) n.A.latest_confirmed (some H) ∧
        (∀ B : Block V, B ∈ n'.A.fast_blocks ↔ B ∈ fb) := by
      cases D with
      | none =>
        simp only [ne_eq, not_true_eq_false, dite_false, pure, Except.pure,
          Except.ok.injEq] at h6
        subst h6
        exact ⟨by rw [hS]; exact Function.update_self _ _ _,
          fun j hj => by rw [hS]; exact Function.update_of_ne hj _ _, by rw [hC],
          fun B => by rw [hF]⟩
      | some D =>
        simp only [ne_eq, reduceCtorEq, not_false_eq_true, dite_true, Option.value,
          Option.get_some, pure, Except.pure, Except.ok.injEq] at h6
        subst h6
        exact ⟨by rw [hS]; exact Function.update_self _ _ _,
          fun j hj => by rw [hS]; exact Function.update_of_ne hj _ _, by rw [hC],
          fun B => by rw [hF]⟩
    refine ⟨?_, fun j hj => hcommon.2.1 j hj, fun hc => ?_, fun _ _ => ⟨hcommon.2.2.1,
      fun B => (hcommon.2.2.2 B).trans (hfbm B), fun hno => ?_, fun L hL1 hL2 => ?_⟩⟩
    · show n'.A.saved_confirmation (s - 1) = _
      rw [if_pos rfl]
      exact hcommon.1
    · rcases hc with hc | hc
      · exact absurd rfl hc
      · have hc' : live_lock_vetoes n.A (fg_to_ac n.S) t H = true := hc
        rw [hnv'] at hc'
        cases hc'
    · -- no lockable block: no entry is added
      cases D with
      | none =>
        simp only [ne_eq, not_true_eq_false, dite_false, pure, Except.pure,
          Except.ok.injEq] at h6
        subst h6
        intro e'
        show e' ∈ n'.A.lock_entries ↔ e' ∈ n.A.lock_entries ∧ t < e'.d
        rw [hL]
        exact hE e'
      | some D =>
        exact absurd ⟨D, (hlkm D).1 (hsome D hD).1⟩ hno
    · -- the deepest lockable block is locked
      cases D with
      | none =>
        have := (hlkm L).2 hL1
        rw [hnone hD] at this
        exact absurd this (Finset.notMem_empty _)
      | some D =>
        simp only [ne_eq, reduceCtorEq, not_false_eq_true, dite_true, Option.value,
          Option.get_some, pure, Except.pure, Except.ok.injEq] at h6
        subst h6
        obtain ⟨hDm, hDall⟩ := hsome D hD
        have hLD : L = D := ancestorEq_antisymm (hDall L ((hlkm L).2 hL1))
          (hL2 D ((hlkm D).1 hDm))
        subst hLD
        have hmemU : ∀ x : LockEntry V,
            x ∈ E ∪ {LockEntry.mk L (C.t_ (s - 1 + C.k) + 5 * C.Δ)} ↔
              x ∈ E ∨ x = LockEntry.mk L (C.t_ (s - 1 + C.k) + 5 * C.Δ) := fun x => by
          rw [Finset.mem_union, Finset.mem_singleton]
        refine ⟨fun e' he' => ?_, fun e he hd => ?_, ?_⟩
        · have he0 : e' ∈ n'.A.lock_entries := he'
          rw [hL] at he0
          rcases (hmemU e').1 he0 with he0 | he0
          · exact Or.inl ((hE e').1 he0)
          · subst he0
            exact Or.inr ⟨rfl, rfl⟩
        · show e ∈ n'.A.lock_entries
          rw [hL]
          exact (hmemU e).2 (Or.inl ((hE e).2 ⟨he, hd⟩))
        · refine ⟨LockEntry.mk L (C.t_ (s - 1 + C.k) + 5 * C.Δ), ?_, rfl, rfl⟩
          show LockEntry.mk L (C.t_ (s - 1 + C.k) + 5 * C.Δ) ∈ n'.A.lock_entries
          rw [hL]
          exact (hmemU _).2 (Or.inr rfl)

/-! ## At a node state's own AC state -/

/-- The confirmation update run on a node state's own AC state, all of whose lock entries have a
deadline after `t`, satisfies `ConfirmationUpdated` from `n` to `n` with the answer as its AC
state, when no two blocks of the tree of `fg_to_ac n.S` share a root.

The variables:
- `C`, `P`: the parameters; `n`: the node state; `t`: the time; `s`: the slot; `A'`: the answer;
- `hH`: no two blocks of the tree share a root, and every lock entry of `n` has a deadline after
  `t`.

Read aloud: the spec's update on a node's own state satisfies the record's predicate. -/
theorem confirmationUpdated_at_node [RootOrder] (C : Config) (P : Provisional V)
    (n : NodeState V) (t : Time) (s : Slot) (A' : ACState V)
    (hH : RootsNameBlocksIn (fg_to_ac n.S).tree ∧ ∀ e ∈ n.A.lock_entries, t < e.d)
    (h : update_confirmation C P n.A (fg_to_ac n.S) t s = .ok A') :
    ConfirmationUpdated (Model.goldilocks (V := V)) C P n t s { n with A := A' } :=
  confirmationUpdated_of_update_confirmation_eq_ok C P n t s n.A.lock_entries A' _ hH.1
    (fun e => ⟨fun he => ⟨he, hH.2 e he⟩, fun he => he.1⟩) h rfl rfl rfl rfl

/-- The revocation of a slot after slot `0` run on a node state's own AC state satisfies
`LocksRevoked` from `n` to `n` with the answer as its AC state, when no two blocks of the tree of
`fg_to_ac n.S` share a root.

The variables:
- `P`: the provisional parameters; `n`: the node state; `t`: the time; `s`: the slot;
- `A'`: the answer; `hRoots`: no two blocks of the tree share a root; `hs`: `s` is not `0`.

Read aloud: the spec's revocation on a node's own state satisfies the record's predicate. -/
theorem locksRevoked_at_node [RootOrder] (P : Provisional V) (n : NodeState V) (t : Time)
    (s : Slot) (A' : ACState V) (hRoots : RootsNameBlocksIn (fg_to_ac n.S).tree) (hs : s ≠ 0)
    (h : revoke_locks P n.A (fg_to_ac n.S) t s = .ok A') :
    LocksRevoked (Model.goldilocks (V := V)) P n t s { n with A := A' } :=
  locksRevoked_of_revoke_locks_eq_ok P n t s n.A.lock_entries A' _ hRoots (fun _ he => he)
    (fun _ he _ => he) (fun h0 => absurd h0 hs) h rfl

/-- A lock entry with the block `B` and the deadline `d` is the entry `LockEntry.mk B d`.

The variables:
- `e`: the entry; `B`: the block; `d`: the deadline.

Read aloud: an entry is determined by its block and its deadline. -/
theorem lockEntry_eq_mk {e : LockEntry V} {B : Block V} {d : Time} (hB : e.B = B)
    (hd : e.d = d) : e = LockEntry.mk B d := by
  cases e
  cases hB
  cases hd
  rfl

open GoldilocksCorrectness.Statements.Routines (NodeInv) in
/-- On a node state satisfying `NodeInv`, the spec's opponents of a block among the votes of a
slot the node holds, their equivocators counted out, answer.

The variables:
- `C`, `P`, `X`: the parameters; `n`: the node state; `s`: the slot; `B'`: the block;
- `hI`: the node invariant.

Read aloud: on a node satisfying the invariant, the opponents of a block answer. -/
theorem opponents_answers_of_nodeInv {C : Config} {P : Provisional V} {X : External V}
    {n : NodeState V} (hI : NodeInv C P X n) (s : Slot) (B' : Block V) :
    ∃ o : Finset V, opponents n.A (fg_to_ac n.S) (n.A.pool s) (equivocators (n.A.pool s)) B' =
      .ok o :=
  GoldilocksCorrectness.Proofs.Routines.opponents_ok n.A
    (GoldilocksCorrectness.Proofs.Routines.nodeInv_frameRoots hI) _ _ B'
    (fun vote hv => hI.2.1 s vote (List.mem_toFinset.1 hv))
    (fun H hH => hI.2.2.2.2.1 H
      ((GoldilocksCorrectness.Proofs.Routines.mem_fg_to_ac_tree _ _).1 hH).1)

end GoldilocksCorrectness.Record.Statements.Routines
