module
public import GoldilocksCorrectness.Proofs.Routines.ConfirmedTip
public import GoldilocksCorrectness.Proofs.Routines.Locks
public import GoldilocksCorrectness.Proofs.Routines.Blocks
public import GoldilocksCorrectness.Proofs.Routines.Walk
import all Goldilocks.AC.Confirmation
import all Goldilocks.AC.State

@[expose] public section

/-!
# The revocation and the update under a live lock

Two routine facts about a lock entry on a block `B` that is live: the revocation of the locks keeps
it when fewer than half of the committee oppose its block (`revoke_locks_keeps_entry`), and the
confirmation update cannot record, fast-confirm or lock a block off `B`'s chain, when the record
is `B` or a descendant of `B` and lies in the frame's tree (`update_confirmation_with_live_lock_of_mem`).
With them, the facts about the deepest block of a set that the anchor reads: a nonempty set whose
roots name its blocks has a deepest block (`deepest?_isSome`).


-/

set_option autoImplicit false

open scoped DC

open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn)

variable {V : Type} [DecidableEq V]

/-! ## Raising images -/

/-- Every member of the set of a raising image that answers has its function answer a member of
the image.

The variables:
- `f`: the raising function; `s`: the set; `S`: the answer; `a`: the member of the set. -/
theorem mem_imageM_of_eq_ok {α β : Type} [DecidableEq α] [DecidableEq β] (f : α → DRE β)
    (s : Finset α) (S : Finset β) (h : s.imageM f = .ok S) (a : α) (ha : a ∈ s) :
    ∃ b : β, f a = .ok b ∧ b ∈ S := by
  induction s using Finset.induction_on generalizing S with
  | empty => simp at ha
  | @insert a' s ha' ih =>
    have hstep : (insert a' s).imageM f =
        Finset.unionM (do return {← f a'}) (s.imageM f) := by
      simp only [Finset.imageM, Finset.fold_insert ha']
    rw [hstep] at h
    cases hf : f a' with
    | error e => simp [hf, Finset.unionM, bind, Except.bind] at h
    | ok b' =>
      cases hs : s.imageM f with
      | error e => simp [hf, hs, Finset.unionM, bind, Except.bind, pure, Except.pure] at h
      | ok S' =>
        simp only [hf, hs, Finset.unionM, bind, Except.bind, pure, Except.pure,
          Except.ok.injEq] at h
        subst h
        rcases Finset.mem_insert.1 ha with rfl | ha
        · exact ⟨b', hf, Finset.mem_union_left _ (Finset.mem_singleton_self _)⟩
        · obtain ⟨b, hb, hbS⟩ := ih S' hs ha
          exact ⟨b, hb, Finset.mem_union_right _ hbS⟩

/-- `B` is a strict ancestor of `C` (`B.ancestorStrict C`) exactly when `B` is not `C` and `B` is
an ancestor of `C` or `C` itself.

The variables:
- `B`, `C`: the two blocks. -/
theorem ancestorStrict_iff {B C : Block V} :
    B.ancestorStrict C = true ↔ B ≠ C ∧ B.AncestorEq C := by
  simp [Block.ancestorStrict, Block.AncestorEq]

variable [RootOrder]

/-! ## The deepest block -/

omit [DecidableEq V] in
/-- No block is deeper than itself.

The variables:
- `B`: the block. -/
theorem deeper_irrefl (B : Block V) : B.deeper B = false := by
  simp [Block.deeper, RootOrder.irrefl]

omit [DecidableEq V] in
/-- A block deeper than one deeper than `D` is deeper than `D`.

The variables:
- `B`, `C`, `D`: the three blocks. -/
theorem deeper_trans {B C D : Block V} (h1 : B.deeper C = true) (h2 : C.deeper D = true) :
    B.deeper D = true := by
  simp only [Block.deeper, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at h1 h2 ⊢
  rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
  · left; omega
  · left; omega
  · left; omega
  · right; exact ⟨by omega, RootOrder.trans _ _ _ h2' h1'⟩

omit [DecidableEq V] in
/-- Of two blocks with different roots, one is deeper than the other.

The variables:
- `B`, `C`: the two blocks. -/
theorem deeper_total {B C : Block V} (hr : B.root ≠ C.root) :
    B.deeper C = true ∨ C.deeper B = true := by
  simp only [Block.deeper, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true]
  rcases Nat.lt_trichotomy B.depth C.depth with h | h | h
  · right; left; exact h
  · rcases RootOrder.total _ _ hr with h' | h'
    · right; right; exact ⟨h, h'⟩
    · left; right; exact ⟨h.symm, h'⟩
  · left; left; exact h

/-- A nonempty set of blocks has a member no member of which is deeper.

The variables:
- `T`: the set. -/
theorem exists_deepest_member (T : Finset (Block V)) (hT : T.Nonempty) :
    ∃ X ∈ T, ∀ C ∈ T, C.deeper X = false := by
  induction T using Finset.induction_on with
  | empty => simp at hT
  | @insert a T ha ih =>
    rcases T.eq_empty_or_nonempty with h | h
    · subst h
      refine ⟨a, Finset.mem_insert_self _ _, fun C hC => ?_⟩
      rw [Finset.mem_insert] at hC
      rcases hC with rfl | hC
      · exact deeper_irrefl C
      · simp at hC
    · obtain ⟨m, hm, hmax⟩ := ih h
      by_cases hma : a.deeper m = true
      · refine ⟨a, Finset.mem_insert_self _ _, fun C hC => ?_⟩
        rcases Finset.mem_insert.1 hC with rfl | hC
        · exact deeper_irrefl C
        · cases hCa : C.deeper a
          · rfl
          · have := deeper_trans hCa hma
            rw [hmax C hC] at this
            cases this
      · refine ⟨m, Finset.mem_insert_of_mem hm, fun C hC => ?_⟩
        rcases Finset.mem_insert.1 hC with rfl | hC
        · simpa using hma
        · exact hmax C hC

/-- A nonempty set of blocks no two of which share a root has a deepest block.

Why: some member has no deeper member; two such members with different roots would each be
deeper than the other.

The variables:
- `T`: the set. -/
theorem deepest?_isSome (T : Finset (Block V)) (hT : T.Nonempty)
    -- no two blocks of `T` share a root
    (hR : RootsNameBlocksIn T) :
    ∃ X : Block V, Block.deepest? T = some X := by
  obtain ⟨X, hX, hmax⟩ := exists_deepest_member T hT
  refine ⟨X, pickUnique?_eq_some hX ?_ fun Y hY hYd => ?_⟩
  · simp only [Block.isDeepestIn, decide_eq_true_eq]
    exact hmax
  · simp only [Block.isDeepestIn, decide_eq_true_eq] at hYd
    by_contra hne
    have hr : Y.root ≠ X.root := fun h => hne (hR Y hY X hX h)
    rcases deeper_total hr with h | h
    · rw [hmax Y hY] at h; cases h
    · rw [hYd X hX] at h; cases h

/-! ## The revocation -/

/-- The revocation moves an entry on a block of the frame's tree other than the genesis block,
fewer than half of the committee opposing it, to itself.

Why: `e.B` is a candidate, and every candidate is an ancestor of `e.B` or `e.B`, so of smaller
depth or `e.B` itself; `e.B` is the deepest candidate.

The variables:
- `P`: the values; `A`: the AC state; `Φ`: the frame; `votes`, `equivocators`: the votes counted
  and the validators counted out; `s`: the slot; `e`: the entry; `b`: the answer. -/
theorem moved_entry_eq_self {P : Provisional V} {A : ACState V} {Φ : Frame V}
    {votes : Finset (GoldfishVote V)} {equivocators : Finset V} {s : Slot}
    {e : LockEntry V} {b : Option (LockEntry V)}
    (h : moved_entry P A Φ votes equivocators s e = .ok b)
    (hT : e.B ∈ Φ.tree) (hgen : e.B ≠ Block.genesis)
    -- the opponents of `e.B`, counted twice, are fewer than the committee of slot `s − 1`
    (hopp : ∀ opp : Finset V, opponents A Φ votes equivocators e.B = .ok opp →
      2 * |opp| < |P.committee (s - 1)|) :
    b = some e := by
  simp only [moved_entry] at h
  obtain ⟨cands, hfilter, hret⟩ := dre_bind_eq_ok h
  obtain ⟨bt, hbt⟩ := filterM_ok_total _ _ cands hfilter e.B hT
  obtain ⟨o, ho, -⟩ := dre_bind_eq_ok hbt
  have hmem : e.B ∈ cands := by
    rw [mem_of_filterM_eq_ok_iff _ _ _ hfilter]
    refine ⟨hT, ?_⟩
    rw [ho, dre_bind_ok]
    have := hopp o ho
    have hr : e.B.ancestorEq e.B = true := ancestorEq_refl e.B
    simp [hgen, this, hr]
    rfl
  have hdeep : Block.deepest? cands = some e.B := by
    refine deepest?_eq_some hmem (fun C hC => ?_) (fun C hC hd => ?_)
    · rw [mem_of_filterM_eq_ok_iff _ _ _ hfilter] at hC
      obtain ⟨-, hp⟩ := hC
      obtain ⟨o', -, hp'⟩ := dre_bind_eq_ok hp
      simp only [pure, Except.pure, Except.ok.injEq, Bool.and_eq_true, decide_eq_true_eq] at hp'
      exact depth_le_of_ancestorEq hp'.1.2
    · rw [mem_of_filterM_eq_ok_iff _ _ _ hfilter] at hC
      obtain ⟨-, hp⟩ := hC
      obtain ⟨o', -, hp'⟩ := dre_bind_eq_ok hp
      simp only [pure, Except.pure, Except.ok.injEq, Bool.and_eq_true, decide_eq_true_eq] at hp'
      exact eq_of_ancestorEq_of_depth hp'.1.2 (by omega)
  rw [hdeep] at hret
  simp only [ne_eq, reduceCtorEq, not_false_eq_true, dite_true, Option.value,
    Option.get_some] at hret
  cases hret
  rfl

/-- An entry that `moved_entry` answers is not on the genesis block: the candidates it picks from
exclude it.

The variables:
- `P`: the values; `A`: the AC state; `Φ`: the frame; `votes`, `equivocators`: the votes counted
  and the validators counted out; `s`: the slot; `e`: the entry moved; `e'`: the entry answered;
- `h`: `moved_entry` answers `e'`. -/
theorem moved_entry_ne_genesis {P : Provisional V} {A : ACState V} {Φ : Frame V}
    {votes : Finset (GoldfishVote V)} {equivocators : Finset V} {s : Slot}
    {e e' : LockEntry V}
    (h : moved_entry P A Φ votes equivocators s e = .ok (some e')) :
    e'.B ≠ Block.genesis := by
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
    obtain ⟨-, hp⟩ := hmem
    obtain ⟨o, -, hret'⟩ := dre_bind_eq_ok hp
    simp only [pure, Except.pure, Except.ok.injEq, Bool.and_eq_true, decide_eq_true_eq] at hret'
    rw [hB']
    exact hret'.1.1

variable [Fintype V]

/-- **Routine fact: the revocation keeps a live entry fewer than half of the committee oppose.**
The proof; the audited statement is in
`Statements/Executions/PeriodHolderStatements.lean`.

The variables:
- `P`: the values; `A`, `A'`: the AC state before and after the revocation; `Φ`: the frame;
  `t`: the time; `s'`: the slot; `e`: the entry. -/
theorem revoke_locks_keeps_entry (P : Provisional V) (A A' : ACState V) (Φ : Frame V) (t : Time)
    (s' : Slot) (e : LockEntry V)
    (hs' : s' ≠ 0) (hrev : revoke_locks P A Φ t s' = .ok A')
    (he : e ∈ A.lock_entries) (hlive : is_live Φ t e = true) (hgen : e.B ≠ Block.genesis)
    (hopp : ∀ opp : Finset V,
      opponents A Φ (A.pool (s' - 1)) (equivocators (A.pool (s' - 1))) e.B = .ok opp →
      2 * |opp| < |P.committee (s' - 1)|) :
    e ∈ A'.lock_entries := by
  simp only [revoke_locks] at hrev
  rw [if_neg hs'] at hrev
  obtain ⟨moved, hmoved, hret⟩ := dre_bind_eq_ok hrev
  cases hret
  show e ∈ present moved
  rw [present_mem_iff]
  have heL : e ∈ live_entries A Φ t := by
    simp only [live_entries, Finset.mem_filter]
    exact ⟨he, hlive⟩
  obtain ⟨b, hb, hbm⟩ := mem_imageM_of_eq_ok _ _ _ hmoved e heL
  have hT : e.B ∈ Φ.tree := by
    simp only [is_live, Bool.and_eq_true, decide_eq_true_eq] at hlive
    exact hlive.2
  rw [moved_entry_eq_self hb hT hgen hopp] at hbm
  exact hbm

/-- After the revocation of slot `s ≥ 1`, no lock entry left is on the genesis block.

Why: every entry left is an entry `moved_entry` answered (`moved_entry_ne_genesis`).

The variables:
- `P`: the values; `A`, `A'`: the AC state before and after the revocation; `Φ`: the frame;
  `t`: the time; `s`: the slot;
- `hs`: the slot is not `0`; `hRevoke`: the revocation answers `A'`. -/
theorem revoke_locks_entry_ne_genesis {P : Provisional V}
    {A A' : ACState V} {Φ : Frame V} {t : Time} {s : Slot}
    (hs : 1 ≤ s)
    (hRevoke : revoke_locks P A Φ t s = .ok A') :
    ∀ e ∈ A'.lock_entries, e.B ≠ Block.genesis := by
  simp only [revoke_locks] at hRevoke
  rw [if_neg (Nat.one_le_iff_ne_zero.mp hs)] at hRevoke
  obtain ⟨moved, hmoved, hret⟩ := dre_bind_eq_ok hRevoke
  cases hret
  intro e he
  rw [present_mem_iff] at he
  obtain ⟨e₀, -, he₀⟩ := mem_of_imageM_eq_ok _ _ _ hmoved _ he
  exact moved_entry_ne_genesis he₀

/-! ## The confirmation update -/

/-- **Routine fact: the update under a live lock on `B`, with the record in the frame's tree.**
The proof; the audited statement is in `Statements/Executions/PeriodHolderStatements.lean`.

The variables:
- `C`, `P`: the parameters and the values; `A`, `A'`: the AC state before and after the update;
  `Φ`: the frame; `t`: the time; `s'`: the slot of the update; `B`: the locked block; `d`: the
  lock's deadline. -/
theorem update_confirmation_with_live_lock_of_mem (C : Config) (P : Provisional V)
    (A A' : ACState V) (Φ : Frame V) (t : Time) (s' : Slot) (B : Block V) (d : Time)
    (hs' : s' ≠ 0) (hUpdate : update_confirmation C P A Φ t s' = .ok A')
    (hlock : LockEntry.mk B d ∈ A.lock_entries) (hlive : is_live Φ t (LockEntry.mk B d) = true)
    (hin : A.latest_confirmed ∈ Φ.tree) (hold : B.AncestorEq A.latest_confirmed) :
    B.AncestorEq A'.latest_confirmed ∧
    (∀ D ∈ A'.fast_blocks, D.compatible B = true) ∧
    (∀ e ∈ A'.lock_entries, e ∈ A.lock_entries ∨ e.B.compatible B = true) ∧
    (∀ C' : Block V, A'.saved_confirmation (s' - 1) = some C' →
      C'.compatible B = true ∨ live_lock_vetoes A Φ t C' = true) := by
  simp only [update_confirmation] at hUpdate
  rw [if_neg hs'] at hUpdate
  obtain ⟨early, -, h1⟩ := dre_bind_eq_ok hUpdate
  obtain ⟨late, -, h2⟩ := dre_bind_eq_ok h1
  obtain ⟨H, -, h3⟩ := dre_bind_eq_ok h2
  obtain ⟨b, -, h4⟩ := dre_bind_eq_ok h3
  cases b
  · -- no block is saved
    rw [if_neg (by decide)] at h4
    split at h4
    case isTrue hne => exact absurd rfl hne
    case isFalse =>
      simp only [pure, Except.pure, Except.ok.injEq] at h4
      subst h4
      refine ⟨hold, fun D hD => by simp at hD, fun e he => Or.inl he, fun C' hC' => ?_⟩
      simp only [Function.update_self] at hC'
      cases hC'
  rw [if_pos rfl] at h4
  split at h4
  case isFalse hne => exact absurd (Option.some_ne_none H) hne
  split at h4
  case isFalse hveto =>
    -- a live lock vetoes `H`: nothing but the saved confirmation and the fast blocks is written
    simp only [pure, Except.pure, Except.ok.injEq] at h4
    subst h4
    refine ⟨hold, fun D hD => by simp at hD, fun e he => Or.inl he, fun C' hC' => ?_⟩
    simp only [Function.update_self, Option.some.injEq] at hC'
    subst hC'
    right
    have h' : live_lock_vetoes { A with
        saved_confirmation := Function.update A.saved_confirmation (s' - 1) (some H),
        fast_blocks := ∅ } Φ t H = true := by
      simpa [Option.value, Option.get_some] using hveto
    exact h'
  case isTrue hveto =>
    obtain ⟨fb, hfb, h5⟩ := dre_bind_eq_ok h4
    obtain ⟨lk, hlk, h6⟩ := dre_bind_eq_ok h5
    have hv' : live_lock_vetoes { A with
        saved_confirmation := Function.update A.saved_confirmation (s' - 1) (some H),
        fast_blocks := ∅ } Φ t H = false := by
      simpa [Option.value, Option.get_some] using hveto
    have hv : live_lock_vetoes A Φ t H = false := hv'
    -- the live lock on `B` does not veto `H`, so `H` is compatible with `B`
    have hHB : H.compatible B = true := by
      have hno : ¬ (B.conflicts H = true) := by
        intro hc
        have : live_lock_vetoes A Φ t H = true := by
          simp only [live_lock_vetoes, decide_eq_true_eq]
          exact ⟨_, hlock, hlive, hc⟩
        rw [hv] at this
        cases this
      rw [conflicts_iff, compatible_iff, not_not] at hno
      rw [compatible_iff]
      exact hno.symm
    have hpathB : ∀ D : Block V, D.AncestorEq H → D.compatible B = true :=
      fun D hD => compatible_of_ancestorEq_compatible hD hHB
    have hfbB : ∀ D ∈ fb, D.compatible B = true := by
      intro D hD
      rw [mem_of_filterM_eq_ok_iff _ _ _ hfb] at hD
      obtain ⟨hD, -⟩ := hD
      simp only [Finset.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hD
      exact hpathB D hD.2.2
    have hlkB : ∀ D ∈ lk, D.compatible B = true := by
      intro D hD
      rw [mem_of_filterM_eq_ok_iff _ _ _ hlk] at hD
      obtain ⟨hD, -⟩ := hD
      simp only [Finset.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hD
      exact hpathB D hD.2.2
    -- the record: kept, or `H` when `B` is an ancestor of `H`
    have hrec : B.AncestorEq (advance Φ A.latest_confirmed (some H)) := by
      rcases advance_some Φ A.latest_confirmed H with ⟨-, -, ha⟩ | ⟨hn, ha⟩
      · rw [ha]; exact hold
      · rw [ha]
        rcases (compatible_iff H B).1 hHB with hHB' | hBH
        · exact absurd ⟨hin, ancestorEq_trans hHB' hold⟩ hn
        · exact hBH
    have hsaved : ∀ C' : Block V,
        Function.update A.saved_confirmation (s' - 1) (some H) (s' - 1) = some C' →
        C'.compatible B = true ∨ live_lock_vetoes A Φ t C' = true := by
      intro C' hC'
      simp only [Function.update_self, Option.some.injEq] at hC'
      subst hC'
      exact Or.inl hHB
    generalize hD : Block.deepest? lk = D at h6
    cases D with
    | none =>
        simp only [ne_eq, not_true_eq_false, dite_false, pure, Except.pure,
          Except.ok.injEq] at h6
        subst h6
        exact ⟨hrec, hfbB, fun e he => Or.inl he, hsaved⟩
    | some D =>
        simp only [ne_eq, reduceCtorEq, not_false_eq_true, dite_true, Option.value,
          Option.get_some, pure, Except.pure, Except.ok.injEq] at h6
        subst h6
        refine ⟨hrec, hfbB, fun e he => ?_, hsaved⟩
        rcases Finset.mem_union.1 he with he | he
        · exact Or.inl he
        · rw [Finset.mem_singleton] at he
          subst he
          exact Or.inr (hlkB D (deepest?_mem hD))

/-- **Routine fact: the update writes only blocks of the frame's tree.** Every answer `A'` of the
confirmation update over the frame `Φ` keeps the record of the confirmed tip or records a block of
which the frame's finalized block `Φ.F` is an ancestor, or which is `Φ.F`; has every fast block a
fast block of `A` or a block of `Φ.tree`; has every lock entry an entry of `A` or an entry on a
block of `Φ.tree` other than the genesis block; and keeps every lock entry of `A`.

Why: the walk starts at `Φ.F`, so the confirmation it saves is `Φ.F` or a descendant of `Φ.F`,
and `advance` records the old record or that confirmation; the fast blocks and the new lock are
blocks of the path, which holds blocks of `Φ.tree` other than the genesis block; the lock entries
are only added to. At slot `0` the update answers `A`.

The variables:
- `C`, `P`: the parameters and the values; `A`, `A'`: the AC state before and after the update;
  `Φ`: the frame; `t`: the time; `s'`: the slot of the update;
- `hUpdate`: the update answers `A'`.

Read aloud: the update records, fast-confirms and locks nothing outside the frame's tree, and
drops no lock. -/
theorem update_confirmation_in_frame (C : Config) (P : Provisional V) (A A' : ACState V)
    (Φ : Frame V) (t : Time) (s' : Slot)
    (hUpdate : update_confirmation C P A Φ t s' = .ok A') :
    (A'.latest_confirmed = A.latest_confirmed ∨ Φ.F.AncestorEq A'.latest_confirmed) ∧
    (∀ D ∈ A'.fast_blocks, D ∈ A.fast_blocks ∨ D ∈ Φ.tree) ∧
    (∀ e ∈ A'.lock_entries, e ∈ A.lock_entries ∨ (e.B ∈ Φ.tree ∧ e.B ≠ Block.genesis)) ∧
    A.lock_entries ⊆ A'.lock_entries := by
  simp only [update_confirmation] at hUpdate
  by_cases hs' : s' = 0
  · rw [if_pos hs'] at hUpdate
    simp only [pure, Except.pure, Except.ok.injEq] at hUpdate
    subst hUpdate
    exact ⟨Or.inl rfl, fun D hD => Or.inl hD, fun e he => Or.inl he, subset_refl _⟩
  rw [if_neg hs'] at hUpdate
  obtain ⟨early, -, h1⟩ := dre_bind_eq_ok hUpdate
  obtain ⟨late, -, h2⟩ := dre_bind_eq_ok h1
  obtain ⟨H, hH, h3⟩ := dre_bind_eq_ok h2
  obtain ⟨b, -, h4⟩ := dre_bind_eq_ok h3
  have hFH : Φ.F.AncestorEq H := by
    rcases ghost_spec hH with h | ⟨h, -⟩
    · rw [h]; exact ancestorEq_refl _
    · exact h
  cases b
  · rw [if_neg (by decide)] at h4
    split at h4
    case isTrue hne => exact absurd rfl hne
    case isFalse =>
      simp only [pure, Except.pure, Except.ok.injEq] at h4
      subst h4
      exact ⟨Or.inl rfl, fun D hD => by simp at hD, fun e he => Or.inl he, subset_refl _⟩
  rw [if_pos rfl] at h4
  split at h4
  case isFalse hne => exact absurd (Option.some_ne_none H) hne
  split at h4
  case isFalse =>
    simp only [pure, Except.pure, Except.ok.injEq] at h4
    subst h4
    exact ⟨Or.inl rfl, fun D hD => by simp at hD, fun e he => Or.inl he, subset_refl _⟩
  case isTrue =>
    obtain ⟨fb, hfb, h5⟩ := dre_bind_eq_ok h4
    obtain ⟨lk, hlk, h6⟩ := dre_bind_eq_ok h5
    have hrec' : advance Φ A.latest_confirmed (some H) = A.latest_confirmed ∨
        Φ.F.AncestorEq (advance Φ A.latest_confirmed (some H)) := by
      rcases advance_some Φ A.latest_confirmed H with ⟨-, -, ha⟩ | ⟨-, ha⟩
      · exact Or.inl ha
      · rw [ha]; exact Or.inr hFH
    have hfbT : ∀ D ∈ fb, D ∈ Φ.tree := by
      intro D hD
      rw [mem_of_filterM_eq_ok_iff _ _ _ hfb] at hD
      obtain ⟨hD, -⟩ := hD
      simp only [Finset.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hD
      exact hD.1
    have hlkT : ∀ D ∈ lk, D ∈ Φ.tree ∧ D ≠ Block.genesis := by
      intro D hD
      rw [mem_of_filterM_eq_ok_iff _ _ _ hlk] at hD
      obtain ⟨hD, -⟩ := hD
      simp only [Finset.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hD
      exact ⟨hD.1, hD.2.1⟩
    generalize hD : Block.deepest? lk = D at h6
    cases D with
    | none =>
        simp only [ne_eq, not_true_eq_false, dite_false, pure, Except.pure,
          Except.ok.injEq] at h6
        subst h6
        exact ⟨hrec', fun D hD => Or.inr (hfbT D hD), fun e he => Or.inl he, subset_refl _⟩
    | some D =>
        simp only [ne_eq, reduceCtorEq, not_false_eq_true, dite_true, Option.value,
          Option.get_some, pure, Except.pure, Except.ok.injEq] at h6
        subst h6
        refine ⟨hrec', fun D hD => Or.inr (hfbT D hD), fun e he => ?_,
          Finset.subset_union_left⟩
        rcases Finset.mem_union.1 he with he | he
        · exact Or.inl he
        · rw [Finset.mem_singleton] at he
          subst he
          exact Or.inr (hlkT D (deepest?_mem hD))

end GoldilocksCorrectness.Proofs.Routines
