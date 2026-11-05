module
public import GoldilocksCorrectness.Proofs.Routines.Locks
public import GoldilocksCorrectness.Proofs.Routines.ACStore
import all Goldilocks.AC.Confirmation
import all Goldilocks.AC.State
import all Goldilocks.Config
import all GoldilocksCorrectness.Statements.Routines.ScheduleDefs

@[expose] public section

/-!
# What the confirmation update reads

The facts about the readers of the confirmation update `update_confirmation` that the proof of
Lemma 8b uses: a resolution time is never earlier than the vote's stamp (`resolution_time_eq_some`),
what `occurrenceBefore` answers, which votes the early and the late filters keep, and when no live
lock entry vetoes a block.
-/

set_option autoImplicit false

open scoped DC

open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Statements.Routines

variable {V : Type} [DecidableEq V]

/-! ## Stamps and resolution times -/

/-- A vote that resolves at `x` has a stamp, and the stamp is `x` or earlier.

The variables:
- `T`: the block tree; `tb`, `tv`: the block and the vote stamps; `vote`: the vote;
- `x`: its resolution time. -/
theorem resolution_time_eq_some {T : Finset (Block V)} {tb : TimestampMap (Block V)}
    {tv : TimestampMap (GoldfishVote V)} {vote : GoldfishVote V} {x : Stamp}
    (h : resolution_time T tb tv vote = .ok (some x)) :
    ∃ τ : Stamp, tv vote = some τ ∧ τ ≤ x := by
  simp only [resolution_time] at h
  obtain ⟨H?, -, h1⟩ := dre_bind_eq_ok h
  cases H? with
  | none => cases h1
  | some H =>
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, dite_true, Option.value,
      Option.get_some] at h1
    split at h1
    · cases hv : tv vote with
      | none => simp [hv, liftM_none, bind, Except.bind] at h1
      | some τ =>
        cases hb : tb H with
        | none => simp [hv, hb, liftM_some, liftM_none, bind, Except.bind] at h1
        | some τH =>
          simp only [hv, hb, liftM_some, bind, Except.bind, pure, Except.pure, Except.ok.injEq,
            Option.some.injEq] at h1
          exact ⟨τ, rfl, h1 ▸ le_max_left τ τH⟩
    · cases h1

/-- A vote that resolves at `x` in `A` has a stamp in `A`, and the stamp is `x` or earlier.

The variables:
- `A`: the AC state; `Φ`: the frame; `vote`: the vote; `x`: its resolution time. -/
theorem tau_eq_some_stamp {A : ACState V} {Φ : Frame V} {vote : GoldfishVote V} {x : Stamp}
    (h : A.tau Φ vote = .ok (some x)) : ∃ τ : Stamp, A.timestamp_vote vote = some τ ∧ τ ≤ x :=
  resolution_time_eq_some h

/-- An occurrence is strictly earlier than the time `t` exactly when it is a stamp strictly earlier
than `t`.

The variables:
- `o`: the occurrence; `t`: the time. -/
theorem occurrenceBefore_eq_true_iff (o : Occurrence) (t : Time) :
    occurrenceBefore o t = true ↔ ∃ x : Stamp, o = some x ∧ x < (t : Stamp) := by
  cases o with
  | none => simp [occurrenceBefore, Id.run]
  | some x =>
    show decide (x < (t : Stamp)) = true ↔ _
    simp

/-! ## The early and the late votes -/

/-- A vote is kept by the early filter of the confirmation update exactly when it is one of
`votes` and resolves strictly before `c`.

The variables:
- `A`: the AC state; `Φ`: the frame; `votes`: the votes filtered; `c`: the cutoff;
- `early`: the answer; `vote`: the vote. -/
theorem mem_early_iff {A : ACState V} {Φ : Frame V} {votes : Finset (GoldfishVote V)} {c : Time}
    {early : Finset (GoldfishVote V)}
    (h : votes.filterM (fun vote => do
      let x ← A.tau Φ vote
      pure (occurrenceBefore x c)) = .ok early)
    (vote : GoldfishVote V) :
    vote ∈ early ↔ vote ∈ votes ∧ ∃ x : Stamp, A.tau Φ vote = .ok (some x) ∧ x < (c : Stamp) := by
  rw [mem_of_filterM_eq_ok_iff _ _ _ h]
  refine and_congr_right fun _ => ?_
  constructor
  · intro hp
    obtain ⟨o, ho, hret⟩ := dre_bind_eq_ok hp
    simp only [pure, Except.pure, Except.ok.injEq] at hret
    obtain ⟨x, rfl, hx⟩ := (occurrenceBefore_eq_true_iff o c).1 hret
    exact ⟨x, ho, hx⟩
  · rintro ⟨x, hx, hlt⟩
    simp only [hx, dre_bind_ok]
    show Except.ok _ = Except.ok _
    rw [(occurrenceBefore_eq_true_iff (some x) c).2 ⟨x, rfl, hlt⟩]

/-- A vote is kept by the late filter (`beforeCutoff`) exactly when it is one of `votes` and has
a stamp strictly before `c`.

The variables:
- `ts`: the stamps; `votes`: the votes filtered; `c`: the cutoff; `late`: the answer;
- `vote`: the vote. -/
theorem mem_beforeCutoff_iff {ts : TimestampMap (GoldfishVote V)} {c : Time}
    {votes late : Finset (GoldfishVote V)} (h : beforeCutoff ts c votes = .ok late)
    (vote : GoldfishVote V) :
    vote ∈ late ↔ vote ∈ votes ∧ ∃ τ : Stamp, ts vote = some τ ∧ τ < (c : Stamp) := by
  simp only [beforeCutoff] at h
  rw [mem_of_filterM_eq_ok_iff _ _ _ h]
  refine and_congr_right fun _ => ?_
  cases hv : ts vote with
  | none => simp [liftM_none, bind, Except.bind]
  | some τ =>
    simp only [liftM_some, bind, Except.bind, pure, Except.pure, Except.ok.injEq,
      decide_eq_true_eq, Option.some.injEq]
    exact ⟨fun h => ⟨τ, rfl, h⟩, fun ⟨τ', hτ', h⟩ => hτ' ▸ h⟩

/-! ## The veto -/

/-- No live lock entry vetoes `B` when the block of every live entry is compatible with `B`.

The variables:
- `A`: the AC state; `Φ`: the frame; `t`: the time; `B`: the block. -/
theorem live_lock_vetoes_eq_false {A : ACState V} {Φ : Frame V} {t : Time} {B : Block V}
    -- the block of every lock entry of `A` live at `t` is compatible with `B`
    (h : ∀ e ∈ A.lock_entries, is_live Φ t e = true → e.B.compatible B = true) :
    live_lock_vetoes A Φ t B = false := by
  simp only [live_lock_vetoes, decide_eq_false_iff_not, not_exists, not_and]
  intro e he hlive hconf
  exact ((conflicts_iff _ _).1 hconf) (h e he hlive)

end GoldilocksCorrectness.Proofs.Routines

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

section

variable [RootOrder]

/-- Every answer of the confirmation update keeps the pool and the stamps: it writes the saved
confirmation, the fast blocks, the record of the confirmed tip and the lock entries only.

The variables:
- `C`, `P`: the parameters and the values; `A`: the AC state; `Φ`: the frame; `t`: the time;
  `s`: the slot. -/
theorem update_confirmation_keepsVotes (C : Config) (P : Provisional V) (A : ACState V)
    (Φ : Frame V) (t : Time) (s : Slot) :
    DREPost (update_confirmation C P A Φ t s) (KeepsVotes A) := by
  simp only [update_confirmation]
  repeat' first
    | exact DREPost.pure ⟨rfl, rfl, rfl⟩
    | refine DREPost.dite (fun _ => ?_) (fun _ => ?_)
    | refine DREPost.ite (fun _ => ?_) (fun _ => ?_)
    | refine DREPost.bind_any (fun _ => ?_)

/-- The confirmation update keeps "`VotesInv` at `t'`, with the block stamps of `A₀`". -/
theorem update_confirmation_from {P : Provisional V} {A₀ : ACState V} {t' : Time} (C : Config)
    (A : ACState V) (Φ : Frame V) (t : Time) (s : Slot)
    (h : VotesInv P A t' ∧ A.timestamp_block = A₀.timestamp_block) :
    DREPost (update_confirmation C P A Φ t s)
      (fun A' => VotesInv P A' t' ∧ A'.timestamp_block = A₀.timestamp_block) :=
  (update_confirmation_keepsVotes C P A Φ t s).mono
    (fun _ hk => ⟨h.1.of_keeps hk, hk.2.2.trans h.2⟩)

end

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- A fast block `B` of the answer of the confirmation update of slot `s` is the saved
confirmation of slot `s − 1` of the answer, or an ancestor of it.

Why: the update empties the fast blocks, and writes them, after saving some block `H` as the
confirmation of slot `s − 1`, as blocks of its path, the non-genesis blocks of `Φ.tree` that are
`H` or ancestors of `H`.

The variables:
- `C`: the configuration; `P`: the provisional parameters, with the committees;
- `A`: the AC state before the update; `A'`: the AC state after it; `Φ`: the frame;
- `t`: the time of the update; `s`: the slot of the update; `B`: the fast block. -/
theorem update_confirmation_fast_block_saved (C : Config) (P : Provisional V)
    (A A' : ACState V) (Φ : Frame V) (t : Time) (s : Slot) (B : Block V)
    -- the slot is not the first
    (hs : 1 ≤ s)
    -- the confirmation update of slot `s` answers `A'`
    (hUpdate : update_confirmation C P A Φ t s = .ok A')
    -- `B` is a fast block of the answer
    (hB : B ∈ A'.fast_blocks) :
    ∃ C' : Block V, A'.saved_confirmation (s - 1) = some C' ∧ B.AncestorEq C' := by
  simp only [update_confirmation] at hUpdate
  rw [if_neg (Nat.one_le_iff_ne_zero.mp hs)] at hUpdate
  obtain ⟨early, -, h1⟩ := dre_bind_eq_ok hUpdate
  obtain ⟨late, -, h2⟩ := dre_bind_eq_ok h1
  obtain ⟨H, -, h3⟩ := dre_bind_eq_ok h2
  obtain ⟨b, -, h4⟩ := dre_bind_eq_ok h3
  cases b
  · -- no block is saved: the fast blocks are emptied
    rw [if_neg (by decide)] at h4
    split at h4
    case isTrue hne => exact absurd rfl hne
    case isFalse =>
      simp only [pure, Except.pure, Except.ok.injEq] at h4
      subst h4
      simp at hB
  rw [if_pos rfl] at h4
  split at h4
  case isFalse hne => exact absurd (Option.some_ne_none H) hne
  split at h4
  case isFalse =>
    -- a live lock vetoes the confirmation: the fast blocks are emptied
    simp only [pure, Except.pure, Except.ok.injEq] at h4
    subst h4
    simp at hB
  obtain ⟨fb, hfb, h5⟩ := dre_bind_eq_ok h4
  obtain ⟨lk, -, h6⟩ := dre_bind_eq_ok h5
  -- the saved confirmation is `H` and the fast blocks are `fb`, whatever the deepest lockable
  -- block
  have hA' : A'.saved_confirmation (s - 1) = some H ∧ A'.fast_blocks = fb := by
    generalize hD : Block.deepest? lk = D at h6
    cases D with
    | none =>
      simp only [ne_eq, not_true_eq_false, dite_false, pure, Except.pure,
        Except.ok.injEq] at h6
      subst h6
      exact ⟨Function.update_self _ _ _, rfl⟩
    | some D =>
      simp only [ne_eq, reduceCtorEq, not_false_eq_true, dite_true, Option.value, Option.get_some,
        pure, Except.pure, Except.ok.injEq] at h6
      subst h6
      exact ⟨Function.update_self _ _ _, rfl⟩
  refine ⟨H, hA'.1, ?_⟩
  rw [hA'.2] at hB
  have hpath := ((mem_of_filterM_eq_ok_iff _ _ _ hfb B).1 hB).1
  simp only [Finset.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hpath
  exact hpath.2.2

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **Kit fact, the lock entry on a saved fast confirmation.** When the confirmation update of a
slot `s ≠ 0` answers `A'`, saves `B` as the confirmation of slot `s − 1`, and `B` is a fast block
of `A'`, then `A'` holds the lock entry on `B` with the deadline `C.t_ (s − 1 + C.k) + 5 · C.Δ`,
and `B` is in `Φ.tree`.

The variables:
- `C`, `P`: the parameters and the values; `A`, `A'`: the AC state before and after the update;
- `Φ`: the frame; `t`: the time; `s`: the slot of the update; `B`: the saved confirmation.

Read aloud: an update that saves a fast confirmation locks it. -/
theorem lock_entry_of_saved_fast (C : Config) (P : Provisional V) (A A' : ACState V)
    (Φ : Frame V) (t : Time) (s : Slot) (B : Block V) (hs : s ≠ 0)
    (hUpdate : update_confirmation C P A Φ t s = .ok A')
    (hSaved : A'.saved_confirmation (s - 1) = some B)
    (hFast : B ∈ A'.fast_blocks) :
    LockEntry.mk B (C.t_ (s - 1 + C.k) + 5 * C.Δ) ∈ A'.lock_entries ∧ B ∈ Φ.tree := by
  simp only [update_confirmation] at hUpdate
  rw [if_neg hs] at hUpdate
  obtain ⟨early, -, h1⟩ := dre_bind_eq_ok hUpdate
  obtain ⟨late, -, h2⟩ := dre_bind_eq_ok h1
  obtain ⟨H, -, h3⟩ := dre_bind_eq_ok h2
  obtain ⟨b, -, h4⟩ := dre_bind_eq_ok h3
  cases b
  · rw [if_neg (by decide)] at h4
    split at h4
    case isTrue hne => exact absurd rfl hne
    case isFalse =>
      simp only [pure, Except.pure, Except.ok.injEq] at h4
      subst h4
      exact absurd hFast (Finset.notMem_empty B)
  rw [if_pos rfl] at h4
  split at h4
  case isFalse hne => exact absurd (Option.some_ne_none H) hne
  split at h4
  case isFalse =>
    simp only [pure, Except.pure, Except.ok.injEq] at h4
    subst h4
    exact absurd hFast (Finset.notMem_empty B)
  obtain ⟨fb, hfb, h5⟩ := dre_bind_eq_ok h4
  obtain ⟨lk, hlk, h6⟩ := dre_bind_eq_ok h5
  -- every block of the path is on the chain of `H`
  have hpath : ∀ L ∈ lk, L ∈ Φ.tree ∧ L.AncestorEq H := by
    intro L hL
    obtain ⟨hp, -⟩ := (mem_of_filterM_eq_ok_iff _ _ _ hlk L).1 hL
    simp only [Finset.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hp
    exact ⟨hp.1, hp.2.2⟩
  generalize hD : Block.deepest? lk = D at h6
  cases D with
  | none =>
    simp only [ne_eq, not_true_eq_false, dite_false, pure, Except.pure, Except.ok.injEq] at h6
    subst h6
    simp only [Function.update_self, Option.some.injEq] at hSaved
    subst hSaved
    -- `B` is fast, so it is lockable: no deepest lockable block is impossible
    exfalso
    obtain ⟨hp, hft⟩ := (mem_of_filterM_eq_ok_iff _ _ _ hfb H).1 hFast
    have hHlk : H ∈ lk := (mem_of_filterM_eq_ok_iff _ _ _ hlk H).2 ⟨hp, by
      simp only [hft]; rfl⟩
    have hD' := deepest?_eq_some hHlk
      (fun D hD' => depth_le_of_ancestorEq (hpath D hD').2)
      (fun D hD' hd => eq_of_ancestorEq_of_depth (hpath D hD').2 hd.ge)
    rw [hD] at hD'
    cases hD'
  | some D =>
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, dite_true, Option.value, Option.get_some,
      pure, Except.pure, Except.ok.injEq] at h6
    subst h6
    simp only [Function.update_self, Option.some.injEq] at hSaved
    subst hSaved
    obtain ⟨hp, hft⟩ := (mem_of_filterM_eq_ok_iff _ _ _ hfb H).1 hFast
    have hHlk : H ∈ lk := (mem_of_filterM_eq_ok_iff _ _ _ hlk H).2 ⟨hp, by
      simp only [hft]; rfl⟩
    have hD' := deepest?_eq_some hHlk
      (fun D hD' => depth_le_of_ancestorEq (hpath D hD').2)
      (fun D hD' hd => eq_of_ancestorEq_of_depth (hpath D hD').2 hd.ge)
    rw [hD] at hD'
    cases hD'
    exact ⟨Finset.mem_union_right _ (Finset.mem_singleton_self _), (hpath H hHlk).1⟩

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

/-- At slot `0` the confirmation update answers its input.

The variables:
- `C`, `P`: the parameters and the values; `A`: the AC state; `Φ`: the frame; `t`: the time. -/
theorem update_confirmation_zero [RootOrder] (C : Config) (P : Provisional V) (A : ACState V)
    (Φ : Frame V) (t : Time) : update_confirmation C P A Φ t 0 = .ok A := by
  simp only [update_confirmation]
  rfl

/-- Every answer of the confirmation update of slot `s` has the saved confirmation of its input at
every slot other than `s − 1`.

The variables:
- `C`, `P`: the parameters and the values; `A`: the AC state; `Φ`: the frame; `t`: the time;
  `s`: the slot of the update. -/
theorem update_confirmation_saved_ne [RootOrder] (C : Config) (P : Provisional V) (A : ACState V)
    (Φ : Frame V) (t : Time) (s : Slot) :
    DREPost (update_confirmation C P A Φ t s)
      (fun A' => ∀ j : Slot, j ≠ s - 1 → A'.saved_confirmation j = A.saved_confirmation j) := by
  simp only [update_confirmation]
  repeat' first
    | exact DREPost.pure (fun _ _ => rfl)
    | exact DREPost.pure (fun _ hj => Function.update_of_ne hj _ _)
    | refine DREPost.dite (fun _ => ?_) (fun _ => ?_)
    | refine DREPost.ite (fun _ => ?_) (fun _ => ?_)
    | refine DREPost.bind_any (fun _ => ?_)

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

section

variable [RootOrder]

/-- The confirmation update keeps "filed by slot, holding `A₀`'s votes and stamps, with `A₀`'s
block stamps, what it holds beyond `A₀` stamped `t₀`". -/
theorem update_confirmation_grows_from {P : Provisional V} {A₀ : ACState V} {t₀ : Time}
    (C : Config) (A : ACState V) (Φ : Frame V) (t : Time) (s : Slot)
    (h : SlotKeyed A ∧ ACGrows A₀ A ∧ A.timestamp_block = A₀.timestamp_block ∧
      ACStampsAt A₀ A t₀) :
    DREPost (update_confirmation C P A Φ t s)
      (fun A' => SlotKeyed A' ∧ ACGrows A₀ A' ∧ A'.timestamp_block = A₀.timestamp_block ∧
        ACStampsAt A₀ A' t₀) :=
  (update_confirmation_keepsVotes C P A Φ t s).mono
    (fun _ hk => ⟨h.1.of_keeps hk, h.2.1.trans (ACGrows.of_keeps hk), hk.2.2.trans h.2.2.1,
      h.2.2.2.trans (ACGrows.of_keeps hk) (ACStampsAt.of_keeps hk t₀)⟩)

end

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [Fintype V] [RootOrder] in
/-- Every opponent of `B'` has a vote among `votes` that opposes `B'`.

The variables:
- `A`: the AC state; `Φ`: the frame; `votes`, `equivocators`: the votes counted and the validators
  counted out; `B'`: the block opposed; `o`: the answer; `v`: the opponent. -/
theorem exists_vote_of_mem_opponents {A : ACState V} {Φ : Frame V}
    {votes : Finset (GoldfishVote V)} {equivocators : Finset V} {B' : Block V} {o : Finset V}
    (h : opponents A Φ votes equivocators B' = .ok o) {v : V} (hv : v ∈ o) :
    ∃ vote ∈ votes, vote.val_index = v ∧ opposes Φ B' vote = .ok true := by
  simp only [opponents] at h
  obtain ⟨opposing, hfilter, hret⟩ := dre_bind_eq_ok h
  cases hret
  simp only [Finset.map', Finset.mem_image] at hv
  obtain ⟨vote, hvote, rfl⟩ := hv
  rw [mem_of_filterM_eq_ok_iff _ _ _ hfilter] at hvote
  obtain ⟨hvs, hp⟩ := hvote
  obtain ⟨τ, -, hp1⟩ := dre_bind_eq_ok hp
  obtain ⟨b, hb, hp2⟩ := dre_bind_eq_ok hp1
  simp only [pure, Except.pure, Except.ok.injEq, Bool.and_eq_true] at hp2
  rw [hp2.2] at hb
  exact ⟨vote, hvs, rfl, hb⟩

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [Fintype V] in
/-- **Routine fact: the block an entry is moved to has fewer than half of the committee opposing
it.** The proof; the audited statement is in
`Statements/Executions/PeriodRevocationStatements.lean`.

The variables:
- `P`: the values; `A`: the AC state; `Φ`: the frame; `votes`, `equivocators`: the votes counted
  and the validators counted out; `s'`: the slot; `e`: the entry moved; `e'`: the entry
  answered. -/
theorem moved_entry_opponents_lt {P : Provisional V} {A : ACState V} {Φ : Frame V}
    {votes : Finset (GoldfishVote V)} {equivocators : Finset V} {s' : Slot}
    {e e' : LockEntry V}
    (h : moved_entry P A Φ votes equivocators s' e = .ok (some e')) :
    (∃ opp : Finset V, opponents A Φ votes equivocators e'.B = .ok opp ∧
      2 * |opp| < |P.committee (s' - 1)|) ∧
    e'.B ∈ Φ.tree ∧ e'.B.AncestorEq e.B ∧ e'.d = e.d := by
  simp only [moved_entry] at h
  obtain ⟨candidates, hfilter, hret⟩ := dre_bind_eq_ok h
  generalize hD : Block.deepest? candidates = D at hret
  cases D with
  | none => cases hret
  | some B' =>
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, dite_true, Option.value,
      Option.get_some] at hret
    cases hret
    have hmem := deepest?_mem hD
    rw [mem_of_filterM_eq_ok_iff _ _ _ hfilter] at hmem
    obtain ⟨hT, hp⟩ := hmem
    obtain ⟨o, ho, hret'⟩ := dre_bind_eq_ok hp
    simp only [pure, Except.pure, Except.ok.injEq, Bool.and_eq_true, decide_eq_true_eq] at hret'
    exact ⟨⟨o, ho, hret'.2⟩, hT, hret'.1.2, rfl⟩

end

section

open Goldilocks

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **Routine fact: every entry the revocation answers is opposed by fewer than half of the
committee.** When the revocation of slot `s ≠ 0` answers `A'`, every lock entry `e` of `A'` has
opponents among the votes of slot `s − 1` of `A`'s pool, the equivocators of that pool counted out,
and those opponents, counted twice, are fewer than the committee of slot `s − 1`.

The variables:
- `P`: the values; `A`, `A'`: the AC state before and after the revocation; `Φ`: the frame; `t`:
  the time; `s`: the slot of the revocation; `e`: the entry;
- `hs`: the slot is not `0`; `hRevoke`: the revocation answers `A'`; `he`: `e` is an entry of
  `A'`.

Read aloud: a lock entry left after the revocation of slot `s` is on a block fewer than half of
the committee of slot `s − 1` voted against. -/
theorem revoke_locks_entry_opponents_lt {P : Provisional V} {A A' : ACState V} {Φ : Frame V}
    {t : Time} {s : Slot} (hs : s ≠ 0) (hRevoke : revoke_locks P A Φ t s = .ok A')
    (e : LockEntry V) (he : e ∈ A'.lock_entries) :
    ∃ opp : Finset V,
      opponents A Φ (A.pool (s - 1)) (equivocators (A.pool (s - 1))) e.B = .ok opp ∧
        2 * |opp| < |P.committee (s - 1)| := by
  simp only [revoke_locks] at hRevoke
  rw [if_neg hs] at hRevoke
  obtain ⟨moved, hmoved, hret⟩ := dre_bind_eq_ok hRevoke
  cases hret
  have he' : some e ∈ moved := (present_mem_iff _ _).1 he
  obtain ⟨e₀, -, he₀⟩ := mem_of_imageM_eq_ok _ _ _ hmoved _ he'
  exact (moved_entry_opponents_lt he₀).1

end

end GoldilocksCorrectness.Proofs.Routines
