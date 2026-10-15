import Proofs.Instance.NoRaise.Predicates

/-!
# `Stamped` is kept by every writer of the store

For each routine that writes the store, a lemma saying that an answer keeps the store `Stamped`,
and, for the routines run inside the tick, keeps the clock, the slot and the saved grades (`Frame`);
and the same for the tick (`stamped_tick`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace SpecRecord.NoRaise

open Spec Spec.Protocol
open DC (DRE)

/-! ## The walkers, read backwards -/

/-- If `x >>= f` answers `b` in `DRE`, then `x` answers some `a` and `f a` answers `b`. -/
theorem DRE.ok_of_bind {α β : Type} {x : DRE α} {f : α → DRE β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- `x >>= f` run from `l` in `DREB` gives `b` exactly when `x` gives some `a` with a list `l'` and
    `f a` run from `l'` gives `b`. -/
theorem DREB.run_bind_ok_iff {V α β : Type} (x : DREB V α) (f : α → DREB V β)
    (l : List (NamedObject V)) (b : β × List (NamedObject V)) :
    (x >>= f).run l = .ok b ↔ ∃ a l', x.run l = .ok (a, l') ∧ (f a).run l' = .ok b := by
  rw [StateT.run_bind]
  cases hx : x.run l with
  | error e =>
    simp only [bind, Except.bind, reduceCtorEq, false_iff, not_exists, not_and]
    intro a l' h
    cases h
  | ok p =>
    obtain ⟨a, l'⟩ := p
    simp only [bind, Except.bind, Except.ok.injEq, Prod.mk.injEq]
    constructor
    · intro h
      exact ⟨a, l', ⟨rfl, rfl⟩, h⟩
    · rintro ⟨a', l'', ⟨rfl, rfl⟩, h⟩
      exact h

/-- A `DRE` routine lifted into `DREB` gives `a` with the list `l'` exactly when the routine answers
    `a` and `l'` is `l`. -/
theorem DREB.liftM_run_ok_iff {V α : Type} (x : DRE α) (l : List (NamedObject V)) (a : α)
    (l' : List (NamedObject V)) :
    ((liftM x : DREB V α).run l = .ok (a, l')) ↔ x = .ok a ∧ l' = l := by
  cases x with
  | error e =>
    constructor
    · intro h; cases h
    · rintro ⟨h, -⟩; cases h
  | ok b =>
    have : ((liftM (Except.ok b : DRE α) : DREB V α).run l) = .ok (b, l) := rfl
    rw [this]
    simp only [Except.ok.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩
    · rintro ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩

/-- `pure a` run in `DREB` from `l` gives exactly `(a, l)`. -/
theorem DREB.pure_run_ok_iff {V α : Type} (a : α) (l : List (NamedObject V))
    (b : α × List (NamedObject V)) :
    ((pure a : DREB V α).run l = .ok b) ↔ b = (a, l) := by
  have : ((pure a : DREB V α).run l) = .ok (a, l) := rfl
  rw [this]
  simp only [Except.ok.injEq]
  exact eq_comm

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The frame -/

/-- The store `st'` has the clock, the slot and the saved grades of `st`, and is `Stamped` when `st`
    is. -/
def Frame (st st' : Store V) : Prop :=
  (Stamped st → Stamped st') ∧ st'.t = st.t ∧ st'.s = st.s ∧ st'.saved_grades = st.saved_grades

/-- Every store is its own frame. -/
theorem Frame.refl (st : Store V) : Frame st st := ⟨id, rfl, rfl, rfl⟩

/-- Frames compose. -/
theorem Frame.trans {st st' st'' : Store V} (h : Frame st st') (h' : Frame st' st'') :
    Frame st st'' :=
  ⟨fun hs => h'.1 (h.1 hs), h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1,
    h'.2.2.2.trans h.2.2.2⟩

/-- A fold over a list by a step that is a frame is a frame. -/
theorem Frame.foldl {α : Type} (f : Store V → α → Store V) (hf : ∀ st a, Frame st (f st a)) :
    ∀ (l : List α) (st : Store V), Frame st (l.foldl f st)
  | [], st => Frame.refl st
  | a :: l, st => (hf st a).trans (Frame.foldl f hf l (f st a))

/-- `Function.update f a (some b)` is not `none` at `x` when `f x` is not `none` for `x ≠ a`. -/
theorem update_ne_none {α β : Type} [DecidableEq α] {f : α → Option β} {a x : α} {b : β}
    (h : x ≠ a → f x ≠ none) : Function.update f a (some b) x ≠ none := by
  by_cases hx : x = a
  · subst hx; simp
  · rw [Function.update_of_ne hx]; exact h hx

/-- A member of `l` updated at the index `i` by appending `y` to `l i` is `y` or a member of `l j`. -/
theorem mem_update_append {ι α : Type} [DecidableEq ι] {l : ι → List α} {i j : ι} {x y : α}
    (h : x ∈ Function.update l i (l i ++ [y]) j) : x = y ∨ x ∈ l j := by
  by_cases hj : j = i
  · subst hj
    rw [Function.update_self, List.mem_append, List.mem_singleton] at h
    exact h.symm
  · rw [Function.update_of_ne hj] at h
    exact Or.inr h

/-! ## The initial store -/

/-- The initial store is stamped. -/
theorem stamped_init : Stamped (Store.init : Store V) := by
  refine ⟨?_, ?_, ?_⟩
  · intro B hB
    simp only [Store.init, Finset.mem_singleton] at hB
    subst hB
    simp [Store.init]
  · intro s u hu
    simp [Store.init] at hu
  · intro r a ha
    simp [Store.init] at ha

/-! ## The writers -/

/-- `add_attestation` is a frame. -/
theorem frame_add_attestation (st : Store V) (a : Attestation V) :
    Frame st (add_attestation st a) := by
  refine ⟨?_, rfl, rfl, rfl⟩
  rintro ⟨h1, h2, h3⟩
  refine ⟨h1, h2, ?_⟩
  intro r b hb
  apply update_ne_none
  intro hne
  rcases mem_update_append (l := st.attestations) hb with rfl | hb
  · exact absurd rfl hne
  · exact h3 r b hb

/-- `admit_attestation` is a frame. -/
theorem frame_admit_attestation (C : Config) (st : Store V) (a : Attestation V) :
    Frame st (admit_attestation C st a) := by
  simp only [admit_attestation, Id.run]
  split_ifs
  · exact frame_add_attestation st a
  · exact Frame.refl st

/-- `admit_attestations` is a frame. -/
theorem frame_admit_attestations (C : Config) (st : Store V) (l : List (Attestation V)) :
    Frame st (admit_attestations C st l) := by
  have : admit_attestations C st l = l.foldl (admit_attestation C) st := by
    simp only [admit_attestations, Id.run, List.forIn_pure_yield_eq_foldl]
    rfl
  rw [this]
  exact Frame.foldl _ (frame_admit_attestation C) l st

/-- `on_goldfish_vote` is a frame. -/
theorem frame_on_goldfish_vote (st : Store V) (u : GoldfishVote V) :
    Frame st (on_goldfish_vote st u) := by
  simp only [on_goldfish_vote, Id.run]
  split_ifs
  · exact Frame.refl st
  · exact Frame.refl st
  · refine ⟨?_, rfl, rfl, rfl⟩
    rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ?_, h3⟩
    intro s w hw
    apply update_ne_none
    intro hne
    rcases mem_update_append (l := st.gf_votes) hw with rfl | hw
    · exact absurd rfl hne
    · exact h2 s w hw

/-- `on_goldfish_vote_checked` is a frame. -/
theorem frame_on_goldfish_vote_checked (P : Provisional V) (st : Store V)
    (u : GoldfishVote V) : Frame st (on_goldfish_vote_checked P st u) := by
  simp only [on_goldfish_vote_checked, Id.run]
  split_ifs <;> first | exact Frame.refl st | exact frame_on_goldfish_vote st u

/-- `update_finality` is a frame. -/
theorem frame_update_finality (st : Store V) (B : Block V) :
    Frame st (update_finality st B) := by
  simp only [update_finality, Id.run]
  split_ifs <;> exact Frame.refl st

/-- `add_block` is a frame. -/
theorem frame_add_block (C : Config) (P : Provisional V) (st : Store V) (B : Block V) :
    Frame st (add_block C P st B) := by
  have heq : add_block C P st B = admit_attestations C (update_finality (B.gf_votes.foldl
      (on_goldfish_vote_checked P)
      { st with σ := Function.update st.σ B (state_transition C P (st.σ B.parent) B),
                T := st.T ∪ {B},
                timestamp_block := Function.update st.timestamp_block B (some (st.t : Stamp)) })
      B) B.attestations := by
    simp only [add_block, Id.run, List.forIn_pure_yield_eq_foldl]
    rfl
  rw [heq]
  refine Frame.trans ?_ ((Frame.foldl _ (frame_on_goldfish_vote_checked P) _ _).trans
    ((frame_update_finality _ B).trans (frame_admit_attestations C _ _)))
  refine ⟨?_, rfl, rfl, rfl⟩
  rintro ⟨h1, h2, h3⟩
  refine ⟨?_, h2, h3⟩
  intro B' hB'
  apply update_ne_none
  intro hne
  rcases Finset.mem_union.mp hB' with hB' | hB'
  · exact h1 B' hB'
  · exact absurd (Finset.mem_singleton.mp hB') hne

/-- `on_block` is a frame. -/
theorem frame_on_block (C : Config) (P : Provisional V) (st : Store V) (B : Block V) :
    Frame st (on_block C P st B) := by
  simp only [on_block, Id.run]
  split_ifs
  · exact frame_add_block C P st B
  · exact Frame.refl st

/-! ## The grade and confirmation writers -/

/-- An answer of `update_grades` is the store with only its saved grades replaced. -/
theorem update_grades_eq {C : Config} {P : Provisional V} {st st' : Store V} {t : Time}
    (h : update_grades C P st t = .ok st') :
    st' = { st with saved_grades := st'.saved_grades } := by
  simp only [update_grades] at h
  repeat' (first
    | (split_ifs at h)
    | (obtain ⟨_, -, h⟩ := DRE.ok_of_bind h; try dsimp only at h))
  all_goals
    have h' := h
    simp only [pure, Except.pure, Except.ok.injEq] at h'
    subst h'
    rfl

/-- An answer of `update_confirmation` is the store with only `live_confirmed`, `latest_stable` and
    `latest_confirmed` replaced. -/
theorem update_confirmation_eq {C : Config} {st st' : Store V} {s : Slot}
    (h : update_confirmation C st s = .ok st') :
    st' = { st with live_confirmed := st'.live_confirmed, latest_stable := st'.latest_stable,
                    latest_confirmed := st'.latest_confirmed } := by
  simp only [update_confirmation] at h
  repeat' (first
    | (split_ifs at h)
    | (obtain ⟨_, -, h⟩ := DRE.ok_of_bind h; try dsimp only at h))
  all_goals
    have h' := h
    simp only [pure, Except.pure, Except.ok.injEq] at h'
    subst h'
    rfl

/-- `update_grades` keeps the store stamped. -/
theorem stamped_update_grades {C : Config} {P : Provisional V} {st st' : Store V} {t : Time}
    (h : update_grades C P st t = .ok st') (hs : Stamped st) : Stamped st' := by
  rw [update_grades_eq h]
  exact hs

/-- `make_grades_compatible_with_finalized` keeps the store stamped. -/
theorem stamped_make_grades_compatible_with_finalized {st : Store V} (hs : Stamped st) :
    Stamped (make_grades_compatible_with_finalized st) := hs

/-! ## The duties' outcomes -/

/-- An answer of the proposal duty `propose_block` is a frame of its input store. -/
theorem frame_propose_block {C : Config} {P : Provisional V} {X : External V} {v : V}
    {st : Store V} {l : List (NamedObject V)} {out : Store V × List (NamedObject V)}
    (h : (propose_block C P X v st).run l = .ok out) : Frame st out.1 := by
  unfold propose_block at h
  cases hb : build_proposal C X v st with
  | error e => rw [hb] at h; cases h
  | ok B =>
    rw [hb] at h
    have h2 : (Except.ok (on_block C P st B, l ++ [NamedObject.block B]) :
        DRE (Store V × List (NamedObject V))) = Except.ok out := h
    cases h2
    exact frame_on_block C P st B

/-- An answer of the Goldfish vote duty `goldfish_vote` is a frame of its input store. -/
theorem frame_goldfish_vote {C : Config} {P : Provisional V} {v : V} {st : Store V}
    {l : List (NamedObject V)} {out : Store V × List (NamedObject V)}
    (h : (goldfish_vote C P v st).run l = .ok out) : Frame st out.1 := by
  unfold goldfish_vote at h
  dsimp only at h
  rw [DREB.run_bind_ok_iff] at h
  obtain ⟨_, _, -, h⟩ := h
  rw [DREB.run_bind_ok_iff] at h
  obtain ⟨_, _, -, h⟩ := h
  rw [DREB.run_bind_ok_iff] at h
  obtain ⟨_, _, -, h⟩ := h
  rw [DREB.run_bind_ok_iff] at h
  obtain ⟨H, _, -, h⟩ := h
  split_ifs at h
  · rw [DREB.run_bind_ok_iff] at h
    obtain ⟨_, _, -, h⟩ := h
    rw [DREB.pure_run_ok_iff] at h
    subst h
    exact frame_on_goldfish_vote_checked P st _
  · rw [DREB.pure_run_ok_iff] at h
    subst h
    exact Frame.refl st

/-- An answer of `update_confirmation` is a frame of its input store. -/
theorem frame_update_confirmation {C : Config} {st st' : Store V} {s : Slot}
    (h : update_confirmation C st s = .ok st') : Frame st st' := by
  rw [update_confirmation_eq h]
  exact ⟨id, rfl, rfl, rfl⟩

/-- An answer of the attestation duty `attest` is a frame of its input store. -/
theorem frame_attest {C : Config} {v : V} {st : Store V} {sh : SigningHistory}
    {l : List (NamedObject V)} {out : (Store V × SigningHistory) × List (NamedObject V)}
    (h : (attest C v st sh).run l = .ok out) : Frame st out.1.1 := by
  unfold attest at h
  dsimp only at h
  cases hb : build_attestation C v st sh with
  | error e => rw [hb] at h; cases h
  | ok p =>
    rw [hb] at h
    have h2 : (Except.ok ((admit_attestation C st p.2, p.1), l ++ [NamedObject.attest p.2]) :
        DRE ((Store V × SigningHistory) × List (NamedObject V))) = Except.ok out := h
    cases h2
    exact frame_admit_attestation C st p.2

/-! ## The tick -/

/-- Run `f` on `a` when `c` holds, and return `a` otherwise. -/
def optStep {α : Type} (c : Prop) [Decidable c] (f : α → DREB V α) (a : α) : DREB V α :=
  if c then f a else pure a

/-- The spec's tick written as a chain of binds, one per step: record the wake, update the grades,
    set the clock and the slot, run the four duties each as an `optStep` behind its condition, then
    apply `make_grades_compatible_with_finalized`. -/
def tickSteps (C : Config) (P : Provisional V) (X : External V) (n : NodeState V) (t : Time) :
    DREB V (NodeState V) := do
  let n0 := record_awake n t
  let st0 ← liftM (update_grades C P n0.st t)
  let st1 : Store V := { st0 with t := t, s := C.slotOf t }
  let s := C.slotOf t
  let r := C.round_of s
  let st4 ← optStep (s > 0) (fun st1 => do
      let st2 ← optStep ((decide (t = C.proposal_time s) && decide (P.proposer s = n0.v) &&
          n0.awake_since (grade1_window_start C r)) = true)
          (propose_block C P X n0.v) st1
      let st3 ← optStep ((decide (t = C.vote_time s) &&
          n0.awake_since (grade1_window_start C r)) = true)
          (goldfish_vote C P n0.v) st2
      optStep ((decide (t = C.gf_confirmation_time s) &&
          n0.awake_since (grade2_window_start C r)) = true)
          (fun st => liftM (update_confirmation C st (s - 1))) st3) st1
  let p ← optStep ((decide (t = C.round_attestation_time r) &&
      n0.awake_since (grade2_window_start C r)) = true)
      (fun p => attest C n0.v p.1 p.2) (st4, n0.signingHistory)
  pure { v := n0.v, st := make_grades_compatible_with_finalized p.1,
         signingHistory := p.2, awakeSince := n0.awakeSince }

/-- The spec's tick is `tickSteps`. -/
theorem tick_eq_tickSteps (C : Config) (P : Provisional V) (X : External V) (n : NodeState V)
    (t : Time) : tick C P X n t = tickSteps C P X n t := by
  simp only [tick, tickSteps, optStep]
  split_ifs <;> simp only [bind_assoc, pure_bind]

/-- `record_awake` writes only `awakeSince`. -/
theorem record_awake_eq (n : NodeState V) (t : Time) :
    record_awake n t = { n with awakeSince := (record_awake n t).awakeSince } := by
  simp only [record_awake, Id.run]
  split_ifs <;> rfl

/-- An answer of an `optStep` whose step is a frame on `g` is a frame on `g`. -/
theorem frame_optStep {α : Type} (c : Prop) [Decidable c] (f : α → DREB V α)
    (g : α → Store V) {a : α} {l : List (NamedObject V)} {out : α × List (NamedObject V)}
    (hf : ∀ l out, (f a).run l = .ok out → Frame (g a) (g out.1))
    (h : (optStep c f a).run l = .ok out) : Frame (g a) (g out.1) := by
  unfold optStep at h
  split_ifs at h
  · exact hf l out h
  · rw [DREB.pure_run_ok_iff] at h
    subst h
    exact Frame.refl _

/-- An answer of the tick's three slot duties, the proposal, the Goldfish vote and the confirmation,
    each behind its condition, is a frame of the store they start from. -/
theorem frame_slot_duties {C : Config} {P : Provisional V} {X : External V} {v : V} {s : Slot}
    {c1 c2 c3 : Prop} [Decidable c1] [Decidable c2] [Decidable c3] {st : Store V}
    {l : List (NamedObject V)} {out : Store V × List (NamedObject V)}
    (h : (do
      let st2 ← optStep c1 (propose_block C P X v) st
      let st3 ← optStep c2 (goldfish_vote C P v) st2
      optStep c3 (fun st => liftM (update_confirmation C st (s - 1))) st3 :
        DREB V (Store V)).run l = .ok out) : Frame st out.1 := by
  rw [DREB.run_bind_ok_iff] at h
  obtain ⟨st2, l1, h1, h⟩ := h
  rw [DREB.run_bind_ok_iff] at h
  obtain ⟨st3, l2, h2, h⟩ := h
  have f1 := frame_optStep _ _ id (fun _ _ hr => frame_propose_block hr) h1
  have f2 := frame_optStep _ _ id (fun _ _ hr => frame_goldfish_vote hr) h2
  have f3 := frame_optStep _ _ id (fun l out hr => by
    obtain ⟨out1, out2⟩ := out
    rw [DREB.liftM_run_ok_iff] at hr
    exact frame_update_confirmation hr.1) h
  exact f1.trans (f2.trans f3)

/-- An answer of the tick at `t` is made of: the grades update's answer `st0` on the store of
    `record_awake n t`; the four duties taking `st0`, with the clock `t` and the slot `C.slotOf t`,
    to a frame `st5` of it; and `make_grades_compatible_with_finalized st5` as the answer's store,
    its validator and `awakeSince` those of `record_awake n t`. -/
theorem tick_outcome {C : Config} {P : Provisional V} {X : External V} {n : NodeState V}
    {t : Time} {out : NodeState V × List (NamedObject V)}
    (h : (tick C P X n t).run [] = .ok out) :
    ∃ st0 st5 : Store V, update_grades C P (record_awake n t).st t = .ok st0 ∧
      Frame { st0 with t := t, s := C.slotOf t } st5 ∧
      out.1.st = make_grades_compatible_with_finalized st5 ∧
      out.1.awakeSince = (record_awake n t).awakeSince ∧ out.1.v = n.v := by
  rw [tick_eq_tickSteps] at h
  unfold tickSteps at h
  dsimp only at h
  rw [DREB.run_bind_ok_iff] at h
  obtain ⟨st0, l0, h0, h⟩ := h
  rw [DREB.liftM_run_ok_iff] at h0
  obtain ⟨h0, rfl⟩ := h0
  rw [DREB.run_bind_ok_iff] at h
  obtain ⟨st4, l3, h3, h⟩ := h
  rw [DREB.run_bind_ok_iff] at h
  obtain ⟨p, l4, h4, h⟩ := h
  rw [DREB.pure_run_ok_iff] at h
  subst h
  have f3 := frame_optStep _ _ id (fun _ _ hr => frame_slot_duties hr) h3
  have f4 := frame_optStep _ _ Prod.fst (fun _ _ hr => frame_attest hr) h4
  refine ⟨st0, p.1, h0, f3.trans f4, rfl, rfl, ?_⟩
  rw [record_awake_eq]

/-- If the tick answers from a node state whose store is stamped, the answer's store is stamped. -/
theorem stamped_tick {C : Config} {P : Provisional V} {X : External V} {n : NodeState V}
    {t : Time} {out : NodeState V × List (NamedObject V)}
    (h : (tick C P X n t).run [] = .ok out) (hs : Stamped n.st) : Stamped out.1.st := by
  obtain ⟨st0, st5, h0, hf, hst, -, -⟩ := tick_outcome h
  rw [hst]
  have hs0 : Stamped st0 := by
    rw [record_awake_eq] at h0
    exact stamped_update_grades h0 hs
  exact stamped_make_grades_compatible_with_finalized (hf.1 hs0)

end SpecRecord.NoRaise
