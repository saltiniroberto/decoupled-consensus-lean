import Proofs.Instance.Facts.Node
import Proofs.Instance.NoRaise.Schedule
import Proofs.Instance.Equalities.Fill
import Proofs.Instance.Facts.Grades
import Proofs.Instance.Equalities.ContractImages

/-!
# Node facts at `Model.spec`: the frame facts, the tick and the confirmation invariants

Proofs of fields of `NodeFacts` at `Model.spec`: the frame facts that hold by computation, the
tick's steps with their conditions, and the confirmation-membership invariants
`spec_initial_invariants`, `spec_invariants_process` and
`spec_confirmation_invariant_tick`.
-/

set_option autoImplicit false

namespace SpecRecord.NodeFacts

open DecoupledConsensusModel DecoupledConsensusModel.Execution DecoupledConsensusModel.Sts
open DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-! ## The frame facts, the contract reads, and the receipt's store -/

/-- When the node's receipt of `o` on `n` returns `n'`, the store type's receipt of `o` on `n`'s
    store is the spec's receipt. -/
theorem okReceipt_val_of_process (S : Setup V) (n : (Model.spec (V := V)).N)
    (o : NamedObject V) (n' : (Model.spec (V := V)).N)
    (hn' : (Model.spec (V := V)).process S n o ⇢ n') :
    (OkMember.receipt_process S n.st o).val = Member.receipt_process S n.val.st o := by
  by_cases h : objectRootHeldByOther n.val.st.T o
  · rw [OkMember.receipt_process_of_held h]
    cases o with
    | block B =>
      have hd : NoRaise.DistinctRoots (Member.receipt_process S n.val.st (.block B)).T := by
        have h2 := n'.property.2.1
        rw [process_val_st S n _ n' hn'] at h2
        exact h2
      rcases SubtypeEqualities.on_block_cases_of_ok _ _ hd with he | hn
      · exact he.symm
      · exact absurd h hn
    | gfVote u => exact h.elim
    | attest a => exact h.elim
  · exact OkMember.receipt_process_val_of_not_held h

/-- The field `wake_cache` of `NodeFacts` at `Model.spec`: the grade cache of `M.wake n` is the
    grade cache of `n`. -/
theorem spec_wake_cache :
    ∀ n : (Model.spec (V := V)).N, ((Model.spec (V := V)).wake n).cache = n.cache := by
  intros; rfl

/-- The field `wake_events_or_id` of `NodeFacts` at `Model.spec`: the member `wakeEvents` is
    `true`. -/
theorem spec_wake_events_or_id :
    (Model.spec (V := V)).wakeEvents = true ∨ ∀ n : (Model.spec (V := V)).N, (Model.spec (V := V)).wake n = n :=
  Or.inl rfl

/-- The field `wake_idem` of `NodeFacts` at `Model.spec`: waking a node state twice gives the
    node state that waking it once gives. -/
theorem spec_wake_idem :
    ∀ n : (Model.spec (V := V)).N, (Model.spec (V := V)).wake ((Model.spec (V := V)).wake n) = (Model.spec (V := V)).wake n := by
  intros; rfl

/-- The field `store_with_cache_bodies` of `NodeFacts` at `Model.spec`: the bodies of
    `M.store_with_cache st c` are the bodies of `st`. -/
theorem spec_store_with_cache_bodies :
    ∀ (st : (Model.spec (V := V)).NS) (c : (Model.spec (V := V)).Cache),
        ((Model.spec (V := V)).store_with_cache st c).bodies = st.bodies := by
  intros; rfl

/-- The field `store_with_cache_sg_rows` of `NodeFacts` at `Model.spec`: the rows of round `r`
    of `M.store_with_cache st c` are those of `st`. -/
theorem spec_store_with_cache_sg_rows :
    ∀ (st : (Model.spec (V := V)).NS) (c : (Model.spec (V := V)).Cache) (r : Round),
        ((Model.spec (V := V)).store_with_cache st c).sg_rows r = st.sg_rows r := by
  intros; rfl

/-- The field `make_grades_compatible_with_finalized_bodies` of `NodeFacts` at `Model.spec`:
    making the saved grades compatible with the finalized block keeps the bodies. -/
theorem spec_make_grades_compatible_with_finalized_bodies :
    ∀ (ns : (Model.spec (V := V)).NS),
        ((Model.spec (V := V)).make_grades_compatible_with_finalized ns).bodies = ns.bodies := by
  intros; rfl

/-- The field `make_grades_compatible_with_finalized_sg_rows` of `NodeFacts` at `Model.spec`:
    making the saved grades compatible with the finalized block keeps the attestation rows. -/
theorem spec_make_grades_compatible_with_finalized_sg_rows :
    ∀ (ns : (Model.spec (V := V)).NS),
        ((Model.spec (V := V)).make_grades_compatible_with_finalized ns).sg_rows = ns.sg_rows := by
  intros; rfl

/-- The field `make_grades_compatible_with_finalized_core_t` of `NodeFacts` at `Model.spec`:
    making the saved grades compatible with the finalized block keeps the store's clock. -/
theorem spec_make_grades_compatible_with_finalized_core_t :
    ∀ (ns : (Model.spec (V := V)).NS),
        ((Model.spec (V := V)).make_grades_compatible_with_finalized ns).core.t = ns.core.t := by
  intros; rfl

/-- The field `make_grades_compatible_with_finalized_core_s` of `NodeFacts` at `Model.spec`:
    making the saved grades compatible with the finalized block keeps the store's slot. -/
theorem spec_make_grades_compatible_with_finalized_core_s :
    ∀ (ns : (Model.spec (V := V)).NS),
        ((Model.spec (V := V)).make_grades_compatible_with_finalized ns).core.s = ns.core.s := by
  intros; rfl

/-- The field `make_grades_compatible_with_finalized_core_T` of `NodeFacts` at `Model.spec`:
    making the saved grades compatible with the finalized block keeps the block tree. -/
theorem spec_make_grades_compatible_with_finalized_core_T :
    ∀ (ns : (Model.spec (V := V)).NS),
        ((Model.spec (V := V)).make_grades_compatible_with_finalized ns).core.T = ns.core.T := by
  intros; rfl

/-- The field `make_grades_compatible_with_finalized_core_F` of `NodeFacts` at `Model.spec`:
    making the saved grades compatible with the finalized block keeps the finalized block. -/
theorem spec_make_grades_compatible_with_finalized_core_F :
    ∀ (ns : (Model.spec (V := V)).NS),
        ((Model.spec (V := V)).make_grades_compatible_with_finalized ns).core.F = ns.core.F := by
  intros; rfl

/-- The field `make_grades_compatible_with_finalized_core_gf_votes` of `NodeFacts` at
    `Model.spec`: making the saved grades compatible with the finalized block keeps the
    Goldfish votes. -/
theorem spec_make_grades_compatible_with_finalized_core_gf_votes :
    ∀ (ns : (Model.spec (V := V)).NS),
        ((Model.spec (V := V)).make_grades_compatible_with_finalized ns).core.gf_votes = ns.core.gf_votes := by
  intros; rfl

/-- The field `make_grades_compatible_with_finalized_core_timestamp_vote` of `NodeFacts` at
    `Model.spec`: making the saved grades compatible with the finalized block keeps the
    Goldfish vote stamps. -/
theorem spec_make_grades_compatible_with_finalized_core_timestamp_vote :
    ∀ (ns : (Model.spec (V := V)).NS),
        ((Model.spec (V := V)).make_grades_compatible_with_finalized ns).core.timestamp_vote = ns.core.timestamp_vote := by
  intros; rfl

/-- The field `make_grades_compatible_with_finalized_core_timestamp_sg_vote` of `NodeFacts` at
    `Model.spec`: making the saved grades compatible with the finalized block keeps the SG vote
    stamps. -/
theorem spec_make_grades_compatible_with_finalized_core_timestamp_sg_vote :
    ∀ (ns : (Model.spec (V := V)).NS),
        ((Model.spec (V := V)).make_grades_compatible_with_finalized ns).core.timestamp_sg_vote = ns.core.timestamp_sg_vote := by
  intros; rfl

/-- The field `make_grades_compatible_with_finalized_core_pool` of `NodeFacts` at `Model.spec`:
    making the saved grades compatible with the finalized block keeps the Goldfish vote pool. -/
theorem spec_make_grades_compatible_with_finalized_core_pool :
    ∀ (ns : (Model.spec (V := V)).NS),
        ((Model.spec (V := V)).make_grades_compatible_with_finalized ns).core.pool = ns.core.pool := by
  intros; rfl

/-- The field `make_grades_compatible_with_finalized_core_round_votes` of `NodeFacts` at
    `Model.spec`: making the saved grades compatible with the finalized block keeps the round
    votes. -/
theorem spec_make_grades_compatible_with_finalized_core_round_votes :
    ∀ (ns : (Model.spec (V := V)).NS),
        (Model.spec (V := V)).round_votes ((Model.spec (V := V)).make_grades_compatible_with_finalized ns).core = (Model.spec (V := V)).round_votes ns.core := by
  intros; rfl

/-- The field `initial_setupWithGST` of `NodeFacts` at `Model.spec`: replacing the setup's GST
    does not change any validator's initial node state. -/
theorem spec_initial_setupWithGST :
    ∀ (S : DecoupledConsensusModel.Execution.Setup V) (g : ℤ) (hg : 0 ≤ g) (v : V), (Model.spec (V := V)).initial (DecoupledConsensusModel.Sts.setupWithGST S g hg) v = (Model.spec (V := V)).initial S v := by
  intros; rfl

/-- The field `process_st` of `NodeFacts` at `Model.spec`: the store of a node state `n'` that
    `n`'s receipt of `o` returns is the store `M.receipt_process` returns on `n`'s store and `o`,
    with its saved grades made compatible with its finalized block. -/
theorem spec_process_st :
    ∀ (S : Setup V) (n : (Model.spec (V := V)).N) (o : NamedObject V) (n' : (Model.spec (V := V)).N)
        (hn' : (Model.spec (V := V)).process S n o ⇢ n'),
        n'.st = (Model.spec (V := V)).make_grades_compatible_with_finalized ((Model.spec (V := V)).receipt_process S n.st o) := by
  intro S n o n' hn'
  apply Subtype.ext
  show n'.val.st = Spec.make_grades_compatible_with_finalized
    (OkMember.receipt_process S n.st o).val
  rw [okReceipt_val_of_process S n o n' hn', process_val_st S n o n' hn']

/-- The field `wake_cache_clipped` of `NodeFacts` at `Model.spec`: if `n`'s grade cache is
    unchanged by clipping at its finalized block, so is the grade cache of `M.wake n`. -/
theorem spec_wake_cache_clipped :
    ∀ n : (Model.spec (V := V)).N,
        (Model.spec (V := V)).clipCache n.st.core.F n.cache = n.cache →
        (Model.spec (V := V)).clipCache ((Model.spec (V := V)).wake n).st.core.F ((Model.spec (V := V)).wake n).cache = ((Model.spec (V := V)).wake n).cache := by
  intro n h
  exact h

/-- The field `gradeContract_eq_frameContract` of `NodeFacts` at `Model.spec`: for every cache
    `c`, `M.gradeContract c` is `M.frameContract c`. -/
theorem spec_gradeContract_eq_frameContract :
    ∀ (c : (Model.spec (V := V)).Cache), (Model.spec (V := V)).gradeContract c = (Model.spec (V := V)).frameContract c := by
  intros; rfl

/-- The field `gradeContract_read` of `NodeFacts` at `Model.spec`: the grade read of the
    contract built from `c` can return `g` exactly when the frame grade read of `c` can. -/
theorem spec_gradeContract_read :
    ∀ (c : (Model.spec (V := V)).Cache) (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig) (st : (Model.spec (V := V)).HS) (r : DecoupledConsensusModel.Round)
        (g : DecoupledConsensusModel.Protocol.GradeRead V), ((Model.spec (V := V)).gradeContract c).read E hc st r ⇢ g ↔ (Model.spec (V := V)).frameGradeRead c E hc st r ⇢ g := by
  intros; exact Iff.rfl

/-- The field `gradeContract_stableRoot` of `NodeFacts` at `Model.spec`: the stable root of the
    grade contract at `c` can return `x` exactly when `M.frameStableRoot c` can. -/
theorem spec_gradeContract_stableRoot :
    ∀ (c : (Model.spec (V := V)).Cache) (E : Env V) (hc : Protocol.HealConfig) (st : (Model.spec (V := V)).HS)
        (r : Round) (x : Option (Block V)),
        ((Model.spec (V := V)).gradeContract c).stableRoot E hc st r ⇢ x ↔ (Model.spec (V := V)).frameStableRoot c E hc st r ⇢ x := by
  intros; exact Iff.rfl

/-- The field `gradeContract_confirmationSG` of `NodeFacts` at `Model.spec`: the SG candidate
    selection of the grade contract at `c` can return `x` exactly when
    `M.frameSGCandidate c E hc st s` can. -/
theorem spec_gradeContract_confirmationSG :
    ∀ (c : (Model.spec (V := V)).Cache) (E : Env V) (hc : Protocol.HealConfig) (st : (Model.spec (V := V)).HS)
        (s : Slot) (x : Option (Block V)),
        ((Model.spec (V := V)).gradeContract c).confirmationSG E hc st s ⇢ x ↔ (Model.spec (V := V)).frameSGCandidate c E hc st s ⇢ x := by
  intros; exact Iff.rfl

/-! ## The tick, step by step with its conditions -/

omit [DecidableEq V] [Fintype V] [Inhabited V] in
/-- `record_awake` keeps the validator. -/
theorem record_awake_v (n : Spec.NodeState V) (t : Spec.Time) :
    (Spec.record_awake n t).v = n.v := by
  unfold Spec.record_awake; simp only [Id.run]; split_ifs <;> rfl

omit [DecidableEq V] [Fintype V] [Inhabited V] in
/-- `record_awake` keeps the store. -/
theorem record_awake_st (n : Spec.NodeState V) (t : Spec.Time) :
    (Spec.record_awake n t).st = n.st := by
  unfold Spec.record_awake; simp only [Id.run]; split_ifs <;> rfl

omit [DecidableEq V] [Fintype V] [Inhabited V] in
/-- `record_awake` keeps the signing history. -/
theorem record_awake_sh (n : Spec.NodeState V) (t : Spec.Time) :
    (Spec.record_awake n t).signingHistory = n.signingHistory := by
  unfold Spec.record_awake; simp only [Id.run]; split_ifs <;> rfl

omit [DecidableEq V] [Fintype V] [Inhabited V] in
/-- The wake test after `record_awake` passes at `x` exactly when `n` has been awake since some
    `a ≤ x`, or `n.awakeSince` is `none` and `t ≤ x`. -/
theorem record_awake_awake_since (n : Spec.NodeState V) (t x : Spec.Time) :
    (Spec.record_awake n t).awake_since x = true ↔
      (∃ a, n.awakeSince = some a ∧ a ≤ x) ∨ (n.awakeSince = none ∧ t ≤ x) := by
  have hp : ∀ {α : Type} (y : α), (pure y : Id α) = y := fun _ => rfl
  cases h : n.awakeSince with
  | none =>
    simp only [Spec.record_awake, Spec.NodeState.awake_since, Id.run, h,
      if_true, ne_eq, reduceCtorEq, not_false_eq_true, Option.value, hp]
    simp
  | some a =>
    simp only [Spec.record_awake, Spec.NodeState.awake_since, Id.run, h,
      ne_eq, reduceCtorEq, not_false_eq_true, if_true, if_false, Option.value, hp]
    simp [h]

omit [Inhabited V] in
/-- If the Goldfish vote duty answers, its store is the input store or the store after a vote it
    sent is admitted, that vote signed by a member of the committee of the store's slot. -/
theorem goldfish_vote_run_signed {C : Spec.Config} {P : Spec.Provisional V}
    {v : V} {st st' : Spec.Store V} {l l' : List (Spec.NamedObject V)}
    (h : (Spec.Protocol.goldfish_vote C P v st).run l = .ok (st', l')) :
    (st' = st ∧ l' = l) ∨ ∃ u : Spec.GoldfishVote V,
      st' = Spec.Protocol.on_goldfish_vote_checked P st u ∧
        l' = l ++ [Spec.NamedObject.gfVote u] ∧
        u.val_index ∈ P.committee u.slot ∧ u.slot = st.s := by
  unfold Spec.Protocol.goldfish_vote at h
  dsimp only at h
  cases h1 : Spec.Protocol.voter_view C st st.s with
  | error e => rw [h1] at h; cases h
  | ok votes =>
  simp only [h1, liftM_ok_bind] at h
  cases h2 : Spec.Protocol.voter_support_view C st st.s with
  | error e => rw [h2] at h; cases h
  | ok sv =>
  simp only [h2, liftM_ok_bind] at h
  cases h3 : Spec.Protocol.voter_filtered_block_tree C st st.s with
  | error e => rw [h3] at h; cases h
  | ok tree =>
  simp only [h3, liftM_ok_bind] at h
  cases h4 : Spec.Protocol.get_head_in_tree_with_layer C st tree votes sv (st.s - 1) with
  | error e => rw [h4] at h; cases h
  | ok H =>
  simp only [h4, liftM_ok_bind] at h
  by_cases hc : v ∈ P.committee st.s
  · right
    refine ⟨⟨v, st.s, H.root⟩, ?_⟩
    rw [if_pos hc] at h
    have h2' : (Except.ok (Spec.Protocol.on_goldfish_vote_checked P st ⟨v, st.s, H.root⟩,
        l ++ [Spec.NamedObject.gfVote ⟨v, st.s, H.root⟩]) :
        DC.DRE (Spec.Store V × List (Spec.NamedObject V))) =
          Except.ok (st', l') := h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h2'
    exact ⟨h2'.1.symm, h2'.2.symm, hc, rfl⟩
  · left
    rw [if_neg hc] at h
    have h2' : (Except.ok (st, l) :
        DC.DRE (Spec.Store V × List (Spec.NamedObject V))) =
          Except.ok (st', l') := h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h2'
    exact ⟨h2'.1.symm, h2'.2.symm⟩

omit [Inhabited V] in
/-- A successful run of the spec's tick, step by step: each optional step (proposal, Goldfish vote
    duty, confirmation update, attestation) ran when its test held and was skipped otherwise. -/
theorem tick_run_cond {C : Spec.Config} {P : Spec.Provisional V}
    {X : Spec.External V} {n n' : Spec.NodeState V}
    {t : Spec.Time} {sent : List (Spec.NamedObject V)}
    (h : (Spec.tick C P X n t).run [] = .ok (n', sent)) :
    ∃ (st0 st2 st3 st4 st5 : Spec.Store V) (sh5 : Spec.SigningHistory)
      (l1 l2 : List (Spec.NamedObject V)),
      Spec.Protocol.update_grades C P n.st t = .ok st0 ∧
      ((0 < C.slotOf t ∧ (decide (t = C.proposal_time (C.slotOf t)) &&
          decide (P.proposer (C.slotOf t) = n.v) &&
          (Spec.record_awake n t).awake_since
            (Spec.grade1_window_start C (C.round_of (C.slotOf t)))) = true) →
        ∃ B : Spec.Block V, st2 = Spec.Protocol.on_block C P
          { st0 with t := t, s := C.slotOf t } B ∧ l1 = [Spec.NamedObject.block B]) ∧
      (¬ (0 < C.slotOf t ∧ (decide (t = C.proposal_time (C.slotOf t)) &&
          decide (P.proposer (C.slotOf t) = n.v) &&
          (Spec.record_awake n t).awake_since
            (Spec.grade1_window_start C (C.round_of (C.slotOf t)))) = true) →
        st2 = { st0 with t := t, s := C.slotOf t } ∧ l1 = []) ∧
      ((0 < C.slotOf t ∧ (decide (t = C.vote_time (C.slotOf t)) &&
          (Spec.record_awake n t).awake_since
            (Spec.grade1_window_start C (C.round_of (C.slotOf t)))) = true) →
        (st3 = st2 ∧ l2 = l1) ∨ ∃ u : Spec.GoldfishVote V,
          st3 = Spec.Protocol.on_goldfish_vote_checked P st2 u ∧
          l2 = l1 ++ [Spec.NamedObject.gfVote u] ∧
          u.val_index ∈ P.committee u.slot ∧ u.slot = st2.s) ∧
      (¬ (0 < C.slotOf t ∧ (decide (t = C.vote_time (C.slotOf t)) &&
          (Spec.record_awake n t).awake_since
            (Spec.grade1_window_start C (C.round_of (C.slotOf t)))) = true) →
        st3 = st2 ∧ l2 = l1) ∧
      ((0 < C.slotOf t ∧ (decide (t = C.gf_confirmation_time (C.slotOf t)) &&
          (Spec.record_awake n t).awake_since
            (Spec.grade2_window_start C (C.round_of (C.slotOf t)))) = true) →
        Spec.Protocol.update_confirmation C st3 (C.slotOf t - 1) = .ok st4) ∧
      (¬ (0 < C.slotOf t ∧ (decide (t = C.gf_confirmation_time (C.slotOf t)) &&
          (Spec.record_awake n t).awake_since
            (Spec.grade2_window_start C (C.round_of (C.slotOf t)))) = true) →
        st4 = st3) ∧
      ((decide (t = C.round_attestation_time (C.round_of (C.slotOf t))) &&
          (Spec.record_awake n t).awake_since
            (Spec.grade2_window_start C (C.round_of (C.slotOf t)))) = true →
        ∃ row : Spec.Attestation V,
          Spec.Protocol.build_attestation C n.v st4 n.signingHistory = .ok (sh5, row) ∧
          st5 = Spec.Protocol.admit_attestation C st4 row ∧
          sent = l2 ++ [Spec.NamedObject.attest row]) ∧
      ((decide (t = C.round_attestation_time (C.round_of (C.slotOf t))) &&
          (Spec.record_awake n t).awake_since
            (Spec.grade2_window_start C (C.round_of (C.slotOf t)))) ≠ true →
        st5 = st4 ∧ sh5 = n.signingHistory ∧ sent = l2) ∧
      n' = { v := n.v, st := Spec.make_grades_compatible_with_finalized st5,
             signingHistory := sh5, awakeSince := (Spec.record_awake n t).awakeSince } := by
  rw [tick_eq_tickChain] at h
  unfold tickChain at h
  dsimp only at h
  rw [run_bind_ok] at h
  obtain ⟨st0, l0, h0, h⟩ := h
  rw [liftM_run] at h0
  obtain ⟨h0, rfl⟩ := h0
  rw [run_bind_ok] at h
  obtain ⟨st2, l1, h1, h⟩ := h
  rw [run_bind_ok] at h
  obtain ⟨st3, l2, h2, h⟩ := h
  rw [run_bind_ok] at h
  obtain ⟨st4, l3, h3, h⟩ := h
  rw [run_bind_ok] at h
  obtain ⟨⟨st5, sh5⟩, l4, h4, h⟩ := h
  unfold optStep at h1 h2 h3 h4
  rw [pure_run] at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rw [record_awake_st] at h0
  simp only [record_awake_v, record_awake_sh] at h1 h2 h3 h4 ⊢
  have h3' : l3 = l2 := by
    split_ifs at h3
    · rw [liftM_run] at h3; exact h3.2
    · rw [pure_run] at h3; simp only [Prod.mk.injEq] at h3; exact h3.2
  subst h3'
  refine ⟨st0, st2, st3, st4, st5, sh5, l1, l3, h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · intro hc
    rw [if_pos hc] at h1
    obtain ⟨B, rfl, rfl⟩ := propose_block_run h1
    exact ⟨B, rfl, rfl⟩
  · intro hc
    rw [if_neg hc, pure_run] at h1
    simp only [Prod.mk.injEq] at h1
    exact ⟨h1.1, h1.2⟩
  · intro hc
    rw [if_pos hc] at h2
    rcases goldfish_vote_run_signed h2 with ⟨rfl, rfl⟩ | ⟨u, rfl, rfl, hu⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨u, rfl, rfl, hu⟩
  · intro hc
    rw [if_neg hc, pure_run] at h2
    simp only [Prod.mk.injEq] at h2
    exact ⟨h2.1, h2.2⟩
  · intro hc
    rw [if_pos hc, liftM_run] at h3
    exact h3.1
  · intro hc
    rw [if_neg hc, pure_run] at h3
    simp only [Prod.mk.injEq] at h3
    exact h3.1
  · intro hc
    rw [if_pos hc] at h4
    obtain ⟨row, hb, rfl, rfl⟩ := attest_run h4
    exact ⟨row, hb, rfl, rfl⟩
  · intro hc
    rw [if_neg hc, pure_run] at h4
    simp only [Prod.mk.injEq] at h4
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h4
    exact ⟨rfl, rfl, rfl⟩

/-- An outcome of the member `tick` at `Model.spec` is an answer of the spec's tick on the node
    state's value, its sent objects mapped by `toProof`. -/
theorem tick_out (S : Setup V) (v : V) (n : (Model.spec (V := V)).N) (t : Time)
    (out : (Model.spec (V := V)).N × List (NamedObject V))
    (hout : (Model.spec (V := V)).tick S v n t ⇢ out) :
    ∃ sent, (Spec.tick (Setup.toSpec S).C (Setup.toSpec S).P (Setup.toSpec S).X n.val
        t).run [] = .ok (out.1.val, sent) ∧ out.2 = sent.map Spec.NamedObject.toProof := by
  obtain ⟨n', sent, hrun, he⟩ := (tick_returns_iff S v n.val t (out.1.val, out.2)).mp hout
  simp only [Prod.mk.injEq] at he
  obtain ⟨h1, h2⟩ := he
  exact ⟨sent, h1 ▸ hrun, h2⟩

/-- The tick's proposal test at `t` on `n`: a slot after genesis, `t` the slot's proposal time,
    `n`'s validator the slot's proposer, and the wake test of the round's grade-1 window. -/
def condP (C : Spec.Config) (P : Spec.Provisional V)
    (n : Spec.NodeState V) (t : Spec.Time) : Prop :=
  0 < C.slotOf t ∧ (decide (t = C.proposal_time (C.slotOf t)) &&
    decide (P.proposer (C.slotOf t) = n.v) &&
    (Spec.record_awake n t).awake_since
      (Spec.grade1_window_start C (C.round_of (C.slotOf t)))) = true

/-- The tick's Goldfish vote test: a slot after genesis, `t` the slot's vote time, and the wake test
    of the grade-1 window. -/
def condV (C : Spec.Config) (n : Spec.NodeState V)
    (t : Spec.Time) : Prop :=
  0 < C.slotOf t ∧ (decide (t = C.vote_time (C.slotOf t)) &&
    (Spec.record_awake n t).awake_since
      (Spec.grade1_window_start C (C.round_of (C.slotOf t)))) = true

/-- The tick's confirmation test: a slot after genesis, `t` the slot's Goldfish confirmation time,
    and the wake test of the grade-2 window. -/
def condC (C : Spec.Config) (n : Spec.NodeState V)
    (t : Spec.Time) : Prop :=
  0 < C.slotOf t ∧ (decide (t = C.gf_confirmation_time (C.slotOf t)) &&
    (Spec.record_awake n t).awake_since
      (Spec.grade2_window_start C (C.round_of (C.slotOf t)))) = true

/-- The tick's attestation test: `t` the attestation time of its slot's round, and the wake test of
    the grade-2 window. -/
def condA (C : Spec.Config) (n : Spec.NodeState V)
    (t : Spec.Time) : Prop :=
  (decide (t = C.round_attestation_time (C.round_of (C.slotOf t))) &&
    (Spec.record_awake n t).awake_since
      (Spec.grade2_window_start C (C.round_of (C.slotOf t)))) = true

omit [Inhabited V] in
/-- `tick_run_cond` with the four tests named `condP`, `condV`, `condC` and `condA`. -/
theorem tick_steps {C : Spec.Config} {P : Spec.Provisional V}
    {X : Spec.External V} {n n' : Spec.NodeState V}
    {t : Spec.Time} {sent : List (Spec.NamedObject V)}
    (h : (Spec.tick C P X n t).run [] = .ok (n', sent)) :
    ∃ (st0 st2 st3 st4 st5 : Spec.Store V) (sh5 : Spec.SigningHistory)
      (l1 l2 : List (Spec.NamedObject V)),
      Spec.Protocol.update_grades C P n.st t = .ok st0 ∧
      (condP C P n t → ∃ B : Spec.Block V, st2 = Spec.Protocol.on_block C P
          { st0 with t := t, s := C.slotOf t } B ∧ l1 = [Spec.NamedObject.block B]) ∧
      (¬ condP C P n t → st2 = { st0 with t := t, s := C.slotOf t } ∧ l1 = []) ∧
      (condV C n t → (st3 = st2 ∧ l2 = l1) ∨ ∃ u : Spec.GoldfishVote V,
          st3 = Spec.Protocol.on_goldfish_vote_checked P st2 u ∧
          l2 = l1 ++ [Spec.NamedObject.gfVote u] ∧
          u.val_index ∈ P.committee u.slot ∧ u.slot = st2.s) ∧
      (¬ condV C n t → st3 = st2 ∧ l2 = l1) ∧
      (condC C n t → Spec.Protocol.update_confirmation C st3 (C.slotOf t - 1) = .ok st4) ∧
      (¬ condC C n t → st4 = st3) ∧
      (condA C n t → ∃ row : Spec.Attestation V,
          Spec.Protocol.build_attestation C n.v st4 n.signingHistory = .ok (sh5, row) ∧
          st5 = Spec.Protocol.admit_attestation C st4 row ∧
          sent = l2 ++ [Spec.NamedObject.attest row]) ∧
      (¬ condA C n t → st5 = st4 ∧ sh5 = n.signingHistory ∧ sent = l2) ∧
      n' = { v := n.v, st := Spec.make_grades_compatible_with_finalized st5,
             signingHistory := sh5, awakeSince := (Spec.record_awake n t).awakeSince } :=
  tick_run_cond h

omit [Inhabited V] in
/-- Every object the tick sends is the proposal, sent when `condP` holds, a Goldfish vote, sent when
    `condV` holds, or an attestation, sent when `condA` holds. -/
theorem tick_sent {C : Spec.Config} {P : Spec.Provisional V}
    {X : Spec.External V} {n n' : Spec.NodeState V}
    {t : Spec.Time} {sent : List (Spec.NamedObject V)}
    (h : (Spec.tick C P X n t).run [] = .ok (n', sent))
    {o : Spec.NamedObject V} (ho : o ∈ sent) :
    (∃ B, o = .block B ∧ condP C P n t) ∨ (∃ u, o = .gfVote u ∧ condV C n t) ∨
      (∃ row, o = .attest row ∧ condA C n t) := by
  obtain ⟨st0, st2, st3, st4, st5, sh5, l1, l2, -, hP1, hP0, hV1, hV0, -, -, hA1, hA0, -⟩ :=
    tick_steps h
  have hl1 : o ∈ l1 → ∃ B, o = .block B ∧ condP C P n t := by
    intro hm
    by_cases hc : condP C P n t
    · obtain ⟨B, -, rfl⟩ := hP1 hc
      exact ⟨B, List.mem_singleton.mp hm, hc⟩
    · rw [(hP0 hc).2] at hm
      exact absurd hm List.not_mem_nil
  have hl2 : o ∈ l2 → (∃ B, o = .block B ∧ condP C P n t) ∨ (∃ u, o = .gfVote u ∧ condV C n t) := by
    intro hm
    by_cases hc : condV C n t
    · rcases hV1 hc with ⟨-, rfl⟩ | ⟨u, -, rfl, -⟩
      · exact Or.inl (hl1 hm)
      · rcases List.mem_append.mp hm with hm | hm
        · exact Or.inl (hl1 hm)
        · exact Or.inr ⟨u, List.mem_singleton.mp hm, hc⟩
    · rw [(hV0 hc).2] at hm
      exact Or.inl (hl1 hm)
  by_cases hc : condA C n t
  · obtain ⟨row, -, -, rfl⟩ := hA1 hc
    rcases List.mem_append.mp ho with hm | hm
    · rcases hl2 hm with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr ⟨row, List.mem_singleton.mp hm, hc⟩)
  · rw [(hA0 hc).2.2] at ho
    rcases hl2 ho with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)

omit [DecidableEq V] [Fintype V] [Inhabited V] in
/-- A slot after genesis is the slot of a time `t ≥ 0`. -/
theorem nonneg_of_slot_pos (C : Spec.Config) {t : Spec.Time}
    (h : 0 < C.slotOf t) : 0 ≤ t := by
  by_contra hneg
  have hΔ : (0 : Int) < 4 * C.Δ := by have := C.Δ_pos; time_omega
  have hf := Int.fdiv_neg_of_neg_of_pos (show (t : Int) < 0 by time_omega) hΔ
  simp only [Spec.Config.slotOf, Int.toNat_eq_zero.mpr hf.le] at h
  exact absurd h (lt_irrefl 0)

omit [DecidableEq V] [Fintype V] [Inhabited V] in
/-- At a time `t ≥ 0`, both wake windows of the round of `t`'s slot start before `t`. -/
theorem window_lt (C : Spec.Config) {t : Spec.Time} (ht : 0 ≤ t) :
    Spec.grade1_window_start C (C.round_of (C.slotOf t)) < t ∧
      Spec.grade2_window_start C (C.round_of (C.slotOf t)) < t := by
  have h := (NoRaise.opening_le_self C ht).1
  have hΔ := C.Δ_pos
  rw [NoRaise.grade1_window_start_eq, NoRaise.grade2_window_start_eq]
  simp only [NoRaise.roundAt] at h
  constructor <;> time_omega

omit [DecidableEq V] [Fintype V] [Inhabited V] in
/-- Every attestation time is positive. -/
theorem attestation_time_pos (C : Spec.Config) (r : Spec.Round) :
    0 < C.round_attestation_time r := by
  have hΔ := C.Δ_pos
  have h0 : (0 : Int) ≤ C.opening r := by
    simp only [Spec.Config.opening, Spec.Config.proposal_time]
    exact Int.mul_nonneg (by time_omega) (Int.natCast_nonneg _)
  simp only [Spec.Config.round_attestation_time]
  time_omega

omit [DecidableEq V] [Fintype V] [Inhabited V] in
/-- A wake test passed at a bound `x < t` reads an `awakeSince` the node held: the node had been
    awake since some `a ≤ x`. -/
theorem awake_of_test {n : Spec.NodeState V} {t x : Spec.Time}
    (h : (Spec.record_awake n t).awake_since x = true) (hx : x < t) :
    ∃ a, n.awakeSince = some a ∧ a ≤ x := by
  rcases (record_awake_awake_since n t x).mp h with h | ⟨-, h⟩
  · exact h
  · exact absurd h (not_le.mpr hx)

omit [Inhabited V] in
/-- When the proposal test holds, the node had been awake since the grade-1 window start of the
    round of `t`'s slot. -/
theorem awake_of_condP {C : Spec.Config} {P : Spec.Provisional V}
    {n : Spec.NodeState V} {t : Spec.Time} (h : condP C P n t) :
    ∃ a, n.awakeSince = some a ∧
      a ≤ Spec.grade1_window_start C (C.round_of (C.slotOf t)) := by
  obtain ⟨hs, h⟩ := h
  simp only [Bool.and_eq_true] at h
  exact awake_of_test h.2 (window_lt C (nonneg_of_slot_pos C hs)).1

omit [Inhabited V] in
/-- When the vote test holds, the node had been awake since the grade-1 window start. -/
theorem awake_of_condV {C : Spec.Config} {n : Spec.NodeState V}
    {t : Spec.Time} (h : condV C n t) :
    ∃ a, n.awakeSince = some a ∧
      a ≤ Spec.grade1_window_start C (C.round_of (C.slotOf t)) := by
  obtain ⟨hs, h⟩ := h
  simp only [Bool.and_eq_true] at h
  exact awake_of_test h.2 (window_lt C (nonneg_of_slot_pos C hs)).1

omit [Inhabited V] in
/-- When the confirmation test holds, the node had been awake since the grade-2 window start. -/
theorem awake_of_condC {C : Spec.Config} {n : Spec.NodeState V}
    {t : Spec.Time} (h : condC C n t) :
    ∃ a, n.awakeSince = some a ∧
      a ≤ Spec.grade2_window_start C (C.round_of (C.slotOf t)) := by
  obtain ⟨hs, h⟩ := h
  simp only [Bool.and_eq_true] at h
  exact awake_of_test h.2 (window_lt C (nonneg_of_slot_pos C hs)).2

omit [Inhabited V] in
/-- When the attestation test holds, the node had been awake since the grade-2 window start. -/
theorem awake_of_condA {C : Spec.Config} {n : Spec.NodeState V}
    {t : Spec.Time} (h : condA C n t) :
    ∃ a, n.awakeSince = some a ∧
      a ≤ Spec.grade2_window_start C (C.round_of (C.slotOf t)) := by
  simp only [condA, Bool.and_eq_true, decide_eq_true_eq] at h
  have ht : 0 ≤ t := by rw [h.1]; exact (attestation_time_pos C _).le
  exact awake_of_test h.2 (window_lt C ht).2

/-- `TreeEq a b`: the store `b` has `a`'s tree, finalized and justified blocks, justified height and
    largest chain-state height. -/
def TreeEq (a b : Spec.Store V) : Prop :=
  b.T = a.T ∧ b.F = a.F ∧ b.J = a.J ∧ b.h_j = a.h_j ∧ b.h_max = a.h_max

omit [DecidableEq V] [Fintype V] [Inhabited V] in
theorem TreeEq.refl (a : Spec.Store V) : TreeEq a a := ⟨rfl, rfl, rfl, rfl, rfl⟩

omit [DecidableEq V] [Fintype V] [Inhabited V] in
theorem TreeEq.trans {a b c : Spec.Store V} (h1 : TreeEq a b) (h2 : TreeEq b c) :
    TreeEq a c :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.1.trans h1.2.2.2.1,
    h2.2.2.2.2.trans h1.2.2.2.2⟩

/-- `RecEq a b`: the store `b` has `a`'s three confirmation records. -/
def RecEq (a b : Spec.Store V) : Prop :=
  b.live_confirmed = a.live_confirmed ∧ b.latest_confirmed = a.latest_confirmed ∧
    b.latest_stable = a.latest_stable

omit [DecidableEq V] [Fintype V] [Inhabited V] in
theorem RecEq.trans {a b c : Spec.Store V} (h1 : RecEq a b) (h2 : RecEq b c) :
    RecEq a c :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩

omit [Fintype V] [Inhabited V] in
theorem recEq_of_keeps {a b : Spec.Store V} (h : Keeps a b) : RecEq a b :=
  ⟨h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1⟩

omit [Inhabited V] in
/-- When the proposal test fails, the tick keeps the tree, the finalized and justified blocks, the
    justified height and the largest chain-state height. -/
theorem tick_treeEq_of_not_condP {C : Spec.Config} {P : Spec.Provisional V}
    {X : Spec.External V} {n n' : Spec.NodeState V}
    {t : Spec.Time} {sent : List (Spec.NamedObject V)}
    (h : (Spec.tick C P X n t).run [] = .ok (n', sent)) (hc : ¬ condP C P n t) :
    TreeEq n.st n'.st := by
  obtain ⟨st0, st2, st3, st4, st5, sh5, l1, l2, h0, -, hP0, hV1, hV0, hC1, hC0, hA1, hA0, rfl⟩ :=
    tick_steps h
  obtain ⟨rfl, -⟩ := hP0 hc
  have e0 : TreeEq n.st { st0 with t := t, s := C.slotOf t } := by
    rw [(update_grades_ok h0).1]; exact TreeEq.refl _
  have e3 : TreeEq { st0 with t := t, s := C.slotOf t } st3 := by
    by_cases hv : condV C n t
    · rcases hV1 hv with ⟨rfl, -⟩ | ⟨u, rfl, -⟩
      · exact TreeEq.refl _
      · obtain ⟨gv, tv, e⟩ := on_goldfish_vote_checked_frame P { st0 with t := t, s := C.slotOf t } u
        rw [e]; exact TreeEq.refl _
    · rw [(hV0 hv).1]; exact TreeEq.refl _
  have e4 : TreeEq st3 st4 := by
    by_cases hcc : condC C n t
    · rw [update_confirmation_ok (hC1 hcc)]; exact TreeEq.refl _
    · rw [hC0 hcc]; exact TreeEq.refl _
  have e5 : TreeEq st4 st5 := by
    by_cases ha : condA C n t
    · obtain ⟨row, -, rfl, -⟩ := hA1 ha
      obtain ⟨at', ts, e⟩ := admit_attestation_frame C st4 row
      rw [e]; exact TreeEq.refl _
    · rw [(hA0 ha).1]; exact TreeEq.refl _
  exact e0.trans (e3.trans (e4.trans (e5.trans (TreeEq.refl _))))

omit [Inhabited V] in
/-- When the confirmation test fails, the tick keeps the three confirmation records. -/
theorem tick_recEq_of_not_condC {C : Spec.Config} {P : Spec.Provisional V}
    {X : Spec.External V} {n n' : Spec.NodeState V}
    {t : Spec.Time} {sent : List (Spec.NamedObject V)}
    (h : (Spec.tick C P X n t).run [] = .ok (n', sent)) (hc : ¬ condC C n t) :
    RecEq n.st n'.st := by
  obtain ⟨st0, st2, st3, st4, st5, sh5, l1, l2, h0, hP1, hP0, hV1, hV0, -, hC0, hA1, hA0, rfl⟩ :=
    tick_steps h
  have e0 : RecEq n.st { st0 with t := t, s := C.slotOf t } := by
    rw [(update_grades_ok h0).1]; exact ⟨rfl, rfl, rfl⟩
  have e2 : RecEq { st0 with t := t, s := C.slotOf t } st2 := by
    by_cases hp : condP C P n t
    · obtain ⟨B, rfl, -⟩ := hP1 hp
      exact recEq_of_keeps (keeps_on_block _ _ _ _)
    · rw [(hP0 hp).1]; exact ⟨rfl, rfl, rfl⟩
  have e3 : RecEq st2 st3 := by
    by_cases hv : condV C n t
    · rcases hV1 hv with ⟨rfl, -⟩ | ⟨u, rfl, -⟩
      · exact ⟨rfl, rfl, rfl⟩
      · exact recEq_of_keeps (keeps_on_goldfish_vote_checked _ _ _)
    · rw [(hV0 hv).1]; exact ⟨rfl, rfl, rfl⟩
  have e5 : RecEq st4 st5 := by
    by_cases ha : condA C n t
    · obtain ⟨row, -, rfl, -⟩ := hA1 ha
      exact recEq_of_keeps (keeps_admit_attestation _ _ _)
    · rw [(hA0 ha).1]; exact ⟨rfl, rfl, rfl⟩
  rw [hC0 hc] at e5
  exact e0.trans (e2.trans (e3.trans (e5.trans ⟨rfl, rfl, rfl⟩)))

omit [DecidableEq V] [Fintype V] [Inhabited V] in
/-- Integer division read off its bounds: if `d * q ≤ t < d * (q + 1)` with `d > 0`, then
`t / d = q`. -/
theorem ediv_eq_of_bounds {t d q : Int} (hd : 0 < d) (h1 : d * q ≤ t) (h2 : t < d * (q + 1)) :
    t / d = q := by
  have e := Int.mul_ediv_add_emod t d
  have m1 := Int.emod_nonneg t (ne_of_gt hd)
  have m2 := Int.emod_lt_of_pos t hd
  rcases lt_trichotomy (t / d) q with h | h | h
  · have : t / d + 1 ≤ q := h
    nlinarith
  · exact h
  · have : q + 1 ≤ t / d := h
    nlinarith

omit [DecidableEq V] [Fintype V] [Inhabited V] in
/-- A time between the starts of slots `s` and `s + 1` is in slot `s`. -/
theorem slotOf_of_bounds (C : Spec.Config) {t : Spec.Time} {s : Nat}
    (h1 : 4 * C.Δ * (s : Int) ≤ t) (h2 : t < 4 * C.Δ * ((s : Int) + 1)) : C.slotOf t = s := by
  have hΔ := C.Δ_pos
  simp only [Spec.Config.slotOf]
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by time_omega), ediv_eq_of_bounds (by time_omega) h1 h2]
  simp

omit [DecidableEq V] [Fintype V] [Inhabited V] in
/-- Round `r`'s attestation time is in slot `r * R + 1`. -/
theorem slotOf_attestation_time (C : Spec.Config) (r : Spec.Round) :
    C.slotOf (C.round_attestation_time r) = r * C.R + 1 := by
  have hΔ := C.Δ_pos
  apply slotOf_of_bounds
  · simp only [Spec.Config.round_attestation_time, Spec.Config.opening,
      Spec.Config.proposal_time]
    push_cast
    nlinarith
  · simp only [Spec.Config.round_attestation_time, Spec.Config.opening,
      Spec.Config.proposal_time]
    push_cast
    nlinarith

omit [DecidableEq V] [Fintype V] [Inhabited V] in
/-- The slot after a round's first slot is in that round. -/
theorem round_of_first_succ (C : Spec.Config) (r : Spec.Round) :
    C.round_of (r * C.R + 1) = r := by
  have hR : 1 < C.R := by have := C.R_ge_three; omega
  simp only [Spec.Config.round_of]
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hR, Nat.zero_add]

omit [DecidableEq V] [Fintype V] [Inhabited V] in
/-- Slot `s`'s confirmation time is in slot `s + 1`. -/
theorem slotOf_confirmation_time (C : Spec.Config) (s : Spec.Slot) :
    C.slotOf (C.confirmation_time s) = s + 1 := by
  have hΔ := C.Δ_pos
  apply slotOf_of_bounds
  · simp only [Spec.Config.confirmation_time, Spec.Config.proposal_time]
    push_cast
    nlinarith
  · simp only [Spec.Config.confirmation_time, Spec.Config.proposal_time]
    push_cast
    nlinarith

/-! ## Tick facts read off the tick's tests -/

/-- The field `tick_send_eq_of_state` of `NodeFacts` at `Model.spec`: two outcomes of `v`'s
    tick at `t` from `n` with equal node states send equal lists of objects. -/
theorem spec_tick_send_eq_of_state :
    ∀ (S : Setup V) (v : V) (n : (Model.spec (V := V)).N) (t : Time)
        (out out' : (Model.spec (V := V)).N × List (NamedObject V)), (Model.spec (V := V)).tick S v n t ⇢ out → (Model.spec (V := V)).tick S v n t ⇢ out' →
        out.1 = out'.1 → out.2 = out'.2 := by
  intro S v n t out out' h1 h2 _
  obtain ⟨s1, r1, e1⟩ := tick_out S v n t out h1
  obtain ⟨s2, r2, e2⟩ := tick_out S v n t out' h2
  rw [r1] at r2
  simp only [Except.ok.injEq, Prod.mk.injEq] at r2
  rw [e1, e2, r2.2]

/-- The field `block_mem_on_tick_emit_awake` of `NodeFacts` at `Model.spec`: if an outcome of
    `v`'s tick at `t` from `n` sends a block, then `n` passes the grade-1 awake test
    `M.awake_for_grade1` of the round of `t`'s slot. -/
theorem spec_block_mem_on_tick_emit_awake :
    ∀ (S : Setup V) (v : V) (n : (Model.spec (V := V)).N) (t : Time)
        (out : (Model.spec (V := V)).N × List (NamedObject V)), (Model.spec (V := V)).tick S v n t ⇢ out → ∀ {B : NamedBlock V},
        NamedObject.block B ∈ out.2 → (Model.spec (V := V)).awake_for_grade1 S v n ((Model.spec (V := V)).round_of S.hc (S.E.slotOf t)) := by
  intro S v n t out hout B hB
  obtain ⟨sent, hrun, hsent⟩ := tick_out S v n t out hout
  rw [hsent] at hB
  obtain ⟨o, ho, hoB⟩ := List.mem_map.mp hB
  rcases tick_sent hrun ho with ⟨B', rfl, hc⟩ | ⟨u, rfl, -⟩ | ⟨row, rfl, -⟩
  · show ∃ a, n.val.awakeSince = some a ∧ a ≤ Spec.grade1_window_start (Setup.toSpec S).C
        ((Setup.toSpec S).C.round_of (S.E.slotOf t))
    rw [← slotOf_eq S t]
    exact awake_of_condP hc
  · simp only [Spec.NamedObject.toProof, reduceCtorEq] at hoB
  · simp only [Spec.NamedObject.toProof, reduceCtorEq] at hoB

/-- The field `gfVote_mem_on_tick_emit_awake` of `NodeFacts` at `Model.spec`: if an outcome of
    `v`'s tick at `t` from `n` sends a Goldfish vote, then `n` passes the grade-1 awake test
    `M.awake_for_grade1` of the round of `t`'s slot. -/
theorem spec_gfVote_mem_on_tick_emit_awake :
    ∀ (S : Setup V) (v : V) (n : (Model.spec (V := V)).N) (t : Time)
        (out : (Model.spec (V := V)).N × List (NamedObject V)), (Model.spec (V := V)).tick S v n t ⇢ out → ∀ {u : GoldfishVote V},
        NamedObject.gfVote u ∈ out.2 → (Model.spec (V := V)).awake_for_grade1 S v n ((Model.spec (V := V)).round_of S.hc (S.E.slotOf t)) := by
  intro S v n t out hout u hu
  obtain ⟨sent, hrun, hsent⟩ := tick_out S v n t out hout
  rw [hsent] at hu
  obtain ⟨o, ho, hou⟩ := List.mem_map.mp hu
  rcases tick_sent hrun ho with ⟨B', rfl, -⟩ | ⟨u', rfl, hc⟩ | ⟨row, rfl, -⟩
  · simp only [Spec.NamedObject.toProof, reduceCtorEq] at hou
  · show ∃ a, n.val.awakeSince = some a ∧ a ≤ Spec.grade1_window_start (Setup.toSpec S).C
        ((Setup.toSpec S).C.round_of (S.E.slotOf t))
    rw [← slotOf_eq S t]
    exact awake_of_condV hc
  · simp only [Spec.NamedObject.toProof, reduceCtorEq] at hou

/-- The field `tick_at_action_asleep` of `NodeFacts` at `Model.spec`: if `before` fails the
    grade-2 awake test `M.awake_for_grade2` of round `r`, then every outcome of `v`'s tick at round
    `r`'s action time from `before` sends nothing. -/
theorem spec_tick_at_action_asleep :
    ∀ (S : Setup V) (v : V) (before : (Model.spec (V := V)).N) (r : Round)
        (out : (Model.spec (V := V)).N × List (NamedObject V)) (hout : (Model.spec (V := V)).tick S v before ((Model.spec (V := V)).a S.hc S.E.Δ r) ⇢ out)
        (hasleep : ¬ (Model.spec (V := V)).awake_for_grade2 S v before r),
        out.2 = [] := by
  intro S v before r out hout hasleep
  obtain ⟨sent, hrun, hsent⟩ := tick_out S v before _ out hout
  obtain ⟨st0, st2, st3, st4, st5, sh5, l1, l2, -, -, hP0, -, hV0, -, -, -, hA0, -⟩ := tick_steps hrun
  have hΔ := (Setup.toSpec S).C.Δ_pos
  have hs : (Setup.toSpec S).C.slotOf ((Model.spec (V := V)).a S.hc S.E.Δ r) =
      r * (Setup.toSpec S).C.R + 1 := slotOf_attestation_time _ r
  have hr : (Setup.toSpec S).C.round_of (r * (Setup.toSpec S).C.R + 1) = r := round_of_first_succ _ r
  have hP : ¬ condP (Setup.toSpec S).C (Setup.toSpec S).P before.val
      ((Model.spec (V := V)).a S.hc S.E.Δ r) := by
    rintro ⟨-, hc⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    have h1 := hc.1.1
    rw [hs] at h1
    change 4 * S.E.Δ * ((r * S.hc.R : Nat) : Int) + 6 * S.E.Δ =
      4 * S.E.Δ * ((r * S.hc.R + 1 : Nat) : Int) at h1
    push_cast at h1
    change (0 : Int) < S.E.Δ at hΔ
    linarith
  have hV : ¬ condV (Setup.toSpec S).C before.val ((Model.spec (V := V)).a S.hc S.E.Δ r) := by
    rintro ⟨-, hc⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    have h1 := hc.1
    rw [hs] at h1
    change 4 * S.E.Δ * ((r * S.hc.R : Nat) : Int) + 6 * S.E.Δ =
      4 * S.E.Δ * ((r * S.hc.R + 1 : Nat) : Int) + S.E.Δ at h1
    push_cast at h1
    change (0 : Int) < S.E.Δ at hΔ
    linarith
  have hA : ¬ condA (Setup.toSpec S).C before.val ((Model.spec (V := V)).a S.hc S.E.Δ r) := by
    intro hc
    obtain ⟨a, ha, hle⟩ := awake_of_condA hc
    rw [hs, hr] at hle
    exact hasleep ⟨a, ha, hle⟩
  obtain ⟨-, rfl⟩ := hP0 hP
  obtain ⟨-, rfl⟩ := hV0 hV
  obtain ⟨-, -, rfl⟩ := hA0 hA
  rw [hsent]
  rfl

/-- The field `tick_frame_of_not_awake_for_grade1` of `NodeFacts` at `Model.spec`: if `n` fails
    the grade-1 awake test of the round of `t`'s slot, every outcome of `v`'s tick at `t` from `n`
    keeps `n`'s bodies and finalized checkpoint `F`. -/
theorem spec_tick_frame_of_not_awake_for_grade1 :
    ∀ (S : Setup V) (v : V) (n : (Model.spec (V := V)).N) (t : Time)
        (out : (Model.spec (V := V)).N × List (NamedObject V)), (Model.spec (V := V)).tick S v n t ⇢ out →
        ¬ (Model.spec (V := V)).awake_for_grade1 S v n ((Model.spec (V := V)).round_of S.hc (S.E.slotOf t)) →
        out.1.st.bodies = n.st.bodies ∧ out.1.st.core.F = n.st.core.F := by
  intro S v n t out hout hna
  obtain ⟨sent, hrun, -⟩ := tick_out S v n t out hout
  have hc : ¬ condP (Setup.toSpec S).C (Setup.toSpec S).P n.val t := by
    intro hc
    apply hna
    show ∃ a, n.val.awakeSince = some a ∧ a ≤ Spec.grade1_window_start (Setup.toSpec S).C
      ((Setup.toSpec S).C.round_of (S.E.slotOf t))
    rw [← slotOf_eq S t]
    exact awake_of_condP hc
  obtain ⟨hT, hF, -⟩ := tick_treeEq_of_not_condP hrun hc
  refine ⟨?_, ?_⟩
  · show Member.bodies out.1.val.st = Member.bodies n.val.st
    unfold Member.bodies
    rw [hT]
  · show out.1.val.st.F.toProof = n.val.st.F.toProof
    rw [hF]

/-- The field `tick_tree_fields_of_not_proposal_vote` of `NodeFacts` at `Model.spec`: if `t` is
    neither the proposal time nor the Goldfish vote time of its slot, every outcome of `v`'s tick at
    `t` from `n` keeps the finalized and justified blocks, the justified height, the largest height,
    the block tree and the bodies of `n`'s store. -/
theorem spec_tick_tree_fields_of_not_proposal_vote :
    ∀ (S : Setup V) (v : V) (n : (Model.spec (V := V)).N) (t : Time)
        (hnp : t ≠ (Model.spec (V := V)).proposal_time S.E (S.E.slotOf t))
        (hnv : t ≠ (Model.spec (V := V)).vote_time S.E (S.E.slotOf t))
        (out : (Model.spec (V := V)).N × List (NamedObject V)) (hout : (Model.spec (V := V)).tick S v n t ⇢ out),
        out.1.st.core.F = n.st.core.F ∧
          out.1.st.core.J = n.st.core.J ∧
          out.1.st.core.h_j = n.st.core.h_j ∧
          out.1.st.core.h_max = n.st.core.h_max ∧
          out.1.st.core.T = n.st.core.T ∧
          out.1.st.bodies = n.st.bodies := by
  intro S v n t hnp _ out hout
  obtain ⟨sent, hrun, -⟩ := tick_out S v n t out hout
  have hc : ¬ condP (Setup.toSpec S).C (Setup.toSpec S).P n.val t := by
    rintro ⟨-, hc⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    have h1 := hc.1.1
    rw [slotOf_eq] at h1
    exact hnp h1
  obtain ⟨hT, hF, hJ, hj, hm⟩ := tick_treeEq_of_not_condP hrun hc
  refine ⟨?_, ?_, hj, hm, ?_, ?_⟩
  · show out.1.val.st.F.toProof = n.val.st.F.toProof
    rw [hF]
  · show out.1.val.st.J.toProof = n.val.st.J.toProof
    rw [hJ]
  · show out.1.val.st.T.image Spec.Block.toProof = n.val.st.T.image Spec.Block.toProof
    rw [hT]
  · show Member.bodies out.1.val.st = Member.bodies n.val.st
    unfold Member.bodies
    rw [hT]

/-- The field `on_tick_emit_stable_of_ne` of `NodeFacts` at `Model.spec`: unless `t` is the
    support cutoff of its own slot after genesis, every outcome of `v`'s tick at `t` from `n` keeps
    `n`'s `latest_stable`. -/
theorem spec_on_tick_emit_stable_of_ne :
    ∀ (S : Setup V) (v : V) (n : (Model.spec (V := V)).N) (t : Time)
        (h : ¬ (0 < S.E.slotOf t ∧ t = (Model.spec (V := V)).support_cutoff S.E (S.E.slotOf t)))
        (out : (Model.spec (V := V)).N × List (NamedObject V)) (hout : (Model.spec (V := V)).tick S v n t ⇢ out),
        out.1.st.core.latest_stable = n.st.core.latest_stable := by
  intro S v n t h out hout
  obtain ⟨sent, hrun, -⟩ := tick_out S v n t out hout
  have hc : ¬ condC (Setup.toSpec S).C n.val t := by
    rintro ⟨hs, hc⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    have h1 := hc.1
    rw [slotOf_eq] at hs h1
    exact h ⟨hs, h1⟩
  obtain ⟨-, -, hst⟩ := tick_recEq_of_not_condC hrun hc
  show out.1.val.st.latest_stable.toProof = n.val.st.latest_stable.toProof
  rw [hst]

/-- The field `on_tick_emit_latest_of_ne` of `NodeFacts` at `Model.spec`: unless `t` is the
    support cutoff of its own slot after genesis, every outcome of `v`'s tick at `t` from `n` keeps
    `n`'s `latest_confirmed`. -/
theorem spec_on_tick_emit_latest_of_ne :
    ∀ (S : Setup V) (v : V) (n : (Model.spec (V := V)).N) (t : Time)
        (h : ¬ (0 < S.E.slotOf t ∧ t = (Model.spec (V := V)).support_cutoff S.E (S.E.slotOf t)))
        (out : (Model.spec (V := V)).N × List (NamedObject V)) (hout : (Model.spec (V := V)).tick S v n t ⇢ out),
        out.1.st.core.latest_confirmed = n.st.core.latest_confirmed := by
  intro S v n t h out hout
  obtain ⟨sent, hrun, -⟩ := tick_out S v n t out hout
  have hc : ¬ condC (Setup.toSpec S).C n.val t := by
    rintro ⟨hs, hc⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    have h1 := hc.1
    rw [slotOf_eq] at hs h1
    exact h ⟨hs, h1⟩
  obtain ⟨-, hlc, -⟩ := tick_recEq_of_not_condC hrun hc
  show out.1.val.st.latest_confirmed.toProof = n.val.st.latest_confirmed.toProof
  rw [hlc]

/-- The field `tick_records_frame_of_not_awake_for_grade2` of `NodeFacts` at `Model.spec`: if
    `n` fails the grade-2 awake test of the round of slot `s + 1`, every outcome of `v`'s tick at
    slot `s`'s confirmation time from `n` keeps `n`'s latest confirmed and latest stable blocks. -/
theorem spec_tick_records_frame_of_not_awake_for_grade2 :
    ∀ (S : Setup V) (v : V) (n : (Model.spec (V := V)).N) (s : Slot)
        (out : (Model.spec (V := V)).N × List (NamedObject V)),
        (Model.spec (V := V)).tick (Setup.alwaysAwake S) v n ((Model.spec (V := V)).confirmation_time S.E s) ⇢ out →
        ¬ (Model.spec (V := V)).awake_for_grade2 (Setup.alwaysAwake S) v n ((Model.spec (V := V)).round_of S.hc (s + 1)) →
        out.1.st.core.latest_confirmed = n.st.core.latest_confirmed ∧
        out.1.st.core.latest_stable = n.st.core.latest_stable := by
  intro S v n s out hout hna
  obtain ⟨sent, hrun, -⟩ := tick_out (Setup.alwaysAwake S) v n _ out hout
  have hs : (Setup.toSpec (Setup.alwaysAwake S)).C.slotOf
      ((Model.spec (V := V)).confirmation_time S.E s) = s + 1 :=
    slotOf_confirmation_time _ s
  have hc : ¬ condC (Setup.toSpec (Setup.alwaysAwake S)).C n.val
      ((Model.spec (V := V)).confirmation_time S.E s) := by
    intro hc
    obtain ⟨a, ha, hle⟩ := awake_of_condC hc
    rw [hs] at hle
    exact hna ⟨a, ha, hle⟩
  obtain ⟨-, hlc, hst⟩ := tick_recEq_of_not_condC hrun hc
  refine ⟨?_, ?_⟩
  · show out.1.val.st.latest_confirmed.toProof = n.val.st.latest_confirmed.toProof
    rw [hlc]
  · show out.1.val.st.latest_stable.toProof = n.val.st.latest_stable.toProof
    rw [hst]

/-- `TSEq a b`: the store `b` has `a`'s tree, block stamps, chain states, finalized and justified
    blocks, justified height, largest chain-state height, clock and slot. -/
def TSEq (a b : Spec.Store V) : Prop :=
  b.T = a.T ∧ b.timestamp_block = a.timestamp_block ∧ b.σ = a.σ ∧ b.F = a.F ∧ b.J = a.J ∧
    b.h_j = a.h_j ∧ b.h_max = a.h_max ∧ b.t = a.t ∧ b.s = a.s

omit [DecidableEq V] [Fintype V] [Inhabited V] in
theorem TSEq.refl (a : Spec.Store V) : TSEq a a :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

omit [DecidableEq V] [Fintype V] [Inhabited V] in
theorem TSEq.trans {a b c : Spec.Store V} (h1 : TSEq a b) (h2 : TSEq b c) :
    TSEq a c := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h1
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := h2
  exact ⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5, b6.trans a6,
    b7.trans a7, b8.trans a8, b9.trans a9⟩

omit [Inhabited V] in
/-- From the proposal step on, the tick keeps every field `TSEq` reads. -/
theorem tick_tseq_after_proposal {C : Spec.Config} {P : Spec.Provisional V}
    {X : Spec.External V} {n n' : Spec.NodeState V}
    {t : Spec.Time} {sent : List (Spec.NamedObject V)}
    (h : (Spec.tick C P X n t).run [] = .ok (n', sent)) :
    ∃ (st0 st2 : Spec.Store V),
      Spec.Protocol.update_grades C P n.st t = .ok st0 ∧
      (condP C P n t → ∃ B : Spec.Block V, st2 = Spec.Protocol.on_block C P
          { st0 with t := t, s := C.slotOf t } B ∧ Spec.NamedObject.block B ∈ sent) ∧
      (¬ condP C P n t → st2 = { st0 with t := t, s := C.slotOf t }) ∧ TSEq st2 n'.st := by
  obtain ⟨st0, st2, st3, st4, st5, sh5, l1, l2, h0, hP1, hP0, hV1, hV0, hC1, hC0, hA1, hA0, rfl⟩ :=
    tick_steps h
  have hl1 : ∀ o ∈ l1, o ∈ sent := by
    intro o ho
    have h2 : o ∈ l2 := by
      by_cases hv : condV C n t
      · rcases hV1 hv with ⟨-, rfl⟩ | ⟨u, -, rfl, -⟩
        · exact ho
        · exact List.mem_append_left _ ho
      · rw [(hV0 hv).2]; exact ho
    by_cases ha : condA C n t
    · obtain ⟨row, -, -, rfl⟩ := hA1 ha
      exact List.mem_append_left _ h2
    · rw [(hA0 ha).2.2]; exact h2
  refine ⟨st0, st2, h0, ?_, fun hc => (hP0 hc).1, ?_⟩
  · intro hc
    obtain ⟨B, hB, hl⟩ := hP1 hc
    exact ⟨B, hB, hl1 _ (by rw [hl]; exact List.mem_singleton_self _)⟩
  have e3 : TSEq st2 st3 := by
    by_cases hv : condV C n t
    · rcases hV1 hv with ⟨rfl, -⟩ | ⟨u, rfl, -⟩
      · exact TSEq.refl _
      · obtain ⟨gv, tv, e⟩ := on_goldfish_vote_checked_frame P st2 u
        rw [e]; exact TSEq.refl _
    · rw [(hV0 hv).1]; exact TSEq.refl _
  have e4 : TSEq st3 st4 := by
    by_cases hcc : condC C n t
    · rw [update_confirmation_ok (hC1 hcc)]; exact TSEq.refl _
    · rw [hC0 hcc]; exact TSEq.refl _
  have e5 : TSEq st4 st5 := by
    by_cases ha : condA C n t
    · obtain ⟨row, -, rfl, -⟩ := hA1 ha
      obtain ⟨at', ts, e⟩ := admit_attestation_frame C st4 row
      rw [e]; exact TSEq.refl _
    · rw [(hA0 ha).1]; exact TSEq.refl _
  exact e3.trans (e4.trans (e5.trans (TSEq.refl _)))

/-- The store of an outcome of the member `tick` at `Model.spec`, up to `TSEq`: the node's
    store with its saved grades, clock and slot written, or, when the tick sends a block, the
    receipt of that block on that store. -/
theorem tick_shape (S : Setup V) (v : V) (n : (Model.spec (V := V)).N) (t : Time)
    (out : (Model.spec (V := V)).N × List (NamedObject V))
    (hout : (Model.spec (V := V)).tick S v n t ⇢ out) :
    ∃ sg : Spec.SavedGrades V,
      (TSEq { n.val.st with saved_grades := sg, t := t, s := (Setup.toSpec S).C.slotOf t }
          out.1.val.st ∧ ∀ B : NamedBlock V, NamedObject.block B ∉ out.2) ∨
      ∃ B : NamedBlock V, NamedObject.block B ∈ out.2 ∧
        TSEq (Member.receipt_process S
          { n.val.st with saved_grades := sg, t := t, s := (Setup.toSpec S).C.slotOf t } (.block B))
          out.1.val.st := by
  obtain ⟨sent, hrun, hsent⟩ := tick_out S v n t out hout
  obtain ⟨st0, st2, h0, hP1, hP0, he⟩ := tick_tseq_after_proposal hrun
  have e0 := (update_grades_ok h0).1
  refine ⟨st0.saved_grades, ?_⟩
  have hst1 : ({ st0 with t := t, s := (Setup.toSpec S).C.slotOf t } : Spec.Store V) = { n.val.st with saved_grades := st0.saved_grades, t := t, s := (Setup.toSpec S).C.slotOf t } := by
    rw [e0]
  by_cases hc : condP (Setup.toSpec S).C (Setup.toSpec S).P n.val t
  · obtain ⟨B, rfl, hB⟩ := hP1 hc
    right
    refine ⟨B.toProofNamed, ?_, ?_⟩
    · rw [hsent]
      exact List.mem_map_of_mem hB
    · rw [← hst1, ← on_block_eq_receipt]
      exact he
  · left
    rw [hP0 hc, hst1] at he
    refine ⟨he, ?_⟩
    intro B hB
    rw [hsent] at hB
    obtain ⟨o, ho, hoB⟩ := List.mem_map.mp hB
    rcases tick_sent hrun ho with ⟨B', rfl, hc'⟩ | ⟨u, rfl, -⟩ | ⟨row, rfl, -⟩
    · exact hc hc'
    · simp only [Spec.NamedObject.toProof, reduceCtorEq] at hoB
    · simp only [Spec.NamedObject.toProof, reduceCtorEq] at hoB

/-- A block the store admits has its slot's proposer, a parent of an earlier slot, and attestations
    of no later round than its slot's. -/
theorem shaped_of_admissible (S : Setup V) {st : Spec.Store V}
    {X : Spec.Block V}
    (h : Spec.Protocol.block_admissible (Spec.Config.toSpec S.E S.hc S.cfg)
      (Spec.Provisional.toSpec S.E) st X = true) :
    X.toProof.proposer? = some (S.E.proposer X.toProof.slot) ∧
      X.toProof.parent.slot < X.toProof.slot ∧
      (Model.spec (V := V)).carried_attestations_admissible S.hc X.toProof = true := by
  obtain ⟨-, hia, -, -, hprop, hps⟩ := (SubtypeEqualities.block_admissible_iff _ _ _ _).mp h
  refine ⟨?_, ?_, ?_⟩
  · rw [SubtypeEqualities.toProof_proposer?, SubtypeEqualities.toProof_slot, hprop]
    rfl
  · rw [SubtypeEqualities.toProof_parent, SubtypeEqualities.toProof_slot,
      SubtypeEqualities.toProof_slot]
    exact hps
  · show Member.carried_attestations_admissible S.hc X.toProof = true
    rw [HandlersFacts.image_carried_attestations_admissible,
      toProof_carried_attestations_admissible S.E S.hc S.cfg]
    exact hia

/-- The field `treeBlockShapedStep_node_tick` of `NodeFacts` at `Model.spec`: if every
    non-genesis block of `n`'s tree names its slot's proposer, has a parent of a strictly earlier
    slot and carries only admissible attestations, so does every non-genesis block of the tree of an
    outcome of `v`'s tick at `t` from `n`. -/
theorem spec_treeBlockShapedStep_node_tick :
    ∀ (S : Setup V) (v : V) (n : (Model.spec (V := V)).N) (t : Int)
        (out : (Model.spec (V := V)).N × List (NamedObject V)) (hout : (Model.spec (V := V)).tick S v n t ⇢ out),
        (∀ B : Block V, B ∈ n.st.core.T → B ≠ Block.genesis →
          B.proposer? = some (S.E.proposer B.slot) ∧ B.parent.slot < B.slot ∧
            (Model.spec (V := V)).carried_attestations_admissible S.hc B = true) →
        ∀ B : Block V, B ∈ out.1.st.core.T → B ≠ Block.genesis →
          B.proposer? = some (S.E.proposer B.slot) ∧ B.parent.slot < B.slot ∧
            (Model.spec (V := V)).carried_attestations_admissible S.hc B = true := by
  intro S v n t out hout hold B hB hne
  have hB' : B ∈ out.1.val.st.T.image Spec.Block.toProof := hB
  obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hB'
  have hn : X ∈ n.val.st.T → _ := fun h => hold X.toProof (Finset.mem_image_of_mem _ h) hne
  obtain ⟨sg, ⟨he, -⟩ | ⟨B0, -, he⟩⟩ := tick_shape S v n t out hout
  · rw [he.1] at hX; exact hn hX
  · rw [he.1] at hX
    rcases SubtypeEqualities.receipt_cases S _ (.block B0) with ⟨hT', -⟩ | ⟨B1, -, hadm, hT', -⟩
    · rw [hT'] at hX; exact hn hX
    · rw [hT'] at hX
      rcases Finset.mem_union.mp hX with hX | hX
      · exact hn hX
      · rw [Finset.mem_singleton.mp hX]
        exact shaped_of_admissible S hadm

/-- The field `treeBlockShapedStep_node_process` of `NodeFacts` at `Model.spec`: if every
    non-genesis block of `n`'s tree names its slot's proposer, has a parent of a strictly earlier
    slot and carries only admissible attestations, so does every non-genesis block of the tree of a
    node state `n`'s receipt of `o` returns. -/
theorem spec_treeBlockShapedStep_node_process :
    ∀ (S : Setup V) (n : (Model.spec (V := V)).N) (o : NamedObject V) (n' : (Model.spec (V := V)).N)
        (hn' : (Model.spec (V := V)).process S n o ⇢ n'),
        (∀ B : Block V, B ∈ n.st.core.T → B ≠ Block.genesis →
          B.proposer? = some (S.E.proposer B.slot) ∧ B.parent.slot < B.slot ∧
            (Model.spec (V := V)).carried_attestations_admissible S.hc B = true) →
        ∀ B : Block V, B ∈ n'.st.core.T → B ≠ Block.genesis →
          B.proposer? = some (S.E.proposer B.slot) ∧ B.parent.slot < B.slot ∧
            (Model.spec (V := V)).carried_attestations_admissible S.hc B = true := by
  intro S n o n' hn' hold B hB hne
  have hB' : B ∈ n'.val.st.T.image Spec.Block.toProof := hB
  rw [process_val_st S n o n' hn', mgc_eq] at hB'
  obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hB'
  change X ∈ (Member.receipt_process S n.val.st o).T at hX
  have hn : X ∈ n.val.st.T → _ := fun h => hold X.toProof (Finset.mem_image_of_mem _ h) hne
  rcases SubtypeEqualities.receipt_cases S n.val.st o with ⟨hT', -⟩ | ⟨B1, -, hadm, hT', -⟩
  · rw [hT'] at hX; exact hn hX
  · rw [hT'] at hX
    rcases Finset.mem_union.mp hX with hX | hX
    · exact hn hX
    · rw [Finset.mem_singleton.mp hX]
      exact shaped_of_admissible S hadm

/-- The field `tick_new_body_origin` of `NodeFacts` at `Model.spec`: a named block that is
    among the bodies of an outcome of `v`'s tick at `t` from `n` and not among `n`'s is sent by that
    outcome. -/
theorem spec_tick_new_body_origin :
    ∀ (S : Setup V) (v : V) (n : (Model.spec (V := V)).N) (t : Time)
        (out : (Model.spec (V := V)).N × List (NamedObject V)) (hout : (Model.spec (V := V)).tick S v n t ⇢ out) (B : NamedBlock V)
        (hpre : B ∉ n.st.bodies) (hpost : B ∈ out.1.st.bodies),
        NamedObject.block B ∈ out.2 := by
  intro S v n t out hout B hpre hpost
  have hpost' : B ∈ out.1.val.st.T.map Spec.Block.toProofNamedEmb := hpost
  obtain ⟨X, hX, rfl⟩ := Finset.mem_map.mp hpost'
  have hXn : X ∉ n.val.st.T := fun h => hpre (Finset.mem_map_of_mem _ h)
  obtain ⟨sg, ⟨he, -⟩ | ⟨B0, hB0, he⟩⟩ := tick_shape S v n t out hout
  · rw [he.1] at hX; exact absurd hX hXn
  · rw [he.1] at hX
    rcases SubtypeEqualities.receipt_cases S _ (.block B0) with ⟨hT', -⟩ | ⟨B1, hB1, hadm, hT', -⟩
    · rw [hT'] at hX; exact absurd hX hXn
    · rw [hT'] at hX
      rcases Finset.mem_union.mp hX with hX | hX
      · exact absurd hX hXn
      · cases hB1
        rw [Finset.mem_singleton.mp hX, Spec.Block.coe_toProofNamedEmb,
          Spec.Block.toProofNamed_toSpecNamed]
        exact hB0

omit [Inhabited V] in
/-- An attestation the tick sends is the one its attestation step built on the node's signing
    history, and the tick's signing history is the one that step returned. -/
theorem tick_attest {C : Spec.Config} {P : Spec.Provisional V}
    {X : Spec.External V} {n n' : Spec.NodeState V}
    {t : Spec.Time} {sent : List (Spec.NamedObject V)}
    (h : (Spec.tick C P X n t).run [] = .ok (n', sent))
    {row : Spec.Attestation V} (hrow : Spec.NamedObject.attest row ∈ sent) :
    ∃ st4 : Spec.Store V, Spec.Protocol.build_attestation C n.v st4
      n.signingHistory = .ok (n'.signingHistory, row) := by
  obtain ⟨st0, st2, st3, st4, st5, sh5, l1, l2, -, hP1, hP0, hV1, hV0, -, -, hA1, hA0, rfl⟩ :=
    tick_steps h
  have hl1 : ∀ o ∈ l1, ∃ B, o = Spec.NamedObject.block B := by
    intro o ho
    by_cases hc : condP C P n t
    · obtain ⟨B, -, rfl⟩ := hP1 hc
      exact ⟨B, List.mem_singleton.mp ho⟩
    · rw [(hP0 hc).2] at ho; exact absurd ho List.not_mem_nil
  have hl2 : Spec.NamedObject.attest row ∉ l2 := by
    intro ho
    have key : ∀ o ∈ l2, (∃ B, o = Spec.NamedObject.block B) ∨
        ∃ u, o = Spec.NamedObject.gfVote u := by
      intro o ho
      by_cases hv : condV C n t
      · rcases hV1 hv with ⟨-, rfl⟩ | ⟨u, -, rfl, -⟩
        · exact Or.inl (hl1 o ho)
        · rcases List.mem_append.mp ho with ho | ho
          · exact Or.inl (hl1 o ho)
          · exact Or.inr ⟨u, List.mem_singleton.mp ho⟩
      · rw [(hV0 hv).2] at ho; exact Or.inl (hl1 o ho)
    rcases key _ ho with ⟨B, hB⟩ | ⟨u, hu⟩
    · cases hB
    · cases hu
  by_cases ha : condA C n t
  · obtain ⟨row', hb, -, rfl⟩ := hA1 ha
    rcases List.mem_append.mp hrow with hm | hm
    · exact absurd hm hl2
    · cases List.mem_singleton.mp hm
      exact ⟨st4, hb⟩
  · rw [(hA0 ha).2.2] at hrow
    exact absurd hrow hl2

/-- An attestation an outcome of the member `tick` sends is the one the spec's `Protocol.create`
    signs on the node's signing history, and the outcome's signing history is the one `create`
    returns. -/
theorem tick_attest_mem (S : Setup V) (v : V) (n : (Model.spec (V := V)).N) (t : Time)
    (out : (Model.spec (V := V)).N × List (NamedObject V))
    (hout : (Model.spec (V := V)).tick S v n t ⇢ out) {a : NamedAttestation V}
    (ha : NamedObject.attest a ∈ out.2) :
    ∃ x : Spec.Protocol.AttestationInput V,
      out.1.val.signingHistory = (Spec.Protocol.create n.val.signingHistory x).1 ∧
      a = (Spec.Protocol.create n.val.signingHistory x).2.toProofNamed := by
  obtain ⟨sent, hrun, hsent⟩ := tick_out S v n t out hout
  rw [hsent] at ha
  obtain ⟨o, ho, hoa⟩ := List.mem_map.mp ha
  rcases tick_sent hrun ho with ⟨B, rfl, -⟩ | ⟨u, rfl, -⟩ | ⟨row, rfl, -⟩
  · simp only [Spec.NamedObject.toProof, reduceCtorEq] at hoa
  · simp only [Spec.NamedObject.toProof, reduceCtorEq] at hoa
  · obtain ⟨st4, hb⟩ := tick_attest hrun ho
    simp only [Spec.Protocol.build_attestation] at hb
    obtain ⟨x, -, hb⟩ := dre_bind_ok hb
    have hb' : Spec.Protocol.create n.val.signingHistory x =
        (out.1.val.signingHistory, row) := by
      have := hb
      simp only [pure, Except.pure, Except.ok.injEq] at this
      exact this
    refine ⟨x, by rw [hb'], ?_⟩
    rw [hb']
    simp only [Spec.NamedObject.toProof, NamedObject.attest.injEq] at hoa
    exact hoa.symm

/-- The field `finalitySafeAt_on_tick_emit` of `NodeFacts` at `Model.spec`: if `n`'s signing
    record has no timeout entry at height `h` and holds the lock `T` at `h`, so does the signing
    record of every outcome of `v`'s tick at `t` from `n`. -/
theorem spec_finalitySafeAt_on_tick_emit :
    ∀ (S : Setup V) (v : V) (n : (Model.spec (V := V)).N) (t : Time) {h : Height}
        {T : BlockId} (hs : n.record.legacy.timeout h = false ∧ n.record.legacy.lock h = some T)
        (out : (Model.spec (V := V)).N × List (NamedObject V)) (hout : (Model.spec (V := V)).tick S v n t ⇢ out),
        out.1.record.legacy.timeout h = false ∧ out.1.record.legacy.lock h = some T := by
  intro S v n t h T hs out hout
  show (Spec.NodeState.signingHistory out.1.val).toProof.legacy.timeout h = false ∧
    (Spec.NodeState.signingHistory out.1.val).toProof.legacy.lock h = some T
  rcases tick_signing (v := v) (t := t) (n := n.val) (out := (out.1.val, out.2)) hout with
    heq | ⟨x, heq, -⟩
  · rw [heq]; exact hs
  · rw [heq, (toProof_create n.val.signingHistory x).1]
    simp only [Protocol.NamedRecord.create, Protocol.NamedRecord.legacyCreate]
    exact Proofs.HealingSurface.create_attestation_finalitySafeAt_mono _ _ _ _ _ _ _ _ hs

/-- The field `on_tick_emit_finalitySafeAt_of_mem` of `NodeFacts` at `Model.spec`: if an
    outcome of `v`'s tick at `t` from `n` sends an attestation with finality pair `(h, T)`, its
    signing record has no timeout entry at `h` and holds the lock `T` at `h`. -/
theorem spec_on_tick_emit_finalitySafeAt_of_mem :
    ∀ (S : Setup V) (v : V) (n : (Model.spec (V := V)).N) (t : Time)
        (out : (Model.spec (V := V)).N × List (NamedObject V)) (hout : (Model.spec (V := V)).tick S v n t ⇢ out)
        {a : NamedAttestation V} (hmem : NamedObject.attest a ∈ out.2) {h : Height} {T : BlockId}
        (hfp : a.finality_pair = some ⟨h, T⟩),
        out.1.record.legacy.timeout h = false ∧ out.1.record.legacy.lock h = some T := by
  intro S v n t out hout a hmem h T hfp
  obtain ⟨x, hsh, rfl⟩ := tick_attest_mem S v n t out hout hmem
  show (Spec.NodeState.signingHistory out.1.val).toProof.legacy.timeout h = false ∧
    (Spec.NodeState.signingHistory out.1.val).toProof.legacy.lock h = some T
  rw [hsh, (toProof_create n.val.signingHistory x).1]
  rw [(toProof_create n.val.signingHistory x).2] at hfp
  simp only [Protocol.NamedRecord.create, Protocol.NamedRecord.legacyCreate,
    Protocol.NamedRecord.encodeRow] at hfp ⊢
  exact Proofs.HealingSurface.create_attestation_finalitySafeAt _ _ _ _ _ _ _ _ hfp

/-- The field `on_tick_emit_timeout_true_of_mem` of `NodeFacts` at `Model.spec`: if an outcome
    of `v`'s tick at `t` from `n` sends an attestation whose height pair is the timeout at `h`, its
    signing record holds a timeout entry at `h`. -/
theorem spec_on_tick_emit_timeout_true_of_mem :
    ∀ (S : Setup V) (v : V) (n : (Model.spec (V := V)).N) (t : Time)
        (out : (Model.spec (V := V)).N × List (NamedObject V)) (hout : (Model.spec (V := V)).tick S v n t ⇢ out)
        {a : NamedAttestation V} (hmem : NamedObject.attest a ∈ out.2) {h : Height}
        (hhp : a.erase.height_pair = HeightPair.timeout h),
        out.1.record.legacy.timeout h = true := by
  intro S v n t out hout a hmem h hhp
  obtain ⟨x, hsh, rfl⟩ := tick_attest_mem S v n t out hout hmem
  show (Spec.NodeState.signingHistory out.1.val).toProof.legacy.timeout h = true
  rw [hsh, (toProof_create n.val.signingHistory x).1, Proofs.NamedRecord.create_legacy_records_erasure]
  rw [(toProof_create n.val.signingHistory x).2] at hhp
  exact Proofs.HealingSurface.record_attestation_timeout_true _ _ hhp

/-! ## The attestations a step newly holds are stamped at the step's clock -/

/-- `RowsAt c a b`: `b` holds every attestation of `a`, every SG stamp of `b` is `a`'s or `c`, and
    every attestation `b` holds in a round and `a` does not has its SG vote stamped `c`. -/
def RowsAt (c : Spec.Time) (a b : Spec.Store V) : Prop :=
  (∀ w, b.timestamp_sg_vote w = a.timestamp_sg_vote w ∨ b.timestamp_sg_vote w = some (c : Stamp)) ∧
    (∀ r x, x ∈ b.sg_pool r → x ∉ a.sg_pool r →
      b.timestamp_sg_vote (Spec.Protocol.sgVote x) = some (c : Stamp)) ∧
    (∀ r, a.sg_pool r ⊆ b.sg_pool r)

omit [Fintype V] [Inhabited V] in
theorem RowsAt.of_eq {c : Spec.Time} {a b : Spec.Store V}
    (h1 : b.attestations = a.attestations) (h2 : b.timestamp_sg_vote = a.timestamp_sg_vote) :
    RowsAt c a b := by
  have hp : ∀ r, b.sg_pool r = a.sg_pool r := fun r => by
    simp only [Spec.Store.sg_pool, StoreSteps.getElem_fn, h1]
  refine ⟨fun w => Or.inl (by rw [h2]), fun r x hx hn => absurd (hp r ▸ hx) hn,
    fun r => (hp r).symm ▸ subset_refl _⟩

omit [Fintype V] [Inhabited V] in
theorem RowsAt.trans {c : Spec.Time} {a b d : Spec.Store V}
    (h1 : RowsAt c a b) (h2 : RowsAt c b d) : RowsAt c a d := by
  refine ⟨fun w => ?_, fun r x hx hn => ?_, fun r => subset_trans (h1.2.2 r) (h2.2.2 r)⟩
  · rcases h2.1 w with e | e
    · rw [e]; exact h1.1 w
    · exact Or.inr e
  · by_cases hb : x ∈ b.sg_pool r
    · have e1 := h1.2.1 r x hb hn
      rcases h2.1 (Spec.Protocol.sgVote x) with e | e
      · rw [e, e1]
      · exact e
    · exact h2.2.1 r x hx hb

omit [Inhabited V] in
/-- The spec's `admit_attestation` adds at most the attestation, stamped at the store's clock. -/
theorem rowsAt_admit (C : Spec.Config) (st : Spec.Store V)
    (row : Spec.Attestation V) :
    RowsAt st.t st (Spec.Protocol.admit_attestation C st row) := by
  rcases StoreSteps.admit_attestation_cases C st row with e | ⟨-, e⟩
  · rw [e]; exact RowsAt.of_eq rfl rfl
  · rw [e]
    refine ⟨fun w => ?_, fun r x hx hn => ?_, fun r y hy => ?_⟩
    · by_cases hw : w = Spec.Protocol.sgVote row
      · right; rw [hw]; exact Function.update_self _ _ _
      · left; exact Function.update_of_ne hw _ _
    · simp only [Spec.Store.sg_pool, StoreSteps.getElem_fn, List.mem_toFinset] at hx hn
      by_cases hr : r = row.round
      · subst hr
        rw [Function.update_self, List.mem_append] at hx
        rcases hx with hx | hx
        · exact absurd hx hn
        · rw [List.mem_singleton.mp hx]; exact Function.update_self _ _ _
      · rw [Function.update_of_ne hr] at hx; exact absurd hx hn
    · simp only [Spec.Store.sg_pool, StoreSteps.getElem_fn, List.mem_toFinset] at hy ⊢
      by_cases hr : r = row.round
      · subst hr; rw [Function.update_self]; exact List.mem_append_left _ hy
      · rw [Function.update_of_ne hr]; exact hy

omit [Inhabited V] in
/-- The spec's `admit_attestations` adds attestations only, each stamped at the store's clock. -/
theorem rowsAt_admits (C : Spec.Config) (rows : List (Spec.Attestation V))
    (st : Spec.Store V) :
    RowsAt st.t st (Spec.Protocol.admit_attestations C st rows) := by
  rw [StoreSteps.admit_attestations_foldl]
  induction rows generalizing st with
  | nil => exact RowsAt.of_eq rfl rfl
  | cons row rs ih =>
    simp only [List.foldl_cons]
    have h1 := rowsAt_admit C st row
    have ht : (Spec.Protocol.admit_attestation C st row).t = st.t := by
      obtain ⟨x, y, e⟩ := StoreSteps.admit_attestation_writes C st row
      rw [e]
    have h2 := ih (Spec.Protocol.admit_attestation C st row)
    rw [ht] at h2
    exact h1.trans h2

omit [Inhabited V] in
/-- The spec's `on_block` adds attestations only, each stamped at the store's clock. -/
theorem rowsAt_on_block (C : Spec.Config) (P : Spec.Provisional V)
    (st : Spec.Store V) (B : Spec.Block V) :
    RowsAt st.t st (Spec.Protocol.on_block C P st B) := by
  rcases StoreSteps.on_block_shape C P st B with e | ⟨-, σ', e⟩
  · rw [e]; exact RowsAt.of_eq rfl rfl
  · rw [e]
    obtain ⟨k1, -, -, k4, k5⟩ := StoreSteps.block_core_keeps P st B σ'
    have h1 : RowsAt st.t st (Spec.Protocol.update_finality
        (B.gf_votes.foldl (Spec.Protocol.on_goldfish_vote_checked P)
          { st with σ := Function.update st.σ B σ', T := st.T ∪ {B},
                    timestamp_block := Function.update st.timestamp_block B (some (st.t : Stamp)) })
        B) := RowsAt.of_eq k4 k5
    have h2 := rowsAt_admits C B.attestations (Spec.Protocol.update_finality
        (B.gf_votes.foldl (Spec.Protocol.on_goldfish_vote_checked P)
          { st with σ := Function.update st.σ B σ', T := st.T ∪ {B},
                    timestamp_block := Function.update st.timestamp_block B (some (st.t : Stamp)) })
        B)
    rw [k1] at h2
    exact h1.trans h2

omit [Inhabited V] in
/-- The spec's receipt of an object adds attestations only, each stamped at the store's clock. -/
theorem rowsAt_receipt (S : Setup V) (st : Spec.Store V) (o : NamedObject V) :
    RowsAt st.t st (Member.receipt_process S st o) := by
  cases o with
  | block B => exact rowsAt_on_block _ _ _ _
  | gfVote u =>
    obtain ⟨gv, tv, e⟩ := receipt_gfVote_frame S st u
    rw [e]; exact RowsAt.of_eq rfl rfl
  | attest a => exact rowsAt_admit _ _ _

/-- The field `rawRelay_tick_outcome_data` of `NodeFacts` at `Model.spec`: if `t ≤ bound`,
    `n`'s named store is coherent, its clock is at most `bound`, and every named attestation in its
    rows of round `k` has round `k` and a receipt stamp at most `bound`, then the same holds of the
    named store of every outcome of `v`'s tick at `t` from `n`. -/
theorem spec_rawRelay_tick_outcome_data :
    ∀ (S : Setup V) (v : V) (n : (Model.spec (V := V)).N) (t : Time)
        (out : (Model.spec (V := V)).N × List (NamedObject V)) (hout : (Model.spec (V := V)).tick S v n t ⇢ out) (bound : Time),
        t ≤ bound → Restated.Vocabulary.Proofs.NamedStore.Coherent (Model.spec (V := V)) S.E S.cfg n.st →
        (n.st.core.t ≤ bound ∧ ∀ k (a : NamedAttestation V), a ∈ n.st.sg_rows k →
          a.round = k ∧ ∃ stamp : Time, stamp ≤ bound ∧
            n.st.core.timestamp_sg_vote ((Model.spec (V := V)).sgVote a.erase) = some (stamp : Stamp)) →
        (out.1.st.core.t ≤ bound ∧ ∀ k (a : NamedAttestation V), a ∈ out.1.st.sg_rows k →
          a.round = k ∧ ∃ stamp : Time, stamp ≤ bound ∧
            out.1.st.core.timestamp_sg_vote ((Model.spec (V := V)).sgVote a.erase) = some (stamp : Stamp)) := by
  intro S v n t out hout bound htb _ hst
  obtain ⟨ht, hrows⟩ := hst
  have hI : StoreSteps.RowsErasuresHeld n.val.st := fun r b hb =>
    (hrows r b.toProofNamed ((HandlersRunFacts.mem_sg_rows_iff n.val.st r b).2 hb)).1
  have hB : StoreSteps.StampsBounded bound n.val.st := by
    refine ⟨ht, fun k a ha => ?_⟩
    obtain ⟨-, s, hs, hst⟩ := hrows k a.toProofNamed ((HandlersRunFacts.mem_sg_rows_iff n.val.st k a).2 ha)
    exact ⟨s, hs, by rwa [HandlersRunFacts.stamp_sgVote_toProofNamed_erase_ok] at hst⟩
  obtain ⟨sent, hrun, -⟩ := tick_out S v n t out hout
  have hreach := StoreSteps.tick_reach _ _ _ n.val out.1.val t [] sent hrun
  obtain ⟨hI', hB'⟩ := StoreSteps.reach_bounded bound htb hreach hI hB
  refine ⟨hB'.1, fun k a ha => ?_⟩
  obtain ⟨a', rfl⟩ := HandlersFacts.exists_namedAtt a
  have ha' := (HandlersRunFacts.mem_sg_rows_iff out.1.val.st k a').1 ha
  refine ⟨hI' k a' ha', ?_⟩
  obtain ⟨s, hs, hst'⟩ := hB'.2 k a' ha'
  refine ⟨s, hs, ?_⟩
  rw [HandlersRunFacts.stamp_sgVote_toProofNamed_erase_ok]
  exact hst'

/-- The field `node_tick_sg_row_stamp` of `NodeFacts` at `Model.spec`: a named attestation that
    is among the rows of its round in an outcome of `v`'s tick at `t` from `n`, and not among `n`'s,
    has SG vote stamp `t` in the outcome's store. -/
theorem spec_node_tick_sg_row_stamp :
    ∀ (S' : Setup V) (v : V) (n : (Model.spec (V := V)).N) (t : Int)
        (out : (Model.spec (V := V)).N × List (NamedObject V)) (hout : (Model.spec (V := V)).tick S' v n t ⇢ out),
        DecoupledConsensusModel.Sts.Restated.Vocabulary.Proofs.NamedStore.Coherent (Model.spec (V := V)) S'.E S'.cfg n.st →
        ∀ a : NamedAttestation V, a ∉ n.st.sg_rows a.round → a ∈ out.1.st.sg_rows a.round →
          out.1.st.core.timestamp_sg_vote ((Model.spec (V := V)).sgVote a.erase) = some (t : Stamp) := by
  intro S v n t out hout _ a h0 h1
  obtain ⟨a', rfl⟩ := HandlersFacts.exists_namedAtt a
  have h0' : a' ∉ n.val.st.sg_pool a'.toProofNamed.round :=
    fun h => h0 ((HandlersRunFacts.mem_sg_rows_iff n.val.st _ a').2 h)
  have h1' := (HandlersRunFacts.mem_sg_rows_iff out.1.val.st _ a').1 h1
  rw [HandlersRunFacts.stamp_sgVote_toProofNamed_erase_ok]
  obtain ⟨sent, hrun, -⟩ := tick_out S v n t out hout
  obtain ⟨st0, st2, st3, st4, st5, sh5, l1, l2, h0g, hP1, hP0, hV1, hV0, hC1, hC0, hA1, hA0, hn'⟩ :=
    tick_steps hrun
  have e0 := (update_grades_ok h0g).1
  have r1 : RowsAt t n.val.st { st0 with t := t, s := (Setup.toSpec S).C.slotOf t } := by
    rw [e0]; exact RowsAt.of_eq rfl rfl
  have k2 : st2.t = t ∧ RowsAt t { st0 with t := t, s := (Setup.toSpec S).C.slotOf t } st2 := by
    by_cases hc : condP (Setup.toSpec S).C (Setup.toSpec S).P n.val t
    · obtain ⟨B, rfl, -⟩ := hP1 hc
      exact ⟨(keeps_on_block _ _ _ _).1, rowsAt_on_block _ _ _ _⟩
    · rw [(hP0 hc).1]; exact ⟨rfl, RowsAt.of_eq rfl rfl⟩
  have k3 : st3.t = st2.t ∧ RowsAt t st2 st3 := by
    by_cases hv : condV (Setup.toSpec S).C n.val t
    · rcases hV1 hv with ⟨rfl, -⟩ | ⟨u, rfl, -⟩
      · exact ⟨rfl, RowsAt.of_eq rfl rfl⟩
      · obtain ⟨gv, tv, e⟩ := on_goldfish_vote_checked_frame (Setup.toSpec S).P st2 u
        rw [e]; exact ⟨rfl, RowsAt.of_eq rfl rfl⟩
    · rw [(hV0 hv).1]; exact ⟨rfl, RowsAt.of_eq rfl rfl⟩
  have k4 : st4.t = st3.t ∧ RowsAt t st3 st4 := by
    by_cases hcc : condC (Setup.toSpec S).C n.val t
    · rw [update_confirmation_ok (hC1 hcc)]; exact ⟨rfl, RowsAt.of_eq rfl rfl⟩
    · rw [hC0 hcc]; exact ⟨rfl, RowsAt.of_eq rfl rfl⟩
  have k5 : RowsAt t st4 st5 := by
    by_cases ha : condA (Setup.toSpec S).C n.val t
    · obtain ⟨row, -, rfl, -⟩ := hA1 ha
      have := rowsAt_admit (Setup.toSpec S).C st4 row
      rw [k4.1, k3.1, k2.1] at this
      exact this
    · rw [(hA0 ha).1]; exact RowsAt.of_eq rfl rfl
  have hall : RowsAt t n.val.st out.1.val.st := by
    rw [hn']
    exact r1.trans (k2.2.trans (k3.2.trans (k4.2.trans (k5.trans (RowsAt.of_eq rfl rfl)))))
  exact hall.2.1 _ a' h1' h0'

/-- The field `receipt_process_sg_row_stamp` of `NodeFacts` at `Model.spec`: a named
    attestation that the receipt of `o` on `st` newly holds among the rows of its round has SG vote
    stamp equal to the clock of `st`. -/
theorem spec_receipt_process_sg_row_stamp :
    ∀ (S' : Setup V) (st : (Model.spec (V := V)).NS) (o : NamedObject V)
        (a : NamedAttestation V), a ∉ st.sg_rows a.round →
        a ∈ ((Model.spec (V := V)).receipt_process S' st o).sg_rows a.round →
        ((Model.spec (V := V)).receipt_process S' st o).core.timestamp_sg_vote ((Model.spec (V := V)).sgVote a.erase) =
          some (st.core.t : Stamp) := by
  intro S st o a h0 h1
  obtain ⟨a', rfl⟩ := HandlersFacts.exists_namedAtt a
  have h0' : a' ∉ st.val.sg_pool a'.toProofNamed.round :=
    fun h => h0 ((HandlersRunFacts.mem_sg_rows_iff st.val _ a').2 h)
  have h1' := (HandlersRunFacts.mem_sg_rows_iff (OkMember.receipt_process S st o).val _ a').1 h1
  rw [HandlersRunFacts.stamp_sgVote_toProofNamed_erase_ok]
  show Spec.Store.timestamp_sg_vote (OkMember.receipt_process S st o).val
    (Spec.Protocol.sgVote a') = some (st.val.t : Stamp)
  by_cases hheld : objectRootHeldByOther st.val.T o
  · rw [OkMember.receipt_process_of_held hheld] at h1'
    exact absurd h1' h0'
  · rw [OkMember.receipt_process_val_of_not_held hheld] at h1' ⊢
    exact (rowsAt_receipt S st.val o).2.1 _ a' h1' h0'

/-! ## The Goldfish votes a step adds -/

/-- `DPool st`: every vote of slot `k`'s list is of slot `k`, every listed vote is stamped, every
stamped vote is listed in its slot, and no stamp is later than the clock. -/
def DPool (st : Spec.Store V) : Prop :=
  (∀ (k : Spec.Slot) (x : Spec.GoldfishVote V), x ∈ st.gf_votes k → x.slot = k) ∧
    (∀ (k : Spec.Slot) (x : Spec.GoldfishVote V), x ∈ st.gf_votes k →
      (st.timestamp_vote x).isSome = true) ∧
    (∀ x : Spec.GoldfishVote V, (st.timestamp_vote x).isSome = true →
      x ∈ st.gf_votes x.slot) ∧
    (∀ (x : Spec.GoldfishVote V) (c : Stamp), st.timestamp_vote x = some c →
      c ≤ (st.t : Stamp))

/-- `VIns P a b`: `b` has `a`'s clock and slot; and when `a` meets `DPool`, so does `b`, `b` keeps
    every vote and stamp of `a`, and every vote `b` newly lists is stamped at `a`'s clock, is of a
    slot at most `a`'s, and is signed by a member of its slot's committee under `P`. -/
def VIns (P : Spec.Provisional V) (a b : Spec.Store V) : Prop :=
  b.t = a.t ∧ b.s = a.s ∧ (DPool a → DPool b ∧
    (∀ (k : Spec.Slot) (x : Spec.GoldfishVote V), x ∈ a.gf_votes k →
      x ∈ b.gf_votes k) ∧
    (∀ (x : Spec.GoldfishVote V) (c : Stamp), a.timestamp_vote x = some c →
      b.timestamp_vote x = some c) ∧
    (∀ x : Spec.GoldfishVote V, x ∉ a.gf_votes x.slot → x ∈ b.gf_votes x.slot →
      b.timestamp_vote x = some (a.t : Stamp) ∧ x.slot ≤ a.s ∧ x.val_index ∈ P.committee x.slot))

omit [Inhabited V] in
theorem VIns.of_eq {P : Spec.Provisional V} {a b : Spec.Store V}
    (h1 : b.gf_votes = a.gf_votes) (h2 : b.timestamp_vote = a.timestamp_vote) (h3 : b.t = a.t)
    (h4 : b.s = a.s) : VIns P a b := by
  refine ⟨h3, h4, fun hp => ⟨?_, fun k x hx => by rw [h1]; exact hx,
    fun x c hx => by rw [h2]; exact hx, fun x hx hx' => absurd (h1 ▸ hx') hx⟩⟩
  obtain ⟨p1, p2, p3, p4⟩ := hp
  refine ⟨fun k x hx => p1 k x (h1 ▸ hx), fun k x hx => h2 ▸ p2 k x (h1 ▸ hx),
    fun x hx => h1 ▸ p3 x (h2 ▸ hx), fun x c hx => h3 ▸ p4 x c (h2 ▸ hx)⟩

omit [Inhabited V] in
theorem VIns.trans {P : Spec.Provisional V} {a b d : Spec.Store V}
    (h1 : VIns P a b) (h2 : VIns P b d) : VIns P a d := by
  obtain ⟨t1, s1, k1⟩ := h1
  obtain ⟨t2, s2, k2⟩ := h2
  refine ⟨t2.trans t1, s2.trans s1, fun hp => ?_⟩
  obtain ⟨pb, m1, c1, n1⟩ := k1 hp
  obtain ⟨pd, m2, c2, n2⟩ := k2 pb
  refine ⟨pd, fun k x hx => m2 k x (m1 k x hx), fun x c hx => c2 x c (c1 x c hx),
    fun x hx hx' => ?_⟩
  by_cases hb : x ∈ b.gf_votes x.slot
  · obtain ⟨e, hs, hc⟩ := n1 x hx hb
    exact ⟨c2 x _ e, hs, hc⟩
  · obtain ⟨e, hs, hc⟩ := n2 x hb hx'
    rw [t1] at e; rw [s1] at hs
    exact ⟨e, hs, hc⟩

omit [Inhabited V] in
/-- The spec's checked vote admission leaves the store unchanged, or appends a vote from a committee
    member, of a slot at most the store's and not yet listed, stamped at the clock. -/
theorem on_goldfish_vote_checked_cases (P : Spec.Provisional V)
    (st : Spec.Store V) (u : Spec.GoldfishVote V) :
    Spec.Protocol.on_goldfish_vote_checked P st u = st ∨
      (u.val_index ∈ P.committee u.slot ∧ ¬ st.s < u.slot ∧ u ∉ st.gf_votes u.slot ∧
        Spec.Protocol.on_goldfish_vote_checked P st u =
          { st with gf_votes := Function.update st.gf_votes u.slot (st.gf_votes u.slot ++ [u]),
                    timestamp_vote := Function.update st.timestamp_vote u (some (st.t : Stamp)) }) := by
  unfold Spec.Protocol.on_goldfish_vote_checked Spec.Protocol.on_goldfish_vote
  simp only [Id.run, pure, StoreSteps.getElem_fn]
  split_ifs <;> first
    | exact Or.inl rfl
    | (right
       refine ⟨?_, ?_, ?_, rfl⟩ <;> simp_all)

omit [Inhabited V] in
/-- The spec's checked vote admission satisfies `VIns`. -/
theorem vIns_checked (P : Spec.Provisional V) (st : Spec.Store V)
    (u : Spec.GoldfishVote V) :
    VIns P st (Spec.Protocol.on_goldfish_vote_checked P st u) := by
  rcases on_goldfish_vote_checked_cases P st u with e | ⟨hc, hs, hn, e⟩
  · rw [e]; exact VIns.of_eq rfl rfl rfl rfl
  · rw [e]
    refine ⟨rfl, rfl, fun hp => ?_⟩
    obtain ⟨p1, p2, p3, p4⟩ := hp
    have hus : st.timestamp_vote u = none := by
      cases h : st.timestamp_vote u with
      | none => rfl
      | some c => exact absurd (p3 u (by rw [h]; rfl)) hn
    have memNew : ∀ k x, x ∈ Function.update st.gf_votes u.slot (st.gf_votes u.slot ++ [u]) k ↔
        x ∈ st.gf_votes k ∨ (k = u.slot ∧ x = u) := by
      intro k x
      by_cases hk : k = u.slot
      · subst hk
        rw [Function.update_self, List.mem_append, List.mem_singleton]
        simp
      · rw [Function.update_of_ne hk]
        simp [hk]
    refine ⟨⟨fun k x hx => ?_, fun k x hx => ?_, fun x hx => ?_, fun x c hx => ?_⟩,
      fun k x hx => (memNew k x).2 (Or.inl hx), fun x c hx => ?_, fun x hx hx' => ?_⟩
    · rcases (memNew k x).1 hx with hx | ⟨rfl, rfl⟩
      · exact p1 k x hx
      · rfl
    · show (Function.update st.timestamp_vote u (some (st.t : Stamp)) x).isSome = true
      by_cases hxu : x = u
      · subst hxu; rw [Function.update_self]; rfl
      · rw [Function.update_of_ne hxu]
        rcases (memNew k x).1 hx with hx | ⟨-, h⟩
        · exact p2 k x hx
        · exact absurd h hxu
    · change (Function.update st.timestamp_vote u (some (st.t : Stamp)) x).isSome = true at hx
      by_cases hxu : x = u
      · subst hxu; exact (memNew _ _).2 (Or.inr ⟨rfl, rfl⟩)
      · rw [Function.update_of_ne hxu] at hx
        exact (memNew _ _).2 (Or.inl (p3 x hx))
    · change Function.update st.timestamp_vote u (some (st.t : Stamp)) x = some c at hx
      by_cases hxu : x = u
      · subst hxu; rw [Function.update_self] at hx; cases hx; exact le_refl _
      · rw [Function.update_of_ne hxu] at hx; exact p4 x c hx
    · show Function.update st.timestamp_vote u (some (st.t : Stamp)) x = some c
      have hxu : x ≠ u := by rintro rfl; rw [hus] at hx; cases hx
      rw [Function.update_of_ne hxu]; exact hx
    · rcases (memNew _ _).1 hx' with h | ⟨-, rfl⟩
      · exact absurd h hx
      · exact ⟨Function.update_self _ _ _, not_lt.mp hs, hc⟩

omit [Inhabited V] in
/-- The checked admission of a list of votes, in order, satisfies `VIns`. -/
theorem vIns_fold (P : Spec.Provisional V) (votes : List (Spec.GoldfishVote V))
    (st : Spec.Store V) :
    VIns P st (votes.foldl (Spec.Protocol.on_goldfish_vote_checked P) st) := by
  induction votes generalizing st with
  | nil => exact VIns.of_eq rfl rfl rfl rfl
  | cons u us ih =>
    simp only [List.foldl_cons]
    exact (vIns_checked P st u).trans (ih _)

omit [Inhabited V] in
/-- The spec's `on_block` satisfies `VIns`. -/
theorem vIns_on_block (C : Spec.Config) (P : Spec.Provisional V)
    (st : Spec.Store V) (B : Spec.Block V) :
    VIns P st (Spec.Protocol.on_block C P st B) := by
  rcases StoreSteps.on_block_shape C P st B with e | ⟨-, σ', e⟩
  · rw [e]; exact VIns.of_eq rfl rfl rfl rfl
  · rw [e]
    generalize hX : ({ st with σ := Function.update st.σ B σ', T := st.T ∪ {B}, timestamp_block := Function.update st.timestamp_block B (some (st.t : Stamp)) } : Spec.Store V) = X
    have h1 : VIns P st X := by rw [← hX]; exact VIns.of_eq rfl rfl rfl rfl
    have h2 := vIns_fold P B.gf_votes X
    obtain ⟨a, b, c, d, e1⟩ := StoreSteps.update_finality_writes
      (B.gf_votes.foldl (Spec.Protocol.on_goldfish_vote_checked P) X) B
    rw [e1]
    obtain ⟨x, y, e2⟩ := StoreSteps.admit_attestations_writes C B.attestations { (B.gf_votes.foldl (Spec.Protocol.on_goldfish_vote_checked P) X) with h_max := a, J := b, h_j := c, F := d }
    rw [e2]
    exact h1.trans (h2.trans (VIns.of_eq rfl rfl rfl rfl))

omit [Inhabited V] in
/-- The spec's receipt of an object satisfies `VIns`. -/
theorem vIns_receipt (S : Setup V) (st : Spec.Store V) (o : NamedObject V) :
    VIns (Spec.Provisional.toSpec S.E) st (Member.receipt_process S st o) := by
  cases o with
  | block B => exact vIns_on_block _ _ _ _
  | gfVote u => exact vIns_checked _ _ _
  | attest a =>
    obtain ⟨x, y, e⟩ := StoreSteps.admit_attestation_writes
      (Spec.Config.toSpec S.E S.hc S.cfg) st (Spec.Attestation.toSpecNamed a)
    show VIns _ st (Spec.Protocol.admit_attestation _ st _)
    rw [e]; exact VIns.of_eq rfl rfl rfl rfl

omit [Fintype V] [Inhabited V] in
/-- A Goldfish vote of the record is in the image of a slot's list exactly when its spec form is in
    the list. -/
theorem mem_map_toProof_iff (L : List (Spec.GoldfishVote V))
    (u : DecoupledConsensusModel.GoldfishVote V) :
    u ∈ L.map Spec.GoldfishVote.toProof ↔ Spec.GoldfishVote.toSpec u ∈ L := by
  rw [List.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact hx
  · intro h; exact ⟨_, h, rfl⟩

omit [Inhabited V] in
/-- From its first store with the clock set, the tick satisfies `VIns`: it only adds votes, each
    stamped at `t`, of a slot at most `t`'s, signed by a committee member. -/
theorem tick_vIns {C : Spec.Config} {P : Spec.Provisional V}
    {X : Spec.External V} {n n' : Spec.NodeState V}
    {t : Spec.Time} {sent : List (Spec.NamedObject V)}
    (h : (Spec.tick C P X n t).run [] = .ok (n', sent)) :
    ∃ sg : Spec.SavedGrades V,
      VIns P { n.st with saved_grades := sg, t := t, s := C.slotOf t } n'.st := by
  obtain ⟨st0, st2, st3, st4, st5, sh5, l1, l2, h0, hP1, hP0, hV1, hV0, hC1, hC0, hA1, hA0, rfl⟩ :=
    tick_steps h
  refine ⟨st0.saved_grades, ?_⟩
  have e0 : ({ st0 with t := t, s := C.slotOf t } : Spec.Store V) = { n.st with saved_grades := st0.saved_grades, t := t, s := C.slotOf t } := by
    rw [(update_grades_ok h0).1]
  rw [← e0]
  have k2 : VIns P { st0 with t := t, s := C.slotOf t } st2 := by
    by_cases hc : condP C P n t
    · obtain ⟨B, rfl, -⟩ := hP1 hc
      exact vIns_on_block _ _ _ _
    · rw [(hP0 hc).1]; exact VIns.of_eq rfl rfl rfl rfl
  have k3 : VIns P st2 st3 := by
    by_cases hv : condV C n t
    · rcases hV1 hv with ⟨rfl, -⟩ | ⟨u, rfl, -⟩
      · exact VIns.of_eq rfl rfl rfl rfl
      · exact vIns_checked _ _ _
    · rw [(hV0 hv).1]; exact VIns.of_eq rfl rfl rfl rfl
  have k4 : VIns P st3 st4 := by
    by_cases hcc : condC C n t
    · rw [update_confirmation_ok (hC1 hcc)]; exact VIns.of_eq rfl rfl rfl rfl
    · rw [hC0 hcc]; exact VIns.of_eq rfl rfl rfl rfl
  have k5 : VIns P st4 st5 := by
    by_cases ha : condA C n t
    · obtain ⟨row, -, rfl, -⟩ := hA1 ha
      obtain ⟨x, y, e⟩ := StoreSteps.admit_attestation_writes C st4 row
      rw [e]; exact VIns.of_eq rfl rfl rfl rfl
    · rw [(hA0 ha).1]; exact VIns.of_eq rfl rfl rfl rfl
  exact k2.trans (k3.trans (k4.trans (k5.trans (VIns.of_eq rfl rfl rfl rfl))))

/-- `Restated.Vocabulary.Protocol.PoolStamps` at a store of the subtype gives `DPool` of its value. -/
theorem dpool_of_poolStamps (st : (Model.spec (V := V)).S)
    (h : Restated.Vocabulary.Protocol.PoolStamps (Model.spec (V := V)) st) : DPool st.val := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun k x hx => ?_, fun k x hx => ?_, fun x hx => ?_, fun x c hx => ?_⟩
  · exact h1 k x.toProof (List.mem_map_of_mem hx)
  · exact h2 k x.toProof (List.mem_map_of_mem hx)
  · have := h3 x.toProof hx
    exact (mem_map_toProof_iff _ _).1 this
  · exact h4 x.toProof c hx

/-- `DPool` of the value of a store of the subtype gives `Restated.Vocabulary.Protocol.PoolStamps` at
    that store. -/
theorem poolStamps_of_dpool (st : (Model.spec (V := V)).S) (h : DPool st.val) :
    Restated.Vocabulary.Protocol.PoolStamps (Model.spec (V := V)) st := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun k u hu => ?_, fun k u hu => ?_, fun u hu => ?_, fun u c hu => ?_⟩
  · exact h1 k _ ((mem_map_toProof_iff _ _).1 hu)
  · exact h2 k _ ((mem_map_toProof_iff _ _).1 hu)
  · exact (mem_map_toProof_iff _ _).2 (h3 _ hu)
  · exact h4 _ c hu

/-- `VIns` of the values of two stores of the subtype gives `Restated.Vocabulary.Protocol.PoolStep`
    between them, and the stamp and slot of every vote added. -/
theorem poolStep_of_vIns {P : Spec.Provisional V} {a b : (Model.spec (V := V)).S}
    (h : VIns P a.val b.val) :
    Restated.Vocabulary.Protocol.PoolStep (Model.spec (V := V)) a b ∧
      ∀ (_ : Restated.Vocabulary.Protocol.PoolStamps (Model.spec (V := V)) a)
        (u : DecoupledConsensusModel.GoldfishVote V), u ∉ a.gf_votes u.slot →
        u ∈ b.gf_votes u.slot → b.timestamp_vote u = some (a.t : Stamp) ∧ u.slot ≤ a.s ∧
          u.val_index ∈ P.committee u.slot := by
  obtain ⟨-, -, k⟩ := h
  refine ⟨fun hps => ?_, fun hps u hu hu' => ?_⟩
  · obtain ⟨pd, m, c, -⟩ := k (dpool_of_poolStamps a hps)
    refine ⟨⟨fun k u hu => ?_, fun u c' hu => c _ c' hu⟩, poolStamps_of_dpool b pd⟩
    exact (mem_map_toProof_iff _ _).2 (m k _ ((mem_map_toProof_iff _ _).1 hu))
  · obtain ⟨-, -, -, nw⟩ := k (dpool_of_poolStamps a hps)
    exact nw _ (fun h' => hu ((mem_map_toProof_iff _ _).2 h'))
      ((mem_map_toProof_iff _ _).1 hu')

/-! ## What the store type's receipt keeps and adds -/

omit [DecidableEq V] [Fintype V] [Inhabited V] in
/-- Two spec blocks with one image have one root. -/
theorem root_eq_of_toProof_eq {X Y : Spec.Block V} (h : X.toProof = Y.toProof) :
    X.root = Y.root := by
  have h1 : X.toProof.root = Y.toProof.root := by rw [h]
  rw [Spec.Block.toProof_root, Spec.Block.toProof_root] at h1
  cases hx : X.root
  cases hy : Y.root
  rw [hx, hy] at h1
  cases h1
  rfl

omit [Inhabited V] in
/-- The checked vote admission keeps every listed vote. -/
theorem votes_mono_checked (P : Spec.Provisional V) (st : Spec.Store V)
    (u : Spec.GoldfishVote V) (k : Spec.Slot) (x : Spec.GoldfishVote V)
    (hx : x ∈ st.gf_votes k) : x ∈ (Spec.Protocol.on_goldfish_vote_checked P st u).gf_votes k := by
  rcases on_goldfish_vote_checked_cases P st u with e | ⟨-, -, -, e⟩
  · rw [e]; exact hx
  · rw [e]
    show x ∈ Function.update st.gf_votes u.slot (st.gf_votes u.slot ++ [u]) k
    by_cases hk : k = u.slot
    · subst hk; rw [Function.update_self]; exact List.mem_append_left _ hx
    · rw [Function.update_of_ne hk]; exact hx

omit [Inhabited V] in
/-- The spec's receipt of an object keeps every listed vote. -/
theorem votes_mono_receipt (S : Setup V) (st : Spec.Store V) (o : NamedObject V)
    (k : Spec.Slot) (x : Spec.GoldfishVote V) (hx : x ∈ st.gf_votes k) :
    x ∈ (Member.receipt_process S st o).gf_votes k := by
  cases o with
  | block B =>
    show x ∈ (Spec.Protocol.on_block _ _ st _).gf_votes k
    rcases StoreSteps.on_block_shape (Spec.Config.toSpec S.E S.hc S.cfg)
      (Spec.Provisional.toSpec S.E) st (Spec.Block.toSpecNamed B) with e | ⟨-, σ', e⟩
    · rw [e]; exact hx
    · rw [e]
      generalize hX : ({ st with σ := Function.update st.σ (Spec.Block.toSpecNamed B) σ', T := st.T ∪ {Spec.Block.toSpecNamed B}, timestamp_block := Function.update st.timestamp_block (Spec.Block.toSpecNamed B) (some (st.t : Stamp)) } : Spec.Store V) = X
      have h1 : x ∈ X.gf_votes k := by rw [← hX]; exact hx
      have h2 : ∀ (votes : List (Spec.GoldfishVote V)) (Y : Spec.Store V),
          x ∈ Y.gf_votes k → x ∈ (votes.foldl (Spec.Protocol.on_goldfish_vote_checked
            (Spec.Provisional.toSpec S.E)) Y).gf_votes k := by
        intro votes
        induction votes with
        | nil => intro Y h; exact h
        | cons u us ih => intro Y h; exact ih _ (votes_mono_checked _ Y u k x h)
      have h3 := h2 (Spec.Block.toSpecNamed B).gf_votes X h1
      obtain ⟨a, b, c, d, e1⟩ := StoreSteps.update_finality_writes
        ((Spec.Block.toSpecNamed B).gf_votes.foldl
          (Spec.Protocol.on_goldfish_vote_checked (Spec.Provisional.toSpec S.E)) X)
        (Spec.Block.toSpecNamed B)
      rw [e1]
      obtain ⟨x', y', e2⟩ := StoreSteps.admit_attestations_writes (Spec.Config.toSpec S.E S.hc S.cfg) (Spec.Block.toSpecNamed B).attestations { ((Spec.Block.toSpecNamed B).gf_votes.foldl (Spec.Protocol.on_goldfish_vote_checked (Spec.Provisional.toSpec S.E)) X) with h_max := a, J := b, h_j := c, F := d }
      rw [e2]
      exact h3
  | gfVote u => exact votes_mono_checked _ _ _ k x hx
  | attest a =>
    obtain ⟨x', y', e⟩ := StoreSteps.admit_attestation_writes
      (Spec.Config.toSpec S.E S.hc S.cfg) st (Spec.Attestation.toSpecNamed a)
    show x ∈ (Spec.Protocol.admit_attestation _ st _).gf_votes k
    rw [e]; exact hx

/-- The field `processed_mono_receipt` of `NodeFacts` at `Model.spec`: the receipt of any
    object keeps every named block among the bodies, every listed Goldfish vote and every named
    attestation among the rows of `st`. -/
theorem spec_processed_mono_receipt :
    ∀ (S : Setup V) (st : (Model.spec (V := V)).NS) (o' : NamedObject V),
        (∀ B : NamedBlock V, B ∈ st.bodies → B ∈ ((Model.spec (V := V)).receipt_process S st o').bodies) ∧
        (∀ u : GoldfishVote V, u ∈ st.core.gf_votes u.slot →
          u ∈ ((Model.spec (V := V)).receipt_process S st o').core.gf_votes u.slot) ∧
        (∀ a : NamedAttestation V, a ∈ st.sg_rows a.round →
          a ∈ ((Model.spec (V := V)).receipt_process S st o').sg_rows a.round) := by
  intro S st o'
  by_cases hheld : objectRootHeldByOther st.val.T o'
  · have e : (Model.spec (V := V)).receipt_process S st o' = st :=
      OkMember.receipt_process_of_held hheld
    rw [e]
    exact ⟨fun B h => h, fun u h => h, fun a h => h⟩
  · have hval := OkMember.receipt_process_val_of_not_held (S := S) hheld
    refine ⟨fun B hB => ?_, fun u hu => ?_, fun a ha => ?_⟩
    · show B ∈ Member.bodies (OkMember.receipt_process S st o').val
      rw [hval]
      exact receipt_bodies_subset S st.val o' hB
    · show u ∈ ((OkMember.receipt_process S st o').val.gf_votes u.slot).map
        Spec.GoldfishVote.toProof
      rw [hval, mem_map_toProof_iff]
      exact votes_mono_receipt S st.val o' _ _ ((mem_map_toProof_iff _ _).1 hu)
    · obtain ⟨a', rfl⟩ := HandlersFacts.exists_namedAtt a
      have ha' := (HandlersRunFacts.mem_sg_rows_iff st.val _ a').1 ha
      apply (HandlersRunFacts.mem_sg_rows_iff (OkMember.receipt_process S st o').val _ a').2
      rw [hval]
      exact (rowsAt_receipt S st.val o').2.2 _ ha'

/-- The field `postCore_bodies_of_erase_mem` of `NodeFacts` at `Model.spec`: if the erasure of
    `B` is already in `before`'s block tree, the core call on `B` keeps `before`'s bodies. -/
theorem spec_postCore_bodies_of_erase_mem :
    ∀ (S : Setup V) (before : (Model.spec (V := V)).NS) (B : NamedBlock V)
        (h : B.erase ∈ before.core.T), ((Model.spec (V := V)).postCore S before B).bodies = before.bodies := by
  intro S before B h
  obtain ⟨Y, hY, hYe⟩ := Finset.mem_image.mp h
  have hX : (Spec.Block.toSpecNamed B).toProof = B.erase := by
    rw [← Spec.Block.toProofNamed_erase, Spec.Block.toProofNamed_toSpecNamed]
  by_cases hheld : RootHeldByOther before.val.T (Spec.Block.toSpecNamed B)
  · have e : (Model.spec (V := V)).postCore S before B = before := OkMember.postCore_of_held hheld
    rw [e]
  · show Member.bodies (OkMember.postCore S before B).val = Member.bodies before.val
    rw [OkMember.postCore_val_of_not_held hheld]
    have hYX : Y = Spec.Block.toSpecNamed B := by
      by_contra hne
      exact hheld ⟨Y, hY, hne, root_eq_of_toProof_eq (hYe.trans hX.symm)⟩
    unfold Member.postCore Handlers.admitBlockCore
    rw [if_neg]
    intro hadm
    exact StoreSteps.not_mem_of_block_admissible _ _ _ _ hadm (hYX ▸ hY)

/-- The field `receipt_noop_or_processed` of `NodeFacts` at `Model.spec`: the receipt of a
    named block, Goldfish vote or named attestation at `st` returns `st`, or a store that holds the
    object received. -/
theorem spec_receipt_noop_or_processed :
    ∀ (S : Setup V) (st : (Model.spec (V := V)).NS),
        (∀ B : NamedBlock V, (Model.spec (V := V)).receipt_process S st (NamedObject.block B) = st ∨
          B ∈ ((Model.spec (V := V)).receipt_process S st (NamedObject.block B)).bodies) ∧
        (∀ u : GoldfishVote V, (Model.spec (V := V)).receipt_process S st (NamedObject.gfVote u) = st ∨
          u ∈ ((Model.spec (V := V)).receipt_process S st (NamedObject.gfVote u)).core.gf_votes u.slot) ∧
        (∀ a : NamedAttestation V, (Model.spec (V := V)).receipt_process S st (NamedObject.attest a) = st ∨
          a ∈ ((Model.spec (V := V)).receipt_process S st (NamedObject.attest a)).sg_rows a.round) := by
  intro S st
  refine ⟨fun B => ?_, fun u => ?_, fun a => ?_⟩
  · by_cases hheld : objectRootHeldByOther st.val.T (.block B)
    · exact Or.inl (OkMember.receipt_process_of_held hheld)
    · have hval := OkMember.receipt_process_val_of_not_held (S := S) hheld
      by_cases hadm : Spec.Protocol.block_admissible (Spec.Config.toSpec S.E S.hc S.cfg)
          (Spec.Provisional.toSpec S.E) st.val (Spec.Block.toSpecNamed B) = true
      · right
        show B ∈ Member.bodies (OkMember.receipt_process S st (.block B)).val
        rw [hval, mem_bodies_iff]
        show Spec.Block.toSpecNamed B ∈ (Spec.Protocol.on_block _ _ st.val _).T
        rw [Handlers.on_block_eq, if_pos hadm, OkStore.admit_attestations_T]
        unfold Handlers.admitBlockCore
        rw [if_pos hadm, SubtypeEqualities.blockCore_T]
        exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
      · left
        apply Subtype.ext
        show (OkMember.receipt_process S st (.block B)).val = st.val
        rw [hval]
        show Spec.Protocol.on_block _ _ st.val _ = st.val
        rw [Handlers.on_block_eq, if_neg hadm]
  · have hheld : ¬ objectRootHeldByOther st.val.T (.gfVote u) := fun h => h
    have hval := OkMember.receipt_process_val_of_not_held (S := S) hheld
    rcases on_goldfish_vote_checked_cases (Spec.Provisional.toSpec S.E) st.val
        (Spec.GoldfishVote.toSpec u) with e | ⟨-, -, -, e⟩
    · left
      apply Subtype.ext
      show (OkMember.receipt_process S st (.gfVote u)).val = st.val
      rw [hval]
      exact e
    · right
      show u ∈ ((OkMember.receipt_process S st (.gfVote u)).val.gf_votes u.slot).map
        Spec.GoldfishVote.toProof
      rw [hval, mem_map_toProof_iff]
      show Spec.GoldfishVote.toSpec u ∈
        (Spec.Protocol.on_goldfish_vote_checked _ st.val _).gf_votes u.slot
      rw [e]
      show Spec.GoldfishVote.toSpec u ∈ Function.update st.val.gf_votes
        (Spec.GoldfishVote.toSpec u).slot
        (st.val.gf_votes (Spec.GoldfishVote.toSpec u).slot ++
          [Spec.GoldfishVote.toSpec u]) (Spec.GoldfishVote.toSpec u).slot
      rw [Function.update_self]
      exact List.mem_append_right _ (List.mem_singleton_self _)
  · have hheld : ¬ objectRootHeldByOther st.val.T (.attest a) := fun h => h
    have hval := OkMember.receipt_process_val_of_not_held (S := S) hheld
    rcases StoreSteps.admit_attestation_cases (Spec.Config.toSpec S.E S.hc S.cfg) st.val
        (Spec.Attestation.toSpecNamed a) with e | ⟨-, e⟩
    · left
      apply Subtype.ext
      show (OkMember.receipt_process S st (.attest a)).val = st.val
      rw [hval]
      exact e
    · right
      have ha : a = (Spec.Attestation.toSpecNamed a).toProofNamed :=
        (Spec.Attestation.toProofNamed_toSpecNamed a).symm
      rw [ha]
      apply (HandlersRunFacts.mem_sg_rows_iff (OkMember.receipt_process S st (.attest _)).val _ _).2
      rw [← ha, hval]
      show Spec.Attestation.toSpecNamed a ∈
        (Spec.Protocol.admit_attestation _ st.val _).sg_pool a.round
      rw [e, StoreSteps.mem_sg_pool_iff]
      show Spec.Attestation.toSpecNamed a ∈ Function.update st.val.attestations
        (Spec.Attestation.toSpecNamed a).round
        (st.val.attestations (Spec.Attestation.toSpecNamed a).round ++
          [Spec.Attestation.toSpecNamed a]) (Spec.Attestation.toSpecNamed a).round
      rw [Function.update_self]
      exact List.mem_append_right _ (List.mem_singleton_self _)

omit [Inhabited V] in
/-- A vote the checked admission of a list newly lists is one of the list. -/
theorem fold_new_mem (P : Spec.Provisional V) (votes : List (Spec.GoldfishVote V))
    (Y : Spec.Store V) (x : Spec.GoldfishVote V) (h0 : x ∉ Y.gf_votes x.slot)
    (h1 : x ∈ (votes.foldl (Spec.Protocol.on_goldfish_vote_checked P) Y).gf_votes x.slot) :
    x ∈ votes := by
  induction votes generalizing Y with
  | nil => exact absurd h1 h0
  | cons u us ih =>
    simp only [List.foldl_cons] at h1
    by_cases hm : x ∈ (Spec.Protocol.on_goldfish_vote_checked P Y u).gf_votes x.slot
    · rcases on_goldfish_vote_checked_cases P Y u with e | ⟨-, -, -, e⟩
      · rw [e] at hm; exact absurd hm h0
      · rw [e] at hm
        change x ∈ Function.update Y.gf_votes u.slot (Y.gf_votes u.slot ++ [u]) x.slot at hm
        by_cases hk : x.slot = u.slot
        · rw [hk, Function.update_self, List.mem_append] at hm
          rcases hm with hm | hm
          · rw [← hk] at hm; exact absurd hm h0
          · rw [List.mem_singleton.mp hm]; exact List.mem_cons_self
        · rw [Function.update_of_ne hk] at hm; exact absurd hm h0
    · exact List.mem_cons_of_mem _ (ih _ hm h1)

omit [Inhabited V] in
/-- An attestation the admission of a list newly holds is one of the list. -/
theorem admits_new_mem (C : Spec.Config) (rows : List (Spec.Attestation V))
    (st : Spec.Store V) (r : Spec.Round) (x : Spec.Attestation V)
    (h0 : x ∉ st.sg_pool r)
    (h1 : x ∈ (Spec.Protocol.admit_attestations C st rows).sg_pool r) : x ∈ rows := by
  rw [StoreSteps.admit_attestations_foldl] at h1
  induction rows generalizing st with
  | nil => exact absurd h1 h0
  | cons row rs ih =>
    simp only [List.foldl_cons] at h1
    by_cases hm : x ∈ (Spec.Protocol.admit_attestation C st row).sg_pool r
    · rcases StoreSteps.admit_attestation_cases C st row with e | ⟨-, e⟩
      · rw [e] at hm; exact absurd hm h0
      · rw [e] at hm
        rw [StoreSteps.mem_sg_pool_iff] at hm h0
        change x ∈ Function.update st.attestations row.round (st.attestations row.round ++ [row]) r at hm
        by_cases hk : r = row.round
        · rw [hk, Function.update_self, List.mem_append] at hm
          rcases hm with hm | hm
          · rw [← hk] at hm; exact absurd hm h0
          · rw [List.mem_singleton.mp hm]; exact List.mem_cons_self
        · rw [Function.update_of_ne hk] at hm; exact absurd hm h0
    · exact List.mem_cons_of_mem _ (ih _ hm h1)

omit [DecidableEq V] [Fintype V] [Inhabited V] in
/-- An element of a list is at some index of it. -/
theorem exists_getElem?_of_mem {α : Type} {L : List α} {x : α} (h : x ∈ L) :
    ∃ j : Nat, L[j]? = some x := by
  obtain ⟨j, hj, e⟩ := List.mem_iff_getElem.mp h
  exact ⟨j, by rw [List.getElem?_eq_getElem hj, e]⟩

omit [Inhabited V] in
/-- A vote `on_block` newly lists is one the block includes. -/
theorem on_block_new_votes (C : Spec.Config) (P : Spec.Provisional V)
    (st : Spec.Store V) (X : Spec.Block V) (x : Spec.GoldfishVote V)
    (h0 : x ∉ st.gf_votes x.slot)
    (h1 : x ∈ (Spec.Protocol.on_block C P st X).gf_votes x.slot) : x ∈ X.gf_votes := by
  rcases StoreSteps.on_block_shape C P st X with e | ⟨-, σ', e⟩
  · rw [e] at h1; exact absurd h1 h0
  · rw [e] at h1
    generalize hY : ({ st with σ := Function.update st.σ X σ', T := st.T ∪ {X}, timestamp_block := Function.update st.timestamp_block X (some (st.t : Stamp)) } : Spec.Store V) = Y at h1
    obtain ⟨a, b, c, d, e1⟩ := StoreSteps.update_finality_writes
      (X.gf_votes.foldl (Spec.Protocol.on_goldfish_vote_checked P) Y) X
    rw [e1] at h1
    obtain ⟨x', y', e2⟩ := StoreSteps.admit_attestations_writes C X.attestations { (X.gf_votes.foldl (Spec.Protocol.on_goldfish_vote_checked P) Y) with h_max := a, J := b, h_j := c, F := d }
    rw [e2] at h1
    refine fold_new_mem P X.gf_votes Y x ?_ h1
    rw [← hY]; exact h0

omit [Inhabited V] in
/-- An attestation `on_block` newly holds is one the block includes. -/
theorem on_block_new_rows (C : Spec.Config) (P : Spec.Provisional V)
    (st : Spec.Store V) (X : Spec.Block V) (r : Spec.Round)
    (x : Spec.Attestation V) (h0 : x ∉ st.sg_pool r)
    (h1 : x ∈ (Spec.Protocol.on_block C P st X).sg_pool r) : x ∈ X.attestations := by
  rcases StoreSteps.on_block_shape C P st X with e | ⟨-, σ', e⟩
  · rw [e] at h1; exact absurd h1 h0
  · rw [e] at h1
    obtain ⟨-, -, -, k4, -⟩ := StoreSteps.block_core_keeps P st X σ'
    refine admits_new_mem C X.attestations _ r x ?_ h1
    intro hm
    apply h0
    rw [StoreSteps.mem_sg_pool_iff] at hm ⊢
    rw [k4] at hm
    exact hm

omit [Fintype V] [Inhabited V] in
/-- The spec form of a named block includes, mapped, the block's Goldfish votes. -/
theorem toSpecNamed_gf_votes_map (B : NamedBlock V) :
    (Spec.Block.toSpecNamed B).gf_votes.map Spec.GoldfishVote.toProof =
      B.gf_votes := by
  rw [← SubtypeEqualities.toProof_gf_votes, ← Spec.Block.toProofNamed_erase,
    Spec.Block.toProofNamed_toSpecNamed]
  cases B <;> simp [DecoupledConsensusModel.NamedBlock.erase, DecoupledConsensusModel.Block.gf_votes,
    DecoupledConsensusModel.NamedBlock.gf_votes]

/-- When the store admits the spec form of a named block `B` and no other held block has its root,
    `B.erase` is not in the tree's image and is in the image of the core call's tree. -/
theorem erase_cases_of_admissible (S : Setup V) (st : (Model.spec (V := V)).NS)
    (B : NamedBlock V)
    (hheld : ¬ RootHeldByOther st.val.T (Spec.Block.toSpecNamed B))
    (hadm : Spec.Protocol.block_admissible (Spec.Config.toSpec S.E S.hc S.cfg)
      (Spec.Provisional.toSpec S.E) st.val (Spec.Block.toSpecNamed B) = true) :
    B.erase ∉ st.core.T ∧ B.erase ∈ ((Model.spec (V := V)).postCore S st B).core.T ∧
      B ∉ st.bodies ∧ B ∈ ((Model.spec (V := V)).postCore S st B).bodies := by
  have hX : (Spec.Block.toSpecNamed B).toProof = B.erase := by
    rw [← Spec.Block.toProofNamed_erase, Spec.Block.toProofNamed_toSpecNamed]
  have hXT := StoreSteps.not_mem_of_block_admissible _ _ _ _ hadm
  have hpc : ((Model.spec (V := V)).postCore S st B).val.T =
      st.val.T ∪ {Spec.Block.toSpecNamed B} := by
    show (OkMember.postCore S st B).val.T = _
    rw [OkMember.postCore_val_of_not_held hheld]
    unfold Member.postCore Handlers.admitBlockCore
    rw [if_pos hadm, SubtypeEqualities.blockCore_T]
  refine ⟨fun h => ?_, ?_, fun h => hXT ((mem_bodies_iff _ _).1 h), ?_⟩
  · obtain ⟨Y, hY, hYe⟩ := Finset.mem_image.mp h
    have hYX : Y = Spec.Block.toSpecNamed B := by
      by_contra hne
      exact hheld ⟨Y, hY, hne, root_eq_of_toProof_eq (hYe.trans hX.symm)⟩
    exact hXT (hYX ▸ hY)
  · show B.erase ∈ ((Model.spec (V := V)).postCore S st B).val.T.image Spec.Block.toProof
    rw [hpc, ← hX]
    exact Finset.mem_image_of_mem _ (Finset.mem_union_right _ (Finset.mem_singleton_self _))
  · show B ∈ Member.bodies ((Model.spec (V := V)).postCore S st B).val
    rw [mem_bodies_iff, hpc]
    exact Finset.mem_union_right _ (Finset.mem_singleton_self _)

/-- The field `flip_of_process` of `NodeFacts` at `Model.spec`: a block, vote or attestation
    newly held after the receipt of `o'` at `st` is `o'`, or, for a vote or an attestation, is
    included in the block `o'` that the core call newly admits. -/
theorem spec_flip_of_process :
    ∀ (S : Setup V) (st : (Model.spec (V := V)).NS) (o' : NamedObject V),
        (∀ B : NamedBlock V, B ∉ st.bodies → B ∈ ((Model.spec (V := V)).receipt_process S st o').bodies →
          NamedObject.block B = o') ∧
        (∀ u : GoldfishVote V, u ∉ st.core.gf_votes u.slot →
          u ∈ ((Model.spec (V := V)).receipt_process S st o').core.gf_votes u.slot →
          NamedObject.gfVote u = o' ∨ ∃ B : NamedBlock V, o' = NamedObject.block B ∧
            (∃ j : Nat, B.gf_votes[j]? = some u) ∧ B.erase ∉ st.core.T ∧
            B.erase ∈ ((Model.spec (V := V)).postCore S st B).core.T) ∧
        (∀ a : NamedAttestation V, a ∉ st.sg_rows a.round →
          a ∈ ((Model.spec (V := V)).receipt_process S st o').sg_rows a.round →
          NamedObject.attest a = o' ∨ ∃ B : NamedBlock V, o' = NamedObject.block B ∧
            (∃ j : Nat, B.attestations[j]? = some a) ∧ B ∉ st.bodies ∧
            B ∈ ((Model.spec (V := V)).postCore S st B).bodies) := by
  intro S st o'
  by_cases hheld : objectRootHeldByOther st.val.T o'
  · have e : (Model.spec (V := V)).receipt_process S st o' = st :=
      OkMember.receipt_process_of_held hheld
    rw [e]
    exact ⟨fun B h0 h1 => absurd h1 h0, fun u h0 h1 => absurd h1 h0, fun a h0 h1 => absurd h1 h0⟩
  have hval := OkMember.receipt_process_val_of_not_held (S := S) hheld
  cases o' with
  | block B =>
    have hheld' : ¬ RootHeldByOther st.val.T (Spec.Block.toSpecNamed B) := hheld
    have hrv : (OkMember.receipt_process S st (.block B)).val = Spec.Protocol.on_block
        (Spec.Config.toSpec S.E S.hc S.cfg) (Spec.Provisional.toSpec S.E) st.val
        (Spec.Block.toSpecNamed B) := hval
    by_cases hadm : Spec.Protocol.block_admissible (Spec.Config.toSpec S.E S.hc S.cfg)
        (Spec.Provisional.toSpec S.E) st.val (Spec.Block.toSpecNamed B) = true
    · obtain ⟨e1, e2, e3, e4⟩ := erase_cases_of_admissible S st B hheld' hadm
      refine ⟨fun B' h0 h1 => ?_, fun u h0 h1 => ?_, fun a h0 h1 => ?_⟩
      · have h1' := (mem_bodies_iff _ _).1 (show B' ∈ Member.bodies (OkMember.receipt_process S st (.block B)).val from h1)
        rw [hrv, Handlers.on_block_eq, if_pos hadm, OkStore.admit_attestations_T] at h1'
        unfold Handlers.admitBlockCore at h1'
        rw [if_pos hadm, SubtypeEqualities.blockCore_T] at h1'
        rcases Finset.mem_union.mp h1' with h | h
        · exact absurd ((mem_bodies_iff _ _).2 h) h0
        · rw [← Spec.Block.toProofNamed_toSpecNamed B', Finset.mem_singleton.mp h,
            Spec.Block.toProofNamed_toSpecNamed]
      · right
        refine ⟨B, rfl, ?_, e1, e2⟩
        have h1' : Spec.GoldfishVote.toSpec u ∈ (Spec.Protocol.on_block
            (Spec.Config.toSpec S.E S.hc S.cfg) (Spec.Provisional.toSpec S.E) st.val
            (Spec.Block.toSpecNamed B)).gf_votes (Spec.GoldfishVote.toSpec u).slot := by
          rw [← hrv]; exact (mem_map_toProof_iff _ _).1 h1
        have hm := on_block_new_votes _ _ _ _ _ (fun h => h0 ((mem_map_toProof_iff _ _).2 h)) h1'
        apply exists_getElem?_of_mem
        rw [← toSpecNamed_gf_votes_map B]
        exact List.mem_map_of_mem hm
      · right
        refine ⟨B, rfl, ?_, e3, e4⟩
        obtain ⟨a', rfl⟩ := HandlersFacts.exists_namedAtt a
        have h0' : a' ∉ st.val.sg_pool a'.toProofNamed.round :=
          fun h => h0 ((HandlersRunFacts.mem_sg_rows_iff st.val _ a').2 h)
        have h1' := (HandlersRunFacts.mem_sg_rows_iff (OkMember.receipt_process S st (.block B)).val _ a').1 h1
        rw [hrv] at h1'
        have hm := on_block_new_rows _ _ _ _ _ _ h0' h1'
        rw [toSpecNamed_attestations, List.mem_map] at hm
        obtain ⟨b, hb, hba⟩ := hm
        apply exists_getElem?_of_mem
        rw [← hba, Spec.Attestation.toProofNamed_toSpecNamed]
        exact hb
    · have hst : (OkMember.receipt_process S st (.block B)).val = st.val := by
        rw [hrv, Handlers.on_block_eq, if_neg hadm]
      refine ⟨fun B' h0 h1 => ?_, fun u h0 h1 => ?_, fun a h0 h1 => ?_⟩
      · exact absurd (show B' ∈ Member.bodies st.val by
          rw [← hst]; exact h1) h0
      · exact absurd (show u ∈ (st.val.gf_votes u.slot).map Spec.GoldfishVote.toProof by
          rw [← hst]; exact h1) h0
      · exact absurd (show a ∈ Member.sg_rows st.val a.round by
          rw [← hst]; exact h1) h0
  | gfVote u' =>
    have hrv : (OkMember.receipt_process S st (.gfVote u')).val =
        Spec.Protocol.on_goldfish_vote_checked (Spec.Provisional.toSpec S.E)
          st.val (Spec.GoldfishVote.toSpec u') := hval
    obtain ⟨gv, tv, efr⟩ := receipt_gfVote_frame S st.val u'
    have hfr : (OkMember.receipt_process S st (.gfVote u')).val =
        { st.val with gf_votes := gv, timestamp_vote := tv } := hval.trans efr
    refine ⟨fun B' h0 h1 => ?_, fun u h0 h1 => ?_, fun a h0 h1 => ?_⟩
    · exact absurd (show B' ∈ Member.bodies st.val by
        have h := (show B' ∈ Member.bodies (OkMember.receipt_process S st (.gfVote u')).val from h1)
        rw [hfr] at h; exact h) h0
    · left
      have h1' : Spec.GoldfishVote.toSpec u ∈ (OkMember.receipt_process S st (.gfVote u')).val.gf_votes (Spec.GoldfishVote.toSpec u).slot :=
        (mem_map_toProof_iff _ _).1 h1
      rw [hrv] at h1'
      have hm := fold_new_mem (Spec.Provisional.toSpec S.E) [Spec.GoldfishVote.toSpec u'] st.val _
        (fun h => h0 ((mem_map_toProof_iff _ _).2 h)) h1'
      rw [List.mem_singleton] at hm
      have : u = u' := by
        rw [← Spec.GoldfishVote.toProof_toSpec u, hm, Spec.GoldfishVote.toProof_toSpec]
      rw [this]
    · exact absurd (show a ∈ Member.sg_rows st.val a.round by
        have h := (show a ∈ Member.sg_rows (OkMember.receipt_process S st (.gfVote u')).val a.round from h1)
        rw [hfr] at h; exact h) h0
  | attest a' =>
    have hrv : (OkMember.receipt_process S st (.attest a')).val =
        Spec.Protocol.admit_attestation (Spec.Config.toSpec S.E S.hc S.cfg)
          st.val (Spec.Attestation.toSpecNamed a') := hval
    obtain ⟨at', ts, efr⟩ := receipt_attest_frame S st.val a'
    have hfr : (OkMember.receipt_process S st (.attest a')).val =
        { st.val with attestations := at', timestamp_sg_vote := ts } := hval.trans efr
    refine ⟨fun B' h0 h1 => ?_, fun u h0 h1 => ?_, fun a h0 h1 => ?_⟩
    · exact absurd (show B' ∈ Member.bodies st.val by
        have h := (show B' ∈ Member.bodies (OkMember.receipt_process S st (.attest a')).val from h1)
        rw [hfr] at h; exact h) h0
    · exact absurd (show u ∈ (st.val.gf_votes u.slot).map Spec.GoldfishVote.toProof by
        have h := (show u ∈ ((OkMember.receipt_process S st (.attest a')).val.gf_votes u.slot).map
          Spec.GoldfishVote.toProof from h1)
        rw [hfr] at h; exact h) h0
    · left
      obtain ⟨b, rfl⟩ := HandlersFacts.exists_namedAtt a
      have h0' : b ∉ st.val.sg_pool b.toProofNamed.round :=
        fun h => h0 ((HandlersRunFacts.mem_sg_rows_iff st.val _ b).2 h)
      have h1' := (HandlersRunFacts.mem_sg_rows_iff (OkMember.receipt_process S st (.attest a')).val _ b).1 h1
      rw [hrv] at h1'
      have hm := admits_new_mem (Spec.Config.toSpec S.E S.hc S.cfg)
        [Spec.Attestation.toSpecNamed a'] st.val _ b h0'
        (by rw [show Spec.Protocol.admit_attestations _ st.val [_] =
              Spec.Protocol.admit_attestation _ st.val _ from by
                rw [StoreSteps.admit_attestations_foldl]; rfl]
            exact h1')
      rw [List.mem_singleton] at hm
      rw [hm, Spec.Attestation.toProofNamed_toSpecNamed]

/-- The field `gradeContract_grade2_block_with` of `NodeFacts` at `Model.spec`: for every
    outcome `g` of the frame grade read of `c` at `st` and `r`, every grade-2 block a duty reads
    through the grade contract of `c` there is the grade-2 candidate of `g`. -/
theorem spec_gradeContract_grade2_block_with :
    ∀ (c : (Model.spec (V := V)).Cache) (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig) (st : (Model.spec (V := V)).HS) (r : DecoupledConsensusModel.Round)
        (g : DecoupledConsensusModel.Protocol.GradeRead V), (Model.spec (V := V)).frameGradeRead c E hc st r ⇢ g →
        ∀ x : Option (Block V), (Model.spec (V := V)).grade2_block_with ((Model.spec (V := V)).gradeContract c) E hc st r ⇢ x → x = g.Q2 := by
  intro c E hc st r g hg x hx
  have hg' := (SpecRecord.returns_successOutcomes _ _).1 hg
  have hx' := (SpecRecord.returns_successOutcomes _ _).1 hx
  cases hr : Spec.Protocol.round_grade_read
      { Spec.Store.ofImage st.val with saved_grades := SpecRecord.fill (Spec.Protocol.advance_to_round
        (st.val.contractOfImage c) r) } r with
  | error e =>
    rw [hr] at hg'
    cases hg'
  | ok gr =>
    rw [hr] at hg'
    simp only [Except.map, Except.ok.injEq] at hg'
    subst hg'
    have hr2 := hr
    simp only [Spec.Protocol.round_grade_read] at hr2
    obtain ⟨A, -, hr2⟩ := dre_bind_ok hr2
    obtain ⟨Q2, hQ, hr2⟩ := dre_bind_ok hr2
    obtain ⟨G0, -, hr2⟩ := dre_bind_ok hr2
    obtain ⟨raw, -, hr2⟩ := dre_bind_ok hr2
    have hgr : gr.Q2 = Q2 := by
      simp only [pure, Except.pure, Except.ok.injEq] at hr2
      rw [← hr2]
    have hq : Spec.Protocol.grade2_block_with
        { Spec.Store.ofImage st.val with saved_grades := SpecRecord.fill (Spec.Protocol.advance_to_round
          (st.val.contractOfImage c) r) } r = .ok Q2 := hQ
    have hx2 : Except.map (Option.map Spec.Block.toProof)
        (Spec.Protocol.grade2_block_with
          { Spec.Store.ofImage st.val with saved_grades := SpecRecord.fill (Spec.Protocol.advance_to_round
            (st.val.contractOfImage c) r) } r) = .ok x := hx'
    rw [hq] at hx2
    simp only [Except.map, Except.ok.injEq] at hx2
    rw [← hx2]
    show Option.map Spec.Block.toProof Q2 = gr.Q2.map Spec.Block.toProof
    rw [hgr]

/-! ## The contract reads against the frame read through the tree -/

/-- The field `gradeContract_sgRoot_eq_frameAnchor` of `NodeFacts` at `Model.spec`: the SG root
    read through the grade contract of `c` at `st` and round `r` can return `x` exactly when
    `M.anchor` at the grade-1 result of the round-`r` frame read from `c` at `st` can. -/
theorem spec_gradeContract_sgRoot_eq_frameAnchor :
    ∀ (c : (Model.spec (V := V)).Cache) (E : Env V) (hc : Protocol.HealConfig)
      (st : (Model.spec (V := V)).HS) (r : Round) (x : Block V),
      (Model.spec (V := V)).get_sg_root_with ((Model.spec (V := V)).gradeContract c) E hc st r ⇢ x ↔
        (Model.spec (V := V)).anchor E hc st r ((Model.spec (V := V)).readFrame c st r).g1 ⇢ x := by
  intro c E hc st r x
  rw [GradesFacts.sd_anchor_readFrame]
  exact Iff.rfl

/-- The field `ModelProperties_gradeContract_read_Q2` of `NodeFacts` at `Model.spec`: for every
    outcome `g` of the grade contract's read of `c` at `st` and `r`, and every outcome `x` of the
    grade-2 block of the round-`r` frame read from `c` at `st`, the grade-2 candidate of `g` is `x`. -/
theorem spec_ModelProperties_gradeContract_read_Q2 : ∀ (c : (Model.spec (V := V)).Cache) (E : Env V) (hc : Protocol.HealConfig)
    (st : (Model.spec (V := V)).HS) (r : Round),
    ∀ g : DecoupledConsensusModel.Protocol.GradeRead V, ((Model.spec (V := V)).gradeContract c).read E hc st r ⇢ g →
    ∀ x : Option (Block V), (Model.spec (V := V)).grade2Block st ((Model.spec (V := V)).readFrame c st r) ⇢ x →
    g.Q2 = x := by
  intro c E hc st r g hg x hx
  obtain ⟨hinj, hpar, hF⟩ := GradesFacts.sd_tree_hyps st
  obtain ⟨A, Q2, -, hQ, -, hgQ, -⟩ := GradesFacts.sd_read_parts (c := c) hg
  have hx' := (SpecRecord.returns_successOutcomes _ _).1 hx
  have hfr : st.val.roundGradesOfImage (Member.readFrame c st.val r) = Member.readFrame c st.val r := by
    rw [GradesImages.readFrame_eq_frameOfImage st.val hinj hpar hF,
      GradesImages.roundGradesOfImage_frameOfImage]
  have hq : Spec.Protocol.grade2Block (Spec.Store.ofImage st.val)
      (SpecRecord.fillRound (st.val.roundGradesOfImage (Member.readFrame c st.val r))) = .ok Q2 := by
    rw [hfr, ← GradesImages.round_grades_ofImage_eq_fillRound_readFrame st.property]
    exact hQ
  have hx2 : Except.map (Option.map Spec.Block.toProof)
      (Spec.Protocol.grade2Block (Spec.Store.ofImage st.val)
        (SpecRecord.fillRound (st.val.roundGradesOfImage (Member.readFrame c st.val r)))) = .ok x := hx'
  rw [hq] at hx2
  simp only [Except.map, Except.ok.injEq] at hx2
  rw [hgQ, hx2]

/-- The field `Sts_gradeContract_read_Q2` of `NodeFacts` at `Model.spec`: every outcome `g` of
    the grade contract's read of `c` at `st` and `r` names every outcome of
    `M.grade2Block st (M.readFrame c st r)` as its grade-2 block. -/
theorem spec_Sts_gradeContract_read_Q2 : ∀ (c : (Model.spec (V := V)).Cache) (E : Env V) (hc : Protocol.HealConfig) (st : (Model.spec (V := V)).HS)
    (r : Round), ∀ g : DecoupledConsensusModel.Protocol.GradeRead V, ((Model.spec (V := V)).gradeContract c).read E hc st r ⇢ g →
    ∀ x : Option (Block V), (Model.spec (V := V)).grade2Block st ((Model.spec (V := V)).readFrame c st r) ⇢ x → g.Q2 = x :=
  spec_ModelProperties_gradeContract_read_Q2

/-- The field `ModelProperties_gradeContract_read_anchor` of `NodeFacts` at `Model.spec`: for
    every outcome `g` of the grade contract's read of `c` at `st` and `r`, and every outcome `a` of
    `M.anchor` at the grade-1 result of the round-`r` frame read from `c` at `st`, the anchor of `g`
    is `a`. -/
theorem spec_ModelProperties_gradeContract_read_anchor : ∀ (c : (Model.spec (V := V)).Cache) (E : Env V)
    (hc : Protocol.HealConfig) (st : (Model.spec (V := V)).HS) (r : Round),
    ∀ g : DecoupledConsensusModel.Protocol.GradeRead V, ((Model.spec (V := V)).gradeContract c).read E hc st r ⇢ g →
    ∀ a : Block V, (Model.spec (V := V)).anchor E hc st r ((Model.spec (V := V)).readFrame c st r).g1 ⇢ a →
    g.anchor = a := by
  intro c E hc st r g hg a ha
  obtain ⟨A, Q2, hA, -, hgA, -, -⟩ := GradesFacts.sd_read_parts (c := c) hg
  rw [GradesFacts.sd_anchor_readFrame] at ha
  have ha' := (SpecRecord.returns_successOutcomes _ _).1 ha
  rw [hA] at ha'
  simp only [Except.map, Except.ok.injEq] at ha'
  rw [hgA, ha']

/-- The field `Sts_gradeContract_read_anchor` of `NodeFacts` at `Model.spec`: for every outcome
    `g` of the grade contract's read of `c` at `st` and `r`, and every outcome `a` of `M.anchor` at
    the grade-1 result of the round-`r` frame read from `c` at `st`, the anchor field of `g` is `a`. -/
theorem spec_Sts_gradeContract_read_anchor : ∀ (c : (Model.spec (V := V)).Cache) (E : Env V) (hc : Protocol.HealConfig)
    (st : (Model.spec (V := V)).HS) (r : Round),
    ∀ g : DecoupledConsensusModel.Protocol.GradeRead V, ((Model.spec (V := V)).gradeContract c).read E hc st r ⇢ g →
    ∀ a : Block V, (Model.spec (V := V)).anchor E hc st r ((Model.spec (V := V)).readFrame c st r).g1 ⇢ a →
    g.anchor = a :=
  spec_ModelProperties_gradeContract_read_anchor

omit [DecidableEq V] [Fintype V] [Inhabited V] in
/-- The spec's `Protocol.record_attestation` commutes with erasing the timeout votes `timeouts` of a
    signing history. -/
theorem record_attestation_erase (sh : Spec.SigningHistory)
    (a : Spec.Attestation V) :
    Spec.Protocol.record_attestation { sh with timeouts := ∅ } a =
      { Spec.Protocol.record_attestation sh a with timeouts := ∅ } := by
  simp only [Spec.Protocol.record_attestation, Id.run]
  split_ifs <;> rfl

omit [DecidableEq V] [Fintype V] [Inhabited V] in
/-- The spec's `Protocol.create_attestation` does not read the timeout votes: on a history with
    `timeouts` erased it signs the same attestation and returns its usual history with `timeouts`
    erased. -/
theorem create_attestation_erase (sh : Spec.SigningHistory) (v : V) (r : Round)
    (confirmed : Option Spec.BlockId)
    (fields : Option (Height × Spec.BlockId × Bool)) (h_j : Height)
    (J : Spec.BlockId) (h_F : Height) :
    Spec.Protocol.create_attestation { sh with timeouts := ∅ } v r confirmed fields h_j J h_F =
      ({ (Spec.Protocol.create_attestation sh v r confirmed fields h_j J h_F).1 with
          timeouts := ∅ },
        (Spec.Protocol.create_attestation sh v r confirmed fields h_j J h_F).2) := by
  simp only [Spec.Protocol.create_attestation, Id.run]
  rw [record_attestation_erase]
  rfl

/-- The attestation input the spec's `Protocol.attestation_input` reads for the validator `v` names
    `v`. -/
theorem attestation_input_val_index {C : Spec.Config} {v : V}
    {st : Spec.Store V} {x : Spec.Protocol.AttestationInput V}
    (h : Spec.Protocol.attestation_input C v st = .ok x) : x.val_index = v := by
  simp only [Spec.Protocol.attestation_input] at h
  obtain ⟨A, -, h⟩ := dre_bind_ok h
  obtain ⟨⟨fields, h_j, J, h_F⟩, -, h⟩ := dre_bind_ok h
  obtain ⟨Cb, -, h⟩ := dre_bind_ok h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  rw [← h]

/-- `tick_attest_mem` with the validator of the attestation input: an attestation the member `tick`
    sends is signed by `Protocol.create` on an input whose validator is `n.v`. -/
theorem tick_attest_input (S : Setup V) (v : V) (n : (Model.spec (V := V)).N) (t : Time)
    (out : (Model.spec (V := V)).N × List (NamedObject V))
    (hout : (Model.spec (V := V)).tick S v n t ⇢ out) {a : NamedAttestation V}
    (ha : NamedObject.attest a ∈ out.2) :
    ∃ x : Spec.Protocol.AttestationInput V, x.val_index = n.val.v ∧
      out.1.val.signingHistory = (Spec.Protocol.create n.val.signingHistory x).1 ∧
      a = (Spec.Protocol.create n.val.signingHistory x).2.toProofNamed := by
  obtain ⟨sent, hrun, hsent⟩ := tick_out S v n t out hout
  rw [hsent] at ha
  obtain ⟨o, ho, hoa⟩ := List.mem_map.mp ha
  rcases tick_sent hrun ho with ⟨B, rfl, -⟩ | ⟨u, rfl, -⟩ | ⟨row, rfl, -⟩
  · simp only [Spec.NamedObject.toProof, reduceCtorEq] at hoa
  · simp only [Spec.NamedObject.toProof, reduceCtorEq] at hoa
  · obtain ⟨st4, hb⟩ := tick_attest hrun ho
    simp only [Spec.Protocol.build_attestation] at hb
    obtain ⟨x, hx, hb⟩ := dre_bind_ok hb
    have hb' : Spec.Protocol.create n.val.signingHistory x =
        (out.1.val.signingHistory, row) := by
      have := hb
      simp only [pure, Except.pure, Except.ok.injEq] at this
      exact this
    refine ⟨x, attestation_input_val_index hx, by rw [hb'], ?_⟩
    rw [hb']
    simp only [Spec.NamedObject.toProof, NamedObject.attest.injEq] at hoa
    exact hoa.symm

/-- The field `on_tick_emit_attestation_created` of `NodeFacts` at `Model.spec`: if `n` runs as
    `v` and an outcome of `v`'s tick at `t` from `n` sends the attestation `a`, then erasing `a`
    gives the attestation `M.create_attestation` returns from `n`'s record with `v`'s index and some
    arguments, and the outcome's record is the record that call returns. -/
theorem spec_on_tick_emit_attestation_created : ∀ (S : Setup V) (v : V) (n : (Model.spec (V := V)).N) (t : Time)
    (hv : (Model.spec (V := V)).runs_as n v)
    (out : (Model.spec (V := V)).N × List (NamedObject V)) (hout : (Model.spec (V := V)).tick S v n t ⇢ out)
    {a : NamedAttestation V} (hmem : NamedObject.attest a ∈ out.2),
    ∃ (r : Round) (confirmed : Option BlockId) (fields : Option (Height × BlockId × Bool))
      (h_j : Height) (J : BlockId) (h_F : Height),
      a.erase = ((Model.spec (V := V)).create_attestation n.record.legacy (S.node v).val_index r confirmed fields
          h_j J h_F).2 ∧
        out.1.record.legacy = ((Model.spec (V := V)).create_attestation n.record.legacy (S.node v).val_index r
          confirmed fields h_j J h_F).1 := by
  intro S v n t hv out hout a hmem
  obtain ⟨x, hxv, hsh, rfl⟩ := tick_attest_input S v n t out hout hmem
  have hv' : n.val.v = v := hv
  have hnode : (S.node v).val_index = x.val_index := by
    rw [S.node_val_index, hxv, hv']
  have hf : ChainStateToHandlers.fieldsToSpec
      (x.fields.map (fun f => (f.1, f.2.1.toProof, f.2.2))) = x.fields := by
    rcases x.fields with _ | ⟨a, b, c⟩ <;> rfl
  have hc : (x.confirmed.map Spec.BlockId.toProof).map Spec.BlockId.toSpec =
      x.confirmed := by
    rcases x.confirmed with _ | b <;> rfl
  refine ⟨x.round, x.confirmed.map Spec.BlockId.toProof,
    x.fields.map (fun f => (f.1, f.2.1.toProof, f.2.2)), x.h_j, x.J.toProof, x.h_F, ?_, ?_⟩
  · show (Spec.Protocol.create n.val.signingHistory x).2.toProofNamed.erase =
      (Spec.Attestation.toProof (Spec.Protocol.create_attestation
        { n.val.signingHistory with timeouts := ∅ } (S.node v).val_index x.round
        ((x.confirmed.map Spec.BlockId.toProof).map Spec.BlockId.toSpec)
        (ChainStateToHandlers.fieldsToSpec (x.fields.map (fun f => (f.1, f.2.1.toProof, f.2.2))))
        x.h_j (Spec.BlockId.toSpec x.J.toProof) x.h_F).2)
    rw [create_attestation_erase, hnode, hc, hf, Spec.Attestation.toProofNamed_erase]
    rfl
  · show { out.1.val.signingHistory with timeouts := ∅ } =
      (Spec.Protocol.create_attestation
        { n.val.signingHistory with timeouts := ∅ } (S.node v).val_index x.round
        ((x.confirmed.map Spec.BlockId.toProof).map Spec.BlockId.toSpec)
        (ChainStateToHandlers.fieldsToSpec (x.fields.map (fun f => (f.1, f.2.1.toProof, f.2.2))))
        x.h_j (Spec.BlockId.toSpec x.J.toProof) x.h_F).1
    rw [create_attestation_erase, hnode, hc, hf, hsh]
    rfl

/-- The field `tick_new_body_core` of `NodeFacts` at `Model.spec`: a named block new among the
    bodies of an outcome of `v`'s tick at `t` from `n` is among the bodies the block core returns on
    `n`'s store with its clock set to `t`, and that core's finalized block is the outcome's. -/
theorem spec_tick_new_body_core :
    ∀ (S : Setup V) (v : V) (n : (Model.spec (V := V)).N) (t : Time)
        (out : (Model.spec (V := V)).N × List (NamedObject V)) (hout : (Model.spec (V := V)).tick S v n t ⇢ out)
        (B : NamedBlock V) (hpre : B ∉ n.st.bodies) (hpost : B ∈ out.1.st.bodies),
        B ∈ ((Model.spec (V := V)).ns_process_block_core S.E S.hc S.cfg ((Model.spec (V := V)).ns_setClock S.E n.st t) B).bodies ∧
          ((Model.spec (V := V)).ns_process_block_core S.E S.hc S.cfg ((Model.spec (V := V)).ns_setClock S.E n.st t) B).core.F =
            out.1.st.core.F := by
  intro S v n t out hout B hpre hpost
  have hpost' : B ∈ out.1.val.st.T.map Spec.Block.toProofNamedEmb := hpost
  obtain ⟨X, hX, rfl⟩ := Finset.mem_map.mp hpost'
  have hXn : X ∉ n.val.st.T := fun h => hpre (Finset.mem_map_of_mem _ h)
  obtain ⟨sg, ⟨he, -⟩ | ⟨B0, hB0, he⟩⟩ := tick_shape S v n t out hout
  · rw [he.1] at hX; exact absurd hX hXn
  · rw [he.1] at hX
    rcases SubtypeEqualities.receipt_cases S _ (.block B0) with ⟨hT', -⟩ | ⟨B1, hB1, hadm, hT', -⟩
    · rw [hT'] at hX; exact absurd hX hXn
    · cases hB1
      rw [hT'] at hX
      rcases Finset.mem_union.mp hX with hX' | hX'
      · exact absurd hX' hXn
      · have hXe : X = Spec.Block.toSpecNamed B0 := Finset.mem_singleton.mp hX'
        subst hXe
        rw [Spec.Block.coe_toProofNamedEmb, Spec.Block.toProofNamed_toSpecNamed]
        have hheld : ¬ RootHeldByOther n.val.st.T (Spec.Block.toSpecNamed B0) := by
          rintro ⟨Y, hY, hne, hr⟩
          have hd := out.1.property.2.1
          have hYo : Y ∈ out.1.val.st.T := by
            rw [he.1, hT']; exact Finset.mem_union_left _ hY
          have hXo : Spec.Block.toSpecNamed B0 ∈ out.1.val.st.T := by
            rw [he.1, hT']; exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
          exact hne (hd Y hYo _ hXo hr)
        have hadm' : Spec.Protocol.block_admissible
            (Spec.Config.toSpec S.E S.hc S.cfg) (Spec.Provisional.toSpec S.E)
            ((Model.spec (V := V)).ns_setClock S.E n.st t).val
            (Spec.Block.toSpecNamed B0) = true := hadm
        have hcore : ((Model.spec (V := V)).ns_process_block_core S.E S.hc S.cfg
            ((Model.spec (V := V)).ns_setClock S.E n.st t) B0).val =
            Handlers.blockCore (Spec.Config.toSpec S.E S.hc S.cfg)
              (Spec.Provisional.toSpec S.E)
              ((Model.spec (V := V)).ns_setClock S.E n.st t).val
              (Spec.Block.toSpecNamed B0) := by
          show (OkMember.ns_process_block_core S.E S.hc S.cfg _ B0).val = _
          rw [OkMember.ns_process_block_core_val_of_not_held hheld]
          unfold Member.ns_process_block_core Handlers.admitBlockCore
          rw [if_pos hadm']
        refine ⟨?_, ?_⟩
        · show B0 ∈ Member.bodies ((Model.spec (V := V)).ns_process_block_core S.E S.hc S.cfg
            ((Model.spec (V := V)).ns_setClock S.E n.st t) B0).val
          rw [hcore, mem_bodies_iff, SubtypeEqualities.blockCore_T]
          exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
        · show ((Model.spec (V := V)).ns_process_block_core S.E S.hc S.cfg
            ((Model.spec (V := V)).ns_setClock S.E n.st t) B0).val.F.toProof =
            out.1.val.st.F.toProof
          rw [hcore, he.2.2.2.1]
          have e1 : (Member.receipt_process S { n.val.st with saved_grades := sg, t := t, s := (Setup.toSpec S).C.slotOf t } (.block B0)).F = (Spec.Protocol.on_block (Spec.Config.toSpec S.E S.hc S.cfg) (Spec.Provisional.toSpec S.E) { ((Model.spec (V := V)).ns_setClock S.E n.st t).val with saved_grades := sg } (Spec.Block.toSpecNamed B0)).F := rfl
          rw [e1, on_block_with_saved_grades]
          show _ = (Spec.Protocol.on_block _ _ ((Model.spec (V := V)).ns_setClock S.E n.st t).val (Spec.Block.toSpecNamed B0)).F.toProof
          rw [Handlers.on_block_eq, if_pos hadm', OkStore.admit_attestations_F]
          unfold Handlers.admitBlockCore
          rw [if_pos hadm']

/-! ## Where the tick's new votes and attestations come from -/

omit [Inhabited V] in
/-- The spec's `on_block` keeps every listed vote. -/
theorem votes_mono_on_block (C : Spec.Config) (P : Spec.Provisional V)
    (st : Spec.Store V) (B : Spec.Block V) (k : Spec.Slot)
    (x : Spec.GoldfishVote V) (hx : x ∈ st.gf_votes k) :
    x ∈ (Spec.Protocol.on_block C P st B).gf_votes k := by
  rcases StoreSteps.on_block_shape C P st B with e | ⟨-, σ', e⟩
  · rw [e]; exact hx
  · rw [e]
    generalize hX : ({ st with σ := Function.update st.σ B σ', T := st.T ∪ {B}, timestamp_block := Function.update st.timestamp_block B (some (st.t : Stamp)) } : Spec.Store V) = Y
    have h1 : x ∈ Y.gf_votes k := by rw [← hX]; exact hx
    have h2 : ∀ (votes : List (Spec.GoldfishVote V)) (Z : Spec.Store V),
        x ∈ Z.gf_votes k → x ∈ (votes.foldl (Spec.Protocol.on_goldfish_vote_checked P) Z).gf_votes k := by
      intro votes
      induction votes with
      | nil => intro Z h; exact h
      | cons u us ih => intro Z h; exact ih _ (votes_mono_checked _ Z u k x h)
    have h3 := h2 B.gf_votes Y h1
    obtain ⟨a, b, c, d, e1⟩ := StoreSteps.update_finality_writes
      (B.gf_votes.foldl (Spec.Protocol.on_goldfish_vote_checked P) Y) B
    rw [e1]
    obtain ⟨x', y', e2⟩ := StoreSteps.admit_attestations_writes C B.attestations { (B.gf_votes.foldl (Spec.Protocol.on_goldfish_vote_checked P) Y) with h_max := a, J := b, h_j := c, F := d }
    rw [e2]
    exact h3

omit [Inhabited V] in
/-- From its first store with the clock set, `st1`, the tick keeps every vote, attestation and
    block, and every vote or attestation it adds is one it sends or one included in the block it
    proposes and sends, admitted by `on_block` at `st1`. -/
theorem tick_origins {C : Spec.Config} {P : Spec.Provisional V}
    {X : Spec.External V} {n n' : Spec.NodeState V}
    {t : Spec.Time} {sent : List (Spec.NamedObject V)}
    (h : (Spec.tick C P X n t).run [] = .ok (n', sent)) :
    ∃ (sg : Spec.SavedGrades V) (st1 : Spec.Store V),
      st1 = { n.st with saved_grades := sg, t := t, s := C.slotOf t } ∧
      (∀ (k : Spec.Slot) (x : Spec.GoldfishVote V), x ∈ st1.gf_votes k →
        x ∈ n'.st.gf_votes k) ∧
      (∀ (r : Spec.Round) (x : Spec.Attestation V), x ∈ st1.sg_pool r →
        x ∈ n'.st.sg_pool r) ∧
      (∀ x : Spec.GoldfishVote V, x ∉ st1.gf_votes x.slot → x ∈ n'.st.gf_votes x.slot →
        Spec.NamedObject.gfVote x ∈ sent ∨ ∃ B : Spec.Block V,
          Spec.NamedObject.block B ∈ sent ∧
          x ∈ (Spec.Protocol.on_block C P st1 B).gf_votes x.slot ∧ x ∈ B.gf_votes) ∧
      (∀ (r : Spec.Round) (x : Spec.Attestation V), x ∉ st1.sg_pool r →
        x ∈ n'.st.sg_pool r →
        Spec.NamedObject.attest x ∈ sent ∨ ∃ B : Spec.Block V,
          Spec.NamedObject.block B ∈ sent ∧
          x ∈ (Spec.Protocol.on_block C P st1 B).sg_pool r ∧ x ∈ B.attestations) := by
  obtain ⟨st0, st2, st3, st4, st5, sh5, l1, l2, h0, hP1, hP0, hV1, hV0, hC1, hC0, hA1, hA0, rfl⟩ :=
    tick_steps h
  have e0 : ({ st0 with t := t, s := C.slotOf t } : Spec.Store V) = { n.st with saved_grades := st0.saved_grades, t := t, s := C.slotOf t } := by
    rw [(update_grades_ok h0).1]
  refine ⟨st0.saved_grades, _, rfl, ?_⟩
  rw [← e0]
  have hl2 : ∀ o ∈ l2, o ∈ sent := by
    intro o ho
    by_cases ha : condA C n t
    · obtain ⟨row, -, -, rfl⟩ := hA1 ha; exact List.mem_append_left _ ho
    · rw [(hA0 ha).2.2]; exact ho
  have hl1 : ∀ o ∈ l1, o ∈ sent := by
    intro o ho
    apply hl2
    by_cases hv : condV C n t
    · rcases hV1 hv with ⟨-, rfl⟩ | ⟨u, -, rfl, -⟩
      · exact ho
      · exact List.mem_append_left _ ho
    · rw [(hV0 hv).2]; exact ho
  have v45 : st5.gf_votes = st3.gf_votes := by
    have e4 : st4.gf_votes = st3.gf_votes := by
      by_cases hcc : condC C n t
      · rw [update_confirmation_ok (hC1 hcc)]
      · rw [hC0 hcc]
    by_cases ha : condA C n t
    · obtain ⟨row, -, rfl, -⟩ := hA1 ha
      obtain ⟨x, y, e⟩ := StoreSteps.admit_attestation_writes C st4 row
      rw [e]; exact e4
    · rw [(hA0 ha).1]; exact e4
  have r34 : st4.attestations = st2.attestations := by
    have e3 : st3.attestations = st2.attestations := by
      by_cases hv : condV C n t
      · rcases hV1 hv with ⟨rfl, -⟩ | ⟨u, rfl, -⟩
        · rfl
        · obtain ⟨gv, tv, e⟩ := on_goldfish_vote_checked_frame P st2 u
          rw [e]
      · rw [(hV0 hv).1]
    by_cases hcc : condC C n t
    · rw [update_confirmation_ok (hC1 hcc)]; exact e3
    · rw [hC0 hcc]; exact e3
  have pool_eq : ∀ (a b : Spec.Store V), a.attestations = b.attestations →
      ∀ r, a.sg_pool r = b.sg_pool r := fun a b hab r => by
    simp only [Spec.Store.sg_pool, StoreSteps.getElem_fn, hab]
  refine ⟨fun k x hx => ?_, fun r x hx => ?_, fun x h0 h1 => ?_, fun r x h0 h1 => ?_⟩
  ·
    show x ∈ st5.gf_votes k
    rw [v45]
    have h2 : x ∈ st2.gf_votes k := by
      by_cases hc : condP C P n t
      · obtain ⟨B, rfl, -⟩ := hP1 hc
        exact votes_mono_on_block C P _ B k x hx
      · rw [(hP0 hc).1]; exact hx
    by_cases hv : condV C n t
    · rcases hV1 hv with ⟨rfl, -⟩ | ⟨u, rfl, -⟩
      · exact h2
      · exact votes_mono_checked P st2 u k x h2
    · rw [(hV0 hv).1]; exact h2
  ·
    show x ∈ st5.sg_pool r
    have h2 : x ∈ st2.sg_pool r := by
      by_cases hc : condP C P n t
      · obtain ⟨B, rfl, -⟩ := hP1 hc
        exact (rowsAt_on_block C P _ B).2.2 r hx
      · rw [(hP0 hc).1]; exact hx
    have h4 : x ∈ st4.sg_pool r := by rw [pool_eq st4 st2 r34]; exact h2
    by_cases ha : condA C n t
    · obtain ⟨row, -, rfl, -⟩ := hA1 ha
      exact (rowsAt_admit C st4 row).2.2 r h4
    · rw [(hA0 ha).1]; exact h4
  ·
    have h1' : x ∈ st3.gf_votes x.slot := by
      have : x ∈ st5.gf_votes x.slot := h1
      rwa [v45] at this
    by_cases h2 : x ∈ st2.gf_votes x.slot
    · by_cases hc : condP C P n t
      · obtain ⟨B, hB, hl⟩ := hP1 hc
        right
        refine ⟨B, hl1 _ (by rw [hl]; exact List.mem_singleton_self _), ?_, ?_⟩
        · rw [← hB]; exact h2
        · rw [hB] at h2; exact on_block_new_votes C P _ B x h0 h2
      · rw [(hP0 hc).1] at h2; exact absurd h2 h0
    · by_cases hv : condV C n t
      · rcases hV1 hv with ⟨rfl, -⟩ | ⟨u, rfl, hl, -⟩
        · exact absurd h1' h2
        · left
          have hm := fold_new_mem P [u] st2 x h2 h1'
          rw [List.mem_singleton] at hm
          subst hm
          exact hl2 _ (by rw [hl]; exact List.mem_append_right _ (List.mem_singleton_self _))
      · rw [(hV0 hv).1] at h1'; exact absurd h1' h2
  ·
    by_cases h4 : x ∈ st4.sg_pool r
    · rw [pool_eq st4 st2 r34] at h4
      by_cases hc : condP C P n t
      · obtain ⟨B, hB, hl⟩ := hP1 hc
        right
        refine ⟨B, hl1 _ (by rw [hl]; exact List.mem_singleton_self _), ?_, ?_⟩
        · rw [← hB]; exact h4
        · rw [hB] at h4; exact on_block_new_rows C P _ B r x h0 h4
      · rw [(hP0 hc).1] at h4; exact absurd h4 h0
    · by_cases ha : condA C n t
      · obtain ⟨row, -, hst5, hsent⟩ := hA1 ha
        left
        have h1' : x ∈ (Spec.Protocol.admit_attestation C st4 row).sg_pool r := by
          rw [← hst5]; exact h1
        have hm := admits_new_mem C [row] st4 r x h4
          (by rw [show Spec.Protocol.admit_attestations C st4 [row] =
                Spec.Protocol.admit_attestation C st4 row from by
                  rw [StoreSteps.admit_attestations_foldl]; rfl]
              exact h1')
        rw [List.mem_singleton] at hm
        subst hm
        rw [hsent]
        exact List.mem_append_right _ (List.mem_singleton_self _)
      · have : x ∈ st5.sg_pool r := h1
        rw [(hA0 ha).1] at this
        exact absurd this h4

omit [Inhabited V] in
/-- A Goldfish vote of the record is in the image of a store's pool exactly when its spec form is in
    the store's list of its slot. -/
theorem mem_store_pool_iff (st : Spec.Store V) (s : Spec.Slot)
    (u : DecoupledConsensusModel.GoldfishVote V) :
    u ∈ Member.store_pool st s ↔ Spec.GoldfishVote.toSpec u ∈ st.gf_votes s := by
  unfold Member.store_pool
  rw [Finset.mem_map]
  simp only [Spec.Store.pool, StoreSteps.getElem_fn, List.mem_toFinset,
    Spec.GoldfishVote.coe_toProofEmb]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact hx
  · intro h; exact ⟨_, h, rfl⟩

omit [Inhabited V] in
/-- The tick sends at most one block. -/
theorem tick_blocks_unique {C : Spec.Config} {P : Spec.Provisional V}
    {X : Spec.External V} {n n' : Spec.NodeState V}
    {t : Spec.Time} {sent : List (Spec.NamedObject V)}
    (h : (Spec.tick C P X n t).run [] = .ok (n', sent))
    {B1 B2 : Spec.Block V} (h1 : Spec.NamedObject.block B1 ∈ sent)
    (h2 : Spec.NamedObject.block B2 ∈ sent) : B1 = B2 := by
  obtain ⟨st0, st2, st3, st4, st5, sh5, l1, l2, -, hP1, hP0, hV1, hV0, -, -, hA1, hA0, -⟩ :=
    tick_steps h
  have key : ∀ B, Spec.NamedObject.block B ∈ sent →
      Spec.NamedObject.block B ∈ l1 := by
    intro B hB
    have hB2 : Spec.NamedObject.block B ∈ l2 := by
      by_cases ha : condA C n t
      · obtain ⟨row, -, -, rfl⟩ := hA1 ha
        rcases List.mem_append.mp hB with hB | hB
        · exact hB
        · cases List.mem_singleton.mp hB
      · rw [(hA0 ha).2.2] at hB; exact hB
    by_cases hv : condV C n t
    · rcases hV1 hv with ⟨-, rfl⟩ | ⟨u, -, rfl, -⟩
      · exact hB2
      · rcases List.mem_append.mp hB2 with hB2 | hB2
        · exact hB2
        · cases List.mem_singleton.mp hB2
    · rw [(hV0 hv).2] at hB2; exact hB2
  have k1 := key B1 h1
  have k2 := key B2 h2
  by_cases hc : condP C P n t
  · obtain ⟨B, -, rfl⟩ := hP1 hc
    cases List.mem_singleton.mp k1
    cases List.mem_singleton.mp k2
    rfl
  · rw [(hP0 hc).2] at k1; exact absurd k1 List.not_mem_nil

/-- No other block of the node's tree has the root of a block the tick sends and admits on its first
    store with the clock set. -/
theorem tick_not_held (S : Setup V) (v : V) (n : (Model.spec (V := V)).N) (t : Time)
    (out : (Model.spec (V := V)).N × List (NamedObject V))
    (hout : (Model.spec (V := V)).tick S v n t ⇢ out) (B : Spec.Block V)
    (hB : NamedObject.block B.toProofNamed ∈ out.2) (sg : Spec.SavedGrades V)
    (hX : B ∈ (Spec.Protocol.on_block (Setup.toSpec S).C (Setup.toSpec S).P
      { n.val.st with saved_grades := sg, t := t, s := (Setup.toSpec S).C.slotOf t } B).T) :
    ¬ RootHeldByOther n.val.st.T B := by
  rintro ⟨Y, hY, hne, hr⟩
  obtain ⟨sent, hrun, hsent⟩ := tick_out S v n t out hout
  obtain ⟨sg', ⟨-, hno⟩ | ⟨B0, hB0, he⟩⟩ := tick_shape S v n t out hout
  · exact hno _ hB
  · have hb1 : Spec.NamedObject.block B ∈ sent := by
      rw [hsent] at hB
      obtain ⟨o, ho, hoB⟩ := List.mem_map.mp hB
      cases o with
      | block B' =>
        simp only [Spec.NamedObject.toProof, NamedObject.block.injEq] at hoB
        rw [Spec.Block.toProofNamed_injective hoB] at ho
        exact ho
      | gfVote u => simp only [Spec.NamedObject.toProof, reduceCtorEq] at hoB
      | attest a => simp only [Spec.NamedObject.toProof, reduceCtorEq] at hoB
    have hb0 : Spec.NamedObject.block (Spec.Block.toSpecNamed B0) ∈ sent := by
      rw [hsent] at hB0
      obtain ⟨o, ho, hoB⟩ := List.mem_map.mp hB0
      cases o with
      | block B' =>
        simp only [Spec.NamedObject.toProof, NamedObject.block.injEq] at hoB
        rw [← hoB, Spec.Block.toSpecNamed_toProofNamed]
        exact ho
      | gfVote u => simp only [Spec.NamedObject.toProof, reduceCtorEq] at hoB
      | attest a => simp only [Spec.NamedObject.toProof, reduceCtorEq] at hoB
    have hBB := tick_blocks_unique hrun hb0 hb1
    have hT : out.1.val.st.T = (Spec.Protocol.on_block (Setup.toSpec S).C (Setup.toSpec S).P
        { n.val.st with saved_grades := sg, t := t, s := (Setup.toSpec S).C.slotOf t } B).T := by
      rw [he.1]
      show (Spec.Protocol.on_block (Setup.toSpec S).C (Setup.toSpec S).P
        { { n.val.st with t := t, s := (Setup.toSpec S).C.slotOf t } with saved_grades := sg' }
        (Spec.Block.toSpecNamed B0)).T = (Spec.Protocol.on_block (Setup.toSpec S).C (Setup.toSpec S).P
        { { n.val.st with t := t, s := (Setup.toSpec S).C.slotOf t } with saved_grades := sg } B).T
      rw [on_block_with_saved_grades, on_block_with_saved_grades, hBB]
    have hYo : Y ∈ out.1.val.st.T := by
      rw [hT]
      exact (keeps_on_block _ _ _ B).2.2.1 hY
    have hXo : B ∈ out.1.val.st.T := by rw [hT]; exact hX
    exact hne (out.1.property.2.1 Y hYo B hXo hr)

/-- The field `tick_new_vote_origin` of `NodeFacts` at `Model.spec`: a Goldfish vote `u` new in
    its slot's pool after `v`'s tick at `t` from `n` is sent by the outcome, or the outcome sends a
    named block `B` whose processing by `M.on_block_with` on `n`'s store with its clock set to `t`
    newly adds `u`. -/
theorem spec_tick_new_vote_origin :
    ∀ (S : Setup V) (v : V) (n : (Model.spec (V := V)).N) (t : Time)
        (out : (Model.spec (V := V)).N × List (NamedObject V)) (hout : (Model.spec (V := V)).tick S v n t ⇢ out) (u : GoldfishVote V)
        (hpre : u ∉ ((Model.spec (V := V)).store_pool n.st.core u.slot))
        (hpost : u ∈ ((Model.spec (V := V)).store_pool out.1.st.core u.slot)),
        NamedObject.gfVote u ∈ out.2 ∨
          ∃ B : NamedBlock V,
            NamedObject.block B ∈ out.2 ∧
            u ∉ ((Model.spec (V := V)).store_pool ((Model.spec (V := V)).ns_setClock S.E n.st t).core u.slot) ∧
            u ∈ ((Model.spec (V := V)).store_pool ((Model.spec (V := V)).on_block_with .alsoCarried S.E S.hc S.cfg
              ((Model.spec (V := V)).ns_setClock S.E n.st t) B).core u.slot) := by
  intro S v n t out hout u hpre hpost
  obtain ⟨sent, hrun, hsent⟩ := tick_out S v n t out hout
  obtain ⟨sg, st1, hst1, hmv, hmr, hnewv, hnewr⟩ := tick_origins hrun
  have hst1' : st1 = { ((Model.spec (V := V)).ns_setClock S.E n.st t).val with saved_grades := sg } := by
    rw [hst1]; rfl
  have hadmT : ∀ B : Spec.Block V, st1 ≠ Spec.Protocol.on_block (Setup.toSpec S).C (Setup.toSpec S).P st1 B →
      Spec.Protocol.block_admissible (Setup.toSpec S).C (Setup.toSpec S).P st1 B = true ∧
        B ∈ (Spec.Protocol.on_block (Setup.toSpec S).C (Setup.toSpec S).P st1 B).T := by
    intro B hne
    by_cases hadm : Spec.Protocol.block_admissible (Setup.toSpec S).C (Setup.toSpec S).P st1 B = true
    · refine ⟨hadm, ?_⟩
      rw [Handlers.on_block_eq, if_pos hadm, OkStore.admit_attestations_T]
      unfold Handlers.admitBlockCore
      rw [if_pos hadm, SubtypeEqualities.blockCore_T]
      exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
    · exact absurd (by rw [Handlers.on_block_eq, if_neg hadm]) hne
  have hheld : ∀ B : Spec.Block V, NamedObject.block B.toProofNamed ∈ out.2 →
      st1 ≠ Spec.Protocol.on_block (Setup.toSpec S).C (Setup.toSpec S).P st1 B →
      ¬ RootHeldByOther ((Model.spec (V := V)).ns_setClock S.E n.st t).val.T B := by
    intro B hB hne
    have := tick_not_held S v n t out hout B hB sg (by rw [← hst1]; exact (hadmT B hne).2)
    exact this
  have h0 : Spec.GoldfishVote.toSpec u ∉ st1.gf_votes (Spec.GoldfishVote.toSpec u).slot := by
    rw [hst1]; exact fun h => hpre ((mem_store_pool_iff _ _ _).2 h)
  have h1 : Spec.GoldfishVote.toSpec u ∈ out.1.val.st.gf_votes (Spec.GoldfishVote.toSpec u).slot :=
    (mem_store_pool_iff _ _ _).1 hpost
  rcases hnewv _ h0 h1 with hv | ⟨B, hB, hm, -⟩
  · left; rw [hsent]; exact List.mem_map_of_mem hv
  · right
    have hBo : NamedObject.block B.toProofNamed ∈ out.2 := by rw [hsent]; exact List.mem_map_of_mem hB
    have hne : st1 ≠ Spec.Protocol.on_block (Setup.toSpec S).C (Setup.toSpec S).P st1 B := by
      intro e; rw [← e] at hm; exact h0 hm
    have hh := hheld B hBo hne
    refine ⟨B.toProofNamed, hBo, fun h => hpre h, ?_⟩
    show u ∈ Member.store_pool (OkMember.on_block_with .alsoCarried S.E S.hc S.cfg
      ((Model.spec (V := V)).ns_setClock S.E n.st t) B.toProofNamed).val u.slot
    rw [OkMember.on_block_with_val_of_not_held (by rw [Spec.Block.toSpecNamed_toProofNamed]; exact hh),
      mem_store_pool_iff]
    show Spec.GoldfishVote.toSpec u ∈ (Spec.Protocol.on_block (Setup.toSpec S).C (Setup.toSpec S).P
      ((Model.spec (V := V)).ns_setClock S.E n.st t).val (Spec.Block.toSpecNamed B.toProofNamed)).gf_votes u.slot
    rw [Spec.Block.toSpecNamed_toProofNamed]
    rw [hst1', on_block_with_saved_grades] at hm
    exact hm

/-- The field `tick_new_full_row_origin` of `NodeFacts` at `Model.spec`: a named attestation
    new among the rows of its round after `v`'s tick at `t` from `n` is sent by the outcome, or the
    outcome sends a block `B` whose processing on `n`'s store with its clock set to `t` newly adds
    it. -/
theorem spec_tick_new_full_row_origin :
    ∀ (S : Setup V) (v : V) (n : (Model.spec (V := V)).N) (t : Time)
        (out : (Model.spec (V := V)).N × List (NamedObject V)) (hout : (Model.spec (V := V)).tick S v n t ⇢ out)
        (a : NamedAttestation V) (hpre : a ∉ n.st.sg_rows a.round)
        (hpost : a ∈ out.1.st.sg_rows a.round),
        NamedObject.attest a ∈ out.2 ∨
          ∃ B, NamedObject.block B ∈ out.2 ∧
            a ∉ ((Model.spec (V := V)).ns_setClock S.E n.st t).sg_rows a.round ∧
            a ∈ ((Model.spec (V := V)).on_block_with .alsoCarried S.E S.hc S.cfg ((Model.spec (V := V)).ns_setClock S.E n.st t) B).sg_rows a.round := by
  intro S v n t out hout a hpre hpost
  obtain ⟨sent, hrun, hsent⟩ := tick_out S v n t out hout
  obtain ⟨sg, st1, hst1, hmv, hmr, hnewv, hnewr⟩ := tick_origins hrun
  have hst1' : st1 = { ((Model.spec (V := V)).ns_setClock S.E n.st t).val with saved_grades := sg } := by
    rw [hst1]; rfl
  have hadmT : ∀ B : Spec.Block V, st1 ≠ Spec.Protocol.on_block (Setup.toSpec S).C (Setup.toSpec S).P st1 B →
      Spec.Protocol.block_admissible (Setup.toSpec S).C (Setup.toSpec S).P st1 B = true ∧
        B ∈ (Spec.Protocol.on_block (Setup.toSpec S).C (Setup.toSpec S).P st1 B).T := by
    intro B hne
    by_cases hadm : Spec.Protocol.block_admissible (Setup.toSpec S).C (Setup.toSpec S).P st1 B = true
    · refine ⟨hadm, ?_⟩
      rw [Handlers.on_block_eq, if_pos hadm, OkStore.admit_attestations_T]
      unfold Handlers.admitBlockCore
      rw [if_pos hadm, SubtypeEqualities.blockCore_T]
      exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
    · exact absurd (by rw [Handlers.on_block_eq, if_neg hadm]) hne
  have hheld : ∀ B : Spec.Block V, NamedObject.block B.toProofNamed ∈ out.2 →
      st1 ≠ Spec.Protocol.on_block (Setup.toSpec S).C (Setup.toSpec S).P st1 B →
      ¬ RootHeldByOther ((Model.spec (V := V)).ns_setClock S.E n.st t).val.T B := by
    intro B hB hne
    have := tick_not_held S v n t out hout B hB sg (by rw [← hst1]; exact (hadmT B hne).2)
    exact this
  obtain ⟨a', rfl⟩ := HandlersFacts.exists_namedAtt a
  have h0 : a' ∉ st1.sg_pool a'.toProofNamed.round := by
    rw [hst1]; exact fun h => hpre ((HandlersRunFacts.mem_sg_rows_iff n.val.st _ a').2 h)
  have h1 := (HandlersRunFacts.mem_sg_rows_iff out.1.val.st _ a').1 hpost
  rcases hnewr _ _ h0 h1 with hv | ⟨B, hB, hm, -⟩
  · left; rw [hsent]; exact List.mem_map_of_mem hv
  · right
    have hBo : NamedObject.block B.toProofNamed ∈ out.2 := by rw [hsent]; exact List.mem_map_of_mem hB
    have hne : st1 ≠ Spec.Protocol.on_block (Setup.toSpec S).C (Setup.toSpec S).P st1 B := by
      intro e; rw [← e] at hm; exact h0 hm
    have hh := hheld B hBo hne
    refine ⟨B.toProofNamed, hBo, fun h => hpre h, ?_⟩
    apply (HandlersRunFacts.mem_sg_rows_iff (OkMember.on_block_with .alsoCarried S.E S.hc S.cfg
      ((Model.spec (V := V)).ns_setClock S.E n.st t) B.toProofNamed).val _ a').2
    rw [OkMember.on_block_with_val_of_not_held (by rw [Spec.Block.toSpecNamed_toProofNamed]; exact hh)]
    show a' ∈ (Spec.Protocol.on_block (Setup.toSpec S).C (Setup.toSpec S).P
      ((Model.spec (V := V)).ns_setClock S.E n.st t).val (Spec.Block.toSpecNamed B.toProofNamed)).sg_pool _
    rw [Spec.Block.toSpecNamed_toProofNamed]
    rw [hst1', on_block_with_saved_grades] at hm
    exact hm

/-- The field `addsOnlyCarried_node_tick` of `NodeFacts` at `Model.spec`: with `st₀` the store
    of `n` with its clock set to `t`, an outcome of `v`'s tick at `t` keeps everything `st₀` holds,
    and every block, vote or attestation it newly holds is one it sends or, for a vote or an
    attestation, one included in a block it sends that the core call at `st₀` newly admits. -/
theorem spec_addsOnlyCarried_node_tick :
    ∀ (S : Setup V) (v : V) (n : (Model.spec (V := V)).N) (t : Int)
        (out : (Model.spec (V := V)).N × List (NamedObject V)) (hout : (Model.spec (V := V)).tick S v n t ⇢ out),
        ((∀ B : NamedBlock V, B ∈ ((Model.spec (V := V)).ns_setClock S.E n.st t).bodies → B ∈ out.1.st.bodies) ∧
          (∀ u : GoldfishVote V, u ∈ ((Model.spec (V := V)).ns_setClock S.E n.st t).core.gf_votes u.slot →
            u ∈ out.1.st.core.gf_votes u.slot) ∧
          (∀ a : NamedAttestation V, a ∈ ((Model.spec (V := V)).ns_setClock S.E n.st t).sg_rows a.round →
            a ∈ out.1.st.sg_rows a.round)) ∧
        (∀ B : NamedBlock V, B ∉ ((Model.spec (V := V)).ns_setClock S.E n.st t).bodies → B ∈ out.1.st.bodies →
          NamedObject.block B ∈ out.2) ∧
        (∀ u : GoldfishVote V, u ∉ ((Model.spec (V := V)).ns_setClock S.E n.st t).core.gf_votes u.slot →
          u ∈ out.1.st.core.gf_votes u.slot →
          NamedObject.gfVote u ∈ out.2 ∨ ∃ B : NamedBlock V, NamedObject.block B ∈ out.2 ∧
            (∃ j : Nat, B.gf_votes[j]? = some u) ∧
            B.erase ∉ ((Model.spec (V := V)).ns_setClock S.E n.st t).core.T ∧
            B.erase ∈ ((Model.spec (V := V)).postCore S ((Model.spec (V := V)).ns_setClock S.E n.st t) B).core.T) ∧
        (∀ a : NamedAttestation V, a ∉ ((Model.spec (V := V)).ns_setClock S.E n.st t).sg_rows a.round →
          a ∈ out.1.st.sg_rows a.round →
          NamedObject.attest a ∈ out.2 ∨ ∃ B : NamedBlock V, NamedObject.block B ∈ out.2 ∧
            (∃ j : Nat, B.attestations[j]? = some a) ∧
            B ∉ ((Model.spec (V := V)).ns_setClock S.E n.st t).bodies ∧
            B ∈ ((Model.spec (V := V)).postCore S ((Model.spec (V := V)).ns_setClock S.E n.st t) B).bodies) := by
  intro S v n t out hout
  obtain ⟨sent, hrun, hsent⟩ := tick_out S v n t out hout
  obtain ⟨sg, st1, hst1, hmv, hmr, hnewv, hnewr⟩ := tick_origins hrun
  have hst1' : st1 = { ((Model.spec (V := V)).ns_setClock S.E n.st t).val with saved_grades := sg } := by
    rw [hst1]; rfl
  have hadmT : ∀ B : Spec.Block V, st1 ≠ Spec.Protocol.on_block (Setup.toSpec S).C (Setup.toSpec S).P st1 B →
      Spec.Protocol.block_admissible (Setup.toSpec S).C (Setup.toSpec S).P st1 B = true ∧
        B ∈ (Spec.Protocol.on_block (Setup.toSpec S).C (Setup.toSpec S).P st1 B).T := by
    intro B hne
    by_cases hadm : Spec.Protocol.block_admissible (Setup.toSpec S).C (Setup.toSpec S).P st1 B = true
    · refine ⟨hadm, ?_⟩
      rw [Handlers.on_block_eq, if_pos hadm, OkStore.admit_attestations_T]
      unfold Handlers.admitBlockCore
      rw [if_pos hadm, SubtypeEqualities.blockCore_T]
      exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
    · exact absurd (by rw [Handlers.on_block_eq, if_neg hadm]) hne
  have hheld : ∀ B : Spec.Block V, NamedObject.block B.toProofNamed ∈ out.2 →
      st1 ≠ Spec.Protocol.on_block (Setup.toSpec S).C (Setup.toSpec S).P st1 B →
      ¬ RootHeldByOther ((Model.spec (V := V)).ns_setClock S.E n.st t).val.T B := by
    intro B hB hne
    have := tick_not_held S v n t out hout B hB sg (by rw [← hst1]; exact (hadmT B hne).2)
    exact this
  have hadm' : ∀ B : Spec.Block V, st1 ≠ Spec.Protocol.on_block (Setup.toSpec S).C (Setup.toSpec S).P st1 B →
      Spec.Protocol.block_admissible (Spec.Config.toSpec S.E S.hc S.cfg)
        (Spec.Provisional.toSpec S.E) ((Model.spec (V := V)).ns_setClock S.E n.st t).val
        (Spec.Block.toSpecNamed B.toProofNamed) = true := by
    intro B hne
    have h := (hadmT B hne).1
    rw [hst1'] at h
    rw [Spec.Block.toSpecNamed_toProofNamed]
    exact h
  refine ⟨⟨fun B hB => ?_, fun u hu => ?_, fun a ha => ?_⟩, fun B hpre hpost => ?_, fun u hpre hpost => ?_,
    fun a hpre hpost => ?_⟩
  · exact tick_bodies_subset (v := v) (t := t) (n := n.val) (out := (out.1.val, out.2)) hout hB
  · apply (mem_map_toProof_iff _ _).2
    apply hmv
    rw [hst1]
    exact (mem_map_toProof_iff _ _).1 hu
  · obtain ⟨a', rfl⟩ := HandlersFacts.exists_namedAtt a
    apply (HandlersRunFacts.mem_sg_rows_iff out.1.val.st _ a').2
    apply hmr
    rw [hst1]
    exact (HandlersRunFacts.mem_sg_rows_iff n.val.st _ a').1 ha
  · exact spec_tick_new_body_origin S v n t out hout B hpre hpost
  · have h0 : Spec.GoldfishVote.toSpec u ∉ st1.gf_votes (Spec.GoldfishVote.toSpec u).slot := by
      rw [hst1]; exact fun h => hpre ((mem_map_toProof_iff _ _).2 h)
    have h1 : Spec.GoldfishVote.toSpec u ∈ out.1.val.st.gf_votes (Spec.GoldfishVote.toSpec u).slot :=
      (mem_map_toProof_iff _ _).1 hpost
    rcases hnewv _ h0 h1 with hv | ⟨B, hB, hm, hmB⟩
    · left; rw [hsent]; exact List.mem_map_of_mem hv
    · right
      have hBo : NamedObject.block B.toProofNamed ∈ out.2 := by rw [hsent]; exact List.mem_map_of_mem hB
      have hne : st1 ≠ Spec.Protocol.on_block (Setup.toSpec S).C (Setup.toSpec S).P st1 B := by
        intro e; rw [← e] at hm; exact h0 hm
      have hh : ¬ RootHeldByOther ((Model.spec (V := V)).ns_setClock S.E n.st t).val.T
          (Spec.Block.toSpecNamed B.toProofNamed) := by
        rw [Spec.Block.toSpecNamed_toProofNamed]; exact hheld B hBo hne
      obtain ⟨e1, e2, -, -⟩ := erase_cases_of_admissible S _ B.toProofNamed hh (hadm' B hne)
      refine ⟨B.toProofNamed, hBo, ?_, e1, e2⟩
      apply exists_getElem?_of_mem
      rw [← toSpecNamed_gf_votes_map B.toProofNamed, Spec.Block.toSpecNamed_toProofNamed]
      exact List.mem_map_of_mem hmB
  · obtain ⟨a', rfl⟩ := HandlersFacts.exists_namedAtt a
    have h0 : a' ∉ st1.sg_pool a'.toProofNamed.round := by
      rw [hst1]; exact fun h => hpre ((HandlersRunFacts.mem_sg_rows_iff n.val.st _ a').2 h)
    have h1 := (HandlersRunFacts.mem_sg_rows_iff out.1.val.st _ a').1 hpost
    rcases hnewr _ _ h0 h1 with hv | ⟨B, hB, hm, hmB⟩
    · left; rw [hsent]; exact List.mem_map_of_mem hv
    · right
      have hBo : NamedObject.block B.toProofNamed ∈ out.2 := by rw [hsent]; exact List.mem_map_of_mem hB
      have hne : st1 ≠ Spec.Protocol.on_block (Setup.toSpec S).C (Setup.toSpec S).P st1 B := by
        intro e; rw [← e] at hm; exact h0 hm
      have hh : ¬ RootHeldByOther ((Model.spec (V := V)).ns_setClock S.E n.st t).val.T
          (Spec.Block.toSpecNamed B.toProofNamed) := by
        rw [Spec.Block.toSpecNamed_toProofNamed]; exact hheld B hBo hne
      obtain ⟨-, -, e3, e4⟩ := erase_cases_of_admissible S _ B.toProofNamed hh (hadm' B hne)
      refine ⟨B.toProofNamed, hBo, ?_, e3, e4⟩
      apply exists_getElem?_of_mem
      rw [SubtypeEqualities.toProofNamed_attestations]
      exact List.mem_map_of_mem hmB

/-! ## The coherence of a store of the subtype -/

omit [Inhabited V] in
/-- The spec's `state_transition` at `Config.toSpec E hc cfg` does not read the round schedule `hc`. -/
theorem state_transition_hc (E : DecoupledConsensusModel.Env V)
    (hc hc' : DecoupledConsensusModel.Protocol.HealConfig)
    (cfg : DecoupledConsensusModel.Protocol.HeightConfig) (P : Spec.Provisional V)
    (σ : Spec.Protocol.ChainState V) (B : Spec.Block V) :
    Spec.Protocol.state_transition (Spec.Config.toSpec E hc cfg) P σ B =
      Spec.Protocol.state_transition (Spec.Config.toSpec E hc' cfg) P σ B := by
  simp only [Spec.Protocol.state_transition, Spec.Protocol.process_height_events,
    Spec.Protocol.progReady, Spec.Protocol.advance_height,
    Spec.Protocol.nonjustifiable, Spec.Config.toSpec]
  rfl

omit [Fintype V] [Inhabited V] in
/-- A parent-closed tree holding a block holds the genesis block. -/
theorem genesis_mem_of_parentClosed {T : Finset (Spec.Block V)}
    (hpc : NoRaise.ParentClosed T) {X : Spec.Block V} (hX : X ∈ T) :
    Spec.Block.genesis ∈ T := by
  induction X with
  | genesis => exact hX
  | node p s r gv gs ats pr ih => exact ih (hpc _ hX)

/-- A store of the subtype whose tree blocks have their derived chain states (`DerivedView`) is
    coherent. -/
theorem coherent_of_derivedView (E : Env V) (cfg : Protocol.HeightConfig)
    (st : (Model.spec (V := V)).NS)
    (h : Restated.Vocabulary.Proofs.NamedStore.DerivedView (Model.spec (V := V)) E cfg st) :
    Restated.Vocabulary.Proofs.NamedStore.Coherent (Model.spec (V := V)) E cfg st := by
  obtain ⟨hstamp, hd, hpc, hF⟩ := st.property
  refine ⟨?_, ?_, ⟨?_, ?_⟩, ?_, h⟩
  · show st.val.T.image Spec.Block.toProof =
      (st.val.T.map Spec.Block.toProofNamedEmb).image NamedBlock.erase
    rw [Finset.map_eq_image, Finset.image_image]
    congr 1
    funext X
    simp [Spec.Block.toProofNamed_erase]
  · intro A hA B hB hAB
    have hA' : A ∈ st.val.T.map Spec.Block.toProofNamedEmb := hA
    have hB' : B ∈ st.val.T.map Spec.Block.toProofNamedEmb := hB
    obtain ⟨X, hX, rfl⟩ := Finset.mem_map.mp hA'
    obtain ⟨Y, hY, rfl⟩ := Finset.mem_map.mp hB'
    simp only [Spec.Block.coe_toProofNamedEmb, Spec.Block.toProofNamed_erase] at hAB
    rw [hd X hX Y hY (root_eq_of_toProof_eq hAB)]
  · show NamedBlock.genesis ∈ st.val.T.map Spec.Block.toProofNamedEmb
    exact Finset.mem_map.mpr ⟨_, genesis_mem_of_parentClosed hpc hF, rfl⟩
  · intro B hB
    have hB' : B ∈ st.val.T.map Spec.Block.toProofNamedEmb := hB
    obtain ⟨X, hX, rfl⟩ := Finset.mem_map.mp hB'
    show _ ∈ st.val.T.map Spec.Block.toProofNamedEmb
    rw [Spec.Block.coe_toProofNamedEmb, SubtypeEqualities.toProofNamed_parent]
    exact Finset.mem_map_of_mem _ (hpc X hX)
  · intro r
    show (st.val.attestations r).map Spec.Attestation.toProof =
      ((st.val.attestations r).map Spec.Attestation.toProofNamed).map
        NamedAttestation.erase
    rw [List.map_map]
    congr 1
    funext a
    simp [Spec.Attestation.toProofNamed_erase]

/-- `DerivedView` at a store of the subtype holds exactly when every tree block's chain state is the
    member `derive_named` of its named image. -/
theorem derivedView_iff (E : Env V) (cfg : Protocol.HeightConfig)
    (st : (Model.spec (V := V)).NS) :
    Restated.Vocabulary.Proofs.NamedStore.DerivedView (Model.spec (V := V)) E cfg st ↔
      ∀ X ∈ st.val.T, st.val.σ X = Member.derive_named E cfg X.toProofNamed := by
  constructor
  · intro h X hX
    have := h X.toProofNamed (Finset.mem_map_of_mem _ hX)
    change st.val.σ (st.val.blockOfImage X.toProofNamed.erase) = _ at this
    rwa [Spec.Block.toProofNamed_erase, σ_read _ st.property.2.1 hX] at this
  · intro h B hB
    have hB' : B ∈ st.val.T.map Spec.Block.toProofNamedEmb := hB
    obtain ⟨X, hX, rfl⟩ := Finset.mem_map.mp hB'
    change st.val.σ (st.val.blockOfImage (Spec.Block.toProofNamed X).erase) = _
    rw [Spec.Block.toProofNamed_erase, σ_read _ st.property.2.1 hX]
    exact h X hX

/-- The field `coherent_postCore` of `NodeFacts` at `Model.spec`: if `before` is coherent, the
    named store after the core call on `B` is coherent. -/
theorem spec_coherent_postCore :
    ∀ (S : Setup V) (before : (Model.spec (V := V)).NS) (B : NamedBlock V),
        DecoupledConsensusModel.Sts.Restated.Vocabulary.Proofs.NamedStore.Coherent (Model.spec (V := V)) S.E S.cfg before →
        DecoupledConsensusModel.Sts.Restated.Vocabulary.Proofs.NamedStore.Coherent (Model.spec (V := V)) S.E S.cfg ((Model.spec (V := V)).postCore S before B) := by
  intro S before B hcoh
  apply coherent_of_derivedView
  have hdv := (derivedView_iff S.E S.cfg before).1 hcoh.2.2.2.2
  apply (derivedView_iff S.E S.cfg _).2
  by_cases hheld : RootHeldByOther before.val.T (Spec.Block.toSpecNamed B)
  · have e : (Model.spec (V := V)).postCore S before B = before := OkMember.postCore_of_held hheld
    rw [e]; exact hdv
  · have hval : ((Model.spec (V := V)).postCore S before B).val = Member.postCore S before.val B :=
      OkMember.postCore_val_of_not_held hheld
    rw [hval]
    unfold Member.postCore Handlers.admitBlockCore
    split_ifs with hadm
    · have e1 : Spec.Protocol.on_block (Spec.Config.toSpec S.E S.hc S.cfg)
          (Spec.Provisional.toSpec S.E) before.val (Spec.Block.toSpecNamed B) =
          Spec.Protocol.admit_attestations (Spec.Config.toSpec S.E S.hc S.cfg)
            (Handlers.blockCore (Spec.Config.toSpec S.E S.hc S.cfg)
              (Spec.Provisional.toSpec S.E) before.val (Spec.Block.toSpecNamed B))
            (Spec.Block.toSpecNamed B).attestations := by
        rw [Handlers.on_block_eq, if_pos hadm]
        unfold Handlers.admitBlockCore
        rw [if_pos hadm]
      obtain ⟨x, y, e2⟩ := StoreSteps.admit_attestations_writes (Spec.Config.toSpec S.E S.hc S.cfg)
        (Spec.Block.toSpecNamed B).attestations
        (Handlers.blockCore (Spec.Config.toSpec S.E S.hc S.cfg)
          (Spec.Provisional.toSpec S.E) before.val (Spec.Block.toSpecNamed B))
      have hσ : (Handlers.blockCore (Spec.Config.toSpec S.E S.hc S.cfg)
          (Spec.Provisional.toSpec S.E) before.val (Spec.Block.toSpecNamed B)).σ =
          (Member.receipt_process S before.val (.block B)).σ := by
        show _ = (Spec.Protocol.on_block _ _ before.val _).σ
        rw [e1, e2]
      have hT : (Handlers.blockCore (Spec.Config.toSpec S.E S.hc S.cfg)
          (Spec.Provisional.toSpec S.E) before.val (Spec.Block.toSpecNamed B)).T =
          (Member.receipt_process S before.val (.block B)).T := by
        show _ = (Spec.Protocol.on_block _ _ before.val _).T
        rw [e1, e2]
      rcases SubtypeEqualities.receipt_cases S before.val (.block B) with
        ⟨hT', hσ', -⟩ | ⟨B1, hB1, hadm', hT', hσ', -⟩
      · intro X hX
        rw [hσ, hσ']
        rw [hT, hT'] at hX
        exact hdv X hX
      · cases hB1
        intro X hX
        rw [hT, hT'] at hX
        rw [hσ, hσ']
        by_cases hXe : X = Spec.Block.toSpecNamed B
        · subst hXe
          rw [Function.update_self, Spec.Block.toProofNamed_toSpecNamed]
          obtain ⟨⟨hXT, hpar⟩, -⟩ := (SubtypeEqualities.block_admissible_iff _ _ _ _).mp hadm'
          rw [hdv _ hpar]
          cases B with
          | genesis =>
            exact absurd (genesis_mem_of_parentClosed before.property.2.2.1 before.property.2.2.2) hXT
          | node p s r gv gs ats pr =>
            rw [toSpecNamed_parent, Spec.Block.toProofNamed_toSpecNamed]
            show _ = Member.named_transition S.E S.cfg (Member.derive_named S.E S.cfg p)
              (.node p s r gv gs ats pr)
            unfold Member.named_transition
            simp only [DecoupledConsensusModel.NamedBlock.parent]
            exact state_transition_hc (V := V) S.E S.hc _ S.cfg (Spec.Provisional.toSpec S.E)
              (Member.derive_named S.E S.cfg p) _
        · rw [Function.update_of_ne hXe]
          rcases Finset.mem_union.mp hX with h | h
          · exact hdv X h
          · exact absurd (Finset.mem_singleton.mp h) hXe
    · exact hdv

/-- The field `initial_invariants` of `NodeFacts` at `Model.spec`: the named store of every
    validator's initial node state satisfies the confirmation-membership invariant, and its named
    signing record satisfies the tick record invariant. -/
theorem spec_initial_invariants :
    ∀ (S : Setup V) (v : V),
        Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant (Model.spec (V := V)) S.E S.cfg ((Model.spec (V := V)).initial S v).st ∧
          Restated.Vocabulary.Proofs.NamedTickRecord.Invariant (Model.spec (V := V)) ((Model.spec (V := V)).initial S v).record := by
  intro S v
  have hrec : (Spec.SigningHistory.initial).toProof = Protocol.NamedRecord.initial := by
    simp only [Spec.SigningHistory.toProof, Protocol.NamedRecord.initial,
      Protocol.Record.initial, Spec.SigningHistory.initial]
    rfl
  have hgen : Spec.Block.genesis.toProof ∈
      (Spec.Store.init : Spec.Store V).T.image Spec.Block.toProof :=
    Finset.mem_image_of_mem _ (Finset.mem_singleton_self _)
  refine ⟨⟨⟨coherent_of_derivedView _ _ _ ?_, hgen, hgen⟩, hgen, hgen, hgen⟩, ?_⟩
  · apply (derivedView_iff _ _ _).2
    intro X hX
    have hX' : X = Spec.Block.genesis :=
      Finset.mem_singleton.mp (show X ∈ (Spec.Store.init : Spec.Store V).T from hX)
    subst hX'
    rfl
  · have h := Proofs.NamedTickRecord.invariant_initial
    rw [← hrec] at h
    exact h


/-!
## The raw grade-2 test, and the confirmation-membership invariant of the receipt and the tick
-/


/-- The field `gradeContract_read_rawG2` of `NodeFacts` at `Model.spec`: for every outcome `g`
    of the grade contract's read of `c` at `st` and `r`, the raw grade-2 field of `g` holds exactly
    when the grade-2 result of the round-`r` frame read from `c` at `st` is a completed block. -/
theorem spec_gradeContract_read_rawG2 :
    ∀ (c : (Model.spec (V := V)).Cache) (E : Env V) (hc : Protocol.HealConfig) (st : (Model.spec (V := V)).HS)
        (r : Round), ∀ g : DecoupledConsensusModel.Protocol.GradeRead V, ((Model.spec (V := V)).gradeContract c).read E hc st r ⇢ g → g.rawG2
          = (((((Model.spec (V := V)).readFrame c st r).g2.bind id).isSome = true) : Prop) := by
  intro c E hc st r g hg
  have hg0 : (Model.spec (V := V)).frameGradeRead c E hc st r ⇢ g := hg
  have hg' := (SpecRecord.returns_successOutcomes _ _).1 hg0
  cases hr : Spec.Protocol.round_grade_read
      { Spec.Store.ofImage st.val with saved_grades := SpecRecord.fill (Spec.Protocol.advance_to_round
        (st.val.contractOfImage c) r) } r with
  | error e =>
    rw [hr] at hg'
    cases hg'
  | ok gr =>
    rw [hr] at hg'
    simp only [Except.map, Except.ok.injEq] at hg'
    subst hg'
    simp only [Spec.Protocol.round_grade_read] at hr
    obtain ⟨A, -, hr⟩ := SpecRecord.NoRaise.DRE.of_bind_ok hr
    obtain ⟨Q2, -, hr⟩ := SpecRecord.NoRaise.DRE.of_bind_ok hr
    obtain ⟨G0, -, hr⟩ := SpecRecord.NoRaise.DRE.of_bind_ok hr
    obtain ⟨raw, hraw, hr⟩ := SpecRecord.NoRaise.DRE.of_bind_ok hr
    simp only [pure, Except.pure, Except.ok.injEq] at hr
    subst hr
    rw [GradesImages.round_grades_ofImage_eq_fillRound_readFrame st.property] at hraw
    show (raw = true) = ((((Member.readFrame c st.val r).g2.toProof).bind id).isSome = true)
    cases h2 : (Member.readFrame c st.val r).g2 with
    | pending =>
      simp only [Spec.Protocol.rawG2, SpecRecord.fillRound, h2,
        SpecRecord.fillResult] at hraw
      cases hraw
      simp
    | computed G =>
      simp only [Spec.Protocol.rawG2, SpecRecord.fillRound, h2,
        SpecRecord.fillResult] at hraw
      cases hraw
      cases G <;> simp

omit [Fintype V] [Inhabited V] in
/-- If `T` is parent-closed and `X` is a block of `T`, every block `A` with `A ⪯ X.toProof` is
    `Y.toProof` for some block `Y` of `T`. -/
theorem preceq_toProof_mem_image {T : Finset (Spec.Block V)}
    (hpc : NoRaise.ParentClosed T) {X : Spec.Block V} (hX : X ∈ T)
    {A : DecoupledConsensusModel.Block V} (h : DecoupledConsensusModel.Block.Preceq A X.toProof) :
    A ∈ T.image Spec.Block.toProof := by
  induction X with
  | genesis =>
    have e : A = Spec.Block.genesis.toProof := by
      simpa [DecoupledConsensusModel.Block.Preceq, DecoupledConsensusModel.Block.preceq] using h
    rw [e]
    exact Finset.mem_image_of_mem _ hX
  | node p s r gv gs ats pr ih =>
    have hn : (Spec.Block.node p s r gv gs ats pr).toProof =
        .node p.toProof s r.toProof (gv.map Spec.GoldfishVote.toProof)
          (gs.map Spec.GoldfishVote.toProof) (ats.map Spec.Attestation.toProof)
          pr := rfl
    rw [hn] at h
    simp only [DecoupledConsensusModel.Block.Preceq, DecoupledConsensusModel.Block.preceq,
      Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with h | h
    · rw [h, ← hn]
      exact Finset.mem_image_of_mem _ hX
    · exact ih (hpc _ hX) (by simpa [DecoupledConsensusModel.Block.Preceq] using h)

/-- If every tree block of `st` has the chain state `derive_named` gives it, so does every tree
    block of the store the spec's receipt of `o` returns. -/
theorem derived_receipt (S : Setup V) (st : Spec.Store V) (o : NamedObject V)
    (hpc : NoRaise.ParentClosed st.T) (hF : st.F ∈ st.T)
    (hdv : ∀ X ∈ st.T, st.σ X = Member.derive_named S.E S.cfg X.toProofNamed) :
    ∀ X ∈ (Member.receipt_process S st o).T,
      (Member.receipt_process S st o).σ X = Member.derive_named S.E S.cfg X.toProofNamed := by
  rcases SubtypeEqualities.receipt_cases S st o with
    ⟨hT', hσ', -⟩ | ⟨B, rfl, hadm', hT', hσ', -⟩
  · intro X hX
    rw [hσ']
    rw [hT'] at hX
    exact hdv X hX
  · intro X hX
    rw [hT'] at hX
    rw [hσ']
    by_cases hXe : X = Spec.Block.toSpecNamed B
    · subst hXe
      rw [Function.update_self, Spec.Block.toProofNamed_toSpecNamed]
      obtain ⟨⟨hXT, hpar⟩, -⟩ := (SubtypeEqualities.block_admissible_iff _ _ _ _).mp hadm'
      rw [hdv _ hpar]
      cases B with
      | genesis =>
        exact absurd (genesis_mem_of_parentClosed hpc hF) hXT
      | node p s r gv gs ats pr =>
        rw [toSpecNamed_parent, Spec.Block.toProofNamed_toSpecNamed]
        show _ = Member.named_transition S.E S.cfg (Member.derive_named S.E S.cfg p)
          (.node p s r gv gs ats pr)
        unfold Member.named_transition
        simp only [DecoupledConsensusModel.NamedBlock.parent]
        exact state_transition_hc (V := V) S.E S.hc _ S.cfg (Spec.Provisional.toSpec S.E)
          (Member.derive_named S.E S.cfg p) _
    · rw [Function.update_of_ne hXe]
      rcases Finset.mem_union.mp hX with h | h
      · exact hdv X h
      · exact absurd (Finset.mem_singleton.mp h) hXe

/-- If the images of `st.F` and `st.J` are images of blocks of `st.T`, the same holds of the store
    the spec's receipt of `o` returns, provided that store's tree is parent-closed and its blocks
    have their derived chain states. -/
theorem roots_receipt (S : Setup V) (st : Spec.Store V) (o : NamedObject V)
    (hdv' : ∀ X ∈ (Member.receipt_process S st o).T, (Member.receipt_process S st o).σ X =
      Member.derive_named S.E S.cfg X.toProofNamed)
    (hpc : NoRaise.ParentClosed (Member.receipt_process S st o).T)
    (hF0 : st.F.toProof ∈ st.T.image Spec.Block.toProof)
    (hJ0 : st.J.toProof ∈ st.T.image Spec.Block.toProof) :
    (Member.receipt_process S st o).F.toProof ∈
        (Member.receipt_process S st o).T.image Spec.Block.toProof ∧
      (Member.receipt_process S st o).J.toProof ∈
        (Member.receipt_process S st o).T.image Spec.Block.toProof := by
  have hk := keeps_receipt_process S st o
  have himg : ∀ {Y : Spec.Block V}, Y.toProof ∈ st.T.image Spec.Block.toProof →
      Y.toProof ∈ (Member.receipt_process S st o).T.image Spec.Block.toProof :=
    fun h => Finset.image_subset_image hk.2.2.1 h
  rcases SubtypeEqualities.receipt_cases S st o with
    ⟨-, -, -, -, hJ', -, hF'⟩ | ⟨B, rfl, -, hT', hσ', -, -, hJc, hFc⟩
  · rw [hF', hJ']
    exact ⟨himg hF0, himg hJ0⟩
  · have hXm : Spec.Block.toSpecNamed B ∈ (Member.receipt_process S st (.block B)).T := by
      rw [hT']
      exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
    have hv := hdv' _ hXm
    rw [hσ', Function.update_self] at hv
    have hgeo := Proofs.NamedDerivationGeometry.derive_named_anchors_preceq S.E S.cfg
      (Spec.Block.toSpecNamed B).toProofNamed
    rw [← toProof_derive_named, ← hv, Spec.Block.toProofNamed_erase] at hgeo
    refine ⟨?_, ?_⟩
    · rcases hFc with e | ⟨e, -⟩
      · rw [e]; exact himg hF0
      · rw [e]; exact preceq_toProof_mem_image hpc hXm hgeo.1
    · rcases hJc with ⟨e, -⟩ | ⟨e, -⟩
      · rw [e]; exact himg hJ0
      · rw [e]; exact preceq_toProof_mem_image hpc hXm hgeo.2

/-- The field `invariants_process` of `NodeFacts` at `Model.spec`: if `n`'s named store
    satisfies the confirmation-membership invariant and its named signing record the tick record
    invariant, both hold of every node state `n`'s receipt of `o` returns. -/
theorem spec_invariants_process :
    ∀ (S : Setup V) (n : (Model.spec (V := V)).N) (o : NamedObject V)
        (hStore : Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant (Model.spec (V := V)) S.E S.cfg n.st)
        (hRecord : Restated.Vocabulary.Proofs.NamedTickRecord.Invariant (Model.spec (V := V)) n.record)
        (n' : (Model.spec (V := V)).N) (hn' : (Model.spec (V := V)).process S n o ⇢ n'),
        Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant (Model.spec (V := V)) S.E S.cfg n'.st ∧
          Restated.Vocabulary.Proofs.NamedTickRecord.Invariant (Model.spec (V := V)) n'.record := by
  intro S n o hStore hRecord n' hn'
  obtain ⟨⟨hcoh, hF0, hJ0⟩, hc1, hc2, hc3⟩ := hStore
  have hval : n'.val = { n.val with st := Spec.make_grades_compatible_with_finalized (Member.receipt_process S n.val.st o) } := by
    rw [(process_returns_iff S n.val n'.val o).mp hn', receiveNamedObject_eq]
  have hst : n'.val.st = Spec.make_grades_compatible_with_finalized
      (Member.receipt_process S n.val.st o) := by rw [hval]
  have hdv := (derivedView_iff S.E S.cfg n.st).1 hcoh.2.2.2.2
  have hdv' : ∀ X ∈ (Member.receipt_process S n.val.st o).T, (Member.receipt_process S n.val.st o).σ X =
      Member.derive_named S.E S.cfg X.toProofNamed :=
    derived_receipt S n.val.st o n.property.2.2.1 n.property.2.2.2 hdv
  have hpc : NoRaise.ParentClosed (Member.receipt_process S n.val.st o).T := by
    have := n'.property.2.2.1
    rw [hst] at this
    exact this
  have hk := keeps_receipt_process S n.val.st o
  have himg : ∀ {Y : Spec.Block V}, Y.toProof ∈ n.val.st.T.image Spec.Block.toProof →
      Y.toProof ∈ (Member.receipt_process S n.val.st o).T.image Spec.Block.toProof :=
    fun h => Finset.image_subset_image hk.2.2.1 h
  have hFJ := roots_receipt S n.val.st o hdv' hpc hF0 hJ0
  refine ⟨⟨⟨coherent_of_derivedView _ _ _ ((derivedView_iff _ _ _).2 ?_), ?_, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
  · intro X hX
    change X ∈ n'.val.st.T at hX
    change n'.val.st.σ X = _
    rw [hst] at hX ⊢
    exact hdv' X hX
  · show n'.val.st.F.toProof ∈ n'.val.st.T.image Spec.Block.toProof
    rw [hst]
    exact hFJ.1
  · show n'.val.st.J.toProof ∈ n'.val.st.T.image Spec.Block.toProof
    rw [hst]
    exact hFJ.2
  · show n'.val.st.live_confirmed.toProof ∈ n'.val.st.T.image Spec.Block.toProof
    rw [hst]
    show (Member.receipt_process S n.val.st o).live_confirmed.toProof ∈ _
    rw [hk.2.2.2.2.2.1]
    exact himg hc1
  · show n'.val.st.latest_confirmed.toProof ∈ n'.val.st.T.image Spec.Block.toProof
    rw [hst]
    show (Member.receipt_process S n.val.st o).latest_confirmed.toProof ∈ _
    rw [hk.2.2.2.2.2.2.1]
    exact himg hc2
  · show n'.val.st.latest_stable.toProof ∈ n'.val.st.T.image Spec.Block.toProof
    rw [hst]
    show (Member.receipt_process S n.val.st o).latest_stable.toProof ∈ _
    rw [hk.2.2.2.2.2.2.2.1]
    exact himg hc3
  · have e : n'.record = n.record := by
      show Member.record n'.val = Member.record n.val
      rw [hval]
      rfl
    rw [e]
    exact hRecord

omit [Fintype V] [Inhabited V] in
/-- `get_fg_root st` is a block of `st.T`, `st.F`, `st.J`, `st.latest_confirmed` or
    `st.latest_stable`. -/
theorem fg_root_mem_union (st : Spec.Store V) :
    Spec.Protocol.get_fg_root st ∈
      st.T ∪ {st.F, st.J, st.latest_confirmed, st.latest_stable} := by
  simp only [Spec.Protocol.get_fg_root, Id.run, pure]
  split_ifs <;> simp

omit [Fintype V] [Inhabited V] in
/-- If `get_sg_root_with C st` answers `A`, then `A` is a block of `st.T`, `st.F`, `st.J`,
    `st.latest_confirmed` or `st.latest_stable`. -/
theorem get_sg_root_with_mem_union {C : Spec.Config} {st : Spec.Store V}
    {A : Spec.Block V} (h : Spec.Protocol.get_sg_root_with C st = .ok A) :
    A ∈ st.T ∪ {st.F, st.J, st.latest_confirmed, st.latest_stable} := by
  unfold Spec.Protocol.get_sg_root_with at h
  obtain ⟨G1, -, h⟩ := dre_bind_ok h
  dsimp only at h
  split at h
  · rename_i hne
    rw [← Except.ok.inj h]
    obtain ⟨X, hX⟩ := Option.ne_none_iff_exists'.mp hne
    simp only [hX, Option.value]
    exact Finset.mem_union_left _ (active_prefix_mem hX)
  · rw [← Except.ok.inj h]
    exact fg_root_mem_union st

omit [Fintype V] [Inhabited V] in
/-- If `round_stable_root st r` answers `G`, then `G` is a block of `st.T`, `st.F`, `st.J`,
    `st.latest_confirmed` or `st.latest_stable`. -/
theorem round_stable_root_mem_union {st : Spec.Store V} {r : Spec.Round}
    {G : Spec.Block V} (h : Spec.Protocol.round_stable_root st r = .ok G) :
    G ∈ st.T ∪ {st.F, st.J, st.latest_confirmed, st.latest_stable} := by
  unfold Spec.Protocol.round_stable_root at h
  obtain ⟨G2, -, h⟩ := dre_bind_ok h
  rw [← Except.ok.inj h]
  simp only [Spec.Protocol.stable_root, Id.run, pure]
  split
  · rename_i hne
    obtain ⟨X, hX⟩ := Option.ne_none_iff_exists'.mp hne
    simp only [hX, Option.value]
    exact Finset.mem_union_left _ (active_prefix_mem hX)
  · exact fg_root_mem_union st

omit [Inhabited V] in
/-- If `update_confirmation C st s` answers `st'`, each of `st'`'s three confirmation records is a
    block of `st.T`, `st.F`, `st.J`, `st.latest_confirmed` or `st.latest_stable`. -/
theorem update_confirmation_mem_union {C : Spec.Config}
    {st st' : Spec.Store V} {s : Spec.Slot}
    (h : Spec.Protocol.update_confirmation C st s = .ok st') :
    st'.live_confirmed ∈ st.T ∪ {st.F, st.J, st.latest_confirmed, st.latest_stable} ∧
      st'.latest_confirmed ∈ st.T ∪ {st.F, st.J, st.latest_confirmed, st.latest_stable} ∧
      st'.latest_stable ∈ st.T ∪ {st.F, st.J, st.latest_confirmed, st.latest_stable} := by
  simp only [Spec.Protocol.update_confirmation] at h
  obtain ⟨_, -, h⟩ := dre_bind_ok h
  obtain ⟨_, -, h⟩ := dre_bind_ok h
  obtain ⟨A, hA, h⟩ := dre_bind_ok h
  obtain ⟨H, hH, h⟩ := dre_bind_ok h
  obtain ⟨He, -, h⟩ := dre_bind_ok h
  obtain ⟨G, hG, h⟩ := dre_bind_ok h
  obtain ⟨S?, hS, h⟩ := dre_bind_ok h
  have hlt : st.latest_confirmed ∈ st.T ∪ {st.F, st.J, st.latest_confirmed, st.latest_stable} := by
    simp
  have hls : st.latest_stable ∈ st.T ∪ {st.F, st.J, st.latest_confirmed, st.latest_stable} := by
    simp
  have hHm : H ∈ st.T ∪ {st.F, st.J, st.latest_confirmed, st.latest_stable} := by
    rcases ghost_mem hH with rfl | hH'
    · exact get_sg_root_with_mem_union hA
    · exact Finset.mem_union_left _ (get_filtered_block_tree_subset st hH')
  have hsm := advance_confirmed_mem hls (round_stable_root_mem_union hG)
  have hroot := fg_root_mem_union st
  split_ifs at h with h1 h2
  · have h' := Except.ok.inj h
    subst h'
    exact ⟨hHm, floor_on_stable_mem hsm (advance_confirmed_mem hlt hHm) hlt, hsm⟩
  · have h' := Except.ok.inj h
    subst h'
    obtain ⟨X, hX⟩ := Option.ne_none_iff_exists'.mp h2
    refine ⟨hroot, floor_on_stable_mem hsm (advance_confirmed_mem hlt ?_) hlt, hsm⟩
    simp only [hX, Option.value]
    exact Finset.mem_union_left _ (confirmation_candidate_mem (hX ▸ hS))
  · have h' := Except.ok.inj h
    subst h'
    exact ⟨hroot, floor_on_stable_mem hsm hlt hlt, hsm⟩

omit [Fintype V] [Inhabited V] in
/-- A block of `T ∪ {F, J, c, s}` has its image in the image of `T` when the four blocks do. -/
theorem image_mem_of_mem_union {T : Finset (Spec.Block V)}
    {F J c s X : Spec.Block V}
    (hF : F.toProof ∈ T.image Spec.Block.toProof)
    (hJ : J.toProof ∈ T.image Spec.Block.toProof)
    (hc : c.toProof ∈ T.image Spec.Block.toProof)
    (hs : s.toProof ∈ T.image Spec.Block.toProof) (hX : X ∈ T ∪ {F, J, c, s}) :
    X.toProof ∈ T.image Spec.Block.toProof := by
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hX
  rcases hX with hX | rfl | rfl | rfl | rfl
  · exact Finset.mem_image_of_mem _ hX
  · exact hF
  · exact hJ
  · exact hc
  · exact hs

/-- The field `confirmation_invariant_tick` of `NodeFacts` at `Model.spec`: if `n`'s named
    store satisfies the confirmation-membership invariant, so does the named store of every outcome
    of `v`'s tick at `t` from `n`. -/
theorem spec_confirmation_invariant_tick :
    ∀ (S : Setup V) (v : V) (n : (Model.spec (V := V)).N) (t : Time)
        (h : Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant (Model.spec (V := V)) S.E S.cfg n.st)
        (out : (Model.spec (V := V)).N × List (NamedObject V)) (hout : (Model.spec (V := V)).tick S v n t ⇢ out),
        Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant (Model.spec (V := V)) S.E S.cfg out.1.st := by
  intro S v n t h out hout
  obtain ⟨⟨hcoh, hF0, hJ0⟩, hc1, hc2, hc3⟩ := h
  have hdv := (derivedView_iff S.E S.cfg n.st).1 hcoh.2.2.2.2
  obtain ⟨sent, hrun, -⟩ := tick_out S v n t out hout
  obtain ⟨st0, st2, st3, st4, st5, sh5, l1, l2, h0, hP1, hP0, hV1, hV0, hC1, hC0, hA1, hA0, hn'⟩ :=
    tick_steps hrun
  have e0 := (update_grades_ok h0).1
  obtain ⟨st1, hst1⟩ : ∃ st1 : Spec.Store V, st1 = { n.val.st with saved_grades := st0.saved_grades, t := t, s := (Setup.toSpec S).C.slotOf t } := ⟨_, rfl⟩
  have hst1' : ({ st0 with t := t, s := (Setup.toSpec S).C.slotOf t } : Spec.Store V) = st1 := by
    rw [hst1, e0]
  have hout' : out.1.val.st = Spec.make_grades_compatible_with_finalized st5 := by rw [hn']
  obtain ⟨gv, tv, rfl⟩ : ∃ gv tv, st3 = { st2 with gf_votes := gv, timestamp_vote := tv } := by
    by_cases hv : condV (Setup.toSpec S).C n.val t
    · rcases hV1 hv with ⟨rfl, -⟩ | ⟨u, rfl, -⟩
      · exact ⟨_, _, rfl⟩
      · exact on_goldfish_vote_checked_frame _ st2 u
    · rw [(hV0 hv).1]; exact ⟨_, _, rfl⟩
  obtain ⟨at', ts, rfl⟩ : ∃ at' ts, st5 = { st4 with attestations := at', timestamp_sg_vote := ts } := by
    by_cases ha : condA (Setup.toSpec S).C n.val t
    · obtain ⟨row, -, rfl, -⟩ := hA1 ha
      exact admit_attestation_frame _ st4 row
    · rw [(hA0 ha).1]; exact ⟨_, _, rfl⟩
  obtain ⟨a, b, c, he4⟩ : ∃ a b c, st4 = { st2 with gf_votes := gv, timestamp_vote := tv, live_confirmed := a, latest_stable := b, latest_confirmed := c } := by
    by_cases hcc : condC (Setup.toSpec S).C n.val t
    · exact ⟨_, _, _, update_confirmation_ok (hC1 hcc)⟩
    · rw [hC0 hcc]; exact ⟨_, _, _, rfl⟩
  have hpc2 : NoRaise.ParentClosed st2.T := by
    have := out.1.property.2.2.1
    rw [hout', he4] at this
    exact this
  have key : (∀ X ∈ st2.T, st2.σ X = Member.derive_named S.E S.cfg X.toProofNamed) ∧
      (st2.F.toProof ∈ st2.T.image Spec.Block.toProof ∧
        st2.J.toProof ∈ st2.T.image Spec.Block.toProof) ∧ Keeps st1 st2 := by
    have hpc1 : NoRaise.ParentClosed st1.T := by rw [hst1]; exact n.property.2.2.1
    have hF1 : st1.F ∈ st1.T := by rw [hst1]; exact n.property.2.2.2
    have hdv1 : ∀ X ∈ st1.T, st1.σ X = Member.derive_named S.E S.cfg X.toProofNamed := by
      rw [hst1]; exact hdv
    have hF1' : st1.F.toProof ∈ st1.T.image Spec.Block.toProof := by rw [hst1]; exact hF0
    have hJ1' : st1.J.toProof ∈ st1.T.image Spec.Block.toProof := by rw [hst1]; exact hJ0
    by_cases hp : condP (Setup.toSpec S).C (Setup.toSpec S).P n.val t
    · obtain ⟨B, hB, -⟩ := hP1 hp
      rw [hst1', on_block_eq_receipt] at hB
      subst hB
      have hd2 := derived_receipt S st1 (.block B.toProofNamed) hpc1 hF1 hdv1
      exact ⟨hd2, roots_receipt S st1 _ hd2 hpc2 hF1' hJ1', keeps_receipt_process S st1 (.block B.toProofNamed)⟩
    · rw [(hP0 hp).1, hst1']
      exact ⟨hdv1, ⟨hF1', hJ1'⟩, Keeps.refl st1⟩
  obtain ⟨hd2, ⟨hF2, hJ2⟩, hk⟩ := key
  have himg : ∀ {Y : Spec.Block V}, Y.toProof ∈ n.val.st.T.image Spec.Block.toProof →
      Y.toProof ∈ st2.T.image Spec.Block.toProof := by
    intro Y hY
    have hs : n.val.st.T ⊆ st2.T := by
      have := hk.2.2.1
      rw [hst1] at this
      exact this
    exact Finset.image_subset_image hs hY
  have hrec : st2.live_confirmed = n.val.st.live_confirmed ∧
      st2.latest_confirmed = n.val.st.latest_confirmed ∧ st2.latest_stable = n.val.st.latest_stable := by
    obtain ⟨-, -, -, -, -, h1, h2, h3, -⟩ := hk
    rw [hst1] at h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have hc4 : st4.live_confirmed.toProof ∈ st2.T.image Spec.Block.toProof ∧
      st4.latest_confirmed.toProof ∈ st2.T.image Spec.Block.toProof ∧
      st4.latest_stable.toProof ∈ st2.T.image Spec.Block.toProof := by
    have hlcf : st2.latest_confirmed.toProof ∈ st2.T.image Spec.Block.toProof := by
      rw [hrec.2.1]; exact himg hc2
    have hls : st2.latest_stable.toProof ∈ st2.T.image Spec.Block.toProof := by
      rw [hrec.2.2]; exact himg hc3
    by_cases hcc : condC (Setup.toSpec S).C n.val t
    · obtain ⟨h1, h2, h3⟩ := update_confirmation_mem_union (hC1 hcc)
      exact ⟨image_mem_of_mem_union hF2 hJ2 hlcf hls h1, image_mem_of_mem_union hF2 hJ2 hlcf hls h2,
        image_mem_of_mem_union hF2 hJ2 hlcf hls h3⟩
    · rw [hC0 hcc]
      refine ⟨?_, hlcf, hls⟩
      show st2.live_confirmed.toProof ∈ _
      rw [hrec.1]; exact himg hc1
  have hT4 : st4.T = st2.T := by rw [he4]
  refine ⟨⟨coherent_of_derivedView _ _ _ ((derivedView_iff _ _ _).2 ?_), ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro X hX
    change X ∈ out.1.val.st.T at hX
    change out.1.val.st.σ X = _
    rw [hout', he4] at hX ⊢
    exact hd2 X hX
  · show out.1.val.st.F.toProof ∈ out.1.val.st.T.image Spec.Block.toProof
    rw [hout', he4]
    exact hF2
  · show out.1.val.st.J.toProof ∈ out.1.val.st.T.image Spec.Block.toProof
    rw [hout', he4]
    exact hJ2
  · show out.1.val.st.live_confirmed.toProof ∈ out.1.val.st.T.image Spec.Block.toProof
    rw [hout']
    show st4.live_confirmed.toProof ∈ st4.T.image Spec.Block.toProof
    rw [hT4]; exact hc4.1
  · show out.1.val.st.latest_confirmed.toProof ∈ out.1.val.st.T.image Spec.Block.toProof
    rw [hout']
    show st4.latest_confirmed.toProof ∈ st4.T.image Spec.Block.toProof
    rw [hT4]; exact hc4.2.1
  · show out.1.val.st.latest_stable.toProof ∈ out.1.val.st.T.image Spec.Block.toProof
    rw [hout']
    show st4.latest_stable.toProof ∈ st4.T.image Spec.Block.toProof
    rw [hT4]; exact hc4.2.2

/-! ## The vote the tick sends is pooled -/

omit [Inhabited V] in
/-- The checked vote admission lists a vote whose signer is in its slot's committee, whose slot is
    neither after the store's slot nor before it less one, and whose signer does not equivocate in
    its slot's pool. -/
theorem mem_on_goldfish_vote_checked (P : Spec.Provisional V)
    (st : Spec.Store V) (u : Spec.GoldfishVote V)
    (hc : u.val_index ∈ P.committee u.slot) (h1 : ¬ st.s < u.slot) (h2 : ¬ u.slot < st.s - 1)
    (he : Spec.Protocol.equivocates (st.pool u.slot) u.val_index = false) :
    u ∈ (Spec.Protocol.on_goldfish_vote_checked P st u).gf_votes u.slot := by
  unfold Spec.Protocol.on_goldfish_vote_checked Spec.Protocol.on_goldfish_vote
  have d1 : decide (u.slot < st.s - 1) = false := decide_eq_false h2
  have d2 : decide (st.s < u.slot) = false := decide_eq_false h1
  by_cases hm : u ∈ st.gf_votes u.slot
  · simp only [Id.run, pure, StoreSteps.getElem_fn, d1, d2, hm, hc, Bool.false_or,
      decide_true, if_true, not_true_eq_false, if_false]
  · simp only [Id.run, pure, StoreSteps.getElem_fn, d1, d2, hm, hc, he, Bool.false_or,
      decide_false, not_true_eq_false, if_false, Bool.false_eq_true]
    simp

omit [DecidableEq V] [Fintype V] [Inhabited V] in
/-- Slot `s`'s vote time is in slot `s`. -/
theorem slotOf_vote_time (C : Spec.Config) (s : Spec.Slot) :
    C.slotOf (C.vote_time s) = s := by
  have hΔ := C.Δ_pos
  apply slotOf_of_bounds
  · simp only [Spec.Config.vote_time, Spec.Config.proposal_time]
    nlinarith
  · simp only [Spec.Config.vote_time, Spec.Config.proposal_time]
    nlinarith

/-- The field `tick_vote_pooled` of `NodeFacts` at `Model.spec`: if an outcome of `v`'s tick at
    slot `s`'s vote time from `n`, `s > 0`, sends the slot-`s` vote `u`, `n`'s pool is well stamped,
    `n`'s clock is at most the vote time, and `u`'s sender does not equivocate in `n`'s slot-`s`
    pool, then `u` is in the outcome's slot-`s` list with a stamp at most the vote time. -/
theorem spec_tick_vote_pooled :
    ∀ (S : Setup V) (v : V) (n : (Model.spec (V := V)).N) (s : Slot) (u : GoldfishVote V)
      (out : (Model.spec (V := V)).N × List (NamedObject V)),
      (Model.spec (V := V)).tick S v n ((Model.spec (V := V)).vote_time S.E s) ⇢ out →
      0 < s → NamedObject.gfVote u ∈ out.2 → u.slot = s →
      (∀ (k : Slot) (x : GoldfishVote V), x ∈ n.st.core.gf_votes k → x.slot = k) →
      (∀ (k : Slot) (x : GoldfishVote V), x ∈ n.st.core.gf_votes k →
        (n.st.core.timestamp_vote x).isSome = true) →
      (∀ x : GoldfishVote V, (n.st.core.timestamp_vote x).isSome = true →
        x ∈ n.st.core.gf_votes x.slot) →
      (∀ (x : GoldfishVote V) (c : Stamp), n.st.core.timestamp_vote x = some c →
        c ≤ (n.st.core.t : Stamp)) →
      n.st.core.t ≤ (Model.spec (V := V)).vote_time S.E s →
      (Model.spec (V := V)).equivocates ((Model.spec (V := V)).store_pool n.st.core s)
        u.val_index = false →
      u ∈ out.1.st.core.gf_votes s ∧
        ∃ c : Stamp, out.1.st.core.timestamp_vote u = some c ∧
          c ≤ ((Model.spec (V := V)).vote_time S.E s : Stamp) := by
  intro S v n s u out hout _ hu hus p1 p2 p3 p4 ht heq
  set C := (Setup.toSpec S).C
  set t := (Model.spec (V := V)).vote_time S.E s
  have htC : t = C.vote_time s := rfl
  have hst : C.slotOf t = s := by rw [htC]; exact slotOf_vote_time C s
  obtain ⟨sent, hrun, hsent⟩ := tick_out S v n t out hout
  rw [hsent] at hu
  obtain ⟨o, ho, hou⟩ := List.mem_map.mp hu
  obtain ⟨st0, st2, st3, st4, st5, sh5, l1, l2, h0, -, hP0, hV1, -, hC1, hC0, hA1, hA0, hn'⟩ :=
    tick_steps hrun
  have hP : ¬ condP C (Setup.toSpec S).P n.val t := by
    rintro ⟨-, hc⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    have h1 := hc.1.1
    rw [hst, htC] at h1
    have hΔ := C.Δ_pos
    simp only [Spec.Config.vote_time] at h1
    linarith
  obtain ⟨hst2, hl1⟩ := hP0 hP
  have e0 := (update_grades_ok h0).1
  have hsent2 : o ∈ l2 := by
    by_cases ha : condA C n.val t
    · obtain ⟨row, -, -, hs⟩ := hA1 ha
      rw [hs] at ho
      rcases List.mem_append.mp ho with h | h
      · exact h
      · rw [List.mem_singleton] at h; subst h
        simp only [Spec.NamedObject.toProof, reduceCtorEq] at hou
    · rw [(hA0 ha).2.2] at ho; exact ho
  rcases tick_sent hrun ho with ⟨B, rfl, -⟩ | ⟨u', rfl, hcV⟩ | ⟨row, rfl, -⟩
  · simp only [Spec.NamedObject.toProof, reduceCtorEq] at hou
  swap
  · simp only [Spec.NamedObject.toProof, reduceCtorEq] at hou
  simp only [Spec.NamedObject.toProof, NamedObject.gfVote.injEq] at hou
  subst hou
  rcases hV1 hcV with ⟨-, hl2⟩ | ⟨w, hst3, hl2, hcom, hslot⟩
  · rw [hl2, hl1] at hsent2; exact absurd hsent2 List.not_mem_nil
  rw [hl2, hl1, List.nil_append, List.mem_singleton,
    Spec.NamedObject.gfVote.injEq] at hsent2
  subst hsent2
  have hs2 : st2.s = s := by rw [hst2]; exact hst
  have hu2 : u'.slot = s := by rw [hslot, hs2]
  have hpool : st2.pool s = n.val.st.pool s := by rw [hst2, e0]; rfl
  have hm3 : u' ∈ st3.gf_votes u'.slot := by
    rw [hst3]
    refine mem_on_goldfish_vote_checked (Setup.toSpec S).P st2 u' hcom
      (by rw [hs2, hu2]; exact lt_irrefl s) (by rw [hs2, hu2]; exact Nat.not_lt.mpr (Nat.sub_le s 1)) ?_
    rw [hu2, hpool]
    have : ((n.val.st.pool s).map Spec.GoldfishVote.toProofEmb).map
        ChainStateToHandlers.goldfishVoteToSpecEmb = n.val.st.pool s := by
      rw [Finset.map_map]
      have e : (Spec.GoldfishVote.toProofEmb (V := V)).trans
          (ChainStateToHandlers.goldfishVoteToSpecEmb (V := V)) = Function.Embedding.refl _ := by
        ext x; rfl
      rw [e, Finset.map_refl]
    have h := heq
    change Spec.Protocol.equivocates
      (((n.val.st.pool s).map Spec.GoldfishVote.toProofEmb).map
        ChainStateToHandlers.goldfishVoteToSpecEmb) u'.val_index = false at h
    rwa [this] at h
  have hd0 : DPool st2 := by
    obtain ⟨d1, d2, d3, d4⟩ := dpool_of_poolStamps n.st.core ⟨p1, p2, p3, p4⟩
    rw [hst2, e0]
    refine ⟨d1, d2, d3, fun x c hx => le_trans (d4 x c hx) ?_⟩
    show ((n.val.st.t : Int) : Stamp) ≤ ((t : Int) : Stamp)
    exact_mod_cast ht
  have hd3 : DPool st3 := by rw [hst3]; exact ((vIns_checked _ st2 u').2.2 hd0).1
  have k4 : VIns (Setup.toSpec S).P st3 st4 := by
    by_cases hcc : condC C n.val t
    · rw [update_confirmation_ok (hC1 hcc)]; exact VIns.of_eq rfl rfl rfl rfl
    · rw [hC0 hcc]; exact VIns.of_eq rfl rfl rfl rfl
  have k5 : VIns (Setup.toSpec S).P st4 st5 := by
    by_cases ha : condA C n.val t
    · obtain ⟨row, -, rfl, -⟩ := hA1 ha
      obtain ⟨x, y, e⟩ := StoreSteps.admit_attestation_writes C st4 row
      rw [e]; exact VIns.of_eq rfl rfl rfl rfl
    · rw [(hA0 ha).1]; exact VIns.of_eq rfl rfl rfl rfl
  have k : VIns (Setup.toSpec S).P st3 out.1.val.st := by
    rw [hn']; exact k4.trans (k5.trans (VIns.of_eq rfl rfl rfl rfl))
  obtain ⟨-, m, c, -⟩ := k.2.2 hd3
  obtain ⟨-, q2, -, q4⟩ := hd3
  obtain ⟨c0, hc0⟩ := Option.isSome_iff_exists.mp (q2 _ _ hm3)
  have ht3 : st3.t = t := by
    rw [hst3]
    rw [(vIns_checked _ st2 u').1, hst2]
  refine ⟨?_, c0, c _ _ hc0, ?_⟩
  · rw [← hu2]
    exact (mem_map_toProof_iff _ _).2 (m _ _ hm3)
  · have := q4 _ _ hc0
    rw [ht3] at this
    exact this

/-! ## The four clauses of `SgMono` through the named images -/

/-- The record's `SgRefused` at a store of the subtype is `SgRefused` at the store's named image. -/
theorem sgRefused_iff (hc : Protocol.HealConfig) (c : (Model.spec (V := V)).S)
    (b : CombinedAttestation V) :
    Restated.SgRefused (Model.spec (V := V)) hc c b ↔
      DecoupledConsensusModel.Sts.SgRefused hc c.val.toProof b := by
  unfold Restated.SgRefused DecoupledConsensusModel.Sts.SgRefused
  show b.round < Member.round_of hc c.val.s - hc.η_SG ∨ b.confirmed ∈ Member.round_votes c.val b ∨
    (Member.round_votes c.val b).card = 2 ↔ _
  rw [HandlersFacts.image_round_votes, HandlersFacts.image_round_of]
  rfl

/-- `SgMono` between the named images of two stores of the subtype gives the record's `SgMono`
    between the stores. -/
theorem sgMono_of_image (hc : Protocol.HealConfig) (st st' : (Model.spec (V := V)).NS)
    (h : DecoupledConsensusModel.Sts.SgMono hc st.val.toProofNamed st'.val.toProofNamed) :
    Restated.SgMono (Model.spec (V := V)) hc st st' := by
  refine ⟨fun b hb => (sgRefused_iff hc st' b).2 (h.refused b ((sgRefused_iff hc st b).1 hb)),
    fun a ha => h.rows a ha, fun a ha hr => h.excluded a ha ((sgRefused_iff hc st _).1 hr),
    fun hs B hB a ha => ?_⟩
  have hs' : DecoupledConsensusModel.Sts.IncludedAttestationsSettled hc st.val.toProofNamed :=
    fun B hB a ha => (hs B hB a ha).imp id (sgRefused_iff hc st _).1
  exact (h.settled hs' B hB a ha).imp id (sgRefused_iff hc st' _).2

omit [Fintype V] [Inhabited V] in
/-- A spec step that keeps the tree and the attestations and does not move the slot back gives
    `SgMono` between the named images. -/
theorem sgI_frame (hc : Protocol.HealConfig) {X Y : Spec.Store V} (hT : Y.T = X.T)
    (ha : Y.attestations = X.attestations) (hs : X.s ≤ Y.s) :
    DecoupledConsensusModel.Sts.SgMono hc X.toProofNamed Y.toProofNamed :=
  DecoupledConsensusModel.Sts.sgMono_of_frame hc
    (by simp only [Spec.Store.toProofNamed, ha])
    (by simp only [Spec.Store.toProofNamed, hT])
    (by simp only [Spec.Store.toProofNamed, Spec.Store.toProof, ha]) hs

omit [Inhabited V] in
/-- The spec's attestation admission gives `SgMono` between the named images. -/
theorem sgI_admit (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig)
    (X : Spec.Store V) (row : Spec.Attestation V) :
    DecoupledConsensusModel.Sts.SgMono hc X.toProofNamed
      (Spec.Protocol.admit_attestation (Spec.Config.toSpec E hc cfg) X
        row).toProofNamed := by
  rw [← toProof_admit_row E hc cfg]
  exact DecoupledConsensusModel.Sts.sgMono_admit_row hc _ _

/-- The spec's block receipt gives `SgMono` between the named images. -/
theorem sgI_on_block (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig)
    (P : Spec.Provisional V) (X : Spec.Store V) (B : Spec.Block V) :
    DecoupledConsensusModel.Sts.SgMono hc X.toProofNamed
      (Spec.Protocol.on_block (Spec.Config.toSpec E hc cfg) P X
        B).toProofNamed := by
  rw [Handlers.on_block_eq]
  split_ifs with hadm
  swap
  · exact DecoupledConsensusModel.Sts.SgMono.refl hc _
  obtain ⟨-, hYs, hYa, -⟩ := HandlersFacts.admitBlockCore_fields
    (Spec.Config.toSpec E hc cfg) P X B
  have hYT : (Handlers.admitBlockCore (Spec.Config.toSpec E hc cfg) P X B).T =
      X.T ∪ {B} := by
    unfold Handlers.admitBlockCore
    rw [if_pos hadm, SubtypeEqualities.blockCore_T]
  set Y := Handlers.admitBlockCore (Spec.Config.toSpec E hc cfg) P X B
  rw [← toProof_admit_rows E hc cfg]
  have href : ∀ b, DecoupledConsensusModel.Sts.SgRefused hc X.toProof b →
      DecoupledConsensusModel.Sts.SgRefused hc Y.toProof b := fun b h =>
    DecoupledConsensusModel.Sts.sgRefused_of_frame hc b
      (by simp only [Spec.Store.toProof, hYa]) (le_of_eq hYs.symm) h
  have hrows : Y.toProofNamed.sg_rows = X.toProofNamed.sg_rows := by
    simp only [Spec.Store.toProofNamed, hYa]
  have hm2 := DecoupledConsensusModel.Sts.sgMono_admit_rows hc
    (B.attestations.map Spec.Attestation.toProofNamed) Y.toProofNamed
  obtain ⟨-, hatt, hslot, -⟩ := (SubtypeEqualities.block_admissible_iff _ _ _ _).mp hadm
  have hnf : ∀ a ∈ B.attestations.map Spec.Attestation.toProofNamed,
      a.round ≤ hc.round_of Y.toProofNamed.core.s := by
    intro a ha
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp ha
    have h1 := List.all_eq_true.mp hatt row hrow
    simp only [decide_eq_true_eq] at h1
    rw [Spec.Attestation.toProofNamed_round]
    refine le_trans h1 ?_
    unfold Spec.Config.round_of DecoupledConsensusModel.Protocol.HealConfig.round_of
    exact Nat.div_le_div_right (le_trans (Nat.le_of_not_lt hslot) (le_of_eq hYs.symm))
  refine ⟨fun b h => hm2.refused b (href b h), fun a h => hm2.rows a (by rw [hrows]; exact h),
    fun a h0 hr => hm2.excluded a (by rw [hrows]; exact h0) (href _ hr), fun h C hC a ha => ?_⟩
  rw [DecoupledConsensusModel.Sts.admit_rows_bodies] at hC
  change C ∈ Y.T.map Spec.Block.toProofNamedEmb at hC
  rw [hYT] at hC
  obtain ⟨Z, hZ, rfl⟩ := Finset.mem_map.mp hC
  rcases Finset.mem_union.mp hZ with hZ | hZ
  · rcases h _ (Finset.mem_map_of_mem _ hZ) a ha with h' | h'
    · exact Or.inl (hm2.rows a (by rw [hrows]; exact h'))
    · exact Or.inr (hm2.refused _ (href _ h'))
  · rw [Finset.mem_singleton.mp hZ] at ha
    refine DecoupledConsensusModel.Sts.admit_rows_settles hc _ Y.toProofNamed hnf a ?_
    simpa using ha

/-- The field `sgMono_process` of `NodeFacts` at `Model.spec`: the four clauses of `SgMono`
    hold from `st` to the store the receipt of `o` returns on `st`. -/
theorem spec_sgMono_process :
    ∀ (S : Setup V) (st : (Model.spec (V := V)).NS) (o : NamedObject V),
      Restated.SgMono (Model.spec (V := V)) S.hc st
        ((Model.spec (V := V)).receipt_process S st o) := by
  intro S st o
  by_cases hheld : objectRootHeldByOther st.val.T o
  · have e : (Model.spec (V := V)).receipt_process S st o = st :=
      OkMember.receipt_process_of_held hheld
    rw [e]
    exact sgMono_of_image _ _ _ (DecoupledConsensusModel.Sts.SgMono.refl _ _)
  apply sgMono_of_image
  show DecoupledConsensusModel.Sts.SgMono _ _ (OkMember.receipt_process S st o).val.toProofNamed
  rw [OkMember.receipt_process_val_of_not_held (S := S) hheld]
  cases o with
  | block B => exact sgI_on_block S.E S.hc S.cfg _ _ _
  | gfVote u =>
    obtain ⟨gv, tv, e⟩ := receipt_gfVote_frame S st.val u
    rw [e]; exact sgI_frame _ rfl rfl le_rfl
  | attest a => exact sgI_admit S.E S.hc S.cfg _ _

/-- The field `sgMono_node_tick` of `NodeFacts` at `Model.spec`: if the slot of `n`'s store is
    at most the slot of `t`, the four clauses of `SgMono` hold from `n`'s store to the store of
    every outcome of `v`'s tick at `t` from `n`. -/
theorem spec_sgMono_node_tick :
    ∀ (S : Setup V) (v : V) (n : (Model.spec (V := V)).N) (t : Int),
      n.st.core.s ≤ S.E.slotOf t → ∀ (out : (Model.spec (V := V)).N × List (NamedObject V)),
      (Model.spec (V := V)).tick S v n t ⇢ out →
        Restated.SgMono (Model.spec (V := V)) S.hc n.st out.1.st := by
  intro S v n t hs out hout
  apply sgMono_of_image
  show DecoupledConsensusModel.Sts.SgMono _ n.val.st.toProofNamed out.1.val.st.toProofNamed
  obtain ⟨sent, hrun, -⟩ := tick_out S v n t out hout
  obtain ⟨st0, st2, st3, st4, st5, sh5, l1, l2, h0, hP1, hP0, hV1, hV0, hC1, hC0, hA1, hA0, hn'⟩ :=
    tick_steps hrun
  have e0 := (update_grades_ok h0).1
  have k0 : DecoupledConsensusModel.Sts.SgMono S.hc n.val.st.toProofNamed
      ({ st0 with t := t, s := (Setup.toSpec S).C.slotOf t } : Spec.Store V).toProofNamed :=
    sgI_frame _ (by rw [e0]) (by rw [e0]) (by rw [slotOf_eq]; exact hs)
  have k2 : DecoupledConsensusModel.Sts.SgMono S.hc
      ({ st0 with t := t, s := (Setup.toSpec S).C.slotOf t } : Spec.Store V).toProofNamed
      st2.toProofNamed := by
    by_cases hc : condP (Setup.toSpec S).C (Setup.toSpec S).P n.val t
    · obtain ⟨B, rfl, -⟩ := hP1 hc
      exact sgI_on_block S.E S.hc S.cfg _ _ _
    · rw [(hP0 hc).1]; exact DecoupledConsensusModel.Sts.SgMono.refl _ _
  have k3 : DecoupledConsensusModel.Sts.SgMono S.hc st2.toProofNamed st3.toProofNamed := by
    by_cases hv : condV (Setup.toSpec S).C n.val t
    · rcases hV1 hv with ⟨rfl, -⟩ | ⟨u, rfl, -, -⟩
      · exact DecoupledConsensusModel.Sts.SgMono.refl _ _
      · rcases on_goldfish_vote_checked_cases (Setup.toSpec S).P st2 u with e | ⟨-, -, -, e⟩ <;>
          rw [e] <;> exact sgI_frame _ rfl rfl le_rfl
    · rw [(hV0 hv).1]; exact DecoupledConsensusModel.Sts.SgMono.refl _ _
  have k4 : DecoupledConsensusModel.Sts.SgMono S.hc st3.toProofNamed st4.toProofNamed := by
    by_cases hcc : condC (Setup.toSpec S).C n.val t
    · rw [update_confirmation_ok (hC1 hcc)]; exact sgI_frame _ rfl rfl le_rfl
    · rw [hC0 hcc]; exact DecoupledConsensusModel.Sts.SgMono.refl _ _
  have k5 : DecoupledConsensusModel.Sts.SgMono S.hc st4.toProofNamed st5.toProofNamed := by
    by_cases ha : condA (Setup.toSpec S).C n.val t
    · obtain ⟨row, -, rfl, -⟩ := hA1 ha
      exact sgI_admit S.E S.hc S.cfg _ _
    · rw [(hA0 ha).1]; exact DecoupledConsensusModel.Sts.SgMono.refl _ _
  rw [hn']
  exact k0.trans (k2.trans (k3.trans (k4.trans (k5.trans (sgI_frame _ rfl rfl le_rfl)))))

/-! ## The head the round action reads -/

/-- The field `round_action_head_mem_gradeContract` of `NodeFacts` at `Model.spec`: the height
    of the finality pair a round action signs is the justified height of a block of the store's
    tree. -/
theorem spec_round_action_head_mem_gradeContract : ∀ (c : (Model.spec (V := V)).Cache) (E : Env V) (hc : Protocol.HealConfig)
    (nd : Protocol.Node V) (st : (Model.spec (V := V)).S) (record : (Model.spec (V := V)).NR) (hJ : st.J ∈ st.T) (hF : st.F ∈ st.T)
    {h : Height} {T : BlockId}
    (out : (Model.spec (V := V)).NR × NamedAttestation V)
    (hout : (Model.spec (V := V)).round_action_with ((Model.spec (V := V)).gradeContract c) E hc nd st.toHealing record ⇢ out)
    (hp : out.2.finality_pair
      = some ⟨h, T⟩), ∃ Hd ∈ st.T, (st.σ Hd).h_j = h := by
  intro c E hc nd st record hJ hF h T out hout hp
  have hout' : Returns (Member.round_action_with ((Model.spec (V := V)).gradeContract c) E hc nd
      st.val record) out := hout
  obtain ⟨p, hp', rfl⟩ := ContractImages.round_action_with_shape hout'
  obtain ⟨i, hi, -, -, rfl⟩ := ContractImages.build_attestation_shape hp'
  unfold Spec.Protocol.attestation_input at hi
  obtain ⟨A_G2, -, hi⟩ := NoRaise.DRE.of_bind_ok hi
  obtain ⟨⟨fields, h_j, J, h_F⟩, hf, hi⟩ := NoRaise.DRE.of_bind_ok hi
  obtain ⟨W, -, hi⟩ := NoRaise.DRE.of_bind_ok hi
  cases Except.ok.inj hi
  obtain ⟨S, H', -, hH', e⟩ := ContractImages.get_fg_vote_with_parts hf
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl, rfl⟩ := e
  rw [(ContractImages.contractStore_fields st.val _ _).1, ContractImages.contractStore_pool] at hH'
  have hmem := ContractImages.get_head_with_contractStore_mem st _ _ hJ hH'
  have hh : (st.val.σ H').h_j = h := by
    have hp2 : (Spec.Protocol.finality_pair record (st.val.σ H').h_j
        (st.val.σ H').J.root (st.val.σ H').h_F).map Spec.FinalityPair.toProof =
          some ⟨h, T⟩ := hp
    unfold Spec.Protocol.finality_pair at hp2
    simp only [Id.run, pure] at hp2
    split_ifs at hp2 <;> simp_all [Spec.FinalityPair.toProof]
  refine ⟨H'.toProof, Finset.mem_image_of_mem _ hmem, ?_⟩
  show (st.val.σ (st.val.blockOfImage H'.toProof)).toProof.h_j = h
  rw [Spec.Store.blockOfImage_toProof_of_injOn st.val st.property.2.1.injOn_toProof hmem]
  simpa [Spec.Protocol.ChainState.toProof] using hh

end SpecRecord.NodeFacts


namespace SpecRecord.NodeRunFacts

open DecoupledConsensusModel DecoupledConsensusModel.Execution DecoupledConsensusModel.Sts
open DecoupledConsensusModel.Sts.Record
open SpecRecord.NodeFacts
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-! ## Fields of `NodeRunFacts` read off the tick and the receipt -/

/-- The field `treeSlotStep_tick` of `NodeRunFacts` at `Model.spec`: if the slot of `n`'s core
    store is at most the slot of `t` and every block of `n`'s core tree is of a slot at most the
    store's, the same holds of every outcome of `v`'s tick at `t` from `n`. -/
theorem spec_treeSlotStep_tick :
    ∀ (S : Setup V) (v : V) (n : (Model.spec (V := V)).N) (t : Int)
        (out : (Model.spec (V := V)).N × List (NamedObject V)), (Model.spec (V := V)).tick S v n t ⇢ out → n.st.core.s ≤ S.E.slotOf t →
        (∀ B : Block V, B ∈ n.st.core.T → B.slot ≤ n.st.core.s) →
        (∀ B : Block V, B ∈ out.1.st.core.T → B.slot ≤ out.1.st.core.s) := by
  intro S v n t out hout hs hT B hB
  have hB' : B ∈ out.1.val.st.T.image Spec.Block.toProof := hB
  obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hB'
  show X.toProof.slot ≤ out.1.val.st.s
  rw [SubtypeEqualities.toProof_slot]
  have hold : ∀ Y ∈ n.val.st.T, Y.slot ≤ n.val.st.s := fun Y hY => by
    have := hT Y.toProof (Finset.mem_image_of_mem _ hY)
    rwa [SubtypeEqualities.toProof_slot] at this
  have hs' : n.val.st.s ≤ (Setup.toSpec S).C.slotOf t := by rw [slotOf_eq]; exact hs
  obtain ⟨sg, ⟨he, -⟩ | ⟨B0, -, he⟩⟩ := tick_shape S v n t out hout
  · rw [he.1] at hX
    rw [he.2.2.2.2.2.2.2.2]
    exact le_trans (hold X hX) hs'
  · rw [he.2.2.2.2.2.2.2.2, (keeps_receipt_process S _ _).2.1]
    rw [he.1] at hX
    rcases SubtypeEqualities.receipt_cases S _ (.block B0) with ⟨hT', -⟩ | ⟨B1, -, hadm, hT', -⟩
    · rw [hT'] at hX; exact le_trans (hold X hX) hs'
    · rw [hT'] at hX
      rcases Finset.mem_union.mp hX with hX | hX
      · exact le_trans (hold X hX) hs'
      · rw [Finset.mem_singleton.mp hX]
        obtain ⟨-, -, hsl, -⟩ := (SubtypeEqualities.block_admissible_iff _ _ _ _).mp hadm
        exact not_lt.mp hsl

/-- The field `treeSlotStep_process` of `NodeRunFacts` at `Model.spec`: if every block of `n`'s
    core tree is of a slot at most the slot of `n`'s core store, the same holds of every node state
    `n`'s receipt of `o` returns. -/
theorem spec_treeSlotStep_process :
    ∀ (S : Setup V) (n : (Model.spec (V := V)).N) (o : NamedObject V) (n' : (Model.spec (V := V)).N), (Model.spec (V := V)).process S n o ⇢ n' →
        (∀ B : Block V, B ∈ n.st.core.T → B.slot ≤ n.st.core.s) →
        (∀ B : Block V, B ∈ n'.st.core.T → B.slot ≤ n'.st.core.s) := by
  intro S n o n' hn' hT B hB
  have hB' : B ∈ n'.val.st.T.image Spec.Block.toProof := hB
  obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hB'
  show X.toProof.slot ≤ n'.val.st.s
  rw [SubtypeEqualities.toProof_slot]
  have hold : ∀ Y ∈ n.val.st.T, Y.slot ≤ n.val.st.s := fun Y hY => by
    have := hT Y.toProof (Finset.mem_image_of_mem _ hY)
    rwa [SubtypeEqualities.toProof_slot] at this
  rw [process_val_st S n o n' hn', mgc_eq] at hX ⊢
  change X ∈ (Member.receipt_process S n.val.st o).T at hX
  change X.slot ≤ (Member.receipt_process S n.val.st o).s
  rw [(keeps_receipt_process S _ o).2.1]
  rcases SubtypeEqualities.receipt_cases S n.val.st o with ⟨hT', -⟩ | ⟨B1, -, hadm, hT', -⟩
  · rw [hT'] at hX; exact hold X hX
  · rw [hT'] at hX
    rcases Finset.mem_union.mp hX with hX | hX
    · exact hold X hX
    · rw [Finset.mem_singleton.mp hX]
      obtain ⟨-, -, hsl, -⟩ := (SubtypeEqualities.block_admissible_iff _ _ _ _).mp hadm
      exact not_lt.mp hsl

/-- The field `poolStep_process` of `NodeRunFacts` at `Model.spec`: the step from `n`'s core
    store to the core store of every node state `n`'s receipt of `o` returns is a `PoolStep`. -/
theorem spec_poolStep_process :
    ∀ (S : Setup V) (n : (Model.spec (V := V)).N) (o : NamedObject V) (n' : (Model.spec (V := V)).N),
        (Model.spec (V := V)).process S n o ⇢ n' → Restated.Vocabulary.Protocol.PoolStep (Model.spec (V := V)) n.st.core n'.st.core := by
  intro S n o n' hn'
  have hv : VIns (Spec.Provisional.toSpec S.E) n.val.st n'.val.st := by
    rw [process_val_st S n o n' hn']
    exact (vIns_receipt S n.val.st o).trans (VIns.of_eq rfl rfl rfl rfl)
  have hp := poolStep_of_vIns (a := n.st.core) (b := n'.st.core) hv
  exact hp.1

/-- The field `voteInsertStep_process` of `NodeRunFacts` at `Model.spec`: the step from `n`'s
    core store to that of a node state `n`'s receipt of `o` returns is a `PoolStep`, and every
    Goldfish vote it newly pools is stamped with the clock of `n`'s core store and of a slot at most
    that store's slot. -/
theorem spec_voteInsertStep_process :
    ∀ (S : Setup V) (n : (Model.spec (V := V)).N) (o : NamedObject V) (n' : (Model.spec (V := V)).N),
        (Model.spec (V := V)).process S n o ⇢ n' →
          Restated.Vocabulary.Protocol.VoteInsertStep (Model.spec (V := V)) n.st.core.t n.st.core.s n.st.core n'.st.core := by
  intro S n o n' hn'
  have hv : VIns (Spec.Provisional.toSpec S.E) n.val.st n'.val.st := by
    rw [process_val_st S n o n' hn']
    exact (vIns_receipt S n.val.st o).trans (VIns.of_eq rfl rfl rfl rfl)
  have hp := poolStep_of_vIns (a := n.st.core) (b := n'.st.core) hv
  exact ⟨hp.1, fun hps u hu hu' => (hp.2 hps u hu hu').1,
    fun hps u hu hu' => not_lt.mpr (hp.2 hps u hu hu').2.1⟩

/-- The field `insertsAt_process` of `NodeRunFacts` at `Model.spec`: the arrow `InsertsAt` at
    the clock of `n`'s core store runs from that core store to the core store of every node state
    `n`'s receipt of `o` returns. -/
theorem spec_insertsAt_process :
    ∀ (S : Setup V) (n : (Model.spec (V := V)).N) (o : NamedObject V) (n' : (Model.spec (V := V)).N),
        (Model.spec (V := V)).process S n o ⇢ n' → Restated.InsertsAt (Model.spec (V := V)) S.E n.st.core.t n.st.core n'.st.core := by
  intro S n o n' hn'
  have hv : VIns (Spec.Provisional.toSpec S.E) n.val.st n'.val.st := by
    rw [process_val_st S n o n' hn']
    exact (vIns_receipt S n.val.st o).trans (VIns.of_eq rfl rfl rfl rfl)
  have hp := poolStep_of_vIns (a := n.st.core) (b := n'.st.core) hv
  intro hps hc
  obtain ⟨hcar, hsta⟩ := hp.1 hps
  refine ⟨hcar, hsta, ?_, hv.2.1, fun u hu hu' => ?_⟩
  · show n'.val.st.t = _
    rw [hv.1]; exact hc
  · obtain ⟨e, hs, hcm⟩ := hp.2 hps u hu hu'
    refine ⟨?_, hs, ?_⟩
    · rw [e, ← hc]
    · simpa [Spec.Provisional.toSpec_committee] using hcm

/-- The field `voteInsertStep_onTickEmit` of `NodeRunFacts` at `Model.spec`: if the clock of
    `n`'s core store is at most `t`, the step from `n`'s core store to that of an outcome of `v`'s
    tick at `t` from `n` is a `PoolStep`, and every Goldfish vote it newly pools is stamped `t` and
    of a slot at most the slot of `t`. -/
theorem spec_voteInsertStep_onTickEmit :
    ∀ (S : Setup V) (v : V) (n : (Model.spec (V := V)).N) (t : Time)
        (out : (Model.spec (V := V)).N × List (NamedObject V)), (Model.spec (V := V)).tick S v n t ⇢ out → n.st.core.t ≤ t →
          Restated.Vocabulary.Protocol.VoteInsertStep (Model.spec (V := V)) t (S.E.slotOf t) n.st.core out.1.st.core := by
  intro S v n t out hout hle
  obtain ⟨sent, hrun, -⟩ := tick_out S v n t out hout
  obtain ⟨sg, -, -, hk⟩ := tick_vIns hrun
  have hd1 : DPool n.val.st → DPool { n.val.st with saved_grades := sg, t := t, s := (Setup.toSpec S).C.slotOf t } := by
    rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, h3, fun x c hx => le_trans (h4 x c hx) ?_⟩
    show ((n.val.st.t : Int) : Stamp) ≤ ((t : Int) : Stamp)
    exact_mod_cast hle
  refine ⟨fun hps => ?_, fun hps u hu hu' => ?_, fun hps u hu hu' => ?_⟩
  · obtain ⟨pd, m, c, -⟩ := hk (hd1 (dpool_of_poolStamps _ hps))
    exact ⟨⟨fun k u hu => (mem_map_toProof_iff _ _).2 (m k _ ((mem_map_toProof_iff _ _).1 hu)),
      fun u c' hu => c _ c' hu⟩, poolStamps_of_dpool _ pd⟩
  · obtain ⟨-, -, -, nw⟩ := hk (hd1 (dpool_of_poolStamps _ hps))
    exact (nw _ (fun h' => hu ((mem_map_toProof_iff _ _).2 h')) ((mem_map_toProof_iff _ _).1 hu')).1
  · obtain ⟨-, -, -, nw⟩ := hk (hd1 (dpool_of_poolStamps _ hps))
    have hs := (nw _ (fun h' => hu ((mem_map_toProof_iff _ _).2 h')) ((mem_map_toProof_iff _ _).1 hu')).2.1
    rw [slotOf_eq] at hs
    exact not_lt.mpr hs

end SpecRecord.NodeRunFacts
