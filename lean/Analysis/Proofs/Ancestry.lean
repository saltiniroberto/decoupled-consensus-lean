import Analysis.Proofs.SlotClosure

/-!
# Ancestry and the height inequalities

Lemma 4 (`lem:finalized-before-justified`, `height_filter_healing.tex:920-931`): the finalized
block precedes the justified block, which precedes the latest block, and the finalized height is
at most the justified height, which is below the state height.

The paper's own proof of Lemma 4 (`lem:finalized-before-justified`, lines 920–931), at
lines 933–943, calls these "ancestry and height inequalities", which is what names this
file. It holds three parts:

* the basic facts about `⪯`, which Definition 5 (`def:block-chain`) defines but nothing had yet
  proved anything about: reflexivity, transitivity, and that a block's parent precedes it;
* `Chained`, the invariant, which is the lemma's four claims plus a fifth about the named target;
* the step lemmas, one per routine of Figures 1 and 2, and the induction that closes the lemma.

## `Chained` needs no threshold hypothesis, where `Settled` did

`Settled` (`Analysis/Proofs/SlotClosure.lean`) carries `0 < q` through every step, because on an
empty electorate every set is a quorum and no branch of the height-event check is ever blocked.
`Chained` needs no such thing: every branch preserves it *whether or not it fires*, so no
threshold and no quorum enters this file. That is why Lemma 4 has no `PositiveWeight` where
Lemma 3 does.

## `Chained.of_fields` is what keeps the step lemmas short

The congruence lemma: a state agreeing with a chained one on the seven fields `Chained` mentions
is chained. The attestation loop and the cursor bump change none of them, so
`of_fields h rfl rfl rfl rfl rfl rfl rfl` discharges those in one line — even though the goal is
a fully expanded record literal that is not syntactically the source.
-/

set_option autoImplicit false

namespace Decoupled

open scoped Decoupled
open Framework.StsMultisetLog

variable {Node Root : Type}

/-! ## Definition 5 (`def:block-chain`)'s ancestry, as a preorder

`⪯` is `a ∈ ancestors b`, so these are list-membership facts about the chain `ancestors` walks.
Neither needs `DecidableEq`: walking the chain compares nothing.
-/

/-- `⪯` is reflexive. Definition 5 (`def:block-chain`) makes "descendant" reflexive, and
    `ancestors` puts the block itself at the head of its own list. -/
theorem Preceq.refl (a : Blk Node Root) : a ⪯ a := by
  cases a <;> simp [Preceq, ancestors]

/-- An ancestor's ancestors are ancestors: the content of transitivity, by structural recursion
    on the descendant. -/
theorem ancestors_subset : ∀ {b c : Blk Node Root}, b ⪯ c →
    ∀ x, x ∈ ancestors b → x ∈ ancestors c
  | _, .genesis, h, x, hx => by
      simp only [Preceq, ancestors, List.mem_singleton] at h
      subst h; exact hx
  | _, .mk p s n a r, h, x, hx => by
      simp only [Preceq, ancestors, List.mem_cons] at h
      rcases h with rfl | h
      · exact hx
      · exact List.mem_cons_of_mem _ (ancestors_subset h x hx)

/-- `⪯` is transitive. -/
theorem Preceq.trans {a b c : Blk Node Root} (hab : a ⪯ b) (hbc : b ⪯ c) : a ⪯ c :=
  ancestors_subset hbc a hab

/-- Genesis precedes every block: `ancestors` always ends at it. -/
theorem genesis_preceq : ∀ (B : Blk Node Root), (Blk.genesis : Blk Node Root) ⪯ B
  | .genesis => Preceq.refl _
  | .mk p _ _ _ _ => List.mem_cons_of_mem _ (genesis_preceq p)

/-- A block's parent precedes it. This is what turns `process_block`'s `parent = σ.L` check into
    an ancestry fact, and it is the only place the check is used. -/
theorem parent_preceq : ∀ {B P : Blk Node Root}, B.parent = some P → P ⪯ B
  | .genesis, _, h => by simp [Blk.parent] at h
  | .mk p _ _ _ _, _, h => by
      simp only [Blk.parent, Option.some.injEq] at h
      subst h
      exact List.mem_cons_of_mem _ (Preceq.refl p)

/-! ### Strict ancestry, by counting the chain

`≺` is `⪯` plus `≠`, and the `≠` half is where acyclicity is needed: a block is not its own parent.
Counting is what supplies it — `ancestors` of a child is one longer than `ancestors` of its parent —
so no antisymmetry lemma and no `sizeOf` argument is required.
-/

theorem ancestors_length_le_of_preceq : ∀ {a b : Blk Node Root}, a ⪯ b →
    (ancestors a).length ≤ (ancestors b).length
  | _, .genesis, h => by
      simp only [Preceq, ancestors, List.mem_singleton] at h
      subst h; exact le_refl _
  | _, .mk p _ _ _ _, h => by
      simp only [Preceq, ancestors, List.mem_cons] at h
      rcases h with rfl | h
      · exact le_refl _
      · have := ancestors_length_le_of_preceq h
        simp only [ancestors, List.length_cons]
        omega

theorem ancestors_length_lt_of_prec : ∀ {b c : Blk Node Root}, b ≺ c →
    (ancestors b).length < (ancestors c).length
  | _, .genesis, h => by
      obtain ⟨h1, h2⟩ := h
      simp only [Preceq, ancestors, List.mem_singleton] at h1
      exact absurd h1 h2
  | _, .mk p _ _ _ _, h => by
      obtain ⟨h1, h2⟩ := h
      simp only [Preceq, ancestors, List.mem_cons] at h1
      rcases h1 with rfl | h1
      · exact absurd rfl h2
      · have := ancestors_length_le_of_preceq h1
        simp only [ancestors, List.length_cons]
        omega

/-- A block *strictly* follows its parent. Equality would make two chains of different length
    equal, which is what the `congrArg` on `length` says. -/
theorem parent_prec : ∀ {B P : Blk Node Root}, B.parent = some P → P ≺ B
  | .genesis, _, h => by simp [Blk.parent] at h
  | .mk p _ _ _ _, _, h => by
      simp only [Blk.parent, Option.some.injEq] at h
      subst h
      refine ⟨List.mem_cons_of_mem _ (Preceq.refl p), fun he => ?_⟩
      have := congrArg (fun b => (ancestors (Node := Node) (Root := Root) b).length) he
      simp [ancestors] at this

/-- **Two ancestors of one block are comparable.** A block's ancestors are a chain, not a tree, so
    anything two of them can be is one before the other.

    Structural recursion on the common descendant: at a child, either one of the two *is* that
    child — and then the other precedes it — or both are ancestors of the parent. -/
theorem preceq_or_preceq : ∀ (c : Blk Node Root) {a b : Blk Node Root}, a ⪯ c → b ⪯ c →
    a ⪯ b ∨ b ⪯ a
  | .genesis, a, b, ha, hb => by
      simp only [Preceq, ancestors, List.mem_singleton] at ha hb
      subst ha; subst hb
      exact Or.inl (Preceq.refl _)
  | .mk p s n as r, a, b, ha, hb => by
      simp only [Preceq, ancestors, List.mem_cons] at ha hb
      rcases ha with rfl | ha
      · exact Or.inr (by simpa only [Preceq, ancestors, List.mem_cons] using hb)
      rcases hb with rfl | hb
      · exact Or.inl (by simpa only [Preceq, ancestors, List.mem_cons] using Or.inr ha)
      exact preceq_or_preceq p ha hb

/-- `⪯` composes with `≺` on the left, and the strictness survives by the count. -/
theorem Preceq.trans_prec {a b c : Blk Node Root} (hab : a ⪯ b) (hbc : b ≺ c) : a ≺ c :=
  ⟨Preceq.trans hab hbc.1, fun he => by
    have h1 := ancestors_length_le_of_preceq hab
    have h2 := ancestors_length_lt_of_prec hbc
    rw [he] at h1
    omega⟩

/-- **`⪯` is antisymmetric**: two blocks each preceding the other are the same block. Same count
    as the two lemmas above — were they distinct, one would be a strict ancestor of the other and
    so have the strictly shorter chain, while the other inequality bounds it the other way. -/
theorem Preceq.antisymm {a b : Blk Node Root} (hab : a ⪯ b) (hba : b ⪯ a) : a = b := by
  by_contra hne
  have h1 := ancestors_length_lt_of_prec (⟨hab, hne⟩ : a ≺ b)
  have h2 := ancestors_length_le_of_preceq hba
  omega

namespace Proofs

/-! ## The invariant -/

/-- The invariant Lemma 4 is proved from. The first four fields are the lemma's own claims; the
    fifth is not in its statement.

    **`targetOnChain` is the conjunct the paper does not state.** It is needed because the target
    branch of the height-event check sets `J ← T_h`, so keeping `F ⪯ J ⪯ L` across that branch
    needs the named target to sit between `J` and `L`. The paper asserts exactly this inside its
    own proof (Lemma 4, `lem:finalized-before-justified`) — "the justification branch sets
    `J = T_h`, which lies on the current chain and already contains the previous `J`"
    (lines 939–940) — without recording it as a hypothesis of
    anything. It is true because `process_slot` is the only routine that names a target and it
    writes `some σ.L`, `advance_height` writing `⊥`. -/
structure Chained (σ : ChainState Node Root) : Prop where
  /-- The finalized block precedes the justified block. -/
  finJust : σ.F ⪯ σ.J
  /-- The justified block precedes the latest block. -/
  justLatest : σ.J ⪯ σ.L
  /-- The finalized height is at most the justified height. -/
  hF_le_hj : σ.h_F ≤ σ.h_j
  /-- The justified height is below the state height. -/
  hj_lt_h : σ.h_j < σ.h
  /-- Not in the paper's statement. See the structure's docstring. -/
  targetOnChain : ∀ T, σ.T_h = some T → σ.J ⪯ T ∧ T ⪯ σ.L

/-- The finality sub-step of the height-event check copies `(J, h_j)` into `(F, h_F)`, which makes
    the first two claims equalities. -/
theorem Chained.finalizeStep {σ : ChainState Node Root} (h : Chained σ) :
    Chained { σ with F := σ.J, h_F := σ.h_j } :=
  { finJust := Preceq.refl _, justLatest := h.justLatest,
    hF_le_hj := le_refl _, hj_lt_h := h.hj_lt_h, targetOnChain := h.targetOnChain }

/-- The congruence lemma. See the file docstring: this is what makes the steps that touch none of
    the seven fields one line each. -/
theorem Chained.of_fields {σ τ : ChainState Node Root} (h : Chained σ)
    (hF : τ.F = σ.F) (hJ : τ.J = σ.J) (hL : τ.L = σ.L) (hhF : τ.h_F = σ.h_F)
    (hhj : τ.h_j = σ.h_j) (hh : τ.h = σ.h) (hT : τ.T_h = σ.T_h) : Chained τ :=
  { finJust := by rw [hF, hJ]; exact h.finJust
    justLatest := by rw [hJ, hL]; exact h.justLatest
    hF_le_hj := by rw [hhF, hhj]; exact h.hF_le_hj
    hj_lt_h := by rw [hhj, hh]; exact h.hj_lt_h
    targetOnChain := by
      intro T hTT; rw [hT] at hTT; rw [hJ, hL]; exact h.targetOnChain T hTT }

/-- Naming a target keeps the invariant, and this is where `targetOnChain` comes from: the target
    written is `σ.L` itself, which `justLatest` puts after `J` and reflexivity puts at `L`. -/
theorem Chained.setTarget {σ : ChainState Node Root} (h : Chained σ) :
    Chained { σ with T_h := some σ.L } :=
  { finJust := h.finJust, justLatest := h.justLatest, hF_le_hj := h.hF_le_hj,
    hj_lt_h := h.hj_lt_h,
    targetOnChain := by
      intro T hT
      simp only [Option.some.injEq] at hT
      subst hT
      exact ⟨h.justLatest, Preceq.refl _⟩ }

/-- `Chained` holds at genesis: all three blocks are `genesis`, and `h_F = h_j = 0 < 1 = h`. -/
theorem chained_gen : Chained (ChainState.gen (Node := Node) (Root := Root)) :=
  { finJust := Preceq.refl _, justLatest := Preceq.refl _,
    hF_le_hj := le_refl _, hj_lt_h := Nat.zero_lt_one,
    targetOnChain := by
      intro T hT
      simp only [ChainState.gen, Option.some.injEq] at hT
      subst hT
      exact ⟨Preceq.refl _, Preceq.refl _⟩ }

section
variable [DecidableEq Node] [DecidableEq Root] [Electorate Node] [Params]

/-! ## The step lemmas, one per routine

Each is stated with `_root_.Decoupled.` on the routine it is about: inside `theorem Chained.foo`
the namespace `Chained` joins the resolution path, so a bare `advanceHeight` in the body would
resolve to `Chained.advanceHeight` — the theorem itself — and `simp only` would report no progress.
-/

/-- A height transition keeps the invariant. `hj` is the fact about the justification being
    installed that `targetOnChain` supplies at the call site: whatever is justified lies between
    `J` and `L`. -/
theorem Chained.advanceHeight {σ : ChainState Node Root} (h : Chained σ)
    (justify : Option (Blk Node Root)) (start : Time)
    (hj : ∀ T, justify = some T → σ.J ⪯ T ∧ T ⪯ σ.L) :
    Chained (_root_.Decoupled.advanceHeight σ justify start) := by
  have h3 := h.hF_le_hj
  have h4 := h.hj_lt_h
  cases justify with
  | none =>
      refine { finJust := ?_, justLatest := ?_, hF_le_hj := ?_, hj_lt_h := ?_,
               targetOnChain := ?_ } <;>
        simp only [_root_.Decoupled.advanceHeight] <;>
        simp [h.finJust, h.justLatest] <;> omega
  | some T =>
      obtain ⟨hJT, hTL⟩ := hj T rfl
      refine { finJust := ?_, justLatest := ?_, hF_le_hj := ?_, hj_lt_h := ?_,
               targetOnChain := ?_ } <;>
        simp only [_root_.Decoupled.advanceHeight] <;>
        simp [Preceq.trans h.finJust hJT, hTL]
      all_goals omega

/-- The height-event check keeps the invariant, whichever of Definition 18's branches it takes.
    `Id.run` is in the `simp only` set so that `split_ifs` reaches the `if`s. -/
theorem Chained.processHeightEvents {σ : ChainState Node Root} (h : Chained σ) (start : Time) :
    Chained (_root_.Decoupled.processHeightEvents σ start) := by
  simp only [_root_.Decoupled.processHeightEvents, Id.run]
  split_ifs
  all_goals
    first
      | exact h.finalizeStep.advanceHeight _ start (fun T hT => h.targetOnChain T hT)
      | exact h.advanceHeight _ start (fun T hT => h.targetOnChain T hT)
      | exact h.finalizeStep.advanceHeight ⊥ start (by simp)
      | exact h.advanceHeight ⊥ start (by simp)
      | exact h.finalizeStep
      | exact h

/-- Closing one slot keeps the invariant: it may name a target, may run the height check, and
    bumps the cursor, which is not one of the seven fields. -/
theorem Chained.processSlot {σ : ChainState Node Root} (h : Chained σ) :
    Chained (_root_.Decoupled.processSlot σ) := by
  simp only [_root_.Decoupled.processSlot, Id.run]
  split_ifs
  all_goals
    first
      | exact Chained.of_fields (h.setTarget.processHeightEvents _) rfl rfl rfl rfl rfl rfl rfl
      | exact Chained.of_fields (h.processHeightEvents _) rfl rfl rfl rfl rfl rfl rfl
      | exact Chained.of_fields h.setTarget rfl rfl rfl rfl rfl rfl rfl
      | exact Chained.of_fields h rfl rfl rfl rfl rfl rfl rfl

theorem Chained.closeSlots :
    ∀ (n : Nat) {σ : ChainState Node Root}, Chained σ →
      Chained (_root_.Decoupled.Proofs.closeSlots n σ)
  | 0, _, h => by rw [_root_.Decoupled.Proofs.closeSlots]; exact h
  | n + 1, _, h => by
      rw [_root_.Decoupled.Proofs.closeSlots]; exact Chained.closeSlots n h.processSlot

/-- Closing slots up to `t` keeps the invariant, through `closeSlots` rather than the `while`. -/
theorem Chained.processSlots {σ : ChainState Node Root} (h : Chained σ) (t : Time) :
    Chained (_root_.Decoupled.processSlots σ t) := by
  rw [processSlots_eq_closeSlots]; exact Chained.closeSlots _ h

/-- Attestation processing touches none of the six block and height fields: it writes
    participation bits, `P`, and the tallies. -/
theorem processAttestation_chainFields (σ : ChainState Node Root) (a : Attestation Node Root)
    (A : Blk Node Root) :
    (processAttestation σ a A).L = σ.L ∧ (processAttestation σ a A).J = σ.J ∧
      (processAttestation σ a A).F = σ.F ∧ (processAttestation σ a A).h = σ.h ∧
      (processAttestation σ a A).h_j = σ.h_j ∧ (processAttestation σ a A).h_F = σ.h_F := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    · simp only [processAttestation]
      repeat' split
      all_goals rfl

/-- The attestation fold leaves every block and height field alone. -/
theorem processAttestations_chainFields :
    ∀ (as : List (Attestation Node Root)) {σ : ChainState Node Root} (A : Blk Node Root),
      (processAttestations σ as A).L = σ.L ∧ (processAttestations σ as A).J = σ.J ∧
        (processAttestations σ as A).h = σ.h
  | [], _, _ => ⟨rfl, rfl, rfl⟩
  | a :: as, σ, A => by
      obtain ⟨hL, hJ, -, hh, -, -⟩ := processAttestation_chainFields σ a A
      obtain ⟨h1, h2, h3⟩ := processAttestations_chainFields as (σ := processAttestation σ a A) A
      rw [processAttestations_cons]
      exact ⟨by rw [h1, hL], by rw [h2, hJ], by rw [h3, hh]⟩

theorem Chained.processAttestation {σ : ChainState Node Root} (h : Chained σ)
    (a : Attestation Node Root) (A : Blk Node Root) :
    Chained (_root_.Decoupled.processAttestation σ a A) := by
  obtain ⟨hL, hJ, hF, hh, hhj, hhF⟩ := processAttestation_chainFields σ a A
  exact h.of_fields hF hJ hL hhF hhj hh (processAttestation_T_h σ a A)

theorem Chained.processAttestations :
    ∀ (as : List (Attestation Node Root)) {σ : ChainState Node Root} (A : Blk Node Root),
      Chained σ → Chained (_root_.Decoupled.processAttestations σ as A)
  | [], _, _, h => h
  | a :: as, _, A, h => by
      rw [processAttestations_cons]
      exact Chained.processAttestations as A (h.processAttestation a A)

/-- The block phase keeps the invariant. This is the one step that needs an ancestry fact rather
    than a field lemma: `L` is replaced by the block, and `J ⪯ L` survives because
    `process_block` has already checked `B.parent = some σ.L`, so `σ.L ⪯ B`. -/
theorem Chained.processBlock {σ σ' : ChainState Node Root} {B : Blk Node Root}
    (h : Chained σ) (he : processBlock σ B = .state σ') : Chained σ' := by
  have hpar : B.parent = some σ.L := by
    simp only [_root_.Decoupled.processBlock, Id.run] at he
    split_ifs at he with hc
    simp only [not_or, ne_eq, not_not] at hc
    exact hc.1
  have hLB : σ.L ⪯ B := parent_preceq hpar
  have hext : Chained { σ with L := B } :=
    { finJust := h.finJust, justLatest := Preceq.trans h.justLatest hLB,
      hF_le_hj := h.hF_le_hj, hj_lt_h := h.hj_lt_h,
      targetOnChain := fun T hT =>
        ⟨(h.targetOnChain T hT).1, Preceq.trans (h.targetOnChain T hT).2 hLB⟩ }
  rw [processBlock_state he]
  exact hext.processAttestations _ _

/-- A whole transition keeps the invariant, the three phases composed. Unlike `Settled`, every
    phase keeps all five conjuncts, so nothing has to be re-established at the end. -/
theorem Chained.stateTransition {σ σ' : ChainState Node Root} {B : Blk Node Root}
    (h : Chained σ) (he : _root_.Decoupled.stateTransition σ B = .state σ') : Chained σ' := by
  obtain ⟨σ₂, hb, rfl⟩ := stateTransition_state he
  exact ((h.processSlots B.slot).processBlock hb).processHeightEvents _

/-- Every block post-state is `Chained`, by induction. -/
theorem chained_of_blockPostState {σ : ChainState Node Root} (h : BlockPostState σ) :
    Chained σ := by
  induction h with
  | gen => exact chained_gen
  | step _ hst ih => exact ih.stateTransition hst

/-- A finality action state is `Chained` too. `actionState` is `process_slots`, so this is
    `Chained.processSlots` applied to the block post-state it starts from — and it needs no
    threshold hypothesis, where routing the same claim through Lemma 3 would have needed one. -/
theorem chained_actionState {σ : ChainState Node Root} (h : BlockPostState σ) (t : Time) :
    Chained (actionState σ t) :=
  (chained_of_blockPostState h).processSlots t

/-- **Lemma 4**, both of the subjects its sentence names. Read aloud: in a block post-state and in
    any of its finality action states alike, the finalized block is the justified block or an
    ancestor of it, the justified block is the latest block or an ancestor of it, and the finalized
    height is at most the justified height, which is below the state height.

    The four conjuncts read straight off `Chained`, twice. The fifth, `targetOnChain`, is what
    carries the induction and is not part of the paper's sentence. -/
theorem finalizedBeforeJustified {σ : ChainState Node Root} (h : BlockPostState σ) (t : Time) :
    let σa := actionState σ t
    (σ.F ⪯ σ.J ∧ σ.J ⪯ σ.L ∧ σ.h_F ≤ σ.h_j ∧ σ.h_j < σ.h) ∧
      (σa.F ⪯ σa.J ∧ σa.J ⪯ σa.L ∧ σa.h_F ≤ σa.h_j ∧ σa.h_j < σa.h) :=
  let c := chained_of_blockPostState h
  let ca := chained_actionState h t
  ⟨⟨c.finJust, c.justLatest, c.hF_le_hj, c.hj_lt_h⟩,
    ca.finJust, ca.justLatest, ca.hF_le_hj, ca.hj_lt_h⟩

end

end Proofs

end Decoupled
