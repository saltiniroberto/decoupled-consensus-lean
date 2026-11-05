module
public import GoldilocksCorrectness.Proofs.Routines.Score
public import GoldilocksCorrectness.Proofs.Routines.Locks
public import GoldilocksCorrectness.Proofs.Routines.Lemma2
public import GoldilocksCorrectness.Proofs.Routines.Kit
public import GoldilocksCorrectness.Proofs.Routines.Confirmation
public import GoldilocksCorrectness.Proofs.Routines.DREPost
import all Init.Data.List.Control
import all Goldilocks.AC.Confirmation
import all Goldilocks.AC.ForkChoice
import all Goldilocks.AC.State

@[expose] public section

/-!
# The routines that may fail answer

`DREOk m` says that the routine `m`, which may fail, answers; `DREBOk m` says that the duty `m`,
which may fail and sends objects, answers from every list of objects sent so far. This page holds
the composition lemmas for both, then the sites where the spec can fail, each answered under the
condition that excludes it: the root lookup `blockWithRoot` (no two blocks of the tree share a
root), the late filter `beforeCutoff` and the resolution time (every vote read is stamped, every
block of the tree is stamped) and the voter's block tree (every block of the frame's tree is
stamped). Then the routines composed of these sites that read no node invariant: the walk, the
head, the opponents of a lock and the moved lock entry, the fast confirmation test.
-/

set_option autoImplicit false

open scoped DC

open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn)
open GoldilocksCorrectness.Proofs.Routines (DREPost DREBPost)

variable {V : Type}

/-! ## The kit -/

/-- `DREOk m`: the routine `m`, which may fail, answers.

Read aloud: `m` is `.ok a` for some `a`.

The variables:
- `m`: the routine. -/
def DREOk {α : Type} (m : DRE α) : Prop := ∃ a : α, m = .ok a

/-- `DREBOk m`: the duty `m`, which may fail and sends objects, answers from every list of objects
sent so far.

Read aloud: whatever was sent before it ran, `m` answers.

The variables:
- `m`: the duty. -/
def DREBOk {α : Type} (m : DREB V α) : Prop :=
  ∀ out : List (NamedObject V), ∃ r : α × List (NamedObject V), m.run out = .ok r

/-- A routine that returns a value answers.

The variables:
- `a`: the value returned. -/
theorem DREOk.pure {α : Type} (a : α) : DREOk (Pure.pure a : DRE α) := ⟨a, rfl⟩

/-- A bind answers when its first routine answers and its continuation answers on every value
satisfying a postcondition of the first routine.

The variables:
- `x`: the first routine; `f`: the continuation; `P`: the postcondition of `x`. -/
theorem DREOk.bind {α β : Type} {x : DRE α} {f : α → DRE β} {P : α → Prop}
    (hx : DREOk x) (hP : DREPost x P) (hf : ∀ a, P a → DREOk (f a)) : DREOk (x >>= f) := by
  obtain ⟨a, ha⟩ := hx
  rw [ha, dre_bind_ok]
  exact hf a (hP a ha)

/-- A bind answers when its first routine answers and its continuation answers on every value.

The variables:
- `x`: the first routine; `f`: the continuation. -/
theorem DREOk.bind_any {α β : Type} {x : DRE α} {f : α → DRE β}
    (hx : DREOk x) (hf : ∀ a, DREOk (f a)) : DREOk (x >>= f) :=
  DREOk.bind hx (DREPost.true x) (fun a _ => hf a)

/-- An `if` answers when each branch answers under its condition.

The variables:
- `c`: the condition; `A`, `B`: the two branches. -/
theorem DREOk.ite {α : Type} {c : Prop} [Decidable c] {A B : DRE α}
    (hA : c → DREOk A) (hB : ¬c → DREOk B) : DREOk (if c then A else B) := by
  split
  · exact hA ‹_›
  · exact hB ‹_›

/-- A dependent `if` answers when each branch answers on every proof of its condition.

The variables:
- `c`: the condition; `A`, `B`: the two branches. -/
theorem DREOk.dite {α : Type} {c : Prop} [Decidable c] {A : c → DRE α} {B : ¬c → DRE α}
    (hA : ∀ h, DREOk (A h)) (hB : ∀ h, DREOk (B h)) : DREOk (dite c A B) := by
  split
  · exact hA ‹_›
  · exact hB ‹_›

/-- The raising lift out of `Option` answers when the option is not `none`.

The variables:
- `x`: the option. -/
theorem DREOk.liftOption {α : Type} {x : Option α} (h : x ≠ none) : DREOk (liftM x : DRE α) := by
  cases x with
  | none => exact absurd rfl h
  | some a => exact ⟨a, rfl⟩

/-- A duty that returns a value, sending nothing, answers.

The variables:
- `a`: the value returned. -/
theorem DREBOk.pure {α : Type} (a : α) : DREBOk (Pure.pure a : DREB V α) :=
  fun out => ⟨(a, out), rfl⟩

/-- A bind of duties answers when its first duty answers and its continuation answers on every
value satisfying a postcondition of the first duty.

The variables:
- `x`: the first duty; `f`: the continuation; `P`: the postcondition of `x`. -/
theorem DREBOk.bind {α β : Type} {x : DREB V α} {f : α → DREB V β} {P : α → Prop}
    (hx : DREBOk x) (hP : DREBPost x P) (hf : ∀ a, P a → DREBOk (f a)) : DREBOk (x >>= f) := by
  intro out
  obtain ⟨⟨a, out'⟩, h⟩ := hx out
  obtain ⟨r, hr⟩ := hf a (hP out a out' h) out'
  refine ⟨r, ?_⟩
  show (x.run out >>= fun p => (f p.1).run p.2) = .ok r
  rw [h, dre_bind_ok]
  exact hr

/-- A bind of duties answers when its first duty answers and its continuation answers on every
value.

The variables:
- `x`: the first duty; `f`: the continuation. -/
theorem DREBOk.bind_any {α β : Type} {x : DREB V α} {f : α → DREB V β}
    (hx : DREBOk x) (hf : ∀ a, DREBOk (f a)) : DREBOk (x >>= f) :=
  DREBOk.bind hx (DREBPost.true x) (fun a _ => hf a)

/-- An `if` of duties answers when each branch answers under its condition.

The variables:
- `c`: the condition; `A`, `B`: the two branches. -/
theorem DREBOk.ite {α : Type} {c : Prop} [Decidable c] {A B : DREB V α}
    (hA : c → DREBOk A) (hB : ¬c → DREBOk B) : DREBOk (if c then A else B) := by
  split
  · exact hA ‹_›
  · exact hB ‹_›

/-- A dependent `if` of duties answers when each branch answers on every proof of its condition.

The variables:
- `c`: the condition; `A`, `B`: the two branches. -/
theorem DREBOk.dite {α : Type} {c : Prop} [Decidable c] {A : c → DREB V α} {B : ¬c → DREB V α}
    (hA : ∀ h, DREBOk (A h)) (hB : ∀ h, DREBOk (B h)) : DREBOk (dite c A B) := by
  split
  · exact hA ‹_›
  · exact hB ‹_›

/-- A routine that answers, run as a duty that sends nothing, answers.

The variables:
- `m`: the routine. -/
theorem DREBOk.liftM {α : Type} {m : DRE α} (h : DREOk m) : DREBOk (liftM m : DREB V α) := by
  intro out
  obtain ⟨a, ha⟩ := h
  exact ⟨(a, out), by rw [ha]; rfl⟩

/-- A routine that answers, lifted into a duty by `MonadLift.monadLift`, answers.

The variables:
- `m`: the routine. -/
theorem DREBOk.monadLift {α : Type} {m : DRE α} (h : DREOk m) :
    DREBOk (MonadLift.monadLift m : DREB V α) := by
  intro out
  obtain ⟨a, ha⟩ := h
  exact ⟨(a, out), by rw [ha]; rfl⟩

/-- Sending an object answers.

The variables:
- `o`: the object sent. -/
theorem DREBOk.broadcast (o : NamedObject V) : DREBOk (broadcast o) :=
  fun out => ⟨((), out ++ [o]), rfl⟩

/-- A raising image of a finite set answers when its function answers on every member.

The variables:
- `f`: the function; `s`: the set. -/
theorem imageM_ok_of_total {α β : Type} [DecidableEq α] [DecidableEq β] (f : α → DRE β)
    (s : Finset α) (h : ∀ a ∈ s, DREOk (f a)) : DREOk (s.imageM f) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨∅, rfl⟩
  | @insert a s ha ih =>
    obtain ⟨b, hb⟩ := h a (Finset.mem_insert_self a s)
    obtain ⟨R, hR⟩ := ih (fun x hx => h x (Finset.mem_insert_of_mem hx))
    have hstep : (insert a s).imageM f =
        Finset.unionM (do return {← f a}) (s.imageM f) := by
      simp only [Finset.imageM, Finset.fold_insert ha]
    rw [hstep, hb, hR]
    exact ⟨_, rfl⟩

/-- The accumulating loop of a raising list filter answers, from every accumulator, when its test
answers on every member.

The variables:
- `p`: the test; `l`: the list. -/
theorem List.filterAuxM_ok_of_total {α : Type} (p : α → DRE Bool) (l : List α)
    (h : ∀ a ∈ l, DREOk (p a)) : ∀ acc : List α, DREOk (List.filterAuxM p l acc) := by
  induction l with
  | nil => exact fun acc => ⟨acc, rfl⟩
  | cons b l ih =>
    intro acc
    have hstep : List.filterAuxM p (b :: l) acc =
        (p b >>= fun c => List.filterAuxM p l (cond c (b :: acc) acc)) := rfl
    rw [hstep]
    exact DREOk.bind_any (h b (List.mem_cons_self ..))
      (fun c => ih (fun a ha => h a (List.mem_cons_of_mem b ha)) _)

/-- A raising list filter answers when its test answers on every member.

The variables:
- `p`: the test; `l`: the list. -/
theorem List.filterM_ok_of_total {α : Type} (p : α → DRE Bool) (l : List α)
    (h : ∀ a ∈ l, DREOk (p a)) : DREOk (l.filterM p) := by
  have hstep : l.filterM p = (List.filterAuxM p l [] >>= fun as => pure as.reverse) := rfl
  rw [hstep]
  exact DREOk.bind_any (List.filterAuxM_ok_of_total p l h []) (fun _ => DREOk.pure _)

variable [DecidableEq V] [Fintype V]

/-! ## The sites where the spec can fail -/

/-- The late filter `beforeCutoff ts t S` answers when every member of `S` has a stamp in `ts`
(the raising lift of `Goldilocks/Objects.lean:450`).

The variables:
- `ts`: the stamps; `t`: the cutoff; `S`: the set filtered. -/
theorem beforeCutoff_ok {α : Type} [DecidableEq α] (ts : TimestampMap α) (t : Time)
    (S : Finset α) (h : ∀ a ∈ S, ts a ≠ none) : DREOk (beforeCutoff ts t S) :=
  filterM_eq_ok_of_total _ S (fun a ha =>
    DREOk.bind_any (DREOk.liftOption (h a ha)) (fun _ => DREOk.pure _))

omit [Fintype V] in
/-- The resolution time of a vote answers when no two blocks of the tree share a root, the vote is
stamped and every block of the tree is stamped (the root lookup of `Goldilocks/Objects.lean:479`,
the raising lifts of `:483` and `:484`).

The variables:
- `T`: the tree; `tb`: the blocks' stamps; `tv`: the votes' stamps; `vote`: the vote. -/
theorem resolution_time_ok (T : Finset (Block V)) (tb : TimestampMap (Block V))
    (tv : TimestampMap (GoldfishVote V)) (vote : GoldfishVote V)
    (hRoots : RootsNameBlocksIn T) (hv : tv vote ≠ none) (hb : ∀ H ∈ T, tb H ≠ none) :
    DREOk (resolution_time T tb tv vote) := by
  simp only [resolution_time, blockWithRoot_eq_ok hRoots, dre_bind_ok]
  generalize hX : Block.find? T vote.head = X
  cases X with
  | none => exact ⟨_, rfl⟩
  | some H =>
    have hH : H ∈ T := (mem_of_pickUnique?_eq_some hX).1
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, dite_true, Option.value, Option.get_some]
    refine DREOk.ite (fun _ => ?_) (fun _ => DREOk.pure _)
    exact DREOk.bind_any (DREOk.liftOption hv) (fun _ =>
      DREOk.bind_any (DREOk.liftOption (hb H hH)) (fun _ => DREOk.pure _))

omit [Fintype V] in
/-- `A.tau Φ vote`, the resolution time of `vote` in the frame's tree, answers when no two blocks
of the frame's tree share a root, the vote is stamped and every block of the frame's tree is
stamped.

The variables:
- `A`: the AC state; `Φ`: the frame; `vote`: the vote. -/
theorem tau_ok (A : ACState V) (Φ : Frame V) (vote : GoldfishVote V)
    (hRoots : RootsNameBlocksIn Φ.tree) (hv : A.timestamp_vote vote ≠ none)
    (hb : ∀ H ∈ Φ.tree, A.timestamp_block H ≠ none) : DREOk (A.tau Φ vote) :=
  resolution_time_ok _ _ _ _ hRoots hv hb

omit [Fintype V] in
/-- `resolved T vote` answers when no two blocks of `T` share a root (the root lookup of
`Goldilocks/Objects.lean:461`).

The variables:
- `T`: the tree; `vote`: the vote. -/
theorem resolved_ok (T : Finset (Block V)) (vote : GoldfishVote V)
    (hRoots : RootsNameBlocksIn T) : DREOk (resolved T vote) := by
  simp only [resolved, blockWithRoot_eq_ok hRoots, dre_bind_ok]
  exact DREOk.dite (fun _ => DREOk.pure _) (fun _ => DREOk.pure _)

-- The `do` block of `voter_block_tree` ends `let blocks ← e; return blocks`, which elaborates to
-- `e` alone: the first alternative closes the goal and the second, for a bind, is never run.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
omit [Fintype V] in
/-- The voter's block tree answers when every block of the frame's tree is stamped (the raising
lift of `Goldilocks/AC/ForkChoice.lean:219`).

The variables:
- `C`: the configuration; `A`: the AC state; `Φ`: the frame; `s`: the slot. -/
theorem voter_block_tree_ok (C : Config) (A : ACState V) (Φ : Frame V) (s : Slot)
    (hb : ∀ B ∈ Φ.tree, A.timestamp_block B ≠ none) : DREOk (voter_block_tree C A Φ s) := by
  simp only [voter_block_tree]
  first
    | exact filterM_eq_ok_of_total _ _ (fun B hB =>
        DREOk.bind_any (DREOk.liftOption (hb B hB)) (fun _ => DREOk.pure _))
    | exact DREOk.bind_any (filterM_eq_ok_of_total _ _ (fun B hB =>
        DREOk.bind_any (DREOk.liftOption (hb B hB)) (fun _ => DREOk.pure _)))
        (fun _ => DREOk.pure _)

/-! ## The routines that compose the sites -/

section Routines

variable [RootOrder]

omit [DecidableEq V] [Fintype V] in
/-- The comparison of two blocks by the walk answers when the score answers on every block.

The variables:
- `score`: the score; `B`, `C`: the two blocks compared. -/
theorem outranks_ok (score : Block V → DRE Nat) (hs : ∀ D, DREOk (score D)) (B C : Block V) :
    DREOk (outranks score B C) := by
  simp only [outranks]
  exact DREOk.bind_any (hs B) (fun _ => DREOk.bind_any (hs C) (fun _ => DREOk.pure _))

omit [Fintype V] in
/-- The test that a block is the best of a set of children answers when the score answers on every
block.

The variables:
- `score`: the score; `children`: the set of children; `B`: the block tested. -/
theorem is_best_in_ok (score : Block V → DRE Nat) (hs : ∀ D, DREOk (score D))
    (children : Finset (Block V)) (B : Block V) : DREOk (is_best_in score children B) := by
  simp only [is_best_in]
  exact DREOk.bind_any (filterM_eq_ok_of_total _ _ (fun C _ => outranks_ok score hs C B))
    (fun _ => DREOk.pure _)

omit [Fintype V] in
/-- The best of a set of children answers when the score answers on every block.

The variables:
- `score`: the score; `children`: the set of children. -/
theorem argmax?_ok (score : Block V → DRE Nat) (hs : ∀ D, DREOk (score D))
    (children : Finset (Block V)) : DREOk (argmax? score children) := by
  simp only [argmax?]
  exact DREOk.bind_any (filterM_eq_ok_of_total _ _ (fun B _ => is_best_in_ok score hs children B))
    (fun _ => DREOk.pure _)

omit [Fintype V] [RootOrder] in
/-- The eligible children of a block answer when the eligibility test answers on every block.

The variables:
- `tree`: the tree; `eligible`: the eligibility test; `H`: the parent. -/
theorem ghost_children_ok (tree : Finset (Block V)) (eligible : Block V → DRE Bool)
    (he : ∀ D, DREOk (eligible D)) (H : Block V) : DREOk (ghost_children tree eligible H) :=
  filterM_eq_ok_of_total _ _ (fun B _ => DREOk.ite (fun _ => he B) (fun _ => DREOk.pure _))

omit [Fintype V] in
/-- One step of the walk answers when the score and the eligibility test answer on every block.

The variables:
- `tree`: the tree; `score`: the score; `eligible`: the eligibility test; `H`: the block the step
  starts from. -/
theorem ghost_step_ok (tree : Finset (Block V)) (score : Block V → DRE Nat)
    (eligible : Block V → DRE Bool) (hs : ∀ D, DREOk (score D)) (he : ∀ D, DREOk (eligible D))
    (H : Block V) : DREOk (ghost_step tree score eligible H) := by
  simp only [ghost_step]
  exact DREOk.bind_any (ghost_children_ok tree eligible he H) (fun ch => argmax?_ok score hs ch)

omit [Fintype V] in
/-- The walk of at most `n` steps answers, from every block, when the score and the eligibility
test answer on every block.

The variables:
- `tree`: the tree; `score`: the score; `eligible`: the eligibility test; `n`: the bound on the
  number of steps. -/
theorem ghost_walk_ok (tree : Finset (Block V)) (score : Block V → DRE Nat)
    (eligible : Block V → DRE Bool) (hs : ∀ D, DREOk (score D)) (he : ∀ D, DREOk (eligible D))
    (n : Nat) : ∀ H : Block V, DREOk (ghost_walk tree score eligible n H) := by
  induction n with
  | zero => exact fun H => DREOk.pure H
  | succ n ih =>
    intro H
    rw [ghost_walk]
    exact DREOk.bind_any (ghost_step_ok tree score eligible hs he H)
      (fun _ => DREOk.dite (fun _ => ih _) (fun _ => DREOk.pure H))

omit [Fintype V] in
/-- The walk from an anchor answers when the score and the eligibility test answer on every block.

The variables:
- `anchor`: the block the walk starts from; `tree`: the tree; `score`: the score; `eligible`: the
  eligibility test. -/
theorem ghost_ok (anchor : Block V) (tree : Finset (Block V)) (score : Block V → DRE Nat)
    (eligible : Block V → DRE Bool) (hs : ∀ D, DREOk (score D)) (he : ∀ D, DREOk (eligible D)) :
    DREOk (ghost anchor tree score eligible) :=
  ghost_walk_ok tree score eligible hs he _ anchor

omit [RootOrder] in
/-- The Goldfish score answers on every block when no two blocks of the frame's tree share a root.

The variables:
- `Φ`: the frame; `votes`, `support_votes`: the votes counted; `s`: the slot; `D`: the block
  scored. -/
theorem goldfish_score_ok {Φ : Frame V} (hRoots : RootsNameBlocksIn Φ.tree)
    (votes support_votes : Finset (GoldfishVote V)) (s : Slot) (D : Block V) :
    DREOk (goldfish_score Φ votes support_votes s D) :=
  ⟨_, goldfish_score_eq_ok hRoots votes support_votes s D⟩

/-- The Goldfish fork choice answers when no two blocks of the frame's tree share a root.

The variables:
- `C`: the configuration; `Φ`: the frame; `t`: the time; `anchor`: the block the walk starts from;
  `tree`: the tree; `votes`, `support_votes`: the votes counted; `s`: the slot. -/
theorem goldfish_fork_choice_ok (C : Config) {Φ : Frame V} (hRoots : RootsNameBlocksIn Φ.tree)
    (t : Time) (anchor : Block V) (tree : Finset (Block V))
    (votes support_votes : Finset (GoldfishVote V)) (s : Slot) :
    DREOk (goldfish_fork_choice C Φ t anchor tree votes support_votes s) :=
  ghost_ok _ _ _ _ (goldfish_score_ok hRoots votes support_votes s)
    (fun D => goldfish_eligible_answers C hRoots t votes support_votes s D)

/-- The head in a given tree answers when no two blocks of the frame's tree share a root.

The variables:
- `C`: the configuration; `A`: the AC state; `Φ`: the frame; `t`: the time; `tree`: the tree;
  `votes`, `support_votes`: the votes counted; `s`: the slot. -/
theorem get_head_in_tree_ok (C : Config) (A : ACState V) {Φ : Frame V}
    (hRoots : RootsNameBlocksIn Φ.tree) (t : Time) (tree : Finset (Block V))
    (votes support_votes : Finset (GoldfishVote V)) (s : Slot) :
    DREOk (get_head_in_tree C A Φ t tree votes support_votes s) :=
  goldfish_fork_choice_ok C hRoots t _ tree votes support_votes s

/-- The head answers when no two blocks of the frame's tree share a root.

The variables:
- `C`: the configuration; `A`: the AC state; `Φ`: the frame; `t`: the time; `votes`,
  `support_votes`: the votes counted; `s`: the slot. -/
theorem get_head_ok (C : Config) (A : ACState V) {Φ : Frame V}
    (hRoots : RootsNameBlocksIn Φ.tree) (t : Time)
    (votes support_votes : Finset (GoldfishVote V)) (s : Slot) :
    DREOk (get_head C A Φ t votes support_votes s) :=
  get_head_in_tree_ok C A hRoots t _ votes support_votes s

omit [Fintype V] [RootOrder] in
/-- The opponents of a lock's block answer when no two blocks of the frame's tree share a root,
every vote counted is stamped and every block of the frame's tree is stamped.

The variables:
- `A`: the AC state; `Φ`: the frame; `votes`: the votes counted; `equivocators`: the validators
  whose votes are not counted; `B'`: the block of the lock. -/
theorem opponents_ok (A : ACState V) {Φ : Frame V} (hRoots : RootsNameBlocksIn Φ.tree)
    (votes : Finset (GoldfishVote V)) (equivocators : Finset V) (B' : Block V)
    -- every vote counted is stamped
    (hv : ∀ vote ∈ votes, A.timestamp_vote vote ≠ none)
    -- every block of the frame's tree is stamped
    (hb : ∀ H ∈ Φ.tree, A.timestamp_block H ≠ none) :
    DREOk (opponents A Φ votes equivocators B') := by
  simp only [opponents]
  refine DREOk.bind_any (filterM_eq_ok_of_total _ _ (fun vote hvote => ?_)) (fun _ => DREOk.pure _)
  exact DREOk.bind_any (tau_ok A Φ vote hRoots (hv vote hvote) hb) (fun _ =>
    DREOk.bind_any ⟨_, opposes_eq_ok hRoots B' vote⟩ (fun _ => DREOk.pure _))

omit [Fintype V] in
/-- The lock entry after the revocation answers under the same three conditions as the opponents:
no two blocks of the frame's tree share a root, every vote counted is stamped and every block of
the frame's tree is stamped.

The variables:
- `P`: the provisional parameters; `A`: the AC state; `Φ`: the frame; `votes`: the votes counted;
  `equivocators`: the validators whose votes are not counted; `s`: the slot; `e`: the lock
  entry. -/
theorem moved_entry_ok (P : Provisional V) (A : ACState V) {Φ : Frame V}
    (hRoots : RootsNameBlocksIn Φ.tree) (votes : Finset (GoldfishVote V))
    (equivocators : Finset V) (s : Slot) (e : LockEntry V)
    -- every vote counted is stamped
    (hv : ∀ vote ∈ votes, A.timestamp_vote vote ≠ none)
    -- every block of the frame's tree is stamped
    (hb : ∀ H ∈ Φ.tree, A.timestamp_block H ≠ none) :
    DREOk (moved_entry P A Φ votes equivocators s e) := by
  simp only [moved_entry]
  refine DREOk.bind_any (filterM_eq_ok_of_total _ _ (fun B' _ => ?_)) (fun _ => ?_)
  · exact DREOk.bind_any (opponents_ok A hRoots votes equivocators B' hv hb)
      (fun _ => DREOk.pure _)
  · exact DREOk.dite (fun _ => DREOk.pure _) (fun _ => DREOk.pure _)

omit [RootOrder] in
/-- The fast confirmation test answers when no two blocks of the frame's tree share a root.

The variables:
- `P`: the provisional parameters; `Φ`: the frame; `support_votes`: the votes counted; `s'`: the
  slot; `B`: the block tested. -/
theorem fast_test_ok (P : Provisional V) {Φ : Frame V} (hRoots : RootsNameBlocksIn Φ.tree)
    (support_votes : Finset (GoldfishVote V)) (s' : Slot) (B : Block V) :
    DREOk (fast_test P Φ support_votes s' B) := by
  simp only [fast_test]
  exact DREOk.bind_any (goldfish_score_ok hRoots _ _ _ B) (fun _ => DREOk.pure _)

end Routines

end GoldilocksCorrectness.Proofs.Routines
