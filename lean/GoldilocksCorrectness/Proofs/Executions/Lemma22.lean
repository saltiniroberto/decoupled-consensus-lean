module
public import GoldilocksCorrectness.Proofs.Routines.Lemma19
public import GoldilocksCorrectness.Proofs.Executions.ProposalPropagation
public import GoldilocksCorrectness.Proofs.Routines.DREPost
public import GoldilocksCorrectness.Proofs.Routines.Node
public import GoldilocksCorrectness.Proofs.Routines.NodeSends

@[expose] public section

/-!
# Lemmas 22a and 22: an honest proposal is held by its proposer, and reaches the next voter

The proofs of `lem22a_proposer_holds_own_proposal` and `lem22_proposal_held_by_voter`, stated in
`GoldilocksCorrectness/Statements/Executions/ProposalPropagationStatements.lean`.

## The routine level

A tick that sends a block ran the proposal in its `if`, on the node state the tick of the
available chain left; at the start of a slot that tick only deletes the expired lock entries
(`ac_on_tick_expire`), so the proposal reads the node's FG state, the pool of its AC state, the
clock `t` and the validator. The proposal broadcasts its block `B` and answers `on_block … B`
(`propose_block_runs`); `block_admissible` answers true on `B` when its root is new to the node,
the attestations of its pool are well formed (`B`'s are some of them), its parent is held, the finalized block is an ancestor of `B` or
`B`, and its parent's slot is earlier than the slot of `t` — the other tests pass by the
construction of `B` and the pool's filing by slot and committee. The attestation duty after it
keeps the tree (`attest_T`). So `B` is in the tree the tick leaves (`tick_proposal_mem_T`).

The relation `DREBRuns R m` ties a routine's answer to what it sends, which neither `DREBPost` nor
`DREBEmits` does alone; its combinators are those of the two.

## Along an execution

- `lem22a`: `p`'s tick at the start of slot `s + 1` is the step `i`, and sent `B` in an outcome
  whose node state `p` holds after the step (`tick_send_step_outcome`); when `B` is an ancestor
  of `p`'s finalized block, `p`'s tree before `t₁` holds `B` (the finalized block is in the tree,
  `lem11_node_invariant`, and so are its ancestors, `ancestors_mem_T_of_exec`) and the tree only grows (`mem_T_mono`); otherwise the
  finalized block is `B` or an ancestor of `B`, and the tick's input state has the FG state and the
  AC state of `p`'s state before `t₁` (`tickInputState_frame`, `stepBefore_eq_of_lbl`); the parent's
  slot is at most the slot `s` of `t₁ − 1` (`slot_lt_of_mem_T_before`); the attestations of `p`'s
  pool are well formed (the node invariant, `lem11_node_invariant`); the routine level gives `B` in
  the tree the tick leaves, which is `x[i + 1][p].st`.
- `lem22`: `mem_T_before_of_send` at `t := t₁`, with `t₁ + Δ = t₃`, so `w` holds `B` before `t₃`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

/-! ## The relation between a routine's answer and what it sends -/

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_eq slot_eq_of_mem voteTime_eq)

namespace GoldilocksCorrectness.Proofs.Executions

open Goldilocks

section Runs

variable {V : Type}

end Runs

end GoldilocksCorrectness.Proofs.Executions

/-! ## The routine level -/

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Statements.Routines
open GoldilocksCorrectness.Proofs.Routines (attest_sends record_awake_frame on_attestation_frame
  on_block_eq)
open GoldilocksCorrectness.Proofs.Routines (ac_on_tick_sends)
open GoldilocksCorrectness.Proofs.Routines (fg_on_block_eq)
open GoldilocksCorrectness.Proofs.Routines (DREBPost DREBEmits DREBRuns)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

end GoldilocksCorrectness.Proofs.Routines

/-! ## Along an execution -/

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicAction AtomicExec Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Proofs.Routines (compatible_of_ancestorEq_compatible compatible_iff)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **Lemma 22a, an honest proposer holds its own proposal.** The proof; the audited statement is
in `Statements/Executions/ProposalPropagationStatements.lean`.

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution; `s`: the slot before the proposal's;
- `i`: the step of `p`'s tick at the start of slot `s + 1`; `B`: the block; `p`: the proposer.

 -/
theorem lem22a_proposer_holds_own_proposal (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s i : ℕ) (B : Block V) (p : V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    -- `p`'s tick at the start of slot `s + 1` is the step `i`, and put `B` on the wire
    (hl : x.lbl i = AtomicAction.tickAllAwake (slotStart S (s + 1)))
    (hsent : (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
      x[i + 1].sent - x[i].sent)
    -- the root of `B` is new to `p`
    (hRootNew : ∀ B' ∈ (stateBefore x (slotStart S (s + 1)) p).S.T, B'.root ≠ B.root)
    -- `p` holds `B`'s parent, and its finalized block is compatible with `B`
    (hParentHeld : B.parent ∈ (stateBefore x (slotStart S (s + 1)) p).S.T)
    (hF : (stateBefore x (slotStart S (s + 1)) p).S.F.compatible B = true) :
    B ∈ (x[i + 1][p].st).S.T := by
  -- step 0: the times; the slot of `t₁` is `s + 1`, the slot of `t₁ − 1` is `s`
  have hΔ := one_le_Δ S
  have hss : slotStart S (s + 1) = slotStart S s + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hss' : slotStart S (s + 1 + 1) = slotStart S (s + 1) + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq S (s + 1), Nat.mul_add, Nat.mul_one]
  have hslot₁ : S.C.slot ((slotStart S (s + 1) : ℕ) : Int) = s + 1 :=
    slot_eq_of_mem S (le_refl _) (by omega)
  have hslot₀ : S.C.slot ((slotStart S (s + 1) - 1 : ℕ) : Int) = s :=
    slot_eq_of_mem S (by omega) (by omega)
  -- step 1: `p`'s tick at `t₁` answered and sent `B`
  obtain ⟨-, n', sent, hrun, hBs, hst, -⟩ := tick_send_step_outcome hl hsent
  have hi : stepBefore x (slotStart S (s + 1)) = i := stepBefore_eq_of_lbl x hl
  -- the finalized block is `B`, an ancestor of `B`, or a descendant of `B`
  rcases (compatible_iff _ _).1 hF with hF | hBF
  rotate_left
  · -- `B` is an ancestor of `p`'s finalized block: `p`'s tree already holds it, and the tree only
    -- grows
    have hFT : (stateBefore x (slotStart S (s + 1)) p).S.F ∈
        (stateBefore x (slotStart S (s + 1)) p).S.T :=
      (lem11_node_invariant S Sched x (stepBefore x (slotStart S (s + 1))) p).1.2.2.2.1
    have hBT : B ∈ (stateBefore x (slotStart S (s + 1)) p).S.T :=
      ancestors_mem_T_of_exec S Sched x _ p _ B hFT hBF
    unfold stateBefore at hBT
    rw [hi] at hBT
    exact mem_T_mono x p (Nat.le_succ i) hBT
  -- step 2: the tick's input state has `p`'s FG state and AC state before `t₁`
  have hS : (tickInputState x i (slotStart S (s + 1)) p).S =
      (stateBefore x (slotStart S (s + 1)) p).S := by
    rw [(tickInputState_frame x i _ p).1]
    unfold stateBefore
    rw [hi]
  have hA : (tickInputState x i (slotStart S (s + 1)) p).A = (x[i][p].st).A :=
    (tickInputState_frame x i _ p).2.1
  -- step 3: the parent's slot is at most `s`, the slot of `t₁ − 1`
  have hps : B.parent.slot < S.C.slot ((slotStart S (s + 1) : ℕ) : Int) := by
    have h := slot_lt_of_mem_T_before S Sched x hDiv hMono (slotStart S (s + 1)) p B.parent
      (by omega) hParentHeld
    rw [hslot₀] at h
    rw [hslot₁]
    exact Nat.lt_succ_of_le h
  -- step 4: the routine level: `B` is in the tree the tick leaves
  have hmem : B ∈ n'.S.T := by
    refine GoldilocksCorrectness.Proofs.Routines.tick_proposal_mem_T S.C S.P S.X _ n' _ sent B
      hrun hBs ?_ ?_ ?_ ?_ ?_ hps
    · intro vote hvote
      rw [hA] at hvote
      exact (lem11_node_invariant S Sched x i p).1.1 _ vote hvote
    · rw [hS]; exact hRootNew
    · -- the attestations of `p`'s pool are well formed: the node invariant
      rw [hS]
      exact (lem11_node_invariant S Sched x (stepBefore x (slotStart S (s + 1))) p).1.2.2.2.2.2.2.2.2.2.2
    · rw [hS]; exact hParentHeld
    · rw [hS]; exact hF
  -- step 5: the tree the tick leaves is `x[i + 1][p].st`'s
  rw [hst]
  exact hmem

/-- **Lemma 22, an honest proposal reaches the next slot's voter.** The proof; the audited
statement is in `Statements/Executions/ProposalPropagationStatements.lean`.

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution; `GST`: the time from which the
  network is synchronous; `s`: the slot before the proposal's;
- `i`: the step of `p`'s tick at the start of slot `s + 1`; `B`: the block; `p`: the proposer;
  `w`: the voter of slot `s + 1`.

Roots name blocks until `voteTime S (s + 1)`: `mem_T_before_of_send`'s bound at the start of
slot `s + 1`, one delay after it. -/
theorem lem22_proposal_held_by_voter (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s i : ℕ) (B : Block V) (p w : V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (voteTime S (s + 1)))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hGST : GST ≤ voteTime S s)
    (hp : p ∉ Sched.adv (slotStart S (s + 1) : Int))
    (hw : ∀ t : ℕ, slotStart S (s + 1) ≤ t → t ≤ voteTime S (s + 1) →
      w ∈ Sched.awake (t : Int) ∧ w ∉ Sched.adv (t : Int))
    -- `p`'s tick at the start of slot `s + 1` is the step `i`, put `B` on the wire, and left
    -- `p` holding `B`
    (hl : x.lbl i = AtomicAction.tickAllAwake (slotStart S (s + 1)))
    (hsent : (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
      x[i + 1].sent - x[i].sent)
    (hBp : B ∈ (x[i + 1][p].st).S.T)
    -- `w`'s finalized block before its vote is compatible with `B`
    (hF : (stateBefore x (voteTime S (s + 1)) w).S.F.compatible B = true) :
    B ∈ (stateBefore x (voteTime S (s + 1)) w).S.T := by
  -- step 0: the times
  have hv₃ : voteTime S (s + 1) = slotStart S (s + 1) + Δ S := voteTime_eq S (s + 1)
  have hv₁ : voteTime S s ≤ slotStart S (s + 1) := by
    rw [voteTime_eq, slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
    have := one_le_Δ S
    omega
  obtain ⟨hti, hti'⟩ := time_of_lbl_tickAllAwake x hl
  -- step 1: `p` is honest at the end of its tick
  have huh : p ∉ Sched.adv (x[i + 1].time : Int) := by
    rw [hti']
    exact hp
  -- step 2: the propagation from `p`'s send, at `t := t₁`
  rw [hv₃] at hF hw ⊢
  exact mem_T_before_of_send S Sched x hDiv hMono GST hSync hCatch hRoots hParent i
    (slotStart S (s + 1)) p w B hsent hBp huh (by omega) (by omega) hw hF (by omega)

end GoldilocksCorrectness.Proofs.Executions
