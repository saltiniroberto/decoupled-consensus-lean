module
public import GoldilocksCorrectness.Statements.Executions.HealedCachesDefs
public import GoldilocksCorrectness.Statements.Executions.HealedAttestationStatements
public import GoldilocksCorrectness.Statements.Routines.CertificateStatements
public import GoldilocksCorrectness.Statements.Executions.InvariantStatements
public import GoldilocksCorrectness.Statements.Routines.AttestationStatements
public import GoldilocksCorrectness.Proofs.Executions.FinalizedFromChain
public import GoldilocksCorrectness.Proofs.Executions.HeightInvariant
public import GoldilocksCorrectness.Proofs.Executions.LockSteps
public import GoldilocksCorrectness.Proofs.Executions.PhaseFrame
public import GoldilocksCorrectness.Proofs.Executions.Clock
public import GoldilocksCorrectness.Proofs.Executions.Invariants
public import GoldilocksCorrectness.Proofs.Routines.Lemma77
public import GoldilocksCorrectness.Proofs.Routines.WalkEnd
public import GoldilocksCorrectness.Proofs.Routines.ChainStateOf
public import GoldilocksCorrectness.Proofs.Routines.FGCaches
public import GoldilocksCorrectness.Proofs.Routines.ConfirmationSupporters
public import GoldilocksCorrectness.Proofs.Routines.Node
public import GoldilocksCorrectness.Proofs.Routines.Wiring

@[expose] public section

/-!
# Lemma 84: the finality caches stay on the honest chain

The proofs of `H_of_h_max` and `lem84_caches_stay_on_chain`, stated in
`GoldilocksCorrectness/Statements/Executions/HealedCachesStatements.lean`, and the kit facts they
use.


-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (supportCutoff)

open GoldilocksCorrectness.Proofs.Routines (DREBPost DREBPost.bind DREBPost.bind_any DREBPost.dite
  DREBPost.ite DREBPost.of_outcome DREBPost.pure JustifiedOnChainWith forIn_yield_inv)
open GoldilocksCorrectness.Statements.Routines (IsEntry chainStateOf)

open GoldilocksCorrectness.Proofs.Routines (CachesOnChainWith fg_on_block_cachesOnChainWith
  fg_on_block_eq mem_fg_to_ac_tree)
open GoldilocksCorrectness.Statements.Routines (ChainStatesComputed)

open GoldilocksCorrectness.Proofs.Routines (update_confirmation_saved_mem)

open GoldilocksCorrectness.Proofs.Routines (CachesFrom cachesFrom_of_frame cachesFrom_refl
  cachesFrom_trans on_attestation_caches on_block_cachesFrom tick_cachesFrom)

open GoldilocksCorrectness.Proofs.Routines (acState_initial_eq fg_to_ac_F initial_eq)

open GoldilocksCorrectness.Proofs.Routines (reaction_tick_cachesFrom receive_cachesFrom)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicAction AtomicExec Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (lem66_chain_state_certified)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-! ## The caches over an abstract set of blocks -/

section Caches

end Caches

/-! ## The honest chain lies in honest trees -/

section HonestTrees

/-- **Kit fact, saved confirmations are in the tree.** At every step of every execution, every
confirmation a validator's AC state holds saved for a slot is a block of its FG state's tree.

Why: the saved confirmations are `none` initially; a step that changes one is the validator's
confirmation update, which saves its frame's finalized block or a block of its frame's tree, both
in the tree; and the tree only grows.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `i`: the step; `v`: the validator;
  `s`: the slot; `C'`: the saved block. -/
theorem saved_confirmation_mem_T_of_exec (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (i : ℕ) (v : V) (s : ℕ) (C' : Block V)
    -- `v`'s node state after `i` steps has `C'` saved as the confirmation of slot `s`
    (hC' : (x[i][v].st).A.saved_confirmation s = some C') :
    C' ∈ (x[i][v].st).S.T := by
  induction i generalizing s C' with
  | zero =>
      rw [getElem_zero_st x v, initial_eq, acState_initial_eq] at hC'
      cases hC'
  | succ i ih =>
      have hTs := mem_T_mono x v (Nat.le_succ i)
      by_cases hne : (x[i + 1][v].st).A.saved_confirmation s =
          (x[i][v].st).A.saved_confirmation s
      · rw [hne] at hC'
        exact hTs (ih s C' hC')
      · obtain ⟨-, -, -, A'', hA'', hsv⟩ := step_saved_changed x i v s hne
        rw [hsv] at hC'
        have h := update_confirmation_saved_mem S.C S.P _ A'' _ _ (s + 1) (Nat.le_add_left 1 s)
          hA'' C' (by rw [Nat.add_sub_cancel]; exact hC')
        refine hTs ?_
        rcases h with h | h
        · rw [h, fg_to_ac_F]
          exact (lem11_node_invariant S Sched x i v).1.2.2.2.1
        · exact ((mem_fg_to_ac_tree _ _).1 h).1

open Classical in
/-- The step `stepBefore x (t + 1)` is at a time at most `t`: it is the tick at `t + 1`, which
starts at `t`, or the first step, at the time `0`.

The variables:
- `x`: the execution; `t`: the time. -/
theorem time_stepBefore_succ_le {S : Setup V} {Sched : Schedule V}
    (x : AtomicExec (protocol S) Sched) (t : ℕ) : x[stepBefore x (t + 1)].time ≤ t := by
  unfold stepBefore
  split
  · rename_i h
    have := (time_of_lbl_tickAllAwake x (Nat.find_spec h)).1
    omega
  · have h0 : x[0].time = 0 := x.init.1
    omega

/-- **Kit fact, the honest chain lies in honest trees.** Under monotone corruption, every block on
the honest chain from slot `s₀` is held, at some step, by a validator outside the adversary set
at that step's time.

Why: a block on the honest chain at slot `s` is the confirmation an updater `u` of slot `s` holds
saved right after the support cutoff of slot `s + 1`, or an ancestor of it; that confirmation is
in `u`'s tree (`saved_confirmation_mem_T_of_exec`), so is the block, and `u` is honest at that
cutoff, so at the earlier time of the step read.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the first slot of the honest
  chain; `B`: the block. -/
theorem onHonestChain_inHonestTree (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ : ℕ) (hMono : Sched.MonotoneCorruption)
    (B : Block V)
    -- `B` is on the honest chain from slot `s₀`
    (hB : OnHonestChain S Sched x s₀ B) :
    inHonestTree x B := by
  obtain ⟨s, -, u, hu, C', hC', hBC⟩ := hB
  have hu' := (Finset.mem_sdiff.1 hu).2
  refine ⟨stepBefore x (supportCutoff S (s + 1) + 1), u, ?_, ?_⟩
  · intro hadv
    exact hu' (hMono _ _ (Int.ofNat_le.2 (time_stepBefore_succ_le x _)) hadv)
  · exact ancestors_mem_T_of_exec S Sched x _ u C' B
      (saved_confirmation_mem_T_of_exec S Sched x _ u s C' hC') hBC

/-- **Kit fact, a block on the honest chain at slot `s` is held by `supportCutoff S (s + 1)`.**
Under monotone corruption, a block on the honest chain at slot `s` is in the tree of an honest
validator at a step whose time is at most `supportCutoff S (s + 1)`, so at most any `t` at least
that cutoff. It is `onHonestChain_inHonestTree` with the slot kept and the step's time bounded.

Why: `onHonestChain_inHonestTree`'s step, `stepBefore x (supportCutoff S (s + 1) + 1)`, is at a
time at most the cutoff (`time_stepBefore_succ_le`). This is the step the three places of kind 4
(`justifiedOnChainWith_of_exec`, `lem85_honest_finalized_on_chain`, `caches_at_handover_of_held`)
need once their honest-chain block comes with its slot.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the first slot of the honest
  chain; `s`: the slot of the block; `t`: the bound on the time; `E`: the block.

Read aloud: the honest chain's block of slot `s` is in an honest tree by the update of slot `s`. -/
theorem onHonestChainAt_inHonestTreeBy (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (hMono : Sched.MonotoneCorruption) (s₀ s t : ℕ)
    (E : Block V)
    -- `E` is on the honest chain at slot `s`, from slot `s₀`
    (hE : OnHonestChainAt S Sched x s₀ s E)
    -- the bound is at least the support cutoff of slot `s + 1`
    (ht : supportCutoff S (s + 1) ≤ t) :
    inHonestTreeBy x t E := by
  obtain ⟨-, u, hu, C', hC', hEC⟩ := hE
  have hu' := (Finset.mem_sdiff.1 hu).2
  refine ⟨stepBefore x (supportCutoff S (s + 1) + 1), u, ?_, ?_, ?_⟩
  · intro hadv
    exact hu' (hMono _ _ (Int.ofNat_le.2 (time_stepBefore_succ_le x _)) hadv)
  · exact le_trans (time_stepBefore_succ_le x _) ht
  · exact ancestors_mem_T_of_exec S Sched x _ u C' E
      (saved_confirmation_mem_T_of_exec S Sched x _ u s C' hC') hEC

/-- **Kit fact, the justifications of an honest validator's blocks.** Under unforgeability, roots
naming blocks among what honest validators hold and monotone corruption, take `v` honest after `j`
steps, fewer than a quorum of validators in the adversary set up to that time, every honest
attestation sent at or after `t₀` naming the honest chain's entry at its height, and every one sent
before `t₀` at a height at most `H`: then for every block `B` that `v` holds after `j` steps, when
the justification height of `B`'s chain state is greater than `H`, its justified block is on the
honest chain from slot `s₀`, is an entry block, and has that justification height.

Why: the justified block has a justification certificate on `B`'s chain (Lemma 66), so its root is
that of an entry block `E` of the honest chain at that height (Lemma 83); both blocks are in honest
trees, so they are one block.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `t₀`: the time
  from which the honest attestations name the honest chain; `H`: the threshold; `j`: the step;
  `v`: the holder.

Roots name blocks until `x[j].time`: the proof compares the justified block, held after `j`
steps, with the entry of the honest chain at a slot `s_a` whose update ran by `x[j].time`
(Lemma 83). -/
theorem justifiedOnChainWith_of_exec (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ t₀ H j : ℕ) (v : V)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hRoots : RootsNameBlocksUntil S Sched x x[j].time)
    -- fewer than a quorum of validators have been in the adversary set up to the time after `j`
    -- steps
    (hAdvQ : AdversaryFewerThanQuorumUntil Sched (quorum V) (x[j].time : Int))
    -- every honest attestation sent at or after `t₀` names the honest chain's entry at its height
    (hAgree : HonestAttestationsOnChain S Sched x s₀ t₀)
    -- every honest attestation sent before `t₀` has height at most `H`
    (hOld : OldAttestationsAtMost S Sched x t₀ H)
    -- `v` is honest after `j` steps
    (hv : v ∉ Sched.adv (x[j].time : Int)) :
    ∀ B ∈ (x[j][v].st).S.T, JustifiedOnChainWith S.C H (OnHonestChain S Sched x s₀) B := by
  intro B hB hH
  obtain ⟨hcert, hJB, hJh⟩ := (lem66_chain_state_certified S.C B).1
    (Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le H) hH))
  obtain ⟨s_a, E, hcut, hE, hEnt, -, hroot⟩ :=
    GoldilocksCorrectness.Statements.Executions.lem83_one_justification_greater_than_threshold S
      Sched x s₀ t₀ H j v B _ _ hU hAdvQ hAgree
      (GoldilocksCorrectness.Statements.Executions.oldAttestationsAtMostHonestAt_of_oldAttestationsAtMost
        S Sched x t₀ _ H hOld) hB hcert hH
  have hJT := ancestors_mem_T_of_exec S Sched x j v B _ hB hJB
  have hEq : (chainStateOf S.C B).J = E := hRoots _ _ ⟨j, v, hv, le_rfl, hJT⟩
    (onHonestChainAt_inHonestTreeBy S Sched x hMono s₀ s_a _ E hE hcut) hroot
  exact ⟨hEq ▸ ⟨s_a, hE⟩, hEq ▸ hEnt, hJh⟩

end HonestTrees

/-! ## `H_of_h_max` -/

/-- **`H_of_h_max`, the proof.** The audited statement is in
`Statements/Executions/HealedCachesStatements.lean`.

Why: an attestation a tick at `t` sends has the chain-state height of a block of the sender's tree
(`tick_attestation_source`), at most the sender's `h_max` after the tick (Lemma 46), at a step
whose time is `t`, before `t₀`, at which the sender is honest.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t₀`: the time before which the
  attestations are read; `H`: the bound. -/
theorem H_of_h_max (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (t₀ H : ℕ)
    (hH : ∀ (i : ℕ) (v : V), x[i].time < t₀ → v ∉ Sched.adv (x[i].time : Int) →
      (x[i][v].st).S.h_max ≤ H) :
    OldAttestationsAtMost S Sched x t₀ H := by
  intro i t v a hl ht _ hHon hsent
  obtain ⟨D, hD, hDh⟩ := tick_attestation_source x hl hsent
  obtain ⟨-, ht1⟩ := time_of_lbl_tickAllAwake x hl
  have hD' := mem_T_mono x v (Nat.le_succ i) hD
  have hσ := (lem11_node_invariant S Sched x (i + 1) v).1.2.2.2.2.2.1 D hD'
  have hb := (lem46_finality_caches S Sched x (i + 1) v).2 D hD'
  rw [hσ, hDh] at hb
  rw [← ht1] at ht hHon
  exact hb.trans (hH (i + 1) v ht hHon)

/-! ## Lemma 84 -/

/-- **Lemma 84, the finality caches stay on the honest chain.** The proof; the audited statement
is in `Statements/Executions/HealedCachesStatements.lean`.

Why: by induction on the step from `i₁`. A validator honest at a step is honest at the step
before (monotone corruption), so its caches there are on the chain; the step keeps its state, or
runs its tick or a delivery to it, each relating the two states (`CachesFrom`), and every block of
its tree after the step has its justification on the honest chain when its height is greater than
`H` (`justifiedOnChainWith_of_exec`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `t₀`: the time
  from which the honest attestations name the honest chain; `H`: the threshold; `i₁`: the first
  step; `t`: the bound on the times of the steps.

Roots name blocks until `t`: the conclusion is for the steps at times at most `t`, and at each
such step `i + 1` the proof reads `justifiedOnChainWith_of_exec`, which takes blocks as held up to
`x[i + 1].time`. -/
theorem lem84_caches_stay_on_chain (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ t₀ H i₁ t : ℕ)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hRoots : RootsNameBlocksUntil S Sched x t)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hAgree : HonestAttestationsOnChain S Sched x s₀ t₀)
    (hOld : OldAttestationsAtMost S Sched x t₀ H)
    (hStart : ∀ v : V, v ∉ Sched.adv (x[i₁].time : Int) →
      CachesOnChain S Sched x s₀ H (x[i₁][v].st)) :
    ∀ (i : ℕ) (v : V), i₁ ≤ i → x[i].time ≤ t → v ∉ Sched.adv (x[i].time : Int) →
      CachesOnChain S Sched x s₀ H (x[i][v].st) := by
  intro i v hi
  induction i, hi using Nat.le_induction with
  | base => exact fun _ => hStart v
  | succ i hi ih =>
      intro ht hv
      have hv' : v ∉ Sched.adv (x[i].time : Int) := fun h =>
        hv (hMono _ _ (Int.ofNat_le.2 (time_le_succ x i)) h)
      have hC := ih (le_trans (time_le_succ x i) ht) hv'
      have hCS := (lem11_node_invariant S Sched x i v).1.2.2.2.2.2.1
      have hJ := justifiedOnChainWith_of_exec S Sched x s₀ t₀ H (i + 1) v hU hMono
        (hRoots.mono ht) (hAdvQ _) hAgree hOld hv
      have hrel : CachesFrom S.C H (OnHonestChain S Sched x s₀) (x[i][v].st)
          (x[i + 1][v].st) := by
        rcases step_cases x i v with h | ⟨t, n', sent, -, -, hok, h⟩ | ⟨sm, -, -, -, h⟩
        · rw [h]
          exact cachesFrom_refl _ _ _ _
        · rw [h]
          obtain ⟨hS, -, -⟩ := tickInputState_frame x i t v
          have h1 := reaction_tick_cachesFrom S H (OnHonestChain S Sched x s₀)
            (tickInputState x i t v) n' (t : Int) sent hok (by rw [hS]; exact hCS)
          exact cachesFrom_trans _ _ _ (cachesFrom_of_frame _ _ _ (congrArg FGState.T hS)
            (congrArg FGState.J hS) (congrArg FGState.h_j hS) (congrArg FGState.F hS)) h1
        · rw [h]
          exact receive_cachesFrom S.C S.P S.X H _ _ _ hCS
      exact hrel.2 hJ hC

end GoldilocksCorrectness.Proofs.Executions
