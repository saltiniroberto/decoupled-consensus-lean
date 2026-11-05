module
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.HealedCachesDefs
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.HealedAttestationStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.CertificateStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.InvariantStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.AttestationStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.FinalizedFromChain
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.HeightInvariant
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.LockSteps
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.PhaseFrame
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Clock
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Invariants
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ChainStateOf
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.FGCaches
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ConfirmationSupporters
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Node
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Wiring
public import GoldilocksCorrectness.Statements.Executions.HealedCachesDefs
public import GoldilocksCorrectness.Statements.Executions.HealedAttestationStatements
public import GoldilocksCorrectness.Statements.Routines.CertificateStatements
public import GoldilocksCorrectness.Statements.Executions.InvariantStatements
public import GoldilocksCorrectness.Statements.Routines.AttestationStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption

@[expose] public section

/-!
# Lemma84, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma84.lean`, over a model `M` whose facts
`F` hold, for an execution `x` of `protocolOf M S`: the saved confirmations are in the tree, the
honest chain lies in honest trees, the justifications of an honest validator's blocks are on the
honest chain, the bound on the old attestations from the greatest chain-state heights, and Lemma 84,
the finality caches stay on the honest chain. The page's routine-level theorems are the facts'
fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (supportCutoff)

open GoldilocksCorrectness.Proofs.Routines (DREBPost DREBPost.bind DREBPost.bind_any DREBPost.dite
  DREBPost.ite DREBPost.of_outcome DREBPost.pure forIn_yield_inv)

open GoldilocksCorrectness.Proofs.Routines (fg_on_block_cachesOnChainWith fg_on_block_eq)

open GoldilocksCorrectness.Proofs.Routines (CachesFrom cachesFrom_of_frame cachesFrom_refl
  cachesFrom_trans on_attestation_caches on_block_cachesFrom tick_cachesFrom)

open GoldilocksCorrectness.Proofs.Routines (acState_initial_eq initial_eq)

open GoldilocksCorrectness.Proofs.Routines (reaction_tick_cachesFrom receive_cachesFrom)

namespace GoldilocksCorrectness.Record.Proofs.Executions

open GoldilocksCorrectness.Record.Statements.Routines (hMax)

open GoldilocksCorrectness.Record.Proofs.Routines (JustifiedOnChainWith)

open GoldilocksCorrectness.Record.Statements.Routines (IsEntry JustificationCertOn)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_trans)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (Vocab.goldilocks)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-! ## The caches over an abstract set of blocks -/

section Caches

end Caches

/-! ## The honest chain lies in honest trees -/

section HonestTrees

/-- **Kit fact, saved confirmations are in the tree.** At every step of every execution, every
confirmation a validator's node state holds saved for a slot is a block of its tree.

Why: the saved confirmations are `none` initially; a step that changes one is the validator's
confirmation update, which saves its frame's finalized block or a block of its frame's tree, both
in the tree; and the tree only grows.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `i`: the step; `v`: the validator;
  `s`: the slot; `C'`: the saved block.

Read aloud: every confirmation a validator saved for a slot is a block of its tree. -/
theorem saved_confirmation_mem_T_of_exec (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (i : ℕ) (v : V) (s : ℕ) (C' : Block V)
    -- `v`'s node state after `i` steps has `C'` saved as the confirmation of slot `s`
    (hC' : (x.st i v).savedConfirmation s = some C') :
    C' ∈ (x.st i v).tree := by
  induction i generalizing s C' with
  | zero =>
      rw [(getElem_zero_st M F) x R v, F.init.initial_savedConfirmation] at hC'
      cases hC'
  | succ i ih =>
      have hTs := (mem_T_mono M F) x R E v (Nat.le_succ i)
      by_cases hne : (x.st (i + 1) v).savedConfirmation s =
          (x.st i v).savedConfirmation s
      · rw [hne] at hC'
        exact hTs (ih s C' hC')
      · obtain ⟨hl, -, -, hUpd⟩ := (step_saved_changed M F U) x R E i v s hne
        -- the update ran from the state at the tick's step
        rw [show x.tickInput v (M.supportCutoff S.C (s + 1)) = x.st i v by
          unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hl]] at hUpd
        have h := GoldilocksCorrectness.Record.Proofs.Routines.update_confirmation_saved_mem
          (Nat.le_add_left 1 s) hUpd C' (by rw [Nat.add_sub_cancel]; exact hC')
        refine hTs ?_
        rcases h with h | h
        · rw [h, (GoldilocksCorrectness.Record.Proofs.Routines.fg_to_ac_F M F)]
          exact (F.nd.nodeInv_finalized_mem_tree
            (lem11_node_invariant M F S A x R E i v (E.not_mem_corrupted_of_tick hl)).1)
        · exact (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 h).1

open Classical in
/-- The step `stepBefore M x (t + 1)` is at a time less than `t + 1` (`stepBefore_time`).

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `t`: the time.

Read aloud: the configuration `stepBefore x (t + 1)` is at a time less than `t + 1`. -/
theorem time_stepBefore_succ_le {S : Setup V} {A : Activity V}
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (t : ℕ) : x.time (x.stepBefore (t + 1)) < t + 1 := by
  have h0 : x.time 0 = 0 := R.time_zero
  have ht : (0 : ℝ) < (t : ℝ) + 1 := by positivity
  unfold Trace.stepBefore Trace.firstAt
  split_ifs with h
  · by_cases hz : Nat.find h = 0
    · rw [hz, Nat.zero_sub, h0]; exact ht
    · have hm := Nat.find_min h (show Nat.find h - 1 < Nat.find h by omega)
      exact (not_le.1 hm).trans_eq (Nat.cast_succ t)
  · rw [Nat.zero_sub, h0]; exact ht

/-- **Kit fact, the honest chain lies in honest trees.** Under monotone corruption, every block on
the honest chain from slot `s₀` is held, at some step, by a validator outside the adversary set
at that step's time.

Why: a block on the honest chain at slot `s` is the confirmation an updater `u` of slot `s` holds
saved right after the support cutoff of slot `s + 1`, or an ancestor of it; that confirmation is
in `u`'s tree (`saved_confirmation_mem_T_of_exec`), so is the block, and `u` is honest at that
cutoff, so at the earlier time of the step read.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the first slot of the honest
  chain; `B`: the block.

Read aloud: every block of the honest chain is held, at some step, by a validator honest at that
step. -/
theorem onHonestChain_inHonestTree (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ : ℕ) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (B : Block V)
    -- `B` is on the honest chain from slot `s₀`
    (hB : OnHonestChain M S A x s₀ B) :
    inHonestTree M A x B := by
  obtain ⟨s, -, u, hu, C', hC', hBC⟩ := hB
  -- `u`'s tick to the support cutoff of slot `s + 1`; the state it leaves has `C'` saved
  obtain ⟨k', hk', -⟩ := Activity.mem_activeThroughoutToTick.1 hu
  have hC'' : (x.st (k' + 1) u).savedConfirmation s = some C' := by
    have h := hC'
    unfold Trace.tickOutput at h
    rwa [(tickStep_eq_of_lbl M) x E hk'] at h
  -- the tick does not change the adversary set (, `corrupted_keep`)
  refine ⟨k' + 1, u, E.not_mem_corrupted_succ_of_tick hk', ?_⟩
  exact (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E _ u C' B
    ((saved_confirmation_mem_T_of_exec M F U) S A x R E _ u s C' hC'') hBC

/-- **Kit fact, a block a validator holds at its own tick is in an honest tree.** When step `k` is
`u`'s tick to `c` at a time at most `t`, and `u` holds `E` at that step, `E` is in the tree of a validator
honest at a step whose time is at most `t` (`inHonestTreeBy`): a tick is by a validator awake and honest
at its own step (`tick_active`).

The roots step of `cert_entry_at_slot`'s and `cert_entry_at_round_slot`'s callers names the attester and
its tick, not a slot's support cutoff: the member of `OnHonestChainAt` reads its saved
confirmation at its own tick, which under the clock-behind bound can be after any time bound
.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `k`: the step; `u`: the validator;
  `c`: its tick's clock value; `t`: the bound on the time; `E`: the block.

Read aloud: a block a validator holds when it ticks is in an honest tree by the time of that tick. -/
theorem onHonestChainAt_inHonestTreeBy (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (Env : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (k : ℕ) (u : V) (c : ℕ) (t : ℝ)
    (E : Block V)
    -- step `k` is `u`'s tick to `c`
    (hl : x.lbl k = Event.tick u c)
    -- at a time at most `t`
    (hk : x.time k ≤ t)
    -- `u` holds `E` at that step
    (hE : E ∈ (x.st k u).tree) :
    inHonestTreeBy M A x t E :=
  ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R Env (i := k) (v := u) (Env.not_mem_corrupted_of_tick hl) hk hE)

/-- **Kit fact, the certificate route with a general `t₀`.** Under unforgeability, take a block `Y`
that `w` holds after `j` steps and a justification certificate on the chain of `Y` at a height `h`
greater than `H` for `T`'s root; when fewer than a quorum of validators have been in the adversary set
up to the later of the time after `j` steps and `t₀`, every honest attestation sent at or after `t₀`
names the honest chain's entry at its height (`hAgree`), and every honest attestation sent before `t₀`
has height at most `H`: some honest attester `uₐ` ran the update of a slot `sₐ` at its own tick to
`M.supportCutoff S.C (sₐ + 1)`, a step before `j`; it is an updater of slot `sₐ`, outside the adversary
set after every step whose time is at most the time after `j` steps; and the entry block `E` of the
height `h` it held in the state its tick started from is on the honest chain at slot `sₐ`, with `T`'s
root.

Why: `cert_entry_at_slot`'s route; the slot `sₐ` is at least `s₀` by `hAgree` at the attester's send,
which asks the attester outside the adversary set up to its tick's clock value.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `t₀`: the time
  from which the honest attestations name the honest chain; `H`: the threshold; `j`: the step; `w`:
  the holder; `Y`: the held block; `T`: the justified block; `h`: its height.

Read aloud: a justification certificate above the threshold on a held chain names, by root, an entry
of the honest chain at a slot whose update an honest attester ran at a tick before `j`, holding the
entry when it ticked. -/
theorem cert_entry_held_of_agree (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ t₀ H j : ℕ) (w : V) (Y T : Block V) (h : Height)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max (x.time j) t₀))
    (hAgree : HonestAttestationsOnChain M S A x s₀ t₀)
    (hOld : OldAttestationsAtMostHonestAt M S A x t₀ t₀ H)
    (hY : Y ∈ (x.st j w).tree) (hJ : JustificationCertOn M Y h T) (hH : H < h) :
    ∃ (s_a : ℕ) (uₐ : V) (E : Block V), x.tickStep uₐ (M.supportCutoff S.C (s_a + 1)) < j ∧
      x.lbl (x.tickStep uₐ (M.supportCutoff S.C (s_a + 1))) = Event.tick uₐ (M.supportCutoff S.C (s_a + 1)) ∧
      uₐ ∈ updaterAt M S A x s_a ∧ uₐ ∉ A.corruptedAtTime x (x.time j) ∧
      E ∈ (x.tickInput uₐ (M.supportCutoff S.C (s_a + 1))).tree ∧
      OnHonestChainAt M S A x s₀ s_a E ∧ IsEntry M S.C E ∧ (M.chainStateOf S.C E).h = h ∧
      T.root = E.root := by
  obtain ⟨X₁, hX₁Y, Q, hqA, hQ⟩ := hJ
  rw [GoldilocksCorrectness.Record.quorumAt_eq_quorum Fx F.sched X₁] at hqA
  -- a member of the quorum outside the adversary set after every step whose time is at most the later
  -- of `x.time j` and `t₀`
  obtain ⟨u, hu, hhonM⟩ : ∃ u ∈ Q, A.HonestThroughTime x (max (x.time j) t₀) u := by
    by_contra hno
    have hall : ∀ v ∈ Q, ∃ i : ℕ, x.time i ≤ max (x.time j) t₀ ∧ v ∈ A.corrupted i := by
      intro v hv
      by_contra hn
      exact hno ⟨v, hv, fun i hi ha => hn ⟨i, hi, ha⟩⟩
    have h3 := hAdvQ Q hall
    omega
  have hhon : x.HonestThrough A j u :=
    fun i' hi' => hhonM i' (le_trans ((time_mono M) x R hi') (le_max_left _ _))
  -- its attestation of the certificate is in its record, and its tick sent it
  obtain ⟨a, hau, hah, haT, -, hon⟩ := hQ u hu
  have hrec : a.content ∈ (x.st j a.val_index).sentAttestations :=
    (GoldilocksCorrectness.Record.Statements.Executions.lem74_honest_attestations_recorded M F) S A x R E j w Y a hY
      ((GoldilocksCorrectness.Record.Proofs.Routines.on_chain_mono M F) a hX₁Y hon)
      (by rw [hau]; exact hhon)
  rw [hau] at hrec
  obtain ⟨j', t', a', hj', hl, -, hsent, -, hcont, -⟩ :=
    (record_content_sent_step M F) S A x R E u j _ hrec
  have hh' : a'.h = h := by
    rw [← hah]
    exact congrArg AttestationContent.h hcont
  have hT' : a'.T = T.root := by
    rw [← haT]
    exact congrArg AttestationContent.T hcont
  -- the tick ran the update of a slot `sₐ`; the attestation's source is a fast block of it, held at the tick
  obtain ⟨sₐ, source, C, ht, hv, -, hsT, hSaved, hsrcC, hh, hT⟩ :=
    (attest_tick_update_source M F U) S A x R j' t' u a' E hl hsent
  -- the tick is not before `t₀`: its height is greater than `H`
  have hge : t₀ ≤ t' := by
    by_contra hlt
    have hle := hOld j' t' u a' hl (by exact_mod_cast (Nat.lt_of_not_le hlt))
      (Activity.not_mem_corruptedAtTime.2 fun k hk => hhonM k (le_trans hk (le_max_right _ _))) hsent
    rw [hh'] at hle
    exact absurd hle (Nat.not_le.mpr hH)
  -- the slot is at least `s₀`: `hAgree` at the send, the attester outside the adversary set up to the real time
  -- of its tick's step `j' < j`
  have hs₀ : s₀ ≤ sₐ := by
    obtain ⟨s, -, hs, ht'', -⟩ := hAgree j' t' u a' hl hge
      (Activity.not_mem_corruptedAtTime.2 fun k hk =>
        hhonM k (le_trans hk (le_trans ((time_mono M) x R (Nat.le_of_lt hj')) (le_max_left _ _)))) hsent
    rw [ht] at ht''
    have h2 := (GoldilocksCorrectness.Record.Proofs.Routines.slot_lt_of_supportCutoff_le M.toSlotLayout F.sched) S (le_of_eq ht''.symm)
    omega
  subst ht
  -- the entry block of the source's height on its chain, held at the tick
  obtain ⟨hE1, hE2, hE3⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.isEntry_T_h M F) S.C source
  have hET : (M.chainStateOf S.C source).T_h ∈ (x.st j' u).tree :=
    (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E j' u
      source _ hsT hE3
  have hts := (tickStep_eq_of_lbl M) x E hl
  have hTI : (M.chainStateOf S.C source).T_h ∈
      (x.tickInput u (M.supportCutoff S.C (sₐ + 1))).tree := by
    unfold Trace.tickInput
    rw [hts]
    exact hET
  exact ⟨sₐ, u, (M.chainStateOf S.C source).T_h, by rw [hts]; exact hj', by rw [hts]; exact hl, hv,
    Activity.not_mem_corruptedAtTime.2 fun k hk => hhonM k (le_trans hk (le_max_left _ _)), hTI,
    ⟨hs₀, u, hv, C, hSaved, ancestorEq_trans hE3 hsrcC⟩, hE1, hE2.trans (hh.trans hh'),
    hT'.symm.trans hT⟩

/-- **Kit fact, the justifications of an honest validator's blocks.** Under unforgeability, roots
naming blocks among what honest validators hold and monotone corruption, take `v` honest after `j`
steps, fewer than a quorum of validators in the adversary set up to that time, every honest
attestation sent at or after `t₀` naming the honest chain's entry at its height, and every one sent
before `t₀` at a height at most `H`: then for every block `B` that `v` holds after `j` steps, when
the justification height of `B`'s chain state is greater than `H`, its justified block is on the
honest chain from slot `s₀`, is an entry block, and has that justification height.

Why: the justified block has a justification certificate on `B`'s chain (Lemma 66), so its root is
that of an entry block `E` of the honest chain at that height, which an honest attester held at its
own tick, a step before `j`; both blocks are in
honest trees, so they are one block.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `t₀`: the time
  from which the honest attestations name the honest chain; `H`: the threshold; `j`: the step;
  `v`: the holder.

Roots name blocks until `x[j].time`: the proof compares the justified block, held after `j`
steps, with the entry the attester held at its tick, a step before `j`.

Read aloud: every block an honest validator holds has its justification, when justified at a height
greater than `H`, on an entry block of the honest chain at that height. -/
theorem justifiedOnChainWith_of_exec (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ t₀ H j : ℕ) (v : V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hRoots : RootsNameBlocksUntil M A x (x.time j))
    -- fewer than a quorum of validators have been in the adversary set up to the later of `x.time j` and `t₀`
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max (x.time j) t₀))
    -- every honest attestation sent at or after `t₀` names the honest chain's entry at its height
    (hAgree : HonestAttestationsOnChain M S A x s₀ t₀)
    -- every attestation sent before `t₀` by a validator honest at `t₀` has height at most `H`
    (hOld : OldAttestationsAtMostHonestAt M S A x t₀ t₀ H)
    -- `v` is honest after `j` steps
    (hv : v ∉ A.corrupted j) :
    ∀ B ∈ (x.st j v).tree, JustifiedOnChainWith M S.C H (OnHonestChain M S A x s₀) B := by
  intro B hB hH
  obtain ⟨hcert, hJB, hJh⟩ := ((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) S.C B).1
    (Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le H) hH))
  obtain ⟨s_a, uₐ, Eb, hk, hl, -, -, hEb, hE, hEnt, -, hroot⟩ :=
    (cert_entry_held_of_agree M F U Fx) S A x R s₀ t₀ H j v B _ _ E hAdvQ hAgree hOld hB hcert hH
  have hJT := (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E j v B _ hB hJB
  -- the attester held the entry at its tick, a step before `j`: one root, so one block
  have hEq : (M.chainStateOf S.C B).J = Eb := hRoots _ _ ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := j) (v := v) hv le_rfl hJT)
    ((onHonestChainAt_inHonestTreeBy M F U) S A x R E _ uₐ (M.supportCutoff S.C (s_a + 1)) _ Eb hl
      ((time_mono M) x R hk.le) hEb) hroot
  exact ⟨hEq ▸ ⟨s_a, hE.1, hE.2⟩, hEq ▸ hEnt, hJh⟩

end HonestTrees

/-! ## `H_of_h_max` -/

/-- **`H_of_h_max`, the proof.** The audited statement is in
`Statements/Executions/HealedCachesStatements.lean`.

Why: an attestation a tick to `t` sends has the chain-state height of a block of the sender's tree
(`tick_attestation_source`), at most the sender's greatest chain-state height after the tick, which
`hH` bounds when `t < t₀` and the sender is honest up to `t₀`. The tick's real time is not read
.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t₀`: the time before which the
  attestations are read; `H`: the bound.

Read aloud: when every validator honest up to `t₀` has, right after each of its ticks to a clock value
less than `t₀`, its greatest chain-state height at most `H`, every attestation such a validator sent at a
tick to a clock value less than `t₀` has height at most `H`. -/
theorem H_of_h_max (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (t₀ H : ℕ)
    (hH : ∀ (i : ℕ) (v : V) (t : ℕ), x.lbl i = Event.tick v t → t < t₀ →
      v ∉ A.corruptedAtTime x t₀ → hMax M S.C (x.st (i + 1) v) ≤ H) :
    OldAttestationsAtMostHonestAt M S A x t₀ t₀ H := by
  intro i t v a hl ht hHonT hsent
  obtain ⟨D, hD, hDh⟩ := (tick_attestation_source M F) x R E hl hsent
  have hD' := (mem_T_mono M F) x R E v (Nat.le_succ i) hD
  have hb := GoldilocksCorrectness.Record.Statements.Routines.le_hMax M (C := S.C) hD'
  rw [hDh] at hb
  exact hb.trans (hH i v t hl (by exact_mod_cast ht) hHonT)

/-! ## Lemma 84 -/

/-- **Kit fact, Lemma 84's induction from one validator's own step.** From a step `i₁` at which the
caches of the validator `v` are on the honest chain, the caches of `v` are on the honest chain at every later
step `i` at a time at most `t` at which `v` is outside the adversary set. Lemma 84's induction reads the
starting caches of `v` only, so the starting step may be `v`'s own.

Why: by induction on the step from `i₁`: a validator honest at a step is honest at the step before
(monotone corruption), and the step keeps its caches on the chain.

The variables:
- as in `lem84_caches_stay_on_chain`; `v`: the validator.

Read aloud: once `v`'s caches are on the honest chain at some step, they stay there at every later step at
which `v` is honest, up to `t`. -/
theorem lem84_caches_stay_on_chain_from (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ t₀ H i₁ t : ℕ) (v : V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hRoots : RootsNameBlocksUntil M A x t)
    -- fewer than a quorum of validators have been in the adversary set up to the later of `t` and `t₀`
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max t t₀))
    (hAgree : HonestAttestationsOnChain M S A x s₀ t₀)
    (hOld : OldAttestationsAtMostHonestAt M S A x t₀ t₀ H)
    (hStart : CachesOnChain M S A x s₀ H (x.st i₁ v)) :
    ∀ i : ℕ, i₁ ≤ i → x.time i ≤ t → v ∉ A.corrupted i → CachesOnChain M S A x s₀ H (x.st i v) := by
  intro i hi
  induction i, hi using Nat.le_induction with
  | base => exact fun _ _ => hStart
  | succ i hi ih =>
      intro ht hv
      have hv' : v ∉ A.corrupted i := E.not_mem_corrupted_of_le (Nat.le_succ i) hv
      have hC := ih (le_trans ((time_le_succ M) x R i) ht) hv'
      have hI := (lem11_node_invariant M F S A x R E i v hv').1
      have hJ := (justifiedOnChainWith_of_exec M F U Fx) S A x R s₀ t₀ H (i + 1) v E
        ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) ht hRoots)
        (hAdvQ.mono (max_le_max_right _ ht)) hAgree hOld hv
      -- the step keeps the state, or runs the tick or a delivery (the fields `tick_cachesFrom`
      -- and `receive_cachesFrom`, from a node state satisfying the node invariant)
      rcases (step_cases M F) x R E i v with h | ⟨t, n', sent, hlt, -, hok, h, -⟩ | ⟨sm, -, -, h⟩ |
          ⟨⟨tR, keep, hlR⟩, -, h⟩
      · rw [h]
        exact hC
      · rw [h] at hJ ⊢
        -- the tick runs from the state at its step
        rw [show x.tickInput v t = x.st i v by
          unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hlt]] at hok
        exact (F.tk.tick_cachesFrom S.C S.P S.X H _ _ (t : Int) n' sent hok hI).2 hJ hC
      · rw [h] at hJ ⊢
        exact (F.rcv.receive_cachesFrom S.C S.P S.X H _ _ _ hI).2 hJ hC
      · -- a wake keeps the justification and the finalized block
        rw [h tR keep hlR]
        obtain ⟨-, -, -, hFin, hJus, hJh, -⟩ := F.wk.wake_readers (x.st i v) (tR : Int)
        unfold CachesOnChain at hC ⊢
        simp only [GoldilocksModel.N.finalized, GoldilocksModel.N.justified,
          GoldilocksModel.N.justifiedHeight] at hC ⊢
        rw [hFin, hJus, hJh]
        exact hC

/-- Lemma 84's induction, for one validator: from `i₁` on, the caches of a validator outside the adversary
set after every step whose time is that of `i₁`, and after the step `i`, are on the honest chain at `i`.

Why: by induction on the step from `i₁`, as Lemma 84's proof: at `i₁`, `hStart`; a validator honest at a step is honest
at the step before (monotone corruption), and the step keeps its caches on the chain.

The variables:
- as in `lem84_caches_stay_on_chain`.

Read aloud: a validator honest at the time of step `i₁` and at a later step `i` has its caches on the honest chain at
`i`. -/
theorem lem84_caches_stay_on_chain_of_honest (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ t₀ H i₁ t : ℕ)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hRoots : RootsNameBlocksUntil M A x t)
    -- fewer than a quorum of validators have been in the adversary set up to the later of `t` and `t₀`
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max t t₀))
    (hAgree : HonestAttestationsOnChain M S A x s₀ t₀)
    (hOld : OldAttestationsAtMostHonestAt M S A x t₀ t₀ H)
    (hStart : ∀ v : V, v ∉ A.corruptedAtTime x (x.time i₁) →
      CachesOnChain M S A x s₀ H (x.st i₁ v)) :
    ∀ (i : ℕ) (v : V), v ∉ A.corruptedAtTime x (x.time i₁) → i₁ ≤ i → x.time i ≤ t → v ∉ A.corrupted i →
      CachesOnChain M S A x s₀ H (x.st i v) := by
  intro i v hv₁ hi
  exact (lem84_caches_stay_on_chain_from M F U Fx) S A x R s₀ t₀ H i₁ t v E hRoots hAdvQ hAgree hOld
    (hStart v hv₁) i hi

/-- **Lemma 84, the finality caches stay on the honest chain.** The proof; the audited statement
is in `Statements/Executions/HealedCachesStatements.lean`.

Why: by induction on the step from `i₁`. A validator honest at a step is honest at the step
before (monotone corruption), so its caches there are on the chain; the step keeps its state, or
runs its tick or a delivery to it, each carrying the caches on the chain from a node state
satisfying the node invariant (the facts `tick_cachesFrom`, `receive_cachesFrom`) when every
block of its tree after the step has its justification on the honest chain when its height is
greater than `H` (`justifiedOnChainWith_of_exec`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `t₀`: the time
  from which the honest attestations name the honest chain; `H`: the threshold; `i₁`: the first
  step; `t`: the bound on the times of the steps.

Roots name blocks until `t`: the conclusion is for the steps at times at most `t`, and at each
such step `i + 1` the proof reads `justifiedOnChainWith_of_exec`, which takes blocks as held up to
`x[i + 1].time`.

Read aloud: when the caches of every validator honest at step `i₁` are on the honest chain with
`h_j > H`, so are those of every validator honest at any later step at a time at most `t`. -/
theorem lem84_caches_stay_on_chain (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ t₀ H i₁ t : ℕ)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hRoots : RootsNameBlocksUntil M A x t)
    -- fewer than a quorum of validators have been in the adversary set up to the later of `t` and `t₀`
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max t t₀))
    (hAgree : HonestAttestationsOnChain M S A x s₀ t₀)
    (hOld : OldAttestationsAtMostHonestAt M S A x t₀ t₀ H)
    (hStart : ∀ v : V, v ∉ A.corruptedAtTime x (x.time i₁) →
      CachesOnChain M S A x s₀ H (x.st i₁ v)) :
    ∀ (i : ℕ) (v : V), i₁ ≤ i → x.time i ≤ t → v ∉ A.corruptedAtTime x (x.time i) →
      CachesOnChain M S A x s₀ H (x.st i v) := by
  intro i v hi ht hv
  -- honest at the time of step `i` is honest at the time of the earlier step `i₁`: a step `k` at that
  -- time comes before `i` (corruption is permanent), or after it at the same time as `i`
  have hv₁ : v ∉ A.corruptedAtTime x (x.time i₁) :=
    Activity.not_mem_corruptedAtTime.2 fun k hk =>
      (Activity.not_mem_corruptedAtTime.1 hv) k (le_trans hk ((time_mono M) x R hi))
  exact (lem84_caches_stay_on_chain_of_honest M F U Fx) S A x R s₀ t₀ H i₁ t E hRoots hAdvQ hAgree hOld
    hStart i v hv₁ hi ht (Activity.not_mem_corruptedAtTime.1 hv i le_rfl)

end GoldilocksCorrectness.Record.Proofs.Executions

