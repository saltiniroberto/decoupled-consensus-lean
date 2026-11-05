module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma107
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.AsyncDeliveryBoundary
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89QuietJ
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma84
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma85
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.BlockPropagation
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.FinalityLivenessDefs
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ChainStateOfCertified
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.FGCaches
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.FGStateReaders
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Node
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Wiring
public import GoldilocksCorrectness.Proofs.Executions.Lemma107
public import GoldilocksCorrectness.Proofs.Executions.Lemma84
public import GoldilocksCorrectness.Proofs.Executions.Lemma85
public import GoldilocksCorrectness.Proofs.Executions.BlockPropagation
public import GoldilocksCorrectness.Statements.Executions.FinalityLivenessDefs
public import GoldilocksCorrectness.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Proofs.Routines.ChainStateOfCertified
public import GoldilocksCorrectness.Proofs.Routines.FGCaches
public import GoldilocksCorrectness.Proofs.Routines.FGState
public import GoldilocksCorrectness.Proofs.Routines.FGStateReaders
public import GoldilocksCorrectness.Proofs.Routines.Node
public import GoldilocksCorrectness.Proofs.Routines.NodeReach
public import GoldilocksCorrectness.Proofs.Routines.Wiring
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma97, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma97.lean`, over a model `M` whose facts
`F` hold, for an execution `x` of `protocolOf M S`: Lemma 97, a reader's finalized block after
healing, and its kit, namely a node state's reach along a step, the certified entry at a round's
slot, the justified block on the honest chain at a round, and a sent block held one delay later. The
page's routine-level theorems are the facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_succ_le_slotStart one_le_Δ
  slotStart_eq slotStart_le_of_le_slot slot_after_healed_round slot_eq_of_mem
  slot_lt_of_supportCutoff_le slot_mono slot_mono_int supportCutoff_eq supportCutoff_mono
  voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (DREBPost DREBPost.bind DREBPost.bind_any DREBPost.ite
  DREBPost.of_outcome DREBPost.pure compatible_of_ancestorEq_both)

open GoldilocksCorrectness.Proofs.Routines (fg_on_block_F fg_on_block_F_reaches fg_on_block_eq)

open GoldilocksCorrectness.Proofs.Routines (ReachFrom block_admissible_of mem_T_receive_block
  on_attestation_caches on_block_reachFrom reachFrom_frame_trans reachFrom_of_frame tick_reachFrom)

open GoldilocksCorrectness.Proofs.Routines (fgState_initial_eq initial_eq)

open GoldilocksCorrectness.Proofs.Routines (receive_reachFrom)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Proofs.Executions (mem_awakeThroughout_iff)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax IsEntry VoterTreeAt JustifiedInTree AnchorAt)

open GoldilocksCorrectness.Record.Proofs.Routines (ReadyFor)
open GoldilocksCorrectness.Record.Statements.Routines (ProgressCertOn)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (Vocab.goldilocks acObject)
open GoldilocksCorrectness.Statements.AbstractTrace.View (AwakeForDelayWithin)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  ancestorEq_compatible genesis_ancestorEq)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded in the goal and in every
hypothesis: `omega` does not see a fact stated at either. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

/-! ## Chain states -/

/-! ## The finality update reaches the block's finalized block -/

section Routines

end Routines

/-! ## Along a validator's steps -/

section Node

/-- Every step relates a validator's node state before it to its node state after it: the tree
is kept, the finalized block is kept or descends, and when `D` enters the tree from a node state
ready for `D` (`ReadyFor`), the new finalized block is the finalized block of `D`'s chain state or a
descendant of it (the landed `ReachFrom`, written out as the facts' `tick_reachFrom` and
`receive_reachFrom` state it).

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `D`: the block; `i`: the step; `v`: the validator.

Read aloud: every step relates a validator's node state before it to its node state after it. -/
theorem step_reachFrom {S : Setup V} {A : Activity V} (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (D : Block V) (i : ℕ) (v : V) :
    (x.st i v).tree ⊆ (x.st (i + 1) v).tree ∧
      (x.st i v).finalized.AncestorEq (x.st (i + 1) v).finalized ∧
      (D ∉ (x.st i v).tree → D ∈ (x.st (i + 1) v).tree → ReadyFor M S.C D (x.st i v) →
        (M.chainStateOf S.C D).F.AncestorEq (x.st (i + 1) v).finalized) := by
  rcases (step_cases M F) x R E i v with h | ⟨t, n', sent, hl, -, hok, h, -⟩ | ⟨sm, hlsm, -, h⟩ |
      ⟨⟨tRw, keepw, hlw⟩, -, h⟩
  · rw [h]
    exact ⟨Finset.Subset.refl _, ancestorEq_refl _, fun hD hD' => absurd hD' hD⟩
  · rw [h]
    -- the tick's input state is the node state or its wake, which keeps the node invariant, the
    -- tree, the finalized and justified blocks and the justification height (`F.wk.wake_readers`)
    have hIn : M.nodeInv S.C S.P S.X (x.tickInput v t) ∧
        (x.tickInput v t).tree = (x.st i v).tree ∧
        (x.tickInput v t).finalized = (x.st i v).finalized ∧
        (x.tickInput v t).justified = (x.st i v).justified ∧
        (x.tickInput v t).justifiedHeight = (x.st i v).justifiedHeight := by
      have hTIi : x.tickInput v t = x.st i v := by
        show x.st (x.tickStep v t) v = x.st i v
        rw [(tickStep_eq_of_lbl M) x E hl]
      rw [hTIi]
      exact ⟨(lem11_node_invariant M F S A x R E i v (E.not_mem_corrupted_of_tick hl)).1, rfl, rfl, rfl, rfl⟩
    obtain ⟨hI', hT, hFin, hJ, hJh⟩ := hIn
    obtain ⟨h1, h2, h3⟩ := F.tkAdded.tick_reachFrom S.C S.P S.X D _ (t : Int) n' sent hok hI'
    rw [hT] at h1 h3
    rw [hFin] at h2
    refine ⟨h1, h2, fun hD hD' hR => h3 hD hD' ?_⟩
    -- `ReadyFor` reads the tree, the justified block and the justification height only
    unfold ReadyFor GoldilocksCorrectness.Record.Statements.Routines.ChainStatesComputed
      GoldilocksCorrectness.Record.Statements.Routines.hMax at hR ⊢
    rw [hT, hJ, hJh]
    exact hR
  · rw [h]
    exact F.rcvAdded.receive_reachFrom S.C S.P S.X D _ _
      (lem11_node_invariant M F S A x R E i v
        (Activity.not_mem_corrupted_of_mem_active (E.deliver_active i v sm hlsm))).1
  · -- a wake keeps the tree and the finalized block
    rw [h tRw keepw hlw]
    obtain ⟨-, -, hT, hFin, -⟩ := F.wk.wake_readers (x.st i v) (tRw : Int)
    have eT : (M.wake (x.st i v) (tRw : Int)).tree = (x.st i v).tree := hT
    have eF : (M.wake (x.st i v) (tRw : Int)).finalized = (x.st i v).finalized := hFin
    rw [eT, eF]
    exact ⟨Finset.Subset.refl _, ancestorEq_refl _, fun hD hD' => absurd hD' hD⟩

/-- **Kit fact, the finalized block after `D` entered the tree.** When every step at which `D`
enters `v`'s tree, before step `j`, starts from an FG state `ReadyFor` `D`, and `v` holds `D` at
step `j`, `v`'s finalized block at step `j` is `D`'s finalized block or a descendant of it.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: once `D` is in `v`'s tree, `v`'s finalized block is `D`'s finalized block or a
descendant of it. -/
theorem F_reaches_of_mem {S : Setup V} {A : Activity V} (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (D : Block V) (v : V) (hDg : D ≠ Block.genesis) :
    ∀ j : ℕ, (∀ i : ℕ, i < j → D ∉ (x.st i v).tree → D ∈ (x.st (i + 1) v).tree →
        ReadyFor M S.C D (x.st i v)) →
      D ∈ (x.st j v).tree → (M.chainStateOf S.C D).F.AncestorEq (x.st j v).finalized := by
  intro j
  induction j with
  | zero =>
      intro _ hD
      rw [(getElem_zero_st M F) x R v, F.init.initial_tree] at hD
      exact absurd (Finset.mem_singleton.1 hD) hDg
  | succ j ih =>
      intro hR hD
      obtain ⟨-, hF, hacc⟩ := (step_reachFrom M F) x R E D j v
      by_cases hDj : D ∈ (x.st j v).tree
      · exact ancestorEq_trans (ih (fun i hi => hR i (Nat.lt_succ_of_lt hi)) hDj) hF
      · exact hacc hDj hD (hR j (Nat.lt_succ_self j) hDj hD)

end Node

/-! ## The honest chain at a round's first slot -/

section Rounds

/-- **Kit fact, the certificate route at a round's first slot.** `cert_entry_at_slot`, with the slot
`sₐ` of the attester's update the first slot `r' * S.C.R` of a round `r'`: the attester's tick is at the
action time of its round (`attest_time_round`), the support cutoff of that round's first slot's next
slot.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `H`: the
  bound on the old attestations' heights; `j`: the step; `w`: the holder; `Y`: the held block;
  `T`: the block the certificate names; `h`: its height.

Read aloud: a certificate higher than the threshold names an entry at a round's first slot, held by an
honest attester that ran that slot's update at a tick before `j`. -/
theorem cert_entry_at_round_slot (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ H j : ℕ) (w : V) (Y T : Block V) (h : Height)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V)
      (max (x.time j) (M.supportCutoff S.C (s₀ + 1))))
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hY : Y ∈ (x.st j w).tree) (hJ : ProgressCertOn M Y h T) (hH : H < h) :
    ∃ (s_a r' : ℕ) (uₐ : V) (E : Block V), s_a = r' * S.C.R ∧
      x.tickStep uₐ (M.supportCutoff S.C (s_a + 1)) < j ∧
      x.lbl (x.tickStep uₐ (M.supportCutoff S.C (s_a + 1))) = Event.tick uₐ (M.supportCutoff S.C (s_a + 1)) ∧
      uₐ ∈ updaterAt M S A x s_a ∧ uₐ ∉ A.corruptedAtTime x (x.time j) ∧
      E ∈ (x.tickInput uₐ (M.supportCutoff S.C (s_a + 1))).tree ∧
      OnHonestChainAt M S A x s₀ s_a E ∧ IsEntry M S.C E ∧ (M.chainStateOf S.C E).h = h ∧
      T.root = E.root := by
  obtain ⟨X₁, hX₁Y, Q, hqA, hQ⟩ := hJ
  rw [GoldilocksCorrectness.Record.quorumAt_eq_quorum Fx F.sched X₁] at hqA
  -- a member of the quorum outside the adversary set after every step whose time is at most the later
  -- of `x.time j` and the support cutoff of slot `s₀ + 1`
  obtain ⟨u, hu, hhonM⟩ : ∃ u ∈ Q, A.HonestThroughTime x (max (x.time j) (M.supportCutoff S.C (s₀ + 1))) u := by
    by_contra hno
    have hall : ∀ v ∈ Q, ∃ i : ℕ, x.time i ≤ max (x.time j) (M.supportCutoff S.C (s₀ + 1)) ∧ v ∈ A.corrupted i := by
      intro v hv
      by_contra hn
      exact hno ⟨v, hv, fun i hi ha => hn ⟨i, hi, ha⟩⟩
    have h3 := hAdvQ Q hall
    omega
  have hhon : x.HonestThrough A j u :=
    fun i' hi' => hhonM i' (le_trans ((time_mono M) x R hi') (le_max_left _ _))
  -- its attestation of the certificate is in its record, and its tick sent it
  obtain ⟨a, hau, hah, haT, hon⟩ := hQ u hu
  have hrec : a.content ∈ (x.st j a.val_index).sentAttestations :=
    (lem74_honest_attestations_recorded M F) S A x R E j w Y a hY
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
  -- the tick is not before the support cutoff of slot `s₀ + 1`: its height is greater than `H`
  have hge : M.supportCutoff S.C (s₀ + 1) ≤ t' := by
    by_contra hlt
    have hle := hOld j' t' u a' hl (by exact_mod_cast (Nat.lt_of_not_le hlt))
      (Activity.not_mem_corruptedAtTime.2 fun k hk => hhonM k (le_trans hk (le_max_right _ _))) hsent
    rw [hh'] at hle
    exact absurd hle (Nat.not_le.mpr hH)
  subst ht
  have hs₀ : s₀ ≤ sₐ := by
    by_contra hlt
    have := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_lt_of_lt M.toSlotLayout
      F.sched) S (show sₐ + 1 < s₀ + 1 by omega)
    omega
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
  -- the tick is at the action time of a round `r'`, the support cutoff of its first slot's next slot
  obtain ⟨r', hr'⟩ := (attest_time_round M F U) S A x R E hl hsent
  have hsa : sₐ = r' * S.C.R := by
    have h1 : M.supportCutoff S.C (sₐ + 1) = M.supportCutoff S.C (r' * S.C.R + 1) := hr'
    have h2 := (GoldilocksCorrectness.Record.Proofs.Routines.slot_lt_of_supportCutoff_le M.toSlotLayout F.sched) S (le_of_eq h1)
    have h3 := (GoldilocksCorrectness.Record.Proofs.Routines.slot_lt_of_supportCutoff_le M.toSlotLayout F.sched) S (le_of_eq h1.symm)
    omega
  exact ⟨sₐ, r', u, (M.chainStateOf S.C source).T_h, hsa, by rw [hts]; exact hj', by rw [hts]; exact hl, hv,
    Activity.not_mem_corruptedAtTime.2 fun k hk => hhonM k (le_trans hk (le_max_left _ _)), hTI,
    ⟨hs₀, u, hv, C, hSaved, ancestorEq_trans hE3 hsrcC⟩, hE1, hE2.trans (hh.trans hh'),
    hT'.symm.trans hT⟩

/-- **Kit fact, an honest justified block above the threshold is on the honest chain at a round's
first slot.** The justified block of `v`'s state after `i` steps, when its height is greater than `H`, is
on the honest chain at the first slot `r' * S.C.R` of a round `r'`, to whose support cutoff of the next
slot some validator ticked at a step before `i`.

Why: its justification certificate names the entry an honest attester held at its tick
(`cert_entry_at_round_slot`); both blocks are held by honest validators by the time of step `i`, with one
root, so they are one block.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `H`: the
  threshold; `i`: the step; `v`: the validator.

Read aloud: an honest justified block higher than the threshold is on the honest chain at a round's
first slot whose update ran at a tick before `i`. -/
theorem justified_onHonestChainAt_round (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ H i : ℕ) (v : V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hRoots : RootsNameBlocksUntil M A x (x.time i))
    -- fewer than a quorum of validators have been in the adversary set up to the later of `x.time i` and the hand-over cutoff
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max (x.time i) (M.supportCutoff S.C (s₀ + 1))))
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hv : v ∉ A.corrupted i)
    (hH : H < (x.st i v).justifiedHeight) :
    ∃ s_a r' : ℕ, s_a = r' * S.C.R ∧
      (∃ (k : ℕ) (u : V), k < i ∧ x.lbl k = Event.tick u (M.supportCutoff S.C (s_a + 1))) ∧
      OnHonestChainAt M S A x s₀ s_a (x.st i v).justified := by
  obtain ⟨⟨D, hD, hJD, hhjD⟩, -, -⟩ := (cachesWitnessed_of_exec M F) S A x R E i v
  have h1 : 1 ≤ (M.chainStateOf S.C D).h_j := by
    rw [← hhjD]; exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le H) hH)
  obtain ⟨hJC, -, -⟩ := ((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) S.C D).1 h1
  rw [← hJD, ← hhjD] at hJC
  obtain ⟨s_a, r', uₐ, Eb, hsa, hk, hl, -, -, hEb, hE, -, -, hroot⟩ := (cert_entry_at_round_slot M F U Fx) S A x R s₀ H i v
    D _ _ E (hAdvQ.mono le_rfl) hOld hD ((progressCertOn_of_justificationCertOn M F) hJC) hH
  have hJT : (x.st i v).justified ∈ (x.st i v).tree :=
    ((GoldilocksCorrectness.Record.Statements.Executions.lem57_justification_cache_and_record M F) S A x R E i v).2.2.1
  -- the attester held the entry at its tick, a step before `i`: one root, so one block
  have hEq : (x.st i v).justified = Eb := hRoots _ _ ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := i) (v := v) hv le_rfl hJT)
    ((onHonestChainAt_inHonestTreeBy M F U) S A x R E _ uₐ (M.supportCutoff S.C (s_a + 1)) _ Eb hl
      ((time_mono M) x R hk.le) hEb) hroot
  exact ⟨s_a, r', hsa, ⟨_, uₐ, hk, hl⟩, by rw [hEq]; exact hE⟩

end Rounds

/-! ## Propagation from an honest send -/

/-- A member of `honestActiveAt M S A x s` ticks to the support cutoff of slot `s + 1` at a step `kR` and is active
after every step from the first one whose time is `t₀` up to `kR`, when the protocol's duty window start of `s` is more
than `ΔClockBehind` before `t₀`.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `A`: the setup, the activity; `R`: the run's facts; `E`: the environment's facts; `s`: the slot; `t₀`: the
  window's start; `w`: the member.

Read aloud: an honest active validator of slot `s` is active from every later time up to its tick to the support
cutoff of `s + 1`, once that time is more than `ΔClockBehind` after the duty window's start. -/
theorem tick_window_of_honestActiveAt (S : Setup V) (A : Activity V) {x : Trace V (NamedObject V) M.N}
    (R : RunFacts M S x) {deadline} {release ΔRedeliver}
    {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {s t₀ : ℕ} {w : V} (hw : w ∈ honestActiveAt M S A x s)
    (ht₀ : ((duty_window_start S.C s : ℤ) : ℝ) + ΔClockBehind < t₀) :
    ∃ kR : ℕ, x.lbl kR = Event.tick w (M.supportCutoff S.C (s + 1)) ∧
      ∀ i : ℕ, t₀ ≤ x.time i → i ≤ kR → w ∈ A.active i :=
  (tick_window_of_activeThroughoutToTick_int M) x R E ((honestActiveAt_window M F) S A s w E hw) ht₀

/-- **Kit fact, the honest chain and an honest round opening slot's proposal.** Under the hypotheses of
`honest_proposal_holder_at` less its `hHoldC`, with the proposer's tick `ip` that sends `D`: `D` is of slot
`s_D` and not the genesis block; the proposer holds `D` after its tick; its finalized block at its tick is
an ancestor of `D`; an entry on the honest chain at a round's first slot `s_a`, to whose next support cutoff
some validator ticked by a support cutoff at most `T`, is compatible with `D`; and an honest validator's
justified and finalized blocks at a step after the hand-over, by a support cutoff at most `T`, are compatible
with `D`.

Why: `honest_proposal_extends_chain_until` (the chain before `s_D` extends `D`'s parent),
`round_chain_frame_after_healing` once the update of `s_D + 1` is at most `T` (`D` is saved at `s_D`),
`onHonestChainBefore_compatible`, `justified_onHonestChainAt_round`, `lem22a_proposer_holds_own_proposal`
with `D`'s parent a viable head of the proposer (`proposal_parent_viable_head`). A tick to the support
cutoff of `s_a + 1` at a real time at most the support cutoff of `c` is a tick of an earlier slot or the
same, since `ΔClockAhead < Δ S` and cutoffs are `4Δ` apart.

The variables:
- as `honest_proposal_holder_at`; `ip`: the proposer's tick to the start of `s_D`.

Read aloud: the proposal of an honest round opening slot after the hand-over is held by its proposer from its
tick, extends the honest chain, and is compatible with every honest justified or finalized block read by a
support cutoff at most `T`. -/
theorem honest_proposal_chain_kit (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ anchor i₂ H T r_D s_D : ℕ)
      (D : Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x T)
    (hRootsU : ∀ v ∈ updaterAt M S A x s_D, RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C (s_D + 1)))))
    (hParent : ParentHeldAtDelivery M x)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) T)
    (hAdvQU : ∀ v ∈ updaterAt M S A x s_D, A.AdversaryFewerThanQuorumUntil x (quorum V) (x.time (x.tickStep v (M.supportCutoff S.C (s_D + 1)))))
    (hSleepK : CommitteeSleepinessUntil M S A x anchor T) (hAnchor : anchor ≤ x.time i₂)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀) (ht₀ : M.supportCutoff S.C (s₀ + 1) ≤ x.time i₂)
    (hChain : ∀ σ : ℕ, M.supportCutoff S.C (σ + 1) ≤ T →
      ConfirmationsChainBefore M S A x s₀ (σ + 1))
    (hInv : ∀ s' : ℕ, s₀ < s' → M.supportCutoff S.C (s' + 1) ≤ T →
      ChainInvFor M S A x (honestActiveAt M S A x s')
        (OnHonestChainBefore M S A x s₀ s') s')
    (hLocks : ∀ s' : ℕ, s₀ < s' → M.supportCutoff S.C (s' + 1) ≤ T →
      ∀ w ∈ honestActiveAt M S A x s',
        LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ s') s' w)
    (hLocks₀ : ∀ w ∈ honestActiveAt M S A x s₀,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (s₀ + 1)) s₀ w)
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hCaches : ∀ (j' : ℕ) (w : V), x.time i₂ ≤ x.time j' → x.time j' ≤ T →
      w ∉ A.corrupted j' → CachesOnChain M S A x s₀ H (x.st j' w))
    (hCachesU : ∀ v ∈ updaterAt M S A x s_D, ∀ (j' : ℕ) (w : V), x.time i₂ ≤ x.time j' →
      x.time j' ≤ x.time (x.tickStep v (M.supportCutoff S.C (s_D + 1))) → w ∉ A.corrupted j' → CachesOnChain M S A x s₀ H (x.st j' w))
    (hsD : s_D = r_D * S.C.R) (hT : M.supportCutoff S.C s_D ≤ T)
    (hAfter : x.time i₂ < M.slotStart S.C s_D ∧
      ∀ k : ℕ, x.lbl k = Event.tick (S.P.proposer s_D) (M.slotStart S.C s_D) → x.time i₂ < x.time k)
    (hOpener : HonestOpenerAt M S A x s_D)
    (ip : ℕ) (hl : x.lbl ip = Event.tick (S.P.proposer s_D) (M.slotStart S.C s_D))
    (hsent : (⟨S.P.proposer s_D, NamedObject.block D⟩ : SignedMsg V (NamedObject V)) ∈
      x.sent (ip + 1) - x.sent ip)
    (hNoCol : ¬ RootCollisionAtProposal M S A x s_D D)
    (hHold : ∀ s' : ℕ, s_D - 1 ≤ s' → s' ≤ s_D → ∀ u ∈ honestActiveAt M S A x s', u ∈ S.P.committee s' →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hHoldP : S.P.proposer s_D ∈ A.activeThroughout x ((M.slotStart S.C s_D - max (Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s_D + 1) : ℕ) : ℝ) + Δs)) :
    D.slot = s_D ∧ D ≠ Block.genesis ∧ D ∈ (x.st (ip + 1) (S.P.proposer s_D)).tree ∧
      (x.st ip (S.P.proposer s_D)).finalized.AncestorEq D ∧
      (∀ (Eb : Block V) (s_a r' k' : ℕ) (u' : V) (c : ℕ), s_a = r' * S.C.R →
        x.lbl k' = Event.tick u' (M.supportCutoff S.C (s_a + 1)) → x.time k' ≤ M.supportCutoff S.C c →
        M.supportCutoff S.C c ≤ T → OnHonestChainAt M S A x s₀ s_a Eb → Eb.compatible D = true) ∧
      (∀ (u : V) (k c : ℕ), x.time i₂ ≤ x.time k → x.time k ≤ M.supportCutoff S.C c →
        M.supportCutoff S.C c ≤ T → u ∉ A.corrupted k →
        (x.st k u).justified.compatible D = true ∧ (x.st k u).finalized.compatible D = true) := by
  -- the preamble: the slot of `s_D`, the proposer's tick, the slot times as sums of one atom and multiples of `Δ S`
  obtain ⟨hs2, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.slot_after_healed_round M.toSlotLayout F.sched) S
    s₀ s_D (by exact_mod_cast lt_of_le_of_lt ht₀ hAfter.1)
  obtain ⟨q, rfl⟩ : ∃ q, s_D = q + 2 := ⟨s_D - 2, by omega⟩
  set p := S.P.proposer (q + 2) with hpdef
  have hipS : x.tickStep p (M.slotStart S.C (q + 2)) = ip := (tickStep_eq_of_lbl M) x E hl
  have hΔ := one_le_Δ S
  have hR := S.C.R_ge_two
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hNetR : (0 : ℝ) ≤ ΔNet := Nat.cast_nonneg _
  have hΔsR : (0 : ℝ) ≤ Δs := Nat.cast_nonneg _
  set L := max (Δ S) Δs with hLdef
  have hmx1 : Δ S ≤ L := le_max_left _ _
  have hmx2 : Δs ≤ L := le_max_right _ _
  have hLK : L + 3 * Δ S < 4 * Δ S * S.C.k := by
    have h : ((L + 3 * Δ S : ℕ) : ℝ) < ((4 * Δ S * S.C.k : ℕ) : ℝ) := by
      push_cast; rw [hLdef]; push_cast; linarith
    exact_mod_cast h
  have hsucc : ∀ s : ℕ, M.slotStart S.C (s + 1) = M.slotStart S.C s + 4 * Δ S := fun s => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U),
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s, Nat.mul_add, Nat.mul_one]
  have hcut : ∀ s : ℕ, M.supportCutoff S.C s = M.slotStart S.C s + 2 * Δ S := fun s => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U),
      (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U)]; omega
  have hvt : M.voteTime S.C (q + 2) = M.slotStart S.C (q + 2) + Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (q + 2)
  have hdw : ∀ s : ℕ, M.dutyWindowStart S.C s + 4 * Δ S * S.C.k = M.slotStart S.C s + Δ S ∨
      (M.dutyWindowStart S.C s = 0 ∧ M.slotStart S.C s + Δ S < 4 * Δ S * S.C.k) := fun s => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U)]
    exact (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_cases M.toSlotLayout F.sched U) S s
  have hsmono : ∀ {a b : ℕ}, a ≤ b → M.slotStart S.C a ≤ M.slotStart S.C b := fun h =>
    (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S h
  -- a support cutoff less than another plus `Δ S` is of an earlier slot or the same slot
  have hcutle : ∀ a b : ℕ, M.supportCutoff S.C a < M.supportCutoff S.C b + Δ S → a ≤ b := by
    intro a b h
    by_contra hn
    have h1 := hsmono (show b + 1 ≤ a by omega)
    have h2 := hsucc b
    rw [hcut a, hcut b] at h
    omega
  have hcutmono : ∀ {a b : ℕ}, a ≤ b → M.supportCutoff S.C a ≤ M.supportCutoff S.C b := fun {a b} h => by
    rw [hcut a, hcut b]; have := hsmono h; omega
  have hst := hsucc (q + 2)
  have hs₀cut : M.supportCutoff S.C (s₀ + 1) < M.slotStart S.C (q + 2) := by
    exact_mod_cast lt_of_le_of_lt ht₀ hAfter.1
  have hGSTst : GST + L ≤ M.slotStart S.C (q + 2) := by
    have := hcutmono (show s₀ ≤ s₀ + 1 by omega); omega
  have hst8 : 8 * Δ S ≤ M.slotStart S.C (q + 2) := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U)]
    have : 4 * Δ S * 2 ≤ 4 * Δ S * (q + 2) := Nat.mul_le_mul_left _ (by omega)
    omega
  have hcutT : ∀ s' : ℕ, s' ≤ q + 1 → M.supportCutoff S.C (s' + 1) ≤ T := fun s' hs' =>
    le_trans (hcutmono (by omega)) hT
  -- the proposer's tick: its real time, the time after it, its honesty up to the update of `s_D`
  have hipR := (E.tick_active ip p _ hl).2
  have hipT : x.time (ip + 1) = x.time ip := R.time_keep ip (by rw [hl]; exact nofun)
  have hi₂ip : x.time i₂ < x.time ip := hAfter.2 ip hl
  have hpH : p ∈ honestActiveAt M S A x (q + 2) := (opener_mem_honestActiveAt M F U) S A R E q hOpener
  have hpu : p ∈ updaterAt M S A x (q + 2) := (honestActiveAt_subset_updaterAt M F) S A x R E (q + 2) hpH
  have hpc : p ∉ A.corruptedAtTime x (M.supportCutoff S.C (q + 2 + 1)) :=
    (not_mem_corruptedAtTime_of_honestActiveAt M F) R E hpH le_rfl
  have hpw : ∀ k : ℕ, x.time k ≤ M.supportCutoff S.C (q + 2 + 1) → p ∉ A.corrupted k :=
    fun k hk => (not_mem_corrupted_of_le_time M) x R E hpc hk
  have hstR : ((M.slotStart S.C (q + 2) : ℕ) : ℝ) + 6 * Δ S = ((M.supportCutoff S.C (q + 2 + 1) : ℕ) : ℝ) := by
    rw [hcut (q + 2 + 1), hst]; push_cast; ring
  have hipcut : x.time ip ≤ M.supportCutoff S.C (q + 2 + 1) := by
    have := hipR.2; linarith
  -- the honest chain before `s_D` extends `D`'s parent, `D` is of slot `s_D` and not the genesis block
  -- (`honest_proposal_extends_chain_until`, its rows read up to `T`)
  have hkT : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.voteTime S.C (q + 2) →
      x.time k ≤ T := by
    intro k u c hk hc
    have h1 := (E.tick_active k u c hk).2.2
    have h2 : ((c : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (q + 2) : ℕ) : ℝ) := by
      rw [hcut (q + 2)]; exact_mod_cast (show c + Δ S ≤ M.slotStart S.C (q + 2) + 2 * Δ S by omega)
    have h3 : ((M.supportCutoff S.C (q + 2) : ℕ) : ℝ) ≤ T := by exact_mod_cast hT
    linarith
  have hHoldPs : p ∈ A.activeThroughout x ((M.slotStart S.C (q + 2) - L : ℕ) : ℝ)
      (((M.slotStart S.C (q + 2) - L : ℕ) : ℝ) + Δs) :=
    Activity.mem_activeThroughout_of_le le_rfl (by
      have : ((M.slotStart S.C (q + 2) - L : ℕ) : ℝ) ≤ ((M.supportCutoff S.C (q + 2 + 1) : ℕ) : ℝ) := by
        exact_mod_cast (show M.slotStart S.C (q + 2) - L ≤ M.supportCutoff S.C (q + 2 + 1) by
          rw [hcut]; have := hsmono (show q + 2 ≤ q + 2 + 1 by omega); omega)
      linarith) hHoldP
  have hLk := (locks_before_of_locks_le M F) S A x s₀ q
    (fun s' h₁ h₂ => hLocks s' h₁ (hcutT s' (by omega))) hLocks₀ (by omega)
  have hRootNew : ∀ B' ∈ (x.tickInput p (M.slotStart S.C (q + 2))).tree, B'.root ≠ D.root :=
    fun B' hB' h => hNoCol ⟨B', hB', h⟩
  obtain ⟨hChainD, hDslot, hDg, hparD, -, -⟩ := (honest_proposal_extends_chain_until M F U Fx) S A x R
    GST s₀ anchor i₂ H q ip D E hNet hSkew hRedeliver Sy hΔs
    (fun k u c hk hc => (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M)
      (hkT k u c hk hc) hRoots)
    hParent (fun k u c hk hc => hAdvQ.mono (hkT k u c hk hc))
    ((GoldilocksCorrectness.Record.Statements.Executions.CommitteeSleepinessUntil.mono M) hSleepK
      (le_trans (hcutmono (by omega)) hT)) hAnchor hGST (hChain q (hcutT q (by omega)))
    (fun s' h₁ h₂ => hInv s' h₁ (hcutT s' h₂)) (fun s' h₁ h₂ => hLocks s' h₁ (hcutT s' h₂)) hOld
    (fun k w c hk hc j u h₁ h₂ h₃ => hCaches j u ((time_mono M) x R h₁.le) (le_trans h₂ (hkT k w c hk hc)) h₃)
    ht₀ (by omega) hAfter.1 hi₂ip hLk (fun u hu hc => hHold (q + 1) (by omega) (by omega) u hu hc)
    ⟨hOpener.1, fun h => hOpener.2 (Finset.mem_union_left _ (Finset.mem_union_left _ h))⟩ hHoldPs hl hsent hRootNew
  -- `D` is on the honest chain at `s_D` once the update of `s_D + 1` is at most `T` (`round_chain_frame_after_healing`)
  have hDon : M.supportCutoff S.C (q + 2 + 1) ≤ T → OnHonestChainAt M S A x s₀ (q + 2) D := by
    intro hc
    obtain ⟨-, -, hSavedAll, -⟩ := (round_chain_frame_after_healing M F U Fx) S A x R GST s₀ anchor i₂ H (q + 2) D
      E hNet hSkew hRedeliver Sy hΔs hRootsU hParent hAdvQU
      ((GoldilocksCorrectness.Record.Statements.Executions.CommitteeSleepinessUntil.mono M) hSleepK hc) hAnchor hGST ht₀
      (hChain (q + 1) (hcutT (q + 1) le_rfl)) (fun s' h₁ h₂ => hInv s' h₁ (le_trans (hcutmono (by omega)) hc))
      (fun s' h₁ h₂ => hLocks s' h₁ (le_trans (hcutmono (by omega)) hc)) hLocks₀ hOld hCachesU hAfter hOpener
      ⟨ip, hl, hsent⟩ hNoCol hHold hHoldPs
    exact ⟨by omega, p, hpu, D, hSavedAll p hpu, ancestorEq_refl D⟩
  have hcompat : ∀ (Eb : Block V) (s_a r' : ℕ), s_a = r' * S.C.R →
      M.supportCutoff S.C (s_a + 1) ≤ T → OnHonestChainAt M S A x s₀ s_a Eb →
      Eb.compatible D = true := by
    intro Eb s_a r' hsa hc hE
    rcases Nat.lt_or_ge s_a (q + 2) with hlt | hge
    · have hrr : r' < r_D := by
        rw [hsa, hsD] at hlt
        exact Nat.lt_of_mul_lt_mul_right hlt
      have hm : (r' + 1) * S.C.R ≤ r_D * S.C.R := Nat.mul_le_mul_right _ hrr
      rw [Nat.succ_mul] at hm
      have hEp := hChainD Eb ⟨s_a, by omega, hE⟩
      exact (compatible_iff _ _).2 (Or.inl (ancestorEq_trans hEp hparD))
    · have hDc := hDon (le_trans (hcutmono (by omega)) hc)
      exact (onHonestChainBefore_compatible M F) S A x s₀ (s_a + 1) Eb D (hChain s_a hc)
        ⟨s_a, by omega, hE⟩ ⟨q + 2, by omega, hDc⟩
  -- an honest validator's justified and finalized blocks at a step after the hand-over and before a support cutoff
  -- at most `T` are compatible with `D`
  have hcompatT : ∀ (Eb : Block V) (s_a r' k' : ℕ) (u' : V) (c : ℕ), s_a = r' * S.C.R →
      x.lbl k' = Event.tick u' (M.supportCutoff S.C (s_a + 1)) → x.time k' ≤ M.supportCutoff S.C c →
      M.supportCutoff S.C c ≤ T → OnHonestChainAt M S A x s₀ s_a Eb → Eb.compatible D = true := by
    intro Eb s_a r' k' u' c hsa hlk' hk' hcT hE
    have h1 := (E.tick_active k' u' _ hlk').2.1
    have hsc : s_a + 1 ≤ c := hcutle _ _ (by
      have : ((M.supportCutoff S.C (s_a + 1) : ℕ) : ℝ) < ((M.supportCutoff S.C c + Δ S : ℕ) : ℝ) := by
        push_cast; linarith
      exact_mod_cast this)
    exact hcompat Eb s_a r' hsa (le_trans (hcutmono hsc) hcT) hE
  have hJcompatU : ∀ (u : V) (k c : ℕ), x.time i₂ ≤ x.time k → x.time k ≤ M.supportCutoff S.C c →
      M.supportCutoff S.C c ≤ T → u ∉ A.corrupted k → (x.st k u).justified.compatible D = true := by
    intro u k c hk1 hk2 hcT hvk
    have hcTR : ((M.supportCutoff S.C c : ℕ) : ℝ) ≤ T := by exact_mod_cast hcT
    have hkT' : x.time k ≤ T := by linarith
    have ht₀R : ((M.supportCutoff S.C (s₀ + 1) : ℕ) : ℝ) ≤ x.time i₂ := ht₀
    obtain ⟨s_a, r', hsa, ⟨k', u', hk'k, hlk'⟩, hJ⟩ := (justified_onHonestChainAt_round M F U Fx) S A x R s₀ H k u E
      ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) hkT' hRoots)
      (hAdvQ.mono (max_le hkT' (by linarith))) hOld hvk (hCaches k u hk1 hkT' hvk).1
    have h2 := (time_mono M) x R hk'k.le
    exact hcompatT _ s_a r' k' u' c hsa hlk' (le_trans h2 hk2) hcT hJ
  have hFcK : ∀ (u : V) (k c : ℕ), x.time i₂ ≤ x.time k → x.time k ≤ M.supportCutoff S.C c →
      M.supportCutoff S.C c ≤ T → u ∉ A.corrupted k → (x.st k u).finalized.compatible D = true := by
    intro u k c hk1 hk2 hcT hvk
    have hcTR : ((M.supportCutoff S.C c : ℕ) : ℝ) ≤ T := by exact_mod_cast hcT
    have hkT' : x.time k ≤ T := by linarith
    exact compatible_of_ancestorEq_both (hCaches k u hk1 hkT' hvk).2.2.2.2 (ancestorEq_refl D)
      (hJcompatU u k c hk1 hk2 hcT hvk)
  -- the proposer holds `D` from its tick; its finalized block at its tick is an ancestor of `D`
  have hpk : p ∉ A.corrupted (x.tickStep p (M.slotStart S.C (q + 2))) := by
    rw [hipS]; exact E.not_mem_corrupted_of_tick hl
  have hInvP := (lem11_node_invariant M F S A x R E _ p hpk).1
  have hPV := (proposal_parent_viable_head M F U) S A x R E (q + 1) D p ⟨ip, hl, hsent⟩
  have hPV' := ((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_heads_iff M F) S.C S.P S.X _ hInvP _).1 hPV
  have hFinP : (x.tickInput p (M.slotStart S.C (q + 2))).finalized.AncestorEq D := ancestorEq_trans hPV'.2.1 hparD
  have hDp : D ∈ (x.st (ip + 1) p).tree :=
    (GoldilocksCorrectness.Record.Statements.Executions.lem22a_proposer_holds_own_proposal M F U) S A x R
      (q + 1) ip D p E hl hsent hRootNew hPV'.1 ((compatible_iff _ _).2 (Or.inl hFinP))
  have hFip : (x.st ip p).finalized.AncestorEq D := by
    have h := hFinP
    unfold Trace.tickInput at h
    rwa [hipS] at h
  exact ⟨hDslot, hDg, hDp, hFip, hcompatT, fun u k c h1 h2 h3 h4 =>
    ⟨hJcompatU u k c h1 h2 h3 h4, hFcK u k c h1 h2 h3 h4⟩⟩

/-- **Kit fact, a holder of an honest round opening slot's proposal at every time after its
send.** Under the hypotheses of Lemma 97 less the reader's: at every natural time `τ` at or after the
real time of the proposer's tick to the start of `s_D` such that some support cutoff lies in `[τ, T]` (some slot `s'` with
`τ ≤ M.supportCutoff S.C s' ≤ T`), some validator holds `D` at a step `kU` at or before `τ` where it
is outside the adversary set, is active at every step whose real time is in `[τ, τ + Δs]`, and has,
at its last step before `τ`, a finalized block compatible with `D`.

Why: by strong induction on `τ`. Up to the support cutoff of slot `s_D + 1`, the proposer of `s_D`
holds `D` from its tick (`lem22a_proposer_holds_own_proposal`), at the step after it, whose real time is
the tick's (`time_keep`), and is an honest active validator of `s_D`. Later: an honest member `w` of the committee of the slot whose update is the
first support cutoff at or after `τ` ticks to `τ − Δ` (before `τ`, `hSkew`), and the block is in its
tree there by `block_at_tick_of_held_step_deadline`, from the holder the induction gives at
`τ − Δ − max (Δ S) Δs` when the proposer's tick is by then, and from the proposer at its tick otherwise
(its finalized block before that tick an ancestor of `D`). Later, a member `w` of `honestActiveAt M S A x σ'` (nonempty by
`committee_majority_of_sleepiness` from `hSleepK`), for `σ'` the slot whose update
`M.supportCutoff S.C (σ' + 1)` is the first support cutoff at or after `τ` (with `σ` the slot of
`τ`: `σ − 1` when `τ` is at or before the support cutoff of `σ`, `σ` otherwise), whose update is
so at most `T`, is active from `τ − max (Δ S) Δs` through `τ` (its duty window, `hΔs`), and holds
`D` before `τ`: by the sync fact from the holder the induction
gives at `τ − max (Δ S) Δs` (the holder read where it already holds `D`) when that time is after the
start of `s_D`, and by synchrony from the proposer's send
otherwise: the block is in `w`'s tree at its tick to a clock value at least one delay after the send
. The compatibility conjunct, for a validator honest at the step before `τ`, from
`hCaches` and the justified block on the honest chain (`justified_onHonestChainAt_round`), as in
Lemma 97's proof. The condition on `τ` keeps every
committee read at a slot whose update is at most `T`; Lemma 97 supplies it from its reader's step.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `A`, `x`: the setup, the activity, the execution; `R`: the run's facts; `GST`: the time
  from which the network is synchronous; `s₀`: the healed slot; `anchor`: the time from which
  committee sleepiness holds; `i₂`: the hand-over step; `H`: the threshold; `T`: the reading time;
- `r_D`, `s_D`: the round and its first slot; `D`: the proposal.

Read aloud: at every time after an honest round opening slot's proposal that is at or before some
support cutoff at most `T`, some validator holds the proposal by then while honest, stays active for
the sync delay after then, and has a finalized block compatible with it. -/
theorem honest_proposal_holder_at (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ anchor i₂ H T r_D s_D : ℕ)
      (D : Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x T)
    (hRootsU : ∀ v ∈ updaterAt M S A x s_D, RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C (s_D + 1)))))
    (hParent : ParentHeldAtDelivery M x)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) T)
    (hAdvQU : ∀ v ∈ updaterAt M S A x s_D, A.AdversaryFewerThanQuorumUntil x (quorum V) (x.time (x.tickStep v (M.supportCutoff S.C (s_D + 1)))))
    (hSleepK : CommitteeSleepinessUntil M S A x anchor T) (hAnchor : anchor ≤ x.time i₂)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀) (ht₀ : M.supportCutoff S.C (s₀ + 1) ≤ x.time i₂)
    (hChain : ∀ σ : ℕ, M.supportCutoff S.C (σ + 1) ≤ T →
      ConfirmationsChainBefore M S A x s₀ (σ + 1))
    (hInv : ∀ s' : ℕ, s₀ < s' → M.supportCutoff S.C (s' + 1) ≤ T →
      ChainInvFor M S A x (honestActiveAt M S A x s')
        (OnHonestChainBefore M S A x s₀ s') s')
    (hLocks : ∀ s' : ℕ, s₀ < s' → M.supportCutoff S.C (s' + 1) ≤ T →
      ∀ w ∈ honestActiveAt M S A x s',
        LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ s') s' w)
    (hLocks₀ : ∀ w ∈ honestActiveAt M S A x s₀,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (s₀ + 1)) s₀ w)
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hCaches : ∀ (j' : ℕ) (w : V), x.time i₂ ≤ x.time j' → x.time j' ≤ T →
      w ∉ A.corrupted j' → CachesOnChain M S A x s₀ H (x.st j' w))
    (hCachesU : ∀ v ∈ updaterAt M S A x s_D, ∀ (j' : ℕ) (w : V), x.time i₂ ≤ x.time j' →
      x.time j' ≤ x.time (x.tickStep v (M.supportCutoff S.C (s_D + 1))) → w ∉ A.corrupted j' → CachesOnChain M S A x s₀ H (x.st j' w))
    (hsD : s_D = r_D * S.C.R) (hT : M.supportCutoff S.C s_D ≤ T)
    (hAfter : x.time i₂ < M.slotStart S.C s_D ∧
      ∀ k : ℕ, x.lbl k = Event.tick (S.P.proposer s_D) (M.slotStart S.C s_D) → x.time i₂ < x.time k)
    (hOpener : HonestOpenerAt M S A x s_D)
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick (S.P.proposer s_D) (M.slotStart S.C s_D) ∧
      (⟨S.P.proposer s_D, NamedObject.block D⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i)
    (hNoCol : ¬ RootCollisionAtProposal M S A x s_D D)
    (hHold : ∀ s' : ℕ, s_D - 1 ≤ s' → s' ≤ s_D → ∀ u ∈ honestActiveAt M S A x s', u ∈ S.P.committee s' →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- every honest committee member of every slot after `s_D` whose update is at most `T` is active from its duty window's
    -- start through the sync delay after that update; the proposer of `s_D` from one delay or one sync delay before its
    -- slot's start through the sync delay after its slot's update
    (hHoldC : ∀ σ' : ℕ, s_D + 1 ≤ σ' → M.supportCutoff S.C (σ' + 1) ≤ T → ∀ u ∈ honestActiveAt M S A x σ',
      u ∈ S.P.committee σ' → u ∈ A.activeThroughout x ((M.dutyWindowStart S.C σ' : ℕ) : ℝ)
        (((M.supportCutoff S.C (σ' + 1) : ℕ) : ℝ) + Δs))
    (hHoldP : S.P.proposer s_D ∈ A.activeThroughout x ((M.slotStart S.C s_D - max (Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s_D + 1) : ℕ) : ℝ) + Δs)) :
    ∀ τ : ℕ, x.time (x.tickStep (S.P.proposer s_D) (M.slotStart S.C s_D)) ≤ τ →
      (∃ s' : ℕ, τ ≤ M.supportCutoff S.C s' ∧ M.supportCutoff S.C s' ≤ T) →
      ∃ (u : V) (kU : ℕ), x.time kU ≤ τ ∧ u ∉ A.corrupted kU ∧ D ∈ (x.st kU u).tree ∧
        u ∈ A.activeThroughout x τ (τ + Δs) ∧ (x.st (x.stepBefore τ) u).finalized.compatible D = true := by
  -- the preamble: the slot of `s_D`, the proposer's tick, the slot times as sums of one atom and multiples of `Δ S`
  obtain ⟨hs2, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.slot_after_healed_round M.toSlotLayout F.sched) S
    s₀ s_D (by exact_mod_cast lt_of_le_of_lt ht₀ hAfter.1)
  obtain ⟨q, rfl⟩ : ∃ q, s_D = q + 2 := ⟨s_D - 2, by omega⟩
  obtain ⟨ip, hl, hsent⟩ := hPropose
  set p := S.P.proposer (q + 2) with hpdef
  have hipS : x.tickStep p (M.slotStart S.C (q + 2)) = ip := (tickStep_eq_of_lbl M) x E hl
  have hΔ := one_le_Δ S
  have hR := S.C.R_ge_two
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hNetR : (0 : ℝ) ≤ ΔNet := Nat.cast_nonneg _
  have hΔsR : (0 : ℝ) ≤ Δs := Nat.cast_nonneg _
  set L := max (Δ S) Δs with hLdef
  have hmx1 : Δ S ≤ L := le_max_left _ _
  have hmx2 : Δs ≤ L := le_max_right _ _
  have hLK : L + 3 * Δ S < 4 * Δ S * S.C.k := by
    have h : ((L + 3 * Δ S : ℕ) : ℝ) < ((4 * Δ S * S.C.k : ℕ) : ℝ) := by
      push_cast; rw [hLdef]; push_cast; linarith
    exact_mod_cast h
  have hsucc : ∀ s : ℕ, M.slotStart S.C (s + 1) = M.slotStart S.C s + 4 * Δ S := fun s => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U),
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s, Nat.mul_add, Nat.mul_one]
  have hcut : ∀ s : ℕ, M.supportCutoff S.C s = M.slotStart S.C s + 2 * Δ S := fun s => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U),
      (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U)]; omega
  have hvt : M.voteTime S.C (q + 2) = M.slotStart S.C (q + 2) + Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (q + 2)
  have hdw : ∀ s : ℕ, M.dutyWindowStart S.C s + 4 * Δ S * S.C.k = M.slotStart S.C s + Δ S ∨
      (M.dutyWindowStart S.C s = 0 ∧ M.slotStart S.C s + Δ S < 4 * Δ S * S.C.k) := fun s => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U)]
    exact (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_cases M.toSlotLayout F.sched U) S s
  have hsmono : ∀ {a b : ℕ}, a ≤ b → M.slotStart S.C a ≤ M.slotStart S.C b := fun h =>
    (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S h
  -- a support cutoff less than another plus `Δ S` is of an earlier slot or the same slot
  have hcutle : ∀ a b : ℕ, M.supportCutoff S.C a < M.supportCutoff S.C b + Δ S → a ≤ b := by
    intro a b h
    by_contra hn
    have h1 := hsmono (show b + 1 ≤ a by omega)
    have h2 := hsucc b
    rw [hcut a, hcut b] at h
    omega
  have hcutmono : ∀ {a b : ℕ}, a ≤ b → M.supportCutoff S.C a ≤ M.supportCutoff S.C b := fun {a b} h => by
    rw [hcut a, hcut b]; have := hsmono h; omega
  have hst := hsucc (q + 2)
  have hs₀cut : M.supportCutoff S.C (s₀ + 1) < M.slotStart S.C (q + 2) := by
    exact_mod_cast lt_of_le_of_lt ht₀ hAfter.1
  have hGSTst : GST + L ≤ M.slotStart S.C (q + 2) := by
    have := hcutmono (show s₀ ≤ s₀ + 1 by omega); omega
  have hst8 : 8 * Δ S ≤ M.slotStart S.C (q + 2) := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U)]
    have : 4 * Δ S * 2 ≤ 4 * Δ S * (q + 2) := Nat.mul_le_mul_left _ (by omega)
    omega
  have hcutT : ∀ s' : ℕ, s' ≤ q + 1 → M.supportCutoff S.C (s' + 1) ≤ T := fun s' hs' =>
    le_trans (hcutmono (by omega)) hT
  -- the proposer's tick: its real time, the time after it, its honesty up to the update of `s_D`
  have hipR := (E.tick_active ip p _ hl).2
  have hipT : x.time (ip + 1) = x.time ip := R.time_keep ip (by rw [hl]; exact nofun)
  have hi₂ip : x.time i₂ < x.time ip := hAfter.2 ip hl
  have hpH : p ∈ honestActiveAt M S A x (q + 2) := (opener_mem_honestActiveAt M F U) S A R E q hOpener
  have hpu : p ∈ updaterAt M S A x (q + 2) := (honestActiveAt_subset_updaterAt M F) S A x R E (q + 2) hpH
  have hpc : p ∉ A.corruptedAtTime x (M.supportCutoff S.C (q + 2 + 1)) :=
    (not_mem_corruptedAtTime_of_honestActiveAt M F) R E hpH le_rfl
  have hpw : ∀ k : ℕ, x.time k ≤ M.supportCutoff S.C (q + 2 + 1) → p ∉ A.corrupted k :=
    fun k hk => (not_mem_corrupted_of_le_time M) x R E hpc hk
  have hstR : ((M.slotStart S.C (q + 2) : ℕ) : ℝ) + 6 * Δ S = ((M.supportCutoff S.C (q + 2 + 1) : ℕ) : ℝ) := by
    rw [hcut (q + 2 + 1), hst]; push_cast; ring
  have hipcut : x.time ip ≤ M.supportCutoff S.C (q + 2 + 1) := by
    have := hipR.2; linarith
  -- the honest chain before `s_D` extends `D`'s parent, `D` is of slot `s_D` and not the genesis block
  -- (`honest_proposal_extends_chain_until`, its rows read up to `T`)
  obtain ⟨hDslot, hDg, hDp, hFip, -, hJF⟩ := (honest_proposal_chain_kit M F U Fx) S A x R GST s₀ anchor i₂ H T r_D
    (q + 2) D E hNet hSkew hRedeliver Sy hΔs hRoots hRootsU hParent hAdvQ hAdvQU hSleepK hAnchor hGST ht₀ hChain hInv
    hLocks hLocks₀ hOld hCaches hCachesU hsD hT hAfter hOpener ip hl hsent hNoCol hHold hHoldP
  have hFcK : ∀ (u : V) (k c : ℕ), x.time i₂ ≤ x.time k → x.time k < M.supportCutoff S.C c →
      M.supportCutoff S.C c ≤ T → u ∉ A.corrupted k → (x.st k u).finalized.compatible D = true :=
    fun u k c h1 h2 h3 h4 => (hJF u k c h1 h2.le h3 h4).2
  -- the strong induction on `τ`
  intro τ
  induction τ using Nat.strong_induction_on with
  | _ τ ih =>
  intro hτ1 hτc
  rw [hipS] at hτ1
  obtain ⟨c, hτc1, hcT⟩ := hτc
  have h8R : ((8 * Δ S : ℕ) : ℝ) ≤ ((M.slotStart S.C (q + 2) : ℕ) : ℝ) := by exact_mod_cast hst8
  push_cast at h8R
  have hτ0 : 1 ≤ τ := by
    have : (0 : ℝ) < τ := by linarith [hipR.1]
    exact_mod_cast this
  have hsbτ := (stepBefore_time M) x R E hτ0
  have hτcR : (τ : ℝ) ≤ M.supportCutoff S.C c := by exact_mod_cast hτc1
  have hi₂sb : x.time i₂ ≤ x.time (x.stepBefore τ) :=
    (time_mono M) x R (((time_lt_iff_le_stepBefore M) x R E hτ0).1 (by linarith))
  by_cases hA : τ ≤ M.supportCutoff S.C (q + 2 + 1)
  · -- the proposer of `s_D`, from its tick
    have hAR : (τ : ℝ) ≤ M.supportCutoff S.C (q + 2 + 1) := by exact_mod_cast hA
    refine ⟨p, ip + 1, by rw [hipT]; exact hτ1, hpw _ (by rw [hipT]; linarith), hDp, ?_,
      hFcK p _ c hi₂sb (by linarith [hsbτ.1]) hcT (hpw _ (by linarith [hsbτ.1]))⟩
    refine Activity.mem_activeThroughout_of_le ?_ (by linarith) hHoldP
    rcases le_or_gt L (M.slotStart S.C (q + 2)) with h | h
    · rw [Nat.cast_sub h]
      have : (Δ S : ℝ) ≤ L := by exact_mod_cast hmx1
      linarith [hipR.1]
    · rw [Nat.sub_eq_zero_of_le h.le]; push_cast; linarith
  · -- an honest member `w` of the committee of the slot `σ'` whose update is the first support cutoff at or after `τ`
    push_neg at hA
    obtain ⟨hσ1, hσ2⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_div_le M.toSlotLayout F.sched U) S τ
    set σ := τ / (4 * Δ S) with hσdef
    have hσ2' := hsucc σ
    have hAτ : M.slotStart S.C (q + 2) + 6 * Δ S < τ := by rw [hcut, hst] at hA; omega
    have hσq : q + 3 ≤ σ := by
      by_contra hn
      have := hsmono (show σ + 1 ≤ q + 2 + 1 by omega)
      rw [hcut] at hA
      omega
    obtain ⟨σ', hσ'q, hτσ', hσ'c, hdwσ'⟩ : ∃ σ' : ℕ, q + 3 ≤ σ' ∧ τ ≤ M.supportCutoff S.C (σ' + 1) ∧ σ' + 1 ≤ c ∧
        M.dutyWindowStart S.C σ' + 2 * Δ S + L ≤ τ := by
      have hcc : ∀ s : ℕ, τ ≤ M.supportCutoff S.C s → σ ≤ s := fun s h => by
        by_contra hn
        have := hsmono (show s + 1 ≤ σ by omega)
        have := hsucc s
        rw [hcut] at h
        omega
      by_cases hτσ : τ ≤ M.supportCutoff S.C σ
      · have hσ1' : σ - 1 + 1 = σ := by omega
        have hq : q + 3 ≤ σ - 1 := by
          by_contra hn
          have h1 := hcutmono (show σ ≤ q + 2 + 1 by omega)
          omega
        refine ⟨σ - 1, hq, by rw [hσ1']; exact hτσ, by rw [hσ1']; exact hcc c hτc1, ?_⟩
        have h1 := hsucc (σ - 1)
        rw [hσ1'] at h1
        rcases hdw (σ - 1) with h | ⟨h, -⟩ <;> omega
      · push_neg at hτσ
        refine ⟨σ, hσq, by rw [hcut, hsucc]; rw [hcut] at hτσ; omega, ?_, ?_⟩
        · by_contra hn
          have := hcutmono (show c ≤ σ by omega)
          omega
        · rw [hcut] at hτσ
          rcases hdw σ with h | ⟨h, -⟩ <;> omega
    have hcσT : M.supportCutoff S.C (σ' + 1) ≤ T := le_trans (hcutmono hσ'c) hcT
    have hancσ' : anchor ≤ M.slotStart S.C (σ' + 1) := by
      have h1 : (anchor : ℝ) < M.slotStart S.C (q + 2) := lt_of_le_of_lt hAnchor hAfter.1
      have h2 : anchor < M.slotStart S.C (q + 2) := by exact_mod_cast h1
      have := hsmono (show q + 2 ≤ σ' + 1 by omega)
      omega
    have hmaj := (committee_majority_of_sleepiness M F) S A x anchor σ' hSleepK hancσ' hcσT
    obtain ⟨w, hw⟩ : (S.P.committee σ' ∩ honestActiveAt M S A x σ').Nonempty :=
      Finset.card_pos.1 (by omega)
    have hwC := (Finset.mem_inter.1 hw).1
    have hwA := (Finset.mem_inter.1 hw).2
    have hWin := hHoldC σ' (by omega) hcσT w hwA hwC
    have hwc : w ∉ A.corruptedAtTime x (M.supportCutoff S.C (σ' + 1)) :=
      (not_mem_corruptedAtTime_of_honestActiveAt M F) R E hwA le_rfl
    -- the times: `τ = d + 2 Δ + L`; the window starts at `a = d + Δ`, the member ticks to `d + Δ + L` and to `d + L`
    obtain ⟨d, hτd, hdwd⟩ : ∃ d : ℕ, τ = d + 2 * Δ S + L ∧ M.dutyWindowStart S.C σ' ≤ d :=
      ⟨τ - 2 * Δ S - L, by omega, by omega⟩
    have hστ : M.slotStart S.C (q + 2) + 4 * Δ S < d + L := by
      rw [hcut, hst] at hA; omega
    have hτR : (τ : ℝ) = d + 2 * Δ S + L := by rw [hτd]; push_cast; ring
    have hLR : (Δ S : ℝ) ≤ L := by exact_mod_cast hmx1
    have hdwR : ((M.dutyWindowStart S.C σ' : ℕ) : ℝ) ≤ d := by exact_mod_cast hdwd
    have hcσR : (τ : ℝ) ≤ ((M.supportCutoff S.C (σ' + 1) : ℕ) : ℝ) := by exact_mod_cast hτσ'
    have hwact : ∀ i : ℕ, (d : ℝ) ≤ x.time i → x.time i ≤ τ → w ∈ A.active i := fun i h1 h2 =>
      Activity.mem_activeThroughout.1 hWin i (by linarith) (by
        have := (time_mono M) x R (Nat.le_succ i); linarith)
    have htick : ∀ e : ℕ, d + Δ S ≤ e → e + Δ S ≤ τ → ∃ k : ℕ, x.lbl k = Event.tick w e ∧
        (e : ℝ) - ΔClockAhead ≤ x.time k ∧ x.time k ≤ e + ΔClockBehind := by
      intro e h1 h2
      have h1R : ((d + Δ S : ℕ) : ℝ) ≤ e := by exact_mod_cast h1
      have h2R : ((e + Δ S : ℕ) : ℝ) ≤ τ := by exact_mod_cast h2
      push_cast at h1R h2R
      exact E.tick_of_active e (by omega) w (fun i h3 h4 => hwact i (by linarith) (by linarith))
    obtain ⟨kR, hkR, hkR1, hkR2⟩ := htick (d + Δ S + L) (by omega) (by omega)
    obtain ⟨k₂, hk₂, -, -⟩ := htick (d + L) (by omega) (by omega)
    push_cast at hkR1 hkR2
    have hkRτ : x.time kR < τ := by linarith
    have hwkR : w ∉ A.corrupted kR := E.not_mem_corrupted_of_tick hkR
    have hστR : ((M.slotStart S.C (q + 2) + 4 * Δ S : ℕ) : ℝ) < ((d + L : ℕ) : ℝ) := by exact_mod_cast hστ
    push_cast at hστR
    have hi₂kR : x.time i₂ ≤ x.time kR := by
      have h1 : (x.time i₂ : ℝ) < M.slotStart S.C (q + 2) := hAfter.1
      linarith
    have hFw : (x.st kR w).finalized.compatible D = true :=
      hFcK w kR c hi₂kR (by linarith) hcT hwkR
    -- the holder: the induction at `a = d + Δ` when the proposer's tick is by then, the proposer otherwise
    have hGSTd : GST ≤ d + Δ S := by omega
    obtain ⟨u, kU, tu, htu, hcuNet, hcuAhead, hcb, hu₀, hu, hDu, hFa⟩ : ∃ (u : V) (kU : ℕ) (tu : ℝ),
        x.time kU ≤ tu ∧ tu + ΔNet + ΔClockAhead ≤ ((d + Δ S + L : ℕ) : ℝ) ∧
        tu + ΔClockAhead < ((d + Δ S + L : ℕ) : ℝ) ∧ tu + ΔNet ≤ ((τ + Δs : ℕ) : ℝ) ∧
        u ∈ A.activeThroughout x ((d + Δ S : ℕ) : ℝ) (((d + Δ S : ℕ) : ℝ) + Δs) ∧
        u ∉ A.corrupted kU ∧ D ∈ (x.st kU u).tree ∧
        (x.st (x.stepBefore (d + Δ S)) u).finalized.compatible D = true := by
      by_cases hP : x.time ip ≤ ((d + Δ S : ℕ) : ℝ)
      · obtain ⟨u, kU, hkU, hu, hDu, hstay, hFa⟩ := ih (d + Δ S) (by omega) (by rw [hipS]; exact hP)
          ⟨c, by omega, hcT⟩
        refine ⟨u, kU, ((d + Δ S : ℕ) : ℝ), hkU, ?_, ?_, ?_, hstay, hu, hDu, hFa⟩ <;> push_cast <;> linarith
      · push_neg at hP
        have hsbP : x.stepBefore (d + Δ S) ≤ ip := by
          have h1 := ((stepBefore_time M) x R E (show 1 ≤ d + Δ S by omega)).1
          exact ((lt_of_time_lt M) x R (by linarith)).le
        refine ⟨p, ip + 1, x.time ip, le_of_eq hipT, ?_, ?_, ?_, ?_, hpw _ (by rw [hipT]; exact hipcut), hDp,
          (compatible_iff _ _).2 (Or.inl (ancestorEq_trans ((F_ancestorEq_of_le M F) x R E p hsbP) hFip))⟩
        · push_cast; linarith [hipR.2]
        · push_cast; linarith [hipR.2]
        · push_cast; linarith [hipR.2]
        · refine Activity.mem_activeThroughout_of_le ?_ ?_ hHoldP
          · exact_mod_cast (show M.slotStart S.C (q + 2) - L ≤ d + Δ S by omega)
          · have : ((d + Δ S : ℕ) : ℝ) < ((M.supportCutoff S.C (q + 2 + 1) : ℕ) : ℝ) := by
              linarith [hipR.2]
            linarith
    have hDw : D ∈ (x.st kR w).tree :=
      block_at_tick_of_held_step_deadline M F U S A x R GST (τ + Δs) tu kU (d + Δ S) (d + Δ S + L) (d + L) kR k₂
        u w D (E.upTo (τ + Δs)) hRedeliver (Sy.upTo (τ + Δs))
        ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M)
          (by have : (τ : ℝ) ≤ T := le_trans hτcR (by exact_mod_cast hcT)
              linarith) hRoots)
        hParent hGSTd (by omega) hcuNet hcuAhead hcb (by omega) hu₀ htu hu hDu hFa hDg hkR
        (fun i h1 h2 => hwact i (by push_cast at h1; linarith) (le_trans ((time_mono M) x R h2) hkRτ.le))
        hk₂ (by omega) (by rw [hDslot]; omega) hFw
    refine ⟨w, kR, hkRτ.le, hwkR, hDw, Activity.mem_activeThroughout_of_le (by linarith) (by linarith) hWin, ?_⟩
    exact hFcK w _ c hi₂sb (by linarith [hsbτ.1]) hcT
      ((not_mem_corrupted_of_le_time M) x R E hwc (by linarith [hsbτ.1]))

/-- **Kit fact, an honest proposal enters a tree no earlier than its proposer's tick.** When the proposer of
slot `s` sends `D` at its tick `ip` to the start of `s`, `D` is of slot `s` and not the genesis block, and the
proposer is outside the adversary set at every step up to `e + 1`, a step `e` at which `D` enters `w`'s tree
comes at or after `ip`.

Why: `w` relays `D` at the step `e` (`step_tree_new`); `D`'s author is its slot's proposer (the tree's
closure, Lemma 11); under unforgeability the proposer put `D` on the wire itself before (`sent_unforgeable`),
first at a tick of its own (`authored_from_own_tick`), and a tick that proposes `D` is at the start of `D`'s
slot (Lemma 19), the tick `ip` (`tick_unique`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`, `R`, `E`: the setup, the activity, the execution, the run's facts, the environment's facts;
  `s`: the slot; `ip`: the proposer's tick; `e`: the entry step; `D`: the proposal; `w`: the holder.

Read aloud: a validator's tree takes in an honest proposal only at or after the proposer's tick that made
it. -/
theorem proposal_entry_after_tick (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver}
    {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (s ip e : ℕ) (D : Block V) (w : V)
    (hl : x.lbl ip = Event.tick (S.P.proposer s) (M.slotStart S.C s))
    (hDslot : D.slot = s) (hg : D ≠ Block.genesis)
    (hp : x.HonestThrough A (e + 1) (S.P.proposer s))
    (hn : D ∉ (x.st e w).tree) (hD : D ∈ (x.st (e + 1) w).tree) :
    ip ≤ e := by
  obtain ⟨hsend, -, -⟩ := (step_tree_new M F) x R E hD hn
  have hprop := ((F.nd.nodeInvCore_treeClosed
    ((lem11_node_invariantCore_of_run M F) S x R (e + 1) w).1).2 D hD hg).2.2.1
  rw [hDslot] at hprop
  have hauth : GoldilocksCorrectness.Statements.Executions.author (NamedObject.block D) =
      some (S.P.proposer s) := hprop
  have hm := (sent_unforgeable M F) R E (e + 1) _ (NamedObject.block D) (S.P.proposer s)
    ((mem_sent_of_mem_sub M F) x hsend) (Or.inl rfl) hauth hp
  obtain ⟨k', hk', t'', hl', hdiff⟩ := (authored_from_own_tick M F) x R E hauth hm hp
  obtain ⟨-, n1, sent1, hrun1, hmem1⟩ := (tick_send_of_honestSendAt M F R E) hl' hdiff
  have hInvT : M.nodeInv S.C S.P S.X (x.tickInput (S.P.proposer s) t'') := by
    rw [show x.tickInput (S.P.proposer s) t'' = x.st k' (S.P.proposer s) by
      unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hl']]
    exact (lem11_node_invariant M F S A x R E k' _ (E.not_mem_corrupted_of_tick hl')).1
  obtain ⟨-, ht'', -, -, _H, _votes, _sv, -, -, -, hB1eq⟩ :=
    (GoldilocksCorrectness.Record.Statements.Routines.lem19_tick_proposes F) S.C S.P S.X _ n1 _ sent1 D
      hrun1 hInvT hmem1
  have hsl : S.C.slot (t'' : Int) = s := by
    rw [← hDslot, hB1eq]
    rfl
  have htt : t'' = M.slotStart S.C s := by
    have h := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_cast M.toSlotLayout F.sched U) S s
    rw [hsl] at ht''
    exact_mod_cast ht''.trans h.symm
  subst htt
  have hk : k' = ip := E.tick_unique k' ip _ _ hl' hl
  omega

/-! ## Lemma 97 -/

/-- **Lemma 97, the reader.** The proof; the audited statement is in
`Statements/Executions/FinalityLivenessStatements.lean`.

Why: the honest proposal `D` of slot `s_D` is on the honest chain: every chain block before
`s_D − 1` is an ancestor of its parent, and, once the update of `s_D` is read, `D` is saved at
`s_D`. An honest justified block, and a certificate's entry, at a round's first slot `s_a` whose
update ran by `T`, are therefore compatible with `D` (`s_a < s_D` gives `s_a ≤ s_D − 2`). The
reader, awake for a delay after the proposal, receives `D` (its finalized block, below its
justified block, being compatible with `D`). At the step that adds `D` to its tree, its FG state
is `ReadyFor` `D`: its justified block is `D`'s finalized block or a descendant of it, or of a
smaller justification height; and a block of its tree at the greatest chain-state height, greater
than `h(D)`, carries a certificate at `h(D) > H` naming an entry compatible with `D`, at `D`'s
height, so `F(D)` is an ancestor of it. So the finalized block reaches `F(D)` there and keeps
descending. The reader's step is at or before some support cutoff at most `T`: the holder the reader receives `D` from is then a member of a committee whose
update is at most `T` (`honest_proposal_holder_at`). The reader is read at its own tick, at or before
its step: `D` is in its tree there by `block_at_tick_of_held_step_deadline`, from that holder
when the proposer's tick is by the window's start `τ`, and from the proposer otherwise; the step that adds
`D` comes after the hand-over, since it comes at or after the proposer's tick
(`proposal_entry_after_tick`) or after the update of `s_D`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₂`: the hand-over step; `H`: the threshold; `T`: the reading time;
- `r_D`, `s_D`: the round and the slot of `D`; `j`: the reader's step, at or before some support
  cutoff at most `T`; `D`: the proposal; `v`: the reader.

Read aloud: whoever is awake for a delay after an honest round opening slot's proposal, at a step
at or before some support cutoff at most `T`, has finalized at least what that proposal's chain
finalized. -/
theorem lem97_reader_finalized (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ anchor i₂ H T r_D s_D j : ℕ) (D : Block V)
      (v : V)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x T)
    (hRootsU : ∀ v ∈ updaterAt M S A x s_D, RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C (s_D + 1)))))
    (hParent : ParentHeldAtDelivery M x)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) T)
    (hAdvQU : ∀ v ∈ updaterAt M S A x s_D, A.AdversaryFewerThanQuorumUntil x (quorum V) (x.time (x.tickStep v (M.supportCutoff S.C (s_D + 1)))))
    (hSleepK : CommitteeSleepinessUntil M S A x anchor T) (hAnchor : anchor ≤ x.time i₂)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀) (ht₀ : M.supportCutoff S.C (s₀ + 1) ≤ x.time i₂)
    (hChain : ∀ σ : ℕ, M.supportCutoff S.C (σ + 1) ≤ T →
      ConfirmationsChainBefore M S A x s₀ (σ + 1))
    (hInv : ∀ s' : ℕ, s₀ < s' → M.supportCutoff S.C (s' + 1) ≤ T →
      ChainInvFor M S A x (honestActiveAt M S A x s')
        (OnHonestChainBefore M S A x s₀ s') s')
    (hLocks : ∀ s' : ℕ, s₀ < s' → M.supportCutoff S.C (s' + 1) ≤ T →
      ∀ w ∈ honestActiveAt M S A x s',
        LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ s') s' w)
    (hLocks₀ : ∀ w ∈ honestActiveAt M S A x s₀,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (s₀ + 1)) s₀ w)
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hCaches : ∀ (j' : ℕ) (w : V), x.time i₂ ≤ x.time j' → x.time j' ≤ T →
      w ∉ A.corrupted j' → CachesOnChain M S A x s₀ H (x.st j' w))
    (hCachesU : ∀ v ∈ updaterAt M S A x s_D, ∀ (j' : ℕ) (w : V), x.time i₂ ≤ x.time j' →
      x.time j' ≤ x.time (x.tickStep v (M.supportCutoff S.C (s_D + 1))) → w ∉ A.corrupted j' → CachesOnChain M S A x s₀ H (x.st j' w))
    (hsD : s_D = r_D * S.C.R) (hT : M.supportCutoff S.C s_D ≤ T)
    (hAfter : x.time i₂ < M.slotStart S.C s_D ∧
      ∀ k : ℕ, x.lbl k = Event.tick (S.P.proposer s_D) (M.slotStart S.C s_D) → x.time i₂ < x.time k)
    (hOpener : HonestOpenerAt M S A x s_D)
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick (S.P.proposer s_D) (M.slotStart S.C s_D) ∧
      (⟨S.P.proposer s_D, NamedObject.block D⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i)
    (hNoCol : ¬ RootCollisionAtProposal M S A x s_D D)
    (hHold : ∀ s' : ℕ, s_D - 1 ≤ s' → s' ≤ s_D → ∀ u ∈ honestActiveAt M S A x s', u ∈ S.P.committee s' →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- every honest committee member of every slot after `s_D` whose update is at most `T` is active from its duty window's
    -- start through the sync delay after that update; the proposer of `s_D` from one delay or one sync delay before its
    -- slot's start through the sync delay after its slot's update
    (hHoldC : ∀ σ' : ℕ, s_D + 1 ≤ σ' → M.supportCutoff S.C (σ' + 1) ≤ T → ∀ u ∈ honestActiveAt M S A x σ',
      u ∈ S.P.committee σ' → u ∈ A.activeThroughout x ((M.dutyWindowStart S.C σ' : ℕ) : ℝ)
        (((M.supportCutoff S.C (σ' + 1) : ℕ) : ℝ) + Δs))
    (hHoldP : S.P.proposer s_D ∈ A.activeThroughout x ((M.slotStart S.C s_D - max (Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s_D + 1) : ℕ) : ℝ) + Δs))
    (hHD : H < (M.chainStateOf S.C D).h)
    (hv : A.HonestThroughTime x (x.time j) v)
    (hjT : ∃ s' : ℕ, x.time j ≤ M.supportCutoff S.C s' ∧ M.supportCutoff S.C s' ≤ T)
    (hAwake : AwakeForDelayWithin S A x Δs v (M.slotStart S.C s_D) j) :
    (M.chainStateOf S.C D).F.AncestorEq (x.st j v).finalized := by
  -- the preamble (`honest_proposal_chain_kit`), the schedule's times, the proposer's tick
  obtain ⟨hs2, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.slot_after_healed_round M.toSlotLayout F.sched) S
    s₀ s_D (by exact_mod_cast lt_of_le_of_lt ht₀ hAfter.1)
  obtain ⟨q, rfl⟩ : ∃ q, s_D = q + 2 := ⟨s_D - 2, by omega⟩
  obtain ⟨ip, hl, hsent⟩ := hPropose
  set p := S.P.proposer (q + 2) with hpdef
  obtain ⟨hDslot, hDg, hDp, hFip, hcompatT, hJF⟩ := (honest_proposal_chain_kit M F U Fx) S A x R GST s₀ anchor i₂ H T
    r_D (q + 2) D E hNet hSkew hRedeliver Sy hΔs hRoots hRootsU hParent hAdvQ hAdvQU hSleepK hAnchor hGST ht₀ hChain
    hInv hLocks hLocks₀ hOld hCaches hCachesU hsD hT hAfter hOpener ip hl hsent hNoCol hHold hHoldP
  obtain ⟨sj, hjsj, hsjT⟩ := hjT
  have hsjTR : ((M.supportCutoff S.C sj : ℕ) : ℝ) ≤ T := by exact_mod_cast hsjT
  have hjTR : x.time j ≤ T := le_trans hjsj hsjTR
  have hΔ := one_le_Δ S
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hNetR : (0 : ℝ) ≤ ΔNet := Nat.cast_nonneg _
  have hΔsR : (0 : ℝ) ≤ Δs := Nat.cast_nonneg _
  set L := max (Δ S) Δs with hLdef
  have hmx1 : Δ S ≤ L := le_max_left _ _
  have hmx2 : Δs ≤ L := le_max_right _ _
  have hLR : (Δ S : ℝ) ≤ L := by exact_mod_cast hmx1
  have hΔsLR : (Δs : ℝ) ≤ L := by exact_mod_cast hmx2
  have hsucc : ∀ s : ℕ, M.slotStart S.C (s + 1) = M.slotStart S.C s + 4 * Δ S := fun s => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U),
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s, Nat.mul_add, Nat.mul_one]
  have hcut : ∀ s : ℕ, M.supportCutoff S.C s = M.slotStart S.C s + 2 * Δ S := fun s => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U),
      (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U)]; omega
  have hsmono : ∀ {a b : ℕ}, a ≤ b → M.slotStart S.C a ≤ M.slotStart S.C b := fun h =>
    (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S h
  have hst := hsucc (q + 2)
  have hs₀cut : M.supportCutoff S.C (s₀ + 1) < M.slotStart S.C (q + 2) := by
    exact_mod_cast lt_of_le_of_lt ht₀ hAfter.1
  have hGSTst : GST + L ≤ M.slotStart S.C (q + 2) := by
    have h1 := hsmono (show s₀ ≤ s₀ + 1 by omega)
    have h2 := hcut s₀
    have h3 := hcut (s₀ + 1)
    omega
  have hst1 : 1 ≤ M.slotStart S.C (q + 2) := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U)]
    have : 4 * Δ S * 1 ≤ 4 * Δ S * (q + 2) := Nat.mul_le_mul_left _ (by omega)
    omega
  have hipR := (E.tick_active ip p _ hl).2
  have hipT : x.time (ip + 1) = x.time ip := R.time_keep ip (by rw [hl]; exact nofun)
  have hpH : p ∈ honestActiveAt M S A x (q + 2) := (opener_mem_honestActiveAt M F U) S A R E q hOpener
  have hpc : p ∉ A.corruptedAtTime x (M.supportCutoff S.C (q + 2 + 1)) :=
    (not_mem_corruptedAtTime_of_honestActiveAt M F) R E hpH le_rfl
  have hpw : ∀ k : ℕ, x.time k ≤ M.supportCutoff S.C (q + 2 + 1) → p ∉ A.corrupted k :=
    fun k hk => (not_mem_corrupted_of_le_time M) x R E hpc hk
  have hstR : ((M.slotStart S.C (q + 2) : ℕ) : ℝ) + 6 * Δ S = ((M.supportCutoff S.C (q + 2 + 1) : ℕ) : ℝ) := by
    rw [hcut (q + 2 + 1), hst]; push_cast; ring
  have hipcut : x.time ip ≤ M.supportCutoff S.C (q + 2 + 1) := by
    have := hipR.2; linarith
  -- the reader's tick `k` to `c`, at or before its step `j`, awake from `τ`
  obtain ⟨τ, c, c₂, k, k₂, hτ1, hτc, hlk, hkj, hawk, hlk₂, hc₂1, hc₂c⟩ := hAwake
  have hτN : M.slotStart S.C (q + 2) ≤ τ := by exact_mod_cast hτ1
  have hc₂N : M.slotStart S.C (q + 2) ≤ c₂ := by exact_mod_cast hc₂1
  have hkR := (E.tick_active k v c hlk).2
  have hkjT : x.time k ≤ x.time j := (time_mono M) x R hkj
  have hvk : v ∉ A.corrupted k := hv k hkjT
  have hcR : ((τ + L : ℕ) : ℝ) ≤ c := by exact_mod_cast hτc
  push_cast at hcR
  have hτR : ((M.slotStart S.C (q + 2) : ℕ) : ℝ) ≤ τ := hτ1
  have hi₂k : x.time i₂ ≤ x.time k := by
    have h1 : x.time i₂ < ((M.slotStart S.C (q + 2) : ℕ) : ℝ) := hAfter.1
    linarith [hkR.1]
  have hτsj : τ ≤ M.supportCutoff S.C sj := by
    have : (τ : ℝ) < ((M.supportCutoff S.C sj : ℕ) : ℝ) := by linarith [hkR.1]
    exact_mod_cast this.le
  have hFw : (x.st k v).finalized.compatible D = true :=
    (hJF v k sj hi₂k (le_trans hkjT hjsj) hsjT hvk).2
  have hGSTτ : GST ≤ τ := by omega
  -- the holder: `honest_proposal_holder_at` at `τ` when the proposer's tick is by then, the proposer otherwise
  obtain ⟨u, kU, tu, htu, hcuNet, hcuAhead, hcb, hu₀, hu, hDu, hFa⟩ : ∃ (u : V) (kU : ℕ) (tu : ℝ),
      x.time kU ≤ tu ∧ tu + ΔNet + ΔClockAhead ≤ (c : ℝ) ∧ tu + ΔClockAhead < (c : ℝ) ∧
      tu + ΔNet ≤ ((τ + L : ℕ) : ℝ) ∧ u ∈ A.activeThroughout x (τ : ℝ) ((τ : ℝ) + Δs) ∧
      u ∉ A.corrupted kU ∧ D ∈ (x.st kU u).tree ∧
      (x.st (x.stepBefore τ) u).finalized.compatible D = true := by
    by_cases hP : x.time ip ≤ (τ : ℝ)
    · obtain ⟨u, kU, hkU, hu, hDu, hstay, hFa⟩ := (honest_proposal_holder_at M F U Fx) S A x R GST s₀ anchor i₂ H T
        r_D (q + 2) D E hNet hSkew hRedeliver Sy hΔs hRoots hRootsU hParent hAdvQ hAdvQU hSleepK hAnchor hGST ht₀
        hChain hInv hLocks hLocks₀ hOld hCaches hCachesU hsD hT hAfter hOpener ⟨ip, hl, hsent⟩ hNoCol hHold hHoldC
        hHoldP τ (by rw [(tickStep_eq_of_lbl M) x E hl]; exact hP) ⟨sj, hτsj, hsjT⟩
      refine ⟨u, kU, τ, hkU, by linarith, by linarith, by push_cast; linarith, hstay, hu, hDu, hFa⟩
    · push_neg at hP
      have hsbP : x.stepBefore τ ≤ ip := by
        have h1 := ((stepBefore_time M) x R E (show 1 ≤ τ by omega)).1
        exact ((lt_of_time_lt M) x R (by linarith)).le
      refine ⟨p, ip + 1, x.time ip, le_of_eq hipT, by linarith [hipR.2], by linarith [hipR.2],
        by push_cast; linarith [hipR.2], ?_, hpw _ (by rw [hipT]; exact hipcut), hDp,
        (compatible_iff _ _).2 (Or.inl (ancestorEq_trans ((F_ancestorEq_of_le M F) x R E p hsbP) hFip))⟩
      refine Activity.mem_activeThroughout_of_le ?_ ?_ hHoldP
      · exact_mod_cast (show M.slotStart S.C (q + 2) - L ≤ τ by omega)
      · linarith
  -- the proposal is in the reader's tree at its tick `k`, so at its step `j`
  have hDk : D ∈ (x.st k v).tree :=
    block_at_tick_of_held_step_deadline M F U S A x R GST (τ + L) tu kU τ c c₂ k k₂ u v D
      (E.upTo (τ + L)) hRedeliver (Sy.upTo (τ + L))
      ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) (le_trans hkjT hjTR) hRoots)
      hParent hGSTτ hτc hcuNet hcuAhead hcb (by omega) hu₀ htu hu hDu hFa hDg hlk
      (fun i h1 h2 => Activity.mem_active.2 ⟨hawk i h1 h2, hv i (le_trans ((time_mono M) x R h2) hkjT)⟩)
      hlk₂ hc₂c (by rw [hDslot]; exact hc₂N) hFw
  have hDj : D ∈ (x.st j v).tree := (mem_T_mono M F) x R E v hkj hDk
  -- at the step that adds `D` to the reader's tree, its FG state is ready for `D`
  refine (F_reaches_of_mem M F) x R E D v hDg j (fun i hi hDi hDi1 => ?_) hDj
  have hiT : x.time i ≤ x.time j := (time_mono M) x R hi.le
  -- the step `i` comes at or after the proposer's tick (`proposal_entry_after_tick`), or after the update of `s_D`:
  -- either way after the hand-over
  have hi2 : x.time i₂ ≤ x.time i := by
    have hi₂ip : x.time i₂ < x.time ip := hAfter.2 ip hl
    by_cases hpi : x.time (i + 1) ≤ M.supportCutoff S.C (q + 2 + 1)
    · have hipi : ip ≤ i := (proposal_entry_after_tick M F U) S A x R E (q + 2) ip i D v hl hDslot hDg
        (fun i' hi' => hpw i' (le_trans ((time_mono M) x R hi') hpi)) hDi hDi1
      linarith [(time_mono M) x R hipi]
    · push_neg at hpi
      have hkeep : x.time (i + 1) = x.time i := by
        rcases (step_cases_per_step M F) x R E i v with h | ⟨t, n', sent, hl', -⟩ | ⟨sm, hl', -⟩ |
            ⟨⟨tR, keep, hl'⟩, -⟩
        · rw [h] at hDi1; exact absurd hDi1 hDi
        all_goals exact R.time_keep i (by rw [hl']; exact nofun)
      linarith
  have hiC : x.time i ≤ M.supportCutoff S.C sj := le_trans hiT hjsj
  have hiTT : x.time i ≤ T := le_trans hiT hjTR
  have hvi : v ∉ A.corrupted i := hv i hiT
  obtain ⟨hH, -, hJent, hJh, -⟩ := hCaches i v hi2 hiTT hvi
  refine ⟨GoldilocksCorrectness.Record.Statements.Routines.chainStatesComputed M S.C _, ?_, ?_⟩
  · -- the justification
    rcases (compatible_iff _ _).1 (hJF v i sj hi2 hiC hsjT hvi).1 with hJD | hDJ
    · by_cases hlt : (x.st i v).justifiedHeight < (M.chainStateOf S.C D).h_j
      · exact Or.inr hlt
      left
      have hFJD := (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_F_ancestorEq_J M F) S.C D
      by_cases hj0 : (M.chainStateOf S.C D).h_j = 0
      · rw [((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_J_spec M F) S.C D).2.1 hj0] at hFJD
        exact ancestorEq_trans hFJD (genesis_ancestorEq _)
      obtain ⟨-, hJDD, hJDh⟩ :=
        ((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) S.C D).1 (by omega_nat)
      rcases ancestorEq_compatible hJD hJDD with hSJ | hJS
      · have hle := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C _ _).2.2.2.1 hSJ
        have heq : (M.chainStateOf S.C (x.st i v).justified).h =
            (M.chainStateOf S.C (M.chainStateOf S.C D).J).h := by
          rw [hJh, hJDh] at hle ⊢
          omega_nat
        have hTe := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C _ _).2.2.2.2 hSJ heq
        have hJe := (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_J_isEntry M F) S.C D (by omega_nat)
        unfold IsEntry at hJent hJe
        rw [hJent, hJe] at hTe
        rw [hTe]
        exact hFJD
      · exact ancestorEq_trans hFJD hJS
    · exact Or.inl (ancestorEq_trans ((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_F_ancestorEq M F) S.C D) hDJ)
  · -- a viable descendant of `F(D)`
    obtain ⟨-, ⟨X, hX, hXh⟩, -⟩ := (cachesWitnessed_of_exec M F) S A x R E i v
    by_cases hle : hMax M S.C (x.st i v) ≤ (M.chainStateOf S.C D).h
    · exact Or.inl hle
    right
    have hlt : (M.chainStateOf S.C D).h < (M.chainStateOf S.C X).h := by
      rw [hXh]; exact Nat.lt_of_not_le hle
    obtain ⟨Y, hYX, -, -, -, hTY, hPC⟩ :=
      (GoldilocksCorrectness.Record.Statements.Routines.lem67_first_advance M F) S.C X (M.chainStateOf S.C D).h
        (by omega_nat) hlt
    have hYT := (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E i v X Y hX hYX
    have ht₀R : ((M.supportCutoff S.C (s₀ + 1) : ℕ) : ℝ) ≤ x.time i₂ := ht₀
    obtain ⟨s_a, r', uₐ, Eb, hsa, hk', hl', -, -, hEb, hE, -, hEh, hroot⟩ := (cert_entry_at_round_slot M F U Fx) S A x R
      s₀ H i v Y _ _ E (hAdvQ.mono (max_le hiTT (by linarith))) hOld hYT hPC hHD
    have hTT := (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E i v Y _ hYT hTY
    have hEq : (M.chainStateOf S.C Y.parent).T_h = Eb :=
      ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) hiTT hRoots) _ _
        ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := i) (v := v) hvi le_rfl hTT)
        ((onHonestChainAt_inHonestTreeBy M F U) S A x R E _ uₐ (M.supportCutoff S.C (s_a + 1)) _ Eb hl'
          ((time_mono M) x R hk'.le) hEb) hroot
    have hEX : Eb.AncestorEq X := hEq ▸ ancestorEq_trans hTY hYX
    have hFE : (M.chainStateOf S.C D).F.AncestorEq Eb := by
      by_cases hF0 : (M.chainStateOf S.C D).h_F = 0
      · rw [(GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_F_genesis M F) S.C D hF0]
        exact genesis_ancestorEq Eb
      rcases (compatible_iff _ _).1 (hcompatT Eb s_a r' _ uₐ sj hsa hl'
          (le_trans ((time_mono M) x R hk'.le) hiC) hsjT hE) with hED | hDE
      · rcases ancestorEq_compatible ((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_F_ancestorEq M F) S.C D)
            hED with h | h
        · exact h
        · exfalso
          have h1 := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C _ _).2.2.2.1 h
          obtain ⟨-, -, -, hFh⟩ :=
            ((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) S.C D).2.2 (by omega_nat)
          have hb := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C D D).1
          rw [hFh, hEh] at h1
          omega_nat
      · exact ancestorEq_trans ((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_F_ancestorEq M F) S.C D) hDE
    exact ⟨X, hX, ancestorEq_trans hFE hEX, max_le (by rw [hXh]) hlt.le⟩

end GoldilocksCorrectness.Record.Proofs.Executions

