module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89RisingJ
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Network
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89StabilityJ
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.ReadingPoints
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.HealedFrame
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma53
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.HeightInvariant
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Certificates
public import GoldilocksCorrectness.Proofs.Executions.Lemma89RisingJ
public import GoldilocksCorrectness.Proofs.Executions.HealedFrame
public import GoldilocksCorrectness.Proofs.Executions.Lemma53
public import GoldilocksCorrectness.Proofs.Executions.HeightInvariant
public import GoldilocksCorrectness.Proofs.Routines.Certificates
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma89WaitJ, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma89WaitJ.lean`, over a model `M` whose
facts `F` hold, for an execution `x` of `protocolOf M S`: part B of Lemma 89, no honest
justification height reaching a waiting honest round opening slot's height before the next one,
namely an honest proposal one more than its proposer's justification height, a fork-choice change
when a validator's justification height reaches a height, and no honest justification height
reaching the waited height before the later opening's support cutoff. The page's routine-level
theorems are the facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax IsEntry VoterTreeAt JustifiedInTree AnchorAt)

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
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  genesis_ancestorEq ancestorEq_compatible ancestorEq_antisymm ancestorEq_genesis_iff)

open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn expireLocks)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- **An honest proposal is higher than its proposer's justification.**

The variables:
- `M`: the model; `F`: its facts.

Read aloud: an honest proposer never proposes at the height its own justification is at. -/
theorem honest_proposal_above_h_j (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (s : ℕ) (B : Block V) (p : V)
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) :
    (x.tickInput p (M.slotStart S.C (s + 1))).justifiedHeight + 1 ≤
      (M.chainStateOf S.C B).h := by
  have hPV := (proposal_parent_viable_head M F U) S A x R E s B p hPropose
  obtain ⟨iB, hl, hsent⟩ := hPropose
  obtain ⟨-, hBg, hpar?, -⟩ := (proposal_parent_walk_end M F U) S A x R E s iB B p hl hsent
  have hPB := GoldilocksCorrectness.Proofs.Routines.ancestorEq_of_parent? hpar?
  obtain ⟨hPT, -, hRP, hflP⟩ := ((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_heads_iff M F) S.C S.P S.X _ ((nodeInv_tickInput_of_tick M F) S A x R E hl) _).1 hPV
  have hmono := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C B.parent B).2.2.2.1 hPB
  have hjl : (x.tickInput p (M.slotStart S.C (s + 1))).justifiedHeight <
      hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) :=
    (h_j_lt_h_max_st M F) S A x R E (x.tickStep p (M.slotStart S.C (s + 1))) p
  have hml := (GoldilocksCorrectness.Record.Proofs.Routines.h_max_sub_one_le_floor M F) S.C S.P S.X (x.tickInput p (M.slotStart S.C (s + 1))) ((nodeInv_tickInput_of_tick M F) S A x R E hl)
  by_cases hhi : (x.tickInput p (M.slotStart S.C (s + 1))).justifiedHeight + 1 ≤
      (M.chainStateOf S.C B.parent).h
  · unfold Height at *
    omega
  have hm1 : hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) =
      (x.tickInput p (M.slotStart S.C (s + 1))).justifiedHeight + 1 := by
    unfold Height at *
    omega
  have hc : M.fg_contest (x.tickInput p (M.slotStart S.C (s + 1))) = false := by
    cases hc' : M.fg_contest (x.tickInput p (M.slotStart S.C (s + 1)))
    · rfl
    · exfalso
      have hfl : M.head_height_floor (x.tickInput p (M.slotStart S.C (s + 1))) =
          hMax M S.C (x.tickInput p (M.slotStart S.C (s + 1))) := by
        rcases (GoldilocksCorrectness.Record.Proofs.Routines.floor_cases M F) S.C S.P S.X (x.tickInput p (M.slotStart S.C (s + 1))) ((nodeInv_tickInput_of_tick M F) S A x R E hl) with ⟨-, -, h⟩ | ⟨h, -⟩
        · exact h
        · rw [hc'] at h; cases h
      unfold Height at *
      omega
  have hroot : M.get_fc_root (x.tickInput p (M.slotStart S.C (s + 1))) =
      (x.tickInput p (M.slotStart S.C (s + 1))).justified := by
    rcases (GoldilocksCorrectness.Record.Proofs.Routines.root_cases M F) S.C S.P S.X (x.tickInput p (M.slotStart S.C (s + 1))) ((nodeInv_tickInput_of_tick M F) S A x R E hl) with ⟨h, -, -⟩ | ⟨-, h | h⟩
    · exact h
    · rw [hc] at h; cases h
    · exact absurd hm1 h
  have hfc : (M.fg_to_ac (x.tickInput p (M.slotStart S.C (s + 1)))).fc_root =
      M.get_fc_root (x.tickInput p (M.slotStart S.C (s + 1))) :=
    (GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F) _
  rw [hfc, hroot] at hRP
  have hPh : (M.chainStateOf S.C B.parent).h = (x.tickInput p (M.slotStart S.C (s + 1))).justifiedHeight := by
    unfold Height at *
    omega
  obtain ⟨⟨D, hD, hJD, hjD⟩, -, -⟩ : GoldilocksCorrectness.Record.Proofs.Routines.CachesWitnessed M S.C (x.tickInput p (M.slotStart S.C (s + 1))) :=
    (cachesWitnessed_of_exec M F) S A x R E (x.tickStep p (M.slotStart S.C (s + 1))) p
  by_cases hj0 : (x.tickInput p (M.slotStart S.C (s + 1))).justifiedHeight = 0
  · have := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C B B).1.1
    unfold Height at *
    omega
  have hj1 : 1 ≤ (M.chainStateOf S.C D).h_j := by
    unfold Height at *
    omega
  obtain ⟨hcert, -, -⟩ := ((GoldilocksCorrectness.Record.Proofs.Routines.lem66_chain_state_certified M F) S.C D).1 hj1
  have hJh := ((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_J_spec M F) S.C D).2.2 hj1
  have hEntry : (M.chainStateOf S.C (M.chainStateOf S.C D).J).T_h = (M.chainStateOf S.C D).J := by
    rcases (chainStateOf_J_entry M F) S.C D with h | h
    · rw [h, (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_genesis_T_h M F)]
    · exact h
  rw [hJD] at hRP
  have hTh : (M.chainStateOf S.C B.parent).T_h = (M.chainStateOf S.C D).J := by
    have he := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C (M.chainStateOf S.C D).J B.parent).2.2.2.2 hRP
      (by rw [hJh, hPh, hjD])
    rw [← he, hEntry]
  obtain ⟨X, hXD, Aₗ, hA, hAv⟩ := hcert
  rw [GoldilocksCorrectness.Record.quorumAt_eq_quorum Fx F.sched X] at hA
  have hPool : ∀ u ∈ Aₗ, ∃ a ∈ (x.tickInput p (M.slotStart S.C (s + 1))).attestationsHeld,
      a.val_index = u ∧ a.h = (M.chainStateOf S.C B.parent).h ∧
        a.T = (M.chainStateOf S.C B.parent).T_h.root ∧ a.τ = false := by
    intro u hu
    obtain ⟨a, hav, hah, haT, haτ, hach⟩ := hAv u hu
    have hmem := (pool_holds_chain_attestations M F) S A x R E (x.tickStep p (M.slotStart S.C (s + 1))) p D a
      hD ((GoldilocksCorrectness.Record.Proofs.Routines.on_chain_mono M F) a hXD hach)
    refine ⟨a, hmem, hav, ?_, ?_, haτ⟩
    · rw [hah, hPh, hjD]
    · rw [haT, hTh]
  have h53 := (lem53_next_honest_proposal_carries_certificate M F U Fx) S A x R E (s + 1) p B B.parent Aₗ
    ⟨iB, hl, hsent⟩ rfl hA
    (fun u hu => by
      obtain ⟨a, ha, h1, h2, h3, -⟩ := hPool u hu
      exact ⟨a, ha, h1, h2, h3⟩)
  have := (h53.2 hPool).1
  unfold Height at *
  omega

/-- **A step that changes a validator's justification height leaves it outside the adversary set.**
Such a step is `w`'s tick or a delivery to `w`: a restart keeps the justification height (the wake's
readers, `wake_readers`) and any other step leaves `w`'s state as it was (`RunFacts.untouched`). A tick
is by a validator active in the configuration it starts from (`tick_active`), so is a delivery
(`deliver_active`), and neither changes the adversary set (`corrupted_keep`).

The variables:
- `M`: the model; `F`: its facts;
- `S`, `A`, `x`: the setup, the activity, the execution; `w`: the validator; `j`: the step.

Read aloud: a validator whose justification height changes at step `j` is outside the adversary set
after step `j`. -/
theorem not_mem_corrupted_succ_of_justifiedHeight_ne (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (w : V) (j : ℕ)
    (hne : (x.st (j + 1) w).justifiedHeight ≠ (x.st j w).justifiedHeight) :
    w ∉ A.corrupted (j + 1) := by
  by_cases ht : ∃ t, x.lbl j = Event.tick w t
  · obtain ⟨t, hl⟩ := ht
    exact E.not_mem_corrupted_succ_of_tick hl
  by_cases hd : ∃ sm, x.lbl j = Event.deliver w sm
  · obtain ⟨sm, hl⟩ := hd
    rw [E.corrupted_keep j (by rw [hl]; simp)]
    exact Activity.not_mem_corrupted_of_mem_active (E.deliver_active j w sm hl)
  by_cases hr : ∃ t keep, x.lbl j = Event.restart w t keep
  · obtain ⟨t, keep, hl⟩ := hr
    exfalso
    apply hne
    rw [(R.restart j w t keep hl).1]
    exact (F.wk.wake_readers _ _).2.2.2.2.2.1
  · exfalso
    apply hne
    push Not at ht hd hr
    rw [R.untouched j w ht hr hd]

/-- **Reaching a justification height `h` with `head_height_floor` at most `h` is a
fork-choice change.**

The variables:
- `M`: the model; `F`: its facts.

Read aloud: a validator whose justification reaches the height of its least viable height moves its
root to the new justified block, which is a fork-choice change. -/
theorem change_of_h_j_reaches (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (w : V) (j h : ℕ)
    (hlo : (x.st j w).justifiedHeight < h)
      (hhi : h ≤ (x.st (j + 1) w).justifiedHeight)
    (hfl : M.head_height_floor (x.st (j + 1) w) ≤ h)
    (hJg : (x.st (j + 1) w).justified ≠ Block.genesis) :
    ForkChoiceChangeStep M S A x w j := by
  -- `w`'s honesty after the step: its justification height changes, so the step is `w`'s tick or a
  -- delivery to `w`
  have hv_B3S1_w : w ∉ A.corrupted (j + 1) :=
    (not_mem_corrupted_succ_of_justifiedHeight_ne M F) S A x R E w j
      (by intro heq; unfold Height at *; omega)
  have hjl' := (h_j_lt_h_max_st M F) S A x R E (j + 1) w
  have hmx' := (GoldilocksCorrectness.Record.Proofs.Routines.h_max_le_floor_add_one M F) S.C S.P S.X (x.st (j + 1) w) ((lem11_node_invariant M F S A x R E (j + 1) w hv_B3S1_w).1)
  have hm1 : hMax M S.C (x.st (j + 1) w) = (x.st (j + 1) w).justifiedHeight + 1 := by
    unfold Height at *
    omega
  have hc : M.fg_contest (x.st (j + 1) w) = false := by
    cases hc' : M.fg_contest (x.st (j + 1) w)
    · rfl
    · exfalso
      have hf : M.head_height_floor (x.st (j + 1) w) =
          hMax M S.C (x.st (j + 1) w) := by
        rcases (GoldilocksCorrectness.Record.Proofs.Routines.floor_cases M F) S.C S.P S.X (x.st (j + 1) w) ((lem11_node_invariant M F S A x R E (j + 1) w hv_B3S1_w).1) with ⟨-, -, h⟩ | ⟨h, -⟩
        · exact h
        · rw [hc'] at h; cases h
      unfold Height at *
      omega
  have hroot : M.get_fc_root (x.st (j + 1) w) = (x.st (j + 1) w).justified := by
    rcases (GoldilocksCorrectness.Record.Proofs.Routines.root_cases M F) S.C S.P S.X (x.st (j + 1) w) ((lem11_node_invariant M F S A x R E (j + 1) w hv_B3S1_w).1) with ⟨h, -, -⟩ | ⟨-, h | h⟩
    · exact h
    · rw [hc] at h; cases h
    · exact absurd hm1 h
  left
  refine ⟨hroot, hm1, ?_⟩
  rw [hroot]
  intro hanc
  have hRJ : (M.get_fc_root (x.st j w)).AncestorEq (x.st j w).justified := by
    rcases (GoldilocksCorrectness.Record.Proofs.Routines.root_cases M F) S.C S.P S.X (x.st j w) ((lem11_node_invariant M F S A x R E j w (E.not_mem_corrupted_of_le (Nat.le_succ j) hv_B3S1_w)).1) with ⟨h1, -, -⟩ | ⟨h1, -⟩
    · rw [h1]
      exact ancestorEq_refl _
    · rw [h1]
      exact (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_J_of_exec M F) S A x R E j w
  have h2 := ancestorEq_trans hanc hRJ
  obtain ⟨⟨D', -, hJ', hj'⟩, -, -⟩ := (cachesWitnessed_of_exec M F) S A x R E (j + 1) w
  obtain ⟨⟨D, -, hJ, hj⟩, -, -⟩ := (cachesWitnessed_of_exec M F) S A x R E j w
  have hh1 : 1 ≤ (M.chainStateOf S.C D').h_j := by
    unfold Height at *
    omega
  have hJ'h := ((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_J_spec M F) S.C D').2.2 hh1
  by_cases hj0 : (M.chainStateOf S.C D).h_j = 0
  · have hg := ((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_J_spec M F) S.C D).2.1 hj0
    rw [hJ, hg] at h2
    exact hJg ((ancestorEq_genesis_iff _).1 h2)
  · have hJh := ((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_J_spec M F) S.C D).2.2 (Nat.one_le_iff_ne_zero.mpr hj0)
    rw [hJ', hJ] at h2
    have hle := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C _ _).2.2.2.1 h2
    rw [hJ'h, hJh] at hle
    unfold Height at *
    omega

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDeliveryUpTo SyncedWithinUpTo deadlineUpTo_eq_some)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ)

/-- **A block an honest validator holds before `t` is in a receiver's tree at its tick to `c`.** A block
`D` other than the genesis block, in `u`'s tree before `t` with `u`'s finalized block before `t` an ancestor
of `D` or `D`, `u` outside the adversary set at its last step before `t` and active from `a` through the
sync delay after it, is in `w`'s tree at its tick `kR` to `c`, when `w`'s finalized block there is
compatible with `D`, `w` is active at every step from the real time `a` up to `kR`, and `w` ticked to a
clock value `c₂`, at least the start of `D`'s slot and at least one delay before `c`. Here `GST ≤ a ≤ t`,
`a + max (Δ S) Δs ≤ t + Δ S ≤ c`.

Why: `u` relayed `D` when it entered its tree (`tree_block_relayed_entry`), before `t`. When the relay is
at a real time at least `a`, the delivery promise `delivered` places a delivery before `kR` (its
deadline `max _ GST + ΔNet` is at most `t + Δ S − ΔClockAhead`, `hNet`); otherwise `u` serves `D` at its
last step before `a`, and the sync fact at `a` does (`delivered_before_of_held_upTo_tick`). Both promises
ask the re-delivery premise, which `w`'s tick to `c₂` supplies (`redeliver_before_of_tick`, with
`c₂ + ΔClockBehind + ΔRedeliver ≤ c − ΔClockAhead` by `hRedeliver`); the delivered block enters `w`'s tree
(`mem_tree_of_admitted_delivery`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`, `R`: the setup, the activity, the execution, the run's facts; `GST`: the time from
  which the network is synchronous; `b`: the bound of the delivery premises; `t`: the time `u`'s tree
  is read before; `a`: the start of the windows; `c`, `kR`: the clock value and the step of `w`'s tick;
  `c₂`, `k₂`: those of `w`'s earlier tick; `u`: the holder; `w`: the receiver; `D`: the block.

Read aloud: a block an honest holder has before `t` is in every receiver's tree at its tick to a clock
value at least one delay after `t`, when the receiver is up from `a` and its finalized block is
compatible with the block. -/
theorem block_at_tick_of_held_before (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST b t a c c₂ kR k₂ : ℕ) (u w : V)
    (D : Block V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ}
    (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks b)
    (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST b)
    (hRoots : RootsNameBlocksUntil M A x (x.time kR))
    (hParent : ParentHeldAtDelivery M x)
    (hGSTa : GST ≤ a) (ha : a + max (Δ S) Δs ≤ t + Δ S) (hat : a ≤ t) (htc : t + Δ S ≤ c)
    (hcb : c ≤ b)
    (hu₀ : u ∈ A.activeThroughout x a (a + Δs))
    (hu : u ∉ A.corrupted (x.stepBefore t))
    (hD : D ∈ (x.stateBefore t u).tree)
    (hFu : (x.stateBefore t u).finalized.AncestorEq D)
    (hg : D ≠ Block.genesis)
    (hkR : x.lbl kR = Event.tick w c)
    (hwin : ∀ i : ℕ, (a : ℝ) ≤ x.time i → i ≤ kR → w ∈ A.active i)
    (hk₂ : x.lbl k₂ = Event.tick w c₂) (hc₂ : c₂ + Δ S ≤ c) (hDc₂ : M.slotStart S.C D.slot ≤ c₂)
    (hFw : (x.st kR w).finalized.compatible D = true) :
    D ∈ (x.st kR w).tree := by
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ := one_le_Δ S
  have hR0 : (0 : ℝ) ≤ ΔRedeliver := by positivity
  have hN0 : (0 : ℝ) ≤ ΔNet := by positivity
  have hD' : D ∈ (x.st (x.stepBefore t) u).tree := hD
  have hwkR : w ∉ A.corrupted kR := E.not_mem_corrupted_of_tick hkR
  have hkRt := (E.tick_active kR w c hkR).2.1
  obtain ⟨ie, hie, hsende, hhone, -, hie1⟩ := (tree_block_relayed_entry M F) x R E hD' hg
  have ht1 : 1 ≤ t := by
    -- the relayed entry `ie` comes before `x.stepBefore t`, so the step after it is at a real time less
    -- than `t`, and every real time of the trace is at least `0`
    have h1 := ((lt_stepBefore_iff M) x R E).1 hie
    have h2 := (time_nonneg M) x R (ie + 1)
    exact Nat.cast_pos.1 (lt_of_le_of_lt h2 h1)
  have hk1t := ((stepBefore_time M) x R E ht1).1
  have hieT : x.time (ie + 1) < t :=
    lt_of_le_of_lt (htime (show ie + 1 ≤ x.stepBefore t by omega)) hk1t
  have hcR : (t : ℝ) + Δ S ≤ c := by exact_mod_cast htc
  have hc₂R : (c₂ : ℝ) + Δ S ≤ c := by exact_mod_cast hc₂
  have hsk : x.stepBefore t < kR := (lt_of_time_lt M) x R (by linarith)
  have hprem := redeliver_before_of_tick M F R E (r := M.slotStart S.C D.slot) hk₂ hkR
    (by linarith) hDc₂
  by_cases hlate : (a : ℝ) ≤ x.time (ie + 1)
  · -- the relay from `a` on: the delivery promise
    have hiek : ie < kR := by omega
    have hGSTR : (GST : ℝ) ≤ t := by exact_mod_cast (le_trans hGSTa hat)
    have hmax : max (x.time (ie + 1)) (GST : ℝ) ≤ t := max_le hieT.le hGSTR
    have hbR : (c : ℝ) ≤ b := by exact_mod_cast hcb
    obtain ⟨j, -, hjk, hlj, hadm, -⟩ := E.delivered ie kR w ⟨u, NamedObject.block D⟩ c
      (max (x.time (ie + 1)) GST + ΔNet) ⟨hsende, hhone⟩ trivial hkR hiek
      (fun j h1 h2 => hwin j (le_trans hlate (htime h1)) h2)
      (deadlineUpTo_eq_some.2 ⟨by linarith, rfl⟩) (by linarith)
      (fun r j₀ k₁ t₁ hr _ _ hnr hjk₁ _ hlk₁ _ hfirst => by
        have hr' : M.slotStart S.C D.slot = r := Option.some.inj hr
        subst hr'
        exact hprem j₀ k₁ t₁ hnr hjk₁ hlk₁ hfirst)
    exact (mem_tree_of_admitted_delivery M F U) R E hRoots hParent hu (htime hsk.le) hD' hlj
      (htime hjk.le) (hadm _ rfl (by omega)) hjk hwkR hFw
  · -- the relay before `a`: `u` serves `D` at its last step before `a`, and the sync fact
    push_neg at hlate
    have h0 : (0 : ℝ) ≤ x.time (ie + 1) := (time_nonneg M) x R (ie + 1)
    have ha1 : 1 ≤ a := by
      have : (0 : ℝ) < (a : ℝ) := lt_of_le_of_lt h0 hlate
      exact_mod_cast this
    have hiek : ie < x.stepBefore a := ((lt_stepBefore_iff M) x R E).2 hlate
    obtain ⟨hk1, hk2⟩ := (stepBefore_time M) x R E ha1
    have hΔsR : (0 : ℝ) ≤ Δs := by positivity
    have hvk : u ∈ A.active (x.stepBefore a) :=
      Activity.mem_activeThroughout.1 hu₀ _ (by linarith) hk2
    have hat' : x.stepBefore a ≤ x.stepBefore t := (stepBefore_mono M) x R E hat
    have hkk : x.stepBefore a < kR := by omega
    have hserve : servesMin M S.C (x.st (x.stepBefore a) u) (x.clockValue (x.stepBefore a) u)
        (NamedObject.block D) :=
      ⟨(mem_T_mono M F) x R E u (show ie + 1 ≤ x.stepBefore a by omega) hie1,
        (compatible_iff _ _).2 (Or.inl (ancestorEq_trans ((F_ancestorEq_of_le M F) x R E u hat') hFu)), hg⟩
    have hamax : a + Δs ≤ c := by
      have := le_max_right (Δ S) Δs
      omega
    rcases (delivered_before_of_held_upTo_tick M) x R E Sy (by omega) hvk hk1 hk2 hserve trivial
        (fun i h1 h2 => Activity.mem_activeThroughout.1 hu₀ i h2 (le_trans h1 (htime (Nat.le_succ i))))
        hGSTa hamax hkR (fun i hi hik => hwin i hi hik)
        (fun r j₀ k₁ t₁ hr _ hnr hjk₁ _ hlk₁ _ hfirst => by
          have hr' : M.slotStart S.C D.slot = r := Option.some.inj hr
          subst hr'
          exact hprem j₀ k₁ t₁ hnr hjk₁ hlk₁ hfirst)
      with hw | ⟨j, -, -, -, -, hlj, hjk, hadm, -⟩
    · exact (mem_T_mono M F) x R E w hkk.le hw.1
    · exact (mem_tree_of_admitted_delivery M F U) R E hRoots hParent hu (htime hsk.le) hD' hlj
        (htime hjk.le) (hadm _ rfl (by omega)) hjk hwkR hFw

/-- **A held block reaches a receiver's tick input, or is low** (`held_spread` read at the receiver's
tick). Under `block_at_tick_of_held_before`'s hypotheses, with fewer than a third of the validators in
the adversary set up to `tEnd`, at least the real time of `kR`: either `D` is in `w`'s tree at its tick
`kR` to `c` with `w`'s finalized block there an ancestor of `D` or `D`, or `D`'s chain-state height is at
most `w`'s justification height there.

Why: when `D` is higher than `w`'s justification height at `kR`, `w`'s finalized block there is an
ancestor of `D` (`F_ancestorEq_of_high_st`), so compatible with it, and `block_at_tick_of_held_before`
puts `D` in `w`'s tree.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `tEnd`: the end of the adversary bound; the others as in `block_at_tick_of_held_before`.

Read aloud: a block an honest validator holds before `t` is, at a receiver's tick at least one delay
later, in the receiver's tree on its finalized block's chain, or at most the receiver's justification
height. -/
theorem held_spread_tick (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST b tEnd t a c c₂ kR k₂ : ℕ) (u w : V)
    (D : Block V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ}
    (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks b)
    (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST b)
    (hRoots : RootsNameBlocksUntil M A x (x.time kR))
    (hParent : ParentHeldAtDelivery M x)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tEnd) (hEnd : x.time kR ≤ tEnd)
    (hGSTa : GST ≤ a) (ha : a + max (Δ S) Δs ≤ t + Δ S) (hat : a ≤ t) (htc : t + Δ S ≤ c)
    (hcb : c ≤ b)
    (hu₀ : u ∈ A.activeThroughout x a (a + Δs))
    (hu : u ∉ A.corrupted (x.stepBefore t))
    (hD : D ∈ (x.stateBefore t u).tree)
    (hFu : (x.stateBefore t u).finalized.AncestorEq D)
    (hg : D ≠ Block.genesis)
    (hkR : x.lbl kR = Event.tick w c)
    (hwin : ∀ i : ℕ, (a : ℝ) ≤ x.time i → i ≤ kR → w ∈ A.active i)
    (hk₂ : x.lbl k₂ = Event.tick w c₂) (hc₂ : c₂ + Δ S ≤ c) (hDc₂ : M.slotStart S.C D.slot ≤ c₂) :
    (D ∈ (x.st kR w).tree ∧ (x.st kR w).finalized.AncestorEq D) ∨
      (M.chainStateOf S.C D).h ≤ (x.st kR w).justifiedHeight := by
  by_cases hlt : (x.st kR w).justifiedHeight < (M.chainStateOf S.C D).h
  · have htime : Monotone x.time := fun _ _ h => R.time_mono h
    have hwkR : w ∉ A.corrupted kR := E.not_mem_corrupted_of_tick hkR
    have hD' : D ∈ (x.st (x.stepBefore t) u).tree := hD
    have hA0 := E.ahead_nonneg
    have hB0 := E.behind_nonneg
    have hR0 : (0 : ℝ) ≤ ΔRedeliver := by positivity
    have hkRt := (E.tick_active kR w c hkR).2.1
    have hcR : (t : ℝ) + Δ S ≤ c := by exact_mod_cast htc
    have hst : x.time (x.stepBefore t) ≤ x.time kR := by
      have := (time_stepBefore_le M) x R E t
      linarith
    have hFD := (F_ancestorEq_of_high_st M F Fx) S A x R E hRoots tEnd kR (x.stepBefore t) w u D hThird
      hEnd (le_trans hst hEnd) hwkR hu hD' hlt (max_le le_rfl hst)
    exact Or.inl ⟨block_at_tick_of_held_before M F U S A x R GST b t a c c₂ kR k₂ u w D E hNet hRedeliver
      Sy hRoots hParent hGSTa ha hat htc hcb hu₀ hu hD hFu hg hkR hwin hk₂ hc₂ hDc₂
      ((compatible_iff _ _).2 (Or.inl hFD)), hFD⟩
  · exact Or.inr (Nat.le_of_not_lt hlt)

/-- **No honest validator reaches the height of a later honest proposal's justification one delay
before it.** When `p` proposes `B` at its tick to the start of slot `s + 1`, active at every step from the
real time `max (Δ S) Δs` before `t + Δ` up to that tick and ticking to the view freeze of slot `s`, a validator `u` active from that time through `t` and honest at its last step
before `t`, with `GST + max (Δ S) Δs ≤ t + Δ` and `t + Δ` at most that start, has `h_j` less than
`B`'s chain-state height. At `t = 0` `u`'s state is the initial one; otherwise `held_spread_h_j`
reads `u` at `t + Δ − max (Δ S) Δs` and `p` from then.

Roots name blocks until the time of the proposer's tick to the start of slot `s + 1`: the proposer's
`h_j` is read at that tick's input (`h_j_mono`), after `u`'s justification spreads to it.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: one delay before an honest proposal, every honest justification is lower than it. -/
theorem h_j_lt_of_later_proposal (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tEnd t s : ℕ) (u p : V) (B : Block V)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep p (M.slotStart S.C (s + 1)))))
    (hParent : ParentHeldAtDelivery M x)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tEnd)
    (hGST : GST + max (Δ S) Δs ≤ t + Δ S) (hle : t + Δ S ≤ M.slotStart S.C (s + 1))
      (hEnd : x.time (x.tickStep p (M.slotStart S.C (s + 1))) ≤ tEnd)
    -- `u` is active from `max (Δ S) Δs` before `t + Δ S` through `t + Δ S`, and honest at its last step before `t`
    (hu₀ : u ∈ A.activeThroughout x ((t + Δ S) - (max (Δ S) Δs)) (t + Δ S))
    (hu : u ∉ A.corrupted (x.stepBefore t))
    -- `p` is active at every step from the real time `max (Δ S) Δs` before `t + Δ S` up to its tick to the start of
    -- slot `s + 1`
    (hp : ∀ i : ℕ, (((t + Δ S) - max (Δ S) Δs : ℕ) : ℝ) ≤ x.time i → i ≤ x.tickStep p (M.slotStart S.C (s + 1)) →
      p ∈ A.active i)
    -- `p` ticks to the view freeze of slot `s`
    (hpv : ∃ k : ℕ, x.lbl k = Event.tick p (M.viewFreeze S.C s))
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) :
    (x.stateBefore t u).justifiedHeight < (M.chainStateOf S.C B).h := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ := one_le_Δ S
  have hR0 : (0 : ℝ) ≤ ΔRedeliver := by positivity
  obtain ⟨kv, hkv⟩ := hpv
  have h3 := (honest_proposal_above_h_j M F U Fx) S A x R E s B p hPropose
  obtain ⟨iP, hiP, -⟩ := hPropose
  have hkP : x.tickStep p (M.slotStart S.C (s + 1)) = iP := (tickStep_eq_of_lbl M) x E hiP
  have hIn : x.tickInput p (M.slotStart S.C (s + 1)) = x.st iP p := by
    unfold Trace.tickInput
    rw [hkP]
  rw [hIn] at h3
  rw [hkP] at hRoots hEnd hp
  obtain ⟨⟨D, hD, hJD, hj⟩, -, -⟩ := (cachesWitnessed_of_stateBefore M F) S A x R E t u
  rw [hj]
  have hlt47 := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C D D).1.2.1
  by_cases hg : D = Block.genesis
  · have hh := (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_genesis_h M F) (C := S.C)
    rw [hg] at hlt47 ⊢
    unfold Height at *
    omega
  have hD' : D ∈ (x.st (x.stepBefore t) u).tree := hD
  obtain ⟨ie, hie, -⟩ := (tree_block_relayed_entry M F) x R E hD' hg
  have ht1 : 1 ≤ t := by
    -- the relayed entry `ie` comes before `x.stepBefore t`, so the step after it is at a real time less
    -- than `t`, and every real time of the trace is at least `0`
    have h1 := ((lt_stepBefore_iff M) x R E).1 hie
    have h2 := (time_nonneg M) x R (ie + 1)
    exact Nat.cast_pos.1 (lt_of_le_of_lt h2 h1)
  have hFu : (x.stateBefore t u).finalized.AncestorEq D := by
    have hFJ := (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_J_of_stateBefore M F) S A x R E t u
    rw [hJD] at hFJ
    exact ancestorEq_trans hFJ ((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_J_spec M F) S.C D).1
  -- the block's slot is at most `s`: `u`'s clock before `t` is less than `t + ΔClockAhead`
  have hsl : ∀ t : ℕ, M.slot S.C t = S.C.slot (t : Int) := fun t => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U),
      GoldilocksCorrectness.Proofs.Routines.slot_natCast]
  have hHs := (slot_le_clockValue_of_mem_tree M F) R E hu hD'
  rw [← hsl] at hHs
  have hcv := (clockValue_le_time_add_ahead M F) x R E (x.stepBefore t) u
  have hkt := ((stepBefore_time M) x R E ht1).1
  have hleR : (t : ℝ) + Δ S ≤ M.slotStart S.C (s + 1) := by exact_mod_cast hle
  have hDs : D.slot ≤ s := by
    by_contra hc
    have h1 := ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_le_iff M.toSlotLayout F.sched) S (s + 1)
      (x.clockValue (x.stepBefore t) u)).2 (le_trans (Nat.succ_le_of_lt (not_le.1 hc)) hHs)
    have h2 : ((M.slotStart S.C (s + 1) : ℕ) : ℝ) ≤ x.clockValue (x.stepBefore t) u := by exact_mod_cast h1
    have h4 : max 0 (x.time (x.stepBefore t) + ΔClockAhead) < (t : ℝ) + Δ S :=
      max_lt (by positivity) (by linarith)
    linarith
  have hfr := (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_eq M.toSlotLayout F.sched U) S s
  have hDc₂ : M.slotStart S.C D.slot ≤ M.viewFreeze S.C s := by
    have := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S hDs
    omega
  have hc₂ := (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_add_Δ_le_slotStart_of_lt M.toSlotLayout
    F.sched) S (Nat.lt_succ_self s)
  have hmx1 := le_max_left (Δ S) Δs
  have hu₀' : u ∈ A.activeThroughout x (((t + Δ S) - max (Δ S) Δs : ℕ) : ℝ)
      ((((t + Δ S) - max (Δ S) Δs : ℕ) : ℝ) + Δs) := by
    refine Activity.mem_activeThroughout.2 (fun i h1 h2 => Activity.mem_activeThroughout.1 hu₀ i ?_ ?_)
    · have : (((t + Δ S) - max (Δ S) Δs : ℕ) : ℝ) + Δs ≤ (t : ℝ) + Δ S := by
        have : (t + Δ S) - max (Δ S) Δs + Δs ≤ t + Δ S := by
          have := le_max_right (Δ S) Δs
          omega
        exact_mod_cast this
      push_cast at this ⊢
      linarith
    · have : ((t : ℝ) + Δ S) - (max (Δ S) Δs : ℕ) ≤ (((t + Δ S) - max (Δ S) Δs : ℕ) : ℝ) := by
        have := Nat.sub_add_cancel (show max (Δ S) Δs ≤ t + Δ S by omega)
        have h' : ((((t + Δ S) - max (Δ S) Δs : ℕ) : ℝ)) + (max (Δ S) Δs : ℕ) = (t : ℝ) + Δ S := by
          exact_mod_cast this
        linarith
      push_cast at this ⊢
      linarith
  rcases (held_spread_tick M F U Fx) S A x R GST (M.slotStart S.C (s + 1)) tEnd t ((t + Δ S) - max (Δ S) Δs)
      (M.slotStart S.C (s + 1)) (M.viewFreeze S.C s) iP kv u p D (E.upTo _) hNet hRedeliver (Sy.upTo _) hRoots
      hParent hThird hEnd (by omega) (by omega) (by omega) hle le_rfl hu₀' hu hD hFu hg hiP hp hkv hc₂ hDc₂
    with ⟨hDw, hFw⟩ | hle'
  · have := (GoldilocksCorrectness.Record.Statements.Executions.h_j_of_mem_T_of_exec M F) S A x R E iP p D hDw hFw
    unfold Height at *
    omega
  · unfold Height at *
    omega

omit [RootOrder] in
/-- A chain state whose justification height is at most `1` has the genesis block as its justified
block: at `0` by `chainStateOf_J_spec`; at `1` the justified block is an entry of height `1`, and
the genesis block, an ancestor of it at the same height, has itself as `T_h`.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: nothing but the genesis block is justified at height at most one. -/
theorem J_genesis_of_h_j_le_one (C : Config) (D : Block V) (h1 : (M.chainStateOf C D).h_j ≤ 1) :
    (M.chainStateOf C D).J = Block.genesis := by
  by_cases h0 : (M.chainStateOf C D).h_j = 0
  · exact ((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_J_spec M F) C D).2.1 h0
  · have hh := ((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_J_spec M F) C D).2.2 (Nat.one_le_iff_ne_zero.mpr h0)
    rcases (chainStateOf_J_entry M F) C D with h | h
    · exact h
    · have he := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) C (Block.genesis : Block V) (M.chainStateOf C D).J).2.2.2.2
        (genesis_ancestorEq _) (by
          rw [hh, (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_genesis_h M F)]
          unfold Height at *
          omega)
      rw [h, (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_genesis_T_h M F)] at he
      exact he.symm

/-- **Before the later opening's support cutoff, no honest validator holds a justification at the
waited height `h`, other than the genesis block.** With `t₀ + Δ` the start of the later opening's
slot `s + 1`, whose honest proposer `p` proposes `B₂` at the height `h`; every honest
`head_height_floor` at most `h` from `t₀` to `tc`; `p` ticking to the view freeze of slot `s`; and no honest fork-choice change from `t₀` to before `tc`:
every honest validator at a time from `tL` to `tc` has `h_j < h`, or the genesis block as its
justified block.

Why: up to `t₀`, by `h_j_lt_of_later_proposal` (the windows from `hAw`). After `t₀`, take the first step
`j` from the one after `x.stepBefore t₀` after which `u`'s `h_j` reaches `h` or its `head_height_floor`
exceeds `h` (before it both are within `h`: at `t₀` by the first part and `hF`, and the step
`x.stepBefore t₀` moves the time, so it leaves `u`'s state as it was). The step `j` is a
`ForkChoiceChangeStep`: its `head_height_floor` rises, or `h_j` reaches `h` with `head_height_floor` at most `h`
(`change_of_h_j_reaches`, `h ≥ 2` keeping the justified block off the genesis block). Its time is from
`t₀` to before `tc`, which `hNo` excludes.

Roots name blocks until the real time of `p`'s tick to the start of slot `s + 1`, a time at most
`tEnd`: `h_j_lt_of_later_proposal` at the later opening's slot `s + 1`, the only reading of the premise.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: until the later opening's support cutoff, no honest validator has justified anything at
the waited height. -/
theorem h_j_lt_or_genesis_before_cutoff (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tEnd tL t₀ tc s h : ℕ) (p : V) (B₂ : Block V)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep p (M.slotStart S.C (s + 1)))))
    (hParent : ParentHeldAtDelivery M x)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tEnd)
    (hL0 : tL ≤ t₀) (ht₀ : t₀ + Δ S = M.slotStart S.C (s + 1))
    (hs : M.slotStart S.C (s + 1) ≤ tEnd)
    -- the proposer's tick to the start of slot `s + 1` is at a real time at most `tEnd`
    (hsT : x.time (x.tickStep p (M.slotStart S.C (s + 1))) ≤ tEnd)
    -- from a time `a` after `GST`, at least one delay or one sync delay before `tL + Δ S` and before `tL`,
    -- every validator outside the adversary set is awake through `tEnd`
    (a : ℕ) (hGSTa : GST ≤ a) (ha : a + max (Δ S) Δs ≤ tL + Δ S) (ha₁ : a + 1 ≤ tL)
    (hAw : ∀ (i : ℕ) (v : V), x.time i ≤ tEnd → (a : ℝ) ≤ x.time (i + 1) → v ∉ A.corrupted i → v ∈ A.awake i)
    -- `p` ticks to the view freeze of slot `s`
    (hpv : ∃ k : ℕ, x.lbl k = Event.tick p (M.viewFreeze S.C s))
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C (s + 1)) ∧
      (⟨p, NamedObject.block B₂⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    (hB₂ : (M.chainStateOf S.C B₂).h = h)
    (hF : ∀ (u : V) (t : ℕ), t₀ ≤ t → t ≤ tc → u ∉ A.corruptedAtTime x t →
      M.head_height_floor (x.stateBefore t u) ≤ h)
    (hNo : ∀ (w : V) (j : ℕ), (t₀ : ℝ) ≤ x.time j → x.time j < (tc : ℝ) → w ∉ A.corrupted j →
      ¬ ForkChoiceChangeStep M S A x w j)
    (u : V) (t : ℕ) (hGt : tL ≤ t) (htc' : t ≤ tc) (hu : u ∉ A.corruptedAtTime x (t + Δ S)) :
    (x.stateBefore t u).justifiedHeight < h ∨
      (x.stateBefore t u).justified = Block.genesis := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  obtain ⟨iP, hiP, hsentP⟩ := hPropose
  have huN : u ∉ A.corruptedAtTime x ((t + Δ S : ℕ) : ℝ) := by
    rw [Nat.cast_add]
    exact hu
  have hkP : x.tickStep p (M.slotStart S.C (s + 1)) = iP := (tickStep_eq_of_lbl M) x E hiP
  have hpP : p ∉ A.corrupted iP := E.not_mem_corrupted_of_tick hiP
  have hsTP : x.time iP ≤ tEnd := by rw [← hkP]; exact hsT
  have hsR : ((M.slotStart S.C (s + 1) : ℕ) : ℝ) ≤ tEnd := by exact_mod_cast hs
  -- up to `t₀`: `h_j_lt_of_later_proposal`, with the windows read from `hAw` and `u`'s, `p`'s honesty
  have hW3 : ∀ t', tL ≤ t' → t' ≤ t₀ → t' ≤ t →
      (x.stateBefore t' u).justifiedHeight < h := by
    intro t' h1 h2 h3
    have hmx1 := le_max_left (Δ S) Δs
    have hat' : a ≤ (t' + Δ S) - max (Δ S) Δs := by omega
    have hatR : (a : ℝ) ≤ (((t' + Δ S) - max (Δ S) Δs : ℕ) : ℝ) := by exact_mod_cast hat'
    have hsub : (((t' + Δ S) - max (Δ S) Δs : ℕ) : ℝ) = (t' : ℝ) + Δ S - (max (Δ S) Δs : ℕ) := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    have ht'R : (t' : ℝ) + Δ S ≤ M.slotStart S.C (s + 1) := by
      have : t' + Δ S ≤ M.slotStart S.C (s + 1) := by omega
      exact_mod_cast this
    have htt'R : (t' : ℝ) + Δ S ≤ ((t + Δ S : ℕ) : ℝ) := by
      have : t' + Δ S ≤ t + Δ S := by omega
      exact_mod_cast this
    have hu₀ : u ∈ A.activeThroughout x ((t' + Δ S) - (max (Δ S) Δs)) (t' + Δ S) := by
      refine Activity.mem_activeThroughout.2 (fun i hi1 hi2 => ?_)
      have hui : u ∉ A.corrupted i := (not_mem_corrupted_of_le_time M) x R E huN (by linarith)
      refine Activity.mem_active.2 ⟨hAw i u (by linarith) ?_ hui, hui⟩
      push_cast at hi2 hsub
      linarith
    have hu' : u ∉ A.corrupted (x.stepBefore t') := by
      refine (not_mem_corrupted_of_le_time M) x R E huN ?_
      have := (time_stepBefore_le M) x R E t'
      have : (t' : ℝ) ≤ t := by exact_mod_cast h3
      push_cast
      have : (0 : ℝ) ≤ Δ S := by positivity
      linarith
    have hp' : ∀ i : ℕ, (((t' + Δ S) - max (Δ S) Δs : ℕ) : ℝ) ≤ x.time i →
        i ≤ x.tickStep p (M.slotStart S.C (s + 1)) → p ∈ A.active i := by
      intro i hi1 hi2
      rw [hkP] at hi2
      have hpi : p ∉ A.corrupted i := fun hc => hpP (E.corrupted_mono _ _ hi2 hc)
      exact Activity.mem_active.2 ⟨hAw i p (le_trans (htime hi2) hsTP)
        (le_trans hatR (le_trans hi1 (htime (Nat.le_succ i)))) hpi, hpi⟩
    have := (h_j_lt_of_later_proposal M F U Fx) S A x R GST tEnd t' s u p B₂ E hNet hSkew hRedeliver Sy
      hRoots hParent hThird (by omega) (by omega) hsT hu₀ hu' hp' hpv ⟨iP, hiP, hsentP⟩
    rw [hB₂] at this
    exact this
  by_cases hlt : (x.stateBefore t u).justifiedHeight < h
  · exact Or.inl hlt
  right
  by_contra hJg
  have htt₀ : t₀ < t := by
    by_contra hle
    exact hlt (hW3 t hGt (by omega) le_rfl)
  -- `h ≥ 2`: a justified block other than the genesis block has a justification height at least 2
  obtain ⟨⟨D, -, hJD, hjD⟩, -, -⟩ := (cachesWitnessed_of_stateBefore M F) S A x R E t u
  have hj2 : 2 ≤ (x.stateBefore t u).justifiedHeight := by
    by_contra hlt2
    apply hJg
    rw [hJD]
    exact (J_genesis_of_h_j_le_one M F) S.C D (by rw [← hjD]; unfold Height at *; omega)
  have hut : u ∉ A.corruptedAtTime x t := (not_mem_corruptedAtTime_of_le M) x R E (by omega) huN
  have hflt := hF u t (by omega) htc' hut
  have hjl := (h_j_lt_h_max M F) S A x R E t u
  have hmx := (GoldilocksCorrectness.Record.Proofs.Routines.h_max_le_floor_add_one M F) S.C S.P S.X
    (x.stateBefore t u) ((nodeInv_stateBefore_of_not_mem_corruptedAtTime M F) S A x R E le_rfl hut)
  have hh2 : 2 ≤ h := by
    unfold Height at *
    omega
  -- the step `x.stepBefore t₀` moves the time, so it leaves `u`'s state as it was
  have ht01 : 1 ≤ t₀ := by omega
  obtain ⟨hk0a, hk0b⟩ := (stepBefore_time M) x R E ht01
  have hother : x.lbl (x.stepBefore t₀) = Event.other := by
    by_contra hne
    have := R.time_keep _ hne
    linarith
  have hst0 : x.st (x.stepBefore t₀ + 1) u = x.st (x.stepBefore t₀) u :=
    R.untouched _ u (fun _ hc => by rw [hother] at hc; cases hc)
      (fun _ _ hc => by rw [hother] at hc; cases hc) (fun _ hc => by rw [hother] at hc; cases hc)
  -- the first step from `x.stepBefore t₀ + 1` after which `u`'s `h_j` reaches `h` or its
  -- `head_height_floor` exceeds `h`
  have hP0 : ¬ (h ≤ (x.st (x.stepBefore t₀ + 1) u).justifiedHeight ∨
      h < M.head_height_floor (x.st (x.stepBefore t₀ + 1) u)) := by
    rw [hst0]
    have h1 : (x.st (x.stepBefore t₀) u).justifiedHeight < h := hW3 t₀ hL0 le_rfl htt₀.le
    have h2 : M.head_height_floor (x.st (x.stepBefore t₀) u) ≤ h :=
      hF u t₀ le_rfl (by omega) ((not_mem_corruptedAtTime_of_le M) x R E htt₀.le hut)
    (try unfold Height at *)
    omega
  have hPt : h ≤ (x.st (x.stepBefore t) u).justifiedHeight ∨
      h < M.head_height_floor (x.st (x.stepBefore t) u) := Or.inl (Nat.le_of_not_lt hlt)
  have hk0t : x.stepBefore t₀ + 1 ≤ x.stepBefore t := by
    by_contra hc
    have heq : x.stepBefore t = x.stepBefore t₀ :=
      le_antisymm (by omega) ((stepBefore_mono M) x R E htt₀.le)
    exact hP0 (by rw [hst0, ← heq]; exact hPt)
  classical
  have hex : ∃ n : ℕ, h ≤ (x.st (x.stepBefore t₀ + 1 + n) u).justifiedHeight ∨
      h < M.head_height_floor (x.st (x.stepBefore t₀ + 1 + n) u) :=
    ⟨x.stepBefore t - (x.stepBefore t₀ + 1), by
      rw [show x.stepBefore t₀ + 1 + (x.stepBefore t - (x.stepBefore t₀ + 1)) = x.stepBefore t by omega]
      exact hPt⟩
  have hn := Nat.find_spec hex
  have hnle : Nat.find hex ≤ x.stepBefore t - (x.stepBefore t₀ + 1) :=
    Nat.find_min' hex (by
      rw [show x.stepBefore t₀ + 1 + (x.stepBefore t - (x.stepBefore t₀ + 1)) = x.stepBefore t by omega]
      exact hPt)
  have hn0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0, Nat.add_zero] at hn
    exact hP0 hn
  have hprev := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
  obtain ⟨j, hjdef⟩ : ∃ j, j = x.stepBefore t₀ + 1 + (Nat.find hex - 1) := ⟨_, rfl⟩
  rw [← hjdef] at hprev
  rw [show x.stepBefore t₀ + 1 + Nat.find hex = j + 1 by omega] at hn
  have hlo : (x.st j u).justifiedHeight < h := by
    (try unfold Height at *)
    omega
  have hflo : M.head_height_floor (x.st j u) ≤ h := by
    (try unfold Height at *)
    omega
  -- the step `j` is at a time from `t₀` to before `tc`, at which `u` is honest
  have ht1 : 1 ≤ t := by omega
  have hkt := ((stepBefore_time M) x R E ht1).1
  have hj0 : (t₀ : ℝ) ≤ x.time j := le_trans hk0b (htime (show x.stepBefore t₀ + 1 ≤ j by omega))
  have hjt : x.time j < x.time (x.stepBefore t) + 1 := by
    have := htime (show j ≤ x.stepBefore t by omega)
    linarith
  have hjtc : x.time j < (tc : ℝ) := by
    have h1 := htime (show j ≤ x.stepBefore t by omega)
    have h2 : (t : ℝ) ≤ tc := by exact_mod_cast htc'
    linarith
  have huj : u ∉ A.corrupted j := by
    refine (not_mem_corrupted_of_le_time M) x R E huN ?_
    have h1 := htime (show j ≤ x.stepBefore t by omega)
    push_cast
    have : (0 : ℝ) ≤ Δ S := by positivity
    linarith
  apply hNo u j hj0 hjtc huj
  rcases hn with hhi | hfl
  · by_cases hfl1 : M.head_height_floor (x.st (j + 1) u) ≤ h
    · have hJg₁ : (x.st (j + 1) u).justified ≠ Block.genesis := by
        intro hg
        obtain ⟨⟨D₁, -, hJD₁, hjD₁⟩, -, -⟩ := (cachesWitnessed_of_exec M F) S A x R E (j + 1) u
        have hh1 : 1 ≤ (M.chainStateOf S.C D₁).h_j := by
          rw [← hjD₁]
          unfold Height at *
          omega
        have hJh := ((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_J_spec M F) S.C D₁).2.2 hh1
        rw [← hJD₁, hg] at hJh
        have : (M.chainStateOf S.C (Block.genesis : Block V)).h = 1 :=
          (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_genesis_h M F) S.C
        rw [this, ← hjD₁] at hJh
        unfold Height at *
        omega
      exact (change_of_h_j_reaches M F) S A x R E u j h hlo hhi hfl1 hJg₁
    · exact Or.inr (by (try unfold Height at *); omega)
  · exact Or.inr (by (try unfold Height at *); omega)


/-- **One delay before an honest proposal, every honest justification is lower than it, read at a step**
. When `p` proposes `B` at its tick to the start
of slot `s + 1`, active at every step from the real time `a` up to that tick and ticking to the view freeze of slot `s`,
a validator `u` outside the adversary set at the step `k`, active from `a` through the sync delay after it, with
`GST ≤ a ≤ x.time k`, `a + max (Δ S) Δs` at most the start of slot `s + 1` and `x.time k + Δ S` at most that start, has
`h_j` at `k` less than `B`'s chain-state height.

Why: as `h_j_lt_of_later_proposal`, with the holder read at its step `k` in place of its last step before a natural
time. The block `D` witnessing `u`'s `h_j` at `k` has its slot at most `s` (`u`'s clock at `k` is at most
`x.time k + ΔClockAhead`, less than the start of slot `s + 1`); when `D` is higher than `p`'s `h_j` at its tick,
`p`'s finalized block there is an ancestor of `D` (`F_ancestorEq_of_high_st`) and `block_at_tick_of_held_step` puts `D`
in `p`'s tree (its earlier tick to the view freeze of slot `s` supplies the re-delivery premise), so `D`'s `h_j` is at
most `p`'s; otherwise `D`'s `h_j` is less than its height, at most `p`'s `h_j`; and `p`'s `h_j` is less than `B`'s
height (`honest_proposal_above_h_j`).

Roots name blocks until the time of the proposer's tick to the start of slot `s + 1`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `A`, `x`, `R`: the setup, the activity, the execution, the run's facts; `GST`: the time from which the network
  is synchronous; `tEnd`: the end of the adversary bound; `a`: the start of the windows; `s + 1`: the proposal's slot;
  `k`: the reader's step; `u`: the reader; `p`: the proposer; `B`: the proposal.

Read aloud: one delay before an honest proposal, every honest validator's justification at a step is lower than it. -/
theorem h_j_lt_of_later_proposal_st (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tEnd a s k : ℕ) (u p : V) (B : Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep p (M.slotStart S.C (s + 1)))))
    (hParent : ParentHeldAtDelivery M x)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tEnd)
    (hEnd : x.time (x.tickStep p (M.slotStart S.C (s + 1))) ≤ tEnd)
    -- the windows start at `a`, from `GST` on and at most the real time of `k`; one delay or one sync delay after `a`
    -- is at most the start of slot `s + 1`, and so is one delay after the real time of `k`
    (hGSTa : GST ≤ a) (hak : (a : ℝ) ≤ x.time k) (ha : a + max (Δ S) Δs ≤ M.slotStart S.C (s + 1))
    (hle : x.time k + Δ S ≤ M.slotStart S.C (s + 1))
    -- `u` is active from `a` through the sync delay after it, and outside the adversary set at `k`
    (hu₀ : u ∈ A.activeThroughout x a (a + Δs))
    (hu : u ∉ A.corrupted k)
    -- `p` is active at every step from the real time `a` up to its tick to the start of slot `s + 1`
    (hp : ∀ i : ℕ, (a : ℝ) ≤ x.time i → i ≤ x.tickStep p (M.slotStart S.C (s + 1)) → p ∈ A.active i)
    -- `p` ticks to the view freeze of slot `s`
    (hpv : ∃ k : ℕ, x.lbl k = Event.tick p (M.viewFreeze S.C s))
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) :
    (x.st k u).justifiedHeight < (M.chainStateOf S.C B).h := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ := one_le_Δ S
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  obtain ⟨kv, hkv⟩ := hpv
  have h3 := (honest_proposal_above_h_j M F U Fx) S A x R E s B p hPropose
  obtain ⟨iP, hiP, -⟩ := hPropose
  have hkP : x.tickStep p (M.slotStart S.C (s + 1)) = iP := (tickStep_eq_of_lbl M) x E hiP
  have hIn : x.tickInput p (M.slotStart S.C (s + 1)) = x.st iP p := by
    unfold Trace.tickInput
    rw [hkP]
  rw [hIn] at h3
  rw [hkP] at hRoots hEnd hp
  obtain ⟨⟨D, hD, hJD, hj⟩, -, -⟩ := (cachesWitnessed_of_exec M F) S A x R E k u
  rw [hj]
  have hlt47 := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C D D).1.2.1
  by_cases hg : D = Block.genesis
  · have hh := (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_genesis_h M F) (C := S.C)
    rw [hg] at hlt47 ⊢
    unfold Height at *
    omega
  have hFu : (x.st k u).finalized.AncestorEq D := by
    have hFJ := (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_J_of_exec M F) S A x R E k u
    rw [hJD] at hFJ
    exact ancestorEq_trans hFJ ((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_J_spec M F) S.C D).1
  -- the block's slot is at most `s`: `u`'s clock at `k` is at most `x.time k + ΔClockAhead`
  have hsl : ∀ t : ℕ, M.slot S.C t = S.C.slot (t : Int) := fun t => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U),
      GoldilocksCorrectness.Proofs.Routines.slot_natCast]
  have hHs := (slot_le_clockValue_of_mem_tree M F) R E hu hD
  rw [← hsl] at hHs
  have hcv := (clockValue_le_time_add_ahead M F) x R E k u
  have hk0 := (time_nonneg M) x R k
  have hDs : D.slot ≤ s := by
    by_contra hc
    have h1 := ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_le_iff M.toSlotLayout F.sched) S (s + 1)
      (x.clockValue k u)).2 (le_trans (Nat.succ_le_of_lt (not_le.1 hc)) hHs)
    have h2 : ((M.slotStart S.C (s + 1) : ℕ) : ℝ) ≤ x.clockValue k u := by exact_mod_cast h1
    have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
    have h4 : max 0 (x.time k + ΔClockAhead) < x.time k + Δ S :=
      max_lt (by linarith) (by linarith)
    linarith
  have hfr := (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_eq M.toSlotLayout F.sched U) S s
  have hDc₂ : M.slotStart S.C D.slot ≤ M.viewFreeze S.C s := by
    have := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S hDs
    omega
  have hc₂ := (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_add_Δ_le_slotStart_of_lt M.toSlotLayout
    F.sched) S (Nat.lt_succ_self s)
  -- the reader's step comes before the proposer's tick
  have hiPt := (E.tick_active iP p _ hiP).2.1
  have hkiP : x.time k ≤ x.time iP := by linarith
  have hpi : p ∉ A.corrupted iP := E.not_mem_corrupted_of_tick hiP
  by_cases hlt : (x.st iP p).justifiedHeight < (M.chainStateOf S.C D).h
  · have hFD := (F_ancestorEq_of_high_st M F Fx) S A x R E hRoots tEnd iP k p u D hThird
      hEnd (le_trans hkiP hEnd) hpi hu hD hlt (max_le le_rfl hkiP)
    -- `stepBefore a ≤ k`, so `u`'s finalized block at its last step before `a` is an ancestor of the one at `k`
    have hak' : x.stepBefore a ≤ k := by
      by_contra hc
      have h1 := ((lt_stepBefore_iff M) x R E).1 (show k < x.stepBefore a by omega)
      have h2 := htime (Nat.le_succ k)
      linarith
    have hFa := GoldilocksCorrectness.Proofs.Routines.compatible_of_ancestorEq_compatible
      ((F_ancestorEq_of_le M F) x R E u hak') ((compatible_iff _ _).2 (Or.inl hFu))
    have hstΔ : Δ S ≤ M.slotStart S.C (s + 1) := by
      have : ((Δ S : ℕ) : ℝ) ≤ M.slotStart S.C (s + 1) := by linarith
      exact_mod_cast this
    have htu : x.time k ≤ ((M.slotStart S.C (s + 1) - Δ S : ℕ) : ℝ) := by
      rw [Nat.cast_sub hstΔ]
      linarith
    have hΔN : ΔNet ≤ Δ S := by
      have : (ΔNet : ℝ) ≤ Δ S := by linarith
      exact_mod_cast this
    have hDw := block_at_tick_of_held_step M F U S A x R GST (M.slotStart S.C (s + 1))
      (M.slotStart S.C (s + 1) - Δ S) k a (M.slotStart S.C (s + 1)) (M.viewFreeze S.C s) iP kv u p D
      (E.upTo _) hNet hSkew hRedeliver (Sy.upTo _) hRoots hParent hGSTa ha (by omega) le_rfl hu₀ htu hu hD hFa hg
      hiP hp hkv hc₂ hDc₂ ((compatible_iff _ _).2 (Or.inl hFD))
    have := (GoldilocksCorrectness.Record.Statements.Executions.h_j_of_mem_T_of_exec M F) S A x R E iP p D hDw hFD
    unfold Height at *
    omega
  · unfold Height at *
    omega

/-- **Before the later opening's support cutoff, no honest validator holds a justification at the waited height `h`,
other than the genesis block, read at a step**. With `p` proposing `B₂` at the height `h` at its tick to the start of slot `s + 1`, as in
`h_j_lt_of_later_proposal_st`: a validator `u` outside the adversary set at a step `k` and active from `a` through
the sync delay after it, with an earlier step `k₁ ≤ k` at a real time at least `tL` and at least one delay before the start of slot `s + 1`,
whose `head_height_floor` at `k₁` and at `k` is at most `h` and none of whose steps from `k₁` to before `k` is a
fork-choice change, has `h_j` at `k` less than `h`, or the genesis block as its justified block there.

Why: at `k₁`, `u`'s `h_j` is less than `h` (`h_j_lt_of_later_proposal_st`, the windows from `hAw`, from `a`). When
`u`'s `h_j` at `k` is at least `h` with a justified block other than the genesis block, `h ≥ 2` (`u`'s `h_j` is less
than its greatest chain-state height, at most its `head_height_floor` plus one, at most `h + 1`); take the first step
`j` from `k₁` after which `u`'s `h_j` reaches `h` or its `head_height_floor` exceeds `h`. The step `j` is a
`ForkChoiceChangeStep`: its `head_height_floor` rises, or `h_j` reaches `h` with `head_height_floor` at most `h`
(`change_of_h_j_reaches`, `h ≥ 2` keeping the justified block off the genesis block); `hNo` excludes it.

Restated in place of the earlier step form (twenty-third launch): the floor and the no-change premise are read on the
reader's own steps from its step `k₁`, the steps its proof reads; a premise read at every honest validator's step up
to a time needs, for the callers' no-change facts, a later tick of each such validator, which only the reader is known
to have.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `A`, `x`, `R`: the setup, the activity, the execution, the run's facts; `GST`: the time from which the network
  is synchronous; `tEnd`: the end of the adversary bound and of the awake window; `tL`: the earliest real time of
  `k₁`; `s + 1`: the later proposal's slot; `h`: its chain-state height; `p`: its proposer; `B₂`: the proposal; `a`:
  the start of the windows; `u`: the reader; `k₁ ≤ k`: its two steps.

Read aloud: until the later opening's support cutoff, no honest validator has justified anything at the waited height,
read at any of its steps after an earlier step one delay before the opening at which its floor is at most that
height, with no fork-choice change of its own in between. -/
theorem h_j_lt_or_genesis_before_cutoff_st (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tEnd tL s h : ℕ) (p : V) (B₂ : Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep p (M.slotStart S.C (s + 1)))))
    (hParent : ParentHeldAtDelivery M x)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tEnd)
    (hs : M.slotStart S.C (s + 1) ≤ tEnd)
    -- the proposer's tick to the start of slot `s + 1` is at a real time at most `tEnd`
    (hsT : x.time (x.tickStep p (M.slotStart S.C (s + 1))) ≤ tEnd)
    -- from a time `a` after `GST`, at least one delay or one sync delay before `tL + Δ S` and before `tL`,
    -- every validator outside the adversary set is awake through `tEnd`
    (a : ℕ) (hGSTa : GST ≤ a) (ha : a + max (Δ S) Δs ≤ tL + Δ S) (ha₁ : a + 1 ≤ tL)
    (hAw : ∀ (i : ℕ) (v : V), x.time i ≤ tEnd → (a : ℝ) ≤ x.time (i + 1) → v ∉ A.corrupted i → v ∈ A.awake i)
    -- `p` ticks to the view freeze of slot `s`
    (hpv : ∃ k : ℕ, x.lbl k = Event.tick p (M.viewFreeze S.C s))
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C (s + 1)) ∧
      (⟨p, NamedObject.block B₂⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    (hB₂ : (M.chainStateOf S.C B₂).h = h)
    -- the reader `u`, outside the adversary set at its step `k` and active from `a` through `a + Δs`; its earlier step
    -- `k₁`, at a real time at least `tL` and at least one delay before the start of slot `s + 1`
    (u : V) (k₁ k : ℕ) (hk₁k : k₁ ≤ k) (hGt : (tL : ℝ) ≤ x.time k₁)
    (hk₁s : x.time k₁ + Δ S ≤ M.slotStart S.C (s + 1))
    (hu : u ∉ A.corrupted k) (hu₀ : u ∈ A.activeThroughout x a (a + Δs))
    -- `u`'s `head_height_floor` at `k₁` and at `k` is at most `h`
    (hF₁ : M.head_height_floor (x.st k₁ u) ≤ h) (hF : M.head_height_floor (x.st k u) ≤ h)
    -- no step of `u` from `k₁` to before `k` is a fork-choice change
    (hNo : ∀ j : ℕ, k₁ ≤ j → j < k → ¬ ForkChoiceChangeStep M S A x u j) :
    (x.st k u).justifiedHeight < h ∨ (x.st k u).justified = Block.genesis := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ := one_le_Δ S
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  obtain ⟨iP, hiP, hsentP⟩ := hPropose
  have hkP : x.tickStep p (M.slotStart S.C (s + 1)) = iP := (tickStep_eq_of_lbl M) x E hiP
  have hpP : p ∉ A.corrupted iP := E.not_mem_corrupted_of_tick hiP
  have hsTP : x.time iP ≤ tEnd := by rw [← hkP]; exact hsT
  have hsR : ((M.slotStart S.C (s + 1) : ℕ) : ℝ) ≤ tEnd := by exact_mod_cast hs
  have hmx1 := le_max_left (Δ S) Δs
  have hmx2 := le_max_right (Δ S) Δs
  -- `u` is outside the adversary set at `k` and at `k₁`
  have hk₁t := htime hk₁k
  have huk : u ∉ A.corrupted k := hu
  have huk₁ : u ∉ A.corrupted k₁ := E.not_mem_corrupted_of_le hk₁k hu
  -- `p` is active at every step from `a` up to its tick
  have hp' : ∀ i : ℕ, (a : ℝ) ≤ x.time i → i ≤ x.tickStep p (M.slotStart S.C (s + 1)) → p ∈ A.active i := by
    intro i hi1 hi2
    rw [hkP] at hi2
    have hpi : p ∉ A.corrupted i := fun hc => hpP (E.corrupted_mono _ _ hi2 hc)
    exact Activity.mem_active.2 ⟨hAw i p (le_trans (htime hi2) hsTP)
      (le_trans hi1 (htime (Nat.le_succ i))) hpi, hpi⟩
  have hatL : ((a + max (Δ S) Δs : ℕ) : ℝ) ≤ (tL : ℝ) + Δ S := by exact_mod_cast ha
  push_cast at hatL
  -- at `k₁`: the step form of `h_j_lt_of_later_proposal`
  have hW₁ : (x.st k₁ u).justifiedHeight < h := by
    have hak : (a : ℝ) ≤ x.time k₁ := by
      have : ((a + 1 : ℕ) : ℝ) ≤ tL := by exact_mod_cast ha₁
      push_cast at this
      linarith
    have ha' : a + max (Δ S) Δs ≤ M.slotStart S.C (s + 1) := by
      have : ((a + max (Δ S) Δs : ℕ) : ℝ) ≤ ((M.slotStart S.C (s + 1) : ℕ) : ℝ) := by
        push_cast
        linarith
      exact_mod_cast this
    have := (h_j_lt_of_later_proposal_st M F U Fx) S A x R GST tEnd a s k₁ u p B₂ E hNet hSkew hRedeliver Sy
      hRoots hParent hThird hsT hGSTa hak ha' hk₁s hu₀ huk₁ hp' hpv ⟨iP, hiP, hsentP⟩
    rw [hB₂] at this
    exact this
  by_cases hlt : (x.st k u).justifiedHeight < h
  · exact Or.inl hlt
  right
  by_contra hJg
  -- `h ≥ 2`: a justified block other than the genesis block has a justification height at least 2
  obtain ⟨⟨D, -, hJD, hjD⟩, -, -⟩ := (cachesWitnessed_of_exec M F) S A x R E k u
  have hj2 : 2 ≤ (x.st k u).justifiedHeight := by
    by_contra hlt2
    apply hJg
    rw [hJD]
    exact (J_genesis_of_h_j_le_one M F) S.C D (by rw [← hjD]; unfold Height at *; omega)
  have hjl := (h_j_lt_h_max_st M F) S A x R E k u
  have hmx := (GoldilocksCorrectness.Record.Proofs.Routines.h_max_le_floor_add_one M F) S.C S.P S.X
    (x.st k u) ((lem11_node_invariant M F S A x R E k u huk).1)
  have hh2 : 2 ≤ h := by
    unfold Height at *
    omega
  -- the first step from `k₁` after which `u`'s `h_j` reaches `h` or its `head_height_floor` exceeds `h`
  have hP0 : ¬ (h ≤ (x.st k₁ u).justifiedHeight ∨ h < M.head_height_floor (x.st k₁ u)) := by
    (try unfold Height at *)
    omega
  have hPt : h ≤ (x.st k u).justifiedHeight ∨ h < M.head_height_floor (x.st k u) :=
    Or.inl (Nat.le_of_not_lt hlt)
  classical
  have hex : ∃ n : ℕ, h ≤ (x.st (k₁ + n) u).justifiedHeight ∨ h < M.head_height_floor (x.st (k₁ + n) u) :=
    ⟨k - k₁, by
      rw [show k₁ + (k - k₁) = k by omega]
      exact hPt⟩
  have hn := Nat.find_spec hex
  have hnle : Nat.find hex ≤ k - k₁ :=
    Nat.find_min' hex (by
      rw [show k₁ + (k - k₁) = k by omega]
      exact hPt)
  have hn0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0, Nat.add_zero] at hn
    exact hP0 hn
  have hprev := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
  obtain ⟨j, hjdef⟩ : ∃ j, j = k₁ + (Nat.find hex - 1) := ⟨_, rfl⟩
  rw [← hjdef] at hprev
  rw [show k₁ + Nat.find hex = j + 1 by omega] at hn
  have hlo : (x.st j u).justifiedHeight < h := by
    (try unfold Height at *)
    omega
  have hflo : M.head_height_floor (x.st j u) ≤ h := by
    (try unfold Height at *)
    omega
  apply hNo j (by omega) (by omega)
  rcases hn with hhi | hfl
  · by_cases hfl1 : M.head_height_floor (x.st (j + 1) u) ≤ h
    · have hJg₁ : (x.st (j + 1) u).justified ≠ Block.genesis := by
        intro hg
        obtain ⟨⟨D₁, -, hJD₁, hjD₁⟩, -, -⟩ := (cachesWitnessed_of_exec M F) S A x R E (j + 1) u
        have hh1 : 1 ≤ (M.chainStateOf S.C D₁).h_j := by
          rw [← hjD₁]
          unfold Height at *
          omega
        have hJh := ((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_J_spec M F) S.C D₁).2.2 hh1
        rw [← hJD₁, hg] at hJh
        have : (M.chainStateOf S.C (Block.genesis : Block V)).h = 1 :=
          (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_genesis_h M F) S.C
        rw [this, ← hjD₁] at hJh
        unfold Height at *
        omega
      exact (change_of_h_j_reaches M F) S A x R E u j h hlo hhi hfl1 hJg₁
    · exact Or.inr (by (try unfold Height at *); omega)
  · exact Or.inr (by (try unfold Height at *); omega)


end GoldilocksCorrectness.Record.Proofs.Executions

