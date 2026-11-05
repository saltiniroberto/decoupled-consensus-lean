module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89Count
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89ChangeJ
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89StabilityJ
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.FGStateReaders
public import GoldilocksCorrectness.Proofs.Executions.Lemma89CountJ
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma89CountJ, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma89CountJ.lean`, over a model `M` whose
facts `F` hold, for an execution `x` of `protocolOf M S`: the steps of the climb's count, namely the
kit for a node state read right after a time `t` by a validator honest at `t`, a held block's
spreading with its consequences for the justification height and the greatest chain-state height, a
contested FG state staying contested, the bundle `ClimbCtx` of the count's hypotheses with its
readers, and `fork_choice_change_kinds`, every fork-choice change of the climb being one of four
kinds. The page's routine-level theorems are the facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ)
open GoldilocksCorrectness.Proofs.Routines (slot_mono slot_mono_int)

open GoldilocksCorrectness.Proofs.Routines (block_admissible_of mem_T_receive_block)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax IsEntry VoterTreeAt JustifiedInTree AnchorAt)

open GoldilocksCorrectness.Record.Statements.Routines (JustificationCertOn)

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
  genesis_ancestorEq ancestorEq_compatible ancestorEq_antisymm)
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn expireLocks)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-! ## Honesty at the time of a configuration -/

/-- A validator honest at `t` is honest at the time of the configuration `stepBefore M x t`, which
is at most `t`.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `w`: the validator; `t`: the time.

Read aloud: a validator honest at `t` is honest at the time of the configuration `stepBefore M x t`.
-/
theorem honest_config {S : Setup V} {A : Activity V} (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) {w : V} {t : ℕ} (hw : w ∉ A.corruptedAtTime x t) :
    w ∉ A.corrupted (x.stepBefore t) := by
  exact (not_mem_corrupted_of_le_time M) x R E hw ((time_stepBefore_le M) x R E t)

/-! ## The kit with honesty at the configuration's time -/

/-- `F_ancestorEq_of_high` with the two validators honest at the times of the configurations their
states are read from (`stepBefore M x t`, `stepBefore M x t'`), rather than at `t` and `t'`. The
proof is the landed one.

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tEnd`: the time up to which the
  adversary bound holds; `t`, `t'`: the two times; `w`, `p`: the two validators; `B`: the block.

Roots name blocks until `tR`, at least `max t t'`: the proof compares (Lemma 89a) a block `w`
holds before `t` with `B`, which `p` holds before `t'`.

Read aloud: when `B`, held by `p`, is higher than `w`'s justification height, `w`'s finalized block
is an ancestor of `B` or `B`, each validator honest at the time of the configuration its state is
read from. -/
theorem F_ancestorEq_of_high_at (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {tR : ℕ} (hRoots : RootsNameBlocksUntil M A x tR)
    (tEnd t t' : ℕ) (w p : V) (B : Block V)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tEnd) (ht : t ≤ tEnd)
      (ht' : t' ≤ tEnd)
    (hw : w ∉ A.corrupted (x.stepBefore t))
    (hp : p ∉ A.corrupted (x.stepBefore t'))
    (hB : B ∈ (x.stateBefore t' p).tree)
    (hlt : (x.stateBefore t w).justifiedHeight < (M.chainStateOf S.C B).h)
    -- the latest time the proof takes a block as held is at most the bound
    (htR : max t t' ≤ tR) :
    (x.stateBefore t w).finalized.AncestorEq B := by
  obtain ⟨D, hD, hF⟩ := (finalizedFromChain_of_exec M F) S A x R E (x.stepBefore t) w
  have hSt : x.stateBefore t w = x.st (x.stepBefore t) w := rfl
  rw [← hSt] at hD hF
  by_cases h0 : (M.chainStateOf S.C D).h_F = 0
  · rw [hF, (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_F_genesis M F) S.C D h0]
    exact genesis_ancestorEq B
  have hFD : (M.chainStateOf S.C D).F.AncestorEq D :=
    (((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) S.C D).2.2
      (Nat.one_le_iff_ne_zero.mpr h0)).2.2.1
  have hjD : (M.chainStateOf S.C D).h_j ≤ (x.stateBefore t w).justifiedHeight :=
    (GoldilocksCorrectness.Record.Statements.Executions.h_j_of_mem_T_of_stateBefore M F) S A x R E t w D hD (by rw [hF]; exact hFD)
  have hFj := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C D D).1.2.2
  have hlt' : (M.chainStateOf S.C D).h_F < (M.chainStateOf S.C B).h :=
    lt_of_le_of_lt hFj (lt_of_le_of_lt hjD hlt)
  have hti := (time_stepBefore_le M) x R E t
  have htj := (time_stepBefore_le M) x R E t'
  have hT : A.AdversaryFewerThanThirdUntil x (validator_count V)
      (max (x.time (x.stepBefore t)) (x.time (x.stepBefore t'))) :=
    hThird.mono (max_le (hti.trans (by exact_mod_cast ht)) (htj.trans (by exact_mod_cast ht')))
  have htR' : max (x.time (x.stepBefore t)) (x.time (x.stepBefore t')) ≤ (tR : ℝ) :=
    le_trans (max_le_max hti htj) (by rw [← Nat.cast_max]; exact_mod_cast htR)
  have h68 := (lem68_honest_past_finalized M F Fx) S A x R E hRoots (x.stepBefore t)
    (x.stepBefore t') w p D B hT hw hp hD hB hlt' htR'
  rw [hF]
  exact h68

/-- `eq_of_cert_same_height` with the two holders honest at the times of the configurations their
states are read from. The proof is the landed one.

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tEnd`, `t`, `t'`: the times;
  `p`, `w`: the two holders; `B₁`, `B₂`: the blocks carrying the certificates; `h`: the height;
  `T`, `T'`: the justified blocks.

Roots name blocks until `tR`, at least `max t t'`: the proof compares `T`, held by `p` before
`t`, with `T'`, held by `w` before `t'`.

Read aloud: two justified blocks at one height, certified on blocks held by two honest validators,
are one block, each holder honest at the time of the configuration its state is read from. -/
theorem eq_of_cert_same_height_at (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {tR : ℕ}
      (hRoots : RootsNameBlocksUntil M A x tR)
    (tEnd t t' : ℕ) (p w : V) (B₁ B₂ T T' : Block V) (h : Height)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tEnd) (ht : t ≤ tEnd)
      (ht' : t' ≤ tEnd)
    (hp : p ∉ A.corrupted (x.stepBefore t))
    (hw : w ∉ A.corrupted (x.stepBefore t'))
    (hB₁ : B₁ ∈ (x.stateBefore t p).tree) (hB₂ : B₂ ∈ (x.stateBefore t' w).tree)
    (hJ : JustificationCertOn M B₁ h T)
    (hJ' : JustificationCertOn M B₂ h T')
    (hT : T ∈ (x.stateBefore t p).tree) (hT' : T' ∈ (x.stateBefore t' w).tree)
    -- the latest time the proof takes a block as held is at most the bound
    (htR : max t t' ≤ tR) :
    T = T' := by
  have hti := (time_stepBefore_le M) x R E t
  have htj := (time_stepBefore_le M) x R E t'
  have hA : A.AdversaryFewerThanThirdUntil x (validator_count V)
      (max (x.time (x.stepBefore t)) (x.time (x.stepBefore t'))) :=
    hThird.mono (max_le (hti.trans (by exact_mod_cast ht)) (htj.trans (by exact_mod_cast ht')))
  have hroot := (lem76_honest_one_justification M F Fx) S A x R E (x.stepBefore t) (x.stepBefore t') p w
    hA B₁ B₂ hB₁ hB₂ h T T' hJ hJ'
  have htR₁ : (t : ℝ) ≤ tR := by exact_mod_cast le_trans (le_max_left _ _) htR
  have htR₂ : (t' : ℝ) ≤ tR := by exact_mod_cast le_trans (le_max_right _ _) htR
  exact hRoots T T' ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := x.stepBefore t) (v := p) hp (le_trans hti htR₁) hT)
    ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := x.stepBefore t') (v := w) hw (le_trans htj htR₂) hT') hroot

/-- `J_eq_of_h_j_eq` with the two validators honest at the times of the configurations their states
are read from. The proof is the landed one.

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tEnd`, `t`, `t'`: the times;
  `p`, `q`: the two validators.

Roots name blocks until `tR`, at least `max t t'`: `eq_of_cert_same_height_at` at the times `t`
and `t'`.

Read aloud: two honest validators with the same justification height have the same justified block,
each honest at the time of the configuration its state is read from. -/
theorem J_eq_of_h_j_eq_at (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {tR : ℕ} (hRoots : RootsNameBlocksUntil M A x tR) (tEnd t t' : ℕ) (p q : V)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tEnd) (ht : t ≤ tEnd)
      (ht' : t' ≤ tEnd)
    (hp : p ∉ A.corrupted (x.stepBefore t))
    (hq : q ∉ A.corrupted (x.stepBefore t'))
    (heq : (x.stateBefore t p).justifiedHeight = (x.stateBefore t' q).justifiedHeight)
    -- the latest time the proof takes a block as held is at most the bound
    (htR : max t t' ≤ tR) :
    (x.stateBefore t p).justified = (x.stateBefore t' q).justified := by
  by_cases h0 : (x.stateBefore t p).justifiedHeight = 0
  · rw [(J_genesis M F) S A x R E t p h0, (J_genesis M F) S A x R E t' q (heq ▸ h0)]
  have h1 : 1 ≤ (x.stateBefore t p).justifiedHeight := Nat.one_le_iff_ne_zero.mpr h0
  obtain ⟨W, hW, hc⟩ := (J_cert M F) S A x R E t p h1
  obtain ⟨W', hW', hc'⟩ := (J_cert M F) S A x R E t' q (heq ▸ h1)
  rw [← heq] at hc'
  exact (eq_of_cert_same_height_at M F Fx) S A x R E hRoots tEnd t t' p q W W' _ _ _ hThird ht ht'
    hp hq hW hW' hc hc' ((J_mem_T M F) S A x R E t p) ((J_mem_T M F) S A x R E t' q) htR

open GoldilocksCorrectness.Proofs.Routines (one_le_Δ) in
open GoldilocksCorrectness.Statements.AbstractTrace (deadlineUpTo_eq_some EnvFactsDeliveryUpTo SyncedWithinUpTo) in
/-- **A block an honest validator holds at a step is in a receiver's tree at its tick to `c`, with the delivery premises
read at the deadline.** `block_at_tick_of_held_step` with its bound `c ≤ b` on the receiver's clock value replaced by what
its proof reads of it: the relay's delivery deadline, at most `tu + ΔNet`, and the sync window's end `a + Δs`, at most `b`
(F-P1-17: a receiver's clock value can exceed the real time of a step before `b` by up to `ΔClockAhead`, its deadline cannot).

The holder-at-a-step twin of `block_at_tick_of_held_tick`: a block `D` other than the genesis block, in
`u`'s tree at a step `kU` whose real time is at most the real number `tu`, `u` outside the adversary set
at `kU`, active from `a` through the sync delay after it and its finalized block at its last step before
`a` compatible with `D`, is in `w`'s tree at its tick `kR` to `c`, when `w`'s finalized block there is
compatible with `D`, `w` is active at every step from the real time `a` up to `kR`, and `w` ticked to a
clock value `c₂`, at least the start of `D`'s slot and at least one delay before `c`. Here `GST ≤ a`,
`a + max (Δ S) Δs ≤ c`, `tu + ΔNet + ΔClockAhead ≤ c`, `tu + ΔClockAhead < c`, `tu + ΔNet ≤ b` and `a + Δs ≤ b`.

The two bounds on `c` are what the proof reads of the earlier
`tu + Δ S ≤ c`; a caller holding that bound gets both from `hNet` and `hSkew`.

Why: as `block_at_tick_of_held_tick`, with the relay's real time at most `tu` (the relay is at or before
`kU`): the delivery promise's deadline `max _ GST + ΔNet` is at most `tu + ΔNet ≤ c − ΔClockAhead`
(`hcuNet`), and `kU` comes before `kR` (its real time is at most `tu`, less than `c − ΔClockAhead`,
`hcuAhead`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`, `R`: the setup, the activity, the execution, the run's facts; `GST`: the time from
  which the network is synchronous; `b`: the bound of the delivery premises; `tu`: a real number
  at least the real time of `kU`, the holder's step; `a`: the start of the windows; `c`, `kR`: the
  clock value and the step of `w`'s tick; `c₂`, `k₂`: those of `w`'s earlier tick; `u`: the holder;
  `w`: the receiver; `D`: the block.

Read aloud: a block an honest holder has at a step by the real time `tu` is in every receiver's tree at
its tick to a clock value at least one delay after `tu`, when the receiver is up from `a`, the holder is
up for one sync delay after `a`, and the receiver's finalized block is compatible with the block. -/
theorem block_at_tick_of_held_step_deadline (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST b : ℕ) (tu : ℝ) (kU a c c₂ kR k₂ : ℕ) (u w : V)
    (D : Block V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ}
    (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks b)
    (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST b)
    (hRoots : RootsNameBlocksUntil M A x (x.time kR))
    (hParent : ParentHeldAtDelivery M x)
    (hGSTa : GST ≤ a) (ha : a + max (Δ S) Δs ≤ c)
    -- T-C-82-3 (re-check 81 section 4.2): the two bounds the proof reads, in place of `tu + Δ S ≤ c`
    (hcuNet : tu + ΔNet + ΔClockAhead ≤ c) (hcuAhead : tu + ΔClockAhead < c)
    (hcb : tu + ΔNet ≤ b) (hab : a + Δs ≤ b)
    (hu₀ : u ∈ A.activeThroughout x a (a + Δs))
    (htu : x.time kU ≤ tu) (hu : u ∉ A.corrupted kU)
    (hD : D ∈ (x.st kU u).tree)
    (hFa : (x.st (x.stepBefore a) u).finalized.compatible D = true)
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
  have hwkR : w ∉ A.corrupted kR := E.not_mem_corrupted_of_tick hkR
  have hkRt := (E.tick_active kR w c hkR).2.1
  have hkUt : x.time kU ≤ tu := htu
  obtain ⟨ie, hie, hsende, hhone, -, hie1⟩ := (tree_block_relayed_entry M F) x R E hD hg
  have hc₂R : (c₂ : ℝ) + Δ S ≤ c := by exact_mod_cast hc₂
  have hmaxR : ((a : ℕ) : ℝ) + Δ S ≤ c := by
    have h1 : a + Δ S ≤ c := le_trans (Nat.add_le_add_left (le_max_left _ _) a) ha
    exact_mod_cast h1
  have hsk : kU < kR := (lt_of_time_lt M) x R (by linarith)
  have hprem := redeliver_before_of_tick M F R E (r := M.slotStart S.C D.slot) hk₂ hkR
    (by linarith) hDc₂
  by_cases hlate : (a : ℝ) ≤ x.time (ie + 1)
  · -- the relay from `a` on: the delivery promise
    have hiek : ie < kR := by omega
    have hieT : x.time (ie + 1) ≤ x.time kU := htime (show ie + 1 ≤ kU by omega)
    have hGSTR : (GST : ℝ) ≤ a := by exact_mod_cast hGSTa
    have hmax : max (x.time (ie + 1)) (GST : ℝ) ≤ tu :=
      max_le (by linarith) (by linarith)
    have hbR : (tu : ℝ) + ΔNet ≤ b := hcb
    obtain ⟨j, -, hjk, hlj, hadm, -⟩ := E.delivered ie kR w ⟨u, NamedObject.block D⟩ c
      (max (x.time (ie + 1)) GST + ΔNet) ⟨hsende, hhone⟩ trivial hkR hiek
      (fun j h1 h2 => hwin j (le_trans hlate (htime h1)) h2)
      (deadlineUpTo_eq_some.2 ⟨by linarith, rfl⟩) (by linarith)
      (fun r j₀ k₁ t₁ hr _ _ hnr hjk₁ _ hlk₁ _ hfirst => by
        have hr' : M.slotStart S.C D.slot = r := Option.some.inj hr
        subst hr'
        exact hprem j₀ k₁ t₁ hnr hjk₁ hlk₁ hfirst)
    exact (mem_tree_of_admitted_delivery M F U) R E hRoots hParent hu (htime hsk.le) hD hlj
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
    have hkk : x.stepBefore a < kR := (lt_of_time_lt M) x R (by linarith)
    have hserve : servesMin M S.C (x.st (x.stepBefore a) u) (x.clockValue (x.stepBefore a) u)
        (NamedObject.block D) :=
      ⟨(mem_T_mono M F) x R E u (show ie + 1 ≤ x.stepBefore a by omega) hie1, hFa, hg⟩
    have hamax : a + Δs ≤ c := by
      have := le_max_right (Δ S) Δs
      omega
    rcases (delivered_before_of_held_upTo_tick M) x R E Sy hab hvk hk1 hk2 hserve trivial
        (fun i h1 h2 => Activity.mem_activeThroughout.1 hu₀ i h2 (le_trans h1 (htime (Nat.le_succ i))))
        hGSTa hamax hkR (fun i hi hik => hwin i hi hik)
        (fun r j₀ k₁ t₁ hr _ hnr hjk₁ _ hlk₁ _ hfirst => by
          have hr' : M.slotStart S.C D.slot = r := Option.some.inj hr
          subst hr'
          exact hprem j₀ k₁ t₁ hnr hjk₁ hlk₁ hfirst)
      with hw | ⟨j, -, -, -, -, hlj, hjk, hadm, -⟩
    · exact (mem_T_mono M F) x R E w hkk.le hw.1
    · exact (mem_tree_of_admitted_delivery M F U) R E hRoots hParent hu (htime hsk.le) hD hlj
        (htime hjk.le) (hadm _ rfl (by omega)) hjk hwkR hFw

/-- Block propagation from an earlier holder, with the holder `u` active at the window's start `t₀` and
honest at the step `stepBefore M x t₁` its tree is read from, rather than active through `t₁`, and the
receiver `w` read at its tick `kR` to a clock value `c` at least one delay after `t`; under the delivery
promise and the sync fact up to `t + Δ S`.

Restated: the receiver is read at its own tick to `c` with `t + Δ S ≤ c`, active at every
step from the real time `t₀` up to that tick, and with an earlier tick to a clock value `c₂` at least the start of
`B`'s slot and at least one delay before `c` (the re-delivery premise's input); a tick to `c` is at a real time of
`[c − ΔClockAhead, c + ΔClockBehind]`, so the earlier text, at the real time `t + Δ S`, is false when
`ΔClockBehind > 0` with the window exactly one delay long. The roots are read until the real time of `kR`.

Why: `block_at_tick_of_held_step_deadline`, with the holder's step `stepBefore M x t₁` (at a real time at most `t₁`)
and its finalized block at its last step before `t₀` an ancestor of the one before `t₁`, so compatible with `B`;
the genesis block is in every tree.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `x`: the execution; `GST`: the time from which
  the network is synchronous; `t₁ ≤ t`: the two times; `t₀`: the window's start; `u`: the holder; `w`: the receiver;
  `B`: the block; `c`, `kR`: the clock value and the step of `w`'s tick; `c₂`, `k₂`: those of `w`'s earlier tick.

Read aloud: a block held and served by `u` before `t₁` is held, at its tick to a clock value at least one delay
after `t`, by every validator active from `t₀` up to that tick whose finalized block there is compatible with it. -/
theorem mem_T_before_add_delay_of_held_at_upTo (U : UniformSchedule M.toSlotLayout) {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x)

    {GST : ℕ} {t : ℕ}
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (t + Δ S)) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : GoldilocksCorrectness.Statements.AbstractTrace.SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (t + Δ S))
    {kR c k₂ c₂ : ℕ}
    (hRoots : RootsNameBlocksUntil M A x (x.time kR))
    (hParent : ParentHeldAtDelivery M x)
    {t₁ : ℕ} {u w : V} {B : Block V}
    (ht₁t : t₁ ≤ t) (t₀ : ℕ) (hGST : GST ≤ t₀) (ht₀₁ : t₀ ≤ t₁)
    (hu₀ : u ∈ A.activeThroughout x t₀ (t₀ + Δs))
    (hu : u ∉ A.corrupted (x.stepBefore t₁))
    (hsel : (x.stateBefore t₁ u).finalized.compatible B = true)
    (hB : B ∈ (x.stateBefore t₁ u).tree)
    -- `w` ticks to `c`, at least one delay after `t`, active at every step from the real time `t₀` up to that tick
    (hc : t + Δ S ≤ c) (hkR : x.lbl kR = Event.tick w c)
    (hwR : ∀ i : ℕ, (t₀ : ℝ) ≤ x.time i → i ≤ kR → w ∈ A.active i)
    -- `w` ticked to `c₂`, at least the start of `B`'s slot and at least one delay before `c`
    (hk₂ : x.lbl k₂ = Event.tick w c₂) (hc₂ : c₂ + Δ S ≤ c) (hBc₂ : M.slotStart S.C B.slot ≤ c₂)
    (ht₀ : t₀ + max (Δ S) Δs ≤ t + Δ S)
    (hcompat : (x.st kR w).finalized.compatible B = true) :
    B ∈ (x.st kR w).tree := by
  by_cases hg : B = Block.genesis
  · subst hg
    exact (genesis_mem_T_of_exec M F) S A x R E kR w
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔN : ΔNet ≤ Δ S := by
    have : (ΔNet : ℝ) ≤ Δ S := by linarith
    exact_mod_cast this
  have hmx1 := le_max_left (Δ S) Δs
  have hmx2 := le_max_right (Δ S) Δs
  have hFa := GoldilocksCorrectness.Proofs.Routines.compatible_of_ancestorEq_compatible
    ((F_ancestorEq_of_le M F) x R E u ((stepBefore_mono M) x R E ht₀₁)) hsel
  -- the two bounds on `c` (T-C-82-3) from `t₁ + Δ S ≤ c` (by `ht₁t` and `hc`), `hNet`, `hSkew` and `0 ≤ ΔClockBehind`
  have hcu : (t₁ : ℝ) + Δ S ≤ c := by exact_mod_cast (show t₁ + Δ S ≤ c by omega)
  exact block_at_tick_of_held_step_deadline M F U S A x R GST (t + Δ S) (t₁ : ℝ) (x.stepBefore t₁) t₀ c c₂ kR k₂ u w B
    E hRedeliver Sy hRoots hParent hGST (by omega)
    (by linarith) (by linarith) (by exact_mod_cast (show t₁ + ΔNet ≤ t + Δ S by omega))
    (by omega) hu₀
    ((time_stepBefore_le M) x R E t₁) hu hB hFa hg hkR hwR hk₂ hc₂ hBc₂ hcompat

/-- A configuration at a time at least `t` is from the step `x.stepBefore t` on.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `t`: the time; `j`: the step.

Read aloud: a step at a time at least `t` is no earlier than the last step before `t`. -/
theorem stepBefore_le_of_le_time_st {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N}
    (R : RunFacts M S x) {deadline} {release ΔRedeliver}
    {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {t j : ℕ} (hj : (t : ℝ) ≤ x.time j) : x.stepBefore t ≤ j := by
  rcases Nat.eq_zero_or_pos t with h0 | h1
  · subst h0
    rw [(stepBefore_zero M) x R]
    exact Nat.zero_le j
  · exact ((stepBefore_lt_of_le_time M) x R E h1 hj).le

/-- **A validator outside the adversary set at a step is outside it at every step at an earlier time.**
A step at an earlier time comes earlier (`lt_of_time_lt`), and corruption is permanent (`corrupted_mono`,
a field of the condition on executions `EnvFactsBy`).

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `w`: the validator; `i`, `j`: the steps.

Read aloud: a validator honest at a step was honest at every step at an earlier time. -/
theorem not_mem_corrupted_of_time_lt {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N}
    (R : RunFacts M S x) {deadline} {release ΔRedeliver}
    {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {w : V} {i j : ℕ} (hw : w ∉ A.corrupted j) (hij : x.time i < x.time j) : w ∉ A.corrupted i :=
  fun h => hw (E.corrupted_mono i j ((lt_of_time_lt M) x R hij).le h)

/-- **A validator honest at a step at a time at least `t₀ ≥ tGAT` is active at `x.stepBefore t₀`,** when
every validator outside the adversary set is awake from `tGAT` through `tAwakeEnd` (at least the step's
time). It is honest there (an earlier step), and awake: awake at the first step at a time at least
`t₀` (the phase's premise), and the step into that one is of the kind `other` when `t₀ ≥ 1` (it moves
the time), so not a restart (`restart_of_awake`, a field of the condition on executions `EnvFactsBy`).

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `tGAT`, `tAwakeEnd`: the phase; `t₀`: the time; `u`: the validator; `j`: the
  step.

Read aloud: a validator honest inside the phase is active at the step before every time of the phase
up to that step's time. -/
theorem mem_active_stepBefore_of_honest_st {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N}
    (R : RunFacts M S x) {deadline} {release ΔRedeliver}
    {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {tGAT tAwakeEnd : ℕ}
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) → v ∉ A.corrupted i → v ∈ A.awake i)
    {t₀ : ℕ} (ht₀ : tGAT ≤ t₀) {u : V} {j : ℕ} (hu : u ∉ A.corrupted j) (hj : (t₀ : ℝ) ≤ x.time j)
    (hjE : x.time j ≤ tAwakeEnd) : u ∈ A.active (x.stepBefore t₀) := by
  have hij : x.stepBefore t₀ ≤ j := (stepBefore_le_of_le_time_st M F) R E hj
  have hui : u ∉ A.corrupted (x.stepBefore t₀) := fun h => hu (E.corrupted_mono _ _ hij h)
  have htime : x.time (x.stepBefore t₀) ≤ tAwakeEnd := le_trans (R.time_mono hij) hjE
  have hnext : (tGAT : ℝ) ≤ x.time (x.stepBefore t₀ + 1) := by
    have h2 := (le_time_stepBefore_succ M) x R E t₀
    have h3 : (tGAT : ℝ) ≤ t₀ := by exact_mod_cast ht₀
    linarith
  exact Activity.mem_active.2 ⟨hAwake _ u htime hnext hui, hui⟩

/-- **A held block reaches every honest awake validator by its tick one delay later, or is low.** From
`GST` on, with the execution assumptions and unforgeability: when `u`, honest at the step `stepBefore M x t₁`
(`t₁ ≤ t`), holds `D` before `t₁`, and `w` ticks at `kR` to a clock value `c` at least one delay after `t`, active
from `a` up to that tick, then at `kR` either `w` holds `D` with its finalized block `D` or an ancestor of `D`, or
`D`'s chain-state height is at most `w`'s cache `h_j`.

Restated: the receiver is read at its tick `kR` (`x.st kR w`) rather than before the real
time `t + Δ S`, which a tick to `t + Δ S` can follow by up to `ΔClockBehind`; the roots are read until the real time
of `kR`, and `tEnd` is at least that time.

Why: when `D` is higher than `w`'s `h_j` at `kR`, `w`'s finalized block there is an ancestor of `D`
(`F_ancestorEq_of_high_st`), so compatible with it, and the network delivers `D` by that tick
(`mem_T_before_add_delay_of_held_at_upTo`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `A`, `x`: the setup, the activity, the execution; `GST`, `tEnd`, `t₁`, `t`: the times;
  `u`: the holder; `w`: the receiver; `D`: the block; `c`, `kR`: the clock value and the step of `w`'s tick;
  `c₂`, `k₂`: those of `w`'s earlier tick.

Read aloud: a block an honest validator holds is held, at its tick one delay later, by every awake honest
validator with its finalized block `D` or an ancestor of `D`, or has chain-state height at most that
validator's justification height. -/
theorem held_spread (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (GST tEnd t₁ t kR c k₂ c₂ : ℕ) (u w : V) (D : Block V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hRoots : RootsNameBlocksUntil M A x (x.time kR))
    (hParent : ParentHeldAtDelivery M x)
    -- `a` is from `GST` on, at least one delay or one sync delay before `t + Δ S`, and at or before `t₁`
    (a : ℕ) (hGSTa : GST ≤ a) (ha : a + max (Δ S) Δs ≤ t + Δ S) (ha₁ : a ≤ t₁)
    -- the holder `u` is active from `a` through the sync delay after it
    (hu₀ : u ∈ A.activeThroughout x a (a + Δs))
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tEnd)
    (ht₁t : t₁ ≤ t) (hEnd : x.time kR ≤ tEnd)
    (hu : u ∉ A.corrupted (x.stepBefore t₁))
    (hD : D ∈ (x.stateBefore t₁ u).tree)
    -- `u` serves `D`: its finalized block before `t₁` is compatible with `D`
    (hsel : (x.stateBefore t₁ u).finalized.compatible D = true)
    -- the receiver `w` ticks to `c`, at least one delay after `t`, active at every step from the real time `a` up to
    -- that tick; it ticked to `c₂`, at least the start of `D`'s slot and at least one delay before `c`
    (hc : t + Δ S ≤ c) (hkR : x.lbl kR = Event.tick w c)
    (hwR : ∀ i : ℕ, (a : ℝ) ≤ x.time i → i ≤ kR → w ∈ A.active i)
    (hk₂ : x.lbl k₂ = Event.tick w c₂) (hc₂ : c₂ + Δ S ≤ c) (hDc₂ : M.slotStart S.C D.slot ≤ c₂) :
    (D ∈ (x.st kR w).tree ∧ (x.st kR w).finalized.AncestorEq D)
      ∨
      (M.chainStateOf S.C D).h ≤ (x.st kR w).justifiedHeight := by
  by_cases hlt : (x.st kR w).justifiedHeight < (M.chainStateOf S.C D).h
  · have hwkR : w ∉ A.corrupted kR := E.not_mem_corrupted_of_tick hkR
    have hD' : D ∈ (x.st (x.stepBefore t₁) u).tree := hD
    have hst : x.time (x.stepBefore t₁) ≤ x.time kR := by
      have h1 := (time_stepBefore_le M) x R E t₁
      have h2 := (E.tick_active kR w c hkR).2.1
      have hA0 := E.ahead_nonneg
      have hB0 := E.behind_nonneg
      have hΔ := GoldilocksCorrectness.Proofs.Routines.one_le_Δ S
      have h3 : (t₁ : ℝ) + Δ S ≤ c := by exact_mod_cast (show t₁ + Δ S ≤ c by omega)
      have h4 : (0 : ℝ) < Δ S := by exact_mod_cast hΔ
      linarith
    have hFD := (F_ancestorEq_of_high_st M F Fx) S A x R E hRoots tEnd kR (x.stepBefore t₁) w u D hThird
      hEnd (le_trans hst hEnd) hwkR hu hD' hlt (max_le le_rfl hst)
    refine Or.inl ⟨?_, hFD⟩
    exact (mem_T_before_add_delay_of_held_at_upTo M F U R) (E.upTo _) hNet hSkew hRedeliver (Sy.upTo _) hRoots hParent ht₁t
      a hGSTa ha₁ hu₀ hu hsel hD hc hkR hwR hk₂ hc₂ hDc₂ ha ((compatible_iff _ _).2 (Or.inl hFD))
  · exact Or.inr (Nat.le_of_not_lt hlt)

/-- **A held block's justification height reaches every honest awake validator's `h_j` by its tick one
delay later.** Under `held_spread`'s hypotheses, `D`'s justification height is at most `w`'s `h_j` at its
tick `kR`: when `w` holds `D` on its finalized block's chain, by the cache (Lemma 57); otherwise `D`'s
justification height is less than its height (Lemma 47), at most `w`'s `h_j`.

Restated: at `w`'s tick `kR`, as `held_spread`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- the others as in `held_spread`.

Read aloud: a held block's justification height is, at a receiver's tick one delay later, at most every awake
honest validator's justification height. -/
theorem held_spread_h_j (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (GST tEnd t₁ t kR c k₂ c₂ : ℕ) (u w : V) (D : Block V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hRoots : RootsNameBlocksUntil M A x (x.time kR))
    (hParent : ParentHeldAtDelivery M x)
    -- `a` is from `GST` on, at least one delay or one sync delay before `t + Δ S`, and at or before `t₁`
    (a : ℕ) (hGSTa : GST ≤ a) (ha : a + max (Δ S) Δs ≤ t + Δ S) (ha₁ : a ≤ t₁)
    -- the holder `u` is active from `a` through the sync delay after it
    (hu₀ : u ∈ A.activeThroughout x a (a + Δs))
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tEnd)
    (ht₁t : t₁ ≤ t) (hEnd : x.time kR ≤ tEnd)
    (hu : u ∉ A.corrupted (x.stepBefore t₁))
    (hD : D ∈ (x.stateBefore t₁ u).tree)
    -- `u` serves `D`: its finalized block before `t₁` is compatible with `D`
    (hsel : (x.stateBefore t₁ u).finalized.compatible D = true)
    -- the receiver `w` ticks to `c`, at least one delay after `t`, active at every step from the real time `a` up to
    -- that tick; it ticked to `c₂`, at least the start of `D`'s slot and at least one delay before `c`
    (hc : t + Δ S ≤ c) (hkR : x.lbl kR = Event.tick w c)
    (hwR : ∀ i : ℕ, (a : ℝ) ≤ x.time i → i ≤ kR → w ∈ A.active i)
    (hk₂ : x.lbl k₂ = Event.tick w c₂) (hc₂ : c₂ + Δ S ≤ c) (hDc₂ : M.slotStart S.C D.slot ≤ c₂) :
    (M.chainStateOf S.C D).h_j ≤ (x.st kR w).justifiedHeight := by
  rcases (held_spread M F) U Fx S A x R GST tEnd t₁ t kR c k₂ c₂ u w D E hNet hSkew hRedeliver Sy hRoots hParent
    a hGSTa ha ha₁ hu₀ hThird ht₁t hEnd hu hD hsel hc hkR hwR hk₂ hc₂ hDc₂ with ⟨hDw, hFD⟩ | hle
  · exact (GoldilocksCorrectness.Record.Statements.Executions.h_j_of_mem_T_of_exec M F) S A x R E kR w D hDw hFD
  · have h47 := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C D D).1.2.1
    unfold Height at *
    omega

/-- **A held block's height reaches every honest awake validator's greatest chain-state height by its
tick one delay later.** Under `held_spread`'s hypotheses, `D`'s chain-state height is at most `w`'s
greatest chain-state height at its tick `kR`: a held block is at most the greatest chain-state height
(Lemma 46), and `h_j` is less than the greatest chain-state height.

Restated: at `w`'s tick `kR`, as `held_spread`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- the others as in `held_spread`.

Read aloud: a held block's chain-state height is, at a receiver's tick one delay later, at most every awake
honest validator's greatest chain-state height. -/
theorem held_spread_h_max (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (GST tEnd t₁ t kR c k₂ c₂ : ℕ) (u w : V) (D : Block V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hRoots : RootsNameBlocksUntil M A x (x.time kR))
    (hParent : ParentHeldAtDelivery M x)
    -- `a` is from `GST` on, at least one delay or one sync delay before `t + Δ S`, and at or before `t₁`
    (a : ℕ) (hGSTa : GST ≤ a) (ha : a + max (Δ S) Δs ≤ t + Δ S) (ha₁ : a ≤ t₁)
    -- the holder `u` is active from `a` through the sync delay after it
    (hu₀ : u ∈ A.activeThroughout x a (a + Δs))
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tEnd)
    (ht₁t : t₁ ≤ t) (hEnd : x.time kR ≤ tEnd)
    (hu : u ∉ A.corrupted (x.stepBefore t₁))
    (hD : D ∈ (x.stateBefore t₁ u).tree)
    -- `u` serves `D`: its finalized block before `t₁` is compatible with `D`
    (hsel : (x.stateBefore t₁ u).finalized.compatible D = true)
    -- the receiver `w` ticks to `c`, at least one delay after `t`, active at every step from the real time `a` up to
    -- that tick; it ticked to `c₂`, at least the start of `D`'s slot and at least one delay before `c`
    (hc : t + Δ S ≤ c) (hkR : x.lbl kR = Event.tick w c)
    (hwR : ∀ i : ℕ, (a : ℝ) ≤ x.time i → i ≤ kR → w ∈ A.active i)
    (hk₂ : x.lbl k₂ = Event.tick w c₂) (hc₂ : c₂ + Δ S ≤ c) (hDc₂ : M.slotStart S.C D.slot ≤ c₂) :
    (M.chainStateOf S.C D).h ≤ hMax M S.C (x.st kR w) := by
  rcases (held_spread M F) U Fx S A x R GST tEnd t₁ t kR c k₂ c₂ u w D E hNet hSkew hRedeliver Sy hRoots hParent
    a hGSTa ha ha₁ hu₀ hThird ht₁t hEnd hu hD hsel hc hkR hwR hk₂ hc₂ hDc₂ with ⟨hDw, -⟩ | hle
  · exact le_hMax M hDw
  · have h := (h_j_lt_h_max_st M F) S A x R E kR w
    unfold Height at *
    omega

/-! ## A contested FG state -/

/-- **A contested state stays contested while its greatest chain-state height stays.** Under
unforgeability, roots naming blocks, permanent corruption and fewer than a third of the validators
in the adversary set up to `tEnd`: when `w` is honest at `t` with `t₂ ≤ t ≤ tEnd`, its FG state
before `t₂` is contested, and its greatest chain-state height before `t` is the one before `t₂`,
then its FG state before `t` is contested.

Why: `h_j` does not decrease and stays less than the greatest chain-state height, so it stays; so
does the justified block (Lemma 76); the contesting block stays held, and the finalized block before
`t` is an ancestor of it, being higher than `h_j` (Lemma 89a).

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tEnd`, `t₂ ≤ t`: the times; `w`: the
  validator.

Roots name blocks until `tR`, at least `t`: the proof compares blocks `w` holds before `t₂ ≤ t`
and before `t` (`h_j_mono`, Lemma 76, Lemma 89a).

Read aloud: an honest validator's contested FG state stays contested while its greatest chain-state
height stays the same. -/
theorem contest_persists (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {tR : ℕ}
      (hRoots : RootsNameBlocksUntil M A x tR)
    (tEnd t₂ t : ℕ) (w : V)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tEnd)
    (h2t : t₂ ≤ t) (ht : t ≤ tEnd) (hw : w ∉ A.corruptedAtTime x t)
    (hc : M.fg_contest (x.stateBefore t₂ w) = true)
    (hm : hMax M S.C (x.stateBefore t w) = hMax M S.C (x.stateBefore t₂ w))
    -- the latest time the proof takes a block as held is at most the bound
    (htR : t ≤ tR) :
    M.fg_contest (x.stateBefore t w) = true := by
  obtain ⟨hm2, Ab, hA, hFA, hAh, hJA⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.fg_contest_spec M F) S.C S.P S.X _ ((nodeInv_stateBefore_of_not_mem_corruptedAtTime M F) S A x R E h2t hw) hc
  have hw2 : w ∉ A.corruptedAtTime x t₂ := (not_mem_corruptedAtTime_of_le M) x R E (by exact_mod_cast h2t) hw
  have hjm := (h_j_mono M F Fx) S A x R E hRoots tEnd t₂ t w hThird h2t ht hw htR
  have hjl := (h_j_lt_h_max M F) S A x R E t w
  have hjeq : (x.stateBefore t w).justifiedHeight = (x.stateBefore t₂ w).justifiedHeight := by
    unfold Height at *
    omega
  have hJ := (J_eq_of_h_j_eq M F Fx) S A x R E hRoots tEnd t t₂ w w hThird ht (le_trans h2t ht)
    hw hw2 hjeq (max_le htR (by omega))
  have hAt : Ab ∈ (x.stateBefore t w).tree := ((stateBefore_grows M F) x R E w h2t).1 hA
  have hFA' := (F_ancestorEq_of_high M F Fx) S A x R E hRoots tEnd t t₂ w w Ab hThird ht
    (le_trans h2t ht) hw hw2 hA (by rw [hAh, hm2, hjeq]; exact Nat.lt_succ_self _)
    (max_le htR (by omega))
  refine (GoldilocksCorrectness.Record.Proofs.Routines.fg_contest_true_of M F) S.C S.P S.X _ ((nodeInv_stateBefore_of_not_mem_corruptedAtTime M F) S A x R E le_rfl hw) Ab (by rw [hm, hm2, hjeq]) hAt hFA' ?_ ?_
  · rw [hAh, hm]
  · rw [hJ]
    exact hJA

/-! ## The first time of a kind of change -/

omit [RootOrder] in
/-- **A level reached within one delay of its first holder is crossed only then.** For a
predicate `Lv w t` on validators and times (a level of `w`'s state before `t`): when a validator
`u` honest at a time `τ ≥ T₁` with `Lv u (τ + 1)` makes every validator `w` honest at a time
`t ≥ τ + 1 + d` before `a` satisfy `Lv w (τ + 1 + d)` (`hspread`), and the level, once reached
from `T₁ + d` on, stays reached up to a time before `a` at which `w` is honest (`hmono`), then
there is a time `τ` such that every crossing of the level (`¬ Lv w t`, `Lv w (t + 1)`) at a
validator honest at `t`, with `T₁ + d ≤ t < a`, is at a time from `τ` to `τ + d`.

Why: `τ` is the least time from `T₁` at which some validator honest then has the level right
after (`Nat.find`); a crossing later than `τ + d` would find the level reached already.

The variables:
- `M`: the model; `F`: its facts;
- `Sched`: the schedule; `Lv`: the level; `T₁`, `d`, `a`: the times.

Read aloud: a level that spreads within `d` and persists is crossed by honest validators only within
`d` after some time `τ`. -/
theorem kind_time (A : Activity V) (x : Trace V (NamedObject V) M.N) (Lv : V → ℕ → Prop) (T₁ d a : ℕ)
    (hspread : ∀ (τ : ℕ) (u w : V) (t : ℕ), T₁ ≤ τ → u ∉ A.corruptedAtTime x τ →
      Lv u (τ + 1) → τ + 1 + d ≤ t → t < a → w ∉ A.corruptedAtTime x t → Lv w (τ + 1 + d))
    (hmono : ∀ (w : V) (t₂ t : ℕ), T₁ + d ≤ t₂ → t₂ ≤ t → t < a → w ∉ A.corruptedAtTime x t →
      Lv w t₂ → Lv w t) :
    ∃ τ : ℕ, ∀ (w : V) (t : ℕ), T₁ + d ≤ t → t < a → w ∉ A.corruptedAtTime x t →
      ¬ Lv w t → Lv w (t + 1) → τ ≤ t ∧ t ≤ τ + d := by
  classical
  by_cases hex : ∃ τ : ℕ, T₁ ≤ τ ∧ ∃ u : V, u ∉ A.corruptedAtTime x τ ∧ Lv u (τ + 1)
  · refine ⟨Nat.find hex, ?_⟩
    intro w t ht1 hta hw hn hy
    have hle : Nat.find hex ≤ t := Nat.find_min' hex ⟨by omega, w, hw, hy⟩
    refine ⟨hle, ?_⟩
    by_contra hgt
    obtain ⟨hT, u, hu, hL⟩ := Nat.find_spec hex
    have hsp := hspread (Nat.find hex) u w t hT hu hL (by omega) hta hw
    exact hn (hmono w (Nat.find hex + 1 + d) t (by omega) (by omega) hta hw hsp)
  · refine ⟨0, ?_⟩
    intro w t ht1 _ hw _ hy
    exact absurd ⟨t, by omega, w, hw, hy⟩ hex

/-! ## The climb's context -/

omit [RootOrder] in
/-- **A level spreading within `d` from its first holder is crossed only before the tick to `τ + d`, per step.**
For a level `Lv w j` of `w`'s configuration at the step `j`, two honesty predicates, `honH w j` for a holder and
`honR w j` for a crossing validator (the receiver of a spread), the clock value `clk w j` of `w` after `j` steps and the
relation `tick w k c` (step `k` is `w`'s tick to the clock value `c`): when a crossing step (`¬ Lv w j`, `Lv w (j + 1)`)
of a validator with `honR w j` gives `honH w (j + 1)` and keeps the time (`hkeep`), and a validator with `honH u k` at a
step `k` whose time is after `T₁` and at most a clock value `τ`, whose clock value there is at most `τ`, with the level
there makes every validator with `honR w j` at a step `j` at or after its tick to `τ + d`, before `a`, have the level
there (`hspread`), then there is a clock value `τ` such that every crossing step of a validator `w` with `honR w j`, at a
time after `T₁` and before `a`, comes before `w`'s tick to `τ + d`, with `τ` at most every natural number that is at
least both that time and `w`'s clock value just after the step, and `τ` greater than `T₁`.

Why: `τ` is the least natural number at least the time and the clock value of a step after `T₁` at which some
validator with `honH` has the level (`Nat.find`), so it is greater than `T₁`; a crossing at or after the crossing
validator's tick to `τ + d` would find the level there already. No `Nat.floor`, no `Nat.ceil`, no unit offset.

The variables:
- `time`: the time of each step; `clk`: the clock value of each validator after each step; `tick`: the
  tick relation; `honH`, `honR`: the honesty of a holder and of a crossing validator; `Lv`: the level; `T₁`, `d`,
  `a`: the clock values.

Read aloud: a level that spreads to every crossing validator by its tick to `τ + d` is crossed, step by step, only
before the crossing validator's tick to `τ + d`, for some clock value `τ`. -/
theorem kind_time_step (time : ℕ → ℝ) (clk : V → ℕ → ℕ) (tick : V → ℕ → ℕ → Prop)
    (honH honR : V → ℕ → Prop) (Lv : V → ℕ → Prop) (T₁ d a : ℕ)
    (hkeep : ∀ (w : V) (j : ℕ), honR w j → ¬ Lv w j → Lv w (j + 1) →
      honH w (j + 1) ∧ time (j + 1) = time j)
    (hspread : ∀ (τ : ℕ) (u : V) (k : ℕ), (T₁ : ℝ) < time k → time k ≤ τ → clk u k ≤ τ → honH u k → Lv u k →
      ∀ (w : V) (j kT : ℕ), tick w kT (τ + d) → kT ≤ j → time j < a → honR w j → Lv w j) :
    ∃ τ : ℕ, ∀ (w : V) (j : ℕ), (T₁ : ℝ) < time j → time j < a → honR w j →
      ¬ Lv w j → Lv w (j + 1) →
      (∀ n : ℕ, time j ≤ n → clk w (j + 1) ≤ n → τ ≤ n) ∧ (∀ kT : ℕ, tick w kT (τ + d) → j < kT) ∧ T₁ < τ := by
  classical
  by_cases hex : ∃ n : ℕ, ∃ (k : ℕ) (u : V), (T₁ : ℝ) < time k ∧ time k ≤ n ∧ clk u k ≤ n ∧ honH u k ∧ Lv u k
  · refine ⟨Nat.find hex, ?_⟩
    intro w j h1 h2 hw hn hy
    obtain ⟨hw1, ht1⟩ := hkeep w j hw hn hy
    obtain ⟨k, u, hk1, hk2, hk3, hu, hL⟩ := Nat.find_spec hex
    refine ⟨fun n hn' hc => Nat.find_min' hex ⟨j + 1, w, by rw [ht1]; exact h1, by rw [ht1]; exact hn', hc,
      hw1, hy⟩, fun kT hkT => ?_, by exact_mod_cast lt_of_lt_of_le hk1 hk2⟩
    by_contra hge
    push Not at hge
    exact hn (hspread (Nat.find hex) u k hk1 hk2 hk3 hu hL w j kT hkT hge h2 hw)
  · refine ⟨0, ?_⟩
    intro w j h1 _ hw hn hy
    obtain ⟨hw1, ht1⟩ := hkeep w j hw hn hy
    obtain ⟨n, hn'⟩ := exists_nat_ge (time j)
    exact absurd ⟨max n (clk w (j + 1)), j + 1, w, by rw [ht1]; exact h1,
      by rw [ht1]; exact le_trans hn' (by exact_mod_cast le_max_left _ _), le_max_right _ _, hw1, hy⟩ hex

omit [RootOrder] in
/-- **A level spreading within `d` from its first holder is crossed only at or after a real start, and before the
crossing validator's tick to any clock value at least that start plus `A + d`.** The real-valued twin of
`kind_time_step`: for the same level `Lv`, honesty predicates `honH`, `honR`, clock values `clk` and tick relation
`tick`, with the real time `time` monotone and every clock value at most `max 0 (time k + A)` (`A ≥ 0`, the clock's
lead), there is a real time `τ` after `T₁` such that every crossing step of a validator `w` with `honR w j`, at a time
after `T₁` and before `a`, is at a real time at least `τ` and before every tick of `w` to a clock value at least
`τ + A + d`.

Why: `τ` is the real time of the first step after `T₁` at which some validator with `honH` has the level
(`Nat.find` over the steps); a crossing is at or after it (the crossing's successor step has the level and the same
time). For a tick of `w` to `c' ≥ τ + A + d`, the clock value `c' − d` is at least that first step's real time and
its holder's clock value there (at most its real time plus `A`), so `hspread` at `c' − d` gives the level at every
step from that tick on; a crossing there would find it already. No `Nat.floor`, no `Nat.ceil`, no unit offset.

The variables:
- `time`: the time of each step; `clk`: the clock value of each validator after each step; `tick`: the
  tick relation; `honH`, `honR`: the honesty of a holder and of a crossing validator; `Lv`: the level; `T₁`, `d`,
  `a`: the clock values; `A`: the clock's lead.

Read aloud: a level that spreads to every crossing validator by its tick to `τ + d` is crossed, step by step, only
at or after the real time it was first held, and before the crossing validator's tick to any clock value at least
that time plus `A + d`. -/
theorem kind_time_step_real (time : ℕ → ℝ) (clk : V → ℕ → ℕ) (tick : V → ℕ → ℕ → Prop)
    (honH honR : V → ℕ → Prop) (Lv : V → ℕ → Prop) (T₁ d a : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (htime : Monotone time) (hclk : ∀ (u : V) (k : ℕ), (clk u k : ℝ) ≤ max 0 (time k + A))
    (hkeep : ∀ (w : V) (j : ℕ), honR w j → ¬ Lv w j → Lv w (j + 1) →
      honH w (j + 1) ∧ time (j + 1) = time j)
    (hspread : ∀ (τ : ℕ) (u : V) (k : ℕ), (T₁ : ℝ) < time k → time k ≤ τ → clk u k ≤ τ → honH u k → Lv u k →
      ∀ (w : V) (j kT : ℕ), tick w kT (τ + d) → kT ≤ j → time j < a → honR w j → Lv w j) :
    ∃ τ : ℝ, ∀ (w : V) (j : ℕ), (T₁ : ℝ) < time j → time j < a → honR w j →
      ¬ Lv w j → Lv w (j + 1) →
      τ ≤ time j ∧ (∀ (kT c' : ℕ), tick w kT c' → τ + A + d ≤ c' → j < kT) ∧ (T₁ : ℝ) < τ := by
  classical
  by_cases hex : ∃ k : ℕ, ∃ u : V, (T₁ : ℝ) < time k ∧ honH u k ∧ Lv u k
  · refine ⟨time (Nat.find hex), ?_⟩
    intro w j h1 h2 hw hn hy
    obtain ⟨hw1, ht1⟩ := hkeep w j hw hn hy
    obtain ⟨u, hk1, hu, hL⟩ := Nat.find_spec hex
    have hmin : Nat.find hex ≤ j + 1 := Nat.find_min' hex ⟨w, by rw [ht1]; exact h1, hw1, hy⟩
    have hτj : time (Nat.find hex) ≤ time j := by
      have := htime hmin
      rw [ht1] at this
      exact this
    refine ⟨hτj, fun kT c' hkT hc' => ?_, hk1⟩
    by_contra hge
    push Not at hge
    have hT0 : (0 : ℝ) ≤ T₁ := by exact_mod_cast Nat.zero_le T₁
    have hdc : d ≤ c' := by
      have : (d : ℝ) ≤ c' := by linarith
      exact_mod_cast this
    have hcast : ((c' - d : ℕ) : ℝ) = (c' : ℝ) - d := by
      rw [Nat.cast_sub hdc]
    have hτc : time (Nat.find hex) ≤ ((c' - d : ℕ) : ℝ) := by rw [hcast]; linarith
    have hclkc : clk u (Nat.find hex) ≤ c' - d := by
      have h := hclk u (Nat.find hex)
      have : (clk u (Nat.find hex) : ℝ) ≤ ((c' - d : ℕ) : ℝ) := by
        refine le_trans h (max_le ?_ ?_)
        · exact_mod_cast Nat.zero_le _
        · rw [hcast]; linarith
      exact_mod_cast this
    have htick : tick w kT (c' - d + d) := by rw [Nat.sub_add_cancel hdc]; exact hkT
    exact hn (hspread (c' - d) u (Nat.find hex) hk1 hτc hclkc hu hL w j kT htick hge h2 hw)
  · refine ⟨0, ?_⟩
    intro w j h1 _ hw hn hy
    obtain ⟨hw1, ht1⟩ := hkeep w j hw hn hy
    exact absurd ⟨j + 1, w, by rw [ht1]; exact h1, hw1, hy⟩ hex

/-- `ClimbCtx M S Sched x GST tGAT tAwakeEnd T₁ r H₂ k₀`: the hypotheses of `fork_choice_change_kinds`
that its proof reads: the execution assumptions, unforgeability, every validator honest in the
phase awake then, fewer than a third in the adversary set up to its end, the threshold `H₂` at `T₁`
and every honest attestation before `aR M S r` at most `H₂`.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the
  times; `T₁`: the time of the threshold; `r`: the round; `H₂`: the threshold.

Roots name blocks until `aR M S r`: every reader of the bundle compares blocks held before times at
most `aR M S r`, the end of the climb.

Read aloud: the hypotheses of `fork_choice_change_kinds` that its proof reads. -/
structure ClimbCtx (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)
    (GST tGAT tAwakeEnd T₁ r H₂ : ℕ) (k₀ : ℕ) (Δs : ℕ) (release : (NamedObject V) → Option ℕ) (ΔRedeliver : ℕ) (ΔClockAhead ΔClockBehind : ℝ) (ΔNet : ℕ) : Prop where
  /-- The environment's facts on the trace, for the delay `(Δ S)` from `GST`. -/
  E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST release acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks
  /-- The network delay and the two clock bounds fit in the delay `Δ S`. -/
  hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S
  /-- The two clock bounds together are less than one delay `Δ S`. -/
  hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S
  /-- A re-delivery after the receiver's clock reaches an object's release clock value, plus both clock bounds, fits in one delay `Δ S`. -/
  hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S
  /-- What an honest validator active at a time `t` would serve at `t` reaches every validator active
  from `t` within `Δs` of the later of `t` and `GST`. -/
  Sy : SyncedWithin A x (servesMin M S.C) acObject release ΔRedeliver Δs GST
  /-- The sync delay is at most the protocol's slow window less three delays. -/
  hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k
  hRoots : RootsNameBlocksUntil M A x (aR M S r)
  hParent : ParentHeldAtDelivery M x
  hGST : GST ≤ tGAT
  /-- The recovery delay less one delay after `tGAT` has elapsed by `T₁`. -/
  hT₁ : tGAT + Δs ≤ T₁
  hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd
  hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
    v ∉ A.corrupted i → v ∈ A.awake i
  hH₂ : OldHeightAttained M S A x T₁ H₂
  hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂
  hEnd : aR M S r ≤ tAwakeEnd
  /-- Every attestation put on the wire by a tick at a step before `k₀`, by a validator outside the adversary set
  at `tAwakeEnd`, has height at most `H₂`. -/
  hOldStep : ∀ (k t : ℕ) (u : V) (a' : Attestation V), k < k₀ → x.lbl k = Event.tick u t →
    u ∉ A.corruptedAtTime x tAwakeEnd →
    (⟨u, NamedObject.attest a'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (k + 1) - x.sent k → a'.h ≤ H₂
  /-- The time of step `k₀` is in the phase. -/
  hEndStep : x.time k₀ ≤ tAwakeEnd
  /-- In the phase, a validator outside the adversary set at its tick to a clock value at least
  `T₁ + Δ S` also ticked to the clock value one delay earlier. -/
  hTick : ∀ (c : ℕ) (w : V) (k : ℕ), T₁ ≤ c → x.lbl k = Event.tick w (c + Δ S) →
    x.time k ≤ tAwakeEnd → w ∉ A.corrupted k → ∃ k' : ℕ, x.lbl k' = Event.tick w c

/-- **The climb's bundle at the first step whose real time reaches the support cutoff of slot `r R`**
. From the clock form `hOld` at `aR M S r`, with `tGAT` at most that
support cutoff: `ClimbCtx` at `k₀ := x.firstAt (M.supportCutoff S.C (r * S.C.R))`.

Why: every step before `k₀` is at a real time less than the support cutoff of slot `r R`, so a tick there is to a clock
value less than that cutoff plus `ΔClockAhead`, less than `aR M S r` (four delays later); a validator outside the
adversary set at `tAwakeEnd` is outside it at `aR M S r`; so `hOld` bounds the attestation (`hOldStep`). Some validator
is outside the adversary set at every step up to `tAwakeEnd` (fewer than a third ever are), so it is awake from `tGAT`
and ticks to one delay after the cutoff, at a real time from the cutoff to `aR M S r`; `k₀` is at or before that tick
(`hEndStep`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`: the setup, the activity, the execution; `R`: the run's facts; the rest as `ClimbCtx`'s fields.

Read aloud: the hypotheses of the climb's count hold at the first step whose real time reaches the support cutoff of
slot `r R`. -/
theorem ClimbCtx.of_clock (U : UniformSchedule M.toSlotLayout) {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {GST tGAT tAwakeEnd T₁ r H₂ : ℕ}
    {Δs : ℕ} {release : (NamedObject V) → Option ℕ} {ΔRedeliver : ℕ} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ}
    (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST release acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithin A x (servesMin M S.C) acObject release ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (aR M S r))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT)
    (hT₁ : tGAT + Δs ≤ T₁)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hH₂ : OldHeightAttained M S A x T₁ H₂)
    (hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂)
    (hEnd : aR M S r ≤ tAwakeEnd)
    (hTick : ∀ (c : ℕ) (w : V) (k : ℕ), T₁ ≤ c → x.lbl k = Event.tick w (c + Δ S) →
      x.time k ≤ tAwakeEnd → w ∉ A.corrupted k → ∃ k' : ℕ, x.lbl k' = Event.tick w c)
    -- the phase starts no later than the support cutoff of slot `r R`
    (htG : tGAT ≤ M.supportCutoff S.C (r * S.C.R)) :
    ClimbCtx M S A x GST tGAT tAwakeEnd T₁ r H₂ (x.firstAt (M.supportCutoff S.C (r * S.C.R))) Δs release ΔRedeliver
      ΔClockAhead ΔClockBehind ΔNet := by
  classical
  have hΔ := GoldilocksCorrectness.Proofs.Routines.one_le_Δ S
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  have haR : aR M S r = M.supportCutoff S.C (r * S.C.R) + 4 * Δ S := by
    unfold aR
    exact (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_succ_eq M.toSlotLayout F.sched U) S _
  set c₀ := M.supportCutoff S.C (r * S.C.R) with hc₀
  have hΔR : (1 : ℝ) ≤ (Δ S : ℝ) := by exact_mod_cast hΔ
  have hex : ∃ i : ℕ, (c₀ : ℝ) ≤ x.time i := E.time_div c₀
  have hfa : x.firstAt c₀ = Nat.find hex := by
    unfold Trace.firstAt
    rw [dif_pos hex]
  -- a step before `k₀` is at a real time less than `c₀`
  have hbefore : ∀ k : ℕ, k < x.firstAt c₀ → x.time k < (c₀ : ℝ) := by
    intro k hk
    rw [hfa] at hk
    exact not_le.1 (Nat.find_min hex hk)
  -- a validator outside the adversary set at every step up to `tAwakeEnd`
  obtain ⟨v, hv⟩ : ∃ v : V, ∀ i : ℕ, x.time i ≤ tAwakeEnd → v ∉ A.corrupted i := by
    by_contra hno
    push Not at hno
    have h3 := hThird Finset.univ (fun v _ => hno v)
    rw [Finset.card_univ] at h3
    unfold validator_count at h3
    omega
  -- it ticks to one delay after `c₀`
  have hvA : v ∈ A.activeThroughout x (((c₀ + Δ S : ℕ) : ℝ) - ΔClockAhead) (((c₀ + Δ S : ℕ) : ℝ) + ΔClockBehind) := by
    refine Activity.mem_activeThroughout.2 fun i h1 h2 => ?_
    have hiE : x.time i ≤ tAwakeEnd := by
      have : ((c₀ + Δ S : ℕ) : ℝ) + Δ S ≤ (tAwakeEnd : ℝ) := by
        exact_mod_cast (show c₀ + Δ S + Δ S ≤ tAwakeEnd by omega)
      linarith
    have hci := hv i hiE
    refine Activity.mem_active.2 ⟨hAwake i v hiE ?_ hci, hci⟩
    have h1' := htime (Nat.le_succ i)
    have : (tGAT : ℝ) + Δ S ≤ ((c₀ + Δ S : ℕ) : ℝ) := by exact_mod_cast (show tGAT + Δ S ≤ c₀ + Δ S by omega)
    linarith
  have hkv := (tickStep_spec M) x R E (t := c₀ + Δ S) (v := v) (by omega) hvA
  have hk₀v : x.firstAt c₀ ≤ x.tickStep v (c₀ + Δ S) := by
    rw [hfa]
    refine Nat.find_min' hex ?_
    have : (c₀ : ℝ) + Δ S - ΔClockAhead ≤ x.time (x.tickStep v (c₀ + Δ S)) := by
      have h := hkv.2.1
      push_cast at h
      linarith
    linarith
  exact
    { E := E, hNet := hNet, hSkew := hSkew, hRedeliver := hRedeliver, Sy := Sy, hΔs := hΔs, hRoots := hRoots,
      hParent := hParent, hGST := hGST, hT₁ := hT₁, hThird := hThird, hAwake := hAwake, hH₂ := hH₂, hOld := hOld,
      hEnd := hEnd,
      hOldStep := fun k t u a' hk hl hu hs => by
        have h1 := (E.tick_active k u t hl).2.1
        have h2 := hbefore k hk
        refine hOld k t u a' hl ?_ ((not_mem_corruptedAtTime_of_le M) x R E hEnd hu) hs
        rw [haR]
        push_cast
        linarith
      hEndStep := by
        have h := htime hk₀v
        have h2 := hkv.2.2
        have : ((c₀ + Δ S : ℕ) : ℝ) + ΔClockBehind ≤ (tAwakeEnd : ℝ) := by
          have : ((c₀ + Δ S : ℕ) : ℝ) + Δ S ≤ (tAwakeEnd : ℝ) := by
            exact_mod_cast (show c₀ + Δ S + Δ S ≤ tAwakeEnd by omega)
          linarith
        linarith
      hTick := hTick }

namespace ClimbCtx
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

variable {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N}
  {GST tGAT tAwakeEnd T₁ r H₂ : ℕ} {k₀ : ℕ}

/-- B2 in the context: from `T₁ + Δ` to `aR M S r`, an honest validator's greatest chain-state
height is `H₂` or `H₂ + 1`.

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed; `C`: the bundle.

Read aloud: from `T₁ + Δ` to `aR M S r`, an honest validator's greatest chain-state height is `H₂`
or `H₂ + 1`. -/
theorem bounds (U : UniformSchedule M.toSlotLayout) (R : RunFacts M S x) (Fx : FixedValidators M.toSlotLayout)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (C : ClimbCtx M S A x GST tGAT tAwakeEnd T₁ r H₂ k₀ Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {t : ℕ} {w : V}
    (h1 : T₁ + Δ S ≤ t) (k : ℕ) (hk : x.lbl k = Event.tick w t) (h2 : k ≤ k₀)
    (hka : x.time k ≤ aR M S r) (hw : w ∉ A.corrupted k) :
    H₂ ≤ hMax M S.C (x.tickInput w t) ∧ hMax M S.C (x.tickInput w t) ≤ H₂ + 1 := by
  have hks := (tickStep_eq_of_lbl M) x C.E hk
  have hkE : x.time k ≤ tAwakeEnd := le_trans (R.time_mono h2) C.hEndStep
  refine ⟨?_, ?_⟩
  · -- the lower bound: Lemma 89b at `w`'s tick `k` to `t`, read at its tick to `t − Δ` (the bundle's `hTick`)
    have hΔ := GoldilocksCorrectness.Proofs.Routines.one_le_Δ S
    have hwc := C.hTick (t - Δ S) w k (by omega) (by rw [Nat.sub_add_cancel (by omega)]; exact hk) hkE hw
    exact old_height_le_hMax_at_tick M F U Fx S A x R GST tGAT tAwakeEnd T₁ H₂ t t (t - Δ S) k w
      (GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsDelivery.upTo C.E t) C.hNet C.hSkew C.hRedeliver
      (C.Sy.upTo t) C.hΔs C.hParent C.hGST C.hT₁ C.hThird C.hAwake C.hH₂ hk hkE
      ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) hka C.hRoots) hw
      (by omega) (by omega) hwc le_rfl
  · -- the upper bound: A2 at `w`'s tick `k`, a step at most `k₀`
    obtain ⟨-, ⟨X, hX, hXh⟩, -⟩ := (cachesWitnessed_of_exec M F) S A x R C.E k w
    show hMax M S.C (x.st (x.tickStep w t) w) ≤ H₂ + 1
    rw [hks, ← hXh]
    exact (GoldilocksCorrectness.Record.Proofs.Executions.held_height_le_before_action M F Fx) S A x R C.E
      tAwakeEnd H₂ k₀ k w X C.hThird C.hOldStep C.hEndStep h2 hX

/-- Before `aR M S r`, every validator's greatest chain-state height is at most `H₂ + 1` (A2).

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed; `C`: the bundle.

Read aloud: before `aR M S r`, every validator's greatest chain-state height is at most `H₂ + 1`. -/
theorem hmax_le (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (Fx : FixedValidators M.toSlotLayout)
    {Δs : ℕ} {ΔNet : ℕ} (C : ClimbCtx M S A x GST tGAT tAwakeEnd T₁ r H₂ k₀ Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {t : ℕ} (w : V)
    (h2 : x.stepBefore t ≤ k₀) : hMax M S.C (x.stateBefore t w) ≤ H₂ + 1 := by
  obtain ⟨-, ⟨X, hX, hXh⟩, -⟩ := (GoldilocksCorrectness.Record.Proofs.Executions.cachesWitnessed_of_stateBefore M F) S A x R E t w
  rw [← hXh]
  exact (GoldilocksCorrectness.Record.Proofs.Executions.held_height_le_before_action M F Fx) S A x R E tAwakeEnd H₂ k₀
    (x.stepBefore t) w X C.hThird C.hOldStep C.hEndStep h2 hX

/-- `bounds` at a configuration: a validator outside the adversary set at a step `j` at a time after
`T₁ + Δ` and before `aR M S r` has its greatest chain-state height at `H₂` or `H₂ + 1` there. It is
outside the adversary set at every step at the time `T₁ + Δ` (they come before `j`), so `bounds` holds
before `T₁ + Δ`, and the greatest chain-state height does not decrease up to `j`; the upper bound is A2
(`hmax_le_st`).

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed; `C`: the bundle; `w`: the
  validator; `j`: the step.

Read aloud: from after `T₁ + Δ` to before `aR M S r`, an honest validator's greatest chain-state height
is `H₂` or `H₂ + 1`. -/
theorem bounds_st (U : UniformSchedule M.toSlotLayout) (R : RunFacts M S x) (Fx : FixedValidators M.toSlotLayout)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (C : ClimbCtx M S A x GST tGAT tAwakeEnd T₁ r H₂ k₀ Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {j : ℕ} {w : V}
    {c k : ℕ} (hc : T₁ + Δ S ≤ c) (hk : x.lbl k = Event.tick w c) (hsj : k ≤ j)
    (hw : w ∉ A.corrupted j) (h2 : j ≤ k₀) (hja : x.time j ≤ aR M S r) :
    H₂ ≤ hMax M S.C (x.st j w) ∧ hMax M S.C (x.st j w) ≤ H₂ + 1 := by
  have hb := C.bounds M F U R Fx (t := c) (w := w) hc k hk (le_trans hsj h2) (le_trans (R.time_mono hsj) hja)
    (fun h => hw (C.E.corrupted_mono k j hsj h))
  have hks := (tickStep_eq_of_lbl M) x C.E hk
  have hb1 : H₂ ≤ hMax M S.C (x.st k w) := by
    have h := hb.1
    unfold Trace.tickInput at h
    rwa [hks] at h
  refine ⟨le_trans hb1 ((h_max_mono_st M F) S A x R C.E w hsj), ?_⟩
  obtain ⟨-, ⟨X, hX, hXh⟩, -⟩ := (cachesWitnessed_of_exec M F) S A x R C.E j w
  rw [← hXh]
  exact (GoldilocksCorrectness.Record.Proofs.Executions.held_height_le_before_action M F Fx) S A x R C.E
    tAwakeEnd H₂ k₀ j w X C.hThird C.hOldStep C.hEndStep h2 hX

/-- A2 at a configuration: at a step before `aR M S r`, every validator's greatest chain-state height is
at most `H₂ + 1`.

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed; `C`: the bundle; `w`: the
  validator; `j`: the step.

Read aloud: before `aR M S r`, every validator's greatest chain-state height is at most `H₂ + 1`. -/
theorem hmax_le_st (R : RunFacts M S x) (Fx : FixedValidators M.toSlotLayout)
    {Δs : ℕ} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (C : ClimbCtx M S A x GST tGAT tAwakeEnd T₁ r H₂ k₀ Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {j : ℕ} (w : V)
    (h2 : j ≤ k₀) : hMax M S.C (x.st j w) ≤ H₂ + 1 := by
  obtain ⟨-, ⟨X, hX, hXh⟩, -⟩ := (cachesWitnessed_of_exec M F) S A x R C.E j w
  rw [← hXh]
  exact (GoldilocksCorrectness.Record.Proofs.Executions.held_height_le_before_action M F Fx) S A x R C.E
    tAwakeEnd H₂ k₀ j w X C.hThird C.hOldStep C.hEndStep h2 hX

/-- From a time `τ` of the climbing phase (`T₁ ≤ τ`), the window of one delay or one sync delay before
`τ + 1 + Δ` starts at or after `tGAT`, where every validator outside the adversary set is awake.

Why: the bundle's line `tGAT + Δs ≤ T₁` and `T₁ ≤ τ`.

The variables:
- `M`: the model; `F`: its facts; `C`: the bundle; `τ`: the time.

Read aloud: the sync window before `τ + 1 + Δ` lies in the phase. -/
theorem syncWindow {Δs : ℕ} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (C : ClimbCtx M S A x GST tGAT tAwakeEnd T₁ r H₂ k₀ Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {τ : ℕ} (hT : T₁ ≤ τ) :
    tGAT + max (Δ S) Δs ≤ τ + 1 + Δ S := by
  have := C.hT₁
  omega

/-- A validator honest at `t ≤ tAwakeEnd` is awake and honest at every time of the phase up to
`t`.

The variables:
- `M`: the model; `F`: its facts; `C`: the bundle.

Read aloud: a validator honest at `t ≤ tAwakeEnd` is awake and honest at every time of the phase up
to `t`. -/
theorem awakeHonest {Δs : ℕ} {release ΔRedeliver} (R : RunFacts M S x) {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (C : ClimbCtx M S A x GST tGAT tAwakeEnd T₁ r H₂ k₀ Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {w : V} {t : ℕ}
    (hw : w ∉ A.corruptedAtTime x t) (ht : t ≤ tAwakeEnd) :
    w ∈ A.activeThroughout x tGAT t :=
  (mem_activeThroughout_of_hAwake_honest_at M F) R C.E C.hAwake le_rfl ht hw

/-- **A receiver's tick to `τ + Δ` before `aR M S r` puts `τ` before `aR M S r`.** The real time of `w`'s tick `kT` to
`τ + Δ` is at least `τ + Δ − ΔClockAhead`, more than `τ` since `ΔClockAhead < Δ` (`hSkew`), and at most the time of a
later step `i` before `aR M S r`.

The variables:
- `M`: the model; `F`: its facts; `C`: the bundle; `τ`: the clock value; `kT`: `w`'s tick to `τ + Δ`; `i`: a later step.

Read aloud: a validator's tick to `τ + Δ`, at or before a step before `aR M S r`, makes `τ` at most `aR M S r`. -/
theorem tau_le_aR (R : RunFacts M S x) {Δs : ℕ} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ}
    (C : ClimbCtx M S A x GST tGAT tAwakeEnd T₁ r H₂ k₀ Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet)
    {τ kT i : ℕ} {w : V} (hkT : x.lbl kT = Event.tick w (τ + Δ S)) (hsi : kT ≤ i) (hta : x.time i < aR M S r) :
    (τ : ℝ) ≤ aR M S r := by
  have h1 := (C.E.tick_active kT w (τ + Δ S) hkT).2.1
  have h2 := R.time_mono hsi
  have hB := C.E.behind_nonneg
  have hS := C.hSkew
  push_cast at h1
  linarith

/-- `held_spread` in the context, holder at a step: a block `D` that `u` holds at a step `j` whose real time
is after `T₁` and whose real time and clock value are at most `τ`, with `u` outside the adversary set at `j` and
its finalized block there compatible with `D`, is, at every step `i` from `w`'s tick to `τ + Δ` on and before
`aR M S r` with `w` outside the adversary set at `i`, in `w`'s tree with `w`'s finalized block an ancestor of
`D` or `D`, or has chain-state height at most `w`'s justification height.

Why: when `D` is higher than `w`'s justification height at `i`, `w`'s finalized block there is an ancestor of
`D` (`F_ancestorEq_of_high_st`); the genesis block is in every tree; otherwise `block_at_tick_of_held_step`
puts `D` in `w`'s tree at its tick to `τ + Δ` (the window from `T₁ − Δs`, where `u` is honest and awake
since its step `j` comes later; `w`'s tick to `τ` by `hTick`; `D`'s slot starts at most at `u`'s clock value
at `j`), and trees grow.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed; `C`: the
  bundle; `τ`: the clock value; `j`: the holder's step; `kT`: `w`'s tick to `τ + Δ`; `i`: the receiver's
  step.

Read aloud: a block `u` holds at a step by `τ` reaches `w` by its tick to `τ + Δ`, or has chain-state height
at most `w`'s justification height. -/
theorem spread (U : UniformSchedule M.toSlotLayout) (R : RunFacts M S x) (Fx : FixedValidators M.toSlotLayout)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (C : ClimbCtx M S A x GST tGAT tAwakeEnd T₁ r H₂ k₀ Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {τ j i kT : ℕ} {u w : V}
    {D : Block V} (hT : (T₁ : ℝ) < x.time j) (hj : x.time j ≤ τ) (hjc : x.clockValue j u ≤ τ) (hu : u ∉ A.corrupted j)
    (hD : D ∈ (x.st j u).tree)
    (hsel : (x.st j u).finalized.compatible D = true) (hkT : x.lbl kT = Event.tick w (τ + Δ S)) (hsi : kT ≤ i)
    (hwA : ∀ l : ℕ, (tGAT : ℝ) ≤ x.time l → l ≤ kT → w ∈ A.active l)
    (hta : x.time i < aR M S r) (hw : w ∉ A.corrupted i) :
    (D ∈ (x.st i w).tree ∧ (x.st i w).finalized.AncestorEq D) ∨
      (M.chainStateOf S.C D).h ≤ (x.st i w).justifiedHeight := by
  by_cases hlt : (x.st i w).justifiedHeight < (M.chainStateOf S.C D).h
  swap
  · exact Or.inr (Nat.le_of_not_lt hlt)
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  have hAE : (aR M S r : ℝ) ≤ tAwakeEnd := by exact_mod_cast C.hEnd
  have hjR : x.time j ≤ aR M S r :=
    le_trans hj (C.tau_le_aR M F R hkT hsi hta)
  have hFD := (F_ancestorEq_of_high_st M F Fx) S A x R C.E C.hRoots tAwakeEnd i j w u D C.hThird
    (le_trans hta.le hAE) (le_trans hjR hAE) hw hu hD hlt (max_le hta.le hjR)
  refine Or.inl ⟨?_, hFD⟩
  by_cases hg : D = Block.genesis
  · subst hg
    exact (genesis_mem_T_of_exec M F) S A x R C.E i w
  have hwkT : w ∉ A.corrupted kT := fun h => hw (C.E.corrupted_mono kT i hsi h)
  have hkTi : x.time kT ≤ x.time i := htime hsi
  have hkTt : x.time kT ≤ tAwakeEnd := le_trans hkTi (le_trans hta.le hAE)
  have hT₁τ : T₁ ≤ τ := by
    have : (T₁ : ℝ) < τ := lt_of_lt_of_le hT hj
    exact_mod_cast this.le
  -- the receiver's tick to `τ`, one delay before its tick to `τ + Δ S` (`hTick`)
  obtain ⟨k₂, hk₂⟩ := C.hTick τ w kT hT₁τ hkT hkTt hwkT
  -- the block's slot starts at the latest at `u`'s clock value at `j`, at most `τ`
  have hsl : ∀ t : ℕ, M.slot S.C t = S.C.slot (t : Int) := fun t => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U),
      GoldilocksCorrectness.Proofs.Routines.slot_natCast]
  have hHs := (slot_le_clockValue_of_mem_tree M F) R C.E hu hD
  rw [← hsl] at hHs
  have hDc₂ : M.slotStart S.C D.slot ≤ τ :=
    le_trans (((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_le_iff M.toSlotLayout F.sched) S D.slot
      (x.clockValue j u)).2 hHs) hjc
  -- the holder is honest and awake from `T₁ − Δs` to `T₁`, before `j`
  have hT1 := C.hT₁
  have hGa := C.hGST
  have haR : ((T₁ - Δs : ℕ) : ℝ) + Δs = T₁ := by
    have : T₁ - Δs + Δs = T₁ := Nat.sub_add_cancel (by omega)
    exact_mod_cast this
  have hu₀ : u ∈ A.activeThroughout x ((T₁ - Δs : ℕ) : ℝ) (((T₁ - Δs : ℕ) : ℝ) + Δs) := by
    refine Activity.mem_activeThroughout.2 (fun l h1 h2 => ?_)
    have hul : u ∉ A.corrupted l :=
      (not_mem_corrupted_of_time_lt M F) R C.E hu (by rw [haR] at h1; linarith)
    have hgl : ((tGAT : ℕ) : ℝ) ≤ ((T₁ - Δs : ℕ) : ℝ) := by exact_mod_cast (show tGAT ≤ T₁ - Δs by omega)
    have hlt' : x.time l ≤ tAwakeEnd := by rw [haR] at h1; linarith
    exact Activity.mem_active.2 ⟨C.hAwake l u hlt' (le_trans hgl h2) hul, hul⟩
  have hsb : x.stepBefore (T₁ - Δs) ≤ j := (stepBefore_le_of_le_time_st M F) R C.E
    (by have : ((T₁ - Δs : ℕ) : ℝ) ≤ T₁ := by exact_mod_cast Nat.sub_le T₁ Δs
        linarith)
  have hFa := GoldilocksCorrectness.Proofs.Routines.compatible_of_ancestorEq_compatible ((F_ancestorEq_of_le M F) x R C.E u hsb) hsel
  have hFw : (x.st kT w).finalized.compatible D = true :=
    (compatible_iff _ _).2 (Or.inl (ancestorEq_trans ((F_ancestorEq_of_le M F) x R C.E w hsi) hFD))
  have hmx := le_max_left (Δ S) Δs
  have hmx' := le_max_right (Δ S) Δs
  have hmx'' : max (Δ S) Δs ≤ Δ S + Δs := max_le (by omega) (by omega)
  refine (mem_T_mono M F) x R C.E w hsi ?_
  exact block_at_tick_of_held_step M F U S A x R GST (τ + Δ S) τ j (T₁ - Δs) (τ + Δ S) τ kT k₂ u w D
    (C.E.upTo _) C.hNet C.hSkew C.hRedeliver (C.Sy.upTo _)
    (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M (le_trans hkTi hta.le) C.hRoots) C.hParent (by omega) (by omega) le_rfl le_rfl hu₀ hj hu hD hFa hg hkT
    (fun l hl hlk => hwA l (le_trans (by exact_mod_cast (show tGAT ≤ T₁ - Δs by omega)) hl) hlk)
    hk₂ le_rfl hDc₂ hFw

/-- `held_spread_h_j` in the context.

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed; `C`: the bundle.

Read aloud: a held block's justification height is at most `w`'s justification height before
`τ + 1 + Δ`. -/
theorem spread_h_j (U : UniformSchedule M.toSlotLayout) (R : RunFacts M S x) (Fx : FixedValidators M.toSlotLayout)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (C : ClimbCtx M S A x GST tGAT tAwakeEnd T₁ r H₂ k₀ Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {τ j i kT : ℕ} {u w : V}
    {D : Block V} (hT : (T₁ : ℝ) < x.time j) (hj : x.time j ≤ τ) (hjc : x.clockValue j u ≤ τ) (hu : u ∉ A.corrupted j)
    (hD : D ∈ (x.st j u).tree)
    (hsel : (x.st j u).finalized.compatible D = true) (hkT : x.lbl kT = Event.tick w (τ + Δ S)) (hsi : kT ≤ i)
    (hwA : ∀ l : ℕ, (tGAT : ℝ) ≤ x.time l → l ≤ kT → w ∈ A.active l)
    (hta : x.time i < aR M S r) (hw : w ∉ A.corrupted i) :
    (M.chainStateOf S.C D).h_j ≤ (x.st i w).justifiedHeight := by
  rcases (C.spread M F U R Fx) hT hj hjc hu hD hsel hkT hsi hwA hta hw with ⟨hDw, hFD⟩ | hle
  · exact (GoldilocksCorrectness.Record.Statements.Executions.h_j_of_mem_T_of_exec M F) S A x R C.E i w D hDw hFD
  · have h47 := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C D D).1.2.1
    unfold Height at *
    omega

/-- `held_spread_h_max` in the context.

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed; `C`: the bundle.

Read aloud: a held block's chain-state height is at most `w`'s greatest chain-state height before
`τ + 1 + Δ`. -/
theorem spread_h_max (U : UniformSchedule M.toSlotLayout) (R : RunFacts M S x) (Fx : FixedValidators M.toSlotLayout)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (C : ClimbCtx M S A x GST tGAT tAwakeEnd T₁ r H₂ k₀ Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {τ j i kT : ℕ} {u w : V}
    {D : Block V} (hT : (T₁ : ℝ) < x.time j) (hj : x.time j ≤ τ) (hjc : x.clockValue j u ≤ τ) (hu : u ∉ A.corrupted j)
    (hD : D ∈ (x.st j u).tree)
    (hsel : (x.st j u).finalized.compatible D = true) (hkT : x.lbl kT = Event.tick w (τ + Δ S)) (hsi : kT ≤ i)
    (hwA : ∀ l : ℕ, (tGAT : ℝ) ≤ x.time l → l ≤ kT → w ∈ A.active l)
    (hta : x.time i < aR M S r) (hw : w ∉ A.corrupted i) :
    (M.chainStateOf S.C D).h ≤ hMax M S.C (x.st i w) := by
  rcases (C.spread M F U R Fx) hT hj hjc hu hD hsel hkT hsi hwA hta hw with ⟨hDw, -⟩ | hle
  · exact le_hMax M hDw
  · have h := (h_j_lt_h_max_st M F) S A x R C.E i w
    unfold Height at *
    omega

/-! ## The four levels: their spreading and their persistence -/

/-- The level `j ≤ h_j` spreads: when `u`, honest at `τ ≥ T₁`, has `h_j ≥ j` before `τ + 1`, every
`w` honest at `t ≥ τ + 1 + Δ` before `aR M S r` has `h_j ≥ j` before `τ + 1 + Δ` (the block
witnessing `u`'s cache, `held_spread_h_j`).

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed; `C`: the bundle.

Read aloud: a justification height of at least `j` at `u` before `τ + 1` reaches every honest `w`
before `τ + 1 + Δ`. -/
theorem spread_level_h_j (U : UniformSchedule M.toSlotLayout) (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (Fx : FixedValidators M.toSlotLayout)
    (C : ClimbCtx M S A x GST tGAT tAwakeEnd T₁ r H₂ k₀ Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) (h : ℕ) {τ j i kT : ℕ}
    {u w : V} (hT : (T₁ : ℝ) < x.time j) (hj : x.time j ≤ τ) (hjc : x.clockValue j u ≤ τ) (hu : u ∉ A.corrupted j)
    (hL : h ≤ (x.st j u).justifiedHeight) (hkT : x.lbl kT = Event.tick w (τ + Δ S)) (hsi : kT ≤ i)
    (hwA : ∀ l : ℕ, (tGAT : ℝ) ≤ x.time l → l ≤ kT → w ∈ A.active l)
    (hta : x.time i < aR M S r) (hw : w ∉ A.corrupted i) :
    h ≤ (x.st i w).justifiedHeight := by
  obtain ⟨⟨D, hD, hJD, hjD⟩, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Executions.cachesWitnessed_of_exec M F) S A x R E j u
  have hsp := (C.spread_h_j M F U R Fx) hT hj hjc hu hD (by
      have hFJ := (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_J_of_exec M F) S A x R E j u
      rw [hJD] at hFJ
      exact (compatible_iff _ _).2 (Or.inl (ancestorEq_trans hFJ ((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_J_spec M F) S.C D).1))) hkT hsi hwA hta hw
  rw [hjD] at hL
  exact le_trans hL hsp

/-- The level `H₂ ≤ head_height_floor` spreads: when `u`, honest at `τ ≥ T₁`, has
`head_height_floor ≥ H₂` before `τ + 1`, so does every `w` honest at `t ≥ τ + 1 + Δ` before
`aR M S r`, before `τ + 1 + Δ`.

Why: either `u`'s greatest chain-state height is at least `H₂ + 1`, and its witness raises `w`'s; or
`u` is contested at greatest chain-state height `H₂`, `h_j = H₂ − 1`, and its contesting block and
its justified block's witness reach `w`, whose state is then contested at `H₂` too, or has greatest
chain-state height `H₂ + 1`.

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed; `C`: the bundle.

Read aloud: `head_height_floor` at least `H₂` at `u` before `τ + 1` reaches every honest `w` before
`τ + 1 + Δ`. -/
theorem spread_level_floor (U : UniformSchedule M.toSlotLayout) (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (Fx : FixedValidators M.toSlotLayout)
    (C : ClimbCtx M S A x GST tGAT tAwakeEnd T₁ r H₂ k₀ Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {τ j i kT : ℕ}
    {u w : V} (hT : (T₁ : ℝ) < x.time j) (hj : x.time j ≤ τ) (hjc : x.clockValue j u ≤ τ) (hu : u ∉ A.corrupted j)
    (hL : H₂ ≤ M.head_height_floor (x.st j u)) (hkT : x.lbl kT = Event.tick w (τ + Δ S)) (hsi : kT ≤ i)
    (hwA : ∀ l : ℕ, (tGAT : ℝ) ≤ x.time l → l ≤ kT → w ∈ A.active l)
    (hta : x.time i < aR M S r) (hik : i ≤ k₀) (hw : w ∉ A.corrupted i) :
    H₂ ≤ M.head_height_floor (x.st i w) := by
  have hΔ := GoldilocksCorrectness.Proofs.Routines.one_le_Δ S
  have hAE : (aR M S r : ℝ) ≤ tAwakeEnd := by exact_mod_cast C.hEnd
  have hjR : x.time j ≤ aR M S r :=
    le_trans hj (C.tau_le_aR M F R hkT hsi hta)
  have hT₁τ : T₁ ≤ τ := by exact_mod_cast (le_trans hT.le hj)
  have hInvU := (lem11_node_invariant M F S A x R E j u hu).1
  have hInvW := (lem11_node_invariant M F S A x R E i w hw).1
  have hfw := (GoldilocksCorrectness.Record.Proofs.Routines.h_max_sub_one_le_floor M F) S.C S.P S.X (x.st i w) hInvW
  by_cases hX : H₂ + 1 ≤ hMax M S.C (x.st j u)
  · obtain ⟨-, ⟨X, hX', hXh⟩, -⟩ := (GoldilocksCorrectness.Record.Proofs.Executions.cachesWitnessed_of_exec M F) S A x R E j u
    have h := (C.spread_h_max M F U R Fx) hT hj hjc hu hX'
      ((compatible_iff _ _).2 (Or.inl ((hMax_witness_compatible_finalized M F Fx) x R C.E C.hRoots j u X
        (C.hThird.mono (le_trans hjR hAE)) hu hX'
        (fun B hB => by rw [hXh]; exact le_hMax M hB) hjR)))
      hkT hsi hwA hta hw
    unfold Height at *
    omega
  rcases Nat.eq_zero_or_pos H₂ with h0 | hpos
  · rw [h0]
    exact Nat.zero_le _
  rcases (GoldilocksCorrectness.Record.Proofs.Routines.floor_cases M F) S.C S.P S.X (x.st j u) hInvU with ⟨hc, hm, hfl⟩ | ⟨-, hfl⟩
  swap
  · exfalso
    rw [hfl] at hL
    unfold Height at *
    omega
  obtain ⟨-, Ab, hA, hFA', hAh, hJA⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.fg_contest_spec M F) S.C S.P S.X _ hInvU hc
  obtain ⟨⟨D, hD, hJD, hjD⟩, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Executions.cachesWitnessed_of_exec M F) S A x R E j u
  have hjw := (C.spread_h_j M F U R Fx) hT hj hjc hu hD (by
      have hFJ := (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_J_of_exec M F) S A x R E j u
      rw [hJD] at hFJ
      exact (compatible_iff _ _).2 (Or.inl (ancestorEq_trans hFJ ((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_J_spec M F) S.C D).1))) hkT hsi hwA hta hw
  rw [← hjD] at hjw
  by_cases hY : H₂ + 1 ≤ hMax M S.C (x.st i w)
  · unfold Height at *
    omega
  have hb := C.bounds_st M F U R Fx (j := i) (w := w) (show T₁ + Δ S ≤ τ + Δ S by omega) hkT hsi hw hik hta.le
  have hjl := (h_j_lt_h_max_st M F) S A x R E i w
  rw [hfl] at hL
  have hmu : hMax M S.C (x.st j u) = H₂ := by
    unfold Height at *
    omega
  have hjeq : (x.st i w).justifiedHeight = (x.st j u).justifiedHeight := by
    unfold Height at *
    omega
  have hmw : hMax M S.C (x.st i w) = (x.st i w).justifiedHeight + 1 := by
    unfold Height at *
    omega
  rcases (C.spread M F U R Fx) hT hj hjc hu hA ((compatible_iff _ _).2 (Or.inl hFA')) hkT hsi hwA hta hw with ⟨hAw, hFA⟩ | hlo
  swap
  · exfalso
    unfold Height at *
    omega
  have hJ := (J_eq_of_h_j_eq_st M F Fx) S A x R E C.hRoots tAwakeEnd i j w u C.hThird
    (le_trans hta.le hAE) (le_trans hjR hAE) hw hu hjeq (max_le hta.le hjR)
  have hcw : M.fg_contest (x.st i w) = true := by
    refine (GoldilocksCorrectness.Record.Proofs.Routines.fg_contest_true_of M F) S.C S.P S.X _ hInvW Ab hmw hAw hFA ?_ ?_
    · rw [hAh]
      unfold Height at *
      omega
    · rw [hJ]
      exact hJA
  rcases (GoldilocksCorrectness.Record.Proofs.Routines.floor_cases M F) S.C S.P S.X (x.st i w) hInvW with ⟨-, -, hflw⟩ | ⟨hcf, -⟩
  · rw [hflw]
    unfold Height at *
    omega
  · rw [hcw] at hcf
    cases hcf

/-- The level `H₂ + 1 ≤ head_height_floor` spreads: when `u`, honest at `τ ≥ T₁`, has
`head_height_floor ≥ H₂ + 1` before `τ + 1`, so does every `w` honest at `t ≥ τ + 1 + Δ` before
`aR M S r`, before `τ + 1 + Δ`.

Why: `u` is then contested at greatest chain-state height `H₂ + 1`, `h_j = H₂` (A2 bounds the
greatest chain-state height); its contesting block and its justified block's witness reach `w`,
whose state is then contested at `H₂ + 1`.

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed; `C`: the bundle.

Read aloud: `head_height_floor` at least `H₂ + 1` at `u` before `τ + 1` reaches every honest `w`
before `τ + 1 + Δ`. -/
theorem spread_level_floor_succ (U : UniformSchedule M.toSlotLayout) (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (Fx : FixedValidators M.toSlotLayout)
    (C : ClimbCtx M S A x GST tGAT tAwakeEnd T₁ r H₂ k₀ Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {τ j i kT : ℕ}
    {u w : V} (hT : (T₁ : ℝ) < x.time j) (hj : x.time j ≤ τ) (hjc : x.clockValue j u ≤ τ) (hu : u ∉ A.corrupted j)
    (hL : H₂ + 1 ≤ M.head_height_floor (x.st j u)) (hkT : x.lbl kT = Event.tick w (τ + Δ S)) (hsi : kT ≤ i)
    (hwA : ∀ l : ℕ, (tGAT : ℝ) ≤ x.time l → l ≤ kT → w ∈ A.active l)
    (hta : x.time i < aR M S r) (hik : i ≤ k₀) (hw : w ∉ A.corrupted i) :
    H₂ + 1 ≤ M.head_height_floor (x.st i w) := by
  have hΔ := GoldilocksCorrectness.Proofs.Routines.one_le_Δ S
  have hAE : (aR M S r : ℝ) ≤ tAwakeEnd := by exact_mod_cast C.hEnd
  have hjR : x.time j ≤ aR M S r :=
    le_trans hj (C.tau_le_aR M F R hkT hsi hta)
  have hT₁τ : T₁ ≤ τ := by exact_mod_cast (le_trans hT.le hj)
  have hInvU := (lem11_node_invariant M F S A x R E j u hu).1
  have hInvW := (lem11_node_invariant M F S A x R E i w hw).1
  -- `j` comes before `w`'s tick to `τ + Δ`: that tick is at a real time at least `τ + Δ − ΔClockAhead`, later
  -- than `τ` (`hSkew`), and the time of `j` is at most `τ`
  have hjsb : j ≤ kT := by
    by_contra hlt
    have hm := (time_mono M) x R (Nat.le_of_lt (Nat.lt_of_not_le hlt))
    have hkt := (C.E.tick_active _ _ _ hkT).2.1
    have hsk := C.hSkew
    have hB0 := C.E.behind_nonneg
    push_cast at hkt
    linarith
  have hmu := C.hmax_le_st M F R Fx u (j := j) (le_trans hjsb (le_trans hsi hik))
  have hflu := (GoldilocksCorrectness.Record.Proofs.Routines.floor_le_h_max M F) S.C S.P S.X (x.st j u) hInvU
  rcases (GoldilocksCorrectness.Record.Proofs.Routines.floor_cases M F) S.C S.P S.X (x.st j u) hInvU with ⟨hc, hm, hfl⟩ | ⟨-, hfl⟩
  swap
  · exfalso
    rw [hfl] at hL
    unfold Height at *
    omega
  obtain ⟨-, Ab, hA, hFA', hAh, hJA⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.fg_contest_spec M F) S.C S.P S.X _ hInvU hc
  obtain ⟨⟨D, hD, hJD, hjD⟩, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Executions.cachesWitnessed_of_exec M F) S A x R E j u
  have hjw := (C.spread_h_j M F U R Fx) hT hj hjc hu hD (by
      have hFJ := (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_J_of_exec M F) S A x R E j u
      rw [hJD] at hFJ
      exact (compatible_iff _ _).2 (Or.inl (ancestorEq_trans hFJ ((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_J_spec M F) S.C D).1))) hkT hsi hwA hta hw
  rw [← hjD] at hjw
  have hmw := C.hmax_le_st M F R Fx w (j := i) hik
  have hjl := (h_j_lt_h_max_st M F) S A x R E i w
  rw [hfl] at hL
  have hjeq : (x.st i w).justifiedHeight = (x.st j u).justifiedHeight := by
    unfold Height at *
    omega
  have hmw' : hMax M S.C (x.st i w) = (x.st i w).justifiedHeight + 1 := by
    unfold Height at *
    omega
  rcases (C.spread M F U R Fx) hT hj hjc hu hA ((compatible_iff _ _).2 (Or.inl hFA')) hkT hsi hwA hta hw with ⟨hAw, hFA⟩ | hlo
  swap
  · exfalso
    unfold Height at *
    omega
  have hJ := (J_eq_of_h_j_eq_st M F Fx) S A x R E C.hRoots tAwakeEnd i j w u C.hThird
    (le_trans hta.le hAE) (le_trans hjR hAE) hw hu hjeq (max_le hta.le hjR)
  have hcw : M.fg_contest (x.st i w) = true := by
    refine (GoldilocksCorrectness.Record.Proofs.Routines.fg_contest_true_of M F) S.C S.P S.X _ hInvW Ab hmw' hAw hFA ?_ ?_
    · rw [hAh]
      unfold Height at *
      omega
    · rw [hJ]
      exact hJA
  rcases (GoldilocksCorrectness.Record.Proofs.Routines.floor_cases M F) S.C S.P S.X (x.st i w) hInvW with ⟨-, -, hflw⟩ | ⟨hcf, -⟩
  · rw [hflw]
    unfold Height at *
    omega
  · rw [hcw] at hcf
    cases hcf

/-- The level `H₂ ≤ head_height_floor` persists: reached before `t₂`, it holds before
every `t ≥ t₂` before `aR M S r` at which `w` is honest (`contest_persists` when the greatest
chain-state height stays `H₂`).

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed; `C`: the bundle.

Read aloud: `head_height_floor` at least `H₂` at `w`, reached before `t₂`, holds before every later
`t` before `aR M S r` at which `w` is honest. -/
theorem mono_level_floor (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (Fx : FixedValidators M.toSlotLayout)
    (C : ClimbCtx M S A x GST tGAT tAwakeEnd T₁ r H₂ k₀ Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {w : V} {t₂ t : ℕ}
    (h2t : t₂ ≤ t) (hta : t < aR M S r) (hw : w ∉ A.corruptedAtTime x t)
    (hL : H₂ ≤ M.head_height_floor (x.stateBefore t₂ w)) :
    H₂ ≤ M.head_height_floor (x.stateBefore t w) := by
  have hft := (GoldilocksCorrectness.Record.Proofs.Routines.h_max_sub_one_le_floor M F) S.C S.P S.X (x.stateBefore t w) ((nodeInv_stateBefore_of_not_mem_corruptedAtTime M F) S A x R C.E le_rfl hw)
  by_cases hX : H₂ + 1 ≤ hMax M S.C (x.stateBefore t w)
  · unfold Height at *
    omega
  rcases Nat.eq_zero_or_pos H₂ with h0 | hpos
  · rw [h0]
    exact Nat.zero_le _
  have hmm := (GoldilocksCorrectness.Record.Proofs.Executions.h_max_mono M F) S A x R C.E w h2t
  rcases (GoldilocksCorrectness.Record.Proofs.Routines.floor_cases M F) S.C S.P S.X (x.stateBefore t₂ w) ((nodeInv_stateBefore_of_not_mem_corruptedAtTime M F) S A x R C.E h2t hw) with ⟨hc, -, hfl⟩ | ⟨-, hfl⟩
  swap
  · exfalso
    rw [hfl] at hL
    unfold Height at *
    omega
  have hmeq : hMax M S.C (x.stateBefore t w) = hMax M S.C (x.stateBefore t₂ w) := by
    unfold Height at *
    omega
  have hct := (GoldilocksCorrectness.Record.Proofs.Executions.contest_persists M F Fx) S A x R C.E C.hRoots tAwakeEnd t₂ t w C.hThird
    h2t (by have := C.hEnd; omega) hw hc hmeq (by omega)
  rcases (GoldilocksCorrectness.Record.Proofs.Routines.floor_cases M F) S.C S.P S.X (x.stateBefore t w) ((nodeInv_stateBefore_of_not_mem_corruptedAtTime M F) S A x R C.E le_rfl hw) with ⟨-, -, hflt⟩ | ⟨hcf, -⟩
  · rw [hflt, hmeq, ← hfl]
    exact hL
  · rw [hct] at hcf
    cases hcf

/-- The level `H₂ + 1 ≤ head_height_floor` persists: reached before `t₂`, it holds before every
`t ≥ t₂` before `aR M S r` at which `w` is honest (`contest_persists`, the greatest chain-state
height staying `H₂ + 1`).

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed; `C`: the bundle.

Read aloud: `head_height_floor` at least `H₂ + 1` at `w`, reached before `t₂`, holds before every
later `t` before `aR M S r` at which `w` is honest. -/
theorem mono_level_floor_succ (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (Fx : FixedValidators M.toSlotLayout)
    {Δs : ℕ} {ΔNet : ℕ} (C : ClimbCtx M S A x GST tGAT tAwakeEnd T₁ r H₂ k₀ Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {w : V}
    {t₂ t : ℕ} (h2t : t₂ ≤ t) (hta : t < aR M S r) (hkt : x.stepBefore t ≤ k₀) (hw : w ∉ A.corruptedAtTime x t)
    (hL : H₂ + 1 ≤ M.head_height_floor (x.stateBefore t₂ w)) :
    H₂ + 1 ≤ M.head_height_floor (x.stateBefore t w) := by
  have hmm := (GoldilocksCorrectness.Record.Proofs.Executions.h_max_mono M F) S A x R C.E w h2t
  have hm2 := C.hmax_le M F R E Fx w (t := t₂) (le_trans ((stepBefore_mono M) x R E h2t) hkt)
  have hmt := C.hmax_le M F R E Fx w (t := t) hkt
  have hfl2 := (GoldilocksCorrectness.Record.Proofs.Routines.floor_le_h_max_of_core M F) S.C S.P S.X (x.stateBefore t₂ w) ((nodeInvCore_of_stateBefore M F) S A x R E t₂ w)
  rcases (GoldilocksCorrectness.Record.Proofs.Routines.floor_cases_of_core M F) S.C S.P S.X (x.stateBefore t₂ w) ((nodeInvCore_of_stateBefore M F) S A x R E t₂ w) with ⟨hc, -, hfl⟩ | ⟨-, hfl⟩
  swap
  · exfalso
    rw [hfl] at hL
    unfold Height at *
    omega
  have hmeq : hMax M S.C (x.stateBefore t w) = hMax M S.C (x.stateBefore t₂ w) := by
    unfold Height at *
    omega
  have hct := (GoldilocksCorrectness.Record.Proofs.Executions.contest_persists M F Fx) S A x R C.E C.hRoots tAwakeEnd t₂ t w C.hThird
    h2t (by have := C.hEnd; omega) hw hc hmeq (by omega)
  rcases (GoldilocksCorrectness.Record.Proofs.Routines.floor_cases_of_core M F) S.C S.P S.X (x.stateBefore t w) ((nodeInvCore_of_stateBefore M F) S A x R E t w) with ⟨-, -, hflt⟩ | ⟨hcf, -⟩
  · rw [hflt, hmeq, ← hfl]
    exact hL
  · rw [hct] at hcf
    cases hcf

/-! ## Every fork-choice change crosses one of the four levels -/

/-- **A fork-choice change of the climb crosses one of four levels.** At a step `j` whose real time
is after `T₁ + Δ` and before `aR M S r`, a `ForkChoiceChangeStep` at a validator honest at `j`
crosses one of the levels `H₂ − 1 ≤ h_j`, `H₂ ≤ head_height_floor`, `H₂ ≤ h_j`, `H₂ + 1 ≤ head_height_floor`: the
level fails at `x.st j w` and holds at `x.st (j + 1) w`.

Why: with the greatest chain-state height at `H₂` or `H₂ + 1` (B2, A2), a rise of
`head_height_floor` (which is the greatest chain-state height or the greatest chain-state height
minus one) is to `H₂` from `H₂ − 1`, or to `H₂ + 1`. A root that becomes the justified block `J`
with greatest chain-state height `h_j + 1` and is no ancestor of the old root comes with a rise of
`h_j` to `H₂ − 1` or `H₂`: were `h_j` unchanged, `J` would be too (Lemma 76) and the greatest
chain-state height as well, and the old root, the finalized block of a contested state (the old `J`
itself otherwise), would leave the new state contested by the same block (Lemma 89a), against its
root being `J`.

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed; `C`: the bundle.

Read aloud: a fork-choice change of an honest validator during the climb crosses one of four levels.
-/
theorem classify (U : UniformSchedule M.toSlotLayout) (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (Fx : FixedValidators M.toSlotLayout)
    (C : ClimbCtx M S A x GST tGAT tAwakeEnd T₁ r H₂ k₀ Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {w : V} {j : ℕ}
    {kT : ℕ} (hkT : x.lbl kT = Event.tick w (T₁ + Δ S)) (h1T : kT < j) (hta : x.time j < aR M S r)
    (hjk : j + 1 ≤ k₀) (hw : w ∉ A.corrupted j)
    (hch : ForkChoiceChangeStep M S A x w j) :
    (¬ H₂ - 1 ≤ (x.st j w).justifiedHeight ∧ H₂ - 1 ≤ (x.st (j + 1) w).justifiedHeight) ∨
    (¬ H₂ ≤ M.head_height_floor (x.st j w) ∧ H₂ ≤ M.head_height_floor (x.st (j + 1) w)) ∨
    (¬ H₂ ≤ (x.st j w).justifiedHeight ∧ H₂ ≤ (x.st (j + 1) w).justifiedHeight) ∨
    (¬ H₂ + 1 ≤ M.head_height_floor (x.st j w) ∧ H₂ + 1 ≤ M.head_height_floor (x.st (j + 1) w)) := by
  -- `w`'s honesty after the step: the change is `w`'s own tick, restart or delivery, which keeps the
  -- adversary set (`honest_succ_of_state_ne`)
  have hv_B3S1_w : w ∉ A.corrupted (j + 1) :=
    ((honest_succ_of_state_ne M F) x R C.E hw (state_ne_of_change_step M F hch)).1
  -- the change is `w`'s own step: it keeps `w`'s honesty and the time
  obtain ⟨hw1, htj⟩ := (honest_succ_of_state_ne M F) x R C.E hw (state_ne_of_change_step M F hch)
  have hAE : (aR M S r : ℝ) ≤ tAwakeEnd := by exact_mod_cast C.hEnd
  have hta1 : x.time (j + 1) < aR M S r := by rw [htj]; exact hta
  have hsj : kT ≤ j := h1T.le
  have hb0 := C.bounds_st M F U R Fx (j := j) (w := w) le_rfl hkT hsj hw (by omega) hta.le
  have hmm := (h_max_mono_st M F) S A x R C.E w (show j ≤ j + 1 by omega)
  have hb1 := C.hmax_le_st M F R Fx w (j := j + 1) hjk
  have hInv0 := (lem11_node_invariant M F S A x R E j w hw).1
  have hInv1 := (lem11_node_invariant M F S A x R E (j + 1) w hv_B3S1_w).1
  rcases hch with ⟨hr1, hm1, hnot⟩ | hfl
  · have hlt : (x.st j w).justifiedHeight < (x.st (j + 1) w).justifiedHeight := by
      by_contra hge
      push Not at hge
      have hj0 := (h_j_lt_h_max_st M F) S A x R E j w
      have heq : (x.st j w).justifiedHeight = (x.st (j + 1) w).justifiedHeight := by
        unfold Height at *
        omega
      have hmeq : hMax M S.C (x.st j w) = hMax M S.C (x.st (j + 1) w) := by
        unfold Height at *
        omega
      have hJ := (J_eq_of_h_j_eq_st M F Fx) S A x R E C.hRoots tAwakeEnd j (j + 1) w w C.hThird
        (le_trans hta.le hAE) (le_trans hta1.le hAE) hw hw1 heq (max_le hta.le hta1.le)
      have hc1 : M.fg_contest (x.st (j + 1) w) = false := by
        rcases (GoldilocksCorrectness.Record.Proofs.Routines.root_cases M F) S.C S.P S.X (x.st (j + 1) w) hInv1 with ⟨-, -, h⟩ | ⟨hF, hor⟩
        · exact h
        · exfalso
          rcases hor with hc | hne
          · obtain ⟨-, B, -, hFB, -, hJB⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.fg_contest_spec M F) S.C S.P S.X _ hInv1 hc
            exact hJB (by rw [← hr1, hF]; exact hFB)
          · exact hne hm1
      rcases (GoldilocksCorrectness.Record.Proofs.Routines.root_cases M F) S.C S.P S.X (x.st j w) hInv0 with ⟨hr0, -, -⟩ | ⟨-, hor0⟩
      · apply hnot
        rw [hr1, hr0, ← hJ]
        exact ancestorEq_refl _
      · rcases hor0 with hc0 | hne0
        · obtain ⟨-, Ab, hA, -, hAh, hJA⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.fg_contest_spec M F) S.C S.P S.X _ hInv0 hc0
          have hAt := (mem_T_mono M F) x R C.E w (show j ≤ j + 1 by omega) hA
          have hFA := (F_ancestorEq_of_high_st M F Fx) S A x R E C.hRoots tAwakeEnd (j + 1) j w w Ab
            C.hThird (le_trans hta1.le hAE) (le_trans hta.le hAE) hw1 hw hA
            (by rw [hAh, hmeq, hm1]; exact Nat.lt_succ_self _) (max_le hta1.le hta.le)
          have hct := (GoldilocksCorrectness.Record.Proofs.Routines.fg_contest_true_of M F) S.C S.P S.X _ hInv1 Ab hm1 hAt hFA
            (by rw [hAh, hmeq])
            (by rw [← hJ]; exact hJA)
          rw [hc1] at hct
          cases hct
        · apply hne0
          unfold Height at *
          omega
    by_cases hjv : (x.st (j + 1) w).justifiedHeight + 1 = H₂
    · left
      unfold Height at *
      exact ⟨by omega, by omega⟩
    · right; right; left
      unfold Height at *
      exact ⟨by omega, by omega⟩
  · have hf0 := (GoldilocksCorrectness.Record.Proofs.Routines.h_max_sub_one_le_floor M F) S.C S.P S.X (x.st j w) hInv0
    have hf1 := (GoldilocksCorrectness.Record.Proofs.Routines.floor_le_h_max M F) S.C S.P S.X (x.st (j + 1) w) hInv1
    by_cases hf : M.head_height_floor (x.st (j + 1) w) = H₂ + 1
    · right; right; right
      unfold Height at *
      exact ⟨by omega, by omega⟩
    · right; left
      unfold Height at *
      exact ⟨by omega, by omega⟩

end ClimbCtx

/-! ## The four kinds of fork-choice change -/

/-- **The four kinds of fork-choice change.** The
proof; the audited statement is in `Statements/Executions/Lemma89Statements.lean`.

The route: every fork-choice change crosses one of four levels
(`ClimbCtx.classify`); each level reached by
an honest validator reaches every honest validator within one delay (`spread_level_…`) and stays
reached (`mono_level_…`, `h_j_mono`), so its crossings lie within one delay after the first time
from `T₁` some honest validator has it (`kind_time`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the
  times; `T₁`: the time of the threshold; `r`: the round; `H₂`: the threshold.

Roots name blocks until `aR M S r`: every change the conclusion classifies is at a time before
`aR M S r`, and the levels are read before times at most `aR M S r` (the bundle `ClimbCtx`).

Read aloud: before the fast block's round, the members' roots and `head_height_floor`s change in at
most four bursts, each within one delay. -/
theorem fork_choice_change_kinds (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd T₁ r H₂ : ℕ)

    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (aR M S r))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT) (hT₁s : tGAT + Δs ≤ T₁)
    (hTick : ∀ (c : ℕ) (w : V) (k : ℕ), T₁ ≤ c → x.lbl k = Event.tick w (c + Δ S) → x.time k ≤ tAwakeEnd → w ∉ A.corrupted k → ∃ k' : ℕ, x.lbl k' = Event.tick w c)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hH₂ : OldHeightAttained M S A x T₁ H₂)
    (k₀ : ℕ)
    (hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂)
    -- every attestation put on the wire by a tick at a step before `k₀`, by a validator outside the adversary set at
    -- `tAwakeEnd`, has height at most `H₂`
    (hOldStep : ∀ (k t : ℕ) (u : V) (a' : Attestation V), k < k₀ → x.lbl k = Event.tick u t →
      u ∉ A.corruptedAtTime x tAwakeEnd →
      (⟨u, NamedObject.attest a'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (k + 1) - x.sent k → a'.h ≤ H₂)
    (hEnd : aR M S r ≤ tAwakeEnd) :
    ∃ τ : Fin 4 → ℝ, ∀ (w : V) (j : ℕ), x.lbl (x.tickStep w (T₁ + Δ S)) = Event.tick w (T₁ + Δ S) →
      x.tickStep w (T₁ + Δ S) < j → x.time j < aR M S r →
      j + 1 ≤ k₀ → w ∉ A.corrupted j → ForkChoiceChangeStep M S A x w j →
      ∃ c : Fin 4, τ c ≤ x.time j ∧
        (∀ (k' c' : ℕ), x.lbl k' = Event.tick w c' → τ c + ΔClockAhead + Δ S ≤ c' → j < k') ∧ (T₁ : ℝ) < τ c := by
  classical
  have hΔ := GoldilocksCorrectness.Proofs.Routines.one_le_Δ S
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hAE : (aR M S r : ℝ) ≤ tAwakeEnd := by exact_mod_cast hEnd
  -- the bundle's end step: the earlier of `k₀` and the configuration in force at `aR M S r`
  have hk₁E : x.time (min k₀ (x.stepBefore (aR M S r))) ≤ tAwakeEnd :=
    le_trans (R.time_mono (min_le_right _ _)) (le_trans ((time_stepBefore_le M) x R E (aR M S r)) hAE)
  have C : ClimbCtx M S A x GST tGAT tAwakeEnd T₁ r H₂ (min k₀ (x.stepBefore (aR M S r))) Δs (releaseOf M S.C)
      ΔRedeliver ΔClockAhead ΔClockBehind ΔNet :=
    { E := E, hNet := hNet, hSkew := hSkew, hRedeliver := hRedeliver, Sy := Sy, hΔs := hΔs, hRoots := hRoots,
      hParent := hParent, hGST := hGST, hT₁ := hT₁s, hThird := hThird, hAwake := hAwake, hH₂ := hH₂, hOld := hOld,
      hEnd := hEnd, hOldStep := fun k t u a' hk => hOldStep k t u a' (lt_of_lt_of_le hk (min_le_left _ _)),
      hEndStep := hk₁E, hTick := hTick }
  -- a crossing step of a validator honest at it is its own step: it keeps its honesty and the time
  have hkeep : ∀ (P : M.N → Prop) (w : V) (j : ℕ),
      (w ∉ A.corrupted j ∧ j + 1 ≤ min k₀ (x.stepBefore (aR M S r)) ∧
        ∃ kT : ℕ, x.lbl kT = Event.tick w (T₁ + Δ S) ∧ kT < j) →
      ¬ P (x.st j w) → P (x.st (j + 1) w) → w ∉ A.corrupted (j + 1) ∧ x.time (j + 1) = x.time j := by
    intro P w j hw hn hy
    exact (honest_succ_of_state_ne M F) x R E hw.1 (fun h => hn (by rw [h] at hy; exact hy))
  -- the receiver of a spread is active from `tGAT` up to its tick
  have hwA : ∀ (w : V) (j kT : ℕ), kT ≤ j → x.time j < aR M S r → w ∉ A.corrupted j →
      ∀ l : ℕ, (tGAT : ℝ) ≤ x.time l → l ≤ kT → w ∈ A.active l := by
    intro w j kT hsi hta hw l h1 h2
    have hwl : w ∉ A.corrupted l := fun h => hw (E.corrupted_mono l j (le_trans h2 hsi) h)
    exact Activity.mem_active.2 ⟨hAwake l w (le_trans (R.time_mono (le_trans h2 hsi)) (le_trans hta.le hAE))
      (le_trans h1 (R.time_mono (Nat.le_succ l))) hwl, hwl⟩
  -- the four levels, each crossed only before the crossing validator's tick to its time plus one delay
  obtain ⟨τ0, h0⟩ := kind_time_step_real M F x.time (fun w j => x.clockValue j w) (fun w k c => x.lbl k = Event.tick w c)
    (fun u k => u ∉ A.corrupted k)
    (fun w j => w ∉ A.corrupted j ∧ j + 1 ≤ min k₀ (x.stepBefore (aR M S r)) ∧
      ∃ kT : ℕ, x.lbl kT = Event.tick w (T₁ + Δ S) ∧ kT < j)
    (fun w j => H₂ - 1 ≤ (x.st j w).justifiedHeight) T₁ (Δ S) (aR M S r) ΔClockAhead hA0 (fun _ _ h => R.time_mono h)
    (fun u k => (clockValue_le_time_add_ahead M F) x R E k u)
    (fun w j => hkeep (fun n => H₂ - 1 ≤ n.justifiedHeight) w j)
    (fun τ u k hT hj hjc hu hL w j kT hkT hsi hta hw =>
      (C.spread_level_h_j M F U R E hNet hSkew hRedeliver Sy hΔs Fx (H₂ - 1)) hT hj hjc hu hL hkT hsi
        (hwA w j kT hsi hta hw.1) hta hw.1)
  obtain ⟨τ1, h1⟩ := kind_time_step_real M F x.time (fun w j => x.clockValue j w) (fun w k c => x.lbl k = Event.tick w c)
    (fun u k => u ∉ A.corrupted k)
    (fun w j => w ∉ A.corrupted j ∧ j + 1 ≤ min k₀ (x.stepBefore (aR M S r)) ∧
      ∃ kT : ℕ, x.lbl kT = Event.tick w (T₁ + Δ S) ∧ kT < j)
    (fun w j => H₂ ≤ M.head_height_floor (x.st j w)) T₁ (Δ S) (aR M S r) ΔClockAhead hA0 (fun _ _ h => R.time_mono h)
    (fun u k => (clockValue_le_time_add_ahead M F) x R E k u)
    (fun w j => hkeep (fun n => H₂ ≤ M.head_height_floor n) w j)
    (fun τ u k hT hj hjc hu hL w j kT hkT hsi hta hw =>
      (C.spread_level_floor M F U R E hNet hSkew hRedeliver Sy hΔs Fx) hT hj hjc hu hL hkT hsi
        (hwA w j kT hsi hta hw.1) hta (by have := hw.2.1; omega) hw.1)
  obtain ⟨τ2, h2⟩ := kind_time_step_real M F x.time (fun w j => x.clockValue j w) (fun w k c => x.lbl k = Event.tick w c)
    (fun u k => u ∉ A.corrupted k)
    (fun w j => w ∉ A.corrupted j ∧ j + 1 ≤ min k₀ (x.stepBefore (aR M S r)) ∧
      ∃ kT : ℕ, x.lbl kT = Event.tick w (T₁ + Δ S) ∧ kT < j)
    (fun w j => H₂ ≤ (x.st j w).justifiedHeight) T₁ (Δ S) (aR M S r) ΔClockAhead hA0 (fun _ _ h => R.time_mono h)
    (fun u k => (clockValue_le_time_add_ahead M F) x R E k u)
    (fun w j => hkeep (fun n => H₂ ≤ n.justifiedHeight) w j)
    (fun τ u k hT hj hjc hu hL w j kT hkT hsi hta hw =>
      (C.spread_level_h_j M F U R E hNet hSkew hRedeliver Sy hΔs Fx H₂) hT hj hjc hu hL hkT hsi
        (hwA w j kT hsi hta hw.1) hta hw.1)
  obtain ⟨τ3, h3⟩ := kind_time_step_real M F x.time (fun w j => x.clockValue j w) (fun w k c => x.lbl k = Event.tick w c)
    (fun u k => u ∉ A.corrupted k)
    (fun w j => w ∉ A.corrupted j ∧ j + 1 ≤ min k₀ (x.stepBefore (aR M S r)) ∧
      ∃ kT : ℕ, x.lbl kT = Event.tick w (T₁ + Δ S) ∧ kT < j)
    (fun w j => H₂ + 1 ≤ M.head_height_floor (x.st j w)) T₁ (Δ S) (aR M S r) ΔClockAhead hA0 (fun _ _ h => R.time_mono h)
    (fun u k => (clockValue_le_time_add_ahead M F) x R E k u)
    (fun w j => hkeep (fun n => H₂ + 1 ≤ M.head_height_floor n) w j)
    (fun τ u k hT hj hjc hu hL w j kT hkT hsi hta hw =>
      (C.spread_level_floor_succ M F U R E hNet hSkew hRedeliver Sy hΔs Fx) hT hj hjc hu hL hkT hsi
        (hwA w j kT hsi hta hw.1) hta (by have := hw.2.1; omega) hw.1)
  refine ⟨fun c : Fin 4 => match c with | 0 => τ0 | 1 => τ1 | 2 => τ2 | 3 => τ3, ?_⟩
  intro w j hlbl hlt hta hjk hw hch
  obtain ⟨-, htj⟩ := (honest_succ_of_state_ne M F) x R E hw (state_ne_of_change_step M F hch)
  -- the change step is before the configuration in force at `aR M S r`
  have hjk₁ : j + 1 ≤ min k₀ (x.stepBefore (aR M S r)) := by
    refine le_min hjk ?_
    have : j < x.stepBefore (aR M S r) := ((lt_stepBefore_iff M) x R E).2 (by rw [htj]; exact hta)
    omega
  -- the change step is after `T₁`: it comes after `w`'s tick to `T₁ + Δ`, whose real time is less than
  -- `ΔClockAhead < Δ` before that clock value
  have hT₁j : (T₁ : ℝ) < x.time j := by
    have h1 := (E.tick_active _ w (T₁ + Δ S) hlbl).2.1
    have h2 := R.time_mono hlt.le
    push_cast at h1
    have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
    linarith
  have hR : w ∉ A.corrupted j ∧ j + 1 ≤ min k₀ (x.stepBefore (aR M S r)) ∧
      ∃ kT : ℕ, x.lbl kT = Event.tick w (T₁ + Δ S) ∧ kT < j := ⟨hw, hjk₁, _, hlbl, hlt⟩
  rcases (C.classify M F U R E hNet hSkew hRedeliver Sy hΔs Fx) hlbl hlt hta hjk₁ hw hch with h | h | h | h
  · exact ⟨0, h0 w j hT₁j hta hR h.1 h.2⟩
  · exact ⟨1, h1 w j hT₁j hta hR h.1 h.2⟩
  · exact ⟨2, h2 w j hT₁j hta hR h.1 h.2⟩
  · exact ⟨3, h3 w j hT₁j hta hR h.1 h.2⟩

end GoldilocksCorrectness.Record.Proofs.Executions

