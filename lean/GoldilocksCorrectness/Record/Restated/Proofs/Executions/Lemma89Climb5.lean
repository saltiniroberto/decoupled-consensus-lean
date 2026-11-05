module
public import GoldilocksCorrectness.Record.Restated.Proofs.View.Bridges
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89ClimbLate
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89Count
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.Lemma89CountDefs
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Proofs.View.Bridges
public import GoldilocksCorrectness.Proofs.Executions.Lemma89ClimbLate
public import GoldilocksCorrectness.Proofs.Executions.Lemma89Count
public import GoldilocksCorrectness.Statements.Executions.Lemma89CountDefs
public import GoldilocksCorrectness.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89rQuietRound
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma89Climb5, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma89Climb5.lean`, over a model `M` whose
facts `F` hold, for an execution `x` of `protocolOf M S`: part B of Lemma 89, the climb to the first
honest fast block on the span premise `OpeningsOutsideWaitsAndWindows` (three span lengths, the
count 9), namely an honest round opening slot's proposal held by its proposer and unique, the count
of honest round opening slots outside the spans before a round, the spans of an appended family, and
the climb itself. The page's routine-level theorems are the facts' fields or have their twins in
phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ Δ_F slotStart voteTime supportCutoff anchorCW)
open GoldilocksCorrectness.Proofs.Routines (after_of_before one_le_Δ slotStart_div_le slotStart_eq
  slotStart_mono supportCutoff_eq supportCutoff_mono supportCutoff_succ_eq voteTime_eq
  voteTime_mono)

open GoldilocksCorrectness.Proofs.Routines (slot_lt_of_ancestorEq_of_treeClosed)

open GoldilocksCorrectness.Proofs.Routines (anchorCW_eq)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Proofs.Executions (r_lt_of_lt_of_mono)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax IsEntry VoterTreeAt JustifiedInTree AnchorAt)
open GoldilocksCorrectness.Record.Statements.Routines (ConfirmationUpdated)

open GoldilocksCorrectness.Record.Statements.Routines (TreeClosed)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (InSpan OpeningsOutsideWaitsAndWindows
  OutsideSpans Vocab.goldilocks acObject fgObject healFrontSlots)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  genesis_ancestorEq ancestorEq_compatible ancestorEq_antisymm ancestorEq_genesis_iff)
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn expireLocks)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-! ## Kit -/

/-- **An opening's proposal has the opening's slot and is held by its proposer.** With the honest
openings `rs 0 < … < rs m` and no opening's proposal colliding with a block its proposer held: a
proposal `B` of opening `j ≤ m` has slot `rs j * R`, and the proposer of that slot holds `B` in the
state its tick to the slot's start leaves (`x.tickOutput`).

Why: `B`'s parent is a viable head of its proposer (`proposal_parent_viable_head`), its root is new
to the proposer (no collision), so the proposer holds it after its tick
(`lem22a_proposer_holds_own_proposal`); the walk's end gives its slot (`proposal_parent_walk_end`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tGAT`, `tAwakeEnd`: the phase; `m`:
  the index of the last honest round opening slot; `j`: the index of an honest round opening slot; `rs`: the rounds of the honest round opening slots; `B`: the proposal.

Read aloud: a proposal of an honest round opening slot has that slot, and its proposer holds it right
after the tick that proposes it, when no honest round opening slot's proposal collides with a block
its proposer held. -/
theorem opening_proposal_held (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (tGAT tAwakeEnd m j : ℕ) (rs : ℕ → ℕ) (B : Block V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSeq : HonestOpeningSeq M S A x rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hj : j ≤ m) (hNoCol : ¬ RootCollisionAtOpening M S A x rs m)
    (hB : ProposalAt M S x (rs j * S.C.R) B) :
    B.slot = rs j * S.C.R ∧
      B ∈ (x.tickOutput (S.P.proposer (rs j * S.C.R)) (M.slotStart S.C (rs j * S.C.R))).tree := by
  have hk := S.C.k_ge_two
  have hmono := r_lt_of_lt_of_mono rs m hSeq.mono
  have h0j : rs 0 * S.C.R ≤ rs j * S.C.R := by
    rcases Nat.eq_zero_or_pos j with h | h
    · rw [h]
    · exact Nat.mul_le_mul_right _ (le_of_lt (hmono 0 j h hj))
  obtain ⟨h2k, -⟩ := (window_after_anchor M F U) S A x rs m tGAT tAwakeEnd (rs j * S.C.R) hSeq h0j
  set s'' := rs j * S.C.R with hs''def
  clear_value s''
  have hB'0 : ProposalAt M S x (s'' - 1 + 1) B := by
    rw [show s'' - 1 + 1 = s'' by omega]
    exact hB
  have hPV' := (proposal_parent_viable_head M F U) S A x R E (s'' - 1) B _ hB'0
  obtain ⟨iB'', hlB'', hsentB''⟩ := hB'0
  have hPV'' := ((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_heads_iff M F) S.C S.P S.X _
    ((nodeInv_tickInput_of_tick M F) S A x R E hlB'') _).1 hPV'
  obtain ⟨hslot, -, hB'par?, -⟩ := (proposal_parent_walk_end M F U) S A x R E (s'' - 1) iB'' B _
    hlB'' hsentB''
  have hPB' := GoldilocksCorrectness.Proofs.Routines.ancestorEq_of_parent? hB'par?
  -- no block of the proposer's tick input has `B`'s root: the openings do not collide
  have hRootNew' : ∀ B₁ ∈ (x.tickInput (S.P.proposer (s'' - 1 + 1)) (M.slotStart S.C (s'' - 1 + 1))).tree,
      B₁.root ≠ B.root := by
    intro B₁ hB₁ heq
    apply hNoCol
    rw [(GoldilocksCorrectness.Record.Proofs.View.rootCollisionAtOpening_unfold M x)]
    refine ⟨j, hj, B, ?_, ?_⟩
    · rw [← hs''def]
      exact hB
    · rw [← hs''def]
      rw [(GoldilocksCorrectness.Record.Proofs.View.rootCollisionAtProposal_unfold M x)]
      rw [show s'' - 1 + 1 = s'' by omega] at hB₁
      exact ⟨B₁, hB₁, heq⟩
  have hBq := (lem22a_proposer_holds_own_proposal M F U) S A x R (s'' - 1) iB'' B _ E hlB''
    hsentB'' hRootNew' hPV''.1
    ((compatible_iff _ _).2 (Or.inl (ancestorEq_trans hPV''.2.1 hPB')))
  refine ⟨hslot.trans (by omega : s'' - 1 + 1 = s''), ?_⟩
  have hto : x.tickOutput (S.P.proposer (s'' - 1 + 1)) (M.slotStart S.C (s'' - 1 + 1)) = x.st (iB'' + 1)
      (S.P.proposer (s'' - 1 + 1)) := by
    unfold Trace.tickOutput; rw [(tickStep_eq_of_lbl M) x E hlB'']
  rw [← hto] at hBq
  rw [show s'' - 1 + 1 = s'' by omega] at hBq
  exact hBq

/-- **An opening's proposal is held by its proposer in the state its tick leaves.** With the honest
round opening slots of the rounds `rs 0 < … < rs m` and no opening's proposal colliding with a block its
proposer held: the proposer of opening `j ≤ m` holds a proposal `B` of that opening in the state its tick
to the start of the opening's slot leaves (`x.tickOutput`), the tick that put `B` on the wire.

Why: the second conjunct of `opening_proposal_held`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tGAT`, `tAwakeEnd`: the phase; `m`:
  the index of the last honest round opening slot; `j`: the index of an honest round opening slot; `rs`:
  the rounds of the honest round opening slots; `B`: the proposal.

Read aloud: a proposal of an honest round opening slot is held by its proposer right after the tick
that proposes it, when no honest round opening slot's proposal collides with a block its proposer
held. -/
theorem opening_proposal_held_tickOutput (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (tGAT tAwakeEnd m j : ℕ) (rs : ℕ → ℕ) (B : Block V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSeq : HonestOpeningSeq M S A x rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hj : j ≤ m) (hNoCol : ¬ RootCollisionAtOpening M S A x rs m)
    (hB : ProposalAt M S x (rs j * S.C.R) B) :
    B ∈ (x.tickOutput (S.P.proposer (rs j * S.C.R)) (M.slotStart S.C (rs j * S.C.R))).tree :=
  ((opening_proposal_held M F U) S A x R tGAT tAwakeEnd m j rs B E hSeq hj hNoCol hB).2

/-- **An opening has one proposal.** With the honest round opening slots of the rounds `rs 0 < … < rs m`, unforgeability
and no opening's proposal colliding with a block its proposer held: two proposals of opening
`j ≤ m` are equal.

Why: the proposer holds the first one one time unit after the slot's start, with the slot's number
(`opening_proposal_held`), and is honest through that time (`HonestOpeningSeq.honest`); the only
block of that slot an honest validator holds is the proposal (`only_block_of_unforgeability`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tGAT`, `tAwakeEnd`: the phase; `m`:
  the index of the last honest round opening slot; `j`: the index of an honest round opening slot; `rs`: the rounds of the honest round opening slots; `B`, `B'`: the
  proposals.

Read aloud: an honest round opening slot has at most one proposal, when no honest round opening
slot's proposal collides with a block its proposer held. -/
theorem opening_proposal_unique (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (tGAT tAwakeEnd m j : ℕ) (rs : ℕ → ℕ) (B B' : Block V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSeq : HonestOpeningSeq M S A x rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hj : j ≤ m) (hNoCol : ¬ RootCollisionAtOpening M S A x rs m)
    (hB : ProposalAt M S x (rs j * S.C.R) B)
      (hB' : ProposalAt M S x (rs j * S.C.R) B') :
    B = B' := by
  obtain ⟨hslot, hheld⟩ := (opening_proposal_held M F U) S A x R tGAT tAwakeEnd m j rs B E hSeq
    hj hNoCol hB
  -- the proposer is outside the adversary set at the step after its tick to the slot's start: a tick keeps the
  -- adversary set, and a tick is by a validator outside it
  obtain ⟨i, hl, -⟩ := hB
  have hts := (tickStep_eq_of_lbl M) x E hl
  have hp : S.P.proposer (rs j * S.C.R) ∉
      A.corrupted (x.tickStep (S.P.proposer (rs j * S.C.R)) (M.slotStart S.C (rs j * S.C.R)) + 1) := by
    rw [hts, E.corrupted_keep i (by rw [hl]; exact fun h => by cases h)]
    exact E.not_mem_corrupted_of_tick hl
  exact (only_block_of_unforgeability_st M F U) S A x R E (rs j * S.C.R)
    (x.tickStep (S.P.proposer (rs j * S.C.R)) (M.slotStart S.C (rs j * S.C.R)) + 1)
    B' B _ _ hp rfl hB' hheld hslot

/-! ## The count before the fast block's round -/

/-- **The climb's end step for `fork_choice_change_kinds`.** Take `k₀` to be the first step whose real time reaches
the support cutoff of slot `r R`. When every honest attestation put on the wire by a tick to a clock value less than
`aR M S r` has height at most `H₂` (the clock form `hOld`, honesty read at `aR M S r ≤ tAwakeEnd`), then every
attestation put on the wire by a tick at a step before `k₀`, by a validator outside the adversary set at `tAwakeEnd`,
has height at most `H₂` (the step form at `k₀`); and every step at a real time less than that support cutoff is
followed by a step at most `k₀`.

Why: a step before `k₀` is at a real time less than the support cutoff of slot `r R`, so a tick there is to a clock
value less than that cutoff plus `ΔClockAhead` (`tick_active`); the cutoff is `4 Δ S` before `aR M S r`
(the uniform layout) and `ΔClockAhead < Δ S` (`hSkew`), so the clock value is less than `aR M S r`. A validator
outside the adversary set at `tAwakeEnd` is outside it at `aR M S r`. The second part is
`time_lt_iff_le_stepBefore` with `x.firstAt c = x.stepBefore c + 1`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`: the setup, the activity, the execution; `R`, `E`: the run's and the environment's facts;
- `tAwakeEnd`: the phase's end; `r`: the round; `H₂`: the bound.

Read aloud: nothing put on the wire before the first step at the support cutoff of slot `r R` attests higher than
`H₂`, and every step before that cutoff comes before that step. -/
theorem climb_end_step_firstAt_supportCutoff (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (tAwakeEnd r H₂ : ℕ)
    (hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂) (hEnd : aR M S r ≤ tAwakeEnd) :
    (∀ (k t : ℕ) (u : V) (a' : Attestation V), k < x.firstAt (M.supportCutoff S.C (r * S.C.R)) →
      x.lbl k = Event.tick u t → u ∉ A.corruptedAtTime x tAwakeEnd →
      (⟨u, NamedObject.attest a'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (k + 1) - x.sent k → a'.h ≤ H₂) ∧
    (∀ j : ℕ, x.time j < M.supportCutoff S.C (r * S.C.R) →
      j + 1 ≤ x.firstAt (M.supportCutoff S.C (r * S.C.R))) := by
  have hΔ := one_le_Δ S
  have hc : M.supportCutoff S.C (r * S.C.R) = 4 * Δ S * (r * S.C.R) + 2 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (r * S.C.R),
      (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (r * S.C.R),
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (r * S.C.R)]
    omega
  have haR : aR M S r = M.supportCutoff S.C (r * S.C.R) + 4 * Δ S := by
    unfold aR
    rw [hc, (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (r * S.C.R + 1),
      (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (r * S.C.R + 1),
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (r * S.C.R + 1),
      Nat.mul_add]
    omega
  have h1 : 1 ≤ M.supportCutoff S.C (r * S.C.R) := by rw [hc]; omega
  have hfa := (firstAt_eq_stepBefore_succ M F) x R E h1
  have hrange : ∀ j : ℕ, x.time j < M.supportCutoff S.C (r * S.C.R) →
      j + 1 ≤ x.firstAt (M.supportCutoff S.C (r * S.C.R)) := fun j hj => by
    rw [hfa]
    exact Nat.succ_le_succ (((time_lt_iff_le_stepBefore M) x R E h1).1 hj)
  refine ⟨fun k t u a' hk hl hu hs => ?_, hrange⟩
  have hkt : x.time k < M.supportCutoff S.C (r * S.C.R) := by
    rw [hfa] at hk
    exact ((time_lt_iff_le_stepBefore M) x R E h1).2 (Nat.le_of_lt_succ hk)
  have ht := (E.tick_active k u t hl).2.1
  have hb := E.behind_nonneg
  refine hOld k t u a' hl ?_ ((not_mem_corruptedAtTime_of_le M) x R E hEnd hu) hs
  have hΔr : (Δ S : ℝ) ≥ 1 := by exact_mod_cast hΔ
  rw [haR]
  push_cast
  linarith

/-- **The climb's end step at the view freeze of slot `r R`** (re-check 61, section 2.5; the twin of
`climb_end_step_firstAt_supportCutoff`). Every attestation put on the wire by a tick of a validator outside the
adversary set at `tAwakeEnd`, at a step before the first step at the view freeze of slot `r R`, has height at most
`H₂`; and every step before that view freeze is before that first step.

Why: a step before the first step at the view freeze is at a real time less than the view freeze, `Δ` after the
support cutoff of slot `r R` (the uniform layout); a tick there is to a clock value less than the view freeze plus
`ΔClockAhead` (`tick_active`), less than the cutoff plus `2Δ` (`ΔClockAhead < Δ`, `hSkew`), at most `aR M S r`, the
cutoff plus `4Δ`; `hOld` bounds such attestations. A validator outside the adversary set at `tAwakeEnd` is outside
it at `aR M S r`. The second part is `time_lt_iff_le_stepBefore` with `x.firstAt c = x.stepBefore c + 1`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`: the setup, the activity, the execution; `R`, `E`: the run's and the environment's facts;
- `tAwakeEnd`: the phase's end; `r`: the round; `H₂`: the bound.

Read aloud: nothing put on the wire before the first step at the view freeze of slot `r R` attests higher than
`H₂`, and every step before that view freeze comes before that step. -/
theorem climb_end_step_firstAt_viewFreeze (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (tAwakeEnd r H₂ : ℕ)
    (hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂) (hEnd : aR M S r ≤ tAwakeEnd) :
    (∀ (k t : ℕ) (u : V) (a' : Attestation V), k < x.firstAt (M.viewFreeze S.C (r * S.C.R)) →
      x.lbl k = Event.tick u t → u ∉ A.corruptedAtTime x tAwakeEnd →
      (⟨u, NamedObject.attest a'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (k + 1) - x.sent k → a'.h ≤ H₂) ∧
    (∀ j : ℕ, x.time j < M.viewFreeze S.C (r * S.C.R) →
      j + 1 ≤ x.firstAt (M.viewFreeze S.C (r * S.C.R))) := by
  have hΔ := one_le_Δ S
  have hc : M.viewFreeze S.C (r * S.C.R) = 4 * Δ S * (r * S.C.R) + 3 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_eq M.toSlotLayout F.sched U) S (r * S.C.R),
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (r * S.C.R)]
  have haR : aR M S r = 4 * Δ S * (r * S.C.R) + 6 * Δ S := by
    unfold aR
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (r * S.C.R + 1),
      (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (r * S.C.R + 1),
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (r * S.C.R + 1),
      Nat.mul_add]
    omega
  have h1 : 1 ≤ M.viewFreeze S.C (r * S.C.R) := by rw [hc]; omega
  have hfa := (firstAt_eq_stepBefore_succ M F) x R E h1
  have hrange : ∀ j : ℕ, x.time j < M.viewFreeze S.C (r * S.C.R) →
      j + 1 ≤ x.firstAt (M.viewFreeze S.C (r * S.C.R)) := fun j hj => by
    rw [hfa]
    exact Nat.succ_le_succ (((time_lt_iff_le_stepBefore M) x R E h1).1 hj)
  refine ⟨fun k t u a' hk hl hu hs => ?_, hrange⟩
  have hkt : x.time k < M.viewFreeze S.C (r * S.C.R) := by
    rw [hfa] at hk
    exact ((time_lt_iff_le_stepBefore M) x R E h1).2 (Nat.le_of_lt_succ hk)
  have ht := (E.tick_active k u t hl).2.1
  have hb := E.behind_nonneg
  refine hOld k t u a' hl ?_ ((not_mem_corruptedAtTime_of_le M) x R E hEnd hu) hs
  have hΔr : (Δ S : ℝ) ≥ 1 := by exact_mod_cast hΔ
  rw [hc] at hkt
  rw [haR]
  push_cast at hkt ⊢
  linarith

/-- **A tick in the phase before a later step.** A validator outside the adversary set at a step `j` in the phase
(every validator honest at a step is awake there, `hAwake`) ticked to every clock value `c ≥ 1` whose window
`[c − ΔClockAhead, c + ΔClockBehind]` starts at or after `tGAT` and ends before the real time of `j`, at a step
before `j`.

Why: every step whose real time is in the window is before `j` (its time is less than `j`'s), so the validator is
outside the adversary set there (corruption is permanent) and, the step's successor being at a real time at least
`tGAT`, awake there (`hAwake`); `tick_of_active` then gives the tick, at a real time in the window, so before `j`.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `A`, `x`: the setup, the activity, the execution; `R`, `E`: the run's and the environment's facts;
- `tGAT`, `tAwakeEnd`: the ends of the phase; `c`: the clock value; `j`: the later step; `w`: the validator.

Read aloud: a validator honest at a step of the phase ticked, before that step, to every clock value whose window
lies in the phase before that step. -/
theorem tick_before_step_in_phase (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)
    (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {tGAT tAwakeEnd : ℕ}
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (c j : ℕ) (w : V) (hc : 1 ≤ c) (hcG : (tGAT : ℝ) ≤ c - ΔClockAhead)
    (hcj : (c : ℝ) + ΔClockBehind < x.time j) (hjE : x.time j ≤ tAwakeEnd) (hw : w ∉ A.corrupted j) :
    ∃ i : ℕ, x.lbl i = Event.tick w c ∧ i < j := by
  obtain ⟨i, hi, -, hi2⟩ := E.tick_of_active c hc w (fun i h1 h2 => by
    have hij : i < j := (lt_of_time_lt M) x R (by linarith)
    have hwi : w ∉ A.corrupted i := E.not_mem_corrupted_of_le hij.le hw
    have hti1 := (time_mono M) x R (Nat.le_succ i)
    have htj := (time_mono M) x R hij.le
    exact Activity.mem_active.2 ⟨hAwake i w (by linarith) (by linarith) hwi, hwi⟩)
  exact ⟨i, hi, (lt_of_time_lt M) x R (by linarith)⟩

/-- **The two bounds of a fork-choice change on its kind's clock value.** For a step `j` of the phase at which `w`
is outside the adversary set and which keeps the real time (`x.time (j + 1) = x.time j`), and a clock value `τ`
greater than `T₁ ≥ tGAT` that is at most every natural number at least both `j`'s real time and `w`'s clock value
after `j`, with every tick of `w` to `τ + Δ` after `j` (the conclusion of `fork_choice_change_kinds`): `τ + Δ` is
less than `N + 2Δ` for every natural number `N` greater than `j`'s real time, and `j`'s real time is at most
`τ + Δ + ΔClockBehind`.

Why: `w`'s clock value after `j` is at most `j`'s real time plus `ΔClockAhead` (`clockValue_le_time_add_ahead`),
so less than `N + Δ` (`ΔClockAhead < Δ` by `hSkew`); so `τ ≤ N + Δ − 1`. If `j`'s real time were greater than
`τ + Δ + ΔClockBehind`, the window of the clock value `τ + Δ`, which starts after `T₁` (`τ > T₁`, `ΔClockAhead < Δ`)
and ends at `τ + Δ + ΔClockBehind`, would lie in the phase before `j`, and `w` would have ticked to `τ + Δ` before `j`
(`tick_before_step_in_phase`), which the second hypothesis excludes.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `A`, `x`: the setup, the activity, the execution; `R`, `E`: the run's and the environment's facts;
- `tGAT`, `tAwakeEnd`: the ends of the phase; `T₁`: the threshold's time; `τ`: the kind's clock value; `j`: the
  step; `w`: the validator.

Read aloud: a change classified at the clock value `τ` has `τ + Δ` less than `N + 2Δ` for every natural number `N`
after the change, and happens at a real time at most `τ + Δ + ΔClockBehind`. -/
theorem kind_clock_bounds (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)
    (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) {tGAT tAwakeEnd T₁ : ℕ}
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hT₁ : tGAT ≤ T₁) (τ j : ℕ) (w : V) (hτT : T₁ < τ) (hjE : x.time j ≤ tAwakeEnd)
    (hw : w ∉ A.corrupted j) (htj : x.time (j + 1) = x.time j)
    (h1 : ∀ n : ℕ, x.time j ≤ n → x.clockValue (j + 1) w ≤ n → τ ≤ n)
    (h2 : ∀ k' : ℕ, x.lbl k' = Event.tick w (τ + Δ S) → j < k') :
    (∀ N : ℕ, x.time j < N → τ + Δ S < N + 2 * Δ S) ∧ x.time j ≤ (τ : ℝ) + Δ S + ΔClockBehind := by
  have hΔ := one_le_Δ S
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  refine ⟨fun N hN => ?_, ?_⟩
  · have hc := (clockValue_le_time_add_ahead M F) x R E (j + 1) w
    rw [htj] at hc
    have hcN : x.clockValue (j + 1) w < N + Δ S := by
      have h0 : (0 : ℝ) < (N : ℝ) + Δ S := by positivity
      have : (x.clockValue (j + 1) w : ℝ) < (N : ℝ) + Δ S :=
        lt_of_le_of_lt hc (max_lt h0 (by linarith))
      exact_mod_cast this
    have hN1 : (N : ℝ) ≤ ((N + Δ S - 1 : ℕ) : ℝ) := by exact_mod_cast (show N ≤ N + Δ S - 1 by omega)
    have := h1 (N + Δ S - 1) (by linarith) (by omega)
    omega
  · by_contra hge
    push Not at hge
    have hτR : (T₁ : ℝ) + 1 ≤ τ := by exact_mod_cast hτT
    have hTR : (tGAT : ℝ) ≤ T₁ := by exact_mod_cast hT₁
    obtain ⟨i, hi, hij⟩ := (tick_before_step_in_phase M F) S A x R E hAwake (τ + Δ S) j w (by omega)
      (by push_cast; linarith) (by push_cast; exact hge) hjE hw
    exact absurd (h2 i hi) (by omega)

/-- **A fork-choice change is at most one delay and the clock's lag after its kind's real start, read at a clock value
.** For a step `j` of the phase at which `w` is outside the adversary set, a real time `τ` greater than
`T₁ ≥ tGAT`, with every tick of `w` to a clock value at least `τ + ΔClockAhead + Δ` after `j` (the conclusion of
`fork_choice_change_kinds`): `j`'s real time is at most `⌈τ + ΔClockAhead⌉₊ + Δ + ΔClockBehind`.

Why: otherwise the window of the clock value `⌈τ + ΔClockAhead⌉₊ + Δ`, which starts after `T₁` and ends at
`⌈τ + ΔClockAhead⌉₊ + Δ + ΔClockBehind`, lies in the phase before `j`, and `w` ticked to that clock value before `j`
(`tick_before_step_in_phase`); it is at least `τ + ΔClockAhead + Δ`, so the hypothesis puts that tick after `j`.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `A`, `x`: the setup, the activity, the execution; `R`, `E`: the run's and the environment's facts;
- `tGAT`, `tAwakeEnd`: the ends of the phase; `T₁`: the threshold's time; `τ`: the kind's real start; `j`: the
  step; `w`: the validator.

Read aloud: a change classified at the real start `τ` happens at a real time at most the least natural number at
least `τ + ΔClockAhead`, plus one delay and `ΔClockBehind`. -/
theorem kind_clock_bounds_real (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)
    (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {tGAT tAwakeEnd T₁ : ℕ}
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hT₁ : tGAT ≤ T₁) (τ : ℝ) (j : ℕ) (w : V) (hτT : (T₁ : ℝ) < τ) (hjE : x.time j ≤ tAwakeEnd)
    (hw : w ∉ A.corrupted j)
    (h2 : ∀ (k' c' : ℕ), x.lbl k' = Event.tick w c' → τ + ΔClockAhead + Δ S ≤ c' → j < k') :
    x.time j ≤ (⌈τ + ΔClockAhead⌉₊ : ℝ) + Δ S + ΔClockBehind := by
  have hΔ := one_le_Δ S
  have hA0 := E.ahead_nonneg
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hce := Nat.le_ceil (τ + ΔClockAhead)
  by_contra hge
  push Not at hge
  have hTR : (tGAT : ℝ) ≤ T₁ := by exact_mod_cast hT₁
  obtain ⟨i, hi, hij⟩ := (tick_before_step_in_phase M F) S A x R E hAwake (⌈τ + ΔClockAhead⌉₊ + Δ S) j w (by omega)
    (by push_cast; linarith) (by push_cast; exact hge) hjE hw
  exact absurd (h2 i _ hi (by push_cast; linarith)) (by omega)

omit [RootOrder] in
/-- **A real kind start `τ'` with `τ' + Δ` in the slots from `s − k − 1` to `s` puts `s` in the span of the kind
.** The real-valued twin of `kind_span_of_bounds`: for a real `τ' ≥ 0` with `τ' + Δ` greater than the
start of slot `s − k − 1` and less than the start of slot `s + 1` (`k + 1 ≤ s`), the slot `s` is in the `k + 2` slots
from the slot `⌊(τ' + Δ) / (4Δ)⌋₊` of `τ' + Δ`.

Why: the slot of `τ' + Δ` is the integer part of `(τ' + Δ) / (4Δ)`, and slot `n` starts at `4Δ n` (the uniform layout).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `s`: the honest round opening slot; `τ'`: the real time the kind's span is read from, less one delay.

Read aloud: a real time `τ'` such that `τ' + Δ` is after the start of slot `s − k − 1` and before the start of slot
`s + 1` has slot `s` within the `k + 2` slots from the slot of `τ' + Δ`. -/
theorem kind_span_of_bounds_real (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (s : ℕ) (τ' : ℝ) (hk : S.C.k + 1 ≤ s) (h0 : 0 ≤ τ')
    (hU : τ' + Δ S < M.slotStart S.C (s + 1))
    (hL : (M.slotStart S.C (s - S.C.k - 1) : ℝ) < τ' + Δ S) :
    InSpan ⌊(τ' + Δ S) / (4 * Δ S)⌋₊ (S.C.k + 2) s := by
  have hΔ := one_le_Δ S
  rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U)] at hU hL
  have h4 : (0 : ℝ) < 4 * Δ S := by
    have : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
    linarith
  set σ := ⌊(τ' + Δ S) / (4 * Δ S)⌋₊ with hσ
  have hq0 : 0 ≤ (τ' + Δ S) / (4 * Δ S) := by positivity
  have hlo : (σ : ℝ) ≤ (τ' + Δ S) / (4 * Δ S) := Nat.floor_le hq0
  have hhi : (τ' + Δ S) / (4 * Δ S) < σ + 1 := Nat.lt_floor_add_one _
  have hlo' : (σ : ℝ) * (4 * Δ S) ≤ τ' + Δ S := by
    rw [le_div_iff₀ h4] at hlo
    exact hlo
  have hhi' : τ' + Δ S < ((σ : ℝ) + 1) * (4 * Δ S) := by
    rw [div_lt_iff₀ h4] at hhi
    exact hhi
  unfold InSpan
  push_cast at hU hL
  constructor
  · have : (σ : ℝ) * (4 * Δ S) < 4 * Δ S * ((s : ℝ) + 1) := lt_of_le_of_lt hlo' hU
    have : (σ : ℝ) < (s : ℝ) + 1 := by nlinarith
    have : σ < s + 1 := by exact_mod_cast this
    omega
  · obtain ⟨e, he⟩ : ∃ e, s = e + (S.C.k + 1) := ⟨s - (S.C.k + 1), by omega⟩
    have hsub : s - S.C.k - 1 = e := by omega
    rw [hsub] at hL
    have : (4 : ℝ) * Δ S * e < ((σ : ℝ) + 1) * (4 * Δ S) := lt_trans hL hhi'
    have : (e : ℝ) < (σ : ℝ) + 1 := by nlinarith
    have : e < σ + 1 := by exact_mod_cast this
    omega

open Classical in
/-- **At most six openings before the climb's end lie outside the spans the climb places.** In the
climb's context: there are two spans of `δt` slots and four spans of `k + 2` slots
such that at most six honest round opening slots `i < m` with `rs i * R < r * R` have their first
slot outside all of them; the one whose round holds `r * R` is among them.

The spans: the four of `k + 2` slots start at the slots of the four clock values of
`fork_choice_change_kinds` plus one delay (`kind_span_of_bounds`); the two of `δt` slots at the slots of the entries of the waiting
openings at the heights `H₂ − 1` and `H₂`.

Why: such an opening either has a step `j` with `ForkChoiceChangeStep` at a validator outside the
adversary set at `j`, at a step from its own tick to the vote time of slot `rs i * R − k − 1` to before the
support cutoff of slot `min (rs (i + 1) * R) (r * R)`, or none. With one, the change's time is less
than `τ c + 2Δ` for one of the four clock values `τ c` (`w`'s tick to `τ c + Δ` is after it), and
`τ c + Δ` is less than `N + 2Δ` for every `N` after the change (`kind_clock_bounds`); outside the span of that kind the change is not in the opening's window
(`kind_span_of_le_cutoff`), so it is in its round, and two openings with a change of one
kind in their rounds would put the later one in that kind's span: at most four. With none and the
next slot at or before `r * R`, the opening is quiet with its base, and Lemma 89r
(`QuietCtx.round89r`) makes it rising or
waiting; with none and the next slot after `r * R`, it is the one whose round holds `r * R`. The
rising ones and that one are at most two (`quiet_rising_before_fast_round_le_two_cutoff`). A waiting
one has its proposal at height `H₂ − 1` or `H₂` (B11 and `hOld` bound it by `H₂`;
`quiet_waiting_next_proposal`), shares its entry with every waiting opening at that height
(`quiet_waiting_same_entry_cutoff`), and its first slot is less than `δt` slots after that
entry's: it lies in that height's wait span.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the
  times; `T₁`: the time of the threshold; `r`: the round of the action time the climb ends at;
  `H₂`: the threshold; `m`: the index of the last honest round opening slot; `rs`: the rounds of the honest round opening slots.

Roots name blocks until `aR M S r`: `fork_choice_change_kinds` and the climb's steps read up to the
action time of round `r`.

Read aloud: before the climb's end, two waits and four windows leave at most six honest round opening slots
outside them. -/
theorem climb_count_before (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd T₁ r H₂ m : ℕ) (rs : ℕ → ℕ)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {ΔNet_F : ℕ} (E_F : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {Δs_F : ℕ} (Sy_F : SyncedWithin A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST)
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    -- for each honest round opening slot, every validator outside the adversary set at the support cutoff of the slot
    -- after its first slot is active through the attestations' sync delay after the later of that first slot's duty
    -- window's start and `GST`
    (hHoldF : ∀ i, i < m → ∀ v, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (rs i * S.C.R + 1)) →
      v ∈ A.activeThroughout x ((max (M.dutyWindowStart S.C (rs i * S.C.R)) GST : ℕ) : ℝ)
        (((max (M.dutyWindowStart S.C (rs i * S.C.R)) GST : ℕ) : ℝ) + Δs_F))
    (hRoots : RootsNameBlocksUntil M A x (aR M S r))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT) (hT₁s : tGAT + Δs ≤ T₁)
    (hTick : ∀ (c : ℕ) (w : V) (k : ℕ), T₁ ≤ c → x.lbl k = Event.tick w (c + Δ S) → x.time k ≤ tAwakeEnd → w ∉ A.corrupted k → ∃ k' : ℕ, x.lbl k' = Event.tick w c)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hH₂ : OldHeightAttained M S A x T₁ H₂)
    (hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂)
    (hEnd : aR M S r ≤ tAwakeEnd)
    (hSeq : HonestOpeningSeq M S A x rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hT₁0 : T₁ + Δ S ≤ M.slotStart S.C (rs 0 * S.C.R - S.C.k - 1))
    (hNoCol : ¬ RootCollisionAtOpening M S A x rs m) :
    ∃ (waits : Fin 2 → ℕ) (w4 : Fin 4 → ℕ),
      ((Finset.range m).filter (fun i => rs i * S.C.R < r * S.C.R ∧
        OutsideSpans S rs waits S.C.δt w4 (S.C.k + 2) i)).card ≤ 6 := by
  have hk := S.C.k_ge_two
  have hΔ := one_le_Δ S
  have hR := S.C.R_ge_two
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hTG : tGAT ≤ T₁ := le_trans (Nat.le_add_right _ _) hT₁s
  have hTGR : (tGAT : ℝ) ≤ T₁ := by exact_mod_cast hTG
  have hT₁0R : (0 : ℝ) ≤ T₁ := Nat.cast_nonneg _
  have hmono := r_lt_of_lt_of_mono rs m hSeq.mono
  -- the uniform layout's times
  have hvt : ∀ s, M.voteTime S.C s = M.slotStart S.C s + Δ S := fun s =>
    (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s
  have hsc : ∀ s, M.supportCutoff S.C s = M.voteTime S.C s + Δ S := fun s =>
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s
  have hssc : ∀ s, M.slotStart S.C (s + 1) = M.supportCutoff S.C s + 2 * Δ S := fun s => by
    rw [hsc, hvt, (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s + 1),
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s, Nat.mul_add, Nat.mul_one]
    omega
  have hEndStep := (climb_end_step_firstAt_viewFreeze M F U) S A x R E hSkew tAwakeEnd r H₂ hOld hEnd
  obtain ⟨τ, hτ⟩ := (fork_choice_change_kinds M F U Fx) S A x R GST tGAT tAwakeEnd T₁ r H₂ E hNet hSkew hRedeliver Sy hΔs
    hRoots hParent hGST hT₁s hTick hThird hAwake hH₂ (x.firstAt (M.viewFreeze S.C (r * S.C.R))) hOld hEndStep.1 hEnd
  -- the times of an opening before the climb's end
  have h0i : ∀ i, i ≤ m → rs 0 * S.C.R ≤ rs i * S.C.R := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with h | h
    · rw [h]
    · exact Nat.mul_le_mul_right _ (le_of_lt (hmono 0 i h hi))
  have hvtLow : ∀ i, i ≤ m → T₁ + 2 * Δ S ≤ M.voteTime S.C (rs i * S.C.R - S.C.k - 1) := by
    intro i hi
    have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (show rs 0 * S.C.R - S.C.k - 1 ≤ rs i * S.C.R - S.C.k - 1 by
      have := h0i i hi
      omega)
    have h2 := hvt (rs i * S.C.R - S.C.k - 1)
    omega
  have hscHigh : ∀ i, M.supportCutoff S.C (min (rs (i + 1) * S.C.R) (r * S.C.R)) < aR M S r := by
    intro i
    have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (min_le_right (rs (i + 1) * S.C.R) (r * S.C.R))
    have h2 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_succ_eq M.toSlotLayout F.sched U) S (r * S.C.R)
    unfold aR
    omega
  have hss : ∀ i, i < m → rs i * S.C.R + S.C.R ≤ rs (i + 1) * S.C.R := by
    intro i hi
    have h' : (rs i + 1) * S.C.R ≤ rs (i + 1) * S.C.R :=
      Nat.mul_le_mul_right _ (hmono i (i + 1) (by omega) hi)
    rw [Nat.add_mul, Nat.one_mul] at h'
    exact h'
  -- the proposals
  have hP : ∀ i, i ≤ m → ∃ B : Block V, ProposalAt M S x (rs i * S.C.R) B :=
    fun i hi => (opening_proposal_exists M F U) S A x R tGAT tAwakeEnd m i rs E hAwake hSkew
      hSeq hi
  let Bf : ℕ → Block V := fun i =>
    if hi : i ≤ m then Classical.choose (hP i hi) else Block.genesis
  have hBf : ∀ i (hi : i ≤ m), ProposalAt M S x (rs i * S.C.R) (Bf i) := by
    intro i hi
    simp only [Bf, dif_pos hi]
    exact Classical.choose_spec (hP i hi)
  have hUniq : ∀ i, i ≤ m → ∀ B : Block V, ProposalAt M S x (rs i * S.C.R) B → B = Bf i :=
    fun i hi B hB => (opening_proposal_unique M F U) S A x R tGAT tAwakeEnd m i rs B (Bf i) E
      hSeq hi hNoCol hB (hBf i hi)
  -- no fork-choice change over an opening's window and round, and the waiting openings
  let NoCh : ℕ → Prop := fun i => ∀ (w : V) (j k k' c : ℕ),
    x.lbl k = Event.tick w (M.voteTime S.C (rs i * S.C.R - S.C.k - 1)) → k ≤ j →
      x.lbl k' = Event.tick w c → c ≤ M.supportCutoff S.C (rs (i + 1) * S.C.R) → j < k' → w ∉ A.corrupted j →
      ¬ ForkChoiceChangeStep M S A x w j
  -- the same, with the round read to the support cutoff of slot `min (rs (i + 1) * R) (r * R)`
  let NoChM : ℕ → Prop := fun i => ∀ (w : V) (j k k' c : ℕ),
    x.lbl k = Event.tick w (M.voteTime S.C (rs i * S.C.R - S.C.k - 1)) → k ≤ j →
      x.lbl k' = Event.tick w c → c ≤ M.supportCutoff S.C (min (rs (i + 1) * S.C.R) (r * S.C.R)) → j < k' →
      w ∉ A.corrupted j → ¬ ForkChoiceChangeStep M S A x w j
  have hNoChOfM : ∀ i, rs (i + 1) * S.C.R ≤ r * S.C.R → NoChM i → NoCh i :=
    fun i hir hNo w j k k' c h0 h1 h2 h3 h4 h5 => hNo w j k k' c h0 h1 h2 (by rw [min_eq_left hir]; exact h3) h4 h5
  let Wt : ℕ → Prop := fun i =>
    i < m ∧ rs (i + 1) * S.C.R ≤ r * S.C.R ∧ NoCh i ∧ ¬ RisingAt M S A x rs i
  have hWfacts : ∀ i, Wt i →
      (∀ B' : Block V, ProposalAt M S x (rs (i + 1) * S.C.R) B' →
        (M.chainStateOf S.C B').h ≤ (M.chainStateOf S.C (Bf i)).h) ∧
      (M.chainStateOf S.C (Bf i)).h ≤ H₂ ∧ H₂ ≤ (M.chainStateOf S.C (Bf i)).h + 1 ∧
      InSpan (M.chainStateOf S.C (Bf i)).T_h.slot S.C.δt (rs i * S.C.R) := by
    intro i hWt
    obtain ⟨him, hir, hNo, hNR⟩ := hWt
    have hBi := hBf i (le_of_lt him)
    have hWait : ∀ B' : Block V, ProposalAt M S x (rs (i + 1) * S.C.R) B' →
        (M.chainStateOf S.C B').h ≤ (M.chainStateOf S.C (Bf i)).h := by
      intro B' hB'
      by_contra hgt
      apply hNR
      intro B₀ B₀' hB₀ hB₀'
      rw [hUniq i (le_of_lt him) B₀ hB₀, hUniq (i + 1) him B₀' hB₀', ← hUniq (i + 1) him B' hB']
      unfold Height at *
      omega
    have hRootsI : RootsNameBlocksUntil M A x (((M.supportCutoff S.C (rs (i + 1) * S.C.R) : ℕ) : ℝ) + ΔClockBehind) :=
      (roots_cutoff_behind_of_aR M F U) S (show rs (i + 1) * S.C.R ≤ r * S.C.R by omega) E.ahead_nonneg hSkew hRoots
    have hTop : (M.chainStateOf S.C (Bf i)).h ≤ H₂ := by
      by_contra hgt
      obtain ⟨t₀, v, a, ht₀, hA, ha, hvR⟩ := (quiet_top_gives_attestation_cutoff_at M F U Fx) S A x R GST tGAT
        tAwakeEnd r m i H₂ (rs (i + 1) * S.C.R) rs (Bf i) E hNet hSkew hRedeliver Sy hΔs hRootsI hParent hGST hThird
        hAwake hActive hCommittees hEnd hSeq him (hss i him) hir hNoCol hNo
        hBi (by unfold Height at *; omega) (aR M S r)
        (by unfold aR; exact (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
                (by have := hss i him; omega)) hEnd
      obtain ⟨j, hl, hm⟩ := hA
      have hlt : t₀ < aR M S r := by
        have h1 := hss i him
        have h2 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (show rs i * S.C.R + 1 + 1 ≤ r * S.C.R + 1 by omega)
        have h3 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_succ_eq M.toSlotLayout F.sched U) S (rs i * S.C.R + 1)
        unfold aR at ht₀ ⊢
        omega
      have := hOld j t₀ v a hl (by exact_mod_cast hlt) hvR hm
      exact absurd this (not_le.2 ha)
    obtain ⟨_B'', -, -, -, -, hlo, -⟩ := (quiet_waiting_next_proposal M F U Fx) S A x R GST tGAT tAwakeEnd T₁
      r H₂ m i rs (Bf i) E hNet hSkew hRedeliver hRoots hParent hGST hT₁s hTick hThird
      hAwake hActive hCommittees hH₂ hOld hEnd hSeq hT₁0 him hir hNoCol hNo E_F hNet_F hSkew_F Sy hΔs Sy_F hΔs_F
      (hHoldF i him) hWait hTop hBi
    obtain ⟨hs1, C⟩ := (quietCtx_of M F U) S A x R GST tGAT tAwakeEnd r m i rs E hNet hSkew hRedeliver Sy hΔs
      hRootsI hParent hGST hThird hAwake hActive hCommittees hEnd hSeq him (hss i him) hir hNoCol hNo
    have hB0 : ProposalAt M S x (rs i * S.C.R - 1 + 1) (Bf i) := by rw [← hs1]; exact hBi
    have h89 := (C.round89r M F R E hNet hSkew hRedeliver U Fx) rfl (Bf i) (Bf (i + 1)) hB0 (hBf (i + 1) him)
      E_F hNet_F hSkew_F Sy hΔs Sy_F hΔs_F
      --: the holder row of the opening's first slot, from the per-opening row
      (fun v hv => by
        have he : rs i * S.C.R - 1 + 1 = rs i * S.C.R := by have := hs1; omega
        have hv' := (Finset.mem_sdiff.1 hv).2
        simp only [Nat.add_sub_cancel, he] at hv' ⊢
        exact hHoldF i him v hv')
    have hW1 := hWait (Bf (i + 1)) (hBf (i + 1) him)
    have hdisj : (Bf (i + 1)).slot < (M.chainStateOf S.C (Bf i)).T_h.slot + S.C.δt := by
      rcases h89.2.1 with h' | ⟨-, h', -⟩
      · exfalso
        unfold Height at *
        omega
      · exact h'
    obtain ⟨hsl1, -⟩ := (opening_proposal_held M F U) S A x R tGAT tAwakeEnd m (i + 1) rs (Bf (i + 1))
      E hSeq him hNoCol (hBf (i + 1) him)
    obtain ⟨hsl0, hheld⟩ := (opening_proposal_held M F U) S A x R tGAT tAwakeEnd m i rs (Bf i)
      E hSeq (le_of_lt him) hNoCol hBi
    have hThs : (M.chainStateOf S.C (Bf i)).T_h.slot ≤ rs i * S.C.R := by
      have hTC : GoldilocksCorrectness.Record.Statements.Routines.TreeClosed M S.P S.X
          (x.tickOutput (S.P.proposer (rs i * S.C.R)) (M.slotStart S.C (rs i * S.C.R))) :=
        F.nd.nodeInvCore_treeClosed
          ((lem11_node_invariantCore_of_run M F) S x R
            (x.tickStep (S.P.proposer (rs i * S.C.R)) (M.slotStart S.C (rs i * S.C.R)) + 1)
            (S.P.proposer (rs i * S.C.R))).1
      by_cases he : (M.chainStateOf S.C (Bf i)).T_h = Bf i
      · rw [he, hsl0]
      · have := (slot_lt_of_ancestorEq_of_treeClosed_node M F) hTC hheld
          ((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_T_h_spec M F) S.C (Bf i)).1 he
        rw [hsl0] at this
        exact le_of_lt this
    have hd2 : rs (i + 1) * S.C.R < (M.chainStateOf S.C (Bf i)).T_h.slot + S.C.δt := by
      rw [← hsl1]
      exact hdisj
    have key : ∀ a b c d e : ℕ, a + e ≤ b → b < c + d → 2 ≤ e → a < c + d := by
      intro a b c d e h1 h2 h3
      omega
    exact ⟨hWait, hTop, hlo, hThs, key _ _ _ _ _ (hss i him) hd2 hR⟩
  -- the spans
  let waits : Fin 2 → ℕ := fun c =>
    if h : ∃ i, Wt i ∧ (M.chainStateOf S.C (Bf i)).h = H₂ - 1 + c.val then
      (M.chainStateOf S.C (Bf (Classical.choose h))).T_h.slot
    else 0
  -- the span of a kind starts at the slot of its clock value plus one delay
  let w4 : Fin 4 → ℕ := fun c => ⌊(τ c + ΔClockAhead + Δ S) / (4 * Δ S)⌋₊
  refine ⟨waits, w4, ?_⟩
  set Fo := (Finset.range m).filter (fun i => rs i * S.C.R < r * S.C.R ∧
    OutsideSpans S rs waits S.C.δt w4 (S.C.k + 2) i) with hFdef
  have hmemF : ∀ i ∈ Fo, i < m ∧ rs i * S.C.R < r * S.C.R ∧
      OutsideSpans S rs waits S.C.δt w4 (S.C.k + 2) i := by
    intro i hi
    rw [hFdef, Finset.mem_filter, Finset.mem_range] at hi
    exact ⟨hi.1, hi.2⟩
  -- a waiting opening is in a wait span
  have hNoWait : ∀ i ∈ Fo, ¬ Wt i := by
    intro i hi hWt
    obtain ⟨-, -, hout⟩ := hmemF i hi
    obtain ⟨hWait, hTop, hlo, hspan⟩ := hWfacts i hWt
    have key : ∀ c : Fin 2, (M.chainStateOf S.C (Bf i)).h = H₂ - 1 + c.val → False := by
      intro c hc
      have hex : ∃ i, Wt i ∧ (M.chainStateOf S.C (Bf i)).h = H₂ - 1 + c.val := ⟨i, hWt, hc⟩
      have hwc : waits c = (M.chainStateOf S.C (Bf (Classical.choose hex))).T_h.slot := by
        simp only [waits, dif_pos hex]
      obtain ⟨hWt₀, hc₀⟩ := Classical.choose_spec hex
      set i₀ := Classical.choose hex with hi₀
      have hEq : (M.chainStateOf S.C (Bf i)).T_h = (M.chainStateOf S.C (Bf i₀)).T_h := by
        have hhe : (M.chainStateOf S.C (Bf i)).h = (M.chainStateOf S.C (Bf i₀)).h := by
          rw [hc, hc₀]
        obtain ⟨him, hir, hNo, -⟩ := hWt
        have him₀ := hWt₀.1
        have hir₀ := hWt₀.2.1
        have hNo₀ := hWt₀.2.2.1
        rcases lt_trichotomy i i₀ with hlt | heq | hgt
        · exact (quiet_waiting_same_entry_cutoff M F U Fx) S A x R GST tGAT tAwakeEnd T₁ r H₂ m i i₀ rs
            (Bf i) (Bf i₀) E hNet hSkew hRedeliver hRoots hParent hGST hT₁s hTick hThird
            hAwake hActive hCommittees hH₂ hOld hEnd hSeq hT₁0 hlt him₀ hir₀ hNoCol hNo hNo₀
            E_F hNet_F hSkew_F Sy hΔs Sy_F hΔs_F (hHoldF i him)
            hWait hTop (hBf i (le_of_lt him)) (hBf i₀ (le_of_lt him₀)) hhe
        · rw [heq]
        · obtain ⟨hWait₀, hTop₀, -, -⟩ := hWfacts i₀ hWt₀
          exact ((quiet_waiting_same_entry_cutoff M F U Fx) S A x R GST tGAT tAwakeEnd T₁ r H₂ m i₀ i
            rs (Bf i₀) (Bf i) E hNet hSkew hRedeliver hRoots hParent hGST hT₁s hTick
            hThird hAwake hActive hCommittees hH₂ hOld hEnd hSeq hT₁0 hgt him hir hNoCol hNo₀ hNo
            E_F hNet_F hSkew_F Sy hΔs Sy_F hΔs_F (hHoldF i₀ him₀)
            hWait₀ hTop₀ (hBf i₀ (le_of_lt him₀)) (hBf i (le_of_lt him)) hhe.symm).symm
      apply hout.1 c
      rw [hwc, ← hEq]
      exact hspan
    by_cases h0 : (M.chainStateOf S.C (Bf i)).h = H₂ - 1
    · exact key 0 (by rw [h0]; rfl)
    · exact key 1 (by
        show (M.chainStateOf S.C (Bf i)).h = H₂ - 1 + 1
        unfold Height at *
        omega)
  -- the openings with a fork-choice change, and the step of the change
  let Ch : ℕ → Prop := fun i => ∃ j : ℕ, ∃ w : V, ∃ k k' c : ℕ,
    x.lbl k = Event.tick w (M.voteTime S.C (rs i * S.C.R - S.C.k - 1)) ∧ k ≤ j ∧
    x.lbl k' = Event.tick w c ∧ c ≤ M.supportCutoff S.C (min (rs (i + 1) * S.C.R) (r * S.C.R)) ∧ j < k' ∧
      w ∉ A.corrupted j ∧ ForkChoiceChangeStep M S A x w j
  have hNoChOf : ∀ i, ¬ Ch i → NoChM i := by
    intro i h w j k k' c h0 h1 h2 h3 h4 h5 h6
    exact h ⟨j, w, k, k', c, h0, h1, h2, h3, h4, h5, h6⟩
  let tc : ℕ → ℕ := fun i => if h : Ch i then Classical.choose h else 0
  have htc0 : ∀ i, Ch i → ∃ w : V, ∃ k k' c : ℕ,
      x.lbl k = Event.tick w (M.voteTime S.C (rs i * S.C.R - S.C.k - 1)) ∧ k ≤ tc i ∧
      x.lbl k' = Event.tick w c ∧ c ≤ M.supportCutoff S.C (min (rs (i + 1) * S.C.R) (r * S.C.R)) ∧ tc i < k' ∧
        w ∉ A.corrupted (tc i) ∧ ForkChoiceChangeStep M S A x w (tc i) := by
    intro i h
    simp only [tc, dif_pos h]
    exact Classical.choose_spec h
  -- the change's real time is at least the vote time less `ΔClockAhead` (its validator's tick to it is no later)
  -- and at most the support cutoff plus `ΔClockBehind` (it is before its validator's tick to a clock value at most
  -- that cutoff,)
  have htc : ∀ i, Ch i → ((M.voteTime S.C (rs i * S.C.R - S.C.k - 1) : ℕ) : ℝ) - ΔClockAhead ≤ x.time (tc i) ∧
      x.time (tc i) ≤ ((M.supportCutoff S.C (min (rs (i + 1) * S.C.R) (r * S.C.R)) : ℕ) : ℝ) + ΔClockBehind ∧
        ∃ w : V, w ∉ A.corrupted (tc i) ∧ ForkChoiceChangeStep M S A x w (tc i) := by
    intro i h
    obtain ⟨w, k, k', c, hk, hkj, hk', hc, hjk, hw, hchg⟩ := htc0 i h
    have hkt := (E.tick_active k w _ hk).2.1
    have htm := (time_mono M) x R hkj
    have hk'c := (E.tick_active k' w c hk').2.2
    have htm' := (time_mono M) x R hjk.le
    have hcR : (c : ℝ) ≤ ((M.supportCutoff S.C (min (rs (i + 1) * S.C.R) (r * S.C.R)) : ℕ) : ℝ) := by
      exact_mod_cast hc
    exact ⟨by linarith, by linarith, w, hw, hchg⟩
  -- the kind of a change, with the two bounds on its clock value (`kind_clock_bounds`)
  let Pk : ℕ → Fin 4 → Prop := fun i c =>
    (T₁ : ℝ) < τ c ∧ τ c ≤ x.time (tc i) ∧ x.time (tc i) ≤ (⌈τ c + ΔClockAhead⌉₊ : ℝ) + Δ S + ΔClockBehind
  let gc : ℕ → Fin 4 := fun i => if h : ∃ c : Fin 4, Pk i c then Classical.choose h else 0
  have hgc : ∀ i ∈ Fo, Ch i → Pk i (gc i) := by
    intro i hi hch
    obtain ⟨him, -, -⟩ := hmemF i hi
    obtain ⟨h1, h2, w, hw, hchg⟩ := htc i hch
    have hlo : ((T₁ + 2 * Δ S : ℕ) : ℝ) - ΔClockAhead ≤ x.time (tc i) :=
      le_trans (by
        have : ((T₁ + 2 * Δ S : ℕ) : ℝ) ≤ ((M.voteTime S.C (rs i * S.C.R - S.C.k - 1) : ℕ) : ℝ) := by
          exact_mod_cast hvtLow i (le_of_lt him)
        linarith) h1
    push_cast at hlo
    have hhi : x.time (tc i) < aR M S r := by
      have h3 : M.supportCutoff S.C (min (rs (i + 1) * S.C.R) (r * S.C.R)) + Δ S ≤ aR M S r := by
        have h4 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
          (min_le_right (rs (i + 1) * S.C.R) (r * S.C.R))
        have h5 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_succ_eq M.toSlotLayout F.sched U) S (r * S.C.R)
        unfold aR
        omega
      have h3' : ((M.supportCutoff S.C (min (rs (i + 1) * S.C.R) (r * S.C.R)) : ℕ) : ℝ) + Δ S ≤ (aR M S r : ℝ) := by
        exact_mod_cast h3
      linarith
    have hjE : x.time (tc i) ≤ tAwakeEnd := le_trans hhi.le (by exact_mod_cast hEnd)
    -- `w`'s tick to `T₁ + Δ` is before the change
    obtain ⟨kT, hkT, hkTj⟩ := (tick_before_step_in_phase M F) S A x R E hAwake (T₁ + Δ S) (tc i) w (by omega)
      (by push_cast; linarith) (by push_cast; linarith) hjE hw
    have hts := (tickStep_eq_of_lbl M) x E hkT
    -- the change is before the view freeze of slot `r R` (re-check 61, theorem 8)
    have hk₀ : tc i + 1 ≤ x.firstAt (M.viewFreeze S.C (r * S.C.R)) := by
      refine hEndStep.2 (tc i) ?_
      have h4 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
        (min_le_right (rs (i + 1) * S.C.R) (r * S.C.R))
      have h5 : M.viewFreeze S.C (r * S.C.R) = M.supportCutoff S.C (r * S.C.R) + Δ S := by
        rw [(GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_eq M.toSlotLayout F.sched U) S (r * S.C.R), hsc, hvt]
        omega
      have h6 : ((M.supportCutoff S.C (min (rs (i + 1) * S.C.R) (r * S.C.R)) : ℕ) : ℝ) + Δ S ≤
          ((M.viewFreeze S.C (r * S.C.R) : ℕ) : ℝ) := by
        exact_mod_cast (show _ ≤ _ by omega)
      linarith
    obtain ⟨c, hA, hB, hTτ⟩ := hτ w (tc i) (by rw [hts]; exact hkT) (by rw [hts]; exact hkTj) hhi hk₀ hw hchg
    have htj := ((honest_succ_of_state_ne M F) x R E hw (state_ne_of_change_step M F hchg)).2
    have hex : ∃ c : Fin 4, Pk i c :=
      ⟨c, hTτ, hA, (kind_clock_bounds_real M F) S A x R E hAwake hTG (τ c) (tc i) w hTτ hjE hw hB⟩
    simp only [gc, dif_pos hex]
    exact Classical.choose_spec hex
  -- a kind's clock value with `τ + Δ` from the start of slot `s − k − 1` to before the start of slot
  -- `s + 1` has the opening's first slot `s` in the kind's span
  have hspanOf : ∀ i, i ≤ m → ∀ c : Fin 4, 0 ≤ τ c + ΔClockAhead →
      τ c + ΔClockAhead + Δ S < M.slotStart S.C (rs i * S.C.R + 1) →
      (M.slotStart S.C (rs i * S.C.R - S.C.k - 1) : ℝ) < τ c + ΔClockAhead + Δ S →
      InSpan (w4 c) (S.C.k + 2) (rs i * S.C.R) := by
    intro i hi c h0 h1 h2
    have h2k := ((window_after_anchor M F U) S A x rs m tGAT tAwakeEnd (rs i * S.C.R) hSeq (h0i i hi)).1
    exact (kind_span_of_bounds_real M F U) S (rs i * S.C.R) (τ c + ΔClockAhead) (by omega) h0 h1 h2
  -- the change is in the opening's round
  have hround : ∀ i ∈ Fo, Ch i → ((M.supportCutoff S.C (rs i * S.C.R) : ℕ) : ℝ) ≤ x.time (tc i) := by
    intro i hi hch
    obtain ⟨him, -, hout⟩ := hmemF i hi
    by_contra hlt
    have hlt' := not_le.mp hlt
    obtain ⟨h1, -, -⟩ := htc i hch
    obtain ⟨hT, hτt, hL⟩ := hgc i hi hch
    refine hout.2 (gc i) (hspanOf i (le_of_lt him) (gc i) (by linarith) ?_ ?_)
    · -- the change is before the opening's support cutoff and at or after the kind's start (theorem 4)
      rw [hssc]
      push_cast
      linarith
    · -- the change is at or after `w`'s tick to the vote time of slot `s − k − 1` (theorem 6)
      have hc1 : (⌈τ (gc i) + ΔClockAhead⌉₊ : ℝ) < τ (gc i) + ΔClockAhead + 1 := Nat.ceil_lt_add_one (by linarith)
      have h4 : ((M.voteTime S.C (rs i * S.C.R - S.C.k - 1) : ℕ) : ℝ) <
          ((⌈τ (gc i) + ΔClockAhead⌉₊ + 2 * Δ S : ℕ) : ℝ) := by
        push_cast
        linarith
      have h5 : M.voteTime S.C (rs i * S.C.R - S.C.k - 1) < ⌈τ (gc i) + ΔClockAhead⌉₊ + 2 * Δ S := by
        exact_mod_cast h4
      rw [hvt] at h5
      have h6 : ((M.slotStart S.C (rs i * S.C.R - S.C.k - 1) + 1 : ℕ) : ℝ) ≤
          ((⌈τ (gc i) + ΔClockAhead⌉₊ + Δ S : ℕ) : ℝ) := by
        exact_mod_cast (show M.slotStart S.C (rs i * S.C.R - S.C.k - 1) + 1 ≤ ⌈τ (gc i) + ΔClockAhead⌉₊ + Δ S by omega)
      push_cast at h6
      linarith
  have hinj : Set.InjOn gc (Fo.filter Ch) := by
    -- two openings with a change of one kind in their rounds: the later one is in the kind's span
    have hone : ∀ i ∈ Fo.filter Ch, ∀ i' ∈ Fo.filter Ch, i < i' → gc i ≠ gc i' := by
      intro i hi i' hi' hlt hgeq
      rw [Finset.mem_filter] at hi hi'
      obtain ⟨him, -, -⟩ := hmemF i hi.1
      obtain ⟨him', -, hout'⟩ := hmemF i' hi'.1
      obtain ⟨-, h2, -⟩ := htc i hi.2
      obtain ⟨hT1, hτ1, -⟩ := hgc i hi.1 hi.2
      obtain ⟨-, -, hL2⟩ := hgc i' hi'.1 hi'.2
      have hr' := hround i' hi'.1 hi'.2
      rw [← hgeq] at hL2
      have hsc' : M.supportCutoff S.C (min (rs (i + 1) * S.C.R) (r * S.C.R)) ≤
          M.supportCutoff S.C (rs i' * S.C.R) := by
        apply (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched)
        refine le_trans (min_le_left _ _) ?_
        rcases Nat.lt_or_ge (i + 1) i' with h | h
        · exact Nat.mul_le_mul_right _ (le_of_lt (hmono (i + 1) i' h (le_of_lt him')))
        · rw [show i' = i + 1 by omega]
      -- the earlier change, before the later opening's support cutoff, bounds the kind's clock value
      have hU' : τ (gc i) + ΔClockAhead + Δ S < M.slotStart S.C (rs i' * S.C.R + 1) := by
        have h3 : x.time (tc i) ≤ ((M.supportCutoff S.C (rs i' * S.C.R) : ℕ) : ℝ) + ΔClockBehind := by
          have : ((M.supportCutoff S.C (min (rs (i + 1) * S.C.R) (r * S.C.R)) : ℕ) : ℝ) ≤
              ((M.supportCutoff S.C (rs i' * S.C.R) : ℕ) : ℝ) := by exact_mod_cast hsc'
          linarith
        rw [hssc]
        push_cast
        linarith
      -- the later change, in the later opening's round, is before the kind's clock value plus two delays
      have hL' : (M.slotStart S.C (rs i' * S.C.R - S.C.k - 1) : ℝ) < τ (gc i) + ΔClockAhead + Δ S := by
        have hc1 : (⌈τ (gc i) + ΔClockAhead⌉₊ : ℝ) < τ (gc i) + ΔClockAhead + 1 :=
          Nat.ceil_lt_add_one (by linarith)
        have h4 : ((M.supportCutoff S.C (rs i' * S.C.R) : ℕ) : ℝ) <
            ((⌈τ (gc i) + ΔClockAhead⌉₊ + 2 * Δ S : ℕ) : ℝ) := by
          push_cast
          linarith
        have h5 : M.supportCutoff S.C (rs i' * S.C.R) < ⌈τ (gc i) + ΔClockAhead⌉₊ + 2 * Δ S := by exact_mod_cast h4
        have h6 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
          (show rs i' * S.C.R - S.C.k - 1 ≤ rs i' * S.C.R by omega)
        rw [hsc, hvt] at h5
        have h7 : ((M.slotStart S.C (rs i' * S.C.R - S.C.k - 1) + 1 : ℕ) : ℝ) ≤
            ((⌈τ (gc i) + ΔClockAhead⌉₊ : ℕ) : ℝ) := by
          exact_mod_cast (show M.slotStart S.C (rs i' * S.C.R - S.C.k - 1) + 1 ≤ ⌈τ (gc i) + ΔClockAhead⌉₊ by omega)
        push_cast at h7
        linarith
      exact hout'.2 (gc i) (hspanOf i' (le_of_lt him') (gc i) (by linarith) hU' hL')
    intro i hi i' hi' hgg
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact hone i hi i' hi' hlt hgg
    · exact hone i' hi' i hi hlt hgg.symm
  have hcardCh : (Fo.filter Ch).card ≤ 4 := by
    have := Finset.card_le_card_of_injOn gc (fun i _ => Finset.mem_univ (gc i)) hinj
    simpa using this
  -- the openings with no change rise
  have hsubRise : Fo.filter (fun i => ¬ Ch i) ⊆ (Finset.range m).filter (fun i =>
      rs i * S.C.R < r * S.C.R ∧
      (∀ (w : V) (j k k' c : ℕ), x.lbl k = Event.tick w (M.voteTime S.C (rs i * S.C.R - S.C.k - 1)) → k ≤ j →
        x.lbl k' = Event.tick w c → c ≤ M.supportCutoff S.C (min (rs (i + 1) * S.C.R) (r * S.C.R)) → j < k' →
        w ∉ A.corrupted j → ¬ ForkChoiceChangeStep M S A x w j) ∧
      (rs (i + 1) * S.C.R ≤ r * S.C.R → RisingAt M S A x rs i)) := by
    intro i hi
    rw [Finset.mem_filter] at hi
    obtain ⟨him, hlt, -⟩ := hmemF i hi.1
    have hNo := hNoChOf i hi.2
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨him, hlt, hNo, fun hir => ?_⟩
    by_contra hNR
    exact hNoWait i hi.1 ⟨him, hir, hNoChOfM i hir hNo, hNR⟩
  have hcardRise := le_trans (Finset.card_le_card hsubRise)
    ((quiet_rising_before_fast_round_le_two_cutoff M F U Fx) S A x R GST tGAT tAwakeEnd T₁ r H₂ m rs
      E hNet hSkew hRedeliver Sy hΔs hRoots hParent hGST hT₁s hTick hThird hAwake hActive hCommittees
      hH₂ hOld hEnd hSeq hT₁0 hNoCol)
  have hsplit := Finset.card_filter_add_card_filter_not (s := Fo) Ch
  omega

/-! ## The climb -/

omit [RootOrder] in
/-- **Five window spans as four and one.** An honest round opening slot outside two families of
spans whose second is the four spans `w` followed by the spans `a` (`Fin.append w a`) is outside
the spans `w` and outside every span `a j`.

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `rs`: the rounds; `waits`, `Lw`: the first family; `w`, `a`: the two parts of
  the second family, of length `L`; `i`: the honest round opening slot.

Read aloud: an honest round opening slot outside the spans `w` followed by the spans `a` is outside
the spans `w` and outside every span `a j`. -/
theorem outsideSpans_append_parts (S : Setup V) (rs : ℕ → ℕ) {nW n₁ n₂ : ℕ}
    (waits : Fin nW → ℕ) (Lw : ℕ) (w : Fin n₁ → ℕ) (a : Fin n₂ → ℕ) (L i : ℕ)
    (h : OutsideSpans S rs waits Lw (Fin.append w a) L i) :
    OutsideSpans S rs waits Lw w L i ∧ ∀ j : Fin n₂, ¬ InSpan (a j) L (rs i * S.C.R) := by
  refine ⟨⟨h.1, fun j => ?_⟩, fun j => ?_⟩
  · have := h.2 (Fin.castAdd n₂ j)
    rwa [Fin.append_left] at this
  · have := h.2 (Fin.natAdd n₁ j)
    rwa [Fin.append_right] at this

/-- **A tick one delay before every tick in the phase.** In a phase where every validator honest at a
step is awake there (`hAwake`), and `T₁` is at least one delay after the phase's start: a validator
that ticks to `c + Δ S`, for a clock value `c ≥ T₁`, at a step `k` in the phase and is outside the
adversary set there also ticked to `c`.

Why: every step whose real time is at most `c + ΔClockBehind` is before `k` (`k` is at a real time at
least `c + Δ S − ΔClockAhead`, later by `hSkew`), so the validator is outside the adversary set there
(corruption is monotone) and, the step being at a real time at least `c − ΔClockAhead`, after `tGAT`,
awake there (`hAwake`); `tick_of_active` then gives its tick to `c`. This is the bundle premise `hTick`
of `ClimbCtx`, derived from the phase's facts.

The variables:
- `M`: the model; `F`: its facts;
- `tGAT`, `tAwakeEnd`: the ends of the phase; `T₁`: the first clock value read.

Read aloud: in the phase, a validator honest at its tick to `c + Δ S` ticked to `c` before. -/
theorem tick_before_of_tick_in_phase (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)
    (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) {tGAT tAwakeEnd T₁ : ℕ}
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hT₁ : tGAT + Δ S ≤ T₁) :
    ∀ (c : ℕ) (w : V) (k : ℕ), T₁ ≤ c → x.lbl k = Event.tick w (c + Δ S) → x.time k ≤ tAwakeEnd →
      w ∉ A.corrupted k → ∃ k' : ℕ, x.lbl k' = Event.tick w c := by
  intro c w k hc hk hkE hwk
  have hΔ := one_le_Δ S
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hkt := (E.tick_active _ _ _ hk).2.1
  push_cast at hkt
  have hcT : ((tGAT : ℕ) : ℝ) + Δ S ≤ c := by exact_mod_cast le_trans hT₁ hc
  obtain ⟨i, hi, -⟩ := E.tick_of_active c (by omega) w (fun i h1 h2 => by
    have hik : i < k := (lt_of_time_lt M) x R (by linarith)
    have hwi : w ∉ A.corrupted i := E.not_mem_corrupted_of_le hik.le hwk
    have hti := (time_mono M) x R hik.le
    have hti1 := (time_mono M) x R (Nat.le_succ i)
    exact Activity.mem_active.2 ⟨hAwake i w (by linarith) (by linarith) hwi, hwi⟩)
  exact ⟨i, hi⟩

/-- **Part B's assembly, the climb to the first honest fast block, with the premise of three span
lengths and the count 9.** The proof; the audited statement is in
`Statements/Executions/Lemma89Statements.lean`.

The route: split on the collision disjunct, so that `hNoCol` holds. Take
`T₁ := M.slotStart S.C (rs 0 * R − 2k) + 3Δ` and `H₂` the greatest height of an honest attestation
before `T₁` (B1). An honest attestation above `H₂` is sent at a time from `T₁` to before
`aR M S (rs (m − 1))`: otherwise every honest attestation before that time is at most `H₂`, and
`climb_count_before` at the round `rs (m − 1)` leaves at most six outside openings before it, with
only the last opening after its span: seven, against the premise's nine. B3 gives the first round
`r` with such an attestation at `aR M S r`, every earlier one at most `H₂`; B4 its fast block `L` of
height `H₂ + 1`; and `T₁ ≤ aR M S r` puts slot `r * R + 1` at or after the committee premise's
anchor. At `r`, the count leaves at most six outside openings `i < m` with `rs i * R < r * R`
, and the last one: at least three
outside honest round opening slots have their first slot at or after `r * R` (`after_of_before`),
hence at least `k + 2` slots after it (the span of `k + 2` slots at `r * R`); the first honest
round opening slot `j` at least `k + 2` slots after `r * R` is at or before the first of them, so
`j + 2 ≤ m`. The landed conclusion names the answer of `v`'s update at `aR S r`; the twin names a
node state `n'` that update can leave (`ConfirmationUpdated`), as `fast_block_at_first_round`'s twin
does.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the times;
  `m`: the index of the last honest round opening slot; `rs`: the rounds of the honest round opening slots.

Roots name blocks until `aR M S (rs (m - 1))`: the count at the round `rs (m − 1)`
(`climb_count_before`), and at the first round `r` above the threshold, whose action time is before
`aR M S (rs (m - 1))`.

Read aloud: nine honest round opening slots outside two timeout waits and five spans of `k + 2`
slots give the first honest fast block one height above the threshold and three honest round opening
slots at least `k + 2` slots after its round. -/
theorem climb_to_fast_block (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd m : ℕ) (rs : ℕ → ℕ)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {ΔNet_F : ℕ} (E_F : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {Δs_F : ℕ} (Sy_F : SyncedWithin A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST)
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    -- for each honest round opening slot, every validator outside the adversary set at the support cutoff of the slot
    -- after its first slot is active through the attestations' sync delay after the later of that first slot's duty
    -- window's start and `GST`
    (hHoldF : ∀ i, i < m → ∀ v, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (rs i * S.C.R + 1)) →
      v ∈ A.activeThroughout x ((max (M.dutyWindowStart S.C (rs i * S.C.R)) GST : ℕ) : ℝ)
        (((max (M.dutyWindowStart S.C (rs i * S.C.R)) GST : ℕ) : ℝ) + Δs_F))
    (hRoots : RootsNameBlocksUntil M A x (aR M S (rs (m - 1))))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hSeq : HonestOpeningSeq M S A x rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hm : OpeningsOutsideWaitsAndWindows S rs m) :
    RootCollisionAtOpening M S A x rs m ∨
    ∃ (r H₂ : ℕ) (v : V) (L : Block V) (n' : M.N),
      anchorCW S tGAT ≤ M.slotStart S.C (r * S.C.R + 1) ∧ aR M S r ≤ tAwakeEnd ∧
      OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂ ∧
      v ∉ A.corruptedAtTime x (aR M S r) ∧
      ConfirmationUpdated M S.C S.P (x.tickInput v (aR M S r)) ((aR M S r : ℕ) : Int)
        (r * S.C.R + 1) n' ∧
      L ∈ M.fastBlocks n' ∧ (M.chainStateOf S.C L).h = H₂ + 1 ∧
      x.time (x.tickStep v (aR M S r)) ≤ tAwakeEnd ∧
      x.lbl (x.tickStep v (aR M S r)) = Event.tick v (aR M S r) ∧
      (∀ (k t : ℕ) (u : V) (a' : Attestation V), k < x.tickStep v (aR M S r) → x.lbl k = Event.tick u t →
        u ∉ A.corruptedAtTime x tAwakeEnd →
        (⟨u, NamedObject.attest a'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (k + 1) - x.sent k → a'.h ≤ H₂) ∧
      ∃ j : ℕ, j + 2 ≤ m ∧ r * S.C.R + S.C.k + 2 ≤ rs j * S.C.R ∧
        ∀ i : ℕ, i < j → rs i * S.C.R < r * S.C.R + S.C.k + 2 := by
  classical
  by_cases hcol : RootCollisionAtOpening M S A x rs m
  · exact Or.inl hcol
  right
  have hk := S.C.k_ge_two
  have hΔ := one_le_Δ S
  have hR := S.C.R_ge_two
  have hmono := r_lt_of_lt_of_mono rs m hSeq.mono
  have hmle : ∀ a b : ℕ, a ≤ b → b ≤ m → rs a * S.C.R ≤ rs b * S.C.R := by
    intro a b hab hbm
    rcases Nat.lt_or_ge a b with h | h
    · exact Nat.mul_le_mul_right _ (le_of_lt (hmono a b h hbm))
    · rw [show a = b by omega]
  obtain ⟨h2k0, hA0⟩ := (window_after_anchor M F U) S A x rs m tGAT tAwakeEnd (rs 0 * S.C.R) hSeq le_rfl
  have hss0 : M.slotStart S.C (rs 0 * S.C.R - 2 * S.C.k + 1) =
      M.slotStart S.C (rs 0 * S.C.R - 2 * S.C.k) + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add, Nat.mul_one]
  -- the threshold, three delays into slot `rs 0 * R − 2k`
  set T₁ := M.slotStart S.C (rs 0 * S.C.R - 2 * S.C.k) + 3 * Δ S with hT₁def
  have hT₁0 : T₁ + Δ S ≤ M.slotStart S.C (rs 0 * S.C.R - S.C.k - 1) :=
    le_trans (show T₁ + Δ S ≤ M.slotStart S.C (rs 0 * S.C.R - 2 * S.C.k + 1) by omega)
      ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (by omega))
  have hT₁ : tGAT ≤ T₁ := by
    have h1 : 4 * Δ S ≤ 4 * Δ S * (S.C.k + 2) := Nat.le_mul_of_pos_right _ (by omega)
    rw [anchorCW_eq] at hA0
    omega
  -- item 4: the recovery delay less one delay after `tGAT` has elapsed by `T₁`
  have hΔs' : Δs + 3 * Δ S < 4 * Δ S * S.C.k := by
    have hm : ((Δs : ℕ) : ℝ) ≤ max ((Δ S : ℕ) : ℝ) ((Δs : ℕ) : ℝ) := le_max_right _ _
    have hA0' := E.ahead_nonneg
    have hB0' := E.behind_nonneg
    exact_mod_cast (show ((Δs + 3 * Δ S : ℕ) : ℝ) < ((4 * Δ S * S.C.k : ℕ) : ℝ) by push_cast; linarith)
  have hT₁s : tGAT + Δs ≤ T₁ := by
    have h2 : 4 * Δ S * (S.C.k + 2) = 4 * Δ S * S.C.k + 4 * Δ S * 2 := Nat.mul_add _ _ _
    rw [anchorCW_eq] at hA0
    omega
  have hT₁Δ : tGAT + Δ S ≤ T₁ := by
    have h2 : 4 * Δ S * (S.C.k + 2) = 4 * Δ S * S.C.k + 4 * Δ S * 2 := Nat.mul_add _ _ _
    rw [anchorCW_eq] at hA0
    omega
  -- a validator ticking to `c + Δ` in the phase ticked to `c` (the climb count's `hTick`)
  have hTick := (tick_before_of_tick_in_phase M F) S A x R E hSkew hAwake hT₁Δ
  obtain ⟨H₂, hH₂⟩ := (exists_old_height_attained M F) S A x R T₁ E
  have hcount : ∀ (waits : Fin 2 → ℕ) (w5 : Fin 5 → ℕ),
      9 ≤ ((Finset.range (m + 1)).filter
        (OutsideSpans S rs waits S.C.δt w5 (S.C.k + 2))).card := hm
  have hm1 : 1 ≤ m := by
    have h := hcount (fun _ => 0) (fun _ => 0)
    have := Finset.card_filter_le (Finset.range (m + 1))
      (OutsideSpans S rs (fun _ : Fin 2 => 0) S.C.δt (fun _ : Fin 5 => 0) (S.C.k + 2))
    rw [Finset.card_range] at this
    omega
  -- an honest attestation above `H₂` before the action time of opening `m − 1`'s round
  have hrm1 : rs (m - 1) * S.C.R + S.C.R ≤ rs m * S.C.R := by
    have h' : (rs (m - 1) + 1) * S.C.R ≤ rs m * S.C.R :=
      Nat.mul_le_mul_right _ (hmono (m - 1) m (by omega) le_rfl)
    rw [Nat.add_mul, Nat.one_mul] at h'
    exact h'
  have hEnd1 : aR M S (rs (m - 1)) ≤ tAwakeEnd := by
    unfold aR
    exact le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)) hSeq.last
  -- `T₁` is before the action time of opening `m − 1`'s round
  have hT₁aR : T₁ ≤ aR M S (rs (m - 1)) := by
    have h0m := hmle 0 (m - 1) (by omega) (by omega)
    have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
      (show rs 0 * S.C.R - 2 * S.C.k + 1 ≤ rs (m - 1) * S.C.R + 1 by omega)
    have h2 : aR M S (rs (m - 1)) = M.slotStart S.C (rs (m - 1) * S.C.R + 1) + 2 * Δ S := by
      unfold aR
      rw [(GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U),
        (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U)]
      omega
    omega
  have hex : ∃ (t₀ : ℕ) (v₀ : V) (a₀ : Attestation V), T₁ ≤ t₀ ∧ t₀ < aR M S (rs (m - 1)) ∧
      HonestAttestationAt M S A x t₀ v₀ a₀ ∧ v₀ ∉ A.corruptedAtTime x t₀ ∧ H₂ < a₀.h := by
    by_contra hno
    have hOld1 : OldAttestationsAtMostHonestAt M S A x (aR M S (rs (m - 1))) (aR M S (rs (m - 1))) H₂ := by
      intro i t v a hl ht hHonR hmem
      by_cases hlt : t < T₁
      · -- a tick before `T₁`: the sender, honest at the action time `≥ T₁`, is honest at `T₁`
        exact hH₂.1 i t v a hl (by exact_mod_cast hlt) ((not_mem_corruptedAtTime_of_le M) x R E (by exact_mod_cast hT₁aR) hHonR) hmem
      · -- a tick from `T₁` on
        by_contra hgt
        exact hno ⟨t, v, a, Nat.le_of_not_lt hlt, by exact_mod_cast ht, ⟨i, hl, hmem⟩,
          (not_mem_corruptedAtTime_of_le M) x R E (by exact_mod_cast ht.le) hHonR, Nat.lt_of_not_le hgt⟩
    obtain ⟨waits, w4, hcnt⟩ := (climb_count_before M F U Fx) S A x R GST tGAT tAwakeEnd T₁ (rs (m - 1))
      H₂ m rs E hNet hSkew hRedeliver E_F hNet_F hSkew_F Sy hΔs Sy_F hΔs_F hHoldF hRoots hParent hGST hT₁s hTick
      hThird hAwake hActive hCommittees hH₂ hOld1 hEnd1 hSeq hT₁0 hcol
    have h9 := hcount waits (Fin.append w4 (fun _ : Fin 1 => rs (m - 1) * S.C.R))
    have hsub : (Finset.range (m + 1)).filter
        (OutsideSpans S rs waits S.C.δt (Fin.append w4 (fun _ : Fin 1 => rs (m - 1) * S.C.R))
          (S.C.k + 2)) ⊆
        (Finset.range m).filter (fun i => rs i * S.C.R < rs (m - 1) * S.C.R ∧
          OutsideSpans S rs waits S.C.δt w4 (S.C.k + 2) i) ∪ {m} := by
      intro i hi
      rw [Finset.mem_filter, Finset.mem_range] at hi
      obtain ⟨hout, hnot⟩ := (outsideSpans_append_parts M F) S rs waits S.C.δt w4 _ (S.C.k + 2) i hi.2
      by_cases him : i = m
      · exact Finset.mem_union_right _ (Finset.mem_singleton.2 him)
      · apply Finset.mem_union_left
        rw [Finset.mem_filter, Finset.mem_range]
        have him' : i < m := by omega
        by_cases hi1 : i = m - 1
        · exfalso
          apply hnot 0
          rw [hi1]
          show rs (m - 1) * S.C.R ≤ rs (m - 1) * S.C.R ∧
            rs (m - 1) * S.C.R < rs (m - 1) * S.C.R + (S.C.k + 2)
          omega
        · have h1 := hmle (i + 1) (m - 1) (by omega) (by omega)
          have h2 := (opening_round_step M F) hSeq him'
          exact ⟨him', by omega, hout⟩
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le ((Finset.range m).filter (fun i =>
      rs i * S.C.R < rs (m - 1) * S.C.R ∧ OutsideSpans S rs waits S.C.δt w4 (S.C.k + 2) i))
      ({m} : Finset ℕ)
    rw [Finset.card_singleton] at h2
    omega
  -- the first round above the threshold, and its fast block
  obtain ⟨t₀, v₀, a₀, ht₀, ht₀', hA₀, hv₀, ha₀⟩ := hex
  obtain ⟨r, hTr, hrt, hOld, v, a, hA, hv, ha, k₀, hk₀, hs₀, hOldk⟩ := (first_attestation_above_bound M F U) S A x R E hSkew T₁ H₂ t₀ tAwakeEnd v₀
    a₀ hH₂ ht₀ (by omega) ⟨hA₀, hv₀⟩ ha₀
  have hEnd : aR M S r ≤ tAwakeEnd := by omega
  -- `v`'s tick to the action time of round `r` is at most `tAwakeEnd`: that action time is at least one slot before
  -- the action time of opening `m − 1`'s round
  have haRlt : aR M S r < aR M S (rs (m - 1)) := by omega
  have haRΔ : aR M S r + Δ S ≤ tAwakeEnd := by
    rcases Nat.lt_or_ge (r * S.C.R + 1) (rs (m - 1) * S.C.R + 1) with h | h
    · have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (show r * S.C.R + 1 + 1 ≤ rs (m - 1) * S.C.R + 1 by omega)
      obtain ⟨-, hc1, -, hs1, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (r * S.C.R + 1)
      have hc2 := ((GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (r * S.C.R + 1 + 1)).2.1
      unfold aR at haRlt hEnd1 ⊢
      omega
    · have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S h
      unfold aR at haRlt h1
      omega
  have hk₀E : x.time k₀ ≤ (tAwakeEnd : ℝ) :=
    (tick_time_le_of_clock_le M F) x E (c₀ := aR M S r)
      (by have : ((aR M S r : ℕ) : ℝ) + Δ S ≤ ((tAwakeEnd : ℕ) : ℝ) := by exact_mod_cast haRΔ
          linarith [hSkew, E.ahead_nonneg]) k₀ v _ hk₀ le_rfl
  have htk : x.tickStep v (aR M S r) = k₀ := (tickStep_eq_of_lbl M) x E hk₀
  obtain ⟨A', L, hUpd, hFast, -, hL⟩ := (fast_block_at_first_round M F U Fx) S A x R E tAwakeEnd r H₂ k₀ v a
    hThird hk₀ hs₀ hOldk hk₀E ha
  have hAnchor : anchorCW S tGAT ≤ M.slotStart S.C (r * S.C.R + 1) := by
    have h1 : aR M S r = M.slotStart S.C (r * S.C.R + 1) + 2 * Δ S := by
      unfold aR
      have := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (r * S.C.R + 1)
      have := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (r * S.C.R + 1)
      omega
    have h2 : rs 0 * S.C.R - 2 * S.C.k + 1 ≤ r * S.C.R + 1 := by
      by_contra hlt
      have := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (show r * S.C.R + 1 ≤ rs 0 * S.C.R - 2 * S.C.k by omega)
      omega
    exact le_trans hA0 ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S h2)
  -- the count at `r`: three outside honest round opening slots at or after `r * R`
  obtain ⟨waits, w4, hcnt⟩ := (climb_count_before M F U Fx) S A x R GST tGAT tAwakeEnd T₁ r H₂ m rs E hNet hSkew hRedeliver
     E_F hNet_F hSkew_F Sy hΔs Sy_F hΔs_F hHoldF ((GoldilocksCorrectness.Record.Statements.Executions.RootsNameBlocksUntil.mono M) (by omega) hRoots) hParent hGST hT₁s hTick
    hThird hAwake hActive
    hCommittees hH₂ hOld hEnd hSeq hT₁0 hcol
  let a₃ : Fin 1 → ℕ := fun _ => r * S.C.R
  have h6 : ((Finset.range m).filter (fun i => rs i * S.C.R < r * S.C.R ∧
      OutsideSpans S rs waits S.C.δt (Fin.append w4 a₃) (S.C.k + 2) i)).card ≤ 6 := by
    refine le_trans (Finset.card_le_card ?_) hcnt
    intro i hi
    rw [Finset.mem_filter] at hi ⊢
    exact ⟨hi.1, hi.2.1,
      ((outsideSpans_append_parts M F) S rs waits S.C.δt w4 a₃ (S.C.k + 2) i hi.2.2).1⟩
  have h3 := after_of_before S rs m (r * S.C.R) 9
    (OutsideSpans S rs waits S.C.δt (Fin.append w4 a₃) (S.C.k + 2))
    (by omega) (fun i hi => hmle i m hi le_rfl) h6 (hcount waits (Fin.append w4 a₃))
  set Bs := (Finset.range (m + 1)).filter (fun i => r * S.C.R ≤ rs i * S.C.R ∧
    OutsideSpans S rs waits S.C.δt (Fin.append w4 a₃) (S.C.k + 2) i) with hBsdef
  have hBs : ∀ i ∈ Bs, i ≤ m ∧ r * S.C.R + S.C.k + 2 ≤ rs i * S.C.R := by
    intro i hi
    rw [hBsdef, Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨him, hge, hO⟩ := hi
    have hnot := ((outsideSpans_append_parts M F) S rs waits S.C.δt w4 a₃ (S.C.k + 2) i hO).2
    have hn := hnot 0
    refine ⟨by omega, ?_⟩
    unfold InSpan at hn
    simp only [a₃] at hn
    omega
  have hexj : ∃ j : ℕ, r * S.C.R + S.C.k + 2 ≤ rs j * S.C.R := by
    obtain ⟨i, hi⟩ := Finset.card_pos.1 (by omega : 0 < Bs.card)
    exact ⟨i, (hBs i hi).2⟩
  refine ⟨r, H₂, v, L, A', hAnchor, hEnd, hOld, hv, hUpd, hFast, hL, by rw [htk]; exact hk₀E, by rw [htk]; exact hk₀,
    by rw [htk]; exact hOldk, Nat.find hexj, ?_,
    Nat.find_spec hexj, fun i hi => ?_⟩
  · have hj : ∀ i ∈ Bs, Nat.find hexj ≤ i ∧ i ≤ m := fun i hi =>
      ⟨Nat.find_min' hexj (hBs i hi).2, (hBs i hi).1⟩
    have hmaps : ∀ i ∈ Bs, (fun i => i - Nat.find hexj) i ∈ Finset.range (m + 1 - Nat.find hexj) := by
      intro i hi
      have := hj i hi
      rw [Finset.mem_range]
      show i - Nat.find hexj < m + 1 - Nat.find hexj
      omega
    have hinj : Set.InjOn (fun i => i - Nat.find hexj) Bs := by
      intro i hi i' hi' he
      have h1 := hj i hi
      have h2 := hj i' hi'
      simp only at he
      omega
    have := Finset.card_le_card_of_injOn (fun i => i - Nat.find hexj) hmaps hinj
    rw [Finset.card_range] at this
    omega
  · have := Nat.find_min hexj hi
    omega

end GoldilocksCorrectness.Record.Proofs.Executions

