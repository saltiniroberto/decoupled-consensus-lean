module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89f
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.HealedFrame
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.PhaseKit
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma84
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma85
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma24
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.BlockPropagation
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Provenance
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.RoundKit
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.HealedCachesDefs
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.HonestChainAfterHealingStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.HonestAccountableStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.UnforgeabilityStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.HeightAttestationStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.CertificateStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.FGStateReaders
public import GoldilocksCorrectness.Proofs.Executions.HealedFrame
public import GoldilocksCorrectness.Proofs.Executions.PhaseKit
public import GoldilocksCorrectness.Proofs.Executions.Lemma84
public import GoldilocksCorrectness.Proofs.Executions.Lemma85
public import GoldilocksCorrectness.Proofs.Executions.Lemma24
public import GoldilocksCorrectness.Proofs.Executions.BlockPropagation
public import GoldilocksCorrectness.Proofs.Executions.Provenance
public import GoldilocksCorrectness.Proofs.Executions.RoundKit
public import GoldilocksCorrectness.Statements.Executions.HealedCachesDefs
public import GoldilocksCorrectness.Statements.Executions.HonestChainAfterHealingStatements
public import GoldilocksCorrectness.Statements.Executions.HonestAccountableStatements
public import GoldilocksCorrectness.Statements.Executions.UnforgeabilityStatements
public import GoldilocksCorrectness.Statements.Executions.HeightAttestationStatements
public import GoldilocksCorrectness.Statements.Routines.CertificateStatements
public import GoldilocksCorrectness.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Proofs.Routines.FGStateReaders
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma91, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma91.lean`, over a model `M` whose facts
`F` hold, for an execution `x` of `protocolOf M S`: the certificate route, the entries of the honest
chain and of the honest chain before a slot, and Lemma 91 (b) to (f), the frame facts after healing,
read with the greatest chain-state height `hMax M S.C n` of the node's tree in place of the cache
`h_max`. The page's routine-level theorems are the facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff)
open GoldilocksCorrectness.Proofs.Routines (lt_supportCutoff_succ one_le_Δ slotStart_eq
  slot_after_healed_round slot_eq_of_mem slot_le_of_supportCutoff_lt voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (compatible_of_ancestorEq_both)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery EnvFactsDeliveryUpTo SyncedWithin SyncedWithinUpTo)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (IsEntry hMax)

open GoldilocksCorrectness.Record.Statements.Routines (JustificationCertOn ProgressCertOn)

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
  ancestorEq_antisymm ancestorEq_of_parent?)

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

/-! ## The certificate route -/

/-- **Kit fact, the certificate route.** Under unforgeability, take a block `Y` that `w` holds
after `j` steps and a progress certificate on the chain of `Y` at a height `h` greater than `H`
naming `T`'s root; when fewer than a quorum of validators have been in the adversary set up to the
later of the time after `j` steps and the support cutoff of slot `s₀ + 1`, and every honest
attestation sent before that cutoff has height at most `H`: some honest attester `uₐ` ran the update
of a slot `sₐ` at least `s₀` at its own tick to `M.supportCutoff S.C (sₐ + 1)`, a step before `j`; it
is an updater of slot `sₐ`, outside the adversary set after every step whose time is at most the time
after `j` steps; and the entry block `E` of the height `h` that it held in the state its tick started
from is on the honest chain at slot `sₐ`, with `T`'s root.

Why: some member `u` of the quorum is honest up to the later time; `u`'s vote is in `u`'s record
(Lemma 74), so `u`'s tick put an attestation with that content on the wire at some earlier step; that
tick ran the update of a slot `sₐ` and the attestation names the entry of its source's chain, held at
the tick (`attest_tick_update_source`); its height is greater than `H`, so the tick is not before the
support cutoff of slot `s₀ + 1` (`hOld`), and `sₐ ≥ s₀`; `u`'s own saved confirmation puts the entry
on the honest chain at `sₐ`. Neither `HonestAttestationsOnChain` nor a time bound on the tick is read.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `H`: the
  bound on the old attestations' heights; `j`: the step; `w`: the holder; `Y`: the held block;
  `T`: the block the certificate names; `h`: its height.

Read aloud: a certificate above the threshold on a held chain names, by root, an entry of the
honest chain at a slot whose update an honest attester ran at a tick before `j`, holding the entry
when it ticked. -/
theorem cert_entry_at_slot (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ H j : ℕ) (w : V) (Y T : Block V) (h : Height)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V)
      (max (x.time j) (M.supportCutoff S.C (s₀ + 1))))
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hY : Y ∈ (x.st j w).tree) (hJ : ProgressCertOn M Y h T) (hH : H < h) :
    ∃ (s_a : ℕ) (uₐ : V) (E : Block V), x.tickStep uₐ (M.supportCutoff S.C (s_a + 1)) < j ∧
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
  exact ⟨sₐ, u, (M.chainStateOf S.C source).T_h, by rw [hts]; exact hj', by rw [hts]; exact hl, hv,
    Activity.not_mem_corruptedAtTime.2 fun k hk => hhonM k (le_trans hk (le_max_left _ _)), hTI,
    ⟨hs₀, u, hv, C, hSaved, ancestorEq_trans hE3 hsrcC⟩, hE1, hE2.trans (hh.trans hh'),
    hT'.symm.trans hT⟩

/-- Two entry blocks of the honest chain at one chain-state height are one block.

Why: they are compatible (`onHonestChain_compatible`); of two blocks of one chain at one height,
the `T_h` is one (Lemma 47 (e)), and each is its own `T_h`.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the first slot of the chain;
  `E`, `E'`: the two entries.

Read aloud: the honest chain has at most one entry at each chain-state height. -/
theorem entry_eq_of_onHonestChain (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (Env : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (s₀ : ℕ) (E E' : Block V)
    (hChain : ConfirmationsChain M S A x s₀)
    (hE : OnHonestChain M S A x s₀ E) (hE' : OnHonestChain M S A x s₀ E')
    (hEe : IsEntry M S.C E) (hEe' : IsEntry M S.C E')
    (hh : (M.chainStateOf S.C E).h = (M.chainStateOf S.C E').h) : E = E' := by
  rcases (compatible_iff _ _).1 ((onHonestChain_compatible M F) S A x s₀ E E' hChain hE hE') with
    h1 | h1
  · have := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C E E').2.2.2.2 h1 hh
    unfold IsEntry at hEe hEe'
    rw [hEe, hEe'] at this
    exact this
  · have := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C E' E).2.2.2.2 h1 hh.symm
    unfold IsEntry at hEe hEe'
    rw [hEe, hEe'] at this
    exact this.symm

/-- An ancestor of a block of the chain before `s'` is on the chain before `s'`.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the first slot of the chain;
  `s'`: the bound on the slot; `D`, `D'`: the ancestor and the block.

Read aloud: the honest chain before slot `s'` is closed under ancestors. -/
theorem onHonestChainBefore_of_ancestorEq (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (s₀ s' : ℕ) {D D' : Block V}
    (hD : OnHonestChainBefore M S A x s₀ s' D') (h : D.AncestorEq D') :
    OnHonestChainBefore M S A x s₀ s' D := by
  obtain ⟨s, hs, hs₀, u, hu, C, hC, hDC⟩ := hD
  exact ⟨s, hs, hs₀, u, hu, C, hC, ancestorEq_trans h hDC⟩

/-- Two blocks on the honest chain before slot `s'` are compatible, when the updaters'
confirmations of the slots from `s₀` to before `s'` form one chain.

Why: each is an ancestor of, or equal to, an updater's confirmation of a slot less than `s'`; the
two confirmations are ordered or, at one slot, compatible.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the first slot of the chain;
  `s'`: the bound on the slot; `B`, `B'`: the blocks.

Read aloud: any two blocks of the honest chain before slot `s'` are compatible, when the updaters'
confirmations of the slots before `s'` form one chain. -/
theorem onHonestChainBefore_compatible (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (s₀ s' : ℕ) (B B' : Block V)
    (hChain : ConfirmationsChainBefore M S A x s₀ s')
    (hB : OnHonestChainBefore M S A x s₀ s' B)
      (hB' : OnHonestChainBefore M S A x s₀ s' B') :
    B.compatible B' = true := by
  obtain ⟨s, hss', hs, v, hv, C, hC, hBC⟩ := hB
  obtain ⟨s'', hs''s', hs'', v', hv', C', hC', hBC'⟩ := hB'
  have hcc : C.compatible C' = true := by
    rcases Nat.lt_trichotomy s s'' with hlt | heq | hgt
    · exact (compatible_iff _ _).2
        (Or.inl ((hChain s s'' v v' C C' hs hlt.le hs''s' hv hv' hC hC').1 hlt))
    · exact (hChain s s'' v v' C C' hs heq.le hs''s' hv hv' hC hC').2 heq
    · exact (compatible_iff _ _).2
        (Or.inr ((hChain s'' s v' v C' C hs'' hgt.le hss' hv' hv hC' hC).1 hgt))
  exact compatible_of_ancestorEq_both hBC hBC' hcc

/-- Two entry blocks of the honest chain before slot `s'` at one chain-state height are one block,
when the updaters' confirmations of the slots from `s₀` to before `s'` form one chain.

Why: as `entry_eq_of_onHonestChain`, with `onHonestChainBefore_compatible`.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the first slot of the chain;
  `s'`: the bound on the slot; `E`, `E'`: the two entries.

Read aloud: the honest chain before slot `s'` has at most one entry at each chain-state height, when
the updaters' confirmations of the slots before `s'` form one chain. -/
theorem entry_eq_of_onHonestChainBefore (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (Env : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (s₀ s' : ℕ) (E E' : Block V)
    (hChain : ConfirmationsChainBefore M S A x s₀ s')
    (hE : OnHonestChainBefore M S A x s₀ s' E) (hE' : OnHonestChainBefore M S A x s₀ s' E')
    (hEe : IsEntry M S.C E) (hEe' : IsEntry M S.C E')
    (hh : (M.chainStateOf S.C E).h = (M.chainStateOf S.C E').h) : E = E' := by
  rcases (compatible_iff _ _).1 ((onHonestChainBefore_compatible M F) S A x s₀ s' E E' hChain hE hE')
    with h1 | h1
  · have := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C E E').2.2.2.2 h1 hh
    unfold IsEntry at hEe hEe'
    rw [hEe, hEe'] at this
    exact this
  · have := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C E' E).2.2.2.2 h1 hh.symm
    unfold IsEntry at hEe hEe'
    rw [hEe, hEe'] at this
    exact this.symm

omit [RootOrder] in
/-- A justification certificate is a progress certificate.

The variables:
- `M`: the model; `F`: its facts;
- `B`: the block whose chain holds the votes; `h`: their height; `T`: the block they name.

Read aloud: every justification certificate is a progress certificate. -/
theorem progressCertOn_of_justificationCertOn {B T : Block V} {h : Height}
    (hJ : JustificationCertOn M B h T) : ProgressCertOn M B h T := by
  obtain ⟨X, hXB, Qa, hA, hAv⟩ := hJ
  exact ⟨X, hXB, Qa, hA, fun v hv => by
    obtain ⟨a, h1, h2, h3, -, h5⟩ := hAv v hv
    exact ⟨a, h1, h2, h3, h5⟩⟩

/-! ## Lemma 91 (d) -/

/-- **Lemma 91 (d), no honest FG state is contested after healing.** The proof; the audited
statement is in `Statements/Executions/HealedFrameStatements.lean`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `i`: the step; `s'`: the bound on the slot; `H`: the threshold; `v`:
  the validator.

Caches at step `i`: the one caches fact the proof reads, `v`'s at step `i`.

Read aloud: after healing there is one justification per height, so nothing contests, and the least
viable height is the greatest chain-state height minus one. -/
theorem lem91d_not_contested_until (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ i s' H : ℕ) (v : V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    -- fewer than a quorum of validators have been in the adversary set up to the later of `x.time i` and the hand-over cutoff
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max (x.time i) (M.supportCutoff S.C (s₀ + 1))))
    (hChain : ConfirmationsChainBefore M S A x s₀ s')
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hCaches : CachesOnChain M S A x s₀ H (x.st i v))
    (hv : v ∉ A.corrupted i)
    (hs' : ∀ s_a : ℕ, (∃ (k : ℕ) (u : V), k < i ∧ x.lbl k = Event.tick u (M.supportCutoff S.C (s_a + 1))) →
      s_a < s') :
    M.fg_contest (x.st i v) = false ∧
      M.head_height_floor (x.st i v) = hMax M S.C (x.st i v) - 1 := by
  -- the entry's slot is read in the step form: `hs'` itself
  have hslot := hs'
  have hc : M.fg_contest (x.st i v) = false := by
    by_contra hcon
    rw [Bool.not_eq_false] at hcon
    have hInv := (lem11_node_invariant M F S A x R E i v hv).1
    obtain ⟨hhm, D, hD, hFD, hDh, hJD⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.fg_contest_spec M F) S.C S.P S.X _ hInv
      hcon
    obtain ⟨hH, -, -, -, -⟩ := hCaches
    have hDh' : (M.chainStateOf S.C D).h = (x.st i v).justifiedHeight + 1 := by
      rw [hDh]
      exact hhm
    obtain ⟨Y, hYD, -, hYp, -, hTY, hPC⟩ := (GoldilocksCorrectness.Record.Statements.Routines.lem67_first_advance M F) S.C D (x.st i v).justifiedHeight
      (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le H) hH))
      (by rw [hDh']; exact Nat.lt_succ_self _)
    have hYT : Y ∈ (x.st i v).tree := (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E i v D Y hD hYD
    -- the entry of the chain named by `Y`'s certificate, confirmed before slot `s'`
    obtain ⟨s_a, uₐ, Eb, hk, hl, -, -, -, hAt, hEe, hEh, hEr⟩ := (cert_entry_at_slot M F U Fx) S A x R s₀ H i v Y _ _ E
       (hAdvQ.mono (by linarith)) hOld hYT hPC hH
    -- the entry of the chain named by the certificate of `J`, confirmed before slot `s'`
    obtain ⟨⟨Dj, hDj, hJDj, hhjDj⟩, -, -⟩ := (cachesWitnessed_of_exec M F) S A x R E i v
    have hj1 : 1 ≤ (M.chainStateOf S.C Dj).h_j := by
      rw [← hhjDj]; exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le H) hH)
    obtain ⟨hJC, -, -⟩ := ((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) S.C Dj).1 hj1
    rw [← hJDj, ← hhjDj] at hJC
    obtain ⟨s_b, u_b, E', hk', hl', -, -, -, hAt', hEe', hEh', hEr'⟩ := (cert_entry_at_slot M F U Fx) S A x R s₀ H i v Dj _ _
      E (hAdvQ.mono (by linarith)) hOld hDj ((progressCertOn_of_justificationCertOn M F) hJC) hH
    have hEE' : Eb = E' :=
      (entry_eq_of_onHonestChainBefore M F) S A x E s₀ s' Eb E' hChain ⟨s_a, hslot s_a ⟨_, uₐ, hk, hl⟩, hAt⟩
        ⟨s_b, hslot s_b ⟨_, u_b, hk', hl'⟩, hAt'⟩ hEe hEe' (hEh.trans hEh'.symm)
    have hTmem : (M.chainStateOf S.C Y.parent).T_h ∈ (x.st i v).tree :=
      (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E i v Y _ hYT hTY
    have hJmem : (x.st i v).justified ∈ (x.st i v).tree := (F.nd.nodeInv_justifiedInTree hInv)
    have hTJ : (M.chainStateOf S.C Y.parent).T_h = (x.st i v).justified := by
      refine (F.nd.nodeInv_rootsNameBlocksIn hInv) _ hTmem _ hJmem ?_
      rw [hEr, hEE', ← hEr']
    apply hJD
    have : (x.st i v).justified.AncestorEq D := by
      rw [← hTJ]; exact ancestorEq_trans hTY hYD
    exact this
  exact ⟨hc, (GoldilocksCorrectness.Record.Proofs.Routines.head_height_floor_of_not_contested M F) S.C S.P S.X _
    (lem11_node_invariant M F S A x R E i v hv).1 hc⟩

/-- **Lemma 91 (d), no honest FG state is contested after healing.** The proof; the audited
statement is in `Statements/Executions/HealedFrameStatements.lean`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `i₁`: the
  step at the phase's end; `i`: the step; `s'`: the bound on the slot; `H`: the threshold; `v`:
  the validator.

It is `lem91d_not_contested_until` with the caches restricted to the steps it reads.

Read aloud: after healing there is one justification per height, so nothing contests, and the least
viable height is the greatest chain-state height minus one. -/
theorem lem91d_not_contested (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ i₁ i s' H : ℕ) (v : V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hAdvQ : ∀ t : ℕ, A.AdversaryFewerThanQuorumUntil x (quorum V) t)
    (hChain : ConfirmationsChainBefore M S A x s₀ s')
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x.time i₁ ≤ x.time j → u ∉ A.corrupted j →
      CachesOnChain M S A x s₀ H (x.st j u))
    (hi : x.time i₁ ≤ x.time i) (hv : v ∉ A.corrupted i)
    (hs' : ∀ s_a : ℕ, (∃ (k : ℕ) (u : V), k < i ∧ x.lbl k = Event.tick u (M.supportCutoff S.C (s_a + 1))) →
      s_a < s') :
    M.fg_contest (x.st i v) = false ∧
      M.head_height_floor (x.st i v) = hMax M S.C (x.st i v) - 1 := by
  -- the adversary bound at every natural number gives it at every real time
  obtain ⟨n, hn⟩ := exists_nat_ge (x.time i)
  exact (lem91d_not_contested_until M F U Fx) S A x R s₀ i s' H v E
    ((hAdvQ (max n (M.supportCutoff S.C (s₀ + 1)))).mono (by push_cast; exact max_le_max hn le_rfl))
    hChain hOld (hCaches i v hi hv) hv hs'

/-! ## The root of the fork choice -/

/-! ## Lemma 91 (f) -/

/-- **Lemma 91 (f), the root of an honest fork choice is on the chain before `s'`.** The proof;
the audited statement is in `Statements/Executions/HealedFrameStatements.lean`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `j`: the step; `s'`: the bound on the slot; `H`: the threshold; `w`:
  the validator.

Roots name blocks until `x[j].time`: the proof compares `w`'s justified block, held after `j`
steps, with the entry of the honest chain at a slot whose update ran by `x[j].time`
(`cert_entry_at_slot`).

Caches at step `j`: the one caches fact the proof reads, `w`'s at step `j`.

Read aloud: the root of an honest fork choice is on the chain confirmed by the attestations sent by
then. -/
theorem lem91f_voter_root_on_chain_before_until (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ j s' H : ℕ) (w : V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hRoots : RootsNameBlocksUntil M A x (x.time j))
    -- fewer than a quorum of validators have been in the adversary set up to the later of `x.time j` and the hand-over cutoff
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max (x.time j) (M.supportCutoff S.C (s₀ + 1))))
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hCaches : CachesOnChain M S A x s₀ H (x.st j w))
    (hw : w ∉ A.corrupted j)
    (hs' : ∀ s_a : ℕ, (∃ (k : ℕ) (u : V), k < j ∧ x.lbl k = Event.tick u (M.supportCutoff S.C (s_a + 1))) →
      s_a < s') :
    OnHonestChainBefore M S A x s₀ s' (M.fg_to_ac (x.st j w)).fc_root := by
  -- the entry's slot is read in the step form: `hs'` itself
  have hslot := hs'
  obtain ⟨⟨D, hD, hJD, hhjD⟩, -, -⟩ := (cachesWitnessed_of_exec M F) S A x R E j w
  obtain ⟨hH, -, -, -, hFJ⟩ := hCaches
  have h1 : 1 ≤ (M.chainStateOf S.C D).h_j := by
    rw [← hhjD]; exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le H) hH)
  obtain ⟨hJC, -, -⟩ := ((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) S.C D).1 h1
  rw [← hJD, ← hhjD] at hJC
  obtain ⟨s_a, uₐ, Eb, hk, hl, -, -, hEb, hAt, -, -, hEr⟩ := (cert_entry_at_slot M F U Fx) S A x R s₀ H j w D _ _ E
     (hAdvQ.mono le_rfl) hOld hD ((progressCertOn_of_justificationCertOn M F) hJC) hH
  -- the entry and `J` have one root, and honest validators hold both
  have hJmem : (x.st j w).justified ∈ (x.st j w).tree :=
    (F.nd.nodeInv_justifiedInTree (lem11_node_invariant M F S A x R E j w hw).1)
  have hEJ : Eb = (x.st j w).justified :=
    hRoots Eb _ ((onHonestChainAt_inHonestTreeBy M F U) S A x R E _ uₐ (M.supportCutoff S.C (s_a + 1)) _ Eb hl
      ((time_mono M) x R hk.le) hEb)
      ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := j) (v := w) hw le_rfl hJmem) hEr.symm
  have hJb : OnHonestChainBefore M S A x s₀ s' (x.st j w).justified := by
    rw [← hEJ]; exact ⟨s_a, hslot s_a ⟨_, uₐ, hk, hl⟩, hAt⟩
  rw [(GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F)]
  rcases (GoldilocksCorrectness.Record.Proofs.Routines.get_fc_root_cases M F) S.C S.P S.X _
      (lem11_node_invariant M F S A x R E j w hw).1 with h | h
  · rw [h]; exact hJb
  · rw [h]; exact (onHonestChainBefore_of_ancestorEq M F) S A x s₀ s' hJb hFJ

/-- **Lemma 91 (f), the root of an honest fork choice is on the chain before `s'`.** The proof;
the audited statement is in `Statements/Executions/HealedFrameStatements.lean`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `i₁`: the
  step at the phase's end; `j`: the step; `s'`: the bound on the slot; `H`: the threshold; `w`:
  the validator.

Roots name blocks until `x[j].time`: the proof compares `w`'s justified block, held after `j`
steps, with the entry of the honest chain at a slot whose update ran by `x[j].time`
(`cert_entry_at_slot`).

It is `lem91f_voter_root_on_chain_before_until` with the caches restricted to the steps it reads.

Read aloud: the root of an honest fork choice is on the chain confirmed by the attestations sent by
then. -/
theorem lem91f_voter_root_on_chain_before (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ i₁ j s' H : ℕ) (w : V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hRoots : RootsNameBlocksUntil M A x (x.time j))
    -- fewer than a quorum of validators have been in the adversary set up to the later of `x.time j` and the hand-over cutoff
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max (x.time j) (M.supportCutoff S.C (s₀ + 1))))
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x.time i₁ ≤ x.time j → u ∉ A.corrupted j →
      CachesOnChain M S A x s₀ H (x.st j u))
    (hj : x.time i₁ ≤ x.time j) (hw : w ∉ A.corrupted j)
    (hs' : ∀ s_a : ℕ, (∃ (k : ℕ) (u : V), k < j ∧ x.lbl k = Event.tick u (M.supportCutoff S.C (s_a + 1))) →
      s_a < s') :
    OnHonestChainBefore M S A x s₀ s' (M.fg_to_ac (x.st j w)).fc_root :=
  (lem91f_voter_root_on_chain_before_until M F U Fx) S A x R s₀ j s' H w E hRoots hAdvQ hOld
    (hCaches j w hj hw) hw hs'

/-! ## Lemma 91 (b) -/

/-- **Lemma 91 (b), `head_height_floor` at the voter is at most the proposal's parent's height.**
The proof; the audited statement is in `Statements/Executions/HealedFrameStatements.lean`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `s`: the
  slot; `H`: the threshold; `w`: the voter; `Q`: the block;
  `iw`: the step of `w`'s tick to the vote time of slot `s`.

Caches at `iw`: the one caches fact the proof reads, `w`'s at its tick step `iw`.

Read aloud: after healing the voter's least viable height never passes a block that extends the
chain before `s − 1`, such as the honest proposal's parent. -/
theorem lem91b_voter_head_height_floor_le_parent_until (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ s H iw : ℕ) (w : V) (Q : Block V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    -- fewer than a quorum of validators have been in the adversary set up to the later of the voter's tick and the hand-over cutoff
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max (x.time iw) (M.supportCutoff S.C (s₀ + 1))))
    -- the voter's tick to its vote time
    (hlw : x.lbl iw = Event.tick w (M.voteTime S.C s))
    -- every tick to a support cutoff at a step before the voter's tick is for a slot before `s − 1`
    (hs' : ∀ s_a : ℕ, (∃ (k : ℕ) (u : V), k < iw ∧ x.lbl k = Event.tick u (M.supportCutoff S.C (s_a + 1))) →
      s_a + 1 < s)
    (hChain : ConfirmationsChainBefore M S A x s₀ (s - 1))
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hCaches : CachesOnChain M S A x s₀ H (x.st iw w))
    (hParentChain : ∀ C : Block V, OnHonestChainBefore M S A x s₀ (s - 1) C → C.AncestorEq Q) :
    M.head_height_floor (x.tickInput w (M.voteTime S.C s)) ≤ (M.chainStateOf S.C Q).h := by
  -- the voter's tick input is its state at `iw`, and it is honest there
  have htw : x.tickStep w (M.voteTime S.C s) = iw := (tickStep_eq_of_lbl M) x E hlw
  have hwi : w ∉ A.corrupted iw := E.not_mem_corrupted_of_tick hlw
  have hstw : x.tickInput w (M.voteTime S.C s) = x.st iw w := by unfold Trace.tickInput; rw [htw]
  rw [hstw, ((lem91d_not_contested_until M F U Fx) S A x R s₀ iw (s - 1) H w E hAdvQ hChain
    hOld hCaches hwi (fun s_a h => by have := hs' s_a h; omega)).2]
  -- `H + 2 ≤ h_w`: the voter's justification height is more than `H` and less than `h_w`
  obtain ⟨hHw, -, -, -, -⟩ := hCaches
  obtain ⟨⟨Dw, hDw, -, hhjDw⟩, ⟨Z, hZ, hZh⟩, -⟩ := (cachesWitnessed_of_exec M F) S A x R E iw w
  have hDwm : (M.chainStateOf S.C Dw).h ≤ hMax M S.C (x.st iw w) :=
    GoldilocksCorrectness.Record.Statements.Routines.le_hMax M (C := S.C) hDw
  have hjh := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C Dw Dw).1.2.1
  have hm2 : H + 2 ≤ hMax M S.C (x.st iw w) := by
    rw [hhjDw] at hHw
    omega_nat
  -- the block that raised `w`'s chain past `h_w − 1` carries a progress certificate at that height
  obtain ⟨Y, hYZ, -, -, -, -, hPC⟩ := (GoldilocksCorrectness.Record.Statements.Routines.lem67_first_advance M F) S.C Z
    (hMax M S.C (x.st iw w) - 1) (by omega_nat) (by rw [hZh]; omega_nat)
  have hYT : Y ∈ (x.st iw w).tree :=
    (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E iw w Z Y hZ hYZ
  -- the entry it names is confirmed at a slot whose support cutoff some validator ticked to before `iw`
  obtain ⟨s_a, uₐ, Eb, hk, hl', -, -, -, hAt, -, hEh, -⟩ := (cert_entry_at_slot M F U Fx) S A x R s₀ H iw w Y _ _ E
    hAdvQ hOld hYT hPC (by omega_nat)
  have hsa := hs' s_a ⟨_, uₐ, hk, hl'⟩
  have hEQ := hParentChain Eb ⟨s_a, by omega, hAt⟩
  have := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C Eb Q).2.2.2.1 hEQ
  rw [hEh] at this
  exact this

/-- **Lemma 91 (b), `head_height_floor` at the voter is at most the proposal's parent's height.**
The proof; the audited statement is in `Statements/Executions/HealedFrameStatements.lean`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `s`: the
  slot; `i₁`: the step at the phase's end; `H`: the threshold; `w`: the voter; `Q`: the block;
  `iw`: the step of `w`'s tick to the vote time of slot `s`.

It is `lem91b_voter_head_height_floor_le_parent_until`
with the caches restricted to the steps it reads.

Read aloud: after healing the voter's least viable height never passes a block that extends the
chain before `s − 1`, such as the honest proposal's parent. -/
theorem lem91b_voter_head_height_floor_le_parent (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ s i₁ H iw : ℕ) (w : V) (Q : Block V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hAdvQ : ∀ t : ℕ, A.AdversaryFewerThanQuorumUntil x (quorum V) t)
    -- the voter's tick to its vote time, at or after `x[i₁].time`
    (hlw : x.lbl iw = Event.tick w (M.voteTime S.C s)) (hiw : x.time i₁ ≤ x.time iw)
    -- every tick to a support cutoff at a step before the voter's tick is for a slot before `s − 1`
    (hs' : ∀ s_a : ℕ, (∃ (k : ℕ) (u : V), k < iw ∧ x.lbl k = Event.tick u (M.supportCutoff S.C (s_a + 1))) →
      s_a + 1 < s)
    (hChain : ConfirmationsChainBefore M S A x s₀ (s - 1))
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x.time i₁ ≤ x.time j → u ∉ A.corrupted j →
      CachesOnChain M S A x s₀ H (x.st j u))
    (hParentChain : ∀ C : Block V, OnHonestChainBefore M S A x s₀ (s - 1) C → C.AncestorEq Q) :
    M.head_height_floor (x.tickInput w (M.voteTime S.C s)) ≤ (M.chainStateOf S.C Q).h := by
  -- a natural number at least the later of the voter's tick and the hand-over cutoff bounds the adversary count
  obtain ⟨T, hT⟩ := exists_nat_ge (max (x.time iw) ((M.supportCutoff S.C (s₀ + 1) : ℕ) : ℝ))
  exact (lem91b_voter_head_height_floor_le_parent_until M F U Fx) S A x R s₀ s H iw w Q E
    ((hAdvQ T).mono hT) hlw hs'
    hChain hOld (hCaches iw w hiw (E.not_mem_corrupted_of_tick hlw)) hParentChain

/-! ## Lemma 91 (c) -/

/-- **Kit fact, a block of an honest validator's tree starts at or before its clock value.** A block in
the tree of a validator outside the adversary set after `k` steps has a slot whose start is at most that
validator's clock value after `k` steps.

Why: `slot_le_clockValue_of_mem_tree` bounds the block's slot by the slot of the clock value, and a slot
at most the slot of a time starts at or before that time (`slotStart_le_iff`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `x`, `R`, `E`: the execution, the run's facts, the environment's facts; `k`: the
  step; `v`: the validator; `D`: the block.

Read aloud: an honest validator holds no block of a slot that starts after its clock value. -/
theorem slotStart_le_clockValue_of_mem_tree (U : UniformSchedule M.toSlotLayout) {S : Setup V}
    {A : Activity V} {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {k : ℕ} {v : V} {D : Block V} (hv : v ∉ A.corrupted k) (hD : D ∈ (x.st k v).tree) :
    M.slotStart S.C D.slot ≤ x.clockValue k v := by
  have hsl : M.slot S.C (x.clockValue k v) = S.C.slot ((x.clockValue k v : ℕ) : Int) := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U),
      GoldilocksCorrectness.Proofs.Routines.slot_natCast]
  have h := (slot_le_clockValue_of_mem_tree M F) R E hv hD
  rw [← hsl] at h
  exact ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_le_iff M.toSlotLayout F.sched) S _ _).2 h

/-- **Kit fact, a block on the honest chain at a slot starts no later than that slot's next slot.** A
block on the honest chain at slot `σ` (an ancestor of, or equal to, a confirmation an updater of `σ`
saved at its tick to the support cutoff of slot `σ + 1`) has a slot whose start is at most the start of
slot `σ + 1`.

Why: the saved confirmation is in the updater's tree after that tick (`saved_confirmation_mem_T_of_exec`),
so the block is too (the tree holds the ancestors of its blocks); the updater's clock value there is the
support cutoff of slot `σ + 1`, a time in slot `σ + 1`; a block of the tree starts at or before the clock
value (`slotStart_le_clockValue_of_mem_tree`), so its slot is at most `σ + 1`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`, `R`, `E`: the setup, the activity, the execution, the run's facts, the environment's
  facts; `s₀`: the healed slot; `σ`: the slot; `B`: the block.

Read aloud: a block on the honest chain at a slot belongs to that slot, an earlier one or the next. -/
theorem slotStart_le_of_onHonestChainAt (U : UniformSchedule M.toSlotLayout) (S : Setup V)
    (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {s₀ σ : ℕ} {B : Block V} (hB : OnHonestChainAt M S A x s₀ σ B) :
    M.slotStart S.C B.slot ≤ M.slotStart S.C (σ + 1) := by
  obtain ⟨-, v, hv, C, hC, hBC⟩ := hB
  obtain ⟨kv, hkv, -⟩ := (Activity.mem_activeThroughoutToTick).1 hv
  have hout : x.tickOutput v (M.supportCutoff S.C (σ + 1)) = x.st (kv + 1) v := by
    unfold Trace.tickOutput; rw [(tickStep_eq_of_lbl M) x E hkv]
  rw [hout] at hC
  have hCT := (saved_confirmation_mem_T_of_exec M F U) S A x R E (kv + 1) v σ C hC
  have hBT := (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E
    (kv + 1) v C B hCT hBC
  have h1 := (slotStart_le_clockValue_of_mem_tree M F U) R E (E.not_mem_corrupted_succ_of_tick hkv) hBT
  rw [x.clockValue_succ_of_tick hkv] at h1
  obtain ⟨-, hc, -, hs1, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 1)
  have hΔ := one_le_Δ S
  have hsl : M.slot S.C (M.supportCutoff S.C (σ + 1)) = σ + 1 :=
    (GoldilocksCorrectness.Record.Proofs.Routines.slot_eq_of_mem M.toSlotLayout F.sched) S (by omega) (by omega)
  have h2 := ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_le_iff M.toSlotLayout F.sched) S _ _).1 h1
  rw [hsl] at h2
  exact (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S h2

/-- **Lemma 91 (c) at the two validators' ticks, on the chain before a slot.** The proof; its audited
statement is in `Statements/Executions/HealedFrameStatements.lean`. After the hand-over step `i₁`, the
greatest chain-state height of the tree of `p` at its tick `kp` to the clock value `cp` is at most that of
`w` at its tick `kw` to a clock value `cw` at least one delay after `cp`, when `w` also ticked earlier to a
value `c₂` from `cp` up to one delay before `cw`, `p` is active from `a₀ := cp + Δ − max(Δ, Δs)` through
the sync delay after it and `w` from `a₀` up to `kw`.

Why: `dev`'s argument, read at the two ticks. `p`'s greatest height `m` is `H + 2` or more (its caches);
the entry `Eb` of the chain at `m − 1` that the certificate on `p`'s chain names is on the honest chain,
and so is `w`'s justified block, so the two are compatible. When `w`'s justified block reaches height
`m`, done. Otherwise it is `Eb` or an ancestor of it, and a block `Z` of `p`'s tree at `kp` at height at
least `m`, with `p`'s finalized block and `Eb` ancestors of it, reaches `w`'s tree by `kw`
(`block_at_tick_of_held_tick`), when `p`'s finalized block at its last step before `a₀` is compatible
with `Z`. That holds when that step is at or before `kp` (the finalized block only grows). When it is
after `kp` and not compatible with `Z`, `p`'s justified block `J'` there is on the honest chain, a strict
descendant of `Eb` (else `p`'s finalized block there, an ancestor of `J'`, is an ancestor of `Z`), so at
height at least `m`; `p` holds `J'` at that step, its finalized block is an ancestor of `J'`, and `J'`
reaches `w`'s tree by `kw` (`block_at_tick_of_held_step`, route (b) of STOP B3R1-90-2).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `A`, `x`, `R`: the setup, the activity, the execution, the run's facts; `GST`: the time from
  which the network is synchronous; `s₀`: the healed slot; `cp`, `kp`: the clock value and the step of
  `p`'s tick; `i₁`: the step at the phase's end; `H`: the threshold; `b`: the bound on the delivery
  premises; `s'`: the bound on the slots of the chain; `cw`, `kw`: the clock value and the step of `w`'s
  tick; `c₂`, `k₂`: those of `w`'s earlier tick; `p`: the proposer; `w`: the voter.

Read aloud: after healing, a validator that ticks to a clock value at least one delay after another's
tick, having ticked earlier to a value from that tick's up to one delay before, knows at its tick a
greatest chain-state height at least the other's at its tick. -/
theorem lem91c_at_until (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ cp i₁ H b s' kp cw kw c₂ k₂ : ℕ) (p w : V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks b) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST b)
    -- roots name blocks up to the real time of `w`'s tick
    (hRoots : RootsNameBlocksUntil M A x (x.time kw))
    (hParent : ParentHeldAtDelivery M x)
    -- fewer than a quorum of validators have been in the adversary set up to the later of the real time of
    -- `w`'s tick and the hand-over cutoff
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max (x.time kw) (M.supportCutoff S.C (s₀ + 1))))
    -- `p` ticks to `cp`; `w` ticks to `cw`, at least one delay after `cp`, and earlier to `c₂`, from `cp` up
    -- to one delay before `cw`
    (hkp : x.lbl kp = Event.tick p cp)
    (hkw : x.lbl kw = Event.tick w cw) (hcw : cp + Δ S ≤ cw)
    (hk₂ : x.lbl k₂ = Event.tick w c₂) (hc₂ : cp ≤ c₂) (hc₂w : c₂ + Δ S ≤ cw)
    (hGST : GST + max (Δ S) Δs ≤ cp + Δ S)
    -- the phase's end step is before every tick of `p` to `cp`
    (hi : ∀ k : ℕ, x.lbl k = Event.tick p cp → x.time i₁ ≤ x.time k)
    (hChain : ConfirmationsChainBefore M S A x s₀ s')
    -- every slot updated at a tick before `kw` is less than `s'`
    (hs' : ∀ s_a : ℕ, (∃ (k : ℕ) (u : V), k < kw ∧ x.lbl k = Event.tick u (M.supportCutoff S.C (s_a + 1))) →
      s_a < s')
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x.time i₁ ≤ x.time j → x.time j ≤ x.time kw →
      u ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j u))
    -- `p` is active from `cp + Δ − max(Δ, Δs)` through the sync delay after it
    (hp : p ∈ A.activeThroughout x ((cp + Δ S - max (Δ S) Δs : ℕ) : ℝ)
      (((cp + Δ S - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- `w` is active from the same start up to its tick
    (hw : w ∈ A.activeThroughout x ((cp + Δ S - max (Δ S) Δs : ℕ) : ℝ) (x.time kw))
    -- the deliveries are read up to at least `cw`
    (hb : cw ≤ b) :
    hMax M S.C (x.tickInput p cp) ≤ hMax M S.C (x.tickInput w cw) := by
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ := one_le_Δ S
  have hkpt := E.tick_active kp p cp hkp
  have hkwt := E.tick_active kw w cw hkw
  have hpkp : p ∉ A.corrupted kp := E.not_mem_corrupted_of_tick hkp
  have hwkw : w ∉ A.corrupted kw := E.not_mem_corrupted_of_tick hkw
  have hcwR : (cp : ℝ) + Δ S ≤ cw := by exact_mod_cast hcw
  have hkpkwT : x.time kp < x.time kw := by linarith [hkpt.2.2, hkwt.2.1]
  have hkpkw : kp < kw := by
    by_contra h
    exact absurd (htime (not_lt.1 h)) (not_le.2 hkpkwT)
  have hip : x.time i₁ ≤ x.time kp := hi kp hkp
  have hiw : x.time i₁ ≤ x.time kw := le_trans hip hkpkwT.le
  have hinp : x.tickInput p cp = x.st kp p := by
    unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hkp]
  have hinw : x.tickInput w cw = x.st kw w := by
    unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hkw]
  rw [hinp, hinw]
  have hAdvp : A.AdversaryFewerThanQuorumUntil x (quorum V) (max (x.time kp) (M.supportCutoff S.C (s₀ + 1))) :=
    hAdvQ.mono (max_le_max hkpkwT.le le_rfl)
  have hRootsp : RootsNameBlocksUntil M A x (x.time kp) :=
    (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) hkpkwT.le hRoots
  -- `p`'s block at `m`, and `H + 2 ≤ m`
  obtain ⟨hHp, -, hJep, -, hFJp⟩ := hCaches kp p hip hkpkwT.le hpkp
  obtain ⟨⟨Dp, hDp, -, hhjDp⟩, ⟨Y, hY, hYh⟩, -⟩ := (cachesWitnessed_of_exec M F) S A x R E kp p
  have hDpm : (M.chainStateOf S.C Dp).h ≤ hMax M S.C (x.st kp p) :=
    GoldilocksCorrectness.Record.Statements.Routines.le_hMax M (C := S.C) hDp
  have hjh := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C Dp Dp).1.2.1
  have hm2 : H + 2 ≤ hMax M S.C (x.st kp p) := by
    rw [hhjDp] at hHp
    omega_nat
  -- the entry of the chain at `m − 1`, an ancestor of `Y`
  obtain ⟨Y₁, hY₁Y, -, -, -, hTY₁, hPC⟩ := (GoldilocksCorrectness.Record.Statements.Routines.lem67_first_advance M F) S.C Y
    (hMax M S.C (x.st kp p) - 1) (by omega_nat) (by rw [hYh]; omega_nat)
  have hY₁T : Y₁ ∈ (x.st kp p).tree :=
    (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E kp p Y Y₁ hY hY₁Y
  obtain ⟨s_a, uₐ, Eb, hk, hka, -, -, hEbT, hAt, hEe, hEh, hEr⟩ := (cert_entry_at_slot M F U Fx) S A x R s₀ H kp p
    Y₁ _ _ E hAdvp hOld hY₁T hPC (by omega_nat)
  have hTT : (M.chainStateOf S.C Y₁.parent).T_h ∈ (x.st kp p).tree :=
    (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E kp p Y₁ _ hY₁T hTY₁
  have hTE : (M.chainStateOf S.C Y₁.parent).T_h = Eb :=
    hRootsp _ _ ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := kp) (v := p)
        hpkp le_rfl hTT)
      ((onHonestChainAt_inHonestTreeBy M F U) S A x R E _ uₐ (M.supportCutoff S.C (s_a + 1)) _ Eb hka
        ((time_mono M) x R hk.le) hEbT) hEr
  have hEY : Eb.AncestorEq Y := by rw [← hTE]; exact ancestorEq_trans hTY₁ hY₁Y
  have hEb : OnHonestChainBefore M S A x s₀ s' Eb := ⟨s_a, hs' s_a ⟨_, uₐ, lt_trans hk hkpkw, hka⟩, hAt⟩
  -- `w`'s justified block
  obtain ⟨hHw, -, hJe, -, hFJ⟩ := hCaches kw w hiw le_rfl hwkw
  obtain ⟨s_b, ⟨kb, ub, hkb, hkbl⟩, hJat⟩ := (justified_onHonestChainAt_of_caches M F U Fx) S A x R s₀
    (M.supportCutoff S.C (s₀ + 1)) H kw w E hRoots hAdvQ
    ((lem82_honest_attestations_on_chain M F U) S A x R s₀ E) hOld hwkw hHw
  have hJchain : OnHonestChainBefore M S A x s₀ s' (x.st kw w).justified :=
    ⟨s_b, hs' s_b ⟨kb, ub, hkb, hkbl⟩, hJat⟩
  have hHCB : ∀ D ∈ (x.st kw w).tree, (M.chainStateOf S.C D).h ≤ hMax M S.C (x.st kw w) := fun D hD =>
    GoldilocksCorrectness.Record.Statements.Routines.le_hMax M (C := S.C) hD
  have key : (x.st kw w).justified.AncestorEq Eb ∨
      hMax M S.C (x.st kp p) ≤ (M.chainStateOf S.C (x.st kw w).justified).h := by
    rcases (compatible_iff _ _).1 ((onHonestChainBefore_compatible M F) S A x s₀ s' _ Eb hChain hJchain
      hEb) with h | h
    · exact Or.inl h
    · have hle := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C Eb _).2.2.2.1 h
      by_cases heq : (M.chainStateOf S.C (x.st kw w).justified).h = (M.chainStateOf S.C Eb).h
      · left
        rw [(entry_eq_of_onHonestChainBefore M F) S A x E s₀ s' _ Eb hChain hJchain hEb hJe hEe heq]
        exact ancestorEq_refl Eb
      · right
        rw [hEh] at hle heq
        omega_nat
  rcases key with hJE | hm
  swap
  · exact le_trans hm (hHCB _ (F.nd.nodeInv_justifiedInTree (lem11_node_invariant M F S A x R E kw w hwkw).1))
  -- a block `Z` of `p`'s tree at `kp`, with `p`'s finalized block and `Eb` ancestors of it, at the greatest
  -- chain-state height of `p`'s tree
  obtain ⟨s_c, ⟨kc, uc, hkc, hkcl⟩, hJpat⟩ := (justified_onHonestChainAt_of_caches M F U Fx) S A x R s₀
    (M.supportCutoff S.C (s₀ + 1)) H kp p E hRootsp hAdvp
    ((lem82_honest_attestations_on_chain M F U) S A x R s₀ E) hOld hpkp hHp
  have hJpchain : OnHonestChainBefore M S A x s₀ s' (x.st kp p).justified :=
    ⟨s_c, hs' s_c ⟨kc, uc, lt_trans hkc hkpkw, hkcl⟩, hJpat⟩
  have hJpT : (x.st kp p).justified ∈ (x.st kp p).tree :=
    F.nd.nodeInv_justifiedInTree (lem11_node_invariant M F S A x R E kp p hpkp).1
  obtain ⟨Z, hZT, hFZ, hEZ, hZh⟩ : ∃ Z ∈ (x.st kp p).tree, (x.st kp p).finalized.AncestorEq Z ∧
      Eb.AncestorEq Z ∧ hMax M S.C (x.st kp p) ≤ (M.chainStateOf S.C Z).h := by
    rcases (compatible_iff _ _).1 ((onHonestChainBefore_compatible M F) S A x s₀ s' _ Eb hChain
      hJpchain hEb) with h | h
    · exact ⟨Y, hY, ancestorEq_trans hFJp (ancestorEq_trans h hEY), hEY, le_of_eq hYh.symm⟩
    · have hle := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C Eb _).2.2.2.1 h
      by_cases heq : (M.chainStateOf S.C (x.st kp p).justified).h = (M.chainStateOf S.C Eb).h
      · have hJEb := (entry_eq_of_onHonestChainBefore M F) S A x E s₀ s' _ Eb hChain hJpchain hEb
          hJep hEe heq
        exact ⟨Y, hY, ancestorEq_trans hFJp (by rw [hJEb]; exact hEY), hEY, le_of_eq hYh.symm⟩
      · refine ⟨_, hJpT, hFJp, h, ?_⟩
        rw [hEh] at hle heq
        omega_nat
  -- the windows' start `a₀`, and what both propagation lemmas read
  have hmx := le_max_left (Δ S) Δs
  have hGSTa : GST ≤ cp + Δ S - max (Δ S) Δs := by omega
  have ha : (cp + Δ S - max (Δ S) Δs) + max (Δ S) Δs ≤ cw := by omega
  have ha₀cp : cp + Δ S - max (Δ S) Δs ≤ cp := by omega
  have hwin : ∀ i : ℕ, ((cp + Δ S - max (Δ S) Δs : ℕ) : ℝ) ≤ x.time i → i ≤ kw → w ∈ A.active i :=
    fun i h1 h2 => (A.mem_activeThroughout).1 hw i (htime h2) (le_trans h1 (htime (Nat.le_succ i)))
  have hcb : cw ≤ b := hb
  -- a block in `w`'s tree at `kw`, given as held by `p`: compatible with `w`'s finalized block, as `Eb` is
  have hFwE : (x.st kw w).finalized.AncestorEq Eb := ancestorEq_trans hFJ hJE
  by_cases hFa : (x.st (x.stepBefore (cp + Δ S - max (Δ S) Δs)) p).finalized.compatible Z = true
  · -- `Z` reaches `w` from `p`'s tick
    by_cases hZg : Z = Block.genesis
    · rw [hZg] at hZh
      exact le_trans hZh (hHCB _ ((GoldilocksCorrectness.Record.Statements.Executions.genesis_mem_T_of_exec M F)
        S A x R E kw w))
    have hZc₂ : M.slotStart S.C Z.slot ≤ c₂ :=
      le_trans ((slotStart_le_clockValue_of_mem_tree M F U) R E hpkp hZT)
        (le_trans (E.clockValue_le_of_set hpkp (Or.inl hkp)) hc₂)
    have hZw := (block_at_tick_of_held_tick M F U) S A x R GST b cp kp (cp + Δ S - max (Δ S) Δs) cw c₂ kw k₂ p w Z
      E hNet hSkew hRedeliver Sy hRoots hParent hGSTa ha hcw hcb hp hkp hZT hFa hZg hkw hwin hk₂ hc₂w hZc₂
      ((compatible_iff _ _).2 (Or.inl (ancestorEq_trans hFwE hEZ)))
    exact le_trans hZh (hHCB Z hZw)
  -- `p`'s last step before `a₀` is after `kp`: there `p`'s justified block `J'` is on the honest chain, a strict
  -- descendant of `Eb`, and `p` serves it (route (b) of STOP B3R1-90-2)
  set j' := x.stepBefore (cp + Δ S - max (Δ S) Δs) with hj'
  have hj'kp : kp < j' := by
    by_contra h
    exact hFa ((compatible_iff _ _).2 (Or.inl (ancestorEq_trans ((F_ancestorEq_of_le M F) x R E p (not_lt.1 h))
      hFZ)))
  have ha1 : 1 ≤ cp + Δ S - max (Δ S) Δs := by
    by_contra h0
    have h00 : cp + Δ S - max (Δ S) Δs = 0 := by omega
    rw [h00, (stepBefore_zero M) x R] at hj'
    omega
  obtain ⟨hj't, hj't1⟩ := (stepBefore_time M) x R E ha1
  rw [← hj'] at hj't hj't1
  have hpj'a := (A.mem_activeThroughout).1 hp j' (by
    have : (0 : ℝ) ≤ (Δs : ℝ) := by positivity
    linarith) hj't1
  have hpj' : p ∉ A.corrupted j' := (Activity.mem_active.1 hpj'a).2
  have ha₀R : ((cp + Δ S - max (Δ S) Δs : ℕ) : ℝ) ≤ cp := by exact_mod_cast ha₀cp
  have hj'cp : x.time j' < cp := lt_of_lt_of_le hj't ha₀R
  have hj'kwT : x.time j' < x.time kw := by linarith [hkwt.2.1]
  have hj'kw : j' < kw := by
    by_contra h
    exact absurd (htime (not_lt.1 h)) (not_le.2 hj'kwT)
  have hipj' : x.time i₁ ≤ x.time j' := le_trans hip (htime hj'kp.le)
  obtain ⟨hHj', -, hJe', -, hFJ'⟩ := hCaches j' p hipj' hj'kwT.le hpj'
  have hRootsj' : RootsNameBlocksUntil M A x (x.time j') :=
    (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) hj'kwT.le hRoots
  obtain ⟨s_d, ⟨kd, ud, hkd, hkdl⟩, hJ'at⟩ := (justified_onHonestChainAt_of_caches M F U Fx) S A x R s₀
    (M.supportCutoff S.C (s₀ + 1)) H j' p E hRootsj' (hAdvQ.mono (max_le_max hj'kwT.le le_rfl))
    ((lem82_honest_attestations_on_chain M F U) S A x R s₀ E) hOld hpj' hHj'
  have hJ'chain : OnHonestChainBefore M S A x s₀ s' (x.st j' p).justified :=
    ⟨s_d, hs' s_d ⟨kd, ud, lt_trans hkd hj'kw, hkdl⟩, hJ'at⟩
  rcases (compatible_iff _ _).1 ((onHonestChainBefore_compatible M F) S A x s₀ s' _ Eb hChain hJ'chain
    hEb) with h | h
  · exact absurd ((compatible_iff _ _).2 (Or.inl (ancestorEq_trans hFJ' (ancestorEq_trans h hEZ)))) hFa
  have hle := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C Eb _).2.2.2.1 h
  have hne : (M.chainStateOf S.C (x.st j' p).justified).h ≠ (M.chainStateOf S.C Eb).h := fun heq => by
    have hJEb := (entry_eq_of_onHonestChainBefore M F) S A x E s₀ s' _ Eb hChain hJ'chain hEb hJe' hEe heq
    exact hFa ((compatible_iff _ _).2 (Or.inl (ancestorEq_trans hFJ' (by rw [hJEb]; exact hEZ))))
  have hJ'h : hMax M S.C (x.st kp p) ≤ (M.chainStateOf S.C (x.st j' p).justified).h := by
    rw [hEh] at hle hne
    omega_nat
  have hJ'T : (x.st j' p).justified ∈ (x.st j' p).tree :=
    F.nd.nodeInv_justifiedInTree (lem11_node_invariant M F S A x R E j' p hpj').1
  by_cases hJ'g : (x.st j' p).justified = Block.genesis
  · rw [hJ'g] at hJ'h
    exact le_trans hJ'h (hHCB _ ((GoldilocksCorrectness.Record.Statements.Executions.genesis_mem_T_of_exec M F)
      S A x R E kw w))
  -- `J'` starts before `cp`: it is on the honest chain at `s_d`, whose update ran at a tick before `j'`
  have hJ'c₂ : M.slotStart S.C (x.st j' p).justified.slot ≤ c₂ := by
    have h1 := (slotStart_le_of_onHonestChainAt M F U) S A x R E hJ'at
    obtain ⟨-, hc, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (s_d + 1)
    have h2 := (E.tick_active kd ud _ hkdl).2.1
    have h3 : x.time kd ≤ x.time j' := htime hkd.le
    have h4 : ((M.slotStart S.C (s_d + 1) : ℕ) : ℝ) + 2 * Δ S = M.supportCutoff S.C (s_d + 1) := by
      rw [hc]; push_cast; ring
    have h5 : ((M.slotStart S.C (s_d + 1) : ℕ) : ℝ) < cp := by
      have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
      linarith
    have h6 : M.slotStart S.C (s_d + 1) < cp := by exact_mod_cast h5
    omega
  have hJ'w := (block_at_tick_of_held_step M F U) S A x R GST b cp j' (cp + Δ S - max (Δ S) Δs) cw c₂ kw k₂ p w
    (x.st j' p).justified E hNet hSkew hRedeliver Sy hRoots hParent hGSTa ha hcw hcb hp hj'cp.le hpj' hJ'T
    ((compatible_iff _ _).2 (Or.inl hFJ')) hJ'g hkw hwin hk₂ hc₂w hJ'c₂
    ((compatible_iff _ _).2 (Or.inl (ancestorEq_trans hFwE h)))
  exact le_trans hJ'h (hHCB _ hJ'w)

/-- **Lemma 91 (c) at the two validators' ticks.** The proof; its audited statement is in
`Statements/Executions/HealedFrameStatements.lean`. `lem91c_at_until` with the chain of the confirmations
of every slot and the caches at every step after the phase's end; the bound on the slots of the chain is
`cw + Δ S`: a tick before `kw` is to a clock value at most the real time of `kw` plus `ΔClockAhead`, so less
than `cw + Δ S`, and a slot is less than its next slot's support cutoff (`lt_supportCutoff_succ`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `A`, `x`, `R`: the setup, the activity, the execution, the run's facts; `GST`: the time from
  which the network is synchronous; `s₀`: the healed slot; `cp`, `kp`: the clock value and the step of
  `p`'s tick; `i₁`: the step at the phase's end; `H`: the threshold; `b`: the bound on the delivery
  premises; `cw`, `kw`: those of `w`'s tick; `c₂`, `k₂`: those of `w`'s earlier tick; `p`: the
  proposer; `w`: the voter.

Read aloud: after healing, a validator that ticks to a clock value at least one delay after another's
tick, having ticked earlier to a value from that tick's up to one delay before, knows at its tick a
greatest chain-state height at least the other's at its tick. -/
theorem lem91c_at (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ cp i₁ H b kp cw kw c₂ k₂ : ℕ) (p w : V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks b) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST b)
    -- roots name blocks up to the real time of `w`'s tick
    (hRoots : RootsNameBlocksUntil M A x (x.time kw))
    (hParent : ParentHeldAtDelivery M x)
    -- fewer than a quorum of validators have been in the adversary set up to the later of the real time of
    -- `w`'s tick and the hand-over cutoff
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max (x.time kw) (M.supportCutoff S.C (s₀ + 1))))
    (hkp : x.lbl kp = Event.tick p cp)
    (hkw : x.lbl kw = Event.tick w cw) (hcw : cp + Δ S ≤ cw)
    (hk₂ : x.lbl k₂ = Event.tick w c₂) (hc₂ : cp ≤ c₂) (hc₂w : c₂ + Δ S ≤ cw)
    (hGST : GST + max (Δ S) Δs ≤ cp + Δ S)
    (hi : ∀ k : ℕ, x.lbl k = Event.tick p cp → x.time i₁ ≤ x.time k)
    (hChain : ConfirmationsChain M S A x s₀)
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x.time i₁ ≤ x.time j → u ∉ A.corrupted j →
      CachesOnChain M S A x s₀ H (x.st j u))
    (hp : p ∈ A.activeThroughout x ((cp + Δ S - max (Δ S) Δs : ℕ) : ℝ)
      (((cp + Δ S - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hw : w ∈ A.activeThroughout x ((cp + Δ S - max (Δ S) Δs : ℕ) : ℝ) (x.time kw))
    (hb : cw ≤ b) :
    hMax M S.C (x.tickInput p cp) ≤ hMax M S.C (x.tickInput w cw) := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hkwt := (E.tick_active kw w cw hkw).2.2
  exact (lem91c_at_until M F U Fx) S A x R GST s₀ cp i₁ H b (cw + Δ S) kp cw kw c₂ k₂ p w E hNet hSkew hRedeliver Sy
    hRoots hParent hAdvQ hkp hkw hcw hk₂ hc₂ hc₂w hGST hi
    ((GoldilocksCorrectness.Record.Statements.Executions.confirmationsChainBefore_of_chain M) S A x s₀ _ hChain)
    (fun s_a ⟨k, u, hk, hkl⟩ => by
      have h1 := (E.tick_active k u _ hkl).2.1
      have h2 : x.time k ≤ x.time kw := (time_mono M) x R hk.le
      have h3 : ((M.supportCutoff S.C (s_a + 1) : ℕ) : ℝ) < ((cw + Δ S : ℕ) : ℝ) := by
        push_cast; linarith
      have h4 : M.supportCutoff S.C (s_a + 1) < cw + Δ S := by exact_mod_cast h3
      exact lt_trans ((GoldilocksCorrectness.Record.Proofs.Routines.lt_supportCutoff_succ M.toSlotLayout F.sched) S s_a) h4)
    hOld (fun j u h₁ _ h₂ => hCaches j u h₁ h₂) hp hw hb

/-- **Lemma 91 (c), the voter is at least as far as the proposer.** The proof; the audited statement is
in `Statements/Executions/HealedFrameStatements.lean`. The instance of `lem91c_at_until` at
`cp := M.slotStart S.C s`, `cw := M.voteTime S.C s`, `c₂ := M.slotStart S.C s` (the voter's own tick to the
slot's start, `kS`), `b := M.voteTime S.C s`; a tick before `kw` is to a clock value less than the
vote time plus one delay, the support cutoff of slot `s`, so it updates a slot less than `s − 1`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `A`, `x`, `R`: the setup, the activity, the execution, the run's facts; `GST`: the time from
  which the network is synchronous; `s₀`: the healed slot; `s`: the slot; `i₁`: the step at the phase's
  end; `H`: the threshold; `kp`: `p`'s tick to the slot's start; `kw`, `kS`: `w`'s ticks to the slot's vote
  time and start; `p`: the proposer; `w`: the voter.

Read aloud: after healing, a voter that ticks to the slot's start and to its vote time knows, at its
vote tick, a height at least as great as the proposer knows at its tick to the slot's start. -/
theorem lem91c_proposer_h_max_le_voter_h_max_until (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ s i₁ H kp kw kS : ℕ) (p w : V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hRoots : RootsNameBlocksUntil M A x (x.time kw))
    (hParent : ParentHeldAtDelivery M x)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max (x.time kw) (M.supportCutoff S.C (s₀ + 1))))
    (hGST : GST + max (Δ S) Δs ≤ M.voteTime S.C s)
    -- the proposer ticks to the slot's start; the voter ticks to the slot's start and to its vote time
    (hkp : x.lbl kp = Event.tick p (M.slotStart S.C s)) (hkw : x.lbl kw = Event.tick w (M.voteTime S.C s))
    (hkS : x.lbl kS = Event.tick w (M.slotStart S.C s))
    -- the phase's end step is before every tick of the proposer to the slot's start
    (hs : ∀ k : ℕ, x.lbl k = Event.tick p (M.slotStart S.C s) → x.time i₁ ≤ x.time k)
    (hChain : ConfirmationsChainBefore M S A x s₀ (s - 1))
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x.time i₁ ≤ x.time j → x.time j ≤ x.time kw →
      u ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j u))
    (hp : p ∈ A.activeThroughout x ((M.voteTime S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.voteTime S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hw : w ∈ A.activeThroughout x ((M.voteTime S.C s - max (Δ S) Δs : ℕ) : ℝ) (x.time kw)) :
    hMax M S.C (x.tickInput p (M.slotStart S.C s)) ≤ hMax M S.C (x.tickInput w (M.voteTime S.C s)) := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  obtain ⟨-, hcut, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S s
  have hkwt := (E.tick_active kw w _ hkw).2.2
  have hvt := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s
  rw [hvt] at hkw hp hw hGST hkwt ⊢
  refine (lem91c_at_until M F U Fx) S A x R GST s₀ (M.slotStart S.C s) i₁ H (M.slotStart S.C s + Δ S) (s - 1) kp
    (M.slotStart S.C s + Δ S) kw (M.slotStart S.C s) kS p w (E.upTo _) hNet hSkew hRedeliver (Sy.upTo _) hRoots
    hParent hAdvQ hkp hkw le_rfl hkS le_rfl le_rfl hGST hs hChain ?_ hOld hCaches hp hw le_rfl
  rintro s_a ⟨k, u, hk, hkl⟩
  have h1 := (E.tick_active k u _ hkl).2.1
  have h2 : x.time k ≤ x.time kw := (time_mono M) x R hk.le
  have h3 : ((M.supportCutoff S.C (s_a + 1) : ℕ) : ℝ) < M.supportCutoff S.C s := by
    rw [hcut]; push_cast at hkwt ⊢; linarith
  have h4 : M.supportCutoff S.C (s_a + 1) < M.supportCutoff S.C s := by exact_mod_cast h3
  by_contra hcon
  have := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
    (show s ≤ s_a + 1 by omega)
  omega

/-- **Lemma 91 (c), the voter is at least as far as the proposer.** The proof; the audited statement is
in `Statements/Executions/HealedFrameStatements.lean`. `lem91c_proposer_h_max_le_voter_h_max_until` with the
chain of the confirmations of every slot and the caches at every step after the phase's end.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `A`, `x`, `R`: the setup, the activity, the execution, the run's facts; `GST`: the time from
  which the network is synchronous; `s₀`: the healed slot; `s`: the slot; `i₁`: the step at the phase's
  end; `H`: the threshold; `kp`: `p`'s tick to the slot's start; `kw`, `kS`: `w`'s ticks to the slot's vote
  time and start; `p`: the proposer; `w`: the voter.

Read aloud: after healing, a voter that ticks to the slot's start and to its vote time knows, at its
vote tick, a height at least as great as the proposer knows at its tick to the slot's start. -/
theorem lem91c_proposer_h_max_le_voter_h_max (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ s i₁ H kp kw kS : ℕ) (p w : V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hRoots : RootsNameBlocksUntil M A x (x.time kw))
    (hParent : ParentHeldAtDelivery M x)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max (x.time kw) (M.supportCutoff S.C (s₀ + 1))))
    (hGST : GST + max (Δ S) Δs ≤ M.voteTime S.C s)
    (hkp : x.lbl kp = Event.tick p (M.slotStart S.C s)) (hkw : x.lbl kw = Event.tick w (M.voteTime S.C s))
    (hkS : x.lbl kS = Event.tick w (M.slotStart S.C s))
    -- the phase's end step is before every tick of the proposer to the slot's start
    (hs : ∀ k : ℕ, x.lbl k = Event.tick p (M.slotStart S.C s) → x.time i₁ ≤ x.time k)
    (hChain : ConfirmationsChain M S A x s₀)
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x.time i₁ ≤ x.time j → u ∉ A.corrupted j →
      CachesOnChain M S A x s₀ H (x.st j u))
    (hp : p ∈ A.activeThroughout x ((M.voteTime S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.voteTime S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hw : w ∈ A.activeThroughout x ((M.voteTime S.C s - max (Δ S) Δs : ℕ) : ℝ) (x.time kw)) :
    hMax M S.C (x.tickInput p (M.slotStart S.C s)) ≤ hMax M S.C (x.tickInput w (M.voteTime S.C s)) :=
  (lem91c_proposer_h_max_le_voter_h_max_until M F U Fx) S A x R GST s₀ s i₁ H kp kw kS p w E hNet hSkew hRedeliver
    Sy hRoots hParent hAdvQ hGST hkp hkw hkS hs
    ((GoldilocksCorrectness.Record.Statements.Executions.confirmationsChainBefore_of_chain M) S A x s₀ _ hChain) hOld
    (fun j u h₁ _ h₂ => hCaches j u h₁ h₂) hp hw

/-! ## Lemma 91 (e) -/

/-- **Lemma 91 (e) at the proposer's tick.** The greatest chain-state height `p` knows at its tick to
the start of slot `s` is at most the chain-state height of the block `B` it proposes at that tick. It is
`lem91e_proposal_height_ge_h_max_until` with every read moved to the proposer's tick step `ip`, where a
node's own state is read: the roots, the count of the adversary and the caches up
to the real time of `ip`, and the slots whose updates ran at ticks before `ip` bounded by `hs'` (the step
form of Lemma 91 (d)). It is the route F-77-3 names for `honest_proposal_extends_chain_until`'s `hMax`
comparison: with `B` in the voter's tree at its tick, the voter's greatest chain-state height is at
least `B`'s.

Why: `p`'s greatest height `m` is reached by a block `Y` it holds (`cachesWitnessed_of_exec`); the
first block `Y₁` of `Y`'s chain at height `m` carries a progress certificate at `m − 1` whose entry
`Eb` is on the honest chain at a slot updated at a tick before `ip` (`cert_entry_at_slot`), so less
than `s − 1` (`hs'`); when `B`'s parent is at `m − 1` (otherwise `B` is already at least at `m`),
`Eb` is the parent's `T_h` (Lemma 47 (e)), `p`'s pool holds the certificate's attestations, and Lemma
53 puts `B` at height `m`; in the timeout case, `Y₁`'s slot is at most `s`, since `p` holds no block of
a slot later than its clock value's (`slot_le_clockValue_of_mem_tree`), at most the start of slot `s`
at that tick (`clockValue_le_of_set`), against Lemma 53's slot bound.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `x`: the setup, the execution; `s₀`: the healed slot; `s`: the slot; `i₁`: the step at the
  phase's end; `H`: the threshold; `ip`: the step of `p`'s tick to the start of slot `s`; `p`: the
  proposer; `B`: the proposal.

Read aloud: an honest proposer's proposal reaches the greatest chain-state height the proposer knows
when it proposes. -/
theorem lem91e_proposal_height_ge_h_max_at_tick (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ s i₁ H ip : ℕ) (p : V) (B : Block V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    -- roots name blocks up to the real time of `p`'s tick
    (hRoots : RootsNameBlocksUntil M A x (x.time ip))
    -- fewer than a quorum of validators have been in the adversary set up to the later of the real time of `p`'s
    -- tick and the hand-over cutoff
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max (x.time ip) (M.supportCutoff S.C (s₀ + 1))))
    (hs : x.time i₁ < M.slotStart S.C s)
    (hChain : ConfirmationsChainBefore M S A x s₀ (s - 1))
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    -- `p`'s caches at its tick are on the chain
    (hCaches : CachesOnChain M S A x s₀ H (x.st ip p))
    -- every slot updated at a tick before `ip` is less than `s − 1`
    (hs' : ∀ s_a : ℕ, (∃ (k : ℕ) (u : V), k < ip ∧ x.lbl k = Event.tick u (M.supportCutoff S.C (s_a + 1))) →
      s_a < s - 1)
    -- step `ip` is `p`'s tick to the start of slot `s`, and it put `B` on the wire
    (hl : x.lbl ip = Event.tick p (M.slotStart S.C s))
    (hsent : (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (ip + 1) - x.sent ip)
    (hParentHeightP : M.head_height_floor (x.tickInput p (M.slotStart S.C s)) ≤
      (M.chainStateOf S.C B.parent).h)
    (hParentChain : ∀ C : Block V, OnHonestChainBefore M S A x s₀ (s - 1) C →
      C.AncestorEq B.parent) :
    hMax M S.C (x.tickInput p (M.slotStart S.C s)) ≤ (M.chainStateOf S.C B).h := by
  have h1s : 1 ≤ s := by
    by_contra h0
    have h0' : s = 0 := by omega
    have hz : M.slotStart S.C 0 = 0 := by
      rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_zero]
    rw [h0', hz] at hs
    have := (time_nonneg M) x R i₁
    push_cast at hs
    linarith
  have hpi : p ∉ A.corrupted ip := E.not_mem_corrupted_of_tick hl
  have hin : x.tickInput p (M.slotStart S.C s) = x.st ip p := by
    unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hl]
  rw [hin] at hParentHeightP ⊢
  -- the proposal's slot and parent
  have hss : s = s - 1 + 1 := by omega
  have hl' := hl
  rw [hss] at hl'
  obtain ⟨hBslot, -, hBpar?, -⟩ := (proposal_parent_walk_end M F U) S A x R E (s - 1) ip B p hl' hsent
  rw [← hss] at hBslot
  have hPB : B.parent.AncestorEq B := ancestorEq_of_parent? hBpar?
  -- `p`'s block at `m`, and `H + 2 ≤ m`
  obtain ⟨hHp, -, -, -, -⟩ := id hCaches
  obtain ⟨⟨Dp, hDp, -, hhjDp⟩, ⟨Y, hY, hYh⟩, -⟩ := (cachesWitnessed_of_exec M F) S A x R E ip p
  have hDpm : (M.chainStateOf S.C Dp).h ≤ hMax M S.C (x.st ip p) :=
    GoldilocksCorrectness.Record.Statements.Routines.le_hMax M (C := S.C) hDp
  have hjh := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C Dp Dp).1.2.1
  have hm2 : H + 2 ≤ hMax M S.C (x.st ip p) := by
    rw [hhjDp] at hHp
    omega_nat
  -- the block that raised `Y`'s chain past `m − 1`, and the branch
  obtain ⟨Y₁, hY₁Y, -, hY₁p, -, hTY₁, hPC, hbranch⟩ :=
    (GoldilocksCorrectness.Record.Statements.Routines.lem67b_first_advance_cases M F) S.C Y
      (hMax M S.C (x.st ip p) - 1) (by omega_nat) (by rw [hYh]; omega_nat)
  have hY₁T : Y₁ ∈ (x.st ip p).tree :=
    (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E ip p Y Y₁ hY hY₁Y
  obtain ⟨s_a, uₐ, Eb, hk, hka, -, -, hEbT, hAt, hEe, hEh, hEr⟩ := (cert_entry_at_slot M F U Fx) S A x R s₀ H ip p
    Y₁ _ _ E hAdvQ hOld hY₁T hPC (by omega_nat)
  have hTT : (M.chainStateOf S.C Y₁.parent).T_h ∈ (x.st ip p).tree :=
    (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E ip p Y₁ _ hY₁T hTY₁
  have hTE : (M.chainStateOf S.C Y₁.parent).T_h = Eb :=
    hRoots _ _ ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := ip) (v := p)
        hpi le_rfl hTT)
      ((onHonestChainAt_inHonestTreeBy M F U) S A x R E _ uₐ (M.supportCutoff S.C (s_a + 1)) _ Eb hka
        ((time_mono M) x R hk.le) hEbT) hEr
  have hsa : s_a < s - 1 := hs' s_a ⟨_, uₐ, hk, hka⟩
  have hEP : Eb.AncestorEq B.parent := hParentChain Eb ⟨s_a, hsa, hAt⟩
  by_cases hm : hMax M S.C (x.st ip p) ≤ (M.chainStateOf S.C B.parent).h
  · exact le_trans hm (((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C B.parent
      B).2.2.2.1 hPB)
  -- the parent is at `m − 1`, with `Eb` the entry of its height
  rw [((lem91d_not_contested_until M F U Fx) S A x R s₀ ip (s - 1) H p E hAdvQ hChain hOld hCaches hpi
    hs').2] at hParentHeightP
  have hEPh : (M.chainStateOf S.C Eb).h = (M.chainStateOf S.C B.parent).h := by
    rw [hEh]; omega_nat
  have hTP : (M.chainStateOf S.C B.parent).T_h = Eb := by
    have := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C Eb B.parent).2.2.2.2
      hEP hEPh
    unfold IsEntry at hEe
    rw [← this, hEe]
  have hpool : ∀ Z : Block V, Z.AncestorEq Y₁ → ∀ a : Attestation V, M.on_chain a Z = true →
      a ∈ (x.tickInput p (M.slotStart S.C s)).attestationsHeld := by
    intro Z hZ a ha
    rw [hin]
    exact (pool_holds_chain_attestations M F) S A x R E ip p Y₁ a hY₁T
      ((GoldilocksCorrectness.Record.Proofs.Routines.on_chain_mono M F) a hZ ha)
  have hProp : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i :=
    ⟨ip, hl, hsent⟩
  rcases hbranch with hJust | hTime
  · obtain ⟨X, hXY, Qa, hA, hAv⟩ := hJust
    rw [GoldilocksCorrectness.Record.quorumAt_eq_quorum Fx F.sched X] at hA
    have hpoolA : ∀ u ∈ Qa, ∃ a ∈ (x.tickInput p (M.slotStart S.C s)).attestationsHeld,
        a.val_index = u ∧ a.h = (M.chainStateOf S.C B.parent).h ∧
        a.T = (M.chainStateOf S.C B.parent).T_h.root ∧ a.τ = false := by
      intro u hu
      obtain ⟨a, h1, h2, h3, h4, h5⟩ := hAv u hu
      refine ⟨a, hpool X hXY a h5, h1, ?_, ?_, h4⟩
      · rw [h2]; omega_nat
      · rw [h3, hTE, hTP]
    have h53 := (lem53_next_honest_proposal_carries_certificate M F U Fx) S A x R E s p B B.parent Qa hProp rfl
      hA (fun u hu => by
        obtain ⟨a, h1, h2, h3, h4, -⟩ := hpoolA u hu
        exact ⟨a, h1, h2, h3, h4⟩)
    have := (h53.2 hpoolA).1
    rw [this]
    omega_nat
  · obtain ⟨X, hXY, Qa, hA, hAv⟩ := hPC
    rw [GoldilocksCorrectness.Record.quorumAt_eq_quorum Fx F.sched X] at hA
    have h53 := (lem53_next_honest_proposal_carries_certificate M F U Fx) S A x R E s p B B.parent Qa hProp rfl
      hA (fun u hu => by
        obtain ⟨a, h1, h2, h3, h5⟩ := hAv u hu
        refine ⟨a, hpool X hXY a h5, h1, ?_, ?_⟩
        · rw [h2]; omega_nat
        · rw [h3, hTE, hTP])
    rcases h53.1 with h | ⟨-, -, hslotB⟩
    · rw [h]; omega_nat
    · exfalso
      -- `p` holds no block of a slot later than its clock value's, at most the start of slot `s`
      have hY₁s : Y₁.slot ≤ s := by
        have h1 := (slot_le_clockValue_of_mem_tree M F) R E hpi hY₁T
        have h2 : x.clockValue ip p ≤ M.slotStart S.C s := E.clockValue_le_of_set hpi (Or.inl hl)
        have h3 := GoldilocksCorrectness.Proofs.Routines.slot_mono_int S
          (show ((x.clockValue ip p : ℕ) : Int) ≤ ((M.slotStart S.C s : ℕ) : Int) by exact_mod_cast h2)
        have h4 : S.C.slot ((M.slotStart S.C s : ℕ) : Int) = s := by
          rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast,
            ← (GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U),
            (GoldilocksCorrectness.Record.Proofs.Routines.slot_eq_of_mem M.toSlotLayout F.sched) S le_rfl
              (by rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U),
                (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add,
                Nat.mul_one]; have := one_le_Δ S; omega)]
        exact h1.trans (h3.trans h4.le)
      rw [hTP, hBslot] at hslotB
      rw [hTE] at hTime
      omega_nat

/-- **Lemma 91 (e), the honest proposal reaches the proposer's greatest chain-state height.** The
proof; the audited statement is in `Statements/Executions/HealedFrameStatements.lean`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `s`: the
  slot; `i₁`: the step at the phase's end; `H`: the threshold; `p`: the proposer; `B`: the
  proposal.

Roots name blocks until the real time of `p`'s tick to `M.slotStart S.C s`: the proof
compares a block `p` holds at that tick (the entry `T_h` of a chain state on `p`'s chain) with the
entry of the honest chain at a slot whose update ran by then (`cert_entry_at_slot`).

Caches at `p`'s tick to `M.slotStart S.C s`: the one caches fact the proof reads.

Read aloud: an honest proposer always includes the certificate that reached the greatest height it
knows. -/
theorem lem91e_proposal_height_ge_h_max_until (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ s i₁ H : ℕ) (p : V) (B : Block V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    -- roots name blocks up to the real time of the proposer's tick to the slot's start
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep p (M.slotStart S.C s))))
    -- fewer than a quorum of validators have been in the adversary set up to the later of the real time of that tick
    -- and the hand-over cutoff
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V)
      (max (x.time (x.tickStep p (M.slotStart S.C s))) (M.supportCutoff S.C (s₀ + 1))))
    -- the slot starts after the phase's end, and every tick of the proposer to that start is at or after it
    (hs : x.time i₁ < M.slotStart S.C s ∧
      ∀ k : ℕ, x.lbl k = Event.tick p (M.slotStart S.C s) → x.time i₁ ≤ x.time k)
    (hChain : ConfirmationsChainBefore M S A x s₀ (s - 1))
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    -- the proposer's caches at its tick to the slot's start are on the honest chain
    (hCaches : CachesOnChain M S A x s₀ H (x.tickInput p (M.slotStart S.C s)))
    (hp : p ∉ A.corruptedAtTime x (M.slotStart S.C s))
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    (hParentHeightP : M.head_height_floor (x.tickInput p (M.slotStart S.C s)) ≤
      (M.chainStateOf S.C B.parent).h)
    (hParentChain : ∀ C : Block V, OnHonestChainBefore M S A x s₀ (s - 1) C →
      C.AncestorEq B.parent) :
    hMax M S.C (x.tickInput p (M.slotStart S.C s)) ≤ (M.chainStateOf S.C B).h := by
  -- the step form at the tick `hPropose` names: every slot updated at a tick before it is less
  -- than `s − 1`, since that tick is at a real time at most `ΔClockBehind` after the slot's start (`hSkew`)
  obtain ⟨ip, hl, hsent⟩ := hPropose
  have hts : x.tickStep p (M.slotStart S.C s) = ip := (tickStep_eq_of_lbl M) x E hl
  have hin : x.tickInput p (M.slotStart S.C s) = x.st ip p := by unfold Trace.tickInput; rw [hts]
  rw [hts] at hRoots hAdvQ
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ : (1 : ℝ) ≤ Δ S := by exact_mod_cast one_le_Δ S
  have h1s : 1 ≤ s := by
    by_contra h0
    have h0' : s = 0 := by omega
    have hz : M.slotStart S.C 0 = 0 := by
      rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_zero]
    have h := hs.1
    rw [h0', hz] at h
    have := (time_nonneg M) x R i₁
    push_cast at h
    linarith
  have hcs : M.slotStart S.C s + 2 * Δ S ≤ M.supportCutoff S.C s := by
    have hc := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s
    have hv := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s
    omega
  have hcsR : ((M.slotStart S.C s : ℕ) : ℝ) + 2 * Δ S ≤ ((M.supportCutoff S.C s : ℕ) : ℝ) := by exact_mod_cast hcs
  have hip2 := (E.tick_active ip p _ hl).2.2
  have hs' : ∀ s_a : ℕ, (∃ (k : ℕ) (u : V), k < ip ∧ x.lbl k = Event.tick u (M.supportCutoff S.C (s_a + 1))) →
      s_a < s - 1 := by
    rintro s_a ⟨k, u, hk, hkl⟩
    have h1 := (E.tick_active k u _ hkl).2.1
    have h2 : x.time k ≤ x.time ip := (time_mono M) x R hk.le
    have h3 : ((M.supportCutoff S.C (s_a + 1) : ℕ) : ℝ) < ((M.supportCutoff S.C s : ℕ) : ℝ) := by linarith
    have h4 : M.supportCutoff S.C (s_a + 1) < M.supportCutoff S.C (s - 1 + 1) := by
      rw [show s - 1 + 1 = s by omega]; exact_mod_cast h3
    exact ((GoldilocksCorrectness.Record.Proofs.Routines.slot_le_of_supportCutoff_lt M.toSlotLayout F.sched) S s_a
      (s - 1)).2.1 h4
  exact (lem91e_proposal_height_ge_h_max_at_tick M F U Fx) S A x R s₀ s i₁ H ip p B E hRoots hAdvQ hs.1 hChain hOld
    (by rw [← hin]; exact hCaches) hs' hl hsent hParentHeightP hParentChain

/-- **Lemma 91 (e), the honest proposal reaches the proposer's greatest chain-state height.** The
proof; the audited statement is in `Statements/Executions/HealedFrameStatements.lean`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `s`: the
  slot; `i₁`: the step at the phase's end; `H`: the threshold; `p`: the proposer; `B`: the
  proposal.

Roots name blocks until the real time of `p`'s tick to `M.slotStart S.C s`: the proof
compares a block `p` holds at that tick (the entry `T_h` of a chain state on `p`'s chain) with the
entry of the honest chain at a slot whose update ran by then (`cert_entry_at_slot`).

It is `lem91e_proposal_height_ge_h_max_until` with the caches restricted to the steps it reads.

Read aloud: an honest proposer always includes the certificate that reached the greatest height it
knows. -/
theorem lem91e_proposal_height_ge_h_max (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ s i₁ H : ℕ) (p : V) (B : Block V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    -- roots name blocks up to the real time of the proposer's tick to the slot's start
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep p (M.slotStart S.C s))))
    -- fewer than a quorum of validators have been in the adversary set up to the later of the real time of that tick
    -- and the hand-over cutoff
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V)
      (max (x.time (x.tickStep p (M.slotStart S.C s))) (M.supportCutoff S.C (s₀ + 1))))
    -- the slot starts after the phase's end, and every tick of the proposer to that start is at or after it
    (hs : x.time i₁ < M.slotStart S.C s ∧
      ∀ k : ℕ, x.lbl k = Event.tick p (M.slotStart S.C s) → x.time i₁ ≤ x.time k)
    (hChain : ConfirmationsChainBefore M S A x s₀ (s - 1))
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x.time i₁ ≤ x.time j → u ∉ A.corrupted j →
      CachesOnChain M S A x s₀ H (x.st j u))
    (hp : p ∉ A.corruptedAtTime x (M.slotStart S.C s))
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    (hParentHeightP : M.head_height_floor (x.tickInput p (M.slotStart S.C s)) ≤
      (M.chainStateOf S.C B.parent).h)
    (hParentChain : ∀ C : Block V, OnHonestChainBefore M S A x s₀ (s - 1) C →
      C.AncestorEq B.parent) :
    hMax M S.C (x.tickInput p (M.slotStart S.C s)) ≤ (M.chainStateOf S.C B).h :=
  (lem91e_proposal_height_ge_h_max_until M F U Fx) S A x R s₀ s i₁ H p B E hSkew hRoots hAdvQ hs
    hChain hOld (by
      obtain ⟨ip, hl, -⟩ := hPropose
      unfold Trace.tickInput
      rw [(tickStep_eq_of_lbl M) x E hl]
      exact hCaches ip p (hs.2 ip hl) (E.not_mem_corrupted_of_tick hl))
    hp hPropose hParentHeightP hParentChain


end GoldilocksCorrectness.Record.Proofs.Executions

