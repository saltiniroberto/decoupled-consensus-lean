module
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

@[expose] public section

/-!
# Lemma 91: the frame facts after healing

The proofs of Lemma 91 (b) to (f), stated in
`GoldilocksCorrectness/Statements/Executions/HealedFrameStatements.lean`, and the kit facts they
use:

- `cert_entry_at_slot`, the certificate route: a progress certificate at a height greater than
  the threshold on a held chain names, by root, an entry of the honest chain at a slot whose
  support cutoff is at most the reading time (Lemma 83's route with Lemma 82 (b));
- `entry_eq_of_onHonestChain`: two entries of the honest chain at one height are one block;
- `onHonestChainBefore_compatible` and `entry_eq_of_onHonestChainBefore`, the same two facts over
  the chain before a slot, read under `ConfirmationsChainBefore`;
- `onHonestChainBefore_of_ancestorEq`, `get_fc_root_cases`, `slot_after_healed_round`.

Lemma 91 (a), `lem91a_attested_height_le_proposer_h_max`, is not landed; the letters (b) to (f) are kept.


-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff)
open GoldilocksCorrectness.Proofs.Routines (lt_supportCutoff_succ one_le_Δ slotStart_eq
  slot_after_healed_round slot_eq_of_mem slot_le_of_supportCutoff_lt voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (compatible_of_ancestorEq_both lem47_chain_state_heights)
open GoldilocksCorrectness.Statements.Routines (IsEntry chainStateOf)

open GoldilocksCorrectness.Proofs.Routines (fc_root_eq fg_contest_spec get_fc_root_cases
  head_height_floor_of_not_contested)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (JustificationCertOn ProgressCertOn
  lem66_chain_state_certified lem67_first_advance lem67b_first_advance_cases)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  ancestorEq_antisymm ancestorEq_of_parent?)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded in the goal and in every
hypothesis: `omega` does not see a fact stated at either. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

/-! ## The certificate route -/

/-- The configuration `stepBefore x t` is at the time `t − 1`, for `t ≥ 1` in an execution where
every time is reached.

The variables:
- `x`: the execution; `t`: the time. -/
theorem time_stepBefore_add_one {S : Setup V} {Sched : Schedule V}
    (x : AtomicExec (protocol S) Sched) (hDiv : TimeDiverges x.toTrace) {t : ℕ} (ht : 1 ≤ t) :
    x[stepBefore x t].time + 1 = t :=
  (stepBefore_spec x hDiv ht).2.1

/-- **Kit fact, the certificate route.** Under unforgeability, take a block `Y` that `w` holds
after `j` steps and a progress certificate on the chain of `Y` at a height `h` greater than `H`
naming `T`'s root; when fewer than a quorum of validators have been in the adversary set up to
the time after `j` steps and every honest attestation sent before the support cutoff of slot
`s₀ + 1` has height at most `H`: some slot `s_a`, whose support cutoff of slot `s_a + 1` is at
most the time after `j` steps, has some entry block `E` on the honest chain at slot `s_a`, with
the chain-state height `h` and `T`'s root.

Why: Lemma 83's route, with Lemma 82 (b) in place of Lemma 82: some member `u` of the quorum is
honest up to the time after `j` steps; `u`'s vote is in `u`'s record (Lemma 74), so `u`'s tick put
an attestation with that content on the wire at some earlier step; its height is greater than
`H`, so it was sent at or after the support cutoff of slot `s₀ + 1`, and Lemma 82 (b) names the
slot `s_a` whose update it followed and the entry.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `H`: the
  bound on the old attestations' heights; `j`: the step; `w`: the holder; `Y`: the held block;
  `T`: the block the certificate names; `h`: its height.

Read aloud: a certificate above the threshold on a held chain names, by root, an entry of the
honest chain confirmed at a slot whose update ran by then. -/
theorem cert_entry_at_slot (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ H j : ℕ) (w : V) (Y T : Block V) (h : Height)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : AdversaryFewerThanQuorumUntil Sched (quorum V) (x[j].time : Int))
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hY : Y ∈ (x[j][w].st).S.T) (hJ : ProgressCertOn Y h T) (hH : H < h) :
    ∃ (s_a : ℕ) (E : Block V), supportCutoff S (s_a + 1) ≤ x[j].time ∧
      OnHonestChainAt S Sched x s₀ s_a E ∧ IsEntry S.C E ∧ (chainStateOf S.C E).h = h ∧
      T.root = E.root := by
  obtain ⟨A, hqA, hA⟩ := hJ
  obtain ⟨u, hu, hhon⟩ : ∃ u ∈ A, HonestThrough x j u := by
    by_contra hno
    have hall : ∀ v ∈ A, ∃ t' : Int, t' ≤ (x[j].time : Int) ∧ v ∈ Sched.adv t' := by
      intro v hv
      by_contra hn
      exact hno ⟨v, hv, fun t' ht' ha => hn ⟨t', ht', ha⟩⟩
    have h3 := hAdvQ A hall
    omega
  obtain ⟨a, hau, hah, haT, hon⟩ := hA u hu
  have hrec := lem74_honest_attestations_recorded S Sched x hU j w Y a hY hon
    (by rw [hau]; exact hhon)
  rw [hau] at hrec
  obtain ⟨j', t', a', hj', hl, hAw, hHon, hsent, -, hcont, -⟩ :=
    record_content_sent_step S Sched x u j _ hrec
  have hh' : a'.h = h := by
    rw [← hah]
    exact congrArg AttestationContent.h hcont
  have hT' : a'.T = T.root := by
    rw [← haT]
    exact congrArg AttestationContent.T hcont
  have htj : t' ≤ x[j].time := by
    rw [← (time_of_lbl_tickAllAwake x hl).2]
    exact time_mono x hj'
  rcases Nat.lt_or_ge t' (supportCutoff S (s₀ + 1)) with hlt | hge
  · have hle := hOld j' t' u a' hl hlt hAw hHon hsent
    rw [hh'] at hle
    exact absurd hle (Nat.not_le.mpr hH)
  · obtain ⟨s, E, C, hs₀, ht', hv, hSaved, hEC, hE, hEh, hEr⟩ :=
      lem82b_entry_at_slot S Sched x s₀ j' t' u a' hDiv hMono hl hge hAw hHon hsent
    exact ⟨s, E, ht' ▸ htj, ⟨hs₀, u, hv, C, hSaved, hEC⟩, hE, hEh.trans hh', hT'.symm.trans hEr⟩

/-- Two entry blocks of the honest chain at one chain-state height are one block.

Why: they are compatible (`onHonestChain_compatible`); of two blocks of one chain at one height,
the `T_h` is one (Lemma 47 (e)), and each is its own `T_h`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the first slot of the chain;
  `E`, `E'`: the two entries. -/
theorem entry_eq_of_onHonestChain (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ : ℕ) (E E' : Block V)
    (hChain : ConfirmationsChain S Sched x s₀)
    (hE : OnHonestChain S Sched x s₀ E) (hE' : OnHonestChain S Sched x s₀ E')
    (hEe : IsEntry S.C E) (hEe' : IsEntry S.C E')
    (hh : (chainStateOf S.C E).h = (chainStateOf S.C E').h) : E = E' := by
  rcases (compatible_iff _ _).1 (onHonestChain_compatible S Sched x s₀ E E' hChain hE hE') with
    h1 | h1
  · have := (lem47_chain_state_heights S.C E E').2.2.2.2 h1 hh
    unfold IsEntry at hEe hEe'
    rw [hEe, hEe'] at this
    exact this
  · have := (lem47_chain_state_heights S.C E' E).2.2.2.2 h1 hh.symm
    unfold IsEntry at hEe hEe'
    rw [hEe, hEe'] at this
    exact this.symm

/-- An ancestor of a block of the chain before `s'` is on the chain before `s'`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the first slot of the chain;
  `s'`: the bound on the slot; `D`, `D'`: the ancestor and the block. -/
theorem onHonestChainBefore_of_ancestorEq (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ s' : ℕ) {D D' : Block V}
    (hD : OnHonestChainBefore S Sched x s₀ s' D') (h : D.AncestorEq D') :
    OnHonestChainBefore S Sched x s₀ s' D := by
  obtain ⟨s, hs, hs₀, u, hu, C, hC, hDC⟩ := hD
  exact ⟨s, hs, hs₀, u, hu, C, hC, ancestorEq_trans h hDC⟩

/-- Two blocks on the honest chain before slot `s'` are compatible, when the updaters'
confirmations of the slots from `s₀` to before `s'` form one chain.

Why: each is an ancestor of, or equal to, an updater's confirmation of a slot less than `s'`; the
two confirmations are ordered or, at one slot, compatible.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the first slot of the chain;
  `s'`: the bound on the slot; `B`, `B'`: the blocks. -/
theorem onHonestChainBefore_compatible (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ s' : ℕ) (B B' : Block V)
    (hChain : ConfirmationsChainBefore S Sched x s₀ s')
    (hB : OnHonestChainBefore S Sched x s₀ s' B) (hB' : OnHonestChainBefore S Sched x s₀ s' B') :
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
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the first slot of the chain;
  `s'`: the bound on the slot; `E`, `E'`: the two entries. -/
theorem entry_eq_of_onHonestChainBefore (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ s' : ℕ) (E E' : Block V)
    (hChain : ConfirmationsChainBefore S Sched x s₀ s')
    (hE : OnHonestChainBefore S Sched x s₀ s' E) (hE' : OnHonestChainBefore S Sched x s₀ s' E')
    (hEe : IsEntry S.C E) (hEe' : IsEntry S.C E')
    (hh : (chainStateOf S.C E).h = (chainStateOf S.C E').h) : E = E' := by
  rcases (compatible_iff _ _).1 (onHonestChainBefore_compatible S Sched x s₀ s' E E' hChain hE hE')
    with h1 | h1
  · have := (lem47_chain_state_heights S.C E E').2.2.2.2 h1 hh
    unfold IsEntry at hEe hEe'
    rw [hEe, hEe'] at this
    exact this
  · have := (lem47_chain_state_heights S.C E' E).2.2.2.2 h1 hh.symm
    unfold IsEntry at hEe hEe'
    rw [hEe, hEe'] at this
    exact this.symm

omit [RootOrder] in
/-- A justification certificate is a progress certificate.

The variables:
- `B`: the block whose chain holds the votes; `h`: their height; `T`: the block they name. -/
theorem progressCertOn_of_justificationCertOn {B T : Block V} {h : Height}
    (hJ : JustificationCertOn B h T) : ProgressCertOn B h T := by
  obtain ⟨A, hA, hAv⟩ := hJ
  exact ⟨A, hA, fun v hv => by
    obtain ⟨a, h1, h2, h3, -, h5⟩ := hAv v hv
    exact ⟨a, h1, h2, h3, h5⟩⟩


/-! ## Lemma 91 (d) -/

/-- **Lemma 91 (d), no honest FG state is contested after healing.** The proof; the audited
statement is in `Statements/Executions/HealedFrameStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `i₁`: the
  step at the phase's end; `i`: the step; `s'`: the bound on the slot; `H`: the threshold; `v`:
  the validator.

Caches up to `x[i].time`: the proof reads `v`'s caches at step `i` only. -/
theorem lem91d_not_contested_until (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ i₁ i s' H : ℕ) (v : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hChain : ConfirmationsChainBefore S Sched x s₀ s')
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → x[j].time ≤ x[i].time →
      u ∉ Sched.adv (x[j].time : Int) → CachesOnChain S Sched x s₀ H (x[j][u].st))
    (hi : x[i₁].time ≤ x[i].time) (hv : v ∉ Sched.adv (x[i].time : Int))
    (hs' : ∀ s_a : ℕ, supportCutoff S (s_a + 1) ≤ x[i].time → s_a < s') :
    fg_contest (x[i][v].st).S = false ∧
      head_height_floor (x[i][v].st).S = (x[i][v].st).S.h_max - 1 := by
  have hc : fg_contest (x[i][v].st).S = false := by
    by_contra hcon
    rw [Bool.not_eq_false] at hcon
    obtain ⟨hhm, D, hD, hFD, hDh, hJD⟩ := fg_contest_spec _ hcon
    obtain ⟨hH, -, -, -, -⟩ := hCaches i v hi le_rfl hv
    have hInv := (lem11_node_invariant S Sched x i v).1
    have hσD : (x[i][v].st).S.σ D = chainStateOf S.C D := hInv.2.2.2.2.2.1 D hD
    have hDh' : (chainStateOf S.C D).h = (x[i][v].st).S.h_j + 1 := by
      have : ((x[i][v].st).S.σ D).h = (x[i][v].st).S.h_max := hDh
      rw [hσD] at this
      rw [this]
      exact hhm
    obtain ⟨Y, hYD, -, hYp, -, hTY, hPC⟩ := lem67_first_advance S.C D (x[i][v].st).S.h_j
      (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le H) hH))
      (by rw [hDh']; exact Nat.lt_succ_self _)
    have hYT : Y ∈ (x[i][v].st).S.T := ancestors_mem_T_of_exec S Sched x i v D Y hD hYD
    -- the entry of the chain named by `Y`'s certificate, confirmed before slot `s'`
    obtain ⟨s_a, E, hcut, hAt, hEe, hEh, hEr⟩ := cert_entry_at_slot S Sched x s₀ H i v Y _ _ hDiv
      hMono hU (hAdvQ _) hOld hYT hPC hH
    -- the entry of the chain named by the certificate of `J`, confirmed before slot `s'`
    obtain ⟨⟨Dj, hDj, hJDj, hhjDj⟩, -, -⟩ := cachesWitnessed_of_exec S Sched x i v
    have hj1 : 1 ≤ (chainStateOf S.C Dj).h_j := by
      rw [← hhjDj]; exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le H) hH)
    obtain ⟨hJC, -, -⟩ := (lem66_chain_state_certified S.C Dj).1 hj1
    rw [← hJDj, ← hhjDj] at hJC
    obtain ⟨s_b, E', hcut', hAt', hEe', hEh', hEr'⟩ := cert_entry_at_slot S Sched x s₀ H i v Dj _ _
      hDiv hMono hU (hAdvQ _) hOld hDj (progressCertOn_of_justificationCertOn hJC) hH
    have hEE' : E = E' :=
      entry_eq_of_onHonestChainBefore S Sched x s₀ s' E E' hChain ⟨s_a, hs' s_a hcut, hAt⟩
        ⟨s_b, hs' s_b hcut', hAt'⟩ hEe hEe' (hEh.trans hEh'.symm)
    have hTmem : (chainStateOf S.C Y.parent).T_h ∈ (x[i][v].st).S.T :=
      ancestors_mem_T_of_exec S Sched x i v Y _ hYT hTY
    have hJmem : (x[i][v].st).S.J ∈ (x[i][v].st).S.T := hInv.2.2.2.2.2.2.2.2.2.1.2.2.2.2.1
    have hTJ : (chainStateOf S.C Y.parent).T_h = (x[i][v].st).S.J := by
      refine hInv.2.2.2.2.2.2.2.2.2.1.1 _ hTmem _ hJmem ?_
      rw [hEr, hEE', ← hEr']
    apply hJD
    have : (x[i][v].st).S.J.AncestorEq D := by
      rw [← hTJ]; exact ancestorEq_trans hTY hYD
    exact this
  exact ⟨hc, head_height_floor_of_not_contested _ hc⟩

/-- **Lemma 91 (d), no honest FG state is contested after healing.** The proof; the audited
statement is in `Statements/Executions/HealedFrameStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `i₁`: the
  step at the phase's end; `i`: the step; `s'`: the bound on the slot; `H`: the threshold; `v`:
  the validator.

It is `lem91d_not_contested_until` with the caches restricted to the steps it reads. -/
theorem lem91d_not_contested (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ i₁ i s' H : ℕ) (v : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hChain : ConfirmationsChainBefore S Sched x s₀ s')
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → u ∉ Sched.adv (x[j].time : Int) →
      CachesOnChain S Sched x s₀ H (x[j][u].st))
    (hi : x[i₁].time ≤ x[i].time) (hv : v ∉ Sched.adv (x[i].time : Int))
    (hs' : ∀ s_a : ℕ, supportCutoff S (s_a + 1) ≤ x[i].time → s_a < s') :
    fg_contest (x[i][v].st).S = false ∧
      head_height_floor (x[i][v].st).S = (x[i][v].st).S.h_max - 1 :=
  lem91d_not_contested_until S Sched x s₀ i₁ i s' H v hDiv hMono hU hAdvQ hChain hOld (fun j u h₁ _
    h₂ => hCaches j u h₁ h₂) hi hv hs'

/-! ## The root of the fork choice -/


/-! ## Lemma 91 (f) -/

/-- **Lemma 91 (f), the root of an honest fork choice is on the chain before `s'`.** The proof;
the audited statement is in `Statements/Executions/HealedFrameStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `i₁`: the
  step at the phase's end; `j`: the step; `s'`: the bound on the slot; `H`: the threshold; `w`:
  the validator.

Roots name blocks until `x[j].time`: the proof compares `w`'s justified block, held after `j`
steps, with the entry of the honest chain at a slot whose update ran by `x[j].time`
(`cert_entry_at_slot`).

Caches up to `x[j].time`: the proof reads `w`'s caches at step `j` only. -/
theorem lem91f_voter_root_on_chain_before_until (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ i₁ j s' H : ℕ) (w : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hRoots : RootsNameBlocksUntil S Sched x x[j].time) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (k : ℕ) (u : V), x[i₁].time ≤ x[k].time → x[k].time ≤ x[j].time →
      u ∉ Sched.adv (x[k].time : Int) → CachesOnChain S Sched x s₀ H (x[k][u].st))
    (hj : x[i₁].time ≤ x[j].time) (hw : w ∉ Sched.adv (x[j].time : Int))
    (hs' : ∀ s_a : ℕ, supportCutoff S (s_a + 1) ≤ x[j].time → s_a < s') :
    OnHonestChainBefore S Sched x s₀ s' (fg_to_ac (x[j][w].st).S).fc_root := by
  obtain ⟨⟨D, hD, hJD, hhjD⟩, -, -⟩ := cachesWitnessed_of_exec S Sched x j w
  obtain ⟨hH, -, -, -, hFJ⟩ := hCaches j w hj le_rfl hw
  have h1 : 1 ≤ (chainStateOf S.C D).h_j := by
    rw [← hhjD]; exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le H) hH)
  obtain ⟨hJC, -, -⟩ := (lem66_chain_state_certified S.C D).1 h1
  rw [← hJD, ← hhjD] at hJC
  obtain ⟨s_a, E, hcut, hAt, -, -, hEr⟩ := cert_entry_at_slot S Sched x s₀ H j w D _ _ hDiv
    hMono hU (hAdvQ _) hOld hD (progressCertOn_of_justificationCertOn hJC) hH
  -- the entry and `J` have one root, and honest validators hold both
  have hJmem : (x[j][w].st).S.J ∈ (x[j][w].st).S.T :=
    (lem11_node_invariant S Sched x j w).1.2.2.2.2.2.2.2.2.2.1.2.2.2.2.1
  have hEJ : E = (x[j][w].st).S.J :=
    hRoots E _ (onHonestChainAt_inHonestTreeBy S Sched x hMono s₀ s_a _ E hAt hcut)
      ⟨j, w, hw, le_rfl, hJmem⟩ hEr.symm
  have hJb : OnHonestChainBefore S Sched x s₀ s' (x[j][w].st).S.J := by
    rw [← hEJ]; exact ⟨s_a, hs' s_a hcut, hAt⟩
  rw [fc_root_eq]
  rcases get_fc_root_cases (x[j][w].st).S with h | h
  · rw [h]; exact hJb
  · rw [h]; exact onHonestChainBefore_of_ancestorEq S Sched x s₀ s' hJb hFJ

/-- **Lemma 91 (f), the root of an honest fork choice is on the chain before `s'`.** The proof;
the audited statement is in `Statements/Executions/HealedFrameStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `i₁`: the
  step at the phase's end; `j`: the step; `s'`: the bound on the slot; `H`: the threshold; `w`:
  the validator.

Roots name blocks until `x[j].time`: the proof compares `w`'s justified block, held after `j`
steps, with the entry of the honest chain at a slot whose update ran by `x[j].time`
(`cert_entry_at_slot`).

It is `lem91f_voter_root_on_chain_before_until` with the caches restricted to the steps it reads. -/
theorem lem91f_voter_root_on_chain_before (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ i₁ j s' H : ℕ) (w : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hRoots : RootsNameBlocksUntil S Sched x x[j].time) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → u ∉ Sched.adv (x[j].time : Int) →
      CachesOnChain S Sched x s₀ H (x[j][u].st))
    (hj : x[i₁].time ≤ x[j].time) (hw : w ∉ Sched.adv (x[j].time : Int))
    (hs' : ∀ s_a : ℕ, supportCutoff S (s_a + 1) ≤ x[j].time → s_a < s') :
    OnHonestChainBefore S Sched x s₀ s' (fg_to_ac (x[j][w].st).S).fc_root :=
  lem91f_voter_root_on_chain_before_until S Sched x s₀ i₁ j s' H w hDiv hMono hRoots hU hAdvQ hOld
    (fun k u h₁ _ h₂ => hCaches k u h₁ h₂) hj hw hs'

/-! ## Lemma 91 (b) -/

/-- **Lemma 91 (b), `head_height_floor` at the voter (the least chain-state height a viable block may have) is at most the proposal's parent's height.** The proof; the
audited statement is in `Statements/Executions/HealedFrameStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `s`: the
  slot; `i₁`: the step at the phase's end; `H`: the threshold; `p`: the proposer; `w`: the voter;
  `Q`: the block.

Caches up to `voteTime S s`: the proof reads `p`'s caches before the start of slot `s` and `w`'s
before the vote time of slot `s` (Lemma 91 (d) there). -/
theorem lem91b_voter_head_height_floor_le_parent_until (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ s i₁ H : ℕ) (p w : V) (Q : Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hs : x[i₁].time < slotStart S s)
    (hChain : ConfirmationsChainBefore S Sched x s₀ (s - 1))
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → x[j].time ≤ voteTime S s →
      u ∉ Sched.adv (x[j].time : Int) → CachesOnChain S Sched x s₀ H (x[j][u].st))
    (hp : p ∉ Sched.adv ((slotStart S s : ℕ) : Int))
    (hw : w ∉ Sched.adv ((voteTime S s : ℕ) : Int))
    (hParentChain : ∀ C : Block V, OnHonestChainBefore S Sched x s₀ (s - 1) C → C.AncestorEq Q)
    (hQ : (stateBefore x (slotStart S s) p).S.h_max - 1 ≤ (chainStateOf S.C Q).h) :
    head_height_floor (stateBefore x (voteTime S s) w).S ≤ (chainStateOf S.C Q).h := by
  have hΔ := one_le_Δ S
  have hvt := voteTime_eq S s
  -- the two reading steps
  obtain ⟨jp, hjp⟩ : ∃ jp, jp = stepBefore x (slotStart S s) := ⟨_, rfl⟩
  obtain ⟨jw, hjw⟩ : ∃ jw, jw = stepBefore x (voteTime S s) := ⟨_, rfl⟩
  have htp : x[jp].time + 1 = slotStart S s := by
    rw [hjp]; exact time_stepBefore_add_one x hDiv (by omega)
  have htw : x[jw].time + 1 = voteTime S s := by
    rw [hjw]; exact time_stepBefore_add_one x hDiv (by omega)
  have hstp : stateBefore x (slotStart S s) p = x[jp][p].st := by unfold stateBefore; rw [hjp]
  have hstw : stateBefore x (voteTime S s) w = x[jw][w].st := by unfold stateBefore; rw [hjw]
  have hpj : p ∉ Sched.adv (x[jp].time : Int) := fun h => hp (hMono _ _ (by omega) h)
  have hwj : w ∉ Sched.adv (x[jw].time : Int) := fun h => hw (hMono _ _ (by omega) h)
  have hip : x[i₁].time ≤ x[jp].time := by omega
  have hiw : x[i₁].time ≤ x[jw].time := by omega
  rw [hstp] at hQ
  rw [hstw, (lem91d_not_contested_until S Sched x s₀ i₁ jw (s - 1) H w hDiv hMono hU hAdvQ hChain
    hOld (fun j u h₁ h₂ h₃ => hCaches j u h₁ (by omega) h₃) hiw hwj (fun s_a h => by
      have := (slot_le_of_supportCutoff_lt S s_a s).1 (by omega)
      omega)).2]
  -- `H + 2 ≤ m`
  obtain ⟨hHp, -, -, -, -⟩ := hCaches jp p hip (by omega) hpj
  obtain ⟨⟨Dp, hDp, -, hhjDp⟩, -, -⟩ := cachesWitnessed_of_exec S Sched x jp p
  have hInvP := (lem11_node_invariant S Sched x jp p).1
  have hDpm : (chainStateOf S.C Dp).h ≤ (x[jp][p].st).S.h_max := by
    have := hInvP.2.2.2.2.2.2.2.2.2.1.2.1.2 Dp hDp
    rw [hInvP.2.2.2.2.2.1 Dp hDp] at this
    exact this
  have hjh := (lem47_chain_state_heights S.C Dp Dp).1.2.1
  have hm2 : H + 2 ≤ (x[jp][p].st).S.h_max := by
    rw [hhjDp] at hHp
    omega_nat
  by_cases hle : (x[jw][w].st).S.h_max ≤ (x[jp][p].st).S.h_max
  · omega_nat
  · -- a block of `w`'s tree at `h_max_w`, and the block that raised its chain past `h_max_w − 1`
    obtain ⟨-, ⟨Z, hZ, hZh⟩, -⟩ := cachesWitnessed_of_exec S Sched x jw w
    obtain ⟨Y, hYZ, -, -, -, -, hPC⟩ := lem67_first_advance S.C Z ((x[jw][w].st).S.h_max - 1)
      (by omega_nat) (by rw [hZh]; omega_nat)
    have hYT : Y ∈ (x[jw][w].st).S.T := ancestors_mem_T_of_exec S Sched x jw w Z Y hZ hYZ
    obtain ⟨s_a, E, hcut, hAt, -, hEh, -⟩ := cert_entry_at_slot S Sched x s₀ H jw w Y _ _ hDiv
      hMono hU (hAdvQ _) hOld hYT hPC (by omega_nat)
    have hsa := (slot_le_of_supportCutoff_lt S s_a s).1 (by omega)
    have hEQ := hParentChain E ⟨s_a, by omega, hAt⟩
    have := (lem47_chain_state_heights S.C E Q).2.2.2.1 hEQ
    rw [hEh] at this
    exact this

/-- **Lemma 91 (b), `head_height_floor` at the voter is at most the proposal's parent's height.** The proof; the
audited statement is in `Statements/Executions/HealedFrameStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `s`: the
  slot; `i₁`: the step at the phase's end; `H`: the threshold; `p`: the proposer; `w`: the voter;
  `Q`: the block.

It is `lem91b_voter_head_height_floor_le_parent_until`
with the caches restricted to the steps it reads. -/
theorem lem91b_voter_head_height_floor_le_parent (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ s i₁ H : ℕ) (p w : V) (Q : Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hs : x[i₁].time < slotStart S s)
    (hChain : ConfirmationsChainBefore S Sched x s₀ (s - 1))
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → u ∉ Sched.adv (x[j].time : Int) →
      CachesOnChain S Sched x s₀ H (x[j][u].st))
    (hp : p ∉ Sched.adv ((slotStart S s : ℕ) : Int))
    (hw : w ∉ Sched.adv ((voteTime S s : ℕ) : Int))
    (hParentChain : ∀ C : Block V, OnHonestChainBefore S Sched x s₀ (s - 1) C → C.AncestorEq Q)
    (hQ : (stateBefore x (slotStart S s) p).S.h_max - 1 ≤ (chainStateOf S.C Q).h) :
    head_height_floor (stateBefore x (voteTime S s) w).S ≤ (chainStateOf S.C Q).h :=
  lem91b_voter_head_height_floor_le_parent_until S Sched x s₀ s i₁ H p w Q hDiv hMono hU hAdvQ hs
    hChain hOld (fun j u h₁ _ h₂ => hCaches j u h₁ h₂) hp hw hParentChain hQ

/-! ## Lemma 91 (c) -/


/-- **Lemma 91 (c) over the proposer's reading time, on the chain before a slot.** The proof; its
audited statement is in `Statements/Executions/HealedFrameStatements.lean`. After the hand-over
step `i₁`, the `h_max` of a validator `p` honest at `t`, read before `t`, is at most the `h_max` of
a validator `w` awake and honest at every time from `t` to `t + Δ S`, read before `t + Δ S`, when
`GST ≤ t`, `1 ≤ t` and `x[i₁].time < t`, and the updaters' confirmations of the slots from `s₀` to
before `s'` form one chain, `s'` greater than every slot whose next slot's support cutoff is before
`t + Δ S`. It is the proof of Lemma 91 (c) with `slotStart S s` written `t` and `voteTime S s`
written `t + Δ S`: that proof reads of the slot only `GST ≤ slotStart S s` and
`1 ≤ slotStart S s`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `t`: the time `p`'s state is read before;
  `i₁`: the step at the phase's end; `H`: the threshold; `b`: the bound on the deadlines; `s'`:
  the bound on the slots of the chain; `p`: the proposer; `w`: the voter.

Restated with the delivery and roots premises up to `b`, the latest deadline being `t + Δ S`
(`p`'s block `Y` reaching `w` by `t + Δ S`; the blocks the proof compares are held by then).

On the chain before `s'`: the two blocks compared, the entry the certificate on `p`'s chain names
and `w`'s justified block, are on the chain at slots whose next slot's support cutoff is before
`t + Δ S` (Lemma 83 and `justified_onHonestChainAt_of_caches`, under the roots premise).

Caches up to `t + Δ S`: the proof reads `p`'s caches before `t` and `w`'s before `t + Δ S`. -/
theorem lem91c_at_until (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ t i₁ H b s' : ℕ) (p w : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject b)
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject b)
    (hRoots : RootsNameBlocksUntil S Sched x b)
    (hParent : ParentHeldAtDelivery S Sched x) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hGST : GST ≤ t) (ht1 : 1 ≤ t) (hi : x[i₁].time < t)
    (hChain : ConfirmationsChainBefore S Sched x s₀ s')
    -- every slot whose next slot's support cutoff is before `t + Δ S` is less than `s'`
    (hs' : ∀ s_a : ℕ, supportCutoff S (s_a + 1) < t + Δ S → s_a < s')
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → x[j].time ≤ t + Δ S →
      u ∉ Sched.adv (x[j].time : Int) → CachesOnChain S Sched x s₀ H (x[j][u].st))
    (hp : p ∉ Sched.adv (t : Int))
    (hw : ∀ t' : ℕ, t ≤ t' → t' ≤ t + Δ S →
      w ∈ Sched.awake (t' : Int) ∧ w ∉ Sched.adv (t' : Int))
    -- the latest deadline the proof reads is at most the bound
    (hb : t + Δ S ≤ b) :
    (stateBefore x t p).S.h_max ≤ (stateBefore x (t + Δ S) w).S.h_max := by
  have hΔ := one_le_Δ S
  obtain ⟨jp, hjp⟩ : ∃ jp, jp = stepBefore x t := ⟨_, rfl⟩
  obtain ⟨jw, hjw⟩ : ∃ jw, jw = stepBefore x (t + Δ S) := ⟨_, rfl⟩
  have htp : x[jp].time + 1 = t := by
    rw [hjp]; exact time_stepBefore_add_one x hDiv (by omega)
  have htw : x[jw].time + 1 = t + Δ S := by
    rw [hjw]; exact time_stepBefore_add_one x hDiv (by omega)
  have hstp : stateBefore x t p = x[jp][p].st := by unfold stateBefore; rw [hjp]
  have hstw : stateBefore x (t + Δ S) w = x[jw][w].st := by unfold stateBefore; rw [hjw]
  have hpj : p ∉ Sched.adv (x[jp].time : Int) := fun h => hp (hMono _ _ (by omega) h)
  have hwv := (hw (t + Δ S) (by omega) le_rfl).2
  have hwj : w ∉ Sched.adv (x[jw].time : Int) := fun h => hwv (hMono _ _ (by omega) h)
  have hip : x[i₁].time ≤ x[jp].time := by omega
  have hiw : x[i₁].time ≤ x[jw].time := by omega
  -- `p`'s block at `m`, and `H + 2 ≤ m`
  obtain ⟨hHp, -, -, -, -⟩ := hCaches jp p hip (by omega) hpj
  obtain ⟨⟨Dp, hDp, -, hhjDp⟩, ⟨Y, hY, hYh⟩, -⟩ := cachesWitnessed_of_exec S Sched x jp p
  have hInvP := (lem11_node_invariant S Sched x jp p).1
  have hDpm : (chainStateOf S.C Dp).h ≤ (x[jp][p].st).S.h_max := by
    have := hInvP.2.2.2.2.2.2.2.2.2.1.2.1.2 Dp hDp
    rw [hInvP.2.2.2.2.2.1 Dp hDp] at this
    exact this
  have hjh := (lem47_chain_state_heights S.C Dp Dp).1.2.1
  have hm2 : H + 2 ≤ (x[jp][p].st).S.h_max := by
    rw [hhjDp] at hHp
    omega_nat
  -- the entry of the chain at `m − 1`, an ancestor of `Y`
  obtain ⟨Y₁, hY₁Y, -, -, -, hTY₁, hPC⟩ := lem67_first_advance S.C Y
    ((x[jp][p].st).S.h_max - 1) (by omega_nat) (by rw [hYh]; omega_nat)
  have hY₁T : Y₁ ∈ (x[jp][p].st).S.T := ancestors_mem_T_of_exec S Sched x jp p Y Y₁ hY hY₁Y
  obtain ⟨s_a, E, hcut, hAt, hEe, hEh, hEr⟩ := cert_entry_at_slot S Sched x s₀ H jp p Y₁ _ _
    hDiv hMono hU (hAdvQ _) hOld hY₁T hPC (by omega_nat)
  have hTT : (chainStateOf S.C Y₁.parent).T_h ∈ (x[jp][p].st).S.T :=
    ancestors_mem_T_of_exec S Sched x jp p Y₁ _ hY₁T hTY₁
  have hTE : (chainStateOf S.C Y₁.parent).T_h = E :=
    hRoots _ _ ⟨jp, p, hpj, by omega, hTT⟩
      (onHonestChainAt_inHonestTreeBy S Sched x hMono s₀ s_a _ E hAt (by omega)) hEr
  have hEY : E.AncestorEq Y := by rw [← hTE]; exact ancestorEq_trans hTY₁ hY₁Y
  -- `w`'s justified block
  obtain ⟨hHw, -, hJe, hJh, hFJ⟩ := hCaches jw w hiw (by omega) hwj
  obtain ⟨s_b, hcutb, hJat⟩ := justified_onHonestChainAt_of_caches S Sched x s₀
    (supportCutoff S (s₀ + 1)) H jw w hU hMono (hRoots.mono (by omega)) hAdvQ
    (lem82_honest_attestations_on_chain S Sched x s₀ hDiv hMono) hOld hwj hHw
  have hJchain : OnHonestChainBefore S Sched x s₀ s' (x[jw][w].st).S.J :=
    ⟨s_b, hs' s_b (by omega), hJat⟩
  have hEb : OnHonestChainBefore S Sched x s₀ s' E := ⟨s_a, hs' s_a (by omega), hAt⟩
  have hInvW := (lem11_node_invariant S Sched x jw w).1
  have hHCB : ∀ D ∈ (x[jw][w].st).S.T, (chainStateOf S.C D).h ≤ (x[jw][w].st).S.h_max := by
    intro D hD
    have := hInvW.2.2.2.2.2.2.2.2.2.1.2.1.2 D hD
    rw [hInvW.2.2.2.2.2.1 D hD] at this
    exact this
  rw [hstp, hstw]
  have key : (x[jw][w].st).S.J.AncestorEq E ∨
      (x[jp][p].st).S.h_max ≤ (chainStateOf S.C (x[jw][w].st).S.J).h := by
    rcases (compatible_iff _ _).1 (onHonestChainBefore_compatible S Sched x s₀ s' _ E hChain hJchain
      hEb) with h | h
    · exact Or.inl h
    · have hle := (lem47_chain_state_heights S.C E _).2.2.2.1 h
      by_cases heq : (chainStateOf S.C (x[jw][w].st).S.J).h = (chainStateOf S.C E).h
      · left
        rw [entry_eq_of_onHonestChainBefore S Sched x s₀ s' _ E hChain hJchain hEb hJe hEe heq]
        exact ancestorEq_refl E
      · right
        rw [hEh] at hle heq
        omega_nat
  rcases key with hJE | hm
  · -- `Y` reaches `w` by the vote time
    have hFY : (x[jw][w].st).S.F.AncestorEq Y := ancestorEq_trans hFJ (ancestorEq_trans hJE hEY)
    have hYp : Y ∈ (stateBefore x t p).S.T := by rw [hstp]; exact hY
    have hYw := mem_T_before_add_delay_upTo hDiv hMono (SynchronyFromWakeUpTo.mono hb hSync)
      (CatchUpOnWakeUpTo.mono hb hCatch) (hRoots.mono hb) hParent
      (t := t) (u := p) (w := w) ht1 hGST hp hYp hw
      (by rw [hstw]; exact (compatible_iff _ _).2 (Or.inl hFY))
    rw [hstw] at hYw
    rw [← hYh]
    exact hHCB Y hYw
  · exact le_trans hm (hHCB _ hInvW.2.2.2.2.2.2.2.2.2.1.2.2.2.2.1)

/-- **Lemma 91 (c) over the proposer's reading time.** The proof; its audited statement is to
land in `Statements/Executions/HealedFrameStatements.lean`. After the
hand-over step `i₁`, the `h_max` of a validator `p` honest at `t`, read before `t`, is at most the
`h_max` of a validator `w` awake and honest at every time from `t` to `t + Δ S`, read before
`t + Δ S`, when `GST ≤ t`, `1 ≤ t` and `x[i₁].time < t`. It is the proof of Lemma 91 (c) with
`slotStart S s` written `t` and `voteTime S s` written `t + Δ S`: that proof reads of the slot
only `GST ≤ slotStart S s` and `1 ≤ slotStart S s`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `t`: the time `p`'s state is read before;
  `i₁`: the step at the phase's end; `H`: the threshold; `b`: the bound on the deadlines;
  `p`: the proposer; `w`: the voter.

Restated with the delivery and roots premises up to `b`, the latest deadline being `t + Δ S`
(`p`'s block `Y` reaching `w` by `t + Δ S`; the blocks the proof compares are held by then).

It is `lem91c_at_until` with the caches restricted to the steps it reads, on the chain before
`t + Δ S` (`lt_supportCutoff_succ`). -/
theorem lem91c_at (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ t i₁ H b : ℕ) (p w : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject b)
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject b)
    (hRoots : RootsNameBlocksUntil S Sched x b)
    (hParent : ParentHeldAtDelivery S Sched x) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hGST : GST ≤ t) (ht1 : 1 ≤ t) (hi : x[i₁].time < t)
    (hChain : ConfirmationsChain S Sched x s₀)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → u ∉ Sched.adv (x[j].time : Int) →
      CachesOnChain S Sched x s₀ H (x[j][u].st))
    (hp : p ∉ Sched.adv (t : Int))
    (hw : ∀ t' : ℕ, t ≤ t' → t' ≤ t + Δ S →
      w ∈ Sched.awake (t' : Int) ∧ w ∉ Sched.adv (t' : Int))
    -- the latest deadline the proof reads is at most the bound
    (hb : t + Δ S ≤ b) :
    (stateBefore x t p).S.h_max ≤ (stateBefore x (t + Δ S) w).S.h_max :=
  lem91c_at_until S Sched x GST s₀ t i₁ H b (t + Δ S) p w hDiv hMono hSync hCatch hRoots
    hParent hU hAdvQ hGST ht1 hi (confirmationsChainBefore_of_chain S Sched x s₀ _ hChain)
    (fun s_a h => lt_trans (lt_supportCutoff_succ S s_a) h) hOld
    (fun j u h₁ _ h₂ => hCaches j u h₁ h₂) hp hw hb

/-- **Lemma 91 (c), the voter is at least as far as the proposer.** The proof; the audited
statement is in `Statements/Executions/HealedFrameStatements.lean`. It is the instance of
`lem91c_at` at `t := slotStart S s`, `b := voteTime S s`: the slot comes after the healed slot's
support cutoff, so `GST ≤ slotStart S s` and `1 ≤ slotStart S s` (`slot_after_healed_round`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `s`: the slot; `i₁`: the step at the phase's end;
  `H`: the threshold; `p`: the proposer; `w`: the voter.

Roots name blocks until `voteTime S s`: `lem91c_at`, which the proof calls with
`b := voteTime S s`, takes blocks as held up to that time (`p`'s block reaching `w` by the vote
time; the entry `cert_entry_at_slot` returns, held by the support cutoff of its slot, a time
before `slotStart S s`).

Caches up to `voteTime S s`: `lem91c_at_until` at `t := slotStart S s`, whose `t + Δ S` is the vote
time of slot `s`.

On the chain before `s − 1`: the blocks `lem91c_at_until` compares are on the chain at slots whose
next slot's support cutoff is before the vote time of slot `s`, so less than `s − 1`. -/
theorem lem91c_proposer_h_max_le_voter_h_max_until (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ s i₁ H : ℕ) (p w : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (voteTime S s))
    (hParent : ParentHeldAtDelivery S Sched x) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hGST : GST ≤ voteTime S s₀) (ht₀ : supportCutoff S (s₀ + 1) ≤ x[i₁].time)
    (hs : x[i₁].time < slotStart S s)
    (hChain : ConfirmationsChainBefore S Sched x s₀ (s - 1))
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → x[j].time ≤ voteTime S s →
      u ∉ Sched.adv (x[j].time : Int) → CachesOnChain S Sched x s₀ H (x[j][u].st))
    (hp : p ∉ Sched.adv ((slotStart S s : ℕ) : Int))
    (hw : ∀ t' : ℕ, slotStart S s ≤ t' → t' ≤ voteTime S s →
      w ∈ Sched.awake (t' : Int) ∧ w ∉ Sched.adv (t' : Int)) :
    (stateBefore x (slotStart S s) p).S.h_max ≤ (stateBefore x (voteTime S s) w).S.h_max := by
  obtain ⟨-, hvs, h1s⟩ := slot_after_healed_round S s₀ s (lt_of_le_of_lt ht₀ hs)
  rw [voteTime_eq S s] at hw hRoots hCaches ⊢
  exact lem91c_at_until S Sched x GST s₀ (slotStart S s) i₁ H (slotStart S s + Δ S) (s - 1) p w
    hDiv hMono (synchronyFromWakeUpTo_of_synchronyFromWake _ hSync)
    (catchUpOnWakeUpTo_of_catchUpOnWake _ hCatch) hRoots hParent hU hAdvQ (by omega) h1s
    hs hChain (fun s_a h => by
      have := (slot_le_of_supportCutoff_lt S s_a s).1 (by rw [voteTime_eq]; exact h)
      omega) hOld hCaches hp hw le_rfl

/-- **Lemma 91 (c), the voter is at least as far as the proposer.** The proof; the audited
statement is in `Statements/Executions/HealedFrameStatements.lean`. It is the instance of
`lem91c_at` at `t := slotStart S s`, `b := voteTime S s`: the slot comes after the healed slot's
support cutoff, so `GST ≤ slotStart S s` and `1 ≤ slotStart S s` (`slot_after_healed_round`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `s`: the slot; `i₁`: the step at the phase's end;
  `H`: the threshold; `p`: the proposer; `w`: the voter.

Roots name blocks until `voteTime S s`: `lem91c_at`, which the proof calls with
`b := voteTime S s`, takes blocks as held up to that time (`p`'s block reaching `w` by the vote
time; the entry `cert_entry_at_slot` returns, held by the support cutoff of its slot, a time
before `slotStart S s`).

It is `lem91c_proposer_h_max_le_voter_h_max_until`
with the caches restricted to the steps it reads, on the chain before `s − 1`. -/
theorem lem91c_proposer_h_max_le_voter_h_max (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ s i₁ H : ℕ) (p w : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (voteTime S s))
    (hParent : ParentHeldAtDelivery S Sched x) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hGST : GST ≤ voteTime S s₀) (ht₀ : supportCutoff S (s₀ + 1) ≤ x[i₁].time)
    (hs : x[i₁].time < slotStart S s)
    (hChain : ConfirmationsChain S Sched x s₀)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → u ∉ Sched.adv (x[j].time : Int) →
      CachesOnChain S Sched x s₀ H (x[j][u].st))
    (hp : p ∉ Sched.adv ((slotStart S s : ℕ) : Int))
    (hw : ∀ t' : ℕ, slotStart S s ≤ t' → t' ≤ voteTime S s →
      w ∈ Sched.awake (t' : Int) ∧ w ∉ Sched.adv (t' : Int)) :
    (stateBefore x (slotStart S s) p).S.h_max ≤ (stateBefore x (voteTime S s) w).S.h_max :=
  lem91c_proposer_h_max_le_voter_h_max_until S Sched x GST s₀ s i₁ H p w hDiv hMono hSync hCatch
    hRoots hParent hU hAdvQ hGST ht₀ hs
    (confirmationsChainBefore_of_chain S Sched x s₀ _ hChain) hOld
    (fun j u h₁ _ h₂ => hCaches j u h₁ h₂) hp hw

/-! ## Lemma 91 (e) -/

/-- **Lemma 91 (e), the honest proposal reaches the proposer's `h_max`.** The proof; the audited
statement is in `Statements/Executions/HealedFrameStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `s`: the
  slot; `i₁`: the step at the phase's end; `H`: the threshold; `p`: the proposer; `B`: the
  proposal.

Roots name blocks until `slotStart S s`: the proof compares a block `p` holds before
`slotStart S s` (the entry `T_h` of a chain state on `p`'s chain) with the entry of the honest
chain at a slot whose update ran by then (`cert_entry_at_slot`).

Caches up to `slotStart S s`: the proof reads `p`'s caches before the start of slot `s` (Lemma 91
(d) there). -/
theorem lem91e_proposal_height_ge_h_max_until (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ s i₁ H : ℕ) (p : V) (B : Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hRoots : RootsNameBlocksUntil S Sched x (slotStart S s)) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hs : x[i₁].time < slotStart S s)
    (hChain : ConfirmationsChainBefore S Sched x s₀ (s - 1))
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → x[j].time ≤ slotStart S s →
      u ∉ Sched.adv (x[j].time : Int) → CachesOnChain S Sched x s₀ H (x[j][u].st))
    (hp : p ∉ Sched.adv ((slotStart S s : ℕ) : Int))
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    (hParentHeightP : head_height_floor (stateBefore x (slotStart S s) p).S ≤
      (chainStateOf S.C B.parent).h)
    (hParentChain : ∀ C : Block V, OnHonestChainBefore S Sched x s₀ (s - 1) C →
      C.AncestorEq B.parent) :
    (stateBefore x (slotStart S s) p).S.h_max ≤ (chainStateOf S.C B).h := by
  have hΔ := one_le_Δ S
  have hvt := voteTime_eq S s
  have h1s : 1 ≤ s := by
    by_contra h0
    have : s = 0 := by omega
    rw [this, slotStart_eq, Nat.mul_zero] at hs
    omega
  obtain ⟨jp, hjp⟩ : ∃ jp, jp = stepBefore x (slotStart S s) := ⟨_, rfl⟩
  have h1t : 1 ≤ slotStart S s := by omega
  have htp : x[jp].time + 1 = slotStart S s := by
    rw [hjp]; exact time_stepBefore_add_one x hDiv h1t
  have hstp : stateBefore x (slotStart S s) p = x[jp][p].st := by unfold stateBefore; rw [hjp]
  have hpj : p ∉ Sched.adv (x[jp].time : Int) := fun h => hp (hMono _ _ (by omega) h)
  have hip : x[i₁].time ≤ x[jp].time := by omega
  -- the proposal's slot and parent
  obtain ⟨ip, hl, hsent⟩ := hPropose
  have hss : s = s - 1 + 1 := by omega
  rw [hss] at hl
  obtain ⟨hBslot, -, hBpar?, -⟩ := proposal_parent_walk_end S Sched x (s - 1) ip B p hl hsent
  rw [← hss] at hBslot hl
  have hPB : B.parent.AncestorEq B := ancestorEq_of_parent? hBpar?
  -- `p`'s block at `m`, and `H + 2 ≤ m`
  obtain ⟨hHp, -, -, -, -⟩ := hCaches jp p hip (by omega) hpj
  obtain ⟨⟨Dp, hDp, -, hhjDp⟩, ⟨Y, hY, hYh⟩, -⟩ := cachesWitnessed_of_exec S Sched x jp p
  have hInvP := (lem11_node_invariant S Sched x jp p).1
  have hDpm : (chainStateOf S.C Dp).h ≤ (x[jp][p].st).S.h_max := by
    have := hInvP.2.2.2.2.2.2.2.2.2.1.2.1.2 Dp hDp
    rw [hInvP.2.2.2.2.2.1 Dp hDp] at this
    exact this
  have hjh := (lem47_chain_state_heights S.C Dp Dp).1.2.1
  have hm2 : H + 2 ≤ (x[jp][p].st).S.h_max := by
    rw [hhjDp] at hHp
    omega_nat
  rw [hstp] at hParentHeightP ⊢
  -- the block that raised `Y`'s chain past `m − 1`, and the branch
  obtain ⟨Y₁, hY₁Y, -, hY₁p, -, hTY₁, hPC, hbranch⟩ := lem67b_first_advance_cases S.C Y
    ((x[jp][p].st).S.h_max - 1) (by omega_nat) (by rw [hYh]; omega_nat)
  have hY₁T : Y₁ ∈ (x[jp][p].st).S.T := ancestors_mem_T_of_exec S Sched x jp p Y Y₁ hY hY₁Y
  obtain ⟨s_a, E, hcut, hAt, hEe, hEh, hEr⟩ := cert_entry_at_slot S Sched x s₀ H jp p Y₁ _ _ hDiv
    hMono hU (hAdvQ _) hOld hY₁T hPC (by omega_nat)
  have hTT : (chainStateOf S.C Y₁.parent).T_h ∈ (x[jp][p].st).S.T :=
    ancestors_mem_T_of_exec S Sched x jp p Y₁ _ hY₁T hTY₁
  have hTE : (chainStateOf S.C Y₁.parent).T_h = E :=
    hRoots _ _ ⟨jp, p, hpj, by omega, hTT⟩
      (onHonestChainAt_inHonestTreeBy S Sched x hMono s₀ s_a _ E hAt (by omega)) hEr
  have hsa := (slot_le_of_supportCutoff_lt S s_a s).1 (by omega)
  have hEP : E.AncestorEq B.parent := hParentChain E ⟨s_a, by omega, hAt⟩
  by_cases hm : (x[jp][p].st).S.h_max ≤ (chainStateOf S.C B.parent).h
  · exact le_trans hm ((lem47_chain_state_heights S.C B.parent B).2.2.2.1 hPB)
  -- the parent is at `m − 1`, with `E` the entry of its height
  rw [(lem91d_not_contested_until S Sched x s₀ i₁ jp (s - 1) H p hDiv hMono hU hAdvQ hChain hOld
    (fun j u h₁ h₂ h₃ => hCaches j u h₁ (by omega) h₃)
    hip hpj (fun s_a h => by
      have := (slot_le_of_supportCutoff_lt S s_a s).1 (by omega)
      omega)).2] at hParentHeightP
  have hEPh : (chainStateOf S.C E).h = (chainStateOf S.C B.parent).h := by
    rw [hEh]; omega_nat
  have hTP : (chainStateOf S.C B.parent).T_h = E := by
    have := (lem47_chain_state_heights S.C E B.parent).2.2.2.2 hEP hEPh
    unfold IsEntry at hEe
    rw [← this, hEe]
  have hpool : ∀ a : Attestation V, on_chain a Y₁ = true →
      a ∈ (stateBefore x (slotStart S s) p).S.attestations := by
    intro a ha
    rw [hstp]
    exact pool_holds_chain_attestations S Sched x jp p Y₁ a hY₁T ha
  have hProp : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent :=
    ⟨ip, hl, hsent⟩
  rcases hbranch with hJust | hTime
  · obtain ⟨A, hA, hAv⟩ := hJust
    have hpoolA : ∀ u ∈ A, ∃ a ∈ (stateBefore x (slotStart S s) p).S.attestations,
        a.val_index = u ∧ a.h = (chainStateOf S.C B.parent).h ∧
        a.T = (chainStateOf S.C B.parent).T_h.root ∧ a.τ = false := by
      intro u hu
      obtain ⟨a, h1, h2, h3, h4, h5⟩ := hAv u hu
      refine ⟨a, hpool a h5, h1, ?_, ?_, h4⟩
      · rw [h2]; omega_nat
      · rw [h3, hTE, hTP]
    have h53 := lem53_next_honest_proposal_carries_certificate S Sched x s p B B.parent A hProp rfl
      hA (fun u hu => by
        obtain ⟨a, h1, h2, h3, h4, -⟩ := hpoolA u hu
        exact ⟨a, h1, h2, h3, h4⟩)
    have := (h53.2 hpoolA).1
    rw [this]
    omega_nat
  · obtain ⟨A, hA, hAv⟩ := hPC
    have h53 := lem53_next_honest_proposal_carries_certificate S Sched x s p B B.parent A hProp rfl
      hA (fun u hu => by
        obtain ⟨a, h1, h2, h3, h5⟩ := hAv u hu
        refine ⟨a, hpool a h5, h1, ?_, ?_⟩
        · rw [h2]; omega_nat
        · rw [h3, hTE, hTP])
    rcases h53.1 with h | ⟨-, -, hslotB⟩
    · rw [h]; omega_nat
    · exfalso
      have hY₁s : Y₁.slot ≤ s := by
        have hY₁b : Y₁ ∈ (stateBefore x (slotStart S s) p).S.T := by rw [hstp]; exact hY₁T
        have := slot_le_of_mem_T_before hDiv hMono hY₁b
        rw [slot_eq_of_mem S le_rfl (by rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]; omega)] at this
        exact this
      rw [hTP, hBslot] at hslotB
      rw [hTE] at hTime
      omega_nat

/-- **Lemma 91 (e), the honest proposal reaches the proposer's `h_max`.** The proof; the audited
statement is in `Statements/Executions/HealedFrameStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `s`: the
  slot; `i₁`: the step at the phase's end; `H`: the threshold; `p`: the proposer; `B`: the
  proposal.

Roots name blocks until `slotStart S s`: the proof compares a block `p` holds before
`slotStart S s` (the entry `T_h` of a chain state on `p`'s chain) with the entry of the honest
chain at a slot whose update ran by then (`cert_entry_at_slot`).

It is `lem91e_proposal_height_ge_h_max_until` with the caches restricted to the steps it reads. -/
theorem lem91e_proposal_height_ge_h_max (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ s i₁ H : ℕ) (p : V) (B : Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hRoots : RootsNameBlocksUntil S Sched x (slotStart S s)) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hs : x[i₁].time < slotStart S s)
    (hChain : ConfirmationsChainBefore S Sched x s₀ (s - 1))
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → u ∉ Sched.adv (x[j].time : Int) →
      CachesOnChain S Sched x s₀ H (x[j][u].st))
    (hp : p ∉ Sched.adv ((slotStart S s : ℕ) : Int))
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    (hParentHeightP : head_height_floor (stateBefore x (slotStart S s) p).S ≤
      (chainStateOf S.C B.parent).h)
    (hParentChain : ∀ C : Block V, OnHonestChainBefore S Sched x s₀ (s - 1) C →
      C.AncestorEq B.parent) :
    (stateBefore x (slotStart S s) p).S.h_max ≤ (chainStateOf S.C B).h :=
  lem91e_proposal_height_ge_h_max_until S Sched x s₀ s i₁ H p B hDiv hMono hRoots hU hAdvQ hs
    hChain hOld (fun j u h₁ _ h₂ => hCaches j u h₁ h₂) hp hPropose hParentHeightP hParentChain

end GoldilocksCorrectness.Proofs.Executions
