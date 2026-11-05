module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89FastFamily
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.ProposalWalk
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.RoundBase
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89r
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89Stability
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89QuietJ
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.HealedRoundRows
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.FGStateReaders
public import GoldilocksCorrectness.Proofs.Executions.Lemma89FastFamily
public import GoldilocksCorrectness.Proofs.Executions.ProposalWalk
public import GoldilocksCorrectness.Proofs.Executions.RoundBase
public import GoldilocksCorrectness.Proofs.Executions.Lemma89r
public import GoldilocksCorrectness.Proofs.Executions.Lemma89Stability
public import GoldilocksCorrectness.Proofs.Executions.Lemma89QuietJ
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma89HealedRound, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma89HealedRound.lean`, over a model `M`
whose facts `F` hold, for an execution `x` of `protocolOf M S`: part C of Lemma 89 on the
fast-confirmation route, the healed round, namely the readers of the bundle `PartAHyps` that place
the line sources at a round's first slot, the round base at an honest round opening slot after the
fast block (C1), Lemma 89's base facts at a round whose base holds (C3), and every honest round
opening slot after the fast block quiet relative to its own confirmations (C2). The page's
routine-level theorems are the facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff viewFreeze
  dutyWindowStart anchorCW)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_le_voteTime dutyWindowStart_of_anchor
  dutyWindowStart_succ_le_slotStart round_slot_le_of_lt slotStart_mono supportCutoff_lt
  supportCutoff_mono times_eq)

open GoldilocksCorrectness.Proofs.Routines (earlySupporterOf_of_keepsVotes expireLocks_keepsVotes)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax IsEntry VoterTreeAt JustifiedInTree AnchorAt)
open GoldilocksCorrectness.Record.Statements.Routines (ProgressCertOn ConfirmationUpdated)

open GoldilocksCorrectness.Record.Statements.Routines (CountedVotes)

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
open GoldilocksCorrectness.Statements.Routines (expireLocks RootsNameBlocksIn)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans ancestorEq_compatible
  ancestorEq_antisymm compatible_iff compatible_of_ancestorEq_compatible ancestorEq_of_parent?)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

open GoldilocksCorrectness.Proofs.Routines (tick_attest_awake awakeSince_of_record_awake
  create_attestation_cases)

/-- **`cert_source_core_fast` with the attester honest up to the phase's end, named as the line source's updater.**
A progress certificate at a height `h > H₂` on the chain of a block `w` holds after `j` steps, within the phase, names
the root of an entry block `E` at the height `h` that is a line source of the first slot of a round `r' ≥ r`, made a
line source by the update an honest validator `u` ran at its tick `k` to `aR M S r'`, a step before `j`; this `u` is
outside the adversary set at `tAwakeEnd`, and `E` is on the chain of the confirmation of slot `r' * R` that `u`'s tick
to `aR M S r'` saved.

Why: `cert_source_core_fast`'s proof, with the certificate's honest member `u` chosen against `hThird` up to
`tAwakeEnd` in place of the later of `x.time j` and `aR M S r` (both are at most `tAwakeEnd`); the line source it
builds is `u`'s own update.

The variables: as `cert_source_core_fast`'s.

Read aloud: a certificate above `H₂` names the entry of a line source of a round's first slot, made by the update of
an attester honest up to the phase's end, on the chain of the confirmation that attester's tick saved. -/
theorem cert_source_core_fast_attester {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N}
    (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) {tGAT tAwakeEnd r H₂ : ℕ} {v : V}
    (hRoots : RootsNameBlocksUntil M A x tAwakeEnd)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hAnchor : anchorCW S tGAT ≤ M.slotStart S.C (r * S.C.R + 1))
    (hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂)
    (hEnd : aR M S r ≤ tAwakeEnd)
    (hk₀ : x.lbl (x.tickStep v (aR M S r)) = Event.tick v (aR M S r))
    (hOldStep : ∀ (k t : ℕ) (u : V) (a' : Attestation V), k < x.firstAt (M.supportCutoff S.C (r * S.C.R)) →
      x.lbl k = Event.tick u t → u ∉ A.corruptedAtTime x tAwakeEnd →
      (⟨u, NamedObject.attest a'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (k + 1) - x.sent k → a'.h ≤ H₂)
    (hEndStep : x.time (x.tickStep v (aR M S r)) ≤ tAwakeEnd)
    {j : ℕ} {w : V} {Y T : Block V} {h : Height} (hj : x.time j ≤ tAwakeEnd)
    (hY : Y ∈ (x.st j w).tree) (hJ : ProgressCertOn M Y h T) (hH : H₂ < h) :
    ∃ (r' : ℕ) (E : Block V) (u : V) (k : ℕ), r ≤ r' ∧ x.lbl k = Event.tick u (aR M S r') ∧ k < j ∧
      u ∈ A.active k ∧ LineSource M S A x r H₂ (r' * S.C.R) E ∧ IsEntry M S.C E ∧
      (M.chainStateOf S.C E).h = h ∧ T.root = E.root ∧
      u ∉ A.corruptedAtTime x tAwakeEnd ∧ ∃ C₀ : Block V,
        M.savedConfirmation (x.tickOutput u (M.supportCutoff S.C (r' * S.C.R + 1))) (r' * S.C.R) = some C₀ ∧
        E.AncestorEq C₀ := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ := GoldilocksCorrectness.Proofs.Routines.one_le_Δ S
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  -- the adversary bound up to `tAwakeEnd` (the twin: the attester is chosen honest up to the phase's end)
  have hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (tAwakeEnd : ℝ) :=
    fun X hX => by
      have h1 := hThird X hX
      have h2 := (GoldilocksCorrectness.Statements.Routines.lem65b_quorum_threshold (V := V)).2
      omega
  obtain ⟨X₁, hX₁Y, Q, hqA, hQ⟩ := hJ
  rw [GoldilocksCorrectness.Record.quorumAt_eq_quorum Fx F.sched X₁] at hqA
  obtain ⟨u, hu, hhonE⟩ : ∃ u ∈ Q, A.HonestThroughTime x (tAwakeEnd : ℝ) u := by
    by_contra hno
    have hall : ∀ v ∈ Q, ∃ i : ℕ, x.time i ≤ (tAwakeEnd : ℝ) ∧ v ∈ A.corrupted i := by
      intro v hv
      by_contra hn
      exact hno ⟨v, hv, fun i hi ha => hn ⟨i, hi, ha⟩⟩
    have h3 := hAdvQ Q hall
    omega
  have hmaxE : max (x.time j) (aR M S r) ≤ (tAwakeEnd : ℝ) := max_le hj (by exact_mod_cast hEnd)
  have hhonM : A.HonestThroughTime x (max (x.time j) (aR M S r)) u := fun i hi => hhonE i (le_trans hi hmaxE)
  have huE : u ∉ A.corruptedAtTime x tAwakeEnd := Activity.not_mem_corruptedAtTime.2 fun i hi => hhonE i hi
  have hhonT : ∀ t'' : ℕ, t'' ≤ max (x.time j) (aR M S r) → u ∉ A.corruptedAtTime x t'' :=
    fun t'' ht'' => Activity.not_mem_corruptedAtTime.2 fun i hi => hhonM i (le_trans hi ht'')
  have hhon : x.HonestThrough A j u :=
    fun i'' hi'' => hhonM i'' (le_trans ((time_mono M) x R hi'') (le_max_left _ _))
  have huR : u ∉ A.corruptedAtTime x (aR M S r) := hhonT _ (le_max_right _ _)
  obtain ⟨a, hau, hah, haT, hon⟩ := hQ u hu
  have hrec := (GoldilocksCorrectness.Record.Proofs.Executions.lem74_honest_attestations_recorded M F) S A x R E j w Y a hY
    ((GoldilocksCorrectness.Record.Proofs.Routines.on_chain_mono M F) a hX₁Y hon)
    (by rw [hau]; exact hhon)
  rw [hau] at hrec
  obtain ⟨j', t', a', hj', hl, hact', hsent, -, hcont, -⟩ :=
    (GoldilocksCorrectness.Record.Proofs.Executions.record_content_sent_step M F) S A x R E u j _ hrec
  have hh' : a'.h = h := by
    rw [← hah]
    exact congrArg AttestationContent.h hcont
  have hT' : a'.T = T.root := by
    rw [← haT]
    exact congrArg AttestationContent.T hcont
  have hge : aR M S r ≤ t' := by
    by_contra hlt
    have hle := hOld j' t' u a' hl (by exact_mod_cast Nat.lt_of_not_le hlt) huR hsent
    rw [hh'] at hle
    exact absurd hle (Nat.not_le.mpr hH)
  obtain ⟨r', rfl⟩ := (attest_time_round M F U) S A x R E hl hsent
  have hrr : r ≤ r' := by
    by_contra hlt
    have : r' * S.C.R + 1 < r * S.C.R + 1 := by
      have := Nat.mul_lt_mul_of_pos_right (Nat.lt_of_not_le hlt)
        (show 0 < S.C.R by have := S.C.R_ge_two; omega)
      omega
    have := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_lt M.toSlotLayout F.sched) S this
    exact absurd hge (Nat.not_le.mpr this)
  obtain ⟨n₀, X, hU, hXf, hXT, hXh, hXT'⟩ :=
    (fast_source_of_attestation M F U) S A x R E r' u a' ⟨j', hl, hsent⟩
  obtain ⟨hE1, hE2, hE3⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.isEntry_T_h M F) S.C X
  -- `u` is an updater of slot `r' * R`: honest up to its tick `j'`, awake from its tick to the duty
  -- window's start of slot `r' * R + 1`
  have hj'j : x.time j' ≤ x.time j := htime hj'.le
  have hhon' : ∀ i : ℕ, i ≤ j' → u ∉ A.corrupted i := fun i hi => hhon i (by omega)
  have hkt := (E.tick_active j' u _ hl).2
  have hdws : tGAT + Δ S ≤ M.dutyWindowStart S.C (r' * S.C.R + 1) :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_of_anchor M.toSlotLayout F.sched U) S
      tGAT (r * S.C.R) hAnchor)
      ((GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_mono M.toSlotLayout F.sched) S
        (show r * S.C.R ≤ r' * S.C.R + 1 by have := Nat.mul_le_mul_right S.C.R hrr; omega))
  have hdw := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_succ_le_slotStart M.toSlotLayout F.sched) S
    (r' * S.C.R)
  have hT0 := (GoldilocksCorrectness.Record.Proofs.Routines.times_le M.toSlotLayout F.sched) S (r' * S.C.R)
  have hT1 := (GoldilocksCorrectness.Record.Proofs.Routines.times_le M.toSlotLayout F.sched) S (r' * S.C.R + 1)
  have hcR : ((M.dutyWindowStart S.C (r' * S.C.R + 1) : ℕ) : ℝ) + 4 * Δ S ≤ (aR M S r' : ℝ) := by
    have : M.dutyWindowStart S.C (r' * S.C.R + 1) + 4 * Δ S ≤ aR M S r' := by
      show _ ≤ M.supportCutoff S.C (r' * S.C.R + 1)
      omega
    exact_mod_cast this
  have hdwsR : ((tGAT : ℕ) : ℝ) + Δ S ≤ ((M.dutyWindowStart S.C (r' * S.C.R + 1) : ℕ) : ℝ) := by
    exact_mod_cast hdws
  obtain ⟨kc, hkc, hkc1, hkc2⟩ := E.tick_of_active (M.dutyWindowStart S.C (r' * S.C.R + 1)) (by omega) u
    (fun i h1 h2 => by
      have hij : i < j' := (lt_of_time_lt M) x R (by linarith)
      have hui := hhon' i hij.le
      exact Activity.mem_active.2 ⟨hAwake i u (by linarith [htime hij.le]) (by linarith [htime (Nat.le_succ i)]) hui, hui⟩)
  have hkcj : kc ≤ j' := tick_step_le_of_le M F E hkc hl (by
    show M.dutyWindowStart S.C (r' * S.C.R + 1) ≤ M.supportCutoff S.C (r' * S.C.R + 1)
    omega)
  have hupd : u ∈ updaterAt M S A x (r' * S.C.R) := by
    show u ∈ A.activeThroughoutToTick x (Goldilocks.duty_window_start S.C (r' * S.C.R + 1))
      (M.supportCutoff S.C (r' * S.C.R + 1))
    refine Activity.mem_activeThroughoutToTick.2 ⟨j', hl, Or.inr ⟨kc, hkcj, M.dutyWindowStart S.C (r' * S.C.R + 1),
      (dutyWindowStart_le_duty_window_start M F U) S (by omega), hkc, fun i h1 h2 => ?_⟩⟩
    have hui := hhon' i h2
    exact Activity.mem_active.2 ⟨hAwake i u (by linarith [htime h2]) (by linarith [htime h1, htime (Nat.le_succ i)]) hui, hui⟩
  have hst := (GoldilocksCorrectness.Record.Proofs.Executions.state_saved_of_update M F U) S A x R (r' * S.C.R) u n₀ E
    hupd hU
  obtain ⟨C₀, hC₀, hXC₀⟩ :=
    GoldilocksCorrectness.Record.Proofs.Routines.update_confirmation_fast_block_saved
      (Nat.le_add_left 1 _) hU hXf
  rw [Nat.add_sub_cancel] at hC₀
  have hkind : (r' * S.C.R = r * S.C.R ∧ X ∈ M.fastBlocks n₀ ∧ (M.chainStateOf S.C X).h = H₂ + 1) ∨
      (r * S.C.R + 1 ≤ r' * S.C.R ∧ (X ∈ M.fastBlocks n₀ ∨
        M.slow_test S.C (x.tickInput u (M.supportCutoff S.C (r' * S.C.R + 1))) (r' * S.C.R) X =
          true)) ∨
      r * S.C.R + S.C.k ≤ r' * S.C.R := by
    rcases Nat.lt_or_eq_of_le hrr with hlt | heq
    · refine Or.inr (Or.inl ⟨?_, Or.inl hXf⟩)
      have h1 := Nat.mul_le_mul_right S.C.R (show r + 1 ≤ r' by omega)
      have h2 := S.C.R_ge_two
      rw [Nat.succ_mul] at h1
      omega
    · subst heq
      refine Or.inl ⟨rfl, hXf, ?_⟩
      -- `X` is `H_v` or an ancestor of it, a block an honest committee member held at its tick to the
      -- vote time of slot `r * R`, a step before `v`'s tick to `aR M S r` (A2 there)
      have hRoots' : RootsNameBlocksUntil M A x ((M.supportCutoff S.C (r * S.C.R + 1) : ℕ) : ℝ) :=
        hRoots.mono M (by exact_mod_cast hEnd)
      obtain ⟨v', -, H_v, hHv, hXH⟩ :=
        (fast_block_has_honest_supporter_of_update M F U) S A x R (anchorCW S tGAT) (r * S.C.R) u E hSkew
          ((votesCastByOwner_of_unforgeability M F) S A x R E) hRoots'
          (hCommittees.mono M hEnd) hAnchor hupd n₀ hU X hXf
      have hk0t := (E.tick_active _ v _ hk₀).2.1
      have hT0' := (GoldilocksCorrectness.Record.Proofs.Routines.times_le M.toSlotLayout F.sched) S (r * S.C.R)
      have hT1' := (GoldilocksCorrectness.Record.Proofs.Routines.times_le M.toSlotLayout F.sched) S (r * S.C.R + 1)
      -- `v'`'s tick to the vote time of slot `r * R` comes before the first step reaching that slot's support cutoff
      have hvk : x.tickStep v' (M.voteTime S.C (r * S.C.R)) ≤ x.firstAt (M.supportCutoff S.C (r * S.C.R)) := by
        by_cases hex : ∃ i : ℕ, x.lbl i = Event.tick v' (M.voteTime S.C (r * S.C.R))
        · obtain ⟨i, hi⟩ := hex
          rw [(tickStep_eq_of_lbl M) x E hi]
          have hit := (E.tick_active i v' _ hi).2.2
          have hvt : ((M.voteTime S.C (r * S.C.R) : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (r * S.C.R) : ℕ) : ℝ) := by
            exact_mod_cast hT0'.2.1
          exact ((lt_firstAt_of_time_lt M F) R E (by linarith)).le
        · simp only [Trace.tickStep, hex, dif_neg, not_false_eq_true]
          exact Nat.zero_le _
      -- that first step is at or before `v`'s tick to `aR M S r`, so in the phase
      have hk0E : x.time (x.firstAt (M.supportCutoff S.C (r * S.C.R))) ≤ tAwakeEnd := by
        have hc : ((M.supportCutoff S.C (r * S.C.R) : ℕ) : ℝ) ≤ x.time (x.tickStep v (aR M S r)) := by
          have : M.supportCutoff S.C (r * S.C.R) + 4 * Δ S ≤ aR M S r := by
            show _ ≤ M.supportCutoff S.C (r * S.C.R + 1)
            omega
          have h4 : ((M.supportCutoff S.C (r * S.C.R) : ℕ) : ℝ) + 4 * Δ S ≤ (aR M S r : ℝ) := by exact_mod_cast this
          linarith
        exact le_trans ((time_mono M) x R ((firstAt_le_of_time_ge M F) R E hc)) hEndStep
      have hle := (held_height_le_before_action M F Fx) S A x R E tAwakeEnd H₂ (x.firstAt (M.supportCutoff S.C (r * S.C.R)))
        (x.tickStep v' (M.voteTime S.C (r * S.C.R))) v' H_v hThird hOldStep hk0E hvk hHv
      have hmono := (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_height_mono M F) S.C hXH
      rw [hXh, hh'] at hmono ⊢
      unfold Height at *
      omega
  refine ⟨r', (M.chainStateOf S.C X).T_h, u, j', hrr, hl, hj', hact', ⟨u, hupd, n₀, C₀, X, hU, hC₀,
    hst.trans hC₀, hE3, hXC₀, hkind⟩, hE1, by rw [hE2, hXh, hh'], ?_, huE, C₀, hst.trans hC₀, ancestorEq_trans hE3 hXC₀⟩
  rw [← hT', ← hXT']

namespace PartAHyps
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

variable {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N}
  {GST tGAT tAwakeEnd r H₂ : ℕ} {v : V} {L : Block V} {n' : M.N}

/-- `cert_source` with the source at a round's first slot: a progress certificate at a height
`h > H₂` on the chain of a block an honest validator holds after `j` steps, within the phase,
names the root of an entry block `E` at the height `h` that is a line source of the first slot of a
round `r' ≥ r` whose update an honest validator `u` ran at its tick `k` to `aR M S r'`, a step before `j` at which
`u` is active (`cert_source_core`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed.

Read aloud: a progress certificate above `H₂` on the chain of a block an honest validator holds in
the phase names the root of an entry block that is a line source of a round's first slot whose
update an honest validator ran at a tick before the reading. -/
theorem cert_source_round (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    {Δs : ℕ} {ΔNet : ℕ} (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {j : ℕ} {w : V}
    {Y T : Block V} {h : Height} (hj : x.time j ≤ tAwakeEnd)
    (hY : Y ∈ (x.st j w).tree) (hJ : ProgressCertOn M Y h T) (hH : H₂ < h) :
    ∃ (r' : ℕ) (E : Block V) (u : V) (k : ℕ), r ≤ r' ∧ x.lbl k = Event.tick u (aR M S r') ∧ k < j ∧
      u ∈ A.active k ∧ LineSource M S A x r H₂ (r' * S.C.R) E ∧ IsEntry M S.C E ∧
      (M.chainStateOf S.C E).h = h ∧ T.root = E.root := by
  exact (cert_source_core M F) R E U Fx P.hSkew P.hRoots P.hThird P.hAwake P.hCommittees P.hAnchor P.hOld
    P.hEnd P.hk₀ P.hOldStep P.hEndStep hj hY hJ hH

/-- **The root is a line source of a round's first slot, at a step.** `root_source` read at a step `j` in place of
the state before a time: when some validator ticked to the action time of round `r` at a step before `j`, the real
time of `j` is less than the support cutoff of slot `σ + 2` less `ΔClockAhead` (the earliest real time of a tick to
that cutoff), `w` is outside the adversary set at `j`, in the phase, and the invariant holds at every slot up to `σ`:
`w`'s fork-choice root at `j` is a line source of the first slot of a round `r' ≥ r` to whose action time an honest
validator ticked a step before `j`.

Why: `root_source`'s argument, read at `j` (`L_tall_st` for `L` at `j`, `F_compat_st` for the finalized block, whose
votes clause is not asked since `j` is before every tick to the support cutoff of slot `σ + 2`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed; `j`: the step.

Read aloud: at a step after a tick to round `r`'s action time and before every tick to the support cutoff of slot
`σ + 2`, an honest validator's fork-choice root is a line source of a round's first slot to whose action time an
honest validator ticked a step before. -/
theorem root_source_st (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {σ j : ℕ} {w : V}
    (hG : ∀ σ', σ' ≤ σ → LineInv M S A x r H₂ σ') (hσ : r * S.C.R ≤ σ)
    (hEnd : M.supportCutoff S.C (σ + 2) ≤ tAwakeEnd)
    (ht0 : ∃ (u : V) (k : ℕ), x.lbl k = Event.tick u (aR M S r) ∧ k < j ∧ u ∈ A.active k)
    (hjt : x.time j < ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) - ΔClockAhead) (hw' : w ∉ A.corrupted j) :
    ∃ r' : ℕ, r ≤ r' ∧ (∃ (u : V) (k : ℕ), x.lbl k = Event.tick u (aR M S r') ∧ k < j ∧ u ∈ A.active k) ∧
      LineSource M S A x r H₂ (r' * S.C.R) (M.get_fc_root (x.st j w)) := by
  have hA0 := E.ahead_nonneg
  have hsk := hSkew
  have hB0 := E.behind_nonneg
  have hEndR : M.supportCutoff S.C (r * S.C.R + 1) ≤ tAwakeEnd := P.hEnd
  -- the tick of `ht0` is at a real time at least the action time of round `r` less `ΔClockAhead`, so `j` is after the
  -- start of slot `r * R + 1`
  obtain ⟨u₀, k₀, hk₀, hk₀j, -⟩ := id ht0
  have hk₀a : ((aR M S r : ℕ) : ℝ) - ΔClockAhead ≤ x.time k₀ := (E.tick_active _ _ _ hk₀).2.1
  have hk₀k : x.time k₀ ≤ x.time j := (time_mono M) x R hk₀j.le
  have hj0 : ((M.slotStart S.C (r * S.C.R + 1) : ℕ) : ℝ) ≤ x.time j := by
    obtain ⟨-, hc1, -, -, hΔ⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (r * S.C.R + 1)
    have haR : aR M S r = M.supportCutoff S.C (r * S.C.R + 1) := rfl
    have h1 : ((M.slotStart S.C (r * S.C.R + 1) : ℕ) : ℝ) + Δ S ≤ ((aR M S r : ℕ) : ℝ) := by
      exact_mod_cast (show M.slotStart S.C (r * S.C.R + 1) + Δ S ≤ aR M S r by omega)
    linarith
  have hLsrc : ∀ Y : Block V, Y.AncestorEq L → ∃ r' : ℕ, r ≤ r' ∧
      (∃ (u : V) (k : ℕ), x.lbl k = Event.tick u (aR M S r') ∧ k < j ∧ u ∈ A.active k) ∧
      LineSource M S A x r H₂ (r' * S.C.R) Y :=
    fun Y hY => ⟨r, le_rfl, ht0, (P.source_L M F R U hEndR).anc M F hY⟩
  have hcE : ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) ≤ (tAwakeEnd : ℕ) := by exact_mod_cast hEnd
  have hjE : x.time j ≤ tAwakeEnd := by linarith
  have hInv : M.nodeInv S.C S.P S.X (x.st j w) :=
    (GoldilocksCorrectness.Record.Proofs.Executions.lem11_node_invariant M F S A x R E j w hw').1
  -- a line source of a round's first slot whose update an honest validator ran at a tick before `j`
  have hcert : ∀ (h : Height) (Y T : Block V), Y ∈ (x.st j w).tree → ProgressCertOn M Y h T →
      H₂ < h → T ∈ (x.st j w).tree → ∃ r' : ℕ, r ≤ r' ∧
        (∃ (u : V) (k : ℕ), x.lbl k = Event.tick u (aR M S r') ∧ k < j ∧ u ∈ A.active k) ∧
        LineSource M S A x r H₂ (r' * S.C.R) T := by
    intro h Y T hY hJ hH hT
    obtain ⟨r', Eb, u, kc, hrr, hkc, hkcj, hku, hE, -, -, hEr⟩ := P.cert_source_round M F R E U Fx hjE hY hJ hH
    have hTE := P.hRoots _ _ ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E
        (i := j) (v := w) hw' hjE hT)
      ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_mono M) x (le_trans ((time_mono M) x R hkcj.le) hjE)
        (P.source_inHonestTreeBy_tick M F R E U hE hkc)) hEr
    rw [hTE]
    exact ⟨r', hrr, ⟨u, kc, hkc, hkcj, hku⟩, hE⟩
  obtain ⟨hLT, hM⟩ := P.L_tall_st M F R E hNet hSkew hRedeliver Sy hΔs U Fx hEndR hj0 hjE hw'
  by_cases hR : M.get_fc_root (x.st j w) = (x.st j w).finalized
  · rw [hR]
    obtain ⟨D, hD, hFD⟩ :=
      (GoldilocksCorrectness.Record.Statements.Executions.finalizedFromChain_of_exec M F) S A x R E j w
    rw [hFD]
    by_cases hle : (M.chainStateOf S.C D).h_F ≤ H₂
    · -- `v` held `L` at its tick to the action time of round `r` (`L_held_v`), honest there, in the phase
      have hv' : v ∉ A.corrupted (x.tickStep v (aR M S r)) := E.not_mem_corrupted_of_tick P.hk₀
      have hT : A.AdversaryFewerThanThirdUntil x (validator_count V)
          (max (x.time j) (x.time (x.tickStep v (aR M S r)))) :=
        P.hThird.mono (max_le hjE P.hEndStep)
      have hLv : L ∈ (x.st (x.tickStep v (aR M S r)) v).tree := (P.L_held_v M F R E U hEndR).2
      exact hLsrc _ ((GoldilocksCorrectness.Record.Proofs.Executions.lem68_honest_past_finalized M F Fx) S A x R E P.hRoots
        j (x.tickStep v (aR M S r)) w v D L hT hw' hv' hD hLv
        (by rw [P.hL]; exact Nat.lt_succ_of_le hle) (max_le hjE P.hEndStep))
    · have hlt : H₂ < (M.chainStateOf S.C D).h_F := Nat.lt_of_not_le hle
      obtain ⟨hJC, -, hFanc, -⟩ :=
        ((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) S.C D).2.2
          (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le H₂) hlt))
      have hFT : (M.chainStateOf S.C D).F ∈ (x.st j w).tree :=
        (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E _ w D _ hD hFanc
      exact hcert _ D _ hD ((GoldilocksCorrectness.Record.Proofs.Executions.progressCertOn_of_justificationCertOn M F) hJC)
        hlt hFT
  have key : hMax M S.C (x.st j w) = (x.st j w).justifiedHeight + 1 ∧
      M.get_fc_root (x.st j w) = (x.st j w).justified := by
    rcases (GoldilocksCorrectness.Record.Proofs.Routines.root_cases M F) S.C S.P S.X (x.st j w) hInv with ⟨hJ, hm, -⟩ | ⟨hF, -⟩
    · exact ⟨hm, hJ⟩
    · exact absurd hF hR
  obtain ⟨⟨D, hD, hJD, hhjD⟩, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Executions.cachesWitnessed_of_exec M F) S A x R E j w
  rw [key.2]
  by_cases hlt : H₂ < (x.st j w).justifiedHeight
  · rw [hhjD] at hlt
    obtain ⟨hJC, hJanc, -⟩ := ((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F)
      S.C D).1 (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le H₂) hlt))
    have hJT : (M.chainStateOf S.C D).J ∈ (x.st j w).tree :=
      (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E _ w D _ hD hJanc
    rw [hJD]
    exact hcert _ D _ hD ((GoldilocksCorrectness.Record.Proofs.Executions.progressCertOn_of_justificationCertOn M F) hJC)
      hlt hJT
  · have hhj : (x.st j w).justifiedHeight = H₂ := by
      have := key.1
      have h1 : (x.st j w).justifiedHeight ≤ H₂ := Nat.le_of_not_lt hlt
      unfold Height at *
      omega
    by_cases h0 : (M.chainStateOf S.C D).h_j = 0
    · have hg := ((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_J_spec M F) S.C D).2.1 h0
      rw [hJD, hg]
      exact hLsrc _ (GoldilocksCorrectness.Proofs.Routines.genesis_ancestorEq L)
    · have hJh := ((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_J_spec M F) S.C D).2.2 (Nat.one_le_iff_ne_zero.2 h0)
      have hFJ : (x.st j w).finalized.AncestorEq (x.st j w).justified := by
        have := (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F) S A x R E j w
        rw [key.2] at this
        exact this
      -- the finalized block is compatible with `L`, read at `j`, which is before every tick to the support cutoff of
      -- slot `σ + 2` (so the votes clause of `F_compat_st` is not asked)
      have hjc : x.time j < ((M.supportCutoff S.C (σ + 3) : ℕ) : ℝ) - ΔClockAhead := by
        have hm := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
          (show σ + 2 ≤ σ + 3 by omega)
        have : ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) ≤ ((M.supportCutoff S.C (σ + 3) : ℕ) : ℝ) := by exact_mod_cast hm
        linarith
      have hFLc : (x.st j w).finalized.compatible L = true :=
        P.F_compat_st M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hσ hEnd hjE hw' hjc (P.source_L M F R U hEndR) hσ
          (fun h => absurd h (by linarith))
      have hFL : (x.st j w).finalized.AncestorEq L := by
        rcases (compatible_iff _ _).1 hFLc with h | h
        · exact h
        · exfalso
          have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_height_mono M F) S.C (ancestorEq_trans h hFJ)
          rw [hJD, hJh, ← hhjD, hhj, P.hL] at h1
          exact Nat.lt_irrefl _ (Nat.lt_of_succ_le h1)
      have hRL := (GoldilocksCorrectness.Record.Proofs.Routines.fc_root_ancestorEq_of_tall M F) S.C S.P S.X _ hInv L hLT hFL (by
        rw [P.hL, key.1, hhj])
      rw [key.2] at hRL
      exact hLsrc _ hRL

/-- **`root_source_st` with the line source's updater named.** As `root_source_st`, with "`v`'s own tick to the
action time of round `r` is a step before `j`" in place of "some validator ticked there before `j`": `w`'s fork-choice
root at `j` is a line source of the first slot of a round `r' ≥ r` made by the update of a validator `u` at its tick `k`
to `aR M S r'`, a step before `j`; `u` is outside the adversary set at `aR M S r'` (so a member of
`Hon M S A x (r' * R)`), and the root is on the chain of the confirmation of slot `r' * R` that this tick saved.

Why: `root_source_st`'s argument; a source on `L`'s chain is `v`'s own update (`source_L`'s proof, `P.hv`), a
certificate's source is its attester's (`cert_source_core_fast_attester`, honest up to `tAwakeEnd`, and `aR M S r'`
is at most `tAwakeEnd` since that attester's tick is before `j`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed; `j`: the step.

Read aloud: at a step after `v`'s tick to round `r`'s action time and before every tick to the support cutoff of
slot `σ + 2`, an honest validator's fork-choice root is on the confirmation saved by the update of a validator honest
at a round's action time, whose tick there came before, and is a line source of that round's first slot. -/
theorem root_source_st_attester (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {σ j : ℕ} {w : V}
    (hG : ∀ σ', σ' ≤ σ → LineInv M S A x r H₂ σ') (hσ : r * S.C.R ≤ σ)
    (hEnd : M.supportCutoff S.C (σ + 2) ≤ tAwakeEnd)
    (hv0 : x.tickStep v (aR M S r) < j)
    (hjt : x.time j < ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) - ΔClockAhead) (hw' : w ∉ A.corrupted j) :
    ∃ r' : ℕ, r ≤ r' ∧ (∃ (u : V) (k : ℕ), x.lbl k = Event.tick u (aR M S r') ∧ k < j ∧ u ∈ A.active k ∧
      u ∉ A.corruptedAtTime x (aR M S r') ∧ ∃ C₀ : Block V,
        M.savedConfirmation (x.tickOutput u (M.supportCutoff S.C (r' * S.C.R + 1))) (r' * S.C.R) = some C₀ ∧
        (M.get_fc_root (x.st j w)).AncestorEq C₀) ∧
      LineSource M S A x r H₂ (r' * S.C.R) (M.get_fc_root (x.st j w)) := by
  have hvk := (E.tick_active _ _ _ P.hk₀).1
  have ht0 : ∃ (u : V) (k : ℕ), x.lbl k = Event.tick u (aR M S r) ∧ k < j ∧ u ∈ A.active k :=
    ⟨v, x.tickStep v (aR M S r), P.hk₀, hv0, hvk⟩
  have hA0 := E.ahead_nonneg
  have hsk := hSkew
  have hB0 := E.behind_nonneg
  have hEndR : M.supportCutoff S.C (r * S.C.R + 1) ≤ tAwakeEnd := P.hEnd
  -- the tick of `ht0` is at a real time at least the action time of round `r` less `ΔClockAhead`, so `j` is after the
  -- start of slot `r * R + 1`
  obtain ⟨u₀, k₀, hk₀, hk₀j, -⟩ := id ht0
  have hk₀a : ((aR M S r : ℕ) : ℝ) - ΔClockAhead ≤ x.time k₀ := (E.tick_active _ _ _ hk₀).2.1
  have hk₀k : x.time k₀ ≤ x.time j := (time_mono M) x R hk₀j.le
  have hj0 : ((M.slotStart S.C (r * S.C.R + 1) : ℕ) : ℝ) ≤ x.time j := by
    obtain ⟨-, hc1, -, -, hΔ⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (r * S.C.R + 1)
    have haR : aR M S r = M.supportCutoff S.C (r * S.C.R + 1) := rfl
    have h1 : ((M.slotStart S.C (r * S.C.R + 1) : ℕ) : ℝ) + Δ S ≤ ((aR M S r : ℕ) : ℝ) := by
      exact_mod_cast (show M.slotStart S.C (r * S.C.R + 1) + Δ S ≤ aR M S r by omega)
    linarith
  have hLsrc : ∀ Y : Block V, Y.AncestorEq L → ∃ r' : ℕ, r ≤ r' ∧
      (∃ (u : V) (k : ℕ), x.lbl k = Event.tick u (aR M S r') ∧ k < j ∧ u ∈ A.active k ∧
        u ∉ A.corruptedAtTime x (aR M S r') ∧ ∃ C₀ : Block V,
          M.savedConfirmation (x.tickOutput u (M.supportCutoff S.C (r' * S.C.R + 1))) (r' * S.C.R) = some C₀ ∧
          Y.AncestorEq C₀) ∧
      LineSource M S A x r H₂ (r' * S.C.R) Y := by
    intro Y hY
    have hvH : v ∈ Hon M S A x (r * S.C.R) := by
      unfold Hon roundMembers
      exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _, P.hv⟩
    have hvU : v ∈ updaterAt M S A x (r * S.C.R) := P.memberU M F U le_rfl hvH hEndR
    obtain ⟨C', hC', hLC'⟩ :=
      GoldilocksCorrectness.Record.Proofs.Routines.update_confirmation_fast_block_saved
        (Nat.le_add_left 1 _) P.hUpdate P.hFast
    rw [Nat.add_sub_cancel] at hC'
    have hst := (state_saved_of_update M F U) S A x R (r * S.C.R) v n' P.E hvU P.hUpdate
    exact ⟨r, le_rfl, ⟨v, x.tickStep v (aR M S r), P.hk₀, hv0, hvk, P.hv, C', hst.trans hC',
      ancestorEq_trans hY hLC'⟩, (P.source_L M F R U hEndR).anc M F hY⟩
  have hcE : ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) ≤ (tAwakeEnd : ℕ) := by exact_mod_cast hEnd
  have hjE : x.time j ≤ tAwakeEnd := by linarith
  have hInv : M.nodeInv S.C S.P S.X (x.st j w) :=
    (GoldilocksCorrectness.Record.Proofs.Executions.lem11_node_invariant M F S A x R E j w hw').1
  -- a line source of a round's first slot whose update an honest validator ran at a tick before `j`
  have hcert : ∀ (h : Height) (Y T : Block V), Y ∈ (x.st j w).tree → ProgressCertOn M Y h T →
      H₂ < h → T ∈ (x.st j w).tree → ∃ r' : ℕ, r ≤ r' ∧
        (∃ (u : V) (k : ℕ), x.lbl k = Event.tick u (aR M S r') ∧ k < j ∧ u ∈ A.active k ∧
          u ∉ A.corruptedAtTime x (aR M S r') ∧ ∃ C₀ : Block V,
            M.savedConfirmation (x.tickOutput u (M.supportCutoff S.C (r' * S.C.R + 1))) (r' * S.C.R) = some C₀ ∧
            T.AncestorEq C₀) ∧
        LineSource M S A x r H₂ (r' * S.C.R) T := by
    intro h Y T hY hJ hH hT
    obtain ⟨r', Eb, u, kc, hrr, hkc, hkcj, hku, hE, -, -, hEr, huE, C₀, hsv, hEC₀⟩ :=
      (cert_source_core_fast_attester M F) R E U Fx P.hSkew P.hRoots P.hThird P.hAwake P.hCommittees P.hAnchor P.hOld
        P.hEnd P.hk₀ P.hOldStep P.hEndStep hjE hY hJ hH
    -- `u`'s tick to `aR M S r'` is before `j`, so `aR M S r'` is less than the support cutoff of slot `σ + 2`
    have hkct := (E.tick_active _ _ _ hkc).2.1
    have hkcj' : x.time kc ≤ x.time j := (time_mono M) x R hkcj.le
    have haRE : aR M S r' ≤ tAwakeEnd := by
      have : ((aR M S r' : ℕ) : ℝ) < (tAwakeEnd : ℕ) := by linarith
      exact_mod_cast this.le
    have huR' : u ∉ A.corruptedAtTime x (aR M S r') := (not_mem_corruptedAtTime_of_le M) x R E haRE huE
    have hTE := P.hRoots _ _ ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E
        (i := j) (v := w) hw' hjE hT)
      ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_mono M) x (le_trans ((time_mono M) x R hkcj.le) hjE)
        (P.source_inHonestTreeBy_tick M F R E U hE hkc)) hEr
    rw [hTE]
    exact ⟨r', hrr, ⟨u, kc, hkc, hkcj, hku, huR', C₀, hsv, hEC₀⟩, hE⟩
  obtain ⟨hLT, hM⟩ := P.L_tall_st M F R E hNet hSkew hRedeliver Sy hΔs U Fx hEndR hj0 hjE hw'
  by_cases hR : M.get_fc_root (x.st j w) = (x.st j w).finalized
  · rw [hR]
    obtain ⟨D, hD, hFD⟩ :=
      (GoldilocksCorrectness.Record.Statements.Executions.finalizedFromChain_of_exec M F) S A x R E j w
    rw [hFD]
    by_cases hle : (M.chainStateOf S.C D).h_F ≤ H₂
    · -- `v` held `L` at its tick to the action time of round `r` (`L_held_v`), honest there, in the phase
      have hv' : v ∉ A.corrupted (x.tickStep v (aR M S r)) := E.not_mem_corrupted_of_tick P.hk₀
      have hT : A.AdversaryFewerThanThirdUntil x (validator_count V)
          (max (x.time j) (x.time (x.tickStep v (aR M S r)))) :=
        P.hThird.mono (max_le hjE P.hEndStep)
      have hLv : L ∈ (x.st (x.tickStep v (aR M S r)) v).tree := (P.L_held_v M F R E U hEndR).2
      exact hLsrc _ ((GoldilocksCorrectness.Record.Proofs.Executions.lem68_honest_past_finalized M F Fx) S A x R E P.hRoots
        j (x.tickStep v (aR M S r)) w v D L hT hw' hv' hD hLv
        (by rw [P.hL]; exact Nat.lt_succ_of_le hle) (max_le hjE P.hEndStep))
    · have hlt : H₂ < (M.chainStateOf S.C D).h_F := Nat.lt_of_not_le hle
      obtain ⟨hJC, -, hFanc, -⟩ :=
        ((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) S.C D).2.2
          (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le H₂) hlt))
      have hFT : (M.chainStateOf S.C D).F ∈ (x.st j w).tree :=
        (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E _ w D _ hD hFanc
      exact hcert _ D _ hD ((GoldilocksCorrectness.Record.Proofs.Executions.progressCertOn_of_justificationCertOn M F) hJC)
        hlt hFT
  have key : hMax M S.C (x.st j w) = (x.st j w).justifiedHeight + 1 ∧
      M.get_fc_root (x.st j w) = (x.st j w).justified := by
    rcases (GoldilocksCorrectness.Record.Proofs.Routines.root_cases M F) S.C S.P S.X (x.st j w) hInv with ⟨hJ, hm, -⟩ | ⟨hF, -⟩
    · exact ⟨hm, hJ⟩
    · exact absurd hF hR
  obtain ⟨⟨D, hD, hJD, hhjD⟩, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Executions.cachesWitnessed_of_exec M F) S A x R E j w
  rw [key.2]
  by_cases hlt : H₂ < (x.st j w).justifiedHeight
  · rw [hhjD] at hlt
    obtain ⟨hJC, hJanc, -⟩ := ((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F)
      S.C D).1 (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le H₂) hlt))
    have hJT : (M.chainStateOf S.C D).J ∈ (x.st j w).tree :=
      (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E _ w D _ hD hJanc
    rw [hJD]
    exact hcert _ D _ hD ((GoldilocksCorrectness.Record.Proofs.Executions.progressCertOn_of_justificationCertOn M F) hJC)
      hlt hJT
  · have hhj : (x.st j w).justifiedHeight = H₂ := by
      have := key.1
      have h1 : (x.st j w).justifiedHeight ≤ H₂ := Nat.le_of_not_lt hlt
      unfold Height at *
      omega
    by_cases h0 : (M.chainStateOf S.C D).h_j = 0
    · have hg := ((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_J_spec M F) S.C D).2.1 h0
      rw [hJD, hg]
      exact hLsrc _ (GoldilocksCorrectness.Proofs.Routines.genesis_ancestorEq L)
    · have hJh := ((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_J_spec M F) S.C D).2.2 (Nat.one_le_iff_ne_zero.2 h0)
      have hFJ : (x.st j w).finalized.AncestorEq (x.st j w).justified := by
        have := (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F) S A x R E j w
        rw [key.2] at this
        exact this
      -- the finalized block is compatible with `L`, read at `j`, which is before every tick to the support cutoff of
      -- slot `σ + 2` (so the votes clause of `F_compat_st` is not asked)
      have hjc : x.time j < ((M.supportCutoff S.C (σ + 3) : ℕ) : ℝ) - ΔClockAhead := by
        have hm := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
          (show σ + 2 ≤ σ + 3 by omega)
        have : ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) ≤ ((M.supportCutoff S.C (σ + 3) : ℕ) : ℝ) := by exact_mod_cast hm
        linarith
      have hFLc : (x.st j w).finalized.compatible L = true :=
        P.F_compat_st M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hσ hEnd hjE hw' hjc (P.source_L M F R U hEndR) hσ
          (fun h => absurd h (by linarith))
      have hFL : (x.st j w).finalized.AncestorEq L := by
        rcases (compatible_iff _ _).1 hFLc with h | h
        · exact h
        · exfalso
          have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_height_mono M F) S.C (ancestorEq_trans h hFJ)
          rw [hJD, hJh, ← hhjD, hhj, P.hL] at h1
          exact Nat.lt_irrefl _ (Nat.lt_of_succ_le h1)
      have hRL := (GoldilocksCorrectness.Record.Proofs.Routines.fc_root_ancestorEq_of_tall M F) S.C S.P S.X _ hInv L hLT hFL (by
        rw [P.hL, key.1, hhj])
      rw [key.2] at hRL
      exact hLsrc _ hRL

/-- **The root is a line source of a round's first slot.** When some validator ticked to the action time
of round `r` at a step before the reading, read before a time at least `ΔClockAhead` before the support
cutoff of slot `σ + 2` (T-R72-1's bound), in the phase, when the invariant holds at every slot up to
`σ`: an honest validator's fork-choice root is a line source of the first slot of a round
`r' ≥ r` to whose action time an honest validator ticked a step before the reading.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed.

Read aloud: after round `r`'s action time, an honest validator's fork-choice root is a line source
of a round's first slot to whose action time an honest validator ticked a step before the reading. -/
theorem root_source (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {σ t : ℕ} {w : V}
    (hG : ∀ σ', σ' ≤ σ → LineInv M S A x r H₂ σ') (hσ : r * S.C.R ≤ σ)
    (hEnd : M.supportCutoff S.C (σ + 2) ≤ tAwakeEnd)
    (ht0 : ∃ (u : V) (k : ℕ), x.lbl k = Event.tick u (aR M S r) ∧ k < x.stepBefore t ∧ u ∈ A.active k)
    (ht : (t : ℝ) ≤ ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) - ΔClockAhead) (hw : w ∉ A.corruptedAtTime x t) :
    ∃ r' : ℕ, r ≤ r' ∧ (∃ (u : V) (k : ℕ), x.lbl k = Event.tick u (aR M S r') ∧ k < x.stepBefore t ∧ u ∈ A.active k) ∧
      LineSource M S A x r H₂ (r' * S.C.R) (M.get_fc_root (x.stateBefore t w)) := by
  obtain ⟨u₀, k₀, hk₀, hk₀t, -⟩ := id ht0
  have hk₀T : x.time (k₀ + 1) < t := ((lt_stepBefore_iff M) x R P.E).1 hk₀t
  have ht1 : 1 ≤ t := by
    have h2 := (time_nonneg M) x R (k₀ + 1)
    exact Nat.cast_pos.1 (lt_of_le_of_lt h2 hk₀T)
  have htj : x.time (x.stepBefore t) < t := ((stepBefore_time M) x R P.E ht1).1
  exact P.root_source_st M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hσ hEnd ht0 (by linarith)
    ((not_mem_corrupted_of_le_time M) x R P.E hw (by exact_mod_cast htj.le))

/-- `tall_entry` with the source at a round's first slot (`cert_source_round`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed.

Read aloud: a block at least two above `H₂` that an honest validator holds in the phase has as an
ancestor an entry block one height less that is a line source of a round's first slot to whose action time an honest validator ticked a step before the reading. -/
theorem tall_entry_round (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    {Δs : ℕ} {ΔNet : ℕ} (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {t : ℕ} {w : V}
    (ht1 : 1 ≤ t) (htE : t ≤ tAwakeEnd) (hw : w ∉ A.corruptedAtTime x t) {Y : Block V}
    (hY : Y ∈ (x.stateBefore t w).tree) (hYh : H₂ + 2 ≤ (M.chainStateOf S.C Y).h) :
    ∃ (r' : ℕ) (E : Block V), r ≤ r' ∧ (∃ (u : V) (k : ℕ), x.lbl k = Event.tick u (aR M S r') ∧
        k < x.stepBefore t ∧ u ∈ A.active k) ∧
      LineSource M S A x r H₂ (r' * S.C.R) E ∧ IsEntry M S.C E ∧
      (M.chainStateOf S.C E).h = (M.chainStateOf S.C Y).h - 1 ∧ E.AncestorEq Y := by
  -- the step before `t` is at a time less than `t` (`stepBefore_time`'s strict bound)
  have htj : x.time (x.stepBefore t) < t := ((stepBefore_time M) x R E ht1).1
  have htE' : ((t : ℕ) : ℝ) ≤ (tAwakeEnd : ℕ) := by exact_mod_cast htE
  have hjE : x.time (x.stepBefore t) ≤ tAwakeEnd := by linarith
  have hw' : w ∉ A.corrupted (x.stepBefore t) :=
    (not_mem_corrupted_of_le_time M) x R P.E hw htj.le
  have hY' : Y ∈ (x.st (x.stepBefore t) w).tree := hY
  obtain ⟨Y', hY'Y, -, -, -, hT', hcert⟩ :=
    (GoldilocksCorrectness.Record.Statements.Routines.lem67_first_advance M F) S.C Y
      ((M.chainStateOf S.C Y).h - 1) (by unfold Height at *; omega) (by unfold Height at *; omega)
  have hY'T := (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E _ w Y Y' hY' hY'Y
  have hT'T := (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E _ w Y' _ hY'T hT'
  obtain ⟨r', Eb, u, kc, hrr, hkc, hkcj, hku, hE, hEe, hEh, hEr⟩ := P.cert_source_round M F R E U Fx hjE hY'T hcert
    (by unfold Height at *; omega)
  have hTE := P.hRoots _ _ ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := x.stepBefore t) (v := w) hw' hjE hT'T)
    ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_mono M) x (le_trans ((time_mono M) x R hkcj.le) hjE) (P.source_inHonestTreeBy_tick M F R E U hE hkc)) hEr
  refine ⟨r', Eb, hrr, ⟨u, kc, hkc, hkcj, hku⟩, hE, hEe, hEh, ?_⟩
  rw [← hTE]
  exact ancestorEq_trans hT' hY'Y

/-- **`head_height_floor` above the threshold is the height of a line source.** Up to the support
cutoff of slot `σ + 2`, in the phase, when the invariant holds at every slot up to `σ` and an honest
validator's greatest chain-state height is at least `H₂ + 2`: its state is not contested, and its
`head_height_floor`, the greatest chain-state height minus one, is the chain-state height of a line
source of the first slot of a round to whose action time an honest validator ticked a step before the reading (the entry at the
greatest chain-state height minus one, `tall_entry_round`; the contest argument of
`viable_candidate`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed.

Read aloud: when an honest validator's greatest chain-state height is at least `H₂ + 2`, its
`head_height_floor` is the chain-state height of a line source of a round's first slot to whose action time an honest validator ticked a step before the reading. -/
theorem floor_source (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {σ t : ℕ}
    {w : V} (hG : ∀ σ', σ' ≤ σ → LineInv M S A x r H₂ σ')
    (hEnd : M.supportCutoff S.C (σ + 2) ≤ tAwakeEnd) (ht1 : 1 ≤ t)
    (ht : (t : ℝ) ≤ ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) - ΔClockAhead) (hw : w ∉ A.corruptedAtTime x t)
    (hM2 : H₂ + 2 ≤ hMax M S.C (x.stateBefore t w)) :
    ∃ (r' : ℕ) (E : Block V), r ≤ r' ∧ (∃ (u : V) (k : ℕ), x.lbl k = Event.tick u (aR M S r') ∧ k < x.stepBefore t ∧ u ∈ A.active k) ∧
      LineSource M S A x r H₂ (r' * S.C.R) E ∧
      M.head_height_floor (x.stateBefore t w) = (M.chainStateOf S.C E).h := by
  have hA0 := E.ahead_nonneg
  have hsk := hSkew
  have hEnd1 : M.supportCutoff S.C (σ + 1) ≤ tAwakeEnd :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (Nat.le_succ _)) hEnd
  have hcE : ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) ≤ (tAwakeEnd : ℕ) := by exact_mod_cast hEnd
  have hEndE : t ≤ tAwakeEnd := by
    have : ((t : ℕ) : ℝ) ≤ (tAwakeEnd : ℕ) := by linarith
    exact_mod_cast this
  -- every tick to the support cutoff of a slot up to `σ + 1` is in the phase (`hSkew`), as in `viable_candidate_of_held_st`
  have hEndT : ∀ μ'' : ℕ, μ'' ≤ σ → ∀ (u : V) (k : ℕ), x.lbl k = Event.tick u (M.supportCutoff S.C (μ'' + 1)) →
      x.time k ≤ tAwakeEnd := by
    intro μ'' hμ'' u k hk
    have hkt := (E.tick_active _ _ _ hk).2.2
    have hm := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
      (show μ'' + 1 ≤ σ + 1 by omega)
    have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_succ_eq M.toSlotLayout F.sched U) S (σ + 1)
    rw [show σ + 1 + 1 = σ + 2 from rfl] at h1
    have hc : ((M.supportCutoff S.C (μ'' + 1) : ℕ) : ℝ) + Δ S ≤ (tAwakeEnd : ℕ) := by
      exact_mod_cast (show M.supportCutoff S.C (μ'' + 1) + Δ S ≤ tAwakeEnd by omega)
    linarith
  -- a slot whose update ran at a tick before the reading is at most `σ`: a tick to the support cutoff of slot
  -- `σ + 2` or later is at a real time at least that cutoff less `ΔClockAhead`, so not before the reading
  have hslot : ∀ (μ' : ℕ) (u : V) (k : ℕ), x.lbl k = Event.tick u (M.supportCutoff S.C (μ' + 1)) →
      k < x.stepBefore t → μ' ≤ σ := by
    intro μ' u k hk hkj
    by_contra h
    have hmono := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
      (show σ + 2 ≤ μ' + 1 by omega)
    have hkt := (E.tick_active _ _ _ hk).2.1
    have h1 := ((lt_stepBefore_iff M) x R E).1 hkj
    have h2 := (time_mono M) x R (Nat.le_succ k)
    have h4 : ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) ≤ ((M.supportCutoff S.C (μ' + 1) : ℕ) : ℝ) := by
      exact_mod_cast hmono
    linarith
  have htj : x.time (x.stepBefore t) < t := ((stepBefore_time M) x R P.E ht1).1
  have hw' : w ∉ A.corrupted (x.stepBefore t) :=
    (not_mem_corrupted_of_le_time M) x R P.E hw htj.le
  have hjE : x.time (x.stepBefore t) ≤ tAwakeEnd := by
    have : ((t : ℕ) : ℝ) ≤ (tAwakeEnd : ℕ) := by exact_mod_cast hEndE
    linarith
  obtain ⟨-, ⟨Y, hY, hYh⟩, -⟩ := (GoldilocksCorrectness.Record.Proofs.Executions.cachesWitnessed_of_stateBefore M F) S A x R E t w
  obtain ⟨r', Eb, hrr, hcut, hE, -, hEh, -⟩ := P.tall_entry_round M F R E U Fx ht1 hEndE hw hY
    (by rw [hYh]; exact hM2)
  rw [hYh] at hEh
  -- the state is not contested
  have hnc : M.fg_contest (x.stateBefore t w) = false := by
    cases hcs : M.fg_contest (x.stateBefore t w)
    · rfl
    exfalso
    obtain ⟨hbox, B, hBT, -, hBh, hJB⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.fg_contest_spec M F) S.C S.P S.X _
      ((nodeInv_stateBefore_of_not_mem_corruptedAtTime M F) S A x R P.E le_rfl hw) hcs
    obtain ⟨μB, EB, ⟨uB, kB, hkB, hkjB, -⟩, hEB, hEBe, hEBh, hEBB⟩ := P.tall_entry M F R E U Fx ht1 hEndE hw hBT
      (by rw [hBh]; exact hM2)
    have hμB : μB ≤ σ := hslot μB uB kB hkB hkjB
    obtain ⟨⟨D, hD, hJD, hhjD⟩, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Executions.cachesWitnessed_of_stateBefore M F) S A x R E t w
    have hlt : H₂ < (M.chainStateOf S.C D).h_j := by
      rw [← hhjD]
      unfold Height at *
      omega
    obtain ⟨hJC, hJanc, hJh⟩ := ((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F)
      S.C D).1 (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le H₂) hlt))
    have hD' : D ∈ (x.st (x.stepBefore t) w).tree := hD
    have hJT : (M.chainStateOf S.C D).J ∈ (x.st (x.stepBefore t) w).tree :=
      (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E _ w D _ hD' hJanc
    obtain ⟨μJ, EJ, uJ, kJ, hkJ, hkjJ, -, hEJ, hEJe, hEJh, hEJr⟩ := P.cert_source M F R E U Fx hjE hD'
      ((GoldilocksCorrectness.Record.Proofs.Executions.progressCertOn_of_justificationCertOn M F) hJC) hlt
    have hμJ : μJ ≤ σ := hslot μJ uJ kJ hkJ hkjJ
    have hJE : (M.chainStateOf S.C D).J = EJ :=
      P.hRoots _ _ ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := x.stepBefore t) (v := w) hw' hjE hJT)
        ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_mono M) x
          (le_trans ((time_mono M) x R hkjJ.le) hjE) (P.source_inHonestTreeBy_tick M F R E U hEJ hkJ)) hEJr
    have hEE : EJ = EB := (GoldilocksCorrectness.Record.Proofs.Routines.entry_eq_of_compatible M F) S.C hEJe hEBe (by
        rw [hEJh, hEBh, ← hhjD, hBh, hbox]
        unfold Height at *
        omega)
      (P.sources_compatible M F R U hG hEnd hEJ hEB hμJ hμB)
    apply hJB
    rw [hJD, hJE, hEE]
    exact hEBB
  have hfloor : M.head_height_floor (x.stateBefore t w) = hMax M S.C (x.stateBefore t w) - 1 :=
    (GoldilocksCorrectness.Record.Proofs.Routines.head_height_floor_of_not_contested M F) S.C S.P S.X _
      ((nodeInv_stateBefore_of_not_mem_corruptedAtTime M F) S A x R P.E le_rfl hw) hnc
  exact ⟨r', Eb, hrr, hcut, hE, by rw [hfloor, hEh]⟩

/-- **`head_height_floor` is at most the height of a block on every early line source's chain.** Up
to the support cutoff of slot `σ + 2`, after the action time of round `r`, in the phase, when the
invariant holds at every slot up to `σ`: if every line source of the first slot of a round to whose action time an honest validator ticked a step before the reading is an ancestor of, or equal to, `Q`, then an honest validator's
`head_height_floor` is at most `Q`'s chain-state height.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed.

Read aloud: when every line source of a round's first slot to whose action time an honest validator ticked a step before the reading
is `Q` or an ancestor of `Q`, an honest validator's `head_height_floor` is at most `Q`'s chain-state
height. -/
theorem floor_le_of_sources (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {σ t : ℕ}
    {w : V} (hG : ∀ σ', σ' ≤ σ → LineInv M S A x r H₂ σ')
    (hEnd : M.supportCutoff S.C (σ + 2) ≤ tAwakeEnd) (ht0 : (∃ (u : V) (k : ℕ), x.lbl k = Event.tick u (aR M S r) ∧ k < x.stepBefore t ∧ u ∈ A.active k))
    (ht : (t : ℝ) ≤ ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) - ΔClockAhead) (hw : w ∉ A.corruptedAtTime x t) {Q : Block V}
    (hQ : ∀ (r' : ℕ) (E : Block V), r ≤ r' →
      (∃ (u : V) (k : ℕ), x.lbl k = Event.tick u (aR M S r') ∧ k < x.stepBefore t ∧ u ∈ A.active k) →
      LineSource M S A x r H₂ (r' * S.C.R) E → E.AncestorEq Q) :
    M.head_height_floor (x.stateBefore t w) ≤ (M.chainStateOf S.C Q).h := by
  have hEndR : M.supportCutoff S.C (r * S.C.R + 1) ≤ tAwakeEnd := P.hEnd
  have hLQ : L.AncestorEq Q := hQ r L le_rfl ht0 (P.source_L M F R U hEndR)
  have ht1 : 1 ≤ t := by
    -- the tick `k₀` comes before `x.stepBefore t`, so the step after it is at a real time less than `t`,
    -- and every real time of the trace is at least `0`
    obtain ⟨-, k₀, -, hk₀t, -⟩ := ht0
    have h1 := ((lt_stepBefore_iff M) x R E).1 hk₀t
    have h2 := (time_nonneg M) x R (k₀ + 1)
    exact Nat.cast_pos.1 (lt_of_le_of_lt h2 h1)
  have hLh := (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_height_mono M F) S.C hLQ
  rw [P.hL] at hLh
  by_cases hM : hMax M S.C (x.stateBefore t w) ≤ H₂ + 1
  · have := (GoldilocksCorrectness.Record.Proofs.Routines.floor_le_h_max_of_core M F) S.C S.P S.X (x.stateBefore t w) ((nodeInvCore_of_stateBefore M F) S A x R E t w)
    unfold Height at *
    omega
  · obtain ⟨r', E, hrr, htk, hE, hfl⟩ := P.floor_source M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hEnd ht1 ht hw
      (by unfold Height at *; omega)
    rw [hfl]
    exact (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_height_mono M F) S.C (hQ r' E hrr htk hE)

/-- **`tall_entry_round` at a step.** A block whose chain state has a height `h ≥ H₂ + 2`, held at step `j` by a
validator outside the adversary set there, in the phase, has an ancestor entry at the height `h − 1` that is a line
source of the first slot of a round `r' ≥ r` to whose action time an honest validator ticked at a step less than `j`
(`cert_source_round`). The body is `tall_entry_round`'s, read at `j` in place of the step before a time.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed; `j`: the step.

Read aloud: a block held at a step, two or more heights past `H₂`, has as an ancestor an entry block one height less
that is a line source of a round's first slot to whose action time an honest validator ticked before that step. -/
theorem tall_entry_round_st (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    {Δs : ℕ} {ΔNet : ℕ} (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {j : ℕ} {w : V}
    (hjE : x.time j ≤ tAwakeEnd) (hw' : w ∉ A.corrupted j) {Y : Block V}
    (hY : Y ∈ (x.st j w).tree) (hYh : H₂ + 2 ≤ (M.chainStateOf S.C Y).h) :
    ∃ (r' : ℕ) (E : Block V), r ≤ r' ∧ (∃ (u : V) (k : ℕ), x.lbl k = Event.tick u (aR M S r') ∧
        k < j ∧ u ∈ A.active k) ∧
      LineSource M S A x r H₂ (r' * S.C.R) E ∧ IsEntry M S.C E ∧
      (M.chainStateOf S.C E).h = (M.chainStateOf S.C Y).h - 1 ∧ E.AncestorEq Y := by
  obtain ⟨Y', hY'Y, -, -, -, hT', hcert⟩ :=
    (GoldilocksCorrectness.Record.Statements.Routines.lem67_first_advance M F) S.C Y
      ((M.chainStateOf S.C Y).h - 1) (by unfold Height at *; omega) (by unfold Height at *; omega)
  have hY'T := (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E _ w Y Y' hY hY'Y
  have hT'T := (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E _ w Y' _ hY'T hT'
  obtain ⟨r', Eb, u, kc, hrr, hkc, hkcj, hku, hE, hEe, hEh, hEr⟩ := P.cert_source_round M F R E U Fx hjE hY'T hcert
    (by unfold Height at *; omega)
  have hTE := P.hRoots _ _ ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := j) (v := w) hw' hjE hT'T)
    ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_mono M) x (le_trans ((time_mono M) x R hkcj.le) hjE) (P.source_inHonestTreeBy_tick M F R E U hE hkc)) hEr
  refine ⟨r', Eb, hrr, ⟨u, kc, hkc, hkcj, hku⟩, hE, hEe, hEh, ?_⟩
  rw [← hTE]
  exact ancestorEq_trans hT' hY'Y

/-- **`floor_source` at a step.** `floor_source` read at the step `j` in place of the step before a time
(rule R3: a validator's own state at its own tick): at a step `j` whose real time is less than the support cutoff of
slot `σ + 2` minus `ΔClockAhead`, in the phase, when the invariant holds at every slot up to `σ` and a validator
outside the adversary set at `j` has its greatest chain-state height at least `H₂ + 2`: its state is not contested,
and its `head_height_floor` is the chain-state height of a line source of the first slot of a round to whose action
time an honest validator ticked at a step less than `j` (`tall_entry_round_st`, `tall_entry_st`, `cert_source`).
The body is `floor_source`'s, read at `j`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed; `j`: the step.

Read aloud: when a validator honest at a step has its greatest chain-state height at least `H₂ + 2`, its
`head_height_floor` there is the chain-state height of a line source of a round's first slot to whose action time an
honest validator ticked before that step. -/
theorem floor_source_st (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {σ j : ℕ}
    {w : V} (hG : ∀ σ', σ' ≤ σ → LineInv M S A x r H₂ σ')
    (hEnd : M.supportCutoff S.C (σ + 2) ≤ tAwakeEnd)
    (hjt : x.time j < ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) - ΔClockAhead) (hw' : w ∉ A.corrupted j)
    (hM2 : H₂ + 2 ≤ hMax M S.C (x.st j w)) :
    ∃ (r' : ℕ) (E : Block V), r ≤ r' ∧ (∃ (u : V) (k : ℕ), x.lbl k = Event.tick u (aR M S r') ∧ k < j ∧ u ∈ A.active k) ∧
      LineSource M S A x r H₂ (r' * S.C.R) E ∧
      M.head_height_floor (x.st j w) = (M.chainStateOf S.C E).h := by
  have hA0 := E.ahead_nonneg
  have hsk := hSkew
  have hcE : ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) ≤ (tAwakeEnd : ℕ) := by exact_mod_cast hEnd
  have hjE : x.time j ≤ tAwakeEnd := by linarith
  -- a slot whose update ran at a tick before `j` is at most `σ`: a tick to the support cutoff of slot `σ + 2` or
  -- later is at a real time at least that cutoff less `ΔClockAhead`, so not before `j`
  have hslot : ∀ (μ' : ℕ) (u : V) (k : ℕ), x.lbl k = Event.tick u (M.supportCutoff S.C (μ' + 1)) →
      k < j → μ' ≤ σ := by
    intro μ' u k hk hkj
    by_contra h
    have hmono := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
      (show σ + 2 ≤ μ' + 1 by omega)
    have hkt := (E.tick_active _ _ _ hk).2.1
    have h2 := (time_mono M) x R hkj.le
    have h4 : ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) ≤ ((M.supportCutoff S.C (μ' + 1) : ℕ) : ℝ) := by
      exact_mod_cast hmono
    linarith
  have hInv := ((lem11_node_invariant M F) S A x R E j w hw').1
  obtain ⟨-, ⟨Y, hY, hYh⟩, -⟩ := (GoldilocksCorrectness.Record.Proofs.Executions.cachesWitnessed_of_exec M F) S A x R E j w
  obtain ⟨r', Eb, hrr, hcut, hE, -, hEh, -⟩ := P.tall_entry_round_st M F R E U Fx hjE hw' hY
    (by rw [hYh]; exact hM2)
  rw [hYh] at hEh
  -- the state is not contested
  have hnc : M.fg_contest (x.st j w) = false := by
    cases hcs : M.fg_contest (x.st j w)
    · rfl
    exfalso
    obtain ⟨hbox, B, hBT, -, hBh, hJB⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.fg_contest_spec M F) S.C S.P S.X _
      hInv hcs
    obtain ⟨μB, EB, ⟨uB, kB, hkB, hkjB, -⟩, hEB, hEBe, hEBh, hEBB⟩ := P.tall_entry_st M F R E U Fx hjE hw' hBT
      (by rw [hBh]; exact hM2)
    have hμB : μB ≤ σ := hslot μB uB kB hkB hkjB
    obtain ⟨⟨D, hD, hJD, hhjD⟩, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Executions.cachesWitnessed_of_exec M F) S A x R E j w
    have hlt : H₂ < (M.chainStateOf S.C D).h_j := by
      rw [← hhjD]
      unfold Height at *
      omega
    obtain ⟨hJC, hJanc, hJh⟩ := ((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F)
      S.C D).1 (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le H₂) hlt))
    have hJT : (M.chainStateOf S.C D).J ∈ (x.st j w).tree :=
      (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E _ w D _ hD hJanc
    obtain ⟨μJ, EJ, uJ, kJ, hkJ, hkjJ, -, hEJ, hEJe, hEJh, hEJr⟩ := P.cert_source M F R E U Fx hjE hD
      ((GoldilocksCorrectness.Record.Proofs.Executions.progressCertOn_of_justificationCertOn M F) hJC) hlt
    have hμJ : μJ ≤ σ := hslot μJ uJ kJ hkJ hkjJ
    have hJE : (M.chainStateOf S.C D).J = EJ :=
      P.hRoots _ _ ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := j) (v := w) hw' hjE hJT)
        ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_mono M) x
          (le_trans ((time_mono M) x R hkjJ.le) hjE) (P.source_inHonestTreeBy_tick M F R E U hEJ hkJ)) hEJr
    have hEE : EJ = EB := (GoldilocksCorrectness.Record.Proofs.Routines.entry_eq_of_compatible M F) S.C hEJe hEBe (by
        rw [hEJh, hEBh, ← hhjD, hBh, hbox]
        unfold Height at *
        omega)
      (P.sources_compatible M F R U hG hEnd hEJ hEB hμJ hμB)
    apply hJB
    rw [hJD, hJE, hEE]
    exact hEBB
  have hfloor : M.head_height_floor (x.st j w) = hMax M S.C (x.st j w) - 1 :=
    (GoldilocksCorrectness.Record.Proofs.Routines.head_height_floor_of_not_contested M F) S.C S.P S.X _ hInv hnc
  exact ⟨r', Eb, hrr, hcut, hE, by rw [hfloor, hEh]⟩

/-- **`floor_le_of_sources` at a step.** `floor_le_of_sources` read at the step `j` in place of the step before a
time (rule R3): at a step `j` whose real time is less than the support cutoff of slot `σ + 2` minus `ΔClockAhead`,
after a tick to the action time of round `r` at a step less than `j`, in the phase, when the invariant holds at every
slot up to `σ`: if every line source of the first slot of a round to whose action time an honest validator ticked at
a step less than `j` is `Q` or an ancestor of `Q`, then the `head_height_floor` of a validator outside the adversary
set at `j` is at most `Q`'s chain-state height (`floor_source_st`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed; `j`: the step.

Read aloud: when every line source of a round's first slot to whose action time an honest validator ticked before a
step is `Q` or an ancestor of `Q`, a validator honest at that step has its `head_height_floor` at most `Q`'s
chain-state height. -/
theorem floor_le_of_sources_st (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {σ j : ℕ}
    {w : V} (hG : ∀ σ', σ' ≤ σ → LineInv M S A x r H₂ σ')
    (hEnd : M.supportCutoff S.C (σ + 2) ≤ tAwakeEnd)
    (ht0 : ∃ (u : V) (k : ℕ), x.lbl k = Event.tick u (aR M S r) ∧ k < j ∧ u ∈ A.active k)
    (hjt : x.time j < ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) - ΔClockAhead) (hw' : w ∉ A.corrupted j) {Q : Block V}
    (hQ : ∀ (r' : ℕ) (E : Block V), r ≤ r' →
      (∃ (u : V) (k : ℕ), x.lbl k = Event.tick u (aR M S r') ∧ k < j ∧ u ∈ A.active k) →
      LineSource M S A x r H₂ (r' * S.C.R) E → E.AncestorEq Q) :
    M.head_height_floor (x.st j w) ≤ (M.chainStateOf S.C Q).h := by
  have hEndR : M.supportCutoff S.C (r * S.C.R + 1) ≤ tAwakeEnd := P.hEnd
  have hLQ : L.AncestorEq Q := hQ r L le_rfl ht0 (P.source_L M F R U hEndR)
  have hLh := (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_height_mono M F) S.C hLQ
  rw [P.hL] at hLh
  by_cases hM : hMax M S.C (x.st j w) ≤ H₂ + 1
  · have := (GoldilocksCorrectness.Record.Proofs.Routines.floor_le_h_max_of_core M F) S.C S.P S.X (x.st j w)
      ((lem11_node_invariantCore_of_run M F) S x R j w).1
    unfold Height at *
    omega
  · obtain ⟨r', E, hrr, htk, hE, hfl⟩ := P.floor_source_st M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hEnd hjt hw'
      (by unfold Height at *; omega)
    rw [hfl]
    exact (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_height_mono M F) S.C (hQ r' E hrr htk hE)

/-- **From slot `r * R + k` on, the live locks a member holds at the vote time of the next slot are
on line sources of slots `μ` with `μ + 1 ≤ s`.** Every such lock is of a slot `μ ≥ s + 1 − k`
(Lemma 41), so `μ ≥ r * R + 1`, and its block is a line source of slot `μ` (`source_lock`,
Lemma 39: the lock is on a confirmation fast or passing the slow test); the update of slot `μ` ran
before the vote time of slot `s + 1`, so `μ < s`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `P`, the phase's hypotheses with the fast block `L` of `v`'s update at the action time of round
  `r`; `s`, the slot; `u`, a member of `Hon M S Sched s`.

Read aloud: one lock lifetime after the fast block's round, every live lock is on the line. -/
theorem late_locks_on_sources (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (U : UniformSchedule M.toSlotLayout)
    {Δs : ℕ} {ΔNet : ℕ} (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {s : ℕ}
    (hs : r * S.C.R + S.C.k ≤ s) (hEnd : M.voteTime S.C (s + 1) ≤ tAwakeEnd) {u : V}
    (hu : u ∈ Hon M S A x s) :
    LiveLocksOnFamilyAt M S A x
      (fun C => ∃ μ : ℕ, μ + 1 ≤ s ∧ LineSource M S A x r H₂ μ C) s u := by
  have hk := S.C.k_ge_two
  refine (GoldilocksCorrectness.Record.Proofs.Executions.liveLocksOnFamilyAt_of_live M F U) S A x R E _ s u (fun e he hl => ?_)
  have hl' := hl
  simp only [(GoldilocksCorrectness.Record.Proofs.Routines.is_live_iff M F)] at hl'
  obtain ⟨hv1, hc1, -, -, hΔ⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (s + 1)
  have hu' : u ∉ A.corruptedAtTime x (M.voteTime S.C (s + 1)) := by
    unfold Hon roundMembers at hu
    exact (not_mem_corruptedAtTime_of_le M) x R E (by exact_mod_cast (show
      M.voteTime S.C (s + 1) ≤ M.supportCutoff S.C (s + 1) by omega)) ((Finset.mem_sdiff.1 hu).2)
  obtain ⟨μ, hd, hcut, -, hsrc⟩ := P.source_lock M F R E U hu' hEnd he
  have hlo : s + 1 - S.C.k ≤ μ :=
    (GoldilocksCorrectness.Record.Statements.Executions.lem41_slot_of_live_entry M F U) S (s + 1 - S.C.k) μ
      (M.voteTime S.C (s + 1)) e hd hl'.1 (by rw [show s + 1 - S.C.k + S.C.k = s + 1 by omega])
  have hhi : μ < s := by
    by_contra h
    have := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (show s + 1 ≤ μ + 1 by omega)
    omega
  exact ⟨μ, by omega, hsrc (by omega)⟩

end PartAHyps

/-- **An honest updater of slot `s` whose finalized block is on `B`'s chain saves `B` (C3's per-member step).** Under
C3's hypotheses with clauses 1 and 3 of `RoundBaseAt` (`hBase1`, `hBase3`) in place of the round base: an updater `u` of
slot `s`, outside the adversary set at the step of its own tick to the support cutoff of slot `s + 1`, whose finalized
block in the state that tick starts from is `B` or an ancestor of `B`, saves `B` as its confirmation of slot `s` at that tick. C1
(`round_base_after_fast_block_opening`) calls it at each step of its induction on the members' ticks to that cutoff,
and C3 at every updater. The updater's honesty is read at its own tick (T-C-91-3, rule R3), as
`updaterAt` gives it, so that C1 calls it at every updater whatever the adversary set at the real time of that cutoff.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed.

Read aloud: an honest updater of slot `s` whose finalized block at its tick to the slot's update is on `B`'s chain
saves `B` as its confirmation of slot `s`. -/
theorem updater_saves_of_finalized_on_proposal (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd s : ℕ) (B : Block V)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (s + 1)))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hs1 : 1 ≤ s) (hAnchor : anchorCW S tGAT ≤ M.slotStart S.C (s + 1))
    (hA : anchorCW S tGAT ≤ M.slotStart S.C s)
    (hEnd : M.supportCutoff S.C (s + 2) ≤ tAwakeEnd)
    (hp : S.P.proposer s ∉ A.corruptedAtTime x (M.supportCutoff S.C s))
    (hB : ProposalAt M S x s B)
    (hBase1 : ∀ w ∈ Hon M S A x s, (M.get_fc_root (x.tickInput w (M.voteTime S.C s))).AncestorEq B.parent ∧
      M.head_height_floor (x.tickInput w (M.voteTime S.C s)) ≤ (M.chainStateOf S.C B.parent).h)
    (hBase3 : ∀ w ∈ Hon M S A x s, ∀ (n₁ : M.N) (sent₁ : List (NamedObject V)),
      .ok (n₁, sent₁) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C s)) ((M.voteTime S.C s : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C s)) s →
      ∀ e ∈ M.lockEntries n₁, M.is_live (x.tickInput w (M.voteTime S.C s)) ((M.voteTime S.C s : ℕ) : Int) e = true →
        e.B.AncestorEq B.parent)
    (hNoCol : ¬ RootCollisionAtProposal M S A x s B)
    (hPrev : ∀ u ∈ S.P.committee (s - 1) ∩ Hon M S A x (s - 1), ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s - 1)) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x.sent (i + 1) - x.sent i) →
      ∃ H_u ∈ (x.tickInput u (M.voteTime S.C (s - 1))).tree,
        vote = GoldfishVote.mk u (s - 1) H_u.root ∧
        (M.get_anchor (x.tickInput (S.P.proposer s) (M.slotStart S.C s))
          ((M.slotStart S.C s : ℕ) : Int)).AncestorEq H_u) :
    ∀ u ∈ updaterAt M S A x s, u ∉ A.corrupted (x.tickStep u (M.supportCutoff S.C (s + 1))) →
      (x.tickInput u (M.supportCutoff S.C (s + 1))).finalized.AncestorEq B →
      (x.tickOutput u (M.supportCutoff S.C (s + 1))).savedConfirmation s = some B := by
  -- `healed_round_updates_upTo` at the one updater `u`: nothing is read of `u` after its tick
  intro u hu _ hFin
  refine ((healed_round_updates_upTo M F U Fx) S A x R GST tGAT tAwakeEnd s B (E.upTo _) hNet hSkew hRedeliver (Sy.upTo _)
    hΔs hRoots hParent hGST hThird hAwake hActive hCommittees hs1 hAnchor hA hEnd hp hB hBase1 hBase3 hNoCol hPrev {u}
    (fun v hv => by rw [Finset.mem_singleton.1 hv]; exact hu)
    (fun v hv => by rw [Finset.mem_singleton.1 hv]; exact hFin)).1 u (Finset.mem_singleton_self u)

/-- **C3, Lemma 89's base facts at the healed round (copy with the previous slot's votes and no
root collision).** The proof; the audited statement is in
`Statements/Executions/Lemma89Statements.lean`. Why: `round_base_steps` with the members
`Hon M S Sched s`, the previous slot's voters the committee's members of `Hon M S Sched (s − 1)`
with `X` the proposer's anchor (`hPrev`), the proposer's viable head on its anchor's chain
(`anchor_has_viable_head`), the values of `head_height_floor` ordered by delivery
(`floor_le_of_delivery_unordered`), the round base's three clauses, the slot's only block
(`only_block_of_unforgeability`) and the fresh root (`hNoCol`); then the restriction to the honest
active validators and the updaters, the saved confirmation read after the update
(`state_saved_of_update`), and the parent in the viable tree (`get_anchor_root_or_viable`).

Roots name blocks until `M.supportCutoff S.C (s + 1)`: the members' update of slot `s`
(`round_base_steps`), the latest time the proof reads.

 at both clock
bounds `0` it is `dev`'s state before the start of slot `s`.

 at both clock
bounds `0` it is `dev`'s state before the start of slot `s`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed.

Read aloud: at a round whose base holds, whose proposal's root is fresh and whose previous slot's
honest votes extend the proposer's anchor, every honest vote is for the proposal, every honest
update confirms it, and the proposal is the slot's. -/
theorem healed_round_base_of_prev_votes (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd s : ℕ) (B : Block V)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (s + 1)))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hs1 : 1 ≤ s) (hAnchor : anchorCW S tGAT ≤ M.slotStart S.C (s + 1))
    (hA : anchorCW S tGAT ≤ M.slotStart S.C s)
    (hEnd : M.supportCutoff S.C (s + 2) ≤ tAwakeEnd)
    (hp : S.P.proposer s ∉ A.corruptedAtTime x (M.supportCutoff S.C s))
    (hB : ProposalAt M S x s B)
    (hBase : RoundBaseAt M S A x B s)
    (hNoCol : ¬ RootCollisionAtProposal M S A x s B)
    (hPrev : ∀ u ∈ S.P.committee (s - 1) ∩ Hon M S A x (s - 1), ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s - 1)) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x.sent (i + 1) - x.sent i) →
      ∃ H_u ∈ (x.tickInput u (M.voteTime S.C (s - 1))).tree,
        vote = GoldfishVote.mk u (s - 1) H_u.root ∧
        (M.get_anchor (x.tickInput (S.P.proposer s) (M.slotStart S.C s))
          ((M.slotStart S.C s : ℕ) : Int)).AncestorEq H_u) :
    HonestChainExtends M S A x (honestActiveAt M S A x s) B s ∧
    (∀ u ∈ updaterAt M S A x s,
      (x.tickOutput u (M.supportCutoff S.C (s + 1))).savedConfirmation s = some B) ∧
    B.slot = s ∧
    B.parent ∈ M.viable_tree (M.fg_to_ac (x.tickInput (S.P.proposer s) (M.slotStart S.C s)))
      (M.fg_to_ac (x.tickInput (S.P.proposer s) (M.slotStart S.C s))).tree := by
  -- the second conclusion at every updater: the helper, with the finalized block on `B`'s chain from
  -- clause 2 of the round base (the root at the updater's own tick, `F_ancestorEq_fc_root_of_exec`)
  have hSaved : ∀ u ∈ updaterAt M S A x s,
      (x.tickOutput u (M.supportCutoff S.C (s + 1))).savedConfirmation s = some B := by
    intro u hu
    obtain ⟨k, hk, -⟩ := Activity.mem_activeThroughoutToTick.1 hu
    have huk : u ∉ A.corrupted k := E.not_mem_corrupted_of_tick hk
    have hti : x.tickInput u (M.supportCutoff S.C (s + 1)) = x.st k u := by
      unfold Trace.tickInput
      rw [(tickStep_eq_of_lbl M) x E hk]
    refine (updater_saves_of_finalized_on_proposal M F U Fx) S A x R GST tGAT tAwakeEnd s B E hNet hSkew hRedeliver Sy hΔs
      hRoots hParent hGST hThird hAwake hActive hCommittees hs1 hAnchor hA hEnd hp hB hBase.1 hBase.2.2 hNoCol hPrev u hu
      (by rw [(tickStep_eq_of_lbl M) x E hk]; exact huk) ?_
    have h2 := (hBase.2.1 u hu).1
    rw [hti] at h2 ⊢
    exact ancestorEq_trans
      ((GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F) S A x R E k u) h2
  -- the third: the proposal is of slot `s` (`proposal_parent_walk_end` at the proposer's tick)
  have hBslot : B.slot = s := by
    obtain ⟨s₀, rfl⟩ : ∃ s₀, s = s₀ + 1 := ⟨s - 1, by omega⟩
    obtain ⟨i, hl, hsent⟩ := hB
    exact ((proposal_parent_walk_end M F U) S A x R E s₀ i B (S.P.proposer (s₀ + 1)) hl hsent).1
  -- the first: `healed_round_votes_upTo` and `healed_round_updates_upTo` at the honest active validators, each an
  -- updater of slot `s` (`hActive`) with its finalized block on `B`'s chain (clause 2)
  have hFinOf : ∀ u ∈ updaterAt M S A x s, (x.tickInput u (M.supportCutoff S.C (s + 1))).finalized.AncestorEq B := by
    intro u hu
    obtain ⟨k, hk, -⟩ := Activity.mem_activeThroughoutToTick.1 hu
    have hti : x.tickInput u (M.supportCutoff S.C (s + 1)) = x.st k u := by
      unfold Trace.tickInput
      rw [(tickStep_eq_of_lbl M) x E hk]
    have h2 := (hBase.2.1 u hu).1
    rw [hti] at h2 ⊢
    exact ancestorEq_trans
      ((GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F) S A x R E k u) h2
  have hHonA : ∀ u ∈ honestActiveAt M S A x s, u ∈ Hon M S A x s := by
    intro u hu
    unfold Hon roundMembers
    exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _, fun h => (Finset.mem_sdiff.1 hu).2 (Finset.mem_union_left _ h)⟩
  have hUpdA : ∀ u ∈ honestActiveAt M S A x s, u ∈ updaterAt M S A x s := by
    intro u hu
    have hdw := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_of_anchor M.toSlotLayout F.sched U) S tGAT s
      hAnchor
    exact (hActive s (by omega)
      (le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)) hEnd)
      u (fun h => (Finset.mem_sdiff.1 hu).2 (Finset.mem_union_left _ h))).2
  have hRest1 : HonestChainExtends M S A x (honestActiveAt M S A x s) B s := by
    obtain ⟨hHeld, hVote, -⟩ := (healed_round_votes_upTo M F U Fx) S A x R GST tGAT tAwakeEnd s B (E.upTo _) hNet hSkew
      hRedeliver (Sy.upTo _) hΔs hRoots hParent hGST hThird hAwake hActive hCommittees hs1 hAnchor hA hEnd hp hB hBase.1
      hBase.2.2 hNoCol hPrev
    obtain ⟨-, hLocks, -⟩ := (healed_round_updates_upTo M F U Fx) S A x R GST tGAT tAwakeEnd s B (E.upTo _) hNet hSkew
      hRedeliver (Sy.upTo _) hΔs hRoots hParent hGST hThird hAwake hActive hCommittees hs1 hAnchor hA hEnd hp hB hBase.1
      hBase.2.2 hNoCol hPrev (honestActiveAt M S A x s) hUpdA (fun v hv => hFinOf v (hUpdA v hv))
    refine ⟨fun u hu vote hSend => ⟨B, hHeld u (hHonA u hu), hVote u (hHonA u hu) vote hSend, ancestorEq_refl B⟩,
      fun w hw n'' sent hrun hA' e he _ => hLocks w hw n'' sent hrun hA' e he, fun v hv C' hC' => ?_⟩
    rw [hSaved v (hUpdA v hv)] at hC'
    cases hC'
    exact ancestorEq_refl B
  have hRest4 : B.parent ∈ M.viable_tree (M.fg_to_ac (x.tickInput (S.P.proposer s) (M.slotStart S.C s)))
      (M.fg_to_ac (x.tickInput (S.P.proposer s) (M.slotStart S.C s))).tree := by
    obtain ⟨s₀, rfl⟩ : ∃ s₀, s = s₀ + 1 := ⟨s - 1, by omega⟩
    obtain ⟨i, hl, hsent⟩ := hB
    obtain ⟨-, -, -, hBend⟩ := (proposal_parent_walk_end M F U) S A x R E s₀ i B (S.P.proposer (s₀ + 1)) hl hsent
    rcases hBend with h | h
    · exact h
    · rw [h]
      rcases (GoldilocksCorrectness.Record.Proofs.Routines.get_anchor_root_or_viable M F)
          (x.tickInput (S.P.proposer (s₀ + 1)) (M.slotStart S.C (s₀ + 1))) ((M.slotStart S.C (s₀ + 1) : ℕ) : Int)
        with h' | h'
      · rw [h']
        -- every fact below is of the proposer's node state at its tick to the start of slot `s₀ + 1`
        have hI := (nodeInv_tickInput_of_tick M F) S A x R E hl
        obtain ⟨W, hW⟩ := (frame_has_viable_head_st M F) S A x R E
          (x.tickStep (S.P.proposer (s₀ + 1)) (M.slotStart S.C (s₀ + 1))) (S.P.proposer (s₀ + 1))
        obtain ⟨hWT, hFW, hRW, -⟩ :=
          ((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_heads_iff M F) S.C S.P S.X _ hI _).1 hW
        have hRT : (M.fg_to_ac (x.tickInput (S.P.proposer (s₀ + 1)) (M.slotStart S.C (s₀ + 1)))).fc_root ∈
            (x.tickInput (S.P.proposer (s₀ + 1)) (M.slotStart S.C (s₀ + 1))).tree :=
          (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E
            (x.tickStep (S.P.proposer (s₀ + 1)) (M.slotStart S.C (s₀ + 1))) (S.P.proposer (s₀ + 1)) W _ hWT hRW
        rw [(GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_tree_iff M F)]
        exact ⟨((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).2 ⟨hRT,
            by rw [(GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F)]
               exact (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F) S A x R E
                 (x.tickStep (S.P.proposer (s₀ + 1)) (M.slotStart S.C (s₀ + 1))) (S.P.proposer (s₀ + 1))⟩,
          ancestorEq_refl _, W, Finset.mem_inter.2 ⟨((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).2
            ⟨hWT, hFW⟩, hW⟩, hRW⟩
      · exact h'
  exact ⟨hRest1, hSaved, hBslot, hRest4⟩

/-! ## The rounds of a finalized block's certificates (F-P3-3-1) -/

/-- **An honest attestation's finality pair is at a height less than the attestation's.** At a tick that puts on the
wire an attestation `a` carrying a finality pair `p`, the pair's height is less than `a`'s height.

Why: the tick's attestation is the one the validator client builds (Lemma 49 over the record), which keeps a finality
pair only when its height is less than the source's height, the attestation's height (the argument of
`attest_tick_finality_pair_lt`, whose page this one does not import).

The variables:
- `M`: the model; `F`: its facts;
- `S`, `A`, `x`, `R`, `E`: the setup, the activity, the execution, the run's facts, the environment's facts;
  `i`: the step of the tick; `t`: its clock value; `v`: the attester; `a`: the attestation; `p`: its finality pair.

Read aloud: an honest attestation's finality pair is at a height less than the attestation's. -/
theorem finality_pair_lt_of_attest_tick (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {i t : ℕ} {v : V} {a : Attestation V}
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hl : x.lbl i = Event.tick v t)
    (hSent : (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈
      x.sent (i + 1) - x.sent i)
    {p : FinalityPair} (hp : a.finality_pair = some p) :
    p.hf < a.h := by
  obtain ⟨-, n', sent, hrun, ha, -, -⟩ := (tick_send_step_outcome_per_step M F R E) hl hSent
  have hts := (tickStep_eq_of_lbl M) x E hl
  have hInvT : M.nodeInv S.C S.P S.X (x.tickInput v t) := by
    unfold Trace.tickInput
    rw [hts]
    exact (lem11_node_invariant M F S A x R E i v (E.not_mem_corrupted_of_tick hl)).1
  obtain ⟨-, -, source, head, -, -, hAtt, -⟩ :=
    (GoldilocksCorrectness.Record.Statements.Routines.lem49_tick_attests F) S.C S.P S.X _ n' _ sent a
      hrun hInvT ha
  obtain ⟨τ, -, -, rfl⟩ := hAtt
  dsimp only at hp ⊢
  rcases hq : M.finality_pair (x.tickInput v t) (M.chainStateOf S.C head).h_j
      (M.chainStateOf S.C head).J.root (M.chainStateOf S.C head).h_F with _ | q
  · rw [hq] at hp
    exact absurd hp (by simp)
  · rw [hq] at hp
    dsimp only at hp
    split_ifs at hp with hle
    have hqp : q = p := Option.some.inj hp
    subst hqp
    exact Nat.lt_of_not_le hle

/-- **An honest attestation above `H₂` is built from a line source of its round's first slot.** An attestation `a`
that `u`'s tick `j'` to the clock value `t'` put on the wire, at a height greater than `H₂`, with `u` outside the
adversary set up to `j'` and at the action time of round `r`, `j'` in the phase: `t'` is the action time of a round
`r' ≥ r`, and `a` is built from a block `X` of `u`'s tick input there that is a line source of the first slot of
round `r'`, with `a`'s height as its chain-state height and `a`'s root as the root of its entry block `T_h(X)`.

Why: `cert_source_core_fast`'s argument from its honest member's sent attestation on. `t'` is at least `aR M S r`
(`hOld`), so it is the action time of a round `r' ≥ r` (`attest_time_round`); `a` is built from a fast block `X` of
`u`'s update (`fast_source_of_attestation`), saved on the confirmation of slot `r' * R` (`state_saved_of_update`),
with `u` an updater of that slot (awake from its tick to the duty window's start); when `r' = r`, `X` is `H_v` or an
ancestor of `H_v`, a block an honest committee member held at its tick to the vote time of slot `r * R`, so its
height is at most `H₂ + 1` (`held_height_le_before_action`), hence `H₂ + 1`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- the hypotheses of `cert_source_core_fast` but its certificate and reading; `j'`, `t'`: the tick and its clock
  value; `u`: the attester; `a`: the attestation.

Read aloud: an honest attestation above `H₂` put on the wire in the phase is built, at a round's action time, from a
line source of that round's first slot whose chain-state height is the attestation's height. -/
theorem attestation_line_source {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N}
    (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) {tGAT tAwakeEnd r H₂ : ℕ} {v : V}
    (hRoots : RootsNameBlocksUntil M A x tAwakeEnd)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hAnchor : anchorCW S tGAT ≤ M.slotStart S.C (r * S.C.R + 1))
    (hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂)
    (hEnd : aR M S r ≤ tAwakeEnd)
    (hk₀ : x.lbl (x.tickStep v (aR M S r)) = Event.tick v (aR M S r))
    (hOldStep : ∀ (k t : ℕ) (u : V) (a' : Attestation V), k < x.firstAt (M.supportCutoff S.C (r * S.C.R)) →
      x.lbl k = Event.tick u t → u ∉ A.corruptedAtTime x tAwakeEnd →
      (⟨u, NamedObject.attest a'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (k + 1) - x.sent k → a'.h ≤ H₂)
    (hEndStep : x.time (x.tickStep v (aR M S r)) ≤ tAwakeEnd)
    {j' t' : ℕ} {u : V} {a : Attestation V} (hl : x.lbl j' = Event.tick u t')
    (hsent : (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (j' + 1) - x.sent j')
    (hhon : ∀ i : ℕ, i ≤ j' → u ∉ A.corrupted i) (huR : u ∉ A.corruptedAtTime x (aR M S r))
    (hj'E : x.time j' ≤ tAwakeEnd) (hH : H₂ < a.h) :
    ∃ r' : ℕ, r ≤ r' ∧ t' = aR M S r' ∧ ∃ X : Block V, X ∈ (x.tickInput u (aR M S r')).tree ∧
      LineSource M S A x r H₂ (r' * S.C.R) X ∧ (M.chainStateOf S.C X).h = a.h ∧
      (M.chainStateOf S.C X).T_h.root = a.T := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ := GoldilocksCorrectness.Proofs.Routines.one_le_Δ S
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  have hge : aR M S r ≤ t' := by
    by_contra hlt
    have hle := hOld j' t' u a hl (by exact_mod_cast Nat.lt_of_not_le hlt) huR hsent
    exact absurd hle (Nat.not_le.mpr hH)
  obtain ⟨r', rfl⟩ := (attest_time_round M F U) S A x R E hl hsent
  have hrr : r ≤ r' := by
    by_contra hlt
    have : r' * S.C.R + 1 < r * S.C.R + 1 := by
      have := Nat.mul_lt_mul_of_pos_right (Nat.lt_of_not_le hlt)
        (show 0 < S.C.R by have := S.C.R_ge_two; omega)
      omega
    have := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_lt M.toSlotLayout F.sched) S this
    exact absurd hge (Nat.not_le.mpr this)
  obtain ⟨n₀, X, hU, hXf, hXT, hXh, hXT'⟩ :=
    (fast_source_of_attestation M F U) S A x R E r' u a ⟨j', hl, hsent⟩
  -- `u` is an updater of slot `r' * R`: honest up to its tick `j'`, awake from its tick to the duty
  -- window's start of slot `r' * R + 1`
  have hkt := (E.tick_active j' u _ hl).2
  have hdws : tGAT + Δ S ≤ M.dutyWindowStart S.C (r' * S.C.R + 1) :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_of_anchor M.toSlotLayout F.sched U) S
      tGAT (r * S.C.R) hAnchor)
      ((GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_mono M.toSlotLayout F.sched) S
        (show r * S.C.R ≤ r' * S.C.R + 1 by have := Nat.mul_le_mul_right S.C.R hrr; omega))
  have hdw := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_succ_le_slotStart M.toSlotLayout F.sched) S
    (r' * S.C.R)
  have hT0 := (GoldilocksCorrectness.Record.Proofs.Routines.times_le M.toSlotLayout F.sched) S (r' * S.C.R)
  have hT1 := (GoldilocksCorrectness.Record.Proofs.Routines.times_le M.toSlotLayout F.sched) S (r' * S.C.R + 1)
  have hcR : ((M.dutyWindowStart S.C (r' * S.C.R + 1) : ℕ) : ℝ) + 4 * Δ S ≤ (aR M S r' : ℝ) := by
    have : M.dutyWindowStart S.C (r' * S.C.R + 1) + 4 * Δ S ≤ aR M S r' := by
      show _ ≤ M.supportCutoff S.C (r' * S.C.R + 1)
      omega
    exact_mod_cast this
  have hdwsR : ((tGAT : ℕ) : ℝ) + Δ S ≤ ((M.dutyWindowStart S.C (r' * S.C.R + 1) : ℕ) : ℝ) := by
    exact_mod_cast hdws
  obtain ⟨kc, hkc, hkc1, hkc2⟩ := E.tick_of_active (M.dutyWindowStart S.C (r' * S.C.R + 1)) (by omega) u
    (fun i h1 h2 => by
      have hij : i < j' := (lt_of_time_lt M) x R (by linarith)
      have hui := hhon i hij.le
      exact Activity.mem_active.2 ⟨hAwake i u (by linarith [htime hij.le]) (by linarith [htime (Nat.le_succ i)]) hui, hui⟩)
  have hkcj : kc ≤ j' := tick_step_le_of_le M F E hkc hl (by
    show M.dutyWindowStart S.C (r' * S.C.R + 1) ≤ M.supportCutoff S.C (r' * S.C.R + 1)
    omega)
  have hupd : u ∈ updaterAt M S A x (r' * S.C.R) := by
    show u ∈ A.activeThroughoutToTick x (Goldilocks.duty_window_start S.C (r' * S.C.R + 1))
      (M.supportCutoff S.C (r' * S.C.R + 1))
    refine Activity.mem_activeThroughoutToTick.2 ⟨j', hl, Or.inr ⟨kc, hkcj, M.dutyWindowStart S.C (r' * S.C.R + 1),
      (dutyWindowStart_le_duty_window_start M F U) S (by omega), hkc, fun i h1 h2 => ?_⟩⟩
    have hui := hhon i h2
    exact Activity.mem_active.2 ⟨hAwake i u (by linarith [htime h2]) (by linarith [htime h1, htime (Nat.le_succ i)]) hui, hui⟩
  have hst := (GoldilocksCorrectness.Record.Proofs.Executions.state_saved_of_update M F U) S A x R (r' * S.C.R) u n₀ E
    hupd hU
  obtain ⟨C₀, hC₀, hXC₀⟩ :=
    GoldilocksCorrectness.Record.Proofs.Routines.update_confirmation_fast_block_saved
      (Nat.le_add_left 1 _) hU hXf
  rw [Nat.add_sub_cancel] at hC₀
  have hkind : (r' * S.C.R = r * S.C.R ∧ X ∈ M.fastBlocks n₀ ∧ (M.chainStateOf S.C X).h = H₂ + 1) ∨
      (r * S.C.R + 1 ≤ r' * S.C.R ∧ (X ∈ M.fastBlocks n₀ ∨
        M.slow_test S.C (x.tickInput u (M.supportCutoff S.C (r' * S.C.R + 1))) (r' * S.C.R) X =
          true)) ∨
      r * S.C.R + S.C.k ≤ r' * S.C.R := by
    rcases Nat.lt_or_eq_of_le hrr with hlt | heq
    · refine Or.inr (Or.inl ⟨?_, Or.inl hXf⟩)
      have h1 := Nat.mul_le_mul_right S.C.R (show r + 1 ≤ r' by omega)
      have h2 := S.C.R_ge_two
      rw [Nat.succ_mul] at h1
      omega
    · subst heq
      refine Or.inl ⟨rfl, hXf, ?_⟩
      -- `X` is `H_v` or an ancestor of it, a block an honest committee member held at its tick to the
      -- vote time of slot `r * R`, a step before `v`'s tick to `aR M S r` (A2 there)
      have hRoots' : RootsNameBlocksUntil M A x ((M.supportCutoff S.C (r * S.C.R + 1) : ℕ) : ℝ) :=
        hRoots.mono M (by exact_mod_cast hEnd)
      obtain ⟨v', -, H_v, hHv, hXH⟩ :=
        (fast_block_has_honest_supporter_of_update M F U) S A x R (anchorCW S tGAT) (r * S.C.R) u E hSkew
          ((votesCastByOwner_of_unforgeability M F) S A x R E) hRoots'
          (hCommittees.mono M hEnd) hAnchor hupd n₀ hU X hXf
      have hk0t := (E.tick_active _ v _ hk₀).2.1
      have hT0' := (GoldilocksCorrectness.Record.Proofs.Routines.times_le M.toSlotLayout F.sched) S (r * S.C.R)
      have hT1' := (GoldilocksCorrectness.Record.Proofs.Routines.times_le M.toSlotLayout F.sched) S (r * S.C.R + 1)
      -- `v'`'s tick to the vote time of slot `r * R` comes before the first step reaching that slot's support cutoff
      have hvk : x.tickStep v' (M.voteTime S.C (r * S.C.R)) ≤ x.firstAt (M.supportCutoff S.C (r * S.C.R)) := by
        by_cases hex : ∃ i : ℕ, x.lbl i = Event.tick v' (M.voteTime S.C (r * S.C.R))
        · obtain ⟨i, hi⟩ := hex
          rw [(tickStep_eq_of_lbl M) x E hi]
          have hit := (E.tick_active i v' _ hi).2.2
          have hvt : ((M.voteTime S.C (r * S.C.R) : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (r * S.C.R) : ℕ) : ℝ) := by
            exact_mod_cast hT0'.2.1
          exact ((lt_firstAt_of_time_lt M F) R E (by linarith)).le
        · simp only [Trace.tickStep, hex, dif_neg, not_false_eq_true]
          exact Nat.zero_le _
      -- that first step is at or before `v`'s tick to `aR M S r`, so in the phase
      have hk0E : x.time (x.firstAt (M.supportCutoff S.C (r * S.C.R))) ≤ tAwakeEnd := by
        have hc : ((M.supportCutoff S.C (r * S.C.R) : ℕ) : ℝ) ≤ x.time (x.tickStep v (aR M S r)) := by
          have : M.supportCutoff S.C (r * S.C.R) + 4 * Δ S ≤ aR M S r := by
            show _ ≤ M.supportCutoff S.C (r * S.C.R + 1)
            omega
          have h4 : ((M.supportCutoff S.C (r * S.C.R) : ℕ) : ℝ) + 4 * Δ S ≤ (aR M S r : ℝ) := by exact_mod_cast this
          linarith
        exact le_trans ((time_mono M) x R ((firstAt_le_of_time_ge M F) R E hc)) hEndStep
      have hle := (held_height_le_before_action M F Fx) S A x R E tAwakeEnd H₂ (x.firstAt (M.supportCutoff S.C (r * S.C.R)))
        (x.tickStep v' (M.voteTime S.C (r * S.C.R))) v' H_v hThird hOldStep hk0E hvk hHv
      have hmono := (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_height_mono M F) S.C hXH
      rw [hXh] at hmono ⊢
      unfold Height at *
      omega
  exact ⟨r', hrr, rfl, X, hXT, ⟨u, hupd, n₀, C₀, X, hU, hC₀, hst.trans hC₀, ancestorEq_refl X, hXC₀, hkind⟩,
    hXh, hXT'⟩

/-- **A finalized block above `H₂` is on a line source of a round before an honest action tick.** For a block `D`
that `w`, outside the adversary set at step `j`, holds after `j` steps, in the phase, whose finalization height is
greater than `H₂`: there are two rounds `r₁ < r₂`, an honest validator's tick to the action time of round `r₂` a step
before `j`, and a line source of the first slot of round `r₁` that `D`'s finalized block is an ancestor of (or equal
to).

Why: the finalized block `F` has a justification certificate and a finality certificate at its height `h_F` on `D`'s
chain (Lemma 66); the two quorums meet in a validator `w'` outside the adversary set up to the later of `j` and the
action time of round `r` (Lemma 65, fewer than a third in the adversary set). `w'`'s target vote at `h_F` for `F`
and its attestation carrying the finality pair `(h_F, F)` (at a height greater than `h_F`,
`finality_pair_lt_of_attest_tick`) were put on the wire by ticks of `w'` before `j` (Lemma 74,
`record_content_sent_step`), at the action times of rounds `r_a` and `r_b` (`attestation_line_source`), built from
line sources `X_a` and `X_b` of the first slots of those rounds, of chain-state heights `h_F` and greater than `h_F`.
The rounds differ: one tick of `w'` puts on the wire attestations built from one source, of one height
(`tick_send_step_outcome_per_step`, Lemma 49). When `r_a < r_b`, `F` is the entry block of `X_a` (both are held by
honest validators in the phase and have one root, `hRoots`). When `r_b < r_a`, `F` is an ancestor of `X_b`, a block
an honest validator holds whose chain-state height is greater than `h_F` (Lemma 68).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- the hypotheses of `cert_source_core_fast` but its certificate; `j`: the reading step; `w`: the holder; `D`: the
  block.

Read aloud: a finalized block above `H₂` that an honest validator holds in the phase is an ancestor of a line source
of the first slot of a round earlier than a round to whose action time an honest validator ticked before the
reading. -/
theorem finalized_source_two_rounds {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N}
    (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) {tGAT tAwakeEnd r H₂ : ℕ} {v : V}
    (hRoots : RootsNameBlocksUntil M A x tAwakeEnd)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hAnchor : anchorCW S tGAT ≤ M.slotStart S.C (r * S.C.R + 1))
    (hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂)
    (hEnd : aR M S r ≤ tAwakeEnd)
    (hk₀ : x.lbl (x.tickStep v (aR M S r)) = Event.tick v (aR M S r))
    (hOldStep : ∀ (k t : ℕ) (u : V) (a' : Attestation V), k < x.firstAt (M.supportCutoff S.C (r * S.C.R)) →
      x.lbl k = Event.tick u t → u ∉ A.corruptedAtTime x tAwakeEnd →
      (⟨u, NamedObject.attest a'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (k + 1) - x.sent k → a'.h ≤ H₂)
    (hEndStep : x.time (x.tickStep v (aR M S r)) ≤ tAwakeEnd)
    {j : ℕ} {w : V} {D : Block V} (hjE : x.time j ≤ tAwakeEnd) (hw : w ∉ A.corrupted j)
    (hD : D ∈ (x.st j w).tree) (hF : H₂ < (M.chainStateOf S.C D).h_F) :
    ∃ r₁ r₂ : ℕ, r₁ < r₂ ∧ (∃ (u : V) (k : ℕ), x.lbl k = Event.tick u (aR M S r₂) ∧ k < j) ∧
      ∃ X : Block V, LineSource M S A x r H₂ (r₁ * S.C.R) X ∧ (M.chainStateOf S.C D).F.AncestorEq X := by
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  have hF1 : 1 ≤ (M.chainStateOf S.C D).h_F := Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le H₂) hF)
  obtain ⟨hJC, hFC, hFanc, -⟩ :=
    ((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) S.C D).2.2 hF1
  obtain ⟨X₁, hX₁D, Q₁, hq₁, hQ₁⟩ := hJC
  obtain ⟨X₂, hX₂D, Q₂, hq₂, hQ₂⟩ := hFC
  have hint := (GoldilocksCorrectness.Record.Proofs.Routines.lem65_quorum_intersection M F Fx) X₁ X₂ Q₁ Q₂ hq₁ hq₂
  -- a member of both quorums outside the adversary set up to the later of `j` and the action time of round `r`
  obtain ⟨w', hw'Q, hhonM⟩ : ∃ w' ∈ Q₁ ∩ Q₂, A.HonestThroughTime x (max (x.time j) (aR M S r)) w' := by
    by_contra hno
    have hall : ∀ v ∈ Q₁ ∩ Q₂, ∃ i : ℕ, x.time i ≤ max (x.time j) (aR M S r) ∧ v ∈ A.corrupted i := by
      intro v hv
      by_contra hn
      exact hno ⟨v, hv, fun i hi ha => hn ⟨i, hi, ha⟩⟩
    have h3 := (hThird.mono (max_le hjE (by exact_mod_cast hEnd))) _ hall
    have h2 := (GoldilocksCorrectness.Statements.Routines.lem65b_quorum_threshold (V := V)).1
    omega
  have hhon : x.HonestThrough A j w' :=
    fun i hi => hhonM i (le_trans ((time_mono M) x R hi) (le_max_left _ _))
  have huR : w' ∉ A.corruptedAtTime x (aR M S r) :=
    Activity.not_mem_corruptedAtTime.2 fun i hi => hhonM i (le_trans hi (le_max_right _ _))
  obtain ⟨hw'1, hw'2⟩ := Finset.mem_inter.1 hw'Q
  obtain ⟨a₁, ha₁v, ha₁h, ha₁T, -, ha₁on⟩ := hQ₁ w' hw'1
  obtain ⟨a₂, ha₂v, ha₂fp, ha₂on⟩ := hQ₂ w' hw'2
  -- both are recorded by `w'`, so put on the wire by ticks of `w'` before `j`
  have hrec₁ := (lem74_honest_attestations_recorded M F) S A x R E j w D a₁ hD
    ((GoldilocksCorrectness.Record.Proofs.Routines.on_chain_mono M F) a₁ hX₁D ha₁on) (by rw [ha₁v]; exact hhon)
  have hrec₂ := (lem74_honest_attestations_recorded M F) S A x R E j w D a₂ hD
    ((GoldilocksCorrectness.Record.Proofs.Routines.on_chain_mono M F) a₂ hX₂D ha₂on) (by rw [ha₂v]; exact hhon)
  rw [ha₁v] at hrec₁
  rw [ha₂v] at hrec₂
  obtain ⟨j₁, t₁, b₁, hj₁, hl₁, -, hs₁, -, hc₁, -⟩ := (record_content_sent_step M F) S A x R E w' j _ hrec₁
  obtain ⟨j₂, t₂, b₂, hj₂, hl₂, -, hs₂, -, hc₂, -⟩ := (record_content_sent_step M F) S A x R E w' j _ hrec₂
  have hb₁h : b₁.h = (M.chainStateOf S.C D).h_F := by
    rw [← ha₁h]
    exact congrArg AttestationContent.h hc₁
  have hb₁T : b₁.T = (M.chainStateOf S.C D).F.root := by
    rw [← ha₁T]
    exact congrArg AttestationContent.T hc₁
  have hb₂fp : b₂.finality_pair = some ⟨(M.chainStateOf S.C D).h_F, (M.chainStateOf S.C D).F.root⟩ := by
    rw [← ha₂fp]
    exact congrArg AttestationContent.finality_pair hc₂
  have hfp : (M.chainStateOf S.C D).h_F < b₂.h :=
    (finality_pair_lt_of_attest_tick M F) S A x R E hl₂ hs₂ hb₂fp
  have hj₁E : x.time j₁ ≤ tAwakeEnd := le_trans (htime hj₁.le) hjE
  have hj₂E : x.time j₂ ≤ tAwakeEnd := le_trans (htime hj₂.le) hjE
  obtain ⟨ra, -, rfl, Xa, hXaT, hXa, -, hXaT'⟩ :=
    (attestation_line_source M F) R E U Fx hSkew hRoots hThird hAwake hCommittees hAnchor hOld hEnd hk₀ hOldStep
      hEndStep hl₁ hs₁ (fun i hi => hhon i (by omega)) huR hj₁E (by rw [hb₁h]; exact hF)
  obtain ⟨rb, -, rfl, Xb, hXbT, hXb, hXbh, -⟩ :=
    (attestation_line_source M F) R E U Fx hSkew hRoots hThird hAwake hCommittees hAnchor hOld hEnd hk₀ hOldStep
      hEndStep hl₂ hs₂ (fun i hi => hhon i (by omega)) huR hj₂E (lt_trans hF hfp)
  -- the two rounds differ: one tick of `w'` puts on the wire attestations of one height
  have hne : ra ≠ rb := by
    intro hab
    subst hab
    have h12 : j₁ = j₂ := by
      rw [← (tickStep_eq_of_lbl M) x E hl₁, (tickStep_eq_of_lbl M) x E hl₂]
    subst h12
    obtain ⟨-, n', sent, hrun, hb₁s, -, hall⟩ := (tick_send_step_outcome_per_step M F R E) hl₁ hs₁
    have hb₂s := hall _ hs₂
    have hInvT : M.nodeInv S.C S.P S.X (x.tickInput w' (aR M S ra)) := by
      unfold Trace.tickInput
      rw [(tickStep_eq_of_lbl M) x E hl₁]
      exact (lem11_node_invariant M F S A x R E j₁ w' (E.not_mem_corrupted_of_tick hl₁)).1
    obtain ⟨-, -, s₁, hd₁, hsrc₁, -, hA₁, -⟩ :=
      (GoldilocksCorrectness.Record.Statements.Routines.lem49_tick_attests F) S.C S.P S.X _ n' _ sent b₁
        hrun hInvT hb₁s
    obtain ⟨-, -, s₂, hd₂, hsrc₂, -, hA₂, -⟩ :=
      (GoldilocksCorrectness.Record.Statements.Routines.lem49_tick_attests F) S.C S.P S.X _ n' _ sent b₂
        hrun hInvT hb₂s
    rw [hsrc₁] at hsrc₂
    obtain rfl := Option.some.inj hsrc₂
    obtain ⟨τ₁, -, -, rfl⟩ := hA₁
    obtain ⟨τ₂, -, -, rfl⟩ := hA₂
    dsimp only at hb₁h hfp
    rw [hb₁h] at hfp
    exact lt_irrefl _ hfp
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · -- `r_a < r_b`: `F` is the entry block of `X_a`
    refine ⟨ra, rb, hlt, ⟨w', j₂, hl₂, hj₂⟩, Xa, hXa, ?_⟩
    obtain ⟨-, -, hE3⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.isEntry_T_h M F) S.C Xa
    have hXast : Xa ∈ (x.st j₁ w').tree := by
      have h := hXaT
      unfold Trace.tickInput at h
      rwa [(tickStep_eq_of_lbl M) x E hl₁] at h
    have hEq : (M.chainStateOf S.C D).F = (M.chainStateOf S.C Xa).T_h := by
      apply hRoots
      · exact (GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E hw hjE
          ((GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E j w D _ hD hFanc)
      · exact (GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (hhon j₁ hj₁.le) hj₁E
          ((GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E j₁ w' Xa _
            hXast hE3)
      · rw [hXaT', hb₁T]
    rw [hEq]
    exact hE3
  · -- `r_b < r_a`: `F` is an ancestor of `X_b`, of chain-state height greater than `h_F` (Lemma 68)
    refine ⟨rb, ra, hlt, ⟨w', j₁, hl₁, hj₁⟩, Xb, hXb, ?_⟩
    have hXbst : Xb ∈ (x.st j₂ w').tree := by
      have h := hXbT
      unfold Trace.tickInput at h
      rwa [(tickStep_eq_of_lbl M) x E hl₂] at h
    exact (lem68_honest_past_finalized M F Fx) S A x R E hRoots j j₂ w w' D Xb
      (hThird.mono (max_le hjE hj₂E)) hw (hhon j₂ hj₂.le) hD hXbst (by rw [hXbh]; exact hfp) (max_le hjE hj₂E)

namespace PartAHyps
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

variable {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N}
  {GST tGAT tAwakeEnd r H₂ : ℕ} {v : V} {L : Block V} {n' : M.N}

/-- **A member saves a confirmation of slot `σ` when the honest votes of slot `σ` extend its finalized block.** For a
slot `σ ≥ r * R` with the support cutoff of slot `σ + 1` in the phase: when every vote of slot `σ` that a member of the
committee of slot `σ` in `Hon M S A x σ` put on the wire at its tick to the vote time of slot `σ` is for a block of that
tick's input that is the finalized block of `u`'s tick input at the support cutoff of slot `σ + 1` or a descendant of
it, every member `u` of `Hon M S A x σ` saves, at its tick to that cutoff, some confirmation of slot `σ`.

Why: `confirmation_saved_of_votes` with the members of the committee in `Hon M S A x σ` as the voters, read with the
bundle's own environment facts; the members are honest active validators and updaters of slot `σ` (`members_sets`),
outside the adversary set at `u`'s tick (`not_mem_corrupted_tickStep_of_outside_at_honest_ticks`), active through the
sync window of Lemma 12 (`activeThroughout_nat_of_awake_from`), more than half of the committee (`committee`), and roots
name blocks up to `u`'s tick to the support cutoff of slot `σ`, which is in the phase.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `P`: the bundle; `σ`: the slot of the votes; `u`: the member; `hV`: the votes clause.

Read aloud: a member saves a confirmation of a slot of the phase when every honest committee vote of that slot extends
the finalized block its update reads. -/
theorem member_saves_confirmation_of_votes (U : UniformSchedule M.toSlotLayout)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ}
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet)
    {σ : ℕ} (hσ : r * S.C.R ≤ σ) (hEnd : M.supportCutoff S.C (σ + 1) ≤ tAwakeEnd) {u : V}
    (hu : u ∈ Hon M S A x σ)
    (hV : ∀ w ∈ S.P.committee σ ∩ Hon M S A x σ, ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick w (M.voteTime S.C σ) ∧
        (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) →
      ∃ H_w ∈ (x.tickInput w (M.voteTime S.C σ)).tree,
        vote = GoldfishVote.mk w σ H_w.root ∧
        (x.tickInput u (M.supportCutoff S.C (σ + 1))).finalized.AncestorEq H_w) :
    ∃ C : Block V, (x.tickOutput u (M.supportCutoff S.C (σ + 1))).savedConfirmation σ = some C := by
  have hA0 := P.E.ahead_nonneg
  have hB0 := P.E.behind_nonneg
  have hsk := P.hSkew
  obtain ⟨hvt1, hc1, -, hs1, hΔ⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S σ
  obtain ⟨-, hc2, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 1)
  have hsets := P.members_sets M F U hσ hEnd
  have hvU : u ∈ updaterAt M S A x σ := hsets.2 hu
  have hcut1 : ∀ w : V, w ∈ Hon M S A x σ → w ∉ A.corruptedAtTime x (M.supportCutoff S.C (σ + 1)) := by
    intro w hw
    unfold Hon roundMembers at hw
    exact (Finset.mem_sdiff.1 hw).2
  -- the voters' blocks
  obtain ⟨H, hH⟩ := (voters_of_votes_clause M F U) S A x P.R σ (S.P.committee σ ∩ Hon M S A x σ) _ P.E P.hSkew
    (fun w hw => ⟨hsets.1 (Finset.mem_inter.1 hw).2, (Finset.mem_inter.1 hw).1⟩) hV
  -- roots name blocks up to `u`'s tick to the support cutoff of slot `σ`, which is in the phase
  have hRootsσ : RootsNameBlocksUntil M A x (x.time (x.tickStep u (M.supportCutoff S.C σ))) := by
    have hvU' := hvU
    unfold updaterAt at hvU'
    obtain ⟨kR, hkR, -⟩ := (updater_reader_gives_core_window M F U) x P.R P.E P.hΔs P.hSkew hvU'
    rw [(tickStep_eq_of_lbl M) x P.E hkR]
    have ht := (P.E.tick_active kR u _ hkR).2.2
    have hle : ((M.supportCutoff S.C σ : ℕ) : ℝ) + Δ S ≤ ((tAwakeEnd : ℕ) : ℝ) := by
      exact_mod_cast (show M.supportCutoff S.C σ + Δ S ≤ tAwakeEnd by omega)
    have hΔR : (1 : ℝ) ≤ (Δ S : ℝ) := by exact_mod_cast hΔ
    exact (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) (by linarith) P.hRoots
  -- every voter is outside the adversary set at `u`'s tick to the support cutoff of slot `σ + 1`
  have hHonTick : ∀ w ∈ S.P.committee σ ∩ Hon M S A x σ,
      w ∉ A.corrupted (x.tickStep u (M.supportCutoff S.C (σ + 1))) := by
    intro w hw
    classical
    have hw' := hsets.1 (Finset.mem_inter.1 hw).2
    have hvU' := hvU
    unfold honestActiveAt at hw'
    unfold updaterAt at hvU'
    have hX : w ∉ Finset.univ.filter (fun w => ∃ (k : ℕ) (w' : V),
        x.lbl k = Event.tick w' (M.supportCutoff S.C (σ + 1)) ∧ w' ∉ A.corrupted k ∧ w ∈ A.corrupted k) :=
      fun h => (Finset.mem_sdiff.1 hw').2 (Finset.mem_union.2 (Or.inr h))
    exact (not_mem_corrupted_tickStep_of_outside_at_honest_ticks M F) x P.E hvU' hX
  -- every voter is active through the sync window Lemma 12 reads
  have hHold : ∀ w ∈ S.P.committee σ ∩ Hon M S A x σ,
      w ∈ A.activeThroughout x ((M.supportCutoff S.C σ - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C σ - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs) := by
    intro w hw
    have hw1 := hcut1 w (Finset.mem_inter.1 hw).2
    have hsync := (P.gstSync M F U hσ).1
    have hb : tGAT ≤ M.supportCutoff S.C σ - max (2 * Δ S) Δs := by
      rcases max_cases (2 * Δ S) Δs with ⟨h, -⟩ | ⟨h, -⟩ <;>
      rcases max_cases (Δ S) Δs with ⟨h', -⟩ | ⟨h', -⟩ <;> rw [h] <;> rw [h'] at hsync <;> omega
    have hend : M.supportCutoff S.C σ - max (2 * Δ S) Δs + Δs ≤ M.supportCutoff S.C (σ + 1) := by
      rcases max_cases (2 * Δ S) Δs with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> omega
    have h := (activeThroughout_nat_of_awake_from M F) P.R P.E P.hAwake hw1 hb hEnd
    refine Activity.mem_activeThroughout_of_le le_rfl ?_ h
    exact_mod_cast hend
  exact (confirmation_saved_of_votes M F U) S A x P.R GST σ
    (S.P.committee σ ∩ Hon M S A x σ) H u P.E P.hNet P.hSkew P.hRedeliver P.Sy P.hΔs
    hRootsσ P.hParent ((GoldilocksCorrectness.Record.Statements.Executions.votesCastByOwner_of_unforgeability M F) S A x P.R P.E)
    (P.gstSync M F U hσ).2.2
    (fun w hw => ⟨(Finset.mem_inter.1 hw).1, hHonTick w hw, (hH w hw).1, (hH w hw).2.1, (hH w hw).2.2⟩)
    hHold
    ((counting_of_committee_majority_st M F) S A x P.R P.E σ (x.tickStep u (M.supportCutoff S.C (σ + 1)))
      (Hon M S A x σ) u (P.committee M F hσ hEnd)).2.1
    hvU

/-- **A member saves a confirmation at every slot after the fast block's round.** For a slot
`σ ≥ r * R + 1` with its support cutoff of slot `σ + 1` in the phase, every member of
`Hon M S Sched σ` saves some confirmation of slot `σ`: the root of its fork choice at its update is
a line source of a slot before `σ` (`root_source`), so every vote of slot `σ` of the committee's
members extends it, and so its finalized block (the line invariant); those votes reach it early
(Lemma 12) and are more than half of its pool's voters, so the update saves the end of its walk
(`update_confirmation_saves_of_supporters`).

Proved (F-P3-3-1): `u`'s finalized block at its tick to the support cutoff of slot `σ + 1` is `L` or an ancestor of
`L` when its finalization height is at most `H₂` (Lemma 68), and otherwise an ancestor of a line source of the first
slot of a round `r₁` earlier than a round to whose action time an honest validator ticked before `u`'s tick
(`finalized_source_two_rounds`), so of a slot at most `σ − 1`; `votes_source` at slot `σ − 1` then gives the votes
clause of `member_saves_confirmation_of_votes`. The phase reaches the support cutoff of slot `σ + 2`, so that `u`'s
tick, at most `ΔClockBehind` after the support cutoff of slot `σ + 1`, is in it.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed.

Read aloud: from the slot after the fast block's round on, every member saves a confirmation of each
slot whose next slot's support cutoff is in the phase. -/
theorem member_saves_confirmation (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet)
    {σ : ℕ} (hσ : r * S.C.R + 1 ≤ σ) (hEnd : M.supportCutoff S.C (σ + 2) ≤ tAwakeEnd) {u : V}
    (hu : u ∈ Hon M S A x σ) :
    ∃ C : Block V,
      (x.tickOutput u (M.supportCutoff S.C (σ + 1))).savedConfirmation σ = some C := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hsk := hSkew
  have hR2 := S.C.R_ge_two
  obtain ⟨σ₀, rfl⟩ : ∃ σ₀, σ = σ₀ + 1 := ⟨σ - 1, by omega⟩
  obtain ⟨-, hc1, -, hs1, hΔ⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ₀ + 1 + 1)
  obtain ⟨-, hc2, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ₀ + 1 + 1 + 1)
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hcc : M.supportCutoff S.C (σ₀ + 1 + 1) + 4 * Δ S = M.supportCutoff S.C (σ₀ + 1 + 2) := by
    show _ = M.supportCutoff S.C (σ₀ + 1 + 1 + 1)
    omega
  have hEnd1 : M.supportCutoff S.C (σ₀ + 1 + 1) ≤ tAwakeEnd := by omega
  have hEndR : M.supportCutoff S.C (r * S.C.R + 1) ≤ tAwakeEnd := P.hEnd
  refine P.member_saves_confirmation_of_votes M F U (by omega) hEnd1 hu ?_
  -- `u`'s tick `kR` to the support cutoff of slot `σ₀ + 2`, in the phase (one delay before the support cutoff of the
  -- next slot)
  have hvU : u ∈ updaterAt M S A x (σ₀ + 1) := (P.members_sets M F U (by omega) hEnd1).2 hu
  obtain ⟨kR, hkR, -⟩ := Activity.mem_activeThroughoutToTick.1 hvU
  have hts := (tickStep_eq_of_lbl M) x E hkR
  have hkRt := (E.tick_active kR u _ hkR).2.2
  have hkRE : x.time kR ≤ tAwakeEnd := by
    have : ((M.supportCutoff S.C (σ₀ + 1 + 1) : ℕ) : ℝ) + 4 * Δ S ≤ ((tAwakeEnd : ℕ) : ℝ) := by
      exact_mod_cast (show M.supportCutoff S.C (σ₀ + 1 + 1) + 4 * Δ S ≤ tAwakeEnd by omega)
    linarith
  have hwR : u ∉ A.corrupted kR := E.not_mem_corrupted_of_tick hkR
  -- `u`'s finalized block is an ancestor of a line source of a slot at most `σ₀`
  obtain ⟨μ, X, hμ, hX, hFX⟩ : ∃ (μ : ℕ) (X : Block V), μ ≤ σ₀ ∧ LineSource M S A x r H₂ μ X ∧
      (x.tickInput u (M.supportCutoff S.C (σ₀ + 1 + 1))).finalized.AncestorEq X := by
    have hti : x.tickInput u (M.supportCutoff S.C (σ₀ + 1 + 1)) = x.st kR u := by
      unfold Trace.tickInput
      rw [hts]
    rw [hti]
    obtain ⟨D, hD, hFD⟩ :=
      (GoldilocksCorrectness.Record.Statements.Executions.finalizedFromChain_of_exec M F) S A x R E kR u
    rw [hFD]
    by_cases hle : (M.chainStateOf S.C D).h_F ≤ H₂
    · -- `v` held `L` at its tick to the action time of round `r` (`L_held_v`), honest there, in the phase
      have hv' : v ∉ A.corrupted (x.tickStep v (aR M S r)) := E.not_mem_corrupted_of_tick P.hk₀
      have hLv : L ∈ (x.st (x.tickStep v (aR M S r)) v).tree := (P.L_held_v M F R E U hEndR).2
      exact ⟨r * S.C.R, L, by omega, P.source_L M F R U hEndR,
        (GoldilocksCorrectness.Record.Proofs.Executions.lem68_honest_past_finalized M F Fx) S A x R E P.hRoots
          kR (x.tickStep v (aR M S r)) u v D L (P.hThird.mono (max_le hkRE P.hEndStep)) hwR hv' hD hLv
          (by rw [P.hL]; exact Nat.lt_succ_of_le hle) (max_le hkRE P.hEndStep)⟩
    · obtain ⟨r₁, r₂, h12, ⟨u₂, k₂, hk₂, hk₂j⟩, X, hX, hFX⟩ :=
        (finalized_source_two_rounds M F) R E U Fx hSkew P.hRoots P.hThird P.hAwake P.hCommittees P.hAnchor P.hOld
          P.hEnd P.hk₀ P.hOldStep P.hEndStep hkRE hwR hD (Nat.lt_of_not_le hle)
      -- the tick `k₂` to the action time of round `r₂` is before `kR`, so `r₂ * R ≤ σ₀ + 1`
      have hr₂ : r₂ * S.C.R ≤ σ₀ + 1 := by
        by_contra hgt
        have hm := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
          (show σ₀ + 1 + 2 ≤ r₂ * S.C.R + 1 by omega)
        have hk2t := (E.tick_active k₂ u₂ _ hk₂).2.1
        have hk2k := (time_mono M) x R hk₂j.le
        have hmR : ((M.supportCutoff S.C (σ₀ + 1 + 1) : ℕ) : ℝ) + 4 * Δ S ≤ ((aR M S r₂ : ℕ) : ℝ) := by
          exact_mod_cast (show M.supportCutoff S.C (σ₀ + 1 + 1) + 4 * Δ S ≤ M.supportCutoff S.C (r₂ * S.C.R + 1) by
            omega)
        linarith
      refine ⟨r₁ * S.C.R, X, ?_, hX, hFX⟩
      have h1 := Nat.mul_le_mul_right S.C.R (show r₁ + 1 ≤ r₂ by omega)
      rw [Nat.succ_mul] at h1
      omega
  -- every honest vote of slot `σ₀ + 1` extends `X` (`votes_source` at slot `σ₀`)
  have hG := P.lineInv_upto M F R E hNet hSkew hRedeliver Sy hΔs U Fx (s := σ₀) hEnd1
  intro w hw vote hSend
  obtain ⟨H_w, hH, hvote, hXH⟩ := P.votes_source M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG (by omega) hEnd1 hX hμ
    w (Finset.mem_inter.1 hw).2 vote hSend
  exact ⟨H_w, hH, hvote, ancestorEq_trans hFX hXH⟩

/-- **The proposer's anchor is an early line source.** For a slot `s` at least `k + 2` slots after
`r * R`, with its support cutoff in the phase and its proposer honest then, the anchor of the
proposer's walk at its tick to the start of slot `s` (the state that tick reads) is a line source of a
slot `μ` with `μ + 2 ≤ s`: the root (`root_source_st` at that tick), or an ancestor of a live lock's block
(`source_lock`, Lemma 41). The proposer ticks to the start of slot `s` (`tick_before`), at a real time at
most `ΔClockBehind` after it, so before every tick to the support cutoff of slot `s`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed.

Read aloud: the anchor of an honest proposer's walk at least `k + 2` slots after the fast block's
round is a line source of a slot at least two slots before the proposal's. -/
theorem anchor_source (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {s : ℕ}
    (hs : r * S.C.R + S.C.k + 2 ≤ s) (hEnd : M.supportCutoff S.C s ≤ tAwakeEnd)
    (hp : S.P.proposer s ∉ A.corruptedAtTime x (M.supportCutoff S.C s)) :
    ∃ μ : ℕ, μ + 2 ≤ s ∧ LineSource M S A x r H₂ μ
      (M.get_anchor (x.tickInput (S.P.proposer s) (M.slotStart S.C s))
        ((M.slotStart S.C s : ℕ) : Int)) := by
  have hk := S.C.k_ge_two
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hsk := hSkew
  obtain ⟨σ₁, rfl⟩ : ∃ σ₁, s = σ₁ + 2 := ⟨s - 2, by omega⟩
  have hG : ∀ σ', σ' ≤ σ₁ → LineInv M S A x r H₂ σ' := P.lineInv_upto M F R E hNet hSkew hRedeliver Sy hΔs U Fx hEnd
  obtain ⟨-, hcs2, -, -, hΔ⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ₁ + 2)
  obtain ⟨hvr, -, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (r * S.C.R)
  obtain ⟨-, hcr1, -, hsr1, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (r * S.C.R + 1)
  have hm0 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (show r * S.C.R ≤ σ₁ + 2 by omega)
  have hm1 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (show r * S.C.R + 1 + 1 ≤ σ₁ + 2 by omega)
  obtain ⟨hG1, -, -⟩ := P.gstSync M F U (le_refl (r * S.C.R))
  have haR : aR M S r = M.supportCutoff S.C (r * S.C.R + 1) := rfl
  have ht : M.slotStart S.C (σ₁ + 2) ≤ M.supportCutoff S.C (σ₁ + 2) := by omega
  -- the proposer ticks to the start of slot `s`, at a step `kp`, at a real time in that clock value's window
  obtain ⟨kp, hkp, -⟩ := P.tick_before M F (w := S.P.proposer (σ₁ + 2)) (c := M.slotStart S.C (σ₁ + 2))
    (t := M.supportCutoff S.C (σ₁ + 2)) (by omega) (by omega) hEnd hp
  have hti : x.tickInput (S.P.proposer (σ₁ + 2)) (M.slotStart S.C (σ₁ + 2)) = x.st kp (S.P.proposer (σ₁ + 2)) := by
    unfold Trace.tickInput
    rw [(tickStep_eq_of_lbl M) x E hkp]
  rw [hti]
  have hkpT := (E.tick_active kp _ _ hkp).2.2
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hcR : ((M.supportCutoff S.C (σ₁ + 2) : ℕ) : ℝ) = ((M.slotStart S.C (σ₁ + 2) : ℕ) : ℝ) + 2 * Δ S := by
    rw [hcs2]; push_cast; ring
  have hpk : S.P.proposer (σ₁ + 2) ∉ A.corrupted kp :=
    (not_mem_corrupted_of_le_time M) x R E hp (by rw [hcR]; linarith)
  -- the root: `root_source_st` at `kp`, after `v`'s tick to the action time of round `r`
  have hk₀ := P.hk₀
  have hk₀T := (E.tick_active _ _ _ hk₀).2.2
  have hgap : ((aR M S r : ℕ) : ℝ) + Δ S ≤ ((M.slotStart S.C (σ₁ + 2) : ℕ) : ℝ) := by
    exact_mod_cast (show aR M S r + Δ S ≤ M.slotStart S.C (σ₁ + 2) by omega)
  have hkpA := (E.tick_active kp _ _ hkp).2.1
  have hk₀j : x.tickStep v (aR M S r) < kp := (lt_of_time_lt M) x R (by linarith)
  have hjt : x.time kp < ((M.supportCutoff S.C (σ₁ + 2) : ℕ) : ℝ) - ΔClockAhead := by rw [hcR]; linarith
  obtain ⟨r', -, ⟨u', k', hk', hk'j, -⟩, hsrc⟩ := P.root_source_st M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG (show r * S.C.R ≤ σ₁ by omega) hEnd
    ⟨v, _, hk₀, hk₀j, (E.tick_active _ _ _ hk₀).1⟩ hjt hpk
  have hroot : ∃ μ : ℕ, μ + 2 ≤ σ₁ + 2 ∧ LineSource M S A x r H₂ μ
      (M.get_fc_root (x.st kp (S.P.proposer (σ₁ + 2)))) := by
    refine ⟨r' * S.C.R, ?_, hsrc⟩
    have h1 := (E.tick_active _ _ _ hk').2.1
    have h2 := (time_mono M) x R hk'j.le
    have h3 : ((aR M S r' : ℕ) : ℝ) < ((M.slotStart S.C (σ₁ + 2) : ℕ) : ℝ) + Δ S := by linarith
    have h4 : aR M S r' < M.slotStart S.C (σ₁ + 2) + Δ S := by exact_mod_cast h3
    have haR' : aR M S r' = M.supportCutoff S.C (r' * S.C.R + 1) := rfl
    by_contra h
    have := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
      (show σ₁ + 2 ≤ r' * S.C.R + 1 by omega)
    omega
  rcases (GoldilocksCorrectness.Record.Proofs.Routines.get_anchor_cases_locked M F) (x.st kp (S.P.proposer (σ₁ + 2)))
    ((M.slotStart S.C (σ₁ + 2) : ℕ) : Int) with h | ⟨-, e, he, hl, hAe⟩
  · rw [h, (GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F)]
    exact hroot
  · have hl' := hl
    simp only [(GoldilocksCorrectness.Record.Proofs.Routines.is_live_iff M F)] at hl'
    have hpt : S.P.proposer (σ₁ + 2) ∉ A.corruptedAtTime x (M.slotStart S.C (σ₁ + 2)) :=
      (not_mem_corruptedAtTime_of_le M) x R E ht hp
    have he' : e ∈ (x.tickInput (S.P.proposer (σ₁ + 2)) (M.slotStart S.C (σ₁ + 2))).lockEntries := by
      rw [hti]; exact he
    obtain ⟨μ₀, hd, hcut, -, hsrc⟩ := P.source_lock M F R E U hpt (le_trans ht hEnd) he'
    have hlo : r * S.C.R + 1 ≤ μ₀ :=
      (GoldilocksCorrectness.Record.Statements.Executions.lem41_slot_of_live_entry M F U) S (r * S.C.R + 1) μ₀
        (M.slotStart S.C (σ₁ + 2)) e hd hl'.1 (by
          obtain ⟨hvk, -, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (r * S.C.R + 1 + S.C.k)
          have := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (show r * S.C.R + 1 + S.C.k + 1 ≤ σ₁ + 2 by omega)
          obtain ⟨-, -, -, hsk, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (r * S.C.R + 1 + S.C.k)
          omega)
    refine ⟨μ₀, ?_, (hsrc hlo).anc M F hAe⟩
    by_contra h
    have := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (show σ₁ + 2 ≤ μ₀ + 1 by omega)
    omega

/-- **The frame's viable head on a line source's chain, at a step.** `frame_source_at`'s second clause read at a step `j`
in place of the state before a time: from the vote time of slot `σ + 1` to before the support cutoff of slot `σ + 2`, in
the phase, when the invariant holds at every slot up to `σ`, `w` is outside the adversary set at `j` and `w`'s fork-choice
root at `j` is a line source `X` of a slot at most `σ` or an ancestor of `X`: some viable head of `w`'s frame at `j` is `X`
or a descendant of `X`.

Why: `w` ticked to the view freeze of every slot from `r * R` to `σ` before `j` (`tick_before_st`), holding `X` and `L`
there (`source_held`, `L_held`), kept since (`mem_T_mono`); `viable_candidate_held_st` gives a block of `w`'s tree at `j`
on `X`'s chain whose chain-state height is at least `w`'s `head_height_floor` there; Lemma 56 makes it a viable head.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed; `j`: the step.

Read aloud: at a step from the vote time of slot `σ + 1` to before the next support cutoff, when an honest validator's root
is on a line source's chain, some viable head of its frame is that source or a descendant of it. -/
theorem frame_source_st (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {σ j : ℕ}
    {w : V} (hG : ∀ σ', σ' ≤ σ → LineInv M S A x r H₂ σ') (hσ : r * S.C.R ≤ σ)
    (hEnd : M.supportCutoff S.C (σ + 2) ≤ tAwakeEnd) (hj0 : ((M.voteTime S.C (σ + 1) : ℕ) : ℝ) ≤ x.time j)
    (hjc : x.time j < ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ)) (hw' : w ∉ A.corrupted j) {μ : ℕ} {X : Block V}
    (hX : LineSource M S A x r H₂ μ X) (hμ : μ ≤ σ)
    (hRX : (M.get_fc_root (x.st j w)).AncestorEq X) :
    ∃ W ∈ (M.fg_to_ac (x.st j w)).tree, W ∈ (M.fg_to_ac (x.st j w)).viable_heads ∧ X.AncestorEq W := by
  obtain ⟨hvσ1, hcσ1, -, hsσ1, hΔ⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 1)
  have hEnd1 : M.supportCutoff S.C (σ + 1) ≤ tAwakeEnd :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (Nat.le_succ _)) hEnd
  have hEndR : M.supportCutoff S.C (r * S.C.R + 1) ≤ tAwakeEnd :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)) hEnd1
  have hcE : ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) ≤ ((tAwakeEnd : ℕ) : ℝ) := by exact_mod_cast hEnd
  have hjE : x.time j ≤ tAwakeEnd := by linarith
  -- `w` ticks to the view freeze of every slot from `r * R` to `σ` before `j` (`tick_before_st`)
  have htick : ∀ μ₁ : ℕ, r * S.C.R ≤ μ₁ → μ₁ ≤ σ →
      ∃ k : ℕ, x.lbl k = Event.tick w (M.viewFreeze S.C μ₁) ∧ k < j := by
    intro μ₁ h1 h2
    obtain ⟨hv₁, -, hf₁, hs₁, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S μ₁
    obtain ⟨hG1, -, -⟩ := P.gstSync M F U h1
    have hm := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
      (show μ₁ + 1 ≤ σ + 1 by omega)
    have hcj : ((M.viewFreeze S.C μ₁ : ℕ) : ℝ) + Δ S ≤ ((M.voteTime S.C (σ + 1) : ℕ) : ℝ) := by
      exact_mod_cast (show M.viewFreeze S.C μ₁ + Δ S ≤ M.voteTime S.C (σ + 1) by omega)
    exact P.tick_before_st M F (by omega) (by linarith) hjE hw'
  have hRF := (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F) S A x R P.E j w
  have hFX : ∀ k₁ : ℕ, k₁ ≤ j → (x.st k₁ w).finalized.AncestorEq X := fun k₁ hk₁ =>
    ancestorEq_trans ((F_ancestorEq_of_le M F) x R P.E w hk₁) (ancestorEq_trans hRF hRX)
  -- `X` and `L` in `w`'s tree at `j`: held at `w`'s ticks to the view freezes (`source_held`, `L_held`), kept since
  have hXj : X ∈ (x.st j w).tree := by
    obtain ⟨k₁, hk₁, hk₁t⟩ := htick μ (hX.slot_ge M F) hμ
    have hk₁R : x.tickStep w (M.viewFreeze S.C μ) = k₁ := (tickStep_eq_of_lbl M) x P.E hk₁
    have hTI₁ : x.tickInput w (M.viewFreeze S.C μ) = x.st k₁ w := by
      show x.st (x.tickStep w (M.viewFreeze S.C μ)) w = x.st k₁ w; rw [hk₁R]
    have hE₁ : M.supportCutoff S.C (μ + 1) ≤ tAwakeEnd :=
      le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)) hEnd1
    have h := P.source_held M F R E hNet hSkew hRedeliver Sy hΔs U hX hE₁ hk₁ (by
      rw [hTI₁]
      exact (compatible_iff _ _).2 (Or.inl (hFX k₁ hk₁t.le)))
    rw [hTI₁] at h
    exact (mem_T_mono M F) x R P.E w hk₁t.le h
  have hLj : L ∈ (x.st j w).tree := by
    obtain ⟨kL, hkL, hkLt⟩ := htick (r * S.C.R) le_rfl hσ
    have hkLR : x.tickStep w (M.viewFreeze S.C (r * S.C.R)) = kL := (tickStep_eq_of_lbl M) x P.E hkL
    have h := P.L_held M F R E hNet hSkew hRedeliver Sy hΔs U Fx hEndR hkL
    rw [show x.tickInput w (M.viewFreeze S.C (r * S.C.R)) = x.st kL w by
      show x.st (x.tickStep w (M.viewFreeze S.C (r * S.C.R))) w = x.st kL w; rw [hkLR]] at h
    exact (mem_T_mono M F) x R P.E w hkLt.le h
  obtain ⟨W, hXW, hWT', hφ⟩ :=
    P.viable_candidate_held_st M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hσ hEnd hjE hw' hjc hX hμ hXj hLj
  have hFW : (x.st j w).finalized.AncestorEq W := ancestorEq_trans hRF (ancestorEq_trans hRX hXW)
  refine ⟨W, ((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).2 ⟨hWT', hFW⟩, ?_, hXW⟩
  refine (((GoldilocksCorrectness.Record.Statements.Routines.lem56_frame_of_shape M F) S.C S.P S.X
    (x.st j w) (GoldilocksCorrectness.Record.Proofs.Executions.lem11_node_invariant M F S A x R E j w hw').1 _ _
    (show GoldilocksCorrectness.Record.Statements.Routines.FrameShape M (x.st j w) (M.get_fc_root (x.st j w))
      (M.head_height_floor (x.st j w)) from ⟨rfl, rfl⟩)).2.2 W).2
    ⟨hWT', hFW, ancestorEq_trans hRX hXW, hφ⟩

/-- **The honest proposal's parent extends every early line source.** For a slot `s` at least
`k + 2` slots after `r * R`, with its support cutoff in the phase, the proposer of slot `s` honest
at that support cutoff and `B` its proposal: every line source of a slot `μ` with `μ + 2 ≤ s` is
an ancestor of, or equal to, `B`'s parent.

Why: the votes of slot `s − 1` of the committee's members extend every such source (`votes_source`,
the line invariant up to slot `s − 2`); the proposer's anchor is its root or an ancestor of a live lock, a
line source in both cases at its tick to the start of slot `s` (`anchor_source`); its frame there has a
viable head on every source's chain (`root_source_st`, `sources_compatible`, `frame_source_st`); so
the walk passes every source (`family_ancestorEq_proposal_parent`, the members' votes by
`votes_source`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed.

Read aloud: the parent of an honest proposal at least `k + 2` slots after the fast block's round is
a descendant of every line source of a slot at least two slots before the proposal's, or that source
itself. -/
theorem parent_extends_sources (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet) {s : ℕ}
    (hs : r * S.C.R + S.C.k + 2 ≤ s) (hEnd : M.supportCutoff S.C s ≤ tAwakeEnd) {B : Block V}
    (hp : S.P.proposer s ∉ A.corruptedAtTime x (M.supportCutoff S.C s))
    (hB : ProposalAt M S x s B) :
    ∀ (μ : ℕ) (Y : Block V), LineSource M S A x r H₂ μ Y → μ + 2 ≤ s →
      Y.AncestorEq B.parent := by
  have hk := S.C.k_ge_two
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hsk := hSkew
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  have hAnch := P.anchor_source M F R E hNet hSkew hRedeliver Sy hΔs U Fx hs hEnd hp
  obtain ⟨σ₁, rfl⟩ : ∃ σ₁, s = σ₁ + 2 := ⟨s - 2, by omega⟩
  set p := S.P.proposer (σ₁ + 2) with hpdef
  have hσ : r * S.C.R ≤ σ₁ := by omega
  have hG : ∀ σ', σ' ≤ σ₁ → LineInv M S A x r H₂ σ' := P.lineInv_upto M F R E hNet hSkew hRedeliver Sy hΔs U Fx hEnd
  obtain ⟨hvs1, hcs1, -, hss1, hΔ⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ₁ + 1)
  obtain ⟨-, hcs2, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ₁ + 2)
  obtain ⟨hvr, -, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (r * S.C.R)
  obtain ⟨-, hcr1, -, hsr1, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (r * S.C.R + 1)
  have hm1 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (show r * S.C.R + 1 + 1 ≤ σ₁ + 2 by omega)
  rw [show σ₁ + 1 + 1 = σ₁ + 2 from rfl] at hss1
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  -- the family: the line sources of slots `μ` with `μ + 2 ≤ σ₁ + 2`
  let 𝓒 : Block V → Prop := fun C => ∃ μ, μ ≤ σ₁ ∧ LineSource M S A x r H₂ μ C
  -- `p`'s tick `iB` to the start of slot `σ₁ + 2`, at which it proposed `B`
  obtain ⟨iB, hlB, hsB⟩ := hB
  have hti : x.tickInput p (M.slotStart S.C (σ₁ + 2)) = x.st iB p := by
    unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hlB]
  have hiBT := (E.tick_active iB _ _ hlB).2.2
  have hiBA := (E.tick_active iB _ _ hlB).2.1
  have hcR : ((M.supportCutoff S.C (σ₁ + 2) : ℕ) : ℝ) = ((M.slotStart S.C (σ₁ + 2) : ℕ) : ℝ) + 2 * Δ S := by
    rw [hcs2]; push_cast; ring
  have hpk : p ∉ A.corrupted iB := E.not_mem_corrupted_of_tick hlB
  -- the root at `iB`: `root_source_st`, after `v`'s tick to the action time of round `r`
  have hk₀ := P.hk₀
  have hk₀T := (E.tick_active _ _ _ hk₀).2.2
  have hgap : ((aR M S r : ℕ) : ℝ) + Δ S ≤ ((M.slotStart S.C (σ₁ + 2) : ℕ) : ℝ) := by
    have haR : aR M S r = M.supportCutoff S.C (r * S.C.R + 1) := rfl
    exact_mod_cast (show aR M S r + Δ S ≤ M.slotStart S.C (σ₁ + 2) by omega)
  have hk₀j : x.tickStep v (aR M S r) < iB := (lt_of_time_lt M) x R (by linarith)
  have hjt : x.time iB < ((M.supportCutoff S.C (σ₁ + 2) : ℕ) : ℝ) - ΔClockAhead := by rw [hcR]; linarith
  obtain ⟨r', -, ⟨u', k', hk', hk'j, -⟩, hsrc⟩ := P.root_source_st M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hσ hEnd
    ⟨v, _, hk₀, hk₀j, (E.tick_active _ _ _ hk₀).1⟩ hjt hpk
  have hroot : 𝓒 (M.get_fc_root (x.st iB p)) := by
    refine ⟨r' * S.C.R, ?_, hsrc⟩
    have h1 := (E.tick_active _ _ _ hk').2.1
    have h2 := (time_mono M) x R hk'j.le
    have h3 : ((aR M S r' : ℕ) : ℝ) < ((M.slotStart S.C (σ₁ + 2) : ℕ) : ℝ) + Δ S := by linarith
    have h4 : aR M S r' < M.slotStart S.C (σ₁ + 2) + Δ S := by exact_mod_cast h3
    have haR' : aR M S r' = M.supportCutoff S.C (r' * S.C.R + 1) := rfl
    by_contra h
    have := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
      (show σ₁ + 2 ≤ r' * S.C.R + 1 by omega)
    omega
  -- `p`'s frame at `iB` has a viable head on the chain of every block of the family
  have hj0 : ((M.voteTime S.C (σ₁ + 1) : ℕ) : ℝ) ≤ x.time iB := by
    have : ((M.voteTime S.C (σ₁ + 1) : ℕ) : ℝ) + Δ S ≤ ((M.slotStart S.C (σ₁ + 2) : ℕ) : ℝ) := by
      exact_mod_cast (show M.voteTime S.C (σ₁ + 1) + Δ S ≤ M.slotStart S.C (σ₁ + 2) by omega)
    linarith
  have hjc : x.time iB < ((M.supportCutoff S.C (σ₁ + 2) : ℕ) : ℝ) := by linarith
  have hFrame : ∀ C : Block V, 𝓒 C →
      ∃ W ∈ (M.fg_to_ac (x.tickInput p (M.slotStart S.C (σ₁ + 2)))).tree,
        W ∈ (M.fg_to_ac (x.tickInput p (M.slotStart S.C (σ₁ + 2)))).viable_heads ∧ C.AncestorEq W := by
    intro C ⟨μC, hμC, hC⟩
    rw [hti]
    obtain ⟨μR, hμR, hR⟩ := hroot
    have hfs := fun {μ' : ℕ} {X : Block V} (hX : LineSource M S A x r H₂ μ' X) (hμ' : μ' ≤ σ₁)
        (hRX : (M.get_fc_root (x.st iB p)).AncestorEq X) =>
      P.frame_source_st M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hσ hEnd hj0 hjc hpk hX hμ' hRX
    rcases (compatible_iff _ _).1 (P.sources_compatible M F R U hG hEnd hR hC hμR hμC) with h | h
    · exact hfs hC hμC h
    · obtain ⟨W, hW, hWv, hRW⟩ := hfs hR hμR (ancestorEq_refl _)
      exact ⟨W, hW, hWv, ancestorEq_trans h hRW⟩
  -- the members of slot `σ₁ + 1`, their votes and the sync window
  have hEs : M.supportCutoff S.C (σ₁ + 1 + 1) ≤ tAwakeEnd := hEnd
  have hpA : p ∈ A.activeThroughout x tGAT (M.supportCutoff S.C (σ₁ + 2)) := P.window M F hp hEnd
  have hsync := (P.gstSync M F U (show r * S.C.R ≤ σ₁ + 1 by omega)).1
  have hG0 : ((tGAT : ℕ) : ℝ) ≤ ((M.supportCutoff S.C (σ₁ + 1) : ℕ) : ℝ) - ΔClockAhead := by
    have hmx := le_max_left (Δ S) Δs
    have : ((tGAT : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (σ₁ + 1) : ℕ) : ℝ) := by
      exact_mod_cast (show tGAT + Δ S ≤ M.supportCutoff S.C (σ₁ + 1) by omega)
    linarith
  have hc01R : ((M.supportCutoff S.C (σ₁ + 1) : ℕ) : ℝ) + ΔClockBehind ≤ ((M.supportCutoff S.C (σ₁ + 2) : ℕ) : ℝ) := by
    have : ((M.supportCutoff S.C (σ₁ + 1) : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (σ₁ + 2) : ℕ) : ℝ) := by
      exact_mod_cast (show M.supportCutoff S.C (σ₁ + 1) + Δ S ≤ M.supportCutoff S.C (σ₁ + 2) by omega)
    linarith
  obtain ⟨kR, hkR, hkR1, hkR2⟩ := E.tick_of_active (M.supportCutoff S.C (σ₁ + 1)) (by omega) p
    (fun j h1 h2 => Activity.mem_activeThroughout.1 hpA j (le_trans h2 hc01R)
      (le_trans (le_trans hG0 h1) (htime (Nat.le_succ j))))
  have hRootsP : RootsNameBlocksUntil M A x (x.time (x.tickStep p (M.supportCutoff S.C (σ₁ + 1)))) := by
    rw [(tickStep_eq_of_lbl M) x E hkR]
    refine (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) ?_ P.hRoots
    have hcE : ((M.supportCutoff S.C (σ₁ + 2) : ℕ) : ℝ) ≤ ((tAwakeEnd : ℕ) : ℝ) := by exact_mod_cast hEnd
    linarith
  have hHold0 : tGAT ≤ M.supportCutoff S.C (σ₁ + 1) - max (2 * Δ S) Δs := by
    rcases max_cases (2 * Δ S) Δs with ⟨h, -⟩ | ⟨h, -⟩ <;>
    rcases max_cases (Δ S) Δs with ⟨h', -⟩ | ⟨h', -⟩ <;> rw [h] <;> rw [h'] at hsync <;> omega
  have hHold1 : M.supportCutoff S.C (σ₁ + 1) - max (2 * Δ S) Δs + Δs ≤ M.supportCutoff S.C (σ₁ + 2) := by
    rcases max_cases (2 * Δ S) Δs with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> omega
  have hmem := P.members_sets M F U (show r * S.C.R ≤ σ₁ + 1 by omega) hEs
  have hTB : x.time iB ≤ ((M.supportCutoff S.C (σ₁ + 1 + 1) : ℕ) : ℝ) := by
    show x.time iB ≤ ((M.supportCutoff S.C (σ₁ + 2) : ℕ) : ℝ)
    linarith
  have hAnchor : 𝓒 (M.get_anchor (x.tickInput p (M.slotStart S.C (σ₁ + 2))) ((M.slotStart S.C (σ₁ + 2) : ℕ) : Int)) := by
    obtain ⟨μa, hμa, ha⟩ := hAnch
    exact ⟨μa, by omega, ha⟩
  have hfam := (GoldilocksCorrectness.Record.Proofs.Executions.family_ancestorEq_proposal_parent M F U) S A x R GST (σ₁ + 1)
    (S.P.committee (σ₁ + 1) ∩ Hon M S A x (σ₁ + 1)) 𝓒 B p P.E P.hNet P.hSkew P.hRedeliver P.Sy P.hΔs
    hRootsP P.hParent (votesCastByOwner_of_unforgeability M F S A x R E)
    (P.gstSync M F U (show r * S.C.R ≤ σ₁ + 1 by omega)).2.2
    (fun u hu => by
      obtain ⟨hK, hH⟩ := Finset.mem_inter.1 hu
      obtain ⟨i, vote, hl, -, -, hsent⟩ :=
        (GoldilocksCorrectness.Record.Statements.Executions.honest_active_votes M F U) S A x R (σ₁ + 1) u
          P.E P.hSkew (hmem.1 hH) hK
      refine ⟨hK, ?_, vote, i, hl, hsent⟩
      rw [(tickStep_eq_of_lbl M) x E hlB]
      exact (not_mem_corrupted_of_le_time M) x R E (Finset.mem_sdiff.1 hH).2 hTB)
    (fun C hC u hu vote hv => by
      obtain ⟨μC, hμC, hCs⟩ := hC
      exact P.votes_source M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hσ hEnd hCs hμC u (Finset.mem_inter.1 hu).2 vote hv)
    ((GoldilocksCorrectness.Record.Proofs.Executions.counting_of_committee_majority_st M F) S A x R E (σ₁ + 1)
      (x.tickStep p (M.slotStart S.C (σ₁ + 1 + 1))) (Hon M S A x (σ₁ + 1)) p
      (P.committee M F (show r * S.C.R ≤ σ₁ + 1 by omega) hEs)).2.1
    (fun u hu => by
      have hub : u ∉ A.corruptedAtTime x (M.supportCutoff S.C (σ₁ + 1 + 1)) :=
        (Finset.mem_sdiff.1 (Finset.mem_inter.1 hu).2).2
      refine Activity.mem_activeThroughout_of_le ?_ ?_
        ((mem_activeThroughout_of_hAwake_honest_at M F) R P.E P.hAwake le_rfl hEs hub)
      · exact_mod_cast hHold0
      · have : ((M.supportCutoff S.C (σ₁ + 1) - max (2 * Δ S) Δs + Δs : ℕ) : ℝ) ≤
            ((M.supportCutoff S.C (σ₁ + 1 + 1) : ℕ) : ℝ) := by exact_mod_cast hHold1
        push_cast at this
        exact this)
    ⟨kR, hkR, fun j h1 h2 => Activity.mem_activeThroughout.1 hpA j
      (le_trans (htime h2) (le_trans hkR2 hc01R))
      (le_trans (le_trans (by exact_mod_cast hHold0) h1) (htime (Nat.le_succ j)))⟩
    ⟨iB, hlB, hsB⟩ hFrame hAnchor
  intro μ Y hY hμ
  exact hfam Y ⟨μ, by omega, hY⟩

end PartAHyps

/-! ## The line kit at a tick past the bundle's end

Copies of `Lemma89FastFamily.lean`'s `cert_source_core_fast`, `F_compat_st`, `F_compat_tick`, `conf_source_at`,
`stepFrame_source`, `base_source` and `step_source`, each with the bundle `PartAHyps` read up to its end `tAwakeEnd` and a
tick to a clock value at most `c₀` read up to a later end `tEnd` through the rows `TickRows`. Then `lineInv_last`: the line invariant at the
slot `σ` whose support cutoff of slot `σ + 1` is the bundle's end, where `lineInv_all` asks one slot more. -/

section TickPast
open GoldilocksCorrectness.Proofs.Executions (mem_awakeThroughout_of_forall)
open GoldilocksCorrectness.Proofs.Routines (compatible_of_ancestorEq_both compatible_symm')
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_le_supportCutoff
  dutyWindowStart_le_voteTime dutyWindowStart_mono dutyWindowStart_of_anchor
  dutyWindowStart_succ_le_slotStart one_le_Δ slotStart_eq slotStart_mono slot_eq_of_mem
  supportCutoff_cast supportCutoff_eq supportCutoff_lt supportCutoff_mono supportCutoff_succ_times
  tGAT_le_slotStart t_lt_of_lt times_eq viewFreeze_eq voteTime_eq)
open GoldilocksCorrectness.Proofs.Routines (duty_window_start_lt_supportCutoff)
open GoldilocksCorrectness.Record.Statements.Routines (ConfirmationUpdated LocksRevoked)
open GoldilocksCorrectness.Record.Statements.Routines (FrameShape ProgressCertOn)

/-- `TickRows M S A x tGAT tAwakeEnd tEnd c₀`: the rows that let the line kit read a tick to a clock value at most `c₀`
past the bundle's end `tAwakeEnd`: a later end `tEnd`, the phase's premises up to `tEnd` (fewer than a third of the
validators in the adversary set, every validator outside it awake from `tGAT`, the committees' sleepiness), and, at
every tick to a clock value at most `c₀`, roots naming blocks up to its real time, which is at most `tEnd`
.

The variables:
- `M`: the model;
- `S`, `A`, `x`: the setup, the activity, the execution; `tGAT`: the phase's start; `tAwakeEnd`: the bundle's end;
  `tEnd`: the later end; `c₀`: the clock bound of the ticks.

Read aloud: the phase lasts to `tEnd`, and roots name blocks up to every tick to a clock value at most `c₀`, each at a
real time at most `tEnd`. -/
structure TickRows (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (tGAT tAwakeEnd tEnd c₀ : ℕ) :
    Prop where
  /-- The later end is at least the bundle's end. -/
  hTE : tAwakeEnd ≤ tEnd
  /-- Fewer than a third of the validators are in the adversary set up to `tEnd`. -/
  hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tEnd
  /-- Every validator outside the adversary set is awake at every step from `tGAT` up to `tEnd`. -/
  hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
    v ∉ A.corrupted i → v ∈ A.awake i
  /-- The committees' sleepiness up to `tEnd`. -/
  hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tEnd
  /-- Roots name blocks up to the real time of every tick to a clock value at most `c₀`. -/
  hRootsTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ c₀ →
    RootsNameBlocksUntil M A x (x.time k)
  /-- Every tick to a clock value at most `c₀` is at a real time at most `tEnd`. -/
  hEndTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ c₀ → x.time k ≤ tEnd

/-- **`cert_source_core_fast` with roots up to the action time of round `r` only (copy).** The statement of
`cert_source_core_fast` with its roots asked only up to the support cutoff of slot `r * R + 1`, the action time of round
`r`: its proof reads them nowhere later. So the phase's end `tAwakeEnd` may be a time up to which roots are not given.

The variables: as `cert_source_core`'s.

Read aloud: a certificate above `H₂` names the entry of a fast block of an honest attester's update, at a tick before
the reading, with roots asked only up to the action time of round `r`. -/theorem cert_source_core_fast_past {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N}
    (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) {tGAT tAwakeEnd r H₂ : ℕ} {v : V}
    (hRoots : RootsNameBlocksUntil M A x ((M.supportCutoff S.C (r * S.C.R + 1) : ℕ) : ℝ))
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hAnchor : anchorCW S tGAT ≤ M.slotStart S.C (r * S.C.R + 1))
    (hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂)
    (hEnd : aR M S r ≤ tAwakeEnd)
    (hk₀ : x.lbl (x.tickStep v (aR M S r)) = Event.tick v (aR M S r))
    (hOldStep : ∀ (k t : ℕ) (u : V) (a' : Attestation V), k < x.firstAt (M.supportCutoff S.C (r * S.C.R)) →
      x.lbl k = Event.tick u t → u ∉ A.corruptedAtTime x tAwakeEnd →
      (⟨u, NamedObject.attest a'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (k + 1) - x.sent k → a'.h ≤ H₂)
    (hEndStep : x.time (x.tickStep v (aR M S r)) ≤ tAwakeEnd)
    {j : ℕ} {w : V} {Y T : Block V} {h : Height} (hj : x.time j ≤ tAwakeEnd)
    (hY : Y ∈ (x.st j w).tree) (hJ : ProgressCertOn M Y h T) (hH : H₂ < h) :
    ∃ (r' : ℕ) (E : Block V) (u : V) (k : ℕ), r ≤ r' ∧ x.lbl k = Event.tick u (aR M S r') ∧ k < j ∧
      u ∈ A.active k ∧ LineSource M S A x r H₂ (r' * S.C.R) E ∧ IsEntry M S.C E ∧
      (M.chainStateOf S.C E).h = h ∧ T.root = E.root ∧
      u ∈ updaterAt M S A x (r' * S.C.R) ∧ ∃ (n₀ : M.N) (X₀ : Block V),
        ConfirmationUpdated M S.C S.P (x.tickInput u (aR M S r')) ((aR M S r' : ℕ) : Int) (r' * S.C.R + 1) n₀ ∧
        X₀ ∈ M.fastBlocks n₀ ∧ E.AncestorEq X₀ := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ := one_le_Δ S
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  -- the adversary bound up to the later of `x.time j` and the action time of round `r`
  have hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max (x.time j) (aR M S r)) :=
    fun X hX => by
      have h1 := (hThird.mono (max_le hj (by exact_mod_cast hEnd))) X hX
      have h2 := (GoldilocksCorrectness.Statements.Routines.lem65b_quorum_threshold (V := V)).2
      omega
  obtain ⟨X₁, hX₁Y, Q, hqA, hQ⟩ := hJ
  rw [GoldilocksCorrectness.Record.quorumAt_eq_quorum Fx F.sched X₁] at hqA
  obtain ⟨u, hu, hhonM⟩ : ∃ u ∈ Q, A.HonestThroughTime x (max (x.time j) (aR M S r)) u := by
    by_contra hno
    have hall : ∀ v ∈ Q, ∃ i : ℕ, x.time i ≤ max (x.time j) (aR M S r) ∧ v ∈ A.corrupted i := by
      intro v hv
      by_contra hn
      exact hno ⟨v, hv, fun i hi ha => hn ⟨i, hi, ha⟩⟩
    have h3 := hAdvQ Q hall
    omega
  have hhonT : ∀ t'' : ℕ, t'' ≤ max (x.time j) (aR M S r) → u ∉ A.corruptedAtTime x t'' :=
    fun t'' ht'' => Activity.not_mem_corruptedAtTime.2 fun i hi => hhonM i (le_trans hi ht'')
  have hhon : x.HonestThrough A j u :=
    fun i'' hi'' => hhonM i'' (le_trans ((time_mono M) x R hi'') (le_max_left _ _))
  have huR : u ∉ A.corruptedAtTime x (aR M S r) := hhonT _ (le_max_right _ _)
  obtain ⟨a, hau, hah, haT, hon⟩ := hQ u hu
  have hrec := (GoldilocksCorrectness.Record.Proofs.Executions.lem74_honest_attestations_recorded M F) S A x R E j w Y a hY
    ((GoldilocksCorrectness.Record.Proofs.Routines.on_chain_mono M F) a hX₁Y hon)
    (by rw [hau]; exact hhon)
  rw [hau] at hrec
  obtain ⟨j', t', a', hj', hl, hact', hsent, -, hcont, -⟩ :=
    (GoldilocksCorrectness.Record.Proofs.Executions.record_content_sent_step M F) S A x R E u j _ hrec
  have hh' : a'.h = h := by
    rw [← hah]
    exact congrArg AttestationContent.h hcont
  have hT' : a'.T = T.root := by
    rw [← haT]
    exact congrArg AttestationContent.T hcont
  have hge : aR M S r ≤ t' := by
    by_contra hlt
    have hle := hOld j' t' u a' hl (by exact_mod_cast Nat.lt_of_not_le hlt) huR hsent
    rw [hh'] at hle
    exact absurd hle (Nat.not_le.mpr hH)
  obtain ⟨r', rfl⟩ := (attest_time_round M F U) S A x R E hl hsent
  have hrr : r ≤ r' := by
    by_contra hlt
    have : r' * S.C.R + 1 < r * S.C.R + 1 := by
      have := Nat.mul_lt_mul_of_pos_right (Nat.lt_of_not_le hlt)
        (show 0 < S.C.R by have := S.C.R_ge_two; omega)
      omega
    have := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_lt M.toSlotLayout F.sched) S this
    exact absurd hge (Nat.not_le.mpr this)
  obtain ⟨n₀, X, hU, hXf, hXT, hXh, hXT'⟩ :=
    (fast_source_of_attestation M F U) S A x R E r' u a' ⟨j', hl, hsent⟩
  obtain ⟨hE1, hE2, hE3⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.isEntry_T_h M F) S.C X
  -- `u` is an updater of slot `r' * R`: honest up to its tick `j'`, awake from its tick to the duty
  -- window's start of slot `r' * R + 1`
  have hj'j : x.time j' ≤ x.time j := htime hj'.le
  have hhon' : ∀ i : ℕ, i ≤ j' → u ∉ A.corrupted i := fun i hi => hhon i (by omega)
  have hkt := (E.tick_active j' u _ hl).2
  have hdws : tGAT + Δ S ≤ M.dutyWindowStart S.C (r' * S.C.R + 1) :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_of_anchor M.toSlotLayout F.sched U) S
      tGAT (r * S.C.R) hAnchor)
      ((GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_mono M.toSlotLayout F.sched) S
        (show r * S.C.R ≤ r' * S.C.R + 1 by have := Nat.mul_le_mul_right S.C.R hrr; omega))
  have hdw := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_succ_le_slotStart M.toSlotLayout F.sched) S
    (r' * S.C.R)
  have hT0 := (GoldilocksCorrectness.Record.Proofs.Routines.times_le M.toSlotLayout F.sched) S (r' * S.C.R)
  have hT1 := (GoldilocksCorrectness.Record.Proofs.Routines.times_le M.toSlotLayout F.sched) S (r' * S.C.R + 1)
  have hcR : ((M.dutyWindowStart S.C (r' * S.C.R + 1) : ℕ) : ℝ) + 4 * Δ S ≤ (aR M S r' : ℝ) := by
    have : M.dutyWindowStart S.C (r' * S.C.R + 1) + 4 * Δ S ≤ aR M S r' := by
      show _ ≤ M.supportCutoff S.C (r' * S.C.R + 1)
      omega
    exact_mod_cast this
  have hdwsR : ((tGAT : ℕ) : ℝ) + Δ S ≤ ((M.dutyWindowStart S.C (r' * S.C.R + 1) : ℕ) : ℝ) := by
    exact_mod_cast hdws
  obtain ⟨kc, hkc, hkc1, hkc2⟩ := E.tick_of_active (M.dutyWindowStart S.C (r' * S.C.R + 1)) (by omega) u
    (fun i h1 h2 => by
      have hij : i < j' := (lt_of_time_lt M) x R (by linarith)
      have hui := hhon' i hij.le
      exact Activity.mem_active.2 ⟨hAwake i u (by linarith [htime hij.le]) (by linarith [htime (Nat.le_succ i)]) hui, hui⟩)
  have hkcj : kc ≤ j' := tick_step_le_of_le M F E hkc hl (by
    show M.dutyWindowStart S.C (r' * S.C.R + 1) ≤ M.supportCutoff S.C (r' * S.C.R + 1)
    omega)
  have hupd : u ∈ updaterAt M S A x (r' * S.C.R) := by
    show u ∈ A.activeThroughoutToTick x (Goldilocks.duty_window_start S.C (r' * S.C.R + 1))
      (M.supportCutoff S.C (r' * S.C.R + 1))
    refine Activity.mem_activeThroughoutToTick.2 ⟨j', hl, Or.inr ⟨kc, hkcj, M.dutyWindowStart S.C (r' * S.C.R + 1),
      (dutyWindowStart_le_duty_window_start M F U) S (by omega), hkc, fun i h1 h2 => ?_⟩⟩
    have hui := hhon' i h2
    exact Activity.mem_active.2 ⟨hAwake i u (by linarith [htime h2]) (by linarith [htime h1, htime (Nat.le_succ i)]) hui, hui⟩
  have hst := (GoldilocksCorrectness.Record.Proofs.Executions.state_saved_of_update M F U) S A x R (r' * S.C.R) u n₀ E
    hupd hU
  obtain ⟨C₀, hC₀, hXC₀⟩ :=
    GoldilocksCorrectness.Record.Proofs.Routines.update_confirmation_fast_block_saved
      (Nat.le_add_left 1 _) hU hXf
  rw [Nat.add_sub_cancel] at hC₀
  have hkind : (r' * S.C.R = r * S.C.R ∧ X ∈ M.fastBlocks n₀ ∧ (M.chainStateOf S.C X).h = H₂ + 1) ∨
      (r * S.C.R + 1 ≤ r' * S.C.R ∧ (X ∈ M.fastBlocks n₀ ∨
        M.slow_test S.C (x.tickInput u (M.supportCutoff S.C (r' * S.C.R + 1))) (r' * S.C.R) X =
          true)) ∨
      r * S.C.R + S.C.k ≤ r' * S.C.R := by
    rcases Nat.lt_or_eq_of_le hrr with hlt | heq
    · refine Or.inr (Or.inl ⟨?_, Or.inl hXf⟩)
      have h1 := Nat.mul_le_mul_right S.C.R (show r + 1 ≤ r' by omega)
      have h2 := S.C.R_ge_two
      rw [Nat.succ_mul] at h1
      omega
    · subst heq
      refine Or.inl ⟨rfl, hXf, ?_⟩
      -- `X` is `H_v` or an ancestor of it, a block an honest committee member held at its tick to the
      -- vote time of slot `r * R`, a step before `v`'s tick to `aR M S r` (A2 there)
      have hRoots' : RootsNameBlocksUntil M A x ((M.supportCutoff S.C (r * S.C.R + 1) : ℕ) : ℝ) :=
        hRoots
      obtain ⟨v', -, H_v, hHv, hXH⟩ :=
        (fast_block_has_honest_supporter_of_update M F U) S A x R (anchorCW S tGAT) (r * S.C.R) u E hSkew
          ((votesCastByOwner_of_unforgeability M F) S A x R E) hRoots'
          (hCommittees.mono M hEnd) hAnchor hupd n₀ hU X hXf
      have hk0t := (E.tick_active _ v _ hk₀).2.1
      have hT0' := (GoldilocksCorrectness.Record.Proofs.Routines.times_le M.toSlotLayout F.sched) S (r * S.C.R)
      have hT1' := (GoldilocksCorrectness.Record.Proofs.Routines.times_le M.toSlotLayout F.sched) S (r * S.C.R + 1)
      -- `v'`'s tick to the vote time of slot `r * R` comes before the first step reaching that slot's support cutoff
      have hvk : x.tickStep v' (M.voteTime S.C (r * S.C.R)) ≤ x.firstAt (M.supportCutoff S.C (r * S.C.R)) := by
        by_cases hex : ∃ i : ℕ, x.lbl i = Event.tick v' (M.voteTime S.C (r * S.C.R))
        · obtain ⟨i, hi⟩ := hex
          rw [(tickStep_eq_of_lbl M) x E hi]
          have hit := (E.tick_active i v' _ hi).2.2
          have hvt : ((M.voteTime S.C (r * S.C.R) : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (r * S.C.R) : ℕ) : ℝ) := by
            exact_mod_cast hT0'.2.1
          exact ((lt_firstAt_of_time_lt M F) R E (by linarith)).le
        · simp only [Trace.tickStep, hex, dif_neg, not_false_eq_true]
          exact Nat.zero_le _
      -- that first step is at or before `v`'s tick to `aR M S r`, so in the phase
      have hk0E : x.time (x.firstAt (M.supportCutoff S.C (r * S.C.R))) ≤ tAwakeEnd := by
        have hc : ((M.supportCutoff S.C (r * S.C.R) : ℕ) : ℝ) ≤ x.time (x.tickStep v (aR M S r)) := by
          have : M.supportCutoff S.C (r * S.C.R) + 4 * Δ S ≤ aR M S r := by
            show _ ≤ M.supportCutoff S.C (r * S.C.R + 1)
            omega
          have h4 : ((M.supportCutoff S.C (r * S.C.R) : ℕ) : ℝ) + 4 * Δ S ≤ (aR M S r : ℝ) := by exact_mod_cast this
          linarith
        exact le_trans ((time_mono M) x R ((firstAt_le_of_time_ge M F) R E hc)) hEndStep
      have hle := (held_height_le_before_action M F Fx) S A x R E tAwakeEnd H₂ (x.firstAt (M.supportCutoff S.C (r * S.C.R)))
        (x.tickStep v' (M.voteTime S.C (r * S.C.R))) v' H_v hThird hOldStep hk0E hvk hHv
      have hmono := (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_height_mono M F) S.C hXH
      rw [hXh, hh'] at hmono ⊢
      unfold Height at *
      omega
  refine ⟨r', (M.chainStateOf S.C X).T_h, u, j', hrr, hl, hj', hact', ⟨u, hupd, n₀, C₀, X, hU, hC₀,
    hst.trans hC₀, hE3, hXC₀, hkind⟩, hE1, by rw [hE2, hXh, hh'], ?_, hupd, n₀, X, hU, hXf, hE3⟩
  rw [← hT', ← hXT']


namespace PartAHyps
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

variable {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N}
  {GST tGAT tAwakeEnd r H₂ : ℕ} {v : V} {L : Block V} {n' : M.N}

/-- **`cert_source_fast` up to the later end (copy).** `cert_source_fast`'s conclusion at a step `j` at a real time at
most `tEnd`, the later end of the rows `TR`: `cert_source_core_fast_past` with the phase up to `tEnd` and the roots up
to the action time of round `r`, inside the bundle.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed.

Read aloud: a certificate above `H₂` names the entry of a fast block of an honest update run at a tick before the
reading, with the reading allowed up to the later end. -/
theorem cert_source_fast_past (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    {Δs : ℕ} {ΔNet : ℕ} (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet)
    {tEnd c₀ : ℕ} (TR : TickRows M S A x tGAT tAwakeEnd tEnd c₀) {j : ℕ} {w : V}
    {Y T : Block V} {h : Height} (hj : x.time j ≤ tEnd)
    (hY : Y ∈ (x.st j w).tree) (hJ : ProgressCertOn M Y h T) (hH : H₂ < h) :
    ∃ (μ : ℕ) (E : Block V) (u : V) (k : ℕ), x.lbl k = Event.tick u (M.supportCutoff S.C (μ + 1)) ∧
      k < j ∧ u ∈ A.active k ∧
      LineSource M S A x r H₂ μ E ∧ IsEntry M S.C E ∧ (M.chainStateOf S.C E).h = h ∧
      T.root = E.root ∧
      u ∈ updaterAt M S A x μ ∧ ∃ (n₀ : M.N) (X₀ : Block V),
        ConfirmationUpdated M S.C S.P (x.tickInput u (M.supportCutoff S.C (μ + 1)))
          ((M.supportCutoff S.C (μ + 1) : ℕ) : Int) (μ + 1) n₀ ∧
        X₀ ∈ M.fastBlocks n₀ ∧ E.AncestorEq X₀ := by
  have hTE : ((tAwakeEnd : ℕ) : ℝ) ≤ ((tEnd : ℕ) : ℝ) := by exact_mod_cast TR.hTE
  have hOld' : ∀ (k t : ℕ) (u : V) (a' : Attestation V), k < x.firstAt (M.supportCutoff S.C (r * S.C.R)) →
      x.lbl k = Event.tick u t → u ∉ A.corruptedAtTime x tEnd →
      (⟨u, NamedObject.attest a'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (k + 1) - x.sent k → a'.h ≤ H₂ :=
    fun k t u a' h1 h2 h3 h4 => P.hOldStep k t u a' h1 h2 (fun hc => h3 (by
      obtain ⟨i, hi, hci⟩ := Activity.mem_corruptedAtTime.1 hc
      exact Activity.mem_corruptedAtTime.2 ⟨i, le_trans hi hTE, hci⟩)) h4
  obtain ⟨r', E', u, k, -, hk, hkj, hku, hE, hE1, hE2, hE3, hF⟩ := (cert_source_core_fast_past M F) R E U Fx P.hSkew
    (P.hRoots.mono M (by exact_mod_cast P.hEnd)) TR.hThird TR.hAwake TR.hCommittees P.hAnchor P.hOld
    (le_trans P.hEnd TR.hTE) P.hk₀ hOld' (le_trans P.hEndStep hTE) hj hY hJ hH
  exact ⟨r' * S.C.R, E', u, k, hk, hkj, hku, hE, hE1, hE2, hE3, hF⟩

/-- **`F_compat_st` at a step past the bundle's end (copy).** Under `F_compat_st`'s hypotheses, with the
bundle's end `tAwakeEnd` and the rows `TR` up to the later end `tEnd`: at a step `j` at a real time at most `tEnd`, at
which roots name blocks (`hRj`), `w` outside the adversary set, and before the earliest real time of a tick to the
support cutoff of slot `σ + 3`, `w`'s finalized block is compatible with the line source `X`.

Why: `F_compat_st`'s argument, with the fewer-than-a-third premise and the certificate's source
(`cert_source_fast_past`) read up to `tEnd`, and the roots up to the later of `j`'s real time and `tAwakeEnd`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed; `j`: the step.

Read aloud: at a step up to the later end, before any tick to the support cutoff of slot `σ + 3`, an honest
validator's finalized block is compatible with every line source of a slot at most `σ`. -/theorem F_compat_st_past (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet)
    {tEnd c₀ : ℕ} (TR : TickRows M S A x tGAT tAwakeEnd tEnd c₀) {σ j : ℕ} {w : V}
    (hG : ∀ σ', σ' ≤ σ → LineInv M S A x r H₂ σ') (hσ : r * S.C.R ≤ σ)
    (hEnd : M.supportCutoff S.C (σ + 2) ≤ tAwakeEnd) (hjE : x.time j ≤ tEnd)
    (hRj : RootsNameBlocksUntil M A x (x.time j))
    (hw' : w ∉ A.corrupted j)
    (hjc : x.time j < ((M.supportCutoff S.C (σ + 3) : ℕ) : ℝ) - ΔClockAhead) {μ : ℕ} {X : Block V}
    (hX : LineSource M S A x r H₂ μ X) (hμ : μ ≤ σ)
    (hV : ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) - ΔClockAhead ≤ x.time j →
      ∀ u ∈ Hon M S A x (σ + 1), ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (σ + 1)) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) →
      ∃ H_u ∈ (x.tickInput u (M.voteTime S.C (σ + 1))).tree,
        vote = GoldfishVote.mk u (σ + 1) H_u.root ∧ X.AncestorEq H_u) :
    (x.st j w).finalized.compatible X = true := by
  have hEnd1 : M.supportCutoff S.C (σ + 1) ≤ tAwakeEnd :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (Nat.le_succ _)) hEnd
  have hEndR : M.supportCutoff S.C (r * S.C.R + 1) ≤ tAwakeEnd :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega)) hEnd1
  obtain ⟨D, hD, hFD⟩ :=
    (GoldilocksCorrectness.Record.Statements.Executions.finalizedFromChain_of_exec M F) S A x R E
      j w
  rw [hFD]
  have hTE : ((tAwakeEnd : ℕ) : ℝ) ≤ ((tEnd : ℕ) : ℝ) := by exact_mod_cast TR.hTE
  -- roots up to the later of `j`'s real time and the bundle's end
  have hRm : RootsNameBlocksUntil M A x (max (x.time j) ((tAwakeEnd : ℕ) : ℝ)) := by
    rcases max_cases (x.time j) ((tAwakeEnd : ℕ) : ℝ) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
    · exact hRj
    · exact P.hRoots
  by_cases hle : (M.chainStateOf S.C D).h_F ≤ H₂
  · -- `v` held `L` at its tick to the action time of round `r` (`L_held_v`), honest there, in the phase
    have hv' : v ∉ A.corrupted (x.tickStep v (aR M S r)) := E.not_mem_corrupted_of_tick P.hk₀
    have hT : A.AdversaryFewerThanThirdUntil x (validator_count V)
        (max (x.time j) (x.time (x.tickStep v (aR M S r)))) :=
      TR.hThird.mono (max_le hjE (P.hEndStep.trans hTE))
    have hLv : L ∈ (x.st (x.tickStep v (aR M S r)) v).tree := (P.L_held_v M F R E U hEndR).2
    have hFL := (GoldilocksCorrectness.Record.Proofs.Executions.lem68_honest_past_finalized M F Fx) S A x R E hRm j
      (x.tickStep v (aR M S r)) w v D L hT hw' hv' hD hLv
      (by rw [P.hL]; exact Nat.lt_succ_of_le hle) (max_le (le_max_left _ _) (P.hEndStep.trans (le_max_right _ _)))
    exact compatible_of_ancestorEq_compatible hFL
      (P.sources_compatible M F R U hG hEnd (P.source_L M F R U hEndR) hX hσ hμ)
  · have hlt : H₂ < (M.chainStateOf S.C D).h_F := Nat.lt_of_not_le hle
    obtain ⟨hJC, -, hFanc, -⟩ :=
      ((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) S.C D).2.2
        (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le H₂) hlt))
    have hFT : (M.chainStateOf S.C D).F ∈ (x.st j w).tree :=
      (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E _ w D _ hD hFanc
    obtain ⟨μ', Eb, u, kc, hkc, hkcj, -, hE, -, -, hEr, hupd, n₀, X₀, hCU, hX₀f, hEX₀⟩ :=
      P.cert_source_fast_past M F R E U Fx TR hjE hD
        ((GoldilocksCorrectness.Record.Proofs.Executions.progressCertOn_of_justificationCertOn M F) hJC) hlt
    have hFE : (M.chainStateOf S.C D).F = Eb :=
      hRm _ _ ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := j) (v := w) hw' (le_max_left _ _) hFT)
        ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_mono M) x
          (le_trans ((time_mono M) x R hkcj.le) (le_max_left _ _)) (P.source_inHonestTreeBy_tick M F R E U hE hkc)) hEr
    rw [hFE]
    -- the update of slot `μ'` ran at a tick before the reading, so `μ' ≤ σ + 1` (`hSkew`)
    have hμ'1 : μ' ≤ σ + 1 := by
      by_contra h
      have hmono := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
        (show σ + 3 ≤ μ' + 1 by omega)
      have h4 : ((M.supportCutoff S.C (σ + 3) : ℕ) : ℝ) ≤ ((M.supportCutoff S.C (μ' + 1) : ℕ) : ℝ) := by
        exact_mod_cast hmono
      have hkt := (E.tick_active _ _ _ hkc).2.1
      have hkk := (time_mono M) x R hkcj.le
      linarith
    rcases Nat.lt_or_eq_of_le hμ'1 with hlt' | heq
    · exact P.sources_compatible M F R U hG hEnd hE hX (by omega) hμ
    · -- the slot under proof: `Eb` is `X₀` or an ancestor of it, a block `u`'s update of slot `σ + 1`
      -- made fast, which the votes of slot `σ + 1` (`hV`) make compatible with `X`
      subst heq
      have hAnc : anchorCW S tGAT ≤ M.slotStart S.C (σ + 1 + 1) :=
        le_trans P.hAnchor ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (by omega))
      exact compatible_of_ancestorEq_compatible hEX₀
        ((fast_block_compatible_of_votes_core M F) R E U P.hSkew (P.hRoots.mono M (by exact_mod_cast hEnd))
          (P.hCommittees.mono M hEnd) hAnc hupd hCU (hV (by
            have hkt := (E.tick_active _ _ _ hkc).2.1
            rw [show σ + 1 + 1 = σ + 2 from rfl] at hkt
            exact le_trans hkt ((time_mono M) x R hkcj.le))) hX₀f)


/-- **`F_compat_tick` at a tick past the bundle's end (copy).** Under `F_compat_tick`'s hypotheses, with the
support cutoff of slot `σ + 2` in the bundle and at most `c₀`, and the rows `TR`: the finalized block of the state `w`'s
tick to the support cutoff of slot `σ + 2` starts from is compatible with the line source `X`.

Why: that tick, when it exists, is at a real time at most `tEnd` with roots naming blocks there (`TR`), and before any
tick to the support cutoff of slot `σ + 3` (`hSkew`), so `F_compat_st_past` applies; otherwise the tick input is the
initial state, whose finalized block is the genesis block.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed.

Read aloud: the finalized block an honest validator's tick to the support cutoff of slot `σ + 2` reads is compatible
with every line source of a slot at most `σ`, with that tick allowed past the bundle's end. -/theorem F_compat_tick_past (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet)
    {tEnd c₀ : ℕ} (TR : TickRows M S A x tGAT tAwakeEnd tEnd c₀) {σ : ℕ} {w : V}
    (hG : ∀ σ', σ' ≤ σ → LineInv M S A x r H₂ σ') (hσ : r * S.C.R ≤ σ)
    (hEnd : M.supportCutoff S.C (σ + 2) ≤ tAwakeEnd) (hc₀ : M.supportCutoff S.C (σ + 2) ≤ c₀) {μ : ℕ} {X : Block V}
    (hX : LineSource M S A x r H₂ μ X) (hμ : μ ≤ σ)
    (hV : ∀ u ∈ Hon M S A x (σ + 1), ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (σ + 1)) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) →
      ∃ H_u ∈ (x.tickInput u (M.voteTime S.C (σ + 1))).tree,
        vote = GoldfishVote.mk u (σ + 1) H_u.root ∧ X.AncestorEq H_u) :
    (x.tickInput w (M.supportCutoff S.C (σ + 2))).finalized.compatible X = true := by
  obtain ⟨-, hc2, -, hs2, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 2)
  obtain ⟨-, hc3, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 3)
  have h23 : M.supportCutoff S.C (σ + 2) + 4 * Δ S ≤ M.supportCutoff S.C (σ + 3) := by
    rw [show σ + 2 + 1 = σ + 3 from rfl] at hs2
    omega
  by_cases hex : ∃ k : ℕ, x.lbl k = Event.tick w (M.supportCutoff S.C (σ + 2))
  · obtain ⟨k, hk⟩ := hex
    have hks : x.tickStep w (M.supportCutoff S.C (σ + 2)) = k := (tickStep_eq_of_lbl M) x E hk
    rw [show x.tickInput w (M.supportCutoff S.C (σ + 2)) = x.st k w by
      show x.st (x.tickStep w (M.supportCutoff S.C (σ + 2))) w = x.st k w; rw [hks]]
    have hkt := (E.tick_active _ _ _ hk).2.2
    have h4 : ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) + 4 * Δ S ≤ ((M.supportCutoff S.C (σ + 3) : ℕ) : ℝ) := by
      exact_mod_cast h23
    have hA0 := E.ahead_nonneg
    have hB0 := E.behind_nonneg
    have hsk := hSkew
    have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast one_le_Δ S
    exact P.F_compat_st_past M F R E hNet hSkew hRedeliver Sy hΔs U Fx TR hG hσ hEnd (TR.hEndTick k w _ hk hc₀)
      (TR.hRootsTick k w _ hk hc₀) (E.not_mem_corrupted_of_tick hk) (by linarith) hX hμ (fun _ => hV)
  · have h0 : x.tickStep w (M.supportCutoff S.C (σ + 2)) = 0 := by
      unfold Trace.tickStep
      rw [dif_neg hex]
    rw [show x.tickInput w (M.supportCutoff S.C (σ + 2)) = x.st 0 w by
      show x.st (x.tickStep w (M.supportCutoff S.C (σ + 2))) w = x.st 0 w; rw [h0],
      (getElem_zero_st M F) x R, F.init.initial_finalized S.C w]
    exact (compatible_iff _ _).2 (Or.inl (GoldilocksCorrectness.Proofs.Routines.genesis_ancestorEq X))


/-- **`conf_source_at` at a tick past the bundle's end (copy).** Within the bundle up to the support cutoff of
slot `σ + 2`, at most `c₀`, with the rows `TR`, when the invariant holds at every slot up to `σ`: an updater `u` of slot
`σ + 1`, at its tick `k` to the support cutoff of slot `σ + 2` (at a real time at most `tEnd`, possibly past
`tAwakeEnd`), saves for slot `σ + 1` a confirmation that is the line source `X` or a descendant of `X`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed; `u`: the updater; `k`:
  its tick.

Read aloud: an updater of slot `σ + 1` saves a confirmation that extends every line source of an earlier slot, with its
tick allowed past the bundle's end. -/theorem conf_source_past (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet)
    {tEnd c₀ : ℕ} (TR : TickRows M S A x tGAT tAwakeEnd tEnd c₀) {σ : ℕ}
    (hG : ∀ σ', σ' ≤ σ → LineInv M S A x r H₂ σ') (hσ : r * S.C.R ≤ σ)
    (hEnd : M.supportCutoff S.C (σ + 2) ≤ tAwakeEnd) {u : V} (hu : u ∈ updaterAt M S A x (σ + 1)) {k : ℕ}
    (hk : x.lbl k = Event.tick u (M.supportCutoff S.C (σ + 2))) (hc₀ : M.supportCutoff S.C (σ + 2) ≤ c₀) {μ : ℕ} {X : Block V}
    (hX : LineSource M S A x r H₂ μ X) (hμ : μ ≤ σ) :
    ∀ C' : Block V, (x.tickOutput u (M.supportCutoff S.C (σ + 2))).savedConfirmation (σ + 1) = some C' →
      X.AncestorEq C' := by
  have hkE : x.time k ≤ tEnd := TR.hEndTick k u _ hk hc₀
  have hEnd1 : M.supportCutoff S.C (σ + 1) ≤ tAwakeEnd :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (Nat.le_succ _)) hEnd
  obtain ⟨-, hcσ2, -, hs2, hΔ⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 2)
  obtain ⟨-, hcσ3, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 3)
  have hc23 : M.supportCutoff S.C (σ + 2) + 4 * Δ S ≤ M.supportCutoff S.C (σ + 3) := by
    rw [show σ + 2 + 1 = σ + 3 from rfl] at hs2
    omega
  -- the votes clause of slot `σ + 1`
  have hV := P.votes_source M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hσ hEnd hX hμ
  -- `u`'s finalized block at its tick input to the support cutoff of slot `σ + 2`: `F_compat_st` at its tick `k`
  have hks : x.tickStep u (M.supportCutoff S.C (σ + 2)) = k := (tickStep_eq_of_lbl M) x P.E hk
  have hwk : u ∉ A.corrupted k := P.E.not_mem_corrupted_of_tick hk
  have hk2 := (P.E.tick_active _ u _ hk).2.2
  have hA0 := P.E.ahead_nonneg
  have hB0 := P.E.behind_nonneg
  have hsk := P.hSkew
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have h23 : ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) + 4 * Δ S ≤ ((M.supportCutoff S.C (σ + 3) : ℕ) : ℝ) := by
    exact_mod_cast hc23
  have hF : (x.tickInput u (M.supportCutoff S.C (σ + 2))).finalized.compatible X = true := by
    show (x.st (x.tickStep u (M.supportCutoff S.C (σ + 2))) u).finalized.compatible X = true
    rw [hks]
    exact P.F_compat_st_past M F R E hNet hSkew hRedeliver Sy hΔs U Fx TR hG hσ hEnd hkE
      (TR.hRootsTick k u _ hk hc₀) hwk (by linarith) hX hμ (fun _ => hV)
  obtain ⟨hHA, -⟩ := P.members_sets M F U (show r * S.C.R ≤ σ + 1 by omega) hEnd
  exact (GoldilocksCorrectness.Record.Proofs.Executions.confirmations_of_votes_clause M F U) S A x R GST (σ + 1) (Hon M S A x (σ + 1)) X u
    P.E P.hNet P.hSkew P.hRedeliver P.Sy P.hΔs ((per_tick_roots_of_roots_until M F) x P.E P.hRoots (by
      have : ((M.supportCutoff S.C (σ + 1) : ℕ) : ℝ) + Δ S ≤ ((tAwakeEnd : ℕ) : ℝ) := by
        exact_mod_cast (show M.supportCutoff S.C (σ + 1) + Δ S ≤ tAwakeEnd by
          obtain ⟨-, hcσ1, -, hs1, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 1)
          rw [show σ + 1 + 1 = σ + 2 from rfl] at hs1
          omega)
      linarith)) P.hParent
    ((votesCastByOwner_of_unforgeability M F) S A x R P.E) (P.gstSync M F U (show r * S.C.R ≤ σ + 1 by omega)).2.2
    hHA (P.committee M F (show r * S.C.R ≤ σ + 1 by omega) hEnd) hV hu hF


/-- **`stepFrame_source` with the bundle up to the support cutoff of slot `σ + 2` (copy).** With that cutoff
in the bundle and at most `c₀`, and the rows `TR`, when the invariant holds at every slot up to `σ`, every validator
honest at that cutoff satisfies `StepFrameAt` relative to every line source of a slot at most `σ`: the third clause
reads `w`'s tick to that cutoff by `F_compat_tick_past`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed.
- `hV`: every vote of slot `σ + 1` that a member of `Hon M S A x (σ + 1)` put on the wire at its tick to the
  vote time of slot `σ + 1` is for a block of its tick input that is `X` or a descendant of `X`.

Read aloud: the step's frame conditions hold relative to every line source, with the tick to the support cutoff of slot
`σ + 2` allowed past the bundle's end. -/theorem stepFrame_source_past (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet)
    {tEnd c₀ : ℕ} (TR : TickRows M S A x tGAT tAwakeEnd tEnd c₀) {σ : ℕ}
    {w : V} (hG : ∀ σ', σ' ≤ σ → LineInv M S A x r H₂ σ') (hσ : r * S.C.R ≤ σ)
    (hEnd : M.supportCutoff S.C (σ + 2) ≤ tAwakeEnd) (hc₀ : M.supportCutoff S.C (σ + 2) ≤ c₀)
    (hw : w ∉ A.corruptedAtTime x (M.supportCutoff S.C (σ + 2))) {μ : ℕ} {X : Block V}
    (hX : LineSource M S A x r H₂ μ X) (hμ : μ ≤ σ)
    (hV : ∀ u ∈ Hon M S A x (σ + 1), ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (σ + 1)) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) →
      ∃ H_u ∈ (x.tickInput u (M.voteTime S.C (σ + 1))).tree,
        vote = GoldfishVote.mk u (σ + 1) H_u.root ∧ X.AncestorEq H_u) : StepFrameAt M S A x X σ w := by
  obtain ⟨hvσ, -, hfσ, hsσ, hΔ⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S σ
  obtain ⟨hvσ1, hcσ1, -, hsσ1, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 1)
  obtain ⟨hv2, hcσ2, -, hs2, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ + 2)
  have hv1c : M.voteTime S.C (σ + 1) ≤ M.supportCutoff S.C (σ + 2) := by
    rw [show σ + 2 = σ + 1 + 1 by omega] at hcσ2 ⊢
    omega
  have hv12 : M.voteTime S.C (σ + 1) ≤ M.voteTime S.C (σ + 2) := by
    rw [show σ + 2 = σ + 1 + 1 by omega] at hv2 ⊢
    omega
  have hvE : M.voteTime S.C (σ + 1) ≤ tAwakeEnd := le_trans hv1c hEnd
  -- `w`, honest at the support cutoff of slot `σ + 2`, ticks to the vote time of slot `σ + 1` (`tick_before`)
  obtain ⟨hG1, -, -⟩ := P.gstSync M F U hσ
  obtain ⟨kv, hkv, -⟩ := P.tick_before M F (c := M.voteTime S.C (σ + 1)) (by omega)
    (by rw [show σ + 2 = σ + 1 + 1 by omega] at hcσ2 ⊢; omega) hEnd hw
  obtain ⟨h1, h2⟩ := P.stepFrame_vote_source M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hσ hEnd hkv hX hμ
  refine ⟨h1, h2, ?_⟩
  · -- the finalized block at `w`'s tick input to the support cutoff of slot `σ + 2`: `F_compat_tick_past`, that tick read
    -- through `TR`
    exact P.F_compat_tick_past M F R E hNet hSkew hRedeliver Sy hΔs U Fx TR hG hσ hEnd hc₀ hX hμ hV


/-- **`base_source` with the bundle up to the support cutoff of slot `μ + 2` (copy).** With that cutoff in
the bundle and at most `c₀`, and the rows `TR`, when the invariant holds at every slot up to `μ`, the slot invariant
relative to a line source of slot `μ` holds at slot `μ + 1`, and every updater's confirmation of slot `μ + 1` extends
the source: `base_source`'s argument, the confirmations by `conf_source_past` at the updaters' ticks to that cutoff.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed.

Read aloud: the slot invariant relative to a line source holds at the slot after the source's, with the updaters'
ticks of that slot allowed past the bundle's end. -/theorem base_source_past (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet)
    {tEnd c₀ : ℕ} (TR : TickRows M S A x tGAT tAwakeEnd tEnd c₀) {μ : ℕ}
    (hG : ∀ σ', σ' ≤ μ → LineInv M S A x r H₂ σ') (hμ : r * S.C.R ≤ μ)
    (hEnd : M.supportCutoff S.C (μ + 2) ≤ tAwakeEnd) (hc₀ : M.supportCutoff S.C (μ + 2) ≤ c₀) {X : Block V}
    (hX : LineSource M S A x r H₂ μ X) :
    HonestChainExtends M S A x (Hon M S A x (μ + 1)) X (μ + 1) ∧
    ∀ u ∈ updaterAt M S A x (μ + 1), ∀ C' : Block V,
      (x.tickOutput u (M.supportCutoff S.C (μ + 2))).savedConfirmation (μ + 1) = some C' → X.AncestorEq C' := by
  have hA0 := P.E.ahead_nonneg
  have hB0 := P.E.behind_nonneg
  have hsk := P.hSkew
  have hΔ := one_le_Δ S
  have hk := S.C.k_ge_two
  have hσ : r * S.C.R ≤ μ := hμ
  have hEnd1 : M.supportCutoff S.C (μ + 1) ≤ tAwakeEnd :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (Nat.le_succ _)) hEnd
  have hc1 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (μ + 1)
  have hc2 : M.supportCutoff S.C (μ + 2) = M.voteTime S.C (μ + 2) + Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (μ + 2)
  have hc3 : M.supportCutoff S.C (μ + 3) = M.voteTime S.C (μ + 3) + Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (μ + 3)
  have hv2 : M.voteTime S.C (μ + 2) = M.voteTime S.C (μ + 1) + 4 * Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_succ M.toSlotLayout F.sched U) S (μ + 1)
  have hv3 : M.voteTime S.C (μ + 3) = M.voteTime S.C (μ + 2) + 4 * Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_succ M.toSlotLayout F.sched U) S (μ + 2)
  have hv1 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (μ + 1)
  have hs1 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (μ + 1)
  have hs2 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (μ + 2)
  have hdc := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_cases M.toSlotLayout F.sched U) S (μ + 2)
  have hk8 := Nat.mul_le_mul_left (4 * Δ S) hk
  have hm2 : 4 * Δ S * (μ + 2) = 4 * Δ S * (μ + 1) + 4 * Δ S := by ring
  -- the votes of slot `μ + 1` (`votes_source`)
  have hV := P.votes_source M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hσ hEnd hX le_rfl
  obtain ⟨hHA1, hUp1⟩ := P.members_sets M F U (show r * S.C.R ≤ μ + 1 by omega) hEnd
  obtain ⟨-, hUp0⟩ := P.members_sets M F U hσ hEnd1
  -- an updater's tick to the support cutoff of slot `s + 1` is inside the phase when that cutoff and one delay are
  have htickE : ∀ (s : ℕ) (u : V) (k : ℕ), x.lbl k = Event.tick u (M.supportCutoff S.C (s + 1)) →
      M.supportCutoff S.C (s + 1) + Δ S ≤ tAwakeEnd → x.time k ≤ tAwakeEnd := by
    intro s u k hk' hE
    have h1 := (P.E.tick_active k u _ hk').2.2
    have : ((M.supportCutoff S.C (s + 1) + Δ S : ℕ) : ℝ) ≤ ((tAwakeEnd : ℕ) : ℝ) := by exact_mod_cast hE
    push_cast at this
    linarith
  -- the updaters' confirmations of slot `μ + 1` (`conf_source_at`)
  have hConf : ∀ u ∈ updaterAt M S A x (μ + 1), ∀ C' : Block V,
      (x.tickOutput u (M.supportCutoff S.C (μ + 2))).savedConfirmation (μ + 1) = some C' → X.AncestorEq C' := by
    intro u hu C' hC'
    obtain ⟨k, hk', -⟩ := Activity.mem_activeThroughoutToTick.1 hu
    exact P.conf_source_past M F R E hNet hSkew hRedeliver Sy hΔs U Fx TR hG hσ hEnd hu hk' hc₀ hX le_rfl C' hC'
  -- the source's saver `u₀` and its confirmation `C₀` of slot `μ`
  obtain ⟨u₀, hu₀, n₀, C₀, X₀, -, -, hC₀, hXX₀, hX₀C₀, -⟩ := id hX
  obtain ⟨k₀, hk₀, -⟩ := Activity.mem_activeThroughoutToTick.1 hu₀
  have hk₀E := htickE μ u₀ k₀ hk₀ (by omega)
  refine ⟨⟨hV, fun w hw n₂ sent₂ hrun₂ hAw₂ e₂ he₂ hlive₂ => ?_, fun v' hv' C' hC' => hConf v' (hUp1 hv') C' hC'⟩, hConf⟩
  -- the live locks of slot `μ + 2` at a member `w` (`locks_step_of_clauses`)
  have hwc : w ∉ A.corruptedAtTime x (M.supportCutoff S.C (μ + 2)) := (Finset.mem_sdiff.1 hw).2
  have hwU : w ∈ updaterAt M S A x μ :=
    hUp0 (((roundMembers_mono M F) S A (μ + 1) (μ + 2) tAwakeEnd R P.E (Nat.le_succ _) hEnd).1 hw)
  -- the facts of slot `μ`: the live locks of `w`'s revocation of slot `μ + 1` (`base_locks`) and `w`'s saved
  -- confirmation of slot `μ`, compatible with the saver's (Lemma 32)
  have hL2 := P.base_locks M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hEnd hX hwc
  have hL3 : ∀ C' : Block V,
      (x.tickOutput w (M.supportCutoff S.C (μ + 1))).savedConfirmation μ = some C' → C'.compatible X = true := by
    intro C' hC'
    obtain ⟨kw, hkw, -⟩ := Activity.mem_activeThroughoutToTick.1 hwU
    have hkwE := htickE μ w kw hkw (by omega)
    have hRoots' : RootsNameBlocksUntil M A x (max (x.time (x.tickStep w (M.supportCutoff S.C (μ + 1))))
        (x.time (x.tickStep u₀ (M.supportCutoff S.C (μ + 1))))) := by
      rw [(tickStep_eq_of_lbl M) x P.E hkw, (tickStep_eq_of_lbl M) x P.E hk₀]
      exact (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) (max_le hkwE hk₀E) P.hRoots
    exact compatible_of_ancestorEq_both (ancestorEq_refl C') (ancestorEq_trans hXX₀ hX₀C₀)
      ((GoldilocksCorrectness.Record.Proofs.Executions.lem32_saved_confirmations_compatible_state M F U) S A x P.R GST μ
        w u₀ C' C₀ P.E P.hNet P.hSkew P.hRedeliver P.Sy P.hΔs hRoots' (P.gstSync M F U hσ).2.1 hwU hu₀ hC' hC₀)
  -- `w`'s reader up to its tick to the vote time of slot `μ + 1`, from its window from `tGAT`
  have hHon : w ∈ A.activeThroughoutToTick x ((M.dutyWindowStart S.C (μ + 2) : ℕ) : ℤ) (M.voteTime S.C (μ + 1)) := by
    have hd := P.dws M F U (show r * S.C.R ≤ μ + 2 by omega)
    have hdv : M.dutyWindowStart S.C (μ + 2) ≤ M.voteTime S.C (μ + 1) := by omega
    have hdR : ((tGAT + Δ S : ℕ) : ℝ) ≤ ((M.dutyWindowStart S.C (μ + 2) : ℕ) : ℝ) := by exact_mod_cast hd
    push_cast at hdR
    have hve : ((M.voteTime S.C (μ + 1) : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (μ + 2) : ℕ) : ℝ) := by
      exact_mod_cast (show M.voteTime S.C (μ + 1) + Δ S ≤ M.supportCutoff S.C (μ + 2) by omega)
    refine (mem_activeThroughoutToTick_of_mem_activeThroughout M F) x R P.E (by omega) (by exact_mod_cast hdv) ?_
    refine Activity.mem_activeThroughout_of_le ?_ ?_ (P.window M F hwc hEnd)
    · push_cast; linarith
    · linarith
  exact (locks_step_of_clauses M F U) S A x R X μ w P.E hL2 hL3 hHon n₂
    ((locksRevoked_of_vote_tickInput M F U) x R (μ + 2) w n₂ sent₂ hrun₂ hAw₂) e₂ he₂ hlive₂


/-- **`step_source` with the bundle up to the support cutoff of slot `σ + 2` (copy).** With that cutoff in
the bundle and at most `c₀`, and the rows `TR`, when the invariant holds at every slot up to `σ`, the slot invariant
relative to a line source of a slot at most `σ` at slot `σ` gives it at slot `σ + 1`: `step_source`'s argument, the
frames by `stepFrame_source_past` and the confirmations by `conf_source_past`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed.

Read aloud: the slot invariant relative to a line source passes from one slot to the next, with the ticks to the
support cutoff of the next slot allowed past the bundle's end. -/theorem step_source_past (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet)
    {tEnd c₀ : ℕ} (TR : TickRows M S A x tGAT tAwakeEnd tEnd c₀) {σ : ℕ}
    (hG : ∀ σ', σ' ≤ σ → LineInv M S A x r H₂ σ') (hσ : r * S.C.R ≤ σ)
    (hEnd : M.supportCutoff S.C (σ + 2) ≤ tAwakeEnd) (hc₀ : M.supportCutoff S.C (σ + 2) ≤ c₀) {μ : ℕ} {X : Block V}
    (hX : LineSource M S A x r H₂ μ X) (hμ : μ ≤ σ)
    (hInv : HonestChainExtends M S A x (Hon M S A x σ) X σ ∧
      ∀ u ∈ updaterAt M S A x σ, ∀ C' : Block V,
        (x.tickOutput u (M.supportCutoff S.C (σ + 1))).savedConfirmation σ = some C' → X.AncestorEq C') :
    HonestChainExtends M S A x (Hon M S A x (σ + 1)) X (σ + 1) ∧
    ∀ u ∈ updaterAt M S A x (σ + 1), ∀ C' : Block V,
      (x.tickOutput u (M.supportCutoff S.C (σ + 2))).savedConfirmation (σ + 1) = some C' → X.AncestorEq C' := by
  have hA0 := P.E.ahead_nonneg
  have hB0 := P.E.behind_nonneg
  have hsk := P.hSkew
  have hΔ := one_le_Δ S
  have hEnd1 : M.supportCutoff S.C (σ + 1) ≤ tAwakeEnd :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (Nat.le_succ _)) hEnd
  have hc1 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (σ + 1)
  have hc2 : M.supportCutoff S.C (σ + 2) = M.voteTime S.C (σ + 2) + Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (σ + 2)
  have hc3 : M.supportCutoff S.C (σ + 3) = M.voteTime S.C (σ + 3) + Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (σ + 3)
  have hv2 : M.voteTime S.C (σ + 2) = M.voteTime S.C (σ + 1) + 4 * Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_succ M.toSlotLayout F.sched U) S (σ + 1)
  have hv3 : M.voteTime S.C (σ + 3) = M.voteTime S.C (σ + 2) + 4 * Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_succ M.toSlotLayout F.sched U) S (σ + 2)
  -- the votes of slot `σ + 1` (`votes_source`) and the members' frames (`stepFrame_source`)
  have hV := P.votes_source M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hσ hEnd hX hμ
  have hSF : ∀ w ∈ Hon M S A x (σ + 1), StepFrameAt M S A x X σ w := fun w hw =>
    P.stepFrame_source_past M F R E hNet hSkew hRedeliver Sy hΔs U Fx TR hG hσ hEnd hc₀ (Finset.mem_sdiff.1 hw).2 hX hμ hV
  obtain ⟨hHA0, hUp0⟩ := P.members_sets M F U hσ hEnd1
  obtain ⟨hHA1, hUp1⟩ := P.members_sets M F U (show r * S.C.R ≤ σ + 1 by omega) hEnd
  -- the voters of a slot: the committee members of its members, each with its vote
  have hvoters : ∀ s : ℕ, r * S.C.R ≤ s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ u ∈ S.P.committee s ∩ Hon M S A x s, u ∈ Hon M S A x s ∧ u ∈ S.P.committee s ∧
        ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s ∧
          ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s) ∧
            (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
              x.sent (i + 1) - x.sent i := by
    intro s hs hE u hu
    obtain ⟨hK, hH⟩ := Finset.mem_inter.1 hu
    obtain ⟨i, vote, hl, hvi, hvs, hsent⟩ :=
      (GoldilocksCorrectness.Record.Statements.Executions.honest_active_votes M F U) S A x R s u P.E P.hSkew
        ((P.members_sets M F U hs hE).1 hH) hK
    exact ⟨hH, hK, vote, hvi, hvs, i, hl, hsent⟩
  -- roots, per tick, up to the clock value `M.supportCutoff S.C (σ + 1)`
  have hRT : ((M.supportCutoff S.C (σ + 1) : ℕ) : ℝ) + ΔClockBehind ≤ ((tAwakeEnd : ℕ) : ℝ) := by
    have : ((M.supportCutoff S.C (σ + 1) + Δ S : ℕ) : ℝ) ≤ ((tAwakeEnd : ℕ) : ℝ) := by
      exact_mod_cast (show M.supportCutoff S.C (σ + 1) + Δ S ≤ tAwakeEnd by omega)
    push_cast at this
    linarith
  have hStep : HonestChainExtends M S A x (Hon M S A x (σ + 1)) X (σ + 1) :=
    (GoldilocksCorrectness.Record.Proofs.Executions.lem79_step_sets M F U) S A x R GST σ (Hon M S A x σ) (Hon M S A x (σ + 1))
      (fun s => S.P.committee s ∩ Hon M S A x s) X P.E P.hNet P.hSkew P.hRedeliver P.Sy P.hΔs
      ((per_tick_roots_of_roots_until M F) x P.E P.hRoots hRT) P.hParent
      ((votesCastByOwner_of_unforgeability M F) S A x R P.E) (P.gstSync M F U hσ).2.2 hInv.1
      ((roundMembers_mono M F) S A (σ + 1) (σ + 2) tAwakeEnd R P.E (Nat.le_succ _) hEnd).1
      hUp0
      (fun u hu => by
        -- the member's reader to its tick to the vote time of slot `σ + 1`, from its window from `tGAT`
        have hd := P.dws M F U (show r * S.C.R ≤ σ + 1 by omega)
        have hdr := (duty_window_start_real_of_pos M F U) S (σ + 1) (by omega)
        have hdv := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_le_voteTime M.toSlotLayout F.sched) S (σ + 1)
        have hdR : ((tGAT + Δ S : ℕ) : ℝ) ≤ ((M.dutyWindowStart S.C (σ + 1) : ℕ) : ℝ) := by exact_mod_cast hd
        push_cast at hdR
        have hle : duty_window_start S.C (σ + 1) ≤ ((M.voteTime S.C (σ + 1) : ℕ) : ℤ) :=
          le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.duty_window_start_le_dutyWindowStart M.toSlotLayout F.sched U) S (σ + 1))
            (by exact_mod_cast (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_le_voteTime M.toSlotLayout F.sched) S (σ + 1))
        have hve : ((M.voteTime S.C (σ + 1) : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (σ + 2) : ℕ) : ℝ) := by
          exact_mod_cast (show M.voteTime S.C (σ + 1) + Δ S ≤ M.supportCutoff S.C (σ + 2) by omega)
        refine (mem_activeThroughoutToTick_of_mem_activeThroughout M F) x R P.E (by omega) hle ?_
        refine Activity.mem_activeThroughout_of_le ?_ ?_ (P.window M F (Finset.mem_sdiff.1 hu).2 hEnd)
        · rw [hdr]; linarith
        · linarith)
      hUp1
      (fun u hu hX => (Finset.mem_sdiff.1 (hHA1 hu)).2 (Finset.mem_union_right _ hX))
      (hvoters σ hσ hEnd1) (hvoters (σ + 1) (by omega) hEnd)
      (fun w _ => ((counting_of_committee_majority_st M F) S A x R P.E σ (x.tickStep w (M.voteTime S.C (σ + 1)))
        (Hon M S A x σ) w (P.committee M F hσ hEnd1)).2.2)
      (fun v' _ => ((counting_of_committee_majority_st M F) S A x R P.E (σ + 1)
        (x.tickStep v' (M.supportCutoff S.C (σ + 2))) (Hon M S A x (σ + 1)) v' (P.committee M F (by omega) hEnd)).2.1)
      (fun w hw => (hSF w hw).1) (fun w hw => (hSF w hw).2.1) (fun w hw => (hSF w hw).2.2)
  refine ⟨hStep, fun u hu C' hC' => ?_⟩
  -- an updater of slot `σ + 1` ticks to the support cutoff of slot `σ + 2`, possibly past the bundle's end
  obtain ⟨k, hk, -⟩ := Activity.mem_activeThroughoutToTick.1 hu
  exact P.conf_source_past M F R E hNet hSkew hRedeliver Sy hΔs U Fx TR hG hσ hEnd hu hk hc₀ hX hμ C' hC'

/-- **The line invariant at the slot whose next support cutoff is the bundle's end.** With the support cutoff of
slot `σ + 1` in the bundle and at most `c₀`, and the rows `TR`: the slot invariant holds at slot `σ` relative to every
line source of an earlier slot. `lineInv_all` gives it when the support cutoff of slot `σ + 2` is in the bundle; here
the invariant at every earlier slot is `lineInv_all`'s, and the step to slot `σ` (`step_source_past`) or the base of a
source of slot `σ − 1` (`base_source_past`) read the ticks to the support cutoff of slot `σ + 1` through `TR`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed.

Read aloud: the line invariant holds at slot `σ` when the support cutoff of slot `σ + 1` is in the bundle, with the
ticks to that cutoff read up to the later end. -/
theorem lineInv_last (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GSTe)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (P : PartAHyps M S A x GST tGAT tAwakeEnd r H₂ v L n' Δs (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet)
    {tEnd c₀ : ℕ} (TR : TickRows M S A x tGAT tAwakeEnd tEnd c₀) {σ : ℕ}
    (hEndσ : M.supportCutoff S.C (σ + 1) ≤ tAwakeEnd) (hc₀ : M.supportCutoff S.C (σ + 1) ≤ c₀) :
    LineInv M S A x r H₂ σ := by
  intro μ X hX hμσ
  have hs := hX.slot_ge M F
  -- the invariant at every earlier slot, inside the bundle
  have hG : ∀ σ', σ' < σ → LineInv M S A x r H₂ σ' := fun σ' h =>
    P.lineInv_all M F R E hNet hSkew hRedeliver Sy hΔs U Fx σ'
      (le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
        (by omega)) hEndσ)
  obtain ⟨σ₀, rfl⟩ : ∃ σ₀, σ = σ₀ + 1 := ⟨σ - 1, by omega⟩
  rcases Nat.lt_or_eq_of_le hμσ with hlt | heq
  · -- a source of a slot `μ` with `μ + 1 < σ`: the step from slot `σ - 1`
    exact P.step_source_past M F R E hNet hSkew hRedeliver Sy hΔs U Fx TR (fun σ' h => hG σ' (by omega)) (by omega)
      hEndσ hc₀ hX (by omega) (hG σ₀ (by omega) μ X hX (by omega))
  · -- the source's own next slot: the base
    obtain rfl : μ = σ₀ := by omega
    exact P.base_source_past M F R E hNet hSkew hRedeliver Sy hΔs U Fx TR (fun σ' h => hG σ' (by omega)) hs hEndσ hc₀ hX

end PartAHyps

end TickPast


/-- **C1, the round base at an opening after the fast block (copy with the round's first slot).**
The proof; the audited statement is in `Statements/Executions/Lemma89Statements.lean`. The update of
`v` at the action time is an outcome `(n', sent)` of `v`'s tick there with `L` among the fast blocks
of `n'` (template A2), without A2's hypothesis that `v` has been awake since the duty window's start
of slot `r * R + 1`: `hAwake`, `hAnchor` and `hv` give it, as for `fast_block_base`'s twin. Why: the
proposal's parent extends every line source of a slot at least two slots before `s`
(`parent_extends_sources`); the roots before the vote time of slot `s` and before the support cutoff
of slot `s + 1` are such sources (`root_source`; at the support cutoff, a round's first slot before
`s`, `round_slot_le_of_lt`); the values of `head_height_floor` (the least chain-state height a
viable block may have) are at most the heights of such sources or of `L` (`floor_le_of_sources`);
the live locks are on line sources of slots before `s − 1`.

Roots name blocks until `M.supportCutoff S.C (s + 2)`: the bundle `PartAHyps` is built with its end
time `M.supportCutoff S.C (s + 2)`, the latest time its kit reads here.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed.

 Clause 2 is proved by induction on the step of each tick to that
cutoff, with the per-member step `updater_saves_of_finalized_on_proposal` (C3's argument). At both clock bounds `0` and
with `dev`'s reads before the cutoff, `hNoCol` is not needed.

Read aloud: after the fast block's round every honest round opening slot finds the members' frames on its
parent's chain and no lock against it. -/
theorem round_base_after_fast_block_opening (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (Run : RunFacts M S x) (GST tGAT tAwakeEnd r H₂ s : ℕ) (v : V) (L B : Block V)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (s + 2)))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hAnchor : anchorCW S tGAT ≤ M.slotStart S.C (r * S.C.R + 1))
    (hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂)
    (hv : v ∉ A.corruptedAtTime x (aR M S r))
    (hL : (M.chainStateOf S.C L).h = H₂ + 1)
    (n' : M.N) (sent : List (NamedObject V))
    (hUpdate : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (aR M S r))
        ((aR M S r : ℕ) : Int))
    (hFast : L ∈ M.fastBlocks n')
    (hs : r * S.C.R + S.C.k + 2 ≤ s) (hsR : S.C.R ∣ s)
    (hEnd : M.supportCutoff S.C (s + 2) ≤ tAwakeEnd)
    (hp : S.P.proposer s ∉ A.corruptedAtTime x (M.supportCutoff S.C s))
    (hB : ProposalAt M S x s B)
    (hNoCol : ¬ RootCollisionAtProposal M S A x s B) :
    RoundBaseAt M S A x B s := by
  have hk2 := S.C.k_ge_two
  have hR2 := S.C.R_ge_two
  have hΔ := GoldilocksCorrectness.Proofs.Routines.one_le_Δ S
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hsk := hSkew
  have hcm : ∀ a b : ℕ, a ≤ b → M.supportCutoff S.C a ≤ M.supportCutoff S.C b := fun a b h =>
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S h
  -- the bundle with its end at the support cutoff of slot `s + 2`
  have P := (PartAHyps.of_tick M F U) (tAwakeEnd := M.supportCutoff S.C (s + 2)) Run E hNet hSkew hRedeliver Sy
    hΔs hRoots hParent hGST (hThird.mono (by exact_mod_cast hEnd))
    (fun i u hi => hAwake i u (le_trans hi (by exact_mod_cast hEnd)))
    (fun s h1 h2 => hActive s h1 (le_trans h2 hEnd)) (hCommittees.mono M hEnd) hAnchor hOld hv hUpdate hFast hL
    (hcm _ _ (by omega))
  have hG : ∀ σ', σ' ≤ s → LineInv M S A x r H₂ σ' :=
    P.lineInv_upto M F Run E hNet hSkew hRedeliver Sy hΔs U Fx le_rfl
  have hσ : r * S.C.R ≤ s := by omega
  obtain ⟨hvs, hcs, -, hss, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S s
  obtain ⟨hvs1, hcs1, -, hss1, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (s + 1)
  rw [show s + 1 + 1 = s + 2 from rfl] at hss1
  obtain ⟨-, hcs2, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (s + 2)
  have haR : aR M S r = M.supportCutoff S.C (r * S.C.R + 1) := rfl
  have hcr : M.supportCutoff S.C (r * S.C.R + 1) + Δ S ≤ M.voteTime S.C s := by
    have := hcm (r * S.C.R + 1) (s - 1) (by omega)
    obtain ⟨-, hc', -, hs', -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (s - 1)
    rw [show s - 1 + 1 = s by omega] at hs'
    omega
  obtain ⟨hG1, -, -⟩ := P.gstSync M F U (le_refl (r * S.C.R))
  have hvr := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_mono M.toSlotLayout F.sched) S
    (show r * S.C.R ≤ s by omega)
  have hk₀ := P.hk₀
  have hk₀T := (E.tick_active _ _ _ hk₀).2.2
  have hk₀A := (E.tick_active _ _ _ hk₀).1
  -- the proposal's parent extends every line source of a slot at least two slots before `s`
  have hPar := P.parent_extends_sources M F Run E hNet hSkew hRedeliver Sy hΔs U Fx
    (show r * S.C.R + S.C.k + 2 ≤ s by omega) (hcm _ _ (by omega)) hp hB
  have hmem : ∀ σ : ℕ, ∀ w ∈ Hon M S A x σ, w ∉ A.corruptedAtTime x (M.supportCutoff S.C (σ + 1)) := by
    intro σ w hw
    unfold Hon roundMembers at hw
    exact (Finset.mem_sdiff.1 hw).2
  -- clause 1
  have hC1 : ∀ w ∈ Hon M S A x s, (M.get_fc_root (x.tickInput w (M.voteTime S.C s))).AncestorEq B.parent ∧
      M.head_height_floor (x.tickInput w (M.voteTime S.C s)) ≤ (M.chainStateOf S.C B.parent).h := by
    intro w hw
    -- clause 1: `w`'s tick to the vote time of slot `s` (`root_source_st`, `floor_le_of_sources_st`); every source
    -- whose round's action time an honest validator ticked to before that tick is of a slot `μ` with `μ + 2 ≤ s`
    have hwc : w ∉ A.corruptedAtTime x (M.supportCutoff S.C s) :=
      (not_mem_corruptedAtTime_of_le M) x Run E (hcm _ _ (Nat.le_succ s)) (hmem s w hw)
    obtain ⟨k, hk, -⟩ := P.tick_before M F (w := w) (c := M.voteTime S.C s) (t := M.supportCutoff S.C s)
      (by omega) (by omega) (hcm _ _ (by omega)) hwc
    have hti : x.tickInput w (M.voteTime S.C s) = x.st k w := by
      unfold Trace.tickInput
      rw [(tickStep_eq_of_lbl M) x E hk]
    rw [hti]
    have hkT := (E.tick_active _ _ _ hk).2.2
    have hw' : w ∉ A.corrupted k := E.not_mem_corrupted_of_tick hk
    have hgap : ((aR M S r : ℕ) : ℝ) + Δ S ≤ ((M.voteTime S.C s : ℕ) : ℝ) := by
      exact_mod_cast (show aR M S r + Δ S ≤ M.voteTime S.C s by omega)
    have hk₀k : x.tickStep v (aR M S r) < k := (lt_of_time_lt M) x Run (by linarith [(E.tick_active _ _ _ hk).2.1])
    have hjt : x.time k < ((M.supportCutoff S.C (s + 2) : ℕ) : ℝ) - ΔClockAhead := by
      have : ((M.voteTime S.C s : ℕ) : ℝ) + 2 * Δ S ≤ ((M.supportCutoff S.C (s + 2) : ℕ) : ℝ) := by
        exact_mod_cast (show M.voteTime S.C s + 2 * Δ S ≤ M.supportCutoff S.C (s + 2) by omega)
      linarith
    have hQ : ∀ (r' : ℕ) (Eb : Block V), r ≤ r' →
        (∃ (u : V) (k' : ℕ), x.lbl k' = Event.tick u (aR M S r') ∧ k' < k ∧ u ∈ A.active k') →
        LineSource M S A x r H₂ (r' * S.C.R) Eb → Eb.AncestorEq B.parent := by
      rintro r' Eb - ⟨u, k', hk', hk'k, -⟩ hE
      have h1 := (E.tick_active _ _ _ hk').2.1
      have h2 := (time_mono M) x Run hk'k.le
      have haR' : aR M S r' = M.supportCutoff S.C (r' * S.C.R + 1) := rfl
      rw [haR'] at h1
      have h3 : ((M.supportCutoff S.C (r' * S.C.R + 1) : ℕ) : ℝ) < ((M.voteTime S.C s + Δ S : ℕ) : ℝ) := by
        push_cast; linarith
      have h : M.supportCutoff S.C (r' * S.C.R + 1) < M.voteTime S.C s + Δ S := by exact_mod_cast h3
      refine hPar _ Eb hE ?_
      by_contra hn
      have := hcm s (r' * S.C.R + 1) (by omega)
      omega
    have ht0 : ∃ (u : V) (k' : ℕ), x.lbl k' = Event.tick u (aR M S r) ∧ k' < k ∧ u ∈ A.active k' :=
      ⟨v, _, hk₀, hk₀k, hk₀A⟩
    obtain ⟨r', hrr, htk, hsrc⟩ := P.root_source_st M F Run E hNet hSkew hRedeliver Sy hΔs U Fx hG hσ le_rfl
      ht0 hjt hw'
    exact ⟨hQ r' _ hrr htk hsrc,
      P.floor_le_of_sources_st M F Run E hNet hSkew hRedeliver Sy hΔs U Fx hG le_rfl ht0 hjt hw' hQ⟩
  -- clause 3
  have hC3 : ∀ w ∈ Hon M S A x s, ∀ (n₁ : M.N) (sent₁ : List (NamedObject V)),
      .ok (n₁, sent₁) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C s)) ((M.voteTime S.C s : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C s)) s →
      ∀ e ∈ M.lockEntries n₁, M.is_live (x.tickInput w (M.voteTime S.C s)) ((M.voteTime S.C s : ℕ) : Int) e = true →
        e.B.AncestorEq B.parent := by
    intro w hw n₁ sent₁ hrun₁ hAw₁ e he hlive
    -- clause 3: the live locks are on line sources of slots `μ + 2 ≤ s` (`late_locks_on_sources` at slot `s − 1`)
    obtain ⟨s₀, rfl⟩ : ∃ s₀, s = s₀ + 1 := ⟨s - 1, by omega⟩
    have hws : w ∈ Hon M S A x s₀ := by
      unfold Hon roundMembers
      exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _,
        (not_mem_corruptedAtTime_of_le M) x Run E (hcm _ _ (Nat.le_succ _)) (hmem (s₀ + 1) w hw)⟩
    have hvE : M.voteTime S.C (s₀ + 1) ≤ M.supportCutoff S.C (s₀ + 1 + 2) := by
      have := hcm (s₀ + 1) (s₀ + 1 + 2) (by omega)
      omega
    obtain ⟨D, ⟨μ, hμ, hsrc⟩, heD⟩ := P.late_locks_on_sources M F Run E U
      (show r * S.C.R + S.C.k ≤ s₀ by omega) hvE hws n₁ sent₁ hrun₁ hAw₁ e he hlive
    exact ancestorEq_trans heD (hPar μ D hsrc (by omega))
  -- clause 2 (, re-check 91 section 5.3; the induction of re-check 88 section 1.2): the helper
  -- `updater_saves_of_finalized_on_proposal` at every updater of slot `s` (its honesty read at its own tick, T-C-91-3), with
  -- `hPrev` built as C2 builds it
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hA1 : anchorCW S tGAT ≤ M.slotStart S.C (s + 1) :=
    le_trans hAnchor ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (by omega))
  have hA0' : anchorCW S tGAT ≤ M.slotStart S.C s :=
    le_trans hAnchor ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (by omega))
  have hdws := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_of_anchor M.toSlotLayout F.sched U) S tGAT s
    hA1
  have hEnd1 : M.supportCutoff S.C (s + 1) ≤ tAwakeEnd := le_trans (hcm _ _ (by omega)) hEnd
  obtain ⟨μA, hμA, hAsrc⟩ := P.anchor_source M F Run E hNet hSkew hRedeliver Sy hΔs U Fx
    (show r * S.C.R + S.C.k + 2 ≤ s by omega) (hcm _ _ (by omega)) hp
  have hGs2 : ∀ σ', σ' ≤ s - 2 → LineInv M S A x r H₂ σ' := fun σ' h => hG σ' (by omega)
  have hPrev := P.votes_source M F Run E hNet hSkew hRedeliver Sy hΔs U Fx hGs2 (show r * S.C.R ≤ s - 2 by omega)
    (hcm _ _ (by omega)) hAsrc (by omega)
  rw [show s - 2 + 1 = s - 1 by omega] at hPrev
  have hSaves := (updater_saves_of_finalized_on_proposal M F U Fx) S A x Run GST tGAT tAwakeEnd s B E hNet hSkew hRedeliver Sy hΔs
    ((GoldilocksCorrectness.Record.Statements.Executions.RootsNameBlocksUntil.mono M) (hcm _ _ (by omega)) hRoots)
    hParent hGST hThird hAwake hActive hCommittees (by omega) hA1 hA0' hEnd hp hB hC1 hC3 hNoCol
    (fun u hu vote hvote => hPrev u (Finset.mem_inter.1 hu).2 vote hvote)
  have hc12 : ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + 4 * Δ S ≤ ((M.supportCutoff S.C (s + 2) : ℕ) : ℝ) := by
    exact_mod_cast (show M.supportCutoff S.C (s + 1) + 4 * Δ S ≤ M.supportCutoff S.C (s + 2) by omega)
  have hvc : ((aR M S r : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) := by
    exact_mod_cast (show aR M S r + Δ S ≤ M.supportCutoff S.C (s + 1) by omega)
  -- the roots at every tick to the support cutoff of slot `s + 1` by a validator outside the adversary set at it, by
  -- strong induction on the tick's step: the root is a line source of a round's first slot (`root_source_st_attester`);
  -- before `s` it is on `B.parent`'s chain (`parent_extends_sources`); of slot `s` it is on the confirmation of an updater
  -- whose tick to that cutoff came before, which saved `B` (the induction hypothesis and the helper)
  have hRootK : ∀ (K : ℕ) (w : V), x.lbl K = Event.tick w (M.supportCutoff S.C (s + 1)) → w ∉ A.corrupted K →
      (M.get_fc_root (x.st K w)).AncestorEq B := by
    intro K
    induction K using Nat.strong_induction_on with
    | _ K ih =>
    intro w hK hwK
    have hKt := (E.tick_active _ _ _ hK).2
    have hk₀K : x.tickStep v (aR M S r) < K := (lt_of_time_lt M) x Run (by linarith [hKt.1])
    have hjt : x.time K < ((M.supportCutoff S.C (s + 2) : ℕ) : ℝ) - ΔClockAhead := by linarith [hKt.2]
    obtain ⟨r', -, ⟨u, k, hk, hkK, -, hu, C₀, hC₀, hroot⟩, hsrc⟩ :=
      P.root_source_st_attester M F Run E hNet hSkew hRedeliver Sy hΔs U Fx hG hσ le_rfl hk₀K hjt hwK
    have haR' : aR M S r' = M.supportCutoff S.C (r' * S.C.R + 1) := rfl
    rw [haR'] at hk hu
    -- `r' * R ≤ s`: `u`'s tick to the support cutoff of slot `r' * R + 1` comes before `K`
    have hle : r' * S.C.R ≤ s := by
      by_contra hn
      have hm := hcm (s + 2) (r' * S.C.R + 1) (by omega)
      have h1 := (E.tick_active _ _ _ hk).2.1
      have h2 := (time_mono M) x Run hkK.le
      have h4 : ((M.supportCutoff S.C (s + 2) : ℕ) : ℝ) ≤ ((M.supportCutoff S.C (r' * S.C.R + 1) : ℕ) : ℝ) := by
        exact_mod_cast hm
      linarith [hKt.2]
    rcases Nat.lt_or_ge (r' * S.C.R) s with hlt | hge
    · -- a source of a round's first slot before `s`, so of a slot at most `s − R`: on `B.parent`'s chain
      obtain ⟨q, hq⟩ := hsR
      have hr'q : r' < q := by
        by_contra hc
        have h5 := Nat.mul_le_mul_right S.C.R (not_lt.1 hc)
        rw [hq, Nat.mul_comm S.C.R q] at hlt
        omega
      have h6 := Nat.mul_le_mul_right S.C.R (Nat.succ_le_of_lt hr'q)
      rw [Nat.succ_mul] at h6
      have h3 : r' * S.C.R + 2 ≤ s := by rw [hq, Nat.mul_comm S.C.R q]; omega
      exact ancestorEq_trans (hPar _ _ hsrc h3) (GoldilocksCorrectness.Proofs.Routines.parent_ancestorEq B)
    · -- a source of slot `s`: `u` saved `B` (its root at its earlier tick is on `B`'s chain, so its finalized block)
      have hrs : r' * S.C.R = s := le_antisymm hle hge
      rw [hrs] at hk hu hC₀
      have huk : u ∉ A.corrupted k := E.not_mem_corrupted_of_tick hk
      have hti : x.tickInput u (M.supportCutoff S.C (s + 1)) = x.st k u := by
        unfold Trace.tickInput
        rw [(tickStep_eq_of_lbl M) x E hk]
      have hfin : (x.tickInput u (M.supportCutoff S.C (s + 1))).finalized.AncestorEq B := by
        rw [hti]
        exact ancestorEq_trans
          ((GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F) S A x Run E k u)
          (ih k hkK u hk huk)
      have hsv := hSaves u (hActive s (by omega) hEnd1 u hu).2
        (by rw [(tickStep_eq_of_lbl M) x E hk]; exact huk) hfin
      have hCB : C₀ = B := Option.some_injective _ (hC₀.symm.trans hsv)
      rw [hCB] at hroot
      exact hroot
  refine ⟨hC1, fun w hw => ?_, hC3⟩
  -- clause 2 at every updater: the tick from membership in `updaterAt`
  obtain ⟨k, hk, -⟩ := Activity.mem_activeThroughoutToTick.1 hw
  have hwk : w ∉ A.corrupted k := E.not_mem_corrupted_of_tick hk
  have hti : x.tickInput w (M.supportCutoff S.C (s + 1)) = x.st k w := by
    unfold Trace.tickInput
    rw [(tickStep_eq_of_lbl M) x E hk]
  rw [hti]
  refine ⟨hRootK k w hk hwk, ?_⟩
  -- the `head_height_floor` half: every line source of a round's first slot to whose action time an honest validator
  -- ticked before `k` is on `B`'s chain (`floor_le_of_sources_st`)
  have hKt := (E.tick_active _ _ _ hk).2
  have hk₀k : x.tickStep v (aR M S r) < k := (lt_of_time_lt M) x Run (by linarith [hKt.1])
  have hjt : x.time k < ((M.supportCutoff S.C (s + 2) : ℕ) : ℝ) - ΔClockAhead := by linarith [hKt.2]
  have ht0 : ∃ (u : V) (k' : ℕ), x.lbl k' = Event.tick u (aR M S r) ∧ k' < k ∧ u ∈ A.active k' :=
    ⟨v, _, hk₀, hk₀k, hk₀A⟩
  refine P.floor_le_of_sources_st M F Run E hNet hSkew hRedeliver Sy hΔs U Fx hG le_rfl ht0 hjt hwk ?_
  rintro r' Eb - ⟨u, k', hk', hk'k, -⟩ hE
  have haR' : aR M S r' = M.supportCutoff S.C (r' * S.C.R + 1) := rfl
  rw [haR'] at hk'
  have hle : r' * S.C.R ≤ s := by
    by_contra hn
    have hm := hcm (s + 2) (r' * S.C.R + 1) (by omega)
    have h1 := (E.tick_active _ _ _ hk').2.1
    have h2 := (time_mono M) x Run hk'k.le
    have h4 : ((M.supportCutoff S.C (s + 2) : ℕ) : ℝ) ≤ ((M.supportCutoff S.C (r' * S.C.R + 1) : ℕ) : ℝ) := by
      exact_mod_cast hm
    linarith [hKt.2]
  rcases Nat.lt_or_ge (r' * S.C.R) s with hlt | hge
  · obtain ⟨q, hq⟩ := hsR
    have hr'q : r' < q := by
      by_contra hc
      have h5 := Nat.mul_le_mul_right S.C.R (not_lt.1 hc)
      rw [hq, Nat.mul_comm S.C.R q] at hlt
      omega
    have h6 := Nat.mul_le_mul_right S.C.R (Nat.succ_le_of_lt hr'q)
    rw [Nat.succ_mul] at h6
    have h3 : r' * S.C.R + 2 ≤ s := by rw [hq, Nat.mul_comm S.C.R q]; omega
    exact ancestorEq_trans (hPar _ _ hE h3) (GoldilocksCorrectness.Proofs.Routines.parent_ancestorEq B)
  · -- a line source of slot `s`: on the confirmation of an updater `u'` of slot `s`, honest at its tick to the support
    -- cutoff of slot `s + 1`; its root at that tick is on `B`'s chain (`hRootK`) and it saved `B` (the helper, T-C-91-3)
    have hrs : r' * S.C.R = s := le_antisymm hle hge
    rw [hrs] at hE
    obtain ⟨u', hu', n₀, C₀, X₀, -, -, hC₀, hEX, hXC, -⟩ := hE
    obtain ⟨k'', hk'', -⟩ := Activity.mem_activeThroughoutToTick.1 hu'
    have hu'k : u' ∉ A.corrupted k'' := E.not_mem_corrupted_of_tick hk''
    have hti' : x.tickInput u' (M.supportCutoff S.C (s + 1)) = x.st k'' u' := by
      unfold Trace.tickInput
      rw [(tickStep_eq_of_lbl M) x E hk'']
    have hfin : (x.tickInput u' (M.supportCutoff S.C (s + 1))).finalized.AncestorEq B := by
      rw [hti']
      exact ancestorEq_trans
        ((GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F) S A x Run E k'' u')
        (hRootK k'' u' hk'' hu'k)
    have hsv := hSaves u' hu' (by rw [(tickStep_eq_of_lbl M) x E hk'']; exact hu'k) hfin
    have hCB : C₀ = B := Option.some_injective _ (hC₀.symm.trans hsv)
    rw [hCB] at hXC
    exact ancestorEq_trans hEX hXC


/-- **C2, every round after the fast block is quiet relative to its own confirmations (copy with
the round's first slot and no root collision).** The proof; the audited statement is in
`Statements/Executions/Lemma89Statements.lean`. The update of `v` at the action time is an outcome
`(n', sent)` of `v`'s tick there with `L` among the fast blocks of `n'` (template A2), without A2's
hypothesis that `v` has been awake since the duty window's start of slot `r * R + 1`: `hAwake`,
`hAnchor` and `hv` give it, as for `fast_block_base`'s twin. Why: the first two clauses are C1's
(`round_base_after_fast_block_opening`); the members save `B` (`healed_round_base_of_prev_votes`,
the previous slot's votes extending the proposer's anchor by `anchor_source` and the line
invariant), so `B` and every member's confirmation of a slot from `s − 1` on are line sources
(`source_conf`), and `stepFrame_source` gives the third and fourth; for the fifth, the next
proposer's root is a line source of a slot `μ ≤ s'' − 2` (`root_source`), on the chain of its own
confirmation when `μ = s'' − 2` and of any member's confirmation of slot `s'' − 2`
(`member_saves_confirmation`) otherwise, and `frame_source_at` gives the viable head.

Roots name blocks until `M.supportCutoff S.C s''`: the bundle `PartAHyps` is built with its end time
`M.supportCutoff S.C s''`, the latest time its kit reads here; C1 and C3 read up to
`M.supportCutoff S.C (s + 2)`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed.

Read aloud: after the fast block, every honest round whose proposal's root is fresh is quiet, with
no window needed. -/
theorem quiet_round_after_fast_block_opening (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd r H₂ s s'' : ℕ) (v : V)
      (L B : Block V)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C s''))
    -- roots name blocks up to the real time of every tick to a clock value at most the support cutoff of slot
    -- `s''` ('s row)
    (hRootsTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C s'' →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hAnchor : anchorCW S tGAT ≤ M.slotStart S.C (r * S.C.R + 1))
    (hOld : OldAttestationsAtMostHonestAt M S A x (aR M S r) (aR M S r) H₂)
    (hv : v ∉ A.corruptedAtTime x (aR M S r))
    (hL : (M.chainStateOf S.C L).h = H₂ + 1)
    (n' : M.N) (sent : List (NamedObject V))
    (hUpdate : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (aR M S r))
        ((aR M S r : ℕ) : Int))
    (hFast : L ∈ M.fastBlocks n')
    (hs : r * S.C.R + S.C.k + 2 ≤ s) (hsR : S.C.R ∣ s) (hs'' : s + S.C.R ≤ s'')
    (hEnd : M.supportCutoff S.C s'' ≤ tAwakeEnd)
    -- every tick to a clock value at most the support cutoff of slot `s''` is at a real time at most `tAwakeEnd`
    -- ('s row)
    (hEndTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C s'' →
      x.time k ≤ tAwakeEnd)
    (hp : S.P.proposer s ∉ A.corruptedAtTime x (M.supportCutoff S.C s))
    (hq : S.P.proposer s'' ∉ A.corruptedAtTime x (M.supportCutoff S.C s''))
    (hB : ProposalAt M S x s B)
    (hNoCol : ¬ RootCollisionAtProposal M S A x s B) :
    QuietRoundOnConfirmations M S A x (Hon M S A x) B s s'' := by
  have hk2 := S.C.k_ge_two
  have hR2 := S.C.R_ge_two
  have hΔ := GoldilocksCorrectness.Proofs.Routines.one_le_Δ S
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hsk := hSkew
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hcm : ∀ a b : ℕ, a ≤ b → M.supportCutoff S.C a ≤ M.supportCutoff S.C b := fun a b h =>
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S h
  have hs2 : s + 2 ≤ s'' := by omega
  -- the bundle with its end at the support cutoff of slot `s''`, and the rows past it
  have P := (PartAHyps.of_tick M F U) (tAwakeEnd := M.supportCutoff S.C s'') R E hNet hSkew hRedeliver Sy
    hΔs hRoots hParent hGST (hThird.mono (by exact_mod_cast hEnd))
    (fun i u hi => hAwake i u (le_trans hi (by exact_mod_cast hEnd)))
    (fun s h1 h2 => hActive s h1 (le_trans h2 hEnd)) (hCommittees.mono M hEnd) hAnchor hOld hv hUpdate hFast hL
    (hcm _ _ (by omega))
  have TR : TickRows M S A x tGAT (M.supportCutoff S.C s'') tAwakeEnd (M.supportCutoff S.C s'') :=
    ⟨hEnd, hThird, hAwake, hCommittees, hRootsTick, hEndTick⟩
  have hEndM : ∀ σ : ℕ, σ ≤ s'' → M.supportCutoff S.C σ ≤ M.supportCutoff S.C s'' := fun σ h => hcm _ _ h
  have hEndA : ∀ σ : ℕ, σ ≤ s'' → M.supportCutoff S.C σ ≤ tAwakeEnd := fun σ h => le_trans (hEndM σ h) hEnd
  have hG : ∀ σ', σ' ≤ s → LineInv M S A x r H₂ σ' :=
    P.lineInv_upto M F R E hNet hSkew hRedeliver Sy hΔs U Fx (hEndM _ hs2)
  have hσ : r * S.C.R ≤ s := by omega
  obtain ⟨hvs, hcs, -, hss, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S s
  obtain ⟨hvs1, hcs1, -, hss1, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (s + 1)
  rw [show s + 1 + 1 = s + 2 from rfl] at hss1
  obtain ⟨-, hcs2, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (s + 2)
  obtain ⟨-, hcr1, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (r * S.C.R + 1)
  have haR : aR M S r = M.supportCutoff S.C (r * S.C.R + 1) := rfl
  have hcr : M.supportCutoff S.C (r * S.C.R + 1) + Δ S ≤ M.voteTime S.C s := by
    have := hcm (r * S.C.R + 1) (s - 1) (by omega)
    obtain ⟨-, hc', -, hs', -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (s - 1)
    rw [show s - 1 + 1 = s by omega] at hs'
    omega
  obtain ⟨hG1, -, -⟩ := P.gstSync M F U (le_refl (r * S.C.R))
  have hvr := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_mono M.toSlotLayout F.sched) S
    (show r * S.C.R ≤ s by omega)
  -- `v`'s tick to the action time of round `r`
  have hk₀ := P.hk₀
  have hk₀T := (E.tick_active _ _ _ hk₀).2.2
  have hk₀A := (E.tick_active _ _ _ hk₀).1
  -- the proposal's parent extends every line source of a slot at least two slots before `s`
  have hPar := P.parent_extends_sources M F R E hNet hSkew hRedeliver Sy hΔs U Fx
    (show r * S.C.R + S.C.k + 2 ≤ s by omega) (hEndM _ (by omega)) hp hB
  -- C1 and C3 (gaps, called under): the members save `B`
  have hBase := (round_base_after_fast_block_opening M F U Fx) S A x R GST tGAT tAwakeEnd r H₂ s v L B
    E hNet hSkew hRedeliver Sy hΔs ((GoldilocksCorrectness.Record.Statements.Executions.RootsNameBlocksUntil.mono M)
      (hEndM _ hs2) hRoots) hParent hGST hThird hAwake hActive hCommittees hAnchor hOld hv hL n' sent hUpdate hFast
    hs hsR (hEndA _ hs2) hp hB hNoCol
  obtain ⟨μA, hμA, hAsrc⟩ := P.anchor_source M F R E hNet hSkew hRedeliver Sy hΔs U Fx
    (show r * S.C.R + S.C.k + 2 ≤ s by omega) (hEndM _ (by omega)) hp
  have hGs2 : ∀ σ', σ' ≤ s - 2 → LineInv M S A x r H₂ σ' := fun σ' h => hG σ' (by omega)
  have hPrev := P.votes_source M F R E hNet hSkew hRedeliver Sy hΔs U Fx hGs2 (show r * S.C.R ≤ s - 2 by omega)
    (hEndM _ (by omega)) hAsrc (by omega)
  rw [show s - 2 + 1 = s - 1 by omega] at hPrev
  obtain ⟨-, hSaved, -, -⟩ := (healed_round_base_of_prev_votes M F U Fx) S A x R GST tGAT tAwakeEnd s B E hNet hSkew
    hRedeliver Sy hΔs ((GoldilocksCorrectness.Record.Statements.Executions.RootsNameBlocksUntil.mono M)
      (hEndM _ (by omega)) hRoots) hParent hGST hThird hAwake hActive hCommittees (by omega)
    (le_trans hAnchor ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (by omega)))
    (le_trans hAnchor ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (by omega)))
    (hEndA _ hs2) hp hB hBase hNoCol (fun u hu vote hvote => hPrev u (Finset.mem_inter.1 hu).2 vote hvote)
  -- a member of a slot is outside the adversary set at its support cutoff
  have hmem : ∀ σ : ℕ, ∀ w ∈ Hon M S A x σ, w ∉ A.corruptedAtTime x (M.supportCutoff S.C (σ + 1)) := by
    intro σ w hw
    unfold Hon roundMembers at hw
    exact (Finset.mem_sdiff.1 hw).2
  have hnon : ∀ σ : ℕ, r * S.C.R ≤ σ → σ + 1 ≤ s'' → ∃ u, u ∈ Hon M S A x σ := by
    intro σ hσ' hσs
    have h := P.committee M F hσ' (hEndM _ hσs)
    obtain ⟨u, hu⟩ : (S.P.committee σ ∩ Hon M S A x σ).Nonempty := Finset.card_pos.1 (by omega)
    exact ⟨u, (Finset.mem_inter.1 hu).2⟩
  -- `B` is a line source of slot `s`
  obtain ⟨u₀, hu₀⟩ := hnon s hσ (by omega)
  have hu₀U := ((P.members_sets M F U hσ (hEndM _ (by omega))).2) hu₀
  have hBsrc : LineSource M S A x r H₂ s B :=
    P.source_conf M F R E U (by omega) hu₀ (hEndM _ (by omega)) (hSaved u₀ hu₀U) (ancestorEq_refl B)
  -- the sources whose round's action time an honest validator ticked to before a step at a real time less than the
  -- support cutoff of slot `s` (resp. `s + 1`) plus one delay
  have hslot : ∀ (r' : ℕ) (k j : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u (aR M S r') → k < j →
      x.time j ≤ ((c : ℕ) : ℝ) + ΔClockBehind →
      M.supportCutoff S.C (r' * S.C.R + 1) < c + Δ S := by
    intro r' k j u c hk hkj hj
    have h1 := (E.tick_active _ _ _ hk).2.1
    have h2 := (time_mono M) x R hkj.le
    have haR' : aR M S r' = M.supportCutoff S.C (r' * S.C.R + 1) := rfl
    rw [haR'] at h1
    have h3 : ((M.supportCutoff S.C (r' * S.C.R + 1) : ℕ) : ℝ) < ((c + Δ S : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast h3
  refine ⟨fun w hw => ?_, fun w hw => ?_, fun s' hs1 hs2' w hw => ?_,
    fun s' hs1 hs2' σ hσ1 hσ2 u hu C hC w hw => ?_, ?_⟩
  · -- clause 1: `w`'s tick to the vote time of slot `s` (`root_source_st`, `floor_le_of_sources_st`)
    have hwc : w ∉ A.corruptedAtTime x (M.supportCutoff S.C s) :=
      (not_mem_corruptedAtTime_of_le M) x R E (hcm _ _ (Nat.le_succ s)) (hmem s w hw)
    obtain ⟨k, hk, -⟩ := P.tick_before M F (w := w) (c := M.voteTime S.C s) (t := M.supportCutoff S.C s)
      (by omega) (by omega) (hEndM _ (by omega)) hwc
    have hti : x.tickInput w (M.voteTime S.C s) = x.st k w := by
      unfold Trace.tickInput
      rw [(tickStep_eq_of_lbl M) x E hk]
    rw [hti]
    have hkT := (E.tick_active _ _ _ hk).2.2
    have hkA := (E.tick_active _ _ _ hk).2.1
    have hw' : w ∉ A.corrupted k := E.not_mem_corrupted_of_tick hk
    have hgap : ((aR M S r : ℕ) : ℝ) + Δ S ≤ ((M.voteTime S.C s : ℕ) : ℝ) := by
      exact_mod_cast (show aR M S r + Δ S ≤ M.voteTime S.C s by omega)
    have hk₀k : x.tickStep v (aR M S r) < k := (lt_of_time_lt M) x R (by linarith)
    have hjt : x.time k < ((M.supportCutoff S.C (s + 2) : ℕ) : ℝ) - ΔClockAhead := by
      have : ((M.voteTime S.C s : ℕ) : ℝ) + 2 * Δ S ≤ ((M.supportCutoff S.C (s + 2) : ℕ) : ℝ) := by
        exact_mod_cast (show M.voteTime S.C s + 2 * Δ S ≤ M.supportCutoff S.C (s + 2) by omega)
      linarith
    have hQ : ∀ (r' : ℕ) (Eb : Block V), r ≤ r' →
        (∃ (u : V) (k' : ℕ), x.lbl k' = Event.tick u (aR M S r') ∧ k' < k ∧ u ∈ A.active k') →
        LineSource M S A x r H₂ (r' * S.C.R) Eb → Eb.AncestorEq B.parent := by
      rintro r' Eb - ⟨u, k', hk', hk'k, -⟩ hE
      have h := hslot r' k' k u (M.voteTime S.C s) hk' hk'k hkT
      refine hPar _ Eb hE ?_
      by_contra hn
      have := hcm s (r' * S.C.R + 1) (by omega)
      omega
    have ht0 : ∃ (u : V) (k' : ℕ), x.lbl k' = Event.tick u (aR M S r) ∧ k' < k ∧ u ∈ A.active k' :=
      ⟨v, _, hk₀, hk₀k, hk₀A⟩
    obtain ⟨r', hrr, htk, hsrc⟩ := P.root_source_st M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hσ (hEndM _ hs2)
      ht0 hjt hw'
    exact ⟨hQ r' _ hrr htk hsrc,
      P.floor_le_of_sources_st M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG (hEndM _ hs2) ht0 hjt hw' hQ⟩
  · -- clause 2: `w`'s tick to the support cutoff of slot `s + 1` (an updater of slot `s`)
    have hwU := ((P.members_sets M F U hσ (hEndM _ (by omega))).2) hw
    obtain ⟨k, hk, -⟩ := Activity.mem_activeThroughoutToTick.1 hwU
    have hti : x.tickInput w (M.supportCutoff S.C (s + 1)) = x.st k w := by
      unfold Trace.tickInput
      rw [(tickStep_eq_of_lbl M) x E hk]
    rw [hti]
    have hkT := (E.tick_active _ _ _ hk).2.2
    have hkA := (E.tick_active _ _ _ hk).2.1
    have hw' : w ∉ A.corrupted k := E.not_mem_corrupted_of_tick hk
    have hgap : ((aR M S r : ℕ) : ℝ) + Δ S ≤ ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) := by
      exact_mod_cast (show aR M S r + Δ S ≤ M.supportCutoff S.C (s + 1) by omega)
    have hk₀k : x.tickStep v (aR M S r) < k := (lt_of_time_lt M) x R (by linarith)
    have hjt : x.time k < ((M.supportCutoff S.C (s + 2) : ℕ) : ℝ) - ΔClockAhead := by
      have : ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + 2 * Δ S ≤ ((M.supportCutoff S.C (s + 2) : ℕ) : ℝ) := by
        exact_mod_cast (show M.supportCutoff S.C (s + 1) + 2 * Δ S ≤ M.supportCutoff S.C (s + 2) by omega)
      linarith
    have hPB : B.parent.AncestorEq B := by
      obtain ⟨s₀, rfl⟩ : ∃ s₀, s = s₀ + 1 := ⟨s - 1, by omega⟩
      obtain ⟨i, hl, hsent⟩ := hB
      obtain ⟨-, -, hBpar?, -⟩ := (proposal_parent_walk_end M F U) S A x R E s₀ i B _ hl hsent
      exact ancestorEq_of_parent? hBpar?
    have hQ : ∀ (r' : ℕ) (Eb : Block V), r ≤ r' →
        (∃ (u : V) (k' : ℕ), x.lbl k' = Event.tick u (aR M S r') ∧ k' < k ∧ u ∈ A.active k') →
        LineSource M S A x r H₂ (r' * S.C.R) Eb → Eb.AncestorEq B := by
      rintro r' Eb - ⟨u, k', hk', hk'k, -⟩ hE
      have h := hslot r' k' k u (M.supportCutoff S.C (s + 1)) hk' hk'k hkT
      rcases Nat.lt_or_ge (M.supportCutoff S.C (r' * S.C.R + 1)) (M.supportCutoff S.C (s + 1)) with hlt | hge
      · exact ancestorEq_trans (hPar _ Eb hE
          ((GoldilocksCorrectness.Record.Proofs.Routines.round_slot_le_of_lt M.toSlotLayout F.sched) S hsR hlt)) hPB
      · -- a source of slot `s` itself: below the confirmation `B` that every updater of slot `s` saved
        have hrs : r' * S.C.R = s := by
          rcases Nat.lt_or_ge s (r' * S.C.R) with h1 | h1
          · have := hcm (s + 2) (r' * S.C.R + 1) (by omega)
            have hΔR' : ((M.supportCutoff S.C (s + 2) : ℕ) : ℝ) ≤ ((M.supportCutoff S.C (r' * S.C.R + 1) : ℕ) : ℝ) := by
              exact_mod_cast this
            omega
          · rcases Nat.lt_or_ge (r' * S.C.R) s with h2 | h2
            · have := hcm (r' * S.C.R + 2) (s + 1) (by omega)
              have h4 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_succ_eq M.toSlotLayout F.sched U) S
                (r' * S.C.R + 1)
              rw [show r' * S.C.R + 1 + 1 = r' * S.C.R + 2 from rfl] at h4
              omega
            · omega
        rw [hrs] at hE
        obtain ⟨u', hu', n₀, C₀, X₀, -, -, hC₀, hEX₀, hX₀C₀, -⟩ := hE
        have hCB : some C₀ = some B := hC₀.symm.trans (by exact hSaved u' hu')
        cases hCB
        exact ancestorEq_trans hEX₀ hX₀C₀
    have ht0 : ∃ (u : V) (k' : ℕ), x.lbl k' = Event.tick u (aR M S r) ∧ k' < k ∧ u ∈ A.active k' :=
      ⟨v, _, hk₀, hk₀k, hk₀A⟩
    obtain ⟨r', hrr, htk, hsrc⟩ := P.root_source_st M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG hσ (hEndM _ hs2)
      ht0 hjt hw'
    exact ⟨hQ r' _ hrr htk hsrc,
      P.floor_le_of_sources_st M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG (hEndM _ hs2) ht0 hjt hw' hQ⟩
  · -- clause 3: the members' frames follow `B` (`stepFrame_source_past`, the rows `TR`)
    have hGs' := P.lineInv_upto M F R E hNet hSkew hRedeliver Sy hΔs U Fx (hEndM _ hs2')
    exact P.stepFrame_source_past M F R E hNet hSkew hRedeliver Sy hΔs U Fx TR hGs' (by omega) (hEndM _ hs2')
      (hEndM _ hs2') (hmem (s' + 1) w hw) hBsrc hs1
      (P.votes_source M F R E hNet hSkew hRedeliver Sy hΔs U Fx hGs' (by omega) (hEndM _ hs2') hBsrc hs1)
  · -- clause 4: the members' frames follow every confirmation a member saved from slot `s − 1` on
    have hGs' := P.lineInv_upto M F R E hNet hSkew hRedeliver Sy hΔs U Fx (hEndM _ hs2')
    have hCsrc : LineSource M S A x r H₂ σ C :=
      P.source_conf M F R E U (by omega) hu (hEndM _ (by omega)) hC (ancestorEq_refl C)
    exact P.stepFrame_source_past M F R E hNet hSkew hRedeliver Sy hΔs U Fx TR hGs' (by omega) (hEndM _ hs2')
      (hEndM _ hs2') (hmem (s' + 1) w hw) hCsrc hσ2
      (P.votes_source M F R E hNet hSkew hRedeliver Sy hΔs U Fx hGs' (by omega) (hEndM _ hs2') hCsrc hσ2)
  · -- clause 5: the next proposer's root at its tick to the start of slot `s''`
    obtain ⟨σ₂, rfl⟩ : ∃ σ₂, s'' = σ₂ + 2 := ⟨s'' - 2, by omega⟩
    set q := S.P.proposer (σ₂ + 2) with hqdef
    have hG₂ : ∀ σ', σ' ≤ σ₂ → LineInv M S A x r H₂ σ' :=
      P.lineInv_upto M F R E hNet hSkew hRedeliver Sy hΔs U Fx le_rfl
    obtain ⟨-, hcq, -, hsq, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ₂ + 2)
    obtain ⟨hvq1, hcq1, -, hsq1, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ₂ + 1)
    rw [show σ₂ + 1 + 1 = σ₂ + 2 from rfl] at hsq1
    have hvq := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_mono M.toSlotLayout F.sched) S
      (show r * S.C.R ≤ σ₂ + 2 by omega)
    obtain ⟨hvqq, -, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (σ₂ + 2)
    have hmx := le_max_left (Δ S) Δs
    -- the proposer ticks to the start of slot `s''`
    obtain ⟨kp, hkp, -⟩ := P.tick_before M F (w := q) (c := M.slotStart S.C (σ₂ + 2))
      (t := M.supportCutoff S.C (σ₂ + 2)) (by omega) (by omega) le_rfl hq
    have hti : x.tickInput q (M.slotStart S.C (σ₂ + 2)) = x.st kp q := by
      unfold Trace.tickInput
      rw [(tickStep_eq_of_lbl M) x E hkp]
    rw [hti]
    have hkpT := (E.tick_active kp _ _ hkp).2.2
    have hkpA := (E.tick_active kp _ _ hkp).2.1
    have hpk : q ∉ A.corrupted kp := E.not_mem_corrupted_of_tick hkp
    have hcR : ((M.supportCutoff S.C (σ₂ + 2) : ℕ) : ℝ) = ((M.slotStart S.C (σ₂ + 2) : ℕ) : ℝ) + 2 * Δ S := by
      rw [hcq]; push_cast; ring
    have hgap : ((aR M S r : ℕ) : ℝ) + Δ S ≤ ((M.slotStart S.C (σ₂ + 2) : ℕ) : ℝ) := by
      have := hcm (r * S.C.R + 1) (σ₂ + 1) (by omega)
      exact_mod_cast (show aR M S r + Δ S ≤ M.slotStart S.C (σ₂ + 2) by omega)
    have hk₀k : x.tickStep v (aR M S r) < kp := (lt_of_time_lt M) x R (by linarith)
    have hjt : x.time kp < ((M.supportCutoff S.C (σ₂ + 2) : ℕ) : ℝ) - ΔClockAhead := by rw [hcR]; linarith
    obtain ⟨r', -, ⟨u', k', hk', hk'j, -, hu'c, C₀, hsv, hRC₀⟩, hsrc⟩ := P.root_source_st_attester M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG₂
      (show r * S.C.R ≤ σ₂ by omega) le_rfl hk₀k hjt hpk
    have hr' : r' * S.C.R ≤ σ₂ := by
      have h := hslot r' k' kp u' (M.slotStart S.C (σ₂ + 2)) hk' hk'j hkpT
      by_contra hn
      have := hcm (σ₂ + 2) (r' * S.C.R + 1) (by omega)
      omega
    -- `q` is a member of slot `σ₂`
    have hqc : q ∉ A.corruptedAtTime x (M.supportCutoff S.C (σ₂ + 1)) :=
      (not_mem_corruptedAtTime_of_le M) x R E (hcm _ _ (Nat.le_succ _)) hq
    have hqH : q ∈ Hon M S A x σ₂ := by
      unfold Hon roundMembers
      exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hqc⟩
    have hqU := ((P.members_sets M F U (show r * S.C.R ≤ σ₂ by omega) (hcm _ _ (Nat.le_succ _))).2) hqH
    -- the witness, by the source's slot (, `dev`'s route): a member's confirmation with the line invariant at slot
    -- `σ₂` when the source is of an earlier slot; the source's own updater and its confirmation when it is of slot `σ₂`
    obtain ⟨C, uC, hCH, hC, hRC⟩ : ∃ (C : Block V) (uC : V), uC ∈ Hon M S A x σ₂ ∧
        (x.tickOutput uC (M.supportCutoff S.C (σ₂ + 1))).savedConfirmation σ₂ = some C ∧
        (M.get_fc_root (x.st kp q)).AncestorEq C := by
      rcases Nat.lt_or_eq_of_le hr' with hlt | heq
      · obtain ⟨C, hC⟩ := P.member_saves_confirmation M F R E hNet hSkew hRedeliver Sy hΔs U Fx
          (show r * S.C.R + 1 ≤ σ₂ by omega) le_rfl hqH
        exact ⟨C, q, hqH, hC, (hG₂ σ₂ le_rfl _ _ hsrc (by omega)).2 q hqU C hC⟩
      · refine ⟨C₀, u', ?_, ?_, hRC₀⟩
        · have hu'σ : u' ∉ A.corruptedAtTime x (M.supportCutoff S.C (σ₂ + 1)) := by
            rw [← heq]; exact hu'c
          unfold Hon roundMembers
          exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hu'σ⟩
        · rw [← heq]; exact hsv
    have hCsrc : LineSource M S A x r H₂ σ₂ C :=
      P.source_conf M F R E U (by omega) hCH (hcm _ _ (Nat.le_succ _)) hC (ancestorEq_refl C)
    have hj0 : ((M.voteTime S.C (σ₂ + 1) : ℕ) : ℝ) ≤ x.time kp := by
      have : ((M.voteTime S.C (σ₂ + 1) : ℕ) : ℝ) + Δ S ≤ ((M.slotStart S.C (σ₂ + 2) : ℕ) : ℝ) := by
        exact_mod_cast (show M.voteTime S.C (σ₂ + 1) + Δ S ≤ M.slotStart S.C (σ₂ + 2) by omega)
      linarith
    have hjc : x.time kp < ((M.supportCutoff S.C (σ₂ + 2) : ℕ) : ℝ) := by linarith
    obtain ⟨W, hW, hWv, hCW⟩ := P.frame_source_st M F R E hNet hSkew hRedeliver Sy hΔs U Fx hG₂
      (show r * S.C.R ≤ σ₂ by omega) le_rfl hj0 hjc hpk hCsrc le_rfl hRC
    rw [← (GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F)] at hRC
    exact ⟨C, ⟨uC, hCH, hC⟩, hRC, W, hW, hWv, hCW⟩

end GoldilocksCorrectness.Record.Proofs.Executions

