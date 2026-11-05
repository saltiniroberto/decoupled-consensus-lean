module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma94
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89rTargets
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.HeightAttestationStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Proofs.Executions.Lemma94
public import GoldilocksCorrectness.Proofs.Executions.Lemma89rTargets
public import GoldilocksCorrectness.Statements.Executions.HeightAttestationStatements
public import GoldilocksCorrectness.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89FastFamily
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma107, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma107.lean`, over a model `M` whose
facts `F` hold, for an execution `x` of `protocolOf M S`: Lemma 107, the honest attestations up to
the next round's action time are at most the opening height, and its kit on a certificate on the
chain of a held block, namely an honest member's attestation on the wire and the heights of a
justification and a finality certificate. The page's routine-level theorems are the facts' fields or
have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff)
open GoldilocksCorrectness.Proofs.Routines (slot_after_healed_round slot_lt_of_supportCutoff_le
  supportCutoff_mono)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax IsEntry VoterTreeAt JustifiedInTree AnchorAt)

open GoldilocksCorrectness.Record.Statements.Routines (FinalityCertOn JustificationCertOn)

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

/-! ## A certificate on a held chain has an honest member's attestation on the wire -/

/-- **Kit theorem, the honest member of a certificate on a held chain.** Under unforgeability, take
a block `D` that `w` holds after `j` steps, and a quorum `A` of validators each with an attestation
included on `D`'s chain whose content satisfies `P`; when fewer than a quorum of validators have
been in the adversary set up to the time after `j` steps, some member `u` of `A`'s tick put on the
wire, at a step `j' < j` at a clock value `t'` at most `x[j].time + ΔClockAhead` (its tick's
step is at a real time at least `t' − ΔClockAhead`), awake and honest then, a well-formed
attestation of its own whose content satisfies `P`.

Why: some member of `A` was never in the adversary set up to the time after `j` steps; its
attestation included on `D`'s chain is in its own record (Lemma 74), and every content of a record
was sent by the validator's own tick at an earlier step (`record_content_sent_step`).

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `j`: the step; `w`: the holder; `D`:
  the held block; `A`: the quorum; `P`: the condition on the contents.

Read aloud: a quorum of attestations on the chain of a held block has a member that put an
attestation with the same content on the wire, awake and honest, at an earlier step. -/
theorem cert_member_sent_before (S : Setup V) (Act : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy Act x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (j : ℕ) (w : V) (D : Block V) (A : Finset V)
    (P : AttestationContent → Prop) (tH : ℕ) (htH : x.time j ≤ tH)
    (hAdvQ : Act.AdversaryFewerThanQuorumUntil x (quorum V) tH)
    (hD : D ∈ (x.st j w).tree)
    (hqA : quorum V ≤ |A|)
    (hA : ∀ v ∈ A, ∃ a : Attestation V, a.val_index = v ∧ P a.content ∧ M.on_chain a D = true) :
    ∃ (j' t' : ℕ) (u : V) (a' : Attestation V), j' < j ∧
      x.lbl j' = Event.tick u t' ∧ (t' : ℝ) ≤ x.time j + ΔClockAhead ∧
      u ∈ Act.active j' ∧
      (⟨u, NamedObject.attest a'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (j' + 1) - x.sent j' ∧
      P a'.content ∧ M.attestation_well_formed a' = true ∧ u ∉ Act.corruptedAtTime x tH := by
  obtain ⟨u, hu, hhonM⟩ : ∃ u ∈ A, Act.HonestThroughTime x tH u := by
    by_contra hno
    have hall : ∀ v ∈ A, ∃ i : ℕ, x.time i ≤ tH ∧ v ∈ Act.corrupted i := by
      intro v hv
      by_contra hn
      exact hno ⟨v, hv, fun i hi ha => hn ⟨i, hi, ha⟩⟩
    have h3 := hAdvQ A hall
    omega
  have hhon : x.HonestThrough Act j u :=
    fun i'' hi'' => hhonM i'' (le_trans ((time_mono M) x R hi'') htH)
  obtain ⟨a, hau, hP, hon⟩ := hA u hu
  have hrec := (lem74_honest_attestations_recorded M F) S Act x R E j w D a hD hon
    (by rw [hau]; exact hhon)
  rw [hau] at hrec
  obtain ⟨j', t', a', hj', hl, hActRC, hsent, -, hcont, hwf⟩ :=
    (record_content_sent_step M F) S Act x R E u j _ hrec
  have htj : (t' : ℝ) ≤ x.time j + ΔClockAhead := by
    have h1 := ((time_of_lbl_tick M) x R E hl).1.1
    have h2 := (time_mono M) x R hj'.le
    linarith
  exact ⟨j', t', u, a', hj', hl, htj, hActRC, hsent, by rw [hcont]; exact hP, hwf,
    Activity.not_mem_corruptedAtTime.2 fun i hi => hhonM i hi⟩

/-- **Kit theorem, a justification certificate on a held chain is at most the bound of the old
attestations.** When every attestation an honest awake validator put on the wire at a tick before
`t₀` has height at most `H`, fewer than a quorum of validators have been in the adversary set up to
the time after `j` steps, and that time, and that time plus `ΔClockAhead` (the most a validator's
clock runs ahead of real time), are less than `t₀`, a justification certificate on the chain
of a block `w` holds after `j` steps is at a height at most `H`.

Why: its honest member's attestation at that height was sent at a time at most the time after `j`
steps (`cert_member_sent_before`).

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t₀`: the time before which the
  attestations are read; `H`: the bound; `j`: the step; `w`: the holder; `D`: the held block;
  `h`: the certificate's height; `T`: the block it names.

Read aloud: when every honest attestation sent before `t₀` has height at most `H`, a justification
certificate on the chain of a block held before `t₀` is at a height at most `H`. -/
theorem justification_cert_height_le (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (t₀ H j : ℕ) (w : V) (D T : Block V) (h : Height)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) t₀)
    (hOld : OldAttestationsAtMostHonestAt M S A x t₀ t₀ H)
    (hj : x.time j < t₀) (hjA : x.time j + ΔClockAhead < t₀)
    (hD : D ∈ (x.st j w).tree)
    (hJ : JustificationCertOn M D h T) :
    h ≤ H := by
  obtain ⟨X₁, hX₁D, Q, hqA, hQ⟩ := hJ
  rw [GoldilocksCorrectness.Record.quorumAt_eq_quorum Fx F.sched X₁] at hqA
  obtain ⟨j', t', u, a', -, hl, ht', hAct, hsent, hP, -, huH⟩ :=
    (cert_member_sent_before M F) S A x R E j w D Q (fun c => c.h = h) t₀ (le_of_lt hj) hAdvQ hD hqA
      (fun v hv => by
        obtain ⟨a, h1, h2, -, -, h5⟩ := hQ v hv
        exact ⟨a, h1, h2, (GoldilocksCorrectness.Record.Proofs.Routines.on_chain_mono M F) a hX₁D h5⟩)
  have hle := hOld j' t' u a' hl (lt_of_le_of_lt ht' hjA) huH hsent
  have hP' : a'.h = h := hP
  rw [hP'] at hle
  exact hle

/-- **Kit theorem, a finality certificate on a held chain is less than the bound of the old
attestations.** Under the hypotheses of `justification_cert_height_le`, a finality certificate on
the chain of a block `w` holds after `j` steps is at a height less than `H`.

Why: its honest member's attestation carries the finality pair at that height and is well formed,
so its own height is greater; it was sent at a time at most the time after `j` steps
(`cert_member_sent_before`).

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t₀`: the time before which the
  attestations are read; `H`: the bound; `j`: the step; `w`: the holder; `D`: the held block;
  `h`: the certificate's height; `T`: the block it names.

Read aloud: when every honest attestation sent before `t₀` has height at most `H`, a finality
certificate on the chain of a block held before `t₀` is at a height less than `H`. -/
theorem finality_cert_height_lt (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (t₀ H j : ℕ) (w : V) (D T : Block V) (h : Height)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) t₀)
    (hOld : OldAttestationsAtMostHonestAt M S A x t₀ t₀ H)
    (hj : x.time j < t₀) (hjA : x.time j + ΔClockAhead < t₀)
    (hD : D ∈ (x.st j w).tree)
    (hF : FinalityCertOn M D h T) :
    h < H := by
  obtain ⟨X₁, hX₁D, Q, hqA, hQ⟩ := hF
  rw [GoldilocksCorrectness.Record.quorumAt_eq_quorum Fx F.sched X₁] at hqA
  obtain ⟨j', t', u, a', -, hl, ht', hAct, hsent, hP, hwf, huH⟩ :=
    (cert_member_sent_before M F) S A x R E j w D Q
      (fun c => c.finality_pair = some ⟨h, T.root⟩) t₀ (le_of_lt hj) hAdvQ hD hqA
      (fun v hv => by
        obtain ⟨a, h1, h2, h3⟩ := hQ v hv
        exact ⟨a, h1, h2, (GoldilocksCorrectness.Record.Proofs.Routines.on_chain_mono M F) a hX₁D h3⟩)
  have hle := hOld j' t' u a' hl (lt_of_le_of_lt ht' hjA) huH hsent
  have hP' : a'.finality_pair = some ⟨h, T.root⟩ := hP
  have hlt := ((F.rd.attestation_well_formed_iff a').1 hwf).2 _ hP'
  exact lt_of_lt_of_le hlt hle

/-! ## Lemma 107 -/

/-- **Lemma 107, the honest attestations up to the next round's action time are at most the
opening proposal's height.** The proof; the audited statement is in
`Statements/Executions/FinalityLivenessStatements.lean`.

Why: an attestation sent before the support cutoff of slot `s₀ + 1` has height at most
`H < h(B)` (`hOld`, and the frame of `round_member_frame_after_healing` with the proposer as the
member, `opener_mem_honestActiveAt`). From then on, Lemma 82 sends it at the support cutoff of a
slot `s_a + 1` and names an entry `E` of the honest chain at slot `s_a` at its height; the time is
the action time of a round (`attest_time_round`), so `s_a` is a round's first slot, less than
`(r + 1) R`, hence at most `s`. At a slot before `s`, `E` is `B` or an ancestor of `B` (the frame's
first conjunct); at `s`, `E` is an ancestor of an updater's confirmation of `s`, which is `B` (its
third conjunct). Then `h(E) ≤ h(B)` (Lemma 47 (d)).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₂`: the hand-over step; `H`: the threshold;
- `r`: the round; `s`: its first slot; `B`: the proposal.

Read aloud: up to the next round's attestations, no honest validator has attested at a height
greater than the proposal of an honest round opening slot. -/
theorem lem107_honest_attestations_at_most_opening_height (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ anchor i₂ H r s : ℕ) (B : Block V)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRootsU : ∀ v ∈ updaterAt M S A x s, RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C (s + 1)))))
    (hParent : ParentHeldAtDelivery M x)
    (hAdvQU : ∀ v ∈ updaterAt M S A x s, A.AdversaryFewerThanQuorumUntil x (quorum V) (x.time (x.tickStep v (M.supportCutoff S.C (s + 1)))))
    (hSleepK : CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C (s + 1))) (hAnchor : anchor ≤ x.time i₂)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀) (ht₀ : M.supportCutoff S.C (s₀ + 1) ≤ x.time i₂)
    (hChain : ConfirmationsChainBefore M S A x s₀ s)
    (hInv : ∀ s' : ℕ, s₀ < s' → s' ≤ s →
      ChainInvFor M S A x (honestActiveAt M S A x s')
        (OnHonestChainBefore M S A x s₀ s') s')
    (hLocks : ∀ s' : ℕ, s₀ < s' → s' ≤ s → ∀ w ∈ honestActiveAt M S A x s',
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ s') s' w)
    (hLocks₀ : ∀ w ∈ honestActiveAt M S A x s₀,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (s₀ + 1)) s₀ w)
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hCachesU : ∀ v ∈ updaterAt M S A x s, ∀ (j : ℕ) (w : V), x.time i₂ ≤ x.time j →
      x.time j ≤ x.time (x.tickStep v (M.supportCutoff S.C (s + 1))) → w ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j w))
    (hs : s = r * S.C.R) (hAfter : x.time i₂ < M.slotStart S.C s ∧
      ∀ k : ℕ, x.lbl k = Event.tick (S.P.proposer s) (M.slotStart S.C s) → x.time i₂ < x.time k)
    (hOpener : HonestOpenerAt M S A x s)
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick (S.P.proposer s) (M.slotStart S.C s) ∧
      (⟨S.P.proposer s, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i)
    (hNoCollision : ¬ RootCollisionAtProposal M S A x s B)
    (hHold : ∀ s' : ℕ, s - 1 ≤ s' → s' ≤ s → ∀ u ∈ honestActiveAt M S A x s', u ∈ S.P.committee s' →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hHoldP : S.P.proposer s ∈ A.activeThroughout x ((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs)) :
    OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C ((r + 1) * S.C.R + 1)) (M.supportCutoff S.C ((r + 1) * S.C.R + 1))
      (M.chainStateOf S.C B).h := by
  obtain ⟨hs2, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.slot_after_healed_round M.toSlotLayout F.sched) S
    s₀ s (by exact_mod_cast lt_of_le_of_lt ht₀ hAfter.1)
  obtain ⟨hChainB, -, hSavedAll, hHB⟩ :=
    (round_chain_frame_after_healing M F U Fx) S A x R GST s₀ anchor i₂ H s B E hNet hSkew hRedeliver Sy hΔs
      hRootsU hParent hAdvQU hSleepK hAnchor hGST ht₀ hChain hInv hLocks hLocks₀ hOld hCachesU
      hAfter hOpener hPropose hNoCollision hHold hHoldP
  have hΔ := GoldilocksCorrectness.Proofs.Routines.one_le_Δ S
  have hR := S.C.R_ge_two
  have hB0 := E.behind_nonneg
  have hcR : ∀ s' : ℕ, ((M.supportCutoff S.C s' : ℕ) : ℝ) = 4 * (Δ S : ℝ) * (s' : ℝ) + 2 * Δ S := fun s' => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s',
      (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s',
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s']; push_cast; ring
  have hcut : M.supportCutoff S.C (s₀ + 1) ≤ M.supportCutoff S.C ((r + 1) * S.C.R + 1) :=
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
      (by rw [Nat.succ_mul]; omega)
  -- a validator outside the adversary set at a time is outside it at every earlier time
  have hmono : ∀ (v : V) (t₁ t₂ : ℝ), t₁ ≤ t₂ → v ∉ A.corruptedAtTime x t₂ → v ∉ A.corruptedAtTime x t₁ := by
    intro v t₁ t₂ h12 h
    rw [Activity.not_mem_corruptedAtTime] at h ⊢
    intro i hi hc
    exact h i (le_trans hi h12) hc
  intro i t v a hl ht hHonR hSent
  rcases Nat.lt_or_ge t (M.supportCutoff S.C (s₀ + 1)) with hlt | hge
  · exact le_trans (hOld i t v a hl (by exact_mod_cast hlt)
      (hmono v _ _ (by exact_mod_cast hcut) hHonR) hSent) (Nat.le_of_lt hHB)
  -- the attestation's tick is at a round's action time `aR r'`, with `r' ≤ r`
  obtain ⟨r', hr'⟩ := (attest_time_round M F U) S A x R E hl hSent
  unfold aR at hr'
  have htN : t < M.supportCutoff S.C ((r + 1) * S.C.R + 1) := by exact_mod_cast ht
  have hr'r : r' ≤ r := by
    by_contra hn
    have := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
      (show (r + 1) * S.C.R + 1 ≤ r' * S.C.R + 1 from by
        have := Nat.mul_le_mul_right S.C.R (show r + 1 ≤ r' by omega); omega)
    omega
  -- the tick is at a real time before the read time of the bound: `v` is outside the adversary set there
  have hmul : r' * S.C.R ≤ r * S.C.R := Nat.mul_le_mul_right _ hr'r
  have hc2 : M.supportCutoff S.C (r' * S.C.R + 1 + 1) ≤ M.supportCutoff S.C ((r + 1) * S.C.R + 1) :=
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
      (by rw [Nat.succ_mul]; omega)
  have hti : x.time i ≤ ((M.supportCutoff S.C ((r + 1) * S.C.R + 1) : ℕ) : ℝ) := by
    have h1 := (E.tick_active i v t hl).2.2
    have h2 : ((M.supportCutoff S.C (r' * S.C.R + 1 + 1) : ℕ) : ℝ) ≤
        ((M.supportCutoff S.C ((r + 1) * S.C.R + 1) : ℕ) : ℝ) := by exact_mod_cast hc2
    have h3 := hcR (r' * S.C.R + 1 + 1)
    have h4 := hcR (r' * S.C.R + 1)
    have hΔR : (1 : ℝ) ≤ (Δ S : ℝ) := by exact_mod_cast hΔ
    have hSk := hSkew
    have hA0 := E.ahead_nonneg
    rw [hr'] at h1
    push_cast at h1 h2 h3 h4
    linarith
  -- from the healed round's update on, the attestation names an entry of the honest chain
  obtain ⟨s_a, Eb, -, hts, ⟨hs₀a, w, hw, C, hC, hEC⟩, -, hEh, -⟩ :=
    (lem82_honest_attestations_on_chain M F U) S A x R s₀ E i t v a hl hge (hmono v _ _ hti hHonR) hSent
  have hsa : s_a = r' * S.C.R := by
    have h1 : M.supportCutoff S.C (s_a + 1) = M.supportCutoff S.C (r' * S.C.R + 1) := by rw [← hts]; exact hr'
    have h2 := (GoldilocksCorrectness.Record.Proofs.Routines.slot_lt_of_supportCutoff_le M.toSlotLayout F.sched) S
      (le_of_eq h1)
    have h3 := (GoldilocksCorrectness.Record.Proofs.Routines.slot_lt_of_supportCutoff_le M.toSlotLayout F.sched) S
      (le_of_eq h1.symm)
    omega
  have hsa_le : s_a ≤ s := by rw [hsa, hs]; exact hmul
  -- `Eb` is `B` or an ancestor of `B`
  have hEB : Eb.AncestorEq B := by
    rcases Nat.lt_or_ge s_a s with hlt' | hge'
    · exact hChainB Eb ⟨s_a, hlt', hs₀a, w, hw, C, hC, hEC⟩
    · obtain rfl : s_a = s := le_antisymm hsa_le hge'
      rw [hSavedAll w hw] at hC
      obtain rfl := Option.some.inj hC
      exact hEC
  have := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C Eb B).2.2.2.1 hEB
  rw [hEh] at this
  exact this

end GoldilocksCorrectness.Record.Proofs.Executions

