module
public import GoldilocksCorrectness.Proofs.Executions.Lemma95
public import GoldilocksCorrectness.Proofs.Executions.Lemma89FastFamily

@[expose] public section

/-!
# Lemma 107: the honest attestations up to the next round's action time

The proof of Lemma 107, `lem107_honest_attestations_at_most_opening_height` (stated in
`GoldilocksCorrectness/Statements/Executions/FinalityLivenessStatements.lean`), and the kit
theorems on a certificate on the chain of a held block that Lemmas 94 and 95
(`Lemma94Pair.lean`, `Lemma95Pair.lean`) read:

- `cert_member_sent_before`: a quorum of attestations on the chain of a block a validator holds
  after `j` steps has a member never in the adversary set up to then, whose tick put an
  attestation with the same content on the wire, awake and honest then, at a step before `j`;
- `justification_cert_height_le` and `finality_cert_height_lt`: when every honest attestation sent
  before `t₀` has height at most `H` and the time after `j` steps is less than `t₀`, a
  justification certificate on the chain of a block held after `j` steps is at a height at most
  `H`, and a finality certificate at a height less than `H`.


-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff)
open GoldilocksCorrectness.Proofs.Routines (slot_after_healed_round slot_lt_of_supportCutoff_le
  supportCutoff_mono)

open GoldilocksCorrectness.Proofs.Routines (lem47_chain_state_heights)
open GoldilocksCorrectness.Statements.Routines (chainStateOf)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (JustificationCertOn FinalityCertOn)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

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
wire, at a step `j' < j` at a time `t' ≤ x[j].time`, awake and honest then, a well-formed
attestation of its own whose content satisfies `P`.

Why: some member of `A` was never in the adversary set up to the time after `j` steps; its
attestation included on `D`'s chain is in its own record (Lemma 74), and every content of a record
was sent by the validator's own tick at an earlier step (`record_content_sent_step`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `j`: the step; `w`: the holder; `D`:
  the held block; `A`: the quorum; `P`: the condition on the contents. -/
theorem cert_member_sent_before (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (j : ℕ) (w : V) (D : Block V) (A : Finset V)
    (P : AttestationContent → Prop)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : AdversaryFewerThanQuorumUntil Sched (quorum V) (x[j].time : Int))
    (hD : D ∈ (x[j][w].st).S.T)
    (hqA : quorum V ≤ |A|)
    (hA : ∀ v ∈ A, ∃ a : Attestation V, a.val_index = v ∧ P a.content ∧ on_chain a D = true) :
    ∃ (j' t' : ℕ) (u : V) (a' : Attestation V), j' < j ∧
      x.lbl j' = AtomicAction.tickAllAwake t' ∧ t' ≤ x[j].time ∧
      u ∈ Sched.awake (t' : Int) ∧ u ∉ Sched.adv (t' : Int) ∧
      (⟨u, NamedObject.attest a'⟩ : SignedMsg V (NamedObject V)) ∈ x[j' + 1].sent - x[j'].sent ∧
      P a'.content ∧ attestation_well_formed a' = true := by
  obtain ⟨u, hu, hhon⟩ : ∃ u ∈ A, HonestThrough x j u := by
    by_contra hno
    have hall : ∀ v ∈ A, ∃ t' : Int, t' ≤ (x[j].time : Int) ∧ v ∈ Sched.adv t' := by
      intro v hv
      by_contra hn
      exact hno ⟨v, hv, fun t' ht' ha => hn ⟨t', ht', ha⟩⟩
    have h3 := hAdvQ A hall
    omega
  obtain ⟨a, hau, hP, hon⟩ := hA u hu
  have hrec := lem74_honest_attestations_recorded S Sched x hU j w D a hD hon
    (by rw [hau]; exact hhon)
  rw [hau] at hrec
  obtain ⟨j', t', a', hj', hl, hAw, hHon, hsent, -, hcont, hwf⟩ :=
    record_content_sent_step S Sched x u j _ hrec
  have htj : t' ≤ x[j].time := by
    rw [← (time_of_lbl_tickAllAwake x hl).2]
    exact time_mono x hj'
  exact ⟨j', t', u, a', hj', hl, htj, hAw, hHon, hsent, by rw [hcont]; exact hP, hwf⟩

/-- **Kit theorem, a justification certificate on a held chain is at most the bound of the old
attestations.** When every attestation an honest awake validator put on the wire at a tick before
`t₀` has height at most `H`, fewer than a quorum of validators have been in the adversary set up to
the time after `j` steps, and that time is less than `t₀`, a justification certificate on the chain
of a block `w` holds after `j` steps is at a height at most `H`.

Why: its honest member's attestation at that height was sent at a time at most the time after `j`
steps (`cert_member_sent_before`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t₀`: the time before which the
  attestations are read; `H`: the bound; `j`: the step; `w`: the holder; `D`: the held block;
  `h`: the certificate's height; `T`: the block it names. -/
theorem justification_cert_height_le (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (t₀ H j : ℕ) (w : V) (D T : Block V) (h : Height)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : AdversaryFewerThanQuorumUntil Sched (quorum V) (x[j].time : Int))
    (hOld : OldAttestationsAtMost S Sched x t₀ H)
    (hj : x[j].time < t₀)
    (hD : D ∈ (x[j][w].st).S.T)
    (hJ : JustificationCertOn D h T) :
    h ≤ H := by
  obtain ⟨A, hqA, hA⟩ := hJ
  obtain ⟨j', t', u, a', -, hl, ht', hAw, hHon, hsent, hP, -⟩ :=
    cert_member_sent_before S Sched x j w D A (fun c => c.h = h) hU hAdvQ hD hqA
      (fun v hv => by
        obtain ⟨a, h1, h2, -, -, h5⟩ := hA v hv
        exact ⟨a, h1, h2, h5⟩)
  have hle := hOld j' t' u a' hl (lt_of_le_of_lt ht' hj) hAw hHon hsent
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
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t₀`: the time before which the
  attestations are read; `H`: the bound; `j`: the step; `w`: the holder; `D`: the held block;
  `h`: the certificate's height; `T`: the block it names. -/
theorem finality_cert_height_lt (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (t₀ H j : ℕ) (w : V) (D T : Block V) (h : Height)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : AdversaryFewerThanQuorumUntil Sched (quorum V) (x[j].time : Int))
    (hOld : OldAttestationsAtMost S Sched x t₀ H)
    (hj : x[j].time < t₀)
    (hD : D ∈ (x[j][w].st).S.T)
    (hF : FinalityCertOn D h T) :
    h < H := by
  obtain ⟨A, hqA, hA⟩ := hF
  obtain ⟨j', t', u, a', -, hl, ht', hAw, hHon, hsent, hP, hwf⟩ :=
    cert_member_sent_before S Sched x j w D A
      (fun c => c.finality_pair = some ⟨h, T.root⟩) hU hAdvQ hD hqA
      (fun v hv => by
        obtain ⟨a, h1, h2, h3⟩ := hA v hv
        exact ⟨a, h1, h2, h3⟩)
  have hle := hOld j' t' u a' hl (lt_of_le_of_lt ht' hj) hAw hHon hsent
  have hP' : a'.finality_pair = some ⟨h, T.root⟩ := hP
  have hlt := ((GoldilocksCorrectness.Proofs.Routines.attestation_well_formed_iff a').1 hwf).2 _ hP'
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
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₂`: the hand-over step; `H`: the threshold;
- `r`: the round; `s`: its first slot; `B`: the proposal. -/
theorem lem107_honest_attestations_at_most_opening_height (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ anchor i₂ H r s : ℕ) (B : Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s + 1)))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hSleepK : CommitteeSleepiness S Sched anchor) (hAnchor : anchor ≤ x[i₂].time)
    (hGST : GST ≤ voteTime S s₀) (ht₀ : supportCutoff S (s₀ + 1) ≤ x[i₂].time)
    (hChain : ConfirmationsChainBefore S Sched x s₀ s)
    (hInv : ∀ s' : ℕ, s₀ < s' → s' ≤ s →
      ChainInvFor S Sched x (honestActiveAt S Sched s') (OnHonestChainBefore S Sched x s₀ s') s')
    (hLocks : ∀ s' : ℕ, s₀ < s' → s' ≤ s → ∀ w ∈ honestActiveAt S Sched s',
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ s') s' w)
    (hLocks₀ : ∀ w ∈ honestActiveAt S Sched s₀,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ (s₀ + 1)) s₀ w)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (w : V), x[i₂].time ≤ x[j].time → x[j].time ≤ supportCutoff S (s + 1) →
      w ∉ Sched.adv (x[j].time : Int) → CachesOnChain S Sched x s₀ H (x[j][w].st))
    (hs : s = r * S.C.R) (hAfter : x[i₂].time < slotStart S s)
    (hOpener : HonestOpenerAt S Sched s)
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s) ∧
      (⟨S.P.proposer s, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent)
    (hNoCollision : ¬ RootCollisionAtProposal S Sched x s B) :
    OldAttestationsAtMost S Sched x (supportCutoff S ((r + 1) * S.C.R + 1))
      (chainStateOf S.C B).h := by
  obtain ⟨hs2, -, -⟩ := slot_after_healed_round S s₀ s (lt_of_le_of_lt ht₀ hAfter)
  obtain ⟨q, hq⟩ : ∃ q, s = q + 2 := ⟨s - 2, by omega⟩
  have hprop : S.P.proposer s ∈ honestActiveAt S Sched s := by
    subst hq
    exact opener_mem_honestActiveAt S Sched q hOpener
  obtain ⟨hChainB, -, hSavedAll, hHB, -⟩ :=
    round_member_frame_after_healing S Sched x GST s₀ anchor i₂ H s B (S.P.proposer s) hDiv hMono
      hSync hCatch hRoots hParent hOwner hU hAdvQ hSleepK hAnchor hGST ht₀ hChain hInv hLocks
      hLocks₀ hOld hCaches hAfter hOpener hPropose hNoCollision hprop
  intro i t v a hl ht hAw hHon hSent
  rcases Nat.lt_or_ge t (supportCutoff S (s₀ + 1)) with hlt | hge
  · exact le_trans (hOld i t v a hl hlt hAw hHon hSent) (Nat.le_of_lt hHB)
  -- from the healed round's action time on, the attestation names an entry of the honest chain
  obtain ⟨s_a, E, -, hts, ⟨hs₀a, w, hw, C, hC, hEC⟩, -, hEh, -⟩ :=
    lem82_honest_attestations_on_chain S Sched x s₀ hDiv hMono i t v a hl hge hAw hHon hSent
  -- the time is a round's action time, so `s_a` is a round's first slot
  obtain ⟨r', hr'⟩ := attest_time_round S Sched x hl hSent
  have hsa : s_a = r' * S.C.R := by
    have h1 : supportCutoff S (s_a + 1) = supportCutoff S (r' * S.C.R + 1) := by
      rw [← hts]; exact hr'
    have h2 := slot_lt_of_supportCutoff_le S (le_of_eq h1)
    have h3 := slot_lt_of_supportCutoff_le S (le_of_eq h1.symm)
    omega
  have hsa_lt : s_a < (r + 1) * S.C.R := by
    by_contra hn
    have := supportCutoff_mono S (show (r + 1) * S.C.R + 1 ≤ s_a + 1 by omega)
    omega
  have hsa_le : s_a ≤ s := by
    rw [hsa, hs]
    rw [hsa] at hsa_lt
    have := Nat.lt_of_mul_lt_mul_right hsa_lt
    exact Nat.mul_le_mul_right _ (by omega)
  -- `E` is `B` or an ancestor of `B`
  have hEB : E.AncestorEq B := by
    rcases Nat.lt_or_ge s_a s with hlt' | hge'
    · exact hChainB E ⟨s_a, hlt', hs₀a, w, hw, C, hC, hEC⟩
    · have hsaeq : s_a = s := le_antisymm hsa_le hge'
      subst hsaeq
      rw [hSavedAll w hw] at hC
      cases hC
      exact hEC
  have := (lem47_chain_state_heights S.C E B).2.2.2.1 hEB
  rw [hEh] at this
  exact this

end GoldilocksCorrectness.Proofs.Executions
