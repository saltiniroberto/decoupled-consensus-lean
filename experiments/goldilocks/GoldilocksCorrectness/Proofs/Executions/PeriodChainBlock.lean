module
public import GoldilocksCorrectness.Statements.Executions.AsyncResilienceChainBlockDefs
public import GoldilocksCorrectness.Proofs.Executions.PeriodFinality
public import GoldilocksCorrectness.Statements.Executions.ChainStateStatements
public import GoldilocksCorrectness.Statements.Routines.CertificateStatements
public import GoldilocksCorrectness.Proofs.Executions.ChainState
public import GoldilocksCorrectness.Proofs.Routines.Accountable
public import GoldilocksCorrectness.Proofs.Routines.ChainStateOf
public import GoldilocksCorrectness.Proofs.Routines.ChainStateOfCertified
public import GoldilocksCorrectness.Proofs.Routines.FGStateReaders
public import GoldilocksCorrectness.Proofs.Routines.Wiring

@[expose] public section

/-! Every landed definition and statement of record stays byte-identical; The audited statements are in
`Statements/Executions/PeriodChainBlockStatements.lean`.

- `AsyncHypsOfChainBlock`, the copy of `AsyncHyps` whose hand-over facts are
  `HandoverFactsOfChainBlock`, and `AsyncHypsOfChainBlock.toAsyncHyps`: the copy gives the
  original (the original certificate clause from the copied attestation clause, by the landed
  `certificatesCompatibleWithAt_of_attestations`), so every landed step lemma taking `AsyncHyps`
  is called through it;
- `attestationsCompatibleWithBefore_of_heldEntry`, `handoverFacts_of_ofChainBlock`,
  `certificatesCompatibleWithOfChainBlock_iff`: the copied clauses against the originals;
- `attest_source_fast_block_updater_inTree`, the copy of `attest_source_fast_block_updater` with
  the conjunct "the fast block is in the attester's tree before the tick";
- `certificatesCompatibleWithAtOfChainBlock_of_attestations`, the copy of
  `certificatesCompatibleWithAt_of_attestations` (Lemma 102's step) concluding the copied
  certificate clause, with roots naming blocks up to `x[j].time`;

- `anchor_extends_B_of_inv_orTwoPast`: the copy of `anchor_extends_B_of_inv` with the hypothesis
  "not contested" weakened to that disjunction.

 Deleted then, with the
originals of these copies: `attestations_step_ofHeldEntry` and `holder_vote_extends_B_orTwoPast`,
the originals of the later copies `attestations_step_ofHeldEntry_ofCompat` and
`holder_vote_extends_B_orTwoPast_ofCompat` (`Proofs/Executions/PeriodCompatCopies.lean`). The
originals still used by the proofs of the top statements stay: `AsyncHyps`, `HandoverFacts`, the
original certificate and attestation clauses, and `certificatesCompatibleWithAt_of_attestations`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ Δ_F slotStart voteTime supportCutoff
  dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_eq slot_eq_of_mem supportCutoff_cast
  supportCutoff_eq supportCutoff_slot supportCutoff_succ_times voteTime_cast voteTime_eq)

open GoldilocksCorrectness.Statements.Routines (IsEntry chainStateOf)

open GoldilocksCorrectness.Statements.Routines (ChainStatesComputed)

open GoldilocksCorrectness.Statements.Routines (CachesCompatibleWith)

open GoldilocksCorrectness.Proofs.Routines (duty_window_start_le_dutyWindowStart
  duty_window_start_lt_supportCutoff)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

section Period

variable (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)

/-- `AsyncHypsOfChainBlock S Sched x GST s B H t₀ anchor tAwakeEnd b₀ b₁`: `AsyncHyps S Sched x
GST s B H t₀ anchor tAwakeEnd b₀ b₁` with the hand-over facts `HandoverFactsOfChainBlock` in place
of `HandoverFacts`.
unforgeability; fewer than a quorum ever corrupted; committee sleepiness from `anchor`, at or
before the start of slot `s + 1`; `GST` at or before `b₀`; the period's bounds; the
lock holders' majority; `t₀` at or before the hand-over cutoff; and the hand-over
facts over the copied clauses, whose last clause reads the confirmed tips from `tAwakeEnd` on
.

 `AsyncHypsOfChainBlock.toAsyncHyps` gives the original. -/
structure AsyncHypsOfChainBlock (GST s : ℕ) (B : Block V) (H t₀ anchor tAwakeEnd b₀ b₁ : ℕ) :
    Prop where
  hDiv : TimeDiverges x.toTrace
  hMono : Sched.MonotoneCorruption
  hSync : SynchronyFromWakeOutside Sched x.toTrace (Δ S) GST acObject b₀ b₁
  hCatch : CatchUpOnWakeOutside Sched x.toTrace (Δ S) GST acObject b₀ b₁
  hSyncF : SynchronyFromWakeOutside Sched x.toTrace (Δ_F S) GST fgObject b₀ b₁
  hCatchF : CatchUpOnWakeOutside Sched x.toTrace (Δ_F S) GST fgObject b₀ b₁
  hParent : ParentHeldAtDelivery S Sched x
  hOwner : VotesCastByOwner S Sched x
  hU : Unforgeability Vocab.goldilocks Sched x.toTrace
  hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t
  hSleepK : CommitteeSleepiness S Sched anchor
  hAnchor : anchor ≤ slotStart S (s + 1)
  hGST : GST ≤ b₀
  hb₀ : supportCutoff S (s + 1) ≤ b₀
  hb : b₀ ≤ b₁
  hb₁ : b₁ + Δ S ≤ voteTime S (s + S.C.k)
  hHold : HoldersOutweighWhereOwed S Sched s b₀ b₁
  ht₀ : t₀ ≤ supportCutoff S (s + 1)
  hHand : HandoverFactsOfChainBlock S Sched x s B H t₀ tAwakeEnd

end Period

end GoldilocksCorrectness.Statements.Executions

namespace GoldilocksCorrectness.Proofs.Executions

open GoldilocksCorrectness.Proofs.Routines (mem_fg_to_ac_tree not_contested_or_two_past)

open GoldilocksCorrectness.Proofs.Routines (entry_eq_of_compatible_le)

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg AtomicHonest)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once. No statement and no proof term changes.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

section Clauses

open GoldilocksCorrectness.Statements.Routines (lem15_tick_updates_confirmation lem49_tick_attests
  ProgressCertOn expireLocks)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_trans ac_to_fg_source_mem
  ac_to_fg_source_fast tick_attest_awake awakeSince_of_record_awake create_attestation_cases
  compatible_iff compatible_of_ancestorEq_compatible ancestorEq_compatible
  update_confirmation_fast_blocks_pass goldfish_score_eq_ok mem_supportersOf_iff
  disjoint_supportersOf_equivocators supportersOf mem_equivocators_iff dre_bind_ok on_chain_mono)

/-! ## The copied clauses against the originals -/

/-- The copied attestation clause gives the original: the conjunct `inHonestTreeBy x t E` is
dropped.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `B`: the protected block; `H`: the
  height threshold; `t₀`: the time from which the attestations are new; `j`: the step. -/
theorem attestationsCompatibleWithBefore_of_heldEntry {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (protocol S) Sched} {B : Block V} {H t₀ j : ℕ}
    (hAtt : AttestationsCompatibleWithBeforeOfHeldEntry S Sched x B H t₀ j) :
    AttestationsCompatibleWithBefore S Sched x B H t₀ j := by
  intro i t v a hi hl hAw hHon hsent
  obtain ⟨hOld, hNew⟩ := hAtt i t v a hi hl hAw hHon hsent
  refine ⟨hOld, fun ht => ?_⟩
  obtain ⟨E, h1, h2, h3, h4, -⟩ := hNew ht
  exact ⟨E, h1, h2, h3, h4⟩

/-- The copied hand-over facts give the original, under unforgeability and with fewer than a
quorum ever corrupted: the original attestation clause from the copied one, and the original
certificate clause from it by the landed Lemma 102 step
(`certificatesCompatibleWithAt_of_attestations`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the hand-over slot; `B`: the
  protected block; `H`: the height threshold; `t₀`: the time from which the attestations are new;
  `tAwakeEnd`: the time from which the confirmed tips are read; `hDiv`:
  every time is reached (the caches clause, read at the steps whose time is the cutoff, gives the
  original's at the step before the time after the cutoff). -/
theorem handoverFacts_of_ofChainBlock {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (protocol S) Sched} {s : ℕ} {B : Block V} {H t₀ tAwakeEnd : ℕ}
    (hDiv : TimeDiverges x.toTrace)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace) (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hHand : HandoverFactsOfChainBlock S Sched x s B H t₀ tAwakeEnd) :
    HandoverFacts S Sched x s B H t₀ tAwakeEnd := by
  obtain ⟨h1, h2, h3c, -, h5, h6, h7⟩ := hHand
  -- the caches clause at the step before the time after the cutoff, whose time is the cutoff
  have h3 : ∀ u ∉ Sched.adv ((supportCutoff S (s + 1) : ℕ) : Int),
      CachesCompatibleWith S B H (stateBefore x (supportCutoff S (s + 1) + 1) u) := fun u hu => by
    have ht := time_stepBefore_add_one x hDiv (show 1 ≤ supportCutoff S (s + 1) + 1 by omega)
    have ht' : x[stepBefore x (supportCutoff S (s + 1) + 1)].time = supportCutoff S (s + 1) := by
      omega
    exact h3c _ u ht' (by rw [ht']; exact hu)
  have h5' : AttestationsCompatibleWithBefore S Sched x B H t₀
      (stepBefore x (supportCutoff S (s + 1) + 1)) :=
    attestationsCompatibleWithBefore_of_heldEntry h5
  exact ⟨h1, h2, h3, certificatesCompatibleWithAt_of_attestations S Sched x _ hU (hAdvQ _) h5',
    h5', h6, h7⟩

/-- The copied bundle gives the original: every field is kept, and the hand-over facts by
`handoverFacts_of_ofChainBlock`.

The variables:
- `P`: the copied hypotheses. -/
theorem AsyncHypsOfChainBlock.toAsyncHyps {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (protocol S) Sched} {GST s : ℕ} {B : Block V} {H t₀ anchor tAwakeEnd b₀ b₁ : ℕ}
    (P : AsyncHypsOfChainBlock S Sched x GST s B H t₀ anchor tAwakeEnd b₀ b₁) :
    AsyncHyps S Sched x GST s B H t₀ anchor tAwakeEnd b₀ b₁ :=
  ⟨P.hDiv, P.hMono, P.hSync, P.hCatch, P.hSyncF, P.hCatchF, P.hParent, P.hOwner, P.hU, P.hAdvQ,
    P.hSleepK, P.hAnchor, P.hGST, P.hb₀, P.hb, P.hb₁, P.hHold, P.ht₀,
    handoverFacts_of_ofChainBlock P.hDiv P.hU P.hAdvQ P.hHand⟩

/-- `CertificatesCompatibleWithOfChainBlock` is `CertificatesCompatibleWithAtOfChainBlock` at every
step.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `H`: the height threshold; `B`: the
  protected block. -/
theorem certificatesCompatibleWithOfChainBlock_iff (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (H : ℕ) (B : Block V) :
    CertificatesCompatibleWithOfChainBlock S Sched x H B ↔
      ∀ j, CertificatesCompatibleWithAtOfChainBlock S Sched x H B j :=
  ⟨fun h j => h j, fun h j => h j⟩

/-! ## The attestation's source is in the attester's tree -/

/-- **The attestation's source is a fast block of the update its tick ran, held before the
tick.** The proof; the audited statement is in
`Statements/Executions/PeriodChainBlockStatements.lean`. The proof of
`attest_source_fast_block_updater`, with the fact `hsT` it has kept in the conclusion.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `i`: the step of the tick; `t`: its
  time; `v`: the attester; `a`: the attestation. -/
theorem attest_source_fast_block_updater_inTree (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (i t : ℕ) (v : V) (a : Attestation V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hl : x.lbl i = AtomicAction.tickAllAwake t)
    (hAwake : v ∈ Sched.awake (t : Int)) (hHon : v ∉ Sched.adv (t : Int))
    (hSent : (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈
      x[i + 1].sent - x[i].sent) :
    ∃ (s' : ℕ) (E F : Block V), t = supportCutoff S (s' + 1) ∧ v ∈ updaterAt S Sched s' ∧
      F ∈ (stateBefore x (t + 1) v).A.fast_blocks ∧ F ∈ (x[i][v].st).S.T ∧
      E.AncestorEq F ∧ IsEntry S.C E ∧
      (chainStateOf S.C E).h = a.h ∧ a.T = E.root := by
  -- the tick, and the attestation it built
  obtain ⟨-, n', sent, hrun, ha, hst, -⟩ := tick_send_step_outcome hl hSent
  obtain ⟨hAct, fi, source, hfi, hsrc, hca, -⟩ :=
    lem49_tick_attests S.C S.P S.X _ n' _ sent a hrun ha
  have hR := (tick_attest_awake S.C S.P S.X (tickInputState x i t v) (t : Int)).of_outcome hrun
  have hawk := hR a ha
  -- the time is the support cutoff of slot `s' + 1`, with `s'` the first slot of the round
  obtain ⟨r, hr⟩ : ∃ r : ℕ, r = S.C.round (S.C.slot (t : Int)) := ⟨_, rfl⟩
  obtain ⟨s', hs⟩ : ∃ s' : ℕ, s' = r * S.C.R := ⟨_, rfl⟩
  obtain ⟨hslot, hround, hact', hcut⟩ := supportCutoff_succ_times S r s' hs
  have htInt : (t : Int) = ((supportCutoff S (s' + 1) : ℕ) : Int) := by
    rw [hact', hslot, hround, hr]
    exact hAct
  have ht : t = supportCutoff S (s' + 1) := by exact_mod_cast htInt
  subst ht
  -- the duty test passed, on the stored `awakeSince`
  rw [hslot] at hawk
  have hdws : duty_window_start S.C (s' + 1) < ((supportCutoff S (s' + 1) : ℕ) : Int) :=
    duty_window_start_lt_supportCutoff S (s' + 1)
  obtain ⟨τ, hτ, hτle⟩ := awakeSince_of_record_awake hawk hdws
  -- the confirmation update of slot `s' + 1` ran in the tick; the source is one of its fast blocks
  have hfast : source ∈ n'.A.fast_blocks := ac_to_fg_source_fast hfi hsrc
  -- the state right after the update keeps the fast blocks
  have hkeep := stateBefore_succ_keepsConfirmation x hDiv v (time_of_lbl_tickAllAwake x hl).2
  rw [hst] at hkeep
  have hF : source ∈ (stateBefore x (supportCutoff S (s' + 1) + 1) v).A.fast_blocks := by
    rw [hkeep.2.2.1]
    exact hfast
  -- the validator is an updater of slot `s'`
  have hc1 : 1 ≤ supportCutoff S (s' + 1) := (supportCutoff_slot S s').2
  have hτ' : (tickInputState x (stepBefore x (supportCutoff S (s' + 1)))
      (supportCutoff S (s' + 1)) v).awakeSince = some τ := by
    rw [stepBefore_eq_of_lbl x hl]
    exact hτ
  have hawake := awake_of_tickInput_awakeSince x hDiv hMono hc1 hτ' hAwake hHon
  have hv : v ∈ updaterAt S Sched s' := by
    refine Finset.mem_sdiff.2 ⟨mem_awakeThroughout_of_forall (fun t'' h1 h2 => ?_), hHon⟩
    refine hawake t'' ?_ h2
    have h3 : duty_window_start S.C (s' + 1) ≤ ((dutyWindowStart S (s' + 1) : ℕ) : Int) :=
      duty_window_start_le_dutyWindowStart S (s' + 1)
    have h4 : ((dutyWindowStart S (s' + 1) : ℕ) : Int) ≤ (t'' : Int) := by exact_mod_cast h1
    exact le_trans hτle (le_trans h3 h4)
  -- the attestation's height and root are the source's chain state's
  have hSeq := (tickInputState_frame x i (supportCutoff S (s' + 1)) v).1
  have hsT : source ∈ (x[i][v].st).S.T := by
    rw [← hSeq]
    exact ((mem_fg_to_ac_tree _ _).1 (ac_to_fg_source_mem hfi hsrc)).1
  have hσ : (x[i][v].st).S.σ source = chainStateOf S.C source :=
    (lem11_node_invariant S Sched x i v).1.2.2.2.2.2.1 source hsT
  rcases create_attestation_cases _ _ _ _ _ _ _ with h0 | ⟨τ', fp', -, -, -, h1⟩
  · rw [h0] at hca
    cases hca
  · rw [h1] at hca
    injection hca with hca
    subst hca
    obtain ⟨hE1, hE2, hE3⟩ := GoldilocksCorrectness.Proofs.Routines.isEntry_T_h S.C source
    refine ⟨s', (chainStateOf S.C source).T_h, source, rfl, hv, hF, hsT, hE3, hE1, ?_, ?_⟩
    · show _ = ((tickInputState x i (supportCutoff S (s' + 1)) v).S.σ source).h
      rw [hSeq, hσ]
      exact hE2
    · show ((tickInputState x i (supportCutoff S (s' + 1)) v).S.σ source).T_h.root = _
      rw [hSeq, hσ]


/-! ## The certificates, over the copied clauses -/

/-- **Lemma 102 at a step, concluding the copied certificate clause.** The proof; the audited
statement is in `Statements/Executions/PeriodChainBlockStatements.lean`. The proof of
`certificatesCompatibleWithAt_of_attestations` up to the honest signer's attestation, which names
an entry `E` compatible with `B` held by an honest validator by the attestation's time, at most
`x[j].time`; the certificate's block `T`, a block of `D`'s chain, is held by `w` at `j`
(`ancestors_mem_T_of_exec`); `E` and `T` have one root, so are one block.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `H`: the height threshold; `t₀`: the
  time from which the attestations are new; `B`: the protected block; `j`: the step.

Roots name blocks until `x[j].time`: the attestation's entry, held by the attestation's time, and
the certificate's block, held by `w` at step `j`, have one root. -/
theorem certificatesCompatibleWithAtOfChainBlock_of_attestations (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) {H t₀ : ℕ} {B : Block V} (j : ℕ)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hRoots : RootsNameBlocksUntil S Sched x x[j].time)
    (hAdvQ : AdversaryFewerThanQuorumUntil Sched (quorum V) (x[j].time : Int))
    (hAtt : AttestationsCompatibleWithBeforeOfHeldEntry S Sched x B H t₀ j) :
    CertificatesCompatibleWithAtOfChainBlock S Sched x H B j := by
  intro w D T h hw hD hTD hJ hH
  obtain ⟨A, hqA, hA⟩ := hJ
  -- a member of the quorum outside the adversary set up to the time after `j` steps
  obtain ⟨u, hu, hhon⟩ : ∃ u ∈ A, HonestThrough x j u := by
    by_contra hno
    have hall : ∀ v ∈ A, ∃ t' : Int, t' ≤ (x[j].time : Int) ∧ v ∈ Sched.adv t' := by
      intro v hv
      by_contra hn
      exact hno ⟨v, hv, fun t' ht' ha => hn ⟨t', ht', ha⟩⟩
    have h3 := hAdvQ A hall
    omega
  -- its vote of the certificate is in its record, and its tick sent it
  obtain ⟨a, hau, hah, haT, hon⟩ := hA u hu
  have hrec := GoldilocksCorrectness.Statements.Executions.lem74_honest_attestations_recorded S
    Sched x hU j w D a hD hon (by rw [hau]; exact hhon)
  rw [hau] at hrec
  obtain ⟨j', t', a', hj', hl, hAw, hHon, hsent, -, hcont, -⟩ :=
    record_content_sent_step S Sched x u j _ hrec
  have hh' : a'.h = h := by
    rw [← hah]
    exact congrArg AttestationContent.h hcont
  have hT' : a'.T = T.root := by
    rw [← haT]
    exact congrArg AttestationContent.T hcont
  obtain ⟨hOld, hNew⟩ := hAtt j' t' u a' hj' hl hAw hHon hsent
  rcases Nat.lt_or_ge t' t₀ with hlt | hge
  · -- before `t₀`, its height would be at most `H`
    have hle := hOld hlt
    rw [hh'] at hle
    exact absurd hle (Nat.not_le.mpr hH)
  · -- from `t₀` on, it names an entry compatible with `B`, held by its time
    obtain ⟨E, hEB, -, -, hET, i₀, v₀, hv₀, hti₀, hE₀⟩ := hNew hge
    -- the certificate's block is held by `w` at `j`
    have hTT : T ∈ (x[j][w].st).S.T := ancestors_mem_T_of_exec S Sched x j w D T hD hTD
    have ht'j : t' ≤ x[j].time := by
      have h1 := (time_of_lbl_tickAllAwake x hl).2
      have h2 := time_mono x (show j' + 1 ≤ j from hj')
      omega
    have hEq : E = T := hRoots E T ⟨i₀, v₀, hv₀, le_trans hti₀ ht'j, hE₀⟩ ⟨j, w, hw, le_rfl, hTT⟩
      (hET.symm.trans hT')
    rw [← hEq]
    exact hEB

/-! ## Not contested, or two past `B` -/

/-- **Not contested, or two past `B`, at an honest validator.** The proof; the audited statement
is in `Statements/Executions/PeriodChainBlockStatements.lean`. `not_contested_or_two_past` at `w`'s
FG state after `j` steps: its chain states are computed (Lemma 11), its caches are compatible with
`B` (`hC`), and the copied certificate clause at `j` covers every held chain.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `H`: the height threshold; `B`: the
  protected block; `j`: the step; `w`: the validator. -/
theorem not_contested_or_two_past_of_certificates (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) {H : ℕ} {B : Block V} (j : ℕ) (w : V)
    (hw : w ∉ Sched.adv (x[j].time : Int))
    (hCert : CertificatesCompatibleWithAtOfChainBlock S Sched x H B j)
    (hC : CachesCompatibleWith S B H (x[j][w].st)) :
    fg_contest (x[j][w].st).S = false ∨
      (chainStateOf S.C B).h + 2 ≤ (x[j][w].st).S.h_max :=
  not_contested_or_two_past S.C (x[j][w].st).S B H
    (lem11_node_invariant S Sched x j w).1.2.2.2.2.2.1
    hC.2.1 hC.2.2.1 hC.2.2.2.1 hC.1
    (fun D hD h T hTD hcert hH _ => hCert w D T h hw hD hTD hcert hH)

end Clauses

section Holders

open GoldilocksCorrectness.Proofs.Routines
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn expireLocks)

/-! ## The anchor and the vote, with not contested or two past `B` -/


end Holders

end GoldilocksCorrectness.Proofs.Executions
