module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma91
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.PeriodChainBlock
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption

@[expose] public section

/-!
# PeriodCertificateEntry, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/PeriodCertificateEntry.lean`, over a model
`M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: the certified entry of a
progress certificate on an honest-held chain is held by its honest attester. The page's
routine-level theorems are the facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (supportCutoff)

namespace GoldilocksCorrectness.Record.Proofs.Executions

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax IsEntry VoterTreeAt JustifiedInTree AnchorAt)

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
open GoldilocksCorrectness.Statements.Executions (Vocab.goldilocks)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- **Kit fact K1: the certified entry is held by an honest attester at its tick.** The proof;
the audited statement is in `Statements/Executions/PeriodCertificateEntryStatements.lean`.
`cert_entry_at_slot`'s route up to the tick step `j'` that sent the honest member's attestation,
then `attest_source_fast_block_updater_inTree` at `j'`; the entry it names and the certified block
have one root and are held by honest validators by `x[j].time`, so they are one block.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `j`: the step; `w`: the holder;
  `Y`: the held block; `T`: the block the certificate names; `h`: its height.

Read aloud: a progress certificate on a chain an honest validator holds has an honest attester that
ran the update of a slot `sₐ` awake and honest from that slot's duty window up to its own tick to
`supportCutoff S (sₐ + 1)`, a step before the step `j`, and is outside the
adversary set after every step whose time is at most the time after `j` steps; that tick
sent it; the certified block `T` is an ancestor of that update's fast block `F`, or `F`, and
the attester held `T` before that tick. -/
theorem cert_entry_held_by_attester (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (j : ℕ) (w : V) (Y T : Block V) (h : Height)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (x.time j))
    (hRoots : RootsNameBlocksUntil M A x (x.time j))
    (hw : w ∉ A.corrupted j)
    (hY : Y ∈ (x.st j w).tree) (hTY : T.AncestorEq Y) (hJ : ProgressCertOn M Y h T) :
    ∃ (sₐ : ℕ) (uₐ : V) (F : Block V), x.tickStep uₐ (M.supportCutoff S.C (sₐ + 1)) < j ∧
      uₐ ∈ A.activeThroughoutToTick x (duty_window_start S.C (sₐ + 1)) (M.supportCutoff S.C (sₐ + 1)) ∧
      uₐ ∉ A.corruptedAtTime x (x.time j) ∧
      F ∈ (x.tickOutput uₐ (M.supportCutoff S.C (sₐ + 1))).fastBlocks ∧ T.AncestorEq F ∧
      T ∈ (x.tickInput uₐ (M.supportCutoff S.C (sₐ + 1))).tree := by
  obtain ⟨X₁, hX₁Y, Q, hqA, hQ⟩ := hJ
  rw [GoldilocksCorrectness.Record.quorumAt_eq_quorum Fx F.sched X₁] at hqA
  -- a member of the quorum outside the adversary set after every step whose time is at most
  -- `x.time j`
  obtain ⟨u, hu, hhonM⟩ : ∃ u ∈ Q, A.HonestThroughTime x (x.time j) u := by
    by_contra hno
    have hall : ∀ v ∈ Q, ∃ i : ℕ, x.time i ≤ x.time j ∧ v ∈ A.corrupted i := by
      intro v hv
      by_contra hn
      exact hno ⟨v, hv, fun i hi ha => hn ⟨i, hi, ha⟩⟩
    have h3 := hAdvQ Q hall
    omega
  have hhon : x.HonestThrough A j u := fun i' hi' => hhonM i' ((time_mono M) x R hi')
  -- its attestation of the certificate is in its record, and its tick sent it
  obtain ⟨a, hau, -, haT, hon⟩ := hQ u hu
  have hrec : a.content ∈ (x.st j a.val_index).sentAttestations :=
    (lem74_honest_attestations_recorded M F) S A x R E j w Y a hY
      ((GoldilocksCorrectness.Record.Proofs.Routines.on_chain_mono M F) a hX₁Y hon)
      (by rw [hau]; exact hhon)
  rw [hau] at hrec
  obtain ⟨j', t', a', hj', hl, -, hsent, -, hcont, -⟩ :=
    (record_content_sent_step M F) S A x R E u j _ hrec
  have hT' : a'.T = T.root := by
    rw [← haT]
    exact congrArg AttestationContent.T hcont
  -- the attestation's source is a fast block of the update the tick ran, in the state the tick
  -- leaves, held before the tick; its entry block of the attestation's height is held there too
  obtain ⟨sₐ, source, -, ht, hv, hF, hsT, -, -, -, hT⟩ :=
    (attest_tick_update_source M F U) S A x R j' t' u a' E hl hsent
  obtain ⟨-, -, hE3⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.isEntry_T_h M F) S.C source
  have hET : (M.chainStateOf S.C source).T_h ∈ (x.st j' u).tree :=
    (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E j' u
      source _ hsT hE3
  -- the certified block is held by `w` at `j`; one root, so one block
  have hTT : T ∈ (x.st j w).tree :=
    (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E j w Y T
      hY hTY
  have hEq : (M.chainStateOf S.C source).T_h = T := hRoots _ T
    ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := j') (v := u) (hhon j' hj'.le) ((time_mono M) x R hj'.le) hET) ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := j) (v := w) hw le_rfl hTT)
    (hT.symm.trans hT')
  rw [hEq] at hE3 hET
  subst ht
  have hts := (tickStep_eq_of_lbl M) x E hl
  refine ⟨sₐ, u, source, by rw [hts]; exact hj', hv, Activity.not_mem_corruptedAtTime.2 hhonM, hF,
    hE3, ?_⟩
  -- the tick's input state is `u`'s state after `j'` steps
  unfold Trace.tickInput
  rw [hts]
  exact hET

end GoldilocksCorrectness.Record.Proofs.Executions

