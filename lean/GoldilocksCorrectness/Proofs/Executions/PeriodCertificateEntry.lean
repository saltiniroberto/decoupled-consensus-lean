module
public import GoldilocksCorrectness.Proofs.Executions.Lemma91
public import GoldilocksCorrectness.Proofs.Executions.PeriodChainBlock

@[expose] public section

/-! a kit statement, new. The audited statement is in
`Statements/Executions/PeriodCertificateEntryStatements.lean`.

- `cert_entry_held_by_attester`: a progress certificate on a chain an honest validator holds has
  an honest attester, an updater of a slot `sₐ` whose tick at `supportCutoff S (sₐ + 1)` sent it;
  the certified block is an ancestor of that update's fast block, and the attester held it before
  that tick.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (supportCutoff)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction AtomicHonest Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (ProgressCertOn)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- **Kit fact K1: the certified entry is held by an honest attester at its tick.** The proof;
the audited statement is in `Statements/Executions/PeriodCertificateEntryStatements.lean`.
`cert_entry_at_slot`'s route up to the tick step `j'` that sent the honest member's attestation,
then `attest_source_fast_block_updater_inTree` at `j'`; the entry it names and the certified block
have one root and are held by honest validators by `x[j].time`, so they are one block.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `j`: the step; `w`: the holder;
  `Y`: the held block; `T`: the block the certificate names; `h`: its height. -/
theorem cert_entry_held_by_attester (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (j : ℕ) (w : V) (Y T : Block V) (h : Height)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : AdversaryFewerThanQuorumUntil Sched (quorum V) (x[j].time : Int))
    (hRoots : RootsNameBlocksUntil S Sched x x[j].time)
    (hw : w ∉ Sched.adv (x[j].time : Int))
    (hY : Y ∈ (x[j][w].st).S.T) (hTY : T.AncestorEq Y) (hJ : ProgressCertOn Y h T) :
    ∃ (sₐ : ℕ) (uₐ : V) (F : Block V), supportCutoff S (sₐ + 1) ≤ x[j].time ∧
      uₐ ∈ updaterAt S Sched sₐ ∧ uₐ ∉ Sched.adv ((supportCutoff S (sₐ + 1) : ℕ) : Int) ∧
      F ∈ (stateBefore x (supportCutoff S (sₐ + 1) + 1) uₐ).A.fast_blocks ∧ T.AncestorEq F ∧
      T ∈ (stateBefore x (supportCutoff S (sₐ + 1)) uₐ).S.T := by
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
  -- its attestation of the certificate is in its record, and its tick sent it
  obtain ⟨a, hau, -, haT, hon⟩ := hA u hu
  have hrec := lem74_honest_attestations_recorded S Sched x hU j w Y a hY hon
    (by rw [hau]; exact hhon)
  rw [hau] at hrec
  obtain ⟨j', t', a', hj', hl, hAw, hHon, hsent, -, hcont, -⟩ :=
    record_content_sent_step S Sched x u j _ hrec
  have hT' : a'.T = T.root := by
    rw [← haT]
    exact congrArg AttestationContent.T hcont
  have htt := time_of_lbl_tickAllAwake x hl
  have ht'j : t' ≤ x[j].time := by
    rw [← htt.2]
    exact time_mono x hj'
  -- the attestation's source is a fast block of the update the tick ran, held before the tick
  obtain ⟨sₐ, E, F, ht, hv, hF, hFT, hEF, -, -, hE3⟩ :=
    attest_source_fast_block_updater_inTree S Sched x j' t' u a' hDiv hMono hl hAw hHon hsent
  have hET : E ∈ (x[j'][u].st).S.T := ancestors_mem_T_of_exec S Sched x j' u F E hFT hEF
  have hui : AtomicHonest x j' u := fun h' =>
    hHon (hMono _ _ (by have := htt.1; omega) h')
  -- the certified block is held by `w` at `j`; one root, so one block
  have hTT : T ∈ (x[j][w].st).S.T := ancestors_mem_T_of_exec S Sched x j w Y T hY hTY
  have hEq : E = T := hRoots E T
    ⟨j', u, hui, by have := htt.1; omega, hET⟩ ⟨j, w, hw, le_rfl, hTT⟩ (hE3.symm.trans hT')
  subst hEq
  subst ht
  refine ⟨sₐ, u, F, ht'j, hv, hHon, hF, hEF, ?_⟩
  show E ∈ (x[stepBefore x (supportCutoff S (sₐ + 1))][u].st).S.T
  rw [stepBefore_eq_of_lbl x hl]
  exact hET

end GoldilocksCorrectness.Proofs.Executions
