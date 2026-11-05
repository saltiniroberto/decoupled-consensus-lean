module
public import GoldilocksCorrectness.Statements.Executions.HealedAttestationDefs
public import GoldilocksCorrectness.Statements.Routines.AttestationStatements
public import GoldilocksCorrectness.Statements.Routines.TickStatements
public import GoldilocksCorrectness.Statements.Executions.HonestChainStatements
public import GoldilocksCorrectness.Statements.Executions.WakeStatements
public import GoldilocksCorrectness.Statements.Executions.InvariantStatements
public import GoldilocksCorrectness.Statements.Executions.ChainStateStatements
public import GoldilocksCorrectness.Proofs.Executions.Wake
public import GoldilocksCorrectness.Proofs.Executions.TickSends
public import GoldilocksCorrectness.Proofs.Executions.RoundKit
public import GoldilocksCorrectness.Proofs.Executions.Lemma42
public import GoldilocksCorrectness.Proofs.Executions.Lemma55
public import GoldilocksCorrectness.Proofs.Routines.Record
public import GoldilocksCorrectness.Proofs.Routines.ChainStateOf
public import GoldilocksCorrectness.Proofs.Routines.ACInterface
public import GoldilocksCorrectness.Proofs.Routines.Node
public import GoldilocksCorrectness.Proofs.Routines.NodeTick

@[expose] public section

/-!
# Lemma 82: the honest attestations after the healed round name the honest chain's entries

The proofs of `isEntry_T_h` and `lem82_honest_attestations_on_chain`, stated in
`GoldilocksCorrectness/Statements/Executions/HealedAttestationStatements.lean`, and the kit facts
they need: the source of the attestation duty is a fast block (`ac_to_fg_source_fast`), a tick
that sends an attestation passed the duty test (`tick_attest_awake`), and the duty test passed on
the state a tick's first step leaves comes from the stored `awakeSince` when the time compared
with is before the tick (`awakeSince_of_record_awake`).

The route of Lemma 82: the attestation is the one the client built at the action time of a round
`r` from the source's height and `T_h` (Lemma 49); that time is the support cutoff of slot
`s + 1` with `s = r · R`; the tick passed the duty test, so it ran the confirmation update of slot
`s + 1` (Lemma 15), whose fast blocks hold the source; the update then saved a confirmation `C`
for slot `s` with the source an ancestor of `C` or `C`; the validator is awake through the
update's window, so it is an updater of slot `s`, and keeps `C` right after its update. The block
that took the source's chain into its height is an entry block of the honest chain at the
attestation's height (`isEntry_T_h`).


-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ supportCutoff dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_eq supportCutoff_cast
  supportCutoff_eq supportCutoff_slot supportCutoff_succ_times voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (duty_window_start_le_dutyWindowStart)

open GoldilocksCorrectness.Proofs.Routines (duty_window_start_lt_supportCutoff)

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Statements.Routines
open GoldilocksCorrectness.Proofs.Routines (propose_block_sends record_awake_awakeSince_some
  record_awake_awakeSince_none)
open GoldilocksCorrectness.Proofs.Routines (ac_on_tick_sends)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

end GoldilocksCorrectness.Proofs.Routines

namespace GoldilocksCorrectness.Proofs.Executions

open GoldilocksCorrectness.Proofs.Routines (mem_fg_to_ac_tree)

open GoldilocksCorrectness.Statements.Routines (IsEntry chainStateOf)

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (lem15_tick_updates_confirmation lem49_tick_attests)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_trans ac_to_fg_source_mem
  ac_to_fg_source_fast tick_attest_awake awakeSince_of_record_awake create_attestation_cases
  update_confirmation_fast_block_saved)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **Lemma 82 (b), the honest attestation's entry at its slot.** The proof; the audited
statement is in `Statements/Executions/HealedAttestationStatements.lean`. Lemma 82
(`lem82_honest_attestations_on_chain`) is this tuple with the updater and its confirmation put
together as `OnHonestChainAt`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot;
- `i`: the step of the tick; `t`: its time; `v`: the attester; `a`: the attestation. -/
theorem lem82b_entry_at_slot (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ i t : ℕ) (v : V) (a : Attestation V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hl : x.lbl i = AtomicAction.tickAllAwake t) (ht₀ : supportCutoff S (s₀ + 1) ≤ t)
    (hAwake : v ∈ Sched.awake (t : Int)) (hHon : v ∉ Sched.adv (t : Int))
    (hSent : (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈
      x[i + 1].sent - x[i].sent) :
    ∃ (s : ℕ) (E C : Block V), s₀ ≤ s ∧ t = supportCutoff S (s + 1) ∧ v ∈ updaterAt S Sched s ∧
      (stateBefore x (supportCutoff S (s + 1) + 1) v).A.saved_confirmation s = some C ∧
      E.AncestorEq C ∧ IsEntry S.C E ∧ (chainStateOf S.C E).h = a.h ∧ a.T = E.root := by
  -- the tick, and the attestation it built
  obtain ⟨-, n', sent, hrun, ha, hst, -⟩ := tick_send_step_outcome hl hSent
  obtain ⟨hAct, fi, source, hfi, hsrc, hca, -⟩ :=
    lem49_tick_attests S.C S.P S.X _ n' _ sent a hrun ha
  have hR := (tick_attest_awake S.C S.P S.X (tickInputState x i t v) (t : Int)).of_outcome hrun
  have hawk := hR a ha
  -- the time is the support cutoff of slot `s + 1`, with `s` the first slot of the round
  obtain ⟨r, hr⟩ : ∃ r : ℕ, r = S.C.round (S.C.slot (t : Int)) := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : ℕ, s = r * S.C.R := ⟨_, rfl⟩
  obtain ⟨hslot, hround, hact', hcut⟩ := supportCutoff_succ_times S r s hs
  have htInt : (t : Int) = ((supportCutoff S (s + 1) : ℕ) : Int) := by
    rw [hact', hslot, hround, hr]
    exact hAct
  have ht : t = supportCutoff S (s + 1) := by exact_mod_cast htInt
  subst ht
  -- the healed slot is at most `s`
  have hs₀ : s₀ ≤ s := by
    rcases Nat.lt_or_ge s s₀ with h | h
    · exfalso
      have hlt : supportCutoff S (s + 1) < supportCutoff S (s₀ + 1) := by
        rw [supportCutoff_eq, supportCutoff_eq, voteTime_eq, voteTime_eq, slotStart_eq,
          slotStart_eq]
        have hΔ := one_le_Δ S
        have := Nat.mul_lt_mul_of_pos_left (show s + 1 < s₀ + 1 by omega)
          (by omega : 0 < 4 * Δ S)
        omega
      exact absurd (lt_of_lt_of_le hlt ht₀) (lt_irrefl _)
    · exact h
  -- the duty test passed, on the stored `awakeSince`
  rw [hslot] at hawk
  have hdws : duty_window_start S.C (s + 1) < ((supportCutoff S (s + 1) : ℕ) : Int) :=
    duty_window_start_lt_supportCutoff S (s + 1)
  obtain ⟨τ, hτ, hτle⟩ := awakeSince_of_record_awake hawk hdws
  -- the confirmation update of slot `s + 1` ran in the tick, and saved a confirmation for slot `s`
  obtain ⟨A'', hUpd, hsave, hfb, -, -⟩ := lem15_tick_updates_confirmation S.C S.P S.X _ n' _ sent
    hrun hcut ⟨τ, hτ, by rw [hslot]; exact hτle⟩
  rw [hslot] at hUpd
  have hfast : source ∈ A''.fast_blocks := by
    rw [← hfb]
    exact ac_to_fg_source_fast hfi hsrc
  obtain ⟨C, hC, hsrcC⟩ := update_confirmation_fast_block_saved S.C S.P _ A'' _ _ (s + 1) source
    (Nat.le_add_left 1 s) hUpd hfast
  rw [Nat.add_sub_cancel] at hC
  -- the state right after the update keeps that confirmation
  have hkeep := stateBefore_succ_keepsConfirmation x hDiv v (time_of_lbl_tickAllAwake x hl).2
  rw [hst] at hkeep
  have hSaved : (stateBefore x (supportCutoff S (s + 1) + 1) v).A.saved_confirmation s =
      some C := by
    rw [hkeep.2.1, hsave]
    exact hC
  -- the validator is an updater of slot `s`
  have hc1 : 1 ≤ supportCutoff S (s + 1) := (supportCutoff_slot S s).2
  have hτ' : (tickInputState x (stepBefore x (supportCutoff S (s + 1))) (supportCutoff S (s + 1))
      v).awakeSince = some τ := by
    rw [stepBefore_eq_of_lbl x hl]
    exact hτ
  have hawake := awake_of_tickInput_awakeSince x hDiv hMono hc1 hτ' hAwake hHon
  have hv : v ∈ updaterAt S Sched s := by
    refine Finset.mem_sdiff.2 ⟨mem_awakeThroughout_of_forall (fun t'' h1 h2 => ?_), hHon⟩
    refine hawake t'' ?_ h2
    have h3 : duty_window_start S.C (s + 1) ≤ ((dutyWindowStart S (s + 1) : ℕ) : Int) :=
      duty_window_start_le_dutyWindowStart S (s + 1)
    have h4 : ((dutyWindowStart S (s + 1) : ℕ) : Int) ≤ (t'' : Int) := by exact_mod_cast h1
    exact le_trans hτle (le_trans h3 h4)
  -- the attestation's height and root are the source's chain state's
  have hSeq := (tickInputState_frame x i (supportCutoff S (s + 1)) v).1
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
    refine ⟨s, (chainStateOf S.C source).T_h, C, hs₀, rfl, hv, hSaved,
      ancestorEq_trans hE3 hsrcC, hE1, ?_, ?_⟩
    · show _ = ((tickInputState x i (supportCutoff S (s + 1)) v).S.σ source).h
      rw [hSeq, hσ]
      exact hE2
    · show ((tickInputState x i (supportCutoff S (s + 1)) v).S.σ source).T_h.root = _
      rw [hSeq, hσ]

/-- **Lemma 82, the honest attestations after the healed round name the honest chain's
entries, each at the slot whose update it followed.** The proof; the audited statement is in
`Statements/Executions/HealedAttestationStatements.lean`. Lemma 82 (b), `lem82b_entry_at_slot`,
with the updater and its saved confirmation put together as `OnHonestChainAt`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot. -/
theorem lem82_honest_attestations_on_chain (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ : ℕ)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption) :
    HonestAttestationsOnChain S Sched x s₀ (supportCutoff S (s₀ + 1)) := by
  intro i t v a hl ht₀ hAwake hHon hSent
  obtain ⟨s, E, C, hs₀, ht, hv, hSaved, hEC, hEe, hEh, hEr⟩ :=
    lem82b_entry_at_slot S Sched x s₀ i t v a hDiv hMono hl ht₀ hAwake hHon hSent
  exact ⟨s, E, hs₀, ht, ⟨hs₀, v, hv, C, hSaved, hEC⟩, hEe, hEh, hEr⟩

end GoldilocksCorrectness.Proofs.Executions
