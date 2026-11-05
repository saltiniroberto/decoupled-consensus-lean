module
public import GoldilocksCorrectness.Proofs.Executions.BlockPropagation
public import GoldilocksCorrectness.Proofs.Executions.Clock
public import GoldilocksCorrectness.Proofs.Routines.FGState
public import GoldilocksCorrectness.Proofs.Routines.Node
public import GoldilocksCorrectness.Proofs.Routines.Wiring

@[expose] public section

/-!
# Lemma 54: an honest attestation is delivered within `Δ_F`

The proofs of `attestation_in_pool_by_GST` and `lem54_honest_attestation_delivered`, stated in
`GoldilocksCorrectness/Statements/Executions/HeightAttestationStatements.lean`, and the kit fact
they need: a validator's pool of attestations only grows along an execution (`AttPoolGrows`,
`pool_grows_of_le`).

The route: the network delivers the attestation before `max t GST + Δ_F`
(`delivered_before_stepBefore_of_honest_send`, at the class `fgObject`); the delivery runs
`on_attestation`, which appends a well-formed attestation to the pool; and no routine removes an
attestation from the pool, so it is in the receiver's node state before `max t GST + Δ_F`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ_F)

open GoldilocksCorrectness.Proofs.Routines (DREBPost DREBPost.bind DREBPost.bind_any DREBPost.dite
  DREBPost.ite DREBPost.of_outcome DREBPost.pure forIn_yield_inv)

open GoldilocksCorrectness.Proofs.Routines (fg_on_attestation_pool fg_on_block_pool)

open GoldilocksCorrectness.Proofs.Routines (AttPoolGrows AttPoolGrows.of_S AttPoolGrows.refl
  on_attestation_pool on_block_pool tick_pool)

open GoldilocksCorrectness.Proofs.Routines (receive_pool)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions

variable {V : Type} [DecidableEq V] [Fintype V]

variable [RootOrder]

section Execution

variable {S : Setup V} {Sched : Schedule V} (x : AtomicExec (protocol S) Sched)

/-- Every step keeps every validator's pool.

The variables:
- `x`: the execution; `i`: the step; `v`: the validator. -/
theorem step_pool (i : ℕ) (v : V) : AttPoolGrows (x[i][v].st) (x[i + 1][v].st) := by
  rcases step_cases x i v with h | ⟨t, n', sent, -, -, hok, h⟩ | ⟨sm, -, -, -, h⟩
  · rw [h]; exact AttPoolGrows.refl _
  · rw [h]
    have hin : AttPoolGrows (x[i][v].st) (tickInputState x i t v) :=
      AttPoolGrows.of_S (tickInputState_frame x i t v).1
    exact hin.trans (DREBPost.of_outcome (tick_pool S.C S.P S.X _ _) hok)
  · rw [h]; exact receive_pool S.C S.P S.X _ _

/-- **Kit fact, the pool of attestations only grows.** From a step to a later one, a
validator's pool of attestations keeps every attestation it holds.

The variables:
- `x`: the execution; `v`: the validator; `i ≤ j`: the two steps.

Read aloud: an attestation a validator holds in its pool stays there. -/
theorem pool_grows_of_le (v : V) {i j : ℕ} (hij : i ≤ j) :
    AttPoolGrows (x[i][v].st) (x[j][v].st) :=
  rel_of_forall_step AttPoolGrows AttPoolGrows.refl (fun _ _ _ h h' => h.trans h')
    (fun k => x[k][v].st) hij (fun k _ _ => step_pool x k v)

end Execution

/-- **Kit theorem, an honest attestation is in the pool by `GST` plus `Δ_F`.** The proof; the
audited statement is in `Statements/Executions/HeightAttestationStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `t`: the time of the send; `v`: the sender; `w`: the receiver; `a`: the
  attestation. -/
theorem attestation_in_pool_by_GST (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST t : ℕ) (v w : V) (a : Attestation V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSyncF : SynchronyFromWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hCatchF : CatchUpOnWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hv : v ∉ Sched.adv (t : Int))
    (hSend : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake t ∧
      (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    (hw : ∀ t' : ℕ, max t GST ≤ t' → t' ≤ max t GST + Δ_F S →
      w ∈ Sched.awake (t' : Int) ∧ w ∉ Sched.adv (t' : Int))
    (hWF : attestation_well_formed a = true) :
    a ∈ (stateBefore x (max t GST + Δ_F S) w).S.attestations := by
  obtain ⟨i, hl, hsent⟩ := hSend
  obtain ⟨hT1, hT2⟩ := time_of_lbl_tickAllAwake x hl
  have hhon : v ∉ Sched.adv (x[i].time : Int) := fun h =>
    hv (hMono _ _ (by exact_mod_cast (by omega : x[i].time ≤ t)) h)
  obtain ⟨d, -, hld, hd⟩ := delivered_before_stepBefore_of_honest_send x hDiv hSyncF hCatchF
    hMono (sm := ⟨v, NamedObject.attest a⟩) ⟨hsent, hhon⟩ trivial
    (by omega : x[i + 1].time ≤ max t GST) (le_max_right t GST) hw
  obtain ⟨-, -, hstep⟩ := deliver_step_state x hld
  have hin : a ∈ (x[d + 1][w].st).S.attestations := by
    rw [hstep]
    exact (on_attestation_pool _ a).2 hWF
  exact pool_grows_of_le x w hd a hin

/-- **Lemma 54, an honest attestation is delivered.** The proof; the audited statement is in
`Statements/Executions/HeightAttestationStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `t`: the time of the send; `v`: the sender; `w`: the receiver; `a`: the
  attestation. -/
theorem lem54_honest_attestation_delivered (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST t : ℕ) (v w : V) (a : Attestation V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSyncF : SynchronyFromWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hCatchF : CatchUpOnWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hGST : GST ≤ t)
    (hv : v ∉ Sched.adv (t : Int))
    (hSend : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake t ∧
      (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    (hw : ∀ t' : ℕ, t ≤ t' → t' ≤ t + Δ_F S →
      w ∈ Sched.awake (t' : Int) ∧ w ∉ Sched.adv (t' : Int))
    (hWF : attestation_well_formed a = true) :
    a ∈ (stateBefore x (t + Δ_F S) w).S.attestations := by
  have h := attestation_in_pool_by_GST S Sched x GST t v w a hDiv hMono hSyncF hCatchF hv hSend
    (by rw [max_eq_left hGST]; exact hw) hWF
  rwa [max_eq_left hGST] at h

end GoldilocksCorrectness.Proofs.Executions
