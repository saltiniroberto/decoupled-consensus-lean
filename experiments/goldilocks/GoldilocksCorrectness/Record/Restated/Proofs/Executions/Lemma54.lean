module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.BlockPropagation
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Clock
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Node
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Wiring
public import GoldilocksCorrectness.Proofs.Executions.BlockPropagation
public import GoldilocksCorrectness.Proofs.Executions.Clock
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma54, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma54.lean`, over a model `M` whose facts
`F` hold, for an execution `x` of `protocolOf M S`: a validator's attestations held only grow along
an execution (the fields `tick_pool` of `F.tk` and `receive_pool` of `F.rcv`), and Lemma 54, an
honest attestation is held by every awake honest validator within `Δ_F` of `GST` (the field
`receive_attestation_held` of `F.rcv`). The page's routine-level theorems are the facts' fields or
have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ_F)

open GoldilocksCorrectness.Proofs.Routines (DREBPost DREBPost.bind DREBPost.bind_any DREBPost.dite
  DREBPost.ite DREBPost.of_outcome DREBPost.pure forIn_yield_inv)

open GoldilocksCorrectness.Proofs.Routines (fg_on_attestation_pool fg_on_block_pool)

open GoldilocksCorrectness.Proofs.Routines (AttPoolGrows AttPoolGrows.of_S AttPoolGrows.refl
  on_attestation_pool on_block_pool tick_pool)

open GoldilocksCorrectness.Proofs.Routines (receive_pool)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Proofs.Executions (rel_of_forall_step)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (fgObject)

variable {V : Type} [DecidableEq V] [Fintype V]
variable (M : GoldilocksModel V) (F : Facts M)
include F

variable [RootOrder]

section Execution

variable {S : Setup V} {A : Activity V} (x : Trace V (NamedObject V) M.N)

/-- Every step keeps every validator's pool.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `i`: the step; `v`: the validator.

Read aloud: every step keeps every attestation a validator holds. -/
theorem step_pool (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (i : ℕ) (v : V) :
    ∀ a ∈ (x.st i v).attestationsHeld, a ∈ (x.st (i + 1) v).attestationsHeld := by
  rcases (step_cases_per_step M F) x R E i v with h | ⟨t, n', sent, hl, -, hok, h, -⟩ | ⟨sm, -, -, h⟩ |
      ⟨⟨tRw, keepw, hlw⟩, -, h⟩
  · rw [h]; exact fun _ ha => ha
  · rw [h]
    have hti : x.tickInput v t = x.st i v := by
      unfold Trace.tickInput
      rw [(tickStep_eq_of_lbl M) x E hl]
    intro a ha
    exact F.tk.tick_pool S.C S.P S.X _ _ n' sent hok a (by rw [hti]; exact ha)
  · rw [h]; exact F.rcv.receive_pool S.C S.P S.X _ _
  · rw [h tRw keepw hlw]
    obtain ⟨-, -, -, -, -, -, hP, -⟩ := F.wk.wake_readers (x.st i v) (tRw : Int)
    intro a ha
    show a ∈ M.attestationsHeld (M.wake (x.st i v) (tRw : Int))
    rw [hP]
    exact ha

/-- **Kit fact, the pool of attestations only grows.** From a step to a later one, a
validator's pool of attestations keeps every attestation it holds.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `v`: the validator; `i ≤ j`: the two steps.

Read aloud: an attestation a validator holds in its pool stays there. -/
theorem pool_grows_of_le (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (v : V) {i j : ℕ} (hij : i ≤ j) :
    ∀ a ∈ (x.st i v).attestationsHeld, a ∈ (x.st j v).attestationsHeld :=
  rel_of_forall_step (fun n n' : M.N => ∀ a ∈ n.attestationsHeld, a ∈ n'.attestationsHeld)
    (fun _ _ ha => ha) (fun _ _ _ h h' a ha => h' a (h a ha))
    (fun k => x.st k v) hij (fun k _ _ => (step_pool M F) x R E k v)

end Execution

/-- **Kit theorem, an honest attestation put on the wire at a tick is in the pool at the receiver's
later tick.** An attestation `a` that `v`, honest at its tick `i` to `t`, put on the
wire there is in `w`'s pool on the state `w`'s tick `kR` to a clock value `D ≥ max t GST + Δ_F S`
starts from, when `w` is active after every step from `i + 1` up to `kR`.

Why: `v`'s tick is at a real time at most `t + ΔClockBehind`, `w`'s tick `kR` at a real time at least
`D − ΔClockAhead ≥ t + Δ_F S − ΔClockAhead`; the two clock bounds together are less than `Δ_F S`
(`hSkew_F`), so `i < kR`. The message's deadline `max (x.time (i + 1)) GST + ΔNet_F` is at most
`max t GST + ΔClockBehind + ΔNet_F ≤ D − ΔClockAhead` (`hNet_F`), so the delivery field delivers `a` to
`w` before `kR` (or a delivery is already there); the pool admits the well-formed attestation and only
grows.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `A`, `x`, `R`: the setup, the activity, the execution, the run's facts; `GST`: the time from
  which attestations are delivered within `ΔNet_F`; `t`: the clock value of `v`'s tick; `v`: the
  sender; `w`: the receiver; `a`: the attestation;
- `E`, `E_F`: the environment's facts for blocks and Goldfish votes, and for attestations;
- `i`: the step of `v`'s tick; `D`: the clock value of `w`'s tick `kR`.

Read aloud: an attestation an honest validator sends at its tick to `t` is in the pool of every
validator active from that tick up to its own tick to a clock value at least `max t GST + Δ_F S`, on
the state that tick starts from. -/
theorem attestation_in_tickInput_of_tick_send (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST t : ℕ) (v w : V) (a : Attestation V)
    {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {ΔNet_F : ℕ} (E_F : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    -- `v` put `a` on the wire at its tick `i` to `t`
    {i : ℕ} (hl : x.lbl i = Event.tick v t)
    (hsent : (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    -- `w` ticks to `D ≥ max t GST + Δ_F S` at `kR`, and is active after every step from `i + 1` up to `kR`
    {D kR : ℕ} (hD : max t GST + Δ_F S ≤ D) (hkR : x.lbl kR = Event.tick w D)
    (hwin : ∀ j : ℕ, i + 1 ≤ j → j ≤ kR → w ∈ A.active j)
    -- `a` is well formed
    (hWF : M.attestation_well_formed a = true) :
    a ∈ (x.st kR w).attestationsHeld := by
  classical
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  have hhon : v ∉ A.corrupted i := E.not_mem_corrupted_of_tick hl
  have hB0 := E.behind_nonneg
  obtain ⟨⟨-, hTi⟩, -, hTi1⟩ := (time_of_lbl_tick M) x R E hl
  have hkRt := (E.tick_active kR w D hkR).2.1
  have hDr : ((max t GST : ℕ) : ℝ) + Δ_F S ≤ D := by exact_mod_cast hD
  have htm : (t : ℝ) ≤ ((max t GST : ℕ) : ℝ) := by exact_mod_cast le_max_left t GST
  have hGm : (GST : ℝ) ≤ ((max t GST : ℕ) : ℝ) := by exact_mod_cast le_max_right t GST
  have hik : i < kR := by
    by_contra hc
    have := htime (show kR ≤ i by omega)
    linarith
  have hdk : max (x.time (i + 1)) (GST : ℝ) + (ΔNet_F : ℝ) ≤ x.time kR := by
    have : max (x.time (i + 1)) (GST : ℝ) ≤ ((max t GST : ℕ) : ℝ) + ΔClockBehind :=
      max_le (by linarith) (by linarith)
    linarith
  have hex : ∃ j, i < j ∧ x.lbl j = Event.deliver w ⟨v, NamedObject.attest a⟩ ∧ j < kR := by
    by_cases hdel : ∃ j₀ : ℕ, i < j₀ ∧ j₀ < kR ∧ x.lbl j₀ = Event.deliver w ⟨v, NamedObject.attest a⟩
    · obtain ⟨j₀, h1, h2, h3⟩ := hdel
      exact ⟨j₀, h1, h3, h2⟩
    · obtain ⟨j, hij, hjk, hlj, -, -⟩ := E_F.delivered i kR w ⟨v, NamedObject.attest a⟩ D
        (max (x.time (i + 1)) (GST : ℝ) + (ΔNet_F : ℝ)) ⟨hsent, hhon⟩
        (show fgObject (NamedObject.attest a) from trivial) hkR hik hwin rfl hdk
        (fun _ j₀ _ _ _ hij₀ hl₀ _ hj₀k₁ hk₁k _ _ _ => absurd ⟨j₀, hij₀, by omega, hl₀⟩ hdel)
      exact ⟨j, hij, hlj, hjk⟩
  obtain ⟨j, -, hlj, hjk⟩ := hex
  obtain ⟨-, hstep⟩ := (deliver_step_state M F) x R E hlj
  have hin : a ∈ (x.st (j + 1) w).attestationsHeld := by
    rw [hstep]
    exact F.rcv.receive_attestation_held S.C S.P S.X _ a hWF
  exact (pool_grows_of_le M F) x R E w hjk a hin

/-- **Kit theorem, an honest attestation is in the pool by `GST` plus `Δ_F`.** The proof; the
audited statement is in `Statements/Executions/HeightAttestationStatements.lean`.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `t`: the time of the send; `v`: the sender; `w`: the receiver; `a`: the
  attestation.

Why: when the send is from `GST` on, synchrony from the send delivers it to `w`, active since the
send; when it is before `GST`, `v` holds `a` from its tick on (`tick_holds_sent`), serves it at
`GST` (`hserve`), and the sync fact at `GST`, read at `w`'s tick `kR`, delivers it.

Read aloud: an attestation that `v`, active from its send through `max t GST` and still serving it
at `GST`, put on the wire at its tick at `t` is held, before `max t GST + max (Δ_F S) Δs_F`, by every
validator active from `max t GST` for one delivery delay or one sync delay, whichever is longer. -/
theorem attestation_in_pool_by_GST (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST t : ℕ) (v w : V) (a : Attestation V)
    {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    -- attestations are delivered within `Δ_F S` after `GST`, to a receiver active since the send
    {ΔNet_F : ℕ} (E_F : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)

    -- what an honest active validator would serve reaches every validator active from then within `Δs_F`
    {Δs_F : ℕ} (Sy_F : SyncedWithin A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST)
    -- `v` is active from the send through `Δs_F` after `max t GST`, the time it serves `a` at
    (hvA : v ∈ A.activeThroughout x t (max t GST + Δs_F))
    -- when the send is before `GST`, `v` still serves `a` at `GST`: its justified height just before `GST`
    -- is at most `a`'s height
    (hserve : t < GST → M.justifiedHeight (x.stateBefore GST v) ≤ a.h)
    -- `v` put `a` on the wire at its tick at `t`
    (hSend : ∃ i : ℕ, x.lbl i = Event.tick v t ∧
      (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    -- `w` ticks to `max t GST + max (Δ_F S) Δs_F` at a step `kR` and is active after every step from the first one
    -- whose time is `ΔClockAhead` before `max t GST` up to `kR` (, T-K1)
    (hw : ∃ kR : ℕ, x.lbl kR = Event.tick w (max t GST + max (Δ_F S) Δs_F) ∧
      ∀ j : ℕ, (((max t GST : ℕ) : ℝ) : ℝ) - ΔClockAhead ≤ x.time j → j ≤ kR → w ∈ A.active j)
    -- `a` is well formed
    (hWF : M.attestation_well_formed a = true) :
    a ∈ (x.tickInput w (max t GST + max (Δ_F S) Δs_F)).attestationsHeld := by
  classical
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  obtain ⟨i, hl, hsent⟩ := hSend
  obtain ⟨kR, hkR, hwR⟩ := hw
  obtain ⟨-, hTi1l, hTi1⟩ := (time_of_lbl_tick M) x R E hl
  have hti : x.tickInput w (max t GST + max (Δ_F S) Δs_F) = x.st kR w := by
    unfold Trace.tickInput
    rw [(tickStep_eq_of_lbl M) x E hkR]
  rw [hti]
  have hmx1 := le_max_left (Δ_F S) Δs_F
  have hmx2 := le_max_right (Δ_F S) Δs_F
  by_cases hsync : (((max t GST : ℕ) : ℝ) : ℝ) - ΔClockAhead ≤ x.time (i + 1)
  · -- the send is at a real time from `max t GST − ΔClockAhead` on: the send-at-a-tick route
    exact (attestation_in_tickInput_of_tick_send M F) S A x R GST t v w a E E_F hNet_F hSkew_F hl hsent
      (by omega) hkR (fun j h1 h2 => hwR j (le_trans hsync (htime h1)) h2) hWF
  · -- the send is at a real time less than `GST − ΔClockAhead`: `v` holds `a` at `GST`, serves it, and
    -- the sync fact at `GST` delivers it before `kR`
    push_neg at hsync
    have hGt' : t < GST := by
      by_contra hc
      push_neg at hc
      have : ((max t GST : ℕ) : ℝ) = t := by rw [max_eq_left hc]
      linarith
    have hmax : max t GST = GST := max_eq_right (le_of_lt hGt')
    rw [hmax] at hsync hkR hwR
    have hG1 : 1 ≤ GST := by omega
    obtain ⟨hkt, hkt'⟩ := (stepBefore_time M) x R E hG1
    -- after its tick, `v` holds the attestation it sent
    obtain ⟨n', sent, hok, hst, hsentL⟩ := R.tick i v t hl
    have hmem : NamedObject.attest a ∈ sent := by
      rw [hsentL, add_tsub_cancel_left] at hsent
      obtain ⟨m', hm', heq⟩ := Multiset.mem_map.1 hsent
      injection heq with _ hmo
      subst hmo
      exact Multiset.mem_coe.1 hm'
    have hInv := (lem11_node_invariant M F S A x R E i v
      (E.not_mem_corrupted_of_tick hl)).1
    have hok' : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.st i v) (t : Int) := hok
    have hheld : a ∈ (x.st (i + 1) v).attestationsHeld := by
      rw [hst]
      exact (F.tk3.tick_holds_sent S.C S.P S.X (x.st i v) (t : Int) n' sent hok' hInv).2 a hmem
    have hiG : i < x.stepBefore GST := ((lt_stepBefore_iff M) x R E).2 (by
      push_cast at hsync
      linarith)
    have hheldG : a ∈ (x.st (x.stepBefore GST) v).attestationsHeld :=
      (pool_grows_of_le M F) x R E v (by omega) a hheld
    have hvA' : v ∈ A.activeThroughout x (t : ℝ) ((GST : ℝ) + Δs_F) := by
      refine Activity.mem_activeThroughout_of_le le_rfl (le_of_eq ?_) hvA
      push_cast [hmax]
      ring
    have htG : (t : ℝ) < GST := by exact_mod_cast hGt'
    have hu : v ∈ A.active (x.stepBefore GST) :=
      Activity.mem_activeThroughout.1 hvA' _ (by
        have : (0 : ℝ) ≤ Δs_F := Nat.cast_nonneg _
        linarith) (by linarith)
    have hkRt := (E.tick_active kR w _ hkR).2.1
    have hΔF : ΔClockAhead < (Δ_F S : ℝ) := by linarith
    have hkkR : x.stepBefore GST ≤ kR := by
      by_contra hc
      have := htime (show kR ≤ x.stepBefore GST by omega)
      have hmF : ((Δ_F S : ℕ) : ℝ) ≤ max ((Δ_F S : ℕ) : ℝ) (Δs_F : ℝ) := le_max_left _ _
      push_cast at hkRt
      linarith
    rcases Sy_F (GST : ℝ) (x.stepBefore GST) v w (NamedObject.attest a) (max GST GST + Δs_F)
        (GST + max (Δ_F S) Δs_F) kR hkt hkt' hu ⟨hheldG, hserve hGt'⟩
        (show fgObject (NamedObject.attest a) from trivial)
        (by
          rw [Nat.ceil_natCast]
          exact fun j h1 h2 => Activity.mem_active_of_mem_activeThroughout_of_time htime hvA'
            (by linarith) (by exact_mod_cast h2)) (by rw [Nat.ceil_natCast]; rfl) hkR (by rw [max_self]; omega)
        (fun j h1 h2 => hwR j (by push_cast; linarith) h2)
        -- an attestation has no release clock value: the re-delivery premise is empty
        (fun _ _ _ _ hrel => absurd hrel (by simp [releaseOf])) with
      hwA | ⟨j, -, -, -, -, hlj, hjk, -, -⟩
    · exact (pool_grows_of_le M F) x R E w hkkR a hwA.1
    · obtain ⟨-, hstep⟩ := (deliver_step_state M F) x R E hlj
      have hin : a ∈ (x.st (j + 1) w).attestationsHeld := by
        rw [hstep]
        exact F.rcv.receive_attestation_held S.C S.P S.X _ a hWF
      exact (pool_grows_of_le M F) x R E w hjk a hin

/-- **Lemma 54, an honest attestation is delivered.** The proof; the audited statement is in
`Statements/Executions/HeightAttestationStatements.lean`.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `t`: the time of the send; `v`: the sender; `w`: the receiver; `a`: the
  attestation.

Read aloud: after `GST`, an attestation an honest validator sends is held, by the tick to the send's
time plus `Δ_F`, by every validator awake and honest for that delay.

Why the tick's input: the delivery promise of the environment
puts the delivery at a step before `w`'s tick to `t + Δ_F S`; the conclusion reads that bound
directly, on the node state that tick starts from, whatever the order of the deliveries and the
ticks at one time. -/
theorem lem54_honest_attestation_delivered (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST t : ℕ) (v w : V) (a : Attestation V)
    {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {ΔNet_F : ℕ} (E_F : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    (hGST : GST ≤ t)
    (hSend : ∃ i : ℕ, x.lbl i = Event.tick v t ∧
      (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    -- `w` ticks to `t + Δ_F S` at a step `kR` and is active after every step from the first one
    -- whose time is `ΔClockAhead` before `t` up to `kR` (, T-K1)
    (hw : ∃ kR : ℕ, x.lbl kR = Event.tick w (t + Δ_F S) ∧
      ∀ j : ℕ, ((t : ℝ) : ℝ) - ΔClockAhead ≤ x.time j → j ≤ kR → w ∈ A.active j)
    (hWF : M.attestation_well_formed a = true) :
    a ∈ (x.tickInput w (t + Δ_F S)).attestationsHeld := by
  obtain ⟨i, hl, hsent⟩ := hSend
  obtain ⟨kR, hkR, hwR⟩ := hw
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  obtain ⟨-, hTi1l, -⟩ := (time_of_lbl_tick M) x R E hl
  have hti : x.tickInput w (t + Δ_F S) = x.st kR w := by
    unfold Trace.tickInput
    rw [(tickStep_eq_of_lbl M) x E hkR]
  rw [hti]
  exact (attestation_in_tickInput_of_tick_send M F) S A x R GST t v w a E E_F hNet_F hSkew_F hl hsent
    (by rw [max_eq_left hGST]) hkR (fun j h1 h2 => hwR j (le_trans hTi1l (htime h1)) h2) hWF

end GoldilocksCorrectness.Record.Proofs.Executions

