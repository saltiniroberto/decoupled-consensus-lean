module
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.ConfirmationCompatibilityStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.AsyncDeliveryStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma31UpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma32UpTo
public import GoldilocksCorrectness.Statements.Executions.ConfirmationCompatibilityStatements
public import GoldilocksCorrectness.Statements.Executions.AsyncDeliveryStatements
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# ConfirmationCompatibilityStatementsUpTo, over a model

The statements of
`GoldilocksCorrectness/Statements/Executions/ConfirmationCompatibilityStatementsUpTo.lean`, over a
model `M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: Lemmas 31 and 32, two
honest confirmations of one slot are compatible, with the delivery premises up to a bound. Each is
the theorem of the same name of `Record/Restated/Proofs/Executions/Lemma31UpTo.lean` or
`Record/Restated/Proofs/Executions/Lemma32UpTo.lean`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ supportCutoff viewFreeze dutyWindowStart)

namespace GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDeliveryUpTo SyncedWithinUpTo)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (ConfirmationUpdated)
open GoldilocksCorrectness.Statements.Executions (acObject)
open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor ConfirmationUpdated)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn expireLocks)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- **Lemma 31, two honest confirmation updates of a slot save compatible blocks.** In an
execution synchronous from the support cutoff of slot `s`, the confirmation updates of slot
`s + 1`, for the slot `s`, on the states of `v₁` and `v₂` at their ticks to the support cutoff of slot
`s + 1`, their expired lock entries removed, that save `C₁` and `C₂` as the confirmation of slot
`s`, save compatible blocks, when each validator is awake and honest from the support cutoff of
slot `s` to its view freeze and ticking to the support cutoff of slot `s + 1`, where its update runs
.

Why: Lemma 30. A vote resolving early at one validator was held there before the support cutoff
of slot `s`, was re-sent then, and reaches the other within one delay, while it is awake; every
pool vote before the update is stamped before it; the two frame trees hold only blocks of honest
validators, where a root names one block.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s`: the slot confirmed;
- `v₁`, `v₂`: the two validators; `n₁'`, `n₂'`: the node states the two updates leave;
- `C₁`, `C₂`: the blocks saved.

Read aloud: in a synchronous execution from the support cutoff of slot `s`, if two validators,
each awake and honest from that cutoff for one delay and ticking to the cutoff where the update for slot `s` runs,
have that update save `C₁` and `C₂`, then `C₁` and `C₂` are on one chain.

Roots name blocks until the later real time of the two ticks to the support cutoff of slot `s + 1`: the
proof compares the blocks of the two
frame trees on `v₁`'s and `v₂`'s states before the support cutoff of slot `s + 1`.

Restated with the delivery premises up to `M.supportCutoff S.C s + Δ S`: Lemma 62, in each
direction, reads the re-sends at the support cutoff of slot `s`, due one delay after it. -/
theorem lem31_saved_confirmations_compatible_upTo (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s : ℕ) (v₁ v₂ : V) (n₁' n₂' : M.N)
    (C₁ C₂ : Block V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C s + Δ S)) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C s + Δ S))
    -- the network is synchronous from the support cutoff of slot `s` on
    (hGST : GST + max (Δ S) Δs ≤ M.viewFreeze S.C s)
    -- `v₁` ticks to the view freeze of slot `s` at `kF₁`, and is active at every step up to that tick
    -- whose real time is at least `ΔClockAhead` before `M.viewFreeze S.C s − max (3 * Δ S) Δs`, and at every
    -- step whose real time is in the sync delay after the earliest re-send
    (kF₁ : ℕ) (hkF₁ : x.lbl kF₁ = Event.tick v₁ (M.viewFreeze S.C s))
    (hwin₁ : ∀ i : ℕ, (M.viewFreeze S.C s : ℝ) - max (3 * Δ S) Δs - ΔClockAhead ≤ x.time i → i ≤ kF₁ →
      v₁ ∈ A.active i)
    (hv₁₀ : v₁ ∈ A.activeThroughout x ((M.viewFreeze S.C s) - (max (Δ S) Δs)) (((M.viewFreeze S.C s) - (max (Δ S) Δs)) + Δs))
    -- `v₂` ticks to the view freeze of slot `s` at `kF₂`, and is active at every step up to that tick
    -- whose real time is at least `ΔClockAhead` before `M.viewFreeze S.C s − max (3 * Δ S) Δs`, and at every
    -- step whose real time is in the sync delay after the earliest re-send
    (kF₂ : ℕ) (hkF₂ : x.lbl kF₂ = Event.tick v₂ (M.viewFreeze S.C s))
    (hwin₂ : ∀ i : ℕ, (M.viewFreeze S.C s : ℝ) - max (3 * Δ S) Δs - ΔClockAhead ≤ x.time i → i ≤ kF₂ →
      v₂ ∈ A.active i)
    (hv₂₀ : v₂ ∈ A.activeThroughout x ((M.viewFreeze S.C s) - (max (Δ S) Δs)) (((M.viewFreeze S.C s) - (max (Δ S) Δs)) + Δs))
    -- `v₁` and `v₂` tick to the support cutoff of slot `s + 1` at `k₁`, `k₂`, where their updates run
    -- (the read point, T-RC10-1,)
    (k₁ : ℕ) (hk₁ : x.lbl k₁ = Event.tick v₁ (M.supportCutoff S.C (s + 1)))
    (k₂ : ℕ) (hk₂ : x.lbl k₂ = Event.tick v₂ (M.supportCutoff S.C (s + 1)))
    -- a root names one block among what honest validators hold, until the later real time of the two
    -- ticks to the support cutoff of slot `s + 1`
    (hRoots : RootsNameBlocksUntil M A x (max (x.time k₁) (x.time k₂)))
    -- the update of slot `s + 1` at `v₁`'s tick to the support cutoff of slot `s + 1` leaves
    -- `n₁'` and saves `C₁` as the confirmation of slot `s`
    (hUpdate₁ : ConfirmationUpdated M S.C S.P (x.tickInput v₁ (M.supportCutoff S.C (s + 1)))
      ((M.supportCutoff S.C (s + 1) : ℕ) : Int) (s + 1) n₁')
    (hSaved₁ : n₁'.savedConfirmation s = some C₁)
    -- likewise at `v₂`
    (hUpdate₂ : ConfirmationUpdated M S.C S.P (x.tickInput v₂ (M.supportCutoff S.C (s + 1)))
      ((M.supportCutoff S.C (s + 1) : ℕ) : Int) (s + 1) n₂')
    (hSaved₂ : n₂'.savedConfirmation s = some C₂) :
    -- then `C₁` and `C₂` are compatible
    C₁.compatible C₂ = true := by
  exact (GoldilocksCorrectness.Record.Proofs.Executions.lem31_saved_confirmations_compatible_upTo M F U) S
    A x R GST s v₁ v₂ n₁' n₂' C₁ C₂ E hNet hSkew hRedeliver Sy hGST kF₁ hkF₁ hwin₁ hv₁₀ kF₂ hkF₂ hwin₂ hv₂₀ k₁ hk₁ k₂ hk₂ hRoots
    hUpdate₁ hSaved₁ hUpdate₂ hSaved₂

/-- **Lemma 32, the saved confirmations of two honest validators are compatible.** In an
execution synchronous from the support cutoff of slot `s`, the blocks `C₁` and `C₂` that `v₁` and
`v₂` have saved as the confirmation of slot `s` on their states before `t₂ + 1`, `t₂` the support
cutoff of slot `s + 1`, are compatible, when each validator is awake and honest from the duty
window's start of slot `s + 1` up to its own tick to `t₂`.

Why: the wake window makes the tick at `t₂` run the confirmation update of slot `s + 1` (Lemma
15), whose saved confirmation the state before `t₂ + 1` keeps; the window contains Lemma 31's,
since the duty window of slot `s + 1` starts no later than slot `s`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s`: the slot confirmed;
- `v₁`, `v₂`: the two validators; `C₁`, `C₂`: the blocks saved.

Read aloud: if two validators, each awake and honest from the duty window's start of slot `s + 1`
up to its own tick to its support cutoff, have `C₁` and `C₂` saved as their confirmation of slot `s` right after that
cutoff, then `C₁` and `C₂` are on one chain.

Roots name blocks until the later real time of `v₁`'s and `v₂`'s ticks to the support cutoff of slot
`s + 1`: Lemma 31, which the proof calls, compares the
frame trees on the states before the support cutoff of slot `s + 1`.

Restated with the delivery premises up to `M.supportCutoff S.C s + Δ S`: Lemma 31 reads the re-sends
at the support cutoff of slot `s`, due one delay after it
(`lem31_saved_confirmations_compatible_upTo`). -/
theorem lem32_saved_confirmations_compatible_state_upTo (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s : ℕ) (v₁ v₂ : V) (C₁ C₂ : Block V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C s + Δ S)) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C s + Δ S))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- a root names one block among what honest validators hold, until the later real time of the two
    -- validators' ticks to the support cutoff of slot `s + 1`
    (hRoots : RootsNameBlocksUntil M A x (max (x.time (x.tickStep v₁ (M.supportCutoff S.C (s + 1))))
      (x.time (x.tickStep v₂ (M.supportCutoff S.C (s + 1))))))
    -- the network is synchronous from the support cutoff of slot `s` on
    (hGST : GST + max (Δ S) Δs ≤ M.viewFreeze S.C s)
    -- `v₁` is awake and honest from the duty window's start of slot `s + 1` up to its own tick to its support cutoff
    (hw₁ : v₁ ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1)))
    -- `v₂` likewise
    (hw₂ : v₂ ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1)))
    -- `v₁`'s state before `t₂ + 1` has `C₁` saved as the confirmation of slot `s`
    (hSaved₁ : (x.tickOutput v₁ (M.supportCutoff S.C (s + 1))).savedConfirmation s = some C₁)
    -- `v₂`'s state before `t₂ + 1` has `C₂` saved as the confirmation of slot `s`
    (hSaved₂ : (x.tickOutput v₂ (M.supportCutoff S.C (s + 1))).savedConfirmation s =
      some C₂) :
    -- then `C₁` and `C₂` are compatible
    C₁.compatible C₂ = true := by
  exact (GoldilocksCorrectness.Record.Proofs.Executions.lem32_saved_confirmations_compatible_state_upTo M F U)
    S A x R GST s v₁ v₂ C₁ C₂ E hNet hSkew hRedeliver Sy hΔs hRoots hGST hw₁ hw₂ hSaved₁ hSaved₂

end GoldilocksCorrectness.Record.Statements.Executions

