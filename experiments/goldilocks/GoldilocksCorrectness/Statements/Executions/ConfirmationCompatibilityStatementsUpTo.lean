module
public import GoldilocksCorrectness.Statements.Executions.ConfirmationCompatibilityStatements
public import GoldilocksCorrectness.Statements.Executions.AsyncDeliveryStatements
public import GoldilocksCorrectness.Proofs.Executions.Lemma31UpTo
public import GoldilocksCorrectness.Proofs.Executions.Lemma32UpTo

@[expose] public section

/-!
# `ConfirmationCompatibilityStatements.lean` with the delivery premises up to a bound

The theorems of
`GoldilocksCorrectness/Statements/Executions/ConfirmationCompatibilityStatements.lean` that name a
delivery premise, restated with `SynchronyFromWakeUpTo` and `CatchUpOnWakeUpTo` at a bound on the
deadlines. The bound of
each twin is the latest ordinary deadline `max t GST + Δ` of a send its proof reads, written in
the twin's own parameters.

* `lem31_saved_confirmations_compatible`, `lem32_saved_confirmations_compatible_state`

No `axiom`, no `native_decide`, no `sorry`. The landed page is imported, never edited.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ supportCutoff viewFreeze dutyWindowStart)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn expireLocks)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **Lemma 31, two honest confirmation updates of a slot save compatible blocks.** In an
execution synchronous from the support cutoff of slot `s`, the confirmation updates of slot
`s + 1`, for the slot `s`, on the states of `v₁` and `v₂` before the support cutoff of slot
`s + 1`, their expired lock entries removed, that save `C₁` and `C₂` as the confirmation of slot
`s`, save compatible blocks, when each validator is awake and honest from the support cutoff of
slot `s` to its view freeze and honest at the support cutoff of slot `s + 1`.

Why: Lemma 30. A vote resolving early at one validator was held there before the support cutoff
of slot `s`, was re-sent then, and reaches the other within one delay, while it is awake; every
pool vote before the update is stamped before it; the two frame trees hold only blocks of honest
validators, where a root names one block.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s`: the slot confirmed;
- `v₁`, `v₂`: the two validators; `A₁'`, `A₂'`: the AC states the two updates answer;
- `C₁`, `C₂`: the blocks saved.

Read aloud: in a synchronous execution from the support cutoff of slot `s`, if two validators,
each awake and honest from that cutoff for one delay and honest when the update for slot `s` runs,
have that update save `C₁` and `C₂`, then `C₁` and `C₂` are on one chain.

Roots name blocks until `supportCutoff S (s + 1)`: the proof compares the blocks of the two
frame trees on `v₁`'s and `v₂`'s states before the support cutoff of slot `s + 1`.

Restated with the delivery premises up to `supportCutoff S s + Δ S`: Lemma 62, in each direction, reads the re-sends at the support cutoff of slot `s`, due one delay after it. -/
theorem lem31_saved_confirmations_compatible_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s : ℕ) (v₁ v₂ : V) (A₁' A₂' : ACState V)
    (C₁ C₂ : Block V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S s + Δ S))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S s + Δ S))
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s + 1)))
    -- the network is synchronous from the support cutoff of slot `s` on
    (hGST : GST ≤ supportCutoff S s)
    -- `v₁` is awake and honest from the support cutoff of slot `s` to its view freeze
    (hv₁ : ∀ t : ℕ, supportCutoff S s ≤ t → t ≤ viewFreeze S s →
      v₁ ∈ Sched.awake (t : Int) ∧ v₁ ∉ Sched.adv (t : Int))
    -- `v₂` is awake and honest from the support cutoff of slot `s` to its view freeze
    (hv₂ : ∀ t : ℕ, supportCutoff S s ≤ t → t ≤ viewFreeze S s →
      v₂ ∈ Sched.awake (t : Int) ∧ v₂ ∉ Sched.adv (t : Int))
    -- `v₁` and `v₂` are honest at the support cutoff of slot `s + 1`, when the updates run
    (hHon₁ : v₁ ∉ Sched.adv (supportCutoff S (s + 1) : Int))
    (hHon₂ : v₂ ∉ Sched.adv (supportCutoff S (s + 1) : Int))
    -- the update of slot `s + 1` on `v₁`'s state before `t₂`, its expired locks removed, answers
    -- `A₁'` and saves `C₁` as the confirmation of slot `s`
    (hUpdate₁ : update_confirmation S.C S.P
        (expireLocks (stateBefore x (supportCutoff S (s + 1)) v₁).A
          ((supportCutoff S (s + 1) : ℕ) : Int))
        (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v₁).S)
        ((supportCutoff S (s + 1) : ℕ) : Int) (s + 1) = .ok A₁')
    (hSaved₁ : A₁'.saved_confirmation s = some C₁)
    -- likewise at `v₂`
    (hUpdate₂ : update_confirmation S.C S.P
        (expireLocks (stateBefore x (supportCutoff S (s + 1)) v₂).A
          ((supportCutoff S (s + 1) : ℕ) : Int))
        (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v₂).S)
        ((supportCutoff S (s + 1) : ℕ) : Int) (s + 1) = .ok A₂')
    (hSaved₂ : A₂'.saved_confirmation s = some C₂) :
    -- then `C₁` and `C₂` are compatible
    C₁.compatible C₂ = true :=
  GoldilocksCorrectness.Proofs.Executions.lem31_saved_confirmations_compatible_upTo S Sched x GST s v₁ v₂
    A₁' A₂' C₁ C₂ hDiv hMono hSync hCatch hRoots hGST hv₁ hv₂ hHon₁ hHon₂ hUpdate₁ hSaved₁
    hUpdate₂ hSaved₂

/-- **Lemma 32, the saved confirmations of two honest validators are compatible.** In an
execution synchronous from the support cutoff of slot `s`, the blocks `C₁` and `C₂` that `v₁` and
`v₂` have saved as the confirmation of slot `s` on their states before `t₂ + 1`, `t₂` the support
cutoff of slot `s + 1`, are compatible, when each validator is awake and honest from the duty
window's start of slot `s + 1` to `t₂`.

Why: the wake window makes the tick at `t₂` run the confirmation update of slot `s + 1` (Lemma
15), whose saved confirmation the state before `t₂ + 1` keeps; the window contains Lemma 31's,
since the duty window of slot `s + 1` starts no later than slot `s`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s`: the slot confirmed;
- `v₁`, `v₂`: the two validators; `C₁`, `C₂`: the blocks saved.

Read aloud: if two validators, each awake and honest from the duty window's start of slot `s + 1`
to its support cutoff, have `C₁` and `C₂` saved as their confirmation of slot `s` right after that
cutoff, then `C₁` and `C₂` are on one chain.

Roots name blocks until `supportCutoff S (s + 1)`: Lemma 31, which the proof calls, compares the
frame trees on the states before the support cutoff of slot `s + 1`.

Restated with the delivery premises up to `supportCutoff S s + Δ S`: Lemma 31 reads the re-sends at the support cutoff of slot `s`, due one delay after it (`lem31_saved_confirmations_compatible_upTo`). -/
theorem lem32_saved_confirmations_compatible_state_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s : ℕ) (v₁ v₂ : V) (C₁ C₂ : Block V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S s + Δ S))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S s + Δ S))
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s + 1)))
    -- the network is synchronous from the support cutoff of slot `s` on
    (hGST : GST ≤ supportCutoff S s)
    -- `v₁` is awake and honest from the duty window's start of slot `s + 1` to its support cutoff
    (hw₁ : ∀ t : ℕ, dutyWindowStart S (s + 1) ≤ t → t ≤ supportCutoff S (s + 1) →
      v₁ ∈ Sched.awake (t : Int) ∧ v₁ ∉ Sched.adv (t : Int))
    -- `v₂` likewise
    (hw₂ : ∀ t : ℕ, dutyWindowStart S (s + 1) ≤ t → t ≤ supportCutoff S (s + 1) →
      v₂ ∈ Sched.awake (t : Int) ∧ v₂ ∉ Sched.adv (t : Int))
    -- `v₁`'s state before `t₂ + 1` has `C₁` saved as the confirmation of slot `s`
    (hSaved₁ : (stateBefore x (supportCutoff S (s + 1) + 1) v₁).A.saved_confirmation s = some C₁)
    -- `v₂`'s state before `t₂ + 1` has `C₂` saved as the confirmation of slot `s`
    (hSaved₂ : (stateBefore x (supportCutoff S (s + 1) + 1) v₂).A.saved_confirmation s =
      some C₂) :
    -- then `C₁` and `C₂` are compatible
    C₁.compatible C₂ = true :=
  GoldilocksCorrectness.Proofs.Executions.lem32_saved_confirmations_compatible_state_upTo S Sched x GST s
    v₁ v₂ C₁ C₂ hDiv hMono hSync hCatch hRoots hGST hw₁ hw₂ hSaved₁ hSaved₂

end GoldilocksCorrectness.Statements.Executions

