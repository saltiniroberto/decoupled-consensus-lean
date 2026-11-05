import LARuns.Goldilocks.Instance
import LARuns.Goldilocks.Proofs567
import GoldilocksVariant.Final.Sync
import GoldilocksCorrectness.Record.Facts
import GoldilocksCorrectness.Record.ScheduleGoldilocks
import GoldilocksCorrectness.Record.Restated.Statements.Executions.ExecutionDefs
import GoldilocksCorrectness.Record.Restated.Statements.Executions.HealedTopStatements
import GoldilocksCorrectness.Record.Restated.Proofs.Executions.PeriodEntryDeliveryLine

/-!
# One run of Goldilocks's node read two ways: as observed, and as a trace

A run `π` of `goldilocksProtocol S` is read by the LARuns statements as observed,
`observeWithCommittees π` (each node's local state replaced by its view, with Goldilocks's
committees), and by the restated top statements as the trace `toTrace (M.initial S.C) π` with the
activity `activityOf π` (`GoldilocksVariant.Final.Projection`), at the spec's model
`M = Model.goldilocks`. The theorems here carry a premise or a conclusion from one reading to the
other:

- section 1: the conditions on the observed run that every top statement takes, and Goldilocks's
  extra condition on redelivery, read on the run itself, in the form the trace's environment facts
  take them (`GoldilocksVariant.Final.envFactsDelivery_toTrace`);
- section 2: the trace's delivery promises at the network's delays, and its sync facts at
  `servesMin` at delays the caller chooses with their relations to the run's, from those
  conditions;
- section 3: the parent-first delivery order on the trace, from Goldilocks's extra condition;
- section 4: the conclusions of Lemma 86's until form read back on the observed run: a root
  collision among blocks honest validators hold, and the compatibility of finalized blocks;
- section 5: the adversary bounds up to a time on the trace, from the weight bounds and, for the
  bound of a third, Goldilocks's extra condition `AdversaryLeavesQuorumBy`;
- section 6: the slot times of the spec (integers) and of the model (natural numbers), as reals;
- section 7: an up-and-honest window on the observed run as an active window on the trace, the
  trace's honest active validators and honest openers as the observed run's (`HonestActiveG`,
  `HonestProposerToUpdateG`), and the top statements' holder rows, tick inputs, updaters, honest round
  opening slots, awake and active validators of the phase, and hand-over ticks, read from the
  conditions on the observed run (natural times where `route-b` has them);
- section 8: the trace's delivery promises and sync facts outside an asynchronous period, for
  statement 4.
-/

set_option autoImplicit false

open scoped NNReal

namespace LARuns.GoldilocksInstance

open Goldilocks (NamedObject RootOrder Block NodeState Time)
open Goldilocks.Sts (Setup)
open GoldilocksVariant.Final (toTrace activityOf newIdx origBefore)
open GoldilocksCorrectness.Record (goldilocksFacts Model.goldilocks)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-! ## 1. The conditions, read on the run -/

section Conditions

variable {S : Setup V} [ProtocolCommittees (goldilocksProtocol S) (Block V)]
  (π : RStsVariant2.Exec (goldilocksProtocol S))

/-- The state the observed run gives `v` in configuration `i` is known exactly when the run's local
state of `v` there is known.

The variables:
- `π`: the run; `i`: the configuration; `v`: the validator. -/
theorem state_observeWithCommittees_ne_none (i : ℕ) (v : V) :
    RStsVariant2.Observable.state (observeWithCommittees (Block := Block V) π) i v ≠ none ↔
      π[i][v] ≠ none := by
  show Option.map _ (π[i][v]) ≠ none ↔ _
  cases π[i][v] <;> simp

/-- Goldilocks's extra condition on redelivery, read on the observed run, holds on the run.

Why: the condition reads the observed run's steps, clocks, sent envelopes, crashed and corrupted
sets, which are the run's, and whether a node's state is known, which is whether the run's local
state is known (`state_observeWithCommittees_ne_none`).

The variables:
- `π`: the run; `release`: the release readings; `ΔRedeliver`: the redelivery delay. -/
theorem redelivered_run {release : (m : NamedObject V) → Option ℕ} {ΔRedeliver : ℝ}
    (h : RedeliveredAfterReleaseFromDelivery release ΔRedeliver
      (observeWithCommittees (Block := Block V) π)) :
    RedeliveredAfterReleaseFromDelivery release ΔRedeliver π := by
  have hs := state_observeWithCommittees_ne_none π
  intro iSend jDeliver kAct v e tRelease tTick hD hrel hS hR hjk hT hle hN hUp
  have key := h iSend jDeliver kAct v e tRelease tTick
    ⟨hD.1, hD.2.1, (hs _ _).2 hD.2.2.1, hD.2.2.2⟩ hrel hS hR hjk hT hle hN
    (fun c hc hc' => by
      obtain ⟨h1, h2, h3⟩ := hUp c hc hc'
      exact ⟨h1, (hs _ _).2 h2, h3⟩)
  obtain ⟨j, hkj, ⟨hj1, hj2, hj3, hj4⟩, hj5, hj6⟩ := key
  exact ⟨j, hkj, ⟨hj1, hj2, (hs _ _).1 hj3, hj4⟩, hj5, hj6⟩

end Conditions

/-! ## 2. The trace's delivery promises -/

section Delivery

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject Vocab.goldilocks)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

variable {S : Setup V} [ProtocolCommittees (goldilocksProtocol S) (Block V)]
  (π : RStsVariant2.Exec (goldilocksProtocol S))

/-- **The trace's delivery promise for blocks and Goldfish votes**, at the network's delay `ΔNet`
and the time `⌈tGST⌉₊`, from the conditions every top statement takes on the observed run with
the network's deadline `syncDeadline tGST (goldilocksΔNetDelivery ΔNet ΔNet_F ΔClockAhead)` and Goldilocks's
extra condition on redelivery at `goldilocksRelease S`.

Why: `GoldilocksVariant.Final.envFactsDelivery_toTrace`, each condition read on the run
(section 1); `tGST ≤ ⌈tGST⌉₊`; a block or a Goldfish vote has the delay `ΔNet − ΔClockAhead`, at
most `ΔNet`.

The variables:
- `π`: the run; `tGST`: the time from which the network is synchronous; `dlW`: the catch-up
  deadline; `ΔClockAhead`, `ΔClockBehind`: the clock bounds; `tGAT`, `tAwakeEnd`: the healing
  phase; `H`: the healing premise; `ΔNet`, `ΔNet_F`: the network's delays; `ΔRedeliver`: the
  redelivery delay; `hC`: the conditions; `hRe`: the extra condition on redelivery. -/
theorem envFactsDelivery_of_conditions {tGST : ℝ} {dlW : (m : NamedObject V) → (t : ℝ) → ℝ}
    {ΔClockAhead ΔClockBehind : ℝ≥0} {tGAT tAwakeEnd : ℝ}
    {H : (segment : (i : ℕ) → Option (PhaseStep V (NamedObject V) (Block V))) → Prop}
    {ΔNet ΔNet_F ΔRedeliver : ℕ}
    (hC : TopStatementConditions tGST
      (RStsVariant2.syncDeadline tGST (goldilocksΔNetDelivery ΔNet ΔNet_F ΔClockAhead)) dlW ΔClockAhead
      ΔClockBehind tGAT tAwakeEnd H (observeWithCommittees (Block := Block V) π))
    (hRe : RedeliveredAfterReleaseFromDelivery (goldilocksRelease S) (ΔRedeliver : ℝ)
      (observeWithCommittees (Block := Block V) π)) :
    EnvFactsDelivery (activityOf π) (toTrace ((Model.goldilocks (V := V)).initial S.C) π)
      ΔClockAhead ΔClockBehind ΔNet ΔRedeliver ⌈tGST⌉₊ (releaseOf Model.goldilocks S.C) acObject
      Vocab.goldilocks := by
  rw [GoldilocksVariant.Final.releaseOf_goldilocks]
  refine GoldilocksVariant.Final.envFactsDelivery_toTrace (M := Model.goldilocks) goldilocksFacts π
    ΔClockAhead.2 ΔClockBehind.2 hC.tickOnce hC.clockWithinSkew
    ((RStsVariant2.clockAdvancesWithin_observe NodeViewOf.view π _ _).1 hC.clockAdvances)
    ((RStsVariant2.ticksWithin_observe NodeViewOf.view π _).1 hC.ticksWithin) hC.actsWithinSkew hC.unforgeable
    ((RStsVariant2.deliveredBeforeActingG_observe NodeViewOf.view π RStsVariant2.TickStepG
      RStsVariant2.TickStepG (fun _ _ => Iff.rfl) _).1 hC.delivered)
    (redelivered_run π hRe) (Nat.le_ceil tGST) ?_
  intro m hm
  cases m <;> simp_all [goldilocksΔNetDelivery, acObject]

/-- **The trace's delivery promise for attestations**, at the network's delay `ΔNet_F` and the
time `⌈tGST⌉₊`, from the same conditions as `envFactsDelivery_of_conditions`.

Why: as `envFactsDelivery_of_conditions`; an attestation has the delay `ΔNet_F`.

The variables: as for `envFactsDelivery_of_conditions`. -/
theorem envFactsDelivery_F_of_conditions {tGST : ℝ} {dlW : (m : NamedObject V) → (t : ℝ) → ℝ}
    {ΔClockAhead ΔClockBehind : ℝ≥0} {tGAT tAwakeEnd : ℝ}
    {H : (segment : (i : ℕ) → Option (PhaseStep V (NamedObject V) (Block V))) → Prop}
    {ΔNet ΔNet_F ΔRedeliver : ℕ}
    (hC : TopStatementConditions tGST
      (RStsVariant2.syncDeadline tGST (goldilocksΔNetDelivery ΔNet ΔNet_F ΔClockAhead)) dlW ΔClockAhead
      ΔClockBehind tGAT tAwakeEnd H (observeWithCommittees (Block := Block V) π))
    (hRe : RedeliveredAfterReleaseFromDelivery (goldilocksRelease S) (ΔRedeliver : ℝ)
      (observeWithCommittees (Block := Block V) π)) :
    EnvFactsDelivery (activityOf π) (toTrace ((Model.goldilocks (V := V)).initial S.C) π)
      ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver ⌈tGST⌉₊ (releaseOf Model.goldilocks S.C) fgObject
      Vocab.goldilocks := by
  rw [GoldilocksVariant.Final.releaseOf_goldilocks]
  refine GoldilocksVariant.Final.envFactsDelivery_toTrace (M := Model.goldilocks) goldilocksFacts π
    ΔClockAhead.2 ΔClockBehind.2 hC.tickOnce hC.clockWithinSkew
    ((RStsVariant2.clockAdvancesWithin_observe NodeViewOf.view π _ _).1 hC.clockAdvances)
    ((RStsVariant2.ticksWithin_observe NodeViewOf.view π _).1 hC.ticksWithin) hC.actsWithinSkew hC.unforgeable
    ((RStsVariant2.deliveredBeforeActingG_observe NodeViewOf.view π RStsVariant2.TickStepG
      RStsVariant2.TickStepG (fun _ _ => Iff.rfl) _).1 hC.delivered)
    (redelivered_run π hRe) (Nat.le_ceil tGST) ?_
  intro m hm
  cases m <;> simp_all [goldilocksΔNetDelivery, fgObject]

open GoldilocksCorrectness.Statements.AbstractTrace (SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

/-- **The trace's sync fact for blocks and Goldfish votes** (`SyncedWithin` at `servesMin`), at the
trace's delay `ΔNet`, catch-up delay `Δs`, sync delay `Δs_tr` and time `GST`, from the conditions
every top statement takes on the observed run with the network's deadlines `syncDeadline tGST
(goldilocksΔNetDelivery ΔNet ΔNet_F ΔClockAhead)` and `syncDeadline tGST (goldilocksΔSyncCatchUp Δs
Δs_F ΔClockAhead)`, and Goldilocks's extra condition on redelivery, when `tGST ≤ GST`,
`ΔNet + ΔClockAhead ≤ Δs_tr` and `max ΔNet Δs ≤ Δs_tr`.

Why: `GoldilocksVariant.Final.syncedWithin_toTrace` at the trace's delays `ΔNet` and `Δs`, each
condition read on the run (section 1); a block or a Goldfish vote has the run's delay
`ΔNet − ΔClockAhead` and catch-up delay `Δs − ΔClockAhead`.

The variables:
- `π`: the run; the others as for `envFactsDelivery_of_conditions`, and `Δs`, `Δs_F`: the catch-up
  delays; `Δs_tr`, `GST`: the trace's sync delay and time; `htGST`, `hΔA`, `hΔs`: the relations. -/
theorem syncedWithin_of_conditions
    {tGST : ℝ} {ΔClockAhead ΔClockBehind : ℝ≥0} {tGAT tAwakeEnd : ℝ}
    {H : (segment : (i : ℕ) → Option (PhaseStep V (NamedObject V) (Block V))) → Prop}
    {ΔNet ΔNet_F ΔRedeliver Δs Δs_F Δs_tr GST : ℕ}
    (hC : TopStatementConditions tGST
      (RStsVariant2.syncDeadline tGST (goldilocksΔNetDelivery ΔNet ΔNet_F ΔClockAhead))
      (RStsVariant2.syncDeadline tGST (goldilocksΔSyncCatchUp Δs Δs_F ΔClockAhead)) ΔClockAhead
      ΔClockBehind tGAT tAwakeEnd H (observeWithCommittees (Block := Block V) π))
    (hRe : RedeliveredAfterReleaseFromDelivery (goldilocksRelease S) (ΔRedeliver : ℝ)
      (observeWithCommittees (Block := Block V) π))
    (htGST : tGST ≤ GST) (hΔA : (ΔNet : ℝ) + ΔClockAhead ≤ Δs_tr)
    (hΔs : max ΔNet Δs ≤ Δs_tr) :
    SyncedWithin (activityOf π) (toTrace ((Model.goldilocks (V := V)).initial S.C) π)
      (servesMin Model.goldilocks S.C) acObject (releaseOf Model.goldilocks S.C) ΔRedeliver Δs_tr
      GST := by
  refine GoldilocksVariant.Final.syncedWithin_toTrace (M := Model.goldilocks) goldilocksFacts
    GoldilocksCorrectness.Record.uniformSchedule_goldilocks π
    ΔClockAhead.2 ΔClockBehind.2 hC.tickOnce hC.clockWithinSkew
    ((RStsVariant2.clockAdvancesWithin_observe NodeViewOf.view π _ _).1 hC.clockAdvances)
    ((RStsVariant2.ticksWithin_observe NodeViewOf.view π _).1 hC.ticksWithin) hC.actsWithinSkew
    hC.unforgeable
    ((RStsVariant2.deliveredBeforeActingG_observe NodeViewOf.view π RStsVariant2.TickStepG
      RStsVariant2.TickStepG (fun _ _ => Iff.rfl) _).1 hC.delivered)
    ((RStsVariant2.catchUpAfterRestartG_observe NodeViewOf.view π RStsVariant2.TickStepG
      RStsVariant2.TickStepG (fun _ _ => Iff.rfl) _ _).1 hC.catchUp)
    (by rw [GoldilocksVariant.Final.releaseOf_goldilocks]; exact redelivered_run π hRe)
    (Δ := ΔNet) (Δw := Δs) htGST ?_ ?_ hΔA hΔs
  · intro m hm
    cases m <;> simp_all [goldilocksΔNetDelivery, acObject]
  · intro m hm
    cases m <;> simp_all [goldilocksΔSyncCatchUp, acObject]

/-- **The trace's sync fact for attestations** (`SyncedWithin` at `servesMin` and `fgObject`), at
the trace's delays `ΔNet_F`, `Δs_F`, `Δs_F_tr` and time `GST`, from the same conditions as
`syncedWithin_of_conditions`, when `tGST ≤ GST`, `ΔNet_F + ΔClockAhead ≤ Δs_F_tr` and
`max ΔNet_F Δs_F ≤ Δs_F_tr`.

Why: `GoldilocksVariant.Final.syncedWithin_F_toTrace`, as for `syncedWithin_of_conditions`; an
attestation has the run's delay `ΔNet_F − ΔClockAhead` and catch-up delay `Δs_F − ΔClockAhead`.

The variables: as for `syncedWithin_of_conditions`, at the attestations' delays. -/
theorem syncedWithin_F_of_conditions
    {tGST : ℝ} {ΔClockAhead ΔClockBehind : ℝ≥0} {tGAT tAwakeEnd : ℝ}
    {H : (segment : (i : ℕ) → Option (PhaseStep V (NamedObject V) (Block V))) → Prop}
    {ΔNet ΔNet_F ΔRedeliver Δs Δs_F Δs_F_tr GST : ℕ}
    (hC : TopStatementConditions tGST
      (RStsVariant2.syncDeadline tGST (goldilocksΔNetDelivery ΔNet ΔNet_F ΔClockAhead))
      (RStsVariant2.syncDeadline tGST (goldilocksΔSyncCatchUp Δs Δs_F ΔClockAhead)) ΔClockAhead
      ΔClockBehind tGAT tAwakeEnd H (observeWithCommittees (Block := Block V) π))
    (hRe : RedeliveredAfterReleaseFromDelivery (goldilocksRelease S) (ΔRedeliver : ℝ)
      (observeWithCommittees (Block := Block V) π))
    (htGST : tGST ≤ GST) (hΔA : (ΔNet_F : ℝ) + ΔClockAhead ≤ Δs_F_tr)
    (hΔs : max ΔNet_F Δs_F ≤ Δs_F_tr) :
    SyncedWithin (activityOf π) (toTrace ((Model.goldilocks (V := V)).initial S.C) π)
      (servesMin Model.goldilocks S.C) fgObject (releaseOf Model.goldilocks S.C) ΔRedeliver
      Δs_F_tr GST := by
  refine GoldilocksVariant.Final.syncedWithin_F_toTrace (M := Model.goldilocks) goldilocksFacts
    π
    ΔClockAhead.2 ΔClockBehind.2 hC.tickOnce hC.clockWithinSkew
    ((RStsVariant2.clockAdvancesWithin_observe NodeViewOf.view π _ _).1 hC.clockAdvances)
    ((RStsVariant2.ticksWithin_observe NodeViewOf.view π _).1 hC.ticksWithin) hC.actsWithinSkew
    hC.unforgeable
    ((RStsVariant2.deliveredBeforeActingG_observe NodeViewOf.view π RStsVariant2.TickStepG
      RStsVariant2.TickStepG (fun _ _ => Iff.rfl) _).1 hC.delivered)
    ((RStsVariant2.catchUpAfterRestartG_observe NodeViewOf.view π RStsVariant2.TickStepG
      RStsVariant2.TickStepG (fun _ _ => Iff.rfl) _ _).1 hC.catchUp)
    (by rw [GoldilocksVariant.Final.releaseOf_goldilocks]; exact redelivered_run π hRe)
    (Δ_F := ΔNet_F) (Δw_F := Δs_F) htGST ?_ ?_ hΔA hΔs
  · intro m hm
    cases m <;> simp_all [goldilocksΔNetDelivery, fgObject]
  · intro m hm
    cases m <;> simp_all [goldilocksΔSyncCatchUp, fgObject]

end Delivery

/-! ## 3. The parent-first delivery order on the trace -/

section Parent

variable {S : Setup V} [ProtocolCommittees (goldilocksProtocol S) (Block V)]
  (π : RStsVariant2.Exec (goldilocksProtocol S))

/-- **The parent-first delivery order on the trace**, from Goldilocks's extra condition
`ParentHeldAtDelivery` on the observed run.

Why: a delivery on the trace is the run's delivery of an envelope with the same signed message to
a validator up and honest (`exists_of_lbl_deliver`), whose node state on the trace is its local
state's memory state in the run's configuration, read on the observed run through its view, whose
finalized block and tree are the node state's.

The variables:
- `π`: the run; `h`: the extra condition. -/
theorem parentHeld_toTrace
    (h : ParentHeldAtDelivery (observeWithCommittees (Block := Block V) π)) :
    GoldilocksCorrectness.Record.Statements.Executions.ParentHeldAtDelivery Model.goldilocks
      (toTrace ((Model.goldilocks (V := V)).initial S.C) π) := by
  intro j v sm B hl hm hB hc
  obtain ⟨k, e, rfl, hlk, hsm, -, hs, -⟩ :=
    GoldilocksVariant.Final.exists_of_lbl_deliver _ π hl
  obtain ⟨l, hl'⟩ := Option.ne_none_iff_exists'.mp hs
  have hst : (toTrace ((Model.goldilocks (V := V)).initial S.C) π).st (newIdx π k) v = l.st :=
    (GoldilocksVariant.Final.toTrace_st_newIdx _ π k v).trans
      (GoldilocksVariant.Final.lastKnownSt_of_some _ π hl')
  rw [hst] at hc ⊢
  have he : e.msg = NamedObject.block B := by rw [← hm, ← hsm]; rfl
  exact h k v e B (NodeViewOf.view l.st) hlk (Option.map_eq_some_iff.mpr ⟨l, hl', rfl⟩) he hB hc

end Parent

/-! ## 4. The conclusions of Lemma 86's until form, read on the observed run -/

section Conclusions

open GoldilocksCorrectness.Record.Statements.Executions (RootCollisionHeldBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)

variable {S : Setup V} [ProtocolCommittees (goldilocksProtocol S) (Block V)]
  (π : RStsVariant2.Exec (goldilocksProtocol S))

omit [ProtocolCommittees (goldilocksProtocol S) (Block V)] in
/-- A block in `v`'s tree on the trace right after a step at a time at most `tBy` is the genesis
block, or is in the tree of a local state of `v` known in a configuration of the run entered at a
time at most `tBy`, with `v` outside the corrupted set there.

Why: the trace's node state after `j + 1` steps is `v`'s initial state, whose tree is
`{genesis}`, or the memory state of a local state of `v` known in a configuration `m` at most the
one the trace reads (`lastKnownSt_cases`); that configuration is entered by the time of step `j`
(the configuration the trace reads after `j + 1` steps is entered by then); a validator whose local
state is known is not corrupted (`getElem_eq_none_of_mem_adv`).

The variables:
- `π`: the run; `tBy`: the time; `j`: the trace step; `v`: the validator; `B`: the block. -/
theorem held_on_run {tBy : ℝ} {j : ℕ} {v : V} {B : Block V}
    (hj : (toTrace ((Model.goldilocks (V := V)).initial S.C) π).time j ≤ tBy)
    (hB : B ∈ ((toTrace ((Model.goldilocks (V := V)).initial S.C) π).st (j + 1) v).S.T) :
    B = Block.genesis ∨
      ∃ (m : ℕ) (l : RStsVariant2.Local V (NamedObject V) (NodeState V)),
        π[m][v] = some l ∧ v ∉ π[m].adv ∧ π.stamp m ≤ tBy ∧ B ∈ l.st.S.T := by
  have hentry : π.stamp (origBefore π (j + 1)) ≤ tBy := by
    rcases GoldilocksVariant.Final.newIdx_or_other (NodeState := NodeState V)
        (fun w => (Model.goldilocks (V := V)).initial S.C w) π j with ⟨k, hk⟩ | ⟨-, he⟩
    · have h1 : origBefore π (j + 1) = k + 1 := by
        rw [← hk]; exact GoldilocksVariant.Final.origBefore_newIdx_succ π k
      have h2 : (toTrace ((Model.goldilocks (V := V)).initial S.C) π).time (newIdx π k) =
          π.stamp (k + 1) := GoldilocksVariant.Final.toTrace_time_newIdx _ π k
      rw [h1]
      exact h2.symm.trans_le (hk ▸ hj)
    · have h1 : π.stamp (origBefore π j) ≤
          (toTrace ((Model.goldilocks (V := V)).initial S.C) π).time j :=
        (GoldilocksVariant.Final.toTrace_time_mem _ π j).1
      rw [he]
      exact h1.trans hj
  have hB₀ : B ∈ (GoldilocksVariant.Final.lastKnownSt (NodeState := NodeState V)
      (fun w => (Model.goldilocks (V := V)).initial S.C w) π (origBefore π (j + 1)) v).S.T := hB
  rcases lastKnownSt_cases (N := NodeState V) (fun w => (Model.goldilocks (V := V)).initial S.C w) π
      (origBefore π (j + 1)) v with h0 | ⟨m, l, hm, hl, he⟩
  · left
    rw [h0] at hB₀
    have hT0 : ((Model.goldilocks (V := V)).initial S.C v).tree = {Block.genesis} :=
      goldilocksFacts.init.initial_tree S.C v
    have hB' : B ∈ ((Model.goldilocks (V := V)).initial S.C v).tree := hB₀
    rwa [hT0, Finset.mem_singleton] at hB'
  · right
    rw [he] at hB₀
    refine ⟨m, l, hl, fun hadv => ?_, (π.stamp_mono hm).trans hentry, hB₀⟩
    rw [π.getElem_eq_none_of_mem_adv m v hadv] at hl
    exact absurd hl (by simp)

omit [ProtocolCommittees (goldilocksProtocol S) (Block V)] in
/-- The genesis block is in the tree of every local state the run knows.

Why: the trace's node state at the step `newIdx π m` is that local state's memory state, and every
node state of the trace has the genesis block in its tree (`lem11_node_invariantCore_of_run`, with
the trace's run facts `runFacts_toTrace`).

The variables:
- `π`: the run; `m`: the configuration; `v`: the validator; `l`: its local state. -/
theorem genesis_mem_of_known {m : ℕ} {v : V} {l : RStsVariant2.Local V (NamedObject V) (NodeState V)}
    (hl : π[m][v] = some l) : Block.genesis ∈ l.st.S.T := by
  have R : RunFacts Model.goldilocks S (toTrace ((Model.goldilocks (V := V)).initial S.C) π) :=
    GoldilocksVariant.Final.runFacts_toTrace goldilocksFacts π
  have h := (goldilocksFacts.nd.nodeInvCore_treeClosed
    ((GoldilocksCorrectness.Record.Proofs.Executions.lem11_node_invariantCore_of_run
      (Model.goldilocks (V := V)) goldilocksFacts) S _ R (newIdx π m) v).1).1
  have hst : (toTrace ((Model.goldilocks (V := V)).initial S.C) π).st (newIdx π m) v = l.st :=
    (GoldilocksVariant.Final.toTrace_st_newIdx _ π m v).trans
      (GoldilocksVariant.Final.lastKnownSt_of_some _ π hl)
  rw [hst] at h
  exact h

/-- A local state of `v` known in a configuration of the run entered by `tBy`, with `v` outside the
corrupted set there and `B` in its tree, puts `B` in an honest node's tree by `tBy` on the observed
run.

The variables:
- `π`: the run; `tBy`: the time; `m`: the configuration; `v`: the validator; `l`: its local
  state; `B`: the block. -/
theorem inHonestTreeByG_of_known {tBy : ℝ} {m : ℕ} {v : V}
    {l : RStsVariant2.Local V (NamedObject V) (NodeState V)} {B : Block V}
    (hl : π[m][v] = some l) (hadv : v ∉ π[m].adv) (hm : π.stamp m ≤ tBy) (hB : B ∈ l.st.S.T) :
    letI : RStsVariant2.BlockTree (NodeView (Block V)) (Block V) := ⟨fun w => (NodeViewOf.view w).T⟩
    RStsVariant2.InHonestTreeByG (observeWithCommittees (Block := Block V) π) tBy B :=
  ⟨m, v, NodeViewOf.view l.st, Option.map_eq_some_iff.mpr ⟨l, hl, rfl⟩, hadv, hm, hB⟩

/-- **A root collision among blocks honest validators hold on the trace by `n` is a root collision
by `n` on the observed run** (`RootCollisionBy`).

Why: each of the two blocks is the genesis block or is in the tree of a local state known by `n`
with its validator honest (`held_on_run`); they are distinct, so at most one is the genesis block,
and the genesis block is in the other's tree (`genesis_mem_of_known`).

The variables:
- `π`: the run; `n`: the time; `h`: the collision. -/
theorem rootCollisionBy_of_heldBy (n : ℕ)
    (h : RootCollisionHeldBy Model.goldilocks S (activityOf π)
      (toTrace ((Model.goldilocks (V := V)).initial S.C) π) n) :
    RootCollisionBy (observeWithCommittees (Block := Block V) π) (n : ℝ) := by
  obtain ⟨B, B', ⟨j, v, -, hj, hB⟩, ⟨j', v', -, hj', hB'⟩, hr, hne⟩ :=
    ((GoldilocksCorrectness.Record.Proofs.View.rootCollisionHeldBy_unfold
      (Model.goldilocks (V := V)) (S := S) (A := activityOf π) _ n).1 h)
  refine ⟨B, B', ?_, ?_, hr, hne⟩
  · rcases held_on_run π hj hB with hg | ⟨m, l, hl, hadv, hm, hBl⟩
    · rcases held_on_run π hj' hB' with hg' | ⟨m', l', hl', hadv', hm', -⟩
      · exact absurd (hg.trans hg'.symm) hne
      · exact Or.inl (hg ▸ inHonestTreeByG_of_known π hl' hadv' hm' (genesis_mem_of_known π hl'))
    · exact Or.inl (inHonestTreeByG_of_known π hl hadv hm hBl)
  · rcases held_on_run π hj' hB' with hg' | ⟨m', l', hl', hadv', hm', hBl'⟩
    · rcases held_on_run π hj hB with hg | ⟨m, l, hl, hadv, hm, -⟩
      · exact absurd (hg.trans hg'.symm) hne
      · exact Or.inl (hg' ▸ inHonestTreeByG_of_known π hl hadv hm (genesis_mem_of_known π hl))
    · exact Or.inl (inHonestTreeByG_of_known π hl' hadv' hm' hBl')

open GoldilocksCorrectness.Record.Proofs.Executions in
omit [ProtocolCommittees (goldilocksProtocol S) (Block V)] in
/-- **An honest proposal is not in its proposer's tree before the tick that proposes it.** On a
trace with the run's facts `R` and the environment's facts `E`, a block `B` that the proposer of
slot `s` puts on the wire at its tick to the start of slot `s` (`ProposalAt`) is not in the
proposer's tree in the state that tick starts from (`x.tickInput`).

Why: the tick's block has slot `s`, and `s` is not `0` (Lemma 19, `lem19_tick_proposes`). If the
proposer held `B` before the tick, its own relay of `B` came at an earlier step
(`tree_block_relayed`), and `B`'s author is the proposer of slot `s`; that author is honest up to
the tick, so `B` was first put on the wire by one of its ticks (`authored_from_own_tick`), at an
earlier step; Lemma 19 makes that tick's clock value the start of slot `s`, and a validator ticks
to one clock value at one step only (`tick_unique`), a contradiction.

The variables:
- `x`: the trace; `A`: its activity; `R`: the run's facts; `E`: the environment's facts; `s`: the
  slot; `B`: the proposal.

Read aloud: an honest proposer does not hold its proposal before it proposes it. -/
theorem proposal_not_mem_tickInput
    {x : GoldilocksCorrectness.Statements.AbstractTrace.Trace V (NamedObject V)
      (Model.goldilocks (V := V)).N}
    {A : GoldilocksCorrectness.Statements.AbstractTrace.Activity V}
    (R : RunFacts Model.goldilocks S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy A x ΔClockAhead ΔClockBehind
      deadline release ΔRedeliver GoldilocksCorrectness.Statements.Executions.acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {s : ℕ} {B : Block V}
    (hP : GoldilocksCorrectness.Record.Statements.Executions.ProposalAt Model.goldilocks S x s B) :
    B ∉ (x.tickInput (S.P.proposer s) ((Model.goldilocks (V := V)).slotStart S.C s)).tree := by
  intro hB
  obtain ⟨k, hl, hm⟩ := hP
  have hts := (tickStep_eq_of_lbl Model.goldilocks) x E hl
  have hti : x.tickInput (S.P.proposer s) ((Model.goldilocks (V := V)).slotStart S.C s) =
      x.st k (S.P.proposer s) := by
    unfold GoldilocksCorrectness.Statements.AbstractTrace.Trace.tickInput; rw [hts]
  rw [hti] at hB
  have hp : S.P.proposer s ∉ A.corrupted k := E.not_mem_corrupted_of_tick hl
  -- the proposing tick: `B` has slot `s`, and `s` is not `0`
  obtain ⟨-, n0, sent0, hrun0, hmem0⟩ := (tick_send_of_honestSendAt Model.goldilocks goldilocksFacts R E) hl hm
  have hInv0 : (Model.goldilocks (V := V)).nodeInv S.C S.P S.X (x.st k (S.P.proposer s)) :=
    (lem11_node_invariant Model.goldilocks goldilocksFacts S A x R E k _ hp).1
  rw [← hti] at hInv0
  obtain ⟨hpos, -, -, -, H, votes, sv, -, -, -, hBeq⟩ :=
    (GoldilocksCorrectness.Record.Statements.Routines.lem19_tick_proposes goldilocksFacts) S.C S.P S.X _
      n0 _ sent0 B hrun0 hInv0 hmem0
  have hΔ := GoldilocksCorrectness.Proofs.Routines.one_le_Δ S
  have hss : (Model.goldilocks (V := V)).slotStart S.C (s + 1) =
      (Model.goldilocks (V := V)).slotStart S.C s + 4 * GoldilocksCorrectness.Statements.Routines.Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq Model.goldilocks.toSlotLayout
        goldilocksFacts.sched GoldilocksCorrectness.Record.uniformSchedule_goldilocks),
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq Model.goldilocks.toSlotLayout
        goldilocksFacts.sched GoldilocksCorrectness.Record.uniformSchedule_goldilocks) S s,
      Nat.mul_add, Nat.mul_one]
  have hsl : S.C.slot (((Model.goldilocks (V := V)).slotStart S.C s : ℕ) : Int) = s := by
    rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast,
      ← (GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast Model.goldilocks.toSlotLayout
        goldilocksFacts.sched GoldilocksCorrectness.Record.uniformSchedule_goldilocks)]
    exact (GoldilocksCorrectness.Record.Proofs.Routines.slot_eq_of_mem Model.goldilocks.toSlotLayout
      goldilocksFacts.sched) S (le_refl _) (by omega)
  rw [hsl] at hpos hBeq
  have hslotB : B.slot = s := by rw [hBeq]; rfl
  have hg : B ≠ Block.genesis := by
    rintro rfl
    exact (Nat.pos_iff_ne_zero.mp hpos) hslotB.symm
  -- `B` in the proposer's tree before the tick came with the proposer's own relay before it
  obtain ⟨i, hi, hsendw, -, -⟩ :=
    (tree_block_relayed Model.goldilocks goldilocksFacts) x R E (k := k) hB hg
  have hprop := ((goldilocksFacts.nd.nodeInvCore_treeClosed
    ((lem11_node_invariantCore_of_run Model.goldilocks goldilocksFacts) S x R k
      (S.P.proposer s)).1).2 B hB hg).2.2.1
  rw [hslotB] at hprop
  have hauth : GoldilocksCorrectness.Statements.Executions.author (NamedObject.block B) =
      some (S.P.proposer s) := hprop
  have hH : x.HonestThrough A (i + 1) (S.P.proposer s) := fun i' hi' =>
    E.not_mem_corrupted_of_le (le_trans hi' (by omega : i + 1 ≤ k)) hp
  have hm' := (sent_unforgeable Model.goldilocks goldilocksFacts) R E (i + 1) _ (NamedObject.block B)
    (S.P.proposer s) ((mem_sent_of_mem_sub Model.goldilocks goldilocksFacts) x hsendw) (Or.inl rfl)
    hauth hH
  -- the first send of `B` is a tick of the proposer before `k`, to the start of slot `s`
  obtain ⟨k', hk', t'', hl', hdiff⟩ :=
    (authored_from_own_tick Model.goldilocks goldilocksFacts) x R E hauth hm' hH
  obtain ⟨-, n1, sent1, hrun1, hmem1⟩ :=
    (tick_send_of_honestSendAt Model.goldilocks goldilocksFacts R E) hl' hdiff
  have hInvT : (Model.goldilocks (V := V)).nodeInv S.C S.P S.X (x.tickInput (S.P.proposer s) t'') := by
    rw [show x.tickInput (S.P.proposer s) t'' = x.st k' (S.P.proposer s) by
      unfold GoldilocksCorrectness.Statements.AbstractTrace.Trace.tickInput
      rw [(tickStep_eq_of_lbl Model.goldilocks) x E hl']]
    exact (lem11_node_invariant Model.goldilocks goldilocksFacts S A x R E k' _
      (E.not_mem_corrupted_of_tick hl')).1
  obtain ⟨-, ht'', -, -, H', votes', sv', -, -, -, hB1eq⟩ :=
    (GoldilocksCorrectness.Record.Statements.Routines.lem19_tick_proposes goldilocksFacts) S.C S.P S.X _
      n1 _ sent1 B hrun1 hInvT hmem1
  have hsl' : S.C.slot (t'' : Int) = s := by
    rw [← hslotB, hB1eq]
    rfl
  have htt : t'' = (Model.goldilocks (V := V)).slotStart S.C s := by
    have h := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_cast Model.goldilocks.toSlotLayout
      goldilocksFacts.sched GoldilocksCorrectness.Record.uniformSchedule_goldilocks) S s
    rw [hsl'] at ht''
    exact_mod_cast ht''.trans h.symm
  subst htt
  have := E.tick_unique k' k _ _ hl' hl
  omega

omit [Fintype V] [RootOrder] [ProtocolCommittees (goldilocksProtocol S) (Block V)] in
/-- A signed message new in the sent log read through `traceMsg` after a step is `traceMsg` of an
envelope new in the sent log after that step, when the sent log only grows.

The variables:
- `a`, `b`: the sent logs before and after; `hab`: `a` is contained in `b`; `sm`: the signed
  message.

Read aloud: what a step adds to the sent log, read as signed messages, is what it adds as envelopes,
read as signed messages. -/
theorem exists_envelope_of_mem_map_sub {N : Type} [DecidableEq N]
    {a b : Multiset (RStsVariant2.Envelope V N)}
    (hab : a ≤ b) {sm : Framework.StsMultisetLog.SignedMsg V N}
    (h : sm ∈ b.map GoldilocksVariant.Final.traceMsg - a.map GoldilocksVariant.Final.traceMsg) :
    ∃ e ∈ b - a, GoldilocksVariant.Final.traceMsg e = sm := by
  obtain ⟨c, rfl⟩ := Multiset.le_iff_exists_add.1 hab
  rw [Multiset.map_add, add_tsub_cancel_left] at h
  rw [add_tsub_cancel_left]
  exact Multiset.mem_map.1 h

open GoldilocksCorrectness.Record.Proofs.Executions in
open GoldilocksCorrectness.Proofs.Executions (r_lt_of_lt_of_mono) in
/-- **A root collision at an honest round opening slot on the trace is a root collision by `t` on the
observed run** (`RootCollisionBy`), statement 1's conclusion `RootCollisionAtOpening` read back:
with the honest round opening slots of the rounds `r 0 < … < r m` (`HonestOpeningSeq`, its ticks to a
clock value at most the last opening's support cutoff at real times at most `tLast`) and
`tLast ≤ t`.

Why: the collision gives an opening `i ≤ m`, a proposal `B` of its first slot `s := r i * R`, put on
the wire at the proposer's tick to the start of `s`, and a block `B'` with `B`'s root in the
proposer's tree in the state that tick starts from (`rootCollisionAtOpening_unfold`,
`rootCollisionAtProposal_unfold`). That tick is a step `k₀` of the run (`exists_of_lbl_tick`); its
clock value, the start of `s`, is at most the support cutoff of `r m * R`, so its real time
`π.stamp (k₀ + 1)` is at most `tLast` (`HonestOpeningSeq.lastTick`). In configuration `k₀` the
proposer's local state is known, so the proposer is honest there, and its memory state is the
trace's state at the tick: `B'` is in an honest node's tree by `t`. The tick's new envelope with `B`
is signed by the proposer: `B` was sent by an honest node by `t`. The two blocks differ: the
proposal is not in the proposer's tree before its tick (`proposal_not_mem_tickInput`).

The variables:
- `π`: the run; `E`: the environment's facts on the trace; `r`, `m`: the honest round opening slots'
  rounds and the index of the last; `tFirst`, `tLast`: `HonestOpeningSeq`'s times; `t`: the time;
  `ht`: `tLast ≤ t`; `h`: the collision on the trace.

Read aloud: if an honest round opening slot's proposal has the root of a block its proposer
already held, then by `t` two distinct blocks with one root were each held or sent by an honest
node. -/
theorem rootCollisionBy_of_atOpening
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy (activityOf π)
      (toTrace ((Model.goldilocks (V := V)).initial S.C) π) ΔClockAhead ΔClockBehind
      deadline release ΔRedeliver GoldilocksCorrectness.Statements.Executions.acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {r : ℕ → ℕ} {m tFirst tLast : ℕ}
    (hSeq : GoldilocksCorrectness.Record.Statements.Executions.HonestOpeningSeq Model.goldilocks S
      (activityOf π) (toTrace ((Model.goldilocks (V := V)).initial S.C) π) r m tFirst tLast)
    {t : ℝ} (ht : (tLast : ℝ) ≤ t)
    (h : GoldilocksCorrectness.Record.Statements.Executions.RootCollisionAtOpening Model.goldilocks S
      (activityOf π) (toTrace ((Model.goldilocks (V := V)).initial S.C) π) r m) :
    RootCollisionBy (observeWithCommittees (Block := Block V) π) t := by
  have R := GoldilocksVariant.Final.runFacts_toTrace goldilocksFacts π
  obtain ⟨i, hi, B, hP, hC⟩ :=
    (GoldilocksCorrectness.Record.Proofs.View.rootCollisionAtOpening_unfold Model.goldilocks _ r m).1 h
  rw [GoldilocksCorrectness.Record.Proofs.View.rootCollisionAtProposal_unfold] at hC
  obtain ⟨B', hB', hroot⟩ := hC
  have hne : B' ≠ B := fun hBB => proposal_not_mem_tickInput R E hP (hBB ▸ hB')
  obtain ⟨k, hl, hm⟩ := hP
  have hts := (tickStep_eq_of_lbl Model.goldilocks) _ E hl
  have hti : (toTrace ((Model.goldilocks (V := V)).initial S.C) π).tickInput
      (S.P.proposer (r i * S.C.R)) ((Model.goldilocks (V := V)).slotStart S.C (r i * S.C.R)) =
      (toTrace ((Model.goldilocks (V := V)).initial S.C) π).st k (S.P.proposer (r i * S.C.R)) := by
    unfold GoldilocksCorrectness.Statements.AbstractTrace.Trace.tickInput; rw [hts]
  rw [hti] at hB'
  obtain ⟨k₀, rfl, hl₀, -⟩ := GoldilocksVariant.Final.exists_of_lbl_tick _ π hl
  -- the tick's real time is at most `tLast`: its clock value is at most the last opening's cutoff
  have hrr : r i ≤ r m := by
    rcases Nat.lt_or_ge i m with him | him
    · exact le_of_lt (r_lt_of_lt_of_mono r m hSeq.mono i m him le_rfl)
    · rw [show i = m by omega]
  have hle : (Model.goldilocks (V := V)).slotStart S.C (r i * S.C.R) ≤
      (Model.goldilocks (V := V)).supportCutoff S.C (r m * S.C.R) := by
    have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono
      Model.goldilocks.toSlotLayout goldilocksFacts.sched) S (Nat.mul_le_mul_right S.C.R hrr)
    have h2 := (GoldilocksCorrectness.Record.Proofs.Routines.times_le
      Model.goldilocks.toSlotLayout goldilocksFacts.sched) S (r m * S.C.R)
    omega
  have htime := hSeq.lastTick _ _ _ hl hle
  rw [show (toTrace ((Model.goldilocks (V := V)).initial S.C) π).time (newIdx π k₀) = π.stamp (k₀ + 1)
    from GoldilocksVariant.Final.toTrace_time_newIdx _ π k₀] at htime
  have hstamp : π.stamp (k₀ + 1) ≤ t := le_trans htime ht
  -- the proposer's local state at the tick
  have hs := π.step_at k₀
  rw [hl₀] at hs
  obtain ⟨l, -, hlk, -⟩ := RStsVariant2.nodeSpec_enabled_known (Pr := goldilocksProtocol S)
    (v := S.P.proposer (r i * S.C.R)) (na := .tick) (c := π[k₀]) hs.1
  have hadv : S.P.proposer (r i * S.C.R) ∉ π[k₀].adv := fun hv => by
    rw [π.getElem_eq_none_of_mem_adv k₀ _ hv] at hlk
    exact absurd hlk (by simp)
  have hst : (toTrace ((Model.goldilocks (V := V)).initial S.C) π).st (newIdx π k₀)
      (S.P.proposer (r i * S.C.R)) = l.st :=
    (GoldilocksVariant.Final.toTrace_st_newIdx _ π k₀ _).trans
      (GoldilocksVariant.Final.lastKnownSt_of_some _ π hlk)
  rw [hst] at hB'
  -- the proposal, as an envelope the tick put on the wire
  rw [show (toTrace ((Model.goldilocks (V := V)).initial S.C) π).sent (newIdx π k₀ + 1) =
      π[k₀ + 1].sent.map GoldilocksVariant.Final.traceMsg
      from GoldilocksVariant.Final.toTrace_sent_newIdx_succ _ π k₀,
    show (toTrace ((Model.goldilocks (V := V)).initial S.C) π).sent (newIdx π k₀) =
      π[k₀].sent.map GoldilocksVariant.Final.traceMsg
      from GoldilocksVariant.Final.toTrace_sent_newIdx _ π k₀] at hm
  obtain ⟨e, he, hee⟩ := exists_envelope_of_mem_map_sub (RStsVariant2.Step.sent_le (π.step_at k₀)) hm
  have hsend : e.sender = S.P.proposer (r i * S.C.R) := congrArg (fun sm => sm.sender) hee
  have hmsg : e.msg = NamedObject.block B := congrArg (fun sm => sm.msg) hee
  refine ⟨B', B, Or.inl ?_, Or.inr ?_, hroot, hne⟩
  · exact inHonestTreeByG_of_known π hlk hadv
      (le_trans (π.stamp_mono (Nat.le_succ k₀)) hstamp) hB'
  · exact ⟨k₀, e, he, by rw [hsend]; exact hadv, hstamp, by rw [hmsg]; rfl⟩

/-- **`hTicksBy` of Lemma 90's and Lemma 98's until forms** (`TicksToUpdatesBy`), at a natural time
`n`, from `SettledAtG` on the observed run at `n` with Goldilocks's update readings, the support
cutoffs `M.supportCutoff S.C (σ + 1)`.

Why: a tick of the trace is a tick of the run at the same clock reading (`exists_of_lbl_tick`), at
the real time `π.stamp (k₀ + 1)` of its step `k₀` (`toTrace_time_newIdx`). A slot's update named by
`TicksToUpdatesBy`, by its cutoff being at most `n` or by a tick to it at a time at most `n`, is an
update reading that `SettledAtG` names in the same two ways; `SettledAtG` then puts every tick to a
reading at most that cutoff at a real time at most `n`.

The variables:
- `π`: the run; `n`: the time; `hS`: no update is half run at `n` on the observed run.

Read aloud: if no update is half run at `n` on the run, none is on its trace. -/
theorem hTicksBy_of_settled {n : ℕ}
    (hS : SettledAtG (fun c : ℕ => ∃ σ : ℕ, c = (Model.goldilocks (V := V)).supportCutoff S.C (σ + 1))
      (observeWithCommittees (Block := Block V) π) (n : ℝ)) :
    GoldilocksCorrectness.Record.Statements.Executions.TicksToUpdatesBy Model.goldilocks S
      (toTrace ((Model.goldilocks (V := V)).initial S.C) π) n := by
  intro σ k u c htrig hl hc
  obtain ⟨k₀, rfl, hl₀, hc₀⟩ := GoldilocksVariant.Final.exists_of_lbl_tick _ π hl
  rw [show (toTrace ((Model.goldilocks (V := V)).initial S.C) π).time (newIdx π k₀) = π.stamp (k₀ + 1)
    from GoldilocksVariant.Final.toTrace_time_newIdx _ π k₀]
  refine hS _ ⟨σ, rfl⟩ ?_ k₀ u c ⟨hl₀, hc₀⟩ hc
  rcases htrig with hle | ⟨k', u', hl', ht'⟩
  · left
    exact_mod_cast hle
  · right
    obtain ⟨k'₀, rfl, hl'₀, hc'₀⟩ := GoldilocksVariant.Final.exists_of_lbl_tick _ π hl'
    rw [show (toTrace ((Model.goldilocks (V := V)).initial S.C) π).time (newIdx π k'₀) =
      π.stamp (k'₀ + 1) from GoldilocksVariant.Final.toTrace_time_newIdx _ π k'₀] at ht'
    exact ⟨k'₀, u', ⟨hl'₀, hc'₀⟩, ht'⟩

omit [ProtocolCommittees (goldilocksProtocol S) (Block V)] in
/-- **Honest through a real time on the trace is honest in every configuration of the run entered by
then** (the conjunct of `HonestThroughEntryStateWithin` and `HonestThroughEntryStateBy`, read from
`route-b`'s `A.HonestThroughTime`). For every real time `t`, `v` is outside the adversary set after
every trace step at a time at most `t` exactly when `v` is outside the corrupted set of every
configuration of the run entered at a real time at most `t`.

Why: the adversary set after trace step `k` is the corrupted set of the run's configuration
`origBefore π k`, entered at a real time at most the time of step `k` (`toTrace_time_mem`); and the
run's configuration `j` is held by the trace step `2 j + ⌊π.stamp j⌋₊`, at the time `π.stamp j`
(`toTrace_time_entry`, `origBefore_entry`).

The variables:
- `π`: the run; `t`: the time; `v`: the validator.

Read aloud: `v` is honest up to `t` on the trace exactly when it is honest in every configuration of
the run entered by `t`. -/
theorem honestThroughTime_iff {t : ℝ} {v : V} :
    (activityOf π).HonestThroughTime (toTrace ((Model.goldilocks (V := V)).initial S.C) π) t v ↔
      ∀ j : ℕ, π.stamp j ≤ t → v ∉ π[j].adv := by
  constructor
  · intro h j hj
    have hk := h (2 * j + ⌊π.stamp j⌋₊)
      (by rw [GoldilocksVariant.Final.toTrace_time_entry]; exact hj)
    rwa [GoldilocksVariant.Final.corrupted_activityOf, GoldilocksVariant.Final.origBefore_entry] at hk
  · intro h k hk
    rw [GoldilocksVariant.Final.corrupted_activityOf]
    exact h _ (le_trans (GoldilocksVariant.Final.toTrace_time_mem _ π k).1 hk)

/-- **The finalized blocks of validators honest through trace steps at times at most `n` being
compatible gives `FinalizedCompatibleBy` on the observed run at every time `t ≤ n`.**

Why: a configuration `k` of the run entered at a time at most `t` is the trace's configuration at
the step `2 k + ⌊stamp k⌋₊`, whose time is `stamp k` (`toTrace_time_entry`) and whose node states
are configuration `k`'s; a validator honest in configuration `k` is honest through that step
(corruption is permanent); and `Block.compatible` is `BlockVocab.Compatible` (`compatible_iff`).

The variables:
- `π`: the run; `t`: the time; `n`: the time the trace's conclusion is read up to; `htn`: `t ≤ n`;
  `h`: the trace's conclusion. -/
theorem finalizedCompatibleBy_of_trace {t : ℝ} {n : ℕ} (htn : t ≤ n)
    (h : ∀ (v₁ v₂ : V) (i j : ℕ),
      (toTrace ((Model.goldilocks (V := V)).initial S.C) π).HonestThrough (activityOf π) i v₁ →
      (toTrace ((Model.goldilocks (V := V)).initial S.C) π).HonestThrough (activityOf π) j v₂ →
      (toTrace ((Model.goldilocks (V := V)).initial S.C) π).time i ≤ n →
      (toTrace ((Model.goldilocks (V := V)).initial S.C) π).time j ≤ n →
      ((toTrace ((Model.goldilocks (V := V)).initial S.C) π).st i v₁).finalized.compatible
        ((toTrace ((Model.goldilocks (V := V)).initial S.C) π).st j v₂).finalized = true) :
    FinalizedCompatibleBy (observeWithCommittees (Block := Block V) π) t := by
  intro v₁ v₂ i j l₁ l₂ ⟨hl₁, hH₁, hi⟩ ⟨hl₂, hH₂, hj⟩
  obtain ⟨lc₁, hlc₁, rfl⟩ := Option.map_eq_some_iff.mp hl₁
  obtain ⟨lc₂, hlc₂, rfl⟩ := Option.map_eq_some_iff.mp hl₂
  have entry : ∀ (k : ℕ) (w : V) (lc : RStsVariant2.Local V (NamedObject V) (NodeState V)),
      π[k][w] = some lc → w ∉ π[k].adv →
      (toTrace ((Model.goldilocks (V := V)).initial S.C) π).HonestThrough (activityOf π)
          (2 * k + ⌊π.stamp k⌋₊) w ∧
        (toTrace ((Model.goldilocks (V := V)).initial S.C) π).time (2 * k + ⌊π.stamp k⌋₊) =
          π.stamp k ∧
        (toTrace ((Model.goldilocks (V := V)).initial S.C) π).st (2 * k + ⌊π.stamp k⌋₊) w =
          lc.st := by
    intro k w lc hlc hw
    refine ⟨fun i' hi' => ?_, GoldilocksVariant.Final.toTrace_time_entry _ π k, ?_⟩
    · rw [GoldilocksVariant.Final.corrupted_activityOf]
      have hle := GoldilocksVariant.Final.origBefore_mono π hi'
      rw [GoldilocksVariant.Final.origBefore_entry] at hle
      exact fun hc => hw (π.adv_mono hle hc)
    · rw [GoldilocksVariant.Final.toTrace_st, GoldilocksVariant.Final.origBefore_entry]
      exact GoldilocksVariant.Final.lastKnownSt_of_some _ π hlc
  obtain ⟨hT₁, ht₁, hs₁⟩ := entry i v₁ lc₁ hlc₁ hH₁
  obtain ⟨hT₂, ht₂, hs₂⟩ := entry j v₂ lc₂ hlc₂ hH₂
  have key := h v₁ v₂ _ _ hT₁ hT₂ (by rw [ht₁]; exact hi.trans htn) (by rw [ht₂]; exact hj.trans htn)
  rw [hs₁, hs₂] at key
  exact (GoldilocksCorrectness.Proofs.Routines.compatible_iff _ _).1 key

omit [ProtocolCommittees (goldilocksProtocol S) (Block V)] in
/-- **The state left by the trace step that holds the run's configuration `k` is that
configuration's.** The trace step `2 k + ⌊π.stamp k⌋₊` (at the real time `π.stamp k`,
`toTrace_time_entry`) is not the trace step of a step of the run, so it leaves the node states it
starts from: the last known memory states at configuration `k`.

Why: the trace step of the run's step `i` is `2 i + 1 + ⌊π.stamp (i + 1)⌋₊`, less than
`2 k + ⌊π.stamp k⌋₊` when `i < k` and more when `k ≤ i` (`π.stamp` is monotone); a trace step that is
not a step of the run keeps the number of the run's steps before it (`newIdx_or_other`), and the
trace step `2 k + ⌊π.stamp k⌋₊` comes after exactly `k` of them (`origBefore_entry`).

The variables:
- `π`: the run; `k`: the configuration; `v`: the validator. -/
theorem toTrace_st_entry_succ (k : ℕ) (v : V) :
    (toTrace ((Model.goldilocks (V := V)).initial S.C) π).st (2 * k + ⌊π.stamp k⌋₊ + 1) v =
      GoldilocksVariant.Final.lastKnownSt ((Model.goldilocks (V := V)).initial S.C) π k v := by
  rcases GoldilocksVariant.Final.newIdx_or_other (NodeState := NodeState V)
      (fun w => (Model.goldilocks (V := V)).initial S.C w) π (2 * k + ⌊π.stamp k⌋₊) with
    ⟨i, hi⟩ | ⟨-, he⟩
  · exfalso
    unfold newIdx at hi
    rcases Nat.lt_or_ge i k with hik | hik
    · have := Nat.floor_mono (π.stamp_mono (show i + 1 ≤ k by omega))
      omega
    · have := Nat.floor_mono (π.stamp_mono (show k ≤ i + 1 by omega))
      omega
  · rw [GoldilocksVariant.Final.toTrace_st]
    erw [he, GoldilocksVariant.Final.origBefore_entry]

omit [ProtocolCommittees (goldilocksProtocol S) (Block V)] in
/-- **A known local state of a validator honest through the entry of its configuration, on the
trace.** For a local state `lc` of `v` known in the run's configuration `k`, with `v` outside the
corrupted set of every configuration entered by the time configuration `k` is entered, the trace
step `2 k + ⌊π.stamp k⌋₊` is at the real time `π.stamp k`, `v` is outside the trace's adversary set
at every step up to that time (`HonestThroughTime`), and the state that step leaves is `lc.st`.

Why: `toTrace_time_entry`, `honestThroughTime_iff`, `toTrace_st_entry_succ` and `lastKnownSt_of_some`.

The variables:
- `π`: the run; `k`: the configuration; `v`: the validator; `lc`: its local state there. -/
theorem entry_of_honestThroughEntry {k : ℕ} {v : V}
    {lc : RStsVariant2.Local V (NamedObject V) (NodeState V)} (hlc : π[k][v] = some lc)
    (hH : ∀ j : ℕ, π.stamp j ≤ π.stamp k → v ∉ π[j].adv) :
    (toTrace ((Model.goldilocks (V := V)).initial S.C) π).time (2 * k + ⌊π.stamp k⌋₊) =
        π.stamp k ∧
      (activityOf π).HonestThroughTime (toTrace ((Model.goldilocks (V := V)).initial S.C) π)
        ((toTrace ((Model.goldilocks (V := V)).initial S.C) π).time (2 * k + ⌊π.stamp k⌋₊)) v ∧
      (toTrace ((Model.goldilocks (V := V)).initial S.C) π).st (2 * k + ⌊π.stamp k⌋₊ + 1) v =
        lc.st := by
  have ht := GoldilocksVariant.Final.toTrace_time_entry ((Model.goldilocks (V := V)).initial S.C) π k
  refine ⟨ht, ?_, (toTrace_st_entry_succ π k v).trans
    (GoldilocksVariant.Final.lastKnownSt_of_some _ π hlc)⟩
  rw [ht]
  exact (honestThroughTime_iff π).2 hH

/-- **Statement 2's agreement, read back from the trace** (`ConfirmedAgreeBetween` on the observed
run at every real time `t` at most the natural `n` up to which the trace's agreement is read).

Why: a configuration `i` of the run entered within `[tFrom, t]` is held by the trace step
`2 i + ⌊π.stamp i⌋₊`, at the real time `π.stamp i`, and the state that step leaves is the node's
state there; a node honest in every configuration entered by then is honest through that step
(`entry_of_honestThroughEntry`); the trace's agreement (`confirmedAgreeBetween_unfold`) then gives the
compatibility of the confirmed tips (`compatible_iff`).

The variables:
- `π`: the run; `tFrom`, `t`: the window read on the run; `n`: the time the trace's agreement is
  read up to; `htn`: `t ≤ n`; `h`: the trace's agreement. -/
theorem confirmedAgreeBetween_of_trace {tFrom t : ℝ} {n : ℕ} (htn : t ≤ n)
    (h : GoldilocksCorrectness.Record.Statements.Executions.ConfirmedAgreeBetween Model.goldilocks S
      (activityOf π) (toTrace ((Model.goldilocks (V := V)).initial S.C) π) tFrom n) :
    ConfirmedAgreeBetween (observeWithCommittees (Block := Block V) π) tFrom t := by
  rw [GoldilocksCorrectness.Record.Proofs.View.confirmedAgreeBetween_unfold] at h
  rintro v₁ v₂ i j l₁ l₂ ⟨hl₁, -, hH₁, hf₁, ht₁⟩ ⟨hl₂, -, hH₂, hf₂, ht₂⟩
  obtain ⟨lc₁, hlc₁, rfl⟩ := Option.map_eq_some_iff.mp hl₁
  obtain ⟨lc₂, hlc₂, rfl⟩ := Option.map_eq_some_iff.mp hl₂
  obtain ⟨he₁, hT₁, hs₁⟩ := entry_of_honestThroughEntry π hlc₁ hH₁
  obtain ⟨he₂, hT₂, hs₂⟩ := entry_of_honestThroughEntry π hlc₂ hH₂
  have key := h v₁ v₂ _ _ hT₁ hT₂ (by rw [he₁]; exact hf₁) (by rw [he₂]; exact hf₂)
    (by rw [he₁]; exact ht₁.trans htn) (by rw [he₂]; exact ht₂.trans htn)
  rw [hs₁, hs₂] at key
  exact (GoldilocksCorrectness.Proofs.Routines.compatible_iff _ _).1 key

/-- **Statement 2's growth, read back from the trace** (`ConfirmedMonotoneBetween` on the observed
run at every real time `t` at most the natural `n` up to which the trace's growth is read).

Why: as `confirmedAgreeBetween_of_trace`, with the trace steps `2 i + ⌊π.stamp i⌋₊` and
`2 j + ⌊π.stamp j⌋₊` in the order of `i ≤ j` (`π.stamp` is monotone); the trace's growth
(`confirmedMonotoneBetween_unfold`) reads honesty at the later step only.

The variables:
- `π`: the run; `tFrom`, `t`: the window read on the run; `n`: the time the trace's growth is read
  up to; `htn`: `t ≤ n`; `h`: the trace's growth. -/
theorem confirmedMonotoneBetween_of_trace {tFrom t : ℝ} {n : ℕ} (htn : t ≤ n)
    (h : GoldilocksCorrectness.Record.Statements.Executions.ConfirmedMonotoneBetween Model.goldilocks
      S (activityOf π) (toTrace ((Model.goldilocks (V := V)).initial S.C) π) tFrom n) :
    ConfirmedMonotoneBetween (observeWithCommittees (Block := Block V) π) tFrom t := by
  rw [GoldilocksCorrectness.Record.Proofs.View.confirmedMonotoneBetween_unfold] at h
  rintro v i j l l' hij ⟨hl, -, hH, hf, -⟩ ⟨hl', -, hH', -, ht'⟩
  obtain ⟨lc, hlc, rfl⟩ := Option.map_eq_some_iff.mp hl
  obtain ⟨lc', hlc', rfl⟩ := Option.map_eq_some_iff.mp hl'
  obtain ⟨he, -, hs⟩ := entry_of_honestThroughEntry π hlc hH
  obtain ⟨he', hT', hs'⟩ := entry_of_honestThroughEntry π hlc' hH'
  have hle : 2 * i + ⌊π.stamp i⌋₊ ≤ 2 * j + ⌊π.stamp j⌋₊ := by
    have := Nat.floor_mono (π.stamp_mono hij)
    omega
  have key := h v _ _ hle hT' (by rw [he]; exact hf) (by rw [he']; exact ht'.trans htn)
  rw [hs, hs'] at key
  exact key

end Conclusions

/-! ## 5. The adversary bound up to a time, on the trace -/

section Adversary

variable {S : Setup V} [ProtocolCommittees (goldilocksProtocol S) (Block V)]
  (π : RStsVariant2.Exec (goldilocksProtocol S))

/-- **Fewer than two thirds of the validators corrupted up to `t` on the trace**, from the weight
bound `WeightBoundsG.quorum` on the observed run at a block an honest node holds by `t`.

Why: a finite set of validators each corrupted after a trace step at a time at most `t` is
corrupted in the run's configuration the last of those steps reads (corruption is permanent),
entered by `t`; there its count, at weight one, is less than the quorum `(2 n + 2) / 3`, so three
times it is less than `2 n`.

The variables:
- `π`: the run; `t`: the time; `B`: the block; `hW`: the weight bounds; `hB`: an honest node holds
  `B` by `t`. -/
theorem adversaryFewerThanTwoThirds_toTrace {tAwakeEnd t : ℝ} {B : Block V}
    (hW : RStsVariant2.WeightBoundsG tAwakeEnd (observeWithCommittees (Block := Block V) π))
    (hB : RStsVariant2.InHonestTreeByG (observeWithCommittees (Block := Block V) π) t B) :
    (activityOf π).AdversaryFewerThanTwoThirdsUntil
      (toTrace ((Model.goldilocks (V := V)).initial S.C) π) (Goldilocks.validator_count V) t := by
  intro X hX
  have hq := hW.quorum t B hB
  obtain ⟨m₀, v₀, l₀, -, -, hm₀, -⟩ := hB
  have hcount : ∀ m : ℕ, π.stamp m ≤ t → (π[m].adv).card < Goldilocks.quorum V := by
    intro m hm
    have h := hq m hm
    have hc : RStsVariant2.counted goldilocksRegistry (π[m].adv) = (π[m].adv).card := by
      simp [RStsVariant2.counted, goldilocksRegistry]
    exact hc ▸ h
  have hn : 0 < Goldilocks.validator_count V := Fintype.card_pos_iff.mpr ⟨v₀⟩
  have hXle : X.card ≤ (π[m₀].adv).card ∨ ∃ m : ℕ, π.stamp m ≤ t ∧ X ⊆ π[m].adv := by
    rcases X.eq_empty_or_nonempty with hX0 | hXne
    · left; simp [hX0]
    · right
      choose idx hidx using hX
      obtain ⟨w, hw, hmax⟩ := Finset.exists_max_image X.attach (fun u => idx u.1 u.2)
        (Finset.attach_nonempty_iff.mpr hXne)
      refine ⟨origBefore π (idx w.1 w.2), ?_, fun u hu => ?_⟩
      · exact ((GoldilocksVariant.Final.toTrace_time_mem _ π _).1).trans (hidx w.1 w.2).1
      · have hu' := (hidx u hu).2
        rw [GoldilocksVariant.Final.corrupted_activityOf] at hu'
        exact π.adv_mono (GoldilocksVariant.Final.origBefore_mono π
          (hmax ⟨u, hu⟩ (Finset.mem_attach _ _))) hu'
  have hX' : X.card < Goldilocks.quorum V := by
    rcases hXle with h | ⟨m, hm, hsub⟩
    · exact h.trans_lt (hcount m₀ hm₀)
    · exact (Finset.card_le_card hsub).trans_lt (hcount m hm)
  unfold Goldilocks.quorum at hX'
  omega

omit [RootOrder] in
/-- **Two quorums of `goldilocksRegistry` can share as few as `2 q − n` validators**, `q` Goldilocks's
quorum and `n` its validator count: `guaranteed goldilocksRegistry goldilocksRegistry ≤ 2 q − n`.

Why: take a set `A` of `q` validators and a set `D` of `2 q − n` of its members (`2 q ≥ n` since
`q = (2 n + 2) / 3`); the validators outside `A` with `D` are `q` validators, a quorum, and share
exactly `D` with `A`. Every validator weighs one, so a set's counted weight is its size. -/
theorem guaranteed_goldilocksRegistry_le :
    RStsVariant2.guaranteed (goldilocksRegistry (V := V)) goldilocksRegistry ≤
      2 * Goldilocks.quorum V - Goldilocks.validator_count V := by
  have hcount : ∀ A : Finset V, RStsVariant2.counted (goldilocksRegistry (V := V)) A = A.card := by
    intro A; simp [RStsVariant2.counted, goldilocksRegistry]
  have hq : Goldilocks.quorum V = (2 * Goldilocks.validator_count V + 2) / 3 := rfl
  have hn : Goldilocks.validator_count V = (Finset.univ : Finset V).card := rfl
  obtain ⟨A, -, hA⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset V))
    (n := Goldilocks.quorum V) (by omega)
  obtain ⟨D, hDA, hD⟩ := Finset.exists_subset_card_eq (s := A)
    (n := 2 * Goldilocks.quorum V - Goldilocks.validator_count V) (by omega)
  have hdisj : Disjoint (Finset.univ \ A) D :=
    Finset.disjoint_of_subset_right hDA Finset.sdiff_disjoint
  have hBcard : ((Finset.univ \ A) ∪ D).card = Goldilocks.quorum V := by
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_sdiff_of_subset (Finset.subset_univ A)]
    omega
  have hAB : A ∩ ((Finset.univ \ A) ∪ D) = D := by
    ext v; constructor
    · intro h; simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff,
        Finset.mem_univ, true_and] at h
      rcases h with ⟨hA', h | h⟩
      · exact absurd hA' h
      · exact h
    · intro h; exact Finset.mem_inter.2 ⟨hDA h, Finset.mem_union_right _ h⟩
  have hmem : (A, (Finset.univ \ A) ∪ D) ∈
      RStsVariant2.quorumPairs (goldilocksRegistry (V := V)) goldilocksRegistry := by
    simp only [RStsVariant2.quorumPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_powerset,
      RStsVariant2.IsQuorum, hcount, hA, hBcard]
    exact ⟨⟨fun _ _ => Finset.mem_univ _, fun _ _ => Finset.mem_univ _⟩, le_rfl, le_rfl⟩
  unfold RStsVariant2.guaranteed
  rw [dif_pos ⟨_, hmem⟩]
  calc _ ≤ RStsVariant2.counted goldilocksRegistry (A ∩ ((Finset.univ \ A) ∪ D)) :=
        Finset.inf'_le _ hmem
    _ = _ := by rw [hcount, hAB, hD]

/-- **Fewer than a third of the validators corrupted up to `tAwakeEnd` on the trace**, from the
weight bound `WeightBoundsG.third` on the observed run at a block an honest node holds by
`tAwakeEnd`, and Goldilocks's extra condition `AdversaryLeavesQuorumBy tAwakeEnd`.

Why: a finite set `X` of validators each corrupted after a trace step at a time at most
`tAwakeEnd` is corrupted in the run's configuration the last of those steps reads (corruption is
permanent), entered by `tAwakeEnd`. There its count is less than `guaranteed`, at most `2 q − n`
(`guaranteed_goldilocksRegistry_le`, `q` the quorum, `n` the validator count); and
`AdversaryLeavesQuorumBy` gives `q ≤ n − |X|`. With `q = (2 n + 2) / 3`, the two give
`3 |X| < n` at every `n`.

The variables:
- `π`: the run; `tAwakeEnd`: the end of the healing phase; `B`: the block; `hW`: the weight
  bounds; `hB`: an honest node holds `B` by `tAwakeEnd`; `hQ`: the extra condition. -/
theorem adversaryFewerThanThird_toTrace {tAwakeEnd : ℝ} {B : Block V}
    (hW : RStsVariant2.WeightBoundsG tAwakeEnd (observeWithCommittees (Block := Block V) π))
    (hB : RStsVariant2.InHonestTreeByG (observeWithCommittees (Block := Block V) π) tAwakeEnd B)
    (hQ : AdversaryLeavesQuorumBy tAwakeEnd (observeWithCommittees (Block := Block V) π)) :
    (activityOf π).AdversaryFewerThanThirdUntil
      (toTrace ((Model.goldilocks (V := V)).initial S.C) π) (Goldilocks.validator_count V)
      tAwakeEnd := by
  intro X hX
  have hrun : ∀ v ∈ X, ∃ m : ℕ, π.stamp m ≤ tAwakeEnd ∧ v ∈ π[m].adv := by
    intro v hv
    obtain ⟨i, hi, hc⟩ := hX v hv
    refine ⟨origBefore π i, ((GoldilocksVariant.Final.toTrace_time_mem _ π _).1).trans hi, ?_⟩
    rwa [GoldilocksVariant.Final.corrupted_activityOf] at hc
  have hleave := hQ X fun v hv => by
    obtain ⟨m, hm, hc⟩ := hrun v hv
    exact ⟨m, hm, fun h => h hc⟩
  have hthird := hW.third B B hB hB
  obtain ⟨m₀, v₀, l₀, -, -, hm₀, -⟩ := hB
  have hg := guaranteed_goldilocksRegistry_le (V := V)
  have hcount : ∀ m : ℕ, π.stamp m ≤ tAwakeEnd →
      (π[m].adv).card < 2 * Goldilocks.quorum V - Goldilocks.validator_count V := by
    intro m hm
    have h := hthird m hm
    have hc : RStsVariant2.counted goldilocksRegistry (π[m].adv) = (π[m].adv).card := by
      simp [RStsVariant2.counted, goldilocksRegistry]
    exact (hc ▸ h).trans_le hg
  have hXle : X.card ≤ (π[m₀].adv).card ∨ ∃ m : ℕ, π.stamp m ≤ tAwakeEnd ∧ X ⊆ π[m].adv := by
    rcases X.eq_empty_or_nonempty with hX0 | hXne
    · left; simp [hX0]
    · right
      choose idx hidx using hX
      obtain ⟨w, hw, hmax⟩ := Finset.exists_max_image X.attach (fun u => idx u.1 u.2)
        (Finset.attach_nonempty_iff.mpr hXne)
      refine ⟨origBefore π (idx w.1 w.2), ?_, fun u hu => ?_⟩
      · exact ((GoldilocksVariant.Final.toTrace_time_mem _ π _).1).trans (hidx w.1 w.2).1
      · have hu' := (hidx u hu).2
        rw [GoldilocksVariant.Final.corrupted_activityOf] at hu'
        exact π.adv_mono (GoldilocksVariant.Final.origBefore_mono π
          (hmax ⟨u, hu⟩ (Finset.mem_attach _ _))) hu'
  have hX' : X.card < 2 * Goldilocks.quorum V - Goldilocks.validator_count V := by
    rcases hXle with h | ⟨m, hm, hsub⟩
    · exact h.trans_lt (hcount m₀ hm₀)
    · exact (Finset.card_le_card hsub).trans_lt (hcount m hm)
  have hq : Goldilocks.quorum V = (2 * Goldilocks.validator_count V + 2) / 3 := rfl
  omega

end Adversary

/-! ## 6. The slot times, as integers and as the trace's natural numbers -/

section SlotTimes

variable (S : Setup V)

omit [RootOrder] in
/-- The start of slot `s` is `4 · S.C.Δ · s`, as an integer.

The variables:
- `S`: the setup; `s`: the slot. -/
theorem slotTime_eq (s : ℕ) : S.C.t_ s = 4 * S.C.Δ * (s : ℤ) := rfl

omit [RootOrder] in
/-- A slot start is never negative.

The variables:
- `S`: the setup; `s`: the slot. -/
theorem slotTime_nonneg (s : ℕ) : @LE.le ℤ _ 0 (S.C.t_ s) := by
  rw [slotTime_eq]
  have := S.C.Δ_pos
  positivity

omit [RootOrder] in
/-- The slot whose start is later is the later slot.

The variables:
- `S`: the setup; `s`, `s'`: the slots; `h`: slot `s` starts before slot `s'`. -/
theorem lt_of_slotTime_lt {s s' : ℕ} (h : S.C.t_ s < S.C.t_ s') : s < s' := by
  by_contra hc
  have hle : (s' : ℤ) ≤ s := by exact_mod_cast not_lt.mp hc
  have := S.C.Δ_pos
  rw [slotTime_eq, slotTime_eq] at h
  nlinarith

omit [RootOrder] in
/-- A natural number at most an integer that is never negative is at most it as reals: a time `z ≥ 0`
of the spec, read as a natural number by `Int.toNat`, is the same real number.

The variables:
- `z`: the integer; `h`: it is not negative. -/
theorem toNat_cast_real {z : ℤ} (h : 0 ≤ z) : ((z.toNat : ℕ) : ℝ) = (z : ℝ) := by
  rw [← Int.cast_natCast, Int.toNat_of_nonneg h]

omit [RootOrder] in
/-- An integer is at most its natural part, as reals.

The variables:
- `z`: the integer. -/
theorem cast_le_toNat_cast (z : ℤ) : (z : ℝ) ≤ ((z.toNat : ℕ) : ℝ) := by
  rw [← Int.cast_natCast]
  exact_mod_cast Int.self_le_toNat z

omit [RootOrder] in
/-- The support cutoff of slot `s − 1`, `S.C.t_ s + 2 · S.C.Δ`, read as the trace's natural number, is
the same real number.

The variables:
- `S`: the setup; `s`: the slot. -/
theorem cutoff_toNat_cast (s : ℕ) :
    (((S.C.t_ s + 2 * S.C.Δ).toNat : ℕ) : ℝ) = ((S.C.t_ s + 2 * S.C.Δ : Time) : ℝ) := by
  apply toNat_cast_real
  have h1 := slotTime_nonneg S s
  have h2 : (0 : ℤ) < S.C.Δ := S.C.Δ_pos
  show (0 : ℤ) ≤ S.C.t_ s + 2 * S.C.Δ
  omega

omit [RootOrder] in
/-- The start of slot `s`, read as the trace's natural number, is the same real number.

The variables:
- `S`: the setup; `s`: the slot. -/
theorem slotTime_toNat_cast (s : ℕ) :
    (((S.C.t_ s).toNat : ℕ) : ℝ) = ((S.C.t_ s : Time) : ℝ) :=
  toNat_cast_real (slotTime_nonneg S s)

omit [RootOrder] in
/-- A slot `s` whose start is at least a natural number `tN` that is later than the start of slot
`S.C.k` is after slot `S.C.k`.

The variables:
- `S`: the setup; `tA`: a real time later than the start of slot `S.C.k`; `tN`: a natural number at
  least `tA`; `s`: the slot. -/
theorem k_lt_of_le_slotStart {tA : ℝ} {tN : ℕ} {s : ℕ}
    (hA : ((S.C.t_ S.C.k : Time) : ℝ) < tA) (htA : tA ≤ (tN : ℝ)) (hs : tN ≤ (S.C.t_ s).toNat) :
    S.C.k < s := by
  apply lt_of_slotTime_lt S
  have h1 : (tN : ℝ) ≤ ((S.C.t_ s : Time) : ℝ) := by
    rw [← slotTime_toNat_cast]; exact_mod_cast hs
  exact_mod_cast hA.trans_le (htA.trans h1)

omit [RootOrder] in
/-- The slot start grows with the slot.

The variables:
- `S`: the setup; `s`, `s'`: the slots, `s ≤ s'`. -/
theorem slotTime_mono {s s' : ℕ} (h : s ≤ s') : @LE.le ℤ _ (S.C.t_ s) (S.C.t_ s') := by
  rw [slotTime_eq, slotTime_eq]
  have := S.C.Δ_pos
  have hle : (s : ℤ) ≤ s' := by exact_mod_cast h
  nlinarith

omit [RootOrder] in
/-- The next slot starts `4 · S.C.Δ` later.

The variables:
- `S`: the setup; `s`: the slot. -/
theorem slotTime_succ (s : ℕ) : @Eq ℤ (S.C.t_ (s + 1)) (S.C.t_ s + 4 * S.C.Δ) := by
  rw [slotTime_eq, slotTime_eq]; push_cast; ring

omit [RootOrder] in
/-- The proposal window of slot `s` starts one delay after the start of slot `s` less the start of
slot `S.C.k + 1`.

The variables:
- `S`: the setup; `s`: the slot. -/
theorem proposal_window_start_eq_slotTime (s : ℕ) :
    Goldilocks.proposal_window_start S.C s = S.C.t_ s + S.C.Δ - S.C.t_ (S.C.k + 1) := by
  show S.C.t_ s + S.C.Δ - 4 * S.C.Δ * ((S.C.k : ℤ) + 1) = _
  rw [slotTime_eq S (S.C.k + 1)]; push_cast; ring

omit [RootOrder] in
/-- The window of slot `s`'s duties starts one delay after the start of slot `s` less the start of
slot `S.C.k`.

The variables:
- `S`: the setup; `s`: the slot. -/
theorem duty_window_start_eq_slotTime (s : ℕ) :
    @Eq ℤ (Goldilocks.duty_window_start S.C s) (S.C.t_ s + S.C.Δ - S.C.t_ S.C.k) := by
  show S.C.t_ s + S.C.Δ - 4 * S.C.Δ * (S.C.k : ℤ) = _
  rw [slotTime_eq S S.C.k]

omit [RootOrder] in
/-- A real time at most a natural number `tN` at most the start of slot `s` read as a natural number is
at most the start of slot `s`.

The variables:
- `S`: the setup; `tA`: the real time; `tN`: the natural number; `s`: the slot. -/
theorem le_slotTime_of {tA : ℝ} {tN : ℕ} {s : ℕ} (htA : tA ≤ (tN : ℝ))
    (hs : tN ≤ (S.C.t_ s).toNat) : tA ≤ ((S.C.t_ s : Time) : ℝ) := by
  rw [← slotTime_toNat_cast]; exact htA.trans (by exact_mod_cast hs)

end SlotTimes

/-! ## 7. The honest active validators and the holders, on the trace -/

section Holders

open GoldilocksCorrectness.Statements.AbstractTrace (Activity)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (honestActiveAt activeAt)
open GoldilocksCorrectness.Record.Statements.Executions (HonestOpenerAt)
open Goldilocks (duty_window_start proposal_window_start)

variable {S : Setup V} [ProtocolCommittees (goldilocksProtocol S) (Block V)]
  (π : RStsVariant2.Exec (goldilocksProtocol S))

/-- A validator up and honest throughout `[a, b]` on the observed run is active throughout `[a, b]`
on the trace.

Why: a trace step whose configuration is in force at some time of `[a, b]` reads the run's
configuration `o := origBefore π j`, entered by the trace step's time (at most `b`); that
configuration is left at or after `a`: the time after the trace step is at most `π.stamp (o + 1)`,
the trace step after a step of the run keeping that step's time.

The variables:
- `π`: the run; `a`, `b`: the window; `v`: the validator; `h`: `v` is up and honest throughout
  `[a, b]` on the observed run. -/
theorem activeThroughout_of_upAndHonest {a b : ℝ} {v : V}
    (h : RStsVariant2.UpAndHonestThroughoutG (observeWithCommittees (Block := Block V) π) a b v) :
    v ∈ (activityOf π).activeThroughout (toTrace ((Model.goldilocks (V := V)).initial S.C) π) a b := by
  simp only [Activity.activeThroughout, Finset.mem_filter, Finset.mem_univ, true_and]
  intro j hjb haj
  rw [GoldilocksVariant.Final.mem_active_activityOf]
  have hm := GoldilocksVariant.Final.toTrace_time_mem
    (fun w => (Model.goldilocks (V := V)).initial S.C w) π j
  have hleft : a ≤ π.stamp (origBefore π j + 1) := by
    rcases GoldilocksVariant.Final.newIdx_or_other (NodeState := NodeState V)
        (fun w => (Model.goldilocks (V := V)).initial S.C w) π j with ⟨k, hk⟩ | ⟨-, he⟩
    · have ho : origBefore π j = k := by rw [← hk]; exact GoldilocksVariant.Final.origBefore_newIdx π k
      have ht : (toTrace ((Model.goldilocks (V := V)).initial S.C) π).time (j + 1) =
          π.stamp (k + 1) := by
        rw [← hk]; exact GoldilocksVariant.Final.toTrace_time_newIdx_succ _ π k
      rw [ho]; rw [ht] at haj; exact haj
    · have hm1 := GoldilocksVariant.Final.toTrace_time_mem
        (fun w => (Model.goldilocks (V := V)).initial S.C w) π (j + 1)
      erw [he] at hm1
      exact haj.trans hm1.2
  obtain ⟨h1, h2, h3⟩ := h (origBefore π j) hleft (hm.1.trans hjb)
  exact ⟨⟨h1, (state_observeWithCommittees_ne_none π _ v).1 h2⟩, h3⟩

omit [ProtocolCommittees (goldilocksProtocol S) (Block V)] in
/-- A validator active throughout a window on the trace is active throughout every window inside it.

The variables:
- `π`: the run; `a`, `b`: the window; `a'`, `b'`: the window inside it; `v`: the validator. -/
theorem activeThroughout_mono {a b a' b' : ℝ} {v : V} (ha : a ≤ a') (hb : b' ≤ b)
    (h : v ∈ (activityOf π).activeThroughout (toTrace ((Model.goldilocks (V := V)).initial S.C) π)
      a b) :
    v ∈ (activityOf π).activeThroughout (toTrace ((Model.goldilocks (V := V)).initial S.C) π)
      a' b' := by
  simp only [Activity.activeThroughout, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
  intro j h1 h2
  exact h j (h1.trans hb) (ha.trans h2)

/-- A validator awake from a tick on the trace, up to its tick to `b`, is up to that tick on the
observed run (`UpToTickG`).

Why: a trace step labelled as `v`'s tick at a reading is the trace step `newIdx π k` of a step `k` of
the run that is that tick; `newIdx π` is strictly increasing, and `v` is awake at the trace step
`newIdx π i` exactly when it is up in the run's configuration `i`.

The variables:
- `π`: the run; `a`: the reading that opens the window; `b`: the reading of the tick that ends it;
  `v`: the validator. -/
theorem upToTickG_of_awakeThroughoutToTick {a : ℤ} {b : ℕ} {v : V}
    (h : v ∈ (activityOf π).awakeThroughoutToTick
      (toTrace ((Model.goldilocks (V := V)).initial S.C) π) a b) :
    UpToTickG (observeWithCommittees (Block := Block V) π) a b v := by
  simp only [Activity.awakeThroughoutToTick, Finset.mem_filter, Finset.mem_univ, true_and] at h
  obtain ⟨k', hk', hcase⟩ := h
  obtain ⟨i', rfl, hl, hc⟩ := GoldilocksVariant.Final.exists_of_lbl_tick _ π hk'
  have hs := state_observeWithCommittees_ne_none π
  have hmono := (GoldilocksVariant.Final.newIdx_strictMono π).monotone
  refine ⟨i', ⟨hl, hc⟩, ?_⟩
  rcases hcase with hall | ⟨k, hkk, c, hca, hkl, hall⟩
  · left
    intro i hi
    have := hall (newIdx π i) (hmono hi)
    rw [GoldilocksVariant.Final.mem_awake_activityOf_newIdx] at this
    exact ⟨this.1, (hs i v).2 this.2⟩
  · right
    obtain ⟨k₀, rfl, hl0, hc0⟩ := GoldilocksVariant.Final.exists_of_lbl_tick _ π hkl
    have hk0 : k₀ ≤ i' := (GoldilocksVariant.Final.newIdx_strictMono π).le_iff_le.1 hkk
    refine ⟨k₀, hk0, c, hca, ⟨hl0, hc0⟩, fun i h1 h2 => ?_⟩
    have := hall (newIdx π i) (hmono h1) (hmono h2)
    rw [GoldilocksVariant.Final.mem_awake_activityOf_newIdx] at this
    exact ⟨this.1, (hs i v).2 this.2⟩

/-- A validator active from a tick on the trace, up to its tick to `b`, is up and honest to that tick
on the observed run (`UpAndHonestToTickG`).

Why: as `upToTickG_of_awakeThroughoutToTick`, with `v` outside the adversary set at the trace step
`newIdx π i` exactly when it is outside the run's corrupted set of configuration `i`.

The variables:
- `π`: the run; `a`: the reading that opens the window; `b`: the reading of the tick that ends it;
  `v`: the validator. -/
theorem upAndHonestToTickG_of_activeThroughoutToTick {a : ℤ} {b : ℕ} {v : V}
    (h : v ∈ (activityOf π).activeThroughoutToTick
      (toTrace ((Model.goldilocks (V := V)).initial S.C) π) a b) :
    UpAndHonestToTickG (observeWithCommittees (Block := Block V) π) a b v := by
  simp only [Activity.activeThroughoutToTick, Finset.mem_filter, Finset.mem_univ, true_and] at h
  obtain ⟨k', hk', hcase⟩ := h
  obtain ⟨i', rfl, hl, hc⟩ := GoldilocksVariant.Final.exists_of_lbl_tick _ π hk'
  have hs := state_observeWithCommittees_ne_none π
  have hmono := (GoldilocksVariant.Final.newIdx_strictMono π).monotone
  have hact : ∀ i : ℕ, v ∈ (activityOf π).active (newIdx π i) →
      v ∉ RStsVariant2.Observable.crashed (observeWithCommittees (Block := Block V) π) i ∧
        RStsVariant2.Observable.state (observeWithCommittees (Block := Block V) π) i v ≠ none ∧
        RStsVariant2.HonestG (observeWithCommittees (Block := Block V) π) i v := by
    intro i hi
    rw [GoldilocksVariant.Final.mem_active_activityOf,
      GoldilocksVariant.Final.origBefore_newIdx] at hi
    exact ⟨hi.1.1, (hs i v).2 hi.1.2, hi.2⟩
  refine ⟨i', ⟨hl, hc⟩, ?_⟩
  rcases hcase with hall | ⟨k, hkk, c, hca, hkl, hall⟩
  · exact Or.inl fun i hi => hact i (hall (newIdx π i) (hmono hi))
  · right
    obtain ⟨k₀, rfl, hl0, hc0⟩ := GoldilocksVariant.Final.exists_of_lbl_tick _ π hkl
    have hk0 : k₀ ≤ i' := (GoldilocksVariant.Final.newIdx_strictMono π).le_iff_le.1 hkk
    exact ⟨k₀, hk0, c, hca, ⟨hl0, hc0⟩, fun i h1 h2 =>
      hact i (hall (newIdx π i) (hmono h1) (hmono h2))⟩

/-- A validator outside the trace's adversary set after every step whose time is at most `c` is
honest up to `c` on the observed run (`HonestByG`).

Why: the run's configuration `j` entered at a time at most `c` is the configuration of the trace step
`2 j + ⌊π.stamp j⌋₊`, whose time is `π.stamp j` (`toTrace_time_entry`, `origBefore_entry`).

The variables:
- `π`: the run; `c`: the time; `v`: the validator. -/
theorem honestByG_of_not_mem_corruptedAtTime {c : ℝ} {v : V}
    (h : v ∉ (activityOf π).corruptedAtTime (toTrace ((Model.goldilocks (V := V)).initial S.C) π) c) :
    HonestByG (observeWithCommittees (Block := Block V) π) c v := by
  intro j hj hadv
  apply h
  simp only [Activity.corruptedAtTime, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨2 * j + ⌊π.stamp j⌋₊, ?_, ?_⟩
  · rw [GoldilocksVariant.Final.toTrace_time_entry]; exact hj
  · rw [GoldilocksVariant.Final.corrupted_activityOf, GoldilocksVariant.Final.origBefore_entry]
    exact hadv

open Classical in
/-- A validator outside the trace's adversary set at every step at which a validator outside it ticks
to `c` is honest, on the observed run, in every configuration from which a validator honest there
ticks at the reading `c`.

Why: the run's tick at step `k` is the trace step `newIdx π k`, labelled with that tick
(`eventOf_eq_tick`), whose adversary set is the run's corrupted set of configuration `k`.

The variables:
- `π`: the run; `c`: the reading; `v`: the validator. -/
theorem honest_at_ticks_of_not_mem {c : ℕ} {v : V}
    (h : v ∉ Finset.univ.filter (fun u => ∃ (k : ℕ) (w : V),
      (toTrace ((Model.goldilocks (V := V)).initial S.C) π).lbl k = GoldilocksCorrectness.Statements.AbstractTrace.Event.tick w c ∧
        w ∉ (activityOf π).corrupted k ∧ u ∈ (activityOf π).corrupted k)) :
    ∀ (k : ℕ) (w : V), TickAtG (observeWithCommittees (Block := Block V) π) k w c →
      RStsVariant2.HonestG (observeWithCommittees (Block := Block V) π) k w →
      RStsVariant2.HonestG (observeWithCommittees (Block := Block V) π) k v := by
  intro k w hT hw hv
  apply h
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨newIdx π k, w, ?_, ?_, ?_⟩
  · exact (GoldilocksVariant.Final.toTrace_lbl_newIdx _ π k).trans
      ((GoldilocksVariant.Final.eventOf_eq_tick π).2 hT)
  · rw [GoldilocksVariant.Final.corrupted_activityOf_newIdx]; exact hw
  · rw [GoldilocksVariant.Final.corrupted_activityOf_newIdx]; exact hv

/-- **An honest active validator of slot `s` on the trace is one on the observed run**:
`honestActiveAt` at Goldilocks's model gives `HonestActiveG`.

Why: its three parts, by `upToTickG_of_awakeThroughoutToTick`, `honestByG_of_not_mem_corruptedAtTime`
(the support cutoff read as a natural number is the same real number) and
`honest_at_ticks_of_not_mem`.

The variables:
- `π`: the run; `s`: the slot; `v`: the validator. -/
theorem honestActiveG_of_mem {s : ℕ} {v : V}
    (h : v ∈ honestActiveAt Model.goldilocks S (activityOf π)
      (toTrace ((Model.goldilocks (V := V)).initial S.C) π) s) :
    HonestActiveG S (observeWithCommittees (Block := Block V) π) s v := by
  unfold honestActiveAt activeAt at h
  rw [Finset.mem_sdiff, Finset.mem_union, not_or] at h
  obtain ⟨hA, hC, hT⟩ := h
  refine ⟨upToTickG_of_awakeThroughoutToTick π hA, ?_, honest_at_ticks_of_not_mem π hT⟩
  have := honestByG_of_not_mem_corruptedAtTime π hC
  rwa [show (((Model.goldilocks (V := V)).supportCutoff S.C (s + 1) : ℕ) : ℝ) =
      ((S.C.t_ (s + 1) + 2 * S.C.Δ : Time) : ℝ) from cutoff_toNat_cast S (s + 1)] at this

open Classical in
/-- **A proposer that ran its slot up to the update on the trace is one on the observed run**: the
proposer of slot `s` in `activeThroughoutToTick` from its proposal window's start to the support
cutoff of slot `s + 1`, outside the adversary set by that cutoff's time and at every honest tick to it,
gives `HonestProposerToUpdateG`.

Why: as `honestActiveG_of_mem`, with `upAndHonestToTickG_of_activeThroughoutToTick`.

The variables:
- `π`: the run; `s`: the slot. -/
theorem honestProposerToUpdateG_of_trace {s : ℕ}
    (h : S.P.proposer s ∈ (activityOf π).activeThroughoutToTick
        (toTrace ((Model.goldilocks (V := V)).initial S.C) π) (proposal_window_start S.C s)
        ((Model.goldilocks (V := V)).supportCutoff S.C (s + 1)) ∧
      S.P.proposer s ∉ (activityOf π).corruptedAtTime
          (toTrace ((Model.goldilocks (V := V)).initial S.C) π)
          ((Model.goldilocks (V := V)).supportCutoff S.C (s + 1)) ∪
        Finset.univ.filter (fun u => ∃ (k : ℕ) (w : V),
          (toTrace ((Model.goldilocks (V := V)).initial S.C) π).lbl k =
            GoldilocksCorrectness.Statements.AbstractTrace.Event.tick w ((Model.goldilocks (V := V)).supportCutoff S.C (s + 1)) ∧
          w ∉ (activityOf π).corrupted k ∧ u ∈ (activityOf π).corrupted k)) :
    HonestProposerToUpdateG S (observeWithCommittees (Block := Block V) π) s := by
  obtain ⟨hA, hN⟩ := h
  rw [Finset.mem_union, not_or] at hN
  refine ⟨upAndHonestToTickG_of_activeThroughoutToTick π hA, ?_, honest_at_ticks_of_not_mem π hN.2⟩
  have := honestByG_of_not_mem_corruptedAtTime π hN.1
  rwa [show (((Model.goldilocks (V := V)).supportCutoff S.C (s + 1) : ℕ) : ℝ) =
      ((S.C.t_ (s + 1) + 2 * S.C.Δ : Time) : ℝ) from cutoff_toNat_cast S (s + 1)] at this

/-- An honest opener of slot `s` on the trace (`HonestOpenerAt`) is a proposer that ran its slot up to
the update on the observed run.

Why: `HonestOpenerAt` holds the premise of `honestProposerToUpdateG_of_trace`, and more.

The variables:
- `π`: the run; `s`: the slot. -/
theorem honestProposerToUpdateG_of_honestOpenerAt {s : ℕ}
    (h : HonestOpenerAt Model.goldilocks S (activityOf π)
      (toTrace ((Model.goldilocks (V := V)).initial S.C) π) s) :
    HonestProposerToUpdateG S (observeWithCommittees (Block := Block V) π) s := by
  obtain ⟨hA, hN⟩ := h
  rw [Finset.mem_union, Finset.mem_union, not_or, not_or] at hN
  exact honestProposerToUpdateG_of_trace π ⟨hA, by rw [Finset.mem_union, not_or]; exact ⟨hN.1.1, hN.2⟩⟩

/-! ### The holder rows of the top statements after the healing phase

Each theorem reads one holder row of `route-b`'s top statements (natural times: the end of the healing
phase `tN`, the slot times of Goldilocks's model) from Goldilocks's extra condition on the observed run
at a real `tA ≤ tN`. Two constants make the model's natural windows the condition's integer ones: the
sync delay `Δs` is at most the start of slot `S.C.k` (from Goldilocks's delay conditions), and `tA` is
later than that start (from its healing premise), so every window read starts at a time that is not
negative. -/

/-- The committee row of `HoldersStayOnlineAfterHealing`, read on the trace at slot `s'`: an honest
active member of slot `s'`'s committee is active throughout the window of `route-b`'s `hHold`.

Why: the member is an honest active validator on the observed run (`honestActiveG_of_mem`); the row
gives it up and honest throughout `[c − max (2Δ) Δs, c − max (2Δ) Δs + Δs]` with `c` the support cutoff
of slot `s' − 1`, which is active throughout on the trace (`activeThroughout_of_upAndHonest`); with
`S.C.k ≤ s'` that window's start is not negative, so the model's natural window is the same.

The variables:
- `π`: the run; `Δs`: the sync delay; `tA`: the end of the healing phase; `hH`: the extra condition;
  `hk`: `Δs` is at most the start of slot `S.C.k`; `s'`: the slot, `S.C.k ≤ s'`; `u`: the member. -/
theorem committee_hold_toTrace {Δs : ℕ} {tA : ℝ}
    (hH : HoldersStayOnlineAfterHealing S Δs tA (observeWithCommittees (Block := Block V) π))
    (hk : (Δs : ℤ) ≤ S.C.t_ S.C.k) {s' : ℕ} (hks : S.C.k ≤ s')
    (hA : tA ≤ ((S.C.t_ (s' + 1) : Time) : ℝ)) {u : V}
    (hu : u ∈ honestActiveAt Model.goldilocks S (activityOf π)
      (toTrace ((Model.goldilocks (V := V)).initial S.C) π) s') (hc : u ∈ S.P.committee s') :
    u ∈ (activityOf π).activeThroughout (toTrace ((Model.goldilocks (V := V)).initial S.C) π)
      (((Model.goldilocks (V := V)).supportCutoff S.C s' -
        max (2 * GoldilocksCorrectness.Statements.Routines.Δ S) Δs : ℕ) : ℝ)
      ((((Model.goldilocks (V := V)).supportCutoff S.C s' -
        max (2 * GoldilocksCorrectness.Statements.Routines.Δ S) Δs : ℕ) : ℝ) + Δs) := by
  have h := activeThroughout_of_upAndHonest π (hH.committee s' hA u hc (honestActiveG_of_mem π hu))
  have hts := slotTime_mono S hks
  have hts0 := slotTime_nonneg S s'
  have hΔ : (0 : ℤ) < S.C.Δ := S.C.Δ_pos
  have hΔn : ((GoldilocksCorrectness.Statements.Routines.Δ S : ℕ) : ℤ) = S.C.Δ :=
    GoldilocksCorrectness.Proofs.Routines.Δ_cast S
  have hW : ((((Model.goldilocks (V := V)).supportCutoff S.C s' -
      max (2 * GoldilocksCorrectness.Statements.Routines.Δ S) Δs : ℕ) : ℝ)) =
      ((S.C.t_ s' + 2 * S.C.Δ - max (2 * S.C.Δ) (Δs : Time) : Time) : ℝ) := by
    rw [← Int.cast_natCast]
    congr 1
    show ((((S.C.t_ s' + 2 * S.C.Δ).toNat -
      max (2 * GoldilocksCorrectness.Statements.Routines.Δ S) Δs : ℕ)) : ℤ) = _
    omega
  rw [hW]
  exact h

/-- **`hHold` of `lem90_healed_confirmed_until` and `lem98_healed_finality_liveness_ofSync`**, from
`HoldersStayOnlineAfterHealing.committee`.

Why: a slot `s'` whose next slot starts at or after `tN` is after slot `S.C.k − 1`
(`k_lt_of_le_slotStart`); `committee_hold_toTrace`.

The variables:
- `π`: the run; `Δs`: the sync delay; `tA`: the end of the healing phase on the observed run, `tN`
  the natural number `route-b` reads; `hH`: the extra condition; `hk`: `Δs` is at most the start of
  slot `S.C.k`; `hA`: `tA` is later than that start; `t`: the time the statement reads up to. -/
theorem hHold_toTrace {Δs : ℕ} {tA : ℝ} {tN : ℕ}
    (hH : HoldersStayOnlineAfterHealing S Δs tA (observeWithCommittees (Block := Block V) π))
    (hk : (Δs : ℤ) ≤ S.C.t_ S.C.k) (hA : ((S.C.t_ S.C.k : Time) : ℝ) < tA) (htA : tA ≤ (tN : ℝ))
    (t : ℕ) :
    ∀ s' : ℕ, tN ≤ (Model.goldilocks (V := V)).slotStart S.C (s' + 1) →
      (Model.goldilocks (V := V)).supportCutoff S.C (s' + 1) ≤ t →
      ∀ u ∈ honestActiveAt Model.goldilocks S (activityOf π)
        (toTrace ((Model.goldilocks (V := V)).initial S.C) π) s', u ∈ S.P.committee s' →
      u ∈ (activityOf π).activeThroughout (toTrace ((Model.goldilocks (V := V)).initial S.C) π)
        (((Model.goldilocks (V := V)).supportCutoff S.C s' -
          max (2 * GoldilocksCorrectness.Statements.Routines.Δ S) Δs : ℕ) : ℝ)
        ((((Model.goldilocks (V := V)).supportCutoff S.C s' -
          max (2 * GoldilocksCorrectness.Statements.Routines.Δ S) Δs : ℕ) : ℝ) + Δs) := by
  intro s' hs' _ u hu hc
  have hks : S.C.k < s' + 1 := k_lt_of_le_slotStart S hA htA hs'
  exact committee_hold_toTrace π hH hk (by omega) (le_slotTime_of S htA hs') hu hc

/-- **`hHoldV` of `confirmedPersists_asyncPeriod_until`**, from
`HoldersStayOnlineAfterHealing.committee`: the honest voters of slots `s − 1` and `s`, for a slot `s`
starting after `tN`.

Why: slot `s` is after slot `S.C.k` (`k_lt_of_le_slotStart`), so `S.C.k ≤ s − 1`, and the slot after
`s'` starts at or after slot `s`; `committee_hold_toTrace`.

The variables:
- `π`: the run; `Δs`: the sync delay; `tA`, `tN`: the end of the healing phase, as in
  `hHold_toTrace`; `hH`: the extra condition; `hk`, `hA`: as in `hHold_toTrace`; `s`: the hand-over
  slot; `hs`: it starts after `tN`. -/
theorem hHoldV_toTrace {Δs : ℕ} {tA : ℝ} {tN : ℕ}
    (hH : HoldersStayOnlineAfterHealing S Δs tA (observeWithCommittees (Block := Block V) π))
    (hk : (Δs : ℤ) ≤ S.C.t_ S.C.k) (hA : ((S.C.t_ S.C.k : Time) : ℝ) < tA) (htA : tA ≤ (tN : ℝ))
    {s : ℕ} (hs : tN < (Model.goldilocks (V := V)).slotStart S.C s) :
    ∀ s' : ℕ, s - 1 ≤ s' → s' ≤ s →
      ∀ u ∈ honestActiveAt Model.goldilocks S (activityOf π)
        (toTrace ((Model.goldilocks (V := V)).initial S.C) π) s', u ∈ S.P.committee s' →
      u ∈ (activityOf π).activeThroughout (toTrace ((Model.goldilocks (V := V)).initial S.C) π)
        (((Model.goldilocks (V := V)).supportCutoff S.C s' -
          max (2 * GoldilocksCorrectness.Statements.Routines.Δ S) Δs : ℕ) : ℝ)
        ((((Model.goldilocks (V := V)).supportCutoff S.C s' -
          max (2 * GoldilocksCorrectness.Statements.Routines.Δ S) Δs : ℕ) : ℝ) + Δs) := by
  intro s' h1 h2 u hu hc
  have hks : S.C.k < s := k_lt_of_le_slotStart S hA htA hs.le
  have hsA : tA ≤ ((S.C.t_ (s' + 1) : Time) : ℝ) :=
    (le_slotTime_of S htA hs.le).trans (by exact_mod_cast slotTime_mono S (by omega))
  exact committee_hold_toTrace π hH hk (by omega) hsA hu hc

/-- The proposer row of `HoldersStayOnlineAfterHealing`, read on the trace at slot `s`: a proposer that
ran its slot up to the update is active throughout the window of `route-b`'s `hHoldP` of Lemma 90 and
of the asynchrony statement.

Why: the row gives it up and honest throughout `[t_s − max Δ Δs, t_s − max Δ Δs + Δs]`, active
throughout on the trace; with `S.C.k < s` the start of slot `s` is at least `Δs` and `4Δ`, so the
window's start is not negative and the model's natural window is the same.

The variables:
- `π`: the run; `Δs`: the sync delay; `tA`: the end of the healing phase; `hH`: the extra condition;
  `hk`: `Δs` is at most the start of slot `S.C.k`; `s`: the slot, after slot `S.C.k`; `hP`: its
  proposer ran it up to the update. -/
theorem proposer_hold_toTrace {Δs : ℕ} {tA : ℝ}
    (hH : HoldersStayOnlineAfterHealing S Δs tA (observeWithCommittees (Block := Block V) π))
    (hk : (Δs : ℤ) ≤ S.C.t_ S.C.k) {s : ℕ} (hks : S.C.k < s)
    (hA : tA ≤ ((S.C.t_ s : Time) : ℝ))
    (hP : HonestProposerToUpdateG S (observeWithCommittees (Block := Block V) π) s) :
    S.P.proposer s ∈ (activityOf π).activeThroughout
      (toTrace ((Model.goldilocks (V := V)).initial S.C) π)
      (((Model.goldilocks (V := V)).slotStart S.C s -
        max (GoldilocksCorrectness.Statements.Routines.Δ S) Δs : ℕ) : ℝ)
      ((((Model.goldilocks (V := V)).slotStart S.C s -
        max (GoldilocksCorrectness.Statements.Routines.Δ S) Δs : ℕ) : ℝ) + Δs) := by
  have h := activeThroughout_of_upAndHonest π (hH.proposer s hA hP)
  have hts := slotTime_mono S (show S.C.k + 1 ≤ s from hks)
  have hsucc := slotTime_succ S S.C.k
  have hΔ : (0 : ℤ) < S.C.Δ := S.C.Δ_pos
  have hΔn : ((GoldilocksCorrectness.Statements.Routines.Δ S : ℕ) : ℤ) = S.C.Δ :=
    GoldilocksCorrectness.Proofs.Routines.Δ_cast S
  have hW : ((((Model.goldilocks (V := V)).slotStart S.C s -
      max (GoldilocksCorrectness.Statements.Routines.Δ S) Δs : ℕ) : ℝ)) =
      ((S.C.t_ s - max S.C.Δ (Δs : Time) : Time) : ℝ) := by
    rw [← Int.cast_natCast]
    congr 1
    show (((S.C.t_ s).toNat - max (GoldilocksCorrectness.Statements.Routines.Δ S) Δs : ℕ) : ℤ) = _
    omega
  rw [hW]
  exact h

/-- **`hHoldP` of `lem90_healed_confirmed_until`**, from `HoldersStayOnlineAfterHealing.proposer`.

Why: a slot starting at or after `tN` is after slot `S.C.k` (`k_lt_of_le_slotStart`); an honest
opener on the trace ran its slot up to the update on the observed run
(`honestProposerToUpdateG_of_honestOpenerAt`); `proposer_hold_toTrace`.

The variables: as `hHold_toTrace`. -/
theorem hHoldP_toTrace {Δs : ℕ} {tA : ℝ} {tN : ℕ}
    (hH : HoldersStayOnlineAfterHealing S Δs tA (observeWithCommittees (Block := Block V) π))
    (hk : (Δs : ℤ) ≤ S.C.t_ S.C.k) (hA : ((S.C.t_ S.C.k : Time) : ℝ) < tA) (htA : tA ≤ (tN : ℝ))
    (t : ℕ) :
    ∀ s : ℕ, tN ≤ (Model.goldilocks (V := V)).slotStart S.C s →
      (Model.goldilocks (V := V)).supportCutoff S.C (s + 1) ≤ t →
      HonestOpenerAt Model.goldilocks S (activityOf π)
        (toTrace ((Model.goldilocks (V := V)).initial S.C) π) s →
      S.P.proposer s ∈ (activityOf π).activeThroughout
        (toTrace ((Model.goldilocks (V := V)).initial S.C) π)
        (((Model.goldilocks (V := V)).slotStart S.C s -
          max (GoldilocksCorrectness.Statements.Routines.Δ S) Δs : ℕ) : ℝ)
        ((((Model.goldilocks (V := V)).slotStart S.C s -
          max (GoldilocksCorrectness.Statements.Routines.Δ S) Δs : ℕ) : ℝ) + Δs) := by
  intro s hs _ hO
  exact proposer_hold_toTrace π hH hk (k_lt_of_le_slotStart S hA htA hs) (le_slotTime_of S htA hs)
    (honestProposerToUpdateG_of_honestOpenerAt π hO)

open Classical in
/-- **`hHoldP` of `confirmedPersists_asyncPeriod_until`**, from
`HoldersStayOnlineAfterHealing.proposer`: the proposer of the hand-over slot `s`, starting after `tN`,
that ran its slot up to the update on the trace (the statement's `hp`).

Why: `k_lt_of_le_slotStart`, `honestProposerToUpdateG_of_trace`, `proposer_hold_toTrace`.

The variables: as `hHoldV_toTrace`; `hp`: the statement's premise on the proposer. -/
theorem hHoldP_async_toTrace {Δs : ℕ} {tA : ℝ} {tN : ℕ}
    (hH : HoldersStayOnlineAfterHealing S Δs tA (observeWithCommittees (Block := Block V) π))
    (hk : (Δs : ℤ) ≤ S.C.t_ S.C.k) (hA : ((S.C.t_ S.C.k : Time) : ℝ) < tA) (htA : tA ≤ (tN : ℝ))
    {s : ℕ} (hs : tN < (Model.goldilocks (V := V)).slotStart S.C s)
    (hp : S.P.proposer s ∈ (activityOf π).activeThroughoutToTick
        (toTrace ((Model.goldilocks (V := V)).initial S.C) π) (proposal_window_start S.C s)
        ((Model.goldilocks (V := V)).supportCutoff S.C (s + 1)) ∧
      S.P.proposer s ∉ (activityOf π).corruptedAtTime
          (toTrace ((Model.goldilocks (V := V)).initial S.C) π)
          ((Model.goldilocks (V := V)).supportCutoff S.C (s + 1)) ∪
        Finset.univ.filter (fun u => ∃ (k : ℕ) (w : V),
          (toTrace ((Model.goldilocks (V := V)).initial S.C) π).lbl k =
            GoldilocksCorrectness.Statements.AbstractTrace.Event.tick w
              ((Model.goldilocks (V := V)).supportCutoff S.C (s + 1)) ∧
          w ∉ (activityOf π).corrupted k ∧ u ∈ (activityOf π).corrupted k)) :
    S.P.proposer s ∈ (activityOf π).activeThroughout
      (toTrace ((Model.goldilocks (V := V)).initial S.C) π)
      (((Model.goldilocks (V := V)).slotStart S.C s -
        max (GoldilocksCorrectness.Statements.Routines.Δ S) Δs : ℕ) : ℝ)
      ((((Model.goldilocks (V := V)).slotStart S.C s -
        max (GoldilocksCorrectness.Statements.Routines.Δ S) Δs : ℕ) : ℝ) + Δs) :=
  proposer_hold_toTrace π hH hk (k_lt_of_le_slotStart S hA htA hs.le) (le_slotTime_of S htA hs.le)
    (honestProposerToUpdateG_of_trace π hp)

/-- **`hHoldP` of `lem98_healed_finality_liveness_ofSync`**, from `FinalityHoldersStayOnline.proposer`:
the honest opener of a slot starting at or after `tN` is active from the start of its slot less the
larger of the delay and the sync delay to the sync delay after the support cutoff of the next slot.

Why: as `proposer_hold_toTrace`, at the condition's longer window, whose end, the support cutoff read
as a natural number, is the same real number.

The variables: as `hHold_toTrace`; `hH` is `FinalityHoldersStayOnline` at `Δs` and `Δs_F`. -/
theorem hHoldP_finality_toTrace {Δs Δs_F : ℕ} {tA : ℝ} {tN : ℕ}
    (hH : FinalityHoldersStayOnline S Δs Δs_F tA (observeWithCommittees (Block := Block V) π))
    (hk : (Δs : ℤ) ≤ S.C.t_ S.C.k) (hA : ((S.C.t_ S.C.k : Time) : ℝ) < tA) (htA : tA ≤ (tN : ℝ))
    (t : ℕ) :
    ∀ s : ℕ, tN ≤ (Model.goldilocks (V := V)).slotStart S.C s →
      (Model.goldilocks (V := V)).supportCutoff S.C (s + 1) ≤ t →
      HonestOpenerAt Model.goldilocks S (activityOf π)
        (toTrace ((Model.goldilocks (V := V)).initial S.C) π) s →
      S.P.proposer s ∈ (activityOf π).activeThroughout
        (toTrace ((Model.goldilocks (V := V)).initial S.C) π)
        (((Model.goldilocks (V := V)).slotStart S.C s -
          max (GoldilocksCorrectness.Statements.Routines.Δ S) Δs : ℕ) : ℝ)
        ((((Model.goldilocks (V := V)).supportCutoff S.C (s + 1) : ℕ) : ℝ) + Δs) := by
  intro s hs _ hO
  have hks : S.C.k < s := k_lt_of_le_slotStart S hA htA hs
  have h := activeThroughout_of_upAndHonest π
    (hH.proposer s (le_slotTime_of S htA hs) (honestProposerToUpdateG_of_honestOpenerAt π hO))
  have hts := slotTime_mono S (show S.C.k + 1 ≤ s from hks)
  have hsucc := slotTime_succ S S.C.k
  have hΔ : (0 : ℤ) < S.C.Δ := S.C.Δ_pos
  have hΔn : ((GoldilocksCorrectness.Statements.Routines.Δ S : ℕ) : ℤ) = S.C.Δ :=
    GoldilocksCorrectness.Proofs.Routines.Δ_cast S
  have hW : ((((Model.goldilocks (V := V)).slotStart S.C s -
      max (GoldilocksCorrectness.Statements.Routines.Δ S) Δs : ℕ) : ℝ)) =
      ((S.C.t_ s - max S.C.Δ (Δs : Time) : Time) : ℝ) := by
    rw [← Int.cast_natCast]
    congr 1
    show (((S.C.t_ s).toNat - max (GoldilocksCorrectness.Statements.Routines.Δ S) Δs : ℕ) : ℤ) = _
    omega
  rw [hW, show (((Model.goldilocks (V := V)).supportCutoff S.C (s + 1) : ℕ) : ℝ) =
      ((S.C.t_ (s + 1) + 2 * S.C.Δ : Time) : ℝ) from cutoff_toNat_cast S (s + 1)]
  exact h

/-- **`hHoldC` of `lem98_healed_finality_liveness_ofSync`**, from
`FinalityHoldersStayOnline.committeeDuties`.

Why: the honest active member is an honest active validator on the observed run; the condition's
window starts at the integer duty window start, at most the model's natural one, and ends at the
support cutoff plus `Δs`, the same real number; `activeThroughout_mono`.

The variables: `π`: the run; `Δs`, `Δs_F`: the sync delays; `tA`, `tN`: the end of the healing phase
on the observed run and as `route-b` reads it, `tA ≤ tN`; `hH`: the extra condition; `t`: the time the
statement reads up to. -/
theorem hHoldC_toTrace {Δs Δs_F : ℕ} {tA : ℝ} {tN : ℕ}
    (hH : FinalityHoldersStayOnline S Δs Δs_F tA (observeWithCommittees (Block := Block V) π))
    (htA : tA ≤ (tN : ℝ)) (t : ℕ) :
    ∀ σ' : ℕ, tN ≤ (Model.goldilocks (V := V)).slotStart S.C σ' →
      (Model.goldilocks (V := V)).supportCutoff S.C (σ' + 1) ≤ t →
      ∀ u ∈ honestActiveAt Model.goldilocks S (activityOf π)
        (toTrace ((Model.goldilocks (V := V)).initial S.C) π) σ', u ∈ S.P.committee σ' →
      u ∈ (activityOf π).activeThroughout (toTrace ((Model.goldilocks (V := V)).initial S.C) π)
        (((Model.goldilocks (V := V)).dutyWindowStart S.C σ' : ℕ) : ℝ)
        ((((Model.goldilocks (V := V)).supportCutoff S.C (σ' + 1) : ℕ) : ℝ) + Δs) := by
  intro σ' hσ _ u hu hc
  have h := activeThroughout_of_upAndHonest π
    (hH.committeeDuties σ' (le_slotTime_of S htA hσ) u hc (honestActiveG_of_mem π hu))
  refine activeThroughout_mono π (cast_le_toNat_cast _) ?_ h
  rw [show (((Model.goldilocks (V := V)).supportCutoff S.C (σ' + 1) : ℕ) : ℝ) =
      ((S.C.t_ (σ' + 1) + 2 * S.C.Δ : Time) : ℝ) from cutoff_toNat_cast S (σ' + 1)]

/-- **`hHoldQ` of `lem98_healed_finality_liveness_ofSync`**, from `FinalityHoldersStayOnline.opener`.

Why: the honest opener of the next round's first slot ran it up to the update on the observed run;
the condition's window starts at the integer proposal window start, at most the model's natural one,
and ends at the slot's start, the same real number; `activeThroughout_mono`.

The variables: as `hHoldC_toTrace`, without `t`. -/
theorem hHoldQ_toTrace {Δs Δs_F : ℕ} {tA : ℝ} {tN : ℕ}
    (hH : FinalityHoldersStayOnline S Δs Δs_F tA (observeWithCommittees (Block := Block V) π))
    (htA : tA ≤ (tN : ℝ)) :
    ∀ r' : ℕ, tN ≤ (Model.goldilocks (V := V)).slotStart S.C (r' * S.C.R) →
      HonestOpenerAt Model.goldilocks S (activityOf π)
        (toTrace ((Model.goldilocks (V := V)).initial S.C) π) ((r' + 1) * S.C.R) →
      S.P.proposer ((r' + 1) * S.C.R) ∈ (activityOf π).activeThroughout
        (toTrace ((Model.goldilocks (V := V)).initial S.C) π)
        (((Model.goldilocks (V := V)).proposalWindowStart S.C ((r' + 1) * S.C.R) : ℕ) : ℝ)
        (((Model.goldilocks (V := V)).slotStart S.C ((r' + 1) * S.C.R) : ℕ) : ℝ) := by
  intro r' hr hO
  have h := activeThroughout_of_upAndHonest π
    (hH.opener r' (le_slotTime_of S htA hr) (honestProposerToUpdateG_of_honestOpenerAt π hO))
  refine activeThroughout_mono π (cast_le_toNat_cast _) ?_ h
  rw [show (((Model.goldilocks (V := V)).slotStart S.C ((r' + 1) * S.C.R) : ℕ) : ℝ) =
      ((S.C.t_ ((r' + 1) * S.C.R) : Time) : ℝ) from slotTime_toNat_cast S _]

/-- **`hAttW` of `lem98_healed_finality_liveness_ofSync`**, from
`FinalityHoldersStayOnline.attesters`.

Why: a round whose first slot starts at or after `tN` has its first slot after slot `S.C.k`
(`k_lt_of_le_slotStart`), so the next round's first slot is too and its proposal window starts at
least one delay after time `0` (`proposal_window_start_eq_slotTime`); the model's natural window is
then the condition's.

The variables: as `hHoldC_toTrace`, without `t`; `hA`: `tA` is later than the start of slot
`S.C.k`. -/
theorem hAttW_toTrace {Δs Δs_F : ℕ} {tA : ℝ} {tN : ℕ}
    (hH : FinalityHoldersStayOnline S Δs Δs_F tA (observeWithCommittees (Block := Block V) π))
    (hA : ((S.C.t_ S.C.k : Time) : ℝ) < tA) (htA : tA ≤ (tN : ℝ)) :
    ∀ r' : ℕ, tN ≤ (Model.goldilocks (V := V)).slotStart S.C (r' * S.C.R) →
      ∀ u ∈ honestActiveAt Model.goldilocks S (activityOf π)
        (toTrace ((Model.goldilocks (V := V)).initial S.C) π) (r' * S.C.R),
      u ∈ (activityOf π).activeThroughout (toTrace ((Model.goldilocks (V := V)).initial S.C) π)
        ((Model.goldilocks (V := V)).proposalWindowStart S.C ((r' + 1) * S.C.R))
        (((Model.goldilocks (V := V)).proposalWindowStart S.C ((r' + 1) * S.C.R) : ℕ) + Δs_F) := by
  intro r' hr u hu
  have h := activeThroughout_of_upAndHonest π
    (hH.attesters r' (le_slotTime_of S htA hr) u (honestActiveG_of_mem π hu))
  have hks : S.C.k < r' * S.C.R := k_lt_of_le_slotStart S hA htA hr
  have hR : r' * S.C.R ≤ (r' + 1) * S.C.R := Nat.mul_le_mul_right _ (Nat.le_succ r')
  have hts := slotTime_mono S (show S.C.k + 1 ≤ (r' + 1) * S.C.R by omega)
  have hpw := proposal_window_start_eq_slotTime S ((r' + 1) * S.C.R)
  have hΔ : (0 : ℤ) < S.C.Δ := S.C.Δ_pos
  have h0 : (0 : ℤ) ≤ Goldilocks.proposal_window_start S.C ((r' + 1) * S.C.R) := by
    rw [hpw]; omega
  have hcast : (((Model.goldilocks (V := V)).proposalWindowStart S.C ((r' + 1) * S.C.R) : ℕ) : ℝ) =
      ((Goldilocks.proposal_window_start S.C ((r' + 1) * S.C.R) : Time) : ℝ) :=
    toNat_cast_real h0
  rw [hcast]
  exact h

omit [ProtocolCommittees (goldilocksProtocol S) (Block V)] in
open Classical in
/-- When `v` ticks to `c` somewhere on the trace, the step `x.tickStep v c` is such a tick.

The variables:
- `π`: the run; `v`: the validator; `c`: the reading; `h`: some trace step is `v`'s tick to `c`. -/
theorem lbl_tickStep_of_exists {v : V} {c : ℕ}
    (h : ∃ i : ℕ, (toTrace ((Model.goldilocks (V := V)).initial S.C) π).lbl i =
      GoldilocksCorrectness.Statements.AbstractTrace.Event.tick v c) :
    (toTrace ((Model.goldilocks (V := V)).initial S.C) π).lbl
        ((toTrace ((Model.goldilocks (V := V)).initial S.C) π).tickStep v c) =
      GoldilocksCorrectness.Statements.AbstractTrace.Event.tick v c := by
  unfold GoldilocksCorrectness.Statements.AbstractTrace.Trace.tickStep
  rw [dif_pos h]
  exact Nat.find_spec h

/-- **`hTickInputs` of `lem98_healed_finality_liveness_ofSync`**, from
`NoAttestationOfActionTickInHeldBlocks`.

Why: an honest active member `v` of the round's first slot ticks to the round's action time on the
trace, so `x.tickStep v c` is such a tick, the trace step `newIdx π k` of the run's tick at step `k`,
taken while `v`'s local state is some `l` (`Step.up_honest`); the trace's input of that tick is
`l.st` (`toTrace_st_newIdx`, `lastKnownSt_of_some`), whose tree is the tree of `v`'s view in
configuration `k` of the observed run. A signed message new on the wire at the trace step of `w`'s
tick to `c` is the trace reading of an envelope new on the wire at the run's step, with the same
sender and object; the condition excludes it.

The variables:
- `π`: the run; `tA`, `tN`: the end of the healing phase on the observed run and as `route-b` reads it,
  `tA ≤ tN`; `hN`: the condition. -/
theorem hTickInputs_toTrace {tA : ℝ} {tN : ℕ}
    (hN : NoAttestationOfActionTickInHeldBlocks S tA (observeWithCommittees (Block := Block V) π))
    (htA : tA ≤ (tN : ℝ)) :
    ∀ r' : ℕ, tN ≤ (Model.goldilocks (V := V)).slotStart S.C (r' * S.C.R) →
      HonestOpenerAt Model.goldilocks S (activityOf π)
        (toTrace ((Model.goldilocks (V := V)).initial S.C) π) (r' * S.C.R) →
      ∀ v ∈ honestActiveAt Model.goldilocks S (activityOf π)
        (toTrace ((Model.goldilocks (V := V)).initial S.C) π) (r' * S.C.R),
      ∀ Z ∈ (Model.goldilocks (V := V)).tree
        ((toTrace ((Model.goldilocks (V := V)).initial S.C) π).tickInput v
          ((Model.goldilocks (V := V)).supportCutoff S.C (r' * S.C.R + 1))),
      ∀ a ∈ Z.attestations, ∀ (j : ℕ) (w : V),
        (toTrace ((Model.goldilocks (V := V)).initial S.C) π).lbl j =
          GoldilocksCorrectness.Statements.AbstractTrace.Event.tick w
            ((Model.goldilocks (V := V)).supportCutoff S.C (r' * S.C.R + 1)) →
        (⟨w, NamedObject.attest a⟩ : Framework.StsMultisetLog.SignedMsg V (NamedObject V)) ∉
          (toTrace ((Model.goldilocks (V := V)).initial S.C) π).sent (j + 1) -
            (toTrace ((Model.goldilocks (V := V)).initial S.C) π).sent j := by
  intro r' hr hO v hv Z hZ a ha j w hj hsent
  have hvA := hv
  unfold honestActiveAt activeAt at hvA
  rw [Finset.mem_sdiff] at hvA
  have hex : ∃ i : ℕ, (toTrace ((Model.goldilocks (V := V)).initial S.C) π).lbl i =
      GoldilocksCorrectness.Statements.AbstractTrace.Event.tick v
        ((Model.goldilocks (V := V)).supportCutoff S.C (r' * S.C.R + 1)) := by
    have h1 := hvA.1
    simp only [Activity.awakeThroughoutToTick, Finset.mem_filter, Finset.mem_univ, true_and] at h1
    obtain ⟨k', hk', -⟩ := h1
    exact ⟨k', hk'⟩
  obtain ⟨k, hk, hl, hc⟩ := GoldilocksVariant.Final.exists_of_lbl_tick _ π (lbl_tickStep_of_exists π hex)
  obtain ⟨-, -, l, -, hlv, -⟩ := (π.step_at k).up_honest (Or.inl hl)
  have hin : (toTrace ((Model.goldilocks (V := V)).initial S.C) π).tickInput v
      ((Model.goldilocks (V := V)).supportCutoff S.C (r' * S.C.R + 1)) = l.st := by
    unfold GoldilocksCorrectness.Statements.AbstractTrace.Trace.tickInput
    rw [← hk]
    exact (GoldilocksVariant.Final.toTrace_st_newIdx _ π k v).trans
      (GoldilocksVariant.Final.lastKnownSt_of_some _ π hlv)
  rw [hin] at hZ
  obtain ⟨j₀, rfl, hl0, hc0⟩ := GoldilocksVariant.Final.exists_of_lbl_tick _ π hj
  have e1 : (toTrace ((Model.goldilocks (V := V)).initial S.C) π).sent (newIdx π j₀ + 1) =
      π[j₀ + 1].sent.map GoldilocksVariant.Final.traceMsg :=
    GoldilocksVariant.Final.toTrace_sent_newIdx_succ _ π j₀
  have e0 : (toTrace ((Model.goldilocks (V := V)).initial S.C) π).sent (newIdx π j₀) = π[j₀].sent.map GoldilocksVariant.Final.traceMsg :=
    GoldilocksVariant.Final.toTrace_sent_newIdx _ π j₀
  rw [e1, e0] at hsent
  have hle : π[j₀].sent ≤ π[j₀ + 1].sent := π.sent_mono (Nat.le_succ j₀)
  have hd : π[j₀ + 1].sent = π[j₀].sent + (π[j₀ + 1].sent - π[j₀].sent) :=
    (add_tsub_cancel_of_le hle).symm
  rw [hd, Multiset.map_add, add_tsub_cancel_left] at hsent
  obtain ⟨e, hnew, hetr⟩ := Multiset.mem_map.1 hsent
  have hes : e.sender = w := congrArg Framework.StsMultisetLog.SignedMsg.sender hetr
  have hem : e.msg = NamedObject.attest a := congrArg Framework.StsMultisetLog.SignedMsg.msg hetr
  exact hN r' (le_slotTime_of S htA hr) (honestProposerToUpdateG_of_honestOpenerAt π hO) v
    (honestActiveG_of_mem π hv) k (NodeViewOf.view l.st) ⟨hl, hc⟩
    (Option.map_eq_some_iff.mpr ⟨l, hlv, rfl⟩) Z hZ a ha j₀ w e ⟨hl0, hc0⟩ hnew hes hem

omit [ProtocolCommittees (goldilocksProtocol S) (Block V)] [RootOrder] in
/-- After the start of the healing phase's honest round opening slots, every slot's duties start at
or after the start of the phase: the window of slot `σ`'s duties starts at or after `tGAT` when slot
`σ` is at or after a slot `s₀` starting at or after `tGAT + 4Δ · healFrontSlots S`.

Why: `duty_window_start S.C σ = t_σ + Δ − 4Δk ≥ tGAT + 4Δ(3k + 1) + Δ − 4Δk ≥ tGAT`.

The variables:
- `tGAT`: the start of the phase; `s₀`, `σ`: the slots, `s₀ ≤ σ`; `hfirst`: slot `s₀` starts at or
  after `tGAT + 4Δ · healFrontSlots S`. -/
theorem le_duty_window_start_of_first {tGAT : ℝ} {s₀ σ : ℕ}
    (hfirst : tGAT + 4 * ((S.C.Δ : Time) : ℝ) * (GoldilocksCorrectness.Statements.Executions.healFrontSlots S : ℕ) ≤ ((S.C.t_ s₀ : Time) : ℝ))
    (h : s₀ ≤ σ) : tGAT ≤ ((duty_window_start S.C σ : Time) : ℝ) := by
  have hm : ((S.C.t_ s₀ : Time) : ℝ) ≤ ((S.C.t_ σ : Time) : ℝ) := by
    exact_mod_cast slotTime_mono S h
  have hΔ : (0 : ℝ) < ((S.C.Δ : Time) : ℝ) := by exact_mod_cast S.C.Δ_pos
  have hk : ((S.C.t_ S.C.k : Time) : ℝ) = 4 * ((S.C.Δ : Time) : ℝ) * (S.C.k : ℝ) := by
    rw [slotTime_eq]; push_cast; ring
  have hhf : ((GoldilocksCorrectness.Statements.Executions.healFrontSlots S : ℕ) : ℝ) = 3 * (S.C.k : ℝ) + 1 := by
    simp [GoldilocksCorrectness.Statements.Executions.healFrontSlots]
  rw [duty_window_start_eq_slotTime]
  push_cast
  rw [hk]
  rw [hhf] at hfirst
  have hK : (0 : ℝ) ≤ (S.C.k : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_nonneg hΔ.le hK]

/-- **`hStay` of the top statements**, from `HoldersStayOnline.updaters`: every updater of a slot from
the first honest round opening slot on is active for `Δs` after the real time of its tick to the
support cutoff of the next slot.

Why: the slot's duties start at or after `tGAT` (`le_duty_window_start_of_first`); an updater ticks to
the cutoff on the trace, so `x.tickStep u c` is such a tick, the run's tick at some step `k`, at the
real time `π.stamp (k + 1)`, taken while `u` is outside the corrupted set (`Step.up_honest`); the
condition gives `u` up and honest from that time for `max Δ Δs ≥ Δs`.

The variables:
- `π`: the run; `Δs`, `Δs_F`: the sync delays; `ΔClockBehind`: the clock's lag bound; `tGAT`, `tA`:
  the healing phase; `hH`: the extra condition; `r`: the rounds of the honest round opening slots;
  `hfirst`: the first one starts at or after `tGAT + 4Δ · healFrontSlots S`; `t`: the time the
  statement reads up to. -/
theorem hStay_toTrace {Δs Δs_F : ℕ} {ΔClockBehind tGAT tA : ℝ}
    (hH : HoldersStayOnline S Δs Δs_F ΔClockBehind tGAT tA (observeWithCommittees (Block := Block V) π))
    {r : ℕ → ℕ}
    (hfirst : tGAT + 4 * ((S.C.Δ : Time) : ℝ) * (GoldilocksCorrectness.Statements.Executions.healFrontSlots S : ℕ) ≤
      ((S.C.t_ (r 0 * S.C.R) : Time) : ℝ))
    (t : ℕ) :
    ∀ σ : ℕ, r 0 * S.C.R ≤ σ → (Model.goldilocks (V := V)).supportCutoff S.C (σ + 1) ≤ t →
      ∀ u ∈ GoldilocksCorrectness.Record.Statements.AbstractTrace.updaterAt Model.goldilocks S
        (activityOf π) (toTrace ((Model.goldilocks (V := V)).initial S.C) π) σ,
      u ∈ (activityOf π).activeThroughout (toTrace ((Model.goldilocks (V := V)).initial S.C) π)
        ((toTrace ((Model.goldilocks (V := V)).initial S.C) π).time
          ((toTrace ((Model.goldilocks (V := V)).initial S.C) π).tickStep u
            ((Model.goldilocks (V := V)).supportCutoff S.C (σ + 1))))
        ((toTrace ((Model.goldilocks (V := V)).initial S.C) π).time
          ((toTrace ((Model.goldilocks (V := V)).initial S.C) π).tickStep u
            ((Model.goldilocks (V := V)).supportCutoff S.C (σ + 1))) + Δs) := by
  intro σ hσ _ u hu
  have hex : ∃ i : ℕ, (toTrace ((Model.goldilocks (V := V)).initial S.C) π).lbl i =
      GoldilocksCorrectness.Statements.AbstractTrace.Event.tick u
        ((Model.goldilocks (V := V)).supportCutoff S.C (σ + 1)) := by
    unfold GoldilocksCorrectness.Record.Statements.AbstractTrace.updaterAt at hu
    simp only [Activity.activeThroughoutToTick, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    obtain ⟨k', hk', -⟩ := hu
    exact ⟨k', hk'⟩
  obtain ⟨k, hk, hl, hc⟩ := GoldilocksVariant.Final.exists_of_lbl_tick _ π (lbl_tickStep_of_exists π hex)
  obtain ⟨hadv, -, -⟩ := (π.step_at k).up_honest (Or.inl hl)
  have h := activeThroughout_of_upAndHonest π
    (hH.updaters σ (le_duty_window_start_of_first hfirst hσ) k u ⟨hl, hc⟩ hadv)
  have et : (toTrace ((Model.goldilocks (V := V)).initial S.C) π).time (newIdx π k) = π.stamp (k + 1) :=
    GoldilocksVariant.Final.toTrace_time_newIdx _ π k
  rw [← hk, et]
  have hst : RStsVariant2.Observable.stamp (observeWithCommittees (Block := Block V) π) (k + 1) =
      π.stamp (k + 1) := rfl
  exact activeThroughout_mono π hst.ge
    (by rw [hst]; have := le_max_right ((S.C.Δ : Time) : ℝ) (Δs : ℝ); linarith) h

omit [ProtocolCommittees (goldilocksProtocol S) (Block V)] in
/-- The time after a trace step is at most the real time at which the run's configuration that step
reads is left.

Why: after a step of the run, the trace keeps that step's time (`toTrace_time_newIdx_succ`); after a
step of the kind `other`, the configuration is the same (`toTrace_time_mem`).

The variables:
- `π`: the run; `j`: the trace step. -/
theorem toTrace_time_succ_le (j : ℕ) :
    (toTrace ((Model.goldilocks (V := V)).initial S.C) π).time (j + 1) ≤
      π.stamp (origBefore π j + 1) := by
  rcases GoldilocksVariant.Final.newIdx_or_other (NodeState := NodeState V)
      (fun w => (Model.goldilocks (V := V)).initial S.C w) π j with ⟨k, hk⟩ | ⟨-, he⟩
  · have ho : origBefore π j = k := by rw [← hk]; exact GoldilocksVariant.Final.origBefore_newIdx π k
    rw [ho, ← hk]
    exact (GoldilocksVariant.Final.toTrace_time_newIdx_succ _ π k).le
  · have hm1 := GoldilocksVariant.Final.toTrace_time_mem
      (fun w => (Model.goldilocks (V := V)).initial S.C w) π (j + 1)
    erw [he] at hm1
    exact hm1.2

/-- **`hAwake` of the top statements**, from `HealingPhaseG` (the condition every top statement takes):
every validator outside the adversary set in a configuration of the trace in force at a time from
`tGATn` to `tN` is awake in it, when `[tGATn, tN]` is inside the phase `[tGAT, tA]`.

Why: the trace step reads the run's configuration `origBefore π j`, entered by the step's time (at
most `tN ≤ tA`) and left at or after the time after it (at least `tGATn ≥ tGAT`); there the honest
validator is up.

The variables:
- `π`: the run; `tGST`, `tGAT`, `tA`: the condition's times; `tGATn`, `tN`: the phase as `route-b`
  reads it. -/
theorem hAwake_toTrace {tGST tGAT tA : ℝ} {tGATn tN : ℕ}
    (hP : RStsVariant2.HealingPhaseG tGST tGAT tA (observeWithCommittees (Block := Block V) π))
    (hG : tGAT ≤ (tGATn : ℝ)) (hN : (tN : ℝ) ≤ tA) :
    ∀ (i : ℕ) (v : V), (toTrace ((Model.goldilocks (V := V)).initial S.C) π).time i ≤ tN →
      (tGATn : ℝ) ≤ (toTrace ((Model.goldilocks (V := V)).initial S.C) π).time (i + 1) →
      v ∉ (activityOf π).corrupted i → v ∈ (activityOf π).awake i := by
  intro i v h1 h2 hv
  rw [GoldilocksVariant.Final.corrupted_activityOf] at hv
  have hm := GoldilocksVariant.Final.toTrace_time_mem
    (fun w => (Model.goldilocks (V := V)).initial S.C w) π i
  obtain ⟨hc, hs⟩ := hP.2.2 (origBefore π i) v
    (hG.trans (h2.trans (toTrace_time_succ_le π i))) (hm.1.trans (h1.trans hN)) hv
  rw [GoldilocksVariant.Final.mem_awake_activityOf]
  exact ⟨hc, (state_observeWithCommittees_ne_none π _ v).1 hs⟩

/-- **`hGST` of the top statements**: the trace's `GST`, `⌈tGST⌉₊` (the time the delivery promises are
read at, `envFactsDelivery_of_conditions`), is at most a natural `tGATn` at least the start of the
phase, from `HealingPhaseG`'s first conjunct.

The variables:
- `π`: the run; `tGST`, `tGAT`, `tA`: the condition's times; `tGATn`: the start of the phase as
  `route-b` reads it. -/
theorem hGST_toTrace {tGST tGAT tA : ℝ} {tGATn : ℕ}
    (hP : RStsVariant2.HealingPhaseG tGST tGAT tA (observeWithCommittees (Block := Block V) π))
    (hG : tGAT ≤ (tGATn : ℝ)) : ⌈tGST⌉₊ ≤ tGATn :=
  Nat.ceil_le.2 (hP.1.trans hG)

/-- **`hTicks₀` of `confirmedPersists_asyncPeriod_until`**, from `ActsWithinSkewG` (the condition
every top statement takes): every tick to the hand-over update, the support cutoff of slot `s + 1`, is
at a real time at most that cutoff plus `ΔClockBehind`, Goldilocks's `tPreAsync` (T-B4-4), so at most
`b₀` when `tPreAsync ≤ b₀`.

The variables:
- `π`: the run; `ΔClockBehind`: the clock's lag bound; `hActs`: the condition; `s`: the hand-over
  slot; `b₀`: the start of the period as `route-b` reads it; `hb`: `tPreAsync ≤ b₀`. -/
theorem hTicks₀_toTrace {ΔClockBehind : ℝ}
    (hActs : RStsVariant2.ActsWithinSkewG ΔClockBehind (observeWithCommittees (Block := Block V) π))
    {s b₀ : ℕ} (hb : ((S.C.t_ (s + 1) + 2 * S.C.Δ : Time) : ℝ) + ΔClockBehind ≤ (b₀ : ℝ)) :
    ∀ (k : ℕ) (u : V), (toTrace ((Model.goldilocks (V := V)).initial S.C) π).lbl k =
        GoldilocksCorrectness.Statements.AbstractTrace.Event.tick u
          ((Model.goldilocks (V := V)).supportCutoff S.C (s + 1)) →
      ((toTrace ((Model.goldilocks (V := V)).initial S.C) π).time k : ℝ) ≤ b₀ := by
  intro k u hk
  obtain ⟨k₀, rfl, hl, hc⟩ := GoldilocksVariant.Final.exists_of_lbl_tick _ π hk
  have et : (toTrace ((Model.goldilocks (V := V)).initial S.C) π).time (newIdx π k₀) = π.stamp (k₀ + 1) :=
    GoldilocksVariant.Final.toTrace_time_newIdx _ π k₀
  rw [et]
  have h := hActs k₀ u _ (Or.inl hl) hc
  have hcut : (((Model.goldilocks (V := V)).supportCutoff S.C (s + 1) : ℕ) : ℝ) =
      ((S.C.t_ (s + 1) + 2 * S.C.Δ : Time) : ℝ) := cutoff_toNat_cast S (s + 1)
  exact h.trans (by rw [hcut]; exact hb)

omit [ProtocolCommittees (goldilocksProtocol S) (Block V)] in
/-- Every natural time `c ≥ 1` is the time after some trace step.

Why: some configuration `i` of the run is in force at `c` (the first one left at or after `c`, the run's
real time growing without bound), and the trace step `2 i + c` moves the time to `c`
(`toTrace_time_of_inForce`).

The variables:
- `π`: the run; `c`: the time. -/
theorem exists_toTrace_time_eq (c : ℕ) (hc : 1 ≤ c) :
    ∃ j : ℕ, (toTrace ((Model.goldilocks (V := V)).initial S.C) π).time j = c := by
  have hex : ∃ i : ℕ, (c : ℝ) ≤ π.stamp (i + 1) := by
    obtain ⟨i, hi⟩ := π.progress c
    exact ⟨i, hi.trans (π.mono i)⟩
  have hin : π.InForce (Nat.find hex) (c : ℝ) := by
    refine ⟨?_, Nat.find_spec hex⟩
    rcases h : Nat.find hex with _ | j
    · rw [π.stamp_zero]; exact_mod_cast hc
    · have := Nat.find_min hex (show j < Nat.find hex by omega)
      exact lt_of_not_ge this
  exact ⟨_, (GoldilocksVariant.Final.toTrace_time_of_inForce _ π hc hin).2.2.2⟩

omit [ProtocolCommittees (goldilocksProtocol S) (Block V)] in
/-- **`hWin` of `confirmedPersists_asyncPeriod_until`**: some trace step's time lies in
`[c, c + ΔClockBehind]` with `c` the hand-over update, the support cutoff of slot `s + 1`.

Why: `c ≥ 2Δ ≥ 1` is the time after some trace step (`exists_toTrace_time_eq`).

The variables:
- `π`: the run; `ΔClockBehind`: the clock's lag bound, at least `0`; `s`: the hand-over slot. -/
theorem hWin_toTrace {ΔClockBehind : ℝ} (hCB : 0 ≤ ΔClockBehind) (s : ℕ) :
    ∃ j₀ : ℕ, (((Model.goldilocks (V := V)).supportCutoff S.C (s + 1) : ℕ) : ℝ) ≤
        (toTrace ((Model.goldilocks (V := V)).initial S.C) π).time j₀ ∧
      (toTrace ((Model.goldilocks (V := V)).initial S.C) π).time j₀ ≤
        (((Model.goldilocks (V := V)).supportCutoff S.C (s + 1) : ℕ) : ℝ) + ΔClockBehind := by
  have h1 : 1 ≤ (Model.goldilocks (V := V)).supportCutoff S.C (s + 1) := by
    have hΔ : (0 : ℤ) < S.C.Δ := S.C.Δ_pos
    have h0 := slotTime_nonneg S (s + 1)
    show 1 ≤ (S.C.t_ (s + 1) + 2 * S.C.Δ).toNat
    omega
  obtain ⟨j, hj⟩ := exists_toTrace_time_eq π _ h1
  exact ⟨j, hj.ge, by rw [hj]; linarith⟩

omit [ProtocolCommittees (goldilocksProtocol S) (Block V)] [RootOrder] in
/-- **`hParam` of `lem98_healed_finality_liveness_ofSync`**, from the second conjunct of
`goldilocksFinalityLivenessHealingConditions` (Goldilocks's room for a round's attestations to reach the
next proposer), the model's natural delays being the spec's.

The variables:
- `ΔClockAhead`, `ΔClockBehind`: the clock bounds; `h`: the conjunct. -/
theorem hParam_toTrace {ΔClockAhead ΔClockBehind : ℝ}
    (h : ((S.C.Δ_F : Time) : ℝ) + ((S.C.Δ : Time) : ℝ) + ΔClockAhead + ΔClockBehind <
      4 * ((S.C.Δ : Time) : ℝ) * (S.C.k + 1)) :
    ((GoldilocksCorrectness.Statements.Routines.Δ_F S : ℕ) : ℝ) +
        (GoldilocksCorrectness.Statements.Routines.Δ S : ℝ) + ΔClockAhead + ΔClockBehind <
      4 * (GoldilocksCorrectness.Statements.Routines.Δ S : ℝ) * (S.C.k + 1) := by
  have h1 : ((GoldilocksCorrectness.Statements.Routines.Δ S : ℕ) : ℝ) = ((S.C.Δ : Time) : ℝ) := by
    rw [← Int.cast_natCast, GoldilocksCorrectness.Proofs.Routines.Δ_cast]
  have h2 : ((GoldilocksCorrectness.Statements.Routines.Δ_F S : ℕ) : ℝ) = ((S.C.Δ_F : Time) : ℝ) := by
    rw [← Int.cast_natCast, GoldilocksCorrectness.Proofs.Routines.Δ_F_cast]
  rw [h1, h2]
  exact h

omit [DecidableEq V] [Fintype V] [RootOrder] in
/-- Increasing rounds: from `r i < r (i + 1)` for every `i < m`, `r i ≤ r j` whenever `i ≤ j ≤ m`.

The variables:
- `r`: the rounds; `m`: the index of the last one; `hmono`: they increase. -/
theorem rounds_le {r : ℕ → ℕ} {m : ℕ} (hmono : ∀ i : ℕ, i < m → r i < r (i + 1)) :
    ∀ i j : ℕ, i ≤ j → j ≤ m → r i ≤ r j := by
  intro i j hij hjm
  induction j with
  | zero => rw [Nat.le_zero.1 hij]
  | succ j ih =>
    rcases Nat.of_le_succ hij with h | h
    · exact (ih h (by omega)).trans (hmono j (by omega)).le
    · rw [h]

omit [DecidableEq V] [Fintype V] [RootOrder] in
/-- Increasing rounds: `r i < r m` for every `i < m`.

The variables: as `rounds_le`. -/
theorem rounds_lt_last {r : ℕ → ℕ} {m : ℕ} (hmono : ∀ i : ℕ, i < m → r i < r (i + 1)) :
    ∀ i : ℕ, i < m → r i < r m := fun i hi =>
  (hmono i hi).trans_le (rounds_le hmono (i + 1) m hi le_rfl)

/-- **`hSeq` of the top statements**: Goldilocks's honest round opening slots on the healing-phase
segment (`HonestOpeningSeqOn`) are `route-b`'s `HonestOpeningSeq` on the trace, read at a natural
`tFirstN` at most every natural number at least `tF + ΔClockAhead`, and a natural `tN` at least the
last opening's support cutoff plus `ΔClockBehind`.

Why: `mono` and `spacing` are the same; `first` from the segment's `first` (the first opening's slot
starts at least `ΔClockAhead` after `tF`, and its start is a natural number); `last` and `lastTick`
from `hN` and `ActsWithinSkewG` (a tick at a reading `c` is at a real time at most
`c + ΔClockBehind`); `honest`:
a proposer corrupted after a trace step at a time at most the cutoff `C` of its slot is corrupted in
the run's configuration that step reads, entered by `C`, so (corruption being permanent) in a
configuration of the segment entered by `C`: that one if it is left at or after `tGAT`, otherwise the
first configuration left at or after `C ≥ tGAT`.

The variables:
- `π`: the run; `ΔClockAhead`, `ΔClockBehind`: the clock bounds; `tGAT`, `tA`: the healing phase of
  the segment; `tF`: the segment's earliest start of the first opening, less `ΔClockAhead`; `r`, `m`:
  the openings; `tFirstN`, `tN`: `route-b`'s natural times; `hseq`: the segment's openings; `hActs`:
  the condition; `hF`: `tFirstN` is at most every natural number at least `tF + ΔClockAhead`; `hN`:
  the last opening's support cutoff plus `ΔClockBehind` is at most `tN`; `hG`: the first opening
  starts at or after `tGAT`. -/
theorem hSeq_toTrace {ΔClockAhead ΔClockBehind tGAT tA tF : ℝ} (hCB : 0 ≤ ΔClockBehind)
    {r : ℕ → ℕ} {m : ℕ} {tFirstN tN : ℕ}
    (hseq : HonestOpeningSeqOn S
      (phaseSegment (observeWithCommittees (Block := Block V) π) tGAT tA) r m ΔClockAhead
        ΔClockBehind tF tA)
    (hActs : RStsVariant2.ActsWithinSkewG ΔClockBehind (observeWithCommittees (Block := Block V) π))
    (hF : ∀ n : ℕ, tF + ΔClockAhead ≤ (n : ℝ) → tFirstN ≤ n)
    (hN : ((S.C.t_ (r m * S.C.R) + 2 * S.C.Δ : Time) : ℝ) + ΔClockBehind ≤ (tN : ℝ))
    (hG : tGAT ≤ ((S.C.t_ (r 0 * S.C.R) : Time) : ℝ)) :
    GoldilocksCorrectness.Record.Statements.Executions.HonestOpeningSeq Model.goldilocks S
      (activityOf π) (toTrace ((Model.goldilocks (V := V)).initial S.C) π) r m tFirstN tN := by
  have hcutm : (((Model.goldilocks (V := V)).supportCutoff S.C (r m * S.C.R) : ℕ) : ℝ) =
      ((S.C.t_ (r m * S.C.R) + 2 * S.C.Δ : Time) : ℝ) := cutoff_toNat_cast S _
  have hlast := hseq.last
  refine ⟨hseq.mono, ?_, ?_, ?_, ?_, hseq.spacing⟩
  · -- first
    apply hF
    rw [show (((Model.goldilocks (V := V)).slotStart S.C (r 0 * S.C.R) : ℕ) : ℝ) =
      ((S.C.t_ (r 0 * S.C.R) : Time) : ℝ) from slotTime_toNat_cast S _]
    exact hseq.first
  · -- last
    have h1 : (((Model.goldilocks (V := V)).supportCutoff S.C (r m * S.C.R) : ℕ) : ℝ) ≤ (tN : ℝ) := by
      rw [hcutm]; linarith
    exact_mod_cast h1
  · -- lastTick
    intro k u c hk hc
    obtain ⟨k₀, rfl, hl, hcl⟩ := GoldilocksVariant.Final.exists_of_lbl_tick _ π hk
    have et : (toTrace ((Model.goldilocks (V := V)).initial S.C) π).time (newIdx π k₀) =
        π.stamp (k₀ + 1) := GoldilocksVariant.Final.toTrace_time_newIdx _ π k₀
    rw [et]
    have h1 := hActs k₀ u c (Or.inl hl) hcl
    have h2 : (c : ℝ) ≤ ((S.C.t_ (r m * S.C.R) + 2 * S.C.Δ : Time) : ℝ) := by
      rw [← hcutm]; exact_mod_cast hc
    exact h1.trans (by linarith)
  · -- honest
    intro i hi hmem
    simp only [Activity.corruptedAtTime, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    obtain ⟨j, hj, hc⟩ := hmem
    rw [GoldilocksVariant.Final.corrupted_activityOf] at hc
    set C : ℝ := ((S.C.t_ (r i * S.C.R) + 2 * S.C.Δ : Time) : ℝ) with hCdef
    have hjC : (toTrace ((Model.goldilocks (V := V)).initial S.C) π).time j ≤ C := by
      rw [hCdef, ← cutoff_toNat_cast S (r i * S.C.R)]; exact hj
    have hoC : π.stamp (origBefore π j) ≤ C :=
      (GoldilocksVariant.Final.toTrace_time_mem _ π j).1.trans hjC
    have hri : r 0 * S.C.R ≤ r i * S.C.R :=
      Nat.mul_le_mul_right _ (rounds_le hseq.mono 0 i (Nat.zero_le _) hi)
    have hrm : r i * S.C.R ≤ r m * S.C.R :=
      Nat.mul_le_mul_right _ (rounds_le hseq.mono i m hi le_rfl)
    have hΔ : (0 : ℝ) < ((S.C.Δ : Time) : ℝ) := by exact_mod_cast S.C.Δ_pos
    have hGC : tGAT ≤ C := by
      have : ((S.C.t_ (r 0 * S.C.R) : Time) : ℝ) ≤ ((S.C.t_ (r i * S.C.R) : Time) : ℝ) := by
        exact_mod_cast slotTime_mono S hri
      rw [hCdef]; push_cast; linarith
    have hCA : C ≤ tA := by
      have : ((S.C.t_ (r i * S.C.R) : Time) : ℝ) ≤ ((S.C.t_ (r m * S.C.R) : Time) : ℝ) := by
        exact_mod_cast slotTime_mono S hrm
      have hl' := hlast
      push_cast at hl'
      rw [hCdef]; push_cast; linarith
    -- a configuration of the segment entered by `C`, at or after `origBefore π j`
    obtain ⟨o', hoo', h1, h2⟩ : ∃ o' : ℕ, origBefore π j ≤ o' ∧ tGAT ≤ π.stamp (o' + 1) ∧
        π.stamp o' ≤ C := by
      by_cases hle : tGAT ≤ π.stamp (origBefore π j + 1)
      · exact ⟨_, le_rfl, hle, hoC⟩
      · have hex : ∃ n : ℕ, C ≤ π.stamp (n + 1) := by
          obtain ⟨n, hn⟩ := π.progress C
          exact ⟨n, hn.trans (π.mono n)⟩
        refine ⟨Nat.find hex, ?_, hGC.trans (Nat.find_spec hex), ?_⟩
        · by_contra hlt
          have := π.stamp_mono (show Nat.find hex + 1 ≤ origBefore π j + 1 by omega)
          have := Nat.find_spec hex
          linarith [not_le.mp hle]
        · rcases h : Nat.find hex with _ | n
          · rw [π.stamp_zero]
            have := π.stamp_nonneg (origBefore π j)
            linarith
          · have := Nat.find_min hex (show n < Nat.find hex by omega)
            exact (not_le.mp this).le
    have hhon := hseq.honest i hi o' _
      (by unfold phaseSegment; exact if_pos ⟨h1, h2.trans hCA⟩) h2
    exact hhon (π.adv_mono hoo' hc)

/-- **`hHoldF` of the top statements**, from `HoldersStayOnline.attesters`: at each honest round
opening slot before the last, every validator outside the trace's adversary set by the support cutoff
of the slot after it is active through the attestations' sync delay after the later of the slot's duty
window start and `GST`.

Why: the slot's duties start at or after `tGAT` (`le_duty_window_start_of_first`), and the support
cutoff of the slot after it is at most the last opening's cutoff, at most `tA` (`HonestOpeningSeqOn`'s
`mono` and `last`); the validator is honest up to that cutoff on the observed run; the condition gives
it up and honest from the duty window's start for `Δs_F`. That start is at least `tGAT ≥ GST ≥ 0`, so
the model's natural `max (dutyWindowStart) GST` is the same real number.

The variables:
- `π`: the run; `Δs`, `Δs_F`: the sync delays; `ΔClockAhead`, `ΔClockBehind`: the clock bounds;
  `tGAT`, `tA`: the healing phase; `hH`: the extra condition; `seg`, `r`, `m`: the segment and its
  openings; `hseq`: the openings, from `ΔClockAhead` after `tGAT + 4Δ · healFrontSlots S`; `GST`: `route-b`'s time from which the
  network is synchronous, at most `tGAT`. -/
theorem hHoldF_toTrace {Δs Δs_F : ℕ} {ΔClockAhead ΔClockBehind tGAT tA : ℝ}
    (hCA : 0 ≤ ΔClockAhead) (hCB : 0 ≤ ΔClockBehind)
    (hH : HoldersStayOnline S Δs Δs_F ΔClockBehind tGAT tA (observeWithCommittees (Block := Block V) π))
    {seg : ℕ → Option (PhaseStep V (NamedObject V) (Block V))} {r : ℕ → ℕ} {m : ℕ}
    (hseq : HonestOpeningSeqOn S seg r m ΔClockAhead ΔClockBehind
      (tGAT + 4 * ((S.C.Δ : Time) : ℝ) *
        (GoldilocksCorrectness.Statements.Executions.healFrontSlots S : ℕ)) tA)
    {GST : ℕ} (hGST : (GST : ℝ) ≤ tGAT) :
    ∀ i, i < m → ∀ v, v ∉ (activityOf π).corruptedAtTime
        (toTrace ((Model.goldilocks (V := V)).initial S.C) π)
        (((Model.goldilocks (V := V)).supportCutoff S.C (r i * S.C.R + 1) : ℕ) : ℝ) →
      v ∈ (activityOf π).activeThroughout (toTrace ((Model.goldilocks (V := V)).initial S.C) π)
        ((max ((Model.goldilocks (V := V)).dutyWindowStart S.C (r i * S.C.R)) GST : ℕ) : ℝ)
        (((max ((Model.goldilocks (V := V)).dutyWindowStart S.C (r i * S.C.R)) GST : ℕ) : ℝ) +
          Δs_F) := by
  intro i hi v hv
  have hri : r 0 * S.C.R ≤ r i * S.C.R :=
    Nat.mul_le_mul_right _ (rounds_le hseq.mono 0 i (Nat.zero_le _) hi.le)
  have hdws := le_duty_window_start_of_first (tGAT := tGAT) (by linarith [hseq.first]) hri
  have hR : 1 ≤ S.C.R := by have := S.C.R_ge_two; omega
  have hrm : r i * S.C.R + 1 ≤ r m * S.C.R := by
    have h := rounds_lt_last hseq.mono i hi
    have : (r i + 1) * S.C.R ≤ r m * S.C.R := Nat.mul_le_mul_right _ h
    rw [Nat.add_mul, one_mul] at this
    omega
  have hcut : ((S.C.t_ (r i * S.C.R + 1) + 2 * S.C.Δ : Time) : ℝ) ≤ tA := by
    have h1 : ((S.C.t_ (r i * S.C.R + 1) : Time) : ℝ) ≤ ((S.C.t_ (r m * S.C.R) : Time) : ℝ) := by
      exact_mod_cast slotTime_mono S hrm
    have hl := hseq.last
    push_cast at hl ⊢
    linarith
  have hhon : HonestByG (observeWithCommittees (Block := Block V) π)
      ((S.C.t_ (r i * S.C.R + 1) + 2 * S.C.Δ : Time) : ℝ) v := by
    have := honestByG_of_not_mem_corruptedAtTime π hv
    rwa [show (((Model.goldilocks (V := V)).supportCutoff S.C (r i * S.C.R + 1) : ℕ) : ℝ) =
      ((S.C.t_ (r i * S.C.R + 1) + 2 * S.C.Δ : Time) : ℝ) from cutoff_toNat_cast S _] at this
  have h := activeThroughout_of_upAndHonest π (hH.attesters (r i) hdws hcut v hhon)
  have h0 : (0 : ℤ) ≤ Goldilocks.duty_window_start S.C (r i * S.C.R) := by
    have : (0 : ℝ) ≤ ((Goldilocks.duty_window_start S.C (r i * S.C.R) : Time) : ℝ) :=
      ((Nat.cast_nonneg GST).trans hGST).trans hdws
    exact_mod_cast this
  have hc : (((Model.goldilocks (V := V)).dutyWindowStart S.C (r i * S.C.R) : ℕ) : ℝ) =
      ((Goldilocks.duty_window_start S.C (r i * S.C.R) : Time) : ℝ) := toNat_cast_real h0
  have hGle : GST ≤ (Model.goldilocks (V := V)).dutyWindowStart S.C (r i * S.C.R) := by
    have : (GST : ℝ) ≤ (((Model.goldilocks (V := V)).dutyWindowStart S.C (r i * S.C.R) : ℕ) : ℝ) := by
      rw [hc]; exact hGST.trans hdws
    exact_mod_cast this
  rw [max_eq_left hGle, hc]
  exact h

omit [ProtocolCommittees (goldilocksProtocol S) (Block V)] in
/-- Every natural time `c`, less a clock bound that is not negative, to `c` plus another, holds the
time after some trace step.

Why: at `c = 0` the trace's first time `0`; otherwise `exists_toTrace_time_eq`.

The variables:
- `π`: the run; `ΔClockAhead`, `ΔClockBehind`: the bounds; `c`: the time. -/
theorem exists_toTrace_time_mem_window {ΔClockAhead ΔClockBehind : ℝ} (hCA : 0 ≤ ΔClockAhead)
    (hCB : 0 ≤ ΔClockBehind) (c : ℕ) :
    ∃ i : ℕ, (c : ℝ) - ΔClockAhead ≤ (toTrace ((Model.goldilocks (V := V)).initial S.C) π).time i ∧
      (toTrace ((Model.goldilocks (V := V)).initial S.C) π).time i ≤ c + ΔClockBehind := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · refine ⟨0, ?_, ?_⟩ <;>
      rw [GoldilocksVariant.Final.toTrace_time_zero] <;> push_cast <;> linarith
  · obtain ⟨j, hj⟩ := exists_toTrace_time_eq π c hc
    exact ⟨j, by rw [hj]; linarith, by rw [hj]; linarith⟩

/-- A validator up and honest on the observed run throughout `[a, b]` ticks, on the trace, at every
natural reading `c` with `[c − ΔClockAhead, c + ΔClockBehind]` inside `[a, b]`, at a trace step whose
time is in that window.

Why: it is active on the trace throughout `[a, b]` (`activeThroughout_of_upAndHonest`), so at every
trace step whose time is in the window; some trace step has its time in the window
(`exists_toTrace_time_mem_window`); `toTrace_tick_of_active_of_time_mem`.

The variables:
- `π`: the run; `ΔClockAhead`, `ΔClockBehind`: the clock bounds; `hSkew`, `hAdv`, `hTicks`: the
  clock conditions on the run; `a`, `b`: the window; `c`: the reading; `v`: the validator. -/
theorem trace_tick_of_upAndHonest {ΔClockAhead ΔClockBehind : ℝ} (hCA : 0 ≤ ΔClockAhead)
    (hCB : 0 ≤ ΔClockBehind)
    (hSkew : RStsVariant2.ClockWithinSkew ΔClockAhead ΔClockBehind π)
    (hAdv : RStsVariant2.ClockAdvancesWithin ΔClockAhead ΔClockBehind π)
    (hTicks : RStsVariant2.TicksWithin ΔClockBehind π) {a b : ℝ} {c : ℕ} {v : V}
    (h : RStsVariant2.UpAndHonestThroughoutG (observeWithCommittees (Block := Block V) π) a b v)
    (ha : a ≤ (c : ℝ) - ΔClockAhead) (hb : (c : ℝ) + ΔClockBehind ≤ b) :
    ∃ i : ℕ, (toTrace ((Model.goldilocks (V := V)).initial S.C) π).lbl i =
        GoldilocksCorrectness.Statements.AbstractTrace.Event.tick v c ∧
      (c : ℝ) - ΔClockAhead ≤ (toTrace ((Model.goldilocks (V := V)).initial S.C) π).time i ∧
      (toTrace ((Model.goldilocks (V := V)).initial S.C) π).time i ≤ c + ΔClockBehind := by
  have hA := activeThroughout_of_upAndHonest π h
  simp only [Activity.activeThroughout, Finset.mem_filter, Finset.mem_univ, true_and] at hA
  exact GoldilocksVariant.Final.toTrace_tick_of_active_of_time_mem π _ ΔClockAhead ΔClockBehind
    hSkew hAdv hTicks c v
    (fun i h1 h2 => hA i (h2.trans hb) (ha.trans (h1.trans
      (GoldilocksVariant.Final.toTrace_time_le_succ _ π i))))
    (exists_toTrace_time_mem_window π hCA hCB c)

/-- In the phase, a validator honest up to the support cutoff `c` of slot `s + 1` is up and honest on
the observed run throughout `[tGAT, c + ΔClockBehind]`, when slot `s`'s duties start at or after
`tGAT` and `c ≤ tA`.

Why: a configuration entered at or before `c` has `v` honest (`HonestByG`) and so up
(`HealingPhaseG`, `c ≤ tA`); one entered after `c` and by `c + ΔClockBehind` is read by
`HoldersStayOnline.phaseEnd`.

The variables:
- `π`: the run; `tGST`, `tGAT`, `tA`: the phase; `ΔClockBehind`: the clock's lag bound; `hP`, `hH`:
  the conditions; `s`: the slot; `v`: the validator. -/
theorem upAndHonest_phase_to_cutoff {tGST tGAT tA ΔClockBehind : ℝ} {Δs Δs_F : ℕ}
    (hP : RStsVariant2.HealingPhaseG tGST tGAT tA (observeWithCommittees (Block := Block V) π))
    (hH : HoldersStayOnline S Δs Δs_F ΔClockBehind tGAT tA (observeWithCommittees (Block := Block V) π))
    {s : ℕ} (hd : tGAT ≤ ((duty_window_start S.C s : Time) : ℝ))
    (hcA : ((S.C.t_ (s + 1) + 2 * S.C.Δ : Time) : ℝ) ≤ tA) {v : V}
    (hv : HonestByG (observeWithCommittees (Block := Block V) π)
      ((S.C.t_ (s + 1) + 2 * S.C.Δ : Time) : ℝ) v) :
    RStsVariant2.UpAndHonestThroughoutG (observeWithCommittees (Block := Block V) π) tGAT
      (((S.C.t_ (s + 1) + 2 * S.C.Δ : Time) : ℝ) + ΔClockBehind) v := by
  intro i h1 h2
  by_cases hi : RStsVariant2.Observable.stamp (observeWithCommittees (Block := Block V) π) i ≤
      ((S.C.t_ (s + 1) + 2 * S.C.Δ : Time) : ℝ)
  · have hon := hv i hi
    obtain ⟨hc, hs⟩ := hP.2.2 i v h1 (hi.trans hcA) hon
    exact ⟨hc, hs, hon⟩
  · have hle : ((S.C.t_ (s + 1) + 2 * S.C.Δ : Time) : ℝ) ≤
        RStsVariant2.Observable.stamp (observeWithCommittees (Block := Block V) π) (i + 1) :=
      (le_of_not_ge hi).trans (π.mono i)
    exact hH.phaseEnd s hd hcA v hv i hle h2

open Classical in
/-- **`hActive` of the top statements**, from `HealingPhaseG`, `HoldersStayOnline.phaseEnd` and the
clock conditions: at every slot `s` whose duties' window, as `route-b` reads it, starts at or after
`tGATn`, and whose update is at most `tN`, every validator outside the trace's adversary set by the
update is an honest active validator and an updater of `s`.

Why: the validator is up and honest on the observed run throughout `[tGAT, c + ΔClockBehind]`, `c` the
update (`upAndHonest_phase_to_cutoff`), so it ticks on the trace at the reading of each window start
and of `c`, each in the window of its reading (`trace_tick_of_upAndHonest`; `tGAT + ΔClockAhead ≤
tGATn` puts the reading of a window start, less `ΔClockAhead`, in the phase); the tick at the window
start comes first (`ΔClockAhead + ΔClockBehind < Δ`), and between the two ticks the validator is
active. When a window start is negative, `tGAT` is too (`hdws`) and the validator is up from the run's
start. Every honest tick to `c` is at a real time at most `c + ΔClockBehind` (`toTrace_tick_active`),
where the validator is honest.

The variables:
- `π`: the run; `tGST`, `tGAT`, `tA`: the phase; `ΔClockAhead`, `ΔClockBehind`: the clock bounds;
  `hP`, `hH`, `hSkew`, `hAdv`, `hTicks`, `hActs`: the conditions; `tGATn`, `tN`: `route-b`'s phase;
  `hdws`: every slot `route-b` reads as starting its duties at or after `tGATn` starts them at or after
  `tGAT`. -/
theorem hActive_toTrace {tGST tGAT tA ΔClockAhead ΔClockBehind : ℝ} {Δs Δs_F : ℕ}
    (hCA : 0 ≤ ΔClockAhead) (hCB : 0 ≤ ΔClockBehind)
    (hΔ : ΔClockAhead + ΔClockBehind < ((S.C.Δ : Time) : ℝ))
    (hP : RStsVariant2.HealingPhaseG tGST tGAT tA (observeWithCommittees (Block := Block V) π))
    (hH : HoldersStayOnline S Δs Δs_F ΔClockBehind tGAT tA (observeWithCommittees (Block := Block V) π))
    (hSkew : RStsVariant2.ClockWithinSkew ΔClockAhead ΔClockBehind π)
    (hAdv : RStsVariant2.ClockAdvancesWithin ΔClockAhead ΔClockBehind π)
    (hTicks : RStsVariant2.TicksWithin ΔClockBehind π)
    (hActs : RStsVariant2.ActsWithinSkewG ΔClockBehind π)
    {tGATn tN : ℕ} (hG : tGAT + ΔClockAhead ≤ (tGATn : ℝ)) (hN : (tN : ℝ) ≤ tA)
    (hdws : ∀ s : ℕ, tGATn ≤ (Model.goldilocks (V := V)).dutyWindowStart S.C s →
      tGAT ≤ ((duty_window_start S.C s : Time) : ℝ)) :
    ∀ s : ℕ, tGATn ≤ (Model.goldilocks (V := V)).dutyWindowStart S.C s →
      (Model.goldilocks (V := V)).supportCutoff S.C (s + 1) ≤ tN →
      ∀ v : V, v ∉ (activityOf π).corruptedAtTime (toTrace ((Model.goldilocks (V := V)).initial S.C) π)
          (((Model.goldilocks (V := V)).supportCutoff S.C (s + 1) : ℕ) : ℝ) →
        v ∈ honestActiveAt Model.goldilocks S (activityOf π)
            (toTrace ((Model.goldilocks (V := V)).initial S.C) π) s ∧
          v ∈ GoldilocksCorrectness.Record.Statements.AbstractTrace.updaterAt Model.goldilocks S
            (activityOf π) (toTrace ((Model.goldilocks (V := V)).initial S.C) π) s := by
  intro s hs hsN v hv
  set x := toTrace ((Model.goldilocks (V := V)).initial S.C) π with hx
  set cN := (Model.goldilocks (V := V)).supportCutoff S.C (s + 1) with hcN
  have hcR : ((cN : ℕ) : ℝ) = ((S.C.t_ (s + 1) + 2 * S.C.Δ : Time) : ℝ) := cutoff_toNat_cast S (s + 1)
  have hd := hdws s hs
  have hcA : ((S.C.t_ (s + 1) + 2 * S.C.Δ : Time) : ℝ) ≤ tA := by
    rw [← hcR]; exact (by exact_mod_cast hsN : ((cN : ℕ) : ℝ) ≤ tN).trans hN
  have hvB : HonestByG (observeWithCommittees (Block := Block V) π)
      ((S.C.t_ (s + 1) + 2 * S.C.Δ : Time) : ℝ) v := by
    have := honestByG_of_not_mem_corruptedAtTime π hv
    rwa [hcR] at this
  have hW := upAndHonest_phase_to_cutoff π hP hH hd hcA hvB
  have hAct := activeThroughout_of_upAndHonest π hW
  have tm : ∀ {a b : ℕ}, a ≤ b → x.time a ≤ x.time b := fun h =>
    GoldilocksVariant.Final.toTrace_time_mono ((Model.goldilocks (V := V)).initial S.C) π h
  simp only [Activity.activeThroughout, Finset.mem_filter, Finset.mem_univ, true_and] at hAct
  -- the slot times, as reals
  have hΔ0 : (0 : ℝ) < ((S.C.Δ : Time) : ℝ) := by exact_mod_cast S.C.Δ_pos
  have hk0 : (0 : ℝ) ≤ ((S.C.t_ S.C.k : Time) : ℝ) := by exact_mod_cast slotTime_nonneg S S.C.k
  have hsucc : ((S.C.t_ (s + 1) : Time) : ℝ) = ((S.C.t_ s : Time) : ℝ) + 4 * ((S.C.Δ : Time) : ℝ) := by
    exact_mod_cast slotTime_succ S s
  have hdR : ((duty_window_start S.C s : Time) : ℝ) =
      ((S.C.t_ s : Time) : ℝ) + ((S.C.Δ : Time) : ℝ) - ((S.C.t_ S.C.k : Time) : ℝ) := by
    rw [duty_window_start_eq_slotTime]; push_cast; ring
  have hd1R : ((duty_window_start S.C (s + 1) : Time) : ℝ) =
      ((S.C.t_ s : Time) : ℝ) + 5 * ((S.C.Δ : Time) : ℝ) - ((S.C.t_ S.C.k : Time) : ℝ) := by
    rw [duty_window_start_eq_slotTime, slotTime_succ]; push_cast; ring
  have hcRR : ((S.C.t_ (s + 1) + 2 * S.C.Δ : Time) : ℝ) =
      ((S.C.t_ s : Time) : ℝ) + 6 * ((S.C.Δ : Time) : ℝ) := by push_cast; rw [hsucc]; ring
  -- the tick to the update
  obtain ⟨kc, hkc, hkc1, hkc2⟩ := trace_tick_of_upAndHonest π hCA hCB hSkew hAdv hTicks
    (c := cN) hW (by rw [hcR, hcRR]; linarith [hd, hdR]) (by linarith [hcR])
  -- a duty window start `d` at most the update's reading, at or after slot `s`'s: either negative,
  -- with `v` active at every trace step up to the tick to the update, or ticked to and active from
  -- that tick to the tick to the update
  have window : ∀ d : ℤ, duty_window_start S.C s ≤ d →
      (d : ℝ) + ΔClockAhead + ΔClockBehind < ((S.C.t_ (s + 1) + 2 * S.C.Δ : Time) : ℝ) →
      (tGATn ≤ d.toNat) →
      (∀ i : ℕ, i ≤ kc → v ∈ (activityOf π).active i) ∨
        (∃ k ≤ kc, ∃ c : ℕ, (c : ℤ) ≤ d ∧ x.lbl k =
          GoldilocksCorrectness.Statements.AbstractTrace.Event.tick v c ∧
          ∀ i : ℕ, k ≤ i → i ≤ kc → v ∈ (activityOf π).active i) := by
    intro d hdd hdc hdn
    by_cases hneg : (0 : ℤ) ≤ d
    · right
      have hdN : ((d.toNat : ℕ) : ℝ) = (d : ℝ) := toNat_cast_real hneg
      have hGd : tGAT + ΔClockAhead ≤ (d : ℝ) := by
        rw [← hdN]; exact hG.trans (by exact_mod_cast hdn)
      obtain ⟨kd, hkd, hkd1, hkd2⟩ := trace_tick_of_upAndHonest π hCA hCB hSkew hAdv hTicks
        (c := d.toNat) hW (by rw [hdN]; linarith) (by rw [hdN]; linarith)
      have hlt : kd ≤ kc := by
        by_contra hgt
        have := tm (show kc ≤ kd by omega)
        rw [hdN] at hkd2; rw [hcR] at hkc1
        linarith
      refine ⟨kd, hlt, d.toNat, by rw [Int.toNat_of_nonneg hneg], hkd, fun i h1 h2 => ?_⟩
      apply hAct i
      · exact ((tm h2).trans hkc2).trans (by linarith [hcR])
      · have := (tm (show kd ≤ i + 1 by omega))
        rw [hdN] at hkd1
        linarith
    · left
      have hGneg : tGAT < 0 := by
        have : ((duty_window_start S.C s : Time) : ℝ) ≤ (d : ℝ) := by exact_mod_cast hdd
        have : (d : ℝ) < 0 := by exact_mod_cast not_le.mp hneg
        linarith
      intro i hi
      apply hAct i
      · exact ((tm hi).trans hkc2).trans (by linarith [hcR])
      · have h0 : (0 : ℝ) ≤ x.time (i + 1) := by
          rw [hx, GoldilocksVariant.Final.toTrace_time]
          exact (π.stamp_nonneg _).trans (le_max_left _ _)
        linarith
  have hds : tGATn ≤ (duty_window_start S.C s).toNat := hs
  have hdd1 : duty_window_start S.C s ≤ duty_window_start S.C (s + 1) := by
    have h1 := duty_window_start_eq_slotTime S s
    have h2 := duty_window_start_eq_slotTime S (s + 1)
    have h3 := slotTime_succ S s
    have h4 : (0 : ℤ) < S.C.Δ := S.C.Δ_pos
    show @LE.le ℤ _ _ _
    omega
  have hds1 : tGATn ≤ (duty_window_start S.C (s + 1)).toNat :=
    hds.trans (Int.toNat_le_toNat hdd1)
  have hw0 := window (duty_window_start S.C s) le_rfl
    (by rw [hdR, hcRR]; linarith) hds
  have hw1 := window (duty_window_start S.C (s + 1)) hdd1
    (by rw [hd1R, hcRR]; linarith) hds1
  constructor
  · unfold honestActiveAt activeAt
    rw [Finset.mem_sdiff, Finset.mem_union, not_or]
    refine ⟨?_, hv, ?_⟩
    · simp only [Activity.awakeThroughoutToTick, Finset.mem_filter, Finset.mem_univ, true_and]
      have hawk : ∀ i, v ∈ (activityOf π).active i → v ∈ (activityOf π).awake i := fun i h =>
        (Finset.mem_sdiff.1 h).1
      refine ⟨kc, hkc, ?_⟩
      rcases hw0 with hall | ⟨k, hk, c, hc, hkl, hall⟩
      · exact Or.inl fun i hi => hawk i (hall i hi)
      · exact Or.inr ⟨k, hk, c, hc, hkl, fun i h1 h2 => hawk i (hall i h1 h2)⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_exists, not_and]
      intro k w hk hw hvk
      obtain ⟨k₀, rfl, hl, hc⟩ := GoldilocksVariant.Final.exists_of_lbl_tick _ π hk
      rw [GoldilocksVariant.Final.corrupted_activityOf_newIdx] at hvk
      have hkt := hActs k₀ w cN (Or.inl hl) hc
      have hlow := GoldilocksVariant.Final.le_stamp_of_clock π ΔClockAhead ΔClockBehind hSkew hc
      have hkt1 : (tGAT : ℝ) ≤ π.stamp (k₀ + 1) := by
        rw [hcR, hcRR] at hlow
        linarith [hd, hdR]
      obtain ⟨-, -, hh⟩ := hW k₀ hkt1 ((π.mono k₀).trans (by rw [hcR] at hkt; exact hkt))
      exact hh hvk
  · unfold GoldilocksCorrectness.Record.Statements.AbstractTrace.updaterAt
    simp only [Activity.activeThroughoutToTick, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨kc, hkc, hw1⟩

end Holders

/-! ## 8. The trace's promises outside an asynchronous period (statement 4) -/

section Outside

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDeliveryOutside SyncedWithinOutside)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject Vocab.goldilocks)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf servesMin)

variable {S : Setup V} [ProtocolCommittees (goldilocksProtocol S) (Block V)]
  (π : RStsVariant2.Exec (goldilocksProtocol S))

/-- **The trace's delivery promise for blocks and Goldfish votes outside the period `[b₀, b₁)`**, at
the network's delay `ΔNet` and the time `⌈tGST⌉₊`, from the conditions every top statement takes on
the observed run with the deadline `deadlineOutside tGST (goldilocksΔNetDelivery ΔNet ΔNet_F
ΔClockAhead) tAsyncStart tAsyncEnd` and Goldilocks's extra condition on redelivery, when
`b₀ ≤ tAsyncStart` and `tAsyncEnd ≤ b₁`.

Why: `GoldilocksVariant.Final.envFactsDeliveryOutside_toTrace`, each condition read on the run
(section 1); a block or a Goldfish vote has the delay `ΔNet − ΔClockAhead`, at most `ΔNet`.

The variables: as for `envFactsDelivery_of_conditions`; `tAsyncStart`, `tAsyncEnd`: the period on the
observed run; `b₀`, `b₁`: the period as `route-b` reads it. -/
theorem envFactsDeliveryOutside_of_conditions {tGST tAsyncStart tAsyncEnd : ℝ}
    {dlW : (m : NamedObject V) → (t : ℝ) → ℝ}
    {ΔClockAhead ΔClockBehind : ℝ≥0} {tGAT tAwakeEnd : ℝ}
    {H : (segment : (i : ℕ) → Option (PhaseStep V (NamedObject V) (Block V))) → Prop}
    {ΔNet ΔNet_F ΔRedeliver b₀ b₁ : ℕ}
    (hC : TopStatementConditions tGST
      (RStsVariant2.deadlineOutside tGST (goldilocksΔNetDelivery ΔNet ΔNet_F ΔClockAhead)
        tAsyncStart tAsyncEnd) dlW ΔClockAhead
      ΔClockBehind tGAT tAwakeEnd H (observeWithCommittees (Block := Block V) π))
    (hRe : RedeliveredAfterReleaseFromDelivery (goldilocksRelease S) (ΔRedeliver : ℝ)
      (observeWithCommittees (Block := Block V) π))
    (hb₀ : (b₀ : ℝ) ≤ tAsyncStart) (hb₁ : tAsyncEnd ≤ b₁) :
    EnvFactsDeliveryOutside (activityOf π) (toTrace ((Model.goldilocks (V := V)).initial S.C) π)
      ΔClockAhead ΔClockBehind ΔNet ΔRedeliver ⌈tGST⌉₊ (releaseOf Model.goldilocks S.C) acObject
      Vocab.goldilocks b₀ b₁ := by
  rw [GoldilocksVariant.Final.releaseOf_goldilocks]
  refine GoldilocksVariant.Final.envFactsDeliveryOutside_toTrace (M := Model.goldilocks)
    goldilocksFacts π ΔClockAhead.2 ΔClockBehind.2 hC.tickOnce hC.clockWithinSkew
    ((RStsVariant2.clockAdvancesWithin_observe NodeViewOf.view π _ _).1 hC.clockAdvances)
    ((RStsVariant2.ticksWithin_observe NodeViewOf.view π _).1 hC.ticksWithin) hC.actsWithinSkew
    hC.unforgeable
    ((RStsVariant2.deliveredBeforeActingG_observe NodeViewOf.view π RStsVariant2.TickStepG
      RStsVariant2.TickStepG (fun _ _ => Iff.rfl) _).1 hC.delivered)
    (redelivered_run π hRe) (Nat.le_ceil tGST) ?_ hb₀ hb₁
  intro m hm
  cases m <;> simp_all [goldilocksΔNetDelivery, acObject]

/-- **The trace's delivery promise for attestations outside the period `[b₀, b₁)`**, at the network's
delay `ΔNet_F`, from the same conditions as `envFactsDeliveryOutside_of_conditions`.

Why: as `envFactsDeliveryOutside_of_conditions`; an attestation has the delay `ΔNet_F − ΔClockAhead`.

The variables: as for `envFactsDeliveryOutside_of_conditions`. -/
theorem envFactsDeliveryOutside_F_of_conditions {tGST tAsyncStart tAsyncEnd : ℝ}
    {dlW : (m : NamedObject V) → (t : ℝ) → ℝ}
    {ΔClockAhead ΔClockBehind : ℝ≥0} {tGAT tAwakeEnd : ℝ}
    {H : (segment : (i : ℕ) → Option (PhaseStep V (NamedObject V) (Block V))) → Prop}
    {ΔNet ΔNet_F ΔRedeliver b₀ b₁ : ℕ}
    (hC : TopStatementConditions tGST
      (RStsVariant2.deadlineOutside tGST (goldilocksΔNetDelivery ΔNet ΔNet_F ΔClockAhead)
        tAsyncStart tAsyncEnd) dlW ΔClockAhead
      ΔClockBehind tGAT tAwakeEnd H (observeWithCommittees (Block := Block V) π))
    (hRe : RedeliveredAfterReleaseFromDelivery (goldilocksRelease S) (ΔRedeliver : ℝ)
      (observeWithCommittees (Block := Block V) π))
    (hb₀ : (b₀ : ℝ) ≤ tAsyncStart) (hb₁ : tAsyncEnd ≤ b₁) :
    EnvFactsDeliveryOutside (activityOf π) (toTrace ((Model.goldilocks (V := V)).initial S.C) π)
      ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver ⌈tGST⌉₊ (releaseOf Model.goldilocks S.C) fgObject
      Vocab.goldilocks b₀ b₁ := by
  rw [GoldilocksVariant.Final.releaseOf_goldilocks]
  refine GoldilocksVariant.Final.envFactsDeliveryOutside_toTrace (M := Model.goldilocks)
    goldilocksFacts π ΔClockAhead.2 ΔClockBehind.2 hC.tickOnce hC.clockWithinSkew
    ((RStsVariant2.clockAdvancesWithin_observe NodeViewOf.view π _ _).1 hC.clockAdvances)
    ((RStsVariant2.ticksWithin_observe NodeViewOf.view π _).1 hC.ticksWithin) hC.actsWithinSkew
    hC.unforgeable
    ((RStsVariant2.deliveredBeforeActingG_observe NodeViewOf.view π RStsVariant2.TickStepG
      RStsVariant2.TickStepG (fun _ _ => Iff.rfl) _).1 hC.delivered)
    (redelivered_run π hRe) (Nat.le_ceil tGST) ?_ hb₀ hb₁
  intro m hm
  cases m <;> simp_all [goldilocksΔNetDelivery, fgObject]

/-- **The trace's sync fact for blocks and Goldfish votes outside the period `[b₀, b₁)`**
(`SyncedWithinOutside` at `servesMin`), at the trace's delay `ΔNet`, catch-up delay `Δs`, sync delay
`Δs_tr` and time `GST`, from the conditions every top statement takes on the observed run with the deadlines
`deadlineOutside tGST (goldilocksΔNetDelivery ΔNet ΔNet_F ΔClockAhead) tAsyncStart tAsyncEnd` and
`deadlineOutside tGST (goldilocksΔSyncCatchUp Δs Δs_F ΔClockAhead) tAsyncStart tAsyncEnd`, and
Goldilocks's extra condition on redelivery, when `tGST ≤ GST`, `b₀ ≤ tAsyncStart`, `tAsyncEnd ≤ b₁`,
`ΔNet + ΔClockAhead ≤ Δs_tr` and `max ΔNet Δs ≤ Δs_tr`.

Why: `GoldilocksVariant.Final.syncedWithinOutside_toTrace` at the trace's delays `ΔNet` and `Δs`,
each condition read on the run (section 1).

The variables: as for `syncedWithin_of_conditions`; `tAsyncStart`, `tAsyncEnd`, `b₀`, `b₁`: as for
`envFactsDeliveryOutside_of_conditions`. -/
theorem syncedWithinOutside_of_conditions
    {tGST tAsyncStart tAsyncEnd : ℝ} {ΔClockAhead ΔClockBehind : ℝ≥0} {tGAT tAwakeEnd : ℝ}
    {H : (segment : (i : ℕ) → Option (PhaseStep V (NamedObject V) (Block V))) → Prop}
    {ΔNet ΔNet_F ΔRedeliver Δs Δs_F Δs_tr GST b₀ b₁ : ℕ}
    (hC : TopStatementConditions tGST
      (RStsVariant2.deadlineOutside tGST (goldilocksΔNetDelivery ΔNet ΔNet_F ΔClockAhead)
        tAsyncStart tAsyncEnd)
      (RStsVariant2.deadlineOutside tGST (goldilocksΔSyncCatchUp Δs Δs_F ΔClockAhead)
        tAsyncStart tAsyncEnd) ΔClockAhead
      ΔClockBehind tGAT tAwakeEnd H (observeWithCommittees (Block := Block V) π))
    (hRe : RedeliveredAfterReleaseFromDelivery (goldilocksRelease S) (ΔRedeliver : ℝ)
      (observeWithCommittees (Block := Block V) π))
    (htGST : tGST ≤ GST) (hb₀ : (b₀ : ℝ) ≤ tAsyncStart) (hb₁ : tAsyncEnd ≤ b₁)
    (hΔA : (ΔNet : ℝ) + ΔClockAhead ≤ Δs_tr) (hΔs : max ΔNet Δs ≤ Δs_tr) :
    SyncedWithinOutside (activityOf π) (toTrace ((Model.goldilocks (V := V)).initial S.C) π)
      (servesMin Model.goldilocks S.C) acObject (releaseOf Model.goldilocks S.C) ΔRedeliver Δs_tr
      GST b₀ b₁ := by
  refine GoldilocksVariant.Final.syncedWithinOutside_toTrace (M := Model.goldilocks) goldilocksFacts
    GoldilocksCorrectness.Record.uniformSchedule_goldilocks π
    ΔClockAhead.2 ΔClockBehind.2 hC.tickOnce hC.clockWithinSkew
    ((RStsVariant2.clockAdvancesWithin_observe NodeViewOf.view π _ _).1 hC.clockAdvances)
    ((RStsVariant2.ticksWithin_observe NodeViewOf.view π _).1 hC.ticksWithin) hC.actsWithinSkew
    hC.unforgeable
    ((RStsVariant2.deliveredBeforeActingG_observe NodeViewOf.view π RStsVariant2.TickStepG
      RStsVariant2.TickStepG (fun _ _ => Iff.rfl) _).1 hC.delivered)
    ((RStsVariant2.catchUpAfterRestartG_observe NodeViewOf.view π RStsVariant2.TickStepG
      RStsVariant2.TickStepG (fun _ _ => Iff.rfl) _ _).1 hC.catchUp)
    (by rw [GoldilocksVariant.Final.releaseOf_goldilocks]; exact redelivered_run π hRe)
    (Δ := ΔNet) (Δw := Δs) htGST ?_ ?_ hb₀ hb₁ hΔA hΔs
  · intro m hm
    cases m <;> simp_all [goldilocksΔNetDelivery, acObject]
  · intro m hm
    cases m <;> simp_all [goldilocksΔSyncCatchUp, acObject]

/-- **The trace's sync fact for attestations outside the period `[b₀, b₁)`** (`SyncedWithinOutside`
at `servesMin` and `fgObject`), at the trace's delays `ΔNet_F`, `Δs_F`, `Δs_F_tr` and time `GST`,
from the same conditions as `syncedWithinOutside_of_conditions`.

Why: `GoldilocksVariant.Final.syncedWithinOutside_F_toTrace`, as for
`syncedWithinOutside_of_conditions`.

The variables: as for `syncedWithinOutside_of_conditions`, at the attestations' delays. -/
theorem syncedWithinOutside_F_of_conditions
    {tGST tAsyncStart tAsyncEnd : ℝ} {ΔClockAhead ΔClockBehind : ℝ≥0} {tGAT tAwakeEnd : ℝ}
    {H : (segment : (i : ℕ) → Option (PhaseStep V (NamedObject V) (Block V))) → Prop}
    {ΔNet ΔNet_F ΔRedeliver Δs Δs_F Δs_F_tr GST b₀ b₁ : ℕ}
    (hC : TopStatementConditions tGST
      (RStsVariant2.deadlineOutside tGST (goldilocksΔNetDelivery ΔNet ΔNet_F ΔClockAhead)
        tAsyncStart tAsyncEnd)
      (RStsVariant2.deadlineOutside tGST (goldilocksΔSyncCatchUp Δs Δs_F ΔClockAhead)
        tAsyncStart tAsyncEnd) ΔClockAhead
      ΔClockBehind tGAT tAwakeEnd H (observeWithCommittees (Block := Block V) π))
    (hRe : RedeliveredAfterReleaseFromDelivery (goldilocksRelease S) (ΔRedeliver : ℝ)
      (observeWithCommittees (Block := Block V) π))
    (htGST : tGST ≤ GST) (hb₀ : (b₀ : ℝ) ≤ tAsyncStart) (hb₁ : tAsyncEnd ≤ b₁)
    (hΔA : (ΔNet_F : ℝ) + ΔClockAhead ≤ Δs_F_tr) (hΔs : max ΔNet_F Δs_F ≤ Δs_F_tr) :
    SyncedWithinOutside (activityOf π) (toTrace ((Model.goldilocks (V := V)).initial S.C) π)
      (servesMin Model.goldilocks S.C) fgObject (releaseOf Model.goldilocks S.C) ΔRedeliver
      Δs_F_tr GST b₀ b₁ := by
  refine GoldilocksVariant.Final.syncedWithinOutside_F_toTrace (M := Model.goldilocks)
    goldilocksFacts π
    ΔClockAhead.2 ΔClockBehind.2 hC.tickOnce hC.clockWithinSkew
    ((RStsVariant2.clockAdvancesWithin_observe NodeViewOf.view π _ _).1 hC.clockAdvances)
    ((RStsVariant2.ticksWithin_observe NodeViewOf.view π _).1 hC.ticksWithin) hC.actsWithinSkew
    hC.unforgeable
    ((RStsVariant2.deliveredBeforeActingG_observe NodeViewOf.view π RStsVariant2.TickStepG
      RStsVariant2.TickStepG (fun _ _ => Iff.rfl) _).1 hC.delivered)
    ((RStsVariant2.catchUpAfterRestartG_observe NodeViewOf.view π RStsVariant2.TickStepG
      RStsVariant2.TickStepG (fun _ _ => Iff.rfl) _ _).1 hC.catchUp)
    (by rw [GoldilocksVariant.Final.releaseOf_goldilocks]; exact redelivered_run π hRe)
    (Δ_F := ΔNet_F) (Δw_F := Δs_F) htGST ?_ ?_ hb₀ hb₁ hΔA hΔs
  · intro m hm
    cases m <;> simp_all [goldilocksΔNetDelivery, fgObject]
  · intro m hm
    cases m <;> simp_all [goldilocksΔSyncCatchUp, fgObject]

end Outside

/-! ## 9. Windows that open the clock's lead early: `hActive` with `hSeq`, and the finality window -/

section Windows

open GoldilocksCorrectness.Statements.AbstractTrace (Activity)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (honestActiveAt activeAt)
open GoldilocksCorrectness.Record.Statements.Executions (HonestOpenerAt QuorumActiveAt FinalityWindowAt)
open Goldilocks (duty_window_start proposal_window_start)

variable {S : Setup V} [ProtocolCommittees (goldilocksProtocol S) (Block V)]
  (π : RStsVariant2.Exec (goldilocksProtocol S))

/-- A validator awake and outside the corrupted set in every configuration of the segment
`[tS, tE]` in force at a time of `[a, b]` is up and honest throughout `[a, b]` on the observed run,
when `[a, b]` is inside `[tS, tE]`.

Why: every configuration of the run in force at a time of `[a, b]` is a configuration of the
segment, with the run's time, its awake set (up, with a known state) and its corrupted set.

The variables:
- `π`: the run; `tS`, `tE`: the segment; `a`, `b`: the window; `v`: the validator. -/
theorem upAndHonest_of_segment {tS tE a b : ℝ} {v : V} (hS : tS ≤ a) (hE : b ≤ tE)
    (h : ∀ (j : ℕ) (st : PhaseStep V (NamedObject V) (Block V)),
      phaseSegment (observeWithCommittees (Block := Block V) π) tS tE j = some st →
      st.time ≤ b →
      (∀ st' : PhaseStep V (NamedObject V) (Block V),
        phaseSegment (observeWithCommittees (Block := Block V) π) tS tE (j + 1) = some st' →
        a ≤ st'.time) →
      v ∈ st.awake ∧ v ∉ st.corrupted) :
    RStsVariant2.UpAndHonestThroughoutG (observeWithCommittees (Block := Block V) π) a b v := by
  intro i h1 h2
  obtain ⟨hw, hc⟩ := h i _ (by unfold phaseSegment; exact if_pos ⟨hS.trans h1, h2.trans hE⟩) h2
    (fun st' hst' => by
      unfold phaseSegment at hst'
      split at hst'
      · cases hst'; exact h1
      · cases hst')
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
  exact ⟨hw.1, Option.isSome_iff_ne_none.mp hw.2, hc⟩

/-- A validator up and honest throughout `[a, b]` on the observed run is honest up to every time `c`
of `[a, b]`.

Why: a configuration entered by `c` and left at or after `a` is in the window; one left before `a`
precedes the first configuration left at or after `a`, which is entered by `a` and so in the window,
and corruption is permanent.

The variables:
- `π`: the run; `a`, `b`: the window; `c`: the time; `v`: the validator. -/
theorem honestByG_of_upAndHonest {a b c : ℝ} {v : V}
    (h : RStsVariant2.UpAndHonestThroughoutG (observeWithCommittees (Block := Block V) π) a b v)
    (hac : a ≤ c) (hcb : c ≤ b) :
    HonestByG (observeWithCommittees (Block := Block V) π) c v := by
  intro j hj
  by_cases hle : a ≤ π.stamp (j + 1)
  · exact (h j hle (hj.trans hcb)).2.2
  · have hex : ∃ n : ℕ, a ≤ π.stamp (n + 1) := by
      obtain ⟨n, hn⟩ := π.progress a
      exact ⟨n, hn.trans (π.mono n)⟩
    have hjo : j < Nat.find hex := by
      by_contra hlt
      have h1 := π.stamp_mono (show Nat.find hex + 1 ≤ j + 1 by omega)
      exact hle ((Nat.find_spec hex).trans h1)
    obtain ⟨n, hn⟩ : ∃ n : ℕ, Nat.find hex = n + 1 := ⟨Nat.find hex - 1, by omega⟩
    have hmin := Nat.find_min hex (show n < Nat.find hex by omega)
    have hso : π.stamp (Nat.find hex) ≤ a := by rw [hn]; exact (not_le.mp hmin).le
    have hon := (h (Nat.find hex) (Nat.find_spec hex) (hso.trans (hac.trans hcb))).2.2
    exact fun hadv => hon (π.adv_mono hjo.le hadv)

/-- A validator honest up to `c` on the observed run is outside the trace's adversary set after every
step whose time is at most `c`.

Why: the trace step `j` reads the run's configuration `origBefore π j`, entered by the step's time.

The variables:
- `π`: the run; `c`: the time; `v`: the validator. -/
theorem not_mem_corruptedAtTime_of_honestByG {c : ℝ} {v : V}
    (h : HonestByG (observeWithCommittees (Block := Block V) π) c v) :
    v ∉ (activityOf π).corruptedAtTime (toTrace ((Model.goldilocks (V := V)).initial S.C) π) c := by
  intro hmem
  simp only [Activity.corruptedAtTime, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  obtain ⟨j, hj, hc⟩ := hmem
  rw [GoldilocksVariant.Final.corrupted_activityOf] at hc
  exact h (origBefore π j) ((GoldilocksVariant.Final.toTrace_time_mem _ π j).1.trans hj) hc

open Classical in
/-- A validator honest up to `c + ΔClockBehind` on the observed run is outside the trace's adversary
set at every step at which a validator ticks to the reading `c`.

Why: such a step is the run's tick at a step `k`, taken from configuration `k` at a real time at most
`c + ΔClockBehind` (`ActsWithinSkewG`).

The variables:
- `π`: the run; `ΔClockBehind`: the clock's lag bound; `hActs`: the condition; `c`: the reading;
  `v`: the validator. -/
theorem not_mem_corrupted_at_ticks_of_honestByG {ΔClockBehind : ℝ}
    (hActs : RStsVariant2.ActsWithinSkewG ΔClockBehind (observeWithCommittees (Block := Block V) π))
    {c : ℕ} {v : V}
    (h : HonestByG (observeWithCommittees (Block := Block V) π) ((c : ℝ) + ΔClockBehind) v) :
    v ∉ Finset.univ.filter (fun u => ∃ (k : ℕ) (w : V),
      (toTrace ((Model.goldilocks (V := V)).initial S.C) π).lbl k =
        GoldilocksCorrectness.Statements.AbstractTrace.Event.tick w c ∧
      w ∉ (activityOf π).corrupted k ∧ u ∈ (activityOf π).corrupted k) := by
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_exists, not_and]
  intro k w hk _ hvk
  obtain ⟨k₀, rfl, hl, hc⟩ := GoldilocksVariant.Final.exists_of_lbl_tick _ π hk
  rw [GoldilocksVariant.Final.corrupted_activityOf_newIdx] at hvk
  have ht := hActs k₀ w c (Or.inl hl) hc
  exact h k₀ ((π.mono k₀).trans ht) hvk

omit [ProtocolCommittees (goldilocksProtocol S) (Block V)] in
/-- When `v` ticks to `c` somewhere on the trace, the step `x.tickStep v c` is at a real time at most
`c + ΔClockBehind`.

Why: it is such a tick (`lbl_tickStep_of_exists`), the run's tick at some step, at a real time at most
`c + ΔClockBehind` (`ActsWithinSkewG`).

The variables:
- `π`: the run; `ΔClockBehind`: the clock's lag bound; `hActs`: the condition; `c`: the reading;
  `v`: the validator; `hex`: some trace step is `v`'s tick to `c`. -/
theorem time_tickStep_le {ΔClockBehind : ℝ}
    (hActs : RStsVariant2.ActsWithinSkewG ΔClockBehind π) {c : ℕ} {v : V}
    (hex : ∃ i : ℕ, (toTrace ((Model.goldilocks (V := V)).initial S.C) π).lbl i =
      GoldilocksCorrectness.Statements.AbstractTrace.Event.tick v c) :
    (toTrace ((Model.goldilocks (V := V)).initial S.C) π).time
        ((toTrace ((Model.goldilocks (V := V)).initial S.C) π).tickStep v c) ≤
      (c : ℝ) + ΔClockBehind := by
  obtain ⟨k₀, hk, hl, hc⟩ := GoldilocksVariant.Final.exists_of_lbl_tick _ π
    (lbl_tickStep_of_exists π hex)
  rw [← hk]
  have et : (toTrace ((Model.goldilocks (V := V)).initial S.C) π).time (newIdx π k₀) =
      π.stamp (k₀ + 1) := GoldilocksVariant.Final.toTrace_time_newIdx _ π k₀
  rw [et]
  exact hActs k₀ v c (Or.inl hl) hc

open GoldilocksCorrectness.Record.Proofs.Executions in
/-- **A root collision at one honest proposal on the trace is a root collision by `t` on the observed
run** (`RootCollisionBy`), `route-b`'s disjunct `RootCollisionAtProposal` read back: for a block `B`
that the proposer of slot `s` puts on the wire at its tick to the start of slot `s` (`ProposalAt`),
when a block with `B`'s root is in the proposer's tree in the state that tick starts from, and `t` is
at least the start of slot `s` plus `ΔClockBehind`.

Why: as `rootCollisionBy_of_atOpening` for one opening. The tick is a step `k₀` of the run
(`exists_of_lbl_tick`) at the real time `π.stamp (k₀ + 1)`, at most the start of slot `s` plus
`ΔClockBehind` (`ActsWithinSkewG`), so at most `t`. In configuration `k₀` the proposer's local state is
known, so the proposer is honest there, and its memory state is the trace's state at the tick: the
other block is in an honest node's tree by `t`. The tick's new envelope with `B` is signed by the
proposer: `B` was sent by an honest node by `t`. The two blocks differ
(`proposal_not_mem_tickInput`).

The variables:
- `π`: the run; `E`: the environment's facts on the trace; `hActs`: the clock condition on acting;
  `s`: the slot; `B`: the proposal, `hP`; `t`: the time, `ht`; `h`: the collision on the trace.

Read aloud: if an honest proposal has the root of a block its proposer already held, then by `t` two
distinct blocks with one root were each held or sent by an honest node. -/
theorem rootCollisionBy_of_atProposal
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy (activityOf π)
      (toTrace ((Model.goldilocks (V := V)).initial S.C) π) ΔClockAhead ΔClockBehind
      deadline release ΔRedeliver GoldilocksCorrectness.Statements.Executions.acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hActs : RStsVariant2.ActsWithinSkewG ΔClockBehind π) {s : ℕ} {B : Block V}
    (hP : GoldilocksCorrectness.Record.Statements.Executions.ProposalAt Model.goldilocks S
      (toTrace ((Model.goldilocks (V := V)).initial S.C) π) s B)
    {t : ℝ} (ht : (((Model.goldilocks (V := V)).slotStart S.C s : ℕ) : ℝ) + ΔClockBehind ≤ t)
    (h : GoldilocksCorrectness.Record.Statements.Executions.RootCollisionAtProposal Model.goldilocks S
      (activityOf π) (toTrace ((Model.goldilocks (V := V)).initial S.C) π) s B) :
    RootCollisionBy (observeWithCommittees (Block := Block V) π) t := by
  have R := GoldilocksVariant.Final.runFacts_toTrace goldilocksFacts π
  rw [GoldilocksCorrectness.Record.Proofs.View.rootCollisionAtProposal_unfold] at h
  obtain ⟨B', hB', hroot⟩ := h
  have hne : B' ≠ B := fun hBB => proposal_not_mem_tickInput R E hP (hBB ▸ hB')
  obtain ⟨k, hl, hm⟩ := hP
  have hts := (tickStep_eq_of_lbl Model.goldilocks) _ E hl
  have hti : (toTrace ((Model.goldilocks (V := V)).initial S.C) π).tickInput
      (S.P.proposer s) ((Model.goldilocks (V := V)).slotStart S.C s) =
      (toTrace ((Model.goldilocks (V := V)).initial S.C) π).st k (S.P.proposer s) := by
    unfold GoldilocksCorrectness.Statements.AbstractTrace.Trace.tickInput; rw [hts]
  rw [hti] at hB'
  obtain ⟨k₀, rfl, hl₀, hc₀⟩ := GoldilocksVariant.Final.exists_of_lbl_tick _ π hl
  -- the tick's real time is at most `t`
  have hstamp : π.stamp (k₀ + 1) ≤ t := le_trans (hActs k₀ _ _ (Or.inl hl₀) hc₀) ht
  -- the proposer's local state at the tick
  have hs := π.step_at k₀
  rw [hl₀] at hs
  obtain ⟨l, -, hlk, -⟩ := RStsVariant2.nodeSpec_enabled_known (Pr := goldilocksProtocol S)
    (v := S.P.proposer s) (na := .tick) (c := π[k₀]) hs.1
  have hadv : S.P.proposer s ∉ π[k₀].adv := fun hv => by
    rw [π.getElem_eq_none_of_mem_adv k₀ _ hv] at hlk
    exact absurd hlk (by simp)
  have hst : (toTrace ((Model.goldilocks (V := V)).initial S.C) π).st (newIdx π k₀)
      (S.P.proposer s) = l.st :=
    (GoldilocksVariant.Final.toTrace_st_newIdx _ π k₀ _).trans
      (GoldilocksVariant.Final.lastKnownSt_of_some _ π hlk)
  rw [hst] at hB'
  -- the proposal, as an envelope the tick put on the wire
  rw [show (toTrace ((Model.goldilocks (V := V)).initial S.C) π).sent (newIdx π k₀ + 1) =
      π[k₀ + 1].sent.map GoldilocksVariant.Final.traceMsg
      from GoldilocksVariant.Final.toTrace_sent_newIdx_succ _ π k₀,
    show (toTrace ((Model.goldilocks (V := V)).initial S.C) π).sent (newIdx π k₀) =
      π[k₀].sent.map GoldilocksVariant.Final.traceMsg
      from GoldilocksVariant.Final.toTrace_sent_newIdx _ π k₀] at hm
  obtain ⟨e, he, hee⟩ := exists_envelope_of_mem_map_sub (RStsVariant2.Step.sent_le (π.step_at k₀)) hm
  have hsend : e.sender = S.P.proposer s := congrArg (fun sm => sm.sender) hee
  have hmsg : e.msg = NamedObject.block B := congrArg (fun sm => sm.msg) hee
  refine ⟨B', B, Or.inl ?_, Or.inr ?_, hroot, hne⟩
  · exact inHonestTreeByG_of_known π hlk hadv
      (le_trans (π.stamp_mono (Nat.le_succ k₀)) hstamp) hB'
  · exact ⟨k₀, e, he, by rw [hsend]; exact hadv, hstamp, by rw [hmsg]; rfl⟩

/-- A validator up and honest on the observed run from `ΔClockAhead` before the integer reading `d`
to `ΔClockBehind` after the natural reading `c` ticks to `c` and is active on the trace from a tick to
a reading at most `d` (or from the trace's start, when `d` is negative) to that tick, when
`d + ΔClockAhead + ΔClockBehind < c`.

Why: it ticks to `c` and, when `d ≥ 0`, to `d` (`trace_tick_of_upAndHonest`), the tick to `d` first
(at a real time at most `d + ΔClockBehind`, less than `c − ΔClockAhead`, the earliest time of the
tick to `c`); between the two it is active (`activeThroughout_of_upAndHonest`). When `d < 0`, every
trace step's time is at least `0 > d − ΔClockAhead`.

The variables:
- `π`: the run; `ΔClockAhead`, `ΔClockBehind`: the clock bounds; `hSkew`, `hAdv`, `hTicks`: the
  clock conditions; `d`: the reading that opens the window; `c`: the reading of the tick that ends it;
  `v`: the validator. -/
theorem activeThroughoutToTick_of_upAndHonest {ΔClockAhead ΔClockBehind : ℝ}
    (hCA : 0 ≤ ΔClockAhead) (hCB : 0 ≤ ΔClockBehind)
    (hSkew : RStsVariant2.ClockWithinSkew ΔClockAhead ΔClockBehind π)
    (hAdv : RStsVariant2.ClockAdvancesWithin ΔClockAhead ΔClockBehind π)
    (hTicks : RStsVariant2.TicksWithin ΔClockBehind π) {d : ℤ} {c : ℕ} {v : V}
    (h : RStsVariant2.UpAndHonestThroughoutG (observeWithCommittees (Block := Block V) π)
      ((d : ℝ) - ΔClockAhead) ((c : ℝ) + ΔClockBehind) v)
    (hdc : (d : ℝ) + ΔClockAhead + ΔClockBehind < (c : ℝ)) :
    v ∈ (activityOf π).activeThroughoutToTick
      (toTrace ((Model.goldilocks (V := V)).initial S.C) π) d c := by
  set x := toTrace ((Model.goldilocks (V := V)).initial S.C) π with hx
  have hAct := activeThroughout_of_upAndHonest π h
  simp only [Activity.activeThroughout, Finset.mem_filter, Finset.mem_univ, true_and] at hAct
  have tm : ∀ {a b : ℕ}, a ≤ b → x.time a ≤ x.time b := fun hab =>
    GoldilocksVariant.Final.toTrace_time_mono ((Model.goldilocks (V := V)).initial S.C) π hab
  obtain ⟨kc, hkc, hkc1, hkc2⟩ := trace_tick_of_upAndHonest π hCA hCB hSkew hAdv hTicks
    (c := c) h (by linarith) le_rfl
  simp only [Activity.activeThroughoutToTick, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨kc, hkc, ?_⟩
  by_cases hneg : (0 : ℤ) ≤ d
  · right
    have hdN : ((d.toNat : ℕ) : ℝ) = (d : ℝ) := toNat_cast_real hneg
    obtain ⟨kd, hkd, hkd1, hkd2⟩ := trace_tick_of_upAndHonest π hCA hCB hSkew hAdv hTicks
      (c := d.toNat) h (by rw [hdN]) (by rw [hdN]; linarith)
    have hlt : kd ≤ kc := by
      by_contra hgt
      have := tm (show kc ≤ kd by omega)
      rw [hdN] at hkd2
      linarith
    refine ⟨kd, hlt, d.toNat, by rw [Int.toNat_of_nonneg hneg], hkd, fun i h1 h2 => ?_⟩
    apply hAct i
    · exact (tm h2).trans hkc2
    · have := tm (show kd ≤ i + 1 by omega)
      rw [hdN] at hkd1
      linarith
  · left
    intro i hi
    apply hAct i
    · exact (tm hi).trans hkc2
    · have h0 : (0 : ℝ) ≤ x.time (i + 1) := by
        rw [hx, GoldilocksVariant.Final.toTrace_time]
        exact (π.stamp_nonneg _).trans (le_max_left _ _)
      have : (d : ℝ) < 0 := by exact_mod_cast not_le.mp hneg
      linarith

omit [ProtocolCommittees (goldilocksProtocol S) (Block V)] in
/-- A validator active from a tick to its tick to `b` on the trace is awake over the same steps.

The variables:
- `π`: the run; `a`: the reading that opens the window; `b`: the reading of the tick that ends it;
  `v`: the validator. -/
theorem awakeThroughoutToTick_of_active {a : ℤ} {b : ℕ} {v : V}
    (h : v ∈ (activityOf π).activeThroughoutToTick
      (toTrace ((Model.goldilocks (V := V)).initial S.C) π) a b) :
    v ∈ (activityOf π).awakeThroughoutToTick
      (toTrace ((Model.goldilocks (V := V)).initial S.C) π) a b := by
  simp only [Activity.activeThroughoutToTick, Activity.awakeThroughoutToTick, Finset.mem_filter,
    Finset.mem_univ, true_and] at h ⊢
  have hawk : ∀ i, v ∈ (activityOf π).active i → v ∈ (activityOf π).awake i := fun i h =>
    (Finset.mem_sdiff.1 h).1
  obtain ⟨k', hk', hcase⟩ := h
  refine ⟨k', hk', ?_⟩
  rcases hcase with hall | ⟨k, hk, c, hc, hkl, hall⟩
  · exact Or.inl fun i hi => hawk i (hall i hi)
  · exact Or.inr ⟨k, hk, c, hc, hkl, fun i h1 h2 => hawk i (hall i h1 h2)⟩

/-- A proposer of slot `s` up and honest on the observed run from `ΔClockAhead` before slot `s`'s
proposal window start to `ΔClockBehind` after the support cutoff of slot `s + 1` is an honest opener of
slot `s` on the trace (`HonestOpenerAt`).

Why: it is active on the trace from its tick to the window's start to its tick to the cutoff
(`activeThroughoutToTick_of_upAndHonest`; the window's start plus both clock bounds is less than the
cutoff); it is honest up to the cutoff plus `ΔClockBehind`, a real time at least the cutoff, the time
of its own tick to the cutoff and of every tick to it.

The variables:
- `π`: the run; `ΔClockAhead`, `ΔClockBehind`: the clock bounds; `hSkew`, `hAdv`, `hTicks`, `hActs`:
  the clock conditions; `s`: the slot; `h`: the proposer's window on the observed run. -/
theorem honestOpenerAt_of_upAndHonest {ΔClockAhead ΔClockBehind : ℝ}
    (hCA : 0 ≤ ΔClockAhead) (hCB : 0 ≤ ΔClockBehind)
    (hΔ : ΔClockAhead + ΔClockBehind < ((S.C.Δ : Time) : ℝ))
    (hSkew : RStsVariant2.ClockWithinSkew ΔClockAhead ΔClockBehind π)
    (hAdv : RStsVariant2.ClockAdvancesWithin ΔClockAhead ΔClockBehind π)
    (hTicks : RStsVariant2.TicksWithin ΔClockBehind π)
    (hActs : RStsVariant2.ActsWithinSkewG ΔClockBehind π) {s : ℕ}
    (h : RStsVariant2.UpAndHonestThroughoutG (observeWithCommittees (Block := Block V) π)
      (((proposal_window_start S.C s : Time) : ℝ) - ΔClockAhead)
      (((S.C.t_ (s + 1) + 2 * S.C.Δ : Time) : ℝ) + ΔClockBehind) (S.P.proposer s)) :
    HonestOpenerAt Model.goldilocks S (activityOf π)
      (toTrace ((Model.goldilocks (V := V)).initial S.C) π) s := by
  set cN := (Model.goldilocks (V := V)).supportCutoff S.C (s + 1) with hcN
  have hcR : ((cN : ℕ) : ℝ) = ((S.C.t_ (s + 1) + 2 * S.C.Δ : Time) : ℝ) := cutoff_toNat_cast S (s + 1)
  have hΔ0 : (0 : ℝ) < ((S.C.Δ : Time) : ℝ) := by exact_mod_cast S.C.Δ_pos
  have hk0 : (0 : ℝ) ≤ ((S.C.t_ (S.C.k + 1) : Time) : ℝ) := by
    exact_mod_cast slotTime_nonneg S (S.C.k + 1)
  have hpR : ((proposal_window_start S.C s : Time) : ℝ) =
      ((S.C.t_ s : Time) : ℝ) + ((S.C.Δ : Time) : ℝ) - ((S.C.t_ (S.C.k + 1) : Time) : ℝ) := by
    rw [proposal_window_start_eq_slotTime]; push_cast; ring
  have hsucc : ((S.C.t_ (s + 1) : Time) : ℝ) = ((S.C.t_ s : Time) : ℝ) + 4 * ((S.C.Δ : Time) : ℝ) := by
    exact_mod_cast slotTime_succ S s
  have hcRR : ((S.C.t_ (s + 1) + 2 * S.C.Δ : Time) : ℝ) =
      ((S.C.t_ s : Time) : ℝ) + 6 * ((S.C.Δ : Time) : ℝ) := by push_cast; rw [hsucc]; ring
  have hU' : RStsVariant2.UpAndHonestThroughoutG (observeWithCommittees (Block := Block V) π)
      (((proposal_window_start S.C s : ℤ) : ℝ) - ΔClockAhead) (((cN : ℕ) : ℝ) + ΔClockBehind)
      (S.P.proposer s) := by
    rw [hcR]; exact h
  have hA := activeThroughoutToTick_of_upAndHonest π hCA hCB hSkew hAdv hTicks hU'
    (by rw [hcR, hcRR, hpR]; linarith)
  have hB : HonestByG (observeWithCommittees (Block := Block V) π) (((cN : ℕ) : ℝ) + ΔClockBehind)
      (S.P.proposer s) :=
    honestByG_of_upAndHonest π hU' (by rw [hcR, hcRR, hpR]; linarith) le_rfl
  have hex : ∃ i : ℕ, (toTrace ((Model.goldilocks (V := V)).initial S.C) π).lbl i =
      GoldilocksCorrectness.Statements.AbstractTrace.Event.tick (S.P.proposer s) cN := by
    simp only [Activity.activeThroughoutToTick, Finset.mem_filter, Finset.mem_univ, true_and] at hA
    obtain ⟨k', hk', -⟩ := hA
    exact ⟨k', hk'⟩
  refine ⟨hA, ?_⟩
  rw [Finset.mem_union, Finset.mem_union, not_or, not_or]
  refine ⟨⟨not_mem_corruptedAtTime_of_honestByG π (fun j hj => hB j (hj.trans (by linarith))),
    not_mem_corruptedAtTime_of_honestByG π
      (fun j hj => hB j (hj.trans (time_tickStep_le π hActs hex)))⟩,
    not_mem_corrupted_at_ticks_of_honestByG π hActs hB⟩

/-- **An honest opener of slot `s` on the finality segment is one on the trace**: Goldilocks's
`HonestOpenerOn` on the segment `[tS, tE]` gives `route-b`'s `HonestOpenerAt`, when the segment holds
the proposer's window, from `ΔClockAhead` before slot `s`'s proposal window start to `ΔClockBehind`
after the support cutoff of slot `s + 1`.

Why: the proposer is up and honest on the observed run through that window
(`upAndHonest_of_segment`); `honestOpenerAt_of_upAndHonest`.

The variables:
- `π`: the run; `ΔClockAhead`, `ΔClockBehind`: the clock bounds; `hSkew`, `hAdv`, `hTicks`, `hActs`:
  the clock conditions; `tS`, `tE`: the segment; `s`: the slot; `h`: the honest opener on the
  segment; `hS`, `hE`: the segment holds the proposer's window. -/
theorem honestOpenerAt_of_honestOpenerOn {ΔClockAhead ΔClockBehind tS tE : ℝ}
    (hCA : 0 ≤ ΔClockAhead) (hCB : 0 ≤ ΔClockBehind)
    (hΔ : ΔClockAhead + ΔClockBehind < ((S.C.Δ : Time) : ℝ))
    (hSkew : RStsVariant2.ClockWithinSkew ΔClockAhead ΔClockBehind π)
    (hAdv : RStsVariant2.ClockAdvancesWithin ΔClockAhead ΔClockBehind π)
    (hTicks : RStsVariant2.TicksWithin ΔClockBehind π)
    (hActs : RStsVariant2.ActsWithinSkewG ΔClockBehind π) {s : ℕ}
    (h : HonestOpenerOn S ΔClockAhead ΔClockBehind
      (phaseSegment (observeWithCommittees (Block := Block V) π) tS tE) s)
    (hS : tS ≤ ((proposal_window_start S.C s : Time) : ℝ) - ΔClockAhead)
    (hE : ((S.C.t_ (s + 1) + 2 * S.C.Δ : Time) : ℝ) + ΔClockBehind ≤ tE) :
    HonestOpenerAt Model.goldilocks S (activityOf π)
      (toTrace ((Model.goldilocks (V := V)).initial S.C) π) s :=
  honestOpenerAt_of_upAndHonest π hCA hCB hΔ hSkew hAdv hTicks hActs
    (upAndHonest_of_segment π hS hE h)

open Classical in
/-- A validator up and honest on the observed run from `ΔClockAhead` before slot `s`'s duty window
start to `ΔClockBehind` after the support cutoff of slot `s + 1` is an honest active validator of slot
`s` on the trace (`honestActiveAt`).

Why: it is active on the trace from its tick to the window's start to its tick to the cutoff, hence
awake (`activeThroughoutToTick_of_upAndHonest`, `awakeThroughoutToTick_of_active`), and honest up to
the cutoff and at every tick to it, as for `honestOpenerAt_of_upAndHonest`.

The variables:
- `π`: the run; `ΔClockAhead`, `ΔClockBehind`: the clock bounds; `hSkew`, `hAdv`, `hTicks`, `hActs`:
  the clock conditions; `s`: the slot; `v`: the validator; `h`: its window on the observed run. -/
theorem mem_honestActiveAt_of_upAndHonest {ΔClockAhead ΔClockBehind : ℝ}
    (hCA : 0 ≤ ΔClockAhead) (hCB : 0 ≤ ΔClockBehind)
    (hΔ : ΔClockAhead + ΔClockBehind < ((S.C.Δ : Time) : ℝ))
    (hSkew : RStsVariant2.ClockWithinSkew ΔClockAhead ΔClockBehind π)
    (hAdv : RStsVariant2.ClockAdvancesWithin ΔClockAhead ΔClockBehind π)
    (hTicks : RStsVariant2.TicksWithin ΔClockBehind π)
    (hActs : RStsVariant2.ActsWithinSkewG ΔClockBehind π) {s : ℕ} {v : V}
    (h : RStsVariant2.UpAndHonestThroughoutG (observeWithCommittees (Block := Block V) π)
      (((duty_window_start S.C s : Time) : ℝ) - ΔClockAhead)
      (((S.C.t_ (s + 1) + 2 * S.C.Δ : Time) : ℝ) + ΔClockBehind) v) :
    v ∈ honestActiveAt Model.goldilocks S (activityOf π)
      (toTrace ((Model.goldilocks (V := V)).initial S.C) π) s := by
  set cN := (Model.goldilocks (V := V)).supportCutoff S.C (s + 1) with hcN
  have hcR : ((cN : ℕ) : ℝ) = ((S.C.t_ (s + 1) + 2 * S.C.Δ : Time) : ℝ) := cutoff_toNat_cast S (s + 1)
  have hΔ0 : (0 : ℝ) < ((S.C.Δ : Time) : ℝ) := by exact_mod_cast S.C.Δ_pos
  have hk0 : (0 : ℝ) ≤ ((S.C.t_ S.C.k : Time) : ℝ) := by exact_mod_cast slotTime_nonneg S S.C.k
  have hdR : ((duty_window_start S.C s : Time) : ℝ) =
      ((S.C.t_ s : Time) : ℝ) + ((S.C.Δ : Time) : ℝ) - ((S.C.t_ S.C.k : Time) : ℝ) := by
    rw [duty_window_start_eq_slotTime]; push_cast; ring
  have hsucc : ((S.C.t_ (s + 1) : Time) : ℝ) = ((S.C.t_ s : Time) : ℝ) + 4 * ((S.C.Δ : Time) : ℝ) := by
    exact_mod_cast slotTime_succ S s
  have hcRR : ((S.C.t_ (s + 1) + 2 * S.C.Δ : Time) : ℝ) =
      ((S.C.t_ s : Time) : ℝ) + 6 * ((S.C.Δ : Time) : ℝ) := by push_cast; rw [hsucc]; ring
  have hU' : RStsVariant2.UpAndHonestThroughoutG (observeWithCommittees (Block := Block V) π)
      (((duty_window_start S.C s : ℤ) : ℝ) - ΔClockAhead) (((cN : ℕ) : ℝ) + ΔClockBehind) v := by
    rw [hcR]; exact h
  have hA := activeThroughoutToTick_of_upAndHonest π hCA hCB hSkew hAdv hTicks hU'
    (by rw [hcR, hcRR, hdR]; linarith)
  have hB : HonestByG (observeWithCommittees (Block := Block V) π) (((cN : ℕ) : ℝ) + ΔClockBehind) v :=
    honestByG_of_upAndHonest π hU' (by rw [hcR, hcRR, hdR]; linarith) le_rfl
  unfold honestActiveAt activeAt
  rw [Finset.mem_sdiff, Finset.mem_union, not_or]
  exact ⟨awakeThroughoutToTick_of_active π hA,
    not_mem_corruptedAtTime_of_honestByG π (fun j hj => hB j (hj.trans (by linarith))),
    not_mem_corrupted_at_ticks_of_honestByG π hActs hB⟩

/-- A validator up and honest on the observed run from `ΔClockAhead` before slot `s + 1`'s duty window
start to `ΔClockBehind` after the support cutoff of slot `s + 1` is an updater of slot `s` on the trace
(`updaterAt`).

Why: `activeThroughoutToTick_of_upAndHonest`; the window's start plus both clock bounds is less than
the cutoff (one delay after it).

The variables:
- `π`: the run; `ΔClockAhead`, `ΔClockBehind`: the clock bounds; `hSkew`, `hAdv`, `hTicks`: the clock
  conditions; `s`: the slot the update evaluates; `v`: the validator; `h`: its window on the observed
  run. -/
theorem mem_updaterAt_of_upAndHonest {ΔClockAhead ΔClockBehind : ℝ}
    (hCA : 0 ≤ ΔClockAhead) (hCB : 0 ≤ ΔClockBehind)
    (hΔ : ΔClockAhead + ΔClockBehind < ((S.C.Δ : Time) : ℝ))
    (hSkew : RStsVariant2.ClockWithinSkew ΔClockAhead ΔClockBehind π)
    (hAdv : RStsVariant2.ClockAdvancesWithin ΔClockAhead ΔClockBehind π)
    (hTicks : RStsVariant2.TicksWithin ΔClockBehind π) {s : ℕ} {v : V}
    (h : RStsVariant2.UpAndHonestThroughoutG (observeWithCommittees (Block := Block V) π)
      (((duty_window_start S.C (s + 1) : Time) : ℝ) - ΔClockAhead)
      (((S.C.t_ (s + 1) + 2 * S.C.Δ : Time) : ℝ) + ΔClockBehind) v) :
    v ∈ GoldilocksCorrectness.Record.Statements.AbstractTrace.updaterAt Model.goldilocks S
      (activityOf π) (toTrace ((Model.goldilocks (V := V)).initial S.C) π) s := by
  set cN := (Model.goldilocks (V := V)).supportCutoff S.C (s + 1) with hcN
  have hcR : ((cN : ℕ) : ℝ) = ((S.C.t_ (s + 1) + 2 * S.C.Δ : Time) : ℝ) := cutoff_toNat_cast S (s + 1)
  have hk0 : (0 : ℝ) ≤ ((S.C.t_ S.C.k : Time) : ℝ) := by exact_mod_cast slotTime_nonneg S S.C.k
  have hdR : ((duty_window_start S.C (s + 1) : Time) : ℝ) =
      ((S.C.t_ (s + 1) : Time) : ℝ) + ((S.C.Δ : Time) : ℝ) - ((S.C.t_ S.C.k : Time) : ℝ) := by
    rw [duty_window_start_eq_slotTime]; push_cast; ring
  have hU' : RStsVariant2.UpAndHonestThroughoutG (observeWithCommittees (Block := Block V) π)
      (((duty_window_start S.C (s + 1) : ℤ) : ℝ) - ΔClockAhead) (((cN : ℕ) : ℝ) + ΔClockBehind) v := by
    rw [hcR]; exact h
  unfold GoldilocksCorrectness.Record.Statements.AbstractTrace.updaterAt
  exact activeThroughoutToTick_of_upAndHonest π hCA hCB hSkew hAdv hTicks hU'
    (by rw [hcR, hdR]; push_cast; linarith)

open Classical in
/-- **A quorum of honest active validators of slot `s` on the finality segment is one on the trace**:
Goldilocks's `QuorumActiveOn` on the segment `[tS, tE]` gives `route-b`'s `QuorumActiveAt`, when the
segment holds the duties' window, from `ΔClockAhead` before slot `s`'s duty window start to
`ΔClockBehind` after the support cutoff of slot `s + 1`.

Why: each validator `QuorumActiveOn` counts is up and honest on the observed run through that window
(`upAndHonest_of_segment`); `mem_honestActiveAt_of_upAndHonest`.

The variables:
- `π`: the run; `ΔClockAhead`, `ΔClockBehind`: the clock bounds; `hSkew`, `hAdv`, `hTicks`, `hActs`:
  the clock conditions; `tS`, `tE`: the segment; `s`: the slot; `h`: the quorum on the segment; `hS`,
  `hE`: the segment holds the duties' window. -/
theorem quorumActiveAt_of_quorumActiveOn {ΔClockAhead ΔClockBehind tS tE : ℝ}
    (hCA : 0 ≤ ΔClockAhead) (hCB : 0 ≤ ΔClockBehind)
    (hΔ : ΔClockAhead + ΔClockBehind < ((S.C.Δ : Time) : ℝ))
    (hSkew : RStsVariant2.ClockWithinSkew ΔClockAhead ΔClockBehind π)
    (hAdv : RStsVariant2.ClockAdvancesWithin ΔClockAhead ΔClockBehind π)
    (hTicks : RStsVariant2.TicksWithin ΔClockBehind π)
    (hActs : RStsVariant2.ActsWithinSkewG ΔClockBehind π) {s : ℕ}
    (h : QuorumActiveOn S ΔClockAhead ΔClockBehind
      (phaseSegment (observeWithCommittees (Block := Block V) π) tS tE) s)
    (hS : tS ≤ ((duty_window_start S.C s : Time) : ℝ) - ΔClockAhead)
    (hE : ((S.C.t_ (s + 1) + 2 * S.C.Δ : Time) : ℝ) + ΔClockBehind ≤ tE) :
    QuorumActiveAt Model.goldilocks S (activityOf π)
      (toTrace ((Model.goldilocks (V := V)).initial S.C) π) s := by
  unfold QuorumActiveOn at h
  unfold QuorumActiveAt
  refine h.trans (Finset.card_le_card ?_)
  intro v hv
  rw [Finset.mem_filter] at hv
  exact mem_honestActiveAt_of_upAndHonest π hCA hCB hΔ hSkew hAdv hTicks hActs
    (upAndHonest_of_segment π hS hE (v := v)
      (fun j st h1 h2 h3 => ⟨(hv.2 j st h1 h2).2 h3, (hv.2 j st h1 h2).1⟩))

/-- **The finality window of round `r` on the trace**: Goldilocks's honest openers of the rounds `r` to
`r + 3` and quorums of the rounds `r` to `r + 2` on the segment `[tS, tE]` (the last two conjuncts of
`goldilocksFinalityConditions`) give `route-b`'s `FinalityWindowAt` at `r`, when the segment starts
at most `ΔClockAhead` before round `r`'s first proposal window and ends at least `ΔClockBehind` after
the update of round `r + 3`'s first slot.

Why: each opener's and each quorum's window is inside `[tS, tE]` (a later slot's proposal window and
duty window start later, a duty window starts after the proposal window of its slot, and an earlier
slot's update is earlier); `honestOpenerAt_of_honestOpenerOn`, `quorumActiveAt_of_quorumActiveOn`.

The variables:
- `π`: the run; `ΔClockAhead`, `ΔClockBehind`: the clock bounds; `hSkew`, `hAdv`, `hTicks`, `hActs`:
  the clock conditions; `tS`, `tE`: the segment; `r`: the round; `hO`, `hQ`: the openers and the
  quorums on the segment; `hS`, `hE`: the segment's ends. -/
theorem finalityWindowAt_of_on {ΔClockAhead ΔClockBehind tS tE : ℝ}
    (hCA : 0 ≤ ΔClockAhead) (hCB : 0 ≤ ΔClockBehind)
    (hΔ : ΔClockAhead + ΔClockBehind < ((S.C.Δ : Time) : ℝ))
    (hSkew : RStsVariant2.ClockWithinSkew ΔClockAhead ΔClockBehind π)
    (hAdv : RStsVariant2.ClockAdvancesWithin ΔClockAhead ΔClockBehind π)
    (hTicks : RStsVariant2.TicksWithin ΔClockBehind π)
    (hActs : RStsVariant2.ActsWithinSkewG ΔClockBehind π) {r : ℕ}
    (hO : ∀ i : ℕ, i < 4 → HonestOpenerOn S ΔClockAhead ΔClockBehind
      (phaseSegment (observeWithCommittees (Block := Block V) π) tS tE) ((r + i) * S.C.R))
    (hQ : ∀ i : ℕ, i < 3 → QuorumActiveOn S ΔClockAhead ΔClockBehind
      (phaseSegment (observeWithCommittees (Block := Block V) π) tS tE) ((r + i) * S.C.R))
    (hS : tS ≤ ((proposal_window_start S.C (r * S.C.R) : Time) : ℝ) - ΔClockAhead)
    (hE : ((S.C.t_ ((r + 3) * S.C.R + 1) + 2 * S.C.Δ : Time) : ℝ) + ΔClockBehind ≤ tE) :
    FinalityWindowAt Model.goldilocks S (activityOf π)
      (toTrace ((Model.goldilocks (V := V)).initial S.C) π) r := by
  have hΔ0 : (0 : ℝ) < ((S.C.Δ : Time) : ℝ) := by exact_mod_cast S.C.Δ_pos
  have hmono : ∀ {σ σ' : ℕ}, σ ≤ σ' → ((S.C.t_ σ : Time) : ℝ) ≤ ((S.C.t_ σ' : Time) : ℝ) :=
    fun h => by exact_mod_cast slotTime_mono S h
  have hpR : ∀ σ : ℕ, ((proposal_window_start S.C σ : Time) : ℝ) =
      ((S.C.t_ σ : Time) : ℝ) + ((S.C.Δ : Time) : ℝ) - ((S.C.t_ (S.C.k + 1) : Time) : ℝ) := by
    intro σ; rw [proposal_window_start_eq_slotTime]; push_cast; ring
  have hdR : ∀ σ : ℕ, ((duty_window_start S.C σ : Time) : ℝ) =
      ((S.C.t_ σ : Time) : ℝ) + ((S.C.Δ : Time) : ℝ) - ((S.C.t_ S.C.k : Time) : ℝ) := by
    intro σ; rw [duty_window_start_eq_slotTime]; push_cast; ring
  have hk1 : ((S.C.t_ S.C.k : Time) : ℝ) ≤ ((S.C.t_ (S.C.k + 1) : Time) : ℝ) := hmono (Nat.le_succ _)
  have hS' : ∀ i : ℕ, tS ≤ ((proposal_window_start S.C ((r + i) * S.C.R) : Time) : ℝ) - ΔClockAhead := by
    intro i
    have := hmono (show r * S.C.R ≤ (r + i) * S.C.R from Nat.mul_le_mul_right _ (by omega))
    rw [hpR] at hS ⊢
    linarith
  have hE' : ∀ i : ℕ, i < 4 →
      ((S.C.t_ ((r + i) * S.C.R + 1) + 2 * S.C.Δ : Time) : ℝ) + ΔClockBehind ≤ tE := by
    intro i hi
    have h1 : (r + i) * S.C.R ≤ (r + 3) * S.C.R := Nat.mul_le_mul_right _ (by omega)
    have := hmono (show (r + i) * S.C.R + 1 ≤ (r + 3) * S.C.R + 1 by omega)
    push_cast at hE ⊢
    linarith
  refine ⟨fun i hi => honestOpenerAt_of_honestOpenerOn π hCA hCB hΔ hSkew hAdv hTicks hActs (hO i hi)
    (hS' i) (hE' i hi), fun i hi => quorumActiveAt_of_quorumActiveOn π hCA hCB hΔ hSkew hAdv hTicks
    hActs (hQ i hi) ?_ (hE' i (by omega))⟩
  have := hS' i
  rw [hpR] at this
  rw [hdR]
  linarith

omit [ProtocolCommittees (goldilocksProtocol S) (Block V)] [RootOrder] in
/-- The natural number `⌈tGAT + ΔClockAhead⌉₊`, plus `4Δ · healFrontSlots S` read at `route-b`'s natural
`Δ S`, is at most every natural number at least `tGAT + 4Δ · healFrontSlots S + ΔClockAhead`, when
`tGAT + ΔClockAhead` is not negative.

Why: such a natural number less `4Δ · healFrontSlots S` is a natural number at least
`tGAT + ΔClockAhead`, so at least its ceiling.

The variables:
- `S`: the setup; `tGAT`: the start of the healing phase; `ΔClockAhead`: the clock's lead bound;
  `h0`: `tGAT + ΔClockAhead` is not negative; `n`: the natural number. -/
theorem ceil_add_healFront_le {tGAT ΔClockAhead : ℝ} (h0 : 0 ≤ tGAT + ΔClockAhead) (n : ℕ)
    (hn : tGAT + 4 * ((S.C.Δ : Time) : ℝ) *
        (GoldilocksCorrectness.Statements.Executions.healFrontSlots S : ℕ) + ΔClockAhead ≤ (n : ℝ)) :
    ⌈tGAT + ΔClockAhead⌉₊ + 4 * GoldilocksCorrectness.Statements.Routines.Δ S *
      GoldilocksCorrectness.Statements.Executions.healFrontSlots S ≤ n := by
  have hD : ((GoldilocksCorrectness.Statements.Routines.Δ S : ℕ) : ℝ) = ((S.C.Δ : Time) : ℝ) := by
    unfold GoldilocksCorrectness.Statements.Routines.Δ
    rw [show ((S.C.Δ.toNat : ℕ) : ℝ) = (((S.C.Δ.toNat : ℕ) : ℤ) : ℝ) by push_cast; rfl,
      Int.toNat_of_nonneg S.C.Δ_pos.le]
  set D := 4 * GoldilocksCorrectness.Statements.Routines.Δ S *
    GoldilocksCorrectness.Statements.Executions.healFrontSlots S with hDdef
  have hDR : ((D : ℕ) : ℝ) = 4 * ((S.C.Δ : Time) : ℝ) *
      (GoldilocksCorrectness.Statements.Executions.healFrontSlots S : ℕ) := by
    rw [hDdef]; push_cast; rw [hD]
  have hDn : D ≤ n := by
    have : (D : ℝ) ≤ (n : ℝ) := by rw [hDR]; linarith
    exact_mod_cast this
  have : ⌈tGAT + ΔClockAhead⌉₊ ≤ n - D := by
    rw [Nat.ceil_le, Nat.cast_sub hDn, hDR]
    linarith
  omega

open Classical in
/-- **`hActive` and `hSeq` of the top statements together**, at `route-b`'s natural start of the
phase `⌈tGAT + ΔClockAhead⌉₊`: from `HealingPhaseG`, `HoldersStayOnline`, the clock conditions and
Goldilocks's honest round opening slots on the healing-phase segment (`HonestOpeningSeqOn`, whose
first opening starts `ΔClockAhead` after `tGAT + 4Δ · healFrontSlots S`), at a natural `tN` at most the
end of the phase `tA` and at least the last opening's support cutoff plus `ΔClockBehind`.

Why: `hActive_toTrace` needs the natural start at least `tGAT + ΔClockAhead`, the ceiling;
`hSeq_toTrace` needs the natural start plus `4Δ · healFrontSlots S` at most every natural number at
least `tGAT + 4Δ · healFrontSlots S + ΔClockAhead` (`ceil_add_healFront_le`), and the first opening at
or after `tGAT`.

The variables:
- `π`: the run; `tGST`, `tGAT`, `tA`: the phase; `ΔClockAhead`, `ΔClockBehind`: the clock bounds;
  `hP`, `hH`, `hSkew`, `hAdv`, `hTicks`, `hActs`: the conditions; `r`, `m`, `hseq`: the openings;
  `h0`: `tGAT + ΔClockAhead` is not negative; `tN`: `route-b`'s end of the phase; `hdws`: every slot
  `route-b` reads as starting its duties at or after the natural start starts them at or after
  `tGAT`. -/
theorem hActive_hSeq_toTrace {tGST tGAT tA ΔClockAhead ΔClockBehind : ℝ} {Δs Δs_F : ℕ}
    (hCA : 0 ≤ ΔClockAhead) (hCB : 0 ≤ ΔClockBehind)
    (hΔ : ΔClockAhead + ΔClockBehind < ((S.C.Δ : Time) : ℝ))
    (hP : RStsVariant2.HealingPhaseG tGST tGAT tA (observeWithCommittees (Block := Block V) π))
    (hH : HoldersStayOnline S Δs Δs_F ΔClockBehind tGAT tA (observeWithCommittees (Block := Block V) π))
    (hSkew : RStsVariant2.ClockWithinSkew ΔClockAhead ΔClockBehind π)
    (hAdv : RStsVariant2.ClockAdvancesWithin ΔClockAhead ΔClockBehind π)
    (hTicks : RStsVariant2.TicksWithin ΔClockBehind π)
    (hActs : RStsVariant2.ActsWithinSkewG ΔClockBehind π)
    {r : ℕ → ℕ} {m : ℕ}
    (hseq : HonestOpeningSeqOn S
      (phaseSegment (observeWithCommittees (Block := Block V) π) tGAT tA) r m ΔClockAhead
        ΔClockBehind
      (tGAT + 4 * ((S.C.Δ : Time) : ℝ) *
        (GoldilocksCorrectness.Statements.Executions.healFrontSlots S : ℕ)) tA)
    (h0 : 0 ≤ tGAT + ΔClockAhead) {tN : ℕ} (hN : (tN : ℝ) ≤ tA)
    (hNlast : ((S.C.t_ (r m * S.C.R) + 2 * S.C.Δ : Time) : ℝ) + ΔClockBehind ≤ (tN : ℝ))
    (hdws : ∀ s : ℕ, ⌈tGAT + ΔClockAhead⌉₊ ≤ (Model.goldilocks (V := V)).dutyWindowStart S.C s →
      tGAT ≤ ((duty_window_start S.C s : Time) : ℝ)) :
    (∀ s : ℕ, ⌈tGAT + ΔClockAhead⌉₊ ≤ (Model.goldilocks (V := V)).dutyWindowStart S.C s →
      (Model.goldilocks (V := V)).supportCutoff S.C (s + 1) ≤ tN →
      ∀ v : V, v ∉ (activityOf π).corruptedAtTime (toTrace ((Model.goldilocks (V := V)).initial S.C) π)
          (((Model.goldilocks (V := V)).supportCutoff S.C (s + 1) : ℕ) : ℝ) →
        v ∈ honestActiveAt Model.goldilocks S (activityOf π)
            (toTrace ((Model.goldilocks (V := V)).initial S.C) π) s ∧
          v ∈ GoldilocksCorrectness.Record.Statements.AbstractTrace.updaterAt Model.goldilocks S
            (activityOf π) (toTrace ((Model.goldilocks (V := V)).initial S.C) π) s) ∧
    GoldilocksCorrectness.Record.Statements.Executions.HonestOpeningSeq Model.goldilocks S
      (activityOf π) (toTrace ((Model.goldilocks (V := V)).initial S.C) π) r m
      (⌈tGAT + ΔClockAhead⌉₊ + 4 * GoldilocksCorrectness.Statements.Routines.Δ S *
        GoldilocksCorrectness.Statements.Executions.healFrontSlots S) tN := by
  have hΔ0 : (0 : ℝ) < ((S.C.Δ : Time) : ℝ) := by exact_mod_cast S.C.Δ_pos
  have hF0 : (0 : ℝ) ≤ 4 * ((S.C.Δ : Time) : ℝ) *
      (GoldilocksCorrectness.Statements.Executions.healFrontSlots S : ℕ) :=
    mul_nonneg (mul_nonneg (by norm_num) hΔ0.le) (Nat.cast_nonneg _)
  have hfirst := hseq.first
  exact ⟨hActive_toTrace π hCA hCB hΔ hP hH hSkew hAdv hTicks hActs (Nat.le_ceil _) hN hdws,
    hSeq_toTrace π hCB hseq hActs (fun n hn => ceil_add_healFront_le h0 n hn) hNlast
      (by linarith)⟩

omit [ProtocolCommittees (goldilocksProtocol S) (Block V)] [RootOrder] in
/-- The start of the healing phase is at most `route-b`'s natural start `⌈tGAT + ΔClockAhead⌉₊`, the
premise `hG` of `hGST_toTrace` and `hAwake_toTrace`.

The variables:
- `tGAT`: the start of the phase; `ΔClockAhead`: the clock's lead bound, not negative. -/
theorem le_ceil_add {tGAT ΔClockAhead : ℝ} (hCA : 0 ≤ ΔClockAhead) :
    tGAT ≤ ((⌈tGAT + ΔClockAhead⌉₊ : ℕ) : ℝ) :=
  (by linarith : tGAT ≤ tGAT + ΔClockAhead).trans (Nat.le_ceil _)

/-! ### Statement 4's rows: the hand-over slot, the bound on the readings, the period's ends, the lock
holders -/

omit [ProtocolCommittees (goldilocksProtocol S) (Block V)] [RootOrder] in
/-- `route-b`'s delay `Δ S`, a natural number, is the spec's delay.

The variables:
- `S`: the setup. -/
theorem routeb_Δ_cast (S : Setup V) :
    ((GoldilocksCorrectness.Statements.Routines.Δ S : ℕ) : ℝ) = ((S.C.Δ : Time) : ℝ) := by
  unfold GoldilocksCorrectness.Statements.Routines.Δ
  rw [show ((S.C.Δ.toNat : ℕ) : ℝ) = (((S.C.Δ.toNat : ℕ) : ℤ) : ℝ) by push_cast; rfl,
    Int.toNat_of_nonneg S.C.Δ_pos.le]

/-- A validator up and honest throughout `[a, b]` on the observed run is up and honest throughout
every window inside it.

The variables:
- `π`: the run; `a`, `b`: the window; `a'`, `b'`: the window inside it; `v`: the validator. -/
theorem upAndHonest_mono {a b a' b' : ℝ} {v : V} (ha : a ≤ a') (hb : b' ≤ b)
    (h : RStsVariant2.UpAndHonestThroughoutG (observeWithCommittees (Block := Block V) π) a b v) :
    RStsVariant2.UpAndHonestThroughoutG (observeWithCommittees (Block := Block V) π) a' b' v :=
  fun i h1 h2 => h i (ha.trans h1) (h2.trans hb)

open Classical in
/-- **`hp` of `confirmedPersists_asyncPeriod_until`**: the proposer of the hand-over slot `s`, up and
honest on the observed run from `ΔClockAhead` before its proposal window start to `ΔClockBehind` after
the support cutoff of slot `s + 1`, is active on the trace from a tick to its window's start to its
tick to the cutoff, and outside the adversary set at the cutoff and at every honest tick to it.

Why: `honestOpenerAt_of_upAndHonest`, whose conclusion holds `hp`'s.

The variables:
- `π`: the run; `ΔClockAhead`, `ΔClockBehind`: the clock bounds; `hSkew`, `hAdv`, `hTicks`, `hActs`:
  the clock conditions; `s`: the hand-over slot; `h`: the proposer's window on the observed run. -/
theorem hp_toTrace {ΔClockAhead ΔClockBehind : ℝ}
    (hCA : 0 ≤ ΔClockAhead) (hCB : 0 ≤ ΔClockBehind)
    (hΔ : ΔClockAhead + ΔClockBehind < ((S.C.Δ : Time) : ℝ))
    (hSkew : RStsVariant2.ClockWithinSkew ΔClockAhead ΔClockBehind π)
    (hAdv : RStsVariant2.ClockAdvancesWithin ΔClockAhead ΔClockBehind π)
    (hTicks : RStsVariant2.TicksWithin ΔClockBehind π)
    (hActs : RStsVariant2.ActsWithinSkewG ΔClockBehind π) {s : ℕ}
    (h : RStsVariant2.UpAndHonestThroughoutG (observeWithCommittees (Block := Block V) π)
      (((proposal_window_start S.C s : Time) : ℝ) - ΔClockAhead)
      (((S.C.t_ (s + 1) + 2 * S.C.Δ : Time) : ℝ) + ΔClockBehind) (S.P.proposer s)) :
    S.P.proposer s ∈ (activityOf π).activeThroughoutToTick
        (toTrace ((Model.goldilocks (V := V)).initial S.C) π) (proposal_window_start S.C s)
        ((Model.goldilocks (V := V)).supportCutoff S.C (s + 1)) ∧
      S.P.proposer s ∉ (activityOf π).corruptedAtTime
          (toTrace ((Model.goldilocks (V := V)).initial S.C) π)
          ((Model.goldilocks (V := V)).supportCutoff S.C (s + 1)) ∪
        Finset.univ.filter (fun u => ∃ (k : ℕ) (w : V),
          (toTrace ((Model.goldilocks (V := V)).initial S.C) π).lbl k =
            GoldilocksCorrectness.Statements.AbstractTrace.Event.tick w
              ((Model.goldilocks (V := V)).supportCutoff S.C (s + 1)) ∧
          w ∉ (activityOf π).corrupted k ∧ u ∈ (activityOf π).corrupted k) := by
  obtain ⟨hA, hN⟩ := honestOpenerAt_of_upAndHonest π hCA hCB hΔ hSkew hAdv hTicks hActs h
  rw [Finset.mem_union, Finset.mem_union, not_or, not_or] at hN
  exact ⟨hA, by rw [Finset.mem_union, not_or]; exact ⟨hN.1.1, hN.2⟩⟩

omit [ProtocolCommittees (goldilocksProtocol S) (Block V)] [RootOrder] in
/-- **`hs` of `confirmedPersists_asyncPeriod_until`**: a slot that starts after the end of the healing
phase `tA` starts after `route-b`'s natural end of the phase `tN ≤ tA` (Goldilocks's proposer
requirements are for the slots that start after `tA`, `goldilocksProposerReqs`).

The variables:
- `S`: the setup; `tA`: the end of the phase; `tN`: `route-b`'s end of the phase; `s`: the slot. -/
theorem hs_toTrace {tA : ℝ} {tN s : ℕ} (hN : (tN : ℝ) ≤ tA) (hs : tA < ((S.C.t_ s : Time) : ℝ)) :
    tN < (Model.goldilocks (V := V)).slotStart S.C s := by
  have : (tN : ℝ) < (((Model.goldilocks (V := V)).slotStart S.C s : ℕ) : ℝ) := by
    rw [show (((Model.goldilocks (V := V)).slotStart S.C s : ℕ) : ℝ) = ((S.C.t_ s : Time) : ℝ) from
      slotTime_toNat_cast S s]
    linarith
  exact_mod_cast this

omit [ProtocolCommittees (goldilocksProtocol S) (Block V)] in
/-- **`hTt` and `hTk` of `confirmedPersists_asyncPeriod_until`**: a natural `T` at least `t` plus the
clock's lead bound `ΔClockAhead` is at least `t`, and at least every reading of a tick at a trace step
whose time is at most `t`.

Why: a tick at a reading `c` is at a real time at least `c − ΔClockAhead` (`le_stamp_of_clock`).

The variables:
- `π`: the run; `ΔClockAhead`, `ΔClockBehind`: the clock bounds; `hSkew`: the condition; `t`: the time
  the statement reads up to; `T`: the bound on the readings. -/
theorem hTt_hTk_toTrace {ΔClockAhead ΔClockBehind : ℝ} (hCA : 0 ≤ ΔClockAhead)
    (hSkew : RStsVariant2.ClockWithinSkew ΔClockAhead ΔClockBehind π) {t T : ℕ}
    (hT : (t : ℝ) + ΔClockAhead ≤ (T : ℝ)) :
    t ≤ T ∧ ∀ (k : ℕ) (v : V) (c : ℕ),
      (toTrace ((Model.goldilocks (V := V)).initial S.C) π).time k ≤ t →
      (toTrace ((Model.goldilocks (V := V)).initial S.C) π).lbl k =
        GoldilocksCorrectness.Statements.AbstractTrace.Event.tick v c → c ≤ T := by
  refine ⟨by exact_mod_cast (show (t : ℝ) ≤ T by linarith), ?_⟩
  intro k v c hk hl
  obtain ⟨k₀, rfl, -, hc⟩ := GoldilocksVariant.Final.exists_of_lbl_tick _ π hl
  have et : (toTrace ((Model.goldilocks (V := V)).initial S.C) π).time (newIdx π k₀) =
      π.stamp (k₀ + 1) := GoldilocksVariant.Final.toTrace_time_newIdx _ π k₀
  rw [et] at hk
  have hlow := GoldilocksVariant.Final.le_stamp_of_clock π ΔClockAhead ΔClockBehind hSkew hc
  exact_mod_cast (show (c : ℝ) ≤ T by linarith)

omit [ProtocolCommittees (goldilocksProtocol S) (Block V)] [RootOrder] in
/-- **`hb` of `confirmedPersists_asyncPeriod_until`**: `route-b`'s natural ends of the period
`b₀ ≤ tAsyncStart` and `b₁ ≥ tAsyncEnd` are in order when the period is.

The variables:
- `tAS`, `tAE`: the period; `b₀`, `b₁`: `route-b`'s ends of it. -/
theorem hb_toTrace {tAS tAE : ℝ} {b₀ b₁ : ℕ} (h₀ : (b₀ : ℝ) ≤ tAS) (h : tAS ≤ tAE)
    (h₁ : tAE ≤ (b₁ : ℝ)) : b₀ ≤ b₁ := by
  exact_mod_cast h₀.trans (h.trans h₁)

omit [ProtocolCommittees (goldilocksProtocol S) (Block V)] [RootOrder] in
/-- **`hb₁` of `confirmedPersists_asyncPeriod_until`**, from Goldilocks's `AsyncPeriodEndsInTime` (the
period plus its recovery `max Δ Δs − Δ` over by `tPeriodEndBy`, the vote time of slot `s + k` less one
delay): `route-b`'s natural end `b₁` plus `max (Δ S) Δs` is at most the vote time of slot `s + k`,
when `b₁` is at most every natural number at least the period's end `tAE`, and `tAE` is not negative.

Why: the vote time of slot `s + k` less `max Δ Δs` is a natural number at least `tAE`.

The variables:
- `S`: the setup; `Δs`: the sync delay; `tAE`: the end of the period; `s`: the hand-over slot; `b₁`:
  `route-b`'s end of the period. -/
theorem hb₁_toTrace {Δs : ℕ} {tAE : ℝ} {s b₁ : ℕ} (h0 : 0 ≤ tAE)
    (hE : tAE + (max ((S.C.Δ : Time) : ℝ) (Δs : ℝ) - ((S.C.Δ : Time) : ℝ)) ≤
      ((S.C.t_ (s + S.C.k) + S.C.Δ : Time) : ℝ) - ((S.C.Δ : Time) : ℝ))
    (hb₁ : ∀ n : ℕ, tAE ≤ (n : ℝ) → b₁ ≤ n) :
    b₁ + max (GoldilocksCorrectness.Statements.Routines.Δ S) Δs ≤
      (Model.goldilocks (V := V)).voteTime S.C (s + S.C.k) := by
  have hv : (((Model.goldilocks (V := V)).voteTime S.C (s + S.C.k) : ℕ) : ℝ) =
      ((S.C.t_ (s + S.C.k) + S.C.Δ : Time) : ℝ) := by
    apply toNat_cast_real
    have h1 := slotTime_nonneg S (s + S.C.k)
    have h2 : (0 : ℤ) < S.C.Δ := S.C.Δ_pos
    show (0 : ℤ) ≤ S.C.t_ (s + S.C.k) + S.C.Δ
    omega
  set M' := max (GoldilocksCorrectness.Statements.Routines.Δ S) Δs with hM'
  have hMR : ((M' : ℕ) : ℝ) = max ((S.C.Δ : Time) : ℝ) (Δs : ℝ) := by
    rw [hM', Nat.cast_max, routeb_Δ_cast]
  set vt := (Model.goldilocks (V := V)).voteTime S.C (s + S.C.k) with hvt
  have hle : M' ≤ vt := by
    have : ((M' : ℕ) : ℝ) ≤ ((vt : ℕ) : ℝ) := by rw [hMR, hv]; linarith
    exact_mod_cast this
  have := hb₁ (vt - M') (by rw [Nat.cast_sub hle, hMR, hv]; linarith)
  omega

open Classical in
/-- **`hHold` of `confirmedPersists_asyncPeriod_until`** (`HoldersOutweighWhereOwed`), from Goldilocks's
`AsyncPeriodSleepinessG` with Goldilocks's committees: at every slot `s' ≥ s + 2` whose previous slot's
votes are owed inside `route-b`'s period `[b₀, b₁)`, the lock holders of slot `s` acting at slot `s'`
outnumber the rest of slot `s'`'s committee.

Why: such a slot `s'` is at most `s + k` (its previous slot's cutoff plus one delay is less than the
vote time of slot `s + k`, `hEnd`), and its committee is affected by the period (`hb₀`, `hb₁`). The
hand-over slot's proposer is up and honest at `tPreAsync`, inside the committee's sleepiness window
(which starts at most one delay after the start of slot `s`), so most of slot `s'`'s committee is up
and honest through `[tPreAsync − ΔPreAsync, tPreAsync]` and through the window; such a member is an
updater of slot `s` (`mem_updaterAt_of_upAndHonest`, `hPreStart`) and an honest active validator of
slot `s'` (`mem_honestActiveAt_of_upAndHonest`), a lock holder.

The variables:
- `π`: the run; `Δs`: the sync delay; `ΔClockAhead`, `ΔClockBehind`: the clock bounds; `hSkew`, `hAdv`,
  `hTicks`, `hActs`: the clock conditions; `hcom`: the observed run's committees are Goldilocks's;
  `tPreAsync`, `ΔPreAsync`, `tAS`, `tAE`, `ΔRecovery`: the condition's times; `hSl`: the condition;
  `s`: the hand-over slot; `tA`, `tP`, `vP`, `hW`: the hand-over slot's proposer, up and honest
  through `[tP, tPreAsync]`; `hPre`, `hPreStart`: `tPreAsync` and its start; `b₀`, `b₁`: `route-b`'s
  ends of the period; `hb₀`: every natural number greater than `b₀` is later than `tAS`; `hb₁`: every
  natural number whose sum with `Δ S` is less than `b₁ + max (Δ S) Δs` is less than `tAE + ΔRecovery`;
  `hEnd`: `route-b`'s `hb₁`. -/
theorem hHoldOutweigh_toTrace {Δs : ℕ} {ΔClockAhead ΔClockBehind tA tP tPreAsync ΔPreAsync tAS tAE ΔRecovery : ℝ}
    (hCA : 0 ≤ ΔClockAhead) (hCB : 0 ≤ ΔClockBehind)
    (hΔ : ΔClockAhead + ΔClockBehind < ((S.C.Δ : Time) : ℝ))
    (hSkew : RStsVariant2.ClockWithinSkew ΔClockAhead ΔClockBehind π)
    (hAdv : RStsVariant2.ClockAdvancesWithin ΔClockAhead ΔClockBehind π)
    (hTicks : RStsVariant2.TicksWithin ΔClockBehind π)
    (hActs : RStsVariant2.ActsWithinSkewG ΔClockBehind π)
    (hcom : ∀ ci : ℕ, RStsVariant2.ObservableWithCommittees.committees
      (observeWithCommittees (Block := Block V) π) ci =
        goldilocksCommitteeSpecs S ΔClockAhead ΔClockBehind ci)
    (hSl : RStsVariant2.AsyncPeriodSleepinessG tPreAsync ΔPreAsync tAS tAE ΔRecovery
      (observeWithCommittees (Block := Block V) π))
    {s : ℕ} {vP : V}
    (hW : RStsVariant2.HonestProposerThroughG tA tPreAsync tP vP
      (observeWithCommittees (Block := Block V) π))
    (hPre : tPreAsync = ((S.C.t_ (s + 1) + 2 * S.C.Δ : Time) : ℝ) + ΔClockBehind)
    (hPreStart : tPreAsync - ΔPreAsync ≤ ((duty_window_start S.C (s + 1) : Time) : ℝ) - ΔClockAhead)
    {b₀ b₁ : ℕ} (hb₀ : ∀ n : ℕ, b₀ < n → tAS < (n : ℝ))
    (hb₁ : ∀ n : ℕ, n + GoldilocksCorrectness.Statements.Routines.Δ S <
      b₁ + max (GoldilocksCorrectness.Statements.Routines.Δ S) Δs → (n : ℝ) < tAE + ΔRecovery)
    (hEnd : b₁ + max (GoldilocksCorrectness.Statements.Routines.Δ S) Δs ≤
      (Model.goldilocks (V := V)).voteTime S.C (s + S.C.k)) :
    GoldilocksCorrectness.Record.Statements.Executions.HoldersOutweighWhereOwed Model.goldilocks S
      (activityOf π) (toTrace ((Model.goldilocks (V := V)).initial S.C) π) s Δs b₀ b₁ := by
  intro s' hss' hb0 hb1
  have hΔ0 : (0 : ℝ) < ((S.C.Δ : Time) : ℝ) := by exact_mod_cast S.C.Δ_pos
  have hcut' : (((Model.goldilocks (V := V)).supportCutoff S.C (s' - 1) : ℕ) : ℝ) =
      ((S.C.t_ (s' - 1) + 2 * S.C.Δ : Time) : ℝ) := cutoff_toNat_cast S (s' - 1)
  -- the committee of slot `s'` is affected by the period
  have haff : RStsVariant2.AffectedByAsync (RStsVariant2.ObservableWithCommittees.committees
      (observeWithCommittees (Block := Block V) π) s') tAS tAE ΔRecovery := by
    rw [hcom]
    refine ⟨?_, ?_⟩
    · show tAS < ((S.C.t_ (s' - 1) + 2 * S.C.Δ : Time) : ℝ)
      rw [← hcut']; exact hb₀ _ hb0
    · show ((S.C.t_ (s' - 1) + 2 * S.C.Δ : Time) : ℝ) < tAE + ΔRecovery
      rw [← hcut']; exact hb₁ _ hb1
  -- `s' ≤ s + k`
  have hsk : s' ≤ s + S.C.k := by
    have h1 : (Model.goldilocks (V := V)).supportCutoff S.C (s' - 1) +
        GoldilocksCorrectness.Statements.Routines.Δ S <
        (Model.goldilocks (V := V)).voteTime S.C (s + S.C.k) := lt_of_lt_of_le hb1 hEnd
    have hv : (((Model.goldilocks (V := V)).voteTime S.C (s + S.C.k) : ℕ) : ℝ) =
        ((S.C.t_ (s + S.C.k) + S.C.Δ : Time) : ℝ) := by
      apply toNat_cast_real
      have h1 := slotTime_nonneg S (s + S.C.k)
      have h2 : (0 : ℤ) < S.C.Δ := S.C.Δ_pos
      show (0 : ℤ) ≤ S.C.t_ (s + S.C.k) + S.C.Δ
      omega
    have h1R : (((Model.goldilocks (V := V)).supportCutoff S.C (s' - 1) : ℕ) : ℝ) +
        ((GoldilocksCorrectness.Statements.Routines.Δ S : ℕ) : ℝ) <
        (((Model.goldilocks (V := V)).voteTime S.C (s + S.C.k) : ℕ) : ℝ) := by exact_mod_cast h1
    rw [hcut', routeb_Δ_cast, hv] at h1R
    push_cast at h1R
    have h2 : ((S.C.t_ (s' - 1) : Time) : ℝ) < ((S.C.t_ (s + S.C.k) : Time) : ℝ) := by linarith
    have h3 : S.C.t_ (s' - 1) < S.C.t_ (s + S.C.k) := by exact_mod_cast h2
    have := lt_of_slotTime_lt S h3
    omega
  -- the slot times, as reals
  have hk0 : (0 : ℝ) ≤ ((S.C.t_ S.C.k : Time) : ℝ) := by exact_mod_cast slotTime_nonneg S S.C.k
  have hdws' : ((duty_window_start S.C s' : Time) : ℝ) ≤ ((S.C.t_ s : Time) : ℝ) + ((S.C.Δ : Time) : ℝ) := by
    have h1 : ((S.C.t_ s' : Time) : ℝ) ≤ ((S.C.t_ (s + S.C.k) : Time) : ℝ) := by
      exact_mod_cast slotTime_mono S hsk
    have h2 : ((S.C.t_ (s + S.C.k) : Time) : ℝ) = ((S.C.t_ s : Time) : ℝ) + ((S.C.t_ S.C.k : Time) : ℝ) := by
      rw [slotTime_eq, slotTime_eq, slotTime_eq]; push_cast; ring
    rw [duty_window_start_eq_slotTime]; push_cast
    linarith
  have hcs : ((S.C.t_ (s + 1) : Time) : ℝ) ≤ ((S.C.t_ (s' + 1) : Time) : ℝ) := by
    exact_mod_cast slotTime_mono S (show s + 1 ≤ s' + 1 by omega)
  have hss : ((S.C.t_ s : Time) : ℝ) ≤ ((S.C.t_ (s + 1) : Time) : ℝ) := by
    exact_mod_cast slotTime_mono S (Nat.le_succ s)
  have hPreR : tPreAsync = ((S.C.t_ (s + 1) : Time) : ℝ) + 2 * ((S.C.Δ : Time) : ℝ) + ΔClockBehind := by
    rw [hPre]; push_cast; ring
  have hsucc : ((S.C.t_ (s + 1) : Time) : ℝ) = ((S.C.t_ s : Time) : ℝ) + 4 * ((S.C.Δ : Time) : ℝ) := by
    exact_mod_cast slotTime_succ S s
  have hPre0 : (0 : ℝ) ≤ tPreAsync := by
    have := slotTime_nonneg S (s + 1)
    have h1 : (0 : ℝ) ≤ ((S.C.t_ (s + 1) : Time) : ℝ) := by exact_mod_cast this
    linarith
  -- the configuration in force at `tPreAsync`, with the hand-over proposer up and honest in it
  have hex : ∃ n : ℕ, tPreAsync ≤ π.stamp (n + 1) := by
    obtain ⟨n, hn⟩ := π.progress tPreAsync
    exact ⟨n, hn.trans (π.mono n)⟩
  have hi1 : tPreAsync ≤ π.stamp (Nat.find hex + 1) := Nat.find_spec hex
  have hi0 : π.stamp (Nat.find hex) ≤ tPreAsync := by
    rcases h : Nat.find hex with _ | n
    · rw [π.stamp_zero]; exact hPre0
    · have := Nat.find_min hex (show n < Nat.find hex by omega)
      exact (not_le.mp this).le
  obtain ⟨-, hst, hhon⟩ := hW.2.2 (Nat.find hex) (hW.2.1.trans hi1) hi0
  obtain ⟨l, hl⟩ := Option.ne_none_iff_exists'.mp hst
  have hi1' : tPreAsync ≤ RStsVariant2.Observable.stamp (observeWithCommittees (Block := Block V) π)
      (Nat.find hex + 1) := hi1
  have hi0' : RStsVariant2.Observable.stamp (observeWithCommittees (Block := Block V) π)
      (Nat.find hex) ≤ tPreAsync := hi0
  have hMost := hSl s' haff vP (Nat.find hex) l hl hhon
    (by rw [hcom]; show ((duty_window_start S.C s' : Time) : ℝ) - ΔClockAhead ≤ _; linarith)
    (by
      rw [hcom]
      show _ ≤ ((S.C.t_ (s' + 1) + 2 * S.C.Δ : Time) : ℝ) + ΔClockBehind
      push_cast; linarith)
  rw [hcom] at hMost
  -- a member with both windows is a lock holder
  have hP : ∀ v : V,
      (RStsVariant2.UpAndHonestThroughoutG (observeWithCommittees (Block := Block V) π)
          (tPreAsync - ΔPreAsync) tPreAsync v ∧
        RStsVariant2.UpAndHonestThroughoutG (observeWithCommittees (Block := Block V) π)
          (goldilocksCommitteeSpecs S ΔClockAhead ΔClockBehind s').sleepinessWindow.tStart
          (goldilocksCommitteeSpecs S ΔClockAhead ΔClockBehind s').sleepinessWindow.tEnd v) →
      v ∈ GoldilocksCorrectness.Record.Statements.AbstractTrace.holdersAt Model.goldilocks S
        (activityOf π) (toTrace ((Model.goldilocks (V := V)).initial S.C) π) s s' := by
    intro v ⟨h1, h2⟩
    unfold GoldilocksCorrectness.Record.Statements.AbstractTrace.holdersAt
    refine Finset.mem_inter.2 ⟨mem_updaterAt_of_upAndHonest π hCA hCB hΔ hSkew hAdv hTicks
      (upAndHonest_mono π hPreStart (le_of_eq hPre.symm) h1), ?_⟩
    exact mem_honestActiveAt_of_upAndHonest π hCA hCB hΔ hSkew hAdv hTicks hActs h2
  unfold RStsVariant2.MostOf at hMost
  refine lt_of_le_of_lt (Finset.card_le_card ?_) (lt_of_lt_of_le hMost (Finset.card_le_card ?_))
  · intro v hv
    simp only [Finset.mem_sdiff, Finset.mem_filter] at hv ⊢
    exact ⟨hv.1, fun hPv => hv.2 (hP v hPv)⟩
  · intro v hv
    simp only [Finset.mem_filter] at hv
    exact Finset.mem_inter.2 ⟨hP v hv.2, hv.1⟩

/-! ### `hDelT` of statement 4, and the finality delivery's window -/

/-- **The trace's delivery promise and catch-up after a restart for blocks and Goldfish votes, outside
the period `[b₀, b₁)`** (`EnvFactsOutside`), at the network's delay `ΔNet`, the catch-up delay `Δs` and
the time `⌈tGST⌉₊`, from the conditions every top statement takes on the observed run with the
deadlines outside the period and Goldilocks's extra condition on redelivery, when `b₀ ≤ tAsyncStart`
and `tAsyncEnd ≤ b₁`.

Why: `GoldilocksVariant.Final.envFactsOutside_toTrace`, each condition read on the run (section 1); a
block or a Goldfish vote has the delay `ΔNet − ΔClockAhead` and the catch-up delay `Δs − ΔClockAhead`.

The variables: as for `syncedWithinOutside_of_conditions`. -/
theorem envFactsOutside_of_conditions {tGST tAsyncStart tAsyncEnd : ℝ}
    {ΔClockAhead ΔClockBehind : ℝ≥0} {tGAT tAwakeEnd : ℝ}
    {H : (segment : (i : ℕ) → Option (PhaseStep V (NamedObject V) (Block V))) → Prop}
    {ΔNet ΔNet_F ΔRedeliver Δs Δs_F b₀ b₁ : ℕ}
    (hC : TopStatementConditions tGST
      (RStsVariant2.deadlineOutside tGST (goldilocksΔNetDelivery ΔNet ΔNet_F ΔClockAhead)
        tAsyncStart tAsyncEnd)
      (RStsVariant2.deadlineOutside tGST (goldilocksΔSyncCatchUp Δs Δs_F ΔClockAhead)
        tAsyncStart tAsyncEnd) ΔClockAhead
      ΔClockBehind tGAT tAwakeEnd H (observeWithCommittees (Block := Block V) π))
    (hRe : RedeliveredAfterReleaseFromDelivery (goldilocksRelease S) (ΔRedeliver : ℝ)
      (observeWithCommittees (Block := Block V) π))
    (hb₀ : (b₀ : ℝ) ≤ tAsyncStart) (hb₁ : tAsyncEnd ≤ b₁) :
    GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsOutside (activityOf π)
      (toTrace ((Model.goldilocks (V := V)).initial S.C) π) ΔClockAhead ΔClockBehind ΔNet Δs
      ΔRedeliver ⌈tGST⌉₊ (GoldilocksCorrectness.Record.Statements.AbstractTrace.releaseOf
        Model.goldilocks S.C) GoldilocksCorrectness.Statements.Executions.acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks b₀ b₁ := by
  rw [GoldilocksVariant.Final.releaseOf_goldilocks]
  refine GoldilocksVariant.Final.envFactsOutside_toTrace (M := Model.goldilocks) goldilocksFacts π
    ΔClockAhead.2 ΔClockBehind.2 hC.tickOnce hC.clockWithinSkew
    ((RStsVariant2.clockAdvancesWithin_observe NodeViewOf.view π _ _).1 hC.clockAdvances)
    ((RStsVariant2.ticksWithin_observe NodeViewOf.view π _).1 hC.ticksWithin) hC.actsWithinSkew
    hC.unforgeable
    ((RStsVariant2.deliveredBeforeActingG_observe NodeViewOf.view π RStsVariant2.TickStepG
      RStsVariant2.TickStepG (fun _ _ => Iff.rfl) _).1 hC.delivered)
    ((RStsVariant2.catchUpAfterRestartG_observe NodeViewOf.view π RStsVariant2.TickStepG
      RStsVariant2.TickStepG (fun _ _ => Iff.rfl) _ _).1 hC.catchUp)
    (redelivered_run π hRe) (Nat.le_ceil tGST) ?_ ?_ hb₀ hb₁
  · intro m hm
    cases m <;> simp_all [goldilocksΔNetDelivery, GoldilocksCorrectness.Statements.Executions.acObject]
  · intro m hm
    cases m <;> simp_all [goldilocksΔSyncCatchUp, GoldilocksCorrectness.Statements.Executions.acObject]

omit [ProtocolCommittees (goldilocksProtocol S) (Block V)] in
/-- **`hDelT` of `confirmedPersists_asyncPeriod_until`**, from the trace's run facts
(`runFacts_toTrace`) and the promises outside the period (`envFactsOutside_of_conditions`), at the
catch-up delay `Δs`: `delT_of_envFactsOutside` at `Δw := Δs ≤ max (Δ S) Δs`.

The variables:
- `π`: the run; `EO`: the promises outside the period at the delay
  `ΔNet` and the catch-up delay `Δs`; `hNet`, `hSkew`, `hRedeliver`, `hΔs`: the delays;
  `hParent`: parents held at delivery on the trace; `GST`, `s`, `b₀`, `b₁`: `route-b`'s times;
  `hGST`, `hb₀`, `hb`, `hb₁`: `route-b`'s premises on them. -/
theorem hDelT_toTrace
    {ΔClockAhead ΔClockBehind : ℝ} {ΔNet ΔRedeliver Δs GST s b₀ b₁ : ℕ}
    (EO : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsOutside (activityOf π)
      (toTrace ((Model.goldilocks (V := V)).initial S.C) π) ΔClockAhead ΔClockBehind ΔNet Δs
      ΔRedeliver GST (GoldilocksCorrectness.Record.Statements.AbstractTrace.releaseOf
        Model.goldilocks S.C) GoldilocksCorrectness.Statements.Executions.acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks b₀ b₁)
    (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ GoldilocksCorrectness.Statements.Routines.Δ S)
    (hSkew : ΔClockAhead + ΔClockBehind < GoldilocksCorrectness.Statements.Routines.Δ S)
    (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤
      GoldilocksCorrectness.Statements.Routines.Δ S)
    (hParent : GoldilocksCorrectness.Record.Statements.Executions.ParentHeldAtDelivery
      Model.goldilocks (toTrace ((Model.goldilocks (V := V)).initial S.C) π))
    (hΔs : (max (GoldilocksCorrectness.Statements.Routines.Δ S) Δs : ℝ) +
      3 * GoldilocksCorrectness.Statements.Routines.Δ S + ΔClockAhead + ΔClockBehind <
        4 * GoldilocksCorrectness.Statements.Routines.Δ S * S.C.k)
    (hGST : GST + max (GoldilocksCorrectness.Statements.Routines.Δ S) Δs ≤
      (Model.goldilocks (V := V)).supportCutoff S.C (s + 1))
    (hb₀ : (Model.goldilocks (V := V)).supportCutoff S.C (s + 1) ≤ b₀) (hb : b₀ ≤ b₁)
    (hb₁ : b₁ + max (GoldilocksCorrectness.Statements.Routines.Δ S) Δs ≤
      (Model.goldilocks (V := V)).voteTime S.C (s + S.C.k)) :
    ∀ B : Block V, GoldilocksCorrectness.Record.Statements.Executions.DelTLine Model.goldilocks S
      (activityOf π) (toTrace ((Model.goldilocks (V := V)).initial S.C) π) s B b₀ b₁ Δs :=
  fun _ => (GoldilocksCorrectness.Record.Proofs.Executions.delT_of_envFactsOutside Model.goldilocks
    goldilocksFacts GoldilocksCorrectness.Record.uniformSchedule_goldilocks)
    (GoldilocksVariant.Final.runFacts_toTrace goldilocksFacts π) EO hNet hSkew
    hRedeliver hParent hΔs (le_max_right _ _) hGST hb₀ hb hb₁

/-- The observed run's step `k` that is `v`'s tick at the clock value `c₀` (`TickAtG`) is the trace
step `newIdx π k`, labelled `Event.tick v c₀`.

Why: the trace step of the run's step `k` is labelled `eventOf π k` (`toTrace_lbl_newIdx`), which is
`v`'s tick at `c₀` exactly when the run's step `k` is `v`'s tick and `v`'s clock reads `c₀` in
configuration `k` (`eventOf_eq_tick`); the observed run's step and clock are the run's.

The variables:
- `π`: the run; `k`: the step; `v`: the validator; `c₀`: the clock value. -/
theorem toTrace_lbl_newIdx_of_tickAtG {k c₀ : ℕ} {v : V}
    (hk : TickAtG (observeWithCommittees (Block := Block V) π) k v c₀) :
    (toTrace ((Model.goldilocks (V := V)).initial S.C) π).lbl (newIdx π k) =
      GoldilocksCorrectness.Statements.AbstractTrace.Event.tick v c₀ :=
  (GoldilocksVariant.Final.toTrace_lbl_newIdx _ π k).trans
    ((GoldilocksVariant.Final.eventOf_eq_tick π).2 hk)

/-- **The window of `AwakeForDelayWithin`** (`route-b`'s reader of a node that has been up for the
finality delivery delay): a validator that ticks on the observed run at the clock value `c₀` and is
up and honest there throughout `[c₀, c₀ + L]`, `t ≤ c₀`, is awake for `max (Δ S) Δs` within `t` and
every step `j` at or after every trace step whose time is at most `c₀ + L`, when `L` is at least
`max (Δ S) Δs + ΔClockBehind` and `ΔClockAhead` is at most `max (Δ S) Δs`.

Why: with `c₂ := c₀` and `c := c₀ + max (Δ S) Δs`, the validator's tick at `c₀` is the trace's
(`toTrace_lbl_newIdx_of_tickAtG`), and it ticks on the trace to `c` (`trace_tick_of_upAndHonest`:
`c − ΔClockAhead ≥ c₀`, `c + ΔClockBehind ≤ c₀ + L`) at a trace step whose time is at most `c₀ + L`,
so at or before `j`; it is active, hence awake, at every trace step from the real time `c₀` up to
that tick (`activeThroughout_of_upAndHonest`).

The variables:
- `π`: the run; `ΔClockAhead`, `ΔClockBehind`: the clock bounds; `hSkew`, `hAdv`, `hTicks`: the clock
  conditions; `Δs`: the sync delay; `k₀`, `c₀`: the step and clock value of the tick that opens the
  window; `L`: the window's length; `t`: the time the reader starts at; `v`: the validator; `j`: the
  step. -/
theorem awakeForDelayWithin_of_upAndHonest {ΔClockAhead ΔClockBehind : ℝ}
    (hCA : 0 ≤ ΔClockAhead) (hCB : 0 ≤ ΔClockBehind)
    (hSkew : RStsVariant2.ClockWithinSkew ΔClockAhead ΔClockBehind π)
    (hAdv : RStsVariant2.ClockAdvancesWithin ΔClockAhead ΔClockBehind π)
    (hTicks : RStsVariant2.TicksWithin ΔClockBehind π) {Δs k₀ c₀ : ℕ} {L t : ℝ} {v : V} {j : ℕ}
    (hk : TickAtG (observeWithCommittees (Block := Block V) π) k₀ v c₀)
    (h : RStsVariant2.UpAndHonestThroughoutG (observeWithCommittees (Block := Block V) π) c₀
      (c₀ + L) v)
    (ht : t ≤ c₀)
    (hA : ΔClockAhead ≤ ((max (GoldilocksCorrectness.Statements.Routines.Δ S) Δs : ℕ) : ℝ))
    (hL : ((max (GoldilocksCorrectness.Statements.Routines.Δ S) Δs : ℕ) : ℝ) + ΔClockBehind ≤ L)
    (hj : ∀ k : ℕ, (toTrace ((Model.goldilocks (V := V)).initial S.C) π).time k ≤ c₀ + L → k ≤ j) :
    GoldilocksCorrectness.Statements.AbstractTrace.View.AwakeForDelayWithin S (activityOf π)
      (toTrace ((Model.goldilocks (V := V)).initial S.C) π) Δs v t j := by
  set x := toTrace ((Model.goldilocks (V := V)).initial S.C) π with hx
  set D := max (GoldilocksCorrectness.Statements.Routines.Δ S) Δs with hD
  have hAct := activeThroughout_of_upAndHonest π h
  simp only [Activity.activeThroughout, Finset.mem_filter, Finset.mem_univ, true_and] at hAct
  have tm : ∀ {a b : ℕ}, a ≤ b → x.time a ≤ x.time b := fun hab =>
    GoldilocksVariant.Final.toTrace_time_mono ((Model.goldilocks (V := V)).initial S.C) π hab
  obtain ⟨k, hk', hk1, hk2⟩ := trace_tick_of_upAndHonest π hCA hCB hSkew hAdv hTicks
    (c := c₀ + D) h (by push_cast; linarith) (by push_cast; linarith)
  refine ⟨c₀, c₀ + D, c₀, k, newIdx π k₀, ht, le_rfl, hk',
    hj k (hk2.trans (by push_cast; linarith)), ?_, toTrace_lbl_newIdx_of_tickAtG π hk, ht, ?_⟩
  · intro i hi hik
    have h1 := hAct i ((tm hik).trans (hk2.trans (by push_cast; linarith)))
      (by have := tm (Nat.le_succ i)
          linarith)
    exact (Finset.mem_sdiff.1 h1).1
  · exact Nat.add_le_add_left (le_max_left _ _) _

/-- **A block sent at the proposer's tick at the start of its slot, on the observed run, is a
proposal on the trace**: the observed run's step `i` of `ProposedAtSlotStart S τ s B` is the trace
step `newIdx π i`, the tick of slot `s`'s proposer at the start of slot `s`, which adds the signed
message `⟨S.P.proposer s, .block B⟩` to the trace's sent log.

Why: the tick is the trace's (`toTrace_lbl_newIdx_of_tickAtG`); the trace's sent log around that
step is the run's, each envelope read as a signed message (`toTrace_sent_newIdx`,
`toTrace_sent_newIdx_succ`), and the run's sent log only grows (`sent_mono`).

The variables:
- `π`: the run; `s`: the slot; `B`: the block. -/
theorem proposalAt_of_proposedAtSlotStart {s : ℕ} {B : Block V}
    (h : ProposedAtSlotStart S (observeWithCommittees (Block := Block V) π) s B) :
    ∃ i : ℕ, (toTrace ((Model.goldilocks (V := V)).initial S.C) π).lbl i =
        GoldilocksCorrectness.Statements.AbstractTrace.Event.tick (S.P.proposer s)
          ((Model.goldilocks (V := V)).slotStart S.C s) ∧
      (⟨S.P.proposer s, NamedObject.block B⟩ : Framework.StsMultisetLog.SignedMsg V (NamedObject V)) ∈
        (toTrace ((Model.goldilocks (V := V)).initial S.C) π).sent (i + 1) -
          (toTrace ((Model.goldilocks (V := V)).initial S.C) π).sent i := by
  obtain ⟨i, e, hT, he, hs, hm⟩ := h
  refine ⟨newIdx π i, toTrace_lbl_newIdx_of_tickAtG π hT, ?_⟩
  have e1 : (toTrace ((Model.goldilocks (V := V)).initial S.C) π).sent (newIdx π i + 1) =
      π[i + 1].sent.map GoldilocksVariant.Final.traceMsg :=
    GoldilocksVariant.Final.toTrace_sent_newIdx_succ _ π i
  have e0 : (toTrace ((Model.goldilocks (V := V)).initial S.C) π).sent (newIdx π i) =
      π[i].sent.map GoldilocksVariant.Final.traceMsg :=
    GoldilocksVariant.Final.toTrace_sent_newIdx _ π i
  rw [e1, e0]
  have hle : π[i].sent ≤ π[i + 1].sent := π.sent_mono (Nat.le_succ i)
  have he' : e ∈ π[i + 1].sent - π[i].sent := he
  have hd : π[i + 1].sent = π[i].sent + (π[i + 1].sent - π[i].sent) :=
    (add_tsub_cancel_of_le hle).symm
  rw [hd, Multiset.map_add, add_tsub_cancel_left]
  refine Multiset.mem_map.2 ⟨e, he', ?_⟩
  show (⟨e.sender, e.msg⟩ : Framework.StsMultisetLog.SignedMsg V (NamedObject V)) = _
  rw [hs, hm]

/-- **`route-b`'s finality reader at the trace step that holds a configuration entered after the
reader's window.** A validator that ticks on the observed run at the clock value `c₀`, is up and
honest there throughout `[c₀, c₀ + L]`, `t ≤ c₀`, read in a configuration `k` entered after
`c₀ + L` (`c₀ + L < π.stamp k`), is awake for `max (Δ S) Δs` within `t` and the trace step
`2 k + ⌊π.stamp k⌋₊` that holds configuration `k`, when `L` is at least `max (Δ S) Δs + ΔClockBehind`
and `ΔClockAhead` at most `max (Δ S) Δs`.

Why: every trace step after `2 k + ⌊π.stamp k⌋₊` is at a time at least `π.stamp k`
(`toTrace_time_entry`, `toTrace_time_mono`), so every trace step at a time at most `c₀ + L` is at or
before it; `awakeForDelayWithin_of_upAndHonest`.

The variables:
- `π`: the run; the clock bounds and conditions as in `awakeForDelayWithin_of_upAndHonest`; `k₀`,
  `c₀`: the tick; `L`: the window's length; `t`: the time the reader starts at; `v`: the
  validator; `k`: the configuration. -/
theorem awakeForDelayWithin_at_entry {ΔClockAhead ΔClockBehind : ℝ}
    (hCA : 0 ≤ ΔClockAhead) (hCB : 0 ≤ ΔClockBehind)
    (hSkew : RStsVariant2.ClockWithinSkew ΔClockAhead ΔClockBehind π)
    (hAdv : RStsVariant2.ClockAdvancesWithin ΔClockAhead ΔClockBehind π)
    (hTicks : RStsVariant2.TicksWithin ΔClockBehind π) {Δs k₀ c₀ : ℕ} {L t : ℝ} {v : V} {k : ℕ}
    (hk : TickAtG (observeWithCommittees (Block := Block V) π) k₀ v c₀)
    (h : RStsVariant2.UpAndHonestThroughoutG (observeWithCommittees (Block := Block V) π) c₀
      (c₀ + L) v)
    (ht : t ≤ c₀)
    (hA : ΔClockAhead ≤ ((max (GoldilocksCorrectness.Statements.Routines.Δ S) Δs : ℕ) : ℝ))
    (hL : ((max (GoldilocksCorrectness.Statements.Routines.Δ S) Δs : ℕ) : ℝ) + ΔClockBehind ≤ L)
    (hlt : (c₀ : ℝ) + L < π.stamp k) :
    GoldilocksCorrectness.Statements.AbstractTrace.View.AwakeForDelayWithin S (activityOf π)
      (toTrace ((Model.goldilocks (V := V)).initial S.C) π) Δs v t (2 * k + ⌊π.stamp k⌋₊) := by
  refine awakeForDelayWithin_of_upAndHonest π hCA hCB hSkew hAdv hTicks hk h ht hA hL ?_
  intro k' hk'
  by_contra hgt
  have hmono := GoldilocksVariant.Final.toTrace_time_mono ((Model.goldilocks (V := V)).initial S.C) π
    (le_of_lt (lt_of_not_ge hgt))
  rw [GoldilocksVariant.Final.toTrace_time_entry] at hmono
  linarith

open GoldilocksCorrectness.Record.Statements.Executions (HonestOpenerAt FinalityWindowAt
  RootCollisionAtProposal RootCollisionAtOpening FinalityIncludedBetween) in
/-- **Statement 3's inclusion, read back from the trace at one reader** (`route-b`'s Lemma 98
conclusion `FinalityIncludedBetween`, read at the natural time `n`). For a slot `s` with the
premises of that conclusion at the round `r`, a block `B` slot `s`'s proposer sent at its tick at the
start of slot `s` on the observed run (`ProposedAtSlotStart`), and a validator `v` with a local state
`lc` known in the run's configuration `k`, honest in every configuration entered by then, entered at
or before a support cutoff at most `n`, and `route-b`'s finality reader at the trace step that holds
configuration `k`: either a root collision at the proposal or at one of the window's four honest
round opening slots, or `B` is the finalized block of `v`'s view there or an ancestor of it, and no
validator had that finalized block in a configuration of the run entered before the start of slot
`s`.

Why: the proposal is the trace's (`proposalAt_of_proposedAtSlotStart`); configuration `k` is held by
the trace step `2 k + ⌊π.stamp k⌋₊`, at the real time `π.stamp k`, with `v` honest through it
(`entry_of_honestThroughEntry`) and its node state `lc.st` there (`toTrace_st`, `origBefore_entry`);
every earlier configuration `k'` is held likewise at the time `π.stamp k'`
(`finalityIncludedBetween_unfold`).

The variables:
- `π`: the run; `Δs`: the sync delay; `tE`: the time from which the slots are read; `n`: the time
  the trace's conclusion is read at; `s`, `r`: the slot and the round; `B`: the proposal; `v`, `k`,
  `lc`: the reader, its configuration and its local state. -/
theorem finalizedIncluded_of_trace {Δs tE n s r k : ℕ} {B : Block V} {v : V}
    {lc : RStsVariant2.Local V (NamedObject V) (NodeState V)}
    (h : FinalityIncludedBetween Model.goldilocks S (activityOf π)
      (toTrace ((Model.goldilocks (V := V)).initial S.C) π) Δs tE n)
    (hs : tE ≤ (Model.goldilocks (V := V)).slotStart S.C s)
    (hO : HonestOpenerAt Model.goldilocks S (activityOf π)
      (toTrace ((Model.goldilocks (V := V)).initial S.C) π) s)
    (hsr : s ≤ r * S.C.R)
    (hW : FinalityWindowAt Model.goldilocks S (activityOf π)
      (toTrace ((Model.goldilocks (V := V)).initial S.C) π) r)
    (hcut : (Model.goldilocks (V := V)).supportCutoff S.C ((r + 3) * S.C.R + 1) ≤ n)
    (hB : ProposedAtSlotStart S (observeWithCommittees (Block := Block V) π) s B)
    (hlc : π[k][v] = some lc) (hH : ∀ j : ℕ, π.stamp j ≤ π.stamp k → v ∉ π[j].adv)
    (hk : ∃ s' : ℕ, π.stamp k ≤ ((Model.goldilocks (V := V)).supportCutoff S.C s' : ℝ) ∧
      (Model.goldilocks (V := V)).supportCutoff S.C s' ≤ n)
    (hAw : GoldilocksCorrectness.Statements.AbstractTrace.View.AwakeForDelayWithin S (activityOf π)
      (toTrace ((Model.goldilocks (V := V)).initial S.C) π) Δs v
      ((Model.goldilocks (V := V)).slotStart S.C ((r + 3) * S.C.R)) (2 * k + ⌊π.stamp k⌋₊)) :
    RootCollisionAtProposal Model.goldilocks S (activityOf π)
        (toTrace ((Model.goldilocks (V := V)).initial S.C) π) s B ∨
      RootCollisionAtOpening Model.goldilocks S (activityOf π)
        (toTrace ((Model.goldilocks (V := V)).initial S.C) π) (fun i => r + i) 3 ∨
      (BlockVocab.anc B (NodeViewOf.view lc.st).F ∧
        ∀ (v' : V) (k' : ℕ) (lc' : RStsVariant2.Local V (NamedObject V) (NodeState V)),
          π[k'][v'] = some lc' → π.stamp k' < ((Model.goldilocks (V := V)).slotStart S.C s : ℝ) →
          (NodeViewOf.view lc'.st).F ≠ (NodeViewOf.view lc.st).F) := by
  rw [GoldilocksCorrectness.Record.Proofs.View.finalityIncludedBetween_unfold] at h
  obtain ⟨-, hall⟩ := h s r hs hO hsr hW hcut
  obtain ⟨i₀, hl₀, hm₀⟩ := proposalAt_of_proposedAtSlotStart π hB
  have hstE : ∀ (k' : ℕ) (w : V) (l : RStsVariant2.Local V (NamedObject V) (NodeState V)),
      π[k'][w] = some l →
      (toTrace ((Model.goldilocks (V := V)).initial S.C) π).st (2 * k' + ⌊π.stamp k'⌋₊) w = l.st := by
    intro k' w l hl
    rw [GoldilocksVariant.Final.toTrace_st, GoldilocksVariant.Final.origBefore_entry]
    exact GoldilocksVariant.Final.lastKnownSt_of_some _ π hl
  rcases hall i₀ B hl₀ hm₀ with hc | hc | hc
  · exact Or.inl hc
  · exact Or.inr (Or.inl hc)
  · right; right
    obtain ⟨he, hT, -⟩ := entry_of_honestThroughEntry π hlc hH
    obtain ⟨hanc, hnew⟩ := hc v _ hT (by rw [he]; exact hk) hAw
    rw [hstE k v lc hlc] at hanc hnew
    refine ⟨hanc, fun v' k' lc' hlc' hk' => ?_⟩
    have := hnew v' (2 * k' + ⌊π.stamp k'⌋₊)
      (by rw [GoldilocksVariant.Final.toTrace_time_entry]; exact hk')
    rwa [hstE k' v' lc' hlc'] at this

/-- **A tick on the trace at a clock value at most that of a tick the observed run's configuration `k`
comes after is at a trace step before the one that holds configuration `k`.** If `v` ticks on the
trace at the clock value `c` at the step `a`, and on the observed run at a clock value `c' ≥ c` at a
step `k' < k`, then `a < 2 k + ⌊π.stamp k⌋₊`.

Why: `a` is the trace step of a step `a₀` of the run (`exists_of_lbl_tick`). Were `a₀` after `k'`,
`v`'s clock would read `c' ≤ c` there (`toTrace_clock_mono`), so `c = c'`, and the two ticks at one
clock value would be one step (`toTrace_tick_unique`), a contradiction; so `a₀ ≤ k' < k`, and the
trace step of the run's step `a₀ < k` is before `2 k + ⌊π.stamp k⌋₊` (`π.stamp` is monotone).

The variables:
- `π`: the run; `hOne`: one tick per clock value; `a`, `c`: the trace tick; `k'`, `c'`: the observed
  tick; `k`: the configuration; `v`: the validator. -/
theorem trace_tick_lt_entry_of_tickAtG (hOne : RStsVariant2.TickOncePerReadingG π)
    {a k k' c c' : ℕ} {v : V}
    (ha : (toTrace ((Model.goldilocks (V := V)).initial S.C) π).lbl a =
      GoldilocksCorrectness.Statements.AbstractTrace.Event.tick v c)
    (hT : TickAtG (observeWithCommittees (Block := Block V) π) k' v c') (hk' : k' < k)
    (hc : c ≤ c') :
    a < 2 * k + ⌊π.stamp k⌋₊ := by
  have ha' := ha
  obtain ⟨a₀, rfl, hl₀, -⟩ := GoldilocksVariant.Final.exists_of_lbl_tick _ π ha
  have hadv₀ : v ∉ π[a₀].adv := ((π.step_at a₀).up_honest (Or.inl hl₀)).1
  have hle : a₀ ≤ k' := by
    by_contra hge
    have hlt : k' < a₀ := lt_of_not_ge hge
    have hmono := GoldilocksVariant.Final.toTrace_clock_mono _ π (newIdx π k') (newIdx π a₀) v c' c
      (GoldilocksVariant.Final.newIdx_strictMono π hlt)
      (by rw [GoldilocksVariant.Final.corrupted_activityOf_newIdx]; exact hadv₀)
      (Or.inl (toTrace_lbl_newIdx_of_tickAtG π hT)) (Or.inl ha')
    have hcc : c = c' := le_antisymm hc hmono
    subst hcc
    have heq := GoldilocksVariant.Final.toTrace_tick_unique _ π hOne _ _ v c
      (toTrace_lbl_newIdx_of_tickAtG π hT) ha'
    have := (GoldilocksVariant.Final.newIdx_strictMono π).injective heq
    omega
  have h1 := (GoldilocksVariant.Final.newIdx_strictMono π).monotone hle
  have h2 := Nat.floor_mono (π.stamp_mono (show k' + 1 ≤ k by omega))
  unfold newIdx at h1 ⊢
  omega

open Classical in
open GoldilocksCorrectness.Record.Statements.Executions (HonestOpenerAt RootCollisionAtProposal
  honestActiveAt) in
/-- **Statement 2's inclusion, read back from the trace at one reader** (`route-b`'s Lemma 90
conclusion `ConfirmedIncludedBetween`, read at the natural time `n`). For a slot `s` starting at or
after `tE`, with its update at most `n` and an honest opener, a block `B` slot `s`'s proposer sent at its
tick at the start of slot `s` on the observed run (`ProposedAtSlotStart`), and a validator `v` that is
an honest active validator of a slot `s' ≥ s` whose update is at most `n`, with a local state `lc`
known in the run's configuration `k` entered at a time at most `n`, honest in every configuration
entered by then, and that ticked, before configuration `k`, at a clock value at least the support
cutoff of slot `s' + 1`: either a root collision at the proposal, or `B` is the confirmed tip of `v`'s
view there or an ancestor of it.

Why: the proposal is the trace's (`proposalAt_of_proposedAtSlotStart`); configuration `k` is held by
the trace step `2 k + ⌊π.stamp k⌋₊` with `v` honest through it and its state `lc.st` after it
(`entry_of_honestThroughEntry`); `v`'s tick to the support cutoff of slot `s' + 1`, which it runs as an
honest active validator of slot `s'` (`honestActiveAt`, `lbl_tickStep_of_exists`), is before that
step (`trace_tick_lt_entry_of_tickAtG`); `confirmedIncludedBetween_unfold`.

The variables:
- `π`: the run; `hOne`: one tick per clock value; `tE`: the time from which the slots are read; `n`:
  the time the trace's conclusion is read at; `s`, `B`: the slot and its proposal; `s'`: the reader's
  slot; `v`, `k`, `lc`: the reader, its configuration and its local state; `k'`, `c'`: the reader's
  tick before configuration `k`. -/
theorem confirmedIncluded_of_trace (hOne : RStsVariant2.TickOncePerReadingG π)
    {tE n s s' k k' c' : ℕ} {B : Block V} {v : V}
    {lc : RStsVariant2.Local V (NamedObject V) (NodeState V)}
    (h : GoldilocksCorrectness.Record.Statements.Executions.ConfirmedIncludedBetween Model.goldilocks
      S (activityOf π) (toTrace ((Model.goldilocks (V := V)).initial S.C) π) tE n)
    (hs : tE ≤ (Model.goldilocks (V := V)).slotStart S.C s)
    (hcs : (Model.goldilocks (V := V)).supportCutoff S.C (s + 1) ≤ n)
    (hO : HonestOpenerAt Model.goldilocks S (activityOf π)
      (toTrace ((Model.goldilocks (V := V)).initial S.C) π) s)
    (hB : ProposedAtSlotStart S (observeWithCommittees (Block := Block V) π) s B)
    (hss' : s ≤ s')
    (hv : v ∈ honestActiveAt Model.goldilocks S (activityOf π)
      (toTrace ((Model.goldilocks (V := V)).initial S.C) π) s')
    (hcs' : (Model.goldilocks (V := V)).supportCutoff S.C (s' + 1) ≤ n)
    (hlc : π[k][v] = some lc) (hH : ∀ j : ℕ, π.stamp j ≤ π.stamp k → v ∉ π[j].adv)
    (hkn : π.stamp k ≤ n)
    (hT : TickAtG (observeWithCommittees (Block := Block V) π) k' v c') (hk' : k' < k)
    (hc' : (Model.goldilocks (V := V)).supportCutoff S.C (s' + 1) ≤ c') :
    RootCollisionAtProposal Model.goldilocks S (activityOf π)
        (toTrace ((Model.goldilocks (V := V)).initial S.C) π) s B ∨
      BlockVocab.anc B (NodeViewOf.view lc.st).C := by
  rw [GoldilocksCorrectness.Record.Proofs.View.confirmedIncludedBetween_unfold] at h
  obtain ⟨-, hall⟩ := h s hs hcs hO
  obtain ⟨i₀, hl₀, hm₀⟩ := proposalAt_of_proposedAtSlotStart π hB
  rcases hall i₀ B hl₀ hm₀ with hc | ⟨-, hc⟩
  · exact Or.inl hc
  · right
    obtain ⟨he, hTe, hst⟩ := entry_of_honestThroughEntry π hlc hH
    have hex : ∃ i : ℕ, (toTrace ((Model.goldilocks (V := V)).initial S.C) π).lbl i =
        GoldilocksCorrectness.Statements.AbstractTrace.Event.tick v
          ((Model.goldilocks (V := V)).supportCutoff S.C (s' + 1)) := by
      have hvA := hv
      unfold honestActiveAt GoldilocksCorrectness.Record.Statements.Executions.activeAt at hvA
      rw [Finset.mem_sdiff] at hvA
      have h1 := hvA.1
      simp only [Activity.awakeThroughoutToTick, Finset.mem_filter, Finset.mem_univ, true_and] at h1
      obtain ⟨k₁, hk₁, -⟩ := h1
      exact ⟨k₁, hk₁⟩
    have hts := trace_tick_lt_entry_of_tickAtG π hOne (lbl_tickStep_of_exists π hex) hT hk' hc'
    have key := hc v _ s' hTe hss' hv hts.le hcs' (by rw [he]; exact hkn)
    rw [hst] at key
    exact key

/-- **`route-b`'s finality reader at the trace step that holds a configuration before which the reader
ticked past its window.** A validator that ticks on the observed run at the clock value `c₀`, is up and
honest there throughout `[c₀, c₀ + L]`, `t ≤ c₀`, and that ticked before configuration `k` at a clock value `c'` at least
`c₀ + max (Δ S) Δs`, is awake for `max (Δ S) Δs` within `t` and the trace step `2 k + ⌊π.stamp k⌋₊`
that holds configuration `k`, when `L` is at least `max (Δ S) Δs + ΔClockBehind` and `ΔClockAhead` at
most `max (Δ S) Δs`.

Why: with `c₂ := c₀` and `c := c₀ + max (Δ S) Δs`, the tick at `c₀` is the trace's
(`toTrace_lbl_newIdx_of_tickAtG`); the validator ticks on the trace to `c` within the window
(`trace_tick_of_upAndHonest`), at a step before the one that holds configuration `k`
(`trace_tick_lt_entry_of_tickAtG`, from its tick at `c' ≥ c` before configuration `k`); it is active,
hence awake, at every trace step from the real time `c₀` up to that tick
(`activeThroughout_of_upAndHonest`).

The variables:
- `π`: the run; the clock bounds and conditions as in `awakeForDelayWithin_of_upAndHonest`; `hOne`:
  one tick per clock value; `k₀`, `c₀`: the tick that opens the window; `L`: the window's length;
  `t`: the time the reader starts at; `v`: the validator; `k`: the configuration; `k'`, `c'`: the
  tick before it. -/
theorem awakeForDelayWithin_of_tickedBefore {ΔClockAhead ΔClockBehind : ℝ}
    (hCA : 0 ≤ ΔClockAhead) (hCB : 0 ≤ ΔClockBehind)
    (hSkew : RStsVariant2.ClockWithinSkew ΔClockAhead ΔClockBehind π)
    (hAdv : RStsVariant2.ClockAdvancesWithin ΔClockAhead ΔClockBehind π)
    (hTicks : RStsVariant2.TicksWithin ΔClockBehind π) (hOne : RStsVariant2.TickOncePerReadingG π)
    {Δs k₀ c₀ k k' c' : ℕ} {L t : ℝ} {v : V}
    (hk : TickAtG (observeWithCommittees (Block := Block V) π) k₀ v c₀)
    (h : RStsVariant2.UpAndHonestThroughoutG (observeWithCommittees (Block := Block V) π) c₀
      (c₀ + L) v)
    (ht : t ≤ c₀)
    (hA : ΔClockAhead ≤ ((max (GoldilocksCorrectness.Statements.Routines.Δ S) Δs : ℕ) : ℝ))
    (hL : ((max (GoldilocksCorrectness.Statements.Routines.Δ S) Δs : ℕ) : ℝ) + ΔClockBehind ≤ L)
    (hT : TickAtG (observeWithCommittees (Block := Block V) π) k' v c') (hk' : k' < k)
    (hc' : c₀ + max (GoldilocksCorrectness.Statements.Routines.Δ S) Δs ≤ c') :
    GoldilocksCorrectness.Statements.AbstractTrace.View.AwakeForDelayWithin S (activityOf π)
      (toTrace ((Model.goldilocks (V := V)).initial S.C) π) Δs v t (2 * k + ⌊π.stamp k⌋₊) := by
  set x := toTrace ((Model.goldilocks (V := V)).initial S.C) π with hx
  set D := max (GoldilocksCorrectness.Statements.Routines.Δ S) Δs with hD
  have hAct := activeThroughout_of_upAndHonest π h
  simp only [Activity.activeThroughout, Finset.mem_filter, Finset.mem_univ, true_and] at hAct
  have tm : ∀ {a b : ℕ}, a ≤ b → x.time a ≤ x.time b := fun hab =>
    GoldilocksVariant.Final.toTrace_time_mono ((Model.goldilocks (V := V)).initial S.C) π hab
  obtain ⟨kc, hkc, -, hkc2⟩ := trace_tick_of_upAndHonest π hCA hCB hSkew hAdv hTicks
    (c := c₀ + D) h (by push_cast; linarith) (by push_cast; linarith)
  refine ⟨c₀, c₀ + D, c₀, kc, newIdx π k₀, ht, le_rfl, hkc,
    (trace_tick_lt_entry_of_tickAtG π hOne hkc hT hk' hc').le, ?_,
    toTrace_lbl_newIdx_of_tickAtG π hk, ht, ?_⟩
  · intro i hi hik
    have h1 := hAct i ((tm hik).trans (hkc2.trans (by push_cast; linarith)))
      (by have := tm (Nat.le_succ i)
          linarith)
    exact (Finset.mem_sdiff.1 h1).1
  · exact Nat.add_le_add_left (le_max_left _ _) _

/-- **`route-b`'s finality reader from statement 3's reader `UpAndHonestForFrom`.** A validator `v`
that, from the clock value `c₀` of one of its ticks at or after `tFrom`, is up and honest for `ΔUp`
on the observed run and has ticked at a clock value at least `c₀ + ΔUp` before configuration `k`
(`UpAndHonestForFrom`), is awake for `max (Δ S) Δs` within every `t ≤ tFrom` and the trace step
`2 k + ⌊π.stamp k⌋₊` that holds configuration `k`, when `ΔUp` is at least
`max (Δ S) Δs + ΔClockBehind` and `ΔClockAhead` at most `max (Δ S) Δs`.

Why: the tick before configuration `k` is at a clock value at least `c₀ + ΔUp`, so at least
`c₀ + max (Δ S) Δs` since `ΔClockBehind` is not negative; `awakeForDelayWithin_of_tickedBefore`.

The variables:
- `π`: the run; the clock bounds and conditions as in `awakeForDelayWithin_of_tickedBefore`; `tFrom`:
  the time the window may start at; `ΔUp`: the window's length; `t`: the time the reader starts at;
  `v`: the validator; `k`: the configuration. -/
theorem awakeForDelayWithin_of_upAndHonestForFrom {ΔClockAhead ΔClockBehind : ℝ}
    (hCA : 0 ≤ ΔClockAhead) (hCB : 0 ≤ ΔClockBehind)
    (hSkew : RStsVariant2.ClockWithinSkew ΔClockAhead ΔClockBehind π)
    (hAdv : RStsVariant2.ClockAdvancesWithin ΔClockAhead ΔClockBehind π)
    (hTicks : RStsVariant2.TicksWithin ΔClockBehind π) (hOne : RStsVariant2.TickOncePerReadingG π)
    {Δs k : ℕ} {tFrom ΔUp t : ℝ} {v : V}
    (hU : UpAndHonestForFrom (observeWithCommittees (Block := Block V) π) tFrom ΔUp k v)
    (ht : t ≤ tFrom)
    (hA : ΔClockAhead ≤ ((max (GoldilocksCorrectness.Statements.Routines.Δ S) Δs : ℕ) : ℝ))
    (hL : ((max (GoldilocksCorrectness.Statements.Routines.Δ S) Δs : ℕ) : ℝ) + ΔClockBehind ≤ ΔUp) :
    GoldilocksCorrectness.Statements.AbstractTrace.View.AwakeForDelayWithin S (activityOf π)
      (toTrace ((Model.goldilocks (V := V)).initial S.C) π) Δs v t (2 * k + ⌊π.stamp k⌋₊) := by
  obtain ⟨k₀, c₀, hk, hc₀, h, k', c', hk', hc', hT⟩ := hU
  refine awakeForDelayWithin_of_tickedBefore π hCA hCB hSkew hAdv hTicks hOne hk h
    (ht.trans hc₀) hA hL hT hk' ?_
  have : ((c₀ + max (GoldilocksCorrectness.Statements.Routines.Δ S) Δs : ℕ) : ℝ) ≤ (c' : ℝ) := by
    push_cast at hL ⊢
    linarith
  exact_mod_cast this

omit [ProtocolCommittees (goldilocksProtocol S) (Block V)] in
/-- A validator outside the corrupted set of the run's configuration `k` is outside the trace's
adversary set at every trace step up to `2 k + ⌊π.stamp k⌋₊`, the one that holds configuration `k`.

Why: the adversary set after trace step `i` is the corrupted set of the run's configuration
`origBefore π i`, at most `k` for `i` at most `2 k + ⌊π.stamp k⌋₊` (`origBefore_mono`,
`origBefore_entry`), and corruption is permanent (`adv_mono`).

The variables:
- `π`: the run; `k`: the configuration; `w`: the validator. -/
theorem honestThrough_entry {k : ℕ} {w : V} (hw : w ∉ π[k].adv) :
    (toTrace ((Model.goldilocks (V := V)).initial S.C) π).HonestThrough (activityOf π)
      (2 * k + ⌊π.stamp k⌋₊) w := by
  intro i' hi'
  rw [GoldilocksVariant.Final.corrupted_activityOf]
  have hle := GoldilocksVariant.Final.origBefore_mono π hi'
  rw [GoldilocksVariant.Final.origBefore_entry] at hle
  exact fun hc => hw (π.adv_mono hle hc)

omit [ProtocolCommittees (goldilocksProtocol S) (Block V)] in
/-- **Statement 4's persistence, read back from the trace at one reader** (`route-b`'s
`ConfirmedPersistsBetween`, read at the natural time `n`). With `route-b`'s premise on the protected
block `P` passed through (a validator `v` honest through a step `T` in `[tA, cutoff (s + 1)]`, past
every tick it runs at a clock value at most the time of `T`, whose confirmed tip there has `P` as an
ancestor or is `P`), an updater `w` of slot `s` with a local state `lc` known in the run's
configuration `k`, honest there, entered within `[b₀, n]` and after `ΔClockBehind` past the support
cutoff of slot `s + 1`, has `P` as its confirmed tip there or an ancestor of it.

Why: configuration `k` is held by the trace step `2 k + ⌊π.stamp k⌋₊` at the real time `π.stamp k`
(`toTrace_time_entry`) with `w` honest through it (`honestThrough_entry`) and its state `lc.st`
(`toTrace_st`, `origBefore_entry`); `w`'s tick to that cutoff, which it runs as an updater, is at a
real time at most the cutoff plus `ΔClockBehind` (`time_tickStep_le`), so at an earlier trace step;
`confirmedPersistsBetween_unfold`.

The variables:
- `π`: the run; `hActs`: the clock condition on acting; `s`: the slot; `tA`, `b₀`, `n`: the trace
  conclusion's times; `v`, `T`, `P`: the protected block's premise; `w`, `k`, `lc`: the reader, its
  configuration and its local state. -/
theorem confirmedPersists_of_trace {ΔClockBehind : ℝ}
    (hActs : RStsVariant2.ActsWithinSkewG ΔClockBehind π) {s tA b₀ n T k : ℕ} {v w : V}
    {P : Block V} {lc : RStsVariant2.Local V (NamedObject V) (NodeState V)}
    (h : GoldilocksCorrectness.Record.Statements.Executions.ConfirmedPersistsBetween Model.goldilocks
      S (activityOf π) (toTrace ((Model.goldilocks (V := V)).initial S.C) π) s tA b₀ n)
    (hTv : (activityOf π).HonestThroughTime (toTrace ((Model.goldilocks (V := V)).initial S.C) π)
      ((toTrace ((Model.goldilocks (V := V)).initial S.C) π).time T) v)
    (hTA : (tA : ℝ) ≤ (toTrace ((Model.goldilocks (V := V)).initial S.C) π).time T)
    (hTc : (toTrace ((Model.goldilocks (V := V)).initial S.C) π).time T ≤
      ((Model.goldilocks (V := V)).supportCutoff S.C (s + 1) : ℝ))
    (hTk : ∀ t : ℕ, (t : ℝ) ≤ (toTrace ((Model.goldilocks (V := V)).initial S.C) π).time T →
      ∀ T' : ℕ, T ≤ T' → (toTrace ((Model.goldilocks (V := V)).initial S.C) π).lbl T' ≠
        GoldilocksCorrectness.Statements.AbstractTrace.Event.tick v t)
    (hP : P.AncestorEq ((Model.goldilocks (V := V)).ac_confirmed
      ((toTrace ((Model.goldilocks (V := V)).initial S.C) π).st T v)))
    (hwU : w ∈ GoldilocksCorrectness.Record.Statements.AbstractTrace.updaterAt Model.goldilocks S
      (activityOf π) (toTrace ((Model.goldilocks (V := V)).initial S.C) π) s)
    (hlc : π[k][w] = some lc) (hw : w ∉ π[k].adv) (hb : (b₀ : ℝ) ≤ π.stamp k)
    (hkn : π.stamp k ≤ n)
    (hcut : ((Model.goldilocks (V := V)).supportCutoff S.C (s + 1) : ℝ) + ΔClockBehind < π.stamp k) :
    BlockVocab.anc P (NodeViewOf.view lc.st).C := by
  rw [GoldilocksCorrectness.Record.Proofs.View.confirmedPersistsBetween_unfold] at h
  have he := GoldilocksVariant.Final.toTrace_time_entry ((Model.goldilocks (V := V)).initial S.C) π k
  have hst : (toTrace ((Model.goldilocks (V := V)).initial S.C) π).st (2 * k + ⌊π.stamp k⌋₊) w =
      lc.st := by
    rw [GoldilocksVariant.Final.toTrace_st, GoldilocksVariant.Final.origBefore_entry]
    exact GoldilocksVariant.Final.lastKnownSt_of_some _ π hlc
  have hex : ∃ i : ℕ, (toTrace ((Model.goldilocks (V := V)).initial S.C) π).lbl i =
      GoldilocksCorrectness.Statements.AbstractTrace.Event.tick w
        ((Model.goldilocks (V := V)).supportCutoff S.C (s + 1)) := by
    have hA := hwU
    unfold GoldilocksCorrectness.Record.Statements.AbstractTrace.updaterAt at hA
    simp only [Activity.activeThroughoutToTick, Finset.mem_filter, Finset.mem_univ, true_and] at hA
    obtain ⟨k', hk', -⟩ := hA
    exact ⟨k', hk'⟩
  have hts : (toTrace ((Model.goldilocks (V := V)).initial S.C) π).tickStep w
      ((Model.goldilocks (V := V)).supportCutoff S.C (s + 1)) < 2 * k + ⌊π.stamp k⌋₊ := by
    by_contra hge
    have hm := GoldilocksVariant.Final.toTrace_time_mono ((Model.goldilocks (V := V)).initial S.C) π
      (le_of_not_gt hge)
    have := time_tickStep_le π hActs hex
    rw [he] at hm
    linarith
  have key := h v T P hTv hTA hTc hTk hP w _ (honestThrough_entry π hw) hwU hts
    (by rw [he]; exact hb) (by rw [he]; exact hkn)
  rw [hst] at key
  exact key

omit [ProtocolCommittees (goldilocksProtocol S) (Block V)] in
/-- **Statement 4's compatibility of the finalized blocks, read back from the trace at one reader**
(`route-b`'s `FinalizedCompatibleBetween`, read at the natural time `n`). With `route-b`'s premise on
the protected block `P` passed through, as in `confirmedPersists_of_trace`, every validator `w` with a
local state `lc` known in the run's configuration `k`, honest there and entered within `[b₀, n]`, has
a finalized block compatible with `P`.

Why: configuration `k` is held by the trace step `2 k + ⌊π.stamp k⌋₊` at the real time `π.stamp k`
with `w` honest through it (`honestThrough_entry`) and its state `lc.st`;
`finalizedCompatibleBetween_unfold`.

The variables:
- `π`: the run; `s`: the slot; `tA`, `b₀`, `n`: the trace conclusion's times; `v`, `T`, `P`: the
  protected block's premise; `w`, `k`, `lc`: the reader, its configuration and its local state. -/
theorem finalizedCompatible_of_trace {s tA b₀ n T k : ℕ} {v w : V}
    {P : Block V} {lc : RStsVariant2.Local V (NamedObject V) (NodeState V)}
    (h : GoldilocksCorrectness.Record.Statements.Executions.FinalizedCompatibleBetween
      Model.goldilocks S (activityOf π) (toTrace ((Model.goldilocks (V := V)).initial S.C) π) s tA
      b₀ n)
    (hTv : (activityOf π).HonestThroughTime (toTrace ((Model.goldilocks (V := V)).initial S.C) π)
      ((toTrace ((Model.goldilocks (V := V)).initial S.C) π).time T) v)
    (hTA : (tA : ℝ) ≤ (toTrace ((Model.goldilocks (V := V)).initial S.C) π).time T)
    (hTc : (toTrace ((Model.goldilocks (V := V)).initial S.C) π).time T ≤
      ((Model.goldilocks (V := V)).supportCutoff S.C (s + 1) : ℝ))
    (hTk : ∀ t : ℕ, (t : ℝ) ≤ (toTrace ((Model.goldilocks (V := V)).initial S.C) π).time T →
      ∀ T' : ℕ, T ≤ T' → (toTrace ((Model.goldilocks (V := V)).initial S.C) π).lbl T' ≠
        GoldilocksCorrectness.Statements.AbstractTrace.Event.tick v t)
    (hP : P.AncestorEq ((Model.goldilocks (V := V)).ac_confirmed
      ((toTrace ((Model.goldilocks (V := V)).initial S.C) π).st T v)))
    (hlc : π[k][w] = some lc) (hw : w ∉ π[k].adv) (hb : (b₀ : ℝ) ≤ π.stamp k)
    (hkn : π.stamp k ≤ n) :
    BlockVocab.Compatible P (NodeViewOf.view lc.st).F := by
  rw [GoldilocksCorrectness.Record.Proofs.View.finalizedCompatibleBetween_unfold] at h
  have he := GoldilocksVariant.Final.toTrace_time_entry ((Model.goldilocks (V := V)).initial S.C) π k
  have hst : (toTrace ((Model.goldilocks (V := V)).initial S.C) π).st (2 * k + ⌊π.stamp k⌋₊) w =
      lc.st := by
    rw [GoldilocksVariant.Final.toTrace_st, GoldilocksVariant.Final.origBefore_entry]
    exact GoldilocksVariant.Final.lastKnownSt_of_some _ π hlc
  have key := h v T P hTv hTA hTc hTk hP w _ (honestThrough_entry π hw)
    (by rw [he]; exact hb) (by rw [he]; exact hkn)
  rw [hst] at key
  exact key

/-! ### The windows read from Goldilocks's premises: the proposer's window, the finality segment's
ends, the start of the updaters' window -/

/-- **The proposer's window of a proposer requirement**: when `p` is Goldilocks's requirement of slot
`s` for the block `B` and its proposer is up and honest from `p.tProposalStart` through `p.tPreAsync`
(`HonestProposerThroughG`, the antecedent statements 2 to 4 take for every requirement), slot `s`'s
proposer is up and honest on the observed run from `ΔClockAhead` before slot `s`'s proposal window
start to `ΔClockBehind` after the support cutoff of slot `s + 1`.

Why: those are `p.tProposalStart` and `p.tPreAsync` (`goldilocksProposerReq`).

The variables:
- `π`: the run; `ΔClockAhead`, `ΔClockBehind`: the clock bounds; `tA`: the end of the healing phase;
  `p`: the requirement; `s`, `B`: its slot and block, `hp`; `h`: the proposer's window. -/
theorem upAndHonest_of_honestProposerThrough {ΔClockAhead ΔClockBehind tA : ℝ}
    {p : ProposerRequirement V (Block V)} {s : ℕ} {B : Block V}
    (hp : p = goldilocksProposerReq S ΔClockAhead ΔClockBehind s B)
    (h : RStsVariant2.HonestProposerThroughG tA p.tPreAsync p.tProposalStart p.proposer
      (observeWithCommittees (Block := Block V) π)) :
    RStsVariant2.UpAndHonestThroughoutG (observeWithCommittees (Block := Block V) π)
      (((proposal_window_start S.C s : Time) : ℝ) - ΔClockAhead)
      (((S.C.t_ (s + 1) + 2 * S.C.Δ : Time) : ℝ) + ΔClockBehind) (S.P.proposer s) := by
  subst hp
  exact h.2.2

open Classical in
/-- **`hp` of `confirmedPersists_asyncPeriod_until`, from statement 4's antecedent**: for Goldilocks's
requirement `p` of the hand-over slot `s`, whose proposer is up and honest from `p.tProposalStart`
through `p.tPreAsync`, the conclusion of `hp_toTrace` at `s`.

Why: `upAndHonest_of_honestProposerThrough`, `hp_toTrace`.

The variables:
- `π`: the run; `ΔClockAhead`, `ΔClockBehind`: the clock bounds; `hSkew`, `hAdv`, `hTicks`, `hActs`:
  the clock conditions; `tA`: the end of the healing phase; `p`, `s`, `B`, `hp`: the requirement, its
  slot and block; `h`: the proposer's window. -/
theorem hp_of_honestProposerThrough {ΔClockAhead ΔClockBehind tA : ℝ}
    (hCA : 0 ≤ ΔClockAhead) (hCB : 0 ≤ ΔClockBehind)
    (hΔ : ΔClockAhead + ΔClockBehind < ((S.C.Δ : Time) : ℝ))
    (hSkew : RStsVariant2.ClockWithinSkew ΔClockAhead ΔClockBehind π)
    (hAdv : RStsVariant2.ClockAdvancesWithin ΔClockAhead ΔClockBehind π)
    (hTicks : RStsVariant2.TicksWithin ΔClockBehind π)
    (hActs : RStsVariant2.ActsWithinSkewG ΔClockBehind π)
    {p : ProposerRequirement V (Block V)} {s : ℕ} {B : Block V}
    (hp : p = goldilocksProposerReq S ΔClockAhead ΔClockBehind s B)
    (h : RStsVariant2.HonestProposerThroughG tA p.tPreAsync p.tProposalStart p.proposer
      (observeWithCommittees (Block := Block V) π)) :
    S.P.proposer s ∈ (activityOf π).activeThroughoutToTick
        (toTrace ((Model.goldilocks (V := V)).initial S.C) π) (proposal_window_start S.C s)
        ((Model.goldilocks (V := V)).supportCutoff S.C (s + 1)) ∧
      S.P.proposer s ∉ (activityOf π).corruptedAtTime
          (toTrace ((Model.goldilocks (V := V)).initial S.C) π)
          ((Model.goldilocks (V := V)).supportCutoff S.C (s + 1)) ∪
        Finset.univ.filter (fun u => ∃ (k : ℕ) (w : V),
          (toTrace ((Model.goldilocks (V := V)).initial S.C) π).lbl k =
            GoldilocksCorrectness.Statements.AbstractTrace.Event.tick w
              ((Model.goldilocks (V := V)).supportCutoff S.C (s + 1)) ∧
          w ∉ (activityOf π).corrupted k ∧ u ∈ (activityOf π).corrupted k) :=
  hp_toTrace π hCA hCB hΔ hSkew hAdv hTicks hActs (upAndHonest_of_honestProposerThrough π hp h)

/-- **The honest opener of a requirement's slot, from statements 2 to 4's antecedent**: for
Goldilocks's requirement `p` of slot `s`, whose proposer is up and honest from `p.tProposalStart`
through `p.tPreAsync`, slot `s` has an honest opener on the trace (`HonestOpenerAt`), the antecedent
of `route-b`'s inclusion of an honest proposal.

Why: `upAndHonest_of_honestProposerThrough`, `honestOpenerAt_of_upAndHonest`.

The variables:
- `π`: the run; `ΔClockAhead`, `ΔClockBehind`: the clock bounds; `hSkew`, `hAdv`, `hTicks`, `hActs`:
  the clock conditions; `tA`: the end of the healing phase; `p`, `s`, `B`, `hp`: the requirement, its
  slot and block; `h`: the proposer's window. -/
theorem honestOpenerAt_of_honestProposerThrough {ΔClockAhead ΔClockBehind tA : ℝ}
    (hCA : 0 ≤ ΔClockAhead) (hCB : 0 ≤ ΔClockBehind)
    (hΔ : ΔClockAhead + ΔClockBehind < ((S.C.Δ : Time) : ℝ))
    (hSkew : RStsVariant2.ClockWithinSkew ΔClockAhead ΔClockBehind π)
    (hAdv : RStsVariant2.ClockAdvancesWithin ΔClockAhead ΔClockBehind π)
    (hTicks : RStsVariant2.TicksWithin ΔClockBehind π)
    (hActs : RStsVariant2.ActsWithinSkewG ΔClockBehind π)
    {p : ProposerRequirement V (Block V)} {s : ℕ} {B : Block V}
    (hp : p = goldilocksProposerReq S ΔClockAhead ΔClockBehind s B)
    (h : RStsVariant2.HonestProposerThroughG tA p.tPreAsync p.tProposalStart p.proposer
      (observeWithCommittees (Block := Block V) π)) :
    HonestOpenerAt Model.goldilocks S (activityOf π)
      (toTrace ((Model.goldilocks (V := V)).initial S.C) π) s :=
  honestOpenerAt_of_upAndHonest π hCA hCB hΔ hSkew hAdv hTicks hActs
    (upAndHonest_of_honestProposerThrough π hp h)

/-- **The finality window, from statement 3's finality premise**: Goldilocks's finality premise for
the requirement `p` on the window `[tS, tE]` (`goldilocksFinalityConditions`, read on the segment of
the observed run inside the window) gives a slot `s`, a block `B` and a round `r` with `p` slot `s`'s
requirement for `B`, `s ≤ r * R`, and `route-b`'s `FinalityWindowAt` at `r`.

Why: the premise's window ends are those `finalityWindowAt_of_on` asks.

The variables:
- `π`: the run; `ΔClockAhead`, `ΔClockBehind`: the clock bounds; `hSkew`, `hAdv`, `hTicks`, `hActs`:
  the clock conditions; `p`: the requirement; `tS`, `tE`: the window; `h`: the finality premise. -/
theorem finalityWindowAt_of_conditions {ΔClockAhead ΔClockBehind tS tE : ℝ}
    (hCA : 0 ≤ ΔClockAhead) (hCB : 0 ≤ ΔClockBehind)
    (hΔ : ΔClockAhead + ΔClockBehind < ((S.C.Δ : Time) : ℝ))
    (hSkew : RStsVariant2.ClockWithinSkew ΔClockAhead ΔClockBehind π)
    (hAdv : RStsVariant2.ClockAdvancesWithin ΔClockAhead ΔClockBehind π)
    (hTicks : RStsVariant2.TicksWithin ΔClockBehind π)
    (hActs : RStsVariant2.ActsWithinSkewG ΔClockBehind π)
    {p : ProposerRequirement V (Block V)}
    (h : goldilocksFinalityConditions S ΔClockAhead ΔClockBehind p tS tE
      (phaseSegment (observeWithCommittees (Block := Block V) π) tS tE)) :
    ∃ (s r : ℕ) (B : Block V), p = goldilocksProposerReq S ΔClockAhead ΔClockBehind s B ∧
      s ≤ r * S.C.R ∧
      FinalityWindowAt Model.goldilocks S (activityOf π)
        (toTrace ((Model.goldilocks (V := V)).initial S.C) π) r := by
  obtain ⟨s, r, B, hp, hsr, hS, hE, hO, hQ⟩ := h
  exact ⟨s, r, B, hp, hsr,
    finalityWindowAt_of_on π hCA hCB hΔ hSkew hAdv hTicks hActs hO hQ hS hE⟩

omit [ProtocolCommittees (goldilocksProtocol S) (Block V)] [RootOrder] in
/-- **The start of the updaters' window, from statement 4's healing premise**: Goldilocks's healing
premise fixes `ΔPreAsync` so that, for Goldilocks's requirement of any slot `s`, `p.tPreAsync −
ΔPreAsync` is `ΔClockAhead` before the start of slot `s + 1`'s duty window (`hPreStart` of
`hHoldOutweigh_toTrace`).

Why: `p.tPreAsync` is the support cutoff of slot `s + 1` plus `ΔClockBehind`, and `ΔPreAsync` that
time less `duty_window_start S.C (s + 1) − ΔClockAhead`.

The variables:
- `S`: the setup; the delays and times of `goldilocksHealingConditions`; `segment`: the healing
  phase's segment; `h`: the healing premise; `s`, `B`: the slot and the block of the requirement. -/
theorem preStart_of_healingConditions {Δs Δs_F ΔNet ΔNet_F ΔRedeliver : ℕ}
    {ΔClockAhead ΔClockBehind ΔPreAsync tGAT tAwakeEnd : ℝ}
    {segment : (i : ℕ) → Option (PhaseStep V (NamedObject V) (Block V))}
    (h : goldilocksHealingConditions S Δs Δs_F ΔNet ΔNet_F ΔRedeliver ΔClockAhead ΔClockBehind
      ΔPreAsync tGAT tAwakeEnd segment) (s : ℕ) (B : Block V) :
    (goldilocksProposerReq S ΔClockAhead ΔClockBehind s B).tPreAsync - ΔPreAsync ≤
      ((duty_window_start S.C (s + 1) : Time) : ℝ) - ΔClockAhead := by
  have h1 := h.2.1 s
  show ((S.C.t_ (s + 1) + 2 * S.C.Δ : Time) : ℝ) + ΔClockBehind - ΔPreAsync ≤ _
  rw [h1]
  linarith

open Classical in
/-- **Statement 4's `hHold`, from statement 4's premises**: `hHoldOutweigh_toTrace` for Goldilocks's
requirement `p` of the hand-over slot `s`, with the hand-over update `p.tPreAsync` and the start of
the updaters' window read from `p` and from Goldilocks's healing premise.

Why: `p.tPreAsync` is `goldilocksProposerReq`'s; `preStart_of_healingConditions`.

The variables: as for `hHoldOutweigh_toTrace`, with `p`, `B`, `hp`: the requirement of slot `s` for
`B`; `hH`: the healing premise on a segment `segment`; `hW`: `p`'s proposer up and honest through
`[p.tProposalStart, p.tPreAsync]`; `hSl`: the sleepiness condition at `p.tPreAsync`. -/
theorem hHoldOutweigh_of_conditions {Δs Δs_F ΔNet ΔNet_F ΔRedeliver : ℕ}
    {ΔClockAhead ΔClockBehind tA tGAT ΔPreAsync tAS tAE ΔRecovery : ℝ}
    {segment : (i : ℕ) → Option (PhaseStep V (NamedObject V) (Block V))}
    (hCA : 0 ≤ ΔClockAhead) (hCB : 0 ≤ ΔClockBehind)
    (hΔ : ΔClockAhead + ΔClockBehind < ((S.C.Δ : Time) : ℝ))
    (hSkew : RStsVariant2.ClockWithinSkew ΔClockAhead ΔClockBehind π)
    (hAdv : RStsVariant2.ClockAdvancesWithin ΔClockAhead ΔClockBehind π)
    (hTicks : RStsVariant2.TicksWithin ΔClockBehind π)
    (hActs : RStsVariant2.ActsWithinSkewG ΔClockBehind π)
    (hcom : ∀ ci : ℕ, RStsVariant2.ObservableWithCommittees.committees
      (observeWithCommittees (Block := Block V) π) ci =
        goldilocksCommitteeSpecs S ΔClockAhead ΔClockBehind ci)
    (hH : goldilocksHealingConditions S Δs Δs_F ΔNet ΔNet_F ΔRedeliver ΔClockAhead ΔClockBehind
      ΔPreAsync tGAT tA segment)
    {p : ProposerRequirement V (Block V)} {s : ℕ} {B : Block V}
    (hp : p = goldilocksProposerReq S ΔClockAhead ΔClockBehind s B)
    (hSl : RStsVariant2.AsyncPeriodSleepinessG p.tPreAsync ΔPreAsync tAS tAE ΔRecovery
      (observeWithCommittees (Block := Block V) π))
    (hW : RStsVariant2.HonestProposerThroughG tA p.tPreAsync p.tProposalStart p.proposer
      (observeWithCommittees (Block := Block V) π))
    {b₀ b₁ : ℕ} (hb₀ : ∀ n : ℕ, b₀ < n → tAS < (n : ℝ))
    (hb₁ : ∀ n : ℕ, n + GoldilocksCorrectness.Statements.Routines.Δ S <
      b₁ + max (GoldilocksCorrectness.Statements.Routines.Δ S) Δs → (n : ℝ) < tAE + ΔRecovery)
    (hEnd : b₁ + max (GoldilocksCorrectness.Statements.Routines.Δ S) Δs ≤
      (Model.goldilocks (V := V)).voteTime S.C (s + S.C.k)) :
    GoldilocksCorrectness.Record.Statements.Executions.HoldersOutweighWhereOwed Model.goldilocks S
      (activityOf π) (toTrace ((Model.goldilocks (V := V)).initial S.C) π) s Δs b₀ b₁ := by
  subst hp
  exact hHoldOutweigh_toTrace π hCA hCB hΔ hSkew hAdv hTicks hActs hcom hSl hW rfl
    (preStart_of_healingConditions hH s B) hb₀ hb₁ hEnd

end Windows

end LARuns.GoldilocksInstance
