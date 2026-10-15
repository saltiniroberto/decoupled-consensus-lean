import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Conditions.ClaimAsyncK_GstShift
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Sts_Spec2Claims_ClaimStableThroughAsyncPeriod
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.ClaimAsyncK_GstShift

/-!
# Moving an execution to a setup with another GST

Theorems over a model `M : Record.Model V` with facts `facts : Record.Facts M`: the protocol does
not read the GST, so an execution moves to the setup `setupWithGST S g hg`, and each execution
premise moves with it.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

/-- The set of a validator's reactions to every event is the same at `S` and at
    `setupWithGST S g hg`. -/
theorem reaction_setupWithGST (facts : Record.Facts M) (S : Setup V) (g : Int) (hg : 0 ≤ g) :
    Record.reactionsOf M (setupWithGST S g hg) = Record.reactionsOf M S := by
  funext p n t e
  cases e with
  | tick =>
    simp only [Record.reactionsOf]
    rw [alwaysAwake_setupWithGST, facts.nd.namedNodeTick_setupWithGST]
    rfl
  | recv m =>
    simp only [Record.reactionsOf]
    rw [alwaysAwake_setupWithGST, facts.nd.namedNodeProcess_setupWithGST]
  | wake => rfl
  | custom ev => exact ev.elim

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

/-- The protocol built from a setup does not change when the setup's GST is replaced. -/
theorem protocol_setupWithGST (facts : Record.Facts M) (S : Setup V) (g : Int) (hg : 0 ≤ g) :
    Record.protocolOf M (setupWithGST S g hg) = Record.protocolOf M S := by
  have h := Restated.reaction_setupWithGST facts S g hg
  unfold Record.protocolOf
  simp only [h, alwaysAwake_setupWithGST, facts.nd.initial_setupWithGST]

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

/-- Unforgeability moves to the setup with GST `g`. -/
theorem tr_Unforgeability (facts : Record.Facts M) (S : Setup V) (g : Int) (hg : 0 ≤ g) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (h : Restated.Unforgeability M S x) :
    Restated.Unforgeability M (setupWithGST S g hg) (Restated.toGST M S g hg (Restated.protocol_setupWithGST facts S g hg) x) :=
  ⟨h.unforgeable, h.carried⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

/-- Well-formed delivery moves to the setup with GST `g`. -/
theorem tr_DeliveryWellFormed (facts : Record.Facts M) (S : Setup V) (g : Int) (hg : 0 ≤ g) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (h : Restated.DeliveryWellFormed M S x) :
    Restated.DeliveryWellFormed M (setupWithGST S g hg) (Restated.toGST M S g hg (Restated.protocol_setupWithGST facts S g hg) x) :=
  ⟨fun j w sm hl => by
      have hc : ∀ s, (setupWithGST S g hg).E.committee s = S.E.committee s :=
        fun s => committee_eq_of_committees_eq (E := (setupWithGST S g hg).E) (E' := S.E) rfl s
      simp only [hc]
      exact h.wire j w sm hl, h.deps⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

/-- Root collision freedom moves to the setup with GST `g`. -/
theorem tr_RootCollisionFree (facts : Record.Facts M) (S : Setup V) (g : Int) (hg : 0 ≤ g) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (h : Restated.RootCollisionFreeInLog M S Sched x) :
    Restated.RootCollisionFreeInLog M (setupWithGST S g hg) Sched (Restated.toGST M S g hg (Restated.protocol_setupWithGST facts S g hg) x) :=
  ⟨h.root_injective⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

/-- A valid execution stays valid at the setup with GST `g`. -/
theorem tr_ExecutionValid (facts : Record.Facts M) (S : Setup V) (g : Int) (hg : 0 ≤ g) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (h : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) :
    Restated.ExecutionValid M (setupWithGST S g hg) Sched (Restated.interface M (setupWithGST S g hg) Sched)
      (Restated.toGST M S g hg (Restated.protocol_setupWithGST facts S g hg) x) :=
  { toUnforgeability := Restated.tr_Unforgeability facts S g hg Sched x h.toUnforgeability
    toDeliveryWellFormed := Restated.tr_DeliveryWellFormed facts S g hg Sched x h.toDeliveryWellFormed
    idealization := Restated.tr_RootCollisionFree facts S g hg Sched x h.idealization
    honestRootsNew := by
      intro k τ s hl hτ hhon B hB
      exact h.honestRootsNew k τ s hl
        (hτ.trans (facts.sch.proposal_time_eq_of_delta_eq (E := (setupWithGST S g hg).E)
          (E' := S.E) rfl s))
        hhon B hB }

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

/-- `CommonViewOfFinalizedDescendantsAt` at `t` moves to the setup with GST `g`. -/
theorem tr_CommonViewOfFinalizedDescendantsAt (facts : Record.Facts M) (S : Setup V) (g : Int) (hg : 0 ≤ g) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (t : Int)
    (h : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x t) :
    Restated.CommonViewOfFinalizedDescendantsAt M (setupWithGST S g hg) Sched (Restated.toGST M S g hg (Restated.protocol_setupWithGST facts S g hg) x) t := h

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

/-- Diverging time moves to the setup with GST `g`. -/
theorem tr_TimeDiverges (facts : Record.Facts M) (S : Setup V) (g : Int) (hg : 0 ≤ g) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (h : Restated.TimeDiverges M x) : Restated.TimeDiverges M (Restated.toGST M S g hg (Restated.protocol_setupWithGST facts S g hg) x) := h

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

/-- Honest committees move to the setup with GST `g`. -/
theorem tr_HonestCommittees (facts : Record.Facts M) (S : Setup V) (g : Int) (hg : 0 ≤ g) (Sched : Schedule V) (h : Restated.HonestCommittees M S Sched (Restated.interface M S Sched)) :
    Restated.HonestCommittees M (setupWithGST S g hg) Sched (Restated.interface M (setupWithGST S g hg) Sched) := by
  have hcm : ∀ s : Slot, (Restated.interface M (setupWithGST S g hg) Sched).committee s
      = (Restated.interface M S Sched).committee s := fun s => committee_eq_of_committees_eq (E := (setupWithGST S g hg).E) (E' := S.E) rfl s
  have hct : ∀ s : Slot, M.confirmation_time (setupWithGST S g hg).E s
      = M.confirmation_time S.E s := fun s => facts.sch.confirmation_time_eq_of_delta_eq (E := (setupWithGST S g hg).E) (E' := S.E) rfl s
  unfold Restated.HonestCommittees at h ⊢
  simp only [hcm, hct]
  exact h

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

/-- The three sleepiness premises at `t` move to the setup with GST `g`. -/
theorem tr_sleepiness (facts : Record.Facts M) (S : Setup V) (g : Int) (hg : 0 ≤ g) (Sched : Schedule V) (t : Int)
    (h : sleepinessW S Sched t ∧ Restated.roundSleepinessW M S Sched t ∧ Restated.committeeSleepinessW M S Sched t) :
    sleepinessW (setupWithGST S g hg) Sched t ∧ Restated.roundSleepinessW M (setupWithGST S g hg) Sched t ∧
      Restated.committeeSleepinessW M (setupWithGST S g hg) Sched t := by
  have hop : ∀ r : Round, M.opening (setupWithGST S g hg).E (setupWithGST S g hg).hc r
      = M.opening S.E S.hc r := fun r => facts.gr.opening_eq_of_delta_eq (E := (setupWithGST S g hg).E) (E' := S.E) rfl _ r
  have hcm : ∀ s : Slot, (setupWithGST S g hg).E.committee s = S.E.committee s :=
    fun s => committee_eq_of_committees_eq (E := (setupWithGST S g hg).E) (E' := S.E) rfl s
  have hct : ∀ s : Slot, M.confirmation_time (setupWithGST S g hg).E s
      = M.confirmation_time S.E s := fun s => facts.sch.confirmation_time_eq_of_delta_eq (E := (setupWithGST S g hg).E) (E' := S.E) rfl s
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, ?_, ?_⟩
  · unfold Restated.roundSleepinessW at h2 ⊢
    simp only [hop]
    exact h2
  · unfold Restated.committeeSleepinessW at h3 ⊢
    simp only [hcm, hct]
    exact h3

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

/-- Strong openings recurring on `[a, b]` move to the setup with GST `g`. -/
theorem tr_strongOpenings (facts : Record.Facts M) (S : Setup V) (g : Int) (hg : 0 ≤ g) (Sched : Schedule V) (a b : Int) (gap : Nat) (h : Restated.strongOpeningsRecurFrom M S Sched a b gap) :
    Restated.strongOpeningsRecurFrom M (setupWithGST S g hg) Sched a b gap := by
  have hpt : ∀ s : Slot, (Restated.interface M (setupWithGST S g hg) Sched).proposalTime s
      = (Restated.interface M S Sched).proposalTime s := fun s => facts.sch.proposal_time_eq_of_delta_eq (E := (setupWithGST S g hg).E) (E' := S.E) rfl s
  have hct : ∀ s : Slot, M.confirmation_time (setupWithGST S g hg).E s
      = M.confirmation_time S.E s := fun s => facts.sch.confirmation_time_eq_of_delta_eq (E := (setupWithGST S g hg).E) (E' := S.E) rfl s
  unfold Restated.strongOpeningsRecurFrom Restated.MultiProposerAt at h ⊢
  simp only [hpt, hct]
  exact h

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

/-- `v` honest through `i` steps of `x` is honest through `i` steps of the moved execution. -/
theorem tr_HonestThrough (facts : Record.Facts M) (S : Setup V) (g : Int) (hg : 0 ≤ g) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (i : Nat) (v : V) (h : Restated.HonestThrough M Sched x i v) :
    Restated.HonestThrough M Sched (Restated.toGST M S g hg (Restated.protocol_setupWithGST facts S g hg) x) i v := h

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

/-- If every honest send to an awake validator is delivered before `max t g + S.E.Δ`, the moved
    execution satisfies `SynchronyFromWake` at the setup with GST `g`. -/
theorem tr_SynchronyBy (facts : Record.Facts M) (S : Setup V) (g : Int) (hg : 0 ≤ g) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (h : Restated.SynchronyFromWakeBy M S x (fun t => max t g + S.E.Δ)) :
    Restated.SynchronyFromWake M (setupWithGST S g hg) (Restated.toGST M S g hg (Restated.protocol_setupWithGST facts S g hg) x) := h

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

/-- If `B` is an ancestor of `w`'s finalized block after `j` steps of the moved execution, it is an
    ancestor of `w`'s finalized block after `j` steps of `x`. -/
theorem tr_back_Preceq_F (facts : Record.Facts M) (S : Setup V) (g : Int) (hg : 0 ≤ g) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (j : Nat) (w : V) (B : Block V)
    (h : Block.Preceq B (((Restated.toGST M S g hg (Restated.protocol_setupWithGST facts S g hg) x)[j][w].st).st.core.F)) :
    Block.Preceq B ((x[j][w].st).st.core.F) := h

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

/-- Delivery outside `[b₀, b₁)` gives delivery of every honest send to an awake validator before
    `max t b₁ + S.E.Δ`. -/
theorem synchronyBy_of_outside (facts : Record.Facts M) (S : Setup V) {Sched : Schedule V}
    (x : AtomicExec (Record.protocolOf M S) Sched) {b₀ b₁ : Int} (hb : b₀ ≤ b₁) (hg : S.E.t_GST ≤ b₁)
    (h : Restated.SynchronyFromWakeOutside M S x b₀ b₁) :
    Restated.SynchronyFromWakeBy M S x (fun t => max t b₁ + S.E.Δ) := by
  intro k w sm hs hw
  have hle := deadlineOutside_le S hb hg (x[k].time : Int)
  obtain ⟨d, hkd, hl, h1, h2⟩ := h k w sm hs (awakeThroughout_mono Sched hw le_rfl hle)
  exact ⟨d, hkd, hl, h1, lt_of_lt_of_le h2 hle⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

/-- Catch-up on wake outside `[b₀, b₁)` gives catch-up before `max t b₁ + S.E.Δ`. -/
theorem catchUpBy_of_outside (facts : Record.Facts M) (S : Setup V) {Sched : Schedule V}
    (x : AtomicExec (Record.protocolOf M S) Sched) {b₀ b₁ : Int} (hb : b₀ ≤ b₁) (hg : S.E.t_GST ≤ b₁)
    (h : Restated.CatchUpOnWakeOutside M S x b₀ b₁) :
    Restated.CatchUpOnWakeBy M S x (fun t => max t b₁ + S.E.Δ) := by
  intro k w sm t_w hs hlt ha hna hw
  have hle := deadlineOutside_le S hb hg t_w
  obtain ⟨d, hkd, hl, h1, h2⟩ := h k w sm t_w hs hlt ha hna
    (awakeThroughout_mono Sched hw le_rfl hle)
  exact ⟨d, hkd, hl, h1, lt_of_lt_of_le h2 hle⟩

end

end DecoupledConsensusModel.Sts.Restated
