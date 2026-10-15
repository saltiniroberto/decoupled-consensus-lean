import Proofs.Vocabulary.Execution.NamedAncestry
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Sts_Interface
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Objects
import Model.Record.Wiring

/-!
# A receipt has an outcome

A receipt can have no outcome when the received block has the root of another block the receiver
holds. The theorems here give a receipt an outcome in three cases: the receipt changed the
receiver's node state; the execution has no root collision among the blocks in play and the receiver
is honest through the delivery; or the run has no root collision among the blocks read through a set
of validators that holds the receiver.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts.Restated

open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog
open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

/-- If step `j` delivers `sm` to `v` and `v`'s node state after the step differs from the one
    before, then `v`'s receipt of `sm`'s payload from its node state before the step has an outcome. -/
theorem receipt_outcome_of_changed (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {j : Nat} {v : V}
    {sm : SignedMsg V (NamedObject V)}
    (hl : x.lbl j = AtomicAction.deliver v sm)
    -- `v`'s node state changed at step `j`
    (hne : x[j + 1][v].st ≠ x[j][v].st) :
    ∃ n' : M.N, M.process (Setup.alwaysAwake S) (x[j][v].st) sm.msg ⇢ n' := by
  rcases Record.st_succ_of_deliver M S Sched x hl with h | ⟨-, heq⟩
  · exact ⟨_, h⟩
  · exact absurd heq hne

/-- If step `j` delivers `sm` to `v`, and `v`'s store had not processed `o` before the step and has
    after it, then `v`'s receipt of `sm`'s payload from its node state before the step has an
    outcome. -/
theorem receipt_outcome_of_flip (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {j : Nat} {v : V}
    {sm : SignedMsg V (NamedObject V)} {o : NamedObject V}
    (hl : x.lbl j = AtomicAction.deliver v sm)
    -- `v`'s store had not processed `o` before step `j`
    (h0 : Restated.Vocabulary.Execution.Object.processed M (x[j][v].st).st o = false)
    -- `v`'s store had processed `o` after step `j`
    (h1 : Restated.Vocabulary.Execution.Object.processed M (x[j + 1][v].st).st o = true) :
    ∃ n' : M.N, M.process (Setup.alwaysAwake S) (x[j][v].st) sm.msg ⇢ n' :=
  receipt_outcome_of_changed facts S Sched x hl (fun h => by rw [h, h0] at h1; cases h1)

/-- When the blocks in play have no root collision, if step `j` delivers `sm` to `v` and `v` is
    honest through step `j`, then `v`'s receipt of `sm`'s payload from its node state before the
    step has an outcome. -/
theorem receipt_outcome_of_deliver_honest (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hroot : Restated.RootCollisionFreeInLog M S Sched x) {j : Nat} {v : V}
    {sm : SignedMsg V (NamedObject V)}
    (hl : x.lbl j = AtomicAction.deliver v sm)
    (hv : Restated.HonestThrough M Sched x j v) :
    ∃ n' : M.N, M.process (Setup.alwaysAwake S) (x[j][v].st) sm.msg ⇢ n' := by
  refine facts.nd.process_nonempty (Setup.alwaysAwake S) (x[j][v].st) sm.msg ?_
  intro B hB C hC hr
  have hs : AtomicStep (Record.protocolOf M S) Sched (x.lbl j) x[j] x[j + 1] := x.step j
  rw [hl] at hs
  have hBlog : Restated.blockInLog M S Sched x B :=
    ⟨B, Or.inl ⟨j, sm, hs.1.1, hB⟩, Proofs.NamedAncestry.named_self B⟩
  have hClog : Restated.blockInLog M S Sched x C :=
    ⟨C, Or.inr ⟨j, v, hv, hC⟩, Proofs.NamedAncestry.named_self C⟩
  exact hroot.root_injective C B hClog hBlog C B
    (Or.inl (Proofs.NamedAncestry.named_self C)) (Or.inr (Proofs.NamedAncestry.named_self B)) hr

/-- When the blocks in play have no root collision and corruption only grows, if step `j` delivers
    `sm` to `v`, then `v`'s receipt of `sm`'s payload from its node state before the step has an
    outcome. -/
theorem receipt_outcome_of_deliver_mono (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hroot : Restated.RootCollisionFreeInLog M S Sched x)
    (hmono : Sched.MonotoneCorruption) {j : Nat} {v : V}
    {sm : SignedMsg V (NamedObject V)}
    (hl : x.lbl j = AtomicAction.deliver v sm) :
    ∃ n' : M.N, M.process (Setup.alwaysAwake S) (x[j][v].st) sm.msg ⇢ n' := by
  have hs : AtomicStep (Record.protocolOf M S) Sched (x.lbl j) x[j] x[j + 1] := x.step j
  rw [hl] at hs
  have hnot : v ∉ Sched.adv (x[j].time : Int) := AtomicStep.deliver_not_adv hs
  exact receipt_outcome_of_deliver_honest facts S Sched x hroot hl
    (fun t' ht' h => hnot (hmono t' _ ht' h))

/-- On a path `W` of `rho`, if the `i`-th event delivers `o` to `v` and `v`'s store in `W (i + 1)`
    differs from its store in `W i`, then `v`'s receipt of `o` from its node state in `W i` has an
    outcome. -/
theorem receipt_outcome_of_changedOn (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    {i : Nat} {v : V} {o : NamedObject V} {t : Int}
    (he : rho.events[i]? = some (.deliver v o t))
    -- `v`'s store changed at the `i`-th event
    (hne : (W (i + 1) v).st ≠ (W i v).st) :
    ∃ n' : M.N, M.process S (W i v) o ⇢ n' := by
  rcases Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_deliver facts S rho he (W i) (hW i).1
      (W (i + 1)) (hW i).2 with h | ⟨-, heq⟩
  · exact ⟨_, h⟩
  · exact absurd (congrArg (fun n => n.st) heq) hne

/-- If the run blocks of `rho` read through `Xb` along `W` have no root collision, `v` is in `Xb`,
    and the `i`-th event delivers `o` to `v`, then `v`'s receipt of `o` from its node state in `W i`
    has an outcome. -/
theorem receipt_outcome_of_rootCollisionFreeOn (facts : Record.Facts M) (S : Setup V)
    {rho : Record.Run V} {W : Nat → V → M.N} {Xb : Finset V}
    (hroot : Restated.RootCollisionFreeOn M S rho W Xb)
    {i : Nat} {v : V} {o : NamedObject V} {t : Int} (hv : v ∈ Xb)
    (he : rho.events[i]? = some (.deliver v o t)) :
    ∃ n' : M.N, M.process S (W i v) o ⇢ n' := by
  refine facts.nd.process_nonempty S (W i v) o ?_
  intro B hB C hC hr
  subst hB
  exact hroot.root_injective C B ⟨C, Or.inr ⟨v, hv, i, hC⟩, Proofs.NamedAncestry.named_self C⟩
    ⟨B, Or.inl (Restated.objects_of_delivery rho he), Proofs.NamedAncestry.named_self B⟩ C B
    (Or.inl (Proofs.NamedAncestry.named_self C)) (Or.inr (Proofs.NamedAncestry.named_self B)) hr

end DecoupledConsensusModel.Sts.Restated
