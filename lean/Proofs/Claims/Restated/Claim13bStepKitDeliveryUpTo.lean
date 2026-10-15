import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bSyncViewUpTo
import Model.Conditions.ClaimAsyncK_DeliveryUpTo
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring
import Proofs.Claims.Restated.Claim13bStepKitDeliveryRecv

/-!
# Recorded attestations, with synchrony up to a cutoff

When an honestly sent attestation is recorded in a receiver's store, assuming synchrony only up to
the send's own delivery deadline, stated over a model `M : Record.Model V` and its facts
`facts : Record.Facts M`.
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

/-- `attest_recorded_of_honestSend_succ` with synchrony assumed only up to the send's delivery
    deadline. -/
theorem attest_recorded_of_honestSend_succ_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {k_0 j : Nat}
    (hsync : Restated.SynchronyFromWakeBefore M S x (max (x[k_0].time : Int) S.E.t_GST + S.E.Δ))
    {v w : V} {a : NamedAttestation V}
    (hsend : Restated.HonestSendAt M S x k_0 (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)))
    (hlate : max (x[k_0].time : Int) S.E.t_GST + S.E.Δ ≤ (x[j].time : Int))
    (haw : AtomicAwake x j w)
    (hwaw : w ∈ Sched.awakeThroughout (x[k_0 + 1].time : Int)
      (max (x[k_0].time : Int) S.E.t_GST + S.E.Δ))
    (hwin : ∀ k : Nat, k < j →
      x.lbl k = AtomicAction.deliver w ⟨v, NamedObject.attest a⟩ →
      ¬ (a.round < (M.round_of S.hc (x[k][w].st).st.core.s) - S.hc.η_SG ∨
         (M.round_of S.hc (x[k][w].st).st.core.s) < a.round))
    (hroom : ∀ k : Nat, k < j →
      x.lbl k = AtomicAction.deliver w ⟨v, NamedObject.attest a⟩ →
      (M.round_votes (x[k][w].st).st.core a.erase).card ≠ 2)
    (hne : ∀ k : Nat, k < j →
      x.lbl k = AtomicAction.deliver w ⟨v, NamedObject.attest a⟩ →
      ∃ n' : M.N, M.process (Setup.alwaysAwake S) (x[k][w].st) (NamedObject.attest a) ⇢ n') :
    ∃ k : Nat, k < j ∧ x.lbl k = AtomicAction.deliver w ⟨v, NamedObject.attest a⟩ ∧
      (a.erase.confirmed ∈ M.round_votes (x[k][w].st).st.core a.erase ∨
        (a ∈ (x[k + 1][w].st).st.sg_rows a.round ∧
          a ∈ (x[j][w].st).st.sg_rows a.round ∧
          (x[k + 1][w].st).st.core.timestamp_sg_vote (M.sgVote a.erase)
            = some (((x[k][w].st).st.core.t : Stamp)))) :=
  Restated.attest_recorded_of_mem_view facts S Sched x
    (Restated.synchronyFromWakeView_of_deliver_succ_upTo facts S Sched x hsync hsend hwaw hlate) haw hwin hroom
    hne

end

end DecoupledConsensusModel.Sts.Restated
