import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bK_FreshAttestersW
import Model.Conditions.Claim13bStepSG
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bK_GradeDescendant

/-!
# The SG blocks of a round against the confirmed blocks of the next

The condition `ConfirmedCompatibleFreshSG`, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For every member `v` of `freshAttestersW` for round `r + 1` at step `n' + 1` and every member
    `v_1` of `HonRound` for round `r`, the block `v_1`'s round-`r` attestation, authored by `v_1`
    and sent at the round-`r` tick, names as confirmed lies on one chain with the confirmed block of
    every healing store `v`'s round-`(r + 1)` action read can leave. -/
def ConfirmedCompatibleFreshSG (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (r : Round) (n n' : Nat) : Prop :=
  ∀ v ∈ Restated.freshAttestersW M S Sched x (r + 1) (n' + 1), ∀ v_1 ∈ Restated.HonRound M S Sched r,
    ∀ a : NamedAttestation V, a.round = r → a.val_index = v_1 →
    (⟨v_1, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n + 1].sent →
    ∀ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies → a.confirmed = some C.root →
    ∀ hs ∈ Restated.actionHealingStore M S (x[n'][v].st) (r + 1),
    Block.compatible C.erase hs.live_confirmed = true

end

end DecoupledConsensusModel.Sts.Restated
