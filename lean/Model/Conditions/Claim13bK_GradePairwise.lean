import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bStepSG
import Model.Record.Wiring

/-!
# The SG blocks of a round against the next round's honest active attesters

The conditions `ConfirmedCompatibleFreshSGOverHonRound` and `PreceqFreshSG`, stated over a model
`M : Record.Model V`.
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

/-- For every member `v` of `HonRound` for round `r + 1` and every member `v_1` of `HonRound` for
    round `r`, the block `v_1`'s round-`r` attestation, authored by `v_1` and sent at the round-`r`
    tick, names as confirmed lies on one chain with the confirmed block of every store `hs` of `v`'s
    round-`(r + 1)` action read. -/
def ConfirmedCompatibleFreshSGOverHonRound (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (r : Round) (n n' : Nat) : Prop :=
  ∀ v ∈ Restated.HonRound M S Sched (r + 1), ∀ v_1 ∈ Restated.HonRound M S Sched r,
    ∀ a : NamedAttestation V, a.round = r → a.val_index = v_1 →
    (⟨v_1, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n + 1].sent →
    ∀ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies → a.confirmed = some C.root →
    ∀ hs ∈ Restated.actionHealingStore M S (x[n'][v].st) (r + 1),
      Block.compatible C.erase hs.live_confirmed = true

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Some member `v_1` of `HonRound` for round `r` sent at the round-`r` tick a round-`r` attestation
    it authored, whose confirmed root names a body `C` of `v_1`'s store after that tick, and `B` is
    an ancestor of `C`. -/
def PreceqFreshSG (M : Record.Model V) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (r : Round) (n : Nat) (B : Block V) : Prop :=
  ∃ v_1 ∈ Restated.HonRound M S Sched r, ∃ a : NamedAttestation V,
    a.round = r ∧ a.val_index = v_1 ∧
    (⟨v_1, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n + 1].sent ∧
    ∃ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies ∧ a.confirmed = some C.root ∧
      Block.Preceq B C.erase

end

end DecoupledConsensusModel.Sts.Restated
