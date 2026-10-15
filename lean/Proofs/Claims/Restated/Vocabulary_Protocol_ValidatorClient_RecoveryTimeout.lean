import Proofs.Vocabulary.Protocol.ValidatorClient.RecoveryTimeout
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Protocol_ValidatorClient_HeightPairCases
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedActionReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_FinalityPairCore
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_HeightPairCases
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_RecordFresh
import Model.Record.Wiring

/-!
# Height pairs of the round action under a timeout

Theorems on the finality pair and the height pair of the round action, at a fresh height and at a
height whose timeout is already recorded, stated over a model `M : Record.Model V` and its facts
`facts : Record.Facts M`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Protocol (Record height_pair own_lock finality_pair)
open Internal
open Execution

/-- For every outcome `A` of the round action and every head `Hd` the action can resolve, `A`'s
    finality pair is the finality pair `record.legacy` gives for the justified height, the root of
    the justified block and the finalized height of `Hd`'s chain state. -/
theorem Vocabulary.Proofs.HealingSurface.round_action_finality_pair_eq (facts : Record.Facts M) (contract : M.Contract)
    (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V)
    (st : M.HS) (record : M.NR)
    (A : M.NR × NamedAttestation V) (hA : M.round_action_with contract E hc nd st record ⇢ A)
    (Hd : Block V)
    (hHd : Restated.Vocabulary.Proofs.HealingSurface.actionHeadWith M contract E hc st ⇢ Hd) :
    A.2.finality_pair =
      M.finality_pair record.legacy (st.σ Hd).h_j (st.σ Hd).J.root (st.σ Hd).h_F := by
  obtain ⟨res, hres, hHd'⟩ := hHd
  exact facts.dt.round_action_finality_pair_eq contract E hc nd st record A hA res hres Hd hHd'

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Protocol (Record height_pair own_lock finality_pair)
open Internal
open Execution

/-- For every outcome `A` of the round action: if the action can select the source `Q`, `Q`'s height
    is `H` and is not justifiable, `record.legacy` is fresh at `H`, and the action can resolve a
    head `Hd` whose justified height is not `H`, then `A`'s height pair is the vote for `H` and
    `Q`'s height target root with the bit `true`. -/
theorem Vocabulary.Proofs.HealingSurface.round_action_height_pair_timeout_of_fresh_source (facts : Record.Facts M)
    (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig)
    (nd : Protocol.Node V) (st : M.HS) (record : M.NR)
    (A : M.NR × NamedAttestation V) (hA : M.round_action_with contract E hc nd st record ⇢ A)
    {H : Height} {Q : Block V}
    (hsource : Restated.Vocabulary.Proofs.HealingSurface.actionSource M contract E hc st ⇢ some Q)
    (hheight : (st.σ Q).h = H) (hnj : (st.σ Q).nj = true)
    (hfresh : Restated.Vocabulary.Proofs.HealingSurface.RecordFreshAt M record.legacy H)
    {Hd : Block V}
    (hHd : Restated.Vocabulary.Proofs.HealingSurface.actionHeadWith M contract E hc st ⇢ Hd)
    (hheadj : (st.σ Hd).h_j ≠ H) :
    A.2.height_pair = NamedHeightPair.vote H (st.σ Q).T_h.root true := by
  have havoid : ∀ p : FinalityPair, A.2.finality_pair = some p → p.height ≠ H := by
    intro p hp
    rw [Restated.Vocabulary.Proofs.HealingSurface.round_action_finality_pair_eq facts contract E hc nd
      st record A hA Hd hHd] at hp
    have hpHeight := facts.vc.finality_pair_height hp
    intro hpH
    exact hheadj (hpHeight.trans hpH)
  rw [Restated.Vocabulary.Proofs.HealingSurface.named_round_action_height_pair facts contract E hc nd
    st record A hA (some Q) hsource, Option.map_some, hheight, hnj,
    facts.vc.height_pair_timeout_of_fresh_of_finality_avoids hfresh _ havoid]
  exact facts.vc.encodeHeight_of_timeout

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Protocol (Record height_pair own_lock finality_pair)
open Internal
open Execution

/-- For every outcome `A` of the round action: if the action can select the source `Q`, `Q`'s height
    is `H`, and `record.legacy` has a timeout at `H`, then `A`'s height pair is the vote for `H` and
    `Q`'s height target root with the bit `true`. -/
theorem Vocabulary.Proofs.HealingSurface.round_action_height_pair_timeout_of_recorded_source (facts : Record.Facts M)
    (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig)
    (nd : Protocol.Node V) (st : M.HS) (record : M.NR)
    (A : M.NR × NamedAttestation V) (hA : M.round_action_with contract E hc nd st record ⇢ A)
    {H : Height} {Q : Block V}
    (hsource : Restated.Vocabulary.Proofs.HealingSurface.actionSource M contract E hc st ⇢ some Q)
    (hheight : (st.σ Q).h = H)
    (htimeout : record.legacy.timeout H = true) :
    A.2.height_pair = NamedHeightPair.vote H (st.σ Q).T_h.root true := by
  rw [Restated.Vocabulary.Proofs.HealingSurface.named_round_action_height_pair facts contract E hc nd
    st record A hA (some Q) hsource, Option.map_some, hheight,
    facts.vc.height_pair_eq_timeout_of_timeout record.legacy _ htimeout]
  exact facts.vc.encodeHeight_of_timeout

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Protocol (Record height_pair own_lock finality_pair)
open Internal
open Execution

/-- For every world `w` before round `r`'s action instant and every action read `n` of `v` computed
    from `w`: if the action can select the FG source `Q`, `Q`'s height in `n` is `H`, and `v`'s
    record in `w` has a timeout at `H`, then every outcome `D` of the attestation duty on `n` has as
    its height pair the vote for `H` and `Q`'s height target root with the bit `true`. -/
theorem Vocabulary.Proofs.HealingSurface.actionAttestationAt_height_pair_timeout_of_recorded (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) {v : V} {r : Round} {Q : Block V} {H : Height} :
    ∀ w ∈ Restated.Vocabulary.Execution.Run.stateBeforeTime M S rho ((Restated.Vocabulary.Execution.Setup.a M S r)),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (w v) r,
      Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ some Q →
      (n.σ Q).h = H →
      (w v).record.legacy.timeout H = true →
      ∀ D : M.NS × M.NR × NamedAttestation V,
        M.duties_attest_with (M.gradeContract n.cache) S.E S.hc (S.node v) n.st n.record ⇢ D →
        D.2.2.height_pair = NamedHeightPair.vote H (n.σ Q).T_h.root true := by
  intro w hw n hn hsource hheight htimeout D hD
  obtain ⟨c, -, st, -, hneq⟩ := hn
  have hrecEq : n.record = (w v).record := by rw [hneq]; exact facts.nd.mkNode_record _ _ _
  obtain ⟨A, hA⟩ := facts.dt.round_action_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (S.node v) (M.toHealing n.st.core) n.record
  rw [facts.dt.attest_with_row _ _ _ _ _ _ D hD A hA]
  have hσ : (M.toHealing n.st.core).σ = n.st.core.σ := facts.sto.ModelProperties_toHealing_σ _
  have hheight' : ((M.toHealing n.st.core).σ Q).h = H := by
    rw [hσ]
    exact hheight
  have h := Restated.Vocabulary.Proofs.HealingSurface.round_action_height_pair_timeout_of_recorded_source facts
    (M.gradeContract n.cache)
    S.E S.hc (S.node v) (M.toHealing n.st.core)
    n.record A hA hsource hheight' (by rw [hrecEq]; exact htimeout)
  rw [hσ] at h
  exact h

end

end DecoupledConsensusModel.Sts.Restated
