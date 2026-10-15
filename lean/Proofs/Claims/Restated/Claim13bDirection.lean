import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Record.Wiring

/-!
# The source block of a non-empty height vote

Over a model `M : Record.Model V`: the height and the root of a non-empty height vote in a round
action's attestation are the chain-state height and the height target of the action's
finality-gadget source block.
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

/-- For every node state `n` the action store can be, if the attestation of an outcome `D` of the
    attestation duty on `n` carries a height vote for height `h₀` and root `entry`, then every
    outcome `o` of the finality-gadget source at `n` is some block `Cfg`, the chain state `n`
    records for `Cfg` is at height `h₀`, and that chain state's height target has root `entry`. -/
theorem source_of_actionAttestation_heightPair (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (w : V) (r : Round)
    {h₀ : Height} {entry : BlockId} {tmo : Bool} :
    ∀ n ∈ Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt M S rho w r,
    ∀ D, M.duties_attest_with (M.gradeContract n.cache) S.E S.hc (S.node w) n.st n.record ⇢ D →
    D.2.2.height_pair = NamedHeightPair.vote h₀ entry tmo →
    ∀ o, Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ o →
    ∃ Cfg : Block V,
      o = some Cfg ∧
      (n.st.core.σ Cfg).h = h₀ ∧
      (n.st.core.σ Cfg).T_h.root = entry := by
  intro n _ D hD h o ho
  let gc := M.gradeContract n.cache
  obtain ⟨A, hA⟩ := facts.dt.round_action_with_nonempty gc S.E S.hc (S.node w)
    (M.toHealing n.st.core) n.record
  rw [facts.dt.attest_with_row gc S.E S.hc (S.node w) n.st n.record D hD A hA] at h
  obtain ⟨I, hI⟩ := facts.dt.with_attestation_input_nonempty gc S.E S.hc (S.node w)
    (M.toHealing n.st.core)
  obtain ⟨pair, hpair⟩ := facts.dt.round_action_with_height_pair_input
    gc S.E S.hc (S.node w) (M.toHealing n.st.core) n.record A hA I hI
  rw [hpair] at h
  obtain ⟨b, hb⟩ := facts.vc.fields_of_encodeHeight_vote _ _ h
  have hdec : ∃ A2, M.grade2_block_with gc S.E S.hc (M.toHealing n.st.core)
      (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ A2 ∧
      M.fg_source_with gc S.E S.hc (M.toHealing n.st.core)
        (M.round_of S.hc (M.toHealing n.st.core).s) A2 ⇢ o := by
    simp only [Restated.Vocabulary.Proofs.HealingSurface.actionFGSource, Record.Returns,
      ExceptT.run_bind, Set.bind_def, Set.mem_iUnion] at ho
    obtain ⟨x, hx, hb⟩ := ho
    cases x with
    | ok a => exact ⟨a, hx, hb⟩
    | error e => simp at hb
  obtain ⟨A2, hA2, hF⟩ := hdec
  rw [facts.dt.with_attestation_input_id_fields gc S.E S.hc (S.node w) _ I hI A2 hA2 o hF] at hb
  rw [Option.map_eq_some_iff] at hb
  obtain ⟨q, hq, hqe⟩ := hb
  rw [facts.sto.ModelProperties_toHealing_σ] at hqe
  refine ⟨q, hq, ?_, ?_⟩
  · exact congrArg (fun p : Height × BlockId × Bool => p.1) hqe
  · exact congrArg (fun p : Height × BlockId × Bool => p.2.1) hqe

end

end DecoupledConsensusModel.Sts.Restated
