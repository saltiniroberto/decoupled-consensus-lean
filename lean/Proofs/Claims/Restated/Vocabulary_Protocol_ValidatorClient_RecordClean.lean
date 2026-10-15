import Proofs.Vocabulary.Protocol.ValidatorClient.RecordClean
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Execution_BodyRetention
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring

/-!
# The block tree grows and the round action's finality pair

A validator's block tree only grows along a run, and the finality pair a round action emits is the
one its signing record gives at the head, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open Protocol (ChainState HeightConfig)
open Protocol (HealConfig)
open Internal
open Execution

private theorem rc_mem_stateBeforeOf_of_path (S : Setup V) (rho : Record.Run V) {i j : Nat}
    (hij : i ≤ j) {w₁ w₂ : V → M.N} (hw₁ : w₁ ∈ Record.stateBeforeOf M S rho i)
    (hw₂ : w₂ ∈ ((rho.events.drop i).take (j - i)).foldlM (Record.worldStepOf M S) w₁) :
    w₂ ∈ Record.stateBeforeOf M S rho j := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  rw [Nat.add_sub_cancel_left] at hw₂
  unfold Record.stateBeforeOf
  rw [List.take_add, List.foldlM_append, Set.bind_def]
  exact Set.mem_iUnion₂.mpr ⟨w₁, hw₁, hw₂⟩

/-- For every world `w₁` before the `i`-th event of `ρ`, every `j ≥ i` and every world `w₂` the
    events `i` to `j - 1` can lead to from `w₁`, the block tree of `v`'s store in `w₁` is contained
    in the block tree of `v`'s store in `w₂`. -/
theorem Vocabulary.Proofs.stateBefore_T_subset (facts : Record.Facts M) (S : Setup V) (ρ : Record.Run V) (v : V) {i : Nat} :
    ∀ w₁ ∈ Record.stateBeforeOf M S ρ i,
    ∀ j : Nat, i ≤ j →
      ∀ w₂ ∈ ((ρ.events.drop i).take (j - i)).foldlM (Record.worldStepOf M S) w₁,
      (w₁ v).st.T ⊆ (w₂ v).st.T := by
  intro w₁ hw₁ j hij w₂ hw₂ B hB
  have hw₂' : w₂ ∈ Record.stateBeforeOf M S ρ j := rc_mem_stateBeforeOf_of_path S ρ hij hw₁ hw₂
  have hTi : (w₁ v).st.core.T = (w₁ v).st.bodies.image NamedBlock.erase :=
    (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S ρ i v w₁ hw₁).1.1.1.1
  have hTj : (w₂ v).st.core.T = (w₂ v).st.bodies.image NamedBlock.erase :=
    (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S ρ j v w₂ hw₂').1.1.1.1
  have hB' : B ∈ (w₁ v).st.core.T := hB
  rw [hTi] at hB'
  obtain ⟨D, hD, hDB⟩ := Finset.mem_image.mp hB'
  show B ∈ (w₂ v).st.core.T
  rw [hTj]
  exact Finset.mem_image.mpr
    ⟨D, Restated.Vocabulary.Proofs.NamedBodyRetention.stateBefore_bodies_mono facts S ρ v hij w₁ hw₁
      w₂ hw₂ hD, hDB⟩

end

section
open DecoupledConsensusModel.Proofs
open Protocol (ChainState HeightConfig)
open Protocol (HealConfig)
open Internal
open Execution

/-- For every outcome `A` of the round action, every choice `res` of one outcome of the resolution
    test per vote, and every head `Hd` `M.get_head_with` can return from `st`'s pool at `st`'s slot
    restricted to the votes `u` with `res u = true`, the finality pair of `A`'s attestation is the
    finality pair `record`'s legacy record gives for the justified height, the root of the justified
    block and the finalized height of `Hd`'s chain state. -/
theorem Vocabulary.Proofs.round_action_finality_pair (facts : Record.Facts M) (contract : M.Contract)
    (E : Env V) (hc : HealConfig) (nd : Protocol.Node V)
    (st : M.HS) (record : M.NR) :
    ∀ A : M.NR × NamedAttestation V, M.round_action_with contract E hc nd st record ⇢ A →
    ∀ res : GoldfishVote V → Bool, (∀ u, M.resolved st.T u ⇢ res u) →
    ∀ Hd : Block V,
      M.get_head_with contract E hc st (st.toFG.toSG.toGoldfishStore.pool st.s)
        ((st.toFG.toSG.toGoldfishStore.pool st.s).filter (fun u => res u = true)) st.s ⇢ Hd →
      A.2.finality_pair =
        M.finality_pair record.legacy
          (st.σ Hd).h_j (st.σ Hd).J.root (st.σ Hd).h_F :=
  facts.dt.round_action_finality_pair_eq contract E hc nd st record

end

end DecoupledConsensusModel.Sts.Restated
