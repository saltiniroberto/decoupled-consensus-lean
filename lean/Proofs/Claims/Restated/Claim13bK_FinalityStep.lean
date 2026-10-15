import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13beRoute3_45
import Proofs.Claims.Restated.Claim13beRoute3_48
import Proofs.Claims.Restated.Claim13beRoute3_69
import Proofs.Claims.Restated.Vocabulary_Execution_EmissionShape
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_Protocol_ValidatorClient_Bridge
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.RunVocabulary
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Node
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_25

/-!
# A lock in a record is backed by a certificate

That a lock in a validator's record is backed by a certificate, read along the path of the bundle
`Restated.AdmissibleFieldsOn`, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.Optimistic
open Framework.StsMultisetLog

local macro "p46% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Claims.Restated.Claim13beRoute3_46)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

local macro "p69% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Claims.Restated.Claim13beRoute3_69)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

/-- Under the bundle with path `W`, if `v ∈ Xb`, `H ≠ 0`, and the record of `v`'s node state in
    `W (strictEventIndex rho t)` locks `L` at `H`, then a certificate for `L` at `H` exists along
    `W` over `Xb`. -/
theorem recordLock_certificateOn_f1 (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} (hv : v ∈ Xb) (t : Int) {H : Height} (hH : H ≠ 0) {L : BlockId}
    (hl : (W (strictEventIndex rho t) v).record.legacy.lock H = some L) :
    Restated.CertificateOn M S rho W Xb H L := by
  obtain ⟨i, hi, t', att, hevent, w₁, hw₁, out, hout, hmem, hpair, hslice⟩ :=
    Restated.Vocabulary.Proofs.HealingSurface.recordLock_finalityEmission_before_migration facts S
      rho v _ (W (strictEventIndex rho t)) (hf.onePath _).1 hl
  have _hr_w₁ := facts.ndRun.stateBeforeOf_reachedNode S rho _ w₁ hw₁ v
  have _hv_w₁ := facts.ndRun.stateBeforeOf_runs_as S rho _ w₁ hw₁ v
  obtain ⟨htime, hrow⟩ := (p46% tick_attest₄₆) facts S v (w₁ v) t' out hout att hmem
  have hle : strictEventIndex rho t' ≤ i := (p46% strict_le_tick₄₆) hf.sorted hevent
  obtain ⟨w₀, hw₀, hslice₀⟩ := ((p46% mem_stateBeforeOf_split₄₆) S rho hle w₁).mp hw₁
  have hw₀' : w₀ ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t' := by
    rw [(p69% stateBeforeTime_eq_strict₆₉) S rho hf.sorted]
    exact hw₀
  have hsame : w₁ v = w₀ v ∨ w₁ v = M.wake (w₀ v) :=
    Restated.Vocabulary.Proofs.NamedRuntime.tick_prefix_eq_strict_of_fields facts S rho hf.sorted
      hf.tickIndexUnique hevent w₀ hw₀' w₁ hslice₀
  have hsameBodies : (w₁ v).st.bodies = (w₀ v).st.bodies := by
    rcases hsame with h | h
    · rw [h]
    · rw [h, (facts.nd.wake_st_record _).1]
  have hsameRead : ∀ r : Round,
      Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (w₁ v) r =
        Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (w₀ v) r := by
    intro r
    rcases hsame with h | h
    · rw [h]
    · rw [h, (p46% actionReadFrom_wake₄₆) facts]
  have hstep : Function.update w₁ v out.1 ∈
      Record.worldStepOf M S w₁ (Record.Event.tick v t') := Or.inl ⟨out, hout, rfl⟩
  have hmono := Restated.Vocabulary.Proofs.NamedBodyRetention.stateBefore_bodies_mono facts S rho v
    (Nat.le_of_lt hi) w₁ hw₁ _ ((p46% mem_slice_cons₄₆) S rho hi hevent hstep hslice)
  have hbodies : ∀ Dn ∈ (w₀ v).st.bodies, Restated.RunBlockOn M S rho W Xb Dn := by
    intro Dn hDn
    rw [← hsameBodies] at hDn
    exact Restated.runBlock_of_stateBefore_memOn facts S W Xb hv (hmono hDn)
  subst htime
  rw [hsameRead] at hrow
  obtain ⟨n', hn', D', hD'⟩ :=
    (p46% actionAttestation_nonempty₄₆) facts S (w₀ v) att.round (S.node v)
  exact (p69% actionFinalityPair_certificate_any₆₉s) facts S W Xb v att.round hH w₀ hw₀' hbodies
    n' hn' D' hD' (by rw [hrow n' hn' D' hD']; exact hpair)

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog

local macro "p67b% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Claims.Restated.Claim13beRoute3_67b)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

end

end DecoupledConsensusModel.Sts.Restated
