module
public import Proofs.Vocabulary.Execution.Runtime
public import Proofs.Vocabulary.Execution.Wire
public import Proofs.Vocabulary.Execution.HealthyLocalFacts
public import Proofs.Vocabulary.Internal.Definitions.NamedOutageEntry
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section

/-!
# Attestation fields of a tick

Lemmas on the attestations a tick emits and on their fields.
-/
namespace DecoupledConsensusModel.Proofs.NamedOutageHistory.OutageInputs
open Execution Internal.NamedOutageEntry
variable {V : Type} [DecidableEq V] [Fintype V]

omit [DecidableEq V] [Fintype V] in
theorem no_attest_proposal (p : Prop) [Decidable p]
    (body : Option (NamedBlock V)) (a : NamedAttestation V) :
    NamedObject.attest a ∉ (if p then
      match body with
      | none => []
      | some B => [NamedObject.block B]
    else []) := by
  split_ifs <;> cases body <;> simp

omit [DecidableEq V] [Fintype V] in
theorem no_attest_vote (p : Prop) [Decidable p]
    (vote : Option (GoldfishVote V)) (a : NamedAttestation V) :
    NamedObject.attest a ∉ (if p then vote.toList.map NamedObject.gfVote else []) := by
  split_ifs <;> cases vote <;> simp

theorem attestation_suffix_fields (gc : Protocol.GradeContract V) (S : Setup V)
    (v : V) (st : Protocol.NamedStore V) (record : Protocol.NamedRecord)
    (t : Time) (a : NamedAttestation V) (prior : List (NamedObject V))
    (hprefix : NamedObject.attest a ∉ prior)
    (h : NamedObject.attest a ∈ (if t = S.a (S.hc.round_of st.core.s) ∧
        (S.node v).awake (S.hc.round_of st.core.s) = true then
      let out := Protocol.NamedDuties.attest_with gc S.E S.hc (S.node v) st record
      (out.1, out.2.1, prior ++ [NamedObject.attest out.2.2])
    else (st, record, prior)).2.2) :
    t = S.a a.round ∧ (S.node v).awake a.round = true ∧ a.val_index = v := by
  split_ifs at h with hact
  · simp only [List.mem_append, List.mem_singleton, hprefix, false_or,
      NamedObject.attest.injEq] at h
    subst a
    exact ⟨hact.1, hact.2, S.node_val_index v⟩
  · exact False.elim (hprefix h)

/-- An attestation a tick emits at `t` has `t = S.a a.round`, its emitter awake at that round, and
    the emitter as its validator. -/
theorem tick_attestation_fields (gc : Protocol.GradeContract V) (S : Setup V)
    (v : V) (st : Protocol.NamedStore V) (record : Protocol.NamedRecord)
    (t : Time) (a : NamedAttestation V)
    (h : NamedObject.attest a ∈
      (Protocol.NamedTick.tick gc S.E S.hc S.cfg (S.node v) st record t).2.2) :
    t = S.a a.round ∧ (S.node v).awake a.round = true ∧ a.val_index = v := by
  rw [NamedTick.tick_computed_duties] at h
  dsimp only at h
  apply attestation_suffix_fields gc S v _ record t a _ ?_ h
  simp only [List.mem_append, no_attest_vote, or_false]
  exact no_attest_proposal _ _ a


end DecoupledConsensusModel.Proofs.NamedOutageHistory.OutageInputs

end
