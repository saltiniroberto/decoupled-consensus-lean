import Proofs.Vocabulary.Protocol.ValidatorClient.SlashableBound
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Protocol_ValidatorClient_Bridge
import Proofs.Vocabulary.Protocol.ValidatorClient.RecordFresh
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_RecordFresh
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Event
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Node
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_SlashableBound
import Model.Record.Wiring

/-!
# No timeout against a finality pair

A validator never emits both a finality pair and a timeout at the same height, stated over a model
`M : Record.Model V` and its facts `facts : Record.Facts M`, with helpers about the signing record
along a run.
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
open DecoupledConsensusModel.Proofs.HealingSurface
open Protocol (Record create_attestation finality_pair height_pair
  record_attestation)
open Internal
open Execution

/-- An event that is not a tick of `v` leaves `v`'s signing record unchanged, in every world it can
    lead to. -/
private theorem sb_step_record (facts : Record.Facts M) (S : Setup V) (w w₂ : V → M.N)
    (e : Record.Event V) (v : V) (hw₂ : w₂ ∈ Record.worldStepOf M S w e)
    (hne : ∀ t : Time, e ≠ .tick v t) : (w₂ v).record = (w v).record := by
  cases e with
  | wake u t =>
    simp only [Record.worldStepOf, Set.mem_singleton_iff] at hw₂
    subst hw₂
    by_cases hu : u = v
    · subst u
      rw [Function.update_self, (facts.nd.wake_st_record (w v)).2]
    · rw [Function.update_of_ne (Ne.symm hu)]
  | tick u t =>
    have hu : u ≠ v := fun h => hne t (by rw [h])
    simp only [Record.worldStepOf, Set.mem_setOf_eq] at hw₂
    rcases hw₂ with ⟨out, -, rfl⟩ | ⟨-, rfl⟩
    · rw [Function.update_of_ne (Ne.symm hu)]
    · rfl
  | deliver u o t =>
    simp only [Record.worldStepOf, Set.mem_setOf_eq] at hw₂
    rcases hw₂ with ⟨n', hn', rfl⟩ | ⟨-, rfl⟩
    · by_cases hu : u = v
      · subst u
        rw [Function.update_self, facts.nd.process_record S (w v) o n' hn']
      · rw [Function.update_of_ne (Ne.symm hu)]
    · rfl

/-- If a property `P` of signing records holds of `v`'s record in the world `w` and every outcome of
    a tick of `v` keeps it, then it holds of `v`'s record in every world the events `l` can lead to
    from `w`. -/
private theorem sb_foldlM_record (facts : Record.Facts M) (S : Setup V) (v : V)
    (P : M.NR → Prop)
    (htick : ∀ (n : M.N) (t : Time) (out : M.N × List (NamedObject V)),
      M.tick S v n t ⇢ out → P n.record → P out.1.record) :
    ∀ (l : List (Record.Event V)) (w : V → M.N), P (w v).record →
      ∀ w₂ ∈ l.foldlM (Record.worldStepOf M S) w, P (w₂ v).record := by
  intro l
  induction l with
  | nil =>
    intro w hw w₂ hw₂
    rw [Set.mem_singleton_iff.mp hw₂]
    exact hw
  | cons e l ih =>
    intro w hw w₂ hw₂
    rw [List.foldlM_cons, Set.bind_def] at hw₂
    obtain ⟨w', hw', hw₂'⟩ := Set.mem_iUnion₂.mp hw₂
    refine ih w' ?_ w₂ hw₂'
    by_cases he : ∃ t, e = .tick v t
    · obtain ⟨t, rfl⟩ := he
      simp only [Record.worldStepOf, Set.mem_setOf_eq] at hw'
      rcases hw' with ⟨out, hout, rfl⟩ | ⟨-, rfl⟩
      · rw [Function.update_self]
        exact htick (w v) t out hout hw
      · exact hw
    · rw [sb_step_record facts S w w' e v hw' (fun t h => he ⟨t, h⟩)]
      exact hw

/-- Along a path `W` of `rho`, if a property `P` of signing records holds of `v`'s record in `W m`
    and every outcome of a tick of `v` keeps it, then it holds of `v`'s record in `W k` for every
    `k ≥ m`. -/
private theorem sb_path_record (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (v : V)
    (P : M.NR → Prop)
    (htick : ∀ (n : M.N) (t : Time) (out : M.N × List (NamedObject V)),
      M.tick S v n t ⇢ out → P n.record → P out.1.record) :
    ∀ (m k : Nat), m ≤ k → P (W m v).record → P (W k v).record := by
  intro m k hmk hm
  induction k with
  | zero =>
    obtain rfl := Nat.le_zero.mp hmk
    exact hm
  | succ k ih =>
    rcases Nat.lt_or_ge m (k + 1) with hlt | hge
    · exact sb_foldlM_record facts S v P htick _ (W k) (ih (Nat.lt_succ_iff.mp hlt))
        (W (k + 1)) (hW k).2
    · obtain rfl := Nat.le_antisymm hmk hge
      exact hm

/-- Along a path `W` of `rho`, `v` does not emit both an attestation `a` whose finality pair is at
    height `h` and an attestation `b` whose height pair is the timeout at `h`. -/
theorem Vocabulary.Proofs.HealingSurface.no_timeout_against_finality (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    {v : V} {a b : NamedAttestation V} {ta tb : Time}
    (ha : Restated.Vocabulary.Execution.Run.emits M S rho W v (Object.attest a) ta)
    (hb : Restated.Vocabulary.Execution.Run.emits M S rho W v (Object.attest b) tb)
    {h : Height} {T : BlockId} (hfp : a.finality_pair = some ⟨h, T⟩)
    (hhp : b.erase.height_pair = HeightPair.timeout h) : False := by
  obtain ⟨i, hi, outa, houta, hWa, hai⟩ := ha
  obtain ⟨j, hj, outb, houtb, hWb, hbj⟩ := hb
  have hsafe : Restated.Vocabulary.Proofs.HealingSurface.FinalitySafeAt M
      (W (i + 1) v).record.legacy h T := by
    rw [hWa]
    exact facts.nd.on_tick_emit_finalitySafeAt_of_mem S v (W i v) ta outa houta hai hfp
  have htimeout : (W (j + 1) v).record.legacy.timeout h = true := by
    rw [hWb]
    exact facts.nd.on_tick_emit_timeout_true_of_mem S v (W j v) tb outb houtb hbj hhp
  rcases Nat.lt_trichotomy i j with hij | rfl | hji
  · have hsafe' := sb_path_record facts S rho W hW v
      (fun R => Restated.Vocabulary.Proofs.HealingSurface.FinalitySafeAt M R.legacy h T)
      (fun n t out hout h' => facts.nd.finalitySafeAt_on_tick_emit S v n t h' out hout)
      (i + 1) (j + 1) (by omega) hsafe
    rw [hsafe'.1] at htimeout
    contradiction
  · rw [hsafe.1] at htimeout
    contradiction
  · have htimeout' := sb_path_record facts S rho W hW v
      (fun R => R.legacy.timeout h = true)
      (fun n t out hout h' => facts.nd.timeout_mono_on_tick_emit S v n t h' out hout)
      (j + 1) (i + 1) (by omega) htimeout
    rw [hsafe.1] at htimeout'
    contradiction

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Protocol (Record create_attestation finality_pair height_pair
  record_attestation)
open Internal
open Execution

end

end DecoupledConsensusModel.Sts.Restated
