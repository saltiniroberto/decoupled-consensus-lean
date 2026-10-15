import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_Protocol_ValidatorClient_Bridge
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Node
import Model.Record.Wiring

/-!
# Where a recorded lock comes from

A lock in a validator's signing record comes from an attestation that validator emitted at an
earlier tick, stated over a model `M : Record.Model V`.
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
open Internal
open Execution
open Internal.HealingSurface

private theorem mr_mem_foldlM_singleton (S : Setup V) (w w₂ : V → M.N) (e : Record.Event V) :
    w₂ ∈ [e].foldlM (Record.worldStepOf M S) w ↔ w₂ ∈ Record.worldStepOf M S w e := by
  rw [List.foldlM_cons, Set.bind_def]
  constructor
  · intro h
    obtain ⟨w', hw', h2⟩ := Set.mem_iUnion₂.mp h
    obtain rfl := Set.mem_singleton_iff.mp h2
    exact hw'
  · intro h
    exact Set.mem_iUnion₂.mpr ⟨w₂, h, Set.mem_singleton w₂⟩

private theorem mr_step_record (facts : Record.Facts M) (S : Setup V) (w w₂ : V → M.N)
    (e : Record.Event V) (v : V) (hw₂ : w₂ ∈ Record.worldStepOf M S w e)
    (hne : ∀ t : Time, e ≠ .tick v t) : (w₂ v).record = (w v).record := by
  cases e with
  | wake u t =>
    obtain rfl : w₂ = Function.update w u (M.wake (w u)) := hw₂
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

private theorem mr_foldlM_record (facts : Record.Facts M) (S : Setup V) (v : V)
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
    · rw [mr_step_record facts S w w' e v hw' (fun t h => he ⟨t, h⟩)]
      exact hw

/-- For every world `w₂` before the `n`-th event of `rho` in which `v`'s signing record holds the
    lock `T` at height `H`, some event `i < n` is `v`'s tick at some `t`, and some world `w₁` before
    event `i` and some outcome `out` of that tick from `v`'s node state in `w₁` send an attestation
    `a` whose finality pair is `(H, T)`, with `w₂` reached from the world that outcome leaves by the
    events `i + 1` to `n - 1`. -/
theorem Vocabulary.Proofs.HealingSurface.recordLock_finalityEmission_before_migration (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (v : V) :
    ∀ (n : Nat) {H : Height} {T : BlockId}, ∀ w₂ ∈ Record.stateBeforeOf M S rho n,
      (w₂ v).record.legacy.lock H = some T →
        ∃ (i : Nat), i < n ∧ ∃ (t : Time) (a : NamedAttestation V),
          rho.events[i]? = some (.tick v t) ∧
          ∃ w₁ ∈ Record.stateBeforeOf M S rho i,
          ∃ out ∈ Restated.Vocabulary.Execution.on_tick_emit M S v (w₁ v) t,
            NamedObject.attest a ∈ out.2 ∧ a.finality_pair = some ⟨H, T⟩ ∧
            w₂ ∈ ((rho.events.drop (i + 1)).take (n - (i + 1))).foldlM (Record.worldStepOf M S)
              (Function.update w₁ v out.1) := by
  intro n
  induction n with
  | zero =>
      intro H T w₂ hw₂ hlock
      have h0 : w₂ = fun u => M.initial S u := Set.mem_singleton_iff.mp hw₂
      subst h0
      change (M.initial S v).record.legacy.lock H = some T at hlock
      rw [facts.nd.initial_record_legacy_lock S v H] at hlock
      cases hlock
  | succ n ih =>
      intro H T w₂ hw₂ hlock
      unfold Record.stateBeforeOf at hw₂
      rw [List.take_add_one, List.foldlM_append, Set.bind_def] at hw₂
      obtain ⟨w₁, hw₁, h2⟩ := Set.mem_iUnion₂.mp hw₂
      cases hpre : (w₁ v).record.legacy.lock H with
      | some X =>
          have hmono : (w₂ v).record.legacy.lock H = some X :=
            mr_foldlM_record facts S v (fun R => R.legacy.lock H = some X)
              (fun n t out hout h' => facts.nd.lock_mono_on_tick_emit S v n t h' out hout)
              _ w₁ hpre w₂ h2
          have hXT : X = T := by
            rw [hlock] at hmono
            exact (Option.some.inj hmono).symm
          subst X
          obtain ⟨i, hi, t, a, hev, w₀, hw₀, out, hout, ha, hpair, hpath⟩ := ih w₁ hw₁ hpre
          refine ⟨i, Nat.lt_succ_of_lt hi, t, a, hev, w₀, hw₀, out, hout, ha, hpair, ?_⟩
          have hk : n + 1 - (i + 1) = n - (i + 1) + 1 := by omega
          have hidx : i + 1 + (n - (i + 1)) = n := by omega
          rw [hk, List.take_add_one, List.getElem?_drop, hidx, List.foldlM_append, Set.bind_def]
          exact Set.mem_iUnion₂.mpr ⟨w₁, hpath, h2⟩
      | none =>
          rcases hevent : rho.events[n]? with _ | e
          · rw [hevent] at h2
            have hw : w₂ = w₁ := Set.mem_singleton_iff.mp h2
            rw [hw, hpre] at hlock
            cases hlock
          · rw [hevent] at h2
            have h2' : w₂ ∈ Record.worldStepOf M S w₁ e := (mr_mem_foldlM_singleton S w₁ w₂ e).1 h2
            by_cases he : ∃ t, e = .tick v t
            · obtain ⟨t, rfl⟩ := he
              simp only [Record.worldStepOf, Set.mem_setOf_eq] at h2'
              rcases h2' with ⟨out, hout, rfl⟩ | ⟨-, rfl⟩
              · rw [Function.update_self] at hlock
                obtain ⟨a, ha, hpair⟩ :=
                  facts.nd.on_tick_emit_lock_introduced S v (w₁ v) t hpre out hout hlock
                refine ⟨n, Nat.lt_succ_self n, t, a, hevent, w₁, hw₁, out, hout, ha, hpair, ?_⟩
                rw [Nat.sub_self, List.take_zero]
                exact Set.mem_singleton _
              · rw [hpre] at hlock
                cases hlock
            · rw [mr_step_record facts S w₁ w₂ e v h2' (fun t h => he ⟨t, h⟩), hpre] at hlock
              cases hlock

end

end DecoupledConsensusModel.Sts.Restated
