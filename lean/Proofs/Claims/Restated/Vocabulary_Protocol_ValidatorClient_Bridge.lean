import Proofs.Vocabulary.Protocol.ValidatorClient.Bridge
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Model.Conditions.Vocabulary_Internal_HealingSurface
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Event
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Node
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Records
import Model.Record.Wiring

/-!
# Signing records and the targets an honest validator emits

An honest validator's signing record stays lock-compatible, records the targets and locks of what it
emits, and no honest validator emits two different targets at one height, stated over a model
`M : Record.Model V`.
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

omit [DecidableEq V] [Fintype V] in
private theorem br_erase_finality_pair (a : NamedAttestation V) :
    a.erase.finality_pair = a.finality_pair := by
  unfold NamedAttestation.erase
  rfl

private theorem br_foldlM_record (facts : Record.Facts M) (S : Setup V) (v : V)
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
    cases e with
    | wake u t =>
      have hw'' : w' = Function.update w u (M.wake (w u)) := hw'
      subst hw''
      by_cases hu : u = v
      · subst u
        rw [Function.update_self, (facts.nd.wake_st_record _).2]
        exact hw
      · rw [Function.update_of_ne (Ne.symm hu)]
        exact hw
    | tick u t =>
      simp only [Record.worldStepOf, Set.mem_setOf_eq] at hw'
      rcases hw' with ⟨out, hout, rfl⟩ | ⟨-, rfl⟩
      · by_cases hu : u = v
        · subst u
          rw [Function.update_self]
          exact htick (w v) t out hout hw
        · rw [Function.update_of_ne (Ne.symm hu)]
          exact hw
      · exact hw
    | deliver u o t =>
      simp only [Record.worldStepOf, Set.mem_setOf_eq] at hw'
      rcases hw' with ⟨n', hn', rfl⟩ | ⟨-, rfl⟩
      · by_cases hu : u = v
        · subst u
          rw [Function.update_self, facts.nd.process_record S (w v) o n' hn']
          exact hw
        · rw [Function.update_of_ne (Ne.symm hu)]
          exact hw
      · exact hw

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution

/-- For every `i` and every world `w` before the `i`-th event of `ρ`, `v`'s signing record in `w` is
    lock-compatible. -/
theorem Vocabulary.Proofs.HealingSurface.stateBefore_lockCompatible (facts : Record.Facts M) (S : Setup V) (ρ : Record.Run V) (v : V) :
    ∀ i : Nat, ∀ w ∈ Record.stateBeforeOf M S ρ i,
      Restated.Vocabulary.Proofs.Records.LockCompatible M (w v).record.legacy := by
  intro i w hw
  refine br_foldlM_record facts S v
    (fun R => Restated.Vocabulary.Proofs.Records.LockCompatible M R.legacy)
    (fun n t out hout h => facts.nd.lockCompatible_on_tick_emit S v n t h out hout) _ _ ?_ w hw
  intro h T hl
  change (M.initial S v).record.legacy.lock h = some T at hl
  rw [facts.nd.initial_record_legacy_lock S v h] at hl
  exact absurd hl (Option.some_ne_none T).symm

/-- When the `i`-th event of `ρ` is `v`'s tick at `t` and `a`'s height pair is the target `(h, T)`,
    for every world `w₁` before that event and every outcome `out` of the tick from `v`'s node state
    in `w₁` that sends `a`, the signing record of `out` holds the target `T` at height `h`. -/
theorem Vocabulary.Proofs.HealingSurface.emits_height_target_recorded (facts : Record.Facts M) (S : Setup V) (ρ : Record.Run V)
    {v : V} {t : Time} {i : Nat}
    {a : NamedAttestation V} (hi : ρ.events[i]? = some (.tick v t))
    {h : Height} {T : BlockId} (hT : a.erase.height_pair = HeightPair.target h T) :
    ∀ w₁ ∈ Record.stateBeforeOf M S ρ i,
    ∀ out ∈ Restated.Vocabulary.Execution.on_tick_emit M S v (w₁ v) t,
      NamedObject.attest a ∈ out.2 → out.1.record.legacy.target h = some T := by
  intro w₁ hw₁ out hout ha
  obtain ⟨r, c, f, h_j, J, h_F, herase, hrec⟩ :=
    facts.nd.on_tick_emit_attestation_created S v (w₁ v) t
      (facts.ndRun.stateBeforeOf_runs_as S ρ i w₁ hw₁ v) out hout ha
  rw [hrec]
  exact facts.vc.create_attestation_saves (w₁ v).record.legacy
    (Restated.Vocabulary.Proofs.HealingSurface.stateBefore_lockCompatible facts S ρ v i w₁ hw₁)
    (S.node v).val_index r c f h_j J h_F (by rw [← herase]; exact hT)

/-- When the `i`-th event of `ρ` is `v`'s tick at `t` and `a`'s finality pair is `(h, J)`, for every
    world `w₁` before that event and every outcome `out` of the tick from `v`'s node state in `w₁`
    that sends `a`, the signing record of `out` holds the lock `J` at height `h`. -/
theorem Vocabulary.Proofs.HealingSurface.emits_finality_locked (facts : Record.Facts M) (S : Setup V) (ρ : Record.Run V)
    {v : V} {t : Time} {i : Nat}
    {a : NamedAttestation V} (hi : ρ.events[i]? = some (.tick v t))
    {h : Height} {J : BlockId} (hfp : a.finality_pair = some ⟨h, J⟩) :
    ∀ w₁ ∈ Record.stateBeforeOf M S ρ i,
    ∀ out ∈ Restated.Vocabulary.Execution.on_tick_emit M S v (w₁ v) t,
      NamedObject.attest a ∈ out.2 → out.1.record.legacy.lock h = some J := by
  intro w₁ hw₁ out hout ha
  obtain ⟨r, c, f, h_j, T, h_F, herase, hrec⟩ :=
    facts.nd.on_tick_emit_attestation_created S v (w₁ v) t
      (facts.ndRun.stateBeforeOf_runs_as S ρ i w₁ hw₁ v) out hout ha
  have hfp' : M.finality_pair (w₁ v).record.legacy h_j T h_F = some ⟨h, J⟩ := by
    rw [← facts.vc.create_attestation_snd_finality_pair (w₁ v).record.legacy (S.node v).val_index
      r c f h_j T h_F, ← herase, br_erase_finality_pair]
    exact hfp
  rw [hrec, facts.vc.create_attestation_fst, facts.vc.record_attestation_lock_eq_own_lock,
    facts.vc.create_attestation_snd_finality_pair, hfp', facts.vc.own_lock_some_self]

private theorem br_marks_agree {R : M.NR}
    (hla : Restated.Vocabulary.Proofs.Records.LockCompatible M R.legacy) {h : Height}
    {T T' : BlockId}
    (hT : R.legacy.target h = some T ∨ R.legacy.lock h = some T)
    (hT' : R.legacy.target h = some T' ∨ R.legacy.lock h = some T') : T = T' := by
  rcases hT with hT | hT <;> rcases hT' with hT' | hT'
  · rw [hT] at hT'
    exact Option.some_inj.mp hT'
  · rcases (hla h T' hT').2 with hn | hs
    · rw [hT] at hn
      contradiction
    · rw [hT] at hs
      exact Option.some_inj.mp hs
  · rcases (hla h T hT).2 with hn | hs
    · rw [hT'] at hn
      contradiction
    · rw [hT'] at hs
      exact (Option.some_inj.mp hs).symm
  · rw [hT] at hT'
    exact Option.some_inj.mp hT'

private theorem br_mark_of_emit (facts : Record.Facts M) (S : Setup V) (ρ : Record.Run V)
    {v : V} {t : Time} {i : Nat} {a : NamedAttestation V} (hi : ρ.events[i]? = some (.tick v t))
    {h : Height} {T : BlockId} (hT : T ∈ targetsAt a.erase h)
    {w₁ : V → M.N} (hw₁ : w₁ ∈ Record.stateBeforeOf M S ρ i)
    {out : M.N × List (NamedObject V)} (hout : out ∈ Restated.Vocabulary.Execution.on_tick_emit M S v (w₁ v) t)
    (ha : NamedObject.attest a ∈ out.2) :
    out.1.record.legacy.target h = some T ∨ out.1.record.legacy.lock h = some T := by
  rcases hT with hheight | hfinality
  · exact Or.inl (Restated.Vocabulary.Proofs.HealingSurface.emits_height_target_recorded facts S ρ hi
      hheight w₁ hw₁ out hout ha)
  · exact Or.inr (Restated.Vocabulary.Proofs.HealingSurface.emits_finality_locked facts S ρ hi
      ((br_erase_finality_pair a).symm.trans hfinality) w₁ hw₁ out hout ha)

private theorem br_path_mark (facts : Record.Facts M) (S : Setup V) (ρ : Record.Run V)
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S ρ W) (v : V)
    {h : Height} {T : BlockId} {k : Nat}
    (hk : (W k v).record.legacy.target h = some T ∨ (W k v).record.legacy.lock h = some T) :
    ∀ n : Nat, k ≤ n →
      (W n v).record.legacy.target h = some T ∨ (W n v).record.legacy.lock h = some T := by
  intro n hkn
  induction n, hkn using Nat.le_induction with
  | base => exact hk
  | succ n _ ih =>
    exact br_foldlM_record facts S v (fun R => R.legacy.target h = some T ∨ R.legacy.lock h = some T)
      (fun n₀ t₀ o ho hR => hR.elim
        (fun hR => Or.inl (facts.nd.target_mono_on_tick_emit S v n₀ t₀ hR o ho))
        (fun hR => Or.inr (facts.nd.lock_mono_on_tick_emit S v n₀ t₀ hR o ho)))
      _ (W n) ih (W (n + 1)) (hW n).2

private theorem br_no_double_ordered (facts : Record.Facts M) (S : Setup V) (ρ : Record.Run V)
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S ρ W)
    {v : V} {a a' : NamedAttestation V} {t t' : Time} {i j : Nat} (hij : i ≤ j)
    (hi : ρ.events[i]? = some (.tick v t))
    {out : M.N × List (NamedObject V)} (hout : M.tick S v (W i v) t ⇢ out)
    (hWi : W (i + 1) v = out.1) (ha : NamedObject.attest a ∈ out.2)
    (hj : ρ.events[j]? = some (.tick v t'))
    {out' : M.N × List (NamedObject V)} (hout' : M.tick S v (W j v) t' ⇢ out')
    (hWj : W (j + 1) v = out'.1) (ha' : NamedObject.attest a' ∈ out'.2)
    {h : Height} {T T' : BlockId} (hT : T ∈ targetsAt a.erase h) (hT' : T' ∈ targetsAt a'.erase h) :
    T = T' := by
  have hm := br_mark_of_emit facts S ρ hi hT (hW i).1 hout ha
  rw [← hWi] at hm
  have hm₄ := br_path_mark facts S ρ hW v hm (j + 1) (Nat.succ_le_succ hij)
  rw [hWj] at hm₄
  have hm' := br_mark_of_emit facts S ρ hj hT' (hW j).1 hout' ha'
  exact br_marks_agree (facts.nd.lockCompatible_on_tick_emit S v (W j v) t'
    (Restated.Vocabulary.Proofs.HealingSurface.stateBefore_lockCompatible facts S ρ v j (W j) (hW j).1)
    out' hout') hm₄ hm'

/-- For every path `W` of `ρ`, no honest validator emits along `W` two attestations carrying
    different targets at one height. -/
theorem Vocabulary.Proofs.HealingSurface.honestNoDoubleTarget (facts : Record.Facts M) (S : Setup V) (ρ : Record.Run V) :
    ∀ W : Nat → V → M.N, Restated.Vocabulary.Execution.NamedRun.OnePath M S ρ W →
      Restated.Vocabulary.Internal.HealingSurface.HonestNoDoubleTarget M S ρ W := by
  rintro W hW v - a a' t t' ⟨i, hi, out, hout, hWi, ha⟩ ⟨j, hj, out', hout', hWj, ha'⟩ h T T' hT hT'
  rcases le_total i j with hij | hji
  · exact br_no_double_ordered facts S ρ hW hij hi hout hWi ha hj hout' hWj ha' hT hT'
  · exact (br_no_double_ordered facts S ρ hW hji hj hout' hWj ha' hi hout hWi ha hT' hT).symm

end

end DecoupledConsensusModel.Sts.Restated
