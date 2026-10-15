import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.RunAll
import Proofs.Claims.Restated.Vocabulary_Protocol_ValidatorClient_Bridge
import Proofs.Claims.Restated.Vocabulary_Protocol_ValidatorClient_SlashableBound
import Model.Conditions.RunAll
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Record.Wiring

/-!
# Honest validators are never slashed

Theorems over a model `M : Record.Model V` with facts `facts : Record.Facts M`: along a path of a
run, two attestations an honest validator emits never form slashing evidence, and everything the run
processes is in the sent log.
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

/-- Along a path `W` of `rho`, two attestations an honest validator `v` emitted never name two
    different targets at the same height. -/
theorem emitted_targets_eq_of_honest (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) {v : V}
    (hhon : v ∈ rho.honest) {a b : NamedAttestation V} {ta tb : Int}
    (ha : Restated.Vocabulary.Execution.NamedRun.emits M S rho W v (.attest a) ta)
    (hb : Restated.Vocabulary.Execution.NamedRun.emits M S rho W v (.attest b) tb) {h : Height} {T U : BlockId}
    (hT : T ∈ Internal.targetsAt a.erase h) (hU : U ∈ Internal.targetsAt b.erase h) :
    T = U :=
  Restated.Vocabulary.Proofs.HealingSurface.honestNoDoubleTarget facts S rho W hW v hhon a b ta tb ha hb h T U hT hU

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Along a path `W` of `rho`, if an honest `v` emits `a` with finality pair `p` and emits `b`, then
    `b`'s height pair does not conflict with `p`. -/
theorem conflictsWithFinality_false_of_honest (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) {v : V}
    (hhon : v ∈ rho.honest) {a b : NamedAttestation V} {ta tb : Int}
    (ha : Restated.Vocabulary.Execution.NamedRun.emits M S rho W v (.attest a) ta)
    (hb : Restated.Vocabulary.Execution.NamedRun.emits M S rho W v (.attest b) tb) {p : FinalityPair}
    (hfp : a.finality_pair = some p) :
    M.conflictsWithFinality b.erase.height_pair p = false := by
  obtain ⟨h, T⟩ := p
  refine facts.cs.conflictsWithFinality_eq_false_of _ _ ?_ ?_
  · intro hhp
    exact Restated.Vocabulary.Proofs.HealingSurface.no_timeout_against_finality facts S rho W hW ha hb hfp hhp
  · intro U hhp
    exact (Restated.emitted_targets_eq_of_honest facts S W hW hhon ha hb
      (Or.inr (show a.erase.finality_pair = some ⟨h, T⟩ from
        (namedAttestation_erase_finality_pair a).trans hfp)) (Or.inl hhp)).symm

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Along a path `W` of `rho`, the height pairs of two attestations an honest `v` emits do not form
    E2 evidence. -/
theorem e2Fields_false_of_honest (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) {v : V}
    (hhon : v ∈ rho.honest) {a b : NamedAttestation V} {ta tb : Int}
    (ha : Restated.Vocabulary.Execution.NamedRun.emits M S rho W v (.attest a) ta)
    (hb : Restated.Vocabulary.Execution.NamedRun.emits M S rho W v (.attest b) tb) :
    M.e2Fields a.erase b.erase = false := by
  refine facts.cs.e2Fields_eq_false_of _ _ ?_
  intro h T U hpa hpb
  exact Restated.emitted_targets_eq_of_honest facts S W hW hhon ha hb (Or.inl hpa) (Or.inl hpb)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Along a path `W` of `rho`, any two attestations an honest `v` emits do not form E1 or E2
    evidence. -/
theorem emissionVoteSafety_of_honest (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (v : V)
    (hhon : v ∈ rho.honest) (a b : NamedAttestation V)
    (ha : ∃ ta : Int, Restated.Vocabulary.Execution.NamedRun.emits M S rho W v (.attest a) ta)
    (hb : ∃ tb : Int, Restated.Vocabulary.Execution.NamedRun.emits M S rho W v (.attest b) tb) :
    ¬ M.Slashable a.erase b.erase := by
  obtain ⟨ta, ha⟩ := ha
  obtain ⟨tb, hb⟩ := hb
  have he1 : M.e1Fields a.erase b.erase = false :=
    facts.csAdded.e1Fields_eq_false_of _ _
      (fun _ hfa => Restated.conflictsWithFinality_false_of_honest facts S W hW hhon ha hb
        ((namedAttestation_erase_finality_pair a).symm.trans hfa))
      (fun _ hfb => Restated.conflictsWithFinality_false_of_honest facts S W hW hhon hb ha
        ((namedAttestation_erase_finality_pair b).symm.trans hfb))
  have he2 := Restated.e2Fields_false_of_honest facts S W hW hhon ha hb
  exact (facts.csAdded.not_Slashable_iff _ _).2 (facts.csAdded.slashable_eq_false_of_fields _ _ he1 he2)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If, along the path `Restated.runAllPath M S Sched x v n` that `x` follows, the run of the first
    `n` steps processes `o` at `v₀` at `t`, then some step `k ≤ n` has a signed message carrying `o`
    in its sent log `x[k].sent`, and the time of step `k` is `t`. -/
theorem mem_sent_of_processes (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) (n : Nat) {v₀ : V}
    {o : NamedObject V} {t : Int}
    (hproc : Restated.Vocabulary.Execution.NamedRun.processes M (Setup.alwaysAwake S)
      (Restated.runAll M S Sched x v n) (Restated.runAllPath M S Sched x v n) v₀ o t) :
    ∃ k ≤ n, (∃ sm : SignedMsg V (NamedObject V), sm ∈ x[k].sent ∧ sm.msg = o) ∧
      (x[k].time : Int) = t := by
  rcases hproc with ⟨idx, hidx, out, hout, hst, ho⟩ | ⟨idx, hidx⟩
  ·
    obtain ⟨k, hk, hmem, hcase⟩ := Restated.runAllPath_at_event facts S Sched x v n idx hidx
    obtain ⟨τ, hlbl, hτ, haw, hdvd⟩ := Restated.tickAllAwake_of_mem_actionEventsOf hmem
    rcases hcase with ⟨t', he', -, -⟩ | ⟨t', he', hb, ha⟩ | ⟨o', t', he', -, -⟩
    · cases he'
    swap
    · cases he'
    obtain rfl : t = t' := (Record.Event.tick.inj he').2
    have hb' : Restated.runAllPath M S Sched x v n idx v₀ = Record.wakeStage M Sched t x[k] v₀ := hb
    have ha' : Restated.runAllPath M S Sched x v n (idx + 1) v₀ = x[k + 1][v₀].st := ha
    have haw' : v₀ ∈ Sched.awake (τ : Int) \ Sched.adv (τ : Int) := haw
    have hout' : M.tick (Setup.alwaysAwake S) v₀ (Record.wakeStage M Sched (τ : Int) x[k] v₀)
        (τ : Int) ⇢ out := by
      rw [hτ, ← hb']
      exact hout
    have hst' : x[k + 1][v₀].st = out.1 := by rw [← ha']; exact hst
    refine ⟨k + 1, hk, ⟨⟨v₀, o⟩, Restated.mem_sent_of_tick_of_state facts S Sched x hlbl haw'
      hdvd (fun out₁ out₂ h₁ h₂ h12 =>
        facts.nd.tick_send_eq_of_state (Setup.alwaysAwake S) v₀ _ _ out₁ out₂ h₁ h₂ h12)
      hout' hst' ho, rfl⟩, ?_⟩
    rw [(Restated.tickAllAwake_time facts S Sched x hlbl).2, hτ]
  ·
    obtain ⟨k, hk, hmem⟩ :=
      Restated.exists_step_of_mem_runEvents facts S Sched x n (List.mem_of_getElem? hidx)
    obtain ⟨m, hlbl, hmsg, ht⟩ := Restated.deliver_of_mem_actionEventsOf hmem
    have hs : AtomicStep (Record.protocolOf M S) Sched (x.lbl k) x[k] x[k + 1] := x.step k
    rw [hlbl] at hs
    exact ⟨k, Nat.le_of_lt hk, ⟨m, hs.1.1, hmsg⟩, ht.symm⟩

end

end DecoupledConsensusModel.Sts.Restated
