import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13beRoute3_22
import Proofs.Claims.Restated.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_43
import Model.Conditions.RunAll
import Model.Conditions.RunVocabulary
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedReceiptCalls
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_43

/-!
# Cutting a run at an instant

The cut of the run of the first `n` sts steps at an instant `T`, and the transfer of emissions,
acceptances, handlings and processings between a run, its cut, and a run extending it, stated over a
model `M : Record.Model V` and its facts `facts : Record.Facts M`.
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
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- If `0 ≤ T ≤ x[n].time`, some step count `m ≤ n` has `x[m]` at `T` and every event of the steps
    `m` to `n - 1` strictly after `T`: `CutAt M S Sched x m n T` holds. -/
theorem exists_cutAt (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    {n : Nat} {T : Int} (hT0 : 0 ≤ T) (hTn : T ≤ (x[n].time : Int)) :
    ∃ m : Nat, Restated.CutAt M S Sched x m n T := by
  classical
  let P : Nat → Prop := fun m => (x[m].time : Int) ≤ T
  let m := Nat.findGreatest P n
  have hle : m ≤ n := Nat.findGreatest_le n
  have h0 : P 0 := by
    show ((x[0].time : Nat) : Int) ≤ T
    have : x[0].time = 0 := x.init.1
    rw [this]; exact_mod_cast hT0
  have hPm : P m := Nat.findGreatest_spec (Nat.zero_le n) h0
  refine ⟨m, hle, ?_, ?_⟩
  · rcases Nat.lt_or_ge m n with hlt | hge
    · have hnot : ¬ P (m + 1) := Nat.findGreatest_is_greatest (Nat.lt_succ_self m) hlt
      have hstep := atomic_time_stepwise x m
      simp only [P, not_le] at hnot hPm
      rcases hstep with h | h
      · rw [h] at hnot; omega
      · rw [h] at hnot; push_cast at hnot; omega
    · have hmn : m = n := le_antisymm hle hge
      simp only [P] at hPm
      rw [hmn] at hPm ⊢
      exact le_antisymm hPm hTn
  · rcases Nat.lt_or_ge m n with hlt | hge
    · have hnot : ¬ P (m + 1) := Nat.findGreatest_is_greatest (Nat.lt_succ_self m) hlt
      simp only [P, not_le] at hnot
      obtain ⟨l, hl, hlate⟩ := Restated.runEvents_append_late facts S Sched x hle
      refine ⟨l, hl, fun e he => ?_⟩
      rw [namedEvent_time_eq]
      exact lt_of_lt_of_le hnot (hlate e he)
    · have hmn : m = n := le_antisymm hle hge
      refine ⟨[], by rw [hmn, List.append_nil], fun e he => absurd he List.not_mem_nil⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- For a cut `CutAt M S Sched x m n T`, removing from the run of the first `n` steps every event
    after `T` and setting the horizon to `T` gives the run of the first `m` steps, whatever honest
    sets the two runs declare. -/
theorem runAll_eq_cutRun (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V) {m n : Nat} {T : Int} (hc : Restated.CutAt M S Sched x m n T) (X X' : Finset V) :
    ({ Restated.runAll M S Sched x v m with honest := X } : Record.Run V) =
      cutRun ({ Restated.runAll M S Sched x v n with honest := X' } : Record.Run V) X T := by
  obtain ⟨l, hl, hlate⟩ := hc.late
  have hin : ∀ e ∈ Restated.runEvents M S Sched x m, Record.Event.time e ≤ T := fun e he => by
    rw [← hc.time_eq]
    exact (Restated.in_horizon_runAll_withHonest facts S Sched x v X m e he).2
  have hev : (Restated.runEvents M S Sched x n).filter (fun e => decide (Record.Event.time e ≤ T)) =
      Restated.runEvents M S Sched x m := by
    rw [hl, List.filter_append, List.filter_eq_self.2 (fun e he => by simpa using hin e he),
      List.filter_eq_nil_iff.2 (fun e he => by simpa using hlate e he), List.append_nil]
  unfold cutRun
  show (⟨X, (x[m].time : Int), Restated.runEvents M S Sched x m⟩ : Record.Run V) =
    ⟨X, T, (Restated.runEvents M S Sched x n).filter (fun e => decide (Record.Event.time e ≤ T))⟩
  rw [hev, hc.time_eq]

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- For `0 ≤ T ≤ x[n].time`, the events of the run of the first `n` sts steps, with any honest set,
    are its events up to `T` followed by events after `T`. -/
theorem cutSuffix_runAll (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V) (n : Nat) (X : Finset V) {T : Int} (hT0 : 0 ≤ T) (hTn : T ≤ (x[n].time : Int)) :
    CutSuffix ({ Restated.runAll M S Sched x v n with honest := X } : Record.Run V) T := by
  obtain ⟨m, hc⟩ := Restated.exists_cutAt facts S Sched x hT0 hTn
  obtain ⟨l, hl, hlate⟩ := hc.late
  have hev := congrArg Record.Run.events (Restated.runAll_eq_cutRun facts S Sched x v hc X X)
  refine ⟨l, ?_, hlate⟩
  show Restated.runEvents M S Sched x n =
    (cutRun ({ Restated.runAll M S Sched x v n with honest := X } : Record.Run V) X T).events ++ l
  exact hl.trans (congrArg (· ++ l) hev)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- If `rho`'s events are a prefix of `rho'`'s and `i` is an index of `rho`, then, along any path
    `W`, `v` handles `o` at `t` at index `i` of `rho'` exactly when it does at index `i` of `rho`. -/
theorem actualHandlesAt_iff_of_prefix (facts : Record.Facts M) (S : Setup V) {rho rho' : Record.Run V}
    (h : rho.events <+: rho'.events) {i : Nat} (hi : i < rho.events.length)
    {W : Nat → V → M.N} {v : V} {o : NamedObject V} {t : Int} :
    Restated.Vocabulary.Execution.NamedRun.actualHandlesAt M S rho' W i v o t ↔
      Restated.Vocabulary.Execution.NamedRun.actualHandlesAt M S rho W i v o t := by
  have he := getElem?_of_prefix h hi
  cases o <;>
    simp only [Restated.Vocabulary.Execution.NamedRun.actualHandlesAt, Restated.Vocabulary.Execution.NamedRun.actualHandlesAtIndex,
      Restated.Vocabulary.Execution.NamedRun.processesAtIndexAlong, Restated.Vocabulary.Execution.NamedReceiptCalls.carriedGoldfishAt,
      Restated.Vocabulary.Execution.NamedReceiptCalls.carriedAttestationAt, Restated.Vocabulary.Execution.NamedReceiptCalls.blockCallAt, he]

/-- If `W i = W' i` and `W (i + 1) = W' (i + 1)`, then `v` handles `o` at `t` at the `i`-th event of
    `rho` along `W` exactly when it does along `W'`. -/
theorem actualHandlesAt_congr_path (S : Setup V) (rho : Record.Run V) {W W' : Nat → V → M.N}
    {i : Nat} (h0 : W i = W' i) (h1 : W (i + 1) = W' (i + 1)) {v : V} {o : NamedObject V}
    {t : Int} :
    Restated.Vocabulary.Execution.NamedRun.actualHandlesAt M S rho W i v o t ↔
      Restated.Vocabulary.Execution.NamedRun.actualHandlesAt M S rho W' i v o t := by
  cases o <;>
    simp only [Restated.Vocabulary.Execution.NamedRun.actualHandlesAt, Restated.Vocabulary.Execution.NamedRun.actualHandlesAtIndex,
      Restated.Vocabulary.Execution.NamedRun.processesAtIndexAlong, Restated.Vocabulary.Execution.NamedReceiptCalls.carriedGoldfishAt,
      Restated.Vocabulary.Execution.NamedReceiptCalls.carriedAttestationAt, Restated.Vocabulary.Execution.NamedReceiptCalls.blockCallAt, h0, h1]

/-- If `W i = W' i` and `W (i + 1) = W' (i + 1)`, then `v` accepts `o` at `t` at the `i`-th event of
    `rho` along `W` exactly when it does along `W'`. -/
theorem acceptsAt_congr_path (S : Setup V) (rho : Record.Run V) {W W' : Nat → V → M.N}
    {i : Nat} (h0 : W i = W' i) (h1 : W (i + 1) = W' (i + 1)) {v : V} {o : NamedObject V}
    {t : Int} :
    Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho W i v o t ↔
      Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho W' i v o t := by
  unfold Restated.Vocabulary.Execution.NamedRun.acceptsAt
  rw [Restated.actualHandlesAt_congr_path S rho h0 h1, h0, h1]

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- If `rho`'s events are a prefix of `rho'`'s and `i` is an index of `rho`, then, along any path
    `W`, `v` accepts `o` at `t` at index `i` of `rho'` exactly when it does at index `i` of `rho`. -/
theorem acceptsAt_iff_of_prefix (facts : Record.Facts M) (S : Setup V) {rho rho' : Record.Run V}
    (h : rho.events <+: rho'.events) {i : Nat} (hi : i < rho.events.length)
    {W : Nat → V → M.N} {v : V} {o : NamedObject V} {t : Int} :
    Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho' W i v o t ↔
      Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho W i v o t := by
  unfold Restated.Vocabulary.Execution.NamedRun.acceptsAt
  rw [Restated.actualHandlesAt_iff_of_prefix facts S h hi]

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- Under `CutSuffix rho T`, along any path `W`, whatever `w` emits at an instant `t ≤ T` in `rho`
    it emits at `t` in `cutRun rho X T`. -/
theorem CutSuffix.emits (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V} {T : Int}
    (hsuf : CutSuffix rho T) (X : Finset V) {W : Nat → V → M.N} {w : V} {o : NamedObject V}
    {t : Int} (ht : t ≤ T)
    (he : Restated.Vocabulary.Execution.NamedRun.emits M S rho W w o t) :
    Restated.Vocabulary.Execution.NamedRun.emits M S (cutRun rho X T) W w o t := by
  obtain ⟨i, hi, ho⟩ := he
  obtain ⟨-, hi'⟩ := hsuf.getElem? X hi ht
  exact ⟨i, hi', ho⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- Under `CutSuffix rho T`, along any path `W`, whatever `w` emits in `cutRun rho X T` it emits in
    `rho`, at the same instant. -/
theorem CutSuffix.emits_of_cut (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V} {T : Int}
    (hsuf : CutSuffix rho T) (X : Finset V) {W : Nat → V → M.N} {w : V} {o : NamedObject V}
    {t : Int}
    (he : Restated.Vocabulary.Execution.NamedRun.emits M S (cutRun rho X T) W w o t) :
    Restated.Vocabulary.Execution.NamedRun.emits M S rho W w o t :=
  Restated.emits_of_prefix facts S (hsuf.prefix X) he

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- Under `CutSuffix rho T`, along any path `W`, if `v` accepts `o` at index `i` of `rho` at an
    instant `t ≤ T`, it accepts `o` at index `i` of `cutRun rho X T` at `t`. -/
theorem CutSuffix.acceptsAt (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V} {T : Int}
    (hsuf : CutSuffix rho T) (X : Finset V) {W : Nat → V → M.N} {i : Nat} {v : V}
    {o : NamedObject V} {t : Int} (ht : t ≤ T)
    (hacc : Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho W i v o t) :
    i < (cutRun rho X T).events.length ∧
      Restated.Vocabulary.Execution.NamedRun.acceptsAt M S (cutRun rho X T) W i v o t := by
  obtain ⟨-, e, he, -, hte⟩ := hacc.1
  obtain ⟨hlt, -⟩ := hsuf.getElem? X he (hte ▸ ht)
  exact ⟨hlt, (Restated.acceptsAt_iff_of_prefix facts S (hsuf.prefix X) hlt).1 hacc⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- Under `CutSuffix rho T`, along any path `W`, if `v` handles `o` at index `i` of
    `cutRun rho X T`, it handles `o` at index `i` of `rho`, at the same instant. -/
theorem CutSuffix.actualHandlesAt_of_cut (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V} {T : Int}
    (hsuf : CutSuffix rho T) (X : Finset V) {W : Nat → V → M.N} {i : Nat} {v : V}
    {o : NamedObject V} {t : Int}
    (hh : Restated.Vocabulary.Execution.NamedRun.actualHandlesAt M S (cutRun rho X T) W i v o t) :
    Restated.Vocabulary.Execution.NamedRun.actualHandlesAt M S rho W i v o t := by
  obtain ⟨e, he, -, -⟩ := hh.2
  exact (Restated.actualHandlesAt_iff_of_prefix facts S (hsuf.prefix X)
    (List.getElem?_eq_some_iff.1 he).1).2 hh

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- Under `CutSuffix rho T`, along any path `W`, if `v` processes `o` at an instant `t ≤ T` in
    `rho`, it processes `o` at `t` in `cutRun rho X T`. -/
theorem CutSuffix.processes (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V} {T : Int}
    (hsuf : CutSuffix rho T) (X : Finset V) {W : Nat → V → M.N} {v : V} {o : NamedObject V}
    {t : Int} (ht : t ≤ T)
    (hp : Restated.Vocabulary.Execution.NamedRun.processes M S rho W v o t) :
    Restated.Vocabulary.Execution.NamedRun.processes M S (cutRun rho X T) W v o t := by
  rcases hp with he | ⟨i, hi⟩
  · exact Or.inl ((Restated.CutSuffix.emits facts S hsuf X ht he))
  · exact Or.inr ⟨i, (hsuf.getElem? X hi ht).2⟩

end

end DecoupledConsensusModel.Sts.Restated
