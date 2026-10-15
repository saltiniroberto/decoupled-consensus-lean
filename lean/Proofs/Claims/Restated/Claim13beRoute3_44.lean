import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13beRoute3_19
import Proofs.Claims.Restated.Claim13beRoute3_20
import Proofs.Claims.Restated.Claim13beRoute3_21
import Proofs.Claims.Restated.Claim13beRoute3_22
import Proofs.Claims.Restated.Claim13beRoute3_23
import Proofs.Claims.Restated.Claim13beRoute3_24
import Proofs.Claims.Restated.Claim13beRoute3_26
import Proofs.Claims.Restated.Claim13beRoute3_30
import Proofs.Claims.Restated.Claim13beRoute3_37
import Proofs.Claims.Restated.Claim13beRoute3_40
import Proofs.Claims.Restated.Claim13beRoute3_41
import Proofs.Claims.Restated.Claim13beRoute3_42
import Proofs.Claims.Restated.Claim13beRoute3_43
import Proofs.Claims.Restated.CommonViewOfFinalizedDescendantsFacts
import Proofs.Claims.Restated.ProcessedFlip
import Proofs.Claims.Restated.Redelivery
import Proofs.Claims.Restated.RunAll
import Proofs.Claims.Restated.ReceiptOutcome
import Proofs.Claims.Restated.SynchronyH
import Proofs.Claims.Restated.VocabularyAssumptionsLemmas
import Proofs.Claims.Restated.WakeWindow
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_AlignedRoundLemmas
import Proofs.Claims.Restated.Vocabulary_Protocol_ValidatorClient_BlockEmission
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_43
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.ProcessedFlip
import Model.Conditions.RunAll
import Model.Conditions.RunVocabulary
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ValidatorVoteSafety
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedReceiptCalls
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_ChainState_AlignedRoundLemmas
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_44

/-!
# The admissibility bundle for the validators not held by the adversary

Every field of `AdmissibleFieldsOn` for the run of the first `n` sts steps, for the family
`notHeldAt Sched` of validators not held by the adversary, read along `runAllPath`, the path of the
run that `x` follows; and the per-instant theorems it is built from (cuts, relays, ticks,
authenticity, the run scope). Stated over a model `M : Record.Model V` and its facts
`facts : Record.Facts M`.
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

/-- If strictly more than half of every slot's committee is honest through the slot's confirmation
    instant, then strictly more than half of every slot's committee is not held by the adversary at
    that instant. -/
theorem honestCommitteesOn_notHeld (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched)) :
    Restated.HonestCommitteesOn M (Setup.alwaysAwake S) (notHeldAt Sched) := by
  intro s
  have h : (S.E.committee s).card <
      2 * ((S.E.committee s) ∩ honestThroughSet Sched (M.confirmation_time S.E s)).card :=
    hcom s
  have hsub : (S.E.committee s) ∩ honestThroughSet Sched (M.confirmation_time S.E s) ⊆
      (S.E.committee s) ∩ notHeldAt Sched (M.confirmation_time S.E s) :=
    Finset.inter_subset_inter_left (honestThroughSet_subset_notHeldAt Sched _)
  have hle := Finset.card_le_card hsub
  show (S.E.committee s).card <
    2 * ((S.E.committee s) ∩ notHeldAt Sched (M.confirmation_time S.E s)).card
  omega

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

/-- If at every instant up to `tAwakeEnd` the adversary holds less than a third of the weight, and
    `x[n].time ≤ tAwakeEnd`, then at every instant `t` up to `x[n].time` the validators outside
    `notHeldAt Sched t` weigh less than a third of the total. -/
theorem belowOneThirdOn_runAll_notHeld (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) (n : Nat) {tAwakeEnd : Int}
    (hthird : ∀ t : Int, t ≤ tAwakeEnd →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hn : (x[n].time : Int) ≤ tAwakeEnd) :
    BelowOneThirdOn (Setup.alwaysAwake S)
      { Restated.runAll M S Sched x v n with honest := notHeldAt Sched (x[n].time : Int) }
      (notHeldAt Sched) := by
  intro t ht
  have ht' : t ≤ (x[n].time : Int) := ht
  show 3 * S.E.electorate.weightOf
      (Finset.univ \ (Finset.univ \ Sched.adv t)) < S.E.W
  rw [sdiff_sdiff_right_self, inf_eq_right.2 (Finset.subset_univ _)]
  have h1 := hthird t (le_trans ht' hn)
  have h2 := weightOf_add_weightOf_sdiff_eq_W S.E (Sched.adv t)
  have h3 := S.E.electorate.weightOf_add_weightOf_sdiff (Sched.adv t)
  omega

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If the adversary holds `w` at the instant of `x[k + 1]`, then `w`'s node state after `k + 1`
    steps is its node state after `k` steps. -/
theorem st_succ_eq_of_adv (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (k : Nat) {w : V} (hw : w ∈ Sched.adv (x[k + 1].time : Int)) :
    x[k + 1][w].st = x[k][w].st := by
  cases hl : x.lbl k with
  | tickAllAwake τ =>
      obtain ⟨-, hτ⟩ := Restated.tickAllAwake_time facts S Sched x hl
      rw [hτ] at hw
      have hs : AtomicStep (Record.protocolOf M S) Sched (x.lbl k) x[k] x[k + 1] := x.step k
      rw [hl] at hs
      obtain ⟨-, w', tk, -, -, hc⟩ := hs
      have h2 : x[k + 1][w] = (tickAllAwakeUpdate Sched τ x[k] w' tk)[w] := by rw [hc]
      rw [h2]
      by_cases haw : w ∈ Sched.awake (τ : Int)
      · exact (tickAllAwakeUpdate_getElem_adv hw).1
      · rw [tickAllAwakeUpdate_getElem_asleep haw]
  | deliver p m =>
      by_cases hp : p = w
      · subst hp
        have hs : AtomicStep (Record.protocolOf M S) Sched (x.lbl k) x[k] x[k + 1] := x.step k
        rw [hl] at hs
        have ht := Restated.deliver_time facts S Sched x hl
        rw [ht] at hw
        exact absurd hw hs.1.2.2
      · rw [Restated.getElem_succ_of_deliver_ne facts S Sched x hl hp]
  | custom _ ev => exact ev.elim
  | adversarial p m => rw [Restated.getElem_succ_of_adversarial facts S Sched x hl]
  | forward p m => rw [Restated.getElem_succ_of_forward facts S Sched x hl]

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Under monotone corruption, a validator's node state after `m` steps is its node state after some
    step `m' ≤ m` through whose instant it was honest, or it is its initial node state. -/
theorem st_eq_honestThrough_or_initial (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (hmono : Sched.MonotoneCorruption) (w : V) :
    ∀ m : Nat, (∃ m' ≤ m, Restated.HonestThrough M Sched x m' w ∧ x[m][w].st = x[m'][w].st) ∨
      x[m][w].st = x[0][w].st := by
  intro m
  induction m with
  | zero => exact Or.inr rfl
  | succ m ih =>
      by_cases hadv : w ∈ Sched.adv (x[m + 1].time : Int)
      · rw [Restated.st_succ_eq_of_adv facts S Sched x m hadv]
        rcases ih with ⟨m', hm', h1, h2⟩ | h
        · exact Or.inl ⟨m', Nat.le_succ_of_le hm', h1, h2⟩
        · exact Or.inr h
      · exact Or.inl ⟨m + 1, le_rfl, fun t' ht' hmem => hadv (hmono _ _ ht' hmem), rfl⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If `m ≤ n` and `idx` is at most the number of events of the first `m` steps, `runAllPath` of the
    first `m` steps and of the first `n` steps agree before event `idx`. -/
private theorem runAllPath_le (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) {m n : Nat} (hmn : m ≤ n) {idx : Nat}
    (hidx : idx ≤ (Restated.runEvents M S Sched x m).length) :
    Restated.runAllPath M S Sched x v m idx = Restated.runAllPath M S Sched x v n idx := by
  obtain ⟨l, hl⟩ := Restated.runEvents_append facts S Sched x hmn
  have htake : (Restated.runEvents M S Sched x n).take idx =
      (Restated.runEvents M S Sched x m).take idx := by
    rw [hl, List.take_append_of_le_length hidx]
  funext u
  unfold Restated.runAllPath
  rw [htake]

private theorem runAllPath_le_at (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) {m n : Nat} (hmn : m ≤ n) {i : Nat}
    {e : Record.Event V} (he : (Restated.runEvents M S Sched x m)[i]? = some e) :
    Restated.runAllPath M S Sched x v m i = Restated.runAllPath M S Sched x v n i ∧
      Restated.runAllPath M S Sched x v m (i + 1) = Restated.runAllPath M S Sched x v n (i + 1) := by
  have hlt := (List.getElem?_eq_some_iff.1 he).1
  exact ⟨runAllPath_le facts S Sched x v hmn hlt.le, runAllPath_le facts S Sched x v hmn hlt⟩

/-- For `m ≤ n`, `w` emits `o` at `t` in the run of the first `m` steps along `runAllPath` of `m`
    exactly when it does along `runAllPath` of `n`. -/
private theorem emits_runAllPath_le (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) {m n : Nat} (hmn : m ≤ n) (X : Finset V)
    {w : V} {o : NamedObject V} {t : Int} :
    Restated.Vocabulary.Execution.NamedRun.emits M (Setup.alwaysAwake S)
        { Restated.runAll M S Sched x v m with honest := X } (Restated.runAllPath M S Sched x v m)
        w o t ↔
      Restated.Vocabulary.Execution.NamedRun.emits M (Setup.alwaysAwake S)
        { Restated.runAll M S Sched x v m with honest := X } (Restated.runAllPath M S Sched x v n)
        w o t := by
  constructor
  · rintro ⟨i, hi, out, hout, h1, h2⟩
    obtain ⟨e0, e1⟩ := runAllPath_le_at facts S Sched x v hmn hi
    exact ⟨i, hi, out, by rw [← e0]; exact hout, by rw [← e1]; exact h1, h2⟩
  · rintro ⟨i, hi, out, hout, h1, h2⟩
    obtain ⟨e0, e1⟩ := runAllPath_le_at facts S Sched x v hmn hi
    exact ⟨i, hi, out, by rw [e0]; exact hout, by rw [e1]; exact h1, h2⟩

/-- For `m ≤ n`, `w` processes `o` at `t` in the run of the first `m` steps along `runAllPath` of
    `m` exactly when it does along `runAllPath` of `n`. -/
private theorem processes_runAllPath_le (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) {m n : Nat} (hmn : m ≤ n) (X : Finset V)
    {w : V} {o : NamedObject V} {t : Int} :
    Restated.Vocabulary.Execution.NamedRun.processes M (Setup.alwaysAwake S)
        { Restated.runAll M S Sched x v m with honest := X } (Restated.runAllPath M S Sched x v m)
        w o t ↔
      Restated.Vocabulary.Execution.NamedRun.processes M (Setup.alwaysAwake S)
        { Restated.runAll M S Sched x v m with honest := X } (Restated.runAllPath M S Sched x v n)
        w o t := by
  constructor
  · rintro (h | h)
    · exact Or.inl ((emits_runAllPath_le facts S Sched x v hmn X).1 h)
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl ((emits_runAllPath_le facts S Sched x v hmn X).2 h)
    · exact Or.inr h

/-- For `m ≤ n`, `w` processes `o` at event `i` of the run of the first `m` steps along `runAllPath`
    of `m` exactly when it does along `runAllPath` of `n`. -/
private theorem processesAtIndexAlong_runAllPath_le (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) {m n : Nat}
    (hmn : m ≤ n) (X : Finset V) {i : Nat} {w : V} {o : NamedObject V} :
    Restated.Vocabulary.Execution.NamedRun.processesAtIndexAlong M (Setup.alwaysAwake S)
        { Restated.runAll M S Sched x v m with honest := X } (Restated.runAllPath M S Sched x v m)
        i w o ↔
      Restated.Vocabulary.Execution.NamedRun.processesAtIndexAlong M (Setup.alwaysAwake S)
        { Restated.runAll M S Sched x v m with honest := X } (Restated.runAllPath M S Sched x v n)
        i w o := by
  constructor
  · rintro (⟨t, hi, out, hout, h1, h2⟩ | h)
    · obtain ⟨e0, e1⟩ := runAllPath_le_at facts S Sched x v hmn hi
      exact Or.inl ⟨t, hi, out, by rw [← e0]; exact hout, by rw [← e1]; exact h1, h2⟩
    · exact Or.inr h
  · rintro (⟨t, hi, out, hout, h1, h2⟩ | h)
    · obtain ⟨e0, e1⟩ := runAllPath_le_at facts S Sched x v hmn hi
      exact Or.inl ⟨t, hi, out, by rw [e0]; exact hout, by rw [e1]; exact h1, h2⟩
    · exact Or.inr h

/-- For `m ≤ n`, `w` handles `o` at `t` at event `j` of the run of the first `m` steps along
    `runAllPath` of `m` exactly when it does along `runAllPath` of `n`. -/
private theorem actualHandlesAt_runAllPath_le (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) {m n : Nat}
    (hmn : m ≤ n) (X : Finset V) {j : Nat} {w : V} {o : NamedObject V} {t : Int} :
    Restated.Vocabulary.Execution.NamedRun.actualHandlesAt M (Setup.alwaysAwake S)
        { Restated.runAll M S Sched x v m with honest := X } (Restated.runAllPath M S Sched x v m)
        j w o t ↔
      Restated.Vocabulary.Execution.NamedRun.actualHandlesAt M (Setup.alwaysAwake S)
        { Restated.runAll M S Sched x v m with honest := X } (Restated.runAllPath M S Sched x v n)
        j w o t := by
  constructor
  · intro h
    obtain ⟨e, he, -, -⟩ := h.2
    obtain ⟨e0, e1⟩ := runAllPath_le_at facts S Sched x v hmn he
    exact (Restated.actualHandlesAt_congr_path _ _ e0 e1).1 h
  · intro h
    obtain ⟨e, he, -, -⟩ := h.2
    obtain ⟨e0, e1⟩ := runAllPath_le_at facts S Sched x v hmn he
    exact (Restated.actualHandlesAt_congr_path _ _ e0 e1).2 h

/-- For `m ≤ n`, `w` accepts `o` at `t` at event `i` of the run of the first `m` steps along
    `runAllPath` of `m` exactly when it does along `runAllPath` of `n`. -/
private theorem acceptsAt_runAllPath_le (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) {m n : Nat}
    (hmn : m ≤ n) (X : Finset V) {i : Nat} {w : V} {o : NamedObject V} {t : Int} :
    Restated.Vocabulary.Execution.NamedRun.acceptsAt M (Setup.alwaysAwake S)
        { Restated.runAll M S Sched x v m with honest := X } (Restated.runAllPath M S Sched x v m)
        i w o t ↔
      Restated.Vocabulary.Execution.NamedRun.acceptsAt M (Setup.alwaysAwake S)
        { Restated.runAll M S Sched x v m with honest := X } (Restated.runAllPath M S Sched x v n)
        i w o t := by
  constructor
  · intro h
    obtain ⟨e, he, -, -⟩ := h.1.2
    obtain ⟨e0, e1⟩ := runAllPath_le_at facts S Sched x v hmn he
    exact (Restated.acceptsAt_congr_path _ _ e0 e1).1 h
  · intro h
    obtain ⟨e, he, -, -⟩ := h.1.2
    obtain ⟨e0, e1⟩ := runAllPath_le_at facts S Sched x v hmn he
    exact (Restated.acceptsAt_congr_path _ _ e0 e1).2 h

/-- For a cut at `T`, a validator not held by the adversary at `T` is not held at `x[m].time`. -/
private theorem cutAt_notHeld {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (Record.protocolOf M S) Sched} {m n : Nat} {T : Int}
    (hc : Restated.CutAt M S Sched x m n T) :
    ∀ v₀ ∈ notHeldAt Sched T, v₀ ∉ Sched.adv (x[m].time : Int) := by
  intro v₀ hv₀
  rw [hc.time_eq]
  exact mem_notHeldAt.1 hv₀

/-- For a cut at `T` among the first `n` steps, `x[m].time ≤ tAwakeEnd` whenever
    `x[n].time ≤ tAwakeEnd`. -/
private theorem cutAt_inPhase (facts : Record.Facts M) {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (Record.protocolOf M S) Sched} {m n : Nat} {T : Int}
    (hc : Restated.CutAt M S Sched x m n T) {tAwakeEnd : Int}
    (hn : (x[n].time : Int) ≤ tAwakeEnd) : (x[m].time : Int) ≤ tAwakeEnd :=
  le_trans (by exact_mod_cast Restated.time_mono facts S Sched x hc.le) hn

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Under monotone corruption, if some validator is not held by the adversary at `0`, every run
    block of the run of the first `n` steps, read through every validator along the path `x`
    follows, is an ancestor of a block in some configuration's sent log or held by a validator
    honest through some configuration's instant. -/
theorem blockInLog_of_blockInRunOn_univ (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V)
    (H : Finset V) (n : Nat)
    (hmono : Sched.MonotoneCorruption) (hzero : ∃ u : V, u ∉ Sched.adv 0) {A : NamedBlock V}
    (hA : Restated.blockInRunOn M (Setup.alwaysAwake S) { Restated.runAll M S Sched x v n with honest := H }
      (Restated.runAllPath M S Sched x v n) Finset.univ A) :
    Restated.blockInLog M S Sched x A := by
  obtain ⟨B, hdir, hpre⟩ := hA
  rcases hdir with hobj | ⟨v₀, -, i, hbodies⟩
  · exact Restated.blockInLog_of_blockInRun_runAll_withHonest facts S Sched x v ∅ n
      (fun _ h => by simp at h) ⟨B, Or.inl hobj, hpre⟩
  · refine ⟨B, ?_, hpre⟩
    obtain ⟨m, hbodies⟩ : ∃ m : Nat, B ∈ (x[m][v₀].st).st.bodies := by
      rcases Restated.exists_veventsOf_eq_filter_take facts S Sched x v₀ n i with
        ⟨m, -, hm⟩ | ⟨m, -, t, hA, hm⟩
      · rw [Restated.runAllPath_eq facts S Sched x v n i v₀ hm] at hbodies
        exact ⟨m, hbodies⟩
      · rw [Restated.runAllPath_eq_wake facts S Sched x v n i v₀ hA hm,
          (facts.nd.wake_st_record _).1] at hbodies
        exact ⟨m, hbodies⟩
    rcases Restated.st_eq_honestThrough_or_initial facts S Sched x hmono v₀ m with ⟨m', -, hh, heq⟩ | heq
    · exact Or.inr ⟨m', v₀, hh, by rw [← heq]; exact hbodies⟩
    · obtain ⟨u, hu⟩ := hzero
      refine Or.inr ⟨0, u, ?_, ?_⟩
      · intro t' ht' hmem
        have h0 : x[0].time = 0 := x.init.1
        rw [h0] at ht'
        exact hu (hmono _ _ ht' hmem)
      · rw [Record.st_zero M S Sched x u]
        rw [heq, Record.st_zero M S Sched x v₀] at hbodies
        show B ∈ (M.initial (Setup.alwaysAwake S) u).st.bodies
        rw [facts.nd.initial_st]
        rwa [facts.nd.initial_st] at hbodies

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- In a valid sts execution with monotone corruption in which some validator is not held by the
    adversary at `0`, `RootCollisionFreeOn` holds of the run of the first `n` steps read through
    every validator along `runAllPath`: no two distinct run blocks share a root, and an honest
    proposer holds no block with the root it gives its own proposal. -/
theorem rootCollisionFreeOn_runAll_univ (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V)
    (H : Finset V) (n : Nat)
    (hmono : Sched.MonotoneCorruption) (hev : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hzero : ∃ u : V, u ∉ Sched.adv 0) :
    Restated.RootCollisionFreeOn M (Setup.alwaysAwake S) { Restated.runAll M S Sched x v n with honest := H }
      (Restated.runAllPath M S Sched x v n) Finset.univ := by
  refine ⟨fun B C hB hC A D hAB hDC hr => hev.idealization.root_injective B C
    (Restated.blockInLog_of_blockInRunOn_univ facts S Sched x v H n hmono hzero hB)
    (Restated.blockInLog_of_blockInRunOn_univ facts S Sched x v H n hmono hzero hC) A D hAB hDC hr,
    ?_⟩
  intro s j hj B hB
  change (Restated.runAll M S Sched x v n).events[j]? =
    some (Record.Event.tick (S.E.proposer s) (M.proposal_time S.E s)) at hj
  change B ∈ (Restated.runAllPath M S Sched x v n j (S.E.proposer s)).st.bodies at hB
  change B.root ≠ (S.node (S.E.proposer s)).new_root s
  obtain ⟨k, -, hmem, hcases⟩ := Restated.runAllPath_at_event facts S Sched x v n j hj
  have hnode : Record.Event.node (Record.Event.tick (S.E.proposer s) (M.proposal_time S.E s) :
      Record.Event V) = S.E.proposer s := rfl
  simp only [hnode] at hmem hcases
  obtain ⟨τ, hl, hτ, hv, -⟩ := Restated.tick_mem_actionEventsOf hmem
  rcases hcases with ⟨t', he', -, -⟩ | ⟨t', he', hb, -⟩ | ⟨o, t', he', -, -⟩
  · cases he'
  · rw [hb, Record.wakeStage_st facts] at hB
    exact hev.honestRootsNew k τ s hl hτ.symm
      (Restated.honest_upTo_of_mono hmono hv) B hB
  · cases he'

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- In a valid sts execution, if every member of `H` is honest through `x[n].time` and the
    validators outside `H` weigh less than a third, `SlashableBoundOn` holds of the run of the first
    `n` steps read through every validator along `runAllPath`: no two run blocks carry slashable
    weight `2q − W` between their chains. -/
theorem slashableBoundOn_runAll_univ (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V)
    (H : Finset V) (n : Nat)
    (hev : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hH : ∀ v₀ ∈ H, Restated.HonestThrough M Sched x n v₀)
    (hbot : Execution.BelowOneThird (Setup.alwaysAwake S) H) :
    Restated.SlashableBoundOn M (Setup.alwaysAwake S) { Restated.runAll M S Sched x v n with honest := H }
      (Restated.runAllPath M S Sched x v n) Finset.univ := by
  have hcar : ∀ B : NamedBlock V,
      Restated.RunBlockOn M (Setup.alwaysAwake S) { Restated.runAll M S Sched x v n with honest := H }
        (Restated.runAllPath M S Sched x v n) Finset.univ B →
      Restated.Vocabulary.Proofs.AlignedRoundLemmas.CarriedByHonest M (Setup.alwaysAwake S)
        { Restated.runAll M S Sched x v n with honest := H } (Restated.runAllPath M S Sched x v n) H
        (M.chain_attestations B.erase) := by
    intro B hB a ha hah
    obtain ⟨X, hXB, row, hrow, rfl⟩ := facts.ev.named_mem_chain_attestations_of_erase B ha
    obtain ⟨v₀, t, hproc⟩ := Restated.processes_of_blockInRun_runAll_withHonest facts S Sched x v Finset.univ n
      hev.toDeliveryWellFormed hB hXB hrow
    obtain ⟨t', -, hem⟩ := (Restated.attestationAuthenticity_runAll_withHonest facts S Sched x v H n
      hev.toUnforgeability hH).carriedAttest v₀ X t hproc row hrow
      (by rw [← namedAttestation_erase_val_index row]; exact hah)
    exact ⟨row, t', rfl, by rw [namedAttestation_erase_val_index]; exact hem⟩
  intro B₁ B₂ hB₁ hB₂
  exact Restated.Vocabulary.Proofs.AlignedRoundLemmas.noSlashableWeightBetween_of_belowOneThird facts
    (Restated.runAllPath M S Sched x v n) hbot
    (Restated.noSelfSlashing_runAll_withHonest facts S Sched x v H n _
      (Restated.OnePath_runAllPath facts S Sched x v n)) (hcar B₁ hB₁) (hcar B₂ hB₂)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For `0 ≤ T ≤ x[n].time` there is a cut `CutAt M S Sched x m n T`; the events of the run of the
    first `n` steps up to `T` come first, and the run of the first `m` steps, with the validators
    not held by the adversary at `T` declared honest, is that run cut at `T`. -/
theorem cut_context (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V) (n : Nat) (X : Finset V) {T : Int} (hT0 : 0 ≤ T) (hTn : T ≤ (x[n].time : Int)) :
    ∃ m : Nat, Restated.CutAt M S Sched x m n T ∧
      CutSuffix ({ Restated.runAll M S Sched x v n with honest := X } : Record.Run V) T ∧
      ({ Restated.runAll M S Sched x v m with honest := notHeldAt Sched T } : Record.Run V) =
        cutRun ({ Restated.runAll M S Sched x v n with honest := X } : Record.Run V) (notHeldAt Sched T) T := by
  obtain ⟨m, hc⟩ := Restated.exists_cutAt facts S Sched x hT0 hTn
  exact ⟨m, hc, Restated.cutSuffix_runAll facts S Sched x v n X hT0 hTn, Restated.runAll_eq_cutRun facts S Sched x v hc _ _⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Whatever a validator processes in the run of the first `n` sts steps, along any path of the run,
    it processes at an instant between `0` and `x[n].time`. -/
theorem processes_time_runAll (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) (H : Finset V) (n : Nat)
    {W : Nat → V → M.N} {w : V} {o : NamedObject V} {t : Int}
    (hp : Restated.Vocabulary.Execution.NamedRun.processes M (Setup.alwaysAwake S) { Restated.runAll M S Sched x v n with honest := H }
      W w o t) :
    0 ≤ t ∧ t ≤ (x[n].time : Int) := by
  rcases hp with ⟨i, hi, -⟩ | ⟨i, hi⟩
  · exact Restated.in_horizon_runAll_withHonest facts S Sched x v H n _ (List.mem_of_getElem? hi)
  · exact Restated.in_horizon_runAll_withHonest facts S Sched x v H n _ (List.mem_of_getElem? hi)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The event at which `w`'s store goes from not having processed `o` to having processed it, along
    the path `x` follows, is a tick or a delivery of `w` at an sts step where the same change
    happens. -/
private theorem flip_event_cases₄₄ (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) (n m : Nat) {w : V}
    {o : NamedObject V} {e₂ : Record.Event V}
    (he₂ : (Restated.runEvents M S Sched x n)[m]? = some e₂) (hnode₂ : Record.Event.node e₂ = w)
    (hm0 : Restated.Vocabulary.Execution.Object.processed M
      (Restated.runAllPath M S Sched x v n m w).st o = false)
    (hm1 : Restated.Vocabulary.Execution.Object.processed M
      (Restated.runAllPath M S Sched x v n (m + 1) w).st o = true) :
    ∃ k₂ < n, e₂ ∈ Record.actionEventsOf M S Sched w (x[k₂].time : Int) (x.lbl k₂) ∧
      Restated.Vocabulary.Execution.Object.processed M (x[k₂][w].st).st o = false ∧
      Restated.Vocabulary.Execution.Object.processed M (x[k₂ + 1][w].st).st o = true ∧
      ((∃ t₂, e₂ = Record.Event.tick w t₂ ∧
          Restated.runAllPath M S Sched x v n m w = Record.wakeStage M Sched t₂ x[k₂] w) ∨
        ∃ o₂ t₂, e₂ = Record.Event.deliver w o₂ t₂) ∧
      Restated.runAllPath M S Sched x v n (m + 1) w = x[k₂ + 1][w].st := by
  obtain ⟨k₂, hk₂, hmem₂, hc₂⟩ := Restated.runAllPath_at_event facts S Sched x v n m he₂
  rw [hnode₂] at hc₂ hmem₂
  refine ⟨k₂, hk₂, hmem₂, ?_⟩
  rcases hc₂ with ⟨t₂, -, hb, ha⟩ | ⟨t₂, het, hb, ha⟩ | ⟨o₂, t₂, hed, hb, ha⟩
  · exfalso
    rw [hb] at hm0
    rw [ha, Record.wakeStage_st facts, hm0] at hm1
    exact absurd hm1 (by simp)
  · rw [hb, Record.wakeStage_st facts] at hm0
    rw [ha] at hm1
    exact ⟨hm0, hm1, Or.inl ⟨t₂, het, hb⟩, ha⟩
  · rw [hb] at hm0
    rw [ha] at hm1
    exact ⟨hm0, hm1, Or.inr ⟨o₂, t₂, hed⟩, ha⟩

/-- If `v₀` accepts `o` at index `i` at instant `t` along the path `x` follows, the event at `i` has
    instant `t` and comes from an sts step `k < n`, `v₀`'s store just before it is its store at
    `x[k]`, and its node state just after it is its node state at `x[k + 1]`. -/
private theorem acceptsAt_pair₄₄ (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) (H : Finset V) (n : Nat)
    {i : Nat} {v₀ : V} {o : NamedObject V} {t : Int}
    (hacc : Restated.Vocabulary.Execution.NamedRun.acceptsAt M (Setup.alwaysAwake S)
      { Restated.runAll M S Sched x v n with honest := H } (Restated.runAllPath M S Sched x v n)
      i v₀ o t) :
    ∃ e : Record.Event V,
      ({ Restated.runAll M S Sched x v n with honest := H } : Record.Run V).events[i]? = some e ∧
      Record.Event.time e = t ∧
      ∃ k < n, e ∈ Record.actionEventsOf M S Sched v₀ (x[k].time : Int) (x.lbl k) ∧
        (Restated.runAllPath M S Sched x v n i v₀).st = (x[k][v₀].st).st ∧
        Restated.runAllPath M S Sched x v n (i + 1) v₀ = x[k + 1][v₀].st := by
  obtain ⟨e, he, hnode, htime⟩ := hacc.1.2
  obtain ⟨k, hk, hmem, hst0, hst1⟩ :=
    Restated.stateBefore_pair_runAll_withHonest facts S Sched x v H n i he
  rw [hnode] at hst0 hst1 hmem
  have hst0' : (Restated.runAllPath M S Sched x v n i v₀).st = (x[k][v₀].st).st := by
    rcases hst0 with h | h
    · rw [h]
    · rw [h, (facts.nd.wake_st_record _).1]
  refine ⟨e, he, htime, k, hk, hmem, hst0', ?_⟩
  rcases hst1 with h | ⟨t', -, h⟩
  · exact h
  ·
    exfalso
    have h0 := hacc.2.1
    have h1 := hacc.2.2
    rw [hst0'] at h0
    rw [h, (facts.nd.wake_st_record _).1, h0] at h1
    exact absurd h1 (by simp)

/-- In the run of the first `n` sts steps, along the path `x` follows, a block that a validator
    honest through `tGAT` accepts at an instant `t ≤ tGAT` is handled, at an instant from `t` and
    before `tGAT + S.E.Δ`, by every member `w` of `H` that has not recorded it after the acceptance
    and whose finalized block at the instant `tGAT + S.E.Δ` is compatible with it, when that instant
    is at most `x[n].time`. -/
theorem relayBlock_of_commonView_honestThroughGAT (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V)
    (H : Finset V) (n : Nat)
    (hmono : Sched.MonotoneCorruption) {tGAT tAwakeEnd : Int}
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hH : ∀ v₀ ∈ H, v₀ ∉ Sched.adv (x[n].time : Int))
    (hn : (x[n].time : Int) ≤ tAwakeEnd)
    {i : Nat} {v₀ w : V} {B : NamedBlock V} {t : Int}
    (hacc : Restated.Vocabulary.Execution.NamedRun.acceptsAt M (Setup.alwaysAwake S)
      { Restated.runAll M S Sched x v n with honest := H } (Restated.runAllPath M S Sched x v n)
      i v₀ (.block B) t)
    (hv₀ : HonestThroughTime Sched tGAT v₀) (hw : w ∈ H)
    (hpw : Restated.Vocabulary.Execution.Object.processed M
      (Restated.runAllPath M S Sched x v n (i + 1) w).st (.block B) = false)
    (ht : t ≤ tGAT) (hdl : tGAT + S.E.Δ ≤ (x[n].time : Int))
    (hcompat : ∀ J : Nat, (x[J].time : Int) = tGAT + S.E.Δ → Restated.HonestThrough M Sched x J w →
      Block.compatible (x[J][w].st).st.core.F B.erase = true) :
    ∃ t', t ≤ t' ∧ t' < tGAT + S.E.Δ ∧
      ∃ j : Nat, Restated.Vocabulary.Execution.NamedRun.actualHandlesAt M (Setup.alwaysAwake S)
        { Restated.runAll M S Sched x v n with honest := H } (Restated.runAllPath M S Sched x v n)
        j w (.block B) t' := by
  have hΔ : 0 < S.E.Δ := S.E.Δ_pos
  have hW : Restated.Vocabulary.Execution.NamedRun.OnePath M (Setup.alwaysAwake S)
      { Restated.runAll M S Sched x v n with honest := H } (Restated.runAllPath M S Sched x v n) :=
    Restated.OnePath_runAllPath facts S Sched x v n
  obtain ⟨e, he, hnode, htime⟩ := hacc.1.2
  have hnw : ∀ u t', e ≠ Record.Event.wake u t' := by
    intro u t' hew
    rcases hacc.1.1 with ⟨t₀, he', -⟩ | ⟨t₀, he'⟩
    · have h := Option.some.inj (he.symm.trans he'); rw [hew] at h; cases h
    · have h := Option.some.inj (he.symm.trans he'); rw [hew] at h; cases h
  obtain ⟨k, hk, hmem, -, hst1⟩ := Restated.stateBefore_pair_runAll_withHonest facts S Sched x v H n i he
  replace hst1 := hst1.resolve_right (fun ⟨t', hew, _⟩ => hnw _ _ hew)
  rw [hnode] at hst1
  have hB1 : B ∈ (x[k + 1][v₀].st).st.bodies := by
    have h := hacc.2.2
    rw [hst1] at h
    exact of_decide_eq_true h
  obtain ⟨hk1, hk0, -⟩ := Restated.time_of_mem_actionEvents facts S Sched x k hmem
  rw [htime] at hk1 hk0
  have ht0 : (0 : Int) ≤ t := by rw [← hk1]; exact Int.natCast_nonneg _
  have hex : ∃ J : Nat, J ≤ n ∧ (x[J].time : Int) = tGAT + S.E.Δ := by
    have hnn : (0 : Int) ≤ tGAT + S.E.Δ := by linarith
    obtain ⟨J, hJn, hJt⟩ := Restated.exists_step_at_time facts S Sched x n (Int.toNat_le.2 hdl)
    exact ⟨J, hJn, by rw [hJt]; exact Int.toNat_of_nonneg hnn⟩
  classical
  let J := Nat.find hex
  obtain ⟨hJn, hJt⟩ : J ≤ n ∧ (x[J].time : Int) = tGAT + S.E.Δ := Nat.find_spec hex
  have hbefore : ∀ j, j < J → (x[j].time : Int) < tGAT + S.E.Δ := by
    intro j hj
    have hle : (x[j].time : Int) ≤ (x[J].time : Int) := by
      exact_mod_cast Restated.time_mono facts S Sched x (Nat.le_of_lt hj)
    rcases lt_or_eq_of_le hle with h | h
    · rwa [hJt] at h
    · exact absurd ⟨le_trans (Nat.le_of_lt hj) hJn, h.trans hJt⟩ (Nat.find_min hex hj)
  have hwJ : Restated.HonestThrough M Sched x J w := by
    intro t' ht' hadv
    have hJn' : (x[J].time : Int) ≤ (x[n].time : Int) := by
      exact_mod_cast Restated.time_mono facts S Sched x hJn
    exact hH w hw (hmono _ _ (le_trans ht' hJn') hadv)
  have hBJ : B ∈ (x[J][w].st).st.bodies := by
    refine Restated.mem_bodies_of_compatible_of_narrowed facts S Sched x hexec hcv (by rw [hk1]; exact ht) hv₀ hB1
      (le_of_eq hJt.symm) hwJ ?_ (hcompat J hJt hwJ)
    · show w ∈ Sched.awake (x[J].time : Int)
      refine hawake _ (by linarith) ?_ w (hwJ _ (le_refl _))
      have : (x[J].time : Int) ≤ (x[n].time : Int) := by exact_mod_cast Restated.time_mono facts S Sched x hJn
      linarith
  set L := (Restated.runEvents M S Sched x J).length with hL
  have hPL : Restated.Vocabulary.Execution.Object.processed M
      (Restated.runAllPath M S Sched x v n L w).st (.block B) = true := by
    rw [hL, Restated.runAllPath_runEvents_length facts S Sched x v hJn w]
    exact decide_eq_true hBJ
  have hiL : i + 1 ≤ L := by
    by_contra hcon
    obtain ⟨k', hJk', -, hmem'⟩ := Restated.step_ge_of_length_le facts S Sched x hJn
      (show L ≤ i by omega) he
    obtain ⟨-, hk0', -⟩ := Restated.time_of_mem_actionEvents facts S Sched x k' hmem'
    have : (x[J].time : Int) ≤ (x[k'].time : Int) := by exact_mod_cast Restated.time_mono facts S Sched x hJk'
    rw [htime] at hk0'
    linarith
  obtain ⟨m, him, hmL, hm0, hm1⟩ := exists_flip_between
    (fun m => Restated.Vocabulary.Execution.Object.processed M
      (Restated.runAllPath M S Sched x v n m w).st (.block B))
    hiL hpw hPL
  replace hm0 : Restated.Vocabulary.Execution.Object.processed M
      (Restated.runAllPath M S Sched x v n m w).st (.block B) = false :=
    hm0
  replace hm1 : Restated.Vocabulary.Execution.Object.processed M
      (Restated.runAllPath M S Sched x v n (m + 1) w).st (.block B) = true := hm1
  have hLn : L ≤ (Restated.runEvents M S Sched x n).length := by
    obtain ⟨l, hl⟩ := Restated.runEvents_append facts S Sched x hJn
    rw [hl, List.length_append]
    omega
  have hmn : m < (Restated.runEvents M S Sched x n).length := lt_of_lt_of_le hmL hLn
  obtain ⟨e₂, he₂⟩ : ∃ e₂ : Record.Event V,
      ({ Restated.runAll M S Sched x v n with honest := H } : Record.Run V).events[m]? = some e₂ :=
    ⟨_, List.getElem?_eq_getElem hmn⟩
  have hnode₂ : Record.Event.node e₂ = w := by
    by_contra hne
    have he₂r : (Restated.runEvents M S Sched x n)[m]? = some e₂ := he₂
    have hf : ((Restated.runEvents M S Sched x n).take (m + 1)).filter
          (fun e => decide (Record.Event.node e = w)) =
        ((Restated.runEvents M S Sched x n).take m).filter
          (fun e => decide (Record.Event.node e = w)) := by
      rw [List.take_add_one, he₂r, Option.toList_some, List.filter_append]
      simp [hne]
    have hsame : Restated.runAllPath M S Sched x v n (m + 1) w
        = Restated.runAllPath M S Sched x v n m w := by
      rcases Restated.exists_veventsOf_eq_filter_take facts S Sched x w n m with
        ⟨j, -, hj⟩ | ⟨j, -, t', hA, hj⟩
      · rw [Restated.runAllPath_eq facts S Sched x v n m w hj,
          Restated.runAllPath_eq facts S Sched x v n (m + 1) w (j := j) (by rw [hf]; exact hj)]
      · rw [Restated.runAllPath_eq_wake facts S Sched x v n m w hA hj,
          Restated.runAllPath_eq_wake facts S Sched x v n (m + 1) w hA (by rw [hf]; exact hj)]
    rw [hsame, hm0] at hm1
    exact absurd hm1 (by simp)
  obtain ⟨k₂, -, hmem₂, hf0, hf1, hc₂', hst₂1⟩ :=
    flip_event_cases₄₄ facts S Sched x v n m (o := .block B) he₂ hnode₂ hm0 hm1
  have hsorted := Restated.sorted_runAll_withHonest_events facts S Sched x v H n
  have htm : t ≤ Record.Event.time e₂ := by
    obtain ⟨hilt, higet⟩ := List.getElem?_eq_some_iff.mp he
    obtain ⟨hmlt, hmget⟩ := List.getElem?_eq_some_iff.mp he₂
    have hkey := (List.pairwise_iff_getElem.mp hsorted) i m hilt hmlt (by omega)
    rw [higet, hmget] at hkey
    rw [← htime]
    exact Restated.time_le_of_key_le hkey
  obtain ⟨k₃, hk₃J, hmem₃⟩ := Restated.step_lt_of_lt_length facts S Sched x hJn hmL he₂
  rcases Restated.flip_step_cases facts S Sched x hf0 hf1 with
    ⟨m', hl, -, -, hcase⟩ | ⟨τ, hl, haw, hdvd, hcase⟩
  ·
    have hmsg : m'.msg = .block B := by
      rcases hcase with h | ⟨B', -, hcc⟩
      · exact h
      · exact hcc.elim
    have he₂eq : e₂ = Record.Event.deliver w (.block B) (x[k₂].time : Int) := by
      rcases hc₂' with ⟨t₂, he₂t, -⟩ | ⟨o₂, t₂, he₂d⟩
      · rw [he₂t] at hmem₂
        obtain ⟨τ, hl', -⟩ := Restated.tickAllAwake_of_mem_actionEventsOf hmem₂
        rw [hl] at hl'; cases hl'
      · rw [he₂d] at hmem₂ ⊢
        obtain ⟨sm, hl', hsm, ht₂⟩ := Restated.deliver_of_mem_actionEventsOf hmem₂
        rw [hl] at hl'
        injection hl' with hw' hm'
        rw [← hsm, ← hm', hmsg, ht₂]
    refine ⟨Record.Event.time e₂, htm, ?_, m,
      Restated.actualHandlesAtIndex_of_processesAtIndex facts (Or.inr ⟨(x[k₂].time : Int), he₂eq ▸ he₂⟩),
      e₂, he₂, hnode₂, rfl⟩
    rw [hnode₂] at hmem₃
    rw [he₂eq] at hmem₃ ⊢
    obtain ⟨-, -, -, ht₃⟩ := Restated.deliver_of_mem_actionEventsOf hmem₃
    show (x[k₂].time : Int) < tGAT + S.E.Δ
    rw [ht₃]
    exact hbefore k₃ hk₃J
  ·
    obtain ⟨out₁, hout₁, hx1, hcase'⟩ := hcase
    have hem : NamedObject.block B ∈ out₁.2 := by
      rcases hcase' with h | ⟨B', -, hcc⟩
      · exact h
      · exact hcc.elim
    obtain ⟨he₂eq, hb₂⟩ : e₂ = Record.Event.tick w (τ : Int) ∧
        Restated.runAllPath M S Sched x v n m w = Record.wakeStage M Sched (τ : Int) x[k₂] w := by
      rcases hc₂' with ⟨t₂, he₂t, hb⟩ | ⟨o₂, t₂, he₂d⟩
      · rw [he₂t] at hmem₂
        obtain ⟨τ', hl', hτ', -⟩ := Restated.tickAllAwake_of_mem_actionEventsOf hmem₂
        rw [hl] at hl'
        injection hl' with hττ
        rw [← hτ', ← hττ] at he₂t hb
        exact ⟨he₂t, hb⟩
      · rw [he₂d] at hmem₂
        obtain ⟨sm, hl', -⟩ := Restated.deliver_of_mem_actionEventsOf hmem₂
        rw [hl] at hl'; cases hl'
    have he₂' : ({ Restated.runAll M S Sched x v n with honest := H } : Record.Run V).events[m]?
        = some (Record.Event.tick w (τ : Int)) := he₂eq ▸ he₂
    have hout' : M.tick (Setup.alwaysAwake S) w (Restated.runAllPath M S Sched x v n m w)
        (τ : Int) ⇢ out₁ := by
      rw [hb₂]; exact hout₁
    have hx1' : Restated.runAllPath M S Sched x v n (m + 1) w = out₁.1 := by
      rw [hst₂1]; exact hx1
    obtain ⟨-, hτ, hprop⟩ := Restated.Vocabulary.Proofs.HealingSurface.emits_block_shape facts (Setup.alwaysAwake S)
      { Restated.runAll M S Sched x v n with honest := H } (Restated.runAllPath M S Sched x v n) hW
      ⟨m, he₂', out₁, hout', hx1', hem⟩
    have hle := Restated.proposal_time_le_of_acceptsAt_block facts S Sched x v H n hmono hexec.toUnforgeability
      hacc hprop (hH w hw)
    refine ⟨Record.Event.time e₂, htm, ?_, m,
      Restated.actualHandlesAtIndex_of_processesAtIndex facts
        (Or.inl ⟨(τ : Int), he₂', out₁, hout', hx1', hem⟩),
      e₂, he₂, hnode₂, rfl⟩
    rw [he₂eq]
    show (τ : Int) < tGAT + S.E.Δ
    have : (τ : Int) = M.proposal_time S.E B.slot := hτ
    linarith

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If `w`'s finalized block in the run of the first `n` sts steps, strictly before the instant
    `T ≤ x[n].time`, is compatible with `B`, then at every step `J` whose instant is strictly before
    `T`, `w`'s finalized block is compatible with `B`. -/
theorem compatible_of_not_excludes_runAll (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V)
    {n J : Nat} {T : Int} {w : V}
    {B : NamedBlock V}
    (hexc : Block.compatible
      (Restated.runAllPath M S Sched x v n (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v n with honest := notHeldAt Sched (x[n].time : Int) } :
          Record.Run V) T) w).st.core.F B.erase = true)
    (hJ : (x[J].time : Int) < T) (hTn : T ≤ (x[n].time : Int)) :
    Block.compatible (x[J][w].st).st.core.F B.erase = true := by
  classical
  have hex : ∃ j : Nat, T ≤ (x[j].time : Int) := ⟨n, hTn⟩
  let j₀ := Nat.find hex
  have hj₀ : T ≤ (x[j₀].time : Int) := Nat.find_spec hex
  have hj₀min : ∀ k, k < j₀ → (x[k].time : Int) < T := fun k hk =>
    lt_of_not_ge (Nat.find_min hex hk)
  have hj₀n : j₀ ≤ n := Nat.find_min' hex hTn
  have hJj : J < j₀ := by
    by_contra hcon
    have := Restated.time_mono_int facts S Sched x (Nat.le_of_not_lt hcon)
    linarith
  have hm : j₀ - 1 + 1 = j₀ := by omega
  obtain ⟨l, hl, hlate⟩ := Restated.runEvents_append_late facts S Sched x (show j₀ - 1 ≤ n by omega)
  have h1 : (Restated.runEvents M S Sched x (j₀ - 1)).filter
      (fun e => decide (Record.Event.time e < T)) = Restated.runEvents M S Sched x (j₀ - 1) := by
    refine List.filter_eq_self.2 (fun e he => ?_)
    have hle := (Restated.in_horizon_runAll_withHonest facts S Sched x v ∅ (j₀ - 1) e he).2
    have hlt : ((x[j₀ - 1].time : Nat) : Int) < T := hj₀min _ (by omega)
    simp only [decide_eq_true_eq]
    exact lt_of_le_of_lt hle hlt
  have h2 : l.filter (fun e => decide (Record.Event.time e < T)) = [] := by
    refine List.filter_eq_nil_iff.2 (fun e he => ?_)
    have hge := hlate e he
    rw [hm] at hge
    simp only [decide_eq_true_eq, not_lt]
    rw [namedEvent_time_eq]
    exact le_trans hj₀ hge
  have hidx : Restated.strictEventIndex
      ({ Restated.runAll M S Sched x v n with honest := notHeldAt Sched (x[n].time : Int) } :
        Record.Run V) T = (Restated.runEvents M S Sched x (j₀ - 1)).length := by
    show ((Restated.runEvents M S Sched x n).filter (fun e => decide (Record.Event.time e < T))).length = _
    rw [hl, List.filter_append, h1, h2, List.append_nil]
  rw [hidx, Restated.runAllPath_runEvents_length facts S Sched x v (show j₀ - 1 ≤ n by omega)] at hexc
  exact Restated.excludes_mono_sts facts S Sched x w (show J ≤ j₀ - 1 by omega) hexc

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If `w`'s finalized block in the run of the first `n` sts steps strictly before
    `max t (tGAT + 1) + Δ` is compatible with `B`, with `t ≤ tGAT` and that instant at most
    `x[n].time`, then at every step whose instant is `tGAT + Δ`, `w`'s finalized block is compatible
    with `B`. -/
theorem relay_compat_of_not_excludes (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V)
    {n : Nat} {tGAT t : Int} {w : V}
    {B : NamedBlock V} (ht : t ≤ tGAT)
    (hdl : max t (tGAT + 1) + S.E.Δ ≤ (x[n].time : Int))
    (hexc : Block.compatible
      (Restated.runAllPath M S Sched x v n (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v n with honest := notHeldAt Sched (x[n].time : Int) } :
          Record.Run V) (max t (tGAT + 1) + S.E.Δ)) w).st.core.F B.erase = true) :
    ∀ J : Nat, (x[J].time : Int) = tGAT + S.E.Δ → Restated.HonestThrough M Sched x J w →
      Block.compatible (x[J][w].st).st.core.F B.erase = true := by
  intro J hJ _
  have hmax : max t (tGAT + 1) = tGAT + 1 := max_eq_right (by linarith)
  exact Restated.compatible_of_not_excludes_runAll facts S Sched x v hexc
    (by rw [hJ, hmax]; linarith) hdl

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

/-- In the run of the first `n` sts steps with any declared set, read along `runAllPath`, an
    attestation that `source` accepts at `t` with `tGAT + 1 ≤ t < c₂`, `source` not held by the
    adversary at `t`, is handled by every `target` not held at `t + S.E.Δ` at an instant from its
    round's opening and before `c₂ + S.E.Δ`, when `c₂ + S.E.Δ ≤ x[n].time`. -/
theorem twoCutoffHandled_runAll_ofNotHeld (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V)
    (H : Finset V) (n : Nat)
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption) {tGAT tAwakeEnd : Int}
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hn : (x[n].time : Int) ≤ tAwakeEnd)
    {source target : V} {i : Nat} {a : NamedAttestation V} {t c₂ : Int}
    (hacc : Restated.Vocabulary.Execution.NamedRun.acceptsAt M (Setup.alwaysAwake S)
      { Restated.runAll M S Sched x v n with honest := H } (Restated.runAllPath M S Sched x v n)
      i source (.attest a) t)
    (hlo : tGAT + 1 ≤ t) (hc₂ : t < c₂)
    (hsource : source ∉ Sched.adv t) (htarget : target ∉ Sched.adv (t + S.E.Δ))
    (hdl : c₂ + S.E.Δ ≤ (x[n].time : Int)) :
    ∃ td, M.opening S.E S.hc a.round ≤ td ∧ td < c₂ + S.E.Δ ∧
      ∃ j : Nat, Restated.Vocabulary.Execution.NamedRun.actualHandlesAt M (Setup.alwaysAwake S)
        { Restated.runAll M S Sched x v n with honest := H } (Restated.runAllPath M S Sched x v n)
        j target (.attest a) td := by
  have hdl' : c₂ + S.E.Δ ≤ (x[n].time : Int) := hdl
  have hopen := Restated.opening_le_of_acceptsAt_attest_runAll_withHonest facts S Sched x v H n hacc
  obtain ⟨e, he, htime, k, hk, hmem, hst0, hst1⟩ := acceptsAt_pair₄₄ facts S Sched x v H n hacc
  have h0 : a ∉ (x[k][source].st).st.sg_rows a.round := by
    have h := hacc.2.1
    rw [hst0] at h
    exact of_decide_eq_false h
  have h1 : a ∈ (x[k + 1][source].st).st.sg_rows a.round := by
    have h := hacc.2.2
    rw [hst1] at h
    exact of_decide_eq_true h
  obtain ⟨hk1, hk0, hk2⟩ := Restated.time_of_mem_actionEvents facts S Sched x k hmem
  rw [htime] at hk1 hk0 hk2
  have hkn : (x[k].time : Int) ≤ (x[n].time : Int) := by
    exact_mod_cast Restated.time_mono facts S Sched x (Nat.le_of_lt hk)
  have hvh : Restated.HonestThrough M Sched x k source :=
    fun t' ht' hadv => hsource (hmono _ _ (le_trans ht' hk0) hadv)
  have hmax : max (x[k + 1].time : Int) S.E.t_GST = t := by
    rw [hk1]; exact max_eq_left (by linarith)
  obtain ⟨d, hd0, hd1, hl⟩ := Restated.attest_delivered_of_recorded_phase facts S Sched x hsync hmono hawake
    h0 h1 hvh (by linarith) (by rw [hmax]; linarith)
    (by rw [hmax]; exact htarget)
  rw [hmax] at hd1
  rw [hk1] at hd0
  have hdn : d < n := by
    by_contra hcon
    have : (x[n].time : Int) ≤ (x[d].time : Int) := by
      exact_mod_cast Restated.time_mono facts S Sched x (Nat.le_of_not_lt hcon)
    linarith
  obtain ⟨j, hj⟩ := Restated.handle_of_deliver_step facts S Sched x v H n hdn hl
  have hdc : (x[d].time : Int) < c₂ + S.E.Δ := by linarith
  exact ⟨(x[d].time : Int), le_trans hopen hd0, hdc, j, hj⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

/-- In the run of the first `n` sts steps with any declared set, read along `runAllPath`, a Goldfish
    vote that `source` accepts at an instant `t ≥ tGAT + 1`, `source` not held by the adversary at
    `t`, is handled by every `target` not held at `t + S.E.Δ` at an instant from `t` and before
    `t + S.E.Δ`, when `t + S.E.Δ ≤ x[n].time`. -/
theorem relayGfVoteHandled_runAll_ofNotHeld (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V)
    (H : Finset V) (n : Nat)
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption) {tGAT tAwakeEnd : Int}
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hn : (x[n].time : Int) ≤ tAwakeEnd)
    {source target : V} {i : Nat} {u : GoldfishVote V} {t : Int}
    (hacc : Restated.Vocabulary.Execution.NamedRun.acceptsAt M (Setup.alwaysAwake S)
      { Restated.runAll M S Sched x v n with honest := H } (Restated.runAllPath M S Sched x v n)
      i source (.gfVote u) t)
    (hlo : tGAT + 1 ≤ t)
    (hsource : source ∉ Sched.adv t) (htarget : target ∉ Sched.adv (t + S.E.Δ))
    (hdl : t + S.E.Δ ≤ (x[n].time : Int)) :
    ∃ t', t ≤ t' ∧ t' < t + S.E.Δ ∧
      ∃ j : Nat, Restated.Vocabulary.Execution.NamedRun.actualHandlesAt M (Setup.alwaysAwake S)
        { Restated.runAll M S Sched x v n with honest := H } (Restated.runAllPath M S Sched x v n)
        j target (.gfVote u) t' := by
  have hdl' : t + S.E.Δ ≤ (x[n].time : Int) := hdl
  obtain ⟨e, he, htime, k, hk, hmem, hst0, hst1⟩ := acceptsAt_pair₄₄ facts S Sched x v H n hacc
  have h0 : u ∉ (M.store_pool (x[k][source].st).st.core u.slot) := by
    have h := hacc.2.1
    rw [hst0] at h
    exact fun hu => of_decide_eq_false h ((facts.sto.mem_store_pool_iff _ u.slot u).mp hu)
  have h1 : u ∈ (M.store_pool (x[k + 1][source].st).st.core u.slot) := by
    have h := hacc.2.2
    rw [hst1] at h
    exact (facts.sto.mem_store_pool_iff _ u.slot u).mpr (of_decide_eq_true h)
  obtain ⟨hk1, hk0, hk2⟩ := Restated.time_of_mem_actionEvents facts S Sched x k hmem
  rw [htime] at hk1 hk0 hk2
  have hkn : (x[k].time : Int) ≤ (x[n].time : Int) := by
    exact_mod_cast Restated.time_mono facts S Sched x (Nat.le_of_lt hk)
  have hvh : Restated.HonestThrough M Sched x k source :=
    fun t' ht' hadv => hsource (hmono _ _ (le_trans ht' hk0) hadv)
  have hmax : max (x[k + 1].time : Int) S.E.t_GST = t := by
    rw [hk1]; exact max_eq_left (by linarith)
  obtain ⟨d, hd0, hd1, hl⟩ := Restated.gfVote_delivered_of_recorded_phase facts S Sched x hsync hmono hawake
    h0 h1 hvh (by linarith) (by rw [hmax]; linarith)
    (by rw [hmax]; exact htarget)
  rw [hmax] at hd1
  rw [hk1] at hd0
  have hdn : d < n := by
    by_contra hcon
    have : (x[n].time : Int) ≤ (x[d].time : Int) := by
      exact_mod_cast Restated.time_mono facts S Sched x (Nat.le_of_not_lt hcon)
    linarith
  obtain ⟨j, hj⟩ := Restated.handle_of_deliver_step facts S Sched x v H n hdn hl
  exact ⟨(x[d].time : Int), hd0, hd1, j, hj⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Every validator not held by the adversary at a public instant `t` with
    `tGAT + 1 ≤ t ≤ x[n].time` ticks at `t` in the run of the first `n` sts steps. -/
theorem tickTotal_runAll_notHeld (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) (n : Nat) {tGAT tAwakeEnd : Int}
    (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hn : (x[n].time : Int) ≤ tAwakeEnd) :
    ∀ t : Int, tGAT + 1 ≤ t → ∀ w ∈ notHeldAt Sched t, PublicTime (Setup.alwaysAwake S) t →
      t ≤ (x[n].time : Int) →
      Record.Event.tick w t ∈
        ({ Restated.runAll M S Sched x v n with honest := notHeldAt Sched (x[n].time : Int) } :
          Record.Run V).events := by
  intro t hlo w hw hpub hhor
  have hg0 := S.E.t_GST_nonneg
  obtain ⟨m, hc, -, heq⟩ := Restated.cut_context facts S Sched x v n (notHeldAt Sched (x[n].time : Int))
    (T := t) (by linarith) hhor
  have htt := Restated.tickTotalFrom_runAll_withHonest facts S Sched x v (notHeldAt Sched t) m tGAT tAwakeEnd
    hawake hmono (cutAt_notHeld hc) (cutAt_inPhase facts hc hn)
  have hmem := htt w hw t hpub (by linarith) (by linarith) (le_of_eq hc.time_eq.symm)
  rw [heq] at hmem
  exact (mem_events_of_cutRun hmem).1

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- In the run of the first `n` sts steps, along `runAllPath`, whatever a validator not held by the
    adversary emits at an instant `t ≥ tGAT + 1` is handled, at an instant from `t` and before
    `t + S.E.Δ`, by every validator `w` not held at `t + S.E.Δ` (when `o` is a block, one whose
    finalized block strictly before `t + S.E.Δ` is compatible with it), when
    `t + S.E.Δ ≤ x[n].time`. -/
theorem broadcast_runAll_notHeld (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) (n : Nat) {tGAT tAwakeEnd : Int}
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption)
    -- every delivery has an outcome from the node state the receiver holds before it
    (hreceipt : ∀ (j : Nat) (w : V) (sm : SignedMsg V (NamedObject V)),
      x.lbl j = AtomicAction.deliver w sm →
      ∃ n' : M.N, M.process (Setup.alwaysAwake S) (x[j][w].st) sm.msg ⇢ n')
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hn : (x[n].time : Int) ≤ tAwakeEnd) :
    ∀ (w₀ : V) (o : NamedObject V) (t : Int), w₀ ∈ notHeldAt Sched t →
      Restated.Vocabulary.Execution.NamedRun.emits M (Setup.alwaysAwake S)
        { Restated.runAll M S Sched x v n with honest := notHeldAt Sched (x[n].time : Int) }
        (Restated.runAllPath M S Sched x v n) w₀ o t →
      ∀ w ∈ notHeldAt Sched (t + S.E.Δ), tGAT + 1 ≤ t →
      t + S.E.Δ ≤ (x[n].time : Int) →
      (∀ B : NamedBlock V, o = .block B →
        Block.compatible (Restated.runAllPath M S Sched x v n (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v n with honest := notHeldAt Sched (x[n].time : Int) } :
            Record.Run V) (t + S.E.Δ)) w).st.core.F B.erase = true) →
      ∃ t', t ≤ t' ∧ t' < t + S.E.Δ ∧ ∃ j : Nat, Restated.Vocabulary.Execution.NamedRun.actualHandlesAt M (Setup.alwaysAwake S)
        { Restated.runAll M S Sched x v n with honest := notHeldAt Sched (x[n].time : Int) }
        (Restated.runAllPath M S Sched x v n) j w o t' := by
  intro w₀ o t _ hem w hw hlo hdl _
  have hΔ := S.E.Δ_pos
  have hg0 := S.E.t_GST_nonneg
  obtain ⟨m, hc, hsuf, heq⟩ := Restated.cut_context facts S Sched x v n (notHeldAt Sched (x[n].time : Int))
    (T := t + S.E.Δ) (by linarith) hdl
  have hem' := Restated.CutSuffix.emits facts (Setup.alwaysAwake S) hsuf
    (notHeldAt Sched (t + S.E.Δ)) (by linarith) hem
  rw [← heq] at hem'
  obtain ⟨i, he, out, hout, h1o, h2o⟩ := (emits_runAllPath_le facts S Sched x v hc.le _).2 hem'
  obtain ⟨t', h1, h2, j, hj⟩ := Restated.handle_of_processesAtIndex_phase facts S Sched x v
    (notHeldAt Sched (t + S.E.Δ)) m hsync hmono hreceipt hawake hgst (cutAt_inPhase facts hc hn)
    (Or.inl ⟨t, he, out, hout, h1o, h2o⟩) he rfl (by show tGAT < t; linarith)
    (le_of_eq hc.time_eq.symm) (cutAt_notHeld hc w hw)
  have hj' := (actualHandlesAt_runAllPath_le facts S Sched x v hc.le _).1 hj
  rw [heq] at hj'
  exact ⟨t', h1, h2, j, (Restated.CutSuffix.actualHandlesAt_of_cut facts (Setup.alwaysAwake S) hsuf _ hj')⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- In the run of the first `n` sts steps, along `runAllPath`, a Goldfish vote a validator accepts
    at an instant `t ≥ tGAT + 1`, by a delivery of the vote itself or its own emission, is handled
    by every validator not held by the adversary at `t + S.E.Δ` at an instant from `t` and before
    `t + S.E.Δ`, when `t + S.E.Δ ≤ x[n].time`. -/
theorem relayGfVote_runAll_notHeld (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) (n : Nat) {tGAT tAwakeEnd : Int}
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption)
    -- every delivery has an outcome from the node state the receiver holds before it
    (hreceipt : ∀ (j : Nat) (w : V) (sm : SignedMsg V (NamedObject V)),
      x.lbl j = AtomicAction.deliver w sm →
      ∃ n' : M.N, M.process (Setup.alwaysAwake S) (x[j][w].st) sm.msg ⇢ n')
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hn : (x[n].time : Int) ≤ tAwakeEnd) :
    ∀ (w₀ : V) (i : Nat) (u : GoldfishVote V) (t : Int), w₀ ∈ notHeldAt Sched t →
      Restated.Vocabulary.Execution.NamedRun.acceptsAt M (Setup.alwaysAwake S)
        { Restated.runAll M S Sched x v n with honest := notHeldAt Sched (x[n].time : Int) }
        (Restated.runAllPath M S Sched x v n) i w₀ (.gfVote u) t →
      Restated.Vocabulary.Execution.NamedRun.processesAtIndexAlong M (Setup.alwaysAwake S)
        { Restated.runAll M S Sched x v n with honest := notHeldAt Sched (x[n].time : Int) }
        (Restated.runAllPath M S Sched x v n) i w₀ (.gfVote u) →
      tGAT + 1 ≤ t → ∀ w ∈ notHeldAt Sched (t + S.E.Δ),
      Restated.Vocabulary.Execution.Object.processed M
        (Restated.runAllPath M S Sched x v n (i + 1) w).st (.gfVote u) = false →
      t + S.E.Δ ≤ (x[n].time : Int) →
      ∃ t', t ≤ t' ∧ t' < t + S.E.Δ ∧ ∃ j : Nat, Restated.Vocabulary.Execution.NamedRun.actualHandlesAt M (Setup.alwaysAwake S)
        { Restated.runAll M S Sched x v n with honest := notHeldAt Sched (x[n].time : Int) }
        (Restated.runAllPath M S Sched x v n) j w (.gfVote u) t' := by
  intro w₀ i u t _ hacc hproc hlo w hw _ hdl
  have hΔ := S.E.Δ_pos
  have hg0 := S.E.t_GST_nonneg
  obtain ⟨m, hc, hsuf, heq⟩ := Restated.cut_context facts S Sched x v n (notHeldAt Sched (x[n].time : Int))
    (T := t + S.E.Δ) (by linarith) hdl
  obtain ⟨hlt, hacc'⟩ := Restated.CutSuffix.acceptsAt facts (Setup.alwaysAwake S) hsuf
    (notHeldAt Sched (t + S.E.Δ)) (by linarith) hacc
  have hge := getElem?_of_prefix (hsuf.prefix (notHeldAt Sched (t + S.E.Δ))) hlt
  have hproc' : Restated.Vocabulary.Execution.NamedRun.processesAtIndexAlong M (Setup.alwaysAwake S)
      (cutRun ({ Restated.runAll M S Sched x v n with honest := notHeldAt Sched (x[n].time : Int) } :
        Record.Run V) (notHeldAt Sched (t + S.E.Δ)) (t + S.E.Δ))
      (Restated.runAllPath M S Sched x v n) i w₀ (.gfVote u) := by
    unfold Restated.Vocabulary.Execution.NamedRun.processesAtIndexAlong at hproc ⊢
    rw [← hge]
    exact hproc
  rw [← heq] at hacc' hproc'
  have hacc'' := (acceptsAt_runAllPath_le facts S Sched x v hc.le _).2 hacc'
  have hproc'' := (processesAtIndexAlong_runAllPath_le facts S Sched x v hc.le _).2 hproc'
  obtain ⟨e, he, -, htime⟩ := hacc''.1.2
  obtain ⟨t', h1, h2, j, hj⟩ := Restated.handle_of_processesAtIndex_phase facts S Sched x v
    (notHeldAt Sched (t + S.E.Δ)) m hsync hmono hreceipt hawake hgst (cutAt_inPhase facts hc hn)
    hproc'' he htime (by omega) (le_of_eq hc.time_eq.symm) (cutAt_notHeld hc w hw)
  have hj' := (actualHandlesAt_runAllPath_le facts S Sched x v hc.le _).1 hj
  rw [heq] at hj'
  exact ⟨t', h1, h2, j, (Restated.CutSuffix.actualHandlesAt_of_cut facts (Setup.alwaysAwake S) hsuf _ hj')⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- In the run of the first `n` sts steps, along `runAllPath`, a block a validator not held by the
    adversary at `max t (tGAT + 1)` accepts at `t` is handled, at an instant from `t` and before
    `max t (tGAT + 1) + S.E.Δ`, by every validator `w` not held at that instant that has not
    recorded it after the acceptance and whose finalized block strictly before that instant is
    compatible with it, when that instant is at most `x[n].time`. -/
theorem relayBlock_runAll_notHeld (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) (n : Nat) {tGAT tAwakeEnd : Int}
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hn : (x[n].time : Int) ≤ tAwakeEnd) :
    ∀ (w₀ : V) (i : Nat) (B : NamedBlock V) (t : Int), w₀ ∈ notHeldAt Sched (max t (tGAT + 1)) →
      Restated.Vocabulary.Execution.NamedRun.acceptsAt M (Setup.alwaysAwake S)
        { Restated.runAll M S Sched x v n with honest := notHeldAt Sched (x[n].time : Int) }
        (Restated.runAllPath M S Sched x v n) i w₀ (.block B) t →
      ∀ w ∈ notHeldAt Sched (max t (tGAT + 1) + S.E.Δ),
      Restated.Vocabulary.Execution.Object.processed M
        (Restated.runAllPath M S Sched x v n (i + 1) w).st (.block B) = false →
      max t (tGAT + 1) + S.E.Δ ≤ (x[n].time : Int) →
      Block.compatible
        (Restated.runAllPath M S Sched x v n (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v n with honest := notHeldAt Sched (x[n].time : Int) } :
            Record.Run V) (max t (tGAT + 1) + S.E.Δ)) w).st.core.F B.erase = true →
      ∃ t', t ≤ t' ∧ t' < max t (tGAT + 1) + S.E.Δ ∧
        ∃ j : Nat, Restated.Vocabulary.Execution.NamedRun.actualHandlesAt M (Setup.alwaysAwake S)
          { Restated.runAll M S Sched x v n with honest := notHeldAt Sched (x[n].time : Int) }
          (Restated.runAllPath M S Sched x v n) j w (.block B) t' := by
  have hreceipt : ∀ (j : Nat) (w : V) (sm : SignedMsg V (NamedObject V)),
      x.lbl j = AtomicAction.deliver w sm →
      ∃ n' : M.N, M.process (Setup.alwaysAwake S) (x[j][w].st) sm.msg ⇢ n' :=
    fun _ _ _ hl =>
      Restated.receipt_outcome_of_deliver_mono facts S Sched x hvalid.idealization hmono hl
  intro w₀ i B t hw₀ hacc w hw hpw hdl hexcl
  have hΔ := S.E.Δ_pos
  have hg0 := S.E.t_GST_nonneg
  have hle1 : t ≤ max t (tGAT + 1) := le_max_left _ _
  have hle2 : tGAT + 1 ≤ max t (tGAT + 1) := le_max_right _ _
  obtain ⟨m, hc, hsuf, heq⟩ := Restated.cut_context facts S Sched x v n (notHeldAt Sched (x[n].time : Int))
    (T := max t (tGAT + 1) + S.E.Δ) (by linarith) hdl
  obtain ⟨hlt, hacc'⟩ := Restated.CutSuffix.acceptsAt facts (Setup.alwaysAwake S) hsuf
    (notHeldAt Sched (max t (tGAT + 1) + S.E.Δ)) (by linarith) hacc
  rw [← heq] at hacc'
  have hacc'' := (acceptsAt_runAllPath_le facts S Sched x v hc.le _).2 hacc'
  obtain ⟨e, he, -, htime⟩ := hacc''.1.2
  have hpw'' : Restated.Vocabulary.Execution.Object.processed M
      (Restated.runAllPath M S Sched x v m (i + 1) w).st (.block B) = false := by
    rw [(runAllPath_le_at facts S Sched x v hc.le he).2]
    exact hpw
  by_cases ht : t ≤ tGAT
  · have hv₀ : HonestThroughTime Sched tGAT w₀ := fun t' ht' =>
      honestThroughTime_of_mem_notHeldAt hmono hw₀ t' (by linarith)
    obtain ⟨t', h1, h2, j, hj⟩ := Restated.relayBlock_of_commonView_honestThroughGAT facts S Sched x v
      (notHeldAt Sched (max t (tGAT + 1) + S.E.Δ)) m hmono hawake
      hcv hvalid
      (cutAt_notHeld hc) (cutAt_inPhase facts hc hn) hacc'' hv₀ hw hpw'' ht
      (by rw [hc.time_eq]; linarith)
      (Restated.relay_compat_of_not_excludes facts S Sched x v ht hdl hexcl)
    have hj' := (actualHandlesAt_runAllPath_le facts S Sched x v hc.le _).1 hj
    rw [heq] at hj'
    exact ⟨t', h1, by linarith, j, (Restated.CutSuffix.actualHandlesAt_of_cut facts (Setup.alwaysAwake S) hsuf _ hj')⟩
  · have hmax : max t (tGAT + 1) = t := max_eq_left (by linarith)
    obtain ⟨t', h1, h2, j, hj⟩ := Restated.handle_of_processesAtIndex_phase facts S Sched x v
      (notHeldAt Sched (max t (tGAT + 1) + S.E.Δ)) m hsync hmono hreceipt hawake hgst (cutAt_inPhase facts hc hn)
      hacc''.1.1 he htime (by linarith) (by rw [hc.time_eq]; linarith) (cutAt_notHeld hc w hw)
    have hj' := (actualHandlesAt_runAllPath_le facts S Sched x v hc.le _).1 hj
    rw [heq] at hj'
    exact ⟨t', h1, by linarith, j, (Restated.CutSuffix.actualHandlesAt_of_cut facts (Setup.alwaysAwake S) hsuf _ hj')⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- In the run of the first `n` sts steps, along `runAllPath`, an object processed at `t` whose
    author is not held by the adversary at `t` was emitted by its author by `t`, and so was each
    Goldfish vote and attestation a block processed at `t` includes. -/
theorem unforgeable_runAll_notHeld (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) (n : Nat)
    (hmono : Sched.MonotoneCorruption)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) :
    (∀ (w₀ : V) (o : NamedObject V) (t : Int), Restated.Vocabulary.Execution.NamedRun.processes M (Setup.alwaysAwake S)
        { Restated.runAll M S Sched x v n with honest := notHeldAt Sched (x[n].time : Int) }
        (Restated.runAllPath M S Sched x v n) w₀ o t →
      ∀ u ∈ notHeldAt Sched t, o.author = some u → ∃ t', t' ≤ t ∧
        Restated.Vocabulary.Execution.NamedRun.emits M (Setup.alwaysAwake S)
          { Restated.runAll M S Sched x v n with honest := notHeldAt Sched (x[n].time : Int) }
          (Restated.runAllPath M S Sched x v n) u o t') ∧
    (∀ (w₀ : V) (B : NamedBlock V) (t : Int), Restated.Vocabulary.Execution.NamedRun.processes M (Setup.alwaysAwake S)
        { Restated.runAll M S Sched x v n with honest := notHeldAt Sched (x[n].time : Int) }
        (Restated.runAllPath M S Sched x v n) w₀ (.block B) t →
      ∀ u ∈ B.gf_votes, u.val_index ∈ notHeldAt Sched t → ∃ t', t' ≤ t ∧
        Restated.Vocabulary.Execution.NamedRun.emits M (Setup.alwaysAwake S)
          { Restated.runAll M S Sched x v n with honest := notHeldAt Sched (x[n].time : Int) }
          (Restated.runAllPath M S Sched x v n) u.val_index (.gfVote u) t') ∧
    (∀ (w₀ : V) (B : NamedBlock V) (t : Int), Restated.Vocabulary.Execution.NamedRun.processes M (Setup.alwaysAwake S)
        { Restated.runAll M S Sched x v n with honest := notHeldAt Sched (x[n].time : Int) }
        (Restated.runAllPath M S Sched x v n) w₀ (.block B) t →
      ∀ a ∈ B.attestations, a.val_index ∈ notHeldAt Sched t → ∃ t', t' ≤ t ∧
        Restated.Vocabulary.Execution.NamedRun.emits M (Setup.alwaysAwake S)
          { Restated.runAll M S Sched x v n with honest := notHeldAt Sched (x[n].time : Int) }
          (Restated.runAllPath M S Sched x v n) a.val_index (.attest a) t') := by
  have key : ∀ (w₀ : V) (o o' : NamedObject V) (t : Int) (u : V),
      Restated.Vocabulary.Execution.NamedRun.processes M (Setup.alwaysAwake S)
        { Restated.runAll M S Sched x v n with honest := notHeldAt Sched (x[n].time : Int) }
        (Restated.runAllPath M S Sched x v n) w₀ o t →
      (o' = o ∨ carries o o') → NamedObject.author o' = some u → u ∈ notHeldAt Sched t →
      ∃ t', t' ≤ t ∧ Restated.Vocabulary.Execution.NamedRun.emits M (Setup.alwaysAwake S)
        { Restated.runAll M S Sched x v n with honest := notHeldAt Sched (x[n].time : Int) }
        (Restated.runAllPath M S Sched x v n) u o' t' := by
    intro w₀ o o' t u hp hco hauth hu
    obtain ⟨ht0, htn⟩ := Restated.processes_time_runAll facts S Sched x v _ n hp
    obtain ⟨m, hc, hsuf, heq⟩ := Restated.cut_context facts S Sched x v n (notHeldAt Sched (x[n].time : Int))
      (T := t) ht0 htn
    have hp' := Restated.CutSuffix.processes facts (Setup.alwaysAwake S) hsuf (notHeldAt Sched t) le_rfl hp
    rw [← heq] at hp'
    have hp'' := (processes_runAllPath_le facts S Sched x v hc.le _).2 hp'
    obtain ⟨t', ht', hem⟩ := Restated.emits_of_signed_runAll_withHonest facts S Sched x v
      (notHeldAt Sched t) m hvalid.toUnforgeability hmono (cutAt_notHeld hc) hp'' hco hauth hu
    have hem' := (emits_runAllPath_le facts S Sched x v hc.le _).1 hem
    rw [heq] at hem'
    exact ⟨t', ht', (Restated.CutSuffix.emits_of_cut facts (Setup.alwaysAwake S) hsuf _ hem')⟩
  refine ⟨?_, ?_, ?_⟩
  · intro w₀ o t hp u hu hauth
    exact key w₀ o o t u hp (Or.inl rfl) hauth hu
  · intro w₀ B t hp u hmem hu
    exact key w₀ (.block B) (.gfVote u) t u.val_index hp (Or.inr (Or.inl ⟨u, hmem, rfl⟩))
      (author_gfVote u) hu
  · intro w₀ B t hp a hmem ha
    exact key w₀ (.block B) (.attest a) t a.val_index hp (Or.inr (Or.inr ⟨a, hmem, rfl⟩))
      (author_attest a) ha

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Along the path `x` follows, every tick at a slot's proposal or Goldfish vote instant whose
    round's grade-1 window starts at or after `tGAT + 1` reads a node state that passes the grade-1
    test of that round under `Setup.alwaysAwake S`. -/
theorem awake_g1_runAllPath (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) (n : Nat) {tGAT tAwakeEnd : Int}
    (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hn : (x[n].time : Int) ≤ tAwakeEnd) :
    ∀ (s : Slot) (u : V) (j : Nat) (τ : Int),
      (τ = M.proposal_time S.E s ∨ τ = M.vote_time S.E s) →
      (Restated.runAll M S Sched x v n).events[j]? = some (Record.Event.tick u τ) →
      tGAT + 1 ≤ M.early S.E S.hc (M.round_of S.hc s) .g1 - S.E.Δ →
      M.awake_for_grade1 (Setup.alwaysAwake S) u (Restated.runAllPath M S Sched x v n j u)
        (M.round_of S.hc s) := by
  intro s u j τ hτ he hlo
  have hΔ : 0 < S.E.Δ := S.E.Δ_pos
  have hhor := (Restated.in_horizon_runAll_withHonest facts S Sched x v
    (Restated.runAll M S Sched x v n).honest n _ (List.mem_of_getElem? he)).2
  obtain ⟨k, -, hmem, hcases⟩ := Restated.runAllPath_at_event facts S Sched x v n j he
  have hnode : Record.Event.node (Record.Event.tick u τ : Record.Event V) = u := rfl
  simp only [hnode] at hmem hcases
  obtain ⟨τ', hl, hτ', hv, -⟩ := tick_mem_actionEventsOf hmem
  rcases hcases with ⟨t', he', -, -⟩ | ⟨t', he', hb, -⟩ | ⟨o, t', he', -, -⟩
  · cases he'
  · have htt : τ = t' := (Record.Event.tick.inj he').2
    subst htt
    rw [hb]
    subst hτ'
    have hhor' : (τ' : Int) ≤ tAwakeEnd := le_trans hhor hn
    refine facts.ndRun.run_fact_g1_at S Sched x k τ' (M.round_of S.hc s) u hl ?_ ?_
      (honest_upTo_of_mono hmono hv)
    · have h1 := facts.gr.early_g1_le_domain_g1 S (M.round_of S.hc s)
      have h2 := facts.gr.Sts_domain_g1_eq_opening S (M.round_of S.hc s)
      have h3 := facts.gr.opening_eq_proposal_time S.E S.hc (M.round_of S.hc s)
      have h4 := facts.sch.proposal_time_mono S.E (facts.gr.opening_slot_round_of_le_slot S.hc s)
      have h5 := facts.sch.proposal_time_lt_vote_time S.E s
      rcases hτ with hτ | hτ <;> rw [hτ] <;> linarith
    · refine Finset.singleton_subset_iff.1 (Finset.le_inf ?_)
      intro t ht
      obtain ⟨h0, h1⟩ := Finset.mem_Icc.1 ht
      exact Finset.singleton_subset_iff.2 (hawake t (by linarith) (by linarith) u
        (honest_upTo_of_mono hmono hv t h1))
  · cases he'

/-- Along the path `x` follows, every tick at a slot `s`'s confirmation instant whose next slot's
    round has its grade-2 window starting at or after `tGAT + 1` reads a node state that passes the
    grade-2 test of that round. -/
theorem awake_g2_runAllPath (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) (n : Nat) {tGAT tAwakeEnd : Int}
    (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hn : (x[n].time : Int) ≤ tAwakeEnd) :
    ∀ (s : Slot) (u : V) (j : Nat),
      (Restated.runAll M S Sched x v n).events[j]? =
        some (Record.Event.tick u (M.confirmation_time S.E s)) →
      tGAT + 1 ≤ M.early S.E S.hc (M.round_of S.hc (s + 1)) .g2 - S.E.Δ →
      M.awake_for_grade2 (Setup.alwaysAwake (Setup.alwaysAwake S)) u
        (Restated.runAllPath M S Sched x v n j u) (M.round_of S.hc (s + 1)) := by
  intro s u j he hlo
  rw [alwaysAwake_alwaysAwake]
  have hΔ : 0 < S.E.Δ := S.E.Δ_pos
  have hhor := (Restated.in_horizon_runAll_withHonest facts S Sched x v
    (Restated.runAll M S Sched x v n).honest n _ (List.mem_of_getElem? he)).2
  obtain ⟨k, -, hmem, hcases⟩ := Restated.runAllPath_at_event facts S Sched x v n j he
  have hnode : Record.Event.node
      (Record.Event.tick u (M.confirmation_time S.E s) : Record.Event V) = u := rfl
  simp only [hnode] at hmem hcases
  obtain ⟨τ', hl, hτ', hv, -⟩ := tick_mem_actionEventsOf hmem
  rcases hcases with ⟨t', he', -, -⟩ | ⟨t', he', hb, -⟩ | ⟨o, t', he', -, -⟩
  · cases he'
  · have htt : M.confirmation_time S.E s = t' := (Record.Event.tick.inj he').2
    rw [hb, ← htt, hτ']
    have hhor' : (τ' : Int) ≤ tAwakeEnd := by rw [← hτ']; exact le_trans hhor hn
    refine facts.ndRun.run_fact_g2_at S Sched x k τ' (M.round_of S.hc (s + 1)) u hl ?_ ?_
      (honest_upTo_of_mono hmono hv)
    · have h1 := facts.gr.early_g2_le_opening S (M.round_of S.hc (s + 1))
      have h3 := facts.gr.opening_eq_proposal_time S.E S.hc (M.round_of S.hc (s + 1))
      have h4 := facts.sch.proposal_time_mono S.E
        (facts.gr.opening_slot_round_of_le_slot S.hc (s + 1))
      have h5 := facts.sch.proposal_time_succ_lt_confirmation_time S.E s
      rw [← hτ']
      linarith
    · refine Finset.singleton_subset_iff.1 (Finset.le_inf ?_)
      intro t ht
      obtain ⟨h0, h1⟩ := Finset.mem_Icc.1 ht
      exact Finset.singleton_subset_iff.2 (hawake t (by linarith) (by linarith) u
        (honest_upTo_of_mono hmono hv t h1))
  · cases he'

/-- The run of the first `n` sts steps, with the validators not held by the adversary at `x[n].time`
    declared honest, satisfies along `runAllPath` every field of `AdmissibleFieldsOn` for the family
    `notHeldAt Sched`, from `tGAT + 1`, with run blocks read through every validator. -/
theorem admissibleFieldsOn_runAll_notHeld (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) (n : Nat)
    {tGAT tAwakeEnd : Int}
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tAwakeEnd →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hn : (x[n].time : Int) ≤ tAwakeEnd) :
    Restated.AdmissibleFieldsOn M (Setup.alwaysAwake S)
      { Restated.runAll M S Sched x v n with honest := notHeldAt Sched (x[n].time : Int) }
      (Restated.runAllPath M S Sched x v n) (notHeldAt Sched) Finset.univ (tGAT + 1) := by
  have hg0 := S.E.t_GST_nonneg
  have hzero : ∃ u : V, u ∉ Sched.adv 0 :=
    exists_notHeld_zero S Sched hthird (le_trans (Int.natCast_nonneg _) hn)
  have hP := Restated.OnePath_runAllPath facts S Sched x v n
  have hreceipt : ∀ (j : Nat) (w : V) (sm : SignedMsg V (NamedObject V)),
      x.lbl j = AtomicAction.deliver w sm →
      ∃ n' : M.N, M.process (Setup.alwaysAwake S) (x[j][w].st) sm.msg ⇢ n' :=
    fun _ _ _ hl =>
      Restated.receipt_outcome_of_deliver_mono facts S Sched x hvalid.idealization hmono hl
  obtain ⟨hunf, hgf, hat⟩ := Restated.unforgeable_runAll_notHeld facts S Sched x v n hmono hvalid
  have hrb := Restated.relayBlock_runAll_notHeld facts S Sched x v n hsync hmono hawake hgst hcv
    hvalid hn
  exact
    { lo_pos := by linarith
      horizon_nonneg := Restated.horizon_nonneg_runAll_withHonest facts S Sched x v _ n
      sorted := Restated.sorted_runAll_withHonest_events facts S Sched x v _ n
      in_horizon := Restated.in_horizon_runAll_withHonest facts S Sched x v _ n
      tick_public := Restated.tick_public_runAll_withHonest facts S Sched x v _ n
      tickIndexUnique := Restated.tickIndexUnique_runAll_withHonest facts S Sched x v _ n
      wire := Restated.wire_runAll_withHonest facts S Sched x v _ n hvalid.toDeliveryWellFormed
      onePath := hP
      tick_outcome := Restated.tick_outcome_runAllPath facts S Sched x v n hmono
        (facts.ndRun.tick_outcome_sts S Sched x hvalid.idealization.root_injective hvalid.honestRootsNew)
      receipt_outcome := fun _ _ _ _ he =>
        Restated.receipt_outcome_of_rootCollisionFreeOn facts _
          (Restated.rootCollisionFreeOn_runAll_univ facts S Sched x v _ n hmono hvalid hzero)
          (Finset.mem_univ _) he
      awake_g1 := fun s u j τ hτ he _ hlo =>
        awake_g1_runAllPath facts S Sched x v n hmono hawake hn s u j τ hτ he hlo
      awake_g2 := fun s u j he _ hlo =>
        awake_g2_runAllPath facts S Sched x v n hmono hawake hn s u j he hlo
      deps := Restated.deps_runAll_withHonest facts S Sched x v _ n hvalid.toDeliveryWellFormed
      tick_total := Restated.tickTotal_runAll_notHeld facts S Sched x v n hmono hawake hgst hn
      broadcast := Restated.broadcast_runAll_notHeld facts S Sched x v n hsync hmono hreceipt hawake hgst hn
      relay_block := fun w₀ i B t hw₀ hacc w hw hpw hdl hexcl =>
        hrb w₀ i B t hw₀ hacc w hw hpw hdl hexcl
      relay_block_admit := fun w₀ i B t hw₀ hacc w hw hpw hdl hexcl => by
        obtain ⟨t', h1, h2, j, hj⟩ := hrb w₀ i B t hw₀ hacc w hw hpw hdl hexcl
        refine ⟨t', h1, h2, j, hj, fun hdel => ?_⟩
        exact Restated.receiver_slot_at_deliveries_runAll facts S Sched x v _ n hmono hawm (facts.ndRun.tick_outcome_sts S Sched x hvalid.idealization.root_injective hvalid.honestRootsNew) j t'
          hdel
          ((Restated.Vocabulary.Proofs.NamedRelayGuards.proposal_time_le_acceptance_of_fields facts
            (Setup.alwaysAwake S) _ (Restated.sorted_runAll_withHonest_events facts S Sched x v _ n)
            (Restated.in_horizon_runAll_withHonest facts S Sched x v _ n) _ hP hacc).trans h1)
      relay_gf_vote := Restated.relayGfVote_runAll_notHeld facts S Sched x v n hsync hmono hreceipt hawake
        hgst hn
      relay_gf_vote_handled := fun w₀ i u t hw₀ hacc hlo w hw _ hdl =>
        Restated.relayGfVoteHandled_runAll_ofNotHeld facts S Sched x v _ n hsync hmono hawake hgst
          hn hacc hlo (mem_notHeldAt.1 hw₀) (mem_notHeldAt.1 hw) hdl
      two_cutoff := fun _ _ source i a t hsource hacc hlo hc₂ _ target htarget _ hdl =>
        Restated.twoCutoffHandled_runAll_ofNotHeld facts S Sched x v _ n hsync hmono hawake hgst hn
          hacc hlo hc₂ (mem_notHeldAt.1 hsource) (mem_notHeldAt.1 htarget) hdl
      unforgeable := hunf
      carried_gf := hgf
      carried_attest := hat
      rootCollisionFree := Restated.rootCollisionFreeOn_runAll_univ facts S Sched x v _ n hmono
        hvalid hzero
      slashableBound := Restated.slashableBoundOn_runAll_univ facts S Sched x v _ n hvalid
        (Restated.honestThrough_of_mem_notHeld facts S Sched x n hmono)
        (Restated.belowOneThird_runAll_notHeld_inPhase facts S Sched x n tAwakeEnd hthird hn) }

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If every window of `gap` rounds from `t₀` that ends by `tEnd'` has a round as
    `MultiProposerRecurrenceOn` asks for `Hs`, so does every such window that ends by any
    `tEnd ≤ tEnd'`. -/
theorem multiProposerRecurrenceOn_mono_end (facts : Record.Facts M) (S : Setup V) (Hs : Int → Finset V) {gap : Nat}
    {t₀ tEnd tEnd' : Int} (hle : tEnd ≤ tEnd')
    (h : Restated.MultiProposerRecurrenceOn M S Hs gap t₀ tEnd') :
    Restated.MultiProposerRecurrenceOn M S Hs gap t₀ tEnd :=
  fun r hstart hwin => h r hstart (le_trans hwin hle)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If `strongOpeningsRecurFrom` holds from `tGAT` with windows ending by `tAwakeEnd`, and
    `x[n].time ≤ tAwakeEnd`, then every window of `gap` rounds from `tGAT` that ends by `x[n].time`
    has a round whose first three proposers are not held by the adversary at their slots'
    confirmation instants. -/
theorem multiProposerRecurrenceOn_runAll_notHeld (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) (n : Nat) {tGAT tAwakeEnd : Int} {gap : Nat}
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tAwakeEnd gap)
    (hn : (x[n].time : Int) ≤ tAwakeEnd) :
    Restated.MultiProposerRecurrenceOn M (Setup.alwaysAwake S) (notHeldAt Sched) gap tGAT
      ({ Restated.runAll M S Sched x v n with honest := notHeldAt Sched (x[n].time : Int) } :
        Record.Run V).horizon :=
  Restated.multiProposerRecurrenceOn_mono_end facts _ _ hn
    (Restated.multiProposerRecurrenceOn_of_strongOpeningsRecurFrom facts S Sched hrec)

end

end DecoupledConsensusModel.Sts.Restated
