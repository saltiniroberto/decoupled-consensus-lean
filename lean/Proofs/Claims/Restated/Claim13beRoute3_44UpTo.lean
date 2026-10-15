import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.ReceiptOutcome
import Proofs.Claims.Restated.Claim13beRoute3_19
import Proofs.Claims.Restated.Claim13beRoute3_21
import Proofs.Claims.Restated.Claim13beRoute3_22
import Proofs.Claims.Restated.Claim13beRoute3_23UpTo
import Proofs.Claims.Restated.Claim13beRoute3_24
import Proofs.Claims.Restated.Claim13beRoute3_24UpTo
import Proofs.Claims.Restated.Claim13beRoute3_26
import Proofs.Claims.Restated.Claim13beRoute3_30
import Proofs.Claims.Restated.Claim13beRoute3_37UpTo
import Proofs.Claims.Restated.Claim13beRoute3_40
import Proofs.Claims.Restated.Claim13beRoute3_41
import Proofs.Claims.Restated.Claim13beRoute3_43
import Proofs.Claims.Restated.Claim13beRoute3_44
import Proofs.Claims.Restated.RunAll
import Model.Conditions.Claim13beRoute3_43
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.ClaimAsyncK_DeliveryUpTo
import Model.Conditions.RunAll
import Model.Conditions.RunVocabulary
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedReceiptCalls
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Record.Wiring

/-!
# The admissibility bundle with synchrony up to the horizon

Every field of `AdmissibleFieldsOn` for the run of the first `n` sts steps and the family
`notHeldAt Sched`, read along `runAllPath`, the path of the run that `x` follows, assuming synchrony
from wake only for sends whose deadline is at most `x[n].time`. Stated over a model
`M : Record.Model V` and its facts `facts : Record.Facts M`.
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

/-- If `b ≤ b'`, synchrony from wake for every send whose deadline is at most `b'` gives it for
    every send whose deadline is at most `b`. -/
private theorem syncBefore_mono {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (Record.protocolOf M S) Sched} {b b' : Int} (hb : b ≤ b')
    (hs : Restated.SynchronyFromWakeBefore M S x b') : Restated.SynchronyFromWakeBefore M S x b :=
  fun k w sm hsend hle haw => hs k w sm hsend (le_trans hle hb) haw

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

/-- If `v₀` accepts `o` at index `i` at instant `t` along the path `x` follows, the event at `i` has
    instant `t` and comes from an sts step `k < n`, `v₀`'s store just before it is its store at
    `x[k]`, and its node state just after it is its node state at `x[k + 1]`. -/
private theorem acceptsAt_pair₄₄UpTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
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

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

/-- With synchrony from wake up to `t + S.E.Δ`, in the run of the first `n` sts steps with any
    declared set, read along `runAllPath`, an attestation that `source` accepts at `t` with
    `tGAT + 1 ≤ t < c₂`, `source` not held by the adversary at `t`, is handled by every `target` not
    held at `t + S.E.Δ` at an instant from its round's opening and before `c₂ + S.E.Δ`, when
    `c₂ + S.E.Δ ≤ x[n].time`. -/
theorem twoCutoffHandled_runAll_ofNotHeld_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V)
    (H : Finset V) (n : Nat)
    {source target : V} {i : Nat} {a : NamedAttestation V} {t c₂ : Int}
    (hsync : Restated.SynchronyFromWakeBefore M S x (t + S.E.Δ))
    (hmono : Sched.MonotoneCorruption) {tGAT tAwakeEnd : Int}
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hn : (x[n].time : Int) ≤ tAwakeEnd)
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
  obtain ⟨e, he, htime, k, hk, hmem, hst0, hst1⟩ := acceptsAt_pair₄₄UpTo facts S Sched x v H n hacc
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
  obtain ⟨d, hd0, hd1, hl⟩ := Restated.attest_delivered_of_recorded_phase_upTo facts S Sched x
    (syncBefore_mono (le_of_eq (by rw [hmax])) hsync) hmono hawake
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

/-- With synchrony from wake up to `t + S.E.Δ`, in the run of the first `n` sts steps with any
    declared set, read along `runAllPath`, a Goldfish vote that `source` accepts at an instant
    `t ≥ tGAT + 1`, `source` not held by the adversary at `t`, is handled by every `target` not held
    at `t + S.E.Δ` at an instant from `t` and before `t + S.E.Δ`, when `t + S.E.Δ ≤ x[n].time`. -/
theorem relayGfVoteHandled_runAll_ofNotHeld_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V)
    (H : Finset V) (n : Nat)
    {source target : V} {i : Nat} {u : GoldfishVote V} {t : Int}
    (hsync : Restated.SynchronyFromWakeBefore M S x (t + S.E.Δ))
    (hmono : Sched.MonotoneCorruption) {tGAT tAwakeEnd : Int}
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hn : (x[n].time : Int) ≤ tAwakeEnd)
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
  obtain ⟨e, he, htime, k, hk, hmem, hst0, hst1⟩ := acceptsAt_pair₄₄UpTo facts S Sched x v H n hacc
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
  obtain ⟨d, hd0, hd1, hl⟩ := Restated.gfVote_delivered_of_recorded_phase_upTo facts S Sched x
    (syncBefore_mono (le_of_eq (by rw [hmax])) hsync) hmono hawake
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

/-- With synchrony from wake up to `x[n].time`, in the run of the first `n` sts steps, along
    `runAllPath`, whatever a validator not held by the adversary emits at an instant `t ≥ tGAT + 1`
    is handled, at an instant from `t` and before `t + S.E.Δ`, by every validator `w` not held at
    `t + S.E.Δ` (when `o` is a block, one whose finalized block strictly before `t + S.E.Δ` is
    compatible with it), when `t + S.E.Δ ≤ x[n].time`. -/
theorem broadcast_runAll_notHeld_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) (n : Nat) {tGAT tAwakeEnd : Int}
    (hsync : Restated.SynchronyFromWakeBefore M S x (x[n].time : Int))
    (hmono : Sched.MonotoneCorruption)
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
  have hmx : (x[m].time : Int) ≤ (x[n].time : Int) := by
    exact_mod_cast Restated.time_mono facts S Sched x hc.le
  obtain ⟨t', h1, h2, j, hj⟩ := Restated.handle_of_processesAtIndex_phase_upTo facts S Sched x v
    (notHeldAt Sched (t + S.E.Δ)) m (t := t) (syncBefore_mono (by linarith) hsync) hmono hreceipt hawake hgst
    (cutAt_inPhase facts hc hn)
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

/-- With synchrony from wake up to `x[n].time`, in the run of the first `n` sts steps, along
    `runAllPath`, a Goldfish vote a validator accepts at an instant `t ≥ tGAT + 1`, by a delivery of
    the vote itself or its own emission, is handled by every validator not held by the adversary at
    `t + S.E.Δ` at an instant from `t` and before `t + S.E.Δ`, when `t + S.E.Δ ≤ x[n].time`. -/
theorem relayGfVote_runAll_notHeld_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) (n : Nat) {tGAT tAwakeEnd : Int}
    (hsync : Restated.SynchronyFromWakeBefore M S x (x[n].time : Int))
    (hmono : Sched.MonotoneCorruption)
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
  obtain ⟨t', h1, h2, j, hj⟩ := Restated.handle_of_processesAtIndex_phase_upTo facts S Sched x v
    (notHeldAt Sched (t + S.E.Δ)) m (t := t) (syncBefore_mono (by linarith) hsync) hmono hreceipt hawake hgst
    (cutAt_inPhase facts hc hn)
    hproc'' he htime (by omega) (le_of_eq hc.time_eq.symm) (cutAt_notHeld hc w hw)
  have hj' := (actualHandlesAt_runAllPath_le facts S Sched x v hc.le _).1 hj
  rw [heq] at hj'
  exact ⟨t', h1, h2, j, (Restated.CutSuffix.actualHandlesAt_of_cut facts (Setup.alwaysAwake S) hsuf _ hj')⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- With synchrony from wake up to `x[n].time`, in the run of the first `n` sts steps, along
    `runAllPath`, a block a validator not held by the adversary at `max t (tGAT + 1)` accepts at `t`
    is handled, at an instant from `t` and before `max t (tGAT + 1) + S.E.Δ`, by every validator `w`
    not held at that instant that has not recorded it after the acceptance and whose finalized block
    strictly before that instant is compatible with it, when that instant is at most `x[n].time`. -/
theorem relayBlock_runAll_notHeld_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) (n : Nat) {tGAT tAwakeEnd : Int}
    (hsync : Restated.SynchronyFromWakeBefore M S x (x[n].time : Int))
    (hmono : Sched.MonotoneCorruption)
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
    obtain ⟨t', h1, h2, j, hj⟩ := Restated.handle_of_processesAtIndex_phase_upTo facts S Sched x v
      (notHeldAt Sched (max t (tGAT + 1) + S.E.Δ)) m (t := t) (syncBefore_mono (by linarith) hsync)
      hmono hreceipt hawake hgst (cutAt_inPhase facts hc hn)
      hacc''.1.1 he htime (by linarith) (by rw [hc.time_eq]; linarith) (cutAt_notHeld hc w hw)
    have hj' := (actualHandlesAt_runAllPath_le facts S Sched x v hc.le _).1 hj
    rw [heq] at hj'
    exact ⟨t', h1, by linarith, j, (Restated.CutSuffix.actualHandlesAt_of_cut facts (Setup.alwaysAwake S) hsuf _ hj')⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- With synchrony from wake up to `x[n].time`, the run of the first `n` sts steps, with the
    validators not held by the adversary at `x[n].time` declared honest, satisfies along
    `runAllPath` every field of `AdmissibleFieldsOn` for the family `notHeldAt Sched`, from
    `tGAT + 1`, with run blocks read through every validator. -/
theorem admissibleFieldsOn_runAll_notHeld_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) (n : Nat)
    {tGAT tAwakeEnd : Int}
    (hsync : Restated.SynchronyFromWakeBefore M S x (x[n].time : Int))
    (hmono : Sched.MonotoneCorruption)
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
  have hrb := relayBlock_runAll_notHeld_upTo facts S Sched x v n hsync hmono hawake hgst hcv
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
        Restated.awake_g1_runAllPath facts S Sched x v n hmono hawake hn s u j τ hτ he hlo
      awake_g2 := fun s u j he _ hlo =>
        Restated.awake_g2_runAllPath facts S Sched x v n hmono hawake hn s u j he hlo
      deps := Restated.deps_runAll_withHonest facts S Sched x v _ n hvalid.toDeliveryWellFormed
      tick_total := Restated.tickTotal_runAll_notHeld facts S Sched x v n hmono hawake hgst hn
      broadcast := broadcast_runAll_notHeld_upTo facts S Sched x v n hsync hmono hreceipt hawake hgst hn
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
      relay_gf_vote := relayGfVote_runAll_notHeld_upTo facts S Sched x v n hsync hmono hreceipt hawake
        hgst hn
      relay_gf_vote_handled := fun w₀ i u t hw₀ hacc hlo w hw _ hdl =>
        relayGfVoteHandled_runAll_ofNotHeld_upTo facts S Sched x v _ n (syncBefore_mono hdl hsync)
          hmono hawake hgst hn hacc hlo (mem_notHeldAt.1 hw₀) (mem_notHeldAt.1 hw) hdl
      two_cutoff := fun _ c₂ source i a t hsource hacc hlo hc₂ _ target htarget _ hdl =>
        twoCutoffHandled_runAll_ofNotHeld_upTo facts S Sched x v _ n (t := t)
          (syncBefore_mono (by
            have hdl' : c₂ + S.E.Δ ≤ (x[n].time : Int) := hdl
            linarith) hsync) hmono hawake hgst hn hacc hlo hc₂
          (mem_notHeldAt.1 hsource) (mem_notHeldAt.1 htarget) hdl
      unforgeable := hunf
      carried_gf := hgf
      carried_attest := hat
      rootCollisionFree := Restated.rootCollisionFreeOn_runAll_univ facts S Sched x v _ n hmono
        hvalid hzero
      slashableBound := Restated.slashableBoundOn_runAll_univ facts S Sched x v _ n hvalid
        (Restated.honestThrough_of_mem_notHeld facts S Sched x n hmono)
        (Restated.belowOneThird_runAll_notHeld_inPhase facts S Sched x n tAwakeEnd hthird hn) }

end

end DecoupledConsensusModel.Sts.Restated
