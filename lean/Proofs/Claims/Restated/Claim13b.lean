import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.HonestNeverSlashed
import Proofs.Claims.Restated.Projection
import Proofs.Claims.Restated.RunAll
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Model.Conditions.RunAll
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ValidatorVoteSafety
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Protocol_ChainState_AlignedRoundLemmas
import Model.Record.Wiring

/-!
# Messages signed by an honest validator, bounded in time

Over a model `M : Record.Model V`: a message signed by a validator the adversary does not hold up to
`tB` came from one of that validator's own ticks, attestations attributed to it are authentic, and
no two stores read at or before `tB` hold slashable weight between them.
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

/-- One step of the sent log, for a validator `v` the adversary does not hold at the step's instant:
    a message under `v`'s signature was already sent, or is in the list of an outcome of `v`'s tick,
    or is forwarded by this step, or is re-sent
    by a delivery to `v` of a message that is the payload or includes it. -/
theorem sent_step_of_honest_at (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    {a : AtomicAction V (NamedObject V) Empty}
    {cfg cfg' : Config V (NamedObject V) (M.N)}
    (hs : AtomicStep (Record.protocolOf M S) Sched a cfg cfg') {v : V} {o : NamedObject V}
    (hv : v ∉ Sched.adv (cfg.time : Int)) :
    (⟨v, o⟩ : SignedMsg V (NamedObject V)) ∈ cfg'.sent →
      (⟨v, o⟩ : SignedMsg V (NamedObject V)) ∈ cfg.sent ∨
        (∃ t : Nat, a = AtomicAction.tickAllAwake t ∧
          v ∈ Sched.awake (t : Int) \ Sched.adv (t : Int) ∧
          ∃ out : M.N × List (NamedObject V),
            M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched (t : Int) cfg v) (t : Int) ⇢ out ∧ o ∈ out.2) ∨
        (∃ p : V, a = AtomicAction.forward p ⟨v, o⟩) ∨
        ∃ sm : SignedMsg V (NamedObject V), a = AtomicAction.deliver v sm ∧
          (sm.msg = o ∨ carries sm.msg o) := by
  refine AtomicStep.elim
    (motive := fun a d d' =>
      v ∉ Sched.adv (d.time : Int) →
        ((⟨v, o⟩ : SignedMsg V (NamedObject V)) ∈ d'.sent →
          (⟨v, o⟩ : SignedMsg V (NamedObject V)) ∈ d.sent ∨
            (∃ t : Nat, a = AtomicAction.tickAllAwake t ∧
              v ∈ Sched.awake (t : Int) \ Sched.adv (t : Int) ∧
              ∃ out : M.N × List (NamedObject V),
                M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched (t : Int) d v) (t : Int) ⇢ out ∧ o ∈ out.2) ∨
            (∃ p : V, a = AtomicAction.forward p ⟨v, o⟩) ∨
            ∃ sm : SignedMsg V (NamedObject V), a = AtomicAction.deliver v sm ∧
              (sm.msg = o ∨ carries sm.msg o)))
    hs ?_ ?_ ?_ ?_ ?_ hv
  · intro d t w tk hen hwake htick _ ho
    have hsent : (tickAllAwakeUpdate Sched t d w tk).sent = d.sent
        + (Sched.awake (t : Int) \ Sched.adv (t : Int)).sum
            (fun q => ((w q).send + (tk q).send).map (SignedMsg.mk q)) := rfl
    rw [hsent, Multiset.mem_add] at ho
    rcases ho with ho | ho
    · exact Or.inl ho
    · obtain ⟨q, hq, hmem⟩ := Multiset.mem_sum.1 ho
      obtain ⟨o', ho', heq⟩ := Multiset.mem_map.1 hmem
      have hqv : q = v := congrArg SignedMsg.sender heq
      have hoo : o' = o := congrArg SignedMsg.msg heq
      subst hqv; subst hoo
      have hwst : (w q).state = Record.wakeStage M Sched (t : Int) d q ∧ (w q).send = 0 := by
        refine ⟨Record.wakeStage_of_TickAllAwakeWake M S Sched (hwake q), ?_⟩
        have hww := hwake q
        unfold TickAllAwakeWake at hww
        by_cases he : q ∈ entrants Sched t
        · rw [if_pos he] at hww
          rw [Record.protocolOf_step_wake M S hww]
        · rw [if_neg he] at hww
          rw [hww]
      rw [hwst.2, zero_add] at ho'
      have htk : tk q ∈ Record.reactionsOf M S q ((w q).state) (t : Int) .tick ∨
          (Record.reactionsOf M S q ((w q).state) (t : Int) .tick = ∅ ∧
            tk q = { state := (w q).state, send := 0 }) := htick q hq
      rcases htk with htk | ⟨-, htk⟩
      · simp only [Record.reactionsOf, Set.mem_setOf_eq] at htk
        obtain ⟨out, hout, htkv⟩ := htk
        rw [htkv] at ho'
        rw [hwst.1] at hout
        exact Or.inr (Or.inl ⟨t, rfl, hq, out, hout, Multiset.mem_coe.1 ho'⟩)
      · -- the tick has no outcome: the step sends nothing for `q`
        rw [htk] at ho'
        exact absurd ho' (by simp)
  · intro d p m res hen hstep _ ho
    have hsent : (applyNodeStepResult p res (receive p m d)).sent
        = d.sent + res.send.map (SignedMsg.mk p) := rfl
    rw [hsent, Multiset.mem_add] at ho
    rcases ho with ho | ho
    · exact Or.inl ho
    · obtain ⟨o', ho', heq⟩ := Multiset.mem_map.1 ho
      have hpv : p = v := congrArg SignedMsg.sender heq
      have hoo : o' = o := congrArg SignedMsg.msg heq
      subst hpv; subst hoo
      have hstep' : res ∈ Record.reactionsOf M S p ((receive p m d)[p].st)
            ((receive p m d)[p].clock : Int) (.recv m) ∨
          (Record.reactionsOf M S p ((receive p m d)[p].st)
              ((receive p m d)[p].clock : Int) (.recv m) = ∅ ∧
            res = { state := (receive p m d)[p].st, send := 0 }) := hstep
      have hsend : res.send = relayedObjects m.msg ∨ res.send = 0 := by
        rcases hstep' with h | ⟨-, h⟩
        · simp only [Record.reactionsOf, Set.mem_setOf_eq] at h
          obtain ⟨n', -, h⟩ := h
          rw [h]; exact Or.inl rfl
        · rw [h]; exact Or.inr rfl
      rcases hsend with hsend | hsend
      · rw [hsend] at ho'
        refine Or.inr (Or.inr (Or.inr ⟨m, rfl, ?_⟩))
        rcases (mem_relayedObjects_iff m.msg o').1 ho' with h | h
        · exact Or.inl h.symm
        · exact Or.inr h
      · -- the receipt has no outcome: the step sends nothing
        rw [hsend] at ho'
        exact absurd ho' (by simp)
  · intro d p ev res _ _ _ _
    exact ev.elim
  · intro d p m hen hvd ho
    have hen' : p ∈ Sched.adv (d.time : Int) := hen
    have hsent : ({ d with sent := ⟨p, m⟩ ::ₘ d.sent } :
        Config V (NamedObject V) (M.N)).sent = ⟨p, m⟩ ::ₘ d.sent := rfl
    rw [hsent, Multiset.mem_cons] at ho
    rcases ho with ho | ho
    · have hpv : v = p := congrArg SignedMsg.sender ho
      subst hpv
      exact absurd hen' hvd
    · exact Or.inl ho
  · intro d p m hen _ ho
    have hsent : ({ d with sent := m ::ₘ d.sent } :
        Config V (NamedObject V) (M.N)).sent = m ::ₘ d.sent := rfl
    rw [hsent, Multiset.mem_cons] at ho
    rcases ho with ho | ho
    · exact Or.inr (Or.inr (Or.inl ⟨p, by rw [ho]⟩))
    · exact Or.inl ho

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- A message sent at a step whose real time is at or before `tB`, under the signature of a
    validator `v` the adversary does not hold at any instant at or before `tB`, with a payload `v`
    authored, is in the list of an outcome of `v`'s own tick at an earlier step `k`, provided signatures are unforgeable. -/
theorem tick_of_honest_signed_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V) (o : NamedObject V) (tB : Int)
    (hv : HonestThroughTime Sched tB v) (hunf : Restated.Unforgeability M S x)
    (hauth : NamedObject.author o = some v) :
    ∀ i : Nat, (x[i].time : Int) ≤ tB →
      (⟨v, o⟩ : SignedMsg V (NamedObject V)) ∈ x[i].sent →
      ∃ k < i, ∃ t : Nat, x.lbl k = AtomicAction.tickAllAwake t ∧
        v ∈ Sched.awake (t : Int) \ Sched.adv (t : Int) ∧
        ∃ out : M.N × List (NamedObject V),
          M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched (t : Int) x[k] v) (t : Int) ⇢ out ∧ o ∈ out.2
  | 0, _, ho => by
      rw [Restated.sent_zero facts S Sched x] at ho
      simp at ho
  | i + 1, hi, ho => by
      have hstep : ((x[i].time : Int)) ≤ ((x[i + 1].time : Int)) := by
        exact_mod_cast Restated.time_mono facts S Sched x (Nat.le_succ i)
      have hi' : (x[i].time : Int) ≤ tB := le_trans hstep hi
      rcases Restated.sent_step_of_honest_at facts S Sched (x.step i) (hv _ hi') ho with
        ho | ⟨t, hlbl, haw, hemit⟩ | ⟨p, hlbl⟩ | ⟨sm, hlbl, hcov⟩
      · obtain ⟨k, hk, hrest⟩ :=
          tick_of_honest_signed_upTo facts S Sched x v o tB hv hunf hauth i hi' ho
        exact ⟨k, Nat.lt_succ_of_lt hk, hrest⟩
      · exact ⟨i, Nat.lt_succ_self i, t, hlbl, haw, hemit⟩
      · have hen : (atomicSpec (Record.protocolOf M S) Sched (x.lbl i)).Enabled x[i] := (x.step i).1
        rw [hlbl] at hen
        have hen' : p ∈ Sched.awake (x[i].time : Int) ∧
            (⟨v, o⟩ : SignedMsg V (NamedObject V)) ∈ x[i][p].view ∧
            p ∉ Sched.adv (x[i].time : Int) := hen
        obtain ⟨k, hk, hrest⟩ := tick_of_honest_signed_upTo facts S Sched x v o tB hv hunf hauth
          i hi' (Restated.mem_sent_of_mem_view facts S Sched x hen'.2.1)
        exact ⟨k, Nat.lt_succ_of_lt hk, hrest⟩
      · -- a delivery to `v` re-sent `o`: the delivered message was already sent, and
        -- `Restated.Unforgeability M` puts `v`'s own copy of `o` there before the step
        have hs := x.step i
        rw [hlbl] at hs
        have hsm : sm ∈ x[i].sent := hs.1.1
        have hhon : Restated.HonestThrough M Sched x i v := fun t' ht' => hv t' (le_trans ht' hi')
        have hvo : (⟨v, o⟩ : SignedMsg V (NamedObject V)) ∈ x[i].sent := by
          rcases hcov with heq | hc
          · have h := hunf.unforgeable i sm v hsm (by rw [heq]; exact hauth) hhon
            rwa [heq] at h
          · exact hunf.carried i sm o v hsm hc hauth hhon
        obtain ⟨k, hk, hrest⟩ :=
          tick_of_honest_signed_upTo facts S Sched x v o tB hv hunf hauth i hi' hvo
        exact ⟨k, Nat.lt_succ_of_lt hk, hrest⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- `tick_of_honest_signed_upTo`, with the conclusion naming the outcome of `v`'s tick that step `k`
    took by its node state, `x[k + 1][v].st = out.1`. -/
theorem tick_of_honest_signed_upTo_taken (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V)
    (o : NamedObject V) (tB : Int)
    (hv : HonestThroughTime Sched tB v) (hunf : Restated.Unforgeability M S x)
    (hauth : NamedObject.author o = some v) :
    ∀ i : Nat, (x[i].time : Int) ≤ tB →
      (⟨v, o⟩ : SignedMsg V (NamedObject V)) ∈ x[i].sent →
      ∃ k < i, ∃ t : Nat, x.lbl k = AtomicAction.tickAllAwake t ∧
        v ∈ Sched.awake (t : Int) \ Sched.adv (t : Int) ∧
        ∃ out : M.N × List (NamedObject V),
          M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched (t : Int) x[k] v) (t : Int) ⇢ out ∧
            x[k + 1][v].st = out.1 ∧ o ∈ out.2
  | 0, _, ho => by
      rw [Restated.sent_zero facts S Sched x] at ho
      simp at ho
  | i + 1, hi, ho => by
      have hstep : ((x[i].time : Int)) ≤ ((x[i + 1].time : Int)) := by
        exact_mod_cast Restated.time_mono facts S Sched x (Nat.le_succ i)
      have hi' : (x[i].time : Int) ≤ tB := le_trans hstep hi
      by_cases hold : (⟨v, o⟩ : SignedMsg V (NamedObject V)) ∈ x[i].sent
      · obtain ⟨k, hk, hrest⟩ :=
          tick_of_honest_signed_upTo_taken facts S Sched x v o tB hv hunf hauth i hi' hold
        exact ⟨k, Nat.lt_succ_of_lt hk, hrest⟩
      rcases Restated.sent_step_of_honest_at facts S Sched (x.step i) (hv _ hi') ho with
        ho' | ⟨t, hlbl, -, -⟩ | ⟨p, hlbl⟩ | ⟨sm, hlbl, hcov⟩
      · exact absurd ho' hold
      · obtain ⟨haw, out, hout, hst, hmem⟩ :=
          Restated.tick_outcome_of_mem_sent_succ facts S Sched x hlbl ho hold
        exact ⟨i, Nat.lt_succ_self i, t, hlbl, haw, out, hout, hst, hmem⟩
      · have hen : (atomicSpec (Record.protocolOf M S) Sched (x.lbl i)).Enabled x[i] := (x.step i).1
        rw [hlbl] at hen
        have hen' : p ∈ Sched.awake (x[i].time : Int) ∧
            (⟨v, o⟩ : SignedMsg V (NamedObject V)) ∈ x[i][p].view ∧
            p ∉ Sched.adv (x[i].time : Int) := hen
        obtain ⟨k, hk, hrest⟩ := tick_of_honest_signed_upTo_taken facts S Sched x v o tB hv
          hunf hauth i hi' (Restated.mem_sent_of_mem_view facts S Sched x hen'.2.1)
        exact ⟨k, Nat.lt_succ_of_lt hk, hrest⟩
      · have hs := x.step i
        rw [hlbl] at hs
        have hsm : sm ∈ x[i].sent := hs.1.1
        have hhon : Restated.HonestThrough M Sched x i v := fun t' ht' => hv t' (le_trans ht' hi')
        have hvo : (⟨v, o⟩ : SignedMsg V (NamedObject V)) ∈ x[i].sent := by
          rcases hcov with heq | hc
          · have h := hunf.unforgeable i sm v hsm (by rw [heq]; exact hauth) hhon
            rwa [heq] at h
          · exact hunf.carried i sm o v hsm hc hauth hhon
        obtain ⟨k, hk, hrest⟩ :=
          tick_of_honest_signed_upTo_taken facts S Sched x v o tB hv hunf hauth i hi' hvo
        exact ⟨k, Nat.lt_succ_of_lt hk, hrest⟩

/-- Along `runAllPath`, the path of `runAll` the sts execution `x` follows, in the run over the
    first `n` steps with honest set `{v}` and step `n`'s real time at or before `tB`, every
    attestation attributed to `v` inside a processed block was emitted by `v` at or before the
    processing instant. -/
theorem attestationAuthenticity_runAll_upTo (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V) (n : Nat)
    (tB : Int) (hunf : Restated.Unforgeability M S x) (hv : HonestThroughTime Sched tB v)
    (hn : (x[n].time : Int) ≤ tB) :
    Restated.Vocabulary.Internal.AttestationAuthenticity M (Setup.alwaysAwake S)
      (Restated.runAll M S Sched x v n) (Restated.runAllPath M S Sched x v n) := by
  constructor
  intro v₀ B t hproc a haB hah
  have hav : a.val_index = v := Finset.mem_singleton.1 hah
  obtain ⟨k, hkn, ⟨sm, hsm, hsmmsg⟩, htk⟩ :=
    Restated.mem_sent_of_processes facts S Sched x v n hproc
  have hkt : (x[k].time : Int) ≤ tB := by
    refine le_trans ?_ hn
    exact_mod_cast Restated.time_mono facts S Sched x hkn
  have hcarries : carries sm.msg (.attest a) := by
    rw [hsmmsg]
    exact Or.inr ⟨a, haB, rfl⟩
  have hauthor : NamedObject.author (NamedObject.attest a) = some v := by
    rw [author_attest, hav]
  have hhonest : Restated.HonestThrough M Sched x k v := fun t' ht' => hv t' (le_trans ht' hkt)
  have hcar := hunf.carried k sm (.attest a) v hsm hcarries hauthor hhonest
  obtain ⟨j, hjk, τ, hlbl, haw, out, hout, hst, hemit⟩ :=
    tick_of_honest_signed_upTo_taken facts S Sched x v (.attest a) tB hv hunf hauthor k hkt
      hcar
  refine ⟨(τ : Int), ?_, ?_⟩
  · have hj1 : x[j + 1].time ≤ x[k].time := Restated.time_mono facts S Sched x hjk
    have hj2 : x[j + 1].time = τ := (Restated.tickAllAwake_time facts S Sched x hlbl).2
    rw [← htk]
    exact_mod_cast hj2 ▸ hj1
  · rw [hav]
    exact Restated.emits_runAllPath_of_tick facts S Sched x v (Nat.lt_of_lt_of_le hjk hkn) hlbl
      haw hout hst hemit

/-- If corruption is monotone, signatures are unforgeable and the adversary at `tB` holds less than
    a third of the weight, then the attestations of any two stores of the execution, read at steps
    whose real times are at or before `tB`, hold no slashable weight between them. -/
theorem noSlashableWeightBetween_stores_upTo (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (tB : Int)
    (hmono : Sched.MonotoneCorruption) (hunf : Restated.Unforgeability M S x)
    (hthird : 3 * S.E.electorate.weightOf (Sched.adv tB) < S.E.electorate.totalWeight)
    {i j : Nat} (hi : (x[i].time : Int) ≤ tB) (hj : (x[j].time : Int) ≤ tB)
    (u w : V) :
    ¬ M.HasSlashableWeightBetween S.E
        (M.store_attestations (x[i][u].st).st.core) (M.store_attestations (x[j][w].st).st.core) := by
  intro hev
  obtain ⟨X, hwX, hX⟩ := facts.ev.hasSlashableWeightBetween_elim hev
  -- Some member of the slashable set is outside `Sched.adv tB`.
  obtain ⟨z, hzX, hzB⟩ : ∃ z ∈ X, z ∉ Sched.adv tB := by
    by_cases hsub : X ⊆ Sched.adv tB
    · exfalso
      have hle := S.E.electorate.weightOf_mono hsub
      have hX3 := facts.ev.totalWeight_le_three_mul_weightOf_of_hasIntersectionWeight hwX
      omega
    · exact Finset.not_subset.1 hsub
  -- Monotone corruption lifts that to honesty through every instant at or before `tB`.
  have hzh : HonestThroughTime Sched tB z := fun t' ht' hmem => hzB (hmono t' tB ht' hmem)
  obtain ⟨a, ha, b, hb, hav, hbv, hsl⟩ := facts.ev.slashableBetween_elim (hX z hzX)
  -- One run covers both stores: the run up to the later of the two steps, along the path `x`
  -- follows.
  have hin : i ≤ max i j := le_max_left i j
  have hjn : j ≤ max i j := le_max_right i j
  have hmax : (x[max i j].time : Int) ≤ tB := by
    rcases le_total i j with hle | hle
    · rw [max_eq_right hle]; exact hj
    · rw [max_eq_left hle]; exact hi
  have hhon : z ∈ (Restated.runAll M S Sched x z (max i j)).honest := Finset.mem_singleton_self z
  have hW := Restated.OnePath_runAllPath facts S Sched x z (max i j)
  have hauth := Restated.attestationAuthenticity_runAll_upTo facts S Sched x z (max i j) tB
    hunf hzh hmax
  have hcarA := Restated.Vocabulary.Proofs.NamedStoreBridge.carriedByHonest_of_stateBefore facts
    (Setup.alwaysAwake S) _ hW hauth u (Restated.runEvents M S Sched x i).length
  have hcarB := Restated.Vocabulary.Proofs.NamedStoreBridge.carriedByHonest_of_stateBefore facts
    (Setup.alwaysAwake S) _ hW hauth w (Restated.runEvents M S Sched x j).length
  rw [Restated.runAllPath_runEvents_length facts S Sched x z hin u] at hcarA
  rw [Restated.runAllPath_runEvents_length facts S Sched x z hjn w] at hcarB
  obtain ⟨ra, ta, hra, hea⟩ := hcarA a ha (by rw [hav]; exact hhon)
  obtain ⟨rb, tb, hrb, heb⟩ := hcarB b hb (by rw [hbv]; exact hhon)
  have hsafe := Restated.emissionVoteSafety_of_honest facts (Setup.alwaysAwake S)
    (Restated.runAll M S Sched x z (max i j)) _ hW z hhon ra rb ⟨ta, hav ▸ hea⟩ ⟨tb, hbv ▸ heb⟩
  rw [hra, hrb] at hsafe
  exact hsafe hsl

end

end DecoupledConsensusModel.Sts.Restated
