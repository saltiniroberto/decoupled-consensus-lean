import Model.Record.Wiring
import Proofs.Vocabulary.Protocol.Handlers.HMaxCore
import Proofs.Vocabulary.Execution.ExcludesRefute
import Proofs.Vocabulary.Execution.Runtime
import Proofs.Vocabulary.Protocol.Grades.RowTrace
import Proofs.Vocabulary.Protocol.Handlers.Bridges
import Proofs.Vocabulary.Protocol.Handlers.TickBridges
import Proofs.Vocabulary.Protocol.Handlers.SGArrivalStampCarrier
import Proofs.Claims.SynchronyH
import Proofs.Claims.Spec2Claims.Claim13beRoute3_22
import Proofs.Claims.Spec2Claims.Claim13beRoute3_25
import Proofs.Claims.Spec2Claims.Claim13beRoute3_43
import Proofs.Claims.Spec2Claims.Claim13beRoute3_44

/-!
# The run vocabulary

Definitions and lemmas over the runs `Record.Run V` and their events `Record.Event V`: the index of
the first event at or after an instant, the cut of a run at an instant, the weight bounds read up to
a run's horizon, and the facts about a run sorted by key. The last section relates each definition
at a run embedded by `Record.Run.ofVocabulary` to the same definition at the `NamedRun` it embeds.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog (Schedule)

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The event indices of an instant -/

section EventIndex

/-- The number of events of the run `rho` at instants strictly before `t`; in a run sorted by key,
    the index of the first event at or after `t`. -/
def strictEventIndex (rho : Record.Run V) (t : Time) : Nat :=
  (rho.events.filter (fun e => decide (e.time < t))).length

/-- The number of events of the run `rho` at instants at or before `t`. -/
def inclusiveEventIndex (rho : Record.Run V) (t : Time) : Nat :=
  (rho.events.filter (fun e => decide (e.time ≤ t))).length

omit [DecidableEq V] [Fintype V] in
/-- If `t ≤ u`, at most as many events of `rho` happen before `t` as before `u`. -/
theorem strictEventIndex_mono
    (rho : Record.Run V) {t u : Time} (htu : t ≤ u) :
    strictEventIndex rho t ≤ strictEventIndex rho u := by
  unfold strictEventIndex
  exact (List.monotone_filter_right rho.events
    (fun e he => by
      simp only [decide_eq_true_eq] at he ⊢
      exact lt_of_lt_of_le he htu)).length_le

omit [DecidableEq V] [Fintype V] in
/-- If `t ≤ u`, at most as many events of `rho` happen at or before `t` as at or before `u`. -/
theorem inclusiveEventIndex_mono
    (rho : Record.Run V) {t u : Time} (htu : t ≤ u) :
    inclusiveEventIndex rho t ≤ inclusiveEventIndex rho u := by
  unfold inclusiveEventIndex
  exact (List.monotone_filter_right rho.events
    (fun e he => by
      simp only [decide_eq_true_eq] at he ⊢
      exact he.trans htu)).length_le

omit [DecidableEq V] [Fintype V] in
/-- At most as many events of `rho` happen before `t` as at or before `t`. -/
theorem strictEventIndex_le_inclusiveEventIndex
    (rho : Record.Run V) (t : Time) :
    strictEventIndex rho t ≤ inclusiveEventIndex rho t := by
  unfold strictEventIndex inclusiveEventIndex
  exact (List.monotone_filter_right rho.events
    (fun e he => by
      simp only [decide_eq_true_eq] at he ⊢
      exact le_of_lt he)).length_le

omit [DecidableEq V] [Fintype V] in
/-- The number of events of `rho` before `t` is the number at or before `t - 1`, instants being
    integers. -/
theorem strictEventIndex_eq_inclusiveEventIndex_pred
    (rho : Record.Run V) (t : Time) :
    strictEventIndex rho t = inclusiveEventIndex rho (t - 1) := by
  have hfilter :
      (fun e : Record.Event V => decide (e.time < t)) =
        (fun e : Record.Event V => decide (e.time ≤ t - 1)) := by
    funext e
    exact Bool.decide_congr (Int.le_sub_one_iff).symm
  unfold strictEventIndex inclusiveEventIndex
  rw [hfilter]

omit [DecidableEq V] [Fintype V] in
/-- If `d ≤ read`, at most as many events of `rho` happen before `d` as before `read`. -/
theorem strict_filter_length_mono (rho : Record.Run V) {d read : Time}
    (hdr : d ≤ read) :
    (rho.events.filter (fun e => decide (e.time < d))).length ≤
      (rho.events.filter (fun e => decide (e.time < read))).length :=
  (List.monotone_filter_right rho.events
    (fun e he => by
      simp only [decide_eq_true_eq] at he ⊢
      exact lt_of_lt_of_le he hdr)).length_le

omit [DecidableEq V] [Fintype V] in
/-- If `early ≤ late`, at most as many events of `rho` happen before `early` as before `late`. -/
theorem strict_lengths_mono (rho : Record.Run V) {early late : Time} (ht : early ≤ late) :
    (rho.events.filter (fun e => decide (e.time < early))).length ≤
      (rho.events.filter (fun e => decide (e.time < late))).length := by
  have hsub := List.Sublist.filter (fun e : Record.Event V => decide (e.time < late))
    (List.filter_sublist (p := fun e : Record.Event V => decide (e.time < early))
      (l := rho.events))
  have hs : (rho.events.filter (fun e => decide (e.time < early))).filter
      (fun e => decide (e.time < late)) = rho.events.filter (fun e => decide (e.time < early)) := by
    apply List.filter_eq_self.mpr
    intro e he
    have hearly : e.time < early := by
      simpa only [decide_eq_true_eq] using (List.mem_filter.mp he).2
    simpa only [decide_eq_true_eq] using hearly.trans_le ht
  rw [hs] at hsub
  exact hsub.length_le

end EventIndex

/-! ## The key order and the instant -/

section Key

omit [DecidableEq V] [Fintype V] in
/-- An event whose key is at most another's happens no later. -/
theorem time_le_of_key_le {e f : Record.Event V}
    (h : Record.Event.key e ≤ Record.Event.key f) : e.time ≤ f.time := by
  rcases Prod.Lex.le_iff.mp h with h' | ⟨h', _⟩
  · exact le_of_lt h'
  · exact le_of_eq h'

omit [DecidableEq V] [Fintype V] in
/-- If `f` happens before `t` and `e`'s key is at most `f`'s, then `e` happens before `t`. -/
theorem downward_lt (t : Time) :
    ∀ e f : Record.Event V, Record.Event.key e ≤ Record.Event.key f →
      decide (f.time < t) = true → decide (e.time < t) = true := by
  intro e f hk hf
  simp only [decide_eq_true_eq] at hf ⊢
  exact lt_of_le_of_lt (time_le_of_key_le hk) hf

omit [DecidableEq V] [Fintype V] in
/-- If `f` happens at or before `t` and `e`'s key is at most `f`'s, then `e` happens at or before
    `t`. -/
theorem downward_le (t : Time) :
    ∀ e f : Record.Event V, Record.Event.key e ≤ Record.Event.key f →
      decide (f.time ≤ t) = true → decide (e.time ≤ t) = true := by
  intro e f hk hf
  simp only [decide_eq_true_eq] at hf ⊢
  exact le_trans (time_le_of_key_le hk) hf

omit [DecidableEq V] [Fintype V] in
/-- An event's instant `Record.Event.time e` equals itself, proved by cases on the event. -/
theorem namedEvent_time_eq (e : Record.Event V) :
    Record.Event.time e = Record.Event.time e := by
  cases e <;> rfl

end Key

/-! ## Runs sorted by key -/

section Sorted

omit [DecidableEq V] [Fintype V] in
/-- In a run sorted by key, the events passing a test closed downward along the key order are a
    prefix of the run. -/
theorem filter_eq_take_of_sorted {ρ : Record.Run V}
    (hsorted : ρ.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    (p : Record.Event V → Bool)
    (hdc : ∀ e f : Record.Event V, Record.Event.key e ≤ Record.Event.key f →
      p f = true → p e = true) :
    ρ.events.filter p = ρ.events.take (ρ.events.filter p).length := by
  refine List.prefix_iff_eq_take.mp ?_
  rw [Proofs.Bridges.filter_eq_takeWhile_of_pairwise hdc _ hsorted]
  exact List.takeWhile_prefix _

omit [DecidableEq V] [Fintype V] in
/-- In a run sorted by key, no event at an index at or past the number of events passing a test
    closed downward along the key order passes it. -/
theorem filter_false_of_index_ge_of_sorted {ρ : Record.Run V}
    (hsorted : ρ.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    (p : Record.Event V → Bool)
    (hdc : ∀ e f : Record.Event V, Record.Event.key e ≤ Record.Event.key f →
      p f = true → p e = true)
    {j : Nat} {e : Record.Event V} (hj : (ρ.events.filter p).length ≤ j)
    (hget : ρ.events[j]? = some e) : p e = false := by
  set n := (ρ.events.filter p).length with hn
  have hfilt : ρ.events.filter p = ρ.events.take n := filter_eq_take_of_sorted hsorted p hdc
  have hdropnil : (ρ.events.drop n).filter p = [] := by
    have h1 : ρ.events.filter p
        = (ρ.events.take n).filter p ++ (ρ.events.drop n).filter p := by
      conv_lhs => rw [← List.take_append_drop n ρ.events]
      rw [List.filter_append]
    have h2 : (ρ.events.take n).filter p = ρ.events.take n := by
      conv_lhs => rw [← hfilt]
      rw [List.filter_filter]
      simp only [Bool.and_self]
      exact hfilt
    rw [h2, ← hfilt] at h1
    exact List.self_eq_append_right.mp h1
  have hmem : e ∈ ρ.events.drop n := by
    refine List.mem_of_getElem? (i := j - n) ?_
    rw [List.getElem?_drop]
    have hjn : n + (j - n) = j := by omega
    rw [hjn]
    exact hget
  by_contra hcon
  have hin : e ∈ (ρ.events.drop n).filter p :=
    List.mem_filter.mpr ⟨hmem, by simpa using hcon⟩
  rw [hdropnil] at hin
  simp at hin

omit [DecidableEq V] [Fintype V] in
/-- In a run sorted by key, every event at an index less than the number of events passing a test
    closed downward along the key order passes it. -/
theorem filter_true_of_index_lt_of_sorted {ρ : Record.Run V}
    (hsorted : ρ.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    (p : Record.Event V → Bool)
    (hdc : ∀ e f : Record.Event V, Record.Event.key e ≤ Record.Event.key f →
      p f = true → p e = true)
    {j : Nat} {e : Record.Event V} (hj : j < (ρ.events.filter p).length)
    (hget : ρ.events[j]? = some e) : p e = true := by
  have hmem : e ∈ ρ.events.filter p := by
    rw [filter_eq_take_of_sorted hsorted p hdc]
    exact List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hj]; exact hget)
  exact (List.mem_filter.mp hmem).2

omit [DecidableEq V] [Fintype V] in
/-- In a run sorted by key, no event at an index at or past the number of events passing a test
    closed downward along the key order passes it; `filter_false_of_index_ge_of_sorted` with the run
    first. -/
theorem filter_false_of_index_ge_sorted (rho : Record.Run V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key))
    (p : Record.Event V → Bool)
    (hdown : ∀ e f : Record.Event V, e.key ≤ f.key → p f = true → p e = true)
    {j : Nat} {e : Record.Event V} (hj : (rho.events.filter p).length ≤ j)
    (hget : rho.events[j]? = some e) : p e = false :=
  filter_false_of_index_ge_of_sorted hsorted p hdown hj hget

omit [DecidableEq V] [Fintype V] in
/-- In a run sorted by key, the event at an index at or past the number of events before `t` happens
    at or after `t`. -/
theorem le_time_of_index_ge_of_sorted {ρ : Record.Run V}
    (hsorted : ρ.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {t : Time} {j : Nat} {e : Record.Event V}
    (hj : (ρ.events.filter (fun e => decide (e.time < t))).length ≤ j)
    (hget : ρ.events[j]? = some e) : t ≤ e.time := by
  have h := filter_false_of_index_ge_of_sorted hsorted _ (downward_lt t) hj hget
  simpa using h

omit [DecidableEq V] [Fintype V] in
/-- In a run sorted by key, if the event at index `j` happens before `cut`, more than `j` events
    happen before `cut`. -/
theorem index_succ_le_strict_filter_length (rho : Record.Run V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key)) (cut : Time)
    {j : Nat} {e : Record.Event V} (he : rho.events[j]? = some e)
    (ht : e.time < cut) :
    j + 1 ≤ (rho.events.filter (fun x => decide (x.time < cut))).length := by
  obtain ⟨hjLen, hjGet⟩ := List.getElem?_eq_some_iff.mp he
  have htake : (rho.events.take (j + 1)).filter (fun x => decide (x.time < cut)) =
      rho.events.take (j + 1) := by
    apply List.filter_eq_self.mpr
    intro x hx
    simp only [decide_eq_true_eq]
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hx
    have hklt : k < j + 1 := by
      have hlen := (List.getElem?_eq_some_iff.mp hk).1
      rw [List.length_take] at hlen
      exact hlen.trans_le (Nat.min_le_left _ _)
    have hkRun : rho.events[k]? = some x := by
      simpa only [List.getElem?_take_of_lt hklt] using hk
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ hklt) with hkj | rfl
    · obtain ⟨hkLen, hkGet⟩ := List.getElem?_eq_some_iff.mp hkRun
      have hkey := (List.pairwise_iff_getElem.mp hsorted) k j hkLen hjLen hkj
      rw [hkGet, hjGet] at hkey
      exact (time_le_of_key_le hkey).trans_lt ht
    · have hxe : x = e := Option.some.inj (hkRun.symm.trans he)
      simpa only [hxe] using ht
  have hsplit : rho.events.filter (fun x => decide (x.time < cut)) =
      (rho.events.take (j + 1)).filter (fun x => decide (x.time < cut)) ++
      (rho.events.drop (j + 1)).filter (fun x => decide (x.time < cut)) := by
    conv_lhs => rw [← List.take_append_drop (j + 1) rho.events]
    rw [List.filter_append]
  have hlength := congrArg List.length hsplit
  rw [htake, List.length_append, List.length_take,
    Nat.min_eq_left (Nat.succ_le_of_lt hjLen)] at hlength
  omega

omit [DecidableEq V] [Fintype V] in
/-- In a run sorted by key, the event at index `i` happens no later than the event at an index
    `j ≥ i`. -/
theorem event_time_le (rho : Record.Run V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key))
    {i j : Nat} {e f : Record.Event V} (he : rho.events[i]? = some e)
    (hf : rho.events[j]? = some f) (hij : i ≤ j) : e.time ≤ f.time := by
  rcases lt_or_eq_of_le hij with hij | rfl
  · obtain ⟨hi, hgeti⟩ := List.getElem?_eq_some_iff.mp he
    obtain ⟨hj, hgetj⟩ := List.getElem?_eq_some_iff.mp hf
    have hk := (List.pairwise_iff_getElem.mp hsorted) i j hi hj hij
    rw [hgeti, hgetj] at hk
    rcases Prod.Lex.le_iff.mp hk with hl | ⟨heq, _⟩
    · exact hl.le
    · exact heq.le
  · have hef : e = f := Option.some.inj (he.symm.trans hf)
    exact (congrArg Record.Event.time hef).le

omit [DecidableEq V] [Fintype V] in
/-- In a run sorted by key, the event at index `j` has key at most the key of the event at a later
    index `i`. -/
theorem key_le_of_index_lt_of_sorted {ρ : Record.Run V}
    (hsorted : ρ.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {j i : Nat} {e f : Record.Event V} (hji : j < i)
    (hj : ρ.events[j]? = some e) (hi : ρ.events[i]? = some f) :
    Record.Event.key e ≤ Record.Event.key f := by
  obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hj
  obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
  have hp := (List.pairwise_iff_getElem.mp hsorted) j i hjl hil hji
  rw [hje, hie] at hp
  exact hp

end Sorted

/-! ## Ticks at one index -/

section Ticks

/-- A tick event sits at one index only: if the event at index `j` of `rho` is a tick and the event
    at index `k` is the same event, then `j = k`. -/
def TickIndexUnique (rho : Record.Run V) : Prop :=
  ∀ {j k : Nat} {hj : j < rho.events.length} {hk : k < rho.events.length} {v : V} {t : Int},
    rho.events[j] = Record.Event.tick v t → rho.events[j] = rho.events[k] → j = k

omit [DecidableEq V] [Fintype V] in
/-- In a run satisfying `TickIndexUnique`, two indices that both hold the tick of `v` at `t` are the
    same index. -/
theorem tick_index_eq_of_unique {rho : Record.Run V} (huniq : TickIndexUnique rho)
    {i j : Nat} {v : V} {t : Int}
    (hi : rho.events[i]? = some (Record.Event.tick v t))
    (hj : rho.events[j]? = some (Record.Event.tick v t)) : i = j := by
  obtain ⟨hil, hiv⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hjl, hjv⟩ := List.getElem?_eq_some_iff.mp hj
  exact huniq hiv (hiv.trans hjv.symm)

/-- Every member of the honest set of `rho` has a tick event at every public instant `t` with
    `t₀ ≤ t`, `0 < t` and `t` at most the horizon. -/
def TickTotalFrom (S : Setup V) (rho : Record.Run V) (t₀ : Int) : Prop :=
  ∀ v ∈ rho.honest, ∀ t, Execution.PublicTime S t → t₀ ≤ t → 0 < t → t ≤ rho.horizon →
    Record.Event.tick v t ∈ rho.events

/-- Every validator in `Sched.awake t` and not in `Sched.adv t`, at a public instant `t` with
    `0 < t` and `t` at most the horizon of `rho`, has a tick event at `t` in `rho`. -/
def TickAtAwake (S : Setup V) (Sched : Schedule V) (rho : Record.Run V) : Prop :=
  ∀ v t, Execution.PublicTime S t → 0 < t → t ≤ rho.horizon → v ∈ Sched.awake t →
    v ∉ Sched.adv t → Record.Event.tick v t ∈ rho.events

end Ticks

/-! ## The weight bounds up to a run's horizon, and the progress deadline -/

section Weights

/-- At every instant `t` up to the horizon of `rho`, the validators outside `Hs t` weigh less than a
    third of the total. -/
def BelowOneThirdOn (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V) : Prop :=
  ∀ t : Int, t ≤ rho.horizon → Execution.BelowOneThird S (Hs t)

/-- At every instant `t` up to the horizon of `rho`, the set `Hs t` weighs more than the validators
    outside it. -/
def HonestWeightMajorityOn (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V) : Prop :=
  ∀ t : Int, t ≤ rho.horizon → Execution.HonestWeightMajority S (Hs t)

/-- If at every instant up to the horizon the validators outside the set weigh less than a third,
    the set weighs more than the rest at every such instant. -/
theorem honestWeightMajorityOn_of_belowOneThirdOn {S : Setup V} {rho : Record.Run V}
    {Hs : Int → Finset V} (h : BelowOneThirdOn S rho Hs) : HonestWeightMajorityOn S rho Hs :=
  fun t ht => Proofs.AlignedRoundLemmas.honestWeightMajority_of_belowOneThird (h t ht)

/-- The round `rGST + 1 + (1 + (D + K + 5) · progressLag' gap delayExtra)`; it does not read the
    run. -/
noncomputable def fgSafetyProgressDeadline
    (S : Setup V) (rho : Record.Run V) (rGST gap : Round) (delayExtra : Nat := 0) : Round :=
  rGST + 1 +
    (1 + (S.cfg.D + S.cfg.K + 5) * Proofs.HealingSurface.progressLag' gap delayExtra)

end Weights

/-! ## A run cut at an instant -/

section Cut

omit [DecidableEq V] [Fintype V] in
/-- The run `rho` cut at the instant `T`: it keeps the events of `rho` at instants at most `T`, in
    `rho`'s order, has horizon `T`, and declares `X` honest. -/
def cutRun (rho : Record.Run V) (X : Finset V) (T : Int) : Record.Run V :=
  { honest := X
    horizon := T
    events := rho.events.filter (fun e => decide (Record.Event.time e ≤ T)) }

omit [DecidableEq V] [Fintype V] in
/-- The event list of `rho` is its events at instants up to `T`, followed only by events at instants
    after `T`. -/
def CutSuffix (rho : Record.Run V) (T : Int) : Prop :=
  ∃ l : List (Record.Event V),
    rho.events = rho.events.filter (fun e => decide (Record.Event.time e ≤ T)) ++ l ∧
      ∀ e ∈ l, T < Record.Event.time e

omit [DecidableEq V] [Fintype V] in
/-- Under `CutSuffix rho T`, `rho`'s events are those of `cutRun rho X T` followed by events
    strictly after `T`. -/
theorem CutSuffix.append {rho : Record.Run V} {T : Int} (hsuf : CutSuffix rho T)
    (X : Finset V) :
    ∃ l : List (Record.Event V), rho.events = (cutRun rho X T).events ++ l ∧
      ∀ e ∈ l, T < Record.Event.time e :=
  hsuf

omit [DecidableEq V] [Fintype V] in
/-- Under `CutSuffix rho T`, the event list of `cutRun rho X T` is a prefix of `rho`'s. -/
theorem CutSuffix.prefix {rho : Record.Run V} {T : Int} (hsuf : CutSuffix rho T)
    (X : Finset V) :
    (cutRun rho X T).events <+: rho.events := by
  obtain ⟨l, hl, -⟩ := hsuf.append X
  exact ⟨l, hl.symm⟩

omit [DecidableEq V] [Fintype V] in
/-- Under `CutSuffix rho T`, an event of `rho` at an instant at most `T` sits at the same index in
    `cutRun rho X T`. -/
theorem CutSuffix.getElem? {rho : Record.Run V} {T : Int} (hsuf : CutSuffix rho T)
    (X : Finset V) {i : Nat} {e : Record.Event V} (he : rho.events[i]? = some e)
    (hte : Record.Event.time e ≤ T) :
    i < (cutRun rho X T).events.length ∧ (cutRun rho X T).events[i]? = some e := by
  obtain ⟨l, hl, hlate⟩ := hsuf.append X
  have hlt : i < (cutRun rho X T).events.length := by
    by_contra hge
    rw [hl, List.getElem?_append_right (Nat.le_of_not_lt hge)] at he
    exact absurd (hlate e (List.mem_of_getElem? he)) (not_lt.2 hte)
  refine ⟨hlt, ?_⟩
  rw [hl, List.getElem?_append_left hlt] at he
  exact he

omit [DecidableEq V] [Fintype V] in
/-- If `rho`'s events are a prefix of `rho'`'s and `i` is an index of `rho`, the event at `i` is the
    same in both. -/
theorem getElem?_of_prefix {rho rho' : Record.Run V} (h : rho.events <+: rho'.events) {i : Nat}
    (hi : i < rho.events.length) : rho'.events[i]? = rho.events[i]? := by
  obtain ⟨l, hl⟩ := h
  rw [← hl, List.getElem?_append_left hi]

omit [DecidableEq V] [Fintype V] in
/-- An event of `cutRun rho X T` is an event of `rho` at an instant at most `T`. -/
theorem mem_events_of_cutRun {rho : Record.Run V} {X : Finset V} {T : Int} {e : Record.Event V}
    (he : e ∈ (cutRun rho X T).events) : e ∈ rho.events ∧ Record.Event.time e ≤ T := by
  obtain ⟨h1, h2⟩ := List.mem_filter.1 he
  exact ⟨h1, by simpa using h2⟩

end Cut

/-! ## The objects a run delivers -/

section Objects

/-- The objects the deliveries of the run `rho` carry, in event order; a wake and a tick carry none. -/
def objects (rho : Record.Run V) : List (NamedObject V) :=
  rho.events.filterMap Record.Event.object?

omit [DecidableEq V] [Fintype V] in
/-- If the event at index `i` of `rho` delivers `o`, then `o` is an object of `rho`. -/
theorem objects_of_delivery (rho : Record.Run V) {i : Nat} {v : V} {o : NamedObject V}
    {t : Time} (hi : rho.events[i]? = some (.deliver v o t)) : o ∈ objects rho := by
  exact List.mem_filterMap.mpr ⟨.deliver v o t, List.mem_of_getElem? hi, rfl⟩

omit [DecidableEq V] [Fintype V] in
/-- If the block `B` is an object of `ρ`, some index of `ρ` holds a delivery of `B`. -/
theorem exists_deliver_of_mem_objects (ρ : Record.Run V) {B : NamedBlock V}
    (h : NamedObject.block B ∈ objects ρ) :
    ∃ (i : Nat) (u : V) (t : Time),
      ρ.events[i]? = some (Record.Event.deliver u (NamedObject.block B) t) := by
  obtain ⟨e, hmem, he⟩ := List.mem_filterMap.mp h
  cases e with
  | wake u t => simp only [Record.Event.object?, reduceCtorEq] at he
  | tick u t => simp only [Record.Event.object?, reduceCtorEq] at he
  | deliver u o t =>
      simp only [Record.Event.object?, Option.some.injEq] at he
      subst he
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hmem
      exact ⟨i, u, t, hi⟩

end Objects

/-! ## Runs embedded by `Record.Run.ofVocabulary` -/

section OfVocabulary

omit [DecidableEq V] [Fintype V] in
private theorem filter_map_ofVocabulary_time (l : List (NamedEvent V)) (q : Time → Bool) :
    (l.map Record.Event.ofVocabulary).filter (fun e => q e.time) =
      (l.filter (fun e => q (NamedEvent.time e))).map Record.Event.ofVocabulary := by
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro e _
  simp only [Function.comp_apply, Record.Event.ofVocabulary_time]

omit [DecidableEq V] [Fintype V] in
/-- `strictEventIndex` of a run embedded by `Record.Run.ofVocabulary` is the `strictEventIndex` of the
    `NamedRun` it embeds. -/
@[record_ofVocabulary]
theorem strictEventIndex_ofVocabulary (rho : NamedRun V) (t : Time) :
    Restated.strictEventIndex (Record.Run.ofVocabulary rho) t =
      _root_.DecoupledConsensusModel.Proofs.HealingSurface.strictEventIndex rho t := by
  unfold Restated.strictEventIndex
    _root_.DecoupledConsensusModel.Proofs.HealingSurface.strictEventIndex
  rw [Record.Run.ofVocabulary_events,
    filter_map_ofVocabulary_time rho.events (fun s => decide (s < t)), List.length_map]

omit [DecidableEq V] [Fintype V] in
/-- `inclusiveEventIndex` of a run embedded by `Record.Run.ofVocabulary` is the `inclusiveEventIndex`
    of the `NamedRun` it embeds. -/
@[record_ofVocabulary]
theorem inclusiveEventIndex_ofVocabulary (rho : NamedRun V) (t : Time) :
    Restated.inclusiveEventIndex (Record.Run.ofVocabulary rho) t =
      _root_.DecoupledConsensusModel.Proofs.HealingSurface.inclusiveEventIndex rho t := by
  unfold Restated.inclusiveEventIndex
    _root_.DecoupledConsensusModel.Proofs.HealingSurface.inclusiveEventIndex
  rw [Record.Run.ofVocabulary_events,
    filter_map_ofVocabulary_time rho.events (fun s => decide (s ≤ t)), List.length_map]

omit [DecidableEq V] [Fintype V] in
/-- The objects of a run embedded by `Record.Run.ofVocabulary` are the objects of the `NamedRun` it
    embeds. -/
@[record_ofVocabulary]
theorem objects_ofVocabulary (rho : NamedRun V) :
    Restated.objects (Record.Run.ofVocabulary rho) = NamedRun.objects rho := by
  unfold Restated.objects NamedRun.objects
  rw [Record.Run.ofVocabulary_events, List.filterMap_map]
  congr 1
  funext e
  simp only [Function.comp_apply, Record.Event.ofVocabulary_object?]

end OfVocabulary

end DecoupledConsensusModel.Sts.Restated
