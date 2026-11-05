module
public import GoldilocksVariant.WiringDefs
public import GoldilocksVariant.Final.Instance
public import GoldilocksCorrectness.Record.Facts
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.RunFactsDefs

@[expose] public section

/-!
# What the steps of a run of Goldilocks do to its trace

For a run `π` of `variantProtocolOf M S`, read as the trace `toTrace (M.initial S.C) π`
(`GoldilocksVariant.Final.Projection`), the fields of `RunFacts M S (toTrace (M.initial S.C) π)` one
by one: the time and the sent log at the start and along the trace, the initial states, a tick, a
restart, a delivery, and a step that is not the validator's own.

The tick's and the restart's fields rest on the node invariant `nodeOk_exec`, which needs the model's
facts `F`. `runFacts_toTrace` gathers the fields.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace GoldilocksVariant.Final

open RStsVariant2 (Exec Execution Envelope Action Step Config Local NodeStepResult NodeEffect
  NodeAction applyNodeStepResult applyEffects receive)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace)
open GoldilocksCorrectness.Record (GoldilocksModel Facts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open Goldilocks (NamedObject RootOrder)
open Goldilocks.Sts (Setup)

/-! ## 1. Local states along a run (any protocol) -/

section Generic

variable {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
  {Pr : RStsVariant2.Protocol Node Msg NodeState Ev}

/-- A step after which a known local state of `v` is unknown is a step after which `v` is
corrupted: only a corruption makes a known local state unknown (the bare framework).

The variables:
- `h`: the step from `c` to `c'` labelled `a`; `v`: the validator. -/
theorem mem_adv_of_step_getElem_eq_none {a : Action Node Msg Ev} {c c' : Config Node Msg NodeState}
    (h : Step Pr a c c') {v : Node} (hc : c[v] ≠ none) (hc' : c'[v] = none) : v ∈ c'.adv := by
  refine h.elim (motive := fun _ d d' => d[v] ≠ none → d'[v] = none → v ∈ d'.adv)
    ?setClock ?tick ?deliver ?deliverAdv ?corrupt ?crash ?crashDuring ?restart ?custom
    ?adversarial hc hc'
  case setClock =>
    intro d w t _ _ hc hc'
    exact absurd hc' hc
  case tick =>
    intro d w _ _ res _ _ _ _ _ hc hc'
    exact absurd ((RStsVariant2.applyNodeStepResult_getElem_eq_none_iff Pr w v res d).1 hc') hc
  case deliver =>
    intro d w e _ _ res _ _ _ _ _ _ _ hc hc'
    exact absurd ((RStsVariant2.applyNodeStepResult_getElem_eq_none_iff Pr w v res _).1 hc') hc
  case deliverAdv =>
    intro d w e _ _ _ hc hc'
    exact absurd hc' hc
  case corrupt =>
    intro d w _ hc hc'
    by_cases hvw : v = w
    · subst hvw; exact Finset.mem_insert_self v d.adv
    · exact absurd ((RStsVariant2.Config.setNode_other w v none d hvw).symm.trans hc') hc
  case crash =>
    intro d w _ hc hc'
    exact absurd hc' hc
  case crashDuring =>
    intro d w na k _ _ res _ _ _ _ hc hc'
    rw [RStsVariant2.applyCrashDuring_getElem_eq_none_iff, RStsVariant2.NodeAction.prepare_getElem]
      at hc'
    exact absurd hc' hc
  case restart =>
    intro d w keep t _ _ _ hc hc'
    by_cases hvw : v = w
    · subst hvw
      exact absurd ((RStsVariant2.Config.setNode_self v _ d).symm.trans hc') (by simp)
    · exact absurd ((RStsVariant2.Config.setNode_other w v _ d hvw).symm.trans hc') hc
  case custom =>
    intro d w ev _ _ res _ _ _ _ _ _ hc hc'
    exact absurd ((RStsVariant2.applyNodeStepResult_getElem_eq_none_iff Pr w v res d).1 hc') hc
  case adversarial =>
    intro d w m recipients _ hc hc'
    exact absurd hc' hc

/-- A validator whose local state is unknown in configuration `i` and that is not corrupted there
has had an unknown local state in every configuration up to the `i`-th: it has never come online
(the bare framework).

Why: a known local state becomes unknown only at the validator's corruption
(`mem_adv_of_step_getElem_eq_none`), and corruption is permanent.

The variables:
- `π`: the execution; `i`: the configuration; `v`: the validator; `i'`: an earlier configuration. -/
theorem getElem_eq_none_of_le (π : Exec Pr) {i : ℕ} {v : Node} (hn : π[i][v] = none)
    (hv : v ∉ π[i].adv) {i' : ℕ} (hi' : i' ≤ i) : π[i'][v] = none := by
  induction i with
  | zero =>
    obtain rfl : i' = 0 := by omega
    exact hn
  | succ i ih =>
    by_cases hii : i' = i + 1
    · subst hii; exact hn
    · have hv' : v ∉ π[i].adv := fun hm => hv (π.adv_mono (Nat.le_succ i) hm)
      have hn' : π[i][v] = none := by
        by_contra hne
        exact hv (mem_adv_of_step_getElem_eq_none (π.step_at i) hne hn)
      exact ih hn' hv' (by omega)

/-- The last known state of a validator whose local state is unknown and that is not corrupted is
`init v` (the projection's reader, any protocol).

The variables:
- `init`: the node states before a local state is known; `π`: the execution; `i`: the
  configuration; `v`: the validator. -/
theorem lastKnownSt_eq_init_of_none (init : (v : Node) → NodeState) (π : Exec Pr) {i : ℕ}
    {v : Node} (hn : π[i][v] = none) (hv : v ∉ π[i].adv) : lastKnownSt init π i v = init v := by
  induction i with
  | zero => exact lastKnownSt_zero init π v
  | succ i ih =>
    rw [lastKnownSt_succ_of_none init π hn]
    exact ih (getElem_eq_none_of_le π hn hv (Nat.le_succ i))
      (fun hm => hv (π.adv_mono (Nat.le_succ i) hm))

/-- A step that leaves `v`'s local state as it was keeps `v`'s last known state (the projection's
reader, any protocol).

The variables:
- `init`: the node states before a local state is known; `π`: the execution; `i`: the step; `v`:
  the validator. -/
theorem lastKnownSt_succ_of_eq (init : (v : Node) → NodeState) (π : Exec Pr) {i : ℕ} {v : Node}
    (h : π[i + 1][v] = π[i][v]) : lastKnownSt init π (i + 1) v = lastKnownSt init π i v := by
  cases hl : π[i][v] with
  | none => exact lastKnownSt_succ_of_none init π (h.trans hl)
  | some l => rw [lastKnownSt_of_some init π (h.trans hl), lastKnownSt_of_some init π hl]

/-- A step of `π` that is not a tick, a restart or a protocol event of `v`, nor a delivery to `v`
outside the corrupted set, keeps `v`'s last known state (the projection's reader, any protocol).

Why: such a step leaves `v`'s local state as it was, makes it unknown (a corruption), or keeps its
memory (a crash during a reaction).

The variables:
- `init`: the node states before a local state is known; `π`: the execution; `i`: the step; `v`:
  the validator. -/
theorem lastKnownSt_succ_of_not_own (init : (v : Node) → NodeState) (π : Exec Pr) {i : ℕ}
    {v : Node}
    -- the step is not a tick of `v`
    (htick : π.lbl i ≠ .tick v)
    -- a delivery to `v` is taken while `v` is corrupted
    (hdel : ∀ e : Envelope Node Msg, π.lbl i = .deliver v e → v ∈ π[i].adv)
    -- the step is not a restart of `v`
    (hres : ∀ keep : Bool, π.lbl i ≠ .restart v keep)
    -- the step is not a protocol event of `v`
    (hcus : ∀ ev : Ev, π.lbl i ≠ .custom v ev) :
    lastKnownSt init π (i + 1) v = lastKnownSt init π i v := by
  have hs := π.step_at i
  by_cases hcd : ∃ (na : NodeAction Node Msg Ev) (k : ℕ), π.lbl i = .crashDuring v na k
  · obtain ⟨na, k, hl⟩ := hcd
    rw [hl] at hs
    obtain ⟨l, d, hl0, hl1⟩ := RStsVariant2.CrashDuringStep.st hs.2
    rw [RStsVariant2.NodeAction.prepare_getElem] at hl0
    rw [lastKnownSt_of_some init π hl1, lastKnownSt_of_some init π hl0]
  by_cases hcor : π.lbl i = .corrupt v
  · rw [hcor] at hs
    exact lastKnownSt_succ_of_none init π hs.corrupt_eq.2.1
  by_cases hd : ∃ e : Envelope Node Msg, π.lbl i = .deliver v e
  · obtain ⟨e, hl⟩ := hd
    have hadv := hdel e hl
    rw [hl] at hs
    obtain ⟨-, -, heq⟩ := hs.deliver_eq_of_mem_adv hadv
    exact lastKnownSt_succ_of_eq init π (by rw [heq]; rfl)
  push Not at hcd hd
  exact lastKnownSt_succ_of_eq init π (hs.getElem_eq htick hd hcus hcd hcor hres)

/-- Effects that are all sends leave every validator's local state as it was (the bare
framework).

The variables:
- `w`: the reacting validator; `effs`: the effects; `d`: the configuration; `v`: the validator
  read. -/
theorem applyEffects_getElem_of_sends {w v : Node} {effs : List (NodeEffect Node Msg NodeState)}
    (h : ∀ ef ∈ effs, ∃ a : RStsVariant2.Addressed Node Msg, ef = .send a)
    (d : Config Node Msg NodeState) : (applyEffects w effs d)[v] = d[v] := by
  induction effs generalizing d with
  | nil => rfl
  | cons ef effs ih =>
    obtain ⟨a, rfl⟩ := h _ List.mem_cons_self
    rw [RStsVariant2.applyEffects_cons, ih (fun ef hef => h ef (List.mem_cons_of_mem _ hef))]
    rfl

/-- A completed reaction of `v` whose effects are the broadcasts of the objects `os` adds to the
sent log, read as the trace reads it, exactly `os` signed by `v` (the projection, any protocol).

The variables:
- `Pr`: the protocol; `v`: the reacting validator; `n`: its new memory state; `os`: the objects;
  `d`: the configuration. -/
theorem sent_applyNodeStepResult_broadcasts (Pr : RStsVariant2.Protocol Node Msg NodeState Ev)
    {v : Node} {n : NodeState} (os : List Msg) (d : Config Node Msg NodeState) :
    (applyNodeStepResult Pr v ⟨n, os.map (fun o => .send ⟨o, .all⟩)⟩ d).sent.map traceMsg =
      d.sent.map traceMsg + (os : Multiset Msg).map (Framework.StsMultisetLog.SignedMsg.mk v) := by
  rw [RStsVariant2.applyNodeStepResult_sent, RStsVariant2.applyEffects_sent, Multiset.map_add]
  congr 1
  simp [List.filterMap_map, Function.comp_def, traceMsg, RStsVariant2.Addressed.sign]

end Generic

/-! ## 2. The trace's own steps, read on the run (any protocol) -/

section TraceSteps

variable {Node Msg NodeState Ev : Type} [DecidableEq Node] [DecidableEq Msg]
  {Pr : RStsVariant2.Protocol Node Msg NodeState Ev} (init : (v : Node) → NodeState) (π : Exec Pr)

/-- A trace step that is the delivery of `sm` to `v` is the trace step `newIdx π k` of a step `k` of
the run that delivers to `v` an envelope whose signed message is `sm`, with `v` up and outside the
corrupted set in configuration `k`.

The variables:
- `j`: the trace step; `v`: the validator; `sm`: the signed message. -/
theorem exists_of_lbl_deliver {j : ℕ} {v : Node} {sm : Framework.StsMultisetLog.SignedMsg Node Msg}
    (h : (toTrace init π).lbl j = Event.deliver v sm) :
    ∃ (k : ℕ) (e : Envelope Node Msg), newIdx π k = j ∧ π.lbl k = .deliver v e ∧
      traceMsg e = sm ∧ v ∉ π[k].crashed ∧ π[k][v] ≠ none ∧ v ∉ π[k].adv := by
  obtain ⟨k, rfl, hk⟩ := exists_newIdx_of_lbl_ne_other init π (by rw [h]; simp)
  obtain ⟨e, hl, hm, hcr, hs, hadv⟩ := (eventOf_eq_deliver π).1 (hk.symm.trans h)
  exact ⟨k, e, rfl, hl, hm, hcr, hs, hadv⟩

/-- A trace step of the kind `other` that is no step of the run keeps every node state.

The variables:
- `j`: the trace step; `v`: the validator. -/
theorem toTrace_st_succ_of_not {j : ℕ} (h : ¬ ∃ i : ℕ, newIdx π i = j) (v : Node) :
    (toTrace init π).st (j + 1) v = (toTrace init π).st j v := by
  rw [toTrace_st, toTrace_st, origBefore_succ_of_not π h]

/-- A trace step that is not a tick, a restart or a delivery keeps the time: only a step of the kind
`other` moves it (the trace layer's `time_keep`).

The variables:
- `j`: the trace step. -/
theorem toTrace_time_keep (j : ℕ) (h : (toTrace init π).lbl j ≠ Event.other) :
    (toTrace init π).time (j + 1) = (toTrace init π).time j := by
  obtain ⟨i, rfl, -⟩ := exists_newIdx_of_lbl_ne_other init π h
  rw [toTrace_time_newIdx_succ, toTrace_time_newIdx]

/-- Nothing is on the wire at the start of the trace (the trace layer's `sent_zero`). -/
theorem toTrace_sent_zero : (toTrace init π).sent 0 = 0 := by
  rw [toTrace_sent, origBefore_zero, show π[0].sent = 0 from π.init.2.2.2]
  rfl

/-- Each trace step keeps every message already on the wire (the trace layer's `sent_mono`).

The variables:
- `j`: the trace step. -/
theorem toTrace_sent_mono (j : ℕ) : (toTrace init π).sent j ≤ (toTrace init π).sent (j + 1) := by
  rw [toTrace_sent, toTrace_sent]
  exact Multiset.map_le_map (π.sent_mono (origBefore_mono π (Nat.le_succ j)))

end TraceSteps

/-! ## 3. Goldilocks's reactions -/

section Goldilocks

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- A tick reaction of `variantProtocolOf M S` is an `.ok` outcome of the model's tick, its objects
broadcast, or, when the tick has no `.ok` outcome, the state kept and nothing sent (Goldilocks's
wiring).

The variables:
- `v`: the validator; `r`: its clock reading; `n`: its memory state; `res`: the reaction. -/
theorem variant_step_tick {M : GoldilocksModel V} {S : Setup V} {v : V} {r : ℕ} {n : M.N}
    {res : NodeStepResult V M.N (NamedObject V)}
    (h : (variantProtocolOf M S).step v r n .tick res) :
    (∃ p : M.N × List (NamedObject V), Except.ok p ∈ M.tick S.C S.P S.X n (r : Int) ∧
      res = ⟨p.1, p.2.map (fun o => .send ⟨o, .all⟩)⟩) ∨
    res = ⟨n, []⟩ := by
  rcases h with h | ⟨-, rfl⟩
  · exact Or.inl h
  · exact Or.inr rfl

/-- A delivery reaction of `variantProtocolOf M S` is the model's receive, its relays broadcast
(Goldilocks's wiring).

The variables:
- `v`: the validator; `r`: its clock reading; `n`: its memory state; `m`: the signed message
  delivered; `res`: the reaction. -/
theorem variant_step_recv {M : GoldilocksModel V} {S : Setup V} {v : V} {r : ℕ} {n : M.N}
    {m : RStsVariant2.SignedMsg V (NamedObject V)} {res : NodeStepResult V M.N (NamedObject V)}
    (h : (variantProtocolOf M S).step v r n (.recv m) res) :
    res = ⟨M.receive S.C S.P S.X n m.msg,
      (M.relayedObjects m.msg).toList.map (fun o => .send ⟨o, .all⟩)⟩ := by
  rcases h with h | ⟨hempty, -⟩
  · exact h
  · have hmem : (⟨M.receive S.C S.P S.X n m.msg,
        (M.relayedObjects m.msg).toList.map (fun o => .send ⟨o, .all⟩)⟩ :
          NodeStepResult V M.N (NamedObject V)) ∈ variantReactions M S n r (.recv m) := rfl
    rw [hempty] at hmem
    exact absurd hmem (Set.notMem_empty _)

/-- Every reaction of `variantProtocolOf M S` has sends as its only effects (Goldilocks's
wiring).

The variables:
- `v`: the validator; `r`: its clock reading; `n`: its memory state; `e`: the event; `res`: the
  reaction. -/
theorem variant_step_sends {M : GoldilocksModel V} {S : Setup V} {v : V} {r : ℕ} {n : M.N}
    {e : RStsVariant2.Event V (NamedObject V) Empty} {res : NodeStepResult V M.N (NamedObject V)}
    (h : (variantProtocolOf M S).step v r n e res) :
    ∀ ef ∈ res.effects, ∃ a : RStsVariant2.Addressed V (NamedObject V), ef = .send a := by
  cases e with
  | tick =>
    rcases variant_step_tick h with ⟨p, -, rfl⟩ | rfl
    · intro ef hef
      obtain ⟨o, -, rfl⟩ := List.mem_map.1 hef
      exact ⟨_, rfl⟩
    · intro ef hef; cases hef
  | recv m =>
    rw [variant_step_recv h]
    intro ef hef
    obtain ⟨o, -, rfl⟩ := List.mem_map.1 hef
    exact ⟨_, rfl⟩
  | custom ev => exact ev.elim

/-! ## 4. The node invariant along a run -/

/-- `NodeOk M S c v`: when `v`'s local state `l` is known in the configuration `c`, `v`'s clock
exists in `c` with a reading `r`; `v`'s memory state and its disk each satisfy the model's node
invariant with a clock at most `r`; and the memory state is the disk, or a wake of the disk. A
condition on Goldilocks's configurations of the variant, kept by every step.

Read aloud: a validator whose local state is known has a clock; its memory and its disk satisfy the
model's node invariant, each with a clock at most the reading; and its memory is its disk, or its
disk woken at some time.

The variables:
- `M`: the model; `S`: the setup; `c`: the configuration; `v`: the validator. -/
def NodeOk (M : GoldilocksModel V) (S : Setup V) (c : Config V (NamedObject V) M.N) (v : V) :
    Prop :=
  ∀ l : Local V (NamedObject V) M.N, c[v] = some l → ∃ r : ℕ, c.clock v = some r ∧
    M.nodeInv S.C S.P S.X l.st ∧ l.st.t ≤ (r : Int) ∧
    M.nodeInv S.C S.P S.X l.disk ∧ l.disk.t ≤ (r : Int) ∧
    (l.st = l.disk ∨ ∃ t' : Goldilocks.Time, l.st = M.wake l.disk t')

/-- `NodeOk` carries over to a configuration in which `v`'s local state is the same and `v`'s
clock, when it exists, reads at least as much (Goldilocks's configurations of the variant).

The variables:
- `c`, `c'`: the two configurations; `v`: the validator. -/
theorem NodeOk.of_clock_le {M : GoldilocksModel V} {S : Setup V}
    {c c' : Config V (NamedObject V) M.N} {v : V} (hl : c'[v] = c[v])
    -- `v`'s clock in `c'` reads at least its reading in `c`
    (hc : ∀ r : ℕ, c.clock v = some r → ∃ r' : ℕ, c'.clock v = some r' ∧ r ≤ r')
    (h : NodeOk M S c v) : NodeOk M S c' v := by
  intro l hl'
  obtain ⟨r, hr, h1, h2, h3, h4, h5⟩ := h l (hl.symm.trans hl')
  obtain ⟨r', hr', hle⟩ := hc r hr
  have hle' : (r : Int) ≤ (r' : Int) := by exact_mod_cast hle
  exact ⟨r', hr', h1, h2.trans hle', h3, h4.trans hle', h5⟩

/-- `NodeOk` carries over to a configuration in which `v`'s local state and clock are the same
(Goldilocks's configurations of the variant).

The variables:
- `c`, `c'`: the two configurations; `v`: the validator. -/
theorem NodeOk.of_eq {M : GoldilocksModel V} {S : Setup V} {c c' : Config V (NamedObject V) M.N}
    {v : V} (hl : c'[v] = c[v]) (hc : c'.clock v = c.clock v) (h : NodeOk M S c v) :
    NodeOk M S c' v :=
  NodeOk.of_clock_le hl (fun r hr => ⟨r, hc.trans hr, le_rfl⟩) h

/-- A step of `variantProtocolOf M S` keeps `NodeOk` at every validator (Goldilocks's run on the
variant).

Why: a tick runs the model's tick at the clock reading, a delivery its receive, and a restart its
wake at the clock reading; each keeps the invariant and leaves a clock at most the reading
(`NodeInvFacts`); a completed reaction writes its new memory state to the disk. A restart keeps the
disk and wakes the memory or the disk, so the memory becomes a wake of the disk (`Facts.wake_wake`
when it was one already). A validator coming online gets its initial state at its reading on both.
A setting of the clock only raises it, and a crash during a reaction applies sends only.

The variables:
- `F`: the model's facts; `h`: the step from `c` to `c'` labelled `a`; `hc`: `NodeOk` in `c`. -/
theorem nodeOk_step {M : GoldilocksModel V} {S : Setup V} (F : Facts M)
    {a : Action V (NamedObject V) Empty} {c c' : Config V (NamedObject V) M.N}
    (h : Step (variantProtocolOf M S) a c c') (hc : ∀ v : V, NodeOk M S c v) :
    ∀ v : V, NodeOk M S c' v := by
  revert hc
  refine h.elim (motive := fun _ d d' => (∀ v : V, NodeOk M S d v) → ∀ v : V, NodeOk M S d' v)
    ?setClock ?tick ?deliver ?deliverAdv ?corrupt ?crash ?crashDuring ?restart ?custom
    ?adversarial
  case setClock =>
    intro d w t _ hlt hc v
    refine NodeOk.of_clock_le (RStsVariant2.setClock_getElem w v t d) (fun r hr => ?_) (hc v)
    by_cases hvw : v = w
    · subst hvw
      exact ⟨t, RStsVariant2.setClock_clock_self v t d, (hlt r hr).le⟩
    · exact ⟨r, (RStsVariant2.setClock_clock_other w v t d hvw).trans hr, le_rfl⟩
  case tick =>
    intro d w l t res _ _ hl ht hres hc v
    by_cases hvw : v = w
    · subst hvw
      intro l' hl'
      rw [RStsVariant2.applyNodeStepResult_getElem_self_of_some _ v res d hl] at hl'
      obtain rfl := Option.some_injective _ hl'
      obtain ⟨r, hr, hi, hit, -⟩ := hc v l hl
      obtain rfl : r = t := Option.some_injective _ (hr.symm.trans ht)
      have hnew : M.nodeInv S.C S.P S.X res.state ∧ res.state.t ≤ (r : Int) := by
        rcases variant_step_tick hres with ⟨q, hq, rfl⟩ | rfl
        · obtain ⟨h1, -, h3⟩ := F.nd.tick_nodeInv S.C S.P S.X l.st (r : Int) hi hit q.1 q.2 hq
          exact ⟨h1, h3.le⟩
        · exact ⟨hi, hit⟩
      refine ⟨r, ?_, hnew.1, hnew.2, hnew.1, hnew.2, Or.inl rfl⟩
      rw [RStsVariant2.applyNodeStepResult_clock]; exact hr
    · exact NodeOk.of_eq (RStsVariant2.applyNodeStepResult_getElem_other _ w v res d hvw)
        (by rw [RStsVariant2.applyNodeStepResult_clock]) (hc v)
  case deliver =>
    intro d w e l t res _ _ _ _ hl ht hres hc v
    by_cases hvw : v = w
    · subst hvw
      intro l' hl'
      rw [RStsVariant2.applyNodeStepResult_getElem_self_of_some _ v res _
        (by rw [RStsVariant2.receive_getElem]; exact hl)] at hl'
      obtain rfl := Option.some_injective _ hl'
      obtain ⟨r, hr, hi, hit, -⟩ := hc v l hl
      rw [variant_step_recv hres]
      obtain ⟨h1, -, h3⟩ := F.nd.receive_nodeInv S.C S.P S.X l.st e.toSignedMsg.msg hi
      have h4 : (M.receive S.C S.P S.X l.st e.toSignedMsg.msg).t ≤ (r : Int) := by
        exact h3.le.trans hit
      refine ⟨r, ?_, h1, h4, h1, h4, Or.inl rfl⟩
      rw [RStsVariant2.applyNodeStepResult_clock, RStsVariant2.receive_clock]; exact hr
    · exact NodeOk.of_eq
        ((RStsVariant2.applyNodeStepResult_getElem_other _ w v res _ hvw).trans
          (RStsVariant2.receive_getElem w v _ d))
        (by rw [RStsVariant2.applyNodeStepResult_clock, RStsVariant2.receive_clock]) (hc v)
  case deliverAdv =>
    intro d w e _ _ _ hc v
    exact NodeOk.of_eq (RStsVariant2.receive_getElem w v _ d)
      (by rw [RStsVariant2.receive_clock]) (hc v)
  case corrupt =>
    intro d w _ hc v
    by_cases hvw : v = w
    · subst hvw
      intro l hl
      exact absurd ((RStsVariant2.Config.setNode_self v none d).symm.trans hl) (by simp)
    · exact NodeOk.of_eq (RStsVariant2.Config.setNode_other w v none d hvw)
        (if_neg (Ne.symm hvw)) (hc v)
  case crash =>
    intro d w _ hc v
    exact NodeOk.of_eq rfl rfl (hc v)
  case crashDuring =>
    intro d w na k l t res _ _ _ hres hc v
    have hl : (RStsVariant2.applyCrashDuring w res k (na.prepare w d))[v] = d[v] := by
      rw [RStsVariant2.applyCrashDuring_getElem]
      rw [applyEffects_getElem_of_sends
        (fun ef hef => variant_step_sends hres ef (List.mem_of_mem_take hef)) _]
      exact RStsVariant2.NodeAction.prepare_getElem w v d na
    exact NodeOk.of_eq hl
      (by rw [RStsVariant2.applyCrashDuring_clock, RStsVariant2.NodeAction.prepare_clock]) (hc v)
  case restart =>
    intro d w keep t _ _ ht hc v
    by_cases hvw : v = w
    · subst hvw
      intro l' hl'
      have hl'' := (RStsVariant2.Config.setNode_self v _ d).symm.trans hl'
      refine ⟨t, ht, ?_⟩
      cases hl : d[v] with
      | some l =>
        rw [hl] at hl''
        obtain rfl := Option.some_injective _ hl''
        obtain ⟨r, hr, h1, h2, h3, h4, h5⟩ := hc v l hl
        obtain rfl : r = t := Option.some_injective _ (hr.symm.trans ht)
        have hsrc : M.nodeInv S.C S.P S.X (if keep then l.st else l.disk) ∧
            (if keep then l.st else l.disk).t ≤ (r : Int) := by
          cases keep
          · exact ⟨h3, h4⟩
          · exact ⟨h1, h2⟩
        obtain ⟨w1, -, w3⟩ := F.nd.wake_nodeInv S.C S.P S.X _ (r : Int) hsrc.1 hsrc.2
        refine ⟨w1, le_of_eq w3, h3, h4, Or.inr ⟨(r : Int), ?_⟩⟩
        show M.wake (if keep then l.st else l.disk) (r : Int) = M.wake l.disk (r : Int)
        cases keep
        · rfl
        · show M.wake l.st (r : Int) = M.wake l.disk (r : Int)
          rcases h5 with h5 | ⟨t', h5⟩
          · rw [h5]
          · rw [h5, F.wake_wake]
      | none =>
        rw [hl] at hl''
        obtain rfl := Option.some_injective _ hl''
        have hinit : M.nodeInv S.C S.P S.X ((variantProtocolOf M S).init t v) ∧
            ((variantProtocolOf M S).init t v).t ≤ (t : Int) := by
          have hi := F.nd.initial_nodeInv S.C S.P S.X v
          have hc0 : (M.initial S.C v).t = 0 := (F.init.initial_clock S.C v).1
          show M.nodeInv S.C S.P S.X (M.wake (M.initial S.C v) t) ∧
            (M.wake (M.initial S.C v) t).t ≤ (t : Int)
          obtain ⟨w1, -, w3⟩ := F.nd.wake_nodeInv S.C S.P S.X _ (t : Int) hi
            (by rw [hc0]; exact Int.natCast_nonneg t)
          exact ⟨w1, le_of_eq w3⟩
        exact ⟨hinit.1, hinit.2, hinit.1, hinit.2, Or.inl rfl⟩
    · exact NodeOk.of_eq (RStsVariant2.Config.setNode_other w v _ d hvw) rfl (hc v)
  case custom =>
    intro d w ev; exact ev.elim
  case adversarial =>
    intro d w m recipients _ hc v
    exact NodeOk.of_eq rfl rfl (hc v)

/-- **The node invariant along a run** (Goldilocks's run on the variant). In every configuration of
a run of `variantProtocolOf M S`, every validator that is online has a clock, and a memory state and
a disk that satisfy the model's node invariant with a clock at most its reading, the memory being
the disk or a wake of the disk.

Why: no local state is known at the start, and every step keeps the invariant (`nodeOk_step`).

The variables:
- `F`: the model's facts; `π`: the run; `i`: the configuration; `v`: the validator. -/
theorem nodeOk_exec {M : GoldilocksModel V} {S : Setup V} (F : Facts M)
    (π : Exec (variantProtocolOf M S)) (i : ℕ) (v : V) : NodeOk M S π[i] v := by
  induction i generalizing v with
  | zero =>
    intro l hl
    exact absurd ((π.init.1 v).symm.trans hl) (by simp)
  | succ i ih =>
    exact nodeOk_step F (π.step_at i) ih v

/-! ## 5. The fields of `RunFacts` -/

/-- Every validator starts the trace from the model's initial state (the trace layer's `init`).

The variables:
- `π`: the run; `v`: the validator. -/
theorem toTrace_init {M : GoldilocksModel V} {S : Setup V} (π : Exec (variantProtocolOf M S))
    (v : V) : (toTrace (M.initial S.C) π).st 0 v = M.initial S.C v := by
  rw [toTrace_st, origBefore_zero, lastKnownSt_zero]

/-- **A tick of the trace is the model's tick** (the trace layer's `tick`, for Goldilocks's run).
At `v`'s tick to `t`, `v` takes an `.ok` outcome of the model's tick from its node state, and the
step puts exactly that outcome's objects on the wire, signed by `v`.

Why: the step is a tick of `π` taken while `v`'s clock reads `t`, whose reaction is an `.ok` outcome
of the model's tick or, when there is none, the state kept; there is one, since `v`'s memory state
satisfies the node invariant with a clock at most `t` (`nodeOk_exec`, `NodeInvFacts.tick_ok`).

The variables:
- `F`: the model's facts; `π`: the run; `j`: the trace step; `v`: the validator; `t`: the
  reading. -/
theorem toTrace_tick {M : GoldilocksModel V} {S : Setup V} (F : Facts M)
    (π : Exec (variantProtocolOf M S)) (j : ℕ) (v : V) (t : ℕ)
    (h : (toTrace (M.initial S.C) π).lbl j = Event.tick v t) :
    ∃ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X ((toTrace (M.initial S.C) π).st j v) (t : Int) ∧
      (toTrace (M.initial S.C) π).st (j + 1) v = n' ∧
      (toTrace (M.initial S.C) π).sent (j + 1) = (toTrace (M.initial S.C) π).sent j +
        (sent : Multiset (NamedObject V)).map (Framework.StsMultisetLog.SignedMsg.mk v) := by
  obtain ⟨i, rfl, hl, hc⟩ := exists_of_lbl_tick (M.initial S.C) π h
  rw [toTrace_st_newIdx, toTrace_st_newIdx_succ, toTrace_sent_newIdx, toTrace_sent_newIdx_succ]
  have hs := π.step_at i
  rw [hl] at hs
  obtain ⟨-, l, t', res, hlv, ht', hres, heq⟩ := hs
  rw [RStsVariant2.NodeAction.prepare_getElem] at hlv
  rw [RStsVariant2.NodeAction.prepare_clock] at ht'
  obtain rfl : t' = t := Option.some_injective _ (ht'.symm.trans hc)
  have heq' : π[i + 1] = applyNodeStepResult (variantProtocolOf M S) v res π[i] := heq
  have hpost : π[i + 1][v] = some { l with st := res.state, disk := res.state } := by
    rw [heq']; exact RStsVariant2.applyNodeStepResult_getElem_self_of_some _ v res _ hlv
  rw [lastKnownSt_of_some _ π hlv, lastKnownSt_of_some _ π hpost]
  obtain ⟨r, hr, hi, hit, -⟩ := nodeOk_exec F π i v l hlv
  obtain rfl : r = t' := Option.some_injective _ (hr.symm.trans hc)
  obtain ⟨⟨o, ho⟩, hne⟩ := F.nd.tick_ok S.C S.P S.X l.st (r : Int) hi hit
  rcases hres with ⟨q, hq, rfl⟩ | ⟨hempty, -⟩
  · refine ⟨q.1, q.2, hq, rfl, ?_⟩
    rw [heq', sent_applyNodeStepResult_broadcasts]
  · -- no `.ok` outcome is impossible: the tick has an outcome, and no failing one
    exfalso
    change variantReactions M S l.st r .tick = ∅ at hempty
    cases o with
    | error e => exact hne e ho
    | ok q =>
      have hmem : (⟨q.1, q.2.map (fun o => .send ⟨o, .all⟩)⟩ :
          NodeStepResult V M.N (NamedObject V)) ∈ variantReactions M S l.st r .tick :=
        ⟨q, ho, rfl⟩
      rw [hempty] at hmem
      exact Set.notMem_empty _ hmem

/-- **A delivery of the trace is the model's receive** (the trace layer's `deliver`, for
Goldilocks's run). At the delivery of `sm` to `v`, `sm` is on the wire, `v` takes the model's
receive of the object of `sm`, and the step puts the model's relays of that object on the wire,
signed by `v`.

Why: the step is a delivery of `π` to `v` up and outside the corrupted set, whose reaction is the
model's receive with its relays broadcast.

The variables:
- `π`: the run; `j`: the trace step; `v`: the validator; `sm`: the signed message. -/
theorem toTrace_deliver {M : GoldilocksModel V} {S : Setup V} (π : Exec (variantProtocolOf M S))
    (j : ℕ) (v : V) (sm : Framework.StsMultisetLog.SignedMsg V (NamedObject V))
    (h : (toTrace (M.initial S.C) π).lbl j = Event.deliver v sm) :
    sm ∈ (toTrace (M.initial S.C) π).sent j ∧
    (toTrace (M.initial S.C) π).st (j + 1) v =
      M.receive S.C S.P S.X ((toTrace (M.initial S.C) π).st j v) sm.msg ∧
    (toTrace (M.initial S.C) π).sent (j + 1) = (toTrace (M.initial S.C) π).sent j +
      (M.relayedObjects sm.msg).map (Framework.StsMultisetLog.SignedMsg.mk v) := by
  obtain ⟨i, e, rfl, hl, rfl, -, -, hadv⟩ := exists_of_lbl_deliver (M.initial S.C) π h
  rw [toTrace_st_newIdx, toTrace_st_newIdx_succ, toTrace_sent_newIdx, toTrace_sent_newIdx_succ]
  have hs := π.step_at i
  rw [hl] at hs
  have hsent := hs.deliver_sent.1
  obtain ⟨-, hf⟩ := hs
  rcases hf with hf | ⟨-, l, t, res, hlv, -, hres, heq⟩
  · exact absurd hf.1 hadv
  have hlv' : π[i][v] = some l := hlv
  have heq' : π[i + 1] =
      applyNodeStepResult (variantProtocolOf M S) v res (receive v e.toSignedMsg π[i]) := heq
  rw [variant_step_recv hres] at heq'
  have hpost : π[i + 1][v] =
      some ⟨M.receive S.C S.P S.X l.st e.msg, M.receive S.C S.P S.X l.st e.msg⟩ := by
    rw [heq']; exact RStsVariant2.applyNodeStepResult_getElem_self_of_some _ v _ _ hlv
  refine ⟨Multiset.mem_map_of_mem _ hsent, ?_, ?_⟩
  · rw [lastKnownSt_of_some _ π hlv', lastKnownSt_of_some _ π hpost]
    rfl
  · rw [heq', sent_applyNodeStepResult_broadcasts, RStsVariant2.receive_sent, Multiset.coe_toList]
    rfl

/-- **A restart of the trace is the model's wake at the restart's reading** (the trace layer's
`restart`, for Goldilocks's run). At `v`'s restart at the reading `t`, `v` takes the model's wake of
its node state at `t`, and nothing is sent.

Why: the step is a restart of `π` taken while `v`'s clock reads `t`. A known local state `l` becomes
the wake at `t` of `l.st` or of `l.disk`, which agree since `l.st` is `l.disk` or a wake of it
(`nodeOk_exec`, `Facts.wake_wake`). An unknown one becomes `(variantProtocolOf M S).init t v`, which
is the wake at `t` of `M.initial S.C v`, the last known state of a validator that has never come
online.

The variables:
- `F`: the model's facts; `π`: the run; `j`: the trace step; `v`: the validator; `t`: the reading;
  `keep`: whether the memory is kept. -/
theorem toTrace_restart {M : GoldilocksModel V} {S : Setup V} (F : Facts M)
    (π : Exec (variantProtocolOf M S)) (j : ℕ) (v : V) (t : ℕ)
    (keep : Bool) (h : (toTrace (M.initial S.C) π).lbl j = Event.restart v t keep) :
    (toTrace (M.initial S.C) π).st (j + 1) v =
        M.wake ((toTrace (M.initial S.C) π).st j v) (t : Int) ∧
      (toTrace (M.initial S.C) π).sent (j + 1) = (toTrace (M.initial S.C) π).sent j := by
  obtain ⟨i, rfl, hl, hc⟩ := exists_of_lbl_restart (M.initial S.C) π h
  rw [toTrace_st_newIdx, toTrace_st_newIdx_succ, toTrace_sent_newIdx, toTrace_sent_newIdx_succ]
  have hs := π.step_at i
  rw [hl] at hs
  obtain ⟨hadv, -, t', ht', -, -, -, -, -, -, hsent⟩ := hs.restart_eq
  rw [hsent]
  refine ⟨?_, rfl⟩
  cases hlv : π[i][v] with
  | some l =>
    rw [lastKnownSt_of_some _ π hlv, lastKnownSt_of_some _ π (hs.restart_getElem_of_some hlv hc)]
    show M.wake (if keep then l.st else l.disk) (t : Int) = M.wake l.st (t : Int)
    cases keep
    · obtain ⟨r, -, -, -, -, -, hrel⟩ := nodeOk_exec F π i v l hlv
      show M.wake l.disk (t : Int) = M.wake l.st (t : Int)
      rcases hrel with hrel | ⟨t'', hrel⟩
      · rw [hrel]
      · rw [hrel, F.wake_wake]
    · rfl
  | none =>
    rw [lastKnownSt_eq_init_of_none _ π hlv hadv,
      lastKnownSt_of_some _ π (hs.restart_getElem_of_none hlv hc)]
    rfl

/-- **A step that is not `v`'s own leaves `v`'s state** (the trace layer's `untouched`, for
Goldilocks's run). A trace step that is not `v`'s tick, restart or delivery leaves `v`'s node state
as it was.

Why: a step of the kind `other` of the trace's own keeps every node state; a step of `π` that the
trace reads as none of the three is not a tick or a restart of `v` (each is taken with a clock,
which the trace reads), and is a delivery to `v` only when `v` is corrupted (`v` up is required of a
delivery to an honest validator), so `lastKnownSt_succ_of_not_own` applies. A crash during a
reaction of `v` keeps its memory.

The variables:
- `π`: the run; `j`: the trace step; `v`: the validator. -/
theorem toTrace_untouched {M : GoldilocksModel V} {S : Setup V} (π : Exec (variantProtocolOf M S))
    (j : ℕ) (v : V)
    -- the step is not a tick of `v`
    (htick : ∀ t : ℕ, (toTrace (M.initial S.C) π).lbl j ≠ Event.tick v t)
    -- the step is not a restart of `v`
    (hres : ∀ (t : ℕ) (keep : Bool), (toTrace (M.initial S.C) π).lbl j ≠ Event.restart v t keep)
    -- the step is not a delivery to `v`
    (hdel : ∀ sm : Framework.StsMultisetLog.SignedMsg V (NamedObject V),
      (toTrace (M.initial S.C) π).lbl j ≠ Event.deliver v sm) :
    (toTrace (M.initial S.C) π).st (j + 1) v = (toTrace (M.initial S.C) π).st j v := by
  by_cases hj : ∃ i : ℕ, newIdx π i = j
  · obtain ⟨i, rfl⟩ := hj
    rw [toTrace_st_newIdx, toTrace_st_newIdx_succ]
    apply lastKnownSt_succ_of_not_own _ π
    · intro hl
      have hs := π.step_at i
      rw [hl] at hs
      obtain ⟨-, t, -, ht⟩ :=
        RStsVariant2.nodeSpec_enabled_known (Pr := variantProtocolOf M S) (v := v) (na := .tick)
          (c := π[i]) hs.1
      exact htick t (by rw [toTrace_lbl_newIdx, eventOf_eq_tick]; exact ⟨hl, ht⟩)
    · intro e hl
      by_contra hv
      have hs := π.step_at i
      rw [hl] at hs
      have hen : (RStsVariant2.nodeSpec (variantProtocolOf M S) v (.deliver e)).Enabled π[i] :=
        hs.1.resolve_left (fun h' => hv h'.1)
      obtain ⟨-, hcr, l, -, hlv, -⟩ := hen
      exact hdel (traceMsg e) (by
        rw [toTrace_lbl_newIdx, eventOf_eq_deliver]
        exact ⟨e, hl, rfl, hcr, by rw [hlv]; simp, hv⟩)
    · intro keep hl
      have hs := π.step_at i
      rw [hl] at hs
      obtain ⟨-, -, t, ht, -⟩ := hs.restart_eq
      exact hres t keep (by rw [toTrace_lbl_newIdx, eventOf_eq_restart]; exact ⟨hl, ht⟩)
    · intro ev; exact ev.elim
  · exact toTrace_st_succ_of_not _ π hj v

/-- **Every run of Goldilocks is a run of the model on its trace** (the trace layer's `RunFacts`, for
Goldilocks's run on the variant).

Why: every field is given by the steps of `π` one at a time (`toTrace_tick`, `toTrace_restart`,
`toTrace_deliver`, `toTrace_untouched`) and by the index lemmas of the projection.

The variables:
- `F`: the model's facts; `π`: the run. -/
theorem runFacts_toTrace {M : GoldilocksModel V} {S : Setup V} (F : Facts M)
    (π : Exec (variantProtocolOf M S)) :
    RunFacts M S (toTrace (M.initial S.C) π) where
  time_zero := toTrace_time_zero _ π
  time_le_succ := toTrace_time_le_succ _ π
  time_keep := toTrace_time_keep _ π
  init := toTrace_init π
  sent_zero := toTrace_sent_zero _ π
  sent_mono := toTrace_sent_mono _ π
  tick := toTrace_tick F π
  restart := toTrace_restart F π
  deliver := toTrace_deliver π
  untouched := toTrace_untouched π

end Goldilocks

end GoldilocksVariant.Final
