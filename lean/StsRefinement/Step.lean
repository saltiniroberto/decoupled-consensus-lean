module
public import StsMultisetLog.Analysis.AtomicLemmas
public import StsRefinement.Notion

@[expose] public section

/-!
# The step lemmas

Under a refinement `R : RefinementT Pr₁ Pr₂ α μ ε τ` and schedules related by
`ScheduleOver τ S₁ S₂`, one atomic step of the refining protocol `Pr₁` is seen through the maps
in one of two ways.

* A step whose label has a refined counterpart (`AtomicAction.mapT μ ε τ a = some b`) is, between
  the projected configurations, an atomic step of the refined protocol `Pr₂` with the label `b`
  (`atomicStep_visible`).
* A step whose label has none (`AtomicAction.mapT μ ε τ a = none`) leaves the projected
  configuration unchanged (`atomicStep_hidden`).

The hidden tick is the one case that needs the configuration to come from an execution: a tick at
`t + 1` with `τ (t + 1) = τ t` writes `t + 1` into every awake clock, and the projected clock is
unchanged only because the clock was `t` before (`ClocksAtTime`, which every configuration of an
atomic execution satisfies by the framework's `atomic_awake_clock_eq_time`). The visible step
needs no such hypothesis (`atomicStep_visible_of_step`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace StsRefinement

open Framework.StsMultisetLog

variable {Node : Type} [DecidableEq Node]
variable {Msg₁ St₁ Ev₁ Msg₂ St₂ Ev₂ : Type} [DecidableEq Msg₁] [DecidableEq Msg₂]

/-- `ClocksAtTime S₁ c`: in the configuration `c`, every validator awake at the current time reads
the current time on its clock. -/
def ClocksAtTime (S₁ : Schedule Node) (c : Config Node Msg₁ St₁) : Prop :=
  ∀ p, p ∈ S₁.awake (c.time : Int) → c[p].clock = c.time

/-- Every configuration of an atomic execution has its awake clocks at the current time. -/
theorem clocksAtTime_of_exec {Pr₁ : Protocol Node Msg₁ St₁ Ev₁} {S₁ : Schedule Node}
    (x : AtomicExec Pr₁ S₁) (i : ℕ) : ClocksAtTime S₁ x[i] :=
  fun p hp => atomic_awake_clock_eq_time x i p hp

/-! ## Messages, views and sent logs through `μ` -/

section Maps

variable {μ : Msg₁ → Option Msg₂}

theorem SignedMsg.mapP_eq_none {m : SignedMsg Node Msg₁} :
    SignedMsg.mapP μ m = none ↔ μ m.msg = none := by
  simp [SignedMsg.mapP]

/-- The messages a validator `q` signs, seen through `μ`: signing and mapping commute. -/
theorem filterMap_mapP_map_mk (q : Node) (s : Multiset Msg₁) :
    (s.map (SignedMsg.mk q)).filterMap (SignedMsg.mapP μ) = (s.filterMap μ).map (SignedMsg.mk q) := by
  rw [Multiset.filterMap_map, Multiset.map_filterMap]
  rfl

/-- `Multiset.filterMap` distributes over a sum over a finite set. -/
theorem filterMap_finset_sum {α β ι : Type} (f : α → Option β) (s : Finset ι)
    (g : ι → Multiset α) : (∑ i ∈ s, g i).filterMap f = ∑ i ∈ s, (g i).filterMap f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Multiset.filterMap_add, ih]

/-- Inserting a message with a refined meaning into a view inserts its image into the refined view. -/
theorem View.mapP_insert_some {m : SignedMsg Node Msg₁} {sm : SignedMsg Node Msg₂}
    (h : SignedMsg.mapP μ m = some sm) (v : View Node Msg₁) :
    View.mapP μ (insert m v) = insert sm (View.mapP μ v) := by
  unfold View.mapP
  rw [Finset.biUnion_insert, h, Option.toFinset_some, Finset.insert_eq]

/-- Inserting a message without a refined meaning into a view leaves the refined view unchanged. -/
theorem View.mapP_insert_none {m : SignedMsg Node Msg₁} (h : SignedMsg.mapP μ m = none)
    (v : View Node Msg₁) : View.mapP μ (insert m v) = View.mapP μ v := by
  simp [View.mapP, Finset.biUnion_insert, h]

theorem View.mem_mapP {m : SignedMsg Node Msg₁} {sm : SignedMsg Node Msg₂}
    {v : View Node Msg₁} (hm : m ∈ v) (h : SignedMsg.mapP μ m = some sm) : sm ∈ View.mapP μ v :=
  Finset.mem_biUnion.2 ⟨m, hm, by simp [h]⟩

end Maps

/-! ## Configurations through the maps -/

section Config

variable {α : St₁ → St₂} {μ : Msg₁ → Option Msg₂} {τ : TimeMap}

@[simp] theorem Config.mapT_time (c : Config Node Msg₁ St₁) :
    (Config.mapT α μ τ c).time = τ c.time := rfl

theorem Config.mapT_getElem (c : Config Node Msg₁ St₁) (p : Node) :
    (Config.mapT α μ τ c)[p] =
      { clock := τ c[p].clock, st := α c[p].st, view := View.mapP μ c[p].view } := rfl

@[simp] theorem Config.mapT_sent (c : Config Node Msg₁ St₁) :
    (Config.mapT α μ τ c).sent = c.sent.filterMap (SignedMsg.mapP μ) := rfl

/-- Applying a reaction commutes with the projection: the projected reaction is applied to the
projected configuration. -/
theorem Config.mapT_applyNodeStepResult (p : Node) (res : NodeStepResult St₁ Msg₁)
    (d : Config Node Msg₁ St₁) :
    Config.mapT α μ τ (applyNodeStepResult p res d) =
      applyNodeStepResult p (NodeStepResult.mapP α μ res) (Config.mapT α μ τ d) := by
  refine Config.ext' rfl (fun q => ?_) ?_
  · simp only [nodes_apply]
    rw [Config.mapT_getElem, applyNodeStepResult_getElem, applyNodeStepResult_getElem,
      Config.mapT_getElem]
    by_cases h : p = q
    · subst h; simp [NodeStepResult.mapP]
    · simp only [h, ↓reduceIte]; rfl
  · simp [Multiset.filterMap_add, filterMap_mapP_map_mk, NodeStepResult.mapP]

/-- A reaction that changes nothing `α` shows and sends nothing with a refined meaning leaves the
projection unchanged. -/
theorem Config.mapT_applyNodeStepResult_hidden (p : Node) (res : NodeStepResult St₁ Msg₁)
    (d : Config Node Msg₁ St₁) (hst : α res.state = α d[p].st) (hs : res.send.filterMap μ = 0) :
    Config.mapT α μ τ (applyNodeStepResult p res d) = Config.mapT α μ τ d := by
  rw [Config.mapT_applyNodeStepResult]
  refine Config.ext' rfl (fun q => ?_) ?_
  · simp only [nodes_apply]
    rw [applyNodeStepResult_getElem]
    by_cases h : p = q
    · subst h; simp [NodeStepResult.mapP, Config.mapT_getElem, hst]
    · simp [h]
  · simp [NodeStepResult.mapP, hs]

/-- Filing a message with a refined meaning into `p`'s view is, through the maps, filing its image. -/
theorem Config.mapT_receive_some {p : Node} {m : SignedMsg Node Msg₁} {sm : SignedMsg Node Msg₂}
    (h : SignedMsg.mapP μ m = some sm) (d : Config Node Msg₁ St₁) :
    Config.mapT α μ τ (receive p m d) = receive p sm (Config.mapT α μ τ d) := by
  refine Config.ext' rfl (fun q => ?_) rfl
  simp only [nodes_apply]
  rw [Config.mapT_getElem, receive_getElem, receive_getElem]
  by_cases hq : p = q
  · subst hq; simp [Config.mapT_getElem, View.mapP_insert_some h]
  · simp [hq, Config.mapT_getElem]

/-- Filing a message without a refined meaning into `p`'s view leaves the projection unchanged. -/
theorem Config.mapT_receive_none {p : Node} {m : SignedMsg Node Msg₁}
    (h : SignedMsg.mapP μ m = none) (d : Config Node Msg₁ St₁) :
    Config.mapT α μ τ (receive p m d) = Config.mapT α μ τ d := by
  refine Config.ext' rfl (fun q => ?_) rfl
  simp only [nodes_apply]
  rw [Config.mapT_getElem, receive_getElem, Config.mapT_getElem]
  by_cases hq : p = q
  · subst hq; simp [View.mapP_insert_none h]
  · simp [hq]

/-- A message put on the wire, seen through the maps. -/
theorem Config.mapT_cons_some {m : SignedMsg Node Msg₁} {sm : SignedMsg Node Msg₂}
    (h : SignedMsg.mapP μ m = some sm) (d : Config Node Msg₁ St₁) :
    Config.mapT α μ τ { d with sent := m ::ₘ d.sent } =
      { Config.mapT α μ τ d with sent := sm ::ₘ (Config.mapT α μ τ d).sent } :=
  Config.ext' rfl (fun _ => rfl) (Multiset.filterMap_cons_some _ _ _ h)

/-- A message without a refined meaning put on the wire leaves the projection unchanged. -/
theorem Config.mapT_cons_none {m : SignedMsg Node Msg₁} (h : SignedMsg.mapP μ m = none)
    (d : Config Node Msg₁ St₁) :
    Config.mapT α μ τ { d with sent := m ::ₘ d.sent } = Config.mapT α μ τ d :=
  Config.ext' rfl (fun _ => rfl) (Multiset.filterMap_cons_none _ _ h)

end Config

/-! ## The tick -/

section Tick

variable {Pr₁ : Protocol Node Msg₁ St₁ Ev₁} {Pr₂ : Protocol Node Msg₂ St₂ Ev₂}
  {S₁ S₂ : Schedule Node} {α : St₁ → St₂} {μ : Msg₁ → Option Msg₂} {ε : Ev₁ → Option Ev₂}
  {τ : TimeMap}

/-- Under `ScheduleOver`, the validators entering the awake set at a visible refining tick are
those entering it at the refined tick. -/
theorem entrants_over (hS : ScheduleOver τ S₁ S₂) {t : ℕ} (hv : τ.Visible t) :
    entrants S₁ (t + 1) = entrants S₂ (τ (t + 1)) := by
  have h1 : ((t + 1 : ℕ) : Int) - 1 = ((t : ℕ) : Int) := by omega
  have h2 : ((τ (t + 1) : ℕ) : Int) - 1 = ((τ t : ℕ) : Int) := by
    unfold TimeMap.Visible at hv; omega
  unfold entrants
  rw [h1, h2, (hS.1 (t + 1)).1, (hS.1 (t + 1)).2, (hS.1 t).1]

/-- **The visible tick.** A refining tick at `t + 1` that moves refined time is, between the
projected configurations, the refined tick at `τ (t + 1)`, with every wake and tick result
mapped. -/
theorem tick_visible_step (R : RefinementT Pr₁ Pr₂ α μ ε τ) (hS : ScheduleOver τ S₁ S₂)
    {t : ℕ} (hv : τ.Visible t) {c : Config Node Msg₁ St₁} (hen : c.time + 1 = t + 1)
    (w tk : Node → NodeStepResult St₁ Msg₁)
    (hw : ∀ p, TickAllAwakeWake Pr₁ S₁ (t + 1) c p (w p))
    (htk : ∀ p ∈ S₁.awake ((t + 1 : ℕ) : Int) \ S₁.adv ((t + 1 : ℕ) : Int),
      Pr₁.step p (t + 1) c[p].view (w p).state .tick (tk p)) :
    AtomicStep Pr₂ S₂ (.tickAllAwake (τ (t + 1))) (Config.mapT α μ τ c)
      (Config.mapT α μ τ (tickAllAwakeUpdate S₁ (t + 1) c w tk)) := by
  have hct : c.time = t := by omega
  have hA := (hS.1 (t + 1)).1
  have hB := (hS.1 (t + 1)).2
  have hE := entrants_over hS hv
  refine ⟨?_, fun p => NodeStepResult.mapP α μ (w p), fun p => NodeStepResult.mapP α μ (tk p),
    fun p => ?_, fun p hp => ?_, ?_⟩
  · show τ c.time + 1 = τ (t + 1)
    rw [hct]; exact hv.symm
  · have hwp := hw p
    unfold TickAllAwakeWake at hwp ⊢
    rw [hE] at hwp
    beta_reduce
    split_ifs at hwp ⊢
    · exact R.wake p _ _ _ _ hwp
    · rw [hwp]; simp [NodeStepResult.mapP, Config.mapT_getElem]
  · rw [← hA, ← hB] at hp
    exact R.tick_visible p t _ _ _ hv (htk p hp)
  · refine Config.ext' rfl (fun q => ?_) ?_
    · simp only [nodes_apply]
      rw [Config.mapT_getElem]
      by_cases ha : q ∈ S₁.awake ((t + 1 : ℕ) : Int)
      · have ha₂ : q ∈ S₂.awake ((τ (t + 1) : ℕ) : Int) := hA ▸ ha
        by_cases hd : q ∈ S₁.adv ((t + 1 : ℕ) : Int)
        · have hd₂ : q ∈ S₂.adv ((τ (t + 1) : ℕ) : Int) := hB ▸ hd
          rw [tickAllAwakeUpdate_getElem_awake_adv ha hd,
            tickAllAwakeUpdate_getElem_awake_adv ha₂ hd₂, Config.mapT_getElem]
        · have hd₂ : q ∉ S₂.adv ((τ (t + 1) : ℕ) : Int) := hB ▸ hd
          rw [tickAllAwakeUpdate_getElem_awake ha hd, tickAllAwakeUpdate_getElem_awake ha₂ hd₂,
            Config.mapT_getElem]
          rfl
      · have ha₂ : q ∉ S₂.awake ((τ (t + 1) : ℕ) : Int) := hA ▸ ha
        rw [tickAllAwakeUpdate_getElem_asleep ha, tickAllAwakeUpdate_getElem_asleep ha₂,
          Config.mapT_getElem]
    · show (c.sent + _).filterMap (SignedMsg.mapP μ) =
        c.sent.filterMap (SignedMsg.mapP μ) + _
      rw [Multiset.filterMap_add, filterMap_finset_sum, hA, hB]
      congr 1
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [Multiset.map_add, Multiset.filterMap_add, filterMap_mapP_map_mk, filterMap_mapP_map_mk,
        ← Multiset.map_add]
      rfl

/-- **The hidden tick.** A refining tick at `t + 1` that does not move refined time leaves the
projected configuration unchanged, provided the awake clocks read the current time `t` before it
(`ClocksAtTime`). -/
theorem tick_hidden_step (R : RefinementT Pr₁ Pr₂ α μ ε τ) (hS : ScheduleOver τ S₁ S₂)
    {t : ℕ} (hh : τ (t + 1) = τ t) {c : Config Node Msg₁ St₁} (hc : ClocksAtTime S₁ c)
    (hen : c.time + 1 = t + 1) (w tk : Node → NodeStepResult St₁ Msg₁)
    (hw : ∀ p, TickAllAwakeWake Pr₁ S₁ (t + 1) c p (w p))
    (htk : ∀ p ∈ S₁.awake ((t + 1 : ℕ) : Int) \ S₁.adv ((t + 1 : ℕ) : Int),
      Pr₁.step p (t + 1) c[p].view (w p).state .tick (tk p)) :
    Config.mapT α μ τ (tickAllAwakeUpdate S₁ (t + 1) c w tk) = Config.mapT α μ τ c := by
  have hct : c.time = t := by omega
  have hAw : S₁.awake ((t + 1 : ℕ) : Int) = S₁.awake ((t : ℕ) : Int) := by
    rw [(hS.1 (t + 1)).1, (hS.1 t).1, hh]
  -- no validator enters the awake set at `t + 1`, so every wake result is inert
  have hinert : ∀ p, w p = { state := c[p].st, send := 0 } := by
    intro p
    have hwp := hw p
    unfold TickAllAwakeWake at hwp
    rw [if_neg] at hwp
    · exact hwp
    · intro hp
      unfold entrants at hp
      have h1 : ((t + 1 : ℕ) : Int) - 1 = ((t : ℕ) : Int) := by omega
      rw [h1] at hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_sdiff.1 hp
      exact hp2 (hAw ▸ (Finset.mem_sdiff.1 hp1).1)
  have hreact : ∀ q ∈ S₁.awake ((t + 1 : ℕ) : Int) \ S₁.adv ((t + 1 : ℕ) : Int),
      α (tk q).state = α c[q].st ∧ (tk q).send.filterMap μ = 0 := by
    intro q hq
    have := htk q hq
    rw [hinert q] at this
    exact R.tick_hidden q t _ _ _ hh this
  have hclock : ∀ q ∈ S₁.awake ((t + 1 : ℕ) : Int), τ (t + 1) = τ c[q].clock := by
    intro q hq
    rw [hc q (by rw [hct, ← hAw]; exact hq), hct, hh]
  refine Config.ext' (by show τ (t + 1) = τ c.time; rw [hct, hh]) (fun q => ?_) ?_
  · simp only [nodes_apply]
    rw [Config.mapT_getElem, Config.mapT_getElem]
    by_cases ha : q ∈ S₁.awake ((t + 1 : ℕ) : Int)
    · by_cases hd : q ∈ S₁.adv ((t + 1 : ℕ) : Int)
      · rw [tickAllAwakeUpdate_getElem_awake_adv ha hd]
        simp only [hclock q ha]
      · rw [tickAllAwakeUpdate_getElem_awake ha hd]
        simp only [hclock q ha, (hreact q (Finset.mem_sdiff.2 ⟨ha, hd⟩)).1]
    · rw [tickAllAwakeUpdate_getElem_asleep ha]
  · show (c.sent + _).filterMap (SignedMsg.mapP μ) = c.sent.filterMap (SignedMsg.mapP μ)
    rw [Multiset.filterMap_add, filterMap_finset_sum, Finset.sum_eq_zero, add_zero]
    intro q hq
    rw [Multiset.map_add, Multiset.filterMap_add, filterMap_mapP_map_mk, filterMap_mapP_map_mk,
      hinert q, (hreact q hq).2]
    simp

end Tick

/-! ## The step lemmas -/

section Steps

variable {Pr₁ : Protocol Node Msg₁ St₁ Ev₁} {Pr₂ : Protocol Node Msg₂ St₂ Ev₂}
  {S₁ S₂ : Schedule Node} {α : St₁ → St₂} {μ : Msg₁ → Option Msg₂} {ε : Ev₁ → Option Ev₂}
  {τ : TimeMap}

/-- **The visible step lemma, with no hypothesis on the clocks.** A refining step whose label has a
refined counterpart `b` is, between the projected configurations, a step of the refined protocol
with the label `b`. -/
theorem atomicStep_visible_of_step (R : RefinementT Pr₁ Pr₂ α μ ε τ) (hS : ScheduleOver τ S₁ S₂)
    {a : AtomicAction Node Msg₁ Ev₁} {b : AtomicAction Node Msg₂ Ev₂}
    {c c' : Config Node Msg₁ St₁}
    (h : AtomicStep Pr₁ S₁ a c c') (hb : AtomicAction.mapT μ ε τ a = some b) :
    AtomicStep Pr₂ S₂ b (Config.mapT α μ τ c) (Config.mapT α μ τ c') := by
  have hAw : ∀ t : ℕ, S₁.awake (t : Int) = S₂.awake ((τ t : ℕ) : Int) := fun t => (hS.1 t).1
  have hAd : ∀ t : ℕ, S₁.adv (t : Int) = S₂.adv ((τ t : ℕ) : Int) := fun t => (hS.1 t).2
  cases a with
  | tickAllAwake t' =>
    obtain ⟨hen, w, tk, hw, htk, rfl⟩ := h
    cases t' with
    | zero => exact absurd (show c.time + 1 = 0 from hen) (by omega)
    | succ t =>
      simp only [AtomicAction.mapT] at hb
      split_ifs at hb with hv
      cases hb
      exact tick_visible_step R hS hv hen w tk hw htk
  | deliver p m =>
    obtain ⟨⟨hm, hp, hadv⟩, hr⟩ := h
    obtain ⟨res, hstep, rfl⟩ := (nodeStep_iff_exists Pr₁ p (.recv m) _ _).1 hr
    simp only [AtomicAction.mapT] at hb
    cases hsm : SignedMsg.mapP μ m with
    | none => rw [hsm] at hb; cases hb
    | some sm =>
      rw [hsm] at hb
      cases hb
      refine ⟨⟨(Multiset.mem_filterMap _ _).2 ⟨m, hm, hsm⟩, ?_, ?_⟩,
        (nodeStep_iff_exists Pr₂ p (.recv sm) _ _).2 ⟨NodeStepResult.mapP α μ res, ?_, ?_⟩⟩
      · show p ∈ S₂.awake ((τ c.time : ℕ) : Int); rw [← hAw]; exact hp
      · show p ∉ S₂.adv ((τ c.time : ℕ) : Int); rw [← hAd]; exact hadv
      · rw [← Config.mapT_receive_some hsm]
        exact R.recv_visible p _ _ _ m sm res hsm hstep
      · rw [← Config.mapT_receive_some hsm, Config.mapT_applyNodeStepResult]
  | custom p ev =>
    obtain ⟨⟨hp, hen, hadv⟩, hr⟩ := h
    obtain ⟨res, hstep, rfl⟩ := (nodeStep_iff_exists Pr₁ p (.custom ev) _ _).1 hr
    simp only [AtomicAction.mapT] at hb
    cases he : ε ev with
    | none => rw [he] at hb; cases hb
    | some ev₂ =>
      rw [he] at hb
      cases hb
      refine ⟨⟨?_, R.enabled _ _ ev ev₂ he hen, ?_⟩,
        (nodeStep_iff_exists Pr₂ p (.custom ev₂) _ _).2 ⟨NodeStepResult.mapP α μ res, ?_, ?_⟩⟩
      · show p ∈ S₂.awake ((τ c.time : ℕ) : Int); rw [← hAw]; exact hp
      · show p ∉ S₂.adv ((τ c.time : ℕ) : Int); rw [← hAd]; exact hadv
      · exact R.custom_visible p _ _ _ ev ev₂ res he hstep
      · rw [Config.mapT_applyNodeStepResult]
  | adversarial p m =>
    obtain ⟨hp, rfl⟩ := h
    simp only [AtomicAction.mapT] at hb
    cases hμ : μ m with
    | none => rw [hμ] at hb; cases hb
    | some m₂ =>
      rw [hμ] at hb
      cases hb
      refine ⟨?_, ?_⟩
      · show p ∈ S₂.adv ((τ c.time : ℕ) : Int); rw [← hAd]; exact hp
      · exact Config.mapT_cons_some (by simp [SignedMsg.mapP, hμ]) c
  | forward p m =>
    obtain ⟨⟨hp, hm, hadv⟩, rfl⟩ := h
    simp only [AtomicAction.mapT] at hb
    cases hsm : SignedMsg.mapP μ m with
    | none => rw [hsm] at hb; cases hb
    | some sm =>
      rw [hsm] at hb
      cases hb
      refine ⟨⟨?_, View.mem_mapP hm hsm, ?_⟩, Config.mapT_cons_some hsm c⟩
      · show p ∈ S₂.awake ((τ c.time : ℕ) : Int); rw [← hAw]; exact hp
      · show p ∉ S₂.adv ((τ c.time : ℕ) : Int); rw [← hAd]; exact hadv

set_option linter.unusedVariables false in
/-- **The visible step lemma.** Under a refinement `R` and schedules related by `ScheduleOver`, a
refining step with label `a` from `c` to `c'` whose projected label is `some b` is, between the
projected configurations, a step of the refined protocol with label `b`. Read aloud: a refining
step with a refined counterpart is, between the projected configurations, a step of the refined
protocol with that label. The hypothesis `hc` is not used (`atomicStep_visible_of_step` is the
form without it); it is kept so that the visible and the hidden step lemma take the same
hypotheses. -/
theorem atomicStep_visible (R : RefinementT Pr₁ Pr₂ α μ ε τ) (hS : ScheduleOver τ S₁ S₂)
    {a : AtomicAction Node Msg₁ Ev₁} {b : AtomicAction Node Msg₂ Ev₂}
    {c c' : Config Node Msg₁ St₁} (hc : ClocksAtTime S₁ c)
    (h : AtomicStep Pr₁ S₁ a c c') (hb : AtomicAction.mapT μ ε τ a = some b) :
    AtomicStep Pr₂ S₂ b (Config.mapT α μ τ c) (Config.mapT α μ τ c') :=
  atomicStep_visible_of_step R hS h hb

/-- **The hidden step lemma.** Under a refinement `R` and schedules related by `ScheduleOver`, a
refining step from `c` to `c'` whose label has no refined counterpart leaves the projected
configuration unchanged, provided the awake clocks of `c` read its time. Read aloud: a refining
step without a refined counterpart leaves the projection unchanged. -/
theorem atomicStep_hidden (R : RefinementT Pr₁ Pr₂ α μ ε τ) (hS : ScheduleOver τ S₁ S₂)
    {a : AtomicAction Node Msg₁ Ev₁} {c c' : Config Node Msg₁ St₁} (hc : ClocksAtTime S₁ c)
    (h : AtomicStep Pr₁ S₁ a c c') (hb : AtomicAction.mapT μ ε τ a = none) :
    Config.mapT α μ τ c' = Config.mapT α μ τ c := by
  cases a with
  | tickAllAwake t' =>
    obtain ⟨hen, w, tk, hw, htk, rfl⟩ := h
    cases t' with
    | zero => exact absurd (show c.time + 1 = 0 from hen) (by omega)
    | succ t =>
      simp only [AtomicAction.mapT] at hb
      split_ifs at hb with hv
      have hh : τ (t + 1) = τ t := by rcases τ.step t with h' | h'; exact h'; exact absurd h' hv
      exact tick_hidden_step R hS hh hc hen w tk hw htk
  | deliver p m =>
    obtain ⟨-, hr⟩ := h
    obtain ⟨res, hstep, rfl⟩ := (nodeStep_iff_exists Pr₁ p (.recv m) _ _).1 hr
    simp only [AtomicAction.mapT, Option.map_eq_none_iff] at hb
    obtain ⟨hst, hs⟩ := R.recv_hidden p _ _ _ m res (SignedMsg.mapP_eq_none.1 hb) hstep
    rw [Config.mapT_applyNodeStepResult_hidden p res _ hst hs, Config.mapT_receive_none hb]
  | custom p ev =>
    obtain ⟨-, hr⟩ := h
    obtain ⟨res, hstep, rfl⟩ := (nodeStep_iff_exists Pr₁ p (.custom ev) _ _).1 hr
    simp only [AtomicAction.mapT, Option.map_eq_none_iff] at hb
    obtain ⟨hst, hs⟩ := R.custom_hidden p _ _ _ ev res hb hstep
    exact Config.mapT_applyNodeStepResult_hidden p res _ hst hs
  | adversarial p m =>
    obtain ⟨-, rfl⟩ := h
    simp only [AtomicAction.mapT, Option.map_eq_none_iff] at hb
    exact Config.mapT_cons_none (SignedMsg.mapP_eq_none.2 hb) c
  | forward p m =>
    obtain ⟨-, rfl⟩ := h
    simp only [AtomicAction.mapT, Option.map_eq_none_iff] at hb
    exact Config.mapT_cons_none hb c

end Steps

end StsRefinement
