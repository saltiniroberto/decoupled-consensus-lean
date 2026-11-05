module
public import StsRefinement.Step
public import StsRefinement.ReadBack

@[expose] public section

/-!
# The case `τ = id`: total maps and the same readings

The refinement notion `RefinementT` covers a refining protocol whose clock is the refined one
(`TimeMap.id`) and whose messages and events all have a refined meaning (`μ`, `ε` total). That case
has its own, simpler form, kept here: `Refinement Pr₁ Pr₂ α μ ε` with total maps, and the
index-preserving projection of executions `AtomicExec.map`, whose read-back facts hold by `rfl`.

The page proves that the simpler form is the case `τ = id` of the general one:
`RefinementT.ofRefinement` makes every `Refinement` a `RefinementT` at `TimeMap.id`,
`TimedProjection.ofMap` makes `AtomicExec.map` a `TimedProjection` with the step map `σ i = i`,
and the step lemma `atomicStep_map` that `AtomicExec.map` rests on is the visible step lemma at
`τ = id`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace StsRefinement

open Framework.StsMultisetLog

variable {Node : Type} [DecidableEq Node]

section IdCase

variable {Msg₁ St₁ Ev₁ Msg₂ St₂ Ev₂ : Type} [DecidableEq Msg₁] [DecidableEq Msg₂]

/-- `SignedMsg.mapMsg μ m`: the signed message `m` with its object mapped by the total map `μ`,
the signer kept. -/
def SignedMsg.mapMsg (μ : Msg₁ → Msg₂) (m : SignedMsg Node Msg₁) : SignedMsg Node Msg₂ :=
  ⟨m.sender, μ m.msg⟩

/-- `Event.map μ ε e`: the event `e` with its message mapped by `μ` and its protocol event by `ε`. -/
def Event.map (μ : Msg₁ → Msg₂) (ε : Ev₁ → Ev₂) : Event Node Msg₁ Ev₁ → Event Node Msg₂ Ev₂
  | .tick => .tick
  | .recv m => .recv (SignedMsg.mapMsg μ m)
  | .wake => .wake
  | .custom e => .custom (ε e)

/-- `NodeStepResult.map α μ r`: the state mapped by `α`, every send by `μ`. -/
def NodeStepResult.map (α : St₁ → St₂) (μ : Msg₁ → Msg₂) (r : NodeStepResult St₁ Msg₁) :
    NodeStepResult St₂ Msg₂ :=
  ⟨α r.state, r.send.map μ⟩

/-- `Config.map α μ c`: the configuration `c` with the same time and clocks, every node state
mapped by `α`, every view and the sent log by `μ`. -/
def Config.map (α : St₁ → St₂) (μ : Msg₁ → Msg₂) (c : Config Node Msg₁ St₁) :
    Config Node Msg₂ St₂ :=
  { time := c.time
    nodes := fun p => { clock := c[p].clock, st := α c[p].st,
                        view := c[p].view.image (SignedMsg.mapMsg μ) }
    sent := c.sent.map (SignedMsg.mapMsg μ) }

/-- `AtomicAction.map μ ε a`: the label `a` with its message mapped by `μ` and its protocol
event by `ε`, the time of a tick kept. -/
def AtomicAction.map (μ : Msg₁ → Msg₂) (ε : Ev₁ → Ev₂) :
    AtomicAction Node Msg₁ Ev₁ → AtomicAction Node Msg₂ Ev₂
  | .tickAllAwake t => .tickAllAwake t
  | .deliver p m => .deliver p (SignedMsg.mapMsg μ m)
  | .custom p e => .custom p (ε e)
  | .adversarial p m => .adversarial p (μ m)
  | .forward p m => .forward p (SignedMsg.mapMsg μ m)

/-- **The refinement notion with total maps and the same readings.**
`Refinement Pr₁ Pr₂ α μ ε`: every initial state maps to the refined initial state; every reaction
of `Pr₁` at a reading `r` maps, through `α` and the total maps `μ`, `ε`, to a reaction of `Pr₂` at
the same reading; and a protocol event's enabling maps forward. It is the case `τ = id` with total
maps of `RefinementT` (`RefinementT.ofRefinement`). -/
structure Refinement (Pr₁ : Protocol Node Msg₁ St₁ Ev₁) (Pr₂ : Protocol Node Msg₂ St₂ Ev₂)
    (α : St₁ → St₂) (μ : Msg₁ → Msg₂) (ε : Ev₁ → Ev₂) : Prop where
  init : ∀ p, α (Pr₁.init p) = Pr₂.init p
  step : ∀ p (r : Time) (view : View Node Msg₁) (st : St₁) (e : Event Node Msg₁ Ev₁)
      (res : NodeStepResult St₁ Msg₁),
    Pr₁.step p r view st e res →
      Pr₂.step p r (view.image (SignedMsg.mapMsg μ)) (α st) (Event.map μ ε e)
        (NodeStepResult.map α μ res)
  enabled : ∀ (r : Time) (st : St₁) (ev : Ev₁), Pr₁.enabled r st ev → Pr₂.enabled r (α st) (ε ev)

variable {Pr₁ : Protocol Node Msg₁ St₁ Ev₁} {Pr₂ : Protocol Node Msg₂ St₂ Ev₂}
  {α : St₁ → St₂} {μ : Msg₁ → Msg₂} {ε : Ev₁ → Ev₂} {S : Schedule Node}

/-- The mapped initial configuration is initial. -/
theorem init_map (R : Refinement Pr₁ Pr₂ α μ ε) {c : Config Node Msg₁ St₁} (h : Init Pr₁ c) :
    Init Pr₂ (Config.map α μ c) := by
  obtain ⟨ht, hn, hs⟩ := h
  refine ⟨ht, fun p => ?_, ?_⟩
  · have hp := hn p
    show ({ clock := c[p].clock, st := α c[p].st, view := c[p].view.image (SignedMsg.mapMsg μ) } :
      Local Node Msg₂ St₂) = _
    rw [hp]
    simp [R.init p]
  · show c.sent.map (SignedMsg.mapMsg μ) = 0
    rw [hs]; rfl

/-! ### The case `τ = id` of `RefinementT` -/

theorem SignedMsg.mapP_some (m : SignedMsg Node Msg₁) :
    SignedMsg.mapP (some ∘ μ) m = some (SignedMsg.mapMsg μ m) := rfl

/-- At total `μ`, the partial view map is the image under `SignedMsg.mapMsg μ`. -/
theorem View.mapP_some (view : View Node Msg₁) :
    View.mapP (some ∘ μ) view = view.image (SignedMsg.mapMsg μ) := by
  ext sm
  simp [View.mapP, SignedMsg.mapP_some, eq_comm]

/-- At total `μ`, the partial reaction map is `NodeStepResult.map`. -/
theorem NodeStepResult.mapP_some (res : NodeStepResult St₁ Msg₁) :
    NodeStepResult.mapP α (some ∘ μ) res = NodeStepResult.map α μ res := by
  simp [NodeStepResult.mapP, NodeStepResult.map, Multiset.filterMap_eq_map]

/-- **At `τ = id` and total maps, the projection of a configuration is `Config.map`.** -/
theorem Config.mapT_id (c : Config Node Msg₁ St₁) :
    Config.mapT α (some ∘ μ) TimeMap.id c = Config.map α μ c := by
  have hs : SignedMsg.mapP (Node := Node) (some ∘ μ) = some ∘ SignedMsg.mapMsg μ := rfl
  simp only [Config.mapT, Config.map, View.mapP_some, hs, Multiset.filterMap_eq_map]
  rfl

/-- **A refinement with total maps and the same readings is a `RefinementT` at `τ = id`.** The
hidden fields hold vacuously. -/
theorem RefinementT.ofRefinement (R : Refinement Pr₁ Pr₂ α μ ε) :
    RefinementT Pr₁ Pr₂ α (some ∘ μ) (some ∘ ε) TimeMap.id where
  init := R.init
  tick_visible p t view st res _ h := by
    rw [View.mapP_some, NodeStepResult.mapP_some]; exact R.step _ _ _ _ _ _ h
  tick_hidden _ t _ _ _ h _ := by exact absurd (show t + 1 = t from h) (by omega)
  wake p r view st res h := by
    rw [View.mapP_some, NodeStepResult.mapP_some]; exact R.step _ _ _ _ _ _ h
  recv_visible p r view st m sm res hm h := by
    rw [View.mapP_some, NodeStepResult.mapP_some]
    rw [SignedMsg.mapP_some, Option.some.injEq] at hm
    subst hm
    exact R.step _ _ _ _ _ _ h
  recv_hidden _ _ _ _ _ _ hm _ := by simp at hm
  custom_visible p r view st ev ev₂ res he h := by
    rw [View.mapP_some, NodeStepResult.mapP_some]
    simp only [Function.comp_apply, Option.some.injEq] at he
    subst he
    exact R.step _ _ _ _ _ _ h
  custom_hidden _ _ _ _ _ _ he _ := by simp at he
  enabled r st ev ev₂ he h := by
    simp only [Function.comp_apply, Option.some.injEq] at he
    subst he
    exact R.enabled r st ev h

/-- No step of an atomic execution is a tick at `0`. -/
theorem lbl_ne_tick_zero (x : AtomicExec Pr₁ S) (i : ℕ) : x.lbl i ≠ .tickAllAwake 0 := by
  intro h
  have hs := (x.step i).1
  simp only [atomicSystem] at hs
  rw [h] at hs
  exact absurd hs (by simp [atomicSpec])

/-- At `τ = id` and total maps, every label other than the tick at `0` maps to its
`AtomicAction.map`. -/
theorem AtomicAction.mapT_id (a : AtomicAction Node Msg₁ Ev₁) (ha : a ≠ .tickAllAwake 0) :
    AtomicAction.mapT (some ∘ μ) (some ∘ ε) TimeMap.id a = some (AtomicAction.map μ ε a) := by
  cases a with
  | tickAllAwake t =>
    cases t with
    | zero => exact absurd rfl ha
    | succ t => simp [AtomicAction.mapT, AtomicAction.map, TimeMap.id]
  | _ => rfl

/-- **The step lemma with total maps, from the visible step lemma at `τ = id`.** Under a refinement `R` with
total maps and the same readings, every atomic step of the refining protocol maps to an atomic step
of the refined protocol with the mapped label, between the mapped configurations. No hypothesis on
the clocks is needed: at `τ = id` every step is visible, and the visible step lemma
(`atomicStep_visible_of_step`) uses none. -/
theorem atomicStep_map (R : Refinement Pr₁ Pr₂ α μ ε) {a : AtomicAction Node Msg₁ Ev₁}
    {c c' : Config Node Msg₁ St₁} (h : AtomicStep Pr₁ S a c c') :
    AtomicStep Pr₂ S (AtomicAction.map μ ε a) (Config.map α μ c) (Config.map α μ c') := by
  have ha : a ≠ .tickAllAwake 0 := by
    rintro rfl
    exact absurd (show c.time + 1 = 0 from h.1) (by omega)
  have hS : ScheduleOver TimeMap.id S S := ⟨fun _ => ⟨rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩⟩
  have := atomicStep_visible_of_step (RefinementT.ofRefinement R) hS h (AtomicAction.mapT_id a ha)
  rwa [Config.mapT_id, Config.mapT_id] at this

/-- The index-preserving projection of a refining execution under a refinement with total maps
and the same readings: configurations by `Config.map`, labels by `AtomicAction.map`. -/
def AtomicExec.map (R : Refinement Pr₁ Pr₂ α μ ε) (x : AtomicExec Pr₁ S) : AtomicExec Pr₂ S where
  cfg i := Config.map α μ (x.cfg i)
  lbl i := AtomicAction.map μ ε (x.lbl i)
  init := init_map R x.init
  step i := atomicStep_map R (x.step i)

/-- **At `τ = id`, `AtomicExec.map` is a `TimedProjection` with `σ = id`.** -/
def TimedProjection.ofMap (R : Refinement Pr₁ Pr₂ α μ ε) (x : AtomicExec Pr₁ S) :
    TimedProjection α (some ∘ μ) (some ∘ ε) TimeMap.id x (AtomicExec.map R x) where
  σ i := i
  zero := rfl
  step _ := Or.inr rfl
  cfg i := (Config.mapT_id x[i]).symm
  lbl_visible i _ := (AtomicAction.mapT_id (x.lbl i) (lbl_ne_tick_zero x i)).symm
  lbl_hidden i h := absurd h (by omega)

/-- The projection keeps the time: `TimedProjection.time` at `τ = id`. -/
theorem map_time (R : Refinement Pr₁ Pr₂ α μ ε) (x : AtomicExec Pr₁ S) (i : ℕ) :
    (AtomicExec.map R x)[i].time = x[i].time := (TimedProjection.ofMap R x).time i

/-- A step of the projection at the time `t` is a step of the refining execution at `t`, with the
same index. Read aloud: the refined execution reaches a time exactly when the refining one does. -/
theorem exists_step_at_time_map (R : Refinement Pr₁ Pr₂ α μ ε) (x : AtomicExec Pr₁ S) (t : Time)
    (Q : Config Node Msg₂ St₂ → Prop) :
    (∃ j : ℕ, (AtomicExec.map R x)[j].time = t ∧ Q (AtomicExec.map R x)[j]) ↔
      ∃ j : ℕ, x[j].time = t ∧ Q (Config.map α μ x[j]) := Iff.rfl


/-- The projection's node states are the mapped ones. -/
@[simp] theorem map_st (R : Refinement Pr₁ Pr₂ α μ ε) (x : AtomicExec Pr₁ S) (i : ℕ) (p : Node) :
    (AtomicExec.map R x)[i][p].st = α (x[i][p].st) := rfl

/-- The projection's sent log is the mapped one. -/
@[simp] theorem map_sent (R : Refinement Pr₁ Pr₂ α μ ε) (x : AtomicExec Pr₁ S) (i : ℕ) :
    (AtomicExec.map R x)[i].sent = (x[i].sent).map (SignedMsg.mapMsg μ) := rfl

/-- The projection's labels are the mapped ones. -/
@[simp] theorem map_lbl (R : Refinement Pr₁ Pr₂ α μ ε) (x : AtomicExec Pr₁ S) (i : ℕ) :
    (AtomicExec.map R x).lbl i = AtomicAction.map μ ε (x.lbl i) := rfl

/-- A step of the projection is a tick at `t` exactly when the refining step is. -/
theorem map_lbl_tick (R : Refinement Pr₁ Pr₂ α μ ε) (x : AtomicExec Pr₁ S) (i : ℕ) (t : Time) :
    (AtomicExec.map R x).lbl i = .tickAllAwake t ↔ x.lbl i = .tickAllAwake t := by
  constructor
  · intro h
    rw [map_lbl] at h
    cases hl : x.lbl i with
    | tickAllAwake t' => rw [hl] at h; simpa [AtomicAction.map] using h
    | _ => rw [hl] at h; simp [AtomicAction.map] at h
  · intro h; simp [map_lbl, h, AtomicAction.map]

/-- **Safety and liveness transfer alike at `τ = id`.** A property of every refined execution
holds of the projection of every refining execution. -/
theorem transfer (R : Refinement Pr₁ Pr₂ α μ ε) (x : AtomicExec Pr₁ S)
    (P : AtomicExec Pr₂ S → Prop) (h : ∀ y : AtomicExec Pr₂ S, P y) :
    P (AtomicExec.map R x) := h _

end IdCase

section IdRefinement

variable {Msg St Ev : Type} [DecidableEq Msg]

/-- Every protocol refines itself through the identity maps. -/
theorem refinement_id (Pr : Protocol Node Msg St Ev) : Refinement Pr Pr id id id where
  init _ := rfl
  step p r view st e res h := by
    have hv : view.image (SignedMsg.mapMsg (id : Msg → Msg)) = view := by
      apply Finset.image_id'
    have he : Event.map (id : Msg → Msg) (id : Ev → Ev) e = e := by
      cases e <;> rfl
    have hr : NodeStepResult.map (id : St → St) (id : Msg → Msg) res = res := by
      simp [NodeStepResult.map]
    rw [hv, he, hr]; exact h
  enabled _ _ _ h := h

end IdRefinement

end StsRefinement
