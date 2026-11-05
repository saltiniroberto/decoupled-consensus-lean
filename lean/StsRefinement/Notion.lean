module
public import StsMultisetLog.Spec.AtomicExecution
public import StsRefinement.Schedule

@[expose] public section

/-!
# The refinement notion

`RefinementT Pr₁ Pr₂ α μ ε τ` says that the refining protocol `Pr₁` refines the refined protocol
`Pr₂` of the sts framework through the state map `α`, the partial message map `μ`, the partial
event map `ε` and the time map `τ`: every refining step is either a refined step at the mapped
time, or invisible to the refined protocol. A message `m` with `μ m = none`, an event `ev` with
`ε ev = none`, and a tick at a refining time that does not move refined time have no refined
meaning.

The page also defines the projection of a configuration (`Config.mapT`) and of a step label
(`AtomicAction.mapT`), and the lifting to executions (`TimedProjection`): a refined execution
standing for a refining one, with its hidden steps removed.
-/

set_option autoImplicit false

namespace StsRefinement

open Framework.StsMultisetLog

variable {Node : Type} [DecidableEq Node]
variable {Msg₁ St₁ Ev₁ Msg₂ St₂ Ev₂ : Type} [DecidableEq Msg₁] [DecidableEq Msg₂]

/-- `SignedMsg.mapP μ m`: the signed message `m` with its object mapped by `μ`, the signer kept;
`none` when `μ` gives the object no refined meaning. -/
def SignedMsg.mapP (μ : Msg₁ → Option Msg₂) (m : SignedMsg Node Msg₁) :
    Option (SignedMsg Node Msg₂) :=
  (μ m.msg).map fun o => ⟨m.sender, o⟩

/-- `View.mapP μ view`: the refined view, the messages of `view` with a refined meaning, mapped. -/
def View.mapP (μ : Msg₁ → Option Msg₂) (view : View Node Msg₁) : View Node Msg₂ :=
  view.biUnion fun m => (SignedMsg.mapP μ m).toFinset

/-- `NodeStepResult.mapP α μ res`: the state mapped by `α`, the sends with a refined meaning
mapped by `μ`. -/
def NodeStepResult.mapP (α : St₁ → St₂) (μ : Msg₁ → Option Msg₂) (res : NodeStepResult St₁ Msg₁) :
    NodeStepResult St₂ Msg₂ :=
  ⟨α res.state, res.send.filterMap μ⟩

/-- **The refinement notion with a map on time.**
`RefinementT Pr₁ Pr₂ α μ ε τ`: the refining protocol `Pr₁` refines the refined protocol `Pr₂`
through the state map `α`, the partial message map `μ`, the partial event map `ε` and the time map
`τ` when

1. every initial state maps to the refined initial state;
2. a tick at a refining reading `t + 1` that moves refined time (`τ.Visible t`) maps to a refined
   tick at `τ (t + 1)`, from the mapped view and state, with the mapped result;
3. a tick at a reading that does not move refined time changes nothing `α` shows and sends nothing
   `μ` gives a meaning to;
4. a wake at a reading `r` maps to a refined wake at `τ r`;
5. a delivery of a message `μ` gives a meaning to maps to a refined delivery; a delivery of any
   other message changes nothing `α` shows and sends nothing with a refined meaning;
6. the same for protocol events, through `ε`, and a visible event's enabling maps forward.

Read aloud: every refining step is either a refined step at the mapped time, or invisible to the
refined protocol. -/
structure RefinementT (Pr₁ : Protocol Node Msg₁ St₁ Ev₁) (Pr₂ : Protocol Node Msg₂ St₂ Ev₂)
    (α : St₁ → St₂) (μ : Msg₁ → Option Msg₂) (ε : Ev₁ → Option Ev₂) (τ : TimeMap) : Prop where
  init : ∀ p, α (Pr₁.init p) = Pr₂.init p
  tick_visible : ∀ p (t : ℕ) view st res, τ.Visible t → Pr₁.step p (t + 1) view st .tick res →
    Pr₂.step p (τ (t + 1)) (View.mapP μ view) (α st) .tick (NodeStepResult.mapP α μ res)
  tick_hidden : ∀ p (t : ℕ) view st res, τ (t + 1) = τ t → Pr₁.step p (t + 1) view st .tick res →
    α res.state = α st ∧ res.send.filterMap μ = 0
  wake : ∀ p (r : ℕ) view st res, Pr₁.step p r view st .wake res →
    Pr₂.step p (τ r) (View.mapP μ view) (α st) .wake (NodeStepResult.mapP α μ res)
  recv_visible : ∀ p (r : ℕ) view st (m : SignedMsg Node Msg₁) (sm : SignedMsg Node Msg₂) res,
    SignedMsg.mapP μ m = some sm → Pr₁.step p r view st (.recv m) res →
    Pr₂.step p (τ r) (View.mapP μ view) (α st) (.recv sm) (NodeStepResult.mapP α μ res)
  recv_hidden : ∀ p (r : ℕ) view st (m : SignedMsg Node Msg₁) res, μ m.msg = none →
    Pr₁.step p r view st (.recv m) res → α res.state = α st ∧ res.send.filterMap μ = 0
  custom_visible : ∀ p (r : ℕ) view st (ev : Ev₁) (ev₂ : Ev₂) res, ε ev = some ev₂ →
    Pr₁.step p r view st (.custom ev) res →
    Pr₂.step p (τ r) (View.mapP μ view) (α st) (.custom ev₂) (NodeStepResult.mapP α μ res)
  custom_hidden : ∀ p (r : ℕ) view st (ev : Ev₁) res, ε ev = none →
    Pr₁.step p r view st (.custom ev) res → α res.state = α st ∧ res.send.filterMap μ = 0
  enabled : ∀ (r : ℕ) st (ev : Ev₁) (ev₂ : Ev₂), ε ev = some ev₂ → Pr₁.enabled r st ev →
    Pr₂.enabled (τ r) (α st) ev₂

/-- `Config.mapT α μ τ c`: the refined configuration `c` stands for: real time and every clock
read through `τ`, every node state through `α`, every view and the sent log `c.sent` through `μ`,
the messages without a refined meaning dropped. -/
def Config.mapT (α : St₁ → St₂) (μ : Msg₁ → Option Msg₂) (τ : TimeMap)
    (c : Config Node Msg₁ St₁) : Config Node Msg₂ St₂ :=
  { time := τ c.time
    nodes := fun p => { clock := τ c[p].clock, st := α c[p].st, view := View.mapP μ c[p].view }
    sent := c.sent.filterMap (SignedMsg.mapP μ) }

/-- `AtomicAction.mapT μ ε τ a`: the refined label a refining label stands for, or `none` for a
hidden step: a tick that does not move refined time, the delivery, forward or adversarial send of
a message without a refined meaning, a protocol event without one. The tick at `0` is never
enabled (`tickAllAwake t` needs the time `t − 1`), so it maps to `none`. -/
def AtomicAction.mapT (μ : Msg₁ → Option Msg₂) (ε : Ev₁ → Option Ev₂) (τ : TimeMap) :
    AtomicAction Node Msg₁ Ev₁ → Option (AtomicAction Node Msg₂ Ev₂)
  | .tickAllAwake 0 => none
  | .tickAllAwake (t + 1) => if τ (t + 1) = τ t + 1 then some (.tickAllAwake (τ (t + 1))) else none
  | .deliver p m => (SignedMsg.mapP μ m).map (.deliver p)
  | .custom p ev => (ε ev).map (.custom p)
  | .adversarial p m => (μ m).map (.adversarial p)
  | .forward p m => (SignedMsg.mapP μ m).map (.forward p)

variable {Pr₁ : Protocol Node Msg₁ St₁ Ev₁} {Pr₂ : Protocol Node Msg₂ St₂ Ev₂}
  {S₁ S₂ : Schedule Node}

/-- **The lifting of a refinement to executions.** `TimedProjection α μ ε τ x y`: the refined
execution `y` stands for the refining execution `x` through the step map `σ`: `σ` starts at `0`
and moves by `0` or `1` per refining step; the refined configuration after `σ i` steps is the
projection of the refining one after `i` steps; a refining step that moves `σ` has the refined
step's label mapped to, and one that does not move it is hidden. Steps of `y` beyond every `σ i`
(when `x` has finitely many visible steps) are any continuation. Read aloud: `y` is `x` with its
hidden steps removed, seen through the maps. -/
structure TimedProjection (α : St₁ → St₂) (μ : Msg₁ → Option Msg₂) (ε : Ev₁ → Option Ev₂)
    (τ : TimeMap) (x : AtomicExec Pr₁ S₁) (y : AtomicExec Pr₂ S₂) where
  /-- The step map: `y`'s step `σ i` stands for `x`'s step `i`. -/
  σ : ℕ → ℕ
  zero : σ 0 = 0
  step : ∀ i, σ (i + 1) = σ i ∨ σ (i + 1) = σ i + 1
  cfg : ∀ i, y[σ i] = Config.mapT α μ τ x[i]
  lbl_visible : ∀ i, σ (i + 1) = σ i + 1 → some (y.lbl (σ i)) = AtomicAction.mapT μ ε τ (x.lbl i)
  lbl_hidden : ∀ i, σ (i + 1) = σ i → AtomicAction.mapT μ ε τ (x.lbl i) = none

end StsRefinement
