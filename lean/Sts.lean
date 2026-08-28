import Spec
import StsMultisetLog

/-!
# The protocol as a transition system

The boundary between `Spec/` and the sts framework (`deps/lean-sts`, the `StsMultisetLog`
flavour). Nothing here is protocol content: `Spec/` says what a validator does, and this file
says when it does it, in the shape the framework's `Protocol` wants — an `init`, and a step
relation over the framework's events.

**Nothing in `Spec/` imports this**, and nothing here changes a definition there. The
extractor does not read it either, so no line of it reaches the document.

## The three events, and what runs on each

`tick` runs `on_tick`, the protocol's own (`Defs/Tick.lean`, this layer's reading in
`09_Healing.lean`). It sets the clock and runs whatever the schedule puts at that instant.

`recv m` runs the handler for the kind of message that arrived, which is what makes the
handlers handlers: `process_block`, `process_goldfish_vote`, `process_sg_vote`. They are the
routines of `Spec/` that take a wire object and fold it into the store, and each is reached
here and nowhere else — no duty calls one after this file exists.

`wake` does nothing. A validator that has slept holds a store whose clock is behind, and the
next `tick` moves it; nothing in this protocol is owed at the moment of waking.

## Where an attestation goes

The round's head no longer travels in a message of its own: `sg_vote` produces a head and the
attestation carries it (`09_Healing.lean`). So an arriving attestation runs `process_sg_vote`
on the SG vote it contains — its validator, its round, its head. A bare `sg_vote` message
runs the same handler, and nothing an honest validator does sends one.

## The clock

The framework hands a reaction `r`, the validator's own clock reading, a `Nat` counting its
ticks. This spec's `Σ.t` is an `Int`, starting at `-1` and moving to whatever `on_tick`
is given, and all of its scheduled instants — `t_s`, `t_s + Δ`, `Γ_j`, the round's action
instant — are values of that clock. So a tick reading `r` is the instant `r` itself:
one tick per unit of the spec's time, and `Σ.t = -1` until the first.

Nothing here says the instants are multiples of `Δ`, which the protocol's own schedule does
say. Putting the ticks on a `Δ` grid instead would be a stronger model, and would also miss
`sgfg_voting i r`, which `SGSchedule` bounds but does not place.

## A raise is not a step

A `Spec/` routine raises when it reads a store that does not record what it asks for — a
block outside `Σ.σ`, say. Those outcomes are not reactions: the step relation holds of the
successful ones. A configuration with no successful outcome at all would leave the protocol
stuck, which the framework forbids, so the relation admits one fallback there — the store
unchanged, nothing sent. `total` is what that fallback discharges; on a store the protocol
can actually reach, no branch of it is taken.
-/

set_option autoImplicit false

namespace DC

open Framework.StsMultisetLog

variable {Validator : Type} [Roots] [DecidableEq Validator] [Electorate Validator]
  [Committees Validator] [RootComputation Validator] [Params] [SGSchedule Validator]
  [GoldfishWalk Validator] [Tick Validator]

/-- The handler that runs when `m` arrives: the store routine of `Spec/` for that kind of
    wire object. An attestation runs the SG-vote handler on the vote it carries, for the
    reason the module header gives. -/
def Store.receive (S : Store Validator) (m : Message Validator) : DRE (Store Validator) :=
  match m with
  | .block B => S.processBlock B
  | .gfVote vote => pure (S.processGoldfishVote vote)
  | .sgVote vote => S.processSGVote vote
  | .attestation a =>
      S.processSGVote (SGVote.mk (validator := a.validator) (round := a.round)
        (head := a.head))

/-- The reactions a validator may have to `e`, holding store `S` with its clock about to
    read `t`: each an answer, so a raised outcome is no reaction. A `tick` may pick, so this
    is a set; the other events are deterministic and it is a singleton or empty. -/
def reactions (S : Store Validator) (t : Int)
    (isProposer : (s : Nat) → (i : Validator) → Bool)
    (e : Event Validator (Message Validator) Empty) :
    Set (NodeStepResult (Store Validator) (Message Validator)) :=
  match e with
  | .tick =>
      { res | ∃ d ∈ (S.onTick t isProposer).outcomes,
          ∃ r : DutyResult Validator, d = .ok r ∧
            res = { state := r.state, send := r.send.val } }
  | .recv m =>
      { res | ∃ S', S.receive m.msg = .ok S' ∧ res = { state := S', send := 0 } }
  | .wake => { res | res = { state := S, send := 0 } }
  | .custom ev => ev.elim

/-- The protocol, in the framework's shape.

    `init i` is `Σ.gen i`, the initial store of the validator running that node — which is
    where `Σ.id` comes from, and why no reaction reads the framework's `p`.

    The step relation is `reactions`, plus the one fallback that keeps the protocol from
    being stuck when nothing succeeds. `Ev := Empty`: every instant this protocol acts at is
    a time, so the framework's own `tick` carries them all and there is no protocol-specific
    event to enable. -/
def protocol (isProposer : (s : Nat) → (i : Validator) → Bool) :
    Protocol Validator (Message Validator) (Store Validator) Empty where
  init i := Store.gen i
  step _p r _view S e res :=
    res ∈ reactions S (r : Int) isProposer e ∨
      (reactions S (r : Int) isProposer e = ∅ ∧ res = { state := S, send := 0 })
  total := by
    classical
    intro _p r _view S e
    by_cases h : (reactions S (r : Int) isProposer e).Nonempty
    · obtain ⟨res, hres⟩ := h
      exact ⟨res, Or.inl hres⟩
    · exact ⟨{ state := S, send := 0 },
        Or.inr ⟨Set.not_nonempty_iff_eq_empty.mp h, rfl⟩⟩
  enabled _ _ ev := ev.elim

end DC
