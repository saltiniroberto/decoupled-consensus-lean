module
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.PhaseDefs
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.AtomicReaders
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.HealedAttestationDefs
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.ConfirmedTipDefs
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.QuietRoundDefs
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.TickDefs
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.FGStateDefs
public import GoldilocksCorrectness.Statements.Routines.TickStatements
public import GoldilocksCorrectness.Statements.Executions.Lemma89Defs

@[expose] public section

/-!
# Lemma89Defs, over a model

The definitions of `GoldilocksCorrectness/Statements/Executions/Lemma89Defs.lean` over a model `M`,
for an execution `x` of `protocolOf M S`: the events at a validator's node state, the members'
confirmations of a window and their chain, the stability of the members' frames through a window,
the action time of a round and the member set of a slot, read at the model's times; an honest
attestation, the threshold on the old attestations, the fast families, the round's base, an honest
opening's proposal and its root collision (its view form on the view of `x`), the kinds of an
opening, and the change of a validator's fork choice. The round's base reads the live locks of every
outcome of the model's tick at the vote time of the round's first slot from a member awake since
that slot's duty window's start (`AwakeFor`); the fork choice's change reads the greatest
chain-state height of the node's tree, `hMax`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (slotStart voteTime supportCutoff)

namespace GoldilocksCorrectness.Record.Statements.Executions

open GoldilocksCorrectness.Record.Statements.Routines (VoterTreeAt AwakeFor ResolvesAt)
open GoldilocksCorrectness.Record.Statements.Routines (hMax)
open GoldilocksCorrectness.Record.Statements.View (nodeView RootCollisionAtOpeningV)

open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)

open Goldilocks
open Goldilocks.Sts (Setup)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V)

/-- `RootOffChainAt M S Sched x w t X`: `w`'s fork-choice root before time `t` is not `X` or an
ancestor of `X`.

The variables:
- `M`: the model;
- `S`, `Sched`, `x`: the setup, the schedule, the execution;
- `w`: the validator; `t`: the time; `X`: the block.

Read aloud: `w`'s root has left `X`'s chain. -/
def RootOffChainAt (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)
    (w : V) (t : ℕ) (X : Block V) : Prop :=
  ¬ (M.get_fc_root (x.stateBefore t w)).AncestorEq X

/-- `RootIncompatibleAt M S Sched x w t X`: `w`'s fork-choice root before time `t` is neither `X`
or an ancestor of `X` nor a descendant of `X`.

The variables:
- `M`: the model;
- `S`, `Sched`, `x`: the setup, the schedule, the execution;
- `w`: the validator; `t`: the time; `X`: the block.

Read aloud: `w`'s root conflicts with `X`. -/
def RootIncompatibleAt (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)
    (w : V) (t : ℕ) (X : Block V) : Prop :=
  ¬ ((M.get_fc_root (x.stateBefore t w)).compatible X = true)

/-- `FinalizedIncompatibleAt M S Sched x w t X`: `w`'s finalized block before time `t` is neither
`X` or an ancestor of `X` nor a descendant of `X`.

The variables:
- `M`: the model;
- `S`, `Sched`, `x`: the setup, the schedule, the execution;
- `w`: the validator; `t`: the time; `X`: the block.

Read aloud: `w`'s finalized block conflicts with `X`. -/
def FinalizedIncompatibleAt (S : Setup V) (A : Activity V)
  (x : Trace V (NamedObject V) M.N)
    (w : V) (t : ℕ) (X : Block V) : Prop :=
  ¬ ((x.stateBefore t w).finalized.compatible X = true)

/-- `RootOffChainAtTick M S Sched x w c X`: the fork-choice root of the state `w`'s tick to the clock
value `c` starts from is not `X` or an ancestor of `X`. It is `RootOffChainAt` read at that tick's
input, the state the tick's vote or update is computed from.

The variables:
- `M`: the model;
- `S`, `Sched`, `x`: the setup, the schedule, the execution;
- `w`: the validator; `c`: the clock value of the tick; `X`: the block.

Read aloud: the root `w`'s tick to `c` starts from has left `X`'s chain. -/
def RootOffChainAtTick (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)
    (w : V) (c : ℕ) (X : Block V) : Prop :=
  ¬ (M.get_fc_root (x.tickInput w c)).AncestorEq X

/-- `HeadHeightFloorPastAtTick M S Sched x w c h`: the `head_height_floor` of the state `w`'s tick
to the clock value `c` starts from (the least chain-state height of a viable block in that state)
is greater than `h`. It is `HeadHeightFloorPastAt` read at that tick's input, the state the tick's
vote or update is computed from.

The variables:
- `M`: the model;
- `S`, `Sched`, `x`: the setup, the schedule, the execution;
- `w`: the validator; `c`: the clock value of the tick; `h`: the height.

Read aloud: in the state `w`'s tick to `c` starts from, no block of chain-state height `h` is
viable. -/
def HeadHeightFloorPastAtTick (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)
    (w : V) (c : ℕ) (h : Height) : Prop :=
  h < M.head_height_floor (x.tickInput w c)

/-- `RootIncompatibleAtTick M S Sched x w c X`: the fork-choice root of the state `w`'s tick to the
clock value `c` starts from is neither `X` or an ancestor of `X` nor a descendant of `X`. It is
`RootIncompatibleAt` read at that tick's input.

The variables:
- `M`: the model;
- `S`, `Sched`, `x`: the setup, the schedule, the execution;
- `w`: the validator; `c`: the clock value of the tick; `X`: the block.

Read aloud: the root `w`'s tick to `c` starts from conflicts with `X`. -/
def RootIncompatibleAtTick (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)
    (w : V) (c : ℕ) (X : Block V) : Prop :=
  ¬ ((M.get_fc_root (x.tickInput w c)).compatible X = true)

/-- `FinalizedIncompatibleAtTick M S Sched x w c X`: the finalized block of the state `w`'s tick to
the clock value `c` starts from is neither `X` or an ancestor of `X` nor a descendant of `X`. It is
`FinalizedIncompatibleAt` read at that tick's input.

The variables:
- `M`: the model;
- `S`, `Sched`, `x`: the setup, the schedule, the execution;
- `w`: the validator; `c`: the clock value of the tick; `X`: the block.

Read aloud: the finalized block `w`'s tick to `c` reads conflicts with `X`. -/
def FinalizedIncompatibleAtTick (S : Setup V) (A : Activity V)
  (x : Trace V (NamedObject V) M.N)
    (w : V) (c : ℕ) (X : Block V) : Prop :=
  ¬ ((x.tickInput w c).finalized.compatible X = true)

/-- `WindowConfirmation M S Sched x Hon a b X`: `X` is the confirmation some member of `Hon (σ + 1)`
saved for a slot `σ` from `a` to `b`, on its node state right after the support cutoff of slot
`σ + 1`.

The variables:
- `M`: the model;
- `S`, `Sched`, `x`: the setup, the schedule, the execution;
- `Hon`: one member set per slot; `a`, `b`: the first and the last slot; `X`: the block.

Read aloud: `X` is a member's confirmation of a slot from `a` to `b`. -/
def WindowConfirmation (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)
    (Hon : ℕ → Finset V) (a b : ℕ) (X : Block V) : Prop :=
  ∃ σ, a ≤ σ ∧ σ ≤ b ∧ ∃ v ∈ Hon (σ + 1),
    (x.tickOutput v (M.supportCutoff S.C (σ + 1))).savedConfirmation σ = some X

/-- `ConfirmationsChainOn M S Sched x Hon a b`: for any two slots `σ ≤ σ'` from `a` to `b`, a
confirmation a member of `Hon (σ + 1)` saved for slot `σ` is an ancestor of, or equal to, one a
member of `Hon (σ' + 1)` saved for slot `σ'` when `σ < σ'`, and compatible with it when `σ = σ'`.

The variables:
- `M`: the model;
- `S`, `Sched`, `x`: the setup, the schedule, the execution;
- `Hon`: one member set per slot; `a`, `b`: the first and the last slot.

Read aloud: the members' confirmations of the slots from `a` to `b` form one chain; the honest
chain does not switch between `a` and `b`. -/
def ConfirmationsChainOn (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)
    (Hon : ℕ → Finset V) (a b : ℕ) : Prop :=
  ∀ (σ σ' : ℕ) (v v' : V) (C C' : Block V), a ≤ σ → σ ≤ σ' → σ' ≤ b →
    v ∈ Hon (σ + 1) → v' ∈ Hon (σ' + 1) →
    (x.tickOutput v (M.supportCutoff S.C (σ + 1))).savedConfirmation σ = some C →
    (x.tickOutput v' (M.supportCutoff S.C (σ' + 1))).savedConfirmation σ' = some C' →
    (σ < σ' → C.AncestorEq C') ∧ (σ = σ' → C.compatible C' = true)

omit [RootOrder] in
/-- `JustifiedWitness M S Y h J`: the chain state of `Y` has justified `J` at the height `h`: its
justification height is `h` and its justified block is `J`.

The variables:
- `M`: the model;
- `S`: the setup; `Y`: the block; `h`: the height; `J`: the justified block.

Read aloud: `Y`'s chain justified `J` at `h`, and nothing after. -/
def JustifiedWitness (S : Setup V) (Y : Block V) (h : Height) (J : Block V) : Prop :=
  (M.chainStateOf S.C Y).h_j = h ∧ (M.chainStateOf S.C Y).J = J

/-- `HeadHeightFloorPastAt M S Sched x w t h`: `w`'s `head_height_floor` before time `t` (the least
chain-state height of a viable block in its state) is greater than `h`.

The variables:
- `M`: the model;
- `S`, `Sched`, `x`: the setup, the schedule, the execution;
- `w`: the validator; `t`: the time; `h`: the height.

Read aloud: `w` finds no block of chain-state height `h` viable. -/
def HeadHeightFloorPastAt (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)
    (w : V) (t : ℕ) (h : Height) : Prop :=
  h < M.head_height_floor (x.stateBefore t w)

/-- `FrontWindowStable M S Sched x Hon s_w s'`: the frames of the members are stable from slot
`s_w + k − 1` to slot `s'`:

1. at every slot `s₁` from `s_w + k − 1` to `s' − 1`, every member of `Hon (s₁ + 1)` satisfies
   `StepFrameAt` relative to every confirmation a member of `Hon (σ + 1)` saved for a slot `σ`
   from `s_w + k − 1` to `s₁`;
2. every member of `Hon s'` has, in the state its tick to the vote time of slot `s' + 1` starts
   from, its fork-choice root on the chain of a live lock block of a member (in the state that
   member's own tick to that vote time starts from) or of a confirmation of slot `s' − 1` a member
   saved at its tick to the support cutoff of slot `s'`.

The variables:
- `M`: the model;
- `S`, `Sched`, `x`: the setup, the schedule, the execution;
- `Hon`: one member set per slot; `s_w`: the slot the window is counted from; `s'`: its last
  slot.

Read aloud: through the window no member's frame leaves the chain of the members'
confirmations, and at its last slot every member's root is on the chain of a member's live lock or
confirmation. -/
def FrontWindowStable (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)
    (Hon : ℕ → Finset V) (s_w s' : ℕ) : Prop :=
  (∀ s₁, s_w + S.C.k - 1 ≤ s₁ → s₁ < s' →
    ∀ σ, s_w + S.C.k - 1 ≤ σ → σ ≤ s₁ → ∀ v ∈ Hon (σ + 1), ∀ C : Block V,
      (x.tickOutput v (M.supportCutoff S.C (σ + 1))).savedConfirmation σ = some C →
      ∀ w ∈ Hon (s₁ + 1), StepFrameAt M S A x C s₁ w) ∧
  (∀ w ∈ Hon s', ∃ D : Block V,
    ((∃ u ∈ Hon s', ∃ e ∈ (x.tickInput u (M.voteTime S.C (s' + 1))).lockEntries,
        M.is_live (x.tickInput u (M.voteTime S.C (s' + 1)))
          ((M.voteTime S.C (s' + 1) : ℕ) : Int) e = true ∧ e.B = D) ∨
      ∃ v ∈ Hon s',
        (x.tickOutput v (M.supportCutoff S.C s')).savedConfirmation (s' - 1) = some D) ∧
    (M.get_fc_root (x.tickInput w (M.voteTime S.C (s' + 1)))).AncestorEq D)

omit [RootOrder] in
/-- `aR M S r`: the action time of round `r`, the support cutoff of slot `r * R + 1`, where the
confirmation update of slot `r * R` runs and the attestation duty follows it.

The variables:
- `M`: the model.

Read aloud: `M.slotStart S.C (r * R) + 6Δ`. -/
def aR (S : Setup V) (r : ℕ) : ℕ := M.supportCutoff S.C (r * S.C.R + 1)

omit [RootOrder] in
/-- `Hon M S Sched σ`: the member set of slot `σ`, the validators outside the adversary set at the
support cutoff of slot `σ + 1`, where the update of slot `σ` runs
(`roundMembers M S Sched (σ + 1)`). An updater of slot `σ` (`updaterAt M S Sched σ`, active up to its
own tick) need not be a member: it may be corrupted after that tick and by the cutoff's real time.
Within a phase whose members are active (the bundle's `hActive`), every member is an updater.

The variables:
- `M`: the model.

Read aloud: the validators honest at the update of slot `σ`. -/
noncomputable def Hon (S : Setup V) (A : Activity V) {Msg N : Type} (x : Trace V Msg N) (σ : ℕ) : Finset V := roundMembers M S A x (σ + 1)

/-- `HonestAttestationAt M S Sched x t v a`: the step `i` that is the tick of `v` at the time `t`
puts on the wire the attestation `a` of `v`.

No `v ∈ A.activeAtTime x t` is asked beside the tick: a
tick is by a validator awake and outside the adversary set at its own step (the environment's
`tick_active`).

The variables:
- `M`: the model.

Read aloud: `v` sent `a` at its tick at `t`. -/
def HonestAttestationAt (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)
    (t : ℕ) (v : V) (a : Attestation V) : Prop :=
  ∃ i : ℕ, x.lbl i = Event.tick v t ∧
    (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i

/-- `OldHeightAttained M S Sched x T₁ H₂`: every attestation a validator awake at its tick and
outside the adversary set at `T₁` put on the wire at a tick before `T₁` has height at most `H₂`
(`OldAttestationsAtMostHonestAt`, the senders' honesty read at `T₁`), and `H₂` is `0` or the height
of such an attestation, whose sender is honest at its tick and at `T₁`. This is the threshold `H₂`
of the route over the attesters honest at `T₁`: the greatest height attested
before `T₁` by a validator still honest at `T₁`.

The variables:
- `M`: the model.

Read aloud: `H₂` is the greatest height attested before `T₁` by a validator honest at `T₁`. -/
def OldHeightAttained (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)
    (T₁ H₂ : ℕ) : Prop :=
  OldAttestationsAtMostHonestAt M S A x T₁ T₁ H₂ ∧
    (H₂ = 0 ∨ ∃ (t : ℕ) (v : V) (a : Attestation V), t < T₁ ∧
      HonestAttestationAt M S A x t v a ∧ v ∉ A.corruptedAtTime x T₁ ∧ a.h = H₂)

/-- `FastFamily M S Sched x r L s C`: `C` is `L` or an ancestor of `L`, or `C` is a confirmation
some member of `Hon M S Sched σ` saved for a slot `σ` from `r * R` to before `s`, or an ancestor of
one. This is the family part A's chain invariant is read for at slot `s`: closed under ancestors, so
that every anchor, root and lock block on the chain is in it.

The variables:
- `M`: the model.

Read aloud: the fast block's line and every confirmation the members saved since its round. -/
def FastFamily (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)
    (r : ℕ) (L : Block V) (s : ℕ) (C : Block V) : Prop :=
  C.AncestorEq L ∨
    ∃ σ : ℕ, r * S.C.R ≤ σ ∧ σ < s ∧ ∃ v ∈ Hon M S A x σ, ∃ C' : Block V,
      (x.tickOutput v (M.supportCutoff S.C (σ + 1))).savedConfirmation σ = some C' ∧
      C.AncestorEq C'

/-- `FastFamilyFrom M S Sched x s₁ L s C`: `C` is `L` or an ancestor of `L`, or `C` is a
confirmation some member of `Hon M S Sched σ` saved for a slot `σ` from `s₁` to before `s`, or an
ancestor of one. `FastFamily M S Sched x r L s` is the case `s₁ = r * R`. Part A reads it with
`s₁ = r * R + k`: the members' confirmations of the slots `r * R` to `r * R + k − 1` are left out,
because a lock made before slot `r * R + 1` on a strict descendant of `L` can pull honest votes onto
one branch above `L` while a member confirms a block on another, and a member's root can later
conflict with that confirmation.

The variables:
- `M`: the model;
- `S`, `Sched`, `x`: the setup, the schedule, the execution;
- `s₁`: the first slot whose confirmations are in the family; `L`: the fast block;
- `s`: the slot the family is read at (its confirmations are those of slots before `s`);
- `C`: the block.

Read aloud: the fast block's line and every confirmation the members saved from slot `s₁` on. -/
def FastFamilyFrom (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)
    (s₁ : ℕ) (L : Block V) (s : ℕ) (C : Block V) : Prop :=
  C.AncestorEq L ∨
    ∃ σ : ℕ, s₁ ≤ σ ∧ σ < s ∧ ∃ v ∈ Hon M S A x σ, ∃ C' : Block V,
      (x.tickOutput v (M.supportCutoff S.C (σ + 1))).savedConfirmation σ = some C' ∧
      C.AncestorEq C'

/-- `RoundBaseAt M S Sched x B s`: at the first slot `s` of a round with the proposal `B`,
every member of `Hon M S Sched s` has, in the state its tick to the vote time of slot `s` starts
from, its fork-choice root `B.parent` or an ancestor of it and its `head_height_floor` at most the
chain-state height of `B.parent`; every updater of slot `s` (`updaterAt M S A x s`, the validators
that tick to `M.supportCutoff S.C (s + 1)` awake and outside the adversary set up to that tick) has, in
the state that tick starts from, its root `B` or an ancestor of `B` and its `head_height_floor` at most
`B`'s chain-state height; and, when it has been awake since the duty window's start of slot `s` (`AwakeFor`), every
lock entry an outcome of its tick at the vote time of slot `s` leaves live is on `B.parent` or an
ancestor of it.

The three clauses read each member's own state at its own tick,
as `QuietRoundOnConfirmations`'s first two clauses do; at both clock bounds `0` they are `dev`'s reads
before the vote time and before the support cutoff. The second clause ranges over the updaters, not over
`Hon M S A x s`: `Hon` reads the adversary set at the real time of the cutoff,
the clause reads each validator's state at its own tick to it, and the updaters are the validators that
have that tick and are honest at it.

The variables:
- `M`: the model;
- `S`, `Sched`, `x`: the setup, the schedule, the execution;
- `B`: the round's proposal; `s`: the round's first slot.

Read aloud: at the round's first slot the members' frames follow the proposal's parent and then
the proposal, and no live lock of an awake member pulls a vote off the parent's chain. -/
def RoundBaseAt (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)
    (B : Block V) (s : ℕ) : Prop :=
  (∀ w ∈ Hon M S A x s,
      (M.get_fc_root (x.tickInput w (M.voteTime S.C s))).AncestorEq B.parent ∧
    M.head_height_floor (x.tickInput w (M.voteTime S.C s)) ≤ (M.chainStateOf S.C B.parent).h) ∧
  (∀ v ∈ updaterAt M S A x s,
      (M.get_fc_root (x.tickInput v (M.supportCutoff S.C (s + 1)))).AncestorEq B ∧
    M.head_height_floor (x.tickInput v (M.supportCutoff S.C (s + 1))) ≤
      (M.chainStateOf S.C B).h) ∧
  (∀ w ∈ Hon M S A x s, ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C s))
        ((M.voteTime S.C s : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C s)) s →
    ∀ e ∈ M.lockEntries n',
      M.is_live (x.tickInput w (M.voteTime S.C s)) ((M.voteTime S.C s : ℕ) : Int) e = true →
      e.B.AncestorEq B.parent)

/-- `ProposalAt M S x s B`: the proposer of slot `s` put the block `B` on the wire at its own tick to
the start of slot `s`.

The variables:
- `M`: the model;
- `S`: the setup; `x`: the trace; `s`: the slot; `B`: the block.

Read aloud: `B` is slot `s`'s proposal. -/
def ProposalAt (S : Setup V) (x : Trace V (NamedObject V) M.N) (s : ℕ) (B : Block V) : Prop :=
  ∃ i : ℕ, x.lbl i = Event.tick (S.P.proposer s) (M.slotStart S.C s) ∧
    (⟨S.P.proposer s, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i

/-- `RootCollisionAtOpening M S Sched x r m`: for some opening `i ≤ m`, the proposer of slot
`r i * R` put a block `B` on the wire at its tick at that slot's start, and some block the
proposer held before that start has `B`'s root.

Defined as its view form: `RootCollisionAtOpeningV` with
Goldilocks's vocabulary `GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks`, on the view
of `x`, `projectTrace (nodeView M) x.toTrace`, whose node states are read as each validator's
finalized block, confirmed tip (`confirmedOf`) and held blocks. `rootCollisionAtOpening_unfold`
(`Proofs/View/Bridges.lean`) reads it on the execution's node states.

The variables:
- `M`: the model.

Read aloud: some honest round opening slot's proposal has the root of a block its proposer already held. -/
def RootCollisionAtOpening (S : Setup V) (A : Activity V)
  (x : Trace V (NamedObject V) M.N)
    (r : ℕ → ℕ) (m : ℕ) : Prop :=
  RootCollisionAtOpeningV M GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks S ((x.map (nodeView M))) r m

/-- `Spoiled M S Sched x r i`: opening `i` of the sequence `r` is not quiet relative to its own
confirmations: some proposal `B` of its first slot fails `QuietRoundOnConfirmations` with the
member sets `Hon M S Sched` and the next opening's first slot `r (i + 1) * R`.

The variables:
- `M`: the model.

Read aloud: opening `i`'s round is spoiled. -/
def Spoiled (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)
    (r : ℕ → ℕ) (i : ℕ) : Prop :=
  ∃ B : Block V, ProposalAt M S x (r i * S.C.R) B ∧
    ¬ QuietRoundOnConfirmations M S A x (Hon M S A x) B (r i * S.C.R) (r (i + 1) * S.C.R)

/-- `QuietWithBase M S Sched x r i`: opening `i` is quiet relative to its own confirmations and the
window of `2k − 1` slots before its first slot is stable (`FrontWindowStable` with the member sets
`Hon M S Sched`).

The variables:
- `M`: the model.

Read aloud: opening `i`'s round is quiet and has its base. -/
def QuietWithBase (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)
    (r : ℕ → ℕ) (i : ℕ) : Prop :=
  (∀ B : Block V, ProposalAt M S x (r i * S.C.R) B →
    QuietRoundOnConfirmations M S A x (Hon M S A x) B (r i * S.C.R) (r (i + 1) * S.C.R)) ∧
  FrontWindowStable M S A x (Hon M S A x) (r i * S.C.R - 2 * S.C.k) (r i * S.C.R - 1)

/-- `ForkChoiceChangeStep M S A x w j`: the step `j` changes `w`'s fork choice in a way a window can
fail on: after the step, `w`'s `h_max` is its `h_j + 1` and its root (`get_fc_root` of its FG state
after the step) is its justified block `J`, so that `get_fc_root` returns `J` by its first case, and
that root is neither `w`'s root before the step nor an ancestor of it; or `w`'s `head_height_floor`
after the step is greater than before.

A root that moves to an ancestor (from `J` to `F`) is not a change here: everything compatible with
the old root is compatible with the new one. A root that moves from `F` to a descendant `J` through
`get_fc_root`'s first case is a change: blocks off `J`'s chain leave the fork choice. The conjunct
`h_max = h_j + 1` leaves out one case: `w`'s finalized block moves onto its justified
block while `h_max ≥ h_j + 2`, so that the root, `get_fc_root`'s second case (the finalized block),
happens to equal `J`. That move changes no viable head of `w`.

Only `w`'s own steps (its tick, restart or deliveries) change `w`'s state, so at any other step this
predicate is false.

The variables:
- `M`: the model;
- `S`, `A`, `x`: the setup, the activity, the execution; `w`: the validator; `j`: the step.

Read aloud: at the step `j`, `w`'s root becomes its justified block through the case
`h_max = h_j + 1`, other than an ancestor of its old root, or its least viable height rises. -/
def ForkChoiceChangeStep (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)
    (w : V) (j : ℕ) : Prop :=
  (M.get_fc_root (x.st (j + 1) w) = (x.st (j + 1) w).justified ∧
    hMax M S.C (x.st (j + 1) w) = (x.st (j + 1) w).justifiedHeight + 1 ∧
    ¬ (M.get_fc_root (x.st (j + 1) w)).AncestorEq (M.get_fc_root (x.st j w))) ∨
  M.head_height_floor (x.st j w) < M.head_height_floor (x.st (j + 1) w)

end GoldilocksCorrectness.Record.Statements.Executions

