module
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.SleepyDefs
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.HonestChainDefs
public import GoldilocksCorrectness.Statements.Executions.HonestChainAfterHealingDefs

@[expose] public section

/-!
# HonestChainAfterHealingDefs, over a model

The definitions of `GoldilocksCorrectness/Statements/Executions/HonestChainAfterHealingDefs.lean`
over a model `M`, for an execution `x` of `protocolOf M S`: the conditions on a member's fgroot,
voter's tree and finalized block that let the chain step at a slot follow a block, the invariant
over a family of blocks, the live locks on a family, and the voter's and the updater's conditions
against the honest chain. The voter's tree is read through `VoterTreeAt`; the live locks through
every outcome of the model's tick at the vote time from a validator awake since the duty window's
start (`AwakeFor`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (voteTime supportCutoff)

namespace GoldilocksCorrectness.Record.Statements.Executions

open GoldilocksCorrectness.Record.Statements.Routines (VoterTreeAt AwakeFor ResolvesAt)

open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Statements.Routines (expireLocks)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V)

/-- `StepFrameAt M S Sched x B s' w`: the frame conditions of the chain step at slot `s'` relative
to the block `B`, at `w`. On the state `w`'s tick to the vote time of slot `s' + 1` starts from,
the state its vote of slot `s' + 1` is computed from, the root of its fork choice is compatible
with `B`;
when that root is `B` or an ancestor of `B`, some block of `w`'s voter tree for slot `s' + 1` that
is `B` or a descendant of `B` is a viable head; and the finalized block of the state `w`'s tick to
the support cutoff of slot `s' + 2` starts from, the block its update reads, is compatible with `B`
. These are Lemma 79's `hF2`, `hF3` and `hFv` at one member.



The variables:
- `M`: the model;
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `B`: the block; `s'`: the slot of the step; `w`: the member.

It is `StepFrameAtTimes M S Sched x B s' (M.voteTime S.C (s' + 1)) (M.supportCutoff S.C (s' + 2)) w`
(`stepFrameAt_iff`).

Read aloud: `w`'s finality gadget lets its vote of slot `s' + 1` and its update of slot `s' + 1`
follow `B`'s chain. -/
def StepFrameAt (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)
    (B : Block V) (s' : ℕ) (w : V) : Prop :=
  (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s' + 1)))).fc_root.compatible B = true ∧
  ((M.fg_to_ac (x.tickInput w (M.voteTime S.C (s' + 1)))).fc_root.AncestorEq B →
    ∃ W, VoterTreeAt M (x.tickInput w (M.voteTime S.C (s' + 1)))
      (S.C.t_ ((s' + 1) - 1) + 3 * S.C.Δ) (s' + 1) W ∧
          W ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s' + 1)))).viable_heads ∧
        B.AncestorEq W) ∧
  (x.tickInput w (M.supportCutoff S.C (s' + 2))).finalized.compatible B = true

/-- `StepFrameAtTimes M S Sched x B s' t_v t_u w`: `StepFrameAt M S Sched x B s' w` with its two
reading points parameters. On the state `w`'s tick to the clock value `t_v` starts from, the root
of its fork choice is compatible with `B`; when that root is `B` or an ancestor of `B`, some block of `w`'s voter tree
for slot `s' + 1` that is `B` or a descendant of `B` is a viable head; and the finalized block of
the state `w`'s tick to the clock value `t_u` starts from is compatible with `B`. `StepFrameAt` is the instance at
`t_v := M.voteTime S.C (s' + 1)` and `t_u := M.supportCutoff S.C (s' + 2)` (`stepFrameAt_iff`).

The variables:
- `M`: the model;
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `B`: the block; `s'`: the slot of the step; `t_v`: the clock value of the tick whose input the
  root and the voter tree are read at; `t_u`: the clock value of the tick whose input the finalized block is read at; `w`: the member.

Read aloud: `w`'s fork-choice root and viable heads read by its tick to `t_v`, and the finalized
block its tick to `t_u` reads, follow `B`'s chain. -/
def StepFrameAtTimes (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)
    (B : Block V) (s' t_v t_u : ℕ) (w : V) : Prop :=
  (M.fg_to_ac (x.tickInput w t_v)).fc_root.compatible B = true ∧
  ((M.fg_to_ac (x.tickInput w t_v)).fc_root.AncestorEq B →
    ∃ W, VoterTreeAt M (x.tickInput w t_v) (S.C.t_ ((s' + 1) - 1) + 3 * S.C.Δ) (s' + 1) W ∧
      W ∈ (M.fg_to_ac (x.tickInput w t_v)).viable_heads ∧ B.AncestorEq W) ∧
  (x.tickInput w t_u).finalized.compatible B = true

/-- `StepFrameAt` is `StepFrameAtTimes` at the vote time of slot `s' + 1` and the support cutoff
of slot `s' + 2`, by definition.

The variables:
- `M`: the model;
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `B`: the block; `s'`: the slot of the step; `w`: the member.

Read aloud: the landed condition is the general one read at the slot's two times. -/
theorem stepFrameAt_iff (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)
    (B : Block V) (s' : ℕ) (w : V) :
    StepFrameAt M S A x B s' w ↔
      StepFrameAtTimes M S A x B s' (M.voteTime S.C (s' + 1)) (M.supportCutoff S.C (s' + 2)) w :=
  Iff.rfl

/-- `ChainInvFor M S Sched x Hon 𝓒 s'`: `HonestChainExtends M S Sched x Hon C s'` for every block
`C` the predicate `𝓒` holds of.

The variables:
- `M`: the model;
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `Hon`: the validators the invariant is read at; `𝓒`: the family of blocks; `s'`: the slot.

Read aloud: at slot `s'`, the votes, the live locks and the saved confirmations of the members of
`Hon` are on the chain of every block of `𝓒` or compatible with it. -/
def ChainInvFor (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)
    (Hon : Finset V) (𝓒 : Block V → Prop) (s' : ℕ) : Prop :=
  ∀ C : Block V, 𝓒 C → HonestChainExtends M S A x Hon C s'

/-- `LiveLocksOnFamilyAt M S Sched x 𝓒 s u`: for every answer `A'` of `u`'s revocation of slot
`s + 1` at the vote time of slot `s + 1`, run on the state `u`'s own tick to that vote time starts
from (`x.tickInput u (M.voteTime S.C (s + 1))`) with its expired entries removed, the block of every
lock entry of `A'` live at that time is a block of the family `𝓒` or an ancestor of one.

The state read is the one `u`'s tick starts from, not the configuration in force at the vote time's
real time: under the two clock bounds the tick to a clock value can come before or after that real
time, and deliveries at one time have no order with the tick.

The variables:
- `M`: the model;
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `𝓒`: the family of blocks; `s`: the slot; `u`: the validator.

Read aloud: after its revocation of slot `s + 1`, every live lock of `u` is on the chain of some
block of `𝓒`. -/
def LiveLocksOnFamilyAt (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)
    (𝓒 : Block V → Prop) (s : ℕ) (u : V) : Prop :=
  ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput u (M.voteTime S.C (s + 1)))
        ((M.voteTime S.C (s + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput u (M.voteTime S.C (s + 1))) (s + 1) →
    ∀ e ∈ M.lockEntries n',
      M.is_live (x.tickInput u (M.voteTime S.C (s + 1)))
        ((M.voteTime S.C (s + 1) : ℕ) : Int) e = true →
      ∃ D : Block V, 𝓒 D ∧ e.B.AncestorEq D

/-- `VoterFrameOnChainAt M S Sched x s₀ s w`: on the state every tick of `w` to the vote time of slot `s` starts
from, for every block `B` on the honest chain of the slots before `s`, the root of `w`'s fork choice is
compatible with `B`, and, when the root is
`B` or an ancestor of `B`, some block of `w`'s voter tree of slot `s` that is `B` or a descendant
of `B` is a viable head. These are Lemma 26b's `hF2` and `hF3` and Lemma 36a's `hF2` and `hF3`,
read against the chain so far.

 a validator with no tick to the vote time is read at no state (it sends no vote). On runs at integer
times at both clock bounds `0` the tick input is the state before the vote time, `dev`'s read.



The variables:
- `M`: the model;
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `s₀`: the first slot of the chain; `s`: the slot of the vote; `w`: the voter.

It is `VoterFrameOnChainAtTime M S Sched x s₀ s (M.voteTime S.C s) w` (`voterFrameOnChainAt_iff`).

Read aloud: `w`'s finality gadget lets its vote of slot `s` follow every block of the honest chain
before `s`. -/
def VoterFrameOnChainAt (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)
    (s₀ s : ℕ) (w : V) : Prop :=
  ∀ B : Block V, OnHonestChainBefore M S A x s₀ s B →
    ∀ k : ℕ, x.lbl k = Event.tick w (M.voteTime S.C s) →
    (M.fg_to_ac (x.st k w)).fc_root.compatible B = true ∧
    ((M.fg_to_ac (x.st k w)).fc_root.AncestorEq B →
      ∃ W, VoterTreeAt M (x.st k w) (S.C.t_ (s - 1) + 3 * S.C.Δ) s W ∧
        W ∈ (M.fg_to_ac (x.st k w)).viable_heads ∧
          B.AncestorEq W)

/-- `VoterFrameOnChainAtTime M S Sched x s₀ s t w`: `VoterFrameOnChainAt M S Sched x s₀ s w` with
the time `w`'s state is read at a parameter `t`; the slot `s` stays, since the voter tree is the
slot's. On the state every tick of `w` to `t` starts from, for every block `B` on the honest chain of the slots
before `s`, the root of `w`'s fork choice is compatible with `B`, and, when the root is `B` or an
ancestor of `B`, some block of `w`'s voter tree of slot `s` that is `B` or a descendant of `B` is
a viable head. `VoterFrameOnChainAt` is the instance at `t := M.voteTime S.C s`
(`voterFrameOnChainAt_iff`).

The variables:
- `M`: the model;
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `s₀`: the first slot of the chain; `s`: the slot of the vote; `t`: the time `w`'s state is read
  at; `w`: the voter.

Read aloud: `w`'s fork-choice root and viable heads, read at its tick to `t`, follow every block of the
honest chain before `s`. -/
def VoterFrameOnChainAtTime (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (s₀ s t : ℕ) (w : V) : Prop :=
  ∀ B : Block V, OnHonestChainBefore M S A x s₀ s B →
    ∀ k : ℕ, x.lbl k = Event.tick w t →
    (M.fg_to_ac (x.st k w)).fc_root.compatible B = true ∧
    ((M.fg_to_ac (x.st k w)).fc_root.AncestorEq B →
      ∃ W, VoterTreeAt M (x.st k w) (S.C.t_ (s - 1) + 3 * S.C.Δ) s W ∧
        W ∈ (M.fg_to_ac (x.st k w)).viable_heads ∧ B.AncestorEq W)

/-- `VoterFrameOnChainAt` is `VoterFrameOnChainAtTime` at the vote time of slot `s`, by
definition.

The variables:
- `M`: the model;
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `s₀`: the first slot of the chain; `s`: the slot of the vote; `w`: the voter.

Read aloud: the landed condition is the general one read at the vote time of slot `s`. -/
theorem voterFrameOnChainAt_iff (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (s₀ s : ℕ) (w : V) :
    VoterFrameOnChainAt M S A x s₀ s w ↔ VoterFrameOnChainAtTime M S A x s₀ s (M.voteTime S.C s) w :=
  Iff.rfl

/-- `UpdaterFinalizedOnChainAt M S Sched x s₀ s v`: on the state `v`'s tick to the support cutoff
of slot `s + 1` starts from, the state its update of slot `s` reads, its finalized block is
compatible with every block on the honest chain of the slots before `s`. This is
Lemma 78's `hF`.

The variables:
- `M`: the model;
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `s₀`: the first slot of the chain; `s`: the slot the update evaluates; `v`: the updater.

It is `UpdaterFinalizedOnChainAtTime M S Sched x s₀ s (M.supportCutoff S.C (s + 1)) v`
(`updaterFinalizedOnChainAt_iff`).

Read aloud: the finalized block `v`'s update of slot `s` reads does not conflict with the honest
chain before `s`. -/
def UpdaterFinalizedOnChainAt (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (s₀ s : ℕ) (v : V) : Prop :=
  ∀ B : Block V, OnHonestChainBefore M S A x s₀ s B →
    (x.tickInput v (M.supportCutoff S.C (s + 1))).finalized.compatible B = true

/-- `UpdaterFinalizedOnChainAtTime M S Sched x s₀ s t v`: `UpdaterFinalizedOnChainAt S Sched x s₀ s
v` with the clock value of the tick whose input is read a parameter `t`. On the state `v`'s tick to
`t` starts from, its finalized block is compatible with every block on the honest chain of the slots
before `s`.
`UpdaterFinalizedOnChainAt` is the instance at `t := M.supportCutoff S.C (s + 1)`
(`updaterFinalizedOnChainAt_iff`).

The variables:
- `M`: the model;
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `s₀`: the first slot of the chain; `s`: the slot the honest chain is read before; `t`: the clock
  value of the tick whose input is read; `v`: the updater.

Read aloud: the finalized block `v`'s tick to `t` reads does not conflict with the honest chain
before `s`. -/
def UpdaterFinalizedOnChainAtTime (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (s₀ s t : ℕ) (v : V) : Prop :=
  ∀ B : Block V, OnHonestChainBefore M S A x s₀ s B →
    (x.tickInput v t).finalized.compatible B = true

/-- `UpdaterFinalizedOnChainAt` is `UpdaterFinalizedOnChainAtTime` at the support cutoff of slot
`s + 1`, by definition.

The variables:
- `M`: the model;
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `s₀`: the first slot of the chain; `s`: the slot the update evaluates; `v`: the updater.

Read aloud: the landed condition is the general one read at the support cutoff of slot `s + 1`. -/
theorem updaterFinalizedOnChainAt_iff (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (s₀ s : ℕ) (v : V) :
    UpdaterFinalizedOnChainAt M S A x s₀ s v ↔
      UpdaterFinalizedOnChainAtTime M S A x s₀ s (M.supportCutoff S.C (s + 1)) v :=
  Iff.rfl

end GoldilocksCorrectness.Record.Statements.Executions

