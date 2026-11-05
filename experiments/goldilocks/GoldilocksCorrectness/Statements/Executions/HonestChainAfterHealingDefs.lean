module
public import GoldilocksCorrectness.Statements.Executions.SleepyDefs
public import GoldilocksCorrectness.Statements.Executions.HonestChainDefs

@[expose] public section

/-!
# The honest chain after the healed slot: the definitions

The definitions the chain step `lem89s_chain_step`, Lemma 81b and Lemma 81
(`GoldilocksCorrectness/Statements/Executions/HonestChainAfterHealingStatements.lean`) read:

- `StepFrameAt S Sched x B s' w`, the frame conditions of the chain step at slot `s'` relative to
  a block `B`, at a member `w`;
- `ChainInvFor S Sched x Hon 𝓒 s'`, `HonestChainExtends` at slot `s'` for every block of a family
  `𝓒`;
- `LiveLocksOnFamilyAt S Sched x 𝓒 s u`, the lock invariant: every lock entry `u`'s revocation of
  slot `s + 1` leaves live is on a block of `𝓒` or an ancestor of one;
- `VoterFrameOnChainAt S Sched x s₀ s w` and `UpdaterFinalizedOnChainAt S Sched x s₀ s v`, the
  frame conditions of Lemma 81 relative to the honest chain of the slots before `s`;
- `StepFrameAtTimes`, `VoterFrameOnChainAtTime` and `UpdaterFinalizedOnChainAtTime`, the same
  three conditions read at times the caller names, each landed form its instance at the slot's
  times.


-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (voteTime supportCutoff)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec Schedule)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Routines (expireLocks)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- `StepFrameAt S Sched x B s' w`: the frame conditions of the chain step at slot `s'` relative
to the block `B`, at `w`. On `w`'s state before the vote time of slot `s' + 1`, the root of its
fork choice is compatible with `B`;
when that root is `B` or an ancestor of `B`, some block of `w`'s voter tree for slot `s' + 1` that
is `B` or a descendant of `B` is a viable head; and `w`'s finalized block before the support
cutoff of slot `s' + 2` is compatible with `B`. These are Lemma 79's `hF2`, `hF3` and `hFv` at one
member.



The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `B`: the block; `s'`: the slot of the step; `w`: the member.

It is `StepFrameAtTimes S Sched x B s' (voteTime S (s' + 1)) (supportCutoff S (s' + 2)) w`
(`stepFrameAt_iff`).

Read aloud: `w`'s finality gadget lets its vote of slot `s' + 1` and its update of slot `s' + 1`
follow `B`'s chain. -/
def StepFrameAt (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (B : Block V) (s' : ℕ) (w : V) : Prop :=
  (fg_to_ac (stateBefore x (voteTime S (s' + 1)) w).S).fc_root.compatible B = true ∧
  ((fg_to_ac (stateBefore x (voteTime S (s' + 1)) w).S).fc_root.AncestorEq B →
    ∀ tree : Finset (Block V),
      voter_block_tree S.C (stateBefore x (voteTime S (s' + 1)) w).A
        (fg_to_ac (stateBefore x (voteTime S (s' + 1)) w).S) (s' + 1) = .ok tree →
      ∃ W ∈ tree, W ∈ (fg_to_ac (stateBefore x (voteTime S (s' + 1)) w).S).viable_heads ∧
        B.AncestorEq W) ∧
  (stateBefore x (supportCutoff S (s' + 2)) w).S.F.compatible B = true

/-- `StepFrameAtTimes S Sched x B s' t_v t_u w`: `StepFrameAt S Sched x B s' w` with its two
reading times parameters. On `w`'s state before the time `t_v`, the root of its fork choice is
compatible with `B`; when that root is `B` or an ancestor of `B`, some block of `w`'s voter tree
for slot `s' + 1` that is `B` or a descendant of `B` is a viable head; and `w`'s finalized block
before the time `t_u` is compatible with `B`. `StepFrameAt` is the instance at
`t_v := voteTime S (s' + 1)` and `t_u := supportCutoff S (s' + 2)` (`stepFrameAt_iff`).

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `B`: the block; `s'`: the slot of the step; `t_v`: the time the root and the voter tree are read
  at; `t_u`: the time the finalized block is read at; `w`: the member.

Read aloud: `w`'s fork-choice root and viable heads read before `t_v`, and its finalized block
read before `t_u`, follow `B`'s chain. -/
def StepFrameAtTimes (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (B : Block V) (s' t_v t_u : ℕ) (w : V) : Prop :=
  (fg_to_ac (stateBefore x t_v w).S).fc_root.compatible B = true ∧
  ((fg_to_ac (stateBefore x t_v w).S).fc_root.AncestorEq B →
    ∀ tree : Finset (Block V),
      voter_block_tree S.C (stateBefore x t_v w).A (fg_to_ac (stateBefore x t_v w).S) (s' + 1) =
        .ok tree →
      ∃ W ∈ tree, W ∈ (fg_to_ac (stateBefore x t_v w).S).viable_heads ∧ B.AncestorEq W) ∧
  (stateBefore x t_u w).S.F.compatible B = true

/-- `StepFrameAt` is `StepFrameAtTimes` at the vote time of slot `s' + 1` and the support cutoff
of slot `s' + 2`, by definition.

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `B`: the block; `s'`: the slot of the step; `w`: the member.

Read aloud: the landed condition is the general one read at the slot's two times. -/
theorem stepFrameAt_iff (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (B : Block V) (s' : ℕ) (w : V) :
    StepFrameAt S Sched x B s' w ↔
      StepFrameAtTimes S Sched x B s' (voteTime S (s' + 1)) (supportCutoff S (s' + 2)) w :=
  Iff.rfl

/-- `ChainInvFor S Sched x Hon 𝓒 s'`: `HonestChainExtends S Sched x Hon C s'` for every block `C`
the predicate `𝓒` holds of.

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `Hon`: the validators the invariant is read at; `𝓒`: the family of blocks; `s'`: the slot.

Read aloud: at slot `s'`, the votes, the live locks and the saved confirmations of the members of
`Hon` are on the chain of every block of `𝓒` or compatible with it. -/
def ChainInvFor (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (Hon : Finset V) (𝓒 : Block V → Prop) (s' : ℕ) : Prop :=
  ∀ C : Block V, 𝓒 C → HonestChainExtends S Sched x Hon C s'

/-- `LiveLocksOnFamilyAt S Sched x 𝓒 s u`: for every answer `A'` of `u`'s revocation of slot
`s + 1` at the vote time of slot `s + 1`, run on `u`'s AC state then with its expired entries
removed, the block of every lock entry of `A'` live at that time is a block of the family `𝓒` or
an ancestor of one.

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `𝓒`: the family of blocks; `s`: the slot; `u`: the validator.

Read aloud: after its revocation of slot `s + 1`, every live lock of `u` is on the chain of some
block of `𝓒`. -/
def LiveLocksOnFamilyAt (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (𝓒 : Block V → Prop) (s : ℕ) (u : V) : Prop :=
  ∀ A' : ACState V,
    revoke_locks S.P (expireLocks (stateBefore x (voteTime S (s + 1)) u).A
      ((voteTime S (s + 1) : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S (s + 1)) u).S)
      ((voteTime S (s + 1) : ℕ) : Int) (s + 1) = .ok A' →
    ∀ e ∈ A'.lock_entries,
      is_live (fg_to_ac (stateBefore x (voteTime S (s + 1)) u).S)
        ((voteTime S (s + 1) : ℕ) : Int) e = true →
      ∃ D : Block V, 𝓒 D ∧ e.B.AncestorEq D

/-- `VoterFrameOnChainAt S Sched x s₀ s w`: on `w`'s state before the vote time of slot `s`, for
every block `B` on the honest chain of the slots before `s`, the root of `w`'s fork choice is
compatible with `B`, and, when the root is
`B` or an ancestor of `B`, some block of `w`'s voter tree of slot `s` that is `B` or a descendant
of `B` is a viable head. These are Lemma 26b's `hF2` and `hF3` and Lemma 36a's `hF2` and `hF3`,
read against the chain so far.



The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `s₀`: the first slot of the chain; `s`: the slot of the vote; `w`: the voter.

It is `VoterFrameOnChainAtTime S Sched x s₀ s (voteTime S s) w` (`voterFrameOnChainAt_iff`).

Read aloud: `w`'s finality gadget lets its vote of slot `s` follow every block of the honest chain
before `s`. -/
def VoterFrameOnChainAt (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (s₀ s : ℕ) (w : V) : Prop :=
  ∀ B : Block V, OnHonestChainBefore S Sched x s₀ s B →
    (fg_to_ac (stateBefore x (voteTime S s) w).S).fc_root.compatible B = true ∧
    ((fg_to_ac (stateBefore x (voteTime S s) w).S).fc_root.AncestorEq B →
      ∀ tree : Finset (Block V),
        voter_block_tree S.C (stateBefore x (voteTime S s) w).A
          (fg_to_ac (stateBefore x (voteTime S s) w).S) s = .ok tree →
        ∃ W ∈ tree, W ∈ (fg_to_ac (stateBefore x (voteTime S s) w).S).viable_heads ∧
          B.AncestorEq W)

/-- `VoterFrameOnChainAtTime S Sched x s₀ s t w`: `VoterFrameOnChainAt S Sched x s₀ s w` with the
time `w`'s state is read at a parameter `t`; the slot `s` stays, since the voter tree is the
slot's. On `w`'s state before the time `t`, for every block `B` on the honest chain of the slots
before `s`, the root of `w`'s fork choice is compatible with `B`, and, when the root is `B` or an
ancestor of `B`, some block of `w`'s voter tree of slot `s` that is `B` or a descendant of `B` is
a viable head. `VoterFrameOnChainAt` is the instance at `t := voteTime S s`
(`voterFrameOnChainAt_iff`).

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `s₀`: the first slot of the chain; `s`: the slot of the vote; `t`: the time `w`'s state is read
  at; `w`: the voter.

Read aloud: `w`'s fork-choice root and viable heads, read before `t`, follow every block of the
honest chain before `s`. -/
def VoterFrameOnChainAtTime (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ s t : ℕ) (w : V) : Prop :=
  ∀ B : Block V, OnHonestChainBefore S Sched x s₀ s B →
    (fg_to_ac (stateBefore x t w).S).fc_root.compatible B = true ∧
    ((fg_to_ac (stateBefore x t w).S).fc_root.AncestorEq B →
      ∀ tree : Finset (Block V),
        voter_block_tree S.C (stateBefore x t w).A (fg_to_ac (stateBefore x t w).S) s = .ok tree →
        ∃ W ∈ tree, W ∈ (fg_to_ac (stateBefore x t w).S).viable_heads ∧ B.AncestorEq W)

/-- `VoterFrameOnChainAt` is `VoterFrameOnChainAtTime` at the vote time of slot `s`, by
definition.

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `s₀`: the first slot of the chain; `s`: the slot of the vote; `w`: the voter.

Read aloud: the landed condition is the general one read at the vote time of slot `s`. -/
theorem voterFrameOnChainAt_iff (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ s : ℕ) (w : V) :
    VoterFrameOnChainAt S Sched x s₀ s w ↔ VoterFrameOnChainAtTime S Sched x s₀ s (voteTime S s) w :=
  Iff.rfl

/-- `UpdaterFinalizedOnChainAt S Sched x s₀ s v`: on `v`'s state before the support cutoff of
slot `s + 1`, where its update of slot `s` runs, its finalized block is compatible with every
block on the honest chain of the slots before `s`. This is Lemma 78's `hF`.

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `s₀`: the first slot of the chain; `s`: the slot the update evaluates; `v`: the updater.

It is `UpdaterFinalizedOnChainAtTime S Sched x s₀ s (supportCutoff S (s + 1)) v`
(`updaterFinalizedOnChainAt_iff`).

Read aloud: `v`'s finalized block does not conflict with the honest chain before `s` when it
updates its confirmation of slot `s`. -/
def UpdaterFinalizedOnChainAt (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ s : ℕ) (v : V) : Prop :=
  ∀ B : Block V, OnHonestChainBefore S Sched x s₀ s B →
    (stateBefore x (supportCutoff S (s + 1)) v).S.F.compatible B = true

/-- `UpdaterFinalizedOnChainAtTime S Sched x s₀ s t v`: `UpdaterFinalizedOnChainAt S Sched x s₀ s
v` with the time `v`'s state is read at a parameter `t`. On `v`'s state before the time `t`, its
finalized block is compatible with every block on the honest chain of the slots before `s`.
`UpdaterFinalizedOnChainAt` is the instance at `t := supportCutoff S (s + 1)`
(`updaterFinalizedOnChainAt_iff`).

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `s₀`: the first slot of the chain; `s`: the slot the honest chain is read before; `t`: the time
  `v`'s state is read at; `v`: the updater.

Read aloud: `v`'s finalized block, read before `t`, does not conflict with the honest chain before
`s`. -/
def UpdaterFinalizedOnChainAtTime (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ s t : ℕ) (v : V) : Prop :=
  ∀ B : Block V, OnHonestChainBefore S Sched x s₀ s B →
    (stateBefore x t v).S.F.compatible B = true

/-- `UpdaterFinalizedOnChainAt` is `UpdaterFinalizedOnChainAtTime` at the support cutoff of slot
`s + 1`, by definition.

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `s₀`: the first slot of the chain; `s`: the slot the update evaluates; `v`: the updater.

Read aloud: the landed condition is the general one read at the support cutoff of slot `s + 1`. -/
theorem updaterFinalizedOnChainAt_iff (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ s : ℕ) (v : V) :
    UpdaterFinalizedOnChainAt S Sched x s₀ s v ↔
      UpdaterFinalizedOnChainAtTime S Sched x s₀ s (supportCutoff S (s + 1)) v :=
  Iff.rfl

end GoldilocksCorrectness.Statements.Executions
