module
public import GoldilocksCorrectness.Proofs.Routines.HeightCacheAttained
public import GoldilocksCorrectness.Proofs.Executions.Invariants

@[expose] public section

/-!
# The cache `h_max` is the greatest chain-state height of the tree

At every step of every execution, every validator's cache `h_max` is the chain-state height of a
block of its tree (`heightCacheAttained_of_exec`), and so, with the bound of Lemma 11
(`HeightCacheBounds`) and the chain states of Lemma 11 (`ChainStatesComputed`), the greatest
chain-state height `(chainStateOf C B).h` over the blocks `B` of its tree
(`h_max_eq_sup_of_exec`).

The proof carries `HeightCacheAttained` of the FG state through each step of the wiring
`GoldilocksCorrectness.Wiring.protocol` on one event (`reaction_heightCacheAttained`), then
through each step of the sts framework's atomic semantics (`atomicStep_heightCacheAttained`), and
along an execution by induction on the step, from the routine lemmas of
`Proofs/Routines/HeightCacheAttained.lean`. No honesty hypothesis is needed: the atomic semantics
changes an adversarial validator's state at no step.

Added for the record migration, step L1.
-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Proofs.Routines (DREBPost.of_outcome)
open GoldilocksCorrectness.Statements.Routines (chainStateOf)
open GoldilocksCorrectness.Statements.Routines (ChainStatesComputed HeightCacheAttained
  HeightCacheBounds)
open GoldilocksCorrectness.Proofs.Routines (initial_heightCacheAttained
  receive_heightCacheAttained tick_heightCacheAttained wake_heightCacheAttained)

namespace GoldilocksCorrectness.Proofs.Executions

open Goldilocks
open GoldilocksCorrectness.Statements.Executions

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

section Execution

open Framework.StsMultisetLog (AtomicAction AtomicExec AtomicStep Event Schedule
  TickAllAwakeWake tickAllAwakeUpdate_getElem_react tickAllAwakeUpdate_getElem_st_of_not_react
  applyNodeStepResult_getElem receive_getElem NodeStepResult View)
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol step_tick_iff step_wake_iff step_recv_iff)

/-- Every step of the wiring on one event keeps `HeightCacheAttained` of the FG state: a tick step
is an answer of the node's tick or keeps the state, a delivery runs the dispatch, a wake writes
`awakeSince` only.

The variables:
- `S`: the setup; `p`: the validator; `r`: the reading; `view`: its view; `n`: the node state;
  `e`: the event; `res`: the step result.

Read aloud: a step of a validator on any event keeps its cache `h_max` the chain-state height of
some block of its tree. -/
theorem reaction_heightCacheAttained (S : Setup V) (p : V) (r : ℕ)
    (view : View V (NamedObject V)) (n : NodeState V) (e : Event V (NamedObject V) Empty)
    (res : NodeStepResult (NodeState V) (NamedObject V))
    (hstep : (protocol S).step p r view n e res)
    -- some block of `n`'s tree has the chain-state height `n.S.h_max`
    (h : HeightCacheAttained n.S) :
    HeightCacheAttained res.state.S := by
  cases e with
  | tick =>
      rcases (step_tick_iff S p r view n res).1 hstep with ⟨n', sent, hok, rfl⟩ | ⟨-, rfl⟩
      · exact DREBPost.of_outcome (tick_heightCacheAttained S.C S.P S.X n (r : Int) h) hok
      · exact h
  | recv m =>
      rw [(step_recv_iff S p r view n m res).1 hstep]
      exact receive_heightCacheAttained S.C S.P S.X n m.msg h
  | wake =>
      rw [(step_wake_iff S p r view n res).1 hstep]
      exact wake_heightCacheAttained n (r : Int) h
  | custom ev => exact ev.elim

/-- Every step of the atomic semantics keeps, for each validator `v`, `HeightCacheAttained` of
the FG state of its node state. At the tick of every awake validator, a validator that reacts runs
its wake reaction (when it enters the awake set) and its tick reaction; a validator that does not
react keeps its state. At a delivery, the receiver runs its reaction to the delivered message. No
other action changes a state.

The variables:
- `S`: the setup; `Sched`: the schedule; `a`: the action; `c`, `c'`: the configurations before
  and after; `v`: the validator.

Read aloud: across any step, a validator's cache `h_max` stays the chain-state height of some
block of its tree. -/
theorem atomicStep_heightCacheAttained {S : Setup V} {Sched : Schedule V}
    {a : AtomicAction V (NamedObject V) Empty}
    {c c' : Framework.StsMultisetLog.Config V (NamedObject V) (NodeState V)}
    (hstep : AtomicStep (protocol S) Sched a c c') (v : V)
    -- some block of `v`'s tree before the step has the chain-state height of its cache `h_max`
    (h : HeightCacheAttained c[v].st.S) :
    HeightCacheAttained c'[v].st.S := by
  refine AtomicStep.elim (motive := fun _ d d' =>
      HeightCacheAttained d[v].st.S → HeightCacheAttained d'[v].st.S) hstep ?_ ?_ ?_ ?_ ?_ h
  · intro d t w tk _ hw htk h'
    by_cases hv : v ∈ Sched.awake (t : Int) \ Sched.adv (t : Int)
    · rw [tickAllAwakeUpdate_getElem_react hv]
      -- the wake stage keeps `HeightCacheAttained` of the FG state
      have hwv : HeightCacheAttained (w v).state.S := by
        have hw' := hw v
        unfold TickAllAwakeWake at hw'
        split at hw'
        · rw [(step_wake_iff S _ _ _ _ _).1 hw']
          exact wake_heightCacheAttained _ _ h'
        · rw [hw']
          exact h'
      exact reaction_heightCacheAttained S _ _ _ _ _ _ (htk v hv) hwv
    · rw [tickAllAwakeUpdate_getElem_st_of_not_react hv]
      exact h'
  · intro d p m res _ hres h'
    rw [applyNodeStepResult_getElem]
    split
    · rename_i hp
      subst hp
      have hst : (Framework.StsMultisetLog.receive p m d)[p].st = d[p].st := by
        rw [receive_getElem, if_pos rfl]
      show HeightCacheAttained res.state.S
      rw [hst] at hres
      exact reaction_heightCacheAttained S _ _ _ _ _ _ hres h'
    · rw [receive_getElem, if_neg (by assumption)]
      exact h'
  · intro d p ev
    exact ev.elim
  · intro d p m _ h'
    exact h'
  · intro d p m _ h'
    exact h'

/-- At every step of every execution, every validator's cache `h_max` is the chain-state height
of a block of its tree. By induction on the step: the initial node state satisfies it
(`initial_heightCacheAttained`), and every step keeps it (`atomicStep_heightCacheAttained`).

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution; `i`: the step; `v`: the
  validator.

Read aloud: at every step of every execution, some block of a validator's tree has the
chain-state height its cache `h_max` holds. -/
theorem heightCacheAttained_of_exec (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (i : ℕ) (v : V) :
    HeightCacheAttained (x[i][v].st).S := by
  induction i with
  | zero =>
      obtain ⟨-, hn, -⟩ := x.init
      show HeightCacheAttained ((x.cfg 0)[v].st).S
      rw [hn v]
      exact initial_heightCacheAttained S.C v
  | succ i ih => exact atomicStep_heightCacheAttained (x.step i) v ih

/-- At every step of every execution, every validator's cache `h_max` is the greatest
chain-state height `(chainStateOf S.C B).h` over the blocks `B` of its tree. The cache is the
chain-state height of a block of the tree (`heightCacheAttained_of_exec`), so it is at most the
greatest; it is at least the chain-state height of every block of the tree (`HeightCacheBounds`,
Lemma 11), so it is at least the greatest; and the chain state the node holds for a block of its
tree is the block's own (`ChainStatesComputed`, Lemma 11).

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution; `i`: the step; `v`: the
  validator.

Read aloud: at every step of every execution, a validator's stored greatest height is the
greatest chain-state height of its tree. -/
theorem h_max_eq_sup_of_exec (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (i : ℕ) (v : V) :
    (x[i][v].st).S.h_max = ((x[i][v].st).S.T).sup (fun B => (chainStateOf S.C B).h) := by
  obtain ⟨⟨-, -, -, -, -, hCS, -, -, -, ⟨-, ⟨-, hHC⟩, -⟩, -⟩, -, -⟩ :=
    lem11_node_invariant S Sched x i v
  obtain ⟨B, hB, hBh⟩ := heightCacheAttained_of_exec S Sched x i v
  refine le_antisymm ?_ (Finset.sup_le fun B' hB' => ?_)
  · rw [← hBh, hCS B hB]
    exact Finset.le_sup (f := fun B => (chainStateOf S.C B).h) hB
  · rw [← hCS B' hB']
    exact hHC B' hB'

end Execution

end GoldilocksCorrectness.Proofs.Executions
