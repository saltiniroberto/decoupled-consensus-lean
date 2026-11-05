module
public import GoldilocksCorrectness.Statements.Executions.AccountableDefs
public import GoldilocksCorrectness.Proofs.Executions.Monotone
public import GoldilocksCorrectness.Proofs.Routines.FGState
public import GoldilocksCorrectness.Proofs.Routines.Node
public import GoldilocksCorrectness.Proofs.Routines.Wiring

@[expose] public section

/-!
# The finalized block is the finalized block of a held chain

At every step of every execution, every validator's finalized block `n.S.F` is the finalized
block of the chain state `chainStateOf C B` of a block `B` of its tree (`FinalizedFromChain`).
The proof carries the relation `FinalizedFrom C n n'` (`n'` holds `n`'s tree, and its finalized
block is `n`'s or the finalized block of the chain state of a block of `n'`'s tree) through every
routine that writes the tree or the finalized block, then through each step of the wiring
`GoldilocksCorrectness.Wiring.protocol` on one event, then through each step of the sts
framework's atomic semantics, and along an execution by induction on the step.

The one routine that moves the finalized block is the finality update, which writes the
finalized block of the chain state it reads; accepting a block runs it on the chain state the
node computed for the block, which is the block's own (`ChainStatesComputed`, a clause of
Lemma 11) because the block's parent is in the tree.

No honesty hypothesis is needed: the atomic semantics changes an adversarial validator's state at
no step.
-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Proofs.Routines (DREBPost DREBPost.bind DREBPost.bind_any DREBPost.dite
  DREBPost.ite DREBPost.of_outcome DREBPost.pure)
open GoldilocksCorrectness.Statements.Routines (chainStateOf)

open GoldilocksCorrectness.Proofs.Routines (fg_on_attestation_keeps fg_on_block_F_cases
  fg_on_block_eq)
open GoldilocksCorrectness.Statements.Routines (ChainStatesComputed FinalizedFromChain)

open GoldilocksCorrectness.Proofs.Routines (FinalizedFrom finalizedFrom_of_frame finalizedFrom_refl
  finalizedFrom_trans initial_finalizedFromChain on_attestation_frame_S on_block_finalizedFrom
  tick_finalizedFrom)

open GoldilocksCorrectness.Proofs.Routines (wake_eq)

open GoldilocksCorrectness.Proofs.Routines (receive_finalizedFrom)

namespace GoldilocksCorrectness.Proofs.Executions

open Goldilocks
open GoldilocksCorrectness.Statements.Executions

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-! ## The relation -/

section Relation

omit [RootOrder] in
/-- `FinalizedFrom` carries `FinalizedFromChain` from the first node state's FG state to the
second's.

The variables:
- `C`: the parameters; `n`, `n'`: the two node states. -/
theorem finalizedFromChain_of_finalizedFrom (C : Config) {n n' : NodeState V}
    (h : FinalizedFromChain C n.S) (hr : FinalizedFrom C n n') : FinalizedFromChain C n'.S := by
  obtain ⟨B, hB, hBF⟩ := h
  obtain ⟨hT, hF⟩ := hr
  rcases hF with hF | ⟨B', hB', hBF'⟩
  · exact ⟨B, hT hB, hF.trans hBF⟩
  · exact ⟨B', hB', hBF'⟩

end Relation

/-! ## The FG routines -/

section FG

end FG

/-! ## The node -/

section Node

end Node

/-! ## The reactions and the steps -/

section Execution

open Framework.StsMultisetLog (AtomicAction AtomicExec AtomicStep Event Schedule
  TickAllAwakeWake tickAllAwakeUpdate_getElem_react tickAllAwakeUpdate_getElem_st_of_not_react
  applyNodeStepResult_getElem receive_getElem NodeStepResult View)
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol step_tick_iff step_wake_iff step_recv_iff)

/-- Every step of the wiring on one event, from a node state whose chain states of its tree are
the blocks' own, relates the node state to the step's state: a tick step is an answer of the
node's tick or keeps the state, a delivery runs the dispatch, a wake writes `awakeSince` only.

The variables:
- `S`: the setup; `p`: the validator; `r`: the reading; `view`: its view; `n`: the node state;
  `e`: the event; `res`: the step result. -/
theorem reaction_finalizedFrom (S : Setup V) (p : V) (r : ℕ) (view : View V (NamedObject V))
    (n : NodeState V) (e : Event V (NamedObject V) Empty)
    (res : NodeStepResult (NodeState V) (NamedObject V))
    (hstep : (protocol S).step p r view n e res)
    -- the chain states of `n`'s tree are the blocks' own
    (hCS : ChainStatesComputed S.C n.S) :
    FinalizedFrom S.C n res.state := by
  cases e with
  | tick =>
      rcases (step_tick_iff S p r view n res).1 hstep with ⟨n', sent, hok, rfl⟩ | ⟨-, rfl⟩
      · exact DREBPost.of_outcome (tick_finalizedFrom S.C S.P S.X n (r : Int) hCS) hok
      · exact finalizedFrom_refl S.C _
  | recv m =>
      rw [(step_recv_iff S p r view n m res).1 hstep]
      exact receive_finalizedFrom S.C S.P S.X n m.msg hCS
  | wake =>
      rw [(step_wake_iff S p r view n res).1 hstep, wake_eq]
      exact finalizedFrom_of_frame S.C rfl rfl
  | custom ev => exact ev.elim

/-- Every step of the atomic semantics relates every validator's node state before the step to
its node state after, given that the chain states of its tree before are the blocks' own. At the
tick of every awake validator, a validator that reacts runs its wake reaction (when it enters the
awake set) and its tick reaction; a validator that does not react keeps its state. At a delivery,
the receiver runs its reaction to the delivered message. No other action changes a state.

The variables:
- `S`: the setup; `Sched`: the schedule; `a`: the action; `c`, `c'`: the configurations before
  and after; `v`: the validator.

Read aloud: across any step, a validator keeps its tree, and its finalized block is kept or
becomes the finalized block of the chain state of a block of its tree. -/
theorem atomicStep_finalizedFrom {S : Setup V} {Sched : Schedule V}
    {a : AtomicAction V (NamedObject V) Empty}
    {c c' : Framework.StsMultisetLog.Config V (NamedObject V) (NodeState V)}
    (h : AtomicStep (protocol S) Sched a c c') (v : V)
    -- the chain states of `v`'s tree before the step are the blocks' own
    (hCS : ChainStatesComputed S.C c[v].st.S) :
    FinalizedFrom S.C c[v].st c'[v].st := by
  refine AtomicStep.elim (motive := fun _ d d' =>
      ChainStatesComputed S.C d[v].st.S → FinalizedFrom S.C d[v].st d'[v].st) h ?_ ?_ ?_ ?_ ?_
      hCS
  · intro d t w tk _ hw htk hCS'
    by_cases hv : v ∈ Sched.awake (t : Int) \ Sched.adv (t : Int)
    · rw [tickAllAwakeUpdate_getElem_react hv]
      -- the wake stage keeps the FG state
      have hwv : FinalizedFrom S.C d[v].st (w v).state ∧ (w v).state.S = d[v].st.S := by
        have hw' := hw v
        unfold TickAllAwakeWake at hw'
        split at hw'
        · rw [(step_wake_iff S _ _ _ _ _).1 hw', wake_eq]
          exact ⟨finalizedFrom_of_frame S.C rfl rfl, rfl⟩
        · rw [hw']
          exact ⟨finalizedFrom_refl S.C _, rfl⟩
      show FinalizedFrom S.C d[v].st (tk v).state
      exact finalizedFrom_trans S.C hwv.1
        (reaction_finalizedFrom S _ _ _ _ _ _ (htk v hv) (by rw [hwv.2]; exact hCS'))
    · rw [tickAllAwakeUpdate_getElem_st_of_not_react hv]
      exact finalizedFrom_refl S.C _
  · intro d p m res _ hres hCS'
    rw [applyNodeStepResult_getElem]
    split
    · rename_i hp
      subst hp
      have hst : (Framework.StsMultisetLog.receive p m d)[p].st = d[p].st := by
        rw [receive_getElem, if_pos rfl]
      show FinalizedFrom S.C d[p].st res.state
      rw [hst] at hres
      exact reaction_finalizedFrom S _ _ _ _ _ _ hres hCS'
    · rw [receive_getElem, if_neg (by assumption)]
      exact finalizedFrom_refl S.C _
  · intro d p ev
    exact ev.elim
  · intro d p m _ _
    exact finalizedFrom_refl S.C _
  · intro d p m _ _
    exact finalizedFrom_refl S.C _

/-- At every step of every execution, every validator's finalized block is the finalized block
of the chain state of a block of its tree. By induction on the step: the initial node state
satisfies it, and every step relates the node state before to the node state after, the chain
states of the tree before being the blocks' own (Lemma 11).

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution; `i`: the step; `v`: the
  validator. -/
theorem finalizedFromChain_of_exec (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (i : ℕ) (v : V) :
    FinalizedFromChain S.C (x[i][v].st).S := by
  induction i with
  | zero =>
      obtain ⟨-, hn, -⟩ := x.init
      show FinalizedFromChain S.C ((x.cfg 0)[v].st).S
      rw [hn v]
      exact initial_finalizedFromChain S.C v
  | succ i ih =>
      exact finalizedFromChain_of_finalizedFrom S.C ih (atomicStep_finalizedFrom (x.step i) v
        (lem11_node_invariant S Sched x i v).1.2.2.2.2.2.1)

end Execution

end GoldilocksCorrectness.Proofs.Executions
