module
public import GoldilocksCorrectness.Statements.Executions.HeightInvariantDefs
public import GoldilocksCorrectness.Statements.Executions.ChainStateStatements
public import GoldilocksCorrectness.Statements.Routines.FrameDefs
public import GoldilocksCorrectness.Proofs.Executions.Monotone
public import GoldilocksCorrectness.Proofs.Routines.FGState
public import GoldilocksCorrectness.Proofs.Routines.Node
public import GoldilocksCorrectness.Proofs.Routines.Wiring

@[expose] public section

/-!
# Lemma 57b: the justified block entered its height

The proofs of `lem57b_justified_is_entry`, its `stateBefore` form and the bridge
`entry_block_of_boxTwo`, stated in
`GoldilocksCorrectness/Statements/Executions/HeightInvariantStatements.lean`.

The route: a chain state's justified block is the genesis block or its own chain state's `T_h`
(`chainStateOf_J_entry`, from Lemma 47 (f) and `chainStateOf_T_h_T_h`). The only writer of a
node's justified block is the finality update, which writes the justified block of the chain
state it reads; accepting a block runs it on the chain state the node computed for the block, so
the written block is the justified block of some `chainStateOf C D`. So the relation
`JustifiedFrom C n n'` (`n'`'s justified block is `n`'s, or the justified block of some chain
state `chainStateOf C D`) is carried through every routine, reaction and step, as
`Proofs/Executions/FinalizedFromChain.lean` carries `FinalizedFrom`, and the statement over
`chainStateOf` (`JustifiedIsEntryChain`) holds along an execution by induction on the step. The
FG state's own chain state of its justified block is `chainStateOf` of it, by Lemma 11's
`ChainStatesComputed` and Lemma 57's `JustifiedInTree`.

No honesty hypothesis is needed: the atomic semantics changes an adversarial validator's state at
no step.
-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Proofs.Routines (DREBPost DREBPost.bind DREBPost.bind_any DREBPost.dite
  DREBPost.ite DREBPost.of_outcome DREBPost.pure chainStateOf_J_spec chainStateOf_T_h
  chainStateOf_height forIn_yield_inv)
open GoldilocksCorrectness.Statements.Routines (chainStateOf)

open GoldilocksCorrectness.Proofs.Routines (fg_on_attestation_J fg_on_block_J_cases)
open GoldilocksCorrectness.Statements.Routines (ChainStatesComputed)

open GoldilocksCorrectness.Proofs.Routines (JustifiedFrom justifiedFrom_of_frame justifiedFrom_refl
  justifiedFrom_trans on_attestation_J on_block_justifiedFrom tick_justifiedFrom)

open GoldilocksCorrectness.Proofs.Routines (chainStateOf_genesis_T_h fgState_initial_eq initial_eq
  wake_eq)

open GoldilocksCorrectness.Proofs.Routines (receive_justifiedFrom)

namespace GoldilocksCorrectness.Proofs.Executions

open Goldilocks
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (BoxTwo)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-! ## The chain states -/

section ChainStates

omit [RootOrder] in
/-- A block's `T_h` is its own `T_h`: the block that took a chain into its height took its own
chain there.

The variables:
- `C`: the parameters; `D`: the block. -/
theorem chainStateOf_T_h_T_h (C : Config) (D : Block V) :
    (chainStateOf C (chainStateOf C D).T_h).T_h = (chainStateOf C D).T_h := by
  induction D with
  | genesis => simp only [chainStateOf_genesis_T_h]
  | node p s r votes support ats v ih =>
      have hne : (Block.node p s r votes support ats v) ≠ Block.genesis := by intro h; cases h
      have h2 := chainStateOf_height C _ hne
      have h3 := chainStateOf_T_h C _ hne
      change _ = (chainStateOf C p).h ∨ _ = (chainStateOf C p).h + 1 at h2
      change (_ = (chainStateOf C p).h → _ = (chainStateOf C p).T_h) ∧ _ at h3
      rcases h2 with h2 | h2
      · rw [h3.1 h2]
        exact ih
      · rw [h3.2 h2]
        exact h3.2 h2

/-- `JustifiedIsEntryChain C J`: the block `J` is the genesis block, or the `T_h` of its chain
state `chainStateOf C J` is `J` itself.

The variables:
- `C`: the parameters; `J`: the block. -/
def JustifiedIsEntryChain (C : Config) (J : Block V) : Prop :=
  J = Block.genesis ∨ (chainStateOf C J).T_h = J

omit [RootOrder] in
/-- A chain state's justified block is the genesis block or the block that took its own chain
into its height.

Why: at the justification height `0` the justified block is the genesis block
(`chainStateOf_J_spec`); otherwise it is the `T_h` of an ancestor-or-self (Lemma 47 (f)), and a
`T_h` is its own `T_h` (`chainStateOf_T_h_T_h`).

The variables:
- `C`: the parameters; `D`: the block whose justified block is read. -/
theorem chainStateOf_J_entry (C : Config) (D : Block V) :
    JustifiedIsEntryChain C (chainStateOf C D).J := by
  by_cases hj : (chainStateOf C D).h_j = 0
  · exact Or.inl ((chainStateOf_J_spec C D).2.1 hj)
  · obtain ⟨Y, -, -, hYT⟩ := GoldilocksCorrectness.Statements.Routines.lem47f_justified_is_entry
      C D _ rfl (Nat.one_le_iff_ne_zero.mpr hj)
    refine Or.inr ?_
    rw [← hYT]
    exact chainStateOf_T_h_T_h C Y

end ChainStates

/-! ## The relation -/

section Relation

omit [RootOrder] in
/-- `JustifiedFrom` carries `JustifiedIsEntryChain` of the justified block from the first node
state to the second.

The variables:
- `C`: the parameters; `n`, `n'`: the two node states. -/
theorem justifiedIsEntryChain_of_justifiedFrom (C : Config) {n n' : NodeState V}
    (h : JustifiedIsEntryChain C n.S.J) (hr : JustifiedFrom C n n') :
    JustifiedIsEntryChain C n'.S.J := by
  rcases hr with hr | ⟨D, hD⟩
  · rw [hr]
    exact h
  · rw [hD]
    exact chainStateOf_J_entry C D

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
theorem reaction_justifiedFrom (S : Setup V) (p : V) (r : ℕ) (view : View V (NamedObject V))
    (n : NodeState V) (e : Event V (NamedObject V) Empty)
    (res : NodeStepResult (NodeState V) (NamedObject V))
    (hstep : (protocol S).step p r view n e res)
    -- the chain states of `n`'s tree are the blocks' own
    (hCS : ChainStatesComputed S.C n.S) :
    JustifiedFrom S.C n res.state := by
  cases e with
  | tick =>
      rcases (step_tick_iff S p r view n res).1 hstep with ⟨n', sent, hok, rfl⟩ | ⟨-, rfl⟩
      · exact DREBPost.of_outcome (tick_justifiedFrom S.C S.P S.X n (r : Int) hCS) hok
      · exact justifiedFrom_refl S.C _
  | recv m =>
      rw [(step_recv_iff S p r view n m res).1 hstep]
      exact receive_justifiedFrom S.C S.P S.X n m.msg hCS
  | wake =>
      rw [(step_wake_iff S p r view n res).1 hstep, wake_eq]
      exact justifiedFrom_of_frame S.C rfl
  | custom ev => exact ev.elim

/-- Every step of the atomic semantics relates every validator's node state before the step to
its node state after, given that the chain states of its tree before are the blocks' own. At the
tick of every awake validator, a validator that reacts runs its wake reaction (when it enters the
awake set) and its tick reaction; a validator that does not react keeps its state. At a delivery,
the receiver runs its reaction to the delivered message. No other action changes a state.

The variables:
- `S`: the setup; `Sched`: the schedule; `a`: the action; `c`, `c'`: the configurations before
  and after; `v`: the validator. -/
theorem atomicStep_justifiedFrom {S : Setup V} {Sched : Schedule V}
    {a : AtomicAction V (NamedObject V) Empty}
    {c c' : Framework.StsMultisetLog.Config V (NamedObject V) (NodeState V)}
    (h : AtomicStep (protocol S) Sched a c c') (v : V)
    -- the chain states of `v`'s tree before the step are the blocks' own
    (hCS : ChainStatesComputed S.C c[v].st.S) :
    JustifiedFrom S.C c[v].st c'[v].st := by
  refine AtomicStep.elim (motive := fun _ d d' =>
      ChainStatesComputed S.C d[v].st.S → JustifiedFrom S.C d[v].st d'[v].st) h ?_ ?_ ?_ ?_ ?_
      hCS
  · intro d t w tk _ hw htk hCS'
    by_cases hv : v ∈ Sched.awake (t : Int) \ Sched.adv (t : Int)
    · rw [tickAllAwakeUpdate_getElem_react hv]
      -- the wake stage keeps the FG state
      have hwv : JustifiedFrom S.C d[v].st (w v).state ∧ (w v).state.S = d[v].st.S := by
        have hw' := hw v
        unfold TickAllAwakeWake at hw'
        split at hw'
        · rw [(step_wake_iff S _ _ _ _ _).1 hw', wake_eq]
          exact ⟨justifiedFrom_of_frame S.C rfl, rfl⟩
        · rw [hw']
          exact ⟨justifiedFrom_refl S.C _, rfl⟩
      show JustifiedFrom S.C d[v].st (tk v).state
      exact justifiedFrom_trans S.C hwv.1
        (reaction_justifiedFrom S _ _ _ _ _ _ (htk v hv) (by rw [hwv.2]; exact hCS'))
    · rw [tickAllAwakeUpdate_getElem_st_of_not_react hv]
      exact justifiedFrom_refl S.C _
  · intro d p m res _ hres hCS'
    rw [applyNodeStepResult_getElem]
    split
    · rename_i hp
      subst hp
      have hst : (Framework.StsMultisetLog.receive p m d)[p].st = d[p].st := by
        rw [receive_getElem, if_pos rfl]
      show JustifiedFrom S.C d[p].st res.state
      rw [hst] at hres
      exact reaction_justifiedFrom S _ _ _ _ _ _ hres hCS'
    · rw [receive_getElem, if_neg (by assumption)]
      exact justifiedFrom_refl S.C _
  · intro d p ev
    exact ev.elim
  · intro d p m _ _
    exact justifiedFrom_refl S.C _
  · intro d p m _ _
    exact justifiedFrom_refl S.C _

/-- At every step of every execution, every validator's justified block is the genesis block or
the `T_h` of its own chain state `chainStateOf`. By induction on the step: the initial node
state's justified block is the genesis block, and every step relates the node state before to the
node state after, the chain states of the tree before being the blocks' own (Lemma 11).

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution; `i`: the step; `v`: the
  validator. -/
theorem justifiedIsEntryChain_of_exec (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (i : ℕ) (v : V) :
    JustifiedIsEntryChain S.C (x[i][v].st).S.J := by
  induction i with
  | zero =>
      obtain ⟨-, hn, -⟩ := x.init
      show JustifiedIsEntryChain S.C ((x.cfg 0)[v].st).S.J
      rw [hn v, show (protocol S).init v = initial S.C v from rfl, initial_eq, fgState_initial_eq]
      exact Or.inl rfl
  | succ i ih =>
      exact justifiedIsEntryChain_of_justifiedFrom S.C ih (atomicStep_justifiedFrom (x.step i) v
        (lem11_node_invariant S Sched x i v).1.2.2.2.2.2.1)

/-- **Lemma 57b, the justified block entered its height.** The proof; the audited statement is in
`Statements/Executions/HeightInvariantStatements.lean`.

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution; `i`: the step; `v`: the
  validator. -/
theorem lem57b_justified_is_entry (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (i : ℕ) (v : V) :
    JustifiedIsEntry (x[i][v].st).S := by
  have hCS := (lem11_node_invariant S Sched x i v).1.2.2.2.2.2.1
  have hJT := (lem57_justification_cache_and_record S Sched x i v).2.2.1
  unfold JustifiedIsEntry
  rw [hCS _ hJT]
  exact justifiedIsEntryChain_of_exec S Sched x i v

/-- The bridge for box 2. The proof; the audited statement is in
`Statements/Executions/HeightInvariantStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `v`: the validator;
- `B`: the block on `J₀`'s chain; `J₀`: the justified block. -/
theorem entry_block_of_boxTwo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (t : ℕ) (v : V) (B J₀ : Block V)
    (hBox : BoxTwo (stateBefore x t v).S J₀)
    (hJ₀ : J₀ ≠ Block.genesis)
    (hJB : J₀.AncestorEq B)
    (hH : (chainStateOf S.C B).h = (stateBefore x t v).S.h_max - 1) :
    (chainStateOf S.C B).T_h = J₀ := by
  obtain ⟨hmax, -, hJ⟩ := hBox
  have hCS := (lem11_node_invariant S Sched x (stepBefore x t) v).1.2.2.2.2.2.1
  obtain ⟨-, hJH, hJT, -⟩ := lem57_justification_cache_and_record S Sched x (stepBefore x t) v
  have hσ : (stateBefore x t v).S.σ J₀ = chainStateOf S.C J₀ := by
    rw [← hJ]
    exact hCS _ hJT
  -- `J₀`'s height is the justification height, which is `B`'s
  have hJh : (chainStateOf S.C J₀).h = (chainStateOf S.C B).h := by
    rcases hJH with hg | hh
    · exact absurd (hJ.symm.trans hg) hJ₀
    · have hh' : ((stateBefore x t v).S.σ J₀).h = (stateBefore x t v).S.h_j := by
        rw [← hJ]
        exact hh
      rw [hσ] at hh'
      rw [hh', hH, hmax, Nat.add_sub_cancel]
  -- the two `T_h` agree (Lemma 47 (e)), and `J₀`'s is `J₀` (Lemma 57b)
  have hT := (GoldilocksCorrectness.Statements.Routines.lem47_chain_state_heights S.C J₀
    B).2.2.2.2 hJB hJh
  rcases lem57b_justified_is_entry S Sched x (stepBefore x t) v with hg | he
  · exact absurd (hJ.symm.trans hg) hJ₀
  · have he' : ((stateBefore x t v).S.σ (stateBefore x t v).S.J).T_h =
        (stateBefore x t v).S.J := he
    rw [hJ, hσ] at he'
    rw [← hT, he']

end Execution

end GoldilocksCorrectness.Proofs.Executions
