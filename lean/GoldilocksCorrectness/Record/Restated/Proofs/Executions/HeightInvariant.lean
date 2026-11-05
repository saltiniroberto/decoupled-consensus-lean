module
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.HeightInvariantDefs
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.ChainStateStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.FrameDefs
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Monotone
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Node
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ChainStateOf
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.ChainStateStatements

@[expose] public section

/-!
# HeightInvariant, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/HeightInvariant.lean` over a model `M`
whose facts `F` hold, for an execution `x` of `protocolOf M S`: a chain state's justified block
entered its height (`JustifiedIsEntryChain`); `JustifiedFrom` carries it from a node state to the
next; each step of the node and of the atomic semantics relates a node state satisfying the model's
node invariant to the next by `JustifiedFrom`; Lemma 57b, the justified block entered its height at
every step; and the bridge for box 2, read with the greatest chain-state height `hMax M S.C n` of
the node's tree.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Proofs.Routines (DREBPost DREBPost.bind DREBPost.bind_any DREBPost.dite
  DREBPost.ite DREBPost.of_outcome DREBPost.pure forIn_yield_inv)

open GoldilocksCorrectness.Proofs.Routines (fg_on_attestation_J fg_on_block_J_cases)

open GoldilocksCorrectness.Proofs.Routines (on_attestation_J on_block_justifiedFrom
  tick_justifiedFrom)

open GoldilocksCorrectness.Proofs.Routines (fgState_initial_eq initial_eq wake_eq)

open GoldilocksCorrectness.Proofs.Routines (receive_justifiedFrom)

namespace GoldilocksCorrectness.Record.Proofs.Executions

open GoldilocksCorrectness.Record.Statements.Routines (hMax)

open GoldilocksCorrectness.Record.Proofs.Routines (JustifiedFrom)
open GoldilocksCorrectness.Record.Statements.Routines (BoxTwo ChainStatesComputed)

open Goldilocks
open GoldilocksCorrectness.Record.Statements.Executions

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-! ## The chain states -/

section ChainStates

omit [RootOrder] in
/-- A block's `T_h` is its own `T_h`: the block that took a chain into its height took its own
chain there.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `D`: the block.

Read aloud: the block that took a chain into its height took its own chain there. -/
theorem chainStateOf_T_h_T_h (C : Config) (D : Block V) :
    (M.chainStateOf C (M.chainStateOf C D).T_h).T_h = (M.chainStateOf C D).T_h := by
  induction D with
  | genesis => simp only [(GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_genesis_T_h M F)]
  | node p s r votes support ats v ih =>
      have hne : (Block.node p s r votes support ats v) ≠ Block.genesis := by intro h; cases h
      have h2 := (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_height M F) C _ hne
      have h3 := (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_T_h M F) C _ hne
      change _ = (M.chainStateOf C p).h ∨ _ = (M.chainStateOf C p).h + 1 at h2
      change (_ = (M.chainStateOf C p).h → _ = (M.chainStateOf C p).T_h) ∧ _ at h3
      rcases h2 with h2 | h2
      · rw [h3.1 h2]
        exact ih
      · rw [h3.2 h2]
        exact h3.2 h2

/-- `JustifiedIsEntryChain M C J`: the block `J` is the genesis block, or the `T_h` of its chain
state `M.chainStateOf C J` is `J` itself.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `J`: the block.

Read aloud: `J` is the genesis block or entered its own chain's height. -/
def JustifiedIsEntryChain (C : Config) (J : Block V) : Prop :=
  J = Block.genesis ∨ (M.chainStateOf C J).T_h = J

omit [RootOrder] in
/-- A chain state's justified block is the genesis block or the block that took its own chain
into its height.

Why: at the justification height `0` the justified block is the genesis block
(`chainStateOf_J_spec`); otherwise it is the `T_h` of an ancestor-or-self (Lemma 47 (f)), and a
`T_h` is its own `T_h` (`chainStateOf_T_h_T_h`).

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `D`: the block whose justified block is read.

Read aloud: a chain state's justified block entered its height. -/
theorem chainStateOf_J_entry (C : Config) (D : Block V) :
    JustifiedIsEntryChain M C (M.chainStateOf C D).J := by
  by_cases hj : (M.chainStateOf C D).h_j = 0
  · exact Or.inl (((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_J_spec M F) C D).2.1 hj)
  · obtain ⟨Y, -, -, hYT⟩ := (GoldilocksCorrectness.Record.Statements.Routines.lem47f_justified_is_entry M F)
      C D _ rfl (Nat.one_le_iff_ne_zero.mpr hj)
    refine Or.inr ?_
    rw [← hYT]
    exact (chainStateOf_T_h_T_h M F) C Y

end ChainStates

/-! ## The relation -/

section Relation

omit [RootOrder] in
/-- `JustifiedFrom` carries `JustifiedIsEntryChain` of the justified block from the first node
state to the second.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `n`, `n'`: the two node states.

Read aloud: `JustifiedFrom` carries `JustifiedIsEntryChain` forward. -/
theorem justifiedIsEntryChain_of_justifiedFrom (C : Config) {n n' : M.N}
    (h : JustifiedIsEntryChain M C n.justified) (hr : JustifiedFrom M C n n') :
    JustifiedIsEntryChain M C n'.justified := by
  rcases hr with hr | ⟨D, hD⟩
  · rw [hr]
    exact h
  · rw [hD]
    exact (chainStateOf_J_entry M F) C D

end Relation

/-! ## The FG routines -/

section FG

end FG

/-! ## The node -/

section Node

end Node

/-! ## The reactions and the steps -/

section Execution

open Framework.StsMultisetLog (AtomicStep Event TickAllAwakeWake tickAllAwakeUpdate_getElem_react tickAllAwakeUpdate_getElem_st_of_not_react applyNodeStepResult_getElem receive_getElem NodeStepResult View)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks.Sts (Setup)

/-- Every step of the wiring on one event, from a node state whose chain states of its tree are
the blocks' own, relates the node state to the step's state: a tick step is an answer of the
node's tick or keeps the state, a delivery runs the dispatch, a wake writes `awakeSince` only.

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `p`: the validator; `r`: the reading; `view`: its view; `n`: the node state;
  `e`: the event; `res`: the step result.

Read aloud: every step of the node relates a node state satisfying the invariant to the next by
`JustifiedFrom`. -/
theorem reaction_justifiedFrom (S : Setup V) (p : V) (r : ℕ) (view : View V (NamedObject V))
    (n : M.N) (e : Event V (NamedObject V) Empty)
    (res : NodeStepResult (M.N) (NamedObject V))
    (hstep : (protocolOf M S).step p r view n e res)
    -- `n` satisfies the model's node invariant
    (hI : M.nodeInv S.C S.P S.X n) :
    JustifiedFrom M S.C n res.state := by
  cases e with
  | tick =>
      rcases ((GoldilocksCorrectness.Record.step_tick_iff M) S p r view n res).1 hstep with ⟨n', sent, hok, rfl⟩ | ⟨-, rfl⟩
      · exact F.tk.tick_justifiedFrom S.C S.P S.X n (r : Int) n' sent hok hI
      · exact (GoldilocksCorrectness.Record.Proofs.Routines.justifiedFrom_refl M F) S.C _
  | recv m =>
      rw [((GoldilocksCorrectness.Record.step_recv_iff M) S p r view n m res).1 hstep]
      exact F.rcv.receive_justifiedFrom S.C S.P S.X n m.msg hI
  | wake =>
      rw [((GoldilocksCorrectness.Record.step_wake_iff M) S p r view n res).1 hstep]
      exact (GoldilocksCorrectness.Record.Proofs.Routines.justifiedFrom_of_frame M F) S.C
        (F.wk.wake_readers n _).2.2.2.2.1
  | custom ev => exact ev.elim

/-- At every step of every execution, every validator's justified block is the genesis block or
the `T_h` of its own chain state `chainStateOf`. By induction on the step: the initial node
state's justified block is the genesis block, and every step relates the node state before to the
node state after, the chain states of the tree before being the blocks' own (Lemma 11).

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `Sched`: the schedule; `x`: the execution; `i`: the step; `v`: the
  validator.

Read aloud: at every step, every validator's justified block entered its height. -/
theorem justifiedIsEntryChain_of_exec (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (i : ℕ) (v : V) :
    JustifiedIsEntryChain M S.C (x.st i v).justified := by
  induction i with
  | zero =>
      rw [R.init v]
      exact Or.inl (F.init.initial_justified S.C v)
  | succ i ih =>
      refine (justifiedIsEntryChain_of_justifiedFrom M F) S.C ih ?_
      by_cases hv : (∃ t, x.lbl i = Event.tick v t) ∨
          (∃ (tR : ℕ) (keep : Bool), x.lbl i = Event.restart v tR keep) ∨
          ∃ sm, x.lbl i = Event.deliver v sm
      · rcases hv with ⟨t, hl⟩ | ⟨tR, keep, hl⟩ | ⟨sm, hl⟩
        · obtain ⟨n', sent, hok, hst, -⟩ := R.tick i v t hl
          rw [hst]
          exact F.tk.tick_justifiedFrom S.C S.P S.X _ (t : Int) n' sent hok
            (lem11_node_invariant M F S A x R E i v (E.not_mem_corrupted_of_tick hl)).1
        · rw [(R.restart i v tR keep hl).1]
          exact (GoldilocksCorrectness.Record.Proofs.Routines.justifiedFrom_of_frame M F) S.C
            (F.wk.wake_readers _ _).2.2.2.2.1
        · rw [(R.deliver i v sm hl).2.1]
          exact F.rcv.receive_justifiedFrom S.C S.P S.X _ sm.msg
            (lem11_node_invariant M F S A x R E i v
              (Activity.not_mem_corrupted_of_mem_active (E.deliver_active i v sm hl))).1
      · push_neg at hv
        rw [R.untouched i v hv.1 hv.2.1 hv.2.2]
        exact (GoldilocksCorrectness.Record.Proofs.Routines.justifiedFrom_refl M F) S.C _

/-- **Lemma 57b, the justified block entered its height.** The proof; the audited statement is in
`Statements/Executions/HeightInvariantStatements.lean`.

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `Sched`: the schedule; `x`: the execution; `i`: the step; `v`: the
  validator.

Read aloud: at every step, every validator's justified block entered its height. -/
theorem lem57b_justified_is_entry (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (i : ℕ) (v : V) :
    JustifiedIsEntry M S.C (x.st i v) := by
  exact (justifiedIsEntryChain_of_exec M F) S A x R E i v

/-- The bridge for box 2. The proof; the audited statement is in
`Statements/Executions/HeightInvariantStatements.lean`.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `v`: the validator;
- `B`: the block on `J₀`'s chain; `J₀`: the justified block.

Read aloud: in box 2, a block on `J₀`'s chain at one less than the greatest height entered that
height at `J₀`. -/
theorem entry_block_of_boxTwo (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (t : ℕ) (v : V) (B J₀ : Block V)
    (hBox : BoxTwo M S.C (x.stateBefore t v) J₀)
    (hJ₀ : J₀ ≠ Block.genesis)
    (hJB : J₀.AncestorEq B)
    (hH : (M.chainStateOf S.C B).h = hMax M S.C (x.stateBefore t v) - 1) :
    (M.chainStateOf S.C B).T_h = J₀ := by
  obtain ⟨hmax, -, hJ⟩ := hBox
  obtain ⟨-, hJH, -, -⟩ := (GoldilocksCorrectness.Record.Statements.Executions.lem57_justification_cache_and_record M F) S A x R E (x.stepBefore t) v
  -- `J₀`'s height is the justification height, which is `B`'s
  have hJh : (M.chainStateOf S.C J₀).h = (M.chainStateOf S.C B).h := by
    rcases hJH with hg | hh
    · exact absurd (hJ.symm.trans hg) hJ₀
    · have hh' : (M.chainStateOf S.C J₀).h = (x.stateBefore t v).justifiedHeight := by
        rw [← hJ]
        exact hh
      rw [hh', hH, hmax, Nat.add_sub_cancel]
  -- the two `T_h` agree (Lemma 47 (e)), and `J₀`'s is `J₀` (Lemma 57b)
  have hT := ((GoldilocksCorrectness.Record.Statements.Routines.lem47_chain_state_heights M F) S.C J₀
    B).2.2.2.2 hJB hJh
  rcases (lem57b_justified_is_entry M F) S A x R E (x.stepBefore t) v with hg | he
  · exact absurd (hJ.symm.trans hg) hJ₀
  · have he' : (M.chainStateOf S.C (x.stateBefore t v).justified).T_h =
        (x.stateBefore t v).justified := he
    rw [hJ] at he'
    rw [← hT, he']

end Execution

end GoldilocksCorrectness.Record.Proofs.Executions

