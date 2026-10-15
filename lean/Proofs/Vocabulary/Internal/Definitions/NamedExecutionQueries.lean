module
public import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.Run
public import Proofs.Vocabulary.Internal.ModelVocabulary.FinalityGadget.Crossing

@[expose] public section


namespace DecoupledConsensusModel.Execution
variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Clock facts -/

/-- A tick at `t` sets the store clock to `t` and the slot to the slot of `t`. -/
def NamedTickTimeQuery (S : Setup V) : Prop :=
  ∀ (v : V) (before : NamedNodeState V) (t : Time),
    (NamedNode.tick S v before t).1.st.core.t = t ∧
    (NamedNode.tick S v before t).1.st.core.s = S.E.slotOf t

/-- Processing an object leaves the store clock and slot unchanged. -/
def NamedProcessTimeQuery (S : Setup V) : Prop :=
  ∀ (n : NamedNodeState V) (o : NamedObject V),
    (NamedNode.process S n o).st.core.t = n.st.core.t ∧
    (NamedNode.process S n o).st.core.s = n.st.core.s

/-- After folding a list of events from a world, a node's clock is its last tick time in the list,
    or unchanged if it has none. -/
def NamedFoldStepTimeQuery (S : Setup V) : Prop :=
  ∀ (w : NamedWorld V) (l : List (NamedEvent V)) (v : V),
    ((l.foldl (NamedWorld.step S) w) v).st.core.t =
      (Run.lastTickIn v l).getD (w v).st.core.t

/-- The clock of `v`'s state before event index `i` is `v`'s last tick time in that prefix, or zero
    if it has none. -/
def NamedStoreTimeEqLastTickQuery (S : Setup V) (rho : NamedRun V) : Prop :=
  ∀ (v : V) (i : Nat),
    (NamedRun.stateBefore S rho i v).st.core.t =
      (Run.lastTickIn v (rho.events.take i)).getD 0

/-! ## Committee-pool invariant -/

/-- The committee-pool invariant of the erased core store. -/
abbrev CorePools (S : Setup V) (st : Protocol.Store V) : Prop :=
  Protocol.CommitteePools S.E st

def NamedTickPoolsQuery (S : Setup V) : Prop :=
  ∀ (v : V) (before : NamedNodeState V) (t : Time),
    CorePools S before.st.core → CorePools S (NamedNode.tick S v before t).1.st.core

def NamedProcessPoolsQuery (S : Setup V) : Prop :=
  ∀ (n : NamedNodeState V) (o : NamedObject V),
    CorePools S n.st.core → CorePools S (NamedNode.process S n o).st.core

/-- Every node of a named world satisfies the committee-pool invariant. -/
def NamedWorldCommitteePools (S : Setup V) (w : NamedWorld V) : Prop :=
  ∀ v : V, CorePools S (w v).st.core

def NamedWorldInitPoolsQuery (S : Setup V) : Prop :=
  NamedWorldCommitteePools S (NamedWorld.init : NamedWorld V)

def NamedWorldStepPoolsQuery (S : Setup V) : Prop :=
  ∀ (w : NamedWorld V) (e : NamedEvent V),
    NamedWorldCommitteePools S w → NamedWorldCommitteePools S (NamedWorld.step S w e)

/-- The committee-pool invariant holds at every event-prefix state, every time read, every
    strict-time read and the final state of the run. -/
def NamedRunPoolsQuery (S : Setup V) (rho : NamedRun V) : Prop :=
  (∀ (i : Nat) (v : V), CorePools S (NamedRun.stateBefore S rho i v).st.core) ∧
  (∀ (t : Time) (v : V), CorePools S (NamedRun.readAt S rho t v).st.core) ∧
  (∀ (t : Time) (v : V), CorePools S (NamedRun.stateBeforeTime S rho t v).st.core) ∧
  (∀ v : V, CorePools S (NamedRun.final S rho v).st.core)

end DecoupledConsensusModel.Execution

end
