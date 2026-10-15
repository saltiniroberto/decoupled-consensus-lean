import Proofs.Instance.Objects
import Proofs.Instance.Equalities.Images

/-!
# The run invariant of a store

The predicates `ChainStatesInTree`, `OffTreeInitial`, `RunStoreInv` and `ConfirmedInTree` on a spec
store, read by `Model.specDraft`.
-/

set_option autoImplicit false

namespace SpecDraftRecord.SubtypeEqualities

open Spec
open SpecDraftRecord.NoRaise
open scoped DC

variable {V : Type} [DecidableEq V]

/-- For every block of the tree `st.T`, the four blocks its chain state names (`L`, `T_h`, `J` and
    `F`) are blocks of the tree. -/
def ChainStatesInTree (st : Store V) : Prop :=
  ∀ B ∈ st.T, (st.σ B).L ∈ st.T ∧ (st.σ B).T_h ∈ st.T ∧ (st.σ B).J ∈ st.T ∧ (st.σ B).F ∈ st.T

/-- Every block outside the tree `st.T` has the initial chain state and no stamp. -/
def OffTreeInitial (st : Store V) : Prop :=
  ∀ B, B ∉ st.T → st.σ B = Protocol.ChainState.initial ∧ st.timestamp_block B = none

/-- The justified block `st.J` is in the tree, `ChainStatesInTree st` holds, and `OffTreeInitial st`
    holds. -/
def RunStoreInv (st : Store V) : Prop :=
  st.J ∈ st.T ∧ ChainStatesInTree st ∧ OffTreeInitial st

end SpecDraftRecord.SubtypeEqualities

namespace SpecDraftRecord.HandlersRunFacts

variable {V : Type} [DecidableEq V]

/-- `st.live_confirmed`, `st.latest_confirmed` and `st.latest_stable` are blocks of the tree `st.T`. -/
def ConfirmedInTree (st : Spec.Store V) : Prop :=
  st.live_confirmed ∈ st.T ∧ st.latest_confirmed ∈ st.T ∧ st.latest_stable ∈ st.T

end SpecDraftRecord.HandlersRunFacts
