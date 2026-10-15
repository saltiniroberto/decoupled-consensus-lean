import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Protocol_Handlers_Pool
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bStepKitConfirm

/-!
# What a write sequence at a fixed clock leaves

The structure `InsertsData` of what one write sequence at clock `c` leaves in a store, and the
condition `InsertsAt`, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- What one write sequence at clock `c` from the store `st` to the store `st'` leaves behind. -/
structure InsertsData (M : Record.Model V) (E : Env V) (c : Int) (st st' : M.S) : Prop where
  /-- Every vote and every stamp `st` held is held in `st'`. -/
  carry : Restated.Vocabulary.Protocol.PoolCarry M st st'
  /-- The store `st'` satisfies `Restated.Vocabulary.Protocol.PoolStamps`. -/
  stamps : Restated.Vocabulary.Protocol.PoolStamps M st'
  /-- The clock of `st'` reads `c`. -/
  clock : st'.t = c
  /-- The slot field is unchanged. -/
  slot : st'.s = st.s
  /-- A vote that entered is stamped with `c`, is of a slot at most `st`'s, and is signed by a
      member of its own slot's committee. -/
  new : ∀ u : GoldfishVote V, u ∉ st.gf_votes u.slot → u ∈ st'.gf_votes u.slot →
    st'.timestamp_vote u = some (c : Stamp) ∧ u.slot ≤ st.s ∧
      u.val_index ∈ E.committee u.slot

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- From a store `st` that satisfies `Restated.Vocabulary.Protocol.PoolStamps` and whose clock reads
    `c`, the write to `st'` leaves `InsertsData`. -/
def InsertsAt (M : Record.Model V) (E : Env V) (c : Int) (st st' : M.S) : Prop :=
  Restated.Vocabulary.Protocol.PoolStamps M st → st.t = c → Restated.InsertsData M E c st st'

end

/-! ## Agreement at the model `Record.Model.vocabulary` -/

section
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- `_root_.DecoupledConsensusModel.Sts.InsertsData` holds exactly when `Restated.InsertsData` holds
    at the model `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem InsertsData_vocabulary_eq (E : Env V) (c : Int) (st st' : Protocol.Store V) :
    _root_.DecoupledConsensusModel.Sts.InsertsData (V := V) E c st st' ↔ Restated.InsertsData (V := V) Record.Model.vocabulary E c st st' :=
  by
  constructor <;> intro h <;> cases h <;> constructor <;>
    (try simp only [record_vocabulary] at *) <;> assumption

/-- `_root_.DecoupledConsensusModel.Sts.InsertsAt` holds exactly when `Restated.InsertsAt` holds at
    the model `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem InsertsAt_vocabulary_eq (E : Env V) (c : Int) (st st' : Protocol.Store V) :
    _root_.DecoupledConsensusModel.Sts.InsertsAt (V := V) E c st st' ↔ Restated.InsertsAt (V := V) Record.Model.vocabulary E c st st' := by
  unfold _root_.DecoupledConsensusModel.Sts.InsertsAt Restated.InsertsAt
  simp only [record_vocabulary]
  exact Iff.rfl

end

end DecoupledConsensusModel.Sts.Restated
