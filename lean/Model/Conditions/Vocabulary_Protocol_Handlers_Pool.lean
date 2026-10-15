import Proofs.Vocabulary.Protocol.Handlers.Pool
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Record.Wiring

/-!
# The Goldfish vote pool

The invariant of a store's Goldfish vote pool and its stamps, what one handler application carries,
and where a pooled vote comes from, stated over a model `M : Record.Model V`, and their agreement
with the definitions of the same name at `Record.Model.vocabulary`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Protocol
open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Internal
open Execution

/-- The invariant of a store's Goldfish vote pool: bucket `k` holds slot-`k` votes only, exactly the
    pooled votes are stamped, and no stamp is later than the store's clock. -/
structure Vocabulary.Protocol.PoolStamps (M : Record.Model V) (st : M.S) : Prop where
  /-- Bucket `k` holds slot-`k` votes only. -/
  slot : ∀ (k : Slot) (u : GoldfishVote V), u ∈ st.gf_votes k → u.slot = k
  /-- A pooled vote is stamped. -/
  stamped : ∀ (k : Slot) (u : GoldfishVote V), u ∈ st.gf_votes k →
    (st.timestamp_vote u).isSome = true
  /-- A stamped vote is pooled. -/
  pooled : ∀ u : GoldfishVote V, (st.timestamp_vote u).isSome = true →
    u ∈ st.gf_votes u.slot
  /-- No vote stamp is later than the store's clock. -/
  bounded : ∀ (u : GoldfishVote V) (c : Stamp), st.timestamp_vote u = some c →
    c ≤ (st.t : Stamp)

end

section
open DecoupledConsensusModel.Protocol
open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Internal
open Execution

/-- What one handler application from `st` to `st'` carries: pooled votes stay pooled, with the same
    stamp. -/
structure Vocabulary.Protocol.PoolCarry (M : Record.Model V) (st st' : M.S) : Prop where
  /-- The pool only grows. -/
  mem : ∀ (k : Slot) (u : GoldfishVote V), u ∈ st.gf_votes k → u ∈ st'.gf_votes k
  /-- A stamp already written is not rewritten. -/
  stamp : ∀ (u : GoldfishVote V) (c : Stamp), st.timestamp_vote u = some c →
    st'.timestamp_vote u = some c

end

section
open DecoupledConsensusModel.Protocol
open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Internal
open Execution

/-- From `PoolStamps` at `st`, the transition to `st'` satisfies `PoolCarry` and `PoolStamps` holds
    at `st'`. -/
def Vocabulary.Protocol.PoolStep (M : Record.Model V) (st st' : M.S) : Prop :=
  Restated.Vocabulary.Protocol.PoolStamps M st → Restated.Vocabulary.Protocol.PoolCarry M st st' ∧ Restated.Vocabulary.Protocol.PoolStamps M st'

end

section
open DecoupledConsensusModel.Protocol
open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Internal
open Execution

/-- Every Goldfish vote in `st'`'s pool was in `st`'s pool, is in `l`, or is included in a block in
    `l`. -/
def Vocabulary.Protocol.GfFrom (M : Record.Model V) (st : M.S) (l : List (Object V)) (st' : M.S) : Prop :=
  ∀ (k : Slot) (u : GoldfishVote V), u ∈ st'.gf_votes k →
    u ∈ st.gf_votes k ∨ Object.gfVote u ∈ l ∨
      ∃ B : NamedBlock V, Object.block B ∈ l ∧ u ∈ B.gf_votes

end

/-! ## Agreement at `Record.Model.vocabulary` -/

section
open DecoupledConsensusModel.Protocol
open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Internal
open Execution

/-- `DecoupledConsensusModel.Protocol.PoolStamps` holds exactly when its form over the record holds
    at `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.PoolStamps_vocabulary_eq (st : Protocol.Store V) :
    _root_.DecoupledConsensusModel.Protocol.PoolStamps (V := V) st ↔ Restated.Vocabulary.Protocol.PoolStamps (V := V) Record.Model.vocabulary st :=
  by
  constructor <;> intro h <;> cases h <;> constructor <;> assumption

/-- `DecoupledConsensusModel.Protocol.PoolCarry` holds exactly when its form over the record holds
    at `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.PoolCarry_vocabulary_eq (st st' : Protocol.Store V) :
    _root_.DecoupledConsensusModel.Protocol.PoolCarry (V := V) st st' ↔ Restated.Vocabulary.Protocol.PoolCarry (V := V) Record.Model.vocabulary st st' :=
  by
  constructor <;> intro h <;> cases h <;> constructor <;> assumption

/-- `DecoupledConsensusModel.Protocol.PoolStep` holds exactly when its form over the record holds at
    `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.PoolStep_vocabulary_eq (st st' : Protocol.Store V) :
    _root_.DecoupledConsensusModel.Protocol.PoolStep (V := V) st st' ↔ Restated.Vocabulary.Protocol.PoolStep (V := V) Record.Model.vocabulary st st' := by
  simp only [_root_.DecoupledConsensusModel.Protocol.PoolStep, Restated.Vocabulary.Protocol.PoolStep,
    Vocabulary.Protocol.PoolStamps_vocabulary_eq, Vocabulary.Protocol.PoolCarry_vocabulary_eq]

/-- `DecoupledConsensusModel.Protocol.GfFrom` holds exactly when its form over the record holds at
    `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.GfFrom_vocabulary_eq (st : Protocol.Store V) (l : List (Object V)) (st' : Protocol.Store V) :
    _root_.DecoupledConsensusModel.Protocol.GfFrom (V := V) st l st' ↔ Restated.Vocabulary.Protocol.GfFrom (V := V) Record.Model.vocabulary st l st' :=
  Iff.rfl

end

end DecoupledConsensusModel.Sts.Restated
