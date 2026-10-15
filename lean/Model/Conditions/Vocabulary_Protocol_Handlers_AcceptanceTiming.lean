import Proofs.Vocabulary.Protocol.Handlers.AcceptanceTiming
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Protocol_Handlers_Pool
import Model.Record.Wiring

/-!
# Goldfish vote insertion timing

The condition on a handler segment that inserts Goldfish votes, stated over a model
`M : Record.Model V`, and its agreement with the definition of the same name at
`Record.Model.vocabulary`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Protocol
open Internal
open Execution

/-- A handler segment from `st` to `st'` satisfies `PoolStep` (`poolStep`), and every Goldfish vote
    it newly inserts is stamped `c` (`new_stamp`) and has a slot no later than `k` (`not_future`). -/
structure Vocabulary.Protocol.VoteInsertStep (M : Record.Model V) (c : Time) (k : Slot)
    (st st' : M.S) : Prop where
  poolStep : Restated.Vocabulary.Protocol.PoolStep M st st'
  new_stamp : ∀ (_hstamps : Restated.Vocabulary.Protocol.PoolStamps M st) (u : GoldfishVote V),
    u ∉ st.gf_votes u.slot → u ∈ st'.gf_votes u.slot →
      st'.timestamp_vote u = some (c : Stamp)
  not_future : ∀ (_hstamps : Restated.Vocabulary.Protocol.PoolStamps M st) (u : GoldfishVote V),
    u ∉ st.gf_votes u.slot → u ∈ st'.gf_votes u.slot →
      ¬ k < u.slot

end

/-! ## Agreement at `Record.Model.vocabulary` -/

section
open DecoupledConsensusModel.Protocol
open Internal
open Execution

/-- The definition `VoteInsertStep` of the same name holds exactly when its form over the record
    holds at `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.VoteInsertStep_vocabulary_eq (c : Time) (k : Slot) (st st' : Protocol.Store V) :
    (priv% Proofs.Vocabulary.Protocol.Handlers.AcceptanceTiming DecoupledConsensusModel.Protocol.VoteInsertStep) (V := V) c k st st' ↔ Restated.Vocabulary.Protocol.VoteInsertStep (V := V) Record.Model.vocabulary c k st st' :=
  by
  constructor <;> intro h <;> cases h <;> constructor <;>
    (try simp only [record_vocabulary] at *) <;> assumption

end

end DecoupledConsensusModel.Sts.Restated
