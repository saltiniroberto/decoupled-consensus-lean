import Proofs.Vocabulary.Protocol.Schedule.Alignment
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Record.Wiring

/-!
# Slot and round alignment of a store

The conditions that a store's slot is the slot of its clock and that its SG vote buckets hold their
own round's attestations, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Statements.Instantiation
open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Internal
open Execution
open Protocol

/-- The slot of `st` is the slot of its clock. -/
def Vocabulary.Proofs.Optimistic.SlotOfClock (M : Record.Model V) (E : Env V) (st : M.S) : Prop :=
  st.s = E.slotOf st.t

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Statements.Instantiation
open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Internal
open Execution
open Protocol

/-- Every bucket `st.sg_votes r` holds round-`r` attestations only. -/
def Vocabulary.Proofs.Optimistic.SgRounds (M : Record.Model V) (st : M.S) : Prop :=
  ∀ (r : Round) (a : CombinedAttestation V), a ∈ st.sg_votes r → a.round = r

end

end DecoupledConsensusModel.Sts.Restated
