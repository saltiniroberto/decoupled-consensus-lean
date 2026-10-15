import Proofs.Vocabulary.Internal.ModelVocabulary.Protocol.NamedStoreReads
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Record.Wiring

/-!
# Store readers

The fields of a named store and of a node state, read through the core store, over a model
`M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol.NamedStore

/-- The field `t` of `st`'s core store. -/
def _root_.DecoupledConsensusModel.Sts.Record.Model.NS.t {M : Record.Model V} (st : M.NS) : Time := st.core.t

end

section
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol.NamedStore

/-- The field `s` of `st`'s core store. -/
def _root_.DecoupledConsensusModel.Sts.Record.Model.NS.s {M : Record.Model V} (st : M.NS) : Slot := st.core.s

end

section
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol.NamedStore

/-- The field `T` of `st`'s core store. -/
def _root_.DecoupledConsensusModel.Sts.Record.Model.NS.T {M : Record.Model V} (st : M.NS) : Finset (Block V) := st.core.T

end

section
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol.NamedStore

/-- The field `F` of `st`'s core store. -/
def _root_.DecoupledConsensusModel.Sts.Record.Model.NS.F {M : Record.Model V} (st : M.NS) : Block V := st.core.F

end

section
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol.NamedStore

/-- The field `J` of `st`'s core store. -/
def _root_.DecoupledConsensusModel.Sts.Record.Model.NS.J {M : Record.Model V} (st : M.NS) : Block V := st.core.J

end

section
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol.NamedStore

/-- The field `h_j` of `st`'s core store. -/
def _root_.DecoupledConsensusModel.Sts.Record.Model.NS.h_j {M : Record.Model V} (st : M.NS) : Height := st.core.h_j

end

section
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol.NamedStore

/-- The field `h_max` of `st`'s core store. -/
def _root_.DecoupledConsensusModel.Sts.Record.Model.NS.h_max {M : Record.Model V} (st : M.NS) : Height := st.core.h_max

end

section
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol.NamedStore

/-- The field `σ` of `st`'s core store. -/
def _root_.DecoupledConsensusModel.Sts.Record.Model.NS.σ {M : Record.Model V} (st : M.NS) : Block V → M.CS := st.core.σ

end

section
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol.NamedStore

/-- The field `live_confirmed` of `st`'s core store. -/
def _root_.DecoupledConsensusModel.Sts.Record.Model.NS.live_confirmed {M : Record.Model V} (st : M.NS) : Block V := st.core.live_confirmed

end

section
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol.NamedStore

/-- The field `latest_confirmed` of `st`'s core store. -/
def _root_.DecoupledConsensusModel.Sts.Record.Model.NS.latest_confirmed {M : Record.Model V} (st : M.NS) : Block V := st.core.latest_confirmed

end

section
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol.NamedStore

/-- The field `latest_stable` of `st`'s core store. -/
def _root_.DecoupledConsensusModel.Sts.Record.Model.NS.latest_stable {M : Record.Model V} (st : M.NS) : Block V := st.core.latest_stable

end

section
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol.NamedStore

/-- The SG pool of round `r` of `st`'s core store. -/
def _root_.DecoupledConsensusModel.Sts.Record.Model.NS.sg_pool {M : Record.Model V} (st : M.NS) (r : Round) : Finset (CombinedAttestation V) :=
  (M.store_sg_pool st.core r)

end

section
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol.NamedStore

/-- The field `timestamp_block` of `st`'s core store. -/
def _root_.DecoupledConsensusModel.Sts.Record.Model.NS.timestamp_block {M : Record.Model V} (st : M.NS) := st.core.timestamp_block

end

section
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol.NamedStore

/-- The field `timestamp_vote` of `st`'s core store. -/
def _root_.DecoupledConsensusModel.Sts.Record.Model.NS.timestamp_vote {M : Record.Model V} (st : M.NS) := st.core.timestamp_vote

end

section
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol.NamedStore

/-- The field `timestamp_sg_vote` of `st`'s core store. -/
def _root_.DecoupledConsensusModel.Sts.Record.Model.NS.timestamp_sg_vote {M : Record.Model V} (st : M.NS) := st.core.timestamp_sg_vote

end

section
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol.NamedStore

/-- The field `gf_votes` of `st`'s core store. -/
def _root_.DecoupledConsensusModel.Sts.Record.Model.NS.gf_votes {M : Record.Model V} (st : M.NS) := st.core.gf_votes

end

section
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol.NamedStore

/-- The pool `M.store_pool` of `st`'s core store. -/
def _root_.DecoupledConsensusModel.Sts.Record.Model.NS.pool {M : Record.Model V} (st : M.NS) := (M.store_pool st.core)

end

section
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol.NamedStore

/-- The healing store of `st`'s core store. -/
def _root_.DecoupledConsensusModel.Sts.Record.Model.NS.toHealing {M : Record.Model V} (st : M.NS) : M.HS := (M.toHealing st.core)

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Execution.NamedNodeState

/-- The healing store of `n`'s core store. -/
def _root_.DecoupledConsensusModel.Sts.Record.Model.N.toHealing {M : Record.Model V} (n : M.N) : M.HS := (M.toHealing n.st.core)

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Execution.NamedNodeState

/-- The field `s` of `n`'s core store. -/
def _root_.DecoupledConsensusModel.Sts.Record.Model.N.s {M : Record.Model V} (n : M.N) : Slot := n.st.core.s

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Execution.NamedNodeState

/-- The field `T` of `n`'s core store. -/
def _root_.DecoupledConsensusModel.Sts.Record.Model.N.T {M : Record.Model V} (n : M.N) : Finset (Block V) := n.st.core.T

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Execution.NamedNodeState

/-- The field `F` of `n`'s core store. -/
def _root_.DecoupledConsensusModel.Sts.Record.Model.N.F {M : Record.Model V} (n : M.N) : Block V := n.st.core.F

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Execution.NamedNodeState

/-- The field `J` of `n`'s core store. -/
def _root_.DecoupledConsensusModel.Sts.Record.Model.N.J {M : Record.Model V} (n : M.N) : Block V := n.st.core.J

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Execution.NamedNodeState

/-- The field `h_j` of `n`'s core store. -/
def _root_.DecoupledConsensusModel.Sts.Record.Model.N.h_j {M : Record.Model V} (n : M.N) : Height := n.st.core.h_j

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Execution.NamedNodeState

/-- The field `h_max` of `n`'s core store. -/
def _root_.DecoupledConsensusModel.Sts.Record.Model.N.h_max {M : Record.Model V} (n : M.N) : Height := n.st.core.h_max

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Execution.NamedNodeState

/-- The field `σ` of `n`'s core store. -/
def _root_.DecoupledConsensusModel.Sts.Record.Model.N.σ {M : Record.Model V} (n : M.N) : Block V → M.CS := n.st.core.σ

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Execution.NamedNodeState

/-- The field `live_confirmed` of `n`'s core store. -/
def _root_.DecoupledConsensusModel.Sts.Record.Model.N.live_confirmed {M : Record.Model V} (n : M.N) : Block V := n.st.core.live_confirmed

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Execution.NamedNodeState

/-- The pool `M.store_pool` of `n`'s core store. -/
def _root_.DecoupledConsensusModel.Sts.Record.Model.N.pool {M : Record.Model V} (n : M.N) := (M.store_pool n.st.core)

end

section
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol.NamedStore
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Execution.NamedNodeState

/-- `DecoupledConsensusModel.Protocol.NamedStore.t` equals `Record.Model.NS.t` at the model
    `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.NamedStore.t_vocabulary_eq (st : NamedStore V) :
    _root_.DecoupledConsensusModel.Protocol.NamedStore.t (V := V) st = Record.Model.NS.t (V := V) (M := Record.Model.vocabulary) st :=
  rfl

/-- `DecoupledConsensusModel.Protocol.NamedStore.s` equals `Record.Model.NS.s` at the model
    `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.NamedStore.s_vocabulary_eq (st : NamedStore V) :
    _root_.DecoupledConsensusModel.Protocol.NamedStore.s (V := V) st = Record.Model.NS.s (V := V) (M := Record.Model.vocabulary) st :=
  rfl

/-- `DecoupledConsensusModel.Protocol.NamedStore.T` equals `Record.Model.NS.T` at the model
    `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.NamedStore.T_vocabulary_eq (st : NamedStore V) :
    _root_.DecoupledConsensusModel.Protocol.NamedStore.T (V := V) st = Record.Model.NS.T (V := V) (M := Record.Model.vocabulary) st :=
  rfl

/-- `DecoupledConsensusModel.Protocol.NamedStore.F` equals `Record.Model.NS.F` at the model
    `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.NamedStore.F_vocabulary_eq (st : NamedStore V) :
    _root_.DecoupledConsensusModel.Protocol.NamedStore.F (V := V) st = Record.Model.NS.F (V := V) (M := Record.Model.vocabulary) st :=
  rfl

/-- `DecoupledConsensusModel.Protocol.NamedStore.J` equals `Record.Model.NS.J` at the model
    `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.NamedStore.J_vocabulary_eq (st : NamedStore V) :
    _root_.DecoupledConsensusModel.Protocol.NamedStore.J (V := V) st = Record.Model.NS.J (V := V) (M := Record.Model.vocabulary) st :=
  rfl

/-- `DecoupledConsensusModel.Protocol.NamedStore.h_j` equals `Record.Model.NS.h_j` at the model
    `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.NamedStore.h_j_vocabulary_eq (st : NamedStore V) :
    _root_.DecoupledConsensusModel.Protocol.NamedStore.h_j (V := V) st = Record.Model.NS.h_j (V := V) (M := Record.Model.vocabulary) st :=
  rfl

/-- `DecoupledConsensusModel.Protocol.NamedStore.h_max` equals `Record.Model.NS.h_max` at the model
    `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.NamedStore.h_max_vocabulary_eq (st : NamedStore V) :
    _root_.DecoupledConsensusModel.Protocol.NamedStore.h_max (V := V) st = Record.Model.NS.h_max (V := V) (M := Record.Model.vocabulary) st :=
  rfl

/-- `DecoupledConsensusModel.Protocol.NamedStore.σ` equals `Record.Model.NS.σ` at the model
    `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.NamedStore.σ_vocabulary_eq (st : NamedStore V) :
    _root_.DecoupledConsensusModel.Protocol.NamedStore.σ (V := V) st = Record.Model.NS.σ (V := V) (M := Record.Model.vocabulary) st :=
  rfl

/-- `DecoupledConsensusModel.Protocol.NamedStore.live_confirmed` equals
    `Record.Model.NS.live_confirmed` at the model `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.NamedStore.live_confirmed_vocabulary_eq (st : NamedStore V) :
    _root_.DecoupledConsensusModel.Protocol.NamedStore.live_confirmed (V := V) st = Record.Model.NS.live_confirmed (V := V) (M := Record.Model.vocabulary) st :=
  rfl

/-- `DecoupledConsensusModel.Protocol.NamedStore.latest_confirmed` equals
    `Record.Model.NS.latest_confirmed` at the model `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.NamedStore.latest_confirmed_vocabulary_eq (st : NamedStore V) :
    _root_.DecoupledConsensusModel.Protocol.NamedStore.latest_confirmed (V := V) st = Record.Model.NS.latest_confirmed (V := V) (M := Record.Model.vocabulary) st :=
  rfl

/-- `DecoupledConsensusModel.Protocol.NamedStore.latest_stable` equals
    `Record.Model.NS.latest_stable` at the model `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.NamedStore.latest_stable_vocabulary_eq (st : NamedStore V) :
    _root_.DecoupledConsensusModel.Protocol.NamedStore.latest_stable (V := V) st = Record.Model.NS.latest_stable (V := V) (M := Record.Model.vocabulary) st :=
  rfl

/-- `DecoupledConsensusModel.Protocol.NamedStore.sg_pool` equals `Record.Model.NS.sg_pool` at the
    model `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.NamedStore.sg_pool_vocabulary_eq (st : NamedStore V) (r : Round) :
    _root_.DecoupledConsensusModel.Protocol.NamedStore.sg_pool (V := V) st r = Record.Model.NS.sg_pool (V := V) (M := Record.Model.vocabulary) st r :=
  rfl

/-- `DecoupledConsensusModel.Protocol.NamedStore.timestamp_block` equals
    `Record.Model.NS.timestamp_block` at the model `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.NamedStore.timestamp_block_vocabulary_eq (st : NamedStore V) :
    _root_.DecoupledConsensusModel.Protocol.NamedStore.timestamp_block (V := V) st = Record.Model.NS.timestamp_block (V := V) (M := Record.Model.vocabulary) st :=
  rfl

/-- `DecoupledConsensusModel.Protocol.NamedStore.timestamp_vote` equals
    `Record.Model.NS.timestamp_vote` at the model `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.NamedStore.timestamp_vote_vocabulary_eq (st : NamedStore V) :
    _root_.DecoupledConsensusModel.Protocol.NamedStore.timestamp_vote (V := V) st = Record.Model.NS.timestamp_vote (V := V) (M := Record.Model.vocabulary) st :=
  rfl

/-- `DecoupledConsensusModel.Protocol.NamedStore.timestamp_sg_vote` equals
    `Record.Model.NS.timestamp_sg_vote` at the model `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.NamedStore.timestamp_sg_vote_vocabulary_eq (st : NamedStore V) :
    _root_.DecoupledConsensusModel.Protocol.NamedStore.timestamp_sg_vote (V := V) st = Record.Model.NS.timestamp_sg_vote (V := V) (M := Record.Model.vocabulary) st :=
  rfl

/-- `DecoupledConsensusModel.Protocol.NamedStore.gf_votes` equals `Record.Model.NS.gf_votes` at the
    model `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.NamedStore.gf_votes_vocabulary_eq (st : NamedStore V) :
    _root_.DecoupledConsensusModel.Protocol.NamedStore.gf_votes (V := V) st = Record.Model.NS.gf_votes (V := V) (M := Record.Model.vocabulary) st :=
  rfl

/-- `DecoupledConsensusModel.Protocol.NamedStore.pool` equals `Record.Model.NS.pool` at the model
    `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.NamedStore.pool_vocabulary_eq (st : NamedStore V) :
    _root_.DecoupledConsensusModel.Protocol.NamedStore.pool (V := V) st = Record.Model.NS.pool (V := V) (M := Record.Model.vocabulary) st :=
  rfl

/-- `DecoupledConsensusModel.Protocol.NamedStore.toHealing` equals `Record.Model.NS.toHealing` at
    the model `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.NamedStore.toHealing_vocabulary_eq (st : NamedStore V) :
    _root_.DecoupledConsensusModel.Protocol.NamedStore.toHealing (V := V) st = Record.Model.NS.toHealing (V := V) (M := Record.Model.vocabulary) st :=
  rfl

/-- `DecoupledConsensusModel.Execution.NamedNodeState.toHealing` equals `Record.Model.N.toHealing`
    at the model `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Execution.NamedNodeState.toHealing_vocabulary_eq (n : NamedNodeState V) :
    _root_.DecoupledConsensusModel.Execution.NamedNodeState.toHealing (V := V) n = Record.Model.N.toHealing (V := V) (M := Record.Model.vocabulary) n :=
  rfl

/-- `DecoupledConsensusModel.Execution.NamedNodeState.s` equals `Record.Model.N.s` at the model
    `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Execution.NamedNodeState.s_vocabulary_eq (n : NamedNodeState V) :
    _root_.DecoupledConsensusModel.Execution.NamedNodeState.s (V := V) n = Record.Model.N.s (V := V) (M := Record.Model.vocabulary) n :=
  rfl

/-- `DecoupledConsensusModel.Execution.NamedNodeState.T` equals `Record.Model.N.T` at the model
    `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Execution.NamedNodeState.T_vocabulary_eq (n : NamedNodeState V) :
    _root_.DecoupledConsensusModel.Execution.NamedNodeState.T (V := V) n = Record.Model.N.T (V := V) (M := Record.Model.vocabulary) n :=
  rfl

/-- `DecoupledConsensusModel.Execution.NamedNodeState.F` equals `Record.Model.N.F` at the model
    `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Execution.NamedNodeState.F_vocabulary_eq (n : NamedNodeState V) :
    _root_.DecoupledConsensusModel.Execution.NamedNodeState.F (V := V) n = Record.Model.N.F (V := V) (M := Record.Model.vocabulary) n :=
  rfl

/-- `DecoupledConsensusModel.Execution.NamedNodeState.J` equals `Record.Model.N.J` at the model
    `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Execution.NamedNodeState.J_vocabulary_eq (n : NamedNodeState V) :
    _root_.DecoupledConsensusModel.Execution.NamedNodeState.J (V := V) n = Record.Model.N.J (V := V) (M := Record.Model.vocabulary) n :=
  rfl

/-- `DecoupledConsensusModel.Execution.NamedNodeState.h_j` equals `Record.Model.N.h_j` at the model
    `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Execution.NamedNodeState.h_j_vocabulary_eq (n : NamedNodeState V) :
    _root_.DecoupledConsensusModel.Execution.NamedNodeState.h_j (V := V) n = Record.Model.N.h_j (V := V) (M := Record.Model.vocabulary) n :=
  rfl

/-- `DecoupledConsensusModel.Execution.NamedNodeState.h_max` equals `Record.Model.N.h_max` at the
    model `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Execution.NamedNodeState.h_max_vocabulary_eq (n : NamedNodeState V) :
    _root_.DecoupledConsensusModel.Execution.NamedNodeState.h_max (V := V) n = Record.Model.N.h_max (V := V) (M := Record.Model.vocabulary) n :=
  rfl

/-- `DecoupledConsensusModel.Execution.NamedNodeState.σ` equals `Record.Model.N.σ` at the model
    `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Execution.NamedNodeState.σ_vocabulary_eq (n : NamedNodeState V) :
    _root_.DecoupledConsensusModel.Execution.NamedNodeState.σ (V := V) n = Record.Model.N.σ (V := V) (M := Record.Model.vocabulary) n :=
  rfl

/-- `DecoupledConsensusModel.Execution.NamedNodeState.live_confirmed` equals
    `Record.Model.N.live_confirmed` at the model `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Execution.NamedNodeState.live_confirmed_vocabulary_eq (n : NamedNodeState V) :
    _root_.DecoupledConsensusModel.Execution.NamedNodeState.live_confirmed (V := V) n = Record.Model.N.live_confirmed (V := V) (M := Record.Model.vocabulary) n :=
  rfl

/-- `DecoupledConsensusModel.Execution.NamedNodeState.pool` equals `Record.Model.N.pool` at the
    model `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Execution.NamedNodeState.pool_vocabulary_eq (n : NamedNodeState V) :
    _root_.DecoupledConsensusModel.Execution.NamedNodeState.pool (V := V) n = Record.Model.N.pool (V := V) (M := Record.Model.vocabulary) n :=
  rfl

end

end DecoupledConsensusModel.Sts.Restated
