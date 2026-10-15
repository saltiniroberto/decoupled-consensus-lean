import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_RowTrace
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_Admission
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_BlockStamp
import Proofs.Vocabulary.Protocol.Schedule.NamedTick
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_ReceiptCallsF1
import Model.Conditions.RunVocabulary
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring

/-!
# Clocks, row stamps and held bodies in a sorted run

In a run sorted by key, the stores around an event have clocks and row stamps at or before the
event's time, and a body held before one time is still held, with the same stamp, before any later
time. Stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedSGArrival
set_option autoImplicit false
open Execution Internal.NamedOutageEntry Internal.NamedStableChainOutage
local macro "sga% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Vocabulary.Protocol.Handlers.SGArrival)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.NamedSGArrival ++ n.getId)))

/-- In a run sorted by key and inside its horizon, for every world `w₁` before event `i` and every
    world `w₂` before event `i + 1`, in each of them `reader`'s clock is at or before `e`'s time,
    and every attestation row `reader` holds for a round `k` is for round `k` and has an SG vote
    stamp at or before `e`'s time. -/
theorem Vocabulary.Proofs.NamedSGArrival.data_at_event_of_fields (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    (hin : ∀ e ∈ rho.events, 0 ≤ e.time ∧ e.time ≤ rho.horizon)
    {i : Nat} {e : Record.Event V} (he : rho.events[i]? = some e) (reader : V) :
    ∀ w₁ ∈ Record.stateBeforeOf M S rho i, ∀ w₂ ∈ Record.stateBeforeOf M S rho (i + 1),
    ((w₁ reader).st.core.t ≤ e.time ∧
        ∀ k (a : NamedAttestation V), a ∈ (w₁ reader).st.sg_rows k →
          a.round = k ∧ ∃ stamp : Time, stamp ≤ e.time ∧
            (w₁ reader).st.core.timestamp_sg_vote (M.sgVote a.erase) = some (stamp : Stamp)) ∧
      ((w₂ reader).st.core.t ≤ e.time ∧
        ∀ k (a : NamedAttestation V), a ∈ (w₂ reader).st.sg_rows k →
          a.round = k ∧ ∃ stamp : Time, stamp ≤ e.time ∧
            (w₂ reader).st.core.timestamp_sg_vote (M.sgVote a.erase) = some (stamp : Stamp)) := by
  have hn := (hin _ (List.mem_of_getElem? he)).1
  intro w₁ hw₁ w₂ hw₂
  constructor
  · exact facts.hdRun.sgArrival_prefix_data S rho e.time hn i
      (fun j f hj hf => Restated.event_time_le rho hsorted hf he hj.le) reader w₁ hw₁
  · exact facts.hdRun.sgArrival_prefix_data S rho e.time hn (i + 1)
      (fun j f hj hf => Restated.event_time_le rho hsorted hf he (Nat.le_of_lt_succ hj)) reader w₂ hw₂

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedOutageClosure
set_option autoImplicit false
open Execution

/-- In a run sorted by key, for `c ≤ d`, for every world `w₁` before `c` in which `reader` holds
    `H`, and every world `w₂` the events from the first one at or after `c` up to the last one
    strictly before `d` lead to from `w₁`, `reader` still holds `H` in `w₂`, and the block stamp of
    `H`'s erasure in `reader`'s store is the same in `w₂` as in `w₁`. -/
theorem Vocabulary.Proofs.NamedOutageClosure.q10_strict_body_carry_of_sorted (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    (reader : V) {c d : Time} (hcd : c ≤ d)
    {H : NamedBlock V} :
    ∀ w₁ ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho c,
    H ∈ (w₁ reader).st.bodies →
    ∀ w₂ ∈ ((rho.events.drop (rho.events.filter (fun e => decide (e.time < c))).length).take
        ((rho.events.filter (fun e => decide (e.time < d))).length -
          (rho.events.filter (fun e => decide (e.time < c))).length)).foldlM
        (Record.worldStepOf M S) w₁,
    H ∈ (w₂ reader).st.bodies ∧
      (w₂ reader).st.core.timestamp_block H.erase =
        (w₁ reader).st.core.timestamp_block H.erase := by
  intro w₁ hw₁ hH w₂ hw₂
  rw [Restated.Vocabulary.Proofs.NamedOutageClosure.strict_read_eq_index facts S rho hsorted c] at hw₁
  exact Restated.Vocabulary.Proofs.NamedBlockStamp.stateBefore_body_stamp_mono facts S rho reader
    (Restated.strict_lengths_mono rho hcd) w₁ hw₁ hH w₂ hw₂

end

end DecoupledConsensusModel.Sts.Restated
