import Proofs.Vocabulary.Internal.Definitions.NamedOutageEntry
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedActionReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# Emissions and reads at a round's action

Whether a validator emits its attestation at a round's action instant along a path of a run, its
confirmation and action reads, and the phase tick of its cache, stated over a model
`M : Record.Model V`, and their counterparts at `Record.Model.vocabulary`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.NamedOutageEntry
open Execution DecoupledConsensusModel.Protocol

/-- `true` exactly when some event `i` of `rho` is `v`'s tick at round `k`'s action instant and some
    outcome of that tick from `v`'s node state in `W i`, with `v`'s node state in `W (i + 1)` as its
    result, sends an attestation of `v` for round `k`. -/
noncomputable def Vocabulary.Internal.NamedOutageEntry.emittedInRound (M : Record.Model V) (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → M.N) (v : V) (k : Round) : Bool := by
  classical
  exact decide (∃ i : Nat,
    rho.events[i]? = some (.tick v (Restated.Vocabulary.Execution.Setup.a M S k)) ∧
    ∃ out : M.N × List (NamedObject V),
      M.tick S v (W i v) (Restated.Vocabulary.Execution.Setup.a M S k) ⇢ out ∧
      W (i + 1) v = out.1 ∧
      out.2.any (fun o =>
        match o with
        | .attest a => decide (a.val_index = v ∧ a.round = k)
        | _ => false) = true)

end

section
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.NamedOutageEntry
open Execution DecoupledConsensusModel.Protocol

/-- The set of `v`'s confirmation reads at time `t`, one for every world that can hold before `t`. -/
def Vocabulary.Internal.NamedOutageEntry.confirmationReadAt (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (v : V) (t : Time) :
    DC.NDR M.N :=
  Restated.Vocabulary.Execution.NamedActionReads.confirmationReadAt M S rho v t

end

section
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.NamedOutageEntry
open Execution DecoupledConsensusModel.Protocol

/-- The outcomes of the phase tick at `t` on `before`'s healing store and cache. -/
def Vocabulary.Internal.NamedOutageEntry.preparedCache (M : Record.Model V) (S : Setup V) (before : M.N) (t : Time) :
    DC.NDRE M.Cache :=
  M.onPhaseTick S.E S.hc before.st.core.toHealing t before.cache

end

section
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.NamedOutageEntry
open Execution DecoupledConsensusModel.Protocol

/-- The set of round-`r` action reads staged from `before`,
    `NamedActionReads.actionReadFrom M S before r`. -/
def Vocabulary.Internal.NamedOutageEntry.actionReadFrom (M : Record.Model V) (S : Setup V) (before : M.N) (r : Round) :
    DC.NDR M.N :=
  Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r

end

/-! ## Agreement at `Record.Model.vocabulary` -/

section
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.NamedOutageEntry
open Execution DecoupledConsensusModel.Protocol

/-- At `Record.Model.vocabulary` and a run embedded by `Record.Run.ofVocabulary`, along the path
    `fun i => NamedRun.stateBefore S rho i`, the restated `emittedInRound` has the value of
    `DecoupledConsensusModel.Internal.NamedOutageEntry.emittedInRound`. -/
@[record_vocabulary]
theorem Vocabulary.Internal.NamedOutageEntry.emittedInRound_vocabulary_eq (S : Setup V) (rho : NamedRun V) (v : V) (k : Round) :
    Restated.Vocabulary.Internal.NamedOutageEntry.emittedInRound (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun i => NamedRun.stateBefore S rho i) v k =
      _root_.DecoupledConsensusModel.Internal.NamedOutageEntry.emittedInRound (V := V) S rho v k := by
  rw [Bool.eq_iff_iff, Restated.Vocabulary.Internal.NamedOutageEntry.emittedInRound,
    _root_.DecoupledConsensusModel.Internal.NamedOutageEntry.emittedInRound, List.any_eq_true]
  simp only [decide_eq_true_eq, Record.Run.ofVocabulary_events,
    Record.Event.map_ofVocabulary_getElem?_tick]
  constructor
  · rintro ⟨i, hi, out, hout, -, hany⟩
    rw [(Record.returns_pure _ out).1 hout] at hany
    refine ⟨i, List.mem_range.mpr (List.getElem?_eq_some_iff.mp hi).1, ?_⟩
    rw [hi]
    exact (if_pos ⟨rfl, rfl⟩).trans hany
  · rintro ⟨i, -, hfi⟩
    cases he : rho.events[i]? with
    | none => rw [he] at hfi; exact absurd hfi Bool.false_ne_true
    | some e =>
      rw [he] at hfi
      rcases e with ⟨u, t⟩ | ⟨u, o, t⟩
      · by_cases hc : u = v ∧ t = _root_.DecoupledConsensusModel.Execution.Setup.a S k
        · obtain ⟨rfl, rfl⟩ := hc
          dsimp only at hfi
          rw [if_pos ⟨rfl, rfl⟩] at hfi
          exact ⟨i, he, _, (Record.returns_pure _ _).2 rfl,
            _root_.DecoupledConsensusModel.Proofs.NamedRuntime.stateBefore_tick S rho he, hfi⟩
        · dsimp only at hfi
          rw [if_neg hc] at hfi
          exact absurd hfi Bool.false_ne_true
      · exact absurd hfi Bool.false_ne_true

/-- At `Record.Model.vocabulary` and a run embedded by `Record.Run.ofVocabulary`, the restated
    `confirmationReadAt` is the singleton of the value of
    `DecoupledConsensusModel.Internal.NamedOutageEntry.confirmationReadAt`. -/
@[record_vocabulary]
theorem Vocabulary.Internal.NamedOutageEntry.confirmationReadAt_vocabulary_eq (S : Setup V) (rho : NamedRun V) (v : V) (t : Time) :
    Restated.Vocabulary.Internal.NamedOutageEntry.confirmationReadAt (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) v t =
      {_root_.DecoupledConsensusModel.Internal.NamedOutageEntry.confirmationReadAt (V := V) S rho v t} :=
  Vocabulary.Execution.NamedActionReads.confirmationReadAt_vocabulary_eq S rho v t

/-- At `Record.Model.vocabulary`, the restated `preparedCache` is the one outcome
    `DecoupledConsensusModel.Internal.NamedOutageEntry.preparedCache` computes. -/
@[record_vocabulary]
theorem Vocabulary.Internal.NamedOutageEntry.preparedCache_vocabulary_eq (S : Setup V) (before : NamedNodeState V) (t : Time) :
    Restated.Vocabulary.Internal.NamedOutageEntry.preparedCache (V := V) Record.Model.vocabulary S before t =
      pure (_root_.DecoupledConsensusModel.Internal.NamedOutageEntry.preparedCache (V := V) S before t) := by
  unfold _root_.DecoupledConsensusModel.Internal.NamedOutageEntry.preparedCache
    Execution.NamedActionReads.preparedCache
  rfl

/-- At `Record.Model.vocabulary`, the restated `actionReadFrom` is the singleton of the value of
    `DecoupledConsensusModel.Internal.NamedOutageEntry.actionReadFrom`. -/
@[record_vocabulary]
theorem Vocabulary.Internal.NamedOutageEntry.actionReadFrom_vocabulary_eq (S : Setup V) (before : NamedNodeState V) (r : Round) :
    Restated.Vocabulary.Internal.NamedOutageEntry.actionReadFrom (V := V) Record.Model.vocabulary S before r =
      {_root_.DecoupledConsensusModel.Internal.NamedOutageEntry.actionReadFrom (V := V) S before r} :=
  Vocabulary.Execution.NamedActionReads.actionReadFrom_vocabulary_eq S before r

end

end DecoupledConsensusModel.Sts.Restated
