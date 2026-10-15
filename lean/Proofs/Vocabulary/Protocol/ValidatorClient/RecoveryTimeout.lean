module
public import Proofs.Vocabulary.Protocol.ValidatorClient.FinalityPairCore
public import Proofs.Vocabulary.ModelProperties.Store_toHealing
public import Proofs.Vocabulary.ModelProperties.NamedDuties_attest_with
public import Proofs.Vocabulary.Protocol.ValidatorClient.RecordFresh
public import Proofs.Vocabulary.Protocol.ValidatorClient.HeightPairCases
public import Proofs.Vocabulary.Internal.Legacy.Definitions.ActionSources
public import Proofs.Vocabulary.Internal.ModelVocabulary.Protocol.NamedStoreReads
import Proofs.Vocabulary.Protocol.ValidatorClient.RecordClean
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section

/-!
# Timeouts at a fresh height in the round action

At a height where the record is fresh, the height pair rule emits a timeout when the `nj` bit is set
and the finality pair avoids that height, and the named round action's finality pair is computed at
its Goldfish head.
-/


namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Protocol (Record height_pair own_lock finality_pair)
open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

omit [DecidableEq V] [Fintype V] in
/-- At a height `H` where the record is fresh, height fields `(H, T, true)` and a finality pair not
    at `H` make `height_pair` emit a timeout at `H`. -/
theorem height_pair_timeout_of_fresh_of_finality_avoids
    {Lambda : Record} {H : Height} {T : BlockId}
    (hfresh : RecordFreshAt Lambda H) (fp : Option FinalityPair)
    (havoid : forall p : FinalityPair, fp = some p -> p.height ≠ H) :
    height_pair Lambda (some (H, T, true)) fp = HeightPair.timeout H := by
  cases fp with
  | none =>
      rcases hfresh with ⟨htarget, htimeout, hlock⟩
      simp [height_pair, own_lock, htarget, htimeout, hlock]
  | some p =>
      exact height_pair_timeout_of_fresh_of_finality_height_ne
        hfresh (havoid p rfl)


/-- The named round action's finality pair is `finality_pair` at the round action's resolved
    Goldfish head. -/
theorem round_action_finality_pair_eq (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V)
    (st : Protocol.HealingStore V) (record : Protocol.NamedRecord) :
    (Protocol.NamedActions.round_action_with contract E hc nd st record).2.finality_pair =
      finality_pair record.legacy
        (st.σ (actionHeadWith contract E hc st)).h_j
        (st.σ (actionHeadWith contract E hc st)).J.root
        (st.σ (actionHeadWith contract E hc st)).h_F := by
  simp only [Protocol.NamedActions.round_action_with, Protocol.with_attestation_input,
    Protocol.NamedActions.creatorInput, Protocol.NamedRecord.create,
    Protocol.NamedRecord.legacyCreate, Protocol.NamedRecord.encodeRow,
    Protocol.get_fg_vote_with, Protocol.create_attestation, actionHeadWith]

/-! ## Run-level exclusion of the recovery height at the action head -/

/-- The store before time `t` is the store at time `t - 1`. -/
theorem storeBeforeTime_eq_storeAt_sub_one_recovery
    (S : Setup V) (rho : Run V) (v : V) (t : Time) :
    rho.storeBeforeTime S v t = rho.storeAt S v (t - 1) := by
  have hfilter :
      (fun e : Event V => decide (e.time < t)) =
        (fun e : Event V => decide (e.time <= t - 1)) := by
    funext e
    exact Bool.decide_congr (Int.le_sub_one_iff).symm
  show (NamedRun.stateBeforeTime S rho t v).st = (NamedRun.readAt S rho (t - 1) v).st
  unfold NamedRun.stateBeforeTime NamedRun.readAt
  rw [hfilter]


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
