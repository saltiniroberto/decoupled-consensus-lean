import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bStepConeIter
import Model.Conditions.Sts_Interface
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# The round invariant with the target clause at the anchor's height

The round invariant `AfterPhaseInvariantOverActiveSetsTop` over the honest active attesters of a
round, stated over a model `M : Record.Model V`.
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

/-- The round invariant at round `r`, tick step `n` and anchor `T`, with the target clause at the
    anchor's own chain-state height. -/
structure AfterPhaseInvariantOverActiveSetsTop (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (r : Round) (n : Nat)
    (T : NamedBlock V) : Prop where
  /-- The step `n` is the framework's tick at round `r`'s action time. -/
  tick : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S r))
  /-- The anchor `T` is a block contained in some message of the sent log. -/
  inPlay : Restated.blockInLog M S Sched x T
  /-- The anchor is the entry of its own chain-state height. -/
  anchorEntry : (M.derive_named S.E S.cfg T).T_h = T.erase
  /-- The anchor's chain-state height is at least the largest `Σ.h_max` an honest active attester of
      round `r` holds at step `n`, minus one. -/
  band : Restated.hmaxRoundAt M S Sched x r n - 1 ≤ (M.derive_named S.E S.cfg T).h
  /-- Every SG block an honest active attester of round `r` attested to at round `r` lies on one
      chain with the anchor. -/
  sg : ∀ v ∈ Restated.HonRound M S Sched r, ∀ a : NamedAttestation V,
    a.round = r → a.val_index = v →
    (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n + 1].sent →
    ∀ C : NamedBlock V, C ∈ (x[n + 1][v].st).st.bodies → a.confirmed = some C.root →
    Block.compatible C.erase T.erase = true
  /-- Any two SG blocks attested to at round `r` by honest active attesters of round `r` lie on one
      chain. -/
  sgPairwise : ∀ v ∈ Restated.HonRound M S Sched r, ∀ v' ∈ Restated.HonRound M S Sched r,
    ∀ a a' : NamedAttestation V,
    a.round = r → a.val_index = v →
    (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n + 1].sent →
    a'.round = r → a'.val_index = v' →
    (⟨v', NamedObject.attest a'⟩ : SignedMsg V (NamedObject V)) ∈ x[n + 1].sent →
    ∀ C C' : NamedBlock V,
    C ∈ (x[n + 1][v].st).st.bodies → a.confirmed = some C.root →
    C' ∈ (x[n + 1][v'].st).st.bodies → a'.confirmed = some C'.root →
    Block.compatible C.erase C'.erase = true
  /-- Every honest active member of the committee of round `r`'s third slot votes there for a
      descendant of the anchor. -/
  heads : Restated.HeadsBelow M S Sched x T.erase ((M.opening_slot S.hc r) + 2)
  /-- Whatever a validator honest through step `n'` has finalized, at any step `n'` up to `n + 1`,
      is an ancestor of the anchor. -/
  fin : ∀ (v : V) (n' : Nat), n' ≤ n + 1 → Restated.HonestThrough M Sched x n' v →
    Block.Preceq (x[n'][v].st).st.core.F T.erase
  /-- Every block an honest active attester of round `r` grades at least 1 for round `r`, in some
      outcome of the grade test, at any phase whose domain time is no later than round `r`'s action
      time, lies on one chain with the anchor. -/
  grade1 : ∀ v ∈ Restated.HonRound M S Sched r,
    ∀ p : Protocol.Phase, M.domain S.E S.hc r p ≤ (Restated.Vocabulary.Execution.Setup.a M S r) →
    ∀ m : Nat, Restated.stepBeforeInstant M x m (M.domain S.E S.hc r p) →
    ∀ B : Block V, ∀ b : Bool,
    M.gradeBool S.E (M.gradeView (M.toHealing (x[m][v].st).st.core))
        (x[m][v].st).st.core.F S.hc.η_SG r (M.early S.E S.hc r p)
        (M.late S.E S.hc r p) B ⇢ b → b = true →
    Block.compatible B T.erase = true
  /-- No non-empty height vote authored and signed up to step `n + 1` by a validator honest through
      its send names a height greater than the anchor's. -/
  heightCeiling : ∀ (v : V) (n' : Nat) (a : NamedAttestation V) (h' : Height)
    (entry : BlockId) (tmo : Bool),
    n' ≤ n + 1 → Restated.HonestThrough M Sched x n' v → a.val_index = v →
    (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n'].sent →
    a.height_pair = NamedHeightPair.vote h' entry tmo →
    h' ≤ (M.derive_named S.E S.cfg T).h
  /-- Every non-empty height vote at the anchor's own chain-state height, authored and signed up to
      step `n + 1` by a validator honest through its send, names the anchor: every block in play
      whose root is the vote's entry is an ancestor of the anchor. -/
  targetsTop : ∀ (v' : V) (n' : Nat) (a : NamedAttestation V) (entry : BlockId) (tmo : Bool),
    n' ≤ n + 1 → Restated.HonestThrough M Sched x n' v' → a.val_index = v' →
    (⟨v', NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n'].sent →
    a.height_pair = NamedHeightPair.vote (M.derive_named S.E S.cfg T).h entry tmo →
    ∀ C : NamedBlock V, Restated.blockInLog M S Sched x C → C.root = entry →
    Block.Preceq C.erase T.erase

end

end DecoupledConsensusModel.Sts.Restated
