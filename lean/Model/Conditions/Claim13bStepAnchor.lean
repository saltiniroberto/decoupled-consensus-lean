import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Claim13bK_FreshAttestersW
import Model.Conditions.Claim13bStepKitTick
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bStepAnchor

/-!
# The anchor of the next round

The new anchor `newAnchor` of round `r + 1`, with its height and its specification, read from the
round-`(r + 1)` action attestations of the honest active attesters, stated over a model
`M : Record.Model V`.
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

/-- For every member `q` of `freshAttestersW` for round `r + 1` at step `n' + 1`, `att q` is an
    attestation `q`'s round-`(r + 1)` action duty can compute from `q`'s node state at step `n'`. -/
def ActionAttestationsOf (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (r : Round) (n' : Nat)
    (att : V → NamedAttestation V) : Prop :=
  ∀ q ∈ Restated.freshAttestersW M S Sched x (r + 1) (n' + 1),
    att q ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n'][q].st) q (r + 1)

/-- The heights of the non-empty height votes `att q` of the members `q` of `freshAttestersW` for
    round `r + 1` at step `n' + 1`. -/
noncomputable def freshVoteHeights (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (r : Round) (n' : Nat)
    (att : V → NamedAttestation V) : Finset Height :=
  (Restated.freshAttestersW M S Sched x (r + 1) (n' + 1)).biUnion fun q =>
    match (att q).height_pair with
    | NamedHeightPair.vote h₀ _ _ => {h₀}
    | NamedHeightPair.empty => ∅

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The larger of `h` and the largest height in `freshVoteHeights` along `att`. -/
noncomputable def newAnchorHeight (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (r : Round) (n' : Nat)
    (att : V → NamedAttestation V) (h : Height) : Height :=
  max h ((Restated.freshVoteHeights M S Sched x r n' att).sup id)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Some member of `freshAttestersW` for round `r + 1` holds `C` at step `n'`; `C`'s chain state
    stands at the new anchor's height read from `att`; `C`'s own replay names it as that height's
    entry; and some member `q` of the same set holds `C` at step `n'` and has in `att q` a height
    vote whose root is `C`'s root. -/
def NewAnchorSpec (M : Record.Model V) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (r : Round) (n' : Nat) (att : V → NamedAttestation V) (T : NamedBlock V) (C : NamedBlock V) :
    Prop :=
  (∃ q ∈ Restated.freshAttestersW M S Sched x (r + 1) (n' + 1), C ∈ (x[n'][q].st).st.bodies) ∧
    (M.derive_named S.E S.cfg C).h
      = Restated.newAnchorHeight M S Sched x r n' att (M.derive_named S.E S.cfg T).h ∧
    (M.derive_named S.E S.cfg C).T_h = C.erase ∧
    (∃ q ∈ Restated.freshAttestersW M S Sched x (r + 1) (n' + 1), C ∈ (x[n'][q].st).st.bodies ∧
      ∃ (h₀ : Height) (tmo : Bool),
        (att q).height_pair = NamedHeightPair.vote h₀ C.root tmo)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The anchor of round `r + 1`: a block satisfying `NewAnchorSpec` along `att` when there is one,
    and `T` otherwise. -/
noncomputable def newAnchor (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (r : Round) (n' : Nat)
    (att : V → NamedAttestation V) (T : NamedBlock V) : NamedBlock V := by
  classical
  exact if h : ∃ C : NamedBlock V, Restated.NewAnchorSpec M S Sched x r n' att T C then h.choose
    else T

end

end DecoupledConsensusModel.Sts.Restated
