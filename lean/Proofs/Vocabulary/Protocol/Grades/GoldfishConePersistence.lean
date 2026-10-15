module
public import Proofs.Vocabulary.Generic.PostGSTCarrierAdmissionCore
public import Proofs.Vocabulary.Protocol.ForkChoice.Views.ProposalCore
public import Proofs.Vocabulary.Protocol.Schedule.GSTZeroHeadResolution
public import Proofs.Vocabulary.Protocol.Grades.ProposalLifecycleCore
import Proofs.Vocabulary.Protocol.ForkChoice.Views.VoteSetValidityCore
import Proofs.Vocabulary.Protocol.Schedule.PostHealingReuse
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section

/-!
# Goldfish cone inputs

The input structures for one step of the Goldfish cone: the facts, other than the Goldfish votes,
needed at a slot-`s + 1` vote duty and at a slot-`s` confirmation read.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.PhaseGrades
open Internal.NamedRecoveryRead
open Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Input structures -/

/-- The facts at `w`'s slot-`s + 1` vote duty, other than the Goldfish votes, that keep `C` under
    its vote head: `C` and every block strictly between the voter anchor and `C` are in the voter
    candidate tree, the FG root is an ancestor of `C`, and the anchor is compatible with `C`. -/
structure GoldfishConeVoteInputs
    (S : Setup V) (rho : Run V) (s : Slot) (C : Block V) (w : V) : Prop where
  candidate : C ∈ voterCandidateTreeAt S rho w (s + 1)
  root : Block.Preceq
    (Protocol.get_fg_root
      (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG) C
  anchor : Block.compatible
    (voterAnchorAt S rho w (s + 1)) C = true
  path : ∀ D : Block V,
    Block.Preceq (voterAnchorAt S rho w (s + 1)) D →
    D ≠ voterAnchorAt S rho w (s + 1) →
    Block.Preceq D C → D ≠ C →
    D ∈ voterCandidateTreeAt S rho w (s + 1)

/-- The facts at `w`'s slot-`s` confirmation read, other than the Goldfish votes: `C` and every
    block strictly between the confirmation anchor and `C` are in the filtered tree, the FG root is
    an ancestor of `C`, and the anchor is compatible with `C`. -/
structure GoldfishConeConfirmationInputs
    (S : Setup V) (rho : Run V) (s : Slot) (C : Block V) (w : V) : Prop where
  candidate : C ∈ filteredTree (confirmationInputRead S rho w s)
  root : Block.Preceq
    (Protocol.get_fg_root
      (confirmationInputRead S rho w s).st.core.toHealing.toFG) C
  anchor : Block.compatible
    (namedConfirmationAnchor S (confirmationInputRead S rho w s)) C = true
  path : ∀ D : Block V,
    Block.Preceq
      (namedConfirmationAnchor S (confirmationInputRead S rho w s)) D →
    D ≠ namedConfirmationAnchor S (confirmationInputRead S rho w s) →
    Block.Preceq D C → D ≠ C →
    D ∈ filteredTree (confirmationInputRead S rho w s)

/-- The facts at `w`'s slot-`s + 1` vote duty, other than the Goldfish votes: either the FG root is
    an ancestor of `C` and `C`, with every block strictly between the voter anchor and `C`, is in
    the voter candidate tree, or `C` is an ancestor of the FG root; and the anchor is compatible
    with `C`. -/
structure GoldfishConeVoteInputs'
    (S : Setup V) (rho : Run V) (s : Slot) (C : Block V) (w : V) : Prop where
  rootSide :
    (Block.Preceq
        (Protocol.get_fg_root
          (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG) C ∧
      C ∈ voterCandidateTreeAt S rho w (s + 1) ∧
      ∀ D : Block V,
        Block.Preceq (voterAnchorAt S rho w (s + 1)) D →
        D ≠ voterAnchorAt S rho w (s + 1) →
        Block.Preceq D C → D ≠ C →
        D ∈ voterCandidateTreeAt S rho w (s + 1)) ∨
    Block.Preceq C
      (Protocol.get_fg_root
        (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG)
  anchor : Block.compatible
    (voterAnchorAt S rho w (s + 1)) C = true


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
