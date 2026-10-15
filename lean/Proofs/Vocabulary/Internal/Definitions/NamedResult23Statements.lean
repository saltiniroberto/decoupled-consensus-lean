module
public import Proofs.Vocabulary.Internal.Legacy.Definitions.NamedDutyReads
public import Proofs.Vocabulary.Internal.ModelVocabulary.Substrate.NamedBlocks
public import Model.Vocabulary.Statements.Instantiation.Certificates


@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

namespace DecoupledConsensusModel
namespace Internal

open Execution NamedRecoveryRead Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The named confirmation anchor -/

/-- The SG root of a prepared read, under the contract of that read's own cache. -/
def namedConfirmationAnchor (S : Setup V) (n : NamedNodeState V) : Block V :=
  Protocol.get_sg_root_with (NamedProfile.gradeContract n.cache) S.E S.hc
    n.st.core.toHealing (S.hc.round_of n.st.core.s)

/-- The confirmation anchor of `v`'s slot-`s` confirmation input read. -/
def confirmationAnchorAt (S : Setup V) (ρ : Run V) (v : V) (s : Slot) : Block V :=
  namedConfirmationAnchor S (confirmationInputRead S ρ v s)


end Internal
end DecoupledConsensusModel

end
