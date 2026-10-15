import Proofs.Vocabulary.Internal.Definitions.NamedResult23Statements
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedDutyReads
import Model.Record.Wiring

/-!
# Confirmation anchors

The SG root of a read under its own grade contract, and the confirmation anchors of a validator's
confirmation input reads, stated over a model `M : Record.Model V`, and their counterparts at
`Record.Model.vocabulary`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Statements.Instantiation
open Execution NamedRecoveryRead Protocol

/-- The outcomes of the SG root read of `n`'s core store at the round of its slot, under the grade
    contract of `n`'s cache. -/
def Vocabulary.Internal.namedConfirmationAnchor (M : Record.Model V) (S : Setup V) (n : M.N) : DC.NDRE (Block V) :=
  M.get_sg_root_with (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc n.st.core.s)

end

section
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Statements.Instantiation
open Execution NamedRecoveryRead Protocol

/-- The set of blocks `B` such that, for some confirmation input read `n` of `v` at slot `s`, the
    confirmation anchor of `n` can return `B`. -/
def Vocabulary.Internal.confirmationAnchorAt (M : Record.Model V) (S : Setup V) (ρ : Record.Run V) (v : V) (s : Slot) : DC.NDR (Block V) :=
  { B | ∃ n ∈ Restated.Vocabulary.Internal.NamedRecoveryRead.confirmationInputRead M S ρ v s,
    Restated.Vocabulary.Internal.namedConfirmationAnchor M S n ⇢ B }

end

/-! ## Agreement at `Record.Model.vocabulary` -/

section
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Statements.Instantiation
open Execution NamedRecoveryRead Protocol

/-- At `Record.Model.vocabulary`, the restated `namedConfirmationAnchor` is the one outcome
    `DecoupledConsensusModel.Internal.namedConfirmationAnchor` computes. -/
@[record_vocabulary]
theorem Vocabulary.Internal.namedConfirmationAnchor_vocabulary_eq (S : Setup V) (n : NamedNodeState V) :
    Restated.Vocabulary.Internal.namedConfirmationAnchor (V := V) Record.Model.vocabulary S n =
      pure (_root_.DecoupledConsensusModel.Internal.namedConfirmationAnchor (V := V) S n) :=
  rfl

/-- At `Record.Model.vocabulary` and a run embedded by `Record.Run.ofVocabulary`, the restated
    `confirmationAnchorAt` is the singleton of the value of
    `DecoupledConsensusModel.Internal.confirmationAnchorAt`. -/
@[record_vocabulary]
theorem Vocabulary.Internal.confirmationAnchorAt_vocabulary_eq (S : Setup V) (ρ : Run V) (v : V) (s : Slot) :
    Restated.Vocabulary.Internal.confirmationAnchorAt (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary ρ) v s =
      {_root_.DecoupledConsensusModel.Internal.confirmationAnchorAt (V := V) S ρ v s} := by
  rw [Restated.Vocabulary.Internal.confirmationAnchorAt,
    Vocabulary.Internal.NamedRecoveryRead.confirmationInputRead_vocabulary_eq]
  ext B
  constructor
  · rintro ⟨n, hn, h⟩
    have hn' : n = _ := hn
    subst hn'
    rw [Vocabulary.Internal.namedConfirmationAnchor_vocabulary_eq] at h
    exact (Record.returns_pure _ _).1 h
  · intro h
    rw [Set.mem_singleton_iff] at h
    subst h
    refine ⟨_, rfl, ?_⟩
    rw [Vocabulary.Internal.namedConfirmationAnchor_vocabulary_eq]
    exact (Record.returns_pure _ _).2 rfl

end

end DecoupledConsensusModel.Sts.Restated
