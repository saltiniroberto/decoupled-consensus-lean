module
public import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.NamedAdmissible

@[expose] public section

/-!
# Execution premises

Schedule well-formedness, execution validity, partial synchrony, and the full-participation premise
`Admissible`.
-/
namespace DecoupledConsensusModel.Execution
variable {V : Type} [DecidableEq V] [Fintype V]

abbrev ScheduleWellFormed (S : Setup V) (rho : Run V) : Prop := NamedScheduleWellFormed S rho
abbrev RootCollisionFree (S : Setup V) (rho : Run V) : Prop := NamedRootCollisionFree S rho
/-- The four execution-validity families: schedule well-formedness, delivery well-formedness,
    run-scoped root-collision freedom and authenticity. It holds no synchrony premise. -/
structure ExecutionValid (S : Setup V) (rho : Run V) : Prop extends
  NamedScheduleWellFormed S rho, NamedDeliveryWellFormed S rho,
  NamedRootCollisionFree S rho,
  NamedUnforgeable S rho

/-- The partial-synchrony network premise, kept separate from execution validity. -/
abbrev PartialSynchrony (S : Setup V) (rho : Run V) : Prop := NamedSynchrony S rho

namespace ScheduleWellFormed
abbrev sorted {S : Setup V} {rho : Run V} (h : ScheduleWellFormed S rho) :=
  NamedScheduleWellFormed.sorted h
abbrev in_horizon {S : Setup V} {rho : Run V} (h : ScheduleWellFormed S rho) :=
  NamedScheduleWellFormed.in_horizon h
end ScheduleWellFormed
namespace DeliveryWellFormed
end DeliveryWellFormed
namespace RootCollisionFree
abbrev root_injective := @NamedRootCollisionFree.root_injective
end RootCollisionFree
namespace Unforgeable
end Unforgeable
namespace Synchrony
end Synchrony
namespace ExecutionValid
end ExecutionValid
namespace PartialSynchrony
end PartialSynchrony
namespace AdmissibleCore
end AdmissibleCore

/-- Execution validity, partial synchrony, and every honest validator awake at every round whose
    action time is from GST to the horizon. -/
structure Admissible (S : Setup V) (rho : Run V) : Prop extends
    ExecutionValid S rho, PartialSynchrony S rho where
  all_awake : ∀ v ∈ rho.honest, ∀ r : Round, S.E.t_GST ≤ S.a r → S.a r ≤ rho.horizon →
    (S.node v).awake r = true

end DecoupledConsensusModel.Execution

end
