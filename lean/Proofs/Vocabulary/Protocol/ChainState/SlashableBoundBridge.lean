module
public import Proofs.Vocabulary.Protocol.ValidatorClient.SlashableBound
public import Proofs.Vocabulary.Protocol.Handlers.StoreBridge
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section

/-!
# The slashable bound from the fault bound

On a core execution, `NoSelfSlashing` holds, and `BelowOneThird` implies `SlashableBound`.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Every run with `AdmissibleCore` satisfies `NoSelfSlashing`. -/
theorem noSelfSlashing_of_admissibleCore (S : Setup V) {rho : Run V}
    (adm : AdmissibleCore S rho) : AlignedRoundLemmas.NoSelfSlashing S rho := by
  intro v a b ha hb
  obtain ⟨ta, ha⟩ := ha
  obtain ⟨tb, hb⟩ := hb
  have he1 : Protocol.e1Fields a.erase b.erase = false := by
    cases hfa : a.erase.finality_pair with
    | none =>
        cases hfb : b.erase.finality_pair with
        | none => simp [Protocol.e1Fields, hfa, hfb]
        | some p =>
            have hconf := conflictsWithFinality_false_of_admissibleCore S adm hb ha hfb
            simp [Protocol.e1Fields, hfa, hfb, hconf]
    | some p =>
        have hconfA := conflictsWithFinality_false_of_admissibleCore S adm ha hb hfa
        cases hfb : b.erase.finality_pair with
        | none => simp [Protocol.e1Fields, hfa, hfb, hconfA]
        | some q =>
            have hconfB := conflictsWithFinality_false_of_admissibleCore S adm hb ha hfb
            simp [Protocol.e1Fields, hfa, hfb, hconfA, hconfB]
  have he2 := e2Fields_false_of_admissibleCore S adm ha hb
  simp [Protocol.slashable, Protocol.e1Slashable,
    Protocol.e2Slashable, he1, he2]

/-- On a run with `AdmissibleCore`, `BelowOneThird` implies `SlashableBound`. -/
theorem slashableBound_of_admissibleCore_belowOneThird (S : Setup V)
    {rho : Run V} (adm : AdmissibleCore S rho)
    (hbot : BelowOneThird S rho.honest) : SlashableBound S rho :=
  AlignedRoundLemmas.slashableBound_of_belowOneThird hbot
    (noSelfSlashing_of_admissibleCore S adm)
    (fun _ hB => Proofs.NamedStoreBridge.carriedByHonest_of_runBlock S adm hB)


/-- On an admissible run, `BelowOneThird` implies `SlashableBound`. -/
theorem slashableBound_of_admissible_belowOneThird (S : Setup V)
    {rho : Run V} (adm : Admissible S rho)
    (hbot : BelowOneThird S rho.honest) : SlashableBound S rho :=
  slashableBound_of_admissibleCore_belowOneThird S adm.toNamedAdmissibleCore hbot

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
