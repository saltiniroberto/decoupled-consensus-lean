import Proofs.Vocabulary.ModelVocabulary.Healing.Schedule
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Record.Wiring

/-!
# Healing schedule times

The grade cutoff times of a round's healing schedule, over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol.HealConfig

/-- `Γ_r^{−1}`, the start of round `r`'s opening slot minus `Δ`: the earliest grade cutoff. -/
def Vocabulary.Protocol.HealConfig.Γ_neg1 (M : Record.Model V) (hc : HealConfig) (Δ : Time) (r : Round) : Time :=
  slotStart Δ ((M.opening_slot hc r)) - Δ

end

section
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol.HealConfig

/-- `Γ_r^0`, the start of round `r`'s opening slot. -/
def Vocabulary.Protocol.HealConfig.Γ_0 (M : Record.Model V) (hc : HealConfig) (Δ : Time) (r : Round) : Time :=
  slotStart Δ ((M.opening_slot hc r))

end

section
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol.HealConfig

/-- `Γ_r^1`, the start of round `r`'s opening slot plus `Δ`. -/
def Vocabulary.Protocol.HealConfig.Γ_1 (M : Record.Model V) (hc : HealConfig) (Δ : Time) (r : Round) : Time :=
  slotStart Δ ((M.opening_slot hc r)) + Δ

end

section
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol.HealConfig

/-- `Γ_r^2`, the start of round `r`'s opening slot plus `2Δ`. -/
def Vocabulary.Protocol.HealConfig.Γ_2 (M : Record.Model V) (hc : HealConfig) (Δ : Time) (r : Round) : Time :=
  slotStart Δ ((M.opening_slot hc r)) + 2 * Δ

end

section
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol.HealConfig

/-- `DecoupledConsensusModel.Protocol.HealConfig.Γ_neg1` equals
    `Restated.Vocabulary.Protocol.HealConfig.Γ_neg1` at the model `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.HealConfig.Γ_neg1_vocabulary_eq (hc : HealConfig) (Δ : Time) (r : Round) :
    _root_.DecoupledConsensusModel.Protocol.HealConfig.Γ_neg1 hc Δ r = Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 (V := V) Record.Model.vocabulary hc Δ r :=
  rfl

/-- `DecoupledConsensusModel.Protocol.HealConfig.Γ_0` equals
    `Restated.Vocabulary.Protocol.HealConfig.Γ_0` at the model `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.HealConfig.Γ_0_vocabulary_eq (hc : HealConfig) (Δ : Time) (r : Round) :
    _root_.DecoupledConsensusModel.Protocol.HealConfig.Γ_0 hc Δ r = Restated.Vocabulary.Protocol.HealConfig.Γ_0 (V := V) Record.Model.vocabulary hc Δ r :=
  rfl

/-- `DecoupledConsensusModel.Protocol.HealConfig.Γ_1` equals
    `Restated.Vocabulary.Protocol.HealConfig.Γ_1` at the model `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.HealConfig.Γ_1_vocabulary_eq (hc : HealConfig) (Δ : Time) (r : Round) :
    _root_.DecoupledConsensusModel.Protocol.HealConfig.Γ_1 hc Δ r = Restated.Vocabulary.Protocol.HealConfig.Γ_1 (V := V) Record.Model.vocabulary hc Δ r :=
  rfl

/-- `DecoupledConsensusModel.Protocol.HealConfig.Γ_2` equals
    `Restated.Vocabulary.Protocol.HealConfig.Γ_2` at the model `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.HealConfig.Γ_2_vocabulary_eq (hc : HealConfig) (Δ : Time) (r : Round) :
    _root_.DecoupledConsensusModel.Protocol.HealConfig.Γ_2 hc Δ r = Restated.Vocabulary.Protocol.HealConfig.Γ_2 (V := V) Record.Model.vocabulary hc Δ r :=
  rfl

end

end DecoupledConsensusModel.Sts.Restated
