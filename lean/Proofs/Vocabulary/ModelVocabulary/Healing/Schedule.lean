module
public import Proofs.Vocabulary.ModelVocabulary.Goldfish.Objects
public import Model.Vocabulary.Protocol.Grades

@[expose] public section

/-!
# The grade cutoffs of a healing round

The grade cutoffs `Γ_neg1`, `Γ_0`, `Γ_1` and `Γ_2` around round `r`'s opening slot, and the
identities placing them and the action time `a_r` on the slot schedule.
-/

namespace DecoupledConsensusModel
namespace Protocol

/-- `R ≥ 2`, from `R ≥ 3`. -/
theorem HealConfig.R_ge_two (hc : HealConfig) : 2 ≤ hc.R :=
  le_trans (by decide) hc.R_ge_three

namespace HealConfig

variable (hc : HealConfig)

/-- `Γ_r^{−1} = t_{rR} − Δ`, the earliest grade cutoff, one delay before the start of round `r`'s
    opening slot. -/
def Γ_neg1 (Δ : Time) (r : Round) : Time :=
  slotStart Δ (hc.opening_slot r) - Δ

/-- `Γ_r^0 = t_{rR}`, the proposal time of round `r`'s opening slot. -/
def Γ_0 (Δ : Time) (r : Round) : Time :=
  slotStart Δ (hc.opening_slot r)

/-- `Γ_r^1 = t_{rR} + Δ`, the Goldfish vote time of round `r`'s opening slot. -/
def Γ_1 (Δ : Time) (r : Round) : Time :=
  slotStart Δ (hc.opening_slot r) + Δ

/-- `Γ_r^2 = t_{rR} + 2Δ`, the support cutoff of round `r`'s opening slot. -/
def Γ_2 (Δ : Time) (r : Round) : Time :=
  slotStart Δ (hc.opening_slot r) + 2 * Δ

end HealConfig

section Alignment

variable {V : Type} [DecidableEq V] [Fintype V]

/-- `Γ_r^0` is the proposal time of round `r`'s opening slot. -/
theorem Γ_0_eq_proposal_time (hc : HealConfig) (E : Env V) (r : Round) :
    hc.Γ_0 E.Δ r = Protocol.proposal_time E (hc.opening_slot r) := rfl

/-- `Γ_r^1` is the Goldfish vote time of round `r`'s opening slot. -/
theorem Γ_1_eq_vote_time (hc : HealConfig) (E : Env V) (r : Round) :
    hc.Γ_1 E.Δ r = Protocol.vote_time E (hc.opening_slot r) := rfl

/-- The action time `a_r` is the confirmation time of round `r`'s opening slot. -/
theorem a_eq_confirmation_time (hc : HealConfig) (E : Env V) (r : Round) :
    hc.a E.Δ r = Protocol.confirmation_time E (hc.opening_slot r) := rfl

/-- The action time `a_r` is the support cutoff of the slot after round `r`'s opening slot,
    `t_{rR+1} + 2Δ`. -/
theorem a_eq_support_cutoff_succ (hc : HealConfig) (E : Env V) (r : Round) :
    hc.a E.Δ r = Protocol.support_cutoff E (hc.opening_slot r + 1) :=
  Protocol.confirmation_time_eq_support_cutoff_succ E (hc.opening_slot r)

end Alignment

end Protocol
end DecoupledConsensusModel

end
