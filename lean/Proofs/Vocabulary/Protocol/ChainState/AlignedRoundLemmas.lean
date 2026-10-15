module
public import Proofs.Vocabulary.Internal.Definitions.Evidence
public import Proofs.Vocabulary.Internal.Execution.Assumptions
public import Proofs.Vocabulary.Internal.Legacy.Assumptions.Weight
public import Proofs.Vocabulary.Internal.ModelVocabulary.Substrate.Weights
public import Proofs.Vocabulary.ModelProperties.HasSlashableWeightBetween
public import Proofs.Vocabulary.ModelProperties.SlashableBetween
public import Proofs.Vocabulary.ModelProperties.Slashable
import Proofs.Vocabulary.Objects.Weights
import Proofs.Vocabulary.Protocol.ChainState.Chain

@[expose] public section

/-!
# Consequences of the fault bound

Consequences of the fault bound `BelowOneThird`: an honest quorum and an honest-weight majority, no
faulty set carrying the intersection weight of two quorums, an honest member in every quorum, and
`SlashableBound` under `NoSelfSlashing` and `CarriedByHonest`. Also the step from compatibility and
a depth bound to ancestry.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace AlignedRoundLemmas

open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The fault bound and its consequences -/

/-- The quorum threshold is at least two thirds: `2W ≤ 3q`. -/
theorem two_mul_W_le_three_mul_q (E : Env V) : 2 * E.W ≤ 3 * E.q := by
  unfold Env.q Env.W Electorate.finalityThreshold
  omega

/-- `BelowOneThird` implies `HonestQuorum`. -/
theorem honestQuorum_of_belowOneThird {S : Setup V} {H : Finset V}
    (h : BelowOneThird S H) : HonestQuorum S H := by
  have hsum := S.E.electorate.weightOf_add_weightOf_sdiff H
  unfold BelowOneThird at h
  unfold HonestQuorum
  unfold Env.q Env.W Electorate.finalityThreshold at *
  omega

/-- `BelowOneThird` implies `HonestWeightMajority`. -/
theorem honestWeightMajority_of_belowOneThird
    {S : Setup V} {H : Finset V}
    (h : BelowOneThird S H) : HonestWeightMajority S H := by
  have hsum := S.E.electorate.weightOf_add_weightOf_sdiff H
  unfold BelowOneThird at h
  unfold HonestWeightMajority
  unfold Env.W at h
  omega

/-- A set with no member in `H` weighs at most the complement of `H`. -/
theorem weight_le_faulty_of_subset {S : Setup V} {H X : Finset V}
    (hX : ∀ i ∈ X, i ∉ H) :
    S.E.electorate.weightOf X ≤ S.E.electorate.weightOf (Finset.univ \ H) :=
  S.E.electorate.weightOf_mono (fun i hi =>
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hX i hi⟩)

/-- Under `BelowOneThird S H`, no set `X` with no member in `H` carries the intersection weight of
    two quorums. -/
theorem no_faulty_intersection {S : Setup V} {H X : Finset V}
    (hbot : BelowOneThird S H) (hw : HasIntersectionWeight S.E X)
    (hX : ∀ i ∈ X, i ∉ H) : False := by
  have hle := weight_le_faulty_of_subset (S := S) hX
  have hq := two_mul_W_le_three_mul_q S.E
  unfold BelowOneThird at hbot
  unfold HasIntersectionWeight at hw
  omega


/-- Every attestation of the pool `A` whose validator is in `H` is the erasure of a row that
    validator emitted in the run `ρ`. -/
def CarriedByHonest (S : Setup V) (ρ : Run V) (H : Finset V)
    (A : Finset (CombinedAttestation V)) : Prop :=
  ∀ a ∈ A, a.val_index ∈ H →
    ∃ (row : NamedAttestation V) (t : Time),
      row.erase = a ∧ ρ.emits S a.val_index (Object.attest row) t


/-- Under `BelowOneThird S H`, every quorum has a member in `H`. -/
theorem honest_member_of_quorum {S : Setup V} {H Q : Finset V}
    (hbot : BelowOneThird S H) (hQ : S.E.electorate.IsQuorum Q) :
    ∃ i ∈ Q, i ∈ H := by
  by_contra hno
  push Not at hno
  exact no_faulty_intersection hbot
    (honest_part_of_quorum S.E hQ (honestQuorum_of_belowOneThird hbot))
    (fun i hi => hno i (Finset.mem_inter.mp hi).1)


/-! ## From the fault bound to the slashing bound -/


/-- In the run `ρ`, no two attestation rows emitted by one validator have erasures that are
    slashable together. -/
def NoSelfSlashing (S : Setup V) (ρ : Run V) : Prop :=
  ∀ (i : V) (a b : NamedAttestation V),
    (∃ t : Time, ρ.emits S i (Object.attest a) t) →
    (∃ t : Time, ρ.emits S i (Object.attest b) t) →
    Protocol.slashable a.erase b.erase = false

theorem noSlashableWeightBetween_of_belowOneThird {S : Setup V} {ρ : Run V}
    {H : Finset V} {A₁ A₂ : Finset (CombinedAttestation V)}
    (hbot : BelowOneThird S H) (hself : NoSelfSlashing S ρ)
    (h₁ : CarriedByHonest S ρ H A₁) (h₂ : CarriedByHonest S ρ H A₂) :
    ¬ HasSlashableWeightBetween S.E A₁ A₂ := by
  intro hS
  obtain ⟨X, hw, hX⟩ := ModelProperties.hasSlashableWeightBetween_elim hS
  refine no_faulty_intersection hbot hw ?_
  intro i hi hiH
  obtain ⟨a, ha, b, hb, hav, hbv, hsl⟩ := ModelProperties.slashableBetween_elim (hX i hi)
  obtain ⟨ra, ta, hra, hea⟩ := h₁ a ha (by rw [hav]; exact hiH)
  obtain ⟨rb, tb, hrb, heb⟩ := h₂ b hb (by rw [hbv]; exact hiH)
  have hsafe := hself i ra rb ⟨ta, hav ▸ hea⟩ ⟨tb, hbv ▸ heb⟩
  rw [hra, hrb] at hsafe
  have hsl' : Protocol.slashable a b = true := ModelProperties.Slashable_iff.mp hsl
  rw [hsafe] at hsl'
  simp at hsl'

/-- `BelowOneThird` on the run's honest set, `NoSelfSlashing`, and the chain attestations of every
    run block being `CarriedByHonest`, together give `SlashableBound`. -/
theorem slashableBound_of_belowOneThird {S : Setup V} {ρ : Run V}
    (hbot : BelowOneThird S ρ.honest) (hself : NoSelfSlashing S ρ)
    (hcar : ∀ B : NamedBlock V, RunBlock S ρ B →
      CarriedByHonest S ρ ρ.honest (chain_attestations B.erase)) :
    SlashableBound S ρ :=
  fun _ _ hB₁ hB₂ =>
    noSlashableWeightBetween_of_belowOneThird hbot hself (hcar _ hB₁) (hcar _ hB₂)


/-! ## Compatibility and a depth bound give ancestry -/

omit [Fintype V] in
/-- If `B` and `C` are compatible and `B`'s depth is at most `C`'s, then `B ⪯ C`. -/
theorem preceq_of_compatible_of_depth_le {B C : Block V}
    (hcmp : Block.compatible B C = true) (hd : B.depth ≤ C.depth) :
    Block.Preceq B C := by
  simp only [Block.compatible, Bool.or_eq_true] at hcmp
  rcases hcmp with h | h
  · exact h
  · have hCB : C = B := Block.preceq_eq_of_depth_le h hd
    subst hCB
    exact Block.preceq_self _


end AlignedRoundLemmas
end Proofs
end DecoupledConsensusModel

end
