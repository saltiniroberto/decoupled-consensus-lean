module
public import Proofs.Vocabulary.Execution.Wire
public import Proofs.Vocabulary.Internal.Definitions.Evidence
public import Model.Vocabulary.Protocol.Evidence
import Proofs.Vocabulary.Protocol.ChainState.Chain

@[expose] public section


namespace DecoupledConsensusModel
namespace Protocol

open Protocol (ChainState HeightConfig)
open Protocol (HealConfig)
open Internal
open DecoupledConsensusModel.Execution

/-! ## Symmetry and monotonicity -/

section Symmetry

variable {V : Type} [DecidableEq V]

/-- Compatibility is symmetric. -/
theorem compatible_comm {B C : Block V} (h : Block.compatible B C = true) :
    Block.compatible C B = true := by
  simp only [Block.compatible, Bool.or_eq_true] at h ⊢
  exact h.symm

/-- Root injectivity on a set holds on every subset. -/
theorem RootInjectiveBelow.mono {S S' : Finset (Block V)}
    (h : Execution.RootInjectiveBelow S')
    (hs : S ⊆ S') : Execution.RootInjectiveBelow S := by
  intro A C hA hC hr
  obtain ⟨B, hB, hAB⟩ := hA
  obtain ⟨B', hB', hCB'⟩ := hC
  exact h A C ⟨B, hs hB, hAB⟩ ⟨B', hs hB', hCB'⟩ hr

variable [Fintype V]

/-- Slashable weight between two pools persists when the pools grow. -/
theorem hasSlashableWeightBetween_mono {E : Env V}
    {A₁ A₂ A₁' A₂' : Finset (CombinedAttestation V)}
    (h : HasSlashableWeightBetween E A₁ A₂) (h₁ : A₁ ⊆ A₁') (h₂ : A₂ ⊆ A₂') :
    HasSlashableWeightBetween E A₁' A₂' := by
  obtain ⟨S, hw, hev⟩ := h
  refine ⟨S, hw, fun i hi => ?_⟩
  obtain ⟨a, ha, b, hb, hav, hbv, hs⟩ := hev i hi
  exact ⟨a, h₁ ha, b, h₂ hb, hav, hbv, hs⟩

end Symmetry

/-! ## Named rows as evidence of the erased block -/

section NamedCrosswalk

variable {V : Type} [DecidableEq V]

/-- An attestation of a named ancestor of `tip` erases to an attestation in the chain attestations
    of `tip.erase`. -/
theorem named_row_erase_mem {tip carrier : NamedBlock V} {a : NamedAttestation V}
    (hc : NamedBlock.Preceq carrier tip) (ha : a ∈ carrier.attestations) :
    a.erase ∈ chain_attestations tip.erase := by
  refine chain_attestations_mono (Proofs.NamedWire.erase_preceq hc) ?_
  cases carrier with
  | genesis => simp only [NamedBlock.attestations, List.not_mem_nil] at ha
  | node p s r votes support rows proposer =>
    exact mem_chain_attestations_of_mem (List.mem_map.mpr ⟨a, ha, rfl⟩)

omit [DecidableEq V] in
/-- A named row whose height pair matches the entry `X` at height `h` erases to a row that conflicts
    with the finality pair `(h, T)` for every root `T ≠ X`. -/
theorem conflictsWithFinality_erase_of_matchesEntry {a : NamedAttestation V}
    {h : Height} {X T : BlockId} (hm : a.height_pair.matchesEntry h X = true)
    (hne : X ≠ T) :
    Protocol.conflictsWithFinality a.erase.height_pair ⟨h, T⟩ = true := by
  have hbe : a.erase.height_pair = a.height_pair.erase := rfl
  rw [hbe]
  cases hp : a.height_pair with
  | empty =>
    rw [hp] at hm
    simp only [NamedHeightPair.matchesEntry] at hm
    exact absurd hm Bool.false_ne_true
  | vote height entry timeout =>
    rw [hp] at hm
    simp only [NamedHeightPair.matchesEntry, decide_eq_true_eq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    cases timeout <;>
      simp [NamedHeightPair.erase, Protocol.conflictsWithFinality, hne]

end NamedCrosswalk


/-! ## A block's evidence is in the store's -/

section HealingStore

variable {V : Type} [DecidableEq V] [Fintype V]


/-- The chain attestations of a block of the store's tree are among the store's attestations. -/
theorem chain_attestations_subset_store {W : Type} [DecidableEq W]
    {st : Protocol.Store W} {B : Block W} (hB : B ∈ st.T) :
    chain_attestations B ⊆ store_attestations st :=
  Finset.subset_biUnion_of_mem chain_attestations hB


end HealingStore


end Protocol
end DecoupledConsensusModel

end
