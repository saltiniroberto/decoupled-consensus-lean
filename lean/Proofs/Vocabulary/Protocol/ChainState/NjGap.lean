module
public import Proofs.Vocabulary.Protocol.ChainState.Chain
import Proofs.Vocabulary.ModelVocabulary.FinalityGadget.ChainState
import Mathlib.Data.Nat.SuccPred

@[expose] public section

/-!
# Recovery-height arithmetic

The `nj` invariant `NjEntry` of a chain state, and the recovery heights `RecoveryHeight`, at which a
chain whose finalized height stays at most the baseline is nonjustifiable.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace NjGap

open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Arithmetic over `Nat` -/

private theorem lt_of_lt_sub {D cap H : Nat} (hD : 1 ≤ D) (h : D < H - cap) :
    cap + 1 < H := by omega


private theorem lt_sub_of_le {D h a b : Nat} (hle : a ≤ b) (h2 : D < h - b) :
    D < h - a := by omega


/-! ## `nj` is the entry formula -/

section Bookkeeping

variable {σ : ChainState V} {a : CombinedAttestation V}

omit [Fintype V] in

/-- `process_attestation` keeps `nj`. -/
theorem process_attestation_nj (σ : ChainState V) (a : CombinedAttestation V) :
    (Protocol.process_attestation σ a).nj = σ.nj := by
  unfold Protocol.process_attestation
  split_ifs <;> rfl


end Bookkeeping

section Entry

variable {cfg : HeightConfig}

omit [Fintype V] [DecidableEq V] in
/-- `nonjustifiable` is antitone in the finalized height: if it holds at `cap`, it holds at every
    `h_F ≤ cap`. -/
theorem nonjustifiable_of_le {h h_F cap : Height} (hle : h_F ≤ cap)
    (hnj : Protocol.nonjustifiable cfg h cap = true) :
    Protocol.nonjustifiable cfg h h_F = true := by
  simp only [Protocol.nonjustifiable, Bool.and_eq_true, decide_eq_true_eq] at hnj ⊢
  exact ⟨hnj.1, lt_sub_of_le hle hnj.2⟩

omit [Fintype V] [DecidableEq V] in
/-- `K ∣ h` and `D < h − h_F` give `nonjustifiable cfg h h_F`. -/
theorem nonjustifiable_of {h h_F : Height} (hdvd : cfg.K ∣ h) (hdebt : cfg.D < h - h_F) :
    Protocol.nonjustifiable cfg h h_F = true := by
  simp only [Protocol.nonjustifiable, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hdvd, hdebt⟩

/-- A chain state's `nj` bit is the `nonjustifiable` formula at its own height, evaluated at some
    finalized height at most its `h_F`. -/
def NjEntry (cfg : HeightConfig) (σ : ChainState V) : Prop :=
  ∃ h_F' : Height, h_F' ≤ σ.h_F ∧ σ.nj = Protocol.nonjustifiable cfg σ.h h_F'

omit [Fintype V] [DecidableEq V] in
/-- The initial chain state satisfies `NjEntry`. -/
theorem njEntry_initial (cfg : HeightConfig) :
    NjEntry cfg (ChainState.initial : ChainState V) := by
  refine ⟨0, Nat.le_refl 0, ?_⟩
  have hK : ¬ cfg.K ∣ 1 := by
    intro h
    have h1 := Nat.le_of_dvd Nat.one_pos h
    have h2 := cfg.K_ge_two
    omega
  simp [Protocol.nonjustifiable, ChainState.initial, hK]

variable (E : Env V)

/-- The finality branch `afterFin` never lowers `h_F`. -/
theorem le_afterFin_h_F (σ : ChainState V) : σ.h_F ≤ (Protocol.afterFin E σ).h_F := by
  rw [Protocol.afterFin_h_F]
  split_ifs with h
  · exact Nat.le_of_lt (Protocol.lt_of_finalityReady E h)
  · exact Nat.le_refl _


end Entry

/-! ## Uniform `nj` at a recovery height -/

section Uniform

variable (E : Env V) (cfg : HeightConfig)

/-- `H` is a recovery height for the baseline `h_F0`: `K ∣ H` and `D < H − h_F0`. -/
def RecoveryHeight (cfg : HeightConfig) (h_F0 H : Height) : Prop :=
  cfg.K ∣ H ∧ cfg.D < H - h_F0


omit [Fintype V] [DecidableEq V] in
/-- A recovery height `H` for the baseline `h_F0` satisfies `h_F0 + 1 < H`. -/
theorem lt_of_recoveryHeight {cfg : HeightConfig} {h_F0 H : Height}
    (h : RecoveryHeight cfg h_F0 H) : h_F0 + 1 < H :=
  lt_of_lt_sub cfg.D_ge_one h.2


end Uniform

/-! ## No justification at a recovery height -/

section NoJustification

variable (E : Env V) (cfg : HeightConfig)

/-- A set `nj` bit makes `targetReady` false. -/
theorem targetReady_eq_false_of_nj {σ : ChainState V} (h : σ.nj = true) :
    Protocol.targetReady E σ = false := by
  simp [Protocol.targetReady, h]


end NoJustification


end NjGap
end Proofs
end DecoupledConsensusModel

end
