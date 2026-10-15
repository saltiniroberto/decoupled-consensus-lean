module
public import Proofs.Vocabulary.Protocol.Handlers.FinalizationBridge
public import Proofs.Vocabulary.Protocol.Handlers.JustificationCarrier
public import Proofs.Vocabulary.Execution.OutageProvenance
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section


namespace DecoupledConsensusModel
namespace Proofs
namespace Bridges

open Internal Execution Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The finalized block -/

/-- The finalized block of `v`'s store before `t` is the derived finalized block of a body `D` of
    that store, and `D`'s derived `h_F` is less than the store's `h_max`. -/
theorem storeFinalizationOnChain_stateBeforeTime (S : Setup V) (rho : NamedRun V)
    (t : Time) (v : V) :
    ∃ D : NamedBlock V, D ∈ (NamedRun.stateBeforeTime S rho t v).st.bodies ∧
      (derive_named S.E S.cfg D).F = (NamedRun.stateBeforeTime S rho t v).st.core.F ∧
      (derive_named S.E S.cfg D).h_F < (NamedRun.stateBeforeTime S rho t v).st.core.h_max :=
  NamedFinalizationBridge.finalization_carrier_stateBeforeTime S rho t v

/-- The finalized block of `v`'s store before event index `i` is the derived finalized block of a
    body `D` of that store, and `D`'s derived `h_F` is less than the store's `h_max`. -/
theorem storeFinalizationOnChain_stateBefore (S : Setup V) (rho : NamedRun V)
    (i : Nat) (v : V) :
    ∃ D : NamedBlock V, D ∈ (NamedRun.stateBefore S rho i v).st.bodies ∧
      (derive_named S.E S.cfg D).F = (NamedRun.stateBefore S rho i v).st.core.F ∧
      (derive_named S.E S.cfg D).h_F < (NamedRun.stateBefore S rho i v).st.core.h_max :=
  NamedFinalizationBridge.finalization_carrier_stateBefore S rho i v

/-! ## The justified block -/


/-- Some body `D` of the store has derived justified block and justification height equal to the
    store's `J` and `h_j`. -/
def NamedStoreJustificationOnChain (S : Setup V) (st : Protocol.NamedStore V) : Prop :=
  ∃ D ∈ st.bodies, (derive_named S.E S.cfg D).J = st.core.J ∧
    (derive_named S.E S.cfg D).h_j = st.core.h_j


/-- `v`'s store before `t` satisfies `NamedStoreJustificationOnChain`. -/
theorem storeJustificationOnChain_stateBeforeTime (S : Setup V) (rho : NamedRun V)
    (t : Time) (v : V) :
    NamedStoreJustificationOnChain S (NamedRun.stateBeforeTime S rho t v).st :=
  NamedJustificationCarrier.justification_carrier_stateBeforeTime S rho t v


/-- `v`'s store before event index `i` satisfies `NamedStoreJustificationOnChain`. -/
theorem storeJustificationOnChain_stateBefore (S : Setup V) (rho : NamedRun V)
    (i : Nat) (v : V) :
    NamedStoreJustificationOnChain S (NamedRun.stateBefore S rho i v).st :=
  NamedJustificationCarrier.justification_carrier_stateBefore S rho i v


/-- Some body of the store has derived finalized block the store's `F` with derived `h_F` less than
    the store's `h_max`, and the store satisfies `NamedStoreJustificationOnChain`. -/
def NamedProvenance (S : Setup V) (st : Protocol.NamedStore V) : Prop :=
  (∃ D ∈ st.bodies, (derive_named S.E S.cfg D).F = st.core.F ∧
      (derive_named S.E S.cfg D).h_F < st.core.h_max) ∧
    NamedStoreJustificationOnChain S st


theorem namedProvenance_stateBefore (S : Setup V) (rho : NamedRun V) (i : Nat) (v : V) :
    NamedProvenance S (NamedRun.stateBefore S rho i v).st :=
  ⟨NamedFinalizationBridge.finalization_carrier_stateBefore S rho i v,
    storeJustificationOnChain_stateBefore S rho i v⟩


/-! ## Honest rows in a processed block were emitted earlier -/

/-- Under `NamedUnforgeable`, an honest attestation `a` of a block processed at time `t` was emitted
    by its validator at its round's action time, which is at most `t`. -/
theorem carriedArePastEmissions_of_processes (S : Setup V) (rho : NamedRun V)
    (auth : NamedUnforgeable S rho)
    {receiver : V} {B : NamedBlock V} {a : NamedAttestation V} {t : Time}
    (hB : NamedRun.processes S rho receiver (.block B) t)
    (ha : a ∈ B.attestations) (hHon : a.val_index ∈ rho.honest) :
    S.a a.round ≤ t ∧ NamedRun.emits S rho a.val_index (.attest a) (S.a a.round) :=
  NamedOutageProvenance.honest_carried_row_emission S rho auth hB ha hHon


/-! ## Rows of an ancestor, erased -/

/-- The erasure of an attestation of a named ancestor of `D` is in the chain attestations of
    `D.erase`. -/
theorem erase_mem_chain_attestations (D : NamedBlock V) :
    ∀ carrier : NamedBlock V, NamedBlock.Preceq carrier D →
      ∀ a : NamedAttestation V, a ∈ carrier.attestations →
        a.erase ∈ chain_attestations D.erase := by
  induction D with
  | genesis =>
    intro carrier hc a ha
    simp only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] at hc
    subst hc
    simp only [NamedBlock.attestations, List.not_mem_nil] at ha
  | node p sl r gv sup rows pr ih =>
    intro carrier hc a ha
    simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
      decide_eq_true_eq] at hc
    show a.erase ∈ chain_attestations
      (Block.node p.erase sl r gv sup (rows.map NamedAttestation.erase) pr)
    simp only [chain_attestations, Finset.mem_union]
    rcases hc with rfl | hcp
    · exact Or.inl (List.mem_toFinset.mpr
        (List.mem_map.mpr ⟨a, by simpa only [NamedBlock.attestations] using ha, rfl⟩))
    · exact Or.inr (ih carrier hcp a ha)

#print axioms erase_mem_chain_attestations

#print axioms storeFinalizationOnChain_stateBeforeTime
#print axioms storeFinalizationOnChain_stateBefore
#print axioms storeJustificationOnChain_stateBeforeTime
#print axioms storeJustificationOnChain_stateBefore
#print axioms namedProvenance_stateBefore
#print axioms carriedArePastEmissions_of_processes

end Bridges
end Proofs
end DecoupledConsensusModel

end
