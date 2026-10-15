import Proofs.Claims.Spec2Claims.Claim13beRoute3_45
import Proofs.Claims.Spec2Claims.Claim13bModel_conflictsWithFinality
import Proofs.Claims.Spec2Claims.Claim13bModel_e2Fields
import Proofs.Claims.Spec2Claims.Claim13bModel_initial_inclG2
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedAttestation_erase

/-!
# Per-instant forms of block and store lemmas

Lemmas on the attestations of run blocks read through `Xb`, with the run's premises given by the
bundle `AdmissibleFieldsOn`.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

variable {V : Type} [DecidableEq V] [Fintype V]

section StoreBridge

local macro "sb% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Vocabulary.Protocol.Handlers.StoreBridge)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.NamedStoreBridge ++ n.getId)))

/-- If `B` is a run block read through `Xb`, `X ⪯ B` and `X` carries the attestation `row`, then
    some validator processed `X` at some instant. -/
theorem processes_of_runBlockOn (S : Setup V) {rho : Run V} (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} (hf : AdmissibleFieldsOn S rho Hs Xb lo)
    {B : NamedBlock V} (hB : RunBlockOn S rho Xb B)
    {X : NamedBlock V} (hXB : NamedBlock.Preceq X B)
    {row : NamedAttestation V} (hrow : row ∈ X.attestations) :
    ∃ (u : V) (t : Time), Run.processes S rho u (Object.block X) t := by
  obtain ⟨C, hC, hBC⟩ := hB
  have hXC : NamedBlock.Preceq X C := (sb% preceq_trans) hXB hBC
  rcases hC with hobj | ⟨w, -, i, hmem⟩
  · obtain ⟨i, u, t, hev⟩ := Proofs.Bridges.exists_deliver_of_mem_objects rho hobj
    rcases (sb% preceq_cases) hXC with rfl | hparent
    · exact ⟨u, t, Or.inr ⟨i, hev⟩⟩
    · have hdeps := hf.deps i u (Object.block C) t hev
      have hpar : C.parent ∈ (rho.stateBefore S i u).st.bodies := by
        exact (Proofs.NamedReceipt.depsPresent_block_iff _ C).1 hdeps
      have hXmem : X ∈ (rho.stateBefore S i u).st.bodies :=
        (sb% ancestor_body_mem)
          ((sb% namedParentClosed_of_inv) S
            (Proofs.NamedRuntime.stateBefore_invariants S rho i u))
          hpar hparent
      obtain ⟨t', hproc⟩ := (sb% processes_of_mem_bodies) S rho u i hXmem hrow
      exact ⟨u, t', hproc⟩
  · have hXmem : X ∈ (rho.stateBefore S i w).st.bodies :=
      (sb% ancestor_body_mem)
        ((sb% namedParentClosed_of_inv) S
          (Proofs.NamedRuntime.stateBefore_invariants S rho i w))
        hmem hXC
    obtain ⟨t', hproc⟩ := (sb% processes_of_mem_bodies) S rho w i hXmem hrow
    exact ⟨w, t', hproc⟩

/-- If the family `Hs` shrinks as time grows and `B` is a run block read through `Xb`, every
    attestation on `B`'s chain signed by a member of `Hs rho.horizon` was emitted by its signer. -/
theorem carriedByHonest_of_runBlockOn (S : Setup V) {rho : Run V} (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} (hf : AdmissibleFieldsOn S rho Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {B : NamedBlock V} (hB : RunBlockOn S rho Xb B) :
    Proofs.AlignedRoundLemmas.CarriedByHonest S rho (Hs rho.horizon)
      (chain_attestations B.erase) := by
  intro a ha hah
  obtain ⟨X, hXB, row, hrow, rfl⟩ := (sb% named_mem_chain_attestations) B ha
  obtain ⟨u, t, hproc⟩ := processes_of_runBlockOn S Hs Xb hf hB hXB hrow
  have hthor : t ≤ rho.horizon := by
    rcases hproc with ⟨i, hi, -⟩ | ⟨i, hi⟩
    · exact (hf.in_horizon _ (List.mem_of_getElem? hi)).2
    · exact (hf.in_horizon _ (List.mem_of_getElem? hi)).2
  obtain ⟨t', -, hem⟩ := hf.carried_attest u X t hproc row hrow
    (hHs _ _ hthor (by rw [← namedAttestation_erase_val_index row]; exact hah))
  exact ⟨row, t', rfl, by rw [namedAttestation_erase_val_index]; exact hem⟩

end StoreBridge

end DecoupledConsensusModel.Sts
