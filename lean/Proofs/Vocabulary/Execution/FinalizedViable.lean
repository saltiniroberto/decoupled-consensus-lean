module
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.GradeBootstrapCore
public import Proofs.Vocabulary.ModelProperties.NamedNode_initial
public import Proofs.Vocabulary.ModelProperties.NamedStore_initial
public import Proofs.Vocabulary.Protocol.Handlers.JustificationBound
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section


namespace DecoupledConsensusModel.Proofs.NamedFinalizedViable
open Execution Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The block body, over an arbitrary builder -/

/-- `on_block_using` preserves `FinalizedViable`, whatever builder the caller supplies. -/
theorem viable_on_block_using (E : Env V) (st : Protocol.Store V) (B : Block V)
    (build : ChainState V → ChainState V) (h : FinalizedViable st) :
    FinalizedViable (Protocol.on_block_using E st B build) := by
  rcases NamedJustificationBound.raw_eq_or_accepted E st B build with hid | hacc
  · rw [hid]
    exact h
  obtain ⟨u, huT, huF, _huJ, _huhj, humax, husigma, hfresh, hFB, hres⟩ := hacc
  rw [hres]
  have hu : FinalizedViable u := by
    obtain ⟨hFT, W, hW, hFW, hh⟩ := (finalizedViable_iff st).mp h
    have hWB : W ≠ B := fun hEq => hfresh (hEq ▸ hW)
    rw [finalizedViable_iff, huT, husigma, huF, humax]
    exact ⟨Finset.mem_insert_of_mem hFT, W, Finset.mem_insert_of_mem hW, hFW, by
      simpa only [if_neg hWB] using hh⟩
  refine finalizedViable_update_finality u (u.σ B) ?_ rfl ?_ hu
  · rw [huT]
    exact Finset.mem_insert_self _ _
  · rw [huF]
    exact hFB

/-! ## The named handlers -/

private theorem viable_process_core (S : Setup V) (st : Protocol.NamedStore V)
    (B : NamedBlock V) (h : FinalizedViable st.core) :
    FinalizedViable (Protocol.NamedStore.process_block_core S.E S.hc S.cfg st B).core := by
  dsimp only [Protocol.NamedStore.process_block_core]
  split_ifs <;> first
    | exact h
    | (rw [NamedStore.commit_core]
       dsimp only [Protocol.on_block_checked_using]
       split_ifs
       · exact viable_on_block_using S.E st.core B.erase _ h
       · exact h)

omit [Fintype V] in
private theorem viable_row (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (a : NamedAttestation V) (h : FinalizedViable st.core) :
    FinalizedViable (Protocol.NamedAdmission.admit_row hc st a).core := by
  rw [NamedAdmission.admit_row_core]
  exact finalizedViable_of_eq (on_sg_vote_T hc st.core a.erase)
    (coreEq_on_sg_vote hc st.core a.erase).σ_eq
    (coreEq_on_sg_vote hc st.core a.erase).F_eq
    (on_sg_vote_h_max hc st.core a.erase) h

omit [Fintype V] in
private theorem viable_rows (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (rows : List (NamedAttestation V)) (h : FinalizedViable st.core) :
    FinalizedViable (Protocol.NamedAdmission.admit_rows hc st rows).core := by
  induction rows generalizing st with
  | nil => exact h
  | cons a rows ih => exact ih _ (viable_row hc st a h)

private theorem viable_block_with (S : Setup V) (st : Protocol.NamedStore V)
    (B : NamedBlock V) (h : FinalizedViable st.core) :
    FinalizedViable
      (Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg st B).core := by
  have hcore := viable_process_core S st B h
  dsimp only [Protocol.NamedAdmission.on_block_with, Protocol.NamedAdmission.admit_carried]
  split_ifs
  · exact viable_rows S.hc _ B.attestations hcore
  · exact hcore


#print axioms viable_on_block_using

end DecoupledConsensusModel.Proofs.NamedFinalizedViable

end
