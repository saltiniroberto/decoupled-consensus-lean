import Proofs.Vocabulary.Protocol.Handlers.ReceiptCallsGF
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Vocabulary.Protocol.Grades.NamedDuties
import Proofs.Vocabulary.Protocol.Handlers.Invariants
import Proofs.Vocabulary.Protocol.Schedule.NamedTick
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedReceiptCalls
import Model.Record.Wiring

/-!
# The Goldfish pool after a block receipt

The block handler's Goldfish pool and the origin of a vote it adds, stated over a model
`M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedReceiptCallsGF
open Execution
open Execution.NamedReceiptCalls

/-- The Goldfish votes of the store `M.on_block_with .alsoCarried` returns on `before` and `B` are
    those of `M.postCore S before B`. -/
theorem Vocabulary.Proofs.NamedReceiptCallsGF.block_with_gf_votes (facts : Record.Facts M) (S : Setup V) (before : M.NS) (B : NamedBlock V) :
    (M.on_block_with .alsoCarried S.E S.hc S.cfg before B).core.gf_votes =
      (M.postCore S before B).core.gf_votes := by
  by_cases h : B ∉ before.bodies ∧ B ∈ (M.postCore S before B).bodies
  · rw [facts.nd.on_block_with_eq_admit_rows_postCore S before B h.1 h.2,
      facts.hd.sameCore_gf_votes (facts.hd.admit_rows_core S.hc (M.postCore S before B) B.attestations)]
    generalize (M.postCore S before B).core = c
    generalize B.attestations.map NamedAttestation.erase = rows
    induction rows generalizing c with
    | nil => rfl
    | cons a rows ih => rw [List.foldl_cons, ih, facts.hd.on_sg_vote_gf_votes]
  · rw [facts.nd.on_block_with_eq_postCore_of_not_new S before B h]

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedReceiptCallsGF
open Execution
open Execution.NamedReceiptCalls

/-- For every path `W` of `rho`, if `before` is the input of a block call of `B` at `v` at the
    `i`-th event of `rho` read along `W`, and the Goldfish vote `u` is not in `before`'s pool but is
    in the pool of the store the block handler returns on `before` and `B`, then `u` is the `j`-th
    Goldfish vote included in `B` for some `j`, carried by that call read along `W`. -/
theorem Vocabulary.Proofs.NamedReceiptCallsGF.block_with_new_vote_origin (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (i : Nat) (v : V)
    (B : NamedBlock V) (before : M.NS)
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    (hcall : Restated.Vocabulary.Execution.NamedReceiptCalls.blockCallAt M S rho W i v B before) (u : GoldfishVote V)
    (hpre : u ∉ (M.store_pool before.core u.slot))
    (hpost : u ∈ (M.store_pool (M.on_block_with
      .alsoCarried S.E S.hc S.cfg before B).core u.slot)) :
    ∃ j, Restated.Vocabulary.Execution.NamedReceiptCalls.carriedGoldfishAt M S rho W i v B j u before := by
  have hpost' : u ∈ (M.store_pool (M.postCore S before B).core u.slot) := by
    rw [facts.sto.mem_pool_iff] at hpost ⊢
    rw [← Restated.Vocabulary.Proofs.NamedReceiptCallsGF.block_with_gf_votes facts S before B]
    exact hpost
  rw [facts.sto.mem_pool_iff] at hpost' hpre
  rw [facts.nd.postCore_eq_process_block_core] at hpost'
  rcases facts.hd.process_block_core_gf_votes_upper S.E S.hc S.cfg before B u.slot u hpost' with
    h | ⟨hmem, hnew, hheld⟩
  · exact absurd h hpre
  · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hmem
    rw [← facts.nd.postCore_eq_process_block_core] at hheld
    exact ⟨j, hcall, hnew, hheld, hj⟩

end

end DecoupledConsensusModel.Sts.Restated
