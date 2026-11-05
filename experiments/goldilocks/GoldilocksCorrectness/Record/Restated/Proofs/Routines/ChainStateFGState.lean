module
public import GoldilocksCorrectness.Record.Facts

@[expose] public section

/-!
# ChainStateFGState, over a model: Lemma 52

The FG-state theorem of `GoldilocksCorrectness/Proofs/Routines/ChainState.lean` over a model `M`
whose facts `F` hold: Lemma 52, a valid held attestation not on the parent's chain is included in
a proposal on the parent. It is stated for a node state `n` satisfying the model's node invariant
`M.nodeInv C P X n` and a parent `H` of `n`'s tree (the reader's fact `proposal_attestations_eq`
holds under both), with `M.chainStateOf C H` for the stored chain state of `H`.

The landed Lemma 52 reads the stored chain state of any block `H`, of the tree or not: its record
form takes `H` in the tree, and it has no recovery here (as the landed `is_viable_iff` on
`FGStateReaders.lean`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section

variable (M : GoldilocksModel V) (F : Facts M)
include M F

/-- **Lemma 52, a valid held attestation not on the parent's chain is included.** The proof; the
audited statement is in `Record/Restated/Statements/Routines/ChainStateStatementsFGState.lean`.

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `hI`: `n` satisfies the model's node invariant; `H`: the parent, a block of `n`'s tree; `a`: the
  attestation.

Read aloud: a valid attestation the node holds that is not on the parent's chain is included in the
proposal. -/
theorem lem52_pool_attestation_included (C : Config) (P : Provisional V) (X : External V)
    (n : M.N) (hI : M.nodeInv C P X n) (H : Block V) (hH : H ∈ n.tree)
    (a : Attestation V) (hPool : a ∈ n.attestationsHeld)
    (hValid : M.valid_attestation (M.chainStateOf C H) a = true)
    (hNew : M.on_chain a H = false) :
    a ∈ M.proposal_attestations n H := by
  rw [F.ndAdded.proposal_attestations_eq hI hH, List.mem_filter]
  refine ⟨hPool, ?_⟩
  simp only [Bool.and_eq_true, Bool.not_eq_true']
  exact ⟨hValid, hNew⟩

end

end GoldilocksCorrectness.Record.Proofs.Routines
