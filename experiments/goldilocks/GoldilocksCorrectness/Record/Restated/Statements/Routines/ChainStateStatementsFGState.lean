module
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ChainStateFGState
public import GoldilocksCorrectness.Statements.Routines.ChainStateStatements

@[expose] public section

/-!
# ChainStateStatementsFGState, over a model: Lemma 52

The FG-state statement of `GoldilocksCorrectness/Statements/Routines/ChainStateStatements.lean` over
a model `M` whose facts `F` hold: Lemma 52, a valid held attestation not on the parent's chain is
included in a proposal on the parent, for a node state `n` satisfying the model's node invariant
and a parent `H` of `n`'s tree. Proved on `Record/Restated/Proofs/Routines/ChainStateFGState.lean`.

The landed Lemma 52 reads the stored chain state of any block `H`, of the tree or not: its record
form takes `H` in the tree, and it has no recovery here.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Statements.Routines

open Goldilocks
open GoldilocksCorrectness.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section

variable (M : GoldilocksModel V) (F : Facts M)
include M F

/-- **Lemma 52, a valid held attestation not on the parent's chain is included.** An attestation
held by the node state `n` that is valid against the chain state `M.chainStateOf C H` of a block
`H` of `n`'s tree and not included in `H` or an ancestor of `H` is among the attestations a block
on `H` includes, `M.proposal_attestations n H`.

Why: `proposal_attestations` filters the held attestations by exactly these two tests.

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `hI`: `n` satisfies the model's node invariant; `H`: the parent of the proposal, a block of `n`'s
  tree; `a`: the attestation.

Read aloud: the proposal includes every valid held attestation its chain does not already hold. -/
theorem lem52_pool_attestation_included (C : Config) (P : Provisional V) (X : External V)
    (n : M.N)
    -- `n` satisfies the model's node invariant
    (hI : M.nodeInv C P X n) (H : Block V)
    -- `H` is a block of `n`'s tree
    (hH : H ∈ n.tree)
    (a : Attestation V)
    -- `a` is held by `n`
    (hPool : a ∈ n.attestationsHeld)
    -- `a` is valid against the chain state of `H`
    (hValid : M.valid_attestation (M.chainStateOf C H) a = true)
    -- `a` is not included in `H` or in an ancestor of `H`
    (hNew : M.on_chain a H = false) :
    a ∈ M.proposal_attestations n H :=
  GoldilocksCorrectness.Record.Proofs.Routines.lem52_pool_attestation_included M F C P X n hI H hH
    a hPool hValid hNew

end

end GoldilocksCorrectness.Record.Statements.Routines
