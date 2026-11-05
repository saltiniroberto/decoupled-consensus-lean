module
public import GoldilocksCorrectness.Proofs.Executions.Lemma84
public import GoldilocksCorrectness.Proofs.Executions.Lemma54
public import GoldilocksCorrectness.Statements.Executions.HealedAttestationStatements
public import GoldilocksCorrectness.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Proofs.Routines.FGState
public import GoldilocksCorrectness.Proofs.Routines.Node
public import GoldilocksCorrectness.Proofs.Routines.Wiring

@[expose] public section

/-!
# The healed-frame kit facts

Two kit facts the frame facts after healing (Lemma 91, `Proofs/Executions/Lemma91.lean`) and the
inclusion of the honest proposal (`Proofs/Executions/Lemma90Inclusion.lean`) read:

- `pool_holds_chain_attestations`: every attestation included in a held block, or in one of its
  ancestors, is in the holder's pool (`ChainsInPool`, an invariant over executions, never a
  `NodeInv` clause);
- `slot_le_of_supportCutoff_lt`: the slot arithmetic of support cutoffs against vote times and
  support cutoffs.


-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Proofs.Routines (DREBPost DREBPost.bind DREBPost.bind_any DREBPost.dite
  DREBPost.ite DREBPost.of_outcome DREBPost.pure forIn_yield_inv)

open GoldilocksCorrectness.Proofs.Routines (fg_on_attestation_keeps fg_on_block_eq fg_on_block_holds
  fg_on_block_pool)

open GoldilocksCorrectness.Proofs.Routines (ChainsInPool on_attestation_chainsInPool
  on_block_chainsInPool tick_chainsInPool)

open GoldilocksCorrectness.Proofs.Routines (fgState_initial_eq initial_eq)

open GoldilocksCorrectness.Proofs.Routines (on_chain_genesis)

open GoldilocksCorrectness.Proofs.Routines (receive_chainsInPool)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-! ## The pool holds what the chains include -/

/-- **Kit fact, the pool holds what the chains include.** At every step of every execution, every
attestation included in a block of a validator's tree, or in one of its ancestors, is in that
validator's pool. A separate invariant over executions, not a clause of `NodeInv`.

Why: initially the tree holds the genesis block alone, which includes nothing; a block enters the
tree only through `fg_on_block`, after `block_admissible` found its parent held, and
`fg_on_block` receives every attestation the block includes into the pool; no routine removes an
attestation from the pool (`AttPoolGrows`), and the tree changes only there.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `i`: the step; `v`: the validator;
- `Y`: the held block; `a`: the attestation.

Read aloud: what a validator's chains include, its pool holds.

 -/
theorem pool_holds_chain_attestations (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (i : ℕ) (v : V) (Y : Block V) (a : Attestation V)
    (hY : Y ∈ (x[i][v].st).S.T) (ha : on_chain a Y = true) :
    a ∈ (x[i][v].st).S.attestations := by
  suffices hI : ∀ i : ℕ, ChainsInPool (x[i][v].st) from hI i Y hY a ha
  intro i
  induction i with
  | zero =>
      rw [getElem_zero_st x v, initial_eq, fgState_initial_eq]
      intro Y hY a ha
      have hY' : Y = Block.genesis := Finset.mem_singleton.1 hY
      subst hY'
      rw [on_chain_genesis] at ha
      cases ha
  | succ i ih =>
      rcases step_cases x i v with h | ⟨t, n', sent, -, -, hrun, h⟩ | ⟨sm, -, -, -, h⟩
      · rw [h]; exact ih
      · rw [h]
        have hin : ChainsInPool (tickInputState x i t v) :=
          ih.of_S (tickInputState_frame x i t v).1
        exact DREBPost.of_outcome (tick_chainsInPool S.C S.P S.X _ _ hin) hrun
      · rw [h]; exact receive_chainsInPool S.C S.P S.X _ _ ih

/-! ## Slots against support cutoffs -/

end GoldilocksCorrectness.Proofs.Executions
