module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma84
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma54
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.HealedAttestationStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Node
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Wiring
public import GoldilocksCorrectness.Statements.Executions.HealedAttestationStatements

@[expose] public section

/-!
# HealedFrame, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/HealedFrame.lean`, over a model `M` whose
facts `F` hold, for an execution `x` of `protocolOf M S`: every attestation included in a held block
or in one of its ancestors is in the holder's pool. The page's routine-level theorems are the facts'
fields or have their twins in phase A.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Proofs.Routines (DREBPost DREBPost.bind DREBPost.bind_any DREBPost.dite
  DREBPost.ite DREBPost.of_outcome DREBPost.pure forIn_yield_inv)

open GoldilocksCorrectness.Proofs.Routines (fg_on_attestation_keeps fg_on_block_eq
  fg_on_block_holds fg_on_block_pool)

open GoldilocksCorrectness.Proofs.Routines (ChainsInPool on_attestation_chainsInPool
  on_block_chainsInPool tick_chainsInPool)

open GoldilocksCorrectness.Proofs.Routines (fgState_initial_eq initial_eq)

open GoldilocksCorrectness.Proofs.Routines (receive_chainsInPool)

namespace GoldilocksCorrectness.Record.Proofs.Executions

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-! ## The pool holds what the chains include -/

/-- **Kit fact, the pool holds what the chains include.** At every step of every execution, every
attestation included in a block of a validator's tree, or in one of its ancestors, is in that
validator's pool. A separate invariant over executions, not a clause of `NodeInv`.

Why: initially the tree holds the genesis block alone (the field `initial_tree`), which includes
nothing (`on_chain_genesis`); a tick and a delivery each keep the node holding every attestation
on the chains of its tree (the facts `tick_chainsInPool`, `receive_chainsInPool`), and the tick
starts from a node state with the configuration's tree and pool (`tickInputState_readers`).

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `i`: the step; `v`: the validator;
- `Y`: the held block; `a`: the attestation.

Read aloud: what a validator's chains include, its pool holds.

 -/
theorem pool_holds_chain_attestations (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (i : ℕ) (v : V) (Y : Block V) (a : Attestation V)
    (hY : Y ∈ (x.st i v).tree) (ha : M.on_chain a Y = true) :
    a ∈ (x.st i v).attestationsHeld := by
  -- the landed `ChainsInPool`, written out over the record
  suffices hI : ∀ i : ℕ, ∀ Y ∈ (x.st i v).tree, ∀ a : Attestation V, M.on_chain a Y = true →
      a ∈ (x.st i v).attestationsHeld from hI i Y hY a ha
  intro i
  induction i with
  | zero =>
      rw [(getElem_zero_st M F) x R v]
      intro Y hY a ha
      rw [F.init.initial_tree] at hY
      have hY' : Y = Block.genesis := Finset.mem_singleton.1 hY
      subst hY'
      rw [(GoldilocksCorrectness.Record.Proofs.Routines.on_chain_genesis M F)] at ha
      cases ha
  | succ i ih =>
      rcases (step_cases_per_step M F) x R E i v with h | ⟨t, n', sent, hl, -, hrun, h, -⟩ | ⟨sm, -, -, h⟩ |
          ⟨⟨tRw, keepw, hlw⟩, -, h⟩
      · rw [h]; exact ih
      · rw [h]
        -- the tick runs from the state at its step
        rw [show x.tickInput v t = x.st i v by
          unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hl]] at hrun
        exact F.tk.tick_chainsInPool S.C S.P S.X _ _ n' sent hrun ih
      · rw [h]; exact F.rcv.receive_chainsInPool S.C S.P S.X _ _ ih
      · -- a wake keeps the tree and the pool
        rw [h tRw keepw hlw]
        obtain ⟨-, -, hT, -, -, -, hA, -⟩ := F.wk.wake_readers (x.st i v) (tRw : Int)
        simp only [GoldilocksModel.N.tree, GoldilocksModel.N.attestationsHeld] at ih ⊢
        rw [hT, hA]
        exact ih

/-! ## Slots against support cutoffs -/

end GoldilocksCorrectness.Record.Proofs.Executions

