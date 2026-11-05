module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.VoteHeadKit
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.PhaseFrame

@[expose] public section

/-!
# What a holder serves: the two execution-level facts of the minimal selection

The minimal selection `servesMin M S.C` (`Record/Restated/Statements/AbstractTrace/ServesDefs.lean`)
serves a block only when it is compatible with the holder's finalized block. The helpers
that read a block through the sync fact take that compatibility as a hypothesis; two families of
call sites supply it from these facts.

- `vote_head_compatible_finalized_of_exec` (on `VoteHeadKit.lean`, low in the import order): the head
  of an honest validator's Goldfish vote, cast at the vote time of a slot, is a block of its tree
  before that time that is its finalized block or a descendant of it.
- `hMax_witness_compatible_finalized`: under fewer than a third adversary, a block of an honest
  validator's tree of the greatest chain-state height is its finalized block or a descendant of it.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Proofs.Executions

open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Record.Statements.Routines (FinalizedFromChain)
open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject)
open GoldilocksCorrectness.Statements.Routines (Δ)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder] {S : Setup V} {A : Activity V}
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- A block `W` of an honest validator's tree after `i` steps whose chain-state height is at least
that of every block of the tree is the validator's finalized block or a descendant of it, when fewer
than a third of the validators have been in the adversary set up to the time of the step.

Why: the finalized block is the finalized block of the chain state of some block `B` of the tree
(`finalizedFromChain_of_exec`); the finalization height of `B`'s chain state is less than `B`'s
chain-state height (Lemma 47), which is at most `W`'s; so Lemma 68 at the validator itself puts the
finalized block at `W` or before it.

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed;
- `S`, `x`: the setup, the execution; `R`: the run's facts; `E`: the environment's facts;
  `hRoots`: roots name blocks until `tR`; `i`: the step; `p`: the validator; `W`: the block.

Read aloud: a block of greatest height in an honest validator's tree is not pruned by its finalized
block. -/
theorem hMax_witness_compatible_finalized (Fx : FixedValidators M.toSlotLayout)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {tR : ℕ} (hRoots : RootsNameBlocksUntil M A x tR) (i : ℕ) (p : V) (W : Block V)
    -- fewer than a third of the validators have been in the adversary set up to the step's time
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) (x.time i))
    -- `p` is honest after `i` steps
    (hp : p ∉ A.corrupted i)
    -- `W` is a block of `p`'s tree of the greatest chain-state height
    (hW : W ∈ (x.st i p).tree)
    (hmax : ∀ B ∈ (x.st i p).tree, (M.chainStateOf S.C B).h ≤ (M.chainStateOf S.C W).h)
    -- the time of the step is at most the bound of `hRoots`
    (htR : x.time i ≤ tR) :
    (x.st i p).finalized.AncestorEq W := by
  obtain ⟨B, hB, hFB⟩ := (finalizedFromChain_of_exec M F) S A x R E i p
  have h47 := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F)
    S.C B B).1
  have hlt : (M.chainStateOf S.C B).h_F < (M.chainStateOf S.C W).h :=
    lt_of_lt_of_le (lt_of_le_of_lt h47.2.2 h47.2.1) (hmax B hB)
  rw [hFB]
  exact (lem68_honest_past_finalized M F Fx) S A x R E hRoots i i p p B W
    (by rwa [max_self]) hp hp hB hW hlt (by rwa [max_self])

end GoldilocksCorrectness.Record.Proofs.Executions
