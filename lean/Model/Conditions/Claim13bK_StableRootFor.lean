import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Record.Wiring

/-!
# Phase results of a cache relative to the clock

The conditions `CacheNoFutureResult` and `G2EntryAbove` on the phase results a validator's cache
holds, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Every result `v`'s cache holds after `k` steps, for a round `r` and a phase `p`, has `r` at most
    the round of `x[k].time`, or that phase's domain time no later than `x[k].time`. -/
def CacheNoFutureResult (M : Record.Model V) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (k : Nat) (v : V) : Prop :=
  ∀ (r : Round) (p : Protocol.Phase) (o : Option (Block V)),
    M.phaseResult (M.cacheAtRound (x[k][v].st).cache r) p = some o →
    r ≤ (M.round_of S.hc (S.E.slotOf (x[k].time : Int))) ∨
      M.domain S.E S.hc r p ≤ (x[k].time : Int)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- `w`'s cache after `k` steps has a round between `q` and the round of `x[k].time`, and holds for
    round `q + 1` and the phase `g2` a root `e` with `X ⪯ e`. -/
def G2EntryAbove (M : Record.Model V) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (q : Round) (X : Block V) (k : Nat) (w : V) : Prop :=
  q ≤ (x[k][w].st).cache.round ∧
    (x[k][w].st).cache.round ≤ (M.round_of S.hc (S.E.slotOf (x[k].time : Int))) ∧
    ∃ e : Block V,
      M.phaseResult (M.cacheAtRound (x[k][w].st).cache (q + 1)) .g2
        = some (some e) ∧ Block.Preceq X e

end

end DecoupledConsensusModel.Sts.Restated
