import Proofs.Vocabulary.Protocol.Grades.NamedNode
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Record.Wiring

/-!
# The grade cache after a tick or a receipt

The grade cache a node state holds after a tick or after processing an object, stated over a model
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
open DecoupledConsensusModel.Proofs.NamedNode
open Execution DecoupledConsensusModel.Protocol

/-- For every outcome `out₁` of `v`'s tick at `t` from a reached node state `n`, and every outcome
    `c` of the cache `onPhaseTick` builds from `n`'s cache at `t`, the grade cache of `out₁.1` is
    `c` clipped at the finalized block of `out₁.1`'s core store. -/
theorem Vocabulary.Proofs.NamedNode.tick_cache_eq (facts : Record.Facts M) (S : Setup V) (v : V) (n : M.N) (t : Time) : ∀ out₁, M.tick S v n t ⇢ out₁ →
    ∀ c, M.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache ⇢ c →
    ∀ (hn : M.reachedNode n := by trivial),
    out₁.1.cache =
      M.clipCache out₁.1.st.core.F c :=
  fun out₁ hout c hc _hn => facts.nd.tick_cache_eq S v n t out₁ hout c hc

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedNode
open Execution DecoupledConsensusModel.Protocol

/-- For every outcome `n₁` of processing the object `o` at a reached node state `n`, the cache of
    `n₁` is `n`'s cache clipped at the finalized block of `n₁`'s core store. -/
theorem Vocabulary.Proofs.NamedNode.process_cache_eq (facts : Record.Facts M) (S : Setup V) (n : M.N) (o : NamedObject V) : ∀ n₁, M.process S n o ⇢ n₁ → 
    ∀ (hn : M.reachedNode n := by trivial),
    n₁.cache =
      M.clipCache n₁.st.core.F n.cache :=
  fun n₁ hc1 _hn => facts.nd.process_cache_eq S n o n₁ hc1

end

end DecoupledConsensusModel.Sts.Restated
