module
public import Proofs.Vocabulary.Protocol.ValidatorClient.Engine
public import Proofs.Vocabulary.ModelProperties.Block_Preceq

@[expose] public section

/-!
# Facts about `Protocol.deepest_clear`

The deepest block of a chain that descends from an optional floor and passes a test.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

variable {V : Type} [DecidableEq V]

/-- The block `deepest_clear` returns descends from the floor `A`. -/
theorem deepest_clear_floor_Preceq {A C B : Block V} {test : Block V → Bool}
    (h : Protocol.deepest_clear (some A) C test = some B) : Block.Preceq A B := by
  unfold Protocol.deepest_clear at h
  exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem h)).2.1

/-- The block `deepest_clear` returns passes the test. -/
theorem deepest_clear_test {floor : Option (Block V)} {C B : Block V} {test : Block V → Bool}
    (h : Protocol.deepest_clear floor C test = some B) : test B = true := by
  unfold Protocol.deepest_clear at h
  exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem h)).2.2

/-- The block `deepest_clear` returns is an ancestor of the chain's tip `C`. -/
theorem deepest_clear_Preceq {floor : Option (Block V)} {C B : Block V} {test : Block V → Bool}
    (h : Protocol.deepest_clear floor C test = some B) : Block.Preceq B C :=
  preceq_eq_true_iff_Preceq.mp (Proofs.Engine.deepest_clear_preceq h)

end DecoupledConsensusModel.Proofs.ModelProperties

end
