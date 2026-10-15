import Proofs.Claims.Spec2Claims.Claim13bModel_clipFrame_s2

/-!
# Facts about `Protocol.clipCache`

The phase results of a grade cache clipped against a finalized block.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.clipCache
  DecoupledConsensusModel.Protocol.cacheAtRound DecoupledConsensusModel.Protocol.pendingFrame
  DecoupledConsensusModel.Protocol.phaseResult

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- If the cache clipped to `F` holds the root `root` for round `r₁` and phase `p`, then the
    unclipped cache holds there a root of which `root` is an ancestor. -/
theorem phaseResult_clipCache {F : Block V} {c : Protocol.Cache V} {r₁ : Round}
    {p : Protocol.Phase} {root : Block V}
    (h : Protocol.phaseResult (Protocol.cacheAtRound (Protocol.clipCache F c) r₁) p
      = some (some root)) :
    ∃ root₀ : Block V,
      Protocol.phaseResult (Protocol.cacheAtRound c r₁) p = some (some root₀) ∧
        Block.Preceq root root₀ := by
  unfold Protocol.cacheAtRound Protocol.clipCache at h
  unfold Protocol.cacheAtRound
  split_ifs at h ⊢ with h1 h2
  · exact phaseResult_clipFrame h
  · exact phaseResult_clipFrame h
  · simp [Protocol.phaseResult, Protocol.pendingFrame] at h
    cases p <;> simp_all

end DecoupledConsensusModel.Sts
