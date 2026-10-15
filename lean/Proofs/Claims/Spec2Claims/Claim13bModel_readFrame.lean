import Proofs.Claims.Spec2Claims.Claim13bInvariantActive
import Proofs.Claims.Spec2Claims.Claim13bModel_readFrame_attest
import Proofs.Claims.Spec2Claims.Claim13bModel_readFrame_cs
import Proofs.Claims.Spec2Claims.Claim13bModel_onPhaseTick_mk_s2

/-!
# Facts about `Protocol.readFrame`

A round's frame read from a cache: the cache's frame at that round, clipped to the store's finalized
block.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.clipFrame
  DecoupledConsensusModel.Protocol.phaseResult DecoupledConsensusModel.Protocol.readFrame

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- If the round-`r` frame read from the cache `c` at the store `st` holds the grade-2 root `root`,
    then the cache's own round-`r` frame holds a grade-2 root `root₀` with `root ⪯ root₀`. -/
theorem readFrame_g2_provenance (c : Protocol.Cache V) (st : Protocol.HealingStore V)
    (r : Round) {root : Block V}
    (h : (Protocol.readFrame c st r).g2 = some (some root)) :
    ∃ root₀ : Block V,
      Protocol.phaseResult (Protocol.cacheAtRound c r) .g2 = some (some root₀) ∧
      Block.Preceq root root₀ :=
  phaseResult_clipFrame (F := st.F) (p := .g2) h

end DecoupledConsensusModel.Sts
