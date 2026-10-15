import Proofs.Claims.Spec2Claims.Claim13bInvariantActive
import Proofs.Claims.Spec2Claims.Claim13bModel_readFrame_attest
import Proofs.Claims.Spec2Claims.Claim13bModel_readFrame_cs
import Proofs.Claims.Spec2Claims.Claim13bModel_onPhaseTick_mk_s2

/-!
# Facts about `Protocol.readFrame`: the grade-1 entry

A grade-1 root of a frame read from a cache is an ancestor of a grade-1 root the cache itself holds
for that round.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.clipFrame
  DecoupledConsensusModel.Protocol.phaseResult DecoupledConsensusModel.Protocol.readFrame

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- If the round-`r` frame read from the cache `c` at the store `st` holds the grade-1 root `root`,
    then the cache's own round-`r` frame holds a grade-1 root `root₀` with `root ⪯ root₀`. -/
theorem readFrame_g1_provenance (c : Protocol.Cache V) (st : Protocol.HealingStore V)
    (r : Round) {root : Block V}
    (h : (Protocol.readFrame c st r).g1 = some (some root)) :
    ∃ root₀ : Block V,
      Protocol.phaseResult (Protocol.cacheAtRound c r) .g1 = some (some root₀) ∧
      Block.Preceq root root₀ :=
  phaseResult_clipFrame (F := st.F) (p := .g1) h

end DecoupledConsensusModel.Sts
