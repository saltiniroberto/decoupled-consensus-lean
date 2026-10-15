import Proofs.Claims.Spec2Claims.Claim13bStepSG
import Proofs.Claims.Spec2Claims.Claim13bModel_confirmationReadFrom

/-!
# Facts about `Protocol.readFrame`: the roots it reads at each phase

Lemmas that unfold `Protocol.readFrame`, `Protocol.clipFrame`, `Protocol.clipResult` and
`Protocol.phaseResult`. The frame read holds the clip of each root the cache holds.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.cacheAtRound
  DecoupledConsensusModel.Protocol.clipFrame DecoupledConsensusModel.Protocol.clipResult
  DecoupledConsensusModel.Protocol.phaseResult DecoupledConsensusModel.Protocol.readFrame

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V]

/-- If the cache `c` holds the grade-1 root `e` for round `r`, the round-`r` frame read from `c` at
    the store `st` holds `Protocol.clipGrade e st.F` as its grade-1 root. -/
theorem readFrame_g1_of_cache {c : Protocol.Cache V} {st : Protocol.HealingStore V} {r : Round}
    {e : Block V}
    (h : Protocol.phaseResult (Protocol.cacheAtRound c r) .g1 = some (some e)) :
    (Protocol.readFrame c st r).g1 = some (some (Protocol.clipGrade e st.F)) := by
  have h' : (Protocol.cacheAtRound c r).g1 = some (some e) := h
  unfold Protocol.readFrame Protocol.clipFrame Protocol.clipResult
  simp only [h', Option.map_some]

/-- If the cache `c` holds the root `e` for round `r` and the phase `p`, the round-`r` frame read
    from `c` at the store `st` holds `Protocol.clipGrade e st.F` for that phase. -/
theorem readFrame_phase_of_cache {c : Protocol.Cache V} {st : Protocol.HealingStore V}
    {r : Round} {p : Protocol.Phase} {e : Block V}
    (h : Protocol.phaseResult (Protocol.cacheAtRound c r) p = some (some e)) :
    Protocol.phaseResult (Protocol.readFrame c st r) p
      = some (some (Protocol.clipGrade e st.F)) := by
  have h' : Protocol.phaseResult (Protocol.cacheAtRound c r) p = some (some e) := h
  cases p <;>
  · simp only [Protocol.phaseResult] at h' ⊢
    unfold Protocol.readFrame Protocol.clipFrame Protocol.clipResult
    simp only [h', Option.map_some]

omit [DecidableEq V] in
/-- A frame's phase result at the phase `g0` is its grade-0 field. -/
theorem phaseResult_g0 (f : Protocol.Frame V) : Protocol.phaseResult f .g0 = f.g0 := rfl

omit [DecidableEq V] in
/-- A frame's phase result at the phase `g1` is its grade-1 field. -/
theorem phaseResult_g1 (f : Protocol.Frame V) : Protocol.phaseResult f .g1 = f.g1 := rfl

omit [DecidableEq V] in
/-- A frame's phase result at the phase `g2` is its grade-2 field. -/
theorem phaseResult_g2 (f : Protocol.Frame V) : Protocol.phaseResult f .g2 = f.g2 := rfl

variable [Fintype V]

end DecoupledConsensusModel.Sts
