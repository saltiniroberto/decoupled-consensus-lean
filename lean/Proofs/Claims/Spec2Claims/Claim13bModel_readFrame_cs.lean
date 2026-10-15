import Model.Vocabulary.Protocol.Grades
import Proofs.Claims.ModelIrreducible
import Proofs.Claims.Spec2Claims.Claim13bModel_clipGrade

/-!
# Facts about `Protocol.readFrame`: the grade-2 root it reads

Lemmas that unfold `Protocol.readFrame`, `Protocol.clipFrame` and `Protocol.clipResult`, the cache's
round-`r` frame clipped to the store's finalized block.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.cacheAtRound
  DecoupledConsensusModel.Protocol.clipFrame DecoupledConsensusModel.Protocol.clipResult
  DecoupledConsensusModel.Protocol.phaseResult DecoupledConsensusModel.Protocol.readFrame

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- If the cache `c` holds the grade-2 root `e` for round `r`, the round-`r` frame read from `c` at
    the store `st` holds `Protocol.clipGrade e st.F` as its grade-2 root. -/
theorem readFrame_g2_of_cache {c : Protocol.Cache V} {st : Protocol.HealingStore V} {r : Round}
    {e : Block V}
    (h : Protocol.phaseResult (Protocol.cacheAtRound c r) .g2 = some (some e)) :
    (Protocol.readFrame c st r).g2 = some (some (Protocol.clipGrade e st.F)) := by
  have h' : (Protocol.cacheAtRound c r).g2 = some (some e) := h
  unfold Protocol.readFrame Protocol.clipFrame Protocol.clipResult
  simp only [h', Option.map_some]

/-- If the round-`r` frame read from the cache `c` at the store `st` holds the root `root` for the
    phase `p`, then the cache's own round-`r` frame holds a root `root₀` for `p` with
    `root ⪯ root₀`. -/
theorem readFrame_phase_provenance (c : Protocol.Cache V) (st : Protocol.HealingStore V)
    (r : Round) {p : Protocol.Phase} {root : Block V}
    (h : Protocol.phaseResult (Protocol.readFrame c st r) p = some (some root)) :
    ∃ root₀ : Block V,
      Protocol.phaseResult (Protocol.cacheAtRound c r) p = some (some root₀) ∧
      Block.Preceq root root₀ := by
  unfold Protocol.readFrame at h
  cases p <;>
  · simp only [Protocol.phaseResult, Protocol.clipFrame, Protocol.clipResult] at h ⊢
    obtain ⟨o, ho, hmap⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨B, hB, rfl⟩ := Option.map_eq_some_iff.1 hmap
    subst hB
    exact ⟨B, ho, clipGrade_Preceq B st.F⟩

end DecoupledConsensusModel.Sts
