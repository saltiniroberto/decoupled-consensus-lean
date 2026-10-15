import Proofs.Vocabulary.Protocol.Grades.CacheProvenance
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Record.Wiring
import Proofs.Vocabulary.ModelVocabularyFacts

/-!
# Origin of a completed grade result

The condition that a validator's completed grade result comes from the initial empty frame or from
an earlier capture, over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedCacheProvenance
open Execution DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol

/-- Either `r` is round 0 and `root` is empty, or some event `j` before event `i` is `v`'s tick at
    the time `M.domain S.E S.hc r p`, and some world before event `j` from which events `j` to
    `i − 1` can lead to `w₁` has `root` as every frozen root `v`'s store there can compute for round
    `r` and phase `p`, clipped to `F`. -/
def Vocabulary.Proofs.NamedCacheProvenance.Origin (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (i : Nat)
    (w₁ : V → M.N) (v : V)
    (r : Round) (p : Phase) (root : Option (Block V)) (F : Block V) : Prop :=
  (r = 0 ∧ root = none) ∨ ∃ (j : Nat) (t : Time),
    j < i ∧ rho.events[j]? = some (.tick v t) ∧ t = M.domain S.E S.hc r p ∧
    ∃ w ∈ Record.stateBeforeOf M S rho j,
    w₁ ∈ ((rho.events.drop j).take (i - j)).foldlM (Record.worldStepOf M S) w ∧
    ∀ fr, M.freezeRoot S.E
      (M.gradeView (M.toHealing (w v).st.core))
      (w v).st.core.F S.hc.η_SG r
      (M.early S.E S.hc r p) (M.late S.E S.hc r p) ⇢ fr →
    root = fr.map (fun B => M.clipGrade B F)

end

end DecoupledConsensusModel.Sts.Restated
