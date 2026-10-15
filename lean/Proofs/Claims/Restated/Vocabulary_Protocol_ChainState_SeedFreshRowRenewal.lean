import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_Action
import Proofs.Claims.Restated.Vocabulary_Protocol_ValidatorClient_HeightPairCases
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_HeightPairCases
import Model.Record.Wiring

/-!
# The action row of a fresh FG source

A theorem over a model `M : Record.Model V` and its facts `facts : Record.Facts M`: when the FG
source of an action read stands at height `H - 1` with entry root `T` and the read's own lock leaves
the action's finality pair empty, the action's attestation carries the height vote for `H - 1` and
`T`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution
open Internal.HealingSurface
open Internal.PhaseGrades
open Protocol
open Proofs.HealingLemmas
open Proofs.Optimistic
open Protocol (own_lock)
open Protocol (derive_named)

/-- For every read `n` of `v`'s round-`r` action in `rho` and every outcome `A` of the round action
    on `n`, if the FG source of `n` at round `r` can be `Q`, `Q`'s chain state in `n`'s healing
    store has height `H - 1` and entry root `T`, and the own lock of `n`'s record at that height
    leaves `A`'s finality pair empty, then the attestation of every outcome of the attestation duty
    on `n` has the height pair `vote (H - 1) T` with the timeout flag `false` or `true`. -/
theorem Vocabulary.Proofs.HealingSurface.seedFreshActionRow_of_source (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V}
    {H : Height} {r : Round} {v : V} {Q : Block V} {T : BlockId} :
    ∀ n ∈ Restated.Vocabulary.Proofs.HealingSurface.actionReadAt M S rho v r,
    ∀ (A : M.NR × NamedAttestation V), M.round_action_with (M.gradeContract n.cache) S.E S.hc
      (S.node v) (M.toHealing n.st.core) n.record ⇢ A →
    ∀ (hsource : Restated.Vocabulary.Internal.PhaseGrades.nodeFGSource M S n r ⇢ some Q)
      (hsourceHeight : ((M.toHealing n.st.core).σ Q).h = H - 1)
      (hsourceEntry : ((M.toHealing n.st.core).σ Q).T_h.root = T)
      (hlock : M.own_lock n.record.legacy ((M.toHealing n.st.core).σ Q).h
        A.2.finality_pair = none),
    ∀ D : M.NS × M.NR × NamedAttestation V,
      M.duties_attest_with (M.gradeContract n.cache) S.E S.hc (S.node v) n.st n.record ⇢ D →
    D.2.2.height_pair = NamedHeightPair.vote (H - 1) T false ∨
      D.2.2.height_pair = NamedHeightPair.vote (H - 1) T true := by
  intro n hn A hA hsource hsourceHeight hsourceEntry hlock D hD
  have hround : (M.round_of S.hc) (M.toHealing n.st.core).s = r := by
    show M.round_of S.hc (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.s = r
    rw [facts.sto.toHealing_s n.st.core]
    exact Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt_round facts S rho v r n hn
  have hsource' : Restated.Vocabulary.Proofs.HealingSurface.actionSource M
      (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core) ⇢ some Q := by
    unfold Restated.Vocabulary.Proofs.HealingSurface.actionSource
    rw [hround]
    exact hsource
  have hpairs :=
    Restated.Vocabulary.Proofs.HealingSurface.round_action_height_pair_target_or_timeout_of_source_lock_none_or_aligned facts
      (M.gradeContract n.cache) S.E S.hc (S.node v) (M.toHealing n.st.core) n.record A hA hsource'
      (Or.inl hlock)
  rw [hsourceHeight, hsourceEntry] at hpairs
  rw [facts.dt.attest_with_row _ _ _ _ _ _ D hD A hA]
  exact hpairs

end

end DecoupledConsensusModel.Sts.Restated
