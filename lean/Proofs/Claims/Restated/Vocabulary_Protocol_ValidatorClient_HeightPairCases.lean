import Proofs.Vocabulary.Protocol.ValidatorClient.HeightPairCases
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_HeightPairCases
import Model.Record.Wiring

/-!
# The height pair of a round action

The cases of the height pair a round action emits: empty, the vote for the selected source's height
and target root, or a timeout, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

private theorem returns_bind_elim {α β : Type} (m : DC.NDRE α) (k : α → DC.NDRE β) (b : β)
    (h : (m >>= k) ⇢ b) : ∃ a, m ⇢ a ∧ k a ⇢ b := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_bind, Set.bind_def] at h
  obtain ⟨e, he, hb⟩ := Set.mem_iUnion₂.mp h
  cases e with
  | ok a => exact ⟨a, he, hb⟩
  | error err => simp at hb

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Protocol (ChainState HeightConfig)
open Protocol (Record height_pair own_lock)

/-- If the own lock of `Lambda` at height `H` under `fp` is empty or `T`, then the height pair
    `M.height_pair` gives for `(H, T, nu)` is the target `(H, T)` or the timeout at `H`. -/
theorem Vocabulary.Proofs.HealingSurface.height_pair_target_or_timeout_of_fields_some_and_lock_none_or_aligned (facts : Record.Facts M)
    (Lambda : M.R) (H : Height) (T : BlockId) (nu : Bool)
    (fp : Option FinalityPair)
    (hlock : M.own_lock Lambda H fp = none ∨ M.own_lock Lambda H fp = some T) :
    M.height_pair Lambda (some (H, T, nu)) fp = HeightPair.target H T ∨
      M.height_pair Lambda (some (H, T, nu)) fp = HeightPair.timeout H := by
  by_cases htimeout : Lambda.timeout H = true
  · exact Or.inr (facts.vc.height_pair_eq_timeout_of_timeout Lambda fp htimeout)
  · have htimeoutFalse : Lambda.timeout H = false :=
      Bool.eq_false_of_not_eq_true htimeout
    rcases hlock with hnone | haligned
    · cases htarget : Lambda.target H with
      | none =>
          cases nu with
          | false =>
              exact Or.inl
                (facts.vc.height_pair_eq_target_of_no_lock_no_target_justifiable
                  Lambda fp htimeoutFalse hnone htarget)
          | true =>
              exact Or.inr
                (facts.vc.height_pair_eq_timeout_of_no_lock_no_target_nonjustifiable
                  Lambda fp htimeoutFalse hnone htarget)
      | some recorded =>
          by_cases heq : recorded = T
          · subst recorded
            exact Or.inl
              (facts.vc.height_pair_eq_target_of_no_lock_recorded_target
                Lambda fp htimeoutFalse hnone htarget)
          · exact Or.inr
              (facts.vc.height_pair_eq_timeout_of_no_lock_off_target_record
                Lambda fp htimeoutFalse hnone htarget heq)
    · exact Or.inl
        (facts.vc.height_pair_eq_target_of_aligned_lock
          Lambda fp htimeoutFalse haligned)

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Protocol (ChainState HeightConfig)
open Protocol (Record height_pair own_lock)

/-- For every outcome `A` of the round action and every source `F` the action can select, `A`'s
    height pair is the codec `M.encodeHeight` of the height fields of `F`, together with the height
    pair `M.height_pair` computes from the legacy record, those fields and `A`'s finality pair. -/
theorem Vocabulary.Proofs.HealingSurface.named_round_action_height_pair (facts : Record.Facts M) (contract : M.Contract)
    (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V)
    (st : M.HS) (record : M.NR)
    (A : M.NR × NamedAttestation V) (hA : M.round_action_with contract E hc nd st record ⇢ A)
    (F : Option (Block V))
    (hF : Restated.Vocabulary.Proofs.HealingSurface.actionSource M contract E hc st ⇢ F) :
    A.2.height_pair =
      M.encodeHeight
        (F.map (fun Q => ((st.σ Q).h, (st.σ Q).T_h.root, (st.σ Q).nj)))
        (M.height_pair record.legacy
          (F.map (fun Q => ((st.σ Q).h, (st.σ Q).T_h.root, (st.σ Q).nj)))
          A.2.finality_pair) := by
  obtain ⟨g, hg, hF'⟩ := returns_bind_elim _ _ _ hF
  exact facts.dt.named_round_action_height_pair contract E hc nd st record A hA g hg F hF'

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Protocol (ChainState HeightConfig)
open Protocol (Record height_pair own_lock)

/-- For every outcome `A` of the round action, if the action can select the source `Q` and the own
    lock at `Q`'s height under `A`'s finality pair is empty or `Q`'s height target root, then `A`'s
    height pair is the vote for `Q`'s height and target root, with the bit `false` or `true`. -/
theorem Vocabulary.Proofs.HealingSurface.round_action_height_pair_target_or_timeout_of_source_lock_none_or_aligned (facts : Record.Facts M)
    (contract : M.Contract)
    (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V)
    (st : M.HS) (record : M.NR)
    (A : M.NR × NamedAttestation V) (hA : M.round_action_with contract E hc nd st record ⇢ A)
    {Q : Block V}
    (hsource : Restated.Vocabulary.Proofs.HealingSurface.actionSource M contract E hc st ⇢ some Q)
    (hlock : M.own_lock record.legacy (st.σ Q).h A.2.finality_pair = none ∨
      M.own_lock record.legacy (st.σ Q).h A.2.finality_pair = some (st.σ Q).T_h.root) :
    A.2.height_pair = NamedHeightPair.vote (st.σ Q).h (st.σ Q).T_h.root false ∨
      A.2.height_pair = NamedHeightPair.vote (st.σ Q).h (st.σ Q).T_h.root true := by
  rw [Restated.Vocabulary.Proofs.HealingSurface.named_round_action_height_pair facts contract E hc nd
    st record A hA (some Q) hsource, Option.map_some]
  rcases Restated.Vocabulary.Proofs.HealingSurface.height_pair_target_or_timeout_of_fields_some_and_lock_none_or_aligned facts
      record.legacy (st.σ Q).h (st.σ Q).T_h.root (st.σ Q).nj
      A.2.finality_pair hlock with htarget | htimeout
  · exact Or.inl (by rw [htarget]; exact facts.vc.encodeHeight_of_target)
  · exact Or.inr (by rw [htimeout]; exact facts.vc.encodeHeight_of_timeout)

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Protocol (ChainState HeightConfig)
open Protocol (Record height_pair own_lock)

/-- For every source `F` the action can select and every outcome `A` of the round action, either `F`
    is none and `A`'s height pair is empty, or `F` is some `Q` and either the own lock at `Q`'s
    height under `A`'s finality pair is a block other than `Q`'s height target root with no timeout
    at that height and `A`'s height pair is empty, or `A`'s height pair is the vote for `Q`'s height
    and target root with the bit `false` or `true`. -/
theorem Vocabulary.Proofs.HealingSurface.round_action_height_pair_cases (facts : Record.Facts M)
    (contract : M.Contract)
    (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V)
    (st : M.HS) (record : M.NR)
    (F : Option (Block V))
    (hF : Restated.Vocabulary.Proofs.HealingSurface.actionSource M contract E hc st ⇢ F)
    (A : M.NR × NamedAttestation V) (hA : M.round_action_with contract E hc nd st record ⇢ A) :
    (F = none ∧ A.2.height_pair = NamedHeightPair.empty) ∨
      ∃ Q, F = some Q ∧
        ((∃ locked,
            record.legacy.timeout (st.σ Q).h = false ∧
            M.own_lock record.legacy (st.σ Q).h A.2.finality_pair = some locked ∧
            locked ≠ (st.σ Q).T_h.root ∧
            A.2.height_pair = NamedHeightPair.empty) ∨
          A.2.height_pair = NamedHeightPair.vote (st.σ Q).h (st.σ Q).T_h.root false ∨
          A.2.height_pair = NamedHeightPair.vote (st.σ Q).h (st.σ Q).T_h.root true) := by
  obtain ⟨g, hg, hF'⟩ := returns_bind_elim _ _ _ hF
  exact facts.vc.round_action_height_pair_cases contract E hc nd st record g hg F hF' A hA

end

end DecoupledConsensusModel.Sts.Restated
