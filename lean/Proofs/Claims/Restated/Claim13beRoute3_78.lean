import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bK_FgJustified
import Proofs.Claims.Restated.Claim13bSGCompatible
import Proofs.Claims.Restated.Claim13bStepAnchor
import Proofs.Claims.Restated.Claim13bStepSGMove
import Proofs.Claims.Restated.Claim13beRoute3_44
import Proofs.Claims.Restated.Claim13beRoute3_58
import Proofs.Claims.Restated.Claim13beRoute3_70
import Proofs.Claims.Restated.Claim13beRoute3_71
import Proofs.Claims.Restated.Claim13beRoute3_72
import Proofs.Claims.Restated.Claim13beRoute3_73
import Proofs.Claims.Restated.Claim13beRoute3_74
import Proofs.Claims.Restated.Claim13beRoute3_75
import Proofs.Claims.Restated.ProcessIdempotent
import Proofs.Claims.Restated.Projection
import Proofs.Claims.Restated.RunAll
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Proofs.Claims.Restated.Vocabulary_Execution_PreparedReadBridge
import Proofs.Claims.Restated.Vocabulary_ModelVocabulary_Healing_Schedule
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_JustificationCarrier
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.Claim13beRoute3_72
import Model.Conditions.RunAll
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedHeadReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_Grades_ProposalLifecycleCore
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_Handlers_TickBridges
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_78

/-!
# The checkpoint and the switch round's second slot

Theorems over a model `M : Record.Model V` and its facts, for a regime along
`runAllPath M S Sched x v N`: the FG roots of the honest votes and actions at the switch round are
ancestors of the regime's checkpoint `T`, and the honest Goldfish votes of the switch round's second
slot descend from `T` or from an honest round-`rW` SG block. The file also holds facts relating the
vote, confirmation and action instants.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

local macro "p63% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_63)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p65% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_65)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p69b% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_69b)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p72% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_72)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p73% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_73)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p74% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_74)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- For every node state `b` and slot `d`, the cache update at `d`'s vote instant has an outcome
    `cc`, and at the node state staged from `b` with `cc` the voter's filtered tree, its two views
    and the in-tree head each have an outcome. -/
private theorem exists_voteHead₇₈ (facts : Record.Facts M)
    (S : Setup V) (b : M.N) (d : Slot) :
    ∃ cc : M.Cache,
      M.onPhaseTick S.E S.hc b.st.core.toHealing (M.vote_time S.E d) b.cache ⇢ cc ∧
      ∃ Tr : Finset (Block V),
        M.voter_filtered_block_tree S.E
          (M.mkNode (M.ns_setClock S.E b.st (M.vote_time S.E d)) b.record cc).st.core
          (M.mkNode (M.ns_setClock S.E b.st (M.vote_time S.E d)) b.record cc).st.core.s ⇢ Tr ∧
      ∃ L : Finset (GoldfishVote V),
        M.voter_view S.E
          (M.toHealing (M.mkNode (M.ns_setClock S.E b.st (M.vote_time S.E d)) b.record
            cc).st.core).toFG.toSG.toGoldfishStore
          (M.mkNode (M.ns_setClock S.E b.st (M.vote_time S.E d)) b.record cc).st.core.s ⇢ L ∧
      ∃ L' : Finset (GoldfishVote V),
        M.voter_support_view S.E
          (M.toHealing (M.mkNode (M.ns_setClock S.E b.st (M.vote_time S.E d)) b.record
            cc).st.core).toFG.toSG.toGoldfishStore
          (M.mkNode (M.ns_setClock S.E b.st (M.vote_time S.E d)) b.record cc).st.core.s ⇢ L' ∧
      ∃ H : Block V,
        M.get_head_in_tree_with_layer
          (M.gradeContract (M.mkNode (M.ns_setClock S.E b.st (M.vote_time S.E d)) b.record cc).cache)
          S.E S.hc
          (M.toHealing (M.mkNode (M.ns_setClock S.E b.st (M.vote_time S.E d)) b.record cc).st.core)
          Tr L L'
          ((M.mkNode (M.ns_setClock S.E b.st (M.vote_time S.E d)) b.record cc).st.core.s - 1) ⇢ H := by
  obtain ⟨cc, hcc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc b.st.core.toHealing
    (M.vote_time S.E d) b.cache
  obtain ⟨Tr, hTr⟩ := facts.fc.voter_filtered_block_tree_nonempty S.E
    (M.mkNode (M.ns_setClock S.E b.st (M.vote_time S.E d)) b.record cc).st.core
    (M.mkNode (M.ns_setClock S.E b.st (M.vote_time S.E d)) b.record cc).st.core.s
  obtain ⟨L, hL⟩ := facts.fc.voter_view_nonempty S.E
    (M.toHealing (M.mkNode (M.ns_setClock S.E b.st (M.vote_time S.E d)) b.record
      cc).st.core).toFG.toSG.toGoldfishStore
    (M.mkNode (M.ns_setClock S.E b.st (M.vote_time S.E d)) b.record cc).st.core.s
  obtain ⟨L', hL'⟩ := facts.fc.voter_support_view_nonempty S.E
    (M.toHealing (M.mkNode (M.ns_setClock S.E b.st (M.vote_time S.E d)) b.record
      cc).st.core).toFG.toSG.toGoldfishStore
    (M.mkNode (M.ns_setClock S.E b.st (M.vote_time S.E d)) b.record cc).st.core.s
  obtain ⟨H, hH⟩ := facts.fc.get_head_in_tree_with_layer_nonempty
    (M.gradeContract (M.mkNode (M.ns_setClock S.E b.st (M.vote_time S.E d)) b.record cc).cache)
    S.E S.hc
    (M.toHealing (M.mkNode (M.ns_setClock S.E b.st (M.vote_time S.E d)) b.record cc).st.core)
    Tr L L'
    ((M.mkNode (M.ns_setClock S.E b.st (M.vote_time S.E d)) b.record cc).st.core.s - 1)
  exact ⟨cc, hcc, Tr, hTr, L, hL, L', hL', H, hH⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- The Goldfish vote instant of slot `opening_slot c + 1` is strictly before the round-`c` action
    instant. -/
theorem vote_time_openingSucc_lt_action_l78 (facts : Record.Facts M) (S : Setup V) (c : Round) :
    M.vote_time S.E ((M.opening_slot S.hc c) + 1) < (Restated.Vocabulary.Execution.Setup.a M S c) := by
  have hSc : (Restated.Vocabulary.Execution.Setup.a M S c) = M.confirmation_time S.E ((M.opening_slot S.hc c)) := by
    rw [Restated.Vocabulary.Execution.Setup.a, facts.sch.a_eq_confirmation_time]
  obtain ⟨-, -, -, -, hv, hc⟩ := facts.sch.slot_instants_l55 S.E (M.opening_slot S.hc c)
  have hΔ := S.E.Δ_pos
  rw [hSc, hv, hc]
  linarith

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- If `s ≤ s'`, then `vote_time s + Δ ≤ confirmation_time s'`. -/
theorem vote_time_add_delta_le_confirmation_l78 (facts : Record.Facts M) (S : Setup V) {s s' : Slot} (h : s ≤ s') :
    M.vote_time S.E s + S.E.Δ ≤ M.confirmation_time S.E s' :=
  (facts.sch.vote_time_add_delta_le_confirmation_time S s).trans (facts.sch.confirmation_time_mono_l78 S h)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- In a valid execution with monotone corruption and the adversary's weight less than a third at
    `x[m].time`, for a validator `w` honest through step `m ≤ n₀ + 1`: if every honest height vote
    signed up to step `n₀ + 1` is at most `T`'s height, every such vote at `T`'s height names an
    ancestor of `T`, and `w`'s justified block after `m` steps is on one chain with `T`, then that
    justified block is an ancestor of `T`. -/
theorem justified_preceq_checkpoint_of_compatible_l78 (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) {m n₀ : Nat} (hm : m ≤ n₀ + 1)
    (hthirdm : 3 * S.E.electorate.weightOf (Sched.adv (x[m].time : Int)) <
      S.E.electorate.totalWeight)
    {w : V} (hw : Restated.HonestThrough M Sched x m w) {T : NamedBlock V}
    (hTlog : Restated.blockInLog M S Sched x T)
    (hceil : ∀ (v' : V) (n' : Nat) (a : NamedAttestation V) (h' : Height)
      (entry : BlockId) (tmo : Bool),
      n' ≤ n₀ + 1 → Restated.HonestThrough M Sched x n' v' → a.val_index = v' →
      (⟨v', NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n'].sent →
      a.height_pair = NamedHeightPair.vote h' entry tmo →
      h' ≤ (M.derive_named S.E S.cfg T).h)
    (htargets : ∀ (v' : V) (n' : Nat) (b : NamedAttestation V) (entry : BlockId) (tmo : Bool),
      n' ≤ n₀ + 1 → Restated.HonestThrough M Sched x n' v' → b.val_index = v' →
      (⟨v', NamedObject.attest b⟩ : SignedMsg V (NamedObject V)) ∈ x[n'].sent →
      b.height_pair = NamedHeightPair.vote (M.derive_named S.E S.cfg T).h entry tmo →
      ∀ C : NamedBlock V, Restated.blockInLog M S Sched x C → C.root = entry →
        Block.Preceq C.erase T.erase)
    (hcomp : Block.compatible (x[m][w].st).st.core.J T.erase = true) :
    Block.Preceq (x[m][w].st).st.core.J T.erase := by
  classical
  rcases Restated.justified_certificate_sts facts S Sched x hvalid hw with
    hgen | ⟨Jn, hJnmem, hJne, -, Q, hQ, hsign⟩
  · rw [hgen]
    exact (preceq_eq_true_iff_Preceq.mp (Protocol.preceq_genesis _))
  obtain ⟨q, hqQ, hqT⟩ := exists_nonAdv_of_quorum_upTo S Sched hmono hthirdm hQ
  have hqm : Restated.HonestThrough M Sched x m q := fun t ht => hqT t ht
  obtain ⟨carrier, a, hcarrier, ha, hval, hpair⟩ := hsign q hqQ
  have hsent : (⟨q, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[m].sent := by
    have h := Restated.carried_vote_in_log facts S Sched x hvalid hcarrier ha (by rw [hval]; exact hqm)
    rw [hval] at h
    exact h
  have hle : (x[m][w].st).st.core.h_j ≤ (M.derive_named S.E S.cfg T).h :=
    hceil q m a _ Jn.root false hm hqm hval hsent hpair
  rcases Nat.lt_or_ge (x[m][w].st).st.core.h_j (M.derive_named S.E S.cfg T).h with
    hlt | hge
  ·
    obtain ⟨D, hDmem, hDJ, hDh⟩ : ∃ D : NamedBlock V, D ∈ (x[m][w].st).st.bodies ∧
        (M.derive_named S.E S.cfg D).J = (x[m][w].st).st.core.J ∧
        (M.derive_named S.E S.cfg D).h_j = (x[m][w].st).st.core.h_j := by
      obtain ⟨w₁, hw₁, hwv⟩ := Record.stateBeforeOf_runOfM M S Sched x facts.nd.wake_events_or_id w m
      have h := Restated.Vocabulary.Proofs.NamedJustificationCarrier.justification_carrier_stateBefore facts
        (Setup.alwaysAwake S) (Record.runOfM M S Sched x w m) (Record.veventsOf M S Sched x w m).length w
        w₁ hw₁
      rw [hwv] at h
      exact h
    rcases facts.cs.justified_ancestor_height S.E S.cfg D with
      h0 | ⟨J', hJ'D, hJ'e, hJ'h⟩
    · rw [← hDJ, facts.cs.justified_zero_is_genesis S.E S.cfg D h0]
      exact (preceq_eq_true_iff_Preceq.mp (Protocol.preceq_genesis _))
    · rcases compatible_cases hcomp with hJT | hTJ
      · exact hJT
      · exfalso
        have hcl : Restated.Vocabulary.Proofs.NamedStore.NamedParentClosed M (x[m][w].st).st :=
          (Restated.nodeInvariant_sts facts S Sched x m w).1.1.1.2.2.1
        have hJ'mem : J' ∈ (x[m][w].st).st.bodies := Restated.mem_bodies_of_preceq hcl hDmem hJ'D
        have hJ'log : Restated.blockInLog M S Sched x J' := Restated.blockInLog_of_mem_bodies facts S Sched hw hJ'mem
        have hTJ' : Block.Preceq T.erase J'.erase := by
          rw [hJ'e, hDJ]
          exact hTJ
        have hnamed : NamedBlock.Preceq T J' :=
          Restated.namedPreceq_of_blockInLog facts S Sched x hvalid.idealization hTlog hJ'log hTJ'
        have hh := facts.cs.derive_height_mono S.E S.cfg hnamed
        rw [hJ'h, hDh] at hh
        exact Nat.lt_irrefl _ (lt_of_lt_of_le hlt hh)
  ·
    have heq : (x[m][w].st).st.core.h_j = (M.derive_named S.E S.cfg T).h :=
      le_antisymm hle hge
    rw [heq] at hpair
    rw [← hJne]
    exact htargets q m a Jn.root false hm hqm hval hsent hpair Jn
      (Restated.blockInLog_of_mem_bodies facts S Sched hw hJnmem) rfl

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- A store's FG root is its justified block when `h_max = h_j + 1`, and its finalized block
    otherwise. -/
theorem get_fg_root_eq_ite_l78 (facts : Record.Facts M) (st : M.S) :
    M.get_fg_root (M.toHealing st).toFG =
      if st.h_max = st.h_j + 1 then st.J else st.F := by
  split_ifs with h
  · exact facts.fc.get_fg_root_toHealing_of_eq st h
  · exact facts.fc.get_fg_root_toHealing_of_ne st h

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- Given the hypotheses of `justified_preceq_checkpoint_of_compatible_l78`, if `w`'s finalized
    block after `m` steps is an ancestor of `T` and its FG root is on one chain with `T`, then its
    FG root is an ancestor of `T`. -/
theorem fgRoot_preceq_checkpoint_of_compatible_l78 (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) {m n₀ : Nat} (hm : m ≤ n₀ + 1)
    (hthirdm : 3 * S.E.electorate.weightOf (Sched.adv (x[m].time : Int)) <
      S.E.electorate.totalWeight)
    {w : V} (hw : Restated.HonestThrough M Sched x m w) {T : NamedBlock V}
    (hTlog : Restated.blockInLog M S Sched x T)
    (hceil : ∀ (v' : V) (n' : Nat) (a : NamedAttestation V) (h' : Height)
      (entry : BlockId) (tmo : Bool),
      n' ≤ n₀ + 1 → Restated.HonestThrough M Sched x n' v' → a.val_index = v' →
      (⟨v', NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n'].sent →
      a.height_pair = NamedHeightPair.vote h' entry tmo →
      h' ≤ (M.derive_named S.E S.cfg T).h)
    (htargets : ∀ (v' : V) (n' : Nat) (b : NamedAttestation V) (entry : BlockId) (tmo : Bool),
      n' ≤ n₀ + 1 → Restated.HonestThrough M Sched x n' v' → b.val_index = v' →
      (⟨v', NamedObject.attest b⟩ : SignedMsg V (NamedObject V)) ∈ x[n'].sent →
      b.height_pair = NamedHeightPair.vote (M.derive_named S.E S.cfg T).h entry tmo →
      ∀ C : NamedBlock V, Restated.blockInLog M S Sched x C → C.root = entry →
        Block.Preceq C.erase T.erase)
    (hF : Block.Preceq (x[m][w].st).st.core.F T.erase)
    (hcomp : Block.compatible
      (M.get_fg_root (M.toHealing (x[m][w].st).st.core).toFG) T.erase = true) :
    Block.Preceq (M.get_fg_root (M.toHealing (x[m][w].st).st.core).toFG) T.erase := by
  rw [Restated.get_fg_root_eq_ite_l78 facts] at hcomp ⊢
  by_cases hroot : (x[m][w].st).st.core.h_max = (x[m][w].st).st.core.h_j + 1
  · rw [if_pos hroot] at hcomp ⊢
    exact Restated.justified_preceq_checkpoint_of_compatible_l78 facts S Sched x hvalid hmono hm hthirdm hw
      hTlog hceil htargets hcomp
  · rw [if_neg hroot]
    exact hF

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- In the regime `hreg` along `runAllPath M S Sched x v N`, with `rW = switchRound M S tE`, a
    source round at or before `rW`, and `topHonestRow` at the tick step `n₀` of `S.a rW` at most
    `T`'s height: every validator `w` in `notHeldAt Sched` at the vote instant of slot
    `opening_slot rW + 1` has, at its vote store of that slot computed in the path's world before
    that instant, an FG root that is an ancestor of `T`. -/
theorem fgRoot_comparable_anchor_at_secondSlot (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V)
    {tGAT tE : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (htd : Restated.TimeDiverges M x)
    {N : Nat}
    (hN : (x[N].time : Int)
      = M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 2))
    {blocked : Height} {first i : Nat} {a : NamedAttestation V} {ta : Int}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hreg : Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N)
      (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
      (notHeldAt Sched) Finset.univ Finset.univ
      (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0)
    (harW : a.round ≤ Restated.switchRound M S tE)
    {n₀ : Nat} (hn₀ : Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    (htop : Restated.topHonestRow M S Sched x n₀ ≤ (M.derive_named S.E S.cfg T).h) :
    ∀ w ∈ notHeldAt Sched (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1)),
      Block.Preceq (M.get_fg_root
        (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M (Setup.alwaysAwake S)
          (Restated.runAllPath M S Sched x v N
            (Restated.strictEventIndex
              ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
              (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))) w).st.core
          ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))).toFG) T.erase := by
  intro w hw
  obtain ⟨N', hN', hN'E, -, -, -, -, -⟩ := Restated.switchRound_instants facts S Sched x tGAT tE gap
    ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
    hgst hlen htd
  have hn : (x[N].time : Int) ≤ tE := by rw [hN.trans hN'.symm]; exact hN'E
  have hf := Restated.admissibleFieldsOn_runAll_notHeld facts S Sched x v N hsync hmono hawake hgst hcv hvalid
    hawm hthird hn
  have hHs : ∀ t t' : Int, t ≤ t' → notHeldAt Sched t' ⊆ notHeldAt Sched t :=
    fun _ _ h => notHeldAt_anti hmono h
  have hHsXb : ∀ t : Int, notHeldAt Sched t ⊆ (Finset.univ : Finset V) :=
    fun _ => Finset.subset_univ _
  have hX : ∀ t : Int, 0 ≤ t → notHeldAt Sched t ⊆ (Finset.univ : Finset V) :=
    fun _ _ => Finset.subset_univ _
  have hXXb : (Finset.univ : Finset V) ⊆ Finset.univ := Finset.Subset.refl _
  have hcomOn := Restated.honestCommitteesOn_notHeld facts S Sched hcom
  have hbelow := Restated.belowOneThirdOn_runAll_notHeld facts S Sched x v N hthird hn
  obtain ⟨-, -, hloOpen, -⟩ := Restated.roundAt_bounds_l71 facts S hgst
  have hlo := hreg.lo_le_opening_l71 facts hf hloOpen
  have hdlo : (M.opening_slot S.hc a.round) + 1 ≤ (M.opening_slot S.hc (Restated.switchRound M S tE)) + 1 :=
    Nat.add_le_add_right (facts.gr.opening_slot_mono S harW) 1
  have hhor : M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) + S.E.Δ ≤
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } :
        Record.Run V).horizon := by
    show _ ≤ (x[N].time : Int)
    rw [hN]
    exact Restated.vote_time_add_delta_le_confirmation_l78 facts S (Nat.le_succ _)
  have hTw := hreg.heads_from_firstInterior facts hf hHs hHsXb hX hXXb hcomOn hbelow hdlo hhor hlo
    (fun k hk u _ j hj => Restated.awake_g2_action_runAllPath facts S Sched x v N hmono hawake hn
        k hk u j hj) w hw
  obtain ⟨m, hm⟩ : ∃ m : Nat,
      Restated.tickStepAt M x m (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1)) :=
    Restated.exists_tickStepAt facts x htd
      (facts.sch.vote_time_pos S (Nat.succ_pos ((M.opening_slot S.hc (Restated.switchRound M S tE)))))
  obtain ⟨hm1, hm0⟩ := Restated.tickStepAt_time facts x hm
  obtain ⟨hn₀1, -⟩ := Restated.tickStepAt_time facts x hn₀
  have hvA := Restated.vote_time_openingSucc_lt_action_l78 facts S (Restated.switchRound M S tE)
  have hmn₀ : m + 1 ≤ n₀ + 1 := by
    by_contra hcon
    have hle : ((x[n₀ + 1].time : Nat) : Int) ≤ ((x[m + 1].time : Nat) : Int) := by
      exact_mod_cast Restated.time_mono facts S Sched x (by omega)
    linarith
  have hn₀N := Restated.succ_le_of_tick_switchRound_l74 facts S Sched x hn₀ hN
  have hmN : m + 1 ≤ N := by omega
  have hread := Restated.stateBeforeTime_runAll_tick facts S Sched x v hm hmN w
  have hwA : w ∉ Sched.adv
      (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1)) :=
    mem_notHeldAt.mp hw
  have hmtime : (x[m].time : Int) ≤
      M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) := by
    linarith
  have hwm : Restated.HonestThrough M Sched x m w := by
    intro t' ht' hmem'
    exact hwA (hmono t' _ (ht'.trans hmtime) hmem')
  have hmE : (x[m].time : Int) ≤ tE := by
    have hle : ((x[m].time : Nat) : Int) ≤ ((x[N].time : Nat) : Int) := by
      exact_mod_cast Restated.time_mono facts S Sched x (by omega)
    linarith
  have hrootEq : M.get_fg_root
      (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M (Setup.alwaysAwake S)
        (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))) w).st.core
        ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))).toFG =
      M.get_fg_root (M.toHealing (x[m][w].st).st.core).toFG := by
    rw [hread]
    exact facts.fc.get_fg_root_toHealing_clock _ _ _
  have hsorted := Restated.sorted_runAll_withHonest_events facts S Sched x v
    (notHeldAt Sched (x[N].time : Int)) N
  have hP : Restated.Vocabulary.Execution.NamedRun.OnePath M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N) := Restated.OnePath_runAllPath facts S Sched x v N
  have hmemW := (p69b% mem_stateBeforeTime_along₆₉b) hsorted hP
    (M.vote_time (Setup.alwaysAwake S).E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))
  obtain ⟨cc, hcc⟩ := facts.gr.onPhaseTick_nonempty (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc
    (Restated.runAllPath M S Sched x v N
      (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))) w).st.core.toHealing
    (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))
    (Restated.runAllPath M S Sched x v N
      (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))) w).cache
  obtain ⟨nd, hnd⟩ : ∃ nd : M.N, nd = M.mkNode
      (M.ns_setClock S.E (Restated.runAllPath M S Sched x v N
        (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
          (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))) w).st
        (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1)))
      (Restated.runAllPath M S Sched x v N
        (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
          (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))) w).record cc :=
    ⟨_, rfl⟩
  have hndmem : nd ∈ Restated.Vocabulary.Internal.NamedRecoveryRead.voteDutyRead M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      w ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) :=
    ⟨_, hmemW, cc, hcc, hnd⟩
  obtain ⟨Tr, hTr⟩ := facts.fc.voter_filtered_block_tree_nonempty S.E nd.st.core nd.st.core.s
  obtain ⟨L, hL⟩ := facts.fc.voter_view_nonempty S.E
    (M.toHealing nd.st.core).toFG.toSG.toGoldfishStore nd.st.core.s
  obtain ⟨L', hL'⟩ := facts.fc.voter_support_view_nonempty S.E
    (M.toHealing nd.st.core).toFG.toSG.toGoldfishStore nd.st.core.s
  obtain ⟨H, hH⟩ := facts.fc.get_head_in_tree_with_layer_nonempty (M.gradeContract nd.cache) S.E S.hc
    (M.toHealing nd.st.core) Tr L L' (nd.st.core.s - 1)
  have hRH := Restated.Vocabulary.Proofs.HealingSurface.fgRoot_preceq_voterHeadAt facts (Setup.alwaysAwake S)
    _ w _ nd hndmem Tr hTr L hL L' hL' H hH
  have hTH : Block.Preceq T.erase H := by
    subst hnd
    exact hTw cc hcc Tr hTr L hL L' hL' H hH
  have hrootNd : M.get_fg_root (M.toHealing nd.st.core).toFG =
      M.get_fg_root (M.toHealing (x[m][w].st).st.core).toFG := by
    rw [hnd, ((p65% dutyNode_parts₆₅) facts S _ _ cc).2.2.2.2.2, hread]
  have hcomp : Block.compatible
      (M.get_fg_root (M.toHealing (x[m][w].st).st.core).toFG) T.erase = true := by
    rw [← hrootNd]
    exact compatible_of_preceq_common_Preceq hRH hTH
  have hF := Restated.fin_at_switchRound_of_regime facts S Sched x v hsync hmono hawake hgst hcv hvalid hawm
    hthird hcom hlen htd hN hreg hn₀ htop w m (by omega) hwm
  rw [hrootEq]
  exact Restated.fgRoot_preceq_checkpoint_of_compatible_l78 facts S Sched x hvalid hmono (n₀ := n₀) (by omega)
    (hthird _ hmE) hwm (Restated.inPlay_at_switchRound_of_regime facts S Sched x v hmono hreg)
    (Restated.heightCeiling_of_topHonestRow facts S Sched x hvalid.toUnforgeability htop)
    (Restated.targetsTop_at_switchRound facts S Sched x v hsync hmono hawake hgst hcv hvalid hawm hthird hcom
      hlen htd hN hreg hn₀) hF hcomp

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- For every world `w₀` that can hold before slot `s`'s vote instant and every outcome `c` of the
    cache update there, the FG root of `w`'s vote-duty read built from `w₀` and `c` is the FG root
    of `voteStore` of `w`'s core store in `w₀`. -/
theorem fgRoot_voteDutyRead_eq_l78 (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (w : V) (s : Slot) :
    ∀ w₀ ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho (M.vote_time S.E s),
    ∀ c : M.Cache,
      M.onPhaseTick S.E S.hc (w₀ w).st.core.toHealing (M.vote_time S.E s) (w₀ w).cache ⇢ c →
    M.get_fg_root
        (M.toHealing (M.mkNode (M.ns_setClock S.E (w₀ w).st (M.vote_time S.E s))
          (w₀ w).record c).st.core).toFG =
      M.get_fg_root (M.toHealing
        (Restated.Vocabulary.Proofs.Optimistic.voteStore M S (w₀ w).st.core s)).toFG := by
  intro w₀ _ c _
  rw [((p65% dutyNode_parts₆₅) facts S (w₀ w) s c).2.2.2.2.2]
  exact (facts.fc.get_fg_root_toHealing_clock _ _ _).symm

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- In the regime `hreg` along `runAllPath M S Sched x v N`, with `rW = switchRound M S tE` and a
    source round before `rW`: for every validator `u` in `notHeldAt Sched` at the vote instant of
    slot `opening_slot rW`, every head `u`'s vote duty of that slot can return, staged from the
    path's world before that instant, descends from `T`. -/
theorem headsAtOpening_of_regime_l78 (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V)
    {tGAT tE : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (htd : Restated.TimeDiverges M x)
    {N : Nat}
    (hN : (x[N].time : Int)
      = M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 2))
    {blocked : Height} {first i : Nat} {a : NamedAttestation V} {ta : Int}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hreg : Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N)
      (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
      (notHeldAt Sched) Finset.univ Finset.univ
      (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0)
    (hbefore : a.round + 1 ≤ Restated.switchRound M S tE) :
    ∀ u ∈ notHeldAt Sched (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)))),
    ∀ cc : M.Cache,
      M.onPhaseTick S.E S.hc
        (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))))) u).st.core.toHealing
        (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))))
        (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))))) u).cache ⇢ cc →
      let n := M.mkNode
        (M.ns_setClock S.E (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))))) u).st
          (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)))))
        (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))))) u).record cc
      ∀ Tr : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ Tr →
      ∀ L : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
      ∀ L' : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
      ∀ H : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
          (M.toHealing n.st.core) Tr L L' (n.st.core.s - 1) ⇢ H →
        Block.Preceq T.erase H := by
  obtain ⟨N', hN', hN'E, -, -, -, -, -⟩ := Restated.switchRound_instants facts S Sched x tGAT tE gap
    ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
    hgst hlen htd
  have hn : (x[N].time : Int) ≤ tE := by rw [hN.trans hN'.symm]; exact hN'E
  have hf := Restated.admissibleFieldsOn_runAll_notHeld facts S Sched x v N hsync hmono hawake hgst hcv hvalid
    hawm hthird hn
  have hHs : ∀ t t' : Int, t ≤ t' → notHeldAt Sched t' ⊆ notHeldAt Sched t :=
    fun _ _ h => notHeldAt_anti hmono h
  have hHsXb : ∀ t : Int, notHeldAt Sched t ⊆ (Finset.univ : Finset V) :=
    fun _ => Finset.subset_univ _
  have hX : ∀ t : Int, 0 ≤ t → notHeldAt Sched t ⊆ (Finset.univ : Finset V) :=
    fun _ _ => Finset.subset_univ _
  have hXXb : (Finset.univ : Finset V) ⊆ Finset.univ := Finset.Subset.refl _
  have hcomOn := Restated.honestCommitteesOn_notHeld facts S Sched hcom
  have hbelow := Restated.belowOneThirdOn_runAll_notHeld facts S Sched x v N hthird hn
  obtain ⟨-, -, hloOpen, -⟩ := Restated.roundAt_bounds_l71 facts S hgst
  have hlo := hreg.lo_le_opening_l71 facts hf hloOpen
  have hdlo : (M.opening_slot S.hc a.round) + 1 ≤ (M.opening_slot S.hc (Restated.switchRound M S tE)) :=
    (facts.gr.opening_slot_succ_le_l78 S a.round).trans (facts.gr.opening_slot_mono S hbefore)
  have hhor : M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))) + S.E.Δ ≤
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } :
        Record.Run V).horizon := by
    show _ ≤ (x[N].time : Int)
    rw [hN]
    exact Restated.vote_time_add_delta_le_confirmation_l78 facts S (Nat.le_add_right _ 2)
  exact hreg.heads_from_firstInterior facts hf hHs hHsXb hX hXXb hcomOn hbelow hdlo hhor hlo
    (fun k hk u _ j hj => Restated.awake_g2_action_runAllPath facts S Sched x v N hmono hawake hn
        k hk u j hj)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- The slot after an opening slot is in that opening's round: `round_of (opening_slot r + 1) = r`. -/
theorem round_of_openingSucc_l78 (facts : Record.Facts M) (S : Setup V) (r : Round) :
    (M.round_of S.hc ((M.opening_slot S.hc r) + 1)) = r :=
  facts.gr.round_of_eq_of_opening_succ_le_of_lt_next_opening S.hc le_rfl (facts.gr.opening_slot_succ_lt_l78 S r)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- A round's grade-1 domain instant is at or before the vote instant of the slot after its opening:
    `domain r g1 ≤ vote_time (opening_slot r + 1)`. -/
theorem domain_g1_le_vote_openingSucc_l78 (facts : Record.Facts M) (S : Setup V) (r : Round) :
    M.domain S.E S.hc r .g1 ≤
      M.vote_time S.E ((M.opening_slot S.hc r) + 1) := by
  rw [facts.gr.Sts_domain_g1_eq_opening, facts.gr.opening_eq_proposal_time]
  obtain ⟨-, -, -, -, hv, -⟩ := facts.sch.slot_instants_l55 S.E (M.opening_slot S.hc r)
  have hΔ := S.E.Δ_pos
  rw [hv]
  linarith

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- Along a path `W` of the run, if every honest vote of slot `s` is a run block descending from
    `T`, and `B` is an ancestor of `T`, then every such vote descends from `B`. -/
theorem namedHonestVotesConeOn_of_preceq_l78 (facts : Record.Facts M) {S : Setup V} {rho : Record.Run V}
    {W : Nat → V → M.N}
    {Hs : Int → Finset V} {Xb : Finset V} {s : Slot} {B T : Block V}
    (hBT : Block.Preceq B T)
    (h : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s (fun X => Block.Preceq T X)) :
    Restated.NamedHonestVotesConeOn M S rho W Hs Xb s (fun X => Block.Preceq B X) := by
  intro w hw hc
  obtain ⟨X, hX, hrun, hem⟩ := h w hw hc
  exact ⟨X, preceq_trans_Preceq hBT hX, hrun, hem⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- In the regime `hreg` along `runAllPath M S Sched x v N`, with `rW = switchRound M S tE` and a
    source round at or before `rW`: every committee member of slot `opening_slot rW + 1` in
    `notHeldAt Sched` at its vote instant votes there, along that path, a run block descending from
    `T`. -/
theorem checkpointCone_at_secondSlot (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V)
    {tGAT tE : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (htd : Restated.TimeDiverges M x)
    {N : Nat}
    (hN : (x[N].time : Int)
      = M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 2))
    {blocked : Height} {first i : Nat} {a : NamedAttestation V} {ta : Int}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hreg : Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N)
      (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
      (notHeldAt Sched) Finset.univ Finset.univ
      (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0)
    (harW : a.round ≤ Restated.switchRound M S tE) :
    Restated.NamedHonestVotesConeOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N)
      (notHeldAt Sched) Finset.univ ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1)
      (fun X => Block.Preceq T.erase X) := by
  obtain ⟨N', hN', hN'E, -, -, -, -, -⟩ := Restated.switchRound_instants facts S Sched x tGAT tE gap
    ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
    hgst hlen htd
  have hn : (x[N].time : Int) ≤ tE := by rw [hN.trans hN'.symm]; exact hN'E
  have hf := Restated.admissibleFieldsOn_runAll_notHeld facts S Sched x v N hsync hmono hawake hgst hcv hvalid
    hawm hthird hn
  have hHs : ∀ t t' : Int, t ≤ t' → notHeldAt Sched t' ⊆ notHeldAt Sched t :=
    fun _ _ h => notHeldAt_anti hmono h
  have hHsXb : ∀ t : Int, notHeldAt Sched t ⊆ (Finset.univ : Finset V) :=
    fun _ => Finset.subset_univ _
  have hX : ∀ t : Int, 0 ≤ t → notHeldAt Sched t ⊆ (Finset.univ : Finset V) :=
    fun _ _ => Finset.subset_univ _
  have hXXb : (Finset.univ : Finset V) ⊆ Finset.univ := Finset.Subset.refl _
  have hcomOn := Restated.honestCommitteesOn_notHeld facts S Sched hcom
  have hbelow := Restated.belowOneThirdOn_runAll_notHeld facts S Sched x v N hthird hn
  obtain ⟨-, -, hloOpen, -⟩ := Restated.roundAt_bounds_l71 facts S hgst
  have hlo := hreg.lo_le_opening_l71 facts hf hloOpen
  have hhor : M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) + S.E.Δ ≤
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } :
        Record.Run V).horizon := by
    show _ ≤ (x[N].time : Int)
    rw [hN]
    exact Restated.vote_time_add_delta_le_confirmation_l78 facts S (Nat.le_succ _)
  rcases Nat.lt_or_ge a.round (Restated.switchRound M S tE) with hlt | hge
  · have hr : (M.round_of (Setup.alwaysAwake S).hc ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1)) =
        Restated.switchRound M S tE := Restated.round_of_openingSucc_l78 facts S (Restated.switchRound M S tE)
    exact ((hreg.laterHistory_main facts hf hHs hHsXb hX hXXb hcomOn hbelow
      (Nat.succ_le_of_lt hlt) hlo (fun k hk u _ j hj => Restated.awake_g2_action_runAllPath facts S Sched x v N hmono hawake hn
        k hk u j hj)).1 _ hr hhor).2
  · have heq : a.round = Restated.switchRound M S tE := le_antisymm harW hge
    have hdlo : (M.opening_slot S.hc a.round) + 1 ≤ (M.opening_slot S.hc (Restated.switchRound M S tE)) + 1 := by
      rw [heq]
    have hdhi : (M.opening_slot S.hc (Restated.switchRound M S tE)) + 1 < (M.opening_slot S.hc (a.round + 1)) := by
      rw [heq]
      exact facts.gr.opening_slot_succ_lt_l78 S _
    exact (hreg.seed.checkpointProtection_sourceRound_of_frame_run facts hf hHs hHsXb hX hXXb hcomOn
      hbelow hreg.crossing hreg.frame hreg.c0le hreg.ready hreg.postPrev hreg.pred
      hreg.minimal hdlo hdhi hhor hlo (fun k hk u _ j hj => Restated.awake_g2_action_runAllPath facts S Sched x v N hmono hawake hn
        k hk u j hj)).2

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- In the regime `hreg` along `runAllPath M S Sched x v N`, with `rW = switchRound M S tE`: for
    every validator `v'` in `notHeldAt Sched` at `S.a rW`, every node state of its round-`rW` action
    read staged from the path's world before `S.a rW` has an FG root that is an ancestor of `T`. -/
theorem actionFgRoot_preceq_checkpoint_at_switchRound (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V)
    {tGAT tE : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (htd : Restated.TimeDiverges M x)
    {N : Nat}
    (hN : (x[N].time : Int)
      = M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 2))
    {blocked : Height} {first i : Nat} {a : NamedAttestation V} {ta : Int}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hreg : Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N)
      (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
      (notHeldAt Sched) Finset.univ Finset.univ
      (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0)
    (harW : a.round ≤ Restated.switchRound M S tE)
    {n₀ : Nat} (hn₀ : Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    (htop : Restated.topHonestRow M S Sched x n₀ ≤ (M.derive_named S.E S.cfg T).h) :
    ∀ v' ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))),
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) v')
        (Restated.switchRound M S tE),
      Block.Preceq (M.get_fg_root (M.toHealing n.st.core).toFG) T.erase := by
  intro v' hv' nd hnd
  obtain ⟨N', hN', hN'E, -, -, -, -, -⟩ := Restated.switchRound_instants facts S Sched x tGAT tE gap
    ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
    hgst hlen htd
  have hn : (x[N].time : Int) ≤ tE := by rw [hN.trans hN'.symm]; exact hN'E
  have hrWN : (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)) ≤ (x[N].time : Int) := by
    rw [hN]; exact Restated.action_le_confirmation_third facts S _
  have hf := Restated.admissibleFieldsOn_runAll_notHeld facts S Sched x v N hsync hmono hawake hgst hcv hvalid
    hawm hthird hn
  have hHs : ∀ t t' : Int, t ≤ t' → notHeldAt Sched t' ⊆ notHeldAt Sched t :=
    fun _ _ h => notHeldAt_anti hmono h
  have hHsXb : ∀ t : Int, notHeldAt Sched t ⊆ (Finset.univ : Finset V) :=
    fun _ => Finset.subset_univ _
  have hX : ∀ t : Int, 0 ≤ t → notHeldAt Sched t ⊆ (Finset.univ : Finset V) :=
    fun _ _ => Finset.subset_univ _
  have hXXb : (Finset.univ : Finset V) ⊆ Finset.univ := Finset.Subset.refl _
  have hcomOn := Restated.honestCommitteesOn_notHeld facts S Sched hcom
  have hbelow := Restated.belowOneThirdOn_runAll_notHeld facts S Sched x v N hthird hn
  obtain ⟨-, -, hloOpen, -⟩ := Restated.roundAt_bounds_l71 facts S hgst
  have hlo := hreg.lo_le_opening_l71 facts hf hloOpen
  have hreadHor : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (Restated.switchRound M S tE)) ≤
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } :
        Record.Run V).horizon := hrWN
  have hcompRead : Block.compatible (M.get_fg_root
      (M.toHealing (Restated.runAllPath M S Sched x v N
        (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
          (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) v').st.core).toFG)
      T.erase = true := by
    refine hreg.seed.fgRoot_compatible_of_recentWitnessHistory_of_frame_run facts hf hHs hHsXb hX
      hXXb hcomOn hbelow hreg.crossing hreg.frame hreg.c0le hreg.ready hreg.postPrev
      hreg.pred hreg.minimal (Restated.Vocabulary.Proofs.Assembly.a_mono facts S harW) ?_ hv' hreadHor hlo
      (fun k hk u _ j hj => Restated.awake_g2_action_runAllPath facts S Sched x v N hmono hawake hn
        k hk u j hj)
    intro r hr hrlt u hu B hB
    have hrHor : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) r) ≤
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } :
          Record.Run V).horizon := le_trans (le_of_lt hrlt) hrWN
    obtain ⟨nr, hnr⟩ := (p73% actionReadFrom_nonempty₇₃) facts (Setup.alwaysAwake S)
      (Restated.runAllPath M S Sched x v N
        (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
          (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) r)) u) r
    obtain ⟨o, ho⟩ := (p63% actionFGSource_nonempty₆₃w) facts (Setup.alwaysAwake S) nr
    exact ((hreg.laterHistory_main facts hf hHs hHsXb hX hXXb hcomOn hbelow hr hlo
      (fun k hk u _ j hj => Restated.awake_g2_action_runAllPath facts S Sched x v N hmono hawake hn
        k hk u j hj)).2 hrHor).2 u hu nr hnr B (hB nr hnr o ho)
  have hn₀N := Restated.succ_le_of_tick_switchRound_l74 facts S Sched x hn₀ hN
  have hread := Restated.stateBeforeTime_runAll_tick facts S Sched x v hn₀ hn₀N v'
  have hsorted := Restated.sorted_runAll_withHonest_events facts S Sched x v
    (notHeldAt Sched (x[N].time : Int)) N
  have hP : Restated.Vocabulary.Execution.NamedRun.OnePath M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N) := Restated.OnePath_runAllPath facts S Sched x v N
  have hmemW := (p69b% mem_stateBeforeTime_along₆₉b) hsorted hP
    (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (Restated.switchRound M S tE))
  have hrootNd : M.get_fg_root (M.toHealing nd.st.core).toFG =
      M.get_fg_root (M.toHealing (x[n₀][v'].st).st.core).toFG := by
    rw [← hread]
    exact Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt_fgRoot_eq_storeBeforeTime facts
      (Setup.alwaysAwake S) _ v' (Restated.switchRound M S tE) _ hmemW nd hnd
  obtain ⟨hn₀1, hn₀0⟩ := Restated.tickStepAt_time facts x hn₀
  have hvA : v' ∉ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) := mem_notHeldAt.mp hv'
  have hn₀time : (x[n₀].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)) := by linarith
  have hv'n₀ : Restated.HonestThrough M Sched x n₀ v' := by
    intro t' ht' hmem'
    exact hvA (hmono t' _ (ht'.trans hn₀time) hmem')
  have hn₀E : (x[n₀].time : Int) ≤ tE := hn₀time.trans (hrWN.trans hn)
  rw [hrootNd]
  rw [hread] at hcompRead
  exact Restated.fgRoot_preceq_checkpoint_of_compatible_l78 facts S Sched x hvalid hmono (n₀ := n₀)
    (Nat.le_succ n₀) (hthird _ hn₀E) hv'n₀ (Restated.inPlay_at_switchRound_of_regime facts S Sched x v hmono hreg)
    (Restated.heightCeiling_of_topHonestRow facts S Sched x hvalid.toUnforgeability htop)
    (Restated.targetsTop_at_switchRound facts S Sched x v hsync hmono hawake hgst hcv hvalid hawm hthird hcom
      hlen htd hN hreg hn₀)
    (Restated.fin_at_switchRound_of_regime facts S Sched x v hsync hmono hawake hgst hcv hvalid hawm hthird
      hcom hlen htd hN hreg hn₀ htop v' n₀ (Nat.le_succ n₀) hv'n₀)
    hcompRead

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- In the regime `hreg` along `runAllPath M S Sched x v N`, with `rW = switchRound M S tE`: for a
    validator `v'` in `notHeldAt Sched` at `S.a rW`, a node state `n` of its round-`rW` action read
    staged from the path's world, and a block `G` the SG vote selector can return at `n`, if `G` is
    an ancestor of the FG root of `n`'s store, then every committee member of slot
    `opening_slot rW + 1` in `notHeldAt Sched` at its vote instant votes there, along the path, a
    run block descending from `G`. -/
theorem fgRootTier_cone_at_secondSlot (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V)
    {tGAT tE : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (htd : Restated.TimeDiverges M x)
    {N : Nat}
    (hN : (x[N].time : Int)
      = M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 2))
    {blocked : Height} {first i : Nat} {a : NamedAttestation V} {ta : Int}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hreg : Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N)
      (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
      (notHeldAt Sched) Finset.univ Finset.univ
      (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0)
    (harW : a.round ≤ Restated.switchRound M S tE)
    {n₀ : Nat} (hn₀ : Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    (htop : Restated.topHonestRow M S Sched x n₀ ≤ (M.derive_named S.E S.cfg T).h)
    {v' : V} (hv' : v' ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    {n : M.N}
    (hnA : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) v')
        (Restated.switchRound M S tE))
    {A2 : Option (Block V)}
    (hA2 : M.grade2_block_with (M.gradeContract n.cache) (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc
        (M.toHealing n.st.core)
        (M.round_of (Setup.alwaysAwake S).hc (M.toHealing n.st.core).s) ⇢ A2)
    {G : Block V}
    (hG : M.get_sg_vote_with (M.gradeContract n.cache) (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc
        (M.toHealing n.st.core)
        (M.round_of (Setup.alwaysAwake S).hc (M.toHealing n.st.core).s) A2 ⇢ G)
    (hroot : Block.Preceq G (M.get_fg_root (M.toHealing n.st.core).toFG)) :
    Restated.NamedHonestVotesConeOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N)
      (notHeldAt Sched) Finset.univ ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1)
      (fun X => Block.Preceq G X) :=
  Restated.namedHonestVotesConeOn_of_preceq_l78 facts
    (preceq_trans_Preceq hroot
      (Restated.actionFgRoot_preceq_checkpoint_at_switchRound facts S Sched x v hsync hmono hawake hgst hcv
        hvalid hawm hthird hcom hlen htd hN hreg harW hn₀ htop v' hv' n hnA))
    (Restated.checkpointCone_at_secondSlot facts S Sched x v hsync hmono hawake hgst hcv hvalid hawm hthird hcom
      hlen htd hN hreg harW)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- In the regime `hreg` along `runAllPath M S Sched x v N`, with `rW = switchRound M S tE` and a
    source round before `rW`: for a validator `v'` in `notHeldAt Sched` at `S.a rW`, a node state
    `n` of its round-`rW` action read whose live confirmation satisfies `GenuineConfirmation` for
    the opening slot, and a block `G` the SG vote selector can return at `n` that is an ancestor of
    that live confirmation, `T` and `G` are on one chain. -/
theorem checkpoint_compatible_clearSG_at_switchRound (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V)
    {tGAT tE : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (htd : Restated.TimeDiverges M x)
    {N : Nat}
    (hN : (x[N].time : Int)
      = M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 2))
    {blocked : Height} {first i : Nat} {a : NamedAttestation V} {ta : Int}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hreg : Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N)
      (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
      (notHeldAt Sched) Finset.univ Finset.univ
      (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0)
    (harW : a.round ≤ Restated.switchRound M S tE)
    {n₀ : Nat} (hn₀ : Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    (htop : Restated.topHonestRow M S Sched x n₀ ≤ (M.derive_named S.E S.cfg T).h)
    (hbefore : a.round + 1 ≤ Restated.switchRound M S tE)
    {v' : V} (hv' : v' ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    {n : M.N}
    (hnA : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) v')
        (Restated.switchRound M S tE))
    (hlive : ∃ C : Block V,
      Restated.Vocabulary.Protocol.GenuineConfirmationWith M (M.gradeContract n.cache) S.E S.hc
        (Restated.Vocabulary.Proofs.Optimistic.tickStore M (Setup.alwaysAwake S)
          (Restated.runAllPath M S Sched x v N
            (Restated.strictEventIndex
              ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
              (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) v').st.core
          (M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)))))
        ((M.opening_slot S.hc (Restated.switchRound M S tE))) C ∧
      C = n.live_confirmed)
    {A2 : Option (Block V)}
    (hA2 : M.grade2_block_with (M.gradeContract n.cache) (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc
        (M.toHealing n.st.core)
        (M.round_of (Setup.alwaysAwake S).hc (M.toHealing n.st.core).s) ⇢ A2)
    {G : Block V}
    (hG : M.get_sg_vote_with (M.gradeContract n.cache) (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc
        (M.toHealing n.st.core)
        (M.round_of (Setup.alwaysAwake S).hc (M.toHealing n.st.core).s) A2 ⇢ G)
    (hclear : Block.Preceq G n.live_confirmed) :
    Block.compatible T.erase G = true := by
  obtain ⟨N', hN', hN'E, -, -, -, -, -⟩ := Restated.switchRound_instants facts S Sched x tGAT tE gap
    ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
    hgst hlen htd
  have hn : (x[N].time : Int) ≤ tE := by rw [hN.trans hN'.symm]; exact hN'E
  have hf := Restated.admissibleFieldsOn_runAll_notHeld facts S Sched x v N hsync hmono hawake hgst hcv hvalid
    hawm hthird hn
  have hHs : ∀ t t' : Int, t ≤ t' → notHeldAt Sched t' ⊆ notHeldAt Sched t :=
    fun _ _ h => notHeldAt_anti hmono h
  have hHsXb : ∀ t : Int, notHeldAt Sched t ⊆ (Finset.univ : Finset V) :=
    fun _ => Finset.subset_univ _
  have hcomOn := Restated.honestCommitteesOn_notHeld facts S Sched hcom
  obtain ⟨-, -, hloOpen, -⟩ := Restated.roundAt_bounds_l71 facts S hgst
  have hlo := hreg.lo_le_opening_l71 facts hf hloOpen
  have hapos : 0 < a.round := hreg.seed.round_pos_l70 facts hf
  obtain ⟨-, hloVote, -, -⟩ := Restated.loBounds_l70 facts S hapos hlo
  have hoPos : 0 < (M.opening_slot S.hc (Restated.switchRound M S tE)) :=
    facts.gr.opening_slot_pos_of_round_pos S.hc (lt_of_lt_of_le hapos harW)
  have hSc : (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)) =
      M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))) := by
    rw [Restated.Vocabulary.Execution.Setup.a, facts.sch.a_eq_confirmation_time]
  have hcut : M.support_cutoff S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))) ≤
      (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)) := by
    rw [hSc]
    exact facts.sch.Protocol_support_cutoff_le_confirmation_time S.E _
  have hpostVote : _ ≤ M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))) :=
    hloVote.trans (facts.sch.vote_time_mono_slots S.E (facts.gr.opening_slot_mono S harW))
  have hconfHor : M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))) ≤
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } :
        Record.Run V).horizon := by
    show _ ≤ (x[N].time : Int)
    rw [hN]
    exact facts.sch.confirmation_time_mono_l78 S (Nat.le_add_right _ 2)
  obtain ⟨C, hgen, hCeq⟩ := hlive
  obtain ⟨c, hc, st, -, rfl⟩ := hnA
  rw [facts.nd.mkNode_cache] at hgen
  have hc' : M.onPhaseTick S.E S.hc
      (Restated.runAllPath M S Sched x v N
        (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
          (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) v').st.core.toHealing
      (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))
      (Restated.runAllPath M S Sched x v N
        (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
          (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) v').cache ⇢ c := hc
  rw [hSc] at hc' hgen
  have hwinW : tGAT + 1 ≤ M.early S.E S.hc
      (M.round_of S.hc (M.opening_slot S.hc (Restated.switchRound M S tE))) .g1 - S.E.Δ := by
    rw [facts.gr.round_of_opening_slot_eq S.hc]
    have h0 := Restated.lo_le_early_g2_sub_delta_of_opening facts S hapos hlo harW
    have h1 := facts.gr.early_g2_add_delta_le_early_g1 S (Restated.switchRound M S tE)
    have hΔ := S.E.Δ_pos
    linarith
  obtain ⟨y, hy, -, hCy⟩ :=
    Restated.genuineConfirmation_exists_honestVoteSupporter_ceilingOn facts (Setup.alwaysAwake S)
      (notHeldAt Sched) Finset.univ hf hHs hHsXb hcomOn (hHs _ _ hcut hv') hoPos hpostVote
      hconfHor c hc' hgen
      (fun z _ hz j hj => hf.awake_g1 _ _ j _ (Or.inr rfl) hj
        (hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E _) hz) hwinW)
  have hyVote : y ∈ notHeldAt Sched
      (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)))) :=
    hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E _) hy
  have hTy := Restated.headsAtOpening_of_regime_l78 facts S Sched x v hsync hmono hawake hgst hcv hvalid hawm
    hthird hcom hlen htd hN hreg hbefore y hyVote
  obtain ⟨cc, hcc, Tr, hTr, L, hL, L', hL', H, hH⟩ := exists_voteHead₇₈ facts (Setup.alwaysAwake S)
    (Restated.runAllPath M S Sched x v N
      (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))))) y)
    ((M.opening_slot S.hc (Restated.switchRound M S tE)))
  have hTH : Block.Preceq T.erase H := hTy cc hcc Tr hTr L hL L' hL' H hH
  have hCH : Block.Preceq C H := hCy cc hcc Tr hTr L hL L' hL' H hH
  have hSGH : Block.Preceq G H := by
    refine preceq_trans_Preceq ?_ hCH
    rw [hCeq]
    exact hclear
  exact compatible_of_preceq_common_Preceq hTH hSGH

end

end DecoupledConsensusModel.Sts.Restated
