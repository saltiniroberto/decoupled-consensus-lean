import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13b
import Proofs.Claims.Restated.HonestNeverSlashed
import Proofs.Claims.Restated.RunAll
import Proofs.Claims.Restated.Vocabulary_Execution_BridgesCore
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Model.Conditions.RunAll
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ValidatorVoteSafety
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Protocol_ChainState_AlignedRoundLemmas
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_21

/-!
# Authenticity and processing in the run built from an execution

Attestation authenticity, the processing of every attestation-carrying block, and the absence of
self-slashing, for the run of the first `n` steps of an execution with a declared honest set. Stated
over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Under `Unforgeability`, along the path `x` follows, an attestation carried by a block the run
    processes and naming a validator of `H` was emitted by that validator earlier, provided every
    member of `H` is honest through step `n`. -/
theorem attestationAuthenticity_runAll_withHonest (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) (H : Finset V) (n : Nat)
    (hunf : Restated.Unforgeability M S x) (hH : ∀ v₀ ∈ H, Restated.HonestThrough M Sched x n v₀) :
    Restated.Vocabulary.Internal.AttestationAuthenticity M (Setup.alwaysAwake S)
      { Restated.runAll M S Sched x v n with honest := H } (Restated.runAllPath M S Sched x v n) := by
  constructor
  intro v₀ B t hproc a haB hah
  have hauth := Restated.attestationAuthenticity_runAll_upTo facts S Sched x a.val_index n
    (x[n].time : Int) hunf (hH a.val_index hah) le_rfl
  exact hauth.carriedAttest v₀ B t hproc a haB (Finset.mem_singleton_self _)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If `n` satisfies `NodeInvariant`, `B` is a body of `n`'s store and `A` is an ancestor of `B`,
    then `A` is a body of `n`'s store. -/
private theorem ancestor_body_mem_of_inv {S : Setup V} {n : M.N}
    (h : Restated.Vocabulary.Proofs.NamedRuntime.NodeInvariant M S n) {A B : NamedBlock V}
    (hB : B ∈ n.st.bodies) (hAB : NamedBlock.Preceq A B) : A ∈ n.st.bodies := by
  have hpc : Restated.Vocabulary.Proofs.NamedStore.NamedParentClosed M n.st := h.1.1.1.2.2.1
  revert hB hAB
  induction B with
  | genesis =>
    intro hB hAB
    simp only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] at hAB
    exact hAB ▸ hB
  | node parent s root votes support rows proposer ih =>
    intro hB hAB
    simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
      decide_eq_true_eq] at hAB
    rcases hAB with rfl | hparent
    · exact hB
    · have hp := hpc.2 _ hB
      rw [Proofs.ModelProperties.named_parent_node] at hp
      exact ih hp (by simp only [NamedBlock.Preceq]; exact hparent)

/-- Along a path `W` of the run, every non-genesis body of a store in `W i` came from a processing
    event of that store's validator. -/
theorem processes_of_mem_bodies_runAll_withHonest (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) (H : Finset V) (n : Nat)
    (W : Nat → V → M.N)
    (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M (Setup.alwaysAwake S)
      { Restated.runAll M S Sched x v n with honest := H } W)
    (i : Nat) (v₀ : V) {X : NamedBlock V}
    (hX : X ∈ (W i v₀).st.bodies)
    {row : NamedAttestation V} (hrow : row ∈ X.attestations) :
    ∃ t : Int, Restated.Vocabulary.Execution.NamedRun.processes M (Setup.alwaysAwake S)
      { Restated.runAll M S Sched x v n with honest := H } W v₀ (NamedObject.block X) t := by
  rcases Restated.Vocabulary.Proofs.Bridges.processes_block_of_mem_T facts (Setup.alwaysAwake S)
      { Restated.runAll M S Sched x v n with honest := H } v₀ W hW i X hX with rfl | ⟨j, e, -, -, hproc⟩
  · exact absurd hrow (by rw [named_genesis_attestations]; simp)
  · exact ⟨e.time, hproc⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If the execution delivers only blocks whose parent the receiver already holds
    (`DeliveryWellFormed`), then every attestation-carrying ancestor of a block delivered in, or
    held by a member of `H` along, the run of the first `n` steps is processed by some validator in
    that run, along the path `x` follows. -/
theorem processes_of_blockInRun_runAll_withHonest (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) (H : Finset V) (n : Nat)
    (hdel : Restated.DeliveryWellFormed M S x) {B X : NamedBlock V}
    (hB : Restated.Vocabulary.Execution.NamedRun.blockInRun M (Setup.alwaysAwake S) { Restated.runAll M S Sched x v n with honest := H }
      (Restated.runAllPath M S Sched x v n) B)
    (hXB : NamedBlock.Preceq X B) {row : NamedAttestation V} (hrow : row ∈ X.attestations) :
    ∃ (v₀ : V) (t : Int), Restated.Vocabulary.Execution.NamedRun.processes M (Setup.alwaysAwake S)
      { Restated.runAll M S Sched x v n with honest := H } (Restated.runAllPath M S Sched x v n)
      v₀ (NamedObject.block X) t := by
  have hW : Restated.Vocabulary.Execution.NamedRun.OnePath M (Setup.alwaysAwake S)
      { Restated.runAll M S Sched x v n with honest := H } (Restated.runAllPath M S Sched x v n) :=
    Restated.OnePath_runAllPath facts S Sched x v n
  obtain ⟨C, hC, hBC⟩ := hB
  have hXC : NamedBlock.Preceq X C :=
    Proofs.NamedOutageHistory.IdxDriverHelpers.named_preceq_trans hXB hBC
  rcases hC with hobj | ⟨v₁, -, i, hmem⟩
  · obtain ⟨i, v₁, t, hev⟩ := Restated.exists_deliver_of_mem_objects
      { Restated.runAll M S Sched x v n with honest := H } hobj
    rcases namedPreceq_eq_or_parent hXC with rfl | hparent
    · exact ⟨v₁, t, Or.inr ⟨i, hev⟩⟩
    · -- the parent of a delivered block is in the receiver's store at the delivery
      have hev' : (Restated.runEvents M S Sched x n)[i]?
          = some (Record.Event.deliver v₁ (NamedObject.block C) t) := hev
      obtain ⟨k, -, hmemk, hcase⟩ := Restated.runAllPath_at_event facts S Sched x v n i hev'
      obtain ⟨m, hlbl, hmsg, -⟩ := Restated.deliver_of_mem_actionEventsOf hmemk
      have hpar : C.parent ∈ (x[k][v₁].st).st.bodies := hdel.deps k v₁ m hlbl C hmsg
      have hb' : Restated.runAllPath M S Sched x v n i v₁ = x[k][v₁].st := by
        rcases hcase with ⟨t₁, he', -, -⟩ | ⟨t₁, he', -, -⟩ | ⟨o₁, t₁, -, hb, -⟩
        · cases he'
        · cases he'
        · exact hb
      rw [← hb'] at hpar
      have hXmem : X ∈ (Restated.runAllPath M S Sched x v n i v₁).st.bodies :=
        ancestor_body_mem_of_inv
          (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts (Setup.alwaysAwake S)
            _ i v₁ _ (hW i).1)
          hpar hparent
      obtain ⟨t', hproc⟩ :=
        Restated.processes_of_mem_bodies_runAll_withHonest facts S Sched x v H n _ hW i v₁ hXmem hrow
      exact ⟨v₁, t', hproc⟩
  · have hXmem : X ∈ (Restated.runAllPath M S Sched x v n i v₁).st.bodies :=
      ancestor_body_mem_of_inv
        (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts (Setup.alwaysAwake S)
          _ i v₁ _ (hW i).1)
        hmem hXC
    obtain ⟨t', hproc⟩ :=
      Restated.processes_of_mem_bodies_runAll_withHonest facts S Sched x v H n _ hW i v₁ hXmem hrow
    exact ⟨v₁, t', hproc⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Along a path `W` of the run of the first `n` steps, no validator's own emissions contain two
    attestations slashable against each other. -/
theorem noSelfSlashing_runAll_withHonest (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) (H : Finset V) (n : Nat)
    (W : Nat → V → M.N)
    (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M (Setup.alwaysAwake S)
      { Restated.runAll M S Sched x v n with honest := H } W) :
    Restated.Vocabulary.Proofs.AlignedRoundLemmas.NoSelfSlashing M (Setup.alwaysAwake S)
      { Restated.runAll M S Sched x v n with honest := H } W := by
  intro v₀ a b ha hb
  have hns := Restated.emissionVoteSafety_of_honest facts (Setup.alwaysAwake S)
    { Restated.runAll M S Sched x v n with honest := Finset.univ } W hW v₀ (Finset.mem_univ v₀) a b ha hb
  exact (facts.csAdded.not_Slashable_iff _ _).1 hns

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Under monotone corruption, every validator the adversary does not hold at `x[n].time` is honest
    through step `n`. -/
theorem honestThrough_of_mem_notHeld (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (n : Nat) (hmono : Sched.MonotoneCorruption) :
    ∀ v₀ ∈ Finset.univ \ Sched.adv (x[n].time : Int), Restated.HonestThrough M Sched x n v₀ := by
  intro v₀ hv₀ t' ht' hmem
  exact (Finset.mem_sdiff.1 hv₀).2 (hmono t' _ ht' hmem)

end

end DecoupledConsensusModel.Sts.Restated
