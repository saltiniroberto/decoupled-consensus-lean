import Proofs.Claims.Spec2Claims.Claim13bModel_initial_inclG2
import Proofs.Claims.Spec2Claims.Claim13bModel_gradeContract_inclG1
import Proofs.Claims.Spec2Claims.Claim13bModel_voter_filtered_block_tree
import Proofs.Claims.Spec2Claims.Claim13bModel_get_head_in_tree_with
import Proofs.Claims.Spec2Claims.Claim13bModel_get_head_in_tree_with_layer
import Proofs.Claims.Spec2Claims.Claim13bModel_on_block_using_s2
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedAdmission_admit_carried
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedAdmission_on_block_with
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedNode_tick
import Proofs.Claims.Spec2Claims.Claim13bModel_update_confirmation_with
import Proofs.Claims.Spec2Claims.Claim13bModel_update_confirmation_with_phase
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedDuties_attest_with
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedDuties_goldfish_vote_with
import Proofs.Claims.Spec2Claims.Claim13bModel_Block_slot
import Proofs.Vocabulary.ModelProperties.NamedStore_initial
import Proofs.Vocabulary.ModelProperties.NamedStore_setClock
import Proofs.Vocabulary.ModelProperties.on_block_using
import Proofs.Vocabulary.ModelProperties.on_block_checked_using
import Proofs.Vocabulary.ModelProperties.NamedStore_process_block_core
import Proofs.Vocabulary.ModelProperties.propose_block_with
import Proofs.Vocabulary.ModelProperties.NamedNode_process
import Proofs.Vocabulary.ModelProperties.NamedReceipt_process
import Proofs.Claims.Spec2Claims.Claim13bModel_on_block_checked_using_s2

/-!
# Slots of the blocks a store holds

The invariant `TreeSlotBounded`, that every block of a store's tree is of a slot at most the store's
slot, and its truth at the initial store.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Every block of `st.T` is of a slot at most `st.s`. -/
def TreeSlotBounded (st : Protocol.Store V) : Prop :=
  ∀ B : Block V, B ∈ st.T → B.slot ≤ st.s

namespace TreeSlotStep

variable {st st' st'' : Protocol.Store V}

end TreeSlotStep

omit [Fintype V] in
/-- The core of the initial named store satisfies `TreeSlotBounded`. -/
theorem treeSlotBounded_init :
    TreeSlotBounded (Protocol.NamedStore.initial : Protocol.NamedStore V).core := by
  intro B hB
  have hmem : B ∈ ({Block.genesis} : Finset (Block V)) := by
    rw [← Proofs.ModelProperties.initial_core_T]; exact hB
  rw [Finset.mem_singleton] at hmem
  subst hmem
  rw [Proofs.ModelProperties.initial_core_s, genesis_slot_inclG2]

section

variable (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)

end

end DecoupledConsensusModel.Sts
