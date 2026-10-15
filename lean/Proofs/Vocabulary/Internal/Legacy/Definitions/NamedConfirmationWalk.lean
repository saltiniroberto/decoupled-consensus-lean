module
public import Proofs.Vocabulary.Internal.Legacy.Definitions.ConfirmationScore
public import Proofs.Vocabulary.Internal.Legacy.Definitions.NamedDutyReads
public import Proofs.Vocabulary.Internal.ModelVocabulary.Protocol.NamedStoreReads

@[expose] public section

/-!
# Named confirmation walk

The confirmation walk on a prepared read, from the SG root of the read's contract, and
`GenuineConfirmationAt`, which holds when the confirmation duty records that walk and the walk
passes the eligibility test.
-/


namespace DecoupledConsensusModel.Internal
open Execution NamedRecoveryRead
variable {V : Type} [DecidableEq V] [Fintype V]

/-- The walk the confirmation duty tests on the prepared read `n` at slot `s`: from the contract's
    SG root over the filtered tree, with the confirmation score and eligibility on the read's core
    store. -/
def namedConfirmationWalk (S : Setup V) (n : NamedNodeState V) (s : Slot) : Block V :=
  let st := n.st.core
  let A := Protocol.get_sg_root_with (NamedProfile.gradeContract n.cache) S.E S.hc
    st.toHealing (S.hc.round_of st.s)
  let tree := Protocol.get_filtered_block_tree st.toHealing.toFG
  Protocol.ghost A tree (confirmationScore S.E st s) (confirmationEligible S.E st s)

/-- At slot `s`'s confirmation time, `v`'s `live_confirmed` is the named confirmation walk of its
    input read, and that walk passes the eligibility test. -/
def GenuineConfirmationAt (S : Setup V) (ρ : Run V) (v : V) (s : Slot) : Prop :=
  let n := confirmationInputRead S ρ v s
  (ρ.storeAt S v (Protocol.confirmation_time S.E s)).live_confirmed =
      namedConfirmationWalk S n s ∧
    confirmationEligible S.E n.st.core s (namedConfirmationWalk S n s) = true

end DecoupledConsensusModel.Internal

end
