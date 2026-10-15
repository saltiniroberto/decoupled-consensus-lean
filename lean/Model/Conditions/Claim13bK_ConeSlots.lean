import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bStepCone
import Model.Conditions.Claim13bStepConeIter
import Model.Conditions.Sts_Interface
import Model.Record.Wiring

/-!
# The slot conditions in the compatibility form

The conditions `ConeAnchorCompatible` and `ConeSlotHypothesesCompatibleAt` on an honest active
voter's vote duty at a slot, against a block `B`, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For every honest active member `v` of slot `(s + 1)`'s committee and every tick step `mr` at
    that slot's vote time, for every outcome `n` of `v`'s vote read, every SG root `A` that `v`'s
    slot-`(s + 1)` vote duty can start its walk from under `n`'s grade contract is an ancestor or a
    descendant of `B`. -/
def ConeAnchorCompatible (M : Record.Model V) (S : Setup V) {Sched : Schedule V}
    (x : AtomicExec (Record.protocolOf M S) Sched) (B : Block V) (s : Slot) : Prop :=
  ∀ (v : V) (mr : Nat), v ∈ Restated.HonSlot M S Sched (s + 1) →
    Restated.tickStepAt M x mr (M.vote_time S.E (s + 1)) →
    ∀ n, Restated.voteReadOf M S (x[mr][v].st) (s + 1) ⇢ n →
    ∀ A, Restated.voteAnchorOf M (M.gradeContract n.cache)
        S.E S.hc (Restated.voteStoreAt M S (x[mr][v].st) (s + 1)) ⇢ A →
    Block.compatible A B = true

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For every honest active member `v` of slot `(s + 1)`'s committee, every tick step `m` at slot
    `s`'s vote time and every tick step `mr` at slot `(s + 1)`'s vote time: `v` is awake from slot
    `s`'s start to its support cutoff; the slot-`s` heads resolve in `v`'s tree; that tree idealizes
    roots; every head an honest active member of slot `s`'s committee can select is the erasure of a
    named block in the sent log; every support vote of a block in `v`'s tree is among that block's
    Goldfish votes; every vote of `v`'s merged view under such a member's name is in `v`'s own
    slot-`s` pool; every merged view is a valid vote set; every SG root the duty can start its walk
    from lies on one chain with `B`; and every block strictly between that root and `B` is in every
    voter tree the duty can build. -/
def ConeSlotHypothesesCompatibleAt (M : Record.Model V) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (B : Block V) (s : Slot) : Prop :=
  ∀ (v : V) (m mr : Nat), v ∈ Restated.HonSlot M S Sched (s + 1) →
    Restated.tickStepAt M x m (M.vote_time S.E s) →
    Restated.tickStepAt M x mr (M.vote_time S.E (s + 1)) →
    v ∈ Sched.awakeThroughout (slotStart S.E.Δ s) (M.support_cutoff S.E s) ∧
    Restated.HeadsResolve M S Sched x v m mr s ∧
    Restated.TreeIdealizes M S Sched x v mr B ∧
    (∀ v' ∈ Restated.HonSlot M S Sched s, ∀ G, Restated.gfHeadFrom M S (x[m][v'].st) s ⇢ G →
      ∃ H : NamedBlock V, Restated.blockInLog M S Sched x H ∧ H.erase = G) ∧
    (∀ Bl ∈ (x[mr][v].st).st.core.T, ∀ u ∈ Bl.gf_support_votes, u ∈ Bl.gf_votes) ∧
    (∀ v' ∈ Restated.HonSlot M S Sched s,
      ∀ Y, Restated.voteViewOf M S.E (Restated.voteStoreAt M S (x[mr][v].st) (s + 1)) ⇢ Y →
      ∀ u ∈ Y, u.val_index = v' → u ∈ (M.store_pool (x[mr][v].st).st.core s)) ∧
    (∀ Y, Restated.voteViewOf M S.E (Restated.voteStoreAt M S (x[mr][v].st) (s + 1)) ⇢ Y →
      Protocol.VoteSetValid S.E ((Restated.voteStoreAt M S (x[mr][v].st) (s + 1)).s - 1) Y) ∧
    (∀ n, Restated.voteReadOf M S (x[mr][v].st) (s + 1) ⇢ n →
      ∀ A, Restated.voteAnchorOf M (M.gradeContract n.cache)
          S.E S.hc (Restated.voteStoreAt M S (x[mr][v].st) (s + 1)) ⇢ A →
      Block.compatible A B = true) ∧
    (∀ n, Restated.voteReadOf M S (x[mr][v].st) (s + 1) ⇢ n →
      ∀ A, Restated.voteAnchorOf M (M.gradeContract n.cache)
          S.E S.hc (Restated.voteStoreAt M S (x[mr][v].st) (s + 1)) ⇢ A →
      ∀ C : Block V, Block.Preceq A C → C ≠ A → Block.Preceq C B →
      ∀ T, Restated.voteTreeOf M S.E (Restated.voteStoreAt M S (x[mr][v].st) (s + 1)) ⇢ T →
      C ∈ T)

end

end DecoupledConsensusModel.Sts.Restated
