import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bStepCone

/-!
# The Goldfish vote duty's reads

The views, tree, SG root, head and vote of the Goldfish vote duty, the vote read and the stores the
vote and confirmation duties read, and the honest active members `HonSlot` of a slot's committee,
stated over a model `M : Record.Model V`. The definitions that call a routine returning a set of
outcomes are themselves sets of outcomes (`DC.NDRE`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The outcomes of the raw merged vote view the Goldfish vote duty reads at the store `st`. -/
def voteViewOf (M : Record.Model V) (E : Env V) (st : M.S) : DC.NDRE (Finset (GoldfishVote V)) :=
  M.voter_view E (M.toHealing st).toFG.toSG.toGoldfishStore st.s

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The outcomes of the support vote view the Goldfish vote duty reads at the store `st`. -/
def voteSupportViewOf (M : Record.Model V) (E : Env V) (st : M.S) : DC.NDRE (Finset (GoldfishVote V)) :=
  M.voter_support_view E (M.toHealing st).toFG.toSG.toGoldfishStore st.s

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The outcomes of the candidate tree the Goldfish vote duty descends at the store `st`. -/
def voteTreeOf (M : Record.Model V) (E : Env V) (st : M.S) : DC.NDRE (Finset (Block V)) :=
  M.voter_filtered_block_tree E st st.s

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The outcomes of the SG root the Goldfish vote duty's walk starts from, read by the grade
    contract for the round of `st`'s own slot. -/
def voteAnchorOf (M : Record.Model V) (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig)
    (st : M.S) : DC.NDRE (Block V) :=
  M.get_sg_root_with contract E hc st.toHealing (M.round_of hc st.s)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The outcomes of the head the Goldfish vote duty selects at the store `st`, from its tree, its
    two vote views and its SG root. -/
def gfHeadWith (M : Record.Model V) (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig)
    (st : M.S) : DC.NDRE (Block V) := do
  let T ← Restated.voteTreeOf M E st
  let W ← Restated.voteViewOf M E st
  let U ← Restated.voteSupportViewOf M E st
  M.get_head_in_tree_with contract E hc st T W U (st.s - 1)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The node states made of `before`'s store with the clock of slot `s`'s vote time written into it,
    `before`'s signing record, and an outcome of the phase tick at that time on `before`'s cache. -/
def voteReadOf (M : Record.Model V) (S : Setup V) (before : M.N) (s : Slot) : DC.NDRE M.N :=
  (fun c => M.mkNode (M.ns_setClock S.E before.st (M.vote_time S.E s)) before.record c) <$>
    M.onPhaseTick S.E S.hc before.st.core.toHealing (M.vote_time S.E s) before.cache

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The heads a validator's slot-`s` vote duty can select from the node state `before`: for each
    outcome `n` of `voteReadOf`, the outcomes of `gfHeadWith` under `n`'s grade contract on `n`'s
    store. -/
def gfHeadFrom (M : Record.Model V) (S : Setup V) (before : M.N) (s : Slot) : DC.NDRE (Block V) := do
  let n ← Restated.voteReadOf M S before s
  Restated.gfHeadWith M (M.gradeContract n.cache) S.E S.hc n.st.core

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The Goldfish votes `⟨v, s, H.root⟩` for the outcomes `H` of `gfHeadFrom`. -/
def gfVoteFrom (M : Record.Model V) (S : Setup V) (before : M.N) (v : V) (s : Slot) :
    DC.NDRE (GoldfishVote V) :=
  (fun H => (⟨v, s, H.root⟩ : GoldfishVote V)) <$> Restated.gfHeadFrom M S before s

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The honest active members of slot `s`'s committee: the members awake throughout slot `s`'s vote
    window and not held by the adversary at slot `s`'s confirmation time. -/
def HonSlot (M : Record.Model V) (S : Setup V) (Sched : Schedule V) (s : Slot) : Finset V :=
  (activeAtW S Sched s ∩ S.E.committee s) \ Sched.adv (M.confirmation_time S.E s)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The store slot `s'`'s vote duty reads: `before`'s store with the clock and the slot of slot
    `s'`'s vote time written into it. -/
def voteStoreAt (M : Record.Model V) (S : Setup V) (before : M.N) (s' : Slot) : M.S :=
  (M.ns_setClock S.E before.st (M.vote_time S.E s')).core

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The store the confirmation duty reads at slot `s`: `before`'s store with the clock and the slot
    of slot `s`'s confirmation time written into it. -/
def confStoreAt (M : Record.Model V) (S : Setup V) (before : M.N) (s : Slot) : M.S :=
  (M.ns_setClock S.E before.st (M.confirmation_time S.E s)).core

end

end DecoupledConsensusModel.Sts.Restated
