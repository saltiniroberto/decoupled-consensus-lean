import Proofs.Vocabulary.Protocol.Handlers.Pool
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Event
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_Protocol_Handlers_Pool
import Model.Record.Wiring

/-!
# Adding a Goldfish vote to the pool

What `on_goldfish_vote` writes when it accepts a vote, and when a vote ends up in the pool with a
stamp, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Protocol
open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Internal
open Execution

/-- If the vote `u` is neither expired, from a future slot nor already pooled in `st`, and its
    validator does not equivocate in the pool of `u`'s slot, then `M.on_goldfish_vote st u` appends
    `u` to that slot's pool, stamps `u` with `st.t`, and keeps the clock. -/
theorem Vocabulary.Protocol.on_goldfish_vote_insert (facts : Record.Facts M) (st : M.S) (u : GoldfishVote V)
    (h1 : ¬ (u.slot < st.s - 1 ∨ st.s < u.slot ∨ u ∈ st.gf_votes u.slot))
    (h2 : ¬ M.equivocates ((M.store_pool st u.slot)) u.val_index = true) :
    (M.on_goldfish_vote st u).gf_votes =
        (fun k => if k = u.slot then st.gf_votes k ++ [u] else st.gf_votes k) ∧
      (M.on_goldfish_vote st u).timestamp_vote =
        (fun x => if x = u then some (st.t : Stamp) else st.timestamp_vote x) ∧
      (M.on_goldfish_vote st u).t = st.t :=
  facts.sch.on_goldfish_vote_insert st u h1 h2

end

section
open DecoupledConsensusModel.Protocol
open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Internal
open Execution

/-- If `st` carries its pool stamps, `u`'s slot is neither expired nor in the future for `st`, and
    `u`'s validator does not equivocate in the pool of `u`'s slot, then after
    `M.on_goldfish_vote st u` the vote `u` is in its slot's pool with a stamp at most `st.t`. -/
theorem Vocabulary.Protocol.mem_and_stamp_of_process (facts : Record.Facts M) (st : M.S) (u : GoldfishVote V)
    (h : Restated.Vocabulary.Protocol.PoolStamps M st) (hfresh : ¬ u.slot < st.s - 1) (hslot : ¬ st.s < u.slot)
    (hequiv : M.equivocates ((M.store_pool st u.slot)) u.val_index = false) :
    u ∈ (M.on_goldfish_vote st u).gf_votes u.slot ∧
      ∃ c : Stamp, (M.on_goldfish_vote st u).timestamp_vote u = some c ∧
        c ≤ (st.t : Stamp) :=
  facts.hd.mem_and_stamp_of_process st u h.slot h.stamped h.pooled h.bounded hfresh hslot hequiv

end

end DecoupledConsensusModel.Sts.Restated
