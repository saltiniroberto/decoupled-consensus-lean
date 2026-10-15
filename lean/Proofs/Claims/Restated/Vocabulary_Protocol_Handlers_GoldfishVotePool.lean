import Proofs.Vocabulary.Protocol.Handlers.GoldfishVotePool
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_Admission
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_Pool
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_TickBridges
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_AdoptionTransport
import Proofs.Vocabulary.Protocol.Schedule.NamedTick
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Protocol_Handlers_Pool
import Model.Record.Wiring

/-!
# The Goldfish pool at proposal ticks and block receipt

A proposal tick keeps the Goldfish votes and stamps of its proposal stage, and a block's fresh
committee vote is pooled before a deadline unless its validator equivocates, stated over a model
`M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.Optimistic
open Internal Execution
open Protocol
open Proofs.HealingSurface (voterAnchorAt voterCandidateTreeAt)

/-- For every outcome `out` of `v`'s tick at `t` from the node state `n`, where `t` is the proposal
    time of its slot `s > 0`, `v`'s node is that slot's proposer and `n` passes the grade-1 awake
    test `M.awake_for_grade1` of that slot's round, the Goldfish votes and their receipt stamps of
    `out`'s store are those of the store of every outcome `D` of the proposal duty on `n`'s store
    with its clock set to `t`, run with the frame contract of every outcome `c` of the phase tick. -/
theorem Vocabulary.Proofs.Optimistic.tick_fields_from_proposal (facts : Record.Facts M)
    (S : Setup V) (v : V) (n : M.N) (t : Time)
    (out : M.N × List (NamedObject V)) (hout : M.tick S v n t ⇢ out)
    (hguard : 0 < S.E.slotOf t ∧
      t = M.proposal_time S.E (S.E.slotOf t) ∧
      S.E.proposer (S.E.slotOf t) = (S.node v).val_index)
    (hrun : M.awake_for_grade1 S v n (M.round_of S.hc (S.E.slotOf t))) :
    ∀ c : M.Cache, M.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache ⇢ c →
    ∀ D : M.NS × Option (NamedBlock V),
      M.duties_propose_block_with (M.frameContract c) S.E S.hc S.cfg (S.node v)
        (M.ns_setClock S.E n.st t) ⇢ D →
      ∀ (hn : M.reachedNode n := by trivial) (hv : M.runs_as n v := by trivial),
      out.1.st.core.gf_votes = D.1.core.gf_votes ∧
        out.1.st.core.timestamp_vote = D.1.core.timestamp_vote :=
  fun c hc1 D hc2 _hn _hv => facts.nd.tick_fields_from_proposal S v n t out hout hguard hrun c hc1 D hc2

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.Optimistic
open Internal Execution
open Protocol
open Proofs.HealingSurface (voterAnchorAt voterCandidateTreeAt)

/-- If `st` carries its pool stamps, the block `B` is new to `st` and kept by the block handler, `B`
    includes the fresh committee vote `u`, and `st`'s clock is before `Γ`, then in the store the
    handler returns `u` is pooled with a stamp before `Γ`, or its validator equivocates among the
    votes stamped before `Γ`. -/
theorem Vocabulary.Proofs.Optimistic.block_carried_before_deadline_or_equivocates (facts : Record.Facts M)
    (S : Setup V) (st : M.NS)
    (B : NamedBlock V) (u : GoldfishVote V) (Γ : Time)
    (hstamps : Restated.Vocabulary.Protocol.PoolStamps M st.core) (hpre : B ∉ st.bodies)
    (hpost : B ∈ (M.on_block_with .alsoCarried S.E S.hc S.cfg st B).bodies)
    (hu : u ∈ B.erase.gf_votes) (hcommittee : u.val_index ∈ S.E.committee u.slot)
    (hfresh : ¬ u.slot < st.core.s - 1) (hfuture : ¬ st.core.s < u.slot)
    (hclock : st.core.t < Γ) :
    (let final := M.on_block_with .alsoCarried S.E S.hc S.cfg st B
     u ∈ beforeCutoff final.core.timestamp_vote Γ ((M.store_pool final.core u.slot)) ∨
       M.equivocates
         (beforeCutoff final.core.timestamp_vote Γ ((M.store_pool final.core u.slot)))
         u.val_index = true) :=
  facts.hd.block_carried_before_deadline_or_equivocates S st B u Γ hstamps hpre hpost hu
    hcommittee hfresh hfuture hclock

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.Optimistic
open Internal Execution
open Protocol
open Proofs.HealingSurface (voterAnchorAt voterCandidateTreeAt)

/-- If `st` carries its pool stamps, the block `B` is new to `st` and kept by the block handler, `B`
    includes the fresh committee vote `u`, and `st`'s clock is before `Γ`, then in the store the
    handler returns `u` is in `beforeCutoff` of its slot's pool at `Γ`, or its validator equivocates
    among the votes of that set. -/
theorem Vocabulary.Proofs.Optimistic.block_carried_beforeCutoff_or_equivocates (facts : Record.Facts M)
    (S : Setup V) (st : M.NS)
    (B : NamedBlock V) (u : GoldfishVote V) (Γ : Time)
    (hstamps : Restated.Vocabulary.Protocol.PoolStamps M st.core) (hpre : B ∉ st.bodies)
    (hpost : B ∈
      (M.on_block_with .alsoCarried S.E S.hc S.cfg st B).bodies)
    (hu : u ∈ B.erase.gf_votes) (hcommittee : u.val_index ∈ S.E.committee u.slot)
    (hfresh : ¬ u.slot < st.core.s - 1) (hfuture : ¬ st.core.s < u.slot)
    (hclock : st.core.t < Γ) :
    (let final := M.on_block_with .alsoCarried S.E S.hc S.cfg st B
     u ∈ beforeCutoff final.core.timestamp_vote Γ ((M.store_pool final.core u.slot)) ∨
       M.equivocates
         (beforeCutoff final.core.timestamp_vote Γ ((M.store_pool final.core u.slot)))
         u.val_index = true) := by
  exact Restated.Vocabulary.Proofs.Optimistic.block_carried_before_deadline_or_equivocates facts S st B u Γ hstamps hpre hpost hu
    hcommittee hfresh hfuture hclock

end

end DecoupledConsensusModel.Sts.Restated
