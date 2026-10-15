import Proofs.Vocabulary.Protocol.Schedule.Alignment
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Node
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Protocol_Schedule_Alignment
import Model.Record.Wiring

/-!
# The Goldfish votes a tick emits

A Goldfish vote a tick emits is the emitter's own vote of its slot, cast at that slot's vote time,
and a tick emits at most one; also membership in `round_votes` and the action time differing from
the proposal time, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Statements.Instantiation
open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Internal
open Execution
open Protocol

/-- For every outcome `out` of `v`'s tick at `t` from the node state `n`, if `out` sends the
    Goldfish vote `u`, then the slot of `t` is positive, `t` is that slot's vote time, for every
    outcome `c` of the phase tick at `t` every outcome `D` of the vote duty, run with the frame
    contract of `c` on `n`'s store with its clock set to `t`, has the vote `u`, `u` is signed by
    `v`, and `u`'s slot is the slot of `t`. -/
theorem Vocabulary.Proofs.Optimistic.gfVote_emitted_shape (facts : Record.Facts M) (S : Setup V) (v : V) (n : M.N) (t : Time)
    (out : M.N × List (NamedObject V)) (hout : out ∈ Restated.Vocabulary.Execution.on_tick_emit M S v n t)
    {u : GoldfishVote V} (h : Object.gfVote u ∈ out.2) (hn : M.reachedNode n := by trivial)
    (hv : M.runs_as n v := by trivial) :
    0 < S.E.slotOf t ∧ t = M.vote_time S.E (S.E.slotOf t) ∧
      (∀ c : M.Cache, M.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache ⇢ c →
        ∀ D : M.NS × Option (GoldfishVote V),
          M.duties_goldfish_vote_with (M.frameContract c) S.E S.hc (S.node v)
            (M.ns_setClock S.E n.st t) ⇢ D → D.2 = some u) ∧
      u.val_index = v ∧ u.slot = S.E.slotOf t :=
  facts.nd.gfVote_emitted_shape S v n t out hout u h

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Statements.Instantiation
open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Internal
open Execution
open Protocol

/-- An outcome `out` of `v`'s tick at `t` from `n` sends at most one Goldfish vote: if it sends `u₁`
    and `u₂`, then `u₁ = u₂`. -/
theorem Vocabulary.Proofs.Optimistic.gfVote_emitted_unique (facts : Record.Facts M) (S : Setup V) (v : V) (n : M.N) (t : Time)
    (out : M.N × List (NamedObject V)) (hout : out ∈ Restated.Vocabulary.Execution.on_tick_emit M S v n t)
    {u₁ u₂ : GoldfishVote V}
    (h₁ : Object.gfVote u₁ ∈ out.2)
    (h₂ : Object.gfVote u₂ ∈ out.2) (hn : M.reachedNode n := by trivial)
    (hv : M.runs_as n v := by trivial) : u₁ = u₂ := by
  obtain ⟨-, -, hd₁, -, -⟩ := Restated.Vocabulary.Proofs.Optimistic.gfVote_emitted_shape facts S v n t out hout h₁
  obtain ⟨-, -, hd₂, -, -⟩ := Restated.Vocabulary.Proofs.Optimistic.gfVote_emitted_shape facts S v n t out hout h₂
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc n.st.core.toHealing t n.cache
  obtain ⟨D, hD⟩ := facts.dt.goldfish_vote_with_nonempty (M.frameContract c) S.E S.hc (S.node v)
    (M.ns_setClock S.E n.st t)
  have e₁ := hd₁ c hc D hD
  rw [hd₂ c hc D hD] at e₁
  exact (Option.some_inj.mp e₁).symm

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Statements.Instantiation
open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Internal
open Execution
open Protocol

/-- For every sequence of worlds `W`, if `ρ` emits the Goldfish vote `u` from `v` at `t` read along
    `W`, then the slot of `t` is positive, `t` is that slot's vote time, `u` is signed by `v`, and
    `u`'s slot is the slot of `t`. -/
theorem Vocabulary.Proofs.Optimistic.emits_gfVote_shape (facts : Record.Facts M) (S : Setup V) {ρ : Record.Run V} {v : V} {u : GoldfishVote V}
    {t : Time} (W : Nat → V → M.N)
    (h : (Restated.Vocabulary.Execution.Run.emits M S ρ W v (Object.gfVote u) t))
    (hn : ∀ i, M.reachedNode (W i v)) (hv : ∀ i, M.runs_as (W i v) v) :
    0 < S.E.slotOf t ∧ t = M.vote_time S.E (S.E.slotOf t) ∧
      u.val_index = v ∧ u.slot = S.E.slotOf t := by
  obtain ⟨i, -, out, hout, -, ho⟩ := h
  obtain ⟨hpos, ht, -, hval, hslot⟩ :=
    Restated.Vocabulary.Proofs.Optimistic.gfVote_emitted_shape facts S v (W i v) t out hout ho (hn i) (hv i)
  exact ⟨hpos, ht, hval, hslot⟩

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Statements.Instantiation
open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Internal
open Execution
open Protocol

/-- `x` is in `M.round_votes st a` exactly when some attestation of `st`'s SG pool of `a`'s round
    has `a`'s validator and confirms `x`. -/
theorem Vocabulary.Proofs.Optimistic.mem_round_votes (facts : Record.Facts M) {st : M.S} {a : CombinedAttestation V}
    {x : Option BlockId} :
    x ∈ M.round_votes st a ↔
      ∃ b ∈ (M.store_sg_pool st a.round), b.val_index = a.val_index ∧ b.confirmed = x :=
  facts.hd.mem_round_votes_iff st a x

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Statements.Instantiation
open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Internal
open Execution
open Protocol

/-- If `t` is round `r`'s action time `M.a S.hc S.E.Δ r`, then `t` is not the proposal time of the
    slot `t` lies in. -/
theorem Vocabulary.Proofs.Optimistic.a_ne_proposal_time (facts : Record.Facts M) (S : Setup V) {t : Time} {r : Round}
    (ht : t = M.a S.hc S.E.Δ r) : t ≠ M.proposal_time S.E (S.E.slotOf t) := by
  have hsc : t = M.support_cutoff S.E ((M.opening_slot S.hc r) + 1) := by
    rw [ht]
    exact (facts.sch.a_eq_confirmation_time S.hc S.E r).trans
      (facts.sch.confirmation_time_eq_support_cutoff_succ S.E (M.opening_slot S.hc r))
  have hslot : S.E.slotOf t = (M.opening_slot S.hc r) + 1 := by
    rw [hsc]; exact facts.sch.slotOf_support_cutoff S.E _
  rw [hslot, hsc]
  exact facts.sch.support_cutoff_ne_proposal_time S.E _

end

end DecoupledConsensusModel.Sts.Restated
