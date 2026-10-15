import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.RunVocabulary
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedReceiptCalls
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_44

/-!
# Committee majorities and run facts

The per-slot committee majority `HonestCommitteesOn` and the bundle `AdmissibleFieldsOn` of the
facts a run satisfies along a path `W`, stated over a model `M : Record.Model V`.
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
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- For every slot `s`, strictly more than half of `s`'s committee is in the set for `s`'s
    confirmation instant. -/
def HonestCommitteesOn (M : Record.Model V) (S : Setup V) (Hs : Int → Finset V) : Prop :=
  ∀ s : Slot, (S.E.committee s).card <
    2 * ((S.E.committee s) ∩ Hs (M.confirmation_time S.E s)).card

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- The facts about the run `rho` along the path `W` from the instant `lo` on, for the family `Hs`:
    sorted, well-formed events in the horizon, timely broadcast, relay and
    handling of blocks, Goldfish votes and attestations, authentic signers, dependencies present at
    each delivery, and run blocks read through `Xb` free of root collisions and of slashable weight
    between their chains. -/
structure AdmissibleFieldsOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → M.N) (Hs : Int → Finset V) (Xb : Finset V) (lo : Int) : Prop where
  lo_pos : 0 < lo
  horizon_nonneg : 0 ≤ rho.horizon
  sorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f)
  in_horizon : ∀ e ∈ rho.events, 0 ≤ Record.Event.time e ∧ Record.Event.time e ≤ rho.horizon
  tickIndexUnique : TickIndexUnique rho
  wire : ∀ (i : Nat) (v : V) (o : NamedObject V) (t : Int),
    rho.events[i]? = some (.deliver v o t) →
      (∀ B : NamedBlock V, o = .block B →
        (∀ u ∈ B.gf_votes, u.slot + 1 = B.slot) ∧
          (∀ u ∈ B.gf_support_votes, u ∈ B.gf_votes) ∧
          (∀ u ∈ B.gf_votes, u.val_index ∈ S.E.committee u.slot)) ∧
      (∀ u : GoldfishVote V, o = .gfVote u → u.val_index ∈ S.E.committee u.slot)
  onePath : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W
  /-- Every tick event of the run has an outcome from the node state `W i v` before it. -/
  tick_outcome : ∀ (i : Nat) (v : V) (t : Int), rho.events[i]? = some (Record.Event.tick v t) →
    ∃ out : M.N × List (NamedObject V), M.tick S v (W i v) t ⇢ out
  /-- Every delivery event of the run has an outcome from the node state `W i v` before it. -/
  receipt_outcome : ∀ (i : Nat) (v : V) (o : NamedObject V) (t : Int),
    rho.events[i]? = some (Record.Event.deliver v o t) →
    ∃ n' : M.N, M.process S (W i v) o ⇢ n'
  /-- At an honest validator's tick at a slot's proposal or Goldfish vote instant, its node state
      before that tick passes the grade-1 awake test of the slot's round, when `lo` is at or before
      that round's grade-1 window start. -/
  awake_g1 : ∀ (s : Slot) (u : V) (j : Nat) (τ : Int),
    (τ = M.proposal_time S.E s ∨ τ = M.vote_time S.E s) →
    rho.events[j]? = some (Record.Event.tick u τ) → u ∈ Hs τ →
    lo ≤ M.early S.E S.hc (M.round_of S.hc s) .g1 - S.E.Δ →
    M.awake_for_grade1 S u (W j u) (M.round_of S.hc s)
  /-- At an honest validator's tick at a slot's confirmation instant, its node state before that
      tick passes the grade-2 awake test of the next slot's round under `Setup.alwaysAwake S`, when
      `lo` is at or before that round's grade-2 window start. -/
  awake_g2 : ∀ (s : Slot) (u : V) (j : Nat),
    rho.events[j]? = some (Record.Event.tick u (M.confirmation_time S.E s)) →
    u ∈ Hs (M.confirmation_time S.E s) →
    lo ≤ M.early S.E S.hc (M.round_of S.hc (s + 1)) .g2 - S.E.Δ →
    M.awake_for_grade2 (Setup.alwaysAwake S) u (W j u) (M.round_of S.hc (s + 1))
  deps : ∀ (i : Nat) (v : V) (o : NamedObject V) (t : Int),
    rho.events[i]? = some (.deliver v o t) →
      ∀ C : NamedBlock V, o = .block C → C.parent ∈ (W i v).st.bodies
  tick_total : ∀ t : Int, lo ≤ t → ∀ v ∈ Hs t, PublicTime S t → t ≤ rho.horizon →
    Record.Event.tick v t ∈ rho.events
  broadcast : ∀ (v : V) (o : NamedObject V) (t : Int), v ∈ Hs t →
    Restated.Vocabulary.Execution.NamedRun.emits M S rho W v o t → ∀ w ∈ Hs (t + S.E.Δ), lo ≤ t → t + S.E.Δ ≤ rho.horizon →
      (∀ B : NamedBlock V, o = .block B →
        Block.compatible (W (strictEventIndex rho (t + S.E.Δ)) w).st.core.F B.erase = true) →
      ∃ t', t ≤ t' ∧ t' < t + S.E.Δ ∧ ∃ j : Nat, Restated.Vocabulary.Execution.NamedRun.actualHandlesAt M S rho W j w o t'
  relay_block : ∀ (v : V) (i : Nat) (B : NamedBlock V) (t : Int), v ∈ Hs (max t lo) →
    Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho W i v (.block B) t → ∀ w ∈ Hs (max t lo + S.E.Δ),
      Restated.Vocabulary.Execution.Object.processed M (W (i + 1) w).st (.block B) = false →
      max t lo + S.E.Δ ≤ rho.horizon →
      Block.compatible
          (W (strictEventIndex rho (max t lo + S.E.Δ)) w).st.core.F B.erase = true →
      ∃ t', t ≤ t' ∧ t' < max t lo + S.E.Δ ∧
        ∃ j : Nat, Restated.Vocabulary.Execution.NamedRun.actualHandlesAt M S rho W j w (.block B) t'
  relay_block_admit : ∀ (v : V) (i : Nat) (B : NamedBlock V) (t : Int), v ∈ Hs (max t lo) →
    Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho W i v (.block B) t → ∀ w ∈ Hs (max t lo + S.E.Δ),
      Restated.Vocabulary.Execution.Object.processed M (W (i + 1) w).st (.block B) = false →
      max t lo + S.E.Δ ≤ rho.horizon →
      Block.compatible
          (W (strictEventIndex rho (max t lo + S.E.Δ)) w).st.core.F B.erase = true →
      ∃ t', t ≤ t' ∧ t' < max t lo + S.E.Δ ∧
        ∃ j : Nat, Restated.Vocabulary.Execution.NamedRun.actualHandlesAt M S rho W j w (.block B) t' ∧
          (rho.events[j]? = some (.deliver w (.block B) t') →
            B.erase.slot ≤ (W j w).st.core.s)
  relay_gf_vote : ∀ (v : V) (i : Nat) (u : GoldfishVote V) (t : Int), v ∈ Hs t →
    Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho W i v (.gfVote u) t →
    Restated.Vocabulary.Execution.NamedRun.processesAtIndexAlong M S rho W i v (.gfVote u) → lo ≤ t →
    ∀ w ∈ Hs (t + S.E.Δ),
      Restated.Vocabulary.Execution.Object.processed M (W (i + 1) w).st (.gfVote u) = false →
      t + S.E.Δ ≤ rho.horizon →
      ∃ t', t ≤ t' ∧ t' < t + S.E.Δ ∧
        ∃ j : Nat, Restated.Vocabulary.Execution.NamedRun.actualHandlesAt M S rho W j w (.gfVote u) t'
  relay_gf_vote_handled : ∀ (v : V) (i : Nat) (u : GoldfishVote V) (t : Int), v ∈ Hs t →
    Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho W i v (.gfVote u) t → lo ≤ t → ∀ w ∈ Hs (t + S.E.Δ),
      Restated.Vocabulary.Execution.Object.processed M (W (i + 1) w).st (.gfVote u) = false →
      t + S.E.Δ ≤ rho.horizon →
      ∃ t', t ≤ t' ∧ t' < t + S.E.Δ ∧
        ∃ j : Nat, Restated.Vocabulary.Execution.NamedRun.actualHandlesAt M S rho W j w (.gfVote u) t'
  two_cutoff : ∀ (r : Round) (c₂ : Int) (source : V) (i : Nat) (a : NamedAttestation V)
    (t : Int), source ∈ Hs t →
    Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho W i source (.attest a) t → lo ≤ t → t < c₂ →
    a.round ∈ M.latest_window S.hc.η_SG r → ∀ target ∈ Hs (t + S.E.Δ),
      Restated.Vocabulary.Execution.Object.processed M (W (i + 1) target).st (.attest a) = false →
      c₂ + S.E.Δ ≤ rho.horizon →
      ∃ td, M.opening S.E S.hc a.round ≤ td ∧ td < c₂ + S.E.Δ ∧
        ∃ j : Nat, Restated.Vocabulary.Execution.NamedRun.actualHandlesAt M S rho W j target (.attest a) td
  unforgeable : ∀ (v : V) (o : NamedObject V) (t : Int), Restated.Vocabulary.Execution.NamedRun.processes M S rho W v o t →
    ∀ u ∈ Hs t, o.author = some u → ∃ t', t' ≤ t ∧ Restated.Vocabulary.Execution.NamedRun.emits M S rho W u o t'
  carried_gf : ∀ (v : V) (B : NamedBlock V) (t : Int), Restated.Vocabulary.Execution.NamedRun.processes M S rho W v (.block B) t →
    ∀ u ∈ B.gf_votes, u.val_index ∈ Hs t →
      ∃ t', t' ≤ t ∧ Restated.Vocabulary.Execution.NamedRun.emits M S rho W u.val_index (.gfVote u) t'
  carried_attest : ∀ (v : V) (B : NamedBlock V) (t : Int),
    Restated.Vocabulary.Execution.NamedRun.processes M S rho W v (.block B) t →
    ∀ a ∈ B.attestations, a.val_index ∈ Hs t →
      ∃ t', t' ≤ t ∧ Restated.Vocabulary.Execution.NamedRun.emits M S rho W a.val_index (.attest a) t'
  rootCollisionFree : Restated.RootCollisionFreeOn M S rho W Xb
  slashableBound : Restated.SlashableBoundOn M S rho W Xb

end

end DecoupledConsensusModel.Sts.Restated
