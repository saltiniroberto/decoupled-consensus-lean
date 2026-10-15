import Proofs.Vocabulary.Execution.W4FKChainAdvanceFold
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_W4FKChainHandlerAdvance
import Proofs.Vocabulary.Protocol.Schedule.NamedTick
import Model.Conditions.Vocabulary_Execution_W4FKChainAdvanceFold
import Model.Conditions.Vocabulary_Internal_Legacy_Assumptions_Weight
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Admissible
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Protocol_Evidence_ProvenanceBridge
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Record.Wiring

/-!
# The invariant `NamedFinalityAdvance` along ticks and receipts

Theorems over a model `M : Record.Model V` and its facts `facts : Record.Facts M`: the invariant
`NamedFinalityAdvance` of a store is kept by setting its clock, admitting a row, the block handler,
the proposal duty, the proposal stage `tickStage1`, a receipt and a tick, the steps that read the
run being read along a path `W` of it.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

/-- If `m >>= k` can return `b`, then `m` can return some `a` from which `k a` can return `b`. -/
private theorem returns_bind_elim {α β : Type} (m : DC.NDRE α) (k : α → DC.NDRE β) (b : β)
    (h : (m >>= k) ⇢ b) : ∃ a, m ⇢ a ∧ k a ⇢ b := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_bind, Set.bind_def] at h
  obtain ⟨e, he, hb⟩ := Set.mem_iUnion₂.mp h
  cases e with
  | ok a => exact ⟨a, he, hb⟩
  | error err => simp at hb

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution
open Protocol (derive_named)

/-- If `st'` has the bodies of `st` and the finalized block of `st` is an ancestor of, or the same
    block as, that of `st'`, then `NamedFinalityAdvance` at `st` gives it at `st'`. -/
theorem Vocabulary.Proofs.HealingSurface.advance_of_bodies_eq_of_F
    (S : Setup V) {st st' : M.NS}
    (hbodies : st'.bodies = st.bodies)
    (hF : Block.Preceq st.core.F st'.core.F)
    (hadv : Restated.Vocabulary.Proofs.HealingSurface.NamedFinalityAdvance M S st) :
    Restated.Vocabulary.Proofs.HealingSurface.NamedFinalityAdvance M S st' := by
  intro D hD
  rw [hbodies] at hD
  exact Proofs.ModelProperties.Preceq_trans (hadv D hD) hF

/-- Setting the clock of `st` to `t` keeps the invariant `NamedFinalityAdvance`. -/
theorem Vocabulary.Proofs.HealingSurface.advance_setClock (facts : Record.Facts M)
    (S : Setup V) (st : M.NS) (t : Time)
    (hadv : Restated.Vocabulary.Proofs.HealingSurface.NamedFinalityAdvance M S st) :
    Restated.Vocabulary.Proofs.HealingSurface.NamedFinalityAdvance M S (M.ns_setClock S.E st t) := by
  refine Restated.Vocabulary.Proofs.HealingSurface.advance_of_bodies_eq_of_F S
    (facts.hd.ModelProperties_setClock_bodies S.E st t) ?_ hadv
  rw [facts.hd.setClock_core_F]
  exact Proofs.ModelProperties.Preceq_self _

/-- Admitting the row `row` into `st` keeps the invariant `NamedFinalityAdvance`. -/
theorem Vocabulary.Proofs.HealingSurface.advance_admit_row (facts : Record.Facts M)
    (S : Setup V) (st : M.NS) (row : NamedAttestation V)
    (hadv : Restated.Vocabulary.Proofs.HealingSurface.NamedFinalityAdvance M S st) :
    Restated.Vocabulary.Proofs.HealingSurface.NamedFinalityAdvance M S (M.admit_row S.hc st row) := by
  refine Restated.Vocabulary.Proofs.HealingSurface.advance_of_bodies_eq_of_F S
    (facts.hd.NamedAdmission_admit_row_bodies S.hc st row) ?_ hadv
  rw [facts.hd.sameCore_F (facts.hd.NamedAdmission_admit_row_core S.hc st row), facts.hd.on_sg_vote_F]
  exact Proofs.ModelProperties.Preceq_self _

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution
open Protocol (derive_named)

/-- Along a path `W` of `rho` with the slashable bound and no root collision, if `st` is coherent,
    holds a body at its maximum height, has named provenance, holds only blocks of the run and
    satisfies `NamedFinalityAdvance`, and `B` is a block of the run when the block handler's result
    holds it, then the store the block handler returns on `B` satisfies `NamedFinalityAdvance`. -/
theorem Vocabulary.Proofs.HealingSurface.advance_on_block_with (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V}
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    (hsb : Restated.Vocabulary.Execution.SlashableBound M S rho W) (hcf : Restated.Vocabulary.Execution.RootCollisionFree M S rho W)
    (admission : Protocol.CarriedAdmission)
    {st : M.NS} {B : NamedBlock V}
    (hcoh : Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg st)
    (hmax : ∃ D ∈ st.bodies, (M.derive_named S.E S.cfg D).h = st.core.h_max)
    (hprov : Restated.Vocabulary.Proofs.Bridges.NamedProvenance M S st)
    (hBrun : B ∈ (M.on_block_with admission S.E S.hc S.cfg st B).bodies →
      Restated.Vocabulary.Execution.RunBlock M S rho W B)
    (hRun : ∀ D ∈ st.bodies, Restated.Vocabulary.Execution.RunBlock M S rho W D)
    (hadv : Restated.Vocabulary.Proofs.HealingSurface.NamedFinalityAdvance M S st) (hn : M.reachedStore st := by trivial) :
    Restated.Vocabulary.Proofs.HealingSurface.NamedFinalityAdvance M S
      (M.on_block_with admission S.E S.hc S.cfg st B) := by
  refine Restated.Vocabulary.Proofs.HealingSurface.advance_of_bodies_eq_of_F S
    (facts.hd.on_block_with_bodies_eq S admission st B) ?_
    (Restated.Vocabulary.Proofs.HealingSurface.processBlockCore_advance facts S hW hsb hcf hcoh hmax hprov ?_ hRun hadv)
  · rw [facts.hd.on_block_with_core_F]
    exact Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mp (Block.preceq_self _)
  intro hmem
  exact hBrun (by rw [facts.hd.on_block_with_bodies_eq]; exact hmem)

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution
open Protocol (derive_named)

/-- Along a path `W` of `rho` with the slashable bound and no root collision, if `st` is coherent,
    holds a body at its maximum height, has named provenance, holds only blocks of the run and
    satisfies `NamedFinalityAdvance`, then every outcome `D` of the proposal duty on `st` whose
    store holds only blocks of the run has a store satisfying `NamedFinalityAdvance`. -/
theorem Vocabulary.Proofs.HealingSurface.advance_propose_block_with (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V}
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    (hsb : Restated.Vocabulary.Execution.SlashableBound M S rho W) (hcf : Restated.Vocabulary.Execution.RootCollisionFree M S rho W)
    (gc : M.Contract) (nd : Protocol.Node V)
    {st : M.NS}
    (hcoh : Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg st)
    (hmax : ∃ D ∈ st.bodies, (M.derive_named S.E S.cfg D).h = st.core.h_max)
    (hprov : Restated.Vocabulary.Proofs.Bridges.NamedProvenance M S st)
    (hRun : ∀ D ∈ st.bodies, Restated.Vocabulary.Execution.RunBlock M S rho W D)
    (hadv : Restated.Vocabulary.Proofs.HealingSurface.NamedFinalityAdvance M S st) :
    ∀ D : M.NS × Option (NamedBlock V), M.duties_propose_block_with gc S.E S.hc S.cfg nd st ⇢ D →
      (∀ X ∈ D.1.bodies, Restated.Vocabulary.Execution.RunBlock M S rho W X) →
      ∀ (hn : M.reachedStore st := by trivial),
      Restated.Vocabulary.Proofs.HealingSurface.NamedFinalityAdvance M S D.1 := by
  intro D hD hBrun _hn
  obtain ⟨o, ho⟩ := facts.dt.proposal_with_nonempty gc .poolAndCarried S.E S.hc nd st
  cases o with
  | none =>
      have hEq : D.1 = st :=
        facts.dt.propose_block_with_fst_of_none gc S.E S.hc S.cfg nd st none ho rfl D hD
      rw [hEq]
      exact hadv
  | some B =>
      have hEq : D.1 = M.store_with_cache (M.on_block_with .alsoCarried S.E S.hc S.cfg st B)
          (M.contractCache gc) :=
        facts.dt.propose_block_with_fst_of_some gc S.E S.hc S.cfg nd st (some B) ho rfl D hD
      rw [hEq, facts.nd.store_with_cache_bodies] at hBrun
      rw [hEq]
      refine Restated.Vocabulary.Proofs.HealingSurface.advance_of_bodies_eq_of_F S
        (facts.nd.store_with_cache_bodies _ _)
        (by rw [facts.nd.store_with_cache_core_F]; exact Proofs.ModelProperties.Preceq_self _) ?_
      exact Restated.Vocabulary.Proofs.HealingSurface.advance_on_block_with facts S hW hsb hcf .alsoCarried hcoh hmax hprov
        (fun hmem => hBrun B hmem) hRun hadv

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution
open Protocol (derive_named)

/-- If `n` passes the grade-1 awake test of the round of `t`'s slot and runs as `v`, then for every
    outcome `out` of `v`'s tick at `t` from `n`, every outcome `c` of the phase tick at `t` on `n`'s
    store and cache, and every outcome `st₁` of the proposal stage `tickStage1` run with the frame
    contract of `c` on `n`'s store, `out`'s store holds the bodies of `st₁`. -/
theorem Vocabulary.Proofs.HealingSurface.tick_bodies_stage1 (facts : Record.Facts M)
    (S : Setup V) (v : V) (n : M.N) (t : Time)
    (hrun : M.awake_for_grade1 S v n (M.round_of S.hc (S.E.slotOf t))) (hv : M.runs_as n v) :
    ∀ out : M.N × List (NamedObject V), M.tick S v n t ⇢ out →
    ∀ c : M.Cache, M.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache ⇢ c →
    ∀ st₁ : M.NS,
      Restated.Vocabulary.Proofs.HealingSurface.tickStage1 M S (M.frameContract c) (S.node v) n.st t ⇢ st₁ →
    ∀ (hn : M.reachedNode n := by trivial),
    out.1.st.bodies = st₁.bodies := by
  intro out hout c hc st₁ hst₁ _hn
  have hf := facts.nd.tick_bodies_and_coreT_from_proposal S v n t out hout
  simp only at hf
  unfold Restated.Vocabulary.Proofs.HealingSurface.tickStage1 at hst₁
  split_ifs at hst₁ with hcond
  · obtain ⟨D, hD, hst⟩ := returns_bind_elim _ _ _ hst₁
    rw [(Record.returns_pure _ _).1 hst]
    exact (hf.1 ⟨hcond.1, hcond.2.1, hcond.2.2, hrun⟩ c hc D hD).1
  · rw [(Record.returns_pure _ _).1 hst₁]
    exact (hf.2 hv (fun h => hcond ⟨h.1, h.2.1, h.2.2.1⟩)).1

/-- If `n` passes the grade-1 awake test of the round of `t`'s slot, then for every outcome `out` of
    `v`'s tick at `t` from `n`: if every outcome of the proposal stage `tickStage1`, run with the
    frame contract of every outcome of the phase tick on `n`'s store, satisfies
    `NamedFinalityAdvance`, so does `out`'s store. -/
theorem Vocabulary.Proofs.HealingSurface.advance_tick_of_stage1 (facts : Record.Facts M) (S : Setup V)
    (v : V) (n : M.N) (t : Time)
    (hrun : M.awake_for_grade1 S v n (M.round_of S.hc (S.E.slotOf t))) :
    ∀ out : M.N × List (NamedObject V), M.tick S v n t ⇢ out →
    (∀ c : M.Cache, M.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache ⇢ c →
      ∀ st₁ : M.NS,
        Restated.Vocabulary.Proofs.HealingSurface.tickStage1 M S (M.frameContract c) (S.node v) n.st t ⇢ st₁ →
        Restated.Vocabulary.Proofs.HealingSurface.NamedFinalityAdvance M S st₁) →
    ∀ (hn : M.reachedNode n := by trivial) (hv : M.runs_as n v := by trivial),
    Restated.Vocabulary.Proofs.HealingSurface.NamedFinalityAdvance M S out.1.st :=
  fun out hout hc2 _hn _hv => facts.nd.advance_tick_of_stage1 S v n t out hout hrun hc2

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution
open Protocol (derive_named)

/-- Along a path `W` of `rho` with the slashable bound and no root collision, if `st` with its clock
    set to `t` is coherent, holds a body at its maximum height, has named provenance and holds only
    blocks of the run, and `st` satisfies `NamedFinalityAdvance`, then every outcome `st₁` of the
    proposal stage `tickStage1` on `st` at `t` whose bodies are blocks of the run satisfies
    `NamedFinalityAdvance`. -/
theorem Vocabulary.Proofs.HealingSurface.advance_stage1 (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V}
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    (hsb : Restated.Vocabulary.Execution.SlashableBound M S rho W) (hcf : Restated.Vocabulary.Execution.RootCollisionFree M S rho W)
    (gc : M.Contract) (nd : Protocol.Node V)
    {st : M.NS} {t : Time}
    (hcoh : Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg (M.ns_setClock S.E st t))
    (hmax : ∃ D ∈ (M.ns_setClock S.E st t).bodies,
      (M.derive_named S.E S.cfg D).h =
        (M.ns_setClock S.E st t).core.h_max)
    (hprov : Restated.Vocabulary.Proofs.Bridges.NamedProvenance M S (M.ns_setClock S.E st t))
    (hRun : ∀ D ∈ (M.ns_setClock S.E st t).bodies, Restated.Vocabulary.Execution.RunBlock M S rho W D)
    (hadv : Restated.Vocabulary.Proofs.HealingSurface.NamedFinalityAdvance M S st) :
    ∀ st₁ : M.NS, Restated.Vocabulary.Proofs.HealingSurface.tickStage1 M S gc nd st t ⇢ st₁ →
      (∀ D ∈ st₁.bodies, Restated.Vocabulary.Execution.RunBlock M S rho W D) →
      ∀ (hn : M.reachedStore st := by trivial),
      Restated.Vocabulary.Proofs.HealingSurface.NamedFinalityAdvance M S st₁ := by
  intro st₁ hst₁ hBrun _hn
  have _hrs : M.reachedStore (M.ns_setClock S.E st t) := facts.sto.reachedStore_setClock S.E st t _hn
  have hadv0 : Restated.Vocabulary.Proofs.HealingSurface.NamedFinalityAdvance M S (M.ns_setClock S.E st t) :=
    Restated.Vocabulary.Proofs.HealingSurface.advance_setClock facts S st t hadv
  unfold Restated.Vocabulary.Proofs.HealingSurface.tickStage1 at hst₁
  split_ifs at hst₁ with hprop
  · obtain ⟨D, hD, hst⟩ := returns_bind_elim _ _ _ hst₁
    rw [(Record.returns_pure _ _).1 hst] at hBrun ⊢
    exact Restated.Vocabulary.Proofs.HealingSurface.advance_propose_block_with facts S hW hsb hcf gc nd
      hcoh hmax hprov hRun hadv0 D hD hBrun
  · rw [(Record.returns_pure _ _).1 hst₁]
    exact hadv0

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution
open Protocol (derive_named)

/-- Along a path `W` of `rho` with the slashable bound and no root collision, if `st` is coherent,
    holds a body at its maximum height, has named provenance, holds only blocks of the run and
    satisfies `NamedFinalityAdvance`, and the store the receipt of `o` returns on `st` holds only
    blocks of the run, then that store satisfies `NamedFinalityAdvance`. -/
theorem Vocabulary.Proofs.HealingSurface.advance_receipt (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V}
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    (hsb : Restated.Vocabulary.Execution.SlashableBound M S rho W) (hcf : Restated.Vocabulary.Execution.RootCollisionFree M S rho W)
    (st : M.NS) (o : NamedObject V)
    (hcoh : Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg st)
    (hmax : ∃ D ∈ st.bodies, (M.derive_named S.E S.cfg D).h = st.core.h_max)
    (hprov : Restated.Vocabulary.Proofs.Bridges.NamedProvenance M S st)
    (hRun : ∀ D ∈ st.bodies, Restated.Vocabulary.Execution.RunBlock M S rho W D)
    (hBrun : ∀ D ∈ (M.receipt_process S st o).bodies, Restated.Vocabulary.Execution.RunBlock M S rho W D)
    (hadv : Restated.Vocabulary.Proofs.HealingSurface.NamedFinalityAdvance M S st) (hn : M.reachedStore st := by trivial) :
    Restated.Vocabulary.Proofs.HealingSurface.NamedFinalityAdvance M S (M.receipt_process S st o) := by
  cases o with
  | block B =>
      rw [facts.nd.process_block] at hBrun ⊢
      exact Restated.Vocabulary.Proofs.HealingSurface.advance_on_block_with facts S hW hsb hcf .alsoCarried hcoh hmax hprov
        (fun hmem => hBrun B hmem) hRun hadv
  | gfVote u =>
      rw [facts.nd.process_gfVote]
      refine Restated.Vocabulary.Proofs.HealingSurface.advance_of_bodies_eq_of_F S
        (facts.hd.ns_with_core_bodies S.E st u _ rfl) ?_ hadv
      rw [facts.hd.ns_with_core_core, facts.hd.on_goldfish_vote_checked_F]
      exact Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mp (Block.preceq_self _)
  | attest row =>
      rw [facts.nd.process_attest]
      exact Restated.Vocabulary.Proofs.HealingSurface.advance_admit_row facts S st row hadv

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution
open Protocol (derive_named)

/-- Along a path `W` of `rho` with the slashable bound and no root collision, if `n`'s store is
    coherent, holds a body at its maximum height, has named provenance, holds only blocks of the run
    and satisfies `NamedFinalityAdvance`, then for every node state `n₁` that `n`'s receipt of `o`
    can return, if every body of `n₁`'s store is a block of the run, `n₁`'s store satisfies
    `NamedFinalityAdvance`. -/
theorem Vocabulary.Proofs.HealingSurface.advance_node_process (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V}
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    (hsb : Restated.Vocabulary.Execution.SlashableBound M S rho W) (hcf : Restated.Vocabulary.Execution.RootCollisionFree M S rho W)
    (n : M.N) (o : NamedObject V)
    (hcoh : Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg n.st)
    (hmax : ∃ D ∈ n.st.bodies, (M.derive_named S.E S.cfg D).h = n.st.core.h_max)
    (hprov : Restated.Vocabulary.Proofs.Bridges.NamedProvenance M S n.st)
    (hRun : ∀ D ∈ n.st.bodies, Restated.Vocabulary.Execution.RunBlock M S rho W D)
    (hadv : Restated.Vocabulary.Proofs.HealingSurface.NamedFinalityAdvance M S n.st) :
    ∀ n₁, M.process S n o ⇢ n₁ →
      (∀ D ∈ n₁.st.bodies, Restated.Vocabulary.Execution.RunBlock M S rho W D) →
      ∀ (hn : M.reachedNode n := by trivial),
      Restated.Vocabulary.Proofs.HealingSurface.NamedFinalityAdvance M S n₁.st := by
  intro n₁ hn₁ hBrun _hn
  have _hrs : M.reachedStore n.st := facts.nd.reachedStore_of_node n _hn
  rw [facts.nd.process_st S n o n₁ hn₁] at hBrun ⊢
  rw [facts.nd.make_grades_compatible_with_finalized_bodies] at hBrun
  refine Restated.Vocabulary.Proofs.HealingSurface.advance_of_bodies_eq_of_F S
    (facts.nd.make_grades_compatible_with_finalized_bodies _) ?_
    (Restated.Vocabulary.Proofs.HealingSurface.advance_receipt facts S hW hsb hcf n.st o hcoh hmax hprov
      hRun hBrun hadv)
  rw [facts.nd.make_grades_compatible_with_finalized_core_F]
  exact Proofs.ModelProperties.Preceq_self _

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution
open Protocol (derive_named)

/-- Along a path `W` of `rho` with the slashable bound and no root collision, if `n`'s store with
    its clock set to `t` is coherent, holds a body at its maximum height, has named provenance and
    holds only blocks of the run, and `n`'s store satisfies `NamedFinalityAdvance`, then for every
    outcome `out₁` of `v`'s tick at `t` from `n` whose store holds only blocks of the run, if `n`
    runs as `v`, `out₁.1`'s store satisfies `NamedFinalityAdvance`. -/
theorem Vocabulary.Proofs.HealingSurface.advance_node_tick (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V}
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    (hsb : Restated.Vocabulary.Execution.SlashableBound M S rho W) (hcf : Restated.Vocabulary.Execution.RootCollisionFree M S rho W)
    (v : V) (n : M.N) (t : Time)
    (hcoh : Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg
      (M.ns_setClock S.E n.st t))
    (hmax : ∃ D ∈ (M.ns_setClock S.E n.st t).bodies,
      (M.derive_named S.E S.cfg D).h =
        (M.ns_setClock S.E n.st t).core.h_max)
    (hprov : Restated.Vocabulary.Proofs.Bridges.NamedProvenance M S (M.ns_setClock S.E n.st t))
    (hRun : ∀ D ∈ (M.ns_setClock S.E n.st t).bodies, Restated.Vocabulary.Execution.RunBlock M S rho W D)
    (hadv : Restated.Vocabulary.Proofs.HealingSurface.NamedFinalityAdvance M S n.st) :
    ∀ out₁, M.tick S v n t ⇢ out₁ →
      (∀ D ∈ out₁.1.st.bodies, Restated.Vocabulary.Execution.RunBlock M S rho W D) →
      M.runs_as n v →
      ∀ (hn : M.reachedNode n := by trivial),
      Restated.Vocabulary.Proofs.HealingSurface.NamedFinalityAdvance M S out₁.1.st := by
  intro out₁ hout hBrun hv _hn
  have _hrs : M.reachedStore n.st := facts.nd.reachedStore_of_node n _hn
  by_cases hrun : M.awake_for_grade1 S v n (M.round_of S.hc (S.E.slotOf t))
  · refine Restated.Vocabulary.Proofs.HealingSurface.advance_tick_of_stage1 facts S v n t hrun out₁ hout ?_
    intro c hc st₁ hst₁
    refine Restated.Vocabulary.Proofs.HealingSurface.advance_stage1 facts S hW hsb hcf (M.frameContract c)
      (S.node v) hcoh hmax hprov hRun hadv st₁ hst₁ ?_
    intro D hD
    refine hBrun D ?_
    rw [Restated.Vocabulary.Proofs.HealingSurface.tick_bodies_stage1 facts S v n t hrun hv out₁ hout c hc st₁ hst₁]
    exact hD
  · -- `n` fails the grade-1 awake test: the tick leaves the bodies and `F` as they were
    obtain ⟨hb, hF⟩ := facts.nd.tick_frame_of_not_awake_for_grade1 S v n t out₁ hout hrun
    refine Restated.Vocabulary.Proofs.HealingSurface.advance_of_bodies_eq_of_F S hb ?_ hadv
    rw [hF]
    exact Proofs.ModelProperties.Preceq_self _

end

end DecoupledConsensusModel.Sts.Restated
