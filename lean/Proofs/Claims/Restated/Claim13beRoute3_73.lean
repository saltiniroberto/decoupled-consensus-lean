import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bStepCone
import Proofs.Claims.Restated.Claim13beRoute3_21
import Proofs.Claims.Restated.Claim13beRoute3_44
import Proofs.Claims.Restated.Claim13beRoute3_71
import Proofs.Claims.Restated.Claim13beRoute3_72
import Proofs.Claims.Restated.Claim13beRoute3_8
import Proofs.Claims.Restated.ProcessIdempotent
import Proofs.Claims.Restated.RunAll
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13bStepCone
import Model.Conditions.Claim13bStepConeIter
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.Claim13beRoute3_72
import Model.Conditions.RunAll
import Model.Conditions.RunVocabulary
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedHeadReads
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring

/-!
# The clauses at a regime's checkpoint

For a run-scoped regime on the run `runAll`, read along `Restated.runAllPath`, stated over a model
`M : Record.Model V`: the seed signer's store is a node state of the execution, and the regime's
checkpoint satisfies the clauses `inPlay`, `anchorEntry`, `heads` and `heightCeiling` at the switch
round.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

/-! ## Helpers -/

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol
open scoped DC

/-- `f <$> m` can return `b` exactly when `m` can return some `a` with `f a = b`. -/
private theorem returns_map_iff₇₃ {α β : Type} (f : α → β) (m : DC.NDRE α) (b : β) :
    (f <$> m) ⇢ b ↔ ∃ a, m ⇢ a ∧ f a = b := by
  unfold Record.Returns
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image]
  constructor
  · rintro ⟨e, he, hb⟩
    cases e with
    | ok a => exact ⟨a, he, by simpa [Except.map] using hb⟩
    | error err => simp [Except.map] at hb
  · rintro ⟨a, ha, rfl⟩
    exact ⟨_, ha, rfl⟩

/-- `m >>= k` can return `b` exactly when `m` can return some `a` from which `k a` can return `b`. -/
private theorem returns_bind_iff₇₃ {α β : Type} (m : DC.NDRE α) (k : α → DC.NDRE β) (b : β) :
    (m >>= k) ⇢ b ↔ ∃ a, m ⇢ a ∧ k a ⇢ b := by
  unfold Record.Returns
  simp only [ExceptT.run_bind, Set.bind_def]
  constructor
  · intro h
    obtain ⟨e, he, hb⟩ := Set.mem_iUnion₂.mp h
    cases e with
    | ok a => exact ⟨a, he, hb⟩
    | error err => simp at hb
  · rintro ⟨a, ha, hb⟩
    exact Set.mem_iUnion₂.mpr ⟨_, ha, hb⟩

/-- Slot `s`'s vote duty can return the head `G` from `before` exactly when some outcome `cc` of the
    phase tick at the vote instant, with `n` the node state of `before`'s store with the vote
    instant written into it and `cc`, and some outcomes of the voter's filtered tree, the voter view
    and the voter support view on `n`'s core store give an in-tree head computation, with the grade
    contract of `n`'s cache, that can return `G`. -/
private theorem gfHeadFrom_returns_iff₇₃ (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (s : Slot) (G : Block V) :
    Restated.gfHeadFrom M S before s ⇢ G ↔
      ∃ cc : M.Cache,
        M.onPhaseTick S.E S.hc before.st.core.toHealing (M.vote_time S.E s) before.cache ⇢ cc ∧
        ∃ n : M.N, n = M.mkNode (M.ns_setClock S.E before.st (M.vote_time S.E s)) before.record cc ∧
        ∃ Tr : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ Tr ∧
        ∃ L : Finset (GoldfishVote V),
          M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L ∧
        ∃ L' : Finset (GoldfishVote V),
          M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' ∧
          M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
            (M.toHealing n.st.core) Tr L L' (n.st.core.s - 1) ⇢ G := by
  unfold Restated.gfHeadFrom Restated.voteReadOf Restated.gfHeadWith Restated.voteTreeOf
    Restated.voteViewOf Restated.voteSupportViewOf
  constructor
  · intro h
    obtain ⟨n, hn, h⟩ := (returns_bind_iff₇₃ _ _ _).1 h
    obtain ⟨cc, hcc, rfl⟩ := (returns_map_iff₇₃ _ _ _).1 hn
    obtain ⟨Tr, hTr, h⟩ := (returns_bind_iff₇₃ _ _ _).1 h
    obtain ⟨L, hL, h⟩ := (returns_bind_iff₇₃ _ _ _).1 h
    obtain ⟨L', hL', h⟩ := (returns_bind_iff₇₃ _ _ _).1 h
    exact ⟨cc, hcc, _, rfl, Tr, hTr, L, hL, L', hL',
      (facts.hd.get_head_in_tree_with_eq_layer _ _ _ _ _ _ _ _ _).1 h⟩
  · rintro ⟨cc, hcc, n, rfl, Tr, hTr, L, hL, L', hL', h⟩
    exact (returns_bind_iff₇₃ _ _ _).2 ⟨_, (returns_map_iff₇₃ _ _ _).2 ⟨cc, hcc, rfl⟩,
      (returns_bind_iff₇₃ _ _ _).2 ⟨Tr, hTr, (returns_bind_iff₇₃ _ _ _).2 ⟨L, hL,
        (returns_bind_iff₇₃ _ _ _).2 ⟨L', hL',
          (facts.hd.get_head_in_tree_with_eq_layer _ _ _ _ _ _ _ _ _).2 h⟩⟩⟩⟩

local macro "p45% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_45)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p50% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_50)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

/-- The round-`r` action read computed from `before` has some node state. -/
private theorem actionReadFrom_nonempty₇₃ (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∃ n, n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r :=
  (p50% actionReadFrom_nonempty₅₀b) facts S before r

/-- Every node state of the round-`r` action read computed from `before` has the bodies of `before`. -/
private theorem actionReadFrom_bodies₇₃ (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      n.st.bodies = before.st.bodies :=
  (p50% actionReadFrom_bodies₅₀) facts S before r

/-- Every node state of the round-`r` action read computed from `before` has the chain-state map of
    `before`. -/
private theorem actionReadFrom_σ₇₃ (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      n.st.core.σ = before.st.core.σ :=
  (p45% actionReadFrom_σ₄₅) facts S before r

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- For a regime on `runAll M S Sched x v N`, read along `Restated.runAllPath M S Sched x v N` over
    the validators not held, with seed attestation `a`, there is a step `k < N` such that the node
    state of `a`'s signer in the world of that path before the events strictly before the action
    instant of `a`'s round is the node state it holds after `k` steps of `x`, and that signer is
    honest through `k`. -/
theorem seedStore_runAll_tick (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V)
    (hmono : Sched.MonotoneCorruption) {N : Nat}
    {r0 : Round} {blocked : Height} {first i : Nat} {a : NamedAttestation V} {ta : Int}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hreg : Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N)
      (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
      (notHeldAt Sched) Finset.univ Finset.univ r0 blocked first i a ta Cfg T Tprev c0) :
    ∃ k : Nat, k < N ∧
      Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            ((Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) a.round))) a.val_index
        = x[k][a.val_index].st ∧
      Restated.HonestThrough M Sched x k a.val_index := by
  obtain ⟨k, hkN, hk, -⟩ := Restated.mem_sent_of_emits_runAll facts S Sched x v hreg.seed.emitted
  have hta : ta = (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) a.round) := hreg.seed.actionTime_eq
  obtain ⟨hk1, hk0⟩ := Restated.tickStepAt_time facts x hk
  have hk' : Restated.tickStepAt M x k ((Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) a.round)) := by rw [← hta]; exact hk
  have hstore := Restated.stateBeforeTime_runAll_tick facts S Sched x v hk' (Nat.succ_le_of_lt hkN) a.val_index
  have hsig : a.val_index ∈ notHeldAt Sched ta := hreg.seed.signerHonest
  have hk'' : a.val_index ∈ notHeldAt Sched (x[k].time : Int) :=
    notHeldAt_anti hmono (show (x[k].time : Int) ≤ ta by omega) hsig
  exact ⟨k, hkN, hstore, Restated.honestThrough_of_mem_notHeld facts S Sched x k hmono _ hk''⟩

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- For a regime on `runAll M S Sched x v N`, read along `Restated.runAllPath M S Sched x v N` over
    the validators not held, some validator honest through some step holds the regime's checkpoint
    `T` among its store's bodies after that step. -/
theorem baseAnchorInHonestStore_of_regime (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V)
    (hmono : Sched.MonotoneCorruption) {N : Nat}
    {r0 : Round} {blocked : Height} {first i : Nat} {a : NamedAttestation V} {ta : Int}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hreg : Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N)
      (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
      (notHeldAt Sched) Finset.univ Finset.univ r0 blocked first i a ta Cfg T Tprev c0) :
    ∃ (m : Nat) (v : V), Restated.HonestThrough M Sched x m v ∧ T ∈ (x[m][v].st).st.bodies := by
  obtain ⟨k, -, hstore, hhon⟩ := Restated.seedStore_runAll_tick facts S Sched x v hmono hreg
  obtain ⟨n, hn⟩ := actionReadFrom_nonempty₇₃ facts (Setup.alwaysAwake S)
    (Restated.runAllPath M S Sched x v N
      (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        ((Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) a.round))) a.val_index) a.round
  have hCfg0 : Cfg ∈ (Restated.runAllPath M S Sched x v N
      (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        ((Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) a.round))) a.val_index).st.bodies := by
    rw [← actionReadFrom_bodies₇₃ facts (Setup.alwaysAwake S) _ a.round n hn]
    exact hreg.seed.sourceMem n hn
  rw [hstore] at hCfg0
  have hco := (Restated.nodeInvariant_sts facts S Sched x k a.val_index).1.1.1
  exact ⟨k, a.val_index, hhon, Restated.mem_bodies_of_preceq hco.2.2.1 hCfg0 hreg.checkpointPreceq⟩

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- For a regime on `runAll M S Sched x v N`, read along `Restated.runAllPath M S Sched x v N` over
    the validators not held, some validator honest through some step holds, after that step, a block
    in its store's tree whose recorded chain state names the erasure of the regime's checkpoint `T`
    as that height's entry. -/
theorem baseAnchorIsStoreEntry_of_regime (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V)
    (hmono : Sched.MonotoneCorruption) {N : Nat}
    {r0 : Round} {blocked : Height} {first i : Nat} {a : NamedAttestation V} {ta : Int}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hreg : Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N)
      (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
      (notHeldAt Sched) Finset.univ Finset.univ r0 blocked first i a ta Cfg T Tprev c0) :
    ∃ (m : Nat) (v : V), Restated.HonestThrough M Sched x m v ∧
      ∃ Cfg' : Block V, Cfg' ∈ (x[m][v].st).st.core.T ∧
        ((x[m][v].st).st.core.σ Cfg').T_h = T.erase := by
  obtain ⟨k, -, hstore, hhon⟩ := Restated.seedStore_runAll_tick facts S Sched x v hmono hreg
  obtain ⟨n, hn⟩ := actionReadFrom_nonempty₇₃ facts (Setup.alwaysAwake S)
    (Restated.runAllPath M S Sched x v N
      (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        ((Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) a.round))) a.val_index) a.round
  have hCfg0 : Cfg ∈ (Restated.runAllPath M S Sched x v N
      (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        ((Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) a.round))) a.val_index).st.bodies := by
    rw [← actionReadFrom_bodies₇₃ facts (Setup.alwaysAwake S) _ a.round n hn]
    exact hreg.seed.sourceMem n hn
  have hTh0 : T.erase = ((Restated.runAllPath M S Sched x v N
      (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        ((Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) a.round))) a.val_index).st.core.σ Cfg.erase).T_h := by
    rw [← actionReadFrom_σ₇₃ facts (Setup.alwaysAwake S) _ a.round n hn]
    exact hreg.seed.checkpointStored n hn
  rw [hstore] at hCfg0 hTh0
  have hco := (Restated.nodeInvariant_sts facts S Sched x k a.val_index).1.1.1
  have hCfgT : Cfg.erase ∈ (x[k][a.val_index].st).st.core.T := by
    rw [hco.1]
    exact Finset.mem_image_of_mem _ hCfg0
  exact ⟨k, a.val_index, hhon, Cfg.erase, hCfgT, hTh0.symm⟩

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- For a regime on `runAll M S Sched x v N`, read along `Restated.runAllPath M S Sched x v N` over
    the validators not held, the regime's checkpoint `T` is one of the blocks the execution put in
    play. -/
theorem inPlay_at_switchRound_of_regime (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V)
    (hmono : Sched.MonotoneCorruption) {N : Nat}
    {r0 : Round} {blocked : Height} {first i : Nat} {a : NamedAttestation V} {ta : Int}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hreg : Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N)
      (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
      (notHeldAt Sched) Finset.univ Finset.univ r0 blocked first i a ta Cfg T Tprev c0) :
    Restated.blockInLog M S Sched x T :=
  Restated.inPlay_at_switchRound facts S Sched x
    (Restated.baseAnchorInHonestStore_of_regime facts S Sched x v hmono hreg)

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- For a regime on `runAll M S Sched x v N`, read along `Restated.runAllPath M S Sched x v N` over
    the validators not held, on a valid execution, the replay of the regime's checkpoint `T` names
    `T` itself as its chain-state height's entry. -/
theorem anchorEntry_at_switchRound_of_regime (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V)
    (hmono : Sched.MonotoneCorruption)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) {N : Nat}
    {r0 : Round} {blocked : Height} {first i : Nat} {a : NamedAttestation V} {ta : Int}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hreg : Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N)
      (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
      (notHeldAt Sched) Finset.univ Finset.univ r0 blocked first i a ta Cfg T Tprev c0) :
    (M.derive_named S.E S.cfg T).T_h = T.erase :=
  Restated.anchorEntry_at_switchRound facts S Sched x hvalid
    (Restated.inPlay_at_switchRound_of_regime facts S Sched x v hmono hreg)
    (Restated.baseAnchorIsStoreEntry_of_regime facts S Sched x v hmono hreg)

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- If step `m` is the tick at `vote_time s` and `x[N].time` is `confirmation_time s`, then
    `m + 1 ≤ N`. -/
theorem succ_le_of_tick_vote_time_l73 (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {m N : Nat} {s : Slot}
    (hm : Restated.tickStepAt M x m (M.vote_time S.E s))
    (hN : (x[N].time : Int) = M.confirmation_time S.E s) :
    m + 1 ≤ N := by
  obtain ⟨-, hm0⟩ := Restated.tickStepAt_time facts x hm
  have hvc := facts.sch.Sts_vote_time_le_confirmation_time S s
  by_contra hcon
  have hle : ((x[N].time : Nat) : Int) ≤ ((x[m].time : Nat) : Int) := by
    exact_mod_cast Restated.time_mono facts S Sched x (by omega)
  linarith

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- Under the theorem's hypotheses, with `N` a step whose time is the confirmation instant of the
    switch round's third slot, for a regime on `runAll M S Sched x v N`, read along
    `Restated.runAllPath M S Sched x v N` over the validators not held, from base round
    `roundAt S tGAT + η_SG + 2`, whose source round is at or before the switch round, every head
    that an honest active member of that slot's committee can vote there, at a tick step at the
    slot's vote instant, is a descendant of the regime's checkpoint `T`. -/
theorem headsBelow_of_regime (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V)
    {tGAT tE : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (htd : Restated.TimeDiverges M x)
    {N : Nat}
    (hN : (x[N].time : Int)
      = M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 2))
    {blocked : Height} {first i : Nat} {a : NamedAttestation V} {ta : Int}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hreg : Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N)
      (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
      (notHeldAt Sched) Finset.univ Finset.univ
      (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0)
    (harW : a.round ≤ Restated.switchRound M S tE) :
    Restated.HeadsBelow M S Sched x T.erase ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 2) := by
  obtain ⟨N', hN', hN'E, -, -, -, -, -⟩ := Restated.switchRound_instants facts S Sched x tGAT tE gap
    ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
    hgst hlen htd
  have hn : (x[N].time : Int) ≤ tE := by rw [hN.trans hN'.symm]; exact hN'E
  have hf := Restated.admissibleFieldsOn_runAll_notHeld facts S Sched x v N hsync hmono hawake hgst hcv hvalid
    hawm hthird hn
  have hHs : ∀ t t' : Int, t ≤ t' → notHeldAt Sched t' ⊆ notHeldAt Sched t :=
    fun _ _ h => notHeldAt_anti hmono h
  have hHsXb : ∀ t : Int, notHeldAt Sched t ⊆ (Finset.univ : Finset V) :=
    fun _ => Finset.subset_univ _
  have hX : ∀ t : Int, 0 ≤ t → notHeldAt Sched t ⊆ (Finset.univ : Finset V) :=
    fun _ _ => Finset.subset_univ _
  have hXXb : (Finset.univ : Finset V) ⊆ Finset.univ := Finset.Subset.refl _
  have hcomOn := Restated.honestCommitteesOn_notHeld facts S Sched hcom
  have hbelow := Restated.belowOneThirdOn_runAll_notHeld facts S Sched x v N hthird hn
  obtain ⟨-, -, hloOpen, -⟩ := Restated.roundAt_bounds_l71 facts S hgst
  have hlo := hreg.lo_le_opening_l71 facts hf hloOpen
  have hdlo : (M.opening_slot S.hc a.round) + 1 ≤ (M.opening_slot S.hc (Restated.switchRound M S tE)) + 2 :=
    Nat.add_le_add (facts.gr.opening_slot_mono S harW) (by decide)
  have hhor : M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 2) + S.E.Δ ≤
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } :
        Record.Run V).horizon := by
    show _ ≤ (x[N].time : Int)
    rw [hN]
    exact facts.sch.vote_time_add_delta_le_confirmation_time S _
  have hheads := hreg.heads_from_firstInterior facts hf hHs hHsXb hX hXXb hcomOn hbelow hdlo
    hhor hlo (fun k hk u _ j hj => Restated.awake_g2_action_runAllPath facts S Sched x v N hmono
      hawake hn k hk u j hj)
  intro w m hw hm G hG
  have hmN := Restated.succ_le_of_tick_vote_time_l73 facts S Sched x hm hN
  have hwN : w ∈ notHeldAt Sched
      (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 2)) :=
    notHeldAt_anti hmono (facts.sch.Sts_vote_time_le_confirmation_time S _)
      (mem_notHeldAt.mpr ((Restated.mem_HonSlot facts).mp hw).2.2)
  rw [← Restated.stateBeforeTime_runAll_tick facts S Sched x v hm hmN w] at hG
  obtain ⟨cc, hcc, n, rfl, Tr, hTr, L, hL, L', hL', hH⟩ :=
    (gfHeadFrom_returns_iff₇₃ facts S _ _ G).1 hG
  exact hheads w hwN cc hcc Tr hTr L hL L' hL' G hH

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- Under unforgeable signatures, if `topHonestRow S Sched x n₀` is at most `T`'s chain-state
    height, then no non-empty height vote signed up to step `n₀ + 1` by a validator honest through
    its send names a height greater than `T`'s. -/
theorem heightCeiling_of_topHonestRow (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hunf : Restated.Unforgeability M S x) {n₀ : Nat}
    {T : NamedBlock V}
    (htop : Restated.topHonestRow M S Sched x n₀ ≤ (M.derive_named S.E S.cfg T).h) :
    ∀ (v : V) (n' : Nat) (a : NamedAttestation V) (h' : Height)
      (entry : BlockId) (tmo : Bool),
      n' ≤ n₀ + 1 → Restated.HonestThrough M Sched x n' v → a.val_index = v →
      (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n'].sent →
      a.height_pair = NamedHeightPair.vote h' entry tmo →
      h' ≤ (M.derive_named S.E S.cfg T).h := by
  intro v n' a h' entry tmo hn' hv hidx hsent hpair
  exact (Restated.honestRow_le_topHonestRow facts S Sched x hunf
    ⟨v, n', a, entry, tmo, hn', hv, hidx, hsent, hpair⟩).trans htop

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

local macro "p72% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_72)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

end

end DecoupledConsensusModel.Sts.Restated
