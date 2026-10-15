import Model.Record.ChainState
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_57b

/-!
# Facts about runs of the chain-state family

Two structures of facts relating a validator's store along a run to the chain states of the named
blocks it holds. `ChainStateVocabularyRunFacts M` reads runs of type `Run V`, with chain states from a
chain-state model `M : ChainStateModel V`. `ChainStateRunFacts M`, for a model `M : Model V`, reads
the worlds that the model's own runs `Record.Run V` reach in its first seven fields, and runs of
type `Run V` in its last five.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts.Record

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Protocol (HeightConfig)
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Facts about runs of type `Run V` relating each validator's store to the chain states, read from
    `M`, of the named blocks it holds. -/
structure ChainStateVocabularyRunFacts (M : ChainStateModel V) : Prop where
  /-- After `i` events, some body of `v`'s store has the store's finalized block as its finalized
      block, with finalized height less than the store's `h_max`. -/
  storeFinalizationOnChain_stateBefore : ∀ (S : Setup V) (rho : NamedRun V) (i : Nat) (v : V),
    ∃ D : NamedBlock V, D ∈ (NamedRun.stateBefore S rho i v).st.bodies ∧
      (M.derive_named S.E S.cfg D).F = (NamedRun.stateBefore S rho i v).st.core.F ∧
      (M.derive_named S.E S.cfg D).h_F < (NamedRun.stateBefore S rho i v).st.core.h_max
  /-- Just before time `t`, some body of `v`'s store has the store's finalized block as its
      finalized block, with finalized height less than the store's `h_max`. -/
  storeFinalizationOnChain_stateBeforeTime : ∀ (S : Setup V) (rho : NamedRun V) (t : Time)
    (v : V),
    ∃ D : NamedBlock V, D ∈ (NamedRun.stateBeforeTime S rho t v).st.bodies ∧
      (M.derive_named S.E S.cfg D).F = (NamedRun.stateBeforeTime S rho t v).st.core.F ∧
      (M.derive_named S.E S.cfg D).h_F < (NamedRun.stateBeforeTime S rho t v).st.core.h_max
  /-- After `i` events, some body of `v`'s store has the store's justified block and justified
      height as its own. -/
  justification_carrier_stateBefore : ∀ (S : Setup V) (rho : NamedRun V) (i : Nat) (v : V),
    ∃ C : NamedBlock V, C ∈ (NamedRun.stateBefore S rho i v).st.bodies ∧
      (M.derive_named S.E S.cfg C).J = (NamedRun.stateBefore S rho i v).st.core.J ∧
      (M.derive_named S.E S.cfg C).h_j = (NamedRun.stateBefore S rho i v).st.core.h_j
  /-- Just before time `t`, some body of `v`'s store has the store's justified block and justified
      height as its own. -/
  storeJustificationOnChain_stateBeforeTime : ∀ (S : Setup V) (rho : NamedRun V) (t : Time)
    (v : V),
    ∃ D ∈ (NamedRun.stateBeforeTime S rho t v).st.bodies,
      (M.derive_named S.E S.cfg D).J = (NamedRun.stateBeforeTime S rho t v).st.core.J ∧
      (M.derive_named S.E S.cfg D).h_j = (NamedRun.stateBeforeTime S rho t v).st.core.h_j
  /-- Just before time `t`, no body of `v`'s store has a justified height greater than the store's. -/
  noHighJustifications_stateBeforeTime : ∀ (S : Setup V) (rho : Run V) (t : Time) (v : V),
    ∀ B ∈ (rho.stateBeforeTime S t v).st.bodies,
      (M.derive_named S.E S.cfg B).h_j ≤ (rho.stateBeforeTime S t v).st.core.h_j
  /-- After `i` events, no body of `v`'s store has a height greater than the store's `h_max`. -/
  heights_le_hMax_stateBefore : ∀ (S : Setup V) (rho : Run V) (i : Nat) (v : V),
    ∀ D ∈ (rho.stateBefore S i v).st.bodies,
      (M.derive_named S.E S.cfg D).h ≤ (rho.stateBefore S i v).st.core.h_max
  /-- After `i` events, the height that `v`'s store records for a body's erasure is the height of
      that body's chain state. -/
  derivedView_stateBefore_h : ∀ (S : Setup V) (rho : Run V) (i : Nat) (v : V),
    ∀ D ∈ (rho.stateBefore S i v).st.bodies,
      ((rho.stateBefore S i v).st.core.σ D.erase).h = (M.derive_named S.E S.cfg D).h
  /-- If `v`'s round-`r` action has the FG source `Cfg`, some body `C` of the store
      `actionReadAt S rho v r` erases to `Cfg`, the store's height, entry and `nj` bit at `Cfg` are
      those of `C`'s chain state, and the action's confirmation witness is `C`'s entry. -/
  action_witness : ∀ (S : Setup V) (rho : Run V) (v : V) (r : Round) (Cfg : Block V),
    actionFGSource S (actionReadAt S rho v r) = some Cfg →
      ∃ C : NamedBlock V,
        C ∈ (actionReadAt S rho v r).st.bodies ∧ C.erase = Cfg ∧
        ((actionReadAt S rho v r).st.core.σ Cfg).h = (M.derive_named S.E S.cfg C).h ∧
        ((actionReadAt S rho v r).st.core.σ Cfg).T_h = (M.derive_named S.E S.cfg C).T_h ∧
        ((actionReadAt S rho v r).st.core.σ Cfg).nj = (M.derive_named S.E S.cfg C).nj ∧
        fgConfirmationWitness S (actionReadAt S rho v r) =
          some (M.derive_named S.E S.cfg C).T_h
  /-- Under `AdmissibleFieldsOn S rho Hs Xb lo`, every body `D` of `v`'s round-`r` action store has,
      in that store, the entry of its chain state. -/
  derivedStateAgrees_actionStoreAtOn : ∀ (S : Setup V) {rho : Run V} (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int}, AdmissibleFieldsOn S rho Hs Xb lo →
    ∀ (v : V) (r : Round), ∀ D ∈ (actionStoreAt S rho v r).st.bodies,
      ((actionStoreAt S rho v r).st.core.σ D.erase).T_h = (M.derive_named S.E S.cfg D).T_h
  /-- Under `AdmissibleFieldsOn S rho Hs Xb lo`, if `v ∈ Xb` and `D` is a body of `v`'s round-`r`
      action store, some body `K` of that store erases to `D`'s entry, has `D`'s height, is an
      ancestor of `D`, and satisfies `RunBlockOn S rho Xb K`. -/
  action_named_checkpointOn : ∀ (S : Setup V) {rho : Run V} (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int}, AdmissibleFieldsOn S rho Hs Xb lo →
    ∀ {v : V}, v ∈ Xb → ∀ {r : Round} {D : NamedBlock V},
      D ∈ (actionStoreAt S rho v r).st.bodies →
    ∃ K : NamedBlock V,
      K ∈ (actionStoreAt S rho v r).st.bodies ∧
      K.erase = (M.derive_named S.E S.cfg D).T_h ∧
      (M.derive_named S.E S.cfg K).h = (M.derive_named S.E S.cfg D).h ∧
      NamedBlock.Preceq K D ∧
      RunBlockOn S rho Xb K
  /-- Under `AdmissibleFieldsOn S rho Hs Xb lo`, if `a`'s signer is in `Xb`, emits `a` at `ta`, and
      `a`'s height pair names the height `h`, then the signer's round-`a.round` action store has
      bodies `D` and `K` at height `h` with `K` erasing to `D`'s entry and `K.erase ⪯ D.erase`, its
      FG source is `D`'s erasure, its confirmation witness is `K`'s entry, and `a`'s height pair is
      the target vote for `K`'s root at `h` or the timeout at `h`. -/
  honestHeightRow_confirmationWitnessOn : ∀ (S : Setup V) {rho : Run V} (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int}, AdmissibleFieldsOn S rho Hs Xb lo →
    ∀ {a : NamedAttestation V} {ta : Time} {h : Height},
    a.val_index ∈ Xb →
    rho.emits S a.val_index (Object.attest a) ta →
    a.height_pair.erase.height? = some h →
    ∃ D K : NamedBlock V,
      fgConfirmationWitness S
          (actionStoreAt S rho a.val_index a.round) =
        some (M.derive_named S.E S.cfg K).T_h ∧
      D ∈ (actionStoreAt S rho a.val_index a.round).st.bodies ∧
      actionFGSource S (actionStoreAt S rho a.val_index a.round) = some D.erase ∧
      (M.derive_named S.E S.cfg D).h = h ∧
      K ∈ (actionStoreAt S rho a.val_index a.round).st.bodies ∧
      K.erase = (M.derive_named S.E S.cfg D).T_h ∧
      (M.derive_named S.E S.cfg K).h = h ∧
      Block.Preceq K.erase D.erase ∧
      (a.height_pair.erase = HeightPair.target h K.erase.root ∨
        a.height_pair.erase = HeightPair.timeout h)
  /-- Under `AdmissibleFieldsOn S rho Hs Xb lo`, with `Hs` non-increasing over time and contained in
      `Xb`, and the validators outside `Hs rho.horizon` weighing less than a third of the total: if
      `v ∈ Xb`, `RunBlockOn S rho Xb T` holds with `T` at height `k ≥ 2`, every height-`k` row
      emitted by a member of `Hs rho.horizon` has `T`'s erasure as its action's confirmation
      witness, and `v`'s `h_max` after `n` events is at most `k + 1`, then `v`'s finalized block
      there is an ancestor of `T.erase`. -/
  storeF_preceq_checkpoint_of_windowOn : ∀ (S : Setup V) {rho : Run V} (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int}, AdmissibleFieldsOn S rho Hs Xb lo →
    (∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) → (∀ t : Int, Hs t ⊆ Xb) →
    Execution.BelowOneThird S (Hs rho.horizon) →
    ∀ {v : V}, v ∈ Xb → ∀ {n : Nat} {k : Height} {T : NamedBlock V},
    RunBlockOn S rho Xb T →
    (M.derive_named S.E S.cfg T).h = k → 2 ≤ k →
    (∀ (b : NamedAttestation V) (tb : Time), b.val_index ∈ Hs rho.horizon →
      NamedRun.emits S rho b.val_index (Object.attest b) tb →
      b.height_pair.erase.height? = some k →
      fgConfirmationWitness S (actionStoreAt S rho b.val_index b.round) = some T.erase) →
    (rho.stateBefore S n v).st.core.h_max ≤ k + 1 →
    Block.Preceq (rho.stateBefore S n v).st.core.F T.erase

/-- Facts about the runs of the model `M` relating each validator's store to the chain states of the
    named blocks it holds. -/
structure ChainStateRunFacts (M : Model V) : Prop where
  /-- For every world `w` the run `rho` can reach before its `i`-th event, some body `D` that `v`
      holds in `w` has `v`'s store's finalized block as its own finalized block, with finalized
      height less than `v`'s store's `h_max`. -/
  storeFinalizationOnChain_stateBefore : ∀ (S : Setup V) (rho : Record.Run V) (i : Nat) (v : V),
    ∀ w ∈ stateBeforeOf M S rho i,
    ∃ D : NamedBlock V, D ∈ (w v).st.bodies ∧
      (M.derive_named S.E S.cfg D).F = (w v).st.core.F ∧
      (M.derive_named S.E S.cfg D).h_F < (w v).st.core.h_max
  /-- For every world `w` that the events of `rho` timed before `t` lead to from the world in which
      every validator `u` holds `M.initial S u`, some body `D` that `v` holds in `w` has `v`'s
      store's finalized block as its own finalized block, with finalized height less than `v`'s
      store's `h_max`. -/
  storeFinalizationOnChain_stateBeforeTime : ∀ (S : Setup V) (rho : Record.Run V) (t : Time)
    (v : V),
    ∀ w ∈ (rho.events.filter (fun e => decide (e.time < t))).foldlM (worldStepOf M S)
        (fun u => M.initial S u),
    ∃ D : NamedBlock V, D ∈ (w v).st.bodies ∧
      (M.derive_named S.E S.cfg D).F = (w v).st.core.F ∧
      (M.derive_named S.E S.cfg D).h_F < (w v).st.core.h_max
  /-- For every world `w` the run `rho` can reach before its `i`-th event, some body `C` that `v`
      holds in `w` has `v`'s store's justified block and justified height as its own. -/
  justification_carrier_stateBefore : ∀ (S : Setup V) (rho : Record.Run V) (i : Nat) (v : V),
    ∀ w ∈ stateBeforeOf M S rho i,
    ∃ C : NamedBlock V, C ∈ (w v).st.bodies ∧
      (M.derive_named S.E S.cfg C).J = (w v).st.core.J ∧
      (M.derive_named S.E S.cfg C).h_j = (w v).st.core.h_j
  /-- For every world `w` that the events of `rho` timed before `t` lead to from the world in which
      every validator `u` holds `M.initial S u`, some body `D` that `v` holds in `w` has `v`'s
      store's justified block and justified height as its own. -/
  storeJustificationOnChain_stateBeforeTime : ∀ (S : Setup V) (rho : Record.Run V) (t : Time)
    (v : V),
    ∀ w ∈ (rho.events.filter (fun e => decide (e.time < t))).foldlM (worldStepOf M S)
        (fun u => M.initial S u),
    ∃ D ∈ (w v).st.bodies,
      (M.derive_named S.E S.cfg D).J = (w v).st.core.J ∧
      (M.derive_named S.E S.cfg D).h_j = (w v).st.core.h_j
  /-- For every world `w` that the events of `rho` timed before `t` lead to from the world in which
      every validator `u` holds `M.initial S u`, no body that `v` holds in `w` has a justified
      height greater than `v`'s store's. -/
  noHighJustifications_stateBeforeTime : ∀ (S : Setup V) (rho : Record.Run V) (t : Time) (v : V),
    ∀ w ∈ (rho.events.filter (fun e => decide (e.time < t))).foldlM (worldStepOf M S)
        (fun u => M.initial S u),
    ∀ B ∈ (w v).st.bodies, (M.derive_named S.E S.cfg B).h_j ≤ (w v).st.core.h_j
  /-- For every world `w` the run `rho` can reach before its `i`-th event, no body that `v` holds in
      `w` has a height greater than `v`'s store's `h_max`. -/
  heights_le_hMax_stateBefore : ∀ (S : Setup V) (rho : Record.Run V) (i : Nat) (v : V),
    ∀ w ∈ stateBeforeOf M S rho i,
    ∀ D ∈ (w v).st.bodies, (M.derive_named S.E S.cfg D).h ≤ (w v).st.core.h_max
  /-- For every world `w` the run `rho` can reach before its `i`-th event and every body `D` that
      `v` holds in `w`, the height `v`'s store records for `D`'s erasure is the height of `D`'s
      chain state. -/
  derivedView_stateBefore_h : ∀ (S : Setup V) (rho : Record.Run V) (i : Nat) (v : V),
    ∀ w ∈ stateBeforeOf M S rho i,
    ∀ D ∈ (w v).st.bodies,
      ((w v).st.core.σ D.erase).h = (M.derive_named S.E S.cfg D).h
  /-- If `v`'s round-`r` action has the FG source `Cfg`, some body `C` of the store
      `actionReadAt S rho v r` erases to `Cfg`, the store's height, entry and `nj` bit at `Cfg` are
      those of `C`'s chain state, and the action's confirmation witness is `C`'s entry. -/
  action_witness : ∀ (S : Setup V) (rho : Run V) (v : V) (r : Round) (Cfg : Block V),
    actionFGSource S (actionReadAt S rho v r) = some Cfg →
      ∃ C : NamedBlock V,
        C ∈ (actionReadAt S rho v r).st.bodies ∧ C.erase = Cfg ∧
        ((actionReadAt S rho v r).st.core.σ Cfg).h = (M.derive_named S.E S.cfg C).h ∧
        ((actionReadAt S rho v r).st.core.σ Cfg).T_h = (M.derive_named S.E S.cfg C).T_h ∧
        ((actionReadAt S rho v r).st.core.σ Cfg).nj = (M.derive_named S.E S.cfg C).nj ∧
        fgConfirmationWitness S (actionReadAt S rho v r) =
          some (M.derive_named S.E S.cfg C).T_h
  /-- Under `AdmissibleFieldsOn S rho Hs Xb lo`, every body `D` of `v`'s round-`r` action store has,
      in that store, the entry of its chain state. -/
  derivedStateAgrees_actionStoreAtOn : ∀ (S : Setup V) {rho : Run V} (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int}, AdmissibleFieldsOn S rho Hs Xb lo →
    ∀ (v : V) (r : Round), ∀ D ∈ (actionStoreAt S rho v r).st.bodies,
      ((actionStoreAt S rho v r).st.core.σ D.erase).T_h = (M.derive_named S.E S.cfg D).T_h
  /-- Under `AdmissibleFieldsOn S rho Hs Xb lo`, if `v ∈ Xb` and `D` is a body of `v`'s round-`r`
      action store, some body `K` of that store erases to `D`'s entry, has `D`'s height, is an
      ancestor of `D`, and satisfies `RunBlockOn S rho Xb K`. -/
  action_named_checkpointOn : ∀ (S : Setup V) {rho : Run V} (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int}, AdmissibleFieldsOn S rho Hs Xb lo →
    ∀ {v : V}, v ∈ Xb → ∀ {r : Round} {D : NamedBlock V},
      D ∈ (actionStoreAt S rho v r).st.bodies →
    ∃ K : NamedBlock V,
      K ∈ (actionStoreAt S rho v r).st.bodies ∧
      K.erase = (M.derive_named S.E S.cfg D).T_h ∧
      (M.derive_named S.E S.cfg K).h = (M.derive_named S.E S.cfg D).h ∧
      NamedBlock.Preceq K D ∧
      RunBlockOn S rho Xb K
  /-- Under `AdmissibleFieldsOn S rho Hs Xb lo`, if `a`'s signer is in `Xb`, emits `a` at `ta`, and
      `a`'s height pair names the height `h`, then the signer's round-`a.round` action store has
      bodies `D` and `K` at height `h` with `K` erasing to `D`'s entry and `K.erase ⪯ D.erase`, its
      FG source is `D`'s erasure, its confirmation witness is `K`'s entry, and `a`'s height pair is
      the target vote for `K`'s root at `h` or the timeout at `h`. -/
  honestHeightRow_confirmationWitnessOn : ∀ (S : Setup V) {rho : Run V} (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int}, AdmissibleFieldsOn S rho Hs Xb lo →
    ∀ {a : NamedAttestation V} {ta : Time} {h : Height},
    a.val_index ∈ Xb →
    rho.emits S a.val_index (Object.attest a) ta →
    a.height_pair.erase.height? = some h →
    ∃ D K : NamedBlock V,
      fgConfirmationWitness S
          (actionStoreAt S rho a.val_index a.round) =
        some (M.derive_named S.E S.cfg K).T_h ∧
      D ∈ (actionStoreAt S rho a.val_index a.round).st.bodies ∧
      actionFGSource S (actionStoreAt S rho a.val_index a.round) = some D.erase ∧
      (M.derive_named S.E S.cfg D).h = h ∧
      K ∈ (actionStoreAt S rho a.val_index a.round).st.bodies ∧
      K.erase = (M.derive_named S.E S.cfg D).T_h ∧
      (M.derive_named S.E S.cfg K).h = h ∧
      Block.Preceq K.erase D.erase ∧
      (a.height_pair.erase = HeightPair.target h K.erase.root ∨
        a.height_pair.erase = HeightPair.timeout h)
  /-- Under `AdmissibleFieldsOn S rho Hs Xb lo`, with `Hs` non-increasing over time and contained in
      `Xb`, and the validators outside `Hs rho.horizon` weighing less than a third of the total: if
      `v ∈ Xb`, `RunBlockOn S rho Xb T` holds with `T` at height `k ≥ 2`, every height-`k` row
      emitted by a member of `Hs rho.horizon` has `T`'s erasure as its action's confirmation
      witness, and `v`'s `h_max` after `n` events is at most `k + 1`, then `v`'s finalized block
      there is an ancestor of `T.erase`. -/
  storeF_preceq_checkpoint_of_windowOn : ∀ (S : Setup V) {rho : Run V} (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int}, AdmissibleFieldsOn S rho Hs Xb lo →
    (∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) → (∀ t : Int, Hs t ⊆ Xb) →
    Execution.BelowOneThird S (Hs rho.horizon) →
    ∀ {v : V}, v ∈ Xb → ∀ {n : Nat} {k : Height} {T : NamedBlock V},
    RunBlockOn S rho Xb T →
    (M.derive_named S.E S.cfg T).h = k → 2 ≤ k →
    (∀ (b : NamedAttestation V) (tb : Time), b.val_index ∈ Hs rho.horizon →
      NamedRun.emits S rho b.val_index (Object.attest b) tb →
      b.height_pair.erase.height? = some k →
      fgConfirmationWitness S (actionStoreAt S rho b.val_index b.round) = some T.erase) →
    (rho.stateBefore S n v).st.core.h_max ≤ k + 1 →
    Block.Preceq (rho.stateBefore S n v).st.core.F T.erase

end DecoupledConsensusModel.Sts.Record
