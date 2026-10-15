import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bInvariantActiveSinceW
import Proofs.Claims.Restated.Claim13bStepConeIter
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13beRoute3_44
import Proofs.Claims.Restated.Claim13beRoute3_45
import Proofs.Claims.Restated.Claim13beRoute3_46
import Proofs.Claims.Restated.Claim13beRoute3_48
import Proofs.Claims.Restated.Claim13beRoute3_49b
import Proofs.Claims.Restated.Claim13beRoute3_50b
import Proofs.Claims.Restated.Claim13beRoute3_51
import Proofs.Claims.Restated.Claim13beRoute3_71
import Proofs.Claims.Restated.Claim13beRoute3_72
import Proofs.Claims.Restated.Claim13beRoute3_76
import Proofs.Claims.Restated.Claim13beRoute3_83
import Proofs.Claims.Restated.Claim13beRoute3_85
import Proofs.Claims.Restated.Claim13beRoute3_85b
import Proofs.Claims.Restated.Claim13beRoute3_88
import Proofs.Claims.Restated.Claim13beRoute3_91
import Proofs.Claims.Restated.Vocabulary_Execution_EmissionShape
import Proofs.Vocabulary.Protocol.ChainState.Chain
import Proofs.Vocabulary.ModelVocabulary
import Proofs.Vocabulary.Protocol.ChainState.DerivationGeometry
import Proofs.Claims.Restated.Vocabulary_Protocol_Duties_Inputs_ActionSources
import Proofs.Claims.Restated.Vocabulary_Protocol_Duties_Proposals_Actions
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_Action
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_PostHealingContinuation
import Proofs.Claims.Restated.Vocabulary_Protocol_ValidatorClient_HeightPairCases
import Proofs.Vocabulary.Protocol.ValidatorClient.RecordFresh
import Proofs.Claims.Restated.Vocabulary_Protocol_ValidatorClient_Bridge
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Event
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_RecordFresh
import Proofs.Claims.Restated.Vocabulary_Protocol_ValidatorClient_RecordTargetHistory
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActiveSinceW
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.Claim13beRoute3_72
import Model.Conditions.Claim13beRoute3_74
import Model.Conditions.Claim13beRoute3_83
import Model.Conditions.RunAll
import Model.Conditions.RunVocabulary
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Node
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Healing_Action
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_Store
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Proofs.Vocabulary.Protocol.ForkChoice.Views.ProposalCore
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_HeightPairCases
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_25
import Proofs.Claims.Spec2Claims.Claim13beRoute3_85c

/-!
# Honest attestation rows at the height of the FG source

The attestation an honest validator emits at a round whose FG source is a run block `P` is a vote at
`P`'s height naming `P`'s entry, or empty under its own lock, and such a row is covered by a later
honest proposal descending from `P`. Stated along a path `W` of the run for a model
`M : Record.Model V`, then along the path an execution follows, and at an honest opening after the
progress deadline.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

local macro "p51% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_51)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "pRT% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Vocabulary_Protocol_ValidatorClient_RecordTargetHistory)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Protocol (ChainState HeightConfig)
open Protocol (Record height_pair own_lock record_attestation)
open Proofs.HealingLemmas

/-! ### A signing record's history along one path of the run -/

/-- Along a path `W` of the run, either the run has no `n`-th event and the world after it is the
    world before it, or the `n`-th event is some `e` and the world after it is one of the worlds `e`
    can lead to from the world before it. -/
private theorem path_step₈₅c {S : Setup V} {rho : Record.Run V} {W : Nat → V → M.N}
    (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (n : Nat) :
    (rho.events[n]? = none ∧ W (n + 1) = W n) ∨
      ∃ e : Record.Event V, rho.events[n]? = some e ∧
        W (n + 1) ∈ Record.worldStepOf M S (W n) e := by
  have h := (hW n).2
  rcases he : rho.events[n]? with _ | e
  · left
    refine ⟨rfl, ?_⟩
    have hnil : (rho.events.drop n).take (n + 1 - n) = [] := by
      rw [List.drop_eq_nil_of_le (List.getElem?_eq_none_iff.mp he), List.take_nil]
    rw [hnil] at h
    exact Set.mem_singleton_iff.mp h
  · right
    refine ⟨e, rfl, ?_⟩
    rw [(p51% drop_take_succ₅₁) he] at h
    exact ((p51% mem_foldlM_singleton₅₁) S _ _ e).1 h

/-- Along a path `W` of the run, if `v`'s signing record in the world before the `n`-th event holds
    the target `T` at height `h`, then some earlier event is a tick of `v` whose outcome on the path
    sends an attestation whose erased height pair is the target `(h, T)`. -/
private theorem recordTarget_along₈₅c (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (v : V) :
    ∀ (n : Nat) {h : Height} {T : BlockId}, (W n v).record.legacy.target h = some T →
      ∃ i : Nat, i < n ∧ ∃ (t : Time) (a : NamedAttestation V),
        rho.events[i]? = some (.tick v t) ∧
        ∃ out : M.N × List (NamedObject V), M.tick S v (W i v) t ⇢ out ∧ W (i + 1) v = out.1 ∧
          NamedObject.attest a ∈ out.2 ∧ a.erase.height_pair = HeightPair.target h T := by
  intro n
  induction n with
  | zero =>
    intro h T htarget
    have h0 : W 0 = fun v' => M.initial S v' := Set.mem_singleton_iff.mp (hW 0).1
    have h1 : W 0 v = M.initial S v := congrFun h0 v
    rw [h1, facts.nd.initial_record_legacy_target S v h] at htarget
    cases htarget
  | succ n ih =>
    intro h T htarget
    rcases path_step₈₅c hW n with ⟨-, hEq⟩ | ⟨e, hev, hstep⟩
    · rw [hEq] at htarget
      obtain ⟨i, hi, r⟩ := ih htarget
      exact ⟨i, Nat.lt_succ_of_lt hi, r⟩
    · by_cases he : ∃ t, e = .tick v t
      · obtain ⟨t, rfl⟩ := he
        simp only [Record.worldStepOf, Set.mem_setOf_eq] at hstep
        rcases hstep with ⟨out, hout, hEq⟩ | ⟨-, hEq⟩
        · have hv : W (n + 1) v = out.1 := by rw [hEq, Function.update_self]
          rw [hv] at htarget
          cases hpre : (W n v).record.legacy.target h with
          | some X =>
            have hmono := facts.nd.target_mono_on_tick_emit S v (W n v) t hpre out hout
            have hXT : X = T := Option.some.inj (hmono.symm.trans htarget)
            subst hXT
            obtain ⟨i, hi, r⟩ := ih hpre
            exact ⟨i, Nat.lt_succ_of_lt hi, r⟩
          | none =>
            obtain ⟨a, ha, hpair⟩ :=
              facts.nd.on_tick_emit_target_introduced S v (W n v) t hpre out hout htarget
            exact ⟨n, Nat.lt_succ_self n, t, a, hev, out, hout, hv, ha, hpair⟩
        · rw [hEq] at htarget
          obtain ⟨i, hi, r⟩ := ih htarget
          exact ⟨i, Nat.lt_succ_of_lt hi, r⟩
      · rw [(pRT% rt_step_record) facts S (W n) (W (n + 1)) e v hstep (fun t h => he ⟨t, h⟩)]
          at htarget
        obtain ⟨i, hi, r⟩ := ih htarget
        exact ⟨i, Nat.lt_succ_of_lt hi, r⟩

/-- Along a path `W` of the run, if `v`'s signing record in the world before the `n`-th event times
    the height `h` out, then some earlier event is a tick of `v` whose outcome on the path sends an
    attestation whose erased height pair is the timeout at `h`. -/
private theorem recordTimeout_along₈₅c (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (v : V) :
    ∀ (n : Nat) {h : Height}, (W n v).record.legacy.timeout h = true →
      ∃ i : Nat, i < n ∧ ∃ (t : Time) (a : NamedAttestation V),
        rho.events[i]? = some (.tick v t) ∧
        ∃ out : M.N × List (NamedObject V), M.tick S v (W i v) t ⇢ out ∧ W (i + 1) v = out.1 ∧
          NamedObject.attest a ∈ out.2 ∧ a.erase.height_pair = HeightPair.timeout h := by
  intro n
  induction n with
  | zero =>
    intro h htimeout
    have h0 : W 0 = fun v' => M.initial S v' := Set.mem_singleton_iff.mp (hW 0).1
    have h1 : W 0 v = M.initial S v := congrFun h0 v
    rw [h1, facts.nd.initial_record_legacy_timeout S v h] at htimeout
    cases htimeout
  | succ n ih =>
    intro h htimeout
    rcases path_step₈₅c hW n with ⟨-, hEq⟩ | ⟨e, hev, hstep⟩
    · rw [hEq] at htimeout
      obtain ⟨i, hi, r⟩ := ih htimeout
      exact ⟨i, Nat.lt_succ_of_lt hi, r⟩
    · by_cases he : ∃ t, e = .tick v t
      · obtain ⟨t, rfl⟩ := he
        simp only [Record.worldStepOf, Set.mem_setOf_eq] at hstep
        rcases hstep with ⟨out, hout, hEq⟩ | ⟨-, hEq⟩
        · have hv : W (n + 1) v = out.1 := by rw [hEq, Function.update_self]
          rw [hv] at htimeout
          cases hpre : (W n v).record.legacy.timeout h with
          | true =>
            obtain ⟨i, hi, r⟩ := ih hpre
            exact ⟨i, Nat.lt_succ_of_lt hi, r⟩
          | false =>
            obtain ⟨a, ha, hpair⟩ :=
              facts.nd.on_tick_emit_timeout_introduced S v (W n v) t hpre out hout htimeout
            exact ⟨n, Nat.lt_succ_self n, t, a, hev, out, hout, hv, ha, hpair⟩
        · rw [hEq] at htimeout
          obtain ⟨i, hi, r⟩ := ih htimeout
          exact ⟨i, Nat.lt_succ_of_lt hi, r⟩
      · rw [(pRT% rt_step_record) facts S (W n) (W (n + 1)) e v hstep (fun t h => he ⟨t, h⟩)]
          at htimeout
        obtain ⟨i, hi, r⟩ := ih htimeout
        exact ⟨i, Nat.lt_succ_of_lt hi, r⟩

/-- If `v ∈ Xb`, `C` is a run block along `W` read through `Xb`, and the FG source of a node state
    `n` of `v`'s round-`r` action read from `W (strictEventIndex rho (S.a r))` can return `C`'s
    erasure, then `C` is among `v`'s bodies in that world and `n`'s chain state at that source is
    `C`'s own. -/
theorem sourceBody_of_actionFGSource_l85c (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} (hv : v ∈ Xb) {r : Round} {C : NamedBlock V}
    (hCrun : Restated.RunBlockOn M S rho W Xb C)
    {n : M.N}
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r)
    (hsrc : Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ some C.erase) :
    C ∈ (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).st.bodies ∧
      n.st.core.σ C.erase = M.derive_named S.E S.cfg C := by
  have hwmem := (p51% mem_stateBeforeTime_along₅₁) hf.sorted hf.onePath
    (Restated.Vocabulary.Execution.Setup.a M S r)
  have hmem : n ∈ Restated.Vocabulary.Proofs.HealingSurface.actionReadAt M S rho v r :=
    ⟨W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)), hwmem, hn⟩
  obtain ⟨D, hD, hDerase, hDderive, -⟩ :=
    Restated.Vocabulary.Proofs.NamedActionSources.action_witness facts S rho v r n hmem C.erase hsrc
  have hDrun : Restated.RunBlockOn M S rho W Xb D :=
    Restated.actionBody_runBlock_coverageOn facts S Hs Xb hf hv hn hD
  have hDC : D = C :=
    hf.rootCollisionFree.root_injective D C hDrun hCrun D C
      (Or.inl (Proofs.NamedAncestry.named_self D))
      (Or.inr (Proofs.NamedAncestry.named_self C)) (by
        rw [← Proofs.NamedWire.erase_root D, ← Proofs.NamedWire.erase_root C, hDerase])
  subst hDC
  refine ⟨?_, hDderive⟩
  rw [← (p51% actionReadFrom_bodies₅₁) facts S _ r n hn]
  exact hD

/-- Along the bundle's path `W`, let `B` be a proposal of slot `s` by a proposer in the set for
    `S.a r + Δ`, with `lo ≤ S.a r` and `S.a r + Δ ≤ proposal_time s ≤ horizon`. If `C`, at height
    `H` with entry root `T`, is an ancestor of `B`'s parent at height `H`, `v` is in the set for
    `proposal_time s`, holds `C` strictly before `S.a r` and is flagged awake for `r`, and round `r`
    is in the row window of the proposer's store, then every attestation of `v`'s round-`r`
    attestation duty that carries `(H, T)` as a vote or a timeout is on the named chain of `B`'s
    parent with `v` in its progress set (and in its target participation for a target vote), or
    among `B`'s own attestations. -/
theorem actionAttestationAt_coveredAtProposal_ofBodyOn_l85c (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {r : Round} {C : NamedBlock V} {H : Height} {T : BlockId}
    (hCheight : (M.derive_named S.E S.cfg C).h = H)
    (hCtarget : (M.derive_named S.E S.cfg C).T_h.root = T)
    {s : Slot} {B : NamedBlock V}
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core.toHealing
      (M.proposal_time S.E s)
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).cache ⇢ c)
    (hB : M.proposal_with (M.gradeContract c) .poolAndCarried
      S.E S.hc (S.node (S.E.proposer s))
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
        (M.proposal_time S.E s)) ⇢ some B)
    (hCP : NamedBlock.Preceq C B.parent)
    (hPheight : (M.derive_named S.E S.cfg B.parent).h = H)
    (hprop : S.E.proposer s ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ))
    (hhor : M.proposal_time S.E s ≤ rho.horizon)
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S r))
    (hdelay : (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ ≤ M.proposal_time S.E s)
    {v : V} (hv : v ∈ Hs (M.proposal_time S.E s))
    (hCpre : C ∈
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).st.bodies)
    (hinWindow : M.inWindow S.hc
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
        (M.proposal_time S.E s)).core r = true)
    (hA : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick v (Restated.Vocabulary.Execution.Setup.a M S r)) → M.awake_for_grade2 S v (W j v) r) :
    ∀ ast ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r,
    ∀ D, M.duties_attest_with (M.gradeContract ast.cache) S.E S.hc (S.node v) ast.st ast.record ⇢ D →
    (D.2.2.height_pair = .vote H T false ∨ D.2.2.height_pair = .vote H T true) →
    ((D.2.2 ∈ Protocol.named_chain_attestations B.parent ∧
        v ∈ (M.derive_named S.E S.cfg B.parent).progress ∧
        (D.2.2.height_pair = .vote H T false →
          v ∈ (M.derive_named S.E S.cfg B.parent).target_participation)) ∨
      D.2.2 ∈ B.attestations) := by
  intro ast hast D hD hpair
  have hFchain := facts.dt.chainRows_iff_named_chain
  have hFprog := facts.csAdded.namedPair_mem_progress_of_suffix_same_height
  have hFtarget := facts.csAdded.namedTarget_mem_of_suffix_same_height
  have hW := hf.onePath
  have hwmem := (p51% mem_stateBeforeTime_along₅₁) hf.sorted hW
    (Restated.Vocabulary.Execution.Setup.a M S r)
  set a := D.2.2 with ha
  set pr := M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
    (M.proposal_time S.E s) with hpr
  have hmem : ast ∈ Restated.Vocabulary.Proofs.HealingSurface.actionReadAt M S rho v r :=
    ⟨W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)), hwmem, hast⟩
  have hdelayLe : (Restated.Vocabulary.Execution.Setup.a M S r) ≤
      (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ :=
    le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)
  have hvDelta : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ) := hHs _ _ hdelay hv
  have hvA : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)) := hHs _ _ hdelayLe hvDelta
  have hactionHor : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon :=
    hdelayLe.trans (hdelay.trans hhor)
  have hemitV : Restated.Vocabulary.Execution.Run.emits M S rho W v (Object.attest a)
      (Restated.Vocabulary.Execution.Setup.a M S r) :=
    Restated.honest_emits_exact_actionAttestationAtOn facts S Hs Xb hf r hvA hactionHor hpost hA
      (fun j hj => hf.tick_outcome j _ _ hj) ast hast D hD
  have haVal : a.val_index = v :=
    (Restated.Vocabulary.Proofs.Optimistic.emits_attest_shape facts S W hW hemitV).1
  have haRound : a.round = r := by
    obtain ⟨g2, hg2⟩ := facts.dt.grade2_block_with_nonempty (M.gradeContract ast.cache) S.E S.hc
      (M.toHealing ast.st.core) (M.round_of S.hc (M.toHealing ast.st.core).s)
    obtain ⟨G, hG⟩ := facts.dt.get_sg_vote_with_nonempty (M.gradeContract ast.cache) S.E S.hc
      (M.toHealing ast.st.core) (M.round_of S.hc (M.toHealing ast.st.core).s) g2
    exact (Restated.Vocabulary.Proofs.HealingSurface.actionAttestationAt_shape facts S rho v r ast hmem
      D hD g2 hg2 G hG).2.1
  have hemit : Restated.Vocabulary.Execution.Run.emits M S rho W a.val_index
      (Object.attest a) ((Restated.Vocabulary.Execution.Setup.a M S a.round)) := by
    rw [haVal, haRound]
    exact hemitV
  have hemitAtR : Restated.Vocabulary.Execution.Run.emits M S rho W a.val_index
      (Object.attest a) ((Restated.Vocabulary.Execution.Setup.a M S r)) := by
    rw [haVal]
    exact hemitV
  have hnotC := Restated.emittedAttestation_not_mem_named_chain_beforeOn facts
    S Hs Xb hf hHs hvA hemitV hCpre
  have hprocessed := Restated.honestAttestation_mem_processedAtProposal_after_gstOn facts
    S Hs Xb hf hHs hhor (by rw [haVal]; exact hvDelta) hprop hemitAtR hpost hdelay
  have haProcessed := Restated.exactRow_mem_namedProcessedOn facts
    S Hs Xb hf hHs (by rw [haVal]; exact hv) hemit hprocessed
  obtain ⟨L, hL⟩ := facts.dt.select_nonempty .poolAndCarried S.hc pr
  have haSelected : a ∈ L :=
    facts.dt.mem_select_of_processed_inWindow .poolAndCarried S.hc _ haProcessed
      (by rw [haRound]; exact hinWindow) L hL
  obtain ⟨input, hinput⟩ := facts.dt.with_proposal_input_nonempty (M.gradeContract c) S.E S.hc
    (S.node (S.E.proposer s)) (M.toHealing pr.core)
  have _hr_s1 : M.reachedStore pr := facts.sto.reachedStore_setClock S.E _ (M.proposal_time S.E s) (facts.nd.reachedStore_of_node _ (facts.ndRun.stateBeforeOf_reachedNode S rho (strictEventIndex rho (M.proposal_time S.E s)) (W (strictEventIndex rho (M.proposal_time S.E s))) (hf.onePath _).1 (S.E.proposer s)))
  have hpay := Restated.Vocabulary.Proofs.NamedActions.proposal_payload facts
    (M.gradeContract c) .poolAndCarried S.E S.hc (S.node (S.E.proposer s)) pr B hB input hinput L hL
  by_cases hchain : a ∈ M.chainRows B.parent
  · left
    have hchain' := (hFchain B.parent a).mp hchain
    refine ⟨hchain', ?_, ?_⟩
    · rw [← haVal]
      apply hFprog S.E S.cfg hCP hchain' hnotC
      · rw [hPheight, hCheight]
      · rw [hCheight, hCtarget]
        exact hpair
    · intro htarget
      rw [← haVal]
      apply hFtarget S.E S.cfg hCP hchain' hnotC
      · rw [hPheight, hCheight]
      · rw [hCheight, hCtarget]
        exact htarget
  · right
    rw [hpay.2.2.2.2.2.2.1]
    apply facts.dt.mem_proposalRows_of_unique B.parent _ a haSelected hchain
    intro b hb hval hround
    exact Restated.honest_selected_row_uniqueOn facts S Hs Xb hf hHs s L hL haSelected hb
      (by rw [haVal]; exact hv) hval hround

/-- For every world `w` strictly before `S.a r` and every node state `n` of `v`'s round-`r` action
    read from `w` whose FG source can return `Q`, the attestation of every outcome of `v`'s
    attestation duty on `n` has as height pair the codec, at the fields of `Q`'s chain state in `n`,
    of the legacy pair of `v`'s record in `w` with that attestation's own finality pair. -/
theorem actionRow_eq_encode_l85c (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (v : V)
    (r : Round) {Q : Block V} :
    ∀ w ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho
      (Restated.Vocabulary.Execution.Setup.a M S r),
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (w v) r,
    Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ some Q →
    ∀ D, M.duties_attest_with (M.gradeContract n.cache) S.E S.hc (S.node v) n.st n.record ⇢ D →
    D.2.2.height_pair =
      M.encodeHeight
        (some ((n.st.core.σ Q).h, (n.st.core.σ Q).T_h.root, (n.st.core.σ Q).nj))
        (M.height_pair (w v).record.legacy
          (some ((n.st.core.σ Q).h, (n.st.core.σ Q).T_h.root, (n.st.core.σ Q).nj))
          D.2.2.finality_pair) := by
  intro w hw n hn hsrc D hD
  obtain ⟨Ar, hAr⟩ := facts.dt.round_action_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (S.node v) (M.toHealing n.st.core) n.record
  have h := Restated.Vocabulary.Proofs.HealingSurface.named_round_action_height_pair facts
    (M.gradeContract n.cache) S.E S.hc (S.node v) (M.toHealing n.st.core) n.record Ar hAr
    (some Q) hsrc
  simp only [Option.map_some, Record.Model.HS.σ, facts.sto.ModelProperties_toHealing_σ] at h
  rw [facts.dt.attest_with_row _ S.E S.hc (S.node v) n.st n.record D hD Ar hAr,
    ← (p51% actionReadFrom_record₅₁) facts S (w v) r n hn]
  exact h

/-- Two run blocks along `W` read through `Xb` with the same entry root have the same `nj` bit. -/
theorem nj_eq_of_entryRoot_l85c (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {A B : NamedBlock V} (hA : Restated.RunBlockOn M S rho W Xb A)
    (hB : Restated.RunBlockOn M S rho W Xb B)
    (hT : (M.derive_named S.E S.cfg A).T_h.root =
      (M.derive_named S.E S.cfg B).T_h.root) :
    (M.derive_named S.E S.cfg A).nj = (M.derive_named S.E S.cfg B).nj := by
  obtain ⟨EA, hEA, hEAe, hEAh, -⟩ := Restated.entry_named_l85 facts S.E S.cfg A
  obtain ⟨EB, hEB, hEBe, hEBh, -⟩ := Restated.entry_named_l85 facts S.E S.cfg B
  have hroot : EA.root = EB.root := by
    rw [← Proofs.NamedWire.erase_root EA, ← Proofs.NamedWire.erase_root EB, hEAe, hEBe]
    exact hT
  have hEq : EA = EB :=
    hf.rootCollisionFree.root_injective A B hA hB EA EB (Or.inl hEA) (Or.inr hEB) hroot
  subst hEq
  rw [← facts.csAdded.nj_eq_on_plateau_l85 S.E S.cfg hEA hEAh, facts.csAdded.nj_eq_on_plateau_l85 S.E S.cfg hEB hEBh]

/-- If `v`'s record in `W (strictEventIndex rho t)` holds the target `T` at `h`, then `v` emitted
    along `W`, at some instant before `t`, an attestation whose height pair is the target vote
    `(h, T)`. -/
theorem recordTarget_emits_before_l85c (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo) (v : V) (t : Int)
    {h : Height} {T : BlockId}
    (hrec : (W (strictEventIndex rho t) v).record.legacy.target h = some T) :
    ∃ (t' : Int) (a : NamedAttestation V), t' < t ∧
      (Restated.Vocabulary.Execution.Run.emits M S rho W v (Object.attest a) t') ∧
      a.height_pair = .vote h T false := by
  obtain ⟨i, hi, t', a, hevent, out, hout, hstep, hemitted, hpair⟩ :=
    recordTarget_along₈₅c facts S hf.onePath v _ hrec
  have hlt : t' < t := (p51% time_lt_of_lt_strict₅₁) hf.sorted hevent hi
  exact ⟨t', a, hlt, ⟨i, hevent, out, hout, hstep, hemitted⟩,
    vote_of_erase_target_l85c (by rw [← namedAttestation_erase_height_pair]; exact hpair)⟩

/-- If `v`'s record in `W (strictEventIndex rho t)` times `h` out, then `v` emitted along `W`, at
    some instant before `t`, an attestation whose height pair is a timeout vote at `h`. -/
theorem recordTimeout_emits_before_l85c (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo) (v : V) (t : Int)
    {h : Height}
    (hrec : (W (strictEventIndex rho t) v).record.legacy.timeout h = true) :
    ∃ (t' : Int) (a : NamedAttestation V) (e : BlockId), t' < t ∧
      (Restated.Vocabulary.Execution.Run.emits M S rho W v (Object.attest a) t') ∧
      a.height_pair = .vote h e true := by
  obtain ⟨i, hi, t', a, hevent, out, hout, hstep, hemitted, hpair⟩ :=
    recordTimeout_along₈₅c facts S hf.onePath v _ hrec
  have hlt : t' < t := (p51% time_lt_of_lt_strict₅₁) hf.sorted hevent hi
  obtain ⟨e, he⟩ := vote_of_erase_timeout_l85c
    ((namedAttestation_erase_height_pair a).symm.trans hpair)
  exact ⟨t', a, e, hlt, ⟨i, hevent, out, hout, hstep, hemitted⟩, he⟩

/-- If the FG source of the node state `n` can return `none`, the attestation of every outcome of
    `v`'s attestation duty on `n` has the empty height pair. -/
private theorem actionRow_empty_of_none₈₅c (facts : Record.Facts M) (S : Setup V) (v : V)
    (n : M.N)
    (hsrc : Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ none) :
    ∀ D, M.duties_attest_with (M.gradeContract n.cache) S.E S.hc (S.node v) n.st n.record ⇢ D →
      D.2.2.height_pair = .empty := by
  intro D hD
  obtain ⟨Ar, hAr⟩ := facts.dt.round_action_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (S.node v) (M.toHealing n.st.core) n.record
  have h := Restated.Vocabulary.Proofs.HealingSurface.named_round_action_height_pair facts
    (M.gradeContract n.cache) S.E S.hc (S.node v) (M.toHealing n.st.core) n.record Ar hAr
    none hsrc
  simp only [Option.map_none, facts.vc.encodeHeight_none] at h
  rw [facts.dt.attest_with_row _ S.E S.hc (S.node v) n.st n.record D hD Ar hAr]
  exact h

/-- If `P` is a run block along `W` read through `Xb` with `nj(P) = false` and entry root `eW`, and
    every attestation emitted along `W` by a member of the set for its instant with a vote at `h(P)`
    names `eW`, then no attestation emitted along `W` by a member of the set for its instant is a
    timeout vote at `h(P)`. -/
theorem noTimeoutVote_l85c (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {P : NamedBlock V} (hPrun : Restated.RunBlockOn M S rho W Xb P)
    (hnj : (M.derive_named S.E S.cfg P).nj = false)
    {eW : BlockId} (heW : (M.derive_named S.E S.cfg P).T_h.root = eW)
    (hone : ∀ (w : V) (t : Int) (a : NamedAttestation V) (e' : BlockId) (b' : Bool),
      (Restated.Vocabulary.Execution.Run.emits M S rho W w (Object.attest a) t) → w ∈ Hs t →
      a.height_pair = .vote (M.derive_named S.E S.cfg P).h e' b' → e' = eW)
    (u : V) :
    ∀ (k : Round) (a : NamedAttestation V) (t : Int), a.round = k →
      (Restated.Vocabulary.Execution.Run.emits M S rho W u (Object.attest a) t) → u ∈ Hs t →
      ∀ e' : BlockId, a.height_pair ≠ .vote (M.derive_named S.E S.cfg P).h e' true := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro a t hk hemit hut e' hpair
  have hW := hf.onePath
  have he' : e' = eW := hone u t a e' true hemit hut hpair
  obtain ⟨-, ht⟩ := Restated.Vocabulary.Proofs.Optimistic.emits_attest_shape facts S W hW hemit
  have hemitk : (Restated.Vocabulary.Execution.Run.emits M S rho W u (Object.attest a) ((Restated.Vocabulary.Execution.Setup.a M S k))) := by
    rw [← hk, ← ht]; exact hemit
  have hutk : u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k)) := by
    rw [← hk, ← ht]; exact hut
  have hwmem := (p51% mem_stateBeforeTime_along₅₁) hf.sorted hW
    (Restated.Vocabulary.Execution.Setup.a M S k)
  obtain ⟨n, hn, D, hD⟩ := (p51% actionAttestation_nonempty₅₁) facts S
    (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S k)) u) k (S.node u)
  have haeq : a = D.2.2 :=
    ((Restated.action_run_emissionOn facts S rho Hs Xb hf u k a).mp hemitk).2.2 n hn D hD
  rw [haeq] at hpair
  obtain ⟨o, ho⟩ := (p51% actionFGSource_nonempty₅₁) facts S n
  cases o with
  | none =>
    rw [actionRow_empty_of_none₈₅c facts S u n ho D hD] at hpair
    cases hpair
  | some Q =>
    have hrow := Restated.actionRow_eq_encode_l85c facts S rho u k _ hwmem n hn ho D hD
    have hmem : n ∈ Restated.Vocabulary.Proofs.HealingSurface.actionReadAt M S rho u k :=
      ⟨W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S k)), hwmem, hn⟩
    obtain ⟨DQ, hDQ, -, hDQderive, -⟩ :=
      Restated.Vocabulary.Proofs.NamedActionSources.action_witness facts S rho u k n hmem Q ho
    have hDQrun : Restated.RunBlockOn M S rho W Xb DQ :=
      Restated.actionBody_runBlock_coverageOn facts S Hs Xb hf (hHsXb _ hutk) hn hDQ
    rw [hDQderive] at hrow
    rcases facts.vc.height_pair_cases_l85c
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S k)) u).record.legacy
        (M.derive_named S.E S.cfg DQ).h (M.derive_named S.E S.cfg DQ).T_h.root
        (M.derive_named S.E S.cfg DQ).nj D.2.2.finality_pair
      with htg | ⟨hto, hcause⟩ | ⟨hem, -⟩
    · rw [htg, facts.vc.encodeHeight_of_target] at hrow
      rw [hrow] at hpair
      exact absurd (NamedHeightPair.vote.inj hpair).2.2 (by decide)
    · rw [hto, facts.vc.encodeHeight_of_timeout] at hrow
      rw [hrow] at hpair
      obtain ⟨hQh, hQe, -⟩ := NamedHeightPair.vote.inj hpair
      rcases hcause with htimeout | ⟨rec, hrec, hne⟩ | hnjQ
      · rw [hQh] at htimeout
        obtain ⟨t', a', e'', hlt, hemit', hpair'⟩ :=
          Restated.recordTimeout_emits_before_l85c facts S Hs Xb hf u ((Restated.Vocabulary.Execution.Setup.a M S k)) htimeout
        obtain ⟨-, ht'⟩ := Restated.Vocabulary.Proofs.Optimistic.emits_attest_shape facts S W hW hemit'
        have hround : a'.round < k := by
          have hlt' : (Restated.Vocabulary.Execution.Setup.a M S a'.round) < (Restated.Vocabulary.Execution.Setup.a M S k) := by rw [← ht']; exact hlt
          exact (Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).lt_iff_lt.mp hlt'
        exact ih a'.round hround a' t' rfl hemit' (hHs _ _ hlt.le hutk) e'' hpair'
      · rw [hQh] at hrec
        obtain ⟨t', a', hlt, hemit', hpair'⟩ :=
          Restated.recordTarget_emits_before_l85c facts S Hs Xb hf u ((Restated.Vocabulary.Execution.Setup.a M S k)) hrec
        have hrecW : rec = eW := hone u t' a' rec false hemit' (hHs _ _ hlt.le hutk) hpair'
        exact hne (hrecW.trans (hQe.trans he').symm)
      · have hnjeq := Restated.nj_eq_of_entryRoot_l85c facts S Hs Xb hf hDQrun hPrun
          (hQe.trans (he'.trans heW.symm))
        rw [hnjeq, hnj] at hnjQ
        cases hnjQ
    · rw [hem, facts.vc.encodeHeight_empty] at hrow
      rw [hrow] at hpair
      cases hpair

/-- Along `W`, let `P` be a run block read through `Xb` such that any two attestations emitted by
    members of the sets for their instants with votes at `h(P)` name the same entry, and let `u` be
    in the set for `S.a q`, awake for `q`, with `lo ≤ S.a q ≤ horizon`. Then every round-`q`
    attestation of `u` at an action node state whose FG source can return `P`'s erasure is either
    `vote h(P) T_h(P) b`, with `b = false` when `nj(P) = false`, or empty, with `u`'s own lock at
    `h(P)` naming a block other than `T_h(P)` and `h(P)` at most `u`'s justified height strictly
    before `S.a q`. -/
theorem honestRow_atSource_engine_l85c (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {P : NamedBlock V} (hPrun : Restated.RunBlockOn M S rho W Xb P)
    (hagree : ∀ (w₁ w₂ : V) (t₁ t₂ : Int) (a₁ a₂ : NamedAttestation V) (e₁ e₂ : BlockId)
      (b₁ b₂ : Bool),
      (Restated.Vocabulary.Execution.Run.emits M S rho W w₁ (Object.attest a₁) t₁) → w₁ ∈ Hs t₁ →
      a₁.height_pair = .vote (M.derive_named S.E S.cfg P).h e₁ b₁ →
      (Restated.Vocabulary.Execution.Run.emits M S rho W w₂ (Object.attest a₂) t₂) → w₂ ∈ Hs t₂ →
      a₂.height_pair = .vote (M.derive_named S.E S.cfg P).h e₂ b₂ → e₁ = e₂)
    {u : V} {q : Round} (hu : u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q))) (hhor : (Restated.Vocabulary.Execution.Setup.a M S q) ≤ rho.horizon)
    (hgat : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S q)) (hA : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S q)) → M.awake_for_grade2 S u (W j u) q) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) u) q,
    Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ some P.erase →
    ∀ D, M.duties_attest_with (M.gradeContract n.cache) S.E S.hc (S.node u) n.st n.record ⇢ D →
    ((D.2.2.height_pair =
          .vote (M.derive_named S.E S.cfg P).h
            (M.derive_named S.E S.cfg P).T_h.root false ∨
        D.2.2.height_pair =
          .vote (M.derive_named S.E S.cfg P).h
            (M.derive_named S.E S.cfg P).T_h.root true) ∧
      ((M.derive_named S.E S.cfg P).nj = false →
        D.2.2.height_pair =
          .vote (M.derive_named S.E S.cfg P).h
            (M.derive_named S.E S.cfg P).T_h.root false)) ∨
    (D.2.2.height_pair = .empty ∧
      ∃ locked : BlockId,
        M.own_lock
            (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) u).record.legacy
            (M.derive_named S.E S.cfg P).h
            D.2.2.finality_pair = some locked ∧
        locked ≠ (M.derive_named S.E S.cfg P).T_h.root ∧
        (M.derive_named S.E S.cfg P).h ≤
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) u).st.core.h_j) := by
  intro n hn hsrc D hD
  have hW := hf.onePath
  have hwmem := (p51% mem_stateBeforeTime_along₅₁) hf.sorted hW
    (Restated.Vocabulary.Execution.Setup.a M S q)
  obtain ⟨-, hσ⟩ := Restated.sourceBody_of_actionFGSource_l85c facts S Hs Xb hf (hHsXb _ hu) hPrun hn hsrc
  have hrow := Restated.actionRow_eq_encode_l85c facts S rho u q _ hwmem n hn hsrc D hD
  rw [hσ] at hrow
  have hemit : (Restated.Vocabulary.Execution.Run.emits M S rho W u (Object.attest D.2.2) ((Restated.Vocabulary.Execution.Setup.a M S q))) :=
    Restated.honest_emits_exact_actionAttestationAtOn facts S Hs Xb hf q hu hhor hgat hA
      (fun j hj => hf.tick_outcome j _ _ hj) n hn D hD
  rcases facts.vc.height_pair_cases_l85c
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) u).record.legacy
      (M.derive_named S.E S.cfg P).h (M.derive_named S.E S.cfg P).T_h.root
      (M.derive_named S.E S.cfg P).nj D.2.2.finality_pair
    with htg | ⟨hto, hcause⟩ | ⟨hem, locked, hl, hne⟩
  · rw [htg, facts.vc.encodeHeight_of_target] at hrow
    exact Or.inl ⟨Or.inl hrow, fun _ => hrow⟩
  · rw [hto, facts.vc.encodeHeight_of_timeout] at hrow
    have hone : ∀ (w : V) (t : Int) (a : NamedAttestation V) (e' : BlockId) (b' : Bool),
        (Restated.Vocabulary.Execution.Run.emits M S rho W w (Object.attest a) t) → w ∈ Hs t →
        a.height_pair = .vote (M.derive_named S.E S.cfg P).h e' b' →
        e' = (M.derive_named S.E S.cfg P).T_h.root :=
      fun w t a e' b' hem hw hp => hagree w u t ((Restated.Vocabulary.Execution.Setup.a M S q)) a _ e' _ b' true hem hw hp hemit hu hrow
    have heW : (M.derive_named S.E S.cfg P).T_h.root =
        (M.derive_named S.E S.cfg P).T_h.root := rfl
    refine Or.inl ⟨Or.inr hrow, fun hnj => ?_⟩
    exfalso
    rcases hcause with htimeout | ⟨rec, hrec, hne⟩ | hnjP
    · obtain ⟨t', a', e'', hlt, hemit', hpair'⟩ :=
        Restated.recordTimeout_emits_before_l85c facts S Hs Xb hf u ((Restated.Vocabulary.Execution.Setup.a M S q)) htimeout
      exact Restated.noTimeoutVote_l85c facts S Hs Xb hf hHs hHsXb hPrun hnj heW hone u a'.round a' t' rfl
        hemit' (hHs _ _ hlt.le hu) e'' hpair'
    · obtain ⟨t', a', hlt, hemit', hpair'⟩ :=
        Restated.recordTarget_emits_before_l85c facts S Hs Xb hf u ((Restated.Vocabulary.Execution.Setup.a M S q)) hrec
      exact hne ((hone u t' a' rec false hemit' (hHs _ _ hlt.le hu) hpair').trans heW.symm)
    · rw [hnj] at hnjP
      cases hnjP
  · right
    rw [hem, facts.vc.encodeHeight_empty] at hrow
    exact ⟨hrow, locked, hl, hne,
      Restated.seedActionOwnLock_height_le_preJustificationOn facts S Hs Xb hf u q n hn D hD hl⟩

/-- If `w`, in the set for `t`, emits along `W` at `t` an attestation whose height pair is
    `vote H e b`, then some run block `E₀` along `W` read through `Xb` has root `e` and height `H`
    and is its own entry. -/
theorem emittedVote_entry_l85c (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {w : V} {t : Int} {a : NamedAttestation V} {H : Height} {e : BlockId} {b : Bool}
    (hemit : (Restated.Vocabulary.Execution.Run.emits M S rho W w (Object.attest a) t)) (hw : w ∈ Hs t)
    (hpair : a.height_pair = .vote H e b) :
    ∃ E₀ : NamedBlock V, Restated.RunBlockOn M S rho W Xb E₀ ∧ E₀.root = e ∧
      (M.derive_named S.E S.cfg E₀).h = H ∧
      (M.derive_named S.E S.cfg E₀).T_h = E₀.erase := by
  have hW := hf.onePath
  obtain ⟨-, ht⟩ := Restated.Vocabulary.Proofs.Optimistic.emits_attest_shape facts S W hW hemit
  have hemitk : (Restated.Vocabulary.Execution.Run.emits M S rho W w (Object.attest a) ((Restated.Vocabulary.Execution.Setup.a M S a.round))) := by
    rw [← ht]; exact hemit
  have hwk : w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S a.round)) := by
    rw [← ht]; exact hw
  have hwmem := (p51% mem_stateBeforeTime_along₅₁) hf.sorted hW
    (Restated.Vocabulary.Execution.Setup.a M S a.round)
  obtain ⟨n, hn, D, hD⟩ := (p51% actionAttestation_nonempty₅₁) facts S
    (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) w) a.round
    (S.node w)
  have haeq : a = D.2.2 :=
    ((Restated.action_run_emissionOn facts S rho Hs Xb hf w a.round a).mp hemitk).2.2
      n hn D hD
  have hpairD : D.2.2.height_pair = .vote H e b := by rw [← haeq]; exact hpair
  obtain ⟨o, ho⟩ := (p51% actionFGSource_nonempty₅₁) facts S n
  cases o with
  | none =>
    rw [actionRow_empty_of_none₈₅c facts S w n ho D hD] at hpairD
    cases hpairD
  | some Q =>
    have hrow := Restated.actionRow_eq_encode_l85c facts S rho w a.round _ hwmem n hn ho D hD
    have hmem : n ∈ Restated.Vocabulary.Proofs.HealingSurface.actionReadAt M S rho w a.round :=
      ⟨W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)), hwmem, hn⟩
    obtain ⟨DQ, hDQ, -, hDQderive, -⟩ :=
      Restated.Vocabulary.Proofs.NamedActionSources.action_witness facts S rho w a.round n hmem Q ho
    have hDQrun : Restated.RunBlockOn M S rho W Xb DQ :=
      Restated.actionBody_runBlock_coverageOn facts S Hs Xb hf (hHsXb _ hwk) hn hDQ
    rw [hDQderive] at hrow
    obtain ⟨hQh, hQe⟩ := facts.vc.encodeHeight_vote_inv_l85c (hrow.symm.trans hpairD)
    obtain ⟨E₀, hE₀, hE₀e, hE₀h, -⟩ := Restated.entry_named_l85 facts S.E S.cfg DQ
    refine ⟨E₀, Restated.blockInRun_of_ancestorOn facts S rho W Xb hDQrun hE₀, ?_, hE₀h.trans hQh, ?_⟩
    · rw [← Proofs.NamedWire.erase_root E₀, hE₀e]
      exact hQe
    · rw [hE₀e]
      exact facts.cs.entry_eq_on_plateau S.E S.cfg hE₀ hE₀h

/-- Two run blocks along `W` at one height, each its own entry, with `E₁`'s erasure an ancestor of
    `E₂`'s, have the same root. -/
theorem entryRoot_eq_of_erasePreceq_l85c (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {E₁ E₂ : NamedBlock V} (h₁ : Restated.RunBlockOn M S rho W Xb E₁)
    (h₂ : Restated.RunBlockOn M S rho W Xb E₂)
    (hh : (M.derive_named S.E S.cfg E₁).h = (M.derive_named S.E S.cfg E₂).h)
    (hT₁ : (M.derive_named S.E S.cfg E₁).T_h = E₁.erase)
    (hT₂ : (M.derive_named S.E S.cfg E₂).T_h = E₂.erase)
    (h12 : Block.Preceq E₁.erase E₂.erase) : E₁.root = E₂.root := by
  obtain ⟨A, hA, hAe⟩ := Proofs.NamedAncestry.erased_ancestor_lift E₂ h12
  have hAE : A = E₁ :=
    hf.rootCollisionFree.root_injective E₂ E₁ h₂ h₁ A E₁ (Or.inl hA)
      (Or.inr (Proofs.NamedAncestry.named_self E₁)) (by
        rw [← Proofs.NamedWire.erase_root A, ← Proofs.NamedWire.erase_root E₁, hAe])
  subst hAE
  have hplat := facts.cs.entry_eq_on_plateau S.E S.cfg hA hh
  rw [hT₁, hT₂] at hplat
  rw [← Proofs.NamedWire.erase_root A, ← Proofs.NamedWire.erase_root E₂, hplat]

/-- Two run blocks along `W` at one height, each its own entry, whose erasures are both ancestors of
    `Z`'s erasure, have the same root. -/
theorem entryRoot_eq_of_underCommon_l85c (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {E₁ E₂ Z : NamedBlock V} (h₁ : Restated.RunBlockOn M S rho W Xb E₁)
    (h₂ : Restated.RunBlockOn M S rho W Xb E₂)
    (hh : (M.derive_named S.E S.cfg E₁).h = (M.derive_named S.E S.cfg E₂).h)
    (hT₁ : (M.derive_named S.E S.cfg E₁).T_h = E₁.erase)
    (hT₂ : (M.derive_named S.E S.cfg E₂).T_h = E₂.erase)
    (hZ₁ : Block.Preceq E₁.erase Z.erase) (hZ₂ : Block.Preceq E₂.erase Z.erase) :
    E₁.root = E₂.root := by
  obtain ⟨A₁, hA₁, hA₁e⟩ := Proofs.NamedAncestry.erased_ancestor_lift Z hZ₁
  obtain ⟨A₂, hA₂, hA₂e⟩ := Proofs.NamedAncestry.erased_ancestor_lift Z hZ₂
  rcases namedPreceq_total_l85 hA₁ hA₂ with h12 | h21
  · have hp := Proofs.NamedWire.erase_preceq h12
    rw [hA₁e, hA₂e] at hp
    exact Restated.entryRoot_eq_of_erasePreceq_l85c facts S Hs Xb hf h₁ h₂ hh hT₁ hT₂ hp
  · have hp := Proofs.NamedWire.erase_preceq h21
    rw [hA₁e, hA₂e] at hp
    exact (Restated.entryRoot_eq_of_erasePreceq_l85c facts S Hs Xb hf h₂ h₁ hh.symm hT₂ hT₁ hp).symm

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel.Proofs.HealingLemmas

/-- In the run of the execution `x` up to step `n`, if `T_0` is an anchor at the re-based deadline
    round, `x[n].time` is at most the switch round's action instant and `h(T_0) ≤ H`, then any two
    attestations emitted along the execution's path by validators not held at their instants, with
    votes at height `H`, name the same entry root. -/
theorem honestVotes_oneEntry_runAll_l85c (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v₀ : V) (n : Nat)
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
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    (hlen : tGAT + (Restated.healingLengthη M S gap + (Restated.constants M S).period) ≤ tE) (htd : Restated.TimeDiverges M x)
    {T_0 : NamedBlock V}
    (hA0 : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.rebasedDeadlineRoundW M S tGAT gap) T_0)
    (hnW : (x[n].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)))
    {H : Height} (htop : (M.derive_named S.E S.cfg T_0).h ≤ H) :
    ∀ (w₁ w₂ : V) (t₁ t₂ : Int) (a₁ a₂ : NamedAttestation V) (e₁ e₂ : BlockId) (b₁ b₂ : Bool),
      Restated.Vocabulary.Execution.NamedRun.emits M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v₀ n) w₁ (Object.attest a₁) t₁ →
      w₁ ∈ notHeldAt Sched t₁ → a₁.height_pair = .vote H e₁ b₁ →
      Restated.Vocabulary.Execution.NamedRun.emits M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v₀ n) w₂ (Object.attest a₂) t₂ →
      w₂ ∈ notHeldAt Sched t₂ → a₂.height_pair = .vote H e₂ b₂ → e₁ = e₂ := by
  have hlen' : tGAT + Restated.healingLengthη M S gap ≤ tE := Restated.healingLength_le_of_kit_l76 facts S hlen
  have hrW : Restated.rebasedDeadlineRoundW M S tGAT gap ≤ Restated.switchRound M S tE :=
    Restated.rebasedDeadlineRoundW_le_switchRound facts S tGAT tE gap (Restated.runAll M S Sched x v₀ 0) hgst hlen'
  have hrD : Restated.deadlineRoundW M S tGAT gap ≤ Restated.switchRound M S tE :=
    (Restated.deadlineRoundW_le_rebased facts S tGAT gap).trans hrW
  obtain ⟨-, hWE⟩ := Restated.window_in_phase_atRound facts S tGAT tE gap hgst hlen' hrD le_rfl
  have hn : (x[n].time : Int) ≤ tE := hnW.trans hWE
  have hf := Restated.admissibleFieldsOn_runAll_notHeld facts S Sched x v₀ n hsync hmono hawake hgst hcv hvalid
    hawm hthird hn
  obtain ⟨T_W, hAW⟩ := Restated.exists_anchorAtRound facts S Sched x hsync hmono hawake hgst hcv hvalid hawm
    hthird hcom hrec hlen' htd hrD le_rfl
  obtain ⟨n_W, hnWt⟩ := Restated.exists_tickStepAt facts x htd (Restated.action_pos facts S (Restated.switchRound M S tE))
  have hprev := Restated.basePreviousRoundSGCompatibleWithAnchor_atRound facts S Sched x tGAT tE gap hlen hgst
    hmono hvalid hsync hawm hcv hcom hthird hawake hrec
  have hclear := Restated.baseClearFGSource_atRound_of_premises facts (gap := gap) S Sched x tGAT tE hgst hmono
    hvalid hsync hawm hcv hcom hthird hawake
  have hun := Restated.honestVotes_onAnchorChain_since_roundW facts S Sched x hsync hmono hawake hgst hcv hvalid
    hawm hthird hcom hrec hlen' htd (Restated.deadlineRoundW_le_rebased facts S tGAT gap) hrW
    (fun r hr1 hr2 => hprev r hr1 hr2)
    (fun r hr1 hr2 => hclear r ((Restated.deadlineRoundW_le_rebased facts S tGAT gap).trans hr1) hr2)
    hA0 hAW hnWt
  have hzero : ∃ u : V, u ∉ Sched.adv 0 :=
    exists_notHeld_zero S Sched hthird (le_trans (Int.natCast_nonneg _) hn)
  have hunder : ∀ (w : V) (t : Int) (a : NamedAttestation V) (e : BlockId) (b : Bool),
      Restated.Vocabulary.Execution.NamedRun.emits M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v₀ n) w (Object.attest a) t →
      w ∈ notHeldAt Sched t → a.height_pair = .vote H e b →
      ∃ E₀ : NamedBlock V, Restated.RunBlockOn M (Setup.alwaysAwake S)
          ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } : Record.Run V)
          (Restated.runAllPath M S Sched x v₀ n) Finset.univ E₀ ∧ E₀.root = e ∧
        (M.derive_named S.E S.cfg E₀).h = H ∧
        (M.derive_named S.E S.cfg E₀).T_h = E₀.erase ∧
        Block.Preceq E₀.erase T_W.erase := by
    intro w t a e b hem hw hp
    obtain ⟨E₀, hE₀run, hE₀root, hE₀h, hE₀T⟩ := Restated.emittedVote_entry_l85c facts (Setup.alwaysAwake S)
      (notHeldAt Sched) Finset.univ hf (fun _ => Finset.subset_univ _) hem hw hp
    obtain ⟨k, hkn, hk, hsent⟩ := Restated.mem_sent_of_emits_runAll facts S Sched x v₀ hem
    obtain ⟨hk1, hk0⟩ := Restated.tickStepAt_time facts x hk
    obtain ⟨hW1, -⟩ := Restated.tickStepAt_time facts x hnWt
    have hkW : k + 1 ≤ n_W + 1 := by
      by_contra hlt
      have h1 : (x[n_W + 1].time : Int) ≤ x[k].time := Restated.time_mono_int facts S Sched x (by omega)
      have h2 : (x[k + 1].time : Int) ≤ x[n].time := Restated.time_mono_int facts S Sched x (by omega)
      omega
    have hval : a.val_index = w :=
      (Restated.Vocabulary.Proofs.Optimistic.emits_attest_shape facts _ _ hf.onePath hem).1
    have hhon : Restated.HonestThrough M Sched x (k + 1) w := by
      intro t' ht' hadv
      exact (mem_notHeldAt.1 hw) (hmono t' t (by rw [← hk1]; exact ht') hadv)
    have hlog := Restated.blockInLog_of_blockInRunOn_univ facts S Sched x v₀ _ n hmono hzero hE₀run
    exact ⟨E₀, hE₀run, hE₀root, hE₀h, hE₀T,
      hun w (k + 1) a H e b hkW hhon hval hsent hp htop E₀ hlog hE₀root⟩
  intro w₁ w₂ t₁ t₂ a₁ a₂ e₁ e₂ b₁ b₂ hem₁ hw₁ hp₁ hem₂ hw₂ hp₂
  obtain ⟨E₁, hE₁run, hE₁root, hE₁h, hE₁T, hE₁W⟩ := hunder w₁ t₁ a₁ e₁ b₁ hem₁ hw₁ hp₁
  obtain ⟨E₂, hE₂run, hE₂root, hE₂h, hE₂T, hE₂W⟩ := hunder w₂ t₂ a₂ e₂ b₂ hem₂ hw₂ hp₂
  rw [← hE₁root, ← hE₂root]
  exact Restated.entryRoot_eq_of_underCommon_l85c facts (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ hf
    hE₁run hE₂run (hE₁h.trans hE₂h.symm) hE₁T hE₂T hE₁W hE₂W

/-- In the run of the execution `x` up to step `n`, with `T_0` an anchor at the re-based deadline
    round and `x[n].time` at most the switch round's action instant: for a round `q` with
    `tGAT + 1 ≤ S.a q` within the horizon, a run block `P` with `h(T_0) ≤ h(P)`, and `u` not held at
    `S.a q` that passes the grade-2 awake test of round `q`, every round-`q` attestation of `u` at
    an action node state whose FG source can return `P`'s erasure is either `vote h(P) T_h(P) b`,
    with `b = false` when `nj(P) = false`, or empty, with `u`'s own lock at `h(P)` naming a block
    other than `T_h(P)` and `h(P)` at most `u`'s justified height strictly before `S.a q`. -/
theorem honestRow_atSourceHeight_runAll_l85c (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v₀ : V) (n : Nat)
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
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    (hlen : tGAT + (Restated.healingLengthη M S gap + (Restated.constants M S).period) ≤ tE) (htd : Restated.TimeDiverges M x)
    {T_0 : NamedBlock V}
    (hA0 : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.rebasedDeadlineRoundW M S tGAT gap) T_0)
    (hnW : (x[n].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)))
    {q : Round}
    (hhor : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) q) ≤
      ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } :
        Record.Run V).horizon)
    (hgat : tGAT + 1 ≤ (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) q))
    {P : NamedBlock V}
    (hPrun : Restated.RunBlockOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v₀ n) Finset.univ P)
    (htop : (M.derive_named S.E S.cfg T_0).h ≤ (M.derive_named S.E S.cfg P).h)
    {u : V} (hu : u ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) q)))
    -- `u`'s node state before each of its ticks at `S.a q` passes the grade-2 awake test of round
    -- `q`.
    (hrun : ∀ j : Nat,
      ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } :
        Record.Run V).events[j]? =
        some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) q)) →
      M.awake_for_grade2 (Setup.alwaysAwake S) u (Restated.runAllPath M S Sched x v₀ n j u) q) :
    ∀ nu ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
      (Restated.runAllPath M S Sched x v₀ n
        (strictEventIndex
          ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } : Record.Run V)
          (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) q)) u) q,
    Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M (Setup.alwaysAwake S) nu ⇢ some P.erase →
    ∀ D, M.duties_attest_with (M.gradeContract nu.cache) S.E S.hc ((Setup.alwaysAwake S).node u)
      nu.st nu.record ⇢ D →
    ((D.2.2.height_pair =
          .vote (M.derive_named S.E S.cfg P).h
            (M.derive_named S.E S.cfg P).T_h.root false ∨
        D.2.2.height_pair =
          .vote (M.derive_named S.E S.cfg P).h
            (M.derive_named S.E S.cfg P).T_h.root true) ∧
      ((M.derive_named S.E S.cfg P).nj = false →
        D.2.2.height_pair =
          .vote (M.derive_named S.E S.cfg P).h
            (M.derive_named S.E S.cfg P).T_h.root false)) ∨
    (D.2.2.height_pair = .empty ∧
      ∃ locked : BlockId,
        M.own_lock
            (Restated.runAllPath M S Sched x v₀ n
              (strictEventIndex
                ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } : Record.Run V)
                (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) q)) u).record.legacy
            (M.derive_named S.E S.cfg P).h
            D.2.2.finality_pair = some locked ∧
        locked ≠ (M.derive_named S.E S.cfg P).T_h.root ∧
        (M.derive_named S.E S.cfg P).h ≤
          (Restated.runAllPath M S Sched x v₀ n
            (strictEventIndex
              ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } : Record.Run V)
              (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) q)) u).st.core.h_j) := by
  have hlen' : tGAT + Restated.healingLengthη M S gap ≤ tE := Restated.healingLength_le_of_kit_l76 facts S hlen
  have hrW : Restated.rebasedDeadlineRoundW M S tGAT gap ≤ Restated.switchRound M S tE :=
    Restated.rebasedDeadlineRoundW_le_switchRound facts S tGAT tE gap (Restated.runAll M S Sched x v₀ 0) hgst hlen'
  have hrD : Restated.deadlineRoundW M S tGAT gap ≤ Restated.switchRound M S tE :=
    (Restated.deadlineRoundW_le_rebased facts S tGAT gap).trans hrW
  obtain ⟨-, hWE⟩ := Restated.window_in_phase_atRound facts S tGAT tE gap hgst hlen' hrD le_rfl
  have hn : (x[n].time : Int) ≤ tE := hnW.trans hWE
  have hf := Restated.admissibleFieldsOn_runAll_notHeld facts S Sched x v₀ n hsync hmono hawake hgst hcv hvalid
    hawm hthird hn
  have hagree := Restated.honestVotes_oneEntry_runAll_l85c facts S Sched x v₀ n hsync hmono hawake hgst hcv
    hvalid hawm hthird hcom hrec hlen htd hA0 hnW htop
  exact Restated.honestRow_atSource_engine_l85c facts (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ hf
    (fun _ _ h => notHeldAt_anti hmono h) (fun _ => Finset.subset_univ _) hPrun hagree hu hhor
    hgat hrun

/-- In the run of the execution `x` up to step `n`, along its path `W`: let `C` be a run block at
    height `H` with entry root `T`, an ancestor of the parent of a slot-`s` proposal `B` at height
    `H`, with `tGAT + 1 ≤ S.a r`, `S.a r + Δ ≤ proposal_time s ≤ x[n].time`, the proposer not held
    at `S.a r + Δ`, round `r` in the row window of the proposer's read, and `v` not held at
    `proposal_time s` and passing the grade-2 awake test of round `r`. Then every round-`r`
    attestation of `v` at an action node state whose FG source can return `C`'s erasure that carries
    `(H, T)` as a vote or a timeout is on the named chain of `B`'s parent with `v` in its progress
    set (and in its target participation for a target vote), or among `B`'s own attestations. -/
theorem honestRow_coveredAtProposal_runAll_l85c (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v₀ : V) (n : Nat)
    {tGAT tAwakeEnd : Int}
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tAwakeEnd →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hn : (x[n].time : Int) ≤ tAwakeEnd)
    {r : Round} {C : NamedBlock V} {H : Height} {T : BlockId}
    (hCrun : Restated.RunBlockOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v₀ n) Finset.univ C)
    (hCheight : (M.derive_named S.E S.cfg C).h = H)
    (hCtarget : (M.derive_named S.E S.cfg C).T_h.root = T)
    {s : Slot} {B : NamedBlock V}
    (hCP : NamedBlock.Preceq C B.parent)
    (hPheight : (M.derive_named S.E S.cfg B.parent).h = H)
    (hprop : S.E.proposer s ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) r) + S.E.Δ))
    (hhor : M.proposal_time S.E s ≤
      ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } :
        Record.Run V).horizon)
    (hpost : tGAT + 1 ≤ (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) r))
    (hdelay : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) r) + S.E.Δ ≤ M.proposal_time S.E s)
    {v : V} (hv : v ∈ notHeldAt Sched (M.proposal_time S.E s))
    -- `v`'s node state before each of its ticks at `S.a r` passes the grade-2 awake test of round
    -- `r`.
    (hrun : ∀ j : Nat,
      ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } :
        Record.Run V).events[j]? =
        some (Record.Event.tick v (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) r)) →
      M.awake_for_grade2 (Setup.alwaysAwake S) v (Restated.runAllPath M S Sched x v₀ n j v) r) :
    let R : Record.Run V :=
      { Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) }
    let W := Restated.runAllPath M S Sched x v₀ n
    let wb := W (strictEventIndex R (M.proposal_time S.E s)) (S.E.proposer s)
    ∀ cb : M.Cache,
      M.onPhaseTick S.E S.hc wb.st.core.toHealing (M.proposal_time S.E s) wb.cache ⇢ cb →
      let pnb := M.mkNode (M.ns_setClock S.E wb.st (M.proposal_time S.E s)) wb.record cb
      M.proposal_with (M.gradeContract cb) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer s)) pnb.st ⇢ some B →
      M.inWindow S.hc pnb.st.core r = true →
    ∀ nv ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
      (W (strictEventIndex R (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) r)) v) r,
    Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M (Setup.alwaysAwake S) nv ⇢ some C.erase →
    ∀ D, M.duties_attest_with (M.gradeContract nv.cache) S.E S.hc ((Setup.alwaysAwake S).node v)
      nv.st nv.record ⇢ D →
    (D.2.2.height_pair = .vote H T false ∨ D.2.2.height_pair = .vote H T true) →
    ((D.2.2 ∈ Protocol.named_chain_attestations B.parent ∧
        v ∈ (M.derive_named S.E S.cfg B.parent).progress ∧
        (D.2.2.height_pair = .vote H T false →
          v ∈ (M.derive_named S.E S.cfg B.parent).target_participation)) ∨
      D.2.2 ∈ B.attestations) := by
  intro R W wb cb hcb pnb hB hinWindow nv hnv hsrc D hD hpair
  have hf := Restated.admissibleFieldsOn_runAll_notHeld facts S Sched x v₀ n hsync hmono hawake hgst hcv hvalid
    hawm hthird hn
  obtain ⟨hCpre, -⟩ := Restated.sourceBody_of_actionFGSource_l85c facts (Setup.alwaysAwake S) (notHeldAt Sched)
    Finset.univ hf (Finset.mem_univ v) hCrun hnv hsrc
  have hst : pnb.st = M.store_with_cache (M.ns_setClock S.E wb.st (M.proposal_time S.E s)) cb :=
    facts.nd.mkNode_st _ _ _
  rw [hst, facts.dt.proposal_with_store_with_cache] at hB
  rw [hst] at hinWindow
  simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at hinWindow
  exact Restated.actionAttestationAt_coveredAtProposal_ofBodyOn_l85c facts (Setup.alwaysAwake S)
    (notHeldAt Sched) Finset.univ hf (fun _ _ h => notHeldAt_anti hmono h) hCheight hCtarget
    cb hcb hB hCP hPheight hprop hhor hpost hdelay hv hCpre hinWindow hrun nv hnv D hD hpair

/-- `roundAt S tGAT + η_SG ≤ deadlineRoundW S tGAT gap`. -/
theorem rGST_le_deadlineRoundW_l85c (facts : Record.Facts M) (S : Setup V) (tGAT : Int) (gap : Nat) :
    Restated.roundAt M S tGAT + S.hc.η_SG ≤ Restated.deadlineRoundW M S tGAT gap := by
  unfold Restated.deadlineRoundW
  exact (Nat.le_succ _).trans (Nat.le_add_right _ _)

/-- In the run of the execution `x` up to step `n`, along its path `W`, for a round `c` at least two
    rounds after `deadlineRoundW S tGAT gap` within the horizon whose opening proposer is not held
    at the opening slot's confirmation instant: every proposal `P` of that proposer's read on `W` is
    a run block read through every validator, and `tGAT + 1 ≤ proposal_time (o_c) ≤ S.a c`. -/
theorem openingProposal_runBlock_runAll_l85c (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v₀ : V) (n : Nat)
    {tGAT tAwakeEnd : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tAwakeEnd →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hn : (x[n].time : Int) ≤ tAwakeEnd)
    {c : Round} (hc : Restated.deadlineRoundW M S tGAT gap + 2 ≤ c)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c) ≤
      ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } :
        Record.Run V).horizon)
    (hopening : S.E.proposer ((M.opening_slot S.hc c)) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c))))
    {P : NamedBlock V} :
    let R : Record.Run V :=
      { Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) }
    let W := Restated.runAllPath M S Sched x v₀ n
    let wp := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c)))
      (S.E.proposer (M.opening_slot S.hc c))
    ∀ cp : M.Cache,
      M.onPhaseTick S.E S.hc wp.st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc c)) wp.cache ⇢ cp →
      let pn := M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E (M.opening_slot S.hc c)))
        wp.record cp
      M.proposal_with (M.gradeContract cp) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc c))) pn.st ⇢ some P →
    Restated.RunBlockOn M (Setup.alwaysAwake S) R W Finset.univ P ∧
      tGAT + 1 ≤ M.proposal_time S.E ((M.opening_slot S.hc c)) ∧
      M.proposal_time S.E ((M.opening_slot S.hc c)) ≤ (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c) := by
  intro R W wp cp hcp pn hP
  have hf := Restated.admissibleFieldsOn_runAll_notHeld facts S Sched x v₀ n hsync hmono hawake hgst hcv hvalid
    hawm hthird hn
  obtain ⟨-, htwo, -, hpos, -⟩ := facts.gr.openingSlots_l86f S hc
  have hstartPos : 0 < (M.opening_slot S.hc c) := Nat.lt_of_lt_of_le hpos (Nat.sub_le _ _)
  have hpropA : M.proposal_time S.E ((M.opening_slot S.hc c)) ≤ (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c) := by
    have h : M.confirmation_time S.E ((M.opening_slot S.hc c)) = (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c) :=
      Restated.confirmation_time_opening_slot facts (Setup.alwaysAwake S) c
    have h' := facts.sch.proposal_time_le_confirmation_time S.E ((M.opening_slot S.hc c))
    linarith
  have hlo : tGAT + 1 ≤ M.proposal_time S.E ((M.opening_slot S.hc c)) := by
    have h1 := Restated.roundAt_lo_le_rGST_l71 facts S tGAT
    have h2 : (Restated.Vocabulary.Execution.Setup.a M S (Restated.roundAt M S tGAT + S.hc.η_SG)) ≤ (Restated.Vocabulary.Execution.Setup.a M S (Restated.deadlineRoundW M S tGAT gap)) :=
      (Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone (Restated.rGST_le_deadlineRoundW_l85c facts S tGAT gap)
    have h3 := Restated.Vocabulary.Protocol.action_lt_proposal_time_two_after facts S (Restated.deadlineRoundW M S tGAT gap)
    have h4 := facts.sch.proposal_time_mono S.E htwo
    linarith
  have hst : pn.st = M.store_with_cache
      (M.ns_setClock S.E wp.st (M.proposal_time S.E (M.opening_slot S.hc c))) cp :=
    facts.nd.mkNode_st _ _ _
  rw [hst, facts.dt.proposal_with_store_with_cache] at hP
  have hwinC : tGAT + 1 ≤ M.early S.E S.hc c .g1 - S.E.Δ := by
    have h1 := Restated.roundAt_lo_le_rGST_l71 facts S tGAT
    have hlt : Restated.roundAt M S tGAT + S.hc.η_SG < c :=
      lt_of_le_of_lt (Restated.rGST_le_deadlineRoundW_l85c facts S tGAT gap)
        (lt_of_lt_of_le (Nat.lt_succ_self _) ((Nat.le_succ _).trans hc))
    have h2 := facts.gr.action_delta_le_early S S.hc.R_ge_three hlt
    have h3 := facts.gr.q10_early_g2_le_early_g1 S c
    have h4 : tGAT + 1 ≤ M.a S.hc S.E.Δ (Restated.roundAt M S tGAT + S.hc.η_SG) := h1
    linarith
  exact ⟨Restated.proposedBlock_runBlockOn facts (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ hf
    (fun _ _ h => notHeldAt_anti hmono h) (fun _ => Finset.subset_univ _) hstartPos hopening
    (hpropA.trans hhor) hlo (fun j hj => hf.tick_outcome j _ _ hj)
    (fun j hj => hf.awake_g1 _ _ j _ (Or.inl rfl) hj
      (notHeldAt_anti hmono (facts.sch.proposal_time_le_confirmation_time S.E _) hopening)
      (by
        show tGAT + 1 ≤ M.early S.E S.hc (M.round_of S.hc (M.opening_slot S.hc c)) .g1 - S.E.Δ
        rw [facts.gr.round_of_opening_slot_eq]; exact hwinC)) cp hcp hP, hlo, hpropA⟩

/-- In the run of the execution `x` up to step `n`, along its path `W`, for a round `c` at least
    three rounds after the deadline round with honest openings at `c` and `c − 1` proposing `P` and
    `P'`, with `S.a c ≤ x[n].time ≤ S.a rW`, `h(T_0) ≤ h(P)` and `u` not held at `S.a c`: every
    round-`c` attestation of `u` is either `vote h(P) T_h(P) b`, with `b = false` when
    `nj(P) = false`, or empty, with `u`'s own lock at `h(P)` naming a block other than `T_h(P)` and
    `h(P)` at most `u`'s justified height strictly before `S.a c`. -/
theorem honestRow_atOpening_runAll_l85c (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v₀ : V) (n : Nat)
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
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    (hlen : tGAT + (Restated.healingLengthη M S gap + (Restated.constants M S).period) ≤ tE) (htd : Restated.TimeDiverges M x)
    {T_0 : NamedBlock V}
    (hA0 : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.rebasedDeadlineRoundW M S tGAT gap) T_0)
    (hnW : (x[n].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)))
    {c : Round} (hc3 : Restated.deadlineRoundW M S tGAT gap + 3 ≤ c)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c) ≤
      ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } :
        Record.Run V).horizon)
    (hopening : S.E.proposer ((M.opening_slot S.hc c)) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c))))
    (hopeningPrev : S.E.proposer ((M.opening_slot S.hc (c - 1))) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc (c - 1)))))
    {P P' : NamedBlock V}
    (htop : (M.derive_named S.E S.cfg T_0).h ≤ (M.derive_named S.E S.cfg P).h)
    {u : V} (hu : u ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c))) :
    let R : Record.Run V :=
      { Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) }
    let W := Restated.runAllPath M S Sched x v₀ n
    let wp := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c)))
      (S.E.proposer (M.opening_slot S.hc c))
    let wp' := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc (c - 1))))
      (S.E.proposer (M.opening_slot S.hc (c - 1)))
    ∀ cp : M.Cache,
      M.onPhaseTick S.E S.hc wp.st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc c)) wp.cache ⇢ cp →
      let pn := M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E (M.opening_slot S.hc c)))
        wp.record cp
      M.proposal_with (M.gradeContract cp) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc c))) pn.st ⇢ some P →
    ∀ cp' : M.Cache,
      M.onPhaseTick S.E S.hc wp'.st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc (c - 1))) wp'.cache ⇢ cp' →
      let pn' := M.mkNode
        (M.ns_setClock S.E wp'.st (M.proposal_time S.E (M.opening_slot S.hc (c - 1))))
        wp'.record cp'
      M.proposal_with (M.gradeContract cp') .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc (c - 1)))) pn'.st ⇢ some P' →
    ∀ nu ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
      (W (strictEventIndex R (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c)) u) c,
    ∀ D, M.duties_attest_with (M.gradeContract nu.cache) S.E S.hc ((Setup.alwaysAwake S).node u)
      nu.st nu.record ⇢ D →
    ((D.2.2.height_pair =
          .vote (M.derive_named S.E S.cfg P).h
            (M.derive_named S.E S.cfg P).T_h.root false ∨
        D.2.2.height_pair =
          .vote (M.derive_named S.E S.cfg P).h
            (M.derive_named S.E S.cfg P).T_h.root true) ∧
      ((M.derive_named S.E S.cfg P).nj = false →
        D.2.2.height_pair =
          .vote (M.derive_named S.E S.cfg P).h
            (M.derive_named S.E S.cfg P).T_h.root false)) ∨
    (D.2.2.height_pair = .empty ∧
      ∃ locked : BlockId,
        M.own_lock
            (W (strictEventIndex R (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c)) u).record.legacy
            (M.derive_named S.E S.cfg P).h
            D.2.2.finality_pair = some locked ∧
        locked ≠ (M.derive_named S.E S.cfg P).T_h.root ∧
        (M.derive_named S.E S.cfg P).h ≤
          (W (strictEventIndex R (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c)) u).st.core.h_j) := by
  intro R W wp wp' cp hcp pn hP cp' hcp' pn' hP' nu hnu D hD
  have hlen' : tGAT + Restated.healingLengthη M S gap ≤ tE := Restated.healingLength_le_of_kit_l76 facts S hlen
  have hrW : Restated.rebasedDeadlineRoundW M S tGAT gap ≤ Restated.switchRound M S tE :=
    Restated.rebasedDeadlineRoundW_le_switchRound facts S tGAT tE gap (Restated.runAll M S Sched x v₀ 0) hgst hlen'
  have hrD : Restated.deadlineRoundW M S tGAT gap ≤ Restated.switchRound M S tE :=
    (Restated.deadlineRoundW_le_rebased facts S tGAT gap).trans hrW
  obtain ⟨-, hWE⟩ := Restated.window_in_phase_atRound facts S tGAT tE gap hgst hlen' hrD le_rfl
  have hn : (x[n].time : Int) ≤ tE := hnW.trans hWE
  obtain ⟨hPrun, hlo, hpropA⟩ := Restated.openingProposal_runBlock_runAll_l85c facts S Sched x v₀ n hsync hmono
    hawake hgst hcv hvalid hawm hthird hn ((Nat.le_succ _).trans hc3) hhor hopening cp hcp hP
  obtain ⟨o, ho⟩ := (p51% actionFGSource_nonempty₅₁) facts (Setup.alwaysAwake S) nu
  have hsrc := Restated.fgSource_eq_openingProposal_runAll_notHeld facts S Sched x v₀ n hsync hmono hawake hgst
    hcv hvalid hawm hthird hn hcom hrec hc3 hhor hopening hopeningPrev cp hcp hP cp' hcp' hP'
    u hu nu hnu o ho
  rw [hsrc] at ho
  have hkc : tGAT + 1 ≤ M.early S.E S.hc c .g2 - S.E.Δ :=
    Restated.lo_le_early_g2_sub_delta_of_action_lt facts S (Restated.roundAt_lo_le_rGST_l71 facts S tGAT)
      (lt_of_le_of_lt (Restated.rGST_le_deadlineRoundW_l85c facts S tGAT gap)
        (lt_of_lt_of_le (Nat.lt_succ_self _) ((Nat.le_add_right _ 2).trans hc3)))
  exact Restated.honestRow_atSourceHeight_runAll_l85c facts S Sched x v₀ n hsync hmono hawake hgst hcv hvalid
    hawm hthird hcom hrec hlen htd hA0 hnW hhor (hlo.trans hpropA) hPrun htop hu
    (fun j hj => Restated.awake_g2_action_runAllPath facts S Sched x v₀ n hmono hawake hn c hkc u j hj)
    nu hnu ho D hD

/-- In the run of the execution `x` up to step `n`, along its path `W`, for a round `c` at least
    three rounds after the deadline round with honest openings at `c` and `c − 1` proposing `P` and
    `P'`: if `P` is an ancestor of the parent of a slot-`s` proposal `B` at height `h(P)`, the
    slot-`s` proposer is not held at `S.a c + Δ`, `S.a c + Δ ≤ proposal_time s ≤ x[n].time`, `v` is
    not held at `proposal_time s` and round `c` is in the row window of the proposer's read, then
    every round-`c` attestation of `v` that carries `(h(P), T_h(P))` as a vote or a timeout is on
    the named chain of `B`'s parent with `v` in its progress set (and in its target participation
    for a target vote), or among `B`'s own attestations. -/
theorem openingRow_coveredAtProposal_runAll_l85c (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v₀ : V) (n : Nat)
    {tGAT tAwakeEnd : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tAwakeEnd →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hn : (x[n].time : Int) ≤ tAwakeEnd)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tAwakeEnd gap)
    {c : Round} (hc3 : Restated.deadlineRoundW M S tGAT gap + 3 ≤ c)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c) ≤
      ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } :
        Record.Run V).horizon)
    (hopening : S.E.proposer ((M.opening_slot S.hc c)) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c))))
    (hopeningPrev : S.E.proposer ((M.opening_slot S.hc (c - 1))) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc (c - 1)))))
    {P P' : NamedBlock V}
    {s : Slot} {B : NamedBlock V}
    (hPB : NamedBlock.Preceq P B.parent)
    (hBheight : (M.derive_named S.E S.cfg B.parent).h =
      (M.derive_named S.E S.cfg P).h)
    (hprop : S.E.proposer s ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c) + S.E.Δ))
    (hphor : M.proposal_time S.E s ≤
      ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } :
        Record.Run V).horizon)
    (hdelay : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c) + S.E.Δ ≤ M.proposal_time S.E s)
    {v : V} (hv : v ∈ notHeldAt Sched (M.proposal_time S.E s)) :
    let R : Record.Run V :=
      { Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) }
    let W := Restated.runAllPath M S Sched x v₀ n
    let wp := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c)))
      (S.E.proposer (M.opening_slot S.hc c))
    let wp' := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc (c - 1))))
      (S.E.proposer (M.opening_slot S.hc (c - 1)))
    let wb := W (strictEventIndex R (M.proposal_time S.E s)) (S.E.proposer s)
    ∀ cp : M.Cache,
      M.onPhaseTick S.E S.hc wp.st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc c)) wp.cache ⇢ cp →
      let pn := M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E (M.opening_slot S.hc c)))
        wp.record cp
      M.proposal_with (M.gradeContract cp) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc c))) pn.st ⇢ some P →
    ∀ cp' : M.Cache,
      M.onPhaseTick S.E S.hc wp'.st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc (c - 1))) wp'.cache ⇢ cp' →
      let pn' := M.mkNode
        (M.ns_setClock S.E wp'.st (M.proposal_time S.E (M.opening_slot S.hc (c - 1))))
        wp'.record cp'
      M.proposal_with (M.gradeContract cp') .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc (c - 1)))) pn'.st ⇢ some P' →
    ∀ cb : M.Cache,
      M.onPhaseTick S.E S.hc wb.st.core.toHealing (M.proposal_time S.E s) wb.cache ⇢ cb →
      let pnb := M.mkNode (M.ns_setClock S.E wb.st (M.proposal_time S.E s)) wb.record cb
      M.proposal_with (M.gradeContract cb) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer s)) pnb.st ⇢ some B →
      M.inWindow S.hc pnb.st.core c = true →
    ∀ nv ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
      (W (strictEventIndex R (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c)) v) c,
    ∀ D, M.duties_attest_with (M.gradeContract nv.cache) S.E S.hc ((Setup.alwaysAwake S).node v)
      nv.st nv.record ⇢ D →
    (D.2.2.height_pair = .vote (M.derive_named S.E S.cfg P).h
          (M.derive_named S.E S.cfg P).T_h.root false ∨
      D.2.2.height_pair = .vote (M.derive_named S.E S.cfg P).h
          (M.derive_named S.E S.cfg P).T_h.root true) →
    ((D.2.2 ∈ Protocol.named_chain_attestations B.parent ∧
        v ∈ (M.derive_named S.E S.cfg B.parent).progress ∧
        (D.2.2.height_pair = .vote (M.derive_named S.E S.cfg P).h
            (M.derive_named S.E S.cfg P).T_h.root false →
          v ∈ (M.derive_named S.E S.cfg B.parent).target_participation)) ∨
      D.2.2 ∈ B.attestations) := by
  intro R W wp wp' wb cp hcp pn hP cp' hcp' pn' hP' cb hcb pnb hB hinWindow nv hnv D hD hpair
  obtain ⟨hPrun, hlo, hpropA⟩ := Restated.openingProposal_runBlock_runAll_l85c facts S Sched x v₀ n hsync hmono
    hawake hgst hcv hvalid hawm hthird hn ((Nat.le_succ _).trans hc3) hhor hopening cp hcp hP
  have hvA : v ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c)) :=
    notHeldAt_anti hmono ((le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans hdelay) hv
  obtain ⟨o, ho⟩ := (p51% actionFGSource_nonempty₅₁) facts (Setup.alwaysAwake S) nv
  have hsrc := Restated.fgSource_eq_openingProposal_runAll_notHeld facts S Sched x v₀ n hsync hmono hawake hgst
    hcv hvalid hawm hthird hn hcom hrec hc3 hhor hopening hopeningPrev cp hcp hP cp' hcp' hP'
    v hvA nv hnv o ho
  rw [hsrc] at ho
  have hkc : tGAT + 1 ≤ M.early S.E S.hc c .g2 - S.E.Δ :=
    Restated.lo_le_early_g2_sub_delta_of_action_lt facts S (Restated.roundAt_lo_le_rGST_l71 facts S tGAT)
      (lt_of_le_of_lt (Restated.rGST_le_deadlineRoundW_l85c facts S tGAT gap)
        (lt_of_lt_of_le (Nat.lt_succ_self _) ((Nat.le_add_right _ 2).trans hc3)))
  exact Restated.honestRow_coveredAtProposal_runAll_l85c facts S Sched x v₀ n hsync hmono hawake hgst hcv hvalid
    hawm hthird hn hPrun rfl rfl hPB hBheight hprop hphor (hlo.trans hpropA) hdelay hv
    (fun j hj => Restated.awake_g2_action_runAllPath facts S Sched x v₀ n hmono hawake hn c hkc v j hj)
    cb hcb hB hinWindow nv hnv ho D hD hpair

end

local macro "p58% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_58)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p71% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_71)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

end DecoupledConsensusModel.Sts.Restated
