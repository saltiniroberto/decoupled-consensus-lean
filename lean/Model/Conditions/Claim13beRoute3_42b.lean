import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.RunVocabulary
import Model.Conditions.Vocabulary_Internal_Definitions_Evidence
import Model.Conditions.Vocabulary_Internal_Definitions_NamedLifecycle
import Model.Conditions.Vocabulary_Internal_Definitions_NamedOutageEntry
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGradeQueries
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Internal_HealingSurface
import Model.Conditions.Vocabulary_Internal_Internal_GradeReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_ModelVocabulary_Healing_Schedule
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Adoption
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Agreement
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_FinalityFilterInterference
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Model.Conditions.Vocabulary_Protocol_Grades_GradeFormsBridge
import Model.Conditions.Vocabulary_Protocol_Grades_LegacyVocabulary
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Proofs.Vocabulary.Protocol.Grades.RelativeOneChain
import Model.Conditions.Vocabulary_Protocol_Handlers_Blocks
import Model.Conditions.Vocabulary_Protocol_Handlers_TickBridges
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_42b

/-!
# Run conditions over a model

Conditions on the run blocks, certificates, heights, votes, grades and SG blocks of a run, stated
over a model `M : Record.Model V` and read along a path `W` of the run or in the worlds before each
instant. The last section proves that each agrees, at the model `Record.Model.vocabulary`, with the
definition of the same name in `DecoupledConsensusModel.Sts`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

open scoped DC in
/-- `b` is an outcome of `pure a` exactly when `a = b`. -/
private theorem returns_pure_eq₄₂b {α : Type} (a b : α) : (pure a : DC.NDRE α) ⇢ b ↔ a = b := by
  rw [Record.returns_pure, eq_comm]

/-- Unfolds the given definitions and `Record.Model.vocabulary`, rewrites with the `record_vocabulary`
    lemmas, and closes the equivalence by definitional equality. -/
syntax "record_vocabulary_iff" "[" Lean.Parser.Tactic.simpArg,* "]" : tactic
macro_rules
  | `(tactic| record_vocabulary_iff [$ls,*]) =>
    `(tactic| first
      | ((try simp only [$ls,*, record_vocabulary, Record.stateBeforeOf_vocabulary, Membership.mem,
          Set.Mem, Singleton.singleton, Set.singleton, setOf, forall_eq]) <;> exact Iff.rfl)
      | ((try simp only [$ls,*, record_vocabulary, Record.stateBeforeOf_vocabulary, Membership.mem,
          Set.Mem, Singleton.singleton, Set.singleton, setOf, forall_eq]) <;>
        (try simp only [Record.Model.vocabulary, returns_pure_eq₄₂b, forall_eq, forall_eq',
          forall_apply_eq_imp_iff]) <;> exact Iff.rfl)
      | ((try simp only [$ls,*, record_vocabulary, record_ofVocabulary, Record.stateBeforeOf_vocabulary,
          List.filter_map, List.length_map, Function.comp_def, Membership.mem,
          Set.Mem, Singleton.singleton, Set.singleton, setOf, forall_eq]) <;> exact Iff.rfl)
      | ((try simp only [$ls,*, record_vocabulary, record_ofVocabulary, Record.stateBeforeOf_vocabulary,
          List.filter_map, List.length_map, Function.comp_def, Membership.mem,
          Set.Mem, Singleton.singleton, Set.singleton, setOf, forall_eq]) <;>
        (try simp only [Record.Model.vocabulary, returns_pure_eq₄₂b, forall_eq, forall_eq',
          forall_apply_eq_imp_iff]) <;> exact Iff.rfl))

/-- Closes a field by a hypothesis, read directly or through `Record.Run.ofVocabulary` at a tick or a
    delivery index. -/
syntax "record_vocabulary_close" : tactic
macro_rules
  | `(tactic| record_vocabulary_close) =>
    `(tactic| first
      | assumption
      | exact (Record.Event.map_ofVocabulary_getElem?_tick _ _ _ _).2 (by assumption)
      | exact (Record.Event.map_ofVocabulary_getElem?_tick _ _ _ _).1 (by assumption)
      | exact (Record.Event.map_ofVocabulary_getElem?_deliver _ _ _ _ _).2 (by assumption)
      | exact (Record.Event.map_ofVocabulary_getElem?_deliver _ _ _ _ _).1 (by assumption))

/-- Splits an equivalence of structures into its fields and closes each as `record_vocabulary_iff` or
    `record_vocabulary_close` does. -/
syntax "record_vocabulary_struct_iff" : tactic
macro_rules
  | `(tactic| record_vocabulary_struct_iff) =>
    `(tactic| first
      | (constructor <;> intro h <;> cases h <;> constructor <;>
          (try simp only [record_vocabulary, record_ofVocabulary, Record.stateBeforeOf_vocabulary,
            Membership.mem, Set.Mem, Singleton.singleton, Set.singleton, setOf, forall_eq] at *) <;>
          record_vocabulary_close)
      | (constructor <;> intro h <;> cases h <;> constructor <;>
          (try simp only [record_vocabulary, record_ofVocabulary, Record.stateBeforeOf_vocabulary,
            Membership.mem, Set.Mem, Singleton.singleton, Set.singleton, setOf, forall_eq] at *) <;>
          (try simp only [Record.Model.vocabulary, returns_pure_eq₄₂b, forall_eq, forall_eq',
            forall_apply_eq_imp_iff] at *) <;> record_vocabulary_close))

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- Roots are collision-free for the run blocks of `rho` read through `Xb` along the path `W`. -/
structure RootCollisionFreeOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N) (Xb : Finset V) : Prop where
  root_injective : ∀ B C : NamedBlock V,
    Restated.blockInRunOn M S rho W Xb B → Restated.blockInRunOn M S rho W Xb C →
    ∀ A D : NamedBlock V,
      (NamedBlock.Preceq A B ∨ NamedBlock.Preceq A C) →
      (NamedBlock.Preceq D B ∨ NamedBlock.Preceq D C) → A.root = D.root → A = D
  /-- No block the proposer of slot `s` holds just before its tick at `s`'s proposal instant has the
      root its node gives slot `s`. -/
  honest_roots_new : ∀ (s : Slot) (j : Nat),
    rho.events[j]? = some (Record.Event.tick (S.E.proposer s) (M.proposal_time S.E s)) →
    ∀ B ∈ (W j (S.E.proposer s)).st.bodies,
      B.root ≠ (S.node (S.E.proposer s)).new_root s

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- Some run block of `rho`, read through `Xb` along the path `W`, erases to `B`. -/
def RunBlockOfOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N) (Xb : Finset V) (B : Block V) : Prop :=
  ∃ D : NamedBlock V, D.erase = B ∧ Restated.RunBlockOn M S rho W Xb D

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- For every two run blocks of `ρ` read through `Xb` along the path `W`, the attestations of their
    chains do not carry slashable weight between them. -/
def SlashableBoundOn (M : Record.Model V) (S : Setup V) (ρ : Record.Run V) (W : Nat → V → M.N) (Xb : Finset V) : Prop :=
  ∀ B₁ B₂ : NamedBlock V, Restated.RunBlockOn M S ρ W Xb B₁ → Restated.RunBlockOn M S ρ W Xb B₂ →
    ¬M.HasSlashableWeightBetween S.E (M.chain_attestations B₁.erase) (M.chain_attestations B₂.erase)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- `a` is delivered in `ρ`, or it is on the chain of some run block of `ρ` read through `Xb` along
    the path `W`. -/
def RunAttestationOn (M : Record.Model V) (S : Setup V) (ρ : Record.Run V) (W : Nat → V → M.N) (Xb : Finset V) (a : NamedAttestation V) :
    Prop :=
  Object.attest a ∈ Restated.objects ρ ∨
    ∃ B : NamedBlock V, Restated.RunBlockOn M S ρ W Xb B ∧ a ∈ named_chain_attestations B

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- Some set `Q` of weight at least `q` has, for each member, an attestation in play (read through
    `Xb` along the path `W`) by that member voting `T` at height `h`. -/
def CertificateOn (M : Record.Model V) (S : Setup V) (ρ : Record.Run V) (W : Nat → V → M.N) (Xb : Finset V) (h : Height) (T : BlockId) :
    Prop :=
  ∃ Q : Finset V, S.E.q ≤ S.E.electorate.weightOf Q ∧
    ∀ v ∈ Q, ∃ a : NamedAttestation V, Restated.RunAttestationOn M S ρ W Xb a ∧
      a.val_index = v ∧ a.height_pair = NamedHeightPair.vote h T false

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- Some subset `Q` of `X` whose weight plus the weight outside `X` reaches `q` has, for each
    member, an attestation emitted along the path `W` with target `T` at height `h`. -/
def CompletableOn (M : Record.Model V) (S : Setup V) (ρ : Record.Run V) (W : Nat → V → M.N) (X : Finset V)
    (h : Height) (T : BlockId) : Prop :=
  ∃ Q ⊆ X,
    S.E.q ≤ S.E.electorate.weightOf Q + S.E.electorate.weightOf (Finset.univ \ X) ∧
      ∀ v ∈ Q, ∃ (a : NamedAttestation V) (t : Time),
        Restated.Vocabulary.Execution.Run.emits M S ρ W v (Object.attest a) t ∧ T ∈ targetsAt a.erase h

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- At each height at most one target is completable by `X` along the path `W`. -/
def PerHeightCompletabilityOn (M : Record.Model V) (S : Setup V) (ρ : Record.Run V) (W : Nat → V → M.N)
    (X : Finset V) : Prop :=
  ∀ (h : Height) (T T' : BlockId), Restated.CompletableOn M S ρ W X h T → Restated.CompletableOn M S ρ W X h T' → T = T'

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- No member of `X` emits, along the path `W`, two attestations with different targets at one
    height. -/
def HonestNoDoubleTargetOn (M : Record.Model V) (S : Setup V) (ρ : Record.Run V) (W : Nat → V → M.N)
    (X : Finset V) : Prop :=
  ∀ v ∈ X, ∀ (a a' : NamedAttestation V) (t t' : Time),
    Restated.Vocabulary.Execution.Run.emits M S ρ W v (Object.attest a) t → Restated.Vocabulary.Execution.Run.emits M S ρ W v (Object.attest a') t' →
      ∀ (h : Height) (T T' : BlockId), T ∈ targetsAt a.erase h → T' ∈ targetsAt a'.erase h →
        T = T'

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- The set of the maxima, over the members of `Hs t`, of the `h_max` of their stores in `w` (zero
    when `Hs t` is empty), for every world `w` that can hold after the events timed up to `t`. -/
noncomputable def honestHMaxAtOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V)
    (t : Time) : DC.NDR Height :=
  (fun w : V → M.N => (Hs t).sup fun v => (w v).st.core.h_max) ''
    Restated.Vocabulary.Execution.NamedRun.readAt M S rho t

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- The set of the maxima, over the members of `X`, of the `h_max` of their stores in `w`, for every
    world `w` that can hold after the first `n` events. -/
noncomputable def honestHMaxBeforeIndexOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (X : Finset V)
    (n : Nat) : DC.NDR Height :=
  (fun w : V → M.N => X.sup fun v => (w v).st.h_max) '' Record.stateBeforeOf M S rho n

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- The set of the largest finalized heights of any body held by a member of `X` in `w`, for every
    world `w` that can hold after the first `n` events. -/
noncomputable def recoveryPrefixFinalityHeightOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (X : Finset V)
    (n : Nat) : DC.NDR Height :=
  (fun w : V → M.N => X.sup fun v =>
    (w v).st.bodies.sup fun B => (M.derive_named S.E S.cfg B).h_F) '' Record.stateBeforeOf M S rho n

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- Every body held by a member of `X` in the world `W n` has finalized height at most `hF0`. -/
def HonestPrefixFinalityCapOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N)
    (X : Finset V) (n : Nat) (hF0 : Height) : Prop :=
  ∀ v ∈ X, ∀ B ∈ (W n v).st.bodies, (M.derive_named S.E S.cfg B).h_F ≤ hF0

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- Every body held by a member of `X` in the world `W n` has the `nj` bit where its height is
    `blocked`, and no justification at `blocked`. -/
def HonestPrefixNJUniverseOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N)
    (X : Finset V) (n : Nat) (blocked : Height) : Prop :=
  ∀ v ∈ X, ∀ B ∈ (W n v).st.bodies,
    ((M.derive_named S.E S.cfg B).h = blocked → (M.derive_named S.E S.cfg B).nj = true) ∧
      (M.derive_named S.E S.cfg B).h_j ≠ blocked

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- No member of `Hs t` whose tick at `t` is among the first `n` events emits there, in any list
    that tick can emit, an attestation with a height pair at `blocked`. -/
def NoLocalHeightPairBeforeOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V) (n : Nat)
    (blocked : Height) : Prop :=
  ∀ {i : Nat} {v : V} {t : Time} {a : NamedAttestation V},
    i < n → v ∈ Hs t → rho.events[i]? = some (Record.Event.tick v t) →
      ∀ l ∈ Restated.Vocabulary.Execution.NamedRun.emittedAt M S rho i v t,
        Object.attest a ∈ l → a.height_pair.erase.height? ≠ some blocked

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- `lag` is positive, and from round `r0` on, at every action instant whose `lag` rounds end within
    the horizon, the largest `h_max` over `Hs` in the world `Wi` gives at that instant is less than
    the one it gives `lag` rounds later. -/
def EventualHeightProgressFromOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V)
    (Wi : Time → V → M.N) (Hs : Int → Finset V) (r0 lag : Round) : Prop :=
  0 < lag ∧ ∀ r : Round, r0 ≤ r → (Restated.Vocabulary.Execution.Setup.a M S (r + lag)) ≤ rho.horizon →
    ((Hs (Restated.Vocabulary.Execution.Setup.a M S r)).sup fun u =>
        (Wi (Restated.Vocabulary.Execution.Setup.a M S r) u).st.core.h_max) <
      ((Hs (Restated.Vocabulary.Execution.Setup.a M S (r + lag))).sup fun u =>
        (Wi (Restated.Vocabulary.Execution.Setup.a M S (r + lag)) u).st.core.h_max)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- Every member of `Hs (vote_time s)` has, in the world `W i` for every index `i` up to the number
    of events before slot `s`'s vote instant, a finalized block that is an ancestor of `B`. -/
def ProposalFinalizedBelowAtDeliveriesOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → M.N) (Hs : Int → Finset V) (s : Slot) (B : NamedBlock V) : Prop :=
  ∀ v ∈ Hs (M.vote_time S.E s),
    ∀ i ≤ (List.filter (fun (e : Record.Event V) => decide (e.time < M.vote_time S.E s)) rho.events).length,
      (W i v).st.core.F ⪯ B.erase

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- `first` is positive, and in the world `W i` of every index `i < first` the maximum `h_max` over
    `X` is at most `H`. -/
structure HeightWindowAtOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N)
    (X : Finset V) (H : Height) (first : Nat) : Prop where
  positive : 0 < first
  before : ∀ i < first, (X.sup fun v => (W i v).st.h_max) ≤ H

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- `first` is positive, the maximum `h_max` over `X` in the world `W first` is `H + 1`, and in the
    world `W i` of every earlier index it is at most `H`. -/
structure FirstHeightProgressAtOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N)
    (X : Finset V) (H : Height) (first : Nat) : Prop where
  positive : 0 < first
  frontier : (X.sup fun v => (W first v).st.h_max) = H + 1
  before : ∀ i < first, (X.sup fun v => (W i v).st.h_max) ≤ H

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- Some member of `X` holds, in the world `W n`, a run block at height `blocked + 2` with an
    ancestor run block at height `blocked`, both held. -/
def PrefixHeightCrossingWitnessOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N)
    (X Xb : Finset V) (n : Nat) (blocked : Height) : Prop :=
  ∃ v ∈ X, ∃ (carrier : NamedBlock V) (anchor : NamedBlock V),
    carrier ∈ (W n v).st.bodies ∧
      anchor ∈ (W n v).st.bodies ∧
        Restated.RunBlockOn M S rho W Xb carrier ∧ Restated.RunBlockOn M S rho W Xb anchor ∧
          anchor.Preceq carrier ∧
            (M.derive_named S.E S.cfg anchor).h = blocked ∧
              (M.derive_named S.E S.cfg carrier).h = blocked + 2

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- The members of `Hs (S.a k)` that emitted in round `k` along the path `W`. -/
noncomputable def honestRoundVotersOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N)
    (Hs : Int → Finset V) (k : Round) : Finset V :=
  (Hs ((Restated.Vocabulary.Execution.Setup.a M S k))).filter
    (fun v => Restated.Vocabulary.Internal.NamedOutageEntry.emittedInRound M S rho W v k)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- The union, over the rounds `k` from `r − η_SG` to `r − 2`, of the round-`k` voters in
    `Hs (S.a k)` along the path `W`. -/
noncomputable def historicalHonestVotersOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N)
    (Hs : Int → Finset V) (r : Round) : Finset V :=
  ((Finset.range r).filter (fun k => r - S.hc.η_SG ≤ k ∧ k + 1 < r)).biUnion
    (fun k => Restated.honestRoundVotersOn M S rho W Hs k)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- The historical voters of `r` that did not vote in round `r − 1`, both along the path `W`. -/
noncomputable def staleHistoricalVotersOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N)
    (Hs : Int → Finset V) (r : Round) : Finset V :=
  Restated.historicalHonestVotersOn M S rho W Hs r \ Restated.honestRoundVotersOn M S rho W Hs (r - 1)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- The weight outside `X` together with the stale historical voters of `r` is less than the weight
    of the round-`(r − 1)` voters inside `X`, all voters along the path `W`. -/
def GradeFormingMajorityOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N)
    (Hs : Int → Finset V) (X : Finset V) (r : Round) : Prop :=
  S.E.electorate.weightOf (Finset.univ \ X ∪ Restated.staleHistoricalVotersOn M S rho W Hs r) <
    S.E.electorate.weightOf (Restated.honestRoundVotersOn M S rho W Hs (r - 1) ∩ X)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- For every member `w` of the set for the phase-`p` domain instant of round `r + 1` and every
    round-`r` voter `u` along the path `W` still in the set for the early phase-`p` cutoff of round
    `r + 1`: every round-`r` SG block `A` computed from `u`'s node state in `Wt (S.a r)` is in the
    tree of `w`'s store in `Wt (domain (r + 1) p)`, and every outcome of `u`'s interpreted inputs at
    that store holds an input for round `r` confirming `A`'s root. -/
def RelativeCarrierWindowAtOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N)
    (Wt : Time → V → M.N) (Hs : Int → Finset V) (r : Round) (p : Phase) : Prop :=
  ∀ w ∈ Hs (M.domain S.E S.hc (r + 1) p),
    ∀ u ∈ Restated.honestRoundVotersOn M S rho W Hs r, u ∈ Hs (M.early S.E S.hc (r + 1) p) →
      ∀ na ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (Wt (Restated.Vocabulary.Execution.Setup.a M S r) u) r,
      ∀ g : Option (Block V), M.grade2_block_with (M.gradeContract na.cache) S.E S.hc
          (M.toHealing na.st.core) (M.round_of S.hc (M.toHealing na.st.core).s) ⇢ g →
      ∀ A : Block V, M.get_sg_vote_with (M.gradeContract na.cache) S.E S.hc
          (M.toHealing na.st.core) (M.round_of S.hc (M.toHealing na.st.core).s) g ⇢ A →
      ∀ I, M.interpretedInputs
            (M.gradeView (M.toHealing (Wt (M.domain S.E S.hc (r + 1) p) w).st.core))
            (Wt (M.domain S.E S.hc (r + 1) p) w).st.core.F S.hc.η_SG (r + 1)
            (M.early S.E S.hc (r + 1) p) u ⇢ I →
      ∃ y ∈ I,
        y.round = r ∧ y.confirmed = some A.root ∧
          Block.find? (Wt (M.domain S.E S.hc (r + 1) p) w).st.core.T A.root = some A

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- Every member of slot `s`'s committee in `Hs (vote_time s)` emitted along the path `W`, at slot
    `s`'s vote instant, a vote whose head is a run block (read through `Xb`) the cone `tgt` admits. -/
def NamedHonestVotesConeOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N)
    (Hs : Int → Finset V) (Xb : Finset V)
    (s : Slot) (tgt : Block V → Prop) : Prop :=
  ∀ x ∈ Hs (M.vote_time S.E s), x ∈ S.E.committee s →
    ∃ X : NamedBlock V, tgt X.erase ∧ Restated.blockInRunOn M S rho W Xb X ∧
      Restated.Vocabulary.Execution.NamedRun.emits M S rho W x (NamedObject.gfVote { val_index := x, slot := s, head := X.erase.root })
        (M.vote_time S.E s)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- Every member of slot `s`'s committee in `Hs (vote_time s)` emitted along the path `W`, at slot
    `s`'s vote instant, the vote naming `B`. -/
def NamedHonestVotesNameOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N)
    (Hs : Int → Finset V) (s : Slot) (B : Block V) : Prop :=
  ∀ v ∈ Hs (M.vote_time S.E s), v ∈ S.E.committee s →
    Restated.Vocabulary.Execution.NamedRun.emits M S rho W v (NamedObject.gfVote { val_index := v, slot := s, head := B.root })
      (M.vote_time S.E s)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- Some member of slot `s`'s committee in `Hs (confirmation_time s)` emitted, along the path `W`,
    at slot `s`'s vote instant, the vote whose head is `head`, a run block read through `Xb`. -/
def NamedHonestHeadOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N)
    (Hs : Int → Finset V) (Xb : Finset V) (s : Slot) (head : NamedBlock V) : Prop :=
  ∃ x ∈ Hs (M.confirmation_time S.E s), x ∈ S.E.committee s ∧ Restated.RunBlockOn M S rho W Xb head ∧
    Restated.Vocabulary.Execution.Run.emits M S rho W x (Object.gfVote { val_index := x, slot := s, head := head.erase.root })
      (M.vote_time S.E s)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- Some member of slot `s`'s committee in `Hs (confirmation_time s)` voted, along the path `W`, at
    slot `s`'s vote instant, for `X`, the erasure of a run block read through `Xb`. -/
def HonestHeadOn (M : Record.Model V) (S : Setup V) (ρ : Record.Run V) (W : Nat → V → M.N) (Hs : Int → Finset V)
    (Xb : Finset V) (s : Slot) (X : Block V) : Prop :=
  ∃ x ∈ Hs (M.confirmation_time S.E s), x ∈ S.E.committee s ∧
    (∃ C : NamedBlock V, C.erase = X ∧ Restated.RunBlockOn M S ρ W Xb C) ∧
      Restated.Vocabulary.Execution.Run.emits M S ρ W x (Object.gfVote { val_index := x, slot := s, head := X.root })
        (M.vote_time S.E s)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- Some head picked along the path `W` from slot `s`'s committee in `Hs (confirmation_time s)` is a
    descendant of `C` at height at least `hM − 1`. -/
def ThinHonestHeadAtOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N)
    (Hs : Int → Finset V) (Xb : Finset V) (hM : Height) (s : Slot) (C : Block V) : Prop :=
  ∃ head : NamedBlock V, Restated.NamedHonestHeadOn M S rho W Hs Xb s head ∧ C ⪯ head.erase ∧
    hM - 1 ≤ (M.derive_named S.E S.cfg head).h

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- Every head picked along the path `W` from slot `s`'s committee in `Hs (confirmation_time s)` is
    found by its root in `T` and stamped in `tb` before slot `s`'s support cutoff. -/
def HeadsResolveInOn (M : Record.Model V) (S : Setup V) (ρ : Record.Run V) (W : Nat → V → M.N)
    (Hs : Int → Finset V) (Xb : Finset V)
    (s : Slot) (T : Finset (Block V)) (tb : TimestampMap (Block V)) : Prop :=
  ∀ X : Block V, Restated.HonestHeadOn M S ρ W Hs Xb s X →
    Block.find? T X.root = some X ∧ stampedBefore tb (M.support_cutoff S.E s) X = true

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- Every head picked along the path `W` from slot `s`'s committee in `Hs (confirmation_time s)` is
    genesis or admitted by `v` along `W` before `Gamma`. -/
def HonestHeadsAvailableBeforeOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N)
    (Hs : Int → Finset V) (Xb : Finset V) (s : Slot) (v : V) (Gamma : Time) : Prop :=
  ∀ X : Block V, Restated.HonestHeadOn M S rho W Hs Xb s X → X = Block.genesis ∨ Restated.Vocabulary.Protocol.AdmittedBefore M S rho W v X Gamma

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- Every member `v` of slot `s`'s committee in `Hs (vote_time s)` has, at every vote node state
    staged from its node state in the world `wd` (one for every outcome of the cache update), a vote
    store whose walk extends to the proposal `B`. -/
def VoteStoresExtendOn (M : Record.Model V) (S : Setup V) (ρ : Record.Run V) (Hs : Int → Finset V) (s : Slot)
    (wd : V → M.N) (B : NamedBlock V) : Prop :=
  ∀ v ∈ Hs (M.vote_time S.E s), v ∈ S.E.committee s →
    ∀ c : M.Cache, M.onPhaseTick S.E S.hc (wd v).st.core.toHealing (M.vote_time S.E s) (wd v).cache ⇢ c →
    ∃ (tree₀ : Finset (Block V)) (H : Block V),
      Restated.Vocabulary.Proofs.Optimistic.NamedVoteStoreExtends M S ρ v s
        (M.mkNode (M.ns_setClock S.E (wd v).st (M.vote_time S.E s)) (wd v).record c) tree₀ H B

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- Every member `v` of slot `s`'s committee in `Hs (vote_time s)` has, at every vote node state `n`
    staged from its node state in the world `wd` at slot `s`'s vote instant, slot `s` and a vote
    store extending to `B`, and every outcome of the Goldfish vote duty at `n` carries a vote that
    `v` emits along the path `W` at that instant. -/
def VoteTickExtendsOn (M : Record.Model V) (S : Setup V) (ρ : Record.Run V) (W : Nat → V → M.N)
    (Hs : Int → Finset V) (s : Slot) (wd : V → M.N) (B : NamedBlock V) : Prop :=
  ∀ v ∈ Hs (M.vote_time S.E s), v ∈ S.E.committee s →
    ∀ c : M.Cache,
      M.onPhaseTick S.E S.hc (wd v).st.core.toHealing (M.vote_time S.E s) (wd v).cache ⇢ c →
    ∀ D : M.NS × Option (GoldfishVote V),
      M.duties_goldfish_vote_with
        (M.gradeContract
          (M.mkNode (M.ns_setClock S.E (wd v).st (M.vote_time S.E s)) (wd v).record c).cache)
        S.E S.hc (S.node v)
        (M.mkNode (M.ns_setClock S.E (wd v).st (M.vote_time S.E s)) (wd v).record c).st ⇢ D →
    ∃ (tree₀ : Finset (Block V)) (H : Block V) (u : GoldfishVote V),
      (M.mkNode (M.ns_setClock S.E (wd v).st (M.vote_time S.E s)) (wd v).record c).st.core.s =
          s ∧
        Restated.Vocabulary.Proofs.Optimistic.NamedVoteStoreExtends M S ρ v s
          (M.mkNode (M.ns_setClock S.E (wd v).st (M.vote_time S.E s)) (wd v).record c)
          tree₀ H B ∧
          D.2 = some u ∧
            Restated.Vocabulary.Execution.NamedRun.emits M S ρ W v (NamedObject.gfVote u) (M.vote_time S.E s)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- For every member `v` of `Hs (S.a r)` and every round-`r` SG block `A` computed from `v`'s node
    state in the world `wd`, every committee member of slot `s` in the set for its vote instant
    votes, along the path `W`, for a descendant of `A`. -/
def NamedSGTargetConeCanonicalityOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N)
    (Hs : Int → Finset V) (Xb : Finset V) (r : Round) (s : Slot) (wd : V → M.N) : Prop :=
  ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)),
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (wd v) r,
    ∀ g : Option (Block V), M.grade2_block_with (M.gradeContract n.cache) S.E S.hc
        (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ g →
    ∀ A : Block V, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc
        (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s) g ⇢ A →
      Restated.NamedHonestVotesConeOn M S rho W Hs Xb s fun X => A ⪯ X

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- For every member `v` of `Hs (S.a r)` and every round-`r` SG block `A` computed from `v`'s node
    state in the world `wd`, every committee member of slot `s` in the set for its vote instant
    votes, along the path `W`, for a descendant of `A`. -/
def SGTargetConeCanonicalityOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N)
    (Hs : Int → Finset V) (Xb : Finset V) (r : Round) (s : Slot) (wd : V → M.N) : Prop :=
  ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)),
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (wd v) r,
    ∀ g : Option (Block V), M.grade2_block_with (M.gradeContract n.cache) S.E S.hc
        (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ g →
    ∀ A : Block V, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc
        (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s) g ⇢ A →
      Restated.NamedHonestVotesConeOn M S rho W Hs Xb s fun X => A ⪯ X

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- The SG target cone of slot `s` is canonical along the path `W`, with the round-`r` carriers
    computed from the world `wa`, and for every run block `B` at height at least `K` whose cone slot
    `s`'s committee votes into, every member of `Hs (vote_time (s + 1))` has, at every vote node
    state staged from its node state in the world `wd`, a finality root that is an ancestor of `B`. -/
structure SGTargetOpeningConeRootLockOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N)
    (Hs : Int → Finset V) (Xb : Finset V) (K : Height) (r : Round) (s : Slot) (wd : V → M.N)
    (wa : V → M.N) : Prop where
  canonical : Restated.SGTargetConeCanonicalityOn M S rho W Hs Xb r s wa
  coneRootLock : ∀ {B : NamedBlock V}, Restated.RunBlockOn M S rho W Xb B →
    K ≤ (M.derive_named S.E S.cfg B).h →
    (Restated.NamedHonestVotesConeOn M S rho W Hs Xb s fun X => B.erase ⪯ X) →
    ∀ v ∈ Hs (M.vote_time S.E (s + 1)),
      ∀ c : M.Cache,
        M.onPhaseTick S.E S.hc (wd v).st.core.toHealing (M.vote_time S.E (s + 1)) (wd v).cache ⇢ c →
        M.get_fg_root (M.toHealing (M.mkNode (M.ns_setClock S.E (wd v).st (M.vote_time S.E (s + 1)))
          (wd v).record c).st.core).toFG ⪯ B.erase

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- Every block that a member of `Hs (domain (r + 1) .g1)` grades 1 in round `r + 1`, at its store
    in `Wt (domain (r + 1) .g1)`, has every committee member of slot `s` vote along the path `W` for
    a descendant of it, and any two such blocks are compatible. -/
structure NamedG1ConcentrationOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N)
    (Wt : Time → V → M.N)
    (Hs : Int → Finset V) (Xb : Finset V) (r : Round) (s : Slot) : Prop where
  supported : ∀ {w : V} {B : Block V}, w ∈ Hs (M.domain S.E S.hc (r + 1) Phase.g1) →
    (∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
      (Wt (M.domain S.E S.hc (r + 1) Phase.g1) w).st (r + 1) Phase.g1 B ⇢ b → b = true) →
    Restated.NamedHonestVotesConeOn M S rho W Hs Xb s fun X => B ⪯ X
  compatible : ∀ {w₁ w₂ : V} {B₁ B₂ : Block V},
    w₁ ∈ Hs (M.domain S.E S.hc (r + 1) Phase.g1) → w₂ ∈ Hs (M.domain S.E S.hc (r + 1) Phase.g1) →
      (∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
        (Wt (M.domain S.E S.hc (r + 1) Phase.g1) w₁).st (r + 1) Phase.g1 B₁ ⇢ b → b = true) →
      (∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
        (Wt (M.domain S.E S.hc (r + 1) Phase.g1) w₂).st (r + 1) Phase.g1 B₂ ⇢ b → b = true) →
      B₁.compatible B₂ = true

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- Conditions on `w`'s confirmation node state `read` for slot `s + 1`: the source's slot-`s`
    confirmation votes reach `read`'s tree, its SG roots are compatible with `B`, its in-tree heads
    are run blocks along the path `W` read through `Xb`, and the votes of `w`'s Goldfish vote duty
    at `read` are emitted along `W` at slot `s + 1`'s vote instant. -/
structure NamedNextVoteAdoptionOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N)
    (Xb : Finset V) (source : M.S) (s : Slot) (B : Block V) (w : V) (read : M.N) : Prop where
  transport :
    ∀ votes : Finset (GoldfishVote V), Restated.Vocabulary.Protocol.confVotes M S.E source s ⇢ votes →
    ∀ L : Finset (GoldfishVote V),
      M.voter_view S.E (M.toHealing read.st.core).toFG.toSG.toGoldfishStore read.st.core.s ⇢ L →
    ∀ L' : Finset (GoldfishVote V),
      M.voter_support_view S.E (M.toHealing read.st.core).toFG.toSG.toGoldfishStore read.st.core.s ⇢ L' →
    Restated.Vocabulary.Protocol.AdoptionTransport M source.T read.st.core.T votes
      (Restated.Vocabulary.Protocol.confLate M S.E source s) L L' B
  support_subset :
    ∀ L : Finset (GoldfishVote V),
      M.voter_view S.E (M.toHealing read.st.core).toFG.toSG.toGoldfishStore read.st.core.s ⇢ L →
    ∀ L' : Finset (GoldfishVote V),
      M.voter_support_view S.E (M.toHealing read.st.core).toFG.toSG.toGoldfishStore read.st.core.s ⇢ L' →
    L' ⊆ L
  anchor :
    ∀ R : Block V, M.get_sg_root_with (M.gradeContract read.cache) S.E S.hc (M.toHealing read.st.core)
      ((M.round_of S.hc read.st.core.s)) ⇢ R →
    R.compatible B = true
  path :
    ∀ R : Block V, M.get_sg_root_with (M.gradeContract read.cache) S.E S.hc (M.toHealing read.st.core)
      ((M.round_of S.hc read.st.core.s)) ⇢ R →
    R ⪯ B →
      ∀ C : Block V, R ⪯ C → C ≠ R → C ⪯ B →
        ∀ T : Finset (Block V), M.voter_filtered_block_tree S.E read.st.core read.st.core.s ⇢ T →
          C ∈ T
  run :
    ∀ T : Finset (Block V), M.voter_filtered_block_tree S.E read.st.core read.st.core.s ⇢ T →
    ∀ L : Finset (GoldfishVote V),
      M.voter_view S.E (M.toHealing read.st.core).toFG.toSG.toGoldfishStore read.st.core.s ⇢ L →
    ∀ L' : Finset (GoldfishVote V),
      M.voter_support_view S.E (M.toHealing read.st.core).toFG.toSG.toGoldfishStore read.st.core.s ⇢ L' →
    ∀ H : Block V, M.get_head_in_tree_with_layer (M.gradeContract read.cache) S.E S.hc
        (M.toHealing read.st.core) T L L' (read.st.core.s - 1) ⇢ H →
    ∃ C : NamedBlock V, C.erase = H ∧ Restated.RunBlockOn M S rho W Xb C
  emit :
    ∀ u : GoldfishVote V,
    ∀ D : M.NS × Option (GoldfishVote V),
      M.duties_goldfish_vote_with (M.gradeContract read.cache) S.E S.hc (S.node w) read.st ⇢ D →
    D.2 = some u →
      Restated.Vocabulary.Execution.Run.emits M S rho W w (Object.gfVote u) (M.vote_time S.E (s + 1))

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- Every member `v` of `Hs (domain r .g2)` has `C` in the filtered tree of its node state in the
    world `wd`, and every outcome of its round-`r` grade-2 store grade for `C` there is `true`. -/
def NamedGradeFormsAtOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V) (r : Round)
    (C : Block V) (wd : V → M.N) : Prop :=
  ∀ v ∈ Hs (M.domain S.E S.hc r Phase.g2),
    C ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M (wd v) ∧
      ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc (wd v).st r Phase.g2 C ⇢ b →
        b = true

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- `P` is an ancestor of every block the SG vote selector can return at a round-`r` action node
    state staged from the node state, in the world `wd`, of a member of `Hs (S.a r)`. -/
def ActionCarriersCoverOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V) (r : Round)
    (P : Block V) (wd : V → M.N) : Prop :=
  ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)),
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (wd v) r,
    ∀ g : Option (Block V), M.grade2_block_with (M.gradeContract n.cache) S.E S.hc
        (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ g →
    ∀ A : Block V, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc
        (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s) g ⇢ A →
      P ⪯ A

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- For any two members `u` and `v` of `Hs (S.a r)`, every round-`r` action carrier of `u` is
    compatible with every round-`r` action carrier of `v`. -/
def HonestActionCarriersOneChainAtOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V)
    (r : Round) : Prop :=
  ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)), ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)),
    ∀ A ∈ Restated.Vocabulary.Proofs.HealingSurface.actionSGBlockAt M S rho u r,
    ∀ A' ∈ Restated.Vocabulary.Proofs.HealingSurface.actionSGBlockAt M S rho v r,
      A.compatible A' = true

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- Every block that the grade-2 selection names at a round-`r` action node state staged from the
    node state of a member of `Hs (S.a r)` in `Wt (S.a r)` is, for every member `w` of `Hs (S.a r)`,
    an ancestor of the finality root of `w`'s store in `Wt (S.a r)` or in its filtered tree there. -/
def SelectedG2SettledAtOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (Wt : Time → V → M.N)
    (Hs : Int → Finset V) (r : Round) : Prop :=
  ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)), ∀ Q : Block V,
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (Wt (Restated.Vocabulary.Execution.Setup.a M S r) u) r,
    Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ some Q →
    ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)),
      Restated.Vocabulary.Proofs.HealingSurface.FinalityFilterNoninterferenceAtRead M S rho w
        ((Restated.Vocabulary.Execution.Setup.a M S r)) (Wt (Restated.Vocabulary.Execution.Setup.a M S r)) Q

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- For every member `u` of `Hs (domain r .g1)` and every block `B`, if every outcome of `u`'s
    round-`r` grade-1 store grade for `B` in the world `Wt (domain r .g1)` is `true`, then for every
    member `w` of `Hs (S.a r)`, `B` is an ancestor of the finality root of `w`'s store in
    `Wt (S.a r)` or in its filtered tree there. -/
def NamedLiveG1SettledAtOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (Wt : Time → V → M.N)
    (Hs : Int → Finset V) (r : Round) : Prop :=
  ∀ u ∈ Hs (M.domain S.E S.hc r Phase.g1), ∀ B : Block V,
    (∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
        (Wt (M.domain S.E S.hc r Phase.g1) u).st r Phase.g1 B ⇢ b → b = true) →
    ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)),
      Restated.Vocabulary.Proofs.HealingSurface.FinalityFilterNoninterferenceAtRead M S rho w
        ((Restated.Vocabulary.Execution.Setup.a M S r)) (Wt (Restated.Vocabulary.Execution.Setup.a M S r)) B

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- Every block the SG vote selector can return at a round-`(r − 1)` action node state staged from
    the node state of a member of `Hs (S.a (r − 1))` in `Wt (S.a (r − 1))` is, for every member `w`
    of `Hs (S.a r)`, an ancestor of the finality root of `w`'s store in `Wt (S.a r)` or in its
    filtered tree there. -/
def PreviousActionCarriersQuietAtOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (Wt : Time → V → M.N)
    (Hs : Int → Finset V) (r : Round) : Prop :=
  ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (r - 1))), ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)),
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (Wt (Restated.Vocabulary.Execution.Setup.a M S (r - 1)) u) (r - 1),
    ∀ g : Option (Block V), M.grade2_block_with (M.gradeContract n.cache) S.E S.hc
        (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ g →
    ∀ A : Block V, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc
        (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s) g ⇢ A →
      Restated.Vocabulary.Proofs.HealingSurface.FinalityFilterNoninterferenceAtRead M S rho w
        ((Restated.Vocabulary.Execution.Setup.a M S r)) (Wt (Restated.Vocabulary.Execution.Setup.a M S r)) A

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- For every member `v` of `Hs (S.a r)` and every round-`r` action node state `n` staged from `v`'s
    node state in `Wt (S.a r)`: if `v` emits along the path `W`, at round `r`'s action instant, an
    attestation of its attestation duty at `n`, then every SG vote computed from the grade-2 block
    at `n` is compatible with `B`. -/
def HonestSGEmissionsCompatibleAtRoundOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N)
    (Wt : Time → V → M.N) (Hs : Int → Finset V) (r : Round) (B : Block V) : Prop :=
  ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)),
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (Wt (Restated.Vocabulary.Execution.Setup.a M S r) v) r,
    ∀ D : M.NS × M.NR × NamedAttestation V,
      M.duties_attest_with (M.gradeContract n.cache) S.E S.hc (S.node v) n.st n.record ⇢ D →
      Restated.Vocabulary.Execution.Run.emits M S rho W v
          (Object.attest D.2.2) ((Restated.Vocabulary.Execution.Setup.a M S r)) →
        (let gc := M.gradeContract n.cache
         let st := (M.toHealing n.st.core)
         let k := (M.round_of S.hc st.s)
         ∀ A2 : Option (Block V), M.grade2_block_with gc S.E S.hc st k ⇢ A2 →
         ∀ G : Block V, M.get_sg_vote_with gc S.E S.hc st k A2 ⇢ G →
           G.compatible B = true)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- For every member `v` of `X`, every attestation `v`'s attestation duty can return at a round-`r`
    action node state staged from `v`'s node state in the world `wa` is on the attestations of the
    chain of `B`'s parent with `v` counted there, or in `B`'s own attestations, and has the height
    pair `(H, T)` with either timeout bit. -/
def NamedTargetedHonestActionProposalCoverageAtOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V)
    (X : Finset V) (r : Round) (B : NamedBlock V) (H : Height) (T : BlockId) (wa : V → M.N) : Prop :=
  let sigma := M.derive_named S.E S.cfg B.parent
  ∀ v ∈ X, ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (wa v) r,
    ∀ D : M.NS × M.NR × NamedAttestation V,
      M.duties_attest_with (M.gradeContract n.cache) S.E S.hc (S.node v) n.st n.record ⇢ D →
    (D.2.2 ∈ named_chain_attestations B.parent ∧
          v ∈ sigma.progress ∧
            (D.2.2.height_pair = NamedHeightPair.vote H T false → v ∈ sigma.target_participation) ∨
        D.2.2 ∈ B.attestations) ∧
      (D.2.2.height_pair = NamedHeightPair.vote H T false ∨ D.2.2.height_pair = NamedHeightPair.vote H T true)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- A clean action read of `P` at round `r`, with every node state taken from the worlds `Wt`: after
    `t_GST`, with the cutoff within the horizon, `P` is active at every reader of round `r + 1`, and
    every reader has resolved, before `Γ_neg1 (r + 1)`, the round-`r` action vote of every author,
    whose head covers `P`. -/
structure CleanActionReadForOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V) (r : Round)
    (Wt : Time → V → M.N) (P : Block V) : Prop where
  post_gst : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S r)
  cutoff_in_horizon : Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (r + 1) ≤ rho.horizon
  active : ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))),
    P ∈ M.get_filtered_block_tree
      (M.toHealing (Wt (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) w).st.core).toFG
  active_domain : ∀ w ∈ Hs (M.domain S.E S.hc (r + 1) Phase.g2),
    P ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
      (Wt (M.domain S.E S.hc (r + 1) Phase.g2) w)
  resolved_support : ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))), ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ),
    let gv := M.gradeView (M.toHealing (Wt (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) w).st.core)
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (Wt (Restated.Vocabulary.Execution.Setup.a M S r) v) r,
    let gc := M.gradeContract n.cache
    let st := M.toHealing n.st.core
    let k := M.round_of S.hc st.s
    ∀ g, M.grade2_block_with gc S.E S.hc st k ⇢ g →
    ∀ B : Block V, M.get_sg_vote_with gc S.E S.hc st k g ⇢ B →
    let u : Protocol.SGVote V := ⟨v, r, some B.root⟩
    occurrenceBefore (sg_resolution_time gv.T gv.timestamp_block gv.timestamp_sg_vote u)
          (Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (r + 1)) = true ∧
      ∀ b : Bool, M.head_covers gv.T P u.confirmed ⇢ b → b = true

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- `C` is active in every G2 read of every member of `Hs (domain r .g2)`, every such reader counts
    every author in `X` as positive for `C`, and an author such a reader can count as opposing is
    outside `X`. -/
structure RelativeG2SupportOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V) (X : Finset V)
    (r : Round) (C : Block V) : Prop where
  active : ∀ v ∈ Hs (M.domain S.E S.hc r Phase.g2),
    ∀ n ∈ Restated.Vocabulary.Proofs.HealingSurface.relativeG2Read M S rho r v,
      C ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M n
  positive : ∀ w ∈ Hs (M.domain S.E S.hc r Phase.g2), ∀ v ∈ X,
    ∀ b ∈ Restated.Vocabulary.Proofs.HealingSurface.relativePositiveAt M S rho r w v C, b = true
  opposing_not_honest : ∀ w ∈ Hs (M.domain S.E S.hc r Phase.g2), ∀ v : V,
    ∀ b ∈ Restated.Vocabulary.Proofs.HealingSurface.relativeOpposingAt M S rho r w v C, b = true → v ∉ X

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- At every instant `read` from round `lo`'s action instant to round `hi`'s, every member of
    `Hs read` has, in its store in the world `Wt read`, a justified height `h_j` with `h_j + 2 ≤ hM`
    and a maximal height exactly `hM`. -/
def GateOffFrameAtOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (Wt : Time → V → M.N)
    (Hs : Int → Finset V) (hM : Height)
    (lo hi : Round) : Prop :=
  ∀ read : Time, (Restated.Vocabulary.Execution.Setup.a M S lo) ≤ read → read ≤ (Restated.Vocabulary.Execution.Setup.a M S hi) → ∀ w ∈ Hs read,
    (Wt read w).st.core.h_j + 2 ≤ hM ∧ (Wt read w).st.core.h_max = hM

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- At every instant `read` from round `lo`'s action instant to round `hi`'s, every member of
    `Hs read` has, in its store in the world `Wt read`, a justified height `h_j` with `h_j + 2 ≤ hM`
    and a maximal height exactly `hM`. -/
def NamedGateOffFrameAtOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (Wt : Time → V → M.N)
    (Hs : Int → Finset V) (hM : Height)
    (lo hi : Round) : Prop :=
  ∀ read : Time, (Restated.Vocabulary.Execution.Setup.a M S lo) ≤ read → read ≤ (Restated.Vocabulary.Execution.Setup.a M S hi) → ∀ w ∈ Hs read,
    (Wt read w).st.core.h_j + 2 ≤ hM ∧ (Wt read w).st.core.h_max = hM

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- At every instant `read` from round `lo`'s action instant to round `hi`'s, every member of
    `Hs read` has, in its store in the world `Wt read`, a justified height `h_j` with `h_j + 2 ≤ hM`
    and a maximal height exactly `hM`. -/
def SeedGateOffFrameAtOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (Wt : Time → V → M.N)
    (Hs : Int → Finset V) (hM : Height)
    (lo hi : Round) : Prop :=
  ∀ read : Time, (Restated.Vocabulary.Execution.Setup.a M S lo) ≤ read → read ≤ (Restated.Vocabulary.Execution.Setup.a M S hi) → ∀ w ∈ Hs read,
    (Wt read w).st.h_j + 2 ≤ hM ∧ (Wt read w).st.h_max = hM

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- Every member `w` of `Hs (vote_time d)` has, in its vote duty store of slot `d` computed from its
    store in the world `Wt (vote_time d)`, maximal height `hM`, a justified height at least two less
    than `hM`, and a finality root that is an ancestor or a descendant of `C`. -/
def VoteDutyFrameAtOn' (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (Wt : Time → V → M.N)
    (Hs : Int → Finset V) (hM : Height) (d : Slot) (C : Block V) : Prop :=
  ∀ w ∈ Hs (M.vote_time S.E d),
    let st := Restated.Vocabulary.Proofs.Optimistic.voteStore M S (Wt (M.vote_time S.E d) w).st.core d
    st.h_max = hM ∧ st.h_j + 2 ≤ hM ∧
      (M.get_fg_root (M.toHealing st).toFG ⪯ C ∨ C ⪯ M.get_fg_root (M.toHealing st).toFG)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- At every slot's vote duty from `lo` to `hi + 1` and every slot's confirmation from `lo` to `hi`,
    every member of the set for that instant has, in its store staged from its node state in the
    world `Wt` of that instant, maximal height `hM` and a justified height at least two less than
    `hM`. -/
structure GateOffSeedConeWindowAtOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V)
    (Wt : Time → V → M.N) (Hs : Int → Finset V)
    (hM : Height) (lo hi : Slot) : Prop where
  voteFrontier : ∀ d : Slot, lo ≤ d → d ≤ hi + 1 → ∀ w ∈ Hs (M.vote_time S.E d),
    (Restated.Vocabulary.Proofs.Optimistic.voteStore M S (Wt (M.vote_time S.E d) w).st.core d).h_max = hM
  voteGateOff : ∀ d : Slot, lo ≤ d → d ≤ hi + 1 → ∀ w ∈ Hs (M.vote_time S.E d),
    (Restated.Vocabulary.Proofs.Optimistic.voteStore M S (Wt (M.vote_time S.E d) w).st.core d).h_j + 2 ≤ hM
  confirmationFrontier : ∀ s : Slot, lo ≤ s → s ≤ hi → ∀ w ∈ Hs (M.confirmation_time S.E s),
    (Restated.Vocabulary.Proofs.Optimistic.tickStore M S (Wt (M.confirmation_time S.E s) w).st.core
      (M.confirmation_time S.E s)).h_max = hM
  confirmationGateOff : ∀ s : Slot, lo ≤ s → s ≤ hi → ∀ w ∈ Hs (M.confirmation_time S.E s),
    (Restated.Vocabulary.Proofs.Optimistic.tickStore M S (Wt (M.confirmation_time S.E s) w).st.core
      (M.confirmation_time S.E s)).h_j + 2 ≤ hM

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- Every member of `X`, in the world `W n` for every `n ≤ stop`, has a finalized block that is an
    ancestor of every run block (read through `Xb` along `W`) at height at least `blocked`
    descending from `Tprev`. -/
def FinalityFloorAtOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N) (X Xb : Finset V) (blocked : Height)
    (stop : Nat) (Tprev : Block V) : Prop :=
  ∀ v ∈ X, ∀ n ≤ stop, ∀ B : NamedBlock V, Restated.RunBlockOn M S rho W Xb B →
    blocked ≤ (M.derive_named S.E S.cfg B).h → Tprev ⪯ B.erase →
      (W n v).st.F ⪯ B.erase

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- Every member of `X`, in the world `W n` for every `n ≤ stop`, has a finalized block that is an
    ancestor of every run block (read through `Xb` along `W`) at height at least `blocked`
    descending from the named block `Tprev`. -/
def NamedFinalityFloorAtOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N) (X Xb : Finset V) (blocked : Height)
    (stop : Nat) (Tprev : NamedBlock V) : Prop :=
  ∀ v ∈ X, ∀ n ≤ stop, ∀ B : NamedBlock V, Restated.RunBlockOn M S rho W Xb B →
    blocked ≤ (M.derive_named S.E S.cfg B).h → Tprev.Preceq B →
      (W n v).st.core.F ⪯ B.erase

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- Conditions at height `blocked` for the members of `X` up to index `stop` of the path `W`: the
    finality floor `FinalityFloorAtOn`, `Tprev` at height at most `blocked`, their fgroot an
    ancestor of every height-`(blocked + 1)` descendant of `Tprev` they hold, and every
    height-`(blocked + 1)` FG source of their action node states in the worlds `Wt` a descendant of
    `Tprev`. -/
structure HeightRegimeFrameOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N)
    (Wt : Time → V → M.N) (X Xb : Finset V) (blocked : Height)
    (stop : Nat) (Tprev : Block V) (c0 : Round) : Prop where
  floor : Restated.FinalityFloorAtOn M S rho W X Xb blocked stop Tprev
  prevHeight : (Restated.Vocabulary.Internal.derived_state M S.E S.cfg Tprev).h ≤ blocked
  rootBelow : ∀ v ∈ X, ∀ n ≤ stop, ∀ Q ∈ (W n v).st.T,
    ((W n v).st.σ Q).h = blocked + 1 → Tprev ⪯ Q →
      M.get_fg_root (W n v).st.toHealing.toFG ⪯ Q
  sourceAbove : ∀ p ∈ X, ∀ r : Round, strictEventIndex rho ((Restated.Vocabulary.Execution.Setup.a M S r)) ≤ stop →
    (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon →
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (Wt (Restated.Vocabulary.Execution.Setup.a M S r) p) r, ∀ B : Block V,
      ∀ A2 : Option (Block V), Restated.Vocabulary.Protocol.grade2_block M S.E S.hc n.toHealing r ⇢ A2 →
      Restated.Vocabulary.Protocol.fg_source M S.E S.hc n.toHealing r A2 ⇢ some B →
        (Restated.Vocabulary.Internal.derived_state M S.E S.cfg B).h = blocked + 1 → Tprev ⪯ B
  namedSourceAbove : ∀ p ∈ X, ∀ r : Round, strictEventIndex rho ((Restated.Vocabulary.Execution.Setup.a M S r)) ≤ stop →
    (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon →
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (Wt (Restated.Vocabulary.Execution.Setup.a M S r) p) r, ∀ B ∈ n.st.bodies,
      Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ some B.erase →
        (M.derive_named S.E S.cfg B).h = blocked + 1 → Tprev ⪯ B.erase

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- Conditions at height `blocked` along the path `W` up to index `stop`: the finality floor
    `NamedFinalityFloorAtOn` for `X`, `Tprev` a run block at height at most `blocked`, the fgroot of
    each member of `X` an ancestor of every height-`(blocked + 1)` descendant of `Tprev` it holds,
    and every height-`(blocked + 1)` body named by the action FG source of a member of `Hs (S.a r)`
    in the worlds `Wt` a descendant of `Tprev`. -/
structure NamedHeightRegimeFrameOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N)
    (Wt : Time → V → M.N) (Hs : Int → Finset V)
    (X Xb : Finset V) (blocked : Height) (stop : Nat) (Tprev : NamedBlock V) (c0 : Round) :
    Prop where
  floor : Restated.NamedFinalityFloorAtOn M S rho W X Xb blocked stop Tprev
  prevRun : Restated.RunBlockOn M S rho W Xb Tprev
  prevHeight : (M.derive_named S.E S.cfg Tprev).h ≤ blocked
  rootBelow : ∀ v ∈ X, ∀ n ≤ stop, ∀ Q ∈ (W n v).st.bodies,
    (M.derive_named S.E S.cfg Q).h = blocked + 1 → Tprev.Preceq Q →
      M.get_fg_root (M.toHealing (W n v).st.core).toFG ⪯ Q.erase
  sourceAbove : ∀ (p : V) (r : Round), p ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)) → strictEventIndex rho ((Restated.Vocabulary.Execution.Setup.a M S r)) ≤ stop →
    (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon →
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (Wt (Restated.Vocabulary.Execution.Setup.a M S r) p) r, ∀ B ∈ n.st.bodies,
      Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ some B.erase →
        (M.derive_named S.E S.cfg B).h = blocked + 1 → Tprev.Preceq B

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- For every attestation `a` that a member of `Hs (S.a a.round)` emits along the path `W` before
    index `first`, and every run block `R` at height `blocked` that `a` targets and that the FG
    confirmation witness of an action node state staged from the attester's node state in
    `Wt (S.a a.round)` names: `R` is an ancestor of `T` whenever some member of `X` has `h_max`
    greater than `blocked` and fgroot `R` in its store in `Wt time`. -/
def NamedOldTargetRootBelowRunOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N)
    (Wt : Time → V → M.N)
    (Hs : Int → Finset V) (X Xb : Finset V) (first : Nat) (blocked : Height) (T : NamedBlock V) : Prop :=
  ∀ (a : NamedAttestation V) (ta : Time), a.val_index ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S a.round)) →
    Restated.Vocabulary.Execution.NamedRun.emits M S rho W a.val_index (Object.attest a) ta →
      strictEventIndex rho ((Restated.Vocabulary.Execution.Setup.a M S a.round)) < first →
        ∀ R : NamedBlock V, Restated.RunBlockOn M S rho W Xb R →
          (M.derive_named S.E S.cfg R).h = blocked →
            a.height_pair.erase = HeightPair.target blocked R.erase.root →
              ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
                  (Wt (Restated.Vocabulary.Execution.Setup.a M S a.round) a.val_index) a.round,
              Restated.Vocabulary.Proofs.HealingSurface.fgConfirmationWitness M S n ⇢ some R.erase →
                ∀ w ∈ X, ∀ time : Time,
                  blocked < (Wt time w).st.h_max →
                    M.get_fg_root (M.toHealing (Wt time w).st.core).toFG = R.erase →
                      R.Preceq T

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- The attestation `attestation`, emitted along the path `W` at event index `index` (between
    `start` and `stop`) by a member of `Hs actionTime` at its round's action instant, has an action
    FG source naming `selectedBlock` at height `blocked + 1` with height target `checkpoint`, and
    the opening slot's honest votes are in the cone of `NamedHonestVotesConeOn`. -/
structure PrefixFGSelectorConeAtOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N)
    (Wt : Time → V → M.N)
    (Hs : Int → Finset V) (Xb : Finset V) (start stop : Nat) (blocked : Height) (index : Nat)
    (attestation : NamedAttestation V) (actionTime : Time) (selectedBlock : NamedBlock V)
    (checkpoint : Block V) : Prop where
  startLeIndex : start ≤ index
  indexLtStop : index < stop
  signerHonest : attestation.val_index ∈ Hs actionTime
  exactTick : rho.events[index]? = some (Record.Event.tick attestation.val_index actionTime)
  tickOutput : ∀ out : M.N × List (NamedObject V),
    M.tick S attestation.val_index (W index attestation.val_index) actionTime ⇢ out →
      Object.attest attestation ∈ out.2
  emitted : Restated.Vocabulary.Execution.NamedRun.emits M S rho W attestation.val_index (Object.attest attestation) actionTime
  actionTime_eq : actionTime = (Restated.Vocabulary.Execution.Setup.a M S attestation.round)
  exactAction : ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (Wt (Restated.Vocabulary.Execution.Setup.a M S attestation.round) attestation.val_index)
      attestation.round,
    ∀ D : M.NS × M.NR × NamedAttestation V,
      M.duties_attest_with (M.gradeContract n.cache) S.E S.hc (S.node attestation.val_index)
        n.st n.record ⇢ D → attestation = D.2.2
  exactFGSource : ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (Wt (Restated.Vocabulary.Execution.Setup.a M S attestation.round) attestation.val_index)
      attestation.round,
    ∀ o : Option (Block V), Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ o →
      o = some selectedBlock.erase
  sourceMem : ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (Wt (Restated.Vocabulary.Execution.Setup.a M S attestation.round) attestation.val_index)
      attestation.round,
    selectedBlock ∈ n.st.bodies
  sourceStoredHeight : ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (Wt (Restated.Vocabulary.Execution.Setup.a M S attestation.round) attestation.val_index)
      attestation.round,
    (n.st.core.σ selectedBlock.erase).h = blocked + 1
  sourceDerivedHeight : (M.derive_named S.E S.cfg selectedBlock).h = blocked + 1
  checkpointStored : ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (Wt (Restated.Vocabulary.Execution.Setup.a M S attestation.round) attestation.val_index)
      attestation.round,
    checkpoint = (n.st.core.σ selectedBlock.erase).T_h
  checkpointDerived : checkpoint = (M.derive_named S.E S.cfg selectedBlock).T_h
  targetOrTimeout : attestation.height_pair.erase = HeightPair.target (blocked + 1) checkpoint.root ∨
    attestation.height_pair.erase = HeightPair.timeout (blocked + 1)
  cone : (Restated.NamedHonestVotesConeOn M S rho W Hs Xb ((M.opening_slot S.hc attestation.round))
      fun X => selectedBlock.erase ⪯ X) ∨
    Restated.NamedHonestVotesConeOn M S rho W Hs Xb ((M.opening_slot S.hc attestation.round) + 1)
      fun X => selectedBlock.erase ⪯ X

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- The conditions that start the height regime at height `blocked` along the path `W`: the members
    of `X` first reach height `blocked + 1` at index `first`, their largest `h_max` at round `r0`'s
    action instant is less than `blocked`, `NamedHeightRegimeFrameOn` holds, and height-`blocked`
    targets confirmed by the FG confirmation witness stay ancestors of later height-`(blocked + 1)`
    run blocks. -/
structure NamedHeightRegimeBaseOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N)
    (Wt : Time → V → M.N)
    (Hs : Int → Finset V) (X Xb : Finset V) (r0 : Round) (blocked : Height) (first : Nat) (Tprev : NamedBlock V) :
    Prop where
  crossing : Restated.FirstHeightProgressAtOn M S rho W X (blocked + 1) first
  start : (X.sup fun v =>
      (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r0)) v).st.h_max) < blocked
  positive : 1 ≤ blocked
  frame : ∀ c : Round,
    (∀ (a : NamedAttestation V) (ta : Time), a.val_index ∈ Hs ta →
      Restated.Vocabulary.Execution.NamedRun.emits M S rho W a.val_index (Object.attest a) ta →
        a.height_pair.erase.height? = some (blocked + 1) → c ≤ a.round) →
      Restated.NamedHeightRegimeFrameOn M S rho W Wt Hs X Xb blocked (first - 1) Tprev c
  oldRoot : ∀ (a : NamedAttestation V) (ta : Time), a.val_index ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S a.round)) →
    Restated.Vocabulary.Execution.NamedRun.emits M S rho W a.val_index (Object.attest a) ta →
      strictEventIndex rho ((Restated.Vocabulary.Execution.Setup.a M S a.round)) < first →
        ∀ R : NamedBlock V, (M.derive_named S.E S.cfg R).h = blocked →
          a.height_pair.erase = HeightPair.target blocked R.erase.root →
            ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
                (Wt (Restated.Vocabulary.Execution.Setup.a M S a.round) a.val_index) a.round,
            Restated.Vocabulary.Proofs.HealingSurface.fgConfirmationWitness M S n ⇢ some R.erase →
              ∀ w ∈ X, ∀ time : Time,
                blocked < (Wt time w).st.h_max →
                  M.get_fg_root (M.toHealing (Wt time w).st.core).toFG = R.erase →
                    ∀ Y : NamedBlock V, Restated.RunBlockOn M S rho W Xb Y →
                      (M.derive_named S.E S.cfg Y).h = blocked + 1 → Tprev.Preceq Y → R.Preceq Y

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- The conditions of `NamedHeightRegimeBaseOn`, with the old root of the field `oldRoot` itself a
    run block read through `Xb`. -/
structure NamedHeightRegimeBaseRunOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N)
    (Wt : Time → V → M.N)
    (Hs : Int → Finset V) (X Xb : Finset V) (r0 : Round) (blocked : Height) (first : Nat) (Tprev : NamedBlock V) :
    Prop where
  crossing : Restated.FirstHeightProgressAtOn M S rho W X (blocked + 1) first
  start : (X.sup fun v =>
      (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r0)) v).st.h_max) < blocked
  positive : 1 ≤ blocked
  frame : ∀ c : Round,
    (∀ (a : NamedAttestation V) (ta : Time), a.val_index ∈ Hs ta →
      Restated.Vocabulary.Execution.NamedRun.emits M S rho W a.val_index (Object.attest a) ta →
        a.height_pair.erase.height? = some (blocked + 1) → c ≤ a.round) →
      Restated.NamedHeightRegimeFrameOn M S rho W Wt Hs X Xb blocked (first - 1) Tprev c
  oldRoot : ∀ (a : NamedAttestation V) (ta : Time), a.val_index ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S a.round)) →
    Restated.Vocabulary.Execution.NamedRun.emits M S rho W a.val_index (Object.attest a) ta →
      strictEventIndex rho ((Restated.Vocabulary.Execution.Setup.a M S a.round)) < first →
        ∀ R : NamedBlock V, Restated.RunBlockOn M S rho W Xb R → (M.derive_named S.E S.cfg R).h = blocked →
          a.height_pair.erase = HeightPair.target blocked R.erase.root →
            ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
                (Wt (Restated.Vocabulary.Execution.Setup.a M S a.round) a.val_index) a.round,
            Restated.Vocabulary.Proofs.HealingSurface.fgConfirmationWitness M S n ⇢ some R.erase →
              ∀ w ∈ X, ∀ time : Time,
                blocked < (Wt time w).st.h_max →
                  M.get_fg_root (M.toHealing (Wt time w).st.core).toFG = R.erase →
                    ∀ Y : NamedBlock V, Restated.RunBlockOn M S rho W Xb Y →
                      (M.derive_named S.E S.cfg Y).h = blocked + 1 → Tprev.Preceq Y → R.Preceq Y

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- The height regime at height `blocked` along the path `W`, around the attestation `a`: the seed
    `PrefixFGSelectorConeAtOn`, the window `HeightWindowAtOn`, the frame `NamedHeightRegimeFrameOn`,
    the condition `NamedOldTargetRootBelowRunOn` on `T`, a grade-1 block at every member of
    `Hs (domain a.round .g1)`, and `a.round` minimal among the rounds of emitted
    height-`(blocked + 1)` attestations. -/
structure NamedHeightRegimeRunOn(M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N)
    (Wt : Time → V → M.N) (Hs : Int → Finset V) (X Xb : Finset V) (r0 : Round) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
    (ta : Time) (Cfg T Tprev : NamedBlock V) (c0 : Round) : Prop where
  seed : Restated.PrefixFGSelectorConeAtOn M S rho W Wt Hs Xb (inclusiveEventIndex rho ((Restated.Vocabulary.Execution.Setup.a M S r0))) first blocked i a
    ta Cfg T.erase
  checkpointPreceq : T.Preceq Cfg
  checkpointErase : T.erase = (M.derive_named S.E S.cfg Cfg).T_h
  crossing : Restated.HeightWindowAtOn M S rho W X (blocked + 1) first
  frame : Restated.NamedHeightRegimeFrameOn M S rho W Wt Hs X Xb blocked (first - 1) Tprev c0
  c0le : c0 ≤ a.round
  ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho a.round
  postPrev : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S (a.round - 1))
  g1 : ∀ w ∈ Hs (M.domain S.E S.hc a.round Phase.g1), ∃ Q : Block V, ∀ b : Bool,
    Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
      (Wt (M.domain S.E S.hc a.round Phase.g1) w).st a.round Phase.g1 Q ⇢ b → b = true
  pred : Restated.NamedOldTargetRootBelowRunOn M S rho W Wt Hs X Xb first blocked T
  minimal : ∀ (b : NamedAttestation V) (tb : Time), b.val_index ∈ Hs tb →
    Restated.Vocabulary.Execution.NamedRun.emits M S rho W b.val_index (Object.attest b) tb →
      b.height_pair.erase.height? = some (blocked + 1) → a.round ≤ b.round

end

/-! ## Agreement at `Record.Model.vocabulary` -/

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- `Restated.RootCollisionFreeOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.RootCollisionFreeOn`. -/
@[record_vocabulary]
theorem RootCollisionFreeOn_vocabulary_eq (S : Setup V) (rho : NamedRun V) (Xb : Finset V) :
    _root_.DecoupledConsensusModel.Sts.RootCollisionFreeOn (V := V) S rho Xb ↔ Restated.RootCollisionFreeOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) (fun i => NamedRun.stateBefore S rho i) Xb :=
  by
  record_vocabulary_struct_iff

/-- `Restated.RunBlockOfOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.RunBlockOfOn`. -/
@[record_vocabulary]
theorem RunBlockOfOn_vocabulary_eq (S : Setup V) (rho : Run V) (Xb : Finset V) (B : Block V) :
    _root_.DecoupledConsensusModel.Sts.RunBlockOfOn (V := V) S rho Xb B ↔ Restated.RunBlockOfOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) (fun i => NamedRun.stateBefore S rho i) Xb B := by
  record_vocabulary_iff [Restated.RunBlockOfOn, _root_.DecoupledConsensusModel.Sts.RunBlockOfOn]

/-- `Restated.SlashableBoundOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.SlashableBoundOn`. -/
@[record_vocabulary]
theorem SlashableBoundOn_vocabulary_eq (S : Setup V) (ρ : Run V) (Xb : Finset V) :
    _root_.DecoupledConsensusModel.Sts.SlashableBoundOn (V := V) S ρ Xb ↔ Restated.SlashableBoundOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary ρ) (fun i => NamedRun.stateBefore S ρ i) Xb := by
  record_vocabulary_iff [Restated.SlashableBoundOn, _root_.DecoupledConsensusModel.Sts.SlashableBoundOn]

/-- `Restated.RunAttestationOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.RunAttestationOn`. -/
@[record_vocabulary]
theorem RunAttestationOn_vocabulary_eq (S : Setup V) (ρ : Run V) (Xb : Finset V) (a : NamedAttestation V) :
    _root_.DecoupledConsensusModel.Sts.RunAttestationOn (V := V) S ρ Xb a ↔ Restated.RunAttestationOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary ρ) (fun i => NamedRun.stateBefore S ρ i) Xb a := by
  record_vocabulary_iff [Restated.RunAttestationOn, _root_.DecoupledConsensusModel.Sts.RunAttestationOn]

/-- `Restated.CertificateOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.CertificateOn`. -/
@[record_vocabulary]
theorem CertificateOn_vocabulary_eq (S : Setup V) (ρ : Run V) (Xb : Finset V) (h : Height) (T : BlockId) :
    _root_.DecoupledConsensusModel.Sts.CertificateOn (V := V) S ρ Xb h T ↔ Restated.CertificateOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary ρ) (fun i => NamedRun.stateBefore S ρ i) Xb h T := by
  record_vocabulary_iff [Restated.CertificateOn, _root_.DecoupledConsensusModel.Sts.CertificateOn]

/-- `Restated.CompletableOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.CompletableOn`. -/
@[record_vocabulary]
theorem CompletableOn_vocabulary_eq (S : Setup V) (ρ : Run V) (X : Finset V) (h : Height) (T : BlockId) :
    _root_.DecoupledConsensusModel.Sts.CompletableOn (V := V) S ρ X h T ↔ Restated.CompletableOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary ρ)
        (fun i => NamedRun.stateBefore S ρ i) X h T := by
  record_vocabulary_iff [Restated.CompletableOn, _root_.DecoupledConsensusModel.Sts.CompletableOn]

/-- `Restated.PerHeightCompletabilityOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.PerHeightCompletabilityOn`. -/
@[record_vocabulary]
theorem PerHeightCompletabilityOn_vocabulary_eq (S : Setup V) (ρ : Run V) (X : Finset V) :
    _root_.DecoupledConsensusModel.Sts.PerHeightCompletabilityOn (V := V) S ρ X ↔ Restated.PerHeightCompletabilityOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary ρ)
        (fun i => NamedRun.stateBefore S ρ i) X := by
  record_vocabulary_iff [Restated.PerHeightCompletabilityOn,
    _root_.DecoupledConsensusModel.Sts.PerHeightCompletabilityOn]

/-- `Restated.HonestNoDoubleTargetOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.HonestNoDoubleTargetOn`. -/
@[record_vocabulary]
theorem HonestNoDoubleTargetOn_vocabulary_eq (S : Setup V) (ρ : Run V) (X : Finset V) :
    _root_.DecoupledConsensusModel.Sts.HonestNoDoubleTargetOn (V := V) S ρ X ↔ Restated.HonestNoDoubleTargetOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary ρ)
        (fun i => NamedRun.stateBefore S ρ i) X := by
  record_vocabulary_iff [Restated.HonestNoDoubleTargetOn,
    _root_.DecoupledConsensusModel.Sts.HonestNoDoubleTargetOn]

/-- `Restated.honestHMaxAtOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.honestHMaxAtOn`. -/
@[record_vocabulary]
theorem honestHMaxAtOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (t : Time) :
    Restated.honestHMaxAtOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) Hs t =
      {_root_.DecoupledConsensusModel.Sts.honestHMaxAtOn (V := V) S rho Hs t} := by
  rw [Restated.honestHMaxAtOn, Vocabulary.Execution.NamedRun.readAt_vocabulary_eq]
  exact Set.image_singleton

/-- `Restated.honestHMaxBeforeIndexOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.honestHMaxBeforeIndexOn`. -/
@[record_vocabulary]
theorem honestHMaxBeforeIndexOn_vocabulary_eq (S : Setup V) (rho : Run V) (X : Finset V) (n : Nat) :
    Restated.honestHMaxBeforeIndexOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) X n =
      {_root_.DecoupledConsensusModel.Sts.honestHMaxBeforeIndexOn (V := V) S rho X n} := by
  rw [Restated.honestHMaxBeforeIndexOn, Record.stateBeforeOf_vocabulary]
  exact Set.image_singleton

/-- `Restated.recoveryPrefixFinalityHeightOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.recoveryPrefixFinalityHeightOn`. -/
@[record_vocabulary]
theorem recoveryPrefixFinalityHeightOn_vocabulary_eq (S : Setup V) (rho : Run V) (X : Finset V) (n : Nat) :
    Restated.recoveryPrefixFinalityHeightOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) X n =
      {_root_.DecoupledConsensusModel.Sts.recoveryPrefixFinalityHeightOn (V := V) S rho X n} := by
  rw [Restated.recoveryPrefixFinalityHeightOn, Record.stateBeforeOf_vocabulary]
  exact Set.image_singleton

/-- `Restated.HonestPrefixFinalityCapOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.HonestPrefixFinalityCapOn`. -/
@[record_vocabulary]
theorem HonestPrefixFinalityCapOn_vocabulary_eq (S : Setup V) (rho : Run V) (X : Finset V) (n : Nat) (hF0 : Height) :
    _root_.DecoupledConsensusModel.Sts.HonestPrefixFinalityCapOn (V := V) S rho X n hF0 ↔
      Restated.HonestPrefixFinalityCapOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun i => NamedRun.stateBefore S rho i) X n hF0 := by
  record_vocabulary_iff [Restated.HonestPrefixFinalityCapOn,
    _root_.DecoupledConsensusModel.Sts.HonestPrefixFinalityCapOn]

/-- `Restated.HonestPrefixNJUniverseOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.HonestPrefixNJUniverseOn`. -/
@[record_vocabulary]
theorem HonestPrefixNJUniverseOn_vocabulary_eq (S : Setup V) (rho : Run V) (X : Finset V) (n : Nat) (blocked : Height) :
    _root_.DecoupledConsensusModel.Sts.HonestPrefixNJUniverseOn (V := V) S rho X n blocked ↔
      Restated.HonestPrefixNJUniverseOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun i => NamedRun.stateBefore S rho i) X n blocked := by
  record_vocabulary_iff [Restated.HonestPrefixNJUniverseOn,
    _root_.DecoupledConsensusModel.Sts.HonestPrefixNJUniverseOn]

/-- `Restated.NoLocalHeightPairBeforeOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.NoLocalHeightPairBeforeOn`. -/
@[record_vocabulary]
theorem NoLocalHeightPairBeforeOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (n : Nat) (blocked : Height) :
    _root_.DecoupledConsensusModel.Sts.NoLocalHeightPairBeforeOn (V := V) S rho Hs n blocked ↔ Restated.NoLocalHeightPairBeforeOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) Hs n blocked := by
  record_vocabulary_iff [Restated.NoLocalHeightPairBeforeOn,
    _root_.DecoupledConsensusModel.Sts.NoLocalHeightPairBeforeOn]

/-- `Restated.EventualHeightProgressFromOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.EventualHeightProgressFromOn`. -/
@[record_vocabulary]
theorem EventualHeightProgressFromOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (r0 lag : Round) :
    _root_.DecoupledConsensusModel.Sts.EventualHeightProgressFromOn (V := V) S rho Hs r0 lag ↔
      Restated.EventualHeightProgressFromOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun t => NamedRun.readAt S rho t) Hs r0 lag := by
  record_vocabulary_iff [Restated.EventualHeightProgressFromOn,
    _root_.DecoupledConsensusModel.Sts.EventualHeightProgressFromOn,
    _root_.DecoupledConsensusModel.Sts.honestHMaxAtOn]

/-- `Restated.ProposalFinalizedBelowAtDeliveriesOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.ProposalFinalizedBelowAtDeliveriesOn`. -/
@[record_vocabulary]
theorem ProposalFinalizedBelowAtDeliveriesOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (s : Slot) (B : NamedBlock V) :
    _root_.DecoupledConsensusModel.Sts.ProposalFinalizedBelowAtDeliveriesOn (V := V) S rho Hs s B ↔
      Restated.ProposalFinalizedBelowAtDeliveriesOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun i => NamedRun.stateBefore S rho i) Hs s B := by
  record_vocabulary_iff [Restated.ProposalFinalizedBelowAtDeliveriesOn,
    _root_.DecoupledConsensusModel.Sts.ProposalFinalizedBelowAtDeliveriesOn]

/-- `Restated.HeightWindowAtOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.HeightWindowAtOn`. -/
@[record_vocabulary]
theorem HeightWindowAtOn_vocabulary_eq (S : Setup V) (rho : Run V) (X : Finset V) (H : Height) (first : Nat) :
    _root_.DecoupledConsensusModel.Sts.HeightWindowAtOn (V := V) S rho X H first ↔
      Restated.HeightWindowAtOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun i => NamedRun.stateBefore S rho i) X H first :=
  ⟨fun h => ⟨h.positive, h.before⟩, fun h => ⟨h.positive, h.before⟩⟩

/-- `Restated.PrefixHeightCrossingWitnessOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.PrefixHeightCrossingWitnessOn`. -/
@[record_vocabulary]
theorem PrefixHeightCrossingWitnessOn_vocabulary_eq (S : Setup V) (rho : Run V) (X Xb : Finset V) (n : Nat)
    (blocked : Height) :
    _root_.DecoupledConsensusModel.Sts.PrefixHeightCrossingWitnessOn (V := V) S rho X Xb n blocked ↔
      Restated.PrefixHeightCrossingWitnessOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun i => NamedRun.stateBefore S rho i) X Xb n blocked := by
  record_vocabulary_iff [Restated.PrefixHeightCrossingWitnessOn,
    _root_.DecoupledConsensusModel.Sts.PrefixHeightCrossingWitnessOn]

/-- `Restated.FirstHeightProgressAtOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.FirstHeightProgressAtOn`. -/
@[record_vocabulary]
theorem FirstHeightProgressAtOn_vocabulary_eq (S : Setup V) (rho : Run V) (X : Finset V) (H : Height) (first : Nat) :
    _root_.DecoupledConsensusModel.Sts.FirstHeightProgressAtOn (V := V) S rho X H first ↔
      Restated.FirstHeightProgressAtOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun i => NamedRun.stateBefore S rho i) X H first :=
  ⟨fun h => ⟨h.positive, h.frontier, h.before⟩, fun h => ⟨h.positive, h.frontier, h.before⟩⟩

/-- `Restated.honestRoundVotersOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.honestRoundVotersOn`. -/
@[record_vocabulary]
theorem honestRoundVotersOn_vocabulary_eq (S : Setup V) (rho : NamedRun V) (Hs : Int → Finset V) (k : Round) :
    Restated.honestRoundVotersOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun i => NamedRun.stateBefore S rho i) Hs k =
      _root_.DecoupledConsensusModel.Sts.honestRoundVotersOn (V := V) S rho Hs k := by
  simp only [Restated.honestRoundVotersOn, Vocabulary.Internal.NamedOutageEntry.emittedInRound_vocabulary_eq]
  rfl

/-- `Restated.historicalHonestVotersOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.historicalHonestVotersOn`. -/
@[record_vocabulary]
theorem historicalHonestVotersOn_vocabulary_eq (S : Setup V) (rho : NamedRun V) (Hs : Int → Finset V) (r : Round) :
    Restated.historicalHonestVotersOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun i => NamedRun.stateBefore S rho i) Hs r =
      _root_.DecoupledConsensusModel.Sts.historicalHonestVotersOn (V := V) S rho Hs r := by
  simp only [Restated.historicalHonestVotersOn, honestRoundVotersOn_vocabulary_eq]
  rfl

/-- `Restated.staleHistoricalVotersOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.staleHistoricalVotersOn`. -/
@[record_vocabulary]
theorem staleHistoricalVotersOn_vocabulary_eq (S : Setup V) (rho : NamedRun V) (Hs : Int → Finset V) (r : Round) :
    Restated.staleHistoricalVotersOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun i => NamedRun.stateBefore S rho i) Hs r =
      _root_.DecoupledConsensusModel.Sts.staleHistoricalVotersOn (V := V) S rho Hs r := by
  simp only [Restated.staleHistoricalVotersOn, historicalHonestVotersOn_vocabulary_eq,
    honestRoundVotersOn_vocabulary_eq]
  rfl

/-- `Restated.GradeFormingMajorityOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.GradeFormingMajorityOn`. -/
@[record_vocabulary]
theorem GradeFormingMajorityOn_vocabulary_eq (S : Setup V) (rho : NamedRun V) (Hs : Int → Finset V) (X : Finset V) (r : Round) :
    _root_.DecoupledConsensusModel.Sts.GradeFormingMajorityOn (V := V) S rho Hs X r ↔ Restated.GradeFormingMajorityOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun i => NamedRun.stateBefore S rho i) Hs X r := by
  record_vocabulary_iff [Restated.GradeFormingMajorityOn,
    _root_.DecoupledConsensusModel.Sts.GradeFormingMajorityOn,
    _root_.DecoupledConsensusModel.Sts.staleHistoricalVotersOn]

/-- `Restated.NamedHonestVotesConeOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.NamedHonestVotesConeOn`. -/
@[record_vocabulary]
theorem NamedHonestVotesConeOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (Xb : Finset V) (s : Slot) (tgt : Block V → Prop) :
    _root_.DecoupledConsensusModel.Sts.NamedHonestVotesConeOn (V := V) S rho Hs Xb s tgt ↔ Restated.NamedHonestVotesConeOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun i => NamedRun.stateBefore S rho i) Hs Xb s tgt := by
  record_vocabulary_iff [Restated.NamedHonestVotesConeOn,
    _root_.DecoupledConsensusModel.Sts.NamedHonestVotesConeOn]

/-- `Restated.NamedHonestVotesNameOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.NamedHonestVotesNameOn`. -/
@[record_vocabulary]
theorem NamedHonestVotesNameOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (s : Slot) (B : Block V) :
    _root_.DecoupledConsensusModel.Sts.NamedHonestVotesNameOn (V := V) S rho Hs s B ↔ Restated.NamedHonestVotesNameOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun i => NamedRun.stateBefore S rho i) Hs s B := by
  record_vocabulary_iff [Restated.NamedHonestVotesNameOn,
    _root_.DecoupledConsensusModel.Sts.NamedHonestVotesNameOn]

/-- `Restated.NamedHonestHeadOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.NamedHonestHeadOn`. -/
@[record_vocabulary]
theorem NamedHonestHeadOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (Xb : Finset V) (s : Slot) (head : NamedBlock V) :
    _root_.DecoupledConsensusModel.Sts.NamedHonestHeadOn (V := V) S rho Hs Xb s head ↔ Restated.NamedHonestHeadOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun i => NamedRun.stateBefore S rho i) Hs Xb s head := by
  record_vocabulary_iff [Restated.NamedHonestHeadOn, _root_.DecoupledConsensusModel.Sts.NamedHonestHeadOn]

/-- `Restated.HonestHeadOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.HonestHeadOn`. -/
@[record_vocabulary]
theorem HonestHeadOn_vocabulary_eq (S : Setup V) (ρ : Run V) (Hs : Int → Finset V) (Xb : Finset V) (s : Slot) (X : Block V) :
    _root_.DecoupledConsensusModel.Sts.HonestHeadOn (V := V) S ρ Hs Xb s X ↔ Restated.HonestHeadOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary ρ)
        (fun i => NamedRun.stateBefore S ρ i) Hs Xb s X := by
  record_vocabulary_iff [Restated.HonestHeadOn, _root_.DecoupledConsensusModel.Sts.HonestHeadOn]

/-- `Restated.ThinHonestHeadAtOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.ThinHonestHeadAtOn`. -/
@[record_vocabulary]
theorem ThinHonestHeadAtOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (Xb : Finset V) (M : Height) (s : Slot) (C : Block V) :
    _root_.DecoupledConsensusModel.Sts.ThinHonestHeadAtOn (V := V) S rho Hs Xb M s C ↔ Restated.ThinHonestHeadAtOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun i => NamedRun.stateBefore S rho i) Hs Xb M s C := by
  record_vocabulary_iff [Restated.ThinHonestHeadAtOn, _root_.DecoupledConsensusModel.Sts.ThinHonestHeadAtOn]

/-- `Restated.HeadsResolveInOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.HeadsResolveInOn`. -/
@[record_vocabulary]
theorem HeadsResolveInOn_vocabulary_eq (S : Setup V) (ρ : Run V) (Hs : Int → Finset V) (Xb : Finset V) (s : Slot) (T : Finset (Block V)) (tb : TimestampMap (Block V)) :
    _root_.DecoupledConsensusModel.Sts.HeadsResolveInOn (V := V) S ρ Hs Xb s T tb ↔ Restated.HeadsResolveInOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary ρ)
        (fun i => NamedRun.stateBefore S ρ i) Hs Xb s T tb := by
  record_vocabulary_iff [Restated.HeadsResolveInOn, _root_.DecoupledConsensusModel.Sts.HeadsResolveInOn]

/-- `Restated.HonestHeadsAvailableBeforeOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.HonestHeadsAvailableBeforeOn`. -/
@[record_vocabulary]
theorem HonestHeadsAvailableBeforeOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (Xb : Finset V) (s : Slot) (v : V) (Gamma : Time) :
    _root_.DecoupledConsensusModel.Sts.HonestHeadsAvailableBeforeOn (V := V) S rho Hs Xb s v Gamma ↔ Restated.HonestHeadsAvailableBeforeOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun i => NamedRun.stateBefore S rho i) Hs Xb s v Gamma := by
  record_vocabulary_iff [Restated.HonestHeadsAvailableBeforeOn,
    _root_.DecoupledConsensusModel.Sts.HonestHeadsAvailableBeforeOn]

/-- At `Record.Model.vocabulary`, the node state staged from `v`'s node state in the world `w` before
    slot `s`'s vote instant, with an outcome `c` of the cache update, is `voteDutyRead S rho v s`. -/
theorem voteDutyRead_mkNode_vocabulary_eq (S : Setup V) (rho : Run V) (v : V) (s : Slot)
    (w : V → (Record.Model.vocabulary (V := V)).N)
    (hw : w = NamedRun.stateBeforeTime S rho (Protocol.vote_time S.E s))
    (c : (Record.Model.vocabulary (V := V)).Cache)
    (hc : Record.Model.vocabulary.onPhaseTick S.E S.hc (w v).st.core.toHealing
      (Record.Model.vocabulary.vote_time S.E s) (w v).cache ⇢ c) :
    Record.Model.vocabulary.mkNode
        (Record.Model.vocabulary.ns_setClock S.E (w v).st (Record.Model.vocabulary.vote_time S.E s))
        (w v).record c =
      _root_.DecoupledConsensusModel.Internal.NamedRecoveryRead.voteDutyRead S rho v s := by
  have hmem : Record.Model.vocabulary.mkNode
        (Record.Model.vocabulary.ns_setClock S.E (w v).st (Record.Model.vocabulary.vote_time S.E s))
        (w v).record c ∈
      Restated.Vocabulary.Internal.NamedRecoveryRead.voteDutyRead Record.Model.vocabulary S
        (Record.Run.ofVocabulary rho) v s :=
    ⟨w, by rw [Vocabulary.Execution.NamedRun.stateBeforeTime_vocabulary_eq, hw]; rfl, c, hc, rfl⟩
  rw [Vocabulary.Internal.NamedRecoveryRead.voteDutyRead_vocabulary_eq] at hmem
  exact hmem

/-- `Restated.VoteStoresExtendOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.VoteStoresExtendOn`. -/
@[record_vocabulary]
theorem VoteStoresExtendOn_vocabulary_eq (S : Setup V) (ρ : Run V) (Hs : Int → Finset V) (s : Slot) (B : NamedBlock V) :
    _root_.DecoupledConsensusModel.Sts.VoteStoresExtendOn (V := V) S ρ Hs s B ↔
      Restated.VoteStoresExtendOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary ρ) Hs s
        (NamedRun.stateBeforeTime S ρ (Protocol.vote_time S.E s)) B := by
  constructor
  · intro h v hv hc c hc'
    obtain ⟨tree₀, H, hx⟩ := h v hv hc
    refine ⟨tree₀, H, ?_⟩
    rw [voteDutyRead_mkNode_vocabulary_eq S ρ v s _ rfl c hc']
    exact (Vocabulary.Proofs.Optimistic.NamedVoteStoreExtends_vocabulary_eq S ρ v s tree₀ H B).1 hx
  · intro h v hv hc
    obtain ⟨tree₀, H, hx⟩ := h v hv hc _ ((Record.returns_pure _ _).2 rfl)
    rw [voteDutyRead_mkNode_vocabulary_eq S ρ v s _ rfl _ ((Record.returns_pure _ _).2 rfl)] at hx
    exact ⟨tree₀, H, (Vocabulary.Proofs.Optimistic.NamedVoteStoreExtends_vocabulary_eq S ρ v s tree₀ H B).2 hx⟩

/-- `Restated.VoteTickExtendsOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.VoteTickExtendsOn`. -/
@[record_vocabulary]
theorem VoteTickExtendsOn_vocabulary_eq (S : Setup V) (ρ : Run V) (Hs : Int → Finset V) (s : Slot) (B : NamedBlock V) :
    _root_.DecoupledConsensusModel.Sts.VoteTickExtendsOn (V := V) S ρ Hs s B ↔ Restated.VoteTickExtendsOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary ρ)
        (fun i => NamedRun.stateBefore S ρ i) Hs s
        (NamedRun.stateBeforeTime S ρ (Protocol.vote_time S.E s)) B := by
  constructor
  · intro h v hv hcom c hc D hD
    obtain ⟨tree₀, H, u, hslot, hal, hduty, hemit⟩ := h v hv hcom
    rw [voteDutyRead_mkNode_vocabulary_eq S ρ v s _ rfl c hc] at hD ⊢
    refine ⟨tree₀, H, u, hslot,
      (Vocabulary.Proofs.Optimistic.NamedVoteStoreExtends_vocabulary_eq S ρ v s tree₀ H B).1 hal, ?_,
      (Vocabulary.Execution.NamedRun.emits_vocabulary_eq S ρ _ _ _).1 hemit⟩
    rw [(Record.returns_pure _ _).1 hD]
    exact hduty
  · intro h v hv hcom
    have hx := h v hv hcom _ ((Record.returns_pure _ _).2 rfl) _ ((Record.returns_pure _ _).2 rfl)
    rw [voteDutyRead_mkNode_vocabulary_eq S ρ v s _ rfl _ ((Record.returns_pure _ _).2 rfl)] at hx
    obtain ⟨tree₀, H, u, hslot, hal, hduty, hemit⟩ := hx
    exact ⟨tree₀, H, u, hslot,
      (Vocabulary.Proofs.Optimistic.NamedVoteStoreExtends_vocabulary_eq S ρ v s tree₀ H B).2 hal, hduty,
      (Vocabulary.Execution.NamedRun.emits_vocabulary_eq S ρ _ _ _).2 hemit⟩

/-- `Restated.NamedSGTargetConeCanonicalityOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.NamedSGTargetConeCanonicalityOn`. -/
@[record_vocabulary]
theorem NamedSGTargetConeCanonicalityOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (Xb : Finset V) (r : Round) (s : Slot) :
    _root_.DecoupledConsensusModel.Sts.NamedSGTargetConeCanonicalityOn (V := V) S rho Hs Xb r s ↔
      Restated.NamedSGTargetConeCanonicalityOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun i => NamedRun.stateBefore S rho i) Hs Xb r s
        (NamedRun.stateBeforeTime S rho (S.a r)) := by
  record_vocabulary_iff [Restated.NamedSGTargetConeCanonicalityOn,
    _root_.DecoupledConsensusModel.Sts.NamedSGTargetConeCanonicalityOn]

/-- At `Record.Model.vocabulary`, a property holds of every block the SG vote selector can return at a
    round-`r` action node state staged from `v`'s node state before `S.a r` exactly when it holds of
    `actionSGBlockAt S rho v r`. -/
private theorem actionCarrierFrom_vocabulary₄₂b (S : Setup V) (rho : Run V) (v : V) (r : Round)
    (p : Block V → Prop) :
    (∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom Record.Model.vocabulary S
        (NamedRun.stateBeforeTime S rho (S.a r) v) r,
      ∀ g : Option (Block V), (Record.Model.vocabulary (V := V)).grade2_block_with
          ((Record.Model.vocabulary (V := V)).gradeContract n.cache) S.E S.hc
          ((Record.Model.vocabulary (V := V)).toHealing n.st.core)
          ((Record.Model.vocabulary (V := V)).round_of S.hc
            ((Record.Model.vocabulary (V := V)).toHealing n.st.core).s) ⇢ g →
      ∀ A : Block V, (Record.Model.vocabulary (V := V)).get_sg_vote_with
          ((Record.Model.vocabulary (V := V)).gradeContract n.cache) S.E S.hc
          ((Record.Model.vocabulary (V := V)).toHealing n.st.core)
          ((Record.Model.vocabulary (V := V)).round_of S.hc
            ((Record.Model.vocabulary (V := V)).toHealing n.st.core).s) g ⇢ A → p A) ↔
      p (actionSGBlockAt S rho v r) := by
  rw [Vocabulary.Execution.NamedActionReads.actionReadFrom_vocabulary_eq]
  constructor
  · intro h
    exact h _ rfl _ ((Record.returns_pure _ _).2 rfl) _ ((Record.returns_pure _ _).2 rfl)
  · intro h n hn g hg A hA
    obtain rfl : n = _ := hn
    obtain rfl := (Record.returns_pure _ _).1 hg
    obtain rfl := (Record.returns_pure _ _).1 hA
    exact h

/-- `Restated.RelativeCarrierWindowAtOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.RelativeCarrierWindowAtOn`. -/
@[record_vocabulary]
theorem RelativeCarrierWindowAtOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (r : Round) (p : Phase) :
    _root_.DecoupledConsensusModel.Sts.RelativeCarrierWindowAtOn (V := V) S rho Hs r p ↔ Restated.RelativeCarrierWindowAtOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun i => NamedRun.stateBefore S rho i) (fun t => NamedRun.stateBeforeTime S rho t)
        Hs r p := by
  have hV := honestRoundVotersOn_vocabulary_eq (V := V) S rho Hs r
  unfold Restated.RelativeCarrierWindowAtOn _root_.DecoupledConsensusModel.Sts.RelativeCarrierWindowAtOn
  rw [hV]
  refine forall₂_congr fun w hw => forall₂_congr fun u hu => imp_congr_right fun huE => ?_
  refine Iff.trans ?_ (actionCarrierFrom_vocabulary₄₂b S rho u r _).symm
  constructor
  · intro h I hI
    obtain rfl := (Record.returns_pure _ _).1 hI
    exact h
  · intro h
    exact h _ ((Record.returns_pure _ _).2 rfl)

/-- `Restated.SGTargetConeCanonicalityOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.SGTargetConeCanonicalityOn`. -/
@[record_vocabulary]
theorem SGTargetConeCanonicalityOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (Xb : Finset V) (r : Round) (s : Slot) :
    _root_.DecoupledConsensusModel.Sts.SGTargetConeCanonicalityOn (V := V) S rho Hs Xb r s ↔ Restated.SGTargetConeCanonicalityOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun i => NamedRun.stateBefore S rho i) Hs Xb r s
        (NamedRun.stateBeforeTime S rho (S.a r)) := by
  have hV := NamedHonestVotesConeOn_vocabulary_eq (V := V) S rho Hs Xb s
  unfold Restated.SGTargetConeCanonicalityOn _root_.DecoupledConsensusModel.Sts.SGTargetConeCanonicalityOn
  refine forall₂_congr fun v hv => ?_
  rw [actionCarrierFrom_vocabulary₄₂b S rho v r]
  exact hV _

/-- `Restated.SGTargetOpeningConeRootLockOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.SGTargetOpeningConeRootLockOn`. -/
@[record_vocabulary]
theorem SGTargetOpeningConeRootLockOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (Xb : Finset V) (K : Height) (r : Round) (s : Slot) :
    _root_.DecoupledConsensusModel.Sts.SGTargetOpeningConeRootLockOn (V := V) S rho Hs Xb K r s ↔ Restated.SGTargetOpeningConeRootLockOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun i => NamedRun.stateBefore S rho i) Hs Xb K r s
        (NamedRun.stateBeforeTime S rho (Protocol.vote_time S.E (s + 1)))
        (NamedRun.stateBeforeTime S rho (S.a r)) := by
  have hC := SGTargetConeCanonicalityOn_vocabulary_eq (V := V) S rho Hs Xb r s
  have hR := RunBlockOn_vocabulary_eq (V := V) S rho Xb
  have hV := NamedHonestVotesConeOn_vocabulary_eq (V := V) S rho Hs Xb s
  constructor
  · intro h
    refine ⟨hC.1 h.canonical, fun {B} hB hK hcone v hv c hc => ?_⟩
    rw [voteDutyRead_mkNode_vocabulary_eq S rho v (s + 1) _ rfl c hc]
    exact h.coneRootLock ((hR B).2 hB) hK ((hV _).2 hcone) v hv
  · intro h
    refine ⟨hC.2 h.canonical, fun {B} hB hK hcone v hv => ?_⟩
    have hx := h.coneRootLock ((hR B).1 hB) hK ((hV _).1 hcone) v hv _
      ((Record.returns_pure _ _).2 rfl)
    rw [voteDutyRead_mkNode_vocabulary_eq S rho v (s + 1) _ rfl _ ((Record.returns_pure _ _).2 rfl)] at hx
    exact hx

/-- At `Record.Model.vocabulary`, `namedG1At S rho w q B` holds exactly when every outcome of the
    round-`q` grade-1 store grade for `B` at `w`'s store before round `q`'s grade-1 domain instant
    is `true`. -/
private theorem namedG1At_iff_body_vocabulary₄₂b (S : Setup V) (rho : Run V) (w : V) (q : Round)
    (B : Block V) :
    _root_.DecoupledConsensusModel.Proofs.HealingSurface.namedG1At S rho w q B ↔
      ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade Record.Model.vocabulary S.E S.hc
        (NamedRun.stateBeforeTime S rho
          ((Record.Model.vocabulary (V := V)).domain S.E S.hc q Phase.g1) w).st q Phase.g1 B ⇢ b →
        b = true := by
  rw [Vocabulary.Proofs.HealingSurface.namedG1At_vocabulary_eq]
  unfold Restated.Vocabulary.Proofs.HealingSurface.namedG1At
  rw [Vocabulary.Internal.PhaseGrades.readAt_vocabulary_eq]
  exact ⟨fun h => h _ rfl, fun h n hn => by obtain rfl : n = _ := hn; exact h⟩

/-- `Restated.NamedG1ConcentrationOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.NamedG1ConcentrationOn`. -/
@[record_vocabulary]
theorem NamedG1ConcentrationOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (Xb : Finset V) (r : Round) (s : Slot) :
    _root_.DecoupledConsensusModel.Sts.NamedG1ConcentrationOn (V := V) S rho Hs Xb r s ↔ Restated.NamedG1ConcentrationOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun i => NamedRun.stateBefore S rho i) (fun t => NamedRun.stateBeforeTime S rho t)
        Hs Xb r s := by
  have hV := NamedHonestVotesConeOn_vocabulary_eq (V := V) S rho Hs Xb s
  have hG := fun (w : V) (B : Block V) => namedG1At_iff_body_vocabulary₄₂b S rho w (r + 1) B
  constructor
  · intro h
    exact ⟨fun hw hB => (hV _).1 (h.supported hw ((hG _ _).2 hB)),
      fun hw₁ hw₂ hB₁ hB₂ => h.compatible hw₁ hw₂ ((hG _ _).2 hB₁) ((hG _ _).2 hB₂)⟩
  · intro h
    exact ⟨fun hw hB => (hV _).2 (h.supported hw ((hG _ _).1 hB)),
      fun hw₁ hw₂ hB₁ hB₂ => h.compatible hw₁ hw₂ ((hG _ _).1 hB₁) ((hG _ _).1 hB₂)⟩

/-- `Restated.NamedNextVoteAdoptionOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.NamedNextVoteAdoptionOn`. -/
@[record_vocabulary]
theorem NamedNextVoteAdoptionOn_vocabulary_eq (S : Setup V) (rho : Run V) (Xb : Finset V) (source : Store V) (s : Slot) (B : Block V) (w : V) :
    _root_.DecoupledConsensusModel.Sts.NamedNextVoteAdoptionOn (V := V) S rho Xb source s B w ↔
      Restated.NamedNextVoteAdoptionOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun i => NamedRun.stateBefore S rho i) Xb source s B w
        (_root_.DecoupledConsensusModel.Execution.NamedActionReads.confirmationReadAt S rho w
          (Protocol.vote_time S.E (s + 1))) := by
  record_vocabulary_struct_iff

/-- `Restated.NamedGradeFormsAtOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.NamedGradeFormsAtOn`. -/
@[record_vocabulary]
theorem NamedGradeFormsAtOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (r : Round) (C : Block V) :
    _root_.DecoupledConsensusModel.Sts.NamedGradeFormsAtOn (V := V) S rho Hs r C ↔
      Restated.NamedGradeFormsAtOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) Hs r C
        (NamedRun.stateBeforeTime S rho (Protocol.domain S.E S.hc r Phase.g2)) := by
  record_vocabulary_iff [Restated.NamedGradeFormsAtOn, _root_.DecoupledConsensusModel.Sts.NamedGradeFormsAtOn]

/-- `Restated.ActionCarriersCoverOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.ActionCarriersCoverOn`. -/
@[record_vocabulary]
theorem ActionCarriersCoverOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (r : Round) (P : Block V) :
    _root_.DecoupledConsensusModel.Sts.ActionCarriersCoverOn (V := V) S rho Hs r P ↔ Restated.ActionCarriersCoverOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) Hs r P
        (NamedRun.stateBeforeTime S rho (S.a r)) := by
  unfold Restated.ActionCarriersCoverOn _root_.DecoupledConsensusModel.Sts.ActionCarriersCoverOn
  refine forall₂_congr fun v hv => ?_
  rw [actionCarrierFrom_vocabulary₄₂b S rho v r]

/-- `Restated.HonestActionCarriersOneChainAtOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.HonestActionCarriersOneChainAtOn`. -/
@[record_vocabulary]
theorem HonestActionCarriersOneChainAtOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (r : Round) :
    _root_.DecoupledConsensusModel.Sts.HonestActionCarriersOneChainAtOn (V := V) S rho Hs r ↔ Restated.HonestActionCarriersOneChainAtOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) Hs r := by
  record_vocabulary_iff [Restated.HonestActionCarriersOneChainAtOn,
    _root_.DecoupledConsensusModel.Sts.HonestActionCarriersOneChainAtOn]

/-- `Restated.SelectedG2SettledAtOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.SelectedG2SettledAtOn`. -/
@[record_vocabulary]
theorem SelectedG2SettledAtOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (r : Round) :
    _root_.DecoupledConsensusModel.Sts.SelectedG2SettledAtOn (V := V) S rho Hs r ↔
      Restated.SelectedG2SettledAtOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun t => NamedRun.stateBeforeTime S rho t) Hs r := by
  record_vocabulary_iff [Restated.SelectedG2SettledAtOn, _root_.DecoupledConsensusModel.Sts.SelectedG2SettledAtOn]

/-- `Restated.NamedLiveG1SettledAtOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.NamedLiveG1SettledAtOn`. -/
@[record_vocabulary]
theorem NamedLiveG1SettledAtOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (r : Round) :
    _root_.DecoupledConsensusModel.Sts.NamedLiveG1SettledAtOn (V := V) S rho Hs r ↔
      Restated.NamedLiveG1SettledAtOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun t => NamedRun.stateBeforeTime S rho t) Hs r := by
  unfold Restated.NamedLiveG1SettledAtOn _root_.DecoupledConsensusModel.Sts.NamedLiveG1SettledAtOn
  refine forall₂_congr fun u hu => forall_congr' fun B => imp_congr ?_ Iff.rfl
  rw [Vocabulary.Proofs.HealingSurface.namedG1At_vocabulary_eq]
  unfold Restated.Vocabulary.Proofs.HealingSurface.namedG1At
  rw [Vocabulary.Internal.PhaseGrades.readAt_vocabulary_eq]
  exact ⟨fun h => h _ rfl, fun h n hn => by obtain rfl : n = _ := hn; exact h⟩

/-- `Restated.PreviousActionCarriersQuietAtOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.PreviousActionCarriersQuietAtOn`. -/
@[record_vocabulary]
theorem PreviousActionCarriersQuietAtOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (r : Round) :
    _root_.DecoupledConsensusModel.Sts.PreviousActionCarriersQuietAtOn (V := V) S rho Hs r ↔
      Restated.PreviousActionCarriersQuietAtOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun t => NamedRun.stateBeforeTime S rho t) Hs r := by
  record_vocabulary_iff [Restated.PreviousActionCarriersQuietAtOn,
    _root_.DecoupledConsensusModel.Sts.PreviousActionCarriersQuietAtOn]

/-- `Restated.HonestSGEmissionsCompatibleAtRoundOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.HonestSGEmissionsCompatibleAtRoundOn`. -/
@[record_vocabulary]
theorem HonestSGEmissionsCompatibleAtRoundOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (r : Round) (B : Block V) :
    _root_.DecoupledConsensusModel.Sts.HonestSGEmissionsCompatibleAtRoundOn (V := V) S rho Hs r B ↔ Restated.HonestSGEmissionsCompatibleAtRoundOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun i => NamedRun.stateBefore S rho i) (fun t => NamedRun.stateBeforeTime S rho t)
        Hs r B := by
  unfold Restated.HonestSGEmissionsCompatibleAtRoundOn
    _root_.DecoupledConsensusModel.Sts.HonestSGEmissionsCompatibleAtRoundOn
  refine forall₂_congr fun v hv => ?_
  rw [Vocabulary.Execution.NamedActionReads.actionReadFrom_vocabulary_eq]
  constructor
  · intro h n hn D hD hemit
    obtain rfl : n = _ := hn
    obtain rfl := (Record.returns_pure _ _).1 hD
    dsimp only
    intro A2 hA2 G hG
    obtain rfl := (Record.returns_pure _ _).1 hA2
    obtain rfl := (Record.returns_pure _ _).1 hG
    exact h ((Vocabulary.Execution.Run.emits_vocabulary_eq S rho _ _ _).2 hemit)
  · intro h hemit
    exact h _ rfl _ ((Record.returns_pure _ _).2 rfl)
      ((Vocabulary.Execution.Run.emits_vocabulary_eq S rho _ _ _).1 hemit)
      _ ((Record.returns_pure _ _).2 rfl) _ ((Record.returns_pure _ _).2 rfl)

/-- `Restated.NamedTargetedHonestActionProposalCoverageAtOn` at the model `Record.Model.vocabulary`
    agrees with `DecoupledConsensusModel.Sts.NamedTargetedHonestActionProposalCoverageAtOn`. -/
@[record_vocabulary]
theorem NamedTargetedHonestActionProposalCoverageAtOn_vocabulary_eq (S : Setup V) (rho : Run V) (X : Finset V) (r : Round) (B : NamedBlock V) (H : Height) (T : BlockId) :
    _root_.DecoupledConsensusModel.Sts.NamedTargetedHonestActionProposalCoverageAtOn (V := V) S rho X r B H T ↔
      Restated.NamedTargetedHonestActionProposalCoverageAtOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) X r B H T
        (NamedRun.stateBeforeTime S rho (S.a r)) := by
  record_vocabulary_iff [Restated.NamedTargetedHonestActionProposalCoverageAtOn,
    _root_.DecoupledConsensusModel.Sts.NamedTargetedHonestActionProposalCoverageAtOn]

/-- `Restated.CleanActionReadForOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.CleanActionReadForOn`. -/
@[record_vocabulary]
theorem CleanActionReadForOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (r : Round) (P : Block V) :
    _root_.DecoupledConsensusModel.Sts.CleanActionReadForOn (V := V) S rho Hs r P ↔ Restated.CleanActionReadForOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) Hs r
        (fun t => NamedRun.stateBeforeTime S rho t) P := by
  constructor
  · intro h
    refine ⟨h.post_gst, h.cutoff_in_horizon, h.active, h.active_domain, ?_⟩
    intro w hw v hv
    dsimp only
    intro n hn g hg B hB
    change n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom Record.Model.vocabulary S
      (NamedRun.stateBeforeTime S rho (S.a r) v) r at hn
    rw [Vocabulary.Execution.NamedActionReads.actionReadFrom_vocabulary_eq] at hn
    obtain rfl := Set.mem_singleton_iff.mp hn
    obtain rfl := (Record.returns_pure _ _).1 hg
    obtain rfl := (Record.returns_pure _ _).1 hB
    refine ⟨(h.resolved_support w hw v hv).1, fun b hb => ?_⟩
    obtain rfl := (Record.returns_pure _ _).1 hb
    exact (h.resolved_support w hw v hv).2
  · intro h
    refine ⟨h.post_gst, h.cutoff_in_horizon, h.active, h.active_domain, ?_⟩
    intro w hw v hv
    have hn : _root_.DecoupledConsensusModel.Execution.NamedActionReads.actionReadFrom S
        (NamedRun.stateBeforeTime S rho (S.a r) v) r ∈
        Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom Record.Model.vocabulary S
          (NamedRun.stateBeforeTime S rho (S.a r) v) r := by
      rw [Vocabulary.Execution.NamedActionReads.actionReadFrom_vocabulary_eq]; rfl
    have h' := h.resolved_support w hw v hv _ hn _ ((Record.returns_pure _ _).2 rfl) _
      ((Record.returns_pure _ _).2 rfl)
    exact ⟨h'.1, h'.2 _ ((Record.returns_pure _ _).2 rfl)⟩

/-- `Restated.RelativeG2SupportOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.RelativeG2SupportOn`. -/
@[record_vocabulary]
theorem RelativeG2SupportOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (X : Finset V) (r : Round) (C : Block V) :
    _root_.DecoupledConsensusModel.Sts.RelativeG2SupportOn (V := V) S rho Hs X r C ↔ Restated.RelativeG2SupportOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) Hs X r C :=
  by
  record_vocabulary_struct_iff

/-- `Restated.GateOffFrameAtOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.GateOffFrameAtOn`. -/
@[record_vocabulary]
theorem GateOffFrameAtOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (M : Height) (lo hi : Round) :
    _root_.DecoupledConsensusModel.Sts.GateOffFrameAtOn (V := V) S rho Hs M lo hi ↔ Restated.GateOffFrameAtOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun t => NamedRun.stateBeforeTime S rho t) Hs M lo hi := by
  record_vocabulary_iff [Restated.GateOffFrameAtOn, _root_.DecoupledConsensusModel.Sts.GateOffFrameAtOn]

/-- `Restated.NamedGateOffFrameAtOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.NamedGateOffFrameAtOn`. -/
@[record_vocabulary]
theorem NamedGateOffFrameAtOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (M : Height) (lo hi : Round) :
    _root_.DecoupledConsensusModel.Sts.NamedGateOffFrameAtOn (V := V) S rho Hs M lo hi ↔ Restated.NamedGateOffFrameAtOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun t => NamedRun.stateBeforeTime S rho t) Hs M lo hi := by
  record_vocabulary_iff [Restated.NamedGateOffFrameAtOn, _root_.DecoupledConsensusModel.Sts.NamedGateOffFrameAtOn]

/-- `Restated.SeedGateOffFrameAtOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.SeedGateOffFrameAtOn`. -/
@[record_vocabulary]
theorem SeedGateOffFrameAtOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (M : Height) (lo hi : Round) :
    _root_.DecoupledConsensusModel.Sts.SeedGateOffFrameAtOn (V := V) S rho Hs M lo hi ↔ Restated.SeedGateOffFrameAtOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun t => NamedRun.stateBeforeTime S rho t) Hs M lo hi := by
  record_vocabulary_iff [Restated.SeedGateOffFrameAtOn, _root_.DecoupledConsensusModel.Sts.SeedGateOffFrameAtOn]

/-- `Restated.VoteDutyFrameAtOn'` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.VoteDutyFrameAtOn'`. -/
@[record_vocabulary]
theorem VoteDutyFrameAtOn'_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (M : Height) (d : Slot) (C : Block V) :
    _root_.DecoupledConsensusModel.Sts.VoteDutyFrameAtOn' (V := V) S rho Hs M d C ↔
      Restated.VoteDutyFrameAtOn' (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun t => NamedRun.stateBeforeTime S rho t) Hs M d C := by
  record_vocabulary_iff [Restated.VoteDutyFrameAtOn', _root_.DecoupledConsensusModel.Sts.VoteDutyFrameAtOn']

/-- `Restated.GateOffSeedConeWindowAtOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.GateOffSeedConeWindowAtOn`. -/
@[record_vocabulary]
theorem GateOffSeedConeWindowAtOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (M : Height) (lo hi : Slot) :
    _root_.DecoupledConsensusModel.Sts.GateOffSeedConeWindowAtOn (V := V) S rho Hs M lo hi ↔ Restated.GateOffSeedConeWindowAtOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun t => NamedRun.stateBeforeTime S rho t) Hs M lo hi :=
  by
  record_vocabulary_struct_iff

/-- `Restated.FinalityFloorAtOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.FinalityFloorAtOn`. -/
@[record_vocabulary]
theorem FinalityFloorAtOn_vocabulary_eq (S : Setup V) (rho : Run V) (X Xb : Finset V) (blocked : Height) (stop : Nat) (Tprev : Block V) :
    _root_.DecoupledConsensusModel.Sts.FinalityFloorAtOn (V := V) S rho X Xb blocked stop Tprev ↔ Restated.FinalityFloorAtOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) (fun i => NamedRun.stateBefore S rho i) X Xb blocked stop Tprev := by
  record_vocabulary_iff [Restated.FinalityFloorAtOn, _root_.DecoupledConsensusModel.Sts.FinalityFloorAtOn]

/-- `Restated.NamedFinalityFloorAtOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.NamedFinalityFloorAtOn`. -/
@[record_vocabulary]
theorem NamedFinalityFloorAtOn_vocabulary_eq (S : Setup V) (rho : Run V) (X Xb : Finset V) (blocked : Height) (stop : Nat) (Tprev : NamedBlock V) :
    _root_.DecoupledConsensusModel.Sts.NamedFinalityFloorAtOn (V := V) S rho X Xb blocked stop Tprev ↔ Restated.NamedFinalityFloorAtOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) (fun i => NamedRun.stateBefore S rho i) X Xb blocked stop Tprev := by
  record_vocabulary_iff [Restated.NamedFinalityFloorAtOn, _root_.DecoupledConsensusModel.Sts.NamedFinalityFloorAtOn]

/-- `Restated.HeightRegimeFrameOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.HeightRegimeFrameOn`. -/
@[record_vocabulary]
theorem HeightRegimeFrameOn_vocabulary_eq (S : Setup V) (rho : Run V) (X Xb : Finset V) (blocked : Height) (stop : Nat) (Tprev : Block V) (c0 : Round) :
    _root_.DecoupledConsensusModel.Sts.HeightRegimeFrameOn (V := V) S rho X Xb blocked stop Tprev c0 ↔
      Restated.HeightRegimeFrameOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) (fun i => NamedRun.stateBefore S rho i)
        (fun t => NamedRun.stateBeforeTime S rho t) X Xb blocked stop Tprev c0 := by
  record_vocabulary_struct_iff

/-- `Restated.NamedHeightRegimeFrameOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.NamedHeightRegimeFrameOn`. -/
@[record_vocabulary]
theorem NamedHeightRegimeFrameOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (X Xb : Finset V) (blocked : Height) (stop : Nat) (Tprev : NamedBlock V) (c0 : Round) :
    _root_.DecoupledConsensusModel.Sts.NamedHeightRegimeFrameOn (V := V) S rho Hs X Xb blocked stop Tprev c0 ↔ Restated.NamedHeightRegimeFrameOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) (fun i => NamedRun.stateBefore S rho i)
        (fun t => NamedRun.stateBeforeTime S rho t) Hs X Xb blocked stop Tprev c0 :=
  by
  record_vocabulary_struct_iff

/-- `Restated.NamedOldTargetRootBelowRunOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.NamedOldTargetRootBelowRunOn`. -/
@[record_vocabulary]
theorem NamedOldTargetRootBelowRunOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (X Xb : Finset V) (first : Nat) (blocked : Height) (T : NamedBlock V) :
    _root_.DecoupledConsensusModel.Sts.NamedOldTargetRootBelowRunOn (V := V) S rho Hs X Xb first blocked T ↔ Restated.NamedOldTargetRootBelowRunOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun i => NamedRun.stateBefore S rho i) (fun t => NamedRun.stateBeforeTime S rho t)
        Hs X Xb first blocked T := by
  record_vocabulary_iff [Restated.NamedOldTargetRootBelowRunOn,
    _root_.DecoupledConsensusModel.Sts.NamedOldTargetRootBelowRunOn]

/-- `Restated.PrefixFGSelectorConeAtOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.PrefixFGSelectorConeAtOn`. -/
@[record_vocabulary]
theorem PrefixFGSelectorConeAtOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (Xb : Finset V) (start stop : Nat) (blocked : Height) (index : Nat) (attestation : NamedAttestation V) (actionTime : Time) (selectedBlock : NamedBlock V) (checkpoint : Block V) :
    _root_.DecoupledConsensusModel.Sts.PrefixFGSelectorConeAtOn (V := V) S rho Hs Xb start stop blocked index attestation actionTime selectedBlock checkpoint ↔ Restated.PrefixFGSelectorConeAtOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun i => NamedRun.stateBefore S rho i) (fun t => NamedRun.stateBeforeTime S rho t)
        Hs Xb start stop blocked index attestation actionTime selectedBlock checkpoint :=
  by
  record_vocabulary_struct_iff

/-- `Restated.NamedHeightRegimeBaseOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.NamedHeightRegimeBaseOn`. -/
@[record_vocabulary]
theorem NamedHeightRegimeBaseOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (X Xb : Finset V) (r0 : Round) (blocked : Height) (first : Nat) (Tprev : NamedBlock V) :
    _root_.DecoupledConsensusModel.Sts.NamedHeightRegimeBaseOn (V := V) S rho Hs X Xb r0 blocked first Tprev ↔ Restated.NamedHeightRegimeBaseOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun i => NamedRun.stateBefore S rho i) (fun t => NamedRun.stateBeforeTime S rho t)
        Hs X Xb r0 blocked first Tprev :=
  by
  record_vocabulary_struct_iff

/-- `Restated.NamedHeightRegimeBaseRunOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.NamedHeightRegimeBaseRunOn`. -/
@[record_vocabulary]
theorem NamedHeightRegimeBaseRunOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (X Xb : Finset V) (r0 : Round) (blocked : Height) (first : Nat) (Tprev : NamedBlock V) :
    _root_.DecoupledConsensusModel.Sts.NamedHeightRegimeBaseRunOn (V := V) S rho Hs X Xb r0 blocked first Tprev ↔ Restated.NamedHeightRegimeBaseRunOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun i => NamedRun.stateBefore S rho i) (fun t => NamedRun.stateBeforeTime S rho t)
        Hs X Xb r0 blocked first Tprev :=
  by
  record_vocabulary_struct_iff

/-- `Restated.NamedHeightRegimeRunOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.NamedHeightRegimeRunOn`. -/
@[record_vocabulary]
theorem NamedHeightRegimeRunOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (X Xb : Finset V) (r0 : Round) (blocked : Height) (first i : Nat) (a : NamedAttestation V) (ta : Time) (Cfg T Tprev : NamedBlock V) (c0 : Round) :
    _root_.DecoupledConsensusModel.Sts.NamedHeightRegimeRunOn (V := V) S rho Hs X Xb r0 blocked first i a ta Cfg T Tprev c0 ↔ Restated.NamedHeightRegimeRunOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun i => NamedRun.stateBefore S rho i) (fun t => NamedRun.stateBeforeTime S rho t)
        Hs X Xb r0 blocked first i a ta Cfg T Tprev c0 :=
  by
  have hG := fun (w : V) (Q : Block V) => namedG1At_iff_body_vocabulary₄₂b S rho w a.round Q
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      fun w hw => (h9 w hw).imp fun Q hQ => (hG w Q).1 hQ, ?_, ?_⟩ <;>
      (try simp only [record_vocabulary, record_ofVocabulary, Membership.mem, Set.Mem] at *) <;>
      record_vocabulary_close
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      fun w hw => (h9 w hw).imp fun Q hQ => (hG w Q).2 hQ, ?_, ?_⟩ <;>
      (try simp only [record_vocabulary, record_ofVocabulary, Membership.mem, Set.Mem] at *) <;>
      record_vocabulary_close

end

end DecoupledConsensusModel.Sts.Restated
