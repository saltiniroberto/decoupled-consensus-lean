import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.NamedReceiptCalls
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Objects
import Model.Record.Wiring

/-!
# Block calls and handled objects

The block calls at an event of a run, the attestations and Goldfish votes included in a called
block, and the objects a validator handles and accepts at an event, read along a path of the run,
over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Execution.NamedReceiptCalls

/-- The `i`-th event of `rho`, read along the path `W`, is a block call of `B` at `v` with input
    store `before`: a delivery of `B` to `v`, with `before` `v`'s store in `W i`, or a tick of `v`
    at some `t` that sends `B`, with `before` `v`'s store in `W i` with its clock set to `t`. -/
def Vocabulary.Execution.NamedReceiptCalls.blockCallAt (M : Record.Model V) (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → M.N) (i : Nat) (v : V) (B : NamedBlock V) (before : M.NS) : Prop :=
  (∃ t : Time, rho.events[i]? = some (.deliver v (.block B) t) ∧ before = (W i v).st) ∨
  ∃ t : Time, rho.events[i]? = some (.tick v t) ∧
    (∃ out : M.N × List (NamedObject V), M.tick S v (W i v) t ⇢ out ∧ W (i + 1) v = out.1 ∧
      NamedObject.block B ∈ out.2) ∧
    before = M.ns_setClock S.E (W i v).st t

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Execution.NamedReceiptCalls

/-- The store `M.postCore S before B` with the first `j` attestations included in `B` admitted. -/
def Vocabulary.Execution.NamedReceiptCalls.f1Input (M : Record.Model V) (S : Setup V) (before : M.NS) (B : NamedBlock V) (j : Nat) :
    M.NS :=
  M.admit_rows S.hc (M.postCore S before B) (B.attestations.take j)

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Execution.NamedReceiptCalls

/-- `before` is the input of a block call of `B` at `v` at the `i`-th event of `rho` read along the
    path `W`, `B` is not among `before`'s bodies but is among those of the store the core insertion
    returns on `before`, and `a` is the `j`-th attestation included in `B`. -/
def Vocabulary.Execution.NamedReceiptCalls.carriedAttestationAt (M : Record.Model V) (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → M.N) (i : Nat) (v : V)
    (B : NamedBlock V) (j : Nat) (a : NamedAttestation V) (before : M.NS) : Prop :=
  Restated.Vocabulary.Execution.NamedReceiptCalls.blockCallAt M S rho W i v B before ∧ B ∉ before.bodies ∧
    B ∈ (M.postCore S before B).bodies ∧ B.attestations[j]? = some a

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Execution.NamedReceiptCalls

/-- `before` is the input of a block call of `B` at `v` at the `i`-th event of `rho` read along the
    path `W`, `B`'s erasure is not in `before`'s tree but is in the tree of the store the core
    insertion returns on `before`, and `u` is the `j`-th Goldfish vote included in `B`. -/
def Vocabulary.Execution.NamedReceiptCalls.carriedGoldfishAt (M : Record.Model V) (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → M.N) (i : Nat) (v : V)
    (B : NamedBlock V) (j : Nat) (u : GoldfishVote V) (before : M.NS) : Prop :=
  Restated.Vocabulary.Execution.NamedReceiptCalls.blockCallAt M S rho W i v B before ∧ B.erase ∉ before.core.T ∧
    B.erase ∈ (M.postCore S before B).core.T ∧ B.gf_votes[j]? = some u

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Execution.NamedRun

/-- The `i`-th event of `rho` is a tick of `v` some outcome of which, from `v`'s node state in
    `W i`, leads to `v`'s node state in `W (i + 1)` and sends `o`; or it is a delivery of `o` to
    `v`. -/
def Vocabulary.Execution.NamedRun.processesAtIndexAlong (M : Record.Model V) (S : Setup V)
    (rho : Record.Run V) (W : Nat → V → M.N) (i : Nat) (v : V) (o : NamedObject V) : Prop :=
  (∃ t : Time, rho.events[i]? = some (.tick v t) ∧
      ∃ out : M.N × List (NamedObject V), M.tick S v (W i v) t ⇢ out ∧ W (i + 1) v = out.1 ∧
        o ∈ out.2) ∨
    ∃ t : Time, rho.events[i]? = some (.deliver v o t)

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Execution.NamedRun

/-- `v` handles `o` at the `i`-th event of `rho` read along the path `W`: it processes `o` there, or
    `o` is a Goldfish vote or an attestation included in a block whose call at that event includes
    it at some position. -/
def Vocabulary.Execution.NamedRun.actualHandlesAtIndex (M : Record.Model V) (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → M.N) (i : Nat) (v : V) :
    NamedObject V → Prop
  | .block B => Restated.Vocabulary.Execution.NamedRun.processesAtIndexAlong M S rho W i v (.block B)
  | .gfVote u => Restated.Vocabulary.Execution.NamedRun.processesAtIndexAlong M S rho W i v (.gfVote u) ∨
      ∃ B j before,
        Restated.Vocabulary.Execution.NamedReceiptCalls.carriedGoldfishAt M S rho W i v B j u before
  | .attest a => Restated.Vocabulary.Execution.NamedRun.processesAtIndexAlong M S rho W i v (.attest a) ∨
      ∃ B j before,
        Restated.Vocabulary.Execution.NamedReceiptCalls.carriedAttestationAt M S rho W i v B j a before

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Execution.NamedRun

/-- `v` handles `o` at the `i`-th event of `rho`, read along the path `W`, and that event is `v`'s,
    at time `t`. -/
def Vocabulary.Execution.NamedRun.actualHandlesAt (M : Record.Model V) (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → M.N) (i : Nat) (v : V)
    (o : NamedObject V) (t : Time) : Prop :=
  Restated.Vocabulary.Execution.NamedRun.actualHandlesAtIndex M S rho W i v o ∧
    ∃ e : Record.Event V, rho.events[i]? = some e ∧ e.node = v ∧ e.time = t

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Execution.NamedRun

/-- `v` handles `o` at the `i`-th event of `rho` at time `t`, read along the path `W`, and `v`'s
    store has not processed `o` in `W i` and has processed it in `W (i + 1)`. -/
def Vocabulary.Execution.NamedRun.acceptsAt (M : Record.Model V) (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → M.N) (i : Nat) (v : V)
    (o : NamedObject V) (t : Time) : Prop :=
  Restated.Vocabulary.Execution.NamedRun.actualHandlesAt M S rho W i v o t ∧
    Restated.Vocabulary.Execution.Object.processed M (W i v).st o = false ∧
    Restated.Vocabulary.Execution.Object.processed M (W (i + 1) v).st o = true

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Execution.NamedReceiptCalls
open DecoupledConsensusModel.Execution.NamedRun

/-- `DecoupledConsensusModel.Execution.NamedReceiptCalls.blockCallAt` holds exactly when
    `Restated.Vocabulary.Execution.NamedReceiptCalls.blockCallAt` holds at the model
    `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Execution.NamedReceiptCalls.blockCallAt_vocabulary_eq (S : Setup V) (rho : NamedRun V) (i : Nat) (v : V) (B : NamedBlock V) (before : Protocol.NamedStore V) :
    _root_.DecoupledConsensusModel.Execution.NamedReceiptCalls.blockCallAt (V := V) S rho i v B before ↔
      Restated.Vocabulary.Execution.NamedReceiptCalls.blockCallAt (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun i => NamedRun.stateBefore S rho i) i v B before := by
  have hT : ∀ t, (Record.Run.ofVocabulary rho).events[i]? = some (.tick v t) ↔
      rho.events[i]? = some (Generic.Event.tick v t) := fun t =>
    Record.Event.map_ofVocabulary_getElem?_tick _ _ _ _
  refine or_congr (exists_congr fun t =>
      and_congr (Record.Event.map_ofVocabulary_getElem?_deliver _ _ _ _ _).symm Iff.rfl)
    (exists_congr fun t => ⟨fun ⟨hi, hB, hb⟩ => ⟨(hT t).2 hi, ⟨_, (Record.returns_pure _ _).2 rfl,
      _root_.DecoupledConsensusModel.Proofs.NamedRuntime.stateBefore_tick S rho hi, hB⟩, hb⟩,
    fun ⟨hi, ⟨out, hout, _, hB⟩, hb⟩ => ⟨(hT t).1 hi, ?_, hb⟩⟩)
  rw [(Record.returns_pure _ out).1 hout] at hB
  exact hB

/-- `DecoupledConsensusModel.Execution.NamedReceiptCalls.f1Input` equals
    `Restated.Vocabulary.Execution.NamedReceiptCalls.f1Input` at the model `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Execution.NamedReceiptCalls.f1Input_vocabulary_eq (S : Setup V) (before : Protocol.NamedStore V) (B : NamedBlock V) (j : Nat) :
    _root_.DecoupledConsensusModel.Execution.NamedReceiptCalls.f1Input (V := V) S before B j = Restated.Vocabulary.Execution.NamedReceiptCalls.f1Input (V := V) Record.Model.vocabulary S before B j :=
  rfl

/-- `DecoupledConsensusModel.Execution.NamedReceiptCalls.carriedAttestationAt` holds exactly when
    `Restated.Vocabulary.Execution.NamedReceiptCalls.carriedAttestationAt` holds at the model
    `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Execution.NamedReceiptCalls.carriedAttestationAt_vocabulary_eq (S : Setup V) (rho : NamedRun V) (i : Nat) (v : V) (B : NamedBlock V) (j : Nat) (a : NamedAttestation V) (before : Protocol.NamedStore V) :
    _root_.DecoupledConsensusModel.Execution.NamedReceiptCalls.carriedAttestationAt (V := V) S rho i v B j a before ↔
      Restated.Vocabulary.Execution.NamedReceiptCalls.carriedAttestationAt (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun i => NamedRun.stateBefore S rho i) i v B j a before :=
  and_congr (Vocabulary.Execution.NamedReceiptCalls.blockCallAt_vocabulary_eq S rho i v B before) Iff.rfl

/-- `DecoupledConsensusModel.Execution.NamedReceiptCalls.carriedGoldfishAt` holds exactly when
    `Restated.Vocabulary.Execution.NamedReceiptCalls.carriedGoldfishAt` holds at the model
    `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Execution.NamedReceiptCalls.carriedGoldfishAt_vocabulary_eq (S : Setup V) (rho : NamedRun V) (i : Nat) (v : V) (B : NamedBlock V) (j : Nat) (u : GoldfishVote V) (before : Protocol.NamedStore V) :
    _root_.DecoupledConsensusModel.Execution.NamedReceiptCalls.carriedGoldfishAt (V := V) S rho i v B j u before ↔
      Restated.Vocabulary.Execution.NamedReceiptCalls.carriedGoldfishAt (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun i => NamedRun.stateBefore S rho i) i v B j u before :=
  and_congr (Vocabulary.Execution.NamedReceiptCalls.blockCallAt_vocabulary_eq S rho i v B before) Iff.rfl

/-- `DecoupledConsensusModel.Execution.NamedRun.processesAtIndex` holds exactly when
    `Restated.Vocabulary.Execution.NamedRun.processesAtIndexAlong` holds at the model
    `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Execution.NamedRun.processesAtIndexAlong_vocabulary_eq (S : Setup V) (rho : NamedRun V) (i : Nat) (v : V) (o : NamedObject V) :
    _root_.DecoupledConsensusModel.Execution.NamedRun.processesAtIndex (V := V) S rho i v o ↔
      Restated.Vocabulary.Execution.NamedRun.processesAtIndexAlong (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun i => NamedRun.stateBefore S rho i) i v o := by
  have hT : ∀ t, (Record.Run.ofVocabulary rho).events[i]? = some (.tick v t) ↔
      rho.events[i]? = some (Generic.Event.tick v t) := fun t =>
    Record.Event.map_ofVocabulary_getElem?_tick _ _ _ _
  refine or_congr (exists_congr fun t => ⟨fun ⟨hi, ho⟩ => ⟨(hT t).2 hi, _, (Record.returns_pure _ _).2 rfl,
      _root_.DecoupledConsensusModel.Proofs.NamedRuntime.stateBefore_tick S rho hi, ho⟩,
    fun ⟨hi, out, hout, _, ho⟩ => ⟨(hT t).1 hi, ?_⟩⟩)
    (exists_congr fun t => (Record.Event.map_ofVocabulary_getElem?_deliver _ _ _ _ _).symm)
  rw [(Record.returns_pure _ out).1 hout] at ho
  exact ho

/-- `DecoupledConsensusModel.Execution.NamedRun.actualHandlesAtIndex` equals
    `Restated.Vocabulary.Execution.NamedRun.actualHandlesAtIndex` at the model
    `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Execution.NamedRun.actualHandlesAtIndex_vocabulary_eq (S : Setup V) (rho : NamedRun V) (i : Nat) (v : V) :
    _root_.DecoupledConsensusModel.Execution.NamedRun.actualHandlesAtIndex (V := V) S rho i v =
      Restated.Vocabulary.Execution.NamedRun.actualHandlesAtIndex (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun i => NamedRun.stateBefore S rho i) i v := by
  funext o
  cases o with
  | block B =>
    exact propext (Vocabulary.Execution.NamedRun.processesAtIndexAlong_vocabulary_eq S rho i v _)
  | gfVote u =>
    exact propext (or_congr
      (Vocabulary.Execution.NamedRun.processesAtIndexAlong_vocabulary_eq S rho i v _)
      (exists_congr fun B => exists_congr fun j => exists_congr fun before =>
        Vocabulary.Execution.NamedReceiptCalls.carriedGoldfishAt_vocabulary_eq S rho i v B j u before))
  | attest a =>
    exact propext (or_congr
      (Vocabulary.Execution.NamedRun.processesAtIndexAlong_vocabulary_eq S rho i v _)
      (exists_congr fun B => exists_congr fun j => exists_congr fun before =>
        Vocabulary.Execution.NamedReceiptCalls.carriedAttestationAt_vocabulary_eq S rho i v B j a before))

/-- `DecoupledConsensusModel.Execution.NamedRun.actualHandlesAt` holds exactly when
    `Restated.Vocabulary.Execution.NamedRun.actualHandlesAt` holds at the model
    `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Execution.NamedRun.actualHandlesAt_vocabulary_eq (S : Setup V) (rho : NamedRun V) (i : Nat) (v : V) (o : NamedObject V) (t : Time) :
    _root_.DecoupledConsensusModel.Execution.NamedRun.actualHandlesAt (V := V) S rho i v o t ↔
      Restated.Vocabulary.Execution.NamedRun.actualHandlesAt (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun i => NamedRun.stateBefore S rho i) i v o t := by
  rw [_root_.DecoupledConsensusModel.Execution.NamedRun.actualHandlesAt,
    Restated.Vocabulary.Execution.NamedRun.actualHandlesAt,
    Vocabulary.Execution.NamedRun.actualHandlesAtIndex_vocabulary_eq]
  refine and_congr Iff.rfl ?_
  simp only [Record.Run.ofVocabulary_events, List.getElem?_map, Option.map_eq_some_iff]
  constructor
  · rintro ⟨e, he, hv, ht⟩
    exact ⟨_, ⟨e, he, rfl⟩, by rw [Record.Event.ofVocabulary_node]; exact hv,
      by rw [Record.Event.ofVocabulary_time]; exact ht⟩
  · rintro ⟨_, ⟨e, he, rfl⟩, hv, ht⟩
    rw [Record.Event.ofVocabulary_node] at hv
    rw [Record.Event.ofVocabulary_time] at ht
    exact ⟨e, he, hv, ht⟩

/-- `DecoupledConsensusModel.Execution.NamedRun.acceptsAt` holds exactly when
    `Restated.Vocabulary.Execution.NamedRun.acceptsAt` holds at the model `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Execution.NamedRun.acceptsAt_vocabulary_eq (S : Setup V) (rho : NamedRun V) (i : Nat) (v : V) (o : NamedObject V) (t : Time) :
    _root_.DecoupledConsensusModel.Execution.NamedRun.acceptsAt (V := V) S rho i v o t ↔
      Restated.Vocabulary.Execution.NamedRun.acceptsAt (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun i => NamedRun.stateBefore S rho i) i v o t := by
  refine and_congr (Vocabulary.Execution.NamedRun.actualHandlesAt_vocabulary_eq S rho i v o t) ?_
  rw [← Vocabulary.Execution.Object.processed_vocabulary_eq]
  exact Iff.rfl

end

end DecoupledConsensusModel.Sts.Restated
