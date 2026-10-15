module
public import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.NamedRun

@[expose] public section

/-!
# Handler calls

The handler calls an event makes: block calls, the Goldfish votes and attestation rows a block
carries, and the calls each object receives.
-/
namespace DecoupledConsensusModel.Execution

namespace NamedReceiptCalls
variable {V : Type} [DecidableEq V] [Fintype V]

/-- A block call at event index `i`: a delivery of `B` to `v`, or `v`'s own proposal of `B` at a
    tick, read on the clock-staged prefix. -/
def blockCallAt (S : Setup V) (rho : NamedRun V) (i : Nat) (v : V)
    (B : NamedBlock V) (before : Protocol.NamedStore V) : Prop :=
  (∃ t : Time, rho.events[i]? = some (.deliver v (.block B) t) ∧
    before = (NamedRun.stateBefore S rho i v).st) ∨
  ∃ t : Time, rho.events[i]? = some (.tick v t) ∧
    NamedObject.block B ∈ NamedRun.emittedAt S rho i v t ∧
    before = Protocol.NamedStore.setClock S.E (NamedRun.stateBefore S rho i v).st t

/-- The store the `j`-th attestation row of `B` is admitted on. -/
def f1Input (S : Setup V) (before : Protocol.NamedStore V) (B : NamedBlock V) (j : Nat) :
    Protocol.NamedStore V :=
  Protocol.NamedAdmission.admit_rows S.hc (postCore S before B) (B.attestations.take j)

def carriedAttestationAt (S : Setup V) (rho : NamedRun V) (i : Nat) (v : V)
    (B : NamedBlock V) (j : Nat) (a : NamedAttestation V) (before : Protocol.NamedStore V) : Prop :=
  blockCallAt S rho i v B before ∧ B ∉ before.bodies ∧
    B ∈ (postCore S before B).bodies ∧ B.attestations[j]? = some a

/-- The `j`-th Goldfish vote `u` of a block `B` that a block call at index `i` newly inserts into
    `v`'s tree. -/
def carriedGoldfishAt (S : Setup V) (rho : NamedRun V) (i : Nat) (v : V)
    (B : NamedBlock V) (j : Nat) (u : GoldfishVote V) (before : Protocol.NamedStore V) : Prop :=
  blockCallAt S rho i v B before ∧ B.erase ∉ before.core.T ∧
    B.erase ∈ (postCore S before B).core.T ∧ B.gf_votes[j]? = some u

end NamedReceiptCalls

namespace NamedRun
variable {V : Type} [DecidableEq V] [Fintype V]

/-- The handler calls `v` makes for an object at event index `i`, rejected calls included: direct
    processing, or a Goldfish vote or row carried by a block. -/
def actualHandlesAtIndex (S : Setup V) (rho : NamedRun V) (i : Nat) (v : V) :
    NamedObject V → Prop
  | .block B => processesAtIndex S rho i v (.block B)
  | .gfVote u => processesAtIndex S rho i v (.gfVote u) ∨
      ∃ B j before, NamedReceiptCalls.carriedGoldfishAt S rho i v B j u before
  | .attest a => processesAtIndex S rho i v (.attest a) ∨
      ∃ B j before, NamedReceiptCalls.carriedAttestationAt S rho i v B j a before

def actualHandlesAt (S : Setup V) (rho : NamedRun V) (i : Nat) (v : V)
    (o : NamedObject V) (t : Time) : Prop :=
  actualHandlesAtIndex S rho i v o ∧
    ∃ e : NamedEvent V, rho.events[i]? = some e ∧ e.node = v ∧ e.time = t

def acceptsAt (S : Setup V) (rho : NamedRun V) (i : Nat) (v : V)
    (o : NamedObject V) (t : Time) : Prop :=
  actualHandlesAt S rho i v o t ∧
    NamedReceipt.processed (stateBefore S rho i v).st o = false ∧
    NamedReceipt.processed (stateBefore S rho (i + 1) v).st o = true

end NamedRun
end DecoupledConsensusModel.Execution

end
