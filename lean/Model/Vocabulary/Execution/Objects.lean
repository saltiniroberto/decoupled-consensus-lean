module
public import Mathlib.Data.Prod.Lex
public import Model.Vocabulary.Objects.NamedBlocks
public import Model.Vocabulary.Generic.Run
public import Model.Vocabulary.Objects.Time

@[expose] public section

/-!
# Wire objects and events

The objects a run carries (a block, a Goldfish vote or an attestation) and the events that deliver
them, with their projections.
-/

section
namespace DecoupledConsensusModel.Execution

inductive NamedObject (V : Type) where
  | block (B : NamedBlock V)
  | gfVote (vote : GoldfishVote V)
  | attest (row : NamedAttestation V)
  deriving DecidableEq, Repr

namespace NamedObject
variable {V : Type}

def author : NamedObject V → Option V
  | .block B => B.proposer?
  | .gfVote vote => some vote.val_index
  | .attest row => some row.val_index

end NamedObject
end DecoupledConsensusModel.Execution
end

section
namespace DecoupledConsensusModel.Execution

abbrev NamedEvent (V : Type) := Generic.Event V (NamedObject V)

namespace NamedEvent
variable {V : Type}

abbrev tick := @Generic.Event.tick V (NamedObject V)
abbrev deliver := @Generic.Event.deliver V (NamedObject V)
def time : NamedEvent V → Time
  | .tick _ t => t
  | .deliver _ _ t => t

def node : NamedEvent V → V
  | .tick v _ => v
  | .deliver v _ _ => v

def object? : NamedEvent V → Option (NamedObject V)
  | .tick _ _ => none
  | .deliver _ object _ => some object

end NamedEvent
end DecoupledConsensusModel.Execution
end

end
