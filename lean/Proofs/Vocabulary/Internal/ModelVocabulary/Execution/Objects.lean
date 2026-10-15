module
public import Model.Vocabulary.Execution.Node

@[expose] public section

/-!
# Wire objects

The objects on the wire: named blocks, Goldfish votes and attestations.
-/
namespace DecoupledConsensusModel.Execution

abbrev Object := NamedObject

namespace Object
abbrev block := @NamedObject.block
abbrev gfVote := @NamedObject.gfVote
abbrev attest := @NamedObject.attest
abbrev wellFormed := @NamedReceipt.wellFormed
abbrev processed := @NamedReceipt.processed
end Object

end DecoupledConsensusModel.Execution

end
