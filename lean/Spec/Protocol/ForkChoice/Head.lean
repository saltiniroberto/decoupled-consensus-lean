import Spec.Protocol.ForkChoice.Goldfish

/-!
# The strong-gadget root and the composed head, over the flat store

The routines that compute the strong-gadget root and the Goldfish head from the flat store
`Store V` of `lean/Spec/Store.lean`, in the namespace `Spec.Protocol`:

- `active_prefix`: the deepest block of the filtered block tree that is an ancestor of a given
  grade block or that block itself;
- `get_sg_root_with`: the strong-gadget root, read from the store's own grade-1 block `st.G1 C`;
- `get_head_in_tree_with_layer`: the Goldfish walk in a given tree from that root
  (`goldfish_fork_choice` of `lean/Spec/Protocol/ForkChoice/Goldfish.lean`, which takes no
  environment);
- `get_head_with`: the same walk in the store's filtered block tree.

`get_sg_root_with` takes no round: it reads the store's grade-1 block, the grade-1 result of the
store's round `C.round_of st.s`.

The three routines raise when the grade-1 result of the store's round is pending, and, for the
two heads, when the walk raises (two blocks of the store's tree share the head root of a support
vote).

This file holds definitions only.
-/

open DC (DRE)

namespace Spec.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]
variable (C : Config)

/-- `active_prefix(st, g)`: the deepest block of the filtered block tree
`get_filtered_block_tree st` that is an ancestor of the grade block `g` or `g` itself; `none`
when `g` is `none` or the filtered tree holds no such block. -/
def active_prefix (st : Store V) (g : Option (Block V)) : Option (Block V) := Id.run do
  let tree := get_filtered_block_tree st
  if g ≠ none then
    return activePrefix tree g.value
  return none

/-- `get_sg_root(st)`: the strong-gadget root. With `G1` the store's grade-1 block of its round
(`st.G1 C`) and `A` its active prefix, the root is `A`, or the fork-choice root
`get_fg_root st` when `A` is `none` (no grade-1 block, or the fork-choice root has passed it).

Raises when the grade-1 result of the store's round is pending. -/
def get_sg_root_with (st : Store V) : DRE (Block V) := do
  let G1 ← st.G1 C
  let A := active_prefix st G1
  if A ≠ none then
    return A.value
  return get_fg_root st

/-- The composed head in the tree `tree`: the anchor `A` is the strong-gadget root
`get_sg_root_with C st`, and the head is the Goldfish walk from `A` through `tree`, scored by the
votes `votes` and the support votes `support_votes` of slot `s`, with ancestry read in the
store's block tree `st.T`.

Raises when the strong-gadget root raises (the grade-1 result of the store's round is pending) or
when the walk raises (two blocks of `st.T` share the head root of a support vote). -/
def get_head_in_tree_with_layer (st : Store V) (tree : Finset (Block V))
    (votes support_votes : Finset (GoldfishVote V)) (s : Slot) : DRE (Block V) := do
  let A ← get_sg_root_with C st
  goldfish_fork_choice st.σ st.h_max st.T st.s A tree votes support_votes s

/-- The composed head in the store's filtered block tree `get_filtered_block_tree st`:
`get_head_in_tree_with_layer` in that tree.

Raises when `get_head_in_tree_with_layer` does. -/
def get_head_with (st : Store V) (votes support_votes : Finset (GoldfishVote V)) (s : Slot) :
    DRE (Block V) :=
  get_head_in_tree_with_layer C st (get_filtered_block_tree st) votes support_votes s

end Spec.Protocol
