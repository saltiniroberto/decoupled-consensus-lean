import Model.Vocabulary.Protocol.ForkChoice.Goldfish
import Proofs.Claims.ModelIrreducible
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.FrontierParent

/-!
# Facts about `Protocol.goldfish_fork_choice`

Lemmas that unfold the Goldfish fork choice, the walk `Protocol.ghost` with the Goldfish score and
the eligibility test `Protocol.goldfish_eligible`.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.goldfish_fork_choice

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The Goldfish fork choice from `A` through `tree` is the walk `Protocol.ghost` from `A` through
    `tree` that scores a block by `Protocol.goldfish_score` and admits a child by
    `Protocol.goldfish_eligible`. -/
theorem goldfish_fork_choice_eq_ghost (E : Env V) (σ : Block V → Protocol.ChainState V)
    (h_max : Height) (T : Finset (Block V)) (cur : Slot) (A : Block V)
    (tree : Finset (Block V)) (votes support : Finset (GoldfishVote V)) (s : Slot) :
    Protocol.goldfish_fork_choice E σ h_max T cur A tree votes support s =
      Protocol.ghost A tree (Protocol.goldfish_score E T votes support s)
        (Protocol.goldfish_eligible E σ h_max T cur votes support s) := rfl

end DecoupledConsensusModel.Sts

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- If no two distinct blocks among the blocks of `tree` and their ancestors share a root, a block
    of `tree` whose parent is the Goldfish fork choice from `A` through `tree` fails
    `Protocol.goldfish_eligible`. -/
theorem goldfish_eligible_eq_false_of_parent_fork_choice {E : Env V}
    {σ : Block V → Protocol.ChainState V} {h_max : Height} {T : Finset (Block V)} {cur : Slot}
    {A : Block V} {tree : Finset (Block V)} {votes support : Finset (GoldfishVote V)} {s : Slot}
    {C : Block V} (hroot : Execution.RootInjectiveBelow tree) (hC : C ∈ tree)
    (hparent : C.parent? =
      some (Protocol.goldfish_fork_choice E σ h_max T cur A tree votes support s)) :
    Protocol.goldfish_eligible E σ h_max T cur votes support s C = false :=
  Proofs.HealingSurface.eligible_child_false_at_ghost_result hroot hC hparent

end DecoupledConsensusModel.Sts
